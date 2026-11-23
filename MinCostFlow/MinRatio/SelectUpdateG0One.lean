module

public import MinCostFlow.MinRatio.SelectUpdateModel
public import MinCostFlow.MinRatio.SelectBlocksParts
public import MinCostFlow.MinRatio.SelectGraphRefill
public import MinCostFlow.MinRatio.SolverRep
import MinCostFlow.LinkCut.PathProg.Rep
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Level-0 gradient update from solver state (`SelectUpdateG0`)

Updates `B.g0Ptr` after `ordChainUpdateCoreBody` for both:
* **Branch A (`firstReb = 0`):** level `0` was rebuilt and compacted to `Finset.range mNew`, so
  every edge `e < mNew` is refreshed from the solver's authoritative gradient storage
  (`tok'.slots`, `tok'.edgeRecords`, and `tok'.treeHeap`);
* **Branch B (`0 < firstReb`):** level `0` was not rebuilt, so `uG` (from slot `0` of
  `UpdateCoreSelectOutAt`) is filtered through `G_0'`'s edge-presence array and each surviving
  touched edge is refreshed from the solver's authoritative gradient storage, while surviving
  untouched edges keep their unchanged gradient (`update_g_eq_of_not_rebuilt0`).

Reading directly from `(tok'.slots, tok'.edgeRecords, tok'.treeHeap)` works independently of the
caller's external `g` array (whose non-inserted entries need not be initialized by `copyInsertedStmt`),
reads tree nodes in-place without splaying (`evalPairs_some_originalGradient`), and uses `0` scratch
in Branch A and `uG.length` scratch in Branch B.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
open MinCostFlow.LinkCut.Path MinCostFlow.LinkCut.PathTree MinCostFlow.LinkCut.PathProg

/-! ## 1. Pure helpers: two's-complement truncation and raw tree-node gradient -/

private theorem unsignedVal_add_split (mem : ℕ → ℕ) (a h : ℕ) :
    ∀ L K, unsignedVal mem a h (L + K) =
      unsignedVal mem a h L + capacity h L * unsignedVal mem (a + L) h K
  | 0, K => by simp [unsignedVal, capacity]
  | L + 1, K => by
    rw [Nat.succ_add, unsignedVal, unsignedVal, capacity_succ]
    have ih := unsignedVal_add_split mem (a + 1) h L K
    rw [show a + 1 + L = a + (L + 1) by omega] at ih
    rw [ih]; ring

/-- Truncating a valid `K`-limb two's-complement block (`L ≤ K`) to its low `L` limbs preserves its
signed value whenever that value fits in `L` limbs. -/
theorem pathIntAt_trunc {mem : ℕ → ℕ} {a h L K : ℕ} {z : ℤ}
    (hLK : L ≤ K) (hP : PathIntAt mem a h K z) (hFit : Num.Fits h L z) :
    PathIntAt mem a h L z := by
  have hValL : Num.Valid mem a h L := fun i hi => hP.1 i (lt_of_lt_of_le hi hLK)
  refine ⟨hValL, ?_⟩
  have hSplit : unsignedVal mem a h K =
      unsignedVal mem a h L + capacity h L * unsignedVal mem (a + L) h (K - L) := by
    have hEq := unsignedVal_add_split mem a h L (K - L)
    rwa [Nat.add_sub_of_le hLK] at hEq
  have hCapDiv : (capacity h L : ℤ) ∣ (capacity h K : ℤ) := by
    refine ⟨(capacity h (K - L) : ℤ), ?_⟩
    have h1 : capacity h K = capacity h L * capacity h (K - L) := by
      unfold capacity; rw [← pow_add, Nat.add_sub_of_le hLK]
    exact_mod_cast h1
  have huL_lt : unsignedVal mem a h L < capacity h L := unsignedVal_lt hValL
  have hModK : ((unsignedVal mem a h K : ℕ) : ℤ) % (capacity h K : ℤ) =
      z % (capacity h K : ℤ) := by
    have hz : z = signedVal h K (unsignedVal mem a h K) := hP.2.symm
    rw [hz]; unfold signedVal
    split_ifs
    · rw [Int.sub_emod_right]
    · simp
  have hModL : ((unsignedVal mem a h L : ℕ) : ℤ) = z % (capacity h L : ℤ) := by
    have h1 : ((unsignedVal mem a h K : ℕ) : ℤ) % (capacity h L : ℤ) =
        ((unsignedVal mem a h L : ℕ) : ℤ) := by
      rw [hSplit]
      push_cast
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (Int.natCast_nonneg _)
        (by exact_mod_cast huL_lt)]
    have h2 : ((unsignedVal mem a h K : ℕ) : ℤ) % (capacity h L : ℤ) =
        z % (capacity h L : ℤ) := by
      rw [← Int.emod_emod_of_dvd _ hCapDiv, hModK, Int.emod_emod_of_dvd _ hCapDiv]
    exact h1.symm.trans h2
  have hRes : unsignedVal mem a h L = residue h L z := by
    unfold residue
    omega
  unfold intVal
  rw [hRes, signedVal_residue hFit]

/-- Reading a raw node's value from `SplayState.evalPairs pathPayload` preserves
`PathEdgeValue.originalGradient`: lazy shifts leave `forward` and `gradient` unchanged, and lazy
reversals flip `forward` and negate `gradient` together. -/
theorem evalPairs_some_originalGradient
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) :
    ∀ (t : AuxTree) (flip : Bool) (acc : PathTag) {x : ℕ} {val : PathEdgeValue},
      (x, some val) ∈ SplayState.evalPairs pathPayload s t flip acc →
      ∃ vRaw : PathEdgeValue, (s.nodes x).val = some vRaw ∧
        vRaw.originalGradient = val.originalGradient
  | .leaf, _, _, _, _, h => by simp [SplayState.evalPairs] at h
  | .node id l r, flip, acc, x, val, h => by
    cases flip with
    | false =>
      simp only [SplayState.evalPairs, Bool.false_eq_true, ↓reduceIte, List.mem_append,
        List.mem_singleton, Prod.mk.injEq] at h
      rcases h with (h | ⟨rfl, hv⟩) | h
      · exact evalPairs_some_originalGradient s _ _ _ h
      · cases hval : (s.nodes x).val with
        | none => simp [hval, pathPayload] at hv
        | some vRaw =>
          simp only [hval, pathPayload, Option.map_some, Option.some.injEq] at hv
          refine ⟨vRaw, rfl, ?_⟩
          rw [hv]; cases vRaw.forward <;> rfl
      · exact evalPairs_some_originalGradient s _ _ _ h
    | true =>
      simp only [SplayState.evalPairs, ↓reduceIte, List.mem_append,
        List.mem_singleton, Prod.mk.injEq] at h
      rcases h with (h | ⟨rfl, hv⟩) | h
      · exact evalPairs_some_originalGradient s _ _ _ h
      · cases hval : (s.nodes x).val with
        | none => simp [hval, pathPayload] at hv
        | some vRaw =>
          simp only [hval, pathPayload, Option.map_some, Option.some.injEq] at hv
          refine ⟨vRaw, rfl, ?_⟩
          rw [hv]; cases hfw : vRaw.forward <;>
            simp [PathEdgeValue.originalGradient, PathEdgeValue.shift, PathEdgeValue.reverse, hfw]
      · exact evalPairs_some_originalGradient s _ _ _ h

private theorem unsignedVal_append_one (mem : ℕ → ℕ) (a h : ℕ) :
    ∀ j, unsignedVal mem a h (j + 1) = unsignedVal mem a h j + capacity h j * mem (a + j)
  | 0 => by simp [unsignedVal, capacity]
  | j + 1 => by
    rw [unsignedVal, unsignedVal_append_one mem (a + 1) h j, unsignedVal, capacity_succ]
    have hidx : a + 1 + j = a + (j + 1) := by omega
    rw [hidx]
    ring

/-! ## 2. Two's-complement limb negation copy (`selNegCopyToBody`) -/

/-- Copy the two's-complement negation of `L` 4-bit limbs from `src` into `dst` (zero scratch).
Arguments: `[src, dst, L]` (`reg 0..2`). -/
def selNegCopyToBody : Stmt :=
  .assign 3 (.const 1) ;;
  forRange 4 (.const 0) (.reg 2)
    (.assign 5 (.bin .add (.bin .sub (.const 15) (.load (.bin .add (.reg 0) (.reg 4)))) (.reg 3)) ;;
     .store (.bin .add (.reg 1) (.reg 4)) (.bin .mod (.reg 5) (.const 16)) ;;
     .assign 3 (.bin .div (.reg 5) (.const 16))) ;;
  .ret (.const 0)

theorem selNegCopyToBody_noRand : selNegCopyToBody.NoRand := by
  simp [selNegCopyToBody, forRange, forUp, Stmt.NoRand]

/-- Contract for `selNegCopyToBody` (`[src, dst, L] → 0`). -/
def selNegCopyToContract (w : ℕ) (z : ℤ) : Contract where
  pre args mem :=
    ∃ src dst L,
      args = [src, dst, L] ∧
      16 < 2 ^ w ∧
      src + L < 2 ^ w ∧ dst + L < 2 ^ w ∧
      (src + L ≤ dst ∨ dst + L ≤ src) ∧
      PathIntAt mem src 4 L z ∧
      Num.Fits 4 L (-z)
  post args mem ret out :=
    ∃ src dst L,
      args = [src, dst, L] ∧ ret = 0 ∧
      PathIntAt out dst 4 L (-z) ∧
      (∀ a, a < dst ∨ dst + L ≤ a → out a = mem a)
  cost args _ := 45 * args.getD 2 0 + 20

private theorem selNegCopyTo_signed_eq {L u v c : ℕ} {z : ℤ}
    (hu : u < capacity 4 L) (hv : v < capacity 4 L) (hc : c ≤ 1)
    (hsum : u + v + capacity 4 L * c = capacity 4 L)
    (hz : signedVal 4 L u = z) (hfit : Num.Fits 4 L (-z)) :
    signedVal 4 L v = -z := by
  rw [← hz] at hfit ⊢
  unfold Num.Fits at hfit
  unfold signedVal at hfit ⊢
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
  · simp only [mul_zero, add_zero] at hsum
    split_ifs at hfit ⊢ <;> omega
  · simp only [mul_one] at hsum
    have hu0 : u = 0 := by omega
    have hv0 : v = 0 := by omega
    subst hu0; subst hv0
    have hp := capacity_pos 4 L
    split_ifs <;> omega

private lemma runs_loop_f {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st : State} (he : e.eval w st = some 0) :
    Runs w p ω (.loop e body) st .normal st (e.size + 1) :=
  runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩)

private lemma runs_loop_t {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st st₁ st₂ : State} {o : Outcome} {c₁ c₂ : ℕ} {v : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h1 : Runs w p ω body st .normal st₁ c₁)
    (h2 : Runs w p ω (.loop e body) st₁ o st₂ c₂) :
    Runs w p ω (.loop e body) st o st₂ (e.size + c₁ + c₂ + 1) :=
  runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st₁, c₁, c₂, he, hv, h1, h2, rfl⟩))

theorem selNegCopyTo_meetsContract {w proc : ℕ} {z : ℤ} {p : Program}
    (hp : p.procs[proc]? = some selNegCopyToBody) :
    MeetsContract w p proc (selNegCopyToContract w z) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _ hpre
  obtain ⟨src, dst, L, rfl, hw16, hsrcW, hdstW, hdisj, hP, hFit⟩ := hpre
  have hStep :
      ∀ (rem : ℕ) (st : State),
        rem ≤ L →
        st.regs 0 = src → st.regs 1 = dst → st.regs 2 = L →
        st.regs 4 = L - rem → st.regs 3 ≤ 1 →
        (∀ i < L - rem, st.mem (dst + i) < 16) →
        unsignedVal mem src 4 (L - rem) + unsignedVal st.mem dst 4 (L - rem) +
            capacity 4 (L - rem) * st.regs 3 = capacity 4 (L - rem) →
        (∀ a, a < dst ∨ dst + L ≤ a → st.mem a = mem a) →
        ∃ out c,
          Runs w p ω
            (forUp 4 (.reg 2)
              (.assign 5 (.bin .add (.bin .sub (.const 15) (.load (.bin .add (.reg 0) (.reg 4))))
                (.reg 3)) ;;
               .store (.bin .add (.reg 1) (.reg 4)) (.bin .mod (.reg 5) (.const 16)) ;;
               .assign 3 (.bin .div (.reg 5) (.const 16))))
            st .normal out c ∧
          out.regs 0 = src ∧ out.regs 1 = dst ∧ out.regs 2 = L ∧ out.regs 3 ≤ 1 ∧
          (∀ i < L, out.mem (dst + i) < 16) ∧
          unsignedVal mem src 4 L + unsignedVal out.mem dst 4 L +
              capacity 4 L * out.regs 3 = capacity 4 L ∧
          (∀ a, a < dst ∨ dst + L ≤ a → out.mem a = mem a) ∧
          c ≤ 45 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro st _ r0 r1 r2 r4 r3 hv hsum hfr
      rw [Nat.sub_zero] at r4 hv hsum
      refine ⟨st, _, runs_loop_f (by simp [Expr.eval, BinOp.eval, r4, r2, show 0 < 2 ^ w by omega]),
        r0, r1, r2, r3, hv, hsum, hfr, by simp [Expr.size]⟩
    | succ rem' ih =>
      intro st hrem r0 r1 r2 r4 r3 hv hsum hfr
      set j := L - (rem' + 1)
      have hjLt : j < L := by omega
      have hsrcMem : st.mem (src + j) = mem (src + j) := hfr (src + j) (by omega)
      have haLt : mem (src + j) < 16 := hP.1 j hjLt
      set d := (15 - mem (src + j)) + st.regs 3
      have hdLt : d < 2 ^ w := by omega
      have hbody :
          ∃ st1 c1,
            Runs w p ω
              ((.assign 5 (.bin .add (.bin .sub (.const 15) (.load (.bin .add (.reg 0) (.reg 4))))
                  (.reg 3)) ;;
                .store (.bin .add (.reg 1) (.reg 4)) (.bin .mod (.reg 5) (.const 16)) ;;
                .assign 3 (.bin .div (.reg 5) (.const 16))) ;;
               .assign 4 (.bin .add (.reg 4) (.const 1)))
              st .normal st1 c1 ∧
            st1.regs 0 = src ∧ st1.regs 1 = dst ∧ st1.regs 2 = L ∧
            st1.regs 4 = j + 1 ∧ st1.regs 3 = d / 16 ∧
            st1.mem = Function.update st.mem (dst + j) (d % 16) ∧ c1 ≤ 38 := by
        let rg5 := Function.update st.regs 5 d
        let m1 := Function.update st.mem (dst + j) (d % 16)
        let rg3 := Function.update rg5 3 (d / 16)
        let rg4 := Function.update rg3 4 (j + 1)
        have rA : Runs w p ω
            (.assign 5 (.bin .add (.bin .sub (.const 15) (.load (.bin .add (.reg 0) (.reg 4))))
              (.reg 3))) st .normal ⟨st.mem, rg5, st.pos⟩ _ :=
          runs_assign_iff.mpr ⟨d, by
            simp [Expr.eval, BinOp.eval, r0, r4, hsrcMem, show src + j < 2 ^ w by omega,
              show 15 < 2 ^ w by omega, show 15 - mem (src + j) < 2 ^ w by omega, hdLt, d], rfl, rfl, rfl⟩
        have rB : Runs w p ω
            (.store (.bin .add (.reg 1) (.reg 4)) (.bin .mod (.reg 5) (.const 16)))
            ⟨st.mem, rg5, st.pos⟩ .normal ⟨m1, rg5, st.pos⟩ _ :=
          runs_store_iff.mpr ⟨dst + j, d % 16,
            by simp [Expr.eval, BinOp.eval, rg5, r1, r4, show dst + j < 2 ^ w by omega],
            by simp [Expr.eval, BinOp.eval, rg5, hw16, show d % 16 < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have rC : Runs w p ω (.assign 3 (.bin .div (.reg 5) (.const 16)))
            ⟨m1, rg5, st.pos⟩ .normal ⟨m1, rg3, st.pos⟩ _ :=
          runs_assign_iff.mpr ⟨d / 16,
            by simp [Expr.eval, BinOp.eval, rg5, hw16, show d / 16 < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have rD : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.const 1)))
            ⟨m1, rg3, st.pos⟩ .normal ⟨m1, rg4, st.pos⟩ _ :=
          runs_assign_iff.mpr ⟨j + 1,
            by simp [Expr.eval, BinOp.eval, rg3, rg5, r4,
              show 1 < 2 ^ w by omega, show j + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
        have rABCD := runs_seq_iff.mpr (Or.inr ⟨_, _, _,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, rB, rC, rfl⟩), rfl⟩), rD, rfl⟩)
        refine ⟨⟨m1, rg4, st.pos⟩, _, rABCD,
          by simp [rg4, rg3, rg5, r0], by simp [rg4, rg3, rg5, r1],
          by simp [rg4, rg3, rg5, r2], by simp [rg4],
          by simp [rg4, rg3], rfl, by simp [Expr.size]⟩
      obtain ⟨st1, c1, hr1, s0, s1, s2, s4, s3, smem, hc1⟩ := hbody
      have hj1 : L - rem' = j + 1 := by omega
      have hv1 : ∀ i < j + 1, st1.mem (dst + i) < 16 := by
        intro i hi
        rw [smem]
        by_cases hEq : i = j
        · subst hEq; simp [Nat.mod_lt _ (by decide : 0 < 16)]
        · rw [Function.update_of_ne (by omega)]; exact hv i (by omega)
      have huv1 : unsignedVal st1.mem dst 4 (j + 1) =
          unsignedVal st.mem dst 4 j + capacity 4 j * (d % 16) := by
        rw [unsignedVal_append_one, smem, Function.update_self]
        congr 1
        exact unsignedVal_congr fun i hi => Function.update_of_ne (by omega) _ _
      have hsum1 : unsignedVal mem src 4 (j + 1) + unsignedVal st1.mem dst 4 (j + 1) +
          capacity 4 (j + 1) * st1.regs 3 = capacity 4 (j + 1) := by
        rw [unsignedVal_append_one, huv1, s3, capacity_succ]
        have hdm : mem (src + j) + (d % 16) + 16 * (d / 16) = 15 + st.regs 3 := by omega
        have hb4 : base 4 = 16 := rfl
        rw [hb4]
        nlinarith
      have hfr1 : ∀ a, a < dst ∨ dst + L ≤ a → st1.mem a = mem a := fun a ha => by
        rw [smem, Function.update_of_ne (by omega)]; exact hfr a ha
      obtain ⟨out, c2, hr2, o0, o1, o2, o3, ov, osum, ofr, hc2⟩ :=
        ih st1 (by omega) s0 s1 s2 (by rw [hj1]; exact s4) (by omega)
          (by rw [hj1]; exact hv1) (by rw [hj1]; exact hsum1) hfr1
      refine ⟨out, _, runs_loop_t (v := 1)
        (by simp [Expr.eval, BinOp.eval, r4, r2, hjLt, show 1 < 2 ^ w by omega])
        (by omega) hr1 hr2, o0, o1, o2, o3, ov, osum, ofr, ?_⟩
      simp [Expr.size]; omega
  let s0 := startState [src, dst, L] mem pos
  let rg3 := Function.update s0.regs 3 1
  let rg4 := Function.update rg3 4 0
  have rInit3 : Runs w p ω (.assign 3 (.const 1)) s0 .normal ⟨mem, rg3, pos⟩ 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, show 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have rInit4 : Runs w p ω (.assign 4 (.const 0)) ⟨mem, rg3, pos⟩ .normal ⟨mem, rg4, pos⟩ 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨out, cL, hrL, _, _, _, o3, ov, osum, ofr, hcL⟩ :=
    hStep L ⟨mem, rg4, pos⟩ le_rfl
      (by simp [rg4, rg3, s0, startState]) (by simp [rg4, rg3, s0, startState])
      (by simp [rg4, rg3, s0, startState]) (by simp [rg4])
      (by dsimp only [rg4, rg3]; rw [Function.update_of_ne (by decide), Function.update_self])
      (fun _ h => by rw [Nat.sub_self] at h; omega)
      (by simp [unsignedVal, capacity, rg4, rg3]) (fun _ _ => rfl)
  have rRet : Runs w p ω (.ret (.const 0)) out (.returned 0) out 2 :=
    runs_ret_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have rFull : Runs w p ω selNegCopyToBody s0 (.returned 0) out _ :=
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, rInit3,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, rInit4, hrL, rfl⟩), rRet, rfl⟩), rfl⟩)
  refine ⟨.returned 0, out, _, rFull,
    ⟨src, dst, L, rfl, rfl, ⟨ov,
      selNegCopyTo_signed_eq (unsignedVal_lt hP.1) (unsignedVal_lt ov) o3 osum hP.2 hFit⟩, ofr⟩, ?_⟩
  simp [selNegCopyToContract]; omega

/-! ## 3. Single-edge gradient copy from solver state (`selCopyG0OneBody`) -/

/-- Copy `modelPre.chain.g e` (`Lk` limbs) into `g0Ptr + e * Lk` directly from the solver state
`(slots, edgeRecords, treeHeap)`, using zero scratch.
Arguments: `[slots, edgeRecords, treeHeap, g0Ptr, e, Lk]` (`reg 0..5`). -/
def selCopyG0OneBody (copyTo negCopyTo : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.reg 4))) ;;
  .cond (.reg 6)
    (.assign 7 (.load (.bin .add (.reg 2) (.const 3))) ;;
     .assign 8 (.load (.bin .add (.reg 2) (.const 4))) ;;
     .assign 9 (.bin .add (.bin .add (.reg 8)
       (.bin .mul (.bin .add (.const 13) (.bin .mul (.const 9) (.reg 7))) (.reg 6))) (.const 10)) ;;
     .assign 10 (.load (.bin .add (.reg 9) (.const 1))) ;;
     .cond (.reg 10)
       (.call 11 copyTo [.bin .add (.reg 9) (.const 2),
         .bin .add (.reg 3) (.bin .mul (.reg 4) (.reg 5)), .reg 5])
       (.call 11 negCopyTo [.bin .add (.reg 9) (.const 2),
         .bin .add (.reg 3) (.bin .mul (.reg 4) (.reg 5)), .reg 5]))
    (.assign 7 (.load (.bin .add (.reg 1) (.reg 4))) ;;
     .call 11 copyTo [.bin .add (.reg 7) (.const 2),
       .bin .add (.reg 3) (.bin .mul (.reg 4) (.reg 5)), .reg 5]) ;;
  .ret (.const 0)

theorem selCopyG0OneBody_noRand (copyTo negCopyTo : ℕ) :
    (selCopyG0OneBody copyTo negCopyTo).NoRand := by
  simp [selCopyG0OneBody, Stmt.NoRand]

/-- Raw-memory premise guaranteeing that `(slots, edgeRecords, treeHeap)` holds a valid `Lk`-limb
representation of `val : ℤ` (with `Fits 4 Lk val` and `Fits 4 Lk (-val)`) for internal edge `e`. -/
def SolverEdgeGradReadable (w : ℕ) (mem : ℕ → ℕ)
    (slots edgeRecords treeHeap g0Ptr eCap e Lk : ℕ) (val : ℤ) : Prop :=
  16 < 2 ^ w ∧ 0 < Lk ∧ e < eCap ∧
  slots + e < 2 ^ w ∧ edgeRecords + e < 2 ^ w ∧
  treeHeap + 5 < 2 ^ w ∧ g0Ptr + eCap * Lk < 2 ^ w ∧
  mem (slots + e) < 2 ^ w ∧
  Num.Fits 4 Lk val ∧ Num.Fits 4 Lk (-val) ∧
  (mem (slots + e) = 0 →
    let recPtr := mem (edgeRecords + e)
    recPtr + 2 + Lk < 2 ^ w ∧
    (recPtr + 2 + Lk ≤ g0Ptr + e * Lk ∨ g0Ptr + (e + 1) * Lk ≤ recPtr + 2) ∧
    PathIntAt mem (recPtr + 2) 4 Lk val) ∧
  (mem (slots + e) ≠ 0 →
    let s := mem (slots + e)
    let K := mem (treeHeap + 3)
    let nb := mem (treeHeap + 4)
    let valPtr := nb + (13 + 9 * K) * s + 10
    Lk ≤ K ∧ K < 2 ^ w ∧ nb < 2 ^ w ∧
    13 + 9 * K < 2 ^ w ∧ (13 + 9 * K) * s < 2 ^ w ∧
    valPtr + 2 + Lk < 2 ^ w ∧
    (valPtr + 2 + Lk ≤ g0Ptr + e * Lk ∨ g0Ptr + (e + 1) * Lk ≤ valPtr + 2) ∧
    ∃ (fwd : Bool) (gRaw : ℤ),
      mem (valPtr + 1) = (if fwd then 1 else 0) ∧
      PathIntAt mem (valPtr + 2) 4 K gRaw ∧
      (if fwd then gRaw else -gRaw) = val)

/-- `SolverEdgeGradReadable` is preserved by any memory update that agrees on `slots + e`,
`edgeRecords + e`, the off-tree record, and the tree arena (in particular any write strictly inside
`[g0Ptr, g0Ptr + eCap * Lk)` when those live outside `[g0Ptr, g0Ptr + eCap * Lk)`). -/
theorem SolverEdgeGradReadable.of_agree {w : ℕ} {mem mem' : ℕ → ℕ}
    {slots edgeRecords treeHeap g0Ptr eCap e Lk : ℕ} {val : ℤ}
    (h : SolverEdgeGradReadable w mem slots edgeRecords treeHeap g0Ptr eCap e Lk val)
    (hs : mem' (slots + e) = mem (slots + e))
    (hr : mem (slots + e) = 0 →
      mem' (edgeRecords + e) = mem (edgeRecords + e) ∧
      ∀ i < Lk, mem' (mem (edgeRecords + e) + 2 + i) = mem (mem (edgeRecords + e) + 2 + i))
    (ht : mem (slots + e) ≠ 0 →
      mem' (treeHeap + 3) = mem (treeHeap + 3) ∧
      mem' (treeHeap + 4) = mem (treeHeap + 4) ∧
      let valPtr := mem (treeHeap + 4) + (13 + 9 * mem (treeHeap + 3)) * mem (slots + e) + 10
      mem' (valPtr + 1) = mem (valPtr + 1) ∧
      ∀ i < mem (treeHeap + 3), mem' (valPtr + 2 + i) = mem (valPtr + 2 + i)) :
    SolverEdgeGradReadable w mem' slots edgeRecords treeHeap g0Ptr eCap e Lk val := by
  obtain ⟨hw16, hLk, heCap, hSW, hRW, hTW, hGW, hSV, hF1, hF2, hOff, hTree⟩ := h
  refine ⟨hw16, hLk, heCap, hSW, hRW, hTW, hGW, hs ▸ hSV, hF1, hF2, fun h0 => ?_, fun hne => ?_⟩
  · have h0' : mem (slots + e) = 0 := hs ▸ h0
    obtain ⟨hrec, hcopy⟩ := hr h0'
    obtain ⟨hW, hD, hP⟩ := hOff h0'
    refine ⟨hrec ▸ hW, hrec ▸ hD, ?_⟩
    rw [hrec]
    exact hP.congr hcopy
  · have hne' : mem (slots + e) ≠ 0 := hs ▸ hne
    obtain ⟨hK, hnb, hfwd, hcopy⟩ := ht hne'
    obtain ⟨hLK, hKW, hnbW, hstrW, hmulW, hVPW, hD, fwd, gRaw, hf, hP, hEq⟩ := hTree hne'
    refine ⟨hK ▸ hLK, hK ▸ hKW, hnb ▸ hnbW, hK ▸ hstrW, ?_, ?_, ?_, fwd, gRaw, ?_, ?_, hEq⟩
    · rw [hK, hs]; exact hmulW
    · rw [hK, hnb, hs]; exact hVPW
    · rw [hK, hnb, hs]; exact hD
    · rw [hK, hnb, hs]; exact hfwd.trans hf
    · rw [hK, hnb, hs]; exact hP.congr (fun i hi => hcopy i hi)

/-- Extract `SolverEdgeGradReadable` for any edge `e ∈ (model.chain.G 0).E` directly from
`solverStateRep.rep` whenever `[g0Ptr, g0Ptr + eCap * L)` lies outside `Rrep.foot` and the integer
gradient fits symmetrically in `L` limbs. -/
theorem solverEdgeGradReadable_of_rep
    {w L P m V psi k epsExp drainUnit root g0Ptr eCap e : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hw16 : 16 < 2 ^ w) (hLpos : 0 < L) (he : e ∈ (model.chain.G 0).E)
    (heCap : e < eCap)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hFootW : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < 2 ^ w)
    (hFootOffG0 : ∀ a, g0Ptr ≤ a → a < g0Ptr + eCap * L →
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a)
    (hg0W : g0Ptr + eCap * L < 2 ^ w)
    (hgEq : model.chain.g e = model.extg (model.intToExt e))
    (hFit : ∀ z : ℤ, (z : ℝ) / (2 : ℝ) ^ P = model.chain.g e → Num.Fits 4 L z ∧ Num.Fits 4 L (-z)) :
    ∃ z : ℤ, (z : ℝ) / (2 : ℝ) ^ P = model.chain.g e ∧
      SolverEdgeGradReadable w mem tok.slots tok.edgeRecords tok.treeHeap g0Ptr eCap e L z := by
  obtain ⟨_, _, _, _, hFresh, _, _, ⟨hEIntCap, _, _, _⟩, _, _, _, _,
    ⟨hTreeTokEq, hArena, _⟩, hAcc, _, _, _, _, hWire, hTags⟩ := hrep
  obtain ⟨hOwn, _, _, _, _, _, _, _, _, hSlotsTag, _, _, _, hRecsTag, _, _, _, hRecBlkTag, _⟩ :=
    hTags
  have heInt : e < tok.intCap := hEIntCap e he
  obtain ⟨he2i, heExt⟩ := hFresh.hRight e he
  set eExt := model.intToExt e
  have hOri := hWire.2.2.2.2 eExt heExt
  have hAccE := (hAcc.1 eExt heExt).2.2
  dsimp only at hOri hAccE
  rw [he2i] at hOri hAccE
  have hSlotsW : tok.slots + e < 2 ^ w :=
    hFootW _ (Or.inl (hOwn _ (by rw [hSlotsTag e heInt]; omega)))
  have hRecsW : tok.edgeRecords + e < 2 ^ w :=
    hFootW _ (Or.inl (hOwn _ (by rw [hRecsTag e heInt]; omega)))
  have hFootTree : ∀ a, tok.treeHeap ≤ a → a < arenaEnd tok.treeHeap tok.tree.n L →
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a := fun a h1 h2 =>
    Or.inr (Or.inl ⟨h1, by rw [hTreeTokEq]; exact h2⟩)
  have hRecPos : 0 < recW (treeLimbs L) * (2 * tok.tree.n + 1) :=
    Nat.mul_pos (by unfold recW treeLimbs; omega) (by omega)
  have hArenaEndW : arenaEnd tok.treeHeap tok.tree.n L ≤ 2 ^ w := by
    have hlt : tok.treeHeap < arenaEnd tok.treeHeap tok.tree.n L := by
      unfold arenaEnd arenaNb; omega
    have hlast := hFootW (arenaEnd tok.treeHeap tok.tree.n L - 1)
      (hFootTree _ (by omega) (by omega))
    omega
  have hTreeHdrW : tok.treeHeap + 5 < 2 ^ w := by
    have h5 : tok.treeHeap + 5 < arenaEnd tok.treeHeap tok.tree.n L := by
      unfold arenaEnd arenaNb; omega
    omega
  have hDisjInterval : ∀ a len, 0 < len →
      (∀ x, a ≤ x → x < a + len →
        (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok x) →
      a + len ≤ g0Ptr + e * L ∨ g0Ptr + (e + 1) * L ≤ a := by
    intro a len hlen hft
    have heMul : e * L + L ≤ eCap * L := by
      have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heCap)
      rwa [Nat.succ_mul] at this
    have he1 : (e + 1) * L = e * L + L := by ring
    by_contra h
    push Not at h
    set x := max a (g0Ptr + e * L)
    have hx1 : a ≤ x ∧ x < a + len := ⟨le_max_left _ _, by omega⟩
    have hx2 : g0Ptr ≤ x ∧ x < g0Ptr + eCap * L := ⟨by omega, by omega⟩
    exact hFootOffG0 x hx2.1 hx2.2 (hft x hx1.1 hx1.2)
  by_cases hInF : e ∈ model.chain.toTreeChain.chainTree.E
  · simp only [hInF, ↓reduceIte] at hOri hAccE
    obtain ⟨_, hEdgeSlot, _, _, val, _, hfp, _, _, _⟩ := hAccE
    have hgVal : (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.chain.g e := by
      rw [hgEq]; exact (hOri val hfp).1
    obtain ⟨hFit1, hFit2⟩ := hFit val.originalGradient hgVal
    set s := mem (tok.slots + e)
    have hsLe : s ≤ 2 * tok.tree.n := by
      unfold isEdgeSlot at hEdgeSlot; exact Nat.le_of_lt hEdgeSlot.2
    have hsPos : 0 < s := by unfold isEdgeSlot at hEdgeSlot; omega
    have hsNe : s ≠ 0 := by omega
    obtain ⟨t, _, hpt⟩ := List.mem_flatMap.mp hfp
    obtain ⟨vRaw, hRawEq, hRawGrad⟩ :=
      evalPairs_some_originalGradient tok.tree.splay t false _ hpt
    have hNode := hArena.nodes s hsLe
    have hValAt := hNode.2.2.2.2.2.2.1
    rw [hRawEq] at hValAt
    obtain ⟨_, _, _, _, hEdgeAt⟩ := hValAt
    set K := treeLimbs L
    set nb := arenaNb tok.treeHeap tok.tree.n
    have hKeq : mem (tok.treeHeap + 3) = K := hArena.hK
    have hnbEq : mem (tok.treeHeap + 4) = nb := hArena.hnb
    have hLK : L ≤ K := by unfold K treeLimbs; omega
    have hStride : (pathLayout 4 K).nodeStride = 13 + 9 * K := by
      rw [recW_stride]; rfl
    have hValPtrEq : (pathLayout 4 K).nodeAddr nb s + NodeLayout.OFF_VAL + 4 =
        nb + (13 + 9 * K) * s + 10 := by
      unfold NodeLayout.nodeAddr NodeLayout.OFF_VAL; rw [hStride]
    rw [hValPtrEq] at hEdgeAt
    set valPtr := nb + (13 + 9 * K) * s + 10
    have hRecEnd : valPtr + 2 + L < arenaEnd tok.treeHeap tok.tree.n L := by
      have hmul : (13 + 9 * K) * s + (13 + 9 * K) ≤ (13 + 9 * K) * (2 * tok.tree.n + 1) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (Nat.succ_le_succ hsLe)
      have h1 : 12 + L < 13 + 9 * K := by unfold K treeLimbs; omega
      have h2 : arenaEnd tok.treeHeap tok.tree.n L =
          nb + (13 + 9 * K) * (2 * tok.tree.n + 1) := by
        unfold arenaEnd K recW nb; rfl
      dsimp only [valPtr]; omega
    have hFootVP : ∀ x, valPtr + 2 ≤ x → x < valPtr + 2 + L →
        (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok x := fun x h1 h2 =>
      hFootTree x (by have hnbGe : tok.treeHeap ≤ nb := by unfold nb arenaNb; omega
                      dsimp only [valPtr] at h1; omega) (by omega)
    have hDisjVP := hDisjInterval (valPtr + 2) L hLpos hFootVP
    have hStrLeEnd : 13 + 9 * K ≤ recW (treeLimbs L) * (2 * tok.tree.n + 1) := by
      have hmul := Nat.mul_le_mul_left (recW (treeLimbs L)) (show 1 ≤ 2 * tok.tree.n + 1 by omega)
      simp only [Nat.mul_one, recW] at hmul; exact hmul
    have hAEnd : arenaEnd tok.treeHeap tok.tree.n L = nb + recW (treeLimbs L) * (2 * tok.tree.n + 1) := rfl
    have hsLtW : s < 2 ^ w := by
      have : 4 * tok.tree.n + 8 ≤ nb := by unfold nb arenaNb; omega
      omega
    have hKLtW : K < 2 ^ w := by omega
    have hnbLtW : nb < 2 ^ w := by omega
    have hStrLtW : 13 + 9 * K < 2 ^ w := by
      have : 8 ≤ nb := by unfold nb arenaNb; omega
      have : 13 + 9 * K < arenaEnd tok.treeHeap tok.tree.n L := by rw [hAEnd]; omega
      omega
    have hMulLtW : (13 + 9 * K) * s < 2 ^ w := by
      have : (13 + 9 * K) * s ≤ valPtr := by dsimp only [valPtr]; omega
      omega
    have hVPLtW : valPtr + 2 + L < 2 ^ w := by omega
    refine ⟨val.originalGradient, hgVal, hw16, hLpos, heCap, hSlotsW, hRecsW, hTreeHdrW, hg0W,
      hsLtW, hFit1, hFit2, fun h0 => absurd h0 hsNe, fun _ => ?_⟩
    rw [hKeq, hnbEq]
    exact ⟨hLK, hKLtW, hnbLtW, hStrLtW, hMulLtW, hVPLtW,
      hDisjVP, vRaw.forward, vRaw.gradient, hEdgeAt.2.1, hEdgeAt.2.2.1, hRawGrad⟩
  · simp only [hInF, ↓reduceIte] at hOri hAccE
    obtain ⟨hs0, val, _, hEdgeAt, _, _, _, _⟩ := hAccE
    obtain ⟨hfwd, hgVal, _⟩ := hOri val hEdgeAt
    have hgVal' : (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.chain.g e := by
      rw [hgEq]; exact hgVal
    obtain ⟨hFit1, hFit2⟩ := hFit val.originalGradient hgVal'
    have hGradEq : val.gradient = val.originalGradient := by
      simp [PathEdgeValue.originalGradient, hfwd]
    set recPtr := mem (tok.edgeRecords + e)
    have hRecTagE := (hRecBlkTag eExt heExt).2
    rw [he2i] at hRecTagE
    have hRecFoot : ∀ j < 2 + 4 * L,
        (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok (recPtr + j) :=
      fun j hj => Or.inl (hOwn _ (by rw [hRecTagE hInF j hj]; omega))
    have hRecEndW : recPtr + 2 + L < 2 ^ w := by
      have h1 := hFootW (recPtr + (2 + 4 * L - 1)) (hRecFoot (2 + 4 * L - 1) (by omega))
      omega
    have hDisjRec := hDisjInterval (recPtr + 2) L hLpos fun x h1 h2 => by
      have hx := hRecFoot (x - recPtr) (by omega)
      rwa [Nat.add_sub_of_le (by omega)] at hx
    refine ⟨val.originalGradient, hgVal', hw16, hLpos, heCap, hSlotsW, hRecsW, hTreeHdrW, hg0W,
      by rw [hs0]; omega, hFit1, hFit2, fun _ => ?_, fun hne => absurd hs0 hne⟩
    refine ⟨hRecEndW, hDisjRec, hGradEq ▸ hEdgeAt.2.2.1⟩

/-- Contract for `selCopyG0OneBody copyTo negCopyTo` (`[slots, edgeRecords, treeHeap, g0Ptr, e, Lk] → 0`). -/
def selCopyG0OneContract (w eCap : ℕ) (val : ℤ) : Contract where
  pre args mem :=
    ∃ slots edgeRecords treeHeap g0Ptr e Lk,
      args = [slots, edgeRecords, treeHeap, g0Ptr, e, Lk] ∧
      SolverEdgeGradReadable w mem slots edgeRecords treeHeap g0Ptr eCap e Lk val
  post args mem ret out :=
    ∃ slots edgeRecords treeHeap g0Ptr e Lk,
      args = [slots, edgeRecords, treeHeap, g0Ptr, e, Lk] ∧ ret = 0 ∧
      PathIntAt out (g0Ptr + e * Lk) 4 Lk val ∧
      (∀ a, a < g0Ptr + e * Lk ∨ g0Ptr + (e + 1) * Lk ≤ a → out a = mem a)
  cost args _ := 45 * args.getD 5 0 + 120

set_option maxHeartbeats 600000 in
theorem selCopyG0One_meetsContract {w proc copyTo negCopyTo eCap : ℕ} {val : ℤ} {p : Program}
    (hp : p.procs[proc]? = some (selCopyG0OneBody copyTo negCopyTo))
    (hCopy : MeetsContract w p copyTo (copyLimbsToContract w))
    (hNeg : ∀ z : ℤ, MeetsContract w p negCopyTo (selNegCopyToContract w z)) :
    MeetsContract w p proc (selCopyG0OneContract w eCap val) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _ hpre
  obtain ⟨slots, edgeRecords, treeHeap, g0Ptr, e, Lk, rfl, hRd⟩ := hpre
  obtain ⟨hw16, hLk, heCap, hSW, hRW, hTW, hGW, hSV, hF1, hF2, hOff, hTree⟩ := hRd
  have heMul : e * Lk + Lk ≤ eCap * Lk := by
    have := Nat.mul_le_mul_right Lk (Nat.succ_le_of_lt heCap)
    rwa [Nat.succ_mul] at this
  have he1 : (e + 1) * Lk = e * Lk + Lk := by ring
  have hdstW : g0Ptr + e * Lk + Lk < 2 ^ w := by omega
  have heLkW : e * Lk < 2 ^ w := by omega
  let s0 := startState [slots, edgeRecords, treeHeap, g0Ptr, e, Lk] mem pos
  let rg6 := Function.update s0.regs 6 (mem (slots + e))
  have rLoadS : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.reg 4)))) s0 .normal
      ⟨mem, rg6, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨mem (slots + e),
      by simp [Expr.eval, BinOp.eval, s0, startState, hSW], rfl, rfl, by simp [Expr.size]⟩
  by_cases hs0 : mem (slots + e) = 0
  · obtain ⟨hRecW, hDisj, hP⟩ := hOff hs0
    let rg7 := Function.update rg6 7 (mem (edgeRecords + e))
    have rLoadR : Runs w p ω (.assign 7 (.load (.bin .add (.reg 1) (.reg 4))))
        ⟨mem, rg6, pos⟩ .normal ⟨mem, rg7, pos⟩ 5 :=
      runs_assign_iff.mpr ⟨mem (edgeRecords + e),
        by simp [Expr.eval, BinOp.eval, rg6, s0, startState, hRW], rfl, rfl, by simp [Expr.size]⟩
    obtain ⟨bC, hbC, oC, stC, cC, hrC, hpC, hcC⟩ :=
      hCopy [mem (edgeRecords + e) + 2, g0Ptr + e * Lk, Lk] mem pos ω
        (by simp only [List.mem_cons, List.not_mem_nil, or_false]
            rintro v (rfl | rfl | rfl) <;> omega)
        ⟨mem (edgeRecords + e) + 2, g0Ptr + e * Lk, Lk, rfl, by omega, by omega, hdstW,
          by rcases hDisj with h | h <;> [left; right] <;> omega,
          fun i hi => by have := hP.1 i hi; unfold base at this; omega⟩
    obtain ⟨_, hcpC, hfrC⟩ := hpC
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hcpC hfrC
    let rg11 := Function.update rg7 11 oC.value
    have rCallC : Runs w p ω
        (.call 11 copyTo [.bin .add (.reg 7) (.const 2),
          .bin .add (.reg 3) (.bin .mul (.reg 4) (.reg 5)), .reg 5])
        ⟨mem, rg7, pos⟩ .normal ⟨stC.mem, rg11, stC.pos⟩ (cC + 10) :=
      runs_call_iff.mpr ⟨[mem (edgeRecords + e) + 2, g0Ptr + e * Lk, Lk], bC, oC, stC, cC,
        by simp [evalArgs, Expr.eval, BinOp.eval, rg7, rg6, s0, startState,
          show 2 < 2 ^ w by omega, show mem (edgeRecords + e) + 2 < 2 ^ w by omega,
          heLkW, show g0Ptr + e * Lk < 2 ^ w by omega],
        hbC, hrC, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    have rElse := runs_seq_iff.mpr (Or.inr ⟨_, _, _, rLoadR, rCallC, rfl⟩)
    have rRet : Runs w p ω (.ret (.const 0)) ⟨stC.mem, rg11, stC.pos⟩
        (.returned 0) ⟨stC.mem, rg11, stC.pos⟩ 2 :=
      runs_ret_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
    refine ⟨.returned 0, ⟨stC.mem, rg11, stC.pos⟩, _,
      by unfold selCopyG0OneBody
         exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, rLoadS,
           runs_seq_iff.mpr (Or.inr ⟨_, _, _,
             runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, rg6, hs0], rElse, rfl⟩,
             rRet, rfl⟩), rfl⟩),
      ⟨slots, edgeRecords, treeHeap, g0Ptr, e, Lk, rfl, rfl, hP.congr hcpC,
        fun a ha => hfrC a (by omega)⟩, ?_⟩
    simp only [selCopyG0OneContract, copyLimbsToContract, List.getD_cons_zero,
      List.getD_cons_succ, Expr.size] at hcC ⊢
    omega
  · obtain ⟨hLK, hKW, hnbW, hStrW, hMulW, hVPW, hDisj, fwd, gRaw, hfwd, hP, hEq⟩ := hTree hs0
    set s := mem (slots + e)
    set K := mem (treeHeap + 3)
    set nb := mem (treeHeap + 4)
    set valPtr := nb + (13 + 9 * K) * s + 10
    have hP_L : PathIntAt mem (valPtr + 2) 4 Lk gRaw := by
      have hFitRaw : Num.Fits 4 Lk gRaw := by
        cases fwd
        · simp only [Bool.false_eq_true, ↓reduceIte] at hEq
          have : gRaw = -val := by omega
          rw [this]; exact hF2
        · simp only [↓reduceIte] at hEq
          rw [hEq]; exact hF1
      exact pathIntAt_trunc hLK hP hFitRaw
    let rg7 := Function.update rg6 7 K
    let rg8 := Function.update rg7 8 nb
    let rg9 := Function.update rg8 9 valPtr
    let rg10 := Function.update rg9 10 (mem (valPtr + 1))
    have rK : Runs w p ω (.assign 7 (.load (.bin .add (.reg 2) (.const 3))))
        ⟨mem, rg6, pos⟩ .normal ⟨mem, rg7, pos⟩ 5 :=
      runs_assign_iff.mpr ⟨K, by
        simp [Expr.eval, BinOp.eval, rg6, s0, startState, show 3 < 2 ^ w by omega,
          show treeHeap + 3 < 2 ^ w by omega, K], rfl, rfl, by simp [Expr.size]⟩
    have rNb : Runs w p ω (.assign 8 (.load (.bin .add (.reg 2) (.const 4))))
        ⟨mem, rg7, pos⟩ .normal ⟨mem, rg8, pos⟩ 5 :=
      runs_assign_iff.mpr ⟨nb, by
        simp [Expr.eval, BinOp.eval, rg7, rg6, s0, startState, show 4 < 2 ^ w by omega,
          show treeHeap + 4 < 2 ^ w by omega, nb], rfl, rfl, by simp [Expr.size]⟩
    have rVP : Runs w p ω
        (.assign 9 (.bin .add (.bin .add (.reg 8)
          (.bin .mul (.bin .add (.const 13) (.bin .mul (.const 9) (.reg 7))) (.reg 6))) (.const 10)))
        ⟨mem, rg8, pos⟩ .normal ⟨mem, rg9, pos⟩ 12 :=
      runs_assign_iff.mpr ⟨valPtr, by
        simp [Expr.eval, BinOp.eval, rg8, rg7, rg6, s0, startState, show 9 < 2 ^ w by omega,
          show 13 < 2 ^ w by omega, show 10 < 2 ^ w by omega, show 9 * K < 2 ^ w by omega,
          hStrW, hMulW, show nb + (13 + 9 * K) * s < 2 ^ w by omega,
          show valPtr < 2 ^ w by omega, valPtr, s], rfl, rfl, by simp [Expr.size]⟩
    have rFwd : Runs w p ω (.assign 10 (.load (.bin .add (.reg 9) (.const 1))))
        ⟨mem, rg9, pos⟩ .normal ⟨mem, rg10, pos⟩ 5 :=
      runs_assign_iff.mpr ⟨mem (valPtr + 1), by
        simp [Expr.eval, BinOp.eval, rg9, show 1 < 2 ^ w by omega,
          show valPtr + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
    have hInner : ∃ mem' pos' cI,
        Runs w p ω
          (.cond (.reg 10)
            (.call 11 copyTo [.bin .add (.reg 9) (.const 2),
              .bin .add (.reg 3) (.bin .mul (.reg 4) (.reg 5)), .reg 5])
            (.call 11 negCopyTo [.bin .add (.reg 9) (.const 2),
              .bin .add (.reg 3) (.bin .mul (.reg 4) (.reg 5)), .reg 5]))
          ⟨mem, rg10, pos⟩ .normal ⟨mem', Function.update rg10 11 0, pos'⟩ cI ∧
        PathIntAt mem' (g0Ptr + e * Lk) 4 Lk val ∧
        (∀ a, a < g0Ptr + e * Lk ∨ g0Ptr + (e + 1) * Lk ≤ a → mem' a = mem a) ∧
        cI ≤ 45 * Lk + 40 := by
      cases fwd with
      | true =>
        simp only [↓reduceIte] at hfwd hEq
        subst hEq
        obtain ⟨bC, hbC, oC, stC, cC, hrC, hpC, hcC⟩ :=
          hCopy [valPtr + 2, g0Ptr + e * Lk, Lk] mem pos ω
            (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                rintro v (rfl | rfl | rfl) <;> omega)
            ⟨valPtr + 2, g0Ptr + e * Lk, Lk, rfl, by omega, by omega, hdstW,
              by rcases hDisj with h | h <;> [left; right] <;> omega,
              fun i hi => by have := hP_L.1 i hi; unfold base at this; omega⟩
        obtain ⟨hoC, hcpC, hfrC⟩ := hpC
        simp only [List.getD_cons_zero, List.getD_cons_succ] at hcpC hfrC
        have rCallC : Runs w p ω
            (.call 11 copyTo [.bin .add (.reg 9) (.const 2),
              .bin .add (.reg 3) (.bin .mul (.reg 4) (.reg 5)), .reg 5])
            ⟨mem, rg10, pos⟩ .normal ⟨stC.mem, Function.update rg10 11 oC.value, stC.pos⟩ (cC + 10) :=
          runs_call_iff.mpr ⟨[valPtr + 2, g0Ptr + e * Lk, Lk], bC, oC, stC, cC,
            by simp [evalArgs, Expr.eval, BinOp.eval, rg10, rg9, rg8, rg7, rg6, s0, startState,
              show 2 < 2 ^ w by omega, show valPtr + 2 < 2 ^ w by omega,
              heLkW, show g0Ptr + e * Lk < 2 ^ w by omega],
            hbC, hrC, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
        rw [hoC] at rCallC
        refine ⟨stC.mem, stC.pos, _,
          runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, rg10, hfwd], rCallC, rfl⟩,
          hP_L.congr hcpC, fun a ha => hfrC a (by omega), ?_⟩
        simp only [copyLimbsToContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size] at hcC ⊢
        omega
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hfwd hEq
        obtain ⟨bN, hbN, oN, stN, cN, hrN, hpN, hcN⟩ :=
          hNeg gRaw [valPtr + 2, g0Ptr + e * Lk, Lk] mem pos ω
            (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                rintro v (rfl | rfl | rfl) <;> omega)
            ⟨valPtr + 2, g0Ptr + e * Lk, Lk, rfl, hw16, by omega, hdstW,
              by rcases hDisj with h | h <;> [left; right] <;> omega, hP_L, hEq ▸ hF1⟩
        obtain ⟨_, _, _, hargsN, hoN, hPN, hfrN⟩ := hpN
        simp only [List.cons.injEq] at hargsN
        obtain ⟨rfl, rfl, rfl, -⟩ := hargsN
        have rCallN : Runs w p ω
            (.call 11 negCopyTo [.bin .add (.reg 9) (.const 2),
              .bin .add (.reg 3) (.bin .mul (.reg 4) (.reg 5)), .reg 5])
            ⟨mem, rg10, pos⟩ .normal ⟨stN.mem, Function.update rg10 11 oN.value, stN.pos⟩ (cN + 10) :=
          runs_call_iff.mpr ⟨[valPtr + 2, g0Ptr + e * Lk, Lk], bN, oN, stN, cN,
            by simp [evalArgs, Expr.eval, BinOp.eval, rg10, rg9, rg8, rg7, rg6, s0, startState,
              show 2 < 2 ^ w by omega, show valPtr + 2 < 2 ^ w by omega,
              heLkW, show g0Ptr + e * Lk < 2 ^ w by omega],
            hbN, hrN, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
        rw [hoN] at rCallN
        refine ⟨stN.mem, stN.pos, _,
          runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, rg10, hfwd], rCallN, rfl⟩,
          hEq ▸ hPN, fun a ha => hfrN a (by omega), ?_⟩
        simp only [selNegCopyToContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size] at hcN ⊢
        omega
    obtain ⟨mem', pos', cI, rI, hP', hfr', hcI⟩ := hInner
    have rThen := runs_seq_iff.mpr (Or.inr ⟨_, _, _, rK,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, rNb,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, rVP,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, rFwd, rI, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have rRet : Runs w p ω (.ret (.const 0)) ⟨mem', Function.update rg10 11 0, pos'⟩
        (.returned 0) ⟨mem', Function.update rg10 11 0, pos'⟩ 2 :=
      runs_ret_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
    refine ⟨.returned 0, ⟨mem', Function.update rg10 11 0, pos'⟩, _,
      by unfold selCopyG0OneBody
         exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, rLoadS,
           runs_seq_iff.mpr (Or.inr ⟨_, _, _,
             runs_cond_iff.mpr ⟨s, _, by simp [Expr.eval, rg6, s], by simpa [hs0] using rThen, rfl⟩,
             rRet, rfl⟩), rfl⟩),
      ⟨slots, edgeRecords, treeHeap, g0Ptr, e, Lk, rfl, rfl, hP', hfr'⟩, ?_⟩
    simp only [selCopyG0OneContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    omega


end MinCostFlow.MinRatio
