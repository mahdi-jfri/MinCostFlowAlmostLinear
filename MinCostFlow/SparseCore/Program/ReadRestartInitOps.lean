module

public import MinCostFlow.SparseCore.Program.ReadRecord
public import MinCostFlow.SparseCore.Program.ReadTree
public import MinCostFlow.DynSpanner.Program.DynGraphInsert
public import WordRAM.Contract

import WordRAM.Tactic

/-!
# Initialization helpers for piece P10 (`ReadRestartInitOps`)

Two helper procedures used by branch initialization (`ReadRestartInit.lean`):

* `copyStretchPairsStmt` (`[eListPtr, nE, L_w, srcNum, srcDen, dstNum, dstDen]`):
  copies the `L_w`-limb numerator and denominator blocks of every listed edge `e` from
  `(srcNum, srcDen)` into `(dstNum, dstDen)` (`copyStretchPairs_meetsContract`), at cost
  `≤ 55 * nE * (L_w + 1) + 20`. Combined with `stretch_of_copy`, this yields `StretchValuesAt`
  and `StretchPairsAt`.
* `splitTreeEdgesStmt bEdge` (`[gPtr, livePtr, frzPtr, ePtrT, nET]`):
  scans the `nET` edge triples `(e, u, v_e)` of the exported tree `T`, inserting each edge into
  `live` when `e ∈ G.E` and into `frz` otherwise (`splitTreeEdges_meetsContract`), at cost
  `≤ 540 * nET + 40`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.MinRatio MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.Num

/-! ## Helper 1: copying stretch tables for active edges of `G` -/

/-- `[eListPtr, nE, L_w, srcNum, srcDen, dstNum, dstDen]`: for each `i < nE`, let `e := mem (eListPtr + i)`
and copy `L_w` words from `srcNum + e * L_w` to `dstNum + e * L_w` and from `srcDen + e * L_w` to
`dstDen + e * L_w`. -/
def copyStretchPairsStmt : Stmt :=
  forRange 7 (.const 0) (.reg 1)
    (.assign 8 (.load (.bin .add (.reg 0) (.reg 7))) ;;
     .assign 9 (.bin .mul (.reg 8) (.reg 2)) ;;
     forRange 10 (.const 0) (.reg 2)
       (.assign 11 (.bin .add (.reg 9) (.reg 10)) ;;
        .assign 12 (.load (.bin .add (.reg 3) (.reg 11))) ;;
        .store (.bin .add (.reg 5) (.reg 11)) (.reg 12) ;;
        .assign 12 (.load (.bin .add (.reg 4) (.reg 11))) ;;
        .store (.bin .add (.reg 6) (.reg 11)) (.reg 12))) ;;
  .ret (.const 0)

theorem copyStretchPairsStmt_noRand : copyStretchPairsStmt.NoRand := by
  simp [copyStretchPairsStmt, forRange, forUp, Stmt.NoRand]

/-- Contract of `copyStretchPairsStmt` for an edge list `eL` (within `eCap`) and stride `L_w`. -/
def copyStretchPairsContract (w eCap L_w : ℕ) (eL : List ℕ) : Contract where
  pre args mem := ∃ eListPtr srcNum srcDen dstNum dstDen,
    args = [eListPtr, eL.length, L_w, srcNum, srcDen, dstNum, dstDen] ∧
    16 ≤ 2 ^ w ∧ ListAt mem eListPtr eL ∧
    eListPtr + eL.length ≤ dstNum ∧
    (∀ e ∈ eL, e < eCap ∧ srcNum + (e + 1) * L_w ≤ dstNum ∧ srcDen + (e + 1) * L_w ≤ dstNum) ∧
    dstNum + eCap * L_w ≤ dstDen ∧ dstDen + eCap * L_w < 2 ^ w
  post args mem ret mem' := ∃ eListPtr srcNum srcDen dstNum dstDen,
    args = [eListPtr, eL.length, L_w, srcNum, srcDen, dstNum, dstDen] ∧ ret = 0 ∧
    (∀ e ∈ eL, ∀ k < L_w,
      mem' (dstNum + e * L_w + k) = mem (srcNum + e * L_w + k) ∧
      mem' (dstDen + e * L_w + k) = mem (srcDen + e * L_w + k)) ∧
    (∀ a, (a < dstNum ∨ dstNum + eCap * L_w ≤ a) → (a < dstDen ∨ dstDen + eCap * L_w ≤ a) →
      mem' a = mem a)
  cost _ _ := 55 * eL.length * (L_w + 1) + 20

/-! ## Helper 2: splitting exported tree edges into `liveT` and `frozenT` -/

/-- `[gPtr, livePtr, frzPtr, ePtrT, nET]`: for each `i < nET`, read `(e, u, v_e)` at
`ePtrT + 3 * i + {0, 1, 2}`; if `e < eCap` and `e` is present in `G`, insert `(e, u, v_e)` into
`livePtr`, else insert it into `frzPtr`. -/
def splitTreeEdgesStmt (bEdge : ℕ) : Stmt :=
  .assign 5 (.load (.reg 0)) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 7 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 5))) ;;
  forRange 8 (.const 0) (.reg 4)
    (.assign 9 (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 8))) ;;
     .assign 10 (.load (.reg 9)) ;;
     .assign 11 (.load (.bin .add (.reg 9) (.const 1))) ;;
     .assign 12 (.load (.bin .add (.reg 9) (.const 2))) ;;
     .cond (.bin .lt (.reg 10) (.reg 6))
       (.cond (.load (.bin .add (.reg 7) (.reg 10)))
         (.call 13 (bEdge + dgIdxInsertEdge) [.reg 1, .reg 10, .reg 11, .reg 12])
         (.call 13 (bEdge + dgIdxInsertEdge) [.reg 2, .reg 10, .reg 11, .reg 12]))
       (.call 13 (bEdge + dgIdxInsertEdge) [.reg 2, .reg 10, .reg 11, .reg 12])) ;;
  .ret (.const 0)

theorem splitTreeEdgesStmt_noRand (bEdge : ℕ) : (splitTreeEdgesStmt bEdge).NoRand := by
  simp [splitTreeEdgesStmt, forRange, forUp, Stmt.NoRand]

/-- Index of `copyStretchPairsStmt` in `readInitOpsProcs`. -/
def readInitOpsIdxStretch : ℕ := 0
/-- Index of `splitTreeEdgesStmt` in `readInitOpsProcs`. -/
def readInitOpsIdxSplitT : ℕ := 1

/-- The two initialization helper procedures. -/
def readInitOpsProcs (bEdge : ℕ) : List Stmt :=
  [copyStretchPairsStmt, splitTreeEdgesStmt bEdge]

theorem readInitOpsProcs_noRand (bEdge : ℕ) : ∀ s ∈ readInitOpsProcs bEdge, s.NoRand := by
  intro s hs
  simp only [readInitOpsProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact copyStretchPairsStmt_noRand
  · exact splitTreeEdgesStmt_noRand bEdge

/-! ## Verification of `copyStretchPairsStmt` -/

theorem copyStretchPairs_meetsContract {w eCap L_w : ℕ} {p : Program} {b bEdge : ℕ}
    {eL : List ℕ} (hp : p.HasAt b (readInitOpsProcs bEdge)) :
    MeetsContract w p (b + readInitOpsIdxStretch) (copyStretchPairsContract w eCap L_w eL) := by
  refine meetsContract_of_runs
    (hp.get (i := readInitOpsIdxStretch) (by simp [readInitOpsProcs, readInitOpsIdxStretch])) ?_
  rintro args mem pos ω hargs
    ⟨eListPtr, srcNum, srcDen, dstNum, dstDen, rfl, hw16, heL_at, heL_le, heL_spec, hnd_le, hd_lt⟩
  simp only [readInitOpsProcs, readInitOpsIdxStretch, List.getElem_cons_zero]
  have hnE_lt : eL.length < 2 ^ w := hargs _ (by simp)
  have hLw_lt : L_w < 2 ^ w := hargs _ (by simp)
  let frame : (ℕ → ℕ) → Prop := fun m =>
    ∀ a, (a < dstNum ∨ dstNum + eCap * L_w ≤ a) → (a < dstDen ∨ dstDen + eCap * L_w ≤ a) →
      m a = mem a
  let Copied : (ℕ → ℕ) → ℕ → Prop := fun m i =>
    ∀ j < i, ∀ (hj : j < eL.length), ∀ k < L_w,
      m (dstNum + eL[j] * L_w + k) = mem (srcNum + eL[j] * L_w + k) ∧
      m (dstDen + eL[j] * L_w + k) = mem (srcDen + eL[j] * L_w + k)
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = eListPtr ∧ st.regs 1 = eL.length ∧ st.regs 2 = L_w ∧
    st.regs 3 = srcNum ∧ st.regs 4 = srcDen ∧ st.regs 5 = dstNum ∧ st.regs 6 = dstDen ∧
    st.regs 7 = i ∧ Copied st.mem i ∧ frame st.mem
  let innerBody : Stmt :=
    .assign 11 (.bin .add (.reg 9) (.reg 10)) ;;
    .assign 12 (.load (.bin .add (.reg 3) (.reg 11))) ;;
    .store (.bin .add (.reg 5) (.reg 11)) (.reg 12) ;;
    .assign 12 (.load (.bin .add (.reg 4) (.reg 11))) ;;
    .store (.bin .add (.reg 6) (.reg 11)) (.reg 12)
  let outerBody : Stmt :=
    .assign 8 (.load (.bin .add (.reg 0) (.reg 7))) ;;
    .assign 9 (.bin .mul (.reg 8) (.reg 2)) ;;
    forRange 10 (.const 0) (.reg 2) innerBody
  have hOuter : Triple w p
      (fun st => st = startState [eListPtr, eL.length, L_w, srcNum, srcDen, dstNum, dstDen] mem pos)
      (forRange 7 (.const 0) (.reg 1) outerBody) (normalPost (Inv eL.length))
      (fun _ => (eL.length - 0) * ((45 * L_w + 20) + Expr.size (.reg 1) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 1) + 5)) := by
    refine Triple.forRange_const (45 * L_w + 20) 0 eL.length (Nat.zero_le _) (by omega) (fun _ => hnE_lt)
      (fun st hst => by
        subst hst
        refine ⟨Expr.eval_const (by omega), by simp [startState], by simp [startState],
          by simp [startState], by simp [startState], by simp [startState], by simp [startState],
          by simp [startState], by simp, fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl⟩)
      (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.1)
      (fun _ _ _ _ hI => by simp [Expr.eval, hI.2.1])
      (fun i _ hi st ω' hI => by
        obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, hCop, hfr⟩ := hI
        set e := eL[i] with he_def
        obtain ⟨he_cap, hsrcN_le, hsrcD_le⟩ := heL_spec e (List.getElem_mem hi)
        have he_mul_le : (e + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right L_w (by omega)
        have he_mul_lt : e * L_w < 2 ^ w := by rw [Nat.add_mul, one_mul] at he_mul_le; omega
        have he_val : st.mem (eListPtr + i) = e := by
          rw [hfr (eListPtr + i) (Or.inl (by omega)) (Or.inl (by omega))]; exact heL_at i hi
        have hr8 : Runs w p ω' (.assign 8 (.load (.bin .add (.reg 0) (.reg 7)))) st .normal
            { st with regs := Function.update st.regs 8 e } 5 :=
          runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r7) (by omega)) he_val,
            rfl, rfl, by simp [Expr.size]⟩
        set st1 := { st with regs := Function.update st.regs 8 e }
        have hr9 : Runs w p ω' (.assign 9 (.bin .mul (.reg 8) (.reg 2))) st1 .normal
            { st1 with regs := Function.update st1.regs 9 (e * L_w) } 4 :=
          runs_assign_iff.mpr ⟨e * L_w, Expr.eval_mul (Expr.eval_reg_of_eq (by simp [st1]))
            (Expr.eval_reg_of_eq (by simp [st1, r2])) he_mul_lt, rfl, rfl, by simp [Expr.size]⟩
        set st2 := { st1 with regs := Function.update st1.regs 9 (e * L_w) }
        let InvK : ℕ → State → Prop := fun k s =>
          s.regs 0 = eListPtr ∧ s.regs 1 = eL.length ∧ s.regs 2 = L_w ∧
          s.regs 3 = srcNum ∧ s.regs 4 = srcDen ∧ s.regs 5 = dstNum ∧ s.regs 6 = dstDen ∧
          s.regs 7 = i ∧ s.regs 9 = e * L_w ∧ s.regs 10 = k ∧
          (∀ m < k, s.mem (dstNum + e * L_w + m) = mem (srcNum + e * L_w + m) ∧
            s.mem (dstDen + e * L_w + m) = mem (srcDen + e * L_w + m)) ∧
          (∀ a, (a < dstNum + e * L_w ∨ dstNum + e * L_w + k ≤ a) →
            (a < dstDen + e * L_w ∨ dstDen + e * L_w + k ≤ a) → s.mem a = st.mem a)
        have hInner : Triple w p (fun s => s = st2)
            (forRange 10 (.const 0) (.reg 2) innerBody) (normalPost (InvK L_w))
            (fun _ => (L_w - 0) * (35 + Expr.size (.reg 2) + 8) +
              (Expr.size (.const 0) + Expr.size (.reg 2) + 5)) := by
          refine Triple.forRange_const 35 0 L_w (Nat.zero_le _) (by omega) (fun _ => hLw_lt)
            (fun s hs => by
              subst hs
              refine ⟨Expr.eval_const (by omega), by simp [st2, st1, r0], by simp [st2, st1, r1],
                by simp [st2, st1, r2], by simp [st2, st1, r3], by simp [st2, st1, r4],
                by simp [st2, st1, r5], by simp [st2, st1, r6], by simp [st2, st1, r7],
                by simp [st2], by simp, fun _ hm => absurd hm (Nat.not_lt_zero _),
                fun _ _ _ => rfl⟩)
            (fun _ _ _ _ hIk => hIk.2.2.2.2.2.2.2.2.2.1)
            (fun _ _ _ _ hIk => by simp [Expr.eval, hIk.2.2.1])
            (fun k _ hk s ω'' hIk => by
              obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s9, s10, hCur, hfrK⟩ := hIk
              have hoff_lt : e * L_w + k < eCap * L_w := by
                rw [Nat.add_mul, one_mul] at he_mul_le; omega
              have hsrcN_a : srcNum + (e * L_w + k) < dstNum := by
                rw [Nat.add_mul, one_mul] at hsrcN_le; omega
              have hsrcD_a : srcDen + (e * L_w + k) < dstNum := by
                rw [Nat.add_mul, one_mul] at hsrcD_le; omega
              have hvalN : s.mem (srcNum + (e * L_w + k)) = mem (srcNum + e * L_w + k) := by
                rw [hfrK _ (Or.inl (by omega)) (Or.inl (by omega)),
                  hfr _ (Or.inl (by omega)) (Or.inl (by omega)), Nat.add_assoc]
              have hvalD : s.mem (srcDen + (e * L_w + k)) = mem (srcDen + e * L_w + k) := by
                rw [hfrK _ (Or.inl (by omega)) (Or.inl (by omega)),
                  hfr _ (Or.inl (by omega)) (Or.inl (by omega)), Nat.add_assoc]
              have hneND : dstNum + (e * L_w + k) ≠ dstDen + (e * L_w + k) := by omega
              have hneSrcD : srcDen + (e * L_w + k) ≠ dstNum + (e * L_w + k) := by omega
              apply runs_start_le
              refine runs_seq_assign_le (v := e * L_w + k)
                (Expr.eval_add (Expr.eval_reg_of_eq s9) (Expr.eval_reg_of_eq s10) (by omega)) ?_
              refine runs_seq_assign_le (v := mem (srcNum + e * L_w + k))
                (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s3]))
                  (Expr.eval_reg_of_eq (by simp)) (by omega)) hvalN) ?_
              refine runs_seq_store_le (x := dstNum + (e * L_w + k))
                (v := mem (srcNum + e * L_w + k))
                (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s5]))
                  (Expr.eval_reg_of_eq (by simp)) (by omega))
                (Expr.eval_reg_of_eq (by simp)) ?_
              refine runs_seq_assign_le (v := mem (srcDen + e * L_w + k))
                (Expr.eval_load_of_eq (Expr.eval_add
                  (Expr.eval_reg_of_eq (v := srcDen) (by simp [s4]))
                  (Expr.eval_reg_of_eq (v := e * L_w + k) (by simp)) (by omega))
                  (by dsimp only; rw [Function.update_of_ne hneSrcD]; exact hvalD)) ?_
              refine runs_store_le (x := dstDen + (e * L_w + k))
                (v := mem (srcDen + e * L_w + k))
                (Expr.eval_add (Expr.eval_reg_of_eq (v := dstDen) (by simp [s6]))
                  (Expr.eval_reg_of_eq (v := e * L_w + k) (by simp)) (by omega))
                (Expr.eval_reg_of_eq (v := mem (srcDen + e * L_w + k)) (by simp)) ?_ ?_
              · refine ⟨⟨by dsimp only; simp [s0], by dsimp only; simp [s1],
                  by dsimp only; simp [s2], by dsimp only; simp [s3], by dsimp only; simp [s4],
                  by dsimp only; simp [s5], by dsimp only; simp [s6], by dsimp only; simp [s7],
                  by dsimp only; simp [s9], by simp, ?_, ?_⟩, by dsimp only; simp [s10]⟩
                · intro m hm
                  by_cases hmk : m = k
                  · subst hmk
                    simp only [Nat.add_assoc, Function.update_self, Function.update_of_ne hneND,
                      and_self]
                  · have hm_lt : m < k := by omega
                    have h1 : dstNum + e * L_w + m ≠ dstDen + (e * L_w + k) := by omega
                    have h2 : dstNum + e * L_w + m ≠ dstNum + (e * L_w + k) := by omega
                    have h3 : dstDen + e * L_w + m ≠ dstDen + (e * L_w + k) := by omega
                    have h4 : dstDen + e * L_w + m ≠ dstNum + (e * L_w + k) := by omega
                    simp only [Function.update_of_ne h1, Function.update_of_ne h2,
                      Function.update_of_ne h3, Function.update_of_ne h4]
                    exact hCur m hm_lt
                · intro a haN haD
                  have h1 : a ≠ dstDen + (e * L_w + k) := by omega
                  have h2 : a ≠ dstNum + (e * L_w + k) := by omega
                  simp only [Function.update_of_ne h1, Function.update_of_ne h2]
                  exact hfrK a (by omega) (by omega)
              · simp [Expr.size])
        obtain ⟨oIn, st3, cIn, hrIn, hPostIn, hcIn⟩ := hInner st2 ω' rfl
        cases oIn with
        | returned _ => exact hPostIn.elim
        | normal =>
        have hInvK : InvK L_w st3 := hPostIn
        obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, _, _, hCurAll, hfrK⟩ := hInvK
        have hrBody : Runs w p ω' outerBody st .normal st3 (5 + (4 + cIn + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st1, 5, 4 + cIn + 1, hr8,
            runs_seq_iff.mpr (Or.inr ⟨st2, 4, cIn, hr9, hrIn, rfl⟩), rfl⟩)
        have hfr' : frame st3.mem := fun a haN haD => by
          have haN' : a < dstNum + e * L_w ∨ dstNum + e * L_w + L_w ≤ a := by
            rw [Nat.add_mul, one_mul] at he_mul_le; omega
          have haD' : a < dstDen + e * L_w ∨ dstDen + e * L_w + L_w ≤ a := by
            rw [Nat.add_mul, one_mul] at he_mul_le; omega
          exact (hfrK a haN' haD').trans (hfr a haN haD)
        have hCop' : Copied st3.mem (i + 1) := by
          intro j hj hjlen k hk
          by_cases hji : j = i
          · subst hji; exact hCurAll k hk
          · have hj_lt : j < i := by omega
            by_cases heq : eL[j] = e
            · rw [heq]; exact hCurAll k hk
            · have haN' : dstNum + eL[j] * L_w + k < dstNum + e * L_w ∨
                  dstNum + e * L_w + L_w ≤ dstNum + eL[j] * L_w + k := by
                rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
                · left
                  have : (eL[j] + 1) * L_w ≤ e * L_w := Nat.mul_le_mul_right L_w (by omega)
                  rw [Nat.add_mul, one_mul] at this; omega
                · right
                  have : (e + 1) * L_w ≤ eL[j] * L_w := Nat.mul_le_mul_right L_w (by omega)
                  rw [Nat.add_mul, one_mul] at this; omega
              have haD' : dstDen + eL[j] * L_w + k < dstDen + e * L_w ∨
                  dstDen + e * L_w + L_w ≤ dstDen + eL[j] * L_w + k := by
                rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
                · left
                  have : (eL[j] + 1) * L_w ≤ e * L_w := Nat.mul_le_mul_right L_w (by omega)
                  rw [Nat.add_mul, one_mul] at this; omega
                · right
                  have : (e + 1) * L_w ≤ eL[j] * L_w := Nat.mul_le_mul_right L_w (by omega)
                  rw [Nat.add_mul, one_mul] at this; omega
              have hN_neD : dstNum + eL[j] * L_w + k < dstDen + e * L_w := by
                have hj_cap := (heL_spec eL[j] (List.getElem_mem hjlen)).1
                have : (eL[j] + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right L_w (by omega)
                rw [Nat.add_mul, one_mul] at this; omega
              have hD_neN : dstNum + e * L_w + L_w ≤ dstDen + eL[j] * L_w + k := by
                rw [Nat.add_mul, one_mul] at he_mul_le; omega
              constructor
              · rw [hfrK _ haN' (Or.inl hN_neD)]; exact (hCop j hj_lt hjlen k hk).1
              · rw [hfrK _ (Or.inr hD_neN) haD']; exact (hCop j hj_lt hjlen k hk).2
        refine ⟨.normal, st3, _, hrBody,
          ⟨⟨by simp [k0], by simp [k1], by simp [k2], by simp [k3], by simp [k4],
            by simp [k5], by simp [k6], by simp, hCop', hfr'⟩, k7⟩, ?_⟩
        simp only [Expr.size, Nat.sub_zero] at hcIn ⊢
        omega)
  apply runs_start_le
  refine runs_seq_triple_le hOuter rfl ?_
  rintro st ⟨_, _, _, _, _, _, _, _, hCopEnd, hfrEnd⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega))
    ⟨eListPtr, srcNum, srcDen, dstNum, dstDen, rfl, rfl, ?_, hfrEnd⟩ ?_
  · intro e he k hk
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    exact hCopEnd j hj hj k hk
  · simp only [copyStretchPairsContract, Expr.size, Nat.sub_zero]
    have hmul : eL.length * (45 * L_w + 20 + 1 + 8) ≤ 55 * eL.length * (L_w + 1) := by
      calc eL.length * (45 * L_w + 20 + 1 + 8)
          ≤ eL.length * (55 * (L_w + 1)) := Nat.mul_le_mul_left _ (by omega)
        _ = 55 * eL.length * (L_w + 1) := by ring
    omega

/-- After copying stretch blocks from `srcNum, srcDen` (meeting `ReadInitAt`) to `dstNum, dstDen`
pointed to by `r + 7, r + 8`, both `StretchValuesAt` and `StretchPairsAt` hold for `v`. -/
theorem stretch_of_copy {mem srcMem : ℕ → ℕ} {r srcNum srcDen dstNum dstDen L_w P : ℕ}
    {v : ReadView}
    (hr7 : mem (r + 7) = dstNum) (hr8 : mem (r + 8) = dstDen)
    (hsrc : ∀ e ∈ v.G.E,
      Num.Valid srcMem (srcNum + e * L_w) 4 L_w ∧ Num.Valid srcMem (srcDen + e * L_w) 4 L_w ∧
      Num.intVal srcMem (srcNum + e * L_w) 4 L_w = v.num e ∧
      Num.intVal srcMem (srcDen + e * L_w) 4 L_w = v.den e)
    (hinv : ∀ e ∈ v.G.E, 0 < v.den e ∧ (v.num e : ℝ) / v.den e = v.lsf.wstr e)
    (hcopy : ∀ e ∈ v.G.E, ∀ k < L_w,
      mem (dstNum + e * L_w + k) = srcMem (srcNum + e * L_w + k) ∧
      mem (dstDen + e * L_w + k) = srcMem (srcDen + e * L_w + k)) :
    StretchValuesAt mem (r + 7) 4 L_w P v.G.E v.lsf.wstr ∧
    StretchPairsAt mem (r + 7) L_w v.G.E v.num v.den := by
  have h1 : ∀ e ∈ v.G.E,
      Num.Valid mem (dstNum + e * L_w) 4 L_w ∧ Num.Valid mem (dstDen + e * L_w) 4 L_w ∧
      Num.intVal mem (dstNum + e * L_w) 4 L_w = v.num e ∧
      Num.intVal mem (dstDen + e * L_w) 4 L_w = v.den e := by
    intro e he
    obtain ⟨hvN, hvD, hiN, hiD⟩ := hsrc e he
    refine ⟨fun k hk => (hcopy e he k hk).1.trans_lt (hvN k hk),
      fun k hk => (hcopy e he k hk).2.trans_lt (hvD k hk), ?_, ?_⟩
    · rw [Num.intVal_congr (fun k hk => (hcopy e he k hk).1)]; exact hiN
    · rw [Num.intVal_congr (fun k hk => (hcopy e he k hk).2)]; exact hiD
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨hvN, hvD, hiN, hiD⟩ := h1 e he
    obtain ⟨hden_pos, hquot⟩ := hinv e he
    rw [hr7, show r + 7 + 1 = r + 8 from rfl, hr8]
    refine ⟨hvN, hvD, ?_, ?_⟩
    · unfold Num.fixVal
      rw [hiD]
      exact div_pos (Int.cast_pos.mpr hden_pos) (pow_pos (by norm_num : (0 : ℝ) < 2) P)
    · unfold Num.fixVal
      rw [hiN, hiD]
      have h2p : ((2 : ℝ) ^ P) ≠ 0 := ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) P)
      rw [div_div_div_cancel_right₀ h2p]
      exact hquot
  · obtain ⟨_, _, hiN, hiD⟩ := h1 e he
    rw [hr7, show r + 7 + 1 = r + 8 from rfl, hr8]
    exact ⟨hiN, hiD⟩

/-! ## Verification of `splitTreeEdgesStmt` -/

/-- One edge insertion step on `(live, frz)` for a triple `t = (e, u, v_e)` of `T`. -/
private def splitTStep (G : MGraph) (p : MGraph × MGraph) (t : ℕ × ℕ × ℕ) : MGraph × MGraph :=
  if t.1 ∈ G.E then
    (p.1.applyUpdate (.insert t.1 t.2.1 t.2.2), p.2)
  else
    (p.1, p.2.applyUpdate (.insert t.1 t.2.1 t.2.2))

private lemma foldl_splitTStep_V (G : MGraph) (eT : List (ℕ × ℕ × ℕ)) (L F : MGraph) :
    (eT.foldl (splitTStep G) (L, F)).1.V = L.V ∧
    (eT.foldl (splitTStep G) (L, F)).2.V = F.V := by
  induction eT generalizing L F with
  | nil => exact ⟨rfl, rfl⟩
  | cons t ts ih =>
    rw [List.foldl_cons]
    by_cases ht : t.1 ∈ G.E
    · rw [show splitTStep G (L, F) t = (L.applyUpdate (.insert t.1 t.2.1 t.2.2), F) by
        simp [splitTStep, ht]]
      simpa [MGraph.applyUpdate] using ih _ _
    · rw [show splitTStep G (L, F) t = (L, F.applyUpdate (.insert t.1 t.2.1 t.2.2)) by
        simp [splitTStep, ht]]
      simpa [MGraph.applyUpdate] using ih _ _

private lemma foldl_splitTStep_E (G : MGraph) (eT : List (ℕ × ℕ × ℕ)) (L F : MGraph) (e : ℕ) :
    (e ∈ (eT.foldl (splitTStep G) (L, F)).1.E ↔ e ∈ L.E ∨ (e ∈ G.E ∧ ∃ t ∈ eT, t.1 = e)) ∧
    (e ∈ (eT.foldl (splitTStep G) (L, F)).2.E ↔ e ∈ F.E ∨ (e ∉ G.E ∧ ∃ t ∈ eT, t.1 = e)) := by
  induction eT generalizing L F with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons]
    by_cases ht : t.1 ∈ G.E
    · rw [show splitTStep G (L, F) t = (L.applyUpdate (.insert t.1 t.2.1 t.2.2), F) by
        simp [splitTStep, ht]]
      obtain ⟨h1, h2⟩ := ih (L.applyUpdate (.insert t.1 t.2.1 t.2.2)) F
      constructor
      · rw [h1]; simp only [MGraph.applyUpdate, Finset.mem_insert, List.mem_cons]
        constructor
        · rintro ((rfl | hL) | ⟨heG, t', ht', rfl⟩)
          · exact Or.inr ⟨ht, t, Or.inl rfl, rfl⟩
          · exact Or.inl hL
          · exact Or.inr ⟨heG, t', Or.inr ht', rfl⟩
        · rintro (hL | ⟨heG, t', rfl | ht', rfl⟩)
          · exact Or.inl (Or.inr hL)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨heG, t', ht', rfl⟩
      · rw [h2]; simp only [List.mem_cons]
        constructor
        · rintro (hF | ⟨heG, t', ht', rfl⟩)
          · exact Or.inl hF
          · exact Or.inr ⟨heG, t', Or.inr ht', rfl⟩
        · rintro (hF | ⟨heG, t', rfl | ht', rfl⟩)
          · exact Or.inl hF
          · exact absurd ht heG
          · exact Or.inr ⟨heG, t', ht', rfl⟩
    · rw [show splitTStep G (L, F) t = (L, F.applyUpdate (.insert t.1 t.2.1 t.2.2)) by
        simp [splitTStep, ht]]
      obtain ⟨h1, h2⟩ := ih L (F.applyUpdate (.insert t.1 t.2.1 t.2.2))
      constructor
      · rw [h1]; simp only [List.mem_cons]
        constructor
        · rintro (hL | ⟨heG, t', ht', rfl⟩)
          · exact Or.inl hL
          · exact Or.inr ⟨heG, t', Or.inr ht', rfl⟩
        · rintro (hL | ⟨heG, t', rfl | ht', rfl⟩)
          · exact Or.inl hL
          · exact absurd heG ht
          · exact Or.inr ⟨heG, t', ht', rfl⟩
      · rw [h2]; simp only [MGraph.applyUpdate, Finset.mem_insert, List.mem_cons]
        constructor
        · rintro ((rfl | hF) | ⟨heG, t', ht', rfl⟩)
          · exact Or.inr ⟨ht, t, Or.inl rfl, rfl⟩
          · exact Or.inl hF
          · exact Or.inr ⟨heG, t', Or.inr ht', rfl⟩
        · rintro (hF | ⟨heG, t', rfl | ht', rfl⟩)
          · exact Or.inl (Or.inr hF)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨heG, t', ht', rfl⟩

private lemma foldl_splitTStep_preserve (G : MGraph) (eT : List (ℕ × ℕ × ℕ)) (L F : MGraph)
    (e : ℕ) (hne : ∀ y ∈ eT, y.1 ≠ e) :
    (eT.foldl (splitTStep G) (L, F)).1.tail e = L.tail e ∧
    (eT.foldl (splitTStep G) (L, F)).1.head e = L.head e ∧
    (eT.foldl (splitTStep G) (L, F)).2.tail e = F.tail e ∧
    (eT.foldl (splitTStep G) (L, F)).2.head e = F.head e := by
  induction eT generalizing L F with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons x xs ih =>
    have hx : x.1 ≠ e := hne x List.mem_cons_self
    have hxs : ∀ y ∈ xs, y.1 ≠ e := fun y hy => hne y (List.mem_cons_of_mem _ hy)
    rw [List.foldl_cons]
    by_cases hG : x.1 ∈ G.E
    · rw [show splitTStep G (L, F) x = (L.applyUpdate (.insert x.1 x.2.1 x.2.2), F) by
        simp [splitTStep, hG]]
      obtain ⟨a, b, c, d⟩ := ih (L.applyUpdate (.insert x.1 x.2.1 x.2.2)) F hxs
      simp only [MGraph.applyUpdate, Function.update_of_ne hx.symm] at a b
      exact ⟨a, b, c, d⟩
    · rw [show splitTStep G (L, F) x = (L, F.applyUpdate (.insert x.1 x.2.1 x.2.2)) by
        simp [splitTStep, hG]]
      obtain ⟨a, b, c, d⟩ := ih L (F.applyUpdate (.insert x.1 x.2.1 x.2.2)) hxs
      simp only [MGraph.applyUpdate, Function.update_of_ne hx.symm] at c d
      exact ⟨a, b, c, d⟩

private lemma foldl_splitTStep_ends (G : MGraph) (eT : List (ℕ × ℕ × ℕ)) (L F : MGraph)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ eT) (hnd : (eT.map Prod.fst).Nodup) :
    (t.1 ∈ G.E → (eT.foldl (splitTStep G) (L, F)).1.tail t.1 = t.2.1 ∧
      (eT.foldl (splitTStep G) (L, F)).1.head t.1 = t.2.2) ∧
    (t.1 ∉ G.E → (eT.foldl (splitTStep G) (L, F)).2.tail t.1 = t.2.1 ∧
      (eT.foldl (splitTStep G) (L, F)).2.head t.1 = t.2.2) := by
  induction eT generalizing L F with
  | nil => exact absurd ht List.not_mem_nil
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    rcases List.mem_cons.mp ht with rfl | ht_xs
    · have hne : ∀ y ∈ xs, y.1 ≠ t.1 := fun y hy hc => hnd.1 (List.mem_map.mpr ⟨y, hy, hc⟩)
      by_cases hG : t.1 ∈ G.E
      · rw [show splitTStep G (L, F) t = (L.applyUpdate (.insert t.1 t.2.1 t.2.2), F) by
          simp [splitTStep, hG]]
        have hp := foldl_splitTStep_preserve G xs (L.applyUpdate (.insert t.1 t.2.1 t.2.2)) F t.1 hne
        simp only [MGraph.applyUpdate, Function.update_self] at hp
        exact ⟨fun _ => ⟨hp.1, hp.2.1⟩, fun h => absurd hG h⟩
      · rw [show splitTStep G (L, F) t = (L, F.applyUpdate (.insert t.1 t.2.1 t.2.2)) by
          simp [splitTStep, hG]]
        have hp := foldl_splitTStep_preserve G xs L (F.applyUpdate (.insert t.1 t.2.1 t.2.2)) t.1 hne
        simp only [MGraph.applyUpdate, Function.update_self] at hp
        exact ⟨fun h => absurd h hG, fun _ => ⟨hp.2.2.1, hp.2.2.2⟩⟩
    · exact ih (splitTStep G (L, F) x).1 (splitTStep G (L, F) x).2 ht_xs hnd.2

private lemma take_nodup_fst (eT : List (ℕ × ℕ × ℕ)) (k : ℕ) (hnd : (eT.map Prod.fst).Nodup)
    (hk : k < eT.length) : ∀ t ∈ eT.take k, t.1 ≠ eT[k].1 := by
  intro t ht hc
  have htake : ((eT.take (k + 1)).map Prod.fst).Nodup :=
    hnd.sublist (List.Sublist.map _ (List.take_sublist _ _))
  rw [List.take_succ_eq_append_getElem hk, List.map_append, List.map_cons, List.map_nil] at htake
  exact (List.nodup_append'.mp htake).2.2 (List.mem_map.mpr ⟨t, ht, hc⟩) List.mem_cons_self

/-- Contract of `splitTreeEdgesStmt` starting from vertex-only `live` and `frz` (`V = G.V, E = ∅`). -/
def splitTreeEdgesContract (w vCap eCap tCap : ℕ) (G T : MGraph)
    (eT : List (ℕ × ℕ × ℕ)) : Contract where
  pre args mem := ∃ gPtr livePtr frzPtr ePtrT,
    args = [gPtr, livePtr, frzPtr, ePtrT, eT.length] ∧
    16 ≤ 2 ^ w ∧
    gPtr + dynGraphSize vCap eCap ≤ livePtr ∧
    livePtr + dynGraphSize vCap eCap ≤ frzPtr ∧
    frzPtr + dynGraphSize vCap tCap < 2 ^ w ∧
    ePtrT + 3 * eT.length ≤ livePtr ∧
    (∀ i (hi : i < eT.length),
      mem (ePtrT + 3 * i) = eT[i].1 ∧
      mem (ePtrT + 3 * i + 1) = eT[i].2.1 ∧
      mem (ePtrT + 3 * i + 2) = eT[i].2.2) ∧
    (eT.map Prod.fst).Nodup ∧
    (∀ t ∈ eT, t.1 ∈ T.E ∧ t.2.1 = T.tail t.1 ∧ t.2.2 = T.head t.1) ∧
    (∀ e ∈ T.E, ∃ t ∈ eT, t.1 = e) ∧
    TreeAgree G T ∧ (∀ e ∈ T.E, e < tCap) ∧
    DynGraphAt mem gPtr vCap eCap G ∧
    DynGraphAt mem livePtr vCap eCap { V := G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 } ∧
    DynGraphAt mem frzPtr vCap tCap { V := G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 }
  post args mem ret mem' := ∃ gPtr livePtr frzPtr ePtrT,
    args = [gPtr, livePtr, frzPtr, ePtrT, eT.length] ∧ ret = 0 ∧
    DynGraphAt mem' livePtr vCap eCap (liveT G T) ∧
    DynGraphAt mem' frzPtr vCap tCap (frozenT G T) ∧
    ∀ a, (a < livePtr ∨ livePtr + dynGraphSize vCap eCap ≤ a) →
      (a < frzPtr ∨ frzPtr + dynGraphSize vCap tCap ≤ a) → mem' a = mem a
  cost _ _ := 540 * eT.length + 40

private lemma runs_cond_pos_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h1 : ∃ o st' c, Runs w p ω s₁ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c, hr, hq, hc⟩ := h1
  exact ⟨o, st', e.size + c + 1, runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using hr, rfl⟩, hq, by omega⟩

private lemma runs_cond_zero_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some 0)
    (h2 : ∃ o st' c, Runs w p ω s₂ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c, hr, hq, hc⟩ := h2
  exact ⟨o, st', e.size + c + 1, runs_cond_iff.mpr ⟨0, c, he, by simpa using hr, rfl⟩, hq, by omega⟩

theorem splitTreeEdges_meetsContract {w vCap eCap tCap : ℕ} {p : Program}
    {b bEdge bOps : ℕ} {G T : MGraph} {eT : List (ℕ × ℕ × ℕ)}
    (hp : p.HasAt b (readInitOpsProcs bEdge)) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (b + readInitOpsIdxSplitT) (splitTreeEdgesContract w vCap eCap tCap G T eT) := by
  refine meetsContract_of_runs
    (hp.get (i := readInitOpsIdxSplitT) (by simp [readInitOpsProcs, readInitOpsIdxSplitT])) ?_
  rintro args mem pos ω hargs
    ⟨gPtr, livePtr, frzPtr, ePtrT, rfl, hw16, hg_le, hl_le, hf_lt, hePtr_le, heT_at, hnd,
      heT_spec, heT_cov, hAgree, hT_cap, hG, hL0, hF0⟩
  simp only [readInitOpsProcs, readInitOpsIdxSplitT, List.getElem_cons_succ, List.getElem_cons_zero]
  have hnET_lt : eT.length < 2 ^ w := hargs _ (by simp)
  have hG_lt_w : gPtr + dynGraphSize vCap eCap < 2 ^ w := by omega
  have hL_lt_w : livePtr + dynGraphSize vCap eCap < 2 ^ w := by omega
  have hvc_g : mem gPtr = vCap := by simpa [dgVCapOff] using hG.2.2.2.1
  have hec_g : mem (gPtr + 1) = eCap := by simpa [dgECapOff] using hG.2.2.2.2.1
  let baseG : MGraph := { V := G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 }
  let frame : (ℕ → ℕ) → Prop := fun m =>
    ∀ a, (a < livePtr ∨ livePtr + dynGraphSize vCap eCap ≤ a) →
      (a < frzPtr ∨ frzPtr + dynGraphSize vCap tCap ≤ a) → m a = mem a
  let Inv : ℕ → State → Prop := fun k st =>
    st.regs 0 = gPtr ∧ st.regs 1 = livePtr ∧ st.regs 2 = frzPtr ∧ st.regs 3 = ePtrT ∧
    st.regs 4 = eT.length ∧ st.regs 5 = vCap ∧ st.regs 6 = eCap ∧
    st.regs 7 = dgEPresBase gPtr vCap ∧ st.regs 8 = k ∧
    DynGraphAt st.mem livePtr vCap eCap ((eT.take k).foldl (splitTStep G) (baseG, baseG)).1 ∧
    DynGraphAt st.mem frzPtr vCap tCap ((eT.take k).foldl (splitTStep G) (baseG, baseG)).2 ∧
    frame st.mem
  let body : Stmt :=
    .assign 9 (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 8))) ;;
    .assign 10 (.load (.reg 9)) ;;
    .assign 11 (.load (.bin .add (.reg 9) (.const 1))) ;;
    .assign 12 (.load (.bin .add (.reg 9) (.const 2))) ;;
    .cond (.bin .lt (.reg 10) (.reg 6))
      (.cond (.load (.bin .add (.reg 7) (.reg 10)))
        (.call 13 (bEdge + dgIdxInsertEdge) [.reg 1, .reg 10, .reg 11, .reg 12])
        (.call 13 (bEdge + dgIdxInsertEdge) [.reg 2, .reg 10, .reg 11, .reg 12]))
      (.call 13 (bEdge + dgIdxInsertEdge) [.reg 2, .reg 10, .reg 11, .reg 12])
  apply runs_start_le
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) hvc_g) ?_
  refine runs_seq_assign_le (v := eCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega)) (by dsimp [dynGraphSize] at hG_lt_w; omega)) hec_g) ?_
  refine runs_seq_assign_le (v := dgEPresBase gPtr vCap)
    (by dsimp only [dgEPresBase]; dsimp only [dynGraphSize] at hG_lt_w; simp only [startState]; eval_expr) ?_
  let stInit : State :=
    { mem := mem
      regs := Function.update (Function.update (Function.update (startState [gPtr, livePtr, frzPtr, ePtrT, eT.length] mem pos).regs 5 vCap) 6 eCap) 7 (dgEPresBase gPtr vCap)
      pos := pos }
  have hLoop : Triple w p (fun st => st = stInit)
      (forRange 8 (.const 0) (.reg 4) body) (normalPost (Inv eT.length))
      (fun _ => (eT.length - 0) * (520 + Expr.size (.reg 4) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 4) + 5)) := by
    refine Triple.forRange_const 520 0 eT.length (Nat.zero_le _) (by omega) (fun _ => hnET_lt)
      (fun st hst => by
        subst hst
        refine ⟨Expr.eval_const (by omega), by simp [stInit, startState], by simp [stInit, startState],
          by simp [stInit, startState], by simp [stInit, startState], by simp [stInit, startState],
          by simp [stInit], by simp [stInit], by simp [stInit], by simp,
          by simpa [stInit, baseG] using hL0, by simpa [stInit, baseG] using hF0,
          fun _ _ _ => rfl⟩)
      (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.2.1)
      (fun _ _ _ _ hI => by simp [Expr.eval, hI.2.2.2.2.1])
      (fun k _ hk st ω' hI => by
        obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, hLk, hFk, hfr⟩ := hI
        set t := eT[k] with ht_def
        set e := t.1
        set u := t.2.1
        set v_e := t.2.2
        obtain ⟨heT, hu_eq, hv_eq⟩ := heT_spec t (List.getElem_mem hk)
        have hu_V : u ∈ G.V := by change t.2.1 ∈ G.V; rw [← hAgree.2.2.1, hu_eq]; exact (hAgree.2.1 e heT).1
        have hv_V : v_e ∈ G.V := by change t.2.2 ∈ G.V; rw [← hAgree.2.2.1, hv_eq]; exact (hAgree.2.1 e heT).2
        have he_tcap : e < tCap := hT_cap e heT
        have he_w : e < 2 ^ w := by dsimp [dynGraphSize] at hf_lt; omega
        have hec_w : eCap < 2 ^ w := by dsimp [dynGraphSize] at hG_lt_w; omega
        have hu_w : u < 2 ^ w := by have := hG.2.1 u hu_V; dsimp [dynGraphSize] at hG_lt_w; omega
        have hv_w : v_e < 2 ^ w := by have := hG.2.1 v_e hv_V; dsimp [dynGraphSize] at hG_lt_w; omega
        have hV_L : ((eT.take k).foldl (splitTStep G) (baseG, baseG)).1.V = G.V :=
          (foldl_splitTStep_V G (eT.take k) baseG baseG).1
        have hV_F : ((eT.take k).foldl (splitTStep G) (baseG, baseG)).2.V = G.V :=
          (foldl_splitTStep_V G (eT.take k) baseG baseG).2
        have he_notL : e ∉ ((eT.take k).foldl (splitTStep G) (baseG, baseG)).1.E := by
          rw [(foldl_splitTStep_E G (eT.take k) baseG baseG e).1]
          rintro (h | ⟨_, t', ht', heq⟩)
          · exact Finset.notMem_empty e h
          · exact take_nodup_fst eT k hnd hk t' ht' heq
        have he_notF : e ∉ ((eT.take k).foldl (splitTStep G) (baseG, baseG)).2.E := by
          rw [(foldl_splitTStep_E G (eT.take k) baseG baseG e).2]
          rintro (h | ⟨_, t', ht', heq⟩)
          · exact Finset.notMem_empty e h
          · exact take_nodup_fst eT k hnd hk t' ht' heq
        have haddr0 : st.mem (ePtrT + 3 * k) = e := by
          rw [hfr _ (Or.inl (by omega)) (Or.inl (by omega))]; exact (heT_at k hk).1
        have haddr1 : st.mem (ePtrT + 3 * k + 1) = u := by
          rw [hfr _ (Or.inl (by omega)) (Or.inl (by omega))]; exact (heT_at k hk).2.1
        have haddr2 : st.mem (ePtrT + 3 * k + 2) = v_e := by
          rw [hfr _ (Or.inl (by omega)) (Or.inl (by omega))]; exact (heT_at k hk).2.2
        have hG_cur : DynGraphAt st.mem gPtr vCap eCap G :=
          hG.of_agree fun a ha1 ha2 => hfr a (Or.inl (by omega)) (Or.inl (by omega))
        have htake_eq : (eT.take (k + 1)).foldl (splitTStep G) (baseG, baseG) =
            splitTStep G ((eT.take k).foldl (splitTStep G) (baseG, baseG)) t := by
          rw [List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons, List.foldl_nil]
        apply runs_start_le
        refine runs_seq_assign_le (v := ePtrT + 3 * k)
          (Expr.eval_add (Expr.eval_reg_of_eq r3)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq r8) (by omega)) (by omega)) ?_
        refine runs_seq_assign_le (v := e)
          (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp)) haddr0) ?_
        refine runs_seq_assign_le (v := u)
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_const (by omega)) (by omega)) haddr1) ?_
        refine runs_seq_assign_le (v := v_e)
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_const (by omega)) (by omega)) haddr2) ?_
        by_cases he_cap : e < eCap
        · have hlt_eval : (Expr.bin .lt (.reg 10) (.reg 6)).eval w
              { mem := st.mem, regs := Function.update (Function.update (Function.update (Function.update st.regs 9 (ePtrT + 3 * k)) 10 e) 11 u) 12 v_e, pos := st.pos } = some 1 :=
            Expr.eval_lt_true (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp [r6])) he_cap (by omega)
          have hep_lt : dgEPresBase gPtr vCap + e < 2 ^ w := by
            dsimp [dgEPresBase, dynGraphSize] at hG_lt_w ⊢; omega
          have hep_eq : st.mem (dgEPresBase gPtr vCap + e) = if e ∈ G.E then 1 else 0 :=
            hG_cur.2.2.2.2.2.2.2.2.2.2.2.1 e he_cap
          by_cases heG : e ∈ G.E
          · have hpres_eval : (Expr.load (.bin .add (.reg 7) (.reg 10))).eval w
                { mem := st.mem, regs := Function.update (Function.update (Function.update (Function.update st.regs 9 (ePtrT + 3 * k)) 10 e) 11 u) 12 v_e, pos := st.pos } = some 1 :=
              Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r7]))
                (Expr.eval_reg_of_eq (by simp)) hep_lt) (by simpa [heG] using hep_eq)
            refine runs_cond_pos_le hlt_eval (by decide) ?_
            refine runs_cond_pos_le hpres_eval (by decide) ?_
            refine runs_call_le (dgInsertEdge_meetsContract hpEdge hpOps)
              (vs := [livePtr, e, u, v_e]) (by simp [evalArgs, Expr.eval, r1])
              (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl|rfl|rfl) <;> omega)
              ⟨livePtr, e, u, v_e, rfl, hw16, hL_lt_w, hV_L.symm ▸ hu_V, hV_L.symm ▸ hv_V, hLk⟩ ?_
            rintro _ mem' pos' ⟨_, _, _, _, hEq, _, hL', hfr'⟩
            simp only [List.cons.injEq, and_true] at hEq
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq
            refine ⟨⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
              by simp [r5], by simp [r6], by simp [r7], by simp, ?_, ?_, ?_⟩, by simp [r8]⟩, ?_⟩
            · rw [htake_eq]; simp only [splitTStep, show t.1 ∈ G.E from heG, ↓reduceIte]
              simpa [he_cap, he_notL] using hL'
            · rw [htake_eq]; simp only [splitTStep, show t.1 ∈ G.E from heG, ↓reduceIte]
              exact hFk.of_agree fun a ha1 _ => hfr' a (Or.inr (by omega))
            · exact fun a haL haF => (hfr' a haL).trans (hfr a haL haF)
            · simp only [dgInsertEdgeContract, argsSize, Expr.size]; omega
          · have hpres_eval : (Expr.load (.bin .add (.reg 7) (.reg 10))).eval w
                { mem := st.mem, regs := Function.update (Function.update (Function.update (Function.update st.regs 9 (ePtrT + 3 * k)) 10 e) 11 u) 12 v_e, pos := st.pos } = some 0 :=
              Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r7]))
                (Expr.eval_reg_of_eq (by simp)) hep_lt) (by simpa [heG] using hep_eq)
            refine runs_cond_pos_le hlt_eval (by decide) ?_
            refine runs_cond_zero_le hpres_eval ?_
            refine runs_call_le (dgInsertEdge_meetsContract hpEdge hpOps)
              (vs := [frzPtr, e, u, v_e]) (by simp [evalArgs, Expr.eval, r2])
              (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl|rfl|rfl) <;> omega)
              ⟨frzPtr, e, u, v_e, rfl, hw16, hf_lt, hV_F.symm ▸ hu_V, hV_F.symm ▸ hv_V, hFk⟩ ?_
            rintro _ mem' pos' ⟨_, _, _, _, hEq, _, hF', hfr'⟩
            simp only [List.cons.injEq, and_true] at hEq
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq
            refine ⟨⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
              by simp [r5], by simp [r6], by simp [r7], by simp, ?_, ?_, ?_⟩, by simp [r8]⟩, ?_⟩
            · rw [htake_eq]; simp only [splitTStep, show t.1 ∉ G.E from heG, ↓reduceIte]
              exact hLk.of_agree fun a _ ha2 => hfr' a (Or.inl (by omega))
            · rw [htake_eq]; simp only [splitTStep, show t.1 ∉ G.E from heG, ↓reduceIte]
              simpa [he_tcap, he_notF] using hF'
            · exact fun a haL haF => (hfr' a haF).trans (hfr a haL haF)
            · simp only [dgInsertEdgeContract, argsSize, Expr.size]; omega
        · have heG : e ∉ G.E := fun hc => he_cap (hG.2.2.1 e hc)
          have hlt_eval : (Expr.bin .lt (.reg 10) (.reg 6)).eval w
              { mem := st.mem, regs := Function.update (Function.update (Function.update (Function.update st.regs 9 (ePtrT + 3 * k)) 10 e) 11 u) 12 v_e, pos := st.pos } = some 0 :=
            Expr.eval_lt_false (Expr.eval_reg_of_eq (v := e) (by simp))
              (Expr.eval_reg_of_eq (v := eCap) (by simp [r6])) (by omega) (by omega)
          refine runs_cond_zero_le hlt_eval ?_
          refine runs_call_le (dgInsertEdge_meetsContract hpEdge hpOps)
            (vs := [frzPtr, e, u, v_e]) (by simp [evalArgs, Expr.eval, r2])
            (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl|rfl|rfl) <;> omega)
            ⟨frzPtr, e, u, v_e, rfl, hw16, hf_lt, hV_F.symm ▸ hu_V, hV_F.symm ▸ hv_V, hFk⟩ ?_
          rintro _ mem' pos' ⟨_, _, _, _, hEq, _, hF', hfr'⟩
          simp only [List.cons.injEq, and_true] at hEq
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq
          refine ⟨⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
            by simp [r5], by simp [r6], by simp [r7], by simp, ?_, ?_, ?_⟩, by simp [r8]⟩, ?_⟩
          · rw [htake_eq]; simp only [splitTStep, show t.1 ∉ G.E from heG, ↓reduceIte]
            exact hLk.of_agree fun a _ ha2 => hfr' a (Or.inl (by omega))
          · rw [htake_eq]; simp only [splitTStep, show t.1 ∉ G.E from heG, ↓reduceIte]
            simpa [he_tcap, he_notF] using hF'
          · exact fun a haL haF => (hfr' a haF).trans (hfr a haL haF)
          · simp only [dgInsertEdgeContract, argsSize, Expr.size]; omega)
  refine runs_seq_triple_le hLoop rfl ?_
  rintro st ⟨_, _, _, _, _, _, _, _, _, hL_end, hF_end, hfrEnd⟩
  rw [List.take_of_length_le le_rfl] at hL_end hF_end
  have hSameL : SameGraph (eT.foldl (splitTStep G) (baseG, baseG)).1 (liveT G T) := by
    refine ⟨(foldl_splitTStep_V G eT baseG baseG).1, ?_, ?_⟩
    · ext e
      rw [(foldl_splitTStep_E G eT baseG baseG e).1]
      simp only [baseG, Finset.notMem_empty, false_or, liveT, Finset.mem_inter]
      constructor
      · rintro ⟨heG, t, ht, rfl⟩; exact ⟨(heT_spec t ht).1, heG⟩
      · rintro ⟨heT, heG⟩; exact ⟨heG, heT_cov e heT⟩
    · intro e he
      rw [(foldl_splitTStep_E G eT baseG baseG e).1] at he
      rcases he with h | ⟨heG, t, ht, rfl⟩
      · exact absurd h (Finset.notMem_empty _)
      · obtain ⟨htT, htTail, htHead⟩ := heT_spec t ht
        obtain ⟨h1, h2⟩ := (foldl_splitTStep_ends G eT baseG baseG t ht hnd).1 heG
        obtain ⟨hGT, hGH⟩ := hAgree.2.2.2 t.1 htT heG
        exact ⟨h1.trans (htTail.trans hGT), h2.trans (htHead.trans hGH)⟩
  have hSameF : SameGraph (eT.foldl (splitTStep G) (baseG, baseG)).2 (frozenT G T) := by
    refine ⟨(foldl_splitTStep_V G eT baseG baseG).2, ?_, ?_⟩
    · ext e
      rw [(foldl_splitTStep_E G eT baseG baseG e).2]
      simp only [baseG, Finset.notMem_empty, false_or, frozenT, Finset.mem_sdiff]
      constructor
      · rintro ⟨heG, t, ht, rfl⟩; exact ⟨(heT_spec t ht).1, heG⟩
      · rintro ⟨heT, heG⟩; exact ⟨heG, heT_cov e heT⟩
    · intro e he
      rw [(foldl_splitTStep_E G eT baseG baseG e).2] at he
      rcases he with h | ⟨heG, t, ht, rfl⟩
      · exact absurd h (Finset.notMem_empty _)
      · obtain ⟨_, htTail, htHead⟩ := heT_spec t ht
        obtain ⟨h1, h2⟩ := (foldl_splitTStep_ends G eT baseG baseG t ht hnd).2 heG
        exact ⟨h1.trans htTail, h2.trans htHead⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega))
    ⟨gPtr, livePtr, frzPtr, ePtrT, rfl, rfl,
      DynGraphAt.of_same hL_end hSameL, DynGraphAt.of_same hF_end hSameF, hfrEnd⟩ ?_
  simp only [splitTreeEdgesContract, Expr.size, Nat.sub_zero]
  omega

end MinCostFlow.SparseCore.Program.Read
