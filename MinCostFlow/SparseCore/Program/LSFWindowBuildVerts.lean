module

public import MinCostFlow.SparseCore.Program.LSFWindowBuildDefs
import WordRAM.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verification of Canonical Guest Builder Sub-Procedures (`LSFWindowBuildHelpers`)

Proves execution lemmas for the five helper procedures in `LSFWindowBuildDefs`:
* `pushHalfEdgeProc_runs`
* `maxCapListProc_runs`
* `buildCanonVertsProc_runs`
* `buildCanonEdgesProc_runs`
* `buildCanonIncProc_runs`
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
  MinCostFlow.DynSpanner.Program MinCostFlow.Num

/-! ## 1. `pushHalfEdgeProc` -/

lemma pushHalfEdgeProc_runs {w base vCap eCap s he : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {pos : ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hs : s < vCap) (hhe : he < 2 * eCap)
    (hsz_lt : base + dynGraphSize vCap eCap < 2 ^ w)
    (hold : mem (dgIncHeadBase base vCap + s) = 0 ∨ mem (dgIncHeadBase base vCap + s) - 1 < 2 * eCap)
    (hdeg : mem (dgSlotDegBase base vCap + s) + 1 < 2 ^ w) :
    ∃ st' c,
      Runs w p ω pushHalfEdgeProc (startState [base, vCap, eCap, s, he] mem pos)
        (.returned 0) st' c ∧
      (∀ a < dynGraphSize vCap eCap,
        st'.mem (base + a) =
          pushHalfEdgeMem vCap eCap s he (fun z => mem (base + z)) a) ∧
      (∀ addr, addr < base ∨ base + dynGraphSize vCap eCap ≤ addr → st'.mem addr = mem addr) ∧
      c ≤ 100 := by
  have hsz_eq : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  set incA := dgIncHeadBase base vCap + s
  set degA := dgSlotDegBase base vCap + s
  set prevB := dgHePrevBase base vCap eCap
  set nextB := dgHeNextBase base vCap eCap
  set oldHead := mem incA
  set deg := mem degA
  have hincA_eq : base + 4 + 6 * vCap + s = incA := rfl
  have hdegA_eq : base + 4 + 5 * vCap + s = degA := rfl
  have hprevB_eq : base + 4 + 7 * vCap + 5 * eCap = prevB := rfl
  have hnextB_eq : base + 4 + 7 * vCap + 7 * eCap = nextB := rfl
  have hshift_inc : incA = base + (dgIncHeadBase 0 vCap + s) := by dsimp [incA, dgIncHeadBase]; omega
  have hshift_deg : degA = base + (dgSlotDegBase 0 vCap + s) := by dsimp [degA, dgSlotDegBase]; omega
  have hshift_prev : ∀ x, prevB + x = base + (dgHePrevBase 0 vCap eCap + x) := fun x => by
    dsimp [prevB, dgHePrevBase]; omega
  have hshift_next : ∀ x, nextB + x = base + (dgHeNextBase 0 vCap eCap + x) := fun x => by
    dsimp [nextB, dgHeNextBase]; omega
  suffices hmain : ∃ o st' c,
      Runs w p ω pushHalfEdgeProc (startState [base, vCap, eCap, s, he] mem pos) o st' c ∧
      (o = .returned 0 ∧
        (∀ a < dynGraphSize vCap eCap,
          st'.mem (base + a) = pushHalfEdgeMem vCap eCap s he (fun z => mem (base + z)) a) ∧
        (∀ addr, addr < base ∨ base + dynGraphSize vCap eCap ≤ addr → st'.mem addr = mem addr)) ∧
      0 + c ≤ 100 by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2⟩, hc⟩
    exact ⟨st', c, hrun, h1, h2, by omega⟩
  unfold pushHalfEdgeProc
  refine runs_seq_assign_le (v := incA)
    (by simp [Expr.eval, BinOp.eval, startState, hincA_eq,
      show 4 < 2 ^ w by omega, show 6 < 2 ^ w by omega, show base + 4 < 2 ^ w by omega,
      show 6 * vCap < 2 ^ w by omega, show base + 4 + 6 * vCap < 2 ^ w by omega,
      show incA < 2 ^ w by dsimp [incA, dgIncHeadBase]; omega]) ?_
  refine runs_seq_assign_le (v := degA)
    (by simp [Expr.eval, BinOp.eval, startState, hdegA_eq,
      show 4 < 2 ^ w by omega, show 5 < 2 ^ w by omega, show base + 4 < 2 ^ w by omega,
      show 5 * vCap < 2 ^ w by omega, show base + 4 + 5 * vCap < 2 ^ w by omega,
      show degA < 2 ^ w by dsimp [degA, dgSlotDegBase]; omega]) ?_
  refine runs_seq_assign_le (v := prevB)
    (by simp [Expr.eval, BinOp.eval, startState, hprevB_eq,
      show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega, show 5 < 2 ^ w by omega,
      show base + 4 < 2 ^ w by omega, show 7 * vCap < 2 ^ w by omega,
      show base + 4 + 7 * vCap < 2 ^ w by omega, show 5 * eCap < 2 ^ w by omega,
      show prevB < 2 ^ w by dsimp [prevB, dgHePrevBase]; omega]) ?_
  refine runs_seq_assign_le (v := nextB)
    (by simp [Expr.eval, BinOp.eval, startState, hnextB_eq,
      show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega, show base + 4 < 2 ^ w by omega,
      show 7 * vCap < 2 ^ w by omega, show base + 4 + 7 * vCap < 2 ^ w by omega,
      show 7 * eCap < 2 ^ w by omega, show nextB < 2 ^ w by dsimp [nextB, dgHeNextBase]; omega]) ?_
  refine runs_seq_assign_le (v := oldHead)
    (Expr.eval_load_of_eq (by simp [Expr.eval]) rfl) ?_
  refine runs_seq_assign_le (v := deg)
    (Expr.eval_load_of_eq (by simp [Expr.eval]) rfl) ?_
  refine runs_seq_store_le (x := prevB + he) (v := 0)
    (by simp [Expr.eval, BinOp.eval, startState, show prevB + he < 2 ^ w by dsimp [prevB, dgHePrevBase]; omega])
    (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_
  refine runs_seq_store_le (x := nextB + he) (v := oldHead)
    (by simp [Expr.eval, BinOp.eval, startState, show nextB + he < 2 ^ w by dsimp [nextB, dgHeNextBase]; omega])
    (by simp [Expr.eval]) ?_
  set m2 := Function.update (Function.update mem (prevB + he) 0) (nextB + he) oldHead
  have hcond_step : ∃ st3 c3,
      Runs w p ω
        (.cond (.bin .lt (.const 0) (.reg 9))
          (.store (.bin .add (.reg 7) (.bin .sub (.reg 9) (.const 1))) (.bin .add (.reg 4) (.const 1)))
          .nop)
        ⟨m2, Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update (startState [base, vCap, eCap, s, he] mem pos).regs 5 incA)
          6 degA) 7 prevB) 8 nextB) 9 oldHead) 10 deg, pos⟩
        .normal st3 c3 ∧
      st3.regs = Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (startState [base, vCap, eCap, s, he] mem pos).regs 5 incA)
        6 degA) 7 prevB) 8 nextB) 9 oldHead) 10 deg ∧
      st3.mem = (if oldHead = 0 then m2 else Function.update m2 (prevB + (oldHead - 1)) (he + 1)) ∧
      c3 ≤ 15 := by
    set st2 : State :=
      ⟨m2, Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (startState [base, vCap, eCap, s, he] mem pos).regs 5 incA)
        6 degA) 7 prevB) 8 nextB) 9 oldHead) 10 deg, pos⟩
    by_cases h0 : oldHead = 0
    · refine ⟨st2, 5, runs_cond_iff.mpr ⟨0, 1,
        by simp [st2, Expr.eval, BinOp.eval, h0, show 0 < 2 ^ w by omega],
        by simp [st2, runs_nop_iff], by simp [Expr.size]⟩, rfl, by simp [st2, h0], by omega⟩
    · have hpos : 0 < oldHead := Nat.pos_of_ne_zero h0
      have hlt_old : oldHead - 1 < 2 * eCap := hold.resolve_left h0
      have hsub_lt : oldHead - 1 < 2 ^ w := by omega
      have haddr_lt : prevB + (oldHead - 1) < 2 ^ w := by dsimp [prevB, dgHePrevBase]; omega
      have hhe1_lt : he + 1 < 2 ^ w := by omega
      refine ⟨{ st2 with mem := Function.update m2 (prevB + (oldHead - 1)) (he + 1) }, 13,
        runs_cond_iff.mpr ⟨1, 9,
          by simp [st2, Expr.eval, BinOp.eval, hpos, show 0 < 2 ^ w by omega, show 1 < 2 ^ w by omega],
          by
            simp only [Nat.one_ne_zero, ↓reduceIte]
            rw [runs_store_iff]
            exact ⟨prevB + (oldHead - 1), he + 1,
              by simp [st2, Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega, hsub_lt, haddr_lt],
              by simp [st2, Expr.eval, BinOp.eval, startState, show 1 < 2 ^ w by omega, hhe1_lt],
              rfl, rfl, by simp [Expr.size]⟩,
          by simp [Expr.size]⟩, rfl, by simp [h0], by omega⟩
  refine runs_seq_of_exists' hcond_step ?_
  intro st3 c3 ⟨hr3, hm3, hc3⟩
  refine runs_seq_store_le (x := incA) (v := he + 1)
    (by simp [Expr.eval, hr3])
    (by simp [Expr.eval, BinOp.eval, hr3, startState, show 1 < 2 ^ w by omega, show he + 1 < 2 ^ w by omega]) ?_
  refine runs_seq_store_le (x := degA) (v := deg + 1)
    (by simp [Expr.eval, hr3])
    (by simp [Expr.eval, BinOp.eval, hr3, show 1 < 2 ^ w by omega, hdeg]) ?_
  refine runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ⟨rfl, ?_, ?_⟩ ?_
  · intro a ha
    have hmem_fin : (fun z => Function.update (Function.update st3.mem incA (he + 1)) degA (deg + 1) (base + z)) =
          pushHalfEdgeMem vCap eCap s he (fun z => mem (base + z)) := by
      have hupd : ∀ (f : ℕ → ℕ) (k v : ℕ),
          (fun z => Function.update f (base + k) v (base + z)) = Function.update (fun z => f (base + z)) k v := by
        intro f k v; funext z
        by_cases hkz : z = k
        · subst hkz; simp
        · rw [Function.update_of_ne (by omega), Function.update_of_ne hkz]
      have hinc_val : mem (base + (dgIncHeadBase 0 vCap + s)) = oldHead := by rw [← hshift_inc]
      have hdeg_val : mem (base + (dgSlotDegBase 0 vCap + s)) = deg := by rw [← hshift_deg]
      rw [hm3]
      unfold pushHalfEdgeMem
      dsimp only
      simp only [hinc_val, hdeg_val, hshift_deg, hshift_inc, hupd]
      split_ifs with h0
      · dsimp only [m2]; simp only [hshift_next, hshift_prev, hupd]
      · dsimp only [m2]; simp only [hshift_prev, hshift_next, hupd]
    exact congrFun hmem_fin a
  · intro addr haddr
    have hdeg_in : base ≤ degA ∧ degA < base + dynGraphSize vCap eCap := by
      dsimp [degA, dgSlotDegBase]; omega
    have hinc_in : base ≤ incA ∧ incA < base + dynGraphSize vCap eCap := by
      dsimp [incA, dgIncHeadBase]; omega
    have hprev_in : base ≤ prevB + he ∧ prevB + he < base + dynGraphSize vCap eCap := by
      dsimp [prevB, dgHePrevBase]; omega
    have hnext_in : base ≤ nextB + he ∧ nextB + he < base + dynGraphSize vCap eCap := by
      dsimp [nextB, dgHeNextBase]; omega
    dsimp only
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm3]
    split_ifs with h0
    · dsimp only [m2]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · have hlt_old : oldHead - 1 < 2 * eCap := hold.resolve_left h0
      have hold_in : base ≤ prevB + (oldHead - 1) ∧ prevB + (oldHead - 1) < base + dynGraphSize vCap eCap := by
        dsimp [prevB, dgHePrevBase]; omega
      dsimp only [m2]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · simp only [Expr.size]; omega

/-! ## 2. `maxCapListProc` -/

lemma maxCapListProc_runs {w arr : ℕ} {L : List ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {pos : ℕ}
    (hw16 : 16 ≤ 2 ^ w) (harr : arr + L.length < 2 ^ w)
    (hL : ListAt mem arr L) (hval : ∀ x ∈ L, x + 1 < 2 ^ w) :
    ∃ st' c,
      Runs w p ω maxCapListProc (startState [arr, L.length] mem pos)
        (.returned (max 1 (L.foldl max 0 + 1))) st' c ∧
      st'.mem = mem ∧
      c ≤ 30 * L.length + 25 := by
  cases L with
  | nil =>
    refine ⟨startState [arr, 0] mem pos, 6, ?_, rfl, by omega⟩
    unfold maxCapListProc
    rw [runs_cond_iff]
    exact ⟨1, 2, by simp [Expr.eval, BinOp.eval, startState, show 0 < 2 ^ w by omega, show 1 < 2 ^ w by omega],
      by simp [runs_ret_iff, Expr.eval, show 1 < 2 ^ w by omega], by simp [Expr.size]⟩
  | cons x xs =>
    set L := x :: xs
    have hlen_pos : 0 < L.length := by simp [L]
    have hmax_eq : max 1 (L.foldl max 0 + 1) = L.foldl max 0 + 1 := max_eq_right (Nat.succ_pos _)
    rw [hmax_eq]
    suffices hmain : ∃ o st' c,
        Runs w p ω maxCapListProc (startState [arr, L.length] mem pos) o st' c ∧
        (o = .returned (L.foldl max 0 + 1) ∧ st'.mem = mem) ∧
        0 + c ≤ 30 * L.length + 25 by
      rcases hmain with ⟨_, st', c, hrun, ⟨rfl, hm⟩, hc⟩
      exact ⟨st', c, hrun, hm, by omega⟩
    unfold maxCapListProc
    refine WordRAM.runs_cond_le (v := 0)
      (by simp [Expr.eval, BinOp.eval, startState, show L.length ≠ 0 by omega, show 0 < 2 ^ w by omega])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_
    let Inv : ℕ → State → Prop := fun i st =>
      st.regs 0 = arr ∧ st.regs 1 = L.length ∧ st.regs 2 = (L.take i).foldl max 0 ∧
      st.regs 3 = i ∧ st.mem = mem
    have hloop : Triple w p
        (fun st => st = { mem := mem, regs := Function.update (startState [arr, L.length] mem pos).regs 2 0, pos := pos })
        (forRange 3 (.const 0) (.reg 1)
          (.assign 4 (.load (.bin .add (.reg 0) (.reg 3))) ;;
           .cond (.bin .lt (.reg 2) (.reg 4)) (.assign 2 (.reg 4)) .nop))
        (normalPost (Inv L.length)) (fun _ => 25 * L.length + 10) := by
      refine (Triple.forRange_const 16 0 L.length (Nat.zero_le _) (by omega) (fun _ => by omega)
        (fun st hst => by
          subst hst
          exact ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], by simp [startState], by simp [startState],
            by simp, by simp, rfl⟩)
        (fun _ _ _ _ hi => hi.2.2.2.1)
        (fun _ st _ _ hi => by simp [Expr.eval, hi.2.1])
        (fun i _ hi st ω' hinv => by
          rcases hinv with ⟨hr0, hr1, hr2, hr3, hmem⟩
          have hmem_i : st.mem (arr + i) = L[i] := by rw [hmem]; exact hL i hi
          have htake : (L.take (i + 1)).foldl max 0 = max ((L.take i).foldl max 0) L[i] := by
            rw [List.take_succ_eq_append_getElem hi, List.foldl_append, List.foldl_cons, List.foldl_nil]
          refine runs_start_le ?_
          refine runs_seq_assign_le (v := L[i])
            (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr0, hr3, show arr + i < 2 ^ w by omega]) hmem_i) ?_
          by_cases hlt : (L.take i).foldl max 0 < L[i]
          · refine WordRAM.runs_cond_le (v := 1)
              (by simp [Expr.eval, BinOp.eval, hr2, hlt, show 1 < 2 ^ w by omega])
              (fun _ => ?_) (fun h => by cases h)
            refine runs_assign_le (v := L[i]) (by simp [Expr.eval])
              ⟨⟨by simp [hr0], by simp [hr1], by simp [htake, hlt.le], by simp, hmem⟩,
               by simp [hr3]⟩ (by dsimp [Expr.size]; omega)
          · refine WordRAM.runs_cond_le (v := 0)
              (by simp [Expr.eval, BinOp.eval, hr2, hlt, show 0 < 2 ^ w by omega])
              (fun h => absurd rfl h) (fun _ => ?_)
            exact runs_nop_le
              ⟨⟨by simp [hr0], by simp [hr1], by simp [htake, Nat.le_of_not_lt hlt, hr2],
                by simp, hmem⟩, by simp [hr3]⟩ (by dsimp [Expr.size]; omega))).mono_cost
        (fun _ _ => by dsimp [Expr.size]; omega)
    refine runs_seq_triple_le hloop rfl fun st₁ hinv => ?_
    rcases hinv with ⟨_, _, hr2, _, hmem⟩
    rw [List.take_length] at hr2
    have hfold_lt : L.foldl max 0 + 1 < 2 ^ w := by
      have hfold_le : ∀ (xs : List ℕ) (init : ℕ),
          init + 1 < 2 ^ w → (∀ y ∈ xs, y + 1 < 2 ^ w) → xs.foldl max init + 1 < 2 ^ w := by
        intro xs
        induction xs with
        | nil => intro init hi _; exact hi
        | cons a as ih =>
          intro init hi has
          exact ih (max init a) (by
            have ha := has a List.mem_cons_self
            rcases le_total init a with h | h <;> simp [h, hi, ha])
            (fun y hy => has y (List.mem_cons_of_mem _ hy))
      exact hfold_le L 0 (by omega) hval
    exact runs_ret_le (v := L.foldl max 0 + 1)
      (by simp [Expr.eval, BinOp.eval, hr2, show 1 < 2 ^ w by omega, hfold_lt])
      ⟨rfl, hmem⟩ (by dsimp [Expr.size]; omega)

/-! ## 3. `buildCanonVertsProc` -/

lemma buildCanonVertsProc_runs {w guestBase : ℕ} {G₀ : MGraph} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {pos : ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hsz_lt : guestBase + dynGraphSize (canonVCap G₀) (canonECap G₀) < 2 ^ w)
    (hvL : ListAt mem (dgVListBase guestBase (canonVCap G₀)) (canonVList G₀)) :
    ∃ st' c,
      Runs w p ω buildCanonVertsProc (startState [guestBase, canonVCap G₀, G₀.n] mem pos)
        (.returned 0) st' c ∧
      (∀ v ∈ G₀.V,
        st'.mem (dgVPresBase guestBase + v) = 1 ∧
        st'.mem (dgVPosBase guestBase (canonVCap G₀) + v) = (canonVList G₀).idxOf v ∧
        st'.mem (dgExtToIntBase guestBase (canonVCap G₀) + v) = v ∧
        st'.mem (dgIntToExtBase guestBase (canonVCap G₀) + v) = v) ∧
      (∀ addr,
        (∀ v ∈ G₀.V,
          addr ≠ dgVPresBase guestBase + v ∧
          addr ≠ dgVPosBase guestBase (canonVCap G₀) + v ∧
          addr ≠ dgExtToIntBase guestBase (canonVCap G₀) + v ∧
          addr ≠ dgIntToExtBase guestBase (canonVCap G₀) + v) →
        st'.mem addr = mem addr) ∧
      c ≤ 50 * G₀.n + 80 := by
  set vCap := canonVCap G₀
  set eCap := canonECap G₀
  set vL := canonVList G₀
  have hvL_len : vL.length = G₀.n := G₀.V.length_sort (· ≤ ·)
  have hvL_nd : vL.Nodup := G₀.V.sort_nodup (· ≤ ·)
  have hvL_mem : ∀ v, v ∈ vL ↔ v ∈ G₀.V := fun v => G₀.V.mem_sort (· ≤ ·)
  have hsz_eq : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hn_le : G₀.n ≤ vCap := by
    have hsub : G₀.V ⊆ Finset.range vCap := fun v hv => Finset.mem_range.mpr (canonVCap_gt hv)
    calc G₀.n = G₀.V.card := rfl
      _ ≤ (Finset.range vCap).card := Finset.card_le_card hsub
      _ = vCap := Finset.card_range vCap
  suffices hmain : ∃ o st' c,
      Runs w p ω buildCanonVertsProc (startState [guestBase, vCap, G₀.n] mem pos) o st' c ∧
      (o = .returned 0 ∧
        (∀ v ∈ G₀.V,
          st'.mem (dgVPresBase guestBase + v) = 1 ∧
          st'.mem (dgVPosBase guestBase vCap + v) = vL.idxOf v ∧
          st'.mem (dgExtToIntBase guestBase vCap + v) = v ∧
          st'.mem (dgIntToExtBase guestBase vCap + v) = v) ∧
        (∀ addr,
          (∀ v ∈ G₀.V,
            addr ≠ dgVPresBase guestBase + v ∧
            addr ≠ dgVPosBase guestBase vCap + v ∧
            addr ≠ dgExtToIntBase guestBase vCap + v ∧
            addr ≠ dgIntToExtBase guestBase vCap + v) →
          st'.mem addr = mem addr)) ∧
      0 + c ≤ 50 * G₀.n + 80 by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2⟩, hc⟩
    exact ⟨st', c, hrun, h1, h2, by omega⟩
  unfold buildCanonVertsProc
  refine runs_seq_assign_le (v := dgVListBase guestBase vCap)
    (by simp [Expr.eval, BinOp.eval, startState, dgVListBase, show 4 < 2 ^ w by omega,
      show guestBase + 4 < 2 ^ w by omega, show guestBase + 4 + vCap < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dgVPresBase guestBase)
    (by simp [Expr.eval, BinOp.eval, startState, dgVPresBase, show 4 < 2 ^ w by omega,
      show guestBase + 4 < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dgVPosBase guestBase vCap)
    (by simp [Expr.eval, BinOp.eval, startState, dgVPosBase, show 4 < 2 ^ w by omega,
      show 2 < 2 ^ w by omega, show guestBase + 4 < 2 ^ w by omega,
      show 2 * vCap < 2 ^ w by omega, show guestBase + 4 + 2 * vCap < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dgExtToIntBase guestBase vCap)
    (by simp [Expr.eval, BinOp.eval, startState, dgExtToIntBase, show 4 < 2 ^ w by omega,
      show 3 < 2 ^ w by omega, show guestBase + 4 < 2 ^ w by omega,
      show 3 * vCap < 2 ^ w by omega, show guestBase + 4 + 3 * vCap < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dgIntToExtBase guestBase vCap)
    (by simp [Expr.eval, BinOp.eval, startState, dgIntToExtBase, show 4 < 2 ^ w by omega,
      show guestBase + 4 < 2 ^ w by omega,
      show 4 * vCap < 2 ^ w by omega, show guestBase + 4 + 4 * vCap < 2 ^ w by omega]) ?_
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 2 = G₀.n ∧ st.regs 3 = dgVListBase guestBase vCap ∧
    st.regs 4 = dgVPresBase guestBase ∧ st.regs 5 = dgVPosBase guestBase vCap ∧
    st.regs 6 = dgExtToIntBase guestBase vCap ∧ st.regs 7 = dgIntToExtBase guestBase vCap ∧
    st.regs 8 = i ∧
    (∀ j (_hj : j < i), ∀ (hjL : j < vL.length),
      let v := vL[j]'hjL
      st.mem (dgVPresBase guestBase + v) = 1 ∧
      st.mem (dgVPosBase guestBase vCap + v) = j ∧
      st.mem (dgExtToIntBase guestBase vCap + v) = v ∧
      st.mem (dgIntToExtBase guestBase vCap + v) = v) ∧
    (∀ addr,
      (∀ v ∈ G₀.V,
        addr ≠ dgVPresBase guestBase + v ∧
        addr ≠ dgVPosBase guestBase vCap + v ∧
        addr ≠ dgExtToIntBase guestBase vCap + v ∧
        addr ≠ dgIntToExtBase guestBase vCap + v) →
      st.mem addr = mem addr)
  have hloop : Triple w p
      (fun st => st.regs 2 = G₀.n ∧ st.regs 3 = dgVListBase guestBase vCap ∧
        st.regs 4 = dgVPresBase guestBase ∧ st.regs 5 = dgVPosBase guestBase vCap ∧
        st.regs 6 = dgExtToIntBase guestBase vCap ∧ st.regs 7 = dgIntToExtBase guestBase vCap ∧
        st.mem = mem)
      (forRange 8 (.const 0) (.reg 2)
        (.assign 9 (.load (.bin .add (.reg 3) (.reg 8))) ;;
         .store (.bin .add (.reg 4) (.reg 9)) (.const 1) ;;
         .store (.bin .add (.reg 5) (.reg 9)) (.reg 8) ;;
         .store (.bin .add (.reg 6) (.reg 9)) (.reg 9) ;;
         .store (.bin .add (.reg 7) (.reg 9)) (.reg 9)))
      (normalPost (Inv G₀.n)) (fun _ => 45 * G₀.n + 10) := by
    refine (Triple.forRange_const 35 0 G₀.n (Nat.zero_le _) (by omega) (fun _ => by omega)
      (fun st hst => by
        rcases hst with ⟨q2, q3, q4, q5, q6, q7, hmeq⟩
        exact ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], by simp [q2], by simp [q3],
          by simp [q4], by simp [q5], by simp [q6], by simp [q7], by simp,
          fun _ hj _ => absurd hj (Nat.not_lt_zero _), fun _ _ => congrFun hmeq _⟩)
      (fun _ _ _ _ hi => hi.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by simp [Expr.eval, hi.1])
      (fun i _ hi st ω' hinv => by
        rcases hinv with ⟨hr2, hr3, hr4, hr5, hr6, hr7, hr8, hset, hfr⟩
        have hiL : i < vL.length := by omega
        set v := vL[i]'hiL
        have hv_mem : v ∈ G₀.V := (hvL_mem v).mp (List.getElem_mem hiL)
        have hv_lt : v < vCap := canonVCap_gt hv_mem
        have hv_read : st.mem (dgVListBase guestBase vCap + i) = v := by
          rw [hfr _ (fun u hu => by
            have := canonVCap_gt hu
            dsimp [dgVListBase, dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]; omega)]
          exact hvL i hiL
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := v)
          (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr3, hr8,
            show dgVListBase guestBase vCap + i < 2 ^ w by dsimp [dgVListBase]; omega]) hv_read) ?_
        refine runs_seq_store_le (x := dgVPresBase guestBase + v) (v := 1)
          (by simp [Expr.eval, BinOp.eval, hr4, show dgVPresBase guestBase + v < 2 ^ w by dsimp [dgVPresBase]; omega])
          (by simp [Expr.eval, show 1 < 2 ^ w by omega]) ?_
        refine runs_seq_store_le (x := dgVPosBase guestBase vCap + v) (v := i)
          (by simp [Expr.eval, BinOp.eval, hr5, show dgVPosBase guestBase vCap + v < 2 ^ w by dsimp [dgVPosBase]; omega])
          (by simp [Expr.eval, hr8]) ?_
        refine runs_seq_store_le (x := dgExtToIntBase guestBase vCap + v) (v := v)
          (by simp [Expr.eval, BinOp.eval, hr6, show dgExtToIntBase guestBase vCap + v < 2 ^ w by dsimp [dgExtToIntBase]; omega])
          (by simp [Expr.eval]) ?_
        refine runs_store_le (x := dgIntToExtBase guestBase vCap + v) (v := v)
          (by simp [Expr.eval, BinOp.eval, hr7, show dgIntToExtBase guestBase vCap + v < 2 ^ w by dsimp [dgIntToExtBase]; omega])
          (by simp [Expr.eval]) ⟨⟨by simp [hr2], by simp [hr3], by simp [hr4], by simp [hr5],
            by simp [hr6], by simp [hr7], by simp, ?_, ?_⟩, by simp [hr8]⟩
          (by dsimp [Expr.size]; omega)
        · intro j hj hjL
          have hu_lt : vL[j] < vCap := canonVCap_gt ((hvL_mem _).mp (List.getElem_mem hjL))
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
          · have hne : vL[j] ≠ v := fun hEq => by
              have := (List.Nodup.getElem_inj hvL_nd).mp hEq; omega
            obtain ⟨h1, h2, h3, h4⟩ := hset j hj' hjL
            refine ⟨?_, ?_, ?_, ?_⟩ <;> (
              dsimp [dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase] at h1 h2 h3 h4 ⊢
              rwa [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
          · refine ⟨?_, ?_, ?_, ?_⟩ <;> (
              dsimp only [v, dgVPresBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase]
              try rw [Function.update_of_ne (by omega)]
              try rw [Function.update_of_ne (by omega)]
              try rw [Function.update_of_ne (by omega)]
              rw [Function.update_self])
        · intro addr haddr
          obtain ⟨h1, h2, h3, h4⟩ := haddr v hv_mem
          dsimp only
          rw [Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
              Function.update_of_ne h1]
          exact hfr addr haddr)).mono_cost (fun _ _ => by dsimp [Expr.size]; omega)
  refine runs_seq_triple_le hloop
    ⟨by simp [startState], by simp, by simp, by simp, by simp, by simp, rfl⟩ fun st₁ hinv => ?_
  rcases hinv with ⟨_, _, _, _, _, _, _, hset, hfr⟩
  refine runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ⟨rfl, ?_, hfr⟩
    (by simp only [Expr.size]; omega)
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((hvL_mem v).mpr hv)
  have h1 := hset j (by omega) hj
  rwa [List.Nodup.idxOf_getElem hvL_nd j hj]

end MinCostFlow.SparseCore.Program
