module

public import MinCostFlow.SparseCore.Program.TourOpsMoveSplit
public import MinCostFlow.SparseCore.Program.OrdStoreSort
import Mathlib.Tactic

/-!
# Collection, rank, sort, and next-block preparation for `moveEnds` (Op 0)

Defines and verifies `tourMoveCollectBody` (`[b, sv, selPtr, len, pairsPtr]` -> `m`), which
filters `sel` to unique active ends belonging to vertex `v` (`endOwner[k] = sv + 1`), writes
`(0, nodeOf k)` pairs at `pairsPtr`, and restores `markArr` to all zeros in `O(len + 1)` time.
Also defines `tourMoveRankSortNextBody` (verified in `TourOpsEditMoveSort.lean`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## WordRAM bodies -/

/-- `tourMoveCollect [b, sv, selPtr, len, pairsPtr]`: collect unique active nodes of `v` whose
keys appear in `mem[selPtr .. selPtr + len)` into `(0, node)` pairs at `pairsPtr`, restore
`markArr` to zero, and return the count `m ≤ len`. -/
def tourMoveCollectBody : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const HDR_END_OWNER))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const HDR_MARK_ARR))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))) ;;
  .assign 9 (.const 0) ;;
  .assign 10 (.const 0) ;;
  .assign 11 (.bin .add (.reg 1) (.const 1)) ;;
  .loop (.bin .lt (.reg 10) (.reg 3))
    (.assign 12 (.load (.bin .add (.reg 2) (.reg 10))) ;;
     .assign 13 (.load (.bin .add (.reg 5) (.reg 12))) ;;
     .cond (.bin .eq (.reg 13) (.reg 11))
       (.assign 13 (.load (.bin .add (.reg 6) (.reg 12))) ;;
        .cond (.bin .eq (.reg 13) (.const 0))
          (.store (.bin .add (.reg 6) (.reg 12)) (.const 1) ;;
           .assign 14 (.load (.bin .add (.reg 7) (.reg 12))) ;;
           .assign 15 (.bin .add (.reg 4) (.bin .add (.reg 9) (.reg 9))) ;;
           .store (.reg 15) (.const 0) ;;
           .store (.bin .add (.reg 15) (.const 1)) (.reg 14) ;;
           .assign 9 (.bin .add (.reg 9) (.const 1)))
          .nop)
       .nop ;;
     .assign 10 (.bin .add (.reg 10) (.const 1))) ;;
  .assign 10 (.const 0) ;;
  .loop (.bin .lt (.reg 10) (.reg 9))
    (.assign 14 (.load (.bin .add (.reg 4) (.bin .add (.bin .add (.reg 10) (.reg 10)) (.const 1)))) ;;
     .assign 12 (.load (.bin .add (.reg 8) (.reg 14))) ;;
     .store (.bin .add (.reg 6) (.reg 12)) (.const 0) ;;
     .assign 10 (.bin .add (.reg 10) (.const 1))) ;;
  .ret (.reg 9)

/-- `tourMoveRankSortNext [b, v, feV, pairsPtr, nxtPtr, m, hCur]`: compute splay ranks into
`pairsPtr[2*i]`, sort `pairsPtr[0 .. 2*m)` via `ordHeapSortBody`, compute `nxtPtr[0 .. m)` via
`ordNext`, and return updated `hCur' ≤ hCur + m`. -/
def tourMoveRankSortNextBody (rankProc sortProc ordOp2 : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const HDR_ORD_H))) ;;
  .assign 12 (.const 0) ;;
  .loop (.bin .lt (.reg 12) (.reg 5))
    (.assign 13 (.bin .add (.reg 3) (.bin .add (.reg 12) (.reg 12))) ;;
     .assign 14 (.load (.bin .add (.reg 13) (.const 1))) ;;
     .call 15 rankProc [.reg 7, .reg 14, .reg 8, .reg 6] ;;
     .store (.reg 13) (.reg 15) ;;
     .assign 12 (.bin .add (.reg 12) (.const 1))) ;;
  .call 15 sortProc [.reg 3, .reg 5] ;;
  .assign 13 (.load (.bin .add (.reg 9) (.reg 2))) ;;
  .assign 12 (.const 0) ;;
  .loop (.bin .lt (.reg 12) (.reg 5))
    (.assign 14 (.load (.bin .add (.reg 3) (.bin .add (.bin .add (.reg 12) (.reg 12)) (.const 1)))) ;;
     .assign 14 (.load (.bin .add (.reg 9) (.reg 14))) ;;
     .assign 15 (.reg 6) ;;
     .call 6 ordOp2 [.reg 11, .reg 1, .reg 14, .reg 6] ;;
     .assign 14 (.load (.reg 15)) ;;
     .cond (.bin .eq (.reg 14) (.reg 13))
       (.store (.bin .add (.reg 4) (.reg 12)) (.const 0))
       (.assign 14 (.load (.bin .add (.reg 10) (.reg 14))) ;;
        .store (.bin .add (.reg 4) (.reg 12)) (.reg 14)) ;;
     .assign 12 (.bin .add (.reg 12) (.const 1))) ;;
  .ret (.reg 6)

theorem tourMovePrep_bodies_noRand (rP sP o2 : ℕ) :
    tourMoveCollectBody.NoRand ∧ (tourMoveRankSortNextBody rP sP o2).NoRand := by
  simp [tourMoveCollectBody, tourMoveRankSortNextBody, Stmt.NoRand]

/-! ## Run theorem for `tourMoveCollectBody` -/

/-- Exact run theorem for `tourMoveCollectBody [b, sv, selPtr, len, pairsPtr]`. -/
theorem tourMoveCollectBody_runs {τ_ord : Type}
    {w vCap eCap b v selPtr len pairsPtr pos : ℕ} {p : Program} (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ} {sel : List End}
    (h : TourCoreAt vCap eCap b s x mem)
    (hvLt : v < vCap) (hsel_len : sel.length = len)
    (hsel_mem : ∀ i (hi : i < len), mem (selPtr + i) = endKey (sel[i]'(by omega)))
    (hsel_lt : ∀ z ∈ sel, z.1 < eCap)
    (hord_le : ordHandleOf b vCap eCap ≤ pairsPtr)
    (hsel_disj : selPtr + len ≤ pairsPtr ∨ pairsPtr + 2 * len ≤ selPtr)
    (hsel_no_mk : ∀ a, selPtr ≤ a → a < selPtr + len → a < b ∨ ordHandleOf b vCap eCap ≤ a)
    (hroom : pairsPtr + 2 * len + 4 < 2 ^ w) (hsel_w : selPtr + len < 2 ^ w)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w) :
    ∃ (m : ℕ) (st' : State) (c : ℕ) (A0 : List ℕ),
      Runs w p ω tourMoveCollectBody
        (startState [b, x.slotOf v, selPtr, len, pairsPtr] mem pos) (.returned m) st' c ∧
      m ≤ len ∧ A0.length = m ∧ A0.Nodup ∧
      (∀ i (hi : i < A0.length), st'.mem (pairsPtr + (2 * i + 1)) = A0[i]) ∧
      (∀ u ∈ A0, 1 ≤ u ∧ u ≤ x.numNodes ∧ endOfKey (x.keyOf u) ∈ s.ord v ∧ endOfKey (x.keyOf u) ∈ sel) ∧
      (∀ z ∈ s.ord v, z ∈ sel → x.nodeOf (endKey z) ∈ A0) ∧
      (∀ a, (a < pairsPtr ∨ pairsPtr + 2 * m ≤ a) → st'.mem a = mem a) ∧
      c ≤ 130 * len + 80 := by
  have hhdr := h.header
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hsv_lt : x.slotOf v < vCap := (h.slot_bij v hvLt).1
  have heo_iff : ∀ k < 2 * eCap, mem (endOwnerBase b vCap eCap + k) = x.slotOf v + 1 ↔ endOfKey k ∈ s.ord v := by
    intro k hk; constructor
    · intro heq; by_contra hnot
      by_cases hex : ∃ w', endOfKey k ∈ s.ord w'
      · obtain ⟨w', hw'⟩ := hex
        have hw'Lt : w' < vCap := by
          by_contra hge; have := h.valid.ordWithin.2.1 w' (Nat.le_of_not_lt hge); rw [this] at hw'; simp at hw'
        have h1 := (h.active_end w' hw'Lt (endOfKey k) hw').2
        rw [endKey_endOfKey', heq] at h1
        have hvw : v = w' := by rw [← (h.slot_bij v hvLt).2.1, (by omega : x.slotOf v = x.slotOf w'), (h.slot_bij w' hw'Lt).2.1]
        exact hnot (hvw ▸ hw')
      · push Not at hex; rw [h.inactive_owner k hk hex] at heq; omega
    · intro hm; simpa [endKey_endOfKey'] using (h.active_end v hvLt (endOfKey k) hm).2
  -- Phase 1: collection loop
  have hloop1 : ∀ (rem i m : ℕ) (A : List ℕ) (stC : State),
      i + rem = len → m ≤ i → A.length = m → A.Nodup →
      stC.regs 0 = b → stC.regs 2 = selPtr → stC.regs 3 = len → stC.regs 4 = pairsPtr →
      stC.regs 5 = endOwnerBase b vCap eCap → stC.regs 6 = markArrBase b vCap eCap →
      stC.regs 7 = nodeOfEndBase b vCap → stC.regs 8 = keyOfNodeBase b vCap eCap →
      stC.regs 9 = m → stC.regs 10 = i → stC.regs 11 = x.slotOf v + 1 →
      (∀ j (hj : j < A.length), stC.mem (pairsPtr + (2 * j + 1)) = A[j]) →
      (∀ u ∈ A, 1 ≤ u ∧ u ≤ x.numNodes ∧ endOfKey (x.keyOf u) ∈ s.ord v ∧ endOfKey (x.keyOf u) ∈ sel.take i) →
      (∀ z ∈ s.ord v, z ∈ sel.take i → x.nodeOf (endKey z) ∈ A) →
      (∀ k < 2 * eCap, stC.mem (markArrBase b vCap eCap + k) = if x.nodeOf k ∈ A ∧ endOfKey k ∈ s.ord v then 1 else 0) →
      (∀ a, (a < markArrBase b vCap eCap ∨ markArrBase b vCap eCap + 2 * eCap ≤ a) →
        (a < pairsPtr ∨ pairsPtr + 2 * m ≤ a) → stC.mem a = mem a) →
      ∃ (mF : ℕ) (AF : List ℕ) (stF : State) (cL : ℕ),
        Runs w p ω (.loop (.bin .lt (.reg 10) (.reg 3))
          (.assign 12 (.load (.bin .add (.reg 2) (.reg 10))) ;;
           .assign 13 (.load (.bin .add (.reg 5) (.reg 12))) ;;
           .cond (.bin .eq (.reg 13) (.reg 11))
             (.assign 13 (.load (.bin .add (.reg 6) (.reg 12))) ;;
              .cond (.bin .eq (.reg 13) (.const 0))
                (.store (.bin .add (.reg 6) (.reg 12)) (.const 1) ;;
                 .assign 14 (.load (.bin .add (.reg 7) (.reg 12))) ;;
                 .assign 15 (.bin .add (.reg 4) (.bin .add (.reg 9) (.reg 9))) ;;
                 .store (.reg 15) (.const 0) ;;
                 .store (.bin .add (.reg 15) (.const 1)) (.reg 14) ;;
                 .assign 9 (.bin .add (.reg 9) (.const 1)))
                .nop)
             .nop ;;
           .assign 10 (.bin .add (.reg 10) (.const 1)))) stC .normal stF cL ∧
        mF ≤ len ∧ AF.length = mF ∧ AF.Nodup ∧
        stF.regs 4 = pairsPtr ∧ stF.regs 6 = markArrBase b vCap eCap ∧
        stF.regs 8 = keyOfNodeBase b vCap eCap ∧ stF.regs 9 = mF ∧
        (∀ j (hj : j < AF.length), stF.mem (pairsPtr + (2 * j + 1)) = AF[j]) ∧
        (∀ u ∈ AF, 1 ≤ u ∧ u ≤ x.numNodes ∧ endOfKey (x.keyOf u) ∈ s.ord v ∧ endOfKey (x.keyOf u) ∈ sel) ∧
        (∀ z ∈ s.ord v, z ∈ sel → x.nodeOf (endKey z) ∈ AF) ∧
        (∀ k < 2 * eCap, stF.mem (markArrBase b vCap eCap + k) = if x.nodeOf k ∈ AF ∧ endOfKey k ∈ s.ord v then 1 else 0) ∧
        (∀ a, (a < markArrBase b vCap eCap ∨ markArrBase b vCap eCap + 2 * eCap ≤ a) →
          (a < pairsPtr ∨ pairsPtr + 2 * mF ≤ a) → stF.mem a = mem a) ∧
        cL ≤ 75 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro i m A stC hrem hmi hAlen hAnd hr0 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11
        hmP hAin hAsur hmk hfr
      have hilen : i = len := by omega
      have htake : sel.take i = sel := List.take_of_length_le (by omega)
      have hcond : (Expr.bin .lt (.reg 10) (.reg 3)).eval w stC = some 0 := by
        simp [Expr.eval, hr10, hr3, hilen, BinOp.eval, (by omega : 0 < 2 ^ w)]
      refine ⟨m, A, stC, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        by omega, hAlen, hAnd, hr4, hr6, hr8, hr9, hmP,
        fun u hu => by simpa [htake] using hAin u hu,
        fun z hz hzs => hAsur z hz (by rwa [htake]), hmk, hfr, by simp [Expr.size]⟩
    | succ rem ih =>
      intro i m A stC hrem hmi hAlen hAnd hr0 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11
        hmP hAin hAsur hmk hfr
      have hi_lt : i < len := by omega
      set z := sel[i]'(by omega)
      set k := endKey z
      have hk_lt : k < 2 * eCap := key_lt_two_mul_of_endOfKey (by simpa [k, endOfKey_endKey] using hsel_lt z (List.getElem_mem _))
      have hsel_eq : stC.mem (selPtr + i) = k := by
        rw [hfr (selPtr + i) (by have := hsel_no_mk (selPtr + i) (by omega) (by omega); simp [markArrBase, ordHandleOf, tourFixedSize] at this ⊢; rcases this with h1 | h2 <;> omega)
          (by rcases hsel_disj with h1 | h2; exact Or.inl (by omega); exact Or.inr (by omega))]
        exact hsel_mem i hi_lt
      have heo_eq : stC.mem (endOwnerBase b vCap eCap + k) = mem (endOwnerBase b vCap eCap + k) :=
        hfr _ (Or.inl (by simp [endOwnerBase, markArrBase]; omega))
          (Or.inl (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))
      have hcond : (Expr.bin .lt (.reg 10) (.reg 3)).eval w stC = some 1 := by
        simp [Expr.eval, hr10, hr3, hi_lt, BinOp.eval, (by omega : 1 < 2 ^ w)]
      set r1 := Function.update stC.regs 12 k
      set eo := mem (endOwnerBase b vCap eCap + k)
      set r2 := Function.update r1 13 eo
      have ha12 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 12) (rBase := 2) (rIdx := 10)
        (base := selPtr) (idx := i) (val := k) (st := stC) hr2 hr10 (by omega) hsel_eq
      have ha13 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 13) (rBase := 5) (rIdx := 12)
        (base := endOwnerBase b vCap eCap) (idx := k) (val := eo) (st := { stC with regs := r1 })
        (by simp [r1, hr5]) (by simp [r1])
        (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) heo_eq
      have htake_succ : sel.take (i + 1) = sel.take i ++ [z] := List.take_succ_eq_append_getElem (by omega)
      -- Split on whether `z ∈ s.ord v ∧ x.nodeOf k ∉ A`
      by_cases hzv : z ∈ s.ord v
      · have heo_v : eo = x.slotOf v + 1 := (heo_iff k hk_lt).mpr (by simpa [k, endOfKey_endKey] using hzv)
        have hcond_eo : (Expr.bin .eq (.reg 13) (.reg 11)).eval w { stC with regs := r2 } = some 1 := by
          simp [Expr.eval, r2, r1, hr11, heo_v, BinOp.eval, (by omega : 1 < 2 ^ w)]
        set mk := stC.mem (markArrBase b vCap eCap + k)
        set r3 := Function.update r2 13 mk
        have ha_mk := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 13) (rBase := 6) (rIdx := 12)
          (base := markArrBase b vCap eCap) (idx := k) (val := mk) (st := { stC with regs := r2 })
          (by simp [r2, r1, hr6]) (by simp [r2, r1])
          (by simp [markArrBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) rfl
        have hmk_val : mk = if x.nodeOf k ∈ A then 1 else 0 := by
          have := hmk k hk_lt; simpa [mk, k, endOfKey_endKey, hzv] using this
        by_cases hmemA : x.nodeOf k ∈ A
        · -- Already seen: skip!
          have hmk1 : mk = 1 := by simp [hmk_val, hmemA]
          have hcond_mk : (Expr.bin .eq (.reg 13) (.const 0)).eval w { stC with regs := r3 } = some 0 := by
            simp [Expr.eval, r3, hmk1, BinOp.eval, (by omega : 0 < 2 ^ w)]
          set r4 := Function.update r3 10 (i + 1)
          have ha10 : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1))) { stC with regs := r3 } .normal { stC with regs := r4 } 4 :=
            runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, r3, r2, r1, hr10, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : i + 1 < 2 ^ w)], rfl, rfl, rfl⟩
          obtain ⟨mF, AF, stF, cL, hrunL, hmF, hAF_l, hAF_nd, hF4, hF6, hF8, hF9, hFmP, hFAin, hFAsur, hFmk, hFfr, hcL⟩ :=
            ih (i + 1) m A { stC with regs := r4 } (by omega) (by omega) hAlen hAnd
              (by simp [r4, r3, r2, r1, hr0]) (by simp [r4, r3, r2, r1, hr2]) (by simp [r4, r3, r2, r1, hr3])
              (by simp [r4, r3, r2, r1, hr4]) (by simp [r4, r3, r2, r1, hr5]) (by simp [r4, r3, r2, r1, hr6])
              (by simp [r4, r3, r2, r1, hr7]) (by simp [r4, r3, r2, r1, hr8]) (by simp [r4, r3, r2, r1, hr9])
              (by simp [r4]) (by simp [r4, r3, r2, r1, hr11]) hmP
              (fun u hu => let ⟨a1, a2, a3, a4⟩ := hAin u hu; ⟨a1, a2, a3, by rw [htake_succ]; exact List.mem_append_left _ a4⟩)
              (fun z' hz' hz't => by
                rw [htake_succ, List.mem_append, List.mem_singleton] at hz't
                rcases hz't with h1 | rfl; exact hAsur z' hz' h1; exact hmemA) hmk hfr
          refine ⟨mF, AF, stF, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega,
            tour_runs_seq_normal ha12 (tour_runs_seq_normal ha13 (tour_runs_seq_normal
              (tour_runs_cond_true hcond_eo (by omega) (tour_runs_seq_normal ha_mk (tour_runs_cond_false hcond_mk (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)))) ha10)),
            hrunL, rfl⟩)),
            hmF, hAF_l, hAF_nd, hF4, hF6, hF8, hF9, hFmP, hFAin, hFAsur, hFmk, hFfr, ?_⟩
          clear * - hcL; simp only [Expr.size] at *; omega
        · -- New active end of `v`: mark and append `u = x.nodeOf k`!
          have hmk0 : mk = 0 := by simp [hmk_val, hmemA]
          have hcond_mk : (Expr.bin .eq (.reg 13) (.const 0)).eval w { stC with regs := r3 } = some 1 := by
            simp [Expr.eval, r3, hmk0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
          set u := x.nodeOf k
          have hu_nz : u ≠ 0 := by simpa [u, k] using (h.active_end v hvLt z hzv).1
          have hu_le : u ≤ x.numNodes := (h.nodeOf_mem k hk_lt).2
          have hu_key : x.keyOf u = k := h.nodeOf_keyOf k hk_lt hu_nz
          set m1 := Function.update stC.mem (markArrBase b vCap eCap + k) 1
          set m2 := Function.update m1 (pairsPtr + 2 * m) 0
          set m3 := Function.update m2 (pairsPtr + 2 * m + 1) u
          have hm1_ne : m1 (nodeOfEndBase b vCap + k) = u := by
            dsimp only [m1]; rw [Function.update_of_ne (by simp [nodeOfEndBase, markArrBase]; omega),
              hfr _ (Or.inl (by simp [nodeOfEndBase, markArrBase]; omega))
                (Or.inl (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))]
            exact (h.nodeOf_mem k hk_lt).1
          have hst_mk : Runs w p ω (.store (.bin .add (.reg 6) (.reg 12)) (.const 1))
              { stC with regs := r3 } .normal { stC with mem := m1, regs := r3 } 5 :=
            runs_store_iff.mpr ⟨markArrBase b vCap eCap + k, 1,
              by simp [Expr.eval, r3, r2, r1, hr6, BinOp.eval, (by simp [markArrBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : markArrBase b vCap eCap + k < 2 ^ w)],
              by simp [Expr.eval, (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
          set r4 := Function.update r3 14 u
          have ha14 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 7) (rIdx := 12)
            (base := nodeOfEndBase b vCap) (idx := k) (val := u) (st := { stC with mem := m1, regs := r3 })
            (by simp [r3, r2, r1, hr7]) (by simp [r3, r2, r1])
            (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) hm1_ne
          set r5 := Function.update r4 15 (pairsPtr + 2 * m)
          have ha15 : Runs w p ω (.assign 15 (.bin .add (.reg 4) (.bin .add (.reg 9) (.reg 9))))
              { stC with mem := m1, regs := r4 } .normal { stC with mem := m1, regs := r5 } 6 :=
            runs_assign_iff.mpr ⟨pairsPtr + 2 * m, by
              simp [Expr.eval, r4, r3, r2, r1, hr4, hr9, BinOp.eval, (by omega : m + m < 2 ^ w),
                (by omega : pairsPtr + (m + m) < 2 ^ w)]; omega, rfl, rfl, rfl⟩
          have hst_p0 : Runs w p ω (.store (.reg 15) (.const 0)) { stC with mem := m1, regs := r5 } .normal
              { stC with mem := m2, regs := r5 } 3 :=
            runs_store_iff.mpr ⟨pairsPtr + 2 * m, 0, by simp [Expr.eval, r5], by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
          have hst_p1 : Runs w p ω (.store (.bin .add (.reg 15) (.const 1)) (.reg 14))
              { stC with mem := m2, regs := r5 } .normal { stC with mem := m3, regs := r5 } 5 :=
            runs_store_iff.mpr ⟨pairsPtr + 2 * m + 1, u,
              by simp [Expr.eval, r5, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : pairsPtr + 2 * m + 1 < 2 ^ w)],
              by simp [Expr.eval, r5, r4], rfl, rfl, rfl⟩
          set r6 := Function.update r5 9 (m + 1)
          have ha9 : Runs w p ω (.assign 9 (.bin .add (.reg 9) (.const 1)))
              { stC with mem := m3, regs := r5 } .normal { stC with mem := m3, regs := r6 } 4 :=
            runs_assign_iff.mpr ⟨m + 1, by simp [Expr.eval, r5, r4, r3, r2, r1, hr9, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : m + 1 < 2 ^ w)], rfl, rfl, rfl⟩
          set r7 := Function.update r6 10 (i + 1)
          have ha10 : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1)))
              { stC with mem := m3, regs := r6 } .normal { stC with mem := m3, regs := r7 } 4 :=
            runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, r6, r5, r4, r3, r2, r1, hr10, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : i + 1 < 2 ^ w)], rfl, rfl, rfl⟩
          have hbody := tour_runs_seq_normal ha12 (tour_runs_seq_normal ha13 (tour_runs_seq_normal
            (tour_runs_cond_true (s₂ := .nop) hcond_eo (by omega) (tour_runs_seq_normal ha_mk (tour_runs_cond_true (s₂ := .nop) hcond_mk (by omega)
              (tour_runs_seq_normal hst_mk (tour_runs_seq_normal ha14 (tour_runs_seq_normal ha15
                (tour_runs_seq_normal hst_p0 (tour_runs_seq_normal hst_p1 ha9)))))))) ha10))
          have hA'_nd : (A ++ [u]).Nodup := List.nodup_append.mpr ⟨hAnd, List.nodup_singleton u, fun a ha b hb => by
            simp only [List.mem_singleton] at hb; subst hb; intro heq; exact hmemA (heq ▸ ha)⟩
          obtain ⟨mF, AF, stF, cL, hrunL, hmF, hAF_l, hAF_nd, hF4, hF6, hF8, hF9, hFmP, hFAin, hFAsur, hFmk, hFfr, hcL⟩ :=
            ih (i + 1) (m + 1) (A ++ [u]) { stC with mem := m3, regs := r7 } (by omega) (by omega)
              (by simp [hAlen]) hA'_nd
              (by simp [r7, r6, r5, r4, r3, r2, r1, hr0]) (by simp [r7, r6, r5, r4, r3, r2, r1, hr2])
              (by simp [r7, r6, r5, r4, r3, r2, r1, hr3]) (by simp [r7, r6, r5, r4, r3, r2, r1, hr4])
              (by simp [r7, r6, r5, r4, r3, r2, r1, hr5]) (by simp [r7, r6, r5, r4, r3, r2, r1, hr6])
              (by simp [r7, r6, r5, r4, r3, r2, r1, hr7]) (by simp [r7, r6, r5, r4, r3, r2, r1, hr8])
              (by simp [r7, r6]) (by simp [r7]) (by simp [r7, r6, r5, r4, r3, r2, r1, hr11])
              (fun j hj => by
                have hj' : j < m + 1 := by simpa [hAlen] using hj
                by_cases hjm : j = m
                · subst hjm; simp [m3, hAlen, u, Nat.add_assoc]
                · have hjlt : j < m := by omega
                  dsimp only [m3, m2, m1]
                  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                    Function.update_of_ne (by simp [markArrBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega),
                    hmP j (by omega), List.getElem_append_left (by omega)])
              (fun u' hu' => by
                rw [List.mem_append, List.mem_singleton] at hu'
                rcases hu' with h1 | rfl
                · let ⟨a1, a2, a3, a4⟩ := hAin u' h1
                  exact ⟨a1, a2, a3, by rw [htake_succ]; exact List.mem_append_left _ a4⟩
                · exact ⟨by omega, hu_le, by simpa [hu_key, k, endOfKey_endKey] using hzv,
                    by rw [htake_succ, hu_key]; simp [k, endOfKey_endKey]⟩)
              (fun z' hz' hz't => by
                rw [htake_succ, List.mem_append, List.mem_singleton] at hz't
                rcases hz't with h1 | rfl
                · exact List.mem_append_left _ (hAsur z' hz' h1)
                · exact List.mem_append_right _ (by simp [u, k]))
              (fun k' hk' => by
                dsimp only [m3, m2, m1]
                rw [Function.update_of_ne (by simp [markArrBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega),
                  Function.update_of_ne (by simp [markArrBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
                by_cases hkk' : k' = k
                · subst hkk'; simp [u, k, endOfKey_endKey, hzv]
                · rw [Function.update_of_ne (by omega), hmk k' hk']
                  have hne_u : x.nodeOf k' ≠ u := fun heq => by
                    have hnz' : x.nodeOf k' ≠ 0 := heq.symm ▸ hu_nz
                    exact hkk' (by rw [← h.nodeOf_keyOf k' hk' hnz', heq, hu_key])
                  simp [hne_u])
              (fun a ha1 ha2 => by
                dsimp only [m3, m2, m1]
                rw [Function.update_of_ne (by rcases ha2 with h1 | h2 <;> omega),
                  Function.update_of_ne (by rcases ha2 with h1 | h2 <;> omega),
                  Function.update_of_ne (by rcases ha1 with h1 | h2 <;> omega)]
                exact hfr a ha1 (by rcases ha2 with h1 | h2; exact Or.inl h1; exact Or.inr (by omega)))
          refine ⟨mF, AF, stF, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega, hbody, hrunL, rfl⟩)),
            hmF, hAF_l, hAF_nd, hF4, hF6, hF8, hF9, hFmP, hFAin, hFAsur, hFmk, hFfr, ?_⟩
          clear * - hcL; simp only [Expr.size] at *; omega
      · -- `z ∉ s.ord v`: `eo ≠ sv + 1`, skip!
        have heo_ne : eo ≠ x.slotOf v + 1 := fun heq => hzv (by simpa [k, endOfKey_endKey] using (heo_iff k hk_lt).mp heq)
        have hcond_eo : (Expr.bin .eq (.reg 13) (.reg 11)).eval w { stC with regs := r2 } = some 0 := by
          simp [Expr.eval, r2, r1, hr11, heo_ne, BinOp.eval, (by omega : 0 < 2 ^ w)]
        set r3 := Function.update r2 10 (i + 1)
        have ha10 : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1))) { stC with regs := r2 } .normal { stC with regs := r3 } 4 :=
          runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, r2, r1, hr10, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : i + 1 < 2 ^ w)], rfl, rfl, rfl⟩
        obtain ⟨mF, AF, stF, cL, hrunL, hmF, hAF_l, hAF_nd, hF4, hF6, hF8, hF9, hFmP, hFAin, hFAsur, hFmk, hFfr, hcL⟩ :=
          ih (i + 1) m A { stC with regs := r3 } (by omega) (by omega) hAlen hAnd
            (by simp [r3, r2, r1, hr0]) (by simp [r3, r2, r1, hr2]) (by simp [r3, r2, r1, hr3])
            (by simp [r3, r2, r1, hr4]) (by simp [r3, r2, r1, hr5]) (by simp [r3, r2, r1, hr6])
            (by simp [r3, r2, r1, hr7]) (by simp [r3, r2, r1, hr8]) (by simp [r3, r2, r1, hr9])
            (by simp [r3]) (by simp [r3, r2, r1, hr11]) hmP
            (fun u hu => let ⟨a1, a2, a3, a4⟩ := hAin u hu; ⟨a1, a2, a3, by rw [htake_succ]; exact List.mem_append_left _ a4⟩)
            (fun z' hz' hz't => by
              rw [htake_succ, List.mem_append, List.mem_singleton] at hz't
              rcases hz't with h1 | rfl; exact hAsur z' hz' h1; exact absurd hz' hzv) hmk hfr
        refine ⟨mF, AF, stF, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega,
          tour_runs_seq_normal ha12 (tour_runs_seq_normal ha13 (tour_runs_seq_normal
            (tour_runs_cond_false hcond_eo (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)) ha10)),
          hrunL, rfl⟩)),
          hmF, hAF_l, hAF_nd, hF4, hF6, hF8, hF9, hFmP, hFAin, hFAsur, hFmk, hFfr, ?_⟩
        clear * - hcL; simp only [Expr.size] at *; omega
  -- Phase 2: cleanup loop clearing `markArr` back to 0
  have hloop2 : ∀ (mF : ℕ) (AF : List ℕ) (rem j : ℕ) (stC : State),
      mF ≤ len → AF.length = mF → AF.Nodup → j + rem = mF →
      stC.regs 4 = pairsPtr → stC.regs 6 = markArrBase b vCap eCap →
      stC.regs 8 = keyOfNodeBase b vCap eCap → stC.regs 9 = mF → stC.regs 10 = j →
      (∀ q (hq : q < AF.length), stC.mem (pairsPtr + (2 * q + 1)) = AF[q]) →
      (∀ u ∈ AF, 1 ≤ u ∧ u ≤ x.numNodes ∧ endOfKey (x.keyOf u) ∈ s.ord v ∧ endOfKey (x.keyOf u) ∈ sel) →
      (∀ k < 2 * eCap, stC.mem (markArrBase b vCap eCap + k) = if x.nodeOf k ∈ AF.drop j ∧ endOfKey k ∈ s.ord v then 1 else 0) →
      (∀ a, (a < markArrBase b vCap eCap ∨ markArrBase b vCap eCap + 2 * eCap ≤ a) →
        (a < pairsPtr ∨ pairsPtr + 2 * mF ≤ a) → stC.mem a = mem a) →
      ∃ (stE : State) (c2 : ℕ),
        Runs w p ω (.loop (.bin .lt (.reg 10) (.reg 9))
          (.assign 14 (.load (.bin .add (.reg 4) (.bin .add (.bin .add (.reg 10) (.reg 10)) (.const 1)))) ;;
           .assign 12 (.load (.bin .add (.reg 8) (.reg 14))) ;;
           .store (.bin .add (.reg 6) (.reg 12)) (.const 0) ;;
           .assign 10 (.bin .add (.reg 10) (.const 1)))) stC .normal stE c2 ∧
        stE.regs 9 = mF ∧
        (∀ q (hq : q < AF.length), stE.mem (pairsPtr + (2 * q + 1)) = AF[q]) ∧
        (∀ a, (a < pairsPtr ∨ pairsPtr + 2 * mF ≤ a) → stE.mem a = mem a) ∧
        c2 ≤ 35 * rem + 10 := by
    intro mF AF rem
    induction rem with
    | zero =>
      intro j stC hmF hAFl hAFnd hrem hr4 hr6 hr8 hr9 hr10 hmP hAin hmk hfr
      have hjm : j = mF := by omega
      have hcond : (Expr.bin .lt (.reg 10) (.reg 9)).eval w stC = some 0 := by
        simp [Expr.eval, hr10, hr9, hjm, BinOp.eval, (by omega : 0 < 2 ^ w)]
      refine ⟨stC, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩), hr9, hmP,
        fun a ha => by
          by_cases hmk_r : markArrBase b vCap eCap ≤ a ∧ a < markArrBase b vCap eCap + 2 * eCap
          · have hk_lt : a - markArrBase b vCap eCap < 2 * eCap := by omega
            have ha_eq : markArrBase b vCap eCap + (a - markArrBase b vCap eCap) = a := by omega
            rw [← ha_eq, hmk _ hk_lt, hjm, ← hAFl, List.drop_length, h.markArr_zero _ hk_lt]; simp
          · exact hfr a (by omega) ha, by simp [Expr.size]⟩
    | succ rem ih =>
      intro j stC hmF hAFl hAFnd hrem hr4 hr6 hr8 hr9 hr10 hmP hAin hmk hfr
      have hj_lt : j < mF := by omega
      set u := AF[j]'(by omega)
      have hu_in := hAin u (List.getElem_mem _)
      set ku := x.keyOf u
      have hku_mem := h.keyOf_mem u hu_in.1 hu_in.2.1
      have hcond : (Expr.bin .lt (.reg 10) (.reg 9)).eval w stC = some 1 := by
        simp [Expr.eval, hr10, hr9, hj_lt, BinOp.eval, (by omega : 1 < 2 ^ w)]
      have hju_mem : stC.mem (pairsPtr + (j + j + 1)) = u := by
        have h2j : j + j = 2 * j := by omega
        rw [h2j]; exact hmP j (by omega)
      have hko_mem : stC.mem (keyOfNodeBase b vCap eCap + u) = ku := by
        have hnn := h.numNodes_le
        rw [hfr _ (Or.inl (by simp [keyOfNodeBase, markArrBase]; omega))
          (Or.inl (by simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))]
        exact hku_mem.1
      set r1 := Function.update stC.regs 14 u
      set r2 := Function.update r1 12 ku
      set mem1 := Function.update stC.mem (markArrBase b vCap eCap + ku) 0
      set r3 := Function.update r2 10 (j + 1)
      have ha14 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 4) (.bin .add (.bin .add (.reg 10) (.reg 10)) (.const 1)))))
          stC .normal { stC with regs := r1 } 9 :=
        runs_assign_iff.mpr ⟨u, by
          simp [Expr.eval, hr4, hr10, BinOp.eval, (by omega : 1 < 2 ^ w),
            (by omega : j + j < 2 ^ w), (by omega : j + j + 1 < 2 ^ w),
            (by omega : pairsPtr + (j + j + 1) < 2 ^ w), hju_mem], rfl, rfl, rfl⟩
      have ha12 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 12) (rBase := 8) (rIdx := 14)
        (base := keyOfNodeBase b vCap eCap) (idx := u) (val := ku) (st := { stC with regs := r1 })
        (by simp [r1, hr8]) (by simp [r1])
        (by have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) hko_mem
      have hst0 : Runs w p ω (.store (.bin .add (.reg 6) (.reg 12)) (.const 0))
          { stC with regs := r2 } .normal { stC with mem := mem1, regs := r2 } 5 :=
        runs_store_iff.mpr ⟨markArrBase b vCap eCap + ku, 0,
          by simp [Expr.eval, r2, r1, hr6, BinOp.eval, (by simp [markArrBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : markArrBase b vCap eCap + ku < 2 ^ w)],
          by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
      have ha10 : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1)))
          { stC with mem := mem1, regs := r2 } .normal { stC with mem := mem1, regs := r3 } 4 :=
        runs_assign_iff.mpr ⟨j + 1, by simp [Expr.eval, r2, r1, hr10, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : j + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hbody := tour_runs_seq_normal ha14 (tour_runs_seq_normal ha12 (tour_runs_seq_normal hst0 ha10))
      have hdrop_c : AF.drop j = u :: AF.drop (j + 1) := List.drop_eq_getElem_cons (by omega)
      have hu_ndrop : u ∉ AF.drop (j + 1) :=
        (List.nodup_cons.mp (hdrop_c ▸ hAFnd.sublist (List.drop_sublist j AF))).1
      obtain ⟨stE, c2, hrun2, hE9, hEmP, hEfr, hc2⟩ :=
        ih (j + 1) { stC with mem := mem1, regs := r3 } hmF hAFl hAFnd (by omega)
          (by simp [r3, r2, r1, hr4]) (by simp [r3, r2, r1, hr6]) (by simp [r3, r2, r1, hr8])
          (by simp [r3, r2, r1, hr9]) (by simp [r3])
          (fun q hq => by
            dsimp only [mem1]; rw [Function.update_of_ne (by simp [markArrBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
            exact hmP q hq) hAin
          (fun k' hk' => by
            dsimp only [mem1]
            by_cases hkk' : k' = ku
            · subst hkk'; rw [Function.update_self, hku_mem.2.2]; simp [hu_ndrop]
            · rw [Function.update_of_ne (by omega), hmk k' hk', hdrop_c]
              have hne_u : x.nodeOf k' ≠ u := fun heq => by
                have hnz' : x.nodeOf k' ≠ 0 := by omega
                exact hkk' (by rw [← h.nodeOf_keyOf k' hk' hnz', heq])
              simp [hne_u])
          (fun a ha1 ha2 => by
            dsimp only [mem1]; rw [Function.update_of_ne (by rcases ha1 with h1 | h2 <;> omega)]
            exact hfr a ha1 ha2)
      refine ⟨stE, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega, hbody, hrun2, rfl⟩)),
        hE9, hEmP, hEfr, by clear * - hc2; simp only [Expr.size] at *; omega⟩
  -- Assemble full `tourMoveCollectBody`
  set s0 : State := startState [b, x.slotOf v, selPtr, len, pairsPtr] mem pos
  set r1 := Function.update s0.regs 5 (endOwnerBase b vCap eCap)
  set r2 := Function.update r1 6 (markArrBase b vCap eCap)
  set r3 := Function.update r2 7 (nodeOfEndBase b vCap)
  set r4 := Function.update r3 8 (keyOfNodeBase b vCap eCap)
  set r5 := Function.update r4 9 0
  set r6 := Function.update r5 10 0
  set r7 := Function.update r6 11 (x.slotOf v + 1)
  have ha5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 0) (off := HDR_END_OWNER)
    (b := b) (val := endOwnerBase b vCap eCap) (st := s0) (by simp [s0, startState])
    (by simp [HDR_END_OWNER]; omega) (by simp [HDR_END_OWNER]; omega) hhdr.2.2.2.2.2.2.2.1
  have ha6 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_MARK_ARR)
    (b := b) (val := markArrBase b vCap eCap) (st := ⟨mem, r1, pos⟩) (by simp [r1, s0, startState])
    (by simp [HDR_MARK_ARR]; omega) (by simp [HDR_MARK_ARR]; omega) hhdr.2.2.2.2.2.2.2.2.2.1
  have ha7 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 0) (off := HDR_NODE_OF_END)
    (b := b) (val := nodeOfEndBase b vCap) (st := ⟨mem, r2, pos⟩) (by simp [r2, r1, s0, startState])
    (by simp [HDR_NODE_OF_END]; omega) (by simp [HDR_NODE_OF_END]; omega) hhdr.2.2.2.2.2.2.1
  have ha8 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 0) (off := HDR_KEY_OF_NODE)
    (b := b) (val := keyOfNodeBase b vCap eCap) (st := ⟨mem, r3, pos⟩) (by simp [r3, r2, r1, s0, startState])
    (by simp [HDR_KEY_OF_NODE]; omega) (by simp [HDR_KEY_OF_NODE]; omega) hhdr.2.2.2.2.2.2.2.2.1
  have ha9 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 9) (val := 0) (st := ⟨mem, r4, pos⟩) (by omega)
  have ha10 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 10) (val := 0) (st := ⟨mem, r5, pos⟩) (by omega)
  have ha11 : Runs w p ω (.assign 11 (.bin .add (.reg 1) (.const 1))) ⟨mem, r6, pos⟩ .normal ⟨mem, r7, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨x.slotOf v + 1, by simp [Expr.eval, r6, r5, r4, r3, r2, r1, s0, startState, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : x.slotOf v + 1 < 2 ^ w)], rfl, rfl, rfl⟩
  obtain ⟨mF, AF, stF, c1, hrun1, hmF, hAFl, hAFnd, hF4, hF6, hF8, hF9, hFmP, hFAin, hFAsur, hFmk, hFfr, hc1⟩ :=
    hloop1 len 0 0 [] ⟨mem, r7, pos⟩ (by omega) (le_refl 0) rfl List.nodup_nil
      (by simp [r7, r6, r5, r4, r3, r2, r1, s0, startState]) (by simp [r7, r6, r5, r4, r3, r2, r1, s0, startState])
      (by simp [r7, r6, r5, r4, r3, r2, r1, s0, startState]) (by simp [r7, r6, r5, r4, r3, r2, r1, s0, startState])
      (by simp [r7, r6, r5, r4, r3, r2, r1]) (by simp [r7, r6, r5, r4, r3, r2])
      (by simp [r7, r6, r5, r4, r3]) (by simp [r7, r6, r5, r4])
      (by simp [r7, r6, r5]) (by simp [r7, r6]) (by simp [r7])
      (fun j hj => by simp at hj) (fun _ hu => by simp at hu) (fun _ _ hz => by simp at hz)
      (fun k hk => by simp [h.markArr_zero k hk]) (fun _ _ _ => rfl)
  set rReset := Function.update stF.regs 10 0
  have haReset := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 10) (val := 0) (st := stF) (by omega)
  obtain ⟨stE, c2, hrun2, hE9, hEmP, hEfr, hc2⟩ :=
    hloop2 mF AF mF 0 { stF with regs := rReset } hmF hAFl hAFnd (by omega)
      (by simp [rReset, hF4]) (by simp [rReset, hF6]) (by simp [rReset, hF8])
      (by simp [rReset, hF9]) (by simp [rReset]) hFmP hFAin (by simpa using hFmk) hFfr
  have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := stE) (r := 9) (v := mF) hE9
  refine ⟨mF, stE, _, AF,
    tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal ha7 (tour_runs_seq_normal ha8
      (tour_runs_seq_normal ha9 (tour_runs_seq_normal ha10 (tour_runs_seq_normal ha11
        (tour_runs_seq_normal hrun1 (tour_runs_seq_normal haReset (tour_runs_seq_normal hrun2 hret))))))))),
    hmF, hAFl, hAFnd, hEmP, hFAin, hFAsur, hEfr, by clear * - hc1 hc2 hmF; omega⟩

end MinCostFlow.SparseCore.Program
