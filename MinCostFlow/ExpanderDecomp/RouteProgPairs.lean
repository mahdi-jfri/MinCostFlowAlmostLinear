module

public import MinCostFlow.ExpanderDecomp.RouteProgPairsBase

import Mathlib.Tactic.Linarith

/-!
# Local Terminal-Pairs Builder: Stage 1 and Contract Proof

Verifies Stage 1 (`pairsScan_triple`) and assembles `buildLocalPairs_meetsContract` for
`buildLocalPairsProc`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Stage 1 Verification (`pairsScanStmt`) -/

lemma pairsScan_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)} {n : ℕ}
    {pAddr locIdAddr workAddr : ℕ} {st0 : State}
    (hX : X ⊆ Finset.range n)
    (hpairs : PairsAt st0.mem pAddr pairs)
    (hbnd : PairsBounded st0.mem pAddr pairs workAddr)
    (htp : RouteTerminalPairs X pairs)
    (hloc_lt : locIdAddr + n ≤ workAddr)
    (hloc : ∀ u < n, st0.mem (locIdAddr + u) = if u ∈ X then locOf X u + 1 else 0)
    (hzero : ZeroFrom st0.mem workAddr)
    (hw : workAddr + localPairsSpace X.card pairs.length + 4 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hregs0 : ∀ r ≤ 10, st0.regs r =
      match r with
      | 0 => pAddr | 1 => X.card | 2 => locIdAddr | 3 => workAddr | 4 => pairs.length
      | 5 => pairsBAddr workAddr
      | 6 => pairsAOffAddr workAddr X.card
      | 7 => pairsALenAddr workAddr X.card pairs.length
      | 8 => pairsADataAddr workAddr X.card pairs.length
      | 9 => pairsATagAddr workAddr X.card pairs.length
      | _ => pairsAWCurAddr workAddr X.card pairs.length) :
    Triple w p (fun st => st = st0) pairsScanStmt
      (normalPost fun st' =>
        (∀ r ≤ 10, st'.regs r = st0.regs r) ∧
        st'.regs 11 = totalDemand pairs ∧
        (∀ i ≤ pairs.length, st'.mem (pairsAOffAddr workAddr X.card + i) = pairAOff pairs i) ∧
        (∀ i < pairs.length, st'.mem (pairsAWCurAddr workAddr X.card pairs.length + i) =
          pairAOff pairs i) ∧
        (∀ i (hi : i < pairs.length),
          st'.mem (pairsALenAddr workAddr X.card pairs.length + i) = (pairs[i]'hi).1.card) ∧
        (∀ v < X.card,
          st'.mem (pairsATagAddr workAddr X.card pairs.length + v) ≤ pairs.length ∧
          ∀ i (hi : i < pairs.length),
            st'.mem (pairsATagAddr workAddr X.card pairs.length + v) = i + 1 ↔
              origOf X v ∈ (pairs[i]'hi).1) ∧
        LocalBPairsAt st'.mem (pairsBAddr workAddr) X pairs ∧
        (∀ a < workAddr, st'.mem a = st0.mem a) ∧
        ZeroFrom st'.mem (workAddr + localPairsSpace X.card pairs.length))
      (fun _ => 110 * pairs.length + 80 * X.card + 35) := by
  set k := pairs.length
  set nX := X.card
  set pairBAddr := pairsBAddr workAddr
  set aOffAddr := pairsAOffAddr workAddr nX
  set aLenAddr := pairsALenAddr workAddr nX k
  set aDataAddr := pairsADataAddr workAddr nX k
  set aTagAddr := pairsATagAddr workAddr nX k
  set aWCurAddr := pairsAWCurAddr workAddr nX k
  have hsp : localPairsSpace nX k = 3 * nX + 3 * k + 1 := rfl
  have htd_le : totalDemand pairs ≤ nX := routeTerminalPairs_totalDemand_le htp
  have hsum_le : pairRemSize pairs 0 ≤ nX := by
    rw [pairRemSize_zero]; exact routeTerminalPairs_sum_card_le htp
  let I : State → Prop := fun st =>
    (∀ r ≤ 10, st.regs r = st0.regs r) ∧
    st.regs 12 ≤ pairs.length ∧
    st.regs 11 = pairAOff pairs (st.regs 12) ∧
    (∀ t < st.regs 12, st.mem (aOffAddr + t) = pairAOff pairs t) ∧
    (∀ t < st.regs 12, st.mem (aWCurAddr + t) = pairAOff pairs t) ∧
    (∀ t (ht : t < pairs.length), t < st.regs 12 → st.mem (aLenAddr + t) = (pairs[t]'ht).1.card) ∧
    (∀ v < nX,
      st.mem (aTagAddr + v) ≤ st.regs 12 ∧
      ∀ t (ht : t < pairs.length), t < st.regs 12 →
        (st.mem (aTagAddr + v) = t + 1 ↔ origOf X v ∈ (pairs[t]'ht).1)) ∧
    (∀ v < nX,
      st.mem (pairBAddr + v) ≤ st.regs 12 ∧
      ∀ t (ht : t < pairs.length), t < st.regs 12 →
        (st.mem (pairBAddr + v) = t + 1 ↔ origOf X v ∈ (pairs[t]'ht).2)) ∧
    (∀ a < workAddr, st.mem a = st0.mem a) ∧
    ZeroFrom st.mem (workAddr + localPairsSpace nX k)
  let loopBody : Stmt := seqStmts
    [ .store (.bin .add (.reg 6) (.reg 12)) (.reg 11)
    , .store (.bin .add (.reg 10) (.reg 12)) (.reg 11)
    , .assign 13 (.load (.bin .add (.bin .add (.reg 0) (.const 1))
        (.bin .mul (.const 2) (.reg 12))))
    , .assign 14 (.load (.reg 13))
    , .store (.bin .add (.reg 7) (.reg 12)) (.reg 14)
    , .assign 11 (.bin .add (.reg 11) (.reg 14))
    , .assign 15 (.const 0)
    , .loop (.bin .lt (.reg 15) (.reg 14))
        (seqStmts
          [ .assign 16 (.load (.bin .add (.bin .add (.reg 13) (.const 1)) (.reg 15)))
          , .assign 17 (.bin .sub (.load (.bin .add (.reg 2) (.reg 16))) (.const 1))
          , .store (.bin .add (.reg 9) (.reg 17)) (.bin .add (.reg 12) (.const 1))
          , .assign 15 (.bin .add (.reg 15) (.const 1)) ])
    , .assign 13 (.load (.bin .add (.bin .add (.reg 0) (.const 2))
        (.bin .mul (.const 2) (.reg 12))))
    , .assign 14 (.load (.reg 13))
    , .assign 15 (.const 0)
    , .loop (.bin .lt (.reg 15) (.reg 14))
        (seqStmts
          [ .assign 16 (.load (.bin .add (.bin .add (.reg 13) (.const 1)) (.reg 15)))
          , .assign 17 (.bin .sub (.load (.bin .add (.reg 2) (.reg 16))) (.const 1))
          , .store (.bin .add (.reg 5) (.reg 17)) (.bin .add (.reg 12) (.const 1))
          , .assign 15 (.bin .add (.reg 15) (.const 1)) ])
    , .assign 12 (.bin .add (.reg 12) (.const 1)) ]
  have hloop :
      Triple w p I (.loop (.bin .lt (.reg 12) (.reg 4)) loopBody)
        (normalPost fun st' =>
          (∀ r ≤ 10, st'.regs r = st0.regs r) ∧
          st'.regs 11 = totalDemand pairs ∧
          (∀ t < k, st'.mem (aOffAddr + t) = pairAOff pairs t) ∧
          (∀ t < k, st'.mem (aWCurAddr + t) = pairAOff pairs t) ∧
          (∀ t (ht : t < k), st'.mem (aLenAddr + t) = (pairs[t]'ht).1.card) ∧
          (∀ v < nX,
            st'.mem (aTagAddr + v) ≤ k ∧
            ∀ t (ht : t < k), st'.mem (aTagAddr + v) = t + 1 ↔ origOf X v ∈ (pairs[t]'ht).1) ∧
          LocalBPairsAt st'.mem pairBAddr X pairs ∧
          (∀ a < workAddr, st'.mem a = st0.mem a) ∧
          ZeroFrom st'.mem (workAddr + localPairsSpace nX k))
        (fun st => 105 * (k - st.regs 12) + 80 * pairRemSize pairs (st.regs 12) + 10) := by
    refine Triple.loop_measure
      (m := fun st => k - st.regs 12)
      (rem := fun st => 105 * (k - st.regs 12) + 80 * pairRemSize pairs (st.regs 12) + 10)
      (condVal := fun st => if st.regs 12 < k then 1 else 0)
      ?_ ?_ ?_
    · intro stL ⟨hregs, _, _, _, _, _, _, _, _, _⟩
      have hr4 : stL.regs 4 = k := (hregs 4 (by decide)).trans (hregs0 4 (by decide))
      eval_expr
    · intro stL ⟨hregs, hi_le, hacc, hoff, hwcur, hlen, htag, hpb, hlow, hzf⟩ hv
      have hi_eq : stL.regs 12 = k := by split_ifs at hv; omega
      rw [hi_eq, pairAOff_length] at hacc
      rw [hi_eq] at hoff hwcur hlen htag hpb
      exact ⟨⟨hregs, hacc, hoff, hwcur,
        fun t ht => hlen t ht ht,
        fun v hv => ⟨(htag v hv).1, fun t ht => (htag v hv).2 t ht ht⟩,
        fun v hv => ⟨(hpb v hv).1, fun t ht => (hpb v hv).2 t ht ht⟩,
        hlow, hzf⟩, by simp [Expr.size]⟩
    · intro stL ⟨hregs, hi_le, hacc, hoff, hwcur, hlen, htag, hpb, hlow, hzf⟩ hv
      have hr : ∀ r ≤ 10, stL.regs r = _ := fun r hr => (hregs r hr).trans (hregs0 r hr)
      have hr0 : stL.regs 0 = pAddr := hr 0 (by decide)
      have hr1 : stL.regs 1 = nX := hr 1 (by decide)
      have hr2 : stL.regs 2 = locIdAddr := hr 2 (by decide)
      have hr4 : stL.regs 4 = k := hr 4 (by decide)
      have hr5 : stL.regs 5 = pairBAddr := hr 5 (by decide)
      have hr6 : stL.regs 6 = aOffAddr := hr 6 (by decide)
      have hr7 : stL.regs 7 = aLenAddr := hr 7 (by decide)
      have hr9 : stL.regs 9 = aTagAddr := hr 9 (by decide)
      have hr10 : stL.regs 10 = aWCurAddr := hr 10 (by decide)
      have hi_lt : stL.regs 12 < k := by split_ifs at hv <;> omega
      set i := stL.regs 12
      set A := (pairs[i]'hi_lt).1
      set B := (pairs[i]'hi_lt).2
      have hAB_tp := htp.1 _ (List.getElem_mem hi_lt)
      have hA_sub : A ⊆ X := hAB_tp.1
      have hB_sub : B ⊆ X := hAB_tp.2.1
      have hA_le : A.card ≤ nX := Finset.card_le_card hA_sub
      have hB_le : B.card ≤ nX := Finset.card_le_card hB_sub
      have hacc_le : pairAOff pairs i ≤ nX := le_trans (pairAOff_le_totalDemand pairs i) htd_le
      have hacc_succ : pairAOff pairs i + A.card = pairAOff pairs (i + 1) :=
        (pairAOff_succ pairs hi_lt).symm
      have hacc1_le : pairAOff pairs (i + 1) ≤ nX :=
        le_trans (pairAOff_le_totalDemand pairs (i + 1)) htd_le
      set aPtr := st0.mem (pAddr + 1 + 2 * i)
      set bPtr := st0.mem (pAddr + 2 + 2 * i)
      have haPtr_bnd : aPtr + 1 + A.card ≤ workAddr := (hbnd.2 i hi_lt).1
      have hbPtr_bnd : bPtr + 1 + B.card ≤ workAddr := (hbnd.2 i hi_lt).2
      have hp_a_lt : pAddr + 1 + 2 * i < workAddr := by have := hbnd.1; omega
      have hp_b_lt : pAddr + 2 + 2 * i < workAddr := by have := hbnd.1; omega
      have hA_vs : VertSetAt st0.mem aPtr A := (hpairs.2 i hi_lt).1
      have hB_vs : VertSetAt st0.mem bPtr B := (hpairs.2 i hi_lt).2
      have hA_len_mem : st0.mem aPtr = A.card := by
        rcases hA_vs with ⟨xs, hnd, hfin, hseq⟩
        rw [hseq.1, ← hfin, List.toFinset_card_of_nodup hnd]
      have hB_len_mem : st0.mem bPtr = B.card := by
        rcases hB_vs with ⟨xs, hnd, hfin, hseq⟩
        rw [hseq.1, ← hfin, List.toFinset_card_of_nodup hnd]
      refine ⟨100 + 35 * A.card + 35 * B.card, ?_⟩
      wram_enter
      subst st
      dsimp only [loopBody, seqStmts]
      refine runs_seq_store_le (x := aOffAddr + i) (v := pairAOff pairs i)
        (by dsimp only [aOffAddr, pairsAOffAddr]; eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := aWCurAddr + i) (v := pairAOff pairs i)
        (by dsimp only [aWCurAddr, pairsAWCurAddr]; eval_expr) (by eval_expr) ?_
      have hmem_aPtr :
          (Function.update (Function.update stL.mem (aOffAddr + i) (pairAOff pairs i))
            (aWCurAddr + i) (pairAOff pairs i)) (pAddr + 1 + 2 * i) = aPtr := by
        rw [Function.update_of_ne (by dsimp only [aWCurAddr, pairsAWCurAddr]; omega),
          Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr]; omega),
          hlow _ hp_a_lt]
      refine runs_seq_assign_le (v := aPtr) (by rw [← hmem_aPtr]; eval_expr) ?_
      have hmem_lenA :
          (Function.update (Function.update stL.mem (aOffAddr + i) (pairAOff pairs i))
            (aWCurAddr + i) (pairAOff pairs i)) aPtr = A.card := by
        rw [Function.update_of_ne (by dsimp only [aWCurAddr, pairsAWCurAddr]; omega),
          Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr]; omega),
          hlow _ (by omega), hA_len_mem]
      refine runs_seq_assign_le (v := A.card) (by rw [← hmem_lenA]; eval_expr) ?_
      refine runs_seq_store_le (x := aLenAddr + i) (v := A.card)
        (by dsimp only [aLenAddr, pairsALenAddr]; eval_expr) (by eval_expr) ?_
      refine runs_seq_assign_le (v := pairAOff pairs (i + 1))
        (by rw [← hacc_succ]; eval_expr) ?_
      refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
      set memA := Function.update
        (Function.update (Function.update stL.mem (aOffAddr + i) (pairAOff pairs i))
          (aWCurAddr + i) (pairAOff pairs i))
        (aLenAddr + i) A.card
      have hmemA_low : ∀ a < workAddr, memA a = st0.mem a := by
        intro a ha
        simp only [memA]
        rw [Function.update_of_ne (by dsimp only [aLenAddr, pairsALenAddr]; omega),
          Function.update_of_ne (by dsimp only [aWCurAddr, pairsAWCurAddr]; omega),
          Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr]; omega),
          hlow a ha]
      have hA_vs' : VertSetAt memA aPtr A := by
        rcases hA_vs with ⟨xs, hnd, hfin, hseq⟩
        have hlen_xs : xs.length = A.card := by rw [← hfin, List.toFinset_card_of_nodup hnd]
        exact ⟨xs, hnd, hfin, seqAt_of_agree_below hseq (by omega) hmemA_low⟩
      have hlocA : ∀ u < n, memA (locIdAddr + u) = if u ∈ X then locOf X u + 1 else 0 := by
        intro u hu; rw [hmemA_low _ (by omega), hloc u hu]
      refine runs_seq_triple_le
        (markSetLoop_triple (arrAddr := aTagAddr) (rArr := 9) (tag := i + 1) (workAddr := workAddr)
          hA_sub hX hA_vs' haPtr_bnd hloc_lt (by dsimp only [aTagAddr, pairsATagAddr]; omega)
          hlocA (by omega) (by dsimp only [aTagAddr, pairsATagAddr]; omega) hw4
          (by simp [hr2]) (by simp [hr9]) (by simp [i])
          (by simp) (by simp) (by simp) (by omega) rfl)
        rfl (fun stA hstA => ?_)
      rcases hstA with ⟨hregsA, htagA, hframeA⟩
      have hregsA_low : ∀ r ≤ 10, stA.regs r = st0.regs r := by
        intro r hr_le
        rw [hregsA r (by omega)]
        simp only [Function.update_of_ne (by omega : r ≠ 15),
          Function.update_of_ne (by omega : r ≠ 11),
          Function.update_of_ne (by omega : r ≠ 14),
          Function.update_of_ne (by omega : r ≠ 13)]
        exact hregs r hr_le
      have hregsA_11 : stA.regs 11 = pairAOff pairs (i + 1) := by
        rw [hregsA 11 (by decide)]; simp
      have hregsA_12 : stA.regs 12 = i := by
        rw [hregsA 12 (by decide)]; simp [i]
      have hstA_low : ∀ a < workAddr, stA.mem a = st0.mem a := by
        intro a ha
        rw [hframeA a (Or.inl (by dsimp only [aTagAddr, pairsATagAddr]; omega)), hmemA_low a ha]
      have hmem_bPtr : stA.mem (pAddr + 2 + 2 * i) = bPtr := hstA_low _ hp_b_lt
      have hrA0 : stA.regs 0 = pAddr := (hregsA_low 0 (by decide)).trans (hregs0 0 (by decide))
      have hrA2 : stA.regs 2 = locIdAddr := (hregsA_low 2 (by decide)).trans (hregs0 2 (by decide))
      have hrA5 : stA.regs 5 = pairBAddr := (hregsA_low 5 (by decide)).trans (hregs0 5 (by decide))
      refine runs_seq_assign_le (v := bPtr) (by rw [← hmem_bPtr]; eval_expr) ?_
      have hmem_lenB : stA.mem bPtr = B.card := by
        rw [hstA_low _ (by omega), hB_len_mem]
      refine runs_seq_assign_le (v := B.card) (by rw [← hmem_lenB]; eval_expr) ?_
      refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
      have hB_vs' : VertSetAt stA.mem bPtr B := by
        rcases hB_vs with ⟨xs, hnd, hfin, hseq⟩
        have hlen_xs : xs.length = B.card := by rw [← hfin, List.toFinset_card_of_nodup hnd]
        exact ⟨xs, hnd, hfin, seqAt_of_agree_below hseq (by omega) hstA_low⟩
      have hlocB : ∀ u < n, stA.mem (locIdAddr + u) = if u ∈ X then locOf X u + 1 else 0 := by
        intro u hu; rw [hstA_low _ (by omega), hloc u hu]
      refine runs_seq_triple_le
        (markSetLoop_triple (arrAddr := pairBAddr) (rArr := 5) (tag := i + 1) (workAddr := workAddr)
          (st0 := { stA with regs := Function.update (Function.update (Function.update stA.regs 13 bPtr) 14 B.card) 15 0 })
          hB_sub hX hB_vs' hbPtr_bnd hloc_lt (by dsimp only [pairBAddr, pairsBAddr]; omega)
          hlocB (by omega) (by dsimp only [pairBAddr, pairsBAddr]; omega) hw4
          (by simp [hrA2]) (by simp [hrA5]) (by simp [hregsA_12])
          (by simp) (by simp) (by simp) (by omega) rfl)
        rfl (fun stB hstB => ?_)
      rcases hstB with ⟨hregsB, hpbB, hframeB⟩
      have hregsB_low : ∀ r ≤ 10, stB.regs r = st0.regs r := by
        intro r hr_le
        rw [hregsB r (by omega)]
        simp only [Function.update_of_ne (by omega : r ≠ 15),
          Function.update_of_ne (by omega : r ≠ 14),
          Function.update_of_ne (by omega : r ≠ 13)]
        exact hregsA_low r hr_le
      have hregsB_11 : stB.regs 11 = pairAOff pairs (i + 1) := by
        rw [hregsB 11 (by decide)]; simp [hregsA_11]
      have hregsB_12 : stB.regs 12 = i := by
        rw [hregsB 12 (by decide)]; simp [hregsA_12]
      refine runs_assign_le (v := i + 1) (by eval_expr) ?_ ?_
      · refine ⟨⟨?_, by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp; omega, ?_⟩
        · intro r hr_le
          dsimp only
          rw [Function.update_of_ne (by omega)]; exact hregsB_low r hr_le
        · simp [hregsB_11]
        · intro t ht
          simp only [Function.update_self] at ht
          rw [hframeB _ (Or.inr (by dsimp only [pairBAddr, pairsBAddr, aOffAddr, pairsAOffAddr]; omega)),
            hframeA _ (Or.inl (by dsimp only [aOffAddr, pairsAOffAddr, aTagAddr, pairsATagAddr]; omega))]
          simp only [memA]
          rw [Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr, aLenAddr, pairsALenAddr]; omega),
            Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr, aWCurAddr, pairsAWCurAddr]; omega)]
          by_cases hti : t = i
          · subst hti; rw [Function.update_self]
          · rw [Function.update_of_ne (by omega)]; exact hoff t (by omega)
        · intro t ht
          simp only [Function.update_self] at ht
          rw [hframeB _ (Or.inr (by dsimp only [pairBAddr, pairsBAddr, aWCurAddr, pairsAWCurAddr]; omega)),
            hframeA _ (Or.inr (by dsimp only [aTagAddr, pairsATagAddr, aWCurAddr, pairsAWCurAddr]; omega))]
          simp only [memA]
          rw [Function.update_of_ne (by dsimp only [aLenAddr, pairsALenAddr, aWCurAddr, pairsAWCurAddr]; omega)]
          by_cases hti : t = i
          · subst hti; rw [Function.update_self]
          · rw [Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr, aWCurAddr, pairsAWCurAddr]; omega)]
            exact hwcur t (by omega)
        · intro t ht ht_lt
          simp only [Function.update_self] at ht_lt
          rw [hframeB _ (Or.inr (by dsimp only [pairBAddr, pairsBAddr, aLenAddr, pairsALenAddr]; omega)),
            hframeA _ (Or.inl (by dsimp only [aLenAddr, pairsALenAddr, aTagAddr, pairsATagAddr]; omega))]
          simp only [memA]
          by_cases hti : t = i
          · subst hti; rw [Function.update_self]
          · rw [Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp only [aLenAddr, pairsALenAddr, aWCurAddr, pairsAWCurAddr]; omega),
              Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr, aLenAddr, pairsALenAddr]; omega)]
            exact hlen t ht (by omega)
        · intro v hv
          simp only [Function.update_self]
          rw [hframeB _ (Or.inr (by dsimp only [pairBAddr, pairsBAddr, aTagAddr, pairsATagAddr]; omega)),
            htagA v hv]
          have hmemA_tag : memA (aTagAddr + v) = stL.mem (aTagAddr + v) := by
            simp only [memA]
            rw [Function.update_of_ne (by dsimp only [aLenAddr, pairsALenAddr, aTagAddr, pairsATagAddr]; omega),
              Function.update_of_ne (by dsimp only [aWCurAddr, pairsAWCurAddr, aTagAddr, pairsATagAddr]; omega),
              Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr, aTagAddr, pairsATagAddr]; omega)]
          rw [hmemA_tag]
          by_cases hvA : origOf X v ∈ A
          · simp only [hvA, ↓reduceIte]
            refine ⟨le_rfl, fun t ht ht_lt => ?_⟩
            by_cases hti : t = i
            · subst hti; exact iff_of_true rfl hvA
            · have hdisj := routeTerminalPairs_disj_fst htp hi_lt ht (Ne.symm hti)
              have hnot : origOf X v ∉ (pairs[t]'ht).1 :=
                Finset.disjoint_left.mp hdisj hvA
              exact iff_of_false (by omega) hnot
          · simp only [hvA, ↓reduceIte]
            refine ⟨Nat.le_succ_of_le (htag v hv).1, fun t ht ht_lt => ?_⟩
            by_cases hti : t = i
            · subst hti
              have hle_i := (htag v hv).1
              exact ⟨fun h => by omega, fun h => absurd h hvA⟩
            · exact (htag v hv).2 t ht (by omega)
        · intro v hv
          simp only [Function.update_self]
          rw [hpbB v hv]
          have hstA_pb : stA.mem (pairBAddr + v) = stL.mem (pairBAddr + v) := by
            rw [hframeA _ (Or.inl (by dsimp only [pairBAddr, pairsBAddr, aTagAddr, pairsATagAddr]; omega))]
            simp only [memA]
            rw [Function.update_of_ne (by dsimp only [pairBAddr, pairsBAddr, aLenAddr, pairsALenAddr]; omega),
              Function.update_of_ne (by dsimp only [pairBAddr, pairsBAddr, aWCurAddr, pairsAWCurAddr]; omega),
              Function.update_of_ne (by dsimp only [pairBAddr, pairsBAddr, aOffAddr, pairsAOffAddr]; omega)]
          rw [hstA_pb]
          by_cases hvB : origOf X v ∈ B
          · simp only [hvB, ↓reduceIte]
            refine ⟨le_rfl, fun t ht ht_lt => ?_⟩
            by_cases hti : t = i
            · subst hti; exact iff_of_true rfl hvB
            · have hdisj := routeTerminalPairs_disj_snd htp hi_lt ht (Ne.symm hti)
              have hnot : origOf X v ∉ (pairs[t]'ht).2 :=
                Finset.disjoint_left.mp hdisj hvB
              exact iff_of_false (by omega) hnot
          · simp only [hvB, ↓reduceIte]
            refine ⟨Nat.le_succ_of_le (hpb v hv).1, fun t ht ht_lt => ?_⟩
            by_cases hti : t = i
            · subst hti
              have hle_i := (hpb v hv).1
              exact ⟨fun h => by omega, fun h => absurd h hvB⟩
            · exact (hpb v hv).2 t ht (by omega)
        · intro a ha
          rw [hframeB a (Or.inl (by dsimp only [pairBAddr, pairsBAddr]; omega))]
          exact hstA_low a ha
        · intro a ha
          have ha' : workAddr + 3 * nX + 3 * k + 1 ≤ a := by
            dsimp only [localPairsSpace] at ha; omega
          rw [hframeB a (Or.inr (by dsimp only [pairBAddr, pairsBAddr]; omega)),
            hframeA a (Or.inr (by dsimp only [aTagAddr, pairsATagAddr]; omega))]
          simp only [memA]
          rw [Function.update_of_ne (by dsimp only [aLenAddr, pairsALenAddr]; omega),
            Function.update_of_ne (by dsimp only [aWCurAddr, pairsAWCurAddr]; omega),
            Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr]; omega)]
          exact hzf a ha
        · have hrem := pairRemSize_eq_succ pairs hi_lt
          have hsz : (Expr.bin .lt (.reg 12) (.reg 4)).size = 3 := rfl
          simp only [Function.update_self, hsz]
          dsimp only [A, B] at hrem ⊢
          omega
      · wram_cost
  wram_enter
  subst st
  unfold pairsScanStmt
  dsimp only [seqStmts]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  set stInit : State :=
    { st0 with regs := Function.update (Function.update st0.regs 11 0) 12 0 }
  have hinit : I stInit := by
    refine ⟨?_, by simp [stInit], by simp [stInit, pairAOff_zero],
      fun t ht => by simp [stInit] at ht,
      fun t ht => by simp [stInit] at ht,
      fun t _ ht => by simp [stInit] at ht,
      ?_, ?_, fun _ _ => rfl, fun a ha => hzero a (by omega)⟩
    · intro r hr; simp [stInit, Function.update_of_ne (by omega : r ≠ 12),
        Function.update_of_ne (by omega : r ≠ 11)]
    · intro v _
      refine ⟨by rw [show stInit.mem _ = 0 from hzero _ (by dsimp only [aTagAddr, pairsATagAddr]; omega)]; omega,
        fun t _ ht => by simp [stInit] at ht⟩
    · intro v _
      refine ⟨by rw [show stInit.mem _ = 0 from hzero _ (by dsimp only [pairBAddr, pairsBAddr]; omega)]; omega,
        fun t _ ht => by simp [stInit] at ht⟩
  refine runs_seq_triple_le hloop hinit (fun st1 hst1 => ?_)
  rcases hst1 with ⟨hr1, h11, hoff1, hwcur1, hlen1, htag1, hpb1, hlow1, hzf1⟩
  have hr1_6 : st1.regs 6 = aOffAddr := (hr1 6 (by decide)).trans (hregs0 6 (by decide))
  have hr1_4 : st1.regs 4 = k := (hr1 4 (by decide)).trans (hregs0 4 (by decide))
  refine runs_store_le (x := aOffAddr + k) (v := totalDemand pairs)
    (by dsimp only [aOffAddr, pairsAOffAddr]; eval_expr) (by eval_expr) ?_ ?_
  · dsimp only [normalPost]
    refine ⟨hr1, h11, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      by_cases hik : i = k
      · subst hik; rw [Function.update_self, pairAOff_length]
      · rw [Function.update_of_ne (by omega)]; exact hoff1 i (by omega)
    · intro i hi
      rw [Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr, aWCurAddr, pairsAWCurAddr]; omega)]
      exact hwcur1 i hi
    · intro i hi
      rw [Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr, aLenAddr, pairsALenAddr]; omega)]
      exact hlen1 i hi
    · intro v hv
      rw [Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr, aTagAddr, pairsATagAddr]; omega)]
      exact htag1 v hv
    · intro v hv
      rw [Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr, pairBAddr, pairsBAddr]; omega)]
      exact hpb1 v hv
    · intro a ha
      rw [Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr]; omega)]
      exact hlow1 a ha
    · intro a ha
      have ha' : workAddr + 3 * nX + 3 * k + 1 ≤ a := by
        dsimp only [localPairsSpace] at ha; omega
      rw [Function.update_of_ne (by dsimp only [aOffAddr, pairsAOffAddr]; omega)]
      exact hzf1 a ha
  · simp only [stInit, Function.update_self, Nat.sub_zero, Expr.size]
    omega

/-! ## 2. Full `buildLocalPairsProc` Contract Proof -/

theorem buildLocalPairs_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [buildLocalPairsProc]) :
    MeetsContract w p b (buildLocalPairsContract w) := by
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨hlen, X, pairs, hnX, hX, hpairs, hbnd, htp, hloc_lt, hloc, hzero, hw, hw4⟩
  rcases args with _ | ⟨pAddr, _ | ⟨nX, _ | ⟨locIdAddr, _ | ⟨workAddr, _ | ⟨n, _ | _⟩⟩⟩⟩⟩ <;>
    simp at hlen
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hnX hX hpairs hbnd hloc_lt hloc hzero hw
  subst hnX
  have hproc : p.procs[b]? = some buildLocalPairsProc := by
    have := hp 0 (by simp)
    simpa using this
  have hk_mem : mem pAddr = pairs.length := hpairs.1
  have hsp : localPairsSpace X.card pairs.length = 3 * X.card + 3 * pairs.length + 1 := rfl
  have htd_le : totalDemand pairs ≤ X.card := routeTerminalPairs_totalDemand_le htp
  have htriple :
      Triple w p (fun st => st = startState [pAddr, X.card, locIdAddr, workAddr, n] mem pos)
        buildLocalPairsProc
        (retPost fun v st' =>
          v = totalDemand pairs ∧
          LocalPairsAt st'.mem (pairsBAddr workAddr) (pairsAOffAddr workAddr X.card)
            (pairsALenAddr workAddr X.card pairs.length)
            (pairsADataAddr workAddr X.card pairs.length) X pairs X.card ∧
          (∀ a < workAddr, st'.mem a = mem a) ∧
          ZeroFrom st'.mem (workAddr + localPairsSpace X.card pairs.length))
        (fun _ => buildLocalPairsCost X.card pairs.length) := by
    wram_enter
    subst st
    unfold buildLocalPairsProc
    dsimp only [seqStmts]
    have hp_lt : pAddr < 2 ^ w := hwords pAddr (by simp)
    have hsp_lt : workAddr + 3 * X.card + 3 * pairs.length + 1 + 4 < 2 ^ w := by
      dsimp only [localPairsSpace] at hw; omega
    refine runs_seq_assign_le (v := pairs.length) (by rw [← hk_mem]; eval_expr) ?_
    refine runs_seq_assign_le (v := pairsBAddr workAddr) (by dsimp only [pairsBAddr]; eval_expr) ?_
    refine runs_seq_assign_le (v := pairsAOffAddr workAddr X.card)
      (by dsimp only [pairsAOffAddr]; eval_expr) ?_
    refine runs_seq_assign_le (v := pairsALenAddr workAddr X.card pairs.length)
      (by dsimp only [pairsALenAddr]; eval_expr) ?_
    refine runs_seq_assign_le (v := pairsADataAddr workAddr X.card pairs.length)
      (by
        have h : pairsADataAddr workAddr X.card pairs.length =
            pairsALenAddr workAddr X.card pairs.length + pairs.length := by
          dsimp only [pairsADataAddr, pairsALenAddr]; omega
        rw [h]; dsimp only [pairsALenAddr]; eval_expr) ?_
    refine runs_seq_assign_le (v := pairsATagAddr workAddr X.card pairs.length)
      (by
        have h : pairsATagAddr workAddr X.card pairs.length =
            pairsADataAddr workAddr X.card pairs.length + X.card := by
          dsimp only [pairsATagAddr, pairsADataAddr]; omega
        rw [h]; dsimp only [pairsADataAddr]; eval_expr) ?_
    refine runs_seq_assign_le (v := pairsAWCurAddr workAddr X.card pairs.length)
      (by
        have h : pairsAWCurAddr workAddr X.card pairs.length =
            pairsATagAddr workAddr X.card pairs.length + X.card := by
          dsimp only [pairsAWCurAddr, pairsATagAddr]; omega
        rw [h]; dsimp only [pairsATagAddr]; eval_expr) ?_
    refine runs_seq_triple_le
      (pairsScan_triple hX hpairs hbnd htp hloc_lt hloc hzero hw hw4
        (by intro r hr; interval_cases r <;> simp [startState]))
      rfl (fun st1 hst1 => ?_)
    rcases hst1 with ⟨hr1, h11, hoff1, hwcur1, hlen1, htag1, hpb1, hlow1, hzf1⟩
    refine runs_seq_triple_le
      (pairsBucket_triple htp hwcur1 htag1 hw hw4
        (by
          intro r hr
          interval_cases r
          · rfl
          · rw [hr1 1 (by decide)]; simp [startState]
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · rw [hr1 8 (by decide)]; simp [startState]
          · rw [hr1 9 (by decide)]; simp [startState]
          · rw [hr1 10 (by decide)]; simp [startState]
          · rfl))
      rfl (fun st2 hst2 => ?_)
    rcases hst2 with ⟨hr2, hdata2, hframe2⟩
    have h11_2 : st2.regs 11 = totalDemand pairs := (hr2 11 (by decide)).trans h11
    refine runs_ret_le (v := totalDemand pairs) (by eval_expr) ?_ ?_
    · dsimp only [retPost]
      refine ⟨rfl, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · intro v hv
        rw [hframe2 _ (Or.inl (by dsimp only [pairsBAddr, pairsADataAddr]; omega))]
        exact hpb1 v hv
      · rw [hframe2 _ (Or.inl (by dsimp only [pairsAOffAddr, pairsADataAddr]; omega)),
          hoff1 pairs.length le_rfl, pairAOff_length]
        exact htd_le
      · intro i hi
        have hoff_i : st2.mem (pairsAOffAddr workAddr X.card + i) = pairAOff pairs i := by
          rw [hframe2 _ (Or.inl (by dsimp only [pairsAOffAddr, pairsADataAddr]; omega))]
          exact hoff1 i (le_of_lt hi)
        have hoff_i1 : st2.mem (pairsAOffAddr workAddr X.card + i + 1) = pairAOff pairs (i + 1) := by
          rw [show pairsAOffAddr workAddr X.card + i + 1 = pairsAOffAddr workAddr X.card + (i + 1) by omega,
            hframe2 _ (Or.inl (by dsimp only [pairsAOffAddr, pairsADataAddr]; omega))]
          exact hoff1 (i + 1) hi
        have hlen_i : st2.mem (pairsALenAddr workAddr X.card pairs.length + i) = (pairs[i]'hi).1.card := by
          rw [hframe2 _ (Or.inl (by dsimp only [pairsALenAddr, pairsADataAddr]; omega))]
          exact hlen1 i hi
        refine ⟨by rw [hoff_i, hoff_i1, hlen_i, pairAOff_succ pairs hi], hlen_i, ?_⟩
        rw [hoff_i]
        exact hdata2 i hi
      · intro a ha
        rw [hframe2 a (Or.inl (by dsimp only [pairsADataAddr]; omega))]
        exact hlow1 a ha
      · intro a ha
        rw [hframe2 a (Or.inr (Or.inr ha))]
        exact hzf1 a ha
    · simp only [buildLocalPairsCost, Expr.size]
      omega
  obtain ⟨o, st', c, hrun, hpost, hcost⟩ :=
    htriple (startState [pAddr, X.card, locIdAddr, workAddr, n] mem pos) ω rfl
  cases o with
  | normal => exact hpost.elim
  | returned v =>
    refine ⟨buildLocalPairsProc, hproc, .returned v, st', c, hrun, ?_, ?_⟩
    · dsimp only [buildLocalPairsContract, Outcome.value]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      intro X' pairs' hnX' hX' hpairs' _ _ _ hloc'
      have hXeq : X' = X := by
        ext u
        by_cases hu : u < n
        · have h1 := hloc u hu
          have h2 := hloc' u hu
          rw [h1] at h2
          by_cases hmem : u ∈ X <;> by_cases hmem' : u ∈ X' <;> simp [hmem, hmem'] at h2 ⊢
        · exact ⟨fun h => absurd (Finset.mem_range.mp (hX' h)) hu,
            fun h => absurd (Finset.mem_range.mp (hX h)) hu⟩
      have hVeq : ∀ {a : ℕ} {S₁ S₂ : Finset ℕ},
          VertSetAt mem a S₁ → VertSetAt mem a S₂ → S₁ = S₂ := by
        intro a S₁ S₂ h1 h2
        rcases h1 with ⟨xs1, _, hfin1, hseq1⟩
        rcases h2 with ⟨xs2, _, hfin2, hseq2⟩
        have hlen12 : xs1.length = xs2.length := by rw [← hseq1.1, hseq2.1]
        have hl : xs1 = xs2 := by
          apply List.ext_getElem hlen12
          intro i hi _
          rw [← hseq1.2 i hi, hseq2.2 i (hlen12 ▸ hi)]
        rw [← hfin1, hl, hfin2]
      have hPeq : pairs' = pairs := by
        have hlen' : pairs'.length = pairs.length := by rw [← hpairs'.1, hpairs.1]
        apply List.ext_getElem hlen'
        intro i hi _
        have h1 := hpairs'.2 i hi
        have h2 := hpairs.2 i (hlen' ▸ hi)
        exact Prod.ext (hVeq h1.1 h2.1) (hVeq h1.2 h2.2)
      subst hXeq; subst hPeq
      exact hpost
    · dsimp only [buildLocalPairsContract]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hk_mem]
      exact hcost

end MinCostFlow.ExpanderDecomp
