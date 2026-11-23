module

public import MinCostFlow.SparseCore.Program.TourOpsEditMovePrep
import Mathlib.Tactic

/-!
# Rank, sort, and cyclic-successor preparation for `moveEnds` (Op 0)

Verifies `tourMoveRankSortNextBody_runs`: given `m` unique active nodes `A0` of `s.ord v` written
at `pairsPtr[2*i + 1]`, computes their splay ranks in `t` (`t.toList.map key = fullTour s v`),
sorts `(rank, node)` pairs in-place via `ordHeapSortBody`, and queries `ordStoreOp 2` (`ordNext`)
to populate `nxtPtr[0 .. m)` in `O((m + 1) * tourLog eCap)` amortized time.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-- Amortized per-`(m + 1) * tourLog` cost constant for `tourMoveRankSortNextBody`. -/
def TOUR_MOVE_SORT_MUL : ℕ := 2 * TOUR_FIND_AMORT + 2 * ORD_SORT_COST_MUL + 2000

private theorem moveSort_mul_split (m mul_ord t : ℕ) :
    (m + 1) * (TOUR_MOVE_SORT_MUL + mul_ord) * t =
      (m + 1) * (2 * TOUR_FIND_AMORT + 80) * t +
      (m + 1) * (2 * ORD_SORT_COST_MUL) * t +
      (m + 1) * (mul_ord + 70) * t +
      (m + 1) * 100 * t +
      (m + 1) * 1750 * t := by
  unfold TOUR_MOVE_SORT_MUL; ring

/-- Verified amortized run theorem for `tourMoveRankSortNextBody [b, v, feV, pairsPtr, nxtPtr, m, hCur]`. -/
theorem tourMoveRankSortNextBody_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap mul_ord b v feV pairsPtr nxtPtr m hCur pos rankProc sortProc siftProc ordOp2 : ℕ}
    {alloc_ord : ℕ → List ℕ → ℕ} {p : Program} {ordInit : ℕ} {ordOp : ℕ → ℕ}
    (C : TourSplayQueryProcs w p)
    (hRank : p.procs[rankProc]? = some (tourSplayRankBody C.splay.splay))
    (hSift : p.procs[siftProc]? = some (ordSiftDownBody siftProc))
    (hSort : p.procs[sortProc]? = some (ordHeapSortBody siftProc))
    (hOrdImpl : R_ord.Implements w p ordInit ordOp (ordStoreCapContract vCap eCap mul_ord alloc_ord))
    (hop2 : ordOp 2 = ordOp2) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem0 mem : ℕ → ℕ}
    {t : AuxTree} {rest : List AuxTree} {sT : SplayState TourVal TourSum Unit}
    {A0 : List ℕ} {aHead : End}
    (h : TourCoreAt vCap eCap b s x mem0)
    (hpre_mem : ∀ a < nodesBase b vCap eCap, mem a = mem0 a)
    (hordRep : R_ord.rep (ordHandleOf b vCap eCap) s.ord x.ordX mem)
    (hordGe : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → ordHandleOf b vCap eCap ≤ a)
    (hordFoot : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → a < pairsPtr)
    (hvLt : v < vCap) (hhead : (s.ord v).head? = some aHead)
    (hfeV_eq : feV = x.nodeOf (endKey aHead))
    (hnT : tourLayout.NodesAt mem (nodesBase b vCap eCap) x.numNodes sT)
    (hinvT : TourForestInv x.numNodes sT (t :: rest)) (hvalsT : TourValsOk w x.numNodes sT)
    (ht_le : ∀ id ∈ t.toList, id ≤ x.numNodes)
    (ht_map : t.toList.map (fun id => endOfKey (x.keyOf id)) = fullTour s.ord s.rf.F h.valid.compat.forest v)
    (hA0_len : A0.length = m) (hA0_nd : A0.Nodup)
    (hA0_mem : ∀ i (hi : i < A0.length), mem (pairsPtr + (2 * i + 1)) = A0[i])
    (hA0_in : ∀ u ∈ A0, 1 ≤ u ∧ u ≤ x.numNodes ∧ endOfKey (x.keyOf u) ∈ s.ord v)
    (hord_le : ordHandleOf b vCap eCap ≤ pairsPtr)
    (hnxt_ge : pairsPtr + 2 * m ≤ nxtPtr) (hh_ge : nxtPtr + m ≤ hCur)
    (hroom : hCur + m + 4 < 2 ^ w) (hw : vCap + 2 * eCap + 4 < 2 ^ w)
    (hwide : 18 ≤ 2 ^ w) (hzero : ZeroFrom mem hCur) :
    let xs := (s.ord v).map fun z => x.nodeOf (endKey z)
    ∃ (h' : ℕ) (t' : AuxTree) (s' : SplayState TourVal TourSum Unit)
      (ordX' : R_ord.τ) (st' : State) (c : ℕ) (A : List ℕ),
      Runs w p ω (tourMoveRankSortNextBody rankProc sortProc ordOp2)
        (startState [b, v, feV, pairsPtr, nxtPtr, m, hCur] mem pos) (.returned h') st' c ∧
      hCur ≤ h' ∧ h' ≤ hCur + m ∧ ZeroFrom st'.mem h' ∧
      A.Perm A0 ∧ A.length = m ∧ A.Nodup ∧
      A.Pairwise (fun u1 u2 => t.toList.idxOf u1 ≤ t.toList.idxOf u2) ∧
      (∀ i (hi : i < A.length), st'.mem (pairsPtr + (2 * i + 1)) = A[i]) ∧
      (∀ i (hi : i < A.length),
        let idx := xs.idxOf A[i]
        st'.mem (nxtPtr + i) = if hlt : idx + 1 < xs.length then xs[idx + 1] else 0) ∧
      tourLayout.NodesAt st'.mem (nodesBase b vCap eCap) x.numNodes s' ∧
      TourForestInv x.numNodes s' (t' :: rest) ∧ TourValsOk w x.numNodes s' ∧
      t'.toList = t.toList ∧ (∀ u ≤ x.numNodes, (s'.nodes u).val = (sT.nodes u).val) ∧
      (∀ a < pairsPtr, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a →
        ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → st'.mem a = mem a) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX' a →
        R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (hCur ≤ a ∧ a < h')) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX' a → ordHandleOf b vCap eCap ≤ a) ∧
      R_ord.rep (ordHandleOf b vCap eCap) s.ord ordX' st'.mem ∧
      c + TOUR_PHI_MULT * forestPhi (t' :: rest) + R_ord.phi (ordHandleOf b vCap eCap) ordX' st'.mem ≤
        TOUR_PHI_MULT * forestPhi (t :: rest) + R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem +
          (m + 1) * (TOUR_MOVE_SORT_MUL + mul_ord) * tourLog eCap := by
  intro xs
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hlog : Nat.log 2 (2 * eCap + 2) + 1 ≤ 2 * tourLog eCap := tourLog_double_le eCap
  have hhdr : TourHeaderAt vCap eCap b x.numNodes mem := by
    have hh := h.header
    have hlt_nb : ∀ k < 16, b + k < nodesBase b vCap eCap := fun k hk => by
      simp [nodesBase]; omega
    exact ⟨(hpre_mem _ (hlt_nb HDR_VCAP (by decide))).trans hh.1,
      (hpre_mem _ (hlt_nb HDR_ECAP (by decide))).trans hh.2.1,
      (hpre_mem _ (hlt_nb HDR_ORD_H (by decide))).trans hh.2.2.1,
      (hpre_mem _ (hlt_nb HDR_NUM_NODES (by decide))).trans hh.2.2.2.1,
      (hpre_mem _ (hlt_nb HDR_FIRST_END (by decide))).trans hh.2.2.2.2.1,
      (hpre_mem _ (hlt_nb HDR_IS_ROOT (by decide))).trans hh.2.2.2.2.2.1,
      (hpre_mem _ (hlt_nb HDR_NODE_OF_END (by decide))).trans hh.2.2.2.2.2.2.1,
      (hpre_mem _ (hlt_nb HDR_END_OWNER (by decide))).trans hh.2.2.2.2.2.2.2.1,
      (hpre_mem _ (hlt_nb HDR_KEY_OF_NODE (by decide))).trans hh.2.2.2.2.2.2.2.2.1,
      (hpre_mem _ (hlt_nb HDR_MARK_ARR (by decide))).trans hh.2.2.2.2.2.2.2.2.2.1,
      (hpre_mem _ (hlt_nb HDR_PRED_ARR (by decide))).trans hh.2.2.2.2.2.2.2.2.2.2.1,
      (hpre_mem _ (hlt_nb HDR_NEXT_ARR (by decide))).trans hh.2.2.2.2.2.2.2.2.2.2.2.1,
      (hpre_mem _ (hlt_nb HDR_NODES_BASE (by decide))).trans hh.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (hpre_mem _ (hlt_nb HDR_FOOT_END (by decide))).trans hh.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      (hpre_mem _ (hlt_nb HDR_FUEL (by decide))).trans hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hrec_le : tourLayout.nodeAddr (nodesBase b vCap eCap) (x.numNodes + 1) ≤ hCur := by
    have := h.numNodes_le; simp [NodeLayout.nodeAddr, tourLayout_stride, nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
  have hm_le_e : m ≤ 2 * eCap := by
    have hnd_k : (A0.map x.keyOf).Nodup := hA0_nd.map_on fun a ha b hb hab => by
      have ha' := hA0_in a ha; have hb' := hA0_in b hb
      rw [← (h.keyOf_mem a ha'.1 ha'.2.1).2.2, hab, (h.keyOf_mem b hb'.1 hb'.2.1).2.2]
    have hcard : (A0.map x.keyOf).length ≤ (Finset.range (2 * eCap)).card := by
      rw [← List.toFinset_card_of_nodup hnd_k]
      refine Finset.card_le_card fun k hk => ?_
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
      have huin := hA0_in u hu
      exact Finset.mem_range.mpr (h.keyOf_mem u huin.1 huin.2.1).2.1
    simp only [List.length_map, Finset.card_range] at hcard; omega
  have hA0_t : ∀ u ∈ A0, u ∈ t.toList := by
    intro u hu
    have huin := hA0_in u hu
    have hft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest v :=
      ((fullTour_spec h.valid.compat v).2 _).mpr ⟨v, huin.2.2, connected_refl _ v⟩
    rw [← ht_map] at hft; obtain ⟨id, hid, hideq⟩ := List.mem_map.mp hft
    have h1 := (hinvT.mem_inCap (t := t) (by simp) hid).1
    have hkeq : x.keyOf id = x.keyOf u := by rw [← endKey_endOfKey' (x.keyOf id), hideq, endKey_endOfKey']
    have heq : id = u := by
      rw [← (h.keyOf_mem id h1 (ht_le id hid)).2.2, hkeq, (h.keyOf_mem u huin.1 huin.2.1).2.2]
    exact heq ▸ hid
  -- Phase 1: compute splay ranks into `pairsPtr + 2 * i`
  have hphase1 : ∀ (rem i : ℕ) (tC : AuxTree) (sC : SplayState TourVal TourSum Unit) (stC : State),
      (hrem : i + rem = m) →
      stC.regs 0 = b → stC.regs 1 = v → stC.regs 2 = feV → stC.regs 3 = pairsPtr →
      stC.regs 4 = nxtPtr → stC.regs 5 = m → stC.regs 6 = hCur →
      stC.regs 7 = nodesBase b vCap eCap → stC.regs 8 = 2 * eCap + 2 →
      stC.regs 9 = keyOfNodeBase b vCap eCap → stC.regs 10 = nodeOfEndBase b vCap →
      stC.regs 11 = ordHandleOf b vCap eCap → stC.regs 12 = i →
      tourLayout.NodesAt stC.mem (nodesBase b vCap eCap) x.numNodes sC →
      TourForestInv x.numNodes sC (tC :: rest) → TourValsOk w x.numNodes sC →
      tC.toList = t.toList → (∀ u ≤ x.numNodes, (sC.nodes u).val = (sT.nodes u).val) →
      ZeroFrom stC.mem hCur →
      (∀ q (hq : q < i), stC.mem (pairsPtr + 2 * q) = t.toList.idxOf (A0[q]'(by omega))) →
      (∀ q (hq : q < A0.length), stC.mem (pairsPtr + (2 * q + 1)) = A0[q]) →
      (∀ a < pairsPtr, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a → stC.mem a = mem a) →
      ∃ (t1 : AuxTree) (s1 : SplayState TourVal TourSum Unit) (st1 : State) (c1 : ℕ),
        Runs w p ω (.loop (.bin .lt (.reg 12) (.reg 5))
          (.assign 13 (.bin .add (.reg 3) (.bin .add (.reg 12) (.reg 12))) ;;
           .assign 14 (.load (.bin .add (.reg 13) (.const 1))) ;;
           .call 15 rankProc [.reg 7, .reg 14, .reg 8, .reg 6] ;;
           .store (.reg 13) (.reg 15) ;;
           .assign 12 (.bin .add (.reg 12) (.const 1)))) stC .normal st1 c1 ∧
        st1.regs 1 = v ∧ st1.regs 2 = feV ∧ st1.regs 3 = pairsPtr ∧ st1.regs 4 = nxtPtr ∧
        st1.regs 5 = m ∧ st1.regs 6 = hCur ∧ st1.regs 9 = keyOfNodeBase b vCap eCap ∧
        st1.regs 10 = nodeOfEndBase b vCap ∧ st1.regs 11 = ordHandleOf b vCap eCap ∧
        tourLayout.NodesAt st1.mem (nodesBase b vCap eCap) x.numNodes s1 ∧
        TourForestInv x.numNodes s1 (t1 :: rest) ∧ TourValsOk w x.numNodes s1 ∧
        t1.toList = t.toList ∧ (∀ u ≤ x.numNodes, (s1.nodes u).val = (sT.nodes u).val) ∧
        ZeroFrom st1.mem hCur ∧
        readPairs st1.mem pairsPtr m = A0.map (fun u => (t.toList.idxOf u, u)) ∧
        (∀ a < pairsPtr, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a → st1.mem a = mem a) ∧
        c1 + TOUR_PHI_MULT * forestPhi (t1 :: rest) ≤
          TOUR_PHI_MULT * forestPhi (tC :: rest) + rem * (TOUR_FIND_AMORT + 40) * (Nat.log 2 (x.numNodes + 2) + 1) + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro i tC sC stC hrem hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12
        hnC hinvC hvalsC htC hvalC hzC hrk hndP hfrC
      have him : i = m := by omega
      have hcond : (Expr.bin .lt (.reg 12) (.reg 5)).eval w stC = some 0 := by
        simp [Expr.eval, hr12, hr5, him, BinOp.eval, (by omega : 0 < 2 ^ w)]
      have hrp : readPairs stC.mem pairsPtr m = A0.map (fun u => (t.toList.idxOf u, u)) := by
        apply List.ext_getElem (by simp [readPairs_length, hA0_len])
        intro q hq _
        simp only [readPairs_length] at hq
        simp only [readPairs_getElem, List.getElem_map]
        exact Prod.ext (hrk q (by omega)) (by simpa [Nat.add_assoc] using hndP q (by omega))
      refine ⟨tC, sC, stC, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        hr1, hr2, hr3, hr4, hr5, hr6, hr9, hr10, hr11, hnC, hinvC, hvalsC, htC, hvalC, hzC, hrp, hfrC, ?_⟩
      simp only [Expr.size]; omega
    | succ rem ih =>
      intro i tC sC stC hrem hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr11 hr12
        hnC hinvC hvalsC htC hvalC hzC hrk hndP hfrC
      have hi_lt : i < m := by omega
      set u := A0[i]'(by omega)
      have hu_tC : u ∈ tC.toList := htC ▸ hA0_t u (List.getElem_mem _)
      have hcond : (Expr.bin .lt (.reg 12) (.reg 5)).eval w stC = some 1 := by
        simp [Expr.eval, hr12, hr5, hi_lt, BinOp.eval, (by omega : 1 < 2 ^ w)]
      set r1 := Function.update stC.regs 13 (pairsPtr + 2 * i)
      set r2 := Function.update r1 14 u
      have ha13 : Runs w p ω (.assign 13 (.bin .add (.reg 3) (.bin .add (.reg 12) (.reg 12))))
          stC .normal { stC with regs := r1 } 6 :=
        runs_assign_iff.mpr ⟨pairsPtr + 2 * i, by
          simp [Expr.eval, hr3, hr12, BinOp.eval, (by omega : i + i < 2 ^ w),
            (by omega : pairsPtr + (i + i) < 2 ^ w)]; omega, rfl, rfl, rfl⟩
      have ha14 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 13) (.const 1))))
          { stC with regs := r1 } .normal { stC with regs := r2 } 5 :=
        runs_assign_iff.mpr ⟨u, by
          simp [Expr.eval, r1, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : pairsPtr + 2 * i + 1 < 2 ^ w),
            show stC.mem (pairsPtr + 2 * i + 1) = u by simpa [Nat.add_assoc] using hndP i (by omega)], rfl, rfl, rfl⟩
      obtain ⟨tN, sN, oN, stN, cN, hrunN, hvN, hnN, hfrN, hinvN, hvalsN, htN, hvalN, _, hcostN⟩ :=
        tourSplayRankBody_runs (pos := stC.pos) (fuel := 2 * eCap + 2) C.toTourSplayCoreProcs ω hnC hinvC hvalsC hu_tC
          (by have := h.numNodes_le; omega) (by omega) ⟨hrec_le, by omega, hzC, by omega⟩
      have hcallR := runs_call_regs4 15 7 14 8 6 (st := { stC with regs := r2 }) hRank
        (by simp [r2, r1, hr7]) (by simp [r2]) (by simp [r2, r1, hr8]) (by simp [r2, r1, hr6]) hrunN
      set r3 := Function.update r2 15 oN.value
      set memN := Function.update stN.mem (pairsPtr + 2 * i) (t.toList.idxOf u)
      have hstR : Runs w p ω (.store (.reg 13) (.reg 15)) { stN with regs := r3 } .normal
          { stN with mem := memN, regs := r3 } 3 :=
        runs_store_iff.mpr ⟨pairsPtr + 2 * i, t.toList.idxOf u,
          by simp [Expr.eval, r3, r2, r1], by simp [Expr.eval, r3, hvN, htC], rfl, rfl, rfl⟩
      set r4 := Function.update r3 12 (i + 1)
      have ha12 : Runs w p ω (.assign 12 (.bin .add (.reg 12) (.const 1)))
          { stN with mem := memN, regs := r3 } .normal { stN with mem := memN, regs := r4 } 4 :=
        runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, r3, r2, r1, hr12, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : i + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hbody := tour_runs_seq_normal ha13 (tour_runs_seq_normal ha14 (tour_runs_seq_normal hcallR (tour_runs_seq_normal hstR ha12)))
      have hnN' : tourLayout.NodesAt memN (nodesBase b vCap eCap) x.numNodes sN :=
        NodesAt.congr tourLayout hnN fun a ha => by
          have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).2; dsimp only [memN]; exact Function.update_of_ne (by omega) _ _
      obtain ⟨t1, s1, st1, c1, hrun1, h11, h12, h13, h14, h15, h16, h19, h110, h111,
        hn1, hinv1, hvals1, ht1, hval1, hz1, hrp1, hfr1, hc1⟩ :=
        ih (i + 1) tN sN { stN with mem := memN, regs := r4 } (by omega)
          (by simp [r4, r3, r2, r1, hr0]) (by simp [r4, r3, r2, r1, hr1]) (by simp [r4, r3, r2, r1, hr2])
          (by simp [r4, r3, r2, r1, hr3]) (by simp [r4, r3, r2, r1, hr4]) (by simp [r4, r3, r2, r1, hr5])
          (by simp [r4, r3, r2, r1, hr6]) (by simp [r4, r3, r2, r1, hr7]) (by simp [r4, r3, r2, r1, hr8])
          (by simp [r4, r3, r2, r1, hr9]) (by simp [r4, r3, r2, r1, hr10]) (by simp [r4, r3, r2, r1, hr11])
          (by simp [r4]) hnN' hinvN hvalsN (htN.trans htC)
          (fun z hz => (hvalN z hz).trans (hvalC z hz))
          (fun a ha => by dsimp only [memN]; rw [Function.update_of_ne (by omega)]; exact hfrN.1 a ha)
          (fun q hq => by
            dsimp only [memN]
            by_cases hqi : q = i
            · subst hqi; simp [u]
            · rw [Function.update_of_ne (by omega), hfrN.2 _ (by omega) (not_inRecords_of_ge_ordHandle_of_le h.numNodes_le (by omega))]
              exact hrk q (by omega))
          (fun q hq => by
            dsimp only [memN]
            rw [Function.update_of_ne (by omega), hfrN.2 _ (by omega) (not_inRecords_of_ge_ordHandle_of_le h.numNodes_le (by omega))]
            exact hndP q hq)
          (fun a ha hnr => by
            dsimp only [memN]
            rw [Function.update_of_ne (by omega), hfrN.2 a (by omega) hnr]
            exact hfrC a ha hnr)
      refine ⟨t1, s1, st1, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega, hbody, hrun1, rfl⟩)),
        h11, h12, h13, h14, h15, h16, h19, h110, h111, hn1, hinv1, hvals1, ht1, hval1, hz1, hrp1, hfr1, ?_⟩
      have hmul : (rem + 1) * (TOUR_FIND_AMORT + 40) * (Nat.log 2 (x.numNodes + 2) + 1) =
          rem * (TOUR_FIND_AMORT + 40) * (Nat.log 2 (x.numNodes + 2) + 1) +
          (TOUR_FIND_AMORT + 40) * (Nat.log 2 (x.numNodes + 2) + 1) := by ring
      have hlog1 : 1 ≤ Nat.log 2 (x.numNodes + 2) + 1 := by omega
      have hstep : TOUR_FIND_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) + 40 ≤
          (TOUR_FIND_AMORT + 40) * (Nat.log 2 (x.numNodes + 2) + 1) := by
        clear * - hlog1; simp only [TOUR_FIND_AMORT]; omega
      clear * - hcostN hc1 hmul hstep; simp only [Expr.size] at *; linarith
  -- Execute header loads + Phase 1
  set s0 : State := startState [b, v, feV, pairsPtr, nxtPtr, m, hCur] mem pos
  set r01 := Function.update s0.regs 7 (nodesBase b vCap eCap)
  set r02 := Function.update r01 8 (2 * eCap + 2)
  set r03 := Function.update r02 9 (keyOfNodeBase b vCap eCap)
  set r04 := Function.update r03 10 (nodeOfEndBase b vCap)
  set r05 := Function.update r04 11 (ordHandleOf b vCap eCap)
  set r06 := Function.update r05 12 0
  have ha7 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 0) (off := HDR_NODES_BASE)
    (b := b) (val := nodesBase b vCap eCap) (st := s0) (by simp [s0, startState])
    (by simp [HDR_NODES_BASE]; omega) (by simp [HDR_NODES_BASE]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ha8 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 0) (off := HDR_FUEL)
    (b := b) (val := 2 * eCap + 2) (st := ⟨mem, r01, pos⟩) (by simp [r01, s0, startState])
    (by simp [HDR_FUEL]; omega) (by simp [HDR_FUEL]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have ha9 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 9) (rBase := 0) (off := HDR_KEY_OF_NODE)
    (b := b) (val := keyOfNodeBase b vCap eCap) (st := ⟨mem, r02, pos⟩) (by simp [r02, r01, s0, startState])
    (by simp [HDR_KEY_OF_NODE]; omega) (by simp [HDR_KEY_OF_NODE]; omega) hhdr.2.2.2.2.2.2.2.2.1
  have ha10 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 10) (rBase := 0) (off := HDR_NODE_OF_END)
    (b := b) (val := nodeOfEndBase b vCap) (st := ⟨mem, r03, pos⟩) (by simp [r03, r02, r01, s0, startState])
    (by simp [HDR_NODE_OF_END]; omega) (by simp [HDR_NODE_OF_END]; omega) hhdr.2.2.2.2.2.2.1
  have ha11 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 0) (off := HDR_ORD_H)
    (b := b) (val := ordHandleOf b vCap eCap) (st := ⟨mem, r04, pos⟩) (by simp [r04, r03, r02, r01, s0, startState])
    (by simp [HDR_ORD_H]; omega) (by simp [HDR_ORD_H]; omega) hhdr.2.2.1
  have ha12 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 12) (val := 0) (st := ⟨mem, r05, pos⟩) (by omega)
  obtain ⟨t1, s1, st1, c1, hrun1, h11, h12, h13, h14, h15, h16, h19, h110, h111,
    hn1, hinv1, hvals1, ht1, hval1, hz1, hrp1, hfr1, hc1⟩ :=
    hphase1 m 0 t sT ⟨mem, r06, pos⟩ (by omega)
      (by simp [r06, r05, r04, r03, r02, r01, s0, startState]) (by simp [r06, r05, r04, r03, r02, r01, s0, startState])
      (by simp [r06, r05, r04, r03, r02, r01, s0, startState]) (by simp [r06, r05, r04, r03, r02, r01, s0, startState])
      (by simp [r06, r05, r04, r03, r02, r01, s0, startState]) (by simp [r06, r05, r04, r03, r02, r01, s0, startState])
      (by simp [r06, r05, r04, r03, r02, r01, s0, startState]) (by simp [r06, r05, r04, r03, r02, r01])
      (by simp [r06, r05, r04, r03, r02]) (by simp [r06, r05, r04, r03]) (by simp [r06, r05, r04])
      (by simp [r06, r05]) (by simp [r06]) hnT hinvT hvalsT rfl (fun _ _ => rfl) hzero
      (fun _ hq => by omega) hA0_mem (fun _ _ _ => rfl)
  -- Phase 2: in-place heapsort of `(rank, node)` pairs at `pairsPtr[0 .. 2*m)`
  obtain ⟨oS, stS, cS, hrunS, ⟨hS_pw, hS_perm, hS_out⟩, hcS⟩ :=
    ordHeapSortBody_runs (w := w) (arr := pairsPtr) (n := m) (pos := st1.pos) hSift ω (by omega) (mem := st1.mem)
  have hcallS : Runs w p ω (.call 15 sortProc [.reg 3, .reg 5]) st1 .normal
      { stS with regs := Function.update st1.regs 15 oS.value } (3 + cS) := by
    have := tour_runs_call_of (r := 15) (args := [.reg 3, .reg 5]) hSort (by simp [evalArgs, Expr.eval, h13, h15]) hrunS
    convert this using 1; simp [argsSize, Expr.size]; omega
  set rS := Function.update st1.regs 15 oS.value
  set A := (readPairs stS.mem pairsPtr m).map Prod.snd
  have hS_perm' : (readPairs stS.mem pairsPtr m).Perm (A0.map fun u => (t.toList.idxOf u, u)) := hrp1 ▸ hS_perm
  have hA_perm : A.Perm A0 := by simpa [A, List.map_map, Function.comp_def] using hS_perm'.map Prod.snd
  have hA_len : A.length = m := by simp [A, readPairs_length]
  have hA_nd : A.Nodup := hA_perm.nodup_iff.mpr hA0_nd
  have hA_mem : ∀ q (hq : q < m), stS.mem (pairsPtr + (2 * q + 1)) = A[q]'(by omega) := fun q hq => by
    simp only [A, List.getElem_map, readPairs_getElem]; simp [Nat.add_assoc]
  have hA_pw : A.Pairwise (fun u1 u2 => t.toList.idxOf u1 ≤ t.toList.idxOf u2) := by
    have hpair_fst : ∀ p ∈ readPairs stS.mem pairsPtr m, p.1 = t.toList.idxOf p.2 := fun p hp => by
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp (hS_perm'.mem_iff.mp hp); rfl
    exact (List.pairwise_map (f := Prod.snd)).mpr
      (hS_pw.imp_of_mem fun {a b} ha hb hab => by rwa [← hpair_fst a ha, ← hpair_fst b hb])
  have hfrS_lo : ∀ a < pairsPtr, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a → stS.mem a = mem a :=
    fun a ha hnr => (hS_out a (Or.inl ha)).trans (hfr1 a ha hnr)
  have hordS_agree : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → stS.mem a = mem a := fun a ha =>
    hfrS_lo a (hordFoot a ha) (not_inRecords_of_ge_ordHandle_of_le h.numNodes_le (hordGe a ha))
  have hOrdS := hOrdImpl.1 (ordHandleOf b vCap eCap) s.ord x.ordX mem stS.mem (fun a ha => (hordS_agree a ha).symm)
  have hnS : tourLayout.NodesAt stS.mem (nodesBase b vCap eCap) x.numNodes s1 :=
    NodesAt.congr tourLayout hn1 fun a ha => hS_out a (Or.inl (lt_of_lt_of_le (inRecords_lt_ordHandle_of_le h.numNodes_le ha).2 hord_le))
  have hzS : ZeroFrom stS.mem hCur := fun a ha => (hS_out a (Or.inr (by omega))).trans (hz1 a ha)
  -- Load `feKey := mem[keyOfNodeBase + feV]` and reset `r12 := 0`
  have haHead_lt : endKey aHead < 2 * eCap := by
    have := h.valid.ordWithin.2.2 v aHead (List.mem_of_head? hhead); exact key_lt_two_mul_of_endOfKey (by simpa [endOfKey_endKey] using this)
  have hfeV_nz : feV ≠ 0 := hfeV_eq ▸ (h.active_end v hvLt aHead (List.mem_of_head? hhead)).1
  have hfeV_le : feV ≤ x.numNodes := hfeV_eq ▸ (h.nodeOf_mem _ haHead_lt).2
  have hfeKey_eq : x.keyOf feV = endKey aHead := by rw [hfeV_eq]; exact h.nodeOf_keyOf _ haHead_lt (hfeV_eq ▸ hfeV_nz)
  have hfeV_cap : feV ≤ 2 * eCap := le_trans hfeV_le h.numNodes_le
  have hmS_feKey : stS.mem (keyOfNodeBase b vCap eCap + feV) = endKey aHead := by
    rw [hfrS_lo _ (by simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
      (not_inRecords_of_lt_nodesBase (by simp [keyOfNodeBase, nodesBase]; omega))]
    rw [hpre_mem _ (by simp [keyOfNodeBase, nodesBase]; omega), ← hfeKey_eq]
    exact (h.keyOf_mem feV (by omega) hfeV_le).1
  set rS1 := Function.update rS 13 (endKey aHead)
  set rS2 := Function.update rS1 12 0
  have ha_fek := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 13) (rBase := 9) (rIdx := 2)
    (base := keyOfNodeBase b vCap eCap) (idx := feV) (val := endKey aHead) (st := { stS with regs := rS })
    (by simp [rS, h19]) (by simp [rS, h12])
    (by have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) hmS_feKey
  have ha_i0 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 12) (val := 0)
    (st := { stS with regs := rS1 }) (by omega)
  -- Phase 3: query `ordNext` for each `A[i]` to populate `nxtPtr[i]`
  have hphase3 : ∀ (rem i hC : ℕ) (ordXC : R_ord.τ) (stC : State),
      (hrem : i + rem = m) → hCur ≤ hC → hC ≤ hCur + i →
      stC.regs 1 = v → stC.regs 3 = pairsPtr → stC.regs 4 = nxtPtr → stC.regs 5 = m →
      stC.regs 6 = hC → stC.regs 9 = keyOfNodeBase b vCap eCap → stC.regs 10 = nodeOfEndBase b vCap →
      stC.regs 11 = ordHandleOf b vCap eCap → stC.regs 12 = i → stC.regs 13 = endKey aHead →
      ZeroFrom stC.mem hC →
      (∀ q (hq : q < m), stC.mem (pairsPtr + (2 * q + 1)) = A[q]'(by omega)) →
      (∀ q (hq : q < i), let idx := xs.idxOf (A[q]'(by omega))
        stC.mem (nxtPtr + q) = if hlt : idx + 1 < xs.length then xs[idx + 1] else 0) →
      tourLayout.NodesAt stC.mem (nodesBase b vCap eCap) x.numNodes s1 →
      (∀ a < pairsPtr, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a →
        ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → stC.mem a = mem a) →
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordXC a →
        R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (hCur ≤ a ∧ a < hC)) →
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordXC a → ordHandleOf b vCap eCap ≤ a) →
      R_ord.rep (ordHandleOf b vCap eCap) s.ord ordXC stC.mem →
      ∃ (h' : ℕ) (ordX' : R_ord.τ) (stF : State) (c3 : ℕ),
        Runs w p ω (.loop (.bin .lt (.reg 12) (.reg 5))
          (.assign 14 (.load (.bin .add (.reg 3) (.bin .add (.bin .add (.reg 12) (.reg 12)) (.const 1)))) ;;
           .assign 14 (.load (.bin .add (.reg 9) (.reg 14))) ;;
           .assign 15 (.reg 6) ;;
           .call 6 ordOp2 [.reg 11, .reg 1, .reg 14, .reg 6] ;;
           .assign 14 (.load (.reg 15)) ;;
           .cond (.bin .eq (.reg 14) (.reg 13))
             (.store (.bin .add (.reg 4) (.reg 12)) (.const 0))
             (.assign 14 (.load (.bin .add (.reg 10) (.reg 14))) ;;
              .store (.bin .add (.reg 4) (.reg 12)) (.reg 14)) ;;
           .assign 12 (.bin .add (.reg 12) (.const 1)))) stC .normal stF c3 ∧
        stF.regs 6 = h' ∧ hCur ≤ h' ∧ h' ≤ hCur + m ∧ ZeroFrom stF.mem h' ∧
        (∀ q (hq : q < m), stF.mem (pairsPtr + (2 * q + 1)) = A[q]'(by omega)) ∧
        (∀ q (hq : q < m), let idx := xs.idxOf (A[q]'(by omega))
          stF.mem (nxtPtr + q) = if hlt : idx + 1 < xs.length then xs[idx + 1] else 0) ∧
        tourLayout.NodesAt stF.mem (nodesBase b vCap eCap) x.numNodes s1 ∧
        (∀ a < pairsPtr, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a →
          ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → stF.mem a = mem a) ∧
        (∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX' a →
          R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (hCur ≤ a ∧ a < h')) ∧
        (∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX' a → ordHandleOf b vCap eCap ≤ a) ∧
        R_ord.rep (ordHandleOf b vCap eCap) s.ord ordX' stF.mem ∧
        c3 + R_ord.phi (ordHandleOf b vCap eCap) ordX' stF.mem ≤
          R_ord.phi (ordHandleOf b vCap eCap) ordXC stC.mem + rem * (mul_ord * tourLog eCap + 70) + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro i hC ordXC stC hrem hh1 hh2 hr1 hr3 hr4 hr5 hr6 hr9 hr10 hr11 hr12 hr13
        hzC hAm hNm hnC hfrC hftC hgeC hrepC
      have him : i = m := by omega
      have hcond : (Expr.bin .lt (.reg 12) (.reg 5)).eval w stC = some 0 := by
        simp [Expr.eval, hr12, hr5, him, BinOp.eval, (by omega : 0 < 2 ^ w)]
      refine ⟨hC, ordXC, stC, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        hr6, hh1, by omega, hzC, hAm, fun q hq => hNm q (by omega), hnC, hfrC, hftC, hgeC, hrepC,
        by simp only [Expr.size]; omega⟩
    | succ rem ih =>
      intro i hC ordXC stC hrem hh1 hh2 hr1 hr3 hr4 hr5 hr6 hr9 hr10 hr11 hr12 hr13
        hzC hAm hNm hnC hfrC hftC hgeC hrepC
      have hi_lt : i < m := by omega
      set u := A[i]'(by omega)
      have hu_in := hA0_in u (hA_perm.mem_iff.mp (List.getElem_mem _))
      set ku := x.keyOf u
      have hku_lt : ku < 2 * eCap := (h.keyOf_mem u hu_in.1 hu_in.2.1).2.1
      have hcond : (Expr.bin .lt (.reg 12) (.reg 5)).eval w stC = some 1 := by
        simp [Expr.eval, hr12, hr5, hi_lt, BinOp.eval, (by omega : 1 < 2 ^ w)]
      have hAm_i : stC.mem (pairsPtr + (i + i + 1)) = u := by
        convert hAm i hi_lt using 2; omega
      have hmC_ku : stC.mem (keyOfNodeBase b vCap eCap + u) = ku := by
        have hu_le_e : u ≤ 2 * eCap := le_trans hu_in.2.1 h.numNodes_le
        rw [hfrC _ (by simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
          (not_inRecords_of_lt_nodesBase (by simp [keyOfNodeBase, nodesBase]; omega))
          (fun hft => by have := hordGe _ hft; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at this; omega)]
        rw [hpre_mem _ (by simp [keyOfNodeBase, nodesBase]; omega)]
        exact (h.keyOf_mem u hu_in.1 hu_in.2.1).1
      set r1 := Function.update stC.regs 14 u
      set r2 := Function.update r1 14 ku
      set r3 := Function.update r2 15 hC
      have ha_u : Runs w p ω (.assign 14 (.load (.bin .add (.reg 3) (.bin .add (.bin .add (.reg 12) (.reg 12)) (.const 1)))))
          stC .normal { stC with regs := r1 } 9 :=
        runs_assign_iff.mpr ⟨u, by
          simp [Expr.eval, hr3, hr12, BinOp.eval, (by omega : 1 < 2 ^ w),
            (by omega : i + i < 2 ^ w), (by omega : i + i + 1 < 2 ^ w),
            (by omega : pairsPtr + (i + i + 1) < 2 ^ w), hAm_i], rfl, rfl, rfl⟩
      have ha_ku := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 9) (rIdx := 14)
        (base := keyOfNodeBase b vCap eCap) (idx := u) (val := ku) (st := { stC with regs := r1 })
        (by simp [r1, hr9]) (by simp [r1])
        (by have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) hmC_ku
      have ha_out : Runs w p ω (.assign 15 (.reg 6)) { stC with regs := r2 } .normal { stC with regs := r3 } 2 :=
        runs_assign_iff.mpr ⟨hC, by simp [Expr.eval, r2, r1, hr6], rfl, rfl, rfl⟩
      -- Call `ordNext [ordH, v, ku, hC]`
      have hfootC_lt : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordXC a → a < hC := fun a ha => by
        rcases hftC a ha with h0 | ⟨_, h2⟩; exact lt_of_lt_of_le (hordFoot a h0) (by omega); exact h2
      have hpreN : (ordStoreCapContract vCap eCap mul_ord alloc_ord).pre 2 s.ord
          [ordHandleOf b vCap eCap, v, ku, hC] stC.mem :=
        ⟨ordHandleOf b vCap eCap, v, ku, hC, rfl, hvLt, hu_in.2.2⟩
      have hargWN : ∀ a ∈ [ordHandleOf b vCap eCap, v, ku, hC], a < 2 ^ w := by
        intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> omega
      obtain ⟨bodyN, hgetN, oN, stN, cN, hrunN, sOrdN, ordXN, hrepN, hpostN, hrespN, hcostN⟩ :=
        hOrdImpl.2.2 2 (ordHandleOf b vCap eCap) s.ord ordXC [ordHandleOf b vCap eCap, v, ku, hC]
          stC.mem stC.pos ω hargWN rfl hrepC hpreN hfootC_lt hzC
          (by simpa [ordStoreCapContract, heapArg] using (by omega : hC + 1 < 2 ^ w))
      rcases hrespN with ⟨hN_ge, hN_le, hzN, hfrN, hfootN⟩
      have hhaN : heapArg [ordHandleOf b vCap eCap, v, ku, hC] = hC := rfl
      simp only [hhaN, ordStoreCapContract, List.getD_cons_zero, List.getD_cons_succ, ordStoreLog_eq_tourLog]
        at hN_ge hN_le hzN hfrN hfootN hcostN hpostN
      rw [hop2] at hgetN
      set kNxt := endKey (cycNext (s.ord v) (endOfKey ku))
      have hkNxt_val : stN.mem hC = kNxt := by simpa [kNxt, cycNext] using hpostN.2
      have hcallN := runs_call_regs4 6 11 1 14 6 (st := { stC with regs := r3 }) hgetN
        (by simp [r3, r2, r1, hr11]) (by simp [r3, r2, r1, hr1]) (by simp [r3, r2]) (by simp [r3, r2, r1, hr6]) hrunN
      set r4 := Function.update r3 6 oN.value
      set r5 := Function.update r4 14 kNxt
      have ha_kn : Runs w p ω (.assign 14 (.load (.reg 15))) { stN with regs := r4 } .normal { stN with regs := r5 } 3 :=
        runs_assign_iff.mpr ⟨kNxt, by simp [Expr.eval, r4, r3, hkNxt_val], rfl, rfl, rfl⟩
      -- Pure relation between `kNxt` and `xs.idxOf u + 1`
      set wVal := if kNxt = endKey aHead then 0 else x.nodeOf kNxt
      have hwVal_spec : let idx := xs.idxOf u
          wVal = if hlt : idx + 1 < xs.length then xs[idx + 1] else 0 := by
        dsimp only
        have hlen_xs : xs.length = (s.ord v).length := List.length_map _
        have hidx_eq : xs.idxOf u = (s.ord v).idxOf (endOfKey ku) := by
          have hu_eq : u = x.nodeOf (endKey (endOfKey ku)) := by
            rw [endKey_endOfKey', (h.keyOf_mem u hu_in.1 hu_in.2.1).2.2]
          have hmem_z := hu_in.2.2
          have hinj_v : ∀ z1 ∈ s.ord v, ∀ z2 ∈ s.ord v, x.nodeOf (endKey z1) = x.nodeOf (endKey z2) → z1 = z2 := by
            intro z1 hz1 z2 hz2 heq
            have h1 := h.nodeOf_keyOf _ (key_lt_two_mul_of_endOfKey (by simpa [endOfKey_endKey] using h.valid.ordWithin.2.2 v z1 hz1)) (h.active_end v hvLt z1 hz1).1
            have h2 := h.nodeOf_keyOf _ (key_lt_two_mul_of_endOfKey (by simpa [endOfKey_endKey] using h.valid.ordWithin.2.2 v z2 hz2)) (h.active_end v hvLt z2 hz2).1
            have hkeq : endKey z1 = endKey z2 := by rw [← h1, heq, h2]
            rw [← endOfKey_endKey z1, hkeq, endOfKey_endKey]
          rw [hu_eq]; dsimp only [xs]; generalize s.ord v = ls at hmem_z hinj_v ⊢
          induction ls with
          | nil => simp at hmem_z
          | cons a as ihl =>
            by_cases ha : a = endOfKey ku
            · subst ha; simp
            · have hne : x.nodeOf (endKey a) ≠ x.nodeOf (endKey (endOfKey ku)) := fun heq =>
                ha (hinj_v a (by simp) (endOfKey ku) hmem_z heq)
              have hmas : endOfKey ku ∈ as := (List.mem_cons.mp hmem_z).resolve_left (Ne.symm ha)
              simp [List.idxOf_cons_ne _ ha, List.idxOf_cons_ne _ hne,
                ihl hmas (fun z1 hz1 z2 hz2 => hinj_v z1 (by simp [hz1]) z2 (by simp [hz2]))]
        have hidx_lt : (s.ord v).idxOf (endOfKey ku) < (s.ord v).length := List.idxOf_lt_length_iff.mpr hu_in.2.2
        have hpos_len : 0 < (s.ord v).length := by omega
        have hcyc : cycNext (s.ord v) (endOfKey ku) =
            (s.ord v)[((s.ord v).idxOf (endOfKey ku) + 1) % (s.ord v).length]'(Nat.mod_lt _ hpos_len) :=
          List.getD_eq_getElem _ _ (Nat.mod_lt _ hpos_len)
        by_cases hlt : (s.ord v).idxOf (endOfKey ku) + 1 < (s.ord v).length
        · have hmod : ((s.ord v).idxOf (endOfKey ku) + 1) % (s.ord v).length = (s.ord v).idxOf (endOfKey ku) + 1 :=
            Nat.mod_eq_of_lt hlt
          have hcyc' : cycNext (s.ord v) (endOfKey ku) = (s.ord v)[(s.ord v).idxOf (endOfKey ku) + 1]'hlt := by
            simpa [hmod] using hcyc
          have hne_hd : kNxt ≠ endKey aHead := fun heq => by
            have h0 : (s.ord v)[0]'hpos_len = aHead :=
              Option.some.inj ((List.getElem?_eq_getElem hpos_len).symm.trans (List.head?_eq_getElem?.symm.trans hhead))
            have heq_e : (s.ord v)[(s.ord v).idxOf (endOfKey ku) + 1]'hlt = (s.ord v)[0]'hpos_len := by
              dsimp only [kNxt] at heq
              rw [h0, ← hcyc', ← endOfKey_endKey (cycNext _ _), heq, endOfKey_endKey]
            have := (List.Nodup.getElem_inj_iff (h.valid.ordWithin.1 v)).mp heq_e
            omega
          simp only [wVal, ite_eq_right_iff.mpr (fun h => absurd h hne_hd), hidx_eq, hlen_xs, hlt, ↓reduceDIte, xs, List.getElem_map, kNxt, hcyc']
        · have heq_len : (s.ord v).idxOf (endOfKey ku) + 1 = (s.ord v).length := by omega
          have hmod : ((s.ord v).idxOf (endOfKey ku) + 1) % (s.ord v).length = 0 := by rw [heq_len, Nat.mod_self]
          have h0 : (s.ord v)[0]'hpos_len = aHead :=
            Option.some.inj ((List.getElem?_eq_getElem hpos_len).symm.trans (List.head?_eq_getElem?.symm.trans hhead))
          have hk_hd : kNxt = endKey aHead := by simp [kNxt, hcyc, hmod, h0]
          simp only [wVal, hk_hd, ↓reduceIte, hidx_eq, hlen_xs, hlt, ↓reduceDIte]
      -- Execute the `cond (r14 == r13)` writing `wVal` to `nxtPtr + i`
      set memN1 := Function.update stN.mem (nxtPtr + i) wVal
      have hcond_branch : ∃ (r6 : ℕ → ℕ) (cB : ℕ), cB ≤ 25 ∧
          (∀ k, k ≠ 14 → r6 k = r5 k) ∧
          Runs w p ω (.cond (.bin .eq (.reg 14) (.reg 13))
            (.store (.bin .add (.reg 4) (.reg 12)) (.const 0))
            (.assign 14 (.load (.bin .add (.reg 10) (.reg 14))) ;;
             .store (.bin .add (.reg 4) (.reg 12)) (.reg 14)))
            { stN with regs := r5 } .normal { stN with mem := memN1, regs := r6 } cB := by
        by_cases hk_hd : kNxt = endKey aHead
        · have hc_t : (Expr.bin .eq (.reg 14) (.reg 13)).eval w { stN with regs := r5 } = some 1 := by
            simp [Expr.eval, r5, r4, r3, r2, r1, hr13, hk_hd, BinOp.eval, (by omega : 1 < 2 ^ w)]
          have hst0 : Runs w p ω (.store (.bin .add (.reg 4) (.reg 12)) (.const 0))
              { stN with regs := r5 } .normal { stN with mem := memN1, regs := r5 } 5 :=
            runs_store_iff.mpr ⟨nxtPtr + i, 0,
              by simp [Expr.eval, r5, r4, r3, r2, r1, hr4, hr12, BinOp.eval, (by omega : nxtPtr + i < 2 ^ w)],
              by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, by congr 1; simp only [memN1, wVal, hk_hd, ↓reduceIte], rfl⟩
          exact ⟨r5, _, by simp [Expr.size], fun _ _ => rfl, tour_runs_cond_true hc_t (by omega) hst0⟩
        · have hc_f : (Expr.bin .eq (.reg 14) (.reg 13)).eval w { stN with regs := r5 } = some 0 := by
            simp [Expr.eval, r5, r4, r3, r2, r1, hr13, hk_hd, BinOp.eval, (by omega : 0 < 2 ^ w)]
          have hkNxt_lt : kNxt < 2 * eCap := by
            have hmem_c : cycNext (s.ord v) (endOfKey ku) ∈ s.ord v := by
              obtain ⟨idx, hidx, heq⟩ := List.getElem_of_mem hu_in.2.2
              rw [← heq, cycNext_eq_getElem (h.valid.ordWithin.1 v) hidx]; exact List.getElem_mem _
            exact key_lt_two_mul_of_endOfKey (by simpa [kNxt, endOfKey_endKey] using h.valid.ordWithin.2.2 v _ hmem_c)
          have hmN_ne : stN.mem (nodeOfEndBase b vCap + kNxt) = x.nodeOf kNxt := by
            rw [hfrN _ (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
              (fun hft => by have := hgeC _ hft; simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at this; omega),
              hfrC _ (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
                (not_inRecords_of_lt_nodesBase (by simp [nodeOfEndBase, nodesBase]; omega))
                (fun hft => by have := hordGe _ hft; simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at this; omega),
              hpre_mem _ (by simp [nodeOfEndBase, nodesBase]; omega)]
            exact (h.nodeOf_mem kNxt hkNxt_lt).1
          set r6 := Function.update r5 14 (x.nodeOf kNxt)
          have ha_ne := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 10) (rIdx := 14)
            (base := nodeOfEndBase b vCap) (idx := kNxt) (val := x.nodeOf kNxt) (st := { stN with regs := r5 })
            (by simp [r5, r4, r3, r2, r1, hr10]) (by simp [r5])
            (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) hmN_ne
          have hstW : Runs w p ω (.store (.bin .add (.reg 4) (.reg 12)) (.reg 14))
              { stN with regs := r6 } .normal { stN with mem := memN1, regs := r6 } 5 :=
            runs_store_iff.mpr ⟨nxtPtr + i, x.nodeOf kNxt,
              by simp [Expr.eval, r6, r5, r4, r3, r2, r1, hr4, hr12, BinOp.eval, (by omega : nxtPtr + i < 2 ^ w)],
              by simp [Expr.eval, r6], rfl, by congr 1; simp only [memN1, wVal, hk_hd, ↓reduceIte], rfl⟩
          exact ⟨r6, _, by simp [Expr.size], fun k hk => by simp [r6, hk],
            tour_runs_cond_false hc_f (tour_runs_seq_normal ha_ne hstW)⟩
      obtain ⟨r6, cB, hcB, hr6_oth, hrunB⟩ := hcond_branch
      set r7 := Function.update r6 12 (i + 1)
      have ha_inc : Runs w p ω (.assign 12 (.bin .add (.reg 12) (.const 1)))
          { stN with mem := memN1, regs := r6 } .normal { stN with mem := memN1, regs := r7 } 4 :=
        runs_assign_iff.mpr ⟨i + 1, by
          simp [Expr.eval, hr6_oth 12 (by decide), r5, r4, r3, r2, r1, hr12, BinOp.eval,
            (by omega : 1 < 2 ^ w), (by omega : i + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hbody := tour_runs_seq_normal ha_u (tour_runs_seq_normal ha_ku (tour_runs_seq_normal ha_out
        (tour_runs_seq_normal hcallN (tour_runs_seq_normal ha_kn (tour_runs_seq_normal hrunB ha_inc)))))
      have hfootN_sub : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordXN a →
          R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (hCur ≤ a ∧ a < oN.value) := fun a ha => by
        rcases hfootN a ha with h1 | ⟨h1, h2⟩
        · rcases hftC a h1 with h0 | ⟨h0a, h0b⟩; exact Or.inl h0; exact Or.inr ⟨h0a, by omega⟩
        · exact Or.inr ⟨by omega, h2⟩
      have hgeN : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordXN a → ordHandleOf b vCap eCap ≤ a := fun a ha => by
        rcases hfootN_sub a ha with h0 | ⟨h1, _⟩; exact hordGe a h0; omega
      have hOrdN1 := hOrdImpl.1 (ordHandleOf b vCap eCap) s.ord ordXN stN.mem memN1 fun a ha => by
        have hna : a ≠ nxtPtr + i := by
          rcases hfootN_sub a ha with h0 | ⟨h1, _⟩
          · have := hordFoot a h0; omega
          · omega
        dsimp only [memN1]; exact (Function.update_of_ne hna _ _).symm
      have hnN1 : tourLayout.NodesAt memN1 (nodesBase b vCap eCap) x.numNodes s1 :=
        NodesAt.congr tourLayout hnC fun a ha => by
          have hlt := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).2
          dsimp only [memN1]; rw [Function.update_of_ne (by omega)]
          exact hfrN a (by omega) (fun hft => by have := hgeC a hft; omega)
      obtain ⟨h', ordX', stF, c3, hrun3, hF6, hFge, hFle, hzF, hFAm, hFNm, hnF, hFfr, hFft, hFgeO, hFrep, hc3⟩ :=
        ih (i + 1) oN.value ordXN { stN with mem := memN1, regs := r7 } (by omega) (by omega) (by omega)
          (by dsimp only; rw [show r7 1 = r6 1 by simp [r7], hr6_oth 1 (by decide)]; simp [r5, r4, r3, r2, r1, hr1])
          (by dsimp only; rw [show r7 3 = r6 3 by simp [r7], hr6_oth 3 (by decide)]; simp [r5, r4, r3, r2, r1, hr3])
          (by dsimp only; rw [show r7 4 = r6 4 by simp [r7], hr6_oth 4 (by decide)]; simp [r5, r4, r3, r2, r1, hr4])
          (by dsimp only; rw [show r7 5 = r6 5 by simp [r7], hr6_oth 5 (by decide)]; simp [r5, r4, r3, r2, r1, hr5])
          (by dsimp only; rw [show r7 6 = r6 6 by simp [r7], hr6_oth 6 (by decide)]; simp [r5, r4])
          (by dsimp only; rw [show r7 9 = r6 9 by simp [r7], hr6_oth 9 (by decide)]; simp [r5, r4, r3, r2, r1, hr9])
          (by dsimp only; rw [show r7 10 = r6 10 by simp [r7], hr6_oth 10 (by decide)]; simp [r5, r4, r3, r2, r1, hr10])
          (by dsimp only; rw [show r7 11 = r6 11 by simp [r7], hr6_oth 11 (by decide)]; simp [r5, r4, r3, r2, r1, hr11])
          (by simp [r7])
          (by dsimp only; rw [show r7 13 = r6 13 by simp [r7], hr6_oth 13 (by decide)]; simp [r5, r4, r3, r2, r1, hr13])
          (fun a ha => by dsimp only [memN1]; rw [Function.update_of_ne (by omega)]; exact hzN a ha)
          (fun q hq => by
            dsimp only [memN1]; rw [Function.update_of_ne (by omega)]
            rw [hfrN _ (by omega) (fun hft => by rcases hftC _ hft with h0 | ⟨h1, _⟩; have := hordFoot _ h0; omega; omega)]
            exact hAm q hq)
          (fun q hq => by
            dsimp only [memN1]
            by_cases hqi : q = i
            · subst hqi; rw [Function.update_self]; exact hwVal_spec
            · rw [Function.update_of_ne (by omega),
                hfrN _ (by omega) (fun hft => by rcases hftC _ hft with h0 | ⟨h1, _⟩; have := hordFoot _ h0; omega; omega)]
              exact hNm q (by omega))
          hnN1
          (fun a ha hnr hnf => by
            dsimp only [memN1]; rw [Function.update_of_ne (by omega)]
            rw [hfrN a (by omega) (fun hft => by rcases hftC a hft with h0 | ⟨h1, _⟩; exact hnf h0; omega)]
            exact hfrC a ha hnr hnf)
          hfootN_sub hgeN (hOrdN1.1 (hpostN.1 ▸ hrepN))
      refine ⟨h', ordX', stF, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega, hbody, hrun3, rfl⟩)),
        hF6, hFge, hFle, hzF, hFAm, hFNm, hnF, hFfr, hFft, hFgeO, hFrep, ?_⟩
      rw [← hOrdN1.2] at hc3
      have hmul : (rem + 1) * (mul_ord * tourLog eCap + 70) = rem * (mul_ord * tourLog eCap + 70) + (mul_ord * tourLog eCap + 70) := by ring
      clear * - hcostN hc3 hcB hmul; simp only [Expr.size] at *; omega
  obtain ⟨h', ordX', stF, c3, hrun3, hF6, hFge, hFle, hzF, hFAm, hFNm, hnF, hFfr, hFft, hFgeO, hFrep, hc3⟩ :=
    hphase3 m 0 hCur x.ordX { stS with regs := rS2 } (by omega) (le_refl _) (by omega)
      (by simp [rS2, rS1, rS, h11]) (by simp [rS2, rS1, rS, h13]) (by simp [rS2, rS1, rS, h14])
      (by simp [rS2, rS1, rS, h15]) (by simp [rS2, rS1, rS, h16]) (by simp [rS2, rS1, rS, h19])
      (by simp [rS2, rS1, rS, h110]) (by simp [rS2, rS1, rS, h111]) (by simp [rS2]) (by simp [rS2, rS1])
      hzS hA_mem (fun _ hq => by omega) hnS (fun a ha hnr _ => hfrS_lo a ha hnr)
      (fun _ ha => Or.inl ha) hordGe (hOrdS.1 hordRep)
  have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := stF) (r := 6) (v := h') hF6
  have hrun_tail := tour_runs_seq_normal hcallS (tour_runs_seq_normal ha_fek (tour_runs_seq_normal ha_i0 (tour_runs_seq_normal hrun3 hret)))
  have hrun_mid := tour_runs_seq_normal ha11 (tour_runs_seq_normal ha12 (tour_runs_seq_normal hrun1 hrun_tail))
  have hrun_all_0 : Runs w p ω (tourMoveRankSortNextBody rankProc sortProc ordOp2)
      (startState [b, v, feV, pairsPtr, nxtPtr, m, hCur] mem pos) (.returned h') stF _ :=
    tour_runs_seq_normal ha7 (tour_runs_seq_normal ha8 (tour_runs_seq_normal ha9 (tour_runs_seq_normal ha10 hrun_mid)))
  have hrun_all : ∃ cAll, cAll ≤ c1 + cS + c3 + 60 ∧
      Runs w p ω (tourMoveRankSortNextBody rankProc sortProc ordOp2)
        (startState [b, v, feV, pairsPtr, nxtPtr, m, hCur] mem pos) (.returned h') stF cAll :=
    ⟨_, by clear * -; omega, hrun_all_0⟩
  obtain ⟨cAll, hcAll, hrun_all⟩ := hrun_all
  have hcost_all : cAll + TOUR_PHI_MULT * forestPhi (t1 :: rest) + R_ord.phi (ordHandleOf b vCap eCap) ordX' stF.mem ≤
      TOUR_PHI_MULT * forestPhi (t :: rest) + R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem +
        (m + 1) * (TOUR_MOVE_SORT_MUL + mul_ord) * tourLog eCap := by
    rw [← hOrdS.2] at hc3
    have hlog_m : Nat.log 2 (m + 2) + 1 ≤ 2 * tourLog eCap :=
      le_trans (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1) hlog
    have hcS' : cS ≤ (m + 1) * (2 * ORD_SORT_COST_MUL) * tourLog eCap := by
      clear * - hcS hlog_m htl
      have h1 : m * (Nat.log 2 (m + 2) + 1) + 1 ≤ (m + 1) * (2 * tourLog eCap) := by
        have h0 := Nat.mul_le_mul_left m hlog_m
        have : m * (2 * tourLog eCap) + 1 ≤ (m + 1) * (2 * tourLog eCap) := by
          rw [Nat.add_mul, Nat.one_mul]; omega
        omega
      have h2 := Nat.mul_le_mul_left ORD_SORT_COST_MUL h1
      calc cS ≤ ORD_SORT_COST_MUL * (m * (Nat.log 2 (m + 2) + 1) + 1) := by omega
        _ ≤ ORD_SORT_COST_MUL * ((m + 1) * (2 * tourLog eCap)) := h2
        _ = (m + 1) * (2 * ORD_SORT_COST_MUL) * tourLog eCap := by ring
    have hc1_le : m * (TOUR_FIND_AMORT + 40) * (Nat.log 2 (x.numNodes + 2) + 1) ≤
        (m + 1) * (2 * TOUR_FIND_AMORT + 80) * tourLog eCap := by
      have h1 := Nat.mul_le_mul_left (m * (TOUR_FIND_AMORT + 40)) (tourLog_of_le h.numNodes_le)
      calc m * (TOUR_FIND_AMORT + 40) * (Nat.log 2 (x.numNodes + 2) + 1)
          ≤ m * (TOUR_FIND_AMORT + 40) * (2 * tourLog eCap) := h1
        _ = m * (2 * TOUR_FIND_AMORT + 80) * tourLog eCap := by ring
        _ ≤ (m + 1) * (2 * TOUR_FIND_AMORT + 80) * tourLog eCap :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have hc3_le : m * (mul_ord * tourLog eCap + 70) ≤ (m + 1) * (mul_ord + 70) * tourLog eCap := by
      have h1 : mul_ord * tourLog eCap + 70 ≤ (mul_ord + 70) * tourLog eCap := by
        rw [Nat.add_mul]; have : 70 ≤ 70 * tourLog eCap := Nat.le_mul_of_pos_right 70 htl; omega
      calc m * (mul_ord * tourLog eCap + 70)
          ≤ m * ((mul_ord + 70) * tourLog eCap) := Nat.mul_le_mul_left m h1
        _ = m * (mul_ord + 70) * tourLog eCap := by ring
        _ ≤ (m + 1) * (mul_ord + 70) * tourLog eCap :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have h100 : 100 ≤ (m + 1) * 100 * tourLog eCap := by
      have h1 : 1 ≤ (m + 1) * tourLog eCap := Nat.mul_pos (by omega) htl
      calc 100 = 100 * 1 := by ring
        _ ≤ 100 * ((m + 1) * tourLog eCap) := Nat.mul_le_mul_left 100 h1
        _ = (m + 1) * 100 * tourLog eCap := by ring
    have htot := moveSort_mul_split m mul_ord (tourLog eCap)
    clear * - hcAll hc1 hcS' hc3 hc1_le hc3_le h100 htot
    omega
  exact ⟨h', t1, s1, ordX', stF, cAll, A, hrun_all,
    hFge, hFle, hzF, hA_perm, hA_len, hA_nd, hA_pw, fun i hi => hFAm i (by omega), fun i hi => hFNm i (by omega),
    hnF, hinv1, hvals1, ht1, hval1,
    hFfr, hFft, hFgeO, hFrep, hcost_all⟩

end MinCostFlow.SparseCore.Program
