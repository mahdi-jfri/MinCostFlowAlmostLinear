module

public import MinCostFlow.SparseCore.Program.TourInitStage1Inner
import Mathlib.Tactic

/-!
# Stage 1 Outer Loop (`tourInitOuter_runs`)

Verifies `tourInitOuterLoop`, scanning all order records of `readOrdRecordsAt` and invoking
`tourInitInner_runs` on each nonempty vertex record.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.DynSpanner.Program
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

theorem tourInitOuter_runs {w vCap eCap ordPtr rsPtr b hOut : ℕ} {p : Program}
    (C : TourSplayOpsProcs w p) (ω : ℕ → Bool) {mem memO : ℕ → ℕ}
    (hOrdAt : OrdListAt mem ordPtr (readOrd mem ordPtr) (1 + ordRecordsWords (readOrdRecordsAt mem ordPtr)))
    (hOrdLe : ordPtr + (1 + ordRecordsWords (readOrdRecordsAt mem ordPtr)) ≤ b)
    (hvalid0 : TourValid vCap eCap (tourInitStage1Abs (readOrdRecordsAt mem ordPtr) (readNatList mem rsPtr)))
    (hord_le : ordHandleOf b vCap eCap ≤ hOut) (hroom_hOut : hOut + 2 < 2 ^ w)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w)
    (hmemO_lt_b : ∀ a < b, memO a = mem a)
    (hrecs_sum_le : ((readOrdRecordsAt mem ordPtr).map fun p => p.2.length).sum ≤ 2 * eCap) :
    open Classical in
    let recs := readOrdRecordsAt mem ordPtr
    let rs := readNatList mem rsPtr
    let s0 := tourInitStage1Abs recs rs
    ∀ (rem idx curPtr nnC : ℕ) (sC : SplayState TourVal TourSum Unit)
      (treesC : List AuxTree) (noC koC : ℕ → ℕ) (ctC : ℕ → Option AuxTree) (stC : State),
      idx + rem = mem ordPtr →
      let done := recs.take idx
      let todo := readOrdRecords mem rem curPtr
      recs = done ++ todo →
      curPtr + ordRecordsWords todo ≤ b →
      nnC = (done.map fun p => p.2.length).sum →
      stC.regs 0 = vCap → stC.regs 1 = eCap → stC.regs 2 = ordPtr → stC.regs 3 = rsPtr →
      stC.regs 4 = b → stC.regs 5 = firstEndBase b → stC.regs 6 = isRootBase b vCap →
      stC.regs 7 = nodeOfEndBase b vCap → stC.regs 8 = endOwnerBase b vCap eCap →
      stC.regs 9 = keyOfNodeBase b vCap eCap → stC.regs 10 = nodesBase b vCap eCap →
      stC.regs 12 = 2 * eCap + 2 → stC.regs 13 = hOut →
      stC.regs 14 = mem ordPtr → stC.regs 15 = curPtr → stC.regs 16 = nnC → stC.regs 17 = idx →
      tourLayout.NodesAt stC.mem (nodesBase b vCap eCap) nnC sC →
      TourForestInv nnC sC treesC → TourValsOk w nnC sC → ZeroFrom stC.mem hOut →
      (∀ u, u ∈ treesC.flatMap AuxTree.toList ↔ 1 ≤ u ∧ u ≤ nnC) →
      (∀ k < 2 * eCap, stC.mem (nodeOfEndBase b vCap + k) = noC k ∧ noC k ≤ nnC) →
      (∀ k, (∀ p ∈ done, ∀ z ∈ p.2, k ≠ endKey z) → noC k = 0) →
      (∀ p ∈ done, ∀ z ∈ p.2, noC (endKey z) ≠ 0 ∧ stC.mem (endOwnerBase b vCap eCap + endKey z) = p.1 + 1) →
      (∀ k < 2 * eCap, (∀ p ∈ done, ∀ z ∈ p.2, endOfKey k ≠ z) → stC.mem (endOwnerBase b vCap eCap + k) = 0) →
      (∀ u, 1 ≤ u → u ≤ nnC →
        stC.mem (keyOfNodeBase b vCap eCap + u) = koC u ∧ koC u < 2 * eCap ∧ noC (koC u) = u) →
      (∀ k < 2 * eCap, noC k ≠ 0 → koC (noC k) = k) →
      (∀ v < vCap, stC.mem (firstEndBase b + v) =
        if ∃ xs, (v, xs) ∈ done ∧ xs ≠ [] then
          match (s0.ord v).head? with | none => 0 | some e => noC (endKey e)
        else 0) →
      (∀ v < vCap, stC.mem (isRootBase b vCap + v) =
        if ∃ xs, (v, xs) ∈ done ∧ xs ≠ [] then 1 else 0) →
      (∀ v, (∃ xs, (v, xs) ∈ done ∧ xs ≠ []) →
        ∃ t, ctC v = some t ∧ t ∈ treesC ∧ t.toList.map (fun u => endOfKey (koC u)) = s0.ord v) →
      (∀ v, (∀ xs, (v, xs) ∈ done → xs = []) → ctC v = none) →
      (∀ t ∈ treesC, ∃ v, (∃ xs, (v, xs) ∈ done ∧ xs ≠ []) ∧ ctC v = some t) →
      (∀ u, 1 ≤ u → u ≤ nnC →
        (sC.nodes u).val = ⟨true, false, tourRootTagVal s0 (endOfKey (koC u))⟩) →
      (sC.nodes 0).val.rootTag = 0 →
      (∀ a, a < b ∨ (ordHandleOf b vCap eCap ≤ a ∧ a < hOut) → stC.mem a = memO a) →
      (∀ a, b ≤ a → a < b + 16 → stC.mem a = memO a) →
      (∀ a, markArrBase b vCap eCap ≤ a → a < nodesBase b vCap eCap → stC.mem a = 0) →
      ∃ (nnF : ℕ) (sF : SplayState TourVal TourSum Unit) (treesF : List AuxTree)
        (noF koF : ℕ → ℕ) (ctF : ℕ → Option AuxTree) (stF : State) (cF : ℕ),
        Runs w p ω (tourInitOuterLoop C.initNode C.join) stC .normal stF cF ∧
        nnF = (recs.map fun p => p.2.length).sum ∧
        stF.regs 3 = rsPtr ∧ stF.regs 4 = b ∧ stF.regs 6 = isRootBase b vCap ∧
        stF.regs 13 = hOut ∧ stF.regs 16 = nnF ∧
        tourLayout.NodesAt stF.mem (nodesBase b vCap eCap) nnF sF ∧
        TourForestInv nnF sF treesF ∧ ZeroFrom stF.mem hOut ∧
        (∀ u, u ∈ treesF.flatMap AuxTree.toList ↔ 1 ≤ u ∧ u ≤ nnF) ∧
        (∀ k < 2 * eCap, stF.mem (nodeOfEndBase b vCap + k) = noF k ∧ noF k ≤ nnF) ∧
        (∀ p ∈ recs, ∀ z ∈ p.2, noF (endKey z) ≠ 0 ∧ stF.mem (endOwnerBase b vCap eCap + endKey z) = p.1 + 1) ∧
        (∀ k < 2 * eCap, (∀ p ∈ recs, ∀ z ∈ p.2, endOfKey k ≠ z) → stF.mem (endOwnerBase b vCap eCap + k) = 0) ∧
        (∀ u, 1 ≤ u → u ≤ nnF →
          stF.mem (keyOfNodeBase b vCap eCap + u) = koF u ∧ koF u < 2 * eCap ∧ noF (koF u) = u) ∧
        (∀ k < 2 * eCap, noF k ≠ 0 → koF (noF k) = k) ∧
        (∀ v < vCap, stF.mem (firstEndBase b + v) =
          match (s0.ord v).head? with | none => 0 | some e => noF (endKey e)) ∧
        (∀ v < vCap, stF.mem (isRootBase b vCap + v) =
          if ∃ xs, (v, xs) ∈ recs ∧ xs ≠ [] then 1 else 0) ∧
        (∀ v, (∃ xs, (v, xs) ∈ recs ∧ xs ≠ []) →
          ∃ t, ctF v = some t ∧ t ∈ treesF ∧ t.toList.map (fun u => endOfKey (koF u)) = s0.ord v) ∧
        (∀ v, (∀ xs, (v, xs) ∈ recs → xs = []) → ctF v = none) ∧
        (∀ t ∈ treesF, ∃ v, (∃ xs, (v, xs) ∈ recs ∧ xs ≠ []) ∧ ctF v = some t) ∧
        (∀ u, 1 ≤ u → u ≤ nnF →
          (sF.nodes u).val = ⟨true, false, tourRootTagVal s0 (endOfKey (koF u))⟩) ∧
        (sF.nodes 0).val.rootTag = 0 ∧
        (∀ a, a < b ∨ (ordHandleOf b vCap eCap ≤ a ∧ a < hOut) → stF.mem a = memO a) ∧
        (∀ a, b ≤ a → a < b + 16 → stF.mem a = memO a) ∧
        (∀ a, markArrBase b vCap eCap ≤ a → a < nodesBase b vCap eCap → stF.mem a = 0) ∧
        cF + TOUR_PHI_MULT * forestPhi treesF ≤
          TOUR_PHI_MULT * forestPhi treesC +
            ordRecordsWords todo * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) + 20 := by
  classical
  intro recs rs s0
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hlen_le_words : ∀ (l : List (ℕ × List End)), l.length ≤ ordRecordsWords l := fun l => by
    induction l with
    | nil => simp [ordRecordsWords]
    | cons _ t ih => simp [ordRecordsWords]; omega
  have hrecs_nd : (recs.map Prod.fst).Nodup := hOrdAt.1
  have hrecs_ord : ∀ p ∈ recs, s0.ord p.1 = p.2 := fun p hp => ordOfRecords_mem_iff hrecs_nd hp
  intro rem
  induction rem with
  | zero =>
    intro idx curPtr nnC sC treesC noC koC ctC stC hidx done todo hrecs_eq _ hnnC
      hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr12 hr13 hr14 hr15 hr16 hr17
      hnC hinvC hvalsC hzC hexC hnoC hno_fr hactC hinactC hkoC hnkC hfeC hirC
      hct_s hct_n ht_cls hvalC hval0 hfr_out hfr_hdr hfr_mk
    have hidx_eq : idx = mem ordPtr := by omega
    have hdone_eq : done = recs := by simpa [done, todo, readOrdRecords] using hrecs_eq.symm
    have hcond : (Expr.bin .lt (.reg 17) (.reg 14)).eval w stC = some 0 := by
      simp [Expr.eval, hr17, hr14, hidx_eq, BinOp.eval, (by omega : 0 < 2 ^ w)]
    refine ⟨nnC, sC, treesC, noC, koC, ctC, stC, _, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
      by rw [hnnC, hdone_eq], hr3, hr4, hr6, hr13, hr16, hnC, hinvC, hzC, hexC, hnoC,
      by rwa [hdone_eq] at hactC, by rwa [hdone_eq] at hinactC, hkoC, hnkC,
      fun v hv => by
        rw [hfeC v hv, hdone_eq]
        by_cases hex : ∃ xs, (v, xs) ∈ recs ∧ xs ≠ []
        · simp [hex]
        · simp only [hex, ↓reduceIte]
          have hnil : s0.ord v = [] := by
            by_cases hm : ∃ xs, (v, xs) ∈ recs
            · obtain ⟨xs, hxs⟩ := hm
              have hxs0 : xs = [] := by by_contra hne; exact hex ⟨xs, hxs, hne⟩
              rw [hrecs_ord (v, xs) hxs, hxs0]
            · exact ordOfRecords_eq_nil_of_not_mem fun xs hxs => hm ⟨xs, hxs⟩
          simp [hnil],
      by rwa [hdone_eq] at hirC, by rwa [hdone_eq] at hct_s, by rwa [hdone_eq] at hct_n,
      by rwa [hdone_eq] at ht_cls, hvalC, hval0, hfr_out, hfr_hdr, hfr_mk, by simp [Expr.size]; omega⟩
  | succ rem ih =>
    intro idx curPtr nnC sC treesC noC koC ctC stC hidx done todo hrecs_eq hcur_le hnnC
      hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10 hr12 hr13 hr14 hr15 hr16 hr17
      hnC hinvC hvalsC hzC hexC hnoC hno_fr hactC hinactC hkoC hnkC hfeC hirC
      hct_s hct_n ht_cls hvalC hval0 hfr_out hfr_hdr hfr_mk
    have hidx_lt : idx < mem ordPtr := by omega
    set v := mem curPtr
    set len := mem (curPtr + 1)
    set xs := (readList mem (curPtr + 2) len).map endOfKey
    have htodo_eq : todo = (v, xs) :: readOrdRecords mem rem (curPtr + 2 + len) := rfl
    have hwords_eq : ordRecordsWords todo = 2 + len + ordRecordsWords (readOrdRecords mem rem (curPtr + 2 + len)) := by
      simp [htodo_eq, ordRecordsWords, xs, readList_length, Nat.add_assoc]
    have hdone_succ : recs.take (idx + 1) = done ++ [(v, xs)] := by
      have hlen_done : done.length = idx := by
        have : recs.length = mem ordPtr := readOrdRecords_length mem (mem ordPtr) (ordPtr + 1)
        simp [done, List.length_take]; omega
      conv_lhs => rw [hrecs_eq, htodo_eq]
      rw [List.take_append, hlen_done, List.take_of_length_le (by omega), show idx + 1 - idx = 1 from by omega]
      rfl
    have hv_in_recs : (v, xs) ∈ recs := by rw [hrecs_eq, htodo_eq]; simp
    have hv_not_done : ∀ ys, (v, ys) ∉ done := fun ys hys => by
      have hnd' := hrecs_nd; rw [hrecs_eq, htodo_eq, List.map_append, List.map_cons, List.nodup_append] at hnd'
      exact hnd'.2.2 v (List.mem_map.mpr ⟨(v, ys), hys, rfl⟩) v List.mem_cons_self rfl
    have hcond : (Expr.bin .lt (.reg 17) (.reg 14)).eval w stC = some 1 := by
      simp [Expr.eval, hr17, hr14, hidx_lt, BinOp.eval, (by omega : 1 < 2 ^ w)]
    have hm_v : stC.mem curPtr = v := (hfr_out curPtr (Or.inl (by omega))).trans (hmemO_lt_b curPtr (by omega))
    have hm_len : stC.mem (curPtr + 1) = len := (hfr_out (curPtr + 1) (Or.inl (by omega))).trans (hmemO_lt_b (curPtr + 1) (by omega))
    set r1 := Function.update stC.regs 18 v
    set r2 := Function.update r1 19 len
    set r3 := Function.update r2 15 (curPtr + 2)
    have ha18 : Runs w p ω (.assign 18 (.load (.reg 15))) stC .normal { stC with regs := r1 } 3 :=
      runs_assign_iff.mpr ⟨v, by simp [Expr.eval, hr15, hm_v], rfl, rfl, rfl⟩
    have ha19 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 19) (rBase := 15) (off := 1)
      (b := curPtr) (val := len) (st := { stC with regs := r1 }) (by simp [r1, hr15]) (by omega)
      (by simp [ordHandleOf, tourFixedSize] at hord_le; omega) hm_len
    have ha15a : Runs w p ω (.assign 15 (.bin .add (.reg 15) (.const 2))) { stC with regs := r2 } .normal { stC with regs := r3 } 4 :=
      runs_assign_iff.mpr ⟨curPtr + 2, by simp [Expr.eval, r2, r1, hr15, BinOp.eval, (by omega : 2 < 2 ^ w), (by simp [ordHandleOf, tourFixedSize] at hord_le; omega : curPtr + 2 < 2 ^ w)], rfl, rfl, rfl⟩
    -- Branch on `len = 0` vs `len ≠ 0`
    have hmid : ∃ (nn1 : ℕ) (s1 : SplayState TourVal TourSum Unit) (trees1 : List AuxTree)
        (no1 ko1 : ℕ → ℕ) (ct1 : ℕ → Option AuxTree) (stM : State) (cM : ℕ),
        Runs w p ω (.cond (.reg 19)
          (.store (.bin .add (.reg 6) (.reg 18)) (.const 1) ;;
           .assign 20 (.const 0) ;; .assign 21 (.const 0) ;;
           tourInitInnerLoop C.initNode C.join) .nop)
          { stC with regs := r3 } .normal stM cM ∧
        nn1 = nnC + len ∧
        (∀ k < 20, k ≠ 16 → stM.regs k = r3 k) ∧ stM.regs 16 = nn1 ∧
        tourLayout.NodesAt stM.mem (nodesBase b vCap eCap) nn1 s1 ∧
        TourForestInv nn1 s1 trees1 ∧ TourValsOk w nn1 s1 ∧ ZeroFrom stM.mem hOut ∧
        (∀ u, u ∈ trees1.flatMap AuxTree.toList ↔ 1 ≤ u ∧ u ≤ nn1) ∧
        (∀ k < 2 * eCap, stM.mem (nodeOfEndBase b vCap + k) = no1 k ∧ no1 k ≤ nn1) ∧
        (∀ k, (∀ p ∈ recs.take (idx + 1), ∀ z ∈ p.2, k ≠ endKey z) → no1 k = 0) ∧
        (∀ p ∈ recs.take (idx + 1), ∀ z ∈ p.2, no1 (endKey z) ≠ 0 ∧ stM.mem (endOwnerBase b vCap eCap + endKey z) = p.1 + 1) ∧
        (∀ k < 2 * eCap, (∀ p ∈ recs.take (idx + 1), ∀ z ∈ p.2, endOfKey k ≠ z) → stM.mem (endOwnerBase b vCap eCap + k) = 0) ∧
        (∀ u, 1 ≤ u → u ≤ nn1 →
          stM.mem (keyOfNodeBase b vCap eCap + u) = ko1 u ∧ ko1 u < 2 * eCap ∧ no1 (ko1 u) = u) ∧
        (∀ k < 2 * eCap, no1 k ≠ 0 → ko1 (no1 k) = k) ∧
        (∀ v' < vCap, stM.mem (firstEndBase b + v') =
          if ∃ ys, (v', ys) ∈ recs.take (idx + 1) ∧ ys ≠ [] then
            match (s0.ord v').head? with | none => 0 | some e => no1 (endKey e)
          else 0) ∧
        (∀ v' < vCap, stM.mem (isRootBase b vCap + v') =
          if ∃ ys, (v', ys) ∈ recs.take (idx + 1) ∧ ys ≠ [] then 1 else 0) ∧
        (∀ v', (∃ ys, (v', ys) ∈ recs.take (idx + 1) ∧ ys ≠ []) →
          ∃ t, ct1 v' = some t ∧ t ∈ trees1 ∧ t.toList.map (fun u => endOfKey (ko1 u)) = s0.ord v') ∧
        (∀ v', (∀ ys, (v', ys) ∈ recs.take (idx + 1) → ys = []) → ct1 v' = none) ∧
        (∀ t ∈ trees1, ∃ v', (∃ ys, (v', ys) ∈ recs.take (idx + 1) ∧ ys ≠ []) ∧ ct1 v' = some t) ∧
        (∀ u, 1 ≤ u → u ≤ nn1 →
          (s1.nodes u).val = ⟨true, false, tourRootTagVal s0 (endOfKey (ko1 u))⟩) ∧
        (s1.nodes 0).val.rootTag = 0 ∧
        (∀ a, a < b ∨ (ordHandleOf b vCap eCap ≤ a ∧ a < hOut) → stM.mem a = memO a) ∧
        (∀ a, b ≤ a → a < b + 16 → stM.mem a = memO a) ∧
        (∀ a, markArrBase b vCap eCap ≤ a → a < nodesBase b vCap eCap → stM.mem a = 0) ∧
        cM + TOUR_PHI_MULT * forestPhi trees1 ≤
          TOUR_PHI_MULT * forestPhi treesC +
            (2 + len) * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) - 30 := by
      by_cases hlen0 : len = 0
      · have hxs0 : xs = [] := by simp [xs, hlen0, readList]
        have hc0 : (Expr.reg 19).eval w { stC with regs := r3 } = some 0 := by simp [Expr.eval, r3, r2, hlen0]
        have hmem_ne : ∀ v', (∃ ys, (v', ys) ∈ recs.take (idx + 1) ∧ ys ≠ []) ↔ ∃ ys, (v', ys) ∈ done ∧ ys ≠ [] := by
          intro v'; rw [hdone_succ]; constructor
          · rintro ⟨ys, hm, hne⟩
            simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hm
            rcases hm with h | ⟨_, rfl⟩
            · exact ⟨ys, h, hne⟩
            · exact absurd hxs0 hne
          · rintro ⟨ys, hm, hne⟩; exact ⟨ys, List.mem_append_left _ hm, hne⟩
        have hmem_all : ∀ v', (∀ ys, (v', ys) ∈ recs.take (idx + 1) → ys = []) ↔ ∀ ys, (v', ys) ∈ done → ys = [] := by
          intro v'; rw [hdone_succ]; constructor
          · intro h ys hys; exact h ys (List.mem_append_left _ hys)
          · intro h ys hys
            simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hys
            rcases hys with hm | ⟨_, rfl⟩
            · exact h ys hm
            · exact hxs0
        refine ⟨nnC, sC, treesC, noC, koC, ctC, { stC with regs := r3 }, _,
          tour_runs_cond_false hc0 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
          by omega, fun _ _ _ => rfl, by simp [r3, r2, r1, hr16],
          hnC, hinvC, hvalsC, hzC, hexC, hnoC,
          fun k hk => hno_fr k fun p hp => hk p (by rw [hdone_succ]; exact List.mem_append_left _ hp),
          fun p hp z hz => by
            rw [hdone_succ, List.mem_append, List.mem_singleton] at hp
            rcases hp with hp | rfl; exact hactC p hp z hz; simp [hxs0] at hz,
          fun k hk hno => hinactC k hk fun p hp => hno p (by rw [hdone_succ]; exact List.mem_append_left _ hp),
          hkoC, hnkC,
          fun v' hv' => by simp only [hmem_ne]; exact hfeC v' hv',
          fun v' hv' => by simp only [hmem_ne]; exact hirC v' hv',
          fun v' hv' => hct_s v' ((hmem_ne v').mp hv'),
          fun v' hv' => hct_n v' ((hmem_all v').mp hv'),
          fun t ht => let ⟨v', hv', hct⟩ := ht_cls t ht; ⟨v', (hmem_ne v').mpr hv', hct⟩,
          hvalC, hval0, hfr_out, hfr_hdr, hfr_mk, ?_⟩
        have : 30 + 10 ≤ (2 + len) * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) := by
          have : 1 ≤ (2 + len) * (2 * tourLog eCap) := Nat.mul_pos (by omega) (by omega)
          calc 30 + 10 ≤ 40 * ((2 + len) * (2 * tourLog eCap)) := by omega
            _ = (2 + len) * 40 * (2 * tourLog eCap) := by ring
            _ ≤ (2 + len) * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by unfold TOUR_JOIN_AMORT; omega))
        clear * - this; simp only [Expr.size]; omega
      · have hxs_len : xs.length = len := by simp [xs, readList_length]
        have hxs_ne : xs ≠ [] := by intro h0; rw [h0] at hxs_len; simp at hxs_len; omega
        have hord_v : s0.ord v = xs := hrecs_ord (v, xs) hv_in_recs
        have hvLt : v < vCap := by
          by_contra hge; have := hvalid0.ordWithin.2.1 v (Nat.le_of_not_lt hge); rw [hord_v] at this; exact hxs_ne this
        have hxs_nd : xs.Nodup := hord_v ▸ hvalid0.ordWithin.1 v
        have hxs_lt : ∀ z ∈ xs, z.1 < eCap := fun z hz => hvalid0.ordWithin.2.2 v z (hord_v ▸ hz)
        have hxs_fresh : ∀ z ∈ xs, noC (endKey z) = 0 := fun z hz =>
          hno_fr (endKey z) fun p hp z' hz' heq => by
            have hzz' : z = z' := by simpa [endOfKey_endKey] using congrArg endOfKey heq
            have hp_in : p ∈ recs := by rw [hrecs_eq]; exact List.mem_append_left _ hp
            have hv_eq : v = p.1 := hvalid0.compat.unique v p.1 z (hord_v ▸ hz) (hzz' ▸ (hrecs_ord p hp_in).symm ▸ hz')
            exact hv_not_done p.2 (by rcases p with ⟨p1, p2⟩; subst hv_eq; exact hp)
        have hnn_end : nnC + xs.length ≤ 2 * eCap := by
          have h1 : (done.map fun p => p.2.length).sum + xs.length ≤ (recs.map fun p => p.2.length).sum := by
            rw [hrecs_eq, htodo_eq]
            simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
            omega
          dsimp only [recs] at h1
          omega
        have hc1 : (Expr.reg 19).eval w { stC with regs := r3 } = some len := by simp [Expr.eval, r3, r2]
        set mIr := Function.update stC.mem (isRootBase b vCap + v) 1
        set r4 := Function.update r3 20 0
        set r5 := Function.update r4 21 0
        have hst_ir : Runs w p ω (.store (.bin .add (.reg 6) (.reg 18)) (.const 1))
            { stC with regs := r3 } .normal { stC with mem := mIr, regs := r3 } 5 :=
          runs_store_iff.mpr ⟨isRootBase b vCap + v, 1,
            by simp [Expr.eval, r3, r2, r1, hr6, BinOp.eval, (by simp [isRootBase, ordHandleOf, tourFixedSize] at hroom_hOut hord_le ⊢; omega : isRootBase b vCap + v < 2 ^ w)],
            by simp [Expr.eval, (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
        have ha20 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 20) (val := 0) (st := { stC with mem := mIr, regs := r3 }) (by omega)
        have ha21 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 21) (val := 0) (st := { stC with mem := mIr, regs := r4 }) (by omega)
        have hmIr_ne : ∀ a, a ≠ isRootBase b vCap + v → mIr a = stC.mem a := fun a ha => Function.update_of_ne ha _ _
        have hnIr : tourLayout.NodesAt mIr (nodesBase b vCap eCap) nnC sC :=
          NodesAt.congr tourLayout hnC fun a ha =>
            hmIr_ne a (by have := (inRecords_lt_ordHandle_of_le (by omega : nnC ≤ 2 * eCap) ha).1; simp [isRootBase, nodesBase] at this ⊢; omega)
        obtain ⟨tV, s1, no1, ko1, stI, cI, hrunI, hrI_lt, hrI16, hn1, hinv1, hvals1, hz1,
          htV_mem, htV_map, hno1_fr, hno1_z, hko1_old, hno1_mem, hko1_mem, hnk1, hfeI, heoI,
          hval1_old, hval1_new, hfrI, hcI⟩ :=
          tourInitInner_runs (v := v) (keysPtr := curPtr + 2) (hOut := hOut) (nn0 := nnC) (xs := xs)
            (st0 := { stC with mem := mIr, regs := r5 }) C ω hvLt hxs_ne hxs_nd hxs_lt hxs_fresh
            (fun j hj => by
              dsimp only
              rw [hmIr_ne _ (by simp [isRootBase]; omega),
                hfr_out _ (Or.inl (by omega)), hmemO_lt_b _ (by omega)]
              simp [xs, readList_getElem, endKey_endOfKey, Nat.add_assoc])
            (by omega) hnn_end
            (fun k hk => by dsimp only; rw [hmIr_ne _ (by simp [nodeOfEndBase, isRootBase]; omega)]; exact hnoC k hk)
            (fun u h1 h2 => by dsimp only; rw [hmIr_ne _ (by simp [keyOfNodeBase, isRootBase]; omega)]; exact hkoC u h1 h2)
            hnkC hnIr hinvC hvalsC hord_le hroom_hOut hw hwide
            (fun a ha => by dsimp only; rw [hmIr_ne a (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]; exact hzC a ha)
            (by simp [r5, r4, r3, r2, r1, hr5]) (by simp [r5, r4, r3, r2, r1, hr7])
            (by simp [r5, r4, r3, r2, r1, hr8]) (by simp [r5, r4, r3, r2, r1, hr9])
            (by simp [r5, r4, r3, r2, r1, hr10]) (by simp [r5, r4, r3, r2, r1, hr12])
            (by simp [r5, r4, r3, r2, r1, hr13]) (by simp [r5, r4, r3])
            (by simp [r5, r4, r3, r2, r1, hr16]) (by simp [r5, r4, r3, r2, r1])
            (by simp [r5, r4, r3, r2, hxs_len]) (by simp [r5, r4]) (by simp [r5])
        have hv_in_V : v ∈ s0.rf.R := by
          simp only [s0, tourInitStage1Abs, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter]
          exact Or.inl ⟨(v, xs), ⟨hv_in_recs, by cases hxs_c : xs with | nil => exact absurd hxs_c hxs_ne | cons _ _ => rfl⟩, rfl⟩
        refine ⟨nnC + xs.length, s1, tV :: treesC, no1, ko1, Function.update ctC v (some tV), stI, _,
          tour_runs_cond_true hc1 hlen0 (tour_runs_seq_normal hst_ir (tour_runs_seq_normal ha20 (tour_runs_seq_normal ha21 hrunI))),
          by omega,
          fun k hk hk16 => by rw [hrI_lt k hk hk16]; simp [r5, r4, Function.update_of_ne (by omega : k ≠ 21), Function.update_of_ne (by omega : k ≠ 20)],
          hrI16, hn1, hinv1, hvals1, hz1,
          fun u => by simp only [List.flatMap_cons, List.mem_append, htV_mem, hexC]; omega,
          hno1_mem,
          fun k hk => by
            rw [hno1_fr k (fun z hz => hk (v, xs) (by rw [hdone_succ]; simp) z hz)]
            exact hno_fr k fun p hp => hk p (by rw [hdone_succ]; exact List.mem_append_left _ hp),
          fun p hp z hz => by
            rw [hdone_succ, List.mem_append, List.mem_singleton] at hp
            rcases hp with hp | rfl
            · have hz_not_xs : z ∉ xs := fun hzx => by
                have hp_in : p ∈ recs := by rw [hrecs_eq]; exact List.mem_append_left _ hp
                have hvp : v = p.1 := hvalid0.compat.unique v p.1 z (hord_v ▸ hzx) ((hrecs_ord p hp_in).symm ▸ hz)
                exact hv_not_done p.2 (by rcases p with ⟨p1, p2⟩; subst hvp; exact hp)
              have hne_xs : ∀ z' ∈ xs, endKey z ≠ endKey z' := fun z' hz' heq =>
                hz_not_xs ((by simpa [endOfKey_endKey] using congrArg endOfKey heq : z = z') ▸ hz')
              have hkz_lt : endKey z < 2 * eCap :=
                endKey_lt_two_mul (hvalid0.ordWithin.2.2 p.1 z ((hrecs_ord p (by rw [hrecs_eq]; exact List.mem_append_left _ hp)).symm ▸ hz))
              rw [hno1_fr _ hne_xs,
                hfrI _ (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
                  (by simp [endOwnerBase, firstEndBase]; omega)
                  (fun z' hz' => by have := endKey_lt_two_mul (hxs_lt z' hz'); simp [endOwnerBase, nodeOfEndBase]; omega)
                  (fun z' hz' => by have := hne_xs z' hz'; omega) (fun _ _ _ => by simp [endOwnerBase, keyOfNodeBase]; omega)
                  (not_inRecords_of_lt_nodesBase (by simp [endOwnerBase, nodesBase]; omega))]
              dsimp only
              rw [hmIr_ne _ (by simp [endOwnerBase, isRootBase]; omega)]
              exact hactC p hp z hz
            · exact ⟨by rw [hno1_z z hz]; omega, heoI z hz⟩,
          fun k hk hno => by
            have hne_xs : ∀ z' ∈ xs, k ≠ endKey z' := fun z' hz' heq =>
              hno (v, xs) (by rw [hdone_succ]; simp) z' hz' (by rw [heq, endOfKey_endKey])
            rw [hfrI _ (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
              (by simp [endOwnerBase, firstEndBase]; omega)
              (fun z' hz' => by have := endKey_lt_two_mul (hxs_lt z' hz'); simp [endOwnerBase, nodeOfEndBase]; omega)
              (fun z' hz' => by have := hne_xs z' hz'; omega) (fun _ _ _ => by simp [endOwnerBase, keyOfNodeBase]; omega)
              (not_inRecords_of_lt_nodesBase (by simp [endOwnerBase, nodesBase]; omega))]
            dsimp only
            rw [hmIr_ne _ (by simp [endOwnerBase, isRootBase]; omega)]
            exact hinactC k hk fun p hp => hno p (by rw [hdone_succ]; exact List.mem_append_left _ hp),
          hko1_mem, hnk1,
          fun v' hv' => by
            by_cases hv'v : v' = v
            · subst hv'v
              have hex : ∃ ys, (v, ys) ∈ recs.take (idx + 1) ∧ ys ≠ [] := ⟨xs, by rw [hdone_succ]; simp, hxs_ne⟩
              simp only [hex, ↓reduceIte, hfeI, hord_v]
              cases hxs_c : xs with
              | nil => exact absurd hxs_c hxs_ne
              | cons a0 as0 =>
                simp only [List.head?_cons]
                rw [hno1_z a0 (by simp [hxs_c])]; simp [hxs_c]
            · rw [hfrI _ (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) (by omega)
                (fun z' hz' => by have := endKey_lt_two_mul (hxs_lt z' hz'); simp [firstEndBase, nodeOfEndBase]; omega)
                (fun z' hz' => by have := endKey_lt_two_mul (hxs_lt z' hz'); simp [firstEndBase, endOwnerBase]; omega)
                (fun _ _ _ => by simp [firstEndBase, keyOfNodeBase]; omega) (not_inRecords_of_lt_nodesBase (by simp [firstEndBase, nodesBase]; omega))]
              dsimp only
              rw [hmIr_ne _ (by simp [firstEndBase, isRootBase]; omega), hfeC v' hv']
              have hiff : (∃ ys, (v', ys) ∈ recs.take (idx + 1) ∧ ys ≠ []) ↔ ∃ ys, (v', ys) ∈ done ∧ ys ≠ [] := by
                rw [hdone_succ]; simp [hv'v]
              simp only [hiff]
              split_ifs with h1
              · cases ho : (s0.ord v').head? with
                | none => rfl
                | some a0 =>
                  have hne_xs : ∀ z' ∈ xs, endKey a0 ≠ endKey z' := fun z' hz' heq => by
                    have ha_eq : a0 = z' := by simpa [endOfKey_endKey] using congrArg endOfKey heq
                    exact hv'v (hvalid0.compat.unique v' v a0 (List.mem_of_head? ho) (ha_eq ▸ hord_v ▸ hz'))
                  exact (hno1_fr _ hne_xs).symm
              · rfl,
          fun v' hv' => by
            rw [hfrI _ (by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
              (by simp [isRootBase, firstEndBase]; omega) (fun _ _ => by simp [isRootBase, nodeOfEndBase]; omega)
              (fun _ _ => by simp [isRootBase, endOwnerBase]; omega) (fun _ _ _ => by simp [isRootBase, keyOfNodeBase]; omega)
              (not_inRecords_of_lt_nodesBase (by simp [isRootBase, nodesBase]; omega))]
            by_cases hv'v : v' = v
            · subst hv'v; dsimp only; simp only [mIr, Function.update_self]
              have hex : ∃ ys, (v, ys) ∈ recs.take (idx + 1) ∧ ys ≠ [] := ⟨xs, by rw [hdone_succ]; simp, hxs_ne⟩
              simp only [hex, ↓reduceIte]
            · dsimp only; rw [hmIr_ne _ (by omega), hirC v' hv']
              have hiff : (∃ ys, (v', ys) ∈ recs.take (idx + 1) ∧ ys ≠ []) ↔ ∃ ys, (v', ys) ∈ done ∧ ys ≠ [] := by
                rw [hdone_succ]; simp [hv'v]
              simp [hiff],
          fun v' hv' => by
            by_cases hv'v : v' = v
            · subst hv'v; refine ⟨tV, by simp, List.mem_cons_self, by rw [htV_map, hord_v]⟩
            · rw [hdone_succ] at hv'
              have hv'_d : ∃ ys, (v', ys) ∈ done ∧ ys ≠ [] := by
                rcases hv' with ⟨ys, hmem, hne⟩; simp [hv'v] at hmem; exact ⟨ys, hmem, hne⟩
              obtain ⟨t0, hct0, ht0_mem, ht0_map⟩ := hct_s v' hv'_d
              refine ⟨t0, by simp [hv'v, hct0], List.mem_cons_of_mem _ ht0_mem, ?_⟩
              rw [← ht0_map]; refine List.map_congr_left fun id hid => ?_
              have h12 := (hexC id).mp (List.mem_flatMap.mpr ⟨t0, ht0_mem, hid⟩)
              rw [hko1_old id h12.1 h12.2],
          fun v' hv' => by
            have hv'v : v' ≠ v := fun heq => hxs_ne (hv' xs (by rw [hdone_succ, heq]; simp))
            rw [Function.update_of_ne hv'v]
            exact hct_n v' fun ys hys => hv' ys (by rw [hdone_succ]; exact List.mem_append_left _ hys),
          fun t ht => by
            rcases List.mem_cons.mp ht with rfl | ht0
            · exact ⟨v, ⟨xs, by rw [hdone_succ]; simp, hxs_ne⟩, by simp⟩
            · obtain ⟨v', hv', hct'⟩ := ht_cls t ht0
              have hv'v : v' ≠ v := fun heq => by rcases hv' with ⟨ys, hys, _⟩; exact hv_not_done ys (heq ▸ hys)
              exact ⟨v', let ⟨ys, hys, hne⟩ := hv'; ⟨ys, by rw [hdone_succ]; exact List.mem_append_left _ hys, hne⟩,
                by simp [hv'v, hct']⟩,
          fun u h1 h2 => by
            by_cases hu_le : u ≤ nnC
            · rw [hval1_old u hu_le, hvalC u h1 hu_le, hko1_old u h1 hu_le]
            · rw [hval1_new u (by omega) h2]
              have hu_tV : u ∈ tV.toList := (htV_mem u).mpr ⟨by omega, h2⟩
              have hk_in : endOfKey (ko1 u) ∈ s0.ord v := by
                rw [hord_v, ← htV_map]; exact List.mem_map_of_mem hu_tV
              by_cases hu1 : u = nnC + 1
              · subst hu1; simp only [↓reduceIte]
                cases hxs_c : xs with
                | nil => exact absurd hxs_c hxs_ne
                | cons a0 as0 =>
                  have hko_eq : endOfKey (ko1 (nnC + 1)) = a0 := by
                    have hno_a0 : no1 (endKey a0) = nnC + 1 := by rw [hno1_z a0 (by simp [hxs_c])]; simp [hxs_c]
                    have hlt_a0 : endKey a0 < 2 * eCap := endKey_lt_two_mul (hxs_lt a0 (by simp [hxs_c]))
                    have := hnk1 (endKey a0) hlt_a0 (by omega); rw [hno_a0] at this; rw [this, endOfKey_endKey]
                  rw [hko_eq, tourRootTagVal_eq_succ hvalid0 hv_in_V (by rw [hord_v, hxs_c]; rfl)]
              · simp only [hu1, ↓reduceIte]
                have hrt0 : tourRootTagVal s0 (endOfKey (ko1 u)) = 0 := by
                  apply tourRootTagVal_eq_zero; intro r' _ hh
                  have hr'v : r' = v := hvalid0.compat.unique r' v _ (List.mem_of_head? hh) hk_in
                  subst hr'v; rw [hord_v] at hh
                  cases hxs_c : xs with
                  | nil => simp [hxs_c] at hh
                  | cons a0 as0 =>
                    simp only [hxs_c, List.head?_cons, Option.some.injEq] at hh
                    have hno_a0 : no1 (endKey a0) = nnC + 1 := by rw [hno1_z a0 (by simp [hxs_c])]; simp [hxs_c]
                    have hkeq : ko1 u = endKey a0 := by rw [← endKey_endOfKey' (ko1 u), ← hh]
                    have hu_eq : u = nnC + 1 := by rw [← (hko1_mem u h1 h2).2.2, hkeq, hno_a0]
                    exact hu1 hu_eq
                rw [hrt0],
          by rw [hval1_old 0 (Nat.zero_le _)]; exact hval0,
          fun a ha => by
            have hlt_out : a < hOut := by rcases ha with h1 | ⟨_, h2⟩; simp [ordHandleOf, tourFixedSize] at hord_le; omega; exact h2
            rw [hfrI a hlt_out (by simp [firstEndBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | ⟨h2, _⟩ <;> omega)
              (fun z hz => by have := endKey_lt_two_mul (hxs_lt z hz); simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | ⟨h2, _⟩ <;> omega)
              (fun z hz => by have := endKey_lt_two_mul (hxs_lt z hz); simp [endOwnerBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | ⟨h2, _⟩ <;> omega)
              (fun u hu1 hu2 => by simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | ⟨h2, _⟩ <;> omega)
              (fun hr => by have := inRecords_lt_ordHandle_of_le hnn_end hr; simp [nodesBase] at this; rcases ha with h1 | ⟨h2, _⟩ <;> omega)]
            dsimp only
            rw [hmIr_ne a (by simp [isRootBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | ⟨h2, _⟩ <;> omega)]
            exact hfr_out a ha,
          fun a ha1 ha2 => by
            rw [hfrI a (by simp [ordHandleOf, tourFixedSize] at hord_le; omega)
              (by simp [firstEndBase]; omega) (fun _ _ => by simp [nodeOfEndBase]; omega)
              (fun _ _ => by simp [endOwnerBase]; omega) (fun _ _ _ => by simp [keyOfNodeBase]; omega)
              (not_inRecords_of_lt_nodesBase (by simp [nodesBase]; omega))]
            dsimp only
            rw [hmIr_ne a (by simp [isRootBase]; omega)]
            exact hfr_hdr a ha1 ha2,
          fun a ha1 ha2 => by
            rw [hfrI a (by simp [nodesBase, ordHandleOf, tourFixedSize] at ha2 hord_le ⊢; omega)
              (by simp [markArrBase, firstEndBase] at ha1 ⊢; omega)
              (fun z hz => by have := endKey_lt_two_mul (hxs_lt z hz); simp [markArrBase, nodeOfEndBase] at ha1 ⊢; omega)
              (fun z hz => by have := endKey_lt_two_mul (hxs_lt z hz); simp [markArrBase, endOwnerBase] at ha1 ⊢; omega)
              (fun u hu1 hu2 => by simp [markArrBase, keyOfNodeBase] at ha1 ⊢; omega)
              (not_inRecords_of_lt_nodesBase ha2)]
            dsimp only
            rw [hmIr_ne a (by simp [markArrBase, isRootBase] at ha1 ⊢; omega)]
            exact hfr_mk a ha1 ha2, ?_⟩
        have h1 : xs.length * (TOUR_JOIN_AMORT + 400) * (2 * tourLog eCap) + 100 ≤
            (2 + len) * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) - 30 := by
          rw [hxs_len]
          have h2t : 2 ≤ 2 * tourLog eCap := by omega
          have hbig : 130 ≤ 2 * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) := by
            have : 2 * (TOUR_JOIN_AMORT + 500) * 2 ≤ 2 * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) :=
              Nat.mul_le_mul_left _ h2t
            unfold TOUR_JOIN_AMORT at this ⊢; omega
          have hlin : len * (TOUR_JOIN_AMORT + 400) * (2 * tourLog eCap) ≤
              len * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
          have hspl : (2 + len) * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) =
              2 * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) +
                len * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) := by ring
          omega
        clear * - hcI h1; simp only [Expr.size]; omega
    obtain ⟨nn1, s1, trees1, no1, ko1, ct1, stM, cM, hrunM, hnn1, hrM_lt, hrM16, hn1, hinv1, hvals1, hz1,
      hex1, hno1_mem, hno1_fr, hact1, hinact1, hko1_mem, hnk1, hfe1, hir1, hct1_s, hct1_n, ht1_cls,
      hval1, hval01, hfr1_out, hfr1_hdr, hfr1_mk, hcM⟩ := hmid
    set r6 := Function.update stM.regs 15 (curPtr + 2 + len)
    set r7 := Function.update r6 17 (idx + 1)
    have hidx_lt_w : idx + 1 < 2 ^ w := by
      have h1 : recs.length = mem ordPtr := readOrdRecords_length mem (mem ordPtr) (ordPtr + 1)
      have h2 := hlen_le_words recs
      dsimp only [recs] at h1 h2
      simp [ordHandleOf, tourFixedSize] at hord_le; omega
    have ha15b : Runs w p ω (.assign 15 (.bin .add (.reg 15) (.reg 19))) stM .normal { stM with regs := r6 } 4 :=
      runs_assign_iff.mpr ⟨curPtr + 2 + len, by
        simp [Expr.eval, hrM_lt 15 (by omega) (by omega), hrM_lt 19 (by omega) (by omega), r3, r2, BinOp.eval,
          (by simp [ordHandleOf, tourFixedSize] at hord_le; omega : curPtr + 2 + len < 2 ^ w)], rfl, rfl, rfl⟩
    have ha17b : Runs w p ω (.assign 17 (.bin .add (.reg 17) (.const 1))) { stM with regs := r6 } .normal { stM with regs := r7 } 4 :=
      runs_assign_iff.mpr ⟨idx + 1, by
        simp [Expr.eval, r6, hrM_lt 17 (by omega) (by omega), r3, r2, r1, hr17, BinOp.eval, (by omega : 1 < 2 ^ w),
          hidx_lt_w], rfl, rfl, rfl⟩
    have hbody := tour_runs_seq_normal ha18 (tour_runs_seq_normal ha19 (tour_runs_seq_normal ha15a (tour_runs_seq_normal hrunM (tour_runs_seq_normal ha15b ha17b))))
    obtain ⟨nnF, sF, treesF, noF, koF, ctF, stF, cRest, hrunR, hnnF, hrF3, hrF4, hrF6, hrF13, hrF16,
      hnF, hinvF, hzF, hexF, hnoF, hactF, hinactF, hkoF, hnkF, hfeF, hirF, hctF_s, hctF_n, htF_cls,
      hvalF, hval0F, hfrF_out, hfrF_hdr, hfrF_mk, hcRest⟩ :=
      ih (idx + 1) (curPtr + 2 + len) nn1 s1 trees1 no1 ko1 ct1 { stM with regs := r7 } (by omega)
        (by rw [hdone_succ, List.append_assoc]; simpa [htodo_eq] using hrecs_eq)
        (by omega) (by rw [hdone_succ]; simp [hnn1, hnnC, xs, readList_length])
        (by simp [r7, r6, hrM_lt 0 (by omega) (by omega), r3, r2, r1, hr0])
        (by simp [r7, r6, hrM_lt 1 (by omega) (by omega), r3, r2, r1, hr1])
        (by simp [r7, r6, hrM_lt 2 (by omega) (by omega), r3, r2, r1, hr2])
        (by simp [r7, r6, hrM_lt 3 (by omega) (by omega), r3, r2, r1, hr3])
        (by simp [r7, r6, hrM_lt 4 (by omega) (by omega), r3, r2, r1, hr4])
        (by simp [r7, r6, hrM_lt 5 (by omega) (by omega), r3, r2, r1, hr5])
        (by simp [r7, r6, hrM_lt 6 (by omega) (by omega), r3, r2, r1, hr6])
        (by simp [r7, r6, hrM_lt 7 (by omega) (by omega), r3, r2, r1, hr7])
        (by simp [r7, r6, hrM_lt 8 (by omega) (by omega), r3, r2, r1, hr8])
        (by simp [r7, r6, hrM_lt 9 (by omega) (by omega), r3, r2, r1, hr9])
        (by simp [r7, r6, hrM_lt 10 (by omega) (by omega), r3, r2, r1, hr10])
        (by simp [r7, r6, hrM_lt 12 (by omega) (by omega), r3, r2, r1, hr12])
        (by simp [r7, r6, hrM_lt 13 (by omega) (by omega), r3, r2, r1, hr13])
        (by simp [r7, r6, hrM_lt 14 (by omega) (by omega), r3, r2, r1, hr14])
        (by simp [r7, r6]) (by simp [r7, r6, hrM16]) (by simp [r7])
        hn1 hinv1 hvals1 hz1 hex1 hno1_mem hno1_fr hact1 hinact1 hko1_mem hnk1 hfe1 hir1
        hct1_s hct1_n ht1_cls hval1 hval01 hfr1_out hfr1_hdr hfr1_mk
    refine ⟨nnF, sF, treesF, noF, koF, ctF, stF, _,
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, _, _, hcond, by omega, hbody, hrunR, rfl⟩)),
      hnnF, hrF3, hrF4, hrF6, hrF13, hrF16, hnF, hinvF, hzF, hexF, hnoF, hactF, hinactF, hkoF, hnkF,
      hfeF, hirF, hctF_s, hctF_n, htF_cls, hvalF, hval0F, hfrF_out, hfrF_hdr, hfrF_mk, ?_⟩
    have hspl : ordRecordsWords todo * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) =
        (2 + len) * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) +
        ordRecordsWords (readOrdRecords mem rem (curPtr + 2 + len)) * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) := by
      rw [hwords_eq]; ring
    have hbig30 : 30 ≤ (2 + len) * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) := by
      have : 2 * (TOUR_JOIN_AMORT + 500) * 2 ≤ (2 + len) * (TOUR_JOIN_AMORT + 500) * (2 * tourLog eCap) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (by omega)
      unfold TOUR_JOIN_AMORT at this ⊢; omega
    clear * - hcM hcRest hspl hbig30; simp only [Expr.size]; omega

end MinCostFlow.SparseCore.Program
