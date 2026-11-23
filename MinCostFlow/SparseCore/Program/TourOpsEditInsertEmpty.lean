module

public import MinCostFlow.SparseCore.Program.TourOpsEditInsertExec
import Mathlib.Tactic

/-!
# Empty-vertex case and core-invariant helper for `insertBefore` (Op 0)

Proves `tourEditInsertBody_runs_empty` (when `s.ord v = []`) and `tourEditInsert_nonempty_core`
(building `TourCoreAt` after the nonempty-vertex splice and optional root-tag/rotation update).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-- Verified amortized run theorem for `tourEditInsertBody [b, v, keyX, yWord, heap]`. -/
theorem tourEditInsertBody_runs_empty {τ_ord : Type}
    {w vCap eCap b v keyX yWord heap pos : ℕ} {p : Program}
    (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem)
    (hkeyLt : keyX < 2 * eCap)
    (hedit : TourEditValid vCap eCap s
      (.insertBefore v (endOfKey keyX) (if yWord = 0 then none else some (endOfKey (yWord - 1)))))
    (hord_le : ordHandleOf b vCap eCap ≤ heap) (hroom : heap + 2 < 2 ^ w)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w) (hzero : ZeroFrom mem heap) (hnil : s.ord v = []) :
    let yOpt : Option End := if yWord = 0 then none else some (endOfKey (yWord - 1))
    let s' := tourApplyEdit s (.insertBefore v (endOfKey keyX) yOpt)
    ∃ (st' : State) (c : ℕ) (x' : TourConcrete τ_ord),
      Runs w p ω (tourEditInsertBody C.initNode C.insertBefore C.setValNode C.rotateFront)
        (startState [b, v, keyX, yWord, heap] mem pos) (.returned heap) st' c ∧
      x'.ordX = x.ordX ∧
      ZeroFrom st'.mem heap ∧
      (∀ a, (a < b ∨ ordHandleOf b vCap eCap ≤ a) → a < heap → st'.mem a = mem a) ∧
      TourCoreAt vCap eCap b s' x' st'.mem ∧
      c + TOUR_PHI_MULT * forestPhi x'.trees ≤
        TOUR_PHI_MULT * forestPhi x.trees + TOUR_EDIT_SIMPLE_MUL * tourLog eCap := by
  intro yOpt s'
  have hvLt : v < vCap := hedit.1
  have hvF : v ∈ s.rf.F.V := hedit.2.1
  have hxOpen : (endOfKey keyX).1 ∉ s.rf.F.E := hedit.2.2.2.1
  have hxFresh : ∀ w', endOfKey keyX ∉ s.ord w' := hedit.2.2.2.2.1
  have hyWord_le : yWord ≤ 2 * eCap := by
    by_cases hy0 : yWord = 0
    · omega
    · have hylt := hedit.2.2.2.2.2 (endOfKey (yWord - 1)) (by simp [hy0])
      have := key_lt_two_mul_of_endOfKey hylt; omega
  have hvalid' : TourValid vCap eCap s' := tourValid_applyEdit_insertBefore h.valid hedit
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hlog : Nat.log 2 (2 * eCap + 2) + 1 ≤ 2 * tourLog eCap := tourLog_double_le eCap
  have hord'_mem : ∀ w' z, z ∈ s'.ord w' ↔ (w' = v ∧ z = endOfKey keyX) ∨ z ∈ s.ord w' := by
    intro w' z; by_cases hwv : w' = v
    · subst hwv; simp only [s', tourApplyEdit, applyOrdEdit, Function.update_self, insertBeforeList, true_and]
      cases yOpt with
      | none => simp [or_comm]
      | some y' =>
        have htd := List.take_append_drop ((s.ord w').idxOf y') (s.ord w')
        simp only [List.mem_append, List.mem_cons]
        constructor
        · rintro (h1 | rfl | h2)
          · exact Or.inr (List.mem_of_mem_take h1)
          · exact Or.inl rfl
          · exact Or.inr (List.mem_of_mem_drop h2)
        · rintro (rfl | hz)
          · exact Or.inr (Or.inl rfl)
          · rw [← htd, List.mem_append] at hz; rcases hz with h1 | h2; exact Or.inl h1; exact Or.inr (Or.inr h2)
    · simp [s', tourApplyEdit, applyOrdEdit, hwv]
  have hxNotMarked : endOfKey keyX ∉ s.marked := fun hm => by
    obtain ⟨⟨w', hw'⟩, _⟩ := h.valid.marked_open _ hm; exact hxFresh w' hw'
  -- Step 1: allocate/reuse `u` and initialize singleton
  obtain ⟨u, nn1, nodeOf1, keyOf1, s1, trees1, mem1, r1, pos1, c1,
    hu1, hunn, hnn_le, hn1k, hk1u, hn1_ne, hk1_old, hn1_mem, hn1_ko, hk1_mem, hhdr1, hn1, hinv1, hphi1,
    hexact1, ht1_sub, ht1_mem, hs1u, hs1ne, hfr1_in, hfr1_out,
    hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hr19, hr110, hr111, hr112, hr113,
    hc1, hrun1⟩ :=
    tourEditInsert_alloc_exec (yWord := yWord) (pos := pos) C ω h hvLt hkeyLt (by omega) hxFresh hord_le hroom hw hwide
  have hmem1_fixed_eq : ∀ a, a < nodesBase b vCap eCap →
      a ≠ b + HDR_NUM_NODES → a ≠ nodeOfEndBase b vCap + keyX → a ≠ keyOfNodeBase b vCap eCap + u →
      mem1 a = mem a := fun a hlt h1 h2 h3 => by
    by_cases hba : b ≤ a
    · exact hfr1_in a hba (by simp [nodesBase, ordHandleOf, tourFixedSize] at hlt ⊢; omega) h1 h2 h3
        (fun i _ => by omega)
    · exact hfr1_out a (Or.inl (by omega))
  have hzero1 : ZeroFrom mem1 heap := fun a ha => by
    rw [hfr1_out a (Or.inr (by omega))]; exact hzero a ha
  have hgeo_eo : endOwnerBase b vCap eCap + keyX < 2 ^ w ∧ x.slotOf v + 1 < 2 ^ w ∧
      firstEndBase b + v < 2 ^ w ∧ isRootBase b vCap + v < 2 ^ w ∧ b + 16 < 2 ^ w := by
    have := (h.slot_bij v hvLt).1
    simp [endOwnerBase, firstEndBase, isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
  have hsv_lt : x.slotOf v < vCap := (h.slot_bij v hvLt).1
  -- Case split on `s.ord v = []` vs `s.ord v ≠ []`
  have hfe0 : mem (firstEndBase b + v) = 0 := by rw [h.firstEnd_mem v hvLt, hnil]; rfl
  have ⟨hvR, hiso⟩ := empty_ord_mem_roots h.valid hvF hnil
  have hcond_fe : (Expr.bin .eq (.reg 9) (.const 0)).eval w ⟨mem1, r1, pos1⟩ = some 1 := by
    simp [Expr.eval, hr19, hfe0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
  set mem2 := Function.update mem1 (firstEndBase b + v) u
  have hst_fe : Runs w p ω (.store (.bin .add (.reg 8) (.reg 1)) (.reg 6))
      ⟨mem1, r1, pos1⟩ .normal ⟨mem2, r1, pos1⟩ 5 :=
    runs_store_iff.mpr ⟨firstEndBase b + v, u,
      by simp [Expr.eval, hr18, hr11, BinOp.eval, hgeo_eo.2.2.1],
      by simp [Expr.eval, hr16], rfl, rfl, rfl⟩
  set r2 := Function.update r1 14 (v + 1)
  have hass_rt : Runs w p ω (.assign 14 (.bin .add (.reg 1) (.const 1)))
      ⟨mem2, r1, pos1⟩ .normal ⟨mem2, r2, pos1⟩ 4 :=
    runs_assign_iff.mpr ⟨v + 1, by simp [Expr.eval, hr11, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : v + 1 < 2 ^ w)],
      rfl, rfl, rfl⟩
  have hAu_lt : nodesBase b vCap eCap + 17 * u + 17 < 2 ^ w := by
    simp [nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
  obtain ⟨oI2, stI2, cI2, hrunI2, ⟨hnuI2, hfrI2⟩, hcI2⟩ :=
    tourInitNodeBody_runs (w := w) (nb := nodesBase b vCap eCap) (x := u) (isOpen := 1)
      (isMarked := 0) (rootTag := v + 1) (pos := pos1) (p := p) ω (mem := mem2) hAu_lt hwide
  have hcallI2 := runs_call_regs5 15 10 6 12 13 14 (st := ⟨mem2, r2, pos1⟩) C.initNode_body
    (by simp [r2, hr110]) (by simp [r2, hr16]) (by simp [r2, hr112]) (by simp [r2, hr113])
    (by simp [r2]) hrunI2
  set r3 := Function.update r2 15 oI2.value
  set mem3 := Function.update stI2.mem (endOwnerBase b vCap eCap + keyX) (x.slotOf v + 1)
  have hst_eo : Runs w p ω (.store (.bin .add (.reg 7) (.reg 2)) (.bin .add (.reg 5) (.const 1)))
      { stI2 with regs := r3 } .normal { stI2 with mem := mem3, regs := r3 } 7 :=
    runs_store_iff.mpr ⟨endOwnerBase b vCap eCap + keyX, x.slotOf v + 1,
      by simp [Expr.eval, r3, r2, hr17, hr12, BinOp.eval, hgeo_eo.1],
      by simp [Expr.eval, r3, r2, hr15, BinOp.eval, (by omega : 1 < 2 ^ w), hgeo_eo.2.1],
      rfl, rfl, rfl⟩
  have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := { stI2 with mem := mem3, regs := r3 })
    (r := 4) (v := heap) (by simp [r3, r2, hr14])
  have hfull : Runs w p ω (tourEditInsertBody C.initNode C.insertBefore C.setValNode C.rotateFront)
      (startState [b, v, keyX, yWord, heap] mem pos) (.returned heap)
      { stI2 with mem := mem3, regs := r3 } _ :=
    runs_seqAppend hrun1 (tour_runs_seq_normal
      (tour_runs_cond_true hcond_fe (by omega) (tour_runs_seq_normal hst_fe (tour_runs_seq_normal hass_rt hcallI2)))
      (tour_runs_seq_normal hst_eo hret))
  -- Construct `s2`, `x'` and prove `TourCoreAt`
  set s2 : SplayState TourVal TourSum Unit :=
    { nodes := Function.update s1.nodes u (tourSingletonNode u ⟨true, false, v + 1⟩) }
  have hn2_mem2 : tourLayout.NodesAt mem2 (nodesBase b vCap eCap) nn1 s1 :=
    NodesAt.congr tourLayout hn1 fun a ha => by
      dsimp only [mem2]; rw [Function.update_of_ne fun heq => by
        have := (inRecords_lt_ordHandle_of_le hnn_le ha).1; simp [firstEndBase, nodesBase] at heq this; omega]
  have hnuI2' : tourLayout.NodeAt stI2.mem (nodesBase b vCap eCap) u (tourSingletonNode u ⟨true, false, v + 1⟩) := by
    simpa [tourSingletonNode] using hnuI2
  obtain ⟨hnI2, hinv2⟩ := tourInitNode_reuse_preserves hn2_mem2 hinv1 hnuI2' hfrI2
  have hn3 : tourLayout.NodesAt mem3 (nodesBase b vCap eCap) nn1 s2 :=
    NodesAt.congr tourLayout hnI2 fun a ha => by
      dsimp only [mem3]; rw [Function.update_of_ne fun heq => by
        have := (inRecords_lt_ordHandle_of_le hnn_le ha).1; simp [endOwnerBase, nodesBase] at heq this; omega]
  have hm3_pre : ∀ a < nodesBase b vCap eCap, a ≠ endOwnerBase b vCap eCap + keyX →
      a ≠ firstEndBase b + v → mem3 a = mem1 a := fun a hlt h1 h2 => by
    dsimp only [mem3]; rw [Function.update_of_ne h1, hfrI2 a (fun i _ => by omega)]
    dsimp only [mem2]; rw [Function.update_of_ne h2]
  have hm3_out : ∀ a, a < b ∨ ordHandleOf b vCap eCap ≤ a → mem3 a = mem a := fun a ha => by
    dsimp only [mem3]
    rw [Function.update_of_ne (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | h2 <;> omega),
      hfrI2 a (fun i hi => by simp [nodesBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | h2 <;> omega)]
    dsimp only [mem2]
    rw [Function.update_of_ne (by simp [firstEndBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | h2 <;> omega)]
    exact hfr1_out a ha
  have hhdr3 : TourHeaderAt vCap eCap b nn1 mem3 := by
    rcases hhdr1 with ⟨h0', h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', h11', h12', h13', h14'⟩
    have hf : ∀ k < 16, mem3 (b + k) = mem1 (b + k) := fun k hk =>
      hm3_pre _ (by simp [nodesBase]; omega) (by simp [endOwnerBase]; omega) (by simp [firstEndBase]; omega)
    exact ⟨by rw [hf _ (by decide)]; exact h0', by rw [hf _ (by decide)]; exact h1',
      by rw [hf _ (by decide)]; exact h2', by rw [hf _ (by decide)]; exact h3',
      by rw [hf _ (by decide)]; exact h4', by rw [hf _ (by decide)]; exact h5',
      by rw [hf _ (by decide)]; exact h6', by rw [hf _ (by decide)]; exact h7',
      by rw [hf _ (by decide)]; exact h8', by rw [hf _ (by decide)]; exact h9',
      by rw [hf _ (by decide)]; exact h10', by rw [hf _ (by decide)]; exact h11',
      by rw [hf _ (by decide)]; exact h12', by rw [hf _ (by decide)]; exact h13',
      by rw [hf _ (by decide)]; exact h14'⟩
  have hft_v : fullTour s'.ord s'.rf.F hvalid'.compat.forest v = [endOfKey keyX] :=
    fullTour_insertOpen_singleton h.valid hedit hnil
  have hft_other : ∀ r' ∈ s.rf.R, r' ≠ v →
      fullTour s'.ord s'.rf.F hvalid'.compat.forest r' = fullTour s.ord s.rf.F h.valid.compat.forest r' := by
    intro r' hr' hne
    exact fullTour_insertOpen_other h.valid hedit fun hconn => hne (hiso r' (connected_symm hconn))
  have hcomp_ne_u : ∀ r' ∈ s.rf.R, r' ≠ v → x.compTree r' ≠ some (AuxTree.node u .leaf .leaf) := by
    intro r' hr' hne hct
    by_cases hft0 : fullTour s.ord s.rf.F h.valid.compat.forest r' = []
    · rw [h.comp_none r' hr' hft0] at hct; cases hct
    · obtain ⟨t0, ht0_eq, ht0_mem, ht0_map⟩ := h.comp_some r' hr' hft0
      rw [ht0_eq] at hct; cases Option.some.inj hct
      have hx_ft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r' := by
        rw [← ht0_map]; simp [AuxTree.toList]
      obtain ⟨w', hw', _⟩ := ((fullTour_spec h.valid.compat r').2 _).mp hx_ft
      have : x.keyOf u = keyX := by
        have : u ∈ x.trees.flatMap AuxTree.toList :=
          List.mem_flatMap.mpr ⟨_, ht0_mem, by simp [AuxTree.toList]⟩
        have hu_old := (h.nodes_exact u).mp this
        rw [← hk1_old u hu_old.1 hu_old.2, hk1u]
      rw [this] at hw'; exact hxFresh w' hw'
  have hxnn_le_nn1 : x.numNodes ≤ nn1 := by
    by_cases h0 : x.numNodes = 0
    · omega
    · have hxnn := (h.nodes_exact x.numNodes).mpr ⟨by omega, le_refl _⟩
      obtain ⟨t0, ht0, hmem0⟩ := List.mem_flatMap.mp hxnn
      by_cases htu : t0 = AuxTree.node u .leaf .leaf
      · subst htu; simp [AuxTree.toList] at hmem0; omega
      · exact ((hexact1 x.numNodes).mp
          (List.mem_flatMap.mpr ⟨t0, List.mem_cons_of_mem _ (ht1_mem t0 ht0 htu), hmem0⟩)).2
  set x' : TourConcrete τ_ord :=
    { ordX := x.ordX, numNodes := nn1, st := s2, trees := AuxTree.node u .leaf .leaf :: trees1,
      nodeOf := nodeOf1, keyOf := keyOf1,
      compTree := Function.update x.compTree v (some (AuxTree.node u .leaf .leaf)),
      slotOf := x.slotOf, vertOf := x.vertOf }
  have hcore' : TourCoreAt vCap eCap b s' x' mem3 :=
    { valid := hvalid', header := hhdr3, numNodes_le := hnn_le
      nodeOf_mem := fun k hk => by
        rw [hm3_pre _ (by simp [nodeOfEndBase, nodesBase]; omega)
          (by simp [nodeOfEndBase, endOwnerBase]; omega) (by simp [nodeOfEndBase, firstEndBase]; omega)]
        exact hn1_mem k hk
      nodeOf_keyOf := hn1_ko
      keyOf_mem := fun id h1 h2 => by
        dsimp only [x'] at h2
        rw [hm3_pre _ (by simp [keyOfNodeBase, nodesBase]; omega)
          (by simp [keyOfNodeBase, endOwnerBase]; omega) (by simp [keyOfNodeBase, firstEndBase]; omega)]
        exact hk1_mem id h1 h2
      firstEnd_mem := fun w' hw' => by
        by_cases hwv : w' = v
        · subst hwv
          have hm3v : mem3 (firstEndBase b + w') = u := by
            dsimp only [mem3]
            rw [Function.update_of_ne (by simp [firstEndBase, endOwnerBase]; omega),
              hfrI2 _ (fun i _ => by simp [firstEndBase, nodesBase]; omega)]
            simp [mem2]
          rw [hm3v]; simp [s', tourApplyEdit, applyOrdEdit, insertBeforeList_head?, hnil, x', hn1k, endKey_endOfKey']
        · rw [hm3_pre _ (by simp [firstEndBase, nodesBase]; omega) (by simp [firstEndBase, endOwnerBase]; omega) (by omega),
            hmem1_fixed_eq _ (by simp [firstEndBase, nodesBase]; omega) (by simp [firstEndBase, HDR_NUM_NODES]; omega)
              (by simp [firstEndBase, nodeOfEndBase]; omega) (by simp [firstEndBase, keyOfNodeBase]; omega),
            h.firstEnd_mem w' hw']
          simp only [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hwv, x']
          cases ho : (s.ord w').head? with
          | none => rfl
          | some a =>
            have ha_ne : endKey a ≠ keyX := fun heq => hxFresh w' (by rw [← heq, endOfKey_endKey]; exact List.mem_of_head? ho)
            exact (hn1_ne _ ha_ne).symm
      isRoot_mem := fun w' hw' => by
        rw [hm3_pre _ (by simp [isRootBase, nodesBase]; omega) (by simp [isRootBase, endOwnerBase]; omega)
          (by simp [isRootBase, firstEndBase]; omega),
          hmem1_fixed_eq _ (by simp [isRootBase, nodesBase]; omega) (by simp [isRootBase, HDR_NUM_NODES]; omega)
            (by simp [isRootBase, nodeOfEndBase]; omega) (by simp [isRootBase, keyOfNodeBase]; omega)]
        exact h.isRoot_mem w' hw'
      slot_bij := h.slot_bij
      slotOf_mem := fun w' hw' => by
        rw [hm3_pre _ (by simp [slotOfVertBase, nodesBase]; omega) (by simp [slotOfVertBase, endOwnerBase]; omega)
          (by simp [slotOfVertBase, firstEndBase]; omega),
          hmem1_fixed_eq _ (by simp [slotOfVertBase, nodesBase]; omega) (by simp [slotOfVertBase, HDR_NUM_NODES]; omega)
            (by simp [slotOfVertBase, nodeOfEndBase]; omega) (by simp [slotOfVertBase, keyOfNodeBase]; omega)]
        exact h.slotOf_mem w' hw'
      vertOf_mem := fun sl hsl => by
        rw [hm3_pre _ (by simp [vertOfSlotBase, nodesBase]; omega) (by simp [vertOfSlotBase, endOwnerBase]; omega)
          (by simp [vertOfSlotBase, firstEndBase]; omega),
          hmem1_fixed_eq _ (by simp [vertOfSlotBase, nodesBase]; omega) (by simp [vertOfSlotBase, HDR_NUM_NODES]; omega)
            (by simp [vertOfSlotBase, nodeOfEndBase]; omega) (by simp [vertOfSlotBase, keyOfNodeBase]; omega)]
        exact h.vertOf_mem sl hsl
      active_end := fun w' hw' z hz => by
        rcases (hord'_mem w' z).mp hz with ⟨rfl, rfl⟩ | hz0
        · refine ⟨by simp [x', hn1k, endKey_endOfKey']; omega, by simp [mem3, x', endKey_endOfKey']⟩
        · have hne : endKey z ≠ keyX := fun heq => hxFresh w' (by rw [← heq, endOfKey_endKey]; exact hz0)
          have hzLt : endKey z < 2 * eCap := by
            have := h.valid.ordWithin.2.2 w' z hz0; simp only [endKey]; cases z.2 <;> simp <;> omega
          rw [hm3_pre _ (by simp [endOwnerBase, nodesBase]; omega) (by omega) (by simp [endOwnerBase, firstEndBase]; omega),
            hmem1_fixed_eq _ (by simp [endOwnerBase, nodesBase]; omega) (by simp [endOwnerBase, HDR_NUM_NODES]; omega)
              (by simp [endOwnerBase, nodeOfEndBase]; omega) (by simp [endOwnerBase, keyOfNodeBase]; omega)]
          simpa [x', hn1_ne _ hne] using h.active_end w' hw' z hz0
      inactive_owner := fun k hk hno => by
        have hne : k ≠ keyX := fun heq => hno v ((hord'_mem v _).mpr (Or.inl ⟨rfl, by rw [heq]⟩))
        rw [hm3_pre _ (by simp [endOwnerBase, nodesBase]; omega) (by omega) (by simp [endOwnerBase, firstEndBase]; omega),
          hmem1_fixed_eq _ (by simp [endOwnerBase, nodesBase]; omega) (by simp [endOwnerBase, HDR_NUM_NODES]; omega)
            (by simp [endOwnerBase, nodeOfEndBase]; omega) (by simp [endOwnerBase, keyOfNodeBase]; omega)]
        exact h.inactive_owner k hk fun w' hw' => hno w' ((hord'_mem w' _).mpr (Or.inr hw'))
      markArr_zero := fun k hk => by
        rw [hm3_pre _ (by simp [markArrBase, nodesBase]; omega) (by simp [markArrBase, endOwnerBase]; omega)
          (by simp [markArrBase, firstEndBase]; omega),
          hmem1_fixed_eq _ (by simp [markArrBase, nodesBase]; omega) (by simp [markArrBase, HDR_NUM_NODES]; omega)
            (by simp [markArrBase, nodeOfEndBase]; omega) (by simp [markArrBase, keyOfNodeBase]; omega)]
        exact h.markArr_zero k hk
      nodesAt := hn3, forestInv := hinv2, nodes_exact := hexact1
      comp_none := fun r' hr' hft0 => by
        by_cases hrv : r' = v
        · subst hrv; rw [hft_v] at hft0; simp at hft0
        · rw [hft_other r' hr' hrv] at hft0
          simpa [x', Function.update_of_ne hrv] using h.comp_none r' hr' hft0
      comp_some := fun r' hr' hft_ne => by
        by_cases hrv : r' = v
        · subst hrv; refine ⟨AuxTree.node u .leaf .leaf, by simp [x'], by simp [x'], ?_⟩
          rw [hft_v]; simp [AuxTree.toList, x', hk1u]
        · rw [hft_other r' hr' hrv] at hft_ne ⊢
          obtain ⟨t0, ht0_eq, ht0_mem, ht0_map⟩ := h.comp_some r' hr' hft_ne
          refine ⟨t0, by simp [x', Function.update_of_ne hrv, ht0_eq],
            List.mem_cons_of_mem _ (ht1_mem t0 ht0_mem (fun htu => hcomp_ne_u r' hr' hrv (htu ▸ ht0_eq))), ?_⟩
          rw [← ht0_map]; refine List.map_congr_left fun id hid => ?_
          have hid_old := (h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨t0, ht0_mem, hid⟩)
          simp [x', hk1_old id hid_old.1 hid_old.2]
      tree_class := fun tr htr => by
        rcases List.mem_cons.mp htr with rfl | htr1
        · exact Or.inl ⟨v, hvR, by simp [x']⟩
        · have ⟨htr_old, hu_ntr⟩ := ht1_sub tr htr1
          rcases h.tree_class tr htr_old with ⟨r', hr'R, hr'eq⟩ | ⟨id, hid_eq, hid_no⟩
          · have hrv : r' ≠ v := fun heq => by
              subst heq; rw [h.comp_none r' hr'R ((fullTour_eq_nil_iff h.valid.compat r').mpr hnil)] at hr'eq; cases hr'eq
            exact Or.inl ⟨r', hr'R, by simp [x', Function.update_of_ne hrv, hr'eq]⟩
          · have hid_ne : id ≠ u := fun heq => hu_ntr (by rw [hid_eq, heq]; simp [AuxTree.toList])
            have hid_old := (h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨tr, htr_old, by rw [hid_eq]; simp [AuxTree.toList]⟩)
            refine Or.inr ⟨id, hid_eq, fun w' hw' => ?_⟩
            rcases (hord'_mem w' _).mp hw' with ⟨_, heq⟩ | hw0
            · have hkeq : keyOf1 id = keyX := by rw [← endKey_endOfKey' (keyOf1 id), heq, endKey_endOfKey']
              have := (hk1_mem id hid_old.1 (le_trans hid_old.2 hxnn_le_nn1)).2.2
              rw [hkeq, hn1k] at this; exact hid_ne this.symm
            · rw [show x'.keyOf id = x.keyOf id from hk1_old id hid_old.1 hid_old.2] at hw0
              exact hid_no w' hw0
      inactive_single := fun id h1 h2 hno => by
        have hid_ne : id ≠ u := fun heq => by
          subst heq; exact hno v ((hord'_mem v _).mpr (Or.inl ⟨rfl, by simp [x', hk1u]⟩))
        have hid_old : id ≤ x.numNodes := by
          have := (hexact1 id).mpr ⟨h1, h2⟩
          simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.cons_append, List.mem_cons] at this
          rcases this with rfl | hmem; exact absurd rfl hid_ne
          obtain ⟨t0, ht0, hid0⟩ := List.mem_flatMap.mp hmem
          exact ((h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨t0, (ht1_sub t0 ht0).1, hid0⟩)).2
        have hno_old : ∀ w', endOfKey (x.keyOf id) ∉ s.ord w' := fun w' hw' =>
          hno w' ((hord'_mem w' _).mpr (Or.inr (by simpa [x', hk1_old id h1 hid_old] using hw')))
        exact List.mem_cons_of_mem _ (ht1_mem _ (h.inactive_single id h1 hid_old hno_old) (by simp [hid_ne]))
      val_active := fun id h1 h2 hact => by
        by_cases hiu : id = u
        · subst hiu
          have hrt_u : tourRootTagVal s' (endOfKey keyX) = v + 1 :=
            tourRootTagVal_eq_succ hvalid' hvR (by simp [s', tourApplyEdit, applyOrdEdit, insertBeforeList_head?, hnil])
          dsimp only [x', s2]
          rw [Function.update_self]
          simp only [tourSingletonNode, hk1u, hrt_u]
          simp [hxOpen, hxNotMarked, s', tourApplyEdit]
        · have hid_old : id ≤ x.numNodes := by
            have := (hexact1 id).mpr ⟨h1, h2⟩
            simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.cons_append, List.mem_cons] at this
            rcases this with rfl | hmem; exact absurd rfl hiu
            obtain ⟨t0, ht0, hid0⟩ := List.mem_flatMap.mp hmem
            exact ((h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨t0, (ht1_sub t0 ht0).1, hid0⟩)).2
          have hko : x'.keyOf id = x.keyOf id := hk1_old id h1 hid_old
          have hact0 : ∃ w', endOfKey (x.keyOf id) ∈ s.ord w' := by
            obtain ⟨w', hw'⟩ := hact
            rcases (hord'_mem w' _).mp hw' with ⟨_, heq⟩ | hw0
            · have hkeq : keyOf1 id = keyX := by rw [← endKey_endOfKey' (keyOf1 id), heq, endKey_endOfKey']
              have := (hk1_mem id h1 h2).2.2; rw [hkeq, hn1k] at this; exact absurd this.symm hiu
            · exact ⟨w', hko ▸ hw0⟩
          have hne_x : endOfKey (x.keyOf id) ≠ endOfKey keyX := fun heq => by
            obtain ⟨w', hw'⟩ := hact0; exact hxFresh w' (heq ▸ hw')
          have hrt_eq : tourRootTagVal s' (endOfKey (x.keyOf id)) = tourRootTagVal s (endOfKey (x.keyOf id)) := by
            by_cases hex : ∃ r' ∈ s.rf.R, (s.ord r').head? = some (endOfKey (x.keyOf id))
            · obtain ⟨r', hr'R, hr'h⟩ := hex
              have hrv : r' ≠ v := fun heq => by subst heq; simp [hnil] at hr'h
              rw [tourRootTagVal_eq_succ h.valid hr'R hr'h,
                tourRootTagVal_eq_succ hvalid' hr'R (by simpa [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hrv] using hr'h)]
            · push Not at hex
              rw [tourRootTagVal_eq_zero hex, tourRootTagVal_eq_zero]
              intro r' hr' hh
              by_cases hrv : r' = v
              · subst hrv; simp [s', tourApplyEdit, applyOrdEdit, insertBeforeList_head?, hnil] at hh
                exact hne_x hh.symm
              · exact hex r' hr' (by simpa [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hrv] using hh)
          have hnd : (s2.nodes id).val = (x.st.nodes id).val := by
            simp [s2, Function.update_of_ne hiu, hs1ne id hiu]
          rw [show (x'.st.nodes id).val = (x.st.nodes id).val from hnd, hko, h.val_active id h1 hid_old hact0, hrt_eq]; rfl
      val_inactive_rt := fun id h1 h2 hno => by
        have hiu : id ≠ u := fun heq => by subst heq; exact hno v ((hord'_mem v _).mpr (Or.inl ⟨rfl, by simp [x', hk1u]⟩))
        have hid_old : id ≤ x.numNodes := by
          have := (hexact1 id).mpr ⟨h1, h2⟩
          simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.cons_append, List.mem_cons] at this
          rcases this with rfl | hmem; exact absurd rfl hiu
          obtain ⟨t0, ht0, hid0⟩ := List.mem_flatMap.mp hmem
          exact ((h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨t0, (ht1_sub t0 ht0).1, hid0⟩)).2
        have hnd : (s2.nodes id).val = (x.st.nodes id).val := by simp [s2, Function.update_of_ne hiu, hs1ne id hiu]
        rw [show (x'.st.nodes id).val = (x.st.nodes id).val from hnd]
        exact h.val_inactive_rt id h1 hid_old fun w' hw' =>
          hno w' ((hord'_mem w' _).mpr (Or.inr (by simpa [x', hk1_old id h1 hid_old] using hw')))
      val_unused_rt := fun id hid hcase => by
        dsimp only [x'] at hid hcase
        have hiu : id ≠ u := by omega
        have hnd : (s2.nodes id).val = (x.st.nodes id).val := by simp [s2, Function.update_of_ne hiu, hs1ne id hiu]
        rw [show (x'.st.nodes id).val = (x.st.nodes id).val from hnd]
        rcases hcase with rfl | hgt
        · exact h.val_unused_rt 0 (Nat.zero_le _) (Or.inl rfl)
        · omega }
  refine ⟨{ stI2 with mem := mem3, regs := r3 }, _, x', hfull, rfl,
    fun a ha => by dsimp only; rw [hm3_out a (Or.inr (by omega))]; exact hzero a ha,
    fun a ha _ => hm3_out a ha, hcore', ?_⟩
  dsimp only [x']; rw [hphi1]
  clear * - hc1 hcI2 htl; simp only [Expr.size, TOUR_SPLICE_COST, TOUR_EDIT_SIMPLE_MUL] at *; omega

end MinCostFlow.SparseCore.Program
