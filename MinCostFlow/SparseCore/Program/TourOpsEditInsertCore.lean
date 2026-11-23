module

public import MinCostFlow.SparseCore.Program.TourOpsEditInsertEmpty
import Mathlib.Tactic

/-!
# Core-invariant helper for nonempty-vertex `insertBefore` (Op 0)

Provides `tourEditInsert_nonempty_core`, constructing `TourCoreAt` after the nonempty-vertex
`insertBefore` splice, optional `firstEnd`/`rootTag`/`rotateFront` update, and final
`endOwner[keyX] := sv + 1` store.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-- Construct `TourCoreAt` for the nonempty-vertex branch of `tourEditInsertBody` once the final
splay tree `tF`, state `sF`, and memory `memEnd` are produced. -/
theorem tourEditInsert_nonempty_core {τ_ord : Type}
    {vCap eCap b v keyX yWord u nn1 feOld headCh : ℕ}
    {s : TourAbs} {x : TourConcrete τ_ord} {mem mem1 memEnd : ℕ → ℕ}
    {nodeOf1 keyOf1 : ℕ → ℕ} {t t₂ tF : AuxTree} {trees1 rest1 : List AuxTree}
    {P Q : List ℕ} {sF : SplayState TourVal TourSum Unit} {aOld yEnd : End} {yNode : ℕ}
    (h : TourCoreAt vCap eCap b s x mem)
    (hkeyLt : keyX < 2 * eCap)
    (hedit : TourEditValid vCap eCap s
      (.insertBefore v (endOfKey keyX) (if yWord = 0 then none else some (endOfKey (yWord - 1)))))
    (hu1 : 1 ≤ u) (_hunn : u ≤ nn1) (hnn_le : nn1 ≤ 2 * eCap)
    (hn1k : nodeOf1 keyX = u) (hk1u : keyOf1 u = keyX)
    (hn1_ne : ∀ k ≠ keyX, nodeOf1 k = x.nodeOf k)
    (hk1_old : ∀ id, 1 ≤ id → id ≤ x.numNodes → keyOf1 id = x.keyOf id)
    (hn1_mem : ∀ k < 2 * eCap, mem1 (nodeOfEndBase b vCap + k) = nodeOf1 k ∧ nodeOf1 k ≤ nn1)
    (hn1_ko : ∀ k < 2 * eCap, nodeOf1 k ≠ 0 → keyOf1 (nodeOf1 k) = k)
    (hk1_mem : ∀ id, 1 ≤ id → id ≤ nn1 →
      mem1 (keyOfNodeBase b vCap eCap + id) = keyOf1 id ∧ keyOf1 id < 2 * eCap ∧ nodeOf1 (keyOf1 id) = id)
    (hhdr1 : TourHeaderAt vCap eCap b nn1 mem1)
    (hexact1 : ∀ id, id ∈ (AuxTree.node u .leaf .leaf :: trees1).flatMap AuxTree.toList ↔ 1 ≤ id ∧ id ≤ nn1)
    (ht1_sub : ∀ tr ∈ trees1, tr ∈ x.trees ∧ u ∉ tr.toList)
    (ht1_mem : ∀ tr ∈ x.trees, tr ≠ AuxTree.node u .leaf .leaf → tr ∈ trees1)
    (hmem1_fixed_eq : ∀ a, a < nodesBase b vCap eCap →
      a ≠ b + HDR_NUM_NODES → a ≠ nodeOfEndBase b vCap + keyX → a ≠ keyOfNodeBase b vCap eCap + u →
      mem1 a = mem a)
    (haOld : (s.ord v).head? = some aOld) (haOld_lt : endKey aOld < 2 * eCap)
    (hfeOld_eq : feOld = x.nodeOf (endKey aOld)) (hfeOld_eq1 : feOld = nodeOf1 (endKey aOld))
    (hfeOld_nz : feOld ≠ 0) (hyEnd_mem : yEnd ∈ s.ord v)
    (hyNode_old : yNode = x.nodeOf (endKey yEnd)) (hy_ko_old : x.keyOf (x.nodeOf (endKey yEnd)) = endKey yEnd)
    (hch_iff : headCh = 1 ↔ (if yWord = 0 then none else some (endOfKey (yWord - 1))) = some aOld)
    (hct_r : x.compTree (s.rf.root v) = some t)
    (hperm_u : (AuxTree.node u .leaf .leaf :: trees1).Perm (AuxTree.node u .leaf .leaf :: t :: rest1))
    (hrest1_eq : rest1 = trees1.erase t) (hyNode_t : yNode ∈ t.toList)
    (ht_PQ : t.toList = P ++ yNode :: Q) (ht₂_PQ : t₂.toList = P ++ u :: yNode :: Q)
    (htF_perm : tF.toList.Perm t₂.toList)
    (hinv1_nd : (AuxTree.node u .leaf .leaf :: t :: rest1).flatMap AuxTree.toList |>.Nodup)
    (hcomp_inj : ∀ r' ∈ s.rf.R, r' ≠ s.rf.root v → x.compTree r' ≠ some t)
    (hnEnd : tourLayout.NodesAt memEnd (nodesBase b vCap eCap) nn1 sF)
    (hinvF : TourForestInv nn1 sF (tF :: rest1))
    (htF_map : tF.toList.map (fun id => endOfKey (keyOf1 id)) =
      fullTour (tourApplyEdit s (.insertBefore v (endOfKey keyX)
        (if yWord = 0 then none else some (endOfKey (yWord - 1))))).ord s.rf.F
        (tourValid_applyEdit_insertBefore h.valid hedit).compat.forest (s.rf.root v))
    (hmEnd_pre : ∀ a < nodesBase b vCap eCap, a ≠ endOwnerBase b vCap eCap + keyX →
      a ≠ firstEndBase b + v → memEnd a = mem1 a)
    (hmEnd_fev : memEnd (firstEndBase b + v) = if headCh = 1 then u else feOld)
    (hmEnd_eo : memEnd (endOwnerBase b vCap eCap + keyX) = x.slotOf v + 1)
    (hvalF : ∀ id, 1 ≤ id → id ≤ nn1 → (sF.nodes id).val =
      if id = u then ⟨true, false, tourRootTagVal (tourApplyEdit s (.insertBefore v (endOfKey keyX)
        (if yWord = 0 then none else some (endOfKey (yWord - 1))))) (endOfKey keyX)⟩
      else if id = feOld then { (x.st.nodes feOld).val with
        rootTag := tourRootTagVal (tourApplyEdit s (.insertBefore v (endOfKey keyX)
          (if yWord = 0 then none else some (endOfKey (yWord - 1))))) aOld }
      else (x.st.nodes id).val)
    (hvalF_un : ∀ id ≤ nn1, id = 0 ∨ nn1 < id → (sF.nodes id).val.rootTag = 0) :
    let yOpt : Option End := if yWord = 0 then none else some (endOfKey (yWord - 1))
    let s' := tourApplyEdit s (.insertBefore v (endOfKey keyX) yOpt)
    let x' : TourConcrete τ_ord :=
      { ordX := x.ordX, numNodes := nn1, st := sF, trees := tF :: rest1,
        nodeOf := nodeOf1, keyOf := keyOf1,
        compTree := Function.update x.compTree (s.rf.root v) (some tF),
        slotOf := x.slotOf, vertOf := x.vertOf }
    TourCoreAt vCap eCap b s' x' memEnd := by
  intro yOpt s' x'
  have hvLt : v < vCap := hedit.1
  have hvF : v ∈ s.rf.F.V := hedit.2.1
  have hxOpen : (endOfKey keyX).1 ∉ s.rf.F.E := hedit.2.2.2.1
  have hxFresh : ∀ w', endOfKey keyX ∉ s.ord w' := hedit.2.2.2.2.1
  have haOld_mem : aOld ∈ s.ord v := List.mem_of_head? haOld
  have hvalid' : TourValid vCap eCap s' := tourValid_applyEdit_insertBefore h.valid hedit
  set r := s.rf.root v
  have hrR : r ∈ s.rf.R := (h.valid.root_spec hvF).1
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
  have hft_other : ∀ r' ∈ s.rf.R, r' ≠ r →
      fullTour s'.ord s'.rf.F hvalid'.compat.forest r' = fullTour s.ord s.rf.F h.valid.compat.forest r' := by
    intro r' hr' hne
    exact fullTour_insertOpen_other h.valid hedit fun hconn =>
      hne ((h.valid.unique_root v hvF).unique ⟨hr', connected_symm hconn⟩ (h.valid.root_spec hvF))
  have hhdrEnd : TourHeaderAt vCap eCap b nn1 memEnd := by
    rcases hhdr1 with ⟨h0', h1', h2', h3', h4', h5', h6', h7', h8', h9', h10', h11', h12', h13', h14'⟩
    have hf : ∀ k < 16, memEnd (b + k) = mem1 (b + k) := fun k hk =>
      hmEnd_pre _ (by simp [nodesBase]; omega) (by simp [endOwnerBase]; omega) (by simp [firstEndBase]; omega)
    exact ⟨by rw [hf _ (by decide)]; exact h0', by rw [hf _ (by decide)]; exact h1',
      by rw [hf _ (by decide)]; exact h2', by rw [hf _ (by decide)]; exact h3',
      by rw [hf _ (by decide)]; exact h4', by rw [hf _ (by decide)]; exact h5',
      by rw [hf _ (by decide)]; exact h6', by rw [hf _ (by decide)]; exact h7',
      by rw [hf _ (by decide)]; exact h8', by rw [hf _ (by decide)]; exact h9',
      by rw [hf _ (by decide)]; exact h10', by rw [hf _ (by decide)]; exact h11',
      by rw [hf _ (by decide)]; exact h12', by rw [hf _ (by decide)]; exact h13',
      by rw [hf _ (by decide)]; exact h14'⟩
  have hnodes_exactF : ∀ id, id ∈ (tF :: rest1).flatMap AuxTree.toList ↔ 1 ≤ id ∧ id ≤ nn1 := by
    intro id
    have hp1 : ((tF :: rest1).flatMap AuxTree.toList).Perm
        ((AuxTree.node u .leaf .leaf :: t :: rest1).flatMap AuxTree.toList) := by
      simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.append_nil]
      change (tF.toList ++ rest1.flatMap AuxTree.toList).Perm ((u :: t.toList) ++ rest1.flatMap AuxTree.toList)
      refine (htF_perm.trans ?_).append_right _
      rw [ht₂_PQ, ht_PQ]; exact List.perm_middle
    have hmem2 : id ∈ (AuxTree.node u .leaf .leaf :: t :: rest1).flatMap AuxTree.toList ↔
        id ∈ (AuxTree.node u .leaf .leaf :: trees1).flatMap AuxTree.toList := by
      simp only [List.mem_flatMap]
      exact ⟨fun ⟨a, ha, hid⟩ => ⟨a, hperm_u.mem_iff.mpr ha, hid⟩,
        fun ⟨a, ha, hid⟩ => ⟨a, hperm_u.mem_iff.mp ha, hid⟩⟩
    exact hp1.mem_iff.trans (hmem2.trans (hexact1 id))
  have hid_old_of_ne_u : ∀ id, 1 ≤ id → id ≤ nn1 → id ≠ u → id ≤ x.numNodes := fun id h1 h2 hiu => by
    have := (hexact1 id).mpr ⟨h1, h2⟩
    simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.cons_append, List.mem_cons] at this
    rcases this with rfl | hmem; exact absurd rfl hiu
    obtain ⟨t0, ht0, hid0⟩ := List.mem_flatMap.mp hmem
    exact ((h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨t0, (ht1_sub t0 ht0).1, hid0⟩)).2
  exact
    { valid := hvalid', header := hhdrEnd, numNodes_le := hnn_le
      nodeOf_mem := fun k hk => by
        rw [hmEnd_pre _ (by simp [nodeOfEndBase, nodesBase]; omega)
          (by simp [nodeOfEndBase, endOwnerBase]; omega) (by simp [nodeOfEndBase, firstEndBase]; omega)]
        exact hn1_mem k hk
      nodeOf_keyOf := hn1_ko
      keyOf_mem := fun id h1 h2 => by
        dsimp only [x'] at h2
        rw [hmEnd_pre _ (by simp [keyOfNodeBase, nodesBase]; omega)
          (by simp [keyOfNodeBase, endOwnerBase]; omega) (by simp [keyOfNodeBase, firstEndBase]; omega)]
        exact hk1_mem id h1 h2
      firstEnd_mem := fun w' hw' => by
        by_cases hwv : w' = v
        · subst hwv; rw [hmEnd_fev]
          simp only [s', tourApplyEdit, applyOrdEdit, Function.update_self, insertBeforeList_head?, haOld, x']
          by_cases h1 : headCh = 1
          · have hyo : yOpt = some aOld := hch_iff.mp h1
            simp [h1, hyo, hn1k, endKey_endOfKey']
          · have hyo : yOpt ≠ some aOld := mt hch_iff.mpr h1
            simp [h1, hyo, hfeOld_eq1]
        · rw [hmEnd_pre _ (by simp [firstEndBase, nodesBase]; omega) (by simp [firstEndBase, endOwnerBase]; omega) (by omega),
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
        rw [hmEnd_pre _ (by simp [isRootBase, nodesBase]; omega) (by simp [isRootBase, endOwnerBase]; omega)
          (by simp [isRootBase, firstEndBase]; omega),
          hmem1_fixed_eq _ (by simp [isRootBase, nodesBase]; omega) (by simp [isRootBase, HDR_NUM_NODES]; omega)
            (by simp [isRootBase, nodeOfEndBase]; omega) (by simp [isRootBase, keyOfNodeBase]; omega)]
        exact h.isRoot_mem w' hw'
      slot_bij := h.slot_bij
      slotOf_mem := fun w' hw' => by
        rw [hmEnd_pre _ (by simp [slotOfVertBase, nodesBase]; omega) (by simp [slotOfVertBase, endOwnerBase]; omega)
          (by simp [slotOfVertBase, firstEndBase]; omega),
          hmem1_fixed_eq _ (by simp [slotOfVertBase, nodesBase]; omega) (by simp [slotOfVertBase, HDR_NUM_NODES]; omega)
            (by simp [slotOfVertBase, nodeOfEndBase]; omega) (by simp [slotOfVertBase, keyOfNodeBase]; omega)]
        exact h.slotOf_mem w' hw'
      vertOf_mem := fun sl hsl => by
        rw [hmEnd_pre _ (by simp [vertOfSlotBase, nodesBase]; omega) (by simp [vertOfSlotBase, endOwnerBase]; omega)
          (by simp [vertOfSlotBase, firstEndBase]; omega),
          hmem1_fixed_eq _ (by simp [vertOfSlotBase, nodesBase]; omega) (by simp [vertOfSlotBase, HDR_NUM_NODES]; omega)
            (by simp [vertOfSlotBase, nodeOfEndBase]; omega) (by simp [vertOfSlotBase, keyOfNodeBase]; omega)]
        exact h.vertOf_mem sl hsl
      active_end := fun w' hw' z hz => by
        rcases (hord'_mem w' z).mp hz with ⟨rfl, rfl⟩ | hz0
        · refine ⟨by simp [x', hn1k, endKey_endOfKey']; omega, by simpa [x', endKey_endOfKey'] using hmEnd_eo⟩
        · have hne : endKey z ≠ keyX := fun heq => hxFresh w' (by rw [← heq, endOfKey_endKey]; exact hz0)
          have hzLt : endKey z < 2 * eCap := by
            have := h.valid.ordWithin.2.2 w' z hz0; simp only [endKey]; cases z.2 <;> simp <;> omega
          rw [hmEnd_pre _ (by simp [endOwnerBase, nodesBase]; omega) (by omega) (by simp [endOwnerBase, firstEndBase]; omega),
            hmem1_fixed_eq _ (by simp [endOwnerBase, nodesBase]; omega) (by simp [endOwnerBase, HDR_NUM_NODES]; omega)
              (by simp [endOwnerBase, nodeOfEndBase]; omega) (by simp [endOwnerBase, keyOfNodeBase]; omega)]
          simpa [x', hn1_ne _ hne] using h.active_end w' hw' z hz0
      inactive_owner := fun k hk hno => by
        have hne : k ≠ keyX := fun heq => hno v ((hord'_mem v _).mpr (Or.inl ⟨rfl, by rw [heq]⟩))
        rw [hmEnd_pre _ (by simp [endOwnerBase, nodesBase]; omega) (by omega) (by simp [endOwnerBase, firstEndBase]; omega),
          hmem1_fixed_eq _ (by simp [endOwnerBase, nodesBase]; omega) (by simp [endOwnerBase, HDR_NUM_NODES]; omega)
            (by simp [endOwnerBase, nodeOfEndBase]; omega) (by simp [endOwnerBase, keyOfNodeBase]; omega)]
        exact h.inactive_owner k hk fun w' hw' => hno w' ((hord'_mem w' _).mpr (Or.inr hw'))
      markArr_zero := fun k hk => by
        rw [hmEnd_pre _ (by simp [markArrBase, nodesBase]; omega) (by simp [markArrBase, endOwnerBase]; omega)
          (by simp [markArrBase, firstEndBase]; omega),
          hmem1_fixed_eq _ (by simp [markArrBase, nodesBase]; omega) (by simp [markArrBase, HDR_NUM_NODES]; omega)
            (by simp [markArrBase, nodeOfEndBase]; omega) (by simp [markArrBase, keyOfNodeBase]; omega)]
        exact h.markArr_zero k hk
      nodesAt := hnEnd, forestInv := hinvF, nodes_exact := hnodes_exactF
      comp_none := fun r' hr' hft0 => by
        by_cases hrr' : r' = r
        · subst hrr'
          have hft0' : tF.toList.map (fun id => endOfKey (keyOf1 id)) = [] := by
            rw [htF_map]; exact hft0
          have hnilF : tF.toList = [] := List.map_eq_nil_iff.mp hft0'
          have hneF := hinvF.nonEmpty tF (by simp)
          cases tF <;> simp [AuxTree.toList] at hneF hnilF
        · rw [hft_other r' hr' hrr'] at hft0
          simpa [x', r, hrr'] using h.comp_none r' hr' hft0
      comp_some := fun r' hr' hft_ne => by
        by_cases hrr' : r' = r
        · subst hrr'; exact ⟨tF, by simp [x', r], by simp [x'], htF_map⟩
        · rw [hft_other r' hr' hrr'] at hft_ne ⊢
          obtain ⟨t0, ht0_eq, ht0_mem, ht0_map⟩ := h.comp_some r' hr' hft_ne
          have ht0_ne_t : t0 ≠ t := fun heq => hcomp_inj r' hr' hrr' (heq ▸ ht0_eq)
          have ht0_ne_u : t0 ≠ AuxTree.node u .leaf .leaf := fun heq => by
            have hu_ft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r' := by
              rw [← ht0_map, heq]; simp [AuxTree.toList]
            obtain ⟨w', hw', _⟩ := ((fullTour_spec h.valid.compat r').2 _).mp hu_ft
            have hu_old := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t0, ht0_mem, by rw [heq]; simp [AuxTree.toList]⟩)
            have : x.keyOf u = keyX := by rw [← hk1_old u hu_old.1 hu_old.2, hk1u]
            exact hxFresh w' (this ▸ hw')
          have ht0_rest1 : t0 ∈ rest1 := by
            rw [hrest1_eq]; exact (List.mem_erase_of_ne ht0_ne_t).mpr (ht1_mem t0 ht0_mem ht0_ne_u)
          refine ⟨t0, by simp [x', r, hrr', ht0_eq], List.mem_cons_of_mem _ ht0_rest1, ?_⟩
          rw [← ht0_map]; refine List.map_congr_left fun id hid => ?_
          have hid_old := (h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨t0, ht0_mem, hid⟩)
          simp [x', hk1_old id hid_old.1 hid_old.2]
      tree_class := fun tr htr => by
        rcases List.mem_cons.mp htr with rfl | htr1
        · exact Or.inl ⟨r, hrR, by simp [x', r]⟩
        · have htr_t1 : tr ∈ trees1 := by rw [hrest1_eq] at htr1; exact List.mem_of_mem_erase htr1
          have ⟨htr_old, hu_ntr⟩ := ht1_sub tr htr_t1
          have htr_ne_t : tr ≠ t := by
            simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.cons_append] at hinv1_nd
            have hnd3 := List.nodup_append.mp (List.nodup_cons.mp hinv1_nd).2
            intro heq; subst heq
            exact hnd3.2.2 yNode hyNode_t yNode (List.mem_flatMap.mpr ⟨_, htr1, hyNode_t⟩) rfl
          rcases h.tree_class tr htr_old with ⟨r', hr'R, hr'eq⟩ | ⟨id, hid_eq, hid_no⟩
          · have hrr' : r' ≠ r := fun heq => htr_ne_t (Option.some.inj (by rw [← hr'eq, heq, hct_r]))
            exact Or.inl ⟨r', hr'R, by simp [x', r, hrr', hr'eq]⟩
          · have hid_ne : id ≠ u := fun heq => hu_ntr (by rw [hid_eq, heq]; simp [AuxTree.toList])
            have hid_old := (h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨tr, htr_old, by rw [hid_eq]; simp [AuxTree.toList]⟩)
            refine Or.inr ⟨id, hid_eq, fun w' hw' => ?_⟩
            rcases (hord'_mem w' _).mp hw' with ⟨_, heq⟩ | hw0
            · have hkeq : keyOf1 id = keyX := by rw [← endKey_endOfKey' (keyOf1 id), heq, endKey_endOfKey']
              have hid_nn : id ≤ nn1 := ((hexact1 id).mp (List.mem_flatMap.mpr ⟨tr, List.mem_cons_of_mem _ htr_t1, by rw [hid_eq]; simp [AuxTree.toList]⟩)).2
              have := (hk1_mem id hid_old.1 hid_nn).2.2; rw [hkeq, hn1k] at this; exact hid_ne this.symm
            · rw [show x'.keyOf id = x.keyOf id from hk1_old id hid_old.1 hid_old.2] at hw0; exact hid_no w' hw0
      inactive_single := fun id h1 h2 hno => by
        have hiu : id ≠ u := fun heq => by subst heq; exact hno v ((hord'_mem v _).mpr (Or.inl ⟨rfl, by simp [x', hk1u]⟩))
        have hid_old := hid_old_of_ne_u id h1 h2 hiu
        have hno_old : ∀ w', endOfKey (x.keyOf id) ∉ s.ord w' := fun w' hw' =>
          hno w' ((hord'_mem w' _).mpr (Or.inr (by simpa [x', hk1_old id h1 hid_old] using hw')))
        have hsing_ne_t : AuxTree.node id .leaf .leaf ≠ t := fun heq => by
          rw [← heq] at hyNode_t; simp [AuxTree.toList] at hyNode_t
          exact hno_old v (by rw [← hyNode_t, hyNode_old, hy_ko_old, endOfKey_endKey]; exact hyEnd_mem)
        refine List.mem_cons_of_mem _ ?_
        rw [hrest1_eq]
        exact (List.mem_erase_of_ne hsing_ne_t).mpr (ht1_mem _ (h.inactive_single id h1 hid_old hno_old) (by simp [hiu]))
      val_active := fun id h1 h2 hact => by
        rw [show (x'.st.nodes id).val = _ from hvalF id h1 h2]
        by_cases hiu : id = u
        · subst hiu; simp [x', hk1u, hxOpen, hxNotMarked, s', yOpt, tourApplyEdit]
        · simp only [hiu, ↓reduceIte]
          have hid_old := hid_old_of_ne_u id h1 h2 hiu
          have hko : x'.keyOf id = x.keyOf id := hk1_old id h1 hid_old
          have hact0 : ∃ w', endOfKey (x.keyOf id) ∈ s.ord w' := by
            obtain ⟨w', hw'⟩ := hact
            rcases (hord'_mem w' _).mp hw' with ⟨_, heq⟩ | hw0
            · have hkeq : keyOf1 id = keyX := by rw [← endKey_endOfKey' (keyOf1 id), heq, endKey_endOfKey']
              have := (hk1_mem id h1 h2).2.2; rw [hkeq, hn1k] at this; exact absurd this.symm hiu
            · exact ⟨w', hko ▸ hw0⟩
          by_cases hife : id = feOld
          · subst hife
            have hkfe : x.keyOf id = endKey aOld := by rw [hfeOld_eq]; exact h.nodeOf_keyOf _ haOld_lt (hfeOld_eq ▸ hfeOld_nz)
            simp only [↓reduceIte, hko, hkfe, endOfKey_endKey]
            rw [h.val_active id h1 hid_old hact0, hkfe, endOfKey_endKey]; rfl
          · simp only [hife, ↓reduceIte, hko]
            rw [h.val_active id h1 hid_old hact0]
            have hne_aOld : endOfKey (x.keyOf id) ≠ aOld := fun heq => hife (by
              rw [hfeOld_eq, ← heq, endKey_endOfKey', (h.keyOf_mem id h1 hid_old).2.2])
            have hne_x : endOfKey (x.keyOf id) ≠ endOfKey keyX := fun heq => by
              obtain ⟨w', hw'⟩ := hact0; exact hxFresh w' (heq ▸ hw')
            have hrt_eq : tourRootTagVal s' (endOfKey (x.keyOf id)) = tourRootTagVal s (endOfKey (x.keyOf id)) := by
              by_cases hex : ∃ r' ∈ s.rf.R, (s.ord r').head? = some (endOfKey (x.keyOf id))
              · obtain ⟨r', hr'R, hr'h⟩ := hex
                have hrv : r' ≠ v := fun heq => by subst heq; rw [haOld] at hr'h; exact hne_aOld (Option.some.inj hr'h).symm
                rw [tourRootTagVal_eq_succ h.valid hr'R hr'h,
                  tourRootTagVal_eq_succ hvalid' hr'R (by simpa [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hrv] using hr'h)]
              · push Not at hex
                rw [tourRootTagVal_eq_zero hex, tourRootTagVal_eq_zero]
                intro r' hr' hh
                by_cases hrv : r' = v
                · subst hrv; simp only [s', tourApplyEdit, applyOrdEdit, Function.update_self, insertBeforeList_head?, haOld] at hh
                  split_ifs at hh <;> exact absurd (Option.some.inj hh).symm (by assumption)
                · exact hex r' hr' (by simpa [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hrv] using hh)
            rw [hrt_eq]; rfl
      val_inactive_rt := fun id h1 h2 hno => by
        have hiu : id ≠ u := fun heq => by subst heq; exact hno v ((hord'_mem v _).mpr (Or.inl ⟨rfl, by simp [x', hk1u]⟩))
        have hife : id ≠ feOld := fun heq => by
          subst heq
          have hkfe : keyOf1 id = endKey aOld := by rw [hfeOld_eq1]; exact hn1_ko _ haOld_lt (hfeOld_eq1 ▸ hfeOld_nz)
          exact hno v ((hord'_mem v _).mpr (Or.inr (by simpa [x', hkfe, endOfKey_endKey] using haOld_mem)))
        have hid_old := hid_old_of_ne_u id h1 h2 hiu
        rw [show (x'.st.nodes id).val = (x.st.nodes id).val by simp [x', hvalF id h1 h2, hiu, hife]]
        exact h.val_inactive_rt id h1 hid_old fun w' hw' =>
          hno w' ((hord'_mem w' _).mpr (Or.inr (by simpa [x', hk1_old id h1 hid_old] using hw')))
      val_unused_rt := hvalF_un }

end MinCostFlow.SparseCore.Program
