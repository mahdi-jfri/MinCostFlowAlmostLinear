module

public import MinCostFlow.SparseCore.Program.TourOpsEditDropExec
public import MinCostFlow.SparseCore.Program.TourOpsEditRotate
import Mathlib.Tactic

/-!
# Core `TourCoreAt` builder and `ordNext` helper for `dropEdge` (Op 0)

Provides `tourDropOne_core` (rebuilding `TourCoreAt` after removing one active open end) and
`tourDropOne_findNewFe_exec` (finding the replacement `firstEnd[v]` via 1 or 2 `ordNext` queries).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Shared `TourCoreAt` builder for single-end drop -/

/-- Construct `TourCoreAt` after dropping active open end `xEnd = endOfKey keyX` at vertex `v`
(node `u = x.nodeOf keyX`), leaving `AuxTree.node u .leaf .leaf` as a detached singleton and
updating `compTree (s.rf.root v)` to `tF?`. -/
theorem tourDropOne_core {τ_ord : Type}
    {vCap eCap b v keyX u : ℕ}
    {s : TourAbs} {x : TourConcrete τ_ord} {mem memF : ℕ → ℕ}
    {t : AuxTree} {tF? : Option AuxTree} {rest : List AuxTree}
    {sF : SplayState TourVal TourSum Unit} {ordX' : τ_ord}
    (h : TourCoreAt vCap eCap b s x mem)
    (hkeyLt : keyX < 2 * eCap) (hvLt : v < vCap)
    (hxv : endOfKey keyX ∈ s.ord v) (hxOpen : (endOfKey keyX).1 ∉ s.rf.F.E)
    (hu_eq : u = x.nodeOf keyX) (hu1 : 1 ≤ u) (hu_le : u ≤ x.numNodes) (hu_key : x.keyOf u = keyX)
    (hct_r : x.compTree (s.rf.root v) = some t)
    (hperm_r : x.trees.Perm (t :: rest)) (hu_t : u ∈ t.toList)
    (hcomp_inj : ∀ r' ∈ s.rf.R, r' ≠ s.rf.root v → x.compTree r' ≠ some t)
    (hnF : tourLayout.NodesAt memF (nodesBase b vCap eCap) x.numNodes sF)
    (hinvF : TourForestInv x.numNodes sF (AuxTree.node u .leaf .leaf :: optTrees tF? ++ rest))
    (htF_perm : (optList tF?).Perm (t.toList.erase u))
    (htF_map : (optList tF?).map (fun id => endOfKey (x.keyOf id)) =
      fullTour (tourDropOneAbs s (endOfKey keyX)).ord s.rf.F
        (tourValid_dropOneAbs h.valid hxOpen).compat.forest (s.rf.root v))
    (hmF_pre : ∀ a < nodesBase b vCap eCap, a ≠ endOwnerBase b vCap eCap + keyX →
      a ≠ firstEndBase b + v → memF a = mem a)
    (hmF_eo0 : memF (endOwnerBase b vCap eCap + keyX) = 0)
    (hmF_fev : memF (firstEndBase b + v) = match ((tourDropOneAbs s (endOfKey keyX)).ord v).head? with
      | none => 0 | some e => x.nodeOf (endKey e))
    (hvalF_active : ∀ id, 1 ≤ id → id ≤ x.numNodes → id ≠ u →
      (∃ w', endOfKey (x.keyOf id) ∈ (tourDropOneAbs s (endOfKey keyX)).ord w') →
      (sF.nodes id).val =
        { isOpen := decide ((endOfKey (x.keyOf id)).1 ∉ s.rf.F.E)
          isMarked := decide (endOfKey (x.keyOf id) ∈ (tourDropOneAbs s (endOfKey keyX)).marked)
          rootTag := tourRootTagVal (tourDropOneAbs s (endOfKey keyX)) (endOfKey (x.keyOf id)) })
    (hvalF_u_rt : (sF.nodes u).val.rootTag = 0)
    (hvalF_other : ∀ id ≤ x.numNodes, (∀ w', endOfKey (x.keyOf id) ∉ s.ord w') ∨ id = 0 ∨ x.numNodes < id →
      (sF.nodes id).val = (x.st.nodes id).val) :
    let s' := tourDropOneAbs s (endOfKey keyX)
    let x' : TourConcrete τ_ord :=
      { ordX := ordX', numNodes := x.numNodes, st := sF,
        trees := AuxTree.node u .leaf .leaf :: optTrees tF? ++ rest,
        nodeOf := x.nodeOf, keyOf := x.keyOf,
        compTree := Function.update x.compTree (s.rf.root v) tF?,
        slotOf := x.slotOf, vertOf := x.vertOf }
    TourCoreAt vCap eCap b s' x' memF := by
  intro s' x'
  have hvF : v ∈ s.rf.F.V := h.valid.compat.vert v (List.ne_nil_of_mem hxv)
  set r := s.rf.root v
  have hrR : r ∈ s.rf.R := (h.valid.root_spec hvF).1
  have hvalid' : TourValid vCap eCap s' := tourValid_dropOneAbs h.valid hxOpen
  have hord'_mem : ∀ w' z, z ∈ s'.ord w' ↔ z ∈ s.ord w' ∧ z ≠ endOfKey keyX := fun w' z => by
    simp [s', tourDropOneAbs, bne_iff_ne]
  have hord'_upd : s'.ord = Function.update s.ord v ((s.ord v).filter fun z => z != endOfKey keyX) :=
    tourDropOneAbs_ord_eq_update h.valid hxv
  have hft_other : ∀ r' ∈ s.rf.R, r' ≠ r →
      fullTour s'.ord s'.rf.F hvalid'.compat.forest r' = fullTour s.ord s.rf.F h.valid.compat.forest r' := by
    intro r' hr' hne
    have hnc : ¬s.rf.F.Connected r' v := fun hc =>
      hne ((h.valid.unique_root v hvF).unique ⟨hr', connected_symm hc⟩ (h.valid.root_spec hvF))
    have h1 := fullTour_dropOneOpen_other h.valid.compat hxv hxOpen hnc
    change fullTour s'.ord s.rf.F _ r' = _
    simpa only [hord'_upd] using h1
  have hhdrF : TourHeaderAt vCap eCap b x.numNodes memF := by
    rcases h.header with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    have hf : ∀ k < 16, memF (b + k) = mem (b + k) := fun k hk =>
      hmF_pre _ (by simp [nodesBase]; omega) (by simp [endOwnerBase]; omega) (by simp [firstEndBase]; omega)
    exact ⟨by rw [hf _ (by decide)]; exact h0, by rw [hf _ (by decide)]; exact h1,
      by rw [hf _ (by decide)]; exact h2, by rw [hf _ (by decide)]; exact h3,
      by rw [hf _ (by decide)]; exact h4, by rw [hf _ (by decide)]; exact h5,
      by rw [hf _ (by decide)]; exact h6, by rw [hf _ (by decide)]; exact h7,
      by rw [hf _ (by decide)]; exact h8, by rw [hf _ (by decide)]; exact h9,
      by rw [hf _ (by decide)]; exact h10, by rw [hf _ (by decide)]; exact h11,
      by rw [hf _ (by decide)]; exact h12, by rw [hf _ (by decide)]; exact h13,
      by rw [hf _ (by decide)]; exact h14⟩
  have hnodes_exactF : ∀ id, id ∈ (AuxTree.node u .leaf .leaf :: optTrees tF? ++ rest).flatMap AuxTree.toList ↔
      1 ≤ id ∧ id ≤ x.numNodes := by
    intro id
    have hflat_opt : (optTrees tF?).flatMap AuxTree.toList = optList tF? := by
      cases tF? <;> simp [optTrees, optList]
    have hp1 : ((AuxTree.node u .leaf .leaf :: optTrees tF? ++ rest).flatMap AuxTree.toList).Perm
        ((t :: rest).flatMap AuxTree.toList) := by
      simp only [List.flatMap_cons, List.flatMap_append, AuxTree.toList, List.nil_append, List.cons_append,
        hflat_opt]
      exact ((htF_perm.cons u).trans (List.perm_cons_erase hu_t).symm).append_right _
    have hmem2 : id ∈ (t :: rest).flatMap AuxTree.toList ↔ id ∈ x.trees.flatMap AuxTree.toList := by
      simp only [List.mem_flatMap]
      exact ⟨fun ⟨a, ha, hid⟩ => ⟨a, hperm_r.mem_iff.mpr ha, hid⟩,
        fun ⟨a, ha, hid⟩ => ⟨a, hperm_r.mem_iff.mp ha, hid⟩⟩
    exact hp1.mem_iff.trans (hmem2.trans (h.nodes_exact id))
  have ht_nrest : t ∉ rest := by
    intro htr
    have hnd := (h.forestInv.perm hperm_r).1.nodupAll
    rw [List.flatMap_cons] at hnd
    exact (List.nodup_append.mp hnd).2.2 u hu_t u (List.mem_flatMap.mpr ⟨t, htr, hu_t⟩) rfl
  exact
    { valid := hvalid', header := hhdrF, numNodes_le := h.numNodes_le
      nodeOf_mem := fun k hk => by
        rw [hmF_pre _ (by simp [nodeOfEndBase, nodesBase]; omega)
          (by simp [nodeOfEndBase, endOwnerBase]; omega) (by simp [nodeOfEndBase, firstEndBase]; omega)]
        exact h.nodeOf_mem k hk
      nodeOf_keyOf := h.nodeOf_keyOf
      keyOf_mem := fun id h1 h2 => by
        dsimp only [x'] at h2; have := h.numNodes_le
        rw [hmF_pre _ (by simp [keyOfNodeBase, nodesBase]; omega)
          (by simp [keyOfNodeBase, endOwnerBase]; omega) (by simp [keyOfNodeBase, firstEndBase]; omega)]
        exact h.keyOf_mem id h1 h2
      firstEnd_mem := fun w' hw' => by
        by_cases hwv : w' = v
        · subst hwv; exact hmF_fev
        · rw [hmF_pre _ (by simp [firstEndBase, nodesBase]; omega)
            (by simp [firstEndBase, endOwnerBase]; omega) (by omega), h.firstEnd_mem w' hw',
            hord'_upd, Function.update_of_ne hwv]
      isRoot_mem := fun w' hw' => by
        rw [hmF_pre _ (by simp [isRootBase, nodesBase]; omega)
          (by simp [isRootBase, endOwnerBase]; omega) (by simp [isRootBase, firstEndBase]; omega)]
        exact h.isRoot_mem w' hw'
      slot_bij := h.slot_bij
      slotOf_mem := fun w' hw' => by
        rw [hmF_pre _ (by simp [slotOfVertBase, nodesBase]; omega)
          (by simp [slotOfVertBase, endOwnerBase]; omega) (by simp [slotOfVertBase, firstEndBase]; omega)]
        exact h.slotOf_mem w' hw'
      vertOf_mem := fun sl hsl => by
        rw [hmF_pre _ (by simp [vertOfSlotBase, nodesBase]; omega)
          (by simp [vertOfSlotBase, endOwnerBase]; omega) (by simp [vertOfSlotBase, firstEndBase]; omega)]
        exact h.vertOf_mem sl hsl
      active_end := fun w' hw' z hz => by
        obtain ⟨hz0, hne_x⟩ := (hord'_mem w' z).mp hz
        have hne_k : endKey z ≠ keyX := fun heq => hne_x (by rw [← heq, endOfKey_endKey])
        have hzLt : endKey z < 2 * eCap := by
          have := h.valid.ordWithin.2.2 w' z hz0; simp only [endKey]; cases z.2 <;> simp <;> omega
        rw [hmF_pre _ (by simp [endOwnerBase, nodesBase]; omega) (by omega)
          (by simp [endOwnerBase, firstEndBase]; omega)]
        exact h.active_end w' hw' z hz0
      inactive_owner := fun k hk hno => by
        by_cases hkk : k = keyX
        · subst hkk; exact hmF_eo0
        · rw [hmF_pre _ (by simp [endOwnerBase, nodesBase]; omega) (by omega)
            (by simp [endOwnerBase, firstEndBase]; omega)]
          refine h.inactive_owner k hk fun w' hw' => hno w' ((hord'_mem w' _).mpr ⟨hw', fun heq => hkk ?_⟩)
          rw [← endKey_endOfKey' k, heq, endKey_endOfKey']
      markArr_zero := fun k hk => by
        rw [hmF_pre _ (by simp [markArrBase, nodesBase]; omega)
          (by simp [markArrBase, endOwnerBase]; omega) (by simp [markArrBase, firstEndBase]; omega)]
        exact h.markArr_zero k hk
      nodesAt := hnF, forestInv := hinvF, nodes_exact := hnodes_exactF
      comp_none := fun r' hr' hft0 => by
        by_cases hrr' : r' = r
        · subst hrr'
          have hft0' : (optList tF?).map (fun id => endOfKey (x.keyOf id)) = [] := by
            rw [htF_map]; exact hft0
          cases htFc : tF? with
          | none => simp [x', r, htFc]
          | some tF =>
            rw [htFc] at hft0' hinvF
            have hnil : tF.toList = [] := by simpa [optList] using hft0'
            have hne := hinvF.nonEmpty tF (by simp [optTrees])
            cases tF <;> simp [AuxTree.toList] at hne hnil
        · rw [hft_other r' hr' hrr'] at hft0
          simpa [x', r, hrr'] using h.comp_none r' hr' hft0
      comp_some := fun r' hr' hft_ne => by
        by_cases hrr' : r' = r
        · subst hrr'
          have hft_ne' : (optList tF?).map (fun id => endOfKey (x.keyOf id)) ≠ [] := by
            rw [htF_map]; exact hft_ne
          cases htFc : tF? with
          | none => rw [htFc] at hft_ne'; simp [optList] at hft_ne'
          | some tF =>
            refine ⟨tF, by simp [x', r, htFc], by simp [x', htFc, optTrees], ?_⟩
            rw [htFc] at htF_map
            exact (by simpa [optList] using htF_map : tF.toList.map (fun id => endOfKey (x.keyOf id)) = _)
        · rw [hft_other r' hr' hrr'] at hft_ne ⊢
          obtain ⟨t0, ht0_eq, ht0_mem, ht0_map⟩ := h.comp_some r' hr' hft_ne
          have ht0_ne_t : t0 ≠ t := fun heq => hcomp_inj r' hr' hrr' (heq ▸ ht0_eq)
          have ht0_rest : t0 ∈ rest := (List.mem_cons.mp (hperm_r.mem_iff.mp ht0_mem)).resolve_left ht0_ne_t
          exact ⟨t0, by simp [x', r, hrr', ht0_eq], by simp [x', ht0_rest], ht0_map⟩
      tree_class := fun tr htr => by
        simp only [x', List.mem_cons, List.mem_append] at htr
        rcases htr with (rfl | hopt) | hrest
        · exact Or.inr ⟨u, rfl, fun w' hw' => ((hord'_mem w' _).mp hw').2 (by rw [hu_key])⟩
        · cases htFc : tF? with
          | none => rw [htFc] at hopt; simp [optTrees] at hopt
          | some tF =>
            rw [htFc] at hopt; simp only [optTrees, Option.toList, List.mem_singleton] at hopt
            exact Or.inl ⟨r, hrR, by simp [x', r, htFc, hopt]⟩
        · have htr_old : tr ∈ x.trees := hperm_r.mem_iff.mpr (by simp [hrest])
          rcases h.tree_class tr htr_old with ⟨r', hr'R, hr'eq⟩ | ⟨id, hid_eq, hid_no⟩
          · have hrr' : r' ≠ r := fun heq => ht_nrest ((Option.some.inj (hr'eq.symm.trans ((congrArg x.compTree heq).trans hct_r))) ▸ hrest)
            exact Or.inl ⟨r', hr'R, by simp [x', r, hrr', hr'eq]⟩
          · exact Or.inr ⟨id, hid_eq, fun w' hw' => hid_no w' ((hord'_mem w' _).mp hw').1⟩
      inactive_single := fun id h1 h2 hno => by
        by_cases hiu : id = u
        · subst hiu; simp [x']
        · have hno_old : ∀ w', endOfKey (x.keyOf id) ∉ s.ord w' := fun w' hw' => by
            refine hno w' ((hord'_mem w' _).mpr ⟨hw', fun heq => hiu ?_⟩)
            have hkeq : x.keyOf id = keyX := by rw [← endKey_endOfKey' (x.keyOf id), heq, endKey_endOfKey']
            rw [hu_eq, ← hkeq, (h.keyOf_mem id h1 h2).2.2]
          have hsing := h.inactive_single id h1 h2 hno_old
          have hne_t : AuxTree.node id .leaf .leaf ≠ t := fun heq => by
            rw [← heq] at hu_t; simp [AuxTree.toList] at hu_t; exact hiu hu_t.symm
          have hrest : AuxTree.node id .leaf .leaf ∈ rest :=
            (List.mem_cons.mp (hperm_r.mem_iff.mp hsing)).resolve_left hne_t
          simp [x', hrest]
      val_active := fun id h1 h2 hact => by
        have hiu : id ≠ u := fun heq => by
          subst heq; obtain ⟨w', hw'⟩ := hact; exact ((hord'_mem w' _).mp hw').2 (by rw [hu_key])
        exact hvalF_active id h1 h2 hiu hact
      val_inactive_rt := fun id h1 h2 hno => by
        dsimp only [x'] at h2
        by_cases hiu : id = u
        · subst hiu; exact hvalF_u_rt
        · have hno_old : ∀ w', endOfKey (x.keyOf id) ∉ s.ord w' := fun w' hw' => by
            refine hno w' ((hord'_mem w' _).mpr ⟨hw', fun heq => hiu ?_⟩)
            have hkeq : x.keyOf id = keyX := by rw [← endKey_endOfKey' (x.keyOf id), heq, endKey_endOfKey']
            rw [hu_eq, ← hkeq, (h.keyOf_mem id h1 h2).2.2]
          rw [show (x'.st.nodes id).val = (x.st.nodes id).val from hvalF_other id (by have := h.numNodes_le; omega) (Or.inl hno_old)]
          exact h.val_inactive_rt id h1 h2 hno_old
      val_unused_rt := fun id hid hcase => by
        rw [show (x'.st.nodes id).val = (x.st.nodes id).val from hvalF_other id hid (Or.inr hcase)]
        exact h.val_unused_rt id hid hcase }


/-! ## `ordNext` helper to find replacement `firstEnd[v]` -/

/-- Execute the 1-or-2 `ordNext` block in Case 1 (`u = feOld`) of `tourDropOneBody`,
computing `newFe` into register 14 and advancing the heap pointer to `hN ≤ heap + 2`. -/
theorem tourDropOne_findNewFe_exec {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap mul_ord b v keyX u heap pos ordOp2 : ℕ}
    {alloc_ord : ℕ → List ℕ → ℕ} {p : Program}
    {ordInit : ℕ} {ordOp : ℕ → ℕ}
    (hOrdImpl : R_ord.Implements w p ordInit ordOp (ordStoreCapContract vCap eCap mul_ord alloc_ord))
    (hop2 : ordOp 2 = ordOp2) (ω : ℕ → Bool)
    {ord0 : ℕ → List End} {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ} {rP : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem)
    (hord0U : OrdUniqueWithin vCap eCap ord0)
    (hordRep : R_ord.rep (ordHandleOf b vCap eCap) ord0 x.ordX mem)
    (hordGe : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → ordHandleOf b vCap eCap ≤ a)
    (hordFoot : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → a < heap)
    (hmiss : (∃ skip : End, skip ≠ endOfKey keyX ∧ ∀ w', s.ord w' = (ord0 w').filter fun z => z != skip) ∨
      s.ord = ord0)
    (hvLt : v < vCap) (hkeyLt : keyX < 2 * eCap)
    (hxv : endOfKey keyX ∈ s.ord v) (hhead_x : (s.ord v).head? = some (endOfKey keyX))
    (hrP0 : rP 0 = b) (hrP1 : rP 1 = keyX) (hrP2 : rP 2 = heap)
    (hrP3 : rP 3 = endOwnerBase b vCap eCap) (hrP5 : rP 5 = v)
    (hrP6 : rP 6 = u) (hrP7 : rP 7 = firstEndBase b)
    (hrP9 : rP 9 = nodesBase b vCap eCap) (hrP10 : rP 10 = 2 * eCap + 2)
    (hord_le : ordHandleOf b vCap eCap ≤ heap) (hroom : heap + 6 < 2 ^ w)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w) (hzero : ZeroFrom mem heap) :
    let s' := tourDropOneAbs s (endOfKey keyX)
    let mem1 := Function.update mem (endOwnerBase b vCap eCap + keyX) 0
    ∃ (hN : ℕ) (newFe : ℕ) (ordXN : R_ord.τ) (stN : State) (cN : ℕ),
      heap ≤ hN ∧ hN ≤ heap + 2 ∧ ZeroFrom stN.mem hN ∧
      (∀ a < ordHandleOf b vCap eCap, stN.mem a = mem1 a) ∧
      (∀ a < heap, (a < b ∨ ordHandleOf b vCap eCap ≤ a) →
        ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → stN.mem a = mem a) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordXN a →
        R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (heap ≤ a ∧ a < hN)) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordXN a → ordHandleOf b vCap eCap ≤ a) ∧
      R_ord.rep (ordHandleOf b vCap eCap) ord0 ordXN stN.mem ∧
      newFe = (match (s'.ord v).head? with | none => 0 | some e => x.nodeOf (endKey e)) ∧
      stN.regs 0 = b ∧ stN.regs 1 = keyX ∧ stN.regs 2 = hN ∧ stN.regs 5 = v ∧
      stN.regs 6 = u ∧ stN.regs 7 = firstEndBase b ∧ stN.regs 9 = nodesBase b vCap eCap ∧
      stN.regs 10 = 2 * eCap + 2 ∧ stN.regs 14 = newFe ∧
      cN + R_ord.phi (ordHandleOf b vCap eCap) ordXN stN.mem ≤
        2 * mul_ord * tourLog eCap + 100 + R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem ∧
      Runs w p ω
        (.assign 11 (.load (.bin .add (.reg 0) (.const HDR_ORD_H))) ;;
         .assign 12 (.reg 2) ;;
         .call 2 ordOp2 [.reg 11, .reg 5, .reg 1, .reg 2] ;;
         .assign 13 (.load (.reg 12)) ;;
         .cond (.bin .eq (.reg 13) (.reg 1))
           (.assign 14 (.const 0))
           (.assign 14 (.load (.bin .add (.reg 3) (.reg 13))) ;;
            .cond (.bin .eq (.reg 14) (.const 0))
              (.assign 12 (.reg 2) ;;
               .call 2 ordOp2 [.reg 11, .reg 5, .reg 13, .reg 2] ;;
               .assign 13 (.load (.reg 12)))
              .nop ;;
            .cond (.bin .eq (.reg 13) (.reg 1))
              (.assign 14 (.const 0))
              (.assign 14 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
               .assign 14 (.load (.bin .add (.reg 14) (.reg 13))))))
        ⟨mem1, rP, pos⟩ .normal stN cN := by
  intro s' mem1
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hhdr := h.header
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hzero1 : ZeroFrom mem1 heap := fun a ha => by
    dsimp only [mem1]; rw [Function.update_of_ne (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
    exact hzero a ha
  have hordRep1 : R_ord.rep (ordHandleOf b vCap eCap) ord0 x.ordX mem1 :=
    (hOrdImpl.1 (ordHandleOf b vCap eCap) ord0 x.ordX mem mem1 fun a ha => by
      have := hordGe a ha; dsimp only [mem1]
      rw [Function.update_of_ne (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at this ⊢; omega)]).1 hordRep
  have hordPhi1 : R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem1 = R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem :=
    ((hOrdImpl.1 (ordHandleOf b vCap eCap) ord0 x.ordX mem mem1 fun a ha => by
      have := hordGe a ha; dsimp only [mem1]
      rw [Function.update_of_ne (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at this ⊢; omega)]).2).symm
  have hm1_ordH : mem1 (b + HDR_ORD_H) = ordHandleOf b vCap eCap := by
    dsimp only [mem1]; rw [Function.update_of_ne (by simp [HDR_ORD_H, endOwnerBase]; omega)]; exact hhdr.2.2.1
  have hcore_for_next : TourCoreAt vCap eCap b s x mem := h
  -- `mem1` has `endOwner[keyX] = 0`, so `hOrdImpl.2.2 2` applies directly.
  have hxv_ord0 : endOfKey keyX ∈ ord0 v := by
    rcases hmiss with ⟨skip, _, hfil⟩ | hEq
    · exact (List.mem_filter.mp (hfil v ▸ hxv)).1
    · exact hEq ▸ hxv
  have hpre_n1 : (ordStoreCapContract vCap eCap mul_ord alloc_ord).pre 2 ord0
      [ordHandleOf b vCap eCap, v, keyX, heap] mem1 :=
    ⟨ordHandleOf b vCap eCap, v, keyX, heap, rfl, hvLt, hxv_ord0⟩
  have hargW1 : ∀ a ∈ [ordHandleOf b vCap eCap, v, keyX, heap], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  obtain ⟨bodyN1, hgetN1, oN1, stN1, cN1, hrunN1, sOrdN1, ordX1, hrepN1, hpostN1, hrespN1, hcostN1⟩ :=
    hOrdImpl.2.2 2 (ordHandleOf b vCap eCap) ord0 x.ordX [ordHandleOf b vCap eCap, v, keyX, heap] mem1 pos ω
      hargW1 rfl hordRep1 hpre_n1 hordFoot hzero1 (by simpa [ordStoreCapContract, heapArg] using (by omega : heap + 1 < 2 ^ w))
  rcases hrespN1 with ⟨hN1_ge, hN1_le, hzN1, hfrN1, hfootN1⟩
  have hha1 : heapArg [ordHandleOf b vCap eCap, v, keyX, heap] = heap := rfl
  simp only [hha1, ordStoreCapContract, List.getD_cons_zero, List.getD_cons_succ] at hN1_ge hN1_le hzN1 hfrN1 hfootN1 hcostN1 hpostN1
  rw [hop2] at hgetN1
  set k1 := endKey (cycNext (ord0 v) (endOfKey keyX))
  have hk1_mem_val : stN1.mem heap = k1 := by simpa [k1, cycNext] using hpostN1.2
  have hge1 : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX1 a → ordHandleOf b vCap eCap ≤ a := fun a ha => by
    rcases hfootN1 a ha with h1 | ⟨h1, _⟩; exact hordGe a h1; omega
  have hfoot1_lt : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX1 a → a < oN1.value := fun a ha => by
    rcases hfootN1 a ha with h1 | ⟨_, h2⟩; exact lt_of_lt_of_le (hordFoot a h1) hN1_ge; exact h2
  have hpreN1_eq : ∀ a < ordHandleOf b vCap eCap, stN1.mem a = mem1 a := fun a ha =>
    hfrN1 a (by omega) fun hft => by have := hordGe a hft; omega
  -- Compute `newFe` and updated `(h_cur, stN, ordXN, cN)` via 1 or 2 `ordNext` calls
  have hspec := head?_dropHead_via_orig_cycNext (orig := ord0 v) (xs := s.ord v) (x := endOfKey keyX)
    (hord0U.nodup v)
    (fun z hz => by rcases hmiss with ⟨skip, _, hfil⟩ | hEq; exact (List.mem_filter.mp (hfil v ▸ hz)).1; exact hEq ▸ hz)
    (by rcases hmiss with ⟨skip, hne, hfil⟩ | hEq; exact Or.inl ⟨skip, hne, hfil v⟩; exact Or.inr (congrFun hEq v))
    hhead_x
  set rN1 := Function.update rP 11 (ordHandleOf b vCap eCap)
  set rN2 := Function.update rN1 12 heap
  have hN_a1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 0) (off := HDR_ORD_H)
    (b := b) (val := ordHandleOf b vCap eCap) (st := ⟨mem1, rP, pos⟩) hrP0
    (by simp [HDR_ORD_H]; omega) (by simp [HDR_ORD_H]; omega) hm1_ordH
  have hN_a2 : Runs w p ω (.assign 12 (.reg 2)) ⟨mem1, rN1, pos⟩ .normal ⟨mem1, rN2, pos⟩ 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, rN1, hrP2], rfl, rfl, rfl⟩
  have hN_c1 := runs_call_regs4 2 11 5 1 2 (st := ⟨mem1, rN2, pos⟩) hgetN1
    (by simp [rN2, rN1]) (by simp [rN2, rN1, hrP5]) (by simp [rN2, rN1, hrP1])
    (by simp [rN2, rN1, hrP2]) hrunN1
  set rN3 := Function.update rN2 2 oN1.value
  set rN4 := Function.update rN3 13 k1
  have hN_a3 : Runs w p ω (.assign 13 (.load (.reg 12))) { stN1 with regs := rN3 } .normal
      { stN1 with regs := rN4 } 3 :=
    runs_assign_iff.mpr ⟨k1, by simp [Expr.eval, rN3, rN2, hk1_mem_val], rfl, rfl, rfl⟩
  have hk1_end_mem : endOfKey k1 ∈ ord0 v := by
    have hc_mem : cycNext (ord0 v) (endOfKey keyX) ∈ ord0 v := by
      obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hxv_ord0
      rw [← heq, cycNext_eq_getElem (hord0U.nodup v) hi]; exact List.getElem_mem _
    simpa [k1, endOfKey_endKey] using hc_mem
  have hk1_lt : k1 < 2 * eCap := by
    have := hord0U.edge_lt hk1_end_mem; exact key_lt_two_mul_of_endOfKey this
  have hfrN1_out : ∀ a < heap, (a < b ∨ ordHandleOf b vCap eCap ≤ a) →
      ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → stN1.mem a = mem a := fun a ha1 ha2 hnf => by
    rw [hfrN1 a ha1 hnf]; dsimp only [mem1]
    exact Function.update_of_ne (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at ha2 ⊢; rcases ha2 with h1 | h2 <;> omega) _ _
  by_cases hk1_eq : k1 = keyX
  · have hc_eq : cycNext (ord0 v) (endOfKey keyX) = endOfKey keyX := by
      rw [← endOfKey_endKey (cycNext _ _)]; exact congrArg endOfKey hk1_eq
    have hhd_none : (s'.ord v).head? = none := by
      simpa [s', tourDropOneAbs, hc_eq] using hspec
    have hcond1 : (Expr.bin .eq (.reg 13) (.reg 1)).eval w { stN1 with regs := rN4 } = some 1 := by
      simp [Expr.eval, rN4, rN3, rN2, rN1, hrP1, hk1_eq, BinOp.eval, (by omega : 1 < 2 ^ w)]
    set rN5 := Function.update rN4 14 0
    have hN_z := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 14) (val := 0)
      (st := { stN1 with regs := rN4 }) (by omega)
    refine ⟨oN1.value, 0, ordX1, { stN1 with regs := rN5 }, _,
      hN1_ge, by omega, hzN1, hpreN1_eq, hfrN1_out, hfootN1, hge1, hpostN1.1 ▸ hrepN1,
      by simp [hhd_none],
      by simp [rN5, rN4, rN3, rN2, rN1, hrP0], by simp [rN5, rN4, rN3, rN2, rN1, hrP1],
      by simp [rN5, rN4, rN3], by simp [rN5, rN4, rN3, rN2, rN1, hrP5],
      by simp [rN5, rN4, rN3, rN2, rN1, hrP6], by simp [rN5, rN4, rN3, rN2, rN1, hrP7],
      by simp [rN5, rN4, rN3, rN2, rN1, hrP9], by simp [rN5, rN4, rN3, rN2, rN1, hrP10],
      by simp [rN5], ?_,
      tour_runs_seq_normal hN_a1 (tour_runs_seq_normal hN_a2 (tour_runs_seq_normal hN_c1
        (tour_runs_seq_normal hN_a3 (tour_runs_cond_true hcond1 (by omega) hN_z))))⟩
    rw [hordPhi1] at hcostN1
    have hmul : mul_ord * tourLog eCap ≤ 2 * mul_ord * tourLog eCap := Nat.mul_le_mul_right _ (by omega)
    clear * - hcostN1 hmul; simp only [Expr.size, ordStoreLog_eq_tourLog] at *; omega
  · -- `k1 ≠ keyX`: check `endOwner[k1]` (`= 0` iff `endOfKey k1 ∉ s.ord v`, i.e., skipped!)
    have hc_ne : cycNext (ord0 v) (endOfKey keyX) ≠ endOfKey keyX := fun heq =>
      hk1_eq (by simp [k1, heq, endKey_endOfKey'])
    have hcond1 : (Expr.bin .eq (.reg 13) (.reg 1)).eval w { stN1 with regs := rN4 } = some 0 := by
      simp [Expr.eval, rN4, rN3, rN2, rN1, hrP1, hk1_eq, BinOp.eval, (by omega : 0 < 2 ^ w)]
    have heo1_addr : endOwnerBase b vCap eCap + k1 < 2 ^ w := by
      simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
    have hmN1_eo1 : stN1.mem (endOwnerBase b vCap eCap + k1) = mem (endOwnerBase b vCap eCap + k1) := by
      rw [hpreN1_eq _ (by simp [endOwnerBase, ordHandleOf, tourFixedSize]; omega)]
      dsimp only [mem1]; exact Function.update_of_ne (by omega) _ _
    set eo1 := mem (endOwnerBase b vCap eCap + k1)
    set rN5 := Function.update rN4 14 eo1
    have hN_a4 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 3) (rIdx := 13)
      (base := endOwnerBase b vCap eCap) (idx := k1) (val := eo1) (st := { stN1 with regs := rN4 })
      (by simp [rN4, rN3, rN2, rN1, hrP3]) (by simp [rN4]) heo1_addr hmN1_eo1
    by_cases hk1_in : cycNext (ord0 v) (endOfKey keyX) ∈ s.ord v
    · -- `k1` is active at `v`: `eo1 = slotOf v + 1 ≠ 0`, skip second `ordNext`, `newFe = nodeOf k1`!
      have heo1_nz : eo1 ≠ 0 := by
        have := (h.active_end v hvLt _ hk1_in).2; simp only [k1, eo1] at *; omega
      have hcond_eo1 : (Expr.bin .eq (.reg 14) (.const 0)).eval w { stN1 with regs := rN5 } = some 0 := by
        simp [Expr.eval, rN5, heo1_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]
      have hcond2 : (Expr.bin .eq (.reg 13) (.reg 1)).eval w { stN1 with regs := rN5 } = some 0 := by
        simp [Expr.eval, rN5, rN4, rN3, rN2, rN1, hrP1, hk1_eq, BinOp.eval, (by omega : 0 < 2 ^ w)]
      have hmN1_ne : stN1.mem (b + HDR_NODE_OF_END) = nodeOfEndBase b vCap := by
        rw [hpreN1_eq _ (by simp [HDR_NODE_OF_END, ordHandleOf, tourFixedSize]; omega)]
        dsimp only [mem1]; rw [Function.update_of_ne (by simp [HDR_NODE_OF_END, endOwnerBase]; omega)]
        exact hhdr.2.2.2.2.2.2.1
      have hmN1_u1 : stN1.mem (nodeOfEndBase b vCap + k1) = x.nodeOf k1 := by
        rw [hpreN1_eq _ (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize]; omega)]
        dsimp only [mem1]; rw [Function.update_of_ne (by simp [nodeOfEndBase, endOwnerBase]; omega)]
        exact (h.nodeOf_mem k1 hk1_lt).1
      set rN6 := Function.update rN5 14 (nodeOfEndBase b vCap)
      set rN7 := Function.update rN6 14 (x.nodeOf k1)
      have hN_a5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 0) (off := HDR_NODE_OF_END)
        (b := b) (val := nodeOfEndBase b vCap) (st := { stN1 with regs := rN5 })
        (by simp [rN5, rN4, rN3, rN2, rN1, hrP0]) (by simp [HDR_NODE_OF_END]; omega)
        (by simp [HDR_NODE_OF_END]; omega) hmN1_ne
      have hN_a6 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 14) (rIdx := 13)
        (base := nodeOfEndBase b vCap) (idx := k1) (val := x.nodeOf k1) (st := { stN1 with regs := rN6 })
        (by simp [rN6]) (by simp [rN6, rN5, rN4])
        (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) hmN1_u1
      have hhd_some : (s'.ord v).head? = some (cycNext (ord0 v) (endOfKey keyX)) := by
        simpa [s', tourDropOneAbs, hc_ne, hk1_in] using hspec
      refine ⟨oN1.value, x.nodeOf k1, ordX1, { stN1 with regs := rN7 }, _,
        hN1_ge, by omega, hzN1, hpreN1_eq, hfrN1_out, hfootN1, hge1, hpostN1.1 ▸ hrepN1,
        by simp [hhd_some, k1],
        by simp [rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP0], by simp [rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP1],
        by simp [rN7, rN6, rN5, rN4, rN3], by simp [rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP5],
        by simp [rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP6], by simp [rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP7],
        by simp [rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP9], by simp [rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP10],
        by simp [rN7], ?_,
        tour_runs_seq_normal hN_a1 (tour_runs_seq_normal hN_a2 (tour_runs_seq_normal hN_c1 (tour_runs_seq_normal hN_a3
          (tour_runs_cond_false hcond1 (tour_runs_seq_normal hN_a4
            (tour_runs_seq_normal (tour_runs_cond_false hcond_eo1 (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩))
              (tour_runs_cond_false hcond2 (tour_runs_seq_normal hN_a5 hN_a6))))))))⟩
      rw [hordPhi1] at hcostN1
      have hmul : mul_ord * tourLog eCap ≤ 2 * mul_ord * tourLog eCap := Nat.mul_le_mul_right _ (by omega)
      clear * - hcostN1 hmul; simp only [Expr.size, ordStoreLog_eq_tourLog] at *; omega
    · -- `k1` was skipped (`endOfKey k1 ∉ s.ord w'` for all `w'`): `eo1 = 0`, call `ordNext` a 2nd time!
      have hk1_nany : ∀ w', endOfKey k1 ∉ s.ord w' := fun w' hw' => by
        have hw'_ord0 : endOfKey k1 ∈ ord0 w' := by
          rcases hmiss with ⟨skip, _, hfil⟩ | hEq; exact (List.mem_filter.mp (hfil w' ▸ hw')).1; exact hEq ▸ hw'
        have hw'v : w' = v := hord0U.unique_v hw'_ord0 hk1_end_mem
        subst hw'v; exact hk1_in (by simpa [k1, endOfKey_endKey] using hw')
      have heo1_0 : eo1 = 0 := h.inactive_owner k1 hk1_lt hk1_nany
      have hcond_eo1 : (Expr.bin .eq (.reg 14) (.const 0)).eval w { stN1 with regs := rN5 } = some 1 := by
        simp [Expr.eval, rN5, heo1_0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
      have hpre_n2 : (ordStoreCapContract vCap eCap mul_ord alloc_ord).pre 2 ord0
          [ordHandleOf b vCap eCap, v, k1, oN1.value] stN1.mem :=
        ⟨ordHandleOf b vCap eCap, v, k1, oN1.value, rfl, hvLt, hk1_end_mem⟩
      have hargW2 : ∀ a ∈ [ordHandleOf b vCap eCap, v, k1, oN1.value], a < 2 ^ w := by
        intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> omega
      obtain ⟨bodyN2, hgetN2, oN2, stN2, cN2, hrunN2, sOrdN2, ordX2, hrepN2, hpostN2, hrespN2, hcostN2⟩ :=
        hOrdImpl.2.2 2 (ordHandleOf b vCap eCap) ord0 ordX1 [ordHandleOf b vCap eCap, v, k1, oN1.value]
          stN1.mem stN1.pos ω hargW2 rfl (hpostN1.1 ▸ hrepN1) hpre_n2 hfoot1_lt hzN1
          (by simpa [ordStoreCapContract, heapArg] using (by omega : oN1.value + 1 < 2 ^ w))
      rcases hrespN2 with ⟨hN2_ge, hN2_le, hzN2, hfrN2, hfootN2⟩
      have hha2 : heapArg [ordHandleOf b vCap eCap, v, k1, oN1.value] = oN1.value := rfl
      simp only [hha2, ordStoreCapContract, List.getD_cons_zero, List.getD_cons_succ] at hN2_ge hN2_le hzN2 hfrN2 hfootN2 hcostN2 hpostN2
      rw [hop2] at hgetN2
      set k2 := endKey (cycNext (ord0 v) (endOfKey k1))
      have hk2_mem_val : stN2.mem oN1.value = k2 := by simpa [k2, cycNext] using hpostN2.2
      have hpreN2_eq : ∀ a < ordHandleOf b vCap eCap, stN2.mem a = mem1 a := fun a ha =>
        (hfrN2 a (by omega) fun hft => by have := hge1 a hft; omega).trans (hpreN1_eq a ha)
      have hfrN2_out : ∀ a < heap, (a < b ∨ ordHandleOf b vCap eCap ≤ a) →
          ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → stN2.mem a = mem a := fun a ha1 ha2 hnf => by
        have hnf1 : ¬R_ord.foot (ordHandleOf b vCap eCap) ordX1 a := fun hft => by
          rcases hfootN1 a hft with h1 | ⟨h1, _⟩; exact hnf h1; omega
        exact (hfrN2 a (by omega) hnf1).trans (hfrN1_out a ha1 ha2 hnf)
      have hfoot2_sub : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX2 a →
          R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (heap ≤ a ∧ a < oN2.value) := fun a ha => by
        rcases hfootN2 a ha with h1 | ⟨h1, h2⟩
        · rcases hfootN1 a h1 with h0 | ⟨h0a, h0b⟩; exact Or.inl h0; exact Or.inr ⟨h0a, by omega⟩
        · exact Or.inr ⟨by omega, h2⟩
      have hge2 : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX2 a → ordHandleOf b vCap eCap ≤ a := fun a ha => by
        rcases hfoot2_sub a ha with h1 | ⟨h1, _⟩; exact hordGe a h1; omega
      set rN6 := Function.update rN5 12 oN1.value
      have hN_b1 : Runs w p ω (.assign 12 (.reg 2)) { stN1 with regs := rN5 } .normal
          { stN1 with regs := rN6 } 2 :=
        runs_assign_iff.mpr ⟨oN1.value, by simp [Expr.eval, rN5, rN4, rN3], rfl, rfl, rfl⟩
      have hN_c2 := runs_call_regs4 2 11 5 13 2 (st := { stN1 with regs := rN6 }) hgetN2
        (by simp [rN6, rN5, rN4, rN3, rN2, rN1]) (by simp [rN6, rN5, rN4, rN3, rN2, rN1, hrP5])
        (by simp [rN6, rN5, rN4]) (by simp [rN6, rN5, rN4, rN3]) hrunN2
      set rN7 := Function.update rN6 2 oN2.value
      set rN8 := Function.update rN7 13 k2
      have hN_b2 : Runs w p ω (.assign 13 (.load (.reg 12))) { stN2 with regs := rN7 } .normal
          { stN2 with regs := rN8 } 3 :=
        runs_assign_iff.mpr ⟨k2, by simp [Expr.eval, rN7, rN6, hk2_mem_val], rfl, rfl, rfl⟩
      have hstep2 := tour_runs_cond_true (s₂ := .nop) hcond_eo1 (by omega)
        (tour_runs_seq_normal hN_b1 (tour_runs_seq_normal hN_c2 hN_b2))
      have hk2_end_eq : endOfKey k2 = cycNext (ord0 v) (cycNext (ord0 v) (endOfKey keyX)) := by
        simp [k2, k1, endOfKey_endKey]
      by_cases hk2_eq : k2 = keyX
      · have hc2_eq : cycNext (ord0 v) (cycNext (ord0 v) (endOfKey keyX)) = endOfKey keyX := by
          rw [← hk2_end_eq, hk2_eq]
        have hhd_none : (s'.ord v).head? = none := by
          simpa [s', tourDropOneAbs, hc_ne, hk1_in, hc2_eq] using hspec
        have hcond2 : (Expr.bin .eq (.reg 13) (.reg 1)).eval w { stN2 with regs := rN8 } = some 1 := by
          simp [Expr.eval, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP1, hk2_eq, BinOp.eval, (by omega : 1 < 2 ^ w)]
        set rN9 := Function.update rN8 14 0
        have hN_z2 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 14) (val := 0)
          (st := { stN2 with regs := rN8 }) (by omega)
        refine ⟨oN2.value, 0, ordX2, { stN2 with regs := rN9 }, _,
          by omega, by omega, hzN2, hpreN2_eq, hfrN2_out, hfoot2_sub, hge2, hpostN2.1 ▸ hrepN2,
          by simp [hhd_none],
          by simp [rN9, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP0],
          by simp [rN9, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP1],
          by simp [rN9, rN8, rN7], by simp [rN9, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP5],
          by simp [rN9, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP6],
          by simp [rN9, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP7],
          by simp [rN9, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP9],
          by simp [rN9, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP10],
          by simp [rN9], ?_,
          tour_runs_seq_normal hN_a1 (tour_runs_seq_normal hN_a2 (tour_runs_seq_normal hN_c1 (tour_runs_seq_normal hN_a3
            (tour_runs_cond_false hcond1 (tour_runs_seq_normal hN_a4 (tour_runs_seq_normal hstep2
              (tour_runs_cond_true hcond2 (by omega) hN_z2)))))))⟩
        rw [hordPhi1] at hcostN1
        have hmul : mul_ord * tourLog eCap + mul_ord * tourLog eCap = 2 * mul_ord * tourLog eCap := by ring
        clear * - hcostN1 hcostN2 hmul; simp only [Expr.size, ordStoreLog_eq_tourLog] at *; omega
      · have hc2_ne : cycNext (ord0 v) (cycNext (ord0 v) (endOfKey keyX)) ≠ endOfKey keyX := fun heq =>
          hk2_eq (by rw [← endKey_endOfKey' k2, hk2_end_eq, heq, endKey_endOfKey'])
        have hhd_some : (s'.ord v).head? = some (endOfKey k2) := by
          rw [hk2_end_eq]; simpa [s', tourDropOneAbs, hc_ne, hk1_in, hc2_ne] using hspec
        have hk2_lt : k2 < 2 * eCap := by
          have hk2_mem : endOfKey k2 ∈ ord0 v := by
            obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hk1_end_mem
            rw [hk2_end_eq, ← show endOfKey k1 = cycNext (ord0 v) (endOfKey keyX) by simp [k1, endOfKey_endKey],
              ← heq, cycNext_eq_getElem (hord0U.nodup v) hi]
            exact List.getElem_mem _
          exact key_lt_two_mul_of_endOfKey (hord0U.edge_lt hk2_mem)
        have hcond2 : (Expr.bin .eq (.reg 13) (.reg 1)).eval w { stN2 with regs := rN8 } = some 0 := by
          simp [Expr.eval, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP1, hk2_eq, BinOp.eval, (by omega : 0 < 2 ^ w)]
        have hmN2_ne : stN2.mem (b + HDR_NODE_OF_END) = nodeOfEndBase b vCap := by
          rw [hpreN2_eq _ (by simp [HDR_NODE_OF_END, ordHandleOf, tourFixedSize]; omega)]
          dsimp only [mem1]; rw [Function.update_of_ne (by simp [HDR_NODE_OF_END, endOwnerBase]; omega)]
          exact hhdr.2.2.2.2.2.2.1
        have hmN2_u2 : stN2.mem (nodeOfEndBase b vCap + k2) = x.nodeOf k2 := by
          rw [hpreN2_eq _ (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize]; omega)]
          dsimp only [mem1]; rw [Function.update_of_ne (by simp [nodeOfEndBase, endOwnerBase]; omega)]
          exact (h.nodeOf_mem k2 hk2_lt).1
        set rN9 := Function.update rN8 14 (nodeOfEndBase b vCap)
        set rN10 := Function.update rN9 14 (x.nodeOf k2)
        have hN_a5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 0) (off := HDR_NODE_OF_END)
          (b := b) (val := nodeOfEndBase b vCap) (st := { stN2 with regs := rN8 })
          (by simp [rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP0]) (by simp [HDR_NODE_OF_END]; omega)
          (by simp [HDR_NODE_OF_END]; omega) hmN2_ne
        have hN_a6 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 14) (rIdx := 13)
          (base := nodeOfEndBase b vCap) (idx := k2) (val := x.nodeOf k2) (st := { stN2 with regs := rN9 })
          (by simp [rN9]) (by simp [rN9, rN8])
          (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) hmN2_u2
        refine ⟨oN2.value, x.nodeOf k2, ordX2, { stN2 with regs := rN10 }, _,
          by omega, by omega, hzN2, hpreN2_eq, hfrN2_out, hfoot2_sub, hge2, hpostN2.1 ▸ hrepN2,
          by simp [hhd_some, endKey_endOfKey'],
          by simp [rN10, rN9, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP0],
          by simp [rN10, rN9, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP1],
          by simp [rN10, rN9, rN8, rN7], by simp [rN10, rN9, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP5],
          by simp [rN10, rN9, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP6],
          by simp [rN10, rN9, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP7],
          by simp [rN10, rN9, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP9],
          by simp [rN10, rN9, rN8, rN7, rN6, rN5, rN4, rN3, rN2, rN1, hrP10],
          by simp [rN10], ?_,
          tour_runs_seq_normal hN_a1 (tour_runs_seq_normal hN_a2 (tour_runs_seq_normal hN_c1 (tour_runs_seq_normal hN_a3
            (tour_runs_cond_false hcond1 (tour_runs_seq_normal hN_a4 (tour_runs_seq_normal hstep2
              (tour_runs_cond_false hcond2 (tour_runs_seq_normal hN_a5 hN_a6))))))))⟩
        rw [hordPhi1] at hcostN1
        have hmul : mul_ord * tourLog eCap + mul_ord * tourLog eCap = 2 * mul_ord * tourLog eCap := by ring
        clear * - hcostN1 hcostN2 hmul; simp only [Expr.size, ordStoreLog_eq_tourLog] at *; omega

end MinCostFlow.SparseCore.Program
