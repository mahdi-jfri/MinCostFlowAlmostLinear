module

public import MinCostFlow.SparseCore.Program.TourEditMath
public import MinCostFlow.SparseCore.Program.TourOpsMark
public import MinCostFlow.SparseCore.Program.TourCutLinkExec
public import MinCostFlow.SparseCore.Program.OrdStoreCapContract
import Mathlib.Tactic

/-!
# Shared infrastructure for `applyEdits` (Op 0)

Provides:
- `TourCoreAt`: all tour-side invariants of `TourRepAt` decoupled from the embedded `ordStore`
  abstract state, so each edit handler updates the tour structures first and then calls
  `ordStoreOp b 0` via `tourCore_commitOrdStore` to obtain a full `TourRepAt`.
- `ordStoreLog_le_tourLog`, `runs_decodeSlot`, and single-edit `OrdEditsAt` helpers for
  forwarding one edit record to `ordStoreOp b 0`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## `TourCoreAt`: tour-side concrete invariant decoupled from `ordStore` -/

/-- All fixed-block and splay-forest invariants of `TourRepAt`, decoupled from `ordRep`. -/
structure TourCoreAt {τ_ord : Type} (vCap eCap b : ℕ)
    (s : TourAbs) (x : TourConcrete τ_ord) (mem : ℕ → ℕ) : Prop where
  valid : TourValid vCap eCap s
  header : TourHeaderAt vCap eCap b x.numNodes mem
  numNodes_le : x.numNodes ≤ 2 * eCap
  nodeOf_mem : ∀ k < 2 * eCap, mem (nodeOfEndBase b vCap + k) = x.nodeOf k ∧ x.nodeOf k ≤ x.numNodes
  nodeOf_keyOf : ∀ k < 2 * eCap, x.nodeOf k ≠ 0 → x.keyOf (x.nodeOf k) = k
  keyOf_mem : ∀ u, 1 ≤ u → u ≤ x.numNodes →
    mem (keyOfNodeBase b vCap eCap + u) = x.keyOf u ∧ x.keyOf u < 2 * eCap ∧ x.nodeOf (x.keyOf u) = u
  firstEnd_mem : ∀ v < vCap,
    mem (firstEndBase b + v) = match (s.ord v).head? with
      | none => 0
      | some e => x.nodeOf (endKey e)
  isRoot_mem : ∀ v < vCap,
    mem (isRootBase b vCap + v) = if v ∈ s.rf.R then 1 else 0
  slot_bij : ∀ v < vCap, x.slotOf v < vCap ∧ x.vertOf (x.slotOf v) = v ∧ x.slotOf (x.vertOf v) = v
  slotOf_mem : ∀ v < vCap, decodeSlot (mem (slotOfVertBase b vCap eCap + v)) v = x.slotOf v
  vertOf_mem : ∀ sl < vCap, decodeSlot (mem (vertOfSlotBase b vCap eCap + sl)) sl = x.vertOf sl
  active_end : ∀ v < vCap, ∀ e ∈ s.ord v,
    x.nodeOf (endKey e) ≠ 0 ∧ mem (endOwnerBase b vCap eCap + endKey e) = x.slotOf v + 1
  inactive_owner : ∀ k < 2 * eCap, (∀ v, endOfKey k ∉ s.ord v) →
    mem (endOwnerBase b vCap eCap + k) = 0
  markArr_zero : ∀ k < 2 * eCap, mem (markArrBase b vCap eCap + k) = 0
  nodesAt : tourLayout.NodesAt mem (nodesBase b vCap eCap) x.numNodes x.st
  forestInv : TourForestInv x.numNodes x.st x.trees
  nodes_exact : ∀ u, u ∈ x.trees.flatMap AuxTree.toList ↔ 1 ≤ u ∧ u ≤ x.numNodes
  comp_none : ∀ r ∈ s.rf.R, fullTour s.ord s.rf.F valid.compat.forest r = [] → x.compTree r = none
  comp_some : ∀ r ∈ s.rf.R, fullTour s.ord s.rf.F valid.compat.forest r ≠ [] →
    ∃ t, x.compTree r = some t ∧ t ∈ x.trees ∧
      t.toList.map (fun u => endOfKey (x.keyOf u)) = fullTour s.ord s.rf.F valid.compat.forest r
  tree_class : ∀ t ∈ x.trees,
    (∃ r ∈ s.rf.R, x.compTree r = some t) ∨
    (∃ u, t = AuxTree.node u .leaf .leaf ∧ ∀ v, endOfKey (x.keyOf u) ∉ s.ord v)
  inactive_single : ∀ u, 1 ≤ u → u ≤ x.numNodes →
    (∀ v, endOfKey (x.keyOf u) ∉ s.ord v) → AuxTree.node u .leaf .leaf ∈ x.trees
  val_active : ∀ u, 1 ≤ u → u ≤ x.numNodes →
    (∃ v, endOfKey (x.keyOf u) ∈ s.ord v) →
    (x.st.nodes u).val =
      { isOpen := decide ((endOfKey (x.keyOf u)).1 ∉ s.rf.F.E)
        isMarked := decide (endOfKey (x.keyOf u) ∈ s.marked)
        rootTag := tourRootTagVal s (endOfKey (x.keyOf u)) }
  val_inactive_rt : ∀ u, 1 ≤ u → u ≤ x.numNodes →
    (∀ v, endOfKey (x.keyOf u) ∉ s.ord v) → (x.st.nodes u).val.rootTag = 0
  val_unused_rt : ∀ u ≤ x.numNodes, u = 0 ∨ x.numNodes < u → (x.st.nodes u).val.rootTag = 0

theorem TourRepAt.toCore {R_ord : DSRep (ℕ → List End)} {vCap eCap b : ℕ}
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem) : TourCoreAt vCap eCap b s x mem where
  valid := h.valid
  header := h.header
  numNodes_le := h.numNodes_le
  nodeOf_mem := h.nodeOf_mem
  nodeOf_keyOf := h.nodeOf_keyOf
  keyOf_mem := h.keyOf_mem
  firstEnd_mem := h.firstEnd_mem
  isRoot_mem := h.isRoot_mem
  slot_bij := h.slot_bij
  slotOf_mem := h.slotOf_mem
  vertOf_mem := h.vertOf_mem
  active_end := h.active_end
  inactive_owner := h.inactive_owner
  markArr_zero := h.markArr_zero
  nodesAt := h.nodesAt
  forestInv := h.forestInv
  nodes_exact := h.nodes_exact
  comp_none := h.comp_none
  comp_some := h.comp_some
  tree_class := h.tree_class
  inactive_single := h.inactive_single
  val_active := h.val_active
  val_inactive_rt := h.val_inactive_rt
  val_unused_rt := h.val_unused_rt

theorem TourCoreAt.toRep {R_ord : DSRep (ℕ → List End)} {vCap eCap b : ℕ}
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem)
    (hord : R_ord.rep (ordHandleOf b vCap eCap) s.ord x.ordX mem)
    (hge : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → ordHandleOf b vCap eCap ≤ a) :
    TourRepAt R_ord vCap eCap b s x mem where
  valid := h.valid
  ordRep := hord
  ordFootGe := hge
  header := h.header
  numNodes_le := h.numNodes_le
  nodeOf_mem := h.nodeOf_mem
  nodeOf_keyOf := h.nodeOf_keyOf
  keyOf_mem := h.keyOf_mem
  firstEnd_mem := h.firstEnd_mem
  isRoot_mem := h.isRoot_mem
  slot_bij := h.slot_bij
  slotOf_mem := h.slotOf_mem
  vertOf_mem := h.vertOf_mem
  active_end := h.active_end
  inactive_owner := h.inactive_owner
  markArr_zero := h.markArr_zero
  nodesAt := h.nodesAt
  forestInv := h.forestInv
  nodes_exact := h.nodes_exact
  comp_none := h.comp_none
  comp_some := h.comp_some
  tree_class := h.tree_class
  inactive_single := h.inactive_single
  val_active := h.val_active
  val_inactive_rt := h.val_inactive_rt
  val_unused_rt := h.val_unused_rt

theorem TourCoreAt.congr_fixed {τ_ord : Type} {vCap eCap b : ℕ}
    {s : TourAbs} {x : TourConcrete τ_ord} {mem mem' : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem)
    (hEq : ∀ a, b ≤ a → a < ordHandleOf b vCap eCap → mem' a = mem a) :
    TourCoreAt vCap eCap b s x mem' := by
  have hhdr : TourHeaderAt vCap eCap b x.numNodes mem' := by
    rcases h.header with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    have hf : ∀ k < 16, mem' (b + k) = mem (b + k) := fun k hk =>
      hEq (b + k) (by omega) (by simp only [ordHandleOf, tourFixedSize]; omega)
    exact ⟨by rw [hf _ (by decide)]; exact h0, by rw [hf _ (by decide)]; exact h1,
      by rw [hf _ (by decide)]; exact h2, by rw [hf _ (by decide)]; exact h3,
      by rw [hf _ (by decide)]; exact h4, by rw [hf _ (by decide)]; exact h5,
      by rw [hf _ (by decide)]; exact h6, by rw [hf _ (by decide)]; exact h7,
      by rw [hf _ (by decide)]; exact h8, by rw [hf _ (by decide)]; exact h9,
      by rw [hf _ (by decide)]; exact h10, by rw [hf _ (by decide)]; exact h11,
      by rw [hf _ (by decide)]; exact h12, by rw [hf _ (by decide)]; exact h13,
      by rw [hf _ (by decide)]; exact h14⟩
  refine
    { valid := h.valid
      header := hhdr
      numNodes_le := h.numNodes_le
      nodeOf_mem := fun k hk => by
        rw [hEq _ (by simp [nodeOfEndBase]; omega) (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.nodeOf_mem k hk
      nodeOf_keyOf := h.nodeOf_keyOf
      keyOf_mem := fun u h1 h2 => by
        have hle := h.numNodes_le
        rw [hEq _ (by simp [keyOfNodeBase]; omega) (by simp [keyOfNodeBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.keyOf_mem u h1 h2
      firstEnd_mem := fun v hv => by
        rw [hEq _ (by simp [firstEndBase]; omega) (by simp [firstEndBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.firstEnd_mem v hv
      isRoot_mem := fun v hv => by
        rw [hEq _ (by simp [isRootBase]; omega) (by simp [isRootBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.isRoot_mem v hv
      slot_bij := h.slot_bij
      slotOf_mem := fun v hv => by
        rw [hEq _ (by simp [slotOfVertBase]; omega) (by simp [slotOfVertBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.slotOf_mem v hv
      vertOf_mem := fun sl hsl => by
        rw [hEq _ (by simp [vertOfSlotBase]; omega) (by simp [vertOfSlotBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.vertOf_mem sl hsl
      active_end := fun v hv e he => by
        have he_lt : endKey e < 2 * eCap := by
          have := h.valid.ordWithin.2.2 v e he; simp only [endKey]; cases e.2 <;> simp <;> omega
        rw [hEq _ (by simp [endOwnerBase]; omega) (by simp [endOwnerBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.active_end v hv e he
      inactive_owner := fun k hk hno => by
        rw [hEq _ (by simp [endOwnerBase]; omega) (by simp [endOwnerBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.inactive_owner k hk hno
      markArr_zero := fun k hk => by
        rw [hEq _ (by simp [markArrBase]; omega) (by simp [markArrBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.markArr_zero k hk
      nodesAt := NodesAt.congr tourLayout h.nodesAt fun a ha =>
        hEq a (by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [nodesBase] at this ⊢; omega)
          (inRecords_lt_ordHandle_of_le h.numNodes_le ha).2
      forestInv := h.forestInv
      nodes_exact := h.nodes_exact
      comp_none := h.comp_none
      comp_some := h.comp_some
      tree_class := h.tree_class
      inactive_single := h.inactive_single
      val_active := h.val_active
      val_inactive_rt := h.val_inactive_rt
      val_unused_rt := h.val_unused_rt }

theorem TourCoreAt.valsOk {τ_ord : Type} {w vCap eCap b : ℕ}
    {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem) (hw : vCap + 2 * eCap + 4 < 2 ^ w) :
    TourValsOk w x.numNodes x.st := by
  have hle := h.numNodes_le
  refine ⟨by omega, fun u hu => ?_⟩
  by_cases h1 : 1 ≤ u ∧ u ≤ x.numNodes
  · by_cases hact : ∃ v, endOfKey (x.keyOf u) ∈ s.ord v
    · rw [h.val_active u h1.1 h1.2 hact]
      have := tourRootTagVal_lt h.valid (x := endOfKey (x.keyOf u))
      dsimp only; omega
    · push Not at hact
      rw [h.val_inactive_rt u h1.1 h1.2 hact]; omega
  · rw [h.val_unused_rt u hu (by omega)]; omega

theorem TourCoreAt.mem_compTree_of_active {τ_ord : Type} {vCap eCap b v : ℕ}
    {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem) {e : End} (he : e ∈ s.ord v) :
    let r := s.rf.root v
    let u := x.nodeOf (endKey e)
    v < vCap ∧ r ∈ s.rf.R ∧ r < vCap ∧ endKey e < 2 * eCap ∧
    1 ≤ u ∧ u ≤ x.numNodes ∧ x.keyOf u = endKey e ∧
    ∃ t rest, x.compTree r = some t ∧ x.trees.Perm (t :: rest) ∧
      t.toList.map (fun id => endOfKey (x.keyOf id)) = fullTour s.ord s.rf.F h.valid.compat.forest r ∧
      u ∈ t.toList := by
  have hv_lt : v < vCap := by
    by_contra hge
    have hnil := h.valid.ordWithin.2.1 v (Nat.le_of_not_lt hge)
    rw [hnil] at he; simp at he
  have hvF : v ∈ s.rf.F.V := h.valid.compat.vert v (List.ne_nil_of_mem he)
  have hr_spec := h.valid.root_spec hvF
  have hr_lt : s.rf.root v < vCap := h.valid.verts_lt _ (h.valid.roots_sub hr_spec.1)
  have he_lt : endKey e < 2 * eCap := by
    have := h.valid.ordWithin.2.2 v e he; simp only [endKey]; cases e.2 <;> simp <;> omega
  have hact := h.active_end v hv_lt e he
  have hu_le : x.nodeOf (endKey e) ≤ x.numNodes := (h.nodeOf_mem (endKey e) he_lt).2
  have hu_key : x.keyOf (x.nodeOf (endKey e)) = endKey e := h.nodeOf_keyOf (endKey e) he_lt hact.1
  have he_ft : e ∈ fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v) :=
    ((fullTour_spec h.valid.compat (s.rf.root v)).2 e).mpr ⟨v, he, connected_symm hr_spec.2⟩
  have hft_ne : fullTour s.ord s.rf.F h.valid.compat.forest (s.rf.root v) ≠ [] := List.ne_nil_of_mem he_ft
  obtain ⟨t, ht_eq, ht_mem, ht_map⟩ := h.comp_some (s.rf.root v) hr_spec.1 hft_ne
  have hperm : x.trees.Perm (t :: x.trees.erase t) := List.perm_cons_erase ht_mem
  have hu_mem : x.nodeOf (endKey e) ∈ t.toList := by
    rw [← ht_map] at he_ft
    obtain ⟨u', hu', hu'e⟩ := List.mem_map.mp he_ft
    have hu'_in : 1 ≤ u' ∧ u' ≤ x.numNodes :=
      (h.nodes_exact u').mp (List.mem_flatMap.mpr ⟨t, ht_mem, hu'⟩)
    have hkeq : x.keyOf u' = endKey e := by rw [← hu'e, endKey_endOfKey']
    have hu'eq : u' = x.nodeOf (endKey e) := by rw [← hkeq, (h.keyOf_mem u' hu'_in.1 hu'_in.2).2.2]
    exact hu'eq ▸ hu'
  exact ⟨hv_lt, hr_spec.1, hr_lt, he_lt, by omega, hu_le, hu_key, t, x.trees.erase t, ht_eq,
    hperm, ht_map, hu_mem⟩

/-! ## `ordStore` commit helper and WordRAM slot-decoding helpers -/

theorem ordStoreLog_eq_tourLog (eCap : ℕ) : ordStoreLog eCap = tourLog eCap := rfl

/-- Commit a single-edit record at `hEdit` to the embedded `ordStore`, turning `TourCoreAt` for
`s'` (with `ordStore` still at `s.ord`) into a full `TourRepAt` for `s'`. -/
theorem tourCore_commitOrdStore {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap mul_ord b hEdit words' hIn pos ordOp0 : ℕ}
    {alloc_ord : ℕ → List ℕ → ℕ} {p : Program}
    {ordInit : ℕ} {ordOp : ℕ → ℕ} (hOrdImpl : R_ord.Implements w p ordInit ordOp (ordStoreCapContract vCap eCap mul_ord alloc_ord))
    (hop0 : ordOp 0 = ordOp0) (ω : ℕ → Bool)
    {ord0 : ℕ → List End} {s' : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    {edit : OrdEdit}
    (hcore : TourCoreAt vCap eCap b s' x mem)
    (hord0U : OrdUniqueWithin vCap eCap ord0)
    (hordRep : R_ord.rep (ordHandleOf b vCap eCap) ord0 x.ordX mem)
    (hordGe : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → ordHandleOf b vCap eCap ≤ a)
    (hordFoot : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → a < hIn)
    (hord_le : ordHandleOf b vCap eCap ≤ hIn)
    (hEditsAt : OrdEditsAt mem hEdit [edit] words')
    (hEditsLe : hEdit + words' ≤ hIn)
    (hEditsWithin : OrdEditsWithin vCap eCap [edit])
    (hOrdEq : s'.ord = applyOrdEdit ord0 edit)
    (hzero : ZeroFrom mem hIn)
    (hroom : hIn + alloc_ord 0 [ordHandleOf b vCap eCap, hEdit, words', hIn] < 2 ^ w) :
    ∃ body o st' c ordX',
      p.procs[ordOp0]? = some body ∧
      Runs w p ω body
        (startState [ordHandleOf b vCap eCap, hEdit, words', hIn] mem pos) o st' c ∧
      hIn ≤ o.value ∧ o.value ≤ hIn + alloc_ord 0 [ordHandleOf b vCap eCap, hEdit, words', hIn] ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < hIn, ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → st'.mem a = mem a) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX' a →
        R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (hIn ≤ a ∧ a < o.value)) ∧
      TourRepAt R_ord vCap eCap b s' { x with ordX := ordX' } st'.mem ∧
      c + R_ord.phi (ordHandleOf b vCap eCap) ordX' st'.mem ≤
        mul_ord * (words' + 1) * tourLog eCap + R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem := by
  have hpre : (ordStoreCapContract vCap eCap mul_ord alloc_ord).pre 0 ord0
      [ordHandleOf b vCap eCap, hEdit, words', hIn] mem := by
    refine ⟨ordHandleOf b vCap eCap, hEdit, words', hIn, rfl, ?_, hEditsLe, ?_, ?_⟩
    · rw [hEditsAt.1]; exact hEditsAt
    · rw [hEditsAt.1]; exact hEditsWithin
    · rw [hEditsAt.1]
      intro k hk
      cases k with
      | zero => simpa [applyOrdEdits] using hord0U
      | succ k' =>
        have hk0 : k' = 0 := by simp at hk; omega
        subst hk0
        have heq1 : applyOrdEdits ord0 ([edit].take 1) = s'.ord := by simp [applyOrdEdits, hOrdEq]
        rw [heq1]
        exact ⟨hcore.valid.ordWithin, hcore.valid.compat.unique⟩
  have hargW : ∀ a ∈ [ordHandleOf b vCap eCap, hEdit, words', hIn], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  obtain ⟨body, hget, o, st', c, hrun, sOrd', ordX', hrep', hpost, hresp, hcost⟩ :=
    hOrdImpl.2.2 0 (ordHandleOf b vCap eCap) ord0 x.ordX [ordHandleOf b vCap eCap, hEdit, words', hIn] mem pos ω
      hargW rfl hordRep hpre hordFoot hzero hroom
  rcases hresp with ⟨hle, hle_sp, hz', hfr', hfoot'⟩
  have hha : heapArg [ordHandleOf b vCap eCap, hEdit, words', hIn] = hIn := rfl
  simp only [hha, ordStoreCapContract, List.getD_cons_zero, List.getD_cons_succ] at hle hle_sp hz' hfr' hfoot' hcost
  have hord_post : applyOrdEdits ord0 (readOrdEdits mem hEdit) = s'.ord := by
    rw [hEditsAt.1, applyOrdEdits, List.foldl_cons, List.foldl_nil, ← hOrdEq]
  have hrep_s' : R_ord.rep (ordHandleOf b vCap eCap) s'.ord ordX' st'.mem := by
    rw [← hord_post]; exact (hpost : sOrd' = _) ▸ hrep'
  have hcore' : TourCoreAt vCap eCap b s' { x with ordX := ordX' } st'.mem := by
    have hcore_mem := hcore.congr_fixed fun a ha1 ha2 =>
      hfr' a (by omega) fun hft => by have := hordGe a hft; omega
    exact
      { valid := hcore_mem.valid, header := hcore_mem.header, numNodes_le := hcore_mem.numNodes_le,
        nodeOf_mem := hcore_mem.nodeOf_mem, nodeOf_keyOf := hcore_mem.nodeOf_keyOf,
        keyOf_mem := hcore_mem.keyOf_mem, firstEnd_mem := hcore_mem.firstEnd_mem,
        isRoot_mem := hcore_mem.isRoot_mem, slot_bij := hcore_mem.slot_bij,
        slotOf_mem := hcore_mem.slotOf_mem, vertOf_mem := hcore_mem.vertOf_mem,
        active_end := hcore_mem.active_end, inactive_owner := hcore_mem.inactive_owner,
        markArr_zero := hcore_mem.markArr_zero, nodesAt := hcore_mem.nodesAt,
        forestInv := hcore_mem.forestInv, nodes_exact := hcore_mem.nodes_exact,
        comp_none := hcore_mem.comp_none, comp_some := hcore_mem.comp_some,
        tree_class := hcore_mem.tree_class, inactive_single := hcore_mem.inactive_single,
        val_active := hcore_mem.val_active, val_inactive_rt := hcore_mem.val_inactive_rt,
        val_unused_rt := hcore_mem.val_unused_rt }
  have hge' : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX' a → ordHandleOf b vCap eCap ≤ a := by
    intro a ha
    rcases hfoot' a ha with h1 | ⟨h1, _⟩
    · exact hordGe a h1
    · omega
  rw [hop0] at hget
  refine ⟨body, o, st', c, ordX', hget, hrun, hle, hle_sp, hz', hfr', hfoot', hcore'.toRep hrep_s' hge', ?_⟩
  simpa [ordStoreCapContract, ordStoreLog_eq_tourLog] using hcost

/-- Query `ordStoreOp b 2` (`next [ordH, v, key, h]`) without disturbing `TourCoreAt`, advancing
the heap cursor to `o.value ≤ h + 1`. -/
theorem tourCore_ordNext {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap mul_ord b v key h pos ordOp2 : ℕ}
    {alloc_ord : ℕ → List ℕ → ℕ} {p : Program}
    {ordInit : ℕ} {ordOp : ℕ → ℕ}
    (hOrdImpl : R_ord.Implements w p ordInit ordOp (ordStoreCapContract vCap eCap mul_ord alloc_ord))
    (hop2 : ordOp 2 = ordOp2) (ω : ℕ → Bool)
    {ord0 : ℕ → List End} {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (hcore : TourCoreAt vCap eCap b s x mem)
    (hordRep : R_ord.rep (ordHandleOf b vCap eCap) ord0 x.ordX mem)
    (hordGe : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → ordHandleOf b vCap eCap ≤ a)
    (hordFoot : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → a < h)
    (hord_le : ordHandleOf b vCap eCap ≤ h)
    (hvLt : v < vCap) (hkeyLt : key < 2 * eCap) (hmem_ord : endOfKey key ∈ ord0 v)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w)
    (hzero : ZeroFrom mem h) (hroom : h + 1 < 2 ^ w) :
    ∃ body o st' c ordX',
      p.procs[ordOp2]? = some body ∧
      Runs w p ω body (startState [ordHandleOf b vCap eCap, v, key, h] mem pos) o st' c ∧
      h ≤ o.value ∧ o.value ≤ h + 1 ∧ ZeroFrom st'.mem o.value ∧
      st'.mem h = endKey (cycNext (ord0 v) (endOfKey key)) ∧
      (∀ a < h, ¬R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → st'.mem a = mem a) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX' a →
        R_ord.foot (ordHandleOf b vCap eCap) x.ordX a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX' a → ordHandleOf b vCap eCap ≤ a) ∧
      R_ord.rep (ordHandleOf b vCap eCap) ord0 ordX' st'.mem ∧
      TourCoreAt vCap eCap b s { x with ordX := ordX' } st'.mem ∧
      c + R_ord.phi (ordHandleOf b vCap eCap) ordX' st'.mem ≤
        mul_ord * tourLog eCap + R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem := by
  have hpre : (ordStoreCapContract vCap eCap mul_ord alloc_ord).pre 2 ord0
      [ordHandleOf b vCap eCap, v, key, h] mem :=
    ⟨ordHandleOf b vCap eCap, v, key, h, rfl, hvLt, hmem_ord⟩
  have hargW : ∀ a ∈ [ordHandleOf b vCap eCap, v, key, h], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  obtain ⟨body, hget, o, st', c, hrun, sOrd', ordX', hrep', hpost, hresp, hcost⟩ :=
    hOrdImpl.2.2 2 (ordHandleOf b vCap eCap) ord0 x.ordX [ordHandleOf b vCap eCap, v, key, h] mem pos ω
      hargW rfl hordRep hpre hordFoot hzero hroom
  rcases hresp with ⟨hle, hle_sp, hz', hfr', hfoot'⟩
  have hha : heapArg [ordHandleOf b vCap eCap, v, key, h] = h := rfl
  simp only [hha, ordStoreCapContract, List.getD_cons_zero, List.getD_cons_succ] at hle hle_sp hz' hfr' hfoot' hcost hpost
  rcases hpost with ⟨hsOrd_eq, hans⟩
  have hcore_mem := hcore.congr_fixed fun a ha1 ha2 =>
    hfr' a (by omega) fun hft => by have := hordGe a hft; omega
  have hcore' : TourCoreAt vCap eCap b s { x with ordX := ordX' } st'.mem :=
    { valid := hcore_mem.valid, header := hcore_mem.header, numNodes_le := hcore_mem.numNodes_le,
      nodeOf_mem := hcore_mem.nodeOf_mem, nodeOf_keyOf := hcore_mem.nodeOf_keyOf,
      keyOf_mem := hcore_mem.keyOf_mem, firstEnd_mem := hcore_mem.firstEnd_mem,
      isRoot_mem := hcore_mem.isRoot_mem, slot_bij := hcore_mem.slot_bij,
      slotOf_mem := hcore_mem.slotOf_mem, vertOf_mem := hcore_mem.vertOf_mem,
      active_end := hcore_mem.active_end, inactive_owner := hcore_mem.inactive_owner,
      markArr_zero := hcore_mem.markArr_zero, nodesAt := hcore_mem.nodesAt,
      forestInv := hcore_mem.forestInv, nodes_exact := hcore_mem.nodes_exact,
      comp_none := hcore_mem.comp_none, comp_some := hcore_mem.comp_some,
      tree_class := hcore_mem.tree_class, inactive_single := hcore_mem.inactive_single,
      val_active := hcore_mem.val_active, val_inactive_rt := hcore_mem.val_inactive_rt,
      val_unused_rt := hcore_mem.val_unused_rt }
  have hge' : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) ordX' a → ordHandleOf b vCap eCap ≤ a := by
    intro a ha; rcases hfoot' a ha with h1 | ⟨h1, _⟩; exact hordGe a h1; omega
  have hans_cyc : st'.mem h = endKey (cycNext (ord0 v) (endOfKey key)) := by
    simpa [cycNext] using hans
  rw [hop2] at hget
  refine ⟨body, o, st', c, ordX', hget, hrun, hle, hle_sp, hz', hans_cyc, hfr', hfoot', hge',
    hsOrd_eq ▸ hrep', hcore', by simpa [ordStoreCapContract, ordStoreLog_eq_tourLog] using hcost⟩

theorem runs_decodeSlot_stmt {w dst rRaw rIdx raw idx : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hRaw : st.regs rRaw = raw) (hIdx : st.regs rIdx = idx)
    (h1 : 1 < 2 ^ w) (hrawW : raw < 2 ^ w) :
    Runs w p ω (.cond (.reg rRaw) (.assign dst (.bin .sub (.reg rRaw) (.const 1))) (.assign dst (.reg rIdx)))
      st .normal { st with regs := Function.update st.regs dst (decodeSlot raw idx) }
      (if raw = 0 then 4 else 6) := by
  by_cases h0 : raw = 0
  · subst h0
    have hcond : (Expr.reg rRaw).eval w st = some 0 := by simp [Expr.eval, hRaw]
    have ha : Runs w p ω (.assign dst (.reg rIdx)) st .normal
        { st with regs := Function.update st.regs dst idx } 2 :=
      runs_assign_iff.mpr ⟨idx, by simp [Expr.eval, hIdx], rfl, rfl, rfl⟩
    have hrun := tour_runs_cond_false (s₁ := .assign dst (.bin .sub (.reg rRaw) (.const 1))) hcond ha
    simpa [decodeSlot, Expr.size] using hrun
  · have hcond : (Expr.reg rRaw).eval w st = some raw := by simp [Expr.eval, hRaw]
    have ha : Runs w p ω (.assign dst (.bin .sub (.reg rRaw) (.const 1))) st .normal
        { st with regs := Function.update st.regs dst (raw - 1) } 4 :=
      runs_assign_iff.mpr ⟨raw - 1, by simp [Expr.eval, hRaw, h1, BinOp.eval, (by omega : raw - 1 < 2 ^ w)], rfl, rfl, rfl⟩
    have hrun := tour_runs_cond_true (s₂ := .assign dst (.reg rIdx)) hcond h0 ha
    simpa [decodeSlot, h0, Expr.size] using hrun

theorem slotOfVertBase_eq (b vCap eCap : ℕ) :
    slotOfVertBase b vCap eCap = nextArrBase b vCap eCap + 2 * eCap := by
  simp [slotOfVertBase, nextArrBase]; omega

theorem vertOfSlotBase_eq (b vCap eCap : ℕ) :
    vertOfSlotBase b vCap eCap = slotOfVertBase b vCap eCap + vCap := by
  simp [vertOfSlotBase, slotOfVertBase]; omega

theorem decodeSlot_succ (v i : ℕ) : decodeSlot (v + 1) i = v := by
  simp [decodeSlot]

theorem decodeSlot_zero (i : ℕ) : decodeSlot 0 i = i := by
  simp [decodeSlot]

/-! ## Singleton node allocation & reuse helpers (`initNode`) -/

/-- The singleton `SplayNode` written by `tourInitNodeBody [nb, u, isOpen, isMarked, rootTag]`. -/
def tourSingletonNode (u : ℕ) (v : TourVal) : SplayNode TourVal TourSum Unit :=
  { left := 0, right := 0, par := 0, ppar := 0, sz := 1,
    val := v, sum := tourPayload.single u v, tag := (), rev := false }

private theorem tourSingleton_treeInv {u : ℕ} {v : TourVal}
    {st : SplayState TourVal TourSum Unit} (hu0 : u ≠ 0)
    (hnd : st.nodes u = tourSingletonNode u v) :
    TreeInv tourPayload st (AuxTree.node u .leaf .leaf) := by
  refine ⟨by simp [AuxTree.toList], hu0, by simp [hnd, tourSingletonNode, AuxTree.rootId],
    by simp [hnd, tourSingletonNode, AuxTree.rootId], by simp [hnd, tourSingletonNode],
    fun h => absurd rfl h, by simp [hnd, tourSingletonNode, AuxTree.countNodes], ?_,
    trivial, trivial⟩
  have hrev : (st.nodes u).rev = false := by simp [hnd, tourSingletonNode]
  rw [tourEvalPairs_eq_map (by intro a ha; simp [AuxTree.toList] at ha; subst ha; exact hrev)]
  simp [AuxTree.toList, hnd, tourSingletonNode, tourPayload_laws.combine_empty_right]

private theorem tourNodesAt_update_node {nb cap u : ℕ}
    {st : SplayState TourVal TourSum Unit} {mem mem' : ℕ → ℕ}
    {nd : SplayNode TourVal TourSum Unit}
    (hn : tourLayout.NodesAt mem nb cap st) (hu : u ≤ cap)
    (hnu : tourLayout.NodeAt mem' nb u nd)
    (hfr : ∀ a, (∀ i < 17, a ≠ nb + 17 * u + i) → mem' a = mem a) :
    tourLayout.NodesAt mem' nb cap { nodes := Function.update st.nodes u nd } := by
  intro j hj
  by_cases hju : j = u
  · subst hju; simpa using hnu
  · dsimp only
    rw [Function.update_of_ne hju]
    exact NodeAt.congr tourLayout (hn j hj) fun off hoff => by
      have hoff17 : off < 17 := by simpa [tourLayout_stride] using hoff
      refine hfr (tourLayout.nodeAddr nb j + off) fun i hi => ?_
      simp only [NodeLayout.nodeAddr, tourLayout_stride]
      have : j < u ∨ u < j := lt_or_gt_of_ne hju
      rcases this with h | h <;> omega

/-- Initializing a fresh node `u` (not yet in `trees`) via `tourInitNodeBody` adds the
zero-potential singleton `AuxTree.node u .leaf .leaf` to `trees` and preserves `NodesAt` and
`TourForestInv`. -/
theorem tourInitNode_fresh_preserves {nb cap u : ℕ} {v : TourVal}
    {st : SplayState TourVal TourSum Unit} {trees : List AuxTree} {mem mem' : ℕ → ℕ}
    (hn : tourLayout.NodesAt mem nb cap st) (hf : TourForestInv cap st trees)
    (hu1 : 1 ≤ u) (hucap : u ≤ cap) (hu_fresh : u ∉ trees.flatMap AuxTree.toList)
    (hnu : tourLayout.NodeAt mem' nb u (tourSingletonNode u v))
    (hfr : ∀ a, (∀ i < 17, a ≠ nb + 17 * u + i) → mem' a = mem a) :
    let s' : SplayState TourVal TourSum Unit :=
      { nodes := Function.update st.nodes u (tourSingletonNode u v) }
    tourLayout.NodesAt mem' nb cap s' ∧
    TourForestInv cap s' (AuxTree.node u .leaf .leaf :: trees) ∧
    forestPhi (AuxTree.node u .leaf .leaf :: trees) = forestPhi trees := by
  intro s'
  have hn' := tourNodesAt_update_node hn hucap hnu hfr
  have hinv' : TourForestInv cap s' (AuxTree.node u .leaf .leaf :: trees) :=
    { nonEmpty := fun t ht => by
        rcases List.mem_cons.mp ht with rfl | ht
        · simp
        · exact hf.nonEmpty t ht
      treesInv := fun t ht => by
        rcases List.mem_cons.mp ht with rfl | ht
        · exact tourSingleton_treeInv (v := v) (by omega) (by simp [s'])
        · exact treeInv_agree (hf.treesInv t ht) fun a ha => by
            have hne : a ≠ u := fun heq => hu_fresh (List.mem_flatMap.mpr ⟨t, ht, heq ▸ ha⟩)
            simp [s', Function.update_of_ne hne]
      nodupAll := by
        simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.cons_append]
        exact List.nodup_cons.mpr ⟨hu_fresh, hf.nodupAll⟩
      inCap := fun a ha => by
        simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.cons_append, List.mem_cons] at ha
        rcases ha with rfl | ha; exact ⟨hu1, hucap⟩; exact hf.inCap a ha
      ptrOk := fun a ha => by
        by_cases hau : a = u
        · subst hau; simp [s', tourSingletonNode]
        · simp [s', Function.update_of_ne hau]; exact hf.ptrOk a ha
      noRev := fun a ha => by
        by_cases hau : a = u
        · subst hau; simp [s', tourSingletonNode]
        · simp [s', Function.update_of_ne hau]; exact hf.noRev a ha }
  refine ⟨hn', hinv', by simp [forestPhi, treePhi_singleton_tourVSize]⟩

/-- Initializing a fresh node `u = cap + 1` via `tourInitNodeBody` extends `NodesAt` and
`TourForestInv` from capacity `cap` to `cap + 1`, adding the zero-potential singleton
`AuxTree.node (cap + 1) .leaf .leaf` to `trees`. -/
theorem tourInitNode_fresh_succ_preserves {nb cap : ℕ} {v : TourVal}
    {st : SplayState TourVal TourSum Unit} {trees : List AuxTree} {mem mem' : ℕ → ℕ}
    (hn : tourLayout.NodesAt mem nb cap st) (hf : TourForestInv cap st trees)
    (hnu : tourLayout.NodeAt mem' nb (cap + 1) (tourSingletonNode (cap + 1) v))
    (hfr : ∀ a, (∀ i < 17, a ≠ nb + 17 * (cap + 1) + i) → mem' a = mem a) :
    let s' : SplayState TourVal TourSum Unit :=
      { nodes := Function.update st.nodes (cap + 1) (tourSingletonNode (cap + 1) v) }
    tourLayout.NodesAt mem' nb (cap + 1) s' ∧
    TourForestInv (cap + 1) s' (AuxTree.node (cap + 1) .leaf .leaf :: trees) ∧
    forestPhi (AuxTree.node (cap + 1) .leaf .leaf :: trees) = forestPhi trees := by
  intro s'
  have hu_fresh : cap + 1 ∉ trees.flatMap AuxTree.toList := fun hm => by
    have := (hf.inCap _ hm).2; omega
  have hn' : tourLayout.NodesAt mem' nb (cap + 1) s' := by
    intro j hj
    by_cases hju : j = cap + 1
    · subst hju; simpa [s'] using hnu
    · dsimp only [s']
      rw [Function.update_of_ne hju]
      exact NodeAt.congr tourLayout (hn j (by omega)) fun off hoff => by
        have hoff17 : off < 17 := by simpa [tourLayout_stride] using hoff
        refine hfr (tourLayout.nodeAddr nb j + off) fun i hi => ?_
        simp only [NodeLayout.nodeAddr, tourLayout_stride]; omega
  have hinv' : TourForestInv (cap + 1) s' (AuxTree.node (cap + 1) .leaf .leaf :: trees) :=
    { nonEmpty := fun t ht => by
        rcases List.mem_cons.mp ht with rfl | ht; · simp
        · exact hf.nonEmpty t ht
      treesInv := fun t ht => by
        rcases List.mem_cons.mp ht with rfl | ht
        · exact tourSingleton_treeInv (v := v) (by omega) (by simp [s'])
        · exact treeInv_agree (hf.treesInv t ht) fun a ha => by
            have hne : a ≠ cap + 1 := fun heq => hu_fresh (List.mem_flatMap.mpr ⟨t, ht, heq ▸ ha⟩)
            simp [s', Function.update_of_ne hne]
      nodupAll := by
        simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.cons_append]
        exact List.nodup_cons.mpr ⟨hu_fresh, hf.nodupAll⟩
      inCap := fun a ha => by
        simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.cons_append, List.mem_cons] at ha
        rcases ha with rfl | ha; · omega
        · have := hf.inCap a ha; omega
      ptrOk := fun a ha => by
        by_cases hau : a = cap + 1
        · subst hau; simp [s', tourSingletonNode]
        · simp only [s', Function.update_of_ne hau]
          have hp := hf.ptrOk a (by omega)
          exact ⟨by omega, by omega, by omega, by omega⟩
      noRev := fun a ha => by
        by_cases hau : a = cap + 1
        · subst hau; simp [s', tourSingletonNode]
        · simp [s', Function.update_of_ne hau]; exact hf.noRev a (by omega) }
  refine ⟨hn', hinv', by simp [forestPhi, treePhi_singleton_tourVSize]⟩

/-- Reinitializing an existing detached singleton `AuxTree.node u .leaf .leaf` in `trees` via
`tourInitNodeBody` updates its `val` in place and preserves `NodesAt`, `TourForestInv`, and
`forestPhi`. -/
theorem tourInitNode_reuse_preserves {nb cap u : ℕ} {v : TourVal}
    {st : SplayState TourVal TourSum Unit} {rest : List AuxTree} {mem mem' : ℕ → ℕ}
    (hn : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (AuxTree.node u .leaf .leaf :: rest))
    (hnu : tourLayout.NodeAt mem' nb u (tourSingletonNode u v))
    (hfr : ∀ a, (∀ i < 17, a ≠ nb + 17 * u + i) → mem' a = mem a) :
    let s' : SplayState TourVal TourSum Unit :=
      { nodes := Function.update st.nodes u (tourSingletonNode u v) }
    tourLayout.NodesAt mem' nb cap s' ∧
    TourForestInv cap s' (AuxTree.node u .leaf .leaf :: rest) := by
  intro s'
  have hu_in := hf.mem_inCap (t := AuxTree.node u .leaf .leaf) (u := u) (by simp) (by simp [AuxTree.toList])
  have hu_nrest : u ∉ rest.flatMap AuxTree.toList := by
    have hnd := hf.nodupAll
    simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.cons_append] at hnd
    exact (List.nodup_cons.mp hnd).1
  have hn' := tourNodesAt_update_node hn hu_in.2 hnu hfr
  refine ⟨hn',
    { nonEmpty := hf.nonEmpty
      treesInv := fun t ht => by
        rcases List.mem_cons.mp ht with rfl | ht
        · exact tourSingleton_treeInv (v := v) (by omega) (by simp [s'])
        · exact treeInv_agree (hf.treesInv t (by simp [ht])) fun a ha => by
            have hne : a ≠ u := fun heq => hu_nrest (List.mem_flatMap.mpr ⟨t, ht, heq ▸ ha⟩)
            simp [s', Function.update_of_ne hne]
      nodupAll := hf.nodupAll
      inCap := hf.inCap
      ptrOk := fun a ha => by
        by_cases hau : a = u
        · subst hau; simp [s', tourSingletonNode]
        · simp [s', Function.update_of_ne hau]; exact hf.ptrOk a ha
      noRev := fun a ha => by
        by_cases hau : a = u
        · subst hau; simp [s', tourSingletonNode]
        · simp [s', Function.update_of_ne hau]; exact hf.noRev a ha }⟩

/-- If `keyX < 2 * eCap` has no allocated node (`x.nodeOf keyX = 0`), then `x.numNodes < 2 * eCap`. -/
theorem TourCoreAt.numNodes_lt_of_zero {τ_ord : Type} {vCap eCap b keyX : ℕ}
    {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem) (hk : keyX < 2 * eCap) (h0 : x.nodeOf keyX = 0) :
    x.numNodes < 2 * eCap := by
  by_contra hge
  have heq : x.numNodes = 2 * eCap := by have := h.numNodes_le; omega
  let S : Finset ℕ := (Finset.Icc 1 x.numNodes).image x.keyOf
  have hinj : Set.InjOn x.keyOf (Finset.Icc 1 x.numNodes : Set ℕ) := by
    intro a ha b' hb' hab
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb'
    have h1 := (h.keyOf_mem a ha.1 ha.2).2.2
    have h2 := (h.keyOf_mem b' hb'.1 hb'.2).2.2
    rw [← h1, ← h2, hab]
  have hcard : S.card = 2 * eCap := by
    rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]; omega
  have hsub : S ⊆ (Finset.range (2 * eCap)).erase keyX := by
    intro k hm
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
    simp only [Finset.mem_Icc] at hu
    have hkm := h.keyOf_mem u hu.1 hu.2
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr hkm.2.1⟩
    intro hkx; rw [hkx, h0] at hkm; omega
  have hlt := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_range.mpr hk), Finset.card_range] at hlt
  omega

end MinCostFlow.SparseCore.Program
