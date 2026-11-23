module

public import MinCostFlow.SparseCore.Program.TourSplayList
public import MinCostFlow.SparseCore.Program.TourSplayNext
public import MinCostFlow.SparseCore.Program.TourContract
public import MinCostFlow.SparseCore.Program.OrdStoreContract
import Mathlib.Tactic

/-!
# Concrete memory representation (`tourRep`) and locality for core rotation tours

Defines the concrete memory layout of `tourRep : DSRep TourAbs` parameterized by an order-store
representation `R_ord : DSRep (ℕ → List End)`:
- A 16-word header at handle `b`, followed by pre-reserved zero-initialized arrays (`firstEnd`,
  `isRoot`, `nodeOfEnd`, `endOwner`, `keyOfNode`, `markArr`, `predArr`, `nextArr`, and the
  `17 * (2 * eCap + 1)` splay node table), occupying `[b, b + tourFixedSize vCap eCap)`.
- The embedded `ordStore` handle at `ordHandleOf b vCap eCap := b + tourFixedSize vCap eCap`,
  with disjoint footprint lying at `≥ ordHandleOf b vCap eCap`.
- Potential `R_ord.phi + TOUR_PHI_MULT * forestPhi x.trees`, and `tourRep_local`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Header offsets and fixed-block geometry -/

def HDR_VCAP : ℕ := 0
def HDR_ECAP : ℕ := 1
def HDR_ORD_H : ℕ := 2
def HDR_NUM_NODES : ℕ := 3
def HDR_FIRST_END : ℕ := 4
def HDR_IS_ROOT : ℕ := 5
def HDR_NODE_OF_END : ℕ := 6
def HDR_END_OWNER : ℕ := 7
def HDR_KEY_OF_NODE : ℕ := 8
def HDR_MARK_ARR : ℕ := 9
def HDR_PRED_ARR : ℕ := 10
def HDR_NEXT_ARR : ℕ := 11
def HDR_NODES_BASE : ℕ := 12
def HDR_FOOT_END : ℕ := 13
def HDR_FUEL : ℕ := 14
def HDR_SIZE : ℕ := 16

def firstEndBase (b : ℕ) : ℕ := b + 16
def isRootBase (b vCap : ℕ) : ℕ := b + 16 + vCap
def nodeOfEndBase (b vCap : ℕ) : ℕ := b + 16 + 2 * vCap
def endOwnerBase (b vCap eCap : ℕ) : ℕ := b + 16 + 2 * vCap + 2 * eCap
def keyOfNodeBase (b vCap eCap : ℕ) : ℕ := b + 16 + 2 * vCap + 4 * eCap
def markArrBase (b vCap eCap : ℕ) : ℕ := b + 16 + 2 * vCap + 6 * eCap + 1
def predArrBase (b vCap eCap : ℕ) : ℕ := b + 16 + 2 * vCap + 8 * eCap + 1
def nextArrBase (b vCap eCap : ℕ) : ℕ := b + 16 + 2 * vCap + 10 * eCap + 1
def slotOfVertBase (b vCap eCap : ℕ) : ℕ := b + 16 + 2 * vCap + 12 * eCap + 1
def vertOfSlotBase (b vCap eCap : ℕ) : ℕ := b + 16 + 3 * vCap + 12 * eCap + 1
def nodesBase (b vCap eCap : ℕ) : ℕ := b + 16 + 4 * vCap + 12 * eCap + 1

/-- Total fixed words reserved by the tour data structure before the embedded `ordStore`. -/
def tourFixedSize (vCap eCap : ℕ) : ℕ :=
  16 + 4 * vCap + 12 * eCap + 1 + 17 * (2 * eCap + 1)

/-- Decode a lazy-identity slot/vertex table entry: `0` stands for identity `i`, and `s + 1`
stands for `s`. -/
def decodeSlot (raw i : ℕ) : ℕ :=
  if raw = 0 then i else raw - 1

/-- Handle of the embedded `ordStore` placed immediately after the fixed tour arrays. -/
def ordHandleOf (b vCap eCap : ℕ) : ℕ := b + tourFixedSize vCap eCap

theorem nodesBase_end_eq (b vCap eCap : ℕ) :
    nodesBase b vCap eCap + 17 * (2 * eCap + 1) = ordHandleOf b vCap eCap := by
  simp only [nodesBase, ordHandleOf, tourFixedSize]; omega

theorem inRecords_lt_ordHandle_of_le {b vCap eCap cap a : ℕ} (hcap : cap ≤ 2 * eCap)
    (h : tourLayout.InRecords (nodesBase b vCap eCap) cap a) :
    nodesBase b vCap eCap ≤ a ∧ a < ordHandleOf b vCap eCap := by
  simp only [NodeLayout.InRecords, nodeAddr, tourLayout_stride, nodesBase, ordHandleOf, tourFixedSize] at h ⊢
  omega

theorem inRecords_lt_ordHandle {b vCap eCap a : ℕ}
    (h : tourLayout.InRecords (nodesBase b vCap eCap) (2 * eCap) a) :
    nodesBase b vCap eCap ≤ a ∧ a < ordHandleOf b vCap eCap :=
  inRecords_lt_ordHandle_of_le (le_refl _) h

theorem not_inRecords_of_lt_nodesBase {b vCap eCap cap a : ℕ}
    (h : a < nodesBase b vCap eCap) :
    ¬tourLayout.InRecords (nodesBase b vCap eCap) cap a := by
  intro hr
  simp only [NodeLayout.InRecords, nodeAddr, tourLayout_stride] at hr
  omega

theorem not_inRecords_of_ge_ordHandle_of_le {b vCap eCap cap a : ℕ} (hcap : cap ≤ 2 * eCap)
    (h : ordHandleOf b vCap eCap ≤ a) :
    ¬tourLayout.InRecords (nodesBase b vCap eCap) cap a := by
  intro hr; have := (inRecords_lt_ordHandle_of_le hcap hr).2; omega

theorem not_inRecords_of_ge_ordHandle {b vCap eCap a : ℕ}
    (h : ordHandleOf b vCap eCap ≤ a) :
    ¬tourLayout.InRecords (nodesBase b vCap eCap) (2 * eCap) a :=
  not_inRecords_of_ge_ordHandle_of_le (le_refl _) h

/-! ## Concrete state and representation predicate -/

/-- Concrete state of the core rotation tour data structure. -/
structure TourConcrete (τ_ord : Type) where
  ordX : τ_ord
  numNodes : ℕ
  st : SplayState TourVal TourSum Unit
  trees : List AuxTree
  nodeOf : ℕ → ℕ
  keyOf : ℕ → ℕ
  compTree : ℕ → Option AuxTree
  slotOf : ℕ → ℕ
  vertOf : ℕ → ℕ

/-- Header words stored at `b + 0..14`. -/
def TourHeaderAt (vCap eCap b numNodes : ℕ) (mem : ℕ → ℕ) : Prop :=
  mem (b + HDR_VCAP) = vCap ∧
  mem (b + HDR_ECAP) = eCap ∧
  mem (b + HDR_ORD_H) = ordHandleOf b vCap eCap ∧
  mem (b + HDR_NUM_NODES) = numNodes ∧
  mem (b + HDR_FIRST_END) = firstEndBase b ∧
  mem (b + HDR_IS_ROOT) = isRootBase b vCap ∧
  mem (b + HDR_NODE_OF_END) = nodeOfEndBase b vCap ∧
  mem (b + HDR_END_OWNER) = endOwnerBase b vCap eCap ∧
  mem (b + HDR_KEY_OF_NODE) = keyOfNodeBase b vCap eCap ∧
  mem (b + HDR_MARK_ARR) = markArrBase b vCap eCap ∧
  mem (b + HDR_PRED_ARR) = predArrBase b vCap eCap ∧
  mem (b + HDR_NEXT_ARR) = nextArrBase b vCap eCap ∧
  mem (b + HDR_NODES_BASE) = nodesBase b vCap eCap ∧
  mem (b + HDR_FOOT_END) = ordHandleOf b vCap eCap ∧
  mem (b + HDR_FUEL) = 2 * eCap + 2

/-- Root tag stored on an active end `x`: `r + 1` if `x` is the first end of some root `r ∈ s.rf.R`,
else `0`. -/
noncomputable def tourRootTagVal (s : TourAbs) (x : End) : ℕ :=
  open Classical in
  if h : ∃ r ∈ s.rf.R, (s.ord r).head? = some x then h.choose + 1 else 0

theorem tourRootTagVal_eq_succ {vCap eCap r : ℕ} {s : TourAbs} {x : End}
    (hv : TourValid vCap eCap s) (hr : r ∈ s.rf.R) (hh : (s.ord r).head? = some x) :
    tourRootTagVal s x = r + 1 := by
  classical
  have hex : ∃ r' ∈ s.rf.R, (s.ord r').head? = some x := ⟨r, hr, hh⟩
  simp only [tourRootTagVal, hex, ↓reduceDIte]
  have hr' : hex.choose ∈ s.rf.R := hex.choose_spec.1
  have hh' : (s.ord hex.choose).head? = some x := hex.choose_spec.2
  have hm1 : x ∈ s.ord r := List.mem_of_head? hh
  have hm2 : x ∈ s.ord hex.choose := List.mem_of_head? hh'
  have heq : hex.choose = r := hv.compat.unique _ r x hm2 hm1
  rw [heq]

theorem tourRootTagVal_eq_zero {s : TourAbs} {x : End}
    (hno : ∀ r ∈ s.rf.R, (s.ord r).head? ≠ some x) :
    tourRootTagVal s x = 0 := by
  classical
  have hne : ¬∃ r ∈ s.rf.R, (s.ord r).head? = some x := by
    rintro ⟨r, hr, hh⟩; exact hno r hr hh
  simp [tourRootTagVal, hne]

theorem tourRootTagVal_lt {vCap eCap : ℕ} {s : TourAbs} {x : End}
    (hv : TourValid vCap eCap s) : tourRootTagVal s x ≤ vCap := by
  classical
  unfold tourRootTagVal
  split_ifs with h
  · have hmem : x ∈ s.ord h.choose := List.mem_of_head? h.choose_spec.2
    have hlt : h.choose < vCap := by
      by_contra hge
      have hnil := hv.ordWithin.2.1 h.choose (Nat.le_of_not_lt hge)
      rw [hnil] at hmem; simp at hmem
    omega
  · omega

/-- Full concrete representation invariant for `tourRep`. -/
structure TourRepAt (R_ord : DSRep (ℕ → List End)) (vCap eCap b : ℕ)
    (s : TourAbs) (x : TourConcrete R_ord.τ) (mem : ℕ → ℕ) : Prop where
  valid : TourValid vCap eCap s
  ordRep : R_ord.rep (ordHandleOf b vCap eCap) s.ord x.ordX mem
  ordFootGe : ∀ a, R_ord.foot (ordHandleOf b vCap eCap) x.ordX a → ordHandleOf b vCap eCap ≤ a
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

/-! ## `DSRep TourAbs` and locality -/

/-- Footprint of `tourRep`: the fixed tour block `[b, ordHandleOf b vCap eCap)` plus the
embedded `ordStore` footprint. -/
def tourFoot (R_ord : DSRep (ℕ → List End)) (vCap eCap b : ℕ)
    (x : TourConcrete R_ord.τ) (a : ℕ) : Prop :=
  (b ≤ a ∧ a < ordHandleOf b vCap eCap) ∨ R_ord.foot (ordHandleOf b vCap eCap) x.ordX a

/-- Potential of `tourRep`: `ordStore` potential plus `TOUR_PHI_MULT * forestPhi x.trees`. -/
def tourPhi (R_ord : DSRep (ℕ → List End)) (vCap eCap b : ℕ)
    (x : TourConcrete R_ord.τ) (mem : ℕ → ℕ) : ℕ :=
  R_ord.phi (ordHandleOf b vCap eCap) x.ordX mem + TOUR_PHI_MULT * forestPhi x.trees

/-- The `DSRep TourAbs` for core rotation tours. -/
def tourRep (R_ord : DSRep (ℕ → List End)) (vCap eCap : ℕ) : DSRep TourAbs where
  τ := TourConcrete R_ord.τ
  rep b s x mem := TourRepAt R_ord vCap eCap b s x mem
  phi b x mem := tourPhi R_ord vCap eCap b x mem
  foot b x a := tourFoot R_ord vCap eCap b x a

theorem tourRep_local {R_ord : DSRep (ℕ → List End)} (hLoc : R_ord.Local) (vCap eCap : ℕ) :
    (tourRep R_ord vCap eCap).Local := by
  intro b s x mem mem' hEq
  have hFixed : ∀ a, b ≤ a → a < ordHandleOf b vCap eCap → mem a = mem' a := fun a h1 h2 =>
    hEq a (Or.inl ⟨h1, h2⟩)
  have hOrd := hLoc (ordHandleOf b vCap eCap) s.ord x.ordX mem mem' fun a ha => hEq a (Or.inr ha)
  refine ⟨fun h => ?_, by simp only [tourRep, tourPhi, hOrd.2]⟩
  dsimp only [tourRep] at h ⊢
  have hhdr : TourHeaderAt vCap eCap b x.numNodes mem' := by
    rcases h.header with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    have hf : ∀ k < 16, mem' (b + k) = mem (b + k) := fun k hk =>
      (hFixed (b + k) (by omega) (by simp only [ordHandleOf, tourFixedSize]; omega)).symm
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
      ordRep := hOrd.1 h.ordRep
      ordFootGe := h.ordFootGe
      header := hhdr
      numNodes_le := h.numNodes_le
      nodeOf_mem := fun k hk => by
        rw [← hFixed _ (by simp [nodeOfEndBase]; omega) (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.nodeOf_mem k hk
      nodeOf_keyOf := h.nodeOf_keyOf
      keyOf_mem := fun u h1 h2 => by
        have hle := h.numNodes_le
        rw [← hFixed _ (by simp [keyOfNodeBase]; omega) (by simp [keyOfNodeBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.keyOf_mem u h1 h2
      firstEnd_mem := fun v hv => by
        rw [← hFixed _ (by simp [firstEndBase]; omega) (by simp [firstEndBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.firstEnd_mem v hv
      isRoot_mem := fun v hv => by
        rw [← hFixed _ (by simp [isRootBase]; omega) (by simp [isRootBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.isRoot_mem v hv
      slot_bij := h.slot_bij
      slotOf_mem := fun v hv => by
        rw [← hFixed _ (by simp [slotOfVertBase]; omega) (by simp [slotOfVertBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.slotOf_mem v hv
      vertOf_mem := fun sl hsl => by
        rw [← hFixed _ (by simp [vertOfSlotBase]; omega) (by simp [vertOfSlotBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.vertOf_mem sl hsl
      active_end := fun v hv e he => by
        have he_lt : endKey e < 2 * eCap := by
          have := h.valid.ordWithin.2.2 v e he; simp only [endKey]; cases e.2 <;> simp <;> omega
        rw [← hFixed _ (by simp [endOwnerBase]; omega) (by simp [endOwnerBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.active_end v hv e he
      inactive_owner := fun k hk hno => by
        rw [← hFixed _ (by simp [endOwnerBase]; omega) (by simp [endOwnerBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.inactive_owner k hk hno
      markArr_zero := fun k hk => by
        rw [← hFixed _ (by simp [markArrBase]; omega) (by simp [markArrBase, ordHandleOf, tourFixedSize]; omega)]
        exact h.markArr_zero k hk
      nodesAt := NodesAt.congr tourLayout h.nodesAt fun a ha =>
        (hFixed a (by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [nodesBase] at this ⊢; omega)
          (inRecords_lt_ordHandle_of_le h.numNodes_le ha).2).symm
      forestInv := h.forestInv
      nodes_exact := h.nodes_exact
      comp_none := h.comp_none
      comp_some := h.comp_some
      tree_class := h.tree_class
      inactive_single := h.inactive_single
      val_active := h.val_active
      val_inactive_rt := h.val_inactive_rt
      val_unused_rt := h.val_unused_rt }

/-! ## Derived lemmas from `TourRepAt` -/

theorem TourRepAt.valsOk {R_ord : DSRep (ℕ → List End)} {w vCap eCap b : ℕ}
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) :
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

end MinCostFlow.SparseCore.Program
