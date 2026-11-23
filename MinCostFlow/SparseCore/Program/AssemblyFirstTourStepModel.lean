module

public import MinCostFlow.SparseCore.Program.AssemblyFirstTourFacts
public import MinCostFlow.SparseCore.Program.OutSplitBound
public import MinCostFlow.SparseCore.CanonCoreSpec

import all MinCostFlow.SparseCore.Program.OutSplitBound
import all MinCostFlow.SparseCore.Program.AssemblyFirstSplitLists
import Mathlib.Tactic

/-!
# Model invariants and mark-potential telescoping for the block tour step (`AssemblyFirstTourStepModel`)

Provides the pure mathematical lemmas backing the deterministic block-by-block tour driver
(`AssemblyFirstTourStepProg.lean`, `AssemblyFirstTourStepProof.lean`):

1. **Graph-equivalence invariance of `TourRepAt` (`tourRepAt_congr_graphEq`)**: `TourRepAt` and
   `fullTour` depend on `s.rf.F` only up to `GraphEq` (`V`, `E`, and `tail`/`head` on `E`), so a
   tour state reached via `eraseForestEdge` / `applyUpdate (.split ...)` matches `cs'.RF`
   propositionally at the end of the step.
2. **Tour mark-potential (`tourMarkPot`)**: defines
   `tourMarkPot keep s := ∑ r ∈ s.rf.R, splitPot (edgeEnds keep) (tourMarkedList s r).toFinset`
   directly on `TourAbs`, links it at the start to `markPot keep tr.S_cur.E (coreGraph G L)`, and
   proves the single-step bounds for every tour operation:
   - `.insertBefore` (unchanged),
   - `.dropEdge e` (`e ∉ keep`, non-increasing),
   - `.rotateTo` (unchanged),
   - any forest-refinement split `(kept, fresh)` (`Y.length + tourMarkPot' ≤ min deg_S' + tourMarkPot`,
     plus all single-record `OutSplitListsAt` properties for `outSmallSide`).
3. **Canonical split-list synchronization (`canonSplitList`)**:
   - Proves `(canonSplitList cs U).length = batchSplitCount (canonCoreBatch cs U)` and
     `batchSplitCount (canonCoreBatch cs U) ≤ tr.S_cur.batchEnc info.U_S` and `≤ vCap`.
   - Proves that every release entry `⟨true, e, kept, fresh⟩` commutes past preceding non-forest
     updates (`.insert` and non-forest `.delete`), keeping `TourValid`, `OutMarksOf`, `keep`-src
     agreement, and `OutSplitListsAt` aligned with `restrictSplits keep (canonCoreBatch cs U)`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## 1. `GraphEq` invariance of `fullTour`, `coreTour`, and `TourRepAt` -/

private lemma connected_iff_of_graphEq {F₁ F₂ : MGraph} (hEq : GraphEq F₁ F₂) {u v : ℕ} :
    F₁.Connected u v ↔ F₂.Connected u v := by
  have hwalk : ∀ {G₁ G₂ : MGraph}, GraphEq G₁ G₂ →
      ∀ {a b : ℕ} {P : List End}, G₁.IsWalk a b P → G₂.IsWalk a b P := by
    intro G₁ G₂ hG a b P hP
    induction hP with
    | nil => exact MGraph.IsWalk.nil _
    | @cons u v x xs he hsrc _ ih =>
      have he2 : x.1 ∈ G₂.E := hG.2.1 ▸ he
      have hsrc2 : G₂.src x = u := by
        obtain ⟨e, b⟩ := x
        cases b
        · exact (hG.2.2 e he).2.symm.trans hsrc
        · exact (hG.2.2 e he).1.symm.trans hsrc
      have hdst2 : G₂.dst x = G₁.dst x := by
        obtain ⟨e, b⟩ := x
        cases b
        · exact (hG.2.2 e he).1.symm
        · exact (hG.2.2 e he).2.symm
      rw [← hdst2] at ih
      exact MGraph.IsWalk.cons he2 hsrc2 ih
  exact ⟨fun ⟨P, hP⟩ => ⟨P, hwalk hEq hP⟩, fun ⟨P, hP⟩ => ⟨P, hwalk (graphEq_symm hEq) hP⟩⟩

private lemma graphEq_eraseForestEdge {F₁ F₂ : MGraph} (hEq : GraphEq F₁ F₂) (e : ℕ) :
    GraphEq (eraseForestEdge F₁ e) (eraseForestEdge F₂ e) := by
  refine ⟨hEq.1, by simp [hEq.2.1], fun f hf => ?_⟩
  have hf1 : f ∈ F₁.E := (Finset.mem_erase.mp hf).2
  exact hEq.2.2 f hf1

private lemma fullTourBlocks_congr_graphEq (ord : ℕ → List End) {F₀₁ F₀₂ : MGraph}
    (hEq0 : GraphEq F₀₁ F₀₂) :
    ∀ (n : ℕ) (F₁ F₂ : MGraph) (hF₁ : F₁.IsForest) (hF₂ : F₂.IsForest) (v : ℕ) (xs : List End),
      (compOf F₁ v).card = n → GraphEq F₁ F₂ →
      fullTourBlocks ord F₀₁ F₁ hF₁ v xs = fullTourBlocks ord F₀₂ F₂ hF₂ v xs := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F₁ F₂ hF₁ hF₂ v xs hn hEq
    rw [fullTourBlocks.eq_def ord F₀₁ F₁ hF₁ v xs, fullTourBlocks.eq_def ord F₀₂ F₂ hF₂ v xs]
    apply List.flatMap_congr
    intro x _
    have hiff0 : x.1 ∈ F₀₁.E ↔ x.1 ∈ F₀₂.E := by rw [hEq0.2.1]
    have hiff : (x.1 ∈ F₁.E ∧ F₁.src x = v) ↔ (x.1 ∈ F₂.E ∧ F₂.src x = v) := by
      constructor
      · rintro ⟨he, hs⟩
        have he2 : x.1 ∈ F₂.E := hEq.2.1 ▸ he
        refine ⟨he2, ?_⟩
        obtain ⟨e, b⟩ := x; cases b
        · exact (hEq.2.2 e he).2.symm.trans hs
        · exact (hEq.2.2 e he).1.symm.trans hs
      · rintro ⟨he, hs⟩
        have he1 : x.1 ∈ F₁.E := hEq.2.1.symm ▸ he
        refine ⟨he1, ?_⟩
        obtain ⟨e, b⟩ := x; cases b
        · exact (hEq.2.2 e he1).2.trans hs
        · exact (hEq.2.2 e he1).1.trans hs
    by_cases h0 : x.1 ∈ F₀₁.E
    · have h02 : x.1 ∈ F₀₂.E := hiff0.mp h0
      simp only [h0, h02, not_true_eq_false, ↓reduceIte]
      by_cases h1 : x.1 ∈ F₁.E ∧ F₁.src x = v
      · have h2 : x.1 ∈ F₂.E ∧ F₂.src x = v := hiff.mp h1
        rw [dite_eq_left h1, dite_eq_left h2]
        have hdst : F₁.dst x = F₂.dst x := by
          obtain ⟨e, b⟩ := x; cases b
          · exact (hEq.2.2 e h1.1).1
          · exact (hEq.2.2 e h1.1).2
        rw [hdst]
        have hlt : (compOf (eraseForestEdge F₁ x.1) (F₂.dst x)).card < n := by
          rw [← hn, ← hdst, ← h1.2]
          exact branch_card_lt hF₁ h1.1
        rw [ih _ hlt (eraseForestEdge F₁ x.1) (eraseForestEdge F₂ x.1)
          (isForest_eraseEdge hF₁ x.1) (isForest_eraseEdge hF₂ x.1) (F₂.dst x)
          (afterEnd x.flip (ord (F₂.dst x))) rfl (graphEq_eraseForestEdge hEq x.1)]
      · have h2 : ¬(x.1 ∈ F₂.E ∧ F₂.src x = v) := fun h => h1 (hiff.mpr h)
        rw [dite_eq_right h1, dite_eq_right h2]
    · have h02 : x.1 ∉ F₀₂.E := fun h => h0 (hiff0.mpr h)
      simp [h0, h02]

private lemma isForest_of_graphEq {F₁ F₂ : MGraph} (hEq : GraphEq F₁ F₂) (hF₁ : F₁.IsForest) :
    F₂.IsForest := by
  refine ⟨fun e he => ?_, fun P ⟨hne, hnd, hw⟩ => ?_⟩
  · have he1 : e ∈ F₁.E := hEq.2.1.symm ▸ he
    obtain ⟨ht, hh⟩ := hF₁.1 e he1
    rw [← (hEq.2.2 e he1).1, ← (hEq.2.2 e he1).2, ← hEq.1]
    exact ⟨ht, hh⟩
  · exact hF₁.2 P ⟨hne, hnd, by
      obtain ⟨v, hP⟩ := hw
      have hwalk : ∀ {a b : ℕ} {Q : List End}, F₂.IsWalk a b Q → F₁.IsWalk a b Q := by
        intro a b Q hQ
        induction hQ with
        | nil => exact MGraph.IsWalk.nil _
        | @cons u v x xs he hsrc _ ih =>
          have he1 : x.1 ∈ F₁.E := hEq.2.1.symm ▸ he
          have hs1 : F₁.src x = u := by
            obtain ⟨e, b⟩ := x; cases b
            · exact (hEq.2.2 e he1).2.trans hsrc
            · exact (hEq.2.2 e he1).1.trans hsrc
          have hd1 : F₁.dst x = F₂.dst x := by
            obtain ⟨e, b⟩ := x; cases b
            · exact (hEq.2.2 e he1).1
            · exact (hEq.2.2 e he1).2
          exact MGraph.IsWalk.cons he1 hs1 (hd1.symm ▸ ih)
      exact ⟨v, hwalk hP⟩⟩

public section

/-- `fullTour` depends on the forest only up to `GraphEq`. -/
theorem fullTour_congr_graphEq (ord : ℕ → List End) {F₁ F₂ : MGraph}
    (hF₁ : F₁.IsForest) (hF₂ : F₂.IsForest) (hEq : GraphEq F₁ F₂) (v : ℕ) :
    fullTour ord F₁ hF₁ v = fullTour ord F₂ hF₂ v :=
  fullTourBlocks_congr_graphEq ord hEq (compOf F₁ v).card F₁ F₂ hF₁ hF₂ v (ord v) rfl hEq

/-- `coreTour` depends on `rf.F` only up to `GraphEq`. -/
theorem coreTour_congr_graphEq (ord : ℕ → List End) {rf₁ rf₂ : RootedForest}
    (hEq : GraphEq rf₁.F rf₂.F) (hR : rf₁.R = rf₂.R) (r : ℕ) :
    coreTour ord rf₁ r = coreTour ord rf₂ r := by
  by_cases hF₁ : rf₁.F.IsForest
  · have hF₂ : rf₂.F.IsForest := isForest_of_graphEq hEq hF₁
    by_cases hr : r ∈ rf₁.R
    · have hr2 : r ∈ rf₂.R := hR ▸ hr
      rw [← fullTour_filter_open ord hF₁ hr, ← fullTour_filter_open ord hF₂ hr2,
        fullTour_congr_graphEq ord hF₁ hF₂ hEq r, hEq.2.1]
    · have hr2 : r ∉ rf₂.R := hR ▸ hr
      simp [coreTour, hr, hr2]
  · have hF₂ : ¬ rf₂.F.IsForest := fun h2 => hF₁ (isForest_of_graphEq (graphEq_symm hEq) h2)
    simp [coreTour, hF₁, hF₂]

/-- `TourRepAt` is invariant under replacing `s.rf.F` by a `GraphEq` forest with the same root set. -/
theorem tourRepAt_congr_graphEq {R_ord : DSRep (ℕ → List End)} {vCap eCap b : ℕ}
    {s₁ s₂ : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (hord : s₁.ord = s₂.ord) (hmk : s₁.marked = s₂.marked)
    (hEq : GraphEq s₁.rf.F s₂.rf.F) (hR : s₁.rf.R = s₂.rf.R)
    (h : TourRepAt R_ord vCap eCap b s₁ x mem) :
    TourRepAt R_ord vCap eCap b s₂ x mem := by
  have hF₂ : s₂.rf.F.IsForest := isForest_of_graphEq hEq h.valid.compat.forest
  have hvalid₂ : TourValid vCap eCap s₂ :=
    { ordWithin := hord ▸ h.valid.ordWithin
      compat :=
        { nodup := hord ▸ h.valid.compat.nodup
          unique := hord ▸ h.valid.compat.unique
          forest := hF₂
          vert := fun v hv => hEq.1 ▸ h.valid.compat.vert v (hord ▸ hv)
          forestEnd := fun e he => by
            have he1 : e ∈ s₁.rf.F.E := hEq.2.1.symm ▸ he
            rw [← (hEq.2.2 e he1).1, ← (hEq.2.2 e he1).2, ← hord]
            exact h.valid.compat.forestEnd e he1 }
      roots_sub := hR ▸ hEq.1 ▸ h.valid.roots_sub
      verts_lt := fun v hv => h.valid.verts_lt v (hEq.1 ▸ hv)
      unique_root := fun v hv => by
        obtain ⟨r, ⟨hrR, hvr⟩, huniq⟩ := h.valid.unique_root v (hEq.1 ▸ hv)
        exact ⟨r, ⟨hR ▸ hrR, (connected_iff_of_graphEq hEq).mp hvr⟩,
          fun r' ⟨hr'R, hvr'⟩ => huniq r' ⟨hR ▸ hr'R, (connected_iff_of_graphEq hEq).mpr hvr'⟩⟩
      marked_open := fun z hz => by
        have hm := h.valid.marked_open z (hmk ▸ hz)
        exact ⟨hord ▸ hm.1, hEq.2.1 ▸ hm.2⟩ }
  have hft : ∀ r, fullTour s₂.ord s₂.rf.F hvalid₂.compat.forest r =
      fullTour s₁.ord s₁.rf.F h.valid.compat.forest r := fun r => by
    change fullTour s₂.ord s₂.rf.F hF₂ r = fullTour s₁.ord s₁.rf.F h.valid.compat.forest r
    rw [← hord]
    exact (fullTour_congr_graphEq s₁.ord h.valid.compat.forest hF₂ hEq r).symm
  have hrt : ∀ z, tourRootTagVal s₂ z = tourRootTagVal s₁ z := fun z => by
    unfold tourRootTagVal; simp only [hord, hR]
  exact
    { valid := hvalid₂
      ordRep := hord ▸ h.ordRep
      ordFootGe := h.ordFootGe
      header := h.header
      numNodes_le := h.numNodes_le
      nodeOf_mem := h.nodeOf_mem
      nodeOf_keyOf := h.nodeOf_keyOf
      keyOf_mem := h.keyOf_mem
      firstEnd_mem := fun v hv => hord ▸ h.firstEnd_mem v hv
      isRoot_mem := fun v hv => hR ▸ h.isRoot_mem v hv
      slot_bij := h.slot_bij
      slotOf_mem := h.slotOf_mem
      vertOf_mem := h.vertOf_mem
      active_end := fun v hv e he => h.active_end v hv e (hord ▸ he)
      inactive_owner := fun k hk hno => h.inactive_owner k hk (hord ▸ hno)
      markArr_zero := h.markArr_zero
      nodesAt := h.nodesAt
      forestInv := h.forestInv
      nodes_exact := h.nodes_exact
      comp_none := fun r hr hnil => h.comp_none r (hR ▸ hr) (hft r ▸ hnil)
      comp_some := fun r hr hne => by
        obtain ⟨t, h1, h2, h3⟩ := h.comp_some r (hR ▸ hr) (hft r ▸ hne)
        exact ⟨t, h1, h2, h3.trans (hft r).symm⟩
      tree_class := fun t ht => by
        rcases h.tree_class t ht with ⟨r, hr, hct⟩ | ⟨u, hu, hno⟩
        · exact Or.inl ⟨r, hR ▸ hr, hct⟩
        · exact Or.inr ⟨u, hu, hord ▸ hno⟩
      inactive_single := fun u h1 h2 hno => h.inactive_single u h1 h2 (hord ▸ hno)
      val_active := fun u h1 h2 hact => by
        have hv := h.val_active u h1 h2 (hord ▸ hact)
        rw [hv, hEq.2.1, hmk, hrt]
      val_inactive_rt := fun u h1 h2 hno => h.val_inactive_rt u h1 h2 (hord ▸ hno)
      val_unused_rt := h.val_unused_rt }

/-- `tourAsmRep` is invariant under `GraphEq` on `rf.F` with the same root set. -/
theorem tourAsmRep_congr_graphEq {vCap eCap tourH : ℕ} {a₁ a₂ : AsmTourAbs}
    {tx : (tourAsmRep vCap eCap).τ} {mem : ℕ → ℕ}
    (hord : a₁.ord = a₂.ord) (hmk : a₁.marked = a₂.marked)
    (hEq : GraphEq a₁.rf.F a₂.rf.F) (hR : a₁.rf.R = a₂.rf.R)
    (h : (tourAsmRep vCap eCap).rep tourH a₁ tx mem) :
    (tourAsmRep vCap eCap).rep tourH a₂ tx mem :=
  tourRepAt_congr_graphEq hord hmk hEq hR h

end

/-! ## 2. Tour mark-potential `tourMarkPot` and single-step lemmas -/

@[expose] public section

/-- Potential of the marked ends of a tour state `s : TourAbs` relative to the kept edges `keep`:
sums `splitPot (edgeEnds keep)` over the marked-end finsets at all roots `r ∈ s.rf.R`. -/
noncomputable def tourMarkPot (keep : Finset ℕ) (s : TourAbs) : ℕ :=
  ∑ r ∈ s.rf.R, splitPot (edgeEnds keep) (tourMarkedList s r).toFinset

/-- Tour-side mark invariant: `s.marked` consists of the open ends in `s.ord` whose edge lies in
`M` (matching `OutMarksOf ⟨coreTour s.ord s.rf, s.marked⟩ (coreTour s.ord s.rf) M`). -/
def TourMarksAt (s : TourAbs) (M : Finset ℕ) : Prop :=
  ∀ z : End, z ∈ s.marked ↔ (∃ v, z ∈ s.ord v) ∧ z.1 ∉ s.rf.F.E ∧ z.1 ∈ M

/-- `keep`-endpoint agreement between a tour state `s` and an output graph `S`: every edge `e ∈ keep`
has both ends open in `s`, and its root endpoint in `s` equals `S.src x`. -/
def TourKeepMatch (keep : Finset ℕ) (s : TourAbs) (S : MGraph) : Prop :=
  S.E = keep ∧
  ∀ x : End, x.1 ∈ keep → (∃ v, x ∈ s.ord v) ∧ x.1 ∉ s.rf.F.E ∧
    s.rf.root (ordSrc s.ord x) = S.src x

end

public section

theorem tourMarkedList_nodup {vCap eCap : ℕ} {s : TourAbs} (hv : TourValid vCap eCap s) (r : ℕ) :
    (tourMarkedList s r).Nodup := by
  classical
  unfold tourMarkedList
  by_cases hr : r ∈ s.rf.R
  · rw [← fullTour_filter_open s.ord hv.compat.forest hr]
    exact ((fullTour_spec hv.compat r).1.filter _).filter _
  · simp [coreTour, hr]

theorem mem_tourMarkedList_iff {vCap eCap : ℕ} {s : TourAbs} (hv : TourValid vCap eCap s)
    {M : Finset ℕ} (hM : TourMarksAt s M) (r : ℕ) (x : End) :
    x ∈ tourMarkedList s r ↔
      r ∈ s.rf.R ∧ (∃ v, x ∈ s.ord v) ∧ x.1 ∉ s.rf.F.E ∧ x.1 ∈ M ∧
        s.rf.root (ordSrc s.ord x) = r := by
  classical
  rw [tourMarkedList, List.mem_filter, decide_eq_true_eq, hM x]
  constructor
  · rintro ⟨hct, hact, hopen, hxM⟩
    obtain ⟨hrR, _, _, hroot⟩ := coreTour_mem_info hv hct
    exact ⟨hrR, hact, hopen, hxM, hroot⟩
  · rintro ⟨hrR, ⟨v, hxv⟩, hopen, hxM, hroot⟩
    refine ⟨?_, ⟨v, hxv⟩, hopen, hxM⟩
    rw [← fullTour_filter_open s.ord hv.compat.forest hrR, List.mem_filter]
    refine ⟨((fullTour_spec hv.compat r).2 x).mpr ⟨v, hxv, ?_⟩, by simpa using hopen⟩
    have hvV : v ∈ s.rf.F.V := hv.compat.vert v (List.ne_nil_of_mem hxv)
    rw [hv.compat.ordSrc_eq hxv] at hroot
    obtain ⟨r', ⟨hr'R, hvr'⟩, huniq⟩ := hv.unique_root v hvV
    have hreq : s.rf.root v = r' := hv.root_eq_of_mem hvV hr'R hvr'
    rw [← hroot, hreq]
    exact connected_symm hvr'

theorem tourMarksAt_iff_outMarksOf {vCap eCap : ℕ} {s : TourAbs} (hv : TourValid vCap eCap s)
    {M : Finset ℕ} :
    TourMarksAt s M ↔
      OutMarksOf ⟨coreTour s.ord s.rf, s.marked⟩ (coreTour s.ord s.rf) M := by
  refine ⟨fun h => ⟨rfl, fun z => ?_⟩, fun ⟨_, h⟩ z => ?_⟩
  · rw [h z]
    constructor
    · rintro ⟨⟨v, hzv⟩, hopen, hzM⟩
      have hvV : v ∈ s.rf.F.V := hv.compat.vert v (List.ne_nil_of_mem hzv)
      obtain ⟨r, ⟨hrR, hvr⟩, _⟩ := hv.unique_root v hvV
      refine ⟨⟨r, ?_⟩, hzM⟩
      rw [← fullTour_filter_open s.ord hv.compat.forest hrR, List.mem_filter]
      exact ⟨((fullTour_spec hv.compat r).2 z).mpr ⟨v, hzv, connected_symm hvr⟩, by simpa using hopen⟩
    · rintro ⟨⟨r, hct⟩, hzM⟩
      obtain ⟨_, hopen, hact, _⟩ := coreTour_mem_info hv hct
      exact ⟨hact, hopen, hzM⟩
  · rw [h z]
    constructor
    · rintro ⟨⟨r, hct⟩, hzM⟩
      obtain ⟨_, hopen, hact, _⟩ := coreTour_mem_info hv hct
      exact ⟨hact, hopen, hzM⟩
    · rintro ⟨⟨v, hzv⟩, hopen, hzM⟩
      have hvV : v ∈ s.rf.F.V := hv.compat.vert v (List.ne_nil_of_mem hzv)
      obtain ⟨r, ⟨hrR, hvr⟩, _⟩ := hv.unique_root v hvV
      refine ⟨⟨r, ?_⟩, hzM⟩
      rw [← fullTour_filter_open s.ord hv.compat.forest hrR, List.mem_filter]
      exact ⟨((fullTour_spec hv.compat r).2 z).mpr ⟨v, hzv, connected_symm hvr⟩, by simpa using hopen⟩

/-- At the initial state matching `(G, L, ρ)`, `tourMarkPot keep s` equals `markPot keep M (coreGraph G L)`. -/
theorem tourMarkPot_eq_markPot {vCap eCap : ℕ} {G : MGraph} {L : LSF} (ρ : Rotation G)
    (hG : G.IsValid) (hF : L.F.IsRootedSpanningForestOf G)
    {s : TourAbs} (hv : TourValid vCap eCap s)
    (hord : s.ord = ρ.order) (hrf : s.rf = L.F) {keep M : Finset ℕ}
    (hMarks : TourMarksAt s M) (hM : M ⊆ (coreGraph G L).E) :
    tourMarkPot keep s = markPot keep M (coreGraph G L) := by
  have hcore : coreTour s.ord s.rf = (coreRotation (L := L) ρ hG hF).order := by
    funext r
    rw [hord, hrf, coreTour_eq_coreRotation ρ hG hF r]
  have hOM : OutMarksOf ⟨(coreRotation (L := L) ρ hG hF).order, s.marked⟩
      (coreRotation (L := L) ρ hG hF).order M := by
    have h1 := (tourMarksAt_iff_outMarksOf hv).mp hMarks
    rw [hcore] at h1
    exact ⟨rfl, h1.2⟩
  unfold tourMarkPot markPot
  rw [hrf]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hml : tourMarkedList s r =
      OutTourAbs.markedList ⟨(coreRotation (L := L) ρ hG hF).order, s.marked⟩ r := by
    simp only [tourMarkedList, OutTourAbs.markedList, hcore]
  rw [hml]
  have heq := (outMarksOf_markedList_eq_markBlock ρ hG hF
    (s := ⟨(coreRotation (L := L) ρ hG hF).order, s.marked⟩) hOM hM r).2
  rw [heq]

/-- Two-end insertion (`[.insertBefore a (e, true) y₁, .insertBefore b (e, false) y₂]`) with
`e ∉ M` preserves `TourMarksAt`, `TourKeepMatch`, and `tourMarkPot`. -/
theorem tourMarkPot_insert {vCap eCap e a b : ℕ} {y₁ y₂ : Option End}
    {s : TourAbs} {keep M : Finset ℕ} {S : MGraph}
    (hv : TourValid vCap eCap s)
    (hv' : TourValid vCap eCap (tourApplyEdits s [.insertBefore a (e, true) y₁, .insertBefore b (e, false) y₂]))
    (hM : TourMarksAt s M) (hK : TourKeepMatch keep s S) (heM : e ∉ M) (hek : e ∉ keep) :
    let s' := tourApplyEdits s [.insertBefore a (e, true) y₁, .insertBefore b (e, false) y₂]
    TourMarksAt s' M ∧ TourKeepMatch keep s' S ∧ tourMarkPot keep s' = tourMarkPot keep s := by
  intro s'
  have hrf : s'.rf = s.rf := rfl
  have hmk : s'.marked = s.marked := rfl
  have hmem_ins : ∀ (ord0 : ℕ → List End) (v : ℕ) (x : End) (y : Option End) (u : ℕ) (z : End),
      z.1 ≠ x.1 → (z ∈ applyOrdEdit ord0 (.insertBefore v x y) u ↔ z ∈ ord0 u) := by
    intro ord0 v x y u z hne
    simp only [applyOrdEdit]
    by_cases huv : u = v
    · subst huv
      simp only [Function.update_self]
      have hzx : z ≠ x := fun h => hne (congrArg Prod.fst h)
      have hmem_ib : ∀ (l : List End), z ∈ insertBeforeList x y l ↔ z = x ∨ z ∈ l := by
        cases y with
        | none => intro l; simp [insertBeforeList, or_comm]
        | some y0 =>
          intro l
          simp only [insertBeforeList, List.mem_append, List.mem_cons]
          have hsplit : z ∈ l ↔ z ∈ l.take (l.idxOf y0) ∨ z ∈ l.drop (l.idxOf y0) := by
            conv_lhs => rw [← List.take_append_drop (l.idxOf y0) l]
            exact List.mem_append
          tauto
      rw [hmem_ib (ord0 u)]
      exact ⟨fun h => h.resolve_left hzx, Or.inr⟩
    · simp [Function.update_of_ne huv]
  have hord_iff : ∀ u (z : End), z.1 ≠ e → (z ∈ s'.ord u ↔ z ∈ s.ord u) := by
    intro u z hne
    change z ∈ applyOrdEdit (applyOrdEdit s.ord (.insertBefore a (e, true) y₁))
      (.insertBefore b (e, false) y₂) u ↔ z ∈ s.ord u
    rw [hmem_ins _ b (e, false) y₂ u z hne, hmem_ins _ a (e, true) y₁ u z hne]
  have hM' : TourMarksAt s' M := by
    intro z
    rw [hmk, hM z, hrf]
    by_cases hze : z.1 = e
    · have : z.1 ∉ M := hze ▸ heM
      simp [this]
    · constructor
      · rintro ⟨⟨u, hu⟩, h1, h2⟩; exact ⟨⟨u, (hord_iff u z hze).mpr hu⟩, h1, h2⟩
      · rintro ⟨⟨u, hu⟩, h1, h2⟩; exact ⟨⟨u, (hord_iff u z hze).mp hu⟩, h1, h2⟩
  have hK' : TourKeepMatch keep s' S := by
    refine ⟨hK.1, fun z hz => ?_⟩
    have hze : z.1 ≠ e := fun h => hek (h ▸ hz)
    obtain ⟨⟨u, hu⟩, hopen, hrt⟩ := hK.2 z hz
    have hu' : z ∈ s'.ord u := (hord_iff u z hze).mpr hu
    refine ⟨⟨u, hu'⟩, hrf ▸ hopen, ?_⟩
    rw [hrf, hv'.compat.ordSrc_eq hu', ← hv.compat.ordSrc_eq hu]
    exact hrt
  have hml : ∀ r, (tourMarkedList s' r).toFinset = (tourMarkedList s r).toFinset := by
    intro r; ext z
    rw [List.mem_toFinset, List.mem_toFinset, mem_tourMarkedList_iff hv' hM',
      mem_tourMarkedList_iff hv hM, hrf]
    by_cases hze : z.1 = e
    · have : z.1 ∉ M := hze ▸ heM
      simp [this]
    · constructor
      · rintro ⟨hrR, ⟨u, hu'⟩, hopen, hzM, hrt⟩
        have hu : z ∈ s.ord u := (hord_iff u z hze).mp hu'
        rw [hv'.compat.ordSrc_eq hu'] at hrt
        exact ⟨hrR, ⟨u, hu⟩, hopen, hzM, by rw [hv.compat.ordSrc_eq hu]; exact hrt⟩
      · rintro ⟨hrR, ⟨u, hu⟩, hopen, hzM, hrt⟩
        have hu' : z ∈ s'.ord u := (hord_iff u z hze).mpr hu
        rw [hv.compat.ordSrc_eq hu] at hrt
        exact ⟨hrR, ⟨u, hu'⟩, hopen, hzM, by rw [hv'.compat.ordSrc_eq hu']; exact hrt⟩
  refine ⟨hM', hK', ?_⟩
  unfold tourMarkPot
  rw [hrf]
  exact Finset.sum_congr rfl fun r _ => by rw [hml r]

/-- Dropping a non-forest edge `[.dropEdge e]` (`e ∉ keep`) updates `M ↦ M.erase e`, preserves
`TourKeepMatch`, and never increases `tourMarkPot`. -/
theorem tourMarkPot_dropEdge {vCap eCap e : ℕ} {s : TourAbs} {keep M : Finset ℕ} {S : MGraph}
    (hv : TourValid vCap eCap s)
    (hv' : TourValid vCap eCap (tourApplyEdits s [.dropEdge e]))
    (hM : TourMarksAt s M) (hK : TourKeepMatch keep s S) (hek : e ∉ keep) :
    let s' := tourApplyEdits s [.dropEdge e]
    TourMarksAt s' (M.erase e) ∧ TourKeepMatch keep s' S ∧ tourMarkPot keep s' ≤ tourMarkPot keep s := by
  intro s'
  have hrf : s'.rf = s.rf := rfl
  have hord_iff : ∀ u (z : End), z ∈ s'.ord u ↔ z ∈ s.ord u ∧ z.1 ≠ e := by
    intro u z
    change z ∈ (s.ord u).filter (fun x => x.1 != e) ↔ _
    simp
  have hM' : TourMarksAt s' (M.erase e) := by
    intro z
    change z ∈ s.marked.filter (fun x => x.1 != e) ↔ _
    simp only [Finset.mem_filter, bne_iff_ne, hM z, hrf, Finset.mem_erase]
    constructor
    · rintro ⟨⟨⟨u, hu⟩, hopen, hzM⟩, hne⟩
      exact ⟨⟨u, (hord_iff u z).mpr ⟨hu, hne⟩⟩, hopen, hne, hzM⟩
    · rintro ⟨⟨u, hu⟩, hopen, hne, hzM⟩
      exact ⟨⟨⟨u, ((hord_iff u z).mp hu).1⟩, hopen, hzM⟩, hne⟩
  have hK' : TourKeepMatch keep s' S := by
    refine ⟨hK.1, fun z hz => ?_⟩
    have hze : z.1 ≠ e := fun h => hek (h ▸ hz)
    obtain ⟨⟨u, hu⟩, hopen, hrt⟩ := hK.2 z hz
    have hu' : z ∈ s'.ord u := (hord_iff u z).mpr ⟨hu, hze⟩
    refine ⟨⟨u, hu'⟩, hrf ▸ hopen, ?_⟩
    rw [hrf, hv'.compat.ordSrc_eq hu', ← hv.compat.ordSrc_eq hu]
    exact hrt
  refine ⟨hM', hK', ?_⟩
  unfold tourMarkPot
  rw [hrf]
  refine Finset.sum_le_sum fun r _ => splitPot_mono _ fun z hz => ?_
  rw [List.mem_toFinset, mem_tourMarkedList_iff hv' hM'] at hz
  rw [List.mem_toFinset, mem_tourMarkedList_iff hv hM]
  obtain ⟨hrR, ⟨u, hu'⟩, hopen, hzM, hrt⟩ := hz
  have hu := ((hord_iff u z).mp hu').1
  rw [hrf, hv'.compat.ordSrc_eq hu'] at hrt
  exact ⟨hrR, ⟨u, hu⟩, hrf ▸ hopen, Finset.mem_of_mem_erase hzM, by rw [hv.compat.ordSrc_eq hu]; exact hrt⟩

/-- Trailing `rotateTo` edits preserve `TourMarksAt`, `TourKeepMatch`, and `tourMarkPot`. -/
theorem tourMarkPot_rotate {vCap eCap : ℕ} {eds : List OrdEdit} {s : TourAbs}
    {keep M : Finset ℕ} {S : MGraph}
    (hrot : ∀ d ∈ eds, d.IsRotate)
    (hv : TourValid vCap eCap s)
    (hv' : TourValid vCap eCap (tourApplyEdits s eds))
    (hM : TourMarksAt s M) (hK : TourKeepMatch keep s S) :
    let s' := tourApplyEdits s eds
    TourMarksAt s' M ∧ TourKeepMatch keep s' S ∧ tourMarkPot keep s' = tourMarkPot keep s := by
  have hstep : ∀ (l : List OrdEdit) (s0 : TourAbs), (∀ d ∈ l, d.IsRotate) →
      (tourApplyEdits s0 l).rf = s0.rf ∧ (tourApplyEdits s0 l).marked = s0.marked ∧
      (∀ u z, z ∈ (tourApplyEdits s0 l).ord u ↔ z ∈ s0.ord u) := by
    intro l
    induction l with
    | nil => intro s0 _; exact ⟨rfl, rfl, fun _ _ => Iff.rfl⟩
    | cons d ds ih =>
      intro s0 hd
      have hd0 : d.IsRotate := hd d List.mem_cons_self
      cases d with
      | rotateTo v y =>
        obtain ⟨hrf1, hmk1, hord1⟩ := ih (tourApplyEdit s0 (.rotateTo v y))
          (fun d' hd' => hd d' (List.mem_cons_of_mem _ hd'))
        refine ⟨hrf1, hmk1, fun u z => (hord1 u z).trans ?_⟩
        change z ∈ Function.update s0.ord v (rotateToList y (s0.ord v)) u ↔ z ∈ s0.ord u
        by_cases huv : u = v
        · subst huv; simp only [Function.update_self]; exact (rotateToList_isRotated (y := y) (xs := s0.ord u)).symm.perm.mem_iff
        · simp [Function.update_of_ne huv]
      | dropEdge _ | moveEnds _ _ _ _ | insertBefore _ _ _ => simp [OrdEdit.IsRotate] at hd0
  obtain ⟨hrf, hmk, hord⟩ := hstep eds s hrot
  intro s'
  have hM' : TourMarksAt s' M := fun z => by
    rw [hmk, hM z, hrf]
    exact ⟨fun ⟨⟨u, hu⟩, h1, h2⟩ => ⟨⟨u, (hord u z).mpr hu⟩, h1, h2⟩,
      fun ⟨⟨u, hu⟩, h1, h2⟩ => ⟨⟨u, (hord u z).mp hu⟩, h1, h2⟩⟩
  have hK' : TourKeepMatch keep s' S := by
    refine ⟨hK.1, fun z hz => ?_⟩
    obtain ⟨⟨u, hu⟩, hopen, hrt⟩ := hK.2 z hz
    have hu' : z ∈ s'.ord u := (hord u z).mpr hu
    refine ⟨⟨u, hu'⟩, hrf ▸ hopen, ?_⟩
    rw [hrf, hv'.compat.ordSrc_eq hu', ← hv.compat.ordSrc_eq hu]
    exact hrt
  refine ⟨hM', hK', ?_⟩
  unfold tourMarkPot
  rw [hrf]
  refine Finset.sum_congr rfl fun r _ => congrArg (splitPot (edgeEnds keep)) ?_
  ext z
  rw [List.mem_toFinset, List.mem_toFinset, mem_tourMarkedList_iff hv' hM',
    mem_tourMarkedList_iff hv hM, hrf]
  constructor
  · rintro ⟨hrR, ⟨u, hu'⟩, hopen, hzM, hrt⟩
    have hu : z ∈ s.ord u := (hord u z).mp hu'
    rw [hv'.compat.ordSrc_eq hu'] at hrt
    exact ⟨hrR, ⟨u, hu⟩, hopen, hzM, by rw [hv.compat.ordSrc_eq hu]; exact hrt⟩
  · rintro ⟨hrR, ⟨u, hu⟩, hopen, hzM, hrt⟩
    have hu' : z ∈ s'.ord u := (hord u z).mpr hu
    rw [hv.compat.ordSrc_eq hu] at hrt
    exact ⟨hrR, ⟨u, hu'⟩, hopen, hzM, by rw [hv'.compat.ordSrc_eq hu']; exact hrt⟩

/-- **Unified split-step potential & `OutSplitListsAt` lemma.**
Whenever a tour transition `s ↦ s'` refines root `kept ∈ s.rf.R` into `{kept, fresh}`
(`fresh ∉ s.rf.R`, `s'.rf.R = insert fresh s.rf.R`), leaves all other roots' marked blocks unchanged,
and splits `kept`'s marked block into `(tourMarkedList s' kept, tourMarkedList s' fresh)` while
matching `S' = S.applyUpdate (.split kept fresh StK ShK)` on `keep ⊆ M ⊆ E₀`, the smaller marked
list `Y` returned by `outSmallSide` satisfies:
1. `Y.Nodup`, `∀ x ∈ Y, x.1 ∈ E₀`, and `∀ x, x.1 ∈ keep → (x ∈ Y ↔ S'.src x = chosenRoot)`;
2. `Y.length + tourMarkPot keep s' ≤ min (S'.deg kept) (S'.deg fresh) + tourMarkPot keep s`. -/
theorem tourMarkPot_split_step {vCap eCap kept fresh : ℕ} {s s' : TourAbs}
    {keep M E₀ : Finset ℕ} {S' : MGraph}
    (hv' : TourValid vCap eCap s')
    (hM' : TourMarksAt s' M)
    (hkM : keep ⊆ M) (hME₀ : M ⊆ E₀)
    (hK' : TourKeepMatch keep s' S')
    (hkept : kept ∈ s.rf.R) (hfresh : fresh ∉ s.rf.R) (hR' : s'.rf.R = insert fresh s.rf.R)
    (hother : ∀ r ∈ s.rf.R, r ≠ kept →
      (tourMarkedList s' r).toFinset = (tourMarkedList s r).toFinset)
    (hunion : (tourMarkedList s' kept).toFinset ∪ (tourMarkedList s' fresh).toFinset =
      (tourMarkedList s kept).toFinset) :
    let side := if (tourMarkedList s' kept).length ≤ (tourMarkedList s' fresh).length then 0 else 1
    let Y := tourMarkedList s' (if side = 0 then kept else fresh)
    Y.Nodup ∧
    (∀ x ∈ Y, x.1 ∈ E₀) ∧
    (∀ x : End, x.1 ∈ keep → (x ∈ Y ↔ S'.src x = if side = 0 then kept else fresh)) ∧
    Y.length + tourMarkPot keep s' ≤
      min (S'.deg kept) (S'.deg fresh) + tourMarkPot keep s := by
  intro side Y
  have hne : kept ≠ fresh := fun h => hfresh (h ▸ hkept)
  have hkept' : kept ∈ s'.rf.R := hR' ▸ Finset.mem_insert_of_mem hkept
  have hfresh' : fresh ∈ s'.rf.R := hR' ▸ Finset.mem_insert_self _ _
  have hndK := tourMarkedList_nodup hv' kept
  have hndF := tourMarkedList_nodup hv' fresh
  have hdisj : Disjoint (tourMarkedList s' kept).toFinset (tourMarkedList s' fresh).toFinset := by
    refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
    rw [List.mem_toFinset, mem_tourMarkedList_iff hv' hM'] at h1 h2
    exact hne (h1.2.2.2.2.symm.trans h2.2.2.2.2)
  have hndY : Y.Nodup := by
    dsimp only [Y]; split_ifs <;> assumption
  have hY_E₀ : ∀ x ∈ Y, x.1 ∈ E₀ := by
    intro x hx
    dsimp only [Y] at hx
    have hmem := (mem_tourMarkedList_iff hv' hM' _ x).mp hx
    exact hME₀ hmem.2.2.2.1
  have hY_keep : ∀ x : End, x.1 ∈ keep → (x ∈ Y ↔ S'.src x = if side = 0 then kept else fresh) := by
    intro x hx
    set r := if side = 0 then kept else fresh
    have hrR : r ∈ s'.rf.R := by dsimp only [r]; split_ifs <;> assumption
    obtain ⟨hact, hopen, hrt⟩ := hK'.2 x hx
    rw [show x ∈ Y ↔ x ∈ tourMarkedList s' r from Iff.rfl, mem_tourMarkedList_iff hv' hM']
    exact ⟨fun ⟨_, _, _, _, hr⟩ => hrt.symm.trans hr,
      fun hs => ⟨hrR, hact, hopen, hkM hx, hrt.trans hs⟩⟩
  have hdeg_eq : ∀ r ∈ s'.rf.R,
      ((tourMarkedList s' r).toFinset ∩ edgeEnds keep).card = S'.deg r := by
    intro r hrR
    have hset : (tourMarkedList s' r).toFinset ∩ edgeEnds keep =
        (edgeEnds keep).filter (fun x => S'.src x = r) := by
      ext x
      simp only [Finset.mem_inter, List.mem_toFinset, mem_edgeEnds, Finset.mem_filter,
        mem_tourMarkedList_iff hv' hM']
      constructor
      · rintro ⟨⟨_, _, _, _, hr⟩, hxk⟩
        exact ⟨hxk, (hK'.2 x hxk).2.2.symm.trans hr⟩
      · rintro ⟨hxk, hs⟩
        obtain ⟨hact, hopen, hrt⟩ := hK'.2 x hxk
        exact ⟨⟨hrR, hact, hopen, hkM hxk, hrt.trans hs⟩, hxk⟩
    rw [hset, card_edgeEnds_filter_src, MGraph.deg, hK'.1]
  have hpot := splitPot_sum_split (edgeEnds keep) s.rf.R
    (fun r => (tourMarkedList s r).toFinset)
    (fun r => (tourMarkedList s' r).toFinset) hkept hfresh hother hunion hdisj
  rw [card_splitPick, hdeg_eq kept hkept', hdeg_eq fresh hfresh'] at hpot
  have hlenY : Y.length =
      min (tourMarkedList s' kept).toFinset.card (tourMarkedList s' fresh).toFinset.card := by
    rw [List.toFinset_card_of_nodup hndK, List.toFinset_card_of_nodup hndF]
    by_cases hle : (tourMarkedList s' kept).length ≤ (tourMarkedList s' fresh).length
    · have hside : side = 0 := ite_eq_left hle
      have hY : Y = tourMarkedList s' kept := by dsimp only [Y]; simp [hside]
      rw [hY, min_eq_left hle]
    · have hside : side = 1 := ite_eq_right hle
      have hY : Y = tourMarkedList s' fresh := by dsimp only [Y]; simp [hside]
      rw [hY, min_eq_right (by omega)]
  refine ⟨hndY, hY_E₀, hY_keep, ?_⟩
  unfold tourMarkPot
  rw [hR', hlenY]
  exact hpot

end

/-! ## 3. Canonical split-list length, bounds, and release-prefix lemmas -/

public section

/-- Leading prefix of `isRelease = true` entries followed by the remaining suffix (which is either
empty or starts with an `isRelease = false` entry). -/
def splitLeadingReleases :
    List CompSplitEntry → List CompSplitEntry × List CompSplitEntry
  | [] => ([], [])
  | e :: rest =>
    if e.isRelease then
      let p := splitLeadingReleases rest
      (e :: p.1, p.2)
    else ([], e :: rest)

theorem splitLeadingReleases_append (L : List CompSplitEntry) :
    (splitLeadingReleases L).1 ++ (splitLeadingReleases L).2 = L := by
  induction L with
  | nil => rfl
  | cons e rest ih =>
    unfold splitLeadingReleases
    split_ifs
    · simp only [List.cons_append, ih]
    · rfl

theorem splitLeadingReleases_fst_true (L : List CompSplitEntry) :
    ∀ e ∈ (splitLeadingReleases L).1, e.isRelease = true := by
  induction L with
  | nil => intro _ h; cases h
  | cons e rest ih =>
    unfold splitLeadingReleases
    split_ifs with hr
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hrest
      · exact hr
      · exact ih x hrest
    · intro _ h; cases h

theorem splitLeadingReleases_snd_head (L : List CompSplitEntry) :
    ∀ e rest, (splitLeadingReleases L).2 = e :: rest → e.isRelease = false := by
  induction L with
  | nil => intro _ _ h; cases h
  | cons a as ih =>
    intro e rest h
    unfold splitLeadingReleases at h
    split_ifs at h with hr
    · exact ih e rest h
    · cases h; simpa using hr

theorem splitLeadingReleases_of_all_true {L₁ L₂ : List CompSplitEntry}
    (h1 : ∀ e ∈ L₁, e.isRelease = true) :
    splitLeadingReleases (L₁ ++ L₂) =
      (L₁ ++ (splitLeadingReleases L₂).1, (splitLeadingReleases L₂).2) := by
  induction L₁ with
  | nil => simp
  | cons a as ih =>
    have ha : a.isRelease = true := h1 a List.mem_cons_self
    have has : ∀ e ∈ as, e.isRelease = true := fun e he => h1 e (List.mem_cons_of_mem _ he)
    simp only [List.cons_append, splitLeadingReleases, ha, ↓reduceIte, ih has]

theorem asmFirstReleasesSplitEntries_all_true (final : Finset ℕ) (L : LSF) (cuts : List ℕ) :
    ∀ e ∈ releasesSplitEntries final L cuts, e.isRelease = true := by
  induction cuts generalizing L with
  | nil => intro _ h; cases h
  | cons c cs ih =>
    intro e he
    simp only [releasesSplitEntries, List.mem_cons] at he
    rcases he with rfl | hrest
    · rfl
    · exact ih _ e hrest

theorem asmFirstReleasesSplitEntries_length (final : Finset ℕ) (L : LSF) (cuts : List ℕ) :
    (releasesSplitEntries final L cuts).length = cuts.length := by
  induction cuts generalizing L with
  | nil => rfl
  | cons c cs ih => simp [releasesSplitEntries, ih]

private lemma batchSplitCount_releasesBatch (G : MGraph) (final : Finset ℕ) (L : LSF)
    (cuts : List ℕ) :
    batchSplitCount (releasesBatch G final L cuts) = cuts.length := by
  induction cuts generalizing L with
  | nil => rfl
  | cons c cs ih =>
    simp only [releasesBatch, batchSplitCount, List.countP_cons, refineSplit, isSplit,
      ↓reduceIte, Bool.false_eq_true, List.length_cons]
    have := ih ⟨L.T, ⟨eraseForestEdge L.F.F c, canonRoots (eraseForestEdge L.F.F c) L.F.R final⟩, L.wstr⟩
    unfold batchSplitCount at this
    omega

private lemma batchSplitCount_inputCoreBatch (cs : CompLSFState) (u : Update) :
    batchSplitCount (inputCoreBatch cs u) = (inputSplitEntries cs u).length := by
  cases u with
  | insert _ _ _ => rfl
  | delete e => by_cases h : e ∈ cs.RF.F.E <;> simp [inputCoreBatch, inputSplitEntries, batchSplitCount, refineSplit, isSplit, h]
  | split _ _ _ _ => simp [inputCoreBatch, inputSplitEntries, batchSplitCount, refineSplit, isSplit]

/-- The number of entries in `canonSplitList cs U` equals `batchSplitCount (canonCoreBatch cs U)`. -/
theorem asmFirstCanonSplitList_length_eq_batchSplitCount (cs : CompLSFState) (U : List Update) :
    (canonSplitList cs U).length = batchSplitCount (canonCoreBatch cs U) := by
  induction U generalizing cs with
  | nil => rfl
  | cons u rest ih =>
    simp only [canonSplitList, canonStepSplits, canonCoreBatch, canonStepCore,
      List.length_append, batchSplitCount, List.countP_append]
    have h1 := batchSplitCount_inputCoreBatch cs u
    have h2 := batchSplitCount_releasesBatch (cs.G.applyUpdate u) (compLSFStepSingle cs u).RF.R
      (inputMid cs u) (((forestAfterInput cs.RF.F u).E \ (compLSFStepSingle cs u).RF.F.E).sort (· ≤ ·))
    have h3 := asmFirstReleasesSplitEntries_length (compLSFStepSingle cs u).RF.R (inputMid cs u)
      (((forestAfterInput cs.RF.F u).E \ (compLSFStepSingle cs u).RF.F.E).sort (· ≤ ·))
    have h4 := ih (compLSFStepSingle cs u)
    unfold batchSplitCount at h1 h2 h4
    omega

/-- Every split in `restrictSplits keep UC` contributes at least `1` to `S.batchEnc`. -/
theorem restrictSplits_length_le_batchEnc (keep : Finset ℕ) :
    ∀ (UC : List Update) (S : MGraph),
      batchSplitCount UC ≤ S.batchEnc (restrictSplits keep UC)
  | [], _ => Nat.zero_le _
  | .insert _ _ _ :: UC, S => by
    simpa [batchSplitCount, isSplit, restrictSplits] using restrictSplits_length_le_batchEnc keep UC S
  | .delete _ :: UC, S => by
    simpa [batchSplitCount, isSplit, restrictSplits] using restrictSplits_length_le_batchEnc keep UC S
  | .split v v' St Sh :: UC, S => by
    simp only [batchSplitCount, List.countP_cons, isSplit, ↓reduceIte, restrictSplits, MGraph.batchEnc,
      MGraph.updateEnc]
    have ih := restrictSplits_length_le_batchEnc keep UC (S.applyUpdate (.split v v' (St ∩ keep) (Sh ∩ keep)))
    unfold batchSplitCount at ih
    omega

/-- The total number of canonical splits of a step is bounded by `tr.S_cur.batchEnc info.U_S`. -/
theorem asmFirstCanonSplitList_length_le_batchEnc {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    (canonSplitList tr.cs U).length ≤
      tr.S_cur.batchEnc (stepBundleTree sparsify tr U ord ord').U_S := by
  rw [asmFirstCanonSplitList_length_eq_batchSplitCount]
  have hBE : tr.S_cur.batchEnc (stepBundleTree sparsify tr U ord ord').U_S =
      (outDelList sparsify tr U ord ord').length +
        (tr.S_cur.applyBatch ((outDelList sparsify tr U ord ord').map Update.delete)).batchEnc
          (restrictSplits (outKeep sparsify tr U ord ord') (canonCoreBatch tr.cs U)) +
        (tr.S_cur.applyBatch ((outDelList sparsify tr U ord ord').map Update.delete ++
          outSplitBatch sparsify tr U ord ord')).batchEnc
          (outInsBatch sparsify tr U ord ord') := by
    rw [outStep_batch_eq, outBatchEnc_append, outBatchEnc_append, batchEnc_dels]
    rfl
  have h1 := restrictSplits_length_le_batchEnc (outKeep sparsify tr U ord ord') (canonCoreBatch tr.cs U)
    (tr.S_cur.applyBatch ((outDelList sparsify tr U ord ord').map Update.delete))
  omega

/-- The total number of canonical splits is also bounded by `vCap` when final roots lie below `vCap`. -/
theorem asmFirstCanonSplitList_length_le_vCap {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {vCap : ℕ}
    {cs : CompLSFState} {U : List Update} {ord ord' : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hBU : cs.G.BatchIsValid U)
    (hOB : OrderedBatch cs.G U ord ord')
    (hR_lt : ∀ v ∈ (compLSFBatch cs U).RF.R, v < vCap) :
    (canonSplitList cs U).length ≤ vCap := by
  obtain ⟨ρ, σ, _, _, hrot⟩ := hOB
  obtain ⟨_, _, _, hsc, _, _⟩ :=
    orderedCore_canonCoreBatch (C_lsst := C_lsst) (ℓ₀ := ℓ₀) hrot (Nat.le_refl 2) hBU cs rfl hI
  rw [asmFirstCanonSplitList_length_eq_batchSplitCount, hsc]
  have hsub : (compLSFBatch cs U).RF.R \ cs.RF.R ⊆ Finset.range vCap := fun v hv =>
    Finset.mem_range.mpr (hR_lt v (Finset.mem_sdiff.mp hv).1)
  exact (Finset.card_le_card hsub).trans (by rw [Finset.card_range])

end

end MinCostFlow.SparseCore.Program
