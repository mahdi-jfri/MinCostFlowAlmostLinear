module

public import MinCostFlow.SparseCore.Program.TourRep
public import MinCostFlow.SparseCore.GraphHelpers
import Mathlib.Tactic

/-!
# Graph-Equivalence Invariance of `TourRepAt` and `initTourForest` (`TourGraphEq`)

Shows that `fullTour`, `TourValid`, and `TourRepAt` depend on the forest `s.rf.F` only up to
`GraphEq` (`V`, `E`, and `tail`/`head` on `E`), and proves that `initTourForest` built from an
`OrdListAt` of a rotation of `G`, the forest-edge list of a rooted spanning forest `rf`, and the
root list of `rf` is `GraphEq` to `rf.F` with the same root set `rf.R`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore

/-! ## `GraphEq` invariance of walks, forests, and `fullTour` -/

theorem src_eq_of_graphEq {F₁ F₂ : MGraph} (hG : GraphEq F₁ F₂) {x : End} (hx : x.1 ∈ F₁.E) :
    F₁.src x = F₂.src x := by
  obtain ⟨e, b⟩ := x
  cases b
  · exact (hG.2.2 e hx).2
  · exact (hG.2.2 e hx).1

theorem dst_eq_of_graphEq {F₁ F₂ : MGraph} (hG : GraphEq F₁ F₂) {x : End} (hx : x.1 ∈ F₁.E) :
    F₁.dst x = F₂.dst x := by
  obtain ⟨e, b⟩ := x
  cases b
  · exact (hG.2.2 e hx).1
  · exact (hG.2.2 e hx).2

theorem isWalk_of_graphEq {F₁ F₂ : MGraph} (hG : GraphEq F₁ F₂) {u v : ℕ} {P : List End}
    (h : F₁.IsWalk u v P) : F₂.IsWalk u v P := by
  induction h with
  | nil u => exact .nil u
  | cons he hsrc _ ih =>
    have he₂ : _ ∈ F₂.E := hG.2.1 ▸ he
    have hsrc₂ : F₂.src _ = _ := (src_eq_of_graphEq hG he).symm.trans hsrc
    have hdst : F₁.dst _ = F₂.dst _ := dst_eq_of_graphEq hG he
    exact .cons he₂ hsrc₂ (hdst ▸ ih)

theorem connected_iff_of_graphEq {F₁ F₂ : MGraph} (hG : GraphEq F₁ F₂) (u v : ℕ) :
    F₁.Connected u v ↔ F₂.Connected u v :=
  ⟨fun ⟨P, hP⟩ => ⟨P, isWalk_of_graphEq hG hP⟩,
   fun ⟨P, hP⟩ => ⟨P, isWalk_of_graphEq (graphEq_symm hG) hP⟩⟩

theorem isValid_of_graphEq {F₁ F₂ : MGraph} (hG : GraphEq F₁ F₂) (h : F₁.IsValid) : F₂.IsValid := by
  intro e he₂
  have he₁ : e ∈ F₁.E := hG.2.1.symm ▸ he₂
  obtain ⟨ht, hh⟩ := h e he₁
  obtain ⟨hte, hhe⟩ := hG.2.2 e he₁
  exact ⟨hG.1 ▸ hte ▸ ht, hG.1 ▸ hhe ▸ hh⟩

theorem isForest_of_graphEq {F₁ F₂ : MGraph} (hG : GraphEq F₁ F₂) (h : F₁.IsForest) :
    F₂.IsForest := by
  refine ⟨isValid_of_graphEq hG h.1, fun P ⟨hne, hnd, u, hW⟩ => ?_⟩
  exact h.2 P ⟨hne, hnd, u, isWalk_of_graphEq (graphEq_symm hG) hW⟩

theorem compOf_of_graphEq {F₁ F₂ : MGraph} (hG : GraphEq F₁ F₂) (u : ℕ) :
    compOf F₁ u = compOf F₂ u := by
  ext v
  simp only [mem_compOf_iff, hG.1, connected_iff_of_graphEq hG]

theorem eraseForestEdge_graphEq {F₁ F₂ : MGraph} (hG : GraphEq F₁ F₂) (e : ℕ) :
    GraphEq (eraseForestEdge F₁ e) (eraseForestEdge F₂ e) := by
  refine ⟨hG.1, ?_, fun f hf => hG.2.2 f (Finset.mem_erase.mp hf).2⟩
  simp [hG.2.1]

theorem fullTourBlocks_of_graphEq {ord : ℕ → List End} {F₀₁ F₀₂ F₁ F₂ : MGraph}
    (hG₀ : GraphEq F₀₁ F₀₂) (hG : GraphEq F₁ F₂) (hF₁ : F₁.IsForest) (hF₂ : F₂.IsForest)
    (v : ℕ) (xs : List End) :
    fullTourBlocks ord F₀₁ F₁ hF₁ v xs = fullTourBlocks ord F₀₂ F₂ hF₂ v xs := by
  rw [fullTourBlocks.eq_def ord F₀₁ F₁, fullTourBlocks.eq_def ord F₀₂ F₂]
  apply List.flatMap_congr
  intro x _
  by_cases hopen : x.1 ∉ F₀₁.E
  · have hopen₂ : x.1 ∉ F₀₂.E := hG₀.2.1 ▸ hopen
    simp [hopen, hopen₂]
  · have hopen₂ : ¬ x.1 ∉ F₀₂.E := hG₀.2.1 ▸ hopen
    by_cases ha : x.1 ∈ F₁.E ∧ F₁.src x = v
    · have ha₂ : x.1 ∈ F₂.E ∧ F₂.src x = v :=
        ⟨hG.2.1 ▸ ha.1, (src_eq_of_graphEq hG ha.1).symm.trans ha.2⟩
      have hdst : F₁.dst x = F₂.dst x := dst_eq_of_graphEq hG ha.1
      simp only [hopen, hopen₂, ↓reduceIte]
      rw [dite_eq_left_iff.mpr (fun h => absurd ha h), dite_eq_left_iff.mpr (fun h => absurd ha₂ h)]
      rw [← hdst]
      congr 2
      exact fullTourBlocks_of_graphEq hG₀ (eraseForestEdge_graphEq hG x.1)
        (isForest_eraseEdge hF₁ x.1) (isForest_eraseEdge hF₂ x.1) (F₁.dst x)
        (afterEnd x.flip (ord (F₁.dst x)))
    · have ha₂ : ¬ (x.1 ∈ F₂.E ∧ F₂.src x = v) := fun ⟨h1, h2⟩ =>
        ha ⟨hG.2.1.symm ▸ h1, (src_eq_of_graphEq hG (hG.2.1.symm ▸ h1)).trans h2⟩
      simp [hopen, hopen₂, ha, ha₂]
termination_by (compOf F₁ v).card
decreasing_by
  rw [← ha.2]
  exact branch_card_lt hF₁ ha.1

theorem fullTour_of_graphEq {ord : ℕ → List End} {F₁ F₂ : MGraph} (hG : GraphEq F₁ F₂)
    (hF₁ : F₁.IsForest) (hF₂ : F₂.IsForest) (r : ℕ) :
    fullTour ord F₁ hF₁ r = fullTour ord F₂ hF₂ r :=
  fullTourBlocks_of_graphEq hG hG hF₁ hF₂ r (ord r)

/-! ## `TourValid` and `TourRepAt` transfer across `GraphEq` -/

theorem tourValid_of_graphEq {vCap eCap : ℕ} {s₁ s₂ : TourAbs}
    (hord : s₁.ord = s₂.ord) (hmk : s₁.marked = s₂.marked) (hR : s₁.rf.R = s₂.rf.R)
    (hG : GraphEq s₁.rf.F s₂.rf.F) (hv : TourValid vCap eCap s₁) :
    TourValid vCap eCap s₂ where
  ordWithin := hord ▸ hv.ordWithin
  compat :=
    { nodup := hord ▸ hv.compat.nodup
      unique := hord ▸ hv.compat.unique
      forest := isForest_of_graphEq hG hv.compat.forest
      vert := fun v hne => hG.1 ▸ hv.compat.vert v (hord ▸ hne)
      forestEnd := fun e he₂ => by
        have he₁ : e ∈ s₁.rf.F.E := hG.2.1.symm ▸ he₂
        obtain ⟨ht, hh⟩ := hv.compat.forestEnd e he₁
        obtain ⟨hte, hhe⟩ := hG.2.2 e he₁
        exact ⟨hord ▸ hte ▸ ht, hord ▸ hhe ▸ hh⟩ }
  roots_sub := hR ▸ hG.1 ▸ hv.roots_sub
  verts_lt := fun v hv₂ => hv.verts_lt v (hG.1.symm ▸ hv₂)
  unique_root := fun v hv₂ => by
    obtain ⟨r, ⟨hrR, hconn⟩, huniq⟩ := hv.unique_root v (hG.1.symm ▸ hv₂)
    exact ⟨r, ⟨hR ▸ hrR, (connected_iff_of_graphEq hG v r).mp hconn⟩,
      fun r' ⟨hrR', hconn'⟩ => huniq r' ⟨hR.symm ▸ hrR', (connected_iff_of_graphEq hG v r').mpr hconn'⟩⟩
  marked_open := fun x hx => by
    obtain ⟨⟨v, hvx⟩, hopen⟩ := hv.marked_open x (hmk.symm ▸ hx)
    exact ⟨⟨v, hord ▸ hvx⟩, hG.2.1 ▸ hopen⟩

theorem tourRootTagVal_of_eq {s₁ s₂ : TourAbs} (hord : s₁.ord = s₂.ord) (hR : s₁.rf.R = s₂.rf.R)
    (x : End) : tourRootTagVal s₁ x = tourRootTagVal s₂ x := by
  simp only [tourRootTagVal, hord, hR]

/-- `TourRepAt` is invariant under replacing `s₁.rf.F` by a `GraphEq` forest `s₂.rf.F` with the
same order, root set, and marked set. -/
theorem tourRep_of_graphEq {R_ord : DSRep (ℕ → List End)} {vCap eCap b : ℕ}
    {s₁ s₂ : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (hord : s₁.ord = s₂.ord) (hmk : s₁.marked = s₂.marked) (hR : s₁.rf.R = s₂.rf.R)
    (hG : GraphEq s₁.rf.F s₂.rf.F)
    (h : TourRepAt R_ord vCap eCap b s₁ x mem) :
    TourRepAt R_ord vCap eCap b s₂ x mem where
  valid := tourValid_of_graphEq hord hmk hR hG h.valid
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
  active_end := fun v hv e he => h.active_end v hv e (hord.symm ▸ he)
  inactive_owner := fun k hk hno => h.inactive_owner k hk (fun v => hord ▸ hno v)
  markArr_zero := h.markArr_zero
  nodesAt := h.nodesAt
  forestInv := h.forestInv
  nodes_exact := h.nodes_exact
  comp_none := fun r hr hnil => by
    have hft := fullTour_of_graphEq (ord := s₁.ord) hG h.valid.compat.forest
      (tourValid_of_graphEq hord hmk hR hG h.valid).compat.forest r
    exact h.comp_none r (hR.symm ▸ hr) (by rw [hft]; simpa only [hord] using hnil)
  comp_some := fun r hr hne => by
    have hft := fullTour_of_graphEq (ord := s₁.ord) hG h.valid.compat.forest
      (tourValid_of_graphEq hord hmk hR hG h.valid).compat.forest r
    obtain ⟨t, hct, ht_mem, hmap⟩ :=
      h.comp_some r (hR.symm ▸ hr) (by rw [hft]; simpa only [hord] using hne)
    refine ⟨t, hct, ht_mem, hmap.trans ?_⟩
    simpa only [hord] using hft
  tree_class := fun t ht => by
    rcases h.tree_class t ht with ⟨r, hr, hct⟩ | ⟨u, hu, hno⟩
    · exact Or.inl ⟨r, hR ▸ hr, hct⟩
    · exact Or.inr ⟨u, hu, fun v => hord ▸ hno v⟩
  inactive_single := fun u h1 h2 hno => h.inactive_single u h1 h2 (fun v => hord ▸ hno v)
  val_active := fun u h1 h2 hact => by
    have hact₁ : ∃ v, endOfKey (x.keyOf u) ∈ s₁.ord v := by simpa only [hord] using hact
    rw [h.val_active u h1 h2 hact₁, hG.2.1, hmk, tourRootTagVal_of_eq hord hR]
  val_inactive_rt := fun u h1 h2 hno => h.val_inactive_rt u h1 h2 (fun v => hord ▸ hno v)
  val_unused_rt := h.val_unused_rt

/-! ## Matching `initTourForest` to a rooted spanning forest `rf` of `G` -/

private theorem ordOfRecords_of_mem_nodup {recs : List (ℕ × List End)}
    (hnd : (recs.map Prod.fst).Nodup) {v : ℕ} {xs : List End} (hmem : (v, xs) ∈ recs) :
    ordOfRecords recs v = xs := by
  induction recs with
  | nil => cases hmem
  | cons p rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | hrest
    · simp [ordOfRecords]
    · have hne : p.1 ≠ v := fun h => hnd.1 (h ▸ List.mem_map_of_mem hrest)
      unfold ordOfRecords
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact ih hnd.2 hrest

/-- When `recs` represents the rotation order `ord = ρ.order` of a valid graph `G` with distinct
record keys, `es` lists the edges of a rooted spanning forest `rf` of `G`, and `rs` lists its
roots `rf.R`, the forest built by `initTourForest recs es rs` has root set `rf.R` and is
`GraphEq` to `rf.F`. -/
theorem initTourForest_graphEq_of_rsf {G : MGraph} {rf : RootedForest}
    (ρ : Rotation G) (hG : G.IsValid) (hF : rf.IsRootedSpanningForestOf G)
    {recs : List (ℕ × List End)} {es rs : List ℕ}
    (hnd : (recs.map Prod.fst).Nodup)
    (hord : ordOfRecords recs = ρ.order)
    (hes : es.toFinset = rf.F.E) (hrs : rs.toFinset = rf.R) :
    GraphEq (initTourForest recs es rs).F rf.F ∧ (initTourForest recs es rs).R = rf.R := by
  have hc := ordForestCompat_of_rotation ρ hG hF
  have hV : (((recs.filter fun p => !p.2.isEmpty).map Prod.fst).toFinset ∪ rs.toFinset) = rf.F.V := by
    ext v
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
      Bool.not_eq_true', List.isEmpty_eq_false_iff, hrs]
    constructor
    · rintro (⟨⟨u, xs⟩, ⟨hmem, hne⟩, rfl⟩ | hr)
      · have hxs : ρ.order u = xs := hord ▸ ordOfRecords_of_mem_nodup hnd hmem
        exact hc.vert u (hxs ▸ hne)
      · exact hF.2.1.symm ▸ hF.2.2.1 hr
    · intro hv
      by_cases hnil : ρ.order v = []
      · right
        have hvG : v ∈ G.V := hF.2.1 ▸ hv
        obtain ⟨r, ⟨hrR, hconn⟩, _⟩ := hF.2.2.2.1 v hvG
        obtain ⟨P, hW⟩ := hconn
        cases hW with
        | nil _ => exact hrR
        | cons he hsrc _ =>
          have hxF := hc.mem_ord_of_forest he
          rw [hsrc, hnil] at hxF
          cases hxF
      · left
        have hord_v : ordOfRecords recs v ≠ [] := by rw [hord]; exact hnil
        unfold ordOfRecords at hord_v
        cases hf : recs.find? (fun p => p.1 == v) with
        | none => simp [hf] at hord_v
        | some p =>
          have hpm := List.mem_of_find?_eq_some hf
          have hpeq : p.1 = v := by
            have := List.find?_some hf; simpa using this
          have hpne : p.2 ≠ [] := by simpa [hf] using hord_v
          exact ⟨p, ⟨hpm, hpne⟩, hpeq⟩
  refine ⟨⟨hV, hes, fun e he => ?_⟩, hrs⟩
  have heF : e ∈ rf.F.E := hes ▸ he
  dsimp only [initTourForest]
  rw [hord]
  exact ⟨hc.ordSrc_of_forest (x := (e, true)) heF, hc.ordSrc_of_forest (x := (e, false)) heF⟩

end MinCostFlow.SparseCore.Program
