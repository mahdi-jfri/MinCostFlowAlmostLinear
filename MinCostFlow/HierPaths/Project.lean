module

public import MinCostFlow.HierPaths.Substitute
public import MinCostFlow.Spanner.Embedding

/-!
# Projecting host walks to walks of the input graph

The hierarchy is built in a host graph whose vertices are terminals (ports). Each terminal has an
*owner*, a vertex of the input graph `G`. Some host edges stand for an edge of `G` (they carry its
number as a *label*); the others are artificial (cloud and padding edges) and join two terminals of
the same owner. A host walk projects to a walk of `G` (a `Spanner.Walk`, the output form of
`GetPath`): drop the artificial steps, and replace each labelled step by the edge of `G` it
carries, between the owners of its two ends. So every host walk projects to an original walk by
suppressing artificial steps.

Main results:
* `projectWalk_isWalk`: the projection of a host walk from `u` to `v` is a walk of `G` from the
  owner of `u` to the owner of `v`.
* `edges_projectWalk`, `length_projectWalk_le`: its edges are the labels of the labelled steps, so
  its length is at most the host length.
* `walkLoad_projectFamily_le`: when distinct host edges carry distinct labels, an edge of `G`
  occurs in the projected family at most as often as some host edge occurs in the host family.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- The projection of the host edge walk `es` of the edge list `EH`, started at `x`: an
unlabelled step is dropped, and a step along a host edge `j` with label `some e` becomes the step
along edge `e` of the input graph between the owners of the two ends of `j`. -/
def projectWalk (EH : List (ℕ × ℕ)) (owner : ℕ → ℕ) (label : ℕ → Option ℕ) :
    ℕ → List ℕ → Walk
  | _, [] => Walk.empty
  | x, j :: es =>
    match label j with
    | none => projectWalk EH owner label (otherEnd EH j x) es
    | some e => (Walk.single (owner x) (owner (otherEnd EH j x)) e).append
        (projectWalk EH owner label (otherEnd EH j x) es)

/-- The owners and labels project the host edge list `EH` onto the input graph `G`: the ends of
every host edge have owners in `G`; an unlabelled host edge joins two terminals with the same
owner; and a host edge with label `e` stands for edge `e` of `G`, whose ends are the owners of its
two ends (in either order). -/
def IsProjection (G : Graph) (EH : List (ℕ × ℕ)) (owner : ℕ → ℕ) (label : ℕ → Option ℕ) : Prop :=
  ∀ j < EH.length,
    owner (edgeAt EH j).1 < G.n ∧ owner (edgeAt EH j).2 < G.n ∧
      (label j = none → owner (edgeAt EH j).1 = owner (edgeAt EH j).2) ∧
      ∀ e, label j = some e →
        e < G.m ∧ Walk.EdgeMatches (G.edges.getD e (0, 0)) (owner (edgeAt EH j).1)
          (owner (edgeAt EH j).2)

/-- The number of occurrences of edge number `e` in a family of walks of the input graph. -/
def walkLoad (F : List Walk) (e : ℕ) : ℕ :=
  (F.map fun P => P.edges.count e).sum

/-- Project every walk of a host family. -/
def projectFamily (EH : List (ℕ × ℕ)) (owner : ℕ → ℕ) (label : ℕ → Option ℕ)
    (F : List (ℕ × List ℕ)) : List Walk :=
  F.map fun p => projectWalk EH owner label p.1 p.2

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- The first edge `j` of a walk at `u` has the ends `u` and `otherEnd EH j u`, in some order. -/
theorem ends_of_isEdgeWalk_cons {EH : List (ℕ × ℕ)} {u v j : ℕ} {es : List ℕ}
    (h : IsEdgeWalk EH u v (j :: es)) :
    ((edgeAt EH j).1 = u ∧ (edgeAt EH j).2 = otherEnd EH j u) ∨
      ((edgeAt EH j).1 = otherEnd EH j u ∧ (edgeAt EH j).2 = u) := by
  unfold otherEnd
  split_ifs with h1
  · exact Or.inl ⟨h1, rfl⟩
  · refine Or.inr ⟨rfl, ?_⟩
    cases h with
    | cons _ hend _ =>
      rcases hend with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h h1
      · exact h

/-- The edges of the projection are the labels of the labelled steps, in order. -/
theorem edges_projectWalk (EH : List (ℕ × ℕ)) (owner : ℕ → ℕ) (label : ℕ → Option ℕ) (x : ℕ)
    (es : List ℕ) : (projectWalk EH owner label x es).edges = es.filterMap label := by
  induction es generalizing x with
  | nil => rfl
  | cons j es ih =>
    unfold projectWalk
    cases hl : label j with
    | none => simp [ih, hl]
    | some e => simp [Walk.edges_append, ih, hl, Walk.single]

/-- **Projection does not lengthen walks.** -/
theorem length_projectWalk_le (EH : List (ℕ × ℕ)) (owner : ℕ → ℕ) (label : ℕ → Option ℕ)
    (x : ℕ) (es : List ℕ) : (projectWalk EH owner label x es).edges.length ≤ es.length := by
  rw [edges_projectWalk]
  exact List.length_filterMap_le _ _

/-- **Projection keeps walks.** If `es` is a host walk from `u` to `v` and the owners and labels
project `EH` onto `G`, then the projection is a walk of `G` from the owner of `u` to the owner of
`v`. The start owner must be a vertex of `G`; this matters only for the empty walk. -/
theorem projectWalk_isWalk {G : Graph} {EH : List (ℕ × ℕ)} {owner : ℕ → ℕ}
    {label : ℕ → Option ℕ} (hproj : IsProjection G EH owner label) {u v : ℕ} {es : List ℕ}
    (hW : IsEdgeWalk EH u v es) (hu : owner u < G.n) :
    (projectWalk EH owner label u es).IsWalk G (owner u) (owner v) := by
  induction es generalizing u with
  | nil =>
    cases hW
    exact ⟨hu, hu, Or.inl ⟨rfl, rfl, rfl⟩⟩
  | cons j es ih =>
    have hj : j < EH.length := hW.lt_length j List.mem_cons_self
    obtain ⟨ho1, ho2, hnone, hsome⟩ := hproj j hj
    have hends := ends_of_isEdgeWalk_cons hW
    have hy : owner (otherEnd EH j u) < G.n := by
      rcases hends with ⟨_, h2⟩ | ⟨h1, _⟩
      · rw [← h2]; exact ho2
      · rw [← h1]; exact ho1
    have hrest := ih (isEdgeWalk_tail_otherEnd hW) hy
    unfold projectWalk
    cases hl : label j with
    | none =>
      have heq : owner u = owner (otherEnd EH j u) := by
        have h := hnone hl
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2] at h; exact h
        · rw [h1, h2] at h; exact h.symm
      simp only
      rw [heq]
      exact hrest
    | some e =>
      obtain ⟨he, hm⟩ := hsome e hl
      simp only
      refine Walk.isWalk_append (Walk.isWalk_single hu hy he ?_) hrest
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at hm; exact hm
      · rw [h1, h2] at hm; exact Walk.edgeMatches_symm hm

/-- Every vertex of the projection of a host walk is the owner of the start or of the far end of
one of its edges. -/
theorem mem_verts_projectWalk {EH : List (ℕ × ℕ)} {owner : ℕ → ℕ} {label : ℕ → Option ℕ}
    {x w : ℕ} {es : List ℕ} (hw : w ∈ (projectWalk EH owner label x es).verts) :
    w = owner x ∨ ∃ j ∈ es, w = owner (edgeAt EH j).1 ∨ w = owner (edgeAt EH j).2 := by
  induction es generalizing x with
  | nil => simp [projectWalk, Walk.empty] at hw
  | cons j es ih =>
    have hother : otherEnd EH j x = (edgeAt EH j).1 ∨ otherEnd EH j x = (edgeAt EH j).2 := by
      unfold otherEnd; split_ifs <;> simp
    have hrec : w ∈ (projectWalk EH owner label (otherEnd EH j x) es).verts →
        w = owner x ∨ ∃ j' ∈ j :: es, w = owner (edgeAt EH j').1 ∨ w = owner (edgeAt EH j').2 := by
      intro hw'
      rcases ih hw' with h | ⟨j', hj', h⟩
      · right
        refine ⟨j, List.mem_cons_self, ?_⟩
        rcases hother with h' | h'
        · rw [h'] at h; exact Or.inl h
        · rw [h'] at h; exact Or.inr h
      · exact Or.inr ⟨j', List.mem_cons_of_mem _ hj', h⟩
    unfold projectWalk at hw
    cases hl : label j with
    | none =>
      rw [hl] at hw
      exact hrec hw
    | some e =>
      rw [hl] at hw
      rcases Walk.mem_verts_append_left hw with h | h
      · simp only [Walk.single, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact Or.inl rfl
        · right
          refine ⟨j, List.mem_cons_self, ?_⟩
          rcases hother with h' | h' <;> rw [h'] <;> simp
      · exact hrec h

/-- When at most one host edge carries the label `e`, namely `j₀`, the edge `e` occurs in the
projection exactly as often as `j₀` occurs in the host walk. -/
theorem count_projectWalk_of_unique {EH : List (ℕ × ℕ)} {owner : ℕ → ℕ} {label : ℕ → Option ℕ}
    {e j₀ : ℕ} (h : ∀ j, label j = some e ↔ j = j₀) (x : ℕ) (es : List ℕ) :
    (projectWalk EH owner label x es).edges.count e = es.count j₀ := by
  rw [edges_projectWalk]
  induction es with
  | nil => rfl
  | cons a es ih =>
    rw [List.filterMap_cons, List.count_cons]
    by_cases ha : a = j₀
    · have hl : label a = some e := (h a).mpr ha
      rw [hl]
      simp [ih, ha]
    · have hne : (a == j₀) = false := beq_eq_false_iff_ne.mpr ha
      cases hl : label a with
      | none => simp [ih, hne]
      | some e' =>
        have he' : e' ≠ e := by
          intro hee
          rw [hee] at hl
          exact ha ((h a).mp hl)
        have : (e' == e) = false := beq_eq_false_iff_ne.mpr he'
        simp [List.count_cons, ih, hne, this]

/-- When no host edge carries the label `e`, the edge `e` does not occur in a projection. -/
theorem count_projectWalk_of_none {EH : List (ℕ × ℕ)} {owner : ℕ → ℕ} {label : ℕ → Option ℕ}
    {e : ℕ} (h : ∀ j, label j ≠ some e) (x : ℕ) (es : List ℕ) :
    (projectWalk EH owner label x es).edges.count e = 0 := by
  rw [edges_projectWalk, List.count_eq_zero]
  intro hmem
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hmem
  exact h j hj

/-- **Projection does not raise the occurrence load.** If distinct host edges carry distinct labels
and every host edge occurs at most `r` times in total in the host family `F`, then every edge of
the input graph occurs at most `r` times in total in the projected family. -/
theorem walkLoad_projectFamily_le {EH : List (ℕ × ℕ)} {owner : ℕ → ℕ} {label : ℕ → Option ℕ}
    (hinj : ∀ j j' e, label j = some e → label j' = some e → j = j')
    {F : List (ℕ × List ℕ)} {r : ℕ} (hr : ∀ j, occLoad F j ≤ r) (e : ℕ) :
    walkLoad (projectFamily EH owner label F) e ≤ r := by
  classical
  by_cases hex : ∃ j₀, label j₀ = some e
  · obtain ⟨j₀, hj₀⟩ := hex
    have hiff : ∀ j, label j = some e ↔ j = j₀ := fun j =>
      ⟨fun hj => hinj j j₀ e hj hj₀, fun hj => hj ▸ hj₀⟩
    have heq : walkLoad (projectFamily EH owner label F) e = occLoad F j₀ := by
      unfold walkLoad projectFamily occLoad
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro p _
      exact count_projectWalk_of_unique hiff p.1 p.2
    rw [heq]
    exact hr j₀
  · have hnone : ∀ j, label j ≠ some e := fun j hj => hex ⟨j, hj⟩
    have heq : walkLoad (projectFamily EH owner label F) e = 0 := by
      unfold walkLoad projectFamily
      rw [List.map_map]
      have : ((fun P : Walk => P.edges.count e) ∘ fun p : ℕ × List ℕ =>
          projectWalk EH owner label p.1 p.2) = fun _ => 0 := by
        funext p
        exact count_projectWalk_of_none hnone p.1 p.2
      rw [this]
      simp
    omega

end MinCostFlow.HierPaths
