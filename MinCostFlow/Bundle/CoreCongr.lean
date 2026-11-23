module

public import MinCostFlow.Bundle.CoreBatch

/-!
# Tours and cores of forests that agree on their edges

Two forests with the same vertices, the same edges and the same endpoints of those edges
have the same tours, the same roots and the same core graph, whatever their endpoint maps say
at absent edge names. So an ordered core batch that ends at one of them also ends at the
other. The global forest of the component-wise LSFs records the endpoints of the current
graph, which change at an inserted edge name. These lemmas let the lemmas on ordered core batches
apply to it.
-/

@[expose] public section

namespace MinCostFlow.Bundle

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore

/-- Two rotations of one graph are equal when their orders are. -/
theorem Rotation.ext_order {G : MGraph} {ρ σ : Rotation G} (h : ρ.order = σ.order) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

private theorem subgraph_of_graphEq {F F' : MGraph} (h : GraphEq F F') : F.IsSubgraph F' :=
  ⟨h.1.symm.le, h.2.1.symm.le, fun e he => by
    have := h.2.2 e (h.2.1 ▸ he)
    exact ⟨this.1.symm, this.2.symm⟩⟩

/-- Graphs that agree on their edges have the same connectivity. -/
theorem connected_iff_of_graphEq {F F' : MGraph} (h : GraphEq F F') {u v : ℕ} :
    F.Connected u v ↔ F'.Connected u v :=
  ⟨connected_of_subgraph (subgraph_of_graphEq (graphEq_symm h)),
    connected_of_subgraph (subgraph_of_graphEq h)⟩

/-- Erasing an edge keeps agreement on edges. -/
theorem graphEq_eraseForestEdge {F F' : MGraph} (h : GraphEq F F') (e : ℕ) :
    GraphEq (eraseForestEdge F e) (eraseForestEdge F' e) :=
  ⟨h.1, by simp [h.2.1], fun f hf => h.2.2 f (Finset.mem_of_mem_erase hf)⟩

private theorem src_eq_of_graphEq {F F' : MGraph} (h : GraphEq F F') {x : End} (hx : x.1 ∈ F.E) :
    F.src x = F'.src x := by
  obtain ⟨e, b⟩ := x
  have := h.2.2 e hx
  cases b
  · exact this.2
  · exact this.1

private theorem dst_eq_of_graphEq {F F' : MGraph} (h : GraphEq F F') {x : End} (hx : x.1 ∈ F.E) :
    F.dst x = F'.dst x := by
  obtain ⟨e, b⟩ := x
  have := h.2.2 e hx
  cases b
  · exact this.1
  · exact this.2

/-- Tour blocks depend only on the edges of the forests and their endpoints. -/
theorem tourBlocks_congr {G F₀ F₀' : MGraph} (ρ : Rotation G) (hE₀ : F₀.E = F₀'.E) :
    ∀ (n : ℕ) (F F' : MGraph) (hF : F.IsForest) (hF' : F'.IsForest) (v : ℕ) (xs : List End),
      (compOf F v).card = n → GraphEq F F' →
      tourBlocks G F₀ ρ F hF v xs = tourBlocks G F₀' ρ F' hF' v xs := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F F' hF hF' v xs hn hEq
    rw [tourBlocks.eq_def G F₀ ρ F hF v xs, tourBlocks.eq_def G F₀' ρ F' hF' v xs]
    apply List.flatMap_congr
    intro x _
    rw [hE₀]
    by_cases h0 : x.1 ∈ F₀'.E
    · simp only [h0, not_true_eq_false, ↓reduceIte]
      by_cases hg : x.1 ∈ F.E ∧ F.src x = v
      · have hg' : x.1 ∈ F'.E ∧ F'.src x = v :=
          ⟨hEq.2.1 ▸ hg.1, (src_eq_of_graphEq hEq hg.1).symm.trans hg.2⟩
        rw [dite_eq_left hg, dite_eq_left hg', dst_eq_of_graphEq hEq hg.1]
        have hlt : (compOf (eraseForestEdge F x.1) (F'.dst x)).card < n := by
          rw [← dst_eq_of_graphEq hEq hg.1, ← hn, ← hg.2]
          exact branch_card_lt hF hg.1
        exact ih _ hlt _ _ _ _ _ _ rfl (graphEq_eraseForestEdge hEq x.1)
      · have hg' : ¬ (x.1 ∈ F'.E ∧ F'.src x = v) := by
          rintro ⟨h1, h2⟩
          exact hg ⟨hEq.2.1 ▸ h1, (src_eq_of_graphEq hEq (hEq.2.1 ▸ h1)).trans h2⟩
        rw [dite_eq_right hg, dite_eq_right hg']
    · simp [h0]

/-- Forests that agree on their edges have the same tours. -/
theorem tour_congr {G F F' : MGraph} (ρ : Rotation G) (hF : F.IsForest) (hF' : F'.IsForest)
    (hEq : GraphEq F F') (v : ℕ) : tour ρ hF v = tour ρ hF' v :=
  tourBlocks_congr ρ hEq.2.1 _ F F' hF hF' v _ rfl hEq

/-- Rooted forests with the same roots and agreeing forests have the same root map. -/
theorem root_congr {RF RF' : RootedForest} (hR : RF.R = RF'.R) (hEq : GraphEq RF.F RF'.F)
    (v : ℕ) : RF.root v = RF'.root v := by
  have hP : (fun r => r ∈ RF.R ∧ RF.F.Connected v r) = (fun r => r ∈ RF'.R ∧ RF'.F.Connected v r) := by
    funext r
    rw [hR, connected_iff_of_graphEq hEq]
  have key : ∀ (P Q : ℕ → Prop), P = Q → ∀ (h₁ : ∃ r, P r) (h₂ : ∃ r, Q r),
      Classical.choose h₁ = Classical.choose h₂ := by
    rintro P Q rfl h₁ h₂
    rfl
  have hiff : (∃ r, r ∈ RF.R ∧ RF.F.Connected v r) ↔ (∃ r, r ∈ RF'.R ∧ RF'.F.Connected v r) := by
    rw [hP]
  unfold RootedForest.root
  split_ifs with h₁ h₂ h₂
  · exact key _ _ hP h₁ h₂
  · exact absurd (hiff.mp h₁) h₂
  · exact absurd (hiff.mpr h₂) h₁
  · rfl

/-- LSFs whose forests agree on their edges and have the same roots have the same core graph
on every graph. -/
theorem coreGraph_congr (G : MGraph) {L L' : LSF} (hR : L.F.R = L'.F.R)
    (hEq : GraphEq L.F.F L'.F.F) : coreGraph G L = coreGraph G L' := by
  have hroot := root_congr hR hEq
  unfold coreGraph
  rw [hR, hEq.2.1]
  simp only [hroot]

/-- The core rotations of such LSFs have the same orders. -/
theorem coreRotation_order_congr {G : MGraph} {L L' : LSF} (ρ : Rotation G) (hG : G.IsValid)
    (hF : L.F.IsRootedSpanningForestOf G) (hF' : L'.F.IsRootedSpanningForestOf G)
    (hR : L.F.R = L'.F.R) (hEq : GraphEq L.F.F L'.F.F) :
    (coreRotation (L := L) ρ hG hF).order = (coreRotation (L := L') ρ hG hF').order := by
  funext v
  change (if v ∈ L.F.R then tour ρ hF.1 v else []) = (if v ∈ L'.F.R then tour ρ hF'.1 v else [])
  by_cases hv : v ∈ L.F.R
  · have hv' : v ∈ L'.F.R := hR ▸ hv
    simp only [hv, hv', ↓reduceIte, tour_congr ρ hF.1 hF'.1 hEq v]
  · have hv' : v ∉ L'.F.R := hR ▸ hv
    simp only [hv, hv', ↓reduceIte]

/-- An ordered core batch can end at any rotation with the same orders on a graph that agrees
on its edges. -/
theorem OrderedCoreBatch.congr_last {G H H' : MGraph} {β : ℕ} {ρ : Rotation G}
    {σ : Rotation H} {U : List Update} (h : OrderedCoreBatch β ρ σ U) (σ' : Rotation H')
    (hH : GraphEq H' H) (hσ : σ'.order = σ.order) : OrderedCoreBatch β ρ σ' U := by
  obtain ⟨hv, he, hr⟩ := h
  refine ⟨hv, graphEq_trans hH he, ?_⟩
  have : σ'.congrGraph (graphEq_trans hH he) = σ.congrGraph he := Rotation.ext_order hσ
  rw [this]
  exact hr

/-- An ordered core batch ending at one LSF also ends at any LSF with the same roots and a
forest that agrees on its edges. -/
theorem OrderedCoreBatch.congr_lsf {G H : MGraph} {β : ℕ} {ρ : Rotation G} {L L' : LSF}
    {U : List Update} (σ : Rotation H) (hH : H.IsValid)
    (hF : L.F.IsRootedSpanningForestOf H) (hF' : L'.F.IsRootedSpanningForestOf H)
    (hR : L.F.R = L'.F.R) (hEq : GraphEq L.F.F L'.F.F)
    (h : OrderedCoreBatch β ρ (coreRotation (L := L) σ hH hF) U) :
    OrderedCoreBatch β ρ (coreRotation (L := L') σ hH hF') U :=
  h.congr_last _ (by rw [coreGraph_congr H hR hEq]; exact graphEq_refl _)
    (coreRotation_order_congr σ hH hF' hF hR.symm (graphEq_symm hEq))

end MinCostFlow.Bundle
