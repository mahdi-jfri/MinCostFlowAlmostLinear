module

public import MinCostFlow.ExpanderDecomp.PortRounding
import MinCostFlow.ExpanderDecomp.Injection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Expansion of the port graph, and padding

The port-graph lemma `lemma_2` builds the root host of the hierarchy: the port graph of the input
graph `G` (`ExpanderDecomp.portGraph`), padded to a power of two of vertices. This file proves its
two expansion steps.

* `isExpansionExpanderOn_portGraph` (expansion before padding). If `G` has conductance at least
  `φ > 0` and every cloud expander has expansion at least `1 / a₀`, the port graph of `G` has edge
  expansion (by cardinality) at least `min(φ, 1) / (2 a₀ + 1)`; with the explicit expander,
  `a₀ = 12` and the bound is `min(φ, 1) / 25`.
  Take a port cut `U` with smaller side `s` and boundary `a`. Round every cloud to its majority
  side (`ExpanderDecomp.roundPortCut`). By cloud expansion at most `u ≤ a₀ a` ports move. The
  rounded cut `S` of `G` has volume at least `s − u` on each side, since the volume of `S` is the
  number of ports of its clouds, and it has at most `a + u` edges, since each moved port lies on
  one original edge. Conductance gives `min(φ, 1)(s − u) ≤ a + u`. This also holds when rounding
  makes a side empty, since then `s ≤ u`. So `min(φ, 1) s ≤ a + 2u ≤ (2 a₀ + 1) a`.
* `isExpansionExpanderOn_pad` (expansion after padding). Attaching new vertices `n₀ + i` to
  distinct old vertices `att i` keeps at least half of an expansion `β ≤ 1`. This is
  `ExpanderDecomp.isExpansionExpanderOn_of_injection` for the matching of the attachment edges.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The attachment edges `(n₀ + i, att i)` for `i < q`: new vertex `n₀ + i` is joined to the old
vertex `att i`. -/
def attEdges (n₀ q : ℕ) (att : ℕ → ℕ) : List (ℕ × ℕ) :=
  (List.range q).map fun i => (n₀ + i, att i)

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The original-edge part of the port graph has at most as many cut edges as the whole port
graph. -/
private theorem cutIn_origPortEdges_le_portGraph (cloud : ℕ → Graph) (G : Graph)
    (X U : Finset ℕ) :
    (Graph.mk (2 * (G.inside X).length) (origPortEdges (G.inside X).length)).cutIn
        (Finset.range (2 * (G.inside X).length)) U ≤
      (portGraph cloud G X).cutIn (portGraph cloud G X).verts U := by
  unfold portGraph Graph.verts
  dsimp only
  exact cutIn_le_cutIn_append_right _ _ _ _ _

/-- A port set has at most as many ports as the canonical lift of its rounding, plus the moved
ports; the same holds for the complements. -/
private theorem card_le_lift_add_moved (G : Graph) (X U : Finset ℕ) :
    U.card ≤ (liftSet G X (roundPortCut G X U)).card + (movedPorts G X U).card ∧
      (Finset.range (2 * (G.inside X).length) \ U).card ≤
        (Finset.range (2 * (G.inside X).length) \ liftSet G X (roundPortCut G X U)).card +
          (movedPorts G X U).card := by
  set U' := liftSet G X (roundPortCut G X U)
  set V := Finset.range (2 * (G.inside X).length)
  constructor
  · have hsub : U ⊆ U' ∪ movedPorts G X U := by
      intro p hp
      by_cases hp' : p ∈ U'
      · exact Finset.mem_union_left _ hp'
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp, hp'⟩))
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  · have hsub : V \ U ⊆ (V \ U') ∪ movedPorts G X U := by
      intro p hp
      rw [Finset.mem_sdiff] at hp
      by_cases hp' : p ∈ U'
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp', hp.2⟩))
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp.1, hp'⟩)
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

/-- **Root host, expansion before padding.** Let every cloud expander have expansion at least
`1 / a₀`, and let `G` have conductance at least `φ > 0`. Then the port graph of `G` has edge
expansion at least `min(φ, 1) / (2 a₀ + 1)`. -/
theorem isExpansionExpanderOn_portGraph {cloud : ℕ → Graph} {α : ℝ}
    (hcloud : IsCloudExpander cloud α) {a₀ : ℕ} (ha₀ : 1 ≤ a₀) (hα : (1 : ℝ) / a₀ ≤ α)
    {G : Graph} {φ : ℝ} (hφ : 0 < φ) (hG : G.IsConductanceExpanderOn G.verts φ) :
    (portGraph cloud G G.verts).IsExpansionExpanderOn (portGraph cloud G G.verts).verts
      (min φ 1 / (2 * a₀ + 1)) := by
  intro U hU _ _
  set X := G.verts
  set S := roundPortCut G X U
  set a := (portGraph cloud G X).cutIn (portGraph cloud G X).verts U
  set u := (movedPorts G X U).card
  have hSX : S ⊆ X := roundPortCut_subset G X U
  have hU' : U ⊆ Finset.range (2 * (G.inside X).length) := hU
  have hmove : u ≤ a₀ * a := movedPorts_le_mul_cut hcloud ha₀ hα hU
  have hcutS : G.cutIn X S ≤ a + u := by
    have h1 : G.cutIn X S ≤ _ := cutIn_roundPortCut_le_orig_add_moved hU'
    have h2 := cutIn_origPortEdges_le_portGraph cloud G X U
    omega
  obtain ⟨hU1, hU2⟩ := card_le_lift_add_moved G X U
  rw [card_liftSet, card_sdiff_liftSet hSX] at *
  have hU1 : U.card ≤ G.volIn X S + u := hU1
  have hU2 : ((portGraph cloud G X).verts \ U).card ≤ G.volIn X (X \ S) + u := hU2
  set φ' := min φ 1
  have hφ'0 : 0 ≤ φ' := le_min hφ.le zero_le_one
  have hφ'1 : φ' ≤ 1 := min_le_right _ _
  have hφ'φ : φ' ≤ φ := min_le_left _ _
  set s : ℝ := min (U.card : ℝ) ((portGraph cloud G X).verts \ U).card
  have hs0 : 0 ≤ s := le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hkey : φ' * (s - u) ≤ a + u := by
    by_cases hS : S.Nonempty ∧ S ≠ X
    · have hc := hG S hSX hS.1 hS.2
      set mv : ℝ := min (G.volIn X S : ℝ) (G.volIn X (X \ S))
      have hmv0 : 0 ≤ mv := le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hsmv : s - u ≤ mv := by
        have h1 : (U.card : ℝ) ≤ G.volIn X S + u := by exact_mod_cast hU1
        have h2 : (((portGraph cloud G X).verts \ U).card : ℝ) ≤ G.volIn X (X \ S) + u := by
          exact_mod_cast hU2
        have h3 : s ≤ mv + u := by
          rw [← min_add_add_right]
          exact min_le_min h1 h2
        linarith
      have hcS : (G.cutIn X S : ℝ) ≤ a + u := by exact_mod_cast hcutS
      calc φ' * (s - u) ≤ φ' * mv := mul_le_mul_of_nonneg_left hsmv hφ'0
        _ ≤ φ * mv := mul_le_mul_of_nonneg_right hφ'φ hmv0
        _ ≤ G.cutIn X S := hc
        _ ≤ a + u := hcS
    · have hsu : s ≤ u := by
        rcases not_and_or.mp hS with h | h
        · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
          have hv : G.volIn X S = 0 := by rw [hSe]; simp [Graph.volIn]
          have h1 : (U.card : ℝ) ≤ u := by
            have : U.card ≤ u := by omega
            exact_mod_cast this
          exact le_trans (min_le_left _ _) h1
        · have hSe : X \ S = ∅ := by
            rw [not_not] at h
            rw [h, Finset.sdiff_self]
          have hv : G.volIn X (X \ S) = 0 := by rw [hSe]; simp [Graph.volIn]
          have h2 : (((portGraph cloud G X).verts \ U).card : ℝ) ≤ u := by
            have : ((portGraph cloud G X).verts \ U).card ≤ u := by omega
            exact_mod_cast this
          exact le_trans (min_le_right _ _) h2
      have h1 : φ' * (s - u) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hφ'0 (by linarith)
      have h2 : (0 : ℝ) ≤ a + u := by positivity
      linarith
  have hmove' : (u : ℝ) ≤ a₀ * a := by exact_mod_cast hmove
  have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  have hφu : φ' * u ≤ u := mul_le_of_le_one_left hu0 hφ'1
  have hmain : φ' * s ≤ (2 * a₀ + 1) * a := by nlinarith
  have hpos : (0 : ℝ) < 2 * a₀ + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  linarith

/-- **Root host, expansion after padding.** Let `E` have expansion at least `β` on the old vertices
`0, …, n₀ − 1`, with `0 ≤ β ≤ 1`. Attach each new vertex `n₀ + i`, `i < q`, by one edge to an old
vertex `att i`, distinct for distinct `i`. Then the result has expansion at least `β / 2` on all
`n₀ + q` vertices. -/
theorem isExpansionExpanderOn_pad {n₀ q : ℕ} {E : List (ℕ × ℕ)} {att : ℕ → ℕ} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hE : (Graph.mk n₀ E).IsExpansionExpanderOn (Finset.range n₀) β)
    (hatt : ∀ i < q, att i < n₀) (hinj : ∀ i < q, ∀ i' < q, att i = att i' → i = i') :
    (Graph.mk (n₀ + q) (E ++ attEdges n₀ q att)).IsExpansionExpanderOn
      (Finset.range (n₀ + q)) (β / 2) := by
  apply isExpansionExpanderOn_of_injection hβ0 hβ1
    (Finset.range_subset_range.mpr (Nat.le_add_right n₀ q)) hE
  · intro e he
    simp only [attEdges, List.mem_map, List.mem_range] at he
    obtain ⟨i, hi, rfl⟩ := he
    simp only [Finset.mem_range]
    exact ⟨by omega, by omega, hatt i hi⟩
  · simp only [attEdges, List.map_map]
    apply List.Nodup.map_on _ List.nodup_range
    intro i hi i' hi' h
    exact hinj i (List.mem_range.mp hi) i' (List.mem_range.mp hi') h
  · intro v hv hvS
    simp only [Finset.mem_range, not_lt] at hv hvS
    refine ⟨(v, att (v - n₀)), ?_, rfl⟩
    simp only [attEdges, List.mem_map, List.mem_range]
    exact ⟨v - n₀, by omega, by rw [Nat.add_sub_cancel' hvS]⟩

end MinCostFlow.HierPaths
