module

public import MinCostFlow.ExpanderDecomp.Embedding
public import MinCostFlow.ExpanderDecomp.Injection
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Joining expanding blocks

The recursive cut player certifies a large graph block by block. It splits the vertex set `X` into
blocks, certifies that each block expands, and then joins the blocks by matchings laid along a
small explicit expander on the block names. This file proves that the result expands, in a
form that separates the two kinds of edges.

The blocks are the fibres of a map `blk : ℕ → ℕ` on `X`. The edges are `Eint ++ Eext`. The
hypotheses are:
* each block expands by at least `β` in `Eint`;
* every vertex has degree at most `Δ` in `Eext[X]`;
* every union of blocks `U` has cut at least `α · min(|U|, |X \ U|)` in `Eext[X]`.

Then `Eint ++ Eext` has expansion at least `αβ / (Δ + 1)` on `X`
(`isExpansionExpanderOn_of_blocks`). The third hypothesis is what matchings along an
`α`-expander on equal blocks give. It is proved where the blocks are built.

The proof rounds a cut `T` to the union `T'` of the blocks that lie mostly in `T`. Let `D` be the
set of vertices on which `T` and `T'` differ. Inside each block, `D` is the smaller part of the
block, so the expansion of the blocks gives at least `β |D|` internal edges across `T`. The
rounded cut `T'` has at least `α (s - |D|)` external edges, where `s` is the smaller side of `T`.
Moving the vertices of `D` back loses at most `Δ |D|` of them. One of the two bounds is large.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Small facts about cuts -/

/-- The expansion bound holds for every subset, including `∅` and `X`, where both sides are
zero. -/
theorem IsExpansionExpanderOn.mul_min_le {G : Graph} {X : Finset ℕ} {ψ : ℝ}
    (h : G.IsExpansionExpanderOn X ψ) {S : Finset ℕ} (hS : S ⊆ X) :
    ψ * min (S.card : ℝ) (X \ S).card ≤ G.cutIn X S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.card_empty, Nat.cast_zero, min_eq_left (Nat.cast_nonneg _), mul_zero]
    exact Nat.cast_nonneg _
  · by_cases heq : S = X
    · subst heq
      rw [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero, min_eq_right (Nat.cast_nonneg _),
        mul_zero]
      exact Nat.cast_nonneg _
    · exact h S hS hne heq

/-- In `G[Y]`, the cut of `Y ∩ T` is the cut of `T`, since the edges of `G[Y]` have both ends in
`Y`. -/
theorem cutIn_inter_self (G : Graph) (Y T : Finset ℕ) : G.cutIn Y (Y ∩ T) = G.cutIn Y T := by
  unfold Graph.cutIn
  congr 1
  apply List.filter_congr
  intro e he
  rw [mem_inside_iff] at he
  simp [Finset.mem_inter, he.2.1, he.2.2]

/-- The cuts of `T` inside disjoint blocks of `X` add up to at most the cut of `T` in `X`. The
blocks are the fibres of `blk` on `X`. Each edge counted on the left has both ends in one block, so
it is counted for one block only, and it is an edge of `G[X]` across `T`. -/
theorem sum_cutIn_blocks_le (G : Graph) (X T : Finset ℕ) (blk : ℕ → ℕ) (I : Finset ℕ) :
    ∑ i ∈ I, G.cutIn (X.filter fun v => blk v = i) T ≤ G.cutIn X T := by
  classical
  simp_rw [cutIn_eq_card]
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro j hj
    rw [Finset.mem_biUnion] at hj
    obtain ⟨i, _, hj⟩ := hj
    simp only [Finset.mem_filter, Finset.mem_range, insideB, Bool.and_eq_true,
      decide_eq_true_eq] at hj ⊢
    exact ⟨hj.1, ⟨hj.2.1.1.1, hj.2.1.2.1⟩, hj.2.2⟩
  · intro i _ i' _ hii'
    refine Finset.disjoint_left.mpr ?_
    intro j hj hj'
    simp only [Finset.mem_filter, Finset.mem_range, insideB, Bool.and_eq_true,
      decide_eq_true_eq] at hj hj'
    exact hii' (hj.2.1.1.2.symm.trans hj'.2.1.1.2)

/-- If `T` and `T'` agree on `X` outside `D`, then the cut of `T'` exceeds the cut of `T` by at
most the volume of `D`: an edge across `T'` but not across `T` has an end in `D`. -/
theorem cutIn_le_cutIn_add_volIn (G : Graph) {X T T' D : Finset ℕ}
    (hD : ∀ v ∈ X, (v ∈ T ↔ v ∈ T') ∨ v ∈ D) :
    G.cutIn X T' ≤ G.cutIn X T + G.volIn X D := by
  rw [cutIn_eq_sum_map, cutIn_eq_sum_map, volIn_eq_sum_map, ← sum_map_add]
  apply sum_map_le_sum_map
  intro e he
  rw [mem_inside_iff] at he
  rcases hD e.1 he.2.1 with h1 | h1 <;> rcases hD e.2 he.2.2 with h2 | h2
  · simp only [← h1, ← h2]
    split_ifs <;> omega
  · simp only [h2, ↓reduceIte]
    split_ifs <;> omega
  · simp only [h1, ↓reduceIte]
    split_ifs <;> omega
  · simp only [h1, h2, ↓reduceIte]
    split_ifs <;> omega

/-! ### Expansion of a union of expanding blocks -/

/-- Inside one block, the vertices of `D` are the smaller part of the block with respect to `T`.
This is how the rounding chooses `A`: a block goes to `T'` when most of it lies in `T`. -/
private theorem card_fibre_le {X T A D : Finset ℕ} {blk : ℕ → ℕ} {i : ℕ} (hi : i ∈ X.image blk)
    (hA : ∀ j ∈ X.image blk, (j ∈ A ↔
      ((X.filter fun v => blk v = j) \ T).card < ((X.filter fun v => blk v = j) ∩ T).card))
    (hD : ∀ v, v ∈ D ↔ v ∈ X ∧ ¬ (v ∈ T ↔ blk v ∈ A)) :
    (D.filter fun v => blk v = i).card ≤
      min ((X.filter fun v => blk v = i) ∩ T).card ((X.filter fun v => blk v = i) \ T).card := by
  by_cases hiA : i ∈ A
  · have hsub : (D.filter fun v => blk v = i) ⊆ (X.filter fun v => blk v = i) \ T := by
      intro v hv
      rw [Finset.mem_filter, hD] at hv
      rw [Finset.mem_sdiff, Finset.mem_filter]
      obtain ⟨⟨hvX, hiff⟩, hb⟩ := hv
      rw [hb] at hiff
      exact ⟨⟨hvX, hb⟩, by tauto⟩
    have hlt := (hA i hi).mp hiA
    have := Finset.card_le_card hsub
    exact le_min (by omega) this
  · have hsub : (D.filter fun v => blk v = i) ⊆ (X.filter fun v => blk v = i) ∩ T := by
      intro v hv
      rw [Finset.mem_filter, hD] at hv
      rw [Finset.mem_inter, Finset.mem_filter]
      obtain ⟨⟨hvX, hiff⟩, hb⟩ := hv
      rw [hb] at hiff
      exact ⟨⟨hvX, hb⟩, by tauto⟩
    have hge : ¬ ((X.filter fun v => blk v = i) \ T).card <
        ((X.filter fun v => blk v = i) ∩ T).card := fun h => hiA ((hA i hi).mpr h)
    have := Finset.card_le_card hsub
    exact le_min this (by omega)

/-- The final arithmetic of Lemma 5. Here `s` is the smaller side of the cut, `s'` the smaller
side of the rounded cut, `d` the number of moved vertices, `ci` and `ce` the internal and external
cuts, and `ce'` the external cut of the rounded cut. -/
private theorem blocks_arith {α β Δ s s' d ci ce ce' : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hΔ0 : 0 ≤ Δ) (hd0 : 0 ≤ d) (hce0 : 0 ≤ ce)
    (hβd : β * d ≤ ci) (hs : s ≤ s' + d) (hext : α * s' ≤ ce') (hmv : ce' ≤ ce + Δ * d) :
    α * β / (Δ + 1) * s ≤ ci + ce := by
  have hαs : α * s ≤ ce + (Δ + 1) * d := by
    have h1 := mul_le_mul_of_nonneg_left hs hα0
    have h2 : α * d ≤ d := by nlinarith
    nlinarith
  have hΔ : (0 : ℝ) < Δ + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hΔ]
  have h1 := mul_le_mul_of_nonneg_left hαs hβ0
  have h2 : β * ce ≤ ce := by nlinarith
  have h3 : β * ((Δ + 1) * d) ≤ (Δ + 1) * ci := by nlinarith
  have h6 : 0 ≤ Δ * ce := mul_nonneg hΔ0 hce0
  nlinarith

/-- **Block lemma.** Let the blocks of `X` be the fibres of `blk`. Suppose that each
block has expansion at least `β` in `Eint`, that every vertex has degree at most `Δ` in `Eext[X]`,
and that every union `U` of blocks has cut at least `α · min(|U|, |X \ U|)` in `Eext[X]`, with
`0 ≤ α, β ≤ 1`. Then `Eint ++ Eext` has expansion at least `αβ / (Δ + 1)` on `X`.

For a cut `T`, let `T'` be the union of the blocks that lie mostly in `T`, and let `D` be the
vertices where `T` and `T'` differ, with `d = |D|`. Then:
* the internal cut of `T` is at least `β d`, by `card_fibre_le` and the expansion of the blocks;
* the external cut of `T'` is at least `α (s - d)`, where `s` is the smaller side of `T`, since
  each side of `T'` differs from the same side of `T` by at most `d` vertices;
* the external cut of `T` is at least that of `T'` minus `Δ d` (`cutIn_le_cutIn_add_volIn`).

So `α s ≤ c_ext + (Δ + 1) d` and `β d ≤ c_int`, which give `α β s ≤ (Δ + 1)(c_int + c_ext)`. -/
theorem isExpansionExpanderOn_of_blocks {n : ℕ} {Eint Eext : List (ℕ × ℕ)} {X : Finset ℕ}
    (blk : ℕ → ℕ) {α β : ℝ} {Δ : ℕ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hint : ∀ i ∈ X.image blk,
      (Graph.mk n Eint).IsExpansionExpanderOn (X.filter fun v => blk v = i) β)
    (hdeg : ∀ v ∈ X, (Graph.mk n Eext).degIn X v ≤ Δ)
    (hext : ∀ A : Finset ℕ, α * min ((X.filter fun v => blk v ∈ A).card : ℝ)
        (X \ X.filter fun v => blk v ∈ A).card ≤
        (Graph.mk n Eext).cutIn X (X.filter fun v => blk v ∈ A)) :
    (Graph.mk n (Eint ++ Eext)).IsExpansionExpanderOn X (α * β / (Δ + 1)) := by
  classical
  intro T hTX _ _
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, ∀ j ∈ X.image blk, (j ∈ A ↔
      ((X.filter fun v => blk v = j) \ T).card < ((X.filter fun v => blk v = j) ∩ T).card) :=
    ⟨(X.image blk).filter fun i =>
      ((X.filter fun v => blk v = i) \ T).card < ((X.filter fun v => blk v = i) ∩ T).card,
      fun j hj => by rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hj, h⟩⟩⟩
  obtain ⟨T', hT'def⟩ : ∃ T' : Finset ℕ, T' = X.filter fun v => blk v ∈ A := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Finset ℕ, D = X.filter fun v => ¬ (v ∈ T ↔ blk v ∈ A) := ⟨_, rfl⟩
  have hT' : ∀ v, v ∈ T' ↔ v ∈ X ∧ blk v ∈ A := fun v => by rw [hT'def, Finset.mem_filter]
  have hD : ∀ v, v ∈ D ↔ v ∈ X ∧ ¬ (v ∈ T ↔ blk v ∈ A) := fun v => by
    rw [hDdef, Finset.mem_filter]
  have hDX : D ⊆ X := fun v hv => ((hD v).mp hv).1
  -- The internal edges: at least `β |D|` of them cross `T`.
  have hβD : β * (D.card : ℝ) ≤ (Graph.mk n Eint).cutIn X T := by
    have hcard : D.card = ∑ i ∈ X.image blk, (D.filter fun v => blk v = i).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro v hv
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem blk (hDX (Finset.mem_coe.mp hv)))
    have hsum : ∑ i ∈ X.image blk, β * ((D.filter fun v => blk v = i).card : ℝ) ≤
        ∑ i ∈ X.image blk, ((Graph.mk n Eint).cutIn (X.filter fun v => blk v = i) T : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have h1 := IsExpansionExpanderOn.mul_min_le (hint i hi)
        (Finset.inter_subset_left : (X.filter fun v => blk v = i) ∩ T ⊆ _)
      rw [cutIn_inter_self] at h1
      have hsd : (X.filter fun v => blk v = i) \ ((X.filter fun v => blk v = i) ∩ T) =
          (X.filter fun v => blk v = i) \ T := by
        ext v
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      rw [hsd] at h1
      have h3 : ((D.filter fun v => blk v = i).card : ℝ) ≤
          min (((X.filter fun v => blk v = i) ∩ T).card : ℝ)
            ((X.filter fun v => blk v = i) \ T).card := by
        exact_mod_cast card_fibre_le hi hA hD
      exact le_trans (mul_le_mul_of_nonneg_left h3 hβ0) h1
    have hle : (∑ i ∈ X.image blk,
        ((Graph.mk n Eint).cutIn (X.filter fun v => blk v = i) T : ℝ)) ≤
        (Graph.mk n Eint).cutIn X T := by
      exact_mod_cast sum_cutIn_blocks_le (Graph.mk n Eint) X T blk (X.image blk)
    rw [hcard, Nat.cast_sum, Finset.mul_sum]
    linarith
  -- The external edges: moving `D` back loses at most `Δ |D|` edges.
  have hmove : (Graph.mk n Eext).cutIn X T' ≤ (Graph.mk n Eext).cutIn X T + Δ * D.card := by
    have h1 : (Graph.mk n Eext).cutIn X T' ≤
        (Graph.mk n Eext).cutIn X T + (Graph.mk n Eext).volIn X D := by
      apply cutIn_le_cutIn_add_volIn
      intro v hv
      by_cases h : (v ∈ T ↔ v ∈ T')
      · exact Or.inl h
      · right
        rw [hT'] at h
        rw [hD]
        exact ⟨hv, by tauto⟩
    have h2 := volIn_le_mul_card hDX hdeg (G := Graph.mk n Eext)
    omega
  -- Each side of `T'` differs from the same side of `T` by at most `|D|` vertices.
  have hc1 : T.card ≤ T'.card + D.card := by
    calc T.card ≤ (T' ∪ D).card := by
          apply Finset.card_le_card
          intro v hvT
          have hv := hTX hvT
          rw [Finset.mem_union, hT', hD]
          by_cases hb : blk v ∈ A
          · exact Or.inl ⟨hv, hb⟩
          · exact Or.inr ⟨hv, by tauto⟩
      _ ≤ _ := Finset.card_union_le _ _
  have hc2 : (X \ T).card ≤ (X \ T').card + D.card := by
    calc (X \ T).card ≤ ((X \ T') ∪ D).card := by
          apply Finset.card_le_card
          intro v hvT
          rw [Finset.mem_sdiff] at hvT
          rw [Finset.mem_union, Finset.mem_sdiff, hT', hD]
          by_cases hb : blk v ∈ A
          · exact Or.inr ⟨hvT.1, by tauto⟩
          · exact Or.inl ⟨hvT.1, by tauto⟩
      _ ≤ _ := Finset.card_union_le _ _
  have hext' := hext A
  rw [← hT'def] at hext'
  rw [cutIn_append]
  push_cast
  have hs : min (T.card : ℝ) (X \ T).card ≤ min (T'.card : ℝ) (X \ T').card + D.card := by
    have h1 : (T.card : ℝ) ≤ T'.card + D.card := by exact_mod_cast hc1
    have h2 : ((X \ T).card : ℝ) ≤ (X \ T').card + D.card := by exact_mod_cast hc2
    rw [← min_add_add_right]
    exact min_le_min h1 h2
  have hmv : ((Graph.mk n Eext).cutIn X T' : ℝ) ≤ (Graph.mk n Eext).cutIn X T + Δ * D.card := by
    exact_mod_cast hmove
  exact blocks_arith hα0 hα1 hβ0 hβ1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hβD hs hext' hmv

end MinCostFlow.ExpanderDecomp
