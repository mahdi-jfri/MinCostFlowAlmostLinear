module

public import MinCostFlow.Statement.Cited.Graphs
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Cuts of appended edge lists, and attaching vertices by a matching

The cut-matching game builds its witness graphs by appending edge lists: the matchings of the
rounds, then further matchings that attach the remaining vertices. This file proves two facts about
that.

* The cut of a set adds over appended edge lists (`cutIn_append`). So adding edges never lowers a
  cut, and expansion survives adding edges (`IsExpansionExpanderOn.append_right`).
* The injection lemma, `isExpansionExpanderOn_of_injection`. Suppose
  `S ⊆ X` and `G[S]` has expansion `β ≤ 1`. Append a matching that joins every vertex of `X \ S`
  to its own vertex of `S`. Then the result has expansion at least `β / 2` on `X`.

The proof of `isExpansionExpanderOn_of_injection`: take the side `Y` of the cut that holds at most half of `S`, and let `c` be
the size of `Y ∩ S`. Each vertex of `Y` outside `S` is matched either into `Y ∩ S` or across the
cut. At most `c` vertices are matched into `Y ∩ S`, since the matching is injective on `S`. At most
`t` are matched across the cut, where `t` is the number of matching edges across it. So the smaller
side of the cut has at most `|Y| ≤ 2c + t` vertices, while the cut has at least
`βc + t ≥ (β/2)(2c + t)` edges.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Appending edges -/

/-- The cut adds over appended edge lists. -/
theorem cutIn_append (n : ℕ) (E E' : List (ℕ × ℕ)) (X S : Finset ℕ) :
    (Graph.mk n (E ++ E')).cutIn X S = (Graph.mk n E).cutIn X S + (Graph.mk n E').cutIn X S := by
  simp [Graph.cutIn, Graph.inside, List.filter_append]

/-- Appending edges does not lower a cut. -/
theorem cutIn_le_cutIn_append_right (n : ℕ) (E E' : List (ℕ × ℕ)) (X S : Finset ℕ) :
    (Graph.mk n E).cutIn X S ≤ (Graph.mk n (E ++ E')).cutIn X S := by
  rw [cutIn_append]; omega

/-- Prepending edges does not lower a cut. -/
theorem cutIn_le_cutIn_append_left (n : ℕ) (E E' : List (ℕ × ℕ)) (X S : Finset ℕ) :
    (Graph.mk n E').cutIn X S ≤ (Graph.mk n (E ++ E')).cutIn X S := by
  rw [cutIn_append]; omega

/-- Expansion survives appending edges. -/
theorem IsExpansionExpanderOn.append_right {n : ℕ} {E : List (ℕ × ℕ)} {X : Finset ℕ} {β : ℝ}
    (h : (Graph.mk n E).IsExpansionExpanderOn X β) (E' : List (ℕ × ℕ)) :
    (Graph.mk n (E ++ E')).IsExpansionExpanderOn X β := by
  intro S hS hne hneX
  have h1 := h S hS hne hneX
  have h2 : ((Graph.mk n E).cutIn X S : ℝ) ≤ (Graph.mk n (E ++ E')).cutIn X S := by
    exact_mod_cast cutIn_le_cutIn_append_right n E E' X S
  linarith

/-- Expansion survives prepending edges. -/
theorem IsExpansionExpanderOn.append_left {n : ℕ} {E' : List (ℕ × ℕ)} {X : Finset ℕ} {β : ℝ}
    (h : (Graph.mk n E').IsExpansionExpanderOn X β) (E : List (ℕ × ℕ)) :
    (Graph.mk n (E ++ E')).IsExpansionExpanderOn X β := by
  intro S hS hne hneX
  have h1 := h S hS hne hneX
  have h2 : ((Graph.mk n E').cutIn X S : ℝ) ≤ (Graph.mk n (E ++ E')).cutIn X S := by
    exact_mod_cast cutIn_le_cutIn_append_left n E E' X S
  linarith

/-! ### Restricting a cut to a subset -/

/-- For `S ⊆ X`, the cut of `Y ∩ S` in `G[S]` is at most the cut of `Y` in `G[X]`: an edge with
both ends in `S` that crosses `Y ∩ S` has both ends in `X` and crosses `Y`. -/
theorem cutIn_inter_le (G : Graph) {X S : Finset ℕ} (hSX : S ⊆ X) (Y : Finset ℕ) :
    G.cutIn S (Y ∩ S) ≤ G.cutIn X Y := by
  unfold Graph.cutIn Graph.inside
  rw [List.filter_filter, List.filter_filter]
  apply length_filter_le_of_imp
  intro e _ he
  have hs : e.1 ∈ S ∧ e.2 ∈ S := by
    by_contra h
    rw [not_and_or] at h
    rcases h with h | h <;> simp [h] at he
  by_cases h1 : e.1 ∈ Y <;> by_cases h2 : e.2 ∈ Y <;>
    simp_all [hSX hs.1, hSX hs.2]

/-! ### Appending an injection matching halves the expansion at most -/

/-- The vertices of `Y` outside `S` number at most `|Y ∩ S| + t`, where `t` is the cut of `Y` in
the matching `M`. Each of them is the first end of an edge of `M`. Those edges whose second end is
in `Y` have distinct second ends in `Y ∩ S`, so there are at most `|Y ∩ S|` of them. The others
cross the cut, so there are at most `t` of them. -/
private theorem card_sdiff_le {n : ℕ} {M : List (ℕ × ℕ)} {X S Y : Finset ℕ} (hSX : S ⊆ X)
    (hM : ∀ e ∈ M, e.1 ∈ X ∧ e.1 ∉ S ∧ e.2 ∈ S) (hsnd : (M.map Prod.snd).Nodup)
    (hcover : ∀ v ∈ X, v ∉ S → ∃ e ∈ M, e.1 = v) (hYX : Y ⊆ X) :
    (Y \ S).card ≤ (Y ∩ S).card + (Graph.mk n M).cutIn X Y := by
  classical
  set M₁ := M.filter fun e => decide (e.1 ∈ Y) && decide (e.2 ∈ Y)
  set M₂ := M.filter fun e => decide (e.1 ∈ Y) && !decide (e.2 ∈ Y)
  have hcov : Y \ S ⊆ (M₁.map Prod.fst).toFinset ∪ (M₂.map Prod.fst).toFinset := by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    obtain ⟨e, he, rfl⟩ := hcover v (hYX hv.1) hv.2
    rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset]
    by_cases h2 : e.2 ∈ Y
    · exact Or.inl (List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, by simp [hv.1, h2]⟩, rfl⟩)
    · exact Or.inr (List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, by simp [hv.1, h2]⟩, rfl⟩)
  have h1 : M₁.length ≤ (Y ∩ S).card := by
    have hnd : (M₁.map Prod.snd).Nodup := hsnd.sublist (List.filter_sublist.map _)
    calc M₁.length = (M₁.map Prod.snd).length := by simp
      _ = (M₁.map Prod.snd).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ ≤ (Y ∩ S).card := by
        apply Finset.card_le_card
        intro w hw
        rw [List.mem_toFinset, List.mem_map] at hw
        obtain ⟨e, he, rfl⟩ := hw
        rw [List.mem_filter] at he
        have hS := (hM e he.1).2.2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at he
        exact Finset.mem_inter.mpr ⟨he.2.2, hS⟩
  have h2 : M₂.length ≤ (Graph.mk n M).cutIn X Y := by
    unfold Graph.cutIn Graph.inside
    rw [List.filter_filter]
    apply length_filter_le_of_imp
    intro e he hp
    have hX := hM e he
    have hY1 : e.1 ∈ Y := by simp_all
    have hY2 : e.2 ∉ Y := by simp_all
    simp [hX.1, hSX hX.2.2, hY1, hY2]
  have h3 := List.toFinset_card_le (M₁.map Prod.fst)
  have h4 := List.toFinset_card_le (M₂.map Prod.fst)
  have h5 := Finset.card_union_le (M₁.map Prod.fst).toFinset (M₂.map Prod.fst).toFinset
  have h6 := Finset.card_le_card hcov
  simp only [List.length_map] at h3 h4
  omega

/-- **Injection lemma.** Let `S ⊆ X`, and let `G[S]` have expansion at least `β` with
`0 ≤ β ≤ 1`. Let `M` be a list of edges from `X \ S` to `S` whose second ends are distinct and
whose first ends cover `X \ S`. Then `G + M` has expansion at least `β / 2` on `X`.

For a cut `T` of `X`, let `Y` be the side holding at most half of `S`, and let `c = |Y ∩ S|`. The
cut of `Y` in `G[X]` is at least `β c`, by the expansion of `G[S]`, and the cut in `M` is some
`t`. By `card_sdiff_le`, the smaller side of the cut has at most `|Y| ≤ 2c + t` vertices. Since
`β / 2 ≤ 1`, we get `(β / 2)(2c + t) ≤ β c + t`. -/
theorem isExpansionExpanderOn_of_injection {n : ℕ} {E M : List (ℕ × ℕ)} {X S : Finset ℕ}
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hSX : S ⊆ X)
    (hS : (Graph.mk n E).IsExpansionExpanderOn S β)
    (hM : ∀ e ∈ M, e.1 ∈ X ∧ e.1 ∉ S ∧ e.2 ∈ S) (hsnd : (M.map Prod.snd).Nodup)
    (hcover : ∀ v ∈ X, v ∉ S → ∃ e ∈ M, e.1 = v) :
    (Graph.mk n (E ++ M)).IsExpansionExpanderOn X (β / 2) := by
  classical
  intro T hTX _ _
  obtain ⟨Y, hYX, hcutY, hminY, hhalf⟩ : ∃ Y ⊆ X,
      (Graph.mk n (E ++ M)).cutIn X Y = (Graph.mk n (E ++ M)).cutIn X T ∧
      min (T.card : ℝ) (X \ T).card ≤ (Y.card : ℝ) ∧ (Y ∩ S).card ≤ (S \ Y).card := by
    by_cases h : (T ∩ S).card ≤ (S \ T).card
    · exact ⟨T, hTX, rfl, min_le_left _ _, h⟩
    · refine ⟨X \ T, Finset.sdiff_subset, cutIn_sdiff _ X T hTX, min_le_right _ _, ?_⟩
      have e1 : ((X \ T) ∩ S).card = (S \ T).card := by
        congr 1
        ext v
        simp only [Finset.mem_inter, Finset.mem_sdiff]
        constructor
        · rintro ⟨⟨_, h⟩, hs⟩
          exact ⟨hs, h⟩
        · rintro ⟨hs, h⟩
          exact ⟨⟨hSX hs, h⟩, hs⟩
      have e2 : (S \ (X \ T)).card = (T ∩ S).card := by
        congr 1
        ext v
        simp only [Finset.mem_inter, Finset.mem_sdiff, not_and, not_not]
        constructor
        · rintro ⟨hs, h⟩
          exact ⟨h (hSX hs), hs⟩
        · rintro ⟨ht, hs⟩
          exact ⟨hs, fun _ => ht⟩
      rw [e1, e2]
      omega
  set c := (Y ∩ S).card with hc
  have hE : β * c ≤ (Graph.mk n E).cutIn S (Y ∩ S) := by
    rcases Nat.eq_zero_or_pos c with h0 | hpos
    · rw [h0, Nat.cast_zero, mul_zero]
      positivity
    · have hne : (Y ∩ S).Nonempty := Finset.card_pos.mp hpos
      have hsd : S \ (Y ∩ S) = S \ Y := by
        ext v
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      have hneq : Y ∩ S ≠ S := by
        intro heq
        have h0 : (S \ Y).card = 0 := by
          rw [← hsd, heq, Finset.sdiff_self, Finset.card_empty]
        omega
      have h := hS (Y ∩ S) Finset.inter_subset_right hne hneq
      rw [hsd, min_eq_left (by exact_mod_cast hhalf)] at h
      exact h
  have hEX : (Graph.mk n E).cutIn S (Y ∩ S) ≤ (Graph.mk n E).cutIn X Y := cutIn_inter_le _ hSX Y
  have hsdY := card_sdiff_le (n := n) hSX hM hsnd hcover hYX
  have hYc := Finset.card_sdiff_add_card_inter Y S
  rw [← hcutY, cutIn_append]
  push_cast
  set t := (Graph.mk n M).cutIn X Y
  have hYr : (Y.card : ℝ) ≤ 2 * c + t := by
    have : Y.card ≤ 2 * c + t := by omega
    exact_mod_cast this
  have hEr : (β * c : ℝ) ≤ (Graph.mk n E).cutIn X Y :=
    le_trans hE (by exact_mod_cast hEX)
  have ht : (0 : ℝ) ≤ t := by positivity
  calc β / 2 * min (T.card : ℝ) (X \ T).card ≤ β / 2 * Y.card :=
        mul_le_mul_of_nonneg_left hminY (by positivity)
    _ ≤ β / 2 * (2 * c + t) := mul_le_mul_of_nonneg_left hYr (by positivity)
    _ = β * c + β / 2 * t := by ring
    _ ≤ (Graph.mk n E).cutIn X Y + t := by nlinarith

end MinCostFlow.ExpanderDecomp
