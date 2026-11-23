module

public import MinCostFlow.HierPaths.Loss
public import Mathlib.Data.Set.Function

/-!
# Surviving siblings keep intact matching edges

The initialization stores a perfect matching between every two sibling groups `Y` and `Z`,
given here as a bijection `σ` from the members of `Y` to those of `Z`. This file shows that if
both `Y` and `Z` contain a terminal that is not globally lost, then at least half of the matching
edges `y – σ y` have both ends not globally lost.

The reason: a terminal `u` of `Y` that is not globally lost shows that the global lost set meets
`Y` exactly in the lost set of `Y`, and that this set has at most `|Y| / 4` elements
(`globalLost_inter_members` and `four_mul_card_lost_le` of `HierPaths/Loss.lean`). The same holds
for `Z`. So at most `|Y| / 4 + |Z| / 4 = |Y| / 2` matching edges have a lost end.

The argument never uses that `Y` and `Z` are different children of one group, only that they
are groups at the same depth. So the statement is proved in that form. It includes `|Y| = 1`.
-/

public section

namespace MinCostFlow.HierPaths

open Finset

variable {x b : ℕ} {F : Finset ℕ}

/-- If a group at depth `j` contains a terminal that is not globally lost, at most a quarter of
its members are globally lost. -/
theorem four_mul_card_globalLost_inter_le (hb : 0 < b) {j g u : ℕ}
    (hu : u ∈ members x b j g) (hux : u < 2 ^ x) (hn : u ∉ globalLost x b F) :
    4 * (globalLost x b F ∩ members x b j g).card ≤ groupSize x b j := by
  rw [← mem_members_iff.mp hu, globalLost_inter_members hux hn]
  exact four_mul_card_lost_le hb hux hn j

/-- **Surviving pairs of siblings.** Let `Y` and `Z` be groups at depth `j` that each contain a
terminal that is not globally lost, and let `σ` be a bijection from the members of `Y` to those
of `Z`. Then at least half of the members `y` of `Y` have `y` and `σ y` both not globally lost. -/
theorem card_members_le_two_mul_card_surviving (hb : 0 < b) {j gY gZ uY uZ : ℕ}
    (huY : uY ∈ members x b j gY) (huYx : uY < 2 ^ x) (hnY : uY ∉ globalLost x b F)
    (huZ : uZ ∈ members x b j gZ) (huZx : uZ < 2 ^ x) (hnZ : uZ ∉ globalLost x b F)
    {σ : ℕ → ℕ} (hσ : Set.BijOn σ (members x b j gY) (members x b j gZ)) :
    (members x b j gY).card ≤ 2 *
      ((members x b j gY).filter
        (fun y => y ∉ globalLost x b F ∧ σ y ∉ globalLost x b F)).card := by
  classical
  have hY := four_mul_card_globalLost_inter_le hb huY huYx hnY
  have hZ := four_mul_card_globalLost_inter_le hb huZ huZx hnZ
  set Y := members x b j gY
  set L := globalLost x b F
  -- the members `y` with `σ y` lost inject into the lost members of `Z`
  have hσL : (Y.filter (fun y => σ y ∈ L)).card ≤ (L ∩ members x b j gZ).card := by
    apply card_le_card_of_injOn σ
    · intro y hy
      have hy' := mem_filter.mp hy
      exact mem_inter.mpr ⟨hy'.2, hσ.mapsTo hy'.1⟩
    · intro y hy y' hy' he
      exact hσ.injOn (mem_filter.mp hy).1 (mem_filter.mp hy').1 he
  have hbad : (Y.filter (fun y => ¬ (y ∉ L ∧ σ y ∉ L))).card ≤
      (L ∩ Y).card + (Y.filter (fun y => σ y ∈ L)).card := by
    calc (Y.filter (fun y => ¬ (y ∉ L ∧ σ y ∉ L))).card
        ≤ ((L ∩ Y) ∪ Y.filter (fun y => σ y ∈ L)).card := by
          apply card_le_card
          intro y hy
          rw [mem_filter] at hy
          rw [mem_union, mem_inter, mem_filter]
          by_cases hyL : y ∈ L
          · exact Or.inl ⟨hyL, hy.1⟩
          · exact Or.inr ⟨hy.1, by_contra fun h => hy.2 ⟨hyL, h⟩⟩
      _ ≤ _ := card_union_le _ _
  have hsplit := card_filter_add_card_filter_not (s := Y) (fun y => y ∉ L ∧ σ y ∉ L)
  rw [card_members] at hsplit ⊢
  omega

/-- **Surviving matching edge**, existence form: under the hypotheses of
`card_members_le_two_mul_card_surviving`, some member `y` of `Y` has `y` and `σ y` both not
globally lost. -/
theorem exists_surviving_matching_edge (hb : 0 < b) {j gY gZ uY uZ : ℕ}
    (huY : uY ∈ members x b j gY) (huYx : uY < 2 ^ x) (hnY : uY ∉ globalLost x b F)
    (huZ : uZ ∈ members x b j gZ) (huZx : uZ < 2 ^ x) (hnZ : uZ ∉ globalLost x b F)
    {σ : ℕ → ℕ} (hσ : Set.BijOn σ (members x b j gY) (members x b j gZ)) :
    ∃ y ∈ members x b j gY, y ∉ globalLost x b F ∧ σ y ∉ globalLost x b F := by
  classical
  have h := card_members_le_two_mul_card_surviving hb huY huYx hnY huZ huZx hnZ hσ
  rw [card_members] at h
  have hpos : 0 < ((members x b j gY).filter
      (fun y => y ∉ globalLost x b F ∧ σ y ∉ globalLost x b F)).card := by
    have := (groupSize_pos : 0 < groupSize x b j)
    omega
  obtain ⟨y, hy⟩ := card_pos.mp hpos
  exact ⟨y, (mem_filter.mp hy).1, (mem_filter.mp hy).2⟩

end MinCostFlow.HierPaths
