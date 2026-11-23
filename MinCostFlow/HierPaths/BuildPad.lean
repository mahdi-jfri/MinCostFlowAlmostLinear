module

public import MinCostFlow.Statement.Cited.Graphs
public import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Small tools for the game of `lemma_3`

The child construction (`lemma_3`) plays a cut-matching game on each child of a group. This file
collects three small tools for it.

* `smallerSide`, `padHalf`: from a cut `U` of `range s` take its smaller side `C`, and pad it to a
  set `C'` of exactly `s / 2` vertices (`card_padHalf`, `subset_padHalf`).
* `flatIndex`, `getD_flatten_flatIndex`: the position in `Ms.flatten` of entry `t` of `Ms[i]`, so
  that the walk of that entry is `emb (flatIndex Ms i t)`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-- The smaller side of the cut `(U, V \ U)` of `V`. -/
def smallerSide (V U : Finset ℕ) : Finset ℕ :=
  if U.card ≤ (V \ U).card then U else V \ U

/-- Pad `C ⊆ range s` to `s / 2` vertices by adding the least vertices outside `C`. -/
def padHalf (s : ℕ) (C : Finset ℕ) : Finset ℕ :=
  C ∪ (((Finset.range s \ C).sort (· ≤ ·)).take (s / 2 - C.card)).toFinset

/-- The position in `Ms.flatten` of entry `t` of `Ms[i]`. -/
def flatIndex {α : Type*} (Ms : List (List α)) (i t : ℕ) : ℕ :=
  ((Ms.take i).map List.length).sum + t

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

/-- The smaller side lies in `V` when `U` does. -/
theorem smallerSide_subset {V U : Finset ℕ} (hU : U ⊆ V) : smallerSide V U ⊆ V := by
  unfold smallerSide
  split_ifs
  · exact hU
  · exact Finset.sdiff_subset

/-- The smaller side has at most half of `V`, and at least the smaller of the two side sizes. -/
theorem card_smallerSide {V U : Finset ℕ} (hU : U ⊆ V) :
    2 * (smallerSide V U).card ≤ V.card ∧
      min U.card (V \ U).card ≤ (smallerSide V U).card := by
  have hc : U.card + (V \ U).card = V.card := by
    rw [Finset.card_sdiff_of_subset hU]; have := Finset.card_le_card hU; omega
  unfold smallerSide
  split_ifs with h
  · exact ⟨by omega, min_le_left _ _⟩
  · exact ⟨by omega, min_le_right _ _⟩

/-- The padded set contains `C`. -/
theorem subset_padHalf (s : ℕ) (C : Finset ℕ) : C ⊆ padHalf s C :=
  Finset.subset_union_left

/-- The padded set lies in `range s` when `C` does. -/
theorem padHalf_subset {s : ℕ} {C : Finset ℕ} (hC : C ⊆ Finset.range s) :
    padHalf s C ⊆ Finset.range s := by
  unfold padHalf
  intro v hv
  rcases Finset.mem_union.mp hv with h | h
  · exact hC h
  · have h' := List.mem_of_mem_take (List.mem_toFinset.mp h)
    exact (Finset.mem_sdiff.mp ((Finset.mem_sort _).mp h')).1

/-- The padded set has exactly `s / 2` vertices when `C ⊆ range s` has at most `s / 2`. -/
theorem card_padHalf {s : ℕ} {C : Finset ℕ} (hC : C ⊆ Finset.range s) (hCs : C.card ≤ s / 2) :
    (padHalf s C).card = s / 2 := by
  unfold padHalf
  set l := (Finset.range s \ C).sort (· ≤ ·)
  have hnd : (l.take (s / 2 - C.card)).Nodup := (Finset.sort_nodup _ _).sublist (List.take_sublist _ _)
  have hdisj : Disjoint C (l.take (s / 2 - C.card)).toFinset := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    have h' := List.mem_of_mem_take (List.mem_toFinset.mp hv')
    exact (Finset.mem_sdiff.mp ((Finset.mem_sort _).mp h')).2 hv
  rw [Finset.card_union_of_disjoint hdisj, List.toFinset_card_of_nodup hnd, List.length_take]
  have hl : l.length = s - C.card := by
    rw [Finset.length_sort, Finset.card_sdiff_of_subset hC, Finset.card_range]
  rw [hl]
  have := Finset.card_le_card hC
  rw [Finset.card_range] at this
  omega

/-- Entry `t` of `Ms[i]` sits at position `flatIndex Ms i t` of `Ms.flatten`. -/
theorem getD_flatten_flatIndex {α : Type*} (Ms : List (List α)) (d : α) {i t : ℕ}
    (hi : i < Ms.length) (ht : t < (Ms.getD i []).length) :
    flatIndex Ms i t < Ms.flatten.length ∧
      Ms.flatten.getD (flatIndex Ms i t) d = (Ms.getD i []).getD t d := by
  induction Ms generalizing i with
  | nil => simp at hi
  | cons m Ms ih =>
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at ht
      simp only [flatIndex, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
        List.flatten_cons, List.length_append, List.getD_cons_zero]
      refine ⟨by omega, ?_⟩
      rw [List.getD_append _ _ _ _ ht]
    | succ i =>
      simp only [List.getD_cons_succ] at ht
      simp only [List.length_cons] at hi
      obtain ⟨h1, h2⟩ := ih (i := i) (by omega) ht
      have hfi : flatIndex (m :: Ms) (i + 1) t = m.length + flatIndex Ms i t := by
        simp [flatIndex, List.take_succ_cons, Nat.add_assoc]
      rw [hfi]
      simp only [List.flatten_cons, List.length_append, List.getD_cons_succ]
      refine ⟨by omega, ?_⟩
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, h2]

end MinCostFlow.HierPaths
