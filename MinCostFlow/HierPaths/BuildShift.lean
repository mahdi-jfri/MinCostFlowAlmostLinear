module

public import MinCostFlow.Statement.Cited.Graphs
import Mathlib.Tactic.Linarith

/-!
# Shifting vertex numbers

The core cut player (`ExpanderDecomp.IsCorePlayer`) works on graphs whose vertices are
`0, …, s − 1`. A child of a group is the interval of terminals `o, …, o + s − 1`. So the game of
`lemma_3` keeps each child's game graph with local numbers, and the child host is moved to the
terminal numbers by adding `o` to every vertex (`shiftEdges`). Adding `o` is injective, so cuts
and expansion do not change (`cutIn_shift`, `isExpansionExpanderOn_shift`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited

/-- Add `o` to both ends of every edge. -/
def shiftEdges (o : ℕ) (E : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  E.map fun e => (o + e.1, o + e.2)

/-- Add `o` to every vertex of a set. -/
def shiftSet (o : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.image (o + ·)

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited

theorem mem_shiftSet {o x : ℕ} {A : Finset ℕ} : o + x ∈ shiftSet o A ↔ x ∈ A := by
  unfold shiftSet
  simp

theorem card_shiftSet (o : ℕ) (A : Finset ℕ) : (shiftSet o A).card = A.card := by
  unfold shiftSet
  exact Finset.card_image_of_injective _ (fun a b h => by simpa using h)

theorem shiftSet_sdiff (o : ℕ) (A B : Finset ℕ) :
    shiftSet o (A \ B) = shiftSet o A \ shiftSet o B := by
  unfold shiftSet
  exact Finset.image_sdiff _ _ (fun a b h => by simpa using h)

theorem shiftSet_subset {o : ℕ} {A B : Finset ℕ} (h : A ⊆ B) : shiftSet o A ⊆ shiftSet o B :=
  Finset.image_subset_image h

/-- **Cuts do not change under a shift.** -/
theorem cutIn_shift (n s o : ℕ) (E : List (ℕ × ℕ)) (A T : Finset ℕ) :
    (Graph.mk n (shiftEdges o E)).cutIn (shiftSet o A) (shiftSet o T) =
      (Graph.mk s E).cutIn A T := by
  unfold Graph.cutIn Graph.inside shiftEdges
  simp only [List.filter_map, List.length_map]
  have h1 : ((fun e : ℕ × ℕ => decide (e.1 ∈ shiftSet o A) && decide (e.2 ∈ shiftSet o A)) ∘
      fun e : ℕ × ℕ => (o + e.1, o + e.2)) = fun e => decide (e.1 ∈ A) && decide (e.2 ∈ A) := by
    funext e
    simp [Function.comp, mem_shiftSet]
  have h2 : ((fun e : ℕ × ℕ => decide (e.1 ∈ shiftSet o T) != decide (e.2 ∈ shiftSet o T)) ∘
      fun e : ℕ × ℕ => (o + e.1, o + e.2)) = fun e => decide (e.1 ∈ T) != decide (e.2 ∈ T) := by
    funext e
    simp [Function.comp, mem_shiftSet]
  rw [h1, h2]

/-- A set inside a shifted set is itself a shifted set. -/
theorem eq_shiftSet_of_subset {o : ℕ} {S T : Finset ℕ} (hT : T ⊆ shiftSet o S) :
    T = shiftSet o (S.filter fun x => o + x ∈ T) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hT hy)
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hy⟩, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (Finset.mem_filter.mp hx).2

/-- **Expansion does not change under a shift.** -/
theorem isExpansionExpanderOn_shift {n s o : ℕ} {E : List (ℕ × ℕ)} {S : Finset ℕ} {β : ℝ}
    (h : (Graph.mk s E).IsExpansionExpanderOn S β) :
    (Graph.mk n (shiftEdges o E)).IsExpansionExpanderOn (shiftSet o S) β := by
  intro T hT hne hneS
  set T₀ := S.filter fun x => o + x ∈ T
  have hTeq := eq_shiftSet_of_subset hT
  have hT₀S : T₀ ⊆ S := Finset.filter_subset _ _
  have hne₀ : T₀.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    rw [hTeq] at hy
    obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hy
    exact ⟨x, hx⟩
  have hneS₀ : T₀ ≠ S := by
    intro heq
    apply hneS
    rw [hTeq]
    exact congrArg (shiftSet o) heq
  have h1 := h T₀ hT₀S hne₀ hneS₀
  rw [hTeq, ← shiftSet_sdiff, card_shiftSet, card_shiftSet, cutIn_shift n s o E S T₀]
  exact h1

end MinCostFlow.HierPaths
