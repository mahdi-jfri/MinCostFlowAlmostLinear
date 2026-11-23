module

public import MinCostFlow.Scaling.ShiftedWordBounds
public import WordRAM.LinkDefs
import WordRAM.Entry

/-!
# Magnitudes in the required input encoding

The statement's maximum capacity includes demands and both capacity bounds.
Each magnitude occurs explicitly in `Instance.encode`. This file proves the
corresponding membership and maximum inequalities, so the reduction's word
bounds refer to the required input word size rather than a larger auxiliary
encoding. Costs are handled by the same input maximum.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Every lower capacity is bounded by the statement's capacity maximum. -/
theorem lower_natAbs_le_maxCapacity (I : Instance) (e : Edge) (he : e ∈ I.edges) :
    e.lower.natAbs ≤ I.maxCapacity := by
  have hh : max e.lower.natAbs e.upper.natAbs ≤ I.maxCapacity :=
    Link.elem_le_foldr_max (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩))
  exact (le_max_left _ _).trans hh

/-- Every upper capacity is bounded by the statement's capacity maximum. -/
theorem upper_natAbs_le_maxCapacity (I : Instance) (e : Edge) (he : e ∈ I.edges) :
    e.upper.natAbs ≤ I.maxCapacity := by
  have hh : max e.lower.natAbs e.upper.natAbs ≤ I.maxCapacity :=
    Link.elem_le_foldr_max (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩))
  exact (le_max_right _ _).trans hh

/-- A valid vertex demand's magnitude occurs explicitly in the input words. -/
theorem demand_natAbs_word_mem (I : Instance) (hv : I.IsValid) (v : Fin I.n) :
    (I.d v).natAbs ∈ I.encode := by
  have hi : v.val < I.demand.length := by rw [hv.2]; exact v.isLt
  have hz : I.d v ∈ I.demand := by
    change I.demand.getD v.val 0 ∈ I.demand
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨I.d v, hz, by simp [encodeInt]⟩)))

/-- Every vertex demand is bounded by the statement's capacity maximum. -/
theorem demand_natAbs_le_maxCapacity (I : Instance) (hv : I.IsValid) (v : Fin I.n) :
    (I.d v).natAbs ≤ I.maxCapacity := by
  have hi : v.val < I.demand.length := by rw [hv.2]; exact v.isLt
  have hmem : I.d v ∈ I.demand := by
    change I.demand.getD v.val 0 ∈ I.demand
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  exact Link.elem_le_foldr_max (List.mem_append_right _ (List.mem_map.mpr ⟨I.d v, hmem, rfl⟩))

private theorem fold_max_le (xs : List ℕ) (M : ℕ) (h : ∀ x ∈ xs, x ≤ M) :
    xs.foldr max 0 ≤ M := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    exact max_le (h x (List.mem_cons_self))
      (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- The capacity maximum is at most the largest word actually in the input. -/
theorem maxCapacity_le_encode_max (I : Instance) : I.maxCapacity ≤ I.encode.foldr max 0 := by
  apply fold_max_le
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    apply max_le
    · exact Link.elem_le_foldr_max (inputEdge_word_mem I e he (by simp [Edge.encode, encodeInt]))
    · exact Link.elem_le_foldr_max (inputEdge_word_mem I e he (by simp [Edge.encode, encodeInt]))
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    apply Link.elem_le_foldr_max
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨z, hz, by simp [encodeInt]⟩)))

/-- The cost maximum is also at most the largest word in the input. -/
theorem maxCost_le_encode_max (I : Instance) : I.maxCost ≤ I.encode.foldr max 0 := by
  apply fold_max_le
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  exact Link.elem_le_foldr_max (inputEdge_word_mem I e he (by simp [Edge.encode, encodeInt]))

end MinCostFlow.Scaling.Machine
