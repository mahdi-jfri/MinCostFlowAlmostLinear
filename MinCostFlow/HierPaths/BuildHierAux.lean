module

public import MinCostFlow.HierPaths.BuildChildHost
public import MinCostFlow.HierPaths.HierData
import Mathlib.Data.List.GetD

/-!
# Facts for the whole construction

* Shifting a graph moves the degrees in a shifted set with it (`inside_shift`, `degIn_shift`),
  and the edge numbers keep their places (`edgeAt_shiftEdges`).
* A group of the hierarchy is a shifted interval (`members_eq_shiftSet`), and the parent of a
  group is a group of the depth above (`parentGroup_lt`).
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

theorem inside_shift (n s o : ℕ) (E : List (ℕ × ℕ)) (A : Finset ℕ) :
    (Graph.mk n (shiftEdges o E)).inside (shiftSet o A) =
      shiftEdges o ((Graph.mk s E).inside A) := by
  unfold Graph.inside shiftEdges
  simp only [List.filter_map]
  congr 1
  apply List.filter_congr
  intro e _
  simp [Function.comp, mem_shiftSet]

/-- **Degrees do not change under a shift.** -/
theorem degIn_shift (n s o : ℕ) (E : List (ℕ × ℕ)) (A : Finset ℕ) (u : ℕ) :
    (Graph.mk n (shiftEdges o E)).degIn (shiftSet o A) (o + u) = (Graph.mk s E).degIn A u := by
  unfold Graph.degIn
  rw [inside_shift n s o E A]
  unfold shiftEdges
  simp only [List.filter_map, List.length_map]
  congr 1
  · congr 1
    apply List.filter_congr
    intro e _
    simp [Function.comp]
  · congr 1
    apply List.filter_congr
    intro e _
    simp [Function.comp]

theorem edgeAt_mem {E : List (ℕ × ℕ)} {j : ℕ} (h : j < E.length) : edgeAt E j ∈ E := by
  unfold edgeAt
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem edgeAt_shiftEdges {o : ℕ} {E : List (ℕ × ℕ)} {j : ℕ} (h : j < E.length) :
    edgeAt (shiftEdges o E) j = (o + (edgeAt E j).1, o + (edgeAt E j).2) := by
  unfold edgeAt shiftEdges
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h]
  simp

/-- A group is the interval of `groupSize` terminals from `g · groupSize`. -/
theorem members_eq_shiftSet (x b j g : ℕ) :
    members x b j g = shiftSet (g * groupSize x b j) (Finset.range (groupSize x b j)) := by
  ext u
  rw [mem_shiftSet_iff, Finset.mem_range]
  simp only [members, Finset.mem_Ico, add_mul, one_mul]
  omega

theorem numGroups_succ (x b j : ℕ) :
    numGroups x b (j + 1) = numGroups x b j * branching x b j := by
  have h1 := numGroups_mul_groupSize (x := x) (b := b) (j := j)
  have h2 := numGroups_mul_groupSize (x := x) (b := b) (j := j + 1)
  rw [groupSize_eq_mul_branching (j := j)] at h1
  apply Nat.eq_of_mul_eq_mul_right (groupSize_pos (x := x) (b := b) (j := j + 1))
  rw [h2, ← h1, Nat.mul_assoc]

theorem parentGroup_lt {x b j c : ℕ} (hc : c < numGroups x b (j + 1)) :
    parentGroup x b j c < numGroups x b j := by
  unfold parentGroup
  rw [Nat.div_lt_iff_lt_mul branching_pos, ← numGroups_succ]
  exact hc

theorem child_eq (x b j c : ℕ) :
    parentGroup x b j c * branching x b j + c % branching x b j = c := by
  unfold parentGroup
  rw [Nat.mul_comm]
  exact Nat.div_add_mod c _

theorem groupSize_succ_le (x b j : ℕ) : groupSize x b (j + 1) ≤ groupSize x b j := by
  rw [groupSize_eq_mul_branching (j := j)]
  exact Nat.le_mul_of_pos_left _ branching_pos

end MinCostFlow.HierPaths
