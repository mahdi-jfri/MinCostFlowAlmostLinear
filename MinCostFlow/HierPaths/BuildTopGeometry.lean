module

public import MinCostFlow.HierPaths.InitProgConnRows

/-!
# Indexing parent and child rows

A parent occupies an interval of terminals. Its children are consecutive
group numbers, so a local child number is an offset within that interval.
-/

public section

namespace MinCostFlow.HierPaths

variable {x b j : ℕ}

/-- The first global child number plus a local child number is in the parent's child interval. -/
theorem buildTopChild_mem (g c : ℕ) (hc : c < branching x b j) :
    g * branching x b j + c ∈ childGroups x b j g := by
  rw [childGroups_eq_Ico, Finset.mem_Ico]
  omega

/-- The child interval starts at the parent's terminal address plus the local child offset. -/
theorem buildTopChild_start (g c : ℕ) :
    (g * branching x b j + c) * groupSize x b (j + 1) =
      g * groupSize x b j + c * groupSize x b (j + 1) := by
  rw [Nat.add_mul, Nat.mul_assoc, ← groupSize_eq_mul_branching]

/-- The end of the parent is obtained by advancing over all of its children. -/
theorem buildTopParent_end (g : ℕ) :
    g * groupSize x b j + branching x b j * groupSize x b (j + 1) =
      (g + 1) * groupSize x b j := by
  rw [← groupSize_eq_mul_branching, Nat.add_mul, Nat.one_mul]

/-- An active local pair occupies the slot obtained from its two global child numbers. -/
theorem buildTopPair_slot {g c c' : ℕ} (hc' : c' < branching x b j) (hcc' : c < c')
    (hs : g * branching x b j + c < 2 ^ x) :
    pairOfIdx x b
      (pairIdxOf x b j (g * branching x b j + c) (g * branching x b j + c')) =
      (j, g * branching x b j + c, g * branching x b j + c') := by
  apply pairOfIdx_pairIdxOf (buildTopChild_mem g c (hcc'.trans hc'))
    (buildTopChild_mem g c' hc') (by omega) hs

end MinCostFlow.HierPaths

end
