module

public import MinCostFlow.HierPaths.BuildTopScheduleLoop
public import MinCostFlow.HierPaths.BuildTopDriver

/-!
# Combining geometric fields with the rest of the row

The schedule writer fills columns three through five. Every other column
is preserved and can be initialized independently.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Complete the driver's row predicate from its geometric and other columns. -/
theorem buildTopScheduleWords_at {mem mem' : ℕ → ℕ} {x b table n j inputCell outputCell : ℕ}
    {D : BuildTopDepthInput} (hj : j < n)
    (hf : BuildTopScheduleGeometryFrame mem mem' table n)
    (hg : BuildTopScheduleGeometryAt mem' x b table n)
    (hs : D.childSize = groupSize x b (j + 1))
    (hk : D.branch = branching x b j) (hn : D.count = numGroups x b j)
    (hother : ∀ k (hklt : k < (D.scheduleWords inputCell outputCell).length), k < 3 ∨ 6 ≤ k →
      mem (table + 13 * j + k) = (D.scheduleWords inputCell outputCell)[k]'hklt) :
    ListAt mem' (table + 13 * j) (D.scheduleWords inputCell outputCell) := by
  obtain ⟨h3,h4,h5⟩ := hg j hj
  intro k hlen
  have hlt : k < 13 := by simpa [BuildTopDepthInput.scheduleWords] using hlen
  by_cases hcol : k < 3 ∨ 6 ≤ k
  · rw [hf _ ?_]
    · exact hother k hlen hcol
    · intro i hi
      unfold buildTopScheduleCell
      rcases Nat.lt_trichotomy i j with hij | rfl | hji
      · right; omega
      · omega
      · left; omega
  · have h : k = 3 ∨ k = 4 ∨ k = 5 := by omega
    rcases h with rfl | rfl | rfl
    · simpa [BuildTopDepthInput.scheduleWords, buildTopScheduleCell, hs] using h3
    · simpa [BuildTopDepthInput.scheduleWords, buildTopScheduleCell, hk, Nat.add_assoc] using h4
    · simpa [BuildTopDepthInput.scheduleWords, buildTopScheduleCell, hn, Nat.add_assoc] using h5

end MinCostFlow.HierPaths

end
