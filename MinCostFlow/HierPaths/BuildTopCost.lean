module

public import MinCostFlow.HierPaths.BuildTopRootProc
import MinCostFlow.HierPaths.InitEntry
import MinCostFlow.HierPaths.BuildProgData

/-!
# Time and reservation for the padded root

The port builder charges linear time in the vertex and edge counts.
Its polynomial heap reserve is accounted for separately.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Consecutive buffers for the vertices, local IDs, padded owners, host graph and port work. -/
@[expose] def buildTopRootWorkspace (n m : ℕ) : ℕ :=
  n + n + 4 * m + (2 + 24 * m) + portGraphWorkSpace n m

/-- The root uses a linear work buffer and the cloud builder's polynomial heap reservation. -/
@[expose] def buildTopRootSpace (n m : ℕ) : ℕ :=
  buildTopRootWorkspace n m + portGraphHeapSpace m

theorem buildTopRootSpace_le (n m : ℕ) :
    buildTopRootSpace n m ≤ 42000 * (n + m + 2) ^ 4 := by
  have hn : n ≤ n + m + 2 := by omega
  have hm : m ^ 4 ≤ (n + m + 2) ^ 4 := Nat.pow_le_pow_left (by omega) _
  have hN : n + m + 2 ≤ (n + m + 2) ^ 4 := by
    calc
      _ = (n + m + 2) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  unfold buildTopRootSpace buildTopRootWorkspace portGraphWorkSpace portGraphHeapSpace
  omega

/-- The padded-root procedure has linear time on an input without isolated vertices. -/
theorem buildTopRoot_cost_le (w : ℕ) (G : Graph) (hv : G.IsValid) (hm : 1 ≤ G.m)
    (hn : ∀ v < G.n, 1 ≤ G.deg v) (args : List ℕ) (mem : ℕ → ℕ) :
    (buildTopRootContract w G).cost args mem ≤
      portGraphCost 0 G.m + 1000 * G.m := by
  have hnm := n_le_two_m hv hn
  simp only [buildTopRootContract, buildTopPortContract, portGraphCost]
  omega

end MinCostFlow.HierPaths

end
