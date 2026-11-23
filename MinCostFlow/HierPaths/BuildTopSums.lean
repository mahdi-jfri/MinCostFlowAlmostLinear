module

public import MinCostFlow.HierPaths.BuildTopValid

/-!
# Adding the work of the parent calls

At one depth the parent groups partition the terminals. Charging a
common factor to each terminal gives one charge of that factor per
terminal at that depth.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp
open scoped BigOperators

/-- Bound the cost of one call by its parent size times a common factor. -/
theorem buildTopLevelCost_le {K s k M r Δ L L' bh E : ℕ} {G : Graph}
    (hs : 1 ≤ s) (hk : 1 ≤ k) (he : G.m ≤ E * (s * k)) :
    buildLevelCost K G s k M r Δ L L' bh + 24 ≤
      s * k * (K * (buildLevelDegree L' *
        ((NOf M r)^2 * (WParam ParamConfig.default M)^(10*r^2+10) + buildLevelDegree L' + 1) +
        (buildLevelDegree L' * k + k*k + 1) * (E + 2) *
          (routePathLen Δ bh L + 1) * (routeCong Δ bh L + 1) + k + 1) + 24) := by
  let X := s * k
  let T := buildLevelDegree L'
  let A := (NOf M r)^2 * (WParam ParamConfig.default M)^(10*r^2+10) + T + 1
  let C := T*k + k*k + 1
  let d := routePathLen Δ bh L + 1
  let R := routeCong Δ bh L + 1
  have hx : 1 ≤ X := Nat.mul_pos (by omega) (by omega)
  change G.m ≤ E * X at he
  have he' : X + G.m + 1 ≤ X * (E + 2) := by
    calc
      _ ≤ X + E * X + X := by omega
      _ = _ := by ring
  have hk' : k ≤ X := Nat.le_mul_of_pos_left _ (by omega)
  have hk₂ : k * k ≤ X * k := Nat.mul_le_mul_right _ hk'
  unfold buildLevelCost
  change K * (T * X * A + C * (X + G.m + 1) * d * R + k*k + 1) + 24 ≤ _
  calc
    _ ≤ K * (T * X * A + C * (X * (E + 2)) * d * R + X*k + X) + X * 24 := by
      gcongr
      exact Nat.le_mul_of_pos_left _ hx
    _ = _ := by
      change _ = X * (K * (T * A + C * (E + 2) * d * R + k + 1) + 24)
      ring

/-- At one depth, a common charge per terminal is paid exactly once per terminal. -/
theorem buildTopDepthSum_le (x b j F : ℕ) (work : ℕ → ℕ)
    (hwork : ∀ g < numGroups x b j, work g ≤ groupSize x b j * F) :
    ∑ g ∈ Finset.range (numGroups x b j), work g ≤ 2 ^ x * F := by
  calc
    _ ≤ ∑ _g ∈ Finset.range (numGroups x b j), groupSize x b j * F :=
      Finset.sum_le_sum fun g hg => hwork g (Finset.mem_range.mp hg)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
      rw [← Nat.mul_assoc, numGroups_mul_groupSize]

/-- The depth factors sum over the full execution. -/
theorem buildTopAllDepthSum_le (x b D : ℕ) (factor : ℕ → ℕ) (work : ℕ → ℕ → ℕ)
    (hwork : ∀ j < D, ∀ g < numGroups x b j, work j g ≤ groupSize x b j * factor j) :
    ∑ j ∈ Finset.range D, ∑ g ∈ Finset.range (numGroups x b j), work j g ≤
      2 ^ x * ∑ j ∈ Finset.range D, factor j := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j hj => buildTopDepthSum_le x b j _ _
    (hwork j (Finset.mem_range.mp hj))

end MinCostFlow.HierPaths

end
