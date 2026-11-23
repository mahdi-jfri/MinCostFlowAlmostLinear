module

public import MinCostFlow.Scaling.CapacitySort
public import MinCostFlow.Scaling.CallLoop
public import MinCostFlow.Scaling.ReductionAlgorithm
public import MinCostFlow.Scaling.SolverAdapter
import Mathlib.Tactic.Ring

/-!
# Counted binary search for the largest negative-cycle bottleneck

Lemma C.10 of Chen et al., arXiv:2203.00671v2, searches the edge capacity
values. At a candidate value, keep arcs of at least that capacity and solve
its unit-capacity circulation problem. A negative optimum answers yes. This
file implements that search with explicit calls, integer objectives, and a
ceiling-logarithmic iteration budget. It records the last successful unit
flow for subsequent negative-cycle extraction.
-/

@[expose] public section
namespace MinCostFlow.Scaling
namespace Circulation

/-- The unit-capacity test graph at a proposed bottleneck. Inactive edge slots
stay inactive, including at the candidate value zero. -/
abbrev bottleneckGraph (I : Circulation) (u : ℕ) : Circulation :=
  { I with capacity := fun e => if 0 < I.capacity e ∧ u ≤ I.capacity e then 1 else 0 }

/-- Every test graph has capacities at most one. -/
theorem bottleneckGraph_capacities (I : Circulation) (u : ℕ) :
    ∀ e, (I.bottleneckGraph u).capacity e ≤ 1 := by
  intro e
  change (if _ then 1 else 0) ≤ 1
  split <;> omega

end Circulation

/-- A half-open binary-search interval and the last successful test flow. -/
structure BottleneckState (I : Circulation) where
  lower : ℕ
  upper : ℕ
  best : Option (ℕ × (Fin I.m → ℤ))

namespace BottleneckState

/-- The number of candidate slots not yet ruled out. -/
def width {I : Circulation} (s : BottleneckState I) : ℕ := s.upper - s.lower

/-- One binary-search iteration. The test flow is integral, and its objective
sign is checked with integer arithmetic. Empty intervals make no solver call. -/
def step (solve : (J : Circulation) → Fin J.m → ℤ) {I : Circulation}
    (candidates : List ℕ) (s : BottleneckState I) : CallResult (BottleneckState I) :=
  if s.lower < s.upper then
    let mid := (s.lower + s.upper) / 2
    let u := candidates.getD mid 0
    let J := I.bottleneckGraph u
    let f := Circulation.solveWithZeroCapacities solve J
    let next := if J.integerObjective f < 0 then
      { lower := mid + 1, upper := s.upper, best := some (u, f) }
    else { s with upper := mid }
    ⟨next, [J.positiveInstance], 40 * (I.m + 1)⟩
  else ⟨s, [], 1⟩

/-- Each search step makes at most one solver call. -/
theorem step_calls (solve : (J : Circulation) → Fin J.m → ℤ) {I : Circulation}
    (candidates : List ℕ) (s : BottleneckState I) :
    (step solve candidates s).calls.length ≤ 1 := by
  unfold step
  split <;> simp

/-- Every test calls the supplied solver on exactly `m` edge slots. -/
theorem step_edges (solve : (J : Circulation) → Fin J.m → ℤ) {I : Circulation}
    (candidates : List ℕ) (s : BottleneckState I) :
    ∀ J ∈ (step solve candidates s).calls, J.m = I.m := by
  unfold step
  split
  · intro J hJ
    have he := List.mem_singleton.mp hJ
    subst J
    rfl
  · simp

/-- Every actual test presents strictly positive unit capacities to the solver. -/
theorem step_capacities (solve : (J : Circulation) → Fin J.m → ℤ) {I : Circulation}
    (candidates : List ℕ) (s : BottleneckState I) :
    ∀ J ∈ (step solve candidates s).calls, ∀ e, J.capacity e = 1 := by
  unfold step
  split
  · intro J hJ
    have he := List.mem_singleton.mp hJ
    subst J
    intro e
    have h := (I.bottleneckGraph _).positiveInstance_capacitiesBounded 1 (by decide)
      (I.bottleneckGraph_capacities _) e
    omega
  · simp

/-- Every test preserves the original polynomial cost bound. -/
theorem step_costs (solve : (J : Circulation) → Fin J.m → ℤ) {I : Circulation}
    (candidates : List ℕ) (s : BottleneckState I) (hc : I.CostsBounded (I.m ^ 10)) :
    ∀ J ∈ (step solve candidates s).calls, J.CostsBounded (J.m ^ 10) := by
  unfold step
  split
  · intro J hJ
    have he := List.mem_singleton.mp hJ
    subst J
    exact Circulation.positiveInstance_costsBounded _ _ hc
  · simp

/-- Graph construction and the objective test take a linear operation budget
in each iteration. The counter also covers the list-index lookup. -/
theorem step_work (solve : (J : Circulation) → Fin J.m → ℤ) {I : Circulation}
    (candidates : List ℕ) (s : BottleneckState I) :
    (step solve candidates s).work ≤ 40 * (I.m + 1) := by
  unfold step
  split
  · exact le_rfl
  · dsimp only
    omega

/-- Both binary-search branches reduce the interval width by at least half. -/
theorem step_width (solve : (J : Circulation) → Fin J.m → ℤ) {I : Circulation}
    (candidates : List ℕ) (s : BottleneckState I) :
    2 * (step solve candidates s).value.width ≤ s.width := by
  unfold step
  split
  · dsimp only
    split <;> dsimp only [width] <;> omega
  · dsimp only [width]
    omega

/-- The half-open interval remains valid and stays within the candidate list. -/
theorem step_interval (solve : (J : Circulation) → Fin J.m → ℤ) {I : Circulation}
    (candidates : List ℕ) (s : BottleneckState I)
    (hs : s.lower ≤ s.upper ∧ s.upper ≤ candidates.length) :
    (step solve candidates s).value.lower ≤ (step solve candidates s).value.upper ∧
      (step solve candidates s).value.upper ≤ candidates.length := by
  unfold step
  split
  · dsimp only
    split <;> dsimp only <;> constructor <;> omega
  · exact hs

/-- After `t` steps, the interval width is at most the original width divided
by `2^t`. The integer form avoids any rounding ambiguity. -/
theorem forRounds_width (solve : (J : Circulation) → Fin J.m → ℤ) {I : Circulation}
    (candidates : List ℕ) (rounds : ℕ) (s : BottleneckState I) :
    2 ^ rounds * (CallResult.forRounds (step solve candidates) rounds s).value.width ≤
      s.width := by
  induction rounds with
  | zero => simp only [CallResult.forRounds, CallResult.pure, Nat.pow_zero, Nat.one_mul, le_refl]
  | succ rounds ih =>
    have h := step_width solve candidates
      (CallResult.forRounds (step solve candidates) rounds s).value
    have hm := Nat.mul_le_mul_left (2 ^ rounds) h
    change 2 ^ (rounds + 1) *
      (step solve candidates (CallResult.forRounds (step solve candidates) rounds s).value).value.width ≤ _
    calc
      _ = 2 ^ rounds * (2 *
          (step solve candidates (CallResult.forRounds (step solve candidates) rounds s).value).value.width) := by
        rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ 2 ^ rounds * (CallResult.forRounds (step solve candidates) rounds s).value.width := hm
      _ ≤ s.width := ih

end BottleneckState

/-- Sort all edge capacity values, then search them for a negative unit optimum. -/
def bottleneckSearch (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) :
    CallResult (BottleneckState I) :=
  let sorted := sortCapacities (List.ofFn I.capacity)
  let r := CallResult.forRounds (BottleneckState.step solve sorted.1)
    (Nat.clog 2 (I.m + 1)) ⟨0, I.m, none⟩
  { r with work := sorted.2 + r.work + I.m }

/-- At most one solver call per ceiling-logarithmic search step is made. -/
theorem bottleneckSearch_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) :
    (bottleneckSearch solve I).calls.length ≤ Nat.clog 2 (I.m + 1) := by
  have h := CallResult.forRounds_calls
    (BottleneckState.step solve (sortCapacities (List.ofFn I.capacity)).1) 1
    (BottleneckState.step_calls solve _) (Nat.clog 2 (I.m + 1))
    (⟨0, I.m, none⟩ : BottleneckState I)
  simpa only [bottleneckSearch, Nat.mul_one] using h

/-- Every bottleneck-search call uses exactly `m` edges. -/
theorem bottleneckSearch_edges (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) : ∀ J ∈ (bottleneckSearch solve I).calls, J.m = I.m :=
  CallResult.forRounds_instances _ _ (BottleneckState.step_edges solve _) _ _

/-- All test calls use positive unit capacities. -/
theorem bottleneckSearch_capacities (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) : ∀ J ∈ (bottleneckSearch solve I).calls, ∀ e, J.capacity e = 1 :=
  CallResult.forRounds_instances _ _ (BottleneckState.step_capacities solve _) _ _

/-- The source's polynomial cost requirement holds for every actual query. -/
theorem bottleneckSearch_costs (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (hc : I.CostsBounded (I.m ^ 10)) :
    ∀ J ∈ (bottleneckSearch solve I).calls, J.CostsBounded (J.m ^ 10) :=
  CallResult.forRounds_instances _ _ (fun s => BottleneckState.step_costs solve _ s hc) _ _

/-- Sorting and all search steps take at most a padded `O(m log m)` counter. -/
theorem bottleneckSearch_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) :
    (bottleneckSearch solve I).work ≤
      120 * (Nat.clog 2 (I.m + 1) + 1) * (I.m + 1) := by
  have hs := sortCapacities_work (List.ofFn I.capacity)
  simp only [List.length_ofFn] at hs
  have hr := CallResult.forRounds_work
    (BottleneckState.step solve (sortCapacities (List.ofFn I.capacity)).1)
    (40 * (I.m + 1)) (BottleneckState.step_work solve _) (Nat.clog 2 (I.m + 1))
    (⟨0, I.m, none⟩ : BottleneckState I)
  change _ ≤ 120 * (Nat.clog 2 (I.m + 1) + 1) * (I.m + 1)
  dsimp only [bottleneckSearch]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at hs hr ⊢
  have he : Nat.clog 2 (I.m + 1) * (40 * I.m) =
      40 * (Nat.clog 2 (I.m + 1) * I.m) := by ring
  rw [he] at hr
  omega

/-- The explicit ceiling-logarithmic budget exhausts the search interval. -/
theorem bottleneckSearch_done (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) : (bottleneckSearch solve I).value.width = 0 := by
  have h := BottleneckState.forRounds_width solve
    (sortCapacities (List.ofFn I.capacity)).1 (Nat.clog 2 (I.m + 1))
    (⟨0, I.m, none⟩ : BottleneckState I)
  have hp := Nat.le_pow_clog (by decide : 1 < 2) (I.m + 1)
  change 2 ^ Nat.clog 2 (I.m + 1) * (bottleneckSearch solve I).value.width ≤ I.m at h
  by_contra hz
  have hw : 1 ≤ (bottleneckSearch solve I).value.width := Nat.pos_of_ne_zero hz
  have hm := Nat.mul_le_mul_left (2 ^ Nat.clog 2 (I.m + 1)) hw
  simp only [Nat.mul_one] at hm
  omega

end MinCostFlow.Scaling
