module

public import MinCostFlow.Scaling.ShortestRoutingModel
public import MinCostFlow.Scaling.IterationBounds
import Mathlib.Tactic.Linarith

/-!
# Integer cost-scaling loop and solver-call bounds

Algorithm CostScaling in Appendix C of Chen et al., arXiv:2203.00671v2,
starts at zero flow and repeatedly halves epsilon. This model stores a power
of two and integer potential numerators. With `B = 2*m`, a potential numerator
`p` represents the potential `(C+1)*p/(B^8*power)`. The numerator doubles when
the power doubles. Rounded costs are computed by integer division.

Each round calls the primal solver once and the primal-to-dual extraction model
once. This file proves the trace and work bounds of those functions. The
optimality invariants of the source's algorithm are proved separately.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Round an integer ratio to a nearest integer, with ties away from zero.
The algorithms use only positive denominators. -/
def nearestQuotient (z : ℤ) (d : ℕ) : ℤ :=
  let q : ℤ := ((z.natAbs + d / 2) / d : ℕ)
  if z < 0 then -q else q

/-- The integral state of the cost-scaling loop. -/
structure CostState (I : Circulation) where
  flow : Fin I.m → ℤ
  potential : Fin I.n → ℤ
  power : ℕ

namespace CostState

/-- Start at zero primal and dual vectors and denominator power one. -/
def initial (I : Circulation) : CostState I := ⟨fun _ => 0, fun _ => 0, 1⟩

/-- The reduced residual cost in units `(C+1)/((2*m)^8*power)`, before rounding. -/
def costNumerator {I : Circulation} (C : ℕ) (s : CostState I)
    (e : Fin (I.m + I.m)) : ℤ :=
  let R := I.residual s.flow
  R.cost e * ((I.m + I.m) ^ 8 : ℕ) * (s.power : ℤ) -
    ((C + 1 : ℕ) : ℤ) * (s.potential (R.tail e) - s.potential (R.head e))

/-- Rounded residual costs, computed by integer arithmetic. -/
def roundedCost {I : Circulation} (C : ℕ) (s : CostState I)
    (e : Fin (I.m + I.m)) : ℤ := nearestQuotient (s.costNumerator C e) (C + 1)

/-- The cost-rounded residual instance. Costs above `B^9` are clipped instead
of dropping their arcs, so the returned dual still constrains every original
arc. Such clipped arcs lie only on positive-cost cycles and will carry no
optimal primal flow. The lower clipping is redundant on epsilon-optimal states. -/
abbrev roundedInstance {I : Circulation} (C : ℕ) (s : CostState I) : Circulation :=
  let R := I.residual s.flow
  let B := I.m + I.m
  { R with
    cost := fun e => max (-((B ^ 8 : ℕ) : ℤ)) (min (s.roundedCost C e) ((B ^ 9 : ℕ) : ℤ)) }

/-- One cost-scaling round, with the two actual bounded-solver inputs recorded. -/
def step (solve : (J : Circulation) → Fin J.m → ℤ) (C : ℕ)
    {I : Circulation} (s : CostState I) : CallResult (CostState I) :=
  let J := s.roundedInstance C
  let delta := Circulation.solveWithZeroCapacities solve J
  let dual := J.extractDualModel solve delta
  { value :=
      { flow := fun e => s.flow e + delta (Fin.castAdd I.m e) - delta (Fin.natAdd I.m e)
        potential := fun v => 2 * (s.potential v + dual.value v)
        power := 2 * s.power }
    calls := J.positiveInstance :: dual.calls
    work := 80 * (I.m + I.n + 1) + dual.work }

/-- Every round makes exactly two calls to the supplied integral solver. -/
theorem step_calls (solve : (J : Circulation) → Fin J.m → ℤ) (C : ℕ)
    {I : Circulation} (s : CostState I) : (step solve C s).calls.length = 2 := rfl

/-- Every round's solver input has at most `8*m+2*n` edge slots. -/
theorem step_edges (solve : (J : Circulation) → Fin J.m → ℤ) (C : ℕ)
    {I : Circulation} (s : CostState I) :
    ∀ J ∈ (step solve C s).calls, J.m ≤ 8 * I.m + 2 * I.n := by
  intro J hJ
  rcases List.mem_cons.mp hJ with hJ | hJ
  · subst J
    change I.m + I.m ≤ _
    omega
  · have h := (s.roundedInstance C).extractDualModel_edges solve _ J hJ
    change J.m = 4 * (I.m + I.m) + 2 * I.n at h
    omega

/-- The round's other-work counter is at most `600*(m+n+1)`. -/
theorem step_work (solve : (J : Circulation) → Fin J.m → ℤ) (C : ℕ)
    {I : Circulation} (s : CostState I) :
    (step solve C s).work ≤ 600 * (I.m + I.n + 1) := by
  have h := (s.roundedInstance C).extractDualModel_work solve
    (Circulation.solveWithZeroCapacities solve (s.roundedInstance C))
  change 80 * (I.m + I.n + 1) + _ ≤ _
  calc
    80 * (I.m + I.n + 1) + _ ≤
        80 * (I.m + I.n + 1) + 200 * ((s.roundedInstance C).m +
          (s.roundedInstance C).n + 1) := Nat.add_le_add le_rfl h
    _ ≤ 600 * (I.m + I.n + 1) := by
      change 80 * (I.m + I.n + 1) + 200 * (I.m + I.m + I.n + 1) ≤ _
      omega

end CostState

/-- The explicit finite loop of Algorithm CostScaling, with integer states. -/
def costLoop (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) (C : ℕ) :
    CallResult (CostState I) :=
  CallResult.forRounds (CostState.step solve C) (costRounds I.n C) (CostState.initial I)

/-- The model makes at most twice the explicit cost-round budget many calls. -/
theorem costLoop_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) :
    (costLoop solve I C).calls.length ≤ 2 * costRounds I.n C := by
  have h := CallResult.forRounds_calls (CostState.step solve C) 2
    (fun s => (CostState.step_calls solve C s).le) (costRounds I.n C) (CostState.initial I)
  simpa only [costLoop, Nat.mul_comm] using h

/-- Every call has at most `8*m+2*n` edges, independent of the loop's states. -/
theorem costLoop_edges (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) :
    ∀ J ∈ (costLoop solve I C).calls, J.m ≤ 8 * I.m + 2 * I.n :=
  CallResult.forRounds_instances _ _ (fun s => CostState.step_edges solve C s) _ _

/-- The loop's other work includes its explicit loop-control counter. -/
theorem costLoop_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) :
    (costLoop solve I C).work ≤ costRounds I.n C * (600 * (I.m + I.n + 1) + 1) :=
  CallResult.forRounds_work _ _ (fun s => CostState.step_work solve C s) _ _

/-- In the nontrivial branch `n <= 2*C`, at most eight padded logarithms of
`C` many bounded-solver calls suffice. -/
theorem costLoop_calls_le_eight_log (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) (hC : 0 < C) (hn : I.n ≤ 2 * C) :
    (costLoop solve I C).calls.length ≤ 8 * Nat.clog 2 (C + 1) := by
  have h := costLoop_calls solve I C
  have ht := costRounds_le_four_log I.n C hC hn
  omega

/-- After isolated-vertex compression every cost-loop call has at most `12*m`
edge slots. -/
theorem costLoop_edges_le_twelve (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) (hn : I.n ≤ 2 * I.m) :
    ∀ J ∈ (costLoop solve I C).calls, J.m ≤ 12 * I.m := by
  intro J hJ
  have h := costLoop_edges solve I C J hJ
  omega

end MinCostFlow.Scaling
