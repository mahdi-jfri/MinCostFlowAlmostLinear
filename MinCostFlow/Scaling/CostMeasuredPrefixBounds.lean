module

public import MinCostFlow.Scaling.CostStepNumericFacts
import Mathlib.Tactic.Ring

/-!
# Bounds on every state reached by measured cost rounds

Every round doubles the denominator power. A dual extraction changes a
potential numerator by at most its source-routing edge count times the
rounded cost bound before that doubling. Induction bounds each potential
by a geometric expression. The actual capacity-backed corrections also
preserve the integral flow capacity constraints throughout the prefix.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The measured round doubles each numerator after adding a label whose
magnitude is at most the rounded source-routing cost budget. -/
theorem costStepMeasured_potential_growth
    (inner : (K : Circulation) → CallResult (Fin K.m → ℤ)) {J : Circulation}
    (s : CostState J) (C : ℕ) :
    ∀ v,((CostState.stepMeasured inner C s).value.potential v).natAbs≤
      2*((s.potential v).natAbs+(4*J.m+J.n)*(J.m+J.m)^10) := by
  let K := s.roundedInstance C
  let delta := (K.invokePositive inner).value
  let dual := K.extractDualMeasured inner delta
  have hdual := extractDualMeasured_natAbs_le inner K delta ((J.m+J.m)^10)
    (s.roundedInstance_polynomialCosts C)
  have hdim : 2*K.m+K.n=4*J.m+J.n := by change 2*(J.m+J.m)+J.n=_; omega
  rw [hdim] at hdual
  intro v
  change (2*(s.potential v+dual.value v)).natAbs≤_
  rw [Int.natAbs_mul]
  change 2*(s.potential v+dual.value v).natAbs≤_
  apply Nat.mul_le_mul_left 2
  exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left (hdual v) _)

/-- Every measured prefix has precisely the prescribed power of two. -/
theorem costMeasuredPrefix_power
    (inner : (K : Circulation) → CallResult (Fin K.m → ℤ)) (J : Circulation) (C t : ℕ) :
    (CallResult.forRounds (CostState.stepMeasured inner C) t (CostState.initial J)).value.power=2^t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change 2*(CallResult.forRounds (CostState.stepMeasured inner C) t (CostState.initial J)).value.power=2^(t+1)
    rw [ih,Nat.pow_succ,Nat.mul_comm]

/-- The geometric potential bound holds at every measured cost prefix.
The added two cost budgets make the induction a direct doubling. -/
theorem costMeasuredPrefix_potential
    (inner : (K : Circulation) → CallResult (Fin K.m → ℤ)) (J : Circulation) (C t : ℕ) :
    let Q := (4*J.m+J.n)*(J.m+J.m)^10
    ∀ v,((CallResult.forRounds (CostState.stepMeasured inner C) t (CostState.initial J)).value.potential v).natAbs+2*Q≤
      2^(t+1)*Q := by
  let Q := (4*J.m+J.n)*(J.m+J.m)^10
  change ∀ v,((CallResult.forRounds (CostState.stepMeasured inner C) t (CostState.initial J)).value.potential v).natAbs+2*Q≤2^(t+1)*Q
  induction t with
  | zero => intro v; change 0+2*Q≤2^1*Q; simp only [Nat.zero_add,Nat.pow_one]; exact le_rfl
  | succ t ih =>
    let s := (CallResult.forRounds (CostState.stepMeasured inner C) t (CostState.initial J)).value
    have hg := costStepMeasured_potential_growth inner s C
    intro v
    change ((CostState.stepMeasured inner C s).value.potential v).natAbs+2*Q≤2^(t+1+1)*Q
    calc
      _ ≤ 2*((s.potential v).natAbs+Q)+2*Q := Nat.add_le_add_right (hg v) _
      _ = 2*((s.potential v).natAbs+2*Q) := by ring
      _ ≤ 2*(2^(t+1)*Q) := Nat.mul_le_mul_left 2 (ih v)
      _ = _ := by rw [Nat.pow_succ]; ring

/-- The actual capacity-backed measured prefixes obey every original
integral capacity constraint. Conservation is not needed for this bound. -/
theorem costMeasuredPrefix_flow_bounds (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (J : Circulation) (C U t : ℕ) (hu : ∀ e,J.capacity e≤U) (hU : 1≤U) :
    let inner := fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U
    let s := (CallResult.forRounds (CostState.stepMeasured inner C) t (CostState.initial J)).value
    ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e := by
  apply CallResult.forRounds_invariant (CostState.stepMeasured _ C)
    (fun s : CostState J => ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e)
    (fun s hs => costStepMeasured_flow_bounds solver entry T hproc s C U hs hu hU)
  intro e
  exact ⟨le_rfl,Int.natCast_nonneg _⟩

end MinCostFlow.Scaling.Machine
