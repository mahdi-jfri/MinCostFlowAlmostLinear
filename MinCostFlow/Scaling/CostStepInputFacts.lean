module

public import MinCostFlow.Scaling.CostStepNumericFacts
import MinCostFlow.Scaling.BottleneckGuestSpace

/-!
# Word budgets for cost-round composition

The rounded graph has the current residual's capacities and its own
polynomial cost bound. A common input-field budget therefore bounds all
its encoded words. The measured dual model's label bound supplies the
actual returned magnitudes needed by the potential-update scan.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Current capacity constraints and the common numerical field budget
make every rounded-instance source word fit the host width. -/
theorem costRounded_words_fit {w : ℕ} {J : Circulation} (s : CostState J) (C U : ℕ)
    (hf : ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) (hu : ∀ e,J.capacity e≤U)
    (hfit : J.n+(J.m+J.m)+U+(J.m+J.m)^10+2<2^w) :
    ∀ x∈(s.roundedInstance C).solverWords,x<2^w := by
  let F := J.n+(J.m+J.m)+U+(J.m+J.m)^10+2
  have hcap := costRounded_capacities_le s C U hf hu
  have hcost := s.roundedInstance_polynomialCosts C
  have hmax := solverWords_max_le_of_bounds (s.roundedInstance C) F (by dsimp only [F]; omega)
    (by dsimp only [F]; omega)
    (fun e => (hcap e).trans (by dsimp only [F]; omega))
    (fun e => (hcost e).trans (by dsimp only [F]; omega)) (by dsimp only [F]; omega)
  intro x hx
  exact (Link.elem_le_foldr_max hx).trans hmax |>.trans_lt hfit

/-- The rounded graph's actual measured dual values satisfy the cost
round's potential magnitude budget, for every inner procedure. -/
theorem costStep_potential_update_budget
    (inner : (K : Circulation) → CallResult (Fin K.m → ℤ)) {J : Circulation}
    (s : CostState J) (C w : ℕ)
    (hbudget : ∀ v,2*((s.potential v).natAbs+(4*J.m+J.n)*(J.m+J.m)^10)<2^w) :
    let K := s.roundedInstance C
    let delta := (K.invokePositive inner).value
    let dual := K.extractDualMeasured inner delta
    ∀ v,2*((s.potential v).natAbs+(dual.value v).natAbs)<2^w := by
  let K := s.roundedInstance C
  let delta := (K.invokePositive inner).value
  have hdual := extractDualMeasured_natAbs_le inner K delta ((J.m+J.m)^10)
    (s.roundedInstance_polynomialCosts C)
  have hdim : 2*K.m+K.n=4*J.m+J.n := by change 2*(J.m+J.m)+J.n=_; omega
  rw [hdim] at hdual
  change ∀ v,2*((s.potential v).natAbs+((K.extractDualMeasured inner delta).value v).natAbs)<2^w
  intro v
  exact (Nat.mul_le_mul_left 2 (Nat.add_le_add_left (hdual v) _)).trans_lt (hbudget v)

end MinCostFlow.Scaling.Machine
