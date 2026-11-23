module

public import MinCostFlow.Scaling.GeneralFlowReduction
public import MinCostFlow.Scaling.DemandScan
import Mathlib.Tactic.Ring

/-!
# The two-call reduction algorithm

The reduction implicit in the proof of Lemma C.1 of Chen et al.,
arXiv:2203.00671v2, is implemented with integer arithmetic. It first rejects
inconsistent capacities, then tests feasibility using an auxiliary circulation,
and finally optimizes a residual circulation. The returned flow is integral.
Correctness is against all feasible real flows, or certifies that none exist.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Evaluate the objective of an integral circulation with integer arithmetic. -/
def Circulation.integerObjective (I : Circulation) (f : Fin I.m → ℤ) : ℤ :=
  ∑ e, I.cost e * f e

/-- The integer objective agrees with the real objective used for correctness. -/
theorem Circulation.integerObjective_cast (I : Circulation) (f : Fin I.m → ℤ) :
    (I.integerObjective f : ℝ) = I.objective (fun e => (f e : ℝ)) := by
  simp only [integerObjective, objective, Int.cast_sum, Int.cast_mul]

namespace FlowReduction

/-- Build the feasibility instance using one edge scan for its demand table. -/
abbrev buildFeasibilityInstance (I : Instance) (hv : I.IsValid) : Circulation :=
  (shiftedGraph I hv).demandInstance (buildShiftedDemands I hv)

/-- The computed instance agrees with the mathematical reduction. -/
theorem buildFeasibilityInstance_eq (I : Instance) (hv : I.IsValid) :
    buildFeasibilityInstance I hv = feasibilityInstance I hv := by
  unfold buildFeasibilityInstance
  rw [buildShiftedDemands_eq]

/-- The exact general-flow reduction. `none` means that the input has no
feasible flow. Both circulation calls and all flow updates use integer data. -/
def reduceToCirculation
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Instance) (hv : I.IsValid) :
    Option (Fin I.m → ℤ) :=
  if ∀ e, (I.edge e).lower ≤ (I.edge e).upper then
    let J := shiftedGraph I hv
    let P := buildFeasibilityInstance I hv
    let g := solve P
    if P.integerObjective g = -(J.demandMass (shiftedDemand I) : ℤ) then
      let f : Fin I.m → ℤ := fun e => g (Fin.castAdd (I.n + I.n) e)
      let h := solve (J.residual f)
      some (fun e => (I.edge e).lower + f e +
        h (Fin.castAdd I.m e) - h (Fin.natAdd I.m e))
    else none
  else none

/-- Correctness of the two-call reduction: success returns an integral exact
minimum-cost flow, and failure proves that no real feasible flow exists. -/
theorem reduceToCirculation_correct_of_calls
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid)
    (hfirst : (buildFeasibilityInstance I hv).Optimal
      (fun e => (solve (buildFeasibilityInstance I hv) e : ℝ)))
    (hsecond : ∀ f : Fin I.m → ℤ, I.IsFeasible (restore I (fun e => (f e : ℝ))) →
      ((shiftedGraph I hv).residual f).Optimal
        (fun e => (solve ((shiftedGraph I hv).residual f) e : ℝ))) :
    (∀ f, reduceToCirculation solve I hv = some f →
      I.IsMinCostFlow (fun e => (f e : ℝ))) ∧
    (reduceToCirculation solve I hv = none → ∀ f, ¬ I.IsFeasible f) := by
  classical
  by_cases hcap : ∀ e, (I.edge e).lower ≤ (I.edge e).upper
  · let J := shiftedGraph I hv
    let P := buildFeasibilityInstance I hv
    let g := solve P
    have hP : (feasibilityInstance I hv).Optimal (fun e => (g e : ℝ)) := by
      have h := hfirst
      change ((shiftedGraph I hv).demandInstance (buildShiftedDemands I hv)).Optimal
        (fun e => (g e : ℝ)) at h
      rw [buildShiftedDemands_eq] at h
      exact h
    by_cases hval : P.integerObjective g = -(J.demandMass (shiftedDemand I) : ℤ)
    · have heq : P.objective (fun e => (g e : ℝ)) =
          -(J.demandMass (shiftedDemand I) : ℝ) := by
        have hc := congrArg (fun z : ℤ => (z : ℝ)) hval
        simpa only [Circulation.integerObjective_cast, Int.cast_neg,
          Int.cast_natCast] using hc
      let f : Fin I.m → ℤ := fun e => g (Fin.castAdd (I.n + I.n) e)
      let h := solve (J.residual f)
      have hf : I.IsFeasible (restore I (fun e => (f e : ℝ))) := by
        have hr := J.demandRestrict_routes (shiftedDemand I)
          (fun e => (g e : ℝ)) hP.1 heq
        apply (feasible_restore_iff I hv hcap _).mpr
        exact hr
      have hm := minCostFlow_of_residual_optimal I hv hcap f hf
        (fun e => (h e : ℝ)) (hsecond f hf)
      have hrun : reduceToCirculation solve I hv = some (fun e =>
          (I.edge e).lower + f e + h (Fin.castAdd I.m e) - h (Fin.natAdd I.m e)) := by
        unfold reduceToCirculation
        rw [ite_eq_left hcap]
        change (if P.integerObjective g = -(J.demandMass (shiftedDemand I) : ℤ)
          then _ else _) = _
        rw [ite_eq_left hval]
      constructor
      · intro result hr
        rw [hrun] at hr
        cases Option.some.inj hr
        have hex : (fun e => (((I.edge e).lower + f e +
            h (Fin.castAdd I.m e) - h (Fin.natAdd I.m e) : ℤ) : ℝ)) =
            restore I (J.augment f (fun e => (h e : ℝ))) := by
          funext e
          simp only [restore, Circulation.augment, Circulation.project, Int.cast_add,
            Int.cast_sub]
          ring
        rw [hex]
        exact hm
      · intro hn
        rw [hrun] at hn
        cases hn
    · have hbad : P.objective (fun e => (g e : ℝ)) ≠
          -(J.demandMass (shiftedDemand I) : ℝ) := by
        intro heq
        apply hval
        apply (Int.cast_inj (α := ℝ)).mp
        simpa only [Circulation.integerObjective_cast, Int.cast_neg,
          Int.cast_natCast] using heq
      have hrun : reduceToCirculation solve I hv = none := by
        unfold reduceToCirculation
        rw [ite_eq_left hcap]
        change (if P.integerObjective g = -(J.demandMass (shiftedDemand I) : ℤ)
          then _ else _) = _
        rw [ite_eq_right hval]
      constructor
      · intro f hf
        rw [hrun] at hf
        cases hf
      · intro _
        exact infeasible_of_phase_value I hv hcap _ hP hbad
  · constructor
    · intro f hf
      unfold reduceToCirculation at hf
      rw [ite_eq_right hcap] at hf
      cases hf
    · intro _ f hf
      apply hcap
      intro e
      apply (Int.cast_le (R := ℝ)).mp
      exact le_trans (hf.2 e).1 (hf.2 e).2

/-- Correctness of the two-call reduction with a general exact solver. -/
theorem reduceToCirculation_correct
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.Optimal (fun e => (solve J e : ℝ)))
    (I : Instance) (hv : I.IsValid) :
    (∀ f, reduceToCirculation solve I hv = some f →
      I.IsMinCostFlow (fun e => (f e : ℝ))) ∧
    (reduceToCirculation solve I hv = none → ∀ f, ¬ I.IsFeasible f) :=
  reduceToCirculation_correct_of_calls solve I hv (hsolve _) (fun _ _ => hsolve _)

/-- Encode the reduction's answer using the exact convention of `Instance`. -/
def reduceAnswer (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) : List ℕ :=
  match reduceToCirculation solve I hv with
  | none => [0]
  | some f => 1 :: (List.finRange I.m).flatMap (fun e => encodeInt (f e))

/-- The reduction returns a correct answer in the problem statement's format,
including its certificate that no feasible real flow exists. -/
theorem reduceAnswer_correct (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.Optimal (fun e => (solve J e : ℝ)))
    (I : Instance) (hv : I.IsValid) : I.IsCorrectAnswer (reduceAnswer solve I hv) := by
  have hc := reduceToCirculation_correct solve hsolve I hv
  cases hr : reduceToCirculation solve I hv with
  | none =>
    left
    exact ⟨by simp only [reduceAnswer, hr], hc.2 hr⟩
  | some f =>
    right
    exact ⟨f, hc.1 f hr, by simp only [reduceAnswer, hr]⟩

end FlowReduction
end MinCostFlow.Scaling
