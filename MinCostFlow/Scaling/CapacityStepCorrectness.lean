module

public import MinCostFlow.Scaling.CapacityLoopModel
public import MinCostFlow.Scaling.ApproximationCorrectness
public import MinCostFlow.Scaling.CapacityRoundingCorrectness
public import MinCostFlow.Scaling.CapacitySolverCorrectness
public import MinCostFlow.Scaling.ResidualGap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# One executed capacity-scaling round halves the objective gap

The proof of Lemma C.9 of Chen et al., arXiv:2203.00671v2, Appendix C,
uses C.10 to select a residual magnitude and C.12 to obtain a constant
approximate residual augmentation. A zero magnitude certifies optimality.
Otherwise the actual scaled solver call is optimal in the rounded graph,
and its `1.1` guarantee implies the weaker factor-two progress used by the
source. All flows and the objective gap remain integral.
-/

@[expose] public section
namespace MinCostFlow.Scaling.CapacityState
variable {I : Circulation}

/-- The nonnegative integral objective gap to a fixed optimal integral flow. -/
def objectiveGap (target : Fin I.m → ℤ) (s : CapacityState I) : ℤ :=
  I.integerObjective s.flow - I.integerObjective target

private theorem gap_zero_of_optimal (target : Fin I.m → ℤ) (s : CapacityState I)
    (ht : I.Optimal (fun e => (target e : ℝ))) (hs : I.Optimal (fun e => (s.flow e : ℝ))) :
    s.objectiveGap target = 0 := by
  have h1 := ht.2 _ hs.1
  have h2 := hs.2 _ ht.1
  have heq : I.objective (fun e => (s.flow e : ℝ)) = I.objective (fun e => (target e : ℝ)) := le_antisymm h2 h1
  rw [← I.integerObjective_cast, ← I.integerObjective_cast] at heq
  have hi := Int.cast_inj.mp heq
  exact sub_eq_zero.mpr hi

/-- Every actual capacity step preserves feasibility and a valid early-stop
certificate, and halves the integral gap to an optimum. -/
theorem step_gap (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (hc : I.CostsBounded (I.m ^ 10)) (hm : 0 < I.m)
    (target : Fin I.m → ℤ) (htarget : I.Optimal (fun e => (target e : ℝ)))
    (s : CapacityState I) (hf : I.Feasible (fun e => (s.flow e : ℝ)))
    (hstop : s.stopped = true → I.Optimal (fun e => (s.flow e : ℝ))) :
    I.Feasible (fun e => ((s.step solve).value.flow e : ℝ)) ∧
      ((s.step solve).value.stopped = true → I.Optimal (fun e => ((s.step solve).value.flow e : ℝ))) ∧
      2 * (s.step solve).value.objectiveGap target ≤ s.objectiveGap target := by
  by_cases hs : s.stopped = true
  · have hz := gap_zero_of_optimal target s htarget (hstop hs)
    simp only [step, hs, ↓reduceIte]
    exact ⟨hf, fun _ => hstop hs, by rw [hz, mul_zero]⟩
  · have hsfalse := Bool.eq_false_iff.mpr hs
    let R := I.residual s.flow
    let candidate := (polyApproxModel solve R).value
    have hcosts : R.CostsBounded (R.m ^ 10) := I.residual_polynomialCosts s.flow hc
    have hcan := lemma_C_10 solve hsolve R hcosts
    change R.Feasible (fun e => (candidate.flow e : ℝ)) ∧
      R.objective (fun e => (candidate.flow e : ℝ)) = -(candidate.magnitude : ℝ) ∧ _ at hcan
    by_cases hB : candidate.magnitude = 0
    · have hRopt := hcan.2.2.2 hB
      have hRcost : R.objective (fun e => (candidate.flow e : ℝ)) = 0 := by rw [hcan.2.1, hB, Nat.cast_zero, neg_zero]
      have hzero : R.Optimal (fun _ => 0) := by
        refine ⟨R.zero_feasible, ?_⟩
        intro g hg
        have hh := hRopt.2 g hg
        rw [hRcost] at hh
        simpa only [Circulation.objective, mul_zero, Finset.sum_const_zero] using hh
      have hopt := I.optimal_of_zero_residual_optimum s.flow hf hzero
      have hz := gap_zero_of_optimal target s htarget hopt
      have hstep : (s.step solve).value = { s with stopped := true } := by
        simp only [step, hsfalse, Bool.false_eq_true, ↓reduceIte]
        have hb : (polyApproxModel solve (I.residual s.flow)).value.magnitude = 0 := hB
        simp only [hb, ↓reduceIte]
      rw [hstep]
      exact ⟨hf, fun _ => hopt, by change 2 * s.objectiveGap target ≤ _; rw [hz, mul_zero]⟩
    · let delta := (R.solveCapacityRoundedModel solve candidate.magnitude).value
      let next : CapacityState I := ⟨fun e => s.flow e + delta (Fin.castAdd I.m e) - delta (Fin.natAdd I.m e), false⟩
      have hstep : (s.step solve).value = next := by
        simp only [step, hsfalse, Bool.false_eq_true, ↓reduceIte]
        have hb : (polyApproxModel solve (I.residual s.flow)).value.magnitude ≠ 0 := hB
        simp only [hb, ↓reduceIte]
        rfl
      have hcast : (fun e => (next.flow e : ℝ)) = I.augment s.flow (fun e => (delta e : ℝ)) := by
        funext e
        simp only [next, Circulation.augment, Circulation.project, Int.cast_add, Int.cast_sub]
        ring
      have hdopt := R.solveCapacityRoundedModel_optimal solve hsolve candidate.magnitude (Nat.pos_of_ne_zero hB) hcosts
      have hdfeas := R.solveCapacityRoundedModel_feasible solve hsolve candidate.magnitude hcosts
      have hnext : I.Feasible (fun e => (next.flow e : ℝ)) := by
        rw [hcast]
        exact I.augment_feasible s.flow hf _ hdfeas
      let optimum := I.differenceLift s.flow (fun e => (target e : ℝ))
      have hopt : R.Optimal optimum := I.differenceLift_optimal s.flow hf _ htarget
      have hBbound : (candidate.magnitude : ℝ) ≤ -R.objective optimum := by
        have hh := hopt.2 _ hcan.1
        rw [hcan.2.1] at hh
        linarith only [hh]
      have happrox : -R.objective optimum ≤ ((R.m ^ 12 : ℕ) : ℝ) * candidate.magnitude := by
        have hh := hcan.2.2.1 optimum hopt.1
        simp only [neg_mul] at hh
        linarith only [hh]
      have hconst := R.lemma_C_12 candidate.magnitude (by change 0 < I.m + I.m; omega)
        (Nat.pos_of_ne_zero hB) hcosts optimum hopt hBbound happrox delta hdopt
      have hnon : R.objective optimum ≤ 0 := by
        have hh := hopt.2 _ R.zero_feasible
        simpa only [Circulation.objective, mul_zero, Finset.sum_const_zero] using hh
      have hhalf : 2 * R.objective (fun e => (delta e : ℝ)) ≤ R.objective optimum := by
        have hh := hconst.2
        linarith only [hh, hnon]
      have hoptcost : R.objective optimum = I.objective (fun e => (target e : ℝ)) -
          I.objective (fun e => (s.flow e : ℝ)) := I.differenceLift_objective _ _
      have hnewcost : I.objective (fun e => (next.flow e : ℝ)) =
          I.objective (fun e => (s.flow e : ℝ)) + R.objective (fun e => (delta e : ℝ)) := by
        rw [hcast, I.augment_objective]
      have hgap : 2 * next.objectiveGap target ≤ s.objectiveGap target := by
        have hh : (2 : ℝ) * (I.objective (fun e => (next.flow e : ℝ)) - I.objective (fun e => (target e : ℝ))) ≤
            I.objective (fun e => (s.flow e : ℝ)) - I.objective (fun e => (target e : ℝ)) := by
          linarith only [hhalf, hoptcost, hnewcost]
        simp only [objectiveGap]
        rw [← I.integerObjective_cast, ← I.integerObjective_cast, ← I.integerObjective_cast] at hh
        exact_mod_cast hh
      rw [hstep]
      exact ⟨hnext, (by intro h; cases h), hgap⟩

end MinCostFlow.Scaling.CapacityState
