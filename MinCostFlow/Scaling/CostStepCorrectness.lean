module

public import MinCostFlow.Scaling.CostStepInterpretation
public import MinCostFlow.Scaling.CostRoundProgress
public import MinCostFlow.Scaling.CostLoopFeasibility
public import MinCostFlow.Scaling.IntegerDualCertificate

/-!
# Correctness of an executed cost-scaling step

The proof of Lemma C.3 of Chen et al., arXiv:2203.00671v2, Appendix C,
uses Lemma C.7 with the dual actually computed by Lemma C.8. Here both
calls are justified using only their own polynomial cost and bounded
capacity specification. Their returned vectors provide the equal-value dual
certificate required by the progress theorem. The encoded update then
preserves epsilon optimality with half the represented epsilon.
-/

@[expose] public section
namespace MinCostFlow.Scaling.CostState
variable {I : Circulation}

/-- One actual cost step preserves the epsilon-optimal state invariant,
using only the bounded primal solver specified in Lemma C.3. -/
theorem step_epsilonOptimalWith
    (solve : (J : Circulation) → Fin J.m → ℤ) (C U : ℕ) (hU : 1 ≤ U)
    (hm : 0 < I.m) (hn : I.n ≤ I.m + I.m)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ max U (I.n + 1)) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (hu : ∀ e, I.capacity e ≤ U) (s : CostState I) (hp : 0 < s.power)
    (hopt : I.EpsilonOptimalWith (fun e => (s.flow e : ℝ)) (s.epsilon C)
      (realPotential (I := I) C s)) :
    I.EpsilonOptimalWith (fun e => ((s.step solve C).value.flow e : ℝ))
      ((s.step solve C).value.epsilon C)
      (realPotential (I := I) C (s.step solve C).value) := by
  let J := s.roundedInstance C
  let delta := Circulation.solveWithZeroCapacities solve J
  let dy := J.extractDualModel solve delta
  have hcosts := s.step_polynomialCosts solve C
  have hcaps := s.step_capacities solve C U hU hopt.2.1.2 hu
  have hmem : J.positiveInstance ∈ (s.step solve C).calls := List.mem_cons_self
  have hdelta : J.Optimal (fun e => (delta e : ℝ)) := by
    apply Circulation.solveWithZeroCapacities_of_optimal
    exact hsolve J.positiveInstance (hcosts _ hmem) (hcaps _ hmem)
  let R := J.residual delta
  let Q := R.shortestRoutingGraph.residual R.shortestRoutingStart
  have hmemQ : Q.positiveInstance ∈ (s.step solve C).calls := by
    apply List.mem_cons_of_mem
    change Q.positiveInstance ∈ [Q.positiveInstance]
    exact List.mem_cons_self
  have hQ : Q.Optimal (fun e => (Circulation.solveWithZeroCapacities solve Q e : ℝ)) := by
    apply Circulation.solveWithZeroCapacities_of_optimal
    exact hsolve Q.positiveInstance (hcosts _ hmemQ) (hcaps _ hmemQ)
  have hy := J.extractDualModel_correct_of_optimal solve delta hdelta hQ
  have hcert := J.integerSlacks_certificate delta hdelta.1 dy.value hy
  rw [s.step_flow_cast solve C, s.step_epsilon solve C]
  have hpotential : realPotential (I := I) C (s.step solve C).value =
      fun v => realPotential (I := I) C s v + s.roundingUnit C * (dy.value v : ℝ) := by
    funext v
    exact s.step_realPotential solve C v
  rw [hpotential]
  exact s.lemma_C_7 C hm hn hp hopt delta hdelta (fun v => (dy.value v : ℝ))
    (fun e => (J.integerLowerSlack dy.value e : ℝ))
    (fun e => (J.integerUpperSlack dy.value e : ℝ)) hcert.1 hcert.2

end MinCostFlow.Scaling.CostState
