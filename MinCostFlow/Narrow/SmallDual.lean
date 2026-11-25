module

public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Scaling.IntegerDualCertificate
import MinCostFlow.Narrow.BitScalingModel
import MinCostFlow.Narrow.DualBoundFreezing
import MinCostFlow.Scaling.DualResidualSigns
import MinCostFlow.Scaling.DualExtractionCorrectness
import MinCostFlow.Scaling.SolverAdapter

/-!
# Dual extraction from small data (Item 5)

This file connects `extractDualFromFlags` — which builds the shortest-routing
subproblem using only the graph topology, small rounded costs, and boolean
residual-presence flags — to `Circulation.extractDualModel`. Using
`bitScaleSolve_residual_pos_iff`, Stage 2's capped residual and capped flow
directly supply the flags. This yields `DualFeasible`, equal primal and dual
objectives, the exact sign conditions for Lemma C.7, the Lemma 4 magnitude
bound `0 ≤ dy v ≤ (J.n - 1) * C_lo`, and the shape/capacity/cost bounds on the
single bounded-solver call `extractDualFromFlagsCall`.
-/

public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling

/-- `extractDualFromFlags` does not depend on `J.capacity`. -/
theorem extractDualFromFlags_indep_capacity (solve : (K : Circulation) → Fin K.m → ℤ)
    (J : Circulation) (cap' : Fin J.m → ℕ) (fwdActive revActive : Fin J.m → Bool) :
    extractDualFromFlags solve { J with capacity := cap' } fwdActive revActive =
      extractDualFromFlags solve J fwdActive revActive := rfl

/-- Under matching residual-presence flags, the capacity functions of the two
shortest-routing graphs are equal. -/
private lemma flagResidualGraph_shortestRoutingGraph_cap_eq (J : Circulation) (f : Fin J.m → ℤ)
    (fwdActive revActive : Fin J.m → Bool)
    (hfwd : ∀ e, fwdActive e = true ↔ 0 < (J.residual f).capacity (Fin.castAdd J.m e))
    (hrev : ∀ e, revActive e = true ↔ 0 < (J.residual f).capacity (Fin.natAdd J.m e)) :
    (flagResidualGraph J fwdActive revActive).shortestRoutingGraph.capacity =
      (J.residual f).shortestRoutingGraph.capacity := by
  funext a
  refine Fin.addCases (m := J.m + J.m) (n := J.n) (fun k => ?_) (fun v => ?_) a
  · simp only [Fin.addCases_left]
    refine Fin.addCases (m := J.m) (n := J.m) (fun e => ?_) (fun e => ?_) k
    · simp only [Fin.addCases_left]
      have hiff : (0 < if fwdActive e = true then 1 else 0) ↔
          0 < ((J.capacity e : ℤ) - f e).toNat := by
        have h1 : (0 < if fwdActive e = true then 1 else 0) ↔ fwdActive e = true := by
          cases fwdActive e <;> simp
        exact h1.trans (by simpa only [Fin.addCases_left] using hfwd e)
      simp only [hiff]
    · simp only [Fin.addCases_right]
      have hiff : (0 < if revActive e = true then 1 else 0) ↔ 0 < (f e).toNat := by
        have h1 : (0 < if revActive e = true then 1 else 0) ↔ revActive e = true := by
          cases revActive e <;> simp
        exact h1.trans (by simpa only [Fin.addCases_right] using hrev e)
      simp only [hiff]
  · simp only [Fin.addCases_right]

/-- When the boolean flags agree with positive residual capacities of `f`, the
flag-based shortest-routing graph equals `(J.residual f).shortestRoutingGraph`. -/
theorem flagResidualGraph_shortestRoutingGraph_eq (J : Circulation) (f : Fin J.m → ℤ)
    (fwdActive revActive : Fin J.m → Bool)
    (hfwd : ∀ e, fwdActive e = true ↔ 0 < (J.residual f).capacity (Fin.castAdd J.m e))
    (hrev : ∀ e, revActive e = true ↔ 0 < (J.residual f).capacity (Fin.natAdd J.m e)) :
    (flagResidualGraph J fwdActive revActive).shortestRoutingGraph =
      (J.residual f).shortestRoutingGraph := by
  have hcap := flagResidualGraph_shortestRoutingGraph_cap_eq J f fwdActive revActive hfwd hrev
  dsimp only [Circulation.shortestRoutingGraph, flagResidualGraph, Circulation.residual] at hcap ⊢
  congr 1

private lemma shortestRouting_call_congr (S₀ : Circulation)
    (c₁ c₂ : Fin S₀.m → ℕ) (hc : c₁ = c₂) (start : Fin S₀.m → ℤ) :
    (({ S₀ with capacity := c₁ } : Circulation).residual start).positiveInstance =
      (({ S₀ with capacity := c₂ } : Circulation).residual start).positiveInstance := by
  subst hc
  rfl

private lemma shortestRouting_labels_congr (solve : (K : Circulation) → Fin K.m → ℤ)
    (S₀ : Circulation)
    (c₁ c₂ : Fin S₀.m → ℕ) (hc : c₁ = c₂) (start : Fin S₀.m → ℤ) (root : Fin S₀.n) :
    let S₁ : Circulation := { S₀ with capacity := c₁ }
    let S₂ : Circulation := { S₀ with capacity := c₂ }
    let d₁ := Circulation.solveWithZeroCapacities solve (S₁.residual start)
    let d₂ := Circulation.solveWithZeroCapacities solve (S₂.residual start)
    let r₁ : Fin S₀.m → ℤ := fun e => start e + d₁ (Fin.castAdd S₀.m e) - d₁ (Fin.natAdd S₀.m e)
    let r₂ : Fin S₀.m → ℤ := fun e => start e + d₂ (Fin.castAdd S₀.m e) - d₂ (Fin.natAdd S₀.m e)
    (S₁.propagateLabels r₁ root).1.labels = (S₂.propagateLabels r₂ root).1.labels := by
  subst hc
  rfl

/-- Under matching residual-presence flags, the single positive-capacity call
made by `extractDualFromFlags` equals the call made by `J.extractDualModel`. -/
theorem extractDualFromFlagsCall_eq (J : Circulation) (f : Fin J.m → ℤ)
    (fwdActive revActive : Fin J.m → Bool)
    (hfwd : ∀ e, fwdActive e = true ↔ 0 < (J.residual f).capacity (Fin.castAdd J.m e))
    (hrev : ∀ e, revActive e = true ↔ 0 < (J.residual f).capacity (Fin.natAdd J.m e)) :
    extractDualFromFlagsCall J fwdActive revActive =
      (((J.residual f).shortestRoutingGraph).residual
        ((J.residual f).shortestRoutingStart)).positiveInstance := by
  have hcap := flagResidualGraph_shortestRoutingGraph_cap_eq J f fwdActive revActive hfwd hrev
  exact shortestRouting_call_congr (J.residual f).shortestRoutingGraph _ _ hcap
    (J.residual f).shortestRoutingStart

/-- Under matching residual-presence flags, `extractDualFromFlags` returns the
exact same potential as `J.extractDualModel`. -/
theorem extractDualFromFlags_eq_extractDualModel
    (solve : (K : Circulation) → Fin K.m → ℤ) (J : Circulation) (f : Fin J.m → ℤ)
    (fwdActive revActive : Fin J.m → Bool)
    (hfwd : ∀ e, fwdActive e = true ↔ 0 < (J.residual f).capacity (Fin.castAdd J.m e))
    (hrev : ∀ e, revActive e = true ↔ 0 < (J.residual f).capacity (Fin.natAdd J.m e)) :
    extractDualFromFlags solve J fwdActive revActive =
      (J.extractDualModel solve f).value := by
  have hcap := flagResidualGraph_shortestRoutingGraph_cap_eq J f fwdActive revActive hfwd hrev
  have hlab := shortestRouting_labels_congr solve (J.residual f).shortestRoutingGraph
    _ _ hcap (J.residual f).shortestRoutingStart (Fin.last J.n)
  funext v
  exact congrFun hlab v.castSucc

/-- Connecting Stage 2's capped residual and capped flow to `extractDualFromFlags`
via `bitScaleSolve_residual_pos_iff`. -/
theorem extractDualFromFlags_bitScale_eq
    (solve solve' : (K : Circulation) → Fin K.m → ℤ) (J : Circulation) :
    let f := bitScaleSolve solve' J
    let fwdActive : Fin J.m → Bool := fun e =>
      decide (0 < cappedResidual J (bitScalingPhases J) (bitScalingPhases J) f (J.m + 1) e)
    let revActive : Fin J.m → Bool := fun e =>
      decide (0 < cappedFlow f (J.m + 1) e)
    extractDualFromFlags solve J fwdActive revActive =
        (J.extractDualModel solve f).value ∧
      extractDualFromFlagsCall J fwdActive revActive =
        (((J.residual f).shortestRoutingGraph).residual
          ((J.residual f).shortestRoutingStart)).positiveInstance := by
  intro f fwdActive revActive
  have hfwd : ∀ e, fwdActive e = true ↔ 0 < (J.residual f).capacity (Fin.castAdd J.m e) := by
    intro e
    dsimp only [fwdActive]
    rw [decide_eq_true_eq]
    exact (bitScaleSolve_residual_pos_iff solve' J e).1
  have hrev : ∀ e, revActive e = true ↔ 0 < (J.residual f).capacity (Fin.natAdd J.m e) := by
    intro e
    dsimp only [revActive]
    rw [decide_eq_true_eq]
    exact (bitScaleSolve_residual_pos_iff solve' J e).2
  exact ⟨extractDualFromFlags_eq_extractDualModel solve J f fwdActive revActive hfwd hrev,
    extractDualFromFlagsCall_eq J f fwdActive revActive hfwd hrev⟩

/-- Correctness of `extractDualFromFlags`: supplies the residual potential
inequalities, `DualFeasible`, equal primal/dual objectives, and the
complementary-slackness sign conditions needed by
`epsilonOptimalWith_augment_of_rounded_signs`. -/
theorem extractDualFromFlags_correct
    (solve : (K : Circulation) → Fin K.m → ℤ) (J : Circulation) (f : Fin J.m → ℤ)
    (fwdActive revActive : Fin J.m → Bool)
    (hfwd : ∀ e, fwdActive e = true ↔ 0 < (J.residual f).capacity (Fin.castAdd J.m e))
    (hrev : ∀ e, revActive e = true ↔ 0 < (J.residual f).capacity (Fin.natAdd J.m e))
    (hf : J.Optimal (fun e => (f e : ℝ)))
    (hcall : (extractDualFromFlagsCall J fwdActive revActive).Optimal
      (fun a => (solve (extractDualFromFlagsCall J fwdActive revActive) a : ℝ))) :
    (∀ a, 0 < (J.residual f).capacity a →
      extractDualFromFlags solve J fwdActive revActive ((J.residual f).tail a) -
        extractDualFromFlags solve J fwdActive revActive ((J.residual f).head a) ≤
        (J.residual f).cost a) ∧
    J.DualFeasible (fun v => (extractDualFromFlags solve J fwdActive revActive v : ℝ))
      (fun e => (J.integerLowerSlack (extractDualFromFlags solve J fwdActive revActive) e : ℝ))
      (fun e => (J.integerUpperSlack (extractDualFromFlags solve J fwdActive revActive) e : ℝ)) ∧
    J.objective (fun e => (f e : ℝ)) =
      J.dualObjective
        (fun e => (J.integerUpperSlack (extractDualFromFlags solve J fwdActive revActive) e : ℝ)) ∧
    ∀ e,
      ((f e : ℝ) < J.capacity e →
        0 ≤ (J.cost e : ℝ) -
          J.potentialDifference (fun v => (extractDualFromFlags solve J fwdActive revActive v : ℝ)) e) ∧
      (0 < (f e : ℝ) →
        (J.cost e : ℝ) -
          J.potentialDifference (fun v => (extractDualFromFlags solve J fwdActive revActive v : ℝ)) e ≤ 0) := by
  have heq := extractDualFromFlags_eq_extractDualModel solve J f fwdActive revActive hfwd hrev
  have hceq := extractDualFromFlagsCall_eq J f fwdActive revActive hfwd hrev
  rw [heq]
  have hQ : ((J.residual f).shortestRoutingGraph.residual
      (J.residual f).shortestRoutingStart).Optimal
      (fun a => (Circulation.solveWithZeroCapacities solve
        ((J.residual f).shortestRoutingGraph.residual
          (J.residual f).shortestRoutingStart) a : ℝ)) := by
    apply Circulation.solveWithZeroCapacities_of_optimal
    rw [← hceq]
    exact hcall
  have hy := J.extractDualModel_correct_of_optimal solve f hf hQ
  have hcert := J.integerSlacks_certificate f hf.1 (J.extractDualModel solve f).value hy
  have hsigns := J.residual_signs_of_dual_equality (fun e => (f e : ℝ))
    (fun v => ((J.extractDualModel solve f).value v : ℝ)) _ _ hf.1 hcert.1 hcert.2
  exact ⟨hy, hcert.1, hcert.2, hsigns⟩

/-- Magnitude bound on `extractDualFromFlags`: `0 ≤ dy v ≤ (J.n - 1) * C_lo`. -/
theorem extractDualFromFlags_bounds
    (solve : (K : Circulation) → Fin K.m → ℤ) (J : Circulation) (C_lo : ℕ)
    (hC : ∀ e, -(C_lo : ℤ) ≤ J.cost e) (f : Fin J.m → ℤ)
    (fwdActive revActive : Fin J.m → Bool)
    (hfwd : ∀ e, fwdActive e = true ↔ 0 < (J.residual f).capacity (Fin.castAdd J.m e))
    (hrev : ∀ e, revActive e = true ↔ 0 < (J.residual f).capacity (Fin.natAdd J.m e))
    (hf : J.Optimal (fun e => (f e : ℝ)))
    (hcall : (extractDualFromFlagsCall J fwdActive revActive).Optimal
      (fun a => (solve (extractDualFromFlagsCall J fwdActive revActive) a : ℝ))) :
    ∀ v : Fin J.n,
      0 ≤ extractDualFromFlags solve J fwdActive revActive v ∧
      extractDualFromFlags solve J fwdActive revActive v ≤
        ((J.n - 1 : ℕ) : ℤ) * (C_lo : ℤ) := by
  have heq := extractDualFromFlags_eq_extractDualModel solve J f fwdActive revActive hfwd hrev
  have hceq := extractDualFromFlagsCall_eq J f fwdActive revActive hfwd hrev
  rw [heq]
  have hQ : ((J.residual f).shortestRoutingGraph.residual
      (J.residual f).shortestRoutingStart).Optimal
      (fun a => (Circulation.solveWithZeroCapacities solve
        ((J.residual f).shortestRoutingGraph.residual
          (J.residual f).shortestRoutingStart) a : ℝ)) := by
    apply Circulation.solveWithZeroCapacities_of_optimal
    rw [← hceq]
    exact hcall
  exact extractDualModel_bounds solve J C_lo hC f hf hQ

/-- Geometry, capacity bounds (`1 ≤ cap ≤ J.n + 1`), and cost bound of the
single solver call `extractDualFromFlagsCall`. -/
theorem extractDualFromFlagsCall_shape (J : Circulation)
    (fwdActive revActive : Fin J.m → Bool) (C : ℕ) (hc : J.CostsBounded C) :
    (extractDualFromFlagsCall J fwdActive revActive).n = J.n + 2 ∧
    (extractDualFromFlagsCall J fwdActive revActive).m = 4 * J.m + 2 * J.n ∧
    (∀ a, 1 ≤ (extractDualFromFlagsCall J fwdActive revActive).capacity a ∧
      (extractDualFromFlagsCall J fwdActive revActive).capacity a ≤ J.n + 1) ∧
    (extractDualFromFlagsCall J fwdActive revActive).CostsBounded C := by
  let R := flagResidualGraph J fwdActive revActive
  have hR_costs : R.CostsBounded C := by
    intro a
    refine Fin.addCases (m := J.m) (n := J.m) (fun e => ?_) (fun e => ?_) a
    · simpa only [R, flagResidualGraph, Fin.addCases_left] using hc e
    · simpa only [R, flagResidualGraph, Fin.addCases_right, Int.natAbs_neg] using hc e
  refine ⟨rfl, ?_, ?_, ?_⟩
  · change (J.m + J.m + J.n) + (J.m + J.m + J.n) = 4 * J.m + 2 * J.n
    omega
  · apply Circulation.positiveInstance_capacitiesBounded
    · exact Nat.succ_le_succ (Nat.zero_le J.n)
    · apply Circulation.residual_capacities_le
      · exact R.shortestRoutingStart_bounds
      · exact R.shortestRoutingGraph_capacities
  · apply Circulation.positiveInstance_costsBounded
    apply Circulation.residual_costsBounded
    apply Circulation.shortestRoutingGraph_costsBounded
    exact hR_costs

end MinCostFlow.Narrow
