module

public import MinCostFlow.Scaling.CostLoopModel
import Mathlib.Tactic.Ring

/-!
# Polynomial solver inputs in the integer cost loop

The cost-scaling model of Appendix C of Chen et al., arXiv:2203.00671v2,
clips rounded costs between `-B^8` and `B^9`, with `B=2*m`. Thus every call has
costs bounded by its own edge count to the tenth power. This is an unconditional
bound on the model's clipped calls. Correctness later shows that lower clipping leaves the reduced cost unchanged
on the algorithm's states.
-/

@[expose] public section
namespace MinCostFlow.Scaling

private theorem natAbs_le_of_bounds (z : ℤ) (b : ℕ)
    (hl : -(b : ℤ) ≤ z) (hu : z ≤ b) : z.natAbs ≤ b := by omega

/-- Every rounded primal instance satisfies the precise polynomial cost bound
required of the source's solver, measured at its own number of edge slots. -/
theorem CostState.roundedInstance_polynomialCosts {I : Circulation} (C : ℕ)
    (s : CostState I) : (s.roundedInstance C).CostsBounded ((I.m + I.m) ^ 10) := by
  intro e
  have hm : 0 < I.m + I.m := by
    have he : e.val < I.m + I.m := e.isLt
    omega
  have h8 : (I.m + I.m) ^ 8 ≤ (I.m + I.m) ^ 10 :=
    Nat.pow_le_pow_right hm (by decide)
  have h9 : (I.m + I.m) ^ 9 ≤ (I.m + I.m) ^ 10 :=
    Nat.pow_le_pow_right hm (by decide)
  apply natAbs_le_of_bounds
  · exact le_trans (neg_le_neg (Int.ofNat_le.mpr h8)) (le_max_left _ _)
  · apply le_trans _ (Int.ofNat_le.mpr h9)
    apply max_le
    · exact le_trans (neg_nonpos.mpr (Int.natCast_nonneg _)) (Int.natCast_nonneg _)
    · exact min_le_right _ _

/-- The additional dual-extraction call also satisfies its own polynomial
cost bound, since its edge count is no smaller than the primal graph's. -/
theorem Circulation.extractDualModel_polynomialCosts
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) (f : Fin I.m → ℤ)
    (hc : I.CostsBounded (I.m ^ 10)) :
    ∀ J ∈ (I.extractDualModel solve f).calls, J.CostsBounded (J.m ^ 10) := by
  intro J hJ e
  have hcost := I.extractDualModel_costs solve f _ hc J hJ e
  have hedge := I.extractDualModel_edges solve f J hJ
  have hm : I.m ≤ J.m := by omega
  exact le_trans hcost (Nat.pow_le_pow_left hm 10)

/-- Both calls of every cost round have polynomially bounded integral costs. -/
theorem CostState.step_polynomialCosts (solve : (J : Circulation) → Fin J.m → ℤ)
    (C : ℕ) {I : Circulation} (s : CostState I) :
    ∀ J ∈ (CostState.step solve C s).calls, J.CostsBounded (J.m ^ 10) := by
  intro J hJ
  rcases List.mem_cons.mp hJ with hJ | hJ
  · subst J
    exact Circulation.positiveInstance_costsBounded _ _ (s.roundedInstance_polynomialCosts C)
  · exact Circulation.extractDualModel_polynomialCosts solve _ _
      (s.roundedInstance_polynomialCosts C) J hJ

/-- Polynomial cost bounds hold for every recorded cost-loop call, without
assuming optimality or feasibility of its intermediate states. -/
theorem costLoop_polynomialCosts (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) :
    ∀ J ∈ (costLoop solve I C).calls, J.CostsBounded (J.m ^ 10) :=
  CallResult.forRounds_instances (CostState.step solve C) _
    (CostState.step_polynomialCosts solve C) _ _

/-- A round's capacities stay below `max U (n+1)` when its original flow
satisfies the capacity constraints. This states the C.8 capacity increase. -/
theorem CostState.step_capacities (solve : (J : Circulation) → Fin J.m → ℤ)
    (C U : ℕ) (hU : 1 ≤ U) {I : Circulation} (s : CostState I)
    (hf : ∀ e, 0 ≤ (s.flow e : ℝ) ∧ (s.flow e : ℝ) ≤ I.capacity e)
    (hu : ∀ e, I.capacity e ≤ U) :
    ∀ J ∈ (CostState.step solve C s).calls, ∀ e,
      1 ≤ J.capacity e ∧ J.capacity e ≤ max U (I.n + 1) := by
  intro J hJ
  rcases List.mem_cons.mp hJ with hJ | hJ
  · subst J
    apply Circulation.positiveInstance_capacitiesBounded
    · exact le_trans hU (le_max_left _ _)
    · intro e
      have hr := I.residual_capacities_le s.flow hf U hu e
      exact le_trans hr (le_max_left _ _)
  · intro e
    have h := (s.roundedInstance C).extractDualModel_capacities solve _ J hJ e
    exact ⟨h.1, le_trans h.2 (le_max_right _ _)⟩

/-- With nonisolated vertex bound and logarithmic round bound, other work is
at most `10000*m*clog_2(C+1)` counted integer operations. -/
theorem costLoop_work_le_ten_thousand (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) (hm : 0 < I.m) (hn : I.n ≤ 2 * I.m)
    (hC : 0 < C) (hnC : I.n ≤ 2 * C) :
    (costLoop solve I C).work ≤ 10000 * I.m * Nat.clog 2 (C + 1) := by
  have h := costLoop_work solve I C
  have ht := costRounds_le_four_log I.n C hC hnC
  have hb : 600 * (I.m + I.n + 1) + 1 ≤ 2500 * I.m := by omega
  calc
    (costLoop solve I C).work ≤ costRounds I.n C *
        (600 * (I.m + I.n + 1) + 1) := h
    _ ≤ (4 * Nat.clog 2 (C + 1)) * (2500 * I.m) := Nat.mul_le_mul ht hb
    _ = 10000 * I.m * Nat.clog 2 (C + 1) := by ring

end MinCostFlow.Scaling
