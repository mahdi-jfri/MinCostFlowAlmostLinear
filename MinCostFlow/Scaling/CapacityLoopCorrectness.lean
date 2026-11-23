module

public import MinCostFlow.Scaling.CapacityStepCorrectness
public import MinCostFlow.Scaling.CapacityIntegralOptimum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The integral gap at the end of capacity scaling

In Lemma C.9 of Chen et al., arXiv:2203.00671v2, Appendix C, the initial
objective gap is at most `m^11 U`. Each executed round halves it. The explicit
round budget makes any remaining positive integer gap impossible.
-/

public section
namespace MinCostFlow.Scaling

/-- The initial objective bound in the proof of Lemma C.9. -/
theorem Circulation.integerObjective_lower (I : Circulation) (U : ℕ)
    (hc : I.CostsBounded (I.m ^ 10)) (hu : ∀ e, I.capacity e ≤ U)
    (f : Fin I.m → ℤ) (hf : I.Feasible (fun e => (f e : ℝ))) :
    -((I.m ^ 11 * U : ℕ) : ℤ) ≤ I.integerObjective f := by
  have he (e : Fin I.m) : -((I.m ^ 10 * U : ℕ) : ℤ) ≤ I.cost e * f e := by
    have hcost : -((I.m ^ 10 : ℕ) : ℤ) ≤ I.cost e := by
      have hh := Int.natCast_natAbs (I.cost e)
      have hb := hc e
      have ha := neg_abs_le (I.cost e)
      omega
    have hn : 0 ≤ f e := Int.cast_nonneg_iff.mp (hf.2 e).1
    have hb : f e ≤ (U : ℤ) := by
      have hh := le_trans (hf.2 e).2 (Nat.cast_le.mpr (hu e))
      change (f e : ℝ) ≤ (U : ℝ) at hh
      exact_mod_cast hh
    have h1 := mul_le_mul_of_nonneg_right hcost hn
    have h2 := mul_le_mul_of_nonpos_left hb (neg_nonpos.mpr (Nat.cast_nonneg (I.m ^ 10) : (0 : ℤ) ≤ _))
    simp only [Nat.cast_mul, neg_mul] at h1 h2 ⊢
    exact h2.trans h1
  have hh := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => he e)
  have hid : (∑ _ : Fin I.m, -((I.m ^ 10 * U : ℕ) : ℤ)) = -((I.m ^ 11 * U : ℕ) : ℤ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_mul, Nat.cast_pow]
    ring
  rw [hid] at hh
  exact hh

/-- Feasibility, the stop certificate, and the scaled gap hold after every
prefix of the actual finite loop. -/
theorem capacityLoop_prefix_gap
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (hc : I.CostsBounded (I.m ^ 10)) (hm : 0 < I.m)
    (target : Fin I.m → ℤ) (ht : I.Optimal (fun e => (target e : ℝ))) (t : ℕ) :
    let s := (CallResult.forRounds (CapacityState.step solve) t (CapacityState.initial I)).value
    I.Feasible (fun e => (s.flow e : ℝ)) ∧
      (s.stopped = true → I.Optimal (fun e => (s.flow e : ℝ))) ∧
      (2 ^ t : ℤ) * s.objectiveGap target ≤ -(I.integerObjective target) := by
  induction t with
  | zero =>
    refine ⟨?_, (by intro h; cases h), ?_⟩
    · simpa only [CallResult.forRounds, CallResult.pure, CapacityState.initial, Int.cast_zero] using I.zero_feasible
    · simp only [pow_zero, one_mul, CapacityState.objectiveGap, CapacityState.initial,
      Circulation.integerObjective, mul_zero, Finset.sum_const_zero, zero_sub,
      CallResult.forRounds, CallResult.pure]
      exact le_rfl
  | succ t ih =>
    dsimp only at ih
    have hs := CapacityState.step_gap solve hsolve hc hm target ht _ ih.1 ih.2.1
    refine ⟨hs.1, hs.2.1, ?_⟩
    have hh := mul_le_mul_of_nonneg_left hs.2.2 (by positivity : (0 : ℤ) ≤ 2 ^ t)
    change (2 ^ (t+1) : ℤ) * _ ≤ _
    rw [pow_succ, mul_assoc]
    exact hh.trans ih.2.2

/-- The finite capacity-scaling loop returns an integral exact optimum,
as concluded in the proof of Lemma C.9. -/
theorem capacityLoop_optimal
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (U : ℕ) (hc : I.CostsBounded (I.m ^ 10))
    (hm : 0 < I.m) (hu : ∀ e, I.capacity e ≤ U) :
    I.Optimal (fun e => ((capacityLoop solve I U).value.flow e : ℝ)) := by
  obtain ⟨target, ht⟩ := I.exists_integral_optimum_of_bounded_solver solve hsolve hc
  let s := (capacityLoop solve I U).value
  have hs := capacityLoop_prefix_gap solve hsolve I hc hm target ht (capacityRounds I.m U)
  change I.Feasible (fun e => (s.flow e : ℝ)) ∧ _ at hs
  change I.Feasible (fun e => (s.flow e : ℝ)) ∧
    (s.stopped = true → I.Optimal (fun e => (s.flow e : ℝ))) ∧
    (2 ^ capacityRounds I.m U : ℤ) * s.objectiveGap target ≤ -I.integerObjective target at hs
  have hbound := I.integerObjective_lower U hc hu target ht.1
  have hgap : s.objectiveGap target ≤ 0 := by
    by_contra hn
    have hpos : 1 ≤ s.objectiveGap target := by omega
    have hh := mul_le_mul_of_nonneg_left hpos (by positivity : (0 : ℤ) ≤ 2 ^ capacityRounds I.m U)
    rw [mul_one] at hh
    have hstop := capacityRounds_stopping I.m U
    have hsmall : I.m ^ 11 * U < 2 ^ capacityRounds I.m U :=
      lt_of_le_of_lt (by rw [Nat.mul_assoc]; omega : I.m ^ 11 * U ≤ 2 * I.m ^ 11 * U) hstop
    have hsmall' : ((I.m ^ 11 * U : ℕ) : ℤ) < 2 ^ capacityRounds I.m U := by exact_mod_cast hsmall
    omega
  refine ⟨hs.1, ?_⟩
  intro g hg
  have hh : I.integerObjective s.flow ≤ I.integerObjective target := sub_nonpos.mp hgap
  have hr := (Int.cast_le (R := ℝ)).mpr hh
  rw [I.integerObjective_cast, I.integerObjective_cast] at hr
  exact hr.trans (ht.2 g hg)

end MinCostFlow.Scaling
