module

public import MinCostFlow.Narrow.Defs
import MinCostFlow.Narrow.CappedRecurrence
import MinCostFlow.Narrow.CappedPhase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bit-scaling model specification and correctness

This file states and proves `BitScalingGoal`, the correctness, call-structure,
capped-recurrence, residual-readout, and shifted-accumulator theorems for the
Stage 2 bit-scaling model `bitScaleSolve`.
-/

@[expose] public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling

/-- The combined specification of the bit-scaling model `bitScaleSolve`:
1. Optimality of `bitScaleSolve solve I` whenever `solve` returns an integral
   optimum on every phase call in `bitScaleModelCalls solve I`.
2. Call count `bitScalingPhases I` and phase-instance shape (vertices of `I`,
   `2 * I.m` slots, capacities at most `I.m + 1`, forward/reverse costs
   `I.cost e` and `-I.cost e`).
3. Phase-by-phase capped capacities and capped residual/flow recurrences at
   cap `M = I.m + 1`.
4. Exact residual-positivity readout from the final capped residual and flow.
5. Shifted-accumulator representation of the final flow `bitScaleSolve solve I`. -/
def BitScalingGoal : Prop :=
  (∀ (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation),
    (∀ J ∈ bitScaleModelCalls solve I, J.Optimal (fun a => (solve J a : ℝ))) →
    I.Optimal (fun e => (bitScaleSolve solve I e : ℝ))) ∧
  (∀ (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation),
    (bitScaleModelCalls solve I).length = bitScalingPhases I ∧
    ∀ t < bitScalingPhases I,
      (bitScalePhaseCall solve I (bitScalingPhases I) t).n = I.n ∧
      (bitScalePhaseCall solve I (bitScalingPhases I) t).m = 2 * I.m ∧
      (∀ a, (bitScalePhaseCall solve I (bitScalingPhases I) t).capacity a ≤ I.m + 1) ∧
      ∀ e, (bitScalePhaseCall solve I (bitScalingPhases I) t).cost (Fin.castAdd I.m e) = I.cost e ∧
           (bitScalePhaseCall solve I (bitScalingPhases I) t).cost (Fin.natAdd I.m e) = -I.cost e) ∧
  (∀ (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation),
    (∀ J ∈ bitScaleModelCalls solve I, J.Optimal (fun a => (solve J a : ℝ))) →
    ∀ t < bitScalingPhases I, ∀ e : Fin I.m,
      (bitScalePhaseCall solve I (bitScalingPhases I) t).capacity (Fin.castAdd I.m e) =
        min (2 * cappedResidual I (bitScalingPhases I) t
              (bitScaleFlow solve I (bitScalingPhases I) t) (I.m + 1) e +
            capBit I (bitScalingPhases I - (t + 1)) e) (I.m + 1) ∧
      (bitScalePhaseCall solve I (bitScalingPhases I) t).capacity (Fin.natAdd I.m e) =
        min (2 * cappedFlow (bitScaleFlow solve I (bitScalingPhases I) t) (I.m + 1) e)
          (I.m + 1) ∧
      0 ≤ bitScaleDelta solve I (bitScalingPhases I) t (Fin.castAdd I.m e) ∧
      (bitScaleDelta solve I (bitScalingPhases I) t (Fin.castAdd I.m e)).toNat ≤
        min (2 * cappedResidual I (bitScalingPhases I) t
              (bitScaleFlow solve I (bitScalingPhases I) t) (I.m + 1) e +
            capBit I (bitScalingPhases I - (t + 1)) e) (I.m + 1) ∧
      0 ≤ bitScaleDelta solve I (bitScalingPhases I) t (Fin.natAdd I.m e) ∧
      (bitScaleDelta solve I (bitScalingPhases I) t (Fin.natAdd I.m e)).toNat ≤
        min (2 * cappedFlow (bitScaleFlow solve I (bitScalingPhases I) t) (I.m + 1) e)
          (I.m + 1) ∧
      cappedResidual I (bitScalingPhases I) (t + 1)
          (bitScaleFlow solve I (bitScalingPhases I) (t + 1)) (I.m + 1) e =
        min (2 * cappedResidual I (bitScalingPhases I) t
              (bitScaleFlow solve I (bitScalingPhases I) t) (I.m + 1) e +
            capBit I (bitScalingPhases I - (t + 1)) e +
            (bitScaleDelta solve I (bitScalingPhases I) t (Fin.natAdd I.m e)).toNat -
            (bitScaleDelta solve I (bitScalingPhases I) t (Fin.castAdd I.m e)).toNat)
          (I.m + 1) ∧
      cappedFlow (bitScaleFlow solve I (bitScalingPhases I) (t + 1)) (I.m + 1) e =
        min (2 * cappedFlow (bitScaleFlow solve I (bitScalingPhases I) t) (I.m + 1) e +
            (bitScaleDelta solve I (bitScalingPhases I) t (Fin.castAdd I.m e)).toNat -
            (bitScaleDelta solve I (bitScalingPhases I) t (Fin.natAdd I.m e)).toNat)
          (I.m + 1)) ∧
  (∀ (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation),
    (∀ J ∈ bitScaleModelCalls solve I, J.Optimal (fun a => (solve J a : ℝ))) →
    ∀ e : Fin I.m,
      (0 < cappedResidual I (bitScalingPhases I) (bitScalingPhases I)
            (bitScaleSolve solve I) (I.m + 1) e ↔
          0 < (I.residual (bitScaleSolve solve I)).capacity (Fin.castAdd I.m e)) ∧
      (0 < cappedFlow (bitScaleSolve solve I) (I.m + 1) e ↔
          0 < (I.residual (bitScaleSolve solve I)).capacity (Fin.natAdd I.m e))) ∧
  (∀ (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) (e : Fin I.m),
    bitScaleSolve solve I e =
      ∑ j ∈ Finset.range (bitScalingPhases I),
        intProject I.m (bitScaleDelta solve I (bitScalingPhases I) j) e *
          (2 : ℤ) ^ (bitScalingPhases I - 1 - j))

/-- Replacing an instance's capacity function by an extensionally equal one
preserves optimality. -/
private lemma optimal_of_capacity_eq (I : Circulation) (c₁ c₂ : Fin I.m → ℕ)
    (hc : ∀ e, c₁ e = c₂ e) (f : Fin I.m → ℝ)
    (h : ({ I with capacity := c₁ } : Circulation).Optimal f) :
    ({ I with capacity := c₂ } : Circulation).Optimal f := by
  have hcap : c₁ = c₂ := funext hc
  subst hcap
  exact h

/-- Truncating by shift `0` recovers the original circulation instance. -/
theorem truncInstance_zero (I : Circulation) : truncInstance I 0 = I := by
  cases I
  simp only [truncInstance, pow_zero, Nat.div_one]

/-- Doubling `truncInstance I k` with bit `k - 1` yields `truncInstance I (k - 1)`. -/
theorem truncInstance_doubled (I : Circulation) (k : ℕ) (hk : 1 ≤ k) :
    doubled (truncInstance I k) (capBit I (k - 1)) = truncInstance I (k - 1) := by
  cases I
  dsimp only [doubled, truncInstance, capBit]
  congr 1
  funext e
  exact (div_two_pow_sub_one _ k hk).symm

/-- Every edge capacity is strictly less than `2 ^ bitScalingPhases I`. -/
theorem capacity_lt_two_pow_bitScalingPhases (I : Circulation) (e : Fin I.m) :
    I.capacity e < 2 ^ bitScalingPhases I :=
  lt_of_le_of_lt (Finset.le_sup (f := I.capacity) (Finset.mem_univ e))
    (Nat.lt_size_self (circMaxCapacity I))

/-- When every capacity is strictly less than `2 ^ T`, the zero flow is optimal
for `truncInstance I T`. -/
theorem truncInstance_zero_optimal (I : Circulation) (T : ℕ)
    (hT : ∀ e, I.capacity e < 2 ^ T) :
    (truncInstance I T).Optimal (fun _ => 0) := by
  refine ⟨(truncInstance I T).zero_feasible, fun f hf => ?_⟩
  have hf0 : f = fun _ => 0 := by
    funext e
    have hcap0 : I.capacity e / 2 ^ T = 0 := Nat.div_eq_of_lt (hT e)
    have hle : f e ≤ 0 := by
      have h2 := (hf.2 e).2
      change f e ≤ ((I.capacity e / 2 ^ T : ℕ) : ℝ) at h2
      simpa only [hcap0, Nat.cast_zero] using h2
    exact le_antisymm hle (hf.2 e).1
  rw [hf0]

/-- Phase invariant: after `t ≤ T` phases, `bitScaleFlow solve I T t` is an
integral optimum of `truncInstance I (T - t)`. -/
theorem bitScaleFlow_optimal_step (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (T : ℕ) (hT : ∀ e, I.capacity e < 2 ^ T)
    (hsolve : ∀ t < T, (bitScalePhaseCall solve I T t).Optimal
      (fun a => (bitScaleDelta solve I T t a : ℝ))) :
    ∀ t ≤ T, (truncInstance I (T - t)).Optimal
      (fun e => (bitScaleFlow solve I T t e : ℝ)) := by
  intro t ht
  induction t with
  | zero =>
    simpa only [Nat.sub_zero, bitScaleFlow, Int.cast_zero] using
      truncInstance_zero_optimal I T hT
  | succ t ih =>
    have hprev := ih (Nat.le_of_succ_le ht)
    have hcall := hsolve t (Nat.lt_of_succ_le ht)
    have hb : ∀ e, capBit I (T - (t + 1)) e ≤ 1 := fun e => by
      dsimp only [capBit]
      omega
    have hk : 1 ≤ T - t := by omega
    have hsub : T - t - 1 = T - (t + 1) := by omega
    have hopt := augment_phaseInstance_optimal (truncInstance I (T - t))
      (capBit I (T - (t + 1))) hb (bitScaleFlow solve I T t) hprev
      (I.m + 1) (Nat.le_succ I.m) (bitScaleDelta solve I T t) hcall
    refine optimal_of_capacity_eq I _ _ (fun e => ?_) _ hopt
    have hdiv := div_two_pow_sub_one (I.capacity e) (T - t) hk
    rw [hsub] at hdiv
    exact hdiv.symm

/-- Correctness of Stage 2 from optimality on its actual phase calls: if `solve`
returns an integral optimum on every instance in `bitScaleModelCalls solve I`,
then `bitScaleSolve solve I` is an integral optimum of `I`. -/
theorem bitScaleSolve_optimal_of_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation)
    (hsolve : ∀ J ∈ bitScaleModelCalls solve I, J.Optimal (fun a => (solve J a : ℝ))) :
    I.Optimal (fun e => (bitScaleSolve solve I e : ℝ)) := by
  have hstep : ∀ t < bitScalingPhases I,
      (bitScalePhaseCall solve I (bitScalingPhases I) t).Optimal
        (fun a => (bitScaleDelta solve I (bitScalingPhases I) t a : ℝ)) := by
    intro t ht
    exact hsolve _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
  have hfinal := bitScaleFlow_optimal_step solve I (bitScalingPhases I)
    (capacity_lt_two_pow_bitScalingPhases I) hstep (bitScalingPhases I) le_rfl
  rw [Nat.sub_self] at hfinal
  exact optimal_of_capacity_eq I _ I.capacity (fun e => div_two_pow_zero (I.capacity e)) _ hfinal

/-- Correctness of Stage 2 for any exact circulation solver: every `Circulation`
is feasible (via the zero flow), so if `solve J` is an optimum for every
circulation `J`, then `bitScaleSolve solve I` is an integral optimum of `I`. -/
theorem bitScaleSolve_optimal (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation)
    (hsolve : ∀ J : Circulation, J.Optimal (fun a => (solve J a : ℝ))) :
    I.Optimal (fun e => (bitScaleSolve solve I e : ℝ)) :=
  bitScaleSolve_optimal_of_calls solve I (fun J _ => hsolve J)

/-- Stage 2 makes exactly `bitScalingPhases I` solver calls. -/
theorem bitScaleModelCalls_length (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) :
    (bitScaleModelCalls solve I).length = bitScalingPhases I := by
  simp [bitScaleModelCalls, bitScaleCalls]

/-- Every phase instance has the vertices of `I`, `2 * I.m` slots, capacities at
most `I.m + 1`, and forward/reverse costs `I.cost e` and `-I.cost e`. -/
theorem bitScalePhaseCall_shape (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (T t : ℕ) :
    (bitScalePhaseCall solve I T t).n = I.n ∧
    (bitScalePhaseCall solve I T t).m = 2 * I.m ∧
    (∀ a, (bitScalePhaseCall solve I T t).capacity a ≤ I.m + 1) ∧
    ∀ e, (bitScalePhaseCall solve I T t).cost (Fin.castAdd I.m e) = I.cost e ∧
         (bitScalePhaseCall solve I T t).cost (Fin.natAdd I.m e) = -I.cost e := by
  refine ⟨rfl, ?_, fun a => Nat.min_le_right _ _, fun e => ?_⟩
  · change I.m + I.m = 2 * I.m
    omega
  · simp only [Fin.addCases_left, Fin.addCases_right, and_self]

/-- Every phase call in `bitScaleModelCalls solve I` inherits any cost bound
`I.CostsBounded C`. -/
theorem bitScaleModelCalls_costsBounded (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) (hc : ∀ e, (I.cost e).natAbs ≤ C) :
    ∀ J ∈ bitScaleModelCalls solve I, ∀ a, (J.cost a).natAbs ≤ C := by
  intro J hJ a
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hJ
  refine Fin.addCases (m := I.m) (n := I.m) (fun e => ?_) (fun e => ?_) a
  · simpa only [Fin.addCases_left] using hc e
  · simpa only [Fin.addCases_right, Int.natAbs_neg] using hc e

/-- Phase-by-phase capped capacities, delta bounds, and capped residual/flow
recurrences at cap `M = I.m + 1`. -/
theorem bitScalePhase_capped_recurrences (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation)
    (hsolve : ∀ J ∈ bitScaleModelCalls solve I, J.Optimal (fun a => (solve J a : ℝ)))
    (t : ℕ) (ht : t < bitScalingPhases I) (e : Fin I.m) :
    (bitScalePhaseCall solve I (bitScalingPhases I) t).capacity (Fin.castAdd I.m e) =
      min (2 * cappedResidual I (bitScalingPhases I) t
            (bitScaleFlow solve I (bitScalingPhases I) t) (I.m + 1) e +
          capBit I (bitScalingPhases I - (t + 1)) e) (I.m + 1) ∧
    (bitScalePhaseCall solve I (bitScalingPhases I) t).capacity (Fin.natAdd I.m e) =
      min (2 * cappedFlow (bitScaleFlow solve I (bitScalingPhases I) t) (I.m + 1) e)
        (I.m + 1) ∧
    0 ≤ bitScaleDelta solve I (bitScalingPhases I) t (Fin.castAdd I.m e) ∧
    (bitScaleDelta solve I (bitScalingPhases I) t (Fin.castAdd I.m e)).toNat ≤
      min (2 * cappedResidual I (bitScalingPhases I) t
            (bitScaleFlow solve I (bitScalingPhases I) t) (I.m + 1) e +
          capBit I (bitScalingPhases I - (t + 1)) e) (I.m + 1) ∧
    0 ≤ bitScaleDelta solve I (bitScalingPhases I) t (Fin.natAdd I.m e) ∧
    (bitScaleDelta solve I (bitScalingPhases I) t (Fin.natAdd I.m e)).toNat ≤
      min (2 * cappedFlow (bitScaleFlow solve I (bitScalingPhases I) t) (I.m + 1) e)
        (I.m + 1) ∧
    cappedResidual I (bitScalingPhases I) (t + 1)
        (bitScaleFlow solve I (bitScalingPhases I) (t + 1)) (I.m + 1) e =
      min (2 * cappedResidual I (bitScalingPhases I) t
            (bitScaleFlow solve I (bitScalingPhases I) t) (I.m + 1) e +
          capBit I (bitScalingPhases I - (t + 1)) e +
          (bitScaleDelta solve I (bitScalingPhases I) t (Fin.natAdd I.m e)).toNat -
          (bitScaleDelta solve I (bitScalingPhases I) t (Fin.castAdd I.m e)).toNat)
        (I.m + 1) ∧
    cappedFlow (bitScaleFlow solve I (bitScalingPhases I) (t + 1)) (I.m + 1) e =
      min (2 * cappedFlow (bitScaleFlow solve I (bitScalingPhases I) t) (I.m + 1) e +
          (bitScaleDelta solve I (bitScalingPhases I) t (Fin.castAdd I.m e)).toNat -
          (bitScaleDelta solve I (bitScalingPhases I) t (Fin.natAdd I.m e)).toNat)
        (I.m + 1) := by
  let T := bitScalingPhases I
  have hstep : ∀ s < T, (bitScalePhaseCall solve I T s).Optimal
      (fun a => (bitScaleDelta solve I T s a : ℝ)) := fun s hs =>
    hsolve _ (List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩)
  have hprev := bitScaleFlow_optimal_step solve I T
    (capacity_lt_two_pow_bitScalingPhases I) hstep t (Nat.le_of_lt ht)
  have hg_bounds : ∀ k, 0 ≤ bitScaleFlow solve I T t k ∧
      bitScaleFlow solve I T t k ≤ ((truncInstance I (T - t)).capacity k : ℤ) := by
    intro k
    have hk1 : 0 ≤ bitScaleFlow solve I T t k :=
      (Int.cast_nonneg_iff (R := ℝ)).mp (hprev.1.2 k).1
    have hk2 : bitScaleFlow solve I T t k ≤ ((truncInstance I (T - t)).capacity k : ℤ) := by
      apply (Int.cast_le (R := ℝ)).mp
      simpa only [Int.cast_natCast] using (hprev.1.2 k).2
    exact ⟨hk1, hk2⟩
  have hd_feas : (bitScalePhaseCall solve I T t).Feasible
      (fun a => (bitScaleDelta solve I T t a : ℝ)) := (hstep t ht).1
  have hcap_f := phaseInstance_capacity_forward (truncInstance I (T - t))
    (capBit I (T - (t + 1))) (bitScaleFlow solve I T t) hg_bounds (I.m + 1) e
  have hcap_r := phaseInstance_capacity_reverse (truncInstance I (T - t))
    (capBit I (T - (t + 1))) (bitScaleFlow solve I T t) (fun k => (hg_bounds k).1) (I.m + 1) e
  have hdf := phaseInstance_delta_bounds (truncInstance I (T - t))
    (capBit I (T - (t + 1))) (bitScaleFlow solve I T t) (I.m + 1)
    (bitScaleDelta solve I T t) hd_feas (Fin.castAdd I.m e)
  have hdr := phaseInstance_delta_bounds (truncInstance I (T - t))
    (capBit I (T - (t + 1))) (bitScaleFlow solve I T t) (I.m + 1)
    (bitScaleDelta solve I T t) hd_feas (Fin.natAdd I.m e)
  have hres := cappedResidual_after_augment (truncInstance I (T - t))
    (capBit I (T - (t + 1))) (bitScaleFlow solve I T t) hg_bounds (I.m + 1)
    (bitScaleDelta solve I T t) hd_feas e
  have hflw := cappedFlow_after_augment (truncInstance I (T - t))
    (capBit I (T - (t + 1))) (bitScaleFlow solve I T t) hg_bounds (I.m + 1)
    (bitScaleDelta solve I T t) hd_feas e
  have hcap_next : (doubled (truncInstance I (T - t)) (capBit I (T - (t + 1)))).capacity e =
      (truncInstance I (T - (t + 1))).capacity e := by
    have hk : 1 ≤ T - t := by omega
    have hsub : T - t - 1 = T - (t + 1) := by omega
    have hdiv := div_two_pow_sub_one (I.capacity e) (T - t) hk
    rw [hsub] at hdiv
    exact hdiv.symm
  refine ⟨hcap_f, hcap_r, hdf.1, ?_, hdr.1, ?_, ?_, hflw⟩
  · exact hcap_f ▸ hdf.2
  · exact hcap_r ▸ hdr.2
  · rw [hcap_next] at hres
    exact hres

/-- At the end of Stage 2, positive capped residual and positive capped flow
identify exactly the active forward and reverse slots of `I.residual g`. -/
theorem bitScaleSolve_residual_pos_iff (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (e : Fin I.m) :
    (0 < cappedResidual I (bitScalingPhases I) (bitScalingPhases I)
          (bitScaleSolve solve I) (I.m + 1) e ↔
        0 < (I.residual (bitScaleSolve solve I)).capacity (Fin.castAdd I.m e)) ∧
    (0 < cappedFlow (bitScaleSolve solve I) (I.m + 1) e ↔
        0 < (I.residual (bitScaleSolve solve I)).capacity (Fin.natAdd I.m e)) := by
  have hm1 : 0 < I.m + 1 := Nat.succ_pos I.m
  constructor
  · simp only [cappedResidual, phaseResidual, Nat.sub_self, pow_zero, Nat.div_one,
      Fin.addCases_left, lt_min_iff, hm1, and_true]
  · simp only [cappedFlow, Fin.addCases_right, lt_min_iff, hm1, and_true]

/-- After `t` phases, the bit-scaling flow equals the shifted binary sum of all
projected phase updates `0, …, t - 1`. -/
theorem bitScaleFlow_eq_sum (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (T t : ℕ) (e : Fin I.m) :
    bitScaleFlow solve I T t e =
      ∑ j ∈ Finset.range t,
        intProject I.m (bitScaleDelta solve I T j) e * (2 : ℤ) ^ (t - 1 - j) := by
  induction t with
  | zero =>
    simp [bitScaleFlow]
  | succ t ih =>
    have hstep : bitScaleFlow solve I T (t + 1) e =
        2 * bitScaleFlow solve I T t e + intProject I.m (bitScaleDelta solve I T t) e := rfl
    rw [hstep, ih, Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjt : j < t := Finset.mem_range.mp hj
    have hexp : t - j = (t - 1 - j) + 1 := by omega
    rw [hexp, pow_succ]
    ring

/-- Shifted-accumulator representation of the final bit-scaling flow
`bitScaleSolve solve I`. -/
theorem bitScaleSolve_eq_sum (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (e : Fin I.m) :
    bitScaleSolve solve I e =
      ∑ j ∈ Finset.range (bitScalingPhases I),
        intProject I.m (bitScaleDelta solve I (bitScalingPhases I) j) e *
          (2 : ℤ) ^ (bitScalingPhases I - 1 - j) :=
  bitScaleFlow_eq_sum solve I (bitScalingPhases I) (bitScalingPhases I) e

/-- Split shifted-accumulator representation separating the positive forward
updates and negative reverse updates for two nonnegative lazy accumulators. -/
theorem bitScaleSolve_eq_pos_sub_neg (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (e : Fin I.m) :
    bitScaleSolve solve I e =
      (∑ j ∈ Finset.range (bitScalingPhases I),
        bitScaleDelta solve I (bitScalingPhases I) j (Fin.castAdd I.m e) *
          (2 : ℤ) ^ (bitScalingPhases I - 1 - j)) -
      (∑ j ∈ Finset.range (bitScalingPhases I),
        bitScaleDelta solve I (bitScalingPhases I) j (Fin.natAdd I.m e) *
          (2 : ℤ) ^ (bitScalingPhases I - 1 - j)) := by
  rw [bitScaleSolve_eq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [intProject]
  ring

/-- Complete proof of `BitScalingGoal` for Stage 2. -/
theorem bitScalingGoal_proved : BitScalingGoal := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro solve I hsolve
    exact bitScaleSolve_optimal_of_calls solve I hsolve
  · intro solve I
    exact ⟨bitScaleModelCalls_length solve I,
      fun t _ => bitScalePhaseCall_shape solve I (bitScalingPhases I) t⟩
  · intro solve I hsolve t ht e
    exact bitScalePhase_capped_recurrences solve I hsolve t ht e
  · intro solve I _ e
    exact bitScaleSolve_residual_pos_iff solve I e
  · intro solve I e
    exact bitScaleSolve_eq_sum solve I e

end MinCostFlow.Narrow
