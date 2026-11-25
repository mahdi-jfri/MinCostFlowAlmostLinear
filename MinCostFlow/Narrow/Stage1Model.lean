module

public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Scaling.EpsilonOptimal
import MinCostFlow.Narrow.BitScalingModel
import MinCostFlow.Narrow.CappedPhase
import MinCostFlow.Narrow.CostBits
import MinCostFlow.Narrow.CostUnitsClip
import MinCostFlow.Narrow.DualBoundFreezing
import MinCostFlow.Narrow.SmallDual
import MinCostFlow.Scaling.RoundedProgress
import MinCostFlow.Scaling.EpsilonExactness
import MinCostFlow.Scaling.CostLoopCorrectness
import MinCostFlow.Scaling.SolverAdapter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Stage 1 narrow-word cost-scaling model and correctness (Items 6 and 7)

This file proves `Stage1Goal`:
- Every round of `narrowCostSolve` preserves `ε_j`-optimality with the ghost
  potential `ghostRealPotential`, tracks unfrozen reduced costs in half units
  via Lemma 5 (`CostBits.lean`), and locks frozen edges via Lemma 4
  (`DualBoundFreezing.lean`), using Stage 2 (`bitScaleSolve`) and small-data
  dual extraction (`extractDualFromFlags`).
- After `narrowCostRounds I = L + p + 1 + Nat.size (I.n + 1)` rounds,
  `ε_J < 1 / (I.n + 1)`, so `lemma_C_5` certifies exact integral optimality of
  `narrowCostSolve solve I`.
- Every positive-capacity solver call in `narrowCostSolverCalls solve I` fits
  `solverContract` and `compressedSolverContract` (`1 ≤ cap ≤ K.m ^ 40`,
  `CostsBounded (K.m ^ 10)`, `K.n ≤ 2 * K.m + 1`).
- The small-state transition (`narrowCostStep_small_state`) updates `frozen`,
  `halfCost`, and the next round's costs solely from the previous round's
  `frozen`, `halfCost`, single edge cost bits, and round dual.
-/

@[expose] public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling

/-- The combined specification of Stage 1 (`narrowCostSolve`):
1. Per-round `ε_j`-optimality with the ghost potential `ghostRealPotential`,
   and exact integral optimality of `narrowCostSolve solve I` after
   `narrowCostRounds I` rounds whenever `solve` is optimal on every call in
   `narrowCostSolverCalls solve I`.
2. Explicit round count `narrowCostRounds I = costScaleBits I + costPrecisionExp I.m + 1 + Nat.size (I.n + 1)`
   and per-call bounds: every `K ∈ narrowCostSolverCalls solve I` has
   `K.n ≤ I.n + 2`, `K.n ≤ 2 * K.m + 1`, `K.m ≤ 8 * I.m + 2 * I.n`,
   `1 ≤ K.capacity a ≤ K.m ^ 40`, and `K.CostsBounded (K.m ^ 10)` (with
   `(K.cost a).natAbs ≤ upperClip I.m`).
3. Small-state transition: `frozen`, `halfCost`, and the rounded slot costs of
   round `j + 1` are explicit functions of those of round `j`, the single edge
   cost bits `costBit (I.cost e) ((L : ℤ) - (j + 1))`, and the round's dual,
   with `|(s.halfCost e)| < freezeThreshold I.m` at every round. -/
def Stage1Goal : Prop :=
  (∀ (solve : (K : Circulation) → Fin K.m → ℤ) (I : Circulation),
    0 < I.m → I.n ≤ 2 * I.m →
    (∀ K ∈ narrowCostSolverCalls solve I, K.Optimal (fun a => (solve K a : ℝ))) →
    (∀ j ≤ narrowCostRounds I,
      I.EpsilonOptimalWith
        (fun e => ((narrowCostStateAt solve I (costScaleBits I) j).flow e : ℝ))
        (stageEps (costScaleBits I) (costPrecisionExp I.m) j)
        (ghostRealPotential solve I (costScaleBits I) j)) ∧
    I.Optimal (fun e => (narrowCostSolve solve I e : ℝ))) ∧
  (∀ (solve : (K : Circulation) → Fin K.m → ℤ) (I : Circulation),
    0 < I.m → I.n ≤ 2 * I.m →
    ∀ K ∈ narrowCostSolverCalls solve I,
      K.n ≤ I.n + 2 ∧
      K.n ≤ 2 * K.m + 1 ∧
      K.m ≤ 8 * I.m + 2 * I.n ∧
      (∀ a, 1 ≤ K.capacity a ∧ K.capacity a ≤ K.m ^ 40) ∧
      K.CostsBounded (upperClip I.m) ∧
      K.CostsBounded (K.m ^ 10)) ∧
  (∀ (solve : (K : Circulation) → Fin K.m → ℤ) (I : Circulation) (L : ℕ)
    (s : NarrowCostState I),
    (∀ e, (narrowCostStep solve I L s).frozen e =
      (stepHalfCost (freezeThreshold I.m) (s.frozen e) (s.halfCost e)
        (costBit (I.cost e) ((L : ℤ) - ((s.round + 1 : ℕ) : ℤ)))
        (narrowRoundDual solve I s (I.tail e) - narrowRoundDual solve I s (I.head e))).1) ∧
    (∀ e, (narrowCostStep solve I L s).halfCost e =
      (stepHalfCost (freezeThreshold I.m) (s.frozen e) (s.halfCost e)
        (costBit (I.cost e) ((L : ℤ) - ((s.round + 1 : ℕ) : ℤ)))
        (narrowRoundDual solve I s (I.tail e) - narrowRoundDual solve I s (I.head e))).2) ∧
    (narrowRoundInstance I (narrowCostStep solve I L s)).cost =
      narrowRoundedCosts I
        (fun e => (stepHalfCost (freezeThreshold I.m) (s.frozen e) (s.halfCost e)
          (costBit (I.cost e) ((L : ℤ) - ((s.round + 1 : ℕ) : ℤ)))
          (narrowRoundDual solve I s (I.tail e) - narrowRoundDual solve I s (I.head e))).1)
        (fun e => (stepHalfCost (freezeThreshold I.m) (s.frozen e) (s.halfCost e)
          (costBit (I.cost e) ((L : ℤ) - ((s.round + 1 : ℕ) : ℤ)))
          (narrowRoundDual solve I s (I.tail e) - narrowRoundDual solve I s (I.head e))).2)) ∧
  (∀ (solve : (K : Circulation) → Fin K.m → ℤ) (I : Circulation),
    0 < I.m → I.n ≤ 2 * I.m →
    ∀ j, ∀ e : Fin I.m,
      ((narrowCostStateAt solve I (costScaleBits I) j).halfCost e).natAbs <
        freezeThreshold I.m)

/-- The round counter of `narrowCostStateAt` equals `j`. -/
theorem narrowCostStateAt_round (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (L j : ℕ) :
    (narrowCostStateAt solve I L j).round = j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (narrowCostStateAt solve I L j).round + 1 = j + 1
    rw [ih]

/-- Stored half-unit reduced costs stay strictly below `freezeThreshold I.m` in
every round. -/
theorem narrowCostStateAt_halfCost_abs_lt (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (L j : ℕ) (e : Fin I.m) :
    ((narrowCostStateAt solve I L j).halfCost e).natAbs < freezeThreshold I.m := by
  cases j with
  | zero =>
    have h8 : 8 ≤ freezeThreshold I.m := by
      unfold freezeThreshold upperClip
      have h1 : 1 ≤ 2 ^ (costPrecisionExp I.m + costClipExp I.m) := Nat.pow_pos (by decide)
      omega
    dsimp only [narrowCostStateAt, narrowCostInitial]
    split <;> omega
  | succ j =>
    exact stepHalfCost_snd_abs_lt (freezeThreshold I.m) (freezeThreshold_pos I.m) _ _ _ _

/-- Geometry, capacity, and cost bounds for every solver call in one Stage 1
round. -/
theorem narrowRoundSolverCalls_bounds (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (hm : 0 < I.m) (hn : I.n ≤ 2 * I.m)
    (s : NarrowCostState I) :
    ∀ K ∈ narrowRoundSolverCalls solve I s,
      K.n ≤ I.n + 2 ∧
      K.n ≤ 2 * K.m + 1 ∧
      K.m ≤ 8 * I.m + 2 * I.n ∧
      (∀ a, 1 ≤ K.capacity a ∧ K.capacity a ≤ K.m ^ 40) ∧
      K.CostsBounded (upperClip I.m) ∧
      K.CostsBounded (K.m ^ 10) := by
  let J := narrowRoundInstance I s
  have hJ_costs : J.CostsBounded (upperClip I.m) :=
    narrowRoundedCosts_natAbs_le I s.frozen s.halfCost
  have huc10 : upperClip I.m ≤ (2 * I.m) ^ 10 := upperClip_le_pow10 I.m hm
  intro K hK
  rcases List.mem_append.mp hK with hstage2 | hdual
  · obtain ⟨P, hP_mem, rfl⟩ := List.mem_map.mp hstage2
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hP_mem
    have hshape := bitScalePhaseCall_shape (Circulation.solveWithZeroCapacities solve)
      J (bitScalingPhases J) t
    have hPn : (bitScalePhaseCall (Circulation.solveWithZeroCapacities solve)
        J (bitScalingPhases J) t).positiveInstance.n = I.n + 1 := by
      change (bitScalePhaseCall (Circulation.solveWithZeroCapacities solve)
        J (bitScalingPhases J) t).n + 1 = I.n + 1
      rw [hshape.1]
    have hPm : (bitScalePhaseCall (Circulation.solveWithZeroCapacities solve)
        J (bitScalingPhases J) t).positiveInstance.m = 4 * I.m := by
      change (bitScalePhaseCall (Circulation.solveWithZeroCapacities solve)
        J (bitScalingPhases J) t).m = 4 * I.m
      rw [hshape.2.1]
      change 2 * (I.m + I.m) = 4 * I.m
      omega
    have hcap_le : ∀ a, (bitScalePhaseCall (Circulation.solveWithZeroCapacities solve)
        J (bitScalingPhases J) t).capacity a ≤ (4 * I.m) ^ 40 := by
      intro a
      have h1 := hshape.2.2.1 a
      have h2 : J.m + 1 ≤ 4 * I.m := by change I.m + I.m + 1 ≤ 4 * I.m; omega
      have h3 : 4 * I.m ≤ (4 * I.m) ^ 40 := by
        simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < 4 * I.m by omega)
          (show 1 ≤ 40 by decide)
      exact le_trans (le_trans h1 h2) h3
    have hP_costs : (bitScalePhaseCall (Circulation.solveWithZeroCapacities solve)
        J (bitScalingPhases J) t).CostsBounded (upperClip I.m) := by
      intro a
      refine Fin.addCases (m := J.m) (n := J.m) (fun e => ?_) (fun e => ?_) a
      · simpa only [Fin.addCases_left] using hJ_costs e
      · simpa only [Fin.addCases_right, Int.natAbs_neg] using hJ_costs e
    have hK_costs : (bitScalePhaseCall (Circulation.solveWithZeroCapacities solve)
        J (bitScalingPhases J) t).positiveInstance.CostsBounded (upperClip I.m) :=
      Circulation.positiveInstance_costsBounded _ _ hP_costs
    refine ⟨?_, ?_, ?_, ?_, hK_costs, ?_⟩
    · change (bitScalePhaseCall (Circulation.solveWithZeroCapacities solve)
        J (bitScalingPhases J) t).positiveInstance.n ≤ I.n + 2
      rw [hPn]; omega
    · change (bitScalePhaseCall (Circulation.solveWithZeroCapacities solve)
        J (bitScalingPhases J) t).positiveInstance.n ≤
        2 * (bitScalePhaseCall (Circulation.solveWithZeroCapacities solve)
          J (bitScalingPhases J) t).positiveInstance.m + 1
      rw [hPn, hPm]; omega
    · change (bitScalePhaseCall (Circulation.solveWithZeroCapacities solve)
        J (bitScalingPhases J) t).positiveInstance.m ≤ 8 * I.m + 2 * I.n
      rw [hPm]; omega
    · intro a
      have hpos := Circulation.positiveInstance_capacitiesBounded
        (bitScalePhaseCall (Circulation.solveWithZeroCapacities solve)
          J (bitScalingPhases J) t) ((4 * I.m) ^ 40)
        (Nat.pow_pos (by omega)) hcap_le a
      rw [hPm]
      exact hpos
    · intro a
      rw [hPm]
      have hpow : (2 * I.m) ^ 10 ≤ (4 * I.m) ^ 10 :=
        Nat.pow_le_pow_left (by omega) 10
      exact le_trans (hK_costs a) (le_trans huc10 hpow)
  · have hKeq : K = extractDualFromFlagsCall J
        (narrowRoundFwdFlags solve I s) (narrowRoundRevFlags solve I s) :=
      List.mem_singleton.mp hdual
    subst hKeq
    have hsh := extractDualFromFlagsCall_shape J
      (narrowRoundFwdFlags solve I s) (narrowRoundRevFlags solve I s)
      (upperClip I.m) hJ_costs
    have hKn : (extractDualFromFlagsCall J (narrowRoundFwdFlags solve I s)
        (narrowRoundRevFlags solve I s)).n = I.n + 2 := hsh.1
    have hKm : (extractDualFromFlagsCall J (narrowRoundFwdFlags solve I s)
        (narrowRoundRevFlags solve I s)).m = 8 * I.m + 2 * I.n := by
      rw [hsh.2.1]
      change 4 * (I.m + I.m) + 2 * I.n = 8 * I.m + 2 * I.n
      omega
    refine ⟨by omega, by omega, by omega, ?_, hsh.2.2.2, ?_⟩
    · intro a
      have hca := hsh.2.2.1 a
      have hle1 : I.n + 1 ≤ 8 * I.m + 2 * I.n := by omega
      have hle2 : 8 * I.m + 2 * I.n ≤ (8 * I.m + 2 * I.n) ^ 40 := by
        simpa only [pow_one] using Nat.pow_le_pow_right (show 0 < 8 * I.m + 2 * I.n by omega)
          (show 1 ≤ 40 by decide)
      rw [hKm]
      exact ⟨hca.1, le_trans (le_trans hca.2 hle1) hle2⟩
    · intro a
      rw [hKm]
      have hpow : (2 * I.m) ^ 10 ≤ (8 * I.m + 2 * I.n) ^ 10 :=
        Nat.pow_le_pow_left (by omega) 10
      exact le_trans (hsh.2.2.2 a) (le_trans huc10 hpow)

/-- Geometry, capacity, and cost bounds for every solver call across all Stage 1
rounds. -/
theorem narrowCostSolverCalls_bounds (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (hm : 0 < I.m) (hn : I.n ≤ 2 * I.m) :
    ∀ K ∈ narrowCostSolverCalls solve I,
      K.n ≤ I.n + 2 ∧
      K.n ≤ 2 * K.m + 1 ∧
      K.m ≤ 8 * I.m + 2 * I.n ∧
      (∀ a, 1 ≤ K.capacity a ∧ K.capacity a ≤ K.m ^ 40) ∧
      K.CostsBounded (upperClip I.m) ∧
      K.CostsBounded (K.m ^ 10) := by
  intro K hK
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp hK
  exact narrowRoundSolverCalls_bounds solve I hm hn _ K hj

/-- Each feasible Stage 1 round makes at most `bitScalingPhases I + 1` bounded
solver calls (`≤ bitScalingPhases I` in Stage 2 plus `1` for dual extraction). -/
theorem narrowRoundSolverCalls_length_le (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (s : NarrowCostState I)
    (hf : ∀ e, 0 ≤ s.flow e ∧ s.flow e ≤ (I.capacity e : ℤ)) :
    (narrowRoundSolverCalls solve I s).length ≤ bitScalingPhases I + 1 := by
  let J := narrowRoundInstance I s
  have hlen : (narrowRoundSolverCalls solve I s).length = bitScalingPhases J + 1 := by
    simp [narrowRoundSolverCalls, bitScaleModelCalls_length, J]
  rw [hlen]
  have hmax : circMaxCapacity J ≤ circMaxCapacity I := by
    unfold circMaxCapacity
    apply Finset.sup_le
    intro a _
    refine Fin.addCases (m := I.m) (n := I.m) (fun e => ?_) (fun e => ?_) a
    · have hfe := hf e
      have hle : J.capacity (Fin.castAdd I.m e) ≤ I.capacity e := by
        simp only [J, Fin.addCases_left]
        omega
      exact le_trans hle (Finset.le_sup (f := I.capacity) (Finset.mem_univ e))
    · have hfe := hf e
      have hle : J.capacity (Fin.natAdd I.m e) ≤ I.capacity e := by
        simp only [J, Fin.addCases_right]
        omega
      exact le_trans hle (Finset.le_sup (f := I.capacity) (Finset.mem_univ e))
  exact Nat.add_le_add_right (Nat.size_le_size hmax) 1

/-- Inductive invariant maintained across all Stage 1 rounds `0 ≤ j ≤ J`. -/
def RoundInvariant (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (L j : ℕ) : Prop :=
  let s := narrowCostStateAt solve I L j
  let y := ghostRealPotential solve I L j
  I.EpsilonOptimalWith (fun e => (s.flow e : ℝ))
    (stageEps L (costPrecisionExp I.m) j) y ∧
  (∀ e, s.frozen e = .none →
    s.halfCost e = costScaled (I.cost e) ((L : ℤ) - (j : ℤ)) -
      2 * (ghostPotential solve I L j (I.tail e) - ghostPotential solve I L j (I.head e))) ∧
  (∀ e, s.frozen e = .pos →
    s.flow e = 0 ∧ freezeMargin I.m L (costPrecisionExp I.m) j ≤ I.reducedCost y e) ∧
  (∀ e, s.frozen e = .neg →
    s.flow e = (I.capacity e : ℤ) ∧
      freezeMargin I.m L (costPrecisionExp I.m) j ≤ -I.reducedCost y e)

private lemma ghostRealPotential_succ (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (L j : ℕ) (v : Fin I.n) :
    ghostRealPotential solve I L (j + 1) v =
      ghostRealPotential solve I L j v +
        stageDelta L j * (narrowRoundDual solve I (narrowCostStateAt solve I L j) v : ℝ) := by
  unfold ghostRealPotential
  change stageDelta L (j + 1) *
      ((2 * (ghostPotential solve I L j v +
        narrowRoundDual solve I (narrowCostStateAt solve I L j) v) : ℤ) : ℝ) = _
  rw [stageDelta_succ]
  push_cast
  ring

/-- Base case (`j = 0`) of `RoundInvariant` at `L = costScaleBits I`. -/
theorem roundInvariant_zero (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) :
    RoundInvariant solve I (costScaleBits I) 0 := by
  let L := costScaleBits I
  have hcost_lt : ∀ e, (I.cost e).natAbs < 2 ^ L := fun e =>
    lt_of_le_of_lt (Finset.le_sup (f := fun k => (I.cost k).natAbs) (Finset.mem_univ e))
      (Nat.lt_size_self (circMaxCost I))
  have hy0 : ghostRealPotential solve I L 0 = fun _ => 0 := by
    funext v
    simp [ghostRealPotential, ghostPotential]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hy0]
    have h0 := I.zero_epsilonOptimal (circMaxCost I) (fun e => by
      have hle : (I.cost e).natAbs ≤ circMaxCost I :=
        Finset.le_sup (f := fun k => (I.cost k).natAbs) (Finset.mem_univ e)
      omega)
    have heps_le : (circMaxCost I : ℝ) + 1 ≤ stageEps L (costPrecisionExp I.m) 0 := by
      have hlt : circMaxCost I < 2 ^ L := Nat.lt_size_self (circMaxCost I)
      have hpow : 2 ^ L ≤ 2 ^ (L + costPrecisionExp I.m + 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hnat : circMaxCost I + 1 ≤ 2 ^ (L + costPrecisionExp I.m + 1) := by omega
      have hcast : ((circMaxCost I + 1 : ℕ) : ℝ) ≤
          ((2 ^ (L + costPrecisionExp I.m + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      unfold stageEps
      simp only [Nat.cast_zero, sub_zero, zpow_natCast]
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using hcast
    simpa only [narrowCostStateAt, narrowCostInitial, Int.cast_zero] using
      I.epsilonOptimalWith_mono _ _ _ _ h0 heps_le
  · intro e _
    change (if I.cost e < 0 then -1 else 0) =
      costScaled (I.cost e) ((L : ℤ) - (0 : ℤ)) - 2 * (0 - 0)
    rw [sub_zero, sub_self, mul_zero, sub_zero]
    exact (costScaled_init (I.cost e) L (hcost_lt e)).symm
  · intro e hpos
    change FreezeState.none = FreezeState.pos at hpos
    exact False.elim (FreezeState.noConfusion hpos)
  · intro e hneg
    change FreezeState.none = FreezeState.neg at hneg
    exact False.elim (FreezeState.noConfusion hneg)

/-- Inductive step of `RoundInvariant` (combining Lemma C.7, Lemma 4, Lemma 5,
Stage 2, and small-data dual extraction). -/
theorem roundInvariant_step (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (hm : 0 < I.m) (hn : I.n ≤ 2 * I.m) (L j : ℕ)
    (hinv : RoundInvariant solve I L j)
    (hcalls : ∀ K ∈ narrowRoundSolverCalls solve I (narrowCostStateAt solve I L j),
      K.Optimal (fun a => (solve K a : ℝ))) :
    RoundInvariant solve I L (j + 1) := by
  let s := narrowCostStateAt solve I L j
  let s' := narrowCostStateAt solve I L (j + 1)
  let J := narrowRoundInstance I s
  let delta := narrowRoundDelta solve I s
  let dy := narrowRoundDual solve I s
  let y := ghostRealPotential solve I L j
  let y' := ghostRealPotential solve I L (j + 1)
  have hround : s.round = j := narrowCostStateAt_round solve I L j
  have hdelta_opt : J.Optimal (fun a => (delta a : ℝ)) := by
    apply bitScaleSolve_optimal_of_calls
    intro P hP
    apply Circulation.solveWithZeroCapacities_of_optimal
    exact hcalls P.positiveInstance (List.mem_append_left _ (List.mem_map.mpr ⟨P, hP, rfl⟩))
  have hfwd_iff : ∀ a, narrowRoundFwdFlags solve I s a = true ↔
      0 < (J.residual delta).capacity (Fin.castAdd J.m a) := by
    intro a
    dsimp only [narrowRoundFwdFlags, J, delta, narrowRoundDelta]
    rw [decide_eq_true_eq]
    exact (bitScaleSolve_residual_pos_iff (Circulation.solveWithZeroCapacities solve) J a).1
  have hrev_iff : ∀ a, narrowRoundRevFlags solve I s a = true ↔
      0 < (J.residual delta).capacity (Fin.natAdd J.m a) := by
    intro a
    dsimp only [narrowRoundRevFlags, J, delta, narrowRoundDelta]
    rw [decide_eq_true_eq]
    exact (bitScaleSolve_residual_pos_iff (Circulation.solveWithZeroCapacities solve) J a).2
  have hdual_call : (extractDualFromFlagsCall J (narrowRoundFwdFlags solve I s)
      (narrowRoundRevFlags solve I s)).Optimal
      (fun a => (solve (extractDualFromFlagsCall J (narrowRoundFwdFlags solve I s)
        (narrowRoundRevFlags solve I s)) a : ℝ)) :=
    hcalls _ (List.mem_append_right _ List.mem_cons_self)
  have hdual_corr := extractDualFromFlags_correct solve J delta
    (narrowRoundFwdFlags solve I s) (narrowRoundRevFlags solve I s)
    hfwd_iff hrev_iff hdelta_opt hdual_call
  have hdual_bnds := extractDualFromFlags_bounds solve J (lowerClip I.m)
    (narrowRoundedCosts_lower_bound I s.frozen s.halfCost) delta
    (narrowRoundFwdFlags solve I s) (narrowRoundRevFlags solve I s)
    hfwd_iff hrev_iff hdelta_opt hdual_call
  have hδ : 0 < stageDelta L j := stageDelta_pos L j
  have hy'_eq : y' = fun v => y v + stageDelta L j * (dy v : ℝ) := by
    funext v
    exact ghostRealPotential_succ solve I L j v
  have hflow'_cast : (fun e => (s'.flow e : ℝ)) = I.augment s.flow (fun a => (delta a : ℝ)) :=
    intAugment_cast I s.flow delta
  have hunf_floor : ∀ e, s.frozen e = .none →
      s.halfCost e = Int.floor (2 * I.reducedCost y e / stageDelta L j) := by
    intro e hfr
    rw [hinv.2.1 e hfr]
    exact (halfCost_eq_floor I L j (ghostPotential solve I L j) e).symm
  have hpos_clip : ∀ e, s.frozen e = .pos →
      s.flow e = 0 ∧ (upperClip I.m : ℝ) * stageDelta L j ≤ I.reducedCost y e := by
    intro e hfr
    exact ⟨(hinv.2.2.1 e hfr).1,
      le_trans (freezeMargin_ge_upperClip_mul_delta I.m L j) (hinv.2.2.1 e hfr).2⟩
  have hneg_clip : ∀ e, s.frozen e = .neg →
      s.flow e = (I.capacity e : ℤ) ∧
        (upperClip I.m : ℝ) * stageDelta L j ≤ -I.reducedCost y e := by
    intro e hfr
    exact ⟨(hinv.2.2.2 e hfr).1,
      le_trans (freezeMargin_ge_upperClip_mul_delta I.m L j) (hinv.2.2.2 e hfr).2⟩
  have herror := narrowRoundedCosts_error_for_progress I hm hn L j s y
    hinv.1 hunf_floor hpos_clip hneg_clip delta hdelta_opt
  have hsigns : ∀ a,
      ((delta a : ℝ) < (I.residual s.flow).capacity a →
        0 ≤ stageDelta L j * ((narrowRoundInstance I s).cost a : ℝ) -
          (I.residual s.flow).potentialDifference (fun v => stageDelta L j * (dy v : ℝ)) a) ∧
      (0 < (delta a : ℝ) →
        stageDelta L j * ((narrowRoundInstance I s).cost a : ℝ) -
          (I.residual s.flow).potentialDifference (fun v => stageDelta L j * (dy v : ℝ)) a ≤ 0) := by
    intro a
    have hpd : (I.residual s.flow).potentialDifference (fun v => stageDelta L j * (dy v : ℝ)) a =
        stageDelta L j * J.potentialDifference (fun v => (dy v : ℝ)) a := by
      simp only [Circulation.potentialDifference]
      ring
    rw [hpd, ← mul_sub]
    constructor
    · intro hlt
      exact mul_nonneg hδ.le ((hdual_corr.2.2.2 a).1 hlt)
    · intro hpos
      exact mul_nonpos_of_nonneg_of_nonpos hδ.le ((hdual_corr.2.2.2 a).2 hpos)
  have heps_next : I.EpsilonOptimalWith (fun e => (s'.flow e : ℝ))
      (stageEps L (costPrecisionExp I.m) (j + 1)) y' := by
    rw [hflow'_cast, hy'_eq, stageEps_succ]
    exact I.epsilonOptimalWith_augment_of_rounded_signs s.flow hinv.1.2.1
      (fun a => (delta a : ℝ)) hdelta_opt.1 y (fun v => stageDelta L j * (dy v : ℝ))
      (fun a => stageDelta L j * (J.cost a : ℝ))
      (stageDelta L j / 2) (stageEps L (costPrecisionExp I.m) j / 2)
      (div_pos (stageEps_pos L (costPrecisionExp I.m) j) (by norm_num))
      (stageDelta_div_two_lt_half_eps L I.m j hm)
      herror hsigns
  -- Verify per-edge unfrozen and frozen invariants at `j + 1`.
  have hdrift : ∀ e, |I.reducedCost y' e - I.reducedCost y e| ≤
      2 * (I.m : ℝ) * stageEps L (costPrecisionExp I.m) j := by
    intro e
    rw [hy'_eq]
    exact reducedCost_drift_le I hn L j y dy hdual_bnds e
  have hstep_eq : ∀ e,
      (s'.frozen e, s'.halfCost e) =
        stepHalfCost (freezeThreshold I.m) (s.frozen e) (s.halfCost e)
          (costBit (I.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)))
          (dy (I.tail e) - dy (I.head e)) := by
    intro e
    dsimp only [s', narrowCostStateAt, narrowCostStep, s, dy]
    rw [hround]
  have hfloor_next : ∀ e, s.frozen e = .none →
      2 * s.halfCost e + costBit (I.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)) -
          4 * (dy (I.tail e) - dy (I.head e)) =
        costScaled (I.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)) -
          2 * (ghostPotential solve I L (j + 1) (I.tail e) -
            ghostPotential solve I L (j + 1) (I.head e)) := by
    intro e hfr
    rw [hinv.2.1 e hfr]
    exact (halfCost_step_identity I L j (ghostPotential solve I L j) dy e).symm
  refine ⟨heps_next, ?_, ?_, ?_⟩
  · -- Unfrozen `halfCost` invariant
    intro e hfr'
    have hsp := hstep_eq e
    cases hfr : s.frozen e with
    | pos =>
      rw [hfr] at hsp
      simp only [stepHalfCost, Prod.mk.injEq] at hsp
      rw [hsp.1] at hfr'
      exact False.elim (FreezeState.noConfusion hfr')
    | neg =>
      rw [hfr] at hsp
      simp only [stepHalfCost, Prod.mk.injEq] at hsp
      rw [hsp.1] at hfr'
      exact False.elim (FreezeState.noConfusion hfr')
    | none =>
      rw [hfr] at hsp
      dsimp only [stepHalfCost] at hsp
      split at hsp
      · simp only [Prod.mk.injEq] at hsp; rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
      · split at hsp
        · simp only [Prod.mk.injEq] at hsp; rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
        · simp only [Prod.mk.injEq] at hsp
          rw [hsp.2]
          exact hfloor_next e hfr
  · -- Positively frozen invariant
    intro e hfr'
    have hsp := hstep_eq e
    cases hfr : s.frozen e with
    | neg =>
      rw [hfr] at hsp
      simp only [stepHalfCost, Prod.mk.injEq] at hsp
      rw [hsp.1] at hfr'
      exact False.elim (FreezeState.noConfusion hfr')
    | pos =>
      have hmargin : freezeMargin I.m L (costPrecisionExp I.m) (j + 1) ≤ I.reducedCost y' e :=
        freezeMargin_preserved I.m L j (I.reducedCost y e) (I.reducedCost y' e)
          (hinv.2.2.1 e hfr).2 (hdrift e)
      exact ⟨(flow_eq_of_freezeMargin I hm L (j + 1) s'.flow y' heps_next e).1 hmargin, hmargin⟩
    | none =>
      rw [hfr] at hsp
      dsimp only [stepHalfCost] at hsp
      split at hsp
      · rename_i hge
        have hfl : Int.floor (2 * I.reducedCost y' e / stageDelta L (j + 1)) =
            2 * s.halfCost e + costBit (I.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)) -
              4 * (dy (I.tail e) - dy (I.head e)) := by
          rw [hfloor_next e hfr]
          exact halfCost_eq_floor I L (j + 1) (ghostPotential solve I L (j + 1)) e
        have hmargin := freezeMargin_of_threshold_pos I.m L (j + 1) (I.reducedCost y' e)
          (hfl ▸ hge)
        exact ⟨(flow_eq_of_freezeMargin I hm L (j + 1) s'.flow y' heps_next e).1 hmargin, hmargin⟩
      · split at hsp
        · simp only [Prod.mk.injEq] at hsp; rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
        · simp only [Prod.mk.injEq] at hsp; rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
  · -- Negatively frozen invariant
    intro e hfr'
    have hsp := hstep_eq e
    cases hfr : s.frozen e with
    | pos =>
      rw [hfr] at hsp
      simp only [stepHalfCost, Prod.mk.injEq] at hsp
      rw [hsp.1] at hfr'
      exact False.elim (FreezeState.noConfusion hfr')
    | neg =>
      have hdrift_neg : |-I.reducedCost y' e - -I.reducedCost y e| ≤
          2 * (I.m : ℝ) * stageEps L (costPrecisionExp I.m) j := by
        have : -I.reducedCost y' e - -I.reducedCost y e = -(I.reducedCost y' e - I.reducedCost y e) := by ring
        rw [this, abs_neg]
        exact hdrift e
      have hmargin : freezeMargin I.m L (costPrecisionExp I.m) (j + 1) ≤ -I.reducedCost y' e :=
        freezeMargin_preserved I.m L j (-I.reducedCost y e) (-I.reducedCost y' e)
          (hinv.2.2.2 e hfr).2 hdrift_neg
      exact ⟨(flow_eq_of_freezeMargin I hm L (j + 1) s'.flow y' heps_next e).2 hmargin, hmargin⟩
    | none =>
      rw [hfr] at hsp
      dsimp only [stepHalfCost] at hsp
      split at hsp
      · simp only [Prod.mk.injEq] at hsp; rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
      · split at hsp
        · rename_i _ hle
          have hfl : Int.floor (2 * I.reducedCost y' e / stageDelta L (j + 1)) =
              2 * s.halfCost e + costBit (I.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)) -
                4 * (dy (I.tail e) - dy (I.head e)) := by
            rw [hfloor_next e hfr]
            exact halfCost_eq_floor I L (j + 1) (ghostPotential solve I L (j + 1)) e
          have hmargin := freezeMargin_of_threshold_neg I.m L (j + 1) hm (I.reducedCost y' e)
            (hfl ▸ hle)
          exact ⟨(flow_eq_of_freezeMargin I hm L (j + 1) s'.flow y' heps_next e).2 hmargin, hmargin⟩
        · simp only [Prod.mk.injEq] at hsp; rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')

/-- `RoundInvariant` holds for every round `j ≤ narrowCostRounds I`. -/
theorem narrowCostStateAt_invariant (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (hm : 0 < I.m) (hn : I.n ≤ 2 * I.m)
    (hsolve : ∀ K ∈ narrowCostSolverCalls solve I, K.Optimal (fun a => (solve K a : ℝ))) :
    ∀ j ≤ narrowCostRounds I, RoundInvariant solve I (costScaleBits I) j := by
  intro j hj
  induction j with
  | zero => exact roundInvariant_zero solve I
  | succ j ih =>
    have hprev := ih (Nat.le_of_succ_le hj)
    have hcalls : ∀ K ∈ narrowRoundSolverCalls solve I
        (narrowCostStateAt solve I (costScaleBits I) j),
        K.Optimal (fun a => (solve K a : ℝ)) := fun K hK =>
      hsolve K (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (Nat.lt_of_succ_le hj), hK⟩)
    exact roundInvariant_step solve I hm hn (costScaleBits I) j hprev hcalls

/-- At the end of `narrowCostRounds I` rounds, `ε_J < 1 / (I.n + 1)`. -/
theorem stageEps_final_lt (I : Circulation) :
    stageEps (costScaleBits I) (costPrecisionExp I.m) (narrowCostRounds I) <
      1 / ((I.n : ℝ) + 1) := by
  unfold stageEps narrowCostRounds
  have hexp : (((costScaleBits I + costPrecisionExp I.m + 1 : ℕ) : ℤ) -
      ((costScaleBits I + costPrecisionExp I.m + 1 + Nat.size (I.n + 1) : ℕ) : ℤ)) =
      -(Nat.size (I.n + 1) : ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast, one_div]
  have hlt : I.n + 1 < 2 ^ Nat.size (I.n + 1) := Nat.lt_size_self (I.n + 1)
  have hlt_r : ((I.n : ℝ) + 1) < (2 : ℝ) ^ Nat.size (I.n + 1) := by
    have : ((I.n + 1 : ℕ) : ℝ) < ((2 ^ Nat.size (I.n + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using this
  have hpos : (0 : ℝ) < (I.n : ℝ) + 1 := by positivity
  exact inv_strictAnti₀ hpos hlt_r

/-- Exact integral optimality of Stage 1 (`narrowCostSolve`) from optimality on
its actual solver calls. -/
theorem narrowCostSolve_optimal_of_calls (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (hm : 0 < I.m) (hn : I.n ≤ 2 * I.m)
    (hsolve : ∀ K ∈ narrowCostSolverCalls solve I, K.Optimal (fun a => (solve K a : ℝ))) :
    I.Optimal (fun e => (narrowCostSolve solve I e : ℝ)) := by
  have hfinal := (narrowCostStateAt_invariant solve I hm hn hsolve (narrowCostRounds I) le_rfl).1
  have hlt := stageEps_final_lt I
  apply I.lemma_C_5 (narrowCostSolve solve I)
  exact ⟨_, I.epsilonOptimalWith_mono _ _ _ _ hfinal hlt.le⟩

/-- Exact integral optimality of Stage 1 from any bounded positive-capacity
solver matching `solverContract` (or `compressedSolverContract`). -/
theorem narrowCostSolve_optimal (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (hm : 0 < I.m) (hn : I.n ≤ 2 * I.m)
    (hsolve : ∀ K : Circulation, K.n ≤ 2 * K.m + 1 → K.CostsBounded (K.m ^ 10) →
      (∀ a, 1 ≤ K.capacity a ∧ K.capacity a ≤ K.m ^ 40) →
      K.Optimal (fun a => (solve K a : ℝ))) :
    I.Optimal (fun e => (narrowCostSolve solve I e : ℝ)) := by
  apply narrowCostSolve_optimal_of_calls solve I hm hn
  intro K hK
  have hb := narrowCostSolverCalls_bounds solve I hm hn K hK
  exact hsolve K hb.2.1 hb.2.2.2.2.2 hb.2.2.2.1

/-- Small-state transition (Item 7): `frozen`, `halfCost`, and the next round's
rounded slot costs are explicit functions of the current round's `frozen`,
`halfCost`, single edge cost bits, and round dual, with no potentials. -/
theorem narrowCostStep_small_state (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (L : ℕ) (s : NarrowCostState I) :
    (∀ e, (narrowCostStep solve I L s).frozen e =
      (stepHalfCost (freezeThreshold I.m) (s.frozen e) (s.halfCost e)
        (costBit (I.cost e) ((L : ℤ) - ((s.round + 1 : ℕ) : ℤ)))
        (narrowRoundDual solve I s (I.tail e) - narrowRoundDual solve I s (I.head e))).1) ∧
    (∀ e, (narrowCostStep solve I L s).halfCost e =
      (stepHalfCost (freezeThreshold I.m) (s.frozen e) (s.halfCost e)
        (costBit (I.cost e) ((L : ℤ) - ((s.round + 1 : ℕ) : ℤ)))
        (narrowRoundDual solve I s (I.tail e) - narrowRoundDual solve I s (I.head e))).2) ∧
    (narrowRoundInstance I (narrowCostStep solve I L s)).cost =
      narrowRoundedCosts I
        (fun e => (stepHalfCost (freezeThreshold I.m) (s.frozen e) (s.halfCost e)
          (costBit (I.cost e) ((L : ℤ) - ((s.round + 1 : ℕ) : ℤ)))
          (narrowRoundDual solve I s (I.tail e) - narrowRoundDual solve I s (I.head e))).1)
        (fun e => (stepHalfCost (freezeThreshold I.m) (s.frozen e) (s.halfCost e)
          (costBit (I.cost e) ((L : ℤ) - ((s.round + 1 : ℕ) : ℤ)))
          (narrowRoundDual solve I s (I.tail e) - narrowRoundDual solve I s (I.head e))).2) :=
  ⟨fun _ => rfl, fun _ => rfl, rfl⟩

/-- Complete proof of `Stage1Goal`. -/
theorem stage1Goal_proved : Stage1Goal := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro solve I hm hn hsolve
    exact ⟨fun j hj => (narrowCostStateAt_invariant solve I hm hn hsolve j hj).1,
      narrowCostSolve_optimal_of_calls solve I hm hn hsolve⟩
  · intro solve I hm hn
    exact narrowCostSolverCalls_bounds solve I hm hn
  · intro solve I L s
    exact narrowCostStep_small_state solve I L s
  · intro solve I _ _ j e
    exact narrowCostStateAt_halfCost_abs_lt solve I (costScaleBits I) j e

end MinCostFlow.Narrow
