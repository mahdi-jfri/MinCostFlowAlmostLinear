module

public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Scaling.EpsilonOptimal
public import MinCostFlow.NarrowProg.TopBitLength
import MinCostFlow.Narrow.CostBits
import MinCostFlow.Narrow.CappedPhase
import MinCostFlow.Narrow.CostUnitsClip
import MinCostFlow.Narrow.DualBoundFreezing
import MinCostFlow.Narrow.SmallDual
import MinCostFlow.Narrow.Stage1Model
import MinCostFlow.Scaling.RoundedProgress
import MinCostFlow.Scaling.EpsilonExactness
import MinCostFlow.Scaling.CostLoopCorrectness
import MinCostFlow.Scaling.SolverAdapter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Relational Stage 1 invariant and arithmetic helpers for the Stage 1 program

Because the second-layer Word-RAM specifications `bitScaleSpec` and `solverSpec`
return an arbitrary optimal integral circulation at each call rather than values
of a fixed global function `solve : (K : Circulation) → Fin K.m → ℤ`, this file
states the per-round Stage 1 invariant `RoundInvariantState I L s y` directly on
a ghost state `(s : NarrowCostState I, y : Fin I.n → ℤ)` and proves:

- `roundInvariantState_zero`: base case at `narrowCostInitial I` and `y = 0`;
- `roundInvariantState_step`: one-round step from any optimal `delta` of
  `narrowRoundInstance I s`, any residual-positivity flags `fwd`/`rev`, and any
  optimal `d_dual` of `extractDualFromFlagsCall (narrowRoundInstance I s) fwd rev`;
- `roundInvariantState_final_optimal`: exact integral optimality at
  `s.round = narrowCostRounds I`;
- arithmetic bridge lemmas (`costBit_neg_eq_sub_one`, `half_div_two_neg`,
  `circMaxCost_eq_maxLimbsVal`, `circMaxCapacity_eq_maxLimbsVal`,
  `capLimbs_length_le_Kcap`, `circMaxCapacity_narrowRound_le`).
-/

public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling MinCostFlow.NarrowProg

/-- Extract the round's integral dual potential directly from a single optimal
solution `d_dual` of `extractDualFromFlagsCall J fwdActive revActive`, without
requiring a global solver function. -/
@[expose] def extractDualFromFlagsOfAnswer (J : Circulation)
    (fwdActive revActive : Fin J.m → Bool)
    (d_dual : Fin (extractDualFromFlagsCall J fwdActive revActive).m → ℤ) : Fin J.n → ℤ :=
  let R := flagResidualGraph J fwdActive revActive
  let S := R.shortestRoutingGraph
  let start := R.shortestRoutingStart
  let Q := S.residual start
  let delta : Fin Q.m → ℤ := fun e => if Q.capacity e = 0 then 0 else d_dual e
  let routing : Fin S.m → ℤ := fun e =>
    start e + delta (Fin.castAdd S.m e) - delta (Fin.natAdd S.m e)
  let labels := S.propagateLabels routing (Fin.last J.n)
  fun v => labels.1.labels v.castSucc

/-- One Stage 1 cost-scaling state transition driven by explicit round answers
`delta` and `dy`. -/
@[expose] def narrowCostStepOfAnswers (I : Circulation) (L : ℕ)
    (s : NarrowCostState I) (delta : Fin (I.m + I.m) → ℤ) (dy : Fin I.n → ℤ) :
    NarrowCostState I :=
  let nextPair (e : Fin I.m) : FreezeState × ℤ :=
    stepHalfCost (freezeThreshold I.m) (s.frozen e) (s.halfCost e)
      (costBit (I.cost e) ((L : ℤ) - ((s.round + 1 : ℕ) : ℤ)))
      (dy (I.tail e) - dy (I.head e))
  { flow := intAugment I.m s.flow delta
    frozen := fun e => (nextPair e).1
    halfCost := fun e => (nextPair e).2
    round := s.round + 1 }

/-- Relational Stage 1 invariant on an explicit ghost state `(s, y)` at round
`s.round`. Matches `RoundInvariant` (`Stage1Model.lean`) conjunct for conjunct. -/
@[expose] def RoundInvariantState (I : Circulation) (L : ℕ)
    (s : NarrowCostState I) (y : Fin I.n → ℤ) : Prop :=
  let yReal : Fin I.n → ℝ := fun v => stageDelta L s.round * (y v : ℝ)
  I.EpsilonOptimalWith (fun e => (s.flow e : ℝ))
    (stageEps L (costPrecisionExp I.m) s.round) yReal ∧
  (∀ e, s.frozen e = .none →
    s.halfCost e = costScaled (I.cost e) ((L : ℤ) - (s.round : ℤ)) -
      2 * (y (I.tail e) - y (I.head e))) ∧
  (∀ e, s.frozen e = .pos →
    s.flow e = 0 ∧ freezeMargin I.m L (costPrecisionExp I.m) s.round ≤ I.reducedCost yReal e) ∧
  (∀ e, s.frozen e = .neg →
    s.flow e = (I.capacity e : ℤ) ∧
      freezeMargin I.m L (costPrecisionExp I.m) s.round ≤ -I.reducedCost yReal e) ∧
  (∀ e, (s.halfCost e).natAbs < freezeThreshold I.m)

/-- Construct a solver function returning `d_dual` on `Q₀` and `0` elsewhere. -/
private noncomputable def singleAnswerSolver (Q₀ : Circulation) (d_dual : Fin Q₀.m → ℤ) :
    (K : Circulation) → Fin K.m → ℤ := by
  classical
  exact fun K => if h : K = Q₀ then h ▸ d_dual else fun _ => 0

private lemma singleAnswerSolver_self (Q₀ : Circulation) (d_dual : Fin Q₀.m → ℤ) :
    singleAnswerSolver Q₀ d_dual Q₀ = d_dual := by
  classical
  simp [singleAnswerSolver]

/-- `extractDualFromFlagsOfAnswer` agrees with `extractDualFromFlags` on the
single-answer solver returning `d_dual`. -/
private lemma extractDualFromFlagsOfAnswer_eq (J : Circulation)
    (fwdActive revActive : Fin J.m → Bool)
    (d_dual : Fin (extractDualFromFlagsCall J fwdActive revActive).m → ℤ) :
    extractDualFromFlagsOfAnswer J fwdActive revActive d_dual =
      extractDualFromFlags (singleAnswerSolver (extractDualFromFlagsCall J fwdActive revActive) d_dual)
        J fwdActive revActive := by
  unfold extractDualFromFlagsOfAnswer extractDualFromFlags Circulation.solveWithZeroCapacities
  dsimp only
  rw [singleAnswerSolver_self]

/-- Dual potential bounds (`0 ≤ dy v ≤ (J.n - 1) * C_lo`) for
`extractDualFromFlagsOfAnswer`. -/
theorem extractDualFromFlagsOfAnswer_bounds (J : Circulation) (C_lo : ℕ)
    (hC : ∀ e, -(C_lo : ℤ) ≤ J.cost e) (f : Fin J.m → ℤ)
    (fwdActive revActive : Fin J.m → Bool)
    (hfwd : ∀ e, fwdActive e = true ↔ 0 < (J.residual f).capacity (Fin.castAdd J.m e))
    (hrev : ∀ e, revActive e = true ↔ 0 < (J.residual f).capacity (Fin.natAdd J.m e))
    (hf : J.Optimal (fun e => (f e : ℝ)))
    (d_dual : Fin (extractDualFromFlagsCall J fwdActive revActive).m → ℤ)
    (hd : (extractDualFromFlagsCall J fwdActive revActive).Optimal (fun a => (d_dual a : ℝ))) :
    ∀ v : Fin J.n,
      0 ≤ extractDualFromFlagsOfAnswer J fwdActive revActive d_dual v ∧
      extractDualFromFlagsOfAnswer J fwdActive revActive d_dual v ≤
        ((J.n - 1 : ℕ) : ℤ) * (C_lo : ℤ) := by
  rw [extractDualFromFlagsOfAnswer_eq]
  apply extractDualFromFlags_bounds _ J C_lo hC f fwdActive revActive hfwd hrev hf
  rw [singleAnswerSolver_self]
  exact hd

/-- Base case (`j = 0`) of `RoundInvariantState`. -/
theorem roundInvariantState_zero (I : Circulation) :
    RoundInvariantState I (costScaleBits I) (narrowCostInitial I) (fun _ => 0) := by
  have h0 := roundInvariant_zero (fun _ _ => 0) I
  have hy0 : ghostRealPotential (fun _ _ => 0) I (costScaleBits I) 0 = fun _ => 0 := by
    funext v; simp [ghostRealPotential, ghostPotential]
  have hlt : ∀ e, ((narrowCostInitial I).halfCost e).natAbs < freezeThreshold I.m :=
    fun e => narrowCostStateAt_halfCost_abs_lt (fun _ _ => 0) I (costScaleBits I) 0 e
  have hr : (fun _ : Fin I.n => stageDelta (costScaleBits I) (narrowCostInitial I).round * ((0 : ℤ) : ℝ)) =
      fun _ => 0 := by funext v; simp
  refine ⟨?_, h0.2.1, ?_, ?_, hlt⟩
  · rw [hr]; simpa only [hy0, narrowCostStateAt, narrowCostInitial] using h0.1
  · intro e hpos; rw [hr]; simpa only [hy0, narrowCostStateAt, narrowCostInitial] using h0.2.2.1 e hpos
  · intro e hneg; rw [hr]; simpa only [hy0, narrowCostStateAt, narrowCostInitial] using h0.2.2.2 e hneg

/-- One-round preservation of `RoundInvariantState` for arbitrary optimal
answers `delta` (from Stage 2) and `d_dual` (from the bounded solver in dual
extraction). -/
theorem roundInvariantState_step (I : Circulation) (hm : 0 < I.m) (hn : I.n ≤ 2 * I.m)
    (L : ℕ) (s : NarrowCostState I) (y : Fin I.n → ℤ)
    (hinv : RoundInvariantState I L s y)
    (delta : Fin (I.m + I.m) → ℤ)
    (hdelta_opt : (narrowRoundInstance I s).Optimal (fun a => (delta a : ℝ)))
    (fwdActive revActive : Fin (I.m + I.m) → Bool)
    (hfwd : ∀ a, fwdActive a = true ↔
      0 < ((narrowRoundInstance I s).residual delta).capacity (Fin.castAdd (I.m + I.m) a))
    (hrev : ∀ a, revActive a = true ↔
      0 < ((narrowRoundInstance I s).residual delta).capacity (Fin.natAdd (I.m + I.m) a))
    (d_dual : Fin (extractDualFromFlagsCall (narrowRoundInstance I s) fwdActive revActive).m → ℤ)
    (hdual_opt : (extractDualFromFlagsCall (narrowRoundInstance I s) fwdActive revActive).Optimal
      (fun a => (d_dual a : ℝ))) :
    let dy := extractDualFromFlagsOfAnswer (narrowRoundInstance I s) fwdActive revActive d_dual
    let s' := narrowCostStepOfAnswers I L s delta dy
    let y' : Fin I.n → ℤ := fun v => 2 * (y v + dy v)
    RoundInvariantState I L s' y' := by
  let J := narrowRoundInstance I s
  let solve := singleAnswerSolver (extractDualFromFlagsCall J fwdActive revActive) d_dual
  let dy := extractDualFromFlagsOfAnswer J fwdActive revActive d_dual
  let s' := narrowCostStepOfAnswers I L s delta dy
  let y' : Fin I.n → ℤ := fun v => 2 * (y v + dy v)
  let j := s.round
  let yReal : Fin I.n → ℝ := fun v => stageDelta L j * (y v : ℝ)
  let yReal' : Fin I.n → ℝ := fun v => stageDelta L (j + 1) * (y' v : ℝ)
  have hdy_eq : dy = extractDualFromFlags solve J fwdActive revActive :=
    extractDualFromFlagsOfAnswer_eq J fwdActive revActive d_dual
  have hcall : (extractDualFromFlagsCall J fwdActive revActive).Optimal
      (fun a => (solve (extractDualFromFlagsCall J fwdActive revActive) a : ℝ)) := by
    simp only [solve, singleAnswerSolver_self]
    exact hdual_opt
  have hdual_corr := extractDualFromFlags_correct solve J delta fwdActive revActive
    hfwd hrev hdelta_opt hcall
  have hdual_bnds := extractDualFromFlags_bounds solve J (lowerClip I.m)
    (narrowRoundedCosts_lower_bound I s.frozen s.halfCost) delta fwdActive revActive
    hfwd hrev hdelta_opt hcall
  rw [← hdy_eq] at hdual_corr hdual_bnds
  have hδ : 0 < stageDelta L j := stageDelta_pos L j
  have hy'_eq : yReal' = fun v => yReal v + stageDelta L j * (dy v : ℝ) := by
    funext v
    dsimp only [yReal', yReal, y']
    rw [stageDelta_succ]
    push_cast
    ring
  have hflow'_cast : (fun e => (s'.flow e : ℝ)) = I.augment s.flow (fun a => (delta a : ℝ)) :=
    intAugment_cast I s.flow delta
  have hunf_floor : ∀ e, s.frozen e = .none →
      s.halfCost e = Int.floor (2 * I.reducedCost yReal e / stageDelta L j) := by
    intro e hfr
    rw [hinv.2.1 e hfr]
    exact (halfCost_eq_floor I L j y e).symm
  have hpos_clip : ∀ e, s.frozen e = .pos →
      s.flow e = 0 ∧ (upperClip I.m : ℝ) * stageDelta L j ≤ I.reducedCost yReal e := by
    intro e hfr
    exact ⟨(hinv.2.2.1 e hfr).1,
      le_trans (freezeMargin_ge_upperClip_mul_delta I.m L j) (hinv.2.2.1 e hfr).2⟩
  have hneg_clip : ∀ e, s.frozen e = .neg →
      s.flow e = (I.capacity e : ℤ) ∧
        (upperClip I.m : ℝ) * stageDelta L j ≤ -I.reducedCost yReal e := by
    intro e hfr
    exact ⟨(hinv.2.2.2.1 e hfr).1,
      le_trans (freezeMargin_ge_upperClip_mul_delta I.m L j) (hinv.2.2.2.1 e hfr).2⟩
  have herror := narrowRoundedCosts_error_for_progress I hm hn L j s yReal
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
      (stageEps L (costPrecisionExp I.m) (j + 1)) yReal' := by
    rw [hflow'_cast, hy'_eq, stageEps_succ]
    exact I.epsilonOptimalWith_augment_of_rounded_signs s.flow hinv.1.2.1
      (fun a => (delta a : ℝ)) hdelta_opt.1 yReal (fun v => stageDelta L j * (dy v : ℝ))
      (fun a => stageDelta L j * (J.cost a : ℝ))
      (stageDelta L j / 2) (stageEps L (costPrecisionExp I.m) j / 2)
      (div_pos (stageEps_pos L (costPrecisionExp I.m) j) (by norm_num))
      (stageDelta_div_two_lt_half_eps L I.m j hm)
      herror hsigns
  have hdrift : ∀ e, |I.reducedCost yReal' e - I.reducedCost yReal e| ≤
      2 * (I.m : ℝ) * stageEps L (costPrecisionExp I.m) j := by
    intro e
    rw [hy'_eq]
    exact reducedCost_drift_le I hn L j yReal dy hdual_bnds e
  have hstep_eq : ∀ e,
      (s'.frozen e, s'.halfCost e) =
        stepHalfCost (freezeThreshold I.m) (s.frozen e) (s.halfCost e)
          (costBit (I.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)))
          (dy (I.tail e) - dy (I.head e)) := fun _ => rfl
  have hfloor_next : ∀ e, s.frozen e = .none →
      2 * s.halfCost e + costBit (I.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)) -
          4 * (dy (I.tail e) - dy (I.head e)) =
        costScaled (I.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)) -
          2 * (y' (I.tail e) - y' (I.head e)) := by
    intro e hfr
    rw [hinv.2.1 e hfr]
    exact (halfCost_step_identity I L j y dy e).symm
  refine ⟨heps_next, ?_, ?_, ?_, ?_⟩
  · intro e hfr'
    have hsp := hstep_eq e
    cases hfr : s.frozen e with
    | pos =>
      rw [hfr] at hsp; simp only [stepHalfCost, Prod.mk.injEq] at hsp
      rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
    | neg =>
      rw [hfr] at hsp; simp only [stepHalfCost, Prod.mk.injEq] at hsp
      rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
    | none =>
      rw [hfr] at hsp; dsimp only [stepHalfCost] at hsp
      split at hsp
      · simp only [Prod.mk.injEq] at hsp; rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
      · split at hsp
        · simp only [Prod.mk.injEq] at hsp; rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
        · simp only [Prod.mk.injEq] at hsp; rw [hsp.2]; exact hfloor_next e hfr
  · intro e hfr'
    have hsp := hstep_eq e
    cases hfr : s.frozen e with
    | neg =>
      rw [hfr] at hsp; simp only [stepHalfCost, Prod.mk.injEq] at hsp
      rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
    | pos =>
      have hmargin : freezeMargin I.m L (costPrecisionExp I.m) (j + 1) ≤ I.reducedCost yReal' e :=
        freezeMargin_preserved I.m L j (I.reducedCost yReal e) (I.reducedCost yReal' e)
          (hinv.2.2.1 e hfr).2 (hdrift e)
      exact ⟨(flow_eq_of_freezeMargin I hm L (j + 1) s'.flow yReal' heps_next e).1 hmargin, hmargin⟩
    | none =>
      rw [hfr] at hsp; dsimp only [stepHalfCost] at hsp
      split at hsp
      · rename_i hge
        have hfl : Int.floor (2 * I.reducedCost yReal' e / stageDelta L (j + 1)) =
            2 * s.halfCost e + costBit (I.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)) -
              4 * (dy (I.tail e) - dy (I.head e)) := by
          rw [hfloor_next e hfr]
          exact halfCost_eq_floor I L (j + 1) y' e
        have hmargin := freezeMargin_of_threshold_pos I.m L (j + 1) (I.reducedCost yReal' e)
          (hfl ▸ hge)
        exact ⟨(flow_eq_of_freezeMargin I hm L (j + 1) s'.flow yReal' heps_next e).1 hmargin, hmargin⟩
      · split at hsp
        · simp only [Prod.mk.injEq] at hsp; rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
        · simp only [Prod.mk.injEq] at hsp; rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
  · intro e hfr'
    have hsp := hstep_eq e
    cases hfr : s.frozen e with
    | pos =>
      rw [hfr] at hsp; simp only [stepHalfCost, Prod.mk.injEq] at hsp
      rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
    | neg =>
      have hdrift_neg : |-I.reducedCost yReal' e - -I.reducedCost yReal e| ≤
          2 * (I.m : ℝ) * stageEps L (costPrecisionExp I.m) j := by
        have : -I.reducedCost yReal' e - -I.reducedCost yReal e =
            -(I.reducedCost yReal' e - I.reducedCost yReal e) := by ring
        rw [this, abs_neg]; exact hdrift e
      have hmargin : freezeMargin I.m L (costPrecisionExp I.m) (j + 1) ≤ -I.reducedCost yReal' e :=
        freezeMargin_preserved I.m L j (-I.reducedCost yReal e) (-I.reducedCost yReal' e)
          (hinv.2.2.2.1 e hfr).2 hdrift_neg
      exact ⟨(flow_eq_of_freezeMargin I hm L (j + 1) s'.flow yReal' heps_next e).2 hmargin, hmargin⟩
    | none =>
      rw [hfr] at hsp; dsimp only [stepHalfCost] at hsp
      split at hsp
      · simp only [Prod.mk.injEq] at hsp; rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
      · split at hsp
        · rename_i _ hle
          have hfl : Int.floor (2 * I.reducedCost yReal' e / stageDelta L (j + 1)) =
              2 * s.halfCost e + costBit (I.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)) -
                4 * (dy (I.tail e) - dy (I.head e)) := by
            rw [hfloor_next e hfr]
            exact halfCost_eq_floor I L (j + 1) y' e
          have hmargin := freezeMargin_of_threshold_neg I.m L (j + 1) hm (I.reducedCost yReal' e)
            (hfl ▸ hle)
          exact ⟨(flow_eq_of_freezeMargin I hm L (j + 1) s'.flow yReal' heps_next e).2 hmargin, hmargin⟩
        · simp only [Prod.mk.injEq] at hsp; rw [hsp.1] at hfr'; exact False.elim (FreezeState.noConfusion hfr')
  · intro e
    exact stepHalfCost_snd_abs_lt (freezeThreshold I.m) (freezeThreshold_pos I.m) _ _ _ _

/-- Exact integral optimality once `s.round = narrowCostRounds I`. -/
theorem roundInvariantState_final_optimal (I : Circulation)
    (s : NarrowCostState I) (y : Fin I.n → ℤ)
    (hround : s.round = narrowCostRounds I)
    (hinv : RoundInvariantState I (costScaleBits I) s y) :
    I.Optimal (fun e => (s.flow e : ℝ)) := by
  have heps := hinv.1
  rw [hround] at heps
  have hlt := stageEps_final_lt I
  apply I.lemma_C_5 s.flow
  exact ⟨_, I.epsilonOptimalWith_mono _ _ _ _ heps hlt.le⟩

/-! ### Arithmetic helpers for the Stage 1 program -/

/-- For a negative integer `c = -a < 0` and bit position `r : ℕ`,
`costBit c r = 1 - ((a - 1) / 2 ^ r) % 2`. -/
theorem costBit_neg_eq_sub_one {c : ℤ} (hc : c < 0) (r : ℕ) :
    costBit c (r : ℤ) = 1 - ((((c.natAbs - 1) / 2 ^ r) % 2 : ℕ) : ℤ) := by
  simp only [costBit, Nat.cast_nonneg, ↓reduceIte, Int.toNat_natCast]
  set d : ℕ := 2 ^ r
  have hd_pos : 0 < d := Nat.two_pow_pos r
  set a : ℕ := c.natAbs
  have ha_pos : 1 ≤ a := by omega
  have hc_eq : c = -(a : ℤ) := by omega
  set q : ℕ := (a - 1) / d
  set rem : ℕ := (a - 1) % d
  have hrem_lt : rem < d := Nat.mod_lt _ hd_pos
  have hdiv_nat : d * q + rem = a - 1 := Nat.div_add_mod (a - 1) d
  have hc_decomp : c = ((d - 1 - rem : ℕ) : ℤ) + (d : ℤ) * (-((q + 1 : ℕ) : ℤ)) := by
    have : (d * q + rem : ℤ) = (a : ℤ) - 1 := by exact_mod_cast hdiv_nat
    have hsub : ((d - 1 - rem : ℕ) : ℤ) = (d : ℤ) - 1 - (rem : ℤ) := by omega
    rw [hc_eq, hsub]
    push_cast
    linarith
  have hd_z : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd_pos
  have hrem_z_lo : (0 : ℤ) ≤ ((d - 1 - rem : ℕ) : ℤ) := by omega
  have hrem_z_hi : ((d - 1 - rem : ℕ) : ℤ) < (d : ℤ) := by omega
  have hquot : c / (d : ℤ) = -((q + 1 : ℕ) : ℤ) := by
    rw [hc_decomp, Int.add_mul_ediv_left _ _ (ne_of_gt hd_z),
      Int.ediv_eq_zero_of_lt hrem_z_lo hrem_z_hi, zero_add]
  change (c / (d : ℤ)) % 2 = 1 - ((q % 2 : ℕ) : ℤ)
  rw [hquot]
  rcases Nat.mod_two_eq_zero_or_one q with hq | hq
  · have hq2 : q = 2 * (q / 2) := by omega
    have hval : (-((q + 1 : ℕ) : ℤ)) = 1 + 2 * (-(((q / 2) + 1 : ℕ) : ℤ)) := by
      push_cast; omega
    rw [hval, Int.add_mul_emod_self_left, hq]
    norm_num
  · have hq2 : q = 2 * (q / 2) + 1 := by omega
    have hval : (-((q + 1 : ℕ) : ℤ)) = 0 + 2 * (-(((q / 2) + 1 : ℕ) : ℤ)) := by
      push_cast; omega
    rw [hval, Int.add_mul_emod_self_left, hq]
    norm_num

/-- For a nonnegative integer `c ≥ 0` and bit position `r : ℕ`,
`costBit c r = (c.natAbs / 2 ^ r) % 2`. -/
theorem costBit_nonneg_eq {c : ℤ} (hc : 0 ≤ c) (r : ℕ) :
    costBit c (r : ℤ) = (((c.natAbs / 2 ^ r) % 2 : ℕ) : ℤ) := by
  simp only [costBit, Nat.cast_nonneg, ↓reduceIte, Int.toNat_natCast]
  have hc_eq : c = (c.natAbs : ℤ) := by omega
  rw [hc_eq]
  norm_cast

/-- Floor division `(-mag + 1) / 2 = -(mag / 2)` for every `mag ≥ 1`. -/
theorem half_div_two_neg {mag : ℕ} (_h : 1 ≤ mag) :
    ((-(mag : ℤ) + 1) / 2 : ℤ) = -((mag / 2 : ℕ) : ℤ) := by
  rcases Nat.mod_two_eq_zero_or_one mag with h0 | h1
  · have hdecomp : -(mag : ℤ) + 1 = 1 + 2 * (-((mag / 2 : ℕ) : ℤ)) := by omega
    rw [hdecomp, Int.add_mul_ediv_left _ _ (by decide : (2 : ℤ) ≠ 0)]
    norm_num
  · have hdecomp : -(mag : ℤ) + 1 = 0 + 2 * (-((mag / 2 : ℕ) : ℤ)) := by omega
    rw [hdecomp, Int.add_mul_ediv_left _ _ (by decide : (2 : ℤ) ≠ 0)]
    norm_num

/-- Equivalence between `Finset.univ.sup f` and `List.foldr max 0` over limb values. -/
private lemma sup_eq_foldr_max {m : ℕ} (f : Fin m → ℕ) (ls : List (List ℕ)) (k : ℕ)
    (hlen : ls.length = m)
    (hval : ∀ j (hj : j < m), Nat.ofDigits (2 ^ k) (ls[j]'(by omega)) = f ⟨j, hj⟩) :
    Finset.univ.sup f = maxLimbsVal k ls := by
  unfold maxLimbsVal
  apply le_antisymm
  · apply Finset.sup_le
    intro e _
    have hmem : f e ∈ ls.map (Nat.ofDigits (2 ^ k)) :=
      List.mem_map.mpr ⟨ls[e.val]'(by omega), List.getElem_mem _, hval e.val e.isLt⟩
    generalize hxs : ls.map (Nat.ofDigits (2 ^ k)) = xs at hmem ⊢
    clear hxs hval hlen
    induction xs with
    | nil => cases hmem
    | cons x xs ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact le_max_left _ _
      · exact le_trans (ih hmem') (le_max_right _ _)
  · suffices ∀ l : List ℕ, (∀ x ∈ l, x ≤ Finset.univ.sup f) → l.foldr max 0 ≤ Finset.univ.sup f by
      apply this
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
      rw [hval j (by omega)]
      exact Finset.le_sup (f := f) (Finset.mem_univ (Fin.mk j (by omega)))
    intro l hl
    induction l with
    | nil => exact Nat.zero_le _
    | cons x xs ih =>
      simp only [List.foldr_cons]
      exact max_le (hl x List.mem_cons_self) (ih fun y hy => hl y (List.mem_cons_of_mem _ hy))

/-- `circMaxCost I` equals `maxLimbsVal k costLimbs`. -/
theorem circMaxCost_eq_maxLimbsVal (I : Circulation) (k : ℕ) (costLimbs : List (List ℕ))
    (hlen : costLimbs.length = I.m)
    (hval : ∀ j (hj : j < I.m),
      Nat.ofDigits (2 ^ k) (costLimbs[j]'(by omega)) = (I.cost ⟨j, hj⟩).natAbs) :
    circMaxCost I = maxLimbsVal k costLimbs :=
  sup_eq_foldr_max (fun e => (I.cost e).natAbs) costLimbs k hlen hval

/-- `circMaxCapacity I` equals `maxLimbsVal k capLimbs`. -/
theorem circMaxCapacity_eq_maxLimbsVal (I : Circulation) (k : ℕ) (capLimbs : List (List ℕ))
    (hlen : capLimbs.length = I.m)
    (hval : ∀ j (hj : j < I.m),
      Nat.ofDigits (2 ^ k) (capLimbs[j]'(by omega)) = I.capacity ⟨j, hj⟩) :
    circMaxCapacity I = maxLimbsVal k capLimbs :=
  sup_eq_foldr_max I.capacity capLimbs k hlen hval

/-- Every canonical limb list of a value `< 2 ^ T` has length at most `T / k + 2`. -/
theorem canonical_length_le_div_add_two {k T : ℕ} (hk : 1 ≤ k) {l : List ℕ}
    (hC : CanonicalLimbs k l) (hlt : Nat.ofDigits (2 ^ k) l < 2 ^ T) :
    l.length ≤ T / k + 2 := by
  by_cases h0 : l.length = 0
  · rw [h0]; exact Nat.zero_le _
  · have hpos : 0 < l.length := Nat.pos_of_ne_zero h0
    have hsize := size_ofDigits_canonical hC hpos
    have hle_T : Nat.size (Nat.ofDigits (2 ^ k) l) ≤ T := Nat.size_le.mpr hlt
    have h1 : (l.length - 1) * k ≤ T := by omega
    have h2 : l.length - 1 ≤ T / k := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr h1
    omega

/-- `2 ^ T < (2 ^ k) ^ (T / k + 2)` for every `k ≥ 1`. -/
theorem two_pow_lt_base_pow_Kcap {k : ℕ} (hk : 1 ≤ k) (T : ℕ) :
    2 ^ T < (2 ^ k) ^ (T / k + 2) := by
  rw [← pow_mul]
  apply Nat.pow_lt_pow_right (by decide)
  have hmod : T % k < k := Nat.mod_lt T (by omega)
  have hdiv : k * (T / k) + T % k = T := Nat.div_add_mod T k
  rw [Nat.mul_add]
  omega

/-- Residual capacities of any feasible flow are bounded by `circMaxCapacity I`. -/
theorem circMaxCapacity_narrowRound_le (I : Circulation) (s : NarrowCostState I)
    (hf : ∀ e, 0 ≤ s.flow e ∧ s.flow e ≤ (I.capacity e : ℤ)) :
    circMaxCapacity (narrowRoundInstance I s) ≤ circMaxCapacity I := by
  unfold circMaxCapacity
  apply Finset.sup_le
  intro a _
  refine Fin.addCases (m := I.m) (n := I.m) (fun e => ?_) (fun e => ?_) a
  · have hfe := hf e
    have hle : (narrowRoundInstance I s).capacity (Fin.castAdd I.m e) ≤ I.capacity e := by
      simp only [Fin.addCases_left]; omega
    exact le_trans hle (Finset.le_sup (f := I.capacity) (Finset.mem_univ e))
  · have hfe := hf e
    have hle : (narrowRoundInstance I s).capacity (Fin.natAdd I.m e) ≤ I.capacity e := by
      simp only [Fin.addCases_right]; omega
    exact le_trans hle (Finset.le_sup (f := I.capacity) (Finset.mem_univ e))

end MinCostFlow.Narrow
