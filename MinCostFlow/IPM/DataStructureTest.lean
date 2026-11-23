module

public import MinCostFlow.IPM.GuardedEpoch
public import MinCostFlow.IPM.EpochLoop
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Bounded target tests using the actual dynamic data structure

The binary search proposed in Section 4 of Chen et al.,
arXiv:2203.00671v2 (page 24), can use guarded epochs rather than an
assumed comparison oracle or an exact permitted-step selector. A wrong
guess may fail a reported-coordinate check or exhaust its epoch budget.
A successful test returns a proved feasible flow of cost at most `F+1/4`.
For every upper guess, all guards pass and the repeated-epoch potential
bound forces success. No hidden-stability assertion for failed guesses
is part of this target-test correctness result.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- Run at most `fuel` guarded epochs, accepting at full refreshes when
the cost is at most one quarter above the target. Failed guards reject. -/
def boundedTargetRun (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure) :
    ℕ → (Fin I.m → ℝ) → Option (Fin I.m → ℝ)
  | 0, base => by
    classical
    exact if residual I F base ≤ 1/4 then some base else none
  | n+1, base => by
    classical
    exact if residual I F base ≤ 1/4 then some base else
      match epochFirstFailure I U κ (residual I F base) A base I.m with
      | some _ => none
      | none => boundedTargetRun I U F κ A n (epochFlow I U κ (residual I F base) A base I.m)

/-- Every successful actual-data-structure test is feasible and meets
its target threshold, including when the guess is below the optimum. -/
theorem boundedTargetRun_sound (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure)
    (fuel : ℕ) (base g : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ))
    (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hout : boundedTargetRun I U F κ A fuel base = some g) :
    I.IsFeasible g ∧ I.cost g ≤ F+1/4 := by
  classical
  have he := epoch_tolerance_bounds I U κ hsize hk hk'
  have he' : ipmDetectThreshold I U κ ≤ 1/100 := by linarith only [he.2.1]
  induction fuel generalizing base with
  | zero =>
    unfold boundedTargetRun at hout
    split_ifs at hout with hstop
    · have heq := Option.some.inj hout
      subst g
      exact ⟨feasible_of_inside I _ hroute hbase, by dsimp only [residual] at hstop; linarith only [hstop]⟩
  | succ fuel ih =>
    unfold boundedTargetRun at hout
    split_ifs at hout with hstop
    · have heq := Option.some.inj hout
      subst g
      exact ⟨feasible_of_inside I _ hroute hbase, by dsimp only [residual] at hstop; linarith only [hstop]⟩
    · cases hscan : epochFirstFailure I U κ (residual I F base) A base I.m with
      | some k => rw [hscan] at hout; contradiction
      | none =>
        rw [hscan] at hout
        have hguards := (epochFirstFailure_none_iff I U κ (residual I F base) A base I.m).mp hscan
        have hnew := guardedEpoch_feasible I U κ (residual I F base) (normalizedIpmAlpha I) (ipmPsi I U)
          (ipmDetectThreshold I U κ) A base I.m hI hm hU hsize hnums he.1.le he' hbase hroute hA hscan
        have hins := epoch_guards_inside I U κ (residual I F base) (normalizedIpmAlpha I) (ipmPsi I U)
          (ipmDetectThreshold I U κ) A base I.m hI hm hU hsize hnums he.1.le he' hbase hA
          (fun j hj => (hguards j hj).1)
        exact ih _ hins hnew.1 hout

private theorem ipmEpochBase_restart (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n : ℕ) :
    ipmEpochBase I U F κ A base (n+1) =
      ipmEpochBase I U F κ A (ipmEpochBase I U F κ A base 1) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (if residual I F (ipmEpochBase I U F κ A base (n+1)) ≤ 1/4 then _ else _) =
      (if residual I F (ipmEpochBase I U F κ A (ipmEpochBase I U F κ A base 1) n) ≤ 1/4 then _ else _)
    rw [ih]

private theorem boundedTargetRun_complete_of_terminal (I : Instance) (U F κ : ℝ)
    (A : MinRatioDataStructure) (fuel : ℕ) (base fstar : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ))
    (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hpot : 0 < residual I F base → potential I (alpha I U) F base ≤ 200*I.m*Real.log (I.m*U))
    (hterminal : residual I F (ipmEpochBase I U F κ A base fuel) ≤ 1/4) :
    (boundedTargetRun I U F κ A fuel base).isSome = true := by
  classical
  induction fuel generalizing base with
  | zero =>
    have hh : residual I F base ≤ 1/4 := hterminal
    simp only [boundedTargetRun, hh, ↓reduceIte, Option.isSome_some]
  | succ fuel ih =>
    by_cases hstop : residual I F base ≤ 1/4
    · simp only [boundedTargetRun, hstop, ↓reduceIte, Option.isSome_some]
    · have hstart : (1/4 : ℝ) < residual I F base := lt_of_not_ge hstop
      have hpos : 0 < residual I F base := lt_trans (by norm_num) hstart
      have hscan := epochFirstFailure_upper I U F κ A base fstar hI hm hU hsize hnums hk hk' hs hF
        hbase hroute hstart (hpot hpos) hA
      have hepoch := epoch_correct I U F κ A base fstar hI hm hU hsize hnums hk hk' hs hF
        hbase hroute hstart (hpot hpos) hA
      dsimp only at hepoch
      have hnewpot : potential I (alpha I U) F (epochFlow I U κ (residual I F base) A base I.m) ≤
          200*I.m*Real.log (I.m*U) := by
        have hdrop0 : 0 ≤ (I.m : ℝ)*((κ*alpha I U/64)^2/500) :=
          mul_nonneg (Nat.cast_nonneg _) (div_nonneg (sq_nonneg _) (by norm_num))
        linarith only [hepoch.2.2.2.1, hpot hpos, hdrop0]
      have hfirst : ipmEpochBase I U F κ A base 1 = epochFlow I U κ (residual I F base) A base I.m := by
        simp only [ipmEpochBase, hstop, ↓reduceIte]
      have hrest : residual I F (ipmEpochBase I U F κ A
          (epochFlow I U κ (residual I F base) A base I.m) fuel) ≤ 1/4 := by
        rw [ipmEpochBase_restart, hfirst] at hterminal
        exact hterminal
      have hrec := ih _ hepoch.2.1 hepoch.1.1 (fun _ => hnewpot) hrest
      simpa only [boundedTargetRun, hstop, ↓reduceIte, hscan] using hrec

/-- The actual guarded test with the explicit epoch budget. -/
def dataStructureGuessTest (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) : Option (Fin I.m → ℝ) :=
  boundedTargetRun I U F κ A (ipmEpochLimit I U κ) base

/-- Every upper target guess is accepted by the actual dynamic-data-
structure test. This replaces the complete permitted-step selector of
the earlier mathematical search model. -/
theorem dataStructureGuessTest_complete (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure)
    (base fstar : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ))
    (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hpot : 0 < residual I F base → potential I (alpha I U) F base ≤ 200*I.m*Real.log (I.m*U)) :
    (dataStructureGuessTest I U F κ A base).isSome = true := by
  classical
  by_cases hstop : residual I F base ≤ 1/4
  · cases hn : ipmEpochLimit I U κ with
    | zero => simp only [dataStructureGuessTest, hn, boundedTargetRun, hstop, ↓reduceIte, Option.isSome_some]
    | succ n => simp only [dataStructureGuessTest, hn, boundedTargetRun, hstop, ↓reduceIte, Option.isSome_some]
  · have hr : 0 < residual I F base := lt_trans (by norm_num) (lt_of_not_ge hstop)
    have hterm := ipmEpochBase_terminates I U F κ A base fstar hI hm hU hsize hnums hk hk'
      hs hF hbase hroute hr (hpot hr) hA
    have hterminal : residual I F (ipmEpochBase I U F κ A base (ipmEpochLimit I U κ)) ≤ 1/4 := by
      dsimp only [residual]
      linarith only [hterm.2]
    exact boundedTargetRun_complete_of_terminal I U F κ A _ base fstar hI hm hU hsize hnums hk hk'
      hs hF hA hbase hroute hpot hterminal

end MinCostFlow.IPM
