module

public import MinCostFlow.IPM.FailureEpochCorrect
public import MinCostFlow.IPM.DataStructureTest
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Target tests that stop on an explicit failure

The restated Theorem 4.6 uses the guarded binary-search test with the
extended Definition 4.5. An Update failure rejects its target immediately,
before Detect or Query. A successful test has the same feasible-flow
certificate as before. On every upper target, the no-failure theorem
makes this test identical to the already proved bounded IPM run.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- Run bounded epochs, rejecting at the first explicit failure or local
guard failure. The data structure is not called again in a rejected test. -/
def boundedFailureTargetRun (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructureWithFailure) :
    ℕ → (Fin I.m → ℝ) → Option (Fin I.m → ℝ)
  | 0, base => by
    classical
    exact if residual I F base ≤ 1/4 then some base else none
  | n+1, base => by
    classical
    exact if residual I F base ≤ 1/4 then some base else
      match epochFirstFailureWithAnswer I U κ (residual I F base) A base I.m with
      | some _ => none
      | none => boundedFailureTargetRun I U F κ A n
          (epochFlow I U κ (residual I F base) A.eraseFailure base I.m)

/-- An accepted failure-aware run is also accepted by its mathematical
zero-increment projection. This implication uses no hidden promise. -/
theorem boundedFailureTargetRun_success_old (I : Instance) (U F κ : ℝ)
    (A : MinRatioDataStructureWithFailure) (fuel : ℕ) (base g : Fin I.m → ℝ)
    (hout : boundedFailureTargetRun I U F κ A fuel base = some g) :
    boundedTargetRun I U F κ A.eraseFailure fuel base = some g := by
  classical
  induction fuel generalizing base with
  | zero => exact hout
  | succ fuel ih =>
    by_cases hstop : residual I F base ≤ 1/4
    · simpa only [boundedFailureTargetRun, boundedTargetRun, hstop, ↓reduceIte] using hout
    · simp only [boundedFailureTargetRun, hstop, ↓reduceIte] at hout
      cases hscan : epochFirstFailureWithAnswer I U κ (residual I F base) A base I.m with
      | some k => rw [hscan] at hout; cases hout
      | none =>
        rw [hscan] at hout
        have ho := epochFirstFailureWithAnswer_none_old I U κ (residual I F base) A base I.m hscan
        simp only [boundedTargetRun, hstop, ↓reduceIte, ho]
        exact ih _ hout

/-- Every accepted test returns a feasible flow of cost at most `F+1/4`,
even when its target is wrong. Failure is not treated as a feasible flow. -/
theorem boundedFailureTargetRun_sound (I : Instance) (U F κ : ℝ)
    (A : MinRatioDataStructureWithFailure) (fuel : ℕ) (base g : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hA : MinRatioSpecWithFailure A κ (normalizedIpmAlpha I) (ipmPsi I U)
      (ipmDetectThreshold I U κ))
    (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hout : boundedFailureTargetRun I U F κ A fuel base = some g) :
    I.IsFeasible g ∧ I.cost g ≤ F+1/4 := by
  exact boundedTargetRun_sound I U F κ A.eraseFailure fuel base g hI hm hU hsize hnums hk hk'
    hA.1 hbase hroute (boundedFailureTargetRun_success_old I U F κ A fuel base g hout)

/-- On an upper target the new test is exactly the old IPM run. Its
hidden prefixes rule out explicit failure, and its numeric guards pass. -/
theorem boundedFailureTargetRun_eq_upper (I : Instance) (U F κ : ℝ)
    (A : MinRatioDataStructureWithFailure) (fuel : ℕ) (base fstar : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hA : MinRatioSpecWithFailure A κ (normalizedIpmAlpha I) (ipmPsi I U)
      (ipmDetectThreshold I U κ))
    (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hpot : 0 < residual I F base → potential I (alpha I U) F base ≤ 200*I.m*Real.log (I.m*U)) :
    boundedFailureTargetRun I U F κ A fuel base = boundedTargetRun I U F κ A.eraseFailure fuel base := by
  classical
  induction fuel generalizing base with
  | zero => rfl
  | succ fuel ih =>
    by_cases hstop : residual I F base ≤ 1/4
    · simp only [boundedFailureTargetRun, boundedTargetRun, hstop, ↓reduceIte]
    · have hstart : (1/4 : ℝ) < residual I F base := lt_of_not_ge hstop
      have hpos : 0 < residual I F base := lt_trans (by norm_num) hstart
      have hscan := epochFirstFailureWithAnswer_upper I U F κ A base fstar hI hm hU hsize hnums
        hk hk' hs hF hbase hroute hstart (hpot hpos) hA
      have ho := epochFirstFailureWithAnswer_none_old I U κ (residual I F base) A base I.m hscan
      have hep := epoch_correct I U F κ A.eraseFailure base fstar hI hm hU hsize hnums hk hk' hs hF
        hbase hroute hstart (hpot hpos) hA.1
      dsimp only at hep
      have hnextpot : potential I (alpha I U) F
          (epochFlow I U κ (residual I F base) A.eraseFailure base I.m) ≤
          200*I.m*Real.log (I.m*U) := by
        have hnonneg : 0 ≤ (I.m : ℝ)*((κ*alpha I U/64)^2/500) :=
          mul_nonneg (Nat.cast_nonneg _) (div_nonneg (sq_nonneg _) (by norm_num))
        linarith only [hep.2.2.2.1, hpot hpos, hnonneg]
      simp only [boundedFailureTargetRun, boundedTargetRun, hstop, ↓reduceIte, hscan, ho]
      exact ih _ hep.2.1 hep.1.1 (fun _ => hnextpot)

/-- The failure-aware comparison test, with the same explicit epoch
budget as the source IPM analysis. -/
def failureAwareGuessTest (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructureWithFailure)
    (base : Fin I.m → ℝ) : Option (Fin I.m → ℝ) :=
  boundedFailureTargetRun I U F κ A (ipmEpochLimit I U κ) base

/-- Every upper target is accepted. Hence an explicit failure or any
other rejection is sound evidence that the target is below the optimum. -/
theorem failureAwareGuessTest_complete (I : Instance) (U F κ : ℝ)
    (A : MinRatioDataStructureWithFailure) (base fstar : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hA : MinRatioSpecWithFailure A κ (normalizedIpmAlpha I) (ipmPsi I U)
      (ipmDetectThreshold I U κ))
    (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hpot : 0 < residual I F base → potential I (alpha I U) F base ≤ 200*I.m*Real.log (I.m*U)) :
    (failureAwareGuessTest I U F κ A base).isSome = true := by
  unfold failureAwareGuessTest
  rw [boundedFailureTargetRun_eq_upper I U F κ A _ base fstar hI hm hU hsize hnums hk hk'
    hs hF hA hbase hroute hpot]
  exact dataStructureGuessTest_complete I U F κ A.eraseFailure base fstar hI hm hU hsize hnums
    hk hk' hs hF hA.1 hbase hroute hpot

/-- A rejected target, including an explicit Update failure, lies
strictly below the optimal value. This follows from upper-target
completeness, without a promise on the rejected input sequence. -/
theorem failureAwareGuessTest_reject (I : Instance) (U F κ : ℝ)
    (A : MinRatioDataStructureWithFailure) (base fstar : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsMinCostFlow fstar)
    (hA : MinRatioSpecWithFailure A κ (normalizedIpmAlpha I) (ipmPsi I U)
      (ipmDetectThreshold I U κ))
    (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hpot : 0 < residual I F base → potential I (alpha I U) F base ≤ 200*I.m*Real.log (I.m*U))
    (hreject : failureAwareGuessTest I U F κ A base = none) : F < I.cost fstar := by
  by_contra hn
  have hh := failureAwareGuessTest_complete I U F κ A base fstar hI hm hU hsize hnums hk hk'
    hs.1 (not_lt.mp hn) hA hbase hroute hpot
  rw [hreject] at hh
  contradiction

end MinCostFlow.IPM
