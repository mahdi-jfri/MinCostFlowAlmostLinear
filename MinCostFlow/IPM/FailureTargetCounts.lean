module

public import MinCostFlow.IPM.FailureTargetTest
public import MinCostFlow.IPM.FailureEpochCounts
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Operation counts for failure-aware bounded target tests

Only attempted epochs contribute a charge. Explicit failure stops the
test before further data structure operations. A completed epoch passed
the original local guards, so its next base remains interior even for a
wrong target. Consequently the per-epoch bounds sum over every actual
attempt. This is the failed-test accounting required by the restatement
of Theorem 4.6 (page 15).
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- Sum charges over epochs actually attempted by the failure-aware
bounded target test. The first failure prevents every later attempt. -/
def boundedFailureTargetCharge (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructureWithFailure)
    (charge : (Fin I.m → ℝ) → ℕ) : ℕ → (Fin I.m → ℝ) → ℕ
  | 0, _ => 0
  | n+1, base => by
    classical
    exact if residual I F base ≤ 1/4 then 0 else
      charge base+match epochFirstFailureWithAnswer I U κ (residual I F base) A base I.m with
      | some _ => 0
      | none => boundedFailureTargetCharge I U F κ A charge n
          (epochFlow I U κ (residual I F base) A.eraseFailure base I.m)

/-- Per-epoch bounds sum over all attempted epochs, including those on
wrong targets. Passing an epoch preserves the next base's domain. -/
theorem boundedFailureTargetCharge_le (I : Instance) (U F κ α Ψ ε : ℝ)
    (A : MinRatioDataStructureWithFailure) (charge : (Fin I.m → ℝ) → ℕ) (K fuel : ℕ)
    (base : Fin I.m → ℝ) (hI : I.IsValid) (hm : 0 < I.m) (hU : 0 ≤ U)
    (hsize : 2 ≤ (I.m : ℝ)*U) (hnums : NumbersBounded I U)
    (he : 0 ≤ ε) (he' : ε ≤ 1/100) (hA : MinRatioSpecWithFailure A κ α Ψ ε)
    (hbase : StrictlyInside I base)
    (hcharge : ∀ f, StrictlyInside I f → charge f ≤ K) :
    boundedFailureTargetCharge I U F κ A charge fuel base ≤ K*fuel := by
  classical
  induction fuel generalizing base with
  | zero => simp only [boundedFailureTargetCharge, Nat.mul_zero, le_refl]
  | succ fuel ih =>
    by_cases hstop : residual I F base ≤ 1/4
    · simp only [boundedFailureTargetCharge, hstop, ↓reduceIte, Nat.zero_le]
    · have hc := hcharge base hbase
      cases hscan : epochFirstFailureWithAnswer I U κ (residual I F base) A base I.m with
      | some k =>
        simp only [boundedFailureTargetCharge, hstop, ↓reduceIte, hscan, Nat.add_zero]
        have hh : K ≤ K*(fuel+1) := by rw [Nat.mul_add, Nat.mul_one]; omega
        exact hc.trans hh
      | none =>
        have hold := epochFirstFailureWithAnswer_none_old I U κ (residual I F base) A base I.m hscan
        have hg := (epochFirstFailure_none_iff I U κ (residual I F base) A.eraseFailure base I.m).mp hold
        have hins := epoch_guards_inside I U κ (residual I F base) α Ψ ε A.eraseFailure base I.m hI hm
          hU hsize hnums he he' hbase hA.1 (fun j hj => (hg j hj).1)
        have hp := ih _ hins
        simp only [boundedFailureTargetCharge, hstop, ↓reduceIte, hscan, Nat.mul_add, Nat.mul_one]
        omega

/-- Charge of the Update calls in one attempted target epoch. -/
def failureTargetUpdateCalls (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructureWithFailure)
    (base : Fin I.m → ℝ) : ℕ := epochProcessedWithAnswer I U κ (residual I F base) A base I.m

/-- Charge of Detect calls, excluding an explicitly failed Update's
unfinished pair. -/
def failureTargetDetectCalls (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructureWithFailure)
    (base : Fin I.m → ℝ) : ℕ := epochCompletedWithAnswer I U κ (residual I F base) A base I.m

/-- Coordinate Queries, with a full final read only on successful epochs. -/
def failureTargetQueryCalls (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructureWithFailure)
    (base : Fin I.m → ℝ) : ℕ := failureEpochQueryCount I U κ (residual I F base) A base I.m

/-- Primitive coefficient update entries, including the failed Update's
input batch. -/
def failureTargetUpdateSize (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructureWithFailure)
    (base : Fin I.m → ℝ) : ℕ := failureEpochUpdateSize I U κ (residual I F base) A base I.m

/-- Detect output entries, counting only completed Detect calls. -/
def failureTargetDetectSize (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructureWithFailure)
    (base : Fin I.m → ℝ) : ℕ := failureEpochDetectSize I U κ (residual I F base) A base I.m

/-- Every target run uses at most `fuel` initializations, `m·fuel`
Update calls and Detect calls, `7m·fuel` Queries, `12m·fuel` primitive
updates and `6m·fuel` Detect output entries. Explicit failures and all
wrong guesses are included, without a hidden-stability assumption. -/
theorem boundedFailureTargetRun_operation_bounds (I : Instance) (U F κ : ℝ)
    (A : MinRatioDataStructureWithFailure) (base : Fin I.m → ℝ) (fuel : ℕ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hA : MinRatioSpecWithFailure A κ (normalizedIpmAlpha I) (ipmPsi I U)
      (ipmDetectThreshold I U κ)) (hbase : StrictlyInside I base) :
    boundedFailureTargetCharge I U F κ A (fun _ => 1) fuel base ≤ fuel ∧
      boundedFailureTargetCharge I U F κ A (failureTargetUpdateCalls I U F κ A) fuel base ≤ I.m*fuel ∧
      boundedFailureTargetCharge I U F κ A (failureTargetDetectCalls I U F κ A) fuel base ≤ I.m*fuel ∧
      boundedFailureTargetCharge I U F κ A (failureTargetQueryCalls I U F κ A) fuel base ≤ 7*I.m*fuel ∧
      boundedFailureTargetCharge I U F κ A (failureTargetUpdateSize I U F κ A) fuel base ≤ 12*I.m*fuel ∧
      boundedFailureTargetCharge I U F κ A (failureTargetDetectSize I U F κ A) fuel base ≤ 6*I.m*fuel := by
  have he := epoch_tolerance_bounds I U κ hsize hk hk'
  have he' : ipmDetectThreshold I U κ ≤ 1/100 := by linarith only [he.2.1]
  have hc := fun K charge => boundedFailureTargetCharge_le I U F κ (normalizedIpmAlpha I)
    (ipmPsi I U) (ipmDetectThreshold I U κ) A charge K fuel base hI hm hU hsize hnums
    he.1.le he' hA hbase
  have hper := fun f hf => failureEpoch_operation_bounds I U κ (residual I F f)
    (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ) A f I.m hI hf hA
  refine ⟨?_, hc I.m _ (fun f hf => (hper f hf).1),
    hc I.m _ (fun f hf => (hper f hf).2.1),
    hc (7*I.m) _ (fun f hf => (hper f hf).2.2.1),
    hc (12*I.m) _ (fun f hf => (hper f hf).2.2.2.2),
    hc (6*I.m) _ (fun f hf => (hper f hf).2.2.2.1)⟩
  simpa only [Nat.one_mul] using hc 1 (fun _ => 1) (fun _ _ => le_rfl)

end MinCostFlow.IPM
