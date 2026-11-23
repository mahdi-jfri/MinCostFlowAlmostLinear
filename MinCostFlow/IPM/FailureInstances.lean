module

public import MinCostFlow.IPM.FailureTargetCounts
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Input prefixes of failure-aware target tests

The restated Theorem 4.6 claims hidden stability only for tests whose
target is at least the optimum. Every tested input is still a valid
operation history. A failed Update ends its epoch at an odd stage,
without a following Detect. The transcript below therefore uses the
sum of attempted Updates and completed Detect calls as its horizon.
Upper-target epochs complete, so their full hidden-stability proof
from the adapted Lemmas 9.1--9.4 applies unchanged.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- The exact instance prefixes evaluated by a bounded failure-aware
target test. A failed Update contributes no later Detect stage. -/
def boundedFailureTargetInstances (I : Instance) (U F κ : ℝ)
    (A : MinRatioDataStructureWithFailure) : ℕ → (Fin I.m → ℝ) → List (DynamicInstance × ℕ)
  | 0, _ => []
  | n+1, base => by
    classical
    exact if residual I F base ≤ 1/4 then [] else
      (epochInstance I U κ (residual I F base) A.eraseFailure base,
        epochProcessedWithAnswer I U κ (residual I F base) A base I.m+
          epochCompletedWithAnswer I U κ (residual I F base) A base I.m)::
      match epochFirstFailureWithAnswer I U κ (residual I F base) A base I.m with
      | some _ => []
      | none => boundedFailureTargetInstances I U F κ A n
          (epochFlow I U κ (residual I F base) A.eraseFailure base I.m)

/-- Every prefix actually fed to the extended data structure is valid,
including one ending at an explicit failure. No hidden witness is
required for a wrong target's input validity. -/
theorem boundedFailureTargetInstances_valid (I : Instance) (U F κ : ℝ)
    (A : MinRatioDataStructureWithFailure) (fuel : ℕ) (base : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hA : MinRatioSpecWithFailure A κ (normalizedIpmAlpha I) (ipmPsi I U)
      (ipmDetectThreshold I U κ)) (hbase : StrictlyInside I base) :
    ∀ p ∈ boundedFailureTargetInstances I U F κ A fuel base,
      MinRatioHistoryValid p.1 epochIsUpdate p.2 := by
  classical
  have he := epoch_tolerance_bounds I U κ hsize hk hk'
  have he' : ipmDetectThreshold I U κ ≤ 1/100 := by linarith only [he.2.1]
  induction fuel generalizing base with
  | zero => intro p hp; exact False.elim (List.not_mem_nil hp)
  | succ fuel ih =>
    by_cases hstop : residual I F base ≤ 1/4
    · simp only [boundedFailureTargetInstances, hstop, ↓reduceIte, List.not_mem_nil,
        false_implies, implies_true]
    · have hv := guardedEpoch_history_valid I U κ (residual I F base) A.eraseFailure base I.m hI hbase
      have hu := epochProcessedWithAnswer_le I U κ (residual I F base) A base I.m
      have hd := epochCompletedWithAnswer_le I U κ (residual I F base) A base I.m
      have hhead := MinRatioHistoryValid.mono _ epochIsUpdate _
        (epochProcessedWithAnswer I U κ (residual I F base) A base I.m+
          epochCompletedWithAnswer I U κ (residual I F base) A base I.m) hv (by omega)
      cases hscan : epochFirstFailureWithAnswer I U κ (residual I F base) A base I.m with
      | some k =>
        simp only [boundedFailureTargetInstances, hstop, ↓reduceIte, hscan, List.mem_cons,
          List.not_mem_nil, or_false]
        intro p hp
        subst p
        exact hhead
      | none =>
        have hold := epochFirstFailureWithAnswer_none_old I U κ (residual I F base) A base I.m hscan
        have hall := (epochFirstFailure_none_iff I U κ (residual I F base) A.eraseFailure base I.m).mp hold
        have hins := epoch_guards_inside I U κ (residual I F base) (normalizedIpmAlpha I)
          (ipmPsi I U) (ipmDetectThreshold I U κ) A.eraseFailure base I.m hI hm hU hsize hnums
          he.1.le he' hbase hA.1 (fun j hj => (hall j hj).1)
        have htail := ih _ hins
        simp only [boundedFailureTargetInstances, hstop, ↓reduceIte, hscan, List.mem_cons]
        intro p hp
        rcases hp with rfl | hp
        · exact hhead
        · exact htail p hp

/-- Every evaluated prefix of an upper-target test is hidden stable
with the normalized parameter and explicit `ipmPsi`. This is the
stability claim in the restated Theorem 4.6; no such claim is made
about rejected lower-target tests. -/
theorem boundedFailureTargetInstances_upper (I : Instance) (U F κ : ℝ)
    (A : MinRatioDataStructureWithFailure) (fuel : ℕ) (base fstar : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hA : MinRatioSpecWithFailure A κ (normalizedIpmAlpha I) (ipmPsi I U)
      (ipmDetectThreshold I U κ))
    (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hpot : 0 < residual I F base → potential I (alpha I U) F base ≤ 200*I.m*Real.log (I.m*U)) :
    ∀ p ∈ boundedFailureTargetInstances I U F κ A fuel base,
      p.1.HiddenStable p.2 (normalizedIpmAlpha I) (ipmPsi I U) := by
  classical
  induction fuel generalizing base with
  | zero => intro p hp; exact False.elim (List.not_mem_nil hp)
  | succ fuel ih =>
    by_cases hstop : residual I F base ≤ 1/4
    · simp only [boundedFailureTargetInstances, hstop, ↓reduceIte, List.not_mem_nil,
        false_implies, implies_true]
    · have hstart : (1/4 : ℝ) < residual I F base := lt_of_not_ge hstop
      have hpos : 0 < residual I F base := lt_trans (by norm_num) hstart
      have hscan := epochFirstFailureWithAnswer_upper I U F κ A base fstar hI hm hU hsize hnums
        hk hk' hs hF hbase hroute hstart (hpot hpos) hA
      have hep := epoch_correct I U F κ A.eraseFailure base fstar hI hm hU hsize hnums hk hk' hs hF
        hbase hroute hstart (hpot hpos) hA.1
      dsimp only at hep
      have hnextpot : potential I (alpha I U) F
          (epochFlow I U κ (residual I F base) A.eraseFailure base I.m) ≤
          200*I.m*Real.log (I.m*U) := by
        have hnonneg : 0 ≤ (I.m : ℝ)*((κ*alpha I U/64)^2/500) :=
          mul_nonneg (Nat.cast_nonneg _) (div_nonneg (sq_nonneg _) (by norm_num))
        linarith only [hep.2.2.2.1, hpot hpos, hnonneg]
      have htail := ih _ hep.2.1 hep.1.1 (fun _ => hnextpot)
      simp only [boundedFailureTargetInstances, hstop, ↓reduceIte,
        epochProcessedWithAnswer, epochCompletedWithAnswer, hscan, Option.getD_none, List.mem_cons]
      intro p hp
      rcases hp with rfl | hp
      · simpa only [two_mul] using hep.2.2.2.2.1
      · exact htail p hp

end MinCostFlow.IPM
