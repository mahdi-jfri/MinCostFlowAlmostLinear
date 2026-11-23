module

public import MinCostFlow.IPM.Machine.EpochCompleteFlow
public import MinCostFlow.IPM.Machine.EpochAnalyticPrefix
import MinCostFlow.IPM.Machine.EpochProgressBound

/-!
# Progress of the flow that the complete epoch stores

The materialized flow is the exact last flow of the certified sequence.
On a promised target the potential decrease therefore holds for the
stored coordinates passed to the next stage.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Transport the dyadic decrease to the actual materialized flow at
the end of an accepted epoch. -/
theorem targetEpoch_materialized_progress_at_range {τ : Type} (I : Instance) (U finish E : ℕ)
    (target κ r : ℝ) (A : MinRatioDataStructureWithFailure)
    (base flow : Fin I.m → ℝ) (Q : EpochPoint τ)
    (hflow : flow=epochHistoryFlow I A Q.history Q.eta Q.op (2*finish) base)
    (hcert : EpochAnalyticPrefixAt I U E target κ r A base finish Q)
    (hm : 0<I.m) (hi : finish≤I.m) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U)
    (hq : 0<κ*Num.IPM.alphaPrime I.m U/32) (hq' : κ*Num.IPM.alphaPrime I.m U/32≤1/2)
    (hf : StrictlyInside I base) (hroute : I.Routes base) (hr : 0<residual I target base)
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target base≤200*I.m*Real.log (I.m*(U:ℝ))) :
    potential I (Num.IPM.alphaPrime I.m U) target flow≤
      potential I (Num.IPM.alphaPrime I.m U) target base-
        (finish:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/2000 := by
  rw [hflow]
  exact epoch_dyadic_progress I U finish target _ A Q.history Q.eta Q.op base hm hi hsize hnums
    hq hq' hf hroute hr hpot hcert.1

/-- Transport the dyadic decrease to the actual materialized flow at
the end of an accepted epoch. -/
theorem targetEpoch_materialized_progress {τ : Type} (I : Instance) (U finish : ℕ)
    (target κ r : ℝ) (A : MinRatioDataStructureWithFailure)
    (base flow : Fin I.m → ℝ) (Q : EpochPoint τ)
    (hflow : flow=epochHistoryFlow I A Q.history Q.eta Q.op (2*finish) base)
    (hcert : EpochAnalyticPrefix I U target κ r A base finish Q)
    (hm : 0<I.m) (hi : finish≤I.m) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U)
    (hq : 0<κ*Num.IPM.alphaPrime I.m U/32) (hq' : κ*Num.IPM.alphaPrime I.m U/32≤1/2)
    (hf : StrictlyInside I base) (hroute : I.Routes base) (hr : 0<residual I target base)
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target base≤200*I.m*Real.log (I.m*(U:ℝ))) :
    potential I (Num.IPM.alphaPrime I.m U) target flow≤
      potential I (Num.IPM.alphaPrime I.m U) target base-
        (finish:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/2000 :=
  targetEpoch_materialized_progress_at_range I U finish _ target κ r A base flow Q hflow hcert
    hm hi hsize hnums hq hq' hf hroute hr hpot

end MinCostFlow.IPM.Machine
