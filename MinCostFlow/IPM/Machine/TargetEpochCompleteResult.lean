module

public import MinCostFlow.IPM.Machine.TargetEpochProgress
public import MinCostFlow.IPM.Machine.TargetEpochContinueResult
public import MinCostFlow.IPM.Machine.EpochCompleteAcceptance
import Mathlib.Tactic.Linarith

/-!
# Promised progress or guarded rejection after the complete epoch

The complete epoch's status is verified on both sides of the target.
Success is a genuine materialized flow. On an upper target with the
potential bound, the analytic certificate forces success and
quantifies the decrease.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 350000 in
/-- Derive both semantic branches needed by the target stage from the
complete epoch's exact returned history. -/
theorem targetEpoch_complete_result_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space loopEnd : ℕ) (mem : ℕ → ℕ)
    (loopState : State) (loopCredit : R.τ)
    {v : ℕ} {final : State} {credit : R.τ}
    (hpost : EpochCompletePost F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L q K heap space I.m
      mem loopEnd loopState loopCredit
      (fun Q => TargetStagePromise I U target (epochVector F I mem L.base) →
        EpochAnalyticPrefix I U target κ r A (epochVector F I mem L.base) I.m Q) v final credit)
    (hlazy : TargetStagePromise I U target (epochVector F I mem L.base) → loopState.mem (loopEnd-1)=1)
    (hframe : ∀ z<L.flow,final.mem z=mem z)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hq : 0<κ*Num.IPM.alphaPrime I.m U/32) (hq' : κ*Num.IPM.alphaPrime I.m U/32≤1/2)
    (hres : residual I target (epochVector F I mem L.base)=r) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hE : L.exponent=ipmRangeExponent I.m U) :
    let base := epochVector F I mem L.base
    let promised := TargetStagePromise I U target base
    (final.mem (v-1)=0 → ¬promised) ∧
    (final.mem (v-1)=1 → TargetStageFlow F I L.exponent L.flow v final.mem ∧
      (promised → potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I final.mem L.flow)≤
        potential I (Num.IPM.alphaPrime I.m U) target base-(I.m:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/2000)) := by
  dsimp only
  constructor
  · intro hbit hp
    have haccept := epochComplete_accepts_upTo F A I U κ target r hA rate allocation R L q K heap space
      I.m loopEnd mem loopState loopCredit _ hpost (hlazy hp) (fun _ h => h hp) hsource harrays hscalars
      hm hU le_rfl hsize hnums hFlo hq hq' hres hr hf hroute hp.2 hE
    omega
  · intro hbit
    obtain ⟨Q,hcert,hend,hfeas,hEq,hslack⟩ := epochComplete_output_flow_upTo F A I κ _ _ _ hA rate allocation R
      L q K heap space I.m loopEnd mem loopState loopCredit _ hpost hframe hsource hroute harrays hscalars hbit
    refine ⟨⟨hend,hfeas,hslack⟩,?_⟩
    intro hp
    have hr0 : 0<residual I target (epochVector F I mem L.base) := by rw [hres]; linarith only [hr]
    exact targetEpoch_materialized_progress I U I.m target κ r A _ _ Q hEq (hcert hp)
      hm le_rfl hsize hnums hq hq' hf hroute hr0 hp.2

/-- Derive both semantic branches needed by the target stage from the
complete epoch's exact returned history. -/
theorem targetEpoch_complete_result {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024))
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space loopEnd : ℕ) (mem : ℕ → ℕ)
    (loopState : State) (loopCredit : R.τ)
    {v : ℕ} {final : State} {credit : R.τ}
    (hpost : EpochCompletePost F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L q K heap space I.m
      mem loopEnd loopState loopCredit
      (fun Q => TargetStagePromise I U target (epochVector F I mem L.base) →
        EpochAnalyticPrefix I U target κ r A (epochVector F I mem L.base) I.m Q) v final credit)
    (hlazy : TargetStagePromise I U target (epochVector F I mem L.base) → loopState.mem (loopEnd-1)=1)
    (hframe : ∀ z<L.flow,final.mem z=mem z)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hq : 0<κ*Num.IPM.alphaPrime I.m U/32) (hq' : κ*Num.IPM.alphaPrime I.m U/32≤1/2)
    (hres : residual I target (epochVector F I mem L.base)=r) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hE : L.exponent=ipmRangeExponent I.m U) :
    let base := epochVector F I mem L.base
    let promised := TargetStagePromise I U target base
    (final.mem (v-1)=0 → ¬promised) ∧
    (final.mem (v-1)=1 → TargetStageFlow F I L.exponent L.flow v final.mem ∧
      (promised → potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I final.mem L.flow)≤
        potential I (Num.IPM.alphaPrime I.m U) target base-(I.m:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/2000)) :=
  targetEpoch_complete_result_upTo F A I U κ target r (hA.upTo I.m I.n) rate allocation R L q K
    heap space loopEnd mem loopState loopCredit hpost hlazy hframe hsource harrays hscalars hm
    hU hsize hnums hFlo hq hq' hres hr hf hroute hE

/-- Derive both semantic branches needed by the target stage from the
complete epoch's exact returned history. -/
theorem targetEpoch_complete_result_at_range_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ target r : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ (Num.IPM.alphaPrime I.m U/8)
      ((E+slackRangeExponent I.m U+6 : ℕ) : ℝ) (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space loopEnd : ℕ) (mem : ℕ → ℕ)
    (loopState : State) (loopCredit : R.τ)
    {v : ℕ} {final : State} {credit : R.τ}
    (hpost : EpochCompletePost F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L q K heap space I.m
      mem loopEnd loopState loopCredit
      (fun Q => TargetStagePromise I U target (epochVector F I mem L.base) →
        EpochAnalyticPrefixAt I U E target κ r A (epochVector F I mem L.base) I.m Q) v final credit)
    (hlazy : TargetStagePromise I U target (epochVector F I mem L.base) → loopState.mem (loopEnd-1)=1)
    (hframe : ∀ z<L.flow,final.mem z=mem z)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hq : 0<κ*Num.IPM.alphaPrime I.m U/32) (hq' : κ*Num.IPM.alphaPrime I.m U/32≤1/2)
    (hres : residual I target (epochVector F I mem L.base)=r) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hE : L.exponent=E) (hWide : ipmRangeExponent I.m U≤E) :
    let base := epochVector F I mem L.base
    let promised := TargetStagePromise I U target base
    (final.mem (v-1)=0 → ¬promised) ∧
    (final.mem (v-1)=1 → TargetStageFlow F I L.exponent L.flow v final.mem ∧
      (promised → potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I final.mem L.flow)≤
        potential I (Num.IPM.alphaPrime I.m U) target base-(I.m:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/2000)) := by
  dsimp only
  constructor
  · intro hbit hp
    have haccept := epochComplete_accepts_at_range_upTo_on F A I U E κ target r hA hP rate allocation R L q K heap space
      I.m loopEnd mem loopState loopCredit _ hpost (hlazy hp) (fun _ h => h hp) hsource harrays hscalars
      hm hU le_rfl hsize hnums hFlo hq hq' hres hr hf hroute hp.2 hE hWide
    omega
  · intro hbit
    obtain ⟨Q,hcert,hend,hfeas,hEq,hslack⟩ := epochComplete_output_flow_upTo_on F A I κ _ _ _ hA hP rate allocation R
      L q K heap space I.m loopEnd mem loopState loopCredit _ hpost hframe hsource hroute harrays hscalars hbit
    refine ⟨⟨hend,hfeas,hslack⟩,?_⟩
    intro hp
    have hr0 : 0<residual I target (epochVector F I mem L.base) := by rw [hres]; linarith only [hr]
    exact targetEpoch_materialized_progress_at_range I U I.m E target κ r A _ _ Q hEq (hcert hp)
      hm le_rfl hsize hnums hq hq' hf hroute hr0 hp.2

/-- Derive both semantic branches needed by the target stage from the
complete epoch's exact returned history. -/
theorem targetEpoch_complete_result_at_range_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ target r : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) ((E+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space loopEnd : ℕ) (mem : ℕ → ℕ)
    (loopState : State) (loopCredit : R.τ)
    {v : ℕ} {final : State} {credit : R.τ}
    (hpost : EpochCompletePost F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L q K heap space I.m
      mem loopEnd loopState loopCredit
      (fun Q => TargetStagePromise I U target (epochVector F I mem L.base) →
        EpochAnalyticPrefixAt I U E target κ r A (epochVector F I mem L.base) I.m Q) v final credit)
    (hlazy : TargetStagePromise I U target (epochVector F I mem L.base) → loopState.mem (loopEnd-1)=1)
    (hframe : ∀ z<L.flow,final.mem z=mem z)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hq : 0<κ*Num.IPM.alphaPrime I.m U/32) (hq' : κ*Num.IPM.alphaPrime I.m U/32≤1/2)
    (hres : residual I target (epochVector F I mem L.base)=r) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hE : L.exponent=E) (hWide : ipmRangeExponent I.m U≤E) :
    let base := epochVector F I mem L.base
    let promised := TargetStagePromise I U target base
    (final.mem (v-1)=0 → ¬promised) ∧
    (final.mem (v-1)=1 → TargetStageFlow F I L.exponent L.flow v final.mem ∧
      (promised → potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I final.mem L.flow)≤
        potential I (Num.IPM.alphaPrime I.m U) target base-(I.m:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/2000)) :=
  targetEpoch_complete_result_at_range_upTo_on F A I U E κ target r
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) rate allocation R L q K heap space loopEnd mem
    loopState loopCredit hpost hlazy hframe hsource harrays hscalars hm hU hsize hnums hFlo hq
    hq' hres hr hf hroute hE hWide

end MinCostFlow.IPM.Machine
