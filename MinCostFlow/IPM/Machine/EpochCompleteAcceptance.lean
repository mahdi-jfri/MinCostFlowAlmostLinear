module

public import MinCostFlow.IPM.Machine.EpochCompleteFrame
public import MinCostFlow.IPM.Machine.EpochAnalyticPrefix
import MinCostFlow.IPM.Machine.EpochProgressBound
import MinCostFlow.IPM.Machine.EpochGuardRanges
import MinCostFlow.IPM.Machine.EpochMaterializationOutput
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.Num.IPM.FixedPointFacts
import Mathlib.Tactic.Linarith

/-!
# Acceptance of the full read on promised targets

The actual lazy trace supplies the potential bound and residual drift.
They give strict slack bounds for the exact coordinates recovered by
the full read, so its measured flag is one.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- After a promised lazy run, the complete read accepts the endpoint
certified by the very same history. -/
theorem epochComplete_accepts_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space finish loopEnd : ℕ) (mem : ℕ → ℕ)
    (loopState : State) (loopCredit : R.τ) (certified : EpochPoint R.τ → Prop)
    {v : ℕ} {final : State} {credit : R.τ}
    (hpost : EpochCompletePost F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L q K heap space finish
      mem loopEnd loopState loopCredit certified v final credit)
    (hlazy : loopState.mem (loopEnd-1)=1)
    (hcert : ∀ Q, certified Q → EpochAnalyticPrefix I U target κ r A (epochVector F I mem L.base) finish Q)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hm : 0<I.m) (hU : 1≤U) (hi : finish≤I.m) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hq : 0<κ*Num.IPM.alphaPrime I.m U/32) (hq' : κ*Num.IPM.alphaPrime I.m U/32≤1/2)
    (hres : residual I target (epochVector F I mem L.base)=r) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hE : L.exponent=ipmRangeExponent I.m U) :
    final.mem (v-1)=1 := by
  unfold EpochCompletePost at hpost
  rw [ite_eq_left hlazy] at hpost
  obtain ⟨Q,hcond,_,hcertQ,hflag,hpre,_,hout,_⟩ := hpost
  have hflow := (epoch_detect_source_geometry F A I κ _ rate allocation R L q K _
    hcond.2.2.2.2.2.2.2.2.2.1).1
  obtain ⟨_,_,_,_,_,_,hframe,hvalid,hgraph,_⟩ := hcond
  have hflagFrame := hflag.1.2.2.1
  have hprefix : ∀ z<L.flow,loopState.mem z=mem z :=
    fun z hz => (hflagFrame z (hz.trans_le hflow)).trans (hframe z hz)
  have hbase : epochVector F I loopState.mem L.base=epochVector F I mem L.base := by
    funext e
    exact Num.IPM.fixVal_frozen hprefix
      ((reported_entry_end L.base F.limbs e.val I.m e.isLt).trans (harrays L.base (by simp)))
  have hr0 : 0<residual I target (epochVector F I mem L.base) := by rw [hres]; linarith only [hr]
  obtain ⟨hroute',hf',hpot',hrange⟩ := epochDyadicPrefix_state I U finish target _ A Q.history Q.eta Q.op
    (epochVector F I mem L.base) hm hi hsize hnums hq hq' hf hroute hr0 hpot (hcert Q hcertQ).1 finish le_rfl
  rw [hres] at hrange
  have hsmall : κ*Num.IPM.alphaPrime I.m U/32/4≤1 := by linarith only [hq']
  have hcurrent := current_residual_gt_eighth hrange hsmall hr
  have hslacks := (epoch_strict_guard_ranges I U target _ hm hU hsize hnums hf' hroute' hpot' hFlo hcurrent.le).2
  apply epoch_materialization_accepts_upTo F A I κ _ _ _ hA rate allocation R L q K loopEnd v
    (2*finish) Q.credit _ r loopState.mem final.mem Q.history Q.eta Q.op hvalid (namedHistory_bounded hgraph) (hgraph _ le_rfl)
    (hsource.frozen hprefix harrays hscalars) hpre hout
  rw [hbase,hE]
  exact hslacks

/-- After a promised lazy run, the complete read accepts the endpoint
certified by the very same history. -/
theorem epochComplete_accepts {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024))
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space finish loopEnd : ℕ) (mem : ℕ → ℕ)
    (loopState : State) (loopCredit : R.τ) (certified : EpochPoint R.τ → Prop)
    {v : ℕ} {final : State} {credit : R.τ}
    (hpost : EpochCompletePost F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L q K heap space finish
      mem loopEnd loopState loopCredit certified v final credit)
    (hlazy : loopState.mem (loopEnd-1)=1)
    (hcert : ∀ Q, certified Q → EpochAnalyticPrefix I U target κ r A (epochVector F I mem L.base) finish Q)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hm : 0<I.m) (hU : 1≤U) (hi : finish≤I.m) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hq : 0<κ*Num.IPM.alphaPrime I.m U/32) (hq' : κ*Num.IPM.alphaPrime I.m U/32≤1/2)
    (hres : residual I target (epochVector F I mem L.base)=r) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hE : L.exponent=ipmRangeExponent I.m U) :
    final.mem (v-1)=1 :=
  epochComplete_accepts_upTo F A I U κ target r (hA.upTo I.m I.n) rate allocation R L q K heap
    space finish loopEnd mem loopState loopCredit certified hpost hlazy hcert hsource harrays
    hscalars hm hU hi hsize hnums hFlo hq hq' hres hr hf hroute hpot hE

/-- After a promised lazy run under `P`, the complete read accepts the endpoint
certified by the very same history. -/
theorem epochComplete_accepts_at_range_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ target r : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ (Num.IPM.alphaPrime I.m U/8) ((E+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n) (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space finish loopEnd : ℕ) (mem : ℕ → ℕ)
    (loopState : State) (loopCredit : R.τ) (certified : EpochPoint R.τ → Prop)
    {v : ℕ} {final : State} {credit : R.τ}
    (hpost : EpochCompletePost F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L q K heap space finish
      mem loopEnd loopState loopCredit certified v final credit)
    (hlazy : loopState.mem (loopEnd-1)=1)
    (hcert : ∀ Q, certified Q → EpochAnalyticPrefixAt I U E target κ r A (epochVector F I mem L.base) finish Q)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hm : 0<I.m) (hU : 1≤U) (hi : finish≤I.m) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hq : 0<κ*Num.IPM.alphaPrime I.m U/32) (hq' : κ*Num.IPM.alphaPrime I.m U/32≤1/2)
    (hres : residual I target (epochVector F I mem L.base)=r) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hE : L.exponent=E) (hWide : ipmRangeExponent I.m U≤E) :
    final.mem (v-1)=1 := by
  unfold EpochCompletePost at hpost
  rw [ite_eq_left hlazy] at hpost
  obtain ⟨Q,hcond,_,hcertQ,hflag,hpre,_,hout,_⟩ := hpost
  have hflow := (epoch_detect_source_geometry F A I κ _ rate allocation R L q K _
    hcond.2.2.2.2.2.2.2.2.2.1).1
  have hPD := hcond.stages hP
  obtain ⟨_,_,_,_,_,_,hframe,hvalid,hgraph,_⟩ := hcond
  have hflagFrame := hflag.1.2.2.1
  have hprefix : ∀ z<L.flow,loopState.mem z=mem z :=
    fun z hz => (hflagFrame z (hz.trans_le hflow)).trans (hframe z hz)
  have hbase : epochVector F I loopState.mem L.base=epochVector F I mem L.base := by
    funext e
    exact Num.IPM.fixVal_frozen hprefix
      ((reported_entry_end L.base F.limbs e.val I.m e.isLt).trans (harrays L.base (by simp)))
  have hr0 : 0<residual I target (epochVector F I mem L.base) := by rw [hres]; linarith only [hr]
  obtain ⟨hroute',hf',hpot',hrange⟩ := epochDyadicPrefix_state I U finish target _ A Q.history Q.eta Q.op
    (epochVector F I mem L.base) hm hi hsize hnums hq hq' hf hroute hr0 hpot (hcert Q hcertQ).1 finish le_rfl
  rw [hres] at hrange
  have hsmall : κ*Num.IPM.alphaPrime I.m U/32/4≤1 := by linarith only [hq']
  have hcurrent := current_residual_gt_eighth hrange hsmall hr
  have hslacks := (epoch_strict_guard_ranges I U target _ hm hU hsize hnums hf' hroute' hpot' hFlo hcurrent.le).2
  apply epoch_materialization_accepts_upTo_on F A I κ _ _ _ hA rate allocation R L q K loopEnd v
    (2*finish) Q.credit _ r loopState.mem final.mem Q.history Q.eta Q.op hvalid (namedHistory_bounded hgraph)
    hPD (hgraph _ le_rfl) (hsource.frozen hprefix harrays hscalars) hpre hout
  rw [hbase,hE]
  intro e
  exact ⟨strict_guard_range_mono hWide (hslacks e).1, strict_guard_range_mono hWide (hslacks e).2⟩

/-- After a promised lazy run, the complete read accepts the endpoint
certified by the very same history. -/
theorem epochComplete_accepts_at_range_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ target r : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) ((E+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space finish loopEnd : ℕ) (mem : ℕ → ℕ)
    (loopState : State) (loopCredit : R.τ) (certified : EpochPoint R.τ → Prop)
    {v : ℕ} {final : State} {credit : R.τ}
    (hpost : EpochCompletePost F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L q K heap space finish
      mem loopEnd loopState loopCredit certified v final credit)
    (hlazy : loopState.mem (loopEnd-1)=1)
    (hcert : ∀ Q, certified Q → EpochAnalyticPrefixAt I U E target κ r A (epochVector F I mem L.base) finish Q)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (harrays : ∀ ptr∈[L.base,L.cost,L.lower,L.upper],ptr+I.m*F.limbs≤L.flow)
    (hscalars : L.residual+F.limbs≤L.flow ∧ L.alpha+F.limbs≤L.flow)
    (hm : 0<I.m) (hU : 1≤U) (hi : finish≤I.m) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hq : 0<κ*Num.IPM.alphaPrime I.m U/32) (hq' : κ*Num.IPM.alphaPrime I.m U/32≤1/2)
    (hres : residual I target (epochVector F I mem L.base)=r) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hE : L.exponent=E) (hWide : ipmRangeExponent I.m U≤E) :
    final.mem (v-1)=1 :=
  epochComplete_accepts_at_range_upTo_on F A I U E κ target r (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _)
    rate allocation R L q K heap space finish loopEnd mem loopState loopCredit certified
    hpost hlazy hcert hsource harrays hscalars hm hU hi hsize hnums hFlo hq hq' hres hr hf hroute hpot hE hWide

end MinCostFlow.IPM.Machine
