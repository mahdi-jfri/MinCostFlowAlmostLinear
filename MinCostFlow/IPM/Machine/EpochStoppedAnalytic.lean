module

public import MinCostFlow.IPM.Machine.EpochCertifiedIteration
public import MinCostFlow.IPM.Machine.EpochIterationAttempt
import MinCostFlow.IPM.Machine.EpochGuardRanges
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith

/-!
# A promised epoch cannot take the machine's failure branch

Before the next call, the dyadic progress bound gives strict slacks
and the held residual remains near its epoch snapshot. The potential
bounds the stored coefficient ranges. The checked program must reach
Update, where hidden stability forces the actual answer to be present.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 400000 in
/-- With an upper target and a certified prefix, every actual iteration
returns success even if the trace was initially specified as a candidate
stopping call. -/
theorem epoch_iteration_promised_accepts_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (L : EpochLayout) (K i v : ℕ) (P : EpochPoint R.τ) (final : ℕ → ℕ)
    (s' : A.State) (capacity : ℝ) (fstar : Fin I.m → ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hcond : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmErrorBits I.m U) K initialMem initialHeap space finish i P)
    (hanalytic : EpochAnalyticPrefix I U target κ r A (epochVector F I P.machine.mem L.base) i P)
    (hstatic : EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) P.machine.mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r P.machine.mem)
    (hlo : L.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hi : i≤ I.m) (hU : 0<U) (hsize : 2≤ I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hFLo : -(I.m*(U:ℝ)^2)≤target)
    (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I P.machine.mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I P.machine.mem L.base))
    (hroute : I.Routes (epochVector F I P.machine.mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I P.machine.mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hout : budgetedIterationResult F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
      (minRatioState A.eraseFailure P.history P.eta P.op (2*i)) s' P.credit (ipmErrorBits I.m U) K
      L.sourceEnd L.tableEnd (L.packet F I (P.machine.regs 8)) P.machine.mem v final) :
    final (v-1)=1 := by
  let a := Num.IPM.alphaPrime I.m U
  let q := κ*a/32
  let eps := κ*a/1024
  let base := epochVector F I P.machine.mem L.base
  let current := epochHistoryFlow I A P.history P.eta P.op (2*i) base
  have hsizeR : 2≤(I.m:ℝ)*U := by exact_mod_cast hsize
  have ha : 0<a := by unfold a Num.IPM.alphaPrime; positivity
  have ha' : a≤alpha I U := (Num.IPM.alphaPrime_bounds I U hsize).2
  have haSmall := ha'.trans (alpha_le I U hsizeR)
  have hx := mul_le_mul_of_nonneg_right hκ' ha.le
  have hq : 0<q := div_pos (mul_pos hκ ha) (by norm_num)
  have hq' : q≤1/2 := by unfold q; linarith only [hx,haSmall]
  have hr0 : 0<residual I target base := hres ▸ (by linarith only [hr] : 0<r)
  obtain ⟨hrouteC,hstrict,hpotC,hdrift⟩ :=
    epochDyadicPrefix_state I U i target q A P.history P.eta P.op base hm hi hsize hnums hq hq'
      hf hroute hr0 hpot hanalytic.1 i le_rfl
  rw [← hres] at hdrift
  have hresC := current_residual_gt_eighth hdrift (by linarith only [hq'] : q/4≤1) hr
  have hRange := epoch_numeric_ranges I U target current hm (by omega) hsize hnums
    hstrict hrouteC hpotC hFLo hresC.le
  have hrange : 1/(2:ℝ)^(slackRangeExponent I.m U)≤r :=
    (dyadic_le_eighth I.m U hm hU).trans (by linarith only [hr])
  obtain ⟨cEnd,cMem,es,actual,hCpost,hCbit,_,hset,hnorm,hcoeff,hvalid,_,hbit⟩ :=
    epoch_iteration_attempt_upTo F A I U κ (a/8) (precisionHiddenPsi I.m U) eps rate allocation R hA
      L (ipmErrorBits I.m U) K i v P final s' a r capacity ((25/32:ℝ)*q^2/50)
      hcond hstatic hsource hlo hnums hrange hi hanalytic.2.2.2.2.2 hRange.2 hout
  have hcert := epoch_certified_iteration_upTo F A I U κ target r rate allocation R hA L K i cEnd P
    cMem es actual capacity fstar hcond hanalytic hstatic hsource hm hi hU hsize hnums hstar hF
    hκ hκ' hxlo hres hr hf hroute hpot hCpost hCbit hset hnorm hcoeff hvalid
  rw [hbit]
  dsimp only at hcert
  rw [hcert.2.2.2.1]
  rfl

/-- With an upper target and a certified prefix, every actual iteration
returns success even if the trace was initially specified as a candidate
stopping call. -/
theorem epoch_iteration_promised_accepts {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024))
    (L : EpochLayout) (K i v : ℕ) (P : EpochPoint R.τ) (final : ℕ → ℕ)
    (s' : A.State) (capacity : ℝ) (fstar : Fin I.m → ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hcond : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmErrorBits I.m U) K initialMem initialHeap space finish i P)
    (hanalytic : EpochAnalyticPrefix I U target κ r A (epochVector F I P.machine.mem L.base) i P)
    (hstatic : EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) P.machine.mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r P.machine.mem)
    (hlo : L.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hi : i≤ I.m) (hU : 0<U) (hsize : 2≤ I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hFLo : -(I.m*(U:ℝ)^2)≤target)
    (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I P.machine.mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I P.machine.mem L.base))
    (hroute : I.Routes (epochVector F I P.machine.mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I P.machine.mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hout : budgetedIterationResult F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
      (minRatioState A.eraseFailure P.history P.eta P.op (2*i)) s' P.credit (ipmErrorBits I.m U) K
      L.sourceEnd L.tableEnd (L.packet F I (P.machine.regs 8)) P.machine.mem v final) :
    final (v-1)=1 :=
  epoch_iteration_promised_accepts_upTo F A I U κ target r rate allocation R (hA.upTo I.m I.n) L
    K i v P final s' capacity fstar hcond hanalytic hstatic hsource hlo hm hi hU hsize hnums
    hstar hF hFLo hκ hκ' hxlo hres hr hf hroute hpot hout

/-- With an upper target and a certified prefix, every actual iteration
returns success even if the trace was initially specified as a candidate
stopping call. -/
theorem epoch_iteration_promised_accepts_widened_upTo_on {PG : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn PG A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hPG : StageAdmits PG (namedInstance I) F.rangeExponent)
    (L : EpochLayout) (K i v : ℕ) (P : EpochPoint R.τ) (final : ℕ → ℕ)
    (s' : A.State) (capacity : ℝ) (fstar : Fin I.m → ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hcond : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmQualityErrorBits I.m U k) K initialMem initialHeap space finish i P)
    (hanalytic : EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A (epochVector F I P.machine.mem L.base) i P)
    (hstatic : EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) P.machine.mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r P.machine.mem)
    (hlo : L.exponent=ipmQualityRangeExponent I.m U k)
    (hm : 0<I.m) (hi : i≤ I.m) (hU : 0<U) (hsize : 2≤ I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hFLo : -(I.m*(U:ℝ)^2)≤target)
    (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I P.machine.mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I P.machine.mem L.base))
    (hroute : I.Routes (epochVector F I P.machine.mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I P.machine.mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hout : budgetedIterationResult F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
      (minRatioState A.eraseFailure P.history P.eta P.op (2*i)) s' P.credit (ipmQualityErrorBits I.m U k) K
      L.sourceEnd L.tableEnd (L.packet F I (P.machine.regs 8)) P.machine.mem v final) :
    final (v-1)=1 := by
  let a := Num.IPM.alphaPrime I.m U
  let q := κ*a/32
  let eps := κ*a/1024
  let base := epochVector F I P.machine.mem L.base
  let current := epochHistoryFlow I A P.history P.eta P.op (2*i) base
  have hsizeR : 2≤(I.m:ℝ)*U := by exact_mod_cast hsize
  have ha : 0<a := by unfold a Num.IPM.alphaPrime; positivity
  have ha' : a≤alpha I U := (Num.IPM.alphaPrime_bounds I U hsize).2
  have haSmall := ha'.trans (alpha_le I U hsizeR)
  have hx := mul_le_mul_of_nonneg_right hκ' ha.le
  have hq : 0<q := div_pos (mul_pos hκ ha) (by norm_num)
  have hq' : q≤1/2 := by unfold q; linarith only [hx,haSmall]
  have hr0 : 0<residual I target base := hres ▸ (by linarith only [hr] : 0<r)
  obtain ⟨hrouteC,hstrict,hpotC,hdrift⟩ :=
    epochDyadicPrefix_state I U i target q A P.history P.eta P.op base hm hi hsize hnums hq hq'
      hf hroute hr0 hpot hanalytic.1 i le_rfl
  rw [← hres] at hdrift
  have hresC := current_residual_gt_eighth hdrift (by linarith only [hq'] : q/4≤1) hr
  have hRange := epoch_numeric_ranges I U target current hm (by omega) hsize hnums
    hstrict hrouteC hpotC hFLo hresC.le
  have hrange : 1/(2:ℝ)^(slackRangeExponent I.m U)≤r :=
    (dyadic_le_eighth I.m U hm hU).trans (by linarith only [hr])
  have hWide : ipmRangeExponent I.m U ≤ ipmQualityRangeExponent I.m U k := by
    have hs := slackRangeExponent_le_qualitySlackExponent I.m U k
    unfold ipmRangeExponent ipmQualityRangeExponent
    omega
  obtain ⟨cEnd,cMem,es,actual,hCpost,hCbit,_,hset,hnorm,hcoeff,hvalid,_,hbit⟩ :=
    epoch_iteration_attempt_at_range_upTo_on F A I U (ipmQualityRangeExponent I.m U k) κ (a/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ) eps rate allocation R hA hPG
      L (ipmQualityErrorBits I.m U k) K i v P final s' a r capacity ((25/32:ℝ)*q^2/50)
      hcond hstatic hsource hlo hWide hnums hrange hi hanalytic.2.2.2.2.2 hRange.2 hout
  have hcert := epoch_certified_iteration_widened_upTo_on F A I U k κ target r rate allocation R hA hPG L K i cEnd P
    cMem es actual capacity fstar hcond hanalytic hstatic hsource hm hi hU hsize hnums hstar hF
    hκ hκ' hxlo hres hr hf hroute hpot hCpost hCbit hset hnorm hcoeff hvalid
  rw [hbit]
  dsimp only at hcert
  rw [hcert.2.2.2.1]
  rfl

/-- With an upper target and a certified prefix, every actual iteration
returns success even if the trace was initially specified as a candidate
stopping call. -/
theorem epoch_iteration_promised_accepts_widened_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (L : EpochLayout) (K i v : ℕ) (P : EpochPoint R.τ) (final : ℕ → ℕ)
    (s' : A.State) (capacity : ℝ) (fstar : Fin I.m → ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hcond : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmQualityErrorBits I.m U k) K initialMem initialHeap space finish i P)
    (hanalytic : EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A (epochVector F I P.machine.mem L.base) i P)
    (hstatic : EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) P.machine.mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r P.machine.mem)
    (hlo : L.exponent=ipmQualityRangeExponent I.m U k)
    (hm : 0<I.m) (hi : i≤ I.m) (hU : 0<U) (hsize : 2≤ I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hFLo : -(I.m*(U:ℝ)^2)≤target)
    (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I P.machine.mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I P.machine.mem L.base))
    (hroute : I.Routes (epochVector F I P.machine.mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I P.machine.mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hout : budgetedIterationResult F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
      (minRatioState A.eraseFailure P.history P.eta P.op (2*i)) s' P.credit (ipmQualityErrorBits I.m U k) K
      L.sourceEnd L.tableEnd (L.packet F I (P.machine.regs 8)) P.machine.mem v final) :
    final (v-1)=1 :=
  epoch_iteration_promised_accepts_widened_upTo_on F A I U k κ target r rate allocation R
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) L K i v P final s' capacity fstar hcond hanalytic
    hstatic hsource hlo hm hi hU hsize hnums hstar hF hFLo hκ hκ' hxlo hres hr hf hroute hpot hout

end MinCostFlow.IPM.Machine
