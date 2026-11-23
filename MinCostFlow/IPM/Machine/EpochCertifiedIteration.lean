module

public import MinCostFlow.IPM.Machine.EpochAnalyticPrefix
public import MinCostFlow.IPM.Machine.EpochDetectAccuracy
public import MinCostFlow.IPM.Machine.EpochUpdateAccuracy
public import MinCostFlow.IPM.Machine.EpochStaticInputs
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith

/-!
# Certifying the two actual inputs and the resulting rounded motion

The previous accepted prefix bounds the held residual and pending
movement. Apply these bounds to the actual old and refreshed caches.
The resulting wider input history is hidden stable before inspecting
the last Update answer.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 350000 in
/-- An actual accepted refresh extends the certified input history.
Together with the rounded request this forces the next Update direction
and bounds the movement measured in that same length array. -/
theorem epoch_certified_iteration_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (L : EpochLayout) (K i v : ℕ) (P : EpochPoint R.τ) (refreshed : ℕ → ℕ)
    (es : List ℕ) (actual capacity : ℝ) (fstar : Fin I.m → ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hcond : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmErrorBits I.m U) K initialMem initialHeap space finish i P)
    (hanalytic : EpochAnalyticPrefix I U target κ r A (epochVector F I P.machine.mem L.base) i P)
    (hstatic : EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) P.machine.mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r P.machine.mem)
    (hm : 0<I.m) (hi : i≤I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I P.machine.mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I P.machine.mem L.base))
    (hroute : I.Routes (epochVector F I P.machine.mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I P.machine.mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8)
      rate allocation R L.handle (minRatioState A.eraseFailure P.history P.eta P.op (2*i)) P.credit
      (ipmErrorBits I.m U) K L.sourceEnd L.tableEnd).post
      ((L.packet F I (P.machine.regs 8)).take 20) P.machine.mem v refreshed)
    (haccept : refreshed (v-1)=1)
    (hset : es.toFinset=(A.detect (minRatioState A.eraseFailure P.history P.eta P.op (2*i))).1)
    (hnorm : NormalizationWithin ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) actual)
    (hnewRange : ∀ e : Fin I.m,1/(2:ℝ)^(ipmRangeExponent I.m U)≤epochVector F I refreshed L.lengths e ∧
      epochVector F I refreshed L.lengths e≤(2:ℝ)^(ipmRangeExponent I.m U))
    (hvalid : MinRatioHistoryValid (appendHistoryIteration P.history (2*i) es
        (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      (appendHistoryIterationOp P.op (2*i)) (2*i+1+1)) :
    let a := Num.IPM.alphaPrime I.m U
    let q := κ*a/32
    let D' := appendHistoryIteration P.history (2*i) es
      (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    let eta' := appendHistoryIterationEta P.eta (2*i) actual
    let op' := appendHistoryIterationOp P.op (2*i)
    let base := epochVector F I P.machine.mem L.base
    EpochHistoryCacheStable I A D' eta' op' (2*i+1+1) base ∧
    (∀ t≤2*i+1+1,EpochInputAccuracy I U target a r q A D' eta' op' base t) ∧
    D'.HiddenStable (2*i+1+1) (a/8) (precisionHiddenPsi I.m U) ∧
    (minRatioFailureDirection A D' eta' op' (2*i+1)).isSome=true ∧
    EpochDyadicPrefix I U target q A D' eta' op' base (i+1) ∧ EpochDetectSchedule op' (i+1) ∧
    (D'.G (2*i+1+1)).lnorm (D'.ℓ (2*i+1+1)) (minRatioIncrement A.eraseFailure D' eta' op' (2*i+1+1))≤
      (κ*a/1024)/4 := by
  dsimp only
  let a := Num.IPM.alphaPrime I.m U
  let x := κ*a
  let q := x/32
  let base := epochVector F I P.machine.mem L.base
  let g := readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m
  let ell := readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m
  let D' := appendHistoryIteration P.history (2*i) es g ell
  let eta' := appendHistoryIterationEta P.eta (2*i) actual
  let op' := appendHistoryIterationOp P.op (2*i)
  have hsizeR : 2≤(I.m:ℝ)*U := by exact_mod_cast hsize
  have ha : 0<a := by unfold a Num.IPM.alphaPrime; positivity
  have ha' : a≤alpha I U := (Num.IPM.alphaPrime_bounds I U hsize).2
  have haSmall := ha'.trans (alpha_le I U hsizeR)
  have hx : x≤1 := (mul_le_mul_of_nonneg_right hκ' ha.le).trans (by
    rw [one_mul]
    linarith only [haSmall])
  have hq : 0<q := div_pos (mul_pos hκ ha) (by norm_num)
  have hq' : q≤1/2 := by unfold q; linarith only [hx]
  have hr0 : 0<residual I target base := hres ▸ (by linarith only [hr] : 0<r)
  obtain ⟨hsteps,hschedule,hstable,hinputs,hpend,_⟩ := hanalytic
  have hstate := epochDyadicPrefix_state I U i target q A P.history P.eta P.op base hm hi hsize hnums hq hq'
    hf hroute hr0 hpot hsteps i le_rfl
  have hcurrent := hstate.2.2.2
  have hresApprox : ScalarApprox (1+8*(x/1024)) r
      (residual I target (epochHistoryFlow I A P.history P.eta P.op (2*i) base)) := by
    rw [← hres] at hcurrent
    rw [show 1+8*(x/1024)=1+q/4 by unfold q; ring]
    exact hcurrent
  obtain ⟨_,_,_,_,_,_,_,hv,hG,hpre,hgOld,hlOld,hcache,hOldRanges,_⟩ := hcond
  obtain ⟨_,_,_,_,_,harrays,hscalars,_,_,_,_,_,_,_,_,_,_,_,_,_,hfmt,_,_⟩ := hstatic
  have hOld (e : Fin I.m) : 1/(2:ℝ)^(ipmRangeExponent I.m U)≤epochVector F I P.machine.mem L.lengths e ∧
      epochVector F I P.machine.mem L.lengths e≤(2:ℝ)^(ipmRangeExponent I.m U) := by
    have h := (hOldRanges e.val e.isLt).2.2.2
    simpa only [readVector,e.isLt,ite_true,epochVector,hfmt,zpow_neg,zpow_natCast,one_div] using h
  have hDetect := epoch_detect_input_accuracy_upTo F A I U κ (a/8) (precisionHiddenPsi I.m U) x target a r
    hA L i P.machine.mem P.history P.eta P.op es g ell actual hm hsizeR hnums ha.le ha' hxlo hx hsource
    hv hG hgOld.symm hlOld.symm hOld hresApprox hcache hpend
  have hUpdate := epoch_update_input_accuracy_upTo F A I U κ (a/8) (precisionHiddenPsi I.m U) x target a r hA
    rate allocation R L i K (P.machine.regs 8) v P.credit P.machine.mem refreshed P.history P.eta P.op es
    actual hm hsizeR hnums ha.le ha' hxlo hx hsource hv hG hlOld.symm hpre hout haccept
    harrays ⟨hscalars L.residual (by simp),hscalars L.alpha (by simp)⟩ hnewRange hresApprox hcache
  have hNewInputs := epoch_input_accuracy_append I U target a r q A P.history P.eta P.op base i es g ell actual
    hinputs hDetect hUpdate
  have hNewCache := epochHistoryCacheStable_append I A P.history P.eta P.op i es g ell actual base hset hstable
  have hNewSchedule := epochDetectSchedule_append P.op i hschedule
  have hNewG := appendHistoryIteration_fixed_graph P.history (namedInstance I) (2*i) es g ell hG
  have hNewSteps := epochDyadicPrefix_append_past I U target q A P.history P.eta P.op base i es g ell actual hsteps
  have hop : op' (2*i+1+1)=true := Function.update_self _ _ _
  have hnorm' : NormalizationWithin ((25/32:ℝ)*q^2/50) (eta' (2*i+1+1)) := by
    simpa only [eta',appendHistoryIterationEta,Function.update_self] using hnorm
  obtain ⟨hhidden,hanswer,hstep,hmove⟩ := epoch_certified_direction_upTo I U i target κ r A D' eta' op'
    base fstar hm hi hU hsize hnums hstar hF hκ hκ' hres hr hf hroute hpot hA hvalid hNewG
    hNewCache hNewInputs hNewSchedule hNewSteps hop hnorm'
  exact ⟨hNewCache,hNewInputs,hhidden,hanswer,
    epochDyadicPrefix_append I U target q A P.history P.eta P.op base i es g ell actual hsteps hstep,
    hNewSchedule,hmove⟩

/-- An actual accepted refresh extends the certified input history.
Together with the rounded request this forces the next Update direction
and bounds the movement measured in that same length array. -/
theorem epoch_certified_iteration {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024))
    (L : EpochLayout) (K i v : ℕ) (P : EpochPoint R.τ) (refreshed : ℕ → ℕ)
    (es : List ℕ) (actual capacity : ℝ) (fstar : Fin I.m → ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hcond : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmErrorBits I.m U) K initialMem initialHeap space finish i P)
    (hanalytic : EpochAnalyticPrefix I U target κ r A (epochVector F I P.machine.mem L.base) i P)
    (hstatic : EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) P.machine.mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r P.machine.mem)
    (hm : 0<I.m) (hi : i≤I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I P.machine.mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I P.machine.mem L.base))
    (hroute : I.Routes (epochVector F I P.machine.mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I P.machine.mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8)
      rate allocation R L.handle (minRatioState A.eraseFailure P.history P.eta P.op (2*i)) P.credit
      (ipmErrorBits I.m U) K L.sourceEnd L.tableEnd).post
      ((L.packet F I (P.machine.regs 8)).take 20) P.machine.mem v refreshed)
    (haccept : refreshed (v-1)=1)
    (hset : es.toFinset=(A.detect (minRatioState A.eraseFailure P.history P.eta P.op (2*i))).1)
    (hnorm : NormalizationWithin ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) actual)
    (hnewRange : ∀ e : Fin I.m,1/(2:ℝ)^(ipmRangeExponent I.m U)≤epochVector F I refreshed L.lengths e ∧
      epochVector F I refreshed L.lengths e≤(2:ℝ)^(ipmRangeExponent I.m U))
    (hvalid : MinRatioHistoryValid (appendHistoryIteration P.history (2*i) es
        (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      (appendHistoryIterationOp P.op (2*i)) (2*i+1+1)) :
    let a := Num.IPM.alphaPrime I.m U
    let q := κ*a/32
    let D' := appendHistoryIteration P.history (2*i) es
      (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    let eta' := appendHistoryIterationEta P.eta (2*i) actual
    let op' := appendHistoryIterationOp P.op (2*i)
    let base := epochVector F I P.machine.mem L.base
    EpochHistoryCacheStable I A D' eta' op' (2*i+1+1) base ∧
    (∀ t≤2*i+1+1,EpochInputAccuracy I U target a r q A D' eta' op' base t) ∧
    D'.HiddenStable (2*i+1+1) (a/8) (precisionHiddenPsi I.m U) ∧
    (minRatioFailureDirection A D' eta' op' (2*i+1)).isSome=true ∧
    EpochDyadicPrefix I U target q A D' eta' op' base (i+1) ∧ EpochDetectSchedule op' (i+1) ∧
    (D'.G (2*i+1+1)).lnorm (D'.ℓ (2*i+1+1)) (minRatioIncrement A.eraseFailure D' eta' op' (2*i+1+1))≤
      (κ*a/1024)/4 :=
  epoch_certified_iteration_upTo F A I U κ target r rate allocation R (hA.upTo I.m I.n) L K i v
    P refreshed es actual capacity fstar hcond hanalytic hstatic hsource hm hi hU hsize hnums
    hstar hF hκ hκ' hxlo hres hr hf hroute hpot hout haccept hset hnorm hnewRange hvalid

/-- An actual accepted refresh extends the certified input history.
Together with the rounded request this forces the next Update direction
and bounds the movement measured in that same length array. -/
theorem epoch_certified_iteration_widened_upTo_on {w : ℕ} {PG : MGraph → (ℕ → ℝ) → Prop} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn PG A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hPG : StageAdmits PG (namedInstance I) F.rangeExponent)
    (L : EpochLayout) (K i v : ℕ) (P : EpochPoint R.τ) (refreshed : ℕ → ℕ)
    (es : List ℕ) (actual capacity : ℝ) (fstar : Fin I.m → ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hcond : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmQualityErrorBits I.m U k) K initialMem initialHeap space finish i P)
    (hanalytic : EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A (epochVector F I P.machine.mem L.base) i P)
    (hstatic : EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) P.machine.mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r P.machine.mem)
    (hm : 0<I.m) (hi : i≤I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I P.machine.mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I P.machine.mem L.base))
    (hroute : I.Routes (epochVector F I P.machine.mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I P.machine.mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8)
      rate allocation R L.handle (minRatioState A.eraseFailure P.history P.eta P.op (2*i)) P.credit
      (ipmQualityErrorBits I.m U k) K L.sourceEnd L.tableEnd).post
      ((L.packet F I (P.machine.regs 8)).take 20) P.machine.mem v refreshed)
    (haccept : refreshed (v-1)=1)
    (hset : es.toFinset=(A.detect (minRatioState A.eraseFailure P.history P.eta P.op (2*i))).1)
    (hnorm : NormalizationWithin ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) actual)
    (hnewRange : ∀ e : Fin I.m,1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤epochVector F I refreshed L.lengths e ∧
      epochVector F I refreshed L.lengths e≤(2:ℝ)^(ipmQualityRangeExponent I.m U k))
    (hvalid : MinRatioHistoryValid (appendHistoryIteration P.history (2*i) es
        (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      (appendHistoryIterationOp P.op (2*i)) (2*i+1+1)) :
    let a := Num.IPM.alphaPrime I.m U
    let q := κ*a/32
    let D' := appendHistoryIteration P.history (2*i) es
      (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    let eta' := appendHistoryIterationEta P.eta (2*i) actual
    let op' := appendHistoryIterationOp P.op (2*i)
    let base := epochVector F I P.machine.mem L.base
    EpochHistoryCacheStable I A D' eta' op' (2*i+1+1) base ∧
    (∀ t≤2*i+1+1,EpochInputAccuracyAt I (ipmQualityRangeExponent I.m U k) target a r q A D' eta' op' base t) ∧
    D'.HiddenStable (2*i+1+1) (a/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ) ∧
    (minRatioFailureDirection A D' eta' op' (2*i+1)).isSome=true ∧
    EpochDyadicPrefix I U target q A D' eta' op' base (i+1) ∧ EpochDetectSchedule op' (i+1) ∧
    (D'.G (2*i+1+1)).lnorm (D'.ℓ (2*i+1+1)) (minRatioIncrement A.eraseFailure D' eta' op' (2*i+1+1))≤
      (κ*a/1024)/4 := by
  dsimp only
  let a := Num.IPM.alphaPrime I.m U
  let x := κ*a
  let q := x/32
  let base := epochVector F I P.machine.mem L.base
  let g := readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m
  let ell := readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m
  let D' := appendHistoryIteration P.history (2*i) es g ell
  let eta' := appendHistoryIterationEta P.eta (2*i) actual
  let op' := appendHistoryIterationOp P.op (2*i)
  have hsizeR : 2≤(I.m:ℝ)*U := by exact_mod_cast hsize
  have ha : 0<a := by unfold a Num.IPM.alphaPrime; positivity
  have ha' : a≤alpha I U := (Num.IPM.alphaPrime_bounds I U hsize).2
  have haSmall := ha'.trans (alpha_le I U hsizeR)
  have hx : x≤1 := (mul_le_mul_of_nonneg_right hκ' ha.le).trans (by
    rw [one_mul]
    linarith only [haSmall])
  have hq : 0<q := div_pos (mul_pos hκ ha) (by norm_num)
  have hq' : q≤1/2 := by unfold q; linarith only [hx]
  have hr0 : 0<residual I target base := hres ▸ (by linarith only [hr] : 0<r)
  obtain ⟨hsteps,hschedule,hstable,hinputs,hpend,_⟩ := hanalytic
  have hstate := epochDyadicPrefix_state I U i target q A P.history P.eta P.op base hm hi hsize hnums hq hq'
    hf hroute hr0 hpot hsteps i le_rfl
  have hcurrent := hstate.2.2.2
  have hresApprox : ScalarApprox (1+8*(x/1024)) r
      (residual I target (epochHistoryFlow I A P.history P.eta P.op (2*i) base)) := by
    rw [← hres] at hcurrent
    rw [show 1+8*(x/1024)=1+q/4 by unfold q; ring]
    exact hcurrent
  have hPGD := hcond.stages hPG
  obtain ⟨_,_,_,_,_,_,_,hv,hG,hpre,hgOld,hlOld,hcache,hOldRanges,_⟩ := hcond
  obtain ⟨_,_,_,_,_,harrays,hscalars,_,_,_,_,_,_,_,_,_,_,_,_,_,hfmt,_,_⟩ := hstatic
  have hPGD' : ∀ j≤2*i+1+1,PG (D'.G j) (D'.ℓ j) := by
    refine appendHistoryIteration_stage_on es g ell hPGD ?_
    rw [hG (2*i) le_rfl]
    refine hPG _ (fun e he => ?_)
    have heM : e<I.m := Finset.mem_range.mp he
    have h := hnewRange ⟨e,heM⟩
    rw [hfmt]
    simpa only [ell,readVector,heM,ite_true,epochVector,zpow_neg,zpow_natCast,one_div] using h
  have hOld (e : Fin I.m) : 1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤epochVector F I P.machine.mem L.lengths e ∧
      epochVector F I P.machine.mem L.lengths e≤(2:ℝ)^(ipmQualityRangeExponent I.m U k) := by
    have h := (hOldRanges e.val e.isLt).2.2.2
    simpa only [readVector,e.isLt,ite_true,epochVector,hfmt,zpow_neg,zpow_natCast,one_div] using h
  have hDetect := epoch_detect_input_accuracy_widened_upTo_on F A I U k κ (a/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ) x target a r
    hA L i P.machine.mem P.history P.eta P.op es g ell actual hm hsizeR hnums ha.le ha' hxlo hx hsource
    hv hG hPGD hgOld.symm hlOld.symm hOld hresApprox hcache hpend
  have hUpdate := epoch_update_input_accuracy_widened_upTo_on F A I U k κ (a/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ) x target a r hA
    rate allocation R L i K (P.machine.regs 8) v P.credit P.machine.mem refreshed P.history P.eta P.op es
    actual hm hsizeR hnums ha.le ha' hxlo hx hsource hv hG hPGD hlOld.symm hpre hout haccept
    harrays ⟨hscalars L.residual (by simp),hscalars L.alpha (by simp)⟩ hnewRange hresApprox hcache
  have hNewInputs := epoch_input_accuracy_at_append I (ipmQualityRangeExponent I.m U k) target a r q A P.history P.eta P.op base i es g ell actual
    hinputs hDetect hUpdate
  have hNewCache := epochHistoryCacheStable_append I A P.history P.eta P.op i es g ell actual base hset hstable
  have hNewSchedule := epochDetectSchedule_append P.op i hschedule
  have hNewG := appendHistoryIteration_fixed_graph P.history (namedInstance I) (2*i) es g ell hG
  have hNewSteps := epochDyadicPrefix_append_past I U target q A P.history P.eta P.op base i es g ell actual hsteps
  have hop : op' (2*i+1+1)=true := Function.update_self _ _ _
  have hnorm' : NormalizationWithin ((25/32:ℝ)*q^2/50) (eta' (2*i+1+1)) := by
    simpa only [eta',appendHistoryIterationEta,Function.update_self] using hnorm
  obtain ⟨hhidden,hanswer,hstep,hmove⟩ := epoch_certified_direction_at_range_upTo_on I U i (ipmQualityRangeExponent I.m U k) target κ r A D' eta' op'
    base fstar hm hi hU hsize hnums hstar hF hκ hκ' hres hr hf hroute hpot hA hvalid hNewG
    hPGD' hNewCache hNewInputs hNewSchedule hNewSteps hop hnorm'
  exact ⟨hNewCache,hNewInputs,hhidden,hanswer,
    epochDyadicPrefix_append I U target q A P.history P.eta P.op base i es g ell actual hsteps hstep,
    hNewSchedule,hmove⟩

theorem epoch_certified_iteration_widened_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (L : EpochLayout) (K i v : ℕ) (P : EpochPoint R.τ) (refreshed : ℕ → ℕ)
    (es : List ℕ) (actual capacity : ℝ) (fstar : Fin I.m → ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hcond : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmQualityErrorBits I.m U k) K initialMem initialHeap space finish i P)
    (hanalytic : EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A (epochVector F I P.machine.mem L.base) i P)
    (hstatic : EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) P.machine.mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r P.machine.mem)
    (hm : 0<I.m) (hi : i≤I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I P.machine.mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I P.machine.mem L.base))
    (hroute : I.Routes (epochVector F I P.machine.mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I P.machine.mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8)
      rate allocation R L.handle (minRatioState A.eraseFailure P.history P.eta P.op (2*i)) P.credit
      (ipmQualityErrorBits I.m U k) K L.sourceEnd L.tableEnd).post
      ((L.packet F I (P.machine.regs 8)).take 20) P.machine.mem v refreshed)
    (haccept : refreshed (v-1)=1)
    (hset : es.toFinset=(A.detect (minRatioState A.eraseFailure P.history P.eta P.op (2*i))).1)
    (hnorm : NormalizationWithin ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) actual)
    (hnewRange : ∀ e : Fin I.m,1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤epochVector F I refreshed L.lengths e ∧
      epochVector F I refreshed L.lengths e≤(2:ℝ)^(ipmQualityRangeExponent I.m U k))
    (hvalid : MinRatioHistoryValid (appendHistoryIteration P.history (2*i) es
        (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      (appendHistoryIterationOp P.op (2*i)) (2*i+1+1)) :
    let a := Num.IPM.alphaPrime I.m U
    let q := κ*a/32
    let D' := appendHistoryIteration P.history (2*i) es
      (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    let eta' := appendHistoryIterationEta P.eta (2*i) actual
    let op' := appendHistoryIterationOp P.op (2*i)
    let base := epochVector F I P.machine.mem L.base
    EpochHistoryCacheStable I A D' eta' op' (2*i+1+1) base ∧
    (∀ t≤2*i+1+1,EpochInputAccuracyAt I (ipmQualityRangeExponent I.m U k) target a r q A D' eta' op' base t) ∧
    D'.HiddenStable (2*i+1+1) (a/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ) ∧
    (minRatioFailureDirection A D' eta' op' (2*i+1)).isSome=true ∧
    EpochDyadicPrefix I U target q A D' eta' op' base (i+1) ∧ EpochDetectSchedule op' (i+1) ∧
    (D'.G (2*i+1+1)).lnorm (D'.ℓ (2*i+1+1)) (minRatioIncrement A.eraseFailure D' eta' op' (2*i+1+1))≤
      (κ*a/1024)/4 :=
  epoch_certified_iteration_widened_upTo_on F A I U k κ target r rate allocation R
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) L K i v P refreshed es actual capacity fstar
    hcond hanalytic hstatic hsource hm hi hU hsize hnums hstar hF hκ hκ' hxlo hres hr hf hroute hpot
    hout haccept hset hnorm hnewRange hvalid

end MinCostFlow.IPM.Machine
