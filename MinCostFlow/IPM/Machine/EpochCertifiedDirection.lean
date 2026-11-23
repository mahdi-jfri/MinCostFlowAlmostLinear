module

public import MinCostFlow.IPM.Machine.EpochHiddenFromInputs
public import MinCostFlow.IPM.Machine.EpochHistoryRun
public import MinCostFlow.IPM.Machine.MinRatioDyadicStep
import MinCostFlow.IPM.Machine.EpochGuardRanges
import MinCostFlow.IPM.Machine.PrecisionEta
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith

import MinCostFlow.IPM.Machine.EpochConditions

/-!
# The promised Update has an admissible direction

Extend only the input history first. Its two current coefficients use
an already certified flow. The resulting hidden stability forces the
data structure to return a circulation, and its actual rounded
normalization gives the next admissible step of Lemma 9.3.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Lemmas 9.2 and 9.3 of Chen et al., arXiv:2203.00671v2 (pages 70–71),
for the last attempted actual Update. No correctness of the final
direction is used in constructing its hidden witness. -/
theorem epoch_certified_direction_upTo (I : Instance) (U i : ℕ) (target κ r : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (base fstar : Fin I.m → ℝ)
    (hm : 0<I.m) (hi : i≤I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target)
    (hκ : 0<κ) (hκ' : κ≤1) (hres : r=residual I target base) (hr : 1/4<r)
    (hf : StrictlyInside I base) (hroute : I.Routes base)
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target base≤200*I.m*Real.log (I.m*(U:ℝ)))
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hv : MinRatioHistoryValid D op (2*i+1+1)) (hG : ∀ t≤2*i+1+1,D.G t=namedInstance I)
    (hcache : EpochHistoryCacheStable I A D eta op (2*i+1+1) base)
    (hinputs : ∀ t≤2*i+1+1,EpochInputAccuracy I U target (Num.IPM.alphaPrime I.m U) r
      (κ*Num.IPM.alphaPrime I.m U/32) A D eta op base t)
    (hschedule : EpochDetectSchedule op (i+1))
    (hsteps : EpochDyadicPrefix I U target (κ*Num.IPM.alphaPrime I.m U/32) A D eta op base i)
    (hop : op (2*i+1+1)=true)
    (hnorm : NormalizationWithin ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (eta (2*i+1+1))) :
    D.HiddenStable (2*i+1+1) (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U) ∧
    (minRatioFailureDirection A D eta op (2*i+1)).isSome=true ∧
    DyadicAdmissibleStep I U target (κ*Num.IPM.alphaPrime I.m U/32)
      (epochHistoryFlow I A D eta op (2*i) base) (epochHistoryFlow I A D eta op (2*i+1+1) base) ∧
    (D.G (2*i+1+1)).lnorm (D.ℓ (2*i+1+1))
      (minRatioIncrement A.eraseFailure D eta op (2*i+1+1))≤(κ*Num.IPM.alphaPrime I.m U/1024)/4 := by
  let a := Num.IPM.alphaPrime I.m U
  let x := κ*a
  let q := x/32
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
  have hstate := epochDyadicPrefix_state I U i target q A D eta op base hm hi hsize hnums hq hq'
    hf hroute hr0 hpot hsteps
  have hbound : ∀ t≤2*i+1+1,
      let f := epochInputFlow I A D eta op t base
      StrictlyInside I f ∧ I.Routes f ∧
      -10*Real.log (I.m*U)≤Real.log (residual I target f) ∧
      potential I a target f≤200*I.m*Real.log (I.m*U) := by
    intro t ht
    have he := epochInputFlow_eq_even I A D eta op i t base hschedule ht
    let j := (t-1)/2
    obtain ⟨hrouteJ,hinterior,hpotJ,hresJ⟩ := hstate j (by unfold j; omega)
    rw [← hres] at hresJ
    have hnear : q/4≤1 := by linarith only [hq']
    have hresLower := current_residual_gt_eighth hresJ hnear hr
    simp only [he]
    exact ⟨hinterior,hrouteJ,epoch_residual_log_lower _ _ hsizeR hresLower.le,hpotJ⟩
  have hhidden := epoch_hidden_of_inputs I U target κ a r A D eta op (2*i+1+1) base fstar
    hm hU hsizeR hnums hstar hF hκ.le hκ' ha ha' hx hv hG hcache hinputs hbound
  let t := 2*i+1
  have hinput := hinputs (t+1) le_rfl
  obtain ⟨hg,hl,hresidual,hlen,hgrad,_,_⟩ := hinput
  have hratio := residual_ratio_three_fourths
    (by linarith only [hq] : 0≤q/4) (by linarith only [hq'] : q/4≤1/3) hresidual
  have hbefore : epochInputFlow I A D eta op (t+1) base=epochHistoryFlow I A D eta op t base := by
    unfold epochInputFlow
    rw [Nat.add_sub_cancel]
  rw [hbefore] at hratio hlen hgrad
  have hnow := minRatio_history_dyadic_step_upTo I U target κ (precisionHiddenPsi I.m U) (x/1024)
    A hA D eta op (t+1) t base (fun e => D.g (t+1) e) (fun e => D.ℓ (t+1) e)
    (r/residual I target (epochHistoryFlow I A D eta op t base)) hκ hv (namedHistory_bounded hG) le_rfl hop
    (hG (t+1) le_rfl) hg hl hhidden hratio hgrad hlen hnorm
  have heq : epochHistoryFlow I A D eta op t base=epochHistoryFlow I A D eta op (2*i) base := by
    funext e
    have hop' := hschedule i (by omega)
    change base e+minRatioFlow A.eraseFailure D eta op (2*i+1) e=_
    rw [minRatioFlow_succ]
    simp only [minRatioIncrement,hop',Bool.false_eq_true,false_and,ite_false,add_zero]
    rfl
  have hdyadic : DyadicAdmissibleStep I U target q (epochHistoryFlow I A D eta op t base)
      (epochHistoryFlow I A D eta op (t+1) base) := hnow.2.1
  rw [heq] at hdyadic
  refine ⟨hhidden,hnow.1,hdyadic,hnow.2.2.trans_eq ?_⟩
  ring

/-- Lemmas 9.2 and 9.3 of Chen et al., arXiv:2203.00671v2 (pages 70–71),
for the last attempted actual Update. No correctness of the final
direction is used in constructing its hidden witness. -/
theorem epoch_certified_direction (I : Instance) (U i : ℕ) (target κ r : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (base fstar : Fin I.m → ℝ)
    (hm : 0<I.m) (hi : i≤I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target)
    (hκ : 0<κ) (hκ' : κ≤1) (hres : r=residual I target base) (hr : 1/4<r)
    (hf : StrictlyInside I base) (hroute : I.Routes base)
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target base≤200*I.m*Real.log (I.m*(U:ℝ)))
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024))
    (hv : MinRatioHistoryValid D op (2*i+1+1)) (hG : ∀ t≤2*i+1+1,D.G t=namedInstance I)
    (hcache : EpochHistoryCacheStable I A D eta op (2*i+1+1) base)
    (hinputs : ∀ t≤2*i+1+1,EpochInputAccuracy I U target (Num.IPM.alphaPrime I.m U) r
      (κ*Num.IPM.alphaPrime I.m U/32) A D eta op base t)
    (hschedule : EpochDetectSchedule op (i+1))
    (hsteps : EpochDyadicPrefix I U target (κ*Num.IPM.alphaPrime I.m U/32) A D eta op base i)
    (hop : op (2*i+1+1)=true)
    (hnorm : NormalizationWithin ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (eta (2*i+1+1))) :
    D.HiddenStable (2*i+1+1) (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U) ∧
    (minRatioFailureDirection A D eta op (2*i+1)).isSome=true ∧
    DyadicAdmissibleStep I U target (κ*Num.IPM.alphaPrime I.m U/32)
      (epochHistoryFlow I A D eta op (2*i) base) (epochHistoryFlow I A D eta op (2*i+1+1) base) ∧
    (D.G (2*i+1+1)).lnorm (D.ℓ (2*i+1+1))
      (minRatioIncrement A.eraseFailure D eta op (2*i+1+1))≤(κ*Num.IPM.alphaPrime I.m U/1024)/4 :=
  epoch_certified_direction_upTo I U i target κ r A D eta op base fstar hm hi hU hsize hnums
    hstar hF hκ hκ' hres hr hf hroute hpot (hA.upTo I.m I.n) hv hG hcache hinputs hschedule
    hsteps hop hnorm

/-- Lemmas 9.2 and 9.3 of Chen et al., arXiv:2203.00671v2 (pages 70–71),
for the last attempted actual Update under `P`. No correctness of the final
direction is used in constructing its hidden witness. -/
theorem epoch_certified_direction_at_range_upTo_on {P : MGraph → (ℕ → ℝ) → Prop}
    (I : Instance) (U i E : ℕ) (target κ r : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (base fstar : Fin I.m → ℝ)
    (hm : 0<I.m) (hi : i≤I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target)
    (hκ : 0<κ) (hκ' : κ≤1) (hres : r=residual I target base) (hr : 1/4<r)
    (hf : StrictlyInside I base) (hroute : I.Routes base)
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target base≤200*I.m*Real.log (I.m*(U:ℝ)))
    (hA : MinRatioSpecWithFailureUpToOn P A κ (Num.IPM.alphaPrime I.m U/8)
      ((E+slackRangeExponent I.m U+6 : ℕ) : ℝ) (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hv : MinRatioHistoryValid D op (2*i+1+1)) (hG : ∀ t≤2*i+1+1,D.G t=namedInstance I)
    (hPD : ∀ j ≤ 2*i+1+1, P (D.G j) (D.ℓ j))
    (hcache : EpochHistoryCacheStable I A D eta op (2*i+1+1) base)
    (hinputs : ∀ t≤2*i+1+1,EpochInputAccuracyAt I E target (Num.IPM.alphaPrime I.m U) r
      (κ*Num.IPM.alphaPrime I.m U/32) A D eta op base t)
    (hschedule : EpochDetectSchedule op (i+1))
    (hsteps : EpochDyadicPrefix I U target (κ*Num.IPM.alphaPrime I.m U/32) A D eta op base i)
    (hop : op (2*i+1+1)=true)
    (hnorm : NormalizationWithin ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (eta (2*i+1+1))) :
    D.HiddenStable (2*i+1+1) (Num.IPM.alphaPrime I.m U/8) ((E+slackRangeExponent I.m U+6 : ℕ) : ℝ) ∧
    (minRatioFailureDirection A D eta op (2*i+1)).isSome=true ∧
    DyadicAdmissibleStep I U target (κ*Num.IPM.alphaPrime I.m U/32)
      (epochHistoryFlow I A D eta op (2*i) base) (epochHistoryFlow I A D eta op (2*i+1+1) base) ∧
    (D.G (2*i+1+1)).lnorm (D.ℓ (2*i+1+1))
      (minRatioIncrement A.eraseFailure D eta op (2*i+1+1))≤(κ*Num.IPM.alphaPrime I.m U/1024)/4 := by
  let a := Num.IPM.alphaPrime I.m U
  let x := κ*a
  let q := x/32
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
  have hstate := epochDyadicPrefix_state I U i target q A D eta op base hm hi hsize hnums hq hq'
    hf hroute hr0 hpot hsteps
  have hbound : ∀ t≤2*i+1+1,
      let f := epochInputFlow I A D eta op t base
      StrictlyInside I f ∧ I.Routes f ∧
      -10*Real.log (I.m*U)≤Real.log (residual I target f) ∧
      potential I a target f≤200*I.m*Real.log (I.m*U) := by
    intro t ht
    have he := epochInputFlow_eq_even I A D eta op i t base hschedule ht
    let j := (t-1)/2
    obtain ⟨hrouteJ,hinterior,hpotJ,hresJ⟩ := hstate j (by unfold j; omega)
    rw [← hres] at hresJ
    have hnear : q/4≤1 := by linarith only [hq']
    have hresLower := current_residual_gt_eighth hresJ hnear hr
    simp only [he]
    exact ⟨hinterior,hrouteJ,epoch_residual_log_lower _ _ hsizeR hresLower.le,hpotJ⟩
  have hhidden := epoch_hidden_of_inputs_at_range I U E target κ a r A D eta op (2*i+1+1) base fstar
    hm hU hsizeR hnums hstar hF hκ.le hκ' ha ha' hx hv hG hcache hinputs hbound
  let t := 2*i+1
  have hinput := hinputs (t+1) le_rfl
  obtain ⟨hg,hl,hresidual,hlen,hgrad,_,_⟩ := hinput
  have hratio := residual_ratio_three_fourths
    (by linarith only [hq] : 0≤q/4) (by linarith only [hq'] : q/4≤1/3) hresidual
  have hbefore : epochInputFlow I A D eta op (t+1) base=epochHistoryFlow I A D eta op t base := by
    unfold epochInputFlow
    rw [Nat.add_sub_cancel]
  rw [hbefore] at hratio hlen hgrad
  have hnow := minRatio_history_dyadic_step_upTo_on I U target κ ((E+slackRangeExponent I.m U+6 : ℕ) : ℝ) (x/1024)
    A hA D eta op (t+1) t base (fun e => D.g (t+1) e) (fun e => D.ℓ (t+1) e)
    (r/residual I target (epochHistoryFlow I A D eta op t base)) hκ hv (namedHistory_bounded hG) hPD le_rfl hop
    (hG (t+1) le_rfl) hg hl hhidden hratio hgrad hlen hnorm
  have heq : epochHistoryFlow I A D eta op t base=epochHistoryFlow I A D eta op (2*i) base := by
    funext e
    have hop' := hschedule i (by omega)
    change base e+minRatioFlow A.eraseFailure D eta op (2*i+1) e=_
    rw [minRatioFlow_succ]
    simp only [minRatioIncrement,hop',Bool.false_eq_true,false_and,ite_false,add_zero]
    rfl
  have hdyadic : DyadicAdmissibleStep I U target q (epochHistoryFlow I A D eta op t base)
      (epochHistoryFlow I A D eta op (t+1) base) := hnow.2.1
  rw [heq] at hdyadic
  refine ⟨hhidden,hnow.1,hdyadic,hnow.2.2.trans_eq ?_⟩
  ring

/-- Lemmas 9.2 and 9.3 of Chen et al., arXiv:2203.00671v2 (pages 70–71),
for the last attempted actual Update. No correctness of the final
direction is used in constructing its hidden witness. -/
theorem epoch_certified_direction_at_range_upTo (I : Instance) (U i E : ℕ) (target κ r : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (base fstar : Fin I.m → ℝ)
    (hm : 0<I.m) (hi : i≤I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target)
    (hκ : 0<κ) (hκ' : κ≤1) (hres : r=residual I target base) (hr : 1/4<r)
    (hf : StrictlyInside I base) (hroute : I.Routes base)
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target base≤200*I.m*Real.log (I.m*(U:ℝ)))
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) ((E+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hv : MinRatioHistoryValid D op (2*i+1+1)) (hG : ∀ t≤2*i+1+1,D.G t=namedInstance I)
    (hcache : EpochHistoryCacheStable I A D eta op (2*i+1+1) base)
    (hinputs : ∀ t≤2*i+1+1,EpochInputAccuracyAt I E target (Num.IPM.alphaPrime I.m U) r
      (κ*Num.IPM.alphaPrime I.m U/32) A D eta op base t)
    (hschedule : EpochDetectSchedule op (i+1))
    (hsteps : EpochDyadicPrefix I U target (κ*Num.IPM.alphaPrime I.m U/32) A D eta op base i)
    (hop : op (2*i+1+1)=true)
    (hnorm : NormalizationWithin ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (eta (2*i+1+1))) :
    D.HiddenStable (2*i+1+1) (Num.IPM.alphaPrime I.m U/8) ((E+slackRangeExponent I.m U+6 : ℕ) : ℝ) ∧
    (minRatioFailureDirection A D eta op (2*i+1)).isSome=true ∧
    DyadicAdmissibleStep I U target (κ*Num.IPM.alphaPrime I.m U/32)
      (epochHistoryFlow I A D eta op (2*i) base) (epochHistoryFlow I A D eta op (2*i+1+1) base) ∧
    (D.G (2*i+1+1)).lnorm (D.ℓ (2*i+1+1))
      (minRatioIncrement A.eraseFailure D eta op (2*i+1+1))≤(κ*Num.IPM.alphaPrime I.m U/1024)/4 :=
  epoch_certified_direction_at_range_upTo_on I U i E target κ r A D eta op base fstar
    hm hi hU hsize hnums hstar hF hκ hκ' hres hr hf hroute hpot
    (hA.upToOn (P := fun _ _ => True)) hv hG (fun _ _ => trivial) hcache hinputs hschedule hsteps hop hnorm

end MinCostFlow.IPM.Machine
