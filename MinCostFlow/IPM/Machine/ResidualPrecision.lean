module

public import MinCostFlow.IPM.Machine.PrecisionProducts
public import MinCostFlow.IPM.Machine.Layout
public import MinCostFlow.Num.IPM.Residual
import Mathlib.Tactic.Linarith

/-!
# Supplying the exact residual procedure's fit premises

The prepared cost table uses integer precision, while flow and target
blocks use the selected fixed-point precision. Bounds on feasible flows
control every dot-product prefix, not just the final sum. Subtracting any
target in the search interval fits even when the residual is negative.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine
open WordRAM

private theorem scan_scaled_abs_le (I : Instance) (U : ℕ) (f : Fin I.m → ℝ)
    {mem : ℕ → ℕ} {cp fp h L P j : ℕ} (hj : j ≤ I.m)
    (hnums : NumbersBounded I U) (hf : I.IsFeasible f)
    (hc : ∀ e : Fin I.m,Num.intVal mem (cp+e.val*L) h L=(I.edge e).cost)
    (hflow : ∀ e : Fin I.m,Num.fixVal mem (fp+e.val*L) h L P=f e) :
    |(Num.IPM.dotNumerator mem cp fp h L j:ℝ)/(2:ℝ)^P| ≤ I.m*(U:ℝ)^2 := by
  rw [Num.IPM.dotNumerator_scaled]
  calc
    _ ≤ ∑ i ∈ Finset.range j,
        |(Num.intVal mem (cp+i*L) h L:ℝ)*Num.fixVal mem (fp+i*L) h L P| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range j,(U:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i < I.m := (Finset.mem_range.mp hi).trans_le hj
      rw [hc ⟨i,him⟩,hflow ⟨i,him⟩,abs_mul,pow_two]
      exact mul_le_mul (hnums.2 ⟨i,him⟩).2.2
        (feasible_abs_le I U hnums f hf ⟨i,him⟩) (abs_nonneg _) (Nat.cast_nonneg _)
    _ = (j:ℝ)*(U:ℝ)^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (sq_nonneg _)

private theorem radius_in_chosen_range (m U : ℕ) (hm : 0 < m) (hU : 0 < U) :
    2*(m:ℝ)*(U:ℝ)^2 ≤ (2:ℝ)^(ipmRangeExponent m U) := by
  apply (twice_search_radius_le_dyadic m U hm hU).trans
  apply pow_le_pow_right₀ (by norm_num)
  unfold ipmRangeExponent
  omega

/-- All products, prefixes and the target subtraction required by the
actual residual procedure fit under the chosen precision. The target can
lie on either side of the optimum. -/
theorem residual_pre_of_chosen_precision (I : Instance) (U : ℕ) (f : Fin I.m → ℝ)
    (F : ℤ) {w cp fp tp heap : ℕ} {mem : ℕ → ℕ}
    (hm : 0 < I.m) (hU : 0 < U) (hnums : NumbersBounded I U) (hf : I.IsFeasible f)
    (hc : ∀ e : Fin I.m,ScalarAt mem (cp+e.val*ipmLimbs I.m U) 4 (ipmLimbs I.m U) 0 ((I.edge e).cost:ℝ))
    (hflow : ∀ e : Fin I.m,ScalarAt mem (fp+e.val*ipmLimbs I.m U) 4
      (ipmLimbs I.m U) (ipmPrecision I.m U) (f e))
    (ht : ScalarAt mem tp 4 (ipmLimbs I.m U) (ipmPrecision I.m U) (F:ℝ))
    (hF : |(F:ℝ)| ≤ I.m*(U:ℝ)^2)
    (hca : cp+I.m*ipmLimbs I.m U ≤ heap)
    (hfa : fp+I.m*ipmLimbs I.m U ≤ heap) (hta : tp+ipmLimbs I.m U ≤ heap)
    (hz : ZeroFrom mem heap)
    (hspace : heap+(8*I.m+4)*ipmLimbs I.m U < 2^w) :
    (Num.IPM.residualContract w 4).pre [cp,fp,I.m,tp,ipmLimbs I.m U,heap] mem := by
  have hcost : ∀ e : Fin I.m,Num.intVal mem (cp+e.val*ipmLimbs I.m U) 4
      (ipmLimbs I.m U)=(I.edge e).cost := by
    intro e
    have hh := (hc e).2
    simp only [Num.fixVal,pow_zero,div_one] at hh
    exact_mod_cast hh
  have hvalues : ∀ e : Fin I.m,Num.fixVal mem (fp+e.val*ipmLimbs I.m U) 4
      (ipmLimbs I.m U) (ipmPrecision I.m U)=f e := fun e => (hflow e).2
  have hbound := radius_in_chosen_range I.m U hm hU
  have hnn : (0:ℝ) ≤ I.m*(U:ℝ)^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  refine ⟨⟨cp,fp,I.m,tp,ipmLimbs I.m U,heap,rfl,hca,hfa,hta,ht.1,?_,?_,?_⟩,hz,hspace⟩
  · intro i hi
    refine ⟨(hc ⟨i,hi⟩).1,(hflow ⟨i,hi⟩).1,?_⟩
    rw [hcost ⟨i,hi⟩]
    simpa only [Finset.sum_singleton] using cost_prefix_numerator_fits I U f
      (fun e => Num.intVal mem (fp+e.val*ipmLimbs I.m U) 4 (ipmLimbs I.m U))
      {⟨i,hi⟩} hm hU hnums hf (fun e => (hvalues e).symm)
  · intro j hj
    apply fits_chosen_scaled_bound
    have hh := scan_scaled_abs_le I U f hj hnums hf hcost hvalues
    linarith only [hh,hbound,hnn]
  · apply fits_chosen_scaled_bound
    rw [Num.IPM.scaled_sub]
    change |(Num.IPM.dotNumerator mem cp fp 4 (ipmLimbs I.m U) I.m:ℝ)/
      (2:ℝ)^(ipmPrecision I.m U)-Num.fixVal mem tp 4 (ipmLimbs I.m U) (ipmPrecision I.m U)| ≤ _
    rw [ht.2]
    have hh := scan_scaled_abs_le I U f (le_refl I.m) hnums hf hcost hvalues
    have htri := abs_sub_le ((Num.IPM.dotNumerator mem cp fp 4 (ipmLimbs I.m U) I.m:ℝ)/
      (2:ℝ)^(ipmPrecision I.m U)) 0 (F:ℝ)
    simp only [sub_zero,zero_sub,abs_neg] at htri
    linarith only [htri,hh,hF,hbound]

private theorem radius_in_widened_range (m U k : ℕ) (hm : 0 < m) (hU : 0 < U) :
    2*(m:ℝ)*(U:ℝ)^2 ≤ (2:ℝ)^(ipmQualityRangeExponent m U k) := by
  apply (twice_search_radius_le_dyadic m U hm hU).trans
  apply pow_le_pow_right₀ (by norm_num)
  have hSlack := slackRangeExponent_le_qualitySlackExponent m U k
  unfold ipmQualityRangeExponent
  omega

/-- All products, prefixes and the target subtraction required by the
actual residual procedure fit under the chosen precision. The target can
lie on either side of the optimum. -/
theorem residual_pre_of_widened_precision (I : Instance) (U k : ℕ) (f : Fin I.m → ℝ)
    (F : ℤ) {w cp fp tp heap : ℕ} {mem : ℕ → ℕ}
    (hm : 0 < I.m) (hU : 0 < U) (hnums : NumbersBounded I U) (hf : I.IsFeasible f)
    (hc : ∀ e : Fin I.m,ScalarAt mem (cp+e.val*ipmQualityLimbs I.m U k) 4 (ipmQualityLimbs I.m U k) 0 ((I.edge e).cost:ℝ))
    (hflow : ∀ e : Fin I.m,ScalarAt mem (fp+e.val*ipmQualityLimbs I.m U k) 4
      (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) (f e))
    (ht : ScalarAt mem tp 4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k) (F:ℝ))
    (hF : |(F:ℝ)| ≤ I.m*(U:ℝ)^2)
    (hca : cp+I.m*ipmQualityLimbs I.m U k ≤ heap)
    (hfa : fp+I.m*ipmQualityLimbs I.m U k ≤ heap) (hta : tp+ipmQualityLimbs I.m U k ≤ heap)
    (hz : ZeroFrom mem heap)
    (hspace : heap+(8*I.m+4)*ipmQualityLimbs I.m U k < 2^w) :
    (Num.IPM.residualContract w 4).pre [cp,fp,I.m,tp,ipmQualityLimbs I.m U k,heap] mem := by
  have hcost : ∀ e : Fin I.m,Num.intVal mem (cp+e.val*ipmQualityLimbs I.m U k) 4
      (ipmQualityLimbs I.m U k)=(I.edge e).cost := by
    intro e
    have hh := (hc e).2
    simp only [Num.fixVal,pow_zero,div_one] at hh
    exact_mod_cast hh
  have hvalues : ∀ e : Fin I.m,Num.fixVal mem (fp+e.val*ipmQualityLimbs I.m U k) 4
      (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k)=f e := fun e => (hflow e).2
  have hbound := radius_in_widened_range I.m U k hm hU
  have hnn : (0:ℝ) ≤ I.m*(U:ℝ)^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  refine ⟨⟨cp,fp,I.m,tp,ipmQualityLimbs I.m U k,heap,rfl,hca,hfa,hta,ht.1,?_,?_,?_⟩,hz,hspace⟩
  · intro i hi
    refine ⟨(hc ⟨i,hi⟩).1,(hflow ⟨i,hi⟩).1,?_⟩
    rw [hcost ⟨i,hi⟩]
    simpa only [Finset.sum_singleton] using cost_prefix_numerator_fits_widened I U k f
      (fun e => Num.intVal mem (fp+e.val*ipmQualityLimbs I.m U k) 4 (ipmQualityLimbs I.m U k))
      {⟨i,hi⟩} hm hU hnums hf (fun e => (hvalues e).symm)
  · intro j hj
    apply fits_quality_scaled_bound
    have hh := scan_scaled_abs_le I U f hj hnums hf hcost hvalues
    linarith only [hh,hbound,hnn]
  · apply fits_quality_scaled_bound
    rw [Num.IPM.scaled_sub]
    change |(Num.IPM.dotNumerator mem cp fp 4 (ipmQualityLimbs I.m U k) I.m:ℝ)/
      (2:ℝ)^(ipmQualityPrecision I.m U k)-Num.fixVal mem tp 4 (ipmQualityLimbs I.m U k) (ipmQualityPrecision I.m U k)| ≤ _
    rw [ht.2]
    have hh := scan_scaled_abs_le I U f (le_refl I.m) hnums hf hcost hvalues
    have htri := abs_sub_le ((Num.IPM.dotNumerator mem cp fp 4 (ipmQualityLimbs I.m U k) I.m:ℝ)/
      (2:ℝ)^(ipmQualityPrecision I.m U k)) 0 (F:ℝ)
    simp only [sub_zero,zero_sub,abs_neg] at htri
    linarith only [htri,hh,hF,hbound]

end MinCostFlow.IPM.Machine
