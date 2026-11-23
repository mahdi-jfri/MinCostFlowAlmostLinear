module

public import MinCostFlow.IPM.Machine.PrecisionSlacks
public import MinCostFlow.IPM.HiddenWitness
import MinCostFlow.IPM.OptimalDirection
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Hidden witness ratios at the stored exponent

The negative-objective part of Chen et al., arXiv:2203.00671v2,
Lemma 9.2 (pages 70--71), uses the direction to an optimal feasible flow.
The potential budget pays for the power barriers at every `a≤alpha`.
The stored residual then loses at most a factor two in the witness ratio.
This permits the hidden parameter `a/8` for the computed coefficients.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- Lemma 4.7 (page 28), with an upper cost guess and an exponent
at most the analytic one. The potential is evaluated at that exponent. -/
theorem direction_of_cost_le_at_exponent (I : Instance) (U a F eps : ℝ)
    (f fstar g l : Fin I.m → ℝ) (hm : 0 < I.m) (hsize : 2 ≤ (I.m:ℝ)*U)
    (ha : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hf : StrictlyInside I f) (hs : I.IsFeasible fstar)
    (hr : 0 < residual I F f) (hF : I.cost fstar ≤ F) (heps : eps ≤ a/2)
    (hg : GradientTolerance (lengths I a f) g (gradient I a F f) eps)
    (hl : VectorApprox 2 l (lengths I a f))
    (hpot : potential I a F f ≤ 200*I.m*Real.log (I.m*U))
    (hreslog : -10*Real.log (I.m*U) ≤ Real.log (residual I F f)) :
    dot g (fun e => fstar e-f e)/(100*I.m+weightedLength l (fun e => fstar e-f e)) ≤ -a/4 := by
  have haSmall := haUpper.trans (alpha_le I U hsize)
  apply direction_of_cost_le_of_budget I a F eps f fstar g l hm hf hs ha
    (by linarith only [haSmall]) hr hF heps hg hl
  have hm0 : (0:ℝ) ≤ I.m := Nat.cast_nonneg _
  have hlog := log_size_ge_half I U hsize
  have hbar := barrier_budget_of_potential I U F a f hpot hreslog
  have hbudget : potential I a F f-20*I.m*Real.log (residual I F f) ≤
      400*I.m*Real.log (I.m*U) := by
    simpa only [potential,ipmBarrierBound,add_sub_cancel_left] using hbar
  have hB0 : 0 ≤ 400*(I.m:ℝ)*Real.log (I.m*U) :=
    mul_nonneg (mul_nonneg (by norm_num) hm0) (by linarith only [hlog])
  calc
    _ ≤ 2*a*(400*I.m*Real.log (I.m*U)) :=
      mul_le_mul_of_nonneg_left hbudget (mul_nonneg (by norm_num) ha)
    _ ≤ 2*alpha I U*(400*I.m*Real.log (I.m*U)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haUpper (by norm_num)) hB0
    _ = 800*I.m*(alpha I U*Real.log (I.m*U)) := by ring
    _ = (4/5:ℝ)*I.m := by rw [alpha_mul_log I U hsize]; ring
    _ ≤ I.m := by linarith only [hm0]

/-- The negative-ratio part of the adapted Lemma 9.2 (pages 70--71),
with a supplied positive stored exponent. Other hidden-witness conditions
are independent of the exponent and keep the source widths. -/
theorem hiddenWidth_ratio_at_exponent (I : Instance) (U a F ε r : ℝ)
    (fstar f g ℓ : Fin I.m → ℝ)
    (hm : 0 < I.m) (hsize : 2 ≤ (I.m : ℝ)*U)
    (haPositive : 0 < a) (haUpper : a ≤ alpha I U)
    (hf : StrictlyInside I f) (hs : I.IsFeasible fstar)
    (hr : 0 < residual I F f) (hF : I.cost fstar ≤ F)
    (_he : 0 ≤ ε) (he' : ε ≤ 1)
    (hres : ScalarApprox (1+ε) r (residual I F f))
    (hg : GradientTolerance (lengths I (a) f)
      (fun e => (r/residual I F f)*g e) (gradient I (a) F f) (a/2))
    (hl : VectorApprox 2 ℓ (lengths I (a) f))
    (hpot : potential I (a) F f ≤ 200*I.m*Real.log (I.m*U))
    (hreslog : -10*Real.log (I.m*U) ≤ Real.log (residual I F f)) :
    (namedInstance I).inner (namedVector g) (namedVector (fun e => fstar e-f e)) /
      (namedInstance I).norm1 (namedVector (hiddenWidth fstar f ℓ)) ≤ -(a/8) := by
  have hq := direction_of_cost_le_at_exponent I U a F (a/2) f fstar
    (fun e => (r/residual I F f)*g e) ℓ hm hsize haPositive.le haUpper hf hs hr hF le_rfl hg hl hpot hreslog
  have hlen : 0 ≤ weightedLength ℓ (fun e => fstar e-f e) :=
    Finset.sum_nonneg fun e _ => abs_nonneg _
  have hmR : (0 : ℝ) < I.m := Nat.cast_pos.mpr hm
  have ha := haPositive
  have hd100 : 0 < 100*(I.m : ℝ)+weightedLength ℓ (fun e => fstar e-f e) := by
    linarith only [hmR, hlen]
  have hd50 : 0 < 50*(I.m : ℝ)+weightedLength ℓ (fun e => fstar e-f e) := by
    linarith only [hmR, hlen]
  have hq' := (div_le_iff₀ hd100).mp hq
  have hneg : dot (fun e => (r/residual I F f)*g e) (fun e => fstar e-f e) ≤ 0 :=
    hq'.trans (mul_nonpos_of_nonpos_of_nonneg (by linarith only [ha]) hd100.le)
  have hratio : (1/2 : ℝ) ≤ residual I F f/r := by
    apply (le_div_iff₀ hres.1).mpr
    have hh := hres.2.2.2
    have hp := mul_le_mul_of_nonneg_right he' hr.le
    linarith only [hh, hp]
  have hid : dot g (fun e => fstar e-f e) =
      (residual I F f/r)*dot (fun e => (r/residual I F f)*g e) (fun e => fstar e-f e) := by
    unfold dot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    field_simp [hr.ne', hres.1.ne']
  have hscaled := mul_le_mul_of_nonpos_right hratio hneg
  rw [namedInstance_inner, hiddenWidth_norm]
  apply (div_le_iff₀ hd50).mpr
  rw [hid]
  nlinarith only [hscaled, hq', mul_nonneg ha.le hmR.le]

end MinCostFlow.IPM.Machine
