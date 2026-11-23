module

public import MinCostFlow.IPM.Machine.DyadicRun
public import MinCostFlow.IPM.Machine.RoundedResidualDrift
import MinCostFlow.IPM.EpochResidual
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith

/-!
# Residual stability with the actual dyadic request

The effective-step interval includes the `25/32` request factor, DS
scalar rounding, and the held-residual ratio. Its normalized cost bound
limits each residual change by `q/(250m)`. The epoch accumulation proof
of Chen et al., arXiv:2203.00671v2, Lemma 9.1 (page 70), then supplies
both snapshot accuracy and the tighter ratio needed by the next step.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- Every actual dyadic-request step has the same relative residual drift
bound as the effective normalized step, including all scalar errors. -/
theorem DyadicAdmissibleStep.residual_change (I : Instance) (U : ℕ) (F q : ℝ)
    (f next : Fin I.m → ℝ) (hm : 0<I.m) (hsize : 2≤I.m*U)
    (hf : StrictlyInside I f) (hres : 0<residual I F f)
    (hq : 0<q) (hqUpper : q≤1/2)
    (hstep : DyadicAdmissibleStep I U F q f next) :
    |residual I F next-residual I F f|/residual I F f≤q/(250*I.m) := by
  obtain ⟨g,l,d,s,r,hs,hr,hg,hl,_,hqual,rfl⟩ := hstep
  have hsReal : (2:ℝ)≤I.m*(U:ℝ) := by exact_mod_cast hsize
  have ha := Num.IPM.alphaPrime_bounds I U hsize
  have ha0 : 0≤Num.IPM.alphaPrime I.m U :=
    (div_nonneg (alpha_pos I U hsReal).le (by norm_num : (0:ℝ)≤10)).trans ha.1
  obtain ⟨p,hplo,hphi,hg',hqual',hnorm⟩ :=
    dyadic_request_normalization I (Num.IPM.alphaPrime I.m U) F q s r f g l d hq hs hr hg hqual
  have hp : 0<p := (by linarith only [hq] : 0<q/2).trans_le hplo
  exact direction_residual_change_of_effective_parameter I (Num.IPM.alphaPrime I.m U) F q p
    (((25/32:ℝ)*r)*q^2/(50*|dot g d|)) f (fun e => s*g e) l d hm hf hres ha0
    (ha.2.trans (alpha_le I U hsReal)) hp (by linarith only [hphi,hqUpper]) hphi hg' hl hqual' hnorm

/-- At most `m` actual dyadic-request steps preserve the held residual to
factor `1+q/4`. Domain hypotheses come from the proved run budget, rather
than a separate residual-stability assumption. -/
theorem dyadic_run_residual_approx (I : Instance) (U N : ℕ) (F q : ℝ)
    (f : ℕ → Fin I.m → ℝ) (hm : 0<I.m) (hsize : 2≤I.m*U) (hN : N≤I.m)
    (hnums : NumbersBounded I U) (hq : 0<q) (hqUpper : q≤1/2)
    (hf0 : StrictlyInside I (f 0)) (hroute0 : I.Routes (f 0))
    (hres0 : 0<residual I F (f 0))
    (hpot0 : potential I (Num.IPM.alphaPrime I.m U) F (f 0)≤200*I.m*Real.log (I.m*(U:ℝ)))
    (hsteps : ∀ i<N,DyadicAdmissibleStep I U F q (f i) (f (i+1))) :
    ∀ t≤N,ScalarApprox (1+q/4) (residual I F (f 0)) (residual I F (f t)) := by
  have hbudget := dyadic_run_budget I U N F q f hm hsize hnums hq hqUpper hf0 hroute0 hres0 hpot0 hsteps
  have hstep : ∀ i<N,|residual I F (f (i+1))-residual I F (f i)|/residual I F (f i)≤(q/250)/I.m := by
    intro i hi
    rw [div_div]
    exact (hsteps i hi).residual_change I U F q _ _ hm hsize (hbudget i hi.le).2.1
      (hbudget i hi.le).2.2.1 hq hqUpper
  intro t ht
  have hh := epoch_residual_approx_prefix (fun i => residual I F (f i)) I.m N (q/250)
    hm hN (by linarith only [hq]) (by linarith only [hqUpper])
    (fun i hi => (hbudget i hi).2.2.1) hstep t ht
  have hb : 0<1+4*(q/250) := by linarith only [hq]
  have hc : 0<1+q/4 := by linarith only [hq]
  have hfactor : 1+4*(q/250)≤1+q/4 := by linarith only [hq]
  have hi := (inv_le_inv₀ hc hb).mpr hfactor
  exact ⟨hh.1,hh.2.1,(mul_le_mul_of_nonneg_right hi hh.2.1.le).trans hh.2.2.1,
    hh.2.2.2.trans (mul_le_mul_of_nonneg_right hfactor hh.2.1.le)⟩

/-- The epoch snapshot bound yields the tighter residual-ratio interval
used in the next dyadic-request step. The last point of the prefix is
included, so the next iteration uses only proved facts about past steps. -/
theorem dyadic_run_residual_ratios (I : Instance) (U N : ℕ) (F q : ℝ)
    (f : ℕ → Fin I.m → ℝ) (hm : 0<I.m) (hsize : 2≤I.m*U) (hN : N≤I.m)
    (hnums : NumbersBounded I U) (hq : 0<q) (hqUpper : q≤1/2)
    (hf0 : StrictlyInside I (f 0)) (hroute0 : I.Routes (f 0))
    (hres0 : 0<residual I F (f 0))
    (hpot0 : potential I (Num.IPM.alphaPrime I.m U) F (f 0)≤200*I.m*Real.log (I.m*(U:ℝ)))
    (hsteps : ∀ i<N,DyadicAdmissibleStep I U F q (f i) (f (i+1))) :
    ∀ t≤N,(3/4:ℝ)≤residual I F (f 0)/residual I F (f t) ∧
      residual I F (f 0)/residual I F (f t)≤4/3 := by
  intro t ht
  exact residual_ratio_three_fourths (by linarith only [hq]) (by linarith only [hqUpper])
    (dyadic_run_residual_approx I U N F q f hm hsize hN hnums hq hqUpper hf0 hroute0 hres0 hpot0 hsteps t ht)

end MinCostFlow.IPM.Machine
