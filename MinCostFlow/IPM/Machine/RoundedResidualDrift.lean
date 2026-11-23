module

public import MinCostFlow.IPM.Machine.PrecisionRun
import MinCostFlow.IPM.StepBounds
import MinCostFlow.IPM.StepTaylor
import MinCostFlow.IPM.EpochResidual
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Residual drift for scalar-rounded epochs

The cost bound in the normalized potential step bounds the relative
residual movement. The effective step parameter lies between q/2 and
2q, so its drift is at most q/(250m). Summing over an epoch of at most
m steps gives the held-residual approximation used by Lemma 9.1 of
Chen et al., arXiv:2203.00671v2 (page 70). All quantities use the stored
barrier exponent, and the scalar-rounding interval is included.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

private theorem normalized_residual_drift (I : Instance) (a F p : ℝ)
    (f g l step : Fin I.m → ℝ) (hm : 0 < I.m) (hf : StrictlyInside I f)
    (hr : 0 < residual I F f) (ha : 0 ≤ a) (ha' : a ≤ 1/500)
    (hp : 0 < p) (hp' : p ≤ 1)
    (hg : GradientTolerance (lengths I a f) g (gradient I a F f) (p/8))
    (hl : VectorApprox 2 l (lengths I a f))
    (hquality : p*weightedLength l step ≤ -dot g step)
    (hscale : dot g step=-p^2/50) :
    |residual I F (fun e => f e+step e)-residual I F f|/residual I F f ≤ p/(500*I.m) := by
  have hc := (normalized_step_bounds I a F p f g l step hm hf hr ha ha' hp hp' hg hl hquality hscale).2.2
  have hdiff : residual I F (fun e => f e+step e)-residual I F f=I.cost step := by
    rw [residual,cost_add,residual]
    ring
  rw [hdiff]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 500) (Nat.cast_pos.mpr hm))).mpr
  nlinarith only [hc]

/-- The normalized cost estimate controls residual movement for any
positive effective parameter at most twice the requested one. This
form applies after combining all scalar normalization errors. -/
theorem direction_residual_change_of_effective_parameter (I : Instance) (a F q p eta : ℝ)
    (f g l d : Fin I.m → ℝ) (hm : 0<I.m) (hf : StrictlyInside I f)
    (hres : 0<residual I F f) (ha : 0≤a) (ha' : a≤1/500)
    (hp : 0<p) (hp' : p≤1) (hphi : p≤2*q)
    (hg' : GradientTolerance (lengths I a f) g (gradient I a F f) (p/8))
    (hl : VectorApprox 2 l (lengths I a f))
    (hqual : dot g d/weightedLength l d≤-p)
    (hnorm : eta*dot g d=-p^2/50) :
    |residual I F (fun e => f e+eta*d e)-residual I F f|/residual I F f≤q/(250*I.m) := by
  have hlen0 : 0 ≤ weightedLength l d := Finset.sum_nonneg fun e _ => abs_nonneg _
  have hlen : 0 < weightedLength l d := by
    by_contra hn
    have hz := le_antisymm (not_lt.mp hn) hlen0
    rw [hz,div_zero] at hqual
    linarith only [hqual,hp]
  have hratio := (div_le_iff₀ hlen).mp hqual
  have hdot : dot g d < 0 :=
    lt_of_le_of_lt hratio (mul_neg_of_neg_of_pos (neg_neg_of_pos hp) hlen)
  have heta : 0 < eta := by
    have hn : eta*dot g d=-p^2/50 := hnorm
    have hsquare := sq_pos_of_pos hp
    nlinarith only [hn,hdot,hsquare]
  have hdscale : dot g (fun e => eta*d e)=eta*dot g d := by
    simp only [dot,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hlscale : weightedLength l (fun e => eta*d e)=eta*weightedLength l d := by
    unfold weightedLength
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [show l e*(eta*d e)=eta*(l e*d e) by ring,abs_mul,abs_of_pos heta]
  have hquality : p*weightedLength l (fun e => eta*d e) ≤
      -dot g (fun e => eta*d e) := by
    rw [hlscale,hdscale]
    have hh := mul_le_mul_of_nonneg_left hratio heta.le
    nlinarith only [hh]
  have hscale : dot g (fun e => eta*d e)=-p^2/50 := by
    rw [hdscale]
    exact hnorm
  have hd := normalized_residual_drift I a F p f g l (fun e => eta*d e)
    hm hf hres ha ha' hp hp' hg' hl hquality hscale
  apply hd.trans
  apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 500*I.m)
    (by positivity : (0:ℝ) < 250*I.m)).mpr
  have hmp := mul_le_mul_of_nonneg_right hphi (Nat.cast_nonneg I.m)
  nlinarith only [hmp]

/-- Scalar-rounded normalization gives the relative residual drift
needed by the epoch proof, at any permitted explicit barrier exponent. -/
theorem rounded_step_residual_change_at_exponent (I : Instance) (a F q s r : ℝ)
    (f g l d : Fin I.m → ℝ) (hm : 0 < I.m) (hf : StrictlyInside I f)
    (hres : 0 < residual I F f) (ha : 0 ≤ a) (ha' : a ≤ 1/500)
    (hq : 0 < q) (hq' : q ≤ 1/2) (hslo : (1/2:ℝ) ≤ s) (hshi : s ≤ 2)
    (hrlo : (1/2:ℝ) ≤ r) (hrhi : r ≤ 2)
    (hg : GradientTolerance (lengths I a f) (fun e => s*g e) (gradient I a F f) (q/16))
    (hl : VectorApprox 2 l (lengths I a f))
    (hqual : dot g d/weightedLength l d ≤ -4*q) :
    |residual I F (fun e => f e+(r*q^2/(50*|dot g d|))*d e)-residual I F f|/
      residual I F f ≤ q/(250*I.m) := by
  obtain ⟨p,hplo,hphi,hg',hqual',hnorm⟩ :=
    rounded_step_normalization_at_exponent I a F q s r f g l d hq hslo hshi hrlo hrhi hg hqual
  have hp : 0 < p := (by linarith only [hq] : 0 < q/2).trans_le hplo
  have hp' : p ≤ 1 := hphi.trans (by linarith only [hq'])
  exact direction_residual_change_of_effective_parameter I a F q p
    (r*q^2/(50*|dot g d|)) f (fun e => s*g e) l d hm hf hres ha ha' hp hp' hphi hg' hl hqual' hnorm

private theorem scalar_approx_mono {b c x y : ℝ} (hb : 0 < b) (hbc : b ≤ c)
    (h : ScalarApprox b x y) : ScalarApprox c x y := by
  have hc : 0 < c := hb.trans_le hbc
  have hi := (inv_le_inv₀ hc hb).mpr hbc
  exact ⟨h.1,h.2.1,(mul_le_mul_of_nonneg_right hi h.2.1.le).trans h.2.2.1,
    h.2.2.2.trans (mul_le_mul_of_nonneg_right hbc h.2.1.le)⟩

/-- The residual snapshot throughout at most m scalar-rounded steps is
within the eight-Detect-threshold tolerance `1+q/4`. This is the epoch
accumulation proof of Chen et al., Lemma 9.1 (page 70), at the supplied
barrier exponent and with scalar normalization rounding included. -/
theorem rounded_epoch_residual_approx_of_steps (I : Instance) (a F q : ℝ) (N : ℕ)
    (f g l d : ℕ → Fin I.m → ℝ) (s r : ℕ → ℝ)
    (hm : 0 < I.m) (hN : N ≤ I.m) (ha : 0 ≤ a) (ha' : a ≤ 1/500)
    (hq : 0 < q) (hq' : q ≤ 1/2)
    (hdom : ∀ t ≤ N,StrictlyInside I (f t) ∧ 0 < residual I F (f t))
    (hsteps : ∀ i < N,
      (1/2:ℝ) ≤ s i ∧ s i ≤ 2 ∧ (1/2:ℝ) ≤ r i ∧ r i ≤ 2 ∧
      GradientTolerance (lengths I a (f i)) (fun e => s i*g i e) (gradient I a F (f i)) (q/16) ∧
      VectorApprox 2 (l i) (lengths I a (f i)) ∧
      dot (g i) (d i)/weightedLength (l i) (d i) ≤ -4*q ∧
      f (i+1)=(fun e => f i e+(r i*q^2/(50*|dot (g i) (d i)|))*d i e)) :
    ∀ t ≤ N,ScalarApprox (1+q/4) (residual I F (f 0)) (residual I F (f t)) := by
  have hstep : ∀ i < N,|residual I F (f (i+1))-residual I F (f i)|/residual I F (f i) ≤
      (q/250)/I.m := by
    intro i hi
    obtain ⟨hslo,hshi,hrlo,hrhi,hg,hl,hqual,hnext⟩ := hsteps i hi
    rw [hnext,div_div]
    exact rounded_step_residual_change_at_exponent I a F q (s i) (r i) (f i) (g i) (l i) (d i)
      hm (hdom i (by omega)).1 (hdom i (by omega)).2 ha ha' hq hq' hslo hshi hrlo hrhi hg hl hqual
  intro t ht
  have hh := epoch_residual_approx_prefix (fun i => residual I F (f i)) I.m N (q/250)
    hm hN (by linarith only [hq]) (by linarith only [hq'])
    (fun i hi => (hdom i hi).2) hstep t ht
  exact scalar_approx_mono (by linarith only [hq]) (by linarith only [hq]) hh

/-- Starting from the source initialization and scalar-rounded step
conditions, budget preservation supplies the domain hypotheses of the
stored-exponent residual proof. No residual-stability oracle is assumed. -/
theorem rounded_run_residual_approx (I : Instance) (U N : ℕ) (F q : ℝ)
    (f g l d : ℕ → Fin I.m → ℝ) (s r : ℕ → ℝ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ I.m*U) (hN : N ≤ I.m)
    (hnums : NumbersBounded I U) (hq : 0 < q) (hqUpper : q ≤ 1/2)
    (hf0 : StrictlyInside I (f 0)) (hroute0 : I.Routes (f 0))
    (hres0 : 0 < residual I F (f 0))
    (hpot0 : potential I (Num.IPM.alphaPrime I.m U) F (f 0) ≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hsteps : ∀ i < N,
      (1/2:ℝ) ≤ s i ∧ s i ≤ 2 ∧ (1/2:ℝ) ≤ r i ∧ r i ≤ 2 ∧
      GradientTolerance (lengths I (Num.IPM.alphaPrime I.m U) (f i))
        (fun e => s i*g i e) (gradient I (Num.IPM.alphaPrime I.m U) F (f i)) (q/16) ∧
      VectorApprox 2 (l i) (lengths I (Num.IPM.alphaPrime I.m U) (f i)) ∧
      IsCirculation I (d i) ∧ dot (g i) (d i)/weightedLength (l i) (d i) ≤ -4*q ∧
      f (i+1)=(fun e => f i e+(r i*q^2/(50*|dot (g i) (d i)|))*d i e)) :
    ∀ t ≤ N,ScalarApprox (1+q/4) (residual I F (f 0)) (residual I F (f t)) := by
  have hbudget := rounded_run_budget I U N F q f g l d s r hm hU hsize hnums hq hqUpper
    hf0 hroute0 hres0 hpot0 hsteps
  have hs : (2:ℝ) ≤ I.m*(U:ℝ) := by exact_mod_cast hsize
  have ha := Num.IPM.alphaPrime_bounds I U hsize
  have ha0 : 0 ≤ Num.IPM.alphaPrime I.m U :=
    (div_nonneg (alpha_pos I U hs).le (by norm_num : (0:ℝ) ≤ 10)).trans ha.1
  apply rounded_epoch_residual_approx_of_steps I (Num.IPM.alphaPrime I.m U) F q N f g l d s r
    hm hN ha0 (ha.2.trans (alpha_le I U hs)) hq hqUpper
    (fun i hi => ⟨(hbudget i hi).2.1,(hbudget i hi).2.2.1⟩)
  intro i hi
  obtain ⟨hslo,hshi,hrlo,hrhi,hg,hl,_,hqual,hnext⟩ := hsteps i hi
  exact ⟨hslo,hshi,hrlo,hrhi,hg,hl,hqual,hnext⟩

end MinCostFlow.IPM.Machine
