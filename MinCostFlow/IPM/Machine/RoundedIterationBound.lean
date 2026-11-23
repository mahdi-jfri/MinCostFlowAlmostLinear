module

public import MinCostFlow.IPM.Machine.PrecisionRun
public import MinCostFlow.IPM.IterationBound
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Counting scalar-rounded steps at the stored exponent

The adapted Lemma 9.3 of Chen et al., arXiv:2203.00671v2 (page 71),
gives a drop of at least `q²/2000` for each scalar-rounded step even
though its effective parameter changes. Apply the counting proof of
Theorem 4.3 (page 25) with parameter `q/2`. This gives the explicit bound
`ceil(800000 m log(mU) / q²)` without treating the rounded run as one
with a constant effective step parameter.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- The uniform iteration limit for scalar-rounded requested parameter `q`. -/
def roundedIterationLimit (I : Instance) (U : ℕ) (q : ℝ) : ℕ :=
  ⌈800000*I.m*Real.log (I.m*(U:ℝ))/q^2⌉₊

/-- Every scalar-rounded step has the same lower bound on potential drop,
although the effective step parameter can vary from one step to the next. -/
theorem rounded_run_uniform_drop (I : Instance) (U N : ℕ) (F q : ℝ)
    (f g l d : ℕ → Fin I.m → ℝ) (s r : ℕ → ℝ)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hq : 0<q) (hqUpper : q≤1/2)
    (hf0 : StrictlyInside I (f 0)) (hroute0 : I.Routes (f 0))
    (hres0 : 0<residual I F (f 0))
    (hpot0 : potential I (Num.IPM.alphaPrime I.m U) F (f 0)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hsteps : ∀ i<N,
      (1/2:ℝ)≤s i ∧ s i≤2 ∧ (1/2:ℝ)≤r i ∧ r i≤2 ∧
      GradientTolerance (lengths I (Num.IPM.alphaPrime I.m U) (f i))
        (fun e => s i*g i e) (gradient I (Num.IPM.alphaPrime I.m U) F (f i)) (q/16) ∧
      VectorApprox 2 (l i) (lengths I (Num.IPM.alphaPrime I.m U) (f i)) ∧
      IsCirculation I (d i) ∧ dot (g i) (d i)/weightedLength (l i) (d i)≤-4*q ∧
      f (i+1)=fun e => f i e+(r i*q^2/(50*|dot (g i) (d i)|))*d i e) :
    ∀ i<N,potential I (Num.IPM.alphaPrime I.m U) F (f (i+1))≤
      potential I (Num.IPM.alphaPrime I.m U) F (f i)-(q/2)^2/500 := by
  have hbudget := rounded_run_budget I U N F q f g l d s r hm hU hsize hnums
    hq hqUpper hf0 hroute0 hres0 hpot0 hsteps
  have hs : (2:ℝ)≤I.m*(U:ℝ) := by exact_mod_cast hsize
  have ha := Num.IPM.alphaPrime_bounds I U hsize
  have ha0 : 0≤Num.IPM.alphaPrime I.m U :=
    (div_nonneg (alpha_pos I U hs).le (by norm_num : (0:ℝ)≤10)).trans ha.1
  intro i hi
  obtain ⟨hroute,hf,hres,_⟩ := hbudget i hi.le
  obtain ⟨hslo,hshi,hrlo,hrhi,hg,hl,hd,hqual,hnext⟩ := hsteps i hi
  have hdrop := rounded_step_decrease_at_exponent I U _ F q (s i) (r i)
    (f i) (g i) (l i) (d i) hm (Nat.cast_nonneg _) hs ha0 ha.2
    hnums hf hroute hres hq hqUpper hslo hshi hrlo hrhi hg hl hd hqual
  dsimp only at hdrop
  rw [← hnext] at hdrop
  have heq : (q/2)^2/500=q^2/2000 := by ring
  rw [heq]
  exact hdrop.2.2.2

/-- The explicit count suffices for the original potential-gap counting
lemma, with `q/2` as its uniform lower effective parameter. -/
theorem roundedIterationLimit_bound (I : Instance) (U : ℕ) (q : ℝ) (hq : 0<q) :
    200000*I.m*Real.log (I.m*(U:ℝ))≤(roundedIterationLimit I U q:ℝ)*(q/2)^2 := by
  have hn : 800000*I.m*Real.log (I.m*(U:ℝ))≤(roundedIterationLimit I U q:ℝ)*q^2 :=
    (div_le_iff₀ (sq_pos_of_pos hq)).mp (Nat.le_ceil _)
  nlinarith only [hn]

/-- Theorem 4.3's counting argument (page 25), applied to the scalar-rounded
run at `alphaPrime`, yields a feasible flow within the source residual
threshold after the explicit rounded iteration limit. -/
theorem rounded_run_residual_bound (I : Instance) (U : ℕ) (F q : ℝ)
    (f g l d : ℕ → Fin I.m → ℝ) (s r : ℕ → ℝ)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hq : 0<q) (hqUpper : q≤1/2)
    (hf0 : StrictlyInside I (f 0)) (hroute0 : I.Routes (f 0))
    (hres0 : 0<residual I F (f 0))
    (hpot0 : potential I (Num.IPM.alphaPrime I.m U) F (f 0)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hsteps : ∀ i<roundedIterationLimit I U q,
      (1/2:ℝ)≤s i ∧ s i≤2 ∧ (1/2:ℝ)≤r i ∧ r i≤2 ∧
      GradientTolerance (lengths I (Num.IPM.alphaPrime I.m U) (f i))
        (fun e => s i*g i e) (gradient I (Num.IPM.alphaPrime I.m U) F (f i)) (q/16) ∧
      VectorApprox 2 (l i) (lengths I (Num.IPM.alphaPrime I.m U) (f i)) ∧
      IsCirculation I (d i) ∧ dot (g i) (d i)/weightedLength (l i) (d i)≤-4*q ∧
      f (i+1)=fun e => f i e+(r i*q^2/(50*|dot (g i) (d i)|))*d i e) :
    I.IsFeasible (f (roundedIterationLimit I U q)) ∧
      I.cost (f (roundedIterationLimit I U q))≤F+Real.rpow (I.m*(U:ℝ)) (-10) := by
  have hbudget := rounded_run_budget I U _ F q f g l d s r hm hU hsize hnums
    hq hqUpper hf0 hroute0 hres0 hpot0 hsteps
  obtain ⟨hroute,hf,hres,_⟩ := hbudget (roundedIterationLimit I U q) le_rfl
  have hdrop := rounded_run_uniform_drop I U _ F q f g l d s r hm hU hsize hnums
    hq hqUpper hf0 hroute0 hres0 hpot0 hsteps
  have huReal : (0:ℝ)<U := by exact_mod_cast (show 0<U by omega)
  have hresBound := residual_after_steps I (Num.IPM.alphaPrime I.m U) F U (q/2) f
    (roundedIterationLimit I U q) hm huReal hf hres hpot0 hdrop
    (roundedIterationLimit_bound I U q hq)
  refine ⟨⟨hroute,fun e => ⟨(hf e).1.le,(hf e).2.le⟩⟩,?_⟩
  unfold residual at hresBound
  linarith only [hresBound]

end MinCostFlow.IPM.Machine
