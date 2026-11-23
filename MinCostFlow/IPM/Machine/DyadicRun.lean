module

public import MinCostFlow.IPM.Machine.PrecisionNormalizationBridge
public import MinCostFlow.IPM.Machine.RoundedIterationBound
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith

/-!
# Runs with the exactly stored dyadic normalization

The machine requests `25/32` times the source normalization. Combine that
factor, the DS rounding, and the tighter epoch residual ratio before
applying the effective-step argument of Chen et al., arXiv:2203.00671v2,
Lemma 9.3 (page 71). Each such step has the same `q²/2000` potential drop.
The proof of Theorem 4.3 (page 25) then counts these actual dyadic-request
steps without dropping the request-storage factor from the model.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- A nonfailed scalar-rounded step with the exact dyadic request.
The stored residual ratio lies in `[3/4,4/3]`; the DS may choose any
normalization in its stated factor-two interval. The witnesses contain
only the step data and its approximation and circulation conditions. -/
def DyadicAdmissibleStep (I : Instance) (U : ℕ) (F q : ℝ)
    (f next : Fin I.m → ℝ) : Prop :=
  ∃ (g l d : Fin I.m → ℝ) (s r : ℝ),
    ((3/4:ℝ)≤s ∧ s≤4/3) ∧ ((1/2:ℝ)≤r ∧ r≤2) ∧
    GradientTolerance (lengths I (Num.IPM.alphaPrime I.m U) f)
      (fun e => s*g e) (gradient I (Num.IPM.alphaPrime I.m U) F f) (q/16) ∧
    VectorApprox 2 l (lengths I (Num.IPM.alphaPrime I.m U) f) ∧
    IsCirculation I d ∧ dot g d/weightedLength l d≤-4*q ∧
    next=fun e => f e+(((25/32:ℝ)*r)*q^2/(50*|dot g d|))*d e

/-- Every dyadic-request admissible step preserves the domain and gives
the potential drop from the adapted Lemma 9.3 (page 71). -/
theorem DyadicAdmissibleStep.spec (I : Instance) (U : ℕ) (F q : ℝ)
    (f next : Fin I.m → ℝ) (hm : 0<I.m) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f) (hroute : I.Routes f)
    (hres : 0<residual I F f) (hq : 0<q) (hqUpper : q≤1/2)
    (hstep : DyadicAdmissibleStep I U F q f next) :
    I.Routes next ∧ StrictlyInside I next ∧ 0<residual I F next ∧
      potential I (Num.IPM.alphaPrime I.m U) F next≤
        potential I (Num.IPM.alphaPrime I.m U) F f-q^2/2000 := by
  obtain ⟨g,l,d,s,r,hs,hr,hg,hl,hd,hqual,rfl⟩ := hstep
  have hsReal : (2:ℝ)≤I.m*(U:ℝ) := by exact_mod_cast hsize
  have ha := Num.IPM.alphaPrime_bounds I U hsize
  have ha0 : 0≤Num.IPM.alphaPrime I.m U :=
    (div_nonneg (alpha_pos I U hsReal).le (by norm_num : (0:ℝ)≤10)).trans ha.1
  exact dyadic_request_step_decrease I U _ F q s r f g l d hm (Nat.cast_nonneg _) hsReal ha0 ha.2
    hnums hf hroute hres hq hqUpper hs hr hg hl hd hqual

/-- Every finite run of actual dyadic-request steps preserves routing,
interiority, positive residual and the original potential budget. -/
theorem dyadic_run_budget (I : Instance) (U N : ℕ) (F q : ℝ)
    (f : ℕ → Fin I.m → ℝ) (hm : 0<I.m) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hq : 0<q) (hqUpper : q≤1/2)
    (hf0 : StrictlyInside I (f 0)) (hroute0 : I.Routes (f 0))
    (hres0 : 0<residual I F (f 0))
    (hpot0 : potential I (Num.IPM.alphaPrime I.m U) F (f 0)≤200*I.m*Real.log (I.m*(U:ℝ)))
    (hsteps : ∀ i<N,DyadicAdmissibleStep I U F q (f i) (f (i+1))) :
    ∀ k≤N,I.Routes (f k) ∧ StrictlyInside I (f k) ∧ 0<residual I F (f k) ∧
      potential I (Num.IPM.alphaPrime I.m U) F (f k)≤200*I.m*Real.log (I.m*(U:ℝ)) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨hroute0,hf0,hres0,hpot0⟩
  | succ k ih =>
    intro hk
    obtain ⟨hroute,hf,hres,hpot⟩ := ih (by omega)
    have hh := (hsteps k (by omega)).spec I U F q _ _ hm hsize hnums hf hroute hres hq hqUpper
    refine ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.trans ?_⟩
    linarith only [hpot,sq_nonneg q]

/-- The explicit scalar-rounded iteration count applies to all runs with
the actual stored request, giving a feasible flow within the source's
residual threshold. This is Theorem 4.3's counting proof (page 25). -/
theorem dyadic_run_residual_bound (I : Instance) (U : ℕ) (F q : ℝ)
    (f : ℕ → Fin I.m → ℝ) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hq : 0<q) (hqUpper : q≤1/2)
    (hf0 : StrictlyInside I (f 0)) (hroute0 : I.Routes (f 0))
    (hres0 : 0<residual I F (f 0))
    (hpot0 : potential I (Num.IPM.alphaPrime I.m U) F (f 0)≤200*I.m*Real.log (I.m*(U:ℝ)))
    (hsteps : ∀ i<roundedIterationLimit I U q,DyadicAdmissibleStep I U F q (f i) (f (i+1))) :
    I.IsFeasible (f (roundedIterationLimit I U q)) ∧
      I.cost (f (roundedIterationLimit I U q))≤F+Real.rpow (I.m*(U:ℝ)) (-10) := by
  have hbudget := dyadic_run_budget I U _ F q f hm hsize hnums hq hqUpper hf0 hroute0 hres0 hpot0 hsteps
  have hdrop : ∀ i<roundedIterationLimit I U q,
      potential I (Num.IPM.alphaPrime I.m U) F (f (i+1))≤
        potential I (Num.IPM.alphaPrime I.m U) F (f i)-(q/2)^2/500 := by
    intro i hi
    obtain ⟨hroute,hf,hres,_⟩ := hbudget i hi.le
    have hh := ((hsteps i hi).spec I U F q _ _ hm hsize hnums hf hroute hres hq hqUpper).2.2.2
    have heq : (q/2)^2/500=q^2/2000 := by ring
    rwa [heq]
  obtain ⟨hroute,hf,hres,_⟩ := hbudget (roundedIterationLimit I U q) le_rfl
  have hresBound := residual_after_steps I (Num.IPM.alphaPrime I.m U) F U (q/2) f
    (roundedIterationLimit I U q) hm (by exact_mod_cast hU) hf hres hpot0 hdrop
    (roundedIterationLimit_bound I U q hq)
  refine ⟨⟨hroute,fun e => ⟨(hf e).1.le,(hf e).2.le⟩⟩,?_⟩
  unfold residual at hresBound
  linarith only [hresBound]

end MinCostFlow.IPM.Machine
