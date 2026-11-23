module

public import MinCostFlow.IPM.Machine.PrecisionRoundedStep
public import MinCostFlow.IPM.Machine.PrecisionInitialPotential
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith

/-!
# Precision ranges along a rounded IPM run

Starting from the half-slack initialization, the scalar-rounded step
argument preserves the potential budget at the representable exponent.
Each nonterminal iterate therefore has the dyadic slack and residual
ranges required by the numerical procedures. The hypotheses describe
step choices and their approximation bounds, not the conclusions of
the numerical-range proof.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- Domain and potential-budget preservation for every finite run of
scalar-rounded steps, with all functions evaluated at `alphaPrime`. -/
theorem rounded_run_budget (I : Instance) (U N : ℕ) (F q : ℝ)
    (f g l d : ℕ → Fin I.m → ℝ) (s r : ℕ → ℝ)
    (hm : 0 < I.m) (_hU : 1 ≤ U) (hsize : 2 ≤ I.m*U)
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
      f (i+1) = fun e => f i e+(r i*q^2/(50*|dot (g i) (d i)|))*d i e) :
    ∀ k ≤ N, I.Routes (f k) ∧ StrictlyInside I (f k) ∧
      0 < residual I F (f k) ∧
      potential I (Num.IPM.alphaPrime I.m U) F (f k) ≤
        200*I.m*Real.log (I.m*(U:ℝ)) := by
  have hs : (2:ℝ) ≤ I.m*(U:ℝ) := by exact_mod_cast hsize
  have ha := Num.IPM.alphaPrime_bounds I U hsize
  have ha0 : 0 ≤ Num.IPM.alphaPrime I.m U :=
    (div_nonneg (alpha_pos I U hs).le (by norm_num : (0:ℝ) ≤ 10)).trans ha.1
  intro k
  induction k with
  | zero => intro _; exact ⟨hroute0,hf0,hres0,hpot0⟩
  | succ k ih =>
    intro hk
    obtain ⟨hroute,hf,hr,hpot⟩ := ih (by omega)
    obtain ⟨hslo,hshi,hrlo,hrhi,hg,hl,hd,hqual,hnext⟩ := hsteps k (by omega)
    have hh := rounded_step_decrease_at_exponent I U _ F q (s k) (r k)
      (f k) (g k) (l k) (d k) hm (Nat.cast_nonneg _) hs ha0 ha.2
      hnums hf hroute hr hq hqUpper hslo hshi hrlo hrhi hg hl hd hqual
    dsimp only at hh
    rw [← hnext] at hh
    refine ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.trans ?_⟩
    linarith only [hpot,sq_nonneg q]

/-- The nonterminal ranges follow directly from an iterate's preserved
budget, routing and interiority. These are precisely the real range
premises of the length and gradient numerical contracts. -/
theorem nonterminal_numeric_ranges (I : Instance) (U : ℕ) (F : ℝ)
    (f : Fin I.m → ℝ) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ I.m*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f) (hroute : I.Routes f)
    (hpot : potential I (Num.IPM.alphaPrime I.m U) F f ≤
      200*I.m*Real.log (I.m*(U:ℝ)))
    (hF : -(I.m*(U:ℝ)^2) ≤ F) (hr : 1/4 < residual I F f) :
    (1/(2:ℝ)^(slackRangeExponent I.m U) ≤ residual I F f ∧
      residual I F f ≤ (2:ℝ)^(slackRangeExponent I.m U)) ∧
    ∀ e, (1/(2:ℝ)^(slackRangeExponent I.m U) ≤ (I.edge e).upper-f e ∧
      (I.edge e).upper-f e ≤ (2:ℝ)^(slackRangeExponent I.m U)) ∧
      (1/(2:ℝ)^(slackRangeExponent I.m U) ≤ f e-(I.edge e).lower ∧
      f e-(I.edge e).lower ≤ (2:ℝ)^(slackRangeExponent I.m U)) := by
  have hu : 0 < U := by omega
  have hfeas : I.IsFeasible f := ⟨hroute,fun e => ⟨(hf e).1.le,(hf e).2.le⟩⟩
  refine ⟨residual_dyadic_range I U F f hm hu hnums hfeas hF hr, ?_⟩
  intro e
  have hs : (2:ℝ) ≤ I.m*(U:ℝ) := by exact_mod_cast hsize
  have hlo := slacks_dyadic_lower I U F f hm hU hsize hf hpot
    (residual_log_lower_of_nonterminal I U F f hs hr) e
  have hhi := slacks_dyadic_upper I U f hm hu hnums hf e
  exact ⟨⟨hlo.1,hhi.1⟩,⟨hlo.2,hhi.2⟩⟩

end MinCostFlow.IPM.Machine
