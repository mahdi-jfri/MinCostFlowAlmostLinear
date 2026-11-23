module

public import MinCostFlow.IPM.Machine.DyadicRun
import MinCostFlow.IPM.StoredStep
import MinCostFlow.IPM.WeightedBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Charging movement from the actual dyadic-request step

The source normalization moves by at most `q/200` in computed lengths.
The `25/32` request factor and at most twofold DS scalar rounding give
movement at most `q/128`. This remains below a constant number of the
Detect thresholds `q/32`, as needed by the charging argument of Chen
et al., arXiv:2203.00671v2, Lemma 9.4 (pages 71--72).
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- Including the exact request factor and every permitted DS scalar
choice changes the source movement bound to at most `q/128`. -/
theorem dyadic_requested_movement {n : ℕ} (q r : ℝ) (g l d : Fin n → ℝ)
    (hq : 0<q) (hr : (1/2:ℝ)≤r ∧ r≤2)
    (hqual : dot g d/weightedLength l d≤-4*q) :
    weightedLength l (fun e => (((25/32:ℝ)*r)*q^2/(50*|dot g d|))*d e)≤q/128 := by
  have hsource := stored_step_movement q g l d hq hqual
  have hfactor : 0≤(25/32:ℝ)*r := mul_nonneg (by norm_num) (by linarith only [hr.1])
  have heq : weightedLength l (fun e => (((25/32:ℝ)*r)*q^2/(50*|dot g d|))*d e)=
      ((25/32:ℝ)*r)*weightedLength l (fun e => (q^2/(50*|dot g d|))*d e) := by
    unfold weightedLength
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [show l e*((((25/32:ℝ)*r)*q^2/(50*|dot g d|))*d e)=
      ((25/32:ℝ)*r)*(l e*((q^2/(50*|dot g d|))*d e)) by ring,
      abs_mul,abs_of_nonneg hfactor]
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left hsource hfactor
  have hrq := mul_le_mul_of_nonneg_right hr.2 hq.le
  nlinarith only [hh,hrq]

/-- Every dyadic admissible step has the required computed-length
movement budget, with the same computed lengths as its witnesses. -/
theorem DyadicAdmissibleStep.stored_movement (I : Instance) (U : ℕ) (F q : ℝ)
    (f next : Fin I.m → ℝ) (hq : 0<q)
    (hstep : DyadicAdmissibleStep I U F q f next) :
    ∃ l : Fin I.m → ℝ,VectorApprox 2 l (lengths I (Num.IPM.alphaPrime I.m U) f) ∧
      weightedLength l (fun e => next e-f e)≤q/128 := by
  obtain ⟨g,l,d,s,r,_,hr,_,hl,_,hqual,rfl⟩ := hstep
  refine ⟨l,hl,?_⟩
  simp only [add_sub_cancel_left]
  exact dyadic_requested_movement q r g l d hq hr hqual

/-- The true current lengths pay at most twice the computed-length
movement. This bounds geometric motion while the old cache is refreshed. -/
theorem DyadicAdmissibleStep.true_movement (I : Instance) (U : ℕ) (F q : ℝ)
    (f next : Fin I.m → ℝ) (hf : StrictlyInside I f) (hq : 0<q)
    (hstep : DyadicAdmissibleStep I U F q f next) :
    weightedLength (lengths I (Num.IPM.alphaPrime I.m U) f) (fun e => next e-f e)≤q/64 := by
  obtain ⟨l,hl,hmovement⟩ := hstep.stored_movement I U F q f next hq
  have hh := weightedLength_le_two I (Num.IPM.alphaPrime I.m U) f l (fun e => next e-f e) hf hl
  linarith only [hh,hmovement]

/-- The movement deposit is below the five-Detect-threshold budget used
by Lemma 9.4's existing charging theorem, for threshold `eps=q/32`. -/
theorem DyadicAdmissibleStep.detect_movement (I : Instance) (U : ℕ) (F q : ℝ)
    (f next : Fin I.m → ℝ) (hq : 0<q)
    (hstep : DyadicAdmissibleStep I U F q f next) :
    ∃ l : Fin I.m → ℝ,VectorApprox 2 l (lengths I (Num.IPM.alphaPrime I.m U) f) ∧
      weightedLength l (fun e => next e-f e)≤5*(q/32) := by
  obtain ⟨l,hl,hmovement⟩ := hstep.stored_movement I U F q f next hq
  exact ⟨l,hl,hmovement.trans (by linarith only [hq])⟩

end MinCostFlow.IPM.Machine
