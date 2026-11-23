module

public import MinCostFlow.IPM.Update
import MinCostFlow.IPM.ResidualStability
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Residual movement of one normalized step

Chen et al., arXiv:2203.00671v2, Lemma 9.1 (page 70), uses Lemma
4.8 to bound the change of the cost residual between full refreshes.
Keeping the effective step parameter in this estimate gives the bound
`q/(50m)` per step. This avoids the extra inverse power of the detection
threshold that arises from replacing the parameter by one too early.
-/

public section
namespace MinCostFlow.IPM

/-- A negative min-ratio guarantee forces a positive direction length
and a negative gradient dot product. -/
theorem Update.direction_sign {I : Instance} {U F q : ℝ} {f : Fin I.m → ℝ}
    (s : Update I U F q f) (hq : 0 < q) :
    0 < weightedLength s.lApprox s.direction ∧ dot s.gApprox s.direction < 0 := by
  have hlen0 : 0 ≤ weightedLength s.lApprox s.direction := Finset.sum_nonneg fun e _ => abs_nonneg _
  have hlen : 0 < weightedLength s.lApprox s.direction := by
    by_contra hn
    have hz := le_antisymm (not_lt.mp hn) hlen0
    have hh := s.quality
    rw [hz, div_zero] at hh
    linarith only [hq, hh]
  have hh := (div_le_iff₀ hlen).mp s.quality
  exact ⟨hlen, lt_of_le_of_lt hh (mul_neg_of_neg_of_pos (neg_neg_of_pos hq) hlen)⟩

/-- The normalization in Theorem 4.3 makes the multiplier positive. -/
theorem Update.stepSize_pos {I : Instance} {U F q : ℝ} {f : Fin I.m → ℝ}
    (s : Update I U F q f) (hq : 0 < q) : 0 < s.stepSize := by
  have hd := (s.direction_sign hq).2
  have hn := s.normalization
  have hs := sq_pos_of_pos hq
  by_contra hh
  have hp := mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hh) hd.le
  linarith only [hp, hn, hs]

/-- The sharper relative residual bound for a normalized IPM step.
This is the cost-movement estimate used in the stored-residual epoch
analysis of Chen et al., Lemma 9.1 (page 70). -/
theorem Update.residual_change {I : Instance} {U F q : ℝ} {f : Fin I.m → ℝ}
    (s : Update I U F q f) (hm : 0 < I.m) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hf : StrictlyInside I f) (hr : 0 < residual I F f) (hq : 0 < q) (hq' : q < 1) :
    |residual I F s.next-residual I F f| / residual I F f ≤ q/(50*I.m) := by
  have ha := alpha_pos I U hsize
  have ha' : alpha I U ≤ 1/2 := (alpha_le I U hsize).trans (by norm_num)
  have hdir := s.direction_sign hq
  have hcost := lemma_4_8 I (alpha I U) F (q/8) q f s.gApprox s.lApprox s.direction
    hm hf hr ha.le ha' (by linarith only [hq']) hq hq'
    s.gradient_error s.length_error hdir.1 s.quality
  have hstep := s.stepSize_pos hq
  have habs : s.stepSize*|dot s.gApprox s.direction| = q^2/50 := by
    rw [abs_of_neg hdir.2]
    linarith only [s.normalization]
  have hdiff : residual I F s.next-residual I F f = s.stepSize*I.cost s.direction := by
    simp only [residual, Update.next, Instance.cost, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    have hid : (∑ e, ((I.edge e).cost : ℝ)*(s.stepSize*s.direction e)) =
        ∑ e, s.stepSize*(((I.edge e).cost : ℝ)*s.direction e) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [hid]
    ring
  rw [hdiff, abs_mul, abs_of_pos hstep]
  calc
    (s.stepSize*|I.cost s.direction|)/residual I F f =
        s.stepSize*(|I.cost s.direction|/residual I F f) := mul_div_assoc _ _ _
    _ ≤ s.stepSize*(|dot s.gApprox s.direction|/(q*I.m)) :=
      mul_le_mul_of_nonneg_left hcost hstep.le
    _ = q/(50*I.m) := by
      rw [← mul_div_assoc, habs]
      field_simp [hq.ne', (Nat.cast_pos.mpr hm : (0 : ℝ) < I.m).ne']

end MinCostFlow.IPM
