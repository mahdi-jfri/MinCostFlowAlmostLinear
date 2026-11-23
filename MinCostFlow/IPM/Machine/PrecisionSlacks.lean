module

public import MinCostFlow.IPM.HiddenBounds
public import MinCostFlow.Num.IPM.AlphaFacts
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Slack ranges for fixed-point precision selection

The precision argument following Chen et al., arXiv:2203.00671v2,
Lemma 9.2 (pages 70--71), bounds each inverse slack power from the
barrier sum before the residual stopping threshold. The full potential
can be negative, so it cannot itself bound those powers. Using its
log-residual term gives barrier budget `400m log(mU)`.

The bounds here allow every exponent between the analytic `alpha/10`
and `alpha`, including the representable `alphaPrime`. They apply to
the potential computed with that exponent. They do not assert that
changing the exponent only changes a length by a constant factor.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- The logarithm of the barrier budget is at most eleven times the
input logarithm. This retains constants in the later squared-log bound. -/
theorem log_barrier_budget_le (I : Instance) (U : ℝ) (hm : 0 < I.m)
    (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U) :
    Real.log (ipmBarrierBound I U) ≤ 11*Real.log (I.m*U) := by
  have hmpos : (0 : ℝ) < I.m := Nat.cast_pos.mpr hm
  have hx : 0 < (I.m : ℝ)*U := lt_of_lt_of_le (by norm_num) hsize
  have hlogpos : 0 < Real.log (I.m*U) := Real.log_pos (lt_of_lt_of_le (by norm_num) hsize)
  have hmle : (I.m : ℝ) ≤ I.m*U := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hU hmpos.le
  have hlogm := Real.log_le_log hmpos hmle
  have hloglog : Real.log (Real.log (I.m*U)) ≤ Real.log (I.m*U) :=
    (Real.log_le_sub_one_of_pos hlogpos).trans (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log (I.m*U) := Real.log_le_log (by norm_num) hsize
  have h400 : Real.log 400 ≤ 9*Real.log (I.m*U) := by
    calc
      Real.log 400 ≤ Real.log ((2 : ℝ)^9) := Real.log_le_log (by norm_num) (by norm_num)
      _ = 9*Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog2 (by norm_num)
  rw [ipmBarrierBound,Real.log_mul (mul_pos (by norm_num) hmpos).ne' hlogpos.ne',
    Real.log_mul (by norm_num : (400 : ℝ) ≠ 0) hmpos.ne']
  linarith only [h400,hlogm,hloglog]

/-- A potential budget and the nonterminal residual log bound control
the barrier sum for any positive exponent, including a dyadic one. -/
theorem barrier_budget_of_potential (I : Instance) (U F a : ℝ) (f : Fin I.m → ℝ)
    (hpot : potential I a F f ≤ 200*I.m*Real.log (I.m*U))
    (hreslog : -10*Real.log (I.m*U) ≤ Real.log (residual I F f)) :
    (∑ e, edgeBarrier I a e (f e)) ≤ ipmBarrierBound I U := by
  have hh := mul_le_mul_of_nonneg_left hreslog
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) (Nat.cast_nonneg I.m))
  unfold potential at hpot
  unfold ipmBarrierBound
  linarith only [hpot,hh]

private theorem slack_log_lower (p a B Q : ℝ) (hp : 0 < p) (ha : 0 < a)
    (hpower : Real.rpow p (-a) ≤ B) (hquot : Real.log B/a ≤ Q) :
    -Q ≤ Real.log p := by
  have hh := Real.log_le_log (Real.rpow_pos_of_pos hp (-a)) hpower
  rw [Real.log_rpow hp] at hh
  have hneg : -Real.log p ≤ Real.log B/a := by
    apply (le_div_iff₀ ha).mpr
    linarith only [hh]
  linarith only [hneg,hquot]

/-- Both slacks have the explicit lower bound
`exp(-110000 log²(mU))` for every exponent at least `alpha/10`.
This is derived from the potential, not assumed as a numerical oracle. -/
theorem slacks_exp_lower (I : Instance) (U F a : ℝ) (f : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (ha : alpha I U/10 ≤ a) (hf : StrictlyInside I f)
    (hpot : potential I a F f ≤ 200*I.m*Real.log (I.m*U))
    (hreslog : -10*Real.log (I.m*U) ≤ Real.log (residual I F f)) (e : Fin I.m) :
    Real.exp (-110000*(Real.log (I.m*U))^2) ≤ (I.edge e).upper-f e ∧
      Real.exp (-110000*(Real.log (I.m*U))^2) ≤ f e-(I.edge e).lower := by
  have halpha := alpha_pos I U hsize
  have hapos : 0 < a := (div_pos halpha (by norm_num)).trans_le ha
  have hlog := log_size_ge_half I U hsize
  have hB := ipmBarrierBound_ge_one I U hm hsize
  have hlogB := log_barrier_budget_le I U hm hU hsize
  have hinv : 1/a ≤ 10000*Real.log (I.m*U) := by
    calc
      1/a ≤ 1/(alpha I U/10) := one_div_le_one_div_of_le (div_pos halpha (by norm_num)) ha
      _ = _ := by unfold alpha; field_simp; ring
  have hprod := mul_le_mul hinv hlogB (Real.log_nonneg hB)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10000) (by linarith only [hlog]))
  have hquot : Real.log (ipmBarrierBound I U)/a ≤ 110000*(Real.log (I.m*U))^2 := by
    have heq : (1/a)*Real.log (ipmBarrierBound I U) = Real.log (ipmBarrierBound I U)/a := by ring
    rw [heq] at hprod
    nlinarith only [hprod]
  have hsum := barrier_budget_of_potential I U F a f hpot hreslog
  have hedge : edgeBarrier I a e (f e) ≤ ipmBarrierBound I U :=
    (Finset.single_le_sum (fun j _ => add_nonneg
      (Real.rpow_nonneg (sub_pos.mpr (hf j).2).le _)
      (Real.rpow_nonneg (sub_pos.mpr (hf j).1).le _)) (Finset.mem_univ e)).trans hsum
  have hupperNonneg : 0 ≤ Real.rpow (((I.edge e).upper : ℝ)-f e) (-a) :=
    (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).2) (-a)).le
  have hlowerNonneg : 0 ≤ Real.rpow (f e-(I.edge e).lower) (-a) :=
    (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).1) (-a)).le
  have hp : Real.rpow (((I.edge e).upper : ℝ)-f e) (-a) ≤ ipmBarrierBound I U := by
    unfold edgeBarrier at hedge
    linarith only [hedge,hlowerNonneg]
  have hq : Real.rpow (f e-(I.edge e).lower) (-a) ≤ ipmBarrierBound I U := by
    unfold edgeBarrier at hedge
    linarith only [hedge,hupperNonneg]
  have hlo := slack_log_lower _ a _ _ (sub_pos.mpr (hf e).2) hapos hp hquot
  have hhi := slack_log_lower _ a _ _ (sub_pos.mpr (hf e).1) hapos hq hquot
  constructor
  · simpa only [neg_mul] using (Real.exp_le_exp.mpr hlo).trans_eq (Real.exp_log (sub_pos.mpr (hf e).2))
  · simpa only [neg_mul] using (Real.exp_le_exp.mpr hhi).trans_eq (Real.exp_log (sub_pos.mpr (hf e).1))

end MinCostFlow.IPM.Machine
