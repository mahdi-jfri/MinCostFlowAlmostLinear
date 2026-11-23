module

public import MinCostFlow.IPM.Machine.IterationBudget
public import MinCostFlow.IPM.Machine.EpochProgressBound
import MinCostFlow.IPM.Machine.EpochGuardRanges
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The finite number of full epochs in a target test

Theorem 4.3 of Chen et al., arXiv:2203.00671v2 (page 25), counts
decreases in the potential. Here each continuing machine epoch has
exactly one step per edge, and the count uses the dyadic parameter.
The maximum number of complete epochs is the integer step budget
with the edge-count factor removed.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- The epoch limit has the same integer formula as the implemented
step budget, with one edge in that formula. Every epoch spends
exactly the actual edge count in steps. -/
def dyadicEpochLimit (bits k j : ℕ) : ℕ :=
  dyadicIterationBudget 1 bits k j

/-- Multiplying the epoch limit by the number of edges gives exactly
the integer step budget. -/
theorem dyadicEpochLimit_mul (m bits k j : ℕ) :
    m*dyadicEpochLimit bits k j=dyadicIterationBudget m bits k j := by
  unfold dyadicEpochLimit dyadicIterationBudget
  ring

/-- If the last residual stays above a quarter, the potential cannot
drop by the entire rounded epoch budget. This is the termination
argument of Theorem 4.3 at the machine's stopping tolerance. -/
theorem target_epoch_budget_exhausted (I : Instance) (U k j : ℕ) (target a : ℝ)
    (initial last : Fin I.m → ℝ)
    (hm : 0<I.m) (hsize : 2≤I.m*U) (hf : StrictlyInside I last) (hr : 1/4<residual I target last)
    (hpot : potential I a target initial≤200*I.m*Real.log (I.m*(U:ℝ)))
    (hdrop : potential I a target last≤potential I a target initial-
      (I.m:ℝ)*(dyadicEpochLimit (I.m.size+U.size) k j:ℝ)*(1/(2:ℝ)^(k+j+5))^2/2000) :
    False := by
  have hsizeR : 2≤(I.m:ℝ)*U := by exact_mod_cast hsize
  have hlog := epoch_residual_log_lower (I.m*(U:ℝ)) (residual I target last)
    hsizeR (by linarith only [hr])
  have hmlog := mul_le_mul_of_nonneg_left hlog
    (show 0≤20*(I.m:ℝ) by positivity)
  have hb : 0< ∑ e,edgeBarrier I a e (last e) := by
    let : Nonempty (Fin I.m) := ⟨⟨0,hm⟩⟩
    exact Finset.sum_pos (fun e _ =>
      add_pos (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).2) _)
        (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).1) _)) Finset.univ_nonempty
  have hscaled := dyadicIterationBudget_scaled I.m (I.m.size+U.size) k j
  rw [← dyadicEpochLimit_mul,Nat.cast_mul] at hscaled
  push_cast at hscaled
  have hlogUpper := (Num.IPM.alpha_bit_length_bounds hsize).1
  push_cast at hlogUpper
  have hmR : (0:ℝ)<I.m := Nat.cast_pos.mpr hm
  have hlogM := mul_le_mul_of_nonneg_left hlogUpper hmR.le
  unfold potential at hdrop hpot
  linarith only [hdrop,hpot,hmlog,hb,hscaled,hlogM]

end MinCostFlow.IPM.Machine
