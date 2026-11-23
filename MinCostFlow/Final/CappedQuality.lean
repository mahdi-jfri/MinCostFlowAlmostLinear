module

public import MinCostFlow.Final.ChainEdgeCap
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Selecting the quality of the capped structure

Compute quality on the actual size, then raise its exponent to the
fixed threshold exponent. Monotonicity identifies the result with
quality computed on the enlarged edge cap.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM IPM.Machine

/-- The integer quality exponent is monotone in the edge count. -/
theorem integerQualityExponent_mono (A : ℕ) : Monotone (integerQualityExponent A) := by
  intro M N h
  have hb := Nat.size_le_size (Nat.add_le_add_right (Nat.size_le_size h) 1)
  unfold integerQualityExponent
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hb)
    (Nat.pow_le_pow_right (by decide)
      (Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left 47 hb) 47)))

/-- The exponent returned to the bounded solver at its actual graph size. -/
def cappedQualityExponent (threshold A M : ℕ) : ℕ :=
  integerQualityExponent A (chainEdgeCap threshold M)

/-- The capped selector adds a single call, comparison, and return. -/
def cappedQualityCost (M : ℕ) : ℕ := integerQualityCost M + 20

/-- The constant embedded in the program is the exponent at the threshold. -/
def cappedQualityBody (quality A threshold : ℕ) : Stmt :=
  .call 1 quality [.reg 0] ;;
  .cond (.bin .lt (.reg 1) (.const (integerQualityExponent A threshold)))
    (.ret (.const (integerQualityExponent A threshold))) (.ret (.reg 1))

/-- The selector contains no random instructions. -/
theorem cappedQualityBody_noRand (quality A threshold : ℕ) :
    (cappedQualityBody quality A threshold).NoRand := by
  simp [cappedQualityBody, Stmt.NoRand]

/-- The selector uses the exact cap and preserves memory. The result
word's own fit condition guarantees that the embedded constant fits. -/
theorem cappedQuality_meetsContract {w entry quality threshold A : ℕ} {p : Program}
    (hBody : p.procs[entry]? = some (cappedQualityBody quality A threshold))
    (hQual : MeetsContract w p quality (solverQualityContract w
      (integerQualityExponent A) integerQualityCost)) :
    MeetsContract w p entry (solverQualityContract w
      (cappedQualityExponent threshold A) cappedQualityCost) := by
  apply meetsContract_of_runs hBody
  intro args mem pos tape hwords hpre
  obtain ⟨M,rfl,hfit⟩ := hpre
  let q := integerQualityExponent A M
  let c := integerQualityExponent A threshold
  have hmax : cappedQualityExponent threshold A M = max q c := by
    rcases le_total M threshold with h | h
    · rw [cappedQualityExponent, chainEdgeCap, max_eq_right h,
        max_eq_right (integerQualityExponent_mono A h)]
    · rw [cappedQualityExponent, chainEdgeCap, max_eq_left h,
        max_eq_left (integerQualityExponent_mono A h)]
  rw [hmax] at hfit
  have hq : q < 2^w := (le_max_left q c).trans_lt hfit
  have hc : c < 2^w := (le_max_right q c).trans_lt hfit
  have hbase : 1 < c := by
    have hb : 0 < (threshold.size+1).size := Nat.size_pos.mpr (by omega)
    have hp : 0 < 2^((47*(threshold.size+1).size+47)/48) := by positivity
    unfold c integerQualityExponent
    have h := Nat.le_mul_of_pos_right (128*(A+1)) hb
    exact (show 1<128*(A+1) by omega).trans_le (h.trans (Nat.le_mul_of_pos_right _ hp))
  have hOne : 1 < 2^w := hbase.trans hc
  apply runs_start_le
  unfold cappedQualityBody
  refine runs_seq_call_le hQual (vs := [M]) rfl hwords ⟨M,rfl,hq⟩ ?_
  intro value mem' pos' hpost
  change mem'=mem ∧ value=q at hpost
  obtain ⟨rfl,rfl⟩ := hpost
  wram_step
  · have h : q<c := by simpa using hcond
    refine runs_ret_le (v:=c) (by eval_expr) ?_ ?_
    · exact ⟨rfl, (hmax.trans (max_eq_right h.le)).symm⟩
    · simp [solverQualityContract,cappedQualityCost,Expr.size_bin,Expr.size_reg,Expr.size_const,
        argsSize_cons,argsSize_nil]
      omega
  · have h : c≤q := Nat.le_of_not_gt (by simpa using hcond)
    refine runs_ret_le (v:=q) (by eval_expr) ?_ ?_
    · exact ⟨rfl, (hmax.trans (max_eq_left h)).symm⟩
    · simp [solverQualityContract,cappedQualityCost,Expr.size_bin,Expr.size_reg,Expr.size_const,
        argsSize_cons,argsSize_nil]
      omega

/-- The fixed threshold changes only the coefficient of the linear
reciprocal-quality envelope used for scratch. -/
theorem cappedQuality_linear (threshold A : ℕ) :
    ∃ C : ℕ, ∀ M, 2^cappedQualityExponent threshold A M ≤ C*(M+2) := by
  obtain ⟨C,hC⟩ := integerQualityExponent_linear A
  refine ⟨C*(threshold+1),fun M => ?_⟩
  have hsize : chainEdgeCap threshold M + 2 ≤ (threshold+1)*(M+2) := by
    exact_mod_cast chainEdgeCap_add_two_le threshold M
  exact (hC _).trans ((Nat.mul_le_mul_left C hsize).trans_eq (Nat.mul_assoc _ _ _).symm)

/-- The selected quality retains a subpolynomial bound in the actual size. -/
theorem cappedQuality_subpolynomial (threshold A M : ℕ) :
    (2:ℝ)^cappedQualityExponent threshold A M ≤
      Chain.alg2TimeFactor (65536*((A:ℝ)+1)*(logScale ((threshold:ℝ)+1))^(47/48:ℝ)*
        logScale (logScale ((threshold:ℝ)+1))) (47/48) M := by
  refine (integerQualityExponent_bounds A _).2.trans ?_
  exact scalingTimeFactor_rescale (by linarith [Nat.cast_nonneg (α:=ℝ) threshold])
    (by positivity) M (chainEdgeCap threshold M) (chainEdgeCap_add_two_le threshold M)

/-- The selector's extra fixed cost is absorbed by a linear allowance. -/
theorem cappedQualityCost_le (M : ℕ) : cappedQualityCost M ≤ 120*(M+1) := by
  have h := integerQualityCost_le M
  unfold cappedQualityCost
  omega

end MinCostFlow.Final
