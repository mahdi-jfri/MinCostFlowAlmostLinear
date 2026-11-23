module

public import MinCostFlow.MinRatio.PathPayload
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Rat.Floor
public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Exact detection thresholds for fixed-point path accounts

The proof of Theorem 5.1 (pages 29–30) tests whether accumulated absolute
flow minus `epsilon / length` is nonnegative. Accumulated flow has an
integer numerator at precision `P`. It therefore suffices to subtract the
integer ceiling of `epsilon * 2^P / length`. This is an exact reformulation
of the test, without rounding the stored flow or approximating the answer.
A coefficient refresh adjusts this threshold while keeping the account.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

/-- The least integer numerator that triggers Detect at one edge. -/
noncomputable def detectorThreshold (P : ℕ) (epsilon length : ℝ) : ℤ :=
  ⌈epsilon * (2 : ℝ) ^ P / length⌉

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

/-- The integer residual implements the exact condition of Section 6. -/
theorem detectorThreshold_test (P : ℕ) (epsilon length : ℝ) (account : ℤ)
    (hLength : 0 < length) :
    epsilon ≤ length * ((account : ℝ) / (2 : ℝ) ^ P) ↔
      0 ≤ account - detectorThreshold P epsilon length := by
  have hScale : 0 < (2 : ℝ) ^ P := pow_pos (zero_lt_two : (0 : ℝ) < 2) P
  rw [sub_nonneg, detectorThreshold, Int.ceil_le, div_le_iff₀ hLength,
    ← mul_div_assoc, le_div_iff₀ hScale, mul_comm (account : ℝ) length]

/-- A positive threshold starts strictly below the reporting boundary. -/
theorem detectorThreshold_pos (P : ℕ) (epsilon length : ℝ)
    (hEpsilon : 0 < epsilon) (hLength : 0 < length) :
    0 < detectorThreshold P epsilon length := by
  apply Int.ceil_pos.mpr
  exact div_pos (mul_pos hEpsilon (pow_pos (zero_lt_two : (0 : ℝ) < 2) P)) hLength

/-- Ceiling the scaled threshold costs less than one unit at its
fixed-point precision. -/
theorem detectorThreshold_scaled_lt (P : ℕ) (epsilon length : ℝ) :
    (detectorThreshold P epsilon length : ℝ) / (2 : ℝ)^P <
      epsilon / length + 1 / (2 : ℝ)^P := by
  have hp : 0 < (2 : ℝ)^P := pow_pos zero_lt_two _
  unfold detectorThreshold
  apply (div_lt_iff₀ hp).2
  rw [add_mul, div_mul_cancel₀ _ hp.ne', div_mul_eq_mul_div]
  exact Int.ceil_lt_add_one _

/-- After reporting and resetting all ready edges, the residual
magnitude is bounded by the threshold. -/
theorem detectorThreshold_residual_after_detect (P : ℕ) (epsilon length : ℝ)
    (account : ℤ) (he : 0 < epsilon) (hl : 0 < length) (ha : 0 ≤ account) :
    let threshold := detectorThreshold P epsilon length
    let next := if threshold ≤ account then 0 else account
    |next - threshold| ≤ threshold := by
  dsimp only
  have hpos := detectorThreshold_pos P epsilon length he hl
  split <;> apply abs_le.mpr <;> omega

/-- After Detect, a length refresh keeps the account and changes the
threshold. Its residual is bounded by the larger of the two thresholds. -/
theorem detectorThreshold_residual_after_refresh (P : ℕ) (epsilon oldLength newLength : ℝ)
    (account : ℤ) (he : 0 < epsilon) (ho : 0 < oldLength) (hn : 0 < newLength)
    (ha : 0 ≤ account) :
    let oldThreshold := detectorThreshold P epsilon oldLength
    let newThreshold := detectorThreshold P epsilon newLength
    let next := if oldThreshold ≤ account then 0 else account
    |next - newThreshold| ≤ max oldThreshold newThreshold := by
  dsimp only
  have ho' := detectorThreshold_pos P epsilon oldLength he ho
  have hn' := detectorThreshold_pos P epsilon newLength he hn
  have hlo := le_max_left (detectorThreshold P epsilon oldLength)
    (detectorThreshold P epsilon newLength)
  have hhi := le_max_right (detectorThreshold P epsilon oldLength)
    (detectorThreshold P epsilon newLength)
  split <;> apply abs_le.mpr <;> omega

/-- The input epsilon and length bounds give a common decoded bound
for the integer threshold. -/
theorem detectorThreshold_scaled_bound (P E : ℕ) (epsilon length : ℝ)
    (he : epsilon ≤ (2 : ℝ)^E) (hl : 1 / (2 : ℝ)^E ≤ length) :
    (detectorThreshold P epsilon length : ℝ) / (2 : ℝ)^P ≤ (2 : ℝ)^(2 * E + 1) := by
  have hp : 0 < (2 : ℝ)^E := pow_pos zero_lt_two _
  have hlen : 0 < length := (one_div_pos.mpr hp).trans_le hl
  have hpow : (1 : ℝ) ≤ 2^P := one_le_pow₀ one_le_two
  have hone : 1 / (2 : ℝ)^P ≤ 1 := (div_le_iff₀ (zero_lt_one.trans_le hpow)).2 (by simpa)
  have hq : epsilon / length ≤ (2 : ℝ)^(2 * E) := by
    apply (div_le_iff₀ hlen).2
    calc
      epsilon ≤ (2 : ℝ)^E := he
      _ = (2 : ℝ)^(2 * E) * (1 / (2 : ℝ)^E) := by
        rw [two_mul, pow_add, mul_assoc, mul_one_div_cancel hp.ne', mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (pow_nonneg zero_le_two _)
  have hbase : (1 : ℝ) ≤ 2^(2 * E) := one_le_pow₀ one_le_two
  calc
    _ ≤ epsilon / length + 1 / (2 : ℝ)^P := (detectorThreshold_scaled_lt _ _ _).le
    _ ≤ (2 : ℝ)^(2 * E) + (2 : ℝ)^(2 * E) := add_le_add hq (hone.trans hbase)
    _ = _ := by rw [pow_succ, mul_two]

/-- The negative threshold written by initialization and Detect
fits the signed limb block under the input magnitude bounds. -/
theorem detectorThreshold_reset_fits {h L P E : ℕ} (epsilon length : ℝ)
    (he : 0 < epsilon) (heU : epsilon ≤ (2 : ℝ)^E)
    (hl : 1 / (2 : ℝ)^E ≤ length) (hw : P + 2 * E + 3 ≤ h * L) :
    Num.Fits h L (-detectorThreshold P epsilon length) := by
  have hp : 0 < (2 : ℝ)^P := pow_pos zero_lt_two _
  have hlen : 0 < length := (one_div_pos.mpr (pow_pos zero_lt_two _)).trans_le hl
  have ht : (0 : ℝ) ≤ (detectorThreshold P epsilon length : ℝ) :=
    by exact_mod_cast (detectorThreshold_pos P epsilon length he hlen).le
  refine Num.IPM.fits_of_scaled_bound (P := P) (E := 2 * E + 1) (by omega) ?_
  rw [Int.cast_neg, neg_div, abs_neg, abs_of_nonneg (div_nonneg ht hp.le)]
  exact detectorThreshold_scaled_bound P E epsilon length heU hl

/-- Detect followed by a length refresh leaves a residual within the
decoded threshold budget for either length. -/
theorem detectorThreshold_refresh_scaled_bound (P E : ℕ) (epsilon oldLength newLength : ℝ)
    (account : ℤ) (he : 0 < epsilon) (heU : epsilon ≤ (2 : ℝ)^E)
    (ho : 1 / (2 : ℝ)^E ≤ oldLength) (hn : 1 / (2 : ℝ)^E ≤ newLength) (ha : 0 ≤ account) :
    let next := if detectorThreshold P epsilon oldLength ≤ account then 0 else account
    |((next - detectorThreshold P epsilon newLength : ℤ) : ℝ) / (2 : ℝ)^P| ≤
      (2 : ℝ)^(2 * E + 1) := by
  dsimp only
  have hmin : 0 < 1 / (2 : ℝ)^E := one_div_pos.mpr (pow_pos zero_lt_two _)
  have hp : 0 < (2 : ℝ)^P := pow_pos zero_lt_two _
  have hres := detectorThreshold_residual_after_refresh P epsilon oldLength newLength account
    he (hmin.trans_le ho) (hmin.trans_le hn) ha
  rw [abs_div, abs_of_pos hp, ← Int.cast_abs]
  refine (div_le_div_of_nonneg_right (Int.cast_le.mpr hres) hp.le).trans ?_
  rw [Int.cast_max, ← max_div_div_right hp.le]
  exact max_le (detectorThreshold_scaled_bound P E epsilon oldLength heU ho)
    (detectorThreshold_scaled_bound P E epsilon newLength heU hn)

/-- Between Detect calls the account is a sum of absolute
increments. After a length refresh, the magnitude of the residual is
bounded by the larger of the new threshold and the total account. -/
theorem detectorThreshold_residual_between_reports (P : ℕ) (epsilon length : ℝ)
    (account : ℤ) (changes : List ℤ) (he : 0 < epsilon) (hl : 0 < length) (ha : 0 ≤ account) :
    let threshold := detectorThreshold P epsilon length
    |account + (changes.map abs).sum - threshold| ≤ max threshold (account + (changes.map abs).sum) := by
  dsimp only
  have ht := detectorThreshold_pos P epsilon length he hl
  have hs : 0 ≤ (changes.map abs).sum := by
    induction changes with
    | nil => simp
    | cons change rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (abs_nonneg _) ih
  have hlo := le_max_left (detectorThreshold P epsilon length) (account + (changes.map abs).sum)
  have hhi := le_max_right (detectorThreshold P epsilon length) (account + (changes.map abs).sum)
  apply abs_le.mpr
  omega

/-- A bound on each routed numerator gives an explicit residual
budget in the number of updates since the last report. -/
theorem detectorThreshold_residual_le_of_count (P : ℕ) (epsilon length : ℝ)
    (account limit : ℤ) (changes : List ℤ) (he : 0 < epsilon) (hl : 0 < length)
    (ha : 0 ≤ account) (hc : ∀ change ∈ changes, |change| ≤ limit) :
    |account + (changes.map abs).sum - detectorThreshold P epsilon length| ≤
      max (detectorThreshold P epsilon length) (account + (changes.length : ℤ) * limit) := by
  have hs : (changes.map abs).sum ≤ (changes.length : ℤ) * limit := by
    induction changes with
    | nil => simp
    | cons head rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
        add_mul, one_mul]
      exact (add_le_add (hc head (by simp)) (ih fun change hm => hc change (List.mem_cons_of_mem _ hm))).trans_eq
        (add_comm _ _)
  exact (detectorThreshold_residual_between_reports P epsilon length account changes he hl ha).trans
    (max_le_max le_rfl (add_le_add_right hs account))

/-- Updating the residual by the absolute numerator tracks one flow change. -/
theorem detectorThreshold_add_flow (P : ℕ) (epsilon length : ℝ) (account delta : ℤ) :
    (account - detectorThreshold P epsilon length) + (PathTag.ofFlow delta).detector =
      (account + |delta|) - detectorThreshold P epsilon length := by
  simp only [PathTag.ofFlow]
  omega

/-- A length refresh changes only the threshold, preserving the accumulated
absolute flow since the last report. -/
theorem detectorThreshold_refresh (P : ℕ) (epsilon oldLength newLength : ℝ) (account : ℤ) :
    (account - detectorThreshold P epsilon oldLength) +
        (detectorThreshold P epsilon oldLength - detectorThreshold P epsilon newLength) =
      account - detectorThreshold P epsilon newLength := by
  omega

/-- Resetting the integer account to zero restores the initial residual. -/
theorem detectorThreshold_reset (P : ℕ) (epsilon length : ℝ) :
    (0 : ℤ) - detectorThreshold P epsilon length = -detectorThreshold P epsilon length :=
  zero_sub _

/-- For dyadic input coefficients, the threshold is a signed integer
ceiling division. This formula is the target of the numeric division
procedure, rather than an approximation to the real threshold. -/
theorem detectorThreshold_dyadic (P : ℕ) (epsilon : ℤ) (length : ℕ) (hLength : 0 < length) :
    detectorThreshold P ((epsilon : ℝ) / (2 : ℝ) ^ P)
        ((length : ℝ) / (2 : ℝ) ^ P) =
      -((-(epsilon * (2 ^ P : ℕ))) / (length : ℤ)) := by
  have hScale : (2 : ℝ) ^ P ≠ 0 := ne_of_gt (pow_pos (zero_lt_two : (0 : ℝ) < 2) P)
  have hLength' : (length : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hLength)
  have heq : ((epsilon : ℝ) / (2 : ℝ) ^ P) * (2 : ℝ) ^ P /
      ((length : ℝ) / (2 : ℝ) ^ P) = (epsilon : ℝ) * (2 : ℝ) ^ P / length := by
    field_simp
  unfold detectorThreshold
  rw [heq]
  have hreal : ((((epsilon * (2 ^ P : ℕ) : ℤ) : ℚ) / (length : ℚ) : ℚ) : ℝ) =
      (epsilon : ℝ) * (2 : ℝ) ^ P / length := by
    push_cast
    rfl
  rw [← hreal, Rat.ceil_cast]
  exact Rat.ceil_intCast_div_natCast _ _

end MinCostFlow.MinRatio
