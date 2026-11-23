module

public import MinCostFlow.IPM.Machine.MinRatioContract
import MinCostFlow.MinRatio.PathNormalizationRange
import MinCostFlow.Num.IPM.DivideFacts
import Mathlib.Tactic.Ring

/-!
# Bounds for the routed increment and the next flow

Algorithm 2 (page 29) routes a multiple of the chosen circulation.
The ratio test bounds each normalized coordinate using the length of
that edge. This bound and the old flow range give room for the next
coordinate in the IPM's fixed-point format.
-/

public section

namespace MinCostFlow.MinRatio

open IPM.Machine

/-- The ratio test bounds every normalized coordinate by the actual
step size divided by the ratio cutoff and the minimum length. -/
theorem pathIncrement_le (G : MGraph) (g length C : ℕ → ℝ)
    {r lower actual : ℝ} (hr : 0 < r) (hlower : 0 < lower)
    (hl : ∀ e ∈ G.E, lower ≤ length e) (ha : 0 ≤ actual)
    (hint : ∀ e ∈ G.E, ∃ z : ℤ, C e = (z : ℝ))
    (hgood : G.inner g C / G.lnorm length C ≤ -r)
    {e : ℕ} (he : e ∈ G.E) :
    |-(actual / G.inner g C) * C e| ≤ actual / (r * lower) := by
  let i := G.inner g C
  let n := G.lnorm length C
  have hm : r * lower ≤ -i := pathFlow_inner_magnitude G g length C hr hlower hl hint hgood
  have hmul : 0 < r * lower := mul_pos hr hlower
  have hi : 0 < -i := hmul.trans_le hm
  have hn0 : 0 ≤ n := Finset.sum_nonneg fun f hf =>
    mul_nonneg (hlower.le.trans (hl f hf)) (abs_nonneg _)
  have hn : 0 < n := by
    refine lt_of_le_of_ne hn0 ?_
    intro hn
    change i / n ≤ -r at hgood
    rw [← hn, div_zero] at hgood
    exact (not_le_of_gt (neg_lt_zero.mpr hr)) hgood
  have hratio : r * n ≤ -i := by
    have h := (div_le_iff₀ hn).mp hgood
    rw [neg_mul, le_neg] at h
    exact h
  have heLen : lower * |C e| ≤ n :=
    (mul_le_mul_of_nonneg_right (hl e he) (abs_nonneg _)).trans
      (Finset.single_le_sum
        (fun f hf => mul_nonneg (hlower.le.trans (hl f hf)) (abs_nonneg _)) he)
  have hcoord : r * lower * |C e| ≤ -i := by
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left heLen hr.le).trans hratio
  have hnormalized : |C e| / (-i) ≤ 1 / (r * lower) := by
    apply (div_le_div_iff₀ hi hmul).mpr
    simpa only [one_mul, mul_comm |C e| (r * lower)] using hcoord
  change |-(actual / i) * C e| ≤ _
  rw [abs_mul, abs_neg, abs_div, abs_of_nonneg ha,
    abs_of_neg (neg_pos.mp hi)]
  calc
    actual / (-i) * |C e| = actual * (|C e| / (-i)) := by rw [div_mul_eq_mul_div, mul_div_assoc, mul_comm]
    _ ≤ actual * (1 / (r * lower)) := mul_le_mul_of_nonneg_left hnormalized ha
    _ = actual / (r * lower) := by rw [mul_one_div]

/-- The IPM bounds on the request, lengths, and ratio give the
`2^(3E+1)` bound for a normalization within the caller's tolerance. -/
theorem pathIncrement_dyadic_le (G : MGraph) (g length C : ℕ → ℝ)
    (E : ℕ) {r requested actual : ℝ}
    (hr : 1 / (2 : ℝ) ^ E ≤ r)
    (hl : ∀ e ∈ G.E, 1 / (2 : ℝ) ^ E ≤ length e)
    (hreq0 : 0 ≤ requested) (hreq : requested ≤ (2 : ℝ) ^ E)
    (hnorm : NormalizationWithin requested actual)
    (hint : ∀ e ∈ G.E, ∃ z : ℤ, C e = (z : ℝ))
    (hgood : G.inner g C / G.lnorm length C ≤ -r)
    {e : ℕ} (he : e ∈ G.E) :
    |-(actual / G.inner g C) * C e| ≤ (2 : ℝ) ^ (3 * E + 1) := by
  have hp : 0 < 1 / (2 : ℝ) ^ E := one_div_pos.mpr (pow_pos (by norm_num) _)
  have ha : 0 ≤ actual := (div_nonneg hreq0 (by norm_num)).trans hnorm.1
  have haBound : |actual| ≤ (2 : ℝ) ^ (E + 1) := by
    rw [abs_of_nonneg ha, pow_succ' (2 : ℝ) E]
    exact hnorm.2.trans (mul_le_mul_of_nonneg_left hreq (by norm_num))
  have hlower : 1 / (2 : ℝ) ^ (2 * E) ≤ r * (1 / (2 : ℝ) ^ E) := calc
    _ = (1 / (2 : ℝ) ^ E) * (1 / (2 : ℝ) ^ E) := by
      rw [div_mul_div_comm, one_mul, two_mul, pow_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right hr hp.le
  have hquot := Num.IPM.quotient_bound haBound hlower
  rw [abs_of_nonneg (div_nonneg ha (mul_nonneg (hp.le.trans hr) hp.le))] at hquot
  have hexp : E + 1 + 2 * E = 3 * E + 1 := by omega
  rw [hexp] at hquot
  exact (pathIncrement_le G g length C (hp.trans_le hr) hp hl ha hint hgood he).trans hquot

/-- A dyadic change of magnitude at most `2^(3E+1)` can be added to
an old flow of magnitude at most `2^E` in the IPM's flow format. -/
theorem pathIncrement_flow_fits {w : ℕ} (F : MinRatioFormat w) (old change : ℤ)
    (hold : |(old : ℝ) / (2 : ℝ) ^ F.fmt.precision| ≤ (2 : ℝ) ^ F.rangeExponent)
    (hchange : |(change : ℝ) / (2 : ℝ) ^ F.fmt.precision| ≤ (2 : ℝ) ^ (3 * F.rangeExponent + 1)) :
    Num.Fits F.fmt.limbBits F.limbs (old + change) := by
  let E := F.rangeExponent
  have hw := F.width
  apply Num.IPM.fits_of_scaled_bound (P := F.fmt.precision) (E := 3 * E + 2)
  · dsimp only [E]
    omega
  · rw [Int.cast_add, add_div]
    have hone : (2 : ℝ) ^ E ≤ (2 : ℝ) ^ (3 * E + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ (2 : ℝ) ^ (3 * E + 1) + (2 : ℝ) ^ (3 * E + 1) := add_le_add (hold.trans hone) hchange
      _ = (2 : ℝ) ^ (3 * E + 2) := by rw [pow_succ (2 : ℝ) (3 * E + 1)]; ring

end MinCostFlow.MinRatio
