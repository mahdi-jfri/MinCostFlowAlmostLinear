module

public import MinCostFlow.MinRatio.PathNormalizationProgram
import MinCostFlow.Num.IPM.DivideFacts

/-!
# Lower bounds for the normalizing divisor

In Algorithm 2 (page 29), a successful circulation passes the ratio
test before it is normalized. Its integer edge coefficients and the
lower bound on edge lengths give a lower bound for the magnitude of
the gradient sum. This controls the size of the fixed-point quotient.
-/

public section

namespace MinCostFlow.MinRatio

/-- A successful integral circulation has negative gradient sum.
Its magnitude is at least the ratio threshold times the minimum length. -/
theorem pathFlow_inner_magnitude (G : MGraph) (g length C : ℕ → ℝ)
    {r lower : ℝ} (hr : 0 < r) (hlower : 0 < lower)
    (hl : ∀ e ∈ G.E, lower ≤ length e)
    (hint : ∀ e ∈ G.E, ∃ z : ℤ, C e = (z : ℝ))
    (hgood : G.inner g C / G.lnorm length C ≤ -r) :
    r * lower ≤ -G.inner g C := by
  have hnonzero : ∃ e ∈ G.E, C e ≠ 0 := by
    by_contra! hn
    have hz : G.lnorm length C = 0 := by
      unfold MGraph.lnorm
      exact Finset.sum_eq_zero fun e he => by rw [hn e he, abs_zero, mul_zero]
    rw [hz, div_zero] at hgood
    exact (not_le_of_gt (neg_lt_zero.mpr hr)) hgood
  obtain ⟨e, he, hne⟩ := hnonzero
  obtain ⟨z, hz⟩ := hint e he
  have hzne : z ≠ 0 := fun h => hne (by simp [hz, h])
  have hzabs : 1 ≤ |C e| := by
    rw [hz, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hzne
  have hnonneg (a : ℕ) (ha : a ∈ G.E) : 0 ≤ length a * |C a| :=
    mul_nonneg (hlower.le.trans (hl a ha)) (abs_nonneg _)
  have hlen : lower ≤ G.lnorm length C := calc
    lower = lower * 1 := (mul_one _).symm
    _ ≤ length e * |C e| := mul_le_mul (hl e he) hzabs (by norm_num) (hlower.le.trans (hl e he))
    _ ≤ G.lnorm length C := Finset.single_le_sum hnonneg he
  have hp : 0 < G.lnorm length C := hlower.trans_le hlen
  have hmul := (div_le_iff₀ hp).mp hgood
  rw [neg_mul, le_neg] at hmul
  exact (mul_le_mul_of_nonneg_left hlen hr.le).trans hmul

/-- At the IPM scale, the ratio and length bounds give a lower bound
of `2^(-2E)` on the positive normalizing divisor. -/
theorem pathFlow_inner_dyadic_lower (G : MGraph) (g length C : ℕ → ℝ)
    {r : ℝ} (E : ℕ) (hr : 1 / (2 : ℝ) ^ E ≤ r)
    (hl : ∀ e ∈ G.E, 1 / (2 : ℝ) ^ E ≤ length e)
    (hint : ∀ e ∈ G.E, ∃ z : ℤ, C e = (z : ℝ))
    (hgood : G.inner g C / G.lnorm length C ≤ -r) :
    1 / (2 : ℝ) ^ (2 * E) ≤ -G.inner g C := by
  have hp : 0 < 1 / (2 : ℝ) ^ E := one_div_pos.mpr (pow_pos (by norm_num) _)
  have hlower := pathFlow_inner_magnitude G g length C (hp.trans_le hr) hp hl hint hgood
  calc
    _ = (1 / (2 : ℝ) ^ E) * (1 / (2 : ℝ) ^ E) := by
      rw [div_mul_div_comm, one_mul, two_mul, pow_add]
    _ ≤ _ := (mul_le_mul_of_nonneg_right hr hp.le).trans hlower

/-- The IPM width margin accommodates the floor quotient when the
actual gradient sum satisfies the scale bound from the ratio test. -/
theorem pathMultiplier_fits {w : ℕ} (F : IPM.Machine.MinRatioFormat w)
    (request magnitude : ℤ)
    (hreq : |(request : ℝ) / (2 : ℝ) ^ F.fmt.precision| ≤ (2 : ℝ) ^ F.rangeExponent)
    (hmag : 1 / (2 : ℝ) ^ (2 * F.rangeExponent) ≤ (magnitude : ℝ) / (2 : ℝ) ^ F.fmt.precision) :
    Num.Fits F.fmt.limbBits F.limbs (pathMultiplier F.fmt.precision request magnitude) := by
  have hq := Num.IPM.quotient_bound hreq hmag
  have hwidth := F.width
  have h := Num.IPM.floor_scaled_fits (P := F.fmt.precision) (h := F.fmt.limbBits)
    (L := F.limbs) hq (by omega)
  convert h using 1
  unfold pathMultiplier
  rw [Num.floorDiv_eq_floor]
  congr 1
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  field_simp

end MinCostFlow.MinRatio
