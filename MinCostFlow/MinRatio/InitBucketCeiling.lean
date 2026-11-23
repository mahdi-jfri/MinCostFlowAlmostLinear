module

public import MinCostFlow.Chain.ConcreteDefs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact bucket ceilings

Characterize the scaled interval accepted by the bucket ceiling test and
show why a symmetric error bound alone does not handle integer ties.
-/

public section
namespace MinCostFlow.MinRatio
open Chain SparseCore

/-- The machine accepts exactly when the scaled enclosure lies inside a
single positive ceiling interval. -/
theorem initBucketCeiling_passes_iff {lo hi scale : ℕ} (hs : 0 < scale) (hh : 0 < hi) :
    (hi - 1) / scale * scale < lo ↔
      ∃ k : ℕ, 0 < k ∧ (k - 1) * scale < lo ∧ hi ≤ k * scale := by
  constructor
  · intro h
    let q := (hi - 1) / scale
    have hu : hi - 1 < (q + 1) * scale :=
      (Nat.div_lt_iff_lt_mul hs).mp (Nat.lt_succ_self q)
    exact ⟨q + 1, Nat.succ_pos _, by simpa only [Nat.add_sub_cancel] using h, by omega⟩
  · rintro ⟨k, hk, hlo, hhi⟩
    have hq : (hi - 1) / scale < k :=
      (Nat.div_lt_iff_lt_mul hs).mpr (by omega)
    exact (Nat.mul_le_mul_right scale (show (hi - 1) / scale ≤ k - 1 by omega)).trans_lt hlo

/-- For an enclosure of the target value, the only interval that can
pass is the one ending at its true ceiling. -/
theorem initBucketCeiling_passes_iff_exact {value : ℝ} {lo hi scale : ℕ}
    (hs : 0 < scale) (hh : 0 < hi)
    (hlo : (lo : ℝ) / scale ≤ value) (hhi : value ≤ (hi : ℝ) / scale) :
    (hi - 1) / scale * scale < lo ↔
      0 < ⌈value⌉₊ ∧ (⌈value⌉₊ - 1) * scale < lo ∧ hi ≤ ⌈value⌉₊ * scale := by
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hs
  constructor
  · intro h
    obtain ⟨k, hk, hl, hu⟩ := (initBucketCeiling_passes_iff hs hh).mp h
    have hl' : ((k - 1 : ℕ) : ℝ) < value := hlo.trans_lt' ((lt_div_iff₀ hs').mpr (by exact_mod_cast hl))
    have hu' : value ≤ (k : ℝ) := hhi.trans ((div_le_iff₀ hs').mpr (by exact_mod_cast hu))
    have hceil : ⌈value⌉₊ = k := by
      apply le_antisymm (Nat.ceil_le.mpr hu')
      have hlow := Nat.lt_ceil.mpr hl'
      omega
    exact hceil.symm ▸ ⟨hk, hl, hu⟩
  · intro h
    exact (initBucketCeiling_passes_iff hs hh).mpr ⟨⌈value⌉₊, h⟩

/-- An enclosure contained in the positive ceiling interval triggers the
integer bucket test. The lower endpoint must be strictly above the
previous integer and the upper endpoint may equal the ceiling. -/
theorem initBucketCeiling_passes_of_error
    {value error : ℝ} {ceil lo hi scale : ℕ} (hc : 0 < ceil) (hs : 0 < scale)
    (hlo : value - error ≤ (lo : ℝ) / scale)
    (hhi : (hi : ℝ) / scale ≤ value + error)
    (hprev : ((ceil - 1 : ℕ) : ℝ) + error < value)
    (hnext : value + error ≤ (ceil : ℝ)) :
    (hi - 1) / scale * scale < lo := by
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hs
  have hbelow : ((ceil - 1 : ℕ) : ℝ) < (lo : ℝ) / scale := by
    linarith only [hprev, hlo]
  have hcut : (ceil - 1) * scale < lo := by
    exact_mod_cast (lt_div_iff₀ hs').mp hbelow
  have hhi' : hi ≤ ceil * scale := by
    exact_mod_cast (div_le_iff₀ hs').mp (hhi.trans hnext)
  by_cases hhiPos : 0 < hi
  · exact (initBucketCeiling_passes_iff hs hhiPos).mpr ⟨ceil, hc, hcut, hhi'⟩
  · have hz : hi = 0 := Nat.eq_zero_of_not_pos hhiPos
    simpa only [hz, Nat.zero_sub, Nat.zero_div, Nat.zero_mul] using
      (Nat.zero_le _).trans_lt hcut

/-- An enclosure crossing an integer cannot certify the bucket ceiling,
regardless of how narrow it is. -/
theorem initBucketCeiling_fails_of_straddle {k lo hi scale : ℕ} (hs : 0 < scale)
    (hlo : lo ≤ k * scale) (hhi : k * scale < hi) :
    ¬ (hi - 1) / scale * scale < lo := by
  have hk : k ≤ (hi - 1) / scale :=
    (Nat.le_div_iff_mul_le hs).mpr (by omega)
  exact not_lt_of_ge (hlo.trans (Nat.mul_le_mul_right scale hk))

/-- Every positive error tolerance permits an enclosure of an integer
that fails the bucket ceiling test. -/
theorem initBucketCeiling_exists_failing_enclosure (k : ℕ) {error : ℝ} (he : 0 < error) :
    ∃ lo hi scale : ℕ, 0 < scale ∧
      (k : ℝ) - error ≤ (lo : ℝ) / scale ∧ (lo : ℝ) / scale ≤ k ∧
      (k : ℝ) ≤ (hi : ℝ) / scale ∧ (hi : ℝ) / scale ≤ (k : ℝ) + error ∧
      ¬ (hi - 1) / scale * scale < lo := by
  obtain ⟨scale, hscale⟩ := exists_nat_gt (1 / error)
  have hsR : (0 : ℝ) < scale := (by positivity : 0 < 1 / error).trans hscale
  have hs : 0 < scale := by exact_mod_cast hsR
  have hwidth : 1 / (scale : ℝ) ≤ error := by
    apply (div_le_iff₀ hsR).mpr
    simpa only [mul_comm] using ((div_lt_iff₀ he).mp hscale).le
  have hlo : (↑(k * scale) : ℝ) / scale = k := by
    push_cast
    exact mul_div_cancel_right₀ _ hsR.ne'
  have hhi : (↑(k * scale + 1) : ℝ) / scale = (k : ℝ) + 1 / scale := by
    push_cast
    rw [add_div, mul_div_cancel_right₀ _ hsR.ne']
  refine ⟨k * scale, k * scale + 1, scale, hs, ?_, ?_, ?_, ?_,
    initBucketCeiling_fails_of_straddle hs le_rfl (Nat.lt_succ_self _)⟩
  · rw [hlo]
    exact sub_le_self _ he.le
  · exact hlo.le
  · rw [hhi]
    exact le_add_of_nonneg_right (by positivity)
  · rw [hhi]
    exact add_le_add_right hwidth _

/-- For an unrestricted real LSST constant, the bucket ceiling argument
can be an integer. Its strict separation therefore requires more than
positivity of the constant. -/
theorem initBucketCeiling_exists_integral_argument (M N : ℕ) (hM : 1 ≤ M)
    (Ψ : ℝ) : ∃ C : ℝ, 1 ≤ C ∧ ∃ q : ℕ,
      let P := concreteChainParams M hM
      let σ := max (2 : ℝ) (max 1 (mwuK0 C * (P.k : ℝ) * (Real.log ((N : ℝ) + 2)) ^ 6))
      (2 * max 0 Ψ + (P.d : ℝ) * Real.log σ) / Real.log 2 = q := by
  let P := concreteChainParams M hM
  let D := (P.d : ℝ)
  let A := 6272 * (P.k : ℝ) * Real.log ((N : ℝ) + 2) ^ 6
  have hd : 0 < D := by unfold D; exact_mod_cast P.hd
  have hk : (0 : ℝ) < P.k := by exact_mod_cast P.hk
  have ha : 0 < A := by
    have hl : 0 < Real.log ((N : ℝ) + 2) := Real.log_pos (by linarith only [Nat.cast_nonneg (α := ℝ) N])
    dsimp [A]
    positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨q, hq⟩ := exists_nat_gt ((2 * max 0 Ψ + D * Real.log (max 2 A)) / Real.log 2)
  let x := ((q : ℝ) * Real.log 2 - 2 * max 0 Ψ) / D
  have hx : Real.log (max 2 A) < x := by
    apply (lt_div_iff₀ hd).mpr
    have hq' := (div_lt_iff₀ hlog).mp hq
    linarith only [hq']
  have hexp : max 2 A ≤ Real.exp x := by
    have h := Real.exp_le_exp.mpr hx.le
    rwa [Real.exp_log (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _))] at h
  let C := Real.exp x / A
  have hC : 1 ≤ C := (le_div_iff₀ ha).mpr (by simpa only [one_mul] using (le_max_right 2 A).trans hexp)
  refine ⟨C, hC, q, ?_⟩
  have hσ : mwuK0 C * (P.k : ℝ) * Real.log ((N : ℝ) + 2) ^ 6 = Real.exp x := by
    rw [mwuK0, max_eq_right hC]
    calc
      _ = C * A := by unfold A; ring
      _ = _ := div_mul_cancel₀ _ ha.ne'
  have htwo : (2 : ℝ) ≤ Real.exp x := (le_max_left _ _).trans hexp
  change (2 * max 0 Ψ + D * Real.log (max 2 (max 1
    (mwuK0 C * (P.k : ℝ) * Real.log ((N : ℝ) + 2) ^ 6)))) / Real.log 2 = _
  rw [hσ, max_eq_right (show (1 : ℝ) ≤ Real.exp x by linarith), max_eq_right htwo, Real.log_exp]
  apply (div_eq_iff hlog.ne').mpr
  unfold x
  field_simp
  ring

/-- A checked upper ceiling identifies the bucket bound for the concrete
chain. The logarithms in the bucket formula are enclosed before this check. -/
theorem concreteBCap_eq_of_scaledBounds
    (C Ψ : ℝ) (M N lo hi scale : ℕ) (hM : 1 ≤ M)
    (hs : 0 < scale) (hhiPos : 0 < hi) :
    let P := concreteChainParams M hM
    let σ := max (2 : ℝ) (max 1 (mwuK0 C * (P.k : ℝ) * (Real.log ((N : ℝ) + 2)) ^ 6))
    let b := (2 * max 0 Ψ + (P.d : ℝ) * Real.log σ) / Real.log 2
    let q := (hi - 1) / scale
    (lo : ℝ) / scale ≤ b → b ≤ (hi : ℝ) / scale → q * scale < lo →
    concreteBCap C Ψ M N hM = q + 3 := by
  dsimp only
  intro hlo hhi hcut
  let q := (hi - 1) / scale
  have hsReal : (0 : ℝ) < scale := by exact_mod_cast hs
  have hloCut : (q : ℝ) < (lo : ℝ) / scale :=
    (lt_div_iff₀ hsReal).mpr (by exact_mod_cast hcut)
  have hq := hloCut.trans_le hlo
  have hb : hi ≤ (q + 1) * scale := by
    have hlt : hi - 1 < (q + 1) * scale :=
      (Nat.div_lt_iff_lt_mul hs).mp (Nat.lt_succ_self q)
    omega
  have hupper : (hi : ℝ) / scale ≤ ((q + 1 : ℕ) : ℝ) :=
    (div_le_iff₀ hsReal).mpr (by exact_mod_cast hb)
  have hce := le_antisymm (Nat.ceil_le.mpr (hhi.trans hupper))
    (Nat.succ_le_of_lt (Nat.lt_ceil.mpr hq))
  dsimp only [concreteBCap]
  rw [hce]

end MinCostFlow.MinRatio
