module

public import MinCostFlow.MinRatio.ShiftQuotaDeposit
import Mathlib.Tactic

/-!
# The size of the shift deposit

The deposit `shiftDeposit i` per update at level `i` is the quota gain of a rebuild at level `i`
divided by the rebuild threshold `intRebuildThreshold i ≈ M₀ / (k^{i+1} log² N₀)`. The gain is at
most `(d + 1) (10 Ψ k)^{d+1-i}`. So the deposit is about `(d + 1) (10 Ψ)^{d+1} k^{d+2} log² N₀ / M₀`,
and since `k ≤ 2 M₀^{1/d}` (a field of `ChainParams`), `k^d ≤ 2^d M₀`. This gives
`shiftDeposit_le`:

  `shiftDeposit i ≤ (d + 1) (11 Ψ)^{d+1} 2^{d+2} M₀^{2/d} (clog₂ (N₀ + 2))² + 1`.

For the parameters of the paper, `d = Θ(log^{1/48} M₀)`, `k = M₀^{1/d}` and
`Ψ = exp(O(log^{23/24} M₀ · log log M₀))`, each factor is `M₀^{o(1)}`: `(11 Ψ)^{d+1}` and `2^{d+2}`
are `exp(O(log^{47/48} M₀ · log log M₀))`, and `M₀^{2/d} = exp(2 log M₀ / d)` is
`exp(O(log^{47/48} M₀))`. This is the bound we need: the deposit is the
`m^{o(1)}` factor that the paper's proof of Theorem 7.1 (page 29) puts in front of `Q / m`.
-/

public section

namespace MinCostFlow.MinRatio

open Chain

private theorem ceil_pow_le {x : ℝ} {X : ℕ} (hx : 0 ≤ x) (hX : x ≤ X) (n : ℕ) :
    ⌈x ^ n⌉₊ ≤ X ^ n := by
  rw [Nat.ceil_le]
  push_cast
  exact pow_le_pow_left₀ hx hX n

/-- The quota gain of a rebuild at level `i ≤ d` is at most `(d + 1) X^{d+1-i}`, where
`X = ⌈10 Ψ k⌉` is at least one. -/
theorem rebuildQuotaGain_le (P : ChainParams) {psi : ℝ} (hpsi : 0 ≤ psi) {i : ℕ}
    (hX : 1 ≤ ⌈10 * psi * (P.k : ℝ)⌉₊) :
    rebuildQuotaGain P psi i ≤ (P.d + 1) * ⌈10 * psi * (P.k : ℝ)⌉₊ ^ (P.d + 1 - i) := by
  unfold rebuildQuotaGain
  have hb : (0 : ℝ) ≤ 10 * psi * (P.k : ℝ) := by positivity
  calc (∑ j : Fin (P.d + 1), if i ≤ j.val then ⌈(10 * psi * (P.k : ℝ)) ^ (j.val + 1 - i)⌉₊ else 0)
      ≤ ∑ _j : Fin (P.d + 1), ⌈10 * psi * (P.k : ℝ)⌉₊ ^ (P.d + 1 - i) := by
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs
        · exact (ceil_pow_le hb (Nat.le_ceil _) _).trans
            (Nat.pow_le_pow_right hX (by have := j.isLt; omega))
        · exact Nat.zero_le _
    _ = (P.d + 1) * ⌈10 * psi * (P.k : ℝ)⌉₊ ^ (P.d + 1 - i) := by simp

/-- The deposit times `M₀` is at most the quota gain times `k^{i+1} clog₂(N₀ + 2)²`, plus `M₀`:
the threshold `t = ⌊M₀ / K⌋` with `K = k^{i+1} clog₂(N₀ + 2)²` has `M₀ < (t + 1) K`. -/
theorem shiftDeposit_mul_le (P : ChainParams) (N₀ : ℕ) (psi : ℝ) (i : ℕ) :
    shiftDeposit P N₀ psi i * P.M₀ ≤
      rebuildQuotaGain P psi i * (P.k ^ (i + 1) * Nat.clog 2 (N₀ + 2) ^ 2) + P.M₀ := by
  set K := P.k ^ (i + 1) * Nat.clog 2 (N₀ + 2) ^ 2 with hK
  set Q := rebuildQuotaGain P psi i
  have hc : 1 ≤ Nat.clog 2 (N₀ + 2) := Nat.succ_le_of_lt (Nat.clog_pos (by omega) (by omega))
  have hKpos : 0 < K := Nat.mul_pos (Nat.pow_pos P.hk) (Nat.pow_pos hc)
  have ht : intRebuildThreshold P N₀ i = P.M₀ / K := rfl
  set t := P.M₀ / K
  unfold shiftDeposit
  rw [ht]
  set D := (Q + t) / (t + 1)
  have h1 : P.M₀ < (t + 1) * K := by
    have := Nat.lt_div_mul_add (a := P.M₀) hKpos
    rw [Nat.add_mul, one_mul]; exact this
  have h2 : D * (t + 1) ≤ Q + t := Nat.div_mul_le_self _ _
  have h3 : t * K ≤ P.M₀ := Nat.div_mul_le_self _ _
  calc D * P.M₀ ≤ D * ((t + 1) * K) := Nat.mul_le_mul_left _ h1.le
    _ = D * (t + 1) * K := by ring
    _ ≤ (Q + t) * K := Nat.mul_le_mul_right _ h2
    _ = Q * K + t * K := by ring
    _ ≤ Q * K + P.M₀ := Nat.add_le_add_left h3 _

/-- **The deposit is subpolynomial.** For `Ψ ≥ 1` and `i ≤ d`,
`shiftDeposit i ≤ (d + 1) (11 Ψ)^{d+1} 2^{d+2} M₀^{2/d} clog₂(N₀ + 2)² + 1`. -/
theorem shiftDeposit_le (P : ChainParams) (N₀ : ℕ) {psi : ℝ} (hpsi : 1 ≤ psi) {i : ℕ}
    (hi : i ≤ P.d) :
    (shiftDeposit P N₀ psi i : ℝ) ≤
      (P.d + 1) * (11 * psi) ^ (P.d + 1) * 2 ^ (P.d + 2) * (P.M₀ : ℝ) ^ (2 / (P.d : ℝ)) *
        (Nat.clog 2 (N₀ + 2) : ℝ) ^ 2 + 1 := by
  have hk1 : (1 : ℝ) ≤ P.k := by exact_mod_cast P.hk
  have hM : (0 : ℝ) < P.M₀ := by exact_mod_cast P.hM₀
  have hd : (0 : ℝ) < P.d := by exact_mod_cast P.hd
  have hX1 : (1 : ℝ) ≤ 10 * psi * P.k := by nlinarith
  have hX : 1 ≤ ⌈10 * psi * (P.k : ℝ)⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  set X := ⌈10 * psi * (P.k : ℝ)⌉₊
  set c := Nat.clog 2 (N₀ + 2)
  have hXle : (X : ℝ) ≤ 11 * psi * P.k := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 10 * psi * P.k)
    nlinarith
  -- `k^d ≤ 2^d M₀` and `k^2 ≤ 4 M₀^{2/d}`
  have hroot : (0 : ℝ) ≤ (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) := Real.rpow_nonneg hM.le _
  have hkd : (P.k : ℝ) ^ P.d ≤ 2 ^ P.d * P.M₀ := by
    calc (P.k : ℝ) ^ P.d ≤ (2 * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ P.d :=
          pow_le_pow_left₀ (by linarith) P.hk_upper _
      _ = 2 ^ P.d * P.M₀ := by
          rw [mul_pow, ← Real.rpow_natCast ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))), ← Real.rpow_mul hM.le,
            one_div_mul_cancel hd.ne', Real.rpow_one]
  have hk2 : (P.k : ℝ) ^ 2 ≤ 4 * (P.M₀ : ℝ) ^ (2 / (P.d : ℝ)) := by
    calc (P.k : ℝ) ^ 2 ≤ (2 * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (by linarith) P.hk_upper _
      _ = 4 * (P.M₀ : ℝ) ^ (2 / (P.d : ℝ)) := by
          rw [mul_pow, ← Real.rpow_natCast ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))), ← Real.rpow_mul hM.le]
          norm_num
          ring_nf
  -- the gain times `k^{i+1}` is at most `(d + 1) (11 Ψ)^{d+1} k^{d+2}`
  have hgain : (rebuildQuotaGain P psi i : ℝ) * (P.k : ℝ) ^ (i + 1) ≤
      (P.d + 1) * (11 * psi) ^ (P.d + 1) * (P.k : ℝ) ^ (P.d + 2) := by
    have hQ : (rebuildQuotaGain P psi i : ℝ) ≤ (P.d + 1) * (X : ℝ) ^ (P.d + 1 - i) := by
      exact_mod_cast rebuildQuotaGain_le P (by linarith) hX
    have hXp : (X : ℝ) ^ (P.d + 1 - i) ≤ (11 * psi) ^ (P.d + 1 - i) * (P.k : ℝ) ^ (P.d + 1 - i) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
    have hpsiPow : (11 * psi) ^ (P.d + 1 - i) ≤ (11 * psi) ^ (P.d + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hkPow : (P.k : ℝ) ^ (P.d + 1 - i) * (P.k : ℝ) ^ (i + 1) = (P.k : ℝ) ^ (P.d + 2) := by
      rw [← pow_add]; congr 1; omega
    calc (rebuildQuotaGain P psi i : ℝ) * (P.k : ℝ) ^ (i + 1)
        ≤ (P.d + 1) * ((11 * psi) ^ (P.d + 1 - i) * (P.k : ℝ) ^ (P.d + 1 - i)) *
            (P.k : ℝ) ^ (i + 1) := by
          gcongr
          exact hQ.trans (by gcongr)
      _ ≤ (P.d + 1) * ((11 * psi) ^ (P.d + 1) * (P.k : ℝ) ^ (P.d + 1 - i)) *
            (P.k : ℝ) ^ (i + 1) := by gcongr
      _ = (P.d + 1) * (11 * psi) ^ (P.d + 1) * (P.k : ℝ) ^ (P.d + 2) := by
          rw [← hkPow]; ring
  have hmul : (shiftDeposit P N₀ psi i : ℝ) * P.M₀ ≤
      (rebuildQuotaGain P psi i : ℝ) * (P.k : ℝ) ^ (i + 1) * (c : ℝ) ^ 2 + P.M₀ := by
    have := shiftDeposit_mul_le P N₀ psi i
    have h' : ((shiftDeposit P N₀ psi i * P.M₀ : ℕ) : ℝ) ≤
        ((rebuildQuotaGain P psi i * (P.k ^ (i + 1) * c ^ 2) + P.M₀ : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at h'
    linarith
  have hkd2 : (P.k : ℝ) ^ (P.d + 2) ≤ 2 ^ P.d * P.M₀ * (4 * (P.M₀ : ℝ) ^ (2 / (P.d : ℝ))) := by
    rw [pow_add]
    exact mul_le_mul hkd hk2 (by positivity) (by positivity)
  have hc0 : (0 : ℝ) ≤ (c : ℝ) ^ 2 := by positivity
  have hA : (0 : ℝ) ≤ (P.d + 1) * (11 * psi) ^ (P.d + 1) := by positivity
  have hbound : (shiftDeposit P N₀ psi i : ℝ) * P.M₀ ≤
      ((P.d + 1) * (11 * psi) ^ (P.d + 1) * 2 ^ (P.d + 2) * (P.M₀ : ℝ) ^ (2 / (P.d : ℝ)) *
        (c : ℝ) ^ 2 + 1) * P.M₀ := by
    calc (shiftDeposit P N₀ psi i : ℝ) * P.M₀
        ≤ (rebuildQuotaGain P psi i : ℝ) * (P.k : ℝ) ^ (i + 1) * (c : ℝ) ^ 2 + P.M₀ := hmul
      _ ≤ (P.d + 1) * (11 * psi) ^ (P.d + 1) * (P.k : ℝ) ^ (P.d + 2) * (c : ℝ) ^ 2 + P.M₀ := by
          gcongr
      _ ≤ (P.d + 1) * (11 * psi) ^ (P.d + 1) *
            (2 ^ P.d * P.M₀ * (4 * (P.M₀ : ℝ) ^ (2 / (P.d : ℝ)))) * (c : ℝ) ^ 2 + P.M₀ := by
          gcongr
      _ = _ := by ring
  exact le_of_mul_le_mul_right hbound hM

end MinCostFlow.MinRatio
