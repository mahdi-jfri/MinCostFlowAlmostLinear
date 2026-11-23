module

public import MinCostFlow.HierPaths.Params

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# `Γ` as a power of two times a polynomial in `d`

Every factor of `Γ` other than `(1 + (2 + d)^4)^2` is at most a power of two. This file
collects their exponents in one number `gammaExp a M` and proves
`Γ ≤ (1 + (2 + d)^4)^2 · 2^{gammaExp a M}` (`gammaHP_le_two_pow`). It then bounds the exponent in
two ways.

* Linearly in `X`: `gammaExp a M ≤ (162 a + 10) X + 26` (`gammaExp_le_linear`). The key step is
  that `j ≈ X^{1/3}` and `⌈log₂(X + 2)⌉ ≤ 3 j`, so `a j ⌈log₂(X + 2)⌉ (2 j + 2) ≤ 162 a X`. Since
  `2^X ≤ 16 (M + 1)`, this gives the polynomial bound `Γ ≤ 2^28 (d + M + 2)^{810 a + 58}`
  (`gammaHP_le_poly`).
* By the 24th root `s = ⌈X^{1/24}⌉`: `gammaExp a M ≤ (36 + 96 a) s^21` and `s^24 ≤ 2^24 X`
  (`gammaExp_le_root`, `root24_pow_le`). This is the form of `log Γ = O(X^{2/3} log(X + 2))`
  that the subpolynomial bounds use, with `X^{2/3} log(X + 2) = O(X^{7/8})`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-- The exponent `12 + 4(j + 1) + 2(j + 1) + 4(⌈X^{2/3}⌉ + 2) + a j ⌈log₂(X + 2)⌉ (2 j + 2)` that
bounds all factors of `Γ` other than `(1 + (2 + d)^4)^2`. -/
def gammaExp (a M : ℕ) : ℕ :=
  12 + 4 * (bigJ M + 1) + 2 * (bigJ M + 1) + 4 * (ceilRoot 2 (bigX M ^ 2) + 2) +
    a * bigJ M * Nat.clog 2 (bigX M + 2) * (2 * bigJ M + 2)

private lemma succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self

/-- `Γ ≤ (1 + (2 + d)^4)^2 · 2^{gammaExp a M}`, factor by factor. -/
theorem gammaHP_le_two_pow (a d M : ℕ) :
    gammaHP a d M ≤ (1 + (2 + d) ^ 4) ^ 2 * 2 ^ gammaExp a M := by
  set j := bigJ M
  set R := ceilRoot 2 (bigX M ^ 2)
  have hj : (j + 2) ^ 4 ≤ 2 ^ (4 * (j + 1)) := by
    rw [pow_mul, ← Nat.pow_mul]; rw [mul_comm 4 (j + 1), Nat.pow_mul]
    exact Nat.pow_le_pow_left (succ_le_two_pow (j + 1)) 4
  have h4 : 4 ^ (j + 1) = 2 ^ (2 * (j + 1)) := by rw [pow_mul]; norm_num
  have hK : (bigKB M + 1) ^ 4 ≤ 2 ^ (4 * (R + 2)) := by
    rw [mul_comm 4 (R + 2), Nat.pow_mul]
    apply Nat.pow_le_pow_left
    change 2 ^ (1 + R) + 1 ≤ 2 ^ (R + 2)
    have : 1 ≤ 2 ^ (1 + R) := Nat.one_le_two_pow
    have h2 : 2 ^ (R + 2) = 2 * 2 ^ (1 + R) := by rw [show R + 2 = (1 + R) + 1 by ring, pow_succ]; ring
    omega
  have hU : bigUX a M ^ (2 * j + 2) =
      2 ^ (a * j * Nat.clog 2 (bigX M + 2) * (2 * j + 2)) := by
    unfold bigUX; rw [← pow_mul]
  have hexp : 2 ^ gammaExp a M = 2 ^ 12 * 2 ^ (4 * (j + 1)) * 2 ^ (2 * (j + 1)) *
      2 ^ (4 * (R + 2)) * 2 ^ (a * j * Nat.clog 2 (bigX M + 2) * (2 * j + 2)) := by
    unfold gammaExp; rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
  unfold gammaHP
  rw [hexp, h4, hU]
  calc 2 ^ 12 * (j + 2) ^ 4 * 2 ^ (2 * (j + 1)) * (bigKB M + 1) ^ 4 * (1 + (2 + d) ^ 4) ^ 2 *
        2 ^ (a * j * Nat.clog 2 (bigX M + 2) * (2 * j + 2))
      ≤ 2 ^ 12 * 2 ^ (4 * (j + 1)) * 2 ^ (2 * (j + 1)) * 2 ^ (4 * (R + 2)) *
        (1 + (2 + d) ^ 4) ^ 2 * 2 ^ (a * j * Nat.clog 2 (bigX M + 2) * (2 * j + 2)) := by
        gcongr
    _ = _ := by ring

lemma one_le_bigX (M : ℕ) : 3 ≤ bigX M := three_le_xOf M

lemma two_le_bigJ (M : ℕ) : 2 ≤ bigJ M := two_le_depthOf M

/-- `⌈log₂(X + 2)⌉ ≤ 3 j`, since `X + 2 ≤ j^3 + 2 ≤ (j + 1)^3 ≤ 2^{3j}`. -/
lemma clog_bigX_le (M : ℕ) : Nat.clog 2 (bigX M + 2) ≤ 3 * bigJ M := by
  apply Nat.clog_le_of_le_pow
  have hX : bigX M ≤ bigJ M ^ 3 := le_ceilRoot_pow 2 (bigX M)
  have hj := two_le_bigJ M
  have h1 : bigJ M + 1 ≤ 2 ^ bigJ M := succ_le_two_pow _
  calc bigX M + 2 ≤ bigJ M ^ 3 + 2 := by omega
    _ ≤ (bigJ M + 1) ^ 3 := by nlinarith
    _ ≤ (2 ^ bigJ M) ^ 3 := Nat.pow_le_pow_left h1 3
    _ = 2 ^ (3 * bigJ M) := by rw [← pow_mul, mul_comm]

/-- `(j + 1)^3 ≤ 27 X`, since `(j - 1)^3 < X` by the minimality of `j`, and `j + 1 ≤ 3 (j - 1)`
for `j ≥ 2`. -/
lemma succ_bigJ_cube_le (M : ℕ) : (bigJ M + 1) ^ 3 ≤ 27 * bigX M := by
  have hj := two_le_bigJ M
  have hlt : (bigJ M - 1) ^ 3 < bigX M := pow_lt_of_lt_ceilRoot (k := 2) (by unfold bigJ at hj ⊢; omega)
  have h3 : bigJ M + 1 ≤ 3 * (bigJ M - 1) := by omega
  calc (bigJ M + 1) ^ 3 ≤ (3 * (bigJ M - 1)) ^ 3 := Nat.pow_le_pow_left h3 3
    _ = 27 * (bigJ M - 1) ^ 3 := by ring
    _ ≤ 27 * bigX M := by omega

/-- `gammaExp a M ≤ (162 a + 10) X + 26`. -/
theorem gammaExp_le_linear (a M : ℕ) : gammaExp a M ≤ (162 * a + 10) * bigX M + 26 := by
  have hj := two_le_bigJ M
  have hjX : bigJ M ≤ bigX M := ceilRoot_le_self 2 (bigX M)
  have hRX : ceilRoot 2 (bigX M ^ 2) ≤ bigX M := by
    apply ceilRoot_le
    have := one_le_bigX M
    exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have hv := clog_bigX_le M
  have hc := succ_bigJ_cube_le M
  have hmain : a * bigJ M * Nat.clog 2 (bigX M + 2) * (2 * bigJ M + 2) ≤ 162 * a * bigX M := by
    calc a * bigJ M * Nat.clog 2 (bigX M + 2) * (2 * bigJ M + 2)
        ≤ a * bigJ M * (3 * bigJ M) * (2 * bigJ M + 2) := by gcongr
      _ ≤ a * (6 * (bigJ M + 1) ^ 3) := by
        have : bigJ M * (3 * bigJ M) * (2 * bigJ M + 2) ≤ 6 * (bigJ M + 1) ^ 3 := by nlinarith
        calc a * bigJ M * (3 * bigJ M) * (2 * bigJ M + 2)
            = a * (bigJ M * (3 * bigJ M) * (2 * bigJ M + 2)) := by ring
          _ ≤ a * (6 * (bigJ M + 1) ^ 3) := Nat.mul_le_mul_left a this
      _ ≤ a * (6 * (27 * bigX M)) := by gcongr
      _ = 162 * a * bigX M := by ring
  unfold gammaExp
  nlinarith

/-- `2^X ≤ 16 (M + 1)`, from `2^{X-1} < 8M + 8`. -/
lemma two_pow_bigX_le (M : ℕ) : 2 ^ bigX M ≤ 16 * (M + 1) := by
  have hX := one_le_bigX M
  unfold bigX at hX ⊢
  obtain ⟨k, hk⟩ : ∃ k, Nat.clog 2 (8 * M + 8) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  have h := Nat.pow_pred_clog_lt_self (b := 2) (x := 8 * M + 8) (by decide) (by omega)
  rw [hk, Nat.pred_succ] at h
  rw [hk, pow_succ]
  omega

/-- The polynomial bound `Γ ≤ 2^28 (d + M + 2)^{810 a + 58}`. -/
theorem gammaHP_le_poly (a d M : ℕ) :
    gammaHP a d M ≤ 2 ^ 28 * (d + M + 2) ^ (810 * a + 58) := by
  set N := d + M + 2
  have hN : 2 ≤ N := by omega
  have hN4 : 16 ≤ N ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ N ^ 4 := Nat.pow_le_pow_left hN 4
  have h2X : 2 ^ bigX M ≤ N ^ 5 := by
    calc 2 ^ bigX M ≤ 16 * (M + 1) := two_pow_bigX_le M
      _ ≤ N ^ 4 * N := Nat.mul_le_mul hN4 (by omega)
      _ = N ^ 5 := by ring
  have hE : 2 ^ gammaExp a M ≤ 2 ^ 26 * N ^ (5 * (162 * a + 10)) := by
    calc 2 ^ gammaExp a M ≤ 2 ^ ((162 * a + 10) * bigX M + 26) :=
          Nat.pow_le_pow_right (by decide) (gammaExp_le_linear a M)
      _ = 2 ^ 26 * (2 ^ bigX M) ^ (162 * a + 10) := by
          rw [pow_add, mul_comm (162 * a + 10) (bigX M), pow_mul, mul_comm]
      _ ≤ 2 ^ 26 * (N ^ 5) ^ (162 * a + 10) := by gcongr
      _ = 2 ^ 26 * N ^ (5 * (162 * a + 10)) := by rw [← pow_mul]
  have hD : (1 + (2 + d) ^ 4) ^ 2 ≤ 4 * N ^ 8 := by
    have h1 : (2 + d) ^ 4 ≤ N ^ 4 := Nat.pow_le_pow_left (by omega) 4
    calc (1 + (2 + d) ^ 4) ^ 2 ≤ (2 * N ^ 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * N ^ 8 := by ring
  calc gammaHP a d M ≤ (1 + (2 + d) ^ 4) ^ 2 * 2 ^ gammaExp a M := gammaHP_le_two_pow a d M
    _ ≤ 4 * N ^ 8 * (2 ^ 26 * N ^ (5 * (162 * a + 10))) := Nat.mul_le_mul hD hE
    _ = (4 * 2 ^ 26) * (N ^ 8 * N ^ (5 * (162 * a + 10))) := mul_mul_mul_comm _ _ _ _
    _ = 2 ^ 28 * N ^ (810 * a + 58) := by
        rw [← pow_add, show 8 + 5 * (162 * a + 10) = 810 * a + 58 by ring]; norm_num

/-! ## The bound by the 24th root of `X` -/

/-- `s^24 ≤ 2^24 X` for `s = ⌈X^{1/24}⌉`, since `(s - 1)^24 < X` and `s ≤ 2 (s - 1)`. -/
lemma root24_pow_le (M : ℕ) : ceilRoot 23 (bigX M) ^ 24 ≤ 2 ^ 24 * bigX M := by
  have hs : 2 ≤ ceilRoot 23 (bigX M) := one_lt_ceilRoot (by have := one_le_bigX M; omega)
  have hlt : (ceilRoot 23 (bigX M) - 1) ^ 24 < bigX M := pow_lt_of_lt_ceilRoot (by omega)
  calc ceilRoot 23 (bigX M) ^ 24 ≤ (2 * (ceilRoot 23 (bigX M) - 1)) ^ 24 :=
        Nat.pow_le_pow_left (by omega) 24
    _ = 2 ^ 24 * (ceilRoot 23 (bigX M) - 1) ^ 24 := by ring
    _ ≤ 2 ^ 24 * bigX M := by omega

/-- `gammaExp a M ≤ (36 + 96 a) s^21` for `s = ⌈X^{1/24}⌉`. Here `j ≤ s^8`, `⌈X^{2/3}⌉ ≤ s^16`
and `⌈log₂(X + 2)⌉ ≤ 24 s`, since `X + 2 ≤ (s + 1)^24 ≤ 2^{24 s}`. -/
theorem gammaExp_le_root (a M : ℕ) :
    gammaExp a M ≤ (36 + 96 * a) * ceilRoot 23 (bigX M) ^ 21 := by
  set s := ceilRoot 23 (bigX M)
  have hs : 2 ≤ s := one_lt_ceilRoot (by have := one_le_bigX M; omega)
  have hXs : bigX M ≤ s ^ 24 := le_ceilRoot_pow 23 (bigX M)
  have hj : bigJ M ≤ s ^ 8 := ceilRoot_le (by
    calc bigX M ≤ s ^ 24 := hXs
      _ = (s ^ 8) ^ (2 + 1) := by ring)
  have hR : ceilRoot 2 (bigX M ^ 2) ≤ s ^ 16 := ceilRoot_le (by
    calc bigX M ^ 2 ≤ (s ^ 24) ^ 2 := Nat.pow_le_pow_left hXs 2
      _ = (s ^ 16) ^ (2 + 1) := by ring)
  have hv : Nat.clog 2 (bigX M + 2) ≤ 24 * s := by
    apply Nat.clog_le_of_le_pow
    have h1 : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
    have h2 : s ^ 24 + 2 ≤ (s + 1) ^ 24 := by
      have h3 : s ^ 23 ≤ (s + 1) ^ 23 := Nat.pow_le_pow_left (by omega) 23
      have h4 : 2 ≤ (s + 1) ^ 23 :=
        le_trans (by norm_num) (Nat.pow_le_pow_left (show 2 ≤ s + 1 by omega) 23)
      calc s ^ 24 + 2 = s ^ 23 * s + 2 := by ring
        _ ≤ (s + 1) ^ 23 * s + (s + 1) ^ 23 := Nat.add_le_add (Nat.mul_le_mul_right s h3) h4
        _ = (s + 1) ^ 24 := by ring
    calc bigX M + 2 ≤ s ^ 24 + 2 := by omega
      _ ≤ (s + 1) ^ 24 := h2
      _ ≤ (2 ^ s) ^ 24 := Nat.pow_le_pow_left h1 24
      _ = 2 ^ (24 * s) := by rw [← pow_mul, mul_comm]
  have hs1 : 1 ≤ s ^ 21 := Nat.one_le_pow _ _ (by omega)
  have hs8 : s ^ 8 ≤ s ^ 21 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hs16 : s ^ 16 ≤ s ^ 21 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hmain : a * bigJ M * Nat.clog 2 (bigX M + 2) * (2 * bigJ M + 2) ≤ 96 * a * s ^ 21 := by
    calc a * bigJ M * Nat.clog 2 (bigX M + 2) * (2 * bigJ M + 2)
        ≤ a * s ^ 8 * (24 * s) * (2 * s ^ 8 + 2) := by gcongr
      _ ≤ a * s ^ 8 * (24 * s) * (4 * s ^ 8) := by
          gcongr; have : 1 ≤ s ^ 8 := Nat.one_le_pow _ _ (by omega); omega
      _ = 96 * a * s ^ 17 := by ring
      _ ≤ 96 * a * s ^ 21 := by gcongr; omega
  unfold gammaExp
  nlinarith

end MinCostFlow.HierPaths
