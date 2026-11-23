module

public import MinCostFlow.DynSpanner.Program.DynSpannerAmortInput
public import MinCostFlow.DynSpanner.Program.DynSpannerAmortSparsify

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The translation cost of the sparsifier in the form of the budget

`sparsifyTransCost_le` bounds the cost of translating `(H', J, emb)` to the cited format and
back by `10000 · N · (log₂ ℓ' + 1) + 250 |E(J)| ⌈γ_ℓ⌉`, where `N` is the size of `J` with its
walks, plus the length `|x|` of the canonical input, its word size `w'` and the register bound
`R` of the guest. In the amortized analysis of a step with `0 < j` we compare this with the budget
of Lemma 5.9, which has one log factor `Λ₁ = 1 + ln(n + m + 2)` and powers of the length bound
`ℓ = lenBound(j - 1)`. This file does the comparison (`sparsifyTransCost_le_budget`), assuming
`|V(J)| ≤ 2 |E(J)|`, `1 ≤ |E(J)|`, `length(emb) ≤ ℓ + 1` and `|V(J)| + |E(J)| ≤ nm`:
`sparsifyTransCost ≤ transConst · |E(J)| (ℓ + 1)² Λ₁ + 500 |E(J)| γ_ℓ`.

The steps, with `Z = |V(J)| + |E(J)| (length + 1) + 1`:
* `|x| ≤ 7 Z`, and `|x| + max x + 2 ≤ 18 Z` (`canonSparsifyInput_size_le`), so the word size is
  `w' ≤ cw (log₂(18 Z) + 1) ≤ 18 cw Z`, and `N ≤ (9 + 18 cw + R) Z`. The word size adds to `N`; it
  does not multiply the log factor.
* `log₂ ℓ' + 1 ≤ 3 (1 + ln Z)` (`natLog2_mul_add_one_le`, since `ℓ' ≤ 2 Z`), and
  `ln Z ≤ ln(nm + 2) + length`, because `Z ≤ (nm + 2)(length + 1)` and `ln(y + 1) ≤ y`. So the log of
  the walk length becomes one more factor `ℓ + 2`.
* `Z ≤ 3 |E(J)| (ℓ + 1)` and `ℓ + 2 ≤ 3 (ℓ + 1) / 2`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

public section

/-- The constant of the translation in the budget form; it depends only on the guest's word-size
constant `cw` and register bound `R`. -/
def transConst (impl : SparsifyImpl) : ℕ :=
  135000 * (9 + 18 * impl.cw + impl.program.regBound)

/-- The word size of the canonical input is at most `18 cw Z`. -/
lemma wordSize_canonSparsifyInput_le (cw : ℕ) (H' J : MGraph) (emb : MinCostFlow.Embedding) :
    wordSize cw (canonSparsifyInput H' J emb) ≤
      cw * (18 * (J.n + J.m * (emb.length J + 1) + 1)) := by
  unfold wordSize
  refine Nat.mul_le_mul_left cw ?_
  have h := canonSparsifyInput_size_le H' J emb
  have h1 := Nat.log_mono_right (b := 2) h
  have h2 := Nat.log_lt_self 2 (x := 18 * (J.n + J.m * (emb.length J + 1) + 1)) (by omega)
  omega

/-- **The translation cost in the form of the budget.** -/
theorem sparsifyTransCost_le_budget (impl : SparsifyImpl) (mMax : ℕ) (H' J : MGraph)
    (emb : MinCostFlow.Embedding) {nm : ℕ} {ℓ : ℝ}
    (hJn : J.n ≤ 2 * J.m) (hJm : 1 ≤ J.m) (hnm : J.n + J.m ≤ nm)
    (hlen : (emb.length J : ℝ) ≤ ℓ + 1) (hℓ : 1 ≤ ℓ) :
    (sparsifyTransCost impl mMax H' J emb : ℝ) ≤
      (transConst impl : ℝ) * (J.m : ℝ) * (ℓ + 1) ^ 2 * (1 + Real.log ((nm : ℝ) + 2)) +
        500 * (J.m : ℝ) * impl.γ_ℓ mMax := by
  have hT := sparsifyTransCost_le impl mMax H' J emb
  simp only at hT
  have hx := canonSparsifyInput_length_le' H' J emb
  have hw := wordSize_canonSparsifyInput_le impl.cw H' J emb
  set len := emb.length J
  set R := impl.program.regBound
  set x := canonSparsifyInput H' J emb
  set Z := J.n + J.m * (len + 1) + 1 with hZ
  -- The factor `N`.
  have hZ1 : 1 ≤ Z := by omega
  have hN : J.n + J.m * (len + 1) + x.length + wordSize impl.cw x + R + 1 ≤
      (9 + 18 * impl.cw + R) * Z := by
    have e1 : impl.cw * (18 * Z) = 18 * (impl.cw * Z) := by ring
    have e2 : (9 + 18 * impl.cw + R) * Z = 9 * Z + 18 * (impl.cw * Z) + R * Z := by ring
    have hRZ : R ≤ R * Z := Nat.le_mul_of_pos_right R hZ1
    rw [e1] at hw
    rw [e2]
    omega
  -- The log factor.
  have hk : J.n + 2 * (J.m * len) + J.m + 2 ≤ 2 ^ 1 * Z := by
    have : J.m * (len + 1) = J.m * len + J.m := by ring
    omega
  have hlog := natLog2_mul_add_one_le hk hZ1
  have hZle : (Z : ℝ) ≤ ((nm : ℝ) + 2) * ((len : ℝ) + 1) := by
    have h1 : (Z : ℝ) = (J.n : ℝ) + (J.m : ℝ) * ((len : ℝ) + 1) + 1 := by
      rw [hZ]; push_cast; ring
    have h2 : ((J.n : ℝ) + (J.m : ℝ)) ≤ (nm : ℝ) := by exact_mod_cast hnm
    have hl0 : (0 : ℝ) ≤ len := Nat.cast_nonneg _
    have hn0 : (0 : ℝ) ≤ J.n := Nat.cast_nonneg _
    nlinarith
  have hZpos : (0 : ℝ) < Z := by exact_mod_cast hZ1
  have hnm2 : (0 : ℝ) < (nm : ℝ) + 2 := by positivity
  have hlen1 : (0 : ℝ) < (len : ℝ) + 1 := by positivity
  have hlnZ : Real.log (Z : ℝ) ≤ Real.log ((nm : ℝ) + 2) + (len : ℝ) := by
    have h1 := Real.log_le_log hZpos hZle
    rw [Real.log_mul hnm2.ne' hlen1.ne'] at h1
    have h2 := Real.log_le_sub_one_of_pos hlen1
    linarith
  set Λ₁ := 1 + Real.log ((nm : ℝ) + 2) with hΛ₁
  have hΛ₁1 : 1 ≤ Λ₁ := by
    have : 0 ≤ Real.log ((nm : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) nm])
    linarith
  have hlam : (Nat.log 2 (J.n + 2 * (J.m * len) + J.m + 2) : ℝ) + 1 ≤
      3 * Λ₁ * (ℓ + 2) := by
    have hl0 : (0 : ℝ) ≤ len := Nat.cast_nonneg _
    have h1 : 1 + Real.log (Z : ℝ) ≤ Λ₁ * ((len : ℝ) + 1) := by
      rw [hΛ₁]; nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ (nm : ℝ) + 2 by
        linarith [Nat.cast_nonneg (α := ℝ) nm])]
    have h2 : Λ₁ * ((len : ℝ) + 1) ≤ Λ₁ * (ℓ + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h3 : ((1 : ℕ) : ℝ) + 2 = 3 := by norm_num
    rw [h3] at hlog
    nlinarith
  -- The size `Z` against `|E(J)| (ℓ + 1)`.
  have hZm : (Z : ℝ) ≤ 3 * (J.m : ℝ) * (ℓ + 1) := by
    have h1 : (Z : ℝ) = (J.n : ℝ) + (J.m : ℝ) * ((len : ℝ) + 1) + 1 := by
      rw [hZ]; push_cast; ring
    have h2 : (J.n : ℝ) ≤ 2 * (J.m : ℝ) := by exact_mod_cast hJn
    have h3 : (1 : ℝ) ≤ J.m := by exact_mod_cast hJm
    have h4 : (J.m : ℝ) * ((len : ℝ) + 1) ≤ (J.m : ℝ) * (ℓ + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  -- Put the pieces together.
  set A : ℝ := (9 + 18 * (impl.cw : ℝ) + (R : ℝ))
  have hA0 : 0 ≤ A := by positivity
  have hNr : ((J.n + J.m * (len + 1) + x.length + wordSize impl.cw x + R + 1 : ℕ) : ℝ) ≤
      A * (Z : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hN
    push_cast at this ⊢
    exact this
  have hN0 : (0 : ℝ) ≤ ((J.n + J.m * (len + 1) + x.length + wordSize impl.cw x + R + 1 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hlam0 : (0 : ℝ) ≤ (Nat.log 2 (J.n + 2 * (J.m * len) + J.m + 2) : ℝ) + 1 := by positivity
  have hprod : ((J.n + J.m * (len + 1) + x.length + wordSize impl.cw x + R + 1 : ℕ) : ℝ) *
      ((Nat.log 2 (J.n + 2 * (J.m * len) + J.m + 2) : ℝ) + 1) ≤
      (A * (3 * (J.m : ℝ) * (ℓ + 1))) * (3 * Λ₁ * (ℓ + 2)) := by
    refine mul_le_mul (le_trans hNr (mul_le_mul_of_nonneg_left hZm hA0)) hlam hlam0 ?_
    have : (0 : ℝ) ≤ J.m := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ ℓ + 1 := by linarith
    positivity
  have hceil : (Nat.ceil (impl.γ_ℓ mMax) : ℝ) ≤ 2 * impl.γ_ℓ mMax := by
    have h1 := Nat.ceil_lt_add_one (show 0 ≤ impl.γ_ℓ mMax by linarith [impl.hγ_ℓ mMax])
    linarith [impl.hγ_ℓ mMax]
  have hTr : (sparsifyTransCost impl mMax H' J emb : ℝ) ≤
      10000 * (((J.n + J.m * (len + 1) + x.length + wordSize impl.cw x + R + 1 : ℕ) : ℝ) *
        ((Nat.log 2 (J.n + 2 * (J.m * len) + J.m + 2) : ℝ) + 1)) +
      250 * ((J.m : ℝ) * (Nat.ceil (impl.γ_ℓ mMax) : ℝ)) := by
    have := (Nat.cast_le (α := ℝ)).mpr hT
    push_cast at this ⊢
    linarith
  have hfin : (A * (3 * (J.m : ℝ) * (ℓ + 1))) * (3 * Λ₁ * (ℓ + 2)) ≤
      (27 / 2) * A * (J.m : ℝ) * (ℓ + 1) ^ 2 * Λ₁ := by
    have h0 : 0 ≤ A * (J.m : ℝ) * (ℓ + 1) * Λ₁ := by
      have : (0 : ℝ) ≤ J.m := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ ℓ + 1 := by linarith
      positivity
    have h1 : ℓ + 2 ≤ 3 / 2 * (ℓ + 1) := by linarith
    nlinarith
  have hmγ : (J.m : ℝ) * (Nat.ceil (impl.γ_ℓ mMax) : ℝ) ≤ (J.m : ℝ) * (2 * impl.γ_ℓ mMax) :=
    mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg _)
  have hconst : (transConst impl : ℝ) = 10000 * ((27 / 2) * A) := by
    simp only [transConst, A, R]; push_cast; ring
  rw [hconst]
  have hpos : 0 ≤ A * (J.m : ℝ) * (ℓ + 1) ^ 2 * Λ₁ := by
    have : (0 : ℝ) ≤ J.m := Nat.cast_nonneg _
    positivity
  nlinarith

end

end MinCostFlow.DynSpanner.Program
