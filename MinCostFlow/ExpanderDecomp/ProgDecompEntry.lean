module

public import WordRAM.Entry
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.Statement
public import MinCostFlow.ExpanderDecomp.ProgDecompEntrySpec

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Top-Level Entry Program for Expander Decomposition (`ProgDecompEntry`)

Implements the deterministic (`NoRand`) Word-RAM entry procedure `decompEntryProc bOuter` for
`ExpanderDecompositionUsed` (`ExpanderDecomp/Statement.lean`):

1. On input `G.encode ++ [1, 200, rOf G.m]` in `initMem`, `GraphAt (initMem input) 0 G` already
   holds at address `0`, `rOf G.m` sits at `input.length - 1`, and memory from `input.length`
   onwards is zero.
2. `decompEntryProc bOuter` reads `n = mem[0]` and `r = mem[len - 1]`, sets `outAddr = len` and
   `h = len + n`, calls the outer decomposition procedure `bOuter` with `[0, r, outAddr, h]`
   (specified by `outerDecompEntryContract K C_sp w` in `ProgDecompEntrySpec.lean`), copies the `n`
   written labels forward from `outAddr` to address `0` (safe even when `n > outAddr` since
   `0 < outAddr`), and returns `n`.
3. `decompEntry_runsTo` and `expanderDecompositionUsed_of_outerContract` (together with
   `expanderDecompositionUsed_of_outerProcs`) derive `ExpanderDecompositionUsed` using
   `decompModelLabels_spec`, `decompModelCost_le_used`, and `phiOut_ge_used`, with explicit
   constants `c = decompEntryWordC C_sp`, `K_out = decompEntryK K`, and `cr = envelopeCr`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Entry Procedure (`NoRand`) and Constants -/

/-- Forward copy loop: copies `r1` (`G.n`) words from `r4` (`outAddr > 0`) down to address `0`.
Because `0 < outAddr`, writing cell `i` never overwrites any unread source cell `outAddr + t`
with `t ≥ i`. -/
def decompEntryCopyStmt : Stmt :=
  forRange 6 (.const 0) (.reg 1) (
    seqStmts [
      .assign 7 (.load (.bin .add (.reg 4) (.reg 6))),
      .store (.reg 6) (.reg 7)
    ]
  )

/-- Top-level entry procedure calling the outer expander-decomposition procedure at index `bOuter`.
Started by `WordRAM.run` with `args = [input.length]` on `initMem (G.encode ++ [1, 200, rOf G.m])`,
writes `decompModelLabels G` at address `0` and returns `G.n`. -/
def decompEntryProc (bOuter : ℕ) : Stmt :=
  seqStmts [
    .assign 1 (.load (.const 0)),
    .assign 2 (.load (.bin .sub (.reg 0) (.const 1))),
    .assign 4 (.reg 0),
    .assign 5 (.bin .add (.reg 4) (.reg 1)),
    .call 3 bOuter [.const 0, .reg 2, .reg 4, .reg 5],
    decompEntryCopyStmt,
    .ret (.reg 1)
  ]

theorem decompEntryProc_noRand (bOuter : ℕ) : (decompEntryProc bOuter).NoRand := by
  simp [decompEntryProc, decompEntryCopyStmt, seqStmts, forRange, forUp, Stmt.NoRand]

/-- Word-size constant `c` chosen for `ExpanderDecompositionUsed`, depending only on the outer
procedure's space constant `C_sp` and `ParamConfig.default`. -/
def decompEntryWordC (C_sp : ℕ) : ℕ :=
  6 * envelopeKNat ParamConfig.default +
    Nat.log 2 (2 * envelopeKNat ParamConfig.default * 200 ^ 2) +
    Nat.log 2 (2 * C_sp + 3) + 10

/-- Conductance/time envelope constant `K_out` chosen for `ExpanderDecompositionUsed`, depending
only on the outer procedure's cost constant `K` and `ParamConfig.default`. -/
def decompEntryK (K : ℕ) : ℝ :=
  ((K + 1) * (envelopeKNat ParamConfig.default + 120) : ℕ)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 2. Word-Size, Conductance, and Cost-Envelope Lemmas -/

private lemma half_lt_log_two_entry : (1 / 2 : ℝ) < Real.log 2 := by
  have h1 : (1 / 2 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := by
    have := Real.add_one_lt_exp (show -(1 / 2 : ℝ) ≠ 0 by norm_num)
    linarith
  have h2 : Real.exp (1 / 2 : ℝ) < 2 := by
    rw [Real.exp_neg] at h1
    have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
    rw [lt_inv_comm₀ (by norm_num) hpos] at h1
    linarith
  have h3 := Real.log_lt_log (Real.exp_pos _) h2
  simpa [Real.log_exp] using h3

private lemma rOf_sq_mul_log_log_le {m : ℕ} (hm : thresholdB1 envelopeCr ≤ m) :
    (rOf m : ℝ) ^ 2 * Real.log (Real.log ((m : ℝ) + 2)) ≤ 5 * Real.log ((m : ℝ) + 2) := by
  set x : ℝ := Real.log ((m : ℝ) + 2)
  have hm4 : 4 ≤ m := le_trans (four_le_thresholdB1 envelopeCr) hm
  have hx2 : 2 ≤ x := two_le_log_of_thresholdB1 hm
  have hx_pos : 0 < x := by linarith
  have hr3_nat : (rOf m) ^ 3 ≤ Nat.log 2 m := rOf_pow_le m
  have hpow_le : (2 : ℝ) ^ (Nat.log 2 m) ≤ (m : ℝ) + 2 := by
    have h1 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 ^ Nat.log 2 m : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hlog_le : (Nat.log 2 m : ℝ) * Real.log 2 ≤ x := by
    have h1 := Real.log_le_log (by positivity) hpow_le
    rwa [Real.log_pow] at h1
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := half_lt_log_two_entry
  have hr3 : (rOf m : ℝ) ^ 3 ≤ 2 * x := by
    have hnat : (rOf m : ℝ) ^ 3 ≤ (Nat.log 2 m : ℝ) := by exact_mod_cast hr3_nat
    have hnn : (0 : ℝ) ≤ (Nat.log 2 m : ℝ) := by positivity
    nlinarith
  set y : ℝ := x ^ (1 / 3 : ℝ)
  have hy_pos : 0 < y := Real.rpow_pos_of_pos hx_pos _
  have hy3 : y ^ 3 = x := by
    dsimp only [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
    norm_num
  have hlogx_le : Real.log x ≤ 3 * y := by
    have h1 : Real.log x = 3 * Real.log y := by
      rw [← hy3, Real.log_pow]
      ring
    have h2 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy_pos
    linarith
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hcube : ((rOf m : ℝ) ^ 2 * Real.log x) ^ 3 ≤ (5 * x) ^ 3 := by
    have h1 : ((rOf m : ℝ) ^ 3) ^ 2 ≤ (2 * x) ^ 2 := pow_le_pow_left₀ (by positivity) hr3 2
    have h2 : (Real.log x) ^ 3 ≤ (3 * y) ^ 3 := pow_le_pow_left₀ hlogx_nn hlogx_le 3
    have h3 : ((rOf m : ℝ) ^ 2 * Real.log x) ^ 3 =
        ((rOf m : ℝ) ^ 3) ^ 2 * (Real.log x) ^ 3 := by ring
    have h4 : (2 * x) ^ 2 * (3 * y) ^ 3 = 108 * x ^ 3 := by
      calc (2 * x) ^ 2 * (3 * y) ^ 3 = 108 * x ^ 2 * y ^ 3 := by ring
        _ = 108 * x ^ 2 * x := by rw [hy3]
        _ = 108 * x ^ 3 := by ring
    have h5 : ((rOf m : ℝ) ^ 3) ^ 2 * (Real.log x) ^ 3 ≤ (2 * x) ^ 2 * (3 * y) ^ 3 :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have h6 : 108 * x ^ 3 ≤ (5 * x) ^ 3 := by
      have : 0 ≤ x ^ 3 := by positivity
      linarith [show (5 * x) ^ 3 = 125 * x ^ 3 by ring]
    linarith
  by_contra hgt
  push Not at hgt
  have hlhs_nn : 0 ≤ (rOf m : ℝ) ^ 2 * Real.log x := by positivity
  have h5x_nn : 0 ≤ 5 * x := by positivity
  have : (5 * x) ^ 3 < ((rOf m : ℝ) ^ 2 * Real.log x) ^ 3 := by
    have hsq : (5 * x) ^ 2 ≤ ((rOf m : ℝ) ^ 2 * Real.log x) ^ 2 := by nlinarith
    nlinarith
  linarith

private lemma mem_le_foldr_max {xs : List ℕ} {x : ℕ} (hx : x ∈ xs) : x ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldr_cons, List.mem_cons] at hx ⊢
    rcases hx with rfl | hmem
    · exact le_max_left _ _
    · exact le_trans (ih hmem) (le_max_right _ _)

private lemma totalTimeRaw_le_pow_aux {G : Graph} {K_nat : ℕ}
    (hK_eq : envelopeK ParamConfig.default = (K_nat : ℝ))
    (hK_pos : 0 < (K_nat : ℝ))
    (hm : thresholdB1 envelopeCr ≤ G.m) :
    let inp := G.encode ++ [1, 200, rOf G.m]
    let B := inp.length + inp.foldr max 0 + 2
    totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) ≤
      B ^ (6 * K_nat + Nat.log 2 (2 * K_nat * 200 ^ 2) + 2) := by
  intro inp B
  have hm4 : 4 ≤ G.m := le_trans (four_le_thresholdB1 envelopeCr) hm
  have hr1 : 1 ≤ rOf G.m := one_le_rOf (by omega)
  have hlen_inp : inp.length = 2 * G.m + 5 := by
    simp only [inp, List.length_append, graph_encode_length, List.length_cons, List.length_nil]
    omega
  have hn_le_max : G.n ≤ inp.foldr max 0 := by
    apply mem_le_foldr_max
    simp [inp, Graph.encode]
  have h200_le_max : 200 ≤ inp.foldr max 0 := by
    apply mem_le_foldr_max
    simp [inp]
  have hB_ge_nm : G.n + 2 * G.m + 7 ≤ B := by
    dsimp only [B]; omega
  have hB_ge_200 : 207 ≤ B := by
    dsimp only [B]; omega
  have hB2 : 2 ≤ B := by omega
  have hcost := totalTimeRaw_le_used ParamConfig.default G.n hm
  have hm2_ge1 : (1 : ℝ) ≤ (G.m : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (G.m : ℝ) := Nat.cast_nonneg _
    linarith
  have hm2_pos : (0 : ℝ) < (G.m : ℝ) + 2 := by linarith
  have hx2 : 2 ≤ Real.log ((G.m : ℝ) + 2) := two_le_log_of_thresholdB1 hm
  have hx_pos : 0 < Real.log ((G.m : ℝ) + 2) := by linarith
  have hrpow1 : ((G.m : ℝ) + 2) ^ (1 + (K_nat : ℝ) / (rOf G.m : ℝ)) ≤
      ((G.m : ℝ) + 2) ^ (1 + K_nat) := by
    have hdiv : (K_nat : ℝ) / (rOf G.m : ℝ) ≤ (K_nat : ℝ) := by
      have hr1_r : (1 : ℝ) ≤ (rOf G.m : ℝ) := by exact_mod_cast hr1
      exact div_le_self hK_pos.le hr1_r
    have hexp : 1 + (K_nat : ℝ) / (rOf G.m : ℝ) ≤ ((1 + K_nat : ℕ) : ℝ) := by
      push_cast; linarith
    calc ((G.m : ℝ) + 2) ^ (1 + (K_nat : ℝ) / (rOf G.m : ℝ))
        ≤ ((G.m : ℝ) + 2) ^ (((1 + K_nat : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hm2_ge1 hexp
      _ = ((G.m : ℝ) + 2) ^ (1 + K_nat) := Real.rpow_natCast _ _
  have hrpow2 : Real.log ((G.m : ℝ) + 2) ^ ((K_nat : ℝ) * (rOf G.m : ℝ) ^ 2) ≤
      ((G.m : ℝ) + 2) ^ (5 * K_nat) := by
    rw [Real.rpow_def_of_pos hx_pos]
    have h5 := rOf_sq_mul_log_log_le hm
    have hexp : Real.log (Real.log ((G.m : ℝ) + 2)) * ((K_nat : ℝ) * (rOf G.m : ℝ) ^ 2) ≤
        ((5 * K_nat : ℕ) : ℝ) * Real.log ((G.m : ℝ) + 2) := by
      have hmul := mul_le_mul_of_nonneg_left h5 hK_pos.le
      push_cast
      linarith
    calc Real.exp (Real.log (Real.log ((G.m : ℝ) + 2)) * ((K_nat : ℝ) * (rOf G.m : ℝ) ^ 2))
        ≤ Real.exp (((5 * K_nat : ℕ) : ℝ) * Real.log ((G.m : ℝ) + 2)) :=
          Real.exp_le_exp.mpr hexp
      _ = Real.exp (Real.log ((G.m : ℝ) + 2) * ((5 * K_nat : ℕ) : ℝ)) := by ring_nf
      _ = ((G.m : ℝ) + 2) ^ (((5 * K_nat : ℕ) : ℝ)) := (Real.rpow_def_of_pos hm2_pos _).symm
      _ = ((G.m : ℝ) + 2) ^ (5 * K_nat) := Real.rpow_natCast _ _
  have hprod : ((G.m : ℝ) + 2) ^ (1 + (K_nat : ℝ) / (rOf G.m : ℝ)) *
      Real.log ((G.m : ℝ) + 2) ^ ((K_nat : ℝ) * (rOf G.m : ℝ) ^ 2) ≤
      ((G.m : ℝ) + 2) ^ (6 * K_nat + 1) := by
    calc ((G.m : ℝ) + 2) ^ (1 + (K_nat : ℝ) / (rOf G.m : ℝ)) *
          Real.log ((G.m : ℝ) + 2) ^ ((K_nat : ℝ) * (rOf G.m : ℝ) ^ 2)
        ≤ ((G.m : ℝ) + 2) ^ (1 + K_nat) * ((G.m : ℝ) + 2) ^ (5 * K_nat) :=
          mul_le_mul hrpow1 hrpow2 (by positivity) (by positivity)
      _ = ((G.m : ℝ) + 2) ^ (6 * K_nat + 1) := by
          rw [← pow_add, show 1 + K_nat + 5 * K_nat = 6 * K_nat + 1 by omega]
  have hdiv200 : ∀ a : ℝ, a / (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2 = a * 200 ^ 2 := by
    intro a; push_cast; ring
  rw [hK_eq, hdiv200] at hcost
  have hB_r : (G.m : ℝ) + 2 ≤ (B : ℝ) := by exact_mod_cast (by omega : G.m + 2 ≤ B)
  have hn_r : (G.n : ℝ) ≤ (B : ℝ) := by exact_mod_cast (by omega : G.n ≤ B)
  have hB_ge1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (by omega : 1 ≤ B)
  have hB_pow_ge : (B : ℝ) ≤ (B : ℝ) ^ (6 * K_nat + 1) := by
    have h1 : (B : ℝ) ^ 1 ≤ (B : ℝ) ^ (6 * K_nat + 1) :=
      pow_le_pow_right₀ hB_ge1 (by omega)
    simpa using h1
  have hreal_bound : (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) : ℝ) ≤
      ((2 * K_nat * 200 ^ 2 : ℕ) : ℝ) * (B : ℝ) ^ (6 * K_nat + 1) := by
    have h1 : ((G.m : ℝ) + 2) ^ (6 * K_nat + 1) ≤ (B : ℝ) ^ (6 * K_nat + 1) :=
      pow_le_pow_left₀ (by positivity) hB_r _
    have h2 : (G.n : ℝ) + ((G.m : ℝ) + 2) ^ (6 * K_nat + 1) * 200 ^ 2 ≤
        2 * 200 ^ 2 * (B : ℝ) ^ (6 * K_nat + 1) := by
      have hGn_le_pow : (G.n : ℝ) ≤ (B : ℝ) ^ (6 * K_nat + 1) := le_trans hn_r hB_pow_ge
      have hpow_nn : (0 : ℝ) ≤ (B : ℝ) ^ (6 * K_nat + 1) := by positivity
      linarith
    have h3 : (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) : ℝ) ≤
        (K_nat : ℝ) * ((G.n : ℝ) + ((G.m : ℝ) + 2) ^ (6 * K_nat + 1) * 200 ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_right hprod (by positivity : (0 : ℝ) ≤ 200 ^ 2)
      have hadd := add_le_add_right hmul (G.n : ℝ)
      exact le_trans hcost (mul_le_mul_of_nonneg_left hadd hK_pos.le)
    calc (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) : ℝ)
        ≤ (K_nat : ℝ) * (2 * 200 ^ 2 * (B : ℝ) ^ (6 * K_nat + 1)) :=
          le_trans h3 (mul_le_mul_of_nonneg_left h2 hK_pos.le)
      _ = ((2 * K_nat * 200 ^ 2 : ℕ) : ℝ) * (B : ℝ) ^ (6 * K_nat + 1) := by
          push_cast; ring
  have hnat_bound : totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) ≤
      (2 * K_nat * 200 ^ 2) * B ^ (6 * K_nat + 1) := by
    exact_mod_cast hreal_bound
  have hconst_le : 2 * K_nat * 200 ^ 2 ≤ B ^ (Nat.log 2 (2 * K_nat * 200 ^ 2) + 1) :=
    le_trans (Nat.lt_pow_succ_log_self (by decide) _).le (Nat.pow_le_pow_left hB2 _)
  calc totalTimeRaw ParamConfig.default G.n G.m (rOf G.m)
      ≤ (2 * K_nat * 200 ^ 2) * B ^ (6 * K_nat + 1) := hnat_bound
    _ ≤ B ^ (Nat.log 2 (2 * K_nat * 200 ^ 2) + 1) * B ^ (6 * K_nat + 1) :=
        Nat.mul_le_mul_right _ hconst_le
    _ = B ^ (6 * K_nat + Nat.log 2 (2 * K_nat * 200 ^ 2) + 2) := by
        rw [← pow_add, show Nat.log 2 (2 * K_nat * 200 ^ 2) + 1 + (6 * K_nat + 1) =
          6 * K_nat + Nat.log 2 (2 * K_nat * 200 ^ 2) + 2 by omega]

private lemma one_le_decompEntryWordC (C_sp : ℕ) : 1 ≤ decompEntryWordC C_sp := by
  unfold decompEntryWordC
  exact le_trans (by decide : 1 ≤ 10) (Nat.le_add_left 10 _)

/-- Word-size headroom for the entry call:
`h + outerDecompSpace C_sp G.n G.m (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m))`
fits strictly inside `2 ^ wordSize (decompEntryWordC C_sp) (G.encode ++ [1, 200, rOf G.m])`. -/
theorem decompEntry_space_lt_two_pow_wordSize (C_sp : ℕ) {G : Graph}
    (_hv : G.IsValid) (_hl : G.IsLoopless) (hm : thresholdB1 envelopeCr ≤ G.m) :
    let inp := G.encode ++ [1, 200, rOf G.m]
    let h := inp.length + G.n
    h + outerDecompSpace C_sp G.n G.m (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m)) <
      2 ^ wordSize (decompEntryWordC C_sp) inp := by
  intro inp h
  set B := inp.length + inp.foldr max 0 + 2
  have hK_pos : 0 < envelopeK ParamConfig.default := envelopeK_pos ParamConfig.default
  have hcost_le : totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) ≤
      B ^ (6 * envelopeKNat ParamConfig.default +
        Nat.log 2 (2 * envelopeKNat ParamConfig.default * 200 ^ 2) + 2) :=
    totalTimeRaw_le_pow_aux rfl hK_pos hm
  have hwc_eq :
      decompEntryWordC C_sp =
        (6 * envelopeKNat ParamConfig.default +
          Nat.log 2 (2 * envelopeKNat ParamConfig.default * 200 ^ 2) + 2) +
        6 + (Nat.log 2 (2 * C_sp + 3) + 1) + 1 := by
    unfold decompEntryWordC
    generalize envelopeKNat ParamConfig.default = K_nat
    omega
  set e₁ := 6 * envelopeKNat ParamConfig.default +
    Nat.log 2 (2 * envelopeKNat ParamConfig.default * 200 ^ 2) + 2
  have hlen_inp : inp.length = 2 * G.m + 5 := by
    simp only [inp, List.length_append, graph_encode_length, List.length_cons, List.length_nil]
    omega
  have hn_le_max : G.n ≤ inp.foldr max 0 := by
    apply mem_le_foldr_max
    simp [inp, Graph.encode]
  have h200_le_max : 200 ≤ inp.foldr max 0 := by
    apply mem_le_foldr_max
    simp [inp]
  have hB2 : 2 ≤ B := by dsimp only [B]; omega
  have hB1 : 1 ≤ B := by omega
  have hh_le_B : h ≤ B := by dsimp only [h, B]; omega
  have hnm_le_B : G.n + G.m + 3 ≤ B := by dsimp only [B]; omega
  have hBe1_pos : 1 ≤ B ^ e₁ := Nat.one_le_pow e₁ B hB1
  have hspace_le :
      outerDecompSpace C_sp G.n G.m (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m)) ≤
        (2 * C_sp) * B ^ (e₁ + 6) := by
    unfold outerDecompSpace
    have h1 : totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) + 1 ≤ 2 * B ^ e₁ := by omega
    have h2 : (G.n + G.m + 3) ^ 6 ≤ B ^ 6 := Nat.pow_le_pow_left hnm_le_B 6
    calc C_sp * (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) + 1) * (G.n + G.m + 3) ^ 6
        ≤ C_sp * (2 * B ^ e₁) * B ^ 6 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left C_sp h1) h2
      _ = (2 * C_sp) * (B ^ e₁ * B ^ 6) := by ring
      _ = (2 * C_sp) * B ^ (e₁ + 6) := by rw [← pow_add]
  have hB_le_pow : B ≤ B ^ (e₁ + 6) := by
    calc B = B ^ 1 := (pow_one B).symm
      _ ≤ B ^ (e₁ + 6) := Nat.pow_le_pow_right hB1 (by omega)
  have htot_le :
      h + outerDecompSpace C_sp G.n G.m (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m)) ≤
        (2 * C_sp + 3) * B ^ (e₁ + 6) := by
    have h1 : h + (2 * C_sp) * B ^ (e₁ + 6) ≤ B ^ (e₁ + 6) + (2 * C_sp) * B ^ (e₁ + 6) :=
      Nat.add_le_add_right (le_trans hh_le_B hB_le_pow) _
    have h2 : B ^ (e₁ + 6) + (2 * C_sp) * B ^ (e₁ + 6) = (2 * C_sp + 1) * B ^ (e₁ + 6) := by ring
    have h3 : (2 * C_sp + 1) * B ^ (e₁ + 6) ≤ (2 * C_sp + 3) * B ^ (e₁ + 6) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hc_le : 2 * C_sp + 3 ≤ B ^ (Nat.log 2 (2 * C_sp + 3) + 1) :=
    le_trans (Nat.lt_pow_succ_log_self (by decide) _).le (Nat.pow_le_pow_left hB2 _)
  have hpow_tot :
      h + outerDecompSpace C_sp G.n G.m (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m)) ≤
        B ^ (decompEntryWordC C_sp) := by
    calc h + outerDecompSpace C_sp G.n G.m (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m))
        ≤ (2 * C_sp + 3) * B ^ (e₁ + 6) := htot_le
      _ ≤ B ^ (Nat.log 2 (2 * C_sp + 3) + 1) * B ^ (e₁ + 6) := Nat.mul_le_mul_right _ hc_le
      _ = B ^ (e₁ + 6 + (Nat.log 2 (2 * C_sp + 3) + 1)) := by
          rw [← pow_add, Nat.add_comm]
      _ ≤ B ^ (decompEntryWordC C_sp) := by
          apply Nat.pow_le_pow_right hB1
          rw [hwc_eq]
          exact Nat.le_succ _
  exact lt_of_le_of_lt hpow_tot (pow_lt_two_pow_wordSize (one_le_decompEntryWordC C_sp) inp)

/-- `IsExpanderDecomposition` is monotone as the conductance lower bound decreases. -/
private lemma isExpanderDecomposition_mono_phi {G : Graph} {ε φ₁ φ₂ : ℝ} {label : List ℕ}
    (h : IsExpanderDecomposition G ε φ₂ label) (hφ : φ₁ ≤ φ₂) :
    IsExpanderDecomposition G ε φ₁ label := by
  refine ⟨h.1, fun X hX S hSX hSne hSneX => ?_, h.2.2⟩
  have hmin_nn : 0 ≤ min (G.volIn X S : ℝ) (G.volIn X (X \ S)) := by
    exact le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact le_trans (mul_le_mul_of_nonneg_right hφ hmin_nn) (h.2.1 X hX S hSX hSne hSneX)

private lemma decompEntry_conductance (K : ℕ) {G : Graph}
    (hm : thresholdB1 envelopeCr ≤ G.m)
    {labels : List ℕ}
    (hspec : IsExpanderDecomposition G (1 / 200) (phiOut ParamConfig.default G.m (rOf G.m)) labels) :
    IsExpanderDecomposition G (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ))
      ((((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) /
        (decompEntryK K * Real.log ((G.m : ℝ) + 2) ^ (decompEntryK K * (rOf G.m : ℝ) ^ 2)))
      labels := by
  have hphi := phiOut_ge_used ParamConfig.default hm
  have hK0_pos : 0 < envelopeK ParamConfig.default := envelopeK_pos ParamConfig.default
  have hK_ge : envelopeK ParamConfig.default ≤ decompEntryK K := by
    unfold decompEntryK envelopeK
    exact_mod_cast (by
      have : envelopeKNat ParamConfig.default ≤ (K + 1) * (envelopeKNat ParamConfig.default + 120) := by
        nlinarith
      exact this)
  have hlog2 : 2 ≤ Real.log ((G.m : ℝ) + 2) := two_le_log_of_thresholdB1 hm
  have hlog1 : 1 ≤ Real.log ((G.m : ℝ) + 2) := by linarith
  have hlog_pos : 0 < Real.log ((G.m : ℝ) + 2) := by linarith
  have hrpow_le :
      Real.log ((G.m : ℝ) + 2) ^ (envelopeK ParamConfig.default * (rOf G.m : ℝ) ^ 2) ≤
      Real.log ((G.m : ℝ) + 2) ^ (decompEntryK K * (rOf G.m : ℝ) ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 (mul_le_mul_of_nonneg_right hK_ge (by positivity))
  have hden_pos : 0 < envelopeK ParamConfig.default *
      Real.log ((G.m : ℝ) + 2) ^ (envelopeK ParamConfig.default * (rOf G.m : ℝ) ^ 2) :=
    mul_pos hK0_pos (Real.rpow_pos_of_pos hlog_pos _)
  have hden_le :
      envelopeK ParamConfig.default *
        Real.log ((G.m : ℝ) + 2) ^ (envelopeK ParamConfig.default * (rOf G.m : ℝ) ^ 2) ≤
      decompEntryK K *
        Real.log ((G.m : ℝ) + 2) ^ (decompEntryK K * (rOf G.m : ℝ) ^ 2) :=
    mul_le_mul hK_ge hrpow_le (Real.rpow_pos_of_pos hlog_pos _).le (le_trans hK0_pos.le hK_ge)
  have hphi_le :
      (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) /
        (decompEntryK K * Real.log ((G.m : ℝ) + 2) ^ (decompEntryK K * (rOf G.m : ℝ) ^ 2)) ≤
      phiOut ParamConfig.default G.m (rOf G.m) :=
    le_trans (div_le_div_of_nonneg_left (by positivity) hden_pos hden_le) hphi
  have hspec' : IsExpanderDecomposition G (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ))
      (phiOut ParamConfig.default G.m (rOf G.m)) labels := by
    simpa using hspec
  exact isExpanderDecomposition_mono_phi hspec' hphi_le

private lemma decompEntry_cost_le_used (K : ℕ) {G : Graph} {cost : ℕ}
    (hm : thresholdB1 envelopeCr ≤ G.m)
    (hcost : cost ≤ K * totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) + K + 28 * G.n + 80) :
    (cost : ℝ) ≤ decompEntryK K * (G.n + ((G.m : ℝ) + 2) ^ (1 + decompEntryK K / rOf G.m) *
      Real.log ((G.m : ℝ) + 2) ^ (decompEntryK K * (rOf G.m : ℝ) ^ 2) /
        (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2) := by
  set K₀ : ℝ := envelopeK ParamConfig.default
  set Kf : ℝ := decompEntryK K
  set T₀ : ℝ := G.n + ((G.m : ℝ) + 2) ^ (1 + K₀ / rOf G.m) *
    Real.log ((G.m : ℝ) + 2) ^ (K₀ * (rOf G.m : ℝ) ^ 2) /
      (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2
  set Tf : ℝ := G.n + ((G.m : ℝ) + 2) ^ (1 + Kf / rOf G.m) *
    Real.log ((G.m : ℝ) + 2) ^ (Kf * (rOf G.m : ℝ) ^ 2) /
      (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2
  have hK0_pos : 0 < K₀ := envelopeK_pos ParamConfig.default
  have hK_ge : K₀ ≤ Kf := by
    dsimp only [K₀, Kf, decompEntryK, envelopeK]
    exact_mod_cast (by
      have : envelopeKNat ParamConfig.default ≤ (K + 1) * (envelopeKNat ParamConfig.default + 120) := by
        nlinarith
      exact this)
  have hlog2 : 2 ≤ Real.log ((G.m : ℝ) + 2) := two_le_log_of_thresholdB1 hm
  have hlog1 : 1 ≤ Real.log ((G.m : ℝ) + 2) := by linarith
  have hm2_ge1 : (1 : ℝ) ≤ (G.m : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (G.m : ℝ) := Nat.cast_nonneg _
    linarith
  have hT0_ge1 : 1 ≤ T₀ := by
    have h1 : (1 : ℝ) ≤ ((G.m : ℝ) + 2) ^ (1 + K₀ / rOf G.m) :=
      Real.one_le_rpow hm2_ge1 (by positivity)
    have h2 : (1 : ℝ) ≤ Real.log ((G.m : ℝ) + 2) ^ (K₀ * (rOf G.m : ℝ) ^ 2) :=
      Real.one_le_rpow hlog1 (by positivity)
    have h3 : (1 : ℝ) ≤ ((G.m : ℝ) + 2) ^ (1 + K₀ / rOf G.m) *
        Real.log ((G.m : ℝ) + 2) ^ (K₀ * (rOf G.m : ℝ) ^ 2) /
          (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2 := by
      have hprod : (1 : ℝ) ≤ ((G.m : ℝ) + 2) ^ (1 + K₀ / rOf G.m) *
          Real.log ((G.m : ℝ) + 2) ^ (K₀ * (rOf G.m : ℝ) ^ 2) := by nlinarith
      have hrew : ((G.m : ℝ) + 2) ^ (1 + K₀ / rOf G.m) *
          Real.log ((G.m : ℝ) + 2) ^ (K₀ * (rOf G.m : ℝ) ^ 2) /
            (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2 =
          ((G.m : ℝ) + 2) ^ (1 + K₀ / rOf G.m) *
          Real.log ((G.m : ℝ) + 2) ^ (K₀ * (rOf G.m : ℝ) ^ 2) * 200 ^ 2 := by
        push_cast; ring
      rw [hrew]; nlinarith
    have hn_nn : (0 : ℝ) ≤ (G.n : ℝ) := by positivity
    dsimp only [T₀]; linarith
  have hGn_le_T0 : (G.n : ℝ) ≤ T₀ := by
    have hpos : 0 ≤ ((G.m : ℝ) + 2) ^ (1 + K₀ / rOf G.m) *
        Real.log ((G.m : ℝ) + 2) ^ (K₀ * (rOf G.m : ℝ) ^ 2) /
          (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2 := by positivity
    dsimp only [T₀]; linarith
  have hT0_le_Tf : T₀ ≤ Tf := by
    have h1 : ((G.m : ℝ) + 2) ^ (1 + K₀ / rOf G.m) ≤ ((G.m : ℝ) + 2) ^ (1 + Kf / rOf G.m) :=
      Real.rpow_le_rpow_of_exponent_le hm2_ge1
        (add_le_add_right (div_le_div_of_nonneg_right hK_ge (by positivity)) 1)
    have h2 : Real.log ((G.m : ℝ) + 2) ^ (K₀ * (rOf G.m : ℝ) ^ 2) ≤
        Real.log ((G.m : ℝ) + 2) ^ (Kf * (rOf G.m : ℝ) ^ 2) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (mul_le_mul_of_nonneg_right hK_ge (by positivity))
    have hprod : ((G.m : ℝ) + 2) ^ (1 + K₀ / rOf G.m) *
        Real.log ((G.m : ℝ) + 2) ^ (K₀ * (rOf G.m : ℝ) ^ 2) ≤
        ((G.m : ℝ) + 2) ^ (1 + Kf / rOf G.m) *
        Real.log ((G.m : ℝ) + 2) ^ (Kf * (rOf G.m : ℝ) ^ 2) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have hdiv := div_le_div_of_nonneg_right hprod (by positivity : (0 : ℝ) ≤ (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2)
    dsimp only [T₀, Tf]; linarith
  have hmodel : (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) : ℝ) ≤ K₀ * T₀ :=
    totalTimeRaw_le_used ParamConfig.default G.n hm
  have hcost_r : (cost : ℝ) ≤
      (K : ℝ) * (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) : ℝ) +
        (K : ℝ) + 28 * (G.n : ℝ) + 80 := by
    exact_mod_cast hcost
  have hcoeff : (K : ℝ) * K₀ + (K : ℝ) + 28 + 80 ≤ Kf := by
    dsimp only [Kf, K₀, decompEntryK, envelopeK]
    push_cast
    nlinarith
  calc (cost : ℝ)
      ≤ (K : ℝ) * (K₀ * T₀) + (K : ℝ) * T₀ + 28 * T₀ + 80 * T₀ := by
        have h1 : (K : ℝ) * (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) : ℝ) ≤
            (K : ℝ) * (K₀ * T₀) :=
          mul_le_mul_of_nonneg_left hmodel (by positivity)
        have h2 : (K : ℝ) ≤ (K : ℝ) * T₀ := by nlinarith
        linarith
    _ = ((K : ℝ) * K₀ + (K : ℝ) + 28 + 80) * T₀ := by ring
    _ ≤ Kf * T₀ := mul_le_mul_of_nonneg_right hcoeff (by linarith)
    _ ≤ Kf * Tf := mul_le_mul_of_nonneg_left hT0_le_Tf (by linarith)

/-! ## 3. Verification of `decompEntryCopyStmt` and `decompEntryProc` -/

private lemma decompEntryCopy_triple {w n outAddr : ℕ}
    (p : Program) (mem : ℕ → ℕ) (labels : List ℕ) (st₀ : State)
    (hlen : labels.length = n) (hlab : ListAt mem outAddr labels)
    (hout_pos : 0 < outAddr) (hout_w : outAddr + n < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr1 : st₀.regs 1 = n) (hr4 : st₀.regs 4 = outAddr) (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) decompEntryCopyStmt
      (normalPost fun st' =>
        st'.regs 1 = n ∧
        ListAt st'.mem 0 labels)
      (fun _ => 26 * n + 20) := by
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 6 = j ∧
    st.regs 1 = n ∧
    st.regs 4 = outAddr ∧
    (∀ t (ht : t < j) (htn : t < n), st.mem t = labels[t]'(by omega)) ∧
    (∀ t (htj : j ≤ t) (htn : t < n), st.mem (outAddr + t) = labels[t]'(by omega))
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 6) (lo := .const 0) (hi := .reg 1)
    (body := seqStmts [
      .assign 7 (.load (.bin .add (.reg 4) (.reg 6))),
      .store (.reg 6) (.reg 7)])
    (P := fun st => st = st₀) (Inv := Inv) 14 0 n (Nat.zero_le n) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega), by simp,
        by dsimp only; rw [Function.update_of_ne (by decide), hr1],
        by dsimp only; rw [Function.update_of_ne (by decide), hr4],
        fun t ht _ => by omega,
        fun t _ htn => by rw [hmem]; exact hlab t (by omega)⟩)
    (fun _ st _ _ hInv => hInv.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq (v := n) hInv.2.1)
    (fun j _ hjlt => by
      intro st ω ⟨hj, h1, h4, hdone, hrem⟩
      have hsrc : st.mem (outAddr + j) = labels[j]'(by omega) := hrem j le_rfl hjlt
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := labels[j]'(by omega))
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq h4) (Expr.eval_reg_of_eq hj) (by omega)) hsrc) ?_
      refine runs_store_le (x := j) (v := labels[j]'(by omega))
        (Expr.eval_reg_of_eq (v := j) (by dsimp only; rw [Function.update_of_ne (by decide), hj]))
        (Expr.eval_reg_of_eq (v := labels[j]'(by omega)) (by simp)) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp,
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), h1],
        by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), h4],
        ?_, ?_⟩,
        by dsimp only; rw [Function.update_of_ne (by decide), hj]⟩
      · intro t ht htn
        dsimp only
        by_cases htj : t = j
        · subst t; rw [Function.update_self]
        · rw [Function.update_of_ne (by omega)]; exact hdone t (by omega) htn
      · intro t htj htn
        dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hrem t (by omega) htn)
  dsimp only [decompEntryCopyStmt]
  refine hloop.conseq (fun _ h => h) ?_ (fun _ _ => by simp only [Expr.size]; omega)
  rintro (_ | v) st' hInv
  · rcases hInv with ⟨_, h1, _, hdone, _⟩
    refine ⟨h1, fun t ht => ?_⟩
    simpa using hdone t (by omega) (by omega)
  · exact hInv.elim

/-- Top-level `RunsTo` theorem for any program `p` with `decompEntryProc bOuter` at index `0` and
an outer decomposition procedure at index `bOuter` meeting `outerDecompEntryContract K C_sp w`. -/
theorem decompEntry_runsTo {p : Program} {bOuter K C_sp : ℕ}
    (h0 : p.HasAt 0 [decompEntryProc bOuter])
    (hOuter : ∀ w, MeetsContract w p bOuter (outerDecompEntryContract K C_sp w))
    {G : Graph} (hv : G.IsValid) (hl : G.IsLoopless) (hm : thresholdB1 envelopeCr ≤ G.m)
    (ω : ℕ → Bool) :
    ∃ out cost,
      RunsTo (wordSize (decompEntryWordC C_sp) (G.encode ++ [1, 200, rOf G.m])) p
        (G.encode ++ [1, 200, rOf G.m]) ω out cost ∧
      IsExpanderDecomposition G (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ))
        ((((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) /
          (decompEntryK K * Real.log ((G.m : ℝ) + 2) ^ (decompEntryK K * (rOf G.m : ℝ) ^ 2)))
        out ∧
      (cost : ℝ) ≤ decompEntryK K * (G.n + ((G.m : ℝ) + 2) ^ (1 + decompEntryK K / rOf G.m) *
        Real.log ((G.m : ℝ) + 2) ^ (decompEntryK K * (rOf G.m : ℝ) ^ 2) /
          (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2) := by
  have hEntry : p.procs[0]? = some (decompEntryProc bOuter) := by simpa using h0 0 (by simp)
  set inp := G.encode ++ [1, 200, rOf G.m] with hinp_def
  set w := wordSize (decompEntryWordC C_sp) inp with hw_def
  have hlen_inp : inp.length = 2 * G.m + 5 := by
    simp only [inp, List.length_append, graph_encode_length, List.length_cons, List.length_nil]
    omega
  have hwc_pos : 1 ≤ decompEntryWordC C_sp := one_le_decompEntryWordC C_sp
  have hspace_lt :
      inp.length + G.n +
        outerDecompSpace C_sp G.n G.m (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m)) <
          2 ^ w :=
    decompEntry_space_lt_two_pow_wordSize C_sp hv hl hm
  have h16 : 16 < 2 ^ w := by
    have hpow : (inp.length + inp.foldr max 0 + 2) ^ decompEntryWordC C_sp < 2 ^ w :=
      pow_lt_two_pow_wordSize hwc_pos inp
    have h1 : 16 ≤ (inp.length + inp.foldr max 0 + 2) ^ decompEntryWordC C_sp := by
      have h200 : 200 ≤ inp.foldr max 0 := mem_le_foldr_max (by simp [inp])
      have hbase : 16 ≤ inp.length + inp.foldr max 0 + 2 := by omega
      exact le_trans hbase (Nat.le_self_pow (by omega) _)
    exact lt_of_le_of_lt h1 hpow
  have hG_at : GraphAt (initMem inp) 0 G := graphAt_initMem_encode G [1, 200, rOf G.m]
  have hmem0 : initMem inp 0 = G.n := graphAt_n hG_at
  have hmem_r : initMem inp (inp.length - 1) = rOf G.m := by
    have hidx : inp.length - 1 = G.encode.length + 2 := by
      rw [hlen_inp, graph_encode_length]; omega
    rw [hidx]
    simp only [inp, initMem, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : G.encode.length ≤ G.encode.length + 2)]
    simp
  have hr_lt : rOf G.m < 2 ^ w :=
    lt_two_pow_wordSize_of_mem hwc_pos (by simp [inp])
  have hreadG : readGraph (initMem inp) 0 = G := readGraph_eq_of_graphAt hG_at
  have hrun : ∃ st' c labels,
      Runs w p ω (decompEntryProc bOuter) (startState [inp.length] (initMem inp) 0)
        (.returned G.n) st' c ∧
      ListAt st'.mem 0 labels ∧
      IsExpanderDecomposition G (1 / 200) (phiOut ParamConfig.default G.m (rOf G.m)) labels ∧
      c ≤ K * totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) + K + 28 * G.n + 78 := by
    suffices h : ∃ o st' c,
        Runs w p ω (decompEntryProc bOuter) (startState [inp.length] (initMem inp) 0) o st' c ∧
        (o = .returned G.n ∧ ∃ labels : List ℕ, ListAt st'.mem 0 labels ∧
          IsExpanderDecomposition G (1 / 200) (phiOut ParamConfig.default G.m (rOf G.m)) labels) ∧
        c ≤ K * totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) + K + 28 * G.n + 78 by
      rcases h with ⟨o, st', c, hr, ⟨rfl, labels, hlist, hspec⟩, hc⟩
      exact ⟨st', c, labels, hr, hlist, hspec, hc⟩
    refine runs_start_le ?_
    dsimp only [decompEntryProc, seqStmts]
    refine runs_seq_assign_le (v := G.n)
      (Expr.eval_load_of_eq (Expr.eval_const (by omega)) hmem0) ?_
    refine runs_seq_assign_le (v := rOf G.m)
      (Expr.eval_load_of_eq
        (Expr.eval_sub
          (Expr.eval_reg_of_eq (v := inp.length) (by
            dsimp only; rw [Function.update_of_ne (by decide)]; simp [startState]))
          (Expr.eval_const (by omega)) (by omega))
        hmem_r) ?_
    refine runs_seq_assign_le (v := inp.length)
      (Expr.eval_reg_of_eq (v := inp.length) (by
        dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        simp [startState])) ?_
    refine runs_seq_assign_le (v := inp.length + G.n)
      (Expr.eval_add
        (Expr.eval_reg_of_eq (v := inp.length) (by simp))
        (Expr.eval_reg_of_eq (v := G.n) (by
          dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_self]))
        (by omega)) ?_
    refine runs_seq_call_le (C := outerDecompEntryContract K C_sp w)
      (vs := [0, rOf G.m, inp.length, inp.length + G.n])
      (hOuter w) ?_ ?_ ?_ ?_
    · simp [evalArgs, Expr.eval, show (0 : ℕ) < 2 ^ w by omega]
    · intro v hv_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_mem
      rcases hv_mem with rfl | rfl | rfl | rfl <;> omega
    · refine ⟨0, rOf G.m, inp.length, inp.length + G.n, G, rfl, hG_at, hv, hl, hm, rfl,
        fun a ha => MinCostFlow.ExpanderDecomp.zeroFrom_initMem inp a (by omega),
        by omega, le_rfl, Or.inr (by omega), hspace_lt, h16⟩
    · intro v mem1 pos1 hpost
      simp only [outerDecompEntryContract, List.getD_cons_zero, List.getD_cons_succ, startState,
        hreadG] at hpost
      rcases hpost with ⟨labels, hlist_labels, hspec_labels⟩
      have hlab_len : labels.length = G.n := hspec_labels.1
      let st1 : State :=
        { mem := mem1,
          regs := Function.update
            (Function.update (Function.update (Function.update (Function.update
              (startState [inp.length] (initMem inp) 0).regs 1 G.n) 2 (rOf G.m)) 4 inp.length)
              5 (inp.length + G.n))
            3 v,
          pos := pos1 }
      refine runs_seq_triple_le
        (decompEntryCopy_triple p mem1 labels st1 hlab_len hlist_labels
          (by omega) (by omega) h16
          (by dsimp only [st1]
              rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_self])
          (by dsimp only [st1]
              rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_self])
          rfl) rfl ?_
      intro st2 ⟨hr1_2, hlist2⟩
      refine runs_ret_le (Expr.eval_reg_of_eq hr1_2) ⟨rfl, labels, hlist2, hspec_labels⟩ ?_
      simp only [outerDecompEntryContract, List.getD_cons_zero, argsSize, Expr.size, startState,
        hreadG]
      omega
  rcases hrun with ⟨st', c, labels, hruns, hlist, hspec, hc⟩
  refine ⟨labels, c + 2,
    runsTo_of_entry hEntry (by omega) hruns hspec.1 hlist,
    decompEntry_conductance K hm hspec,
    decompEntry_cost_le_used K hm (by omega)⟩

/-- **Main theorem (`ExpanderDecompositionUsed` modulo the outer procedure contract):**
if a program `p` has `decompEntryProc bOuter` at index `0` and an outer decomposition procedure at
index `bOuter` meeting `outerDecompEntryContract K C_sp w` for every word size `w`, then
`ExpanderDecompositionUsed` holds. -/
theorem expanderDecompositionUsed_of_outerContract {p : Program} {bOuter K C_sp : ℕ}
    (h0 : p.HasAt 0 [decompEntryProc bOuter])
    (hOuter : ∀ w, MeetsContract w p bOuter (outerDecompEntryContract K C_sp w)) :
    ExpanderDecompositionUsed := by
  refine ⟨decompEntryK K, envelopeCr, p, decompEntryWordC C_sp, ?_, envelopeCr_pos,
    fun G hv hl hm ω => decompEntry_runsTo h0 hOuter hv hl hm ω⟩
  unfold decompEntryK
  exact_mod_cast (by
    have : 0 < (K + 1) * (envelopeKNat ParamConfig.default + 120) := by positivity
    exact this)

/-- Convenience wrapper for a relocatable list of outer procedures `outerProcs` placed at index `1`:
assembles `P := ⟨decompEntryProc 1 :: outerProcs⟩` and proves `ExpanderDecompositionUsed`. -/
theorem expanderDecompositionUsed_of_outerProcs (outerProcs : List Stmt) (K C_sp : ℕ)
    (hOuter : ∀ w (p : Program), p.HasAt 1 outerProcs →
      MeetsContract w p 1 (outerDecompEntryContract K C_sp w)) :
    ExpanderDecompositionUsed := by
  let P : Program := ⟨decompEntryProc 1 :: outerProcs⟩
  have h0 : P.HasAt 0 [decompEntryProc 1] := by
    intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0; simp [P]
  have h1 : P.HasAt 1 outerProcs := by
    intro i hi
    simp [P, hi, Nat.add_comm]
  exact expanderDecompositionUsed_of_outerContract h0 (fun w => hOuter w P h1)

end MinCostFlow.ExpanderDecomp
