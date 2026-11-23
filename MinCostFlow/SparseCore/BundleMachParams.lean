module

public import MinCostFlow.SparseCore.BundleCoreParams
import Mathlib.Tactic.Linarith

/-!
# Parameters of Lemma 5.17 for the machine cost

`bundleCoreParamsMach E` is `bundleCoreParams E` with the cost constant and the polylog exponent
raised so that the cost clauses of `IsSpecOrdRestart` hold for the machine cost `machCost`
(`Chain/BundleRestartMachSpec.lean`): `c_T` becomes `65 c_T + 18000` and `p_T` becomes
`max 6 (p_T + 3)`.
The machine cost multiplies the model cost by `bundleLogFactor M N ≤ 16 log² (M + N + 2)` and
charges bucket-spanner initializations and updates via `spanInitBound` and `spanBatchCharge`,
giving the factor `65` and up to three more powers of the logarithm. The LSF initializations carry
two more factors `bundleLogFactor`, giving the term `16384 M log⁶`. Thus `max 6 (p_T + 3)` covers
all terms for every `E : SparseCoreEnv` (including `p_s_hi = p_t_hi = 0`, where `p_T + 4 = 5 < 6`,
while giving `6` on `concreteEnv` where `p_s_hi = p_t_hi = 1`). All other parameters are those of
`bundleCoreParams E`, and every constant is free of the input.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

/-- The parameters of Lemma 5.17 for `sparseCoreBundleRestartToolMachWith` with spanner charge
constant `spanConst`. -/
noncomputable def bundleCoreParamsMachWith (E : SparseCoreEnv) (spanConst : ℕ) :
    MinCostFlow.Chain.SparseCoreParams :=
  { bundleCoreParams E with
    c_T := ((max 1 spanConst : ℕ) : ℝ) * (65 * (bundleCoreParams E).c_T + 18000)
    p_T := max 6 ((bundleCoreParams E).p_T + 3) }

/-- The parameters of Lemma 5.17 for `sparseCoreBundleRestartToolMach` at unit spanner charge
constant `spanConst = 1`. -/
noncomputable def bundleCoreParamsMach (E : SparseCoreEnv) : MinCostFlow.Chain.SparseCoreParams :=
  bundleCoreParamsMachWith E 1

lemma bundleCoreParamsMachWith_c_T (E : SparseCoreEnv) (spanConst : ℕ) :
    (bundleCoreParamsMachWith E spanConst).c_T =
      ((max 1 spanConst : ℕ) : ℝ) *
        (65 * (37810 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi + E.c_n) + 18000) := rfl

lemma bundleCoreParamsMachWith_p_T (E : SparseCoreEnv) (spanConst : ℕ) :
    (bundleCoreParamsMachWith E spanConst).p_T = max 6 (max E.p_s_hi E.p_t_hi + 4) := rfl

lemma bundleCoreParamsMach_c_T (E : SparseCoreEnv) :
    (bundleCoreParamsMach E).c_T =
      65 * (37810 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi + E.c_n) + 18000 := by
  simp [bundleCoreParamsMach, bundleCoreParamsMachWith_c_T]

lemma bundleCoreParamsMach_p_T (E : SparseCoreEnv) :
    (bundleCoreParamsMach E).p_T = max 6 (max E.p_s_hi E.p_t_hi + 4) := rfl

theorem bundleCoreParamsMachWith_valid (E : SparseCoreEnv) (spanConst : ℕ) :
    (bundleCoreParamsMachWith E spanConst).Valid := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := bundleCoreParams_valid E
  have hc : (0 : ℝ) ≤ ((max 1 spanConst : ℕ) : ℝ) := Nat.cast_nonneg _
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9,
    mul_nonneg hc (by linarith)⟩

theorem bundleCoreParamsMach_valid (E : SparseCoreEnv) : (bundleCoreParamsMach E).Valid :=
  bundleCoreParamsMachWith_valid E 1

end MinCostFlow.SparseCore

end
