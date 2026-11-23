module

public import MinCostFlow.SparseCore.Program.AssemblyReemb
public import MinCostFlow.Expander.Section8Asymptotics

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Subpolynomial sparsifier stretch and depth monotonicity (`AssemblyStretch`)

Provides the stretch and depth helpers for the branch-module bridge:
* `SparsifySubpolyStretch impl`: subpolynomial walk-length stretch
  `∃ C_sp > 0, ∀ m, impl.γ_ℓ m ≤ exp (C_sp * log (m + 2) ^ (7 / 8))`, matching Theorem 8.1
  (page 39) and `SparsifyImplHyp`.
* `sparsifyPolyStretch_of_subpolyStretch`: recovers `SparsifyPolyStretch impl`
  (`⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ`) from `SparsifySubpolyStretch impl` for the branch
  restart space polynomial (`AssemblyBranchRestartPoly.lean`).
* `chosenL_mono` and `chosenL_sq_le_chosenL_add_sq`: monotonicity of `Expander.chosenL`,
  discharging `Expander.chosenL (M₀ ^ 2) ≤ Expander.chosenL ((M + N) ^ 2)` whenever `4 * M₀ ≤ N`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.DynSpanner.Program

/-- Subpolynomial upper bound on the walk-length stretch `impl.γ_ℓ m` of a sparsifier
implementation (Theorem 8.1, page 39): `impl.γ_ℓ m ≤ exp (C_sp * log (m + 2) ^ (7 / 8))` for
some constant `C_sp > 0`. Combined with `depth ≤ Expander.chosenL ((M + N) ^ 2)`, this bounds
the spanner walk length `3 ^ depth * (impl.γ_ℓ M) ^ (depth + 1)` linearly in `M + N + 2`. -/
def SparsifySubpolyStretch (impl : SparsifyImpl) : Prop :=
  ∃ C_sp : ℝ, 0 < C_sp ∧
    ∀ m : ℕ, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ))

private theorem rpow_le_add_one {t a : ℝ} (ht : 0 ≤ t) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    t ^ a ≤ t + 1 := by
  by_cases h1 : t ≤ 1
  · calc t ^ a ≤ 1 ^ a := Real.rpow_le_rpow ht h1 ha0
      _ = 1 := Real.one_rpow a
      _ ≤ t + 1 := by linarith
  · have h1' : 1 < t := not_le.mp h1
    calc t ^ a ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1'.le ha1
      _ = t := Real.rpow_one t
      _ ≤ t + 1 := by linarith

/-- Every sparsifier program satisfying `SparsifySubpolyStretch impl` also satisfies
`SparsifyPolyStretch impl` (with `Cγ = ⌈exp C_sp⌉₊`, `cγ = ⌈C_sp⌉₊`). -/
theorem sparsifyPolyStretch_of_subpolyStretch {impl : SparsifyImpl}
    (h : SparsifySubpolyStretch impl) : SparsifyPolyStretch impl := by
  obtain ⟨C_sp, hCpos, hγ⟩ := h
  refine ⟨Nat.ceil (Real.exp C_sp), Nat.ceil C_sp, fun m => ?_⟩
  have hγm := hγ m
  set x : ℝ := (m : ℝ) + 2
  have hx1 : (1 : ℝ) ≤ x := by dsimp only [x]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hxpos : (0 : ℝ) < x := by linarith
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hrpow : Real.log x ^ (7 / 8 : ℝ) ≤ Real.log x + 1 :=
    rpow_le_add_one hlog_nn (by norm_num) (by norm_num)
  have hcγ_ge : C_sp ≤ (Nat.ceil C_sp : ℝ) := Nat.le_ceil C_sp
  have hCγ_ge : Real.exp C_sp ≤ (Nat.ceil (Real.exp C_sp) : ℝ) := Nat.le_ceil (Real.exp C_sp)
  have hexp_arg : C_sp * Real.log x ^ (7 / 8 : ℝ) ≤ C_sp + (Nat.ceil C_sp : ℝ) * Real.log x := by
    have h1 : C_sp * Real.log x ^ (7 / 8 : ℝ) ≤ C_sp * (Real.log x + 1) :=
      mul_le_mul_of_nonneg_left hrpow hCpos.le
    have h2 : C_sp * Real.log x ≤ (Nat.ceil C_sp : ℝ) * Real.log x :=
      mul_le_mul_of_nonneg_right hcγ_ge hlog_nn
    linarith
  have hbound : impl.γ_ℓ m ≤ ((Nat.ceil (Real.exp C_sp) * (m + 2) ^ Nat.ceil C_sp : ℕ) : ℝ) := by
    push_cast
    calc impl.γ_ℓ m
        ≤ Real.exp (C_sp * Real.log x ^ (7 / 8 : ℝ)) := hγm
      _ ≤ Real.exp (C_sp + (Nat.ceil C_sp : ℝ) * Real.log x) := Real.exp_le_exp.mpr hexp_arg
      _ = Real.exp C_sp * Real.exp (Real.log x * (Nat.ceil C_sp : ℝ)) := by
          rw [Real.exp_add, mul_comm (Nat.ceil C_sp : ℝ) (Real.log x)]
      _ = Real.exp C_sp * x ^ (Nat.ceil C_sp : ℝ) := by rw [← Real.rpow_def_of_pos hxpos]
      _ = Real.exp C_sp * x ^ Nat.ceil C_sp := by rw [Real.rpow_natCast]
      _ ≤ (Nat.ceil (Real.exp C_sp) : ℝ) * x ^ Nat.ceil C_sp :=
          mul_le_mul_of_nonneg_right hCγ_ge (by positivity)
  exact Nat.ceil_le.mpr hbound

/-- `Expander.chosenL` is monotone in its natural-number argument. -/
theorem chosenL_mono {a b : ℕ} (h : a ≤ b) : Expander.chosenL a ≤ Expander.chosenL b := by
  unfold Expander.chosenL
  apply Nat.ceil_mono
  have ha1 : (1 : ℝ) ≤ (a : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) a]
  have hab : (a : ℝ) + 2 ≤ (b : ℝ) + 2 := by
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h
    linarith
  exact Real.rpow_le_rpow (Real.log_nonneg ha1) (Real.log_le_log (by linarith) hab) (by norm_num)

/-- The dry-run balancing depth `Expander.chosenL (M₀ ^ 2)` is at most
`Expander.chosenL ((M + N) ^ 2)` whenever `4 * M₀ ≤ N`. -/
theorem chosenL_sq_le_chosenL_add_sq {M₀ M N : ℕ} (hN : 4 * M₀ ≤ N) :
    Expander.chosenL (M₀ ^ 2) ≤ Expander.chosenL ((M + N) ^ 2) :=
  chosenL_mono (Nat.pow_le_pow_left (by omega) 2)

end MinCostFlow.SparseCore.Program
