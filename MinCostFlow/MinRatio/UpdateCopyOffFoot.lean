module

import Mathlib.Data.Nat.Notation

/-!
# The copies that `Update` hands on miss the footprint (`UpdateCopyOffFoot`)

The contract of `Update` places the caller's gradient and length arrays below the heap pointer
`heap` of the call, as it places the solver's footprint, but it does not say that they miss the
footprint. So `Update` first copies the entries of the inserted edges into two arrays of `n`
words each, at `gC` and `gC + n`, above `heap` (`copyInsertedStmt`), and hands these copies on.

`copies_off_foot` shows that no word of the two copies lies in the footprint after the
preparation of `Update` or in the owned cells of the select state. The old footprint and the
owned cells lie below `heap`, which is at most `gC`. The cells that the preparation adds to the
footprint lie at `h0` or above, and `gC + 2 n ≤ h0`. The select-aware `Update`
(`solverOps_update_runs_credit_sel`) uses it for the premise of `ChainRefreshStepSpecWKFBLSel`
that the arrays it hands on lie off the footprint and off the owned cells.
-/

public section

namespace MinCostFlow.MinRatio

/-- The two copies `[gC, gC + n)` and `[gC + n, gC + 2 n)` miss the new footprint `foot'` and the
owned cells `owned`, when the old footprint and the owned cells lie below `heap ≤ gC` and the new
footprint adds only cells from `h0 ≥ gC + 2 n` on. -/
theorem copies_off_foot {foot foot' owned : ℕ → Prop} {heap gC n h0 h2 : ℕ}
    (hbelow : ∀ a, foot a ∨ owned a → a < heap)
    (hft : ∀ a, foot' a → foot a ∨ (h0 ≤ a ∧ a < h2))
    (hle : heap ≤ gC) (hh0 : gC + 2 * n ≤ h0) :
    ∀ j < n, ¬ (foot' (gC + j) ∨ owned (gC + j)) ∧
      ¬ (foot' (gC + n + j) ∨ owned (gC + n + j)) := by
  have hoff (a : ℕ) (hlo : gC ≤ a) (hhi : a < h0) : ¬ (foot' a ∨ owned a) := by
    rintro (hf | ho)
    · rcases hft a hf with h | ⟨h, _⟩
      · have := hbelow a (Or.inl h)
        omega
      · omega
    · have := hbelow a (Or.inr ho)
      omega
  intro j hj
  exact ⟨hoff _ (Nat.le_add_right _ _) (by omega), hoff _ (by omega) (by omega)⟩

end MinCostFlow.MinRatio
