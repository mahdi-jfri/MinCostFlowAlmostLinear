module

public import MinCostFlow.MinRatio.UpdateAssemblyBase
import Mathlib.Tactic

/-!
# The vectors handed to the refresh (`UpdateOverlayRead`)

`Update` copies the entries of `g` and `l` at the inserted edges. The refresh reads the copy
over the stored vector (`updateOverlay`). This file shows that the result is the caller's
vector when every edge below `m` is live.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program

/-- The overlay of a copied vector over the stored one is the caller's vector `v` under three
conditions. First, `v` agrees with the stored vector on the live edges that the batch does not
insert. Second, `v` is `0` from `m` on. Third, the copy agrees with `v` at the inserted edges.
An edge that is neither live nor inserted is at least `m`, since every edge below `m` is live.
There both sides are `0`. -/
theorem updateOverlay_readVector_eq {E : Finset ℕ} {U : List Update} {mem : ℕ → ℕ}
    {src L P m : ℕ} {stored v : ℕ → ℝ} (hE : ∀ e < m, e ∈ E)
    (hst : ∀ e ∈ E, ¬ (∃ u ∈ U, u.Inserts e) → v e = stored e)
    (hv0 : ∀ e, m ≤ e → v e = 0)
    (hcp : ∀ e, (∃ u ∈ U, u.Inserts e) → readVector mem src 4 L P m e = v e) :
    updateOverlay E U (readVector mem src 4 L P m) stored = v := by
  refine updateOverlay_eq hst fun e he => ?_
  by_cases hins : ∃ u ∈ U, u.Inserts e
  · exact hcp e hins
  · have hme : m ≤ e := by
      by_contra hlt
      exact he ⟨hE e (by omega), hins⟩
    rw [hv0 e hme]
    unfold readVector
    rw [ite_eq_right (by omega)]

end MinCostFlow.MinRatio
