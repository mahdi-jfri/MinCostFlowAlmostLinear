module

public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Interval

/-!
# Counting distinct nested terminal cuts

For the path swaps in Algorithm 2 (page 29), edges with the same
terminal cut can use the same representative. A family of nonempty
terminal subsets that are nested or disjoint has at most the square
of the number of terminals. The least element and the size identify
each set in the family.
-/

public section

namespace MinCostFlow.MinRatio

/-- A nonempty family of nested or disjoint terminal cuts has at
most a quadratic number of distinct members. -/
theorem terminalCutCount_le (terminals : Finset ℕ) (cuts : Finset (Finset ℕ))
    (hsub : ∀ s ∈ cuts, s ⊆ terminals)
    (hne : ∀ s ∈ cuts, s.Nonempty)
    (hlam : ∀ s ∈ cuts, ∀ t ∈ cuts, s ⊆ t ∨ t ⊆ s ∨ Disjoint s t) :
    cuts.card ≤ terminals.card * terminals.card := by
  classical
  let key := fun s : Finset ℕ =>
    (if h : s.Nonempty then s.min' h else 0, s.card - 1)
  apply (Finset.card_le_card_of_injOn key (t := terminals ×ˢ Finset.range terminals.card) ?_ ?_).trans
  · simp
  · intro s hs
    change s ∈ cuts at hs
    have hn := hne s hs
    have hc := Finset.card_le_card (hsub s hs)
    have hp := Finset.card_pos.mpr hn
    simp only [key, dite_eq_left hn, Finset.mem_product, Finset.mem_range, Finset.mem_coe]
    exact ⟨hsub s hs (Finset.min'_mem _ _), by omega⟩
  · intro s hs t ht hk
    change s ∈ cuts at hs
    change t ∈ cuts at ht
    have hsn := hne s hs
    have htn := hne t ht
    have hsc := Finset.card_pos.mpr hsn
    have htc := Finset.card_pos.mpr htn
    simp only [key, dite_eq_left hsn, dite_eq_left htn, Prod.mk.injEq] at hk
    have hcard : s.card = t.card := by omega
    rcases hlam s hs t ht with hst | hts | hd
    · exact Finset.eq_of_subset_of_card_le hst hcard.ge
    · exact (Finset.eq_of_subset_of_card_le hts hcard.le).symm
    · have hsm := Finset.min'_mem s hsn
      have htm := Finset.min'_mem t htn
      exact (Finset.disjoint_left.mp hd hsm (hk.1.symm ▸ htm)).elim

end MinCostFlow.MinRatio
