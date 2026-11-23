module

public import MinCostFlow.DynSpanner.Program.CanonicalSparsify

import MinCostFlow.DynSpanner.Program.GraphTranslateRev

/-!
# The length of the walks returned by the sparsifier

Theorem 8.1 (page 39) returns an embedding `Π_{J → J̃}` of length at most `γ_ℓ`: in the cited form
(`CitedSparsifyProp`) every walk of the guest's output has at most `γ_ℓ` edges. The canonical
sparsifier `canonicalSparsify` translates these walks back to `MGraph` walks with
`citedWalkSteps`, which keeps their number of edges. So each walk `(canonicalSparsify …).emb e`
of an edge `e` of `J` has at most `⌈γ_ℓ⌉` steps (`canonicalSparsify_emb_length_le`). The cost of
the program after the sparsifier call (copying and composing these walks) is linear in these
lengths, which is why we need the bound.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

public section

/-- Each output walk of the canonical sparsifier has at most `⌈γ_ℓ⌉` steps (Theorem 8.1,
page 39: the embedding `Π_{J → J̃}` has length at most `γ_ℓ`). -/
theorem canonicalSparsify_emb_length_le (impl : SparsifyImpl) (mMax : ℕ)
    {H' J : MGraph} {emb : MinCostFlow.Embedding}
    (hH' : H'.IsValid) (hJ : J.IsValid) (hJm : J.m ≤ mMax)
    (hLen : J.E.Nonempty → 1 ≤ emb.length J) (hemb : emb.IsEmbedding J H') :
    ∀ e ∈ J.E, ((canonicalSparsify impl H' J emb).emb e).length ≤ ⌈impl.γ_ℓ mMax⌉₊ := by
  intro e he
  by_cases hJn : 1 ≤ J.n
  · have hV : CanonicalSparsifyValid impl H' J emb := ⟨hJn, hH', hJ, hLen, hemb⟩
    obtain ⟨body, o, st', cost, cJtilde, kept, embJJtilde,
      hp, hr, _, _, _, hProp, hOut, _⟩ :=
      canonicalGuestRun_exists impl mMax hH' hJ hJm hLen hemb
    rw [canonicalSparsify_eq_of_run hV hp hr hOut]
    simp only [citedEmbToMGraph, he, ↓reduceIte]
    rw [citedWalkSteps_length]
    have hj_lt : (vertsOf J.E).idxOf e < (toCitedJ J).m := by
      rw [toCitedJ_m]; exact idxOf_lt_card he
    have hlen_nat : (embJJtilde ((vertsOf J.E).idxOf e)).edges.length ≤
        Spanner.length (toCitedJ J) embJJtilde := by
      unfold Spanner.length
      exact (Finset.le_fold_max _).mpr (Or.inr ⟨_, Finset.mem_range.mpr hj_lt, le_rfl⟩)
    have hlen_r : ((embJJtilde ((vertsOf J.E).idxOf e)).edges.length : ℝ) ≤ impl.γ_ℓ mMax :=
      le_trans (by exact_mod_cast hlen_nat) hProp.2.2.2.2.2.2.2.1
    exact le_trans (min_le_right _ _) (Nat.cast_le.mp (hlen_r.trans (Nat.le_ceil _)))
  · have hnV : ¬ CanonicalSparsifyValid impl H' J emb := fun h => hJn h.1
    simp only [canonicalSparsify, hnV, ↓reduceDIte, idEmb, List.length_singleton]
    exact Nat.one_le_iff_ne_zero.mpr fun h0 => by
      have := (Nat.ceil_eq_zero (a := impl.γ_ℓ mMax)).mp h0
      linarith [impl.hγ_ℓ mMax]

end

end MinCostFlow.DynSpanner.Program
