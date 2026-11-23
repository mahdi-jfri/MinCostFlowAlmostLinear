module

public import MinCostFlow.Expander.ExpanderDecomp

/-!
# The expander decomposition that the proof uses

The proof of Theorem 1.1 calls the expander decomposition of [CGLNPS21], Corollary 6.1
(`Cited.ExpanderDecomposition`), in one way only. Algorithm 5 (`Decompose`, Appendix B, page 49)
calls it with `ε = 1/200` and with the parameter `r = rOf m = ⌊(log₂ m)^{1/3}⌋`, on loopless
graphs with at least `thresholdB1 cr` edges (`MinCostFlow/Expander/DecomposeProg.lean`,
`MinCostFlow/Expander/ExpanderDecomp.lean`).

This file states that use as the proposition `ExpanderDecompositionUsed`. It has the same shape as
the cited statement, specialized to `a = 1`, `b = 200` and `r = rOf m`: the same constants `K` and
`cr`, one program `P` with word size constant `c`, the same conductance
`ε / (K · log(m+2)^{K r²})`, and the same time bound
`K · (n + (m+2)^{1+K/r} · log(m+2)^{K r²} / ε²)`. The casts are written as the cited statement
produces them at `a = 1` and `b = 200`.

`ExpanderDecompositionUsed.of_cited` derives it from the cited statement. The files of
`MinCostFlow/ExpanderDecomp/` prove it directly, without the cited statement.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander WordRAM

/-- The expander decomposition used by Algorithm 5: [CGLNPS21], Corollary 6.1
(arXiv:1910.08025v2, page 43), at `ε = 1/200` and `r = rOf m`. There are constants `K > 0` and
`cr > 0`, a program `P` and a word size constant `c` such that on every loopless graph `G` with at
least `thresholdB1 cr` edges, for every sequence of random bits, `P` halts on
`G.encode ++ [1, 200, rOf m]` with a `(1/200, φ)`-expander decomposition of `G` for
`φ = (1/200) / (K · log(m+2)^{K r²})`, within `K · (n + (m+2)^{1+K/r} · log(m+2)^{K r²} / (1/200)²)`
steps, where `r = rOf m`. -/
def ExpanderDecompositionUsed : Prop :=
  ∃ (K cr : ℝ) (P : Program) (c : ℕ), 0 < K ∧ 0 < cr ∧
    ∀ G : Graph, G.IsValid → G.IsLoopless → thresholdB1 cr ≤ G.m → ∀ ω, ∃ out cost,
      RunsTo (wordSize c (G.encode ++ [1, 200, rOf G.m])) P (G.encode ++ [1, 200, rOf G.m]) ω
        out cost ∧
      IsExpanderDecomposition G (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ))
        ((((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) /
          (K * Real.log ((G.m : ℝ) + 2) ^ (K * (rOf G.m : ℝ) ^ 2))) out ∧
      (cost : ℝ) ≤ K * (G.n + ((G.m : ℝ) + 2) ^ (1 + K / rOf G.m) *
        Real.log ((G.m : ℝ) + 2) ^ (K * (rOf G.m : ℝ) ^ 2) /
          (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2)

/-- The cited statement gives the use: take `a = 1`, `b = 200` and `r = rOf m`, which satisfies
`1 ≤ r ≤ cr · log m` once `m ≥ thresholdB1 cr` (`rOf_le_cr_log`). -/
theorem ExpanderDecompositionUsed.of_cited (h : Cited.ExpanderDecomposition) :
    ExpanderDecompositionUsed := by
  obtain ⟨K, cr, P, c, hK, hcr, hspec⟩ := h
  refine ⟨K, cr, P, c, hK, hcr, fun G hv hl hm ω => ?_⟩
  obtain ⟨hr1, hr⟩ := rOf_le_cr_log hcr hm
  exact hspec G 1 200 (rOf G.m) hv hl le_rfl (by norm_num) hr1 hr ω

end MinCostFlow.ExpanderDecomp
