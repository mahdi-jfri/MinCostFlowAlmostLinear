module

public import MinCostFlow.Final.AssemblyDryRunWitness
public import MinCostFlow.DynSpanner.Program.SparsifyImplUsed

/-!
# The sparsifier program of Section 8 meets `SparsifyImplHyp`

The dry run of the final assembly (`Final/AssemblyDryRun.lean`) takes a sparsifier program `impl`
and a constant `C_sp` with `SparsifyImplHyp impl C_sp` (`Final/AssemblyDryRunWitness.lean`): unit
time factor, `p_s = p_t = 1`, and both `γ` factors at most `exp(C_sp log^{7/8}(m + 2))`.

Here we show that the program `sparsifyImplUsed` of `DynSpanner/Program/SparsifyImplUsed.lean`
(Algorithm 4, page 42, on the tools of Section 8) meets it. Each clause is one lemma of that file.
-/

namespace MinCostFlow.Final.DryRun

open MinCostFlow.DynSpanner.Program

public section

/-- The program `sparsifyImplUsed` of `Sparsify` (Theorem 8.1, page 39) meets the hypothesis
`SparsifyImplHyp` of the dry run for some constant `C_sp`. -/
theorem sparsifyImplHyp_sparsifyImplUsed : ∃ C_sp : ℝ, SparsifyImplHyp sparsifyImplUsed C_sp := by
  obtain ⟨C_sp, hC, h⟩ := sparsifyImplUsed_gamma_bound
  exact ⟨C_sp, hC, sparsifyImplUsed_p_s, sparsifyImplUsed_p_t, sparsifyImplUsed_γ_t, h⟩

end

end MinCostFlow.Final.DryRun
