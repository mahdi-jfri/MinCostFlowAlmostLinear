module

public import MinCostFlow.LSF.ModelWith
public import MinCostFlow.LSF.Program.Layout

/-!
# The parameters of the initial state

The state that `lsfInitPost` asks for is `initLSFWith` at the tree, root, representatives, edge
order and decomposition that the init driver computes, with the properties `ValidLSFParams`.
On the main branch (`G₀` has an edge) the tree is an LSST of the weighted copy graph, so the
`if` in `ValidLSFParams` takes its first branch. `validParams_of_parts` puts the parts together;
the threshold part holds for `defaultThreshNat` (`defaultThreshNat_isWstrThresh`), and the root
lies in `G₀.V` because it is one of the representatives.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF

@[expose] public section

/-- `ValidLSFParams` from its parts, when `G₀` has an edge. -/
theorem validParams_of_parts {K_AN : ℝ} {G₀ : MGraph} {ℓ₀ v : ℕ → ℝ} {k_nat : ℕ}
    {T_raw : MGraph} {r₀ : ℕ} {C_reps : Finset ℕ} {π : ℕ → ℕ} {W_T : Finset (Finset ℕ)}
    (hT : IsLSST (open Classical in if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀)
      (open Classical in if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₀ else fun _ => 1)
      (fun _ => 1) ((4 * max K_AN 1 + 5) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_raw)
    (hC : IsCompReps G₀ r₀ C_reps)
    (hπ : IsApproxCongOrder (open Classical in if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀)
      (projectTree G₀ v T_raw)
      (open Classical in if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₀ else fun _ => 1) (5 / 4) π)
    (hW : IsTreeDecompSpec G₀ (projectTree G₀ v T_raw) (k_nat : ℝ) W_T) (hk : 1 ≤ k_nat) :
    ValidLSFParams (4 * max K_AN 1 + 5) (5 / 4) (defaultThreshNat K_AN G₀.n k_nat : ℝ)
      (defaultK_sigma K_AN : ℝ) G₀ ℓ₀ v (k_nat : ℝ) T_raw r₀ C_reps π W_T := by
  classical
  have hk1 : (1 : ℝ) ≤ (k_nat : ℝ) := by exact_mod_cast hk
  exact ⟨hT, hC.2.1 hC.1, hC, hπ, hW, defaultThreshNat_isWstrThresh hk1 le_rfl (by linarith)⟩

end

end MinCostFlow.LSF.Program
