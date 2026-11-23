module

public import MinCostFlow.Chain.Ordered.Algorithm1
public import MinCostFlow.Chain.LevelConnected
import MinCostFlow.Chain.Ordered.BudgetHelpers
import Mathlib.Tactic.Linarith

/-!
# Ordered Algorithm 1 Level Connectedness and Last-Level Size Bound

Ordered-chain counterpart of `MinCostFlow.Chain.LevelConnected`: propagates connectedness across
ordered `ChainInv`, yielding `((st.G i).n : ℝ) ≤ (st.G i).m + 1` at every level `0 ≤ i ≤ P.d`,
the small last-level vertex bound `(st.G P.d).n ≤ levelM TP P P.d + 1`, and
`ChainInv.toTreeChain_holds_own`. Reuses the graph-level lemmas `connected_n_le_m_add_one` and
`isSparsifiedCoreGraph_connected` from `MinCostFlow.Chain.LevelConnected`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow MinCostFlow.LSF MinCostFlow.Bundle

section Connectedness

/-- Under ordered `ChainInv`, if `st.G 0` is connected, then every level graph `st.G i`
(`0 ≤ i ≤ P.d`) is connected and satisfies `(st.G i).n ≤ (st.G i).m + 1`. -/
theorem chainInv_connected {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    (hConn0 : ∀ u ∈ (st.G 0).V, ∀ v ∈ (st.G 0).V, (st.G 0).Connected u v) :
    ∀ i ≤ P.d,
      (∀ u ∈ (st.G i).V, ∀ v ∈ (st.G i).V, (st.G i).Connected u v) ∧
      (st.G i).n ≤ (st.G i).m + 1 := by
  have hLvl := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInv
  intro i hi
  induction i with
  | zero => exact ⟨hConn0, connected_n_le_m_add_one (hLvl 0 (Nat.zero_le _)).1 hConn0⟩
  | succ i ih =>
    have hi_lt : i < P.d := hi
    obtain ⟨hConni, _⟩ := ih (Nat.le_of_lt hi_lt)
    have hBi := (hLvl i (Nat.le_of_lt hi_lt)).2.2.2.2 hi_lt (st.bran i) (hInv.hBran i hi_lt)
    have hConnsucc : ∀ u ∈ (st.G (i + 1)).V, ∀ v ∈ (st.G (i + 1)).V, (st.G (i + 1)).Connected u v := by
      rw [hInv.hGSucc i hi_lt]
      exact isSparsifiedCoreGraph_connected hBi.1 hBi.2 hConni
    exact ⟨hConnsucc, connected_n_le_m_add_one (hLvl (i + 1) hi).1 hConnsucc⟩

/-- Under ordered `ChainInv` and connectedness of `st.G 0`, every level `i ≤ P.d` satisfies the
component bound `((st.G i).n : ℝ) ≤ 1 * (((st.G i).m : ℝ) + 1)` (`c_n = 1`), and at level `P.d`
the vertex count satisfies `(st.G P.d).n ≤ levelM TP P P.d + 1`. -/
theorem chainInv_comp_bound_all_levels {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    (hConn0 : ∀ u ∈ (st.G 0).V, ∀ v ∈ (st.G 0).V, (st.G 0).Connected u v) :
    (∀ i ≤ P.d, ((st.G i).n : ℝ) ≤ (1 : ℝ) * (((st.G i).m : ℝ) + 1)) ∧
    (st.G P.d).n ≤ levelM TP P P.d + 1 := by
  have hConnAll := chainInv_connected hTP hγM₀ hγk hInv hConn0
  have hLvl := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInv
  refine ⟨fun i hi => ?_, ?_⟩
  · have hnat : (st.G i).n ≤ (st.G i).m + 1 := (hConnAll i hi).2
    have hreal : ((st.G i).n : ℝ) ≤ ((st.G i).m : ℝ) + 1 := by exact_mod_cast hnat
    linarith
  · have hPd_nat : (st.G P.d).n ≤ (st.G P.d).m + 1 := (hConnAll P.d le_rfl).2
    have hm_le_lvl : ((st.G P.d).m : ℝ) ≤ (levelM TP P P.d : ℝ) :=
      (hLvl P.d le_rfl).2.2.1
    have hm_nat : (st.G P.d).m ≤ levelM TP P P.d := by exact_mod_cast hm_le_lvl
    omega

/-- Connectedness-based counterpart of `ChainInv.toTreeChain_holds_noHidden`: under connectedness
of `st.G 0`, the last-level stretch in `TreeChain.Holds` is bounded at its own level-`d` vertex
cap `LP.σ_last (levelM TP P P.d + 1)` instead of `LP.σ_last (st.G 0).n`. -/
theorem ChainInv.toTreeChain_holds_own {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    {σ_mwu : ℕ → ℝ} (hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → σ_mwu n₁ ≤ σ_mwu n₂)
    (hTP : TP.Valid) (hLP : LP.Valid)
    (hMWU : T.ToolMWUOrdRestartNoHiddenLe σ_mwu (P.M₀ ^ 2))
    (hEmb : T.ToolEmbedsSurvivingOrdRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    (hConn0 : ∀ u ∈ (st.G 0).V, ∀ v ∈ (st.G 0).V, (st.G 0).Connected u v) :
    let σ_tot := max (TP.σ P.k (st.G 0).n) (LP.σ_last (levelM TP P P.d + 1))
    let σ_mwu_tot := max (σ_mwu (st.G 0).n) (LP.σ_mwu (st.G 0).n)
    st.toTreeChain.Holds (st.G 0) st.ℓ σ_tot σ_mwu_tot (TP.γ_ℓ (P.M₀ ^ 2)) (TP.γ_c (P.M₀ ^ 2)) ∧
    st.toTreeChain.LastLevelSpans ∧
    st.toTreeChain.EmbedsSurviving := by
  have hB := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInv
  have hPd_le : (st.G P.d).n ≤ levelM TP P P.d + 1 :=
    (chainInv_comp_bound_all_levels hTP hγM₀ hγk hInv hConn0).2
  have hOld := ChainInv.toTreeChain_holds_noHidden hσ_mwu_mono hTP hLP hMWU hEmb hγM₀ hγk hInv
  refine ⟨?_, hOld.2.1, hOld.2.2⟩
  refine ⟨hOld.1.1, hOld.1.2.1, hOld.1.2.2.1, hOld.1.2.2.2.1, ?_, hOld.1.2.2.2.2.2.1, ?_,
    hOld.1.2.2.2.2.2.2.2⟩
  · intro i hi
    refine ⟨hInv.hBran i hi, ?_, ?_, ?_⟩
    · intro j hj
      have hij := (hB i (Nat.le_of_lt hi)).2.2.2.2 hi j hj
      exact ⟨LSF.Holds.mono_σ hij.1 (le_max_left _ _), hij.2.toNoSize⟩
    · exact (hOld.1.2.2.2.2.1 i hi).2.2.1
    · exact (hOld.1.2.2.2.2.1 i hi).2.2.2
  · intro j hj
    exact LSF.Holds.mono_σ (hInv.hLastHolds j hj)
      (le_trans (hLP.2.1 _ _ hPd_le) (le_max_right _ _))

end Connectedness

end MinCostFlow.Chain.Ordered
