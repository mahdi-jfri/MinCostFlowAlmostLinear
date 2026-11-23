module

public import MinCostFlow.Chain.Ordered.Budget
public import MinCostFlow.Chain.FindCycleProofs
import MinCostFlow.Chain.Ordered.BudgetHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# FindCycle Quality and Level Graph Size Bounds for Ordered Algorithm 1 (Lemma 5.11 Helpers)

Ordered-chain counterpart of `MinCostFlow.Chain.FindCycleProofs`: derives `findCycle_spec*` and
`level_graph_size_bounds*` for ordered `ChainInv` and `LevelHistory`, reusing the generic
`TreeChain` results `findCycle_spec_of_holds` and `nonIsolatedV_card_le` from
`MinCostFlow.Chain.FindCycleProofs`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section FindCycleProofs

/-- **Algorithm 1 `FindCycle` specification (Lemma 5.11, pages 20, 24)** for ordered `ChainInv`:
for any state `st` satisfying ordered `ChainInv`, `ToolMWUOrdRestartNoHidden`, and
`ToolEmbedsSurvivingOrdRestartNoHidden`, and any valid pair `(c, w)` for `(st.G 0, st.ℓ)`,
`algorithm1_findCycle st` outputs a circulation `Δ` achieving the Lemma A.2 ratio bound and
represented by at most `1 + TP.γ_ℓ (P.M₀ ^ 2)` off-tree edges. -/
theorem findCycle_spec_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    {σ_mwu : ℕ → ℝ} (hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → σ_mwu n₁ ≤ σ_mwu n₂)
    (hTP : TP.Valid) (hLP : LP.Valid)
    (hMWU : T.ToolMWUOrdRestartNoHiddenLe σ_mwu (P.M₀ ^ 2))
    (hEmb : T.ToolEmbedsSurvivingOrdRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    {c w : ℕ → ℝ} (hvp : IsValidPair (st.G 0) st.ℓ c w) :
    let σ_tot := max (TP.σ P.k (st.G 0).n) (LP.σ_last (st.G 0).n)
    let C := st.toTreeChain
    let (Δ, walk, optEdge) := algorithm1_findCycle st
    (st.G 0).IsCirculation Δ ∧
    (st.G 0).inner st.g Δ ≤ 0 ∧
    ((walkEdges walk \ C.chainTree.E).card : ℝ) ≤ 1 + TP.γ_ℓ (P.M₀ ^ 2) ∧
    (optEdge = none → Δ = 0 ∧ walk = [] ∧ (st.G 0).inner st.g c = 0) ∧
    (∀ e, optEdge = some e →
      e ∈ (st.G 0).E \ C.chainTree.E ∧
      0 < (st.G 0).lnorm st.ℓ Δ ∧
      (1 / (σ_tot + 1)) *
          (|(st.G 0).inner st.g c| / ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i)) ≤
        |(st.G 0).inner st.g Δ| / (st.G 0).lnorm st.ℓ Δ) := by
  have hTree := ChainInv.toTreeChain_holds_noHidden hσ_mwu_mono hTP hLP hMWU hEmb hγM₀ hγk hInv
  exact findCycle_spec_of_holds st (hTP.2.2.1 (P.M₀ ^ 2)) hInv.hℓPos hTree.1 hTree.2.1 hTree.2.2 hvp

end FindCycleProofs

section LevelGraphSizes

/-- **Level graph size bounds (Lemma 5.11 proof, page 24)** for ordered `ChainInv`:
1. `|(st.G i).E| ≤ levelM TP P i` for all `i ≤ P.d`;
2. the non-isolated vertex count of `st.G i` is at most `2 * levelM TP P i`;
3. for `0 < i ≤ P.d`, if level `i - 1`'s `LevelHistory` base graph `H.D.G 0` is connected, then
   `|(st.G i).V| ≤ c_R * (2 * P.M₀ * γ_ℓ^i / k^i + 3)`. -/
theorem level_graph_size_bounds_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) :
    (∀ i ≤ P.d, ((st.G i).m : ℝ) ≤ (levelM TP P i : ℝ)) ∧
    (∀ i ≤ P.d, ((nonIsolatedV (st.G i)).card : ℝ) ≤ 2 * (levelM TP P i : ℝ)) ∧
    (∀ i, 0 < i → i ≤ P.d →
      ∀ H : LevelHistory T TP P N₀ st (i - 1),
        (∀ u ∈ (H.D.G 0).V, ∀ v ∈ (H.D.G 0).V, (H.D.G 0).Connected u v) →
        ((st.G i).n : ℝ) ≤ TP.c_R * (2 * (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i + 3)) := by
  have hLev := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInv
  refine ⟨fun i hi => (hLev i hi).2.2.1, fun i hi => ?_, fun i hi0 hi H hConn => ?_⟩
  · have hni : ((nonIsolatedV (st.G i)).card : ℝ) ≤ 2 * ((st.G i).m : ℝ) := by
      exact_mod_cast nonIsolatedV_card_le (st.G i)
    linarith [(hLev i hi).2.2.1]
  · have hi_prev_lt : i - 1 < P.d := by omega
    have hi_prev_le : i - 1 ≤ P.d := Nat.le_of_lt hi_prev_lt
    have hSp := (hLev (i - 1) hi_prev_le).2.2.2.2 hi_prev_lt (st.bran (i - 1))
      (hInv.hBran (i - 1) hi_prev_lt)
    have hVsubR : (st.G i).V ⊆ (T.lsfs (st.scState (i - 1)) (st.bran (i - 1))).F.R := by
      have hGsucc := hInv.hGSucc (i - 1) hi_prev_lt
      rw [show i - 1 + 1 = i by omega] at hGsucc
      rw [hGsucc]
      exact hSp.2.1.1
    have hn_le_R : ((st.G i).n : ℝ) ≤ ((T.lsfs (st.scState (i - 1)) (st.bran (i - 1))).F.R.card : ℝ) :=
      by exact_mod_cast Finset.card_le_card hVsubR
    have hSpec := H.hOK.noHidden P.k H.len (levelM TP P (i - 1)) N₀ H.D H.ord H.restarts
      P.hk H.hG0 H.hD H.hLen H.hℓPos H.hOrd H.hInitMBound H.hInitNBound H.hRestartsLt
      (by rw [H.hUpd]; exact H.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hR := (hSpec.1 H.len (le_refl _) (st.bran (i - 1)) (hInv.hBran (i - 1) hi_prev_lt)).2.2 hConn
    dsimp only at hR
    rw [← H.hRun] at hR
    have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
    have hlog_pos : 0 < Real.log ((N₀ : ℝ) + 2) := log_add_two_pos _ (Nat.cast_nonneg _)
    have hsq_pos : 0 < (Real.log ((N₀ : ℝ) + 2)) ^ 2 := sq_pos_of_pos hlog_pos
    have hUpdLog : (((Finset.Icc 1 H.len).sum fun s => (H.D.U s).length : ℕ) : ℝ) *
        (Real.log ((N₀ : ℝ) + 2)) ^ 2 ≤ (levelM TP P (i - 1) : ℝ) / (P.k : ℝ) := by
      have hT' : (((Finset.Icc 1 H.len).sum fun s => (H.D.U s).length : ℕ) : ℝ) ≤
          (levelM TP P (i - 1) : ℝ) / ((P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 2) := by
        rw [H.hUpd]
        exact H.hThresh
      have h1 := mul_le_mul_of_nonneg_right hT' hsq_pos.le
      calc
        (((Finset.Icc 1 H.len).sum fun s => (H.D.U s).length : ℕ) : ℝ) *
            (Real.log ((N₀ : ℝ) + 2)) ^ 2
            ≤ (levelM TP P (i - 1) : ℝ) / ((P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 2) *
                (Real.log ((N₀ : ℝ) + 2)) ^ 2 := h1
        _ = (levelM TP P (i - 1) : ℝ) / (P.k : ℝ) := by
          field_simp [hk_pos.ne', hsq_pos.ne']
    have hm0_lt := levelM_lt_add_one hTP P (i - 1)
    have hm0_div_k : (levelM TP P (i - 1) : ℝ) / (P.k : ℝ) ≤
        (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i + 1 := by
      have hdiv : (levelM TP P (i - 1) : ℝ) / (P.k : ℝ) ≤
          ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (i - 1) + 1) / (P.k : ℝ) :=
        div_le_div_of_nonneg_right hm0_lt.le hk_pos.le
      have hk_pow : (P.k : ℝ) ^ i = (P.k : ℝ) ^ (i - 1) * (P.k : ℝ) := by
        rw [← pow_succ, show i - 1 + 1 = i by omega]
      have hγ_pow : (TP.γ_ℓ (P.M₀ ^ 2)) ^ i = (TP.γ_ℓ (P.M₀ ^ 2)) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (i - 1) := by
        rw [← pow_succ', show i - 1 + 1 = i by omega]
      have hpow_eq : (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (i - 1) / (P.k : ℝ) =
          (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i := by
        rw [div_pow, hk_pow, hγ_pow]
        field_simp [hk_pos.ne']
      have hinvk : (1 : ℝ) / (P.k : ℝ) ≤ 1 := by
        rw [div_le_one hk_pos]
        exact_mod_cast P.hk
      linarith [add_div ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (i - 1)) 1 (P.k : ℝ)]
    have hcR : 0 ≤ TP.c_R := hTP.2.2.2.2.2.2.2.2.1
    refine le_trans hn_le_R (le_trans hR ?_)
    have hinner : (levelM TP P (i - 1) : ℝ) / (P.k : ℝ) +
          (((Finset.Icc 1 H.len).sum fun s => (H.D.U s).length : ℕ) : ℝ) *
            (Real.log ((N₀ : ℝ) + 2)) ^ 2 + 1 ≤
        2 * (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i + 3 := by
      have hdbl :
          (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i +
            (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i =
          2 * (P.M₀ : ℝ) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ i / (P.k : ℝ) ^ i := by ring
      linarith [hm0_div_k, hUpdLog, hdbl]
    exact mul_le_mul_of_nonneg_left hinner hcR

end LevelGraphSizes

end MinCostFlow.Chain.Ordered
