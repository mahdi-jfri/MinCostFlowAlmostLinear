module

public import MinCostFlow.Chain.Ordered.Budget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Invariant Consequences and Ordered Budget Helpers for Algorithm 1

This file proves the structural consequences of `Ordered.ChainInv` (`level_bounds_aux_noHidden`,
`ChainInv.toTreeChain_holds_noHidden`, and the length ranges `chainInv_levelLenRange`) and the
basic monotonicity and decomposition lemmas for the ordered runtime budgets `opRuntimeBudget`,
`activeRestartCap`, `ChainBudgetInv`, and `ChainBudgetInvWith` (which carry the `(k + 1)` factor
from `SparseCoreRestartTool.IsSpecOrdRestartNoHidden`).
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section LevelBounds

/-- Per-level validity, vertex inclusion, edge-count bound, chain-length positivity, and
sparsified core graph guarantees implied by `ChainInv`. -/
lemma level_bounds_aux_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ)
    (hTP : TP.Valid)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) :
    ∀ i ≤ P.d,
      (st.G i).IsValid ∧
      (st.G i).V ⊆ (st.G 0).V ∧
      ((st.G i).m : ℝ) ≤ (levelM TP P i : ℝ) ∧
      (∀ e ∈ (st.G i).E, 0 < st.toTreeChain.chainLen st.ℓ i e) ∧
      (∀ _hi : i < P.d, ∀ j < P.k,
        (T.lsfs (st.scState i) j).Holds (st.G i) (st.toTreeChain.chainLen st.ℓ i)
          (TP.σ P.k (st.G 0).n) ∧
        IsSparsifiedCoreGraphAt (st.G i) (T.lsfs (st.scState i) j)
          (st.toTreeChain.chainLen st.ℓ i) (P.k : ℝ) (TP.γ_ℓ (P.M₀ ^ 2)) (TP.γ_c (P.M₀ ^ 2))
          (levelM TP P i) (T.S (st.scState i) j) (T.emb (st.scState i) j)) := by
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  intro i
  induction i with
  | zero =>
    intro _
    have hV0 : (st.G 0).V ⊆ (st.G 0).V := Finset.Subset.refl _
    have hm0 : ((st.G 0).m : ℝ) ≤ (levelM TP P 0 : ℝ) := by
      exact_mod_cast le_trans hInv.hG0m (M₀_le_levelM_zero hTP P)
    have hℓ0 : ∀ e ∈ (st.G 0).E, 0 < st.toTreeChain.chainLen st.ℓ 0 e := hInv.hℓPos
    refine ⟨hInv.hG0Valid, hV0, hm0, hℓ0, fun hi j hj => ?_⟩
    obtain ⟨H⟩ := hInv.hHist 0 hi
    have hSpec := H.hOK.noHidden P.k H.len (levelM TP P 0) N₀ H.D H.ord H.restarts
      P.hk H.hG0 H.hD H.hLen H.hℓPos H.hOrd H.hInitMBound H.hInitNBound H.hRestartsLt
      (by rw [H.hUpd]; exact H.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hAt := hSpec.1 H.len (le_refl _) j hj
    dsimp only at hAt
    rw [H.hEndG, ← H.hRun] at hAt
    have hHolds : (T.lsfs (st.scState 0) j).Holds (st.G 0) (st.toTreeChain.chainLen st.ℓ 0)
        (TP.σ P.k (st.G 0).n) := by
      have h1 := LSF.Holds.congr_len hAt.1 fun e he => H.hEndℓ e he
      exact LSF.Holds.mono_σ h1 (hTP.2.1 _ _ _ _ (le_refl _) (by simp))
    have hm0_le : levelM TP P 0 ≤ P.M₀ ^ 2 := levelM_le_sq hTP hγM₀ hγk 0
    have hSp : IsSparsifiedCoreGraphAt (st.G 0) (T.lsfs (st.scState 0) j)
        (st.toTreeChain.chainLen st.ℓ 0) (P.k : ℝ) (TP.γ_ℓ (P.M₀ ^ 2)) (TP.γ_c (P.M₀ ^ 2))
        (levelM TP P 0) (T.S (st.scState 0) j) (T.emb (st.scState 0) j) := by
      have h2 := hAt.2.1
      have h2' : IsSparsifiedCoreGraphAt (st.G 0) (T.lsfs (st.scState 0) j)
          (st.toTreeChain.chainLen st.ℓ 0) (P.k : ℝ)
          (TP.γ_ℓ (levelM TP P 0)) (TP.γ_c (levelM TP P 0)) (levelM TP P 0)
          (T.S (st.scState 0) j) (T.emb (st.scState 0) j) := by
        rcases h2 with ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩
        refine ⟨hs1, hs2, fun e he e' he' => ?_, hs4, hs5, hs6⟩
        have he0 : e ∈ (st.G 0).E := (Finset.mem_sdiff.mp he).1
        have he'0 : e' ∈ (st.G 0).E := by
          have he'S : e' ∈ (T.S (st.scState 0) j).E := mem_E_of_mem_walkEdges (hs2.2 e he) he'
          exact (Finset.mem_sdiff.mp (hs1.2.1 he'S)).1
        simpa [coreLen, H.hEndℓ e he0, H.hEndℓ e' he'0] using hs3 e he e' he'
      exact isSparsifiedCoreGraphAt_mono h2' hk_pos (le_trans zero_le_one (hTP.2.2.1 _))
        (hTP.2.2.2.1 _ _ hm0_le) (hTP.2.2.2.2.2.1 _ _ hm0_le) le_rfl
    exact ⟨hHolds, hSp⟩
  | succ k ih =>
    intro hk
    have hk_lt : k < P.d := hk
    obtain ⟨hkValid, hkV, _, hkℓ, hkLSF⟩ := ih (Nat.le_of_lt hk_lt)
    have hActive := hkLSF hk_lt (st.bran k) (hInv.hBran k hk_lt)
    have hSp := hActive.2
    have hGeq : st.G (k + 1) = T.S (st.scState k) (st.bran k) := hInv.hGSucc k hk_lt
    have hk1Valid : (st.G (k + 1)).IsValid := by
      rw [hGeq]
      have hCore := coreGraph_isValid hkValid hActive.1.2.1
      intro e he
      have hEnd := hSp.1.2.2 e he
      have hc := hCore e (hSp.1.2.1 he)
      rw [hEnd.1, hEnd.2]
      exact ⟨hSp.2.1.1 hc.1, hSp.2.1.1 hc.2⟩
    have hk1V : (st.G (k + 1)).V ⊆ (st.G 0).V := by
      have hsub : (st.G (k + 1)).V ⊆ (st.G k).V := by
        rw [hGeq]
        exact Finset.Subset.trans hSp.1.1 hActive.1.2.1.2.2.1
      exact Finset.Subset.trans hsub hkV
    have hk1m : ((st.G (k + 1)).m : ℝ) ≤ (levelM TP P (k + 1) : ℝ) := by
      rw [hGeq]
      exact_mod_cast levelM_step_nat hTP hγk hSp.2.2.2.2.2
    have hk1ℓ : ∀ e ∈ (st.G (k + 1)).E, 0 < st.toTreeChain.chainLen st.ℓ (k + 1) e := by
      intro e he
      rw [hGeq] at he
      have heGk : e ∈ (st.G k).E := (Finset.mem_sdiff.mp (hSp.1.2.1 he)).1
      have hw1 : 1 ≤ (T.lsfs (st.scState k) (st.bran k)).wstr e := by
        have hnonneg : ∀ f ∈ (st.G k).E, 0 ≤ st.toTreeChain.chainLen st.ℓ k f :=
          fun f hf => (hkℓ f hf).le
        have h1 := one_le_stretch hActive.1.2.1.2.2.2.2 hnonneg heGk
        exact le_trans h1 (hActive.1.2.2.2 e heGk).1
      simp only [TreeChain.chainLen, coreLen, TreeChain.activeLSF, ChainState.toTreeChain,
        hk_lt, ↓reduceIte]
      exact mul_pos (lt_of_lt_of_le zero_lt_one hw1) (hkℓ e heGk)
    refine ⟨hk1Valid, hk1V, hk1m, hk1ℓ, fun hk1_lt j hj => ?_⟩
    obtain ⟨H⟩ := hInv.hHist (k + 1) hk1_lt
    have hSpec := H.hOK.noHidden P.k H.len (levelM TP P (k + 1)) N₀ H.D H.ord H.restarts
      P.hk H.hG0 H.hD H.hLen H.hℓPos H.hOrd H.hInitMBound H.hInitNBound H.hRestartsLt
      (by rw [H.hUpd]; exact H.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hAt := hSpec.1 H.len (le_refl _) j hj
    dsimp only at hAt
    rw [H.hEndG, ← H.hRun] at hAt
    have hn_le : (st.G (k + 1)).n ≤ (st.G 0).n := Finset.card_le_card hk1V
    have hHolds : (T.lsfs (st.scState (k + 1)) j).Holds (st.G (k + 1))
        (st.toTreeChain.chainLen st.ℓ (k + 1)) (TP.σ P.k (st.G 0).n) := by
      have h1 := LSF.Holds.congr_len hAt.1 fun e he => H.hEndℓ e he
      exact LSF.Holds.mono_σ h1 (hTP.2.1 _ _ _ _ (le_refl _) hn_le)
    have hm_init_le : levelM TP P (k + 1) ≤ P.M₀ ^ 2 := levelM_le_sq hTP hγM₀ hγk (k + 1)
    have hSp' : IsSparsifiedCoreGraphAt (st.G (k + 1)) (T.lsfs (st.scState (k + 1)) j)
        (st.toTreeChain.chainLen st.ℓ (k + 1)) (P.k : ℝ) (TP.γ_ℓ (P.M₀ ^ 2)) (TP.γ_c (P.M₀ ^ 2))
        (levelM TP P (k + 1)) (T.S (st.scState (k + 1)) j) (T.emb (st.scState (k + 1)) j) := by
      have h2 := hAt.2.1
      have h2' : IsSparsifiedCoreGraphAt (st.G (k + 1)) (T.lsfs (st.scState (k + 1)) j)
          (st.toTreeChain.chainLen st.ℓ (k + 1)) (P.k : ℝ)
          (TP.γ_ℓ (levelM TP P (k + 1))) (TP.γ_c (levelM TP P (k + 1))) (levelM TP P (k + 1))
          (T.S (st.scState (k + 1)) j) (T.emb (st.scState (k + 1)) j) := by
        rcases h2 with ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩
        refine ⟨hs1, hs2, fun e he e' he' => ?_, hs4, hs5, hs6⟩
        have he1 : e ∈ (st.G (k + 1)).E := (Finset.mem_sdiff.mp he).1
        have he'1 : e' ∈ (st.G (k + 1)).E := by
          have he'S : e' ∈ (T.S (st.scState (k + 1)) j).E := mem_E_of_mem_walkEdges (hs2.2 e he) he'
          exact (Finset.mem_sdiff.mp (hs1.2.1 he'S)).1
        simpa [coreLen, H.hEndℓ e he1, H.hEndℓ e' he'1] using hs3 e he e' he'
      exact isSparsifiedCoreGraphAt_mono h2' hk_pos (le_trans zero_le_one (hTP.2.2.1 _))
        (hTP.2.2.2.1 _ _ hm_init_le) (hTP.2.2.2.2.2.1 _ _ hm_init_le) le_rfl
    exact ⟨hHolds, hSp'⟩

/-- `ChainInv` implies the full `TreeChain.Holds`, `LastLevelSpans`, and `EmbedsSurviving`
guarantees on `st.toTreeChain`. -/
theorem ChainInv.toTreeChain_holds_noHidden {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    {σ_mwu : ℕ → ℝ} (hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → σ_mwu n₁ ≤ σ_mwu n₂)
    (hTP : TP.Valid) (hLP : LP.Valid)
    (hMWU : T.ToolMWUOrdRestartNoHiddenLe σ_mwu (P.M₀ ^ 2))
    (hEmb : T.ToolEmbedsSurvivingOrdRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) :
    let σ_tot := max (TP.σ P.k (st.G 0).n) (LP.σ_last (st.G 0).n)
    let σ_mwu_tot := max (σ_mwu (st.G 0).n) (LP.σ_mwu (st.G 0).n)
    st.toTreeChain.Holds (st.G 0) st.ℓ σ_tot σ_mwu_tot (TP.γ_ℓ (P.M₀ ^ 2)) (TP.γ_c (P.M₀ ^ 2)) ∧
    st.toTreeChain.LastLevelSpans ∧
    st.toTreeChain.EmbedsSurviving := by
  have hB := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInv
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, hInv.hG0Valid, P.hk, hInv.hLastK, ?_, hInv.hLastBran, ?_, ?_⟩
    · intro i hi
      refine ⟨hInv.hBran i hi, ?_, ?_, ?_⟩
      · intro j hj
        have hij := (hB i (Nat.le_of_lt hi)).2.2.2.2 hi j hj
        exact ⟨LSF.Holds.mono_σ hij.1 (le_max_left _ _), hij.2.toNoSize⟩
      · intro e he
        obtain ⟨H⟩ := hInv.hHist i hi
        have hm := hMWU P.k H.len (levelM TP P i) N₀ H.D H.ord H.restarts
          (levelM_le_sq hTP hγM₀ hγk i) P.hk H.hG0 H.hD H.hLen H.hℓPos H.hOrd H.hInitMBound H.hInitNBound H.hRestartsLt
          (by rw [H.hUpd]; exact H.hThresh) H.len (le_refl _) e (H.hEndG ▸ he)
        have hn_le : (st.G i).n ≤ (st.G 0).n :=
          Finset.card_le_card (hB i (Nat.le_of_lt hi)).2.1
        rw [H.hEndG, ← H.hRun] at hm
        exact le_trans hm (le_trans (hσ_mwu_mono _ _ hn_le) (le_max_left _ _))
      · simpa [ChainState.toTreeChain] using hInv.hGSucc i hi
    · intro j hj
      have hn_le : (st.G P.d).n ≤ (st.G 0).n :=
        Finset.card_le_card (hB P.d (le_refl P.d)).2.1
      exact LSF.Holds.mono_σ (hInv.hLastHolds j hj)
        (le_trans (hLP.2.1 _ _ hn_le) (le_max_right _ _))
    · intro e he
      have hn_le : (st.G P.d).n ≤ (st.G 0).n :=
        Finset.card_le_card (hB P.d (le_refl P.d)).2.1
      exact le_trans (hInv.hLastMWU e he) (le_trans (hLP.2.2.2.1 _ _ hn_le) (le_max_right _ _))
  · intro u hu v hv hconn
    simp only [TreeChain.activeLSF, ChainState.toTreeChain, lt_irrefl, ↓reduceIte]
    exact hInv.hLastSpans st.lastBran hInv.hLastBran u hu v hv hconn
  · intro i hi e he
    obtain ⟨H⟩ := hInv.hHist i hi
    have heS : e ∈ (T.S (st.scState i) (st.bran i)).E := by
      have hGeq := hInv.hGSucc i hi
      change e ∈ (st.G (i + 1)).E at he
      rw [← hGeq]; exact he
    have he' := hEmb P.k H.len (levelM TP P i) N₀ H.D H.ord H.restarts
      P.hk H.hG0 H.hD H.hLen H.hℓPos H.hOrd H.hInitMBound H.hInitNBound H.hRestartsLt
      (by rw [H.hUpd]; exact H.hThresh) H.len (le_refl _) (st.bran i) (hInv.hBran i hi) e
      (H.hRun ▸ heS)
    have hi' : i < P.d := hi
    dsimp only [ChainState.toTreeChain] at he ⊢
    rw [← H.hRun] at he'
    change (if i < P.d then T.emb (st.scState i) (st.bran i) else fun _ => []) e = [(e, true)]
    rw [ite_eq_left_iff.mpr (fun h => absurd hi' h)]
    exact he'

/-- Under `ChainInv`, lengths in `[e^{-Λ}, e^Λ]` at level `0` give the range `LevelLenRange` at
every level `i ≤ P.d`: each level multiplies the length of an edge it keeps by its stretch, which
lies in `[1, σ]` (`level_bounds_aux_noHidden`). -/
theorem chainInv_levelLenRange {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) {Λ : ℝ}
    (hℓ : LenInRange Λ (st.G 0) st.ℓ) :
    ∀ i ≤ P.d, LevelLenRange TP P N₀ Λ i (st.G i) (st.toTreeChain.chainLen st.ℓ i) := by
  intro i hi e he
  have hLvl := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInv
  set σ_cap := max (2 : ℝ) (TP.σ P.k N₀)
  have hσ_le_cap : TP.σ P.k (st.G 0).n ≤ σ_cap :=
    le_trans (hTP.2.1 _ _ _ _ le_rfl hInv.hG0n) (le_max_right _ _)
  have hσ_cap_pos : 0 ≤ σ_cap := le_trans zero_le_two (le_max_left _ _)
  induction i generalizing e with
  | zero =>
    simpa [TreeChain.chainLen] using hℓ e he
  | succ i ih =>
    have hi_lt : i < P.d := hi
    have hBi := (hLvl i (Nat.le_of_lt hi_lt)).2.2.2.2 hi_lt (st.bran i) (hInv.hBran i hi_lt)
    rw [hInv.hGSucc i hi_lt] at he
    have heCore : e ∈ (coreGraph (st.G i) (T.lsfs (st.scState i) (st.bran i))).E :=
      hBi.2.1.2.1 he
    have heGi : e ∈ (st.G i).E := (Finset.mem_sdiff.mp heCore).1
    have hPrev := ih (Nat.le_of_lt hi_lt) e heGi
    have hℓ_pos : ∀ f ∈ (st.G i).E, 0 ≤ st.toTreeChain.chainLen st.ℓ i f := fun f hf =>
      (hLvl i (Nat.le_of_lt hi_lt)).2.2.2.1 f hf |>.le
    have hstr1 : 1 ≤ (T.lsfs (st.scState i) (st.bran i)).wstr e :=
      le_trans (one_le_stretch hBi.1.2.1.2.2.2.2 hℓ_pos heGi) (hBi.1.2.2.2 e heGi).1
    have hw_le : (T.lsfs (st.scState i) (st.bran i)).wstr e ≤ σ_cap :=
      le_trans (hBi.1.2.2.2 e heGi).2 hσ_le_cap
    have hcl_eq : st.toTreeChain.chainLen st.ℓ (i + 1) e =
        (T.lsfs (st.scState i) (st.bran i)).wstr e * st.toTreeChain.chainLen st.ℓ i e := by
      simp [TreeChain.chainLen, coreLen, TreeChain.activeLSF, ChainState.toTreeChain, hi_lt]
    have h0 : 0 ≤ st.toTreeChain.chainLen st.ℓ i e := le_trans (Real.exp_pos _).le hPrev.1
    rw [hcl_eq]
    refine ⟨?_, ?_⟩
    · calc Real.exp (-Λ) ≤ st.toTreeChain.chainLen st.ℓ i e := hPrev.1
        _ = 1 * st.toTreeChain.chainLen st.ℓ i e := (one_mul _).symm
        _ ≤ (T.lsfs (st.scState i) (st.bran i)).wstr e * st.toTreeChain.chainLen st.ℓ i e :=
            mul_le_mul_of_nonneg_right hstr1 h0
    · calc (T.lsfs (st.scState i) (st.bran i)).wstr e * st.toTreeChain.chainLen st.ℓ i e
          ≤ σ_cap * (Real.exp Λ * σ_cap ^ i) := mul_le_mul hw_le hPrev.2 h0 hσ_cap_pos
        _ = Real.exp Λ * σ_cap ^ (i + 1) := by rw [pow_succ]; ring

end LevelBounds

section BudgetMonotonicity

lemma opRuntimeBudget_mono {TP : SparseCoreParams} {LP : LastLevelParams}
    (hTP : TP.Valid) (hLP : LP.Valid) (P : ChainParams) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) (i₀ : ℕ) :
    opRuntimeBudget TP LP P n₁ i₀ ≤ opRuntimeBudget TP LP P n₂ i₀ := by
  unfold opRuntimeBudget
  exact mul_le_mul_of_nonneg_left (Chain.opRuntimeBudget_mono hTP hLP P hn i₀) (by positivity)

lemma activeRestartCap_nonneg {TP : SparseCoreParams} (hTP : TP.Valid) (P : ChainParams)
    (n : ℕ) (cRest : ℕ → ℕ) : 0 ≤ activeRestartCap TP P n cRest := by
  unfold activeRestartCap
  exact mul_nonneg (by positivity) (Chain.activeRestartCap_nonneg hTP P n cRest)

lemma activeRestartCap_zero (TP : SparseCoreParams) (P : ChainParams) (n : ℕ) :
    activeRestartCap TP P n (fun _ => 0) = 0 := by
  simp [activeRestartCap, Chain.activeRestartCap_zero]

lemma ChainBudgetInvWith.mono_n {T : SparseCoreRestartTool} {P : ChainParams}
    {TP : SparseCoreParams} {LP : LastLevelParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) {st : ChainState T P} {overflow : ℝ}
    (hB : ChainBudgetInvWith TP LP N₀ st overflow) {n' : ℕ} (hn : N₀ ≤ n') :
    (st.closedRuntime : ℝ) ≤
      ∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
          opRuntimeBudget TP LP P n' i + overflow := by
  have hRestartNN : 0 ≤ activeRestartCap TP P N₀ st.curRestarts :=
    activeRestartCap_nonneg hTP P N₀ st.curRestarts
  refine le_trans (le_trans (le_add_of_nonneg_right hRestartNN) hB.1)
    (add_le_add (Finset.sum_le_sum fun i _ => ?_) le_rfl)
  exact mul_le_mul_of_nonneg_left (opRuntimeBudget_mono hTP hLP P hn i) (Nat.cast_nonneg _)

lemma ChainBudgetInv.mono_n {T : SparseCoreRestartTool} {P : ChainParams}
    {TP : SparseCoreParams} {LP : LastLevelParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) {st : ChainState T P}
    (hB : ChainBudgetInv TP LP N₀ st) {n' : ℕ} (hn : N₀ ≤ n') :
    (st.closedRuntime : ℝ) ≤
      ∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
          opRuntimeBudget TP LP P n' i := by
  simpa using hB.toWith.mono_n hTP hLP hn

/-- Clearing active restarts at levels `[i₀, P.d)` retires their `((P.k : ℝ) + 1)`-scaled restart
allowances from `activeRestartCap`. -/
lemma activeRestartCap_rebuild (TP : SparseCoreParams) (P : ChainParams) (n i₀ : ℕ)
    (hi₀ : i₀ ≤ P.d) (cRest : ℕ → ℕ) :
    activeRestartCap TP P n (fun j => if i₀ ≤ j ∧ j < P.d then 0 else cRest j) +
      ((P.k : ℝ) + 1) * ∑ j ∈ Finset.Ico i₀ P.d, (cRest j : ℝ) * restartCostCap TP P n j =
    activeRestartCap TP P n cRest := by
  unfold activeRestartCap
  rw [← mul_add, Chain.activeRestartCap_rebuild TP P n i₀ hi₀ cRest]

/-- Incrementing active restarts at `i₀` and clearing `[i₀ + 1, P.d)` retires the suffix allowances
and adds `((P.k : ℝ) + 1) * restartCostCap TP P n i₀`. -/
lemma activeRestartCap_shift (TP : SparseCoreParams) (P : ChainParams) (n i₀ : ℕ)
    (hi₀ : i₀ < P.d) (cRest : ℕ → ℕ) :
    activeRestartCap TP P n (fun j =>
      if j = i₀ then cRest i₀ + 1 else if i₀ + 1 ≤ j ∧ j < P.d then 0 else cRest j) +
      ((P.k : ℝ) + 1) * ∑ j ∈ Finset.Ico (i₀ + 1) P.d, (cRest j : ℝ) * restartCostCap TP P n j =
    activeRestartCap TP P n cRest + ((P.k : ℝ) + 1) * restartCostCap TP P n i₀ := by
  unfold activeRestartCap
  rw [← mul_add, Chain.activeRestartCap_shift TP P n i₀ hi₀ cRest, mul_add]

end BudgetMonotonicity

end MinCostFlow.Chain.Ordered
