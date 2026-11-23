module

public import MinCostFlow.Chain.Algorithm1
public import MinCostFlow.Chain.SparseCoreNoHidden
import MinCostFlow.Chain.EncodingSize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Invariant and cost preservation for Algorithm 1

This file proves that `initialize`, `rebuild`, `shift`, and `update` of `Algorithm 1` preserve
`ChainInv` (hence `TreeChain.Holds`, `LastLevelSpans`, `EmbedsSurviving`, and the level size
bounds) and `ChainBudgetInv` (bounding `closedRuntime` and `closedTreeUpdates` in terms of
`shiftCount`, `rebuildCount`, and `updCount`).
-/

@[expose] public section

namespace MinCostFlow.Chain

section LogHelpers

private lemma log_two_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
  have h1 : (1 / 2 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := by
    have := Real.add_one_lt_exp (show -(1 / 2 : ℝ) ≠ 0 by norm_num)
    linarith
  have h2 : Real.exp (1 / 2 : ℝ) < 2 := by
    rw [Real.exp_neg] at h1
    have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
    rw [lt_inv_comm₀ (by norm_num) hpos] at h1
    linarith
  rw [← Real.log_exp (1 / 2 : ℝ)]
  exact Real.log_lt_log (Real.exp_pos _) h2

lemma log_add_two_pos (x : ℝ) (hx : 0 ≤ x) : 0 < Real.log (x + 2) := by
  have h1 : (1 : ℝ) < x + 2 := by linarith
  exact Real.log_pos h1

lemma log_add_two_gt_half (x : ℝ) (hx : 0 ≤ x) : (1 / 2 : ℝ) < Real.log (x + 2) := by
  have h2 : (2 : ℝ) ≤ x + 2 := by linarith
  exact lt_of_lt_of_le log_two_gt_half (Real.log_le_log (by norm_num) h2)

lemma updateThreshold_nonneg (k m₀ n₀ : ℕ) : 0 ≤ SparseCoreTool.updateThreshold k m₀ n₀ := by
  unfold SparseCoreTool.updateThreshold
  positivity

lemma updateThreshold_le_four_div (k m₀ n₀ : ℕ) (hk : 0 < k) :
    SparseCoreTool.updateThreshold k m₀ n₀ ≤ 4 * (m₀ : ℝ) / (k : ℝ) := by
  unfold SparseCoreTool.updateThreshold
  have hlog : (1 / 2 : ℝ) < Real.log ((n₀ : ℝ) + 2) := log_add_two_gt_half n₀ (Nat.cast_nonneg n₀)
  have hsq : (1 / 4 : ℝ) ≤ (Real.log ((n₀ : ℝ) + 2)) ^ 2 := by nlinarith
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hden : (k : ℝ) * (1 / 4 : ℝ) ≤ (k : ℝ) * (Real.log ((n₀ : ℝ) + 2)) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hk_pos.le
  have hden_pos : (0 : ℝ) < (k : ℝ) * (1 / 4 : ℝ) := by positivity
  calc
    (m₀ : ℝ) / ((k : ℝ) * (Real.log ((n₀ : ℝ) + 2)) ^ 2)
        ≤ (m₀ : ℝ) / ((k : ℝ) * (1 / 4 : ℝ)) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg m₀) hden_pos hden
    _ = 4 * (m₀ : ℝ) / (k : ℝ) := by ring

lemma max_one_threshold_le_of_lt {k m₀ n₀ upd : ℕ}
    (h : SparseCoreTool.updateThreshold k m₀ n₀ < (upd : ℝ)) :
    max (1 : ℝ) (SparseCoreTool.updateThreshold k m₀ n₀) ≤ (upd : ℝ) := by
  by_cases h1 : SparseCoreTool.updateThreshold k m₀ n₀ ≤ 1
  · rw [max_eq_left h1]
    have hpos : (0 : ℝ) < (upd : ℝ) := lt_of_le_of_lt (updateThreshold_nonneg k m₀ n₀) h
    have hnat : 0 < upd := by exact_mod_cast hpos
    exact_mod_cast hnat
  · push Not at h1
    rw [max_eq_right h1.le]
    exact h.le

private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  simpa only [Real.log_exp] using Real.log_le_log (by norm_num) h2

private lemma log_add_two_le_clog (n : ℕ) :
    Real.log ((n : ℝ) + 2) ≤ (Nat.clog 2 (n + 2) : ℝ) := by
  have hpow : ((n + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 (n + 2) := by
    exact_mod_cast Nat.le_pow_clog Nat.one_lt_two (n + 2)
  have hlog : Real.log ((n : ℝ) + 2) ≤ (Nat.clog 2 (n + 2) : ℝ) * Real.log 2 := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) + 2) (by simpa using hpow)
    simpa only [Real.log_pow] using h
  exact hlog.trans (mul_le_of_le_one_right (Nat.cast_nonneg _) log_two_le_one)

private lemma clog_add_two_le_four_log (n : ℕ) :
    (Nat.clog 2 (n + 2) : ℝ) ≤ 4 * Real.log ((n : ℝ) + 2) := by
  have hcl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos Nat.one_lt_two (by omega)
  have hpow : (2 : ℝ) ^ (Nat.clog 2 (n + 2) - 1) ≤ (n : ℝ) + 2 := by
    have h := (Nat.pow_pred_clog_lt_self Nat.one_lt_two (by omega : 1 < n + 2)).le
    exact_mod_cast h
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (Nat.clog 2 (n + 2) - 1)) hpow
  rw [Real.log_pow, Nat.cast_sub hcl, Nat.cast_one] at hlog
  have hlog2_pos : 0 < Real.log 2 := lt_trans (by norm_num) log_two_gt_half
  have hdiv : (Nat.clog 2 (n + 2) : ℝ) - 1 ≤ Real.log ((n : ℝ) + 2) / Real.log 2 :=
    (le_div_iff₀ hlog2_pos).mpr hlog
  have hN0 : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hhalf : (1 / 2 : ℝ) < Real.log 2 := log_two_gt_half
  have h2 : Real.log ((n : ℝ) + 2) / Real.log 2 ≤ 2 * Real.log ((n : ℝ) + 2) := by
    apply (div_le_iff₀ hlog2_pos).mpr
    nlinarith [hhalf, hN0]
  nlinarith [hdiv, h2, hN0, hhalf]

/-- The integer rebuild threshold stays within the paper's real sparse-core update
budget `M_i / (k log² N₀)` for every valid `TP` and every level `i`. -/
lemma intRebuildThreshold_le_updateThreshold {TP : SparseCoreParams} {P : ChainParams}
    (hTP : TP.Valid) (N₀ i : ℕ) :
    (intRebuildThreshold P N₀ i : ℝ) ≤
      SparseCoreTool.updateThreshold P.k (levelM TP P i) N₀ := by
  unfold intRebuildThreshold SparseCoreTool.updateThreshold
  let b := Nat.clog 2 (N₀ + 2)
  let L := Real.log ((N₀ : ℝ) + 2)
  let D := P.k ^ (i + 1) * b ^ 2
  have hk_pos : (0 : ℝ) < (P.k : ℝ) := Nat.cast_pos.mpr P.hk
  have hL_pos : 0 < L := log_add_two_pos N₀ (Nat.cast_nonneg _)
  have hLb : L ≤ (b : ℝ) := log_add_two_le_clog N₀
  have hD_cast : (D : ℝ) = (P.k : ℝ) ^ (i + 1) * (b : ℝ) ^ 2 := by
    dsimp [D]; push_cast; rfl
  have hD_ge : (P.k : ℝ) ^ (i + 1) * L ^ 2 ≤ (D : ℝ) := by
    rw [hD_cast]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL_pos.le hLb 2) (by positivity)
  have hdiv : ((P.M₀ / D : ℕ) : ℝ) * (D : ℝ) ≤ (P.M₀ : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self P.M₀ D
  have hstep1 : ((P.M₀ / D : ℕ) : ℝ) ≤ (P.M₀ : ℝ) / ((P.k : ℝ) ^ (i + 1) * L ^ 2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    exact (mul_le_mul_of_nonneg_left hD_ge (Nat.cast_nonneg _)).trans hdiv
  have hM_le : (P.M₀ : ℝ) / (P.k : ℝ) ^ i ≤ (levelM TP P i : ℝ) := by
    have hγℓ : 1 ≤ TP.γ_ℓ (P.M₀ ^ 2) := hTP.2.2.1 (P.M₀ ^ 2)
    have hinv : (1 / (P.k : ℝ)) ^ i ≤ (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ i :=
      pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hγℓ hk_pos.le) i
    have h1 : (P.M₀ : ℝ) / (P.k : ℝ) ^ i = (P.M₀ : ℝ) * (1 / (P.k : ℝ)) ^ i := by
      rw [one_div, inv_pow, div_eq_mul_inv]
    rw [h1]
    exact le_trans (mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _))
      (gamma_div_pow_le_levelM hTP P i)
  have hstep2 : (P.M₀ : ℝ) / ((P.k : ℝ) ^ (i + 1) * L ^ 2) ≤
      (levelM TP P i : ℝ) / ((P.k : ℝ) * L ^ 2) := by
    calc (P.M₀ : ℝ) / ((P.k : ℝ) ^ (i + 1) * L ^ 2)
        = ((P.M₀ : ℝ) / (P.k : ℝ) ^ i) / ((P.k : ℝ) * L ^ 2) := by rw [pow_succ]; ring
      _ ≤ (levelM TP P i : ℝ) / ((P.k : ℝ) * L ^ 2) :=
        div_le_div_of_nonneg_right hM_le (by positivity)
  exact hstep1.trans hstep2

end LogHelpers

section LevelBounds

lemma level_bounds_aux_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ)
    (hTP : TP.Valid) (hT : T.IsSpecRestartNoHidden TP)
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
    have hSpec := hT P.k H.len (levelM TP P 0) N₀ H.D H.restarts
      P.hk H.hG0 H.hD H.hLen H.hℓPos H.hInitMBound H.hInitNBound H.hRestartsLt
      (by rw [H.hUpd]; exact H.hThresh)
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
    have hSpec := hT P.k H.len (levelM TP P (k + 1)) N₀ H.D H.restarts
      P.hk H.hG0 H.hD H.hLen H.hℓPos H.hInitMBound H.hInitNBound H.hRestartsLt
      (by rw [H.hUpd]; exact H.hThresh)
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

lemma level_bounds_aux (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ)
    (hTP : TP.Valid) (hT : T.IsSpecRestart TP)
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
          (levelM TP P i) (T.S (st.scState i) j) (T.emb (st.scState i) j)) :=
  level_bounds_aux_noHidden T L TP LP P N₀ hTP hT.toNoHidden hγM₀ hγk hInv

theorem ChainInv.toTreeChain_holds_noHidden {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    {σ_mwu : ℕ → ℝ} (hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → σ_mwu n₁ ≤ σ_mwu n₂)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hMWU : T.ToolMWURestartNoHidden σ_mwu)
    (hEmb : T.ToolEmbedsSurvivingRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) :
    let σ_tot := max (TP.σ P.k (st.G 0).n) (LP.σ_last (st.G 0).n)
    let σ_mwu_tot := max (σ_mwu (st.G 0).n) (LP.σ_mwu (st.G 0).n)
    st.toTreeChain.Holds (st.G 0) st.ℓ σ_tot σ_mwu_tot (TP.γ_ℓ (P.M₀ ^ 2)) (TP.γ_c (P.M₀ ^ 2)) ∧
    st.toTreeChain.LastLevelSpans ∧
    st.toTreeChain.EmbedsSurviving := by
  have hB := level_bounds_aux_noHidden T L TP LP P N₀ hTP hT hγM₀ hγk hInv
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, hInv.hG0Valid, P.hk, hInv.hLastK, ?_, hInv.hLastBran, ?_, ?_⟩
    · intro i hi
      refine ⟨hInv.hBran i hi, ?_, ?_, ?_⟩
      · intro j hj
        have hij := (hB i (Nat.le_of_lt hi)).2.2.2.2 hi j hj
        exact ⟨LSF.Holds.mono_σ hij.1 (le_max_left _ _), hij.2.toNoSize⟩
      · intro e he
        obtain ⟨H⟩ := hInv.hHist i hi
        have hm := hMWU P.k H.len (levelM TP P i) N₀ H.D H.restarts
          P.hk H.hG0 H.hD H.hLen H.hℓPos H.hInitMBound H.hInitNBound H.hRestartsLt
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
    have he' := hEmb P.k H.len (levelM TP P i) N₀ H.D H.restarts
      P.hk H.hG0 H.hD H.hLen H.hℓPos H.hInitMBound H.hInitNBound H.hRestartsLt
      (by rw [H.hUpd]; exact H.hThresh) H.len (le_refl _) (st.bran i) (hInv.hBran i hi) e
      (H.hRun ▸ heS)
    have hi' : i < P.d := hi
    dsimp only [ChainState.toTreeChain] at he ⊢
    rw [← H.hRun] at he'
    change (if i < P.d then T.emb (st.scState i) (st.bran i) else fun _ => []) e = [(e, true)]
    rw [ite_eq_left_iff.mpr (fun h => absurd hi' h)]
    exact he'

theorem ChainInv.toTreeChain_holds {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    {σ_mwu : ℕ → ℝ} (hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → σ_mwu n₁ ≤ σ_mwu n₂)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP) (hMWU : T.ToolMWURestart σ_mwu)
    (hEmb : T.ToolEmbedsSurvivingRestart)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) :
    let σ_tot := max (TP.σ P.k (st.G 0).n) (LP.σ_last (st.G 0).n)
    let σ_mwu_tot := max (σ_mwu (st.G 0).n) (LP.σ_mwu (st.G 0).n)
    st.toTreeChain.Holds (st.G 0) st.ℓ σ_tot σ_mwu_tot (TP.γ_ℓ (P.M₀ ^ 2)) (TP.γ_c (P.M₀ ^ 2)) ∧
    st.toTreeChain.LastLevelSpans ∧
    st.toTreeChain.EmbedsSurviving :=
  hInv.toTreeChain_holds_noHidden hσ_mwu_mono hTP hLP
    hT.toNoHidden hMWU.toNoHidden hEmb.toNoHidden hγM₀ hγk

end LevelBounds

section BudgetDefinitions

/-- Polylogarithmic factor `L(n) = log(M₀ + n + 2)`. -/
noncomputable def logFactor (P : ChainParams) (n : ℕ) : ℝ :=
  Real.log ((P.M₀ : ℝ) + (n : ℝ) + 2)

/-- A triggered integer rebuild charges at least one sixteenth of the amortized floor
`M₀ / (k^{i+1} · (logFactor P N₀)²)`. -/
lemma m0_div_logFactor_le_sixteen_mul_intRebuildThreshold_succ
    (P : ChainParams) (N₀ i : ℕ) :
    (P.M₀ : ℝ) / ((P.k : ℝ) ^ (i + 1) * (logFactor P N₀) ^ 2) ≤
      16 * ((intRebuildThreshold P N₀ i : ℝ) + 1) := by
  unfold intRebuildThreshold
  let b := Nat.clog 2 (N₀ + 2)
  let L := Real.log ((N₀ : ℝ) + 2)
  let D := P.k ^ (i + 1) * b ^ 2
  have hk_pos : (0 : ℝ) < (P.k : ℝ) := Nat.cast_pos.mpr P.hk
  have hL_pos : 0 < L := log_add_two_pos N₀ (Nat.cast_nonneg _)
  have hb_pos : 0 < b := Nat.clog_pos Nat.one_lt_two (by omega)
  have hD_pos : 0 < D := Nat.mul_pos (pow_pos P.hk _) (pow_pos hb_pos 2)
  have hbl : (b : ℝ) ≤ 4 * L := clog_add_two_le_four_log N₀
  have hD_hi : (D : ℝ) ≤ 16 * ((P.k : ℝ) ^ (i + 1) * L ^ 2) := by
    have hD_cast : (D : ℝ) = (P.k : ℝ) ^ (i + 1) * (b : ℝ) ^ 2 := by
      dsimp [D]; push_cast; rfl
    rw [hD_cast]
    calc (P.k : ℝ) ^ (i + 1) * (b : ℝ) ^ 2
        ≤ (P.k : ℝ) ^ (i + 1) * (4 * L) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg b) hbl 2) (by positivity)
      _ = 16 * ((P.k : ℝ) ^ (i + 1) * L ^ 2) := by ring
  have hM_le : (P.M₀ : ℝ) ≤ (((P.M₀ / D : ℕ) : ℝ) + 1) * (D : ℝ) := by
    have h := (Nat.div_lt_iff_lt_mul hD_pos).mp (Nat.lt_succ_self (P.M₀ / D))
    exact_mod_cast h.le
  have hlog_le : L ≤ logFactor P N₀ := by
    unfold logFactor
    exact Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) N₀])
      (by linarith [Nat.cast_nonneg (α := ℝ) P.M₀])
  have hden_le : (P.k : ℝ) ^ (i + 1) * L ^ 2 ≤ (P.k : ℝ) ^ (i + 1) * (logFactor P N₀) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL_pos.le hlog_le 2) (by positivity)
  have hstep1 : (P.M₀ : ℝ) / ((P.k : ℝ) ^ (i + 1) * (logFactor P N₀) ^ 2) ≤
      (P.M₀ : ℝ) / ((P.k : ℝ) ^ (i + 1) * L ^ 2) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hden_le
  have hstep2 : (P.M₀ : ℝ) / ((P.k : ℝ) ^ (i + 1) * L ^ 2) ≤
      16 * (((P.M₀ / D : ℕ) : ℝ) + 1) := by
    apply (div_le_iff₀ (by positivity)).mpr
    calc (P.M₀ : ℝ)
        ≤ (((P.M₀ / D : ℕ) : ℝ) + 1) * (D : ℝ) := hM_le
      _ ≤ (((P.M₀ / D : ℕ) : ℝ) + 1) * (16 * ((P.k : ℝ) ^ (i + 1) * L ^ 2)) :=
          mul_le_mul_of_nonneg_left hD_hi (by positivity)
      _ = 16 * (((P.M₀ / D : ℕ) : ℝ) + 1) * ((P.k : ℝ) ^ (i + 1) * L ^ 2) := by ring
  exact hstep1.trans hstep2

/-- Per-level lifetime runtime cap for level `i < P.d` (covers `T.cost` + `curEnc`). -/
noncomputable def levelToolCap (TP : SparseCoreParams) (P : ChainParams) (n i : ℕ) : ℝ :=
  2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) *
    (P.k : ℝ) * TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P n) ^ TP.p_T +
  if i = 0 then
    200 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * Real.log (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2)
  else
    5 * TP.γ_r (P.M₀ ^ 2) *
      ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (i - 1) / (P.k : ℝ) + 1)

/-- Per-restart runtime cost cap for level `i < P.d`. -/
noncomputable def restartCostCap (TP : SparseCoreParams) (P : ChainParams) (n i : ℕ) : ℝ :=
  2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) *
    TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P n) ^ TP.p_T

/-- Cumulative active restart runtime allowance across levels `< P.d`. -/
noncomputable def activeRestartCap (TP : SparseCoreParams) (P : ChainParams) (n : ℕ)
    (curRestarts : ℕ → ℕ) : ℝ :=
  ∑ i ∈ Finset.range P.d, (curRestarts i : ℝ) * restartCostCap TP P n i

/-- Extra `batchEnc` cap for a single overflowing batch triggering `Rebuild(0)`. -/
noncomputable def extraEncCap (P : ChainParams) : ℝ :=
  40 * (P.M₀ : ℝ) * Real.log (2 * (P.M₀ : ℝ) + 2)

/-- Level-`d` rebuild runtime cap during one lifetime of `scState (P.d - 1)`. -/
noncomputable def lastCostCap (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams)
    (n : ℕ) : ℝ :=
  (4 * TP.γ_r (P.M₀ ^ 2) * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) *
      (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (P.d - 1) / (P.k : ℝ) +
    4 * TP.γ_r (P.M₀ ^ 2) + 1) *
    (LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
      (2 * logFactor P n) ^ LP.p_last)

/-- Runtime budget retired by one invocation of `Rebuild(i₀)` or `Shift(i₀)`. -/
noncomputable def opRuntimeBudget (TP : SparseCoreParams) (LP : LastLevelParams)
    (P : ChainParams) (n i₀ : ℕ) : ℝ :=
  (if i₀ < P.d then (Finset.Ico i₀ P.d).sum (levelToolCap TP P n) else 0) +
  lastCostCap TP LP P n +
  (if i₀ = 0 then extraEncCap P else 0)

/-- Per-level decremental tree-update cap (`i < P.d`). -/
noncomputable def levelDecCap (TP : SparseCoreParams) (P : ChainParams) (i : ℕ) : ℝ :=
  5 * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1)

/-- Level-`d` tree-update cap during one lifetime of `scState (P.d - 1)`. -/
noncomputable def lastTreeCap (TP : SparseCoreParams) (P : ChainParams) : ℝ :=
  2 * (4 * TP.γ_r (P.M₀ ^ 2) * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) *
        (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (P.d - 1) / (P.k : ℝ)) +
    4 * TP.γ_r (P.M₀ ^ 2)) * (levelM TP P P.d : ℝ)

/-- Tree-update bound for replacing `T^𝒢` from level `i₀` to `P.d`. -/
noncomputable def diffTreeCap (TP : SparseCoreParams) (P : ChainParams) (i₀ : ℕ) : ℝ :=
  2 * (Finset.Ico i₀ (P.d + 1)).sum (fun j => (levelM TP P j : ℝ))

/-- Tree-update budget retired by one invocation of `Rebuild(i₀)` or `Shift(i₀)`. -/
noncomputable def opTreeBudget (TP : SparseCoreParams) (P : ChainParams) (i₀ : ℕ) : ℝ :=
  (if i₀ < P.d then (Finset.Ico i₀ P.d).sum (levelDecCap TP P) else 0) +
  lastTreeCap TP P +
  diffTreeCap TP P i₀

/-- Amortized budget invariant maintained alongside `ChainInv`. -/
def ChainBudgetInv {T : SparseCoreRestartTool} {P : ChainParams}
    (TP : SparseCoreParams) (LP : LastLevelParams) (N₀ : ℕ) (st : ChainState T P) : Prop :=
  (st.closedRuntime : ℝ) + activeRestartCap TP P N₀ st.curRestarts ≤
    ∑ i ∈ Finset.range (P.d + 1),
      ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
        opRuntimeBudget TP LP P N₀ i ∧
  (st.closedTreeUpdates : ℝ) ≤
    diffTreeCap TP P 0 +
    ∑ i ∈ Finset.range (P.d + 1),
      ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
        opTreeBudget TP P i

/-- Amortized budget invariant with an explicit extra runtime allowance `overflow` (for external
batches of length exceeding `P.M₀`). -/
def ChainBudgetInvWith {T : SparseCoreRestartTool} {P : ChainParams}
    (TP : SparseCoreParams) (LP : LastLevelParams) (N₀ : ℕ) (st : ChainState T P)
    (overflow : ℝ) : Prop :=
  (st.closedRuntime : ℝ) + activeRestartCap TP P N₀ st.curRestarts ≤
    ∑ i ∈ Finset.range (P.d + 1),
      ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
        opRuntimeBudget TP LP P N₀ i + overflow ∧
  (st.closedTreeUpdates : ℝ) ≤
    diffTreeCap TP P 0 +
    ∑ i ∈ Finset.range (P.d + 1),
      ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
        opTreeBudget TP P i

lemma ChainBudgetInv.toWith {T : SparseCoreRestartTool} {P : ChainParams}
    {TP : SparseCoreParams} {LP : LastLevelParams} {N₀ : ℕ} {st : ChainState T P}
    (hB : ChainBudgetInv TP LP N₀ st) : ChainBudgetInvWith TP LP N₀ st 0 :=
  ⟨by simpa using hB.1, hB.2⟩

lemma ChainBudgetInvWith.toZero {T : SparseCoreRestartTool} {P : ChainParams}
    {TP : SparseCoreParams} {LP : LastLevelParams} {N₀ : ℕ} {st : ChainState T P}
    (hB : ChainBudgetInvWith TP LP N₀ st 0) : ChainBudgetInv TP LP N₀ st :=
  ⟨by simpa using hB.1, hB.2⟩

end BudgetDefinitions

section DynamicHelpers2

lemma applyUpdate_E_card_le (G : MGraph) (u : Update) :
    (G.applyUpdate u).E.card ≤ G.E.card + 1 := by
  cases u with
  | insert e _ _ =>
    simpa [MGraph.applyUpdate] using Finset.card_insert_le e G.E
  | delete e =>
    have : (G.applyUpdate (.delete e)).E.card ≤ G.E.card :=
      Finset.card_le_card (Finset.erase_subset e G.E)
    omega
  | split _ _ _ _ =>
    simp [MGraph.applyUpdate]

lemma applyBatch_E_card_le (G : MGraph) (U : List Update) :
    (G.applyBatch U).E.card ≤ G.E.card + U.length := by
  induction U generalizing G with
  | nil => simp [MGraph.applyBatch]
  | cons u U ih =>
    simp only [MGraph.applyBatch, List.foldl_cons, List.length_cons]
    have h1 := ih (G.applyUpdate u)
    change (List.foldl MGraph.applyUpdate (G.applyUpdate u) U).E.card ≤
      (G.applyUpdate u).E.card + U.length at h1
    have h2 := applyUpdate_E_card_le G u
    omega

lemma Finset.sum_Icc_one_succ (f : ℕ → ℕ) (k : ℕ) :
    (Finset.Icc 1 (k + 1)).sum f = (Finset.Icc 1 k).sum f + f (k + 1) := by
  have hEq : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hNot : k + 1 ∉ Finset.Icc 1 k := by simp
  rw [hEq, Finset.sum_insert hNot, add_comm]

lemma dynamic_V_subset {D : DynamicInstance} {len : ℕ}
    (hD : D.IsValid len) : ∀ t ≤ len, (D.G 0).V ⊆ (D.G t).V := by
  intro t
  induction t with
  | zero => intro _; exact Finset.Subset.refl _
  | succ k ih =>
    intro hk
    have hk_le : k ≤ len := Nat.le_of_succ_le hk
    have hstep := (hD (k + 1) (by omega) hk).2
    rw [hstep]
    exact Finset.Subset.trans (ih hk_le) (applyBatch_V_subset (D.G k) (D.U (k + 1)))

lemma dynamic_n_le {D : DynamicInstance} {len : ℕ}
    (hD : D.IsValid len) {t : ℕ} (ht : t ≤ len) : (D.G 0).n ≤ (D.G t).n :=
  Finset.card_le_card (dynamic_V_subset hD t ht)

lemma dynamic_m_le {D : DynamicInstance} {len : ℕ}
    (hD : D.IsValid len) : ∀ t ≤ len,
      (D.G t).m ≤ (D.G 0).m + (Finset.Icc 1 t).sum (fun s => (D.U s).length) := by
  intro t
  induction t with
  | zero => intro _; simp [MGraph.m]
  | succ k ih =>
    intro hk
    have hk_le : k ≤ len := Nat.le_of_succ_le hk
    have hstep := (hD (k + 1) (by omega) hk).2
    have hcard : (D.G (k + 1)).m ≤ (D.G k).m + (D.U (k + 1)).length := by
      unfold MGraph.m
      rw [hstep]
      exact applyBatch_E_card_le (D.G k) (D.U (k + 1))
    rw [Finset.sum_Icc_one_succ]
    have ihk := ih hk_le
    omega

lemma diffTreeChanges_length_triangle (A B C : Finset ℕ) :
    (diffTreeChanges A C).length ≤ (diffTreeChanges A B).length + (diffTreeChanges B C).length := by
  simp only [diffTreeChanges_length]
  have h1 : A \ C ⊆ (A \ B) ∪ (B \ C) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B <;> [exact Or.inr ⟨hxB, hx.2⟩; exact Or.inl ⟨hx.1, hxB⟩]
  have h2 : C \ A ⊆ (C \ B) ∪ (B \ A) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
    by_cases hxB : x ∈ B <;> [exact Or.inr ⟨hxB, hx.2⟩; exact Or.inl ⟨hx.1, hxB⟩]
  have hc1 := le_trans (Finset.card_le_card h1) (Finset.card_union_le (A \ B) (B \ C))
  have hc2 := le_trans (Finset.card_le_card h2) (Finset.card_union_le (C \ B) (B \ A))
  omega

lemma diffTreeChanges_length_biUnion {ι : Type*} (I : Finset ι) (A B : ι → Finset ℕ) :
    (diffTreeChanges (I.biUnion A) (I.biUnion B)).length ≤
      I.sum (fun i => (diffTreeChanges (A i) (B i)).length) := by
  simp only [diffTreeChanges_length]
  have h1 : I.biUnion A \ I.biUnion B ⊆ I.biUnion (fun i => A i \ B i) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, not_exists, not_and] at hx ⊢
    obtain ⟨⟨i, hi, hxA⟩, hnot⟩ := hx
    exact ⟨i, hi, hxA, hnot i hi⟩
  have h2 : I.biUnion B \ I.biUnion A ⊆ I.biUnion (fun i => B i \ A i) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, not_exists, not_and] at hx ⊢
    obtain ⟨⟨i, hi, hxB⟩, hnot⟩ := hx
    exact ⟨i, hi, hxB, hnot i hi⟩
  have hc1 := le_trans (Finset.card_le_card h1) Finset.card_biUnion_le
  have hc2 := le_trans (Finset.card_le_card h2) Finset.card_biUnion_le
  rw [Finset.sum_add_distrib]
  exact Nat.add_le_add hc1 hc2

lemma diffTreeChanges_chainTree_le_suffix {T : SparseCoreRestartTool} {P : ChainParams}
    {st₁ st₂ : ChainState T P} {i₀ : ℕ} (hi₀ : i₀ ≤ P.d + 1)
    (hpre : ∀ j < i₀, (st₁.toTreeChain.activeLSF j).F.F.E =
      (st₂.toTreeChain.activeLSF j).F.F.E) :
    (diffTreeChanges st₁.toTreeChain.chainTree.E st₂.toTreeChain.chainTree.E).length ≤
      (Finset.Ico i₀ (P.d + 1)).sum fun j =>
        (st₁.toTreeChain.activeLSF j).F.F.E.card + (st₂.toTreeChain.activeLSF j).F.F.E.card := by
  have hbi := diffTreeChanges_length_biUnion (Finset.range (P.d + 1))
    (fun j => (st₁.toTreeChain.activeLSF j).F.F.E)
    (fun j => (st₂.toTreeChain.activeLSF j).F.F.E)
  change (diffTreeChanges st₁.toTreeChain.chainTree.E st₂.toTreeChain.chainTree.E).length ≤ _
  have hsplit : Finset.range (P.d + 1) = Finset.range i₀ ∪ Finset.Ico i₀ (P.d + 1) := by
    ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range i₀) (Finset.Ico i₀ (P.d + 1)) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_range, Finset.mem_Ico] at hj1 hj2
    omega
  have hzero : (Finset.range i₀).sum (fun j =>
      (diffTreeChanges (st₁.toTreeChain.activeLSF j).F.F.E
        (st₂.toTreeChain.activeLSF j).F.F.E).length) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hpre j (Finset.mem_range.mp hj)]
    simp [diffTreeChanges_length]
  refine le_trans hbi ?_
  rw [hsplit, Finset.sum_union hdisj, hzero, zero_add]
  exact Finset.sum_le_sum fun j _ => diffTreeChanges_length_le_add _ _

end DynamicHelpers2

section BudgetMonotonicity

lemma logFactor_pos (P : ChainParams) (n : ℕ) : 0 < logFactor P n := by
  unfold logFactor
  apply Real.log_pos
  have : (1 : ℝ) ≤ P.M₀ := by exact_mod_cast P.hM₀
  linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]

lemma logFactor_mono (P : ChainParams) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    logFactor P n₁ ≤ logFactor P n₂ := by
  unfold logFactor
  apply Real.log_le_log
  · have : (1 : ℝ) ≤ P.M₀ := by exact_mod_cast P.hM₀
    linarith [show (0 : ℝ) ≤ n₁ from Nat.cast_nonneg n₁]
  · exact_mod_cast (show P.M₀ + n₁ + 2 ≤ P.M₀ + n₂ + 2 by omega)

lemma levelToolCap_nonneg {TP : SparseCoreParams} (hTP : TP.Valid) (P : ChainParams)
    (n i : ℕ) : 0 ≤ levelToolCap TP P n i := by
  rcases hTP with ⟨_, _, hγℓ_ge, _, _, _, hγr_ge, _, _, hcT⟩
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγℓ_nonneg : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
  have hγr_nonneg : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hγr_ge (P.M₀ ^ 2))
  have hlog : 0 ≤ logFactor P n := (logFactor_pos P n).le
  have hlog10 : 0 ≤ Real.log (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2) :=
    Real.log_nonneg (by
      have := mul_nonneg (Nat.cast_nonneg (α := ℝ) P.M₀) hγℓ_nonneg
      linarith)
  unfold levelToolCap
  split_ifs <;> positivity

lemma levelToolCap_mono {TP : SparseCoreParams} (hTP : TP.Valid) (P : ChainParams)
    {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) (i : ℕ) :
    levelToolCap TP P n₁ i ≤ levelToolCap TP P n₂ i := by
  rcases hTP with ⟨_, _, hγℓ_ge, _, _, _, hγr_ge, _, _, hcT⟩
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγℓ_nonneg : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
  have hγr_nonneg : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hγr_ge (P.M₀ ^ 2))
  have hlog_pow : (2 * logFactor P n₁) ^ TP.p_T ≤ (2 * logFactor P n₂) ^ TP.p_T :=
    pow_le_pow_left₀ (by linarith [(logFactor_pos P n₁).le]) (by linarith [logFactor_mono P hn]) _
  unfold levelToolCap
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left hlog_pow
  positivity

lemma lastCostCap_nonneg {TP : SparseCoreParams} {LP : LastLevelParams}
    (hTP : TP.Valid) (hLP : LP.Valid) (P : ChainParams) (n : ℕ) :
    0 ≤ lastCostCap TP LP P n := by
  rcases hTP with ⟨_, _, hγℓ_ge, _, _, _, hγr_ge, _, _, _⟩
  rcases hLP with ⟨_, _, _, _, hcLast⟩
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγℓ_nonneg : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
  have hγr_nonneg : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hγr_ge (P.M₀ ^ 2))
  have hlog : 0 ≤ logFactor P n := (logFactor_pos P n).le
  unfold lastCostCap
  positivity

lemma lastCostCap_mono {TP : SparseCoreParams} {LP : LastLevelParams}
    (hTP : TP.Valid) (hLP : LP.Valid) (P : ChainParams) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    lastCostCap TP LP P n₁ ≤ lastCostCap TP LP P n₂ := by
  rcases hTP with ⟨_, _, hγℓ_ge, _, _, _, hγr_ge, _, _, _⟩
  rcases hLP with ⟨_, _, _, _, hcLast⟩
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγℓ_nonneg : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
  have hγr_nonneg : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hγr_ge (P.M₀ ^ 2))
  have hlog_pow : (2 * logFactor P n₁) ^ LP.p_last ≤ (2 * logFactor P n₂) ^ LP.p_last :=
    pow_le_pow_left₀ (by linarith [(logFactor_pos P n₁).le]) (by linarith [logFactor_mono P hn]) _
  unfold lastCostCap
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul_of_nonneg_left hlog_pow (by positivity)

lemma opRuntimeBudget_mono {TP : SparseCoreParams} {LP : LastLevelParams}
    (hTP : TP.Valid) (hLP : LP.Valid) (P : ChainParams) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) (i₀ : ℕ) :
    opRuntimeBudget TP LP P n₁ i₀ ≤ opRuntimeBudget TP LP P n₂ i₀ := by
  unfold opRuntimeBudget
  apply add_le_add _ le_rfl
  apply add_le_add _ (lastCostCap_mono hTP hLP P hn)
  split_ifs
  · exact Finset.sum_le_sum fun j _ => levelToolCap_mono hTP P hn j
  · exact le_rfl

lemma levelDecCap_nonneg {TP : SparseCoreParams} (hTP : TP.Valid) (P : ChainParams) (i : ℕ) :
    0 ≤ levelDecCap TP P i := by
  rcases hTP with ⟨_, _, hγℓ_ge, _, _, _, _, _, _, _⟩
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγℓ_nonneg : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
  unfold levelDecCap
  positivity

lemma diffTreeCap_nonneg {TP : SparseCoreParams} (_hTP : TP.Valid) (P : ChainParams) (i₀ : ℕ) :
    0 ≤ diffTreeCap TP P i₀ := by
  unfold diffTreeCap
  have hsum : 0 ≤ (Finset.Ico i₀ (P.d + 1)).sum (fun j => (levelM TP P j : ℝ)) :=
    Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  linarith

lemma opTreeBudget_nonneg {TP : SparseCoreParams} (hTP : TP.Valid) (P : ChainParams) (i₀ : ℕ) :
    0 ≤ opTreeBudget TP P i₀ := by
  unfold opTreeBudget
  have h1 : 0 ≤ if i₀ < P.d then (Finset.Ico i₀ P.d).sum (levelDecCap TP P) else 0 := by
    split_ifs
    · exact Finset.sum_nonneg fun j _ => levelDecCap_nonneg hTP P j
    · exact le_rfl
  linarith [diffTreeCap_nonneg hTP P i₀, show 0 ≤ lastTreeCap TP P from by
    rcases hTP with ⟨_, _, hγℓ_ge, _, _, _, hγr_ge, _, _, _⟩
    have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
    have hγℓ_nonneg : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
    have hγr_nonneg : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hγr_ge (P.M₀ ^ 2))
    unfold lastTreeCap; positivity]

lemma ChainBudgetInvWith.mono_n {T : SparseCoreRestartTool} {P : ChainParams}
    {TP : SparseCoreParams} {LP : LastLevelParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) {st : ChainState T P} {overflow : ℝ}
    (hB : ChainBudgetInvWith TP LP N₀ st overflow) {n' : ℕ} (hn : N₀ ≤ n') :
    (st.closedRuntime : ℝ) ≤
      ∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
          opRuntimeBudget TP LP P n' i + overflow := by
  have hRestartNN : 0 ≤ activeRestartCap TP P N₀ st.curRestarts := by
    unfold activeRestartCap
    refine Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) ?_
    rcases hTP with ⟨_, _, hγℓ_ge, _, _, _, hγr_ge, _, _, hcT⟩
    have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
    have hγℓ_nn : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
    have hγr_nn : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hγr_ge (P.M₀ ^ 2))
    have hlog := (logFactor_pos P N₀).le
    unfold restartCostCap
    positivity
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

lemma restartCostCap_nonneg {TP : SparseCoreParams} (hTP : TP.Valid) (P : ChainParams)
    (n i : ℕ) : 0 ≤ restartCostCap TP P n i := by
  rcases hTP with ⟨_, _, hγℓ_ge, _, _, _, hγr_ge, _, _, hcT⟩
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγℓ_nn : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
  have hγr_nn : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hγr_ge (P.M₀ ^ 2))
  have hlog : 0 ≤ 2 * logFactor P n := by linarith [(logFactor_pos P n).le]
  unfold restartCostCap
  positivity

lemma restartCostCap_le_levelToolCap {TP : SparseCoreParams} (hTP : TP.Valid) (P : ChainParams)
    (n i : ℕ) : restartCostCap TP P n i ≤ levelToolCap TP P n i := by
  rcases hTP with ⟨_, _, hγℓ_ge, _, _, _, hγr_ge, _, _, hcT⟩
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hk_ge : (1 : ℝ) ≤ P.k := by exact_mod_cast P.hk
  have hγℓ_nn : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
  have hγr_nn : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hγr_ge (P.M₀ ^ 2))
  have hlog : 0 ≤ 2 * logFactor P n := by linarith [(logFactor_pos P n).le]
  have hlog10 : 0 ≤ Real.log (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2) :=
    Real.log_nonneg (by
      have := mul_nonneg (Nat.cast_nonneg (α := ℝ) P.M₀) hγℓ_nn
      linarith)
  unfold restartCostCap levelToolCap
  have hmul :
      2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) *
          TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P n) ^ TP.p_T ≤
        2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) *
          (P.k : ℝ) * TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P n) ^ TP.p_T := by
    calc
      2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) *
            TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P n) ^ TP.p_T
          = 2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) *
              1 * TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P n) ^ TP.p_T := by ring
      _ ≤ 2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) *
            (P.k : ℝ) * TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P n) ^ TP.p_T := by gcongr
  have htail : 0 ≤ if i = 0 then
        200 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * Real.log (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2)
      else 5 * TP.γ_r (P.M₀ ^ 2) *
        ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (i - 1) / (P.k : ℝ) + 1) := by
    split_ifs <;> positivity
  linarith

lemma activeRestartCap_nonneg {TP : SparseCoreParams} (hTP : TP.Valid) (P : ChainParams)
    (n : ℕ) (cRest : ℕ → ℕ) : 0 ≤ activeRestartCap TP P n cRest :=
  Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (restartCostCap_nonneg hTP P n i)

lemma activeRestartCap_zero (TP : SparseCoreParams) (P : ChainParams) (n : ℕ) :
    activeRestartCap TP P n (fun _ => 0) = 0 := by
  simp [activeRestartCap]

lemma activeRestartCap_rebuild (TP : SparseCoreParams) (P : ChainParams) (n i₀ : ℕ)
    (hi₀ : i₀ ≤ P.d) (cRest : ℕ → ℕ) :
    activeRestartCap TP P n (fun j => if i₀ ≤ j ∧ j < P.d then 0 else cRest j) +
      ∑ j ∈ Finset.Ico i₀ P.d, (cRest j : ℝ) * restartCostCap TP P n j =
    activeRestartCap TP P n cRest := by
  unfold activeRestartCap
  have hsplit : Finset.range P.d = Finset.range i₀ ∪ Finset.Ico i₀ P.d := by
    ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range i₀) (Finset.Ico i₀ P.d) := by
    rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_union hdisj]
  have hPre : ∑ j ∈ Finset.range i₀,
      ((if i₀ ≤ j ∧ j < P.d then 0 else cRest j : ℕ) : ℝ) * restartCostCap TP P n j =
      ∑ j ∈ Finset.range i₀, (cRest j : ℝ) * restartCostCap TP P n j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hlt := Finset.mem_range.mp hj
    simp [show ¬ (i₀ ≤ j ∧ j < P.d) by omega]
  have hSuf : ∑ j ∈ Finset.Ico i₀ P.d,
      ((if i₀ ≤ j ∧ j < P.d then 0 else cRest j : ℕ) : ℝ) * restartCostCap TP P n j = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rcases Finset.mem_Ico.mp hj with ⟨h1, h2⟩
    simp [h1, h2]
  rw [hPre, hSuf, add_zero]

lemma activeRestartCap_shift (TP : SparseCoreParams) (P : ChainParams) (n i₀ : ℕ)
    (hi₀ : i₀ < P.d) (cRest : ℕ → ℕ) :
    activeRestartCap TP P n (fun j =>
      if j = i₀ then cRest i₀ + 1 else if i₀ + 1 ≤ j ∧ j < P.d then 0 else cRest j) +
      ∑ j ∈ Finset.Ico (i₀ + 1) P.d, (cRest j : ℝ) * restartCostCap TP P n j =
    activeRestartCap TP P n cRest + restartCostCap TP P n i₀ := by
  unfold activeRestartCap
  have hsplit : Finset.range P.d = Finset.range i₀ ∪ Finset.Ico i₀ P.d := by
    ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range i₀) (Finset.Ico i₀ P.d) := by
    rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
  have hIco : Finset.Ico i₀ P.d = insert i₀ (Finset.Ico (i₀ + 1) P.d) := by
    ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  have hNotMem : i₀ ∉ Finset.Ico (i₀ + 1) P.d := by
    simp only [Finset.mem_Ico]; omega
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_union hdisj, hIco,
    Finset.sum_insert hNotMem, Finset.sum_insert hNotMem]
  have hPre : ∑ j ∈ Finset.range i₀,
      ((if j = i₀ then cRest i₀ + 1 else if i₀ + 1 ≤ j ∧ j < P.d then 0 else cRest j : ℕ) : ℝ) *
        restartCostCap TP P n j =
      ∑ j ∈ Finset.range i₀, (cRest j : ℝ) * restartCostCap TP P n j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hlt := Finset.mem_range.mp hj
    have hne : j ≠ i₀ := by omega
    have hns : ¬ (i₀ + 1 ≤ j ∧ j < P.d) := by omega
    simp only [hne, ↓reduceIte, hns]
  have hSuf : ∑ j ∈ Finset.Ico (i₀ + 1) P.d,
      ((if j = i₀ then cRest i₀ + 1 else if i₀ + 1 ≤ j ∧ j < P.d then 0 else cRest j : ℕ) : ℝ) *
        restartCostCap TP P n j = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rcases Finset.mem_Ico.mp hj with ⟨h1, h2⟩
    simp [show j ≠ i₀ by omega, h1, h2]
  have hAt :
      ((if i₀ = i₀ then cRest i₀ + 1 else if i₀ + 1 ≤ i₀ ∧ i₀ < P.d then 0 else cRest i₀ : ℕ) : ℝ) *
        restartCostCap TP P n i₀ =
      (cRest i₀ : ℝ) * restartCostCap TP P n i₀ + restartCostCap TP P n i₀ := by
    simp only [↓reduceIte, Nat.cast_add, Nat.cast_one]
    ring
  rw [hPre, hAt, hSuf]
  ring

end BudgetMonotonicity

end MinCostFlow.Chain
