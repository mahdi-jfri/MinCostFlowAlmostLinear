module

public import MinCostFlow.Chain.Theorem5_1Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 5.1 (`theorem_5_1`): Own-level, `d = 1`, and Unconnected Extensions

Re-exports `MinCostFlow.Chain.Theorem5_1Core` (`theorem_5_1_param`, `theorem_5_1`,
`theorem_5_1_relaxed`) and completes Theorem 5.1 with:
* `theorem_5_1_relaxed_own_kappa_lower`, `theorem_5_1_relaxed_own_with`, and
  `theorem_5_1_relaxed_own` (`algorithm2_dsWithFailureWith` / `algorithm2_dsWithFailureOwn`),
* `theorem_5_1_d_one`, and
* `lemma_5_11_noHidden_without_connected`.
-/

@[expose] public section

namespace MinCostFlow.Chain

section MainTheorem

/-- Lower bound on `alg2KappaOwn` for `theorem_5_1_relaxed_own` / `theorem_5_1_relaxed_own_with`,
independent of any dynamic query sequence `(D, η, isUpdate, T)`. -/
lemma theorem_5_1_relaxed_own_kappa_lower {cfg : Alg2Config} (hVNH : cfg.ValidNoHidden)
    {C_γ C_ψ C_N : ℝ} (hD : cfg.P.d = chosenD (23 / 24) cfg.P.M₀)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last (levelM cfg.TP cfg.P cfg.P.d + 1) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2)) :
    let κ_own := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
    0 < κ_own ∧ alg2KappaLower (15 + 5 * C_γ) (47 / 48) cfg.P.M₀ ≤ κ_own := by
  have ha : ((1 : ℝ) + (23 : ℝ) / 24) / 2 = (47 : ℝ) / 48 := by norm_num
  have hσT' : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ (((1 : ℝ) + 23 / 24) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by rwa [ha]
  have hσL' : cfg.LP.σ_last (levelM cfg.TP cfg.P cfg.P.d + 1) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ (((1 : ℝ) + 23 / 24) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by rwa [ha]
  have hlogF' : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ (((1 : ℝ) + 23 / 24) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by rwa [ha]
  simpa only [alg2KappaOwn, ha] using
    alg2KappaAt_lower_of_params (levelM cfg.TP cfg.P cfg.P.d + 1) hVNH
      (by norm_num : (0 : ℝ) < 23 / 24) (by norm_num : (23 : ℝ) / 24 < 1)
      hD hCγ hCψ hCN hγℓ hγr hσT' hσL' hσM hcT hcL hΨ hlogF' hlogN

/-- Generalization of `theorem_5_1_relaxed_own` to `algorithm2_dsWithFailureWith cfg κ` for any
`κ` with `0 < κ ≤ alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀`. -/
theorem theorem_5_1_relaxed_own_with (κ : ℝ) {cfg : Alg2Config} (hV : cfg.Valid)
    (hκ_pos : 0 < κ) (hκ_le : κ ≤ alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
    {C_γ C_ψ C_N : ℝ}
    (hD : cfg.P.d = chosenD (23 / 24) cfg.P.M₀)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last (levelM cfg.TP cfg.P cfg.P.d + 1) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2))
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (hConn : ∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) :
    let A := algorithm2_dsWithFailureWith cfg κ
    let κ_own := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
    let C_κ := 15 + 5 * C_γ
    let C_rt := 62 + 21 * C_γ + 4 * C_ψ + C_N
    let f := alg2TimeFactor C_rt (47 / 48)
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
    let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
    let Q_upd := alg2UpdateQueries D isUpdate T
    let K_upd := alg2UpdateCount isUpdate T
    let Q_det := alg2DetectSizeWith cfg κ D η isUpdate T
    let K_det := alg2DetectCount isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
    (0 < κ ∧ alg2KappaLower C_κ (47 / 48) cfg.P.M₀ ≤ κ_own) ∧
    (Filter.Tendsto (fun m : ℕ => Real.log (f m) / Real.log (m : ℝ)) Filter.atTop (nhds 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 1 ≤ B ∧ ∀ m : ℕ, 1 ≤ m → f m ≤ B * (m : ℝ) ^ δ) ∧
    (∀ t ≤ T,
      A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) =
        (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t).flow ∧
      ∀ e ∈ (D.G t).E,
        A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) e =
          MinCostFlow.IPM.minRatioFlow A.eraseFailure D η isUpdate t e) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
      (D.G (t + 1)).IsCirculation
          (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) ∧
      (D.HiddenStable (t + 1) cfg.α cfg.Ψ →
        (MinCostFlow.IPM.minRatioFailureDirection A D η isUpdate t).isSome = true ∧
        (D.G (t + 1)).inner (D.g (t + 1))
            (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) /
          (D.G (t + 1)).lnorm (D.ℓ (t + 1))
            (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) ≤ -(κ * cfg.α)) ∧
      ∀ Δ, MinCostFlow.IPM.minRatioFailureDirection A D η isUpdate t = some Δ →
        let stNext := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1)
        let T_tree := stNext.extTree
        (D.G (t + 1)).IsSubgraph T_tree ∧
        T_tree.IsForest ∧
        (∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V,
          (D.G (t + 1)).Connected u v → T_tree.Connected u v) ∧
        ((∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V, (D.G (t + 1)).Connected u v) →
          T_tree.IsSpanningTreeOn (D.G (t + 1)).V) ∧
        ∃ (offTreeEdges : List (ℕ × Bool)) (treePaths : List (ℕ × ℕ)),
          (offTreeEdges.length : ℝ) ≤ f cfg.P.M₀ ∧
          (∀ x ∈ offTreeEdges, x.1 ∈ (D.G (t + 1)).E \ T_tree.E) ∧
          (treePaths.length : ℝ) ≤ f cfg.P.M₀ ∧
          (∀ p ∈ treePaths, T_tree.Connected p.1 p.2) ∧
          ∀ e : ℕ, Δ e =
            (offTreeEdges.map (fun x => walkFlow [x] e)).sum +
            (treePaths.map (fun p => walkFlow (T_tree.forestPath p.1 p.2) e)).sum) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
      (A.detect (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t)).1 =
        MinCostFlow.IPM.minRatioDetectSet A.eraseFailure D η isUpdate cfg.ε t) ∧
    (D.HiddenStable T cfg.α cfg.Ψ →
      ¬ minRatioFailFailedBefore (algorithm2_dsWith cfg κ) D η isUpdate T) ∧
    (alg2LctAmortizedCharge cfg.N₀ st.lctDetectOps ≤ f cfg.P.M₀ * ((Q_det : ℝ) + (K_det : ℝ)) ∧
      st.chain.rebuildCount cfg.P.d = 0 ∧
      st.chain.rebuildCount 0 + st.chain.updCount 0 ≤ Q_upd ∧
      (st.chain.totalRuntime : ℝ) ≤ alg2RuntimeBoundSR cfg st ∧
      (st.chain.totalTreeUpdates : ℝ) ≤ alg2TreeUpdatesBoundSR cfg st ∧
      (∀ i : Fin (cfg.P.d + 1),
        (st.chain.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P Ψ_g st.chain.rebuildCount i.val) ∧
      (st.largeBatchEnc : ℝ) ≤ 40 * (Q_upd : ℝ) *
        Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2) ∧
      ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ cfg.P.M₀) →
        st.largeBatchEnc = 0)) ∧
    (((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
        f cfg.P.M₀ * Q_tot +
          40 * (Q_upd : ℝ) * Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2)) ∧
      ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ cfg.P.M₀) →
        (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
          f cfg.P.M₀ * Q_tot)) := by
  have ha : ((1 : ℝ) + (23 : ℝ) / 24) / 2 = (47 : ℝ) / 48 := by norm_num
  have hσT' : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ (((1 : ℝ) + 23 / 24) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by
    rwa [ha]
  have hσL' : cfg.LP.σ_last (levelM cfg.TP cfg.P cfg.P.d + 1) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ (((1 : ℝ) + 23 / 24) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by
    rwa [ha]
  have hlogF' : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ (((1 : ℝ) + 23 / 24) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by
    rwa [ha]
  simpa only [alg2KappaOwn, ha] using
    theorem_5_1_param_at_of_collapsed_with (levelM cfg.TP cfg.P cfg.P.d + 1) κ hV hκ_pos hκ_le
      (by norm_num : (0 : ℝ) < 23 / 24) (by norm_num : (23 : ℝ) / 24 < 1)
      hD hCγ hCψ hCN hγℓ hγr hσT' hσL' hσM hcT hcL hΨ hlogF' hlogN
      hHist hmBound hnBound
      (fun t ht _ _ _ _ hIc hFc =>
        (chainInv_comp_bound_all_levels hV.hTP hV.toNoHidden.hT hV.hγM₀ hV.hγk hIc
          (hFc.connected (hConn t ht))).2)
      (theorem_5_1_collapsed_with κ hV.toNoHidden hHist hmBound hnBound)

/-- Connectedness-based variant of `theorem_5_1_relaxed` for `algorithm2_dsOwn`: replaces the
global-`N₀` hypothesis on `LP.σ_last` with the own-level bound
`cfg.LP.σ_last (levelM cfg.TP cfg.P cfg.P.d + 1)` under input graph connectedness `hConn`. -/
theorem theorem_5_1_relaxed_own {cfg : Alg2Config} (hV : cfg.Valid) {C_γ C_ψ C_N : ℝ}
    (hD : cfg.P.d = chosenD (23 / 24) cfg.P.M₀)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last (levelM cfg.TP cfg.P cfg.P.d + 1) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2))
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (hConn : ∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) :
    let A := algorithm2_dsWithFailureOwn cfg
    let κ := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
    let C_κ := 15 + 5 * C_γ
    let C_rt := 62 + 21 * C_γ + 4 * C_ψ + C_N
    let f := alg2TimeFactor C_rt (47 / 48)
    let st := minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate T
    let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
    let Q_upd := alg2UpdateQueries D isUpdate T
    let K_upd := alg2UpdateCount isUpdate T
    let Q_det := alg2DetectSizeOwn cfg D η isUpdate T
    let K_det := alg2DetectCount isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
    (0 < κ ∧ alg2KappaLower C_κ (47 / 48) cfg.P.M₀ ≤ κ) ∧
    (Filter.Tendsto (fun m : ℕ => Real.log (f m) / Real.log (m : ℝ)) Filter.atTop (nhds 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 1 ≤ B ∧ ∀ m : ℕ, 1 ≤ m → f m ≤ B * (m : ℝ) ^ δ) ∧
    (∀ t ≤ T,
      A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) =
        (minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate t).flow ∧
      ∀ e ∈ (D.G t).E,
        A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) e =
          MinCostFlow.IPM.minRatioFlow A.eraseFailure D η isUpdate t e) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
      (D.G (t + 1)).IsCirculation
          (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) ∧
      (D.HiddenStable (t + 1) cfg.α cfg.Ψ →
        (MinCostFlow.IPM.minRatioFailureDirection A D η isUpdate t).isSome = true ∧
        (D.G (t + 1)).inner (D.g (t + 1))
            (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) /
          (D.G (t + 1)).lnorm (D.ℓ (t + 1))
            (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) ≤ -(κ * cfg.α)) ∧
      ∀ Δ, MinCostFlow.IPM.minRatioFailureDirection A D η isUpdate t = some Δ →
        let stNext := minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate (t + 1)
        let T_tree := stNext.extTree
        (D.G (t + 1)).IsSubgraph T_tree ∧
        T_tree.IsForest ∧
        (∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V,
          (D.G (t + 1)).Connected u v → T_tree.Connected u v) ∧
        ((∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V, (D.G (t + 1)).Connected u v) →
          T_tree.IsSpanningTreeOn (D.G (t + 1)).V) ∧
        ∃ (offTreeEdges : List (ℕ × Bool)) (treePaths : List (ℕ × ℕ)),
          (offTreeEdges.length : ℝ) ≤ f cfg.P.M₀ ∧
          (∀ x ∈ offTreeEdges, x.1 ∈ (D.G (t + 1)).E \ T_tree.E) ∧
          (treePaths.length : ℝ) ≤ f cfg.P.M₀ ∧
          (∀ p ∈ treePaths, T_tree.Connected p.1 p.2) ∧
          ∀ e : ℕ, Δ e =
            (offTreeEdges.map (fun x => walkFlow [x] e)).sum +
            (treePaths.map (fun p => walkFlow (T_tree.forestPath p.1 p.2) e)).sum) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
      (A.detect (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t)).1 =
        MinCostFlow.IPM.minRatioDetectSet A.eraseFailure D η isUpdate cfg.ε t) ∧
    (D.HiddenStable T cfg.α cfg.Ψ →
      ¬ minRatioFailFailedBefore (algorithm2_dsOwn cfg) D η isUpdate T) ∧
    (alg2LctAmortizedCharge cfg.N₀ st.lctDetectOps ≤ f cfg.P.M₀ * ((Q_det : ℝ) + (K_det : ℝ)) ∧
      st.chain.rebuildCount cfg.P.d = 0 ∧
      st.chain.rebuildCount 0 + st.chain.updCount 0 ≤ Q_upd ∧
      (st.chain.totalRuntime : ℝ) ≤ alg2RuntimeBoundSR cfg st ∧
      (st.chain.totalTreeUpdates : ℝ) ≤ alg2TreeUpdatesBoundSR cfg st ∧
      (∀ i : Fin (cfg.P.d + 1),
        (st.chain.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P Ψ_g st.chain.rebuildCount i.val) ∧
      (st.largeBatchEnc : ℝ) ≤ 40 * (Q_upd : ℝ) *
        Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2) ∧
      ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ cfg.P.M₀) →
        st.largeBatchEnc = 0)) ∧
    (((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
        f cfg.P.M₀ * Q_tot +
          40 * (Q_upd : ℝ) * Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2)) ∧
      ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ cfg.P.M₀) →
        (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
          f cfg.P.M₀ * Q_tot)) := by
  simpa only [algorithm2_dsWithFailureOwn, alg2KappaOwn, alg2KappaAt,
    algorithm2_dsOwn, alg2DetectSizeOwn] using
    theorem_5_1_relaxed_own_with (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV
      (alg2KappaAt_pos hV.toNoHidden (levelM cfg.TP cfg.P cfg.P.d + 1)) le_rfl
      hD hCγ hCψ hCN hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF hlogN
      hHist hmBound hnBound hConn

/-- Unconditional `d = 1` specialization of `theorem_5_1` at `β = 23 / 24` (requiring neither
`Alg2RebuildCollapseHyp` nor `ToolSwitchedRecourse`). -/
theorem theorem_5_1_d_one {cfg : Alg2Config} (hV : cfg.Valid) (hd : cfg.P.d = 1)
    {C_γ C_ψ C_N : ℝ} (hD : cfg.P.d = chosenD (23 / 24) cfg.P.M₀)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2))
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let A := algorithm2_dsWithFailure cfg
    let κ := alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
    let C_κ := 15 + 5 * C_γ
    let C_rt := 62 + 21 * C_γ + 4 * C_ψ + C_N
    let f := alg2TimeFactor C_rt (47 / 48)
    let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
    let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
    let Q_upd := alg2UpdateQueries D isUpdate T
    let K_upd := alg2UpdateCount isUpdate T
    let Q_det := alg2DetectSize cfg D η isUpdate T
    let K_det := alg2DetectCount isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
    (0 < κ ∧ alg2KappaLower C_κ (47 / 48) cfg.P.M₀ ≤ κ) ∧
    (Filter.Tendsto (fun m : ℕ => Real.log (f m) / Real.log (m : ℝ)) Filter.atTop (nhds 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 1 ≤ B ∧ ∀ m : ℕ, 1 ≤ m → f m ≤ B * (m : ℝ) ^ δ) ∧
    (∀ t ≤ T,
      A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) =
        (minRatioFailState (algorithm2_ds cfg) D η isUpdate t).flow ∧
      ∀ e ∈ (D.G t).E,
        A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) e =
          MinCostFlow.IPM.minRatioFlow A.eraseFailure D η isUpdate t e) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
      (D.G (t + 1)).IsCirculation
          (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) ∧
      (D.HiddenStable (t + 1) cfg.α cfg.Ψ →
        (MinCostFlow.IPM.minRatioFailureDirection A D η isUpdate t).isSome = true ∧
        (D.G (t + 1)).inner (D.g (t + 1))
            (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) /
          (D.G (t + 1)).lnorm (D.ℓ (t + 1))
            (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) ≤ -(κ * cfg.α)) ∧
      ∀ Δ, MinCostFlow.IPM.minRatioFailureDirection A D η isUpdate t = some Δ →
        let stNext := minRatioFailState (algorithm2_ds cfg) D η isUpdate (t + 1)
        let T_tree := stNext.extTree
        (D.G (t + 1)).IsSubgraph T_tree ∧
        T_tree.IsForest ∧
        (∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V,
          (D.G (t + 1)).Connected u v → T_tree.Connected u v) ∧
        ((∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V, (D.G (t + 1)).Connected u v) →
          T_tree.IsSpanningTreeOn (D.G (t + 1)).V) ∧
        ∃ (offTreeEdges : List (ℕ × Bool)) (treePaths : List (ℕ × ℕ)),
          (offTreeEdges.length : ℝ) ≤ f cfg.P.M₀ ∧
          (∀ x ∈ offTreeEdges, x.1 ∈ (D.G (t + 1)).E \ T_tree.E) ∧
          (treePaths.length : ℝ) ≤ f cfg.P.M₀ ∧
          (∀ p ∈ treePaths, T_tree.Connected p.1 p.2) ∧
          ∀ e : ℕ, Δ e =
            (offTreeEdges.map (fun x => walkFlow [x] e)).sum +
            (treePaths.map (fun p => walkFlow (T_tree.forestPath p.1 p.2) e)).sum) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
      (A.detect (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t)).1 =
        MinCostFlow.IPM.minRatioDetectSet A.eraseFailure D η isUpdate cfg.ε t) ∧
    (D.HiddenStable T cfg.α cfg.Ψ →
      ¬ minRatioFailFailedBefore (algorithm2_ds cfg) D η isUpdate T) ∧
    (alg2LctAmortizedCharge cfg.N₀ st.lctDetectOps ≤ f cfg.P.M₀ * ((Q_det : ℝ) + (K_det : ℝ)) ∧
      st.chain.rebuildCount cfg.P.d = 0 ∧
      st.chain.rebuildCount 0 + st.chain.updCount 0 ≤ Q_upd ∧
      (st.chain.totalRuntime : ℝ) ≤ alg2RuntimeBoundSR cfg st ∧
      (st.chain.totalTreeUpdates : ℝ) ≤ alg2TreeUpdatesBoundSR cfg st ∧
      (∀ i : Fin (cfg.P.d + 1),
        (st.chain.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P Ψ_g st.chain.rebuildCount i.val) ∧
      (st.largeBatchEnc : ℝ) ≤ 40 * (Q_upd : ℝ) *
        Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2) ∧
      ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ cfg.P.M₀) →
        st.largeBatchEnc = 0)) ∧
    (((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
        f cfg.P.M₀ * Q_tot +
          40 * (Q_upd : ℝ) * Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2)) ∧
      ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ cfg.P.M₀) →
        (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
          f cfg.P.M₀ * Q_tot)) := by
  have ha : ((1 : ℝ) + (23 : ℝ) / 24) / 2 = (47 : ℝ) / 48 := by norm_num
  have hlogF' : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ (((1 : ℝ) + 23 / 24) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by
    rwa [ha]
  simpa only [ha] using
    theorem_5_1_param_d_one hV hd (by norm_num : (0 : ℝ) < 23 / 24) (by norm_num : (23 : ℝ) / 24 < 1)
      hD hCγ hCψ hCN hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF' hlogN hHist hmBound hnBound

/-- **Lemma 5.11** without `ConnectedOn`:
every conclusion of `Lemma5_11.lemma_5_11_noHidden` EXCEPT the optional `(H.D.G 0).Connected`
clause holds unconditionally without ANY graph-connectivity hypothesis on `G₀` or `(H.D.G 0)`. -/
theorem lemma_5_11_noHidden_without_connected (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ)
    {σ_mwu : ℕ → ℝ} (hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → σ_mwu n₁ ≤ σ_mwu n₂)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (hMWU : T.ToolMWURestartNoHidden σ_mwu) (hEmb : T.ToolEmbedsSurvivingRestartNoHidden)
    (hNoReinsTool : T.ToolNoReinsertRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ)
    (hG0Valid : G₀.IsValid) (hG0m : G₀.m ≤ P.M₀) (hG0n : G₀.n ≤ N₀) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    (acts : List ChainAction) (hActs : ChainActionListValid P N₀ G₀ ℓ₀ acts) :
    let st₀ := (algorithm1_initialize T L P (levelM TP P) N₀ G₀ ℓ₀ g₀).1
    let initCh := (algorithm1_initialize T L P (levelM TP P) N₀ G₀ ℓ₀ g₀).2
    let stEnd := (execChainActions T L TP P N₀ st₀ acts).1
    let chs := (execChainActions T L TP P N₀ st₀ acts).2
    let σ_tot := max (TP.σ P.k (stEnd.G 0).n) (LP.σ_last (stEnd.G 0).n)
    let σ_mwu_tot := max (σ_mwu (stEnd.G 0).n) (LP.σ_mwu (stEnd.G 0).n)
    ChainInv T L TP LP P N₀ stEnd ∧
    stEnd.toTreeChain.Holds (stEnd.G 0) stEnd.ℓ σ_tot σ_mwu_tot (TP.γ_ℓ (P.M₀ ^ 2)) (TP.γ_c (P.M₀ ^ 2)) ∧
    stEnd.toTreeChain.LastLevelSpans ∧
    stEnd.toTreeChain.EmbedsSurviving ∧
    ((initCh :: chs).foldl applyTreeChanges ∅ = stEnd.toTreeChain.chainTree.E ∧
      initCh.length + (chs.map List.length).sum ≤ stEnd.totalTreeUpdates) ∧
    ((∀ i ≤ P.d, ((stEnd.G i).m : ℝ) ≤ (levelM TP P i : ℝ)) ∧
      (∀ i ≤ P.d, ((nonIsolatedV (stEnd.G i)).card : ℝ) ≤ 2 * (levelM TP P i : ℝ)) ∧
      (∀ i ≤ P.d, (stEnd.G i).n ≤ (stEnd.G 0).n)) ∧
    (∀ c w : ℕ → ℝ, IsValidPair (stEnd.G 0) stEnd.ℓ c w →
      let C := stEnd.toTreeChain
      let (Δ, walk, optEdge) := algorithm1_findCycle stEnd
      (stEnd.G 0).IsCirculation Δ ∧
      (stEnd.G 0).inner stEnd.g Δ ≤ 0 ∧
      ((walkEdges walk \ C.chainTree.E).card : ℝ) ≤ 1 + TP.γ_ℓ (P.M₀ ^ 2) ∧
      (optEdge = none → Δ = 0 ∧ walk = [] ∧ (stEnd.G 0).inner stEnd.g c = 0) ∧
      (∀ e, optEdge = some e →
        e ∈ (stEnd.G 0).E \ C.chainTree.E ∧
        0 < (stEnd.G 0).lnorm stEnd.ℓ Δ ∧
        (1 / (σ_tot + 1)) *
            (|(stEnd.G 0).inner stEnd.g c| / ∑ i ∈ Finset.range (C.d + 1), (C.G i).norm1 (C.chainW w i)) ≤
          |(stEnd.G 0).inner stEnd.g Δ| / (stEnd.G 0).lnorm stEnd.ℓ Δ)) ∧
    ((stEnd.totalRuntime : ℝ) ≤
      ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
        (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) *
        (TP.γ_r (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (3 * P.d + 2)) *
        (2 * logFactor P N₀) ^ (max TP.p_T LP.p_last + 1) *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((stEnd.shiftCount i + stEnd.rebuildCount i : ℕ) : ℝ) * powTerm P i)) ∧
    ((stEnd.totalTreeUpdates : ℝ) ≤
      (14 * (P.d : ℝ) + 36) * (TP.γ_ℓ (P.M₀ ^ 2) * TP.γ_r (P.M₀ ^ 2)) ^ (2 * P.d + 1) *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((stEnd.shiftCount i + stEnd.rebuildCount i : ℕ) : ℝ) * powTerm P i)) := by
  have hBase := lemma_5_11_noHidden T L TP LP P N₀ hσ_mwu_mono hTP hLP hT hL hMWU hEmb hNoReinsTool hγM₀ hγk
    G₀ ℓ₀ g₀ hG0Valid hG0m hG0n hℓ₀ acts hActs
  rcases hBase with ⟨hInv, hHolds, hSpan, hEmbS, hTree, hSizes, hFC, hRT, hTU⟩
  refine ⟨hInv, hHolds, hSpan, hEmbS, hTree, ⟨hSizes.1, hSizes.2.1, fun i hi => ?_⟩, hFC, hRT, hTU⟩
  have hAux := (level_bounds_aux_noHidden T L TP LP P N₀ hTP hT hγM₀ hγk hInv i hi).2.1
  exact Finset.card_le_card hAux

end MainTheorem

end MinCostFlow.Chain
