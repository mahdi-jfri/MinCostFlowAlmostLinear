module

public import MinCostFlow.Chain.Ordered.Theorem5_1SmallKappa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 5.1 Core (`theorem_5_1`) for the Ordered Chain: Parameterized and Relaxed Variants

Ordered-chain counterpart of `MinCostFlow/Chain/Theorem5_1Core.lean`, proving the parameterized
and relaxed global-`N₀` formulations of **Theorem 5.1** (`jtree.tex` lines 8–23, pages 15 & 25–31):
* `theorem_5_1_param` / `theorem_5_1` (specializing exponent `β = 23/24 → 47/48`), and
* `theorem_5_1_relaxed` (permitting `hσT` and `hσL` up to `exp(O(L^{47/48} · LL))`).
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section MainTheorem

private theorem theorem_5_1_param_at_of_collapsed
    (n_last : ℕ) {cfg : Alg2Config} (hV : cfg.ValidOrd)
    {β C_γ C_ψ C_N : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hD : cfg.P.d = chosenD β cfg.P.M₀)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last n_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2))
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (hLastBound : ∀ t ≤ T, ∀ {ch e2i i2e nf}, ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch →
      FreshInv (D.G t) (ch.G 0) e2i i2e nf → (ch.G cfg.P.d).n ≤ n_last)
    (hColl :
      let κ := alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ n_last
      let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
      let Q_upd := alg2UpdateQueries D isUpdate T
      let K_upd := alg2UpdateCount isUpdate T
      let Q_det := alg2DetectSizeWith cfg κ D η isUpdate T
      let K_det := alg2DetectCount isUpdate T
      let Q_tot := (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
      ((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
        alg2CollapsedFactor cfg * Q_tot +
          40 * (Q_upd : ℝ) * Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2)) ∧
      ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ cfg.P.M₀) →
        (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
          alg2CollapsedFactor cfg * Q_tot)) :
    let κ := alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ n_last
    let A := algorithm2_dsWithFailureWith cfg κ
    let a := (1 + β) / 2
    let C_κ := 15 + 5 * C_γ
    let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
    let f := alg2TimeFactor C_rt a
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
    let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
    let Q_upd := alg2UpdateQueries D isUpdate T
    let K_upd := alg2UpdateCount isUpdate T
    let Q_det := alg2DetectSizeWith cfg κ D η isUpdate T
    let K_det := alg2DetectCount isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
    (0 < κ ∧ alg2KappaLower C_κ a cfg.P.M₀ ≤ κ) ∧
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
          f cfg.P.M₀ * Q_tot)) :=
  theorem_5_1_param_at_of_collapsed_with
    n_last (alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ n_last) hV
    (Ordered.alg2KappaAt_pos hV.toNoHidden n_last) le_rfl hβ0 hβ1 hD hCγ hCψ hCN
    hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF hlogN hHist hEdge hLen hmBound hnBound hLastBound hColl

/-- Internal bridge specializing `theorem_5_1_param_at_of_collapsed` to `n_last = cfg.N₀`. -/
theorem theorem_5_1_param_of_collapsed
    {cfg : Alg2Config} (hV : cfg.ValidOrd)
    {β C_γ C_ψ C_N : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hD : cfg.P.d = chosenD β cfg.P.M₀)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2))
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (hColl :
      let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
      let Q_upd := alg2UpdateQueries D isUpdate T
      let K_upd := alg2UpdateCount isUpdate T
      let Q_det := alg2DetectSize cfg D η isUpdate T
      let K_det := alg2DetectCount isUpdate T
      let Q_tot := (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
      ((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
        alg2CollapsedFactor cfg * Q_tot +
          40 * (Q_upd : ℝ) * Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2)) ∧
      ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ cfg.P.M₀) →
        (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
          alg2CollapsedFactor cfg * Q_tot)) :
    let A := algorithm2_dsWithFailure cfg
    let κ := alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
    let a := (1 + β) / 2
    let C_κ := 15 + 5 * C_γ
    let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
    let f := alg2TimeFactor C_rt a
    let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
    let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
    let Q_upd := alg2UpdateQueries D isUpdate T
    let K_upd := alg2UpdateCount isUpdate T
    let Q_det := alg2DetectSize cfg D η isUpdate T
    let K_det := alg2DetectCount isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
    (0 < κ ∧ alg2KappaLower C_κ a cfg.P.M₀ ≤ κ) ∧
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
          f cfg.P.M₀ * Q_tot)) :=
  theorem_5_1_param_at_of_collapsed
    cfg.N₀ hV hβ0 hβ1 hD hCγ hCψ hCN hγℓ hγr hσT hσL hσM
    hcT hcL hΨ hlogF hlogN hHist hEdge hLen hmBound hnBound
    (fun t ht _ _ _ _ hIc hFc => chainInv_last_le_N0 hV.toNoHidden (hnBound t ht) hIc hFc) hColl

/-- **Parameterized Theorem 5.1** (`jtree.tex` lines 8–23, page 15) for any sparse-core & MWU
exponent `β ∈ (0, 1)`, combining all clauses of the paper statement for the ordered chain
unconditionally for all `d ≥ 1`. -/
theorem theorem_5_1_param
    {cfg : Alg2Config} (hV : cfg.ValidOrd) {β C_γ C_ψ C_N : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hD : cfg.P.d = chosenD β cfg.P.M₀)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2))
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let A := algorithm2_dsWithFailure cfg
    let κ := alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
    let a := (1 + β) / 2
    let C_κ := 15 + 5 * C_γ
    let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
    let f := alg2TimeFactor C_rt a
    let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
    let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
    let Q_upd := alg2UpdateQueries D isUpdate T
    let K_upd := alg2UpdateCount isUpdate T
    let Q_det := alg2DetectSize cfg D η isUpdate T
    let K_det := alg2DetectCount isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
    (0 < κ ∧ alg2KappaLower C_κ a cfg.P.M₀ ≤ κ) ∧
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
          f cfg.P.M₀ * Q_tot)) :=
  theorem_5_1_param_of_collapsed
    hV hβ0 hβ1 hD hCγ hCψ hCN hγℓ hγr
    (exp_rpow_le_half_one_add cfg.P.hM₀ hβ1 hCγ hσT)
    (exp_rpow_le_half_one_add cfg.P.hM₀ hβ1 hCγ hσL) hσM hcT hcL hΨ
    hlogF hlogN hHist hEdge hLen hmBound hnBound
    (theorem_5_1_collapsed hV.toNoHidden hHist hEdge hLen hmBound hnBound)

/-- **Theorem 5.1** (`jtree.tex` lines 8–23, page 15),
specialized at Theorem 8.6's sparse-core & MWU exponent `β = 23 / 24`, giving subpolynomial factor
`f(m) = exp(O(log^{47/48} m · log log m))` and `κ = exp(-O(log^{47/48} m · log log m))`. -/
theorem theorem_5_1
    {cfg : Alg2Config} (hV : cfg.ValidOrd) {C_γ C_ψ C_N : ℝ}
    (hD : cfg.P.d = chosenD (23 / 24) cfg.P.M₀)
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
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let A := algorithm2_dsWithFailure cfg
    let κ := alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
    let C_κ := 15 + 5 * C_γ
    let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
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
    theorem_5_1_param
      hV (by norm_num : (0 : ℝ) < 23 / 24) (by norm_num : (23 : ℝ) / 24 < 1)
      hD hCγ hCψ hCN hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF' hlogN hHist hEdge hLen hmBound hnBound

/-- Relaxed specialization of `theorem_5_1` at `β = 23 / 24` permitting `hσT` and `hσL` up to
`exp(C_γ * (log(M₀ + 2))^(47/48) * log(log(M₀ + 2) + 2))`, preserving `C_κ` and `C_rt`. -/
theorem theorem_5_1_relaxed
    {cfg : Alg2Config} (hV : cfg.ValidOrd) {C_γ C_ψ C_N : ℝ}
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
    (hσL : cfg.LP.σ_last cfg.N₀ ≤
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
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let A := algorithm2_dsWithFailure cfg
    let κ := alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
    let C_κ := 15 + 5 * C_γ
    let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
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
  have hσT' : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ (((1 : ℝ) + 23 / 24) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by
    rwa [ha]
  have hσL' : cfg.LP.σ_last cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ (((1 : ℝ) + 23 / 24) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by
    rwa [ha]
  have hlogF' : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ (((1 : ℝ) + 23 / 24) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by
    rwa [ha]
  simpa only [ha] using
    theorem_5_1_param_of_collapsed
      hV (by norm_num : (0 : ℝ) < 23 / 24) (by norm_num : (23 : ℝ) / 24 < 1)
      hD hCγ hCψ hCN hγℓ hγr hσT' hσL' hσM hcT hcL hΨ hlogF' hlogN hHist hEdge hLen hmBound hnBound
      (theorem_5_1_collapsed hV.toNoHidden hHist hEdge hLen hmBound hnBound)

end MainTheorem

end MinCostFlow.Chain.Ordered
