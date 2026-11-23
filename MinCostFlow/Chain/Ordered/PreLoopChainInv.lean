module

public import MinCostFlow.Chain.Ordered.Algorithm2Uncond
import MinCostFlow.Chain.Ordered.UpdateProofs
import MinCostFlow.Chain.Ordered.RenameFacts

/-!
# The chain invariant before the shift loop

An `Update` of Algorithm 2 first translates the batch to internal names, then runs Algorithm 1's
`Update` on the chain, and then runs the shift loop. The proof of
`algorithm2_uncond_preserves_with` shows that the chain after Algorithm 1's `Update`, before the
shift loop, meets `ChainInv`. It does not export this fact. The amortized cost of `Update`
(`update_fwd_amortized`, `MinRatio/OrdSolverShiftPotential.lean`) needs it, since it uses the
recourse bound `ChainInv.hRecFwd` on that chain. This file states it.

`alg2_preLoop_chainInv_with` repeats the first steps of the `Update` case of
`algorithm2_uncond_preserves_with`: the reached state at stage `t` meets `Alg2UncondInvWith`,
the batch at stage `t + 1` translates to a valid internal batch, and
`update_preserves_with_noHidden` gives `ChainInv` of the result.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

/-- **`ChainInv` before the shift loop.** Take the hypotheses of
`algorithm2_uncond_preserves_with`, and a stage `t + 1 ≤ T`. Let `st` be the state reached at
stage `t`. Then the chain that Algorithm 1's `Update` returns for the translated batch of stage
`t + 1` (the chain that the shift loop of stage `t + 1` starts from) meets `ChainInv`. -/
theorem alg2_preLoop_chainInv_with {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) (t : ℕ) (ht : t + 1 ≤ T) :
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t
    let tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
    ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
      (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
        (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))).1 := by
  dsimp only
  set st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t
  set tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
  have ht_le : t ≤ T := Nat.le_of_succ_le ht
  have hI := (algorithm2_uncond_preserves_with (η := η) κ hV hHist hEdge hLen hmBound
    hnBound).1 t ht_le
  rcases hI with ⟨hInv, hBud, _, _, hFresh, hExtG, hExtLG, hChℓ, _, _, _, _, _, _, _⟩
  have hD := hHist.1 (t + 1) (Nat.succ_pos t) ht
  have hG1Valid := (hHist.2.1 (t + 1) ht).1
  have hℓ1Pos := (hHist.2.1 (t + 1) ht).2
  have hBatch_ext : st.extG.BatchIsValid (D.U (t + 1)) := by rw [hExtG]; exact hD.1
  have hTB := translateBatch_preserves (D.U (t + 1)) st.extG (st.chain.G 0)
    st.extToInt st.intToExt st.nextFresh hFresh hBatch_ext
  dsimp only at hTB
  change _ ∧ _ at hTB
  rcases hTB with ⟨hExtG', hFresh', hBatch_int, hNR_int, _, _, _, hi2e_old, _, hYesInsExt⟩
  have hEdge_int : ∀ u' ∈ tb.2.2.2.2, IsEdgeUpdate u' :=
    translateBatch_isEdgeUpdate st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
      (hEdge (t + 1) (Nat.succ_pos t) ht)
  have hExtEq : tb.1 = D.G (t + 1) := by
    rw [hExtG', hExtG]; exact hD.2.symm
  have hG0'Valid : ((st.chain.G 0).applyBatch tb.2.2.2.2).IsValid :=
    (hFresh'.isValid_iff).mpr (hExtEq ▸ hG1Valid)
  have hG0'm : ((st.chain.G 0).applyBatch tb.2.2.2.2).m ≤ cfg.P.M₀ := by
    rw [hFresh'.m_eq, hExtEq]; exact hmBound (t + 1) ht
  have hG0'n : ((st.chain.G 0).applyBatch tb.2.2.2.2).n ≤ cfg.N₀ := by
    rw [hFresh'.n_eq, hExtEq]; exact hnBound (t + 1) ht
  have hℓ_intR : LenInRange (max 0 cfg.Ψ) ((st.chain.G 0).applyBatch tb.2.2.2.2)
      (fun e' => D.ℓ (t + 1) (tb.2.2.1 e')) :=
    fun e' he' => hLen.lenInRange ht hℓ1Pos _ (hExtEq ▸ (hFresh'.hRight e' he').2)
  have hℓ_intStable : ∀ e' ∈ ((st.chain.G 0).applyBatch tb.2.2.2.2).E, e' ∈ (st.chain.G 0).E →
      (∀ u' ∈ tb.2.2.2.2, ¬ u'.Inserts e') →
        (fun e' => D.ℓ (t + 1) (tb.2.2.1 e')) e' = st.chain.ℓ e' := by
    intro e' he' he'0 _
    have he'_lt : e' < st.nextFresh := hFresh.hLtFresh e' he'0
    have hi2e_eq : tb.2.2.1 e' = st.intToExt e' := hi2e_old e' he'_lt
    obtain ⟨_, he_pre⟩ := hFresh.hRight e' he'0
    obtain ⟨_, he_ext'⟩ := hFresh'.hRight e' he'
    have he_ext1 : st.intToExt e' ∈ (D.G (t + 1)).E := by
      rw [← hExtEq, ← hi2e_eq]; exact he_ext'
    have hNoIns_ext : D.NotInsertedBetween (st.intToExt e') t (t + 1) := by
      intro s hs1 hs2 u hu hIns
      have hseq : s = t + 1 := by omega
      subst hseq
      have hge := hYesInsExt (st.intToExt e') (hExtEq ▸ he_ext1) ⟨u, hu, hIns⟩
      have he2i'_eq : tb.2.1 (st.intToExt e') = e' := by
        rw [← hi2e_eq]; exact (hFresh'.hRight e' he').1
      exact absurd (lt_of_lt_of_le he'_lt (le_trans hge (le_of_eq he2i'_eq))) (lt_irrefl _)
    have hℓ_same := (hHist.2.2.2 (t + 1) (Nat.succ_pos t) ht _ he_ext1 hNoIns_ext).2
    dsimp only
    rw [hi2e_eq, hℓ_same, hChℓ]
    dsimp only [Nat.add_sub_cancel]
    exact (hExtLG _ (hExtG ▸ he_pre)).1.symm
  have hU := update_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hV.hT hV.hL hV.hNoReins hV.hγM₀ hV.hγk hInv hBud tb.2.2.2.2
    (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))
    hBatch_int hNR_int hEdge_int hG0'Valid hG0'm hG0'n hℓ_intR hℓ_intStable
  dsimp only at hU
  exact hU.1

end MinCostFlow.Chain.Ordered
