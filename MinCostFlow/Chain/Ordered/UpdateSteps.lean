module

public import MinCostFlow.Chain.Ordered.UpdateStepsCore
import MinCostFlow.Chain.Ordered.BudgetHelpers
import MinCostFlow.Chain.Ordered.BudgetHelpersCost
import MinCostFlow.Chain.Ordered.RebuildSuffix
import MinCostFlow.Chain.Ordered.InitPreserves
import MinCostFlow.Chain.Ordered.RebuildPreserves
import MinCostFlow.Chain.Algorithm1InitPreserves
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Update-loop overflow (rebuild) step for Algorithm 1 with orders

This file proves `updateLoop_succ_over_step`, handling the case in `updateLoop` where level `idx`
exceeds its rebuild threshold and triggers `algorithm1_rebuild` from `idx`. It retires the active
tool, encoding, restart, and last-level costs into the `(k + 1)`-scaled runtime budget
`opRuntimeBudget` and updates the tree-change count.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

/-- The rebuild of the overflow step of `updateLoop` from level `idx`, started from any graph
`curG` and vectors `ℓ'`, `g'` that satisfy the rebuild part `UpdateLoopInvCore` of the loop
invariant: it preserves `ChainInv` and `ChainBudgetInvWith`, and bounds tree updates. -/
lemma rebuild_over_step
    (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) {Λ : ℝ} (hT : ChainToolSupply T TP P N₀ Λ)
    (hL : L.IsSpec LP)
    (_hNoReinsTool : T.ToolNoReinsertOrdRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {stOrig : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    {overflow extraOverflow : ℝ}
    (hBudgetOrig : ChainBudgetInvWith TP LP N₀ stOrig overflow) (hExtraNN : 0 ≤ extraOverflow)
    (ℓ' g' : ℕ → ℝ)
    (rem' idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ)
    (hLoop : UpdateLoopInvCore TP N₀ Λ extraOverflow stOrig st ℓ' g' (rem' + 1) idx curG curU
      curEncAcc)
    (hOver : intRebuildThreshold P N₀ idx < st.updCount idx + curU.length) :
    let (stEnd, _) := algorithm1_rebuild T L P { st with ℓ := ℓ', g := g' } idx curG curEncAcc
    ChainInv T L TP LP P N₀ stEnd ∧
    ChainBudgetInvWith TP LP N₀ stEnd (overflow + extraOverflow) ∧
    (stOrig.G 0).n ≤ (stEnd.G 0).n ∧
    (∀ i, stOrig.shiftCount i = stEnd.shiftCount i) ∧
    (∀ i, stOrig.rebuildCount i ≤ stEnd.rebuildCount i) ∧
    (diffTreeChanges stOrig.toTreeChain.chainTree.E stEnd.toTreeChain.chainTree.E).length +
      stOrig.totalTreeUpdates ≤ stEnd.totalTreeUpdates := by
  have hOrigCost := ChainInv.level_cost_bounds_noHidden hTP hLP hγM₀ hγk hInvOrig
  have hγr_nn : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hTP.2.2.2.2.2.2.1 (P.M₀ ^ 2))
  have hk1_ge : (1 : ℝ) ≤ (P.k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
    linarith
  have hidxLt : idx < P.d := by have := hLoop.hidxSum; omega
  set stWithLG := { st with ℓ := ℓ', g := g' }
  set oldE := stWithLG.toTreeChain.chainTree.E
  set G0 := fun j => if j = idx then curG else stWithLG.G j
  set res := rebuildSuffix T L P stWithLG.lvlM stWithLG.N₀ ℓ' g' (P.d - idx) idx
    G0 stWithLG.scState stWithLG.bran stWithLG.updCount
    stWithLG.curEnc stWithLG.curDecUpdates stWithLG.curFwd
  set retiredTool := (Finset.Ico idx P.d).sum fun j =>
    T.cost (stWithLG.scState j) + stWithLG.curEnc j
  set retiredDec := (Finset.Ico idx P.d).sum fun j => stWithLG.curDecUpdates j
  set stMidCore : ChainState T P :=
    { stWithLG with
      G := res.1, scState := res.2.1,
      curRestarts := fun j => if idx ≤ j ∧ j < P.d then 0 else stWithLG.curRestarts j,
      bran := res.2.2.1, updCount := res.2.2.2.1,
      lastK := res.2.2.2.2.2.2.2.1.1, lastLSFs := res.2.2.2.2.2.2.2.1.2, lastBran := 0,
      curLastRebuilds := 0, curLastCost := res.2.2.2.2.2.2.2.2,
      curEnc := res.2.2.2.2.1, curDecUpdates := res.2.2.2.2.2.1,
      curFwd := res.2.2.2.2.2.2.1,
      curLastTreeUpdates := 0 }
  have hG0Valid : (G0 0).IsValid := by
    by_cases h0 : idx = 0
    · subst h0; simp only [G0, ↓reduceIte]; exact hLoop.hCurGValid
    · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
      simp only [G0, hne0, ↓reduceIte]; exact (hLoop.hG0New (Nat.pos_of_ne_zero h0)).1
  have hG0m : (G0 0).m ≤ P.M₀ := by
    by_cases h0 : idx = 0
    · subst h0; simp only [G0, ↓reduceIte]; exact (hLoop.hCurGV0 rfl).1
    · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
      simp only [G0, hne0, ↓reduceIte]; exact (hLoop.hG0New (Nat.pos_of_ne_zero h0)).2.1
  have hG0n : (G0 0).n ≤ N₀ := by
    by_cases h0 : idx = 0
    · subst h0; simp only [G0, ↓reduceIte]; exact (hLoop.hCurGV0 rfl).2.1
    · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
      simp only [G0, hne0, ↓reduceIte]; exact (hLoop.hG0New (Nat.pos_of_ne_zero h0)).2.2.1
  have hℓ0 : ∀ e ∈ (G0 0).E, 0 < stWithLG.ℓ e := by
    by_cases h0 : idx = 0
    · subst h0; simp only [G0, ↓reduceIte]; exact (hLoop.hCurGV0 rfl).2.2.2
    · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
      simp only [G0, hne0, ↓reduceIte]; exact (hLoop.hG0New (Nat.pos_of_ne_zero h0)).2.2.2.2
  have hGi0V : (G0 idx).V ⊆ (G0 0).V := by
    by_cases h0 : idx = 0
    · subst h0; exact Finset.Subset.refl _
    · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
      simp only [G0, ↓reduceIte, hne0]; exact hLoop.hCurGVPos (Nat.pos_of_ne_zero h0)
  have hGi0m : ((G0 idx).m : ℝ) ≤ (levelM TP P idx : ℝ) := by
    simp only [G0, ↓reduceIte]; exact hLoop.hCurGM
  have hOrdIdx : ∃ ρ : Rotation (G0 idx), ρ.order = chainLevelOrd T G0 stWithLG.scState stWithLG.bran idx := by
    obtain ⟨ρAfter, hAfter⟩ := hLoop.hCurOrdEx
    have hGidx : G0 idx = curG := by simp [G0]
    refine ⟨hGidx.symm ▸ ρAfter, ?_⟩
    rw [oupd_rotation_cast_order, hAfter]
  have hℓ_idx : LevelLenRange TP P N₀ Λ idx (G0 idx)
      ((mkPartialChain T P G0 stWithLG.scState stWithLG.bran (G0 idx)).chainLen ℓ' idx) := by
    intro e he
    simp only [G0, ↓reduceIte] at he
    set Cpartial0 : TreeChain :=
      { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
    have heq : (mkPartialChain T P G0 stWithLG.scState stWithLG.bran (G0 idx)).chainLen ℓ' idx =
        Cpartial0.chainLen ℓ' idx := by
      apply chainLen_congr_lt
        (C₁ := mkPartialChain T P G0 stWithLG.scState stWithLG.bran (G0 idx))
        (C₂ := Cpartial0)
      · intro j hj
        change G0 j = Cpartial0.G j
        simp [G0, Cpartial0, stWithLG, Nat.ne_of_lt hj]
      · intro j hj
        simp [mkPartialChain, Cpartial0, ChainState.toTreeChain, TreeChain.activeLSF,
          stWithLG, show j < P.d by omega]
    rw [heq]; exact hLoop.hCurLenRange e he
  let stTmp : ChainState T P := { stWithLG with G := G0 }
  have hPreHist' : ∀ j < idx, Nonempty (LevelHistory T TP P N₀ stTmp j) := by
    intro j hj
    obtain ⟨H⟩ := hLoop.hPreHist j hj
    have hjne : j ≠ idx := Nat.ne_of_lt hj
    refine ⟨{ H with
      hEndG := by simpa [stTmp, G0, stWithLG, hjne] using H.hEndG
      hEndℓ := fun e he => by
        have he' : e ∈ (stWithLG.G j).E := by simpa [stTmp, G0, hjne] using he
        have hCL := chainLen_congr_lt (C₁ := stTmp.toTreeChain) (C₂ := stWithLG.toTreeChain) ℓ' j
          (fun m hm => by change stTmp.G m = stWithLG.G m; simp [stTmp, G0, show m ≠ idx by omega])
          (fun m hm => by simp [ChainState.toTreeChain, TreeChain.activeLSF, stTmp, show m < P.d by omega])
        change H.D.ℓ H.len e = stTmp.toTreeChain.chainLen ℓ' j e
        rw [hCL]; exact H.hEndℓ e he'
      hEndg := by
        have hCG := chainGrad_congr_lt (C₁ := stTmp.toTreeChain) (C₂ := stWithLG.toTreeChain) g' j
          (fun m hm => by change stTmp.G m = stWithLG.G m; simp [stTmp, G0, show m ≠ idx by omega])
          (fun m hm => by simp [ChainState.toTreeChain, TreeChain.activeLSF, stTmp, show m < P.d by omega])
        change H.D.g H.len = stTmp.toTreeChain.chainGrad g' j
        rw [hCG]; exact H.hEndg
      hEndOrd := by
        have hOrdJ : stTmp.levelOrd j = stWithLG.levelOrd j := by
          unfold ChainState.levelOrd chainLevelOrd
          split_ifs with hj0
          · subst hj0
            have h0ne : (0 : ℕ) ≠ idx := Nat.ne_of_lt hj
            simp [stTmp, G0, h0ne]
          · rfl
        rw [hOrdJ]; exact H.hEndOrd }⟩
  have hPreGSucc' : ∀ j < idx, G0 (j + 1) = T.S (stWithLG.scState j) (stWithLG.bran j) := by
    intro j hj
    by_cases h1 : j + 1 = idx
    · have hpos : 0 < idx := by omega
      have hprev := hLoop.hCurGFromPrev hpos
      rw [show idx - 1 = j by omega] at hprev
      simp only [G0, h1, ↓reduceIte, stWithLG]
      exact hprev
    · simp only [G0, h1, ↓reduceIte, stWithLG]
      exact hLoop.hPreGSucc j (by omega)
  have hStRecFwd : ChainRecBound P (TP.γ_r (P.M₀ ^ 2)) st := by
    intro j hj
    refine ⟨?_, ?_⟩
    · by_cases hjt : j < idx
      · exact (hLoop.hLoopRecFwd j hjt).1
      · have hge : idx ≤ j := Nat.le_of_not_lt hjt
        rw [hLoop.hCurFwdGe j hge, hLoop.hUpdGe j hge]
        exact (hInvOrig.hRecFwd j hj).1
    · by_cases hjt : j < idx
      · exact (hLoop.hLoopRecFwd j hjt).2
      · have hge : idx ≤ j := Nat.le_of_not_lt hjt
        rw [hLoop.hCurFwdGe j hge, hLoop.hUpdGe j hge, hLoop.hRecGt (j + 1) (by omega)]
        by_cases hjeq : j = idx
        · rw [hjeq, hLoop.hCurRecAt]
          have h1 := (hInvOrig.hRecFwd idx hidxLt).2
          have hle : (stOrig.recUpdates idx : ℝ) - (stOrig.updCount idx : ℝ) ≤
              ((stOrig.recUpdates idx + curU.length : ℕ) : ℝ) - (stOrig.updCount idx : ℝ) := by
            push_cast; linarith
          exact le_trans h1 (mul_le_mul_of_nonneg_left hle hγr_nn)
        · have hgt : idx < j := lt_of_le_of_ne hge (Ne.symm hjeq)
          rw [hLoop.hRecGt j hgt]
          exact (hInvOrig.hRecFwd j hj).2
  have hPreRecReb : ∀ j < P.d,
      ((stWithLG.rebuildCount j : ℝ) * ((intRebuildThreshold P N₀ j : ℝ) + 1) +
        if j < idx then (stWithLG.updCount j : ℝ) else 0) ≤ (stWithLG.recUpdates j : ℝ) := by
    intro j hj
    split_ifs with hjt
    · exact hLoop.hLoopRecReb j hjt
    · have hge : idx ≤ j := Nat.le_of_not_lt hjt
      dsimp only [stWithLG]
      rw [congrFun hLoop.hCnt.2 j, add_zero]
      have hOrigJ := hInvOrig.hRecRebuild j hj
      have hupdNN : (0 : ℝ) ≤ (stOrig.updCount j : ℝ) := Nat.cast_nonneg _
      by_cases hjeq : j = idx
      · rw [hjeq] at hOrigJ ⊢
        rw [hLoop.hCurRecAt]
        push_cast
        linarith
      · rw [hLoop.hRecGt j (lt_of_le_of_ne hge (Ne.symm hjeq))]; linarith
  have hInvMid : ChainInv T L TP LP P N₀ stMidCore :=
    rebuildSuffix_preserves_noHidden T L TP LP P N₀ hTP hLP hT hL hγM₀ hγk hidxLt
      G0 stWithLG.scState stWithLG.bran stWithLG.updCount
      stWithLG.curEnc stWithLG.curDecUpdates stWithLG.curFwd
      hG0Valid (by simp only [G0, ↓reduceIte]; exact hLoop.hCurGValid) hGi0V hGi0m hG0m hG0n hℓ0 hℓ_idx
      hPreHist' (fun j hj => by dsimp only [stWithLG]; rw [hLoop.hBran]; exact hInvOrig.hBran j (lt_trans hj hidxLt))
      hPreGSucc' hPreRecReb hStRecFwd (fun hpos => by dsimp only [stWithLG]; exact hLoop.hPreEnc0 hpos)
      (hLoop.hLvlM.trans hInvOrig.hLvlM) (hLoop.hN0.trans hInvOrig.hN0) rfl
  set stMid : ChainState T P :=
    { stMidCore with
      rebuildCount := fun j => if j = idx then stWithLG.rebuildCount idx + 1 else stWithLG.rebuildCount j
      closedRuntime := stWithLG.closedRuntime + retiredTool + stWithLG.curLastCost + curEncAcc
      closedTreeUpdates := stWithLG.closedTreeUpdates + retiredDec + stWithLG.curLastTreeUpdates }
  set changes := diffTreeChanges oldE stMid.toTreeChain.chainTree.E
  set stFinal : ChainState T P :=
    { stMid with closedTreeUpdates := stMid.closedTreeUpdates + changes.length }
  have hAlgoEq : algorithm1_rebuild T L P stWithLG idx curG curEncAcc = (stFinal, changes) := by
    dsimp only [algorithm1_rebuild]
    rw [dite_eq_left_iff.mpr fun h => absurd hidxLt h]
  have hRS := rebuildSuffix_spec_noHidden T L TP LP P N₀ hTP hLP hT hL hγM₀ hγk ℓ' g' (P.d - idx) idx
    G0 stWithLG.scState stWithLG.bran stWithLG.updCount
    stWithLG.curEnc stWithLG.curDecUpdates stWithLG.curFwd
    (by omega) (by simp only [G0, ↓reduceIte]; exact hLoop.hCurGValid) hGi0V hG0n hGi0m hℓ_idx hOrdIdx
  have hResEq : res = rebuildSuffix T L P (levelM TP P) N₀ ℓ' g' (P.d - idx) idx
      G0 stWithLG.scState stWithLG.bran stWithLG.updCount
      stWithLG.curEnc stWithLG.curDecUpdates stWithLG.curFwd := by
    dsimp only [res, stWithLG]; rw [hLoop.hLvlM, hInvOrig.hLvlM, hLoop.hN0, hInvOrig.hN0]
  rw [← hResEq] at hRS
  have hRebFinal : ∀ j < P.d,
      (stFinal.rebuildCount j : ℝ) * ((intRebuildThreshold P N₀ j : ℝ) + 1) +
        (stFinal.updCount j : ℝ) ≤ (stFinal.recUpdates j : ℝ) := by
    intro j hj
    dsimp only [stFinal, stMid, stMidCore, stWithLG]
    by_cases hjt : j < idx
    · have hne : j ≠ idx := Nat.ne_of_lt hjt
      simp only [hne, ↓reduceIte]
      rw [(hRS.2.1 j hjt).2.2.1]
      exact hLoop.hLoopRecReb j hjt
    · have hge : idx ≤ j := Nat.le_of_not_lt hjt
      rw [(hRS.2.2.1 j hge hj).2.1]
      by_cases hjeq : j = idx
      · subst hjeq
        simp only [↓reduceIte, Nat.cast_add, Nat.cast_one]
        have hOverMax : (intRebuildThreshold P N₀ j : ℝ) + 1 ≤
            ((st.updCount j + curU.length : ℕ) : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hOver)
        have hOrigJ := hInvOrig.hRecRebuild j hj
        rw [← congrFun hLoop.hCnt.2 j, ← hLoop.hUpdGe j (le_refl j)] at hOrigJ
        rw [hLoop.hCurRecAt]
        push_cast at hOverMax ⊢
        nlinarith
      · have hgt : idx < j := lt_of_le_of_ne hge (Ne.symm hjeq)
        simp only [hjeq, ↓reduceIte, Nat.cast_zero, add_zero]
        have hOrigJ := hInvOrig.hRecRebuild j hj
        have hupdNN : (0 : ℝ) ≤ stOrig.updCount j := Nat.cast_nonneg _
        rw [congrFun hLoop.hCnt.2 j, hLoop.hRecGt j hgt]
        linarith
  have hInvFinal : ChainInv T L TP LP P N₀ stFinal :=
    chainInv_with_bookkeeping hInvMid rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl hRebFinal
  have hG0Final : stFinal.G 0 = G0 0 := hRS.1 0 (Nat.zero_le _)
  have hn_le : (stOrig.G 0).n ≤ (stFinal.G 0).n := by
    rw [hG0Final]
    by_cases h0 : idx = 0
    · subst h0; simp only [G0, ↓reduceIte]; exact Finset.card_le_card (hLoop.hCurGV0 rfl).2.2.1
    · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
      simp only [G0, hne0, ↓reduceIte]; exact Finset.card_le_card (hLoop.hG0New (Nat.pos_of_ne_zero h0)).2.2.2.1
  have hPreActive : ∀ j < idx,
      (stWithLG.toTreeChain.activeLSF j).F.F.E = (stMidCore.toTreeChain.activeLSF j).F.F.E := by
    intro j hj
    rcases hRS.2.1 j hj with ⟨a1, a2, _⟩
    have hjlt : j < P.d := lt_trans hj hidxLt
    simp only [TreeChain.activeLSF, ChainState.toTreeChain, hjlt, ↓reduceIte]
    change (T.lsfs (stWithLG.scState j) (stWithLG.bran j)).F.F.E =
      (T.lsfs (res.2.1 j) (res.2.2.1 j)).F.F.E
    rw [a1, a2]
  have hDiffCap : (changes.length : ℝ) ≤ diffTreeCap TP P idx := by
    have hCostMid := ChainInv.level_cost_bounds_noHidden hTP hLP hγM₀ hγk hInvMid
    have htri := diffTreeChanges_chainTree_le_suffix (Nat.le_succ_of_le (Nat.le_of_lt hidxLt)) hPreActive
    have hStCard : ∀ j ≤ P.d, ((stWithLG.toTreeChain.activeLSF j).F.F.E.card : ℝ) ≤
        (levelM TP P j : ℝ) := by
      intro j hj
      by_cases hjt : j < idx
      · obtain ⟨H⟩ := hLoop.hPreHist j hjt
        have hSpec := H.hOK.noHidden P.k H.len (levelM TP P j) N₀ H.D H.ord H.restarts
          P.hk H.hG0 H.hD H.hLen H.hℓPos H.hOrd H.hInitMBound H.hInitNBound H.hRestartsLt
          (by rw [H.hUpd]; exact H.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
        have hAt := hSpec.1 H.len (le_refl _) (stWithLG.bran j) (by
          dsimp only [stWithLG]; rw [hLoop.hBran]; exact hInvOrig.hBran j (lt_trans hjt hidxLt))
        have hsubE : (T.lsfs (stWithLG.scState j) (stWithLG.bran j)).F.F.E ⊆ (stWithLG.G j).E := by
          rw [H.hRun, ← H.hEndG]
          exact hAt.1.2.1.2.2.2.2.2.1
        have hactive : (stWithLG.toTreeChain.activeLSF j).F.F.E =
            (T.lsfs (stWithLG.scState j) (stWithLG.bran j)).F.F.E := by
          simp [TreeChain.activeLSF, ChainState.toTreeChain, lt_trans hjt hidxLt]
        rw [hactive]
        exact le_trans (by exact_mod_cast Finset.card_le_card hsubE) (hLoop.hPreM j hjt)
      · have hge : idx ≤ j := Nat.le_of_not_lt hjt
        have hActEq : (stWithLG.toTreeChain.activeLSF j).F.F.E =
            (stOrig.toTreeChain.activeLSF j).F.F.E := by
          by_cases hjd : j < P.d
          · simp [TreeChain.activeLSF, ChainState.toTreeChain, hjd, stWithLG,
              hLoop.hScGe j hge, hLoop.hBran]
          · have hjeq : j = P.d := by omega
            subst hjeq
            simp [TreeChain.activeLSF, ChainState.toTreeChain, stWithLG,
              hLoop.hLast.2.1, hLoop.hLast.2.2]
        rw [hActEq]
        exact hOrigCost.2.2.2.2 j hj
    unfold diffTreeCap
    calc
      (changes.length : ℝ)
          ≤ ∑ j ∈ Finset.Ico idx (P.d + 1),
              (((stWithLG.toTreeChain.activeLSF j).F.F.E.card : ℝ) +
                ((stMid.toTreeChain.activeLSF j).F.F.E.card : ℝ)) := by exact_mod_cast htri
      _ ≤ ∑ j ∈ Finset.Ico idx (P.d + 1),
            ((levelM TP P j : ℝ) + (levelM TP P j : ℝ)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjd := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hj).2
        exact add_le_add (hStCard j hjd) (hCostMid.2.2.2.2 j hjd)
      _ = 2 * ∑ j ∈ Finset.Ico idx (P.d + 1), (levelM TP P j : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
  have hBudget : ChainBudgetInvWith TP LP N₀ stFinal (overflow + extraOverflow) := by
    refine ⟨?_, ?_⟩
    · have hOldR := hBudgetOrig.1
      have hSumEq := sum_range_inc_coeff P.d idx (Nat.le_of_lt hidxLt)
        (fun j => stOrig.shiftCount j + stOrig.rebuildCount j)
        (fun j => stFinal.shiftCount j + stFinal.rebuildCount j)
        (fun j _ => by
          dsimp only [stFinal, stMid, stMidCore, stWithLG]
          rw [hLoop.hCnt.1, hLoop.hCnt.2]
          split_ifs with h <;> [subst h; rfl]; omega)
        (opRuntimeBudget TP LP P N₀)
      have hRetTool : (retiredTool : ℝ) ≤
          ((P.k : ℝ) + 1) * (Finset.Ico idx P.d).sum (levelToolCap TP P N₀) +
            ((P.k : ℝ) + 1) *
              ∑ j ∈ Finset.Ico idx P.d, (stOrig.curRestarts j : ℝ) * restartCostCap TP P N₀ j := by
        push_cast [retiredTool]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j hj => ?_
        rw [← mul_add]
        have hmem := Finset.mem_Ico.mp hj
        by_cases hjeq : j = idx
        · subst hjeq
          rw [show stWithLG.scState j = stOrig.scState j from hLoop.hScGe j (le_refl j)]
          by_cases h0 : j = 0
          · subst h0
            rw [show stWithLG.curEnc 0 = stOrig.curEnc 0 from (hLoop.hCurEnc0 rfl).1]
            exact hOrigCost.1 0 hidxLt
          · have hpos := Nat.pos_of_ne_zero h0
            have hEncBd := (hLoop.hCurEncPos hpos).2 hidxLt
            have hEncNN : 0 ≤ 5 * TP.γ_r (P.M₀ ^ 2) *
                ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (j - 1) / (P.k : ℝ) + 1) := by
              have hγℓ_nn : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hTP.2.2.1 (P.M₀ ^ 2))
              positivity
            have hEncBd' : (st.curEnc j : ℝ) ≤ ((P.k : ℝ) + 1) *
                (5 * TP.γ_r (P.M₀ ^ 2) *
                  ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (j - 1) / (P.k : ℝ) + 1)) :=
              le_trans hEncBd (le_mul_of_one_le_left hEncNN hk1_ge)
            obtain ⟨Ho⟩ := hInvOrig.hHist j hidxLt
            have hCostO := LevelHistory.cost_le_cap_add_restart hTP hγM₀ hγk hidxLt Ho
            have hCapJ : levelToolCap TP P N₀ j =
                2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ j + 1) *
                  (P.k : ℝ) * TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P N₀) ^ TP.p_T +
                5 * TP.γ_r (P.M₀ ^ 2) *
                  ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (j - 1) / (P.k : ℝ) + 1) := by
              unfold levelToolCap; rw [ite_eq_right_iff.mpr fun h => absurd h h0]
            change (T.cost (stOrig.scState j) : ℝ) + (st.curEnc j : ℝ) ≤ _
            rw [hCapJ]
            linarith
        · have hgt : idx < j := lt_of_le_of_ne hmem.1 (Ne.symm hjeq)
          rw [show stWithLG.scState j = stOrig.scState j from hLoop.hScGe j hmem.1,
            show stWithLG.curEnc j = stOrig.curEnc j from hLoop.hEncGt j hgt]
          exact hOrigCost.1 j hmem.2
      have hLastC : (stWithLG.curLastCost : ℝ) ≤ ((P.k : ℝ) + 1) * lastCostCap TP LP P N₀ := by
        rw [show stWithLG.curLastCost = stOrig.curLastCost from hLoop.hLastStats.2.1]
        exact le_trans (hOrigCost.2.2.1 P.hd)
          (le_mul_of_one_le_left (lastCostCap_nonneg hTP hLP P N₀) hk1_ge)
      have hExBd : (curEncAcc : ℝ) ≤
          ((P.k : ℝ) + 1) * (if idx = 0 then extraEncCap P else 0) + extraOverflow := by
        by_cases h0 : idx = 0
        · subst h0
          simp only [↓reduceIte]
          have hexNN : 0 ≤ extraEncCap P := by
            unfold extraEncCap
            have hlog : 0 ≤ Real.log (2 * (P.M₀ : ℝ) + 2) :=
              Real.log_nonneg (by linarith [show (0 : ℝ) ≤ P.M₀ from Nat.cast_nonneg _])
            positivity
          have h1 := (hLoop.hCurEnc0 rfl).2.2
          have h2 : extraEncCap P ≤ ((P.k : ℝ) + 1) * extraEncCap P :=
            le_mul_of_one_le_left hexNN hk1_ge
          linarith
        · simp only [h0, ↓reduceIte, mul_zero, zero_add]
          rw [(hLoop.hCurEncPos (Nat.pos_of_ne_zero h0)).1]
          simpa using hExtraNN
      have hCR : (stFinal.closedRuntime : ℝ) =
          (stOrig.closedRuntime : ℝ) + (retiredTool : ℝ) + (stWithLG.curLastCost : ℝ) +
            (curEncAcc : ℝ) := by
        change ((stWithLG.closedRuntime + retiredTool + stWithLG.curLastCost + curEncAcc : ℕ) : ℝ) = _
        rw [show stWithLG.closedRuntime = stOrig.closedRuntime from hLoop.hClosed.1]
        push_cast; rfl
      have hCRest : stFinal.curRestarts =
          fun j => if idx ≤ j ∧ j < P.d then 0 else stOrig.curRestarts j := by
        ext j; dsimp only [stFinal, stMid, stMidCore, stWithLG]; rw [hLoop.hRestarts]
      have hAR := activeRestartCap_rebuild TP P N₀ idx (Nat.le_of_lt hidxLt) stOrig.curRestarts
      have hOpR : opRuntimeBudget TP LP P N₀ idx =
          ((P.k : ℝ) + 1) * (Finset.Ico idx P.d).sum (levelToolCap TP P N₀) +
            ((P.k : ℝ) + 1) * lastCostCap TP LP P N₀ +
            ((P.k : ℝ) + 1) * (if idx = 0 then extraEncCap P else 0) := by
        unfold opRuntimeBudget Chain.opRuntimeBudget
        rw [ite_eq_left_iff.mpr fun h => absurd hidxLt h]
        ring
      rw [hCR, hCRest, hSumEq, hOpR]
      linarith [hOldR]
    · have hSumEq := sum_range_inc_coeff P.d idx (Nat.le_of_lt hidxLt)
        (fun j => stOrig.shiftCount j + stOrig.rebuildCount j)
        (fun j => stFinal.shiftCount j + stFinal.rebuildCount j)
        (fun j _ => by
          dsimp only [stFinal, stMid, stMidCore, stWithLG]
          rw [hLoop.hCnt.1, hLoop.hCnt.2]
          split_ifs with h <;> [subst h; rfl]; omega)
        (opTreeBudget TP P)
      have hRetDec : (retiredDec : ℝ) ≤ (Finset.Ico idx P.d).sum (levelDecCap TP P) := by
        push_cast [retiredDec]
        refine Finset.sum_le_sum fun j hj => ?_
        have hmem := Finset.mem_Ico.mp hj
        rw [show stWithLG.curDecUpdates j = stOrig.curDecUpdates j from hLoop.hDecGe j hmem.1]
        exact hOrigCost.2.1 j hmem.2
      have hLastT : (stWithLG.curLastTreeUpdates : ℝ) ≤ lastTreeCap TP P := by
        rw [show stWithLG.curLastTreeUpdates = stOrig.curLastTreeUpdates from hLoop.hLastStats.2.2]
        exact hOrigCost.2.2.2.1
      have hCL : (stFinal.closedTreeUpdates : ℝ) =
          (stOrig.closedTreeUpdates : ℝ) + (retiredDec : ℝ) + (stWithLG.curLastTreeUpdates : ℝ) +
            (changes.length : ℝ) := by
        change ((stWithLG.closedTreeUpdates + retiredDec + stWithLG.curLastTreeUpdates + changes.length : ℕ) : ℝ) = _
        rw [show stWithLG.closedTreeUpdates = stOrig.closedTreeUpdates from hLoop.hClosed.2]
        push_cast; rfl
      have hOpT : opTreeBudget TP P idx =
          (Finset.Ico idx P.d).sum (levelDecCap TP P) + lastTreeCap TP P + diffTreeCap TP P idx := by
        unfold opTreeBudget; rw [ite_eq_left_iff.mpr fun h => absurd hidxLt h]
      rw [hCL, hSumEq, hOpT]
      linarith [hBudgetOrig.2]
  rw [hAlgoEq]
  refine ⟨hInvFinal, hBudget, hn_le,
    fun i => by dsimp only [stFinal, stMid, stMidCore, stWithLG]; exact (congrFun hLoop.hCnt.1 i).symm,
    fun i => by
      change stOrig.rebuildCount i ≤ if i = idx then stWithLG.rebuildCount idx + 1 else stWithLG.rebuildCount i
      have hRc := congrFun hLoop.hCnt.2
      dsimp only [stWithLG] at hRc ⊢
      split_ifs with h
      · rw [h, hRc]; exact Nat.le_succ _
      · rw [hRc],
    ?_⟩
  have hSumDec :
      (Finset.range P.d).sum stFinal.curDecUpdates + retiredDec =
        (Finset.range P.d).sum st.curDecUpdates := by
    have hsplit : Finset.range P.d = Finset.range idx ∪ Finset.Ico idx P.d := by
      ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range idx) (Finset.Ico idx P.d) := by
      rw [Finset.disjoint_left]; intro j h1 h2
      simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_union hdisj]
    have hPreEq : (Finset.range idx).sum stFinal.curDecUpdates = (Finset.range idx).sum st.curDecUpdates := by
      refine Finset.sum_congr rfl fun j hj => ?_
      exact (hRS.2.1 j (Finset.mem_range.mp hj)).2.2.2.2.1
    have hZero : (Finset.Ico idx P.d).sum stFinal.curDecUpdates = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hmem := Finset.mem_Ico.mp hj
      exact (hRS.2.2.1 j hmem.1 hmem.2).2.2.2.1
    change (Finset.range idx).sum stFinal.curDecUpdates + (Finset.Ico idx P.d).sum stFinal.curDecUpdates +
        retiredDec = _
    rw [hPreEq, hZero, add_zero]
  have hStepLen : (diffTreeChanges st.toTreeChain.chainTree.E stFinal.toTreeChain.chainTree.E).length =
      changes.length := rfl
  have hTri := diffTreeChanges_length_triangle stOrig.toTreeChain.chainTree.E
    st.toTreeChain.chainTree.E stFinal.toTreeChain.chainTree.E
  unfold ChainState.totalTreeUpdates
  change (diffTreeChanges stOrig.toTreeChain.chainTree.E stFinal.toTreeChain.chainTree.E).length +
      (stOrig.closedTreeUpdates + (Finset.range P.d).sum stOrig.curDecUpdates +
        stOrig.curLastTreeUpdates) ≤
    stWithLG.closedTreeUpdates + retiredDec + stWithLG.curLastTreeUpdates + changes.length +
      (Finset.range P.d).sum stFinal.curDecUpdates + 0
  rw [hLoop.hClosed.2, hLoop.hLastStats.2.2]
  rw [hStepLen] at hTri
  have hTD := hLoop.hTreeDiff
  omega

/-- Overflow step (`rem = rem' + 1`, `hOver`) of `updateLoop`: triggers `algorithm1_rebuild`
from `idx`, started from `rebuildStartGraph idx curG` (at level `0`, `curG` with its edges renamed
to `0, …, |E| - 1`), preserves `ChainInv` and `ChainBudgetInvWith`, and bounds tree updates. -/
lemma updateLoop_succ_over_step
    (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) {Λ : ℝ} (hT : ChainToolSupply T TP P N₀ Λ)
    (hL : L.IsSpec LP)
    (hNoReinsTool : T.ToolNoReinsertOrdRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {stOrig : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    {overflow extraOverflow : ℝ}
    (hBudgetOrig : ChainBudgetInvWith TP LP N₀ stOrig overflow) (hExtraNN : 0 ≤ extraOverflow)
    (ℓ' g' : ℕ → ℝ)
    (rem' idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ)
    (hLoop : UpdateLoopInv TP N₀ Λ extraOverflow stOrig st ℓ' g' (rem' + 1) idx curG curU curEncAcc)
    (hOver : intRebuildThreshold P N₀ idx < st.updCount idx + curU.length) :
    let (stEnd, _) := updateLoop T L TP P N₀ ℓ' g' (rem' + 1) idx st curG curU curEncAcc
    ChainInv T L TP LP P N₀ stEnd ∧
    ChainBudgetInvWith TP LP N₀ stEnd (overflow + extraOverflow) ∧
    (stOrig.G 0).n ≤ (stEnd.G 0).n ∧
    (∀ i, stOrig.shiftCount i = stEnd.shiftCount i) ∧
    (∀ i, stOrig.rebuildCount i ≤ stEnd.rebuildCount i) ∧
    (diffTreeChanges stOrig.toTreeChain.chainTree.E stEnd.toTreeChain.chainTree.E).length +
      stOrig.totalTreeUpdates ≤ stEnd.totalTreeUpdates := by
  dsimp only [updateLoop]
  rw [ite_eq_left_iff.mpr fun h => absurd hOver h]
  exact rebuild_over_step T L TP LP P hTP hLP hT hL hNoReinsTool hγM₀ hγk hInvOrig hBudgetOrig
    hExtraNN _ _ rem' idx st _ curU curEncAcc hLoop.toCore.toStart hOver

end MinCostFlow.Chain.Ordered
