module

public import MinCostFlow.Chain.Ordered.UpdateStepNoRebuildHist
import MinCostFlow.Chain.Ordered.BudgetHelpers
import MinCostFlow.Chain.EncodingSize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algorithm 1 with orders: update-loop non-overflow step

Proves `updateLoop_succ_notOver_step`: when level `idx` does not exceed its rebuild threshold,
`updateLoop` advances to level `idx + 1` while preserving `UpdateLoopInv` (including the extended
ordered level history at `idx` and the ordered rotation transition `hCurOrd` at `idx + 1`).
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

/-- Non-overflow step (`rem = rem' + 1`, `¬ hOver`) of `updateLoop`: advances from `idx` to
`idx + 1` while preserving `UpdateLoopInv`. -/
lemma updateLoop_succ_notOver_step
    (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (_hLP : LP.Valid) {Λ : ℝ} (_hL : L.IsSpec LP)
    (hNoReinsTool : T.ToolNoReinsertOrdRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {stOrig : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    {overflow extraOverflow : ℝ}
    (_hBudgetOrig : ChainBudgetInvWith TP LP N₀ stOrig overflow) (_hExtraNN : 0 ≤ extraOverflow)
    (ℓ' g' : ℕ → ℝ)
    (rem' idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ)
    (hLoop : UpdateLoopInv TP N₀ Λ extraOverflow stOrig st ℓ' g' (rem' + 1) idx curG curU curEncAcc)
    (hOver : ¬ intRebuildThreshold P N₀ idx < st.updCount idx + curU.length) :
    ∃ stNext nextG nextU,
      (updateLoop T L TP P N₀ ℓ' g' (rem' + 1) idx st curG curU curEncAcc).1 =
        (updateLoop T L TP P N₀ ℓ' g' rem' (idx + 1) stNext nextG nextU 0).1 ∧
      UpdateLoopInv TP N₀ Λ extraOverflow stOrig stNext ℓ' g' rem' (idx + 1) nextG nextU 0 := by
  have hOrigLev := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInvOrig
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hidxLt : idx < P.d := by have := hLoop.hidxSum; omega
  obtain ⟨data⟩ := oupd_notOver_data T L TP LP P hTP hInvOrig ℓ' g' rem' idx st curG curU curEncAcc
    hLoop hOver
  rcases data with ⟨sc', U_S, fiChanges, nextG, nextU, nextEnc, stNext, Horig, D', ord', restarts',
    branchSeq', hHidxNew, hHidxFields, hSc'Eq, hUSEq, hFiEq, hNextGEqDef, hNextUEqDef, hNextEncDef, hStNextEq,
    hD'G0, hD'Gend, hD'Gnext, hD'Unext, hD'Valid, hD'Len, hD'ℓPos, hD'Ord, hRestLt',
    hRunPre, hRunPostPre, hRunNextPre, hRunNextPost, hUpdSum', hThresh', hBranIdx,
    hBranTail', hWinFwd', hCurFwdEq, hRebOrig, hAtEnd, hWstrStep, hRecEnd,
    hNextGValid, hNextG_eq, hNextGBatch, hNextOrd⟩
  rcases hHidxFields with ⟨hHD, hHLen, hHS0, hHOrd, hHRest⟩
  set Cpartial : TreeChain :=
    { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
  set ℓi := Cpartial.chainLen ℓ' idx
  have hUpdIdx : stNext.updCount idx = st.updCount idx + curU.length := by rw [hStNextEq]; simp
  have hCurFwdIdx : stNext.curFwd idx = st.curFwd idx + nextU.length := by rw [hStNextEq]; simp
  have hRecNextIdx : stNext.recUpdates (idx + 1) = st.recUpdates (idx + 1) + nextU.length := by
    rw [hStNextEq]; simp
  have hRecIdxEq : stNext.recUpdates idx = st.recUpdates idx := by rw [hStNextEq]; simp
  have hBranEq : stNext.bran idx = st.bran idx := by rw [hStNextEq]
  have hm0le : levelM TP P idx ≤ P.M₀ ^ 2 := levelM_le_sq hTP hγM₀ hγk idx
  have hPreEnc0Next : 0 < idx + 1 → (stNext.curEnc 0 : ℝ) ≤
      20 * ((levelM TP P 0 : ℝ) + (stNext.updCount 0 : ℝ)) *
        Real.log ((levelM TP P 0 : ℝ) + (stNext.updCount 0 : ℝ) + 2) := by
    intro _
    by_cases h0 : idx = 0
    · subst h0
      have h21 := lemma_2_1 hHidxNew.hG0 hHidxNew.hD
      have hEnc0 : stNext.curEnc 0 ≤
          (Finset.Icc 1 hHidxNew.len).sum fun s => (hHidxNew.D.G (s - 1)).batchEnc (hHidxNew.D.U s) :=
        hHidxNew.hEnc0Le rfl
      have hm0r : ((hHidxNew.D.G 0).m : ℝ) ≤ (levelM TP P 0 : ℝ) := by
        rw [hHD]; exact_mod_cast (hD'G0 ▸ Horig.hInitMBound)
      have hlog0 : 0 ≤ Real.log (((hHidxNew.D.G 0).m : ℝ) + (stNext.updCount 0 : ℝ) + 2) :=
        Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (hHidxNew.D.G 0).m from Nat.cast_nonneg _,
          show (0 : ℝ) ≤ stNext.updCount 0 from Nat.cast_nonneg _])
      have hlogLe : Real.log (((hHidxNew.D.G 0).m : ℝ) + (stNext.updCount 0 : ℝ) + 2) ≤
          Real.log ((levelM TP P 0 : ℝ) + (stNext.updCount 0 : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      rw [hHidxNew.hUpd] at h21
      have hEnc0r : (stNext.curEnc 0 : ℝ) ≤
          20 * (((hHidxNew.D.G 0).m : ℝ) + (stNext.updCount 0 : ℝ)) *
            Real.log (((hHidxNew.D.G 0).m : ℝ) + (stNext.updCount 0 : ℝ) + 2) :=
        le_trans (by exact_mod_cast hEnc0) h21
      refine le_trans hEnc0r ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by norm_num)) hlogLe hlog0 (by positivity)
    · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
      have heqC : stNext.curEnc 0 = st.curEnc 0 := by rw [hStNextEq]; simp [hne0]
      have heqU : stNext.updCount 0 = st.updCount 0 := by rw [hStNextEq]; simp [hne0]
      rw [heqC, heqU]
      exact hLoop.hPreEnc0 (Nat.pos_of_ne_zero h0)
  have hNextG_V : nextG.V ⊆ curG.V := by
    rw [hNextGEqDef]
    intro v hv
    have hvR := hAtEnd.2.1.1 hv
    exact hAtEnd.1.2.1.2.2.1 hvR
  have hNextG_m : (nextG.m : ℝ) ≤ (levelM TP P (idx + 1) : ℝ) := by
    rw [hNextGEqDef]
    have hcard : ((T.S sc' (st.bran idx)).E.card : ℝ) ≤
        (levelM TP P idx : ℝ) * TP.γ_ℓ (levelM TP P idx) / P.k :=
      hAtEnd.2.2.2.2.2.2
    have hγℓ_le : TP.γ_ℓ (levelM TP P idx) ≤ TP.γ_ℓ (P.M₀ ^ 2) := hTP.2.2.2.1 _ _ hm0le
    have hcard' : ((T.S sc' (st.bran idx)).E.card : ℝ) ≤
        (levelM TP P idx : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) / P.k :=
      le_trans hcard (by gcongr)
    exact_mod_cast levelM_step_nat hTP hγk hcard'
  have hCurGn : curG.n ≤ N₀ := by
    by_cases h0 : idx = 0
    · subst h0; exact (hLoop.hCurGV0 rfl).2.1
    · have hpos := Nat.pos_of_ne_zero h0
      exact le_trans (Finset.card_le_card (hLoop.hCurGVPos hpos)) (hLoop.hG0New hpos).2.2.1
  have hCurLenNextRange : LevelLenRange TP P N₀ Λ (idx + 1) nextG
      (({ stNext.toTreeChain with G := fun j => if j = idx + 1 then nextG else stNext.G j } : TreeChain).chainLen ℓ' (idx + 1)) := by
    intro e he
    set Cnext' : TreeChain :=
      { stNext.toTreeChain with G := fun j => if j = idx + 1 then nextG else stNext.G j }
    have heCur : e ∈ curG.E := (Finset.mem_sdiff.mp (hAtEnd.2.1.2.1 (hNextGEqDef ▸ he))).1
    have hw1 : 1 ≤ (T.lsfs sc' (st.bran idx)).wstr e := by
      have hnonneg : ∀ f ∈ curG.E, 0 ≤ ℓi f := fun f hf => (hLoop.hCurLenPos f hf).le
      exact le_trans (one_le_stretch hAtEnd.1.2.1.2.2.2.2 hnonneg heCur) (hAtEnd.1.2.2.2 e heCur).1
    have hCLpre : Cnext'.chainLen ℓ' idx = ℓi := by
      apply chainLen_congr_lt (C₁ := Cnext') (C₂ := Cpartial) ℓ' idx
        (fun j hj => by
          dsimp only [Cnext', Cpartial, ChainState.toTreeChain]
          rw [hStNextEq]
          simp [show j ≠ idx + 1 by omega, show j ≠ idx by omega])
        (fun j hj => by
          have hjlt : j < P.d := lt_trans hj hidxLt
          dsimp only [TreeChain.activeLSF, Cnext', Cpartial, ChainState.toTreeChain]
          rw [hStNextEq]
          simp [hjlt, show j ≠ idx by omega])
    have hLidx : Cnext'.activeLSF idx = T.lsfs sc' (st.bran idx) := by
      dsimp only [TreeChain.activeLSF, Cnext', ChainState.toTreeChain]
      rw [hStNextEq]; simp [hidxLt]
    have hwσ : (T.lsfs sc' (st.bran idx)).wstr e ≤ max 2 (TP.σ P.k N₀) :=
      le_trans (hAtEnd.1.2.2.2 e heCur).2
        (le_trans (hTP.2.1 _ _ _ _ le_rfl (hCurGn)) (le_max_right _ _))
    change Real.exp (-Λ) ≤ coreLen (Cnext'.activeLSF idx) (Cnext'.chainLen ℓ' idx) e ∧
      coreLen (Cnext'.activeLSF idx) (Cnext'.chainLen ℓ' idx) e ≤
        Real.exp Λ * max 2 (TP.σ P.k N₀) ^ (idx + 1)
    rw [hLidx, hCLpre]
    unfold coreLen
    exact hLoop.hCurLenRange.stretch_step heCur hw1 hwσ
  have hCurLenNextStable : ∀ e ∈ nextG.E, e ∈ (stOrig.G (idx + 1)).E → (∀ u ∈ nextU, ¬ u.Inserts e) →
      ({ stNext.toTreeChain with G := fun j => if j = idx + 1 then nextG else stNext.G j } : TreeChain).chainLen ℓ' (idx + 1) e =
        stOrig.toTreeChain.chainLen stOrig.ℓ (idx + 1) e := by
    intro e heNext heOrigNext hNoInsNext
    set Cnext' : TreeChain :=
      { stNext.toTreeChain with G := fun j => if j = idx + 1 then nextG else stNext.G j }
    have heCur : e ∈ curG.E := (Finset.mem_sdiff.mp (hAtEnd.2.1.2.1 (hNextGEqDef ▸ heNext))).1
    have heOrigIdx : e ∈ (stOrig.G idx).E := by
      have hSpOrig := (hOrigLev idx (Nat.le_of_lt hidxLt)).2.2.2.2 hidxLt (stOrig.bran idx)
        (hInvOrig.hBran idx hidxLt)
      have heS : e ∈ (T.S (stOrig.scState idx) (stOrig.bran idx)).E := by
        rw [← hInvOrig.hGSucc idx hidxLt]; exact heOrigNext
      exact (Finset.mem_sdiff.mp (hSpOrig.2.1.2.1 heS)).1
    have hNoInsCur : ∀ u ∈ curU, ¬ u.Inserts e := by
      have hNR := hNoReinsTool P.k (Horig.len + 1) (levelM TP P idx) N₀ D' ord' restarts'
        P.hk (hD'G0 ▸ Horig.hG0) hD'Valid hD'Len hD'ℓPos hD'Ord
        (hD'G0 ▸ Horig.hInitMBound) (hD'G0 ▸ Horig.hInitNBound) hRestLt' hThresh'
        (Horig.len + 1) (by omega) (le_refl _) (st.bran idx) hBranIdx
        e (by
          simp only [Nat.add_sub_cancel]
          rw [hRunPostPre Horig.len (le_refl _), ← Horig.hRun, congrFun hLoop.hBran idx,
            ← hInvOrig.hGSucc idx hidxLt]
          exact heOrigNext)
        (by
          rw [hRunNextPost]
          exact hNextGEqDef ▸ heNext)
        (fun u hu => by
          rw [hRunNextPre] at hu
          exact hNoInsNext u (hNextUEqDef ▸ hu))
      intro u hu
      exact hNR u (by rw [hD'Unext]; exact hu)
    have hCLpre : Cnext'.chainLen ℓ' idx e = stOrig.toTreeChain.chainLen stOrig.ℓ idx e := by
      have heq1 : Cnext'.chainLen ℓ' idx = ℓi := by
        apply chainLen_congr_lt (C₁ := Cnext') (C₂ := Cpartial) ℓ' idx
          (fun j hj => by
            dsimp only [Cnext', Cpartial, ChainState.toTreeChain]
            rw [hStNextEq]
            simp [show j ≠ idx + 1 by omega, show j ≠ idx by omega])
          (fun j hj => by
            have hjlt : j < P.d := lt_trans hj hidxLt
            dsimp only [TreeChain.activeLSF, Cnext', Cpartial, ChainState.toTreeChain]
            rw [hStNextEq]
            simp [hjlt, show j ≠ idx by omega])
      rw [heq1]
      exact hLoop.hCurLenStable e heCur heOrigIdx hNoInsCur
    have hWstrEq : (Cnext'.activeLSF idx).wstr e = (stOrig.toTreeChain.activeLSF idx).wstr e := by
      have h1 : Cnext'.activeLSF idx = T.lsfs sc' (st.bran idx) := by
        dsimp only [TreeChain.activeLSF, Cnext', ChainState.toTreeChain]
        rw [hStNextEq]; simp [hidxLt]
      have h2 : stOrig.toTreeChain.activeLSF idx = T.lsfs (stOrig.scState idx) (stOrig.bran idx) := by
        simp [TreeChain.activeLSF, ChainState.toTreeChain, hidxLt]
      rw [h1, h2]
      have hW := hWstrStep e (hD'Gnext.symm ▸ heCur) (hD'Gend.symm ▸ heOrigIdx)
        (fun u hu => hNoInsCur u (hD'Unext ▸ hu))
      rw [← hLoop.hScGe idx (le_refl idx), ← congrFun hLoop.hBran idx]
      exact hW
    change coreLen (Cnext'.activeLSF idx) (Cnext'.chainLen ℓ' idx) e =
      coreLen (stOrig.toTreeChain.activeLSF idx) (stOrig.toTreeChain.chainLen stOrig.ℓ idx) e
    unfold coreLen
    rw [hWstrEq, hCLpre]
  have hTreeDiffNext : (diffTreeChanges stOrig.toTreeChain.chainTree.E stNext.toTreeChain.chainTree.E).length +
      (Finset.range P.d).sum stOrig.curDecUpdates ≤ (Finset.range P.d).sum stNext.curDecUpdates := by
    have hStepDiff : (diffTreeChanges st.toTreeChain.chainTree.E stNext.toTreeChain.chainTree.E).length ≤
        fiChanges.length := by
      have hbi := diffTreeChanges_length_biUnion (Finset.range (P.d + 1))
        (fun j => (st.toTreeChain.activeLSF j).F.F.E)
        (fun j => (stNext.toTreeChain.activeLSF j).F.F.E)
      have hsplit : Finset.range (P.d + 1) = insert idx (Finset.range (P.d + 1) \ {idx}) := by
        ext j
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
        by_cases hji : j = idx
        · simp [hji]; omega
        · simp [hji]
      have hnot : idx ∉ Finset.range (P.d + 1) \ {idx} := by simp
      have hzero : (Finset.range (P.d + 1) \ {idx}).sum (fun j =>
          (diffTreeChanges (st.toTreeChain.activeLSF j).F.F.E
            (stNext.toTreeChain.activeLSF j).F.F.E).length) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hne : j ≠ idx := by simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj; exact hj.2
        have hActEq : stNext.toTreeChain.activeLSF j = st.toTreeChain.activeLSF j := by
          by_cases hjlt : j < P.d
          · dsimp only [TreeChain.activeLSF, ChainState.toTreeChain]
            rw [hStNextEq]; simp [hjlt, hne]
          · have hjeq : j = P.d := by
              have hlt' := (Finset.mem_sdiff.mp hj).1
              rw [Finset.mem_range] at hlt'; omega
            subst hjeq
            dsimp only [TreeChain.activeLSF, ChainState.toTreeChain]
            rw [hStNextEq]; simp
        rw [hActEq, diffTreeChanges_length]
        simp
      change (diffTreeChanges st.toTreeChain.chainTreeEdges stNext.toTreeChain.chainTreeEdges).length ≤ _
      unfold TreeChain.chainTreeEdges
      refine le_trans hbi ?_
      rw [hsplit, Finset.sum_insert hnot, hzero, add_zero]
      dsimp only [TreeChain.activeLSF, ChainState.toTreeChain]
      rw [hStNextEq, hFiEq]
      simp [hidxLt]
    have hSumDec : (Finset.range P.d).sum stNext.curDecUpdates =
        (Finset.range P.d).sum st.curDecUpdates + fiChanges.length := by
      have hsplit : Finset.range P.d = insert idx (Finset.range P.d \ {idx}) := by
        ext j
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
        by_cases hji : j = idx
        · simp [hji]; omega
        · simp [hji]
      have hnot : idx ∉ Finset.range P.d \ {idx} := by simp
      have hPre : (∑ j ∈ Finset.range P.d \ {idx}, stNext.curDecUpdates j) =
          ∑ j ∈ Finset.range P.d \ {idx}, st.curDecUpdates j := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hne : j ≠ idx := by simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj; exact hj.2
        rw [hStNextEq]; simp [hne]
      change (∑ j ∈ Finset.range P.d, stNext.curDecUpdates j) =
        (∑ j ∈ Finset.range P.d, st.curDecUpdates j) + fiChanges.length
      rw [hsplit, Finset.sum_insert hnot, Finset.sum_insert hnot, hPre]
      have hAtIdx : stNext.curDecUpdates idx = st.curDecUpdates idx + fiChanges.length := by
        rw [hStNextEq]; simp
      rw [hAtIdx]
      ring
    have hTri := diffTreeChanges_length_triangle stOrig.toTreeChain.chainTree.E
      st.toTreeChain.chainTree.E stNext.toTreeChain.chainTree.E
    have hTD := hLoop.hTreeDiff
    omega
  have hLoopNext : UpdateLoopInv TP N₀ Λ extraOverflow stOrig stNext ℓ' g'
      rem' (idx + 1) nextG nextU 0 := by
    refine {
      hidxSum := by have := hLoop.hidxSum; omega
      hGGe := fun j hj => by
        have hne : j ≠ idx := by omega
        rw [hStNextEq]; dsimp only; simp only [hne, ↓reduceIte]
        exact hLoop.hGGe j (by omega)
      hScGe := fun j hj => by
        have hne : j ≠ idx := by omega
        rw [hStNextEq]; dsimp only; simp only [hne, ↓reduceIte]
        exact hLoop.hScGe j (by omega)
      hRestarts := by rw [hStNextEq]; exact hLoop.hRestarts
      hUpdGe := fun j hj => by
        have hne : j ≠ idx := by omega
        rw [hStNextEq]; dsimp only; simp only [hne, ↓reduceIte]
        exact hLoop.hUpdGe j (by omega)
      hDecGe := fun j hj => by
        have hne : j ≠ idx := by omega
        rw [hStNextEq]; dsimp only; simp only [hne, ↓reduceIte]
        exact hLoop.hDecGe j (by omega)
      hEncGt := fun j hj => by
        have hne1 : j ≠ idx := by omega
        have hne2 : j ≠ idx + 1 := by omega
        rw [hStNextEq]; dsimp only; simp only [hne1, hne2, ↓reduceIte]
        exact hLoop.hEncGt j (by omega)
      hCurFwdGe := fun j hj => by
        have hne : j ≠ idx := by omega
        rw [hStNextEq]; dsimp only; simp only [hne, ↓reduceIte]
        exact hLoop.hCurFwdGe j (by omega)
      hRecGt := fun j hj => by
        have hne : j ≠ idx + 1 := by omega
        rw [hStNextEq]; dsimp only; simp only [hne, ↓reduceIte]
        exact hLoop.hRecGt j (by omega)
      hCurRecAt := by
        rw [hRecNextIdx, hLoop.hRecGt (idx + 1) (Nat.lt_succ_self idx)]
      hBran := by rw [hStNextEq]; exact hLoop.hBran
      hLast := by rw [hStNextEq]; exact hLoop.hLast
      hLG := by rw [hStNextEq]; exact hLoop.hLG
      hCnt := by rw [hStNextEq]; exact hLoop.hCnt
      hClosed := by rw [hStNextEq]; exact hLoop.hClosed
      hLastStats := by rw [hStNextEq]; exact hLoop.hLastStats
      hG0New := fun _ => by
        by_cases h0 : idx = 0
        · subst h0; rw [hStNextEq]; dsimp only; simp only [↓reduceIte]
          exact ⟨hLoop.hCurGValid, hLoop.hCurGV0 rfl⟩
        · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
          rw [hStNextEq]; dsimp only; simp only [hne0, ↓reduceIte]
          exact hLoop.hG0New (Nat.pos_of_ne_zero h0)
      hPreHist := fun j hj => by
        by_cases hjeq : j = idx
        · subst hjeq; exact ⟨hHidxNew⟩
        · have hjlt : j < idx := by omega
          obtain ⟨Hj⟩ := hLoop.hPreHist j hjlt
          have hcurEncSucc : stNext.curEnc (j + 1) = st.curEnc (j + 1) := by
            by_cases h1 : j + 1 = idx
            · have hpos : 0 < idx := by omega
              rw [hStNextEq]; simp [h1, (hLoop.hCurEncPos hpos).1]
            · have h1' : j + 1 ≠ idx := h1
              have hne0 : j ≠ idx := hjeq
              rw [hStNextEq]; dsimp only
              simp only [h1', hne0, Nat.add_right_cancel_iff, ↓reduceIte]
          have hcurEnc0 : j = 0 → stNext.curEnc 0 = st.curEnc 0 := fun hj0 => by
            subst hj0
            have hpos : 0 < idx := by omega
            rw [hStNextEq]; simp [Ne.symm (Nat.ne_of_gt hpos)]
          have hOrdJ : ({ stNext with ℓ := ℓ', g := g' } : ChainState T P).levelOrd j =
              ({ st with ℓ := ℓ', g := g' } : ChainState T P).levelOrd j := by
            unfold ChainState.levelOrd chainLevelOrd
            split_ifs with hj0
            · subst hj0
              have h0ne : (0 : ℕ) ≠ idx := Ne.symm (Nat.ne_of_gt hjlt)
              rw [hStNextEq]; simp [h0ne]
            · have hne1 : j - 1 ≠ idx := by omega
              rw [hStNextEq]; simp [hne1]
          exact ⟨{ Hj with
            hRestartsCount := by rw [hStNextEq]; exact Hj.hRestartsCount
            hS0Fresh := by rw [hStNextEq]; exact Hj.hS0Fresh
            hNoRestartAfterS0 := by rw [hStNextEq]; exact Hj.hNoRestartAfterS0
            hEndG := by rw [hStNextEq]; simp [hjeq]; exact Hj.hEndG
            hEndℓ := fun e he => by
              have hGj : stNext.G j = st.G j := by rw [hStNextEq]; simp [hjeq]
              have hCL := chainLen_congr_lt (C₁ := stNext.toTreeChain) (C₂ := st.toTreeChain) ℓ' j
                (fun m hm => by
                  change stNext.G m = st.G m
                  rw [hStNextEq]; simp [show m ≠ idx by omega])
                (fun m hm => by
                  have hmlt : m < P.d := by omega
                  dsimp only [TreeChain.activeLSF, ChainState.toTreeChain]
                  rw [hStNextEq]; simp [hmlt, show m ≠ idx by omega])
              change Hj.D.ℓ Hj.len e = stNext.toTreeChain.chainLen ℓ' j e
              rw [hCL]; exact Hj.hEndℓ e (hGj ▸ he)
            hEndg := by
              have hCG := chainGrad_congr_lt (C₁ := stNext.toTreeChain) (C₂ := st.toTreeChain) g' j
                (fun m hm => by
                  change stNext.G m = st.G m
                  rw [hStNextEq]; simp [show m ≠ idx by omega])
                (fun m hm => by
                  have hmlt : m < P.d := by omega
                  dsimp only [TreeChain.activeLSF, ChainState.toTreeChain]
                  rw [hStNextEq]; simp [hmlt, show m ≠ idx by omega])
              change Hj.D.g Hj.len = stNext.toTreeChain.chainGrad g' j
              rw [hCG]; exact Hj.hEndg
            hUpd := by rw [hStNextEq]; simp [hjeq]; exact Hj.hUpd
            hThresh := by rw [hStNextEq]; simp [hjeq]; exact Hj.hThresh
            hEndOrd := by rw [hOrdJ]; exact Hj.hEndOrd
            hRun := by rw [hStNextEq]; simp [hjeq]; exact Hj.hRun
            hBranchTail := by rw [hStNextEq]; exact Hj.hBranchTail
            hCurFwdEq := by rw [hStNextEq]; simp [hjeq]; exact Hj.hCurFwdEq
            hDecEq := by rw [hStNextEq]; simp [hjeq]; exact Hj.hDecEq
            hEnc0Le := fun h0 => by rw [hcurEnc0 h0]; exact Hj.hEnc0Le h0
            hEncLe := fun h1 => by rw [hcurEncSucc, show stNext.bran j = st.bran j by rw [hStNextEq]]; exact Hj.hEncLe h1 }⟩
      hPreGSucc := fun j hj => by
        by_cases h1 : j + 1 = idx
        · have hpos : 0 < idx := by omega
          have hjne : j ≠ idx := by omega
          have hjeq : idx - 1 = j := by omega
          rw [hStNextEq]; dsimp only; simp only [h1, hjne, ↓reduceIte]
          have hprev := hLoop.hCurGFromPrev hpos
          rw [hjeq] at hprev
          exact hprev
        · have hjne : j ≠ idx := by omega
          rw [hStNextEq]; dsimp only; simp only [h1, hjne, ↓reduceIte]
          exact hLoop.hPreGSucc j (by omega)
      hPreV := fun j hj => by
        by_cases h0 : idx = 0
        · subst h0
          have hj0 : j = 0 := by omega
          subst hj0; exact Finset.Subset.refl _
        · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
          have hG0 : stNext.G 0 = st.G 0 := by rw [hStNextEq]; simp [hne0]
          rw [hG0]
          by_cases hjeq : j = idx
          · subst hjeq; rw [hStNextEq]; dsimp only; simp only [↓reduceIte]
            exact hLoop.hCurGVPos (Nat.pos_of_ne_zero h0)
          · rw [hStNextEq]; dsimp only; simp only [hjeq, ↓reduceIte]
            exact hLoop.hPreV j (by omega)
      hPreM := fun j hj => by
        by_cases hjeq : j = idx
        · subst hjeq; rw [hStNextEq]; dsimp only; simp only [↓reduceIte]; exact hLoop.hCurGM
        · rw [hStNextEq]; dsimp only; simp only [hjeq, ↓reduceIte]; exact hLoop.hPreM j (by omega)
      hPreEnc0 := hPreEnc0Next
      hLoopRecReb := fun j hj => by
        by_cases hjeq : j = idx
        · subst hjeq
          have hrb : stNext.rebuildCount j = stOrig.rebuildCount j := by
            rw [hStNextEq]; dsimp only; rw [hLoop.hCnt.2]
          rw [hrb, hUpdIdx, hLoop.hUpdGe j (le_refl j), hRecIdxEq, hLoop.hCurRecAt]
          have hOrigJ := hInvOrig.hRecRebuild j hidxLt
          push_cast at hOrigJ ⊢
          linarith
        · have hjlt : j < idx := by omega
          have hne1 : j ≠ idx + 1 := by omega
          have hrb : stNext.rebuildCount j = st.rebuildCount j := by rw [hStNextEq]
          have hupd : stNext.updCount j = st.updCount j := by rw [hStNextEq]; simp [hjeq]
          have hrec : stNext.recUpdates j = st.recUpdates j := by rw [hStNextEq]; simp [hne1]
          rw [hrb, hupd, hrec]
          exact hLoop.hLoopRecReb j hjlt
      hLoopRecFwd := fun j hj => by
        by_cases hjeq : j = idx
        · subst hjeq
          refine ⟨?_, ?_⟩
          · have hcf : (stNext.curFwd j : ℝ) =
                (((Finset.Icc 1 (Horig.len + 1)).sum fun s =>
                  ((T.runOrdAfterUpdate P.k (levelM TP P j) N₀ D' ord' restarts' s).2
                    (branchSeq' s)).length : ℕ) : ℝ) := by
              exact_mod_cast hCurFwdEq
            have hIccSplit : Finset.Icc 1 (Horig.len + 1) =
                Finset.Icc 1 Horig.s₀ ∪ Finset.Icc (Horig.s₀ + 1) (Horig.len + 1) := by
              ext s; simp only [Finset.mem_Icc, Finset.mem_union]; have := Horig.hs₀; omega
            have hIccDisj : Disjoint (Finset.Icc 1 Horig.s₀)
                (Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)) := by
              rw [Finset.disjoint_left]; intro s h1 h2
              simp only [Finset.mem_Icc] at h1 h2; omega
            have hLHS :
                (Finset.Icc 1 (Horig.len + 1)).sum (fun s =>
                  ((T.runOrdAfterUpdate P.k (levelM TP P j) N₀ D' ord' restarts' s).2
                    (branchSeq' s)).length) =
                  (Finset.Icc 1 Horig.s₀).sum (fun s =>
                    ((T.runOrdAfterUpdate P.k (levelM TP P j) N₀ D' ord' restarts' s).2
                      (branchSeq' s)).length) +
                  (Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum (fun s =>
                    ((T.runOrdAfterUpdate P.k (levelM TP P j) N₀ D' ord' restarts' s).2
                      (st.bran j)).length) := by
              rw [hIccSplit, Finset.sum_union hIccDisj]
              congr 1
              refine Finset.sum_congr rfl fun s hs => ?_
              rcases Finset.mem_Icc.mp hs with ⟨hs1, hs2⟩
              have hbt := hBranTail' s hs1 hs2
              change branchSeq' s = stNext.bran j at hbt
              rw [hbt, hBranEq]
            have hRHS :
                (Finset.Icc 1 (Horig.len + 1)).sum (fun s => (D'.U s).length) =
                  (Finset.Icc 1 Horig.s₀).sum (fun s => (D'.U s).length) +
                  (Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum (fun s => (D'.U s).length) := by
              rw [hIccSplit, Finset.sum_union hIccDisj]
            have hγr_le := hTP.2.2.2.2.2.2.2.1 _ _ hm0le
            have hTail :
                (((Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s =>
                  ((T.runOrdAfterUpdate P.k (levelM TP P j) N₀ D' ord' restarts' s).2
                    (st.bran j)).length : ℕ) : ℝ) ≤
                  TP.γ_r (P.M₀ ^ 2) * (((Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s =>
                    (D'.U s).length : ℕ) : ℝ) :=
              le_trans hRecEnd.1 (mul_le_mul_of_nonneg_right hγr_le (Nat.cast_nonneg _))
            rw [hcf, hLHS, hUpdIdx, ← hUpdSum', hRHS, Nat.cast_add, Nat.cast_add, mul_add]
            exact add_le_add hWinFwd' hTail
          · rw [hRecNextIdx, hLoop.hRecGt (j + 1) (Nat.lt_succ_self j),
              hCurFwdIdx, hLoop.hCurFwdGe j (le_refl j),
              hRecIdxEq, hLoop.hCurRecAt, hUpdIdx, hLoop.hUpdGe j (le_refl j)]
            have hOrig2 := (hInvOrig.hRecFwd j hidxLt).2
            push_cast
            linarith
        · have hjlt : j < idx := by omega
          have hcf : stNext.curFwd j = st.curFwd j := by rw [hStNextEq]; simp [hjeq]
          have hup : stNext.updCount j = st.updCount j := by rw [hStNextEq]; simp [hjeq]
          have hr1 : stNext.recUpdates (j + 1) = st.recUpdates (j + 1) := by
            rw [hStNextEq]; dsimp only
            simp only [Nat.add_right_cancel_iff, hjeq, ↓reduceIte]
          have hr0 : stNext.recUpdates j = st.recUpdates j := by
            rw [hStNextEq]; simp [show j ≠ idx + 1 by omega]
          rw [hcf, hup, hr1, hr0]
          exact hLoop.hLoopRecFwd j hjlt
      hPreLastReb := fun hPd _ => by
        have hlast : idx + 1 = P.d := hPd
        have hieq : P.d - 1 = idx := by omega
        rw [hieq]
        refine ⟨hHidxNew, ?_⟩
        have hIcc : Finset.Icc (Horig.s₀ + 1) (Horig.len + 1) =
            insert (Horig.len + 1) (Finset.Icc (Horig.s₀ + 1) Horig.len) := by
          ext s; simp only [Finset.mem_Icc, Finset.mem_insert]; have := Horig.hs₀; omega
        have hNotMem : Horig.len + 1 ∉ Finset.Icc (Horig.s₀ + 1) Horig.len := by
          simp only [Finset.mem_Icc]; omega
        have hSumPre : (Finset.Icc (Horig.s₀ + 1) Horig.len).sum (fun s =>
              ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2
                (stNext.bran idx)).length) =
            (Finset.Icc (Horig.s₀ + 1) Horig.len).sum (fun s =>
              ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts s).2
                (stOrig.bran idx)).length) := by
          refine Finset.sum_congr rfl fun s hs => ?_
          have hsl := (Finset.mem_Icc.mp hs).2
          rw [hRunPre s hsl, hBranEq, congrFun hLoop.hBran idx]
        have hLastTerm :
            ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' (Horig.len + 1)).2
              (stNext.bran idx)).length = nextU.length := by
          rw [hRunNextPre, hBranEq, hNextUEqDef]
        have hIfLe : (if nextU = [] then 0 else 1) ≤ nextU.length := by
          cases nextU with
          | nil => simp
          | cons _ _ => simp
        rw [hHS0, hHLen, hHD, hHOrd, hHRest]
        rw [hIcc, Finset.sum_insert hNotMem, add_comm, hSumPre, hLastTerm]
        have hLastEq : stNext.curLastRebuilds = stOrig.curLastRebuilds := by
          rw [hStNextEq]; exact hLoop.hLastStats.1
        rw [hLastEq]
        have hR0 := hRebOrig hlast
        omega
      hCurGEq := hNextG_eq
      hCurGBatch := hNextGBatch
      hCurGValid := hNextGValid
      hCurGM := hNextG_m
      hCurGV0 := fun h0 => by omega
      hCurGVPos := fun _ => by
        by_cases h0 : idx = 0
        · subst h0; rw [hStNextEq]; dsimp only; simp only [↓reduceIte]; exact hNextG_V
        · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
          have hG0 : stNext.G 0 = st.G 0 := by rw [hStNextEq]; simp [hne0]
          rw [hG0]
          exact Finset.Subset.trans hNextG_V (hLoop.hCurGVPos (Nat.pos_of_ne_zero h0))
      hCurGFromPrev := fun _ => by rw [hStNextEq, hNextGEqDef]; simp
      hCurOrd := hNextOrd
      hCurEnc0 := fun h0 => by omega
      hCurEncPos := fun _ => by
        refine ⟨rfl, fun hidx1Lt => ?_⟩
        have hEncSpec := hRecEnd.2
        have hsub : Finset.Icc (Horig.s₀ + 1) (Horig.len + 1) ⊆ Finset.Icc 1 (Horig.len + 1) := by
          intro s hs; simp only [Finset.mem_Icc] at hs ⊢; omega
        have hU_sub :
            (((Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s => (D'.U s).length : ℕ) : ℝ) ≤
              (((Finset.Icc 1 (Horig.len + 1)).sum fun s => (D'.U s).length : ℕ) : ℝ) := by
          exact_mod_cast Finset.sum_le_sum_of_subset hsub
        have hEnc1 : (stNext.curEnc (idx + 1) : ℝ) ≤
            (((Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s =>
              (T.S (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ D' ord' restarts' (s - 1))
                (stNext.bran idx)).batchEnc
                ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2
                  (stNext.bran idx)) : ℕ) : ℝ) := by
          have hE := hHidxNew.hEncLe hidx1Lt
          rw [hHS0, hHLen, hHD, hHOrd, hHRest] at hE
          exact_mod_cast hE
        rw [hBranEq] at hEnc1
        have hγrle := hTP.2.2.2.2.2.2.2.1 _ _ hm0le
        have hupd_le : (((Finset.Icc 1 (Horig.len + 1)).sum fun s => (D'.U s).length : ℕ) : ℝ) ≤
            4 * (levelM TP P idx : ℝ) / (P.k : ℝ) :=
          le_trans hThresh' (updateThreshold_le_four_div P.k _ _ P.hk)
        have hγr0 : 0 ≤ TP.γ_r (levelM TP P idx) := le_trans zero_le_one (hTP.2.2.2.2.2.2.1 _)
        have hγrM0 : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hTP.2.2.2.2.2.2.1 _)
        have hm0_lt := levelM_lt_add_one hTP P idx
        have hdiv1 : (1 : ℝ) / (P.k : ℝ) ≤ 1 := by
          rw [div_le_one hk_pos]
          exact_mod_cast P.hk
        calc
          (stNext.curEnc (idx + 1) : ℝ)
              ≤ TP.γ_r (levelM TP P idx) * ((levelM TP P idx : ℝ) / (P.k : ℝ) +
                  (((Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s =>
                    (D'.U s).length : ℕ) : ℝ)) :=
                le_trans hEnc1 hEncSpec
          _ ≤ TP.γ_r (levelM TP P idx) * ((levelM TP P idx : ℝ) / (P.k : ℝ) +
                  (((Finset.Icc 1 (Horig.len + 1)).sum fun s => (D'.U s).length : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_left (add_le_add le_rfl hU_sub) hγr0
          _ ≤ TP.γ_r (P.M₀ ^ 2) *
                ((levelM TP P idx : ℝ) / (P.k : ℝ) + 4 * (levelM TP P idx : ℝ) / (P.k : ℝ)) :=
                mul_le_mul hγrle (add_le_add (le_refl _) hupd_le) (by positivity) hγrM0
          _ = 5 * TP.γ_r (P.M₀ ^ 2) * ((levelM TP P idx : ℝ) / (P.k : ℝ)) := by ring
          _ ≤ 5 * TP.γ_r (P.M₀ ^ 2) *
                (((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ idx + 1) / (P.k : ℝ)) := by
                gcongr
          _ = 5 * TP.γ_r (P.M₀ ^ 2) *
                ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ idx / (P.k : ℝ) +
                  1 / (P.k : ℝ)) := by
                ring
          _ ≤ 5 * TP.γ_r (P.M₀ ^ 2) *
                ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ idx / (P.k : ℝ) + 1) := by
                gcongr
      hCurLenRange := hCurLenNextRange
      hCurLenStable := hCurLenNextStable
      hDecMono := fun j hj => by
        by_cases hjeq : j = idx
        · subst hjeq; rw [hStNextEq]; dsimp only; simp only [↓reduceIte]
          have := hLoop.hDecMono j hj; omega
        · rw [hStNextEq]; dsimp only; simp only [hjeq, ↓reduceIte]; exact hLoop.hDecMono j hj
      hTreeDiff := hTreeDiffNext
      hLvlM := by rw [hStNextEq]; exact hLoop.hLvlM
      hN0 := by rw [hStNextEq]; exact hLoop.hN0 }
  refine ⟨stNext, nextG, nextU, ?_, hLoopNext⟩
  dsimp only [updateLoop]
  rw [ite_eq_right_iff.mpr fun h => absurd h hOver]
  rw [hStNextEq, hFiEq, hNextGEqDef, hNextEncDef, hNextUEqDef, hSc'Eq, hUSEq]

end MinCostFlow.Chain.Ordered
