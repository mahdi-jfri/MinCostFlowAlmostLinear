module

public import MinCostFlow.Chain.Ordered.UpdateStepsBase
public import MinCostFlow.Chain.Ordered.Compact

/-!
# The part of the update-loop invariant that a rebuild step uses

`updateLoop_succ_over_step` (`UpdateSteps.lean`) handles the case where level `idx` passes its
rebuild threshold and `updateLoop` calls `algorithm1_rebuild` from `idx`. The rebuild starts from
`rebuildStartGraph idx curG` with the vectors `rebuildStartFn idx curG ℓ'`, which at level `0` are
`curG` and `ℓ'` with the edges renamed to `0, …, |E| - 1`. The renamed graph is not
`(G 0).applyBatch U`, so the full invariant `UpdateLoopInv` does not hold for it.

This file defines `UpdateLoopInvCore`: the fields of `UpdateLoopInv` that the rebuild step uses,
with the order clause `hCurOrd` replaced by the existence of a rotation of the start graph with the
level order (`hCurOrdEx`). `UpdateLoopInv.toCore` forgets the other fields, and
`UpdateLoopInvCore.toStart` moves the invariant to the start graph and vectors of the rebuild.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

/-- The fields of `UpdateLoopInv` that the rebuild step of `updateLoop` uses (see the module
docstring). -/
structure UpdateLoopInvCore {T : SparseCoreRestartTool} (TP : SparseCoreParams) {P : ChainParams}
    (N₀ : ℕ) (Λ extraOverflow : ℝ) (stOrig st : ChainState T P) (ℓ' g' : ℕ → ℝ)
    (rem idx : ℕ) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ) : Prop where
  hidxSum : idx + rem = P.d
  hGGe : ∀ j, idx ≤ j → st.G j = stOrig.G j
  hScGe : ∀ j, idx ≤ j → st.scState j = stOrig.scState j
  hRestarts : st.curRestarts = stOrig.curRestarts
  hUpdGe : ∀ j, idx ≤ j → st.updCount j = stOrig.updCount j
  hDecGe : ∀ j, idx ≤ j → st.curDecUpdates j = stOrig.curDecUpdates j
  hEncGt : ∀ j, idx < j → st.curEnc j = stOrig.curEnc j
  hCurFwdGe : ∀ j, idx ≤ j → st.curFwd j = stOrig.curFwd j
  hRecGt : ∀ j, idx < j → st.recUpdates j = stOrig.recUpdates j
  hCurRecAt : st.recUpdates idx = stOrig.recUpdates idx + curU.length
  hBran : st.bran = stOrig.bran
  hLast : st.lastK = stOrig.lastK ∧ st.lastLSFs = stOrig.lastLSFs ∧ st.lastBran = stOrig.lastBran
  hLG : st.ℓ = stOrig.ℓ ∧ st.g = stOrig.g
  hCnt : st.shiftCount = stOrig.shiftCount ∧ st.rebuildCount = stOrig.rebuildCount
  hClosed : st.closedRuntime = stOrig.closedRuntime ∧ st.closedTreeUpdates = stOrig.closedTreeUpdates
  hLastStats : st.curLastRebuilds = stOrig.curLastRebuilds ∧
    st.curLastCost = stOrig.curLastCost ∧ st.curLastTreeUpdates = stOrig.curLastTreeUpdates
  hG0New : 0 < idx → (st.G 0).IsValid ∧ (st.G 0).m ≤ P.M₀ ∧ (st.G 0).n ≤ N₀ ∧
    (stOrig.G 0).V ⊆ (st.G 0).V ∧ (∀ e ∈ (st.G 0).E, 0 < ℓ' e)
  hPreHist : ∀ j < idx, Nonempty (LevelHistory T TP P N₀ { st with ℓ := ℓ', g := g' } j)
  hPreGSucc : ∀ j, j + 1 < idx → st.G (j + 1) = T.S (st.scState j) (st.bran j)
  hPreV : ∀ j < idx, (st.G j).V ⊆ (st.G 0).V
  hPreM : ∀ j < idx, ((st.G j).m : ℝ) ≤ (levelM TP P j : ℝ)
  hPreEnc0 : 0 < idx → (st.curEnc 0 : ℝ) ≤
    20 * ((levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ)) *
      Real.log ((levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ) + 2)
  hLoopRecReb : ∀ j < idx,
    (st.rebuildCount j : ℝ) * ((intRebuildThreshold P N₀ j : ℝ) + 1) +
      (st.updCount j : ℝ) ≤ (st.recUpdates j : ℝ)
  hLoopRecFwd : ∀ j < idx,
    (st.curFwd j : ℝ) ≤ TP.γ_r (P.M₀ ^ 2) * (st.updCount j : ℝ) ∧
    ((st.recUpdates (j + 1) : ℝ) - (st.curFwd j : ℝ)) ≤
      TP.γ_r (P.M₀ ^ 2) * ((st.recUpdates j : ℝ) - (st.updCount j : ℝ))
  hCurGValid : curG.IsValid
  hCurGM : (curG.m : ℝ) ≤ (levelM TP P idx : ℝ)
  hCurGV0 : idx = 0 → curG.m ≤ P.M₀ ∧ curG.n ≤ N₀ ∧ (stOrig.G 0).V ⊆ curG.V ∧
    (∀ e ∈ curG.E, 0 < ℓ' e)
  hCurGVPos : 0 < idx → curG.V ⊆ (st.G 0).V
  hCurGFromPrev : 0 < idx → curG = T.S (st.scState (idx - 1)) (st.bran (idx - 1))
  hCurOrdEx : ∃ ρ : Rotation curG,
    ρ.order = chainLevelOrd T (fun j => if j = idx then curG else st.G j) st.scState st.bran idx
  hCurEnc0 : idx = 0 → st.curEnc 0 = stOrig.curEnc 0 ∧ curEncAcc = (stOrig.G 0).batchEnc curU ∧
    (curEncAcc : ℝ) ≤ extraEncCap P + extraOverflow
  hCurEncPos : 0 < idx → curEncAcc = 0 ∧
    (idx < P.d → (st.curEnc idx : ℝ) ≤
      5 * TP.γ_r (P.M₀ ^ 2) *
        ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (idx - 1) / (P.k : ℝ) + 1))
  hCurLenRange : LevelLenRange TP P N₀ Λ idx curG
    (({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen ℓ' idx)
  hTreeDiff : (diffTreeChanges stOrig.toTreeChain.chainTree.E st.toTreeChain.chainTree.E).length +
    (Finset.range P.d).sum stOrig.curDecUpdates ≤ (Finset.range P.d).sum st.curDecUpdates
  hLvlM : st.lvlM = stOrig.lvlM
  hN0 : st.N₀ = stOrig.N₀


variable {T : SparseCoreRestartTool} {TP : SparseCoreParams} {P : ChainParams} {N₀ : ℕ}
  {Λ extraOverflow : ℝ} {stOrig st : ChainState T P} {ℓ' g' : ℕ → ℝ} {rem idx : ℕ} {curG : MGraph}
  {curU : List Update} {curEncAcc : ℕ}

/-- `UpdateLoopInv` gives its rebuild part `UpdateLoopInvCore`. -/
lemma UpdateLoopInv.toCore
    (h : UpdateLoopInv TP N₀ Λ extraOverflow stOrig st ℓ' g' rem idx curG curU curEncAcc) :
    UpdateLoopInvCore TP N₀ Λ extraOverflow stOrig st ℓ' g' rem idx curG curU curEncAcc where
  hidxSum := h.hidxSum
  hGGe := h.hGGe
  hScGe := h.hScGe
  hRestarts := h.hRestarts
  hUpdGe := h.hUpdGe
  hDecGe := h.hDecGe
  hEncGt := h.hEncGt
  hCurFwdGe := h.hCurFwdGe
  hRecGt := h.hRecGt
  hCurRecAt := h.hCurRecAt
  hBran := h.hBran
  hLast := h.hLast
  hLG := h.hLG
  hCnt := h.hCnt
  hClosed := h.hClosed
  hLastStats := h.hLastStats
  hG0New := h.hG0New
  hPreHist := h.hPreHist
  hPreGSucc := h.hPreGSucc
  hPreV := h.hPreV
  hPreM := h.hPreM
  hPreEnc0 := h.hPreEnc0
  hLoopRecReb := h.hLoopRecReb
  hLoopRecFwd := h.hLoopRecFwd
  hCurGValid := h.hCurGValid
  hCurGM := h.hCurGM
  hCurGV0 := h.hCurGV0
  hCurGVPos := h.hCurGVPos
  hCurGFromPrev := h.hCurGFromPrev
  hCurEnc0 := h.hCurEnc0
  hCurEncPos := h.hCurEncPos
  hCurLenRange := h.hCurLenRange
  hTreeDiff := h.hTreeDiff
  hLvlM := h.hLvlM
  hN0 := h.hN0
  hCurOrdEx := by
    obtain ⟨_, ρAfter, _, hAfter, _⟩ := h.hCurOrd
    exact ⟨ρAfter, hAfter⟩

/-- At level `0`, the level order of the chain with `G` at level `0` is `sortedEnds G`, which a
rotation of `G` has. -/
lemma exists_rotation_levelOrd_zero (G : MGraph) (sc : ℕ → T.State) (bran : ℕ → ℕ)
    (Gs : ℕ → MGraph) :
    ∃ ρ : Rotation G, ρ.order = chainLevelOrd T (fun j => if j = 0 then G else Gs j) sc bran 0 :=
  ⟨sortedRotation G, by simp [chainLevelOrd, sortedRotation]⟩

/-- The rebuild part of the invariant moves to the start graph and vectors of a rebuild of level
`idx`: at level `0` the edges are renamed by `compactRank`, and each edge of the start graph
carries the length of the edge of `curG` it comes from (`rebuildStartFn_exists`). -/
lemma UpdateLoopInvCore.toStart
    (h : UpdateLoopInvCore TP N₀ Λ extraOverflow stOrig st ℓ' g' rem idx curG curU curEncAcc) :
    UpdateLoopInvCore TP N₀ Λ extraOverflow stOrig st (rebuildStartFn idx curG ℓ')
      (rebuildStartFn idx curG g') rem idx (rebuildStartGraph idx curG) curU curEncAcc := by
  by_cases h0 : idx = 0
  · subst h0
    have hLen := h.hCurLenRange
    have hV0 := h.hCurGV0 rfl
    exact
    { h with
      hG0New := fun hpos => absurd hpos (lt_irrefl 0)
      hPreHist := fun _ hj => absurd hj (Nat.not_lt_zero _)
      hCurGValid := rebuildStartGraph_isValid 0 h.hCurGValid
      hCurGM := by rw [rebuildStartGraph_m]; exact h.hCurGM
      hCurGV0 := fun _ => by
        refine ⟨by rw [rebuildStartGraph_m]; exact hV0.1, by rw [rebuildStartGraph_n]; exact hV0.2.1,
          by rw [rebuildStartGraph_V]; exact hV0.2.2.1, fun j hj => ?_⟩
        obtain ⟨e, he, hfe⟩ := rebuildStartFn_exists (α := ℝ) 0 hj
        rw [hfe]; exact hV0.2.2.2 e he
      hCurGVPos := fun hpos => absurd hpos (lt_irrefl 0)
      hCurGFromPrev := fun hpos => absurd hpos (lt_irrefl 0)
      hCurOrdEx := exists_rotation_levelOrd_zero _ _ _ _
      hCurLenRange := fun j hj => by
        obtain ⟨e, he, hfe⟩ := rebuildStartFn_exists (α := ℝ) 0 hj
        have := hLen e he
        simp only [TreeChain.chainLen] at this ⊢
        rw [hfe]; exact this }
  · rw [rebuildStartFn_pos h0, rebuildStartFn_pos h0, rebuildStartGraph_pos h0]
    exact h

end MinCostFlow.Chain.Ordered
