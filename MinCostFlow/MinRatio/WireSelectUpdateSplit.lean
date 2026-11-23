module

public import MinCostFlow.MinRatio.WireSelectSplitPotModel
public import MinCostFlow.SparseCore.CanonCoreValid

import MinCostFlow.MinRatio.OrdSparseCoreHelpers
import MinCostFlow.MinRatio.PassReset
import MinCostFlow.Chain.Ordered.BudgetHelpers
import MinCostFlow.Chain.Ordered.UpdateProofs

/-!
# Surviving-edge ends and frozen potentials across `Update` on reached states (`WireSelectUpdateSplit`)

Instantiates `WireSelectSplitPotModel` (`progTool_nonRebuilt_endPotAgree` and
`progTool_nonRebuilt_selectPotInv`) directly on `algorithm1_update`, `ShiftLoopChainInv`, and
`OrdSolverReachedInv` / `alg2PreLoopState` for `sparseCoreProgTool`:

1. `algorithm1_update_nonRebuilt_structure`: unconditionally extracts from `updateLoop` either
   a rebuild starting at level `0` (or rebuilding the sole level `0` when `P.d = 0 ∧ U₀ ≠ []`), or
   the exact non-rebuilt prefix `0, …, i` and per-level batches `U 0, …, U i` (matching
   `firstRebuiltLevel P.d st.rebuildCount st'.rebuildCount`).
2. `progTool_algorithm1_update_nonRebuiltBatches`: upgrades the structural prefix into
   `NonRebuiltBatches` for `sparseCoreProgTool` using `progTool_S_updateOrd` and rotation-free
   `buildUSOrd_batchIsValid` (`CanonCoreValid.lean`).
3. `progTool_shiftLoop_update_splitPot`: for `ShiftLoopChainInv` (with `ValidOrdNoHidden`,
   `sparseCoreProgTool`, and `IsValidLSFInitFor`), proves all premises of `endPotAgree_of_split`,
   `EndPotAgree`, per-level `SelectPotInvAt`, and full `SelectPotInv` after `algorithm1_update`.
4. `progTool_reachedInv_preLoop_splitPot`: for `OrdSolverReachedInv` and `alg2PreLoopState`,
   additionally discharges `hBatch`, `NoBatchReinsert`, `IsEdgeUpdate`, and gradient stability
   `hgEq` on surviving internal edges from `OrdSolverReached`, `RefreshBatch`, and `hagree`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered
open MinCostFlow.SparseCore MinCostFlow.LSF MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program MinCostFlow.IPM.Machine

/-! ## 1. Unconditional prefix extraction from `updateLoop` -/

private theorem updateLoop_nonRebuilt_aux (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ)
    (stOrig : ChainState T P) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ)
      (Upre : ℕ → List Update),
      idx + rem = P.d →
      st.rebuildCount = stOrig.rebuildCount →
      st.bran = stOrig.bran →
      (∀ j, idx ≤ j → st.G j = stOrig.G j ∧ st.scState j = stOrig.scState j) →
      st.lastLSFs = stOrig.lastLSFs →
      st.lastBran = stOrig.lastBran →
      Upre idx = curU →
      (0 < idx → st.G 0 = (stOrig.G 0).applyBatch (Upre 0)) →
      (∀ j < idx,
        ∃ ℓj gj ordj,
          st.scState j = (T.updateOrd (stOrig.scState j) (Upre j) ℓj gj ordj).1 ∧
          Upre (j + 1) = (T.updateOrd (stOrig.scState j) (Upre j) ℓj gj ordj).2 (stOrig.bran j) ∧
          (j + 1 < idx → st.G (j + 1) = T.S (st.scState j) (stOrig.bran j))) →
      (0 < idx → curG = T.S (st.scState (idx - 1)) (stOrig.bran (idx - 1))) →
      (idx = 0 → curG = (stOrig.G 0).applyBatch curU) →
      let stEnd := (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1
      (firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount = some 0 ∨
        (P.d = 0 ∧ Upre 0 ≠ [])) ∨
      ∃ (i : ℕ) (U : ℕ → List Update),
        i ≤ P.d ∧ U 0 = Upre 0 ∧
        ((firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount = some (i + 1) ∧ i < P.d) ∨
          (firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount = none ∧
            (i = P.d ∨ (i + 1 = P.d ∧ U P.d ≠ [])))) ∧
        stEnd.G 0 = (stOrig.G 0).applyBatch (U 0) ∧
        (∀ j ≤ i, j < P.d →
          stEnd.bran j = stOrig.bran j ∧
          ∃ ℓj gj ordj,
            stEnd.scState j = (T.updateOrd (stOrig.scState j) (U j) ℓj gj ordj).1 ∧
            (j + 1 ≤ i →
              U (j + 1) = (T.updateOrd (stOrig.scState j) (U j) ℓj gj ordj).2 (stOrig.bran j) ∧
              stEnd.G (j + 1) = T.S (stEnd.scState j) (stOrig.bran j))) ∧
        (i = P.d → U P.d = [] ∧ stEnd.lastLSFs = stOrig.lastLSFs ∧ stEnd.lastBran = stOrig.lastBran) := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU curEncAcc Upre hsum hReb hBr hGe hLastL hLastB hUidx hG0 hPre hCurPrev hCur0
    have hidxEq : idx = P.d := by omega
    subst hidxEq
    dsimp only [Ordered.updateLoop]
    by_cases hEmp : curU = []
    · simp only [hEmp, ↓reduceIte]
      right
      refine ⟨P.d, Upre, le_rfl, rfl, Or.inr ⟨by rw [hReb]; exact firstRebuiltLevel_eq_of_eq _, Or.inl rfl⟩,
        ?_, ?_, ?_⟩
      · by_cases hd0 : P.d = 0
        · have hCur := hCur0 hd0
          rw [hd0] at hUidx ⊢
          simp only [↓reduceIte, hCur, hUidx]
        · have hpos : 0 < P.d := Nat.pos_of_ne_zero hd0
          simp only [show (0 : ℕ) ≠ P.d by omega, ↓reduceIte]
          exact hG0 hpos
      · intro j _ hjd
        obtain ⟨ℓj, gj, ordj, hsc, hU1, hG1⟩ := hPre j hjd
        refine ⟨congrFun hBr j, ℓj, gj, ordj, hsc, fun hj1 => ⟨hU1, ?_⟩⟩
        by_cases hlast : j + 1 = P.d
        · simp only [hlast, ↓reduceIte]
          have hpos : 0 < P.d := by omega
          have hcp := hCurPrev hpos
          rwa [show P.d - 1 = j by omega] at hcp
        · simp only [hlast, ↓reduceIte]
          exact hG1 (by omega)
      · intro _
        exact ⟨hUidx.trans hEmp, hLastL, hLastB⟩
    · simp only [hEmp, ↓reduceIte]
      by_cases hd0 : P.d = 0
      · left; right; exact ⟨hd0, by rw [← hd0, hUidx]; exact hEmp⟩
      · have hpos : 0 < P.d := Nat.pos_of_ne_zero hd0
        right
        refine ⟨P.d - 1, Upre, Nat.sub_le _ _, rfl,
          Or.inr ⟨by rw [hReb]; exact firstRebuiltLevel_eq_of_eq _,
            Or.inr ⟨by omega, by rw [hUidx]; exact hEmp⟩⟩, ?_, ?_, fun h => by omega⟩
        · simp only [show (0 : ℕ) ≠ P.d by omega, ↓reduceIte]
          exact hG0 hpos
        · intro j hj hjd
          obtain ⟨ℓj, gj, ordj, hsc, hU1, hG1⟩ := hPre j hjd
          refine ⟨congrFun hBr j, ℓj, gj, ordj, hsc, fun hj1 => ⟨hU1, ?_⟩⟩
          simp only [show j + 1 ≠ P.d by omega, ↓reduceIte]
          exact hG1 (by omega)
  | succ rem' ih =>
    intro idx st curG curU curEncAcc Upre hsum hReb hBr hGe hLastL hLastB hUidx hG0 hPre hCurPrev hCur0
    have hidxLt : idx < P.d := by omega
    dsimp only [Ordered.updateLoop]
    by_cases hOver : intRebuildThreshold P N₀ idx < st.updCount idx + curU.length
    · simp only [hOver, ↓reduceIte]
      set stLG : ChainState T P :=
        { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
      have hfirst : firstRebuiltLevel P.d stOrig.rebuildCount
          (Ordered.algorithm1_rebuild T L P stLG idx (rebuildStartGraph idx curG) curEncAcc).1.rebuildCount =
          some idx := by
        rw [← hReb]
        simp only [Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
        simpa [stLG] using Chain.firstRebuiltLevel_eq_of_inc hidxLt stLG.rebuildCount
      by_cases h0 : idx = 0
      · left; left; subst h0; exact hfirst
      · have hpos : 0 < idx := Nat.pos_of_ne_zero h0
        right
        set G0 := fun j => if j = idx then rebuildStartGraph idx curG else stLG.G j
        obtain ⟨hGpre, hSBpre, _⟩ := ordRebuildSuffix_prefix_and_coreAt T L P stLG.lvlM stLG.N₀
          stLG.ℓ stLG.g (P.d - idx) idx (by omega) G0 stLG.scState stLG.bran stLG.updCount
          stLG.curEnc stLG.curDecUpdates stLG.curFwd
        have hEndG : ∀ j < idx,
            (Ordered.algorithm1_rebuild T L P stLG idx (rebuildStartGraph idx curG) curEncAcc).1.G j = st.G j := by
          intro j hj
          simp only [Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
          rw [hGpre j (le_of_lt hj)]
          simp only [G0, show j ≠ idx by omega, ↓reduceIte, stLG]
        have hEndSc : ∀ j < idx,
            (Ordered.algorithm1_rebuild T L P stLG idx (rebuildStartGraph idx curG) curEncAcc).1.scState j =
              st.scState j := fun j hj => by
          simp only [Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
          exact (hSBpre j hj).1
        have hEndBr : ∀ j < idx,
            (Ordered.algorithm1_rebuild T L P stLG idx (rebuildStartGraph idx curG) curEncAcc).1.bran j =
              st.bran j := fun j hj => by
          simp only [Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
          exact (hSBpre j hj).2.1
        refine ⟨idx - 1, Upre, by omega, rfl, Or.inl ⟨by rwa [Nat.sub_add_cancel hpos], by omega⟩,
          by rw [hEndG 0 hpos]; exact hG0 hpos, ?_, fun h => by omega⟩
        intro j hj _
        have hjlt : j < idx := by omega
        obtain ⟨ℓj, gj, ordj, hsc, hU1, hG1⟩ := hPre j hjlt
        refine ⟨(hEndBr j hjlt).trans (congrFun hBr j), ℓj, gj, ordj, (hEndSc j hjlt).trans hsc,
          fun hj1 => ⟨hU1, ?_⟩⟩
        rw [hEndG (j + 1) (by omega), hEndSc j hjlt]
        exact hG1 (by omega)
    · simp only [hOver, ↓reduceIte]
      let Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
      let ℓi := Cpartial.chainLen ℓ' idx
      let gi := Cpartial.chainGrad g' idx
      let ord_i := chainLevelOrd T (fun j => if j = idx then curG else st.G j) st.scState st.bran idx
      let upd := T.updateOrd (st.scState idx) curU ℓi gi ord_i
      let nextG := T.S upd.1 (st.bran idx)
      let nextU := upd.2 (st.bran idx)
      let stNext : ChainState T P :=
        { st with
          G := fun j => if j = idx then curG else st.G j
          scState := fun j => if j = idx then upd.1 else st.scState j
          updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
          recUpdates := fun j =>
            if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
          curFwd := fun j =>
            if j = idx then st.curFwd idx + nextU.length else st.curFwd j
          curEnc := fun j =>
            if j = idx then st.curEnc idx + curEncAcc
            else if j = idx + 1 then st.curEnc (idx + 1) + (st.G (idx + 1)).batchEnc nextU
            else st.curEnc j
          curDecUpdates := fun j =>
            if j = idx then
              st.curDecUpdates idx +
                (diffTreeChanges (T.lsfs (st.scState idx) (st.bran idx)).F.F.E
                  (T.lsfs upd.1 (st.bran idx)).F.F.E).length
            else st.curDecUpdates j }
      let Upre' := Function.update Upre (idx + 1) nextU
      have hU0eq : Upre' 0 = Upre 0 := Function.update_of_ne (by omega) _ _
      have hRec := ih (idx + 1) stNext nextG nextU 0 Upre' (by omega) hReb hBr
        (fun j hj => by
          have hne : j ≠ idx := by omega
          exact ⟨by simpa [stNext, hne] using (hGe j (by omega)).1,
            by simpa [stNext, hne] using (hGe j (by omega)).2⟩)
        hLastL hLastB (Function.update_self (idx + 1) nextU Upre)
        (fun _ => by
          by_cases h0 : idx = 0
          · subst h0; simp only [stNext, ↓reduceIte, hU0eq, hUidx]; exact hCur0 rfl
          · simp only [stNext, show (0 : ℕ) ≠ idx by omega, ↓reduceIte, hU0eq]
            exact hG0 (Nat.pos_of_ne_zero h0))
        (fun j hj => by
          by_cases hjeq : j = idx
          · subst hjeq
            have hUj : Upre' j = curU := by
              dsimp only [Upre']
              rw [Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_self j)), hUidx]
            have hUj1 : Upre' (j + 1) = nextU := Function.update_self _ _ _
            refine ⟨ℓi, gi, ord_i, ?_, ?_, fun hlt => absurd hlt (lt_irrefl _)⟩
            · simp only [stNext, ↓reduceIte, hUj, upd, (hGe j le_rfl).2]
            · rw [hUj1, hUj]; simp only [nextU, upd, (hGe j le_rfl).2, congrFun hBr j]
          · have hjlt : j < idx := by omega
            have hUj : Upre' j = Upre j := Function.update_of_ne (by omega) _ _
            have hUj1 : Upre' (j + 1) = Upre (j + 1) := Function.update_of_ne (by omega) _ _
            obtain ⟨ℓj, gj, ordj, hsc, hU1, hG1⟩ := hPre j hjlt
            refine ⟨ℓj, gj, ordj, ?_, by rw [hUj, hUj1]; exact hU1, fun _ => ?_⟩
            · simp only [stNext, hjeq, ↓reduceIte, hUj]; exact hsc
            · by_cases hj1eq : j + 1 = idx
              · simp only [stNext, hj1eq, ↓reduceIte, hjeq]
                have hpos : 0 < idx := by omega
                have hcp := hCurPrev hpos
                rwa [show idx - 1 = j by omega] at hcp
              · simp only [stNext, hj1eq, ↓reduceIte, hjeq]
                exact hG1 (by omega))
        (fun _ => by
          simp only [Nat.add_sub_cancel, stNext, ↓reduceIte, nextG, congrFun hBr idx])
        (fun h0 => absurd h0 (Nat.succ_ne_zero idx))
      simpa only [hU0eq] using hRec

/-- Unconditional extraction of the non-rebuilt prefix `0, …, i` and per-level batches `U` from
`algorithm1_update`. -/
theorem algorithm1_update_nonRebuilt_structure (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P)
    (U₀ : List Update) (g' ℓ' : ℕ → ℝ) :
    let st' := (Ordered.algorithm1_update T L TP P N₀ st U₀ g' ℓ').1
    (firstRebuiltLevel P.d st.rebuildCount st'.rebuildCount = some 0 ∨
      (P.d = 0 ∧ U₀ ≠ [])) ∨
    ∃ (i : ℕ) (U : ℕ → List Update),
      i ≤ P.d ∧ U 0 = U₀ ∧
      ((firstRebuiltLevel P.d st.rebuildCount st'.rebuildCount = some (i + 1) ∧ i < P.d) ∨
        (firstRebuiltLevel P.d st.rebuildCount st'.rebuildCount = none ∧
          (i = P.d ∨ (i + 1 = P.d ∧ U P.d ≠ [])))) ∧
      st'.G 0 = (st.G 0).applyBatch (U 0) ∧
      (∀ j ≤ i, j < P.d →
        st'.bran j = st.bran j ∧
        ∃ ℓj gj ordj,
          st'.scState j = (T.updateOrd (st.scState j) (U j) ℓj gj ordj).1 ∧
          (j + 1 ≤ i →
            U (j + 1) = (T.updateOrd (st.scState j) (U j) ℓj gj ordj).2 (st.bran j) ∧
            st'.G (j + 1) = T.S (st'.scState j) (st.bran j))) ∧
      (i = P.d → U P.d = [] ∧ st'.lastLSFs = st.lastLSFs ∧ st'.lastBran = st.lastBran) := by
  let st0 : ChainState T P :=
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U₀.length else st.recUpdates j }
  exact updateLoop_nonRebuilt_aux T L TP P N₀ ℓ' g' st P.d 0 st0
    ((st.G 0).applyBatch U₀) U₀ ((st.G 0).batchEnc U₀) (fun _ => U₀)
    (Nat.zero_add P.d) rfl rfl (fun _ _ => ⟨rfl, rfl⟩) rfl rfl rfl
    (fun h => absurd h (lt_irrefl 0)) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun h => absurd h (lt_irrefl 0)) (fun _ => rfl)

/-! ## 2. Upgrading to `NonRebuiltBatches` for `sparseCoreProgTool` -/

private theorem progTool_step_batchIsValid {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ} {G₀ G₀' : MGraph} {ℓ ℓ' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {st st' : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    (hInv : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ st)
    (hH : st.toTreeChain.Holds G₀ ℓ σ σ_mwu γ_ℓ γ_c)
    (hH' : st'.toTreeChain.Holds G₀' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hInit : ∀ b < P.k, IsValidLSFInitFor lsfInit C_lsst P.k b)
    {k : ℕ} (hkd : k < P.d) {Uk : List Update} {ℓk gk : ℕ → ℝ} {ordk : ℕ → List End}
    (hBk : (st.G k).BatchIsValid Uk) (hGk' : st'.G k = (st.G k).applyBatch Uk)
    (hbr : st'.bran k = st.bran k)
    (hsc' : st'.scState k =
      ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd (st.scState k) Uk ℓk gk ordk).1) :
    (st.G (k + 1)).BatchIsValid
      (((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd (st.scState k) Uk ℓk gk ordk).2
        (st.bran k)) := by
  let T := sparseCoreProgTool lsfInit C_lsst depth impl
  have hGk : st.G (k + 1) = T.S (st.scState k) (st.bran k) := hInv.hGSucc k hkd
  by_cases hne : (st.scState k).isNonempty = true
  · have hup := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) (st.scState k) hne Uk ℓk gk ordk
    have hne' : (st'.scState k).isNonempty = true := by
      rw [hsc']; change (T.updateOrd _ _ _ _ _).1.isNonempty = true; rw [hup]; exact hne
    -- Extract `CompLSFInv`, `cs.G = st.G k`, and `S_cur.V = cs.RF.R` from `ChainInv`.
    let tr := (st.scState k).trees (st.bran k)
    obtain ⟨ℓ₀, hI, hcsG, hS_V⟩ := progTool_chainInv_level_compLSFInv hInv hInit hkd hne
    have hS_eq : st.G (k + 1) = tr.S_cur := by
      rw [hGk]; exact progTool_S_of_nonempty (st.scState k) hne (st.bran k)
    have hL_eq : tr.cs.lsf = st.toTreeChain.activeLSF k := by
      simp only [TreeChain.activeLSF, ChainState.toTreeChain, hkd, ↓reduceIte]
      change tr.cs.lsf = if (st.scState k).isNonempty then tr.cs.lsf else emptyLSF
      simp [hne]
    have hS_val : tr.S_cur.IsValid := by
      rw [← hS_eq]; exact st.toTreeChain.G_isValid hH (k + 1) hkd
    have hSp := ((hH.2.2.2.2.1 k hkd).2.1 (st.bran k) (hInv.hBran k hkd)).2
    have hS_sub : (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph tr.S_cur := by
      rw [← hS_eq, hcsG, hL_eq]
      simpa [TreeChain.activeLSF, ChainState.toTreeChain, hkd, hGk] using hSp.1
    -- Show `targetE' ⊆ cs_new.G.E \ cs_new.RF.F.E` via `buildUSOrd_applyBatch_E_eq` and `hH'`.
    let info := stepBundleTree (fun _ => canonicalSparsify impl) tr Uk (st.scState k).ord ordk
    have hGk'S : st'.G (k + 1) = T.S (st'.scState k) (st'.bran k) := by
      have := (hH'.2.2.2.2.1 k hkd).2.2.2
      simpa [ChainState.toTreeChain] using this
    have hS'_eq : st'.G (k + 1) = info.state.S_cur := by
      rw [hGk'S, hbr, progTool_S_of_nonempty _ hne', hsc']
      change ((T.updateOrd (st.scState k) Uk ℓk gk ordk).1.trees (st.bran k)).S_cur = _
      rw [hup]
    have hL'_eq : (compLSFBatch tr.cs Uk).lsf = st'.toTreeChain.activeLSF k := by
      simp only [TreeChain.activeLSF, ChainState.toTreeChain, hkd, ↓reduceIte, hbr]
      change (compLSFBatch tr.cs Uk).lsf =
        if (st'.scState k).isNonempty then ((st'.scState k).trees (st.bran k)).cs.lsf else emptyLSF
      rw [ite_eq_left hne', hsc']
      change _ = ((T.updateOrd (st.scState k) Uk ℓk gk ordk).1.trees (st.bran k)).cs.lsf
      rw [hup]; rfl
    have hcsG' : (compLSFBatch tr.cs Uk).G = st'.G k := by
      rw [compLSFBatch_G, hcsG, hGk']
    have hS_sub' : (coreGraph (compLSFBatch tr.cs Uk).G (compLSFBatch tr.cs Uk).lsf).IsSubgraph
        info.state.S_cur := by
      have hbr' : st'.bran k < st'.toTreeChain.k := (hH'.2.2.2.2.1 k hkd).1
      have hSp' := ((hH'.2.2.2.2.1 k hkd).2.1 (st'.bran k) hbr').2.1
      rw [← hS'_eq, hcsG', hL'_eq]
      simpa [TreeChain.activeLSF, ChainState.toTreeChain, hkd, hGk'S] using hSp'
    have hTgt_sub : info.state.S_cur.E ⊆
        (compLSFBatch tr.cs Uk).G.E \ (compLSFBatch tr.cs Uk).RF.F.E := hS_sub'.2.1
    rw [hS_eq, hup]
    change tr.S_cur.BatchIsValid info.U_S
    dsimp only [info, stepBundleTree, coreBatchOf_eq]
    refine buildUSOrd_batchIsValid hI (hcsG.symm ▸ hBk) hS_val hS_V hS_sub ?_ _
    have hEeq : info.state.S_cur.E = _ :=
      buildUSOrd_applyBatch_E_eq (canonCoreBatch tr.cs Uk) Uk (compLSFBatch tr.cs Uk) tr.S_cur _ _
    exact hEeq ▸ hTgt_sub
  · have hf : (st.scState k).isNonempty = false := Bool.eq_false_iff.mpr hne
    have hup := asm_updateOrd_of_empty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) (st.scState k) hf Uk ℓk gk ordk
    rw [hup]; trivial

/-- **Upgrading `algorithm1_update` to `NonRebuiltBatches` for `sparseCoreProgTool`.** -/
theorem progTool_algorithm1_update_nonRebuiltBatches {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ} {G₀ G₀' : MGraph} {ℓ ℓh' ℓ' g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {st : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P} {U₀ : List Update}
    (hInv : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ st)
    (hH : st.toTreeChain.Holds G₀ ℓ σ σ_mwu γ_ℓ γ_c)
    (hH' : (Ordered.algorithm1_update (sparseCoreProgTool lsfInit C_lsst depth impl) L TP P N₀ st U₀ g' ℓ').1.toTreeChain.Holds
      G₀' ℓh' σ' σ'_mwu γ'_ℓ γ'_c)
    (hInit : ∀ b < P.k, IsValidLSFInitFor lsfInit C_lsst P.k b)
    (hBatch₀ : (st.G 0).BatchIsValid U₀) (hNR₀ : NoBatchReinsert (st.G 0) U₀) :
    let st' := (Ordered.algorithm1_update (sparseCoreProgTool lsfInit C_lsst depth impl) L TP P N₀ st U₀ g' ℓ').1
    (firstRebuiltLevel P.d st.rebuildCount st'.rebuildCount = some 0 ∨
      (P.d = 0 ∧ U₀ ≠ [])) ∨
    ∃ (i : ℕ) (U : ℕ → List Update),
      U 0 = U₀ ∧
      ((firstRebuiltLevel P.d st.rebuildCount st'.rebuildCount = some (i + 1) ∧ i < P.d) ∨
        (firstRebuiltLevel P.d st.rebuildCount st'.rebuildCount = none ∧
          (i = P.d ∨ (i + 1 = P.d ∧ U P.d ≠ [])))) ∧
      NonRebuiltBatches (sparseCoreProgTool lsfInit C_lsst depth impl) st st' U i := by
  intro st'
  rcases algorithm1_update_nonRebuilt_structure (sparseCoreProgTool lsfInit C_lsst depth impl)
      L TP P N₀ st U₀ g' ℓ' with hAllReb | ⟨i, U, hi_d, hU0, hCase, hG0', hStep, hLast⟩
  · exact Or.inl hAllReb
  · right
    have hGB : ∀ j ≤ i, st'.G j = (st.G j).applyBatch (U j) ∧ (st.G j).BatchIsValid (U j) := by
      intro j
      induction j with
      | zero =>
        intro _
        exact ⟨hG0', hU0.symm ▸ hBatch₀⟩
      | succ k ih =>
        intro hk1
        have hk : k ≤ i := Nat.le_of_succ_le hk1
        have hkd : k < P.d := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (le_trans hk1 hi_d)
        obtain ⟨hGk', hBk⟩ := ih hk
        obtain ⟨hbr, ℓk, gk, ordk, hsc', hNext⟩ := hStep k hk hkd
        obtain ⟨hUk1, hGk1⟩ := hNext hk1
        refine ⟨?_, ?_⟩
        · rw [hGk1, hsc', hUk1, hInv.hGSucc k hkd]
          exact progTool_S_updateOrd (st.scState k) (U k) ℓk gk ordk (st.bran k)
        · rw [hUk1]
          exact progTool_step_batchIsValid hInv hH hH' hInit hkd hBk hGk' hbr hsc'
    refine ⟨i, U, hU0, hCase, hi_d, hU0.symm ▸ hNR₀, hGB, ?_, hLast⟩
    intro j hj hjd
    obtain ⟨hbr, ℓj, gj, ordj, hsc', hNext⟩ := hStep j hj hjd
    exact ⟨hbr, ℓj, gj, ordj, hsc', fun hj1 => (hNext hj1).1⟩

/-! ## 3. Forms for `ShiftLoopChainInv` and `OrdSolverReachedInv` -/

/-- **Items 1 & 2 on `ShiftLoopChainInv` after `algorithm1_update`.**
Starting from a chain `st` meeting `ShiftLoopChainInv` (with `sparseCoreProgTool` and
`IsValidLSFInitFor`), after `algorithm1_update` either level `0` (or all levels) is rebuilt, or
there exist the exact non-rebuilt prefix `0, …, i` and per-level batches `U` (`U 0 = U₀`) such
that, setting `φ' j = splitPot (φ j) (batchSplits (U j))` for every `j ≤ i`:
* all four premises of `endPotAgree_of_split` and `EndPotAgree st.toTreeChain st'.toTreeChain φ φ' i`
  hold;
* `SelectPotInvAt st'.toTreeChain g' φ' j` holds for every `j ≤ i`;
* combining with fresh `SelectPotInvAt` on rebuilt levels `j > i` yields full
  `SelectPotInv st'.toTreeChain g' φ'`. -/
theorem progTool_shiftLoop_update_splitPot {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {cfg : Alg2Config}
    (hT : cfg.T = sparseCoreProgTool lsfInit C_lsst depth impl)
    (hV : cfg.ValidOrdNoHidden)
    (hInit : ∀ b < cfg.P.k, IsValidLSFInitFor lsfInit C_lsst cfg.P.k b)
    {st : ChainState cfg.T cfg.P} (hShift : ShiftLoopChainInv cfg st)
    (U₀ : List Update) (g' ℓ' : ℕ → ℝ)
    (hBatch₀ : (st.G 0).BatchIsValid U₀) (hNR₀ : NoBatchReinsert (st.G 0) U₀)
    (hEdge : ∀ u ∈ U₀, IsEdgeUpdate u)
    (hG0'Valid : ((st.G 0).applyBatch U₀).IsValid)
    (hG0'm : ((st.G 0).applyBatch U₀).m ≤ cfg.P.M₀)
    (hG0'n : ((st.G 0).applyBatch U₀).n ≤ cfg.N₀)
    (hℓ'R : LenInRange (max 0 cfg.Ψ) ((st.G 0).applyBatch U₀) ℓ')
    (hℓ'Stable : ∀ e ∈ ((st.G 0).applyBatch U₀).E, e ∈ (st.G 0).E →
      (∀ u ∈ U₀, ¬ u.Inserts e) → ℓ' e = st.ℓ e)
    {φ : ℕ → ℕ → ℝ} (hPot : SelectPotInv st.toTreeChain st.g φ)
    (hgEq : ∀ f ∈ ((Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st U₀ g' ℓ').1.G 0).E,
      f ∈ (st.G 0).E → g' f = st.g f) :
    let st' := (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st U₀ g' ℓ').1
    (firstRebuiltLevel cfg.P.d st.rebuildCount st'.rebuildCount = some 0 ∨
      (cfg.P.d = 0 ∧ U₀ ≠ [])) ∨
    ∃ (i : ℕ) (U : ℕ → List Update),
      i ≤ cfg.P.d ∧ U 0 = U₀ ∧
      ((firstRebuiltLevel cfg.P.d st.rebuildCount st'.rebuildCount = some (i + 1) ∧ i < cfg.P.d) ∨
        (firstRebuiltLevel cfg.P.d st.rebuildCount st'.rebuildCount = none ∧
          (i = cfg.P.d ∨ (i + 1 = cfg.P.d ∧ U cfg.P.d ≠ [])))) ∧
      ∀ φ' : ℕ → ℕ → ℝ, (∀ j ≤ i, φ' j = splitPot (φ j) (batchSplits (U j))) →
        (∀ j ≤ i, (st.toTreeChain.G j).IsValid) ∧
        (∀ j ≤ i, ∀ v ∈ (st.toTreeChain.G j).V, φ' j v = φ j v) ∧
        (∀ j ≤ i, ∀ f ∈ (st'.toTreeChain.G j).E, f ∈ (st.toTreeChain.G j).E →
          ((st'.toTreeChain.G j).tail f = (st.toTreeChain.G j).tail f ∨
            φ' j ((st'.toTreeChain.G j).tail f) = φ j ((st.toTreeChain.G j).tail f)) ∧
          ((st'.toTreeChain.G j).head f = (st.toTreeChain.G j).head f ∨
            φ' j ((st'.toTreeChain.G j).head f) = φ j ((st.toTreeChain.G j).head f))) ∧
        EndPotAgree st.toTreeChain st'.toTreeChain φ φ' i ∧
        (∀ j ≤ i, SelectPotInvAt st'.toTreeChain g' φ' j) ∧
        ((∀ j, i < j → j ≤ cfg.P.d → SelectPotInvAt st'.toTreeChain g' φ' j) →
          SelectPotInv st'.toTreeChain g' φ') := by
  rcases cfg with ⟨T, L, TP, LP, P, σ_mwu, N₀, α, Ψ, ε⟩
  dsimp only at hT hV hInit hShift hBatch₀ hNR₀ hEdge hG0'Valid hG0'm hG0'n hℓ'R hℓ'Stable hPot hgEq ⊢
  subst hT
  obtain ⟨hInv, ⟨overflow, hBud⟩, _, _⟩ := hShift
  have hUpd := update_preserves_with_noHidden (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P
    hV.hTP hV.hLP hV.hT hV.hL hV.hNoReins hV.hγM₀ hV.hγk hInv hBud U₀ g' ℓ'
    hBatch₀ hNR₀ hEdge hG0'Valid hG0'm hG0'n hℓ'R hℓ'Stable
  dsimp only at hUpd
  have hH := (hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hH' := (hUpd.1.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  rcases progTool_algorithm1_update_nonRebuiltBatches hInv hH hH' hInit hBatch₀ hNR₀ with
    hAllReb | ⟨i, U, hU0, hCase, hNR⟩
  · exact Or.inl hAllReb
  · right
    refine ⟨i, U, hNR.1, hU0, hCase, fun φ' hPhi => ?_⟩
    obtain ⟨h1, h2, h3, hEP⟩ := progTool_nonRebuilt_endPotAgree hInv hH hH' hInit hNR hPhi
    obtain ⟨hPotAt, hPotFull⟩ := progTool_nonRebuilt_selectPotInv hInv hH hH' hInit hNR hPhi hPot hgEq
    exact ⟨h1, h2, h3, hEP, hPotAt, hPotFull⟩

/-- **Items 1 & 2 on `OrdSolverReachedInv` and `alg2PreLoopState`.**
For a solver state `model` meeting `OrdSolverReachedInv` (with `sparseCoreProgTool`,
`ValidOrdNoHidden`, and `IsValidLSFInitFor`) and a valid `RefreshBatch` meeting `hagree`,
`translateBatch` automatically discharges `hBatch₀`, `NoBatchReinsert`, `IsEdgeUpdate`, and
gradient stability `hgEq` on surviving internal edges, giving the exact premises of
`endPotAgree_of_split`, `EndPotAgree`, per-level `SelectPotInvAt`, and full `SelectPotInv` on
`pre := alg2PreLoopState cfg model U_ext g_ext l_ext`. -/
theorem progTool_reachedInv_preLoop_splitPot {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {κ : ℝ} {G : MGraph} {P : ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    (hT : cfg.T = sparseCoreProgTool lsfInit C_lsst depth impl)
    (hV : cfg.ValidOrdNoHidden)
    (hInit : ∀ b < cfg.P.k, IsValidLSFInitFor lsfInit C_lsst cfg.P.k b)
    (hm : G.m ≤ cfg.P.M₀) (hn : G.n ≤ cfg.N₀)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (h : OrdSolverReachedInv κ G P model tok)
    {U_ext : List Update} {g_ext l_ext : ℕ → ℝ}
    (hU : RefreshBatch G U_ext) (hl : ∀ e ∈ G.E, 0 < l_ext e)
    (hlR : ∀ e ∈ G.E, |Real.log (l_ext e)| ≤ cfg.Ψ)
    (hagree : ∀ e ∈ G.E, (∀ u ∈ U_ext, ¬ u.Inserts e) →
      g_ext e = model.extg e ∧ l_ext e = model.extℓ e)
    {φ : ℕ → ℕ → ℝ} (hPot : SelectPotInv model.chain.toTreeChain model.chain.g φ) :
    let tb := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U_ext
    let pre := alg2PreLoopState cfg model U_ext g_ext l_ext
    (firstRebuiltLevel cfg.P.d model.chain.rebuildCount pre.chain.rebuildCount = some 0 ∨
      (cfg.P.d = 0 ∧ tb.2.2.2.2 ≠ [])) ∨
    ∃ (i : ℕ) (U : ℕ → List Update),
      i ≤ cfg.P.d ∧ U 0 = tb.2.2.2.2 ∧
      ((firstRebuiltLevel cfg.P.d model.chain.rebuildCount pre.chain.rebuildCount = some (i + 1) ∧
          i < cfg.P.d) ∨
        (firstRebuiltLevel cfg.P.d model.chain.rebuildCount pre.chain.rebuildCount = none ∧
          (i = cfg.P.d ∨ (i + 1 = cfg.P.d ∧ U cfg.P.d ≠ [])))) ∧
      ∀ φ' : ℕ → ℕ → ℝ, (∀ j ≤ i, φ' j = splitPot (φ j) (batchSplits (U j))) →
        (∀ j ≤ i, (model.chain.toTreeChain.G j).IsValid) ∧
        (∀ j ≤ i, ∀ v ∈ (model.chain.toTreeChain.G j).V, φ' j v = φ j v) ∧
        (∀ j ≤ i, ∀ f ∈ (pre.chain.toTreeChain.G j).E, f ∈ (model.chain.toTreeChain.G j).E →
          ((pre.chain.toTreeChain.G j).tail f = (model.chain.toTreeChain.G j).tail f ∨
            φ' j ((pre.chain.toTreeChain.G j).tail f) = φ j ((model.chain.toTreeChain.G j).tail f)) ∧
          ((pre.chain.toTreeChain.G j).head f = (model.chain.toTreeChain.G j).head f ∨
            φ' j ((pre.chain.toTreeChain.G j).head f) = φ j ((model.chain.toTreeChain.G j).head f))) ∧
        EndPotAgree model.chain.toTreeChain pre.chain.toTreeChain φ φ' i ∧
        (∀ j ≤ i, SelectPotInvAt pre.chain.toTreeChain (fun e' => g_ext (tb.2.2.1 e')) φ' j) ∧
        ((∀ j, i < j → j ≤ cfg.P.d →
            SelectPotInvAt pre.chain.toTreeChain (fun e' => g_ext (tb.2.2.1 e')) φ' j) →
          SelectPotInv pre.chain.toTreeChain (fun e' => g_ext (tb.2.2.1 e')) φ') := by
  obtain ⟨D, η, op, T_step, hHist, hEdgeD, hLenD, hGD, hEq⟩ := h.2.1
  have hUncond := (algorithm2_uncond_preserves_with (η := η) κ hV hHist hEdgeD hLenD
    (fun t ht => by rw [hGD t ht]; exact hm) (fun t ht => by rw [hGD t ht]; exact hn)).1 T_step le_rfl
  rw [← hEq] at hUncond
  rcases hUncond with ⟨hInv, hBud, _, _, hFresh, hExtG, hExtLG, hChℓ, hChg, _, _, _, _, _, _⟩
  have hGT : D.G T_step = G := hGD T_step le_rfl
  have hExtG_G : model.extG = G := hExtG.trans hGT
  have hGValid : G.IsValid := hGT ▸ (hHist.2.1 T_step le_rfl).1
  have hBatch_ext : model.extG.BatchIsValid U_ext := hExtG_G.symm ▸ hU.1
  set tb := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U_ext
  have hTB := translateBatch_preserves U_ext model.extG (model.chain.G 0)
    model.extToInt model.intToExt model.nextFresh hFresh hBatch_ext
  dsimp only at hTB
  rcases hTB with ⟨hExtG', hFresh', hBatch_int, hNR_int, _, _, _, hi2e_old, _, hYesInsExt⟩
  have hExtEq : tb.1 = G := by rw [hExtG', hExtG_G]; exact hU.2.1
  have hEdgeU : ∀ u ∈ U_ext, IsEdgeUpdate u := fun u hu => by
    have hns := hU.2.2 u hu
    cases u with
    | insert _ _ _ => trivial
    | delete _ => trivial
    | split _ _ _ _ => exact absurd hns id
  have hEdge_int : ∀ u' ∈ tb.2.2.2.2, IsEdgeUpdate u' :=
    translateBatch_isEdgeUpdate model.extG model.extToInt model.intToExt model.nextFresh U_ext hEdgeU
  have hG0'Valid : ((model.chain.G 0).applyBatch tb.2.2.2.2).IsValid :=
    hFresh'.isValid_iff.mpr (hExtEq ▸ hGValid)
  have hG0'm : ((model.chain.G 0).applyBatch tb.2.2.2.2).m ≤ cfg.P.M₀ := by
    rw [hFresh'.m_eq, hExtEq]; exact hm
  have hG0'n : ((model.chain.G 0).applyBatch tb.2.2.2.2).n ≤ cfg.N₀ := by
    rw [hFresh'.n_eq, hExtEq]; exact hn
  have hℓ_intR : LenInRange (max 0 cfg.Ψ) ((model.chain.G 0).applyBatch tb.2.2.2.2)
      (fun e' => l_ext (tb.2.2.1 e')) := by
    intro e' he'
    have heExt : tb.2.2.1 e' ∈ G.E := hExtEq ▸ (hFresh'.hRight e' he').2
    have hpos := hl _ heExt
    have hlog := hlR _ heExt
    have hmax : |Real.log (l_ext (tb.2.2.1 e'))| ≤ max 0 cfg.Ψ := le_trans hlog (le_max_right _ _)
    rw [abs_le] at hmax
    dsimp only
    exact ⟨by rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hmax.1,
      by rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hmax.2⟩
  -- Surviving internal edges correspond to external edges not inserted by `U_ext`.
  have hSurvExt : ∀ e' ∈ ((model.chain.G 0).applyBatch tb.2.2.2.2).E, e' ∈ (model.chain.G 0).E →
      tb.2.2.1 e' = model.intToExt e' ∧
      model.intToExt e' ∈ G.E ∧
      (∀ u ∈ U_ext, ¬ u.Inserts (model.intToExt e')) := by
    intro e' he' he0
    have hlt : e' < model.nextFresh := hFresh.hLtFresh e' he0
    have hi2e_eq : tb.2.2.1 e' = model.intToExt e' := hi2e_old e' hlt
    have heExt : model.intToExt e' ∈ G.E := by
      rw [← hExtEq, ← hi2e_eq]; exact (hFresh'.hRight e' he').2
    refine ⟨hi2e_eq, heExt, fun u hu hIns => ?_⟩
    have hge := hYesInsExt (model.intToExt e') (hExtEq ▸ heExt) ⟨u, hu, hIns⟩
    have he2i'_eq : tb.2.1 (model.intToExt e') = e' := by
      rw [← hi2e_eq]; exact (hFresh'.hRight e' he').1
    exact absurd (lt_of_lt_of_le hlt (le_trans hge (le_of_eq he2i'_eq))) (lt_irrefl _)
  have hℓ_intStable : ∀ e' ∈ ((model.chain.G 0).applyBatch tb.2.2.2.2).E, e' ∈ (model.chain.G 0).E →
      (∀ u' ∈ tb.2.2.2.2, ¬ u'.Inserts e') →
      (fun e' => l_ext (tb.2.2.1 e')) e' = model.chain.ℓ e' := by
    intro e' he' he0 _
    obtain ⟨hi2e_eq, heExt, hNoIns⟩ := hSurvExt e' he' he0
    dsimp only
    rw [hi2e_eq, (hagree _ heExt hNoIns).2, hChℓ]
  have hConn0 : ∀ u ∈ (model.chain.G 0).V, ∀ v ∈ (model.chain.G 0).V, (model.chain.G 0).Connected u v := by
    have hWalk : ∀ {a b : ℕ} {P : List (ℕ × Bool)}, model.extG.IsWalk a b P →
        (model.chain.G 0).Connected a b := by
      intro a b P hW
      induction hW with
      | nil u => exact ⟨[], .nil u⟩
      | @cons u v x P hx hsrc _ ih =>
        obtain ⟨P', hP'⟩ := ih
        have heInt : model.extToInt x.1 ∈ (model.chain.G 0).E :=
          hFresh.hE ▸ Finset.mem_image_of_mem _ hx
        have htail := hFresh.hTail x.1 hx
        have hhead := hFresh.hHead x.1 hx
        have hsrc' : (model.chain.G 0).src (model.extToInt x.1, x.2) = u := by
          by_cases hb : x.2 = true <;> simpa [MGraph.src, hb, htail, hhead] using hsrc
        have hdst' : (model.chain.G 0).dst (model.extToInt x.1, x.2) = model.extG.dst x := by
          by_cases hb : x.2 = true <;> simp [MGraph.dst, hb, htail, hhead]
        exact ⟨(model.extToInt x.1, x.2) :: P', .cons heInt hsrc' (hdst'.symm ▸ hP')⟩
    intro u hu v hv
    have huE : u ∈ G.V := hExtG_G ▸ hFresh.hV ▸ hu
    have hvE : v ∈ G.V := hExtG_G ▸ hFresh.hV ▸ hv
    obtain ⟨P, hP⟩ := hConn u huE v hvE
    exact hWalk (hExtG_G.symm ▸ hP)
  have hℓ0R : LenInRange (max 0 cfg.Ψ) (model.chain.G 0) model.chain.ℓ := by
    intro e' he0
    have heExt : model.intToExt e' ∈ (D.G T_step).E := hExtG ▸ (hFresh.hRight e' he0).2
    have hpos := (hHist.2.1 T_step le_rfl).2 _ heExt
    have hlog := hLenD T_step le_rfl _ heExt
    have hmax : |Real.log (D.ℓ T_step (model.intToExt e'))| ≤ max 0 cfg.Ψ :=
      le_trans hlog (le_max_right _ _)
    rw [abs_le] at hmax
    have hEqℓ : model.chain.ℓ e' = D.ℓ T_step (model.intToExt e') := by
      rw [hChℓ]; exact (hExtLG _ (hExtG ▸ heExt)).1
    rw [hEqℓ]
    exact ⟨by rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hmax.1,
      by rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hmax.2⟩
  have hShift : ShiftLoopChainInv cfg model.chain := ⟨hInv, ⟨_, hBud⟩, hℓ0R, hConn0⟩
  -- Gradient stability `hgEq` on surviving internal edges of level `0` (when level `0` is not rebuilt).
  let ch1 := (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain tb.2.2.2.2
    (fun e' => g_ext (tb.2.2.1 e')) (fun e' => l_ext (tb.2.2.1 e'))).1
  by_cases hReb0 : firstRebuiltLevel cfg.P.d model.chain.rebuildCount ch1.rebuildCount = some 0
  · left; left; exact hReb0
  · by_cases hd0 : cfg.P.d = 0 ∧ tb.2.2.2.2 ≠ []
    · left; right; exact hd0
    · have hG0_eq : ch1.G 0 = (model.chain.G 0).applyBatch tb.2.2.2.2 := by
        rcases algorithm1_update_nonRebuilt_structure cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain
            tb.2.2.2.2 (fun e' => g_ext (tb.2.2.1 e')) (fun e' => l_ext (tb.2.2.1 e')) with
          hA | ⟨_, U, _, hU0, _, hG0', _, _⟩
        · rcases hA with h0 | h1
          · exact absurd h0 hReb0
          · exact absurd h1 hd0
        · rw [hG0', hU0]
      have hgEq : ∀ f ∈ (ch1.G 0).E, f ∈ (model.chain.G 0).E →
          (fun e' => g_ext (tb.2.2.1 e')) f = model.chain.g f := by
        intro f hf' hf0
        obtain ⟨hi2e_eq, heExt, hNoIns⟩ := hSurvExt f (hG0_eq ▸ hf') hf0
        dsimp only
        rw [hi2e_eq, (hagree _ heExt hNoIns).1, hChg]
      exact progTool_shiftLoop_update_splitPot hT hV hInit hShift tb.2.2.2.2
        (fun e' => g_ext (tb.2.2.1 e')) (fun e' => l_ext (tb.2.2.1 e'))
        hBatch_int hNR_int hEdge_int hG0'Valid hG0'm hG0'n hℓ_intR hℓ_intStable hPot hgEq

end MinCostFlow.MinRatio
