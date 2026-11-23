module

public import MinCostFlow.MinRatio.SelectPhiBounded
public import MinCostFlow.MinRatio.OrdChainRefreshWiredBase
public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
public import MinCostFlow.MinRatio.WireReembModel
import MinCostFlow.Chain.Ordered.UpdateProofs
import MinCostFlow.Chain.BundleRestartBun
import MinCostFlow.Chain.BundleRestartMach
import MinCostFlow.SparseCore.SplitSpannerBase
import MinCostFlow.SparseCore.BundleCompStep
import Mathlib.Tactic

/-!
# Pure model helpers for the select-maintenance part of `Update` (`SelectUpdateModel`)

Provides the model-level lemmas needed when composing the select-region and select-heap update with
`OrdChainUpdateCoreSpecWExtKFBL` (`WireChainCoreSpecKFBL.lean`) to prove
`OrdChainUpdateCoreSpecWKFBLSel` (`OrdSelSpecs.lean`):

1. **`SelectPhiBoundedAt` across non-rebuilt splits (`selectPhiBoundedAt_of_splitPot`):**
   Lifts `splitPot_abs_le_of_batchIsValid` (`SelectPhiBounded.lean`) directly to
   `SelectPhiBoundedAt`.
2. **Gradient bound at `modelPre` (`update_g_bound_at_modelPre`):**
   Proves `∀ e ∈ (alg2PreResetState cfg model U gVec lVec).chain.G 0 |>.E,
   |(alg2PreResetState cfg model U gVec lVec).chain.g e| ≤ M_g` from `FreshInv`, `RefreshBatch`,
   and `∀ e ∈ model.extG.E, |gVec e| ≤ M_g`, handling both level-`0` rebuilds (compacted
   `compactGraph` + `compactUnrank`) and non-level-`0` rebuilds.
3. **Surviving level-`0` gradient agreement (`update_g_eq_of_not_inserts_nonRebuilt`):**
   When level `0` is not rebuilt, every surviving internal edge of `G 0` keeps its gradient across
   `alg2PreResetState` whenever external non-inserted edges keep `gVec e = model.extg e`.
4. **Decremental forest non-deletion (`compLSFBatch_noDel_of_mem_F`,
   `progTool_nonRebuilt_newF_noDel`):**
   Every edge surviving in the decremental forest `F'_j` of a non-rebuilt level `j < min firstReb d`
   is never deleted by `levelU j`, discharging `hNewFNoDel` of `selectUpdateNonRebuiltLevel_runs`.
5. **Touched-list capacity bounds (`uG_caps_of_batchWithinCaps`, `fDel_caps_of_oldGraph`):**
   Discharges `e < B.eCap` for `D.uG` and `D.fDel` from `BatchWithinCaps` and old graph caps.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered
open MinCostFlow.SparseCore MinCostFlow.LSF MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program MinCostFlow.IPM.Machine

/-! ## 1. `SelectPhiBoundedAt` across `splitPot` -/

/-- `SelectPhiBoundedAt` is preserved at a non-rebuilt level `j` when `φ' j = splitPot (φ j)
(batchSplits U)` across a valid batch `U` with `C'.G j = (C.G j).applyBatch U`. -/
theorem selectPhiBoundedAt_of_splitPot {C C' : TreeChain} {φ φ' : ℕ → ℕ → ℝ}
    {N j : ℕ} {M_g : ℝ} {U : List Update}
    (hBd : SelectPhiBoundedAt C φ N M_g j)
    (hG : C'.G j = (C.G j).applyBatch U)
    (hBV : (C.G j).BatchIsValid U)
    (hφ : φ' j = splitPot (φ j) (batchSplits U)) :
    SelectPhiBoundedAt C' φ' N M_g j := by
  intro v hv
  rw [hφ]
  exact splitPot_abs_le_of_batchIsValid hBV hBd v (hG ▸ hv)

/-! ## 2. Level-`0` graph and gradient after `updateLoop` / `alg2PreResetState` -/

private theorem updateLoop_G0_and_g_aux (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ)
    (stOrig : ChainState T P) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ),
      idx + rem = P.d →
      st.rebuildCount = stOrig.rebuildCount →
      ∀ G₀' : MGraph, (idx = 0 → curG = G₀') → (0 < idx → st.G 0 = G₀') →
        let stEnd := (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1
        (firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount = some 0 ∧
          stEnd.G 0 = G₀'.compact ∧
          stEnd.g = fun j => g' (compactUnrank G₀'.E j)) ∨
        (firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount ≠ some 0 ∧
          stEnd.G 0 = G₀' ∧
          stEnd.g = g') := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU curEncAcc hsum hReb G₀' hCur0 hG0
    have hidx : idx = P.d := by omega
    subst hidx
    dsimp only [Ordered.updateLoop]
    have hNoReb : firstRebuiltLevel P.d stOrig.rebuildCount st.rebuildCount = none := by
      rw [hReb]; exact firstRebuiltLevel_eq_of_eq _
    split_ifs <;>
    · right
      refine ⟨by change firstRebuiltLevel P.d stOrig.rebuildCount st.rebuildCount ≠ some 0
                 rw [hNoReb]; decide, ?_, rfl⟩
      by_cases hd0 : P.d = 0
      · simp only [hd0, ↓reduceIte]; exact hCur0 hd0
      · simp only [show (0 : ℕ) ≠ P.d by omega, ↓reduceIte]; exact hG0 (Nat.pos_of_ne_zero hd0)
  | succ rem' ih =>
    intro idx st curG curU curEncAcc hsum hReb G₀' hCur0 hG0
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
      set Ginit := fun j => if j = idx then rebuildStartGraph idx curG else stLG.G j
      obtain ⟨hGpre, _, _⟩ := ordRebuildSuffix_prefix_and_coreAt T L P stLG.lvlM stLG.N₀
        stLG.ℓ stLG.g (P.d - idx) idx (by omega) Ginit stLG.scState stLG.bran stLG.updCount
        stLG.curEnc stLG.curDecUpdates stLG.curFwd
      have hG0Res :
          (Ordered.algorithm1_rebuild T L P stLG idx (rebuildStartGraph idx curG) curEncAcc).1.G 0 =
          Ginit 0 := by
        simp only [Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
        exact hGpre 0 (Nat.zero_le _)
      have hgRes :
          (Ordered.algorithm1_rebuild T L P stLG idx (rebuildStartGraph idx curG) curEncAcc).1.g =
          rebuildStartFn idx curG g' := by
        simp only [Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte, stLG]
      by_cases hidx0 : idx = 0
      · subst hidx0
        left
        refine ⟨hfirst, ?_, ?_⟩
        · rw [hG0Res]; simp only [Ginit, ↓reduceIte, rebuildStartGraph, hCur0 rfl]
        · rw [hgRes]; simp only [rebuildStartFn, ↓reduceIte, hCur0 rfl]
      · right
        refine ⟨by rw [hfirst]; intro h; exact hidx0 (Option.some.inj h), ?_, ?_⟩
        · rw [hG0Res]; simp only [Ginit, Ne.symm hidx0, ↓reduceIte, stLG]
          exact hG0 (Nat.pos_of_ne_zero hidx0)
        · rw [hgRes]; simp only [rebuildStartFn, hidx0, ↓reduceIte]
    · simp only [hOver, ↓reduceIte]
      refine ih (idx + 1) _ _ _ 0 (by omega) (by exact hReb) G₀' (fun h => by omega) (fun _ => ?_)
      by_cases hidx0 : idx = 0
      · subst hidx0; simp only [↓reduceIte]; exact hCur0 rfl
      · simp only [Ne.symm hidx0, ↓reduceIte]; exact hG0 (Nat.pos_of_ne_zero hidx0)

/-- Characterizes `G 0` and `g` after `Ordered.algorithm1_update`: either level `0` rebuilt
(`G 0 = ((st.G 0).applyBatch U).compact` and `g = fun j => g' (compactUnrank ...)`), or level `0`
did not rebuild (`G 0 = (st.G 0).applyBatch U` and `g = g'`). -/
theorem algorithm1_update_G0_and_g (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P)
    (U : List Update) (g' ℓ' : ℕ → ℝ) :
    let stEnd := (Ordered.algorithm1_update T L TP P N₀ st U g' ℓ').1
    let G₀' := (st.G 0).applyBatch U
    (firstRebuiltLevel P.d st.rebuildCount stEnd.rebuildCount = some 0 ∧
      stEnd.G 0 = G₀'.compact ∧
      stEnd.g = fun j => g' (compactUnrank G₀'.E j)) ∨
    (firstRebuiltLevel P.d st.rebuildCount stEnd.rebuildCount ≠ some 0 ∧
      stEnd.G 0 = G₀' ∧
      stEnd.g = g') :=
  updateLoop_G0_and_g_aux T L TP P N₀ ℓ' g' st P.d 0
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U.length else st.recUpdates j }
    ((st.G 0).applyBatch U) U ((st.G 0).batchEnc U) (Nat.zero_add _) rfl
    ((st.G 0).applyBatch U) (fun _ => rfl) (fun h => by omega)

/-- **Gradient bound at `modelPre = alg2PreResetState cfg model U gVec lVec`:**
If `FreshInv` holds on `model`, `RefreshBatch model.extG U` holds, and `|gVec e| ≤ M_g` on
`model.extG.E`, then `|modelPre.chain.g e| ≤ M_g` for every `e ∈ (modelPre.chain.G 0).E`
(both when level `0` rebuilds with compaction and when it does not). -/
theorem update_g_bound_at_modelPre {cfg : Alg2Config} {model : Alg2State cfg}
    {U : List Update} {gVec lVec : ℕ → ℝ} {M_g : ℝ}
    (hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh)
    (hRef : RefreshBatch model.extG U)
    (hg : ∀ e ∈ model.extG.E, |gVec e| ≤ M_g) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    ∀ e ∈ (modelPre.chain.G 0).E, |modelPre.chain.g e| ≤ M_g := by
  intro modelPre e he
  set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  have hTr := translateBatch_preserves U model.extG (model.chain.G 0)
    model.extToInt model.intToExt model.nextFresh hFresh hRef.1
  dsimp only at hTr
  have hTrFresh : FreshInv tr.1 ((model.chain.G 0).applyBatch tr.2.2.2.2)
      tr.2.1 tr.2.2.1 tr.2.2.2.1 := hTr.2.1
  have hExtEq : tr.1 = model.extG := hTr.1.trans hRef.2.1
  rcases algorithm1_update_G0_and_g cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain tr.2.2.2.2
      (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e')) with
    ⟨_, hG0, hgEq⟩ | ⟨_, hG0, hgEq⟩
  · have hG0' : modelPre.chain.G 0 = ((model.chain.G 0).applyBatch tr.2.2.2.2).compact := hG0
    have hgEq' : modelPre.chain.g = fun j => gVec (tr.2.2.1 (compactUnrank
        ((model.chain.G 0).applyBatch tr.2.2.2.2).E j)) := hgEq
    rw [hG0'] at he
    have hlt : e < ((model.chain.G 0).applyBatch tr.2.2.2.2).E.card := by
      simpa [MGraph.compact] using he
    have huMem : compactUnrank ((model.chain.G 0).applyBatch tr.2.2.2.2).E e ∈
        ((model.chain.G 0).applyBatch tr.2.2.2.2).E := compactUnrank_mem hlt
    have hExtMem : tr.2.2.1 (compactUnrank ((model.chain.G 0).applyBatch tr.2.2.2.2).E e) ∈
        model.extG.E := by
      rw [← hExtEq]; exact (hTrFresh.hRight _ huMem).2
    rw [hgEq']
    exact hg _ hExtMem
  · have hG0' : modelPre.chain.G 0 = (model.chain.G 0).applyBatch tr.2.2.2.2 := hG0
    have hgEq' : modelPre.chain.g = fun e' => gVec (tr.2.2.1 e') := hgEq
    rw [hG0'] at he
    have hExtMem : tr.2.2.1 e ∈ model.extG.E := by
      rw [← hExtEq]; exact (hTrFresh.hRight _ he).2
    rw [hgEq']
    exact hg _ hExtMem

/-- When level `0` is not rebuilt (`firstRebuiltLevel ≠ some 0`), every surviving internal edge
`e ∈ (modelPre.chain.G 0).E ∩ (model.chain.G 0).E` keeps its gradient
`modelPre.chain.g e = model.chain.g e` provided external non-inserted edges satisfy `hagree` and
`model.chain.g e = model.extg (model.intToExt e)`. -/
theorem update_g_eq_of_not_rebuilt0 {cfg : Alg2Config} {model : Alg2State cfg}
    {U : List Update} {gVec lVec : ℕ → ℝ}
    (hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh)
    (hRef : RefreshBatch model.extG U)
    (hgOld : ∀ e ∈ (model.chain.G 0).E, model.chain.g e = model.extg (model.intToExt e))
    (hagree : ∀ e ∈ model.extG.E, (∀ u ∈ U, ¬ u.Inserts e) → gVec e = model.extg e)
    (hNoReb0 :
      let modelPre := alg2PreResetState cfg model U gVec lVec
      firstRebuiltLevel cfg.P.d model.chain.rebuildCount modelPre.chain.rebuildCount ≠ some 0) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    ∀ e ∈ (modelPre.chain.G 0).E, e ∈ (model.chain.G 0).E →
      modelPre.chain.g e = model.chain.g e := by
  intro modelPre e heNew heOld
  set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  have hTr := translateBatch_preserves U model.extG (model.chain.G 0)
    model.extToInt model.intToExt model.nextFresh hFresh hRef.1
  dsimp only at hTr
  have hExtEq : tr.1 = model.extG := hTr.1.trans hRef.2.1
  have hStruct := algorithm1_update_G0_and_g cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain tr.2.2.2.2
    (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e'))
  have ⟨hG0, hgEq⟩ :
      modelPre.chain.G 0 = (model.chain.G 0).applyBatch tr.2.2.2.2 ∧
      modelPre.chain.g = fun e' => gVec (tr.2.2.1 e') := by
    rcases hStruct with ⟨h0, _, _⟩ | ⟨_, hG0, hgEq⟩
    · exact absurd h0 hNoReb0
    · exact ⟨hG0, hgEq⟩
  have hlt : e < model.nextFresh := hFresh.hLtFresh e heOld
  have hI2E : tr.2.2.1 e = model.intToExt e := hTr.2.2.2.2.2.2.2.1 e hlt
  have hRight := hTr.2.1.hRight e (hG0 ▸ heNew)
  have hExtMem : model.intToExt e ∈ model.extG.E := by
    rw [← hExtEq, ← hI2E]; exact hRight.2
  have hNoInsExt : ∀ u ∈ U, ¬ u.Inserts (model.intToExt e) := by
    intro u hu hIns
    have hge : model.nextFresh ≤ tr.2.1 (model.intToExt e) :=
      hTr.2.2.2.2.2.2.2.2.2 (model.intToExt e) (hExtEq.symm ▸ hExtMem) ⟨u, hu, hIns⟩
    have heq : tr.2.1 (model.intToExt e) = e := by rw [← hI2E]; exact hRight.1
    omega
  rw [hgEq]
  dsimp only
  rw [hI2E, hagree (model.intToExt e) hExtMem hNoInsExt, hgOld e heOld]

/-! ## 3. Decremental forest non-deletion (`compLSFBatch_noDel_of_mem_F`) -/

private theorem compLSFInv_F_E_subset_G_E {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) : cs.RF.F.E ⊆ cs.G.E := by
  intro e he
  change e ∈ (components cs.G₀).biUnion (fun C => (cs.compSt C).RF.F.E) at he
  rw [Finset.mem_biUnion] at he
  obtain ⟨C, hC, heF⟩ := he
  exact hI.hCE_sub C hC ((hI.hCompLSF C hC).1.hF_sub_G.2.1 heF)

/-- No edge surviving in the decremental forest `(compLSFBatch cs U).lsf.F.F.E` was deleted by `U`. -/
theorem compLSFBatch_noDel_of_mem_F {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) :
    ∀ {U : List Update}, cs.G.BatchIsValid U →
      ∀ e ∈ (compLSFBatch cs U).lsf.F.F.E, Update.delete e ∉ U
  | [], _, _, _, h => by cases h
  | u :: rest, hBV, e, he, hmem => by
    have hI1 : CompLSFInv C_lsst ℓ₀ (compLSFStepSingle cs u) := compLSFInv_step hI hBV.1
    have hBV1 : (compLSFStepSingle cs u).G.BatchIsValid rest := hBV.2
    rcases List.mem_cons.mp hmem with rfl | hrest
    · have hsub : (compLSFBatch (compLSFStepSingle cs (.delete e)) rest).lsf.F.F.E ⊆
          (compLSFStepSingle cs (.delete e)).lsf.F.F.E :=
        (compLSFBatch_decremental hI1 hBV1).1
      have he1 : e ∈ (compLSFStepSingle cs (.delete e)).RF.F.E := hsub he
      have heG1 : e ∈ (compLSFStepSingle cs (.delete e)).G.E := compLSFInv_F_E_subset_G_E hI1 he1
      simp [compLSFStepSingle, MGraph.applyUpdate] at heG1
    · exact compLSFBatch_noDel_of_mem_F hI1 hBV1 e he hrest

/-- On every non-rebuilt level `j < P.d` of `NonRebuiltBatches` for `sparseCoreProgTool`, every
edge in the updated active forest `F'_j` satisfies `Update.delete e ∉ U j`. -/
theorem progTool_nonRebuilt_newF_noDel {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ}
    {st st' : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    {U : ℕ → List Update} {i j : ℕ}
    (hInv : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ st)
    (hInit : ∀ b < P.k, IsValidLSFInitFor lsfInit C_lsst P.k b)
    (hNR : NonRebuiltBatches (sparseCoreProgTool lsfInit C_lsst depth impl) st st' U i)
    (hj : j ≤ i) (hjd : j < P.d) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    ∀ e ∈ (T.lsfs (st'.scState j) (st'.bran j)).F.F.E, Update.delete e ∉ U j := by
  intro T e he
  obtain ⟨_, _, hGB, hStep, _⟩ := hNR
  obtain ⟨hbr, ℓj, gj, ordj, hsc', _⟩ := hStep j hj hjd
  rw [hbr] at he
  by_cases hne : (st.scState j).isNonempty = true
  · obtain ⟨_, hI, hcsG, _⟩ := progTool_chainInv_level_compLSFInv hInv hInit hjd hne
    have hup := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) (st.scState j) hne (U j) ℓj gj ordj
    have hne' : (st'.scState j).isNonempty = true := by
      rw [hsc']; change (T.updateOrd _ _ _ _ _).1.isNonempty = true; rw [hup]; exact hne
    have hL_new : T.lsfs (st'.scState j) (st.bran j) =
        (compLSFBatch ((st.scState j).trees (st.bran j)).cs (U j)).lsf := by
      change (if (st'.scState j).isNonempty then _ else _) = _
      rw [ite_eq_left hne', hsc']
      change ((T.updateOrd (st.scState j) (U j) ℓj gj ordj).1.trees (st.bran j)).cs.lsf = _
      rw [hup]; rfl
    rw [hL_new] at he
    exact compLSFBatch_noDel_of_mem_F hI (hcsG.symm ▸ (hGB j hj).2) e he
  · have hf : (st.scState j).isNonempty = false := Bool.eq_false_iff.mpr hne
    have hup := asm_updateOrd_of_empty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) (st.scState j) hf (U j) ℓj gj ordj
    have hne' : (st'.scState j).isNonempty = false := by
      rw [hsc']; change (T.updateOrd _ _ _ _ _).1.isNonempty = false; rw [hup]; exact hf
    have hEmpty : (T.lsfs (st'.scState j) (st.bran j)).F.F.E = ∅ := by
      change (if (st'.scState j).isNonempty then _ else emptyLSF).F.F.E = ∅
      simp [hne', emptyLSF, emptyGraph]
    rw [hEmpty] at he; cases he

/-! ## 4. Touched-list capacity helpers -/

/-- Every edge in `coreBatchTouchedEdges U` lies below `eCap` whenever `oldG.BatchIsValid U`,
`BatchWithinCaps vCap eCap U`, and every edge of `oldG.E` lies below `eCap`. -/
theorem mem_coreBatchTouchedEdges_lt_eCap {vCap eCap : ℕ} :
    ∀ {oldG : MGraph} {U : List Update},
      oldG.BatchIsValid U →
      (∀ e ∈ oldG.E, e < eCap) →
      BatchWithinCaps vCap eCap U →
      ∀ e ∈ coreBatchTouchedEdges U, e < eCap
  | _, [], _, _, _, _, h => by cases h
  | oldG, .insert e₀ a b :: rest, hBV, hG, hC, e, h => by
    simp only [coreBatchTouchedEdges, List.mem_cons] at h
    have he₀ : e₀ < eCap := hC (.insert e₀ a b) List.mem_cons_self
    rcases h with rfl | hr
    · exact he₀
    · refine mem_coreBatchTouchedEdges_lt_eCap hBV.2 (fun x hx => ?_)
        (fun u hu => hC u (List.mem_cons_of_mem _ hu)) e hr
      simp only [MGraph.applyUpdate, Finset.mem_insert] at hx
      rcases hx with rfl | hx'
      · exact he₀
      · exact hG x hx'
  | oldG, .delete e₀ :: rest, hBV, hG, hC, e, h => by
    simp only [coreBatchTouchedEdges, List.mem_cons] at h
    rcases h with rfl | hr
    · exact hG e hBV.1
    · refine mem_coreBatchTouchedEdges_lt_eCap hBV.2 (fun x hx => ?_)
        (fun u hu => hC u (List.mem_cons_of_mem _ hu)) e hr
      simp only [MGraph.applyUpdate, Finset.mem_erase] at hx
      exact hG x hx.2
  | oldG, .split v v' St Sh :: rest, hBV, hG, hC, e, h =>
    mem_coreBatchTouchedEdges_lt_eCap hBV.2 (fun x hx => hG x hx)
      (fun u hu => hC u (List.mem_cons_of_mem _ hu)) e h

/-- Every edge in `fDel` lies below `eCap` when `fDel.toFinset = oldF.E \ newF.E`, `oldF.E ⊆ oldG.E`,
and all edges of `oldG.E` lie below `eCap`. -/
theorem mem_fDel_lt_eCap {eCap : ℕ} {oldG oldF newF : MGraph} {fDel : List ℕ}
    (hEq : fDel.toFinset = oldF.E \ newF.E)
    (hSub : oldF.E ⊆ oldG.E) (hCap : ∀ e ∈ oldG.E, e < eCap) :
    ∀ e ∈ fDel, e < eCap := fun e he => by
  have hm : e ∈ oldF.E \ newF.E := hEq ▸ List.mem_toFinset.mpr he
  exact hCap e (hSub (Finset.mem_sdiff.mp hm).1)

/-! ## 5. Re-embedded edge list capacity bound (`progReemb_mem_G_or_S`, `progReemb_lt_eCap`) -/

private theorem applyBatch_E_subset_of_delOrSplit :
    ∀ {G : MGraph} {U : List Update}, (∀ u ∈ U, isDelOrSplit u) → (G.applyBatch U).E ⊆ G.E
  | _, [], _ => Finset.Subset.refl _
  | G, u :: rest, hds => by
    have hu : isDelOrSplit u := hds u List.mem_cons_self
    have hrest : ∀ v ∈ rest, isDelOrSplit v := fun v hv => hds v (List.mem_cons_of_mem u hv)
    have h1 : (G.applyUpdate u).E ⊆ G.E := by
      cases u with
      | insert _ _ _ => simp [isDelOrSplit] at hu
      | delete e => exact Finset.erase_subset e G.E
      | split _ _ _ _ => exact Finset.Subset.refl _
    exact Finset.Subset.trans
      (applyBatch_E_subset_of_delOrSplit (G := G.applyUpdate u) (U := rest) hrest) h1

private theorem bundleCompStep_isDelOrSplit {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} :
    ∀ u ∈ (bundleCompStep cs B k ord ord' U).1, isDelOrSplit u := by
  by_cases hR : BundleStepReady cs B k ord ord' U
  · rw [bundleCompStep_eq hR]
    exact (bundleRunsStep_spec hR).1.2.2.2.1
  · rw [bundleCompStep_of_not hR]
    intro _ h; cases h

private theorem mem_restrictSplits_ne_delete {keep : Finset ℕ} {e : ℕ} :
    ∀ {UC : List Update}, Update.delete e ∉ restrictSplits keep UC
  | [] => by simp [restrictSplits]
  | .insert _ _ _ :: rest => mem_restrictSplits_ne_delete (UC := rest)
  | .delete _ :: rest => mem_restrictSplits_ne_delete (UC := rest)
  | .split _ _ _ _ :: rest => by
    have hrest := mem_restrictSplits_ne_delete (keep := keep) (e := e) (UC := rest)
    simp [restrictSplits, hrest]

private theorem mem_buildUSOrd_delete {UC U : List Update} {cs_new : CompLSFState}
    {S_prev : MGraph} {targetE D_reins : Finset ℕ} {e : ℕ}
    (h : Update.delete e ∈ buildUSOrd UC U cs_new S_prev targetE D_reins) :
    e ∈ S_prev.E := by
  unfold buildUSOrd at h
  simp only [List.mem_append] at h
  rcases h with (hdel | hsp) | hins
  · rw [List.mem_map] at hdel
    obtain ⟨x, hx, hxeq⟩ := hdel
    cases hxeq
    exact (Finset.mem_sdiff.mp ((Finset.mem_sort (· ≤ ·)).mp hx)).1
  · exact absurd hsp mem_restrictSplits_ne_delete
  · rw [List.mem_map] at hins
    obtain ⟨_, _, hxeq⟩ := hins
    cases hxeq

/-- Every edge listed in `progReemb lsfInit C_lsst depth impl st U ord' b` on a reached state
`SparseCoreOrdInput` belongs either to the old graph `G.E` or to the old sparsified core
`(T.S st b).E`. -/
theorem progReemb_mem_G_or_S {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}
    {k M N : ℕ} {st : SparseCoreBundleState depth} {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hk : 0 < k)
    (hinp : SparseCoreOrdInput (sparseCoreProgTool lsfInit C_lsst depth impl) k M N st G ord n)
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    (U : List Update) (ord' : ℕ → List End) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    ∀ e ∈ progReemb lsfInit C_lsst depth impl st U ord' j,
      e ∈ G.E ∨ e ∈ (T.S st j).E := by
  classical
  intro T e he
  by_cases hne : st.isNonempty = true
  · rw [progReemb_of_nonempty st hne, mem_stepBundleTree_reembList] at he
    set tr := st.trees j
    set sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut :=
      fun _ => canonicalSparsify impl
    set Tm := sparseCoreBundleRestartToolMachWith lsfInit C_lsst depth sparsify
      (canonicalSparsifyParams impl) (dsAmortConst impl)
    set Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst depth sparsify
    obtain ⟨τ, D, ordSeq, restarts, hG₀, _, _, hℓ₀, hD, hOrd, hGτ, _, _, _, hrun⟩ :=
      sparseCoreOrdInput_exists_run Tm hinp
    have hNM := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst depth
      sparsify (canonicalSparsifyParams impl) (dsAmortConst impl) k M N D ordSeq restarts τ).2.2
    rw [hrun] at hNM
    have hV₀ : (D.G 0).V.Nonempty := by
      have h1 := (runOrdAfterRestarts_isNonempty lsfInit C_lsst depth sparsify
        k M N D ordSeq restarts τ).2.1
      rw [← hNM.isNonempty, hne] at h1
      exact of_decide_eq_true h1.symm
    have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst depth sparsify
      k M N τ hk D ordSeq restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit τ le_rfl
    set pre := (Tb.runOrdAfterUpdate k M N D ordSeq restarts τ).1.trees j
    set post := (Tb.runOrdAfterRestarts k M N D ordSeq restarts τ).trees j
    have hbf : BundleBaseFieldsEq post pre :=
      (foldl_bundleRestart_props lsfInit C_lsst depth sparsify
        (Tb.runOrdAfterUpdate k M N D ordSeq restarts τ).1 (restarts τ)).2.2.2.2.1 j
    have hEq : BundleNonMachEq tr post := hNM.trees j
    have hI_τ : CompLSFInv C_lsst (D.ℓ 0) post.cs := hbf.cs ▸ hBun.2.2.2.2.2.2.2.1
    have hG₀_eq : post.cs.G₀ = D.G 0 := by
      rw [hbf.cs, hBun.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
    have htrG₀_eq : tr.cs.G₀ = D.G 0 := by rw [hEq.cs]; exact hG₀_eq
    have hpostG : post.cs.G = G := by
      rw [hbf.cs, hBun.2.2.2.2.2.2.2.2.1, hGτ]
    have hBunSubG : ∀ C ∈ components (D.G 0), ∀ b : ℤ, (tr.bun (C, b)).edges ⊆ G.E := by
      intro C hC0 b f hf
      have hReady := ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC0).2 b).2.1
      rw [← hpostG]
      exact hI_τ.hCE_sub C (hG₀_eq.symm ▸ hC0) (hReady.2.2 (hEq.bun ▸ hf))
    have hActSub : tr.activeComps ⊆ components (D.G 0) := by
      rw [hEq.activeComps, hbf.activeComps]
      exact hBun.2.2.2.2.2.2.2.2.2.1.2
    unfold stepBundleTree_reembSet at he
    simp only [Finset.mem_union] at he
    rcases he with (hLazy | hDyn) | hDelS
    · left
      rw [Finset.mem_biUnion] at hLazy
      obtain ⟨C, hC, hLazyB⟩ := hLazy
      rw [Finset.mem_biUnion] at hLazyB
      obtain ⟨b, _, heB⟩ := hLazyB
      have hC0 : C ∈ components (D.G 0) :=
        htrG₀_eq ▸ Finset.filter_subset _ _ (Finset.mem_sdiff.mp hC).1
      exact hBunSubG C hC0 b heB
    · left
      rw [Finset.mem_biUnion] at hDyn
      obtain ⟨C, hC, hDynB⟩ := hDyn
      rw [Finset.mem_biUnion] at hDynB
      obtain ⟨b, _, heD⟩ := hDynB
      have hC0 : C ∈ components (D.G 0) := by
        change C ∈ tr.activeComps ∪ (touchedCompsBatch tr.cs U \ tr.activeComps) at hC
        rcases Finset.mem_union.mp hC with h1 | h2
        · exact hActSub h1
        · exact htrG₀_eq ▸ Finset.filter_subset _ _ (Finset.mem_sdiff.mp h2).1
      have heUpd := DynSpanner.updateReembSet_subset_G (tr.dyn (C, b)) _ _ heD
      rw [update_G_eq] at heUpd
      have heDyn : e ∈ (tr.dyn (C, b)).G.E :=
        applyBatch_E_subset_of_delOrSplit bundleCompStep_isDelOrSplit heUpd
      have hGE : GraphEq (post.dyn (C, b)).G (post.bun (C, b)).graph :=
        ((hBun.2.2.2.2.2.2.2.2.2.2.2 C hC0).2 b).2.2.2.2.2.2
      have heBun : e ∈ (tr.bun (C, b)).edges := by
        rw [hEq.bun]
        exact show e ∈ (post.bun (C, b)).graph.E from hGE.2.1 ▸ (hEq.dyn ▸ heDyn)
      exact hBunSubG C hC0 b heBun
    · right
      rw [List.mem_toFinset, List.mem_filterMap] at hDelS
      obtain ⟨u, hu, hsome⟩ := hDelS
      cases u with
      | insert _ _ _ => simp at hsome
      | split _ _ _ _ => simp at hsome
      | delete e' =>
        simp only [Option.some.injEq] at hsome
        subst hsome
        have heS : e' ∈ tr.S_cur.E := mem_buildUSOrd_delete hu
        rw [progTool_S_of_nonempty st hne j]
        exact heS
  · have hf : st.isNonempty = false := Bool.eq_false_iff.mpr hne
    have hEmpty : progReemb lsfInit C_lsst depth impl st U ord' j = [] := by
      change (if st.isNonempty then _ else []) = []
      simp [hf]
    rw [hEmpty] at he; cases he

/-- Every edge in `progReemb lsfInit C_lsst depth impl st U ord' j` lies below `eCap` whenever all
edges of `G.E` and `(T.S st j).E` lie below `eCap`. -/
theorem progReemb_lt_eCap {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}
    {k M N eCap : ℕ} {st : SparseCoreBundleState depth} {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hk : 0 < k)
    (hinp : SparseCoreOrdInput (sparseCoreProgTool lsfInit C_lsst depth impl) k M N st G ord n)
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    (U : List Update) (ord' : ℕ → List End)
    (hGCap : ∀ e ∈ G.E, e < eCap)
    (hSCap : ∀ e ∈ ((sparseCoreProgTool lsfInit C_lsst depth impl).S st j).E, e < eCap) :
    ∀ e ∈ progReemb lsfInit C_lsst depth impl st U ord' j, e < eCap := fun e he => by
  rcases progReemb_mem_G_or_S hk hinp hInit U ord' e he with h1 | h2
  · exact hGCap e h1
  · exact hSCap e h2

end MinCostFlow.MinRatio

end
