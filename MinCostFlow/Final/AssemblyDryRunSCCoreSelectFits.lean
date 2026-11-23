module

public import MinCostFlow.Final.AssemblyDryRunSCCoreSelectAcct
public import MinCostFlow.MinRatio.WireSelectTouchedWstr
public import MinCostFlow.MinRatio.WireReembFacts
public import MinCostFlow.MinRatio.WireReembPot
public import MinCostFlow.MinRatio.SelectUpdateModel
import MinCostFlow.SparseCore.Program.OutEditsStep
import MinCostFlow.Chain.Ordered.UpdateStepsBase
import Mathlib.Tactic

/-!
# Post-core link facts (`hLinkFacts`) for select-aware `Update` (`AssemblyDryRunSCCoreSelectFits`)

Discharges all 21 conjuncts of the `hLinkFacts` callback in `ordChainUpdateCoreSelBody_runs`
(`MinRatio/WireUpdateSelect.lean`) from `UpdateCoreLevelLink`, `UpdateCoreSelectOutAt`,
`ShiftLoopChainInv` before and after `Update`, `FreshInv`, `RefreshBatch`, `SelectPotInv`, and
`SelectPhiBoundedAt`:

1. `update_ℓ_eq_of_not_rebuilt0`: surviving level-`0` length agreement when level `0` is not rebuilt.
2. `progTool_nonRebuilt_orderedBatch`: proves `OrderedBatch (oldCh.G j) (levelU j) (oldCh.levelOrd j)
   (newCh.levelOrd j)` for every non-rebuilt level `j < min firstReb cfg.P.d` by induction on `j`.
3. `dryCoreSel_hLinkFacts`: proves all 21 conjuncts of `hLinkFacts` at `uWordsMul = 10`,
   `uWordsFix = cfg.P.d`, `c = 1`, `pot = progReembPot`, and `reembFn = progReemb`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Surviving level-`0` length agreement (`update_ℓ_eq_of_not_rebuilt0`) -/

private lemma updateLoop_ℓ_of_not_rebuilt0_aux (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) (stOrig : ChainState T P) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ),
      idx + rem = P.d → st.rebuildCount = stOrig.rebuildCount →
      firstRebuiltLevel P.d stOrig.rebuildCount
        (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1.rebuildCount ≠ some 0 →
      (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1.ℓ = ℓ' := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU curEncAcc hsum _ _
    have hidx : idx = P.d := by omega
    subst hidx; unfold Ordered.updateLoop; split_ifs <;> rfl
  | succ rem' ih =>
    intro idx st curG curU curEncAcc hsum hReb hNo0
    have hidxLt : idx < P.d := by omega
    unfold Ordered.updateLoop at hNo0 ⊢
    by_cases hOver : intRebuildThreshold P N₀ idx < st.updCount idx + curU.length
    · simp only [hOver, ↓reduceIte] at hNo0 ⊢
      set stLG : ChainState T P :=
        { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
      have hfirst : firstRebuiltLevel P.d stOrig.rebuildCount
          (Ordered.algorithm1_rebuild T L P stLG idx (rebuildStartGraph idx curG) curEncAcc).1.rebuildCount =
          some idx := by
        rw [← hReb]; simp only [Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
        simpa [stLG] using Chain.firstRebuiltLevel_eq_of_inc hidxLt stLG.rebuildCount
      have hidxNe0 : idx ≠ 0 := fun h0 => hNo0 (h0 ▸ hfirst)
      simp only [Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte, stLG, rebuildStartFn, hidxNe0, ↓reduceIte]
    · simp only [hOver, ↓reduceIte] at hNo0 ⊢
      exact ih (idx + 1) _ _ _ 0 (by omega) hReb hNo0

/-- Twin of `update_g_eq_of_not_rebuilt0` for edge lengths `ℓ`. -/
theorem update_ℓ_eq_of_not_rebuilt0 {cfg : Alg2Config} {model : Alg2State cfg}
    {U : List Update} {gVec lVec : ℕ → ℝ}
    (hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh)
    (hRef : RefreshBatch model.extG U)
    (hℓOld : ∀ e ∈ (model.chain.G 0).E, model.chain.ℓ e = model.extℓ (model.intToExt e))
    (hagree : ∀ e ∈ model.extG.E, (∀ u ∈ U, ¬ u.Inserts e) → lVec e = model.extℓ e)
    (hNoReb0 :
      let modelPre := alg2PreResetState cfg model U gVec lVec
      firstRebuiltLevel cfg.P.d model.chain.rebuildCount modelPre.chain.rebuildCount ≠ some 0) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    ∀ e ∈ (modelPre.chain.G 0).E, e ∈ (model.chain.G 0).E →
      modelPre.chain.ℓ e = model.chain.ℓ e := by
  intro modelPre e heNew heOld
  set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  have hTr := translateBatch_preserves U model.extG (model.chain.G 0)
    model.extToInt model.intToExt model.nextFresh hFresh hRef.1
  dsimp only at hTr
  have hExtEq : tr.1 = model.extG := hTr.1.trans hRef.2.1
  have hG0 : modelPre.chain.G 0 = (model.chain.G 0).applyBatch tr.2.2.2.2 := by
    rcases algorithm1_update_G0_and_g cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain tr.2.2.2.2
        (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e')) with
      ⟨h0, _, _⟩ | ⟨_, hG0', _⟩
    · exact absurd h0 hNoReb0
    · exact hG0'
  have hℓEq : modelPre.chain.ℓ = fun e' => lVec (tr.2.2.1 e') :=
    updateLoop_ℓ_of_not_rebuilt0_aux cfg.T cfg.L cfg.TP cfg.P cfg.N₀
      (fun e' => lVec (tr.2.2.1 e')) (fun e' => gVec (tr.2.2.1 e')) model.chain
      cfg.P.d 0 _ ((model.chain.G 0).applyBatch tr.2.2.2.2) tr.2.2.2.2
      ((model.chain.G 0).batchEnc tr.2.2.2.2) (Nat.zero_add _) rfl hNoReb0
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
  rw [hℓEq]; dsimp only
  rw [hI2E, hagree (model.intToExt e) hExtMem hNoInsExt, hℓOld e heOld]

/-! ## 2. Inductive `OrderedBatch` along non-rebuilt levels (`progTool_nonRebuilt_orderedBatch`) -/

private lemma applyBatch_V_eq_of_isEdge_fits :
    ∀ {U : List Update} {G : MGraph}, (∀ u ∈ U, IsEdgeUpdate u) → (G.applyBatch U).V = G.V
  | [], _, _ => rfl
  | u :: rest, G, hE => by
    have h1 : (G.applyUpdate u).V = G.V := by
      have hu := hE u List.mem_cons_self
      cases u <;> simp [IsEdgeUpdate, MGraph.applyUpdate] at hu ⊢
    exact (applyBatch_V_eq_of_isEdge_fits (U := rest) (G := G.applyUpdate u)
      (fun x hx => hE x (List.mem_cons_of_mem _ hx))).trans h1

/-- Every non-rebuilt level `j < min firstReb P.d` in `UpdateCoreLevelLink` satisfies
`OrderedBatch (oldCh.G j) (levelU j) (oldCh.levelOrd j) (newCh.levelOrd j)`. -/
theorem progTool_nonRebuilt_orderedBatch {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ} {G₀ G₀' : MGraph} {ℓ ℓ' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {oldCh newCh : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    {firstReb : ℕ} {levelU levelUS : ℕ → List Update}
    (hInv0 : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ oldCh)
    (hInv1 : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ newCh)
    (hH0 : oldCh.toTreeChain.Holds G₀ ℓ σ σ_mwu γ_ℓ γ_c)
    (hH1 : newCh.toTreeChain.Holds G₀' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hInit : ∀ b < P.k, IsValidLSFInitFor lsfInit C_lsst P.k b)
    (hNR : NonRebuiltBatches (sparseCoreProgTool lsfInit C_lsst depth impl) oldCh newCh levelU (firstReb - 1))
    (hStepAll : ∀ j < min firstReb P.d,
      levelU (j + 1) = levelUS j ∧
      ∃ ℓj gj ordj,
        newCh.scState j = ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd
          (oldCh.scState j) (levelU j) ℓj gj ordj).1 ∧
        levelUS j = ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd
          (oldCh.scState j) (levelU j) ℓj gj ordj).2 (oldCh.bran j))
    (hV0Eq : (newCh.G 0).V = (oldCh.G 0).V) :
    ∀ j < min firstReb P.d,
      OrderedBatch (oldCh.G j) (levelU j) (oldCh.levelOrd j) (newCh.levelOrd j) := by
  let T := sparseCoreProgTool lsfInit C_lsst depth impl
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨hG0Eq, hB0⟩ := hNR.2.2.1 0 (Nat.zero_le _)
    have hEdge0 : ∀ u ∈ levelU 0, IsEdgeUpdate u :=
      isEdgeUpdate_of_applyBatch_V_eq hB0 ((congrArg MGraph.V hG0Eq.symm).trans hV0Eq)
    refine ⟨sortedRotation (oldCh.G 0), sortedRotation ((oldCh.G 0).applyBatch (levelU 0)), ?_, ?_, ?_⟩
    · simp [sortedRotation, ChainState.levelOrd, Ordered.chainLevelOrd]
    · simp [sortedRotation, ChainState.levelOrd, Ordered.chainLevelOrd, hG0Eq]
    · exact RotationBatch.mono (sortedRotation_batch hB0 hEdge0) (Nat.zero_le 2)
  | succ k ih =>
    intro hk1
    have hk : k < min firstReb P.d := Nat.lt_of_succ_lt hk1
    have hkd : k < P.d := lt_of_lt_of_le hk (Nat.min_le_right _ _)
    have hkLe : k ≤ firstReb - 1 := by omega
    have hk1Le : k + 1 ≤ firstReb - 1 := by omega
    have hOrdK := ih hk
    obtain ⟨hUk1Eq, ℓk, gk, ordk, hsc', hUS⟩ := hStepAll k hk
    have hbrEq : newCh.bran k = oldCh.bran k := (hNR.2.2.2.1 k hkLe hkd).1
    obtain ⟨hGk'Eq, hBk⟩ := hNR.2.2.1 k hkLe
    obtain ⟨hGk1'Eq, _⟩ := hNR.2.2.1 (k + 1) hk1Le
    have hGk1Old : oldCh.G (k + 1) = T.S (oldCh.scState k) (oldCh.bran k) := hInv0.hGSucc k hkd
    have hGk1New : newCh.G (k + 1) = T.S (newCh.scState k) (oldCh.bran k) := by
      rw [← hbrEq]; exact hInv1.hGSucc k hkd
    by_cases hne : (oldCh.scState k).isNonempty = true
    · have hup := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) (oldCh.scState k) hne (levelU k) ℓk gk ordk
      have hne' : (newCh.scState k).isNonempty = true := by
        rw [hsc']; change (T.updateOrd _ _ _ _ _).1.isNonempty = true; rw [hup]; exact hne
      have hOrd0 : (oldCh.scState k).ord = oldCh.levelOrd k :=
        (asm_input_inv _ _ _ _ _ _
          (levelHistory_sparseCoreOrdInput (Classical.choice (hInv0.hHist k hkd)))).2.1 hne
      have hOrd1 : (newCh.scState k).ord = newCh.levelOrd k :=
        (asm_input_inv _ _ _ _ _ _
          (levelHistory_sparseCoreOrdInput (Classical.choice (hInv1.hHist k hkd)))).2.1 hne'
      have hOrdkEq : ordk = newCh.levelOrd k := by
        rw [← hOrd1, hsc']; change _ = (T.updateOrd _ _ _ _ _).1.ord; rw [hup]
      let tr := (oldCh.scState k).trees (oldCh.bran k)
      obtain ⟨ℓ₀, hI, hcsG, hS_V⟩ := progTool_chainInv_level_compLSFInv hInv0 hInit hkd hne
      have hS_eq : oldCh.G (k + 1) = tr.S_cur := by
        rw [hGk1Old]; exact progTool_S_of_nonempty (oldCh.scState k) hne (oldCh.bran k)
      have hS'_eq : newCh.G (k + 1) =
          (stepBundleTree (fun _ => canonicalSparsify impl) tr (levelU k)
            (oldCh.levelOrd k) (newCh.levelOrd k)).state.S_cur := by
        rw [hGk1New, progTool_S_of_nonempty _ hne', hsc']
        change ((T.updateOrd (oldCh.scState k) (levelU k) ℓk gk ordk).1.trees (oldCh.bran k)).S_cur = _
        rw [hup, hOrd0, hOrdkEq]
      have hUS_eq : levelU (k + 1) =
          (stepBundleTree (fun _ => canonicalSparsify impl) tr (levelU k)
            (oldCh.levelOrd k) (newCh.levelOrd k)).U_S := by
        rw [hUk1Eq, hUS]
        change (T.updateOrd (oldCh.scState k) (levelU k) ℓk gk ordk).2 (oldCh.bran k) = _
        rw [hup, hOrd0, hOrdkEq]
      have hS_val : tr.S_cur.IsValid := by
        rw [← hS_eq]; exact oldCh.toTreeChain.G_isValid hH0 (k + 1) hkd
      have hL_eq : tr.cs.lsf = oldCh.toTreeChain.activeLSF k := by
        simp only [TreeChain.activeLSF, ChainState.toTreeChain, hkd, ↓reduceIte]
        change tr.cs.lsf = if (oldCh.scState k).isNonempty then tr.cs.lsf else emptyLSF
        simp [hne]
      have hSp := ((hH0.2.2.2.2.1 k hkd).2.1 (oldCh.bran k) (hInv0.hBran k hkd)).2
      have hS_sub : (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph tr.S_cur := by
        rw [← hS_eq, hcsG, hL_eq]
        simpa [TreeChain.activeLSF, ChainState.toTreeChain, hkd, hGk1Old] using hSp.1
      have hL'_eq : (compLSFBatch tr.cs (levelU k)).lsf = newCh.toTreeChain.activeLSF k := by
        simp only [TreeChain.activeLSF, ChainState.toTreeChain, hkd, ↓reduceIte, hbrEq]
        change (compLSFBatch tr.cs (levelU k)).lsf =
          if (newCh.scState k).isNonempty then ((newCh.scState k).trees (oldCh.bran k)).cs.lsf else emptyLSF
        rw [ite_eq_left hne', hsc']
        change _ = ((T.updateOrd (oldCh.scState k) (levelU k) ℓk gk ordk).1.trees (oldCh.bran k)).cs.lsf
        rw [hup]; rfl
      have hcsG' : (compLSFBatch tr.cs (levelU k)).G = newCh.G k := by
        rw [compLSFBatch_G, hcsG, hGk'Eq]
      have hS_sub' : (coreGraph (compLSFBatch tr.cs (levelU k)).G
          (compLSFBatch tr.cs (levelU k)).lsf).IsSubgraph
          (stepBundleTree (fun _ => canonicalSparsify impl) tr (levelU k)
            (oldCh.levelOrd k) (newCh.levelOrd k)).state.S_cur := by
        have hbr' : newCh.bran k < newCh.toTreeChain.k := (hH1.2.2.2.2.1 k hkd).1
        have hSp' := ((hH1.2.2.2.2.1 k hkd).2.1 (newCh.bran k) hbr').2.1
        rw [← hS'_eq, hcsG', hL'_eq]
        simpa [TreeChain.activeLSF, ChainState.toTreeChain, hkd, hbrEq, hGk1New] using hSp'
      have hReady : OutStepReady (fun _ => canonicalSparsify impl) tr (levelU k)
          (oldCh.levelOrd k) (newCh.levelOrd k) :=
        ⟨C_lsst, ℓ₀, hI, hcsG.symm ▸ hBk, hcsG.symm ▸ hOrdK, hS_val, hS_V, hS_sub, hS_sub'⟩
      obtain ⟨ρS, σS, hρS, hσS, hRotS, _⟩ :=
        outStep_rotations (fun _ => canonicalSparsify impl) tr (levelU k)
          (oldCh.levelOrd k) (newCh.levelOrd k) hReady
      have hRotOld : oldCh.levelOrd (k + 1) = tr.outOrder (oldCh.levelOrd k) := by
        conv_lhs => unfold ChainState.levelOrd Ordered.chainLevelOrd
        rw [ite_eq_right (Nat.succ_ne_zero k), Nat.add_sub_cancel]
        change (if (oldCh.scState k).isNonempty then
          ((oldCh.scState k).trees (oldCh.bran k)).outOrder (oldCh.scState k).ord else fun _ => []) = _
        rw [ite_eq_left hne, hOrd0]
      have hRotNew : newCh.levelOrd (k + 1) =
          (stepBundleTree (fun _ => canonicalSparsify impl) tr (levelU k)
            (oldCh.levelOrd k) (newCh.levelOrd k)).state.outOrder (newCh.levelOrd k) := by
        conv_lhs => unfold ChainState.levelOrd Ordered.chainLevelOrd
        rw [ite_eq_right (Nat.succ_ne_zero k), Nat.add_sub_cancel, hbrEq]
        change (if (newCh.scState k).isNonempty then
          ((newCh.scState k).trees (oldCh.bran k)).outOrder (newCh.scState k).ord else fun _ => []) = _
        rw [ite_eq_left hne', hOrd1, hsc']
        change (((T.updateOrd (oldCh.scState k) (levelU k) ℓk gk ordk).1).trees (oldCh.bran k)).outOrder _ = _
        rw [hup, hOrd0, hOrdkEq]
      have hEqApp : (stepBundleTree (fun _ => canonicalSparsify impl) tr (levelU k)
          (oldCh.levelOrd k) (newCh.levelOrd k)).state.S_cur =
          (oldCh.G (k + 1)).applyBatch (levelU (k + 1)) := by
        rw [← hS'_eq, hGk1'Eq]
      refine ⟨hS_eq.symm ▸ ρS, hEqApp ▸ σS, ?_, ?_, ?_⟩
      · rw [oupd_rotation_cast_order, hρS, hRotOld]
      · rw [oupd_rotation_cast_order, hσS, hRotNew]
      · exact oupd_rotationBatch_cast hS_eq.symm hEqApp hUS_eq.symm
          (h₁ := by rw [← hS'_eq, hGk1'Eq, hS_eq, hUS_eq]) (h₂ := rfl)
          (oupd_rotation_cast_order _ _).symm (oupd_rotation_cast_order _ _).symm
          (by simpa using hRotS)
    · have hf : (oldCh.scState k).isNonempty = false := Bool.eq_false_iff.mpr hne
      have hup := asm_updateOrd_of_empty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) (oldCh.scState k) hf (levelU k) ℓk gk ordk
      have hne' : (newCh.scState k).isNonempty = false := by
        rw [hsc']; change (T.updateOrd _ _ _ _ _).1.isNonempty = false; rw [hup]; exact hf
      have hUempty : levelU (k + 1) = [] := by
        rw [hUk1Eq, hUS]
        change (T.updateOrd (oldCh.scState k) (levelU k) ℓk gk ordk).2 (oldCh.bran k) = []
        rw [hup]
      have hGOldE : oldCh.G (k + 1) = emptyGraph := by
        rw [hGk1Old]; change (if (oldCh.scState k).isNonempty then _ else emptyGraph) = _; simp [hf]
      have hOrdOldE : oldCh.levelOrd (k + 1) = fun _ => [] := by
        conv_lhs => unfold ChainState.levelOrd Ordered.chainLevelOrd
        rw [ite_eq_right (Nat.succ_ne_zero k), Nat.add_sub_cancel]
        change (if (oldCh.scState k).isNonempty then _ else fun _ => []) = _; simp [hf]
      have hOrdNewE : newCh.levelOrd (k + 1) = fun _ => [] := by
        conv_lhs => unfold ChainState.levelOrd Ordered.chainLevelOrd
        rw [ite_eq_right (Nat.succ_ne_zero k), Nat.add_sub_cancel]
        change (if (newCh.scState k).isNonempty then _ else fun _ => []) = _; simp [hne']
      rw [hUempty, hGOldE, hOrdOldE, hOrdNewE]
      refine ⟨sortedRotation emptyGraph, sortedRotation (emptyGraph.applyBatch []), ?_, ?_, ?_⟩
      · funext v; simp [sortedRotation, sortedEnds, emptyGraph]
      · funext v; simp [sortedRotation, sortedEnds, emptyGraph, MGraph.applyBatch]
      · exact RotationBatch.mono (sortedRotation_batch trivial (fun _ h => by cases h)) (Nat.zero_le 2)

/-! ## 3. Full `hLinkFacts` discharge (`dryCoreSel_hLinkFacts`) -/

private lemma mem_coreBatchTouchedEdges_exists {e : ℕ} :
    ∀ {U : List Update}, e ∈ coreBatchTouchedEdges U → ∃ u ∈ U, u.Inserts e ∨ u = .delete e
  | [], h => by cases h
  | .insert e₀ a b :: rest, h => by
    simp only [coreBatchTouchedEdges, List.mem_cons] at h
    rcases h with rfl | hr
    · exact ⟨.insert e a b, List.mem_cons_self, Or.inl rfl⟩
    · obtain ⟨u, hu, h1⟩ := mem_coreBatchTouchedEdges_exists hr
      exact ⟨u, List.mem_cons_of_mem _ hu, h1⟩
  | .delete e₀ :: rest, h => by
    simp only [coreBatchTouchedEdges, List.mem_cons] at h
    rcases h with rfl | hr
    · exact ⟨.delete e, List.mem_cons_self, Or.inr rfl⟩
    · obtain ⟨u, hu, h1⟩ := mem_coreBatchTouchedEdges_exists hr
      exact ⟨u, List.mem_cons_of_mem _ hu, h1⟩
  | .split _ _ _ _ :: rest, h => by
    simp only [coreBatchTouchedEdges] at h
    obtain ⟨u, hu, h1⟩ := mem_coreBatchTouchedEdges_exists h
    exact ⟨u, List.mem_cons_of_mem _ hu, h1⟩

private lemma mem_coreBatchTouchedEdges_buildUSOrd_lt {eCap : ℕ} {UC U : List Update}
    {cs_new : CompLSFState} {S_prev : MGraph} {targetE D_reins : Finset ℕ}
    (hOld : ∀ e ∈ S_prev.E, e < eCap)
    (hNew : ∀ e ∈ (S_prev.applyBatch (buildUSOrd UC U cs_new S_prev targetE D_reins)).E, e < eCap) :
    ∀ e ∈ coreBatchTouchedEdges (buildUSOrd UC U cs_new S_prev targetE D_reins), e < eCap := by
  intro e he
  obtain ⟨u, hu, huE⟩ := mem_coreBatchTouchedEdges_exists he
  dsimp only [buildUSOrd] at hu
  simp only [List.mem_append] at hu
  rcases hu with (hdel | hsp) | hins
  · rw [List.mem_map] at hdel
    obtain ⟨x, hx, rfl⟩ := hdel
    have hxEq : x = e := huE.elim (fun h => by simp [Update.Inserts] at h) (fun h => by cases h; rfl)
    subst hxEq
    exact hOld x (Finset.mem_sdiff.mp ((Finset.mem_sort (· ≤ ·)).mp hx)).1
  · exfalso
    have hNoEdge : ∀ {keep : Finset ℕ} {UL : List Update}, ∀ v ∈ restrictSplits keep UL,
        ¬ v.Inserts e ∧ v ≠ .delete e := by
      intro keep UL; induction UL with
      | nil => intro _ h; cases h
      | cons w rest ih =>
        intro v hv; cases w with
        | insert _ _ _ => exact ih v hv
        | delete _ => exact ih v hv
        | split _ _ _ _ =>
          simp only [restrictSplits, List.mem_cons] at hv
          rcases hv with rfl | hv'
          · exact ⟨by simp [Update.Inserts], fun h => by cases h⟩
          · exact ih v hv'
    exact huE.elim (hNoEdge u hsp).1 (hNoEdge u hsp).2
  · rw [List.mem_map] at hins
    obtain ⟨x, hx, rfl⟩ := hins
    have hxEq : x = e := huE.elim id (fun h => by cases h)
    subst hxEq
    have hxTgt := (Finset.mem_sdiff.mp ((Finset.mem_sort (· ≤ ·)).mp hx)).1
    exact hNew x ((buildUSOrd_applyBatch_E_eq UC U cs_new S_prev targetE D_reins).symm ▸ hxTgt)

private lemma mem_coreBatchTouchedEdges_US_lt_eCap {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {eCap : ℕ} {st : SparseCoreBundleState depth}
    {U : List Update} {ℓ g : ℕ → ℝ} {ord' : ℕ → List End} {b : ℕ}
    (hSCapOld : ∀ e ∈ ((sparseCoreProgTool lsfInit C_lsst depth impl).S st b).E, e < eCap)
    (hSCapNew : ∀ e ∈ ((sparseCoreProgTool lsfInit C_lsst depth impl).S
      ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1 b).E, e < eCap) :
    ∀ e ∈ coreBatchTouchedEdges
      (((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').2 b), e < eCap := by
  let T := sparseCoreProgTool lsfInit C_lsst depth impl
  intro e he
  by_cases hne : st.isNonempty = true
  · have hup := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) st hne U ℓ g ord'
    have hne' : (T.updateOrd st U ℓ g ord').1.isNonempty = true := by rw [hup]; exact hne
    have hSOld : (T.S st b).E = (st.trees b).S_cur.E := progTool_S_of_nonempty st hne b ▸ rfl
    have hSNew : (T.S (T.updateOrd st U ℓ g ord').1 b).E =
        (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees b) U st.ord ord').state.S_cur.E := by
      rw [progTool_S_of_nonempty _ hne' b, hup]
    have hUS : (T.updateOrd st U ℓ g ord').2 b =
        (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees b) U st.ord ord').U_S := by rw [hup]
    rw [hUS] at he
    exact mem_coreBatchTouchedEdges_buildUSOrd_lt
      (fun x hx => hSCapOld x (hSOld ▸ hx))
      (fun x hx => hSCapNew x (hSNew ▸ hx)) e he
  · have hf : st.isNonempty = false := Bool.eq_false_iff.mpr hne
    have hup := asm_updateOrd_of_empty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) st hf U ℓ g ord'
    have hUS : (T.updateOrd st U ℓ g ord').2 b = [] := by rw [hup]
    rw [hUS] at he; cases he

set_option maxHeartbeats 800000 in
/-- Discharges all 21 conjuncts of `hLinkFacts` in `ordChainUpdateCoreSelBody_runs`
(`MinRatio/WireUpdateSelect.lean`) at `uWordsMul = 10`, `uWordsFix = fun _ => cfg.P.d`, `c = 1`,
`pot`, and `reembFn` matching `progReembPot` and `progReemb`. -/
theorem dryCoreSel_hLinkFacts
    {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}
    {cfg : Alg2Config} {w P L capExp vCap eCap heap midHeap firstReb E m : ℕ}
    {pot : cfg.T.State → ℕ} {reembFn : ToolReembFn cfg.T}
    {foot : ℕ → Prop} {memCore : ℕ → ℕ}
    {model : Alg2State cfg} {U : List Update} {gVec lVec : ℕ → ℝ} {φ0 : ℕ → ℕ → ℝ}
    {levelU levelUS : ℕ → List Update} {diffLists : ℕ → LevelDiffLists}
    (hT : cfg.T = sparseCoreProgTool lsfInit C_lsst depth impl)
    (hPotEq : pot = hT ▸ (progReembPot : (sparseCoreProgTool lsfInit C_lsst depth impl).State → ℕ))
    (hReembFnEq : reembFn = hT ▸ progReemb lsfInit C_lsst depth impl)
    (hV : cfg.ValidOrdNoHidden)
    (hdepth : 1 ≤ depth) (hγt : ∀ M, impl.γ_t M = 1)
    (hInit : ∀ b < cfg.P.k, IsValidLSFInitFor lsfInit C_lsst cfg.P.k b)
    (hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh)
    (hRef : RefreshBatch model.extG U)
    (hV0 : (model.chain.G 0).V.Nonempty)
    (hgOld : ∀ e ∈ (model.chain.G 0).E, model.chain.g e = model.extg (model.intToExt e))
    (hℓOld : ∀ e ∈ (model.chain.G 0).E, model.chain.ℓ e = model.extℓ (model.intToExt e))
    (hAgree : ∀ e ∈ model.extG.E, (∀ u ∈ U, ¬ u.Inserts e) →
      gVec e = model.extg e ∧ lVec e = model.extℓ e)
    (hShift0 : ShiftLoopChainInv cfg model.chain)
    (hShift1 : ShiftLoopChainInv cfg (alg2PreResetState cfg model U gVec lVec).chain)
    (hPot0 : SelectPotInv model.chain.toTreeChain model.chain.g φ0)
    (hPhiBd0 : ∀ j ≤ cfg.P.d, SelectPhiBoundedAt model.chain.toTreeChain φ0 (2 * m + 2) ((2 : ℝ) ^ E) j)
    (hOldCap : ∀ j ≤ cfg.P.d, ∀ e ∈ (model.chain.G j).E, e < eCap)
    (hNewCap : ∀ j ≤ cfg.P.d, ∀ e ∈ ((alg2PreResetState cfg model U gVec lVec).chain.G j).E, e < eCap)
    (hLink : UpdateCoreLevelLink model.chain (alg2PreResetState cfg model U gVec lVec).chain
      firstReb levelU levelUS)
    (hOut : UpdateCoreSelectOutAt w P L capExp vCap eCap reembFn
      foot memCore heap midHeap firstReb model.chain
      (alg2PreResetState cfg model U gVec lVec).chain levelU levelUS diffLists) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let PhiBd := fun φ j =>
      SelectPhiBoundedAt modelPre.chain.toTreeChain φ (2 * m + 2) ((2 : ℝ) ^ E) j
    ∃ ins : ℕ → ℕ → Prop,
      (firstReb = 0 → (modelPre.chain.G 0).E = Finset.range (modelPre.chain.G 0).m) ∧
      (0 < firstReb → ∀ e ∈ (modelPre.chain.G 0).E, e ∈ (model.chain.G 0).E →
        modelPre.chain.g e = model.chain.g e) ∧
      (0 < firstReb → ∀ e ∈ (modelPre.chain.G 0).E, e ∈ (model.chain.G 0).E →
        modelPre.chain.ℓ e = model.chain.ℓ e) ∧
      (∀ j < min firstReb cfg.P.d,
        let C := model.chain.toTreeChain
        let C' := modelPre.chain.toTreeChain
        (∀ e ∈ (C'.activeLSF j).F.F.E, Update.delete e ∉ levelU j) ∧
        (C'.activeLSF j).F.F.E ⊆ (C.activeLSF j).F.F.E ∧
        (∀ e ∈ (diffLists j).uS, e < eCap) ∧
        (∀ e ∈ (diffLists j).reemb, e < eCap) ∧
        (∀ e ∈ (C'.G j).E, e ∉ (diffLists j).uG →
          e ∈ (C.G j).E ∧ C'.chainLen modelPre.chain.ℓ (j + 1) e = C.chainLen model.chain.ℓ (j + 1) e) ∧
        (∀ e ∈ (C'.activeCore j).E,
          e ∉ (diffLists j).uG → e ∉ (diffLists j).fDel → e ∉ (diffLists j).uS →
          e ∉ (diffLists j).reemb →
          e ∈ (C.activeCore j).E ∧ C'.activeEmb j e = C.activeEmb j e) ∧
        SparseCoreOrdInput cfg.T cfg.P.k (modelPre.chain.lvlM j) modelPre.chain.N₀
          (modelPre.chain.scState j) (modelPre.chain.G j) (modelPre.chain.levelOrd j)
          (modelPre.chain.updCount j) ∧
        modelPre.chain.bran j < cfg.P.k ∧
        LevelDiffCovers C C' j ins (diffLists j)) ∧
      (∀ j, j < firstReb → j ≤ cfg.P.d →
        ∀ f ∈ (modelPre.chain.G j).E, f ∈ (model.chain.G j).E → ¬ ins j f →
          (modelPre.chain.toTreeChain.activeLSF j).wstr f =
            (model.chain.toTreeChain.activeLSF j).wstr f) ∧
      (∀ j, j + 1 < firstReb → j < cfg.P.d →
        ∀ f ∈ (modelPre.chain.G (j + 1)).E, f ∈ (model.chain.G (j + 1)).E →
          ins j f → ins (j + 1) f) ∧
      (let φS := fun j => if j < min firstReb cfg.P.d then splitPot (φ0 j) (batchSplits (levelU j)) else φ0 j
       0 < firstReb → EndPotAgree model.chain.toTreeChain modelPre.chain.toTreeChain φ0 φS (firstReb - 1)) ∧
      (let φS := fun j => if j < min firstReb cfg.P.d then splitPot (φ0 j) (batchSplits (levelU j)) else φ0 j
       ∀ j < firstReb, j ≤ cfg.P.d → SelectPotInvAt modelPre.chain.toTreeChain modelPre.chain.g φS j) ∧
      (let φS := fun j => if j < min firstReb cfg.P.d then splitPot (φ0 j) (batchSplits (levelU j)) else φ0 j
       ∀ j < firstReb, j ≤ cfg.P.d → PhiBd φS j) ∧
      (firstReb = cfg.P.d + 1 →
        modelPre.chain.G cfg.P.d = model.chain.G cfg.P.d ∧
        modelPre.chain.toTreeChain.activeLSF cfg.P.d = model.chain.toTreeChain.activeLSF cfg.P.d ∧
        (∀ e ∈ (modelPre.chain.G cfg.P.d).E,
          modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (cfg.P.d + 1) e =
            model.chain.toTreeChain.chainLen model.chain.ℓ (cfg.P.d + 1) e) ∧
        (∀ f ∈ (modelPre.chain.G cfg.P.d).E, ¬ ins cfg.P.d f)) ∧
      (∀ j < min firstReb cfg.P.d, (diffLists j).uG.length ≤ (levelU j).length) ∧
      (∀ j < min firstReb cfg.P.d,
        ReembCostBound (diffLists j).reemb
          (cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j)) 1
          (pot (model.chain.scState j)) (pot (modelPre.chain.scState j))) ∧
      ((Finset.range (min firstReb cfg.P.d)).sum (fun j => memCore (heap + 1 + 12 * j + 11)) ≤
        10 * (modelPre.chain.totalRuntime - model.chain.totalRuntime) + cfg.P.d) ∧
      ((Finset.range (min firstReb cfg.P.d)).sum (fun j => (levelU j).length) ≤
        2 * (modelPre.chain.totalRuntime - model.chain.totalRuntime)) ∧
      ((Finset.range (min firstReb cfg.P.d)).sum (fun j => (diffLists j).uS.length) ≤
        2 * (modelPre.chain.totalRuntime - model.chain.totalRuntime)) ∧
      ((Finset.range (min firstReb cfg.P.d)).sum (fun j => (diffLists j).fDel.length) ≤
        modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates) ∧
      ((Finset.range (min firstReb cfg.P.d)).sum
          (fun j => cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j)) +
        (Finset.Ico firstReb cfg.P.d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) ≤
        modelPre.chain.totalRuntime - model.chain.totalRuntime) ∧
      (firstReb < cfg.P.d →
        (Finset.Ico firstReb cfg.P.d).sum (fun j => (modelPre.chain.G j).m) ≤
          modelPre.chain.totalRuntime - model.chain.totalRuntime ∧
        (modelPre.chain.G cfg.P.d).m ≤ modelPre.chain.totalRuntime - model.chain.totalRuntime) ∧
      (firstReb < cfg.P.d →
        (model.chain.G firstReb).m ≤ 2 * (modelPre.chain.totalRuntime - model.chain.totalRuntime)) ∧
      (firstReb = 0 →
        (modelPre.chain.G 0).m ≤ modelPre.chain.totalRuntime - model.chain.totalRuntime) := by
  subst hReembFnEq
  have hAcct := dryCoreSel_update_accounting hT hV hFresh hRef hV0 hShift0 hShift1 hLink hOut
  rcases cfg with ⟨T, Ltool, TP, LP, Pch, σ_mwu, N₀, α, Ψ, ε⟩
  dsimp only at hT hPotEq hV hInit hFresh hRef hV0 hgOld hℓOld hAgree hShift0 hShift1 hPot0 hPhiBd0 hOldCap hNewCap hLink hOut hAcct ⊢
  subst hT; subst hPotEq
  let cfg : Alg2Config := ⟨sparseCoreProgTool lsfInit C_lsst depth impl, Ltool, TP, LP, Pch, σ_mwu, N₀, α, Ψ, ε⟩
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let modelPre := alg2PreResetState cfg model U gVec lVec
  let ins : ℕ → ℕ → Prop := fun j e => ∃ u ∈ levelU j, u.Inserts e
  have hH0 := (hShift0.1.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb hV.hγM₀ hV.hγk).1
  have hH1 := (hShift1.1.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb hV.hγM₀ hV.hγk).1
  have hNoReb0 : 0 < firstReb → firstRebuiltLevel Pch.d model.chain.rebuildCount modelPre.chain.rebuildCount ≠ some 0 := by
    intro hPos h0
    by_cases hfr : firstReb < Pch.d
    · have h1 := hLink.2.1 (by dsimp only [cfg]; exact hfr); rw [h1] at h0; exact absurd (Option.some.inj h0) (by omega)
    · have h1 := hLink.2.2.1 (by dsimp only [cfg]; omega); rw [h1] at h0; cases h0
  have hBranchA : firstReb = 0 → (modelPre.chain.G 0).E = Finset.range (modelPre.chain.G 0).m := by
    intro h0
    have hfirst0 : firstRebuiltLevel Pch.d model.chain.rebuildCount modelPre.chain.rebuildCount = some 0 := by
      rw [← h0]; exact hLink.2.1 (by rw [h0]; exact Pch.hd)
    rcases algorithm1_update_G0_and_g cfg.T Ltool TP Pch N₀ model.chain tr.2.2.2.2
        (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e')) with ⟨_, hG0', _⟩ | ⟨hNe0, _, _⟩
    · have hG0'' : modelPre.chain.G 0 = ((model.chain.G 0).applyBatch tr.2.2.2.2).compact := hG0'
      rw [hG0'']; simp [MGraph.compact, MGraph.m]
    · exact absurd hfirst0 hNe0
  have hgSurv : 0 < firstReb → ∀ e ∈ (modelPre.chain.G 0).E, e ∈ (model.chain.G 0).E → modelPre.chain.g e = model.chain.g e :=
    fun hPos => update_g_eq_of_not_rebuilt0 hFresh hRef hgOld (fun e he hno => (hAgree e he hno).1) (hNoReb0 hPos)
  have hℓSurv : 0 < firstReb → ∀ e ∈ (modelPre.chain.G 0).E, e ∈ (model.chain.G 0).E → modelPre.chain.ℓ e = model.chain.ℓ e :=
    fun hPos => update_ℓ_eq_of_not_rebuilt0 hFresh hRef hℓOld (fun e he hno => (hAgree e he hno).2) (hNoReb0 hPos)
  have hV0Eq : 0 < firstReb → (modelPre.chain.G 0).V = (model.chain.G 0).V := by
    intro hPos
    rcases algorithm1_update_G0_and_g cfg.T Ltool TP Pch N₀ model.chain tr.2.2.2.2
        (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e')) with ⟨h0, _, _⟩ | ⟨_, hG0', _⟩
    · exact absurd h0 (hNoReb0 hPos)
    · have hG0'' : modelPre.chain.G 0 = (model.chain.G 0).applyBatch tr.2.2.2.2 := hG0'
      rw [hG0'']
      exact applyBatch_V_eq_of_isEdge_fits (translateBatch_isEdgeUpdate _ _ _ _ _ fun u hu => by
        have hns := hRef.2.2 u hu
        cases u with | insert _ _ _ => trivial | delete _ => trivial | split _ _ _ _ => exact absurd hns id)
  have hOrdB : ∀ j < min firstReb Pch.d,
      OrderedBatch (model.chain.G j) (levelU j) (model.chain.levelOrd j) (modelPre.chain.levelOrd j) :=
    fun j hj => progTool_nonRebuilt_orderedBatch hShift0.1 hShift1.1 hH0 hH1 hInit
      (hLink.2.2.2.1 (by omega)) hLink.2.2.2.2.1 (hV0Eq (by omega)) j hj
  let φS : ℕ → ℕ → ℝ := fun j => if j < min firstReb Pch.d then splitPot (φ0 j) (batchSplits (levelU j)) else φ0 j
  have hPhiSMatch : 0 < firstReb → ∀ j ≤ firstReb - 1, φS j = splitPot (φ0 j) (batchSplits (levelU j)) := by
    intro hPos j hj; dsimp only [φS]
    by_cases hlt : j < min firstReb Pch.d
    · rw [ite_eq_left hlt]
    · rw [ite_eq_right hlt]
      have hFRLe : firstReb ≤ Pch.d + 1 := hLink.1
      have hjd : j = Pch.d := by omega
      rw [hjd, ((hLink.2.2.2.1 hPos).2.2.2.2 (by dsimp only [cfg]; omega)).1]; rfl
  refine ⟨ins, hBranchA, hgSurv, hℓSurv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hAcct.1, hAcct.2.1, hAcct.2.2.1, hAcct.2.2.2.1, hAcct.2.2.2.2.1,
    hAcct.2.2.2.2.2.1, hAcct.2.2.2.2.2.2.1, hAcct.2.2.2.2.2.2.2⟩
  · -- Per-level non-rebuilt facts (`j < min firstReb Pch.d`)
    intro j hj
    have hPos : 0 < firstReb := by omega
    have hjLe : j ≤ firstReb - 1 := by omega
    have hjd : j < Pch.d := lt_of_lt_of_le hj (Nat.min_le_right _ _)
    have hNR := hLink.2.2.2.1 hPos
    have hS := hOut.2.2 j hj
    obtain ⟨_, ℓj, gj, ordj, hsc', hUS⟩ := hLink.2.2.2.2.1 j hj
    have hbrEq : modelPre.chain.bran j = model.chain.bran j := (hNR.2.2.2.1 j hjLe hjd).1
    have hIn0 : SparseCoreOrdInput cfg.T Pch.k (levelM TP Pch j) N₀
        (model.chain.scState j) (model.chain.G j) (model.chain.levelOrd j)
        (model.chain.updCount j) := levelHistory_sparseCoreOrdInput (Classical.choice (hShift0.1.hHist j hjd))
    have hIn1 : SparseCoreOrdInput cfg.T Pch.k (modelPre.chain.lvlM j) modelPre.chain.N₀
        (modelPre.chain.scState j) (modelPre.chain.G j) (modelPre.chain.levelOrd j)
        (modelPre.chain.updCount j) := by
      rw [congrFun hShift1.1.hLvlM j, hShift1.1.hN0]
      exact levelHistory_sparseCoreOrdInput (Classical.choice (hShift1.1.hHist j hjd))
    have huGEq : (diffLists j).uG = batchTouchedEdges (levelU j) :=
      hS.2.1.trans (coreBatchTouchedEdges_eq_batchTouchedEdges _)
    have huSEq : (diffLists j).uS = batchTouchedEdges (levelUS j) :=
      hS.2.2.2.2.1.trans (coreBatchTouchedEdges_eq_batchTouchedEdges _)
    have hOrdjEq : (model.chain.scState j).isNonempty = true → ordj = modelPre.chain.levelOrd j := by
      intro hne
      have hup := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) (model.chain.scState j) hne (levelU j) ℓj gj ordj
      have hne' : (modelPre.chain.scState j).isNonempty = true := by
        rw [hsc']; change (cfg.T.updateOrd _ _ _ _ _).1.isNonempty = true; rw [hup]; exact hne
      have hOrd1 := (asm_input_inv _ _ _ _ _ _ hIn1).2.1 hne'
      rw [← hOrd1, hsc']; change _ = (cfg.T.updateOrd _ _ _ _ _).1.ord; rw [hup]
    have hTouched := progTool_nonRebuilt_touched_covers hShift0.1 hInit hNR j hjLe
    have hReembEq : (diffLists j).reemb =
        progReemb lsfInit C_lsst depth impl (model.chain.scState j) (levelU j)
          (modelPre.chain.levelOrd j) (model.chain.bran j) := hS.2.2.2.2.2.1
    have hSeq : modelPre.chain.toTreeChain.activeS j =
        (model.chain.toTreeChain.activeS j).applyBatch (levelUS j) := by
      simp only [TreeChain.activeS, ChainState.toTreeChain, cfg, hjd, ↓reduceIte, hbrEq, hUS]
      rw [hsc']
      exact progTool_S_updateOrd (model.chain.scState j) (levelU j) ℓj gj ordj (model.chain.bran j)
    have hUS_cov : ∀ e, (e ∈ (modelPre.chain.toTreeChain.activeS j).E ↔
        e ∉ (model.chain.toTreeChain.activeS j).E) → e ∈ (diffLists j).uS := fun e hxor => by
      rw [huSEq]; exact mem_batchTouchedEdges_of_symmDiff (hSeq ▸ hxor)
    have hLDC : LevelDiffCovers model.chain.toTreeChain modelPre.chain.toTreeChain j ins (diffLists j) := by
      have huG_cov : ∀ e, ((e ∈ (modelPre.chain.toTreeChain.G j).E ↔ e ∉ (model.chain.toTreeChain.G j).E) ∨
          ins j e) → e ∈ (diffLists j).uG := fun e h => by
        rw [huGEq]; exact h.elim (hTouched.2.2.1 e) (fun ⟨u, hu, hI⟩ => hTouched.2.1 e ⟨u, hu, Or.inl hI⟩)
      have hfDel_cov : ∀ e, e ∈ (model.chain.toTreeChain.activeLSF j).F.F.E →
          e ∉ (modelPre.chain.toTreeChain.activeLSF j).F.F.E → e ∈ (diffLists j).fDel := by
        intro e heO heN
        rw [← List.mem_toFinset, hS.2.2.2.1]
        exact Finset.mem_sdiff.mpr ⟨by simpa [TreeChain.activeLSF, ChainState.toTreeChain, cfg, hjd] using heO,
          by simpa [TreeChain.activeLSF, ChainState.toTreeChain, cfg, hjd] using heN⟩
      have hfIns_cov : ∀ e, e ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.E →
          e ∉ (model.chain.toTreeChain.activeLSF j).F.F.E → e ∈ (diffLists j).uG := fun e h1 h2 => by
        rw [huGEq]; exact hTouched.2.2.2.2.1 e h1 h2
      by_cases hne : (model.chain.scState j).isNonempty = true
      · have hOrdEq := hOrdjEq hne
        have hReemb : ReembCovers model.chain.toTreeChain modelPre.chain.toTreeChain j (diffLists j).reemb := by
          rw [hReembEq, ← hOrdEq]
          exact reembCovers_of_progTool_of_input hjd hjd hbrEq (Nat.lt_of_lt_of_le Nat.zero_lt_one Pch.hk)
            hdepth (model.chain.scState j) hIn0 hne (levelU j) ℓj gj ordj (hNR.2.2.1 j hjLe).2
            (hOrdEq ▸ hOrdB j hj) (hInit (model.chain.bran j) (hShift0.1.hBran j hjd))
            (hNR.2.2.1 j hjLe).1 (by dsimp only [ChainState.toTreeChain, cfg]; rw [hsc'])
            (by dsimp only [ChainState.toTreeChain, cfg]; rw [hsc']) rfl
            (by dsimp only [ChainState.toTreeChain, cfg]; rw [hsc'])
        refine ⟨huG_cov, hfDel_cov, hfIns_cov, hUS_cov, hReemb, fun e heO heN ⟨x, hxEmb, hins⟩ => ?_⟩
        refine hReemb e heO heN ?_
        have hup := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
          (canonicalSparsifyParams impl) (dsAmortConst impl) (model.chain.scState j) hne (levelU j) ℓj gj ordj
        have hne' : (modelPre.chain.scState j).isNonempty = true := by
          rw [hsc']; change (cfg.T.updateOrd _ _ _ _ _).1.isNonempty = true; rw [hup]; exact hne
        have htree' : (modelPre.chain.scState j).trees (modelPre.chain.bran j) =
            (stepBundleTree (fun _ => canonicalSparsify impl)
              ((model.chain.scState j).trees (model.chain.bran j))
              (levelU j) (model.chain.scState j).ord ordj).state := by
          rw [hbrEq, hsc']; change ((cfg.T.updateOrd _ _ _ _ _).1.trees (model.chain.bran j)) = _; rw [hup]
        have heOff : e ∉ ((model.chain.scState j).trees (model.chain.bran j)).S_cur.E := by
          simpa [TreeChain.activeS, ChainState.toTreeChain, cfg, hjd, hne, sparseCoreProgTool,
            sparseCoreBundleRestartToolMachWith, sparseCoreBundleRestartToolWith,
            sparseCoreBundleToolWith] using (Finset.mem_sdiff.mp heO).2
        have heOff' : e ∉ (stepBundleTree (fun _ => canonicalSparsify impl)
            ((model.chain.scState j).trees (model.chain.bran j))
            (levelU j) (model.chain.scState j).ord ordj).state.S_cur.E := by
          rw [← htree']
          simpa [TreeChain.activeS, ChainState.toTreeChain, cfg, hjd, hne', sparseCoreProgTool,
            sparseCoreBundleRestartToolMachWith, sparseCoreBundleRestartToolWith,
            sparseCoreBundleToolWith] using (Finset.mem_sdiff.mp heN).2
        have hxTr : x ∈ ((model.chain.scState j).trees (model.chain.bran j)).emb e := by
          simpa [TreeChain.activeEmb, ChainState.toTreeChain, cfg, hjd, hne, sparseCoreProgTool,
            sparseCoreBundleRestartToolMachWith, sparseCoreBundleRestartToolWith,
            sparseCoreBundleToolWith] using hxEmb
        have hneEmb := progTool_emb_ne_of_inserts lsfInit C_lsst depth hdepth impl
          (Nat.lt_of_lt_of_le Nat.zero_lt_one Pch.hk) (model.chain.scState j) (model.chain.G j)
          (model.chain.levelOrd j) hIn0 hne (levelU j) ordj (hNR.2.2.1 j hjLe).2
          (hOrdEq ▸ hOrdB j hj) (hInit (model.chain.bran j) (hShift0.1.hBran j hjd))
          heOff heOff' hxTr hins
        simpa [TreeChain.activeEmb, ChainState.toTreeChain, cfg, hjd, hne, hne', htree',
          sparseCoreProgTool, sparseCoreBundleRestartToolMachWith,
          sparseCoreBundleRestartToolWith, sparseCoreBundleToolWith] using hneEmb
      · have hf : (model.chain.scState j).isNonempty = false := Bool.eq_false_iff.mpr hne
        have hup := asm_updateOrd_of_empty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
          (canonicalSparsifyParams impl) (dsAmortConst impl) (model.chain.scState j) hf (levelU j) ℓj gj ordj
        have hne' : (modelPre.chain.scState j).isNonempty = false := by
          rw [hsc']; change (cfg.T.updateOrd _ _ _ _ _).1.isNonempty = false; rw [hup]; exact hf
        refine ⟨huG_cov, hfDel_cov, hfIns_cov, hUS_cov, ?_, ?_⟩
        · intro e _ _ hEmbNe
          exfalso; apply hEmbNe
          simp only [TreeChain.activeEmb, ChainState.toTreeChain, cfg, hjd, ↓reduceIte]
          change (if (modelPre.chain.scState j).isNonempty then _ else fun _ => []) e =
            (if (model.chain.scState j).isNonempty then _ else fun _ => []) e
          simp [hne', hf]
        · intro e _ _ ⟨x, hxEmb, _⟩
          simp only [TreeChain.activeEmb, ChainState.toTreeChain, hjd, ↓reduceIte] at hxEmb
          change x ∈ (if (model.chain.scState j).isNonempty then _ else fun _ => []) e at hxEmb
          simp [hf] at hxEmb
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hIn1, hShift1.1.hBran j hjd, hLDC⟩
    · have h1 := progTool_nonRebuilt_newF_noDel hShift0.1 hInit hNR hjLe hjd
      intro e he; exact h1 e (by simpa [TreeChain.activeLSF, ChainState.toTreeChain, hjd] using he)
    · exact progTool_nonRebuilt_forest_subset hShift0.1 hInit hNR j hjLe
    · rw [hS.2.2.2.2.1, hUS]
      exact mem_coreBatchTouchedEdges_US_lt_eCap
        (fun e he => hOldCap (j + 1) (by omega) e (hShift0.1.hGSucc j hjd ▸ he))
        (fun e he => hNewCap (j + 1) (by omega) e (by
          rw [hShift1.1.hGSucc j hjd, hbrEq, hsc']; exact he))
    · rw [hReembEq]
      exact progReemb_lt_eCap (Nat.lt_of_lt_of_le Nat.zero_lt_one Pch.hk) hIn0
        (hInit (model.chain.bran j) (hShift0.1.hBran j hjd)) (levelU j) (modelPre.chain.levelOrd j)
        (hOldCap j hjd.le)
        (fun e he => hOldCap (j + 1) (by omega) e (hShift0.1.hGSucc j hjd ▸ he))
    · intro e heNew heNotUG
      have heOld : e ∈ (model.chain.G j).E := by
        by_contra hnot; exact heNotUG (hLDC.1 e (Or.inl ⟨fun _ => hnot, fun _ => heNew⟩))
      have hNoIns : ∀ u ∈ levelU j, ¬ u.Inserts e := fun u hu hI =>
        heNotUG (hLDC.1 e (Or.inr ⟨u, hu, hI⟩))
      exact ⟨heOld, (progTool_nonRebuilt_wstr_and_chainLen_of_not_inserts hShift0.1 hH0 hH1 hNR
        (hℓSurv hPos) j hjLe e heNew heOld hNoIns).2⟩
    · intro e heCore' heNotUG heNotFDel heNotUS heNotReemb
      have heCore'S : e ∈ (modelPre.chain.G j).E \ (modelPre.chain.toTreeChain.activeLSF j).F.F.E := by
        simpa [TreeChain.activeCore, coreGraph, ChainState.toTreeChain, hjd, cfg] using heCore'
      have heG' : e ∈ (modelPre.chain.G j).E := (Finset.mem_sdiff.mp heCore'S).1
      have heNotF' : e ∉ (modelPre.chain.toTreeChain.activeLSF j).F.F.E := (Finset.mem_sdiff.mp heCore'S).2
      have heG : e ∈ (model.chain.G j).E := by
        by_contra hnot; exact heNotUG (hLDC.1 e (Or.inl ⟨fun _ => hnot, fun _ => heG'⟩))
      have heNotF : e ∉ (model.chain.toTreeChain.activeLSF j).F.F.E := fun hF =>
        heNotFDel (hLDC.2.1 e hF heNotF')
      have heCore : e ∈ (model.chain.toTreeChain.activeCore j).E := by
        simpa [TreeChain.activeCore, coreGraph, ChainState.toTreeChain, hjd, cfg] using
          Finset.mem_sdiff.mpr ⟨heG, heNotF⟩
      refine ⟨heCore, ?_⟩
      by_cases heS' : e ∈ (modelPre.chain.toTreeChain.activeS j).E
      · have heS : e ∈ (model.chain.toTreeChain.activeS j).E := by
          by_contra hnot; exact heNotUS (hLDC.2.2.2.1 e ⟨fun _ => hnot, fun _ => heS'⟩)
        have hEmbOfS : ∀ (st : SparseCoreBundleState depth) (b : ℕ),
            e ∈ ((sparseCoreProgTool lsfInit C_lsst depth impl).S st b).E →
            (sparseCoreProgTool lsfInit C_lsst depth impl).emb st b e = [(e, true)] := by
          intro st b hmem
          by_cases hst : st.isNonempty = true
          · have hSmem : e ∈ (st.trees b).S_cur.E := by
              simpa [sparseCoreProgTool, sparseCoreBundleRestartToolMachWith,
                sparseCoreBundleRestartToolWith, sparseCoreBundleToolWith, hst] using hmem
            simp [sparseCoreProgTool, sparseCoreBundleRestartToolMachWith,
              sparseCoreBundleRestartToolWith, sparseCoreBundleToolWith, hst,
              BundleTreeState.emb, hSmem]
          · exfalso
            have hf : st.isNonempty = false := Bool.eq_false_iff.mpr hst
            simp [sparseCoreProgTool, sparseCoreBundleRestartToolMachWith,
              sparseCoreBundleRestartToolWith, sparseCoreBundleToolWith, hf, emptyGraph] at hmem
        have hemb0 : model.chain.toTreeChain.activeEmb j e = [(e, true)] := by
          simp only [TreeChain.activeEmb, ChainState.toTreeChain, hjd, ↓reduceIte]
          exact hEmbOfS _ _ (by simpa [TreeChain.activeS, ChainState.toTreeChain, hjd] using heS)
        have hemb1 : modelPre.chain.toTreeChain.activeEmb j e = [(e, true)] := by
          simp only [TreeChain.activeEmb, ChainState.toTreeChain, cfg, hjd, ↓reduceIte]
          exact hEmbOfS _ _ (by simpa [TreeChain.activeS, ChainState.toTreeChain, cfg, hjd] using heS')
        rw [hemb0, hemb1]
      · have heNotS : e ∉ (model.chain.toTreeChain.activeS j).E := fun hS0 =>
          heNotUS (hLDC.2.2.2.1 e ⟨fun h => absurd h heS', fun h => absurd hS0 h⟩)
        by_contra hEmbNe
        exact heNotReemb (hLDC.2.2.2.2.1 e
          (Finset.mem_sdiff.mpr ⟨by simpa [TreeChain.activeCore, TreeChain.activeLSF, ChainState.toTreeChain, hjd, cfg] using heCore, heNotS⟩)
          (Finset.mem_sdiff.mpr ⟨by simpa [TreeChain.activeCore, TreeChain.activeLSF, ChainState.toTreeChain, hjd, cfg] using heCore', heS'⟩)
          hEmbNe)
  · intro j hj _ f hf' hf hNoIns
    exact progTool_nonRebuilt_wstr_eq_of_not_inserts (hLink.2.2.2.1 (by omega)) j (by omega)
      f hf' hf (fun u hu hI => hNoIns ⟨u, hu, hI⟩)
  · intro j hj1 _ f hf' hf ⟨u, hu, hI⟩
    by_contra hNo
    exact progTool_nonRebuilt_not_inserts_of_top hShift0.1 hH0 hH1 (hLink.2.2.2.1 (by omega))
      (j + 1) (by omega) f hf' hf (fun v hv hIv => hNo ⟨v, hv, hIv⟩) j (Nat.le_succ j) u hu hI
  · intro hPos
    exact (progTool_nonRebuilt_endPotAgree hShift0.1 hH0 hH1 hInit (hLink.2.2.2.1 hPos)
      (hPhiSMatch hPos)).2.2.2
  · intro j hj _
    have hPos : 0 < firstReb := by omega
    exact (progTool_nonRebuilt_selectPotInv hShift0.1 hH0 hH1 hInit (hLink.2.2.2.1 hPos)
      (hPhiSMatch hPos) hPot0 (hgSurv hPos)).1 j (by omega)
  · intro j hj hjLe
    have hPos : 0 < firstReb := by omega
    have hNR := hLink.2.2.2.1 hPos
    exact selectPhiBoundedAt_of_splitPot (hPhiBd0 j hjLe) (hNR.2.2.1 j (by omega)).1
      (hNR.2.2.1 j (by omega)).2 (hPhiSMatch hPos j (by omega))
  · intro hEq
    have hPos : 0 < firstReb := by omega
    have hNR := hLink.2.2.2.1 hPos
    obtain ⟨hUdEmpty, hLastLSF, hLastBr⟩ := hNR.2.2.2.2 (by dsimp only [cfg]; omega)
    have hGdEq : modelPre.chain.G Pch.d = model.chain.G Pch.d := by
      have h1 := (hNR.2.2.1 Pch.d (by omega)).1; rw [hUdEmpty] at h1; exact h1
    refine ⟨hGdEq,
      by simp only [TreeChain.activeLSF, ChainState.toTreeChain, lt_irrefl, ↓reduceIte, hLastLSF, hLastBr],
      fun e he => (progTool_nonRebuilt_wstr_and_chainLen_of_not_inserts hShift0.1 hH0 hH1 hNR
        (hℓSurv hPos) Pch.d (by omega) e he (hGdEq ▸ he)
        (fun u hu => by rw [hUdEmpty] at hu; cases hu)).2,
      fun f _ ⟨u, hu, _⟩ => by rw [hUdEmpty] at hu; cases hu⟩
  · intro j hj
    rw [(hOut.2.2 j hj).2.1, coreBatchTouchedEdges_eq_batchTouchedEdges]
    exact batchTouchedEdges_length_le (levelU j)
  · intro j hj
    have hPos : 0 < firstReb := by omega
    have hjd : j < Pch.d := lt_of_lt_of_le hj (Nat.min_le_right _ _)
    obtain ⟨_, ℓj, gj, ordj, hsc', _⟩ := hLink.2.2.2.2.1 j hj
    have hReembEq : (diffLists j).reemb =
        progReemb lsfInit C_lsst depth impl (model.chain.scState j) (levelU j)
          (modelPre.chain.levelOrd j) (model.chain.bran j) := (hOut.2.2 j hj).2.2.2.2.2.1
    by_cases hne : (model.chain.scState j).isNonempty = true
    · have hIn0 := levelHistory_sparseCoreOrdInput (Classical.choice (hShift0.1.hHist j hjd))
      have hIn1 := levelHistory_sparseCoreOrdInput (Classical.choice (hShift1.1.hHist j hjd))
      have hup := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) (model.chain.scState j) hne (levelU j) ℓj gj ordj
      have hne' : (modelPre.chain.scState j).isNonempty = true := by
        rw [hsc']; change (cfg.T.updateOrd _ _ _ _ _).1.isNonempty = true; rw [hup]; exact hne
      have hOrd1 := (asm_input_inv _ _ _ _ _ _ hIn1).2.1 hne'
      have hOrdkEq : ordj = modelPre.chain.levelOrd j := by
        rw [← hOrd1, hsc']; change _ = (cfg.T.updateOrd _ _ _ _ _).1.ord; rw [hup]
      rw [hReembEq, ← hOrdkEq, hsc']
      exact reembCostBound_of_progTool (model.chain.scState j) hne (levelU j) ℓj gj ordj
        (progTool_chainInv_bran_lt_k hShift0.1 hjd).2
        (progTool_branchLazyCovers (Nat.lt_of_lt_of_le Nat.zero_lt_one Pch.hk) hIn0 hne
          (hInit _ (hShift0.1.hBran j hjd)) (levelU j) ordj)
        (hsc' ▸ progTool_branchCostLeMach (Nat.lt_of_lt_of_le Nat.zero_lt_one Pch.hk) hdepth
          (hγt _) hIn1 (hInit _ (hShift0.1.hBran j hjd)))
    · have hf : (model.chain.scState j).isNonempty = false := Bool.eq_false_iff.mpr hne
      have hup := asm_updateOrd_of_empty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) (model.chain.scState j) hf (levelU j) ℓj gj ordj
      have hne' : (modelPre.chain.scState j).isNonempty = false := by
        rw [hsc']; change (cfg.T.updateOrd _ _ _ _ _).1.isNonempty = false; rw [hup]; exact hf
      have hR0 : (diffLists j).reemb = [] := by
        rw [hReembEq]; change (if (model.chain.scState j).isNonempty then _ else []) = []; simp [hf]
      have hP0 : progReembPot (modelPre.chain.scState j) = 0 := by
        unfold progReembPot; simp [hne']
      change (diffLists j).reemb.length + progReembPot (modelPre.chain.scState j) ≤
        1 * (cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j) + 1) +
        progReembPot (model.chain.scState j)
      rw [hR0, hP0]; simp

end MinCostFlow.Final.DryRun

end
