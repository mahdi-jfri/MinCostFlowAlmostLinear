module

public import MinCostFlow.Final.AssemblyDryRunSCDeepSelectCode
public import MinCostFlow.Final.WireDeepSelectSizes
public import MinCostFlow.MinRatio.OrdSelSpecs
import MinCostFlow.Final.AssemblyDryRunSCDeepSelectFits
import MinCostFlow.Final.WireSelectDryFits
import MinCostFlow.Final.AssemblyDryRunSCConnected
import MinCostFlow.MinRatio.WireShiftDeepCostKFBL
import MinCostFlow.MinRatio.SelectRebuildNoRoom
import MinCostFlow.MinRatio.WireSelectEvalKeyBridge
import MinCostFlow.MinRatio.SelectPhiFill
import MinCostFlow.MinRatio.SelectMetaTableWrite
import MinCostFlow.MinRatio.SelectCoreLenFill
import MinCostFlow.MinRatio.SelectCoreList
import MinCostFlow.MinRatio.SelectEmbCopy
import MinCostFlow.MinRatio.SelectRegionSkeleton
import MinCostFlow.DynSpanner.Program.DynGraphRefill
import Mathlib.Tactic

/-!
# Proof of `ShiftDeepChainSyncSpecWExtKFBLSel` for `dryDeepSelectCode` (`AssemblyDryRunSCDeepSelectProof`)

Discharges the select-aware deep-shift contract `ShiftDeepChainSyncSpecWExtKFBLSel`
(`MinRatio/OrdSelSpecs.lean`) for `dryDeepSelectCode` (`Final/AssemblyDryRunSCDeepSelectCode.lean`)
inside `dryLinkedProgramSel` at `drySCRep`, `dryPot`, `DryChainLenGridInv`, and
`dryInnerSizesWithSelect` (with `shiftSel := mkDryShiftSelectSizes Psc termSel` for any
`termSel : DryTermSelectSizes` and `initSel : DryInitSelectSizes`, including the concrete
`dryShiftSelectSizes Psc` and `dryInitSelectSizes Psc`).
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

private lemma tool_restart_init_lower_cast {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂) {k : ℕ}
    (hR : ∀ {M N n b : ℕ} {st : T₂.State} {G' : MGraph} {ord : ℕ → List End},
      SparseCoreOrdInput T₂ k M N st G' ord n → b < k →
      G'.m * SparseCore.bundleLogFactor M N ≤ T₂.cost (T₂.restart st b) - T₂.cost st)
    (hI : ∀ {M N : ℕ} {G' : MGraph} {ℓ' g' : ℕ → ℝ} {ord : ℕ → List End},
      G'.IsValid →
      3 * G'.m * SparseCore.bundleLogFactor M N ≤ T₂.cost (T₂.initOrd k M N G' ℓ' g' ord)) :
    (∀ {M N n b : ℕ} {st : T₁.State} {G' : MGraph} {ord : ℕ → List End},
      SparseCoreOrdInput T₁ k M N st G' ord n → b < k →
      G'.m * SparseCore.bundleLogFactor M N ≤ T₁.cost (T₁.restart st b) - T₁.cost st) ∧
    (∀ {M N : ℕ} {G' : MGraph} {ℓ' g' : ℕ → ℝ} {ord : ℕ → List End},
      G'.IsValid →
      3 * G'.m * SparseCore.bundleLogFactor M N ≤ T₁.cost (T₁.initOrd k M N G' ℓ' g' ord)) := by
  subst h; exact ⟨hR, hI⟩

set_option maxHeartbeats 800000 in
/-- Opaque-program core of `dryDeepSelectCode_hDeepSel`: shares one `let` block for `I, V, k, F,
cfg, G` across all hypotheses and keeps `p`, `b`, `op`, `Rcore`, and the size bounds opaque so
`shiftDeepSelectBody_runs` unifies syntactically without unfolding `dryLinkedProgramSel`. -/
private theorem dryDeepSelectCode_hDeepSel_body
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap1 : ∀ e, 1 ≤ J.capacity e)
    {w : ℕ}
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤ w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    ∀ (limbMul : ℕ) (PscP : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ)
      (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
      (p : Program) (b : ℕ) (op : ℕ → ℕ)
      (deepSpaceInner deepSpace deepFixed treeMulInner treeMul toolMul K : ℕ),
      Rcore.Local →
      10 ≤ w → 16 < 2 ^ w →
      F.limbs < 2 ^ w →
      dryLastStretchP J ≤ 40 * F.rangeExponent →
      dryLastStretchP J < 2 ^ w →
      cfg.P.k < 2 ^ w →
      0 < initTargetCap cfg G →
      initTargetCap cfg G ≤ selectHeapCap cfg G I.m →
      p.procs[b]? = some (shiftDeepSelectBody (b + 1) (b + 7) (b + 10) (op 3) (b + 12) (b + 13)) →
      p.procs[b + 10]? = some (selectInitInteriorLoopBody (b + 10) (b + 11)) →
      p.procs[b + 11]? = some (selectFillInteriorLevelBody (op 2) (op 4) (b + 9)
        (b + 14) (b + 16) (b + 17)) →
      p.procs[b + 12]? = some (selectFillLastLevelBody (b + 9) (b + 14)) →
      p.procs[b + 13]? = some (selectRefreshFinalizeBody (b + 18) (b + 19)) →
      p.procs[b + 17]? = some (selEmbCopyBody (b + 47)) →
      p.procs[b + 18]? = some (selectPhiLoopBody (b + 18) (b + 73)) →
      p.procs[b + 19]? = some (selectRebuildSuffixBody (b + 19) (b + 20)) →
      p.procs[b + 20]? = some (selectRebuildLevelBody (b + 56) (b + 21)) →
      p.procs[b + 21]? = some (selectProcessListBody (b + 21) (b + 22)) →
      p.procs[b + 22]? = some (selectProcessEdgeBody (b + 74) (b + 53) (b + 55)) →
      p.HasAt (b + 35) (selectHeapOpsModule (b + 35) 4) →
      p.HasAt (b + 57) (selectPhiFillModule (b + 57) 4) →
      p.HasAt (b + 74) (evalKeyModule (b + 74) 4) →
      (∀ B metaBase lvlMeta,
        MeetsContract w p (b + 7) (selTableWriteContract w B metaBase lvlMeta (dryLastStretchP J))) →
      (∀ vcF ecF (Fold Fnew : MGraph),
        MeetsContract w p (b + 9) (dgCopyRefillContract w G.n (initTargetCap cfg G) vcF ecF Fold Fnew)) →
      (∀ eL : List ℕ,
        MeetsContract w p (b + 14) (selCoreLenFillContract w F.fmt.precision (initTargetCap cfg G) eL)) →
      (∀ eL : List ℕ, MeetsContract w p (b + 16) (selFilterAbsentContract w eL)) →
      (∀ j < cfg.P.d, ∀ G' : MGraph, G'.n ≤ G'.m + 1 → G'.m ≤ I.m →
        SparseCoreReadoutFootAt F.fmt F.limbs (dryDepth J) cfg.T G' cfg.P.k
          (levelM cfg.TP cfg.P j) cfg.N₀ G.n (initTargetCap cfg G)
          dryCapExp PscP allocation Rcore p op) →
      ShiftDeepChainSyncSpecWExtKFBL w F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
        (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
        (dryCapLimit dryWitnessUsed J) PscP.wordExp (dryLastStretchP J) (dryDeepIntCapMax J)
        (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G) cfg Rcore p (b + 1)
        deepSpaceInner
        (deepShiftFixedBound PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d (dryLastMult J))
        (deepShiftToolMulBound F.limbs dryCapExp PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d
          (dryLastMult J))
        treeMulInner →
      selectProcessEdgeCost (selectHeapCap cfg G I.m) F.limbs
        (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs) + 60 ≤ K →
      deepSpaceInner + shiftDeepSelectSpaceBound cfg.P.d G.n (initTargetCap cfg G)
        (selectHeapCap cfg G I.m) F.limbs dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀
        (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs) = deepSpace →
      deepShiftFixedBound PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d (dryLastMult J) +
        shiftDeepSelectFixedBound PscP.readout cfg.P.d F.limbs = deepFixed →
      deepShiftToolMulBound F.limbs dryCapExp PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d
        (dryLastMult J) +
        shiftDeepSelectToolMulBound cfg.P.d F.limbs dryCapExp (levelM cfg.TP cfg.P 0) cfg.N₀
          (drySlot I.m) K ≤ toolMul →
      treeMulInner ≤ treeMul →
      ShiftDeepChainSyncSpecWExtKFBLSel w F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
        (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
        (dryCapLimit dryWitnessUsed J) PscP.wordExp (dryLastStretchP J) (dryDeepIntCapMax J)
        (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G) 4 2 K F.rangeExponent
        (dryLastStretchP J) (drySlot I.m) cfg G (dryPot J) (DryChainLenGridInv J) Rcore p b
        deepSpace deepFixed toolMul treeMul := by
  intro I V k F cfg G limbMul PscP allocation Rcore p b op
    deepSpaceInner deepSpace deepFixed treeMulInner treeMul toolMul K
    hlocalCore hw10 hw16 hLkW hpLastLe hpLastW hkW heCapPos heCapLeHeap
    hEntryAt hIntLoopAt hFillIntAt hFillLastAt hFinAt hEmbCopyAt hPhiLoopAt hRebSufAt
    hRebLvlAt hProcListAt hProcEdgeAt hHeapMod hPhiMod hEvalMod
    hTableWrite hDgCopy hCoreLen hFilter hFootAtAll hDeepInner hK hSpaceEq hFixEq
    hToolMulLe hTreeMulLe
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1
  have hT : cfg.T = sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision)
      dryCLsstUsed (dryDepth J) sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool dryWitnessUsed sparsifyImplUsed rfl rfl rfl J hw
  obtain ⟨hRestartLower, hInitLower⟩ := tool_restart_init_lower_cast hT (k := cfg.P.k)
    (fun hIn hb => sparseCoreBundleRestartToolMachWith_restart_lower _ _ _ _ _ _ hIn hb)
    (fun hG => sparseCoreBundleRestartToolMachWith_init_lower _ _ _ _ _ _ cfg.P.hk hG)
  refine ⟨shiftDeepSelectBody (b + 1) (b + 7) (b + 10) (op 3) (b + 12) (b + 13), hEntryAt, ?_⟩
  intro root heap pos i ω mem0 mem model tok sg B_t R_t
  dsimp only
  intro hiLt hRep0 hMeta0 hCaps0 hLay0 _hSelInv0 hReembPot0 hRegInv0 hShift0 hGrid0 hMemEq hSched'
    hNum0 hOffInv0 hOffBd0 hCapFacts hBranLt hModelInv hModelK hIntCapLe hForestCap
    hLogW hCapT hFootBothLt hzHeap hRoom
  let Rrep := solverStateRep cfg F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
    (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) Rcore
  let model' := alg2LoopShiftStep cfg model i
  obtain ⟨⟨B, hBslot, hBlkInv0⟩, hPhiBd0, hg0⟩ := hRegInv0
  obtain ⟨hRegAt0, hOwnDisj0⟩ := SelectRegionAt.of_solverSelectBlocksInv hBlkInv0
  have hcapEq : sg.loc.cap = selectHeapCap cfg G I.m := hBlkInv0.2.2.2.2.1
  have hOwnEq : sg.owned = fun a => sg.loc.hb ≤ a ∧ a < B.endAddr := hBlkInv0.2.2.2.2.2.2.1
  have hBreg : SelectRegion sg.loc.hb sg.loc B sg.loc.metaPtr := hBlkInv0.2.2.2.2.2.1
  have hsbLtEnd : sg.loc.hb < B.endAddr := by
    obtain ⟨hlo1, hlo2, hlo3, hlo4⟩ := hBreg.bounds
    have h2 : sg.loc.hb < sg.loc.endAddr := by
      rw [sg.loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega
    omega
  have hEndHeap : B.endAddr ≤ heap := by
    have hlt := hFootBothLt (B.endAddr - 1) (Or.inr (by rw [hOwnEq]; omega))
    omega
  have hHeapW : heap < 2 ^ w := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hRoom
  have hSlotW : B.slot < 2 ^ w := by
    have hBe : B.eCap = initTargetCap cfg G := hBlkInv0.2.2.1
    have h1 : B.slot ≤ B.eCap * B.slot := Nat.le_mul_of_pos_left _ (by rw [hBe]; exact heCapPos)
    have h2 : B.eCap * B.slot ≤ B.levelSize := by unfold SelectBlocksLoc.levelSize; omega
    have h3 : B.levelSize ≤ (B.d + 1) * B.levelSize := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have h4 : B.endAddr = B.base + selectBlocksSize B.d B.vCap B.eCap B.Lk B.slot := B.endAddr_eq
    unfold selectBlocksSize at h4
    have h5 : (B.d + 1) * B.levelSize = (B.d + 1) *
        (dynGraphSize B.vCap B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot) := rfl
    omega
  -- Post-shift chain and grid invariants
  have hShift' : Ordered.ShiftLoopChainInv cfg model'.chain := hShift0.shift hVcfg i.val hiLt.le
  have hInv' := hShift'.1
  have hGrid' : DryChainLenGridInv J model'.chain :=
    dryChainLenGridInv_shift J hJn hJm hCap1 hShift0 hGrid0 hiLt.le
  have hTH' := hInv'.toTreeChain_holds_noHidden hVcfg.hσ_mwu_mono hVcfg.hTP hVcfg.hLP hVcfg.hMWU
    hVcfg.hEmb hVcfg.hγM₀ hVcfg.hγk
  have hLvlM : ∀ j, model'.chain.lvlM j = levelM cfg.TP cfg.P j := fun j => congrFun hInv'.hLvlM j
  have hN0 : model'.chain.N₀ = cfg.N₀ := hInv'.hN0
  obtain ⟨_, _, _, _, _, hModOld'⟩ := hBlkInv0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hModNewEx : ∃ σ' σ'_mwu γ'_ℓ γ'_c,
      SelectModelInv model' (model'.chain.G 0) σ' σ'_mwu γ'_ℓ γ'_c :=
    ⟨_, _, _, _, hTH'.1, hTH'.2.1, hInv'.hBran,
      fun j hj => by
        rw [hLvlM j, hN0]
        exact levelHistory_sparseCoreOrdInput (Classical.choice (hInv'.hHist j hj)),
      hModOld'.2.2.2.2.1, hModOld'.2.2.2.2.2⟩
  obtain ⟨σ', σ'_mwu, γ'_ℓ, γ'_c, hModNew⟩ := hModNewEx
  -- Prefix agreement for `G 0` and `g`
  have hPref := shiftDeep_prefix_agree model i hiLt
  have hG0Eq : model'.chain.G 0 = model.chain.G 0 := hPref.1 0 (Nat.zero_le _)
  have hgEq : ∀ e, model'.chain.g e = model.chain.g e := hPref.2.2.2.2.2.1
  have hg0' : ∀ e ∈ (model'.chain.G 0).E, |model'.chain.g e| ≤ (2 : ℝ) ^ F.rangeExponent := by
    intro e he; rw [hgEq e]; exact hg0 e (hG0Eq ▸ he)
  have hG0n' : (model'.chain.G 0).n ≤ 2 * I.m + 2 := hGrid'.2.1
  have hℓPos' : ∀ e ∈ (model'.chain.G 0).E, 0 < model'.chain.ℓ e := fun e he => by
    have hlt := (hGrid'.2.2.1 0 (Nat.zero_le _)).1 e he
    have h0 : model'.chain.toTreeChain.chainLen model'.chain.ℓ 0 e = model'.chain.ℓ e := rfl
    rw [h0] at hlt
    exact lt_of_lt_of_le (by positivity) hlt.1
  -- Vertex and edge capacity bounds for `model` and `model'`
  have hdPos : 0 < cfg.P.d := by omega
  have hOldEcap : (model.chain.G i.val).m ≤ initTargetCap cfg G :=
    (Finset.card_le_card fun e he => Finset.mem_range.mpr ((hCaps0 i.val hiLt).2.2.1 e he)).trans
      (by simp)
  have hNewVcap : ∀ j ≤ cfg.P.d, ∀ v ∈ (model'.chain.G j).V, v < G.n := by
    intro j hj v hv
    have hB' := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
      hVcfg.hTP hVcfg.hγM₀ hVcfg.hγk hInv' j hj
    exact (hCaps0 0 hdPos).2.1 v (hG0Eq ▸ hB'.2.1 hv)
  have hNewEcap : ∀ j ≤ cfg.P.d, ∀ e ∈ (model'.chain.G j).E, e < initTargetCap cfg G := by
    intro j hj e he
    have hSub := chainInv_G_E_subset_G0 hVcfg hInv' j hj
    exact (hCaps0 0 hdPos).2.2.1 e (hG0Eq ▸ hSub he)
  have hNewEcapHeap : ∀ j ≤ cfg.P.d, ∀ e ∈ (model'.chain.G j).E, e < sg.loc.cap := fun j hj e he =>
    lt_of_lt_of_le (hNewEcap j hj e he) (hcapEq ▸ heCapLeHeap)
  -- Per-level readout foot and embedding bounds on `model'`
  have hFootAt : ∀ j, i.val ≤ j → j < cfg.P.d →
      SparseCoreReadoutFootAt F.fmt F.limbs (dryDepth J) cfg.T (model'.chain.G j) cfg.P.k
        (model'.chain.lvlM j) model'.chain.N₀ G.n (initTargetCap cfg G) dryCapExp PscP
        allocation Rcore p op := by
    intro j _ hj
    have hGn : (model'.chain.G j).n ≤ (model'.chain.G j).m + 1 := hShift'.levels_n_le hVcfg j hj.le
    have hGm : (model'.chain.G j).m ≤ I.m :=
      (Finset.card_le_card (chainInv_G_E_subset_G0 hVcfg hInv' j hj.le)).trans hGrid'.1
    rw [hLvlM j, hN0]
    exact hFootAtAll j hj (model'.chain.G j) hGn hGm
  have hEmbBd : ∀ j < cfg.P.d, ∀ e ∈ (model'.chain.toTreeChain.activeCore j).E,
      (model'.chain.toTreeChain.activeEmb j e).length ≤ dryMaxEmbLen I.m := fun j hj e he =>
    (progTool_embLen_le_dryMaxEmbLen_of_shiftLoop J hJn hJm hCap1 hShift' j hj e he).1
  have hEmbSlot : ∀ j, i.val ≤ j → j < cfg.P.d →
      ∀ e ∈ (model'.chain.toTreeChain.activeCore j).E,
        (mWalkEncode (model'.chain.toTreeChain.activeEmb j e)).length ≤ B.slot := fun j _ hj e he => by
    rw [mWalkEncode_length, hBslot]; unfold drySlot
    have := hEmbBd j hj e he; omega
  -- State-dependent select helper contracts
  have hHeapC := selectHeapOpsModule_meetsContracts (w := w) (h := 4) (by decide) hw10 hHeapMod sg.loc
  have hEmbCopy : ∀ j, i.val ≤ j → j < cfg.P.d → ∀ eL : List ℕ,
      MeetsContract w p (b + 17)
        (selEmbCopyContract w eL (model'.chain.toTreeChain.activeEmb j)) :=
    fun _ _ _ _ => selEmbCopy_meetsContract hEmbCopyAt hHeapC.2.1
  have hPhiFill : ∀ (solverG : ℕ → ℕ) (φ : ℕ → ℕ → ℝ),
      MeetsContract w p (b + 73)
        (selectPhiFillContract w 4 F.fmt.precision
          (selectMlocOf B sg.loc.metaPtr solverG (dryLastStretchP J))
          model'.chain.toTreeChain (model'.chain.G 0) model'.chain.g model'.chain.ℓ
          σ' σ'_mwu γ'_ℓ γ'_c φ) :=
    fun _ _ => selectPhiFillModule_meetsContract (w := w) (h := 4) (by decide) hw10 hPhiMod
  have hCandFit : CandidateKeysFit 4 F.fmt.precision (dryLastStretchP J) F.limbs
      model'.chain.toTreeChain model'.chain.g model'.chain.ℓ :=
    dry_candidateKeysFit_of_shiftLoop J hJn hJm hCap1 hShift' hGrid' hpLastLe
      (M_g := (2 : ℝ) ^ F.rangeExponent) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (show F.rangeExponent ≤ 40 * F.rangeExponent by omega)) hg0'
  have hRebLvl : ∀ (solverG : ℕ → ℕ) (φ : ℕ → ℕ → ℝ),
      MeetsContract w p (b + 20)
        (selectRebuildLevelNoRoomContract w 4 F.fmt.precision sg.loc
          (selectMlocOf B sg.loc.metaPtr solverG (dryLastStretchP J))
          model'.chain.toTreeChain model'.chain.g model'.chain.ℓ φ
          (fun j => model'.chain.toTreeChain.chainLen model'.chain.ℓ (j + 1))
          (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs)
          (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs)) := by
    intro solverG φ
    have hMLk : (selectMlocOf B sg.loc.metaPtr solverG (dryLastStretchP J)).Lk = F.limbs :=
      hBlkInv0.2.2.2.1
    have hEdge : MeetsContract w p (b + 22)
        (selectProcessEdgeContract w 4 F.fmt.precision sg.loc
          (selectMlocOf B sg.loc.metaPtr solverG (dryLastStretchP J))
          model'.chain.toTreeChain model'.chain.g model'.chain.ℓ φ
          (fun j => model'.chain.toTreeChain.chainLen model'.chain.ℓ (j + 1))
          (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs)
          (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs)) := by
      have h1 := selectProcessEdge_meetsContract_evalKey
        (loc := sg.loc) (mloc := selectMlocOf B sg.loc.metaPtr solverG (dryLastStretchP J))
        (C := model'.chain.toTreeChain) (G := model'.chain.G 0) (g := model'.chain.g)
        (ℓ := model'.chain.ℓ) (φ := φ)
        (coreLen := fun j => model'.chain.toTreeChain.chainLen model'.chain.ℓ (j + 1))
        (maxEmbLen := dryMaxEmbLen I.m)
        hProcEdgeAt hEvalMod (by decide) hw10 hModNew.1 hModNew.2.1 hℓPos'
        (fun lvl hlvl e he => hEmbBd lvl hlvl e (Finset.mem_sdiff.mp he).1)
        (by rw [hMLk]; exact hCandFit)
        hHeapC.2.2.2.2.2.2.2.1 hHeapC.2.2.2.2.2.2.2.2.2.1
      rw [hMLk] at h1
      exact h1
    exact selectRebuildLevel_meetsContract_noRoom hRebLvlAt
      hHeapC.2.2.2.2.2.2.2.2.2.2
      (fun _ => selectProcessList_meetsContract_noRoom hProcListAt hEdge)
  -- `K` lower bound and `PhiBd` invariants
  have hK' : selectProcessEdgeCost sg.loc.cap F.limbs (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs) +
      60 ≤ K := hcapEq ▸ hK
  let PhiBd : (ℕ → ℕ → ℝ) → ℕ → Prop :=
    fun φ j => SelectPhiBoundedAt model'.chain.toTreeChain φ (2 * I.m + 2) ((2 : ℝ) ^ F.rangeExponent) j
  have hPhiBdPref : ∀ r < i.val, PhiBd sg.φ r := fun r hr v hv =>
    hPhiBd0 r (by omega) v ((hPref.1 r hr.le) ▸ hv)
  have hPhiBdStep : ∀ j ≤ cfg.P.d, ∀ (φ : ℕ → ℕ → ℝ) (φj : ℕ → ℝ),
      (∀ r < j, SelectPotInvAt model'.chain.toTreeChain model'.chain.g φ r) →
      (∀ r < j, PhiBd φ r) →
      (∀ v ∈ (model'.chain.toTreeChain.activeLSF j).F.F.V,
        ∃ r ∈ (model'.chain.toTreeChain.activeLSF j).F.F.V,
          (model'.chain.toTreeChain.activeLSF j).F.F.Connected v r ∧
          φj v = walkInner (potGrad model'.chain.toTreeChain model'.chain.g φ j)
            ((model'.chain.toTreeChain.activeLSF j).F.F.forestPath v r)) →
      ∀ r < j + 1, PhiBd (Function.update φ j φj) r := by
    intro j hj φ φj hPot hBd hFill r hr
    by_cases hrj : r = j
    · subst hrj
      exact selectPhiBoundedAt_of_phiFill (by positivity) hModNew.1 hj hG0n' hg0' hPot hBd hFill
    · exact selectPhiBoundedAt_update_ne φj hrj (hBd r (by omega))
  have hFitPhi : ∀ j ≤ cfg.P.d, ∀ φ' : ℕ → ℕ → ℝ,
      (∀ r < j, SelectPotInvAt model'.chain.toTreeChain model'.chain.g φ' r) →
      (∀ r < j, PhiBd φ' r) →
      (∀ e ∈ (model'.chain.toTreeChain.activeLSF j).F.F.E,
        PotGradEvalFits 4 F.limbs F.fmt.precision model'.chain.toTreeChain model'.chain.g φ' j e) ∧
      ForestWalkFits 4 F.limbs F.fmt.precision (model'.chain.toTreeChain.activeLSF j).F.F
        (potGrad model'.chain.toTreeChain model'.chain.g φ' j) :=
    fun j hj φ' _ hBd => dry_phiFillFits_of_shiftLoop J hJn hJm hCap1 hShift' hG0n' hj
      (M_g := (2 : ℝ) ^ F.rangeExponent) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (show F.rangeExponent ≤ 80 * F.rangeExponent by omega))
      hg0' hBd
  have hRoom' : heap + deepSpaceInner +
      shiftDeepSelectSpaceBound cfg.P.d G.n (initTargetCap cfg G) sg.loc.cap F.limbs dryCapExp
        (levelM cfg.TP cfg.P 0) cfg.N₀ (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs) < 2 ^ w := by
    rw [hcapEq, Nat.add_assoc, hSpaceEq]; exact hRoom
  -- Execute `shiftDeepSelectBody_runs`
  obtain ⟨nextHeap, cost, out, tok', sg', hrBody, hHeapLo, hHeapHi, hLevEq, hIntEq, hTabEq, hRecEq,
      _, _, hRep', hMeta', hCaps', hLay', hNum', hOffInv', hOffBd', _, hsgOwn', hsgPot', hRegAt',
      hSelInv', hPhiBd', hz', hFr', hFt', hOwnDisj', hCost'⟩ :=
    shiftDeepSelectBody_runs
      (w := w) (L := F.limbs) (P := F.fmt.precision) (m := I.m) (V := V)
      (psi := ⌈cfg.Ψ⌉₊) (k := k) (epsExp := k + Num.IPM.alphaExponent I.m V + 10)
      (drainUnit := detectOffTreeDrainUnit F.limbs) (capExp := dryCapExp) (limbMul := limbMul)
      (capLimit := dryCapLimit dryWitnessUsed J) (wordExp := PscP.wordExp)
      (stretchPrec := dryLastStretchP J) (intCapMax := dryDeepIntCapMax J)
      (forestEdgeCap := dryDeepForestEdgeCap J) (vCap := G.n) (eCap := initTargetCap cfg G)
      (pLast := dryLastStretchP J) (sb := sg.loc.hb) (metaBase := sg.loc.metaPtr)
      (depth := dryDepth J)
      (evalSpace := evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs)
      (evalCost := evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs)
      (K := K) (deepSpace := deepSpaceInner)
      (deepFixed := deepShiftFixedBound PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d (dryLastMult J))
      (deepToolMul := deepShiftToolMulBound F.limbs dryCapExp PscP (levelM cfg.TP cfg.P 0) cfg.N₀
        cfg.P.d (dryLastMult J))
      (treeMul := treeMulInner)
      (deepProc := b + 1) (tableWriteProc := b + 7) (intLoopProc := b + 10)
      (fillIntProc := b + 11) (fillLastProc := b + 12) (finalizeProc := b + 13)
      (phiLoopProc := b + 18) (phiFillProc := b + 73) (rebuildSuffixProc := b + 19)
      (rebuildLvlProc := b + 20) (dgCopyProc := b + 9) (coreLenProc := b + 14)
      (filterProc := b + 16) (embCopyProc := b + 17)
      (fmt := F.fmt) (cfg := cfg) (G := G) (initialGraph := fun j => model'.chain.G j)
      (Psc := PscP) (allocation := allocation) (Rcore := Rcore) (pot := dryPot J) (p := p) (op := op)
      (PhiBd := PhiBd)
      hlocalCore rfl rfl hw16 hw10 hLkW hpLastW hkW hSlotW heCapPos
      hVcfg.hTP hVcfg.hγk (drySC_toolCostMono J) (dryPot_facts J)
      hRestartLower hInitLower hK'
      hDeepInner (fun lvlMeta => hTableWrite B sg.loc.metaPtr lvlMeta)
      hIntLoopAt hFillIntAt hFillLastAt hFinAt hPhiLoopAt hRebSufAt
      hFootAt hDgCopy hCoreLen hFilter hEmbCopy hPhiFill hRebLvl
      hiLt hRep0 hMeta0 hCaps0 hMemEq hSched' hNum0 hOffInv0 hOffBd0 hCapFacts hBranLt
      hModelInv hModelK hIntCapLe hForestCap hLogW hCapT
      (fun a ha => hFootBothLt a (Or.inl ha)) hzHeap
      hRegAt0 hReembPot0 hOwnDisj0 hEndHeap hModNew
      hOldEcap hNewVcap hNewEcap hNewEcapHeap
      (fun j _ hj => dryDeepSel_hLenFitInt J hJn hJm hCap1 hInv' hGrid' j hj)
      hEmbSlot
      (dryDeepSel_hLenFitLast J hJn hJm hCap1 hShift0 hGrid0 hiLt)
      hPhiBdPref hPhiBdStep hFitPhi hRoom'
  have hBlkInv' : SolverSelectBlocksInv G F.limbs F.fmt.precision I.m G.n (initTargetCap cfg G)
      (dryLastStretchP J) B model' (Rrep.foot root tok') tok' sg' out.mem :=
    hRegAt'.to_solverSelectBlocksInv fun a h1 h2 =>
      hOwnDisj' a (by rw [hsgOwn', hOwnEq]; exact ⟨h1, h2⟩)
  have hRegInv' : SolverSelectRegionInv G F.limbs F.fmt.precision I.m F.rangeExponent
      (dryLastStretchP J) (drySlot I.m) G.n (initTargetCap cfg G)
      model' (Rrep.foot root tok') tok' sg' out.mem :=
    ⟨⟨B, hBslot, hBlkInv'⟩, hPhiBd', hg0'⟩
  refine ⟨nextHeap, cost, out, tok', sg', hrBody, hHeapLo, ?_, hLevEq, hIntEq, hTabEq, hRecEq,
    hRep', hMeta', hCaps', hLay' hLay0, hSelInv', hsgPot', hRegInv', hNum', hOffInv', hOffBd', hz',
    fun a ha hnot => hFr' a ha (fun hf => hnot (Or.inl hf)) (fun ho => hnot (Or.inr ho)),
    fun a ha => ?_, ?_⟩
  · rw [hcapEq, Nat.add_assoc, hSpaceEq] at hHeapHi; exact hHeapHi
  · rcases ha with hf' | ho'
    · rcases hFt' a hf' with hf | hnew
      · exact Or.inl (Or.inl hf)
      · exact Or.inr hnew
    · exact Or.inl (Or.inr (hsgOwn' ▸ ho'))
  · rw [hBslot, hFixEq] at hCost'
    have hMul1 := Nat.mul_le_mul_right (model'.chain.totalRuntime - model.chain.totalRuntime) hToolMulLe
    have hMul2 := Nat.mul_le_mul_right (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) hTreeMulLe
    have hLhs : cost + Rrep.phi root tok' out.mem + K * sg'.reembPot =
        cost + (Rrep.phi root tok' out.mem + K * sg'.reembPot) := Nat.add_assoc ..
    have hRhs : deepFixed + toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
        treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
        Rrep.phi root tok mem0 + K * sg.reembPot =
        deepFixed + toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
        treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
        (Rrep.phi root tok mem0 + K * sg.reembPot) := Nat.add_assoc ..
    dsimp only [Rrep, model'] at hCost' hMul1 hMul2 hLhs hRhs ⊢
    rw [hLhs, hRhs]
    exact hCost'.trans (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add_left hMul1 _) hMul2) _)

/-- **Unconditional proof of `ShiftDeepChainSyncSpecWExtKFBLSel` for
`dryDeepSelectCode`:** discharges `ShiftDeepChainSyncSpecWExtKFBLSel` at `lay.shiftDeepChain`
inside `dryLinkedProgramSel` for any `initSel : DryInitSelectSizes` (`hInitSelSz`),
`termSel : DryTermSelectSizes` (`hTerm`), `openSz : DryOpenSizes` (`hOpen`), and sub-code blocks
`initCode`, `coreCode`, `selectCode`, `termCode`, `selInitCode`, with
`shiftSel := mkDryShiftSelectSizes Psc termSel` and
`selSz := mkDrySelectRebuildSizes initSel shiftSel`. -/
theorem dryDeepSelectCode_hDeepSel (Psc : DrySparseCorePieces)
    (initCode coreCode selectCode termCode selInitCode : SolverInnerSubCode)
    (openSz : DryOpenSizes) (hOpen : DryOpenSizeBounds openSz)
    (initSel : DryInitSelectSizes) (hInitSelSz : DryInitSelectSizeBounds initSel)
    (termSel : DryTermSelectSizes) (hTerm : DryTermSelectSizeBounds termSel) :
    let shiftSel := mkDryShiftSelectSizes Psc termSel
    let hShiftSel := mkDryShiftSelectSizeBounds Psc hTerm
    let selSz := mkDrySelectRebuildSizes initSel shiftSel
    let hSel := mkDrySelectRebuildSizeBounds hInitSelSz hShiftSel
    let inner := dryInnerCodeSel initCode coreCode selectCode termCode dryDeepSelectCode
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let limbMul := concreteReadout2LimbMul dryWitnessUsed
      let PscP := drySCParams Psc dryCapExp limbMul
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let s := dryInnerSizesWithSelect Psc openSz selSz source J
      ShiftDeepChainSyncSpecWExtKFBLSel
        (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
        F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
        (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
        (dryCapLimit dryWitnessUsed J) PscP.wordExp
        (dryLastStretchP J) (dryDeepIntCapMax J) (dryDeepForestEdgeCap J)
        G.n (initTargetCap cfg G) 4 2 (selSz.keyCost source J) F.rangeExponent
        (dryLastStretchP J) (drySlot I.m) cfg G (dryPot J)
        (DryChainLenGridInv J) Rcore
        (dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode)
        (dryTailLay Psc.sc inner).shiftDeepChain
        s.deepSpace s.deepFixed s.toolMul s.treeMul := by
  intro shiftSel hShiftSel selSz hSel inner source J hJn hJm hCost hCap hw
    I V k F cfg G limbMul PscP Rcore s
  let W := dryWitnessUsed
  let coeff := dryAllocCoeffConcrete Psc openSz hOpen selSz hSel
  let deg := dryAllocDegConcrete Psc openSz hOpen selSz hSel
  let w := dryWordSize W coeff deg source
  let p := dryLinkedProgramSel W Psc.sc inner selInitCode
  let lay := dryTailLay Psc.sc inner
  let b := lay.shiftDeepChain
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hfit := ipm_quality_parameter_words_fit I.m V k hw
  have hw14 : 14 ≤ w := hfit.1
  have hw10 : 10 ≤ w := by omega
  have hw16 : 16 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 16 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hB14 : 2 ^ 14 * ipmQualityParameterBound I.m V k < 2 ^ w := by
    have hsz : ipmQualityParameterBound I.m V k < 2 ^ (ipmQualityParameterBound I.m V k).size :=
      Nat.lt_size_self _
    calc 2 ^ 14 * ipmQualityParameterBound I.m V k
        < 2 ^ 14 * 2 ^ (ipmQualityParameterBound I.m V k).size :=
          Nat.mul_lt_mul_of_pos_left hsz (by decide)
      _ = 2 ^ (14 + (ipmQualityParameterBound I.m V k).size) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  have hL4W : 4 * F.limbs + 2 < 2 ^ w := by
    have hLle : F.limbs ≤ ipmQualityParameterBound I.m V k := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityParameterBound]; omega
    have hB1 : 1 ≤ ipmQualityParameterBound I.m V k := by unfold ipmQualityParameterBound; omega
    omega
  have hLkW : F.limbs < 2 ^ w := by omega
  have hpLastLe : dryLastStretchP J ≤ 40 * F.rangeExponent := by
    have h1 := dryLastStretchP_le_forty_rangeExponent J hJn hJm hCap1
    have hmono : (I.m + 1).size ≤ (max I.m (levelM cfg.TP cfg.P cfg.P.d) + 1).size :=
      Nat.size_le_size (Nat.add_le_add_right (le_max_left _ _) 1)
    dsimp only [dryLastStretchP, F, ipmQualityMinRatioFormat, I, V, k, cfg] at h1 hmono ⊢
    omega
  have hpLastW : dryLastStretchP J < 2 ^ w := by
    have hE4L : 40 * F.rangeExponent ≤ 4 * F.limbs := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityLimbs, ipmQualityPrecision,
        ipmQualityErrorBits]
      omega
    omega
  have hWordCoeff : Classical.choose (concrete_solver_word_bounds_poly W) ≤ coeff :=
    (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨hQuotaBoundW, _⟩ :=
    Classical.choose_spec (concrete_solver_word_bounds_poly W)
      coeff deg hWordCoeff source J hJn hJm hCap1 hw
  have hkW : cfg.P.k < 2 ^ w := by
    have hpsi1 : 1 ≤ alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀ := by unfold alg2PsiGameNat; omega
    have h1 : cfg.P.k ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k := by
      unfold shiftQuotaBase; exact Nat.le_mul_of_pos_left _ (by omega)
    have h2 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ≤
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_self_pow (by omega) _
    have h3 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) ≤
        (2 * G.m + 2) * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact lt_of_le_of_lt ((h1.trans h2).trans h3) hQuotaBoundW
  have heCapPos : 0 < initTargetCap cfg G := by
    have hImPos : 0 < I.m := lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap1).1
    have hGm : G.m = I.m := namedInstance_m I
    unfold initTargetCap; omega
  have heCapLeHeap : initTargetCap cfg G ≤ selectHeapCap cfg G I.m := by
    have hGm : G.m = I.m := namedInstance_m I
    unfold initTargetCap selectHeapCap; rw [hGm]; omega
  obtain ⟨hEntryAt, _, _, _, hWireEdgeAt, _, _, hTabWAt, hTabRowAt, hDgCopyAt, hIntLoopAt,
      hFillIntAt, hFillLastAt, hFinAt, hCoreLenAt, hCoreEdgeAt, hFilterAt, hEmbCopyAt,
      hPhiLoopAt, hRebSufAt, hRebLvlAt, hProcListAt, hProcEdgeAt,
      hDgRefMod, hHeapMod, hPhiMod, hEvalMod⟩ :=
    dryDeepSelectCode_hasAll Psc initCode coreCode selectCode termCode selInitCode
  have hOpsAt := dryLinkedProgramSel_ops_hasAt W Psc.sc inner selInitCode
  have hInitH := solverOpsProcs_initHelpers hw14 hOpsAt
  have hK : selectProcessEdgeCost (selectHeapCap cfg G I.m) F.limbs
      (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs) + 60 ≤ selSz.keyCost source J :=
    (dryKeyCost_covers source J).2.1
  exact dryDeepSelectCode_hDeepSel_body J hJn hJm hCap1 hw
    limbMul PscP (drySCAlloc Psc dryCapExp limbMul J) Rcore p b lay.scOp
    (dryDeepSpace Psc J) s.deepSpace s.deepFixed
    (wireTreeSyncEditCost F.limbs (detectOffTreeDrainUnit F.limbs) + 2) s.treeMul s.toolMul
    (selSz.keyCost source J)
    (drySCRep_local Psc coeff deg source J hw)
    hw10 hw16 hLkW hpLastLe hpLastW hkW heCapPos heCapLeHeap
    hEntryAt hIntLoopAt hFillIntAt hFillLastAt hFinAt hEmbCopyAt hPhiLoopAt hRebSufAt
    hRebLvlAt hProcListAt hProcEdgeAt hHeapMod hPhiMod hEvalMod
    (fun _ _ _ => selTableWrite_meetsContract hTabWAt (selTableRow_meetsContract hTabRowAt))
    (fun _ _ _ _ => dgCopyRefill_meetsContract hDgCopyAt (fun _ _ => dgRefillModule_meetsContract hDgRefMod))
    (fun _ => selCoreLenFill_meetsContract hCoreLenAt
      (selCoreLenEdge_meetsContract hCoreEdgeAt hInitH.2.2.2.2.2.1 hWireEdgeAt
        hInitH.2.2.2.2.1 hInitH.2.2.1 hInitH.2.2.2.2.2.2.1 hInitH.1))
    (fun _ => selFilterAbsent_meetsContract hFilterAt)
    (fun j hj G' hGn hGm =>
      (drySC_coreKFBL_sel Psc inner selInitCode coeff deg source J hJn hJm hCap1 hw j hj G' hGn hGm).2)
    (dryDeepSelectCode_hDeepInner Psc initCode coreCode selectCode termCode selInitCode openSz hOpen
      selSz hSel source J hJn hJm hCost hCap hw)
    hK rfl rfl
    ((dryDeepSelectToolMul_le Psc initSel shiftSel source J).trans (Nat.le_add_right _ _))
    (Nat.le_add_right _ _)

end MinCostFlow.Final.DryRun

end
