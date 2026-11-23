module

public import MinCostFlow.Final.AssemblyDryRunSCCoreSelectProof
import MinCostFlow.Final.AssemblyDryRunSCCoreMissing

/-!
# End-to-end select-aware `Update` corollary (`AssemblyDryRunSCCoreSelectEnd`)

Combines the unconditional dry-run select-aware wrapper `dryCoreSel_hWrap`
(`Final/AssemblyDryRunSCCoreSelectProof.lean`) with Adapters 1, 3, 4 and the conditional Adapter 2
(`Final/AssemblyDryRunSCCoreAdapters.lean`): given any inner core sub-code `innerCoreCode` whose
entry meets `OrdChainUpdateCoreSpecWExtKFBL` at every budget `(Bb, Rb)` (at `innerSz`), and after
whose runs the level blocks are apart (the disjointness clause of the core), `dryCoreSelectCode innerCoreCode` at
`lay.ordChainCore` meets `OrdChainUpdateCoreSpecWKFBLSel` at `dryCoreSelectSizes Psc innerSz`.
The facts `CoreSelMissingHyps` that Adapter 2 needs come from the premises of the Sel spec, by
`dryCoreSel_missingHyps` (`Final/AssemblyDryRunSCCoreMissing.lean`).
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- **End-to-end select-aware `Update` corollary (`dryCoreSel_hCoreSel_of_ext`):**
combines `dryCoreSel_hWrap`, `dryCoreSel_hA1`, `dryCoreSel_hA3`, `dryCoreSel_hA4`,
`dryCoreSel_missingHyps` and `dryCoreSel_hA2_of_missing`. Given any inner core block
`innerCoreCode` satisfying `OrdChainUpdateCoreSpecWExtKFBL` at every budget `(Bb, Rb)` (at
`innerSz`), and after whose runs the level blocks are apart, `dryCoreSelectCode innerCoreCode` at
`lay.ordChainCore` satisfies `OrdChainUpdateCoreSpecWKFBLSel` at `dryCoreSelectSizes Psc innerSz`. -/
theorem dryCoreSel_hCoreSel_of_ext (Psc : DrySparseCorePieces)
    (initCode innerCoreCode selectCode termCode deepCode selInitCode : SolverInnerSubCode)
    (innerSz : DryCoreOpenSizes) (hInnerSz : DryCoreOpenSizeBounds innerSz)
    (initSel : DryInitSelectSizes) (hInitSelSz : DryInitSelectSizeBounds initSel)
    (shiftSel : DryShiftSelectSizes) (hShiftSel : DryShiftSelectSizeBounds shiftSel) :
    let coreSz := dryCoreSelectSizes Psc innerSz
    let hCoreSz := dryCoreSelectSizeBounds Psc hInnerSz
    let openSz := coreSz.toDryOpenSizes
    let hOpen := hCoreSz.toDryOpenSizeBounds
    let selSz := mkDrySelectRebuildSizes initSel shiftSel
    let hSel := mkDrySelectRebuildSizeBounds hInitSelSz hShiftSel
    let inner := dryInnerCodeSel initCode (dryCoreSelectCode innerCoreCode) selectCode termCode deepCode
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
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
      let lay := dryTailLay Psc.sc inner
      let w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source
      (∀ Bb Rb : ℤ,
        OrdChainUpdateCoreSpecWExtKFBL w F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
          (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
          (dryCapLimit dryWitnessUsed J) PscP.wordExp (dryLastStretchP J)
          (dryDeepIntCapMax J) (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G)
          cfg G (dryReembFn J) Rcore p (lay.ordChainCore + 1 + innerCoreCode.off)
          (innerSz.coreSpace source J) (innerSz.coreFixed source J)
          (innerSz.coreToolMul source J) (innerSz.coreTreeMul source J) Bb Rb) →
      (∀ (innerBody : Stmt),
        p.procs[lay.ordChainCore + 1 + innerCoreCode.off]? = some innerBody →
        ∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
          (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg F.limbs Rcore)
          (sg : SelectGhost) (U : List Update) (B R : ℤ),
          UpdateCoreSelPremAt w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
            (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
            (dryCapLimit dryWitnessUsed J) (dryDeepIntCapMax J) (dryDeepForestEdgeCap J)
            G.n (initTargetCap cfg G) 4 2 (dryLastStretchP J) (drySlot I.m)
            cfg G (dryPot J) (DryChainLenGridInv J) Rcore s.coreSpace
            root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R →
          (∀ u ∈ U, ∀ e, u.Inserts e →
            Num.Valid mem0 (g + e * F.limbs) 4 F.limbs ∧
              Num.Valid mem0 (l + e * F.limbs) 4 F.limbs) →
          (∀ i < cfg.P.d, model.chain.rebuildCount i + 1 < 2 ^ w) →
          SolverLevelLayoutAt G.n (initTargetCap cfg G) tok mem0 →
          ∀ (nextHeap cost : ℕ) (out : State) (tok' : SolverToken cfg F.limbs Rcore),
            Runs w p ω innerBody (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
              (.returned nextHeap) out cost →
            tok'.table = tok.table →
            SolverLevelMetaDisjAt G.n (initTargetCap cfg G) tok' out.mem) →
      OrdChainUpdateCoreSpecWKFBLSel w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
        (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
        (dryCapLimit dryWitnessUsed J) (dryDeepIntCapMax J) (dryDeepForestEdgeCap J)
        G.n (initTargetCap cfg G) 4 2 (selSz.keyCost source J) (dryLastStretchP J) (drySlot I.m)
        cfg G (dryPot J) (DryChainLenGridInv J) Rcore p lay.ordChainCore
        s.coreSpace s.coreFixed s.toolMul s.treeMul := by
  intro coreSz hCoreSz openSz hOpen selSz hSel inner source J hJn hJm hCost hCap hw
    I V k F cfg G limbMul PscP Rcore s p lay w hExt hCoreDisjAll
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  obtain ⟨innerBody, hInnerAt, _⟩ := hExt 0 0
  refine dryCoreSel_hWrap Psc initCode innerCoreCode selectCode termCode deepCode selInitCode
    innerSz hInnerSz initSel hInitSelSz shiftSel hShiftSel source J hJn hJm hCost hCap hw
    innerBody hInnerAt ?_ (hCoreDisjAll innerBody hInnerAt)
  intro root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok sg U B R hPrem
    hglValid hRebW hLay
  obtain ⟨b', hb', hRun⟩ := hExt B R
  have hbb : b' = innerBody := Option.some.inj (hb'.symm.trans hInnerAt)
  subst hbb
  have hExtM := dryCoreSel_hA1 J hJn hJm hCap1 hw limbMul (dryDeepIntCapMax J)
    (dryDeepForestEdgeCap J) Rcore s.coreSpace root uIntBuf editsPtr editWords g l heap mem0 mem
    model tok sg U B R hPrem
  have hWordExpLe : PscP.wordExp ≤ 39 := by
    dsimp only [PscP]; rw [drySCParams_wordExp]; exact drySCWordExp_le_39 Psc
  have hMiss := dryCoreSel_missingHyps (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel) PscP.wordExp (le_max_right _ _) hWordExpLe
    source J hJn hJm hCap1 hw hPrem hglValid hRebW hLay
  have hMI := dryCoreSel_hA2_of_missing J hJn hJm hCap1 hw hPrem hMiss
  have hMK := dryCoreSel_hA3 J hJn hJm hCap1 hw limbMul (dryDeepIntCapMax J)
    (dryDeepForestEdgeCap J) Rcore s.coreSpace root uIntBuf editsPtr editWords g l heap mem0 mem
    model tok sg U B R hPrem
  have hFC := dryCoreSel_hA4 J hJn hJm hCap1 hw limbMul (dryDeepIntCapMax J)
    (dryDeepForestEdgeCap J) Rcore s.coreSpace root uIntBuf editsPtr editWords g l heap mem0 mem
    model tok sg U B R hPrem
  obtain ⟨hRep0, hMeta0, hCaps0, _, _, _, _, _, _, _, hNum0, hOffInv0, hOffBd0, _, hCapT, _, _,
    _, hIntCapEq, hIntCapMax, _, hLogW, hShift, _, hWire, hBran, _, _, hMemEq, hFresh, hTrNf,
    hBatch, hSmall, hEdits, hEditsW, hEdHeap, hRef, hFootLt, hGLt, hLLt, _, hULe, hz0,
    hRoom⟩ := hPrem
  have hRoomIn : heap + innerSz.coreSpace source J U.length < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right _ _) heap) hRoom
  exact hRun root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok U B R hRep0 hMeta0
    hCaps0 hIntCapEq hExtM hNum0 hOffInv0 hOffBd0 le_rfl le_rfl hShift hWire hBran hMI hMK
    hIntCapMax hFC hLogW hCapT hMemEq hFresh hTrNf hBatch hSmall hEdits hEditsW hEdHeap hRef
    (fun a ha => hFootLt a (Or.inl ha)) hGLt hLLt hULe hz0 hRoomIn

end MinCostFlow.Final.DryRun

end
