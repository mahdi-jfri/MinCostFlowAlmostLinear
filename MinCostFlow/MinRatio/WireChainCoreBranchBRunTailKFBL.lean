module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailSufKFBL
import WordRAM.Tactic

/-!
# The tail of the run of Branch B (`WireChainCoreBranchBRunTailKFBL`)

The tail goal `BranchBRunTailGoalKFBL` builds a full run `BranchBRunKFBL` from a head
`BranchBRunHeadKFBL`. The fields of the run up to `modelEq`, and `ec0_eq`, `levelU0`, are those of
the head. The others:
* `Fp`, `oldFs`, `newFs`: their definitions;
* `split`: the split goal `BranchBTailSplitGoalKFBL`;
* `phaseX`: the phase goal `BranchBTailPhaseGoalKFBL`;
* `suf`, `sufRecCut`: the suffix from the state after the exit (`suffix_run`), with the room goal
  `BranchBTailRoomGoalKFBL`;
* `cost`, `runs`, `costLe`: the run goal `BranchBTailRunsGoalKFBL`;
* `rebuiltOrd`: `ord_end` (the meta words of the levels have tag `22 + d`, so the suffix keeps
  them, and `rebuiltOrdX` gives the order after the exit).

`branchBRunTailGoal_of_parts` proves the tail goal from the four goals.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

namespace BranchBRunHeadKFBL

variable {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
      collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {stepCap : ℕ → ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}

variable (Hd : BranchBRunHeadKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)

/-- The order of the rebuilt level blocks at a memory `mem'` that keeps the words that the suffix
keeps: the meta words of the levels lie below `uIntBuf` with tag `22 + d`, so they are kept, and
`rebuiltOrdX` gives the order at the memory after the exit. -/
theorem ord_end (mem' : ℕ → ℕ)
    (hFr : ∀ a < Hd.sX.regs 4, a ≠ root + 11 →
      (a < uIntBuf → tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧
        tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) →
      (uIntBuf ≤ a → ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap
        Hd.curTreeTok1 a) → mem' a = Hd.sX.mem a) :
    BranchBRebuiltOrdKFBL (solverLevelMetaAddr tok.table cfg.P.d) cfg.P.d (Hd.fr + 1) heap vCap
      eCap L mem' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := Hd.start.rep0
  obtain ⟨hOwn, hT1, _⟩ := hTags
  obtain ⟨_, _, _, _, hMT, _⟩ := Hd.start.meta0
  obtain ⟨hU, _, _, hFl, hX⟩ := heap_order Hd
  have hS1 := (heap_order Hd).2.1
  have hS2 := (heap_order Hd).2.2.1
  have hk (x : ℕ) (hx : x < 2 * cfg.P.d) :
      mem' (solverLevelMetaAddr tok.table cfg.P.d + x) =
        Hd.sX.mem (solverLevelMetaAddr tok.table cfg.P.d + x) := by
    have ht := hMT x hx
    have hlt := Hd.start.footLt _ (Or.inl (hOwn _ (by rw [ht]; omega)))
    refine hFr _ (by omega) (fun he => ?_) (fun _ => by rw [ht]; omega)
      (fun h => absurd h (by omega))
    rw [he, hT1 11 (by omega)] at ht; omega
  have hO := Hd.rebuiltOrdX
  unfold BranchBRebuiltOrdKFBL at hO ⊢
  obtain ⟨h1, h2⟩ := hO
  have e1 (j : ℕ) : solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j =
      solverLevelMetaAddr tok.table cfg.P.d + (cfg.P.d + j) := by omega
  refine ⟨fun j hj1 hj2 => ?_, fun j₁ j₂ hj₁ hj₂ hj₃ => ?_⟩
  · rw [e1, hk (cfg.P.d + j) (by omega), hk j (by omega), ← e1]
    exact h1 j hj1 hj2
  · rw [e1, hk (cfg.P.d + j₂) (by omega), hk j₁ (by omega), ← e1]
    exact h2 j₁ j₂ hj₁ hj₂ hj₃

set_option maxHeartbeats 1600000 in
/-- **The tail of a run of Branch B from its parts.** From a head, the split facts, the tree state
after the exit, the room of the suffix and the run of the whole core, a full run of Branch B. -/
theorem tail_of_parts
    (hS : ∀ (Fp : Finset ℕ) (oldFs newFs : List MGraph),
      Fp = (Finset.range Hd.fr).biUnion (fun j => (Hd.X.toTreeChain.activeLSF j).F.F.E) →
      oldFs = (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else []) →
      newFs = (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.X Hd.fr else []) →
      (∀ Y : Finset ℕ,
        (∀ e, e ∈ Y ↔ (∃ j < min Hd.fr cfg.P.d, e ∈ (Hd.D j).fDel) ∧ e ∈ Hd.G1.E) →
        Hd.F1 \ Y = Fp ∪ (graphListEdgeUnion oldFs ∩ Hd.G1.E)) ∧
      (∀ j < min Hd.fr cfg.P.d, ∀ e ∈ (Hd.D j).fDel, e ∈ Hd.G1.E → e ∈ Hd.F1) ∧
      (∀ e ∈ Fp, e ∉ graphListEdgeUnion oldFs) ∧ (∀ e ∈ Fp, e ∉ graphListEdgeUnion newFs) ∧
      Fp ∪ graphListEdgeUnion newFs = Hd.X.toTreeChain.chainTree.E ∧
      ((List.range (min Hd.fr cfg.P.d)).flatMap fun j => (Hd.D j).fDel).Nodup)
    (hP : TreeSyncPhaseAt L tok root uIntBuf (Hd.sX.regs 4) tok.rootGraph Hd.G1 Hd.F1 Hd.canonVal
      B R (Hd.G1.E \ (model.chain.G 0).E) Hd.curTree1 Hd.curTreeTok1 Hd.offCnt1 Hd.sX.mem)
    (hR :
    let T := ∑ j ∈ Finset.range Hd.i₀, (Hd.D j).fDel.length
    let S := graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else []) +
      graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.X Hd.fr else [])
    Hd.sX.regs 4 + (2 * T + T * wireTreeSyncEditSpace L) +
        (3 * tok.intCap + 4 * S + S * wireTreeSyncEditSpace L) + 1 ≤
      heap + coreSpace U.length)
    (hN :
    ∀ (o : Outcome) (out : State) (cS : ℕ),
    Runs w p ω (wireBranchBSuffixKFBL emitCuts packEditsProc filterEdits (opTree 4) (opTree 1)
      (opTree 0) bind canonCopy isNeg pushInsProc) Hd.sX o out cS →
    ∃ cost : ℕ, Runs w p ω (ordChainUpdateCoreBodyKFBL
        (wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg
          refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
          sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
        (wireBranchBKFBL collectDel emitCuts packEditsProc filterEdits zeroIns
          refreshAccountsProc updateLen0Proc copyProc updLen slotProc pushInsProc bind canonCopy
          isNeg dgApply initCore coreLenProc lastInit opTree opCore))
      (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos) o out cost ∧
      cost ≤ Hd.c0 + Hd.cP + Hd.cF + Hd.cL + Hd.cX + cS + 12) :
    Nonempty (BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
        intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
        bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
        dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
        edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
        collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
        coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
        allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
        editsPtr editWords g l heap pos ω mem0 mem model tok U B R) := by
  have hSp := hS _ _ _ rfl rfl rfl
  obtain ⟨out, cS, nextHeap, ct, ctt, oc, hRC, hSuf⟩ := suffix_run Hd hP rfl rfl hSp hR
  have hSuf' := hSuf
  obtain ⟨hSufRun, _, _, _, _, _, _, _, _, hSufFr, _⟩ := hSuf'
  obtain ⟨cost, hRuns, hCost⟩ := hN _ out cS hSufRun
  exact ⟨{ Hd with
    Fp := _, Fp_eq := rfl, oldFs := _, oldFs_eq := rfl, newFs := _, newFs_eq := rfl,
    split := hSp, phaseX := hP, out := out, cS := cS, nextHeap := nextHeap, curTree := ct,
    curTreeTok := ctt, offCnt := oc, suf := hSuf, cost := cost, runs := hRuns, costLe := hCost,
    rebuiltOrd := ord_end Hd out.mem hSufFr, sufRecCut := hRC }⟩

end BranchBRunHeadKFBL

/-- **The tail goal of Branch B from its parts**: the split goal, the phase goal, the room goal
and the run goal. -/
theorem branchBRunTailGoal_of_parts (hS : BranchBTailSplitGoalKFBL)
    (hP : BranchBTailPhaseGoalKFBL) (hR : BranchBTailRoomGoalKFBL)
    (hN : BranchBTailRunsGoalKFBL) : BranchBRunTailGoalKFBL :=
  fun Hd => BranchBRunHeadKFBL.tail_of_parts Hd (hS Hd) (hP Hd) (hR Hd) (hN Hd)

/-- The order goal of the tail (`BranchBTailOrdGoalKFBL`) holds: `ord_end`. -/
theorem branchBTailOrdGoalKFBL_proved : BranchBTailOrdGoalKFBL :=
  fun Hd mem' h => BranchBRunHeadKFBL.ord_end Hd mem' h

end MinCostFlow.MinRatio

end
