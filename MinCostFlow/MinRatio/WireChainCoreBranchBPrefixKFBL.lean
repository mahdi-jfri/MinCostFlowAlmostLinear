module

public import MinCostFlow.MinRatio.WireChainCoreBranchBPrefixAuxKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBSync1KFBL
public import MinCostFlow.MinRatio.WireChainCoreRefreshLen0KFBL
public import MinCostFlow.MinRatio.WireShiftDeepSteps
import WordRAM.Tactic

/-!
# The start of Branch B (`WireChainCoreBranchBPrefixKFBL`)

Branch B of the chain-update core runs when level `0` is not rebuilt. Before its level loop it
does four things.
1. It stores the pointer to the old forest of the terminal level in the array of old forests
   (`collectTermForestStmt 80`), which the exits of the loop read.
2. It writes `0` at the slots of the inserted names. A batch may refresh an edge twice; it then
   deletes a fresh name, and the cut emitter of the next step must skip that name.
3. Sync 1 (`wireBranchBSync1Stmt`): the deleted names on the path tree leave it.
4. It writes `0` at the slots of the inserted names again (the sync may write slots of names off
   the root graph), refreshes the accounts of the refreshed edges, and writes the lengths of level
   `0` (`wireRefreshLen0Stmt`).

`wireBranchBPrefixKFBL_runs` runs these steps from the state after the dispatch of the core. It
gives the tree state after Sync 1 at a memory `memS1`, the words that the later steps keep from
`memS1`, the accounts after the refresh, and the cost with the change of the tree potential.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The start of Branch B: store the old terminal forest, zero the slots of the inserted names,
Sync 1, zero them again, then refresh the accounts and the lengths of level `0`. -/
@[expose] def wireBranchBPrefixKFBL (collectDel emitCuts readTree cutTree linkTree bind canonCopy
    isNeg zeroIns refreshAccountsProc updateLen0Proc : ℕ) : Stmt :=
  collectTermForestStmt 80 ;;
  wireZeroInsStmt zeroIns ;;
  wireBranchBSync1Stmt collectDel emitCuts readTree cutTree linkTree bind canonCopy isNeg ;;
  wireZeroInsStmt zeroIns ;;
  wireRefreshLen0Stmt refreshAccountsProc updateLen0Proc

theorem wireBranchBPrefixKFBL_noRand (collectDel emitCuts readTree cutTree linkTree bind
    canonCopy isNeg zeroIns refreshAccountsProc updateLen0Proc : ℕ) :
    (wireBranchBPrefixKFBL collectDel emitCuts readTree cutTree linkTree bind canonCopy isNeg
      zeroIns refreshAccountsProc updateLen0Proc).NoRand := by
  simp only [wireBranchBPrefixKFBL, Stmt.NoRand]
  exact ⟨collectTermForestStmt_noRand _, wireZeroInsStmt_noRand _,
    wireBranchBSync1Stmt_noRand _ _ _ _ _ _ _ _, wireZeroInsStmt_noRand _,
    wireRefreshLen0Stmt_noRand _ _⟩

/-- A refreshed name of the root graph gets a fresh name, which is not an edge of the root
graph. -/
theorem refreshed_newName_not_mem {extG G0 : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    {U : List Update} (hFresh : FreshInv extG G0 e2i i2e nf) (hRef : RefreshBatch extG U)
    {ei : ℕ} (hei : ei ∈ G0.E)
    (hdel : Update.delete ei ∈ (translateBatch extG e2i i2e nf U).2.2.2.2) :
    (translateBatch extG e2i i2e nf U).2.1 ((translateBatch extG e2i i2e nf U).2.2.1 ei) ∉
      G0.E := by
  classical
  obtain ⟨_, _, _, hUnch, hRep⟩ := refreshBatch_edge_dichotomy hFresh hRef
  obtain ⟨heMap, heExt⟩ := hFresh.hRight ei hei
  by_cases hIns : ∃ u ∈ U, u.Inserts (i2e ei)
  · obtain ⟨_, _, hi2e, hnot, _⟩ := hRep (i2e ei) heExt hIns
    rw [heMap] at hi2e
    rw [hi2e]
    exact hnot
  · obtain ⟨_, _, _, hnd, _⟩ := hUnch (i2e ei) heExt hIns
    rw [heMap] at hnd
    exact absurd hdel hnd

set_option maxHeartbeats 4000000 in
/-- The run of the start of Branch B from the state after the dispatch of the core. The tree
state after Sync 1 holds at `memS1` for the chain tree without the deleted names, with the heap
pointer `hS1`. Below `h0` (the heap pointer after the dispatch) `memS1` differs from `mem` only
at the words that a sync may write and at the stored old terminal forest. Below `hS1` the
refresh writes only the words of names off the root graph and the lengths of level `0`. The
slots of the inserted names are `0` at the end. -/
theorem wireBranchBPrefixKFBL_runs
    {w L P m V psi k epsExp drainUnit wordExp stretchPrec initTree bind canonCopy isNeg
      collectDel emitCuts zeroIns refreshAccountsProc shift negate refreshOneProc divide add sub
      copy updateLen0Proc root uIntBuf editsPtr editWords g l heap ec0 termHandle lastBran lsfHdr
      forestPtr : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {p : Program} {opTree : ℕ → ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {st : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
    (hCollect : p.procs[collectDel]? = some wireCollectDeletedEdgesBody)
    (hEmit : p.procs[emitCuts]? = some wireEmitTreeCutsBody)
    (hZeroIns : p.procs[zeroIns]? = some wireZeroInsertSlotsBody)
    (hRefAccProc : p.procs[refreshAccountsProc]? =
      some (wireRefreshAccountsBody shift negate refreshOneProc))
    (hRefOneProc : p.procs[refreshOneProc]? =
      some (wireRefreshOneAccountBody divide add sub negate copy isNeg))
    (hUpdLen0Proc : p.procs[updateLen0Proc]? = some (wireUpdateLen0FromBatchBody copy))
    (hFmtBits : fmt.limbBits = 4) (hLpos : 0 < L) (hPword : P < 2 ^ w) (hw18 : 18 < 2 ^ w)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree
      opTree (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hBindOk : MeetsContract w p bind (pathSlotBindContract w))
    (hCanonOk : ∀ v, MeetsContract w p canonCopy (wireCanonCopyContract w v))
    (hIsNegOk : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w 4))
    (hdiv : MeetsContract w p divide (Num.fixedDivideContract w 4))
    (hadd : MeetsContract w p add (Num.addContract w 4))
    (hsub : MeetsContract w p sub (Num.subtractContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hNum0 : PathTreeNumericInv tok.tree tok.trees B R)
    (hOffInv0 : OffTreeRecInv model L mem0 tok.edgeRecords B)
    (hOffBd0 : OffTreeRecBound model L mem0 tok.edgeRecords B)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hLogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hCapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hRef : RefreshBatch model.extG U)
    (hMemEq : ∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a)
    (hFreshMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        tr.2.1 tr.2.2.1 tr.2.2.2.1)
    (hTrNfLe :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      tr.2.2.2.1 ≤ tok.intCap)
    (hBatchMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      IPM.Machine.BatchAt mem uIntBuf tr.2.2.2.2)
    (hSmallMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf))
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hGLt : g + m * L ≤ uIntBuf) (hLLt : l + m * L ≤ uIntBuf)
    (hULeEd : uIntBuf + cfg.P.d ≤ editsPtr) (hEdHeap : editsPtr + editWords = heap)
    (hLevel0Meta :
      let lm := solverLevelMetaAddr tok.table cfg.P.d
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      EdgeValuesAt mem0 (mem0 lm) 4 L P (model.chain.G 0).E
        (model.chain.toTreeChain.chainLen model.chain.ℓ 0) ∧
      (∀ a, mem0 lm ≤ a → a < mem0 lm + ec0 * L → tok.tag a = 23 + cfg.P.d) ∧
      (∀ e ∈ (model.chain.G 0).E, e < ec0) ∧
      (∀ e ∈ ((model.chain.G 0).applyBatch tr.2.2.2.2).E, e < ec0) ∧
      (∀ u ∈ tr.2.2.2.2, match u with | .insert ei _ _ => ei < ec0 | _ => True))
    (hz : ZeroFrom mem heap) (hStMem : st.mem = mem)
    (hRegs : st.regs 4 = heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ∧
      st.regs 70 = root ∧ st.regs 71 = 0 ∧ st.regs 73 = tok.handle ∧ st.regs 75 = cfg.P.d ∧
      st.regs 77 = tok.handle + 18 ∧ st.regs 78 = tok.handle + 18 + (cfg.P.d + 1) ∧
      st.regs 80 = heap + 1 + 12 * cfg.P.d ∧
      st.regs 83 = solverLevelMetaAddr tok.table cfg.P.d ∧ st.regs 87 = uIntBuf ∧
      st.regs 90 = g ∧ st.regs 91 = l ∧ st.regs 94 = L)
    (hTermH : mem (tok.handle + 18 + cfg.P.d) = termHandle)
    (hTermB : mem (tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d) = lastBran)
    (hLsfHdr : mem (termHandle + 1 + lastBran) = lsfHdr) (hForestPtr : mem (lsfHdr + 1) = forestPtr)
    (hHBW : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d < 2 ^ w)
    (hTW : termHandle + 1 + lastBran < 2 ^ w) (hLW : lsfHdr + 1 < 2 ^ w)
    (hRoom : heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 + 3 * U.length +
      U.length * wireTreeSyncEditSpace L + 1 + 3 * L + U.length * wireRefreshOneSpace L < 2 ^ w) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let d := cfg.P.d
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let U_int := tr.2.2.2.2
    let G0 := model.chain.G 0
    let G0' := G0.applyBatch U_int
    let F := model.chain.toTreeChain.chainTree.E
    let F1 := F \ (batchDeletedEdges U_int).toFinset
    let h0 := heap + 1 + 12 * d + 3 * (d + 1) + 4
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
    let ℓ' := fun e' => lVec (tr.2.2.1 e')
    let lm := solverLevelMetaAddr tok.table d
    ∃ (out : State) (cost hS1 heap2 : ℕ) (memS1 : ℕ → ℕ) (curTree' : PathTreeState)
      (curTreeTok' : Rtree.τ) (offCnt' : ℕ) (canonVal newCanonVal : ℕ → PathEdgeValue),
      Runs w p ω (wireBranchBPrefixKFBL collectDel emitCuts (opTree 4) (opTree 1) (opTree 0) bind
        canonCopy isNeg zeroIns refreshAccountsProc updateLen0Proc) st .normal out cost ∧
      out.regs 4 = heap2 ∧ (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      h0 ≤ hS1 ∧ hS1 ≤ h0 + 3 * U.length + U.length * wireTreeSyncEditSpace L ∧
      hS1 + 3 * L ≤ heap2 ∧ heap2 ≤ hS1 + 3 * L + U.length * wireRefreshOneSpace L ∧
      ZeroFrom out.mem heap2 ∧
      TreeSyncPhaseAt L tok root uIntBuf hS1 tok.rootGraph G0 F1 canonVal B R ∅ curTree'
        curTreeTok' offCnt' memS1 ∧
      (∀ a, Rtree.foot tok.treeHeap curTreeTok' a →
        Rtree.foot tok.treeHeap tok.treeTok a ∨ (h0 ≤ a ∧ a < hS1)) ∧
      (∀ ei ∈ F, Update.delete ei ∈ U_int →
        h0 ≤ memS1 (tok.edgeRecords + ei) ∧ memS1 (tok.edgeRecords + ei) + (2 + 4 * L) ≤ hS1) ∧
      (∀ ei ∈ G0.E, ei ∉ F → memS1 (tok.edgeRecords + ei) = mem0 (tok.edgeRecords + ei)) ∧
      (∀ a < h0, a ≠ root + 11 →
        (a < uIntBuf → tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧
          tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) →
        memS1 a = Function.update mem (heap + 1 + 12 * d + d) forestPtr a) ∧
      (∀ a < hS1, (∀ ei < tok.intCap, ei ∉ G0.E → a ≠ tok.slots + ei ∧
          a ≠ tok.edgeThresholds + ei ∧ a ≠ tok.edgeRecords + ei) →
        (a < mem0 lm ∨ mem0 lm + ec0 * L ≤ a) → out.mem a = memS1 a) ∧
      (∀ e ∈ batchInsertedEdges U_int, out.mem (tok.slots + e) = 0) ∧
      EdgeValuesAt out.mem (mem0 lm) 4 L P G0'.E ℓ' ∧
      (∀ e ∈ model.extG.E,
        let ei := model.extToInt e
        let v := canonVal ei
        v.forward = true ∧ |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧
        |v.detector| ≤ B ∧
        (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (v.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg e ∧
        (v.length : ℝ) / (2 : ℝ) ^ P = model.extℓ e ∧
        ∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
          v.detector = acc - detectorThreshold P cfg.ε (model.extℓ e)) ∧
      (∀ e ∈ model.extG.E,
        let ei := tr.2.1 e
        let v := newCanonVal ei
        PathIntAt out.mem (out.mem (tok.edgeThresholds + ei))
            4 L (detectorThreshold P cfg.ε (lVec e)) ∧
        v.forward = true ∧ |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B ∧
        (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (v.originalGradient : ℝ) / (2 : ℝ) ^ P = gVec e ∧
        (v.length : ℝ) / (2 : ℝ) ^ P = lVec e ∧
        (∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
          v.detector = acc - detectorThreshold P cfg.ε (lVec e)) ∧
        (ei ∈ G0.E →
          newCanonVal ei = canonVal ei ∧
          out.mem (tok.edgeThresholds + ei) = mem0 (tok.edgeThresholds + ei) ∧
          out.mem (tok.edgeRecords + ei) = memS1 (tok.edgeRecords + ei) ∧
          (ei ∉ F1 → PathEdgeAt out.mem (out.mem (tok.edgeRecords + ei)) 4 L (some v))) ∧
        (ei ∉ G0.E →
          hS1 + 3 * L ≤ out.mem (tok.edgeThresholds + ei) ∧
          out.mem (tok.edgeThresholds + ei) + L ≤ heap2 ∧
          hS1 + 3 * L ≤ out.mem (tok.edgeRecords + ei) ∧
          out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heap2 ∧
          PathEdgeAt out.mem (out.mem (tok.edgeRecords + ei)) 4 L (some v))) ∧
      (∀ ei₁ ∈ G0'.E, ∀ ei₂ ∈ G0'.E, ei₁ ≠ ei₂ → ei₁ ∉ F1 → ei₂ ∉ F1 →
        out.mem (tok.edgeRecords + ei₁) + (2 + 4 * L) ≤ out.mem (tok.edgeRecords + ei₂) ∨
        out.mem (tok.edgeRecords + ei₂) + (2 + 4 * L) ≤ out.mem (tok.edgeRecords + ei₁)) ∧
      (∀ ei₁ ∈ G0'.E, ei₁ ∉ G0.E → ∀ ei₂ ∈ G0'.E, ei₂ ∉ G0.E →
        out.mem (tok.edgeThresholds + ei₁) + L ≤ out.mem (tok.edgeRecords + ei₂) ∨
        out.mem (tok.edgeRecords + ei₂) + (2 + 4 * L) ≤ out.mem (tok.edgeThresholds + ei₁)) ∧
      cost + (Rtree.phi tok.treeHeap curTreeTok' memS1 + offCnt' * drainUnit) ≤
        35 + 2 * (50 * U.length + 45) +
          (U.length * (wireTreeSyncEditCost L drainUnit + 2) + 90 * U.length + 230) +
          ((U.length * (wireRefreshOneCost L + 120) + 71 * L + 210) +
            (U.length * (17 * L + 70) + 80)) + 4 +
          (Rtree.phi tok.treeHeap tok.treeTok mem0 + tok.offReadyCount * drainUnit) := by
  classical
  intro Rtree d tr U_int G0 G0' F F1 h0 gVec lVec ℓ' lm
  obtain ⟨hr4, hr70, hr71, hr73, hr75, hr77, hr78, hr80, hr83, hr87, hr90, hr91, hr94⟩ := hRegs
  have hRep0_keep := hRep0
  obtain ⟨hRootDir0, _, _, _, hFreshInv, _, _, ⟨hG0Cap, hIntCapPos, _, _⟩, _, _, _, _, _, _,
    _, _, _, _, hWire0, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, _, _, _, _, _, _, _, hT9, _, _, hT12, hT13, _, _, hT16, _, _, hT20,
    _⟩ := hTags0
  obtain ⟨_, _, ⟨hForestF, _⟩, _, _⟩ := hWire0
  have hOldSub : F ⊆ G0.E := hModelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hG0nEq : G0.n = model.extG.n := by unfold MGraph.n; rw [← hFreshInv.hV]
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hRootW : root + 16 ≤ uIntBuf := by
    have := htagLt (by rw [hT1 15 (by omega)]; decide); omega
  have hThrEnd : tok.edgeThresholds + tok.intCap ≤ uIntBuf := by
    have := htagLt (by rw [hT12 (tok.intCap - 1) (by omega)]; decide); omega
  have hRecEnd : tok.edgeRecords + tok.intCap ≤ uIntBuf := by
    have := htagLt (by rw [hT13 (tok.intCap - 1) (by omega)]; decide); omega
  have hSlotEnd : tok.slots + tok.intCap ≤ uIntBuf := by
    have := htagLt (by rw [hT9 (tok.intCap - 1) (by omega)]; decide); omega
  have hTreeFootLt (a : ℕ) (ha : Rtree.foot tok.treeHeap tok.treeTok a) : a < uIntBuf :=
    htagLt (by rw [hT16 a ha]; decide)
  -- facts on the internal batch
  have hEdgeU : ∀ u ∈ U, IsEdgeUpdate u := fun u hu => by
    cases u with
    | insert _ _ _ | delete _ => trivial
    | split _ _ _ _ => exact hRef.2.2 _ hu
  have hULenEq : U_int.length = U.length :=
    translateBatch_length_eq U model.extG model.extToInt model.intToExt model.nextFresh hEdgeU
  obtain ⟨_, _, hEdgeInt, _, _⟩ := refreshBatch_edge_dichotomy hFreshInv hRef
  obtain ⟨_, _, hRangeAll, hNodupR, _⟩ :=
    translateBatch_oldId_facts U model.extG G0 model.extToInt model.intToExt model.nextFresh
      hFreshInv hRef.1 hEdgeU
  obtain ⟨_, _, hG0Valid, _, _, _, hInsFresh, _, _, _⟩ :=
    translateBatch_preserves U model.extG G0 model.extToInt model.intToExt model.nextFresh
      hFreshInv hRef.1
  have hTrNf : tr.2.2.2.1 ≤ tok.intCap := hTrNfLe
  have hInsLt : ∀ e ∈ batchInsertedEdges U_int, e < tok.intCap ∧ e ∉ G0.E := by
    intro e he
    obtain ⟨u, hu, hue⟩ := (mem_batchInsertedEdges_iff U_int e).mp he
    obtain ⟨hlo, hhi⟩ := hInsFresh u hu e hue
    have hhi' : e < tr.2.2.2.1 := hhi
    have hlo' : model.nextFresh ≤ e := hlo
    exact ⟨by omega, fun hG => by have := hFreshInv.hLtFresh e hG; omega⟩
  have hDelLt : ∀ e ∈ batchDeletedEdges U_int, e < tok.intCap := by
    intro e he
    have hd := (mem_batchDeletedEdges_iff U_int e).mp he
    have := hRangeAll _ hd
    exact lt_of_lt_of_le this hTrNf
  have hBW : ∀ t < editsPtr - d - uIntBuf, mem (uIntBuf + t) < 2 ^ w :=
    branchB_batchWords_lt hRep0_keep hModelInv hRef hTrNfLe hBatchMem hSmallMem hFootLt
      (by omega) (by omega)
  -- step 1: store the old terminal forest
  obtain ⟨s1, c1, r1, hc1, hs1Mem, hs1Regs⟩ :=
    collectTermForestStmt_runs (w := w) (p := p) (ω := ω) (st := st) (dstReg := 80)
      (dstPtrs := heap + 1 + 12 * d) (baseIdx := 0) (d := d) (handleBase := tok.handle + 18)
      (branchBase := tok.handle + 18 + (d + 1)) (termHandle := termHandle)
      (lastBran := lastBran) (lsfHdr := lsfHdr) (forestPtr := forestPtr)
      hr80 hr71 hr75 hr77 hr78 (by decide) (Nat.zero_le _)
      (by rw [hStMem]; exact hTermH) (by rw [hStMem]; exact hTermB)
      (by rw [hStMem]; exact hLsfHdr) (by rw [hStMem]; exact hForestPtr)
      (by omega) hHBW hTW hLW (by omega) (by omega)
  rw [Nat.sub_zero] at hs1Mem
  have hs1At (a : ℕ) (ha : a ≠ heap + 1 + 12 * d + d) : s1.mem a = mem a := by
    rw [hs1Mem, Function.update_of_ne ha, hStMem]
  -- step 2: zero the slots of the inserted names
  have hSmall1 : SmallBatchAt s1.mem uIntBuf G0 U_int (editsPtr - d - uIntBuf) :=
    smallBatchAt_congr hSmallMem (fun x _ hx2 => hs1At x (by omega))
  have hSlots0 : mem0 (root + 6) = tok.slots := by simpa using hRootDir0 6 (by simp)
  have hMemEqOf {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) (h6 : v ≠ 6) (h7 : v ≠ 7)
      (h8 : v ≠ 8) : mem a = mem0 a :=
    hMemEq a (htagLt (by rw [ht]; exact hv)) (by rw [ht]; exact h6) (by rw [ht]; exact h7)
      (by rw [ht]; exact h8)
  have hRoot6 : s1.mem (root + 6) = tok.slots :=
    (hs1At _ (by omega)).trans
      ((hMemEqOf (hT1 6 (by omega)) (by decide) (by decide) (by decide) (by decide)).trans hSlots0)
  have hSlotLtIns : ∀ e ∈ batchInsertedEdges U_int, tok.slots + e < uIntBuf := fun e he => by
    have := (hInsLt e he).1; omega
  have hNotSlotOfTag {a : ℕ} (ht : tok.tag a ≠ 9) :
      ∀ e ∈ batchInsertedEdges U_int, a ≠ tok.slots + e :=
    fun e he hae => ht (by rw [hae]; exact hT9 e (hInsLt e he).1)
  have hNotSlotOfGe {a : ℕ} (ha : uIntBuf ≤ a) :
      ∀ e ∈ batchInsertedEdges U_int, a ≠ tok.slots + e :=
    fun e he hae => by have := hSlotLtIns e he; omega
  obtain ⟨s2, c2, r2, hc2, hs2Regs, hs2Zero, hs2Fr⟩ :=
    wireZeroInsStmt_runs (zeroIns := zeroIns) (ω := ω) hZeroIns hSmall1 hEdgeInt
      (fun j hj => by rw [hs1At _ (by omega)]; exact hBW j hj) hSlotLtIns (by omega) (by omega)
      ⟨(hs1Regs 70 (by decide) (by decide) (by decide)).trans hr70,
        (hs1Regs 87 (by decide) (by decide) (by decide)).trans hr87⟩
      hRoot6 (by omega)
  -- step 3: Sync 1
  have hS2Mem0 (a : ℕ) (ha : a < uIntBuf) (h9 : tok.tag a ≠ 9) (h6 : tok.tag a ≠ 6)
      (h7 : tok.tag a ≠ 7) (h8 : tok.tag a ≠ 8) : s2.mem a = mem0 a :=
    (hs2Fr a (hNotSlotOfTag h9)).trans ((hs1At a (by omega)).trans (hMemEq a ha h6 h7 h8))
  have hTagNe {a : ℕ} (htag : tok.tag a = 1 ∨ tok.tag a = 2 ∨ tok.tag a = 10 ∨
      tok.tag a = 11 ∨ tok.tag a = 12 ∨ tok.tag a = 13 ∨ tok.tag a = 14 ∨ tok.tag a = 15 ∨
      tok.tag a = 16 ∨ tok.tag a = 18 ∨ tok.tag a = 20) :
      tok.tag a ≠ 9 ∧ tok.tag a ≠ 6 ∧ tok.tag a ≠ 7 ∧ tok.tag a ≠ 8 := by
    rcases htag with h | h | h | h | h | h | h | h | h | h | h <;> (rw [h]; decide)
  obtain ⟨canonVal, hPh0, hCanonExt⟩ :=
    treeSyncPhaseAt_of_rep (heapX := h0) (mem := s2.mem) hRep0_keep hNum0 hOffInv0 hOffBd0
      hOldSub hFootLt (by omega)
      (fun a ha htag => hS2Mem0 a ha (hTagNe htag).1 (hTagNe htag).2.1 (hTagNe htag).2.2.1
        (hTagNe htag).2.2.2)
      (fun ei hei => by
        have hc := hG0Cap ei hei
        have hnot : ∀ e ∈ batchInsertedEdges U_int, tok.slots + ei ≠ tok.slots + e :=
          fun e he h => (hInsLt e he).2 (by rw [show e = ei by omega]; exact hei)
        exact (hs2Fr _ hnot).trans ((hs1At _ (by omega)).trans
          (hMemEqOf (hT9 ei hc) (by decide) (by decide) (by decide) (by decide))))
  have hSmall2 : SmallBatchAt s2.mem uIntBuf G0 U_int (editsPtr - d - uIntBuf) :=
    smallBatchAt_congr hSmall1 (fun x hx1 _ => hs2Fr x (hNotSlotOfGe hx1))
  have hBW2 : ∀ j < editsPtr - d - uIntBuf, s2.mem (uIntBuf + j) < 2 ^ w := fun j hj => by
    rw [hs2Fr _ (hNotSlotOfGe (by omega)), hs1At _ (by omega)]; exact hBW j hj
  have hz2 : ZeroFrom s2.mem h0 := fun a ha => by
    rw [hs2Fr a (hNotSlotOfGe (by omega)), hs1At a (by omega)]; exact hz a (by omega)
  have hS2R (r : ℕ) (hr : 70 ≤ r) : s2.regs r = st.regs r :=
    (hs2Regs r (by omega) (by omega)).trans (hs1Regs r (by omega) (by omega) (by omega))
  obtain ⟨s3, c3, hS1, curTree', curTreeTok', offCnt', r3, hs3R4, hs3Regs, hS1Lo, hS1Hi, hz3,
      hPh3, hDiff, hFoot3, hKeepRec3, hDRec3, hFr3, hc3⟩ :=
    wireBranchBSync1Stmt_runs (collectDel := collectDel) (emitCuts := emitCuts)
      (initTree := initTree) (drainUnit := drainUnit) (opTree := opTree) (ω := ω) (st := s2)
      (U := U_int) (bW := editsPtr - d - uIntBuf)
      hCollect hEmit hFmtBits hw18 hTreeImpl hBindOk hCanonOk hIsNegOk hRep0_keep hFootLt hG0nEq
      hLogW hCapT hPh0 hForestF hSmall2 hEdgeInt hBW2 (by omega) hDelLt
      (fun e he hnG => by
        rcases batchDeletedEdges_mem_or_inserted G0 U_int hG0Valid e he with h | h
        · exact absurd h hnG
        · exact hs2Zero e h)
      (by rw [batchDeletedEdges_filter]; exact hNodupR)
      ⟨(hs2Regs 4 (by decide) (by decide)).trans ((hs1Regs 4 (by decide) (by decide)
          (by decide)).trans hr4),
        (hS2R 70 (by decide)).trans hr70, (hS2R 73 (by decide)).trans hr73,
        (hS2R 87 (by decide)).trans hr87⟩
      hz2 (by rw [hULenEq]; omega)
  rw [hULenEq] at hS1Hi hc3
  have hF1eq : F \ (treeCutsOf (fun e => s2.mem (tok.slots + e))
      (batchDeletedEdges U_int)).toFinset = F1 := by
    ext e
    simp only [F1, Finset.mem_sdiff, List.mem_toFinset]
    rw [hDiff e, mem_batchDeletedEdges_iff]
    tauto
  rw [hF1eq] at hPh3
  -- step 4: zero the slots of the inserted names again
  have hS3Eq2 (a : ℕ) (ha : a < h0) (hne : a ≠ root + 11)
      (htag : a < uIntBuf → tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧
        tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) : s3.mem a = s2.mem a :=
    hFr3 a ha hne htag (fun h hf => by have := hTreeFootLt a hf; omega)
  have hSmall3 : SmallBatchAt s3.mem uIntBuf G0 U_int (editsPtr - d - uIntBuf) :=
    smallBatchAt_congr hSmall2 (fun x hx1 hx2 =>
      hS3Eq2 x (by omega) (by omega) (fun h => absurd h (by omega)))
  have hBW3 : ∀ j < editsPtr - d - uIntBuf, s3.mem (uIntBuf + j) < 2 ^ w := fun j hj => by
    rw [hS3Eq2 _ (by omega) (by omega) (fun h => absurd h (by omega))]; exact hBW2 j hj
  have hS3R (r : ℕ) (hr : 70 ≤ r) : s3.regs r = st.regs r := (hs3Regs r hr).trans (hS2R r hr)
  obtain ⟨s4, c4, r4, hc4, hs4Regs, hs4Zero, hs4Fr⟩ :=
    wireZeroInsStmt_runs (zeroIns := zeroIns) (ω := ω) hZeroIns hSmall3 hEdgeInt hBW3
      hSlotLtIns (by omega) (by omega)
      ⟨(hS3R 70 (by decide)).trans hr70, (hS3R 87 (by decide)).trans hr87⟩ hPh3.dir.1 (by omega)
  have hS4R (r : ℕ) (hr : 70 ≤ r) : s4.regs r = st.regs r :=
    (hs4Regs r (by omega) (by omega)).trans (hS3R r hr)
  -- step 5: the refresh of the accounts and the lengths of level `0`
  have hdPos : 0 < d := hModelInv.1.1
  have hTagL0 : ∀ a, mem0 lm ≤ a → a < mem0 lm + ec0 * L → tok.tag a = 23 + d :=
    hLevel0Meta.2.1
  have hOldLenEnd : mem0 lm + ec0 * L ≤ uIntBuf := by
    by_cases h0L : ec0 * L = 0
    · obtain ⟨_, _, _, _, hOwn0, _, _⟩ := hMeta0.2.2.2.2.2 0 hdPos
      have hOwn0' : tok.owned (mem0 lm) := by simpa using hOwn0
      have := hFootLt (mem0 lm) (Or.inl hOwn0'); omega
    · have := htagLt (by
        rw [hTagL0 (mem0 lm + ec0 * L - 1) (by omega) (by omega)]; omega)
      omega
  have hNotMutOfTag {a v : ℕ} (ht : tok.tag a = v) (h12 : v ≠ 12) (h13 : v ≠ 13) :
      ¬ InRefreshMutable tok.edgeThresholds tok.edgeRecords tok.intCap a := by
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have := hT12 (a - tok.edgeThresholds) (by omega)
      rw [show tok.edgeThresholds + (a - tok.edgeThresholds) = a by omega, ht] at this
      exact h12 this
    · have := hT13 (a - tok.edgeRecords) (by omega)
      rw [show tok.edgeRecords + (a - tok.edgeRecords) = a by omega, ht] at this
      exact h13 this
  have hNotMutOfGe {a : ℕ} (ha : uIntBuf ≤ a) :
      ¬ InRefreshMutable tok.edgeThresholds tok.edgeRecords tok.intCap a := by
    rintro (⟨_, _⟩ | ⟨_, _⟩) <;> omega
  have hS4Eq3 (a : ℕ) (h : ∀ e ∈ batchInsertedEdges U_int, a ≠ tok.slots + e) :
      s4.mem a = s3.mem a := hs4Fr a h
  have hS4Mem0 : ∀ a < uIntBuf, a ≠ root + 11 →
      tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 →
      tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 →
      tok.tag a ≠ 13 → tok.tag a ≠ 14 → tok.tag a ≠ 15 → tok.tag a ≠ 16 →
      (∀ j < cfg.P.d, tok.tag a ≠ 21 + j) → s4.mem a = mem0 a := by
    intro a ha hne11 h6 h7 h8 h9 h10 h11 h13 h14 h15 h16 _
    exact (hS4Eq3 a (hNotSlotOfTag h9)).trans ((hS3Eq2 a (by omega) hne11
      (fun _ => ⟨h9, h10, h11, h13, h14, h15, h16⟩)).trans (hS2Mem0 a ha h9 h6 h7 h8))
  have hS4MemFresh : ∀ a < heap,
      (tok.tag a = 6 ∨ tok.tag a = 7 ∨ tok.tag a = 8 ∨ uIntBuf ≤ a) → s4.mem a = mem a := by
    intro a ha hcase
    have hne : a ≠ heap + 1 + 12 * d + d := by omega
    rcases hcase with h | h | h | h
    all_goals first
      | (have hlt : a < uIntBuf := htagLt (by rw [h]; decide)
         have h11 : a ≠ root + 11 := fun he => by rw [he, hT1 11 (by omega)] at h; omega
         exact (hS4Eq3 a (hNotSlotOfTag (by rw [h]; decide))).trans ((hS3Eq2 a (by omega) h11
           (fun _ => by rw [h]; decide)).trans ((hs2Fr a (hNotSlotOfTag (by rw [h]; decide))).trans
           (hs1At a hne))))
      | exact (hS4Eq3 a (hNotSlotOfGe h)).trans ((hS3Eq2 a (by omega) (by omega)
          (fun h' => absurd h' (by omega))).trans ((hs2Fr a (hNotSlotOfGe h)).trans
          (hs1At a hne)))
  have hRec43 (ei : ℕ) (hc : ei < tok.intCap) :
      s4.mem (tok.edgeRecords + ei) = s3.mem (tok.edgeRecords + ei) :=
    hS4Eq3 _ (hNotSlotOfTag (by rw [hT13 ei hc]; decide))
  have hOffSynced4 :
      (∀ ei ∈ G0.E, (Update.delete ei ∈ U_int ∨ ei ∉ F1) →
        PathEdgeAt s4.mem (s4.mem (tok.edgeRecords + ei)) 4 L (some (canonVal ei)) ∧
        s4.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ hS1 ∧
        (∀ j < 2 + 4 * L, ¬ InRefreshMutable tok.edgeThresholds tok.edgeRecords tok.intCap
          (s4.mem (tok.edgeRecords + ei) + j) ∧
          (s4.mem (tok.edgeRecords + ei) + j < mem0 lm ∨
            mem0 lm + ec0 * L ≤ s4.mem (tok.edgeRecords + ei) + j))) ∧
      (∀ e₁ ∈ G0.E, ∀ e₂ ∈ G0.E, e₁ ≠ e₂ → e₁ ∉ F1 → e₂ ∉ F1 →
        s4.mem (tok.edgeRecords + e₁) + (2 + 4 * L) ≤ s4.mem (tok.edgeRecords + e₂) ∨
        s4.mem (tok.edgeRecords + e₂) + (2 + 4 * L) ≤ s4.mem (tok.edgeRecords + e₁)) := by
    refine ⟨fun ei hei hcase => ?_, fun e1 h1 e2 h2 hne hn1 hn2 => by
      rw [hRec43 e1 (hG0Cap e1 h1), hRec43 e2 (hG0Cap e2 h2)]
      exact hPh3.offDisj e1 h1 e2 h2 hne hn1 hn2⟩
    have hnF1 : ei ∉ F1 := by
      rcases hcase with h | h
      · intro hm
        exact (Finset.mem_sdiff.mp hm).2
          (List.mem_toFinset.mpr ((mem_batchDeletedEdges_iff _ _).mpr h))
      · exact h
    rw [hRec43 ei (hG0Cap ei hei)]
    have hLoc := hPh3.recLoc ei hei hnF1
    have hWord (j : ℕ) (hj : j < 2 + 4 * L) :
        ∀ e ∈ batchInsertedEdges U_int, s3.mem (tok.edgeRecords + ei) + j ≠ tok.slots + e := by
      by_cases hlt : s3.mem (tok.edgeRecords + ei) + j < uIntBuf
      · exact hNotSlotOfTag (by rw [(hLoc j hj).1 hlt]; decide)
      · exact hNotSlotOfGe (by omega)
    refine ⟨(hPh3.offRec ei hei hnF1).congr (fun x hx1 hx2 => by
        have := hWord (x - s3.mem (tok.edgeRecords + ei)) (by omega)
        rw [show s3.mem (tok.edgeRecords + ei) + (x - s3.mem (tok.edgeRecords + ei)) = x by
          omega] at this
        exact hS4Eq3 x this),
      by have := (hLoc (1 + 4 * L) (by omega)).2.2.2; omega, fun j hj => ?_⟩
    by_cases hlt : s3.mem (tok.edgeRecords + ei) + j < uIntBuf
    · have ht := (hLoc j hj).1 hlt
      refine ⟨hNotMutOfTag ht (by decide) (by decide), ?_⟩
      by_contra hc
      push Not at hc
      have := hTagL0 _ hc.1 hc.2
      rw [ht] at this; omega
    · exact ⟨hNotMutOfGe (by omega), Or.inr (by omega)⟩
  obtain ⟨s5, c5, heap2, newCanonVal, r5, hc5, hs5R4, hH2Lo, hH2Hi, hz5, hs5Regs, hLen5, hFr5,
      hFrTab5, hAcc5, hDisj5, hDisjTR5⟩ :=
    wireRefreshLen0_runs (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (wordExp := wordExp)
      (stretchPrec := stretchPrec) (refreshAccountsProc := refreshAccountsProc) (shift := shift)
      (negate := negate) (refreshOneProc := refreshOneProc) (divide := divide) (add := add)
      (sub := sub) (copy := copy) (isNeg := isNeg) (updateLen0Proc := updateLen0Proc)
      (root := root) (uIntBuf := uIntBuf) (editsPtr := editsPtr) (g := g) (l := l)
      (heap := heap) (heapSync := hS1) (ec0 := ec0) (cfg := cfg) (Rcore := Rcore) (p := p)
      (ω := ω) (mem0 := mem0) (mem := mem) (st := s4) (model := model) (tok := tok) (U := U)
      (B := B) (curE := F1) (canonVal := canonVal)
      hRefAccProc hRefOneProc hUpdLen0Proc hshift hdiv hadd hsub hneg hcopy hIsNegOk
      hRep0_keep hMeta0 hModelInv hRef hFreshMem hTrNfLe hBatchMem hSmallMem hFootLt hGLt hLLt
      hULeEd (by omega) (by omega) hLpos hPword hw18 hLevel0Meta hCanonExt
      ⟨(hs4Regs 4 (by decide) (by decide)).trans hs3R4, (hS4R 70 (by decide)).trans hr70,
        (hS4R 83 (by decide)).trans hr83, (hS4R 87 (by decide)).trans hr87,
        (hS4R 90 (by decide)).trans hr90, (hS4R 91 (by decide)).trans hr91,
        (hS4R 94 (by decide)).trans hr94⟩
      (fun a ha => by rw [hS4Eq3 a (hNotSlotOfGe (by omega))]; exact hz3 a ha)
      hS4Mem0 hS4MemFresh hOffSynced4 (by omega)
  -- the run and the facts of the end state
  have rAll : Runs w p ω (wireBranchBPrefixKFBL collectDel emitCuts (opTree 4) (opTree 1)
      (opTree 0) bind canonCopy isNeg zeroIns refreshAccountsProc updateLen0Proc) st .normal s5
      (c1 + (c2 + (c3 + (c4 + c5 + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, c1, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, c2, _, r2,
        runs_seq_iff.mpr (Or.inr ⟨s3, c3, _, r3,
          runs_seq_iff.mpr (Or.inr ⟨s4, c4, c5, r4, r5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hS5Eq4 (a : ℕ) (ha : a < hS1)
      (hNon : ∀ ei < tok.intCap, ei ∉ G0.E → a ≠ tok.slots + ei ∧
        a ≠ tok.edgeThresholds + ei ∧ a ≠ tok.edgeRecords + ei)
      (hLens : a < mem0 lm ∨ mem0 lm + ec0 * L ≤ a) : s5.mem a = s4.mem a := by
    have hNoRen (ei : ℕ) (hei : ei ∈ G0.E) :
        ¬ ∃ ei_old ∈ G0.E, Update.delete ei_old ∈ U_int ∧ tr.2.1 (tr.2.2.1 ei_old) = ei := by
      rintro ⟨ei_old, hold, hdel, heq⟩
      exact refreshed_newName_not_mem hFreshInv hRef hold hdel (heq ▸ hei)
    by_cases hT : tok.edgeThresholds ≤ a ∧ a < tok.edgeThresholds + tok.intCap
    · have hc : a - tok.edgeThresholds < tok.intCap := by omega
      have ha' : a = tok.edgeThresholds + (a - tok.edgeThresholds) := by omega
      by_cases hG : a - tok.edgeThresholds ∈ G0.E
      · rw [ha']; exact (hFrTab5 _ hc (hNoRen _ hG)).1
      · exact absurd ha' (hNon _ hc hG).2.1
    · by_cases hR : tok.edgeRecords ≤ a ∧ a < tok.edgeRecords + tok.intCap
      · have hc : a - tok.edgeRecords < tok.intCap := by omega
        have ha' : a = tok.edgeRecords + (a - tok.edgeRecords) := by omega
        by_cases hG : a - tok.edgeRecords ∈ G0.E
        · rw [ha']; exact (hFrTab5 _ hc (hNoRen _ hG)).2
        · exact absurd ha' (hNon _ hc hG).2.2
      · exact hFr5 a ha (by rintro (h | h) <;> contradiction) hLens
  refine ⟨s5, _, hS1, heap2, s3.mem, curTree', curTreeTok', offCnt', canonVal, newCanonVal, rAll,
    hs5R4, fun r hr => (hs5Regs r hr).trans (hS4R r hr), hS1Lo, hS1Hi, hH2Lo, hH2Hi, hz5, hPh3,
    hFoot3, fun ei heiF hdel => hDRec3 ei ((hDiff ei).mpr ⟨hdel, heiF⟩),
    fun ei hei hnot => ?_, fun a ha hne htag => ?_,
    fun a ha hNon hLens => (hS5Eq4 a ha hNon hLens).trans (hS4Eq3 a (fun e he =>
      (hNon e (hInsLt e he).1 (hInsLt e he).2).1)),
    fun e he => ?_, hLen5, hCanonExt, fun e he => ?_, hDisj5, hDisjTR5, ?_⟩
  · -- the records of the names off the tree
    have hc := hG0Cap ei hei
    exact (hKeepRec3 ei hei hnot).trans
      (hS2Mem0 _ (by omega) (by rw [hT13 ei hc]; decide) (by rw [hT13 ei hc]; decide)
        (by rw [hT13 ei hc]; decide) (by rw [hT13 ei hc]; decide))
  · -- the frame from the start to `memS1`
    have hS2 : s2.mem a = s1.mem a := by
      by_cases hlt : a < uIntBuf
      · exact hs2Fr a (hNotSlotOfTag (htag hlt).1)
      · exact hs2Fr a (hNotSlotOfGe (by omega))
    rw [hS3Eq2 a ha hne htag, hS2, hs1Mem, hStMem]
  · -- the slots of the inserted names
    have hlt := hSlotLtIns e he
    have ht : tok.tag (tok.slots + e) = 9 := hT9 e (hInsLt e he).1
    rw [hFr5 _ (by omega) (hNotMutOfTag ht (by decide) (by decide)) (by
      by_contra hc
      push Not at hc
      have := hTagL0 _ hc.1 hc.2
      rw [ht] at this; omega)]
    exact hs4Zero e he
  · -- the accounts after the refresh
    obtain ⟨hThr, hFwd, hgB, hlB, hflB, hdB, hFl, hGr, hLn, hAc, hIn, hOut⟩ := hAcc5 e he
    refine ⟨hThr, hFwd, hgB, hlB, hflB, hdB, hFl, hGr, hLn, hAc, fun hG => ?_, hOut⟩
    obtain ⟨h1, h2, h3, h4⟩ := hIn hG
    exact ⟨h1, h2, h3.trans (hRec43 _ (hG0Cap _ hG)), h4⟩
  · -- the cost
    have hPhi : Rtree.phi tok.treeHeap tok.treeTok s2.mem =
        Rtree.phi tok.treeHeap tok.treeTok mem0 := rfl
    rw [hPhi] at hc3
    rw [hULenEq] at hc2 hc4
    dsimp only [Rtree] at hc3 ⊢
    omega

end MinCostFlow.MinRatio
