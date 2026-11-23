module

public import MinCostFlow.MinRatio.WireChainCoreBranchA
public import MinCostFlow.MinRatio.WireChainCoreBranchAPreRunKFBL
import WordRAM.Tactic

/-!
# Branch A Step 3 execution under `KFBL` (`WireChainCoreBranchAPrefixRunKFBL`)

Executes Step 3 of Branch A starting from the state `s2` after `wireBranchASteps0To2KFBL_runs`:
- runs `wireBranchAPrefixStmt` (rename, compact `edgeThresholds`/`edgeRecords`/`newLen0`/
  `newRootGraph`, build `sortedEnds`), and
- aliases `reg 29 := mem[root + 14]` (`newRootGraph`) and `mem[levelMeta + d] := reg 29`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- Branch A Step 3 statement: `wireBranchAPrefixStmt` followed by aliasing
`mem[levelMeta + d] := mem[root + 14]`. -/
@[expose] def wireBranchAStep3StmtKFBL (renameProc compactProc sortedEndsProc : ℕ) : Stmt :=
  wireBranchAPrefixStmt renameProc compactProc sortedEndsProc ;;
  .assign 29 (.load (.bin .add (.reg 70) (.const 14))) ;;
  .store (.bin .add (.reg 83) (.reg 75)) (.reg 29)

theorem wireBranchAStep3StmtKFBL_noRand (renameProc compactProc sortedEndsProc : ℕ) :
    (wireBranchAStep3StmtKFBL renameProc compactProc sortedEndsProc).NoRand := by
  simp [wireBranchAStep3StmtKFBL, wireBranchAPrefixStmt, Stmt.NoRand]

set_option maxHeartbeats 600000 in
/-- Execute Branch A Step 3 (`s2 → s3`): rename, compact level-0 graph/lengths/edge-tables,
build `sortedEnds`, and alias `levelMeta[d] := newRootGraph`. -/
theorem wireBranchAStep3KFBL_runs
    {w L P m V psi k epsExp drainUnit vCap eCap
      renameProc compactProc sortedEndsProc copy dgInit
      root uIntBuf heap heap1 heapSync heap2 : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {p : Program} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {s2 : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B : ℤ}
    {gVec lVec : ℕ → ℝ}
    {curTree1 : PathTreeState}
    {curTreeTok1 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {newCanonVal : ℕ → PathEdgeValue}
    (hdPos : 0 < cfg.P.d) (hmPos : 0 < m) (hLpos : 0 < L) (heCapPos : 0 < eCap) (hw18 : 18 < 2 ^ w)
    (hvCapEq : vCap = model.extG.n) (heCapEq : eCap = tok.rootECap)
    (hRenProc : p.procs[renameProc]? = some level0RenameBody)
    (hCompProc : p.procs[compactProc]? = some (wireCompactLevel0Body copy dgInit))
    (hSortProc : p.procs[sortedEndsProc]? = some buildSortedEndsBody)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hDGInit :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
      ∀ vL eTriples, MeetsContract w p dgInit
        (dgInitFromListsContract w model.extG.n tok.rootECap G0'.compact vL eTriples))
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hG0'Cap :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      ∀ e ∈ ((model.chain.G 0).applyBatch tr.2.2.2.2).E, e < tok.rootECap ∧ e < tok.intCap)
    (hRef : RefreshBatch model.extG U)
    (hMemEq : ∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a)
    (hFreshMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        tr.2.1 tr.2.2.1 tr.2.2.2.1)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < uIntBuf)
    (hULeHeap : uIntBuf ≤ heap)
    (hHeaps :
      heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ heap1 ∧
      heap1 ≤ heapSync ∧ heapSync + 3 * L ≤ heap2)
    (hRegs2 :
      s2.regs 4 = heap2 ∧ s2.regs 70 = root ∧ s2.regs 73 = tok.handle ∧
      s2.regs 75 = cfg.P.d ∧ s2.regs 83 = solverLevelMetaAddr tok.table cfg.P.d)
    (hz2 : ZeroFrom s2.mem heap2)
    (hHeap0_2 : s2.mem heap = 0)
    (hEmptyPtrs2 : ∀ j < cfg.P.d + 1,
      s2.mem (heap + 1 + 12 * cfg.P.d + 2 * (cfg.P.d + 1) + j) =
        heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1))
    (hEmptyG2 : ∀ j < 4, s2.mem (heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + j) = 0)
    (hTreeRep1 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).rep tok.treeHeap curTree1 curTreeTok1 s2.mem)
    (hTreeFoot1 : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok1 a →
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
        (heap1 ≤ a ∧ a < heapSync))
    (hZeroSlots2 : ∀ j < tok.intCap, s2.mem (tok.slots + j) = 0)
    (hRootG2 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      DynGraphAt s2.mem tok.rootGraph model.extG.n tok.rootECap ((model.chain.G 0).applyBatch tr.2.2.2.2))
    (hLen0_2 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      EdgeValuesAt s2.mem (mem0 (solverLevelMetaAddr tok.table cfg.P.d)) 4 L P
        ((model.chain.G 0).applyBatch tr.2.2.2.2).E (fun e' => lVec (tr.2.2.1 e')))
    (hs2_frame_arr : ∀ a < heap + 1 + 12 * cfg.P.d, a ≠ root + 11 →
      tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 → tok.tag a ≠ 12 → tok.tag a ≠ 13 →
      tok.tag a ≠ 14 → tok.tag a ≠ 15 → tok.tag a ≠ 16 → tok.tag a ≠ 20 →
      tok.tag a ≠ 23 + cfg.P.d → (∀ j < cfg.P.d, tok.tag a ≠ 21 + j) → s2.mem a = mem a)
    (hCanon2 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0 := model.chain.G 0
      ∀ e ∈ model.extG.E,
        let ei := tr.2.1 e
        let v := newCanonVal ei
        PathIntAt s2.mem (s2.mem (tok.edgeThresholds + ei)) 4 L (detectorThreshold P cfg.ε (lVec e)) ∧
        PathEdgeAt s2.mem (s2.mem (tok.edgeRecords + ei)) 4 L (some v) ∧
        v.forward = true ∧ |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B ∧
        (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (v.originalGradient : ℝ) / (2 : ℝ) ^ P = gVec e ∧
        (v.length : ℝ) / (2 : ℝ) ^ P = lVec e ∧
        (∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
          v.detector = acc - detectorThreshold P cfg.ε (lVec e)) ∧
        (ei ∈ G0.E →
          s2.mem (tok.edgeThresholds + ei) = mem0 (tok.edgeThresholds + ei) ∧
          ((ei ∈ model.chain.toTreeChain.chainTree.E →
              heap1 ≤ s2.mem (tok.edgeRecords + ei) ∧
              s2.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heapSync ∧
              ∀ a, s2.mem (tok.edgeRecords + ei) ≤ a →
                a < s2.mem (tok.edgeRecords + ei) + (2 + 4 * L) →
                ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok1 a) ∧
           (ei ∉ model.chain.toTreeChain.chainTree.E →
              s2.mem (tok.edgeRecords + ei) = mem0 (tok.edgeRecords + ei)))) ∧
        (ei ∉ G0.E →
          heapSync + 3 * L ≤ s2.mem (tok.edgeThresholds + ei) ∧
          s2.mem (tok.edgeThresholds + ei) + L ≤ heap2 ∧
          heapSync + 3 * L ≤ s2.mem (tok.edgeRecords + ei) ∧
          s2.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heap2))
    (hOffDisj2 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
      ∀ ei₁ ∈ G0'.E, ∀ ei₂ ∈ G0'.E, ei₁ ≠ ei₂ →
        s2.mem (tok.edgeRecords + ei₁) + (2 + 4 * L) ≤ s2.mem (tok.edgeRecords + ei₂) ∨
        s2.mem (tok.edgeRecords + ei₂) + (2 + 4 * L) ≤ s2.mem (tok.edgeRecords + ei₁))
    (hThrOffDisj2 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0 := model.chain.G 0
      let G0' := G0.applyBatch tr.2.2.2.2
      ∀ ei₁ ∈ G0'.E, ei₁ ∉ G0.E → ∀ ei₂ ∈ G0'.E, ei₂ ∉ G0.E →
        s2.mem (tok.edgeThresholds + ei₁) + L ≤ s2.mem (tok.edgeRecords + ei₂) ∨
        s2.mem (tok.edgeRecords + ei₂) + (2 + 4 * L) ≤ s2.mem (tok.edgeThresholds + ei₁))
    (hPrefRoom :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
      heap2 + 2 * tok.intCap + wireCompactLevel0Space model.extG.n tok.rootECap L G0'.m +
        (1 + 4 * model.extG.n + 2 * tok.rootECap) < 2 ^ w) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let d := cfg.P.d
    let cnt := d + 1
    let arrBase := heap + 1 + 12 * d
    let emptyPtrs := arrBase + 2 * cnt
    let emptyGraphPtr := arrBase + 3 * cnt
    let levelMeta := solverLevelMetaAddr tok.table d
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let G0 := model.chain.G 0
    let G0' := G0.applyBatch tr.2.2.2.2
    let ℓ' := fun e' => lVec (tr.2.2.1 e')
    let ordW := 1 + 2 * vCap + 2 * G0'.compact.m
    ∃ (out : State) (cost newLen0 newRootGraph ordPtr0 heap3 : ℕ),
      Runs w p ω (wireBranchAStep3StmtKFBL renameProc compactProc sortedEndsProc) s2 .normal out cost ∧
      cost ≤ (70 * tok.intCap + 40 * m + 80) + wireCompactLevel0Cost vCap eCap tok.intCap L G0'.m +
        (150 * eCap + 60 * vCap + 120) + 165 ∧
      heap2 ≤ newLen0 ∧ newLen0 + eCap * L ≤ newRootGraph ∧
      newRootGraph + dynGraphSize vCap eCap ≤ ordPtr0 ∧ ordPtr0 + ordW ≤ heap3 ∧
      heap3 ≤ heap2 + 2 * tok.intCap + wireCompactLevel0Space vCap eCap L G0'.m + (1 + 4 * vCap + 2 * eCap) ∧
      out.regs 4 = heap3 ∧ out.regs 28 = newLen0 ∧ out.regs 29 = newRootGraph ∧ out.regs 30 = ordPtr0 ∧
      ZeroFrom out.mem heap3 ∧ (∀ r, 70 ≤ r → out.regs r = s2.regs r) ∧
      out.mem heap = 0 ∧
      (∀ j < cnt, out.mem (emptyPtrs + j) = emptyGraphPtr) ∧
      (∀ j < 4, out.mem (emptyGraphPtr + j) = 0) ∧
      FreshTablesAt out.mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        (level0E2I true G0' tr.2.1) (level0I2E true G0' tr.2.2.1) (level0NF true G0' tr.2.2.2.1) ∧
      out.mem (root + 14) = newRootGraph ∧ out.mem (root + 11) = 0 ∧
      out.mem levelMeta = newLen0 ∧ out.mem (levelMeta + d) = newRootGraph ∧
      DynGraphAt out.mem newRootGraph vCap eCap G0'.compact ∧
      EdgeValuesAt out.mem newLen0 4 L P G0'.compact.E (fun j => ℓ' (compactUnrank G0'.E j)) ∧
      OrdListAt out.mem ordPtr0 (sortedEnds G0'.compact) ordW ∧
      (∀ t < ordW, out.mem (ordPtr0 + t) < 2 ^ w) ∧
      (∀ e < tok.intCap, out.mem (tok.slots + e) = 0) ∧
      (∀ e < tok.intCap, out.mem (tok.inOffReady + e) = 0) ∧
      OffReadyInv out.mem 0 tok.offReadyList tok.inOffReady tok.intCap ∧
      Rtree.rep tok.treeHeap curTree1 curTreeTok1 out.mem ∧
      Rtree.phi tok.treeHeap curTreeTok1 out.mem = Rtree.phi tok.treeHeap curTreeTok1 s2.mem ∧
      (∀ e ∈ model.extG.E,
        let eiOld := tr.2.1 e
        let eiNew := level0E2I true G0' tr.2.1 e
        let v := newCanonVal eiOld
        eiNew < G0'.m ∧ compactUnrank G0'.E eiNew = eiOld ∧
        PathIntAt out.mem (out.mem (tok.edgeThresholds + eiNew)) 4 L (detectorThreshold P cfg.ε (lVec e)) ∧
        PathEdgeAt out.mem (out.mem (tok.edgeRecords + eiNew)) 4 L (some v) ∧
        v.forward = true ∧ |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B ∧
        (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (v.originalGradient : ℝ) / (2 : ℝ) ^ P = gVec e ∧
        (v.length : ℝ) / (2 : ℝ) ^ P = lVec e ∧
        (∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
          v.detector = acc - detectorThreshold P cfg.ε (lVec e)) ∧
        (eiOld ∈ G0.E →
          out.mem (tok.edgeThresholds + eiNew) = mem0 (tok.edgeThresholds + eiOld) ∧
          ((eiOld ∈ model.chain.toTreeChain.chainTree.E →
              heap1 ≤ out.mem (tok.edgeRecords + eiNew) ∧
              out.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) ≤ heapSync ∧
              ∀ a, out.mem (tok.edgeRecords + eiNew) ≤ a →
                a < out.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) →
                ¬ Rtree.foot tok.treeHeap curTreeTok1 a) ∧
           (eiOld ∉ model.chain.toTreeChain.chainTree.E →
              out.mem (tok.edgeRecords + eiNew) = mem0 (tok.edgeRecords + eiOld)))) ∧
        (eiOld ∉ G0.E →
          heapSync + 3 * L ≤ out.mem (tok.edgeThresholds + eiNew) ∧
          out.mem (tok.edgeThresholds + eiNew) + L ≤ heap2 ∧
          heapSync + 3 * L ≤ out.mem (tok.edgeRecords + eiNew) ∧
          out.mem (tok.edgeRecords + eiNew) + (2 + 4 * L) ≤ heap2)) ∧
      (∀ e₁ ∈ model.extG.E, ∀ e₂ ∈ model.extG.E, e₁ ≠ e₂ →
        out.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₁) + (2 + 4 * L) ≤
          out.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) ∨
        out.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) + (2 + 4 * L) ≤
          out.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₁)) ∧
      (∀ e₁ ∈ model.extG.E, tr.2.1 e₁ ∉ G0.E → ∀ e₂ ∈ model.extG.E, tr.2.1 e₂ ∉ G0.E →
        out.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e₁) + L ≤
          out.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) ∨
        out.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) + (2 + 4 * L) ≤
          out.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e₁)) ∧
      (∀ a < arrBase, a ≠ root + 11 → a ≠ root + 14 →
        tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 →
        tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 →
        tok.tag a ≠ 12 → tok.tag a ≠ 13 → tok.tag a ≠ 14 → tok.tag a ≠ 15 →
        tok.tag a ≠ 16 → tok.tag a ≠ 20 → tok.tag a ≠ 22 + d → tok.tag a ≠ 23 + d →
        (∀ j < d, tok.tag a ≠ 21 + j) → out.mem a = mem a) := by
  dsimp only
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let G0 := model.chain.G 0
  let G0' := G0.applyBatch tr.2.2.2.2
  have hMeta0_keep := hMeta0
  obtain ⟨hRootDir0, _, hNumHdr0, hInitPar0, hFreshInv0, _, _, ⟨_, hIntCapPos, _, _⟩,
    _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, hT2, _, _, _, hT6, hT7, hT8, hT9, _, _, hT12, hT13, hT14, hT15,
    hT16, hT1718, _, hT20, _⟩ := hTags0
  obtain ⟨_, _, _, _, hTagMeta0, _⟩ := hMeta0
  obtain ⟨hH1Lo, hSyncLo, hH2Lo⟩ := hHeaps
  obtain ⟨hr4, hr70, hr73, hr75, hr83⟩ := hRegs2
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hTagLen0 : ∀ a, mem0 (solverLevelMetaAddr tok.table cfg.P.d) ≤ a →
      a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) + eCap * L → tok.tag a = 23 + cfg.P.d :=
    (SolverLevelMetaAt.atCaps hMeta0_keep hCaps0 0 hdPos).2.2.2.1
  obtain ⟨hTr1Eq, hFreshTr, _, hDichUnch, hDichRep⟩ := refreshBatch_edge_dichotomy hFreshInv0 hRef
  have hs2_eq_mem0 {a : ℕ} (ht : tok.tag a ≠ 0) (h6 : tok.tag a ≠ 6) (h7 : tok.tag a ≠ 7)
      (h8 : tok.tag a ≠ 8) (h9 : tok.tag a ≠ 9) (h10 : tok.tag a ≠ 10) (h11 : tok.tag a ≠ 11)
      (h12 : tok.tag a ≠ 12) (h13 : tok.tag a ≠ 13) (h14 : tok.tag a ≠ 14) (h15 : tok.tag a ≠ 15)
      (h16 : tok.tag a ≠ 16) (h20 : tok.tag a ≠ 20) (h23 : tok.tag a ≠ 23 + cfg.P.d)
      (hc : ∀ j < cfg.P.d, tok.tag a ≠ 21 + j) (hne11 : a ≠ root + 11) : s2.mem a = mem0 a :=
    (hs2_frame_arr a (by have := htagLt ht; omega) hne11 h9 h10 h11 h12 h13 h14 h15 h16 h20
      h23 hc).trans (hMemEq a (htagLt ht) h6 h7 h8)
  have hs2_eq_mem {a : ℕ} (ha : a < uIntBuf) (ht : tok.tag a = 6 ∨ tok.tag a = 7 ∨ tok.tag a = 8) :
      s2.mem a = mem a := by
    have hne11 : a ≠ root + 11 := fun h => by rw [h, hT1 11 (by omega)] at ht; rcases ht with h' | h' | h' <;> omega
    exact hs2_frame_arr a (by omega) hne11
      (by rcases ht with h' | h' | h' <;> omega) (by rcases ht with h' | h' | h' <;> omega)
      (by rcases ht with h' | h' | h' <;> omega) (by rcases ht with h' | h' | h' <;> omega)
      (by rcases ht with h' | h' | h' <;> omega) (by rcases ht with h' | h' | h' <;> omega)
      (by rcases ht with h' | h' | h' <;> omega) (by rcases ht with h' | h' | h' <;> omega)
      (by rcases ht with h' | h' | h' <;> omega) (by rcases ht with h' | h' | h' <;> omega)
      (fun j _ => by rcases ht with h' | h' | h' <;> omega)
  have hTagSep (a b va vb : ℕ) (ha : tok.tag a = va) (hb : tok.tag b = vb) (hne : va ≠ vb) : a ≠ b :=
    fun h => hne (ha.symm.trans (h ▸ hb))
  have hDisjTag (b1 n1 v1 b2 n2 v2 : ℕ) (hn1 : 0 < n1) (hn2 : 0 < n2)
      (h1 : ∀ i < n1, tok.tag (b1 + i) = v1)
      (h2 : ∀ i < n2, tok.tag (b2 + i) = v2) (hne : v1 ≠ v2) : b1 + n1 ≤ b2 ∨ b2 + n2 ≤ b1 := by
    by_contra h; push Not at h
    rcases le_total b1 b2 with hle | hle
    · exact hne ((h1 (b2 - b1) (by omega)).symm.trans
        (by rw [show b1 + (b2 - b1) = b2 by omega]; simpa using h2 0 hn2))
    · exact hne.symm ((h2 (b1 - b2) (by omega)).symm.trans
        (by rw [show b2 + (b1 - b2) = b1 by omega]; simpa using h1 0 hn1))
  have hDisjTagR (b1 n1 v1 b2 n2 v2 : ℕ) (hn1 : 0 < n1) (hn2 : 0 < n2)
      (h1 : ∀ a, b1 ≤ a → a < b1 + n1 → tok.tag a = v1)
      (h2 : ∀ i < n2, tok.tag (b2 + i) = v2) (hne : v1 ≠ v2) : b1 + n1 ≤ b2 ∨ b2 + n2 ≤ b1 :=
    hDisjTag b1 n1 v1 b2 n2 v2 hn1 hn2 (fun i hi => h1 (b1 + i) (by omega) (by omega)) h2 hne
  have hDisjTagSingle (c vc b n vb : ℕ) (hc : tok.tag c = vc) (hb : ∀ i < n, tok.tag (b + i) = vb)
      (hne : vc ≠ vb) : c < b ∨ b + n ≤ c := by
    by_contra h; push Not at h
    exact hne (hc.symm.trans (by have := hb (c - b) (by omega); rwa [show b + (c - b) = c by omega] at this))
  have hDisjTagSingleR (b n vb c vc : ℕ) (hb : ∀ a, b ≤ a → a < b + n → tok.tag a = vb)
      (hc : tok.tag c = vc) (hne : vb ≠ vc) : b + n ≤ c ∨ c < b :=
    (hDisjTagSingle c vc b n vb hc (fun i hi => hb (b + i) (by omega) (by omega)) hne.symm).symm
  have hECapLPos : 0 < eCap * L := Nat.mul_pos heCapPos hLpos
  have hDGPos : 0 < dynGraphSize model.extG.n tok.rootECap := by unfold dynGraphSize; omega
  have hRoot2 : SolverRootDirAt s2.mem root tok.handle tok.table tok.levelsEnd tok.forward
      tok.inverse tok.freshCounter tok.slots tok.names tok.slotThresholds tok.edgeThresholds
      tok.edgeRecords (s2.mem (root + 11)) tok.offReadyList tok.inOffReady tok.rootGraph tok.intCap := by
    intro j hj
    have hj16 : j < 16 := by simpa using hj
    by_cases h11 : j = 11
    · subst h11; simp
    · rw [hs2_eq_mem0 (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide)
        (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide)
        (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide)
        (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide)
        (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; omega)
        (fun r _ => by rw [hT1 j hj16]; omega) (by omega)]
      have h0 := hRootDir0 j hj
      have : [tok.handle, tok.table, tok.levelsEnd, tok.forward, tok.inverse, tok.freshCounter,
          tok.slots, tok.names, tok.slotThresholds, tok.edgeThresholds, tok.edgeRecords,
          s2.mem (root + 11), tok.offReadyList, tok.inOffReady, tok.rootGraph, tok.intCap][j] =
        [tok.handle, tok.table, tok.levelsEnd, tok.forward, tok.inverse, tok.freshCounter,
          tok.slots, tok.names, tok.slotThresholds, tok.edgeThresholds, tok.edgeRecords,
          tok.offReadyCount, tok.offReadyList, tok.inOffReady, tok.rootGraph, tok.intCap][j] := by
        interval_cases j <;> first | rfl | contradiction
      exact h0.trans this.symm
  have hFresh2 : FreshTablesAt s2.mem tok.forward tok.inverse tok.freshCounter m tok.intCap
      tr.2.1 tr.2.2.1 tr.2.2.2.1 :=
    ⟨(hs2_eq_mem (htagLt (by rw [hT6]; decide)) (Or.inl hT6)).trans hFreshMem.1,
     fun e he => (hs2_eq_mem (htagLt (by rw [hT7 e he]; decide)) (Or.inr (Or.inl (hT7 e he)))).trans (hFreshMem.2.1 e he),
     fun j hj => (hs2_eq_mem (htagLt (by rw [hT8 j hj]; decide)) (Or.inr (Or.inr (hT8 j hj)))).trans (hFreshMem.2.2 j hj)⟩
  have hTagLM0 : tok.tag (solverLevelMetaAddr tok.table cfg.P.d) = 22 + cfg.P.d := by
    simpa using hTagMeta0 0 (by omega)
  obtain ⟨s3a, cPref, rPref, hcPref, hs3a_4, hs3a_28, _, hs3a_30, hs3a_ge70, hFresh3a,
      hTab3a, hLen3a, hRG3a, _, hOrd3a, hOrdW3a, hOrdEnd3a, hR14_3a, hR11_3a, hLM0_3a, _,
      hZeroIn3a, hOffInv3a, hz3a, hs3a_frame⟩ :=
    wireBranchAPrefix_runs (w := w) (L := L) (P := P) (m := m) (n := model.extG.n)
      (rootECap := tok.rootECap) (oldLenECap := eCap) (intCap := tok.intCap) (d := cfg.P.d)
      (root := root) (handle := tok.handle) (table := tok.table) (levelsEnd := tok.levelsEnd)
      (forward := tok.forward) (inverse := tok.inverse) (freshCounter := tok.freshCounter)
      (slots := tok.slots) (names := tok.names) (slotThresholds := tok.slotThresholds)
      (edgeThresholds := tok.edgeThresholds) (edgeRecords := tok.edgeRecords)
      (offReadyCount := s2.mem (root + 11)) (offReadyList := tok.offReadyList)
      (inOffReady := tok.inOffReady) (oldRootGraph := tok.rootGraph)
      (oldLen0 := mem0 (solverLevelMetaAddr tok.table cfg.P.d))
      (heap0 := heap2) (renameProc := renameProc) (compactProc := compactProc)
      (sortedEndsProc := sortedEndsProc) (copyWords := copy) (dgInit := dgInit)
      (G0' := G0') (oldℓ := fun e' => lVec (tr.2.2.1 e')) (e2i := tr.2.1) (i2e := tr.2.2.1)
      (nf := tr.2.2.2.1) (p := p) (ω := ω) (st := s2)
      hRenProc hCompProc hSortProc hcopy hDGInit hr70 hr73 hr75 hr83 hr4 hRoot2
      ((hs2_eq_mem0 (by rw [hT2 5 (by omega)]; decide) (by rw [hT2 5 (by omega)]; decide)
        (by rw [hT2 5 (by omega)]; decide) (by rw [hT2 5 (by omega)]; decide)
        (by rw [hT2 5 (by omega)]; decide) (by rw [hT2 5 (by omega)]; decide)
        (by rw [hT2 5 (by omega)]; decide) (by rw [hT2 5 (by omega)]; decide)
        (by rw [hT2 5 (by omega)]; decide) (by rw [hT2 5 (by omega)]; decide)
        (by rw [hT2 5 (by omega)]; decide) (by rw [hT2 5 (by omega)]; decide)
        (by rw [hT2 5 (by omega)]; decide) (by rw [hT2 5 (by omega)]; omega)
        (fun _ _ => by rw [hT2 5 (by omega)]; omega)
        (hTagSep _ _ _ _ (hT2 5 (by omega)) (hT1 11 (by omega)) (by decide))).trans
        (by simpa using hNumHdr0 0 (by simp)))
      ((hs2_eq_mem0 (by rw [hT2 9 (by omega)]; decide) (by rw [hT2 9 (by omega)]; decide)
        (by rw [hT2 9 (by omega)]; decide) (by rw [hT2 9 (by omega)]; decide)
        (by rw [hT2 9 (by omega)]; decide) (by rw [hT2 9 (by omega)]; decide)
        (by rw [hT2 9 (by omega)]; decide) (by rw [hT2 9 (by omega)]; decide)
        (by rw [hT2 9 (by omega)]; decide) (by rw [hT2 9 (by omega)]; decide)
        (by rw [hT2 9 (by omega)]; decide) (by rw [hT2 9 (by omega)]; decide)
        (by rw [hT2 9 (by omega)]; decide) (by rw [hT2 9 (by omega)]; omega)
        (fun _ _ => by rw [hT2 9 (by omega)]; omega)
        (hTagSep _ _ _ _ (hT2 9 (by omega)) (hT1 11 (by omega)) (by decide))).trans
        (by simpa using hInitPar0 0 (by simp)))
      ((hs2_eq_mem0 (by rw [hT2 11 (by omega)]; decide) (by rw [hT2 11 (by omega)]; decide)
        (by rw [hT2 11 (by omega)]; decide) (by rw [hT2 11 (by omega)]; decide)
        (by rw [hT2 11 (by omega)]; decide) (by rw [hT2 11 (by omega)]; decide)
        (by rw [hT2 11 (by omega)]; decide) (by rw [hT2 11 (by omega)]; decide)
        (by rw [hT2 11 (by omega)]; decide) (by rw [hT2 11 (by omega)]; decide)
        (by rw [hT2 11 (by omega)]; decide) (by rw [hT2 11 (by omega)]; decide)
        (by rw [hT2 11 (by omega)]; decide) (by rw [hT2 11 (by omega)]; omega)
        (fun _ _ => by rw [hT2 11 (by omega)]; omega)
        (hTagSep _ _ _ _ (hT2 11 (by omega)) (hT1 11 (by omega)) (by decide))).trans
        (by simpa using hInitPar0 2 (by simp)))
      (hs2_eq_mem0 (by rw [hTagLM0]; omega) (by rw [hTagLM0]; omega) (by rw [hTagLM0]; omega)
        (by rw [hTagLM0]; omega) (by rw [hTagLM0]; omega) (by rw [hTagLM0]; omega)
        (by rw [hTagLM0]; omega) (by rw [hTagLM0]; omega) (by rw [hTagLM0]; omega)
        (by rw [hTagLM0]; omega) (by rw [hTagLM0]; omega) (by rw [hTagLM0]; omega)
        (by rw [hTagLM0]; omega) (by rw [hTagLM0]; omega) (fun _ _ => by rw [hTagLM0]; omega)
        (hTagSep _ _ _ _ hTagLM0 (hT1 11 (by omega)) (by omega)))
      hFresh2 hRootG2 hLen0_2 hG0'Cap (fun e he => heCapEq.symm ▸ (hG0'Cap e he).1) hdPos hw18
      ⟨by have := htagLt (by rw [hT1 15 (by omega)]; decide); omega,
       by have := htagLt (by rw [hT2 17 (by omega)]; decide); omega,
       by have := htagLt (by rw [hTagMeta0 (2 * cfg.P.d - 1) (by omega)]; omega); omega,
       by have h4 : 4 ≤ dynGraphSize model.extG.n tok.rootECap := by unfold dynGraphSize; omega
          have := htagLt (by rw [hT20 (tok.rootGraph + dynGraphSize model.extG.n tok.rootECap - 1) (by omega) (by omega)]; decide); omega,
       by have := htagLt (by rw [hTagLen0 (mem0 (solverLevelMetaAddr tok.table cfg.P.d) + eCap * L - 1) (by omega) (by omega)]; omega); omega,
       by have := htagLt (by rw [hT7 (m - 1) (by omega)]; decide); omega,
       by have := htagLt (by rw [hT8 (tok.intCap - 1) (by omega)]; decide); omega,
       by have := htagLt (by rw [hT6]; decide); omega,
       by have := htagLt (by rw [hT12 (tok.intCap - 1) (by omega)]; decide); omega,
       by have := htagLt (by rw [hT13 (tok.intCap - 1) (by omega)]; decide); omega,
       by have := htagLt (by rw [hT15 (tok.intCap - 1) (by omega)]; decide); omega⟩
      ⟨hDisjTag _ _ 7 _ _ 8 hmPos hIntCapPos hT7 hT8 (by decide),
       hDisjTagSingle _ 6 _ _ 7 hT6 hT7 (by decide), hDisjTagSingle _ 6 _ _ 8 hT6 hT8 (by decide),
       hDisjTag _ _ 1 _ _ 7 (by decide) hmPos hT1 hT7 (by decide),
       hDisjTag _ _ 1 _ _ 8 (by decide) hIntCapPos hT1 hT8 (by decide),
       (hDisjTagSingle _ 6 _ _ 1 hT6 hT1 (by decide)).symm,
       hDisjTag _ _ 2 _ _ 7 (by decide) hmPos hT2 hT7 (by decide),
       hDisjTag _ _ 2 _ _ 8 (by decide) hIntCapPos hT2 hT8 (by decide),
       (hDisjTagSingle _ 6 _ _ 2 hT6 hT2 (by decide)).symm,
       hDisjTag _ _ (22 + cfg.P.d) _ _ 7 (by omega) hmPos hTagMeta0 hT7 (by omega),
       hDisjTag _ _ (22 + cfg.P.d) _ _ 8 (by omega) hIntCapPos hTagMeta0 hT8 (by omega),
       (hDisjTagSingle _ 6 _ _ (22 + cfg.P.d) hT6 hTagMeta0 (by omega)).symm,
       hDisjTagR _ _ 20 _ _ 7 hDGPos hmPos hT20 hT7 (by decide),
       hDisjTagR _ _ 20 _ _ 8 hDGPos hIntCapPos hT20 hT8 (by decide),
       hDisjTagSingleR _ _ 20 _ 6 hT20 hT6 (by decide),
       hDisjTagR _ _ (23 + cfg.P.d) _ _ 7 hECapLPos hmPos hTagLen0 hT7 (by omega),
       hDisjTagR _ _ (23 + cfg.P.d) _ _ 8 hECapLPos hIntCapPos hTagLen0 hT8 (by omega),
       hDisjTagSingleR _ _ (23 + cfg.P.d) _ 6 hTagLen0 hT6 (by omega),
       hDisjTag _ _ 12 _ _ 7 hIntCapPos hmPos hT12 hT7 (by decide),
       hDisjTag _ _ 12 _ _ 8 hIntCapPos hIntCapPos hT12 hT8 (by decide),
       (hDisjTagSingle _ 6 _ _ 12 hT6 hT12 (by decide)).symm,
       hDisjTag _ _ 13 _ _ 7 hIntCapPos hmPos hT13 hT7 (by decide),
       hDisjTag _ _ 13 _ _ 8 hIntCapPos hIntCapPos hT13 hT8 (by decide),
       (hDisjTagSingle _ 6 _ _ 13 hT6 hT13 (by decide)).symm,
       hDisjTag _ _ 15 _ _ 7 hIntCapPos hmPos hT15 hT7 (by decide),
       hDisjTag _ _ 15 _ _ 8 hIntCapPos hIntCapPos hT15 hT8 (by decide),
       (hDisjTagSingle _ 6 _ _ 15 hT6 hT15 (by decide)).symm,
       hDisjTag _ _ 14 _ _ 7 hIntCapPos hmPos hT14 hT7 (by decide),
       hDisjTag _ _ 14 _ _ 8 hIntCapPos hIntCapPos hT14 hT8 (by decide),
       (hDisjTagSingle _ 6 _ _ 14 hT6 hT14 (by decide)).symm,
       hDisjTag _ _ 12 _ _ 13 hIntCapPos hIntCapPos hT12 hT13 (by decide),
       hDisjTag _ _ 12 _ _ 15 hIntCapPos hIntCapPos hT12 hT15 (by decide),
       hDisjTag _ _ 13 _ _ 15 hIntCapPos hIntCapPos hT13 hT15 (by decide),
       hDisjTag _ _ 1 _ _ (22 + cfg.P.d) (by decide) (by omega) hT1 hTagMeta0 (by omega),
       hDisjTag _ _ 1 _ _ 12 (by decide) hIntCapPos hT1 hT12 (by decide),
       hDisjTag _ _ 1 _ _ 13 (by decide) hIntCapPos hT1 hT13 (by decide),
       hDisjTag _ _ 1 _ _ 15 (by decide) hIntCapPos hT1 hT15 (by decide),
       hDisjTag _ _ (22 + cfg.P.d) _ _ 12 (by omega) hIntCapPos hTagMeta0 hT12 (by omega),
       hDisjTag _ _ (22 + cfg.P.d) _ _ 13 (by omega) hIntCapPos hTagMeta0 hT13 (by omega),
       hDisjTag _ _ (22 + cfg.P.d) _ _ 15 (by omega) hIntCapPos hTagMeta0 hT15 (by omega),
       hDisjTagR _ _ (23 + cfg.P.d) _ _ 12 hECapLPos hIntCapPos hTagLen0 hT12 (by omega),
       hDisjTagR _ _ (23 + cfg.P.d) _ _ 13 hECapLPos hIntCapPos hTagLen0 hT13 (by omega),
       hDisjTagR _ _ 20 _ _ 12 hDGPos hIntCapPos hT20 hT12 (by decide),
       hDisjTagR _ _ 20 _ _ 13 hDGPos hIntCapPos hT20 hT13 (by decide)⟩
      hz2 hPrefRoom
  let capP := min tok.rootECap tok.intCap
  have hCapPLe : capP ≤ tok.intCap := Nat.min_le_right _ _
  let newLen0 := heap2 + 2 * capP
  let newRootGraph := newLen0 + tok.rootECap * L + 3 * G0'.m
  let ordPtr0 := newLen0 + wireCompactLevel0Space model.extG.n tok.rootECap L G0'.m
  let heap3 := ordPtr0 + 1 + 4 * model.extG.n + 2 * tok.rootECap
  have hNRGLtW : newRootGraph < 2 ^ w := by
    dsimp only [newRootGraph, newLen0, wireCompactLevel0Space, G0', G0, tr] at hPrefRoom ⊢; omega
  let lm := solverLevelMetaAddr tok.table cfg.P.d
  let s3b : State := { s3a with regs := Function.update s3a.regs 29 newRootGraph }
  let s3 : State := { s3b with mem := Function.update s3b.mem (lm + cfg.P.d) newRootGraph }
  have r3b : Runs w p ω (.assign 29 (.load (.bin .add (.reg 70) (.const 14)))) s3a .normal s3b 5 :=
    runs_assign_iff.mpr ⟨newRootGraph, by
      simp [Expr.eval, BinOp.eval, hs3a_ge70 70 (by decide), hr70, show 14 < 2 ^ w by omega,
        show root + 14 < 2 ^ w by have := htagLt (by rw [hT1 14 (by omega)]; decide); omega, hR14_3a]; rfl,
      rfl, rfl, rfl⟩
  have r3c : Runs w p ω (.store (.bin .add (.reg 83) (.reg 75)) (.reg 29)) s3b .normal s3 5 :=
    runs_store_iff.mpr ⟨lm + cfg.P.d, newRootGraph, by
      have hW : lm + cfg.P.d < 2 ^ w := by have := htagLt (by rw [hTagMeta0 cfg.P.d (by omega)]; omega); omega
      simp [Expr.eval, BinOp.eval, s3b, hs3a_ge70 83 (by decide), hr83, hs3a_ge70 75 (by decide), hr75,
        lm, hW],
      by simp [Expr.eval, s3b], rfl, rfl, rfl⟩
  have hs3_eq_s3a (a : ℕ) (hne : a ≠ lm + cfg.P.d) : s3.mem a = s3a.mem a := by
    simp [s3, s3b, Function.update_of_ne hne]
  have hs3_eq_s2 (a : ℕ) (ha : a < heap2) (h6 : tok.tag a ≠ 6) (h7 : tok.tag a ≠ 7)
      (h8 : tok.tag a ≠ 8) (h12 : tok.tag a ≠ 12) (h13 : tok.tag a ≠ 13)
      (h14 : tok.tag a ≠ 14) (h15 : tok.tag a ≠ 15) (h22 : tok.tag a ≠ 22 + cfg.P.d)
      (hne11 : a ≠ root + 11) (hne14 : a ≠ root + 14) : s3.mem a = s2.mem a := by
    have hneLMd : a ≠ lm + cfg.P.d := fun h => h22 (by rw [h]; exact hTagMeta0 cfg.P.d (by omega))
    rw [hs3_eq_s3a a hneLMd]
    refine hs3a_frame a ha
      (fun ⟨h1, h2⟩ => h7 (by have := hT7 (a - tok.forward) (by omega); rwa [show tok.forward + (a - tok.forward) = a by omega] at this))
      (fun ⟨h1, h2⟩ => h8 (by have := hT8 (a - tok.inverse) (by omega); rwa [show tok.inverse + (a - tok.inverse) = a by omega] at this))
      (fun h => h6 (h ▸ hT6)) (fun hm => ?_)
    rcases hm with rfl | rfl | rfl | rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hne11 rfl
    · exact hne14 rfl
    · exact h22 (by simpa using hTagMeta0 0 (by omega))
    · exact hneLMd rfl
    · exact h12 (by have := hT12 (a - tok.edgeThresholds) (by omega); rwa [show tok.edgeThresholds + (a - tok.edgeThresholds) = a by omega] at this)
    · exact h13 (by have := hT13 (a - tok.edgeRecords) (by omega); rwa [show tok.edgeRecords + (a - tok.edgeRecords) = a by omega] at this)
    · exact h14 (by have := hT14 (a - tok.offReadyList) (by omega); rwa [show tok.offReadyList + (a - tok.offReadyList) = a by omega] at this)
    · exact h15 (by have := hT15 (a - tok.inOffReady) (by omega); rwa [show tok.inOffReady + (a - tok.inOffReady) = a by omega] at this)
  have hs3_eq_s2_ge (a : ℕ) (ha1 : heap ≤ a) (ha2 : a < heap2) : s3.mem a = s2.mem a := by
    have hneT (v : ℕ) (hv : v ≠ 0) : tok.tag a ≠ v := fun h => absurd (htagLt (by rw [h]; exact hv)) (by omega)
    exact hs3_eq_s2 a ha2 (hneT 6 (by decide)) (hneT 7 (by decide)) (hneT 8 (by decide))
      (hneT 12 (by decide)) (hneT 13 (by decide)) (hneT 14 (by decide)) (hneT 15 (by decide))
      (hneT (22 + cfg.P.d) (by omega))
      (by have := htagLt (by rw [hT1 11 (by omega)]; decide); omega)
      (by have := htagLt (by rw [hT1 14 (by omega)]; decide); omega)
  have hLMdLtHeap : lm + cfg.P.d < heap2 := by
    have := htagLt (by rw [hTagMeta0 cfg.P.d (by omega)]; omega); omega
  have hTreeAgree3 : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok1 a →
      s3.mem a = s2.mem a := fun a ha => by
    rcases hTreeFoot1 a ha with h0 | ⟨hlo, hhi⟩
    · have ht := hT16 a h0
      exact hs3_eq_s2 a (by have := htagLt (by rw [ht]; decide); omega)
        (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide)
        (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; omega)
        (hTagSep _ _ _ _ ht (hT1 11 (by omega)) (by decide))
        (hTagSep _ _ _ _ ht (hT1 14 (by omega)) (by decide))
    · exact hs3_eq_s2_ge a (by omega) (by omega)
  have hTreeLoc3 := (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC)
    tok.treeHeap curTree1 curTreeTok1 s2.mem s3.mem (fun a ha => (hTreeAgree3 a ha).symm)
  refine ⟨s3, cPref + (5 + 5 + 1) + 1, newLen0, newRootGraph, ordPtr0, heap3,
    runs_seq_iff.mpr (Or.inr ⟨s3a, cPref, 5 + 5 + 1, rPref,
      runs_seq_iff.mpr (Or.inr ⟨s3b, 5, 5, r3b, r3c, rfl⟩), rfl⟩),
    by rw [hvCapEq, heCapEq]; linarith [hcPref],
    by dsimp only [newLen0]; omega,
    by dsimp only [newRootGraph, newLen0]; rw [heCapEq]; omega,
    by dsimp only [ordPtr0, newRootGraph, newLen0, wireCompactLevel0Space]; rw [hvCapEq, heCapEq]; omega,
    by rw [hvCapEq]; exact hOrdEnd3a,
    by dsimp only [heap3, ordPtr0, newLen0, G0', G0, tr]; rw [hvCapEq, heCapEq]; omega,
    by simp [s3, s3b, hs3a_4, heap3, ordPtr0, newLen0, capP],
    by simp [s3, s3b, hs3a_28, newLen0, capP], by simp [s3, s3b],
    by simp [s3, s3b, hs3a_30, ordPtr0, newLen0, capP],
    fun a ha => by rw [hs3_eq_s3a a (by dsimp only [heap3, ordPtr0, newLen0] at ha; omega)]; exact hz3a a ha,
    fun r hr => by simp only [s3, s3b, Function.update_of_ne (by omega : r ≠ 29)]; exact hs3a_ge70 r hr,
    (hs3_eq_s2_ge heap le_rfl (by omega)).trans hHeap0_2,
    fun j hj => (hs3_eq_s2_ge _ (by omega) (by omega)).trans (hEmptyPtrs2 j hj),
    fun j hj => (hs3_eq_s2_ge _ (by omega) (by omega)).trans (hEmptyG2 j hj),
    ?_, ?_, ?_, (hs3_eq_s3a lm (by omega)).trans hLM0_3a, by simp [s3, lm],
    by rw [hvCapEq, heCapEq]; exact dynGraphAt_of_agree hRG3a (fun a ha1 _ => hs3_eq_s3a a (by dsimp only [newRootGraph, newLen0] at ha1; omega)),
    hLen3a.congr (fun e he t ht => hs3_eq_s3a _ (by omega)),
    by rw [hvCapEq]; exact ordListAt_of_agree hOrd3a (fun t ht => hs3_eq_s3a _ (by omega)),
    fun t ht => by rw [hs3_eq_s3a _ (by omega)]; exact hOrdW3a t (hvCapEq ▸ ht),
    ?_, ?_, ?_, hTreeLoc3.1 hTreeRep1, hTreeLoc3.2.symm, ?_, ?_, ?_, ?_⟩
  · exact ⟨(hs3_eq_s3a _ (hTagSep _ _ _ _ hT6 (hTagMeta0 cfg.P.d (by omega)) (by omega))).trans hFresh3a.1,
      fun e he => (hs3_eq_s3a _ (hTagSep _ _ _ _ (hT7 e he) (hTagMeta0 cfg.P.d (by omega)) (by omega))).trans (hFresh3a.2.1 e he),
      fun j hj => (hs3_eq_s3a _ (hTagSep _ _ _ _ (hT8 j hj) (hTagMeta0 cfg.P.d (by omega)) (by omega))).trans (hFresh3a.2.2 j hj)⟩
  · exact (hs3_eq_s3a _ (hTagSep _ _ _ _ (hT1 14 (by omega)) (hTagMeta0 cfg.P.d (by omega)) (by omega))).trans hR14_3a
  · exact (hs3_eq_s3a _ (hTagSep _ _ _ _ (hT1 11 (by omega)) (hTagMeta0 cfg.P.d (by omega)) (by omega))).trans hR11_3a
  · intro e he
    have ht := hT9 e he
    exact (hs3_eq_s2 _ (by have := htagLt (by rw [ht]; decide); omega)
      (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide)
      (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; decide) (by rw [ht]; omega)
      (hTagSep _ _ _ _ ht (hT1 11 (by omega)) (by decide))
      (hTagSep _ _ _ _ ht (hT1 14 (by omega)) (by decide))).trans (hZeroSlots2 e he)
  · intro e he
    exact (hs3_eq_s3a _ (hTagSep _ _ _ _ (hT15 e he) (hTagMeta0 cfg.P.d (by omega)) (by omega))).trans (hZeroIn3a e he)
  · obtain ⟨hc, _, _, h3', _⟩ := hOffInv3a
    refine ⟨hc, fun j hj => by omega, fun j1 hj1 => by omega, fun e he => by
      rw [hs3_eq_s3a _ (hTagSep _ _ _ _ (hT15 e he) (hTagMeta0 cfg.P.d (by omega)) (by omega))]; exact h3' e he,
      fun e he h1 => by
        rw [hs3_eq_s3a _ (hTagSep _ _ _ _ (hT15 e he) (hTagMeta0 cfg.P.d (by omega)) (by omega))] at h1
        exact False.elim (by have := hZeroIn3a e he; omega)⟩
  · intro e he
    have heiOldG0' : tr.2.1 e ∈ G0'.E := hFreshTr.hE ▸ Finset.mem_image_of_mem tr.2.1 (hTr1Eq.symm ▸ he)
    have hRankLt : compactRank G0'.E (tr.2.1 e) < G0'.m := compactRank_lt heiOldG0'
    have hG0'mLeInt : G0'.m ≤ tok.intCap := by
      have h := Finset.card_le_card (fun x hx => Finset.mem_range.mpr (hG0'Cap x hx).2)
      simpa [MGraph.m] using h
    have hUnrank : compactUnrank G0'.E (compactRank G0'.E (tr.2.1 e)) = tr.2.1 e :=
      compactUnrank_rank heiOldG0'
    have hE2IEq : level0E2I true G0' tr.2.1 e = compactRank G0'.E (tr.2.1 e) := by
      unfold level0E2I; simp
    obtain ⟨hThr2, hRec2, hvf, hvg, hvl, hvfl, hvd, hof, hog, hol, hacc, hInG0, hNotG0⟩ := hCanon2 e he
    have hThrCell : s3.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e) = s2.mem (tok.edgeThresholds + tr.2.1 e) := by
      rw [hE2IEq, hs3_eq_s3a _ (hTagSep _ _ _ _ (hT12 _ (lt_of_lt_of_le hRankLt hG0'mLeInt)) (hTagMeta0 cfg.P.d (by omega)) (by omega)),
        (hTab3a _ hRankLt).1, hUnrank]
    have hRecCell : s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) = s2.mem (tok.edgeRecords + tr.2.1 e) := by
      rw [hE2IEq, hs3_eq_s3a _ (hTagSep _ _ _ _ (hT13 _ (lt_of_lt_of_le hRankLt hG0'mLeInt)) (hTagMeta0 cfg.P.d (by omega)) (by omega)),
        (hTab3a _ hRankLt).2, hUnrank]
    have hOldEq (hOld : tr.2.1 e ∈ G0.E) : model.extToInt e = tr.2.1 e := by
      by_cases hRepE : ∃ u ∈ U, Update.Inserts e u
      · exact False.elim ((hDichRep e he hRepE).2.2.2.1 hOld)
      · exact (hDichUnch e he hRepE).2.1.symm
    have hThrAgree : ∀ t < L, s3.mem (s2.mem (tok.edgeThresholds + tr.2.1 e) + t) =
        s2.mem (s2.mem (tok.edgeThresholds + tr.2.1 e) + t) := fun t ht => by
      by_cases hOld : tr.2.1 e ∈ G0.E
      · rw [(hInG0 hOld).1]
        have hTag17 : tok.tag (mem0 (tok.edgeThresholds + tr.2.1 e) + t) = 17 := by
          rw [← hOldEq hOld]; exact (hT1718 e he).1 t ht
        have hLtH2 : mem0 (tok.edgeThresholds + tr.2.1 e) + t < heap2 := by
          have := htagLt (by rw [hTag17]; decide); omega
        exact hs3_eq_s2 _ hLtH2
          (by rw [hTag17]; decide) (by rw [hTag17]; decide) (by rw [hTag17]; decide)
          (by rw [hTag17]; decide) (by rw [hTag17]; decide) (by rw [hTag17]; decide)
          (by rw [hTag17]; decide) (by rw [hTag17]; omega)
          (hTagSep _ _ _ _ hTag17 (hT1 11 (by omega)) (by decide))
          (hTagSep _ _ _ _ hTag17 (hT1 14 (by omega)) (by decide))
      · obtain ⟨hlo, hhi, _, _⟩ := hNotG0 hOld
        change heapSync + 3 * L ≤ s2.mem (tok.edgeThresholds + tr.2.1 e) at hlo
        change s2.mem (tok.edgeThresholds + tr.2.1 e) + L ≤ heap2 at hhi
        exact hs3_eq_s2_ge _ (by omega) (by omega)
    have hRecAgree : ∀ a, s2.mem (tok.edgeRecords + tr.2.1 e) ≤ a →
        a < s2.mem (tok.edgeRecords + tr.2.1 e) + (2 + 4 * L) → s3.mem a = s2.mem a := fun a ha1 ha2 => by
      by_cases hOld : tr.2.1 e ∈ G0.E
      · by_cases hTree : tr.2.1 e ∈ model.chain.toTreeChain.chainTree.E
        · obtain ⟨hlo, hhi, _⟩ := (hInG0 hOld).2.1 hTree
          change heap1 ≤ s2.mem (tok.edgeRecords + tr.2.1 e) at hlo
          change s2.mem (tok.edgeRecords + tr.2.1 e) + (2 + 4 * L) ≤ heapSync at hhi
          exact hs3_eq_s2_ge a (by omega) (by omega)
        · have hPtrEq : s2.mem (tok.edgeRecords + tr.2.1 e) = mem0 (tok.edgeRecords + tr.2.1 e) := (hInG0 hOld).2.2 hTree
          have heOld := hOldEq hOld
          have hTag18 : tok.tag a = 18 := by
            have := (hT1718 e he).2 (heOld.symm ▸ hTree) (a - mem0 (tok.edgeRecords + tr.2.1 e)) (by omega)
            rwa [heOld, show mem0 (tok.edgeRecords + tr.2.1 e) + (a - mem0 (tok.edgeRecords + tr.2.1 e)) = a by omega] at this
          exact hs3_eq_s2 a (by have := htagLt (by rw [hTag18]; decide); omega)
            (by rw [hTag18]; decide) (by rw [hTag18]; decide) (by rw [hTag18]; decide)
            (by rw [hTag18]; decide) (by rw [hTag18]; decide) (by rw [hTag18]; decide)
            (by rw [hTag18]; decide) (by rw [hTag18]; omega)
            (hTagSep _ _ _ _ hTag18 (hT1 11 (by omega)) (by decide))
            (hTagSep _ _ _ _ hTag18 (hT1 14 (by omega)) (by decide))
      · obtain ⟨_, _, hlo, hhi⟩ := hNotG0 hOld
        change heapSync + 3 * L ≤ s2.mem (tok.edgeRecords + tr.2.1 e) at hlo
        change s2.mem (tok.edgeRecords + tr.2.1 e) + (2 + 4 * L) ≤ heap2 at hhi
        exact hs3_eq_s2_ge a (by omega) (by omega)
    refine ⟨hE2IEq ▸ hRankLt, hE2IEq ▸ hUnrank,
      by rw [hThrCell]; exact hThr2.congr hThrAgree,
      by rw [hRecCell]; exact hRec2.congr (fun a ha1 ha2 => hRecAgree a ha1 (by
        change a < s2.mem (tok.edgeRecords + tr.2.1 e) + 2 + 4 * L at ha2; omega)),
      hvf, hvg, hvl, hvfl, hvd, hof, hog, hol, hacc,
      fun hOld => by rw [hThrCell, hRecCell]; exact hInG0 hOld,
      fun hNot => by rw [hThrCell, hRecCell]; exact hNotG0 hNot⟩
  · intro e₁ he1 e₂ he2 hne
    have hG0'mLeInt : G0'.m ≤ tok.intCap := by
      have h := Finset.card_le_card (fun x hx => Finset.mem_range.mpr (hG0'Cap x hx).2)
      simpa [MGraph.m] using h
    have h1G : tr.2.1 e₁ ∈ G0'.E := hFreshTr.hE ▸ Finset.mem_image_of_mem tr.2.1 (hTr1Eq.symm ▸ he1)
    have h2G : tr.2.1 e₂ ∈ G0'.E := hFreshTr.hE ▸ Finset.mem_image_of_mem tr.2.1 (hTr1Eq.symm ▸ he2)
    have h1Ne2 : tr.2.1 e₁ ≠ tr.2.1 e₂ := fun h => hne ((hFreshTr.hLeft e₁ (hTr1Eq.symm ▸ he1)).symm.trans (h ▸ hFreshTr.hLeft e₂ (hTr1Eq.symm ▸ he2)))
    have hC (e : ℕ) (hG : tr.2.1 e ∈ G0'.E) :
        s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e) = s2.mem (tok.edgeRecords + tr.2.1 e) := by
      unfold level0E2I; simp only [↓reduceIte]
      have hR : compactRank G0'.E (tr.2.1 e) < G0'.m := compactRank_lt hG
      rw [hs3_eq_s3a _ (hTagSep _ _ _ _ (hT13 _ (lt_of_lt_of_le hR hG0'mLeInt)) (hTagMeta0 cfg.P.d (by omega)) (by omega)),
        (hTab3a _ hR).2, compactUnrank_rank hG]
    rw [hC e₁ h1G, hC e₂ h2G]; exact hOffDisj2 _ h1G _ h2G h1Ne2
  · intro e₁ he1 hnot1 e₂ he2 hnot2
    have hG0'mLeInt : G0'.m ≤ tok.intCap := by
      have h := Finset.card_le_card (fun x hx => Finset.mem_range.mpr (hG0'Cap x hx).2)
      simpa [MGraph.m] using h
    have h1G : tr.2.1 e₁ ∈ G0'.E := hFreshTr.hE ▸ Finset.mem_image_of_mem tr.2.1 (hTr1Eq.symm ▸ he1)
    have h2G : tr.2.1 e₂ ∈ G0'.E := hFreshTr.hE ▸ Finset.mem_image_of_mem tr.2.1 (hTr1Eq.symm ▸ he2)
    have hC1 : s3.mem (tok.edgeThresholds + level0E2I true G0' tr.2.1 e₁) = s2.mem (tok.edgeThresholds + tr.2.1 e₁) := by
      unfold level0E2I; simp only [↓reduceIte]
      have hR : compactRank G0'.E (tr.2.1 e₁) < G0'.m := compactRank_lt h1G
      rw [hs3_eq_s3a _ (hTagSep _ _ _ _ (hT12 _ (lt_of_lt_of_le hR hG0'mLeInt)) (hTagMeta0 cfg.P.d (by omega)) (by omega)),
        (hTab3a _ hR).1, compactUnrank_rank h1G]
    have hC2 : s3.mem (tok.edgeRecords + level0E2I true G0' tr.2.1 e₂) = s2.mem (tok.edgeRecords + tr.2.1 e₂) := by
      unfold level0E2I; simp only [↓reduceIte]
      have hR : compactRank G0'.E (tr.2.1 e₂) < G0'.m := compactRank_lt h2G
      rw [hs3_eq_s3a _ (hTagSep _ _ _ _ (hT13 _ (lt_of_lt_of_le hR hG0'mLeInt)) (hTagMeta0 cfg.P.d (by omega)) (by omega)),
        (hTab3a _ hR).2, compactUnrank_rank h2G]
    rw [hC1, hC2]; exact hThrOffDisj2 _ h1G hnot1 _ h2G hnot2
  · intro a ha hne11 hne14 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h20 h22 h23 hc
    exact (hs3_eq_s2 a (by omega) h6 h7 h8 h12 h13 h14 h15 h22 hne11 hne14).trans
      (hs2_frame_arr a ha hne11 h9 h10 h11 h12 h13 h14 h15 h16 h20 h23 hc)

end MinCostFlow.MinRatio
