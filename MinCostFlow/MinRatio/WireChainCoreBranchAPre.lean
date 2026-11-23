module

public import MinCostFlow.MinRatio.WireChainCorePreCommon
import WordRAM.Tactic

/-!
# Branch A pre-chain synchronization and account refresh (`WireChainCoreBranchAPre`)

Provides `wireBranchASync1AndPrepStmt` and `wireBranchASync1AndPrep_runs`, covering the first half
of Branch A (level-0 rebuild) after Phase 0 forest collection:
1. Fills `emptyPtrs[0..d]` with `emptyGraphPtr` (`wireFillEmptyPtrsLoop`).
2. Packs `oldF → ∅` via `wireSuffixPackEditsBody` and cuts every active tree edge from `tok.tree`
   via `wireTreeSyncLoop` (`wireTreeSyncLoop_defer_runs` with `deferSet := ∅`), saving up-to-date
   canonical `PathEdgeAt` records for all edges of `G₀`.
3. Zeroes `slots[0..intCap)` via `wireZeroSlotsStmt`.
4. Refreshes replaced edge accounts (`edgeThresholds`/`edgeRecords`), updates `rootGraph` in place
   from `G₀` to `G₀'`, and updates `levelMeta[0]` to `ℓ'` via `wireRefreshAndUpdateRootStmt`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- Branch A pre-chain statement: Sync 1 (`oldF → ∅`), zero `slots[0..intCap)`, refresh accounts,
update `rootGraph` to `G₀'`, and update `levelMeta[0]` to `ℓ'`. -/
@[expose] def wireBranchASync1AndPrepStmt
    (packEditsProc readTree cutTree linkTree bind canonCopy isNeg
      refreshAccountsProc dgApply updateLen0Proc : ℕ) : Stmt :=
  wireFillEmptyPtrsLoop ;;
  .assign 10 (.load (.bin .add (.reg 70) (.const 15))) ;;
  .assign 6 (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 10))) ;;
  .call 18 packEditsProc [.reg 80, .reg 92, .reg 79, .reg 10, .reg 4] ;;
  .assign 27 (.reg 70) ;;
  .assign 29 (.reg 73) ;;
  shiftTermSetupLoop ;;
  wireTreeSyncLoop readTree cutTree linkTree bind canonCopy isNeg ;;
  .assign 4 (.reg 3) ;;
  wireZeroSlotsStmt ;;
  wireRefreshAndUpdateRootStmt refreshAccountsProc dgApply updateLen0Proc

theorem wireBranchASync1AndPrepStmt_noRand
    (packEditsProc readTree cutTree linkTree bind canonCopy isNeg
      refreshAccountsProc dgApply updateLen0Proc : ℕ) :
    (wireBranchASync1AndPrepStmt packEditsProc readTree cutTree linkTree bind canonCopy isNeg
      refreshAccountsProc dgApply updateLen0Proc).NoRand := by
  simp [wireBranchASync1AndPrepStmt, wireFillEmptyPtrsLoop_noRand, shiftTermSetupLoop,
    wireTreeSyncLoop_noRand, wireZeroSlotsStmt_noRand, wireRefreshAndUpdateRootStmt_noRand,
    Stmt.NoRand]

private theorem pathRep_foot_base_a {L C b : ℕ} {s : PathTreeState}
    {x : (LinkCut.PathProg.pathRep 4 L C).τ} {mem : ℕ → ℕ}
    (_hrep : (LinkCut.PathProg.pathRep 4 L C).rep b s x mem) :
    (LinkCut.PathProg.pathRep 4 L C).foot b x b := by
  refine ⟨le_rfl, ?_⟩
  unfold LinkCut.PathProg.arenaEnd LinkCut.PathProg.arenaNb LinkCut.PathProg.recW
  have h1 : 1 ≤ LinkCut.PathProg.recW (LinkCut.PathProg.treeLimbs L) := by
    unfold LinkCut.PathProg.recW; omega
  have h3 := Nat.mul_pos h1 (by omega : 0 < 2 * x.1.n + 1)
  unfold LinkCut.PathProg.recW at h3; omega

set_option maxHeartbeats 1200000 in
/-- Execute `wireBranchASync1AndPrepStmt` starting from `st` right after Phase 0
(`updateCoreInitRegs` + `collectCopyLSFForestsLoop` + `collectTermForestStmt`). -/
theorem wireBranchASync1AndPrep_runs
    {w L P m V psi k epsExp drainUnit wordExp stretchPrec
      packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc
      root uIntBuf editsPtr g l heap heap1 ec0 : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree : ℕ → ℕ}
    {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {st : State}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
    (hPackProc : p.procs[packEditsProc]? = some wireSuffixPackEditsBody)
    (hRefAccProc : p.procs[refreshAccountsProc]? =
      some (wireRefreshAccountsBody shift negate refreshOneProc))
    (hRefOneProc : p.procs[refreshOneProc]? =
      some (wireRefreshOneAccountBody divide add sub negate copy isNeg))
    (hUpdLen0Proc : p.procs[updateLen0Proc]? = some (wireUpdateLen0FromBatchBody copy))
    (hFmtBits : fmt.limbBits = 4) (hLpos : 0 < L) (hPword : P < 2 ^ w) (hw18 : 18 < 2 ^ w)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hBindOk : MeetsContract w p bind (pathSlotBindContract w))
    (hCanonOk : ∀ v, MeetsContract w p canonCopy (wireCanonCopyContract w v))
    (hIsNegOk : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w 4))
    (hdiv : MeetsContract w p divide (Num.fixedDivideContract w 4))
    (hadd : MeetsContract w p add (Num.addContract w 4))
    (hsub : MeetsContract w p sub (Num.subtractContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hDGApplyRoot :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      MeetsContract w p dgApply
        (dgApplyBatchContract w model.extG.n tok.rootECap (model.chain.G 0) (model.chain.G 0)
          tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf)))
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
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < uIntBuf)
    (hGLt : g + m * L ≤ uIntBuf) (hLLt : l + m * L ≤ uIntBuf)
    (hULeEd : uIntBuf + cfg.P.d ≤ editsPtr) (hEdLeHeap : editsPtr ≤ heap)
    (hH1Ge : heap + 3 * (cfg.P.d + 1) + 4 ≤ heap1)
    (hLevel0Meta :
      let lm := solverLevelMetaAddr tok.table cfg.P.d
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      EdgeValuesAt mem0 (mem0 lm) 4 L P (model.chain.G 0).E
        (model.chain.toTreeChain.chainLen model.chain.ℓ 0) ∧
      (∀ a, mem0 lm ≤ a → a < mem0 lm + ec0 * L → tok.tag a = 23 + cfg.P.d) ∧
      (∀ e ∈ (model.chain.G 0).E, e < ec0) ∧
      (∀ e ∈ ((model.chain.G 0).applyBatch tr.2.2.2.2).E, e < ec0) ∧
      (∀ u ∈ tr.2.2.2.2, match u with | .insert ei _ _ => ei < ec0 | _ => True))
    (hRegs :
      st.regs 4 = heap1 ∧ st.regs 70 = root ∧ st.regs 73 = tok.handle ∧
      st.regs 75 = cfg.P.d ∧ st.regs 79 = cfg.P.d + 1 ∧ st.regs 80 = heap ∧
      st.regs 83 = solverLevelMetaAddr tok.table cfg.P.d ∧ st.regs 87 = uIntBuf ∧
      st.regs 90 = g ∧ st.regs 91 = l ∧
      st.regs 92 = heap + 2 * (cfg.P.d + 1) ∧ st.regs 93 = heap + 3 * (cfg.P.d + 1) ∧
      st.regs 94 = L)
    (hz1 : ZeroFrom st.mem heap1)
    (hEmptyZero : ∀ j < 4, st.mem (heap + 3 * (cfg.P.d + 1) + j) = 0)
    (hOldForests : ∀ j (hj : j < cfg.P.d + 1),
      let G := (chainSuffixForests model.chain 0)[j]'(by rw [chainSuffixForests_length]; omega)
      ∃ vc ec, DynGraphAt st.mem (st.mem (heap + j)) vc ec G ∧
        (st.mem (heap + j) + dynGraphSize vc ec ≤ heap ∨
          heap + 3 * (cfg.P.d + 1) + 4 ≤ st.mem (heap + j)) ∧
        st.mem (heap + j) + dynGraphSize vc ec ≤ heap1 ∧
        ∀ e ∈ G.E, e < tok.intCap)
    (hStFrame : ∀ a < heap, (∀ j < cfg.P.d, ¬ Rcore.foot (tok.coreHandle j) (tok.coreTok j) a) →
      st.mem a = mem a)
    (hRoom :
      let sumOld := graphListEdgeSum (chainSuffixForests model.chain 0)
      heap1 + (3 * tok.intCap + sumOld * (2 + wireTreeSyncEditSpace L)) +
        (3 * L + U.length * wireRefreshOneSpace L) < 2 ^ w) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let U_int := tr.2.2.2.2
    let G0 := model.chain.G 0
    let G0' := G0.applyBatch U_int
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
    let ℓ' := fun e' => lVec (tr.2.2.1 e')
    let lm := solverLevelMetaAddr tok.table cfg.P.d
    let sumOld := graphListEdgeSum (chainSuffixForests model.chain 0)
    ∃ (out : State) (cost heapSync heap2 : ℕ) (curTree1 : PathTreeState)
      (curTrees1 : List AuxTree) (curFree1 : List ℕ) (curDepth1 : ℕ → ℕ)
      (curTreeTok1 : Rtree.τ) (newCanonVal : ℕ → PathEdgeValue),
      Runs w p ω (wireBranchASync1AndPrepStmt packEditsProc (opTree 4) (opTree 1) (opTree 0)
        bind canonCopy isNeg refreshAccountsProc dgApply updateLen0Proc) st .normal out cost ∧
      cost + Rtree.phi tok.treeHeap curTreeTok1 out.mem ≤
        (230 * (cfg.P.d + 1) + 85 * sumOld + 300) +
        sumOld * (wireTreeSyncEditCost L drainUnit + 2) +
        (15 * tok.intCap + 30) +
        (U.length * (wireRefreshOneCost L + 120) + 71 * L + 210) +
        (670 * (4 * U.length + 1) + 30) + (U.length * (17 * L + 70) + 80) +
        (Rtree.phi tok.treeHeap tok.treeTok mem0 + tok.offReadyCount * drainUnit) ∧
      out.regs 4 = heap2 ∧
      heap1 ≤ heapSync ∧ heapSync ≤ heap1 + 3 * tok.intCap + sumOld * (2 + wireTreeSyncEditSpace L) ∧
      heapSync + 3 * L ≤ heap2 ∧ heap2 ≤ heapSync + 3 * L + U.length * wireRefreshOneSpace L ∧
      ZeroFrom out.mem heap2 ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      (∀ j < cfg.P.d + 1, out.mem (heap + 2 * (cfg.P.d + 1) + j) = heap + 3 * (cfg.P.d + 1)) ∧
      (∀ j < 4, out.mem (heap + 3 * (cfg.P.d + 1) + j) = 0) ∧
      curTree1.n = model.extG.n ∧
      LctInvWith pathPayload curTree1 curTrees1 curFree1 curDepth1 ∧
      PathTreeNumericInv curTree1 curTrees1 B R ∧
      TreeEditNamedSlots curTree1 curTrees1 { G0' with E := ∅ }
        (fun ei => out.mem (tok.slots + ei)) (fun sl => out.mem (tok.names + sl)) ∧
      TreeEditLiveAccounts curTree1 curTrees1 { G0' with E := ∅ }
        (fun ei => out.mem (tok.slots + ei)) newCanonVal ∧
      Rtree.rep tok.treeHeap curTree1 curTreeTok1 out.mem ∧
      (∀ a, Rtree.foot tok.treeHeap curTreeTok1 a →
        Rtree.foot tok.treeHeap tok.treeTok a ∨ (heap1 ≤ a ∧ a < heapSync)) ∧
      (∀ j < tok.intCap, out.mem (tok.slots + j) = 0) ∧
      DynGraphAt out.mem tok.rootGraph model.extG.n tok.rootECap G0' ∧
      EdgeValuesAt out.mem (mem0 lm) 4 L P G0'.E ℓ' ∧
      (∀ a < heap1, a ≠ root + 11 →
        (a < heap + 2 * (cfg.P.d + 1) ∨ heap + 3 * (cfg.P.d + 1) ≤ a) →
        tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 → tok.tag a ≠ 12 → tok.tag a ≠ 13 →
        tok.tag a ≠ 14 → tok.tag a ≠ 15 → tok.tag a ≠ 16 → tok.tag a ≠ 20 →
        (a < mem0 lm ∨ mem0 lm + ec0 * L ≤ a) → out.mem a = st.mem a) ∧
      (∀ e ∈ model.extG.E,
        let ei := tr.2.1 e
        let v := newCanonVal ei
        PathIntAt out.mem (out.mem (tok.edgeThresholds + ei)) 4 L (detectorThreshold P cfg.ε (lVec e)) ∧
        PathEdgeAt out.mem (out.mem (tok.edgeRecords + ei)) 4 L (some v) ∧
        v.forward = true ∧ |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B ∧
        (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (v.originalGradient : ℝ) / (2 : ℝ) ^ P = gVec e ∧
        (v.length : ℝ) / (2 : ℝ) ^ P = lVec e ∧
        (∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
          v.detector = acc - detectorThreshold P cfg.ε (lVec e)) ∧
        (ei ∈ G0.E →
          out.mem (tok.edgeThresholds + ei) = mem0 (tok.edgeThresholds + ei) ∧
          ((ei ∈ model.chain.toTreeChain.chainTree.E →
              heap1 ≤ out.mem (tok.edgeRecords + ei) ∧
              out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heapSync ∧
              ∀ a, out.mem (tok.edgeRecords + ei) ≤ a →
                a < out.mem (tok.edgeRecords + ei) + (2 + 4 * L) →
                ¬ Rtree.foot tok.treeHeap curTreeTok1 a) ∧
           (ei ∉ model.chain.toTreeChain.chainTree.E →
              out.mem (tok.edgeRecords + ei) = mem0 (tok.edgeRecords + ei)))) ∧
        (ei ∉ G0.E →
          heapSync + 3 * L ≤ out.mem (tok.edgeThresholds + ei) ∧
          out.mem (tok.edgeThresholds + ei) + L ≤ heap2 ∧
          heapSync + 3 * L ≤ out.mem (tok.edgeRecords + ei) ∧
          out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heap2)) ∧
      (∀ ei₁ ∈ G0'.E, ∀ ei₂ ∈ G0'.E, ei₁ ≠ ei₂ →
        out.mem (tok.edgeRecords + ei₁) + (2 + 4 * L) ≤ out.mem (tok.edgeRecords + ei₂) ∨
        out.mem (tok.edgeRecords + ei₂) + (2 + 4 * L) ≤ out.mem (tok.edgeRecords + ei₁)) ∧
      (∀ ei₁ ∈ G0'.E, ei₁ ∉ G0.E → ∀ ei₂ ∈ G0'.E, ei₂ ∉ G0.E →
        out.mem (tok.edgeThresholds + ei₁) + L ≤ out.mem (tok.edgeRecords + ei₂) ∨
        out.mem (tok.edgeRecords + ei₂) + (2 + 4 * L) ≤ out.mem (tok.edgeThresholds + ei₁)) := by
  classical
  dsimp only
  set Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  set d := cfg.P.d
  set cnt := d + 1
  set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  set U_int := tr.2.2.2.2
  set G0 := model.chain.G 0
  set G0' := G0.applyBatch U_int
  set oldF := model.chain.toTreeChain.chainTree
  set lm := solverLevelMetaAddr tok.table d
  set emptyPtrs := heap + 2 * cnt
  set emptyGraphPtr := heap + 3 * cnt
  set sumOld := graphListEdgeSum (chainSuffixForests model.chain 0)
  have hRep0_keep := hRep0
  obtain ⟨hRootDir0, hDetHdr0, _, _, hFreshInv, _, _, ⟨hG0Cap, hIntCapPos, _, _⟩, _,
    hOffReady0, hTreeN0, hLct0, hTreeRep0, hAccounts0, _, _, _, _, hWire0, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, hT2, _, _, _, _, _, _, hT9, hT10, hT11, hT12, hT13, hT14, hT15,
    hT16, hT1718, _, hT20, hT21⟩ := hTags0
  obtain ⟨_, hRootG0, _, hNamed0, _⟩ := hWire0
  have hOldSub : oldF.E ⊆ G0.E := hModelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hG0nEq : G0.n = model.extG.n := by unfold MGraph.n; rw [← hFreshInv.hV]
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < uIntBuf := hFootLt a (Or.inl (hOwnOfTag a h))
  have hStEqMem0 {a : ℕ} (ha : a < uIntBuf)
      (h6 : tok.tag a ≠ 6) (h7 : tok.tag a ≠ 7) (h8 : tok.tag a ≠ 8)
      (hC : ∀ j < d, tok.tag a ≠ 21 + j) : st.mem a = mem0 a :=
    (hStFrame a (by omega) (fun j hj hf => hC j hj (hT21 j hj a hf))).trans (hMemEq a ha h6 h7 h8)
  -- Step 1: `wireFillEmptyPtrsLoop`
  obtain ⟨s1, cFill, rFill, hcFill, hFillPtrs, hFrFill, hRegsFill⟩ :=
    wireFillEmptyPtrsLoop_runs (w := w) (emptyPtrs := emptyPtrs) (emptyGraphPtr := emptyGraphPtr)
      (cnt := cnt) (p := p) (ω := ω) (st := st)
      hRegs.2.2.2.2.1 hRegs.2.2.2.2.2.2.2.2.2.2.1 hRegs.2.2.2.2.2.2.2.2.2.2.2.1 (by omega) (by omega)
  have hOldForests1 : ForestPtrListAt s1.mem heap (chainSuffixForests model.chain 0) tok.intCap heap1 := by
    refine ⟨by rw [chainSuffixForests_length]; omega, fun j hj => ?_⟩
    have hj' : j < cnt := by rw [chainSuffixForests_length] at hj; omega
    obtain ⟨vc, ec, hDG, hDisjE, hEnd, hCap⟩ := hOldForests j hj'
    have hPtrEq : s1.mem (heap + j) = st.mem (heap + j) := hFrFill _ (Or.inl (by omega))
    refine ⟨vc, ec, ?_, hPtrEq ▸ hEnd, hCap⟩
    rw [hPtrEq]
    exact hDG.of_agree fun a ha1 ha2 => hFrFill a (by rcases hDisjE with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
  have hEmptyForests1 : ForestPtrListAt s1.mem emptyPtrs (List.replicate cnt emptyZeroGraph) tok.intCap heap1 := by
    refine ⟨by simp [emptyPtrs]; omega, fun j hj => ?_⟩
    have hj' : j < cnt := by simpa using hj
    refine ⟨0, 0, ?_, ?_, fun _ he => by simp [emptyZeroGraph] at he⟩
    · rw [hFillPtrs j hj']
      have hG : (List.replicate cnt emptyZeroGraph)[j]'hj = emptyZeroGraph := List.getElem_replicate hj
      rw [hG]
      exact emptyZeroGraph_dynGraphAt fun t ht =>
        (hFrFill (emptyGraphPtr + t) (Or.inr (by omega))).trans (hEmptyZero t ht)
    · rw [hFillPtrs j hj']; unfold dynGraphSize; omega
  -- Step 2: pack `oldF → ∅` via `wireSuffixPackEditsBody`
  have hIntCap1 : s1.mem (root + 15) = tok.intCap :=
    (hFrFill (root + 15) (Or.inl (by have := htagLt (by rw [hT1 15 (by omega)]; decide); omega))).trans
      ((hStEqMem0 (htagLt (by rw [hT1 15 (by omega)]; decide))
        (by rw [hT1 15 (by omega)]; decide) (by rw [hT1 15 (by omega)]; decide)
        (by rw [hT1 15 (by omega)]; decide) (fun j _ => by rw [hT1 15 (by omega)]; omega)).trans
        (by simpa using hRootDir0 15 (by simp)))
  have hS1R (r : ℕ) (hr : 70 ≤ r) : s1.regs r = st.regs r := hRegsFill r (by omega)
  let editsBuf1 := heap1 + 3 * tok.intCap
  let s2 := { s1 with regs := Function.update s1.regs 10 tok.intCap }
  let s3 := { s2 with regs := Function.update s2.regs 6 editsBuf1 }
  have r2 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 70) (.const 15)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨tok.intCap, by simp [Expr.eval, BinOp.eval, hS1R 70 (by decide), hRegs.2.1,
      show 15 < 2 ^ w by omega, show root + 15 < 2 ^ w by have := htagLt (by rw [hT1 15 (by omega)]; decide); omega,
      hIntCap1], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 6 (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 10)))) s2 .normal s3 6 :=
    runs_assign_iff.mpr ⟨editsBuf1, by simp [Expr.eval, BinOp.eval, s2, hRegsFill 4 (by decide),
      hRegs.1, show 3 < 2 ^ w by omega, show 3 * tok.intCap < 2 ^ w by omega,
      show editsBuf1 < 2 ^ w by dsimp [editsBuf1]; omega, editsBuf1], rfl, rfl, rfl⟩
  have hPack1Room : heap1 + 3 * tok.intCap + 2 * (sumOld + graphListEdgeSum (List.replicate cnt emptyZeroGraph)) < 2 ^ w := by
    rw [graphListEdgeSum_replicate_empty, add_zero]
    have hmul : 2 * sumOld ≤ sumOld * (2 + wireTreeSyncEditSpace L) := by
      have : 2 * sumOld = sumOld * 2 := Nat.mul_comm _ _
      rw [this]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨outPack, cPack, edits1, rPackBody, hcPack, hEdits1Le, hEditsAt4, hDiff1Raw, hzPack, hFrPack⟩ :=
    wireSuffixPackEdits_runs (w := w) (oldPtrs := heap) (newPtrs := emptyPtrs) (cnt := cnt)
      (intCap := tok.intCap) (heap := heap1) (pos := s3.pos)
      (oldFs := chainSuffixForests model.chain 0) (newFs := List.replicate cnt emptyZeroGraph)
      (p := p) (ω := ω) (mem := s3.mem)
      (chainSuffixForests_length model.chain 0) List.length_replicate
      hOldForests1 hEmptyForests1 (fun a ha => (hFrFill a (Or.inr (by omega))).trans (hz1 a ha))
      hPack1Room (by omega)
  rw [graphListEdgeSum_replicate_empty, add_zero] at hcPack hEdits1Le
  have hOldUnionEq : graphListEdgeUnion (chainSuffixForests model.chain 0) = oldF.E := by
    have := chainTree_E_eq_prefix_union_suffix model.chain (Nat.zero_le _)
    simpa [oldF] using this.symm
  have hDiff1 : TreeEditDifference oldF.E ∅ edits1 := by
    rwa [hOldUnionEq, graphListEdgeUnion_replicate_empty] at hDiff1Raw
  let s4 : State := { regs := Function.update s3.regs 18 edits1.length, mem := outPack.mem, pos := outPack.pos }
  have r4 : Runs w p ω (.call 18 packEditsProc [.reg 80, .reg 92, .reg 79, .reg 10, .reg 4])
      s3 .normal s4 (5 + cPack + 1) :=
    runs_call_iff.mpr ⟨[heap, emptyPtrs, cnt, tok.intCap, heap1], wireSuffixPackEditsBody,
      .returned edits1.length, outPack, cPack,
      by simp [evalArgs, Expr.eval, s3, s2, hS1R 80 (by decide), hS1R 92 (by decide),
        hS1R 79 (by decide), hRegsFill 4 (by decide), hRegs.1, hRegs.2.2.2.2.1,
        hRegs.2.2.2.2.2.1, hRegs.2.2.2.2.2.2.2.2.2.2.1],
      hPackProc, rPackBody, rfl, rfl, by simp [argsSize, Expr.size]⟩
  -- Step 3: `shiftTermSetupLoop` + `wireTreeSyncLoop` (`oldF → { G0 with E := ∅ }`)
  have hS4EqS1 (a : ℕ) (ha : a < heap1) : s4.mem a = s1.mem a := hFrPack a ha
  have hS4EqMem0 {a : ℕ} (ha : a < uIntBuf)
      (h6 : tok.tag a ≠ 6) (h7 : tok.tag a ≠ 7) (h8 : tok.tag a ≠ 8)
      (hC : ∀ j < d, tok.tag a ≠ 21 + j) : s4.mem a = mem0 a :=
    (hS4EqS1 a (by omega)).trans ((hFrFill a (Or.inl (by omega))).trans (hStEqMem0 ha h6 h7 h8 hC))
  have hLoadRoot (j : ℕ) (hj : j < 16) : s4.mem (root + j) = mem0 (root + j) :=
    hS4EqMem0 (htagLt (by rw [hT1 j hj]; decide)) (by rw [hT1 j hj]; decide)
      (by rw [hT1 j hj]; decide) (by rw [hT1 j hj]; decide) (fun _ _ => by rw [hT1 j hj]; omega)
  have hLoadHdr (j : ℕ) (hj : j < 18) : s4.mem (tok.handle + j) = mem0 (tok.handle + j) :=
    hS4EqMem0 (htagLt (by rw [hT2 j hj]; decide)) (by rw [hT2 j hj]; decide)
      (by rw [hT2 j hj]; decide) (by rw [hT2 j hj]; decide) (fun _ _ => by rw [hT2 j hj]; omega)
  have hRootG4 : DynGraphAt s4.mem tok.rootGraph model.extG.n tok.rootECap G0 :=
    hRootG0.of_agree fun a ha1 ha2 =>
      hS4EqMem0 (htagLt (by rw [hT20 a ha1 ha2]; decide)) (by rw [hT20 a ha1 ha2]; decide)
        (by rw [hT20 a ha1 ha2]; decide) (by rw [hT20 a ha1 ha2]; decide)
        (fun _ _ => by rw [hT20 a ha1 ha2]; omega)
  let s5a := { s4 with regs := Function.update s4.regs 27 root }
  let s5b := { s5a with regs := Function.update s5a.regs 29 tok.handle }
  have r5a : Runs w p ω (.assign 27 (.reg 70)) s4 .normal s5a 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, s4, s3, s2, hS1R 70 (by decide), hRegs.2.1], rfl, rfl, rfl⟩
  have r5b : Runs w p ω (.assign 29 (.reg 73)) s5a .normal s5b 2 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s5a, s4, s3, s2, hS1R 73 (by decide), hRegs.2.2.1], rfl, rfl, rfl⟩
  have hRootW : root + 16 ≤ uIntBuf := by have := htagLt (by rw [hT1 15 (by omega)]; decide); omega
  have hHandleW : tok.handle + 18 ≤ uIntBuf := by have := htagLt (by rw [hT2 17 (by omega)]; decide); omega
  have hRootGW : tok.rootGraph + dynGraphSize model.extG.n tok.rootECap ≤ uIntBuf := by
    have hpos : 0 < dynGraphSize model.extG.n tok.rootECap := by unfold dynGraphSize; omega
    have := htagLt (by rw [hT20 (tok.rootGraph + dynGraphSize model.extG.n tok.rootECap - 1) (by omega) (by omega)]; decide); omega
  obtain ⟨s6, cSetup, rSetup, hcSetup, hs6Mem, h6_0, h6_1, h6_2, h6_3, h6_6, h6_18, h6_9, h6_10,
      h6_11, h6_19, h6_20, h6_22, h6_23, h6_24, h6_25, h6_26⟩ :=
    shiftTermSetupLoop_runs (w := w) (st := s5b) (editPtr := editsBuf1) (nEdits := edits1.length)
      (root := root) (handle := tok.handle) (by simp [s5b, s5a, s4, s3]) (by simp [s5b, s5a, s4])
      (by simp [s5b, s5a]) (by simp [s5b])
      ((hLoadHdr 0 (by omega)).trans (by simpa using hDetHdr0 0 (by simp)))
      ((hLoadHdr 5 (by omega)).trans (by simpa using hDetHdr0 5 (by simp)))
      ((hLoadRoot 14 (by omega)).trans (by simpa using hRootDir0 14 (by simp)))
      (by simpa [dgVCapOff] using hRootG4.2.2.2.1)
      (by simpa [dgECapOff] using hRootG4.2.2.2.2.1)
      ((hLoadRoot 6 (by omega)).trans (by simpa using hRootDir0 6 (by simp)))
      ((hLoadRoot 7 (by omega)).trans (by simpa using hRootDir0 7 (by simp)))
      ((hLoadRoot 8 (by omega)).trans (by simpa using hRootDir0 8 (by simp)))
      ((hLoadRoot 9 (by omega)).trans (by simpa using hRootDir0 9 (by simp)))
      ((hLoadRoot 10 (by omega)).trans (by simpa using hRootDir0 10 (by simp)))
      ((hLoadRoot 12 (by omega)).trans (by simpa using hRootDir0 12 (by simp)))
      ((hLoadRoot 13 (by omega)).trans (by simpa using hRootDir0 13 (by simp)))
      (by omega) (by omega) (by dsimp [editsBuf1]; omega) (by omega)
  have hS6Regs : ∀ r, 70 ≤ r → s6.regs r = st.regs r := fun r hr =>
    (runs_regs_ge_of_noWriteGe rSetup shiftTermSetupLoop_noWriteGe70 r hr).trans (by
      simp [s5b, s5a, s4, s3, s2, Function.update_of_ne (by omega : r ≠ 29),
        Function.update_of_ne (by omega : r ≠ 27), Function.update_of_ne (by omega : r ≠ 18),
        Function.update_of_ne (by omega : r ≠ 6), Function.update_of_ne (by omega : r ≠ 10), hS1R r hr])
  let heap0Sync := editsBuf1 + 2 * edits1.length
  obtain ⟨canonVal, hLive0, hCanonExt⟩ := liveAccounts_of_solverStateRep hRep0_keep hNum0 hOffInv0 hOffBd0 hOldSub
  have hCanonProp : ∀ ei ∈ G0.E, (canonVal ei).forward = true ∧ |(canonVal ei).gradient| ≤ B ∧
      |(canonVal ei).length| ≤ B ∧ |(canonVal ei).flow| ≤ B ∧ |(canonVal ei).detector| ≤ B := fun ei heiG => by
    obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
    obtain ⟨hf, hg, hl, hfl, hd, _⟩ := hCanonExt (model.intToExt ei) heExt
    rw [heMap] at hf hg hl hfl hd; exact ⟨hf, hg, hl, hfl, hd⟩
  have h2nW : 2 * G0.n + 1 < 2 ^ w := by
    rw [hG0nEq]; by_cases hn0 : model.extG.n = 0
    · omega
    · have := htagLt (by rw [hT10 (2 * tok.tree.n - 1) (by omega)]; decide); omega
  have hTreeHeapLt : tok.treeHeap < 2 ^ w :=
    lt_trans (htagLt (by rw [hT16 tok.treeHeap (pathRep_foot_base_a hTreeRep0)]; decide)) (by omega)
  have hSync1Room : heap0Sync + edits1.length * wireTreeSyncEditSpace L < 2 ^ w := by
    have h1 : 2 * edits1.length + edits1.length * wireTreeSyncEditSpace L =
        edits1.length * (2 + wireTreeSyncEditSpace L) := by ring
    have h2 : edits1.length * (2 + wireTreeSyncEditSpace L) ≤ sumOld * (2 + wireTreeSyncEditSpace L) :=
      Nat.mul_le_mul_right _ hEdits1Le
    dsimp [heap0Sync, editsBuf1]; omega
  let empG0 : MGraph := { G0 with E := ∅ }
  have hEmpForest : empG0.IsForest :=
    ⟨fun _ h => absurd h (by simp [empG0]), fun c hc => by
      cases c with
      | nil => exact hc.1 rfl
      | cons step _ =>
        cases step with
        | mk e dir => obtain ⟨u, hw⟩ := hc.2.2; cases hw with | cons hmem _ _ => simp [empG0] at hmem⟩
  have hCtx1 : WireSyncCtx w L drainUnit cfg Rcore p fmt initTree opTree bind canonCopy isNeg
      root editsBuf1 heap0Sync s6.mem G0 oldF empG0 edits1 tok canonVal B R :=
    { fmtBits := hFmtBits, treeImpl := hTreeImpl, bindOk := hBindOk, canonOk := hCanonOk,
      isNegOk := hIsNegOk, diff := hDiff1, editsAt := hs6Mem.symm ▸ hEditsAt4,
      editsEnd := le_rfl,
      editsTag0 := fun a ha1 _ =>
        ⟨by by_contra hne; have := htagLt hne; dsimp [editsBuf1] at ha1; omega,
         fun h => by rw [h] at ha1; dsimp [editsBuf1] at ha1; omega⟩,
      rootGraph := hs6Mem.symm ▸ (hG0nEq.symm ▸ hRootG4),
      oldSub := hOldSub, newSub := Finset.empty_subset _, newForest := hEmpForest,
      oldEnds := fun _ _ => ⟨rfl, rfl⟩, newEnds := fun _ h => by simp [empG0] at h,
      capE := hG0Cap,
      vtxE := fun ei hei => by
        obtain ⟨h1, h2⟩ := hRootG0.1 ei hei; rw [hG0nEq]; exact ⟨hRootG0.2.1 _ h1, hRootG0.2.1 _ h2⟩,
      canonProp := hCanonProp,
      tags := ⟨fun a ha => lt_of_lt_of_le (htagLt ha) (by dsimp [heap0Sync, editsBuf1]; omega),
        hT1, hT9, fun j hj => hT10 j (by omega), fun j hj => hT11 j (by omega), hT12, hT13, hT14, hT15,
        hT16, fun ei heiG hnot j hj => by
          obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
          have h13 : s6.mem (tok.edgeRecords + ei) = mem0 (tok.edgeRecords + ei) :=
            hs6Mem.symm ▸ hS4EqMem0 (htagLt (by rw [hT13 ei (hG0Cap ei heiG)]; decide))
              (by rw [hT13 ei (hG0Cap ei heiG)]; decide) (by rw [hT13 ei (hG0Cap ei heiG)]; decide)
              (by rw [hT13 ei (hG0Cap ei heiG)]; decide) (fun _ _ => by rw [hT13 ei (hG0Cap ei heiG)]; omega)
          rw [h13]; have ht := (hT1718 (model.intToExt ei) heExt).2 (heMap.symm ▸ hnot) j hj
          rwa [heMap] at ht,
        fun a ha1 ha2 => hT20 a ha1 (by rw [← hG0nEq]; exact ha2)⟩,
      treeHeapLt := hTreeHeapLt, nW := h2nW, logW := hG0nEq.symm ▸ hLogW,
      capT := hG0nEq.symm ▸ hCapT, hw11 := by omega, room := hSync1Room }
  have hS6OfTag {a v : ℕ} (ht : tok.tag a = v) (hv : v = 1 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨ v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15 ∨ v = 16 ∨ v = 18) :
      s6.mem a = mem0 a :=
    hs6Mem.symm ▸ hS4EqMem0 (htagLt (by rw [ht]; omega)) (by omega) (by omega) (by omega) (fun _ _ => by omega)
  have hInv1Init : WireSyncDeferInv ∅ root editsBuf1 heap0Sync s6.mem G0 oldF empG0 edits1
      tok canonVal B R [] edits1 tok.tree tok.treeTok heap0Sync tok.offReadyCount s6 := by
    have hGr0 : ({ G0 with E := oldF.E } : MGraph) = oldF := rfl
    refine ⟨rfl, h6_0, h6_1, h6_2, h6_3, by simpa using h6_6, h6_18,
      hG0nEq.symm ▸ h6_9, hG0nEq.symm ▸ h6_10, hG0nEq.symm ▸ h6_11,
      h6_19, h6_20, h6_22, h6_23, h6_24, h6_25, h6_26, le_rfl, by simp, hs6Mem.symm ▸ hzPack,
      fun _ ha => Or.inl ha, fun _ _ _ _ _ _ _ _ _ _ => rfl, hTreeN0.trans hG0nEq.symm,
      ⟨tok.trees, tok.free, tok.depth, hLct0, hNum0,
        hGr0.symm ▸ namedSlots_congr_slot hNamed0
          (fun ei hei => hS6OfTag (hT9 ei (hG0Cap ei (hOldSub hei))) (by omega))
          (fun sl _ his => hS6OfTag (hT10 sl (by unfold isEdgeSlot at his; omega)) (by omega)),
        hGr0.symm ▸ liveAccounts_congr_slot hLive0
          (fun ei hei => hS6OfTag (hT9 ei (hG0Cap ei (hOldSub hei))) (by omega))⟩,
      (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC tok.treeHeap tok.tree tok.treeTok
        mem0 s6.mem (fun a ha => (hS6OfTag (hT16 a ha) (by omega)).symm)).1 hTreeRep0,
      fun ei hei => by
        obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei (hOldSub hei)
        have hAcc := hAccounts0.1 (model.intToExt ei) heExt
        have hei' : ei ∈ model.chain.toTreeChain.chainTree.E := hei
        rw [heMap] at hAcc; simp only [hei', ↓reduceIte] at hAcc
        have hS := hS6OfTag (hT9 ei (hG0Cap ei (hOldSub hei))) (by omega)
        have hT := hS6OfTag (hT12 ei (hG0Cap ei (hOldSub hei))) (by omega)
        rw [hS, hT]; exact (hS6OfTag (hT11 _ (by unfold isEdgeSlot at hAcc; omega)) (by omega)).trans hAcc.2.2.2.2.2.1,
      fun ei heiG hnot => by
        obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
        have hAcc := hAccounts0.1 (model.intToExt ei) heExt
        have hnot' : ei ∉ model.chain.toTreeChain.chainTree.E := hnot
        rw [heMap] at hAcc; simp only [hnot', ↓reduceIte] at hAcc
        exact (hS6OfTag (hT9 ei (hG0Cap ei heiG)) (by omega)).trans hAcc.2.2.1,
      fun ei heiG hnot => by
        obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
        have hrec := (hCanonExt (model.intToExt ei) heExt).2.2.2.2.2.2.2.2.2 (heMap.symm ▸ hnot)
        rw [heMap] at hrec
        rw [hS6OfTag (hT13 ei (hG0Cap ei heiG)) (by omega)]
        exact hrec.congr (fun a ha1 ha2 => by
          have ht := (hT1718 (model.intToExt ei) heExt).2 (heMap.symm ▸ hnot) (a - mem0 (tok.edgeRecords + ei)) (by omega)
          rw [heMap, show mem0 (tok.edgeRecords + ei) + (a - mem0 (tok.edgeRecords + ei)) = a by omega] at ht
          exact hS6OfTag ht (by omega)),
      fun ei heiG hnot _ hdet => by
        obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
        have hAcc := hAccounts0.1 (model.intToExt ei) heExt
        have hnot' : ei ∉ model.chain.toTreeChain.chainTree.E := hnot
        rw [heMap] at hAcc; simp only [hnot', ↓reduceIte] at hAcc
        obtain ⟨v, acc, hpa, _, _, _, hpush⟩ := hAcc.2.2.2
        have hrec := (hCanonExt (model.intToExt ei) heExt).2.2.2.2.2.2.2.2.2 (heMap.symm ▸ hnot)
        rw [heMap] at hrec
        have hveq : v.detector = (canonVal ei).detector := by
          have h1 := hpa.2.2.2.2.2.2; have h2 := hrec.2.2.2.2.2.2; omega
        exact (hS6OfTag (hT15 ei (hG0Cap ei heiG)) (by omega)).trans (hpush (hveq.symm ▸ hdet)),
      fun _ _ hnot => ⟨fun h => absurd h hnot, fun _ => rfl⟩,
      fun e1 h1G e2 h2G hne hnot1 hnot2 => by
        obtain ⟨hm1, he1⟩ := hFreshInv.hRight e1 h1G; obtain ⟨hm2, he2⟩ := hFreshInv.hRight e2 h2G
        rw [hS6OfTag (hT13 e1 (hG0Cap e1 h1G)) (by omega), hS6OfTag (hT13 e2 (hG0Cap e2 h2G)) (by omega)]
        have hd := hOffInv0.2 _ he1 _ he2 (fun h => hne (hm1.symm.trans (h ▸ hm2))) (hm1.symm ▸ hnot1) (hm2.symm ▸ hnot2)
        rwa [hm1, hm2] at hd,
      (hS6OfTag (hT1 11 (by omega)) (by omega)).trans (by simpa using hRootDir0 11 (by simp)),
      ⟨hOffReady0.1,
       fun j hj => by
         have hCntLe := hOffReady0.1
         rw [hS6OfTag (hT14 j (by omega)) (by omega)]
         exact ⟨(hOffReady0.2.1 j hj).1, (hS6OfTag (hT15 _ (hOffReady0.2.1 j hj).1) (by omega)).trans (hOffReady0.2.1 j hj).2⟩,
       fun j1 hj1 j2 hj2 hne => by
         have hCntLe := hOffReady0.1
         rw [hS6OfTag (hT14 j1 (by omega)) (by omega), hS6OfTag (hT14 j2 (by omega)) (by omega)]
         exact hOffReady0.2.2.1 j1 hj1 j2 hj2 hne,
       fun e he => by rw [hS6OfTag (hT15 e he) (by omega)]; exact hOffReady0.2.2.2.1 e he,
       fun e he h1 => by
         have hCntLe := hOffReady0.1
         rw [hS6OfTag (hT15 e he) (by omega)] at h1
         obtain ⟨j, hj, hje⟩ := hOffReady0.2.2.2.2 e he h1
         exact ⟨j, hj, (hS6OfTag (hT14 j (by omega)) (by omega)).trans hje⟩⟩⟩
  obtain ⟨s7, cLoop, curTree1, curTreeTok1, heapSync, curOffCnt1, rLoop, hInv1End, hcLoop⟩ :=
    wireTreeSyncLoop_defer_runs hCtx1 hInv1Init
  have hS7Regs : ∀ r, 70 ≤ r → s7.regs r = st.regs r := fun r hr =>
    (runs_regs_ge_of_noWriteGe rLoop (wireTreeSyncLoop_noWriteGe70 _ _ _ _ _ _) r hr).trans (hS6Regs r hr)
  have hPhiTree0 : Rtree.phi tok.treeHeap tok.treeTok s6.mem = Rtree.phi tok.treeHeap tok.treeTok mem0 :=
    (LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC tok.treeHeap tok.tree tok.treeTok
      mem0 s6.mem (fun a ha => (hS6OfTag (hT16 a ha) (by omega)).symm)).2
  obtain ⟨_, _, _, _, h7_3, _, _, _, _, _, _, _, _, _, _, _, _, hHSLo, hHSHi, hz7, hTreeFoot7, hFr7,
    hTreeN7, ⟨curTrees1, curFree1, curDepth1, hLct1, hNum1, hNamed1, hLive1⟩, hTreeRep7,
    _, _, hOffRec7, _, hOffWhere7, hOffDisj7, _, _⟩ := hInv1End
  have hApplyEmp : applyTreeChanges oldF.E edits1 = ∅ := hDiff1.result.2
  rw [hApplyEmp] at hNamed1 hLive1 hOffRec7 hOffWhere7 hOffDisj7
  let s8 := { s7 with regs := Function.update s7.regs 4 heapSync }
  have r8 : Runs w p ω (.assign 4 (.reg 3)) s7 .normal s8 2 :=
    runs_assign_iff.mpr ⟨heapSync, by simp [Expr.eval, h7_3], rfl, rfl, rfl⟩
  -- Step 4: `wireZeroSlotsStmt`
  have hS8_root (j : ℕ) (hj : j < 16) (h11 : j ≠ 11) : s8.mem (root + j) = mem0 (root + j) :=
    (hFr7 (root + j) (by dsimp [heap0Sync, editsBuf1]; omega) (by omega)
      (by rw [hT1 j hj]; decide) (by rw [hT1 j hj]; decide) (by rw [hT1 j hj]; decide)
      (by rw [hT1 j hj]; decide) (by rw [hT1 j hj]; decide) (by rw [hT1 j hj]; decide)
      (by rw [hT1 j hj]; decide)).trans (hs6Mem.symm ▸ hLoadRoot j hj)
  have hSlotsW : tok.slots + tok.intCap < 2 ^ w := by
    have := htagLt (by rw [hT9 (tok.intCap - 1) (by omega)]; decide); omega
  obtain ⟨s9, cZero, rZero, hcZero, hSlotsZero9, hFrZero9, hRegsZero9⟩ :=
    wireZeroSlotsStmt_runs (w := w) (root := root) (slots := tok.slots) (intCap := tok.intCap)
      (p := p) (ω := ω) (st := s8)
      (by simp [s8, hS7Regs 70 (by decide), hRegs.2.1])
      ((hS8_root 6 (by omega) (by decide)).trans (by simpa using hRootDir0 6 (by simp)))
      ((hS8_root 15 (by omega) (by decide)).trans (by simpa using hRootDir0 15 (by simp)))
      (by omega) hSlotsW (by omega)
  have hS9EqS7 {a : ℕ} (h : a < tok.slots ∨ tok.slots + tok.intCap ≤ a) : s9.mem a = s7.mem a := hFrZero9 a h
  have hNot9OfTag {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 9) : a < tok.slots ∨ tok.slots + tok.intCap ≤ a := by
    by_contra h; push Not at h
    have := hT9 (a - tok.slots) (by omega)
    rw [show tok.slots + (a - tok.slots) = a by omega, ht] at this; exact hv this
  have hNot9OfGe {a : ℕ} (ha : heap1 ≤ a) : a < tok.slots ∨ tok.slots + tok.intCap ≤ a := by
    have hEnd : tok.slots + tok.intCap ≤ uIntBuf := by
      have := htagLt (by rw [hT9 (tok.intCap - 1) (by omega)]; decide); omega
    exact Or.inr (by omega)
  have hS9EqS6 {a : ℕ} (ha : a < heap0Sync) (hne11 : a ≠ root + 11)
      (ht9 : tok.tag a ≠ 9) (ht10 : tok.tag a ≠ 10) (ht11 : tok.tag a ≠ 11)
      (ht13 : tok.tag a ≠ 13) (ht14 : tok.tag a ≠ 14) (ht15 : tok.tag a ≠ 15) (ht16 : tok.tag a ≠ 16) :
      s9.mem a = s6.mem a :=
    (hS9EqS7 (a := a) (by
      by_contra h; push Not at h; have := hT9 (a - tok.slots) (by omega)
      rw [show tok.slots + (a - tok.slots) = a by omega] at this; exact ht9 this)).trans
      (hFr7 a ha hne11 ht9 ht10 ht11 ht13 ht14 ht15 ht16)
  have hS9Regs : ∀ r, 70 ≤ r → s9.regs r = st.regs r := fun r hr =>
    (hRegsZero9 r (Or.inr hr)).trans (by simp [s8, Function.update_of_ne (by omega : r ≠ 4), hS7Regs r hr])
  have hS9R4 : s9.regs 4 = heapSync := (hRegsZero9 4 (Or.inl rfl)).trans (by simp [s8])
  -- Step 5: `wireRefreshAndUpdateRoot_runs`
  have hTagEmpty (a : ℕ) (h1 : emptyPtrs ≤ a) (h2 : a < emptyPtrs + cnt) : tok.tag a = 0 := by
    by_contra hne; have := htagLt hne; dsimp [emptyPtrs] at h1; omega
  have hS9Mem0 : ∀ a < uIntBuf, a ≠ root + 11 →
      tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 →
      tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 →
      tok.tag a ≠ 13 → tok.tag a ≠ 14 → tok.tag a ≠ 15 → tok.tag a ≠ 16 →
      (∀ j < d, tok.tag a ≠ 21 + j) → s9.mem a = mem0 a := by
    intro a ha hne11 h6 h7 h8 h9 h10 h11 h13 h14 h15 h16 hC
    exact (hS9EqS6 (by dsimp [heap0Sync, editsBuf1]; omega) hne11 h9 h10 h11 h13 h14 h15 h16).trans
      (hs6Mem.symm ▸ hS4EqMem0 ha h6 h7 h8 hC)
  have hS9MemFresh : ∀ a < heap,
      (tok.tag a = 6 ∨ tok.tag a = 7 ∨ tok.tag a = 8 ∨ uIntBuf ≤ a) → s9.mem a = mem a := by
    intro a ha hcase
    have hTagNot : tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧
        tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16 ∧ a ≠ root + 11 ∧
        ∀ j < d, ¬ Rcore.foot (tok.coreHandle j) (tok.coreTok j) a := by
      rcases hcase with h | h | h | h
      · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          fun he => by rw [he, hT1 11 (by omega)] at h; omega, fun j hj hf => by have := hT21 j hj a hf; omega⟩
      · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          fun he => by rw [he, hT1 11 (by omega)] at h; omega, fun j hj hf => by have := hT21 j hj a hf; omega⟩
      · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          fun he => by rw [he, hT1 11 (by omega)] at h; omega, fun j hj hf => by have := hT21 j hj a hf; omega⟩
      · have ht0 : tok.tag a = 0 := by by_contra hne; have := htagLt hne; omega
        exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          fun he => by rw [he, hT1 11 (by omega)] at ht0; omega,
          fun j hj hf => by have := hFootLt a (Or.inr (Or.inr ⟨j, hj, hf⟩)); omega⟩
    exact (hS9EqS6 (by dsimp [heap0Sync, editsBuf1]; omega) hTagNot.2.2.2.2.2.2.2.1
      hTagNot.1 hTagNot.2.1 hTagNot.2.2.1 hTagNot.2.2.2.1 hTagNot.2.2.2.2.1
      hTagNot.2.2.2.2.2.1 hTagNot.2.2.2.2.2.2.1).trans
      (hs6Mem.symm ▸ (hS4EqS1 a (by omega)).trans ((hFrFill a (Or.inl (by omega))).trans
        (hStFrame a ha hTagNot.2.2.2.2.2.2.2.2)))
  have hSync1Le : heapSync ≤ heap1 + 3 * tok.intCap + sumOld * (2 + wireTreeSyncEditSpace L) := by
    have h1 : 2 * edits1.length + edits1.length * wireTreeSyncEditSpace L =
        edits1.length * (2 + wireTreeSyncEditSpace L) := by ring
    have h2 : edits1.length * (2 + wireTreeSyncEditSpace L) ≤ sumOld * (2 + wireTreeSyncEditSpace L) :=
      Nat.mul_le_mul_right _ hEdits1Le
    dsimp [heap0Sync, editsBuf1] at hHSHi; omega
  have hETEnd : tok.edgeThresholds + tok.intCap ≤ uIntBuf := by
    have := htagLt (by rw [hT12 (tok.intCap - 1) (by omega)]; decide); omega
  have hEREnd : tok.edgeRecords + tok.intCap ≤ uIntBuf := by
    have := htagLt (by rw [hT13 (tok.intCap - 1) (by omega)]; decide); omega
  have hOldLenEnd : mem0 (solverLevelMetaAddr tok.table cfg.P.d) + ec0 * L ≤ uIntBuf := by
    by_cases h0 : ec0 * L = 0
    · obtain ⟨_, _, _, _, hOwn0, _, _⟩ := hMeta0.2.2.2.2.2 0 hModelInv.1.1
      have hOwn0' : tok.owned (mem0 (solverLevelMetaAddr tok.table cfg.P.d)) := by simpa using hOwn0
      have := hFootLt (mem0 (solverLevelMetaAddr tok.table cfg.P.d)) (Or.inl hOwn0'); omega
    · have hTagL0 : ∀ a, mem0 (solverLevelMetaAddr tok.table cfg.P.d) ≤ a →
          a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) + ec0 * L → tok.tag a = 23 + d := hLevel0Meta.2.1
      have := htagLt (by rw [hTagL0 (mem0 (solverLevelMetaAddr tok.table cfg.P.d) + ec0 * L - 1) (by omega) (by omega)]; omega); omega
  have hNotMutOfTag {a v : ℕ} (ht : tok.tag a = v) (h12 : v ≠ 12) (h13 : v ≠ 13) :
      ¬ InRefreshMutable tok.edgeThresholds tok.edgeRecords tok.intCap a := by
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have := hT12 (a - tok.edgeThresholds) (by omega)
      rw [show tok.edgeThresholds + (a - tok.edgeThresholds) = a by omega, ht] at this; exact h12 this
    · have := hT13 (a - tok.edgeRecords) (by omega)
      rw [show tok.edgeRecords + (a - tok.edgeRecords) = a by omega, ht] at this; exact h13 this
  have hOffSynced9 :
      (∀ ei ∈ G0.E, (Update.delete ei ∈ U_int ∨ ei ∉ (∅ : Finset ℕ)) →
        PathEdgeAt s9.mem (s9.mem (tok.edgeRecords + ei)) 4 L (some (canonVal ei)) ∧
        s9.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ heapSync ∧
        (∀ j < 2 + 4 * L, ¬ InRefreshMutable tok.edgeThresholds tok.edgeRecords tok.intCap
          (s9.mem (tok.edgeRecords + ei) + j) ∧
          (s9.mem (tok.edgeRecords + ei) + j < tok.rootGraph ∨
            tok.rootGraph + dynGraphSize model.extG.n tok.rootECap ≤ s9.mem (tok.edgeRecords + ei) + j) ∧
          (s9.mem (tok.edgeRecords + ei) + j < mem0 (solverLevelMetaAddr tok.table cfg.P.d) ∨
            mem0 (solverLevelMetaAddr tok.table cfg.P.d) + ec0 * L ≤ s9.mem (tok.edgeRecords + ei) + j))) ∧
      (∀ e₁ ∈ G0.E, ∀ e₂ ∈ G0.E, e₁ ≠ e₂ → e₁ ∉ (∅ : Finset ℕ) → e₂ ∉ (∅ : Finset ℕ) →
        s9.mem (tok.edgeRecords + e₁) + (2 + 4 * L) ≤ s9.mem (tok.edgeRecords + e₂) ∨
        s9.mem (tok.edgeRecords + e₂) + (2 + 4 * L) ≤ s9.mem (tok.edgeRecords + e₁)) := by
    have hRec9 (ei : ℕ) (hei : ei ∈ G0.E) : s9.mem (tok.edgeRecords + ei) = s7.mem (tok.edgeRecords + ei) :=
      hS9EqS7 (hNot9OfTag (hT13 ei (hG0Cap ei hei)) (by decide))
    refine ⟨fun ei hei _ => ?_, fun e1 h1 e2 h2 hne _ _ => by
      rw [hRec9 e1 h1, hRec9 e2 h2]; exact hOffDisj7 e1 h1 e2 h2 hne (by simp) (by simp)⟩
    rw [hRec9 ei hei]
    have hRec7 := hOffRec7 ei hei (by simp)
    by_cases hOld : ei ∈ oldF.E
    · obtain ⟨hlo, hhi, _⟩ := (hOffWhere7 ei hei (by simp)).1 hOld
      refine ⟨hRec7.congr (fun a ha1 ha2 => hS9EqS7 (hNot9OfGe (by dsimp [heap0Sync, editsBuf1] at hlo; omega))),
        hhi, fun j hj => ⟨fun hm => by rcases hm with ⟨_, _⟩ | ⟨_, _⟩ <;> (dsimp [heap0Sync, editsBuf1] at hlo; omega),
          Or.inr (by dsimp [heap0Sync, editsBuf1] at hlo; omega),
          Or.inr (by dsimp [heap0Sync, editsBuf1] at hlo; omega)⟩⟩
    · have hEq0 : s7.mem (tok.edgeRecords + ei) = mem0 (tok.edgeRecords + ei) :=
        ((hOffWhere7 ei hei (by simp)).2 hOld).trans (hS6OfTag (hT13 ei (hG0Cap ei hei)) (by omega))
      obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei hei
      have hTag18 (j : ℕ) (hj : j < 2 + 4 * L) : tok.tag (mem0 (tok.edgeRecords + ei) + j) = 18 := by
        have := (hT1718 (model.intToExt ei) heExt).2 (heMap.symm ▸ hOld) j hj; rwa [heMap] at this
      rw [hEq0] at hRec7 ⊢
      refine ⟨hRec7.congr (fun a ha1 ha2 => by
          have hta : tok.tag a = 18 := by
            have := hTag18 (a - mem0 (tok.edgeRecords + ei)) (by omega)
            rwa [show mem0 (tok.edgeRecords + ei) + (a - mem0 (tok.edgeRecords + ei)) = a by omega] at this
          exact hS9EqS7 (hNot9OfTag hta (by decide))),
        by have := htagLt (by rw [hTag18 (2 + 4 * L - 1) (by omega)]; decide); omega,
        fun j hj => ?_⟩
      have ht := hTag18 j hj
      exact ⟨hNotMutOfTag ht (by decide) (by decide),
        by by_contra h; push Not at h; have := hT20 _ h.1 h.2; rw [ht] at this; omega,
        by by_contra h; push Not at h; have := hLevel0Meta.2.1 _ h.1 h.2; rw [ht] at this; omega⟩
  obtain ⟨s10, cRefAll, heap2, newCanonVal, rRefAll, hcRefAll, h10_4, hH2Lo, hH2Hi, hz10, h10Regs,
      hDG10, hLen10, hFr10, _, hAcc10, hDisjRec10, hDisjThrRec10⟩ :=
    wireRefreshAndUpdateRoot_runs (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (wordExp := wordExp) (stretchPrec := stretchPrec)
      (refreshAccountsProc := refreshAccountsProc) (shift := shift) (negate := negate)
      (refreshOneProc := refreshOneProc) (divide := divide) (add := add) (sub := sub)
      (copy := copy) (isNeg := isNeg) (dgApply := dgApply) (updateLen0Proc := updateLen0Proc)
      (root := root) (uIntBuf := uIntBuf) (editsPtr := editsPtr) (g := g) (l := l) (heap := heap)
      (heapSync := heapSync) (ec0 := ec0) (cfg := cfg) (Rcore := Rcore) (p := p) (ω := ω)
      (mem0 := mem0) (mem := mem) (st := s9) (model := model) (tok := tok) (U := U) (B := B)
      (curE := ∅) (canonVal := canonVal)
      hRefAccProc hRefOneProc hUpdLen0Proc hshift hdiv hadd hsub hneg hcopy hIsNegOk hDGApplyRoot
      hRep0_keep hMeta0 hModelInv hRef hFreshMem hTrNfLe hBatchMem hSmallMem hFootLt hGLt hLLt
      hULeEd hEdLeHeap (by dsimp [heap0Sync, editsBuf1] at hHSLo; omega) hLpos hPword hw18
      hLevel0Meta (fun e he => by
        obtain ⟨hf, hg, hl, hfl, hd, h1, h2, h3, h4, _⟩ := hCanonExt e he
        exact ⟨hf, hg, hl, hfl, hd, h1, h2, h3, h4⟩)
      ⟨hS9R4, (hS9Regs 70 (by decide)).trans hRegs.2.1,
       (hS9Regs 83 (by decide)).trans hRegs.2.2.2.2.2.2.1,
       (hS9Regs 87 (by decide)).trans hRegs.2.2.2.2.2.2.2.1,
       (hS9Regs 90 (by decide)).trans hRegs.2.2.2.2.2.2.2.2.1,
       (hS9Regs 91 (by decide)).trans hRegs.2.2.2.2.2.2.2.2.2.1,
       (hS9Regs 94 (by decide)).trans hRegs.2.2.2.2.2.2.2.2.2.2.2.2⟩
      (fun a ha => (hS9EqS7 (hNot9OfGe (by dsimp [heap0Sync, editsBuf1] at hHSLo; omega))).trans (hz7 a ha))
      hS9Mem0 hS9MemFresh hOffSynced9 (by omega)
  -- Compose full run and verify post-state
  have hS10EqS7_tree (a : ℕ) (ha : Rtree.foot tok.treeHeap curTreeTok1 a) : s10.mem a = s7.mem a := by
    rcases hTreeFoot7 a ha with h0 | ⟨hlo, hhi⟩
    · have h16 := hT16 a h0
      exact (hFr10 a (lt_of_lt_of_le (htagLt (by rw [h16]; decide)) (by dsimp [heap0Sync, editsBuf1] at hHSLo; omega))
        (hNotMutOfTag h16 (by decide) (by decide))
        (by by_contra h; push Not at h; have := hT20 a h.1 h.2; rw [h16] at this; omega)
        (by by_contra h; push Not at h; have := hLevel0Meta.2.1 a h.1 h.2; rw [h16] at this; omega)).trans
        (hS9EqS7 (hNot9OfTag h16 (by decide)))
    · exact (hFr10 a hhi (fun hm => by rcases hm with ⟨_, _⟩ | ⟨_, _⟩ <;> (dsimp [heap0Sync, editsBuf1] at hlo; omega))
        (Or.inr (by dsimp [heap0Sync, editsBuf1] at hlo; omega))
        (Or.inr (by dsimp [heap0Sync, editsBuf1] at hlo; omega))).trans
        (hS9EqS7 (hNot9OfGe (by dsimp [heap0Sync, editsBuf1] at hlo; omega)))
  have hTreeLoc10 := LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC
    tok.treeHeap curTree1 curTreeTok1 s7.mem s10.mem (fun a ha => (hS10EqS7_tree a ha).symm)
  have hTreeRep10 : Rtree.rep tok.treeHeap curTree1 curTreeTok1 s10.mem := hTreeLoc10.1 hTreeRep7
  have hTreePhi10 : Rtree.phi tok.treeHeap curTreeTok1 s10.mem = Rtree.phi tok.treeHeap curTreeTok1 s7.mem := hTreeLoc10.2
  have hSlotsZero10 (j : ℕ) (hj : j < tok.intCap) : s10.mem (tok.slots + j) = 0 := by
    have h9 := hT9 j hj
    exact (hFr10 (tok.slots + j) (lt_of_lt_of_le (htagLt (by rw [h9]; decide)) (by dsimp [heap0Sync, editsBuf1] at hHSLo; omega))
      (hNotMutOfTag h9 (by decide) (by decide))
      (by by_contra h; push Not at h; have := hT20 _ h.1 h.2; rw [h9] at this; omega)
      (by by_contra h; push Not at h; have := hLevel0Meta.2.1 _ h.1 h.2; rw [h9] at this; omega)).trans
      (hSlotsZero9 j hj)
  have hNamed10 : TreeEditNamedSlots curTree1 curTrees1 { G0' with E := ∅ }
      (fun ei => s10.mem (tok.slots + ei)) (fun sl => s10.mem (tok.names + sl)) :=
    ⟨fun _ h => by simp at h, fun sl hsl his => by
      obtain ⟨he, _⟩ := hNamed1.inverse sl hsl his; simp at he, fun _ h => by simp at h⟩
  have hLive10 : TreeEditLiveAccounts curTree1 curTrees1 { G0' with E := ∅ }
      (fun ei => s10.mem (tok.slots + ei)) newCanonVal := fun _ h => by simp at h
  have rAll : Runs w p ω (wireBranchASync1AndPrepStmt packEditsProc (opTree 4) (opTree 1) (opTree 0)
      bind canonCopy isNeg refreshAccountsProc dgApply updateLen0Proc) st .normal s10 _ :=
    runs_seq_iff.mpr (Or.inr ⟨s1, cFill, _, rFill,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 6, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 5 + cPack + 1, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5a, 2, _, r5a,
      runs_seq_iff.mpr (Or.inr ⟨s5b, 2, _, r5b,
      runs_seq_iff.mpr (Or.inr ⟨s6, cSetup, _, rSetup,
      runs_seq_iff.mpr (Or.inr ⟨s7, cLoop, _, rLoop,
      runs_seq_iff.mpr (Or.inr ⟨s8, 2, _, r8,
      runs_seq_iff.mpr (Or.inr ⟨s9, cZero, _, rZero, rRefAll, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hGeU_eq (a : ℕ) (hlo : uIntBuf ≤ a) (hhi : a < heap1) : s10.mem a = s1.mem a := by
    have ht0 : tok.tag a = 0 := by by_contra hne; have := htagLt hne; omega
    refine (hFr10 a (by dsimp [heap0Sync, editsBuf1] at hHSLo; omega)
      (fun hm => by rcases hm with ⟨_, _⟩ | ⟨_, _⟩ <;> omega) (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((hS9EqS6 (by dsimp [heap0Sync, editsBuf1]; omega) (fun h => by rw [h, hT1 11 (by omega)] at ht0; omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (hs6Mem.symm ▸ hS4EqS1 a hhi))
  refine ⟨s10, _, heapSync, heap2, curTree1, curTrees1, curFree1, curDepth1, curTreeTok1,
    newCanonVal, rAll, ?_, h10_4, by dsimp [heap0Sync, editsBuf1] at hHSLo; omega, hSync1Le,
    hH2Lo, hH2Hi, hz10, fun r hr => (h10Regs r hr).trans (hS9Regs r hr),
    fun j hj => (hGeU_eq (emptyPtrs + j) (by dsimp [emptyPtrs]; omega) (by dsimp [emptyPtrs]; omega)).trans (hFillPtrs j hj),
    fun j hj => (hGeU_eq (emptyGraphPtr + j) (by dsimp [emptyGraphPtr]; omega) (by dsimp [emptyGraphPtr]; omega)).trans
      ((hFrFill (emptyGraphPtr + j) (Or.inr (by dsimp [emptyGraphPtr, emptyPtrs]; omega))).trans (hEmptyZero j hj)),
    hTreeN7.trans hG0nEq, hLct1, hNum1, hNamed10, hLive10, hTreeRep10,
    fun a ha => (hTreeFoot7 a ha).imp id (fun ⟨h1, h2⟩ => ⟨by dsimp [heap0Sync, editsBuf1] at h1; omega, h2⟩),
    hSlotsZero10, hDG10, hLen10, ?_, ?_,
    fun e1 h1 e2 h2 hne => hDisjRec10 e1 h1 e2 h2 hne (by simp) (by simp), hDisjThrRec10⟩
  · dsimp [Rtree] at hTreePhi10 hPhiTree0 hcLoop ⊢
    rw [hTreePhi10]; rw [hPhiTree0] at hcLoop
    have hmul : edits1.length * (wireTreeSyncEditCost L drainUnit + 2) ≤
        sumOld * (wireTreeSyncEditCost L drainUnit + 2) := Nat.mul_le_mul_right _ hEdits1Le
    dsimp [cnt, sumOld] at hcLoop hcPack hcFill hmul ⊢; omega
  · intro a ha hne11 hNotE h9 h10 h11 h12 h13 h14 h15 h16 h20 hNotL0
    exact (hFr10 a (by dsimp [heap0Sync, editsBuf1] at hHSLo; omega)
      (hNotMutOfTag rfl h12 h13)
      (by by_contra h; push Not at h; exact h20 (hT20 a h.1 h.2)) hNotL0).trans
      ((hS9EqS6 (by dsimp [heap0Sync, editsBuf1]; omega) hne11 h9 h10 h11 h13 h14 h15 h16).trans
        (hs6Mem.symm ▸ (hS4EqS1 a ha).trans (hFrFill a (by dsimp [emptyPtrs, emptyGraphPtr, cnt] at hNotE ⊢; omega))))
  · intro e he
    obtain ⟨hThr, hFwd, hgB, hlB, hflB, hdB, hFl, hGr, hLn, hAcc, hIn, hOut⟩ := hAcc10 e he
    set ei := tr.2.1 e
    refine ⟨hThr, ?_, hFwd, hgB, hlB, hflB, hdB, hFl, hGr, hLn, hAcc, fun heiG0 => ?_, fun hNot => ?_⟩
    · by_cases hG : ei ∈ G0.E
      · exact (hIn hG).2.2.2 (by simp)
      · exact (hOut hG).2.2.2.2
    · obtain ⟨_, hT, hR, _⟩ := hIn heiG0
      have hRec9 : s9.mem (tok.edgeRecords + ei) = s7.mem (tok.edgeRecords + ei) :=
        hS9EqS7 (hNot9OfTag (hT13 ei (hG0Cap ei heiG0)) (by decide))
      refine ⟨hT, ⟨fun hOld => ?_, fun hNotOld => ?_⟩⟩
      · obtain ⟨hlo, hhi, hnf⟩ := (hOffWhere7 ei heiG0 (by simp)).1 hOld
        rw [hR, hRec9]
        exact ⟨by dsimp [heap0Sync, editsBuf1] at hlo; omega, hhi, hnf⟩
      · rw [hR, hRec9]
        exact ((hOffWhere7 ei heiG0 (by simp)).2 hNotOld).trans (hS6OfTag (hT13 ei (hG0Cap ei heiG0)) (by omega))
    · obtain ⟨h1, h2, h3, h4, _⟩ := hOut hNot
      exact ⟨h1, h2, h3, h4⟩

end MinCostFlow.MinRatio
