module

public import MinCostFlow.MinRatio.WireChainCoreBranchBTopGoalKFBL

/-!
# The facts after the parts of Branch B, as named propositions (`WireChainCoreBranchBPartsKFBL`)

The run lemmas of the parts of Branch B end in long conclusions with witnesses. The top theorem
of Branch B and the goals of its fields read these facts at the witnesses, so this file names them.
Each definition is the conclusion of its run lemma, with the witnesses as parameters, so the
conclusion of the run lemma unfolds to `∃ witnesses, definition`.

* `BranchBStartKFBL`: the premises of `OrdChainCoreBranchBPostKFBL` at a start state, except the
  two bounds `B ≤ B_bound` and `R ≤ R_bound`, which no run lemma reads.
* `BranchBPrefixFactsKFBL`: the conclusion of `wireBranchBPrefixKFBL_runs`.
* `BranchBLoopExitAtKFBL`: the body of `BranchBLoopExitKFBL`, with `BranchBLoopExitKFBL.exists_at`.
* `BranchBSuffixFactsKFBL`: the conclusion of `wireBranchBSuffixKFBL_runs` without its first
  conjunct (the records of the cut edges of the tree).
* `BranchBExitCaseKFBL`: what each of the three exits gives besides `BranchBExitOutKFBL`: the
  case, the run of the exit, its heap and its cost (the conclusions of the two exit goals and of
  `wireBranchBTermEmpty_exitOut`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The premises of `OrdChainCoreBranchBPostKFBL` at the start state of the core (the memory of
the solver rep `mem0`, the memory `mem` at the call, the model `model`, the token `tok`, the outer
batch `U`), without the two bounds `B ≤ B_bound` and `R ≤ R_bound`. -/
structure BranchBStartKFBL (w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp
    stretchPrec intCapMax forestEdgeCap vCap eCap : ℕ) (cfg : Alg2Config) (G : MGraph)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (coreSpace : ℕ → ℕ)
    (root uIntBuf editsPtr editWords g l heap : ℕ) (mem0 mem : ℕ → ℕ) (model : Alg2State cfg)
    (tok : SolverToken cfg L Rcore) (U : List Update) (B R : ℤ) : Prop where
  rep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0
  meta0 : SolverLevelMetaAt P V model tok mem0
  caps0 : SolverLevelCapsAt vCap eCap model tok mem0
  intCapEq : tok.intCap = initTargetCap cfg G
  extM : model.extG.m = m
  num0 : PathTreeNumericInv tok.tree tok.trees B R
  offInv0 : OffTreeRecInv model L mem0 tok.edgeRecords B
  offBd0 : OffTreeRecBound model L mem0 tok.edgeRecords B
  shiftInv : Chain.Ordered.ShiftLoopChainInv cfg model.chain
  wire : WireCapFacts capExp limbMul L capLimit model
  bran : ∀ j < cfg.P.d, model.chain.bran j < cfg.P.k
  modelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B
  modelInvKFBL : UpdateCoreModelInvKFBL model U
    (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
    (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)
  intCapLe : tok.intCap ≤ intCapMax
  forestCap : graphListEdgeSum (chainSuffixForests model.chain 0) +
    graphListEdgeSum (chainSuffixForests (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain 0) ≤
      forestEdgeCap
  logW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L
  capT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ)
  memEq : ∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a
  fresh : FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
    (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1
    (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1
    (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.1
  trNf : (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.1 ≤
    tok.intCap
  batch : BatchAt mem uIntBuf
    (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2
  small : SmallBatchAt mem uIntBuf (model.chain.G 0)
    (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2
    (editsPtr - cfg.P.d - uIntBuf)
  edits : OrdEditsAt mem editsPtr (batchToOrdEdits
    (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2) editWords
  editsW : ∀ j < editWords, mem (editsPtr + j) < 2 ^ w
  edHeap : editsPtr + editWords = heap
  refresh : RefreshBatch model.extG U
  footLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
    a < uIntBuf
  gLt : g + m * L ≤ uIntBuf
  lLt : l + m * L ≤ uIntBuf
  uLe : uIntBuf + cfg.P.d ≤ editsPtr
  zero : ZeroFrom mem heap
  room : heap + coreSpace U.length < 2 ^ w
  noFire : ¬ intRebuildThreshold cfg.P cfg.N₀ 0 < model.chain.updCount 0 +
    (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2.length

/-- The facts after the start of Branch B, at the end state `out` of the run from `st`: the
conclusion of `wireBranchBPrefixKFBL_runs`, with its witnesses as parameters. -/
@[expose] def BranchBPrefixFactsKFBL (w L P m drainUnit collectDel emitCuts bind canonCopy isNeg
    zeroIns refreshAccountsProc updateLen0Proc root uIntBuf g l heap ec0 forestPtr : ℕ)
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (p : Program) (opTree : ℕ → ℕ)
    (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ) (st : State) (model : Alg2State cfg)
    (tok : SolverToken cfg L Rcore) (U : List Update) (B R : ℤ) (out : State)
    (cost hS1 heap2 : ℕ) (memS1 : ℕ → ℕ) (curTree' : PathTreeState)
    (curTreeTok' : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (offCnt' : ℕ)
    (canonVal newCanonVal : ℕ → PathEdgeValue) : Prop :=
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
      (Rtree.phi tok.treeHeap tok.treeTok mem0 + tok.offReadyCount * drainUnit)

/-- The facts at the exit of the plain-step loop of Branch B with the witnesses of
`BranchBLoopExitKFBL` as parameters. -/
@[expose] def BranchBLoopExitAtKFBL (w L P depth vCap eCap capExp dgApply copyProc updLen slotProc
    wordExp stretchPrec N0 : ℕ) (fmt : Num.Format w) (cfg : Alg2Config)
    (Psc : SparseCoreOrdParams) (reembFn : ToolReembFn cfg.T)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (RL : DSRep (ℕ × (ℕ → LSF))) (p : Program)
    (opCore : ℕ → ℕ) (ω : ℕ → Bool) (A : BranchBAddrs) (origLen : ℕ → ℕ → ℝ) (ℓ' g' : ℕ → ℝ)
    (BWc EWc ULc stepSpace : ℕ → ℕ) (ch0 : ChainState cfg.T cfg.P) (termTok : RL.τ)
    (rem idx : ℕ) (ch : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update)
    (curEnc : ℕ) (st : State) (tok : ℕ → Rcore.τ) (levelUS : ℕ → List Update)
    (D : ℕ → LevelDiffLists) (i₀ : ℕ) (sE sF : State) (cost : ℕ) (chE : ChainState cfg.T cfg.P)
    (curGE : MGraph) (curUE : List Update) (curEditsE : List OrdEdit) (curEncE : ℕ)
    (oldOrdE : ℕ → List End) (tokE : ℕ → Rcore.τ) (bE bWE eE eWE : ℕ)
    (levelUE levelUSE : ℕ → List Update) (DE : ℕ → LevelDiffLists) : Prop :=
  Runs w p ω (wireBranchBLoopKFBL (opCore 0) (opCore 2) dgApply copyProc updLen slotProc)
    st .normal sF cost ∧
  idx ≤ i₀ ∧ i₀ ≤ cfg.P.d ∧
  (¬ (intRebuildThreshold cfg.P N0 idx < ch.updCount idx + curU.length) →
    idx < cfg.P.d → idx < i₀) ∧
  BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
    (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
    EWc ULc ch0 termTok i₀ chE curGE curUE curEditsE oldOrdE sE tokE bE bWE eE eWE levelUE
    levelUSE DE ∧
  UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen
    ℓ' g' (cfg.P.d - i₀) i₀ chE curGE curUE curEncE oldOrdE ∧
  (i₀ < cfg.P.d → intRebuildThreshold cfg.P N0 i₀ < chE.updCount i₀ + curUE.length) ∧
  (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P N0 ℓ' g' rem idx ch curG curU
      curEnc).1 =
    (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P N0 ℓ' g' (cfg.P.d - i₀) i₀ chE
      curGE curUE curEncE).1 ∧
  sF.mem = sE.mem ∧
  (∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 99 → sF.regs r = sE.regs r) ∧ sF.regs 99 = i₀ ∧
  st.regs 4 ≤ sE.regs 4 ∧ sE.regs 4 ≤ st.regs 4 + (Finset.Ico idx i₀).sum stepSpace ∧
  (∀ j < idx, chE.scState j = ch.scState j ∧ levelUSE j = levelUS j ∧ DE j = D j) ∧
  (∀ a < st.regs 4, (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) a) →
    (∀ j < cfg.P.d, (a < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ a) ∧
      (a < A.lPtr0 j ∨ A.lPtr0 j + eCap * L ≤ a)) →
    (∀ j < cfg.P.d, a ≠ A.ucBase + j) →
    (a < A.selBase ∨ A.selBase + 1 + 12 * cfg.P.d ≤ a) → sF.mem a = st.mem a) ∧
  (∀ j < cfg.P.d, ∀ a, Rcore.foot (A.coreH j) (tokE j) a →
    Rcore.foot (A.coreH j) (tok j) a ∨ (st.regs 4 ≤ a ∧ a < sE.regs 4)) ∧
  cost + branchBPhiSum Rcore A tokE sE.mem ≤
    (Finset.Ico idx i₀).sum (fun j =>
      branchBStepCostKFBL L capExp Psc cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀ (BWc j)
        (EWc j) (cfg.T.cost (chE.scState j) - cfg.T.cost (ch0.scState j))
        (levelUSE j).length (DE j).fDel.length (DE j).reemb.length + 4) + 32 +
    branchBPhiSum Rcore A tok st.mem ∧
  (∀ j, idx ≤ j → j < i₀ →
    cfg.T.cost (chE.scState j) - cfg.T.cost (ch.scState j) =
      (branchBStepData cfg ℓ' g' rem idx ch curG curU curEnc j).2.1 ∧
    (levelUSE j).length = (branchBStepData cfg ℓ' g' rem idx ch curG curU curEnc j).2.2) ∧
  (ToolCostMono cfg.T → ch.totalRuntime +
    (Finset.Ico idx i₀).sum (fun j => cfg.T.cost (chE.scState j) - cfg.T.cost (ch.scState j)) ≤
    chE.totalRuntime)

/-- `BranchBLoopExitKFBL` gives the facts `BranchBLoopExitAtKFBL` at some witnesses. -/
theorem BranchBLoopExitKFBL.exists_at {w L P depth vCap eCap capExp dgApply copyProc updLen
    slotProc wordExp stretchPrec N0 : ℕ} {fmt : Num.Format w} {cfg : Alg2Config}
    {Psc : SparseCoreOrdParams} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {opCore : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ} {ℓ' g' : ℕ → ℝ}
    {BWc EWc ULc stepSpace : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ}
    {rem idx : ℕ} {ch : ChainState cfg.T cfg.P} {curG : MGraph} {curU : List Update}
    {curEnc : ℕ} {st : State} {tok : ℕ → Rcore.τ} {levelUS : ℕ → List Update}
    {D : ℕ → LevelDiffLists}
    (h : BranchBLoopExitKFBL w L P depth vCap eCap capExp dgApply copyProc updLen slotProc wordExp
      stretchPrec N0 fmt cfg Psc reembFn Rcore RL p opCore ω A origLen ℓ' g' BWc EWc ULc
      stepSpace ch0 termTok rem idx ch curG curU curEnc st tok levelUS D) :
    ∃ (i₀ : ℕ) (sE sF : State) (cost : ℕ) (chE : ChainState cfg.T cfg.P) (curGE : MGraph)
      (curUE : List Update) (curEditsE : List OrdEdit) (curEncE : ℕ)
      (oldOrdE : ℕ → List End) (tokE : ℕ → Rcore.τ) (bE bWE eE eWE : ℕ)
      (levelUE levelUSE : ℕ → List Update) (DE : ℕ → LevelDiffLists),
      BranchBLoopExitAtKFBL w L P depth vCap eCap capExp dgApply copyProc updLen slotProc wordExp
        stretchPrec N0 fmt cfg Psc reembFn Rcore RL p opCore ω A origLen ℓ' g' BWc EWc ULc
        stepSpace ch0 termTok rem idx ch curG curU curEnc st tok levelUS D i₀ sE sF cost chE
        curGE curUE curEditsE curEncE oldOrdE tokE bE bWE eE eWE levelUE levelUSE DE :=
  h

/-- The facts after the suffix of Branch B, at the end state `out` of the run from `st`: the
conclusion of `wireBranchBSuffixKFBL_runs` without its first conjunct, with its witnesses as
parameters. -/
@[expose] def BranchBSuffixFactsKFBL (L drainUnit emitCuts packEdits filterEdits bind canonCopy
    isNeg pushInsProc root uIntBuf heapX rg offCnt n dd i₀ : ℕ) {w : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (p : Program) (opTree : ℕ → ℕ) (ω : ℕ → Bool)
    (st : State) (tok : SolverToken cfg L Rcore) (B R : ℤ) (G0 : MGraph) (F Fp N : Finset ℕ)
    (canonVal : ℕ → PathEdgeValue)
    (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ)
    (fDel : ℕ → List ℕ) (oldFs newFs : List MGraph) (Ub : List Update) (out : State)
    (cost nextHeap : ℕ) (curTree' : PathTreeState)
    (curTreeTok' : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (offCnt' : ℕ) :
    Prop :=
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  let T := ∑ j ∈ Finset.range n, (fDel j).length
  let oldE := graphListEdgeUnion oldFs
  let newE := graphListEdgeUnion newFs
  let S := graphListEdgeSum oldFs + graphListEdgeSum newFs
  Runs w p ω (wireBranchBSuffixKFBL emitCuts packEdits filterEdits (opTree 4) (opTree 1)
    (opTree 0) bind canonCopy isNeg pushInsProc) st (.returned nextHeap) out cost ∧
  heapX ≤ nextHeap ∧
  nextHeap ≤ heapX + (2 * T + T * wireTreeSyncEditSpace L) +
    (3 * tok.intCap + 4 * S + S * wireTreeSyncEditSpace L) ∧
  ZeroFrom out.mem nextHeap ∧
  TreeSyncPhaseAt L tok root uIntBuf nextHeap rg G0 (Fp ∪ newE) canonVal B R
    (N \ (batchInsertedEdges Ub).toFinset) curTree' curTreeTok' offCnt' out.mem ∧
  (∀ a, Rtree.foot tok.treeHeap curTreeTok' a →
    Rtree.foot tok.treeHeap curTreeTok a ∨ (heapX ≤ a ∧ a < nextHeap)) ∧
  (∀ ei ∈ G0.E, ei ∉ Fp ∪ newE →
    out.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei) ∨
    (heapX ≤ out.mem (tok.edgeRecords + ei) ∧
      out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ nextHeap)) ∧
  (∀ ei ∈ G0.E, ei ∉ F → ei ∉ Fp ∪ newE →
    out.mem (tok.edgeRecords + ei) = st.mem (tok.edgeRecords + ei)) ∧
  (∀ a, BranchBSuffixKeep L tok root uIntBuf heapX curTreeTok a → out.mem a = st.mem a) ∧
  (∀ a < heapX, a ≠ root + 11 →
    (a < uIntBuf → tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧
      tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) →
    (uIntBuf ≤ a → ¬ Rtree.foot tok.treeHeap curTreeTok a) → out.mem a = st.mem a) ∧
  cost + (Rtree.phi tok.treeHeap curTreeTok' out.mem + offCnt' * drainUnit) ≤
    T * (wireTreeSyncEditCost L drainUnit + 2) + 40 * T + 64 * n + 175 +
      ((oldE \ newE).card + (newE \ oldE).card) * (wireTreeSyncEditCost L drainUnit + 2) +
      155 * S + 210 * (dd + 1 - i₀) + 350 +
      (160 * Ub.length + 60 + Ub.length * drainUnit) + 20 +
      (Rtree.phi tok.treeHeap curTreeTok st.mem + offCnt * drainUnit)

/-- What the exit of the loop of Branch B gives besides `BranchBExitOutKFBL`, in each of its three
cases. The loop exits at level `i₀` with the state `sE` at the top of the last pass, the state `sL`
after the loop, the model `chE`, the batch `curUE` of level `i₀` (its graph `curGE`, its encoding
`curEncE`, `curBW` words) and the tokens `tokE`; the exit ends at `sX` at cost `cX`.
* The interior exit (`0 < i₀ < d`): the first rebuilt level is `fr = i₀`, the model `X` is the
  rebuild from `i₀`, and the facts are those of `BranchBIntExitLayGoalKFBL`, at the level space
  `levelSpace` and the level cost `levelCost X`.
* The terminal exit with a batch (`i₀ = d`, `curUE ≠ []`): `fr = d`, `X` is the update loop at
  level `d`, the token of level `d - 1` is new, and the facts are those of
  `BranchBTermExitLayGoalKFBL` at `nextM = levelM d`.
* The terminal exit with an empty batch (`i₀ = d`, `curUE = []`): `fr = d + 1`, the tokens and the
  last level stay, and the facts are those of `wireBranchBTermEmpty_exitOut`. -/
@[expose] def BranchBExitCaseKFBL (w L P vCap eCap capExp capLimit lastMul lastSpace dgApply
    initCore coreLenProc lastInit : ℕ) (cfg : Alg2Config) (Psc : SparseCoreOrdParams)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program) (opCore : ℕ → ℕ) (ω : ℕ → Bool)
    (levelSpace : ℕ → ℕ) (levelCost : ChainState cfg.T cfg.P → ℕ → ℕ)
    (tok : SolverToken cfg L Rcore) (A : BranchBAddrs) (ℓ' g' : ℕ → ℝ) (i₀ : ℕ)
    (sE sL : State) (chE : ChainState cfg.T cfg.P) (curGE : MGraph) (curUE : List Update)
    (curEncE curBW : ℕ) (tokE : ℕ → Rcore.τ) (sX : State) (cX fr vcL ecL termTokN hT : ℕ)
    (tokN : ℕ → Rcore.τ) (X : ChainState cfg.T cfg.P) : Prop :=
  (0 < i₀ ∧ i₀ < cfg.P.d ∧ fr = i₀ ∧ vcL = vCap ∧ ecL = eCap ∧
    X = (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P { chE with ℓ := ℓ', g := g' } i₀ curGE
      curEncE).1 ∧
    Runs w p ω (wireBranchBIntKFBL dgApply initCore (opCore 3) (opCore 2) coreLenProc
      (opCore 5) lastInit) sL .normal sX cX ∧
    sX.regs 4 ≤ sE.regs 4 + 10 * (cfg.P.d - i₀) +
      (1 + ordRotWords (chainLevelOrdAbs chE (i₀ - 1)) (chE.bran (i₀ - 1))) +
      (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace + 7 ∧
    cX + (Finset.range cfg.P.d).sum
        (fun j => Rcore.phi (sX.mem (A.handleBase + j)) (tokN j) sX.mem) ≤
      2 * ((cfg.P.d - i₀) * (Psc.readout + 48)) + 670 * curBW +
        Psc.mul * (ordRotWords (chainLevelOrdAbs chE (i₀ - 1)) (chE.bran (i₀ - 1)) + 1) *
          SparseCore.bundleLogFactor (levelM cfg.TP cfg.P (i₀ - 1)) cfg.N₀ +
        (Finset.Ico i₀ cfg.P.d).sum (fun j => levelCost X j + 9) +
        lastMul * (cfg.L.cost (X.G cfg.P.d) + 1) + Psc.readout + 15 * (cfg.P.d - i₀) +
        413 + branchBPhiSum Rcore A tokE sE.mem) ∨
  (i₀ = cfg.P.d ∧ curUE ≠ [] ∧ fr = cfg.P.d ∧ vcL = vCap ∧ ecL = eCap ∧
    X = (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' 0 cfg.P.d chE curGE
      curUE curEncE).1 ∧
    (∃ y : Rcore.τ, tokN = fun j => if j = cfg.P.d - 1 then y else tokE j) ∧
    Runs w p ω (wireBranchBTermKFBL (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
      collectTermForestStmt 81) sL .normal sX cX ∧
    (∃ h1, sE.regs 4 ≤ h1 ∧
      h1 ≤ sE.regs 4 + (1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
        levelM cfg.TP cfg.P cfg.P.d * wireCoreLenEdgeSpace
          (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) +
        (2 + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P cfg.P.d)) + lastSpace ∧
      sX.regs 4 = h1 + 7) ∧
    cX + branchBPhiSum Rcore A tokN sX.mem +
        (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P curGE.E).phi
          (sX.mem (A.handleBase + cfg.P.d)) termTokN sX.mem ≤
      3 * Psc.readout + copyGraphLiveCost curGE.n curGE.m +
        curGE.m * (wireCoreLenEdgeCost
          (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) + 30) +
        Psc.mul * (ordRotWords (chainLevelOrdAbs chE (cfg.P.d - 1)) (chE.bran (cfg.P.d - 1)) +
          1) * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀ +
        lastMul * (cfg.L.cost curGE + 1) + 360 + 36 + branchBPhiSum Rcore A tokE sE.mem) ∨
  (i₀ = cfg.P.d ∧ curUE = [] ∧ fr = cfg.P.d + 1 ∧ vcL = tok.vcLast ∧ ecL = tok.ecLast ∧
    X = (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' 0 cfg.P.d chE curGE
      curUE curEncE).1 ∧
    tokN = tokE ∧ termTokN = tok.termTok ∧ hT = sE.regs 4 ∧
    Runs w p ω (wireBranchBTermKFBL (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
      collectTermForestStmt 81) sL .normal sX cX ∧
    cX ≤ 44 ∧ sX.regs 4 = sE.regs 4 ∧
    branchBPhiSum Rcore A tokE sX.mem = branchBPhiSum Rcore A tokE sE.mem)

end MinCostFlow.MinRatio
