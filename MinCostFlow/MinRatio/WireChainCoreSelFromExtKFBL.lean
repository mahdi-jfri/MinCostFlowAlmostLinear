module

public import MinCostFlow.MinRatio.WireChainCoreSpecProofKFBL
public import MinCostFlow.MinRatio.OrdSelSpecs
import WordRAM.Tactic

/-!
# The select-aware core spec from the chain-core spec (`WireChainCoreSelFromExtKFBL`)

The solver takes the select-aware core spec `OrdChainUpdateCoreSpecWKFBLSel` (`hCoreSel`). This
file writes the path from `OrdChainUpdateCoreSpecWExtKFBL` to it, and states each piece of the
path as a proposition.

The path has two steps.
1. The Sel spec gives its premises as one list (`UpdateCoreSelPremAt`). Most premises of the Ext
   spec are in that list. Four are not: `model.extG.m = m` and the three model facts
   `UpdateCoreModelInv`, `UpdateCoreModelInvKFBL` and the bound on the forest edges. Each is an
   adapter here (`UpdateCoreSelAdaptExtM`, `UpdateCoreSelAdaptModelInv`,
   `UpdateCoreSelAdaptKFBLInv`, `UpdateCoreSelAdaptForest`). With them, the Ext spec at the budget
   `B_bound := B`, `R_bound := R` gives the post of the core under the Sel premises
   (`ordChainCoreSelPrem_of_ext`).
2. The select-aware procedure at `ordChainCoreProc` runs the core and then keeps the select
   region in step. That composition is the proposition `UpdateCoreSelWrapKFBL`. The core has
   its own sizes, and the procedure has the sizes of the Sel spec, which add the select update.

`ordChainUpdateCoreSpecWKFBLSel_of_parts` puts the two steps together with the proof of the Ext
spec of `WireChainCoreSpecProofKFBL.lean`. Its premises are the Branch B case
(`OrdChainCoreBranchBPostKFBL`, at every budget), the four adapters and the wrapper. The file
`Final/AssemblyDryRunSCCoreAdapters.lean` proves the adapters at the parameters of the final
solver.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program IPM.Machine

/-- The premises of `OrdChainUpdateCoreSpecWKFBLSel` at one start state, in the order of that
spec. -/
@[expose] def UpdateCoreSelPremAt
    (w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax forestEdgeCap
      vCap eCap dMul kOff pLast slot : ℕ)
    (cfg : Alg2Config) (G : MGraph) (pot : cfg.T.State → ℕ)
    (DeepInv : ChainState cfg.T cfg.P → Prop) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (coreSpace : ℕ → ℕ) (root uIntBuf editsPtr editWords g l heap : ℕ) (mem0 mem : ℕ → ℕ)
    (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (sg : SelectGhost)
    (U : List Update) (B R : ℤ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
  let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
  let modelPre := alg2PreResetState cfg model U gVec lVec
  Rrep.rep root model tok mem0 ∧
  SolverLevelMetaAt P V model tok mem0 ∧
  SolverLevelCapsAt vCap eCap model tok mem0 ∧
  SolverSelectInv G L P m dMul kOff tok.table model (Rrep.foot root tok)
    (LevelMetaFoot tok) sg mem0 ∧
  sg.reembPot = chainReembPot pot model.chain ∧
  SolverSelectRegionInv G L P m E pLast slot vCap eCap model (Rrep.foot root tok) tok sg mem0 ∧
  OrdSolverReached cfg (1 / (2 : ℝ) ^ k) G model ∧
  DeepInv model.chain ∧
  MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
    G 4 L P model ∧
  SolverTreeNumericInv P model tok ∧
  PathTreeNumericInv tok.tree tok.trees B R ∧
  OffTreeRecInv model L mem0 tok.edgeRecords B ∧
  OffTreeRecBound model L mem0 tok.edgeRecords B ∧
  treeBudgetBase P E ≤ B ∧
  2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) ∧
  (∀ e ∈ model.extG.E, |model.extg e| ≤ (2 : ℝ) ^ E ∧
    (2 : ℝ) ^ (-(E : ℤ)) ≤ model.extℓ e ∧ model.extℓ e ≤ (2 : ℝ) ^ E) ∧
  (∀ e ∈ model.extG.E, |model.flow e| ≤ (2 : ℝ) ^ E) ∧
  (∀ e ∈ model.extG.E, 0 ≤ model.detectAccum e ∧
    model.extℓ e * model.detectAccum e < cfg.ε) ∧
  tok.intCap = initTargetCap cfg G ∧
  tok.intCap ≤ intCapMax ∧
  2 * (model.chain.G 0).n ≤ forestEdgeCap ∧
  Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L ∧
  Chain.Ordered.ShiftLoopChainInv cfg model.chain ∧
  Chain.Ordered.ShiftLoopChainInv cfg modelPre.chain ∧
  WireCapFacts capExp limbMul L capLimit model ∧
  (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) ∧
  (∀ e ∈ model.extG.E, |gVec e| ≤ (2 : ℝ) ^ E ∧
    (2 : ℝ) ^ (-(E : ℤ)) ≤ lVec e ∧ lVec e ≤ (2 : ℝ) ^ E) ∧
  (∀ e ∈ model.extG.E, (∀ u ∈ U, ¬ u.Inserts e) →
    gVec e = model.extg e ∧ lVec e = model.extℓ e) ∧
  (∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a) ∧
  FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
    tr.2.1 tr.2.2.1 tr.2.2.2.1 ∧
  tr.2.2.2.1 ≤ tok.intCap ∧
  BatchAt mem uIntBuf tr.2.2.2.2 ∧
  DynSpanner.Program.SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2
    (editsPtr - cfg.P.d - uIntBuf) ∧
  OrdEditsAt mem editsPtr (batchToOrdEdits tr.2.2.2.2) editWords ∧
  (∀ j < editWords, mem (editsPtr + j) < 2 ^ w) ∧
  editsPtr + editWords = heap ∧
  RefreshBatch model.extG U ∧
  (∀ a, Rrep.foot root tok a ∨ sg.owned a → a < uIntBuf) ∧
  g + m * L ≤ uIntBuf ∧ l + m * L ≤ uIntBuf ∧
  (∀ j < m * L, ¬ (Rrep.foot root tok (g + j) ∨ sg.owned (g + j)) ∧
    ¬ (Rrep.foot root tok (l + j) ∨ sg.owned (l + j))) ∧
  uIntBuf + cfg.P.d ≤ editsPtr ∧
  ZeroFrom mem heap ∧
  heap + coreSpace U.length < 2 ^ w

/-- Adapter 1: the Sel premises give `model.extG.m = m` (a premise of the Ext spec). The
reached state has `model.extG = G`, and `G.m = m` at the dry values. -/
@[expose] def UpdateCoreSelAdaptExtM
    (w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax forestEdgeCap
      vCap eCap dMul kOff pLast slot : ℕ)
    (cfg : Alg2Config) (G : MGraph) (pot : cfg.T.State → ℕ)
    (DeepInv : ChainState cfg.T cfg.P → Prop) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (coreSpace : ℕ → ℕ) : Prop :=
  ∀ (root uIntBuf editsPtr editWords g l heap : ℕ) (mem0 mem : ℕ → ℕ) (model : Alg2State cfg)
    (tok : SolverToken cfg L Rcore) (sg : SelectGhost) (U : List Update) (B R : ℤ),
    UpdateCoreSelPremAt w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax
      forestEdgeCap vCap eCap dMul kOff pLast slot cfg G pot DeepInv Rcore coreSpace root uIntBuf
      editsPtr editWords g l heap mem0 mem model tok sg U B R →
    model.extG.m = m

/-- Adapter 2: the Sel premises give `UpdateCoreModelInv` (the level-meta layout, the caps and
name bounds of the batch, the footprint part, the refreshed-edge numbers and the model facts on
`modelPre`). -/
@[expose] def UpdateCoreSelAdaptModelInv
    (w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax forestEdgeCap
      vCap eCap dMul kOff pLast slot wordExp stretchPrec : ℕ)
    (cfg : Alg2Config) (G : MGraph) (pot : cfg.T.State → ℕ)
    (DeepInv : ChainState cfg.T cfg.P → Prop) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (coreSpace : ℕ → ℕ) : Prop :=
  ∀ (root uIntBuf editsPtr editWords g l heap : ℕ) (mem0 mem : ℕ → ℕ) (model : Alg2State cfg)
    (tok : SolverToken cfg L Rcore) (sg : SelectGhost) (U : List Update) (B R : ℤ),
    UpdateCoreSelPremAt w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax
      forestEdgeCap vCap eCap dMul kOff pLast slot cfg G pot DeepInv Rcore coreSpace root uIntBuf
      editsPtr editWords g l heap mem0 mem model tok sg U B R →
    UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B

/-- Adapter 3: the Sel premises give `UpdateCoreModelInvKFBL` (the `ChainInv` facts of the model
before and after the update, from the two `ShiftLoopChainInv` premises). -/
@[expose] def UpdateCoreSelAdaptKFBLInv
    (w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax forestEdgeCap
      vCap eCap dMul kOff pLast slot : ℕ)
    (cfg : Alg2Config) (G : MGraph) (pot : cfg.T.State → ℕ)
    (DeepInv : ChainState cfg.T cfg.P → Prop) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (coreSpace : ℕ → ℕ) : Prop :=
  ∀ (root uIntBuf editsPtr editWords g l heap : ℕ) (mem0 mem : ℕ → ℕ) (model : Alg2State cfg)
    (tok : SolverToken cfg L Rcore) (sg : SelectGhost) (U : List Update) (B R : ℤ),
    UpdateCoreSelPremAt w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax
      forestEdgeCap vCap eCap dMul kOff pLast slot cfg G pot DeepInv Rcore coreSpace root uIntBuf
      editsPtr editWords g l heap mem0 mem model tok sg U B R →
    UpdateCoreModelInvKFBL model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)

/-- Adapter 4: the Sel premises bound the edges of the suffix forests before and after the update
by `forestEdgeCap` (each sum is below the vertex count of the root graph). -/
@[expose] def UpdateCoreSelAdaptForest
    (w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax forestEdgeCap
      vCap eCap dMul kOff pLast slot : ℕ)
    (cfg : Alg2Config) (G : MGraph) (pot : cfg.T.State → ℕ)
    (DeepInv : ChainState cfg.T cfg.P → Prop) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (coreSpace : ℕ → ℕ) : Prop :=
  ∀ (root uIntBuf editsPtr editWords g l heap : ℕ) (mem0 mem : ℕ → ℕ) (model : Alg2State cfg)
    (tok : SolverToken cfg L Rcore) (sg : SelectGhost) (U : List Update) (B R : ℤ),
    UpdateCoreSelPremAt w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax
      forestEdgeCap vCap eCap dMul kOff pLast slot cfg G pot DeepInv Rcore coreSpace root uIntBuf
      editsPtr editWords g l heap mem0 mem model tok sg U B R →
    graphListEdgeSum (chainSuffixForests model.chain 0) +
      graphListEdgeSum (chainSuffixForests (alg2PreResetState cfg model U
        (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
        (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain 0) ≤
      forestEdgeCap

/-- The chain core `body` under the Sel premises: from every start state that meets them, the
post of the Ext spec holds at the budget `B, R` of that state. The premises use the space
`coreSpace` of the select-aware procedure, and the post uses the sizes `innerSpace`,
`innerFixed`, `innerToolMul`, `innerTreeMul` of the core alone. -/
@[expose] def OrdChainCoreSelPremPost
    (w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax forestEdgeCap
      vCap eCap dMul kOff pLast slot : ℕ)
    (cfg : Alg2Config) (G : MGraph) (pot : cfg.T.State → ℕ)
    (DeepInv : ChainState cfg.T cfg.P → Prop) (reembFn : ToolReembFn cfg.T)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program) (coreSpace : ℕ → ℕ)
    (innerSpace innerFixed : ℕ → ℕ) (innerToolMul innerTreeMul : ℕ) (body : Stmt) : Prop :=
  ∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
    (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (sg : SelectGhost)
    (U : List Update) (B R : ℤ),
    UpdateCoreSelPremAt w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax
      forestEdgeCap vCap eCap dMul kOff pLast slot cfg G pot DeepInv Rcore coreSpace root uIntBuf
      editsPtr editWords g l heap mem0 mem model tok sg U B R →
    OrdChainCoreExtPost w L P m V psi k epsExp drainUnit capExp vCap eCap cfg reembFn Rcore p
      innerSpace innerFixed innerToolMul innerTreeMul B R body root uIntBuf editsPtr editWords g l
      heap pos ω mem0 mem model tok U

/-- The select-aware wrapper: the procedure at `ordChainCoreProc` meets the Sel spec when the
chain core `body` meets `OrdChainCoreSelPremPost`. The wrapper runs the core and then keeps the
select region in step with the new chain, from the select output of the core. The core has its
own sizes (`innerSpace`, `innerFixed`, `innerToolMul`, `innerTreeMul`), and the wrapper has the
sizes of the Sel spec (`coreSpace`, `coreFixed`, `toolMul`, `treeMul`), which add the cost and
space of the select update. -/
@[expose] def UpdateCoreSelWrapKFBL
    (w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax forestEdgeCap
      vCap eCap dMul kOff K pLast slot : ℕ)
    (cfg : Alg2Config) (G : MGraph) (pot : cfg.T.State → ℕ)
    (DeepInv : ChainState cfg.T cfg.P → Prop) (reembFn : ToolReembFn cfg.T)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program) (ordChainCoreProc : ℕ)
    (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ)
    (innerSpace innerFixed : ℕ → ℕ) (innerToolMul innerTreeMul : ℕ) (body : Stmt) : Prop :=
  OrdChainCoreSelPremPost w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax
      forestEdgeCap vCap eCap dMul kOff pLast slot cfg G pot DeepInv reembFn Rcore p coreSpace
      innerSpace innerFixed innerToolMul innerTreeMul body →
    OrdChainUpdateCoreSpecWKFBLSel w L P E m V psi k epsExp drainUnit capExp limbMul capLimit
      intCapMax forestEdgeCap vCap eCap dMul kOff K pLast slot cfg G pot DeepInv Rcore p
      ordChainCoreProc coreSpace coreFixed toolMul treeMul

/-- Step 1: the Ext spec of the core at every budget, with the four adapters, gives the post of
the core under the Sel premises. The Ext spec runs at `B_bound := B`, `R_bound := R`, at the
sizes of the core. Its room premise follows from the room of the Sel premises, since the space
of the core is at most `coreSpace` (`hInnerLe`). -/
theorem ordChainCoreSelPrem_of_ext
    {w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax forestEdgeCap
      vCap eCap dMul kOff pLast slot wordExp stretchPrec coreProc : ℕ}
    {cfg : Alg2Config} {G : MGraph} {pot : cfg.T.State → ℕ}
    {DeepInv : ChainState cfg.T cfg.P → Prop} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {coreSpace : ℕ → ℕ}
    {innerSpace innerFixed : ℕ → ℕ} {innerToolMul innerTreeMul : ℕ} {body : Stmt}
    (hBody : p.procs[coreProc]? = some body)
    (hInnerLe : ∀ u, innerSpace u ≤ coreSpace u)
    (hExt : ∀ Bb Rb : ℤ, OrdChainUpdateCoreSpecWExtKFBL w L P m V psi k epsExp drainUnit capExp
      limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg G reembFn Rcore
      p coreProc innerSpace innerFixed innerToolMul innerTreeMul Bb Rb)
    (hA1 : UpdateCoreSelAdaptExtM w L P E m V psi k epsExp drainUnit capExp limbMul capLimit
      intCapMax forestEdgeCap vCap eCap dMul kOff pLast slot cfg G pot DeepInv Rcore coreSpace)
    (hA2 : UpdateCoreSelAdaptModelInv w L P E m V psi k epsExp drainUnit capExp limbMul capLimit
      intCapMax forestEdgeCap vCap eCap dMul kOff pLast slot wordExp stretchPrec cfg G pot DeepInv
      Rcore coreSpace)
    (hA3 : UpdateCoreSelAdaptKFBLInv w L P E m V psi k epsExp drainUnit capExp limbMul capLimit
      intCapMax forestEdgeCap vCap eCap dMul kOff pLast slot cfg G pot DeepInv Rcore coreSpace)
    (hA4 : UpdateCoreSelAdaptForest w L P E m V psi k epsExp drainUnit capExp limbMul capLimit
      intCapMax forestEdgeCap vCap eCap dMul kOff pLast slot cfg G pot DeepInv Rcore coreSpace) :
    OrdChainCoreSelPremPost w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax
      forestEdgeCap vCap eCap dMul kOff pLast slot cfg G pot DeepInv reembFn Rcore p coreSpace
      innerSpace innerFixed innerToolMul innerTreeMul body := by
  intro root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok sg U B R hPrem
  have hExtM := hA1 root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R hPrem
  have hMI := hA2 root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R hPrem
  have hMK := hA3 root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R hPrem
  have hFC := hA4 root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R hPrem
  obtain ⟨body', hP', hRun⟩ := hExt B R
  have hbb : body' = body := Option.some.inj (hP'.symm.trans hBody)
  subst hbb
  obtain ⟨hRep0, hMeta0, hCaps0, _, _, _, _, _, _, _, hNum0, hOffInv0, hOffBd0, _, hCapT, _, _,
    _, hIntCapEq, hIntCapMax, _, hLogW, hShift, _, hWire, hBran, _, _, hMemEq, hFresh, hTrNf,
    hBatch, hSmall, hEdits, hEditsW, hEdHeap, hRef, hFootLt, hGLt, hLLt, _, hULe, hz0,
    hRoom⟩ := hPrem
  exact hRun root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok U B R hRep0 hMeta0
    hCaps0 hIntCapEq hExtM hNum0 hOffInv0 hOffBd0 le_rfl le_rfl hShift hWire hBran hMI hMK
    hIntCapMax hFC hLogW hCapT hMemEq hFresh hTrNf hBatch hSmall hEdits hEditsW hEdHeap hRef
    (fun a ha => hFootLt a (Or.inl ha)) hGLt hLLt hULe hz0
    (lt_of_le_of_lt (Nat.add_le_add_left (hInnerLe U.length) heap) hRoom)

/-- **The Sel spec of the chain core from its pieces.** The core at `coreProc` is
`ordChainUpdateCoreBodyKFBL` with Branch A the code of `wireBranchAKFBL` and any `branchB`. The
premises are the Branch B case at every budget (`hB`), the four adapters (`hA1`–`hA4`) and
the select-aware wrapper (`hWrap`). The facts `hGSup`, `hGM`, `hM0Le` are about the parameters
only, and `E` holds the contracts of the procedures that Branch A calls. The core runs at its own
sizes (`innerSpace`, `innerFixed`, `innerToolMul`, `innerTreeMul`), with `innerSpace` at most
`coreSpace`, and the Sel spec holds at the sizes of the wrapper. -/
theorem ordChainUpdateCoreSpecWKFBLSel_of_parts
    {w L P Ex m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap dMul kOff K pLast slot
      packEditsProc initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc
      divide add sub copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc
      dgInit coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc coreProc
      ordChainCoreProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul : ℕ}
    {innerSpace innerFixed : ℕ → ℕ} {innerToolMul innerTreeMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {reembFn : ToolReembFn cfg.T}
    {pot : cfg.T.State → ℕ} {DeepInv : ChainState cfg.T cfg.P → Prop}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {branchB : Stmt}
    {stepCap : ℕ → ℕ → ℕ}
    (E : BranchAEnvKFBL w L P m capExp capLimit fcap lastMul intCapMax forestEdgeCap drainUnit
      edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply updateLen0Proc
      initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc signExt mul
      intDiv lastInit rebuildOffReadyProc innerSpace innerFixed innerToolMul fmt cfg G Psc
      levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Rcore p opTree
      opCore opLast stepCap)
    (hInnerLe : ∀ u, innerSpace u ≤ coreSpace u)
    (hProc : p.procs[coreProc]? = some (ordChainUpdateCoreBodyKFBL
      (wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg
        refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
        sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
      branchB))
    (hGSup : G.E.sup id ≤ G.m) (hGM : G.m = m) (hM0Le : cfg.P.M₀ ≤ m + mThresh)
    (hB : ∀ Bb Rb : ℤ, OrdChainCoreBranchBPostKFBL w L P m V psi k epsExp drainUnit capExp
      limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg G reembFn Rcore
      p innerSpace innerFixed innerToolMul innerTreeMul Bb Rb (ordChainUpdateCoreBodyKFBL
        (wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg
          refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
          sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
        branchB))
    (hA1 : UpdateCoreSelAdaptExtM w L P Ex m V psi k epsExp drainUnit capExp limbMul capLimit
      intCapMax forestEdgeCap vCap eCap dMul kOff pLast slot cfg G pot DeepInv Rcore coreSpace)
    (hA2 : UpdateCoreSelAdaptModelInv w L P Ex m V psi k epsExp drainUnit capExp limbMul
      capLimit intCapMax forestEdgeCap vCap eCap dMul kOff pLast slot wordExp stretchPrec cfg G
      pot DeepInv Rcore coreSpace)
    (hA3 : UpdateCoreSelAdaptKFBLInv w L P Ex m V psi k epsExp drainUnit capExp limbMul capLimit
      intCapMax forestEdgeCap vCap eCap dMul kOff pLast slot cfg G pot DeepInv Rcore coreSpace)
    (hA4 : UpdateCoreSelAdaptForest w L P Ex m V psi k epsExp drainUnit capExp limbMul capLimit
      intCapMax forestEdgeCap vCap eCap dMul kOff pLast slot cfg G pot DeepInv Rcore coreSpace)
    (hWrap : UpdateCoreSelWrapKFBL w L P Ex m V psi k epsExp drainUnit capExp limbMul capLimit
      intCapMax forestEdgeCap vCap eCap dMul kOff K pLast slot cfg G pot DeepInv reembFn Rcore p
      ordChainCoreProc coreSpace coreFixed toolMul treeMul innerSpace innerFixed innerToolMul
      innerTreeMul (ordChainUpdateCoreBodyKFBL
        (wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg
          refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
          sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
        branchB)) :
    OrdChainUpdateCoreSpecWKFBLSel w L P Ex m V psi k epsExp drainUnit capExp limbMul capLimit
      intCapMax forestEdgeCap vCap eCap dMul kOff K pLast slot cfg G pot DeepInv Rcore p
      ordChainCoreProc coreSpace coreFixed toolMul treeMul :=
  hWrap (ordChainCoreSelPrem_of_ext hProc hInnerLe
    (fun Bb Rb => ordChainUpdateCoreSpecWExtKFBL_of_branchB (B_bound := Bb) (R_bound := Rb)
      (treeMul := innerTreeMul) (V := V) (psi := psi) (k := k) (epsExp := epsExp) (limbMul := limbMul)
      (reembFn := reembFn) E hProc hGSup hGM hM0Le (hB Bb Rb))
    hA1 hA2 hA3 hA4)

end MinCostFlow.MinRatio
