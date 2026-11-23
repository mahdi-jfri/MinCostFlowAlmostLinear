module

public import MinCostFlow.MinRatio.WireChainCoreBranchBHeadPrefixKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBFrontLoopU0KFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBFrontRepKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBPrefixAuxKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBBatchOK
import MinCostFlow.MinRatio.WireChainCoreBranchBCostProofModel
import MinCostFlow.SparseCore.Program.AssemblyReemb
import WordRAM.Tactic

/-!
# The front and the loop of the head of Branch B (`WireChainCoreBranchBHeadLoopKFBL`)

The second part of a head of a run of Branch B: the front and the loop of plain steps, run from
the state `sP` after the prefix (`wireBranchBFrontLoopKFBL_runs_levelU0`).
`branchBHead_frontLoop` gives the run of the front, the facts at the exit of the loop at named
witnesses (`BranchBLoopExitAtKFBL`), and the fact that the loop keeps the batch of level `0`.

The premises of the front and the loop come from the start and from the prefix facts:
* the words that the front reads agree with `mem0` (`branchBPrefix_frontAgree`, from the two frames
  of the prefix);
* the batch of level `0` at `uIntBuf` and its edits at `editsPtr` lie between `uIntBuf` and
  `heap`, where the prefix writes nothing but the pointer to the old last forest, so they are
  unchanged; their words fit in a machine word (`branchB_batchWords_lt`, the edits from the
  start);
* the lengths of level `0` after the refresh are the conjunct of the prefix facts;
* the sizes of the batch and of the edits (`smallBatchAt_words_le_edgeOnly`,
  `ordEditsEnc_batchToOrdEdits_le`), the room (`spaceTotalBranchB`) and the step space
  (`updStepSpaceDom`) come from the totals of the core;
* every batch of the loop is valid at its level (`branchBStepBatch_ok`, from `cfg.TP.Valid`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

section Start

variable {w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
  forestEdgeCap vCap eCap : ℕ} {cfg : Alg2Config} {G : MGraph}
  {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {coreSpace : ℕ → ℕ}
  {root uIntBuf editsPtr editWords g l heap : ℕ} {mem0 mem : ℕ → ℕ} {model : Alg2State cfg}
  {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}

/-- The length block of level `0` has the tag `23 + d`, and the edges of the new root graph are
below `eCap`. -/
private theorem start_len0 (S : BranchBStartKFBL w L P m V psi k epsExp drainUnit capExp limbMul
      capLimit wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg G Rcore coreSpace root
      uIntBuf editsPtr editWords g l heap mem0 mem model tok U B R) :
    (∀ x, mem0 (solverLevelMetaAddr tok.table cfg.P.d) ≤ x →
      x < mem0 (solverLevelMetaAddr tok.table cfg.P.d) + eCap * L →
      tok.tag x = 23 + cfg.P.d) ∧
    ∀ e ∈ ((model.chain.G 0).applyBatch
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2).E,
      e < eCap := by
  have hdPos : 0 < cfg.P.d := S.modelInv.1.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hWire0, _⟩ := S.rep0
  obtain ⟨_, _, _, _, _, _, _, _, ⟨hRootEq, vcOf, ecOf, hLev, _, _⟩, _, hG0'Cap, _⟩ :=
    S.modelInv
  have hCap0 : vcOf 0 = vCap ∧ ecOf 0 = eCap :=
    dynGraphAt_caps_eq (hLev 0 hdPos).1 (S.caps0 0 hdPos)
  have hRootCap : model.extG.n = vCap ∧ tok.rootECap = eCap := by
    have hDG0 := S.caps0 0 hdPos
    rw [hRootEq] at hDG0
    exact dynGraphAt_caps_eq hWire0.2.1 hDG0
  refine ⟨fun x h1 h2 => ?_, fun e he => by rw [← hRootCap.2]; exact (hG0'Cap e he).1⟩
  have hL := (hLev 0 hdPos).2.2.2.1
  rw [add_zero, hCap0.2] at hL
  exact hL x h1 h2

/-- Across the prefix, the words in `[uIntBuf, heap)` keep their values: the prefix writes there
only the pointer to the old last forest, above the select slots. -/
private theorem start_keepLow (S : BranchBStartKFBL w L P m V psi k epsExp drainUnit capExp
      limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg G Rcore
      coreSpace root uIntBuf editsPtr editWords g l heap mem0 mem model tok U B R)
    {hS1 forestPtr : ℕ} {memS1 memOut : ℕ → ℕ}
    (hh0 : heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ hS1)
    (hFr1 : ∀ a < heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4, a ≠ root + 11 →
      (a < uIntBuf → tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧
        tok.tag a ≠ 14 ∧ tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) →
      memS1 a = Function.update mem (heap + 1 + 12 * cfg.P.d + cfg.P.d) forestPtr a)
    (hFr2 : ∀ a < hS1, (∀ ei < tok.intCap, ei ∉ (model.chain.G 0).E → a ≠ tok.slots + ei ∧
        a ≠ tok.edgeThresholds + ei ∧ a ≠ tok.edgeRecords + ei) →
      (a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) ∨
        mem0 (solverLevelMetaAddr tok.table cfg.P.d) + eCap * L ≤ a) →
      memOut a = memS1 a) :
    ∀ x, uIntBuf ≤ x → x < heap → memOut x = mem x := by
  have hTagL0 := (start_len0 S).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := S.rep0
  obtain ⟨hOwn, hT1, _, _, _, _, _, _, _, hT9, _, _, hT12, hT13, _, _, _, _, _, _, _⟩ := hTags0
  have hLt {x : ℕ} (ht : tok.tag x ≠ 0) : x < uIntBuf := S.footLt x (Or.inl (hOwn x ht))
  have hR11 : root + 11 < uIntBuf := hLt (by rw [hT1 11 (by omega)]; decide)
  intro x h1 h2
  have hOff : x < mem0 (solverLevelMetaAddr tok.table cfg.P.d) ∨
      mem0 (solverLevelMetaAddr tok.table cfg.P.d) + eCap * L ≤ x := by
    by_contra hc
    have := hLt (x := x) (by rw [hTagL0 x (by omega) (by omega)]; omega)
    omega
  rw [hFr2 x (by omega) (fun ei hei _ => ⟨fun h => by
      have := hLt (x := tok.slots + ei) (by rw [hT9 ei hei]; decide); omega, fun h => by
      have := hLt (x := tok.edgeThresholds + ei) (by rw [hT12 ei hei]; decide); omega,
      fun h => by
      have := hLt (x := tok.edgeRecords + ei) (by rw [hT13 ei hei]; decide); omega⟩) hOff,
    hFr1 x (by omega) (by omega) (fun h => absurd h (by omega)),
    Function.update_of_ne (by omega)]

/-- The batch of level `0` and its edits at a memory that agrees with `mem` on `[uIntBuf, heap)`,
with their sizes. -/
private theorem start_batchEdits (S : BranchBStartKFBL w L P m V psi k epsExp drainUnit capExp
      limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg G Rcore
      coreSpace root uIntBuf editsPtr editWords g l heap mem0 mem model tok U B R)
    {memOut : ℕ → ℕ} {heap2 : ℕ} (hKeep : ∀ x, uIntBuf ≤ x → x < heap → memOut x = mem x)
    (hH2 : heap ≤ heap2) (hLenW : U.length < 2 ^ w) (hUW : uIntBuf < 2 ^ w) :
    let U_int := (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2
    (SmallBatchAt memOut uIntBuf (model.chain.G 0) U_int (editsPtr - cfg.P.d - uIntBuf) ∧
      (∀ t < editsPtr - cfg.P.d - uIntBuf, memOut (uIntBuf + t) < 2 ^ w) ∧
      uIntBuf + cfg.P.d ≤ editsPtr ∧ editsPtr + editWords ≤ heap2) ∧
    (OrdEditsAt memOut editsPtr (batchToOrdEdits U_int) editWords ∧
      (∀ t < editWords, memOut (editsPtr + t) < 2 ^ w)) ∧
    editsPtr - cfg.P.d - uIntBuf ≤ 4 * U.length + 1 ∧ editWords ≤ 10 * U.length + 1 ∧
    U_int.length = U.length := by
  intro U_int
  have hUle := S.uLe
  have hEd := S.edHeap
  have hEdgeU : ∀ u ∈ U, IsEdgeUpdate u := fun u hu => by
    cases u with
    | insert _ _ _ | delete _ => trivial
    | split _ _ _ _ => exact S.refresh.2.2 _ hu
  have hULenEq : U_int.length = U.length :=
    translateBatch_length_eq U model.extG model.extToInt model.intToExt model.nextFresh hEdgeU
  have hEdgeInt : ∀ u ∈ U_int, IsEdgeUpdate u :=
    (refreshBatch_edge_dichotomy S.rep0.2.2.2.2.1 S.refresh).2.2.1
  have hb0 : editsPtr - cfg.P.d - uIntBuf ≤ 4 * U.length + 1 := by
    rw [← hULenEq]; exact smallBatchAt_words_le_edgeOnly S.small hEdgeInt
  have he0 : editWords ≤ 10 * U.length + 1 := by
    have h1 : editWords ≤ 5 * ordEditsEnc (batchToOrdEdits U_int) + 1 := S.edits.2.2
    have h2 := ordEditsEnc_batchToOrdEdits_le U_int hEdgeInt
    omega
  have hBW := branchB_batchWords_lt S.rep0 S.modelInv S.refresh S.trNf S.batch S.small S.footLt
    hUW hLenW
  refine ⟨⟨smallBatchAt_of_agree S.small (fun x h1 h2 => hKeep x h1 (by omega)),
      fun t ht => by rw [hKeep _ (by omega) (by omega)]; exact hBW t ht, hUle, by omega⟩,
    ⟨ordEditsAt_of_agree S.edits (fun x h1 h2 => hKeep x (by omega) (by omega)),
      fun t ht => by rw [hKeep _ (by omega) (by omega)]; exact S.editsW t ht⟩,
    hb0, he0, hULenEq⟩

end Start

/-- The room of the front and the loop from the space total of Branch B. -/
private theorem room_arith {heap h0 hS1 heap2 bW u L ts rs d S B C D E F Y W : ℕ}
    (h0eq : h0 = heap + 1 + 12 * d + 3 * (d + 1) + 4) (h1 : hS1 ≤ h0 + 3 * u + u * ts)
    (h2 : heap2 ≤ hS1 + 3 * L + u * rs) (h3 : bW ≤ 4 * u + 1)
    (h4 : (1 + 12 * d) + 3 * (d + 1) + 4 + (3 * u + u * ts) + (3 * L + u * rs) + (4 * u + 1) +
      S + B + C + D + E + F ≤ Y)
    (h5 : heap + Y < W) : heap2 + bW + S < W := by
  omega

set_option maxHeartbeats 1600000 in
/-- **The front and the loop of Branch B.** After the prefix of Branch B at `ec0 := eCap`, from a
state `st` with the registers of the dispatch, the front runs to a state at heap
`heap2 + bW`, and the loop from there exits with the facts `BranchBLoopExitAtKFBL`, at the trace
caps and the step space `updStepSpace j U.length`, from the start values `levelUS` and `D`. The
loop keeps the batch `U_int` of level `0`. -/
theorem branchBHead_frontLoop
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
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
    (EA : BranchAEnvKFBL w L P m capExp capLimit fcap lastMul intCapMax forestEdgeCap drainUnit
      edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply updateLen0Proc
      initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc signExt mul
      intDiv lastInit rebuildOffReadyProc coreSpace coreFixed toolMul fmt cfg G Psc levelSpace
      levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Rcore p opTree opCore
      opLast stepCap)
    (EB : BranchBEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy collectDel emitCuts zeroIns
      filterEdits pushInsProc pushProc isNeg fmt cfg Psc allocation Ginit reembFn Rcore p opCore)
    (S : BranchBStartKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp
      stretchPrec intCapMax forestEdgeCap vCap eCap cfg G Rcore coreSpace root uIntBuf editsPtr
      editWords g l heap mem0 mem model tok U B R)
    (hTS : ∀ ch, ShiftLoopChainInv cfg ch → BranchBToolStepKFBL cfg stepCap ch)
    (hTP : cfg.TP.Valid)
    {st : State} (hStMem : st.mem = mem)
    (hRegs : st.regs 4 = heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ∧ st.regs 70 = root ∧
          st.regs 71 = 0 ∧ st.regs 72 = heap ∧ st.regs 73 = tok.handle ∧ st.regs 75 = cfg.P.d ∧
          st.regs 76 = cfg.P.k ∧ st.regs 77 = tok.handle + 18 ∧
          st.regs 78 = tok.handle + 18 + (cfg.P.d + 1) ∧ st.regs 79 = cfg.P.d + 1 ∧
          st.regs 80 = heap + 1 + 12 * cfg.P.d ∧
          st.regs 81 = heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) ∧
          st.regs 82 = solverLvlMAddr tok.table cfg.P.d ∧
          st.regs 83 = solverLevelMetaAddr tok.table cfg.P.d ∧
          st.regs 85 = tok.levelsEnd + 3 * (cfg.P.d + 1) ∧
          st.regs 86 = tok.levelsEnd + 2 * (cfg.P.d + 1) ∧ st.regs 87 = uIntBuf ∧
          st.regs 90 = g ∧ st.regs 91 = l ∧
          st.regs 92 = heap + 1 + 12 * cfg.P.d + 2 * (cfg.P.d + 1) ∧
          st.regs 93 = heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) ∧ st.regs 94 = L ∧
          st.regs 95 = P ∧ st.regs 98 = Expander.chosenL (cfg.P.M₀ ^ 2))
    (hRegs2 : st.regs 74 = tok.table ∧ st.regs 84 = tok.levelsEnd ∧ st.regs 88 = editsPtr ∧
          st.regs 89 = editWords)
    {forestPtr : ℕ} {sP : State} {cP hS1 heap2 : ℕ} {memS1 : ℕ → ℕ} {curTree1 : PathTreeState}
    {curTreeTok1 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ} {offCnt1 : ℕ}
    {canonVal0 canonVal : ℕ → PathEdgeValue}
    (hPre : BranchBPrefixFactsKFBL w L P m drainUnit collectDel emitCuts bind canonCopy isNeg
      zeroIns refreshAccountsProc updateLen0Proc root uIntBuf g l heap eCap forestPtr p opTree ω
      mem0 mem st model tok U B R sP cP hS1 heap2 memS1 curTree1 curTreeTok1 offCnt1 canonVal0
      canonVal)
    (levelUS : ℕ → List Update) (D : ℕ → LevelDiffLists) :
    let d := cfg.P.d
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let U_int := tr.2.2.2.2
    let G0 := model.chain.G 0
    let bW := editsPtr - d - uIntBuf
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
    let ℓ' := fun e' => lVec (tr.2.2.1 e')
    let g' := fun e' => gVec (tr.2.2.1 e')
    let st0 : ChainState cfg.T cfg.P :=
      { model.chain with
        recUpdates := fun j =>
          if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
    let A := branchBAddrsOf tok mem0 heap heap2
    let RL := LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
      (model.chain.G d).E
    let C := branchBTraceCaps edMul
      (fun j => SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) bW editWords
      U_int.length (branchBStepData cfg ℓ' g' d 0 st0 (G0.applyBatch U_int) U_int
        (G0.batchEnc U_int))
    ∃ (s : State) (cF : ℕ),
      Runs w p ω (wireBranchBFrontKFBL copyProc) sP .normal s cF ∧
      cF ≤ 20 * bW + 60 ∧ s.regs 4 = heap2 + bW ∧ (∀ a < heap2, s.mem a = sP.mem a) ∧
      (∀ r, r ≠ 4 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 30 → r ≠ 96 → r ≠ 97 → r ≠ 99 →
        s.regs r = sP.regs r) ∧
      ∃ (i₀ : ℕ) (sE sF : State) (cost : ℕ) (chE : ChainState cfg.T cfg.P) (curGE : MGraph)
        (curUE : List Update) (curEditsE : List OrdEdit) (curEncE : ℕ)
        (oldOrdE : ℕ → List End) (tokE : ℕ → Rcore.τ) (bE bWE eE eWE : ℕ)
        (levelUE levelUSE : ℕ → List Update) (DE : ℕ → LevelDiffLists),
        BranchBLoopExitAtKFBL w L P depth vCap eCap capExp dgApply copyProc updLen slotProc
          wordExp stretchPrec cfg.N₀ fmt cfg Psc reembFn Rcore RL p opCore ω A
          (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j) ℓ' g'
          (fun j => (C j).1) (fun j => (C j).2.1) (fun j => (C j).2.2)
          (fun j => updStepSpace j U.length) st0 tok.termTok d 0 st0 (G0.applyBatch U_int) U_int
          (G0.batchEnc U_int) s tok.coreTok levelUS D i₀ sE sF cost chE curGE curUE curEditsE
          curEncE oldOrdE tokE bE bWE eE eWE levelUE levelUSE DE ∧
        levelUE 0 = U_int := by
  intro d tr U_int G0 bW gVec lVec ℓ' g' st0 A RL C
  obtain ⟨-, hP4, hPregs, hh0, hS1le, hheap2lo, hheap2hi, hzP, -, -, -, -, hFr1, hFr2, -, hLen0P,
    -, -, -, -, -⟩ := hPre
  have hUH : uIntBuf ≤ heap := by have := S.uLe; have := S.edHeap; omega
  have hSpB := EA.ops.spaceTotalBranchB U.length
  have hRoomH := S.room
  obtain ⟨hTagL0, hCurGCap⟩ := start_len0 S
  have hHh0 : heap ≤ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 := by omega
  have hAg := branchBPrefix_frontAgree S.rep0 S.footLt hUH hHh0 hh0 hTagL0 S.memEq hFr1 hFr2
  have hKeepLow := start_keepLow S hh0 hFr1 hFr2
  have hSlot : heap + 1 + 12 * cfg.P.d ≤ heap2 :=
    ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans
      (hh0.trans ((Nat.le_add_right _ _).trans hheap2lo))
  have hH2 : heap ≤ heap2 := ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans hSlot
  have hLenW : U.length < 2 ^ w := by omega
  have hUW : uIntBuf < 2 ^ w := by omega
  obtain ⟨hBatch, hEdits, hb0, he0, hULenEq⟩ := start_batchEdits S hKeepLow hH2 hLenW hUW
  obtain ⟨r4, r70, r71, r72, r73, r75, r76, r77, r78, r79, r80, r81, r82, r83, r85, r86, r87, r90,
    r91, r92, r93, r94, r95, r98⟩ := hRegs
  obtain ⟨r74, r84, r88, r89⟩ := hRegs2
  have hRegsFL : sP.regs 4 = heap2 ∧ sP.regs 72 = heap ∧ sP.regs 73 = tok.handle ∧
      sP.regs 74 = tok.table ∧ sP.regs 75 = cfg.P.d ∧ sP.regs 76 = cfg.P.k ∧
      sP.regs 77 = tok.handle + 18 ∧ sP.regs 78 = tok.handle + 18 + (cfg.P.d + 1) ∧
      sP.regs 82 = solverLvlMAddr tok.table cfg.P.d ∧
      sP.regs 83 = solverLevelMetaAddr tok.table cfg.P.d ∧
      sP.regs 85 = tok.levelsEnd + 3 * (cfg.P.d + 1) ∧
      sP.regs 86 = tok.levelsEnd + 2 * (cfg.P.d + 1) ∧
      sP.regs 87 = uIntBuf ∧ sP.regs 88 = editsPtr ∧ sP.regs 89 = editWords ∧ sP.regs 94 = L ∧
      sP.regs 95 = P ∧ sP.regs 98 = depth := by
    simp only [hPregs _ (by omega : 70 ≤ 72), hPregs _ (by omega : 70 ≤ 73),
      hPregs _ (by omega : 70 ≤ 74), hPregs _ (by omega : 70 ≤ 75), hPregs _ (by omega : 70 ≤ 76),
      hPregs _ (by omega : 70 ≤ 77), hPregs _ (by omega : 70 ≤ 78), hPregs _ (by omega : 70 ≤ 82),
      hPregs _ (by omega : 70 ≤ 83), hPregs _ (by omega : 70 ≤ 85), hPregs _ (by omega : 70 ≤ 86),
      hPregs _ (by omega : 70 ≤ 87), hPregs _ (by omega : 70 ≤ 88), hPregs _ (by omega : 70 ≤ 89),
      hPregs _ (by omega : 70 ≤ 94), hPregs _ (by omega : 70 ≤ 95), hPregs _ (by omega : 70 ≤ 98)]
    exact ⟨hP4, r72, r73, r74, r75, r76, r77, r78, r82, r83, r85, r86, r87, r88, r89, r94, r95,
      r98.trans EB.depthEq.symm⟩
  have hRoom : heap2 + bW + (Finset.range cfg.P.d).sum (fun j => updStepSpace j U.length) <
      2 ^ w :=
    room_arith rfl hS1le hheap2hi hb0 hSpB hRoomH
  exact wireBranchBFrontLoopKFBL_runs_levelU0 (u := U.length) (ω := ω) (st := sP)
    (heap2 := heap2)
    (model := model) (U := U) (mem0 := mem0) (g := g) (l := l) (m := m) (editsPtr := editsPtr)
    (editWords := editWords) (uIntBuf := uIntBuf) (heap := heap) (tok := tok)
    (stepCap := stepCap) (updStepSpace := updStepSpace) (V := V) (psi := psi) (k := k)
    (epsExp := epsExp) (drainUnit := drainUnit) (root := root) (B := B) (wordExp := wordExp)
    (stretchPrec := stretchPrec) (p := p) (opCore := opCore) (Rcore := Rcore) EB.loop S.rep0
        S.meta0 S.caps0 S.modelInv
    S.refresh S.footLt hUH hSlot S.modelInv.2.1.1 S.shiftInv.lvlM_eq S.bran hAg hRegsFL
    hCurGCap hLen0P hBatch hEdits hzP (hTS _ S.shiftInv) EA.ops.updStepSpaceDom hb0 he0
    hULenEq.le hRoom S.noFire levelUS D
    (branchBStepBatch_ok hTP S.shiftInv S.modelInv S.modelInvKFBL)

end MinCostFlow.MinRatio
