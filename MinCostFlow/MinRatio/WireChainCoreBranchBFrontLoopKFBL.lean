module

public import MinCostFlow.MinRatio.WireChainCoreBranchBLoopKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBFrontKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBFrontRepKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBStaticKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBLoopCapsKFBL
import WordRAM.Tactic

/-!
# The front and the loop of Branch B from the solver rep (`WireChainCoreBranchBFrontLoopKFBL`)

After the prefix of Branch B, the front copies the batch of level `0` to the heap and sets the
loop registers, and the loop runs the plain steps until a level must be rebuilt or all `d` levels
are done. This file runs both from the solver rep at `mem0`, at a state whose memory agrees with
`mem0` on the words that the front reads (the agreement that `branchBPrefix_frontAgree` gives).

* `BranchBLoopExitKFBL`: the facts at the exit of the loop, as `wireBranchBLoopKFBL_runs`
  states them. Naming them lets the later steps take them as one premise.
* `wireBranchBFrontLoopKFBL_runs`: the run of the front, and the exit facts of the loop that
  starts where the front ends. The caps of the loop are the trace caps (`branchBTraceCaps`), and
  the step space is `updStepSpace j u` (`branchBLoop_stepSpace`), so the heap that the loop uses
  is bounded by a sum that depends only on `u`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The facts at the exit of the plain-step loop of Branch B, run from the state `st` at level
`idx` with `rem` levels left: the conclusion of `wireBranchBLoopKFBL_runs`. -/
@[expose] def BranchBLoopExitKFBL (w L P depth vCap eCap capExp dgApply copyProc updLen slotProc
    wordExp stretchPrec N0 : ℕ) (fmt : Num.Format w) (cfg : Alg2Config)
    (Psc : SparseCoreOrdParams) (reembFn : ToolReembFn cfg.T)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (RL : DSRep (ℕ × (ℕ → LSF))) (p : Program)
    (opCore : ℕ → ℕ) (ω : ℕ → Bool) (A : BranchBAddrs) (origLen : ℕ → ℕ → ℝ) (ℓ' g' : ℕ → ℝ)
    (BWc EWc ULc stepSpace : ℕ → ℕ) (ch0 : ChainState cfg.T cfg.P) (termTok : RL.τ)
    (rem idx : ℕ) (ch : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update)
    (curEnc : ℕ) (st : State) (tok : ℕ → Rcore.τ) (levelUS : ℕ → List Update)
    (D : ℕ → LevelDiffLists) : Prop :=
  ∃ (i₀ : ℕ) (sE sF : State) (cost : ℕ) (chE : ChainState cfg.T cfg.P) (curGE : MGraph)
    (curUE : List Update) (curEditsE : List OrdEdit) (curEncE : ℕ)
    (oldOrdE : ℕ → List End) (tokE : ℕ → Rcore.τ) (bE bWE eE eWE : ℕ)
    (levelUE levelUSE : ℕ → List Update) (DE : ℕ → LevelDiffLists),
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

set_option maxHeartbeats 3200000 in
/-- **The front and the loop of Branch B.** The solver rep holds at `mem0`, and the state `st`
after the prefix has the registers of the dispatch, the heap pointer `heap2` above the select
slots, the batch of level `0` at `uIntBuf` (in `editsPtr - d - uIntBuf` words), its edits at
`editsPtr`, the new lengths of level `0`, and a memory that agrees with `mem0` on the words that
the front reads (`hAg`). The tool meets `BranchBToolStepKFBL` at the chain of the model, the step
space meets `updStepSpaceDom` (`hDom`), and the start sizes are within `4 u + 1`, `10 u + 1` and
`u`. Each batch that the loop passes to a level meets `BranchBStepBatchOK` there (the premise
of the conclusion). Then the front runs to a state `s` at heap `heap2 + bW`, and the loop from
`s` exits with the facts `BranchBLoopExitKFBL` at the trace caps, with step space
`updStepSpace j u`. -/
theorem wireBranchBFrontLoopKFBL_runs
    {w L P m V psi k epsExp drainUnit wordExp stretchPrec vCap eCap capExp edMul initCore dgApply
      copyProc updLen slotProc collectProc edgeProc signExt mul intDiv copy depth root uIntBuf
      editsPtr editWords g l heap heap2 u : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opCore : ℕ → ℕ} {ω : ℕ → Bool}
    {mem0 : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update}
    {B : ℤ} {st : State} {stepCap : ℕ → ℕ → ℕ} {updStepSpace : ℕ → ℕ → ℕ}
    (E : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore
      p opCore)
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hRef : RefreshBatch model.extG U)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hUH : uIntBuf ≤ heap) (hSlot : heap + 1 + 12 * cfg.P.d ≤ heap2)
    (hN : model.chain.N₀ = cfg.N₀) (hLvl : model.chain.lvlM = levelM cfg.TP cfg.P)
    (hBran : ∀ j < cfg.P.d, model.chain.bran j < cfg.P.k)
    (hAg : ∀ a, (tok.tag a = 3 ∨ tok.tag a = 4 ∨ tok.tag a = 5 ∨ 19 ≤ tok.tag a) →
      (tok.tag a = 23 + cfg.P.d →
        a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) ∨
        mem0 (solverLevelMetaAddr tok.table cfg.P.d) + eCap * L ≤ a) →
      st.mem a = mem0 a)
    (hRegs : st.regs 4 = heap2 ∧ st.regs 72 = heap ∧ st.regs 73 = tok.handle ∧
      st.regs 74 = tok.table ∧ st.regs 75 = cfg.P.d ∧ st.regs 76 = cfg.P.k ∧
      st.regs 77 = tok.handle + 18 ∧ st.regs 78 = tok.handle + 18 + (cfg.P.d + 1) ∧
      st.regs 82 = solverLvlMAddr tok.table cfg.P.d ∧
      st.regs 83 = solverLevelMetaAddr tok.table cfg.P.d ∧
      st.regs 85 = tok.levelsEnd + 3 * (cfg.P.d + 1) ∧
      st.regs 86 = tok.levelsEnd + 2 * (cfg.P.d + 1) ∧
      st.regs 87 = uIntBuf ∧ st.regs 88 = editsPtr ∧ st.regs 89 = editWords ∧ st.regs 94 = L ∧
      st.regs 95 = P ∧ st.regs 98 = depth)
    (hCurGCap :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      ∀ e ∈ ((model.chain.G 0).applyBatch tr.2.2.2.2).E, e < eCap)
    (hLen0 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      EdgeValuesAt st.mem (mem0 (solverLevelMetaAddr tok.table cfg.P.d)) 4 L P
        ((model.chain.G 0).applyBatch tr.2.2.2.2).E (fun e' => lVec (tr.2.2.1 e')))
    (hBatch :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      SmallBatchAt st.mem uIntBuf (model.chain.G 0) tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf) ∧
      (∀ t < editsPtr - cfg.P.d - uIntBuf, st.mem (uIntBuf + t) < 2 ^ w) ∧
      uIntBuf + cfg.P.d ≤ editsPtr ∧ editsPtr + editWords ≤ heap2)
    (hEdits :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      OrdEditsAt st.mem editsPtr (batchToOrdEdits tr.2.2.2.2) editWords ∧
      (∀ t < editWords, st.mem (editsPtr + t) < 2 ^ w))
    (hz : ZeroFrom st.mem heap2)
    (hT : BranchBToolStepKFBL cfg stepCap model.chain)
    (hDom : ∀ (idx uLen coreH gB bPtr bW ePtr eW lB h nU uL : ℕ), idx < cfg.P.d →
      bW ≤ branchBCapBW stepCap uLen idx → eW ≤ branchBCapEW edMul cfg stepCap uLen idx →
      nU ≤ branchBCapUL stepCap uLen (idx + 1) → uL ≤ branchBCapUL stepCap uLen idx →
      3 * alloc 0 [coreH, gB, bPtr, bW, ePtr, eW, lB, lB, h] + 7 +
        nU * wireCoreLenEdgeSpace (ordLevelLwMax L capExp (levelM cfg.TP cfg.P idx) cfg.N₀) +
        uL + nU ≤ updStepSpace idx uLen)
    (hb0 : editsPtr - cfg.P.d - uIntBuf ≤ 4 * u + 1) (he0 : editWords ≤ 10 * u + 1)
    (hu0 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      tr.2.2.2.2.length ≤ u)
    (hRoom : heap2 + (editsPtr - cfg.P.d - uIntBuf) +
      (Finset.range cfg.P.d).sum (fun j => updStepSpace j u) < 2 ^ w)
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
    (∀ j < d, BranchBStepBatchOK cfg model.chain j
      (branchBStepBatch cfg ℓ' g' d 0 st0 (G0.applyBatch U_int) U_int (G0.batchEnc U_int) j)) →
    ∃ (s : State) (cF : ℕ),
      Runs w p ω (wireBranchBFrontKFBL copyProc) st .normal s cF ∧
      cF ≤ 20 * bW + 60 ∧ s.regs 4 = heap2 + bW ∧ (∀ a < heap2, s.mem a = st.mem a) ∧
      (∀ r, r ≠ 4 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 30 → r ≠ 96 → r ≠ 97 → r ≠ 99 →
        s.regs r = st.regs r) ∧
      BranchBLoopExitKFBL w L P depth vCap eCap capExp dgApply copyProc updLen slotProc wordExp
        stretchPrec cfg.N₀ fmt cfg Psc reembFn Rcore RL p opCore ω A
        (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j) ℓ' g'
        (fun j => (C j).1) (fun j => (C j).2.1) (fun j => (C j).2.2) (fun j => updStepSpace j u)
        st0 tok.termTok d 0 st0 (G0.applyBatch U_int) U_int (G0.batchEnc U_int) s tok.coreTok
        levelUS D := by
  intro d tr U_int G0 bW gVec lVec ℓ' g' st0 A RL C hV
  obtain ⟨hr4, hr72, hr73, hr74, hr75, hr76, hr77, hr78, hr82, hr83, hr85, hr86, hr87, hr88,
    hr89, hr94, hr95, hr98⟩ := hRegs
  have hw : 2 ^ w > heap2 := by omega
  -- the facts of the rep that the front reads
  obtain ⟨hN0c, hCellsR, hTermCells, hRepsR, hDisjR, hGraphsR, hLenGtR, hTermR⟩ :=
    branchBFrontMem_of_rep (heapFloor := heap2) E.loc hRep0 hMeta0 hCaps0 hModelInv hFootLt hUH
      hAg
  obtain ⟨S, hStatic, hN0Word⟩ :=
    branchBStatic_of_rep (heapFloor := heap2) hRep0 hMeta0 hCaps0 hModelInv hFootLt hUH
  obtain ⟨_, _, hEdgeOnly, hOrd0, hValid, hFor⟩ :=
    branchBLevel0Edits_of_rep hRep0 hCaps0 hModelInv hRef
  have hRLLoc : RL.Local :=
    LastLevelProgram.lastLevelRepresentation_local tok.vcLast tok.ecLast 4 L P
      (model.chain.G d).E
  have hLvlj : ∀ j < d, st0.lvlM j = levelM cfg.TP cfg.P j := fun j _ => by
    show model.chain.lvlM j = _; rw [hLvl]
  -- the front
  obtain ⟨s, cF, rF, hcF, hs4, hsFr, hsRegs, I⟩ :=
    wireBranchBFrontKFBL_runs (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (copyProc := copyProc) (N0 := cfg.N₀) (heap := heap2)
      (uIntBuf := uIntBuf) (editsPtr := editsPtr) (editWords := editWords) (fmt := fmt)
      (RL := RL) (p := p) (ω := ω) (reembFn := reembFn) (A := A)
      (origLen := fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j) (ℓ' := ℓ')
      (BWc := fun j => (C j).1) (EWc := fun j => (C j).2.1) (ULc := fun j => (C j).2.2)
      (ch0 := st0) (termTok := tok.termTok) (curG := G0.applyBatch U_int) (U := U_int)
      (edits := batchToOrdEdits U_int) (tok := tok.coreTok) (levelU := fun _ => U_int)
      (levelUS := levelUS) (D := D) (st := st)
      E.loc hRLLoc S (by show heap + 1 + 12 * d ≤ heap2; exact hSlot)
      (by have := E.w16; omega) E.copyP
      ⟨hr4, hr72, hr73, hr74, hr75, hr76, hr77, hr78, hr82, hr83, hr85, hr86, hr87, hr88, hr89,
        hr94, hr95, hr98⟩
      le_rfl (by rw [hN0c]; exact hN) hN0Word
      (fun j hj => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hCellsR j hj
        exact ⟨h1, h2, h3, h4, hBran j hj, lt_of_lt_of_le h5 (by omega), h6, h7, h8, h9⟩)
      hTermCells hRepsR hDisjR hStatic hGraphsR hCurGCap
      (fun _ => by
        show EdgeValuesAt st.mem (mem0 (solverLevelMetaAddr tok.table cfg.P.d + 0)) 4 L P _ ℓ'
        rw [add_zero]; exact hLen0)
      hLenGtR hTermR hBatch hEdgeOnly hEdits hOrd0 hValid hFor ⟨le_rfl, le_rfl, le_rfl⟩ rfl hN hz
      (by omega)
  refine ⟨s, cF, rF, hcF, hs4, hsFr, hsRegs, ?_⟩
  -- the model invariant and the sizes at the start of the loop
  have hM := updateLoopModelInv_of_coreModelInv hCaps0 hModelInv
  have hSz := updateLoopSizeInv_of_traceCaps cfg ℓ' g' edMul
    (fun j => SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) d st0
    (G0.applyBatch U_int) U_int (G0.batchEnc U_int) bW editWords U_int.length
  have hStepSp := branchBLoop_stepSpace (allocation := alloc) hDom hT ℓ' g' (rem := d) le_rfl
    (st := st0) (curG := G0.applyBatch U_int) (curU := U_int) (curEnc := G0.batchEnc U_int)
    (bW0 := bW) (eW0 := editWords) (u := u) (fun _ => rfl) rfl hb0 he0 hu0 hV
  have hRoomL : s.regs 4 + (Finset.Ico 0 d).sum (fun j => updStepSpace j u) < 2 ^ w := by
    rw [hs4, ← Finset.range_eq_Ico]; exact hRoom
  exact wireBranchBLoopKFBL_runs (wordExp := wordExp) (stretchPrec := stretchPrec) E hRLLoc S
    (by show heap + 1 + 12 * d ≤ heap2; exact hSlot) rfl hLvlj hStepSp d 0 st0
    (G0.applyBatch U_int) U_int (batchToOrdEdits U_int) (G0.batchEnc U_int) (st0.levelOrd 0) s
    tok.coreTok heap2 bW editsPtr editWords (fun _ => U_int) levelUS D (by omega) I hM hSz hRoomL

end MinCostFlow.MinRatio
