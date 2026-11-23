module

public import MinCostFlow.MinRatio.WireChainCoreBranchBFrontLoopKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBPartsKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBModelProofLink
import WordRAM.Tactic

/-!
# The loop of Branch B keeps the batch of level `0` (`WireChainCoreBranchBFrontLoopU0KFBL`)

`wireBranchBFrontLoopKFBL_runs` runs the front and the loop of plain steps, but its exit facts do
not say that the loop keeps the batch `levelU 0` of level `0`. We need this fact for the field
`levelU0` of a run of Branch B. `wireBranchBFrontLoopKFBL_runs_levelU0` gives the same run with
the exit facts at named witnesses (`BranchBLoopExitAtKFBL`) and the extra fact
`levelUE 0 = U_int`.

The proof runs the front and the loop a second time, now with `wireBranchBLoopKFBL_runs_levelU0`,
which tracks `levelU 0` but gives fewer facts. Runs are deterministic (`Runs.det`), so both runs
end in the same state. In that state, slot `0` holds an encoding of `levelUE 0` and of the batch
of the second run, which is `U_int`. A batch of edge updates is fixed by its encoding
(`batchAt_eq_of_isEdgeUpdate`), so the two batches are equal.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- `wireBranchBFrontLoopKFBL_runs` with the exit facts at named witnesses and with
`levelUE 0 = U_int`. The extra premise `hNoFire` says that level `0` is not rebuilt, so the loop
does at least one plain step. -/
theorem wireBranchBFrontLoopKFBL_runs_levelU0
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
    (hNoFire : ¬ intRebuildThreshold cfg.P cfg.N₀ 0 < model.chain.updCount 0 +
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2.length)
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
      ∃ (i₀ : ℕ) (sE sF : State) (cost : ℕ) (chE : ChainState cfg.T cfg.P) (curGE : MGraph)
        (curUE : List Update) (curEditsE : List OrdEdit) (curEncE : ℕ)
        (oldOrdE : ℕ → List End) (tokE : ℕ → Rcore.τ) (bE bWE eE eWE : ℕ)
        (levelUE levelUSE : ℕ → List Update) (DE : ℕ → LevelDiffLists),
        BranchBLoopExitAtKFBL w L P depth vCap eCap capExp dgApply copyProc updLen slotProc
          wordExp stretchPrec cfg.N₀ fmt cfg Psc reembFn Rcore RL p opCore ω A
          (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j) ℓ' g'
          (fun j => (C j).1) (fun j => (C j).2.1) (fun j => (C j).2.2)
          (fun j => updStepSpace j u) st0 tok.termTok d 0 st0 (G0.applyBatch U_int) U_int
          (G0.batchEnc U_int) s tok.coreTok levelUS D i₀ sE sF cost chE curGE curUE curEditsE
          curEncE oldOrdE tokE bE bWE eE eWE levelUE levelUSE DE ∧
        levelUE 0 = U_int := by
  intro d tr U_int G0 bW gVec lVec ℓ' g' st0 A RL C hV
  have hFL := wireBranchBFrontLoopKFBL_runs (u := u) (ω := ω) (st := st) (heap2 := heap2)
    (stepCap := stepCap) E hRep0 hMeta0 hCaps0 hModelInv hRef hFootLt hUH hSlot hN hLvl hBran hAg
    hRegs hCurGCap hLen0 hBatch hEdits hz hT hDom hb0 he0 hu0 hRoom levelUS D
  obtain ⟨s, cF, rF, hcF, hs4, hsFr, hsRegs, hEx⟩ := hFL hV
  obtain ⟨i₀, sE, sF, cost, chE, curGE, curUE, curEditsE, curEncE, oldOrdE, tokE, bE, bWE, eE,
    eWE, levelUE, levelUSE, DE, hAt⟩ := hEx.exists_at
  refine ⟨s, cF, rF, hcF, hs4, hsFr, hsRegs, i₀, sE, sF, cost, chE, curGE, curUE, curEditsE,
    curEncE, oldOrdE, tokE, bE, bWE, eE, eWE, levelUE, levelUSE, DE, hAt, ?_⟩
  have hdPos : 0 < d := hModelInv.1.1
  obtain ⟨hr4, hr72, hr73, hr74, hr75, hr76, hr77, hr78, hr82, hr83, hr85, hr86, hr87, hr88,
    hr89, hr94, hr95, hr98⟩ := hRegs
  -- the facts of the rep that the front reads, as in `wireBranchBFrontLoopKFBL_runs`
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
  -- the front again, now keeping its loop invariant `I`
  obtain ⟨s', _, rF', _, _, _, _, I⟩ :=
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
  -- both fronts end in the same state, because runs are deterministic
  have hsEq : s = s' := (Runs.det rF rF').2.1
  subst hsEq
  -- the loop again, with `wireBranchBLoopKFBL_runs_levelU0`
  have hM := updateLoopModelInv_of_coreModelInv hCaps0 hModelInv
  have hSz := updateLoopSizeInv_of_traceCaps cfg ℓ' g' edMul
    (fun j => SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) d st0
    (G0.applyBatch U_int) U_int (G0.batchEnc U_int) bW editWords U_int.length
  have hStepSp := branchBLoop_stepSpace (allocation := alloc) hDom hT ℓ' g' (rem := d) le_rfl
    (st := st0) (curG := G0.applyBatch U_int) (curU := U_int) (curEnc := G0.batchEnc U_int)
    (bW0 := bW) (eW0 := editWords) (u := u) (fun _ => rfl) rfl hb0 he0 hu0 hV
  have hRoomL : s.regs 4 + (Finset.Ico 0 d).sum (fun j => updStepSpace j u) < 2 ^ w := by
    rw [hs4, ← Finset.range_eq_Ico]; exact hRoom
  obtain ⟨i₀', sE', sF', _, _, _, _, _, _, _, _, _, _, _, levelUE', _, _, rL', _, hPos', IE',
      hsF'mem, hU0'⟩ :=
    wireBranchBLoopKFBL_runs_levelU0 (wordExp := wordExp) (stretchPrec := stretchPrec) E hRLLoc S
      (by show heap + 1 + 12 * d ≤ heap2; exact hSlot) rfl hLvlj hStepSp d 0 st0
      (G0.applyBatch U_int) U_int (batchToOrdEdits U_int) (G0.batchEnc U_int) (st0.levelOrd 0) s
      tok.coreTok heap2 bW editsPtr editWords (fun _ => U_int) levelUS D (by omega) I hM hSz
      hRoomL
  -- both loops end in the same state, so their exit states have the same memory
  have hsFEq : sF = sF' := (Runs.det hAt.1 rL').2.1
  have hMemEq : sE'.mem = sE.mem := by
    rw [← hsF'mem, ← hsFEq, hAt.2.2.2.2.2.2.2.2.1]
  -- slot `0` encodes `levelUE 0` and `U_int`; since level `0` is not rebuilt, `0 < i₀`
  have hi0Pos : 0 < i₀ := hAt.2.2.2.1 hNoFire hdPos
  have hi0'Pos : 0 < i₀' := hPos' hNoFire hdPos
  have hSlotH := (hAt.2.2.2.2.1.slots 0 hi0Pos).2.2.2.2.2.1.1
  have hSlot' := (IE'.slots 0 hi0'Pos).2.2.2.2.2.1.1
  rw [hMemEq, hU0'] at hSlot'
  exact (batchAt_eq_of_isEdgeUpdate hEdgeOnly hSlot' hSlotH).symm

end MinCostFlow.MinRatio
