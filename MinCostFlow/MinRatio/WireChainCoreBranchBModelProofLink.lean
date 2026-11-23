module

public import MinCostFlow.MinRatio.WireChainCoreBranchBModelProofKeep
import MinCostFlow.MinRatio.WireChainCoreBranchBFrontKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBFrontLoopKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBLoopKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBBatchOK
import MinCostFlow.MinRatio.WireChainCoreBranchBPrefixAuxKFBL
import MinCostFlow.MinRatio.WireChainCoreSyncDefs
import MinCostFlow.MinRatio.PassReset
import MinCostFlow.SparseCore.Program.AssemblyReemb
import WordRAM.Tactic

/-!
# Level-link and `names` fields for `BranchBModelGoalKFBL` (`WireChainCoreBranchBModelProofLink`)

Proves `branchBModel_link` (`UpdateCoreLevelLink`) and `branchBModel_names` from `BranchBRunKFBL`:
* `wireBranchBLoopKFBL_runs_levelU0`: lightweight induction mirroring `wireBranchBLoopKFBL_runs`
  that tracks `levelUE 0 = levelU 0` across plain passes.
* `branchBModel_levelU0`: proves `H.levelU 0 = H.Uint` by running `wireBranchBFrontKFBL_runs` and
  `wireBranchBLoopKFBL_runs_levelU0`, identifying the final loop state with `H.sL` via `Runs.det`,
  and comparing the two `SmallBatchAt` encodings of slot `0` via `batchAt_eq_of_isEdgeUpdate`.
* `branchBModel_link`: proves all six conjuncts of `UpdateCoreLevelLink`, using
  `branchBModel_levelU0` + `translateBatch_preserves` for `NoBatchReinsert` and
  `branchBModel_case3_Gd_eq` for `j = d` in Case 3 (`fr = d + 1`).
* `branchBModel_names`: proves the `names` field via `branchBModel_names_of_link`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

private theorem ordEditsEnc_batchToOrdEdits_le :
    ∀ U : List Update, ordEditsEnc (batchToOrdEdits U) ≤ 2 * U.length
  | [] => by simp [batchToOrdEdits, ordEditsEnc]
  | u :: rest => by
    have ih := ordEditsEnc_batchToOrdEdits_le rest
    simp only [batchToOrdEdits, List.flatMap_cons, ordEditsEnc, List.map_append, List.sum_append,
      List.length_cons] at ih ⊢
    cases u <;> simp [edgeUpdateToOrdEdits, OrdEdit.enc] <;> omega

/-- Lightweight loop run lemma mirroring `wireBranchBLoopKFBL_runs` that preserves `levelU 0`
across plain passes (`UN j := if j = idx + 1 then nextU else levelU j`). -/
theorem wireBranchBLoopKFBL_runs_levelU0
    {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy wordExp stretchPrec N0 : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {opCore : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ} {ℓ' g' : ℕ → ℝ}
    {BWc EWc ULc stepSpace : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ}
    (E : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore
      p opCore)
    (hRLLoc : RL.Local)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hSlotLe : A.selBase + 1 + 12 * cfg.P.d ≤ A.heapFloor)
    (hN0 : N0 = cfg.N₀) (hLvlM : ∀ j < cfg.P.d, ch0.lvlM j = levelM cfg.TP cfg.P j)
    (hStepSp : ∀ j < cfg.P.d, ∀ coreH gB bPtr bW ePtr eW lB h nU uL : ℕ, bW ≤ BWc j →
      eW ≤ EWc j → nU ≤ ULc (j + 1) → uL ≤ ULc j →
      3 * alloc 0 [coreH, gB, bPtr, bW, ePtr, eW, lB, lB, h] + 7 +
        nU * wireCoreLenEdgeSpace (ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀) +
        uL + nU ≤ stepSpace j) :
    ∀ (rem idx : ℕ) (ch : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update)
      (curEditsList : List OrdEdit) (curEnc : ℕ) (oldOrd : ℕ → List End) (st : State)
      (tok : ℕ → Rcore.τ) (curBatch curBatchWords curEdits curEditsWords : ℕ)
      (levelU levelUS : ℕ → List Update) (D : ℕ → LevelDiffLists),
      idx + rem = cfg.P.d →
      BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
        (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
        EWc ULc ch0 termTok idx ch curG curU curEditsList oldOrd st tok curBatch curBatchWords
        curEdits curEditsWords levelU levelUS D →
      UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen
        ℓ' g' rem idx ch curG curU curEnc oldOrd →
      UpdateLoopSizeInv cfg ℓ' g' edMul
        (fun j => SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) BWc EWc ULc rem
        idx ch curG curU curEnc →
      st.regs 4 + (Finset.Ico idx cfg.P.d).sum stepSpace < 2 ^ w →
      ∃ (i₀ : ℕ) (sE sF : State) (cost : ℕ) (chE : ChainState cfg.T cfg.P) (curGE : MGraph)
        (curUE : List Update) (curEditsE : List OrdEdit) (oldOrdE : ℕ → List End)
        (tokE : ℕ → Rcore.τ) (bE bWE eE eWE : ℕ) (levelUE levelUSE : ℕ → List Update)
        (DE : ℕ → LevelDiffLists),
        Runs w p ω (wireBranchBLoopKFBL (opCore 0) (opCore 2) dgApply copyProc updLen slotProc)
          st .normal sF cost ∧
        idx ≤ i₀ ∧
        (¬ (intRebuildThreshold cfg.P N0 idx < ch.updCount idx + curU.length) →
          idx < cfg.P.d → idx < i₀) ∧
        BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
          (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
          EWc ULc ch0 termTok i₀ chE curGE curUE curEditsE oldOrdE sE tokE bE bWE eE eWE levelUE
          levelUSE DE ∧
        sF.mem = sE.mem ∧
        levelUE 0 = levelU 0 := by
  have hw0 : w ≠ 0 := by intro h; have := E.w16; subst h; omega
  intro rem
  induction rem with
  | zero =>
    intro idx ch curG curU curEditsList _ oldOrd st tok curBatch curBatchWords curEdits
      curEditsWords levelU levelUS D hSum I _ _ _
    have hIdx : idx = cfg.P.d := by omega
    have hr96 := I.regs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hr99 := I.regs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    exact ⟨idx, st, st, 4, ch, curG, curU, curEditsList, oldOrd, tok, curBatch, curBatchWords,
      curEdits, curEditsWords, levelU, levelUS, D,
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr96, hr99, hIdx], rfl, rfl,
        rfl⟩), le_rfl, fun _ h => by omega, I, rfl, rfl⟩
  | succ rem ih =>
    intro idx ch curG curU curEditsList curEnc oldOrd st tok curBatch curBatchWords curEdits
      curEditsWords levelU levelUS D hSum I hM hSz hRoom
    have hIdxLt : idx < cfg.P.d := by omega
    obtain ⟨hFloor, hr10, _, _, _, _, _, hr74, _, _, _, _, _, _, hr85, _, _, _, hr96, _, _,
      hr99⟩ := I.regs
    have hIco : ∀ (f : ℕ → ℕ) (k : ℕ), idx < k →
        (Finset.Ico idx k).sum f = f idx + (Finset.Ico (idx + 1) k).sum f := fun f k hk => by
      have h1 : Finset.Ico idx k = insert idx (Finset.Ico (idx + 1) k) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [h1, Finset.sum_insert (by simp)]
    have hUCW : ch.updCount idx + curU.length < 2 ^ w := hM.1
    by_cases hOver : intRebuildThreshold cfg.P N0 idx < ch.updCount idx + curU.length
    · have hucLt := S.ucLt
      have htabLt := S.tableLt
      obtain ⟨sF, rBody, hsFmem, hsFregs, hsF99⟩ :=
        wireBranchBLoopBodyKFBL_runs_over (opCore 0) (opCore 2) dgApply copyProc updLen slotProc
          (p := p) (ω := ω) hr10 I.batchLen hr85 hr96 hr74 (I.cells idx hIdxLt).2.2.2.2.2.2.2.2.1
          (I.cells idx hIdxLt).1 (by omega) (by omega) hUCW hOver
      have hsF96 : sF.regs 96 = idx := (hsFregs 96 (by decide) (by decide) (by decide)
        (by decide)).trans hr96
      have rLoop : Runs w p ω
          (wireBranchBLoopKFBL (opCore 0) (opCore 2) dgApply copyProc updLen slotProc)
          st .normal sF (3 + 24 + 4 + 1) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, sF, 24, 4,
          by simp [Expr.eval, BinOp.eval, hr96, hr99, hIdxLt, hw0], by decide, rBody,
          runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hsF96, hsF99], rfl, rfl,
            rfl⟩), rfl⟩))
      exact ⟨idx, st, sF, _, ch, curG, curU, curEditsList, oldOrd, tok, curBatch, curBatchWords,
        curEdits, curEditsWords, levelU, levelUS, D, rLoop, le_rfl, fun h _ => absurd hOver h,
        I, hsFmem, rfl⟩
    · have hRoom1 : st.regs 4 + stepSpace idx < 2 ^ w := by
        rw [hIco stepSpace cfg.P.d hIdxLt] at hRoom; omega
      obtain ⟨out, cB, tok1, nextEdits, c, rBody, hSpace, hOut⟩ :=
        wireBranchBLoopBodyKFBL_runs_plain (ω := ω) E S hSlotLe hN0 hLvlM
          (by omega : idx + (rem + 1) = cfg.P.d) I hM hSz hOver (hStepSp idx hIdxLt) hRoom1
      obtain ⟨I', hM', hSz', _⟩ :=
        branchBLoopInvKFBL_pass E.loc hRLLoc S hSlotLe (by omega : idx + (rem + 1) = cfg.P.d) I
          hM hSz hOver hOut
      have h4 : Function.update out.regs 96 (idx + 1) 4 = out.regs 4 :=
        Function.update_of_ne (by decide) _ _
      have hRoom' : ({ out with regs := Function.update out.regs 96 (idx + 1) } : State).regs 4 +
          (Finset.Ico (idx + 1) cfg.P.d).sum stepSpace < 2 ^ w := by
        show Function.update out.regs 96 (idx + 1) 4 + _ < _
        rw [h4]
        rw [hIco stepSpace cfg.P.d hIdxLt] at hRoom
        omega
      obtain ⟨i₀, sE, sF, cR, chE, curGE, curUE, curEditsE, oldOrdE, tokE, bE, bWE, eE, eWE,
          levelUE, levelUSE, DE, rRest, hi1, _, IE, hsFmem, hU0⟩ :=
        ih (idx + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) I' hM' hSz' hRoom'
      have rLoop : Runs w p ω
          (wireBranchBLoopKFBL (opCore 0) (opCore 2) dgApply copyProc updLen slotProc)
          st .normal sF (3 + cB + cR + 1) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, cB, cR,
          by simp [Expr.eval, BinOp.eval, hr96, hr99, hIdxLt, hw0], by decide, rBody, rRest,
          rfl⟩))
      refine ⟨i₀, sE, sF, _, chE, curGE, curUE, curEditsE, oldOrdE, tokE, bE, bWE, eE, eWE,
        levelUE, levelUSE, DE, rLoop, by omega, fun _ _ => by omega, IE, hsFmem, ?_⟩
      exact hU0.trans (ite_eq_right (by omega))

section LinkFields

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

/-- Recovers `H.levelU 0 = H.Uint` by re-running the front and the lightweight loop lemma
`wireBranchBLoopKFBL_runs_levelU0`, identifying the end memory with `H.sE.mem` via `Runs.det`,
and applying `batchAt_eq_of_isEdgeUpdate` to slot `0`. -/
theorem branchBModel_levelU0
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    H.levelU 0 = H.Uint := by
  set d := cfg.P.d
  set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  set U_int := tr.2.2.2.2
  set G0 := model.chain.G 0
  set bW := editsPtr - d - uIntBuf
  set gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
  set lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
  set ℓ' := fun e' => lVec (tr.2.2.1 e')
  set g' := fun e' => gVec (tr.2.2.1 e')
  set st0 : ChainState cfg.T cfg.P :=
    { model.chain with
      recUpdates := fun j =>
        if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
  set A := branchBAddrsOf tok mem0 heap H.heap2
  set RL := LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
    (model.chain.G d).E
  set C := branchBTraceCaps edMul
    (fun j => SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) bW editWords
    U_int.length (branchBStepData cfg ℓ' g' d 0 st0 (G0.applyBatch U_int) U_int (G0.batchEnc U_int))
  have hdPos : 0 < d := H.start.modelInv.1.1
  have hUH : uIntBuf ≤ heap := by have := H.start.uLe; have := H.start.edHeap; omega
  have hSlot : heap + 1 + 12 * d ≤ H.heap2 := by
    have := H.pre.2.2.2.1; have := H.pre.2.2.2.2.2.1; omega
  have hInv := H.start.shiftInv.1
  have hN : model.chain.N₀ = cfg.N₀ := hInv.hN0
  have hLvl : model.chain.lvlM = levelM cfg.TP cfg.P := hInv.hLvlM
  have hFresh : FreshInv model.extG G0 model.extToInt model.intToExt model.nextFresh :=
    H.start.rep0.2.2.2.2.1
  have hOwn := H.start.rep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hT1 := H.start.rep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLt {x : ℕ} (ht : tok.tag x ≠ 0) : x < uIntBuf := H.start.footLt x (Or.inl (hOwn x ht))
  -- Agreement `H.sP.mem = mem0` on front words
  have hTagL0 : ∀ a, mem0 (solverLevelMetaAddr tok.table d) ≤ a →
      a < mem0 (solverLevelMetaAddr tok.table d) + eCap * L → tok.tag a = 23 + d := by
    intro a h1 h2
    obtain ⟨_, _, _, _, _, _, _, _, ⟨_, vcOf, ecOf, hLev, _, _⟩, _⟩ := H.start.modelInv
    have hCap0 := dynGraphAt_caps_eq (hLev 0 hdPos).1 (H.start.caps0 0 hdPos)
    have hL := (hLev 0 hdPos).2.2.2.1
    rw [add_zero, hCap0.2] at hL
    exact hL a h1 h2
  have hAg : ∀ a, (tok.tag a = 3 ∨ tok.tag a = 4 ∨ tok.tag a = 5 ∨ 19 ≤ tok.tag a) →
      (tok.tag a = 23 + d →
        a < mem0 (solverLevelMetaAddr tok.table d) ∨
        mem0 (solverLevelMetaAddr tok.table d) + eCap * L ≤ a) →
      H.sP.mem a = mem0 a := by
    intro a ht hOff23
    have haU : a < uIntBuf := hLt (by omega)
    have hR11 : a ≠ root + 11 := fun h => by
      have h1 := hT1 11 (by omega); rw [← h] at h1; omega
    have hOffL0 : a < mem0 (solverLevelMetaAddr tok.table d) ∨
        mem0 (solverLevelMetaAddr tok.table d) + eCap * L ≤ a := by
      by_cases h23 : tok.tag a = 23 + d
      · exact hOff23 h23
      · by_contra hc; simp only [not_or, not_lt, not_le] at hc
        exact h23 (hTagL0 a hc.1 hc.2)
    rw [branchBModel_prefixFrame H a (by omega) hR11 (fun _ => by omega) hOffL0]
    exact H.start.memEq a haU (by omega) (by omega) (by omega)
  -- `H.sP.mem = mem` on `[uIntBuf, heap)`
  have hHighAg : ∀ a, uIntBuf ≤ a → a < heap → H.sP.mem a = mem a := by
    intro a ha1 ha2
    have hR11 : a ≠ root + 11 := fun h => by
      have h1 := hLt (by rw [hT1 11 (by omega)]; decide); omega
    have hOffL0 : a < mem0 (solverLevelMetaAddr tok.table d) ∨
        mem0 (solverLevelMetaAddr tok.table d) + eCap * L ≤ a := by
      by_contra hc; simp only [not_or, not_lt, not_le] at hc
      have h1 := hLt (by rw [hTagL0 a hc.1 hc.2]; omega); omega
    exact branchBModel_prefixFrame H a ha2 hR11 (fun hU => absurd ha1 (by omega)) hOffL0
  -- Front memory and static facts
  obtain ⟨hN0c, hCellsR, hTermCells, hRepsR, hDisjR, hGraphsR, hLenGtR, hTermR⟩ :=
    branchBFrontMem_of_rep (heapFloor := H.heap2) H.envB.loop.loc H.start.rep0 H.start.meta0
      H.start.caps0 H.start.modelInv H.start.footLt hUH hAg
  obtain ⟨S, hStatic, hN0Word⟩ :=
    branchBStatic_of_rep (heapFloor := H.heap2) H.start.rep0 H.start.meta0 H.start.caps0
      H.start.modelInv H.start.footLt hUH
  obtain ⟨_, _, hEdgeOnly, hOrd0, hValid, hFor⟩ :=
    branchBLevel0Edits_of_rep H.start.rep0 H.start.caps0 H.start.modelInv H.start.refresh
  have hRLLoc : RL.Local :=
    LastLevelProgram.lastLevelRepresentation_local tok.vcLast tok.ecLast 4 L P (model.chain.G d).E
  have hLvlj : ∀ j < d, st0.lvlM j = levelM cfg.TP cfg.P j := fun j _ => by
    show model.chain.lvlM j = _; rw [hLvl]
  -- Bounds on `bW`, `editWords`, `U_int.length`, and heap room
  have hULenEq : U_int.length = U.length :=
    (translateBatch_preserves U model.extG G0 model.extToInt model.intToExt model.nextFresh hFresh
      H.start.refresh.1).2.2.2.2.1
  have hb0 : bW ≤ 4 * U.length + 1 := by
    have h1 : bW ≤ 4 * U_int.length + 1 := smallBatchAt_words_le_edgeOnly H.start.small hEdgeOnly
    omega
  have he0 : editWords ≤ 10 * U.length + 1 := by
    have h1 : editWords ≤ 5 * ordEditsEnc (batchToOrdEdits U_int) + 1 := H.start.edits.2.2
    have h2 : ordEditsEnc (batchToOrdEdits U_int) ≤ 2 * U_int.length :=
      ordEditsEnc_batchToOrdEdits_le U_int
    omega
  have hSpB := H.envA.ops.spaceTotalBranchB U.length
  have hRoomH := H.start.room
  have hhS1Hi : H.hS1 ≤ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 + 3 * U.length +
      U.length * wireTreeSyncEditSpace L := H.pre.2.2.2.2.1
  have hHeap2Hi : H.heap2 ≤ H.hS1 + 3 * L + U.length * wireRefreshOneSpace L :=
    H.pre.2.2.2.2.2.2.1
  have hRoomLoop : H.heap2 + bW + (Finset.range d).sum (fun j => updStepSpace j U.length) < 2 ^ w := by
    change H.heap2 + bW + (Finset.range cfg.P.d).sum (fun j => updStepSpace j U.length) < 2 ^ w
    omega
  have hCurGCap : ∀ e ∈ (G0.applyBatch U_int).E, e < eCap := by
    obtain ⟨_, _, _, _, _, _, _, _, ⟨hRootEq, _, _⟩, _, hG0'Cap, _⟩ := H.start.modelInv
    have hDG0 := H.start.caps0 0 hdPos
    rw [hRootEq] at hDG0
    have hRootCap := dynGraphAt_caps_eq H.start.rep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1 hDG0
    intro e he; rw [← hRootCap.2]; exact (hG0'Cap e he).1
  have hBatchWMem : ∀ t < bW, mem (uIntBuf + t) < 2 ^ w :=
    branchB_batchWords_lt H.start.rep0 H.start.modelInv H.start.refresh H.start.trNf H.start.batch
      H.start.small H.start.footLt (by omega) (by omega)
  have hBatchSP : SmallBatchAt H.sP.mem uIntBuf G0 U_int bW ∧
      (∀ t < bW, H.sP.mem (uIntBuf + t) < 2 ^ w) ∧
      uIntBuf + d ≤ editsPtr ∧ editsPtr + editWords ≤ H.heap2 := by
    have hEdH := H.start.edHeap; have hUL := H.start.uLe
    refine ⟨smallBatchAt_congr H.start.small fun x hx1 hx2 => hHighAg x (by omega) (by omega),
      fun t ht => by rw [hHighAg (uIntBuf + t) (by omega) (by omega)]; exact hBatchWMem t ht,
      hUL, by omega⟩
  have hEditsSP : OrdEditsAt H.sP.mem editsPtr (batchToOrdEdits U_int) editWords ∧
      (∀ t < editWords, H.sP.mem (editsPtr + t) < 2 ^ w) := by
    have hEdH := H.start.edHeap; have hUL := H.start.uLe
    refine ⟨ordEditsAt_of_agree H.start.edits fun x hx1 hx2 => hHighAg x (by omega) (by omega),
      fun t ht => by rw [hHighAg (editsPtr + t) (by omega) (by omega)]; exact H.start.editsW t ht⟩
  -- Registers of `H.sP`
  have hReg70 := H.pre.2.2.1
  obtain ⟨_, _, _, r72, r73, r75, r76, r77, r78, _, _, _, r82, r83, r85, r86, r87, _, _, _, _,
    r94, r95, r98⟩ := H.dispatch.2.2.1
  obtain ⟨r74, _, r88, r89⟩ := H.dispatch.2.2.2
  have hRegsSP : H.sP.regs 4 = H.heap2 ∧ H.sP.regs 72 = A.selBase ∧ H.sP.regs 73 = A.handle ∧
      H.sP.regs 74 = A.table ∧ H.sP.regs 75 = d ∧ H.sP.regs 76 = cfg.P.k ∧
      H.sP.regs 77 = A.handleBase ∧ H.sP.regs 78 = A.branchBase ∧ H.sP.regs 82 = A.lvlMTable ∧
      H.sP.regs 83 = A.levelMeta ∧ H.sP.regs 85 = A.ucBase ∧ H.sP.regs 86 = A.rcBase ∧
      H.sP.regs 87 = uIntBuf ∧ H.sP.regs 88 = editsPtr ∧ H.sP.regs 89 = editWords ∧
      H.sP.regs 94 = L ∧ H.sP.regs 95 = P ∧ H.sP.regs 98 = depth :=
    ⟨H.pre.2.1,
      (hReg70 72 (by decide)).trans r72, (hReg70 73 (by decide)).trans r73,
      (hReg70 74 (by decide)).trans r74, (hReg70 75 (by decide)).trans r75,
      (hReg70 76 (by decide)).trans r76, (hReg70 77 (by decide)).trans r77,
      (hReg70 78 (by decide)).trans r78, (hReg70 82 (by decide)).trans r82,
      (hReg70 83 (by decide)).trans r83, (hReg70 85 (by decide)).trans r85,
      (hReg70 86 (by decide)).trans r86, (hReg70 87 (by decide)).trans r87,
      (hReg70 88 (by decide)).trans r88, (hReg70 89 (by decide)).trans r89,
      (hReg70 94 (by decide)).trans r94, (hReg70 95 (by decide)).trans r95,
      by rw [hReg70 98 (by decide), r98, H.envB.depthEq]⟩
  -- Run the front from `H.sP`
  obtain ⟨s', _, rF', _, hs'4, _, _, I0'⟩ :=
    wireBranchBFrontKFBL_runs (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (copyProc := copyProc) (N0 := cfg.N₀) (heap := H.heap2)
      (uIntBuf := uIntBuf) (editsPtr := editsPtr) (editWords := editWords) (fmt := fmt)
      (RL := RL) (p := p) (ω := ω) (reembFn := reembFn) (A := A)
      (origLen := fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j) (ℓ' := ℓ')
      (BWc := fun j => (C j).1) (EWc := fun j => (C j).2.1) (ULc := fun j => (C j).2.2)
      (ch0 := st0) (termTok := tok.termTok) (curG := G0.applyBatch U_int) (U := U_int)
      (edits := batchToOrdEdits U_int) (tok := tok.coreTok) (levelU := fun _ => U_int)
      (levelUS := H.levelUS0) (D := H.D0) (st := H.sP)
      H.envB.loop.loc hRLLoc S hSlot (by have := H.envB.loop.w16; omega) H.envB.loop.copyP
      hRegsSP le_rfl (by rw [hN0c]; exact hN) hN0Word
      (fun j hj => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hCellsR j hj
        exact ⟨h1, h2, h3, h4, H.start.bran j hj, lt_of_lt_of_le h5 (by omega), h6, h7, h8, h9⟩)
      hTermCells hRepsR hDisjR hStatic hGraphsR hCurGCap
      (fun _ => by
        show EdgeValuesAt H.sP.mem (mem0 (solverLevelMetaAddr tok.table d + 0)) 4 L P _ ℓ'
        rw [add_zero]
        exact H.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      hLenGtR hTermR hBatchSP hEdgeOnly hEditsSP hOrd0 hValid hFor ⟨le_rfl, le_rfl, le_rfl⟩ rfl hN
      H.pre.2.2.2.2.2.2.2.1 (by omega)
  -- Run the lightweight loop from `s'` carrying `levelUE' 0 = U_int`
  have hM := updateLoopModelInv_of_coreModelInv H.start.caps0 H.start.modelInv
  have hSz := updateLoopSizeInv_of_traceCaps cfg ℓ' g' edMul
    (fun j => SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) d st0
    (G0.applyBatch U_int) U_int (G0.batchEnc U_int) bW editWords U_int.length
  have hV := branchBStepBatch_ok H.tpValid H.start.shiftInv H.start.modelInv H.start.modelInvKFBL
  have hStepSp := branchBLoop_stepSpace (allocation := allocation) H.envA.ops.updStepSpaceDom
    (H.toolStep model.chain H.start.shiftInv) ℓ' g' (rem := d) le_rfl
    (st := st0) (curG := G0.applyBatch U_int) (curU := U_int) (curEnc := G0.batchEnc U_int)
    (bW0 := bW) (eW0 := editWords) (u := U.length) (fun _ => rfl) rfl hb0 he0 (by omega) hV
  have hRoomL' : s'.regs 4 + (Finset.Ico 0 d).sum (fun j => updStepSpace j U.length) < 2 ^ w := by
    rw [hs'4, ← Finset.range_eq_Ico]; exact hRoomLoop
  obtain ⟨i₀', sE', sF', _, _, _, _, _, _, _, _, _, _, _, levelUE', _, _, rL', _, hPos', IE',
      hsF'mem, hU0'⟩ :=
    wireBranchBLoopKFBL_runs_levelU0 (wordExp := wordExp) (stretchPrec := stretchPrec) H.envB.loop
      hRLLoc S hSlot rfl hLvlj hStepSp d 0 st0 (G0.applyBatch U_int) U_int (batchToOrdEdits U_int)
      (G0.batchEnc U_int) (st0.levelOrd 0) s' tok.coreTok H.heap2 bW editsPtr editWords
      (fun _ => U_int) H.levelUS0 H.D0 (by omega) I0' hM hSz hRoomL'
  -- Identify `s' = H.sF0` and `sF' = H.sL` via `Runs.det`
  have hsEq : H.sF0 = s' := (Runs.det H.front.1 rF').2.1
  rw [← hsEq] at rL'
  have hsLEq : H.sL = sF' := (Runs.det H.loop.1 rL').2.1
  have hMemEq : sE'.mem = H.sE.mem := by
    rw [← hsF'mem, ← hsLEq, H.loop.2.2.2.2.2.2.2.2.1]
  -- Compare `SmallBatchAt` at slot 0 in `H.sE.mem`
  have hi0Pos : 0 < H.i₀ := H.loop.2.2.2.1 (by rw [H.st0_eq, H.Uint_eq]; exact H.start.noFire) hdPos
  have hi0'Pos : 0 < i₀' := hPos' H.start.noFire hdPos
  have hSlotH := (H.loop.2.2.2.2.1.slots 0 hi0Pos).2.2.2.2.2.1.1
  have hSlot' := (IE'.slots 0 hi0'Pos).2.2.2.2.2.1.1
  rw [hMemEq, hU0'] at hSlot'
  rw [H.A_eq, H.st0_eq] at hSlotH
  have hEq : U_int = H.levelU 0 := batchAt_eq_of_isEdgeUpdate hEdgeOnly hSlot' hSlotH
  rw [H.Uint_eq]
  exact hEq.symm

/-- Proves the `link` (`UpdateCoreLevelLink`) field of `BranchBModelFieldsKFBL`. -/
theorem branchBModel_link
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    UpdateCoreLevelLink model.chain
      (alg2PreResetState cfg model U
        (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
        (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain
      H.fr H.levelU H.levelUS := by
  set gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
  set lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
  have hMod : (alg2PreResetState cfg model U gVec lVec).chain = H.X := by
    dsimp only [gVec, lVec]; rw [← H.gVec_eq, ← H.lVec_eq]; exact H.modelEq.symm
  rw [hMod]
  have hI := H.loop.2.2.2.2.1
  have hFrLe : H.fr ≤ cfg.P.d + 1 := H.exitOut.frLe
  have hMin : min H.fr cfg.P.d = H.i₀ := branchBModel_min_fr_d H
  have hChEReb : H.chE.rebuildCount = model.chain.rebuildCount := by
    rw [hI.modelFrame.2.2.2.2.2.2.2, H.st0_eq]
  have hSt0G : H.st0.G = model.chain.G := by rw [H.st0_eq]
  have hSt0Sc : H.st0.scState = model.chain.scState := by rw [H.st0_eq]
  have hSt0Br : H.st0.bran = model.chain.bran := by rw [H.st0_eq]
  have hChEBr : H.chE.bran = model.chain.bran := hI.modelFrame.2.1.trans hSt0Br
  -- `NoBatchReinsert` at level 0
  have hNR0 : NoBatchReinsert (model.chain.G 0) (H.levelU 0) := by
    rw [branchBModel_levelU0 H, H.Uint_eq]
    exact (translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt model.intToExt
      model.nextFresh H.start.rep0.2.2.2.2.1 H.start.refresh.1).2.2.2.1
  refine ⟨hFrLe, ?_, ?_, ?_, ?_, ?_⟩
  · -- `fr < d → firstRebuiltLevel = some fr`
    intro hlt
    rcases H.exitCase with h1 | h2 | h3
    · obtain ⟨_, hiLt, hfrEq, _, _, hXeq, _⟩ := h1
      have hR := algorithm1_rebuild_lt cfg.T cfg.L cfg.P { H.chE with ℓ := H.ℓ', g := H.g' }
        hiLt H.curGE H.curEncE
      rw [hXeq, hR.2.2.2, hfrEq]
      dsimp only
      rw [hChEReb]
      exact Chain.firstRebuiltLevel_eq_of_inc hiLt model.chain.rebuildCount
    · omega
    · omega
  · -- `d ≤ fr → firstRebuiltLevel = none`
    intro hge
    have hRebEq : H.X.rebuildCount = model.chain.rebuildCount := by
      rcases H.exitCase with h1 | h2 | h3
      · omega
      · obtain ⟨_, hne, _, _, _, hXeq, _⟩ := h2
        rw [hXeq]; simp only [Chain.Ordered.updateLoop, hne, ↓reduceIte]; exact hChEReb
      · obtain ⟨_, hemp, _, _, _, hXeq, _⟩ := h3
        rw [hXeq]; simp only [Chain.Ordered.updateLoop, hemp, ↓reduceIte]; exact hChEReb
    rw [hRebEq]
    exact Chain.firstRebuiltLevel_eq_of_eq model.chain.rebuildCount
  · -- `0 < fr → NonRebuiltBatches`
    intro hPos
    refine ⟨by omega, hNR0, ?_, ?_, ?_⟩
    · -- `∀ j ≤ fr - 1, X.G j = (model.chain.G j).applyBatch (levelU j) ∧ BatchIsValid`
      intro j hj
      by_cases hlt : j < H.i₀
      · have hXlt := branchBModel_X_lt H hlt
        have hSm := hI.slotModel j hlt
        rw [hXlt.1, hSm.2.2.2.2.2.2.1, hSt0G]
        exact ⟨rfl, hSt0G ▸ hSm.2.2.2.2.2.2.2.1⟩
      · -- Only possible in Case 3 (`i₀ = d`, `curUE = []`, `fr = d + 1`, `j = d`)
        rcases H.exitCase with h1 | h2 | h3
        · omega
        · omega
        · obtain ⟨hiD, hEmpty, hfrEq, _⟩ := h3
          have hjEq : j = cfg.P.d := by omega
          subst hjEq
          have hUd : H.levelU cfg.P.d = [] := by
            rw [← hiD, hI.curULink, hEmpty]
          rw [hUd, branchBModel_case3_Gd_eq H hiD hEmpty]
          exact ⟨rfl, trivial⟩
    · -- `∀ j ≤ fr - 1, j < d → ...`
      intro j hj hjd
      have hlt : j < H.i₀ := by omega
      have hXlt := branchBModel_X_lt H hlt
      have hSm := hI.slotModel j hlt
      obtain ⟨ℓj, gj, ordj, hSc, hUS⟩ := hSm.2.2.2.2.2.2.2.2.2
      rw [hXlt.2.2.1, hChEBr]
      refine ⟨rfl, ℓj, gj, ordj, ?_, fun _ => ?_⟩
      · rw [hXlt.2.1, hSc, hSt0Sc]
      · rw [hSm.2.2.2.2.2.2.2.2.1, hUS, hSt0Sc, hSt0Br]
    · -- `fr - 1 = d → levelU d = [] ∧ X.lastLSFs = model.chain.lastLSFs ∧ X.lastBran = model.chain.lastBran`
      intro hEq
      rcases H.exitCase with h1 | h2 | h3
      · omega
      · omega
      · obtain ⟨hiD, hEmpty, _, _, _, hXeq, _⟩ := h3
        have hUd : H.levelU cfg.P.d = [] := by rw [← hiD, hI.curULink, hEmpty]
        rw [hUd, hXeq]
        refine ⟨rfl, ?_, ?_⟩
        · simp only [Chain.Ordered.updateLoop, hEmpty, ↓reduceIte]
          rw [hI.modelFrame.2.2.2.1, H.st0_eq]
        · simp only [Chain.Ordered.updateLoop, hEmpty, ↓reduceIte]
          rw [hI.modelFrame.2.2.2.2.1, H.st0_eq]
  · -- `∀ j < min fr d, levelU (j + 1) = levelUS j ∧ ∃ ℓj gj ordj, ...`
    intro j hj
    have hlt : j < H.i₀ := by rw [← hMin]; exact hj
    have hXlt := branchBModel_X_lt H hlt
    have hSm := hI.slotModel j hlt
    obtain ⟨ℓj, gj, ordj, hSc, hUS⟩ := hSm.2.2.2.2.2.2.2.2.2
    refine ⟨hSm.2.2.2.2.2.2.2.2.1, ℓj, gj, ordj, ?_, ?_⟩
    · rw [hXlt.2.1, hSc, hSt0Sc]
    · rw [hUS, hSt0Sc, hSt0Br]
  · -- `fr = d → levelU d ≠ []`
    intro hfrD
    rcases H.exitCase with h1 | h2 | h3
    · omega
    · obtain ⟨hiD, hne, _⟩ := h2
      rw [← hiD, hI.curULink]
      exact hne
    · omega

/-- Proves the `names` field of `BranchBModelFieldsKFBL`. -/
theorem branchBModel_names
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let modelPre := alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)
    modelPre.extToInt = tr.2.1 ∧ modelPre.intToExt = tr.2.2.1 ∧ modelPre.nextFresh = tr.2.2.2.1 :=
  branchBModel_names_of_link H (branchBModel_link H)

end LinkFields

end MinCostFlow.MinRatio
