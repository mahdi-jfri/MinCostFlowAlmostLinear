module

public import MinCostFlow.MinRatio.WireChainCoreMetaDisjBranchBReb
public import MinCostFlow.MinRatio.WireChainCoreBranchBIntExitKFBL
public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBExitLayInt
import WordRAM.Tactic

/-!
# Rebuilt-block order at the Branch B interior exit (`WireChainCoreMetaDisjBranchB`)

This file proves the block-ordering fact `BranchBRebuiltOrdKFBL` on the exit state of the
interior rebuild step `wireBranchBIntKFBL` of Branch B, on the exact range `i₀ + 1, …, d - 1`
written by `ordRebuildSuffixProgramKFBLStore_runs_ord` (level `i₀` keeps its old `levelMeta`
pointers below `A.selBase`):
* `wireBranchBIntKFBL_runs_exit_ord`: runs `wireBranchBIntKFBL` from the loop-exit state and
  produces `BranchBRebuiltOrdKFBL A.levelMeta cfg.P.d (i₀ + 1)` at both `sE.regs 4` and
  `A.selBase`.
* `wireBranchBIntKFBL_exit_rebuiltOrd`: by determinism of `Runs` (`Runs.det`), the same ordering
  holds for every run of `wireBranchBIntKFBL`.
* `wireBranchBIntKFBL_exit_metaDisj`: instantiating `branchB_metaDisj` at `fr := i₀ + 1` gives
  `SolverLevelMetaDisjAt vCap eCap tok' out.mem` at the interior exit from `SolverLevelMetaDisjAt`
  on the start state.
* `OrdChainCoreBranchBMetaDisjKFBL`: the Branch B case of the meta-disjointness clause of the
  chain core, in the form of `OrdChainCoreBranchBPostKFBL`. `branchB_metaDisj_end`
  (`WireChainCoreBranchBMetaDisjEndKFBL.lean`) proves it.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- **The meta-disjointness clause for Branch B.** When the rebuild test at level `0` does not
fire, every run of the chain core `body` from a start state meeting the Ext-spec premises
and `SolverLevelMetaDisjAt vCap eCap tok mem0` ends in a state meeting
`SolverLevelMetaDisjAt vCap eCap tok' out.mem` for any `tok'` with `tok'.table = tok.table`. -/
@[expose] def OrdChainCoreBranchBMetaDisjKFBL
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap : ℕ)
    (cfg : Alg2Config) (G : MGraph) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (coreSpace : ℕ → ℕ) (body : Stmt) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
    (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore)
    (U : List Update) (B R : ℤ),
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
    let modelPre := alg2PreResetState cfg model U gVec lVec
    Rrep.rep root model tok mem0 →
    SolverLevelMetaAt P V model tok mem0 →
    SolverLevelCapsAt vCap eCap model tok mem0 →
    SolverLevelMetaDisjAt vCap eCap tok mem0 →
    tok.intCap = initTargetCap cfg G →
    model.extG.m = m →
    PathTreeNumericInv tok.tree tok.trees B R →
    OffTreeRecInv model L mem0 tok.edgeRecords B →
    OffTreeRecBound model L mem0 tok.edgeRecords B →
    Chain.Ordered.ShiftLoopChainInv cfg model.chain →
    WireCapFacts capExp limbMul L capLimit model →
    (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
    UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B →
    UpdateCoreModelInvKFBL model U gVec lVec →
    tok.intCap ≤ intCapMax →
    graphListEdgeSum (chainSuffixForests model.chain 0) +
      graphListEdgeSum (chainSuffixForests modelPre.chain 0) ≤ forestEdgeCap →
    Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
    2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
    (∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a) →
    FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
      tr.2.1 tr.2.2.1 tr.2.2.2.1 →
    tr.2.2.2.1 ≤ tok.intCap →
    BatchAt mem uIntBuf tr.2.2.2.2 →
    SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf) →
    OrdEditsAt mem editsPtr (batchToOrdEdits tr.2.2.2.2) editWords →
    (∀ j < editWords, mem (editsPtr + j) < 2 ^ w) →
    editsPtr + editWords = heap →
    RefreshBatch model.extG U →
    (∀ a, Rrep.foot root tok a → a < uIntBuf) →
    g + m * L ≤ uIntBuf → l + m * L ≤ uIntBuf →
    uIntBuf + cfg.P.d ≤ editsPtr →
    ZeroFrom mem heap →
    heap + coreSpace U.length < 2 ^ w →
    ¬ intRebuildThreshold cfg.P cfg.N₀ 0 < model.chain.updCount 0 + tr.2.2.2.2.length →
    ∀ (nextHeap cost : ℕ) (out : State) (tok' : SolverToken cfg L Rcore),
      Runs w p ω body (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
        (.returned nextHeap) out cost →
      tok'.table = tok.table →
      SolverLevelMetaDisjAt vCap eCap tok' out.mem

set_option maxHeartbeats 1600000 in
/-- **Rebuilt-block order at the interior exit of Branch B.** Runs `wireBranchBIntKFBL` from the
loop-exit state at `0 < i₀ < d` and proves `BranchBRebuiltOrdKFBL A.levelMeta cfg.P.d (i₀ + 1)`
at both `sE.regs 4` and `A.selBase`. -/
theorem wireBranchBIntKFBL_runs_exit_ord
    {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy N0 oldPtrs newPtrs intCap i₀ wordExp stretchPrec
      capLimit coreLenProc lastInit lastMul lastSpace : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {opCore opLast : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ}
    {ℓ' g' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ}
    {ch : ChainState cfg.T cfg.P} {curG : MGraph} {curU : List Update}
    {curEditsList : List OrdEdit} {curEnc : ℕ} {oldOrd : ℕ → List End} {sE st : State}
    {tok : ℕ → Rcore.τ} {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists} {levelSpace levelCost : ℕ → ℕ}
    (E : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore
      p opCore)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hOldLo : A.selBase + 1 + 12 * cfg.P.d ≤ oldPtrs)
    (hOldNew : oldPtrs + (cfg.P.d + 1) ≤ newPtrs)
    (hNewHi : newPtrs + (cfg.P.d + 1) ≤ A.heapFloor)
    (hN0 : N0 = cfg.N₀) (hLvlM : ∀ j < cfg.P.d, ch0.lvlM j = levelM cfg.TP cfg.P j)
    (hN00 : ch0.N₀ = N0) (hPos : 0 < i₀) (hLt : i₀ < cfg.P.d)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
      EWc ULc ch0 termTok i₀ ch curG curU curEditsList oldOrd sE tok curBatch curBatchWords
      curEdits curEditsWords levelU levelUS D)
    (hM : UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen
      ℓ' g' (cfg.P.d - i₀) i₀ ch curG curU curEnc oldOrd)
    (hFire : intRebuildThreshold cfg.P N0 i₀ < ch.updCount i₀ + curU.length)
    (hstMem : st.mem = sE.mem)
    (hstRegs : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 99 → st.regs r = sE.regs r)
    (h71 : sE.regs 71 = 0) (h80 : sE.regs 80 = oldPtrs) (h81 : sE.regs 81 = newPtrs)
    (hIn0 : ∀ j, i₀ ≤ j → j < cfg.P.d →
      SparseCoreOrdInput cfg.T cfg.P.k (ch0.lvlM j) ch0.N₀ (ch0.scState j) (ch0.G j)
        (ch0.levelOrd j) (ch0.updCount j))
    (next : ChainState cfg.T cfg.P)
    (hNext : next = (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
      { ch with ℓ := ℓ', g := g' } i₀ curG curEnc).1)
    (hWordExpEq : Psc.wordExp = wordExp) (hInitOrdEq : ToolInitOrdEqOnE cfg.T)
    (hNextN : ∀ j ≤ cfg.P.d, (next.G j).n ≤ next.N₀)
    (hNextRot : ∀ j < cfg.P.d, ordRotWords (chainLevelOrdAbs next j) (next.bran j) ≤
      1 + 2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m)
    (hImpl : ∀ j, i₀ ≤ j → j < cfg.P.d →
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth cfg.T (next.G j) cfg.P.k (next.lvlM j)
          next.N₀ vCap eCap capExp Psc alloc) ∧
      SparseCoreReadoutFootAt fmt L depth cfg.T (next.G j) cfg.P.k (next.lvlM j) next.N₀ vCap
        eCap capExp Psc alloc Rcore p opCore)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hLastImpl :
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
        (next.G cfg.P.d).E).Implements w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L (next.G cfg.P.d) vCap eCap lastMul
          stretchPrec lastAlloc))
    (hLevelSpaceDom : ∀ j gB lB grB oB h, i₀ ≤ j → j < cfg.P.d →
      ordLevelSpace L capExp capLimit
        (alloc 6 [gB, lB, grB, oB, cfg.P.k, next.lvlM j, next.N₀, L, fmt.precision, depth, h])
        (next.lvlM j) next.N₀ (next.G (j + 1)).m ≤ levelSpace j)
    (hLevelCostDom : ∀ j, i₀ ≤ j → j < cfg.P.d →
      updateCoreRebuildLevelCost L capExp cfg Psc next j ≤ levelCost j)
    (hLastSpaceDom : ∀ gB lB h, lastAlloc 1 [gB, lB, L, fmt.precision, h] ≤ lastSpace)
    (hFCap : ∀ j, i₀ ≤ j → j < cfg.P.d →
      ∀ e ∈ (cfg.T.lsfs (next.scState j) (next.bran j)).F.F.E, e < intCap)
    (hLastFCap : ∀ e ∈ (next.lastLSFs next.lastBran).F.F.E, e < intCap)
    (hLWord : L < 2 ^ w) (hPWord : P < 2 ^ w) (hWidth : P ≤ 4 * L) (hDepthW : depth < 2 ^ w)
    (hNW : N0 < 2 ^ w)
    (hRoom : sE.regs 4 + 10 * (cfg.P.d - i₀) +
      (1 + ordRotWords (chainLevelOrdAbs ch (i₀ - 1)) (ch.bran (i₀ - 1))) +
      (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace + 7 < 2 ^ w) :
    ∃ (out : State) (cost : ℕ),
      Runs w p ω (wireBranchBIntKFBL dgApply initCore (opCore 3) (opCore 2) coreLenProc
        (opCore 5) lastInit) st .normal out cost ∧
      BranchBRebuiltOrdKFBL A.levelMeta cfg.P.d (i₀ + 1) (sE.regs 4) vCap eCap L out.mem ∧
      BranchBRebuiltOrdKFBL A.levelMeta cfg.P.d (i₀ + 1) A.selBase vCap eCap L out.mem := by
  obtain ⟨hFloor, _, _, _, _, hr72, _, _, hr75, _, hr77, hr78, _, hr83, hr85, _, _, _, hr96,
    _, _, _⟩ := I.regs
  have hN : ch.N₀ = N0 := I.modelFrame.2.2.2.2.2.1
  have hLvlCh : ∀ j < cfg.P.d, ch.lvlM j = levelM cfg.TP cfg.P j := fun j hj => by
    rw [I.modelFrame.2.2.2.2.2.2.1]; exact hLvlM j hj
  obtain ⟨rem, hrem⟩ : ∃ rem, cfg.P.d - i₀ = rem + 1 := ⟨cfg.P.d - i₀ - 1, by omega⟩
  rw [hrem] at hM
  obtain ⟨_, hValid, hCaps, hCurG, _, hIf⟩ := hM
  have hFire' : intRebuildThreshold cfg.P ch.N₀ i₀ < ch.updCount i₀ + curU.length := by
    rw [hN]; exact hFire
  simp only [hFire', ↓reduceIte] at hIf
  obtain ⟨hReb, hInPrev0⟩ := hIf
  have hi0 : i₀ ≠ 0 := by omega
  rw [rebuildStartGraph_pos hi0, rebuildStartFn_pos hi0, rebuildStartFn_pos hi0] at hReb
  have hInPrev := hInPrev0 hPos
  clear hi0 hrem hInPrev0
  obtain ⟨_, _, _, _, _, _, hRebW, _, _, _, _, _, _⟩ :=
    branchBIntNext_facts (fmt := fmt) (Psc := Psc) ch curG ℓ' g' curEnc i₀ next hNext hPos hLt
      hReb hWordExpEq E.prec hInitOrdEq hNextN hNextRot
  have hHBLt := S.hbLt
  have hBBLt := S.bbLt
  have hMetaLt := S.metaLt
  have hUCLt := S.ucLt
  have hRCLt := S.rcLt
  have hGLt : A.gPtr0 i₀ + dynGraphSize vCap eCap ≤ A.selBase := S.gLt i₀ hLt
  have hm1 : i₀ - 1 < cfg.P.d := by omega
  have hGLt1 : A.gPtr0 (i₀ - 1) + dynGraphSize vCap eCap ≤ A.selBase := S.gLt (i₀ - 1) hm1
  have hSlotLe : A.selBase + 1 + 12 * cfg.P.d ≤ A.heapFloor := by omega
  have hFootLoc := I.footLoc
  -- Part 1
  obtain ⟨s, c1, tokM, ordPtr, ordWords, r1, h1hi, M, _⟩ :=
    wireBranchBIntOldKFBL_runs (ω := ω) (st := st) E S hOldLo (by omega) hN0 hLvlM hN00 hPos
      hLt I hstMem hstRegs h71 h80 hIn0 hValid hCaps hCurG hRebW hInPrev (by omega)
  -- Part 2 (standard + `_ord`)
  obtain ⟨s3, c2, _, _, r2, h3hi, B, _⟩ :=
    wireBranchBIntRebNewKFBL_runs (ω := ω) E S hOldLo (by omega) (by omega) hNewHi hPos hLt I M
      h71 h81 next hNext hReb hWordExpEq hInitOrdEq hNextN hNextRot hImpl hcapLim hCoreLenProc
      hLastImpl hLevelSpaceDom hLevelCostDom hLastSpaceDom hFCap hLastFCap hLWord hPWord hWidth
      hDepthW hNW (by omega)
  obtain ⟨s3', _, r2', hOrd3'⟩ :=
    wireBranchBIntRebNewKFBL_runs_ord (ω := ω) E S hOldLo (by omega) (by omega) hNewHi hPos hLt I M
      h71 h81 next hNext hReb hWordExpEq hInitOrdEq hNextN hNextRot hImpl hcapLim hCoreLenProc
      hLastImpl hLevelSpaceDom hLevelCostDom hLastSpaceDom hFCap hLastFCap hLWord hPWord hWidth
      hDepthW hNW (by omega)
  have hs3Eq : s3' = s3 := (Runs.det r2' r2).2.1
  have hOrd3 : BranchBRebuiltOrdKFBL A.levelMeta cfg.P.d (i₀ + 1) (s.regs 4) vCap eCap L s3.mem :=
    hs3Eq ▸ hOrd3'
  have hsE4 : sE.regs 4 < s.regs 4 := by have := M.heapLo; have := M.ord.2.2.1; omega
  have hs3 : s.regs 4 ≤ s3.regs 4 := B.heapLo
  have hRoom3 : s3.regs 4 + 7 < 2 ^ w := by omega
  clear hRoom h1hi h3hi
  have hR3 (r : ℕ) (h70 : 70 ≤ r) (h99 : r ≠ 99) : s3.regs r = sE.regs r :=
    (B.regs r h70).trans (M.regs r h70 h99)
  have hTokM1 : ∀ a, Rcore.foot (A.coreH (i₀ - 1)) (tokM (i₀ - 1)) a →
      Rcore.foot (A.coreH (i₀ - 1)) (tok (i₀ - 1)) a ∨ (sE.regs 4 ≤ a ∧ a < s.regs 4) :=
    (M.reps (i₀ - 1) hm1).2
  have hKeep3 : ∀ a < sE.regs 4,
      (∀ j, i₀ ≤ j + 1 → j < cfg.P.d → ¬ Rcore.foot (A.coreH j) (tok j) a) →
      (a < A.gPtr0 i₀ ∨ A.gPtr0 i₀ + dynGraphSize vCap eCap ≤ a) →
      BranchBIntKeepCell cfg.P.d i₀ A a →
      (a < oldPtrs + i₀ ∨ oldPtrs + cfg.P.d ≤ a) →
      (a < newPtrs + i₀ ∨ newPtrs + (cfg.P.d + 1) ≤ a) → s3.mem a = sE.mem a :=
    fun a ha hc hg hk ho hn =>
      (B.frame a (by omega) hk.2.1 hk.2.2.1 hk.2.2.2 hn).trans (M.frame a ha hc hg hk.1 ho)
  have hK3S : ∀ x, BranchBStaticWord cfg.P.d A x → BranchBIntKeepCell cfg.P.d i₀ A x →
      s3.mem x = sE.mem x := fun x hx hk => by
    obtain ⟨hxs, hxf, hxg, _⟩ := branchBStaticWord_off S I.static hx
    exact hKeep3 x (by omega) (fun j _ hj => hxf j hj) (hxg i₀ hLt).1 hk (Or.inl (by omega))
      (Or.inl (by omega))
  have h3HB : ∀ j < i₀, s3.mem (A.handleBase + j) = sE.mem (A.handleBase + j) := fun j hj =>
    hK3S _ (.hb (by omega) (by omega)) (.hb S hj hLt)
  have h3BB : ∀ j < i₀, s3.mem (A.branchBase + j) = sE.mem (A.branchBase + j) := fun j hj =>
    hK3S _ (.bb (by omega) (by omega)) (.bb S hj hLt)
  have h3LMd : ∀ j ≤ i₀, s3.mem (A.levelMeta + cfg.P.d + j) =
      sE.mem (A.levelMeta + cfg.P.d + j) := fun j hj =>
    hK3S _ (.lm (by omega) (by omega)) (.lmd S hj hLt)
  have hLoc1 := E.loc (A.coreH (i₀ - 1)) (chainLevelOrdAbs ch (i₀ - 1)) (tokM (i₀ - 1)) s.mem
    s3.mem (fun a ha => by
      rcases hTokM1 a ha with h0 | ⟨_, h2⟩
      · have hlt := (I.reps (i₀ - 1) hm1).2 a h0
        obtain ⟨f1, f2, f3, _, f5, _⟩ := branchBCoresDisjStatic_footSep I.static hm1 h0
        have hk : BranchBIntKeepCell cfg.P.d i₀ A a := .of_sep f1 f2 f3 f5 hLt
        refine (B.frame a (by omega) hk.2.1 hk.2.2.1 hk.2.2.2 ?_).symm
        rcases hFootLoc (i₀ - 1) hm1 a h0 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      · exact (B.frame a h2 (Or.inr (by omega)) (Or.inr (by omega))
          ⟨Or.inr (by omega), Or.inr (by omega)⟩ (Or.inr (by omega))).symm)
  have hRep1 : Rcore.rep (A.coreH (i₀ - 1)) (chainLevelOrdAbs ch (i₀ - 1)) (tokM (i₀ - 1))
      s3.mem := by
    have h := (M.reps (i₀ - 1) hm1).1
    simp only [show ¬ i₀ ≤ i₀ - 1 by omega, ↓reduceIte] at h
    exact hLoc1.1 h
  obtain ⟨_, _, c3t, c4t, c5t, c6t, c7t, _, _, _⟩ := I.cells (i₀ - 1) hm1
  have hG1 : DynGraphAt s3.mem (A.gPtr0 (i₀ - 1)) vCap eCap (ch.G (i₀ - 1)) :=
    dynGraphAt_of_agree (I.graphs (i₀ - 1) hm1) (fun x hx1 hx2 => by
      obtain ⟨_, _, g3, g4, _, g6, g7, _, g9⟩ := S.gSep (i₀ - 1) hm1 x hx1 hx2
      exact hKeep3 x (by omega)
        (fun j _ hj => (I.static j hj).2.2.2.2.1 (i₀ - 1) hm1 x hx1 hx2)
        ((g9 i₀ hLt).2 (by omega)) (.of_sep g3 g4 g6 (g7.imp_right Nat.le_of_lt) hLt)
        (Or.inl (by omega)) (Or.inl (by omega)))
  have hInT : SparseCoreOrdInput cfg.T cfg.P.k (levelM cfg.TP cfg.P (i₀ - 1)) cfg.N₀
      (ch.scState (i₀ - 1)) (ch.G (i₀ - 1)) (ch.levelOrd (i₀ - 1)) (ch.updCount (i₀ - 1)) := by
    rw [← hLvlCh (i₀ - 1) hm1, ← hN0, ← hN]; exact hInPrev
  -- Part 3
  obtain ⟨out, c3, _, _, r3, _, _, _, _, _, _, _, _, _, _, hFrT, _, _, _, _, _, _⟩ :=
    wireBranchBIntTailKFBL_runs (tool := cfg.T) (ω := ω) (st := s3) (d := cfg.P.d) (idx := i₀)
      (selBase := A.selBase) (ucBase := A.ucBase) (cur := s3.regs 4)
      (handleBase := A.handleBase) (branchBase := A.branchBase) (levelMeta := A.levelMeta)
      (handle := A.coreH (i₀ - 1)) (branch := ch.bran (i₀ - 1)) (graph := A.gPtr0 (i₀ - 1))
      (a := ⟨ch.scState (i₀ - 1), ch.G (i₀ - 1), ch.levelOrd (i₀ - 1), ch.updCount (i₀ - 1)⟩)
      (x := tokM (i₀ - 1)) E.loc (E.footAt (i₀ - 1) hm1)
      ⟨rfl, (hR3 72 (by omega) (by omega)).trans hr72,
        (hR3 75 (by omega) (by omega)).trans hr75, (hR3 77 (by omega) (by omega)).trans hr77,
        (hR3 78 (by omega) (by omega)).trans hr78, (hR3 83 (by omega) (by omega)).trans hr83,
        (hR3 85 (by omega) (by omega)).trans hr85, (hR3 96 (by omega) (by omega)).trans hr96⟩
      hLt.le (by omega)
      ⟨(h3HB (i₀ - 1) (by omega)).trans c3t, (h3BB (i₀ - 1) (by omega)).trans c4t,
        (h3LMd (i₀ - 1) (by omega)).trans c7t⟩
      ⟨by omega, by omega, by omega⟩ c5t E.kW c6t hG1 (by omega) hRep1 hInT
      (fun z hz => by
        rcases hTokM1 z hz with h | h
        · have := (I.reps (i₀ - 1) hm1).2 z h; omega
        · omega)
      B.zero (by omega) (by omega)
      ⟨fun hf => by
        rcases hTokM1 _ hf with h | h
        · rcases hFootLoc (i₀ - 1) hm1 _ h with h' | h' <;> omega
        · omega,
       fun hf => by
        rcases hTokM1 _ hf with h | h
        · rcases hFootLoc (i₀ - 1) hm1 _ h with h' | h' <;> omega
        · omega⟩
      (fun z hz => by
        rcases hz with ⟨hz1, hz2⟩ | hz
        · obtain ⟨n1, n2, n3⟩ := branchBStatic_uc_ne S (z := z) (by omega) hz2 hm1
          refine ⟨by omega, fun hf => ?_, ?_, n1, n2, n3, by omega, by omega⟩
          · rcases hTokM1 z hf with h | h
            · obtain ⟨_, _, _, f4, _, _⟩ := branchBCoresDisjStatic_footSep I.static hm1 h
              rcases f4 with f4 | f4 <;> omega
            · omega
          · by_contra hc
            simp only [not_or, not_lt, not_le] at hc
            obtain ⟨_, _, _, _, _, _, _, g8, _⟩ := S.gSep (i₀ - 1) hm1 z hc.1 hc.2
            rcases g8 with g8 | g8 <;> omega
        · subst hz
          refine ⟨by omega, fun hf => ?_, Or.inr (by omega), by omega, by omega, by omega,
            by omega, by omega⟩
          rcases hTokM1 _ hf with h | h
          · rcases hFootLoc (i₀ - 1) hm1 _ h with h' | h' <;> omega
          · omega)
      (Or.inr (by omega))
  have hKeepMeta : ∀ j < 2 * cfg.P.d, out.mem (A.levelMeta + j) = s3.mem (A.levelMeta + j) := by
    intro j hj
    obtain ⟨hxs, hxf, _, hxu⟩ :=
      branchBStaticWord_off S I.static
        (BranchBStaticWord.lm (x := A.levelMeta + j) (by omega) (by omega))
    refine hFrT (A.levelMeta + j) (by omega) (fun hf => ?_) ?_ (by omega) (by omega) (by omega)
    · rcases hTokM1 _ hf with h | h
      · exact hxf (i₀ - 1) hm1 h
      · omega
    · by_contra hc
      simp only [not_or, not_lt, not_le] at hc
      exact hxu (A.levelMeta + j - A.ucBase) (by omega) (by omega)
  have hRuns : Runs w p ω (wireBranchBIntKFBL dgApply initCore (opCore 3) (opCore 2) coreLenProc
      (opCore 5) lastInit) st .normal out (c1 + (c2 + c3 + 1) + 1) := by
    unfold wireBranchBIntKFBL
    exact runs_seq_iff.mpr (Or.inr ⟨s, c1, c2 + c3 + 1, r1,
      runs_seq_iff.mpr (Or.inr ⟨s3, c2, c3, r2, r3, rfl⟩), rfl⟩)
  exact ⟨out, _, hRuns,
    hOrd3.of_agree_le (le_of_lt hsE4) hKeepMeta,
    hOrd3.of_agree_le (by omega) hKeepMeta⟩

/-- **Rebuilt-block order for every run of `wireBranchBIntKFBL`.** By `Runs.det`, any run of the
interior step from the loop-exit state satisfies `BranchBRebuiltOrdKFBL A.levelMeta cfg.P.d
(i₀ + 1)` at both `sE.regs 4` and `A.selBase`. -/
theorem wireBranchBIntKFBL_exit_rebuiltOrd
    {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy N0 oldPtrs newPtrs intCap i₀ wordExp stretchPrec
      capLimit coreLenProc lastInit lastMul lastSpace cost : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {opCore opLast : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ}
    {ℓ' g' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ}
    {ch : ChainState cfg.T cfg.P} {curG : MGraph} {curU : List Update}
    {curEditsList : List OrdEdit} {curEnc : ℕ} {oldOrd : ℕ → List End} {sE st out : State}
    {tok : ℕ → Rcore.τ} {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists} {levelSpace levelCost : ℕ → ℕ}
    (E : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore
      p opCore)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hOldLo : A.selBase + 1 + 12 * cfg.P.d ≤ oldPtrs)
    (hOldNew : oldPtrs + (cfg.P.d + 1) ≤ newPtrs)
    (hNewHi : newPtrs + (cfg.P.d + 1) ≤ A.heapFloor)
    (hN0 : N0 = cfg.N₀) (hLvlM : ∀ j < cfg.P.d, ch0.lvlM j = levelM cfg.TP cfg.P j)
    (hN00 : ch0.N₀ = N0) (hPos : 0 < i₀) (hLt : i₀ < cfg.P.d)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
      EWc ULc ch0 termTok i₀ ch curG curU curEditsList oldOrd sE tok curBatch curBatchWords
      curEdits curEditsWords levelU levelUS D)
    (hM : UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen
      ℓ' g' (cfg.P.d - i₀) i₀ ch curG curU curEnc oldOrd)
    (hFire : intRebuildThreshold cfg.P N0 i₀ < ch.updCount i₀ + curU.length)
    (hstMem : st.mem = sE.mem)
    (hstRegs : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 99 → st.regs r = sE.regs r)
    (h71 : sE.regs 71 = 0) (h80 : sE.regs 80 = oldPtrs) (h81 : sE.regs 81 = newPtrs)
    (hIn0 : ∀ j, i₀ ≤ j → j < cfg.P.d →
      SparseCoreOrdInput cfg.T cfg.P.k (ch0.lvlM j) ch0.N₀ (ch0.scState j) (ch0.G j)
        (ch0.levelOrd j) (ch0.updCount j))
    (next : ChainState cfg.T cfg.P)
    (hNext : next = (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
      { ch with ℓ := ℓ', g := g' } i₀ curG curEnc).1)
    (hWordExpEq : Psc.wordExp = wordExp) (hInitOrdEq : ToolInitOrdEqOnE cfg.T)
    (hNextN : ∀ j ≤ cfg.P.d, (next.G j).n ≤ next.N₀)
    (hNextRot : ∀ j < cfg.P.d, ordRotWords (chainLevelOrdAbs next j) (next.bran j) ≤
      1 + 2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m)
    (hImpl : ∀ j, i₀ ≤ j → j < cfg.P.d →
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth cfg.T (next.G j) cfg.P.k (next.lvlM j)
          next.N₀ vCap eCap capExp Psc alloc) ∧
      SparseCoreReadoutFootAt fmt L depth cfg.T (next.G j) cfg.P.k (next.lvlM j) next.N₀ vCap
        eCap capExp Psc alloc Rcore p opCore)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hLastImpl :
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
        (next.G cfg.P.d).E).Implements w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L (next.G cfg.P.d) vCap eCap lastMul
          stretchPrec lastAlloc))
    (hLevelSpaceDom : ∀ j gB lB grB oB h, i₀ ≤ j → j < cfg.P.d →
      ordLevelSpace L capExp capLimit
        (alloc 6 [gB, lB, grB, oB, cfg.P.k, next.lvlM j, next.N₀, L, fmt.precision, depth, h])
        (next.lvlM j) next.N₀ (next.G (j + 1)).m ≤ levelSpace j)
    (hLevelCostDom : ∀ j, i₀ ≤ j → j < cfg.P.d →
      updateCoreRebuildLevelCost L capExp cfg Psc next j ≤ levelCost j)
    (hLastSpaceDom : ∀ gB lB h, lastAlloc 1 [gB, lB, L, fmt.precision, h] ≤ lastSpace)
    (hFCap : ∀ j, i₀ ≤ j → j < cfg.P.d →
      ∀ e ∈ (cfg.T.lsfs (next.scState j) (next.bran j)).F.F.E, e < intCap)
    (hLastFCap : ∀ e ∈ (next.lastLSFs next.lastBran).F.F.E, e < intCap)
    (hLWord : L < 2 ^ w) (hPWord : P < 2 ^ w) (hWidth : P ≤ 4 * L) (hDepthW : depth < 2 ^ w)
    (hNW : N0 < 2 ^ w)
    (hRoom : sE.regs 4 + 10 * (cfg.P.d - i₀) +
      (1 + ordRotWords (chainLevelOrdAbs ch (i₀ - 1)) (ch.bran (i₀ - 1))) +
      (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace + 7 < 2 ^ w)
    (hRun : Runs w p ω (wireBranchBIntKFBL dgApply initCore (opCore 3) (opCore 2) coreLenProc
      (opCore 5) lastInit) st .normal out cost) :
    BranchBRebuiltOrdKFBL A.levelMeta cfg.P.d (i₀ + 1) (sE.regs 4) vCap eCap L out.mem ∧
    BranchBRebuiltOrdKFBL A.levelMeta cfg.P.d (i₀ + 1) A.selBase vCap eCap L out.mem := by
  obtain ⟨out₁, _, hRun₁, hOrdE, hOrdSel⟩ :=
    wireBranchBIntKFBL_runs_exit_ord E S hOldLo hOldNew hNewHi hN0 hLvlM hN00 hPos hLt I hM
      hFire hstMem hstRegs h71 h80 h81 hIn0 next hNext hWordExpEq
      hInitOrdEq hNextN hNextRot hImpl hcapLim hCoreLenProc hLastImpl hLevelSpaceDom hLevelCostDom
      hLastSpaceDom hFCap hLastFCap hLWord hPWord hWidth hDepthW hNW hRoom
  have hEq : out₁ = out := (Runs.det hRun₁ hRun).2.1
  subst hEq
  exact ⟨hOrdE, hOrdSel⟩

/-- **The meta-disjointness clause at the interior exit of Branch B.** Combining
`wireBranchBIntKFBL_exit_rebuiltOrd`,
`branchBIntExitLayGoalKFBL_proved` (which proves `metaKeep` for `j < i₀ + 1`), and
`branchB_metaDisj` instantiated at `fr := i₀ + 1` gives `SolverLevelMetaDisjAt vCap eCap tok'
out.mem` at the end of `wireBranchBIntKFBL`. -/
theorem wireBranchBIntKFBL_exit_metaDisj
    {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy N0 oldPtrs newPtrs intCap i₀ wordExp stretchPrec
      capLimit coreLenProc lastInit lastMul lastSpace cost : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {opCore opLast : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ}
    {ℓ' g' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ}
    {ch : ChainState cfg.T cfg.P} {curG : MGraph} {curU : List Update}
    {curEditsList : List OrdEdit} {curEnc : ℕ} {oldOrd : ℕ → List End} {sE st out : State}
    {tok : ℕ → Rcore.τ} {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists} {levelSpace levelCost : ℕ → ℕ}
    {tok0 tok' : SolverToken cfg L Rcore} {mem0 : ℕ → ℕ}
    (hLM : A.levelMeta = solverLevelMetaAddr tok0.table cfg.P.d)
    (hG0Eq : ∀ j < cfg.P.d, A.gPtr0 j = mem0 (solverLevelMetaAddr tok0.table cfg.P.d + cfg.P.d + j))
    (hL0Eq : ∀ j < cfg.P.d, A.lPtr0 j = mem0 (solverLevelMetaAddr tok0.table cfg.P.d + j))
    (hOld : SolverLevelMetaDisjAt vCap eCap tok0 mem0)
    (htab : tok'.table = tok0.table)
    (E : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore
      p opCore)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hOldLo : A.selBase + 1 + 12 * cfg.P.d ≤ oldPtrs)
    (hOldNew : oldPtrs + (cfg.P.d + 1) ≤ newPtrs)
    (hNewHi : newPtrs + (cfg.P.d + 1) ≤ A.heapFloor)
    (hN0 : N0 = cfg.N₀) (hLvlM : ∀ j < cfg.P.d, ch0.lvlM j = levelM cfg.TP cfg.P j)
    (hN00 : ch0.N₀ = N0) (hPos : 0 < i₀) (hLt : i₀ < cfg.P.d)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
      EWc ULc ch0 termTok i₀ ch curG curU curEditsList oldOrd sE tok curBatch curBatchWords
      curEdits curEditsWords levelU levelUS D)
    (hM : UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen
      ℓ' g' (cfg.P.d - i₀) i₀ ch curG curU curEnc oldOrd)
    (hFire : intRebuildThreshold cfg.P N0 i₀ < ch.updCount i₀ + curU.length)
    (hstMem : st.mem = sE.mem)
    (hstRegs : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 99 → st.regs r = sE.regs r)
    (h71 : sE.regs 71 = 0) (h80 : sE.regs 80 = oldPtrs) (h81 : sE.regs 81 = newPtrs)
    (hIn0 : ∀ j, i₀ ≤ j → j < cfg.P.d →
      SparseCoreOrdInput cfg.T cfg.P.k (ch0.lvlM j) ch0.N₀ (ch0.scState j) (ch0.G j)
        (ch0.levelOrd j) (ch0.updCount j))
    (hOldLast : ∃ vc ec, DynGraphAt sE.mem (sE.mem (oldPtrs + cfg.P.d)) vc ec
        (ch0.lastLSFs ch0.lastBran).F.F ∧
      ∀ a, sE.mem (oldPtrs + cfg.P.d) ≤ a →
        a < sE.mem (oldPtrs + cfg.P.d) + dynGraphSize vc ec → RL.foot (A.coreH cfg.P.d) termTok a)
    (hOldFCap : ∀ j, i₀ ≤ j → j < cfg.P.d →
      ∀ e ∈ (cfg.T.lsfs (ch0.scState j) (ch0.bran j)).F.F.E, e < intCap)
    (hOldLastFCap : ∀ e ∈ (ch0.lastLSFs ch0.lastBran).F.F.E, e < intCap)
    (next : ChainState cfg.T cfg.P)
    (hNext : next = (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
      { ch with ℓ := ℓ', g := g' } i₀ curG curEnc).1)
    (hWordExpEq : Psc.wordExp = wordExp) (hInitOrdEq : ToolInitOrdEqOnE cfg.T)
    (hNextN : ∀ j ≤ cfg.P.d, (next.G j).n ≤ next.N₀)
    (hNextRot : ∀ j < cfg.P.d, ordRotWords (chainLevelOrdAbs next j) (next.bran j) ≤
      1 + 2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m)
    (hImpl : ∀ j, i₀ ≤ j → j < cfg.P.d →
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth cfg.T (next.G j) cfg.P.k (next.lvlM j)
          next.N₀ vCap eCap capExp Psc alloc) ∧
      SparseCoreReadoutFootAt fmt L depth cfg.T (next.G j) cfg.P.k (next.lvlM j) next.N₀ vCap
        eCap capExp Psc alloc Rcore p opCore)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hLastImpl :
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
        (next.G cfg.P.d).E).Implements w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L (next.G cfg.P.d) vCap eCap lastMul
          stretchPrec lastAlloc))
    (hLevelSpaceDom : ∀ j gB lB grB oB h, i₀ ≤ j → j < cfg.P.d →
      ordLevelSpace L capExp capLimit
        (alloc 6 [gB, lB, grB, oB, cfg.P.k, next.lvlM j, next.N₀, L, fmt.precision, depth, h])
        (next.lvlM j) next.N₀ (next.G (j + 1)).m ≤ levelSpace j)
    (hLevelCostDom : ∀ j, i₀ ≤ j → j < cfg.P.d →
      updateCoreRebuildLevelCost L capExp cfg Psc next j ≤ levelCost j)
    (hLastSpaceDom : ∀ gB lB h, lastAlloc 1 [gB, lB, L, fmt.precision, h] ≤ lastSpace)
    (hFCap : ∀ j, i₀ ≤ j → j < cfg.P.d →
      ∀ e ∈ (cfg.T.lsfs (next.scState j) (next.bran j)).F.F.E, e < intCap)
    (hLastFCap : ∀ e ∈ (next.lastLSFs next.lastBran).F.F.E, e < intCap)
    (hLWord : L < 2 ^ w) (hPWord : P < 2 ^ w) (hWidth : P ≤ 4 * L) (hDepthW : depth < 2 ^ w)
    (hNW : N0 < 2 ^ w)
    (hRoom : sE.regs 4 + 10 * (cfg.P.d - i₀) +
      (1 + ordRotWords (chainLevelOrdAbs ch (i₀ - 1)) (ch.bran (i₀ - 1))) +
      (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace + 7 < 2 ^ w)
    (hRun : Runs w p ω (wireBranchBIntKFBL dgApply initCore (opCore 3) (opCore 2) coreLenProc
      (opCore 5) lastInit) st .normal out cost) :
    SolverLevelMetaDisjAt vCap eCap tok' out.mem := by
  obtain ⟨_, hOrdSel⟩ :=
    wireBranchBIntKFBL_exit_rebuiltOrd E S hOldLo hOldNew hNewHi hN0 hLvlM hN00 hPos hLt I hM
      hFire hstMem hstRegs h71 h80 h81 hIn0 next hNext hWordExpEq
      hInitOrdEq hNextN hNextRot hImpl hcapLim hCoreLenProc hLastImpl hLevelSpaceDom hLevelCostDom
      hLastSpaceDom hFCap hLastFCap hLWord hPWord hWidth hDepthW hNW hRoom hRun
  obtain ⟨out₂, _, _, _, hRun₂, _, _, _, _, hLay⟩ :=
    branchBIntExitLayGoalKFBL_proved E S hOldLo hOldNew hNewHi hN0 hLvlM hN00 hPos hLt I hM
      hFire hstMem hstRegs h71 h80 h81 hIn0 hOldLast hOldFCap hOldLastFCap next hNext hWordExpEq
      hInitOrdEq hNextN hNextRot hImpl hcapLim hCoreLenProc hLastImpl hLevelSpaceDom hLevelCostDom
      hLastSpaceDom hFCap hLastFCap hLWord hPWord hWidth hDepthW hNW hRoom
  have hEq : out₂ = out := (Runs.det hRun₂ hRun).2.1
  subst hEq
  refine solverLevelMetaDisjAt_of_kept_rebuilt (fr := i₀ + 1) (heap := A.selBase) hOld htab
    (fun j hj hjd => ?_) (fun j _ hjd => ?_) (hLM ▸ hOrdSel)
  · obtain ⟨hKL, hKG⟩ := hLay.metaKeep j (by omega)
    exact ⟨by rw [← hLM, hKL, (I.cells j hjd).2.2.2.2.2.2.2.1, hL0Eq j hjd, ← hLM],
           by rw [← hLM, hKG, (I.cells j hjd).2.2.2.2.2.2.1, hG0Eq j hjd, ← hLM]⟩
  · rw [← hL0Eq j hjd, ← hG0Eq j hjd]
    exact ⟨S.lLt j hjd, S.gLt j hjd⟩

end MinCostFlow.MinRatio
