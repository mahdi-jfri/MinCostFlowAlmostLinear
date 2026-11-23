module

public import MinCostFlow.MinRatio.WireChainCoreBranchBExitLayGoalKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBForestLocKFBL

/-!
# The places of the forests of the exits of Branch B as propositions
(`WireChainCoreBranchBForestLocGoalKFBL`)

The suffix of Branch B needs the words of the graphs of the two forest lists in the set
`BranchBSuffixKeep` (`branchBSuffixKeep_of_forestLoc`), so it needs where the exits put these
graphs: `BranchBExitForestLocKFBL`. The exit interface `BranchBExitOutKFBL` does not say it. This
file states it as two propositions, with the premises of the two exit goals of
`WireChainCoreBranchBExitLayGoalKFBL`, for every run of the exit:
* `BranchBIntExitForestLocGoalKFBL`: the interior exit at `fr = i₀`;
* `BranchBTermExitForestLocGoalKFBL`: the terminal exit with a batch at `fr = d`.
The terminal exit with an empty batch lists no forests (`BranchBExitForestLocKFBL.of_nil`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- With no forests in the two lists, `BranchBExitForestLocKFBL` holds. -/
theorem BranchBExitForestLocKFBL.of_nil {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {RL : DSRep (ℕ × (ℕ → LSF))} {A : BranchBAddrs} {oldPtrs newPtrs fr : ℕ}
    {tok : ℕ → Rcore.τ} {termTok : RL.τ} {out : State} :
    BranchBExitForestLocKFBL A oldPtrs newPtrs fr [] [] tok termTok out :=
  ⟨fun t ht => absurd ht (by simp), fun t ht => absurd ht (by simp)⟩

/-- **The places of the forests of the interior exit.** With the premises of
`BranchBIntExitLayGoalKFBL`, every run of the interior exit ends in a state where the graphs of the
old forests (at `oldPtrs + i₀`) and of the new forests (at `newPtrs + i₀`) lie in the footprints of
the cores at the tokens `tok`, of the last level at `termTok`, or in the heap above the floor. -/
@[expose] def BranchBIntExitForestLocGoalKFBL : Prop :=
  ∀ {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
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
      (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace + 7 < 2 ^ w),
    ∀ (out : State) (cost : ℕ),
      Runs w p ω (wireBranchBIntKFBL dgApply initCore (opCore 3) (opCore 2) coreLenProc
        (opCore 5) lastInit) st .normal out cost →
      BranchBExitForestLocKFBL (RL := RL) A oldPtrs newPtrs i₀ (chainSuffixForests ch0 i₀)
        (chainSuffixForests next i₀) tok termTok out

/-- **The places of the forests of the terminal exit with a batch.** With the premises
of `BranchBTermExitLayGoalKFBL`, every run of the terminal exit ends in a state where the graphs of
the old and new last forests (at `oldPtrs + d` and `newPtrs + d`) lie in the footprints of the
cores at the tokens `tok`, of the last level at `termTok`, or in the heap above the floor. -/
@[expose] def BranchBTermExitForestLocGoalKFBL : Prop :=
  ∀ {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy wordExp stretchPrec N0 capLimit coreLenProc lastInit
      lastMul lastSpace nextM vcL ecL oldPtrs newPtrs intCap : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {E0 : Finset ℕ} {p : Program}
    {opCore opLast : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ}
    {ℓ' g' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : ℕ}
    {ch : ChainState cfg.T cfg.P} {curG : MGraph} {curU : List Update}
    {curEditsList : List OrdEdit} {curEnc : ℕ} {oldOrd : ℕ → List End} {sE st : State}
    {tok : ℕ → Rcore.τ} {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists}
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
    (hd : 0 < cfg.P.d)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt)
      (RL := LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P E0) reembFn A origLen ℓ' N0
      BWc EWc ULc ch0 termTok cfg.P.d ch curG curU curEditsList oldOrd sE tok curBatch
      curBatchWords curEdits curEditsWords levelU levelUS D)
    (hM : UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen
      ℓ' g' 0 cfg.P.d ch curG curU curEnc oldOrd)
    (hstMem : st.mem = sE.mem)
    (hstRegs : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 99 → st.regs r = sE.regs r)
    (hNonEmpty : curU ≠ [])
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hLastImpl : (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P curG.E).Implements w p
      lastInit opLast
      (lastLevelRuntimeMachineContract fmt L cfg.L curG vCap eCap lastMul stretchPrec lastAlloc))
    (hLastSp : ∀ g l h, lastAlloc 1 [g, l, L, fmt.precision, h] ≤ lastSpace)
    (hLWord : L < 2 ^ w) (hPWord : P < 2 ^ w) (hWidth : P ≤ 4 * L)
    (hHm : curG.m ≤ nextM)
    (hRotW : ordRotWords (chainLevelOrdAbs ch (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1)) ≤
      1 + 2 * cfg.N₀ + 2 * nextM)
    (hRoom : sE.regs 4 + (1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
      nextM * wireCoreLenEdgeSpace
        (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) +
      (2 + 2 * cfg.N₀ + 2 * nextM)) + lastSpace + 7 < 2 ^ w)
    (h71 : sE.regs 71 = 0) (h81 : sE.regs 81 = newPtrs)
    (hOldLast : ∃ vc ec, DynGraphAt sE.mem (sE.mem (oldPtrs + cfg.P.d)) vc ec
        (ch0.lastLSFs ch0.lastBran).F.F ∧
      ∀ a, sE.mem (oldPtrs + cfg.P.d) ≤ a →
        a < sE.mem (oldPtrs + cfg.P.d) + dynGraphSize vc ec →
        (LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P E0).foot (A.coreH cfg.P.d)
          termTok a)
    (hOldLastFCap : ∀ e ∈ (ch0.lastLSFs ch0.lastBran).F.F.E, e < intCap),
    let X := (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P N0 ℓ' g' 0 cfg.P.d ch curG curU
      curEnc).1
    (0 < X.lastK) → (∀ e ∈ (X.lastLSFs X.lastBran).F.F.E, e < intCap) →
    ∀ (out : State) (cost : ℕ),
      Runs w p ω (wireBranchBTermKFBL (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
        collectTermForestStmt 81) st .normal out cost →
      BranchBExitForestLocKFBL
        (RL := LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P E0) A oldPtrs newPtrs
        cfg.P.d (chainSuffixForests ch0 cfg.P.d) (chainSuffixForests X cfg.P.d) tok termTok out

end MinCostFlow.MinRatio
