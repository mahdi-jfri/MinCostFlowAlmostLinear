module

public import MinCostFlow.MinRatio.WireChainCoreBranchBIntExitKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBTermOutKFBL

/-!
# The places of the words of the exits of Branch B (`WireChainCoreBranchBExitLayGoalKFBL`)

`BranchBExitOutKFBL` holds the facts after an exit of the loop of Branch B: those of
`BranchBExitBaseKFBL` and the places `BranchBExitLayKFBL` (the cut `hT`, the select data in the
zone, the new cores, the new last level and the new level blocks below `hT`, and the meta words
kept below `fr + 1`). The empty terminal exit gives all of it (`wireBranchBTermEmpty_exitOut`).
For the two other exits, this file states the places as propositions: each goal is the statement
of the run lemma of its exit with the places at the end state added.
* `BranchBIntExitLayGoalKFBL`: the interior exit (`wireBranchBIntKFBL_runs_exit`);
* `BranchBTermExitLayGoalKFBL`: the terminal exit with a batch (`wireBranchBTermNonEmpty_exitOut`).

`BranchBExitOutKFBL.of_int_lay` and `BranchBExitOutKFBL.of_base_lay` give `BranchBExitOutKFBL`
from the facts of the goals.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- **The places of the interior exit.** The statement of `wireBranchBIntKFBL_runs_exit`
(`WireChainCoreBranchBIntExitKFBL.lean`), with the places `BranchBExitLayKFBL` at the end state,
at `firstReb = i₀` and the rebuilt chain `next`. -/
@[expose] def BranchBIntExitLayGoalKFBL : Prop :=
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
    ∃ (out : State) (cost termTokN : ℕ) (tokN : ℕ → Rcore.τ),
      Runs w p ω (wireBranchBIntKFBL dgApply initCore (opCore 3) (opCore 2) coreLenProc
        (opCore 5) lastInit) st .normal out cost ∧
      out.regs 4 ≤ sE.regs 4 + 10 * (cfg.P.d - i₀) +
        (1 + ordRotWords (chainLevelOrdAbs ch (i₀ - 1)) (ch.bran (i₀ - 1))) +
        (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace + 7 ∧
      BranchBIntOutKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
        (capExp := capExp) A oldPtrs newPtrs intCap i₀ ch0 ch next levelU D sE out tok tokN
        termTokN ∧
      cost + (Finset.range cfg.P.d).sum
          (fun j => Rcore.phi (out.mem (A.handleBase + j)) (tokN j) out.mem) ≤
        2 * ((cfg.P.d - i₀) * (Psc.readout + 48)) + 670 * curBatchWords +
          Psc.mul * (ordRotWords (chainLevelOrdAbs ch (i₀ - 1)) (ch.bran (i₀ - 1)) + 1) *
            SparseCore.bundleLogFactor (levelM cfg.TP cfg.P (i₀ - 1)) cfg.N₀ +
          (Finset.Ico i₀ cfg.P.d).sum (fun j => levelCost j + 9) +
          lastMul * (cfg.L.cost (next.G cfg.P.d) + 1) + Psc.readout + 15 * (cfg.P.d - i₀) +
          413 + branchBPhiSum Rcore A tok sE.mem ∧
      ∃ hT : ℕ, BranchBExitLayKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
        (capExp := capExp) A vCap eCap i₀ ch0 ch next levelU D sE out tokN termTokN hT

/-- **The places of the terminal exit with a batch.** The statement of
`wireBranchBTermNonEmpty_exitOut` (`WireChainCoreBranchBTermOutKFBL.lean`), with the places
`BranchBExitLayKFBL` at the end state, at `firstReb = d`. -/
@[expose] def BranchBTermExitLayGoalKFBL : Prop :=
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
    ∃ (out : State) (cost h1 : ℕ) (y : Rcore.τ) (termTokN : ℕ),
      let tokN : ℕ → Rcore.τ := fun j => if j = cfg.P.d - 1 then y else tok j
      Runs w p ω (wireBranchBTermKFBL (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
        collectTermForestStmt 81) st .normal out cost ∧
      sE.regs 4 ≤ h1 ∧
      h1 ≤ sE.regs 4 + (1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
        nextM * wireCoreLenEdgeSpace
          (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) +
        (2 + 2 * cfg.N₀ + 2 * nextM)) + lastSpace ∧
      out.regs 4 = h1 + 7 ∧
      BranchBExitBaseKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
        (capExp := capExp) A vCap eCap oldPtrs newPtrs intCap cfg.P.d ch0 ch X levelU D sE out
        tok tokN termTokN ∧
      cost + branchBPhiSum Rcore A tokN out.mem +
          (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P curG.E).phi
            (out.mem (A.handleBase + cfg.P.d)) termTokN out.mem ≤
        3 * Psc.readout + copyGraphLiveCost curG.n curG.m +
          curG.m * (wireCoreLenEdgeCost
            (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) + 30) +
          Psc.mul * (ordRotWords (chainLevelOrdAbs ch (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1)) +
            1) * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀ +
          lastMul * (cfg.L.cost curG + 1) + 360 + 36 + branchBPhiSum Rcore A tok sE.mem ∧
      ∃ hT : ℕ, BranchBExitLayKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
        (capExp := capExp) A vCap eCap cfg.P.d ch0 ch X levelU D sE out tokN termTokN hT

/-- `BranchBExitOutKFBL` of the interior exit, from the facts `BranchBIntOutKFBL` and the places
of the goal `BranchBIntExitLayGoalKFBL`. -/
theorem BranchBExitOutKFBL.of_int_lay {w L P vCap eCap capExp : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {A : BranchBAddrs}
    {oldPtrs newPtrs intCap i₀ hT : ℕ} {ch0 ch next : ChainState cfg.T cfg.P}
    {levelU : ℕ → List Update} {D : ℕ → LevelDiffLists} {sE out : State}
    {tok tokN : ℕ → Rcore.τ} {termTokN : ℕ} (hi : i₀ < cfg.P.d)
    (O : BranchBIntOutKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
      (capExp := capExp) A oldPtrs newPtrs intCap i₀ ch0 ch next levelU D sE out tok tokN
      termTokN)
    (Y : BranchBExitLayKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
      (capExp := capExp) A vCap eCap i₀ ch0 ch next levelU D sE out tokN termTokN hT) :
    BranchBExitOutKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
      (capExp := capExp) A vCap eCap oldPtrs newPtrs intCap i₀ ch0 ch next levelU D sE out tok
      tokN termTokN hT :=
  { toBranchBExitBaseKFBL := BranchBExitBaseKFBL.of_int hi O, toBranchBExitLayKFBL := Y }

/-- `BranchBExitOutKFBL` from its two parts, as for the terminal exit with a batch. -/
theorem BranchBExitOutKFBL.of_base_lay {w L P vCap eCap capExp : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {A : BranchBAddrs}
    {vcL ecL oldPtrs newPtrs intCap fr hT : ℕ} {ch0 ch X : ChainState cfg.T cfg.P}
    {levelU : ℕ → List Update} {D : ℕ → LevelDiffLists} {sE out : State}
    {tok tokN : ℕ → Rcore.τ} {termTokN : ℕ}
    (O : BranchBExitBaseKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
      (capExp := capExp) A vcL ecL oldPtrs newPtrs intCap fr ch0 ch X levelU D sE out tok tokN
      termTokN)
    (Y : BranchBExitLayKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
      (capExp := capExp) A vcL ecL fr ch0 ch X levelU D sE out tokN termTokN hT) :
    BranchBExitOutKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
      (capExp := capExp) A vcL ecL oldPtrs newPtrs intCap fr ch0 ch X levelU D sE out tok tokN
      termTokN hT :=
  { toBranchBExitBaseKFBL := O, toBranchBExitLayKFBL := Y }

end MinCostFlow.MinRatio
