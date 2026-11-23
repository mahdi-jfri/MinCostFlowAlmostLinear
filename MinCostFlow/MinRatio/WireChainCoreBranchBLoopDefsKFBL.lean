module

public import MinCostFlow.MinRatio.WireChainCoreBranchBStepKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBDoneKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBLoopDefs
import WordRAM.Tactic

/-!
# The Branch B loop under `KFBL`: program and invariant (`WireChainCoreBranchBLoopDefsKFBL`)

Branch B walks the levels `idx = 0, 1, …` and runs a plain update step at each of them
(`wireBranchBStepKFBL`), until the batch of a level `idx < d` would pass its rebuild threshold, or
until `idx = d`. The loop of this file runs only the plain steps. When the threshold test fires at
level `idx`, the loop stores `idx` in the end register `reg 99` and so stops with `reg 96 = idx`.
The interior rebuild and the terminal step run after the loop.

* `wireBranchBLoopBodyKFBL`, `wireBranchBLoopKFBL`: the body and the loop.
* `BranchBAddrs`: the fixed addresses of the core that the loop reads.
* `UpdateLoopSizeInv`: caps on the words of the batches and the edit lists along the trace of
  `Chain.Ordered.updateLoop`, so that the heap used by every step is bounded in advance.
* `BranchBLoopInvKFBL`: the state of the machine at the top of the loop at level `idx`. Besides
  the register, model and memory facts of the loop, it holds the finished slots of the levels
  `j < idx`
  (`BranchBDoneSlots`) and the model facts on their lists.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- One pass of the loop at level `idx = reg 96`. It loads the batch length (`mem (reg 10)`), the
update counter and the rebuild threshold of the level. If the threshold test fires, it stores
`idx` in the end register `reg 99`. Otherwise it runs the plain step and moves to `idx + 1`. -/
@[expose] def wireBranchBLoopBodyKFBL (updCore readLSF dgApply copyProc updLen slotProc : ℕ) :
    Stmt :=
  .assign 16 (.load (.reg 10)) ;;
  .assign 17 (.load (.bin .add (.reg 85) (.reg 96))) ;;
  .assign 18 (.load (.bin .add (.reg 74) (.reg 96))) ;;
  .cond (.bin .lt (.reg 18) (.bin .add (.reg 17) (.reg 16)))
    (.assign 99 (.reg 96))
    (wireBranchBStepKFBL updCore readLSF dgApply copyProc updLen slotProc ;;
     .assign 96 (.bin .add (.reg 96) (.const 1)))

/-- The plain-step loop of Branch B: it runs while `reg 96 < reg 99`. -/
@[expose] def wireBranchBLoopKFBL (updCore readLSF dgApply copyProc updLen slotProc : ℕ) :
    Stmt :=
  .loop (.bin .lt (.reg 96) (.reg 99))
    (wireBranchBLoopBodyKFBL updCore readLSF dgApply copyProc updLen slotProc)

theorem wireBranchBLoopBodyKFBL_noRand (updCore readLSF dgApply copyProc updLen slotProc : ℕ) :
    (wireBranchBLoopBodyKFBL updCore readLSF dgApply copyProc updLen slotProc).NoRand := by
  simp [wireBranchBLoopBodyKFBL, wireBranchBStepKFBL_noRand, Stmt.NoRand]

theorem wireBranchBLoopKFBL_noRand (updCore readLSF dgApply copyProc updLen slotProc : ℕ) :
    (wireBranchBLoopKFBL updCore readLSF dgApply copyProc updLen slotProc).NoRand := by
  simp [wireBranchBLoopKFBL, wireBranchBLoopBodyKFBL_noRand, Stmt.NoRand]

/-- The fixed addresses that the loop of Branch B reads: the solver header `handle`, the
threshold table, the handle, branch, level-size, level-meta, rebuild-counter and
update-counter arrays, the select base `selBase` (the `1 + 12 d` words of the slots start there),
the first word `heapFloor` of the fresh heap of Branch B, and the graph, length and handle of
each level. -/
structure BranchBAddrs where
  handle : ℕ
  table : ℕ
  handleBase : ℕ
  branchBase : ℕ
  lvlMTable : ℕ
  levelMeta : ℕ
  rcBase : ℕ
  ucBase : ℕ
  selBase : ℕ
  heapFloor : ℕ
  gPtr0 : ℕ → ℕ
  lPtr0 : ℕ → ℕ
  coreH : ℕ → ℕ

/-- Caps on the sizes that a plain step reads, along the trace of `Chain.Ordered.updateLoop`:
at each plain level `idx`, the words of the forwarded batch are at most `BWc (idx + 1)`, the
edit words that op `0` may write are at most `EWc (idx + 1)` when the input words are at most
`BWc idx` and `EWc idx`, and the forwarded batch has at most `ULc (idx + 1)` updates. The state
after the step is the one of `UpdateLoopModelInv`. -/
@[expose] noncomputable def UpdateLoopSizeInv (cfg : Alg2Config) (ℓ' g' : ℕ → ℝ)
    (edMul : ℕ) (logf BWc EWc ULc : ℕ → ℕ) :
    (rem idx : ℕ) → ChainState cfg.T cfg.P → MGraph → List Update → ℕ → Prop
  | 0, _, _, _, _, _ => True
  | rem + 1, idx, st, curG, curU, curEnc =>
    if intRebuildThreshold cfg.P st.N₀ idx < st.updCount idx + curU.length then True
    else
      let Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
      let ℓi := Cpartial.chainLen ℓ' idx
      let gi := Cpartial.chainGrad g' idx
      let updRes := cfg.T.updateOrd (st.scState idx) curU ℓi gi
        (Chain.Ordered.chainLevelOrd cfg.T (fun j => if j = idx then curG else st.G j)
          st.scState st.bran idx)
      let sc' := updRes.1
      let nextG := cfg.T.S sc' (st.bran idx)
      let nextU := updRes.2 (st.bran idx)
      let nextEnc := (st.G (idx + 1)).batchEnc nextU
      let fiChanges := diffTreeChanges (cfg.T.lsfs (st.scState idx) (st.bran idx)).F.F.E
        (cfg.T.lsfs sc' (st.bran idx)).F.F.E
      let stNext : ChainState cfg.T cfg.P :=
        { st with
          G := fun j => if j = idx then curG else st.G j
          scState := fun j => if j = idx then sc' else st.scState j
          updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
          recUpdates := fun j =>
            if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
          curFwd := fun j =>
            if j = idx then st.curFwd idx + nextU.length else st.curFwd j
          curEnc := fun j =>
            if j = idx then st.curEnc idx + curEnc
            else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc
            else st.curEnc j
          curDecUpdates := fun j =>
            if j = idx then st.curDecUpdates idx + fiChanges.length else st.curDecUpdates j }
      5 * (cfg.T.S (st.scState idx) (st.bran idx)).batchEnc nextU + 1 ≤ BWc (idx + 1) ∧
      edMul * (cfg.T.cost sc' - cfg.T.cost (st.scState idx) +
        (BWc idx + EWc idx + 1) * logf idx) ≤ EWc (idx + 1) ∧
      nextU.length ≤ ULc (idx + 1) ∧
      UpdateLoopSizeInv cfg ℓ' g' edMul logf BWc EWc ULc rem (idx + 1) stNext nextG nextU 0

/-- The state of the machine at the top of the plain-step loop of Branch B at level `idx`.

The model state is `ch`: the levels `j < idx` took their plain step, the batch `curU` enters
level `idx`, and `curG = (ch.G idx).applyBatch curU`. The start state of the loop is `ch0`.
The core of level `j` is at `A.coreH j` with token `tok j`. Its abstract state is that of `ch`,
except at `idx`, where its order is still the old one `oldOrd`. The lists of the finished levels
`j < idx` are `D j`, their input batches `levelU j` and their forwarded batches `levelUS j`. The
cores of the levels `j ≥ idx` are still in their start state: the stored order of level `idx` is
the one of `ch0` (`oldOrdEq`), and so are the update counters from `idx` on (`updFrame`). The
word `A.lvlMTable - 1` holds `N₀` (`hdrCell`), and `n0Word` places it away from everything a step
writes. -/
structure BranchBLoopInvKFBL {w L P depth vCap eCap capExp : ℕ} {fmt : Num.Format w}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))}
    (reembFn : ToolReembFn cfg.T) (A : BranchBAddrs) (origLen : ℕ → ℕ → ℝ) (ℓ' : ℕ → ℝ)
    (N0 : ℕ) (BWc EWc ULc : ℕ → ℕ) (ch0 : ChainState cfg.T cfg.P) (termTok : RL.τ)
    (idx : ℕ) (ch : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update)
    (curEditsList : List OrdEdit) (oldOrd : ℕ → List End) (st : State) (tok : ℕ → Rcore.τ)
    (curBatch curBatchWords curEdits curEditsWords : ℕ) (levelU levelUS : ℕ → List Update)
    (D : ℕ → LevelDiffLists) : Prop where
  idxLe : idx ≤ cfg.P.d
  regs : A.heapFloor ≤ st.regs 4 ∧ st.regs 10 = curBatch ∧ st.regs 11 = curBatchWords ∧
    st.regs 12 = curEdits ∧ st.regs 13 = curEditsWords ∧ st.regs 72 = A.selBase ∧
    st.regs 73 = A.handle ∧ st.regs 74 = A.table ∧ st.regs 75 = cfg.P.d ∧
    st.regs 76 = cfg.P.k ∧ st.regs 77 = A.handleBase ∧ st.regs 78 = A.branchBase ∧
    st.regs 82 = A.lvlMTable ∧ st.regs 83 = A.levelMeta ∧ st.regs 85 = A.ucBase ∧
    st.regs 86 = A.rcBase ∧ st.regs 94 = L ∧ st.regs 95 = P ∧ st.regs 96 = idx ∧
    st.regs 97 = 0 ∧ st.regs 98 = depth ∧ st.regs 99 = cfg.P.d
  hdrCell : st.mem (A.lvlMTable - 1) = N0
  n0Word : 0 < A.lvlMTable ∧
    (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) (A.lvlMTable - 1)) ∧
    (∀ j < cfg.P.d,
      (A.lvlMTable - 1 < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ A.lvlMTable - 1) ∧
      (A.lvlMTable - 1 < A.lPtr0 j ∨ A.lPtr0 j + eCap * L ≤ A.lvlMTable - 1) ∧
      A.lvlMTable - 1 ≠ A.ucBase + j ∧ A.lvlMTable - 1 ≠ A.rcBase + j)
  cells : ∀ j < cfg.P.d,
    st.mem (A.table + j) = intRebuildThreshold cfg.P N0 j ∧
    st.mem (A.lvlMTable + j) = ch.lvlM j ∧
    st.mem (A.handleBase + j) = A.coreH j ∧
    st.mem (A.branchBase + j) = ch.bran j ∧
    ch.bran j < cfg.P.k ∧ A.coreH j < 2 ^ w ∧
    st.mem (A.levelMeta + cfg.P.d + j) = A.gPtr0 j ∧
    st.mem (A.levelMeta + j) = A.lPtr0 j ∧
    st.mem (A.ucBase + j) = ch.updCount j ∧
    st.mem (A.rcBase + j) = ch.rebuildCount j
  termCells : st.mem (A.handleBase + cfg.P.d) = A.coreH cfg.P.d ∧
    st.mem (A.branchBase + cfg.P.d) = ch.lastBran
  reps : ∀ j < cfg.P.d,
    Rcore.rep (A.coreH j)
      (if j = idx then ⟨ch.scState j, ch.G j, oldOrd, ch.updCount j⟩ else chainLevelOrdAbs ch j)
      (tok j) st.mem ∧
    (∀ a, Rcore.foot (A.coreH j) (tok j) a → a < st.regs 4)
  footLoc : ∀ j < cfg.P.d, ∀ a, Rcore.foot (A.coreH j) (tok j) a →
    a < A.selBase ∨ A.heapFloor ≤ a
  footOld : ∀ j, idx ≤ j → j < cfg.P.d → ∀ a, Rcore.foot (A.coreH j) (tok j) a → a < A.selBase
  disj : ∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ ≠ j₂ →
    ∀ a, Rcore.foot (A.coreH j₁) (tok j₁) a → ¬ Rcore.foot (A.coreH j₂) (tok j₂) a
  static : BranchBCoresDisjStatic (cfg := cfg) (Rcore := Rcore) L A.handle A.table A.handleBase
    A.branchBase A.lvlMTable A.levelMeta A.rcBase A.ucBase (fun _ => vCap) (fun _ => eCap)
    A.gPtr0 A.lPtr0 A.coreH tok
  graphs : ∀ j < cfg.P.d, DynGraphAt st.mem (A.gPtr0 j) vCap eCap (ch.G j)
  lensLt : ∀ j < idx,
    EdgeValuesAt st.mem (A.lPtr0 j) 4 L P (ch.G j).E (ch.toTreeChain.chainLen ℓ' j)
  lensEq : idx < cfg.P.d →
    EdgeValuesAt st.mem (A.lPtr0 idx) 4 L P curG.E
      (({ ch.toTreeChain with G := fun j => if j = idx then curG else ch.G j } : TreeChain).chainLen
        ℓ' idx)
  lensGt : ∀ j, idx < j → j < cfg.P.d →
    EdgeValuesAt st.mem (A.lPtr0 j) 4 L P (ch.G j).E (origLen j)
  term : RL.rep (A.coreH cfg.P.d) (ch.lastK, ch.lastLSFs) termTok st.mem ∧
    (∀ a, RL.foot (A.coreH cfg.P.d) termTok a →
      a < A.selBase ∧
      (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) a) ∧
      (∀ j < cfg.P.d, (a < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ a) ∧
        (a < A.lPtr0 j ∨ A.lPtr0 j + eCap * L ≤ a)) ∧
      (a < A.handleBase ∨ A.handleBase + cfg.P.d < a) ∧
      (a < A.branchBase ∨ A.branchBase + cfg.P.d < a) ∧
      (a < A.levelMeta ∨ A.levelMeta + 2 * cfg.P.d ≤ a) ∧
      (a < A.ucBase ∨ A.ucBase + cfg.P.d ≤ a) ∧
      (a < A.rcBase ∨ A.rcBase + cfg.P.d < a))
  batchLen : st.mem curBatch = curU.length
  batch : idx < cfg.P.d →
    SmallBatchAt st.mem curBatch (ch.G idx) curU curBatchWords ∧
    (decodeBatch st.mem curBatch (ch.G idx)).1 = curU ∧
    (∀ t < curBatchWords, st.mem (curBatch + t) < 2 ^ w ∧
      ∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) (curBatch + t)) ∧
    A.heapFloor ≤ curBatch ∧ curBatch + curBatchWords ≤ st.regs 4 ∧
    OrdEditsAt st.mem curEdits curEditsList curEditsWords ∧
    (∀ t < curEditsWords, st.mem (curEdits + t) < 2 ^ w) ∧
    curEdits + curEditsWords ≤ st.regs 4 ∧
    applyOrdEdits oldOrd curEditsList =
      chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j) ch.scState ch.bran idx ∧
    OrdEditsValidFor vCap eCap oldOrd curEditsList ∧
    OrdEditsForBatch (ch.G idx) curU curEditsList
  sizes : curBatchWords ≤ BWc idx ∧ curEditsWords ≤ EWc idx ∧ curU.length ≤ ULc idx
  slots : BranchBDoneSlots w P cfg.P.d
    (fun j => ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
    (fun r => Rcore.foot (A.coreH r) (tok r)) A.heapFloor (st.regs 4) A.selBase st.mem idx D
    ch0.G levelU (fun j => (ch.G j).E) (fun j => (cfg.T.lsfs (ch.scState j) (ch.bran j)).wstr)
  slotModel : ∀ j < idx,
    (D j).uG = coreBatchTouchedEdges (levelU j) ∧
    (D j).uS = coreBatchTouchedEdges (levelUS j) ∧
    (D j).fDel.Nodup ∧
    (D j).fDel.toFinset = (cfg.T.lsfs (ch0.scState j) (ch0.bran j)).F.F.E \
      (cfg.T.lsfs (ch.scState j) (ch.bran j)).F.F.E ∧
    (D j).reemb = reembFn (ch0.scState j) (levelU j) (ch.levelOrd j) (ch0.bran j) ∧
    BatchWithinCaps vCap eCap (levelU j) ∧
    ch.G j = (ch0.G j).applyBatch (levelU j) ∧ (ch0.G j).BatchIsValid (levelU j) ∧
    levelU (j + 1) = levelUS j ∧
    ∃ ℓj gj ordj,
      ch.scState j = (cfg.T.updateOrd (ch0.scState j) (levelU j) ℓj gj ordj).1 ∧
      levelUS j = (cfg.T.updateOrd (ch0.scState j) (levelU j) ℓj gj ordj).2 (ch0.bran j)
  curULink : levelU idx = curU
  modelFrame : (∀ j, idx ≤ j → ch.G j = ch0.G j ∧ ch.scState j = ch0.scState j) ∧
    ch.bran = ch0.bran ∧ ch.lastK = ch0.lastK ∧ ch.lastLSFs = ch0.lastLSFs ∧
    ch.lastBran = ch0.lastBran ∧ ch.N₀ = N0 ∧ ch.lvlM = ch0.lvlM ∧
    ch.rebuildCount = ch0.rebuildCount
  zero : ZeroFrom st.mem (st.regs 4)
  oldOrdEq : oldOrd = ch0.levelOrd idx
  updFrame : ∀ j, idx ≤ j → ch.updCount j = ch0.updCount j

end MinCostFlow.MinRatio
