module

public import MinCostFlow.MinRatio.WireChainCoreBranchBHeadKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBTailKFBL
import MinCostFlow.SparseCore.Program.AssemblyReemb
import MinCostFlow.SparseCore.Program.OutStepIns
import MinCostFlow.MinRatio.WireSelectEvalKeyMath
import WordRAM.Tactic

/-!
# A Branch B level step under `KFBL` (`WireChainCoreBranchBStepKFBL`)

At a level `idx` that `Update` does not rebuild, the chain-update core runs the head of the step
(`wireBranchBStepHeadKFBL`: op `0` on the batch of the level, the level graph, the update counter
and the forwarded batch) and then its tail (`wireBranchBStepTailKFBL`: the copies of the `fDel`
list and of the re-embedding list of the active branch, op `2` with the copy of its descriptor, the
core lengths of the next level, and the slot of the level). This file puts the two together as
`wireBranchBStepKFBL` and proves its run lemma `wireBranchBStepKFBL_runs`.

The proof composes the two run lemmas. The head changes, below its heap pointer `curHeap`, only the
core footprint, the level graph and the update counter. So the batch of the level, the lengths of
the level and the old lengths of the next level reach the tail unchanged. The tail changes, below
`curHeap`, only the core footprint, the lengths of the next level and the slot. So the level graph,
the counter and the forwarded batch and edits of the head reach the end unchanged. The level clause
of the tail moves to the region `[curHeap, out.regs 4)` without a change of memory.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- A non-rebuild level step at `idx = reg 96`: the head (op `0`, the level graph, the update
counter, the forwarded batch) and the tail (the copies, op `2`, the next lengths, the slot). -/
@[expose] def wireBranchBStepKFBL (updCore readLSF dgApply copyProc updLen slotProc : ℕ) : Stmt :=
  wireBranchBStepHeadKFBL updCore dgApply ;;
  wireBranchBStepTailKFBL copyProc readLSF updLen slotProc

theorem wireBranchBStepKFBL_noRand (updCore readLSF dgApply copyProc updLen slotProc : ℕ) :
    (wireBranchBStepKFBL updCore readLSF dgApply copyProc updLen slotProc).NoRand := by
  simp only [wireBranchBStepKFBL, Stmt.NoRand, wireBranchBStepHeadKFBL_noRand,
    wireBranchBStepTailKFBL_noRand, and_self]

private theorem step_cost_arith {cH cT phi0 phi1 phiF X bW U F Ro Y : ℕ}
    (hH : cH + phi1 ≤ X + 670 * bW + 200 + phi0)
    (hT : cT + phiF ≤ F + Ro + Y + 60 * U + 700 + phi1) (hU : 2 * U ≤ bW) :
    cH + cT + 1 + phiF ≤ X + 700 * bW + F + Ro + Y + 901 + phi0 := by
  omega

/-- A word that the step lemma keeps: below the heap pointer, off the old footprint, the level
graph, the update counter, the next lengths and the slot. -/
private theorem step_frame {mem₀ mem₁ mem₂ : ℕ → ℕ} {foot0 foot1 : ℕ → Prop}
    {curHeap h1 gPtr gSize ucAddr nlPtr nlLen slot : ℕ} {next : Prop} {x : ℕ}
    (hfr1 : ∀ a < curHeap, ¬ foot0 a → (a < gPtr ∨ gPtr + gSize ≤ a) → a ≠ ucAddr →
      mem₁ a = mem₀ a)
    (hfr2 : ∀ a < h1, ¬ foot1 a → (next → a < nlPtr ∨ nlPtr + nlLen ≤ a) →
      (a < slot ∨ slot + 12 ≤ a) → mem₂ a = mem₁ a)
    (hfoot1 : ∀ a, foot1 a → foot0 a ∨ (curHeap ≤ a ∧ a < h1)) (hH1 : curHeap ≤ h1)
    (hx : x < curHeap) (h0 : ¬ foot0 x) (hg : x < gPtr ∨ gPtr + gSize ≤ x) (hu : x ≠ ucAddr)
    (hn : next → x < nlPtr ∨ nlPtr + nlLen ≤ x) (hs : x < slot ∨ slot + 12 ≤ x) :
    mem₂ x = mem₀ x := by
  have h1 : ¬ foot1 x := fun h => by
    rcases hfoot1 x h with h' | h'
    · exact h0 h'
    · omega
  rw [hfr2 x (by omega) h1 hn hs, hfr1 x hx h0 hg hu]

set_option maxHeartbeats 1600000 in
/-- One run of a non-rebuild level step. Op `0` turns the abstract state of the level into
`aNext`, the level graph becomes `curG`, the update counter grows by the batch length, and the
forwarded batch and order edits of the active branch `b` lie in fresh heap, off the new footprint,
with their pointers in `regs 10..13`. When `idx + 1 < d`, the core lengths of the next level are
written. Below `curHeap`, only the footprint of the core, the level graph, the update counter, the
next lengths and the slot of the level change. The memory clauses of the level hold at the final
memory (`SelOutLevelMemAt`), with the change record `c` of branch `b`, its re-embedding list, the
two touched-edge lists and the stretch descriptor in `[curHeap, out.regs 4)` off the new footprint,
and the batch at `curBatch`. The heap grows by at most three op-`0` allocations, the next lengths,
the two touched-edge lists and a constant. -/
theorem wireBranchBStepKFBL_runs
    {w L P depth M N vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy idx coreH gPtr lPtr nextLPtr curBatch curBatchWords curEdits
      curEditsWords curHeap handleBase branchBase levelMeta updCountBase selBase ecNext : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc : ℕ → List ℕ → ℕ} {Ginit : MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opCore : ℕ → ℕ}
    {ω : ℕ → Bool} {st : State}
    (ch : ChainState cfg.T cfg.P) (curU : List Update) (curEditsList : List OrdEdit)
    (oldOrd : ℕ → List End) (ℓi gi oldNextℓ : ℕ → ℝ) (coreTok0 : Rcore.τ)
    (hCoreLocal : Rcore.Local)
    (hFour : fmt.limbBits = 4) (hPrec : fmt.precision = P) (hw16 : 16 ≤ 2 ^ w)
    (hUpdOrdEq : ToolUpdateOrdEqOnE cfg.T)
    (hCoreImpl : Rcore.Implements w p initCore opCore
      (sparseCoreOrdMachineContractKFRBL fmt L depth cfg.T reembFn Ginit cfg.P.k M N vCap eCap
        capExp Psc alloc))
    (hOut : SparseCoreUpdateOutFootAt fmt L depth cfg.T Ginit cfg.P.k M N vCap eCap capExp Psc
      alloc edMul Rcore p opCore)
    (hPlace : SparseCoreReembPlaceAt fmt L depth cfg.T Ginit cfg.P.k M N vCap eCap capExp Psc
      alloc Rcore p opCore)
    (hFootAt : SparseCoreReadoutFootAt fmt L depth cfg.T Ginit cfg.P.k M N vCap eCap capExp Psc
      alloc Rcore p opCore)
    (hDGApply : MeetsContract w p dgApply
      (dgApplyBatchContract w vCap eCap (ch.G idx) (ch.G idx) curU curBatchWords))
    (hCopy : p.procs[copyProc]? = some wireRawCopyBody)
    (hSlotP : p.procs[slotProc]? = some (wireSelOutSlotBody collectProc))
    (hColl : p.procs[collectProc]? = some wireCollectTouchedEdgesBody)
    (hUpdLen : p.procs[updLen]? = some (wireUpdateCoreLenFromBatchBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopyW : MeetsContract w p copy (copyWordsContract w))
    (hIdx : idx < cfg.P.d) (hdW : cfg.P.d < 2 ^ w) (hkW : cfg.P.k < 2 ^ w)
    (hRegs :
      st.regs 4 = curHeap ∧ st.regs 10 = curBatch ∧ st.regs 11 = curBatchWords ∧
      st.regs 12 = curEdits ∧ st.regs 13 = curEditsWords ∧ st.regs 72 = selBase ∧
      st.regs 75 = cfg.P.d ∧ st.regs 76 = cfg.P.k ∧ st.regs 77 = handleBase ∧
      st.regs 78 = branchBase ∧ st.regs 83 = levelMeta ∧ st.regs 85 = updCountBase ∧
      st.regs 94 = L ∧ st.regs 96 = idx)
    (hHCell : st.mem (handleBase + idx) = coreH)
    (hBCell : st.mem (branchBase + idx) = ch.bran idx)
    (hBrLt : ch.bran idx < cfg.P.k)
    (hGCell : st.mem (levelMeta + cfg.P.d + idx) = gPtr)
    (hLCell : st.mem (levelMeta + idx) = lPtr)
    (hNLCell : idx + 1 < cfg.P.d → st.mem (levelMeta + (idx + 1)) = nextLPtr)
    (hUCCell : st.mem (updCountBase + idx) = ch.updCount idx)
    (hUCW : ch.updCount idx + curU.length < 2 ^ w)
    (hCoreH_W : coreH < 2 ^ w)
    (hRep : Rcore.rep coreH ⟨ch.scState idx, ch.G idx, oldOrd, ch.updCount idx⟩ coreTok0 st.mem)
    (hIn : SparseCoreOrdInput cfg.T cfg.P.k M N (ch.scState idx) (ch.G idx) oldOrd
      (ch.updCount idx))
    (hFoot : ∀ a, Rcore.foot coreH coreTok0 a → a < curHeap)
    (hGAt : DynGraphAt st.mem gPtr vCap eCap (ch.G idx))
    (hSmall : SmallBatchAt st.mem curBatch (ch.G idx) curU curBatchWords)
    (hDecode : (decodeBatch st.mem curBatch (ch.G idx)).1 = curU)
    (hBatchValid : (ch.G idx).BatchIsValid curU)
    (hBatchCaps : BatchWithinCaps vCap eCap curU)
    (hBatchW : ∀ j < curBatchWords, st.mem (curBatch + j) < 2 ^ w)
    (hEditsAt : OrdEditsAt st.mem curEdits curEditsList curEditsWords)
    (hEditsW : ∀ j < curEditsWords, st.mem (curEdits + j) < 2 ^ w)
    (hValid : OrdEditsValidFor vCap eCap oldOrd curEditsList)
    (hBlocks : OrdEditsForBatch (ch.G idx) curU curEditsList)
    (hNewOrdEq :
      applyOrdEdits oldOrd curEditsList =
        chainLevelOrd cfg.T (fun j => if j = idx then (ch.G idx).applyBatch curU else ch.G j)
          ch.scState ch.bran idx)
    (hOrdBatch : OrderedBatch (ch.G idx) curU oldOrd (applyOrdEdits oldOrd curEditsList))
    (hUpdThresh : ((ch.updCount idx + curU.length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold cfg.P.k M N)
    (hLenAt : EdgeValuesAt st.mem lPtr 4 L P ((ch.G idx).applyBatch curU).E ℓi)
    (hLenCap : ∀ e ∈ ((ch.G idx).applyBatch curU).E, e < eCap)
    (hLenPos : ∀ e ∈ ((ch.G idx).applyBatch curU).E, 0 < ℓi e)
    (hNext : idx + 1 < cfg.P.d →
      let curG := (ch.G idx).applyBatch curU
      let newOrd := chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j)
        ch.scState ch.bran idx
      let upd := cfg.T.updateOrd (ch.scState idx) curU ℓi gi newOrd
      let GS := cfg.T.S (ch.scState idx) (ch.bran idx)
      EdgeValuesAt st.mem nextLPtr 4 L P GS.E oldNextℓ ∧ (∀ e ∈ GS.E, e < ecNext) ∧
      (∀ u ∈ upd.2 (ch.bran idx), match u with
        | .insert e _ _ => e ∈ curG.E ∧ e < eCap ∧ e < ecNext ∧
            (∃ q : ℤ, Num.Fits 4 L q ∧
              (q : ℝ) / (2 : ℝ) ^ P = coreLen (cfg.T.lsfs upd.1 (ch.bran idx)) ℓi e)
        | _ => True) ∧
      (∀ e ∈ (GS.applyBatch (upd.2 (ch.bran idx))).E,
        (¬ ∃ u ∈ upd.2 (ch.bran idx), u.Inserts e) →
        e ∈ GS.E ∧ oldNextℓ e = coreLen (cfg.T.lsfs upd.1 (ch.bran idx)) ℓi e))
    (hBelow :
      handleBase + idx < curHeap ∧ branchBase + idx < curHeap ∧
      levelMeta + cfg.P.d + idx < curHeap ∧ updCountBase + idx < curHeap ∧
      gPtr + dynGraphSize vCap eCap ≤ curHeap ∧ lPtr + eCap * L ≤ curHeap ∧
      curBatch + curBatchWords ≤ curHeap ∧ curEdits + curEditsWords ≤ curHeap)
    (hDisj :
      (∀ a, gPtr ≤ a → a < gPtr + dynGraphSize vCap eCap →
        ¬ Rcore.foot coreH coreTok0 a ∧ a ≠ updCountBase + idx ∧
        (a < curBatch ∨ curBatch + curBatchWords ≤ a)) ∧
      ¬ Rcore.foot coreH coreTok0 (updCountBase + idx) ∧
      (updCountBase + idx < curBatch ∨ curBatch + curBatchWords ≤ updCountBase + idx) ∧
      (∀ t < curBatchWords, ¬ Rcore.foot coreH coreTok0 (curBatch + t)))
    (hLenOff : ∀ x, lPtr ≤ x → x < lPtr + eCap * L →
      ¬ Rcore.foot coreH coreTok0 x ∧ (x < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ x) ∧
        x ≠ updCountBase + idx)
    (hNextOff : idx + 1 < cfg.P.d →
      nextLPtr + ecNext * L ≤ curHeap ∧
      (lPtr + eCap * L ≤ nextLPtr ∨ nextLPtr + ecNext * L ≤ lPtr) ∧
      (∀ x, nextLPtr ≤ x → x < nextLPtr + ecNext * L →
        ¬ Rcore.foot coreH coreTok0 x ∧ (x < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ x) ∧
          x ≠ updCountBase + idx) ∧
      ¬ Rcore.foot coreH coreTok0 (levelMeta + (idx + 1)) ∧
      (levelMeta + (idx + 1) < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ levelMeta + (idx + 1)) ∧
      levelMeta + (idx + 1) ≠ updCountBase + idx ∧
      (∀ t < curBatchWords, curBatch + t < nextLPtr ∨ nextLPtr + ecNext * L ≤ curBatch + t))
    (hSlotLe : selBase + 1 + 12 * idx + 12 ≤ curHeap)
    (hSlotOff : ∀ i < 12, ¬ Rcore.foot coreH coreTok0 (selBase + 1 + 12 * idx + i) ∧
      (selBase + 1 + 12 * idx + i < curBatch ∨
        curBatch + curBatchWords ≤ selBase + 1 + 12 * idx + i) ∧
      (idx + 1 < cfg.P.d → selBase + 1 + 12 * idx + i < nextLPtr ∨
        nextLPtr + ecNext * L ≤ selBase + 1 + 12 * idx + i) ∧
      (selBase + 1 + 12 * idx + i < gPtr ∨
        gPtr + dynGraphSize vCap eCap ≤ selBase + 1 + 12 * idx + i) ∧
      selBase + 1 + 12 * idx + i ≠ updCountBase + idx)
    (hz : ZeroFrom st.mem curHeap)
    (hRoom :
      let curG := (ch.G idx).applyBatch curU
      let newOrd := chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j)
        ch.scState ch.bran idx
      let nextU := (cfg.T.updateOrd (ch.scState idx) curU ℓi gi newOrd).2 (ch.bran idx)
      curHeap + 3 * alloc 0
          [coreH, gPtr, curBatch, curBatchWords, curEdits, curEditsWords, lPtr, lPtr, curHeap] +
        7 + nextU.length * wireCoreLenEdgeSpace (ordLevelLwMax L capExp M N) + curU.length +
        nextU.length < 2 ^ w) :
    let curG := (ch.G idx).applyBatch curU
    let newOrd := chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j)
      ch.scState ch.bran idx
    let upd := cfg.T.updateOrd (ch.scState idx) curU ℓi gi newOrd
    let sc' := upd.1
    let nextU := upd.2 (ch.bran idx)
    let aNext : SparseCoreOrdAbs cfg.T := ⟨sc', curG, newOrd, ch.updCount idx + curU.length⟩
    let args := [coreH, gPtr, curBatch, curBatchWords, curEdits, curEditsWords, lPtr, lPtr, curHeap]
    let k := cfg.P.k
    let b := ch.bran idx
    let GS := cfg.T.S (ch.scState idx) b
    let reemb := reembFn (ch.scState idx) curU newOrd b
    let LwMax := ordLevelLwMax L capExp M N
    ∃ (out : State) (cost : ℕ) (coreTok' : Rcore.τ) (nextEdits : List OrdEdit)
      (c : Read.LSFChange),
      Runs w p ω (wireBranchBStepKFBL (opCore 0) (opCore 2) dgApply copyProc updLen slotProc)
        st .normal out cost ∧
      curHeap ≤ out.regs 4 ∧
      out.regs 4 ≤ curHeap + 3 * alloc 0 args + 7 + nextU.length * wireCoreLenEdgeSpace LwMax +
        curU.length + nextU.length ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      Rcore.rep coreH aNext coreTok' out.mem ∧
      SparseCoreOrdInput cfg.T k M N sc' curG newOrd (ch.updCount idx + curU.length) ∧
      (∀ a, Rcore.foot coreH coreTok' a →
        Rcore.foot coreH coreTok0 a ∨ (curHeap ≤ a ∧ a < out.regs 4)) ∧
      DynGraphAt out.mem gPtr vCap eCap curG ∧
      out.mem (updCountBase + idx) = ch.updCount idx + curU.length ∧
      SmallBatchAt out.mem (out.regs 10) GS nextU (out.regs 11) ∧
      (decodeBatch out.mem (out.regs 10) GS).1 = nextU ∧
      OrdEditsAt out.mem (out.regs 12) nextEdits (out.regs 13) ∧
      applyOrdEdits (cfg.T.rot (ch.scState idx) b) nextEdits = cfg.T.rot sc' b ∧
      OrdEditsForBatch GS nextU nextEdits ∧
      OrdEditsValidFor vCap eCap (cfg.T.rot (ch.scState idx) b) nextEdits ∧
      curHeap ≤ out.regs 10 ∧ out.regs 10 + out.regs 11 ≤ out.regs 4 ∧
      curHeap ≤ out.regs 12 ∧ out.regs 12 + out.regs 13 ≤ out.regs 4 ∧
      (∀ t < out.regs 11, out.mem (out.regs 10 + t) < 2 ^ w ∧
        ¬ Rcore.foot coreH coreTok' (out.regs 10 + t)) ∧
      (∀ t < out.regs 13, out.mem (out.regs 12 + t) < 2 ^ w ∧
        ¬ Rcore.foot coreH coreTok' (out.regs 12 + t)) ∧
      out.regs 13 ≤ edMul * (cfg.T.cost sc' - cfg.T.cost (ch.scState idx) +
        (curBatchWords + curEditsWords + 1) * SparseCore.bundleLogFactor M N) ∧
      (idx + 1 < cfg.P.d →
        EdgeValuesAt out.mem nextLPtr 4 L P (GS.applyBatch nextU).E
          (coreLen (cfg.T.lsfs sc' b) ℓi)) ∧
      (∀ a < curHeap, ¬ Rcore.foot coreH coreTok0 a →
        (a < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ a) → a ≠ updCountBase + idx →
        (idx + 1 < cfg.P.d → a < nextLPtr ∨ nextLPtr + ecNext * L ≤ a) →
        (a < selBase + 1 + 12 * idx ∨ selBase + 1 + 12 * idx + 12 ≤ a) →
        out.mem a = st.mem a) ∧
      c.Exact (cfg.T.lsfs (ch.scState idx) b) (cfg.T.lsfs sc' b) ∧ (∀ e ∈ c.fDel, e < 2 ^ w) ∧
      SelOutLevelMemAt w P LwMax
        (fun x => (curHeap ≤ x ∧ ¬ Rcore.foot coreH coreTok' x) ∨
          (curBatch ≤ x ∧ x < curBatch + curBatchWords))
        (fun x => Rcore.foot coreH coreTok' x ∨ (curHeap ≤ x ∧ x < out.regs 4))
        curBatch (out.regs 4) out.mem (selBase + 1 + 12 * idx)
        ⟨coreBatchTouchedEdges curU, c.fDel, coreBatchTouchedEdges nextU, reemb⟩ (ch.G idx) curU
        curG.E (cfg.T.lsfs sc' b).wstr ∧
      cost + Rcore.phi coreH coreTok' out.mem ≤
        Psc.mul * (cfg.T.cost sc' - cfg.T.cost (ch.scState idx) +
          (k + 1) * (curBatchWords + curEditsWords + 1) * SparseCore.bundleLogFactor M N) +
        700 * curBatchWords + 20 * (c.fDel.length + reemb.length) + Psc.readout +
        nextU.length * (wireCoreLenEdgeCost LwMax + 120) + 901 +
        Rcore.phi coreH coreTok0 st.mem := by
  dsimp only at hNext hRoom ⊢
  set curG := (ch.G idx).applyBatch curU with hcurG
  set newOrd := chainLevelOrd cfg.T (fun j => if j = idx then curG else ch.G j) ch.scState
    ch.bran idx with hnewOrd
  set upd := cfg.T.updateOrd (ch.scState idx) curU ℓi gi newOrd with hupd
  set sc' := upd.1 with hsc'
  set nextU := upd.2 (ch.bran idx) with hnextU
  set aNext : SparseCoreOrdAbs cfg.T := ⟨sc', curG, newOrd, ch.updCount idx + curU.length⟩
    with haNext
  set A0 := alloc 0
    [coreH, gPtr, curBatch, curBatchWords, curEdits, curEditsWords, lPtr, lPtr, curHeap] with hA0
  obtain ⟨hr4, hr10, hr11, hr12, hr13, hr72, hr75, hr76, hr77, hr78, hr83, hr85, hr94, hr96⟩ :=
    hRegs
  obtain ⟨hHBLt, hBBLt, hLMLt, hUCLt, hGLe, hLLe, hBLe, hELe⟩ := hBelow
  obtain ⟨hDisjG, hUCFoot, hUCB, hDisjB⟩ := hDisj
  -- the head
  obtain ⟨s1, cH, h1, tok1, rH, h4H, hH1lo, hH1hi, hr2H, hr3H, hr6H, hr7H, hr23H, hr24H, hr25H,
      hr10H, hr11H, hr12H, hr13H, hreg70, hz1, hrep1, hIn1, hfoot1, hG1, hUC1, hUS1, hDec1,
      ⟨nextEdits, hEd1, hEdRot, hEdFor, hEdValid⟩, hbase3, hUSlo, hUShi, hEdlo, hEdhi, hUSW1,
      hEdW1, hEdB, hF1, hR1, hRlo1, hRhi1, hfr1, hcH⟩ :=
    wireBranchBStepHeadKFBL_runs (ω := ω) ch curU curEditsList oldOrd ℓi gi coreTok0 hCoreLocal
      hFour hPrec hw16 hUpdOrdEq hCoreImpl hOut hPlace hDGApply
      ⟨hr4, hr10, hr11, hr12, hr13, hr75, hr77, hr78, hr83, hr85, hr96⟩ hHCell hBCell hBrLt
      hGCell hLCell hUCCell hUCW hCoreH_W hRep hIn hFoot hGAt hSmall hDecode hBatchValid
      hBatchCaps hBatchW hEditsAt hEditsW hValid hBlocks hNewOrdEq hOrdBatch hUpdThresh hLenAt
      hLenCap hLenPos ⟨hHBLt, hBBLt, hLMLt, hUCLt, hGLe, hLLe, hBLe, hELe⟩
      ⟨hDisjG, hUCFoot, hUCB, hDisjB⟩ hz (by omega)
  -- what the head keeps for the tail
  have hBoff : ∀ x, curBatch ≤ x → x < curBatch + curBatchWords →
      ¬ Rcore.foot coreH coreTok0 x ∧ (x < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ x) ∧
        x ≠ updCountBase + idx := fun x hx1 hx2 => by
    refine ⟨?_, ?_, by omega⟩
    · have := hDisjB (x - curBatch) (by omega)
      rwa [show curBatch + (x - curBatch) = x by omega] at this
    · by_contra hc
      have := (hDisjG x (by omega) (by omega)).2.2
      omega
  have hU1 : SmallBatchAt s1.mem curBatch (ch.G idx) curU curBatchWords :=
    smallBatchAt_of_agree hSmall fun x hx1 hx2 => by
      obtain ⟨h0, hg, hu⟩ := hBoff x hx1 hx2
      exact hfr1 x (by omega) h0 hg hu
  have hUW1 : ∀ t < curBatchWords, s1.mem (curBatch + t) < 2 ^ w := fun t ht => by
    obtain ⟨h0, hg, hu⟩ := hBoff (curBatch + t) (by omega) (by omega)
    rw [hfr1 _ (by omega) h0 hg hu]; exact hBatchW t ht
  have hLen1 : EdgeValuesAt s1.mem lPtr 4 L P curG.E ℓi :=
    EdgeValuesAt.congr hLenAt fun e he i hi => by
      have := branchBEntry_lt (hLenCap e he) hi
      obtain ⟨h0, hg, hu⟩ := hLenOff (lPtr + e * L + i) (by omega) (by omega)
      exact hfr1 _ (by omega) h0 hg hu
  have hNext1 : idx + 1 < cfg.P.d →
      levelMeta + (idx + 1) < curHeap ∧ ¬ Rcore.foot coreH coreTok0 (levelMeta + (idx + 1)) ∧
      s1.mem (levelMeta + (idx + 1)) = nextLPtr ∧
      EdgeValuesAt s1.mem nextLPtr 4 L P (cfg.T.S (ch.scState idx) (ch.bran idx)).E oldNextℓ ∧
      (∀ e ∈ (cfg.T.S (ch.scState idx) (ch.bran idx)).E, e < ecNext) ∧
      (∀ u ∈ nextU, match u with
        | .insert e _ _ => e ∈ curG.E ∧ e < eCap ∧ e < ecNext ∧
            (∃ q : ℤ, Num.Fits 4 L q ∧
              (q : ℝ) / (2 : ℝ) ^ P = coreLen (cfg.T.lsfs sc' (ch.bran idx)) ℓi e)
        | _ => True) ∧
      (∀ e ∈ ((cfg.T.S (ch.scState idx) (ch.bran idx)).applyBatch nextU).E,
        (¬ ∃ u ∈ nextU, u.Inserts e) →
        e ∈ (cfg.T.S (ch.scState idx) (ch.bran idx)).E ∧
          oldNextℓ e = coreLen (cfg.T.lsfs sc' (ch.bran idx)) ℓi e) ∧
      (∀ e ∈ ((cfg.T.S (ch.scState idx) (ch.bran idx)).applyBatch nextU).E,
        (∃ u ∈ nextU, u.Inserts e) → ∃ j, ∃ hj : j < nextU.length, nextU[j].Inserts e) ∧
      nextLPtr + ecNext * L ≤ curHeap ∧
      (lPtr + eCap * L ≤ nextLPtr ∨ nextLPtr + ecNext * L ≤ lPtr) ∧
      (∀ x, nextLPtr ≤ x → x < nextLPtr + ecNext * L → ¬ Rcore.foot coreH coreTok0 x) ∧
      (∀ t < curBatchWords, curBatch + t < nextLPtr ∨ nextLPtr + ecNext * L ≤ curBatch + t) :=
    fun hlt => by
      obtain ⟨hNLV, hGE, hIns, hAgree⟩ := hNext hlt
      obtain ⟨hNLle, hNLdisjL, hNLoff, hCF, hCG, hCU, hBNL⟩ := hNextOff hlt
      refine ⟨by omega, hCF, (hfr1 _ (by omega) hCF hCG hCU).trans (hNLCell hlt),
        EdgeValuesAt.congr hNLV fun e he i hi => ?_, hGE, hIns, hAgree, ?_, hNLle, hNLdisjL,
        fun x hx1 hx2 => (hNLoff x hx1 hx2).1, hBNL⟩
      · have := branchBEntry_lt (hGE e he) hi
        obtain ⟨h0, hg, hu⟩ := hNLoff (nextLPtr + e * L + i) (by omega) (by omega)
        exact hfr1 _ (by omega) h0 hg hu
      · intro e _ hex
        obtain ⟨u, hu, hins⟩ := hex
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hu
        exact ⟨j, hj, hins⟩
  have hUlen : 2 * curU.length ≤ curBatchWords := by
    have := batchBodyAt_length_le hSmall.1.2.2
    have := hSmall.1.1
    omega
  -- the tail
  obtain ⟨s2, cT, tokF, c, rT, h4lo, h4hi, hregT, hrep2, hfootF, hz2, hfr2, hlen2, hex, hcw,
      hLvl, hcT⟩ :=
    wireBranchBStepTailKFBL_runs (ω := ω) (s := s1) (tok0 := coreTok0) (a := aNext)
      (G0 := ch.G idx) (U := curU) (GS := cfg.T.S (ch.scState idx) (ch.bran idx)) (US := nextU)
      (oldLsf := cfg.T.lsfs (ch.scState idx)) (oldNextℓ := oldNextℓ) (ℓi := ℓi)
      hCoreLocal hFour hPrec hw16 hFootAt hCopy hSlotP hColl hUpdLen hEdgeProc hSign hMul hDiv
      hCopyW ⟨hr2H, hr3H, h4H, hr6H, hr7H, hr10H, hr23H, hr24H, hr25H,
        (hreg70 72 (by omega)).trans hr72, (hreg70 75 (by omega)).trans hr75,
        (hreg70 76 (by omega)).trans hr76, (hreg70 83 (by omega)).trans hr83,
        (hreg70 94 (by omega)).trans hr94, (hreg70 96 (by omega)).trans hr96⟩
      hIdx hdW hBrLt hkW hCoreH_W hF1 hR1 hRlo1 hRhi1 hH1lo hG1 hGLe hrep1 hIn1 hfoot1 hFoot hz1
      hUS1 (fun t ht => (hUSW1 t ht).1) hUSlo hUShi (fun t ht => (hUSW1 t ht).2) hU1 hUW1 hBLe
      hDisjB hLen1 hLenCap hLLe (fun x hx1 hx2 => (hLenOff x hx1 hx2).1) hNext1 hSlotLe
      (fun i hi => ⟨(hSlotOff i hi).1, (hSlotOff i hi).2.1, (hSlotOff i hi).2.2.1⟩) (by omega)
  generalize hslot : selBase + 1 + 12 * idx = slot at hSlotLe hSlotOff hfr2 hLvl ⊢
  set base := curHeap + 1 + 4 * ch.bran idx with hbase
  -- what the tail keeps
  have hnf1 : ∀ x, x < curHeap → ¬ Rcore.foot coreH coreTok0 x → ¬ Rcore.foot coreH tok1 x :=
    fun x hx hn hf => by
      rcases hfoot1 x hf with h | h
      · exact hn h
      · omega
  have hHi : ∀ x, curHeap ≤ x → x < h1 → ¬ Rcore.foot coreH tok1 x → s2.mem x = s1.mem x :=
    fun x hx1 hx2 hn => hfr2 x hx2 hn (fun hlt => Or.inr (by have := (hNextOff hlt).1; omega))
      (Or.inr (by omega))
  have hoffF : ∀ x, x < h1 → ¬ Rcore.foot coreH tok1 x → ¬ Rcore.foot coreH tokF x :=
    fun x hx hn hf => by
      rcases hfootF x hf with h | h
      · exact hn h
      · omega
  have hG2 : DynGraphAt s2.mem gPtr vCap eCap curG :=
    dynGraphAt_of_agree hG1 fun x hx1 hx2 => by
      refine hfr2 x (by omega) (hnf1 x (by omega) (hDisjG x hx1 hx2).1) (fun hlt => ?_) ?_
      · by_contra hc
        have := ((hNextOff hlt).2.2.1 x (by omega) (by omega)).2.1
        omega
      · by_contra hc
        have := (hSlotOff (x - slot) (by omega)).2.2.2.1
        omega
  have hUC2 : s2.mem (updCountBase + idx) = ch.updCount idx + curU.length := by
    refine (hfr2 _ (by omega) (hnf1 _ hUCLt hUCFoot) (fun hlt => ?_) ?_).trans hUC1
    · by_contra hc
      exact ((hNextOff hlt).2.2.1 (updCountBase + idx) (by omega) (by omega)).2.2 rfl
    · by_contra hc
      have := (hSlotOff (updCountBase + idx - slot) (by omega)).2.2.2.2
      omega
  have hUS2 : SmallBatchAt s2.mem (s1.mem base) (cfg.T.S (ch.scState idx) (ch.bran idx)) nextU
      (s1.mem (base + 1)) :=
    smallBatchAt_of_agree hUS1 fun x hx1 hx2 => hHi x (by omega) (by omega) (by
      have := (hUSW1 (x - s1.mem base) (by omega)).2
      rwa [show s1.mem base + (x - s1.mem base) = x by omega] at this)
  have hDec2 : (decodeBatch s2.mem (s1.mem base) (cfg.T.S (ch.scState idx) (ch.bran idx))).1 =
      nextU :=
    decodeBatch_of_agree hUS1.1 hDec1 fun t ht =>
      hHi _ (by omega) (by omega) (hUSW1 t ht).2
  have hEd2 : OrdEditsAt s2.mem (s1.mem (base + 2)) nextEdits (s1.mem (base + 3)) :=
    ordEditsAt_of_agree hEd1 fun x hx1 hx2 => hHi x (by omega) (by omega) (by
      have := (hEdW1 (x - s1.mem (base + 2)) (by omega)).2
      rwa [show s1.mem (base + 2) + (x - s1.mem (base + 2)) = x by omega] at this)
  have hUSW2 : ∀ t < s1.mem (base + 1), s2.mem (s1.mem base + t) < 2 ^ w ∧
      ¬ Rcore.foot coreH tokF (s1.mem base + t) := fun t ht => by
    rw [hHi _ (by omega) (by omega) (hUSW1 t ht).2]
    exact ⟨(hUSW1 t ht).1, hoffF _ (by omega) (hUSW1 t ht).2⟩
  have hEdW2 : ∀ t < s1.mem (base + 3), s2.mem (s1.mem (base + 2) + t) < 2 ^ w ∧
      ¬ Rcore.foot coreH tokF (s1.mem (base + 2) + t) := fun t ht => by
    rw [hHi _ (by omega) (by omega) (hEdW1 t ht).2]
    exact ⟨(hEdW1 t ht).1, hoffF _ (by omega) (hEdW1 t ht).2⟩
  have e10 : s2.regs 10 = s1.mem base := (hregT 10 (by omega)).trans hr10H
  have e11 : s2.regs 11 = s1.mem (base + 1) := (hregT 11 (by omega)).trans hr11H
  have e12 : s2.regs 12 = s1.mem (base + 2) := (hregT 12 (by omega)).trans hr12H
  have e13 : s2.regs 13 = s1.mem (base + 3) := (hregT 13 (by omega)).trans hr13H
  have hcost := step_cost_arith hcH hcT hUlen
  have hrun : Runs w p ω (wireBranchBStepKFBL (opCore 0) (opCore 2) dgApply copyProc updLen
      slotProc) st .normal s2 (cH + cT + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, cH, cT, rH, rT, rfl⟩)
  refine ⟨s2, cH + cT + 1, tokF, nextEdits, c, ?_⟩
  rw [e10, e11, e12, e13]
  exact ⟨hrun, by omega, by omega, hz2, fun r hr => (hregT r (by omega)).trans (hreg70 r hr),
    hrep2, hIn1,
    fun x hx => by
      rcases hfootF x hx with h | h
      · rcases hfoot1 x h with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h'.1, by omega⟩
      · exact Or.inr ⟨by omega, h.2⟩,
    hG2, hUC2, hUS2, hDec2, hEd2, hEdRot, hEdFor, hEdValid, hUSlo, by omega, hEdlo, by omega,
    hUSW2, hEdW2, hEdB, hlen2,
    fun x hx h0 hg hu hn hs => step_frame hfr1 hfr2 hfoot1 hH1lo hx h0 hg hu hn hs,
    hex, hcw,
    SelOutLevelMemAt.transfer hLvl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun x _ _ h => h.imp (fun h' => ⟨by omega, h'.2⟩) id)
      (fun x h => h.imp id fun h' => ⟨by omega, h'.2⟩) le_rfl le_rfl,
    hcost⟩

end MinCostFlow.MinRatio
