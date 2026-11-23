module

public import MinCostFlow.MinRatio.WireChainCoreBranchBTailFrontKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBSlotCallKFBL
public import MinCostFlow.MinRatio.WireChainCoreSelOutLevelAtKFBL
import MinCostFlow.SparseCore.Program.AssemblyReemb
import WordRAM.Tactic

/-!
# The second half of a Branch B level step under `KFBL` (`WireChainCoreBranchBTailKFBL`)

After the head of a level step (`wireBranchBStepHeadKFBL`: op `0`, the level graph, the update
counter and the forwarded batch), the chain-update core makes the outputs that the select part of
`Update` reads at this level, and the lengths of the next level. The first three parts
(`wireBranchBStepTailFrontKFBL`: the copies of the two lists, op `2` with the descriptor copy, and
the next lengths) are in `WireChainCoreBranchBTailFrontKFBL.lean`. The last part fills the slot of
the level (`wireBranchBSlotStmt`).

This file gives the whole second half, `wireBranchBStepTailKFBL`, and its run lemma
`wireBranchBStepTailKFBL_runs`. The slot writer writes only the twelve slot words and fresh heap
above the pointer that the first three parts leave. So every fact of the first three parts that
the select part needs stays: the copies and the descriptor are in fresh heap off the footprint,
the stretch rows are in the footprint or in the op-`2` output, and the batch of the level is off
the slot. The level clause comes out as `SelOutLevelMemAt` at the final memory.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- The part of a non-rebuild level step after its head: copy the two lists, call op `2` and copy
its descriptor, write the core lengths of the next level, and fill the slot of the level. -/
@[expose] def wireBranchBStepTailKFBL (copyProc readLSF updLen slotProc : ℕ) : Stmt :=
  wireBranchBStepTailFrontKFBL copyProc readLSF updLen ;;
  wireBranchBSlotStmt slotProc

theorem wireBranchBStepTailKFBL_noRand (copyProc readLSF updLen slotProc : ℕ) :
    (wireBranchBStepTailKFBL copyProc readLSF updLen slotProc).NoRand := by
  simp only [wireBranchBStepTailKFBL, Stmt.NoRand, wireBranchBStepTailFrontKFBL_noRand,
    wireBranchBSlotStmt_noRand, and_self]

private theorem tail_cost_arith {c3 c4 phiY phi1 A Ro C U US : ℕ}
    (h3 : c3 + phiY ≤ A + Ro + US * (C + 60) + 320 + phi1) (h4 : c4 ≤ 60 * (U + US) + 340) :
    c3 + c4 + 1 + phiY ≤ A + Ro + US * (C + 120) + 60 * U + 700 + phi1 := by
  have : US * (C + 120) = US * (C + 60) + 60 * US := by ring
  omega

set_option maxHeartbeats 1600000 in
/-- One run of the tail of a non-rebuild level step, from the state that the head leaves. The head
left the change records and the re-embedding list of the active branch `b` in its output
`[curHeap, h1)`, the forwarded batch `US` there off the footprint, and the core of the level at the
token `tok1`, whose footprint lies in the old one `tok0` and in `[curHeap, h1)`. The tail:
* keeps the core at the new token `tokF`, whose footprint grows only into `[h1, out.regs 4)`;
* writes the core lengths of the next level when `idx + 1 < d`;
* changes no word below `h1` outside the footprint, that length vector and the slot;
* leaves the memory clauses of the level (`SelOutLevelMemAt`), with every word of the copies, the
  descriptor and the touched-edge lists in `[h1, out.regs 4)` off the footprint, the batch at
  `curBatch`, and every stretch row in the footprint or in `[h1, out.regs 4)`;
* costs `20` per copied entry, one readout, a constant per entry of the two batches, and a
  constant. -/
theorem wireBranchBStepTailKFBL_runs
    {w L P depth k M N vCap eCap capExp copyProc updLen slotProc collectProc edgeProc signExt mul
      intDiv copy idx d b coreH gPtr lPtr nextLPtr levelMeta selBase curHeap h1 curBatch
      curBatchWords nextB nextBW ecNext : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {Ginit : MGraph}
    {Psc : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ} {Rcore : DSRep (SparseCoreOrdAbs tool)}
    {p : Program} {opCore : ℕ → ℕ} {ω : ℕ → Bool} {s : State}
    {a : SparseCoreOrdAbs tool} {tok0 tok1 : Rcore.τ} {G0 GS : MGraph} {U US : List Update}
    {oldLsf : ℕ → LSF} {reemb : List ℕ} {ℓi oldNextℓ : ℕ → ℝ}
    (hLocal : Rcore.Local) (hFour : fmt.limbBits = 4) (hPrec : fmt.precision = P)
    (hw16 : 16 ≤ 2 ^ w)
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool Ginit k M N vCap eCap capExp Psc alloc
      Rcore p opCore)
    (hCopy : p.procs[copyProc]? = some wireRawCopyBody)
    (hSlotP : p.procs[slotProc]? = some (wireSelOutSlotBody collectProc))
    (hColl : p.procs[collectProc]? = some wireCollectTouchedEdgesBody)
    (hUpdLen : p.procs[updLen]? = some (wireUpdateCoreLenFromBatchBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopyW : MeetsContract w p copy (copyWordsContract w))
    (hRegs : s.regs 2 = b ∧ s.regs 3 = coreH ∧ s.regs 4 = h1 ∧ s.regs 6 = gPtr ∧
      s.regs 7 = lPtr ∧ s.regs 10 = nextB ∧ s.regs 23 = curBatch ∧ s.regs 24 = curBatchWords ∧
      s.regs 25 = curHeap ∧ s.regs 72 = selBase ∧ s.regs 75 = d ∧ s.regs 76 = k ∧
      s.regs 83 = levelMeta ∧ s.regs 94 = L ∧ s.regs 96 = idx)
    (hIdx : idx < d) (hdW : d < 2 ^ w) (hb : b < k) (hkW : k < 2 ^ w) (hCoreHW : coreH < 2 ^ w)
    (hF : BranchOutFChgAt w s.mem curHeap h1 k oldLsf (tool.lsfs a.st))
    (hR : ReembListAt s.mem (s.mem (curHeap + 1 + 4 * k + 2 * b))
      (s.mem (curHeap + 2 + 4 * k + 2 * b)) reemb)
    (hRlo : curHeap ≤ s.mem (curHeap + 1 + 4 * k + 2 * b))
    (hRhi : s.mem (curHeap + 1 + 4 * k + 2 * b) + s.mem (curHeap + 2 + 4 * k + 2 * b) ≤ h1)
    (hH1 : curHeap ≤ h1)
    (hGAt : DynGraphAt s.mem gPtr vCap eCap a.G) (hGLe : gPtr + dynGraphSize vCap eCap ≤ curHeap)
    (hRep : Rcore.rep coreH a tok1 s.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hFoot1 : ∀ x, Rcore.foot coreH tok1 x → Rcore.foot coreH tok0 x ∨ (curHeap ≤ x ∧ x < h1))
    (hFoot0 : ∀ x, Rcore.foot coreH tok0 x → x < curHeap)
    (hz : ZeroFrom s.mem h1)
    (hUS : SmallBatchAt s.mem nextB GS US nextBW)
    (hUSW : ∀ t < nextBW, s.mem (nextB + t) < 2 ^ w)
    (hUSLo : curHeap ≤ nextB) (hUSHi : nextB + nextBW ≤ h1)
    (hUSOff : ∀ t < nextBW, ¬ Rcore.foot coreH tok1 (nextB + t))
    (hU : SmallBatchAt s.mem curBatch G0 U curBatchWords)
    (hUW : ∀ t < curBatchWords, s.mem (curBatch + t) < 2 ^ w)
    (hULe : curBatch + curBatchWords ≤ curHeap)
    (hUOff : ∀ t < curBatchWords, ¬ Rcore.foot coreH tok0 (curBatch + t))
    (hPrevLen : EdgeValuesAt s.mem lPtr 4 L P a.G.E ℓi)
    (hPrevCap : ∀ e ∈ a.G.E, e < eCap)
    (hPrevLe : lPtr + eCap * L ≤ curHeap)
    (hPrevOff : ∀ x, lPtr ≤ x → x < lPtr + eCap * L → ¬ Rcore.foot coreH tok0 x)
    (hNext : idx + 1 < d →
      levelMeta + (idx + 1) < curHeap ∧ ¬ Rcore.foot coreH tok0 (levelMeta + (idx + 1)) ∧
      s.mem (levelMeta + (idx + 1)) = nextLPtr ∧
      EdgeValuesAt s.mem nextLPtr 4 L P GS.E oldNextℓ ∧
      (∀ e ∈ GS.E, e < ecNext) ∧
      (∀ u ∈ US, match u with
        | .insert e _ _ => e ∈ a.G.E ∧ e < eCap ∧ e < ecNext ∧
            (∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P = coreLen (tool.lsfs a.st b) ℓi e)
        | _ => True) ∧
      (∀ e ∈ (GS.applyBatch US).E, (¬ ∃ u ∈ US, u.Inserts e) →
        e ∈ GS.E ∧ oldNextℓ e = coreLen (tool.lsfs a.st b) ℓi e) ∧
      (∀ e ∈ (GS.applyBatch US).E, (∃ u ∈ US, u.Inserts e) →
        ∃ j, ∃ hj : j < US.length, US[j].Inserts e) ∧
      nextLPtr + ecNext * L ≤ curHeap ∧
      (lPtr + eCap * L ≤ nextLPtr ∨ nextLPtr + ecNext * L ≤ lPtr) ∧
      (∀ x, nextLPtr ≤ x → x < nextLPtr + ecNext * L → ¬ Rcore.foot coreH tok0 x) ∧
      (∀ t < curBatchWords, curBatch + t < nextLPtr ∨ nextLPtr + ecNext * L ≤ curBatch + t))
    (hSlot : selBase + 1 + 12 * idx + 12 ≤ curHeap)
    (hSlotOff : ∀ i < 12, ¬ Rcore.foot coreH tok0 (selBase + 1 + 12 * idx + i) ∧
      (selBase + 1 + 12 * idx + i < curBatch ∨
        curBatch + curBatchWords ≤ selBase + 1 + 12 * idx + i) ∧
      (idx + 1 < d → selBase + 1 + 12 * idx + i < nextLPtr ∨
        nextLPtr + ecNext * L ≤ selBase + 1 + 12 * idx + i))
    (hRoom : h1 + 2 * (h1 - curHeap) + 7 +
      US.length * wireCoreLenEdgeSpace (ordLevelLwMax L capExp M N) + U.length + US.length <
        2 ^ w) :
    ∃ (out : State) (cost : ℕ) (tokF : Rcore.τ) (c : Read.LSFChange),
      Runs w p ω (wireBranchBStepTailKFBL copyProc (opCore 2) updLen slotProc) s .normal out cost ∧
      h1 ≤ out.regs 4 ∧ out.regs 4 ≤ h1 + 2 * (h1 - curHeap) + 7 +
        US.length * wireCoreLenEdgeSpace (ordLevelLwMax L capExp M N) + U.length + US.length ∧
      (∀ r, (r < 18 ∧ r ≠ 4 ∧ r ≠ 5) ∨ (23 ≤ r ∧ r ≤ 25) ∨ 33 < r → out.regs r = s.regs r) ∧
      Rcore.rep coreH a tokF out.mem ∧
      (∀ x, Rcore.foot coreH tokF x → Rcore.foot coreH tok1 x ∨ (h1 ≤ x ∧ x < out.regs 4)) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ x < h1, ¬ Rcore.foot coreH tok1 x →
        (idx + 1 < d → x < nextLPtr ∨ nextLPtr + ecNext * L ≤ x) →
        (x < selBase + 1 + 12 * idx ∨ selBase + 1 + 12 * idx + 12 ≤ x) → out.mem x = s.mem x) ∧
      (idx + 1 < d → EdgeValuesAt out.mem nextLPtr 4 L P (GS.applyBatch US).E
        (coreLen (tool.lsfs a.st b) ℓi)) ∧
      c.Exact (oldLsf b) (tool.lsfs a.st b) ∧ (∀ e ∈ c.fDel, e < 2 ^ w) ∧
      SelOutLevelMemAt w P (ordLevelLwMax L capExp M N)
        (fun x => (h1 ≤ x ∧ ¬ Rcore.foot coreH tokF x) ∨
          (curBatch ≤ x ∧ x < curBatch + curBatchWords))
        (fun x => Rcore.foot coreH tokF x ∨ (h1 ≤ x ∧ x < out.regs 4))
        curBatch (out.regs 4) out.mem (selBase + 1 + 12 * idx)
        ⟨coreBatchTouchedEdges U, c.fDel, coreBatchTouchedEdges US, reemb⟩ G0 U a.G.E
        (tool.lsfs a.st b).wstr ∧
      cost + Rcore.phi coreH tokF out.mem ≤ 20 * (c.fDel.length + reemb.length) + Psc.readout +
        US.length * (wireCoreLenEdgeCost (ordLevelLwMax L capExp M N) + 120) +
        60 * U.length + 700 + Rcore.phi coreH tok1 s.mem := by
  obtain ⟨hr2, hr3, hr4, hr6, hr7, hr10, hr23, hr24, hr25, hr72, hr75, hr76, hr83, hr94, hr96⟩ :=
    hRegs
  -- the copies, op `2` and the next lengths
  obtain ⟨s3, c3, ret, Lw, y, c, r3, hex, hcw, hFL, hRL, hret, h4lo, h4hi, h26, h27, h28, h29, h31,
      h32, hreg3, hrep3, hfootY, hz3, hfr3, hLF, hLR, hLw, hSV, hT0, hT1, hU3, hUW3, hUS3, hUSW3,
      hlen3, hc3⟩ :=
    wireBranchBStepTailFrontKFBL_runs (ω := ω) hLocal hFour hPrec hw16 hFootAt hCopy hUpdLen hEdgeProc hSign
      hMul hDiv hCopyW ⟨hr2, hr3, hr4, hr6, hr7, hr10, hr23, hr24, hr25, hr75, hr76, hr83, hr94,
        hr96⟩ hIdx hdW hb hkW hCoreHW hF hR hRlo hRhi hH1 hGAt hGLe hRep hIn hFoot1 hFoot0 hz hUS
      hUSW hUSLo hUSHi hUSOff hU hUW hULe hUOff hPrevLen hPrevCap hPrevLe hPrevOff hNext
      (by omega)
  clear hF hR hRlo hRhi hGAt hGLe hRep hIn hz hUS hUSW hUSOff hU hUW hUOff hPrevLen hPrevCap
    hPrevLe hPrevOff hFootAt hCopy hUpdLen hEdgeProc hSign hMul hDiv hCopyW
  generalize hLwMaxDef : ordLevelLwMax L capExp M N = LwMax at hRoom h4hi hLw hc3 ⊢
  set cur := h1 + c.fDel.length + reemb.length with hcur
  -- the slot
  obtain ⟨s4, c4, r4, h4d, hreg4, hpost4, hc4⟩ :=
    wireBranchBSlotStmt_runs (w := w) (ω := ω) (s := s3) (by omega) hSlotP hColl
      ⟨(hreg3 72 (by omega)).trans hr72, (hreg3 96 (by omega)).trans hr96, rfl, h26, h27, h28, h29,
        h31, h32, (hreg3 23 (by omega)).trans hr23, (hreg3 24 (by omega)).trans hr24,
        (hreg3 10 (by omega)).trans hr10⟩
      hU3 hUW3 (by omega) hUS3 hUSW3 (by omega) (by omega) hz3 (by omega)
  generalize hslot : selBase + 1 + 12 * idx = slot at hSlot hSlotOff hpost4 ⊢
  clear hSlotP hColl hRoom hr2 hr3 hr4 hr6 hr7 hr10 hr23 hr24 hr25 hr72 hr75 hr76 hr83 hr94 hr96
    h26 h27 h28 h29 h31 h32 hdW hkW hCoreHW hb hw16
  have hTU := coreBatchTouchedEdges_length_le U
  have hTS := coreBatchTouchedEdges_length_le US
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hLG, hLS, hlo4, hz4⟩ :=
    hpost4
  have hfoot1lt : ∀ x, Rcore.foot coreH tok1 x → x < h1 := fun x hx => by
    rcases hFoot1 x hx with h | h
    · have := hFoot0 x h; omega
    · omega
  have hNotSlot0 : ∀ x, Rcore.foot coreH tok0 x → x < slot ∨ slot + 12 ≤ x := fun x hx => by
    by_contra hc
    have := (hSlotOff (x - slot) (by omega)).1
    rw [show slot + (x - slot) = x by omega] at this
    exact this hx
  have hHi : ∀ x, curHeap ≤ x → x < cur + 7 → s4.mem x = s3.mem x := fun x hx1 hx2 =>
    hlo4 x (by omega) (Or.inr (by omega))
  have hYmem : ∀ x, Rcore.foot coreH y x ∨ (cur ≤ x ∧ x < ret) → s4.mem x = s3.mem x := by
    intro x hx
    rcases hx with hf | hf
    · rcases hfootY x hf with h | h
      · rcases hFoot1 x h with h' | h'
        · exact hlo4 x (by have := hFoot0 x h'; omega) (hNotSlot0 x h')
        · exact hHi x (by omega) (by omega)
      · exact hHi x (by omega) (by omega)
    · exact hHi x (by omega) (by omega)
  have hoffY : ∀ x, h1 ≤ x → x < cur ∨ cur + 5 ≤ x → ¬ Rcore.foot coreH y x := fun x hx1 hx2 hf => by
    rcases hfootY x hf with h | h
    · have := hfoot1lt x h; omega
    · omega
  have hLoc4 := hLocal coreH a y s3.mem s4.mem fun x hx => (hYmem x (Or.inl hx)).symm
  have hL1 : ∀ t, h1 ≤ t → t < cur → s4.mem t = s3.mem t := fun t ht1 ht2 =>
    hHi t (by omega) (by omega)
  have hd5 : s4.mem (cur + 5) = s3.mem (cur + 5) := hHi _ (by omega) (by omega)
  have hd6 : s4.mem (cur + 5 + 1) = s3.mem (cur + 5 + 1) := hHi _ (by omega) (by omega)
  have hcost : c3 + c4 + 1 + Rcore.phi coreH y s4.mem ≤
      20 * (c.fDel.length + reemb.length) + Psc.readout +
        US.length * (wireCoreLenEdgeCost LwMax + 120) + 60 * U.length + 700 +
        Rcore.phi coreH tok1 s.mem := by
    rw [← hLoc4.2]
    exact tail_cost_arith hc3 hc4
  have hregF : ∀ r, (r < 18 ∧ r ≠ 4 ∧ r ≠ 5) ∨ (23 ≤ r ∧ r ≤ 25) ∨ 33 < r →
      s4.regs r = s.regs r := fun r hr => by
    rw [hreg4 r (by omega) (by omega)]; exact hreg3 r hr
  have hout1 : h1 ≤ s4.regs 4 := by omega
  have hout2 : s4.regs 4 ≤ h1 + 2 * (h1 - curHeap) + 7 +
      US.length * wireCoreLenEdgeSpace LwMax + U.length + US.length := by omega
  have hrun : Runs w p ω (wireBranchBStepTailKFBL copyProc (opCore 2) updLen slotProc) s .normal s4
      (c3 + c4 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s3, c3, c4, r3, r4, rfl⟩)
  generalize c3 + c4 + 1 = cT at hcost hrun
  clear hc3 hc4 hreg3 hreg4 hLwMaxDef hslot r3 r4
  refine ⟨s4, cT, y, c, hrun, hout1, hout2, hregF, hLoc4.1 hrep3,
    fun x hx => (hfootY x hx).imp id fun h => ⟨by omega, by omega⟩,
    by rw [h4d]; exact hz4,
    fun x hx hn hNL hs => by rw [hlo4 x (by omega) hs]; exact hfr3 x hx hn hNL,
    fun hlt => ?_, hex, hcw, ?_, hcost⟩
  · have hEl := branchBNextEdge_lt (hNext hlt).2.2.2.2.1 (hNext hlt).2.2.2.2.2.1
      (hNext hlt).2.2.2.2.2.2.1 (hNext hlt).2.2.2.2.2.2.2.1
    have hNLend := (hNext hlt).2.2.2.2.2.2.2.2.1
    exact EdgeValuesAt.congr (hlen3 hlt) fun e he i hi => by
      have := branchBEntry_lt (hEl e he) hi
      refine hlo4 _ (by omega) ?_
      by_contra hc
      have := (hSlotOff (nextLPtr + e * L + i - slot) (by omega)).2.2 hlt
      omega
  · refine selOutLevelMemAt_of_slotPost
      ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hLG, hLS, hlo4, hz4⟩
      ⟨by omega, by omega, fun t ht => Or.inl ⟨by omega, hoffY _ (by omega) (Or.inr (by omega))⟩⟩
      (fun i hi => by rw [hL1 (h1 + i) (by omega) (by omega)]; exact hLF i hi)
      ⟨by omega, by omega, fun t ht => Or.inl ⟨by omega, hoffY _ (by omega) (Or.inl (by omega))⟩⟩
      ⟨rfl, fun i hi => by
        rw [hL1 (h1 + c.fDel.length + i) (by omega) (by omega)]; exact hLR i hi⟩
      ⟨by omega, by omega, fun t ht => Or.inl ⟨by omega, hoffY _ (by omega) (Or.inl (by omega))⟩⟩
      (smallBatchAt_of_agree hU3 fun x hx1 hx2 => hlo4 x (by omega)
        (by
          by_contra hc
          have := (hSlotOff (x - slot) (by omega)).2.1
          omega))
      (fun t ht => by
        rw [hlo4 _ (by omega) (by
          by_contra hc
          have := (hSlotOff (curBatch + t - slot) (by omega)).2.1
          omega)]
        exact hUW3 t ht)
      ⟨le_rfl, by omega, fun t ht => Or.inr ⟨by omega, by omega⟩⟩
      ⟨by omega, by omega, fun t ht => Or.inl ⟨by omega, hoffY _ (by omega) (Or.inr (by omega))⟩⟩
      hLw ?_ ?_ ?_
    · exact stretchValuesAt_of_moved hSV (fun _ => ⟨hd5, hd6⟩)
        (fun e he t ht => hYmem _ ((hT0.2 e he).2 t ht))
        (fun e he t ht => hYmem _ ((hT1.2 e he).2 t ht))
    · refine ⟨by rw [hd5]; exact hT0.1, fun e he => ?_⟩
      rw [hd5]
      refine ⟨by have := (hT0.2 e he).1; omega, fun t ht => ?_⟩
      rcases (hT0.2 e he).2 t ht with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, by omega⟩
    · refine ⟨by rw [hd6]; exact hT1.1, fun e he => ?_⟩
      rw [hd6]
      refine ⟨by have := (hT1.2 e he).1; omega, fun t ht => ?_⟩
      rcases (hT1.2 e he).2 t ht with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by omega, by omega⟩

end MinCostFlow.MinRatio
