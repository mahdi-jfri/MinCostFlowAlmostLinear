module

public import MinCostFlow.MinRatio.WireChainCoreBranchBCopyKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBDescKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBNextLenKFBL
import MinCostFlow.SparseCore.Program.AssemblyReemb
import MinCostFlow.MinRatio.WireSelectEvalKeyMath
import WordRAM.Tactic

/-!
# Copies, op `2` and next lengths in a Branch B level step (`WireChainCoreBranchBTailFrontKFBL`)

After the head of a level step (`wireBranchBStepHeadKFBL`: op `0`, the level graph, the update
counter and the forwarded batch), the chain-update core makes the outputs that the select part of
`Update` reads at this level, and the lengths of the next level. This file does the first three
parts of that work:
1. it copies the `fDel` list of the active branch and its re-embedding list to the first free word
   (`wireBranchBCopyListsStmt`);
2. it calls op `2` and copies the stretch descriptor (`wireBranchBReadDescStmt`);
3. when the level is not the last one, it writes the core lengths of the next level
   (`wireBranchBNextLenStmt`).

The run lemma `wireBranchBStepTailFrontKFBL_runs` composes the three run lemmas. Each part writes
only fresh heap, the core footprint (op `2`) and the length vector of the next level (part 3). So
the copies and the descriptor stay where part 1 and part 2 put them, the stretch rows stay in the
footprint or in the op-`2` output, and the two batches stay. The slot of the level comes next, in
`WireChainCoreBranchBTailKFBL.lean`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- The first three parts of a non-rebuild level step after its head: copy the two lists, call
op `2` and copy its descriptor, and write the core lengths of the next level. -/
@[expose] def wireBranchBStepTailFrontKFBL (copyProc readLSF updLen : ℕ) : Stmt :=
  wireBranchBCopyListsStmt copyProc ;;
  wireBranchBReadDescStmt readLSF ;;
  wireBranchBNextLenStmt updLen

theorem wireBranchBStepTailFrontKFBL_noRand (copyProc readLSF updLen : ℕ) :
    (wireBranchBStepTailFrontKFBL copyProc readLSF updLen).NoRand := by
  simp only [wireBranchBStepTailFrontKFBL, Stmt.NoRand, wireBranchBCopyListsStmt_noRand,
    wireBranchBReadDescStmt_noRand, wireBranchBNextLenStmt_noRand, and_self]

private theorem coreLenEdgeSpace_mono' {K₁ K₂ : ℕ} (h : K₁ ≤ K₂) :
    wireCoreLenEdgeSpace K₁ ≤ wireCoreLenEdgeSpace K₂ := by
  unfold wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
  have hmul : (2 * K₁) * (2 * K₁ + 1) ≤ (2 * K₂) * (2 * K₂ + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

private theorem coreLenEdgeCost_mono' {K₁ K₂ : ℕ} (h : K₁ ≤ K₂) :
    wireCoreLenEdgeCost K₁ ≤ wireCoreLenEdgeCost K₂ := by
  unfold wireCoreLenEdgeCost
  have hsq : K₁ ^ 2 ≤ K₂ ^ 2 := Nat.pow_le_pow_left h 2
  omega

/-- Every edge of the next level after the forwarded batch is below `ecNext`: an edge that the batch
does not insert was in the old graph, and an inserted edge is below `ecNext` by the insert facts. -/
theorem branchBNextEdge_lt {GS : MGraph} {US : List Update} {ecNext eCap L P : ℕ}
    {E : Finset ℕ} {forest : LSF} {ℓi oldNextℓ : ℕ → ℝ}
    (hGE : ∀ e ∈ GS.E, e < ecNext)
    (hInsInfo : ∀ u ∈ US, match u with
      | .insert e _ _ => e ∈ E ∧ e < eCap ∧ e < ecNext ∧
          (∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P = coreLen forest ℓi e)
      | _ => True)
    (hAgreeOld : ∀ e ∈ (GS.applyBatch US).E, (¬ ∃ u ∈ US, u.Inserts e) →
      e ∈ GS.E ∧ oldNextℓ e = coreLen forest ℓi e)
    (hMemIns : ∀ e ∈ (GS.applyBatch US).E, (∃ u ∈ US, u.Inserts e) →
      ∃ j, ∃ hj : j < US.length, US[j].Inserts e) :
    ∀ e ∈ (GS.applyBatch US).E, e < ecNext := by
  intro e he
  by_cases hins : ∃ u ∈ US, u.Inserts e
  · obtain ⟨j, hj, hjIns⟩ := hMemIns e he hins
    have hmem : US[j] ∈ US := List.getElem_mem hj
    have hi := hInsInfo _ hmem
    revert hi hjIns
    cases US[j] with
    | insert e' x y => intro hjIns hi; simp only [Update.Inserts] at hjIns; subst hjIns; exact hi.2.2.1
    | delete _ => intro hjIns; exact hjIns.elim
    | split _ _ _ _ => intro hjIns; exact hjIns.elim
  · exact hGE e (hAgreeOld e he hins).1

/-- Word `i` of entry `e` of a table with `L` words per entry and `cap` entries lies in the table. -/
theorem branchBEntry_lt {e cap L i : ℕ} (he : e < cap) (hi : i < L) : e * L + i < cap * L := by
  have : (e + 1) * L ≤ cap * L := Nat.mul_le_mul_right L he
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

/-- The length part of the tail in both cases: at a level below `d - 1` it writes the core lengths
of the next level, and at the last level it does nothing. -/
private theorem nextLen_runs_either
    {w updLen edgeProc signExt mul intDiv copy idx d levelMeta batchPtr stretchDesc prevLenPtr
      curLenPtr L Lw LwMax P ecPrev ecCur totalWords heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {s : State} {G : MGraph} {U : List Update}
    {forest : LSF} {prevℓ oldCurℓ : ℕ → ℝ} {prevE : Finset ℕ}
    (hUpdLen : p.procs[updLen]? = some (wireUpdateCoreLenFromBatchBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hRegs : s.regs 96 = idx ∧ s.regs 75 = d ∧ s.regs 83 = levelMeta ∧ s.regs 10 = batchPtr ∧
      s.regs 31 = stretchDesc ∧ s.regs 7 = prevLenPtr ∧ s.regs 94 = L ∧ s.regs 32 = Lw ∧
      s.regs 4 = heap)
    (hIdx : idx < d) (hdW : d < 2 ^ w) (hLw : max L Lw ≤ LwMax)
    (hNext : idx + 1 < d →
      levelMeta + (idx + 1) < 2 ^ w ∧ s.mem (levelMeta + (idx + 1)) = curLenPtr ∧
      SmallBatchAt s.mem batchPtr G U totalWords ∧ (∀ j < totalWords, s.mem (batchPtr + j) < 2 ^ w) ∧
      StretchValuesAt s.mem stretchDesc 4 Lw P prevE forest.wstr ∧
      EdgeValuesAt s.mem prevLenPtr 4 L P prevE prevℓ ∧
      EdgeValuesAt s.mem curLenPtr 4 L P G.E oldCurℓ ∧
      (∀ e ∈ G.E, e < ecCur) ∧
      (∀ u ∈ U, match u with
        | .insert e _ _ => e ∈ prevE ∧ e < ecPrev ∧ e < ecCur ∧
            (∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P = coreLen forest prevℓ e)
        | _ => True) ∧
      (∀ e ∈ (G.applyBatch U).E, (¬ ∃ u ∈ U, u.Inserts e) →
        e ∈ G.E ∧ oldCurℓ e = coreLen forest prevℓ e) ∧
      (∀ e ∈ (G.applyBatch U).E, (∃ u ∈ U, u.Inserts e) →
        ∃ k, ∃ hk : k < U.length, U[k].Inserts e) ∧
      batchPtr + totalWords ≤ heap ∧ stretchDesc + 2 ≤ heap ∧
      (∀ e ∈ prevE, s.mem stretchDesc + e * Lw + Lw ≤ heap ∧
        s.mem (stretchDesc + 1) + e * Lw + Lw ≤ heap) ∧
      prevLenPtr + ecPrev * L ≤ heap ∧ curLenPtr + ecCur * L ≤ heap ∧
      (batchPtr + totalWords ≤ curLenPtr ∨ curLenPtr + ecCur * L ≤ batchPtr) ∧
      (prevLenPtr + ecPrev * L ≤ curLenPtr ∨ curLenPtr + ecCur * L ≤ prevLenPtr) ∧
      (∀ e ∈ prevE, ∀ k < Lw, s.mem stretchDesc + e * Lw + k < curLenPtr ∨
        curLenPtr + ecCur * L ≤ s.mem stretchDesc + e * Lw + k) ∧
      (∀ e ∈ prevE, ∀ k < Lw, s.mem (stretchDesc + 1) + e * Lw + k < curLenPtr ∨
        curLenPtr + ecCur * L ≤ s.mem (stretchDesc + 1) + e * Lw + k))
    (hz : ZeroFrom s.mem heap)
    (hRoom : heap + U.length * wireCoreLenEdgeSpace LwMax < 2 ^ w)
    (hw5 : 5 < 2 ^ w) :
    ∃ (out : State) (cost : ℕ),
      Runs w p ω (wireBranchBNextLenStmt updLen) s .normal out cost ∧
      heap ≤ out.regs 4 ∧ out.regs 4 ≤ heap + U.length * wireCoreLenEdgeSpace LwMax ∧
      (∀ r, r ≠ 4 → r ≠ 20 → out.regs r = s.regs r) ∧
      (idx + 1 < d →
        EdgeValuesAt out.mem curLenPtr 4 L P (G.applyBatch U).E (coreLen forest prevℓ)) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ a < heap, (idx + 1 < d → a < curLenPtr ∨ curLenPtr + ecCur * L ≤ a) →
        out.mem a = s.mem a) ∧
      cost ≤ U.length * (wireCoreLenEdgeCost LwMax + 60) + 90 := by
  have hSp : wireCoreLenEdgeSpace (max L Lw) ≤ wireCoreLenEdgeSpace LwMax :=
    coreLenEdgeSpace_mono' hLw
  have hCo : wireCoreLenEdgeCost (max L Lw) ≤ wireCoreLenEdgeCost LwMax :=
    coreLenEdgeCost_mono' hLw
  by_cases hlt : idx + 1 < d
  · obtain ⟨hMetaW, hCell, hSmall, hBatchW, hStretch, hPrevLen, hCurLen, hGE, hInsInfo,
      hAgreeOld, hMemIns, hBatchLe, hStretchLe, hNumDenLe, hPrevLe, hCurLe, hDisjBatch, hDisjPrev,
      hDisjNum, hDisjDen⟩ := hNext hlt
    have hR : heap + U.length * wireCoreLenEdgeSpace (max L Lw) < 2 ^ w :=
      lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left _ hSp) _) hRoom
    obtain ⟨out, cost, hrun, hlo, hhi, hregs, hlen, hz', hfr, hc⟩ :=
      wireBranchBNextLenStmt_runs_lt hUpdLen hEdgeProc hSign hMul hDiv hCopy hRegs hlt hMetaW hCell
        hSmall hBatchW hStretch hPrevLen hCurLen hGE hInsInfo hAgreeOld hMemIns hBatchLe
        hStretchLe hNumDenLe hPrevLe hCurLe hDisjBatch hDisjPrev hDisjNum hDisjDen hz hR hw5
    have hm : U.length * wireCoreLenEdgeSpace (max L Lw) ≤
        U.length * wireCoreLenEdgeSpace LwMax := Nat.mul_le_mul_left _ hSp
    have hmc : U.length * (wireCoreLenEdgeCost (max L Lw) + 60) ≤
        U.length * (wireCoreLenEdgeCost LwMax + 60) := Nat.mul_le_mul_left _ (by omega)
    exact ⟨out, cost, hrun, hlo, by omega, hregs, fun _ => hlen, hz',
      fun a ha h => hfr a ha (h hlt), by omega⟩
  · obtain ⟨c, hrun, hc⟩ := wireBranchBNextLenStmt_runs_ge (w := w) (updLen := updLen) (p := p) (ω := ω) (s := s)
      (by omega) hRegs.1 hRegs.2.1 (by omega) (by omega)
    refine ⟨s, c, hrun, by rw [hRegs.2.2.2.2.2.2.2.2], by rw [hRegs.2.2.2.2.2.2.2.2]; omega,
      fun _ _ _ => rfl, fun h => absurd h hlt, by rw [hRegs.2.2.2.2.2.2.2.2]; exact hz,
      fun _ _ _ => rfl, by omega⟩

private theorem front_cost_arith {c1 c2 c3 phiY phi1 F R Ro C US : ℕ}
    (h1 : c1 ≤ 20 * (F + R) + 150) (h2 : c2 + phiY ≤ Ro + 70 + phi1)
    (h3 : c3 ≤ US * (C + 60) + 90) :
    c1 + (c2 + c3 + 1) + 1 + phiY ≤ 20 * (F + R) + Ro + US * (C + 60) + 320 + phi1 := by
  omega

set_option maxHeartbeats 1600000 in
/-- One run of the first three parts after the head of a non-rebuild level step. The head left the
change records and the re-embedding list of the active branch `b` in its output `[curHeap, h1)`,
the forwarded batch `US` there off the footprint, and the core of the level at the token `tok1`,
whose footprint lies in the old one `tok0` and in `[curHeap, h1)`. Write
`cur = h1 + |c.fDel| + |reemb|`, where `c` is the change record of branch `b`. The run:
* copies `c.fDel` to `h1` and the re-embedding list right after it, up to `cur`;
* leaves the core at the token `y` of op `2`, whose footprint grows only into `[cur, ret)`, and
  the copied descriptor at `cur + 5`, with the stretch values of the new forest in rows of `Lw`
  words that lie in that footprint or in `[cur, ret)`;
* writes the core lengths of the next level when `idx + 1 < d`;
* changes no word below `h1` outside the footprint of `tok1` and that length vector;
* costs `20` per copied entry, one readout, a constant per entry of the forwarded batch, and a
  constant. -/
theorem wireBranchBStepTailFrontKFBL_runs
    {w L P depth k M N vCap eCap capExp copyProc updLen edgeProc signExt mul intDiv
      copy idx d b coreH gPtr lPtr nextLPtr levelMeta curHeap h1 curBatch
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
    (hUpdLen : p.procs[updLen]? = some (wireUpdateCoreLenFromBatchBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopyW : MeetsContract w p copy (copyWordsContract w))
    (hRegs : s.regs 2 = b ∧ s.regs 3 = coreH ∧ s.regs 4 = h1 ∧ s.regs 6 = gPtr ∧
      s.regs 7 = lPtr ∧ s.regs 10 = nextB ∧ s.regs 23 = curBatch ∧ s.regs 24 = curBatchWords ∧
      s.regs 25 = curHeap ∧ s.regs 75 = d ∧ s.regs 76 = k ∧
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
    (hRoom : h1 + 2 * (h1 - curHeap) + 7 +
      US.length * wireCoreLenEdgeSpace (ordLevelLwMax L capExp M N) < 2 ^ w) :
    ∃ (out : State) (cost ret Lw : ℕ) (y : Rcore.τ) (c : Read.LSFChange),
      Runs w p ω (wireBranchBStepTailFrontKFBL copyProc (opCore 2) updLen) s .normal out cost ∧
      c.Exact (oldLsf b) (tool.lsfs a.st b) ∧ (∀ e ∈ c.fDel, e < 2 ^ w) ∧
      c.fDel.length ≤ h1 - curHeap ∧ reemb.length ≤ h1 - curHeap ∧
      ret ≤ h1 + c.fDel.length + reemb.length + 5 ∧
      h1 + c.fDel.length + reemb.length + 7 ≤ out.regs 4 ∧
      out.regs 4 ≤ h1 + c.fDel.length + reemb.length + 7 +
        US.length * wireCoreLenEdgeSpace (ordLevelLwMax L capExp M N) ∧
      out.regs 26 = h1 ∧ out.regs 27 = c.fDel.length ∧ out.regs 28 = h1 + c.fDel.length ∧
      out.regs 29 = reemb.length ∧ out.regs 31 = h1 + c.fDel.length + reemb.length + 5 ∧
      out.regs 32 = Lw ∧
      (∀ r, (r < 18 ∧ r ≠ 4 ∧ r ≠ 5) ∨ (23 ≤ r ∧ r ≤ 25) ∨ 33 < r → out.regs r = s.regs r) ∧
      Rcore.rep coreH a y out.mem ∧
      (∀ x, Rcore.foot coreH y x → Rcore.foot coreH tok1 x ∨
        (h1 + c.fDel.length + reemb.length ≤ x ∧ x < ret)) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ x < h1, ¬ Rcore.foot coreH tok1 x →
        (idx + 1 < d → x < nextLPtr ∨ nextLPtr + ecNext * L ≤ x) → out.mem x = s.mem x) ∧
      ListAt out.mem h1 c.fDel ∧ ListAt out.mem (h1 + c.fDel.length) reemb ∧
      Lw ≤ ordLevelLwMax L capExp M N ∧
      StretchValuesAt out.mem (h1 + c.fDel.length + reemb.length + 5) 4 Lw P a.G.E
        (tool.lsfs a.st b).wstr ∧
      SelOutTableAt w (Rcore.foot coreH y) (h1 + c.fDel.length + reemb.length) ret out.mem
        (h1 + c.fDel.length + reemb.length + 5) Lw a.G.E ∧
      SelOutTableAt w (Rcore.foot coreH y) (h1 + c.fDel.length + reemb.length) ret out.mem
        (h1 + c.fDel.length + reemb.length + 5 + 1) Lw a.G.E ∧
      SmallBatchAt out.mem curBatch G0 U curBatchWords ∧
      (∀ t < curBatchWords, out.mem (curBatch + t) < 2 ^ w) ∧
      SmallBatchAt out.mem nextB GS US nextBW ∧ (∀ t < nextBW, out.mem (nextB + t) < 2 ^ w) ∧
      (idx + 1 < d → EdgeValuesAt out.mem nextLPtr 4 L P (GS.applyBatch US).E
        (coreLen (tool.lsfs a.st b) ℓi)) ∧
      cost + Rcore.phi coreH y out.mem ≤ 20 * (c.fDel.length + reemb.length) + Psc.readout +
        US.length * (wireCoreLenEdgeCost (ordLevelLwMax L capExp M N) + 60) + 320 +
        Rcore.phi coreH tok1 s.mem := by
  obtain ⟨hr2, hr3, hr4, hr6, hr7, hr10, hr23, hr24, hr25, hr75, hr76, hr83, hr94, hr96⟩ :=
    hRegs
  generalize hLwMaxDef : ordLevelLwMax L capExp M N = LwMax at hRoom ⊢
  -- Part 1: the copies of the two lists
  obtain ⟨s1, c1, c, r1, hex, hcw, hFL, hRL, h26, h27, h28, h29, h4a, hLF, hLR, hfr1, hreg1,
      hc1⟩ :=
    wireBranchBCopyListsStmt_runs (w := w) (p := p) (ω := ω) (by omega) hCopy hr2 hr4 hr25 hr76
      hb hF hR hRlo hRhi (by omega)
  set cur := h1 + c.fDel.length + reemb.length with hcur
  have hfoot1lt : ∀ x, Rcore.foot coreH tok1 x → x < h1 := fun x hx => by
    rcases hFoot1 x hx with h | h
    · have := hFoot0 x h; omega
    · omega
  have hrep1 : Rcore.rep coreH a tok1 s1.mem :=
    ((hLocal coreH a tok1 s.mem s1.mem fun x hx =>
      (hfr1 x (Or.inl (hfoot1lt x hx))).symm).1 hRep)
  have hphi1 : Rcore.phi coreH tok1 s1.mem = Rcore.phi coreH tok1 s.mem :=
    ((hLocal coreH a tok1 s.mem s1.mem fun x hx =>
      (hfr1 x (Or.inl (hfoot1lt x hx))).symm).2).symm
  have hG1 : DynGraphAt s1.mem gPtr vCap eCap a.G :=
    dynGraphAt_of_agree hGAt fun x _ hx => hfr1 x (Or.inl (by omega))
  have hz1 : ZeroFrom s1.mem cur := fun x hx => by
    rw [hfr1 x (Or.inr (by omega))]; exact hz x (by omega)
  -- Part 2: op `2` and the descriptor copy
  obtain ⟨s2, ret, c2, y, r2, hret1, hret2, h4b, h30b, h31b, h32b, hreg2, hrep2, hfoot2, hz2, hfr2,
      hLw2, hSV2, hT0, hT1, hRows2, hc2⟩ :=
    wireBranchBReadDescStmt_runs (ω := ω) hLocal hFootAt ((hreg1 2 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr2)
      ((hreg1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hr3)
      ((hreg1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hr6)
      h4a hb hkW hCoreHW hG1 (by omega) hrep1 hIn (fun x hx => by have := hfoot1lt x hx; omega)
      hz1 (by omega)
  rw [hFour, hPrec] at hSV2
  have hLw2' : s2.mem (cur + 4) ≤ LwMax := by rw [← hLwMaxDef]; exact hLw2
  set Lw := s2.mem (cur + 4) with hLwDef
  have hfootY : ∀ x, Rcore.foot coreH y x →
      Rcore.foot coreH tok0 x ∨ (curHeap ≤ x ∧ x < h1) ∨ (cur ≤ x ∧ x < ret) := fun x hx => by
    rcases hfoot2 x hx with h | h
    · rcases hFoot1 x h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h)
  -- what parts 1 and 2 keep below `h1`
  have hkeep12 : ∀ x < h1, ¬ Rcore.foot coreH tok1 x → s2.mem x = s.mem x := fun x hx hn => by
    rw [hfr2 x (by omega) hn, hfr1 x (Or.inl hx)]
  have hoff1 : ∀ x, x < curHeap → ¬ Rcore.foot coreH tok0 x → ¬ Rcore.foot coreH tok1 x :=
    fun x hx hn hf => by
      rcases hFoot1 x hf with h | h
      · exact hn h
      · omega
  have hreg12 : ∀ r, (r < 18 ∧ r ≠ 4 ∧ r ≠ 5) ∨ (23 ≤ r ∧ r ≤ 25) ∨ 33 < r →
      s2.regs r = s.regs r := fun r hr => by
    rw [hreg2 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      hreg1 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)]
  have hUS2 : SmallBatchAt s2.mem nextB GS US nextBW :=
    smallBatchAt_of_agree hUS fun x hx1 hx2 => hkeep12 x (by omega) (by
      have := hUSOff (x - nextB) (by omega); rwa [show nextB + (x - nextB) = x by omega] at this)
  have hUSW2 : ∀ t < nextBW, s2.mem (nextB + t) < 2 ^ w := fun t ht => by
    rw [hkeep12 _ (by omega) (hUSOff t ht)]; exact hUSW t ht
  have hU2 : ∀ x, curBatch ≤ x → x < curBatch + curBatchWords → s2.mem x = s.mem x :=
    fun x hx1 hx2 => hkeep12 x (by omega) (hoff1 x (by omega) (by
      have := hUOff (x - curBatch) (by omega)
      rwa [show curBatch + (x - curBatch) = x by omega] at this))
  -- Part 3: the lengths of the next level
  obtain ⟨s3, c3, r3, h4c1, h4c2, hreg3, hlen3, hz3, hfr3, hc3⟩ :=
    nextLen_runs_either (s := s2) (LwMax := LwMax) (ω := ω) (G := GS) (U := US)
      (forest := tool.lsfs a.st b) (prevℓ := ℓi) (oldCurℓ := oldNextℓ) (prevE := a.G.E)
      (ecPrev := eCap) (ecCur := ecNext) (totalWords := nextBW) (curLenPtr := nextLPtr)
      hUpdLen hEdgeProc hSign hMul hDiv hCopyW
      ⟨(hreg12 96 (by omega)).trans hr96, (hreg12 75 (by omega)).trans hr75,
        (hreg12 83 (by omega)).trans hr83, (hreg12 10 (by omega)).trans hr10, h31b,
        (hreg12 7 (by omega)).trans hr7, (hreg12 94 (by omega)).trans hr94, h32b, h4b⟩
      hIdx hdW (max_le (by rw [← hLwMaxDef]; unfold ordLevelLwMax; omega) hLw2')
      (fun hlt => by
        obtain ⟨hMLt, hMOff, hCell, hCurLen, hGE, hInsInfo, hAgreeOld, hMemIns, hNLLe, hDisjPrev,
          hNLOff, _⟩ := hNext hlt
        refine ⟨by omega, (hkeep12 _ (by omega) (hoff1 _ hMLt hMOff)).trans hCell, hUS2, hUSW2,
          hSV2, ?_, ?_, hGE, hInsInfo, hAgreeOld, hMemIns, by omega, by omega,
          fun e he => ⟨by have := (hRows2 e he).1; omega, by have := (hRows2 e he).2; omega⟩,
          by omega, by omega, Or.inr (by omega), hDisjPrev, ?_, ?_⟩
        · exact EdgeValuesAt.congr hPrevLen fun e he i hi => by
            have := branchBEntry_lt (hPrevCap e he) hi
            exact hkeep12 _ (by omega) (hoff1 _ (by omega) (hPrevOff _ (by omega) (by omega)))
        · exact EdgeValuesAt.congr hCurLen fun e he i hi => by
            have := branchBEntry_lt (hGE e he) hi
            exact hkeep12 _ (by omega) (hoff1 _ (by omega) (hNLOff _ (by omega) (by omega)))
        · intro e he t ht
          rcases (hT0.2 e he).2 t ht with hf | hf
          · rcases hfootY _ hf with h | h | h
            · by_contra hc
              exact hNLOff _ (by omega) (by omega) h
            · exact Or.inr (by omega)
            · exact Or.inr (by omega)
          · exact Or.inr (by omega)
        · intro e he t ht
          rcases (hT1.2 e he).2 t ht with hf | hf
          · rcases hfootY _ hf with h | h | h
            · by_contra hc
              exact hNLOff _ (by omega) (by omega) h
            · exact Or.inr (by omega)
            · exact Or.inr (by omega)
          · exact Or.inr (by omega))
      hz2 (by omega) (by omega)
  have hreg123 : ∀ r, (r < 18 ∧ r ≠ 4 ∧ r ≠ 5) ∨ (23 ≤ r ∧ r ≤ 25) ∨ 33 < r →
      s3.regs r = s.regs r := fun r hr => by
    rw [hreg3 r (by omega) (by omega)]; exact hreg12 r hr
  have hkeep3 : ∀ x < cur + 7, (idx + 1 < d → x < nextLPtr ∨ nextLPtr + ecNext * L ≤ x) →
      s3.mem x = s2.mem x := hfr3
  have hNLend : idx + 1 < d → nextLPtr + ecNext * L ≤ curHeap := fun hlt =>
    (hNext hlt).2.2.2.2.2.2.2.2.1
  have hHi : ∀ x, curHeap ≤ x → x < cur + 7 → s3.mem x = s2.mem x := fun x hx1 hx2 =>
    hkeep3 x hx2 (fun hlt => Or.inr (by have := hNLend hlt; omega))
  have hUoffNL : ∀ x, curBatch ≤ x → x < curBatch + curBatchWords →
      (idx + 1 < d → x < nextLPtr ∨ nextLPtr + ecNext * L ≤ x) := fun x hx1 hx2 hlt => by
    have := (hNext hlt).2.2.2.2.2.2.2.2.2.2.2 (x - curBatch) (by omega)
    rwa [show curBatch + (x - curBatch) = x by omega] at this
  have hU3 : SmallBatchAt s3.mem curBatch G0 U curBatchWords :=
    smallBatchAt_of_agree hU fun x hx1 hx2 => by
      rw [hkeep3 x (by omega) (hUoffNL x hx1 hx2)]; exact hU2 x hx1 hx2
  have hUW3 : ∀ t < curBatchWords, s3.mem (curBatch + t) < 2 ^ w := fun t ht => by
    rw [hkeep3 _ (by omega) (hUoffNL _ (by omega) (by omega)), hU2 _ (by omega) (by omega)]
    exact hUW t ht
  have hUS3 : SmallBatchAt s3.mem nextB GS US nextBW :=
    smallBatchAt_of_agree hUS2 fun x hx1 hx2 => hHi x (by omega) (by omega)
  have hUSW3 : ∀ t < nextBW, s3.mem (nextB + t) < 2 ^ w := fun t ht => by
    rw [hHi _ (by omega) (by omega)]; exact hUSW2 t ht
  have hNotNL0 : ∀ x, Rcore.foot coreH tok0 x →
      (idx + 1 < d → x < nextLPtr ∨ nextLPtr + ecNext * L ≤ x) := fun x hx hlt => by
    by_contra hc
    exact (hNext hlt).2.2.2.2.2.2.2.2.2.2.1 x (by omega) (by omega) hx
  have hYmem : ∀ x, Rcore.foot coreH y x ∨ (cur ≤ x ∧ x < ret) → s3.mem x = s2.mem x := by
    intro x hx
    rcases hx with hf | hf
    · rcases hfootY x hf with h | h | h
      · exact hkeep3 x (by have := hFoot0 x h; omega) (hNotNL0 x h)
      · exact hHi x (by omega) (by omega)
      · exact hHi x (by omega) (by omega)
    · exact hHi x (by omega) (by omega)
  have hLoc3 := hLocal coreH a y s2.mem s3.mem fun x hx => (hYmem x (Or.inl hx)).symm
  have hL1 : ∀ t, h1 ≤ t → t < cur → s3.mem t = s1.mem t := fun t ht1 ht2 => by
    rw [hHi t (by omega) (by omega)]
    exact hfr2 t ht2 fun hf => by have := hfoot1lt t hf; omega
  have hd5 : s3.mem (cur + 5) = s2.mem (cur + 5) := hHi _ (by omega) (by omega)
  have hd6 : s3.mem (cur + 5 + 1) = s2.mem (cur + 5 + 1) := hHi _ (by omega) (by omega)
  have hcost : c1 + (c2 + c3 + 1) + 1 + Rcore.phi coreH y s3.mem ≤
      20 * (c.fDel.length + reemb.length) + Psc.readout +
        US.length * (wireCoreLenEdgeCost LwMax + 60) + 320 + Rcore.phi coreH tok1 s.mem := by
    rw [← hLoc3.2, ← hphi1]
    exact front_cost_arith hc1 hc2 hc3
  have hrun : Runs w p ω (wireBranchBStepTailFrontKFBL copyProc (opCore 2) updLen) s .normal s3
      (c1 + (c2 + c3 + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, c1, _, r1, runs_seq_iff.mpr (Or.inr ⟨s2, c2, c3, r2, r3, rfl⟩),
      rfl⟩)
  have h26' : s3.regs 26 = h1 := (hreg3 26 (by omega) (by omega)).trans ((hreg2 26 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h26)
  have h27' : s3.regs 27 = c.fDel.length := (hreg3 27 (by omega) (by omega)).trans ((hreg2 27
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h27)
  have h28' : s3.regs 28 = h1 + c.fDel.length := (hreg3 28 (by omega) (by omega)).trans ((hreg2 28
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28)
  have h29' : s3.regs 29 = reemb.length := (hreg3 29 (by omega) (by omega)).trans ((hreg2 29
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h29)
  refine ⟨s3, _, ret, Lw, y, c, hrun, hex, hcw, hFL, hRL, hret2, h4c1, h4c2, h26', h27', h28',
    h29', (hreg3 31 (by omega) (by omega)).trans h31b, (hreg3 32 (by omega) (by omega)).trans h32b,
    hreg123, hLoc3.1 hrep2, hfoot2, hz3,
    fun x hx hn hNL => by rw [hkeep3 x (by omega) hNL]; exact hkeep12 x hx hn,
    fun i hi => by rw [hL1 (h1 + i) (by omega) (by omega)]; exact hLF i hi,
    fun i hi => by rw [hL1 (h1 + c.fDel.length + i) (by omega) (by omega)]; exact hLR i hi,
    hLw2', ?_, ?_, ?_, hU3, hUW3, hUS3, hUSW3, hlen3, hcost⟩
  · exact stretchValuesAt_of_moved hSV2 (fun _ => ⟨hd5, hd6⟩)
      (fun e he t ht => hYmem _ ((hT0.2 e he).2 t ht))
      (fun e he t ht => hYmem _ ((hT1.2 e he).2 t ht))
  · refine ⟨by rw [hd5]; exact hT0.1, fun e he => ?_⟩
    rw [hd5]
    exact hT0.2 e he
  · refine ⟨by rw [hd6]; exact hT1.1, fun e he => ?_⟩
    rw [hd6]
    exact hT1.2 e he

end MinCostFlow.MinRatio
