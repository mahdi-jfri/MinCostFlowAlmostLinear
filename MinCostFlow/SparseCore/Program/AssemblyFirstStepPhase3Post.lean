module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase3Proof

import Mathlib.Tactic

/-!
# The post of Phase 3 as a predicate (`AssemblyFirstStepPhase3Post`)

The top proof of the first step (`AssemblyFirstStepTop`) passes the state from Phase 3 to
Phase 4 through a predicate `Q₃`. Its main part is the post of Phase 3 (`asmFirstPhase3_runs`),
which this file names `AsmFirstPhase3Post`: it is the post of `asmFirstPhase3_runs` for the end
`hEnd`, the final state `st'` and the cost `cost`, word for word. `AsmFirstPhase3PostAt` is the
same post with its witnesses as arguments, so that `Q₄` can name them. `asmFirstPhase3_runs_post`
restates `asmFirstPhase3_runs` with it.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

@[expose] public section

/-- **The post of Phase 3** (`asmFirstPhase3_runs`) for the end `hEnd`, the final state `st'`,
the cost `cost`, and the witnesses: the tour state `tx_pot'`, the places `splitPtr` and
`outDescPtr`, the marks `mk'`, the marked edges `M`, the split lists `Ys` and the touched slots
`touched`. -/
def AsmFirstPhase3PostAt (w depth slotCap vCap eCap bBun bTourStep fDelTriples fBuildGroups bunH tourH batch words edits
      editWords spPtr delEdgesPtr h pos : ℕ) (p : Program) (ω : ℕ → Bool)
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState depth) (U : List Update) (ord : ℕ → List End) (ed : List OrdEdit)
    (delEdges : List ℕ) (slotOf : Finset ℕ × ℤ → ℕ)
    (S₀ : BundleTableState slotCap) (m : BundleTableMeta slotCap)
    (tx_pot : (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).τ)
    (mem₀ : ℕ → ℕ) (hEnd : ℕ) (st' : State) (cost : ℕ)
    (tx_pot' : (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).τ)
    (splitPtr outDescPtr : ℕ) (mk' : Finset End) (M : Finset ℕ) (Ys : List (List End))
    (touched : List ℕ) : Prop :=
  let ord' := applyOrdEdits ord ed
  let info := stepBundleTree sp tr U ord ord'
  let keep := outKeep sp tr U ord ord'
  let G₁ := tr.S_cur.applyBatch ((outDelList sp tr U ord ord').map Update.delete)
  let S' := tableAfterStepRuns tr.cs tr.k ord' U S₀
  let TRpot := asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap
  Runs w p ω (asmFirstPhase3Stmt fDelTriples fBuildGroups (bTourStep + 2) (bBun + bundleIdxStep))
    (startState [bunH, slotCap, vCap, tourH, batch, words, edits, editWords, spPtr, delEdgesPtr, delEdges.length, h] mem₀ pos)
    (.returned hEnd) st' cost ∧
  (bunTableHeadroomRep slotCap vCap eCap tr.k).rep bunH S' m st'.mem ∧
  bunRestartInv vCap eCap S' (outCoreOrder info.state ord') ∧
  BunTableMatches info.state slotOf S' ∧
  TRpot.rep tourH ⟨ord', info.state.cs.RF, mk'⟩ tx_pot' st'.mem ∧
  keep ⊆ M ∧ M ⊆ tr.S_cur.E ∧
  OutMarksOf ⟨coreTour ord' info.state.cs.RF, mk'⟩ (outCoreOrder info.state ord') M ∧
  OutSplitListsAt st'.mem hEnd (fun a => a < h + 2 ∨ TRpot.foot tourH tx_pot' a)
    keep tr.S_cur.E splitPtr G₁ (restrictSplits keep info.U_core) Ys ∧
  (Ys.map List.length).sum ≤
    G₁.batchEnc (restrictSplits keep info.U_core) +
      markPot keep tr.S_cur.E (coreGraph tr.cs.G tr.cs.lsf) ∧
  st'.mem h = splitPtr ∧ st'.mem (h + 1) = outDescPtr ∧
  h + 2 ≤ outDescPtr ∧ outDescPtr + 1 + 3 * slotCap ≤ hEnd ∧
  touched.Nodup ∧ (∀ s ∈ touched, s < slotCap) ∧
  st'.mem outDescPtr = touched.length ∧
  (∀ i (hi : i < touched.length),
    let s := touched[i]'hi
    ∃ (hs : s < slotCap) (batchPtr totalWords : ℕ),
      st'.mem (outDescPtr + 1 + 3 * i) = s ∧
      st'.mem (outDescPtr + 1 + 3 * i + 1) = batchPtr ∧
      st'.mem (outDescPtr + 1 + 3 * i + 2) = totalWords ∧
      outDescPtr + 1 + 3 * slotCap ≤ batchPtr ∧ batchPtr + totalWords ≤ hEnd ∧
      ∀ B₀, S₀ ⟨s, hs⟩ = some B₀ →
        SmallBatchAt st'.mem batchPtr B₀.graph (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 totalWords) ∧
  (∀ j B₀, S₀ j = some B₀ → j.1 ∉ touched →
    (bundleCompStep tr.cs B₀ tr.k ord ord' U).1 = []) ∧
  (∀ j : Fin slotCap, S₀ j = none → j.1 ∉ touched) ∧
  h + 2 ≤ hEnd ∧
  hEnd ≤ h + asmFirstPhase3Space slotCap vCap eCap words editWords delEdges.length ∧
  ZeroFrom st'.mem hEnd ∧
  (∀ a, TRpot.foot tourH tx_pot' a → TRpot.foot tourH tx_pot a ∨ (h + 2 ≤ a ∧ a < hEnd)) ∧
  (∀ a < h, ¬ (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m a →
    ¬ TRpot.foot tourH tx_pot a → st'.mem a = mem₀ a) ∧
  cost + 70 * touched.length + (bunTableHeadroomRep slotCap vCap eCap tr.k).phi bunH m st'.mem +
      TRpot.phi tourH tx_pot' st'.mem ≤
    buildDelTriplesCost tourBundleSpec eCap delEdges.length +
    buildGroupsCost (canonSplitList tr.cs U).length +
    tourBlockStepMul *
      ((Ys.map List.length).sum + tr.S_cur.batchEnc info.U_S + words + editWords + 1) *
      ordStoreLog eCap +
    bundleStepCost tourBundleSpec eCap delEdges.length
      (splitGroupsOf ((canonSplitList tr.cs U).map fun s => (s.kept, s.fresh))) +
    bunPhiMul * branchStepCharge sp tr U ord ord' +
    bundleScanPotMul tourBundleSpec eCap *
      (2 * (U.length + (canonSplitList tr.cs U).length) * (Nat.log 2 (4 * eCap) + 2)) + 120 +
    (bunTableHeadroomRep slotCap vCap eCap tr.k).phi bunH m mem₀ +
    TRpot.phi tourH tx_pot mem₀

/-- **The post of Phase 3** (`asmFirstPhase3_runs`) for the end `hEnd`, the final state `st'`
and the cost `cost`. -/
def AsmFirstPhase3Post (w depth slotCap vCap eCap bBun bTourStep fDelTriples fBuildGroups bunH tourH batch words edits
      editWords spPtr delEdgesPtr h pos : ℕ) (p : Program) (ω : ℕ → Bool)
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState depth) (U : List Update) (ord : ℕ → List End) (ed : List OrdEdit)
    (delEdges : List ℕ) (slotOf : Finset ℕ × ℤ → ℕ)
    (S₀ : BundleTableState slotCap) (m : BundleTableMeta slotCap)
    (tx_pot : (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).τ)
    (mem₀ : ℕ → ℕ) (hEnd : ℕ) (st' : State) (cost : ℕ) : Prop :=
  ∃ tx_pot' splitPtr outDescPtr mk' M Ys, ∃ touched : List ℕ,
    AsmFirstPhase3PostAt w depth slotCap vCap eCap bBun bTourStep fDelTriples fBuildGroups bunH tourH batch words edits editWords spPtr delEdgesPtr h pos p ω sp tr U ord ed delEdges slotOf S₀ m tx_pot mem₀ hEnd st' cost
      tx_pot' splitPtr outDescPtr mk' M Ys touched

end

public section

set_option maxHeartbeats 1200000 in
/-- **Phase 3 with its post named** (`asmFirstPhase3_runs` with `AsmFirstPhase3Post`). -/
theorem asmFirstPhase3_runs_post {w depth slotCap vCap eCap bBun bTour bOut bCopy bTourStep
      fDelTriples fBuildGroups bunH tourH batch words edits editWords spPtr delEdgesPtr h pos : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpBun : p.HasAt bBun (bundleProcs bBun (tourOp bTour 4) (tourOp bTour 12) (tourOp bTour 10)))
    (hpT : HasTourProcs p bTour)
    (hpO : OutProcsAt p bOut (tourOp bTour 8) (tourOp bTour 7) (tourOp bTour 11) (tourOp bTour 9))
    (hpC : p.HasAt bCopy [copyWords])
    (hpTS : p.HasAt bTourStep (asmFirstTourBlockProcs bTourStep bTour bOut bCopy))
    (hfDel : p.procs[fDelTriples]? = some (asmFirstBuildDelTriplesStmt (bBun + bundleIdxReadParent)))
    (hfGrp : p.procs[fBuildGroups]? = some (asmFirstBuildGroupsStmt (bBun + bundleOffSort)))
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord : ℕ → List End} {ed : List OrdEdit}
    {mk : Finset End} {delEdges : List ℕ} {slotOf : Finset ℕ × ℤ → ℕ}
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {tx_pot : (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).τ}
    {mem₀ : ℕ → ℕ}
    (hready : OutStepReady sp tr U ord (applyOrdEdits ord ed))
    (hOFB : OrdEditsForBatch tr.cs.G U ed)
    (hOVF : OrdEditsValidFor vCap eCap ord ed)
    (hRlt : ∀ r ∈ (compLSFBatch tr.cs U).RF.R, r < vCap)
    (hE_old : ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E, e < eCap)
    (hE_new : ∀ e ∈ (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).E, e < eCap)
    (hDel_set : delEdges.toFinset = batchDeletes U)
    (hDel_cap : ∀ e ∈ delEdges, e < eCap)
    (hMarks : OutMarksOf ⟨coreTour ord tr.cs.RF, mk⟩ (outCoreOrder tr ord) tr.S_cur.E)
    (hinv0 : bunRestartInv vCap eCap S₀ (outCoreOrder tr ord))
    (hMatch0 : ∀ q ∈ activePairs (stepBundleTree sp tr U ord (applyOrdEdits ord ed)).state,
      ∃ (hs : slotOf q < slotCap) (B : BundleState), S₀ ⟨slotOf q, hs⟩ = some B ∧ BunAgree B (tr.bun q))
    (hBunNone : ∀ j : Fin slotCap, S₀ j ≠ none →
      ∃ q ∈ activePairs (stepBundleTree sp tr U ord (applyOrdEdits ord ed)).state, slotOf q = j.1)
    (hSlotInj : ∀ q₁ ∈ activePairs (stepBundleTree sp tr U ord (applyOrdEdits ord ed)).state,
      ∀ q₂ ∈ activePairs (stepBundleTree sp tr U ord (applyOrdEdits ord ed)).state,
        slotOf q₁ = slotOf q₂ → q₁ = q₂)
    (hBReady : ∀ j B₀, S₀ j = some B₀ → BundleStepReady tr.cs B₀ tr.k ord (applyOrdEdits ord ed) U)
    (hRepB : (bunTableHeadroomRep slotCap vCap eCap tr.k).rep bunH S₀ m mem₀)
    (hRepT : (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).rep
      tourH ⟨ord, tr.cs.RF, mk⟩ tx_pot mem₀)
    (hBatch : SmallBatchAt mem₀ batch tr.cs.G U words)
    (hEdits : OrdEditsAt mem₀ edits ed editWords)
    (hSpAt : SplitEntriesAt mem₀ spPtr (canonSplitList tr.cs U))
    (hDelAt : ListAt mem₀ delEdgesPtr delEdges)
    (hw16 : 16 ≤ 2 ^ w) (hw_sq : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htourH_w : tourH < 2 ^ w) (_hslotCap_w : slotCap < 2 ^ w)
    (hBatch_le : batch + words ≤ h) (hEdits_le : edits + editWords ≤ h)
    (hSp_le : spPtr + splitEntriesWords (canonSplitList tr.cs U) ≤ h)
    (hDel_le : delEdgesPtr + delEdges.length ≤ h)
    (htbl_le : bunH + bundleTableFixedSize slotCap eCap ≤ h)
    (hblks_w : ∀ js : Fin slotCap, ∀ q c, m.slotBlocks js = some (q, c) → q + bundleSlotBlockSize c < 2 ^ w)
    (hfootB_lt : ∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m a → a < h)
    (hfootT_lt : ∀ a, (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).foot tourH tx_pot a → a < h)
    (hdisjBT : ∀ a, (bunTableHeadroomRep slotCap vCap eCap tr.k).foot bunH m a →
      ¬ (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).foot tourH tx_pot a)
    (hBF : ∀ a, batch ≤ a → a < batch + words →
      ¬ (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).foot tourH tx_pot a)
    (hEF : ∀ a, edits ≤ a → a < edits + editWords →
      ¬ (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).foot tourH tx_pot a)
    (hSF : ∀ a, spPtr ≤ a → a < spPtr + splitEntriesWords (canonSplitList tr.cs U) →
      ¬ (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).foot tourH tx_pot a)
    (hDF : ∀ a, delEdgesPtr ≤ a → a < delEdgesPtr + delEdges.length →
      ¬ (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec) vCap eCap).foot tourH tx_pot a)
    (hZero : ZeroFrom mem₀ h)
    (hSpace : h + asmFirstPhase3Space slotCap vCap eCap words editWords delEdges.length < 2 ^ w) :
    ∃ hEnd st' cost, AsmFirstPhase3Post w depth slotCap vCap eCap bBun bTourStep fDelTriples fBuildGroups bunH
        tourH batch words edits editWords spPtr delEdgesPtr h pos p ω sp tr U ord ed delEdges slotOf
        S₀ m tx_pot mem₀ hEnd st' cost :=
  asmFirstPhase3_runs hpBun hpT hpO hpC hpTS hfDel hfGrp sp hready hOFB hOVF hRlt hE_old hE_new
    hDel_set hDel_cap hMarks hinv0 hMatch0 hBunNone hSlotInj hBReady hRepB hRepT hBatch hEdits
    hSpAt hDelAt hw16 hw_sq hpk_w htourH_w _hslotCap_w hBatch_le hEdits_le hSp_le hDel_le htbl_le
    hblks_w hfootB_lt hfootT_lt hdisjBT hBF hEF hSF hDF hZero hSpace

end

end MinCostFlow.SparseCore.Program
