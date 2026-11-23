module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActProof

import Mathlib.Tactic

/-!
# The post of Phase 2 as a predicate (`AssemblyFirstStepNewActPost`)

The top proof of the first step (`AssemblyFirstStepTop`) passes the state from Phase 2 to the
later phases through a predicate `Q₂`. Its main part is the post of Phase 2
(`asmFirstNewAct_runs`), which this file names `AsmFirstNewActPost`: it is the post of
`asmFirstNewAct_runs` for the end `hEnd`, the final state `st'` and the cost `c`, word for word.
`AsmFirstNewActPostAt` is the same post with its witnesses (the new side record, the tour state
and the lazy lists) as arguments, so that `Q₃` can name them. `asmFirstNewAct_runs_post` restates
`asmFirstNewAct_runs` with it.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

@[expose] public section

/-- **The post of Phase 2** (`asmFirstNewAct_runs`) for the end `hEnd`, the final state `st'`,
the cost `c`, and the witnesses: the side record `y'`, the tour state `tx1` and the lazy lists
`lazyE`. -/
def AsmFirstNewActPostAt (TS : BundleTourSpec) (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (w depth capExp fVertRoot fInitOne fInitSpan : ℕ) (impl : SparsifyImpl) (p : Program)
    (ω : ℕ → Bool) (hRoot : AsmFirstTourRootAt TR w p fVertRoot)
    (restH tourH newCompsPtr h pos : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
    (mk : Finset End)
    (y : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth)
    (tx₀ : (TR y.vCap5 y.eCap5).τ) (newComps : List (ℕ × ℕ)) (mem₀ : ℕ → ℕ) (hEnd : ℕ)
    (st' : State) (c : ℕ)
    (y' : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth)
    (tx1 : (TR y.vCap5 y.eCap5).τ) (lazyE : Fin newComps.length → List ℕ) : Prop :=
  let newSet : Finset (Finset ℕ) := (newComps.map fun p => y.comps.getD p.1 ∅).toFinset
  let tr_mid : BundleTreeState depth := { tr with activeComps := tr.activeComps ∪ newSet }
  let nSlots1 := y.slots.length + newCompsBucketSum tr y.comps newComps
  Runs w p ω (asmFirstNewActStmt fInitOne fInitSpan)
    (startState [restH, tourH, newCompsPtr, newComps.length, h] mem₀ pos)
    (.returned hEnd) st' c ∧
  y'.bunH = y.bunH ∧ y'.spanH = y.spanH ∧ y'.slotsPtr = y.slotsPtr ∧
  y'.slotsCap = y.slotsCap ∧ y'.slotCap = y.slotCap ∧ y'.vCap5 = y.vCap5 ∧
  y'.eCap5 = y.eCap5 ∧ y'.cap = y.cap ∧ y'.splitB = y.splitB ∧
  y'.spV = y.spV ∧ y'.spE = y.spE ∧ y'.mMax = y.mMax ∧
  y'.cmpH = y.cmpH ∧ y'.bktH = y.bktH ∧ y'.ctH = y.ctH ∧
  y'.comps = y.comps ∧ y'.kB = y.kB ∧ y'.walkPot = y.walkPot ∧ y'.lgFac = y.lgFac ∧
  y'.slots = List.range nSlots1 ∧
  (∀ q ∈ activePairs tr, y'.slotOf q = y.slotOf q) ∧
  SlotMapOK tr_mid y.slotCap y.cap y'.slots y'.slotOf ∧
  BunTableMatches tr_mid y'.slotOf y'.bunS ∧
  (∀ q ∈ activePairs tr_mid, ∃ (hs : y'.slotOf q < y'.cap) (d : DSHist),
    y'.spanS ⟨y'.slotOf q, hs⟩ = some d ∧
    d.state (asmBrSP impl w depth y') = tr.dyn q ∧
    d.G₀ = tr.initBunG q ∧
    (∀ u ∈ d.flat, isDelOrSplit u) ∧ d.G₀.BatchIsValid d.flat ∧ (∀ B ∈ d.Us, B ≠ [])) ∧
  AsmFirstSideSlotInv tr_mid y' ∧
  (bunTableHeadroomRep y'.slotCap y'.vCap5 y'.eCap5 y'.kB).rep y'.bunH y'.bunS y'.xBun st'.mem ∧
  (bucketSpannerRep (asmBrSP impl w depth y') y'.cap).rep y'.spanH y'.spanS y'.xSpan st'.mem ∧
  (TR y.vCap5 y.eCap5).rep tourH ⟨ord, tr.cs.RF, mk⟩ tx1 st'.mem ∧
  bunRestartInv y.vCap5 y.eCap5 y'.bunS (outCoreOrder tr ord) ∧
  st'.mem (restH + ASM_SD_NSLOTS) = nSlots1 ∧
  ListAt st'.mem y.slotsPtr y'.slots ∧ nSlots1 ≤ y.slotsCap ∧
  (∀ c (hc : c < y.comps.length),
    st'.mem (y.ctH + 3 * c + 1) = y'.cslPtr c ∧
    st'.mem (y.ctH + 3 * c + 2) = (y'.cslL c).length ∧
    (y'.cslL c).Nodup ∧
    (∀ bi (hbi : bi < (y'.cslL c).length),
      st'.mem (y'.cslPtr c + 2 * bi) = bucketCode (y'.cslL c)[bi].1 ∧
      st'.mem (y'.cslPtr c + 2 * bi + 1) = (y'.cslL c)[bi].2) ∧
    (∀ b t, (b, t) ∈ y'.cslL c ↔
      (y.comps[c], b) ∈ activePairs tr_mid ∧ t = y'.slotOf (y.comps[c], b))) ∧
  (∀ a, asmSdMapCell y' a →
    (∀ c < y.comps.length, a ≠ y.ctH + 3 * c) →
    (∀ v < y.vCap5, a ≠ y.cmpH + v) → st'.mem a < 2 ^ w) ∧
  (∀ i j, i ≠ j → ∀ a, asmSdMapPart y' i a → ¬ asmSdMapPart y' j a) ∧
  (∀ a, asmSdMapCell y' a → ¬ (y.slotsPtr ≤ a ∧ a < y.slotsPtr + y.slotsCap + 1)) ∧
  (∀ i < 4, ∀ j < 4, i ≠ j → ∀ a, asmSdPart restH y' i a → ¬ asmSdPart restH y' j a) ∧
  (∀ a, asmSdFoot restH y' a → ¬ (TR y.vCap5 y.eCap5).foot tourH tx1 a) ∧
  (∀ k (hk : k < newComps.length),
    ListAt st'.mem (st'.mem (h + 2 * k)) (lazyE ⟨k, hk⟩) ∧
    st'.mem (h + 2 * k + 1) = (lazyE ⟨k, hk⟩).length ∧
    (lazyE ⟨k, hk⟩).Pairwise (· < ·) ∧
    (lazyE ⟨k, hk⟩).toFinset = compCoreEdges tr (y.comps.getD (newComps.getD k (0, 0)).1 ∅) ∧
    h + 2 * newComps.length ≤ st'.mem (h + 2 * k) ∧
    st'.mem (h + 2 * k) + (lazyE ⟨k, hk⟩).length ≤ hEnd ∧
    (∀ a, st'.mem (h + 2 * k) ≤ a → a < st'.mem (h + 2 * k) + (lazyE ⟨k, hk⟩).length →
      ¬ (bunTableHeadroomRep y'.slotCap y'.vCap5 y'.eCap5 y'.kB).foot y'.bunH y'.xBun a ∧
      ¬ bucketFoot y'.spanH y'.xSpan a ∧
      ¬ (TR y.vCap5 y.eCap5).foot tourH tx1 a)) ∧
  h + 2 * newComps.length ≤ hEnd ∧
  hEnd ≤ h + newActTotalSpace TS hRoot.querySpace impl w y tr ord newComps ∧
  ZeroFrom st'.mem hEnd ∧
  (∀ a, asmSdFoot restH y' a → asmSdFoot restH y a ∨ (h + 2 * newComps.length ≤ a ∧ a < hEnd)) ∧
  (∀ a, (TR y.vCap5 y.eCap5).foot tourH tx1 a →
    (TR y.vCap5 y.eCap5).foot tourH tx₀ a ∨ (h + 2 * newComps.length ≤ a ∧ a < hEnd)) ∧
  (∀ a < h,
    ¬ (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH y.xBun a →
    ¬ bucketFoot y.spanH y.xSpan a →
    ¬ (TR y.vCap5 y.eCap5).foot tourH tx₀ a →
    a ≠ restH + ASM_SD_NSLOTS →
    (∀ k (_hk : k < newComps.length), ¬ (y.ctH + 3 * (newComps.getD k (0, 0)).1 + 1 ≤ a ∧
      a < y.ctH + 3 * (newComps.getD k (0, 0)).1 + 3)) →
    ¬ (y.slotsPtr + y.slots.length ≤ a ∧ a < y.slotsPtr + nSlots1) →
    st'.mem a = mem₀ a) ∧
  c + (bunTableHeadroomRep y'.slotCap y'.vCap5 y'.eCap5 y'.kB).phi y'.bunH y'.xBun st'.mem +
      320 * (capExp + 1) * y'.lgFac * bucketPhi (asmBrSP impl w depth y') y'.xSpan +
      (TR y.vCap5 y.eCap5).phi tourH tx1 st'.mem ≤
    newActCostMul TS hRoot.mul *
      (newComps.length + 1 + newSet.sum tr.lazyMachInitCost) * ordStoreLog y.eCap5 +
    320 * (capExp + 1) * y.lgFac * newSet.sum tr.lazyMachInitCost +
    (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).phi y.bunH y.xBun mem₀ +
    320 * (capExp + 1) * y.lgFac * bucketPhi (asmBrSP impl w depth y) y.xSpan +
    (TR y.vCap5 y.eCap5).phi tourH tx₀ mem₀

/-- **The post of Phase 2** (`asmFirstNewAct_runs`) for the end `hEnd`, the final state `st'`
and the cost `c`. -/
def AsmFirstNewActPost (TS : BundleTourSpec) (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (w depth capExp fVertRoot fInitOne fInitSpan : ℕ) (impl : SparsifyImpl) (p : Program)
    (ω : ℕ → Bool) (hRoot : AsmFirstTourRootAt TR w p fVertRoot)
    (restH tourH newCompsPtr h pos : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
    (mk : Finset End)
    (y : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth)
    (tx₀ : (TR y.vCap5 y.eCap5).τ) (newComps : List (ℕ × ℕ)) (mem₀ : ℕ → ℕ) (hEnd : ℕ)
    (st' : State) (c : ℕ) : Prop :=
  ∃ (y' : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth)
    (tx1 : (TR y.vCap5 y.eCap5).τ) (lazyE : Fin newComps.length → List ℕ),
    AsmFirstNewActPostAt TS TR w depth capExp fVertRoot fInitOne fInitSpan impl p ω hRoot restH tourH newCompsPtr h pos tr ord mk y tx₀ newComps mem₀ hEnd st' c y' tx1 lazyE

end

public section

set_option maxHeartbeats 1200000 in
/-- **Phase 2 with its post named** (`asmFirstNewAct_runs` with `AsmFirstNewActPost`). -/
theorem asmFirstNewAct_runs_post {TS : BundleTourSpec} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {w depth L capExp limbMul bBun fVertRoot fTourList fTourLen fTourOwner
      fInitOne fInitSpan fExp bExport bSpan : ℕ}
    {impl : SparsifyImpl} {Ψ : BundleTreeState depth → ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpBun : p.HasAt bBun (bundleProcs bBun fTourList fTourLen fTourOwner))
    (hRoot : AsmFirstTourRootAt TR w p fVertRoot)
    (hTB : AsmBrTourBridge TS TR w p fTourList fTourLen fTourOwner)
    (hfOne : p.procs[fInitOne]? = some (asmFirstInitOneCompStmt fVertRoot fTourList
      (bBun + bundleOffSort) (bBun + bundleIdxInitSlots)))
    (hfSpan : p.procs[fInitSpan]? = some (asmFirstInitSpanBody fExp (bSpan + bsIdxOp0 + 0)))
    (hfExp : p.procs[fExp]? = some (asmFirstInitExpBody bExport))
    (hpExport : p.HasAt bExport [bundleExportGraphStmt])
    (hpSpan : p.HasAt bSpan (bucketSpannerProcs impl bSpan))
    (hTR_loc : ∀ v e, (TR v e).Local)
    {restH tourH newCompsPtr h pos : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End} {mk : Finset End}
    {y : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth}
    {tx₀ : (TR y.vCap5 y.eCap5).τ} {newComps : List (ℕ × ℕ)} {mem_orig mem₀ : ℕ → ℕ}
    (hSide : AsmBrSideAt (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w depth L capExp limbMul Ψ restH ⟨tr, ord, y.vCap5, y.eCap5⟩ y mem_orig)
    (hAgree : ∀ a, asmSdFoot restH y a →
      (∀ c < y.comps.length, a ≠ y.ctH + 3 * c) →
      (∀ v < y.vCap5, a ≠ y.cmpH + v) → mem₀ a = mem_orig a)
    (hInactiveDyn : ∀ C ∈ components tr.cs.G₀, C ∉ tr.activeComps →
      ∀ b ∈ tr.activeBuckets C,
        tr.dyn (C, b) = DSHist.state (asmBrSP impl w depth y) ⟨tr.initBunG (C, b), []⟩)
    (hrepT : (TR y.vCap5 y.eCap5).rep tourH ⟨ord, tr.cs.RF, mk⟩ tx₀ mem₀)
    (hvCapG : ∀ u ∈ tr.cs.G.V, u < y.vCap5) (heCapG : ∀ e ∈ tr.cs.G.E, e < y.eCap5)
    (hw16 : 16 ≤ 2 ^ w) (hvCapW : y.vCap5 < 2 ^ w) (heCapW : 4 * y.eCap5 < 2 ^ w)
    (htourW : tourH < 2 ^ w)
    (hfootSide : ∀ a, asmSdFoot restH y a → a < h)
    (hfootT : ∀ a, (TR y.vCap5 y.eCap5).foot tourH tx₀ a → a < h)
    (hdisjST : ∀ a, asmSdFoot restH y a → ¬ (TR y.vCap5 y.eCap5).foot tourH tx₀ a)
    (hNC_at : ∀ i (hi : i < newComps.length),
      mem₀ (newCompsPtr + 2 * i) = (newComps[i]'hi).1 ∧
      mem₀ (newCompsPtr + 2 * i + 1) = (newComps[i]'hi).2)
    (hNC_lt : newCompsPtr + 2 * newComps.length ≤ h)
    (hNC_disj : ∀ a, newCompsPtr ≤ a → a < newCompsPtr + 2 * newComps.length →
      ¬ asmSdFoot restH y a ∧ ¬ (TR y.vCap5 y.eCap5).foot tourH tx₀ a)
    (hNC_nd : (newComps.map Prod.fst).Nodup)
    (hNC_ok : ∀ q ∈ newComps, ∃ hc : q.1 < y.comps.length,
      y.comps[q.1]'hc ∉ tr.activeComps ∧ q.2 ∈ (tr.cs.compSt (y.comps[q.1]'hc)).G.V)
    (hZero : ZeroFrom mem₀ h)
    (hSpace : h + newActTotalSpace TS hRoot.querySpace impl w y tr ord newComps < 2 ^ w) :
    ∃ hEnd st' c, AsmFirstNewActPost TS TR w depth capExp fVertRoot fInitOne fInitSpan impl p ω hRoot restH
        tourH newCompsPtr h pos tr ord mk y tx₀ newComps mem₀ hEnd st' c :=
  asmFirstNewAct_runs hpBun hRoot hTB hfOne hfSpan hfExp hpExport hpSpan hTR_loc hSide hAgree
    hInactiveDyn hrepT hvCapG heCapG hw16 hvCapW heCapW htourW hfootSide hfootT hdisjST hNC_at
    hNC_lt hNC_disj hNC_nd hNC_ok hZero hSpace

end

end MinCostFlow.SparseCore.Program
