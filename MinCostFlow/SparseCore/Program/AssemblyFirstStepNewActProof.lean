module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActMath

import Mathlib.Tactic

/-!
# Phase 2b end-to-end verification (`AssemblyFirstStepNewActProof`)

Verifies `asmFirstNewActStmt fInitOne fInitSpan` (`AssemblyFirstStepNewActProg.lean`):
1. Runs `asmFirstNewAct_loop_runs` to initialize P5's bundle slots and `csl`/`lazyE` lists for
   every newly active component in `newComps`.
2. If any new slots were allocated (`nSlots0 < nSlots1`), invokes `asmFirstStepActivateSpans_runs`
   on `[nSlots0 .. nSlots1)` to activate P6's bucket spanners on their initial bundle graphs.
3. Proves the complete post-Phase-2 bundle-side state (including `SlotMapOK`, `BunTableMatches`,
   `bucketSpannerRep` matching `tr.dyn` under the inactive invariant `hInactiveDyn`, `AsmFirstSideSlotInv`,
   updated `csl`, preserved `lazyE`, disjointness, footprint growth, frame, `ZeroFrom`, space
   bound `newActTotalSpace`, and amortized cost + potential bound with the side potential
   `320 * (capExp + 1) * y.lgFac * bucketPhi`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

public section

set_option maxHeartbeats 1200000 in
/-- **Complete verification of Phase 2 (`asmFirstNewActStmt`)**:
initializes P5's bundle slots and P6's bucket spanners for all newly active components in
`newComps`, advancing the bundle side from `tr` to `tr_mid := { tr with activeComps := tr.activeComps ∪ newSet }`
while preserving `lazyE` lists at `[h, h + 2 * newComps.length)` and meeting the amortized cost
bound against `320 * (capExp + 1) * y.lgFac * bucketPhi`. Takes `hInactiveDyn` (the inactive invariant) for initial spanner states on inactive
components. -/
theorem asmFirstNewAct_runs {TS : BundleTourSpec} {TR : ℕ → ℕ → DSRep AsmTourAbs}
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
    let newSet : Finset (Finset ℕ) := (newComps.map fun p => y.comps.getD p.1 ∅).toFinset
    let tr_mid : BundleTreeState depth := { tr with activeComps := tr.activeComps ∪ newSet }
    let nSlots1 := y.slots.length + newCompsBucketSum tr y.comps newComps
    ∃ hEnd st' c,
      ∃ (y' : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth)
      (tx1 : (TR y.vCap5 y.eCap5).τ) (lazyE : Fin newComps.length → List ℕ),
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
        (TR y.vCap5 y.eCap5).phi tourH tx₀ mem₀ := by
  intro newSet tr_mid nSlots1
  have hSide0 := hSide
  obtain ⟨hRec_eq, hrepB0, hrepS0, hSl0, _, _, hMapWords⟩ := asmBrSide_lift_agree hSide hAgree
  rcases hSide with ⟨hRecBun0, hRecSpan0, hRecSlots0, hRecNSlots0, _, _, _, hRecSpL0, hRecSplit0,
    hRecSpV0, hRecSpE0, _, hRecW0, _, _, _, hSlotsLeCap, hPartDisj, hMaps, hModel⟩
  unfold AsmBrSideModel at hModel; unfold AsmSdMapsAt at hMaps; dsimp only at hModel hMaps
  rcases hMaps with ⟨_, _, _, _, hCompsNd, hCompsMem, _, _, _, _, hMapDisj, hMapNotSl⟩
  rcases hModel with ⟨hSlotMap0, _, hSpanMatch0, hScurInv, _, _,
    ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩, hParamsLe, hSpanC, hSplitEq, _, _, _, _, hLazyBound, _, _, _,
    ⟨hTotCap, hSlotsRange, hFreeBun0, hFreeSpan0⟩, hInactiveInv, hCrossInv, _⟩
  have hSD_sz : ASM_SD_SIZE = 16 := rfl
  have hSD_ns : ASM_SD_NSLOTS = 3 := rfl
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have hrestH_lt : restH + ASM_SD_SIZE ≤ h := by
    by_contra hlt; push Not at hlt
    have : restH + ASM_SD_SIZE - 1 < h := hfootSide _ ⟨0, by omega, by omega, by omega⟩
    omega
  have hLoopSp_le : h + 2 * newComps.length + newActLoopSpace TS hRoot.querySpace tr ord y.comps newComps < 2 ^ w := by
    unfold newActTotalSpace at hSpace; dsimp only at hSpace; omega
  -- Prologue: `r5 := mem[restH + ASM_SD_NSLOTS]`, `r6 := h + 2 * nNew`
  set st0 := startState [restH, tourH, newCompsPtr, newComps.length, h] mem₀ pos
  have hr5_val : mem₀ (restH + ASM_SD_NSLOTS) = y.slots.length := (hRec_eq ASM_SD_NSLOTS (by decide)).trans hRecNSlots0
  have ha5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const ASM_SD_NSLOTS)))) st0 .normal
      { st0 with regs := Function.update st0.regs 5 y.slots.length } _ :=
    runs_assign_iff.mpr ⟨y.slots.length, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st0, startState]))
        (Expr.eval_const (by omega)) (by omega)) hr5_val, rfl, rfl, rfl⟩
  set stA : State := { st0 with regs := Function.update st0.regs 5 y.slots.length }
  have ha6 : Runs w p ω (.assign 6 (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 3)))) stA .normal
      { stA with regs := Function.update stA.regs 6 (h + 2 * newComps.length) } _ :=
    runs_assign_iff.mpr ⟨h + 2 * newComps.length,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [stA, st0, startState]))
        (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq (by simp [stA, st0, startState])) (by omega))
        (by omega), rfl, rfl, rfl⟩
  set stB : State := { stA with regs := Function.update stA.regs 6 (h + 2 * newComps.length) }
  -- Step 1: Run `asmFirstNewAct_loop_runs`
  obtain ⟨st1, cLoop, ⟨m1, tx1⟩, hrunLoop, hInvEnd, hcostLoop⟩ :=
    asmFirstNewAct_loop_runs (st₀ := stB) (ω := ω) hpBun hRoot hTB hfOne hSide0 hAgree hrepT
      hvCapG heCapG hw16 hvCapW heCapW htourW hfootSide hfootT hdisjST
      hNC_at hNC_lt hNC_disj hNC_nd hNC_ok hZero hLoopSp_le rfl
      ⟨by simp [stB, stA, st0, startState, Function.update],
       by simp [stB, stA, st0, startState, Function.update],
       by simp [stB, stA, st0, startState, Function.update],
       by simp [stB, stA, st0, startState, Function.update],
       by simp [stB, stA, st0, startState, Function.update],
       by simp [stB, stA, Function.update],
       by simp [stB, Function.update]⟩
  dsimp only [NewActLoopInv] at hInvEnd
  rw [List.take_length] at hInvEnd
  rcases hInvEnd with ⟨h1, S1, slotOf1, cslPtr1, cslL1, lazyE,
    hregs1, _, hr6_1, hSlotMap1, hBunMatch1, hOldSlot1, hS1_out, hrepB1, hrepT1, hInvB1,
    hNSl1, hSlots_new1, hCt1, hCslDisj1, hLazy1, hh1_lo, hh1_hi, hz1,
    hftB1, hftT1, hdisjBT1, hfr1⟩
  have hr0_1 : st1.regs 0 = restH := (hregs1 0 (by decide) (by decide) (by decide) (by decide)).trans (by simp [stB, stA, st0, startState])
  have hr1_1 : st1.regs 1 = tourH := (hregs1 1 (by decide) (by decide) (by decide) (by decide)).trans (by simp [stB, stA, st0, startState])
  have hr5_1 : st1.regs 5 = y.slots.length := (hregs1 5 (by decide) (by decide) (by decide) (by decide)).trans (by simp [stB, stA, st0, startState])
  have hsl_lt : y.slotsPtr + y.slotsCap + 1 ≤ h := by
    have : y.slotsPtr + y.slotsCap < h := hfootSide _ ⟨3, by omega, Or.inl ⟨by omega, by omega⟩⟩
    omega
  have hnSlots1_cap : nSlots1 ≤ y.slotCap ∧ nSlots1 ≤ y.cap ∧ nSlots1 ≤ y.slotsCap := by
    have hcard : y.slots.length = (activePairs tr).card := by
      rw [← List.toFinset_card_of_nodup hSlotMap0.1, ← hSlotMap0.image_eq,
        Finset.card_image_of_injOn fun q₁ hq₁ q₂ hq₂ heq => hSlotMap0.2.2.2.1 q₁ hq₁ q₂ hq₂ heq]
    have hle : nSlots1 ≤ min (min y.slotCap y.cap) y.slotsCap := by
      dsimp only [nSlots1]; rw [hcard]
      exact (activeBuckets_disj_sum_le tr y.comps hCompsNd hCompsMem hScurInv.1 newComps hNC_nd
        fun q hq => by obtain ⟨hc, hnot, _⟩ := hNC_ok q hq; exact ⟨hc, by rwa [getElem!_pos y.comps q.1 hc]⟩).trans hTotCap
    exact ⟨le_trans hle (le_trans (min_le_left _ _) (min_le_left _ _)),
      le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _)),
      le_trans hle (min_le_right _ _)⟩
  have hRec1 : ∀ off < ASM_SD_SIZE, off ≠ ASM_SD_NSLOTS → st1.mem (restH + off) = mem_orig (restH + off) :=
    fun off hoff hne => (hfr1 (restH + off) (by omega)
      (fun hB => hPartDisj 0 (by omega) 1 (by omega) (by decide) (restH + off) ⟨by omega, by omega⟩ hB)
      (hdisjST (restH + off) ⟨0, by omega, by omega, by omega⟩) (by omega)
      (fun k hk ⟨h1', h2'⟩ => hPartDisj 0 (by omega) 3 (by omega) (by decide) (restH + off) ⟨by omega, by omega⟩
        (Or.inr ⟨2, by omega, by
          have := (hNC_ok _ (List.getElem_mem hk)).1
          rw [List.getD_eq_getElem newComps (0, 0) hk] at h2'; omega⟩))
      (fun ⟨h1', h2'⟩ => hPartDisj 0 (by omega) 3 (by omega) (by decide) (restH + off) ⟨by omega, by omega⟩
        (Or.inl ⟨by omega, by omega⟩))).trans (hRec_eq off hoff)
  have hrepS1 : (bucketSpannerRep (asmBrSP impl w depth y) y.cap).rep y.spanH y.spanS y.xSpan st1.mem :=
    ((bucketSpannerRep_local (asmBrSP impl w depth y) y.cap) y.spanH y.spanS y.xSpan mem₀ st1.mem fun a ha =>
      (hfr1 a (hfootSide a ⟨2, by omega, ha⟩)
        (fun hB => hPartDisj 2 (by omega) 1 (by omega) (by decide) a ha hB)
        (hdisjST a ⟨2, by omega, ha⟩)
        (fun hEq => hPartDisj 2 (by omega) 0 (by omega) (by decide) a ha ⟨by omega, by omega⟩)
        (fun k hk ⟨h1', h2'⟩ => hPartDisj 2 (by omega) 3 (by omega) (by decide) a ha
          (Or.inr ⟨2, by omega, by
            have := (hNC_ok _ (List.getElem_mem hk)).1
            rw [List.getD_eq_getElem newComps (0, 0) hk] at h2'; omega⟩))
        (fun ⟨h1', h2'⟩ => hPartDisj 2 (by omega) 3 (by omega) (by decide) a ha
          (Or.inl ⟨by omega, by omega⟩))).symm).1 hrepS0
  -- Load `r8 := mem[restH + ASM_SD_NSLOTS] = nSlots1`
  have ha8 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const ASM_SD_NSLOTS)))) st1 .normal
      { st1 with regs := Function.update st1.regs 8 nSlots1 } _ :=
    runs_assign_iff.mpr ⟨nSlots1, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq hr0_1) (Expr.eval_const (by omega)) (by omega)) hNSl1, rfl, rfl, rfl⟩
  set stC : State := { st1 with regs := Function.update st1.regs 8 nSlots1 }
  set P := asmBrSP impl w depth y
  set newSlots : List ℕ := List.range' y.slots.length (newCompsBucketSum tr y.comps newComps)
  have hnewSlots_len : newSlots.length = newCompsBucketSum tr y.comps newComps := by simp [newSlots]
  have hnewSlots_mem : ∀ s, s ∈ newSlots ↔ y.slots.length ≤ s ∧ s < nSlots1 := fun s => by
    simp [newSlots, List.mem_range'_1, nSlots1]
  have hNewSlotPair : ∀ s ∈ newSlots, ∃ q ∈ activePairs tr_mid,
      q.1 ∈ newSet ∧ q.1 ∈ components tr.cs.G₀ ∧ q.1 ∉ tr.activeComps ∧ q.2 ∈ tr.activeBuckets q.1 ∧
      slotOf1 q = s ∧ (∃ hs : s < y.slotCap, ∃ B, S1 ⟨s, hs⟩ = some B ∧ BunAgree B (tr.bun q)) ∧
      asmFirstInitSlotGraph S1 s = tr.initBunG q ∧ SpanGraphOK P (asmFirstInitSlotGraph S1 s) := by
    intro s hs
    have ⟨hs_ge, hs_lt⟩ := (hnewSlots_mem s).mp hs
    obtain ⟨q, hq, hsq⟩ := hSlotMap1.2.2.1 s (List.mem_range.mpr hs_lt)
    rcases Finset.mem_biUnion.mp hq with ⟨C', hC', hb_img⟩
    rcases Finset.mem_image.mp hb_img with ⟨b', hb', rfl⟩
    have hq_not_old : C' ∉ tr.activeComps := fun hAct => by
      have hq_old : (C', b') ∈ activePairs tr := Finset.mem_biUnion.mpr ⟨C', hAct, Finset.mem_image_of_mem _ hb'⟩
      have := hOldSlot1 (C', b') hq_old
      have := List.mem_range.mp (hSlotsRange ▸ hSlotMap0.2.1 (C', b') hq_old); omega
    have hC'_new : C' ∈ newSet := (Finset.mem_union.mp hC').resolve_left hq_not_old
    have hC'_mem : C' ∈ components tr.cs.G₀ := by
      rw [List.mem_toFinset, List.mem_map] at hC'_new; rcases hC'_new with ⟨p', hp', rfl⟩
      obtain ⟨hlt', _, _⟩ := hNC_ok p' hp'; rw [List.getD_eq_getElem y.comps ∅ hlt']
      exact (hCompsMem _).mp (List.getElem_mem hlt')
    obtain ⟨hsB, B, hSB, hAg⟩ := hBunMatch1 (C', b') hq
    obtain ⟨_, _, _, _, hLz⟩ := hInactiveInv C' hC'_mem hq_not_old
    obtain ⟨_, hInitG, hSpOk⟩ := hLz b' hb'
    have hSB' : S1 ⟨s, hsq ▸ hsB⟩ = some B := by convert hSB using 2; exact Fin.ext hsq.symm
    have hGeq : asmFirstInitSlotGraph S1 s = tr.initBunG (C', b') := by
      rw [asmFirstInitSlotGraph, slotB_eq (hsq ▸ hsB) hSB', hInitG]; exact bunAgree_normGraph_eq hAg
    exact ⟨(C', b'), hq, hC'_new, hC'_mem, hq_not_old, hb', hsq, ⟨hsq ▸ hsB, B, hSB', hAg⟩, hGeq, hGeq.symm ▸ hSpOk⟩
  have hok_new : ∀ s ∈ newSlots, SpanGraphOK P (asmFirstInitSlotGraph S1 s) := fun s hs => by
    obtain ⟨_, _, _, _, _, _, _, _, _, hok⟩ := hNewSlotPair s hs; exact hok
  -- Step 2: Execute `if r5 < r8`
  set S6' : BucketSpannerState y.cap := spanAfter y.spanS (asmFirstInitSlotGraph S1) newSlots
  have hcond_runs : ∃ hEnd st2 cSpan x6',
      Runs w p ω
        (.cond (.bin .lt (.reg 5) (.reg 8))
          (.assign 9 (.bin .sub (.reg 8) (.reg 5)) ;;
           .assign 10 (.load (.bin .add (.reg 0) (.const ASM_SD_BUN))) ;;
           .assign 11 (.load (.bin .add (.reg 0) (.const ASM_SD_SPAN))) ;;
           .assign 12 (.bin .add (.load (.bin .add (.reg 0) (.const ASM_SD_SLOTS))) (.reg 5)) ;;
           .assign 13 (.load (.bin .add (.reg 0) (.const ASM_SD_SPLIT))) ;;
           .assign 14 (.load (.bin .add (.reg 0) (.const ASM_SD_SPV))) ;;
           .assign 15 (.load (.bin .add (.reg 0) (.const ASM_SD_SPE))) ;;
           .assign 16 (.load (.bin .add (.reg 0) (.const ASM_SD_SPL))) ;;
           .call 6 fInitSpan [.reg 10, .reg 1, .reg 11, .const 0, .reg 9, .reg 12, .reg 6,
             .const 0, .const 0, .reg 13, .reg 14, .reg 15, .reg 16])
          .nop)
        stC .normal st2 cSpan ∧
      st2.regs 6 = hEnd ∧
      (bucketSpannerRep P y.cap).rep y.spanH S6' x6' st2.mem ∧
      (∀ a, bucketFoot y.spanH x6' a → bucketFoot y.spanH y.xSpan a ∨ (h1 ≤ a ∧ a < hEnd)) ∧
      (∀ a < h1, ¬ bucketFoot y.spanH y.xSpan a → st2.mem a = st1.mem a) ∧
      h1 ≤ hEnd ∧
      hEnd ≤ h1 + newSlots.length * (10 + 13 * P.eCap + P.vCap + asmFiSpanCapSpace P) ∧
      ZeroFrom st2.mem hEnd ∧
      cSpan + specPhi P S6' ≤ specPhi P y.spanS +
        (newSlots.map fun s => bundleExportCost (slotB S1 s)).sum +
        (newSlots.map fun s => spanActivateCost P (asmFirstInitSlotGraph S1 s)).sum +
        200 * newSlots.length + 300 := by
    by_cases hlt : y.slots.length < nSlots1
    · have hcond : (Expr.bin .lt (.reg 5) (.reg 8)).eval w stC = some 1 :=
        Expr.eval_lt_true (Expr.eval_reg_of_eq (by simp [stC, hr5_1]))
          (Expr.eval_reg_of_eq (by simp [stC])) hlt h1w
      have hfitSpan : h1 + 6 * newSlots.length + 10 * edgeTot S1 newSlots +
          (newSlots.map fun s => bundleExportSpace (slotB S1 s)).sum +
          (newSlots.map fun s => spanActivateSpace P (asmFirstInitSlotGraph S1 s)).sum ≤
          h1 + newSlots.length * (10 + 13 * P.eCap + P.vCap + asmFiSpanCapSpace P) := by
        have h1' := asmFi_edgeTot_le P hok_new
        have h2' := asmFi_exportSpace_le P hok_new
        have h3' := asmFi_activateSpace_le P hok_new
        have h10 : 10 * edgeTot S1 newSlots ≤ 10 * (newSlots.length * P.eCap) :=
          Nat.mul_le_mul_left 10 h1'
        have hring : newSlots.length * (10 + 13 * P.eCap + P.vCap + asmFiSpanCapSpace P) =
            6 * newSlots.length + 10 * (newSlots.length * P.eCap) +
            newSlots.length * (4 + P.vCap + 3 * P.eCap) +
            newSlots.length * asmFiSpanCapSpace P := by ring
        omega
      have htbl_lt_w : y.bunH + bundleTableFixedSize y.slotCap y.eCap5 < 2 ^ w := by
        have : y.bunH + bundleTableFixedSize y.slotCap y.eCap5 - 1 < h :=
          hfootSide _ ⟨1, by omega, Or.inl ⟨by unfold bundleTableFixedSize; omega, by unfold bundleTableFixedSize; omega⟩⟩
        unfold bundleTableFixedSize at *; omega
      have hlistNew : ListAt st1.mem (y.slotsPtr + y.slots.length) newSlots := fun bi hbi => by
        have hlt_bi : bi < newCompsBucketSum tr y.comps newComps := by simpa [newSlots] using hbi
        have := hSlots_new1 (y.slots.length + bi) (by omega) (by omega)
        simpa [newSlots, Nat.add_assoc] using this
      obtain ⟨oSp, stSp, cSp, x6', hrunSp, hrep6', hft6', hfr6', hhLoSp, hhHiSp, hzSp, hcSp⟩ :=
        asmFirstStepActivateSpans_runs (P := P) (cap := y.cap) (ω := ω) (pos := stC.pos)
          hfExp hpExport hpSpan hw16
          (by change depth < 2 ^ w; rw [← hRecSpL0]; exact hRecW0 ASM_SD_SPL (by decide))
          (by change y.splitB < 2 ^ w; rw [← hRecSplit0]; exact hRecW0 ASM_SD_SPLIT (by decide))
          (by change y.spV < 2 ^ w; rw [← hRecSpV0]; exact hRecW0 ASM_SD_SPV (by decide))
          (by change y.spE < 2 ^ w; rw [← hRecSpE0]; exact hRecW0 ASM_SD_SPE (by decide))
          hrepB1.1 (fun a ha => by rcases hftB1 a ha with h0 | ⟨_, hhi⟩; exact lt_of_lt_of_le (hfootSide a ⟨1, by omega, h0⟩) (by omega); exact hhi)
          (fun s hs => by obtain ⟨_, _, _, _, _, _, _, ⟨hsB, B, hSB, _⟩, _, _⟩ := hNewSlotPair s hs; exact ⟨hsB, B, hSB⟩)
          hlistNew (by rw [hnewSlots_len]; omega) hz1 htbl_lt_w hok_new
          (fun s hs => by have := (hnewSlots_mem s).mp hs; omega)
          hrepS1 (fun a ha => lt_of_lt_of_le (hfootSide a ⟨2, by omega, ha⟩) (by omega))
          (fun a ha1 ha2 hS => hPartDisj 2 (by omega) 3 (by omega) (by decide) a hS (Or.inl ⟨by omega, by omega⟩))
          (by
            have h1 : h1 + newSlots.length * (10 + 13 * P.eCap + P.vCap + asmFiSpanCapSpace P) < 2 ^ P.w := by
              unfold newActTotalSpace at hSpace
              dsimp only [P, asmBrSP] at hSpace ⊢
              rw [hnewSlots_len]; omega
            exact lt_of_le_of_lt hfitSpan h1)
      have h0w : 0 < 2 ^ w := by omega
      have hsub9 : (Expr.bin .sub (.reg 8) (.reg 5)).eval w stC = some newSlots.length := by
        simp [Expr.eval, BinOp.eval, stC, hr5_1, newSlots, nSlots1, (by omega : newCompsBucketSum tr y.comps newComps < 2 ^ w)]
      set st9 := { stC with regs := Function.update stC.regs 9 newSlots.length }
      set st10 := { st9 with regs := Function.update st9.regs 10 y.bunH }
      set st11 := { st10 with regs := Function.update st10.regs 11 y.spanH }
      set st12 := { st11 with regs := Function.update st11.regs 12 (y.slotsPtr + y.slots.length) }
      set st13 := { st12 with regs := Function.update st12.regs 13 y.splitB }
      set st14 := { st13 with regs := Function.update st13.regs 14 y.spV }
      set st15 := { st14 with regs := Function.update st14.regs 15 y.spE }
      set st16 := { st15 with regs := Function.update st15.regs 16 depth }
      set stCall := { stSp with regs := Function.update st16.regs 6 oSp.value }
      have hcallSp : Runs w p ω
          (.call 6 fInitSpan [.reg 10, .reg 1, .reg 11, .const 0, .reg 9, .reg 12, .reg 6,
            .const 0, .const 0, .reg 13, .reg 14, .reg 15, .reg 16]) st16 .normal stCall _ :=
        runs_call_iff.mpr ⟨[y.bunH, tourH, y.spanH, 0, newSlots.length, y.slotsPtr + y.slots.length, h1,
          0, 0, y.splitB, y.spV, y.spE, depth], _, oSp, stSp, cSp,
          by simp [evalArgs, Expr.eval, st16, st15, st14, st13, st12, st11, st10, st9, stC, hr1_1, hr6_1, h0w],
          hfSpan, hrunSp, rfl, rfl, rfl⟩
      have hT : ∃ cB, Runs w p ω
          (.assign 9 (.bin .sub (.reg 8) (.reg 5)) ;;
           .assign 10 (.load (.bin .add (.reg 0) (.const ASM_SD_BUN))) ;;
           .assign 11 (.load (.bin .add (.reg 0) (.const ASM_SD_SPAN))) ;;
           .assign 12 (.bin .add (.load (.bin .add (.reg 0) (.const ASM_SD_SLOTS))) (.reg 5)) ;;
           .assign 13 (.load (.bin .add (.reg 0) (.const ASM_SD_SPLIT))) ;;
           .assign 14 (.load (.bin .add (.reg 0) (.const ASM_SD_SPV))) ;;
           .assign 15 (.load (.bin .add (.reg 0) (.const ASM_SD_SPE))) ;;
           .assign 16 (.load (.bin .add (.reg 0) (.const ASM_SD_SPL))) ;;
           .call 6 fInitSpan [.reg 10, .reg 1, .reg 11, .const 0, .reg 9, .reg 12, .reg 6,
             .const 0, .const 0, .reg 13, .reg 14, .reg 15, .reg 16]) stC .normal stCall cB ∧ cB ≤ cSp + 90 := by
        have e9 : Runs w p ω (.assign 9 (.bin .sub (.reg 8) (.reg 5))) stC .normal st9 _ := runs_assign_iff.mpr ⟨_, hsub9, rfl, rfl, rfl⟩
        have e10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 0) (.const ASM_SD_BUN)))) st9 .normal st10 _ :=
          runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st9, stC, hr0_1]))
            (Expr.eval_const (by unfold ASM_SD_BUN; omega)) (by unfold ASM_SD_BUN; omega)) ((hRec1 ASM_SD_BUN (by decide) (by decide)).trans hRecBun0), rfl, rfl, rfl⟩
        have e11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 0) (.const ASM_SD_SPAN)))) st10 .normal st11 _ :=
          runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st10, st9, stC, hr0_1]))
            (Expr.eval_const (by unfold ASM_SD_SPAN; omega)) (by unfold ASM_SD_SPAN; omega)) ((hRec1 ASM_SD_SPAN (by decide) (by decide)).trans hRecSpan0), rfl, rfl, rfl⟩
        have e12 : Runs w p ω (.assign 12 (.bin .add (.load (.bin .add (.reg 0) (.const ASM_SD_SLOTS))) (.reg 5))) st11 .normal st12 _ :=
          runs_assign_iff.mpr ⟨_, Expr.eval_add (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st11, st10, st9, stC, hr0_1]))
            (Expr.eval_const (by unfold ASM_SD_SLOTS; omega)) (by unfold ASM_SD_SLOTS; omega)) ((hRec1 ASM_SD_SLOTS (by decide) (by decide)).trans hRecSlots0))
            (Expr.eval_reg_of_eq (by simp [st11, st10, st9, stC, hr5_1])) (by omega), rfl, rfl, rfl⟩
        have e13 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 0) (.const ASM_SD_SPLIT)))) st12 .normal st13 _ :=
          runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st12, st11, st10, st9, stC, hr0_1]))
            (Expr.eval_const (by unfold ASM_SD_SPLIT; omega)) (by unfold ASM_SD_SPLIT; omega)) ((hRec1 ASM_SD_SPLIT (by decide) (by decide)).trans hRecSplit0), rfl, rfl, rfl⟩
        have e14 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 0) (.const ASM_SD_SPV)))) st13 .normal st14 _ :=
          runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st13, st12, st11, st10, st9, stC, hr0_1]))
            (Expr.eval_const (by unfold ASM_SD_SPV; omega)) (by unfold ASM_SD_SPV; omega)) ((hRec1 ASM_SD_SPV (by decide) (by decide)).trans hRecSpV0), rfl, rfl, rfl⟩
        have e15 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 0) (.const ASM_SD_SPE)))) st14 .normal st15 _ :=
          runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st14, st13, st12, st11, st10, st9, stC, hr0_1]))
            (Expr.eval_const (by unfold ASM_SD_SPE; omega)) (by unfold ASM_SD_SPE; omega)) ((hRec1 ASM_SD_SPE (by decide) (by decide)).trans hRecSpE0), rfl, rfl, rfl⟩
        have e16 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 0) (.const ASM_SD_SPL)))) st15 .normal st16 _ :=
          runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st15, st14, st13, st12, st11, st10, st9, stC, hr0_1]))
            (Expr.eval_const (by unfold ASM_SD_SPL; omega)) (by unfold ASM_SD_SPL; omega)) ((hRec1 ASM_SD_SPL (by decide) (by decide)).trans hRecSpL0), rfl, rfl, rfl⟩
        refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st9, _, _, e9,
          runs_seq_iff.mpr (Or.inr ⟨st10, _, _, e10,
          runs_seq_iff.mpr (Or.inr ⟨st11, _, _, e11,
          runs_seq_iff.mpr (Or.inr ⟨st12, _, _, e12,
          runs_seq_iff.mpr (Or.inr ⟨st13, _, _, e13,
          runs_seq_iff.mpr (Or.inr ⟨st14, _, _, e14,
          runs_seq_iff.mpr (Or.inr ⟨st15, _, _, e15,
          runs_seq_iff.mpr (Or.inr ⟨st16, _, _, e16, hcallSp, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), ?_⟩
        simp only [argsSize, Expr.size]; omega
      obtain ⟨cB, hrunB, hcB⟩ := hT
      refine ⟨oSp.value, stCall, _, x6',
        runs_cond_iff.mpr ⟨1, cB, hcond, by simpa using hrunB, rfl⟩,
        by simp [stCall], hrep6', hft6', hfr6', hhLoSp, hhHiSp.trans hfitSpan, hzSp, ?_⟩
      simp only [Expr.size, S6']; omega
    · have hcond : (Expr.bin .lt (.reg 5) (.reg 8)).eval w stC = some 0 := by
        simp [Expr.eval, BinOp.eval, stC, hr5_1, hlt, (by omega : 0 < 2 ^ w)]
      have hempty : newSlots = [] := by
        have : newCompsBucketSum tr y.comps newComps = 0 := by omega
        simp [newSlots, this]
      have hS6_eq : S6' = y.spanS := by
        funext j; simp [S6', hempty, spanAfter]
      refine ⟨h1, stC, _, y.xSpan,
        runs_cond_iff.mpr ⟨0, 1, hcond, by simp [runs_nop_iff], rfl⟩,
        by simp [stC, hr6_1], hS6_eq ▸ hrepS1, fun a ha => Or.inl ha, fun _ _ _ => rfl,
        le_refl _, by simp [hempty], hz1, by rw [hS6_eq]; simp [Expr.size]; omega⟩
  obtain ⟨hEnd, st2, cSpan, x6', hrunCond, hr6_2, hrep6', hft6', hfr6', hhEnd_lo, hhEnd_hi, hzEnd, hcSpan⟩ := hcond_runs
  have hret : Runs w p ω (.ret (.reg 6)) st2 (.returned hEnd) st2 2 :=
    runs_ret_iff.mpr ⟨hEnd, Expr.eval_reg_of_eq hr6_2, rfl, rfl, rfl⟩
  have hfullRun : Runs w p ω (asmFirstNewActStmt fInitOne fInitSpan) st0 (.returned hEnd) st2 _ :=
    runs_seq_iff.mpr (Or.inr ⟨stA, _, _, ha5,
      runs_seq_iff.mpr (Or.inr ⟨stB, _, _, ha6,
      runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hrunLoop,
      runs_seq_iff.mpr (Or.inr ⟨stC, _, _, ha8,
      runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hrunCond, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  let y' : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth :=
    { y with bunS := S1, xBun := m1, spanS := S6', xSpan := x6', slots := List.range nSlots1,
             slotOf := slotOf1, cslPtr := cslPtr1, cslL := cslL1 }
  have hB1_not_S : ∀ a, (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH m1 a →
      a < h1 ∧ ¬ bucketFoot y.spanH y.xSpan a := fun a ha => by
    rcases hftB1 a ha with h0 | ⟨hlo, hhi⟩
    · exact ⟨lt_of_lt_of_le (hfootSide a ⟨1, by omega, h0⟩) (by omega),
        fun hS => hPartDisj 1 (by omega) 2 (by omega) (by decide) a h0 hS⟩
    · exact ⟨hhi, fun hS => by have := hfootSide a ⟨2, by omega, hS⟩; omega⟩
  have hT1_not_S : ∀ a, (TR y.vCap5 y.eCap5).foot tourH tx1 a →
      a < h1 ∧ ¬ bucketFoot y.spanH y.xSpan a := fun a ha => by
    rcases hftT1 a ha with h0 | ⟨hlo, hhi⟩
    · exact ⟨lt_of_lt_of_le (hfootT a h0) (by omega), fun hS => hdisjST a ⟨2, by omega, hS⟩ h0⟩
    · exact ⟨hhi, fun hS => by have := hfootSide a ⟨2, by omega, hS⟩; omega⟩
  have hB_loc := (bunTableHeadroomRep_local y.slotCap y.vCap5 y.eCap5 y.kB) y.bunH S1 m1 st1.mem st2.mem
    fun a ha => (hfr6' a (hB1_not_S a ha).1 (hB1_not_S a ha).2).symm
  have hT_loc := (hTR_loc y.vCap5 y.eCap5) tourH ⟨ord, tr.cs.RF, mk⟩ tx1 st1.mem st2.mem
    fun a ha => (hfr6' a (hT1_not_S a ha).1 (hT1_not_S a ha).2).symm
  -- `S6'` matches `tr.dyn` on `activePairs tr_mid` (using the inactive invariant `hInactiveDyn`)
  have hSpanMatch' : ∀ q ∈ activePairs tr_mid, ∃ (hs : slotOf1 q < y.cap) (d : DSHist),
      S6' ⟨slotOf1 q, hs⟩ = some d ∧ d.state P = tr.dyn q ∧ d.G₀ = tr.initBunG q ∧
      (∀ u ∈ d.flat, isDelOrSplit u) ∧ d.G₀.BatchIsValid d.flat ∧ (∀ B ∈ d.Us, B ≠ []) := by
    intro q hq
    have hs_mem := hSlotMap1.2.1 q hq
    have hs_cap : slotOf1 q < y.cap := (hSlotMap1.2.2.2.2 _ hs_mem).2
    by_cases hOld : q ∈ activePairs tr
    · have hsq : slotOf1 q = y.slotOf q := hOldSlot1 q hOld
      have hlt0 : slotOf1 q < y.slots.length := by rw [hsq]; exact List.mem_range.mp (hSlotsRange ▸ hSlotMap0.2.1 q hOld)
      have hnot_new : slotOf1 q ∉ newSlots := fun hm => by have := (hnewSlots_mem _).mp hm; omega
      obtain ⟨hs0, d, hSd, hst, hG0, hds, hbv, hne⟩ := hSpanMatch0 q hOld
      refine ⟨hs_cap, d, ?_, hst, hG0, hds, hbv, hne⟩
      dsimp only [S6']; rw [spanAfter_of_not_mem y.spanS (asmFirstInitSlotGraph S1) hnot_new]
      convert hSd using 2; exact Fin.ext hsq
    · have hge0 : y.slots.length ≤ slotOf1 q := by
        by_contra hlt; push Not at hlt
        obtain ⟨q0, hq0, hsq0⟩ := hSlotMap0.2.2.1 (slotOf1 q) (hSlotsRange ▸ List.mem_range.mpr hlt)
        have hq0_mid : q0 ∈ activePairs tr_mid := by
          rcases Finset.mem_biUnion.mp hq0 with ⟨C', hC', hb'⟩; exact Finset.mem_biUnion.mpr ⟨C', Finset.mem_union_left _ hC', hb'⟩
        have hEq_q : q = q0 := hSlotMap1.2.2.2.1 q hq q0 hq0_mid ((hOldSlot1 q0 hq0).trans hsq0).symm
        exact hOld (hEq_q ▸ hq0)
      have hmem_new : slotOf1 q ∈ newSlots := (hnewSlots_mem _).mpr ⟨hge0, List.mem_range.mp hs_mem⟩
      obtain ⟨q', hq', _, hC'_mem, hC'_not, hb', hsq', _, hGeq', _⟩ := hNewSlotPair _ hmem_new
      have hqq' : q = q' := hSlotMap1.2.2.2.1 q hq q' hq' hsq'.symm
      subst hqq'
      refine ⟨hs_cap, ⟨tr.initBunG q, []⟩, ?_, (hInactiveDyn q.1 hC'_mem hC'_not q.2 hb').symm, rfl,
        (fun _ h => by cases h), trivial, fun _ h => by cases h⟩
      dsimp only [S6']; rw [spanAfter_of_mem y.spanS (asmFirstInitSlotGraph S1) hmem_new, hGeq']
  have hSideSlotInv' : AsmFirstSideSlotInv tr_mid y' := by
    refine ⟨hTotCap, by simp [y'], fun j hj => ?_, fun j hj => ?_⟩
    · have hge : nSlots1 ≤ j.1 := by simp [y'] at hj; omega
      exact (hS1_out j (Or.inr hge)).trans (hFreeBun0 j (by rw [hSlotsRange]; simp; omega))
    · have hge : nSlots1 ≤ j.1 := by simp [y'] at hj; omega
      have hnot_new : j.1 ∉ newSlots := fun hm => by have := (hnewSlots_mem _).mp hm; omega
      dsimp only [y', S6']; rw [spanAfter_of_not_mem _ _ hnot_new]
      exact hFreeSpan0 j (by rw [hSlotsRange]; simp; omega)
  have hfr_not_S0 : ∀ a < h, ¬ bucketFoot y.spanH y.xSpan a → st2.mem a = st1.mem a :=
    fun a ha hns => hfr6' a (by omega) hns
  have hSlotsList' : ListAt st2.mem y.slotsPtr (List.range nSlots1) := fun s hs => by
    have hslt : s < nSlots1 := by simpa using hs
    have hfrS : st2.mem (y.slotsPtr + s) = st1.mem (y.slotsPtr + s) :=
      hfr_not_S0 (y.slotsPtr + s) (by omega)
        (fun hS => hPartDisj 2 (by omega) 3 (by omega) (by decide) (y.slotsPtr + s) hS (Or.inl ⟨by omega, by omega⟩))
    rw [hfrS, List.getElem_range]
    by_cases hlt0 : s < y.slots.length
    · have h1 := hfr1 (y.slotsPtr + s) (by omega)
        (fun hB => hPartDisj 1 (by omega) 3 (by omega) (by decide) (y.slotsPtr + s) hB (Or.inl ⟨by omega, by omega⟩))
        (hdisjST (y.slotsPtr + s) ⟨3, by omega, Or.inl ⟨by omega, by omega⟩⟩)
        (fun hEq => hPartDisj 0 (by omega) 3 (by omega) (by decide) (y.slotsPtr + s) ⟨by omega, by omega⟩ (Or.inl ⟨by omega, by omega⟩))
        (fun k hk ⟨h1', h2'⟩ => hMapNotSl (y.slotsPtr + s) ⟨2, by omega, by
          have := (hNC_ok _ (List.getElem_mem hk)).1; rw [List.getD_eq_getElem newComps (0, 0) hk] at h2'; omega⟩ ⟨by omega, by omega⟩)
        (by omega)
      have h0 := hSl0 s hlt0
      have hr : y.slots[s]'hlt0 = s := by
        have := congrArg (fun l => l.getD s 0) hSlotsRange
        rw [List.getD_eq_getElem _ _ hlt0, List.getD_eq_getElem _ _ (by simp [hlt0]), List.getElem_range] at this
        exact this
      exact h1.trans (h0.trans hr)
    · exact hSlots_new1 s (by omega) hslt
  have hcsl_not_S0 : ∀ c (hc : c < y.comps.length), ∀ a, cslPtr1 c ≤ a → a < cslPtr1 c + 2 * (cslL1 c).length →
      a < h1 ∧ ¬ bucketFoot y.spanH y.xSpan a := fun c hc a ha1 ha2 => by
    obtain ⟨_, _, _, _, _, _, hnotP, hrg⟩ := hCt1 c hc
    rcases hrg with h0 | ⟨hlo_np, hlo_p, _⟩
    · omega
    · by_cases hcp : c ∈ newComps.map Prod.fst
      · have ⟨hc1, hc2⟩ := hlo_p hcp
        exact ⟨by omega, fun hS => by have := hfootSide a ⟨2, by omega, hS⟩; omega⟩
      · have ⟨hcp_eq, hcl_eq⟩ := hnotP hcp
        have ha_lt := hlo_np hcp
        exact ⟨by omega, fun hS => hPartDisj 2 (by omega) 3 (by omega) (by decide) a hS
          (Or.inr ⟨c + 3, hc, hcp_eq ▸ ha1, hcp_eq ▸ hcl_eq ▸ ha2⟩)⟩
  have hMapDisj' : ∀ i j, i ≠ j → ∀ a, asmSdMapPart y' i a → ¬ asmSdMapPart y' j a := by
    intro i j hne a hi hj
    have hcsl_new_ge : ∀ c (hc : c < y.comps.length), c ∈ newComps.map Prod.fst →
        cslPtr1 c ≤ a → a < cslPtr1 c + 2 * (cslL1 c).length → h + 2 * newComps.length ≤ a := fun c hc hcp h1' h2' => by
      obtain ⟨_, _, _, _, _, _, _, hrg⟩ := hCt1 c hc
      rcases hrg with h0 | ⟨_, hlo_p, _⟩; omega; have := (hlo_p hcp).1; omega
    have hlt_h_012 : ∀ k < 3, asmSdMapPart y' k a → a < h := fun k hk hka => by
      match k with
      | 0 => exact hfootSide a ⟨3, by omega, Or.inr ⟨0, hka⟩⟩
      | 1 => exact hfootSide a ⟨3, by omega, Or.inr ⟨1, hka⟩⟩
      | 2 => exact hfootSide a ⟨3, by omega, Or.inr ⟨2, hka⟩⟩
    match i, j with
    | 0, 0 | 1, 1 | 2, 2 => exact absurd rfl hne
    | 0, 1 | 0, 2 | 1, 0 | 1, 2 | 2, 0 | 2, 1 => exact hMapDisj _ _ hne a hi hj
    | c₁ + 3, c₂ + 3 => exact hCslDisj1 c₁ hi.1 c₂ hj.1 (by omega) a hi.2.1 hi.2.2 ⟨hj.2.1, hj.2.2⟩
    | 0, c + 3 | 1, c + 3 | 2, c + 3 =>
      by_cases hcp : c ∈ newComps.map Prod.fst
      · have := hcsl_new_ge c hj.1 hcp hj.2.1 hj.2.2; have := hlt_h_012 _ (by omega) hi; omega
      · obtain ⟨_, _, _, _, _, _, hnotP, _⟩ := hCt1 c hj.1; obtain ⟨hpe, hle⟩ := hnotP hcp
        exact hMapDisj _ (c + 3) hne a hi ⟨hj.1, hpe ▸ hj.2.1, hpe ▸ hle ▸ hj.2.2⟩
    | c + 3, 0 | c + 3, 1 | c + 3, 2 =>
      by_cases hcp : c ∈ newComps.map Prod.fst
      · have := hcsl_new_ge c hi.1 hcp hi.2.1 hi.2.2; have := hlt_h_012 _ (by omega) hj; omega
      · obtain ⟨_, _, _, _, _, _, hnotP, _⟩ := hCt1 c hi.1; obtain ⟨hpe, hle⟩ := hnotP hcp
        exact hMapDisj (c + 3) _ hne a ⟨hi.1, hpe ▸ hi.2.1, hpe ▸ hle ▸ hi.2.2⟩ hj
  have hMapNotSl' : ∀ a, asmSdMapCell y' a → ¬ (y.slotsPtr ≤ a ∧ a < y.slotsPtr + y.slotsCap + 1) := by
    rintro a ⟨k, hk⟩ ⟨hs1, hs2⟩
    match k with
    | 0 => exact hMapNotSl a ⟨0, hk⟩ ⟨hs1, hs2⟩
    | 1 => exact hMapNotSl a ⟨1, hk⟩ ⟨hs1, hs2⟩
    | 2 => exact hMapNotSl a ⟨2, hk⟩ ⟨hs1, hs2⟩
    | c + 3 =>
      by_cases hcp : c ∈ newComps.map Prod.fst
      · obtain ⟨_, _, _, _, _, _, _, hrg⟩ := hCt1 c hk.1
        dsimp only [asmSdMapPart, y'] at hk
        rcases hrg with h0 | ⟨_, hlo_p, _⟩
        · omega
        · have := (hlo_p hcp).1; omega
      · obtain ⟨_, _, _, _, _, _, hnotP, _⟩ := hCt1 c hk.1; obtain ⟨hpe, hle⟩ := hnotP hcp
        exact hMapNotSl a ⟨c + 3, hk.1, hpe ▸ hk.2.1, hpe ▸ hle ▸ hk.2.2⟩ ⟨hs1, hs2⟩
  have hPart3_lt1 : ∀ a, asmSdPart restH y' 3 a → a < h1 ∧
      ¬ (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH m1 a ∧
      ¬ bucketFoot y.spanH y.xSpan a ∧ ¬ (TR y.vCap5 y.eCap5).foot tourH tx1 a := by
    rintro a (hsl | ⟨k, hk⟩)
    · dsimp only [y'] at hsl
      refine ⟨by omega,
        fun hB => by rcases hftB1 a hB with h0 | ⟨hlo, _⟩; exact hPartDisj 1 (by omega) 3 (by omega) (by decide) a h0 (Or.inl hsl); omega,
        fun hS => hPartDisj 2 (by omega) 3 (by omega) (by decide) a hS (Or.inl hsl),
        fun hT => by rcases hftT1 a hT with h0 | ⟨hlo, _⟩; exact hdisjST a ⟨3, by omega, Or.inl hsl⟩ h0; omega⟩
    · have h012 : ∀ (idx : ℕ), idx < 3 → asmSdMapPart y idx a →
          a < h1 ∧ ¬ (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH m1 a ∧
          ¬ bucketFoot y.spanH y.xSpan a ∧ ¬ (TR y.vCap5 y.eCap5).foot tourH tx1 a := fun idx _ hidx => by
        have ha_h : a < h := hfootSide a ⟨3, by omega, Or.inr ⟨idx, hidx⟩⟩
        refine ⟨by omega,
          fun hB => by rcases hftB1 a hB with h0 | ⟨hlo, _⟩; exact hPartDisj 1 (by omega) 3 (by omega) (by decide) a h0 (Or.inr ⟨idx, hidx⟩); omega,
          fun hS => hPartDisj 2 (by omega) 3 (by omega) (by decide) a hS (Or.inr ⟨idx, hidx⟩),
          fun hT => by rcases hftT1 a hT with h0 | ⟨hlo, _⟩; exact hdisjST a ⟨3, by omega, Or.inr ⟨idx, hidx⟩⟩ h0; omega⟩
      match k with
      | 0 => exact h012 0 (by omega) hk
      | 1 => exact h012 1 (by omega) hk
      | 2 => exact h012 2 (by omega) hk
      | c + 3 =>
        obtain ⟨_, _, _, _, _, _, _, hrg⟩ := hCt1 c hk.1
        dsimp only [asmSdMapPart, y'] at hk
        rcases hrg with h0 | ⟨_, _, hcells⟩
        · omega
        · exact ⟨(hcsl_not_S0 c hk.1 a hk.2.1 hk.2.2).1, (hcells a hk.2.1 hk.2.2).1,
            (hcsl_not_S0 c hk.1 a hk.2.1 hk.2.2).2, (hcells a hk.2.1 hk.2.2).2.1⟩
  have hPartDisj' : ∀ i < 4, ∀ j < 4, i ≠ j → ∀ a, asmSdPart restH y' i a → ¬ asmSdPart restH y' j a := by
    intro i hi j hj hne a hai haj
    have h0_lt : ∀ a, asmSdPart restH y' 0 a → a < h := fun a ha => hfootSide a ⟨0, by omega, ha⟩
    match i, j with
    | 0, 0 | 1, 1 | 2, 2 | 3, 3 => exact absurd rfl hne
    | 0, 1 => rcases hftB1 a haj with h0 | ⟨hlo, _⟩; exact hPartDisj 0 (by omega) 1 (by omega) (by decide) a hai h0; have := h0_lt a hai; omega
    | 1, 0 => rcases hftB1 a hai with h0 | ⟨hlo, _⟩; exact hPartDisj 1 (by omega) 0 (by omega) (by decide) a h0 haj; have := h0_lt a haj; omega
    | 0, 2 => rcases hft6' a haj with h0 | ⟨hlo, _⟩; exact hPartDisj 0 (by omega) 2 (by omega) (by decide) a hai h0; have := h0_lt a hai; omega
    | 2, 0 => rcases hft6' a hai with h0 | ⟨hlo, _⟩; exact hPartDisj 2 (by omega) 0 (by omega) (by decide) a h0 haj; have := h0_lt a haj; omega
    | 0, 3 =>
      rcases haj with hsl | ⟨k, hk⟩
      · exact hPartDisj 0 (by omega) 3 (by omega) (by decide) a hai (Or.inl hsl)
      · match k with
        | 0 => exact hPartDisj 0 (by omega) 3 (by omega) (by decide) a hai (Or.inr ⟨0, hk⟩)
        | 1 => exact hPartDisj 0 (by omega) 3 (by omega) (by decide) a hai (Or.inr ⟨1, hk⟩)
        | 2 => exact hPartDisj 0 (by omega) 3 (by omega) (by decide) a hai (Or.inr ⟨2, hk⟩)
        | c + 3 =>
          by_cases hcp : c ∈ newComps.map Prod.fst
          · obtain ⟨_, _, _, _, _, _, _, hrg⟩ := hCt1 c hk.1
            dsimp only [asmSdMapPart, y'] at hk
            rcases hrg with h0 | ⟨_, hlo_p, _⟩
            · omega
            · have := (hlo_p hcp).1; have := h0_lt a hai; omega
          · obtain ⟨_, _, _, _, _, _, hnotP, _⟩ := hCt1 c hk.1; obtain ⟨hpe, hle⟩ := hnotP hcp
            exact hPartDisj 0 (by omega) 3 (by omega) (by decide) a hai (Or.inr ⟨c + 3, hk.1, hpe ▸ hk.2.1, hpe ▸ hle ▸ hk.2.2⟩)
    | 3, 0 =>
      rcases hai with hsl | ⟨k, hk⟩
      · exact hPartDisj 3 (by omega) 0 (by omega) (by decide) a (Or.inl hsl) haj
      · match k with
        | 0 => exact hPartDisj 3 (by omega) 0 (by omega) (by decide) a (Or.inr ⟨0, hk⟩) haj
        | 1 => exact hPartDisj 3 (by omega) 0 (by omega) (by decide) a (Or.inr ⟨1, hk⟩) haj
        | 2 => exact hPartDisj 3 (by omega) 0 (by omega) (by decide) a (Or.inr ⟨2, hk⟩) haj
        | c + 3 =>
          by_cases hcp : c ∈ newComps.map Prod.fst
          · obtain ⟨_, _, _, _, _, _, _, hrg⟩ := hCt1 c hk.1
            dsimp only [asmSdMapPart, y'] at hk
            rcases hrg with h0 | ⟨_, hlo_p, _⟩
            · omega
            · have := (hlo_p hcp).1; have := h0_lt a haj; omega
          · obtain ⟨_, _, _, _, _, _, hnotP, _⟩ := hCt1 c hk.1; obtain ⟨hpe, hle⟩ := hnotP hcp
            exact hPartDisj 3 (by omega) 0 (by omega) (by decide) a (Or.inr ⟨c + 3, hk.1, hpe ▸ hk.2.1, hpe ▸ hle ▸ hk.2.2⟩) haj
    | 1, 2 => rcases hft6' a haj with h0 | ⟨hlo, _⟩; exact (hB1_not_S a hai).2 h0; have := (hB1_not_S a hai).1; omega
    | 2, 1 => rcases hft6' a hai with h0 | ⟨hlo, _⟩; exact (hB1_not_S a haj).2 h0; have := (hB1_not_S a haj).1; omega
    | 1, 3 => exact (hPart3_lt1 a haj).2.1 hai
    | 3, 1 => exact (hPart3_lt1 a hai).2.1 haj
    | 2, 3 => rcases hft6' a hai with h0 | ⟨hlo, _⟩; exact (hPart3_lt1 a haj).2.2.1 h0; have := (hPart3_lt1 a haj).1; omega
    | 3, 2 => rcases hft6' a haj with h0 | ⟨hlo, _⟩; exact (hPart3_lt1 a hai).2.2.1 h0; have := (hPart3_lt1 a hai).1; omega
  have hdisjST' : ∀ a, asmSdFoot restH y' a → ¬ (TR y.vCap5 y.eCap5).foot tourH tx1 a := by
    rintro a ⟨i, hi, hai⟩ hT
    match i with
    | 0 => rcases hftT1 a hT with h0 | ⟨hlo, _⟩; exact hdisjST a ⟨0, by omega, hai⟩ h0; have := hfootSide a ⟨0, by omega, hai⟩; omega
    | 1 => exact hdisjBT1 a hai hT
    | 2 => rcases hft6' a hai with h0 | ⟨hlo, _⟩; exact (hT1_not_S a hT).2 h0; have := (hT1_not_S a hT).1; omega
    | 3 => exact (hPart3_lt1 a hai).2.2.2 hT
  -- Cost bound via `asmFirstNewAct_cost_bound`
  have hCost_total := asmFirstNewAct_cost_bound (TS := TS) (rMul := hRoot.mul) (K := 320 * (capExp + 1) * y.lgFac)
    hI ρ hρ hCrossInv heCapG hCompsNd hCompsMem hSlotMap0 hSlotsRange hFreeSpan0
    hParamsLe hSpanC hSplitEq hLazyBound hInactiveInv hNC_nd hNC_ok hSlotMap1 hBunMatch1
    hOldSlot1 hcostLoop hcSpan
  -- Package all postconditions
  refine ⟨hEnd, st2, _, y', tx1, lazyE, hfullRun,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    hOldSlot1, hSlotMap1, hBunMatch1, hSpanMatch', hSideSlotInv',
    hB_loc.1 hrepB1, hrep6', hT_loc.1 hrepT1, hInvB1,
    (hfr_not_S0 (restH + ASM_SD_NSLOTS) (by omega)
      (fun hS => hPartDisj 2 (by omega) 0 (by omega) (by decide) (restH + ASM_SD_NSLOTS) hS ⟨by omega, by omega⟩)).trans hNSl1,
    hSlotsList', hnSlots1_cap.2.2, ?_, ?_, hMapDisj', hMapNotSl', hPartDisj', hdisjST', ?_,
    by omega, by unfold newActTotalSpace; dsimp only [P] at hhEnd_hi ⊢; rw [hnewSlots_len] at hhEnd_hi; omega, hzEnd, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨hct1_c, _, hct2_c, hnd_c, hcsl_c, hiff_c, _, _⟩ := hCt1 c hc
    have hct_fr : ∀ off, off = 1 ∨ off = 2 → st2.mem (y.ctH + 3 * c + off) = st1.mem (y.ctH + 3 * c + off) := fun off hoff =>
      hfr_not_S0 _ (hfootSide _ ⟨3, by omega, Or.inr ⟨2, by omega, by omega⟩⟩)
        (fun hS => hPartDisj 2 (by omega) 3 (by omega) (by decide) _ hS (Or.inr ⟨2, by omega, by omega⟩))
    refine ⟨(hct_fr 1 (Or.inl rfl)).trans hct1_c, (hct_fr 2 (Or.inr rfl)).trans hct2_c, hnd_c,
      fun bi hbi => by
        dsimp only [y'] at hbi ⊢
        exact ⟨(hfr6' _ (hcsl_not_S0 c hc _ (by omega) (by omega)).1 (hcsl_not_S0 c hc _ (by omega) (by omega)).2).trans (hcsl_c bi hbi).1,
          (hfr6' _ (hcsl_not_S0 c hc _ (by omega) (by omega)).1 (hcsl_not_S0 c hc _ (by omega) (by omega)).2).trans (hcsl_c bi hbi).2⟩,
      hiff_c⟩
  · rintro a ⟨k, hk⟩ hnc hnv
    match k with
    | 0 =>
      dsimp only [asmSdMapPart, y'] at hk
      exact absurd (show a = y.cmpH + (a - y.cmpH) by omega) (hnv (a - y.cmpH) (by omega))
    | 1 =>
      have ha_h : a < h := hfootSide a ⟨3, by omega, Or.inr ⟨1, hk⟩⟩
      have h1' := hfr_not_S0 a ha_h (fun hS => hPartDisj 2 (by omega) 3 (by omega) (by decide) a hS (Or.inr ⟨1, hk⟩))
      have h2' := hfr1 a ha_h
        (fun hB => hPartDisj 1 (by omega) 3 (by omega) (by decide) a hB (Or.inr ⟨1, hk⟩))
        (hdisjST a ⟨3, by omega, Or.inr ⟨1, hk⟩⟩)
        (fun hEq => hPartDisj 0 (by omega) 3 (by omega) (by decide) a ⟨by omega, by omega⟩ (Or.inr ⟨1, hk⟩))
        (fun idx hidx ⟨h1', h2'⟩ => hMapDisj 1 2 (by decide) a hk ⟨by omega, by
          have := (hNC_ok _ (List.getElem_mem hidx)).1; rw [List.getD_eq_getElem newComps (0, 0) hidx] at h2'; omega⟩)
        (fun ⟨h1', h2'⟩ => hMapNotSl a ⟨1, hk⟩ ⟨by omega, by omega⟩)
      rw [h1', h2']; exact hMapWords a (Or.inl hk)
    | 2 =>
      have ha_h : a < h := hfootSide a ⟨3, by omega, Or.inr ⟨2, hk⟩⟩
      have h1' := hfr_not_S0 a ha_h (fun hS => hPartDisj 2 (by omega) 3 (by omega) (by decide) a hS (Or.inr ⟨2, hk⟩))
      dsimp only [asmSdMapPart, y'] at hk
      set c := (a - y.ctH) / 3
      have hc : c < y.comps.length := by omega
      have hrem : (a - y.ctH) % 3 = 1 ∨ (a - y.ctH) % 3 = 2 := by have h0 := hnc c hc; omega
      obtain ⟨hct1_c, hcslW_c, hct2_c, hnd_c, _, hiff_c, _, _⟩ := hCt1 c hc
      rw [h1']
      rcases hrem with hr1 | hr2
      · rw [show a = y.ctH + 3 * c + 1 by omega, hct1_c]; exact hcslW_c
      · rw [show a = y.ctH + 3 * c + 2 by omega, hct2_c]
        have hlen_le : (cslL1 c).length ≤ nSlots1 := by
          rw [← List.toFinset_card_of_nodup hnd_c]
          have hsub : (cslL1 c).toFinset.image Prod.snd ⊆ Finset.range nSlots1 := fun t ht => by
            rcases Finset.mem_image.mp ht with ⟨⟨b, t'⟩, hbt, rfl⟩
            have h1' := (hiff_c b t').mp (List.mem_toFinset.mp hbt)
            rw [h1'.2]; exact Finset.mem_range.mpr (List.mem_range.mp (hSlotMap1.2.1 _ h1'.1))
          have hinj : Set.InjOn Prod.snd ((cslL1 c).toFinset : Set (ℤ × ℕ)) := fun p₁ hp₁ p₂ hp₂ hEq => by
            have h1' := (hiff_c p₁.1 p₁.2).mp (List.mem_toFinset.mp hp₁)
            have h2' := (hiff_c p₂.1 p₂.2).mp (List.mem_toFinset.mp hp₂)
            have hq_eq := hSlotMap1.2.2.2.1 _ h1'.1 _ h2'.1 (by rw [← h1'.2, ← h2'.2]; exact hEq)
            exact Prod.ext (Prod.mk.inj hq_eq).2 hEq
          rw [← Finset.card_image_of_injOn hinj]
          exact (Finset.card_le_card hsub).trans (by simp)
        omega
    | c + 3 =>
      obtain ⟨_, _, _, _, _, _, _, hrg_c⟩ := hCt1 c hk.1
      dsimp only [asmSdMapPart, y'] at hk
      rcases hrg_c with h0 | ⟨_, _, hcells⟩
      · omega
      · rw [hfr6' a (hcsl_not_S0 c hk.1 a hk.2.1 hk.2.2).1 (hcsl_not_S0 c hk.1 a hk.2.1 hk.2.2).2]
        exact (hcells a hk.2.1 hk.2.2).2.2
  · intro k hk
    obtain ⟨hlz_at, hlz_len, hpw, hfin, hlo, hhi, hcells⟩ := hLazy1 k hk
    have hslot_eq : st2.mem (h + 2 * k) = st1.mem (h + 2 * k) ∧ st2.mem (h + 2 * k + 1) = st1.mem (h + 2 * k + 1) :=
      ⟨hfr6' _ (by omega) (fun hS => by have := hfootSide _ ⟨2, by omega, hS⟩; omega),
       hfr6' _ (by omega) (fun hS => by have := hfootSide _ ⟨2, by omega, hS⟩; omega)⟩
    refine ⟨?_, hslot_eq.2.trans hlz_len, hpw, hfin, ?_⟩
    · intro idx hidx
      rw [hslot_eq.1, hfr6' _ (by omega) (fun hS => by have := hfootSide _ ⟨2, by omega, hS⟩; omega)]
      exact hlz_at idx hidx
    · rw [hslot_eq.1]
      refine ⟨hlo, by omega, fun a ha1 ha2 => ⟨(hcells a ha1 ha2).1, ?_, (hcells a ha1 ha2).2⟩⟩
      intro hS; rcases hft6' a hS with h0 | ⟨hlo', _⟩
      · have := hfootSide a ⟨2, by omega, h0⟩; omega
      · omega
  · rintro a ⟨i, hi, hai⟩
    match i with
    | 0 => exact Or.inl ⟨0, by omega, hai⟩
    | 1 => rcases hftB1 a hai with h0 | ⟨hlo, hhi⟩; exact Or.inl ⟨1, by omega, h0⟩; exact Or.inr ⟨hlo, by omega⟩
    | 2 => rcases hft6' a hai with h0 | ⟨hlo, hhi⟩; exact Or.inl ⟨2, by omega, h0⟩; exact Or.inr ⟨by omega, hhi⟩
    | 3 =>
      rcases hai with hsl | ⟨m, hm⟩
      · exact Or.inl ⟨3, by omega, Or.inl hsl⟩
      · match m with
        | 0 => exact Or.inl ⟨3, by omega, Or.inr ⟨0, hm⟩⟩
        | 1 => exact Or.inl ⟨3, by omega, Or.inr ⟨1, hm⟩⟩
        | 2 => exact Or.inl ⟨3, by omega, Or.inr ⟨2, hm⟩⟩
        | c + 3 =>
          by_cases hcp : c ∈ newComps.map Prod.fst
          · obtain ⟨_, _, _, _, _, _, _, hrg⟩ := hCt1 c hm.1
            dsimp only [asmSdMapPart, y'] at hm
            rcases hrg with h0 | ⟨_, hlo_p, _⟩
            · omega
            · have := hlo_p hcp; exact Or.inr ⟨by omega, by omega⟩
          · obtain ⟨_, _, _, _, _, _, hnotP, _⟩ := hCt1 c hm.1; obtain ⟨hpe, hle⟩ := hnotP hcp
            exact Or.inl ⟨3, by omega, Or.inr ⟨c + 3, hm.1, hpe ▸ hm.2.1, hpe ▸ hle ▸ hm.2.2⟩⟩
  · intro a ha; rcases hftT1 a ha with h0 | ⟨hlo, hhi⟩; exact Or.inl h0; exact Or.inr ⟨hlo, by omega⟩
  · intro a ha hnb hns hnt hnsl hct hsl
    exact (hfr_not_S0 a ha hns).trans (hfr1 a ha hnb hnt hnsl hct hsl)
  · have hbp0 : bucketPhi P y.xSpan = specPhi P y.spanS := bucketPhi_eq_specPhi hrepS0
    have hbp1 : bucketPhi P x6' = specPhi P S6' := bucketPhi_eq_specPhi hrep6'
    change _ + (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).phi y.bunH m1 st2.mem +
      320 * (capExp + 1) * y.lgFac * bucketPhi P x6' + (TR y.vCap5 y.eCap5).phi tourH tx1 st2.mem ≤ _
    rw [hB_loc.2.symm, hT_loc.2.symm, hbp0, hbp1]
    dsimp only [P, S6', newSlots, newSet] at hCost_total ⊢
    simp only [Expr.size] at hCost_total ⊢
    omega

end

end MinCostFlow.SparseCore.Program
