module

public import MinCostFlow.SparseCore.Program.AssemblyFsOpen
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSpaceTotal

import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue11
import MinCostFlow.SparseCore.Program.AssemblyFirstWalkBank
import Mathlib.Tactic

/-!
# The spanners and the tasks of Phase 4 are valid (`AssemblyFirstStepSpaceTasks`)

The space bound of Phase 4 (`asmFirstStepSpace_le_poly_std`) needs two facts on the spanners of
Phase 2 and the tasks of Phase 3: every history held by the spanners is valid (`P4HistValid`),
and every task is valid on its slot (`P4TaskValid`) with a batch of at most the space of Phase 3.
This file proves them (`asmFirstStep_p4_spaceFacts`), with the bound of the end of Phase 3 and
the equal caps of the side record before and after Phase 2.

* A history in a slot is valid because the rep of the spanners says so (`DSRepAt`). The slot is
  the slot of an active pair (the slot invariant of Phase 2), so its initial graph is the initial
  graph of the bundle of the pair. That graph has at most `2 m` vertices (the bound of the
  branch), and its edges lie below `eCap`. With `2 eCap + splitB + 1 ≤ spV` (the side model),
  the vertices and the splits fit in `spV`.
* A task is valid because Phase 4 gets `DSUpdatePre` for it (the first part of `AsmFsP4Open`,
  proved by `asmFirstStep_hOpen`). The batch of the task lies in the cells of Phase 3, so its
  length is at most the space of Phase 3.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

/-- The graph of a valid history is its initial graph after its flat batch (a copy of the
private lemma of `AssemblyFsOpen`). -/
private lemma dsHist_G_eq_applyBatch' {P : DSParams} {d : DSHist}
    (hL : 1 ≤ P.L) (hVG₀ : d.G₀.IsValid) (hGm₀ : d.G₀.m ≤ P.mMax)
    (hbv : d.G₀.BatchIsValid d.flat) (hds : ∀ u ∈ d.flat, isDelOrSplit u) :
    (d.state P).G = d.G₀.applyBatch d.flat := by
  have hq1 : 1 ≤ d.q P := le_trans (by decide) (two_le_phaseBase _ _)
  have hI := (runInv_all hVG₀ hL hq1 hGm₀ (canonicalSparsify_spec_absorb P.impl P.mMax)
    hbv hds d.flat.length le_rfl).1.G_eq
  simpa [DSHist.state, List.take_length] using hI

public section

set_option maxHeartbeats 4000000 in
/-- **The facts of the space of Phase 4**, after Phases 2 and 3: every history in the spanners
`y'.spanS` is valid with room for its vertices and splits; every task is valid with a batch of at
most the space of Phase 3; the touched slots are at most `slotCap`; the end of Phase 3 is below
the start plus the spaces of Phases 1 to 3; and the side record keeps its caps in Phase 2. The
premise `hOut` is the first part of `AsmFsP4Open`. -/
theorem asmFirstStep_p4_spaceFacts {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {space : ℕ → ℕ}
    (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (st₂ : State) (c₂ : ℕ) (st₃ : State) (c₃ hEnd₂ : ℕ)
    (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ)
    (hEnd₃ : ℕ) (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (splitPtr outDescPtr : ℕ) (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End))
    (touched : List ℕ)
    (hA : AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A)
    (hQ₃ : AsmFsQ₃At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃
      tx_pot' splitPtr outDescPtr mk' Mset Ys touched)
    (hOut : AsmFirstBunStepOut (asmBrSP impl w depth y') y'.cap y'.spanS (outDescPtr + 1) hEnd₃
      (p4TasksOf st₃.mem (outDescPtr + 1) touched.length) st₃.mem) :
    let sbF := scanBatchFold A.tr.cs.G
      (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps A.tr.activeComps) A.U
    (∀ (j : Fin y'.cap) (d : DSHist), y'.spanS j = some d →
      P4HistValid (asmBrSP impl w depth y') d ∧
      d.G₀.n + (asmBrSP impl w depth y').splitBound ≤ (asmBrSP impl w depth y').vCap) ∧
    (∀ t ∈ p4TasksOf st₃.mem (outDescPtr + 1) touched.length,
      P4TaskValid (asmBrSP impl w depth y') y'.spanS st₃.mem t ∧
      t.W ≤ asmFirstPhase3Space A.x.xRest.slotCap A.x.vCap A.x.eCap A.words A.editWords
        sbF.delEdges.length) ∧
    touched.length ≤ A.x.xRest.slotCap ∧
    hEnd₃ ≤ A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words +
      newActTotalSpace TS hRoot.querySpace impl w A.x.xRest A.tr A.ord sbF.newComps +
      asmFirstPhase3Space A.x.xRest.slotCap A.x.vCap A.x.eCap A.words A.editWords
        sbF.delEdges.length ∧
    y'.cap = A.x.xRest.cap ∧ y'.spV = A.x.xRest.spV ∧ y'.spE = A.x.xRest.spE ∧
    y'.mMax = A.x.xRest.mMax ∧ y'.splitB = A.x.xRest.splitB := by
  intro sbF
  obtain ⟨hScanF, tx₀, hTx, hP2, hP3⟩ := hQ₃
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  obtain ⟨vCap, eCap, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour, xTour,
    restH, xRest⟩ := x
  unfold AsmFsPre AsmFsPreRaw at hA
  unfold AsmFsScanFacts at hScanF
  dsimp only [AsmFsArgs.newComps, sbF] at hA hScanF hP2 hP3 hOut ⊢
  obtain ⟨-, -, hd1, -, -, -, -, -, hUB', hR, hFacts, hBat, hU, -, -, -, -, -, -, -, -,
    -, -, -, -, hfoot, -, -, -, -⟩ := hA
  obtain ⟨hRA, hv, he, -, -, -, -, -⟩ := hR
  dsimp only at hv he
  subst hv he
  obtain ⟨hM, -, -, -⟩ := hScanF
  obtain rfl : xTour = tx₀ := (eq_of_heq hTx).symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTourRep, -, hSide, -, -, -,
    hDisj⟩ := hRA
  have hSide' := hSide
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMod⟩ := hSide'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hspE_le0, -, -, -, -, -, -, -, -, -,
    hspV_ge0, -⟩ := hMod
  dsimp only at hspE_le0 hspV_ge0
  have hTR_loc : ∀ v e, (TRc v e).Local := fun v e =>
    asmTourRepWithPot_local tourAsmRep_local (bundleScanPotMul tourBundleSpec) v e
  have hfootSide : ∀ a, asmSdFoot restH xRest a → a < h := fun a ha => hfoot a ⟨5, by decide, ha⟩
  have hfootT : ∀ a, (TRc xRest.vCap5 xRest.eCap5).foot tourH xTour a → a < h :=
    fun a ha => hfoot a ⟨4, by decide, ha⟩
  have hdisjST : ∀ a, asmSdFoot restH xRest a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xTour a :=
    fun a hs ht => hDisj 5 (by decide) 4 (by decide) (by decide) a hs ht
  have hUW : 2 * U.length ≤ words - 1 := batchBodyAt_len_le hBat.1.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hset, -, -, -⟩ :=
    asmFirstStep_phase2_pre hTR_loc hSide hTourRep.2.2 hfootSide hfootT hdisjST hU hUW hM
  obtain ⟨-, -, -, -, -, hslc, -, -, hcap5, hsplitB5, hspV5, hspE5, hmMax5, -, -, -, -, -,
    -, -, -, -, hSlotN, -, hspanS, hSlotInv, -, hRepS, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hEnd₂le⟩ := hP2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h2d, -, hnd3, hlt3, -, hdesc3, -, -, -,
    hEnd₃le, -⟩ := hP3
  set sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify impl
  set ord' := applyOrdEdits ord ed
  set info := stepBundleTree sp tr U ord ord'
  set SP := asmBrSP impl w depth y'
  set newSet : Finset (Finset ℕ) :=
    ((scanBatchFold tr.cs.G (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps)
      U).newComps.map fun q => xRest.comps.getD q.1 ∅).toFinset
  set tr_mid : BundleTreeState depth := { tr with activeComps := tr.activeComps ∪ newSet }
  have hActMid : activePairs tr_mid = activePairs info.state := by
    ext ⟨C, b⟩
    simp only [mem_activePairs, tr_mid, info, stepBundleTree, hset, Finset.mem_union,
      Finset.mem_sdiff]
  -- the histories in the slots
  have hSlotValid : ∀ (j : Fin y'.cap) (d : DSHist), y'.spanS j = some d →
      P4HistValid SP d ∧ d.G₀.n + SP.splitBound ≤ SP.vCap := by
    intro j d hjd
    have hslot := hRepS.1 j
    rw [hjd] at hslot
    cases hx : y'.xSpan.slots j with
    | none => rw [hx] at hslot; exact hslot.elim
    | some bm =>
      rw [hx] at hslot
      obtain ⟨-, ⟨-, hdsRep, -⟩, -⟩ := hslot
      obtain ⟨-, hVG₀, hGm₀, hG₀E, hBV, hds, -⟩ := hdsRep
      refine ⟨⟨hVG₀, hGm₀, hG₀E, hBV, hds⟩, ?_⟩
      -- the slot is the slot of an active pair
      have hjs : j.1 ∈ y'.slots := by
        by_contra hns
        rw [hSlotInv.2.2.2 j hns] at hjd
        cases hjd
      obtain ⟨q, hq_mid, hqs⟩ := hSlotN.2.2.1 j.1 hjs
      obtain ⟨hsS, d₀, hSd₀, -, hdG₀, -⟩ := hspanS q hq_mid
      have hdd : d = d₀ := by
        have hj' : (⟨y'.slotOf q, hsS⟩ : Fin y'.cap) = j := Fin.ext hqs
        rw [hj', hjd] at hSd₀
        exact Option.some.inj hSd₀
      subst hdd
      have hq : q ∈ activePairs info.state := hActMid ▸ hq_mid
      have hC' : q.1 ∈ components info.state.cs.G₀ := hFacts.2.2.1.1 (mem_activePairs.mp hq).1
      have hG₀_n2m : d.G₀.n ≤ 2 * d.G₀.m := by rw [hdG₀]; exact (hUB'.2 q.1 hC' q.2).2.2.1
      have hG₀E_x : ∀ e ∈ d.G₀.E, e < xRest.eCap5 := fun e he =>
        lt_of_lt_of_le (hG₀E e he) (by show y'.spE ≤ xRest.eCap5; omega)
      have hG₀_m_le_eCap : d.G₀.m ≤ xRest.eCap5 := by
        calc d.G₀.E.card ≤ (Finset.range xRest.eCap5).card :=
              Finset.card_le_card fun e he => Finset.mem_range.mpr (hG₀E_x e he)
          _ = xRest.eCap5 := Finset.card_range _
      show d.G₀.n + y'.splitB ≤ y'.spV
      omega
  refine ⟨hSlotValid, ?_, ?_, ?_, hcap5, hspV5, hspE5, hmMax5, hsplitB5⟩
  · -- the tasks
    intro t ht
    refine ⟨?_, ?_⟩
    · intro hs' d' hSd' _
      obtain ⟨hs, d, hSd, hPre⟩ := hOut.hslots t ht
      have hdd : d' = d := by
        have h1 : y'.spanS ⟨t.slot, hs⟩ = some d := hSd
        have hfin : (⟨t.slot, hs⟩ : Fin y'.cap) = ⟨t.slot, hs'⟩ := rfl
        rw [hfin, hSd'] at h1
        exact Option.some.inj h1
      subst hdd
      obtain ⟨⟨hVG₀, hGm₀, hG₀E, hBV, hds⟩, hn⟩ := hSlotValid _ _ hSd'
      obtain ⟨b', bp, W, h', hargs, -, -, hW, -, -, hUV, hUds, -, hsc, -⟩ := hPre
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, hbp, hWe, -⟩ := hargs
      subst hbp hWe
      have hGeq_d : (d'.state SP).G = d'.G₀.applyBatch d'.flat :=
        dsHist_G_eq_applyBatch' hd1 hVG₀ hGm₀ hBV hds
      refine ⟨hVG₀, hGm₀, hG₀E, hn, batchIsValid_append.mpr ⟨hBV, hGeq_d ▸ hUV⟩, ?_, hsc, ?_⟩
      · intro u hu
        rcases List.mem_append.mp hu with h1 | h2
        · exact hds u h1
        · exact hUds u h2
      · show (opBatch SP d' [0, t.batchPtr, t.W, hEnd₃] st₃.mem).2.sum ≤ t.W
        omega
    · obtain ⟨i, hi, rfl⟩ := mem_p4TasksOf ht
      obtain ⟨-, bp, totW, -, htb, htw, hbp1, hbp2, -⟩ := hdesc3 i hi
      dsimp only
      rw [htw]
      rw [hslc] at hEnd₃le
      omega
  · have := asmFirstStep_touched_len hnd3 hlt3
    omega
  · rw [hslc] at hEnd₃le
    omega

end

end MinCostFlow.SparseCore.Program
