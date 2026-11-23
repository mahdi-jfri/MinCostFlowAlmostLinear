module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNCDefs
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSideSpan

import MinCostFlow.SparseCore.Program.AssemblyFirstStepEmbStep
import MinCostFlow.SparseCore.Program.AssemblyFirstStepSideSpan
import MinCostFlow.SparseCore.Program.AssemblyFirstStepHP4
import MinCostFlow.SparseCore.Program.AssemblyFirstStepNC
import Mathlib.Tactic

/-!
# The embedding table after the first step (`AssemblyFirstStepEmb`)

After Phase 4 the embedding table must cover the core edges of the new state and hold their new
walks (`AsmFsEmbGoal`, conjuncts 2 and 3 of the post). This file proves it
(`asmFirstStep_hEmb_of`), with no premise.

The view after Phase 4 is the view of the post of Phase 4 (its post 6). Its model is
`p4Emb_model` (`AssemblyFirstStepEmbStep.lean`), whose hypotheses come from the same places as in
the proof of `hP4` (`AssemblyFirstStepHP4.lean`): the slot model of Phase 4 from the posts of
Phases 2, 3 and 4, the facts of the model from the side model of the branch before the step, and
the old view from the rep of the branch. The histories of the spanners after the tasks are valid
by the rep of the spanners after Phase 4 (`bucketSpannerRep_slot_valid`).

With the side goal (`asmFirstStep_hSide_full`), this leaves only the space goal in `hNC`
(`asmFirstStep_hNC_full`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

public section

/-- **A history held by the spanners is valid**: its initial graph is valid and below the edge
cap of the parameters, and its batches are valid deletions and splits, as the rep of the slot
(`DSRepAt`) says. -/
theorem bucketSpannerRep_slot_valid {P : DSParams} {cap tbl : ℕ} {S : BucketSpannerState cap}
    {x : BucketSpannerMeta P.L cap} {mem : ℕ → ℕ} (h : (bucketSpannerRep P cap).rep tbl S x mem)
    {j : Fin cap} {d : DSHist} (hj : S j = some d) :
    d.G₀.IsValid ∧ d.G₀.m ≤ P.mMax ∧ d.G₀.BatchIsValid d.flat ∧ ∀ u ∈ d.flat, isDelOrSplit u := by
  have hslot := h.1 j
  rw [hj] at hslot
  cases hx : x.slots j with
  | none =>
    rw [hx] at hslot
    exact hslot.elim
  | some bm =>
    rw [hx] at hslot
    obtain ⟨-, ⟨-, hdsRep, -⟩, -⟩ := hslot
    obtain ⟨-, hV, hm, -, hBV, hds, -⟩ := hdsRep
    exact ⟨hV, hm, hBV, hds⟩

set_option maxHeartbeats 8000000 in
/-- **The embedding table after the step** (`AsmFsEmbGoal`). -/
theorem asmFirstStep_hEmb_of {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {space : ℕ → ℕ} :
    AsmFsEmbGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne fInitSpan p
      hRoot bBun bTourStep fDelTriples fBuildGroups K space := by
  intro A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr
    mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ
  obtain ⟨⟨hScanF, tx₀, hTx, hP2, hP3⟩, hP4⟩ := hQ
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  obtain ⟨vCap, eCap, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour, xT0,
    restH, xRest⟩ := x
  unfold AsmFsPre AsmFsPreRaw at hA
  unfold AsmFsScanFacts at hScanF
  dsimp only [AsmFsArgs.newComps] at hA hScanF hP2 hP3 hP4 hTx ⊢
  obtain ⟨-, -, hd1, -, -, -, -, -, -, hR, hFacts, hBat, hU, -, -, hOB, -, -, -, -, -, -, -, -, -,
    hfoot, -, -, -, -⟩ := hA
  obtain ⟨hRA, hv, he, -, -, -, -, -⟩ := hR
  dsimp only at hv he
  subst hv he
  obtain ⟨hM, -, -, -⟩ := hScanF
  obtain rfl : xT0 = tx₀ := (eq_of_heq hTx).symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdomOld, hembOld, -, hTourRep, -, hSide, -,
    -, -, hDisj⟩ := hRA
  have hSide' := hSide
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMod⟩ := hSide'
  obtain ⟨hSMO, -, -, hModOld, -, hk, ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩, -, -, -, -, hBD, -, -, -, -, -, -,
    hSlotInvOld, hInact, -, hInactDyn, hPart, hDynGOld, -⟩ := hMod
  have hTR_loc : ∀ v e, (TRc v e).Local := fun v e =>
    asmTourRepWithPot_local tourAsmRep_local (bundleScanPotMul tourBundleSpec) v e
  have hfootSide : ∀ a, asmSdFoot restH xRest a → a < h := fun a ha => hfoot a ⟨5, by decide, ha⟩
  have hfootT : ∀ a, (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a → a < h :=
    fun a ha => hfoot a ⟨4, by decide, ha⟩
  have hdisjST : ∀ a, asmSdFoot restH xRest a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a :=
    fun a hs ht => hDisj 5 (by decide) 4 (by decide) (by decide) a hs ht
  have hUW : 2 * U.length ≤ words - 1 := batchBodyAt_len_le hBat.1.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hset, -⟩ :=
    asmFirstStep_phase2_pre hTR_loc hSide hTourRep.2.2 hfootSide hfootT hdisjST hU hUW hM
  obtain ⟨-, -, -, -, -, hslc, -, -, hcap5, -, -, -, -, -, -, -, -, -, -, -, hslots', hkeepSlot,
    hSlotN, hMatch, hspanS, hSlotInv, -⟩ := hP2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hnd3, -, -, hdesc3, hunt3, hnone3, -⟩ := hP3
  obtain ⟨hqs, hqsOK, hns, hnsOK, hRepX', hE4, -⟩ := hP4
  have hNew : ∀ C ∈ (List.map (fun q => xRest.comps.getD q.1 ∅) (scanBatchFold tr.cs.G
      (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps) U).newComps).toFinset,
      C ∈ components tr.cs.G₀ ∧ C ∉ tr.activeComps := by
    intro C hC
    rw [hset] at hC
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hC
    exact ⟨touchedCompsBatch_subset _ _ h1, h2⟩
  have hSlot' : SlotMapOK { tr with activeComps := tr.activeComps ∪
      (List.map (fun q => xRest.comps.getD q.1 ∅) (scanBatchFold tr.cs.G (asmFirstScanStart mem
          xRest.cmpH xRest.comps tr.activeComps) U).newComps).toFinset } y'.slotCap y'.cap y'.slots
      y'.slotOf := by
    rw [hslc, hcap5]
    exact hSlotN
  have hBReady := asmFirstStep_phase3_ready (ord' := applyOrdEdits ord ed) hI hk hU hOB hPart
    hInact hNew hSlot' hMatch hSlotInv.2.2.1
  have hT := asmFirstStep_p4_slotTasks (P := asmBrSP impl w depth y') hset
    (fun q hq => by
      obtain ⟨hs, d, h1, h2, -⟩ := hspanS q hq
      exact ⟨hs, d, h1, h2⟩)
    hSMO hSlotInvOld.2.1 hSlotN hslots' hkeepSlot hSlot' hMatch hSlotInv.2.2.1 hBReady
    (p4_dynGraphEq (fun _ => canonicalSparsify impl) (U := U) (ord' := applyOrdEdits ord ed)
      hInact hInactDyn hDynGOld)
    hnd3 hdesc3 hunt3 hnone3
  have hSM := hT.model hqs hqsOK hns hnsOK
  obtain ⟨-, -, hModN, hBDN, -⟩ := hFacts
  rw [← hqs] at hRepX' hE4
  have hModel := p4Emb_model (P := asmBrSP impl w depth y') rfl hI hU hModOld hBD hModN hBDN
    (asmFirstStep_dynG_new (fun _ => canonicalSparsify impl) hI hU hOB hk hInact hInactDyn hPart
      hDynGOld)
    (asmFirstStep_inactiveBkts hI hρ hInact)
    (asmFirstStep_bunEdges (fun _ => canonicalSparsify impl) hI hk hU hOB hPart hInact)
    (asmFirstStep_dynG_old hDynGOld) hd1
    (fun j d hj => bucketSpannerRep_slot_valid hRepX' hj) hSM hdomOld hembOld
  rw [hE4.1]
  exact hModel

/-- **`hNC` with only the space goal left**: the side goal holds from `hp`, `hWB` and `hVerts`
(`asmFirstStep_hSide_full`), and the embedding goal holds (`asmFirstStep_hEmb_of`). -/
theorem asmFirstStep_hNC_full {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {ysMul : ℕ} {space : ℕ → ℕ} (hys : 4 * capExp + 5 ≤ ysMul) (hp : 1 ≤ max impl.p_s impl.p_t)
    (hWB : ∀ A, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      A.x.xRest.spV + A.x.xRest.spE + 2 < 2 ^ w ∧
      (36 * (A.x.xRest.spV + 2 * A.x.xRest.spE + 1)) ^ impl.cw < 2 ^ w)
    (hVerts : ∀ A, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      ∀ v ∈ batchVerts A.U, v < A.x.vCap)
    (hSp : AsmFsSpaceGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne fInitSpan p
      hRoot bBun bTourStep fDelTriples fBuildGroups K space) :
    AsmFsNCGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K ysMul space :=
  asmFirstStep_hNC_of hys (asmFirstStep_hSide_full hp hWB hVerts) asmFirstStep_hEmb_of hSp

end

end MinCostFlow.SparseCore.Program
