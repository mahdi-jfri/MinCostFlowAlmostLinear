module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepHP2
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase3Post

import Mathlib.Tactic

/-!
# Phase 3 in the top proof of the first step (`AssemblyFirstStepHP3`)

The top proof (`asmFirstStep_coreStepAt_of`) asks, as `hP3`, that Phase 3 runs on the arguments
that the driver passes, from the state that Phase 2 leaves (`AsmFsQ₂`), that two words of its
result fit in a word, and that a predicate `Q₃` holds after it. This file chooses `Q₃` and proves
`hP3` (`asmFirstStep_hP3`), on the tour family of `scProg` and its bundle table `scProgB5`.

`Q₃` (`AsmFsQ₃`) keeps the facts of the scan, the post of Phase 2 with its witnesses (the side
record `y'`, the tour state `tx1` and the lazy lists), and the post of Phase 3
(`AsmFirstPhase3Post`) for the bundle table of `y'` and the tour state `tx1`.

The premises of Phase 3 come from these places:
* the model: the readiness of the step and the bounds on the names (`asmFirstStep_phase3_model`,
  from the facts of the old and the new state), the old marks (`asmFirstStep_marks_old`), the
  slots after Phase 2 (`asmFirstStep_phase3_slots`) and the readiness of the bundles
  (`asmFirstStep_phase3_ready`);
* the memory: the bundle table and the tour after Phase 2 (its post), and the inputs, which
  Phases 1 and 2 keep (`asmFirstStep_phase2_keep`, `asmFirstStep_keep12`,
  `asmFirstStep_phase3_inputs`);
* the places: the inputs and the deleted edges lie below the end of the scan, and the new cells
  of Phase 2 lie above it, so they are apart; the bundle table lies below the end of Phase 2
  (`bunTable_place_of_foot`);
* the caps in a word (`asmFirstStep_cap_words`, with `3 capExp ≤ wordExp`).
The procedures that Phase 3 calls are premises (`hpBun` to `hfGrp`),
and so is the room of Phases 2 and 3 (`hSp3`, from the space bound of the step).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

@[expose] public section

/-- **The predicate `Q₃` after Phase 3**: the facts of the scan, the post of Phase 2 with its
witnesses `y'`, `tx1` and `lazyE`, and the post of Phase 3 for the bundle table of `y'`, the tour
state `tx1`, the deleted edges of the scan at `h + 9 + 2 eCap + vCap + 4 words`, and the end of
Phase 2 as the heap pointer. Both outcomes are returns. -/
def AsmFsQ₃ {depth : ℕ} (TS : BundleTourSpec) (impl : SparsifyImpl) (P L capExp limbMul w : ℕ)
    (Ψ : BundleTreeState depth → ℕ) (fVertRoot fInitOne fInitSpan : ℕ) (p : Program)
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) (bBun bTourStep fDelTriples fBuildGroups : ℕ)
    (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (o₂ : Outcome) (st₂ : State) (c₂ : ℕ) (o₃ : Outcome) (st₃ : State)
    (c₃ : ℕ) : Prop :=
  AsmFsScanFacts TRc scProgB5 impl P L capExp limbMul w Ψ A st₁ c₁ ∧
  ∃ hEnd₂, o₂ = .returned hEnd₂ ∧
  ∃ tx₀ : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ, HEq tx₀ A.x.xTour ∧
  ∃ (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (scanBatchFold A.tr.cs.G (asmFirstScanStart A.mem A.x.xRest.cmpH
      A.x.xRest.comps A.tr.activeComps) A.U).newComps.length → List ℕ),
  AsmFirstNewActPostAt TS TRc w depth capExp fVertRoot fInitOne fInitSpan impl p A.ω hRoot
      A.x.restH A.x.tourH (A.h + 9 + 2 * A.x.eCap + A.x.vCap)
      (A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words) st₁.pos A.tr A.ord
      A.x.sTour.marked A.x.xRest tx₀
      (scanBatchFold A.tr.cs.G
        (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps A.tr.activeComps) A.U).newComps
      st₁.mem hEnd₂ st₂ c₂ y' tx1 lazyE ∧
  ∃ hEnd₃, o₃ = .returned hEnd₃ ∧
  AsmFirstPhase3Post w depth y'.slotCap A.x.xRest.vCap5 A.x.xRest.eCap5 bBun bTourStep
      fDelTriples fBuildGroups y'.bunH A.x.tourH A.batch A.words A.edits A.editWords A.spPtr
      (A.h + 9 + 2 * A.x.eCap + A.x.vCap + 4 * A.words) hEnd₂ st₂.pos p A.ω
      (fun _ => canonicalSparsify impl) A.tr A.U A.ord A.ed
      (scanBatchFold A.tr.cs.G
        (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps A.tr.activeComps) A.U).delEdges
      y'.slotOf y'.bunS y'.xBun tx1 st₂.mem hEnd₃ st₃ c₃

end

public section

set_option maxHeartbeats 3200000 in
/-- **`hP3` of the top proof.** On the tour family of `scProg` and its bundle table, with a word
exponent of at least `3 capExp` (`hwe`), the procedures of Phase 3 in `p`, and room for
Phases 2 and 3 after the scan (`hSp3`): from `AsmFsQ₂`, Phase 3 runs on the arguments that the
driver passes, the end of Phase 2 and the place of the descriptors that Phase 3 writes are below
`2 ^ w - 1`, and `AsmFsQ₃` holds after it. -/
theorem asmFirstStep_hP3 {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTour bOut bCopy bTourStep fDelTriples fBuildGroups : ℕ}
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot)
    (hpBun : p.HasAt bBun (bundleProcs bBun (tourOp bTour 4) (tourOp bTour 12) (tourOp bTour 10)))
    (hpT : HasTourProcs p bTour)
    (hpO : OutProcsAt p bOut (tourOp bTour 8) (tourOp bTour 7) (tourOp bTour 11) (tourOp bTour 9))
    (hpC : p.HasAt bCopy [copyWords])
    (hpTS : p.HasAt bTourStep (asmFirstTourBlockProcs bTourStep bTour bOut bCopy))
    (hfDel : p.procs[fDelTriples]? =
      some (asmFirstBuildDelTriplesStmt (bBun + bundleIdxReadParent)))
    (hfGrp : p.procs[fBuildGroups]? = some (asmFirstBuildGroupsStmt (bBun + bundleOffSort)))
    (hwe : 3 * capExp ≤ wordExp) (space : ℕ → ℕ)
    (hSp3 : ∀ A, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words +
        newActTotalSpace TS hRoot.querySpace impl w A.x.xRest A.tr A.ord
          (scanBatchFold A.tr.cs.G (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
            A.tr.activeComps) A.U).newComps +
        asmFirstPhase3Space A.x.xRest.slotCap A.x.vCap A.x.eCap A.words A.editWords
          (scanBatchFold A.tr.cs.G (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
            A.tr.activeComps) A.U).delEdges.length < 2 ^ w) :
    ∀ A st₁ c₁ o₂ st₂ c₂, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      AsmFsQ₂ TS TRc impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot A st₁ c₁
        o₂ st₂ c₂ →
      ∃ o₃ st₃ c₃, Runs w p A.ω
          (asmFirstPhase3Stmt fDelTriples fBuildGroups (bTourStep + 2) (bBun + bundleIdxStep))
          (startState [A.x.xRest.bunH, A.x.xRest.slotCap, A.x.vCap,
            A.x.tourH, A.batch, A.words, A.edits, A.editWords, A.spPtr,
            A.h + 9 + 2 * A.x.eCap + A.x.vCap + 4 * A.words, st₁.mem (A.h + 7), o₂.value]
            st₂.mem st₂.pos) o₃ st₃ c₃ ∧
        o₂.value + 1 < 2 ^ w ∧ st₃.mem (o₂.value + 1) + 1 < 2 ^ w ∧
        AsmFsQ₃ TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
          bTourStep fDelTriples fBuildGroups A st₁ c₁ o₂ st₂ c₂ o₃ st₃ c₃ := by
  intro A st₁ c₁ o₂ st₂ c₂ hA hQ₂
  have hsp := hSp3 A hA
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  obtain ⟨vCap, eCap, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour, xTour,
    restH, xRest⟩ := x
  unfold AsmFsPre AsmFsPreRaw at hA
  unfold AsmFsQ₂ AsmFsScanFacts at hQ₂
  dsimp only at hA hQ₂ hsp ⊢
  obtain ⟨hM0, hN0, -, -, hw16, hW, -, -, -, hR, hFacts, hBat, hU, hCaps, hEd, hOB, hOVF, hOFB,
    -, -, hSpE, hBin, hEin, -, hSin, hfoot, hwords, -, -⟩ := hA
  have hOld := asmBrModelFacts_of_rep hR
  obtain ⟨hRA, hv, he, -, -, -, hsl, -⟩ := hR
  dsimp only at hv he hsl hOld
  subst hv he
  obtain ⟨⟨hM, h6, h7, hc₁⟩, hEnd₂, rfl, tx₀, hTx, y', tx1, lazyE, hP2⟩ := hQ₂
  obtain rfl : xTour = tx₀ := (eq_of_heq hTx).symm
  have hP2c := hP2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTourRep, hMk, hSide, -, hcap, -,
    hDisj⟩ := hRA
  dsimp only at hcap
  rw [hM0, hN0] at hcap
  have hSide' := hSide
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMod⟩ := hSide'
  obtain ⟨-, -, -, -, -, hk, ⟨C_lsst, ℓ₀, hI, -⟩, -, -, -, -, -, -, -, -, -, -, hkB, -, hInact,
    -, -, hPart, -⟩ := hMod
  have hTR_loc : ∀ v e, (TRc v e).Local := fun v e =>
    asmTourRepWithPot_local tourAsmRep_local (bundleScanPotMul tourBundleSpec) v e
  have hfootSide : ∀ a, asmSdFoot restH xRest a → a < h := fun a ha => hfoot a ⟨5, by decide, ha⟩
  have hfootT : ∀ a, (TRc xRest.vCap5 xRest.eCap5).foot tourH xTour a → a < h :=
    fun a ha => hfoot a ⟨4, by decide, ha⟩
  have hdisjST : ∀ a, asmSdFoot restH xRest a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xTour a :=
    fun a hs ht => hDisj 5 (by decide) 4 (by decide) (by decide) a hs ht
  have hUW : 2 * U.length ≤ words - 1 := batchBodyAt_len_le hBat.1.2.2
  obtain ⟨-, -, -, -, -, -, -, -, hok, -, hset, -, hdel, hdlen⟩ :=
    asmFirstStep_phase2_pre hTR_loc hSide hTourRep.2.2 hfootSide hfootT hdisjST hU hUW hM
  obtain ⟨-, hbunH, -, -, -, hslc, hv5, he5, -, -, -, -, -, -, -, -, -, hkB', -, -, -, -,
    hSlot, hMatch, -, hSlotInv, hRepB, -, hRepT, hinv0, -, -, hnsl, -, -, -, -, -, hdisj', -,
    hlen2, hEndle, hZ2, hfootS', hfootT', hfr, -⟩ := hP2
  -- the words of the caps, and the room
  obtain ⟨hwsq, hpk, -, -, hslW⟩ := asmFirstStep_cap_words hW hcap hwe hsl
  have hScanPos : 0 < asmFirstScanBatchSpace xRest.vCap5 xRest.eCap5 words := by
    unfold asmFirstScanBatchSpace; omega
  have hhw : h < 2 ^ w := hwords h (by simp)
  have htourW : tourH < 2 ^ w := by
    have := hfootT tourH (asmTourRepWithPot_foot_self tourAsmRep_handle_foot _ _ _ tourH xTour)
    omega
  have hE2w : hEnd₂ < 2 ^ w := by omega
  -- the model premises
  obtain ⟨hready, hRlt, hEold, hEnew, hDcap⟩ :=
    asmFirstStep_phase3_model (fun _ => canonicalSparsify impl) hOld hFacts hU hOB hCaps hdel
  have hMarks := asmFirstStep_marks_old hTourRep.2.1 hMk
  have hNew : ∀ C ∈ (List.map (fun q => xRest.comps.getD q.1 ∅) (scanBatchFold tr.cs.G
      (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps) U).newComps).toFinset,
      C ∈ components tr.cs.G₀ ∧ C ∉ tr.activeComps := by
    intro C hC
    rw [hset] at hC
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hC
    exact ⟨touchedCompsBatch_subset _ _ h1, h2⟩
  have hFree := hSlotInv.2.2.1
  rw [← hslc] at hSlot
  obtain ⟨hMatch0, hBunNone, hSlotInj⟩ := asmFirstStep_phase3_slots
    (tr' := (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord
      (applyOrdEdits ord ed)).state)
    (activePairs_mid_eq _ tr U ord _ hset) rfl hSlot hMatch hFree
  have hBReady := asmFirstStep_phase3_ready (ord' := applyOrdEdits ord ed) hI hk hU hOB hPart
    hInact hNew hSlot hMatch hFree
  -- the inputs, which Phases 1 and 2 keep
  have hK2keep := asmFirstStep_phase2_keep (fun q hq => (hok q hq).1) hnsl hfr
  have hK := asmFirstStep_keep12 hM hK2keep (by omega)
  have hK2 : ∀ a, h ≤ a →
      a < h + 6 + asmFirstScanBatchSpace xRest.vCap5 xRest.eCap5 words →
      st₂.mem a = st₁.mem a := fun a h1 h2 =>
    hK2keep a h2 (fun hs => by have := hfootSide a hs; omega)
      (fun ht => by have := hfootT a ht; omega)
  have hdlenW : (scanBatchFold tr.cs.G
      (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps) U).delEdges.length ≤ words := by
    refine le_trans hdlen ?_
    omega
  have hout : ∀ a n, InputAt w mem
      ((asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).foot b
        ⟨xRest.vCap5, xRest.eCap5, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour,
          xTour, restH, xRest⟩) a n h →
      ∀ i < n, ¬ asmSdFoot restH xRest (a + i) ∧
        ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xTour (a + i) :=
    fun a n hin i hi => ⟨fun hs => (hin.2 i hi).2 ⟨5, by decide, hs⟩,
      fun ht => (hin.2 i hi).2 ⟨4, by decide, ht⟩⟩
  obtain ⟨hBatch', hEdits', hSpAt', hDelAt'⟩ := asmFirstStep_phase3_inputs hM hK hK2 le_rfl
    hdlenW hBat hEd hSpE (hout _ _ hBin) hBin.1 (hout _ _ hEin) hEin.1 (hout _ _ hSin) hSin.1
  -- the places of the bundle table and the tour after Phase 2
  have hBf : ∀ a, (bunTableHeadroomRep y'.slotCap y'.vCap5 y'.eCap5 y'.kB).foot y'.bunH y'.xBun a →
      a < hEnd₂ := fun a ha => by
    rcases hfootS' a ⟨1, by decide, ha⟩ with hs | ⟨_, h2⟩
    · have := hfootSide a hs
      omega
    · exact h2
  have hdisjBT : ∀ a, (bunTableHeadroomRep y'.slotCap y'.vCap5 y'.eCap5 y'.kB).foot y'.bunH
      y'.xBun a → ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH tx1 a :=
    fun a hb ht => hdisj' a ⟨1, by decide, hb⟩ ht
  rw [hv5, he5, hkB', hkB] at hRepB hBf hdisjBT
  obtain ⟨htbl, hblk⟩ := bunTable_place_of_foot hBf hE2w
  have hTf : ∀ a, (TRc xRest.vCap5 xRest.eCap5).foot tourH tx1 a → a < hEnd₂ := fun a ha => by
    rcases hfootT' a ha with ht | ⟨_, h2⟩
    · have := hfootT a ht
      omega
    · exact h2
  have hapart : ∀ a0 n, InputAt w mem
      ((asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).foot b
        ⟨xRest.vCap5, xRest.eCap5, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour,
          xTour, restH, xRest⟩) a0 n h →
      ∀ a, a0 ≤ a → a < a0 + n → ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH tx1 a := by
    intro a0 n hin a h1 h2 ht
    rcases hfootT' a ht with ht0 | ⟨h3, _⟩
    · exact (hout _ _ hin (a - a0) (by omega)).2 (by rwa [Nat.add_sub_cancel' h1])
    · have := hin.1
      omega
  have hDF : ∀ a, h + 9 + 2 * xRest.eCap5 + xRest.vCap5 + 4 * words ≤ a →
      a < h + 9 + 2 * xRest.eCap5 + xRest.vCap5 + 4 * words + (scanBatchFold tr.cs.G
        (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps) U).delEdges.length →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH tx1 a := by
    intro a h1 h2 ht
    rcases hfootT' a ht with ht0 | ⟨h3, _⟩
    · have := hfootT a ht0
      omega
    · unfold asmFirstScanBatchSpace at h3
      omega
  rw [← hslc] at hsp
  obtain ⟨hEnd₃, st₃, c₃, hpost3⟩ := asmFirstPhase3_runs_post (pos := st₂.pos) (ω := ω)
    (bunH := y'.bunH) (h := hEnd₂) (delEdges := (scanBatchFold tr.cs.G
      (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps) U).delEdges)
    hpBun hpT hpO hpC hpTS hfDel hfGrp
    (fun _ => canonicalSparsify impl) hready hOFB hOVF hRlt hEold hEnew hdel hDcap hMarks hinv0
    hMatch0 hBunNone hSlotInj hBReady hRepB hRepT hBatch' hEdits' hSpAt' hDelAt' hw16 hwsq hpk
    htourW (by rw [hslc]; exact hslW) (by have := hBin.1; omega) (by have := hEin.1; omega)
    (by have := hSin.1; omega)
    (by unfold asmFirstScanBatchSpace at hlen2; omega) htbl hblk hBf hTf hdisjBT
    (hapart _ _ hBin) (hapart _ _ hEin) (hapart _ _ hSin) hDF hZ2 (by omega)
  have hp3 := hpost3
  obtain ⟨_, _, _, _, _, _, _, hrun3, -, -, -, -, -, -, -, -, -, -, hd12, -, hd14, -, -, -, -, -, -,
    h21, h22, -, -, -, -⟩ := hp3
  refine ⟨.returned hEnd₃, st₃, c₃, ?_, ?_, ?_, ⟨hM, h6, h7, hc₁⟩, hEnd₂, rfl, xTour, HEq.rfl, y',
    tx1, lazyE, hP2c, hEnd₃, rfl, hpost3⟩
  · rw [h7, ← hbunH, ← hslc]
    exact hrun3
  · show hEnd₂ + 1 < 2 ^ w
    omega
  · show st₃.mem (hEnd₂ + 1) + 1 < 2 ^ w
    omega

end

end MinCostFlow.SparseCore.Program
