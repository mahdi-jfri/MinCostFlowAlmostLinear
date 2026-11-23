module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepTop
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActPost

import Mathlib.Tactic

/-!
# Phase 2 in the top proof of the first step (`AssemblyFirstStepHP2`)

The top proof (`asmFirstStep_coreStepAt_of`) asks, as `hP2`, that Phase 2 runs on the arguments
that the driver passes, from the memory that the scan of Phase 1 leaves, and that a predicate
`Q₂` holds after it. This file chooses `Q₂` and proves `hP2` (`asmFirstStep_hP2`), for the bundle
table `scProgB5` of `scProg` and any tour family `TR` that is local and holds its handle.

`Q₂` (`AsmFsQ₂`) keeps what the later phases read: the facts of the scan (`AsmFsScanFacts`), and
the post of Phase 2 (`AsmFirstNewActPost`) for the side record and the tour of the branch before
the step. The tour state has the type `(TR vCap eCap).τ` at the caps of the branch, while
Phase 2 states it at the caps `vCap5`, `eCap5` of the side record. The rep says that the two
pairs of caps are equal, so `Q₂` names a tour state `tx₀` at the caps of the side record that is
the tour state of the branch up to this equality (`HEq`).

The premises of Phase 2 come from three places:
* the rep of the branch: the side record, the tour, the feet, and the facts of the old state
  (`asmBrModelFacts_of_rep`);
* the scan: `asmFirstStep_phase2_pre`;
* the caps in a word (`asmFirstStep_cap_words`), for which the word exponent must be at least
  `3 capExp` (`hwe`).
The procedures that Phase 2 calls are premises (`hpBun` to `hpSpan`), and so is the room of
Phase 2 (`hSp2`, from the space bound of the step).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

@[expose] public section

/-- **The facts of the scan of Phase 1** on the arguments `A`, for the state `st₁` and the cost
`c₁` at its end: the premises of `hP2` in `asmFirstStep_coreStepAt_of`. -/
def AsmFsScanFacts {depth : ℕ} (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (impl : SparsifyImpl) (P L capExp limbMul w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (A : AsmFsArgs (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).τ depth)
    (st₁ : State) (c₁ : ℕ) : Prop :=
  ScanMemAt A.mem st₁.mem A.x.xRest.cmpH A.x.xRest.ctH A.x.xRest.comps.length A.x.vCap
    A.x.eCap A.words (A.h + 6) (scanBatchFold A.tr.cs.G
      (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps A.tr.activeComps) A.U) ∧
  st₁.mem (A.h + 6) = (scanBatchFold A.tr.cs.G
      (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps A.tr.activeComps)
      A.U).newComps.length ∧
  st₁.mem (A.h + 7) = (scanBatchFold A.tr.cs.G
      (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps A.tr.activeComps)
      A.U).delEdges.length ∧
  c₁ ≤ 245 * A.words + 120

/-- **The predicate `Q₂` after Phase 2**: the facts of the scan, and the post of Phase 2 for the
side record and the tour of the branch, the list of the new components at
`h + 9 + 2 eCap + vCap`, and the end of the scan as the heap pointer. The outcome is a return. -/
def AsmFsQ₂ {depth : ℕ} (TS : BundleTourSpec) (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (impl : SparsifyImpl) (P L capExp limbMul w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (fVertRoot fInitOne fInitSpan : ℕ) (p : Program) (hRoot : AsmFirstTourRootAt TR w p fVertRoot)
    (A : AsmFsArgs (asmBrFullRep (depth := depth) TR scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (o₂ : Outcome) (st₂ : State) (c₂ : ℕ) : Prop :=
  AsmFsScanFacts TR scProgB5 impl P L capExp limbMul w Ψ A st₁ c₁ ∧
  ∃ hEnd, o₂ = .returned hEnd ∧
  ∃ tx₀ : (TR A.x.xRest.vCap5 A.x.xRest.eCap5).τ, HEq tx₀ A.x.xTour ∧
    AsmFirstNewActPost TS TR w depth capExp fVertRoot fInitOne fInitSpan impl p A.ω hRoot
      A.x.restH A.x.tourH (A.h + 9 + 2 * A.x.eCap + A.x.vCap)
      (A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words) st₁.pos A.tr A.ord
      A.x.sTour.marked A.x.xRest tx₀
      (scanBatchFold A.tr.cs.G
        (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps A.tr.activeComps) A.U).newComps
      st₁.mem hEnd st₂ c₂

end

public section

set_option maxHeartbeats 1600000 in
/-- **`hP2` of the top proof.** For the bundle table `scProgB5`, a local tour family `TR` that
holds its handle (`hTh`), a word exponent of at least `3 capExp` (`hwe`), the procedures of
Phase 2 in `p`, and room for Phase 2 after the scan (`hSp2`): from the facts of the scan,
Phase 2 (`asmFirstNewActStmt fInitOne fInitSpan`) runs on the arguments that the driver passes,
and `AsmFsQ₂` holds after it. -/
theorem asmFirstStep_hP2 {TS : BundleTourSpec} {TR : ℕ → ℕ → DSRep AsmTourAbs} {depth : ℕ}
    {impl : SparsifyImpl} {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {p : Program}
    {bBun fVertRoot fTourList fTourLen fTourOwner fInitOne fInitSpan fExp bExport bSpan : ℕ}
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
    (hTh : ∀ vCap eCap tourH (tx : (TR vCap eCap).τ), (TR vCap eCap).foot tourH tx tourH)
    (hwe : 3 * capExp ≤ wordExp) (space : ℕ → ℕ)
    (hSp2 : ∀ A, AsmFsPre TR scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words +
        newActTotalSpace TS hRoot.querySpace impl w A.x.xRest A.tr A.ord
          (scanBatchFold A.tr.cs.G (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
            A.tr.activeComps) A.U).newComps < 2 ^ w) :
    ∀ A (st₁ : State) (c₁ : ℕ),
      AsmFsPre TR scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      ScanMemAt A.mem st₁.mem A.x.xRest.cmpH A.x.xRest.ctH A.x.xRest.comps.length A.x.vCap
        A.x.eCap A.words (A.h + 6) (scanBatchFold A.tr.cs.G
        (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
        A.tr.activeComps) A.U) →
      st₁.mem (A.h + 6) = (scanBatchFold A.tr.cs.G
        (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
        A.tr.activeComps) A.U).newComps.length →
      st₁.mem (A.h + 7) = (scanBatchFold A.tr.cs.G
        (asmFirstScanStart A.mem A.x.xRest.cmpH A.x.xRest.comps
        A.tr.activeComps) A.U).delEdges.length →
      c₁ ≤ 245 * A.words + 120 →
      ∃ o₂ st₂ c₂, Runs w p A.ω (asmFirstNewActStmt fInitOne fInitSpan)
          (startState [A.x.restH, A.x.tourH, A.h + 9 + 2 * A.x.eCap + A.x.vCap, st₁.mem (A.h + 6),
            A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words] st₁.mem st₁.pos)
          o₂ st₂ c₂ ∧
        AsmFsQ₂ TS TR impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot A st₁ c₁
          o₂ st₂ c₂ := by
  intro A st₁ c₁ hA hM h6 h7 hc₁
  have hsp := hSp2 A hA
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  obtain ⟨vCap, eCap, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour, xTour,
    restH, xRest⟩ := x
  unfold AsmFsPre AsmFsPreRaw at hA
  dsimp only at hA hM h6 h7 hc₁ hsp ⊢
  obtain ⟨hM0, hN0, -, -, hw16, hW, -, -, -, hR, -, hBat, hU, hCaps, -, -, -, -, -, -, -, -, -,
    -, -, hfoot, hwords, -, -⟩ := hA
  have hOld := asmBrModelFacts_of_rep hR
  obtain ⟨hRA, hv, he, -, -, -, hsl, -⟩ := hR
  dsimp only at hv he hsl hOld
  subst hv he
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTourRep, -, hSide, -, hcap, -,
    hDisj⟩ := hRA
  dsimp only at hcap
  rw [hM0, hN0] at hcap
  have hfootSide : ∀ a, asmSdFoot restH xRest a → a < h := fun a ha => hfoot a ⟨5, by decide, ha⟩
  have hfootT : ∀ a, (TR xRest.vCap5 xRest.eCap5).foot tourH xTour a → a < h :=
    fun a ha => hfoot a ⟨4, by decide, ha⟩
  have hdisjST : ∀ a, asmSdFoot restH xRest a → ¬ (TR xRest.vCap5 xRest.eCap5).foot tourH xTour a :=
    fun a hs ht => hDisj 5 (by decide) 4 (by decide) (by decide) a hs ht
  have hUW : 2 * U.length ≤ words - 1 := batchBodyAt_len_le hBat.1.2.2
  obtain ⟨hAgree, hInactiveDyn, hT1, -, hat, hlt, hNdisj, hnd, hok, hZ, -, -, -, -⟩ :=
    asmFirstStep_phase2_pre hTR_loc hSide hTourRep.2.2 hfootSide hfootT hdisjST hU hUW hM
  obtain ⟨-, -, heW, hvW, -⟩ := asmFirstStep_cap_words hW hcap hwe hsl
  have htourW : tourH < 2 ^ w := by
    have h1 := hfootT tourH (hTh _ _ tourH xTour)
    have h2 : h < 2 ^ w := hwords h (by simp)
    omega
  obtain ⟨hEnd, st', c', hpost⟩ := asmFirstNewAct_runs_post (pos := st₁.pos) (ω := ω) hpBun hRoot
    hTB hfOne hfSpan hfExp hpExport hpSpan hTR_loc hSide hAgree hInactiveDyn hT1
    hOld.2.2.2.2.2.2.2.1 hOld.2.2.2.2.2.2.2.2.1 hw16 hvW heW htourW
    (fun a ha => by have := hfootSide a ha; omega) (fun a ha => by have := hfootT a ha; omega)
    hdisjST hat hlt hNdisj hnd hok hZ (by omega)
  have hrun := hpost
  obtain ⟨-, -, -, hrun, -⟩ := hrun
  refine ⟨.returned hEnd, st', c', ?_, ⟨hM, h6, h7, hc₁⟩, hEnd, rfl, xTour, HEq.rfl, hpost⟩
  rw [h6]
  exact hrun

end

end MinCostFlow.SparseCore.Program
