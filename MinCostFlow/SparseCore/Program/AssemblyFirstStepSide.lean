module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNCDefs

import MinCostFlow.SparseCore.Program.AssemblyFirstStepNC
import Mathlib.Tactic

/-!
# The bundle side at the end of the first step (`AssemblyFirstStepSide`)

The post of the step asks that the bundle side after the step (`asmFsSideAfter`) holds the new
state of the model (`AsmFsSideGoal`). The side is a record of `16` words, the bundle table, the
bucket spanners, the slot list and the maps (`AsmBrSideAt`). This file proves the memory part of
it, and leaves two goals: the maps for the new state (`AsmFsSideMapsGoal`) and the facts on the
model (`AsmFsSideModelGoal`).

* The record: Phase 2 writes the number of slots at `restH + 3`, and no phase writes the other
  words (`asmFirstStep_phase2_keepRec` for Phases 1 and 2; the parts `0` and `3` of the side after
  Phase 2 lie apart from the bundle table, the spanners, the tour and the embedding table, which
  are the cells that Phases 3 and 4 write below their start).
* The bundle table is the table of Phase 3 and the spanners those of Phase 4; the slot list is
  that of Phase 2. Each lies apart from the cells that the later phases and the driver write.
* The parts are apart: those of the side after Phase 2 are apart, and the new spanners lie in its
  spanners or above the end of Phase 3.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

@[expose] public section

/-- **The maps of the bundle side after the step** for the new state of the model, in the final
memory. -/
def AsmFsSideMapsGoal {depth : ℕ} (TS : BundleTourSpec) (impl : SparsifyImpl)
    (P L capExp limbMul wordExp w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (fVertRoot fInitOne fInitSpan : ℕ) (p : Program)
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) (bBun bTourStep fDelTriples fBuildGroups : ℕ)
    (K : AsmFirstP4Code TRc w impl p fVertRoot) (space : ℕ → ℕ) : Prop :=
  ∀ (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (st₂ : State) (c₂ : ℕ) (st₃ : State) (c₃ : ℕ)
    (o₄ : Outcome) (st₄ : State) (c₄ : ℕ)
    (hEnd₂ : ℕ) (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ) (hEnd₃ : ℕ)
    (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (splitPtr outDescPtr : ℕ)
    (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End)) (touched : List ℕ)
    (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (x' : BucketSpannerMeta depth y'.cap) (yE : EmbConc)
    (tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (Ld Li Lr T₀ : List ℕ),
    AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
    AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ →
    AsmSdMapsAt w A.x.restH
      ⟨(stepBundleTree (fun _ => canonicalSparsify impl) A.tr A.U A.ord
        (applyOrdEdits A.ord A.ed)).state, applyOrdEdits A.ord A.ed, A.x.vCap, A.x.eCap⟩
      (asmFsSideAfter impl w Ψ A.tr A.U A.ord A.ed y' st₃.mem outDescPtr touched.length x')
      (Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂))

/-- **The model facts of the bundle side after the step** (`AsmBrSideModel`) for the new state. -/
def AsmFsSideModelGoal {depth : ℕ} (TS : BundleTourSpec) (impl : SparsifyImpl)
    (P L capExp limbMul wordExp w : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (fVertRoot fInitOne fInitSpan : ℕ) (p : Program)
    (hRoot : AsmFirstTourRootAt TRc w p fVertRoot) (bBun bTourStep fDelTriples fBuildGroups : ℕ)
    (K : AsmFirstP4Code TRc w impl p fVertRoot) (space : ℕ → ℕ) : Prop :=
  ∀ (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (st₂ : State) (c₂ : ℕ) (st₃ : State) (c₃ : ℕ)
    (o₄ : Outcome) (st₄ : State) (c₄ : ℕ)
    (hEnd₂ : ℕ) (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ) (hEnd₃ : ℕ)
    (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (splitPtr outDescPtr : ℕ)
    (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End)) (touched : List ℕ)
    (qs : List (SpanUpdTask × P4TaskOut)) (ns : List (ℕ × List ℕ))
    (x' : BucketSpannerMeta depth y'.cap) (yE : EmbConc)
    (tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ) (Ld Li Lr T₀ : List ℕ),
    AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
    AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ →
    AsmBrSideModel impl w depth L capExp limbMul Ψ
      ⟨(stepBundleTree (fun _ => canonicalSparsify impl) A.tr A.U A.ord
        (applyOrdEdits A.ord A.ed)).state, applyOrdEdits A.ord A.ed, A.x.vCap, A.x.eCap⟩
      (asmFsSideAfter impl w Ψ A.tr A.U A.ord A.ed y' st₃.mem outDescPtr touched.length x')

end

public section

/-- **Phases 1 and 2 keep the words of the side record but the number of slots.** The scan writes
only the vertex array and the active flags, which are cells of the maps. Phase 2 keeps every cell
below its start outside the bundle table, the spanners, the tour, the number of slots, the cells
of the table of the components of the new components and the new part of the slot list
(`hfr`). The record lies apart from all of them, since the parts of the side are apart. -/
theorem asmFirstStep_phase2_keepRec {TR : ℕ → ℕ → DSRep AsmTourAbs} {impl : SparsifyImpl}
    {w depth L capExp limbMul : ℕ} {Ψ : BundleTreeState depth → ℕ} {a₀ : AsmBranchAbs depth}
    {y : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth}
    {tx₀ : (TR y.vCap5 y.eCap5).τ} {restH tourH words h h₂ nSlots1 : ℕ}
    {newComps : List (ℕ × ℕ)} {mem mem₁ mem₂ : ℕ → ℕ} {sb : ScanBatchState}
    (hM : ScanMemAt mem mem₁ y.cmpH y.ctH y.comps.length y.vCap5 y.eCap5 words (h + 6) sb)
    (hNC : ∀ q ∈ newComps, q.1 < y.comps.length) (hsl : nSlots1 ≤ y.slotsCap)
    (hfr : ∀ a < h₂,
        ¬ (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH y.xBun a →
        ¬ bucketFoot y.spanH y.xSpan a →
        ¬ (TR y.vCap5 y.eCap5).foot tourH tx₀ a →
        a ≠ restH + ASM_SD_NSLOTS →
        (∀ k (_hk : k < newComps.length), ¬ (y.ctH + 3 * (newComps.getD k (0, 0)).1 + 1 ≤ a ∧
          a < y.ctH + 3 * (newComps.getD k (0, 0)).1 + 3)) →
        ¬ (y.slotsPtr + y.slots.length ≤ a ∧ a < y.slotsPtr + nSlots1) →
        mem₂ a = mem₁ a)
    (hSide : AsmBrSideAt (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w depth L capExp limbMul Ψ restH a₀ y mem)
    (hST : ∀ a, asmSdFoot restH y a → ¬ (TR y.vCap5 y.eCap5).foot tourH tx₀ a)
    (hlt : ∀ a, asmSdFoot restH y a → a < h) (hh : h ≤ h₂) :
    ∀ i < ASM_SD_SIZE, i ≠ ASM_SD_NSLOTS → mem₂ (restH + i) = mem (restH + i) := by
  intro i hi hi3
  have h16 : ASM_SD_SIZE = 16 := rfl
  have h3 : ASM_SD_NSLOTS = 3 := rfl
  have hD := hSide.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR0 : asmSdPart restH y 0 (restH + i) := ⟨Nat.le_add_right _ _, by omega⟩
  have hlt0 := hlt _ ⟨0, by decide, hR0⟩
  have hn3 : ∀ c, asmSdPart restH y 3 c → c ≠ restH + i := fun c hc he =>
    hD 0 (by decide) 3 (by decide) (by decide) _ hR0 (he ▸ hc)
  rw [hfr _ (by omega) (fun hb => hD 0 (by decide) 1 (by decide) (by decide) _ hR0 hb)
    (fun hb => hD 0 (by decide) 2 (by decide) (by decide) _ hR0 hb)
    (hST _ ⟨0, by decide, hR0⟩) (by omega) (fun k hk hin => ?_) (fun hin => ?_)]
  · refine asmFirstStep_scan_frame hM _ (by omega) (fun v hv he => ?_) (fun c hc he => ?_)
    · exact hn3 _ (Or.inr ⟨0, by omega, by omega⟩) he.symm
    · exact hn3 _ (Or.inr ⟨2, by omega, by omega⟩) he.symm
  · have hq : (newComps.getD k (0, 0)).1 < y.comps.length := by
      rw [List.getD_eq_getElem _ _ hk]
      exact hNC _ (List.getElem_mem hk)
    exact hn3 _ (Or.inr ⟨2, by omega, by omega⟩) rfl
  · exact hn3 _ (Or.inl ⟨by omega, by omega⟩) rfl

set_option maxHeartbeats 8000000 in
/-- **The bundle side after the step** (`AsmFsSideGoal`), from the maps (`hMaps`) and the model
facts (`hModel`) for the new state. -/
theorem asmFirstStep_hSide_of {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {space : ℕ → ℕ}
    (hMaps : AsmFsSideMapsGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne
      fInitSpan p hRoot bBun bTourStep fDelTriples fBuildGroups K space)
    (hModel : AsmFsSideModelGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne
      fInitSpan p hRoot bBun bTourStep fDelTriples fBuildGroups K space) :
    AsmFsSideGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne fInitSpan p hRoot
      bBun bTourStep fDelTriples fBuildGroups K space := by
  intro A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr
    mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ
  have hmaps := hMaps A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr
    outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ
  have hmodel := hModel A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr
    outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ
  obtain ⟨⟨hScanF, tx₀, hTx, hP2, hP3⟩, hP4⟩ := hQ
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  obtain ⟨vCap, eCap, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour, xT0,
    restH, xRest⟩ := x
  unfold AsmFsPre AsmFsPreRaw at hA
  unfold AsmFsScanFacts at hScanF
  dsimp only [AsmFsArgs.newComps] at hA hScanF hP2 hP3 hP4 hmaps hmodel hTx ⊢
  obtain ⟨hM0, hN0, -, -, hw16, -, -, -, -, hR, hFacts, hBat, hU, -, hEd, -, -, -, -, -, -, -,
    -, -, -, hfoot, hwords, -, hspace, -⟩ := hA
  have hOld := asmBrModelFacts_of_rep hR
  obtain ⟨hRA, hv, he, -, -, -, -, -⟩ := hR
  dsimp only at hv he hOld
  subst hv he
  obtain ⟨hM, -, -, -⟩ := hScanF
  obtain rfl : xT0 = tx₀ := (eq_of_heq hTx).symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTourRep, -, hSide, -,
    -, -, hDisj⟩ := hRA
  have hTR_loc : ∀ v e, (TRc v e).Local := fun v e =>
    asmTourRepWithPot_local tourAsmRep_local (bundleScanPotMul tourBundleSpec) v e
  have hfootSide : ∀ a, asmSdFoot restH xRest a → a < h := fun a ha => hfoot a ⟨5, by decide, ha⟩
  have hfootT : ∀ a, (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a → a < h :=
    fun a ha => hfoot a ⟨4, by decide, ha⟩
  have hfootE : ∀ a, embFoot xRest.eCap5 embH yEmb a → a < h :=
    fun a ha => hfoot a ⟨2, by decide, ha⟩
  have hdisjST : ∀ a, asmSdFoot restH xRest a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a :=
    fun a hs ht => hDisj 5 (by decide) 4 (by decide) (by decide) a hs ht
  have hdisjES : ∀ a, embFoot xRest.eCap5 embH yEmb a → ¬ asmSdFoot restH xRest a :=
    fun a he hs => hDisj 2 (by decide) 5 (by decide) (by decide) a he hs
  have hdisjET : ∀ a, embFoot xRest.eCap5 embH yEmb a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a :=
    fun a he ht => hDisj 2 (by decide) 4 (by decide) (by decide) a he ht
  -- the scan and the post of Phase 2
  have hUW : 2 * U.length ≤ words - 1 := batchBodyAt_len_le hBat.1.2.2
  obtain ⟨-, -, -, -, -, -, -, -, hok, -⟩ :=
    asmFirstStep_phase2_pre hTR_loc hSide hTourRep.2.2 hfootSide hfootT hdisjST hU hUW hM
  obtain ⟨-, hbunH, hspanH, hsPtr, hsCap, hslc, hv5, he5, hcap5, hsplB, hspV, hspE, hmMax, -, -,
    -, -, hkB', -, -, hslots', -, hSlotN, -, -, -, -, -, -, -, hnslCell, hListS, hnslCap, -, -, -,
    -, hdisjSide, hdisj', -, hlen2, -, -, hfootS', hfootT', hfr, -⟩ := hP2
  -- the post of Phase 3
  obtain ⟨-, hBun3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h3e, -, -,
    hfootT3, hfr3, -⟩ := hP3
  -- the post of Phase 4
  have hP4c := hP4
  obtain ⟨-, -, -, -, hRepX', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    h4a, -, -, hfr4, hfootX', -, -, -, -, -, -⟩ := hP4c
  -- the places
  obtain ⟨e₂, he₂⟩ : ∃ e₂, e₂ = h + 6 + asmFirstScanBatchSpace xRest.vCap5 xRest.eCap5 words + 2 *
      (scanBatchFold tr.cs.G (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps)
      U).newComps.length := ⟨_, rfl⟩
  rw [← he₂] at hlen2 hfootS' hfootT'
  have he₂h : h + 6 ≤ e₂ := by omega
  have hhw : h < 2 ^ w := hwords h (by simp)
  have hkB : xRest.kB = tr.k := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMod⟩ := hSide
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hkB, -⟩ := hMod
    exact hkB
  have hBunConv : ∀ a, (bunTableHeadroomRep y'.slotCap xRest.vCap5 xRest.eCap5 tr.k).foot y'.bunH
      y'.xBun a → (bunTableHeadroomRep y'.slotCap y'.vCap5 y'.eCap5 y'.kB).foot y'.bunH y'.xBun a :=
    fun a ha => by rw [hv5, he5, hkB', hkB]; exact ha
  have hBunSd : ∀ a, (bunTableHeadroomRep y'.slotCap xRest.vCap5 xRest.eCap5 tr.k).foot y'.bunH
      y'.xBun a → asmSdFoot restH y' a := fun a ha => ⟨1, by decide, hBunConv a ha⟩
  have hBkSd : ∀ a, bucketFoot y'.spanH y'.xSpan a → asmSdFoot restH y' a :=
    fun a ha => ⟨2, by decide, ha⟩
  have hSdLoc : ∀ a, asmSdFoot restH y' a →
      (asmSdFoot restH xRest a ∧ a < h) ∨ (e₂ ≤ a ∧ a < hEnd₂) := by
    intro a ha
    rcases hfootS' a ha with hs | hr
    · exact Or.inl ⟨hs, hfootSide a hs⟩
    · exact Or.inr hr
  have hT3 : ∀ a, (TRc xRest.vCap5 xRest.eCap5).foot tourH tx_pot' a →
      (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a ∨ (e₂ ≤ a ∧ a < hEnd₃) := by
    intro a ha
    rcases hfootT3 a ha with h1 | h1
    · rcases hfootT' a h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨h2.1, by omega⟩
    · exact Or.inr ⟨by omega, h1.2⟩
  -- the cells below `h`
  have hK2keep := asmFirstStep_phase2_keep (fun q hq => (hok q hq).1) hnslCap hfr
  have hK := asmFirstStep_keep12 hM hK2keep (by omega)
  have hK3 := asmFirstStep_keep123 hK hfr3
    (fun a hb => by
      rcases hfootS' a (hBunSd a hb) with hs | ⟨h1, _⟩
      · exact Or.inl hs
      · exact Or.inr (by omega))
    (fun a ht => by
      rcases hfootT' a ht with ht0 | ⟨h1, _⟩
      · exact Or.inl ht0
      · exact Or.inr (by omega))
    (by omega)
  have hK4 : ∀ a < h, ¬ asmSdFoot restH xRest a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a → ¬ embFoot xRest.eCap5 embH yEmb a →
      st₄.mem a = mem a := by
    intro a ha hs ht hem
    have hb : ¬ bucketFoot y'.spanH y'.xSpan a := fun hb => by
      rcases hSdLoc a (hBkSd a hb) with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hs h1
      · omega
    have ht3 : ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH tx_pot' a := fun h3 => by
      rcases hT3 a h3 with h1 | ⟨h1, _⟩
      · exact ht h1
      · omega
    rw [hfr4 a (by omega) hb hem ht3 (Or.inl ha)]
    exact hK3 a ha hs ht
  have hmem' : ∀ a, a ≠ h + 1 →
      Function.update st₄.mem (h + 1) (st₃.mem hEnd₂) a = st₄.mem a :=
    fun a ha => Function.update_of_ne ha _ _
  have hKall : ∀ a < h, ¬ asmSdFoot restH xRest a →
      ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH xT0 a → ¬ embFoot xRest.eCap5 embH yEmb a →
      Function.update st₄.mem (h + 1) (st₃.mem hEnd₂) a = mem a := fun a ha hs ht hem => by
    rw [hmem' a (by omega)]
    exact hK4 a ha hs ht hem
  -- the cells of the parts `0` and `3` of the side after Phase 2 keep their values
  have hTx3 : ∀ a, asmSdFoot restH y' a → ¬ (TRc xRest.vCap5 xRest.eCap5).foot tourH tx_pot' a :=
    fun a hs ht => by
      rcases hfootT3 a ht with h1 | ⟨h1, _⟩
      · exact hdisj' a hs h1
      · rcases hSdLoc a hs with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
  have hK34 : ∀ a, asmSdFoot restH y' a → ¬ asmSdPart restH y' 2 a →
      Function.update st₄.mem (h + 1) (st₃.mem hEnd₂) a = st₃.mem a := by
    intro a hs hb
    have hloc := hSdLoc a hs
    rw [hmem' a (by rcases hloc with ⟨_, h1⟩ | ⟨h1, _⟩ <;> omega)]
    refine hfr4 a (by rcases hloc with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega) hb (fun he => ?_) (hTx3 a hs)
      (by rcases hloc with ⟨_, h1⟩ | ⟨h1, _⟩ <;> omega)
    rcases hloc with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hdisjES a he h1
    · have := hfootE a he
      omega
  have hKy : ∀ a, asmSdFoot restH y' a → ¬ asmSdPart restH y' 1 a → ¬ asmSdPart restH y' 2 a →
      Function.update st₄.mem (h + 1) (st₃.mem hEnd₂) a = st₂.mem a := by
    intro a hs h1 hb
    rw [hK34 a hs hb]
    refine hfr3 a (by rcases hSdLoc a hs with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega)
      (fun hu => h1 (hBunConv a hu)) (fun ht => hdisj' a hs ht)
  -- the record cells
  have hRecS : ∀ i < ASM_SD_SIZE, asmSdPart restH y' 0 (restH + i) :=
    fun i hi => ⟨Nat.le_add_right _ _, by omega⟩
  have hRec' : ∀ i < ASM_SD_SIZE, Function.update st₄.mem (h + 1) (st₃.mem hEnd₂) (restH + i) =
      st₂.mem (restH + i) := fun i hi =>
    hKy _ ⟨0, by decide, hRecS i hi⟩
      (fun h1 => hdisjSide 0 (by decide) 1 (by decide) (by decide) _ (hRecS i hi) h1)
      (fun h2 => hdisjSide 0 (by decide) 2 (by decide) (by decide) _ (hRecS i hi) h2)
  have hRec2 := asmFirstStep_phase2_keepRec hM (fun q hq => (hok q hq).1) hnslCap hfr
    hSide hdisjST hfootSide (by omega)
  have hRec : ∀ i < ASM_SD_SIZE, i ≠ ASM_SD_NSLOTS →
      Function.update st₄.mem (h + 1) (st₃.mem hEnd₂) (restH + i) = mem (restH + i) :=
    fun i hi hi3 => (hRec' i hi).trans (hRec2 i hi hi3)
  have hlenS : y'.slots.length = xRest.slots.length +
      newCompsBucketSum tr xRest.comps (scanBatchFold tr.cs.G
        (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps) U).newComps := by
    rw [hslots', List.length_range]
  -- the new spanners lie apart from the parts of the side after Phase 2 but its spanners
  have hX : ∀ k < 4, k ≠ 2 → ∀ c, bucketFoot y'.spanH x' c → ¬ asmSdPart restH y' k c :=
    fun k hk hk2 c hx hy => by
      rcases hfootX' c hx with hx | ⟨hx1, _⟩
      · exact hdisjSide 2 (by decide) k hk (Ne.symm hk2) c hx hy
      · rcases hSdLoc c ⟨k, hk, hy⟩ with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
  have hSide0 := hSide
  obtain ⟨o1, o2, o3, -, o5, o6, o7, o8, o9, o10, o11, o12, oW, -, -, -, -, -, -, -⟩ := hSide0
  rw [asmBrSideRep_rep, AsmBrSideAt]
  refine ⟨(hRec _ (by decide) (by decide)).trans (o1.trans hbunH.symm),
    (hRec _ (by decide) (by decide)).trans (o2.trans hspanH.symm),
    (hRec _ (by decide) (by decide)).trans (o3.trans hsPtr.symm), ?_,
    (hRec _ (by decide) (by decide)).trans (o5.trans hslc.symm),
    (hRec _ (by decide) (by decide)).trans (o6.trans he5.symm),
    (hRec _ (by decide) (by decide)).trans (o7.trans hcap5.symm),
    (hRec _ (by decide) (by decide)).trans o8,
    (hRec _ (by decide) (by decide)).trans (o9.trans hsplB.symm),
    (hRec _ (by decide) (by decide)).trans (o10.trans hspV.symm),
    (hRec _ (by decide) (by decide)).trans (o11.trans hspE.symm),
    (hRec _ (by decide) (by decide)).trans (o12.trans hmMax.symm), ?_, ?_, ?_, ?_, ?_, ?_,
    hmaps, hmodel⟩
  · -- the number of slots
    rw [hRec' _ (by decide), hnslCell]
    exact hlenS.symm
  · -- the record holds words
    intro i hi
    by_cases hi3 : i = ASM_SD_NSLOTS
    · subst hi3
      rw [hRec' _ hi, hnslCell]
      have : xRest.slotsPtr + xRest.slotsCap < h :=
        hfootSide _ ⟨3, by decide, Or.inl ⟨by omega, by omega⟩⟩
      omega
    · rw [hRec i hi hi3]
      exact oW i hi
  · -- the bundle table of Phase 3
    show (bunTableHeadroomRep y'.slotCap y'.vCap5 y'.eCap5 y'.kB).rep y'.bunH
      (tableAfterStepRuns tr.cs tr.k (applyOrdEdits ord ed) U y'.bunS) y'.xBun _
    rw [hv5, he5, hkB', hkB]
    refine (bunTableHeadroomRep_local _ _ _ _ _ _ _ st₃.mem _ fun a ha => ?_).1 hBun3
    have hs := hBunSd a ha
    exact (hK34 a hs fun h2 =>
      hdisjSide 1 (by decide) 2 (by decide) (by decide) a (hBunConv a ha) h2).symm
  · -- the spanners of Phase 4
    refine (bucketSpannerRep_local _ _ _ _ _ st₄.mem _ fun a ha => ?_).1 hRepX'
    refine (hmem' a ?_).symm
    rcases hfootX' a ha with h1 | ⟨h1, _⟩
    · rcases hSdLoc a (hBkSd a h1) with ⟨_, h2⟩ | ⟨h2, _⟩ <;> omega
    · omega
  · -- the slot list of Phase 2
    show ListAt _ y'.slotsPtr y'.slots
    rw [hsPtr]
    refine ListAt.congr hListS (fun k hk1 hk2 => ?_)
    have hp3 : asmSdPart restH y' 3 k := Or.inl ⟨by rw [hsPtr]; omega, by rw [hsPtr, hsCap]; omega⟩
    exact hKy k ⟨3, by decide, hp3⟩
      (fun h1 => hdisjSide 3 (by decide) 1 (by decide) (by decide) k hp3 h1)
      (fun h2 => hdisjSide 3 (by decide) 2 (by decide) (by decide) k hp3 h2)
  · -- the number of slots is at most the cap
    show y'.slots.length ≤ y'.slotsCap
    rw [hlenS, hsCap]
    exact hnslCap
  · -- the parts are apart
    intro i hi j hj hij c hci hcj
    by_cases hi2 : i = 2
    · subst hi2
      have hj2 : j ≠ 2 := fun e => hij e.symm
      exact hX j hj hj2 c (asmSdPart_sideAfter.2.mp hci) ((asmSdPart_sideAfter.1 j hj2).mp hcj)
    · by_cases hj2 : j = 2
      · subst hj2
        exact hX i hi hi2 c (asmSdPart_sideAfter.2.mp hcj) ((asmSdPart_sideAfter.1 i hi2).mp hci)
      · exact hdisjSide i hi j hj hij c ((asmSdPart_sideAfter.1 i hi2).mp hci)
          ((asmSdPart_sideAfter.1 j hj2).mp hcj)

end

end MinCostFlow.SparseCore.Program
