module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSide

import MinCostFlow.SparseCore.Program.AssemblyFirstStepNC
import Mathlib.Tactic

/-!
# The maps of the bundle side after the first step (`AssemblyFirstStepSideMaps`)

The maps of the bundle side (`AsmSdMapsAt`) must hold for the new state after the step
(`AsmFsSideMapsGoal`). This file proves it (`asmFirstStep_hMaps_of`), from the first conjunct of
`hVerts` (the vertices that the batch names lie below `vCap`).

* The record words of the maps: no phase writes them (the record cells, as in
  `AssemblyFirstStepSide.lean`).
* The vertex array: the scan writes, at each vertex of a component of the new state, the index
  of the component (`scanBatchFold_correct`). The later phases keep the array, since it is a part
  of the maps (`asmFirstStep_phase2_keepMap` for Phase 2).
* The bucket array: no phase writes it, and the buckets of the edges do not change.
* The table of the components: the scan writes the active flags of the new state, and Phase 2
  writes the slot lists of the new components (its post 34). The pairs of the new state are
  those of Phase 2 (`activePairs_mid_eq`).
* The words: the flags are `0` or `1`. The vertex array holds old values of the array, since a
  split copies the value at a vertex below `vCap` (`scanBatchFold_cmpMap_lt`). Phase 2 gives the
  rest.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

public section

/-- **The maps of the side after the step are those of the side after Phase 2**: the maps read
only fields that the step keeps. -/
theorem asmSdMapsAt_sideAfter
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {depth : ℕ}
    {impl : SparsifyImpl} {w : ℕ} {Ψ : BundleTreeState depth → ℕ} {tr : BundleTreeState depth}
    {U : List Update} {ord : ℕ → List End} {ed : List OrdEdit} {y' : AsmBrSide B5 depth}
    {mem₃ : ℕ → ℕ} {outDescPtr nTouched : ℕ} {x' : BucketSpannerMeta depth y'.cap}
    {s : ℕ} {a : AsmBranchAbs depth} {mem : ℕ → ℕ} (h : AsmSdMapsAt w s a y' mem) :
    AsmSdMapsAt w s a (asmFsSideAfter impl w Ψ tr U ord ed y' mem₃ outDescPtr nTouched x') mem :=
  h

/-- **The vertex array of the scan holds words**: the scan changes the array only at a split,
where it copies the value at the old vertex, which lies below `vCap`. -/
theorem scanBatchFold_cmpMap_lt {G : MGraph} {vCap B : ℕ} :
    ∀ (U : List Update) (st : ScanBatchState), (∀ v ∈ batchVerts U, v < vCap) →
      (∀ x < vCap, st.cmpMap x < B) → ∀ x < vCap, (scanBatchFold G st U).cmpMap x < B := by
  intro U
  induction U with
  | nil =>
    intro st _ h
    exact h
  | cons u U ih =>
    intro st hV h x hx
    have hV' : ∀ v ∈ batchVerts U, v < vCap := fun v hv =>
      hV v (by rw [batchVerts]; exact Finset.mem_union_right _ hv)
    have hu : ∀ v ∈ updVerts u, v < vCap := fun v hv =>
      hV v (by rw [batchVerts]; exact Finset.mem_union_left _ hv)
    refine ih (scanBatchStep G st u) hV' (fun y hy => ?_) x hx
    cases u with
    | insert e a b => simpa [scanBatchStep] using h y hy
    | delete e =>
      simp only [scanBatchStep]
      split_ifs <;> simpa using h y hy
    | split v v' St Sh =>
      simp only [scanBatchStep, scanActivate_cmpMap]
      by_cases hyv : y = v'
      · subst hyv
        rw [Function.update_self]
        exact h v (hu v (by simp [updVerts]))
      · rw [Function.update_of_ne hyv]
        exact h y hy

/-- **Phases 1 and 2 keep the cells of the maps outside the slot data of the new components.**
The cells of the maps lie in the part `3` of the side, apart from the bundle table, the
spanners, the tour, the record and the slot list. So the frame of Phase 2 (`hfr`) keeps each of
them that is not a cell of the slot data of a component. -/
theorem asmFirstStep_phase2_keepMap {TR : ℕ → ℕ → DSRep AsmTourAbs} {impl : SparsifyImpl}
    {w depth L capExp limbMul : ℕ} {Ψ : BundleTreeState depth → ℕ} {a₀ : AsmBranchAbs depth}
    {y : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth}
    {tx₀ : (TR y.vCap5 y.eCap5).τ} {restH tourH words h h₂ nSlots1 : ℕ}
    {newComps : List (ℕ × ℕ)} {mem mem₁ mem₂ : ℕ → ℕ} {sb : ScanBatchState}
    (_hM : ScanMemAt mem mem₁ y.cmpH y.ctH y.comps.length y.vCap5 y.eCap5 words (h + 6) sb)
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
    ∀ a, asmSdMapCell y a →
      (∀ c < y.comps.length, ¬ (y.ctH + 3 * c + 1 ≤ a ∧ a < y.ctH + 3 * c + 3)) →
      mem₂ a = mem₁ a := by
  intro a ha hct
  have h16 : ASM_SD_SIZE = 16 := rfl
  have h3 : ASM_SD_NSLOTS = 3 := rfl
  have hD := hSide.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMS := hSide.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2
  have hP3 : asmSdPart restH y 3 a := Or.inr ha
  have hlt3 := hlt a ⟨3, by decide, hP3⟩
  refine hfr a (by omega) (fun hb => hD 3 (by decide) 1 (by decide) (by decide) a hP3 hb)
    (fun hb => hD 3 (by decide) 2 (by decide) (by decide) a hP3 hb) (hST a ⟨3, by decide, hP3⟩)
    (fun he => hD 0 (by decide) 3 (by decide) (by decide) a ⟨by omega, by omega⟩ hP3)
    (fun k hk hin => ?_) (fun hin => hMS a ha ⟨by omega, by omega⟩)
  have hq : (newComps.getD k (0, 0)).1 < y.comps.length := by
    rw [List.getD_eq_getElem _ _ hk]
    exact hNC _ (List.getElem_mem hk)
  exact hct _ hq hin

set_option maxHeartbeats 8000000 in
/-- **The maps of the bundle side after the step** (`AsmFsSideMapsGoal`), from the first conjunct
of `hVerts`. -/
theorem asmFirstStep_hMaps_of {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {space : ℕ → ℕ}
    (hVerts : ∀ A, AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A →
      ∀ v ∈ batchVerts A.U, v < A.x.vCap) :
    AsmFsSideMapsGoal TS impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne fInitSpan p
      hRoot bBun bTourStep fDelTriples fBuildGroups K space := by
  intro A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr
    mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ
  have hVU := hVerts A hA
  obtain ⟨⟨hScanF, tx₀, hTx, hP2, hP3⟩, hP4⟩ := hQ
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  obtain ⟨vCap, eCap, tCap, L_w, readH, yRead, embH, yEmb, outH, gOut, tourH, sTour, xT0,
    restH, xRest⟩ := x
  unfold AsmFsPre AsmFsPreRaw at hA
  unfold AsmFsScanFacts at hScanF
  dsimp only [AsmFsArgs.newComps] at hA hScanF hP2 hP3 hP4 hVU hTx ⊢
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
  obtain ⟨-, -, -, -, -, -, -, -, hok, -, hNew, -⟩ :=
    asmFirstStep_phase2_pre hTR_loc hSide hTourRep.2.2 hfootSide hfootT hdisjST hU hUW hM
  obtain ⟨-, hbunH, hspanH, hsPtr, hsCap, hslc, hv5, he5, hcap5, hsplB, hspV, hspE, hmMax, hcmpH, hbktH,
    hctH, hcomps, hkB', -, -, hslots', -, hSlotN, -, -, -, -, -, -, -, hnslCell, hListS, hnslCap, hCT, hMW, hMD,
    hMS, hdisjSide, hdisj', -, hlen2, -, -, hfootS', hfootT', hfr, -⟩ := hP2
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
  -- the maps of the side before the step, and the scan
  have hSide0 := hSide
  dsimp only at hSide0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMaps0, hMod0⟩ := hSide0
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, -, mW, mD, -⟩ := hMaps0
  obtain ⟨-, -, -, -, -, -, ⟨C₀, ℓ₀, hI0, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, hCross0,
    -⟩ := hMod0
  obtain ⟨-, ⟨C₁, ℓ₁, hI1, -⟩, -, -, -, -, -, hV1, -⟩ := hFacts
  obtain ⟨hScCmp0, -, -, hScAct0, -⟩ := scanBatchFold_correct (tr := tr) (U := U)
    (comps := xRest.comps) (cmpMap₀ := fun v => mem (xRest.cmpH + v)) hI0 hU m5 m6
    (fun c hc v hv => (m7 c hc v hv).2) hCross0
  have hScCmp : ∀ c (hc : c < xRest.comps.length),
      ∀ v ∈ ((compLSFBatch tr.cs U).compSt xRest.comps[c]).G.V,
      (scanBatchFold tr.cs.G (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps)
        U).cmpMap v = c := hScCmp0
  have hScAct : ∀ c (hc : c < xRest.comps.length),
      (scanBatchFold tr.cs.G (asmFirstScanStart mem xRest.cmpH xRest.comps tr.activeComps)
        U).actFlag c = true ↔
      xRest.comps[c] ∈ tr.activeComps ∪ (touchedCompsBatch tr.cs U \ tr.activeComps) := hScAct0
  have hAP := activePairs_mid_eq (fun _ => canonicalSparsify impl) tr U ord
    (applyOrdEdits ord ed) hNew
  have hG0' : (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord
      (applyOrdEdits ord ed)).state.cs.G₀ = tr.cs.G₀ := compLSFBatch_G₀ tr.cs U
  have hcl : y'.comps.length = xRest.comps.length := by rw [hcomps]
  -- the cells of the maps
  have hKm : ∀ a, asmSdMapCell y' a →
      Function.update st₄.mem (h + 1) (st₃.mem hEnd₂) a = st₂.mem a := fun a ha =>
    hKy a ⟨3, by decide, Or.inr ha⟩
      (fun h1 => hdisjSide 3 (by decide) 1 (by decide) (by decide) a (Or.inr ha) h1)
      (fun h2 => hdisjSide 3 (by decide) 2 (by decide) (by decide) a (Or.inr ha) h2)
  have hK2m := asmFirstStep_phase2_keepMap hM (fun q hq => (hok q hq).1) hnslCap hfr hSide hdisjST
    hfootSide (by omega)
  refine asmSdMapsAt_sideAfter ?_
  rw [AsmSdMapsAt]
  refine ⟨(hRec _ (by decide) (by decide)).trans (m1.trans hcmpH.symm),
    (hRec _ (by decide) (by decide)).trans (m2.trans hbktH.symm),
    (hRec _ (by decide) (by decide)).trans (m3.trans hctH.symm),
    (hRec _ (by decide) (by decide)).trans (m4.trans hcl.symm), by rw [hcomps]; exact m5,
    fun C => by rw [hcomps, hG0']; exact m6 C, ?_, ?_, ?_, ?_, hMD,
    fun a ha => by rw [hsPtr, hsCap]; exact hMS a ha⟩
  · -- the vertex array
    intro c hc v hv
    have hc' : c < xRest.comps.length := by omega
    rw [List.getElem_of_eq hcomps hc] at hv
    have hC : xRest.comps[c] ∈ components (stepBundleTree (fun _ => canonicalSparsify impl) tr U
        ord (applyOrdEdits ord ed)).state.cs.G₀ := by
      rw [hG0']
      exact (m6 _).mp (List.getElem_mem _)
    have hvlt : v < xRest.vCap5 := by
      refine hV1 v ?_
      rw [← hI1.hV_eq]
      exact Finset.mem_biUnion.mpr ⟨_, hC, hv⟩
    refine ⟨by omega, ?_⟩
    have hp0 : asmSdMapPart xRest 0 (xRest.cmpH + v) := ⟨by omega, by omega⟩
    rw [hKm (y'.cmpH + v) ⟨0, by omega, by omega⟩, hcmpH,
      hK2m (xRest.cmpH + v) ⟨0, hp0⟩ (fun c' hc'' hin =>
        mD 0 2 (by decide) _ hp0 ⟨by omega, by omega⟩), hM.1 v hvlt]
    exact hScCmp c hc' v hv
  · -- the bucket array
    intro e he
    rw [hG0'] at he
    obtain ⟨h1, h2⟩ := m8 e he
    refine ⟨by omega, ?_⟩
    have hb1 : asmSdMapPart xRest 1 (xRest.bktH + e) := ⟨by omega, by omega⟩
    have hlt := hfootSide _ ⟨3, by decide, Or.inr ⟨1, hb1⟩⟩
    rw [hKm (y'.bktH + e) ⟨1, by omega, by omega⟩, hbktH,
      hK2m (xRest.bktH + e) ⟨1, hb1⟩ (fun c hc hin => mD 1 2 (by decide) _ hb1 ⟨by omega, by omega⟩),
      asmFirstStep_scan_frame hM (xRest.bktH + e) (by omega)
        (fun v hv heq => mD 1 0 (by decide) _ hb1 ⟨by omega, by omega⟩)
        (fun c hc heq => mD 1 2 (by decide) _ hb1 ⟨by omega, by omega⟩)]
    exact h2
  · -- the table of the components
    intro c hc
    have hc' : c < xRest.comps.length := by omega
    have hgc := List.getElem_of_eq hcomps hc
    obtain ⟨t1, t2, t3, t4, t5⟩ := hCT c hc'
    refine ⟨?_, ?_, ?_, t3, fun i hi => ?_, fun b t => ?_⟩
    · rw [hKm (y'.ctH + 3 * c) ⟨2, by omega, by omega⟩, hctH,
        hK2m (xRest.ctH + 3 * c) ⟨2, by omega, by omega⟩ (fun c' hc'' hin => by omega),
        hM.2.1 c hc', hgc]
      by_cases hin : xRest.comps[c] ∈ tr.activeComps ∪ (touchedCompsBatch tr.cs U \ tr.activeComps)
      · rw [if_pos ((hScAct c hc').mpr hin)]
        exact (if_pos hin).symm
      · rw [if_neg (fun h' => hin ((hScAct c hc').mp h'))]
        exact (if_neg hin).symm
    · rw [hKm (y'.ctH + 3 * c + 1) ⟨2, by omega, by omega⟩, hctH]
      exact t1
    · rw [hKm (y'.ctH + 3 * c + 2) ⟨2, by omega, by omega⟩, hctH]
      exact t2
    · obtain ⟨u1, u2⟩ := t4 i hi
      exact ⟨(hKm _ ⟨c + 3, hc, by omega, by omega⟩).trans u1,
        (hKm _ ⟨c + 3, hc, by omega, by omega⟩).trans u2⟩
    · rw [hgc, ← hAP]
      exact t5 b t
  · -- the words of the maps
    intro a ha
    rw [hKm a ha]
    by_cases hcmp : ∃ v < xRest.vCap5, a = xRest.cmpH + v
    · obtain ⟨v, hv, rfl⟩ := hcmp
      have hp0 : asmSdMapPart xRest 0 (xRest.cmpH + v) := ⟨by omega, by omega⟩
      rw [hK2m (xRest.cmpH + v) ⟨0, hp0⟩ (fun c hc hin => mD 0 2 (by decide) _ hp0 ⟨by omega, by omega⟩),
        hM.1 v hv]
      exact scanBatchFold_cmpMap_lt U _ hVU
        (fun x hx => mW _ ⟨0, show xRest.cmpH ≤ xRest.cmpH + x ∧ _ from ⟨by omega, by omega⟩⟩) v hv
    · by_cases hfl : ∃ c < xRest.comps.length, a = xRest.ctH + 3 * c
      · obtain ⟨c, hc, rfl⟩ := hfl
        rw [hK2m (xRest.ctH + 3 * c) ⟨2, by omega, by omega⟩ (fun c' hc' hin => by omega),
          hM.2.1 c hc]
        split_ifs <;> omega
      · push_neg at hcmp hfl
        exact hMW a ha (fun c hc => hfl c hc) (fun v hv => hcmp v hv)
end

end MinCostFlow.SparseCore.Program
