module

public import MinCostFlow.SparseCore.Program.TourOutBridge
public import MinCostFlow.SparseCore.Program.AssemblyBranchTour
public import MinCostFlow.SparseCore.Program.AssemblyBranchOrd
public import MinCostFlow.SparseCore.Program.AssemblyBranchBunValue
import Mathlib.Tactic

/-!
# Tour Conversion for Branch Views (`TourAsmBridge`)

Defines the branch tour family `tourAsmRep : ℕ → ℕ → DSRep AsmTourAbs` from `tourDSRep`, proves
the equivalence between `TourCordOK` and `coreTour` (at both roots and non-roots), and discharges
all three tour conversion pieces required by `AsmBrPieces` (`AssemblyBranchValue.lean`):
* `tourDS_asmBrOutProj`: `AsmBrOutProj tourOutSpec tourAsmRep w p` for P7's view `asmTourView`;
* `tourDS_asmBrTourListProj`: `AsmBrTourListProj tourAsmRep w p (tourOp b 9) tourMul` for readout 5;
* `tourDS_asmBrTourBridge`: `AsmBrTourBridge tourBundleSpec tourAsmRep w p` for P5's view
  `asmTourCordView` (`BundleTourAt` with `listSpace len = 3 + len` and `querySpace = 1`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Part 1: `AsmTourAbs` ↔ `TourAbs` and the branch tour family `tourAsmRep` -/

/-- Convert branch tour state `AsmTourAbs` to P2's `TourAbs`. -/
def asmTourToTour (s : AsmTourAbs) : TourAbs := ⟨s.ord, s.rf, s.marked⟩

/-- Convert P2's `TourAbs` to branch tour state `AsmTourAbs`. -/
def tourToAsmTour (s : TourAbs) : AsmTourAbs := ⟨s.ord, s.rf, s.marked⟩

theorem tourToAsmTour_asmTourToTour (s : AsmTourAbs) :
    tourToAsmTour (asmTourToTour s) = s := by
  cases s; rfl

theorem asmTourToTour_tourToAsmTour (s : TourAbs) :
    asmTourToTour (tourToAsmTour s) = s := by
  cases s; rfl

theorem asmTourToTour_applyEdit (s : AsmTourAbs) (e : OrdEdit) :
    asmTourToTour (asmTourApplyEdit s e) = tourApplyEdit (asmTourToTour s) e := by
  cases e <;> rfl

theorem asmTourToTour_applyEdits (s : AsmTourAbs) (es : List OrdEdit) :
    asmTourToTour (asmTourApplyEdits s es) = tourApplyEdits (asmTourToTour s) es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    simp only [asmTourApplyEdits, tourApplyEdits, List.foldl_cons]
    rw [← asmTourToTour_applyEdit]
    exact ih (asmTourApplyEdit s e)

theorem asmTourEditValid_iff (vCap eCap : ℕ) (s : AsmTourAbs) (e : OrdEdit) :
    AsmTourEditValid vCap eCap s e ↔ TourEditValid vCap eCap (asmTourToTour s) e := by
  cases e <;> rfl

theorem asmTourEditsValid_iff (vCap eCap : ℕ) (s : AsmTourAbs) (es : List OrdEdit) :
    AsmTourEditsValid vCap eCap s es ↔ TourEditsValid vCap eCap (asmTourToTour s) es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    simp only [AsmTourEditsValid, TourEditsValid, asmTourEditValid_iff, ← asmTourToTour_applyEdit]
    exact and_congr_right fun _ => ih (asmTourApplyEdit s e)

/-- Branch tour representation family `TR : ℕ → ℕ → DSRep AsmTourAbs` built from `tourDSRep`. -/
def tourAsmRep (vCap eCap : ℕ) : DSRep AsmTourAbs where
  τ := (tourDSRep vCap eCap).τ
  rep b s x mem := (tourDSRep vCap eCap).rep b (asmTourToTour s) x mem
  phi := (tourDSRep vCap eCap).phi
  foot := (tourDSRep vCap eCap).foot

/-- `tourAsmRep vCap eCap` is local. -/
theorem tourAsmRep_local (vCap eCap : ℕ) : (tourAsmRep vCap eCap).Local :=
  fun b s x mem mem' hag => tourDS_local vCap eCap b (asmTourToTour s) x mem mem' hag

/-- The tour handle always lies in `(tourAsmRep vCap eCap).foot`. -/
theorem tourAsmRep_handle_foot (vCap eCap tourH : ℕ) (x : (tourAsmRep vCap eCap).τ) :
    (tourAsmRep vCap eCap).foot tourH x tourH :=
  tourFoot_handle (ordStoreRep vCap eCap) vCap eCap tourH x

/-- Every `TourCordOK ord rf cord` agrees pointwise with `coreTour ord rf` at both roots and
non-roots. -/
theorem tourCordOK_eq_coreTour {ord : ℕ → List End} {rf : RootedForest} {cord : ℕ → List End}
    (hok : TourCordOK ord rf cord) (r : ℕ) :
    cord r = coreTour ord rf r := by
  obtain ⟨cs, ⟨_, _, hI, ρ, hρ, hcord⟩, hrf⟩ := hok
  subst hρ hrf
  rw [hcord]
  exact (coreTour_eq_coreRotation ρ hI.hG_val (compLSF_RF_isRSF hI) r).symm

/-! ## Part 2: P7 conversion (`AsmBrOutProj`) and readout 5 conversion (`AsmBrTourListProj`) -/

/-- `tourProcs b` meets P7's four-operation `OutTourAt tourOutSpec` interface on P7's view
`asmTourView (tourAsmRep vCap eCap) ord rf cord`. -/
def tourDS_asmTourView_outTourAt (w vCap eCap : ℕ) (p : Program) (b : ℕ)
    (hp : HasTourProcs p b) (ord : ℕ → List End) (rf : RootedForest) (cord : ℕ → List End) :
    OutTourAt tourOutSpec w vCap eCap p
      (tourOp b 8) (tourOp b 7) (tourOp b 11) (tourOp b 9) where
  rep := asmTourView (tourAsmRep vCap eCap) ord rf cord
  rep_local := asmTourView_local (tourAsmRep_local vCap eCap) ord rf cord
  nextMarked_runs := fun tourH key v h s tx mem pos ω _ _ _ _ _ hmem hrep hfoot hz hsp => by
    rcases hrep with ⟨hcord_eq, hok, hR⟩
    change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH ⟨ord, rf, s.marked⟩ tx mem at hR
    have hcord : ∀ r, s.cord r = coreTour ord rf r := fun r => by
      rw [hcord_eq]; exact tourCordOK_eq_coreTour hok r
    have hmem' : endOfKey key ∈ coreTour ord rf v := hcord v ▸ hmem
    obtain ⟨_, _, ⟨u, hxu⟩, _⟩ := coreTour_mem_info hR.valid hmem'
    have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hR hfoot hsp
    let C := hp.toSplayQuery (w := w) (by omega)
    obtain ⟨o, st', c, hrun, hval', x', hrep', hans, hresp', hcost⟩ :=
      tourOp_nextMarked_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hxu hw1 (by omega)
        hfoot hz hsp
    have hnm_eq := tourNextMarked_eq_outNextMarked hR.valid hmem'
    refine ⟨_, hp.op8_body, o, st', c, x', hrun,
      ⟨hcord_eq, hok, hrep'⟩, ?_, by omega, hresp', ?_⟩
    · rw [hans, hnm_eq]
      simp only [OutTourAbs.nextMarked, hcord v]
      cases (afterEnd (endOfKey key) (coreTour ord rf v) ++ [endOfKey key]).find?
        (fun z => decide (z ∈ s.marked)) <;> rfl
    · rw [ordStoreLog_eq_tourLog]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
      dsimp only [asmTourView, tourAsmRep, tourDSRep, tourOutSpec] at hcost ⊢
      omega
  setMark_runs := fun tourH key flag v h s tx mem pos ω _ _ _ hfl _ _ hmem hrep hfoot hz hsp => by
    rcases hrep with ⟨hcord_eq, hok, hR⟩
    change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH ⟨ord, rf, s.marked⟩ tx mem at hR
    have hcord : ∀ r, s.cord r = coreTour ord rf r := fun r => by
      rw [hcord_eq]; exact tourCordOK_eq_coreTour hok r
    have hmem' : endOfKey key ∈ coreTour ord rf v := hcord v ▸ hmem
    obtain ⟨_, hopen, ⟨u, hxu⟩, _⟩ := coreTour_mem_info hR.valid hmem'
    have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hR hfoot hsp
    let C := hp.toSplayQuery (w := w) (by omega)
    obtain ⟨o, st', c, hrun, _, x', hrep', hresp', hcost⟩ :=
      tourOp_setMark_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hxu hopen hfl
        hw1 (by omega) hfoot hz (by dsimp only [tourOutSpec] at hsp; omega)
    have hsm_eq : tourSetMark ⟨ord, rf, s.marked⟩ (endOfKey key) flag =
        ⟨ord, rf, (s.setMark (endOfKey key) flag).marked⟩ := by
      simp only [OutTourAbs.setMark, tourSetMark]
      split_ifs <;> rfl
    have hcord_eq' : (s.setMark (endOfKey key) flag).cord = cord := hcord_eq
    refine ⟨_, hp.op7_body, o, st', c, x', hrun,
      ⟨hcord_eq', hok, by dsimp only [tourAsmRep, tourDSRep, asmTourToTour]; rw [← hsm_eq]; exact hrep'⟩,
      ⟨hresp'.1, le_trans hresp'.2.1 (by dsimp only [tourOutSpec]; omega),
       hresp'.2.2.1, hresp'.2.2.2.1, hresp'.2.2.2.2⟩, ?_⟩
    rw [ordStoreLog_eq_tourLog]
    have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_forest
    dsimp only [asmTourView, tourAsmRep, tourDSRep, tourOutSpec] at hcost ⊢
    omega
  firstMarked_runs := fun tourH r h s tx mem pos ω _ hrLt _ hrep hfoot hz hsp => by
    rcases hrep with ⟨hcord_eq, hok, hR⟩
    change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH ⟨ord, rf, s.marked⟩ tx mem at hR
    have hcord : s.cord r = coreTour ord rf r := by
      rw [hcord_eq]; exact tourCordOK_eq_coreTour hok r
    have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hR hfoot hsp
    let C := hp.toSplayQuery (w := w) (by omega)
    obtain ⟨o, st', c, hrun, hval', x', hrep', hans, hresp', hcost⟩ :=
      tourOp_firstMarked_runs (pos := pos) (ordStoreRep_local vCap eCap) C C.markTests
        C.markTests_cost C.markDesc_body C.findFirstMark_body ω hR hrLt hw1 (by omega)
        hfoot hz hsp
    have hml : s.markedList r = tourMarkedList ⟨ord, rf, s.marked⟩ r := by
      simp only [OutTourAbs.markedList, tourMarkedList, hcord]
    refine ⟨_, hp.op11_body, o, st', c, x', hrun,
      ⟨hcord_eq, hok, hrep'⟩, ?_, by omega, hresp', ?_⟩
    · rw [hans, hml]; cases (tourMarkedList ⟨ord, rf, s.marked⟩ r).head? <;> rfl
    · rw [ordStoreLog_eq_tourLog]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
      dsimp only [asmTourView, tourAsmRep, tourDSRep, tourOutSpec] at hcost ⊢
      omega
  listMarked_runs := fun tourH r h s tx mem pos ω _ hrLt _ hrep hfoot hz hsp => by
    rcases hrep with ⟨hcord_eq, hok, hR⟩
    change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH ⟨ord, rf, s.marked⟩ tx mem at hR
    have hcord : s.cord r = coreTour ord rf r := by
      rw [hcord_eq]; exact tourCordOK_eq_coreTour hok r
    have hml : s.markedList r = tourMarkedList ⟨ord, rf, s.marked⟩ r := by
      simp only [OutTourAbs.markedList, tourMarkedList, hcord]
    have hsp' : h + 1 + (tourMarkedList ⟨ord, rf, s.marked⟩ r).length < 2 ^ w := by
      dsimp only [tourOutSpec] at hsp; rw [← hml]; omega
    have ⟨_, hw2⟩ := tourDS_wide_of_foot hR hfoot (by omega : h + 1 < 2 ^ w)
    let C := hp.toListExact (w := w) (by omega)
    obtain ⟨o, st', c, hrun, x', hrep', hlist', hval', hz', hfr', hft', hcost⟩ :=
      tourOp_listMarked_exact_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hrLt
        hfoot hz hsp'
    refine ⟨_, hp.op9_body, o, st', c, x', hrun,
      ⟨hcord_eq, hok, hrep'⟩, by rwa [hml], by rw [hval', hml],
      ⟨by omega, by dsimp only [tourOutSpec] at hval' ⊢; rw [hval', hml]; omega,
       hz', hfr', fun a ha => Or.inl (hft' a ha)⟩, ?_⟩
    rw [hml]
    have hmono := Nat.mul_le_mul_right (ordStoreLog eCap)
      (Nat.mul_le_mul_right ((tourMarkedList ⟨ord, rf, s.marked⟩ r).length + 1) tourMul_ge_query)
    dsimp only [asmTourView, tourAsmRep, tourDSRep, tourOutSpec] at hcost ⊢
    omega

/-- **Tour conversion for P7 (`AsmBrOutProj`)**: `tourProcs b` meets `AsmBrOutProj tourOutSpec
tourAsmRep w p (tourOp b 8) (tourOp b 7) (tourOp b 11) (tourOp b 9)`. -/
theorem tourDS_asmBrOutProj (w b : ℕ) (p : Program) (hp : HasTourProcs p b) :
    AsmBrOutProj tourOutSpec tourAsmRep w p
      (tourOp b 8) (tourOp b 7) (tourOp b 11) (tourOp b 9) :=
  fun vCap eCap ord rf cord =>
    ⟨tourDS_asmTourView_outTourAt w vCap eCap p b hp ord rf cord, rfl⟩

/-- **Tour conversion for readout 5 (`AsmBrTourListProj`)**: `tourProcs b` (`tourOp b 9`) meets
`AsmBrTourListProj tourAsmRep w p (tourOp b 9) tourMul`. -/
theorem tourDS_asmBrTourListProj (w b : ℕ) (p : Program) (hp : HasTourProcs p b) :
    AsmBrTourListProj tourAsmRep w p (tourOp b 9) tourMul := by
  intro ord rf cord
  refine ⟨fun vCap eCap tourH tx => tourAsmRep_handle_foot vCap eCap tourH tx, ?_⟩
  intro vCap eCap tourH r h s tx mem pos ω _ hrLt _ hrep hfoot hz hroom
  rcases hrep with ⟨hcord_eq, hok, hR⟩
  change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH ⟨ord, rf, s.marked⟩ tx mem at hR
  have hcord : s.cord r = coreTour ord rf r := by
    rw [hcord_eq]; exact tourCordOK_eq_coreTour hok r
  have hml : s.markedList r = tourMarkedList ⟨ord, rf, s.marked⟩ r := by
    simp only [OutTourAbs.markedList, tourMarkedList, hcord]
  have hsp' : h + 1 + (tourMarkedList ⟨ord, rf, s.marked⟩ r).length < 2 ^ w := by
    rw [← hml]; exact hroom
  have ⟨_, hw2⟩ := tourDS_wide_of_foot hR hfoot (by omega : h + 1 < 2 ^ w)
  let C := hp.toListExact (w := w) (by omega)
  obtain ⟨o, st', c, hrun, x', hrep', hlist', hval', hz', hfr', hft', hcost⟩ :=
    tourOp_listMarked_exact_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hrLt
      hfoot hz hsp'
  refine ⟨_, hp.op9_body, o, st', c, x', hrun,
    ⟨hcord_eq, hok, hrep'⟩, by rwa [hml], by rw [hval', hml], hz', hfr', hft', ?_⟩
  rw [hml]
  have hmono := Nat.mul_le_mul_right (ordStoreLog eCap)
    (Nat.mul_le_mul_right ((tourMarkedList ⟨ord, rf, s.marked⟩ r).length + 1) tourMul_ge_query)
  dsimp only [asmTourView, tourAsmRep, tourDSRep] at hcost ⊢
  omega

/-! ## Part 3: P5 conversion (`tourBundleSpec` and `AsmBrTourBridge`) -/

/-- `BundleTourSpec` met by `tourProcs b`: `listSpace len = 3 + len` (linear with constant `3`)
and exact `querySpace = 1`. -/
def tourBundleSpec : BundleTourSpec where
  mul := tourMul
  listSpace len := 3 + len
  querySpace := 1
  listSpace_ge _ := by omega
  listSpace_mono hab := by omega
  querySpace_ge := by decide

/-- Linear space bound for `tourBundleSpec.listSpace` (`cT = 3`, for `asmBrBunAt_of_bunRestart`). -/
theorem tourBundleSpec_listSpace_le (len : ℕ) :
    tourBundleSpec.listSpace len ≤ 3 * (len + 1) := by
  dsimp only [tourBundleSpec]; omega

/-- `tourProcs b` meets P5's three-operation `BundleTourAt tourBundleSpec` interface on P5's view
`asmTourCordView (tourAsmRep vCap eCap) vo vf vc mk`. -/
def tourDS_asmTourCordView_bundleTourAt (w vCap eCap : ℕ) (p : Program) (b : ℕ)
    (hp : HasTourProcs p b) (vo : ℕ → List End) (vf : RootedForest) (vc : ℕ → List End)
    (mk : Finset End) :
    BundleTourAt tourBundleSpec w vCap eCap p (tourOp b 4) (tourOp b 12) (tourOp b 10) where
  rep := asmTourCordView (tourAsmRep vCap eCap) vo vf vc mk
  rep_local := asmTourCordView_local (tourAsmRep_local vCap eCap) vo vf vc mk
  list_runs := fun tourH v h cord tx mem pos ω _ hvCap _ _ hrep hfoot hz hsp => by
    rcases hrep with ⟨hcord_eq, hok, hR⟩
    change cord = vc at hcord_eq
    change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH ⟨vo, vf, mk⟩ tx mem at hR
    have hcord : cord v = coreTour vo vf v := by
      rw [hcord_eq]; exact tourCordOK_eq_coreTour hok v
    have hsp' : h + (3 + (coreTour vo vf v).length) < 2 ^ w := by
      dsimp only [tourBundleSpec] at hsp; rw [← hcord]; exact hsp
    have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hR hfoot hsp'
    let C := hp.toSplayQuery (w := w) (by omega)
    obtain ⟨o, st', c, hrun, x', hrep', hlist', hval', hresp', hcost⟩ :=
      tourOp_listTour_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hvCap hw1 (by omega)
        hfoot hz hsp'
    refine ⟨_, hp.op4_body, o, st', c, x', hrun,
      ⟨hcord_eq, hok, hrep'⟩, by rwa [hcord], by rw [hval', hcord],
      by dsimp only [tourBundleSpec]; rwa [hcord], ?_⟩
    rw [hcord, ordStoreLog_eq_tourLog]
    have hmono := Nat.mul_le_mul_right (tourLog eCap)
      (Nat.mul_le_mul_right ((coreTour vo vf v).length + 1) tourMul_ge_query)
    dsimp only [asmTourCordView, cordRepM, asmTourView, tourAsmRep, tourDSRep, tourBundleSpec]
      at hcost ⊢
    omega
  len_runs := fun tourH v h cord tx mem pos ω _ hvCap _ _ hrep hfoot hz hsp => by
    rcases hrep with ⟨hcord_eq, hok, hR⟩
    change cord = vc at hcord_eq
    change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH ⟨vo, vf, mk⟩ tx mem at hR
    have hcord : cord v = coreTour vo vf v := by
      rw [hcord_eq]; exact tourCordOK_eq_coreTour hok v
    have hsp' : h + 1 < 2 ^ w := hsp
    have ⟨_, hw2⟩ := tourDS_wide_of_foot hR hfoot hsp'
    let C := hp.toSplayCore (w := w) (by omega)
    obtain ⟨o, st', c, hrun, hval', x', hrep', hans, hz', hfr', hft', hcost⟩ :=
      tourOp_len_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hvCap hfoot hz hsp'
    refine ⟨_, hp.op12_body, o, st', c, x', hrun,
      ⟨hcord_eq, hok, hrep'⟩, by rw [hans, hcord], by rw [hval'],
      ⟨by omega, by dsimp only [tourBundleSpec]; omega, hz', hfr', fun a ha => Or.inl (hft' a ha)⟩,
      ?_⟩
    rw [ordStoreLog_eq_tourLog]
    have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
    dsimp only [asmTourCordView, cordRepM, asmTourView, tourAsmRep, tourDSRep, tourBundleSpec]
      at hcost ⊢
    omega
  owner_runs := fun tourH key v h cord tx mem pos ω _ _ _ _ _ hmem _ hrep hfoot hz hsp => by
    rcases hrep with ⟨hcord_eq, hok, hR⟩
    change cord = vc at hcord_eq
    change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH ⟨vo, vf, mk⟩ tx mem at hR
    have hcord : cord v = coreTour vo vf v := by
      rw [hcord_eq]; exact tourCordOK_eq_coreTour hok v
    obtain ⟨_, _, hact, hroot⟩ := coreTour_mem_info hR.valid (hcord ▸ hmem)
    have hsp' : h + 1 < 2 ^ w := hsp
    have ⟨_, hw2⟩ := tourDS_wide_of_foot hR hfoot hsp'
    let C := hp.toSplayCore (w := w) (by omega)
    obtain ⟨o, st', c, hrun, hval', x', hrep', hans, hz', hfr', hft', hcost⟩ :=
      tourOp_rootOf_exact_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hact hfoot hz hsp'
    refine ⟨_, hp.op10_body, o, st', c, x', hrun,
      ⟨hcord_eq, hok, hrep'⟩, by rw [hans, hroot], by rw [hval'],
      ⟨by omega, by dsimp only [tourBundleSpec]; omega, hz', hfr', fun a ha => Or.inl (hft' a ha)⟩,
      ?_⟩
    rw [ordStoreLog_eq_tourLog]
    have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
    dsimp only [asmTourCordView, cordRepM, asmTourView, tourAsmRep, tourDSRep, tourBundleSpec]
      at hcost ⊢
    omega

/-- **Tour conversion for P5 (`AsmBrTourBridge`)**: `tourProcs b` meets `AsmBrTourBridge
tourBundleSpec tourAsmRep w p (tourOp b 4) (tourOp b 12) (tourOp b 10)`. -/
theorem tourDS_asmBrTourBridge (w b : ℕ) (p : Program) (hp : HasTourProcs p b) :
    AsmBrTourBridge tourBundleSpec tourAsmRep w p (tourOp b 4) (tourOp b 12) (tourOp b 10) :=
  fun vCap eCap vo vf vc mk =>
    ⟨tourDS_asmTourCordView_bundleTourAt w vCap eCap p b hp vo vf vc mk, rfl⟩

end MinCostFlow.SparseCore.Program
