module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPack
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepTop
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepHP2
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepHP4
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepCostGoal
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepEmb
public import MinCostFlow.SparseCore.Program.AssemblyFsOpen
public import MinCostFlow.SparseCore.Program.AssemblyFsOpenVerts
public import MinCostFlow.SparseCore.Program.AssemblyFsOpenWords
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSpaceTotal
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSpacePre
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSpaceP4
public import MinCostFlow.SparseCore.Program.AssemblyFirstTourPot
public import MinCostFlow.SparseCore.Program.TourAsmBridge

import Mathlib.Tactic

/-!
# The pieces of the first step on `scProg` (`AssemblyFirstStepPackTop`)

With the code `asmFsStepCode` of `AssemblyFirstStepPack.lean` as the first step of `scProg`, this
file proves `AsmFsPieces` (`asmFirstStep_pieces_scProg`) at the space
`asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp`, from the space bounds and the cost goal.

* The six procedure indices and the procedures that Phases 2, 3 and 4 call come from the places of
  the blocks of `scProg` (`scProg_hasTour`, `scProg_hasBundle`, ...) and of the first step
  (`asmFsStep_scProg_has`). The root of a vertex in the tour is `asmFsRootSc`, and the procedures
  of Phase 4 are `asmFsKSc`.
* Phases 2, 3 and 4 are `asmFirstStep_hP2`, `asmFirstStep_hP3` and `asmFirstStep_hP4`, with
  `hOpen` and `hVerts` from `asmFirstStep_hOpen` and `asmFirstStep_hVerts`.
* The post is `asmFirstStep_hPost_of`, with the part without the cost from
  `asmFirstStep_hNC_full`.

The room of Phases 1 to 3 comes from `AssemblyFirstStepSpacePre.lean`, and the room of Phase 4
(`hSp4`) and the bound of the last result (`hSpG`) from `AssemblyFirstStepSpaceP4.lean`. The only
premise left is the cost goal `hCost`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

set_option hygiene false in
/-- The program `scProg` with the first step `asmFsStepCode`. -/
local notation "pSc" => scProg impl cf asmFsStepCode firstInit

set_option hygiene false in
/-- Its layout. -/
local notation "LSc" => scLayout impl cf asmFsStepCode firstInit

public section

/-- **The first step sits at `L.envStep.bSelf` of `scProg`.** -/
theorem asmFsStep_scProg_has (impl : SparsifyImpl) (cf : ScCompCode) (firstInit : ScSubCode) :
    (pSc).HasAt (LSc).envStep.bSelf (asmFsStepProcs (LSc).envStep) :=
  scProg_hasFirstStep impl cf asmFsStepCode firstInit

end

@[expose] public section

/-- **The root of a vertex in the tour** of `scProg`, at the procedure `7` of the first step. -/
noncomputable def asmFsRootSc (impl : SparsifyImpl) (cf : ScCompCode) (firstInit : ScSubCode)
    (w : ℕ) :
    AsmFirstTourRootAt TRc w pSc ((LSc).envStep.bSelf + 7) :=
  asmFirstTourVertRoot_withPot_runs w (LSc).bTour ((LSc).envStep.bSelf + 7) pSc
    (scProg_hasTour impl cf asmFsStepCode firstInit)
    (hasAt_getElem? (asmFsStep_scProg_has impl cf firstInit) (i := 7) rfl)
    (bundleScanPotMul tourBundleSpec)

/-- **The procedures of Phase 4** in `scProg` (`asmFsP4Code`). -/
noncomputable def asmFsKSc (impl : SparsifyImpl) (cf : ScCompCode) (firstInit : ScSubCode) (w : ℕ) :
    AsmFirstP4Code TRc w impl pSc ((LSc).envStep.bSelf + 7) :=
  asmFsP4Code (asmFsStep_scProg_has impl cf firstInit)
    (scProg_hasSpan impl cf asmFsStepCode firstInit)
    (scProg_hasCopy impl cf asmFsStepCode firstInit)
    (tourAsmRepWithPot_endRootAt w (LSc).bTour pSc (scProg_hasTour impl cf asmFsStepCode firstInit)
      (bundleScanPotMul tourBundleSpec))
    (bundleProcs_unpack (scProg_hasBundle impl cf asmFsStepCode firstInit)).1

end

public section

/-- The root query of `asmFsRootSc` uses one cell. -/
theorem asmFsRootSc_querySpace (impl : SparsifyImpl) (cf : ScCompCode) (firstInit : ScSubCode)
    (w : ℕ) : (asmFsRootSc impl cf firstInit w).querySpace = 1 :=
  asmFirstTourVertRoot_withPot_runs_querySpace _ _ _ _ _ _ _

/-- The root query of an end, in `asmFsKSc`, uses one cell. -/
theorem asmFsKSc_querySpace (impl : SparsifyImpl) (cf : ScCompCode) (firstInit : ScSubCode)
    (w : ℕ) : (asmFsKSc impl cf firstInit w).HE.querySpace = 1 :=
  tourAsmRepWithPot_endRootAt_querySpace _ _ _ _ _

set_option maxHeartbeats 1000000 in
/-- **The pieces of the first step on `scProg`** (`AsmFsPieces`), at the space
`asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp` and its polynomial, from the cost goal `hCost`.
The constant `C_sp`
bounds the length factor of the sparsifier (`hC`, `hγ`). The word exponent is at least
`3 capExp` (`hwe`), the sparsifier has `1 ≤ max p_s p_t` (`hp`), and `ysMul` is at least
`4 capExp + 5` (`hys`). -/
theorem asmFirstStep_pieces_scProg {depth : ℕ} (impl : SparsifyImpl) (cf : ScCompCode)
    (firstInit : ScSubCode) {P L capExp limbMul wordExp w c₀ mul ysMul : ℕ} {C_sp : ℝ}
    {Ψ : BundleTreeState depth → ℕ}
    (hwe : 3 * capExp ≤ wordExp) (hp : 1 ≤ max impl.p_s impl.p_t)
    (hys : 4 * capExp + 5 ≤ ysMul)
    (hC : 0 < C_sp)
    (hγ : ∀ m, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    (hCost : AsmFsCostGoal tourBundleSpec impl P L capExp limbMul wordExp w Ψ
      ((LSc).envStep.bSelf + 7) ((LSc).envStep.bSelf + 4) ((LSc).envStep.bSelf + 5) pSc
      (asmFsRootSc impl cf firstInit w) (LSc).bBun ((LSc).envStep.bSelf + 48)
      ((LSc).envStep.bSelf + 9) ((LSc).envStep.bSelf + 10) (asmFsKSc impl cf firstInit w) mul
      (asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp)) :
    AsmFsPieces TRc scProgB5 impl P L capExp limbMul wordExp w Ψ pSc (LSc).I.fCoreS mul ysMul
      (asmFirstStepSpacePolyStd c₀ impl.cw capExp C_sp) := by
  have hS := asmFsStep_scProg_has impl cf firstInit
  have hT := scProg_hasTour impl cf asmFsStepCode firstInit
  have hB := scProg_hasBundle impl cf asmFsStepCode firstInit
  have hBu := bundleProcs_unpack hB
  have hTR_loc : ∀ v e, (TRc v e).Local := fun v e =>
    asmTourRepWithPot_local tourAsmRep_local (bundleScanPotMul tourBundleSpec) v e
  have hTh : ∀ vCap eCap tourH (tx : (TRc vCap eCap).τ), (TRc vCap eCap).foot tourH tx tourH :=
    asmTourRepWithPot_foot_self tourAsmRep_handle_foot (bundleScanPotMul tourBundleSpec)
  have hP2 := asmFirstStep_hP2 (TS := tourBundleSpec) (P := P) (L := L) (limbMul := limbMul)
    (Ψ := Ψ) (fInitOne := (LSc).envStep.bSelf + 4)
    (fInitSpan := (LSc).envStep.bSelf + 5) (fExp := (LSc).envStep.bSelf + 6) hB
    (asmFsRootSc impl cf firstInit w)
    (asmTourRepWithPot_bundleBridge (tourDS_asmBrTourBridge w (LSc).bTour pSc hT)
      (bundleScanPotMul tourBundleSpec))
    (hasAt_getElem? hS (i := 4) rfl) (hasAt_getElem? hS (i := 5) rfl)
    (hasAt_getElem? hS (i := 6) rfl) hBu.2.2.2.2.2.2.1
    (scProg_hasSpan impl cf asmFsStepCode firstInit) hTR_loc hTh hwe
    (asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp)
    (fun A hA => by rw [asmFsRootSc_querySpace]; exact asmFirstStep_hSp2_std (c₀ := c₀) hC hγ A hA)
  have hP3 := asmFirstStep_hP3 (TS := tourBundleSpec) (P := P) (L := L) (limbMul := limbMul)
    (Ψ := Ψ) (fInitOne := (LSc).envStep.bSelf + 4)
    (fInitSpan := (LSc).envStep.bSelf + 5) (asmFsRootSc impl cf firstInit w) hB hT
    (scProg_hasOut impl cf asmFsStepCode firstInit) (scProg_hasCopy impl cf asmFsStepCode firstInit)
    (asmFsStep_hasTourBlock hS) (hasAt_getElem? hS (i := 9) rfl)
    (hasAt_getElem? hS (i := 10) rfl) hwe (asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp)
    (fun A hA => by rw [asmFsRootSc_querySpace]; exact asmFirstStep_hSp3_std (c₀ := c₀) hC hγ A hA)
  have hSp4 := asmFirstStep_hSp4_std (c₀ := c₀) (capExp := capExp) (depth := depth)
    (P := P) (L := L)
    (limbMul := limbMul) (wordExp := wordExp) (Ψ := Ψ) (fInitOne := (LSc).envStep.bSelf + 4)
    (fInitSpan := (LSc).envStep.bSelf + 5) (bBun := (LSc).bBun)
    (bTourStep := (LSc).envStep.bSelf + 48) (fDelTriples := (LSc).envStep.bSelf + 9)
    (fBuildGroups := (LSc).envStep.bSelf + 10)
    (asmFsRootSc_querySpace impl cf firstInit w) (asmFsKSc_querySpace impl cf firstInit w) hC hγ
  have hSpG := asmFirstStep_hSpG_std (c₀ := c₀) (capExp := capExp) (depth := depth)
    (P := P) (L := L)
    (limbMul := limbMul) (wordExp := wordExp) (Ψ := Ψ) (fInitOne := (LSc).envStep.bSelf + 4)
    (fInitSpan := (LSc).envStep.bSelf + 5) (bBun := (LSc).bBun)
    (bTourStep := (LSc).envStep.bSelf + 48) (fDelTriples := (LSc).envStep.bSelf + 9)
    (fBuildGroups := (LSc).envStep.bSelf + 10) (K := asmFsKSc impl cf firstInit w)
    (asmFsRootSc_querySpace impl cf firstInit w) (asmFsKSc_querySpace impl cf firstInit w) hC hγ
  have hP4 := asmFirstStep_hP4 (TS := tourBundleSpec) (asmFsRootSc impl cf firstInit w)
    (asmFsKSc impl cf firstInit w) hwe (asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp) hSp4
    (asmFirstStep_hOpen (asmFsRootSc impl cf firstInit w))
    asmFirstStep_hVerts
  have hNC := asmFirstStep_hNC_full (K := asmFsKSc impl cf firstInit w) hys hp
    asmFirstStep_sideWordBounds_of_spaceStd (fun A hA => (asmFirstStep_hVerts A hA).1) hSpG
  exact ⟨(LSc).envStep.bSelf + 1, (LSc).envStep.bSelf + 2, (LSc).envStep.bSelf + 3,
    (LSc).envStep.bSelf + 8, (LSc).envStep.bSelf + 11, _, _, _, _, _, _, _,
    hasAt_getElem? hS (i := 0) rfl, hasAt_getElem? hS (i := 1) rfl,
    hasAt_getElem? hS (i := 2) rfl, hasAt_getElem? hS (i := 3) rfl,
    hasAt_getElem? hS (i := 8) rfl, hasAt_getElem? hS (i := 11) rfl,
    asmFirstStepSpaceFnStd_mono c₀ impl.cw capExp C_sp,
    asmFirstStepSpaceFnStd_le_poly c₀ impl.cw capExp C_sp, asmFirstStep_hSp1_std, hP2, hP3, hP4,
    asmFirstStep_hPost_of hNC hCost⟩

end

end MinCostFlow.SparseCore.Program
