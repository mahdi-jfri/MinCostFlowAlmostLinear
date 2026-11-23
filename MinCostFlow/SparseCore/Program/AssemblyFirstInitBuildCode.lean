module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBuildRun
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitTourPot
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitCode
public import MinCostFlow.Num.ModulePlacement
import Mathlib.Tactic

/-!
# The build of a branch at its init as a block of `scProg` (`AssemblyFirstInitBuildCode`)

The first phase of the init of a branch is the block `asmFirstInitCode build`
(`AssemblyFirstInitCode.lean`). It places the block `build` of the build at its base plus `2`.
Here we give that block, `asmFirstInitBuildCode`, and prove `AsmBrCoreInitAt` for the first phase
inside `scProg` (`asmBrCoreInitAt_scProg_build`).

The block of the build holds, from its base `b`, the body of the build and the procedures that only
the build calls:
* `b`: the body `asmFirstInitBuildBody`;
* `b + 1` to `b + 6`: P2's init of the tour, the sorted roots, P5's table, P6's spanners, the export
  of a slot, and the export of a graph in the form `DynGraphAt`;
* `b + 7`: the map to the components (`compMapModule`, `3` procedures);
* `b + 10`: the back (`asmFirstInitBackModule`, `12` procedures);
* `b + 22`: the slot lists (`slotListModule`, `5` procedures);
* `b + 27`: the bucket table (`bucketTableModule`).

The other procedures that the build calls are shared with the rest of `scProg`: P5's procedures
(with the sort and the export of a bundle graph), P6's, P2's, and P10's reads. Their bases are in
the environment `env` of the block.

`asmFirstInitBuildAt_of_block` proves `AsmFirstInitBuildAt` for a block placed at the base of
`env`, from `asmFirstInitBuildAt_mk` (`AssemblyFirstInitBuildRun.lean`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.Expander
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The procedures of the build when its block is at base `b`. -/
def asmFirstInitBuildProcsAt (b : ℕ) : AsmFirstInitProcs where
  fTour := b + 1
  fBkt := b + 27
  fComp := b + 7
  fSlot := b + 22
  fRoots := b + 2
  fBun := b + 3
  fSpan := b + 4
  fRootTbl := b + 10
  fS0 := b + 11
  fMark := b + 17
  fEmb := b + 19

/-- The first seven procedures of the block of the build. -/
def asmFirstInitBuildHead (env : ScFirstEnv) : List Stmt :=
  [asmFirstInitBuildBody (asmFirstInitBuildProcsAt env.bSelf),
    tourBranchInitStmt (tourInit env.bTour),
    rootsListBody (env.bBun + bundleOffSort),
    asmFirstInitBunBody (env.bBun + bundleIdxTableInit) (env.bBun + bundleIdxInitSlots),
    asmFirstInitSpanBody (env.bSelf + 5) (env.bSpan + bsIdxOp0 + 0),
    asmFirstInitExpBody (env.bBun + bundleIdxExportGraph),
    asmFirstExportDynGraphStmt]

/-- **The procedures of the block of the build**, at the base `env.bSelf`. -/
def asmFirstInitBuildList (env : ScFirstEnv) : List Stmt :=
  asmFirstInitBuildHead env ++
    (compMapModule (env.bSelf + 7) ++
      (asmFirstInitBackModule env.readLib env.bRead env.bSpan env.bTour (env.bSelf + 7)
          (env.bSelf + 6) (env.bSelf + 10) ++
        (slotListModule (env.bSelf + 22) ++ bucketTableModule (env.bSelf + 27))))

/-- **The block of the build**, with its main procedure at its base. -/
def asmFirstInitBuildCode : ScSubCode where
  procs := asmFirstInitBuildList
  hnoRand env s hs := by
    simp only [asmFirstInitBuildList, asmFirstInitBuildHead, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    rcases hs with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hs | hs | hs | hs
    · exact asmFirstInitBuildBody_noRand _
    · exact tourBranchInitStmt_noRand _
    · exact rootsListBody_noRand _
    · exact asmFirstInitBunBody_noRand _ _
    · exact asmFirstInitSpanBody_noRand _ _
    · exact asmFirstInitExpBody_noRand _
    · exact asmFirstExportDynGraphStmt_noRand
    · simp only [compMapModule, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl
      · exact compMapBody_noRand _ _
      · exact buildCsrProc_noRand
      · exact bfsLabelsProc_noRand
    · exact asmFirstInitBackModule_noRand _ _ _ _ _ _ _ s hs
    · exact slotListModule_noRand _ s hs
    · exact bucketTableModule_noRand _ s hs
  offMain := 0

/-- **Where the procedures of the block of the build are**, when the block is at the base of
`env`. -/
theorem asmFirstInitBuildList_hasAt {p : Program} {env : ScFirstEnv}
    (h : p.HasAt env.bSelf (asmFirstInitBuildList env)) :
    p.procs[env.bSelf]? = some (asmFirstInitBuildBody (asmFirstInitBuildProcsAt env.bSelf)) ∧
    p.procs[env.bSelf + 1]? = some (tourBranchInitStmt (tourInit env.bTour)) ∧
    p.procs[env.bSelf + 2]? = some (rootsListBody (env.bBun + bundleOffSort)) ∧
    p.procs[env.bSelf + 3]? =
      some (asmFirstInitBunBody (env.bBun + bundleIdxTableInit) (env.bBun + bundleIdxInitSlots)) ∧
    p.procs[env.bSelf + 4]? =
      some (asmFirstInitSpanBody (env.bSelf + 5) (env.bSpan + bsIdxOp0 + 0)) ∧
    p.procs[env.bSelf + 5]? = some (asmFirstInitExpBody (env.bBun + bundleIdxExportGraph)) ∧
    p.procs[env.bSelf + 6]? = some asmFirstExportDynGraphStmt ∧
    p.HasAt (env.bSelf + 7) (compMapModule (env.bSelf + 7)) ∧
    p.HasAt (env.bSelf + 10) (asmFirstInitBackModule env.readLib env.bRead env.bSpan env.bTour
      (env.bSelf + 7) (env.bSelf + 6) (env.bSelf + 10)) ∧
    p.HasAt (env.bSelf + 22) (slotListModule (env.bSelf + 22)) ∧
    p.HasAt (env.bSelf + 27) (bucketTableModule (env.bSelf + 27)) := by
  have hH := MinCostFlow.Num.hasAt_append_left h
  have hR1 := MinCostFlow.Num.hasAt_append_right h
  have e1 : env.bSelf + (asmFirstInitBuildHead env).length = env.bSelf + 7 := rfl
  rw [e1] at hR1
  have hC := MinCostFlow.Num.hasAt_append_left hR1
  have hR2 := MinCostFlow.Num.hasAt_append_right hR1
  have e2 : env.bSelf + 7 + (compMapModule (env.bSelf + 7)).length = env.bSelf + 10 := rfl
  rw [e2] at hR2
  have hB := MinCostFlow.Num.hasAt_append_left hR2
  have hR3 := MinCostFlow.Num.hasAt_append_right hR2
  have e3 : env.bSelf + 10 + (asmFirstInitBackModule env.readLib env.bRead env.bSpan env.bTour
      (env.bSelf + 7) (env.bSelf + 6) (env.bSelf + 10)).length = env.bSelf + 22 := by
    rw [asmFirstInitBackModule_length]
  rw [e3] at hR3
  have hS := MinCostFlow.Num.hasAt_append_left hR3
  have hK := MinCostFlow.Num.hasAt_append_right hR3
  have e4 : env.bSelf + 22 + (slotListModule (env.bSelf + 22)).length = env.bSelf + 27 := by
    simp only [slotListModule, List.length_cons, sortProcs_length]
  rw [e4] at hK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hC, hB, hS, hK⟩
  · simpa [asmFirstInitBuildHead] using hH 0 (by simp [asmFirstInitBuildHead])
  · simpa [asmFirstInitBuildHead] using hH 1 (by simp [asmFirstInitBuildHead])
  · simpa [asmFirstInitBuildHead] using hH 2 (by simp [asmFirstInitBuildHead])
  · simpa [asmFirstInitBuildHead] using hH 3 (by simp [asmFirstInitBuildHead])
  · simpa [asmFirstInitBuildHead] using hH 4 (by simp [asmFirstInitBuildHead])
  · simpa [asmFirstInitBuildHead] using hH 5 (by simp [asmFirstInitBuildHead])
  · simpa [asmFirstInitBuildHead] using hH 6 (by simp [asmFirstInitBuildHead])

/-- **The build from its block.** If the block of the build is at the base of `env` in `p`, and
P2's, P5's, P6's and P10's procedures are at the bases of `env`, then the build meets
`AsmFirstInitBuildAt` on `asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)` at the
base of `env`, with multiplier `asmFiBuildCostMul capExp limbMul + asmFiTourPotMul capExp` and
space `asmFiBuildSpacePoly impl.cw Cγ cγ capExp`. The facts outside the run are those of
`asmFirstInitBuildAt_mk`. -/
noncomputable def asmFirstInitBuildAt_of_block {depth P L capExp limbMul wordExp w Cγ cγ : ℕ}
    {impl : SparsifyImpl} {lsfInit : LSFInit} {CFR : DSRep CompFamilyAbs} {p : Program}
    {env : ScFirstEnv} (hblk : p.HasAt env.bSelf (asmFirstInitBuildList env))
    (hpT : HasTourProcs p env.bTour)
    (hpB : p.HasAt env.bBun
      (bundleProcs env.bBun (tourOp env.bTour 4) (tourOp env.bTour 12) (tourOp env.bTour 10)))
    (hpSp : p.HasAt env.bSpan (bucketSpannerProcs impl env.bSpan))
    (hRL : env.readLib.Has p)
    (hpRead : p.HasAt env.bRead (readBranchProcs env.readLib env.fCFRoot env.bRead))
    (hd : 1 ≤ depth) (hp : 1 ≤ max impl.p_s impl.p_t)
    (hInit : ∀ k j, j < k → ∃ C_lsst, IsValidLSFInitFor lsfInit C_lsst k j)
    (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ) :
    AsmFirstInitBuildAt (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5
      CFR lsfInit impl depth P L capExp limbMul wordExp w walkPot p env.bSelf :=
  have hB := bundleProcs_unpack hpB
  have hb := asmFirstInitBuildList_hasAt hblk
  asmFirstInitBuildAt_withTourPot
    (asmFirstInitBuildAt_mk (asmFirstInitBuildProcsAt env.bSelf) hb.1 hb.2.1
      hb.2.2.2.2.2.2.2.2.2.2 hb.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.2.1 hB.1 hb.2.2.1 hpT hpB
      hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2.1 hB.2.2.2.2.2.2.1 hpSp rfl rfl rfl rfl hRL hpRead
      hb.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.1 hd hp hInit hγ)

/-- The multiplier and the space of `asmFirstInitBuildAt_of_block`. -/
theorem asmFirstInitBuildAt_of_block_mul {depth P L capExp limbMul wordExp w Cγ cγ : ℕ}
    {impl : SparsifyImpl} {lsfInit : LSFInit} {CFR : DSRep CompFamilyAbs} {p : Program}
    {env : ScFirstEnv} (hblk : p.HasAt env.bSelf (asmFirstInitBuildList env))
    (hpT : HasTourProcs p env.bTour)
    (hpB : p.HasAt env.bBun
      (bundleProcs env.bBun (tourOp env.bTour 4) (tourOp env.bTour 12) (tourOp env.bTour 10)))
    (hpSp : p.HasAt env.bSpan (bucketSpannerProcs impl env.bSpan))
    (hRL : env.readLib.Has p)
    (hpRead : p.HasAt env.bRead (readBranchProcs env.readLib env.fCFRoot env.bRead))
    (hd : 1 ≤ depth) (hp : 1 ≤ max impl.p_s impl.p_t)
    (hInit : ∀ k j, j < k → ∃ C_lsst, IsValidLSFInitFor lsfInit C_lsst k j)
    (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ) :
    (asmFirstInitBuildAt_of_block (P := P) (L := L) (wordExp := wordExp) (w := w)
        (capExp := capExp) (limbMul := limbMul) (CFR := CFR) hblk hpT hpB hpSp hRL hpRead hd hp
        hInit hγ).mul = asmFiBuildCostMul capExp limbMul + asmFiTourPotMul capExp ∧
      (asmFirstInitBuildAt_of_block (P := P) (L := L) (wordExp := wordExp) (w := w)
        (capExp := capExp) (limbMul := limbMul) (CFR := CFR) hblk hpT hpB hpSp hRL hpRead hd hp
        hInit hγ).space = asmFiBuildSpacePoly impl.cw Cγ cγ capExp :=
  ⟨rfl, rfl⟩

/-! ## The build inside `scProg` -/

/-- The index of the build inside `scProg` is the base of its block, `bFirstI + 2`. -/
theorem asmFirstInitBuildIdx_eq (impl : SparsifyImpl) (cf : ScCompCode) (firstStep : ScSubCode) :
    asmFirstInitBuildIdx impl cf firstStep asmFirstInitBuildCode =
      (scLayout impl cf firstStep (asmFirstInitCode asmFirstInitBuildCode)).envInit.shift2.bSelf := by
  rw [asmFirstInitBuildIdx, show asmFirstInitBuildCode.offMain = 0 from rfl, Nat.add_zero,
    ScFirstEnv.shift2, scLayout_envInit_bSelf]

/-- **The build inside `scProg`.** With the first phase of the init `asmFirstInitCode
asmFirstInitBuildCode`, the block of the build is at `bFirstI + 2` with the bases of P2, P5, P6
and P10 of `scProg` (`ScFirstEnv.shift2` of the environment of the first phase). So the build meets
`AsmFirstInitBuildAt` at its index `asmFirstInitBuildIdx`. -/
noncomputable def asmFirstInitBuildAt_scProg {impl : SparsifyImpl} {cf : ScCompCode}
    {firstStep : ScSubCode} {depth P L capExp limbMul wordExp w Cγ cγ : ℕ} {lsfInit : LSFInit}
    {CFR : DSRep CompFamilyAbs}
    (hd : 1 ≤ depth) (hp : 1 ≤ max impl.p_s impl.p_t)
    (hInit : ∀ k j, j < k → ∃ C_lsst, IsValidLSFInitFor lsfInit C_lsst k j)
    (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ) :
    AsmFirstInitBuildAt (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5
      CFR lsfInit impl depth P L capExp limbMul wordExp w walkPot
      (scProg impl cf firstStep (asmFirstInitCode asmFirstInitBuildCode))
      (asmFirstInitBuildIdx impl cf firstStep asmFirstInitBuildCode) :=
  let Lc := scLayout impl cf firstStep (asmFirstInitCode asmFirstInitBuildCode)
  let env : ScFirstEnv :=
    { Lc.envInit with bSelf := asmFirstInitBuildIdx impl cf firstStep asmFirstInitBuildCode }
  have henv : Lc.envInit.shift2 = env := by
    simp only [env, asmFirstInitBuildIdx_eq]
    rfl
  have hblk : (scProg impl cf firstStep (asmFirstInitCode asmFirstInitBuildCode)).HasAt env.bSelf
      (asmFirstInitBuildList env) :=
    henv ▸ (asmFirstInitCode_hasAt (scLayout_envInit_bSelf impl cf firstStep _)
      (scProg_hasFirstInit impl cf firstStep _)).2.2
  asmFirstInitBuildAt_of_block (env := env) hblk (scProg_hasTour impl cf firstStep _)
    (scProg_hasBundle impl cf firstStep _) (scProg_hasSpan impl cf firstStep _)
    (scProg_hasReadLib impl cf firstStep _) (scProg_blocks impl cf firstStep _).2.2.1 hd hp hInit
    hγ

/-- **The first phase of the init inside `scProg`, with the block of the build.** It meets
`AsmBrCoreInitAt` on `asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)` at the
procedure `fCoreI` of the layout, with multiplier
`asmFirstInitMul (asmFiBuildCostMul capExp limbMul + asmFiTourPotMul capExp)` and space
`asmFirstInitSpace (asmFiBuildSpacePoly impl.cw Cγ cγ capExp)` (`asmBrCoreInitAt_scProg_build_mul`). -/
noncomputable def asmBrCoreInitAt_scProg_build {impl : SparsifyImpl} {cf : ScCompCode}
    {firstStep : ScSubCode} {depth P L capExp limbMul wordExp w Cγ cγ : ℕ} {lsfInit : LSFInit}
    {CFR : DSRep CompFamilyAbs}
    (hd : 1 ≤ depth) (hp : 1 ≤ max impl.p_s impl.p_t)
    (hInit : ∀ k j, j < k → ∃ C_lsst, IsValidLSFInitFor lsfInit C_lsst k j)
    (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ) :
    AsmBrCoreInitAt (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5 CFR
      lsfInit impl depth P L capExp limbMul wordExp w walkPot
      (scProg impl cf firstStep (asmFirstInitCode asmFirstInitBuildCode))
      (scLayout impl cf firstStep (asmFirstInitCode asmFirstInitBuildCode)).I.fCoreI :=
  asmBrCoreInitAt_scProg
    (asmTourRepWithPot_local tourAsmRep_local (bundleScanPotMul tourBundleSpec))
    (fun k slotCap vCap eCap => bunTableHeadroomRep_local slotCap vCap eCap k)
    (asmFirstInitBuildAt_scProg hd hp hInit hγ)

/-- The multiplier and the space of `asmBrCoreInitAt_scProg_build`. -/
theorem asmBrCoreInitAt_scProg_build_mul {impl : SparsifyImpl} {cf : ScCompCode}
    {firstStep : ScSubCode} {depth P L capExp limbMul wordExp w Cγ cγ : ℕ} {lsfInit : LSFInit}
    {CFR : DSRep CompFamilyAbs}
    (hd : 1 ≤ depth) (hp : 1 ≤ max impl.p_s impl.p_t)
    (hInit : ∀ k j, j < k → ∃ C_lsst, IsValidLSFInitFor lsfInit C_lsst k j)
    (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ Cγ * (m + 2) ^ cγ) :
    (asmBrCoreInitAt_scProg_build (cf := cf) (firstStep := firstStep) (P := P) (L := L)
        (wordExp := wordExp) (w := w) (capExp := capExp) (limbMul := limbMul) (CFR := CFR) hd hp
        hInit hγ).mul =
        asmFirstInitMul (asmFiBuildCostMul capExp limbMul + asmFiTourPotMul capExp) ∧
      (asmBrCoreInitAt_scProg_build (cf := cf) (firstStep := firstStep) (P := P) (L := L)
        (wordExp := wordExp) (w := w) (capExp := capExp) (limbMul := limbMul) (CFR := CFR) hd hp
        hInit hγ).space = asmFirstInitSpace (asmFiBuildSpacePoly impl.cw Cγ cγ capExp) :=
  ⟨rfl, rfl⟩

end MinCostFlow.SparseCore.Program
