module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInit
public import MinCostFlow.SparseCore.Program.AssemblyCode
public import MinCostFlow.SparseCore.Program.TourAsmBridge
public import MinCostFlow.SparseCore.Program.AssemblyFirstWalkPot

/-!
# The first phase of the init of a branch as a block of `scProg` (`AssemblyFirstInitCode`)

The single sparse-core program `scProg` (`AssemblyCode.lean`) takes the first phase of the init
of a branch as a block of procedures, `firstInit : ScSubCode`, placed at `L.bFirstI` with its main
procedure at `L.bFirstI + firstInit.offMain`. This file gives that block for the program
`asmFirstInitStmt` (`AssemblyFirstInitBuild.lean`), and proves `AsmBrCoreInitAt` for it inside
`scProg`.

The block `asmFirstInitCode build` is, from its base `b`:
* at `b`, the main procedure `asmFirstInitStmt`;
* at `b + 1`, scfirst's export procedure `asmFirstExportDynGraphStmt`;
* from `b + 2` on, the procedures of the build, a block `build : ScSubCode` placed at base `b + 2`
  with the same fixed bases of the other pieces.

`asmBrCoreInitAt_scProg` proves `AsmBrCoreInitAt` at the main procedure from the build at its main
procedure (`AsmFirstInitBuildAt`, at the index `asmFirstInitBuildIdx`), by
`asmBrCoreInitAt_of_build`. Its multiplier is that of the build plus `500`
(`asmFirstInitMul`), and its space is `asmFirstInitSpace` of the space of the build.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio

/-- The fixed bases of a block placed `2` cells after the block with bases `env`. -/
def ScFirstEnv.shift2 (env : ScFirstEnv) : ScFirstEnv := { env with bSelf := env.bSelf + 2 }

/-- **The block of the first phase of the init**, from the block `build` of the build: the main
procedure, the export procedure, then the build at base `bSelf + 2`. -/
def asmFirstInitCode (build : ScSubCode) : ScSubCode where
  procs env := asmFirstInitStmt (env.bSelf + 2 + build.offMain) (env.bSelf + 1) ::
    asmFirstExportDynGraphStmt :: build.procs env.shift2
  hnoRand env s hs := by
    simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | hs
    · exact asmFirstInitStmt_noRand _ _
    · exact asmFirstExportDynGraphStmt_noRand
    · exact build.hnoRand _ s hs
  offMain := 0

/-- **Where the procedures of the block are**, when the block is placed at the base `b` of `env`. -/
theorem asmFirstInitCode_hasAt {p : Program} {build : ScSubCode} {env : ScFirstEnv} {b : ℕ}
    (henv : env.bSelf = b) (h : p.HasAt b ((asmFirstInitCode build).procs env)) :
    p.procs[b]? = some (asmFirstInitStmt (b + 2 + build.offMain) (b + 1)) ∧
    p.procs[b + 1]? = some asmFirstExportDynGraphStmt ∧
    p.HasAt (b + 2) (build.procs env.shift2) := by
  subst henv
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · have h0 := h 0 (by simp [asmFirstInitCode])
    simpa [asmFirstInitCode] using h0
  · have h1 := h 1 (by simp [asmFirstInitCode])
    simpa [asmFirstInitCode] using h1
  · have h2 := h (i + 2) (by simp [asmFirstInitCode]; omega)
    rw [show env.bSelf + (i + 2) = env.bSelf + 2 + i by omega] at h2
    simpa [asmFirstInitCode] using h2

/-- **The first phase of the init at the base `b` of a program**, when the block
`asmFirstInitCode build` is placed at `b` and the build meets `AsmFirstInitBuildAt` at its main
procedure `b + 2 + build.offMain`. -/
noncomputable def asmBrCoreInitAt_of_code {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {CFR : DSRep CompFamilyAbs} {lsfInit : LSFInit} {impl : SparsifyImpl}
    {depth P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {build : ScSubCode} {env : ScFirstEnv} {b : ℕ}
    (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    (henv : env.bSelf = b) (hblk : p.HasAt b ((asmFirstInitCode build).procs env))
    (B : AsmFirstInitBuildAt TR B5 CFR lsfInit impl depth P L capExp limbMul wordExp w Ψ p
      (b + 2 + build.offMain)) :
    AsmBrCoreInitAt TR B5 CFR lsfInit impl depth P L capExp limbMul wordExp w Ψ p b :=
  asmBrCoreInitAt_of_build hTR hB5 B (asmFirstInitCode_hasAt henv hblk).1
    (asmFirstInitCode_hasAt henv hblk).2.1

/-- The index of the main procedure of the build inside `scProg`. -/
def asmFirstInitBuildIdx (impl : SparsifyImpl) (cf : ScCompCode) (firstStep build : ScSubCode) :
    ℕ :=
  (scLayout impl cf firstStep (asmFirstInitCode build)).bFirstI + 2 + build.offMain

theorem scLayout_envInit_bSelf (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) :
    (scLayout impl cf firstStep firstInit).envInit.bSelf =
      (scLayout impl cf firstStep firstInit).bFirstI := rfl

theorem scLayout_fCoreI (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep firstInit : ScSubCode) :
    (scLayout impl cf firstStep firstInit).I.fCoreI =
      (scLayout impl cf firstStep firstInit).bFirstI + firstInit.offMain := rfl

theorem asmFirstInitCode_offMain (build : ScSubCode) : (asmFirstInitCode build).offMain = 0 := rfl

/-- **A first phase of the init at an equal index**, with the same multiplier and space. -/
def AsmBrCoreInitAt.cast {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {CFR : DSRep CompFamilyAbs} {lsfInit : LSFInit} {impl : SparsifyImpl}
    {depth P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {f f' : ℕ} (e : f = f')
    (V : AsmBrCoreInitAt TR B5 CFR lsfInit impl depth P L capExp limbMul wordExp w Ψ p f) :
    AsmBrCoreInitAt TR B5 CFR lsfInit impl depth P L capExp limbMul wordExp w Ψ p f' where
  mul := V.mul
  space := V.space
  runs := e ▸ V.runs

theorem scLayout_fCoreI_asmFirstInit (impl : SparsifyImpl) (cf : ScCompCode)
    (firstStep build : ScSubCode) :
    (scLayout impl cf firstStep (asmFirstInitCode build)).bFirstI =
      (scLayout impl cf firstStep (asmFirstInitCode build)).I.fCoreI := by
  rw [scLayout_fCoreI, asmFirstInitCode_offMain, Nat.add_zero]

/-- **The first phase of the init inside `scProg`.** Given the locality of the tour family and of
the bundle tables, and the build at its main procedure in `scProg`, the main procedure of the
block `asmFirstInitCode build` (the procedure `fCoreI` of the layout) meets `AsmBrCoreInitAt`, with
multiplier `asmFirstInitMul B.mul` and space `asmFirstInitSpace B.space`
(`asmBrCoreInitAt_scProg_mul`). -/
noncomputable def asmBrCoreInitAt_scProg {impl : SparsifyImpl} {cf : ScCompCode}
    {firstStep build : ScSubCode} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {CFR : DSRep CompFamilyAbs} {lsfInit : LSFInit}
    {depth P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ}
    (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    (B : AsmFirstInitBuildAt TR B5 CFR lsfInit impl depth P L capExp limbMul wordExp w Ψ
      (scProg impl cf firstStep (asmFirstInitCode build))
      (asmFirstInitBuildIdx impl cf firstStep build)) :
    AsmBrCoreInitAt TR B5 CFR lsfInit impl depth P L capExp limbMul wordExp w Ψ
      (scProg impl cf firstStep (asmFirstInitCode build))
      (scLayout impl cf firstStep (asmFirstInitCode build)).I.fCoreI :=
  AsmBrCoreInitAt.cast (scLayout_fCoreI_asmFirstInit impl cf firstStep build)
    (asmBrCoreInitAt_of_code hTR hB5 (scLayout_envInit_bSelf impl cf firstStep _)
      (scProg_blocks impl cf firstStep (asmFirstInitCode build)).2.2.2.2.2.2.2.2.2.1 B)

/-- The multiplier and the space of `asmBrCoreInitAt_scProg`. -/
theorem asmBrCoreInitAt_scProg_mul {impl : SparsifyImpl} {cf : ScCompCode}
    {firstStep build : ScSubCode} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {CFR : DSRep CompFamilyAbs} {lsfInit : LSFInit}
    {depth P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ}
    (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    (B : AsmFirstInitBuildAt TR B5 CFR lsfInit impl depth P L capExp limbMul wordExp w Ψ
      (scProg impl cf firstStep (asmFirstInitCode build))
      (asmFirstInitBuildIdx impl cf firstStep build)) :
    (asmBrCoreInitAt_scProg hTR hB5 B).mul = asmFirstInitMul B.mul ∧
      (asmBrCoreInitAt_scProg hTR hB5 B).space = asmFirstInitSpace B.space :=
  ⟨rfl, rfl⟩

/-- The bundle tables of the branch: P5's tables with the headroom invariant, with the bundle cap
first. -/
abbrev asmFirstB5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState) :=
  fun k slotCap vCap eCap => Restart.bunTableHeadroomRep slotCap vCap eCap k

/-- **The first phase of the init inside `scProg`, at the parts the branch uses**: the tour family
`tourAsmRep`, the bundle tables `asmFirstB5` and the walk potential `walkPot`. -/
noncomputable def asmBrCoreInitAt_scProg_used {impl : SparsifyImpl} {cf : ScCompCode}
    {firstStep build : ScSubCode} {CFR : DSRep CompFamilyAbs} {lsfInit : LSFInit}
    {depth P L capExp limbMul wordExp w : ℕ}
    (B : AsmFirstInitBuildAt tourAsmRep asmFirstB5 CFR lsfInit impl depth P L capExp limbMul
      wordExp w walkPot (scProg impl cf firstStep (asmFirstInitCode build))
      (asmFirstInitBuildIdx impl cf firstStep build)) :
    AsmBrCoreInitAt tourAsmRep asmFirstB5 CFR lsfInit impl depth P L capExp limbMul wordExp w
      walkPot (scProg impl cf firstStep (asmFirstInitCode build))
      (scLayout impl cf firstStep (asmFirstInitCode build)).I.fCoreI :=
  asmBrCoreInitAt_scProg tourAsmRep_local
    (fun k slotCap vCap eCap => Restart.bunTableHeadroomRep_local slotCap vCap eCap k) B

/-- The multiplier and the space of `asmBrCoreInitAt_scProg_used`. -/
theorem asmBrCoreInitAt_scProg_used_mul {impl : SparsifyImpl} {cf : ScCompCode}
    {firstStep build : ScSubCode} {CFR : DSRep CompFamilyAbs} {lsfInit : LSFInit}
    {depth P L capExp limbMul wordExp w : ℕ}
    (B : AsmFirstInitBuildAt tourAsmRep asmFirstB5 CFR lsfInit impl depth P L capExp limbMul
      wordExp w walkPot (scProg impl cf firstStep (asmFirstInitCode build))
      (asmFirstInitBuildIdx impl cf firstStep build)) :
    (asmBrCoreInitAt_scProg_used B).mul = asmFirstInitMul B.mul ∧
      (asmBrCoreInitAt_scProg_used B).space = asmFirstInitSpace B.space :=
  ⟨rfl, rfl⟩

end MinCostFlow.SparseCore.Program
