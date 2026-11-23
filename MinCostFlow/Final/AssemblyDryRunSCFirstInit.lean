module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBuildCode
public import MinCostFlow.Final.AssemblyDryRunSCStretch

/-!
# The first phase of the init of a branch in the dry run (`AssemblyDryRunSCFirstInit`)

`theorem_1_1_skeleton` (`Final/Theorem11Skeleton.lean`) takes the first phase of the init of a
branch as a block `firstInit : ScSubCode`, with the hypothesis `hFirstInit`: for every
`1 ≤ depth`, every P4 family `CF` in `scProg`, and `P ≤ 4 * L_in`, the procedure `fCoreI` of the
layout meets `AsmBrCoreInitAt`, with multiplier `C.initMul capExp limbMul` and space
`C.initSpace capExp`.

Here we close `hFirstInit` for the block `dryFirstInit = asmFirstInitCode asmFirstInitBuildCode`
(`drySC_hFirstInit`). The first phase is `asmBrCoreInitAt_scProg_build`
(`AssemblyFirstInitBuildCode.lean`), at the sparsifier `sparsifyImplUsed` and the LSF init
`dryLSFInitUsed L_in fmt.precision` of the dry run. Its three facts outside the run hold there:
* `1 ≤ max p_s p_t`, since `sparsifyImplUsed.p_s = 1` (`sparsifyImplUsed_p_s`);
* a valid LSF init for each branch `j < k`, at `dryCLsstUsed`
  (`dryLSFInitUsed_isValidLSFInitFor`);
* a polynomial bound on the stretch of `sparsifyImplUsed`, with the constants `dryFiCγ` and
  `dryFicγ` chosen from `sparsifyPolyStretch_sparsifyImplUsed`.

The multiplier is `dryFirstInitMul capExp limbMul` and the space `dryFirstInitSpace capExp`. The
constants `C` of `theorem_1_1_skeleton` are shared with the first phase of a step, so `drySC_hFirstInit`
takes the two equalities `C.initMul = dryFirstInitMul` and `C.initSpace = dryFirstInitSpace` as
hypotheses.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM MinCostFlow.SparseCore MinCostFlow.SparseCore.Program MinCostFlow.DynSpanner.Program

/-- The factor of the polynomial bound on the stretch of `sparsifyImplUsed`. -/
def dryFiCγ : ℕ := Classical.choose sparsifyPolyStretch_sparsifyImplUsed

/-- The degree of the polynomial bound on the stretch of `sparsifyImplUsed`. -/
def dryFicγ : ℕ := Classical.choose (Classical.choose_spec sparsifyPolyStretch_sparsifyImplUsed)

/-- The stretch of `sparsifyImplUsed` at `m` is at most `dryFiCγ * (m + 2) ^ dryFicγ`. -/
theorem dryFi_stretch (m : ℕ) : ⌈sparsifyImplUsed.γ_ℓ m⌉₊ ≤ dryFiCγ * (m + 2) ^ dryFicγ :=
  Classical.choose_spec (Classical.choose_spec sparsifyPolyStretch_sparsifyImplUsed) m

/-- `sparsifyImplUsed` has `1 ≤ max p_s p_t`, since its `p_s` is `1`. -/
theorem sparsifyImplUsed_one_le_max_p :
    1 ≤ max sparsifyImplUsed.p_s sparsifyImplUsed.p_t := by
  rw [sparsifyImplUsed_p_s]
  exact le_max_left _ _

/-- **The first phase of the init of a branch in the dry run**: the main procedure, the export of a
graph, and the block of the build. -/
def dryFirstInit : ScSubCode := asmFirstInitCode asmFirstInitBuildCode

/-- The multiplier of the first phase of the init in the dry run. -/
def dryFirstInitMul (capExp limbMul : ℕ) : ℕ :=
  asmFirstInitMul (asmFiBuildCostMul capExp limbMul + asmFiTourPotMul capExp)

/-- The space of the first phase of the init in the dry run. -/
def dryFirstInitSpace (capExp : ℕ) : PolyBound :=
  asmFirstInitSpace (asmFiBuildSpacePoly sparsifyImplUsed.cw dryFiCγ dryFicγ capExp)

/-- **The hypothesis `hFirstInit` of `theorem_1_1_skeleton`**, for `firstInit := dryFirstInit` and
any constants `C` whose `initMul` and `initSpace` are `dryFirstInitMul` and `dryFirstInitSpace`.
The witness is `asmBrCoreInitAt_scProg_build`. The hypothesis `P ≤ 4 * L_in` is not used here,
since `AsmBrCoreInitAt.runs` asks it again for each run, and the root of `CF` is not used. -/
theorem drySC_hFirstInit (cf : ScCompCode) (CFS : AsmCompFamilySpec) (firstStep : ScSubCode)
    (C : ScFirstConsts)
    (hMul : ∀ capExp limbMul, C.initMul capExp limbMul = dryFirstInitMul capExp limbMul)
    (hSpace : ∀ capExp, C.initSpace capExp = dryFirstInitSpace capExp) :
    let L := scLayout sparsifyImplUsed cf firstStep dryFirstInit
    let p := scProg sparsifyImplUsed cf firstStep dryFirstInit
    ∀ depth : ℕ, 1 ≤ depth →
      ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L_in : ℕ)
        (CF : AsmCompFamilyAt CFS (dryLSFInitUsed L_in fmt.precision) w fmt L_in capExp limbMul
          p cf.fInit cf.fBatch),
        fmt.precision ≤ 4 * L_in → CF.fRoot = cf.fRoot →
        ∃ JI : AsmBrCoreInitAt
            (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5 CF.rep
            (dryLSFInitUsed L_in fmt.precision) sparsifyImplUsed depth fmt.precision L_in capExp
            limbMul (asmBrWordExp C.toAsmBrConsts capExp) w walkPot p L.I.fCoreI,
          JI.mul = C.initMul capExp limbMul ∧
          JI.space = C.initSpace capExp := by
  intro L p depth hd capExp limbMul w fmt L_in CF _ _
  refine ⟨asmBrCoreInitAt_scProg_build hd sparsifyImplUsed_one_le_max_p
    (fun k j hj => ⟨dryCLsstUsed, dryLSFInitUsed_isValidLSFInitFor L_in fmt.precision k j hj⟩)
    dryFi_stretch, ?_, ?_⟩
  · rw [hMul]
    rfl
  · rw [hSpace]
    rfl

end MinCostFlow.Final.DryRun
