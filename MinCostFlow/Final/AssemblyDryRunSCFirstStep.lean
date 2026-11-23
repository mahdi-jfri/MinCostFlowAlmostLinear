module

public import MinCostFlow.Final.AssemblyDryRunSCFirstInit
public import MinCostFlow.Final.AssemblyDryRunSCCompImpl
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPackTop

/-!
# The first phase of the step of a branch in the dry run (`AssemblyDryRunSCFirstStep`)

`theorem_1_1_of_parts` (`Final/Theorem11Parts.lean`) asks, for the first phase of the step of a
branch, a code block `firstStep`, constants `C : ScFirstConsts` with `C.firstWordExp 3 ≤ 39`, the
constants of the init (`C.initMul = dryFirstInitMul`, `C.initSpace = dryFirstInitSpace`), and
`hFirstStep`: on `scProg` at `firstInit := dryFirstInit`, the procedure `fCoreS` of the layout
meets `AsmBrCoreStepAt` with the multipliers and the space of `C`.

This file gives them from one premise: the cost goal of the step (`DryFirstStepCost`), at the
multiplier `stepMul` that it proves. The goal is proved in `Final/AssemblyDryRunSCFirstStepCost.lean`
(`dryFirstStep_cost`).
* `firstStep := asmFsStepCode`, the code of `AssemblyFirstStepPack.lean`.
* `C := dryFirstConsts stepMul`: the multiplier `stepMul`, the multiplier `4 capExp + 5` of the
  walks, the space `asmFirstStepSpacePolyStd 0 cw capExp dryFsCsp`, the constants of the init, and
  the word exponent `0` (the step needs only `3 capExp ≤ wordExp`, which P10's exponent gives).
  The constant `dryFsCsp` bounds the stretch of the sparsifier (`sparsifyImplUsed_gamma_bound`).
* `dryFirstStep_hFirstStep`: `hFirstStep`, from the pieces `asmFirstStep_pieces_scProg` and
  `asmFirstStep_scProg_of`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM MinCostFlow.SparseCore MinCostFlow.SparseCore.Program MinCostFlow.DynSpanner.Program

/-- The constant of the stretch of the sparsifier of the dry run:
`γ_ℓ m ≤ exp(dryFsCsp · log(m + 2) ^ (7/8))` (`sparsifyImplUsed_gamma_bound`). -/
def dryFsCsp : ℝ := Classical.choose sparsifyImplUsed_gamma_bound

theorem dryFsCsp_pos : 0 < dryFsCsp := (Classical.choose_spec sparsifyImplUsed_gamma_bound).1

theorem dryFsCsp_gamma (m : ℕ) :
    sparsifyImplUsed.γ_ℓ m ≤ Real.exp (dryFsCsp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
  ((Classical.choose_spec sparsifyImplUsed_gamma_bound).2 m).1

/-- The constants of the first phases of the dry run, for the multiplier `stepMul` of the cost of
the step. -/
def dryFirstConsts (stepMul : ℕ → ℕ → ℕ) : ScFirstConsts where
  stepMul := stepMul
  stepYs := fun capExp _ => 4 * capExp + 5
  stepSpace := fun capExp => asmFirstStepSpacePolyStd 0 sparsifyImplUsed.cw capExp dryFsCsp
  initMul := dryFirstInitMul
  initSpace := dryFirstInitSpace
  firstWordExp := fun _ => 0

/-- `hC` of `theorem_1_1_of_parts`. -/
theorem dryFirstConsts_hC (stepMul : ℕ → ℕ → ℕ) : (dryFirstConsts stepMul).firstWordExp 3 ≤ 39 :=
  Nat.zero_le _

/-- `hInitMul` of `theorem_1_1_of_parts`. -/
theorem dryFirstConsts_initMul (stepMul : ℕ → ℕ → ℕ) :
    ∀ capExp limbMul, (dryFirstConsts stepMul).initMul capExp limbMul =
      dryFirstInitMul capExp limbMul :=
  fun _ _ => rfl

/-- `hInitSpace` of `theorem_1_1_of_parts`. -/
theorem dryFirstConsts_initSpace (stepMul : ℕ → ℕ → ℕ) :
    ∀ capExp, (dryFirstConsts stepMul).initSpace capExp = dryFirstInitSpace capExp :=
  fun _ => rfl

/-- The word exponent of a branch is at least `3 capExp`, since P10's exponent is
`4 capExp + 2 + log(…)`. -/
theorem dryFirstConsts_wordExp_ge (stepMul : ℕ → ℕ → ℕ) (capExp : ℕ) :
    3 * capExp ≤ asmBrWordExp (dryFirstConsts stepMul).toAsmBrConsts capExp :=
  le_max_of_le_left (by unfold asmP10WordExp; omega)

/-- **The cost goal of the first step in the dry run**: `AsmFsCostGoal` on
`scProg` at `firstStep := asmFsStepCode`, `firstInit := dryFirstInit`, the multiplier
`stepMul capExp limbMul`, the potential `walkPot` and the space
`asmFirstStepSpaceFnStd 0 cw capExp dryFsCsp`, for every depth `1 ≤ depth` and `P ≤ 4 L_in`. -/
def DryFirstStepCost (stepMul : ℕ → ℕ → ℕ) : Prop :=
  ∀ depth : ℕ, 1 ≤ depth → ∀ (capExp limbMul w P L_in : ℕ), P ≤ 4 * L_in →
    AsmFsCostGoal tourBundleSpec sparsifyImplUsed P L_in capExp limbMul
      (asmBrWordExp (dryFirstConsts stepMul).toAsmBrConsts capExp) w (walkPot (L := depth))
      ((scLayout sparsifyImplUsed dryCompCode asmFsStepCode dryFirstInit).envStep.bSelf + 7)
      ((scLayout sparsifyImplUsed dryCompCode asmFsStepCode dryFirstInit).envStep.bSelf + 4)
      ((scLayout sparsifyImplUsed dryCompCode asmFsStepCode dryFirstInit).envStep.bSelf + 5)
      (scProg sparsifyImplUsed dryCompCode asmFsStepCode dryFirstInit)
      (asmFsRootSc sparsifyImplUsed dryCompCode dryFirstInit w)
      (scLayout sparsifyImplUsed dryCompCode asmFsStepCode dryFirstInit).bBun
      ((scLayout sparsifyImplUsed dryCompCode asmFsStepCode dryFirstInit).envStep.bSelf + 48)
      ((scLayout sparsifyImplUsed dryCompCode asmFsStepCode dryFirstInit).envStep.bSelf + 9)
      ((scLayout sparsifyImplUsed dryCompCode asmFsStepCode dryFirstInit).envStep.bSelf + 10)
      (asmFsKSc sparsifyImplUsed dryCompCode dryFirstInit w) (stepMul capExp limbMul)
      (asmFirstStepSpaceFnStd 0 sparsifyImplUsed.cw capExp dryFsCsp)

/-- **`hFirstStep` of `theorem_1_1_of_parts`** at `firstStep := asmFsStepCode` and
`C := dryFirstConsts stepMul`, from the cost goal `hCost`. -/
theorem dryFirstStep_hFirstStep (stepMul : ℕ → ℕ → ℕ) (hCost : DryFirstStepCost stepMul) :
    let L := scLayout sparsifyImplUsed dryCompCode asmFsStepCode dryFirstInit
    let p := scProg sparsifyImplUsed dryCompCode asmFsStepCode dryFirstInit
    ∀ depth : ℕ, 1 ≤ depth →
      ∀ (capExp limbMul w : ℕ) (fmt : Num.Format w) (L_in : ℕ)
        (CF : AsmCompFamilyAt dryCFS (dryLSFInitUsed L_in fmt.precision) w fmt L_in capExp
          limbMul p dryCompCode.fInit dryCompCode.fBatch),
        fmt.precision ≤ 4 * L_in → CF.fRoot = dryCompCode.fRoot →
        ∃ JS : AsmBrCoreStepAt
            (asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)) scProgB5
            sparsifyImplUsed depth fmt.precision L_in capExp limbMul
            (asmBrWordExp (dryFirstConsts stepMul).toAsmBrConsts capExp) w walkPot p L.I.fCoreS,
          JS.mul = (dryFirstConsts stepMul).stepMul capExp limbMul ∧
          JS.ysMul = (dryFirstConsts stepMul).stepYs capExp limbMul ∧
          JS.spaceP = (dryFirstConsts stepMul).stepSpace capExp :=
  asmFirstStep_scProg_of (CFS := dryCFS) (lsfInit := dryLSFInitUsed) (C := dryFirstConsts stepMul)
    fun depth hd capExp limbMul w fmt L_in _ hP =>
      asmFirstStep_pieces_scProg sparsifyImplUsed dryCompCode dryFirstInit (c₀ := 0)
        (dryFirstConsts_wordExp_ge stepMul capExp) sparsifyImplUsed_one_le_max_p le_rfl
        dryFsCsp_pos dryFsCsp_gamma (hCost depth hd capExp limbMul w fmt.precision L_in hP)

end MinCostFlow.Final.DryRun
