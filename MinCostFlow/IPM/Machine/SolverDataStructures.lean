module

public import MinCostFlow.IPM.Machine.SolverSearchLink
public import MinCostFlow.IPM.Machine.SolverRoundLink
public import MinCostFlow.IPM.EdgeOnly

/-!
# The two data structures used by the bounded solver

The search uses Definition 4.5 with failure (page 14), and the
rounder uses the forest from Lemma 4.1. The same dispatch addresses
serve all calls in a solver program. The implementations may expose
their resource bounds by the dimensions of the current instance.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- Addresses for the data structures and the size-dependent quality computation. -/
structure SolverDispatch where
  cycleInit : ℕ
  cycleOp : ℕ → ℕ
  forestInit : ℕ
  forestOp : ℕ → ℕ
  quality : ℕ := 0

/-- Read-only computation of the quality exponent on the augmented edge
count. Its return and cost depend only on that count. -/
def solverQualityContract (w : ℕ) (k charge : ℕ → ℕ) : Contract where
  pre args _ := ∃ M, args = [M] ∧ k M < 2^w
  post args mem result final := final = mem ∧ result = k (args.getD 0 0)
  cost args _ := charge (args.getD 0 0)

/-- Numerical parameters to the data structures. An operation-specific
allocation function can be bounded by a uniform per-instance envelope. -/
structure SolverResources where
  qualityExponent : ℕ
  cycleRate : ℕ → ℕ
  cycleAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ
  cycleSpace : ℕ → ℕ → ℕ
  forestRate : ℕ → ℕ
  forestAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ
  forestInitSpace : ℕ → ℕ → ℕ
  forestOpSpace : ℕ → ℕ → ℕ

/-- Both shared machine contracts at the stored precision, with the
allocation bounds used to reserve their workspace. -/
structure SolverDataStructuresAt (w : ℕ) (p : Program) (entry : SolverDispatch)
    (resources : SolverResources) (I : Instance) (V : ℕ)
    (hw : ipmParameterWordBits I.m V≤w)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (RC : DSRep C.State)
    (RD : DSRep D.State) : Prop where
  cycleModel : MinRatioSpecWithFailureUpTo C (1/(2:ℝ)^resources.qualityExponent)
    (Num.IPM.alphaPrime I.m V/8) (precisionHiddenPsi I.m V)
    ((1/(2:ℝ)^resources.qualityExponent)*Num.IPM.alphaPrime I.m V/1024) I.m I.n
  cycleMachine : RC.Implements w p entry.cycleInit entry.cycleOp
    (minRatioMachineContract (ipmMinRatioFormat I.m V hw) C (namedInstance I)
      I.m (1/(2:ℝ)^resources.qualityExponent) (Num.IPM.alphaPrime I.m V/8)
      resources.cycleRate (resources.cycleAllocation I.n I.m))
  cycleBound : ∀ j<4, ∀ args, resources.cycleAllocation I.n I.m j args≤resources.cycleSpace I.n I.m
  forestMachine : RD.Implements w p entry.forestInit entry.forestOp
    (forestMachineContract D w 4 (ipmLimbs I.m V) (ipmPrecision I.m V)
      resources.forestRate (resources.forestAllocation I.n I.m))
  forestInitBound : ∀ b,resources.forestAllocation I.n I.m 6 [I.n,ipmLimbs I.m V,ipmPrecision I.m V,b]≤resources.forestInitSpace I.n I.m
  forestOpBound : ∀ j<6, ∀ args, resources.forestAllocation I.n I.m j args≤resources.forestOpSpace I.n I.m

/-- The preparation, bisection and recovery charges before bounding
augmented dimensions by the original dimensions. -/
def solverSearchCharge {w : ℕ} (resources : SolverResources) (I : Instance) (V : ℕ)
    (hw : ipmParameterWordBits I.m V≤w) : ℕ :=
  targetSearchCost (ipmMinRatioFormat I.m V hw) I.m V resources.qualityExponent
    (ipmRangeExponent I.m V) resources.cycleRate

/-- The bisection reservation counts every complete test. -/
def solverSearchReserve {w : ℕ} (resources : SolverResources) (I : Instance) (V : ℕ)
    (hw : ipmParameterWordBits I.m V≤w) : ℕ :=
  targetSearchSpace (ipmMinRatioFormat I.m V hw) I.m V resources.qualityExponent
    (ipmRangeExponent I.m V) (resources.cycleSpace I.n I.m)

/-- Total cost of copying and rounding the accepted table and writing
the original edge prefix. -/
def solverRecoveryCharge (resources : SolverResources) (I : Instance) (V m : ℕ) : ℕ :=
  let L := ipmLimbs I.m V
  roundMachineCost (resources.forestRate I.n) L I.n I.m+17*(I.m*L)+m*(100*L+240)+100

/-- Fresh workspace for copying, rounding and recovery. -/
def solverRecoveryReserve (resources : SolverResources) (I : Instance) (V m : ℕ) : ℕ :=
  let L := ipmLimbs I.m V
  I.m*L+roundMachineSpace (resources.forestInitSpace I.n I.m) (resources.forestOpSpace I.n I.m)
    L I.m+recoverScanSpace L m

/-- Both shared machine contracts at the stored precision, with the
allocation bounds used to reserve their workspace. -/
structure SolverQualityDataStructuresAt (w : ℕ) (p : Program) (entry : SolverDispatch)
    (resources : SolverResources) (I : Instance) (V : ℕ)
    (hw : ipmQualityParameterWordBits I.m V resources.qualityExponent≤w)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (RC : DSRep C.State)
    (RD : DSRep D.State) : Prop where
  cycleModel : MinRatioSpecWithFailureUpTo C (1/(2:ℝ)^resources.qualityExponent)
    (Num.IPM.alphaPrime I.m V/8) ((ipmQualityRangeExponent I.m V resources.qualityExponent+slackRangeExponent I.m V+6 : ℕ) : ℝ)
    ((1/(2:ℝ)^resources.qualityExponent)*Num.IPM.alphaPrime I.m V/1024) I.m I.n
  cycleMachine : RC.Implements w p entry.cycleInit entry.cycleOp
    (minRatioMachineContract (ipmQualityMinRatioFormat I.m V resources.qualityExponent hw) C (namedInstance I)
      I.m (1/(2:ℝ)^resources.qualityExponent) (Num.IPM.alphaPrime I.m V/8)
      resources.cycleRate (resources.cycleAllocation I.n I.m))
  cycleBound : ∀ j<4, ∀ args, resources.cycleAllocation I.n I.m j args≤resources.cycleSpace I.n I.m
  forestMachine : RD.Implements w p entry.forestInit entry.forestOp
    (forestMachineContract D w 4 (ipmQualityLimbs I.m V resources.qualityExponent) (ipmQualityPrecision I.m V resources.qualityExponent)
      resources.forestRate (resources.forestAllocation I.n I.m))
  forestInitBound : ∀ b,resources.forestAllocation I.n I.m 6 [I.n,ipmQualityLimbs I.m V resources.qualityExponent,ipmQualityPrecision I.m V resources.qualityExponent,b]≤resources.forestInitSpace I.n I.m
  forestOpBound : ∀ j<6, ∀ args, resources.forestAllocation I.n I.m j args≤resources.forestOpSpace I.n I.m

/-- Connected edge-only variant of `SolverQualityDataStructuresAt`, requiring `C` to hold on
connected edge-only histories of bounded size. -/
structure SolverQualityConnectedDataStructuresAt (w : ℕ) (p : Program) (entry : SolverDispatch)
    (resources : SolverResources) (I : Instance) (V : ℕ)
    (hw : ipmQualityParameterWordBits I.m V resources.qualityExponent≤w)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (RC : DSRep C.State)
    (RD : DSRep D.State) : Prop where
  cycleModel : MinRatioSpecWithFailureEdgeOnlyConnectedUpTo C (1/(2:ℝ)^resources.qualityExponent)
    (Num.IPM.alphaPrime I.m V/8) ((ipmQualityRangeExponent I.m V resources.qualityExponent+slackRangeExponent I.m V+6 : ℕ) : ℝ)
    ((1/(2:ℝ)^resources.qualityExponent)*Num.IPM.alphaPrime I.m V/1024) I.m I.n
  cycleMachine : RC.Implements w p entry.cycleInit entry.cycleOp
    (minRatioMachineContract (ipmQualityMinRatioFormat I.m V resources.qualityExponent hw) C (namedInstance I)
      I.m (1/(2:ℝ)^resources.qualityExponent) (Num.IPM.alphaPrime I.m V/8)
      resources.cycleRate (resources.cycleAllocation I.n I.m))
  cycleBound : ∀ j<4, ∀ args, resources.cycleAllocation I.n I.m j args≤resources.cycleSpace I.n I.m
  forestMachine : RD.Implements w p entry.forestInit entry.forestOp
    (forestMachineContract D w 4 (ipmQualityLimbs I.m V resources.qualityExponent) (ipmQualityPrecision I.m V resources.qualityExponent)
      resources.forestRate (resources.forestAllocation I.n I.m))
  forestInitBound : ∀ b,resources.forestAllocation I.n I.m 6 [I.n,ipmQualityLimbs I.m V resources.qualityExponent,ipmQualityPrecision I.m V resources.qualityExponent,b]≤resources.forestInitSpace I.n I.m
  forestOpBound : ∀ j<6, ∀ args, resources.forestAllocation I.n I.m j args≤resources.forestOpSpace I.n I.m

/-- Any unrestricted `SolverQualityDataStructuresAt` satisfies the connected edge-only variant. -/
theorem SolverQualityDataStructuresAt.toConnected {w : ℕ} {p : Program} {entry : SolverDispatch}
    {resources : SolverResources} {I : Instance} {V : ℕ}
    {hw : ipmQualityParameterWordBits I.m V resources.qualityExponent≤w}
    {C : MinRatioDataStructureWithFailure} {D : DynForest} {RC : DSRep C.State}
    {RD : DSRep D.State}
    (h : SolverQualityDataStructuresAt w p entry resources I V hw C D RC RD) :
    SolverQualityConnectedDataStructuresAt w p entry resources I V hw C D RC RD where
  cycleModel := h.cycleModel.toEdgeOnlyConnected
  cycleMachine := h.cycleMachine
  cycleBound := h.cycleBound
  forestMachine := h.forestMachine
  forestInitBound := h.forestInitBound
  forestOpBound := h.forestOpBound

/-- The preparation, bisection and recovery charges before bounding
augmented dimensions by the original dimensions. -/
def solverQualitySearchCharge {w : ℕ} (resources : SolverResources) (I : Instance) (V : ℕ)
    (hw : ipmQualityParameterWordBits I.m V resources.qualityExponent≤w) : ℕ :=
  targetSearchCost (ipmQualityMinRatioFormat I.m V resources.qualityExponent hw) I.m V resources.qualityExponent
    (ipmQualityRangeExponent I.m V resources.qualityExponent) resources.cycleRate

/-- The bisection reservation counts every complete test. -/
def solverQualitySearchReserve {w : ℕ} (resources : SolverResources) (I : Instance) (V : ℕ)
    (hw : ipmQualityParameterWordBits I.m V resources.qualityExponent≤w) : ℕ :=
  targetSearchSpace (ipmQualityMinRatioFormat I.m V resources.qualityExponent hw) I.m V resources.qualityExponent
    (ipmQualityRangeExponent I.m V resources.qualityExponent) (resources.cycleSpace I.n I.m)

/-- Total cost of copying and rounding the accepted table and writing
the original edge prefix. -/
def solverQualityRecoveryCharge (resources : SolverResources) (I : Instance) (V m : ℕ) : ℕ :=
  let L := ipmQualityLimbs I.m V resources.qualityExponent
  roundMachineCost (resources.forestRate I.n) L I.n I.m+17*(I.m*L)+m*(100*L+240)+100

/-- Fresh workspace for copying, rounding and recovery. -/
def solverQualityRecoveryReserve (resources : SolverResources) (I : Instance) (V m : ℕ) : ℕ :=
  let L := ipmQualityLimbs I.m V resources.qualityExponent
  I.m*L+roundMachineSpace (resources.forestInitSpace I.n I.m) (resources.forestOpSpace I.n I.m)
    L I.m+recoverScanSpace L m

/-- Generalized solver resources where the forest rate and operation space also
depend on the limb count `L` and the forest allocation also depends on `w` and `L`.
Leaves `forestMachineContract` unchanged (`initPre` unchanged so existing link-cut
forest proofs apply without changing `MinCostFlow/LinkCut/`). -/
structure SolverForestResources where
  qualityExponent : ℕ
  cycleRate : ℕ → ℕ
  cycleAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ
  cycleSpace : ℕ → ℕ → ℕ
  forestRate : ℕ → ℕ → ℕ
  forestAllocation : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → ℕ
  forestInitSpace : ℕ → ℕ → ℕ
  forestOpSpace : ℕ → ℕ → ℕ → ℕ

/-- Embed `SolverResources` (ignoring `w` and `L` in forest bounds) into
`SolverForestResources`. -/
def SolverResources.toForestResources (r : SolverResources) : SolverForestResources where
  qualityExponent := r.qualityExponent
  cycleRate := r.cycleRate
  cycleAllocation := r.cycleAllocation
  cycleSpace := r.cycleSpace
  forestRate n _ := r.forestRate n
  forestAllocation _ _ n m := r.forestAllocation n m
  forestInitSpace := r.forestInitSpace
  forestOpSpace _ n m := r.forestOpSpace n m

/-- Connected-graph data structures parameterized by `SolverForestResources`, allowing the
forest rate and space to depend on the instance limb count `L` and the forest allocation to
depend on both `w` and `L`. -/
structure SolverQualityForestDataStructuresAt (w : ℕ) (p : Program) (entry : SolverDispatch)
    (resources : SolverForestResources) (I : Instance) (V : ℕ)
    (hw : ipmQualityParameterWordBits I.m V resources.qualityExponent ≤ w)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (RC : DSRep C.State)
    (RD : DSRep D.State) : Prop where
  cycleModel : MinRatioSpecWithFailureEdgeOnlyConnectedUpTo C (1 / (2 : ℝ) ^ resources.qualityExponent)
    (Num.IPM.alphaPrime I.m V / 8)
    ((ipmQualityRangeExponent I.m V resources.qualityExponent + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    ((1 / (2 : ℝ) ^ resources.qualityExponent) * Num.IPM.alphaPrime I.m V / 1024) I.m I.n
  cycleMachine : RC.Implements w p entry.cycleInit entry.cycleOp
    (minRatioMachineContract (ipmQualityMinRatioFormat I.m V resources.qualityExponent hw) C (namedInstance I)
      I.m (1 / (2 : ℝ) ^ resources.qualityExponent) (Num.IPM.alphaPrime I.m V / 8)
      resources.cycleRate (resources.cycleAllocation I.n I.m))
  cycleBound : ∀ j < 4, ∀ args, resources.cycleAllocation I.n I.m j args ≤ resources.cycleSpace I.n I.m
  forestMachine :
    let L := ipmQualityLimbs I.m V resources.qualityExponent
    let P := ipmQualityPrecision I.m V resources.qualityExponent
    RD.Implements w p entry.forestInit entry.forestOp
      (forestMachineContract D w 4 L P (fun n => resources.forestRate n L) (resources.forestAllocation w L I.n I.m))
  forestInitBound :
    let L := ipmQualityLimbs I.m V resources.qualityExponent
    let P := ipmQualityPrecision I.m V resources.qualityExponent
    ∀ b, resources.forestAllocation w L I.n I.m 6 [I.n, L, P, b] ≤ resources.forestInitSpace I.n I.m
  forestOpBound :
    let L := ipmQualityLimbs I.m V resources.qualityExponent
    ∀ j < 6, ∀ args, resources.forestAllocation w L I.n I.m j args ≤ resources.forestOpSpace L I.n I.m

/-- Any `SolverQualityConnectedDataStructuresAt` satisfies the `L`- and `w`-aware variant. -/
theorem SolverQualityConnectedDataStructuresAt.toForest {w : ℕ} {p : Program} {entry : SolverDispatch}
    {resources : SolverResources} {I : Instance} {V : ℕ}
    {hw : ipmQualityParameterWordBits I.m V resources.qualityExponent ≤ w}
    {C : MinRatioDataStructureWithFailure} {D : DynForest} {RC : DSRep C.State}
    {RD : DSRep D.State}
    (h : SolverQualityConnectedDataStructuresAt w p entry resources I V hw C D RC RD) :
    SolverQualityForestDataStructuresAt w p entry resources.toForestResources I V hw C D RC RD where
  cycleModel := h.cycleModel
  cycleMachine := h.cycleMachine
  cycleBound := h.cycleBound
  forestMachine := h.forestMachine
  forestInitBound := h.forestInitBound
  forestOpBound := h.forestOpBound

/-- Search charge for `SolverForestResources`. -/
def solverQualityForestSearchCharge {w : ℕ} (resources : SolverForestResources) (I : Instance) (V : ℕ)
    (hw : ipmQualityParameterWordBits I.m V resources.qualityExponent ≤ w) : ℕ :=
  targetSearchCost (ipmQualityMinRatioFormat I.m V resources.qualityExponent hw) I.m V resources.qualityExponent
    (ipmQualityRangeExponent I.m V resources.qualityExponent) resources.cycleRate

/-- Bisection space reservation for `SolverForestResources`. -/
def solverQualityForestSearchReserve {w : ℕ} (resources : SolverForestResources) (I : Instance) (V : ℕ)
    (hw : ipmQualityParameterWordBits I.m V resources.qualityExponent ≤ w) : ℕ :=
  targetSearchSpace (ipmQualityMinRatioFormat I.m V resources.qualityExponent hw) I.m V resources.qualityExponent
    (ipmQualityRangeExponent I.m V resources.qualityExponent) (resources.cycleSpace I.n I.m)

/-- Total cost of copying, rounding (with `L`-dependent forest rate), and recovery. -/
def solverQualityForestRecoveryCharge (resources : SolverForestResources) (I : Instance) (V m : ℕ) : ℕ :=
  let L := ipmQualityLimbs I.m V resources.qualityExponent
  roundMachineCost (resources.forestRate I.n L) L I.n I.m + 17 * (I.m * L) + m * (100 * L + 240) + 100

/-- Fresh workspace for copying, rounding (with `L`-dependent op space), and recovery. -/
def solverQualityForestRecoveryReserve (resources : SolverForestResources) (I : Instance) (V m : ℕ) : ℕ :=
  let L := ipmQualityLimbs I.m V resources.qualityExponent
  I.m * L + roundMachineSpace (resources.forestInitSpace I.n I.m) (resources.forestOpSpace L I.n I.m)
    L I.m + recoverScanSpace L m

/-- `V`-passing variant of `SolverDataStructuresAt`: expects `V` in `init` arg 5. -/
structure SolverDataStructuresWithVAt (w : ℕ) (p : Program) (entry : SolverDispatch)
    (resources : SolverResources) (I : Instance) (V : ℕ)
    (hw : ipmParameterWordBits I.m V≤w)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (RC : DSRep C.State)
    (RD : DSRep D.State) : Prop where
  cycleModel : MinRatioSpecWithFailureUpTo C (1/(2:ℝ)^resources.qualityExponent)
    (Num.IPM.alphaPrime I.m V/8) (precisionHiddenPsi I.m V)
    ((1/(2:ℝ)^resources.qualityExponent)*Num.IPM.alphaPrime I.m V/1024) I.m I.n
  cycleMachine : RC.Implements w p entry.cycleInit entry.cycleOp
    (minRatioMachineContractWithV (ipmMinRatioFormat I.m V hw) C (namedInstance I)
      I.m V (1/(2:ℝ)^resources.qualityExponent) (Num.IPM.alphaPrime I.m V/8)
      resources.cycleRate (resources.cycleAllocation I.n I.m))
  cycleBound : ∀ j<4, ∀ args, resources.cycleAllocation I.n I.m j args≤resources.cycleSpace I.n I.m
  forestMachine : RD.Implements w p entry.forestInit entry.forestOp
    (forestMachineContract D w 4 (ipmLimbs I.m V) (ipmPrecision I.m V)
      resources.forestRate (resources.forestAllocation I.n I.m))
  forestInitBound : ∀ b,resources.forestAllocation I.n I.m 6 [I.n,ipmLimbs I.m V,ipmPrecision I.m V,b]≤resources.forestInitSpace I.n I.m
  forestOpBound : ∀ j<6, ∀ args, resources.forestAllocation I.n I.m j args≤resources.forestOpSpace I.n I.m

/-- `V`-passing variant of `SolverQualityDataStructuresAt`: expects `V` in `init` arg 5. -/
structure SolverQualityDataStructuresWithVAt (w : ℕ) (p : Program) (entry : SolverDispatch)
    (resources : SolverResources) (I : Instance) (V : ℕ)
    (hw : ipmQualityParameterWordBits I.m V resources.qualityExponent≤w)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (RC : DSRep C.State)
    (RD : DSRep D.State) : Prop where
  cycleModel : MinRatioSpecWithFailureUpTo C (1/(2:ℝ)^resources.qualityExponent)
    (Num.IPM.alphaPrime I.m V/8) ((ipmQualityRangeExponent I.m V resources.qualityExponent+slackRangeExponent I.m V+6 : ℕ) : ℝ)
    ((1/(2:ℝ)^resources.qualityExponent)*Num.IPM.alphaPrime I.m V/1024) I.m I.n
  cycleMachine : RC.Implements w p entry.cycleInit entry.cycleOp
    (minRatioMachineContractWithV (ipmQualityMinRatioFormat I.m V resources.qualityExponent hw) C (namedInstance I)
      I.m V (1/(2:ℝ)^resources.qualityExponent) (Num.IPM.alphaPrime I.m V/8)
      resources.cycleRate (resources.cycleAllocation I.n I.m))
  cycleBound : ∀ j<4, ∀ args, resources.cycleAllocation I.n I.m j args≤resources.cycleSpace I.n I.m
  forestMachine : RD.Implements w p entry.forestInit entry.forestOp
    (forestMachineContract D w 4 (ipmQualityLimbs I.m V resources.qualityExponent) (ipmQualityPrecision I.m V resources.qualityExponent)
      resources.forestRate (resources.forestAllocation I.n I.m))
  forestInitBound : ∀ b,resources.forestAllocation I.n I.m 6 [I.n,ipmQualityLimbs I.m V resources.qualityExponent,ipmQualityPrecision I.m V resources.qualityExponent,b]≤resources.forestInitSpace I.n I.m
  forestOpBound : ∀ j<6, ∀ args, resources.forestAllocation I.n I.m j args≤resources.forestOpSpace I.n I.m

/-- `V`-passing connected edge-only variant of `SolverQualityDataStructuresAt`. -/
structure SolverQualityConnectedDataStructuresWithVAt (w : ℕ) (p : Program) (entry : SolverDispatch)
    (resources : SolverResources) (I : Instance) (V : ℕ)
    (hw : ipmQualityParameterWordBits I.m V resources.qualityExponent≤w)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (RC : DSRep C.State)
    (RD : DSRep D.State) : Prop where
  cycleModel : MinRatioSpecWithFailureEdgeOnlyConnectedUpTo C (1/(2:ℝ)^resources.qualityExponent)
    (Num.IPM.alphaPrime I.m V/8) ((ipmQualityRangeExponent I.m V resources.qualityExponent+slackRangeExponent I.m V+6 : ℕ) : ℝ)
    ((1/(2:ℝ)^resources.qualityExponent)*Num.IPM.alphaPrime I.m V/1024) I.m I.n
  cycleMachine : RC.Implements w p entry.cycleInit entry.cycleOp
    (minRatioMachineContractWithV (ipmQualityMinRatioFormat I.m V resources.qualityExponent hw) C (namedInstance I)
      I.m V (1/(2:ℝ)^resources.qualityExponent) (Num.IPM.alphaPrime I.m V/8)
      resources.cycleRate (resources.cycleAllocation I.n I.m))
  cycleBound : ∀ j<4, ∀ args, resources.cycleAllocation I.n I.m j args≤resources.cycleSpace I.n I.m
  forestMachine : RD.Implements w p entry.forestInit entry.forestOp
    (forestMachineContract D w 4 (ipmQualityLimbs I.m V resources.qualityExponent) (ipmQualityPrecision I.m V resources.qualityExponent)
      resources.forestRate (resources.forestAllocation I.n I.m))
  forestInitBound : ∀ b,resources.forestAllocation I.n I.m 6 [I.n,ipmQualityLimbs I.m V resources.qualityExponent,ipmQualityPrecision I.m V resources.qualityExponent,b]≤resources.forestInitSpace I.n I.m
  forestOpBound : ∀ j<6, ∀ args, resources.forestAllocation I.n I.m j args≤resources.forestOpSpace I.n I.m

/-- Any unrestricted `SolverQualityDataStructuresWithVAt` satisfies the connected edge-only variant. -/
theorem SolverQualityDataStructuresWithVAt.toConnected {w : ℕ} {p : Program} {entry : SolverDispatch}
    {resources : SolverResources} {I : Instance} {V : ℕ}
    {hw : ipmQualityParameterWordBits I.m V resources.qualityExponent≤w}
    {C : MinRatioDataStructureWithFailure} {D : DynForest} {RC : DSRep C.State}
    {RD : DSRep D.State}
    (h : SolverQualityDataStructuresWithVAt w p entry resources I V hw C D RC RD) :
    SolverQualityConnectedDataStructuresWithVAt w p entry resources I V hw C D RC RD where
  cycleModel := h.cycleModel.toEdgeOnlyConnected
  cycleMachine := h.cycleMachine
  cycleBound := h.cycleBound
  forestMachine := h.forestMachine
  forestInitBound := h.forestInitBound
  forestOpBound := h.forestOpBound

/-- `V`-passing variant of `SolverQualityForestDataStructuresAt`. -/
structure SolverQualityForestDataStructuresWithVAt (w : ℕ) (p : Program) (entry : SolverDispatch)
    (resources : SolverForestResources) (I : Instance) (V : ℕ)
    (hw : ipmQualityParameterWordBits I.m V resources.qualityExponent ≤ w)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (RC : DSRep C.State)
    (RD : DSRep D.State) : Prop where
  cycleModel : MinRatioSpecWithFailureEdgeOnlyConnectedUpTo C (1 / (2 : ℝ) ^ resources.qualityExponent)
    (Num.IPM.alphaPrime I.m V / 8)
    ((ipmQualityRangeExponent I.m V resources.qualityExponent + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    ((1 / (2 : ℝ) ^ resources.qualityExponent) * Num.IPM.alphaPrime I.m V / 1024) I.m I.n
  cycleMachine : RC.Implements w p entry.cycleInit entry.cycleOp
    (minRatioMachineContractWithV (ipmQualityMinRatioFormat I.m V resources.qualityExponent hw) C (namedInstance I)
      I.m V (1 / (2 : ℝ) ^ resources.qualityExponent) (Num.IPM.alphaPrime I.m V / 8)
      resources.cycleRate (resources.cycleAllocation I.n I.m))
  cycleBound : ∀ j < 4, ∀ args, resources.cycleAllocation I.n I.m j args ≤ resources.cycleSpace I.n I.m
  forestMachine :
    let L := ipmQualityLimbs I.m V resources.qualityExponent
    let P := ipmQualityPrecision I.m V resources.qualityExponent
    RD.Implements w p entry.forestInit entry.forestOp
      (forestMachineContract D w 4 L P (fun n => resources.forestRate n L) (resources.forestAllocation w L I.n I.m))
  forestInitBound :
    let L := ipmQualityLimbs I.m V resources.qualityExponent
    let P := ipmQualityPrecision I.m V resources.qualityExponent
    ∀ b, resources.forestAllocation w L I.n I.m 6 [I.n, L, P, b] ≤ resources.forestInitSpace I.n I.m
  forestOpBound :
    let L := ipmQualityLimbs I.m V resources.qualityExponent
    ∀ j < 6, ∀ args, resources.forestAllocation w L I.n I.m j args ≤ resources.forestOpSpace L I.n I.m

/-- Any `SolverQualityConnectedDataStructuresWithVAt` satisfies the `L`- and `w`-aware variant. -/
theorem SolverQualityConnectedDataStructuresWithVAt.toForest {w : ℕ} {p : Program} {entry : SolverDispatch}
    {resources : SolverResources} {I : Instance} {V : ℕ}
    {hw : ipmQualityParameterWordBits I.m V resources.qualityExponent ≤ w}
    {C : MinRatioDataStructureWithFailure} {D : DynForest} {RC : DSRep C.State}
    {RD : DSRep D.State}
    (h : SolverQualityConnectedDataStructuresWithVAt w p entry resources I V hw C D RC RD) :
    SolverQualityForestDataStructuresWithVAt w p entry resources.toForestResources I V hw C D RC RD where
  cycleModel := h.cycleModel
  cycleMachine := h.cycleMachine
  cycleBound := h.cycleBound
  forestMachine := h.forestMachine
  forestInitBound := h.forestInitBound
  forestOpBound := h.forestOpBound

end MinCostFlow.IPM.Machine
