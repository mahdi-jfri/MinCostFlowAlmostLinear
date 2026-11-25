module

public import MinCostFlow.Final.CappedConnectedProgram
public import MinCostFlow.Final.OrderedConcreteChainModel
public import MinCostFlow.Final.ConnectedIPMWorkspace
import Mathlib.Tactic

/-!
# Concrete data structure program package for Theorem 1.1

Bundles:
1. no cited-result hypotheses (every cited result or the case of it used by the paper is proved
   in this repository);
2. no ordered restart obligations: `Chain.Ordered.concrete_theorem_5_1` proves the restricted
   tool spec and the MWU bound for `sparseCoreBundleRestartToolMachWith lsfInit` itself, and
   `ToolEmbedsSurvivingOrdRestart` and `ToolNoReinsertOrdRestart` are discharged by
   `Chain.Ordered.concreteRestartEmbeds` and `Chain.Ordered.concreteRestartNoReinsert`;
3. the machine programs for the min-ratio data structure (`cycle`) and dynamic forest (`forest`)
   implementing `Chain.Ordered.algorithm2_dsWithFailureOwn` and `forestModel` together with their
   polynomial space and subpolynomial/polylogarithmic rate bounds.

From these parameters alone, `OrderedConcreteChainModel` and `CappedConnectedProgram` supply the
connected solver contract and outer scaling execution.
-/

@[expose] public noncomputable section
namespace MinCostFlow.Final
open Chain IPM IPM.Machine WordRAM Scaling Scaling.Machine

/-- Linear upper coefficient for `2 ^ cappedQualityExponent threshold A M`. -/
def concreteQualityLinearCoeff (threshold A : ℕ) : ℕ :=
  Classical.choose (cappedQuality_linear threshold A)

theorem cappedQuality_linear_spec (threshold A M : ℕ) :
    2 ^ cappedQualityExponent threshold A M ≤ concreteQualityLinearCoeff threshold A * (M + 2) :=
  Classical.choose_spec (cappedQuality_linear threshold A) M

/-- Polynomial scratch degree matching `connectedIPMRuntimeWorkspace_polynomial`. -/
def cappedScratchDegree (c d Ck : ℕ) : ℕ :=
  10 * (Nat.clog 2 (c * 8 ^ d) + d + 2 * (Nat.clog 2 Ck + 3) + 240)

/-- The complete parameter package for `theorem_1_1_of_concrete_programs`: the machine programs
with their polynomial space and rate bounds. The degree-free ordered bundle chain witness is fixed
(`orderedConcreteChainWitness`), and it carries no restart obligations. -/
structure ConcreteDataStructurePrograms where
  /-- Rounding dynamic-forest model (link-cut tree specification). -/
  forestModel : Rounding.DynForest
  forestSpec : forestModel.IsSpec
  dispatch : SolverDispatch
  /-- Machine procedures for the min-ratio data structure. -/
  cycle : List Stmt
  /-- Machine procedures for the dynamic-forest rounder. -/
  forest : List Stmt
  cycleDeterministic : ∀ s ∈ cycle, s.NoRand
  forestDeterministic : ∀ s ∈ forest, s.NoRand
  qualityAddress : linkedConnectedQualityBase dispatch cycle forest + 2 = dispatch.quality
  resources : SolverResources
  allocationCoefficient : ℕ
  allocationDegree : ℕ
  cycleSpace_poly : ∀ n m, resources.cycleSpace n m ≤ allocationCoefficient * (n + m + 2) ^ allocationDegree
  forestInitSpace_poly : ∀ n m, resources.forestInitSpace n m ≤ allocationCoefficient * (n + m + 2) ^ allocationDegree
  forestOpSpace_poly : ∀ n m, resources.forestOpSpace n m ≤ allocationCoefficient * (n + m + 2) ^ allocationDegree
  cycleRateExponent : ℝ
  cycleRateExponent_nonneg : 0 ≤ cycleRateExponent
  cycleRateConstant : ℝ
  cycleRateConstant_pos : 0 < cycleRateConstant
  cycleRate_subpoly : ∀ M, (resources.cycleRate M : ℝ) ≤ cycleRateConstant * alg2TimeFactor cycleRateExponent (47 / 48) M
  forestConstant : ℝ
  forestLogDegree : ℕ
  forestRate_polylog : ∀ n, (resources.forestRate n : ℝ) ≤ forestConstant * Real.log ((n : ℝ) + 2) ^ forestLogDegree
  /-- Machine implementations of `Chain.Ordered.algorithm2_dsWithFailureOwn` and `forestModel`
  in the linked solver program at the guest word width. -/
  supported : ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → J.CostsBounded (J.m ^ 10) →
    (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
    let W := orderedConcreteChainWitness
    let threshold := orderedConcreteEdgeThreshold W
    let A := orderedConcreteQualityBudget W
    let Ck := concreteQualityLinearCoeff threshold A
    let deg := cappedScratchDegree allocationCoefficient allocationDegree Ck
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent threshold A I.m
    let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
    let p := linkedCappedSolverProgram threshold A dispatch cycle forest
    let cfg := orderedConcreteCirculationCfg W J
    ∀ hw : ipmQualityParameterWordBits I.m V k ≤ w,
      ∃ (RC : DSRep (Chain.Ordered.algorithm2_dsWithFailureOwn cfg).State) (RD : DSRep forestModel.State),
        RC.Implements w p dispatch.cycleInit dispatch.cycleOp
          (minRatioMachineContract (ipmQualityMinRatioFormat I.m V k hw)
            (Chain.Ordered.algorithm2_dsWithFailureOwn cfg) (namedInstance I) I.m
            (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
            resources.cycleRate (resources.cycleAllocation I.n I.m)) ∧
        (∀ j < 4, ∀ args, resources.cycleAllocation I.n I.m j args ≤ resources.cycleSpace I.n I.m) ∧
        RD.Implements w p dispatch.forestInit dispatch.forestOp
          (forestMachineContract forestModel w 4 (ipmQualityLimbs I.m V k) (ipmQualityPrecision I.m V k)
            resources.forestRate (resources.forestAllocation I.n I.m)) ∧
        (∀ b, resources.forestAllocation I.n I.m 6 [I.n, ipmQualityLimbs I.m V k, ipmQualityPrecision I.m V k, b] ≤
          resources.forestInitSpace I.n I.m) ∧
        (∀ j < 6, ∀ args, resources.forestAllocation I.n I.m j args ≤ resources.forestOpSpace I.n I.m)

/-- The degree-free ordered Theorem 5.1 witness used by `P`. -/
def ConcreteDataStructurePrograms.witness (_P : ConcreteDataStructurePrograms) :
    OrderedConcreteChainWitness :=
  orderedConcreteChainWitness

def ConcreteDataStructurePrograms.qualityBudget (P : ConcreteDataStructurePrograms) : ℕ :=
  orderedConcreteQualityBudget P.witness

def ConcreteDataStructurePrograms.edgeThreshold (P : ConcreteDataStructurePrograms) : ℕ :=
  orderedConcreteEdgeThreshold P.witness

def ConcreteDataStructurePrograms.qualityLinearCoeff (P : ConcreteDataStructurePrograms) : ℕ :=
  concreteQualityLinearCoeff P.edgeThreshold P.qualityBudget

def ConcreteDataStructurePrograms.scratchDegree (P : ConcreteDataStructurePrograms) : ℕ :=
  cappedScratchDegree P.allocationCoefficient P.allocationDegree P.qualityLinearCoeff

def ConcreteDataStructurePrograms.runtimeResources (P : ConcreteDataStructurePrograms) :
    SolverRuntimeResources :=
  ⟨P.resources, cappedQualityExponent P.edgeThreshold P.qualityBudget, cappedQualityCost⟩

def ConcreteDataStructurePrograms.solver (P : ConcreteDataStructurePrograms) : Program :=
  linkedCappedSolverProgram P.edgeThreshold P.qualityBudget P.dispatch P.cycle P.forest

theorem ConcreteDataStructurePrograms.solver_deterministic (P : ConcreteDataStructurePrograms) :
    P.solver.IsDeterministic :=
  linkedCappedSolverProgram_deterministic P.edgeThreshold P.qualityBudget P.dispatch P.cycle P.forest
    P.cycleDeterministic P.forestDeterministic

/-- At the canonical guest word width the linked capped solver implements
the connected compressed-circulation solver contract. -/
theorem ConcreteDataStructurePrograms.solver_meetsContract (P : ConcreteDataStructurePrograms)
    (J : Circulation) :
    let w := wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords
    MeetsContract w P.solver 0 (compressedSolverContract w
      (connectedSolverRuntimeTime P.runtimeResources)
      (connectedSolverRuntimeWorkspace P.runtimeResources)) := by
  dsimp only
  let w := wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords
  have hw : 2 < 2 ^ w := by
    have hc : 1 ≤ scratchWordMultiplier 1 P.scratchDegree := by
      unfold scratchWordMultiplier
      omega
    have hBase : 2 ≤ J.solverWords.length + J.solverWords.foldr max 0 + 2 := by omega
    exact (hBase.trans (Nat.le_self_pow (by omega) _)).trans_lt
      (pow_lt_two_pow_wordSize hc J.solverWords)
  change MeetsContract w (linkedCappedSolverProgram P.edgeThreshold P.qualityBudget P.dispatch P.cycle P.forest) 0
    (compressedSolverContract w
      (connectedSolverRuntimeTime ⟨P.resources, cappedQualityExponent P.edgeThreshold P.qualityBudget, cappedQualityCost⟩)
      (connectedSolverRuntimeWorkspace ⟨P.resources, cappedQualityExponent P.edgeThreshold P.qualityBudget, cappedQualityCost⟩))
  refine linkedCappedSolverProgram_meetsConnectedContract w P.edgeThreshold P.qualityBudget P.resources P.dispatch P.cycle P.forest
    P.forestModel P.forestSpec hw P.qualityAddress.symm ?_
  intro J' hJn hm hCost hCap
  dsimp only
  intro hwJ
  have hp : ∀ e, 1 ≤ J'.capacity e := fun e => (hCap e).1
  let W := P.witness
  have hModel := orderedConcrete_minRatioSpecWithFailureEdgeOnlyConnectedUpTo W J' hJn hm hp
  obtain ⟨RC, RD, hCycle, hCBound, hForest, hFInit, hFOp⟩ :=
    P.supported J J' hJn hm hCost hCap hwJ
  refine ⟨Chain.Ordered.algorithm2_dsWithFailureOwn (orderedConcreteCirculationCfg W J'), RC, RD, ?_⟩
  exact {
    cycleModel := hModel
    cycleMachine := hCycle
    cycleBound := hCBound
    forestMachine := hForest
    forestInitBound := hFInit
    forestOpBound := hFOp }

/-- The concrete linked solver's scratch reservation obeys the polynomial bound. -/
theorem ConcreteDataStructurePrograms.workspace_le (P : ConcreteDataStructurePrograms) (n m : ℕ) :
    connectedSolverRuntimeWorkspace P.runtimeResources n m ≤ (n + m + 2) ^ P.scratchDegree := by
  have hdim : ∀ M ∈ Finset.Icc m (7 * m),
      P.allocationCoefficient * (n + 1 + M + 2) ^ P.allocationDegree ≤
        (P.allocationCoefficient * 8 ^ P.allocationDegree) * (n + m + 2) ^ P.allocationDegree := by
    intro M hM
    have hMle : M ≤ 7 * m := (Finset.mem_Icc.mp hM).2
    have hsum : n + 1 + M + 2 ≤ 8 * (n + m + 2) := by omega
    calc
      P.allocationCoefficient * (n + 1 + M + 2) ^ P.allocationDegree
          ≤ P.allocationCoefficient * (8 * (n + m + 2)) ^ P.allocationDegree :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum _)
      _ = (P.allocationCoefficient * 8 ^ P.allocationDegree) * (n + m + 2) ^ P.allocationDegree := by
            rw [Nat.mul_pow, mul_assoc]
  exact connectedIPMRuntimeWorkspace_polynomial P.runtimeResources n m
    (P.allocationCoefficient * 8 ^ P.allocationDegree) P.allocationDegree P.qualityLinearCoeff
    (fun M => cappedQuality_linear_spec P.edgeThreshold P.qualityBudget M)
    (fun M hM => (P.cycleSpace_poly (n + 1) M).trans (hdim M hM))
    (fun M hM => (P.forestInitSpace_poly (n + 1) M).trans (hdim M hM))
    (fun M hM => (P.forestOpSpace_poly (n + 1) M).trans (hdim M hM))


end MinCostFlow.Final
