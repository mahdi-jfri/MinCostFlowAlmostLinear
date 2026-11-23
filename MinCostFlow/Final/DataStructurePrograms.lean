module

public import MinCostFlow.Final.IPMWorkspace
public import MinCostFlow.Final.OuterScalingRunsTo
public import MinCostFlow.IPM.Machine.BoundedSolver
public import MinCostFlow.Final.RuntimeQualityBounds
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.IPM.Machine.SolverInitialBounds
import Mathlib.Tactic

/-!
# The two modules supplied to the final solver

The graph data structures occupy fixed procedure slots after the
bounded IPM code. Their contracts use the precision of the actual
augmented instance. A common polynomial allocation bound fits
all of these calls in the scratch reserved by outer scaling.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine IPM IPM.Machine

/-- Place the quality code directly after the two supplied data structures. -/
def linkedQualityBase (dispatch : SolverDispatch) (cycle forest : List Stmt) : ℕ :=
  (boundedIPMRuntimeModule 0 dispatch).length + cycle.length + forest.length

/-- Put the runtime IPM at zero, then the data structures and the two
procedures for the integer quality calculation. -/
def linkedSolverProgram (A : ℕ) (dispatch : SolverDispatch)
    (cycle forest : List Stmt) : Program :=
  let b := linkedQualityBase dispatch cycle forest
  Program.mk (boundedIPMRuntimeModule 0 dispatch ++ cycle ++ forest ++
    [Num.IPM.bitLengthBody b, integerQualityBody b A])

/-- The two module implementations and their bounds at all canonical solver
widths. Entry addresses are absolute indices in the linked solver. -/
structure DataStructurePrograms where
  resources : SolverResources
  dispatch : SolverDispatch
  cycle : List Stmt
  forest : List Stmt
  cycleDeterministic : ∀ body ∈ cycle, body.NoRand
  forestDeterministic : ∀ body ∈ forest, body.NoRand
  cycleInitAddress : dispatch.cycleInit ∈ Finset.Ico
    (boundedIPMRuntimeModule 0 dispatch).length
    ((boundedIPMRuntimeModule 0 dispatch).length + cycle.length)
  cycleOpAddress : ∀ j < 4, dispatch.cycleOp j ∈ Finset.Ico
    (boundedIPMRuntimeModule 0 dispatch).length
    ((boundedIPMRuntimeModule 0 dispatch).length + cycle.length)
  forestInitAddress : dispatch.forestInit ∈ Finset.Ico
    ((boundedIPMRuntimeModule 0 dispatch).length + cycle.length)
    ((boundedIPMRuntimeModule 0 dispatch).length + cycle.length + forest.length)
  forestOpAddress : ∀ j < 6, dispatch.forestOp j ∈ Finset.Ico
    ((boundedIPMRuntimeModule 0 dispatch).length + cycle.length)
    ((boundedIPMRuntimeModule 0 dispatch).length + cycle.length + forest.length)
  qualityBudget : ℕ
  qualityAddress : dispatch.quality = linkedQualityBase dispatch cycle forest + 1
  qualityLinearCoefficient : ℕ
  qualityLinear : ∀ M, 2^integerQualityExponent qualityBudget M ≤ qualityLinearCoefficient*(M+2)
  forestModel : Rounding.DynForest
  forestSpec : forestModel.IsSpec
  allocationCoefficient : ℕ
  allocationDegree : ℕ
  cycleSpace : ∀ n m M, M ∈ Finset.Icc m (3*m) →
    resources.cycleSpace (n+1) M ≤ allocationCoefficient*(n+m+2)^allocationDegree
  forestInitSpace : ∀ n m M, M ∈ Finset.Icc m (3*m) →
    resources.forestInitSpace (n+1) M ≤ allocationCoefficient*(n+m+2)^allocationDegree
  forestOpSpace : ∀ n m M, M ∈ Finset.Icc m (3*m) →
    resources.forestOpSpace (n+1) M ≤ allocationCoefficient*(n+m+2)^allocationDegree
  cycleConstant : ℝ
  forestConstant : ℝ
  forestLogDegree : ℕ
  cycleRate : ∀ m, (resources.cycleRate m : ℝ) ≤ Chain.alg2TimeFactor cycleConstant (47/48) m
  forestRate : ∀ n, (resources.forestRate n : ℝ) ≤ forestConstant*Real.log ((n:ℝ)+2)^forestLogDegree
  supported : ∀ (source J : Circulation), J.n ≤ 2*J.m+1 → 0 < J.m → J.CostsBounded (J.m^10) →
    (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m^40) →
    ∀ hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m) ≤
      wordSize (scratchWordMultiplier 1
        (10*(Nat.clog 2 allocationCoefficient+allocationDegree+2*(Nat.clog 2 qualityLinearCoefficient+2)+240)))
        source.solverWords,
      integerQualityExponent qualityBudget (solverAugmented J).m ≤ slackRangeExponent (solverAugmented J).m (solverPenalty J.m) ∧
      ∃ (cycleModel : MinRatioDataStructureWithFailure) (RC : DSRep cycleModel.State) (RD : DSRep forestModel.State),
        SolverDataStructuresAt _ (linkedSolverProgram qualityBudget dispatch cycle forest) dispatch
          ({resources with qualityExponent := integerQualityExponent qualityBudget (solverAugmented J).m}) (solverAugmented J) (solverPenalty J.m) hw cycleModel forestModel RC RD

/-- The runtime selection and its cost are fixed by the integer program. -/
def DataStructurePrograms.runtimeResources (P : DataStructurePrograms) : SolverRuntimeResources :=
  ⟨P.resources, integerQualityExponent P.qualityBudget, integerQualityCost⟩

/-- Subpolynomial coefficient of the selected reciprocal quality. -/
def DataStructurePrograms.qualityConstant (P : DataStructurePrograms) : ℝ :=
  65536*((P.qualityBudget:ℝ)+1)

theorem DataStructurePrograms.quality (P : DataStructurePrograms) (m : ℕ) :
    (2:ℝ)^P.runtimeResources.qualityExponent m ≤
      Chain.alg2TimeFactor P.qualityConstant (47/48) m :=
  (integerQualityExponent_bounds P.qualityBudget m).2

/-- The polynomial degree sufficient for every bounded IPM call. -/
def DataStructurePrograms.scratchDegree (P : DataStructurePrograms) : ℕ :=
  10*(Nat.clog 2 P.allocationCoefficient+P.allocationDegree+2*(Nat.clog 2 P.qualityLinearCoefficient+2)+240)

/-- The bounded solver with both supplied modules installed. -/
def DataStructurePrograms.solver (P : DataStructurePrograms) : Program :=
  linkedSolverProgram P.qualityBudget P.dispatch P.cycle P.forest

/-- Every solver procedure is deterministic after linking. -/
theorem DataStructurePrograms.solver_deterministic (P : DataStructurePrograms) :
    P.solver.IsDeterministic := by
  intro body hb
  let b := linkedQualityBase P.dispatch P.cycle P.forest
  change body ∈ boundedIPMRuntimeModule 0 P.dispatch ++ P.cycle ++ P.forest ++
    [Num.IPM.bitLengthBody b, integerQualityBody b P.qualityBudget] at hb
  rcases List.mem_append.mp hb with hb | hb
  · rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact boundedIPMRuntimeModule_noRand _ _ body hb
      · exact P.cycleDeterministic body hb
    · exact P.forestDeterministic body hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact Num.IPM.bitLengthModule_noRand b _ List.mem_cons_self
    · exact integerQualityBody_noRand _ _

/-- At each selected guest width the linked program implements the
bounded-circulation solver contract on compressed inputs. -/
theorem DataStructurePrograms.solver_meetsContract (P : DataStructurePrograms) (J : Circulation) :
    let w := wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords
    MeetsContract w P.solver 0 (compressedSolverContract w
      (solverRuntimeTime P.runtimeResources) (solverRuntimeWorkspace P.runtimeResources)) := by
  dsimp only
  let b := linkedQualityBase P.dispatch P.cycle P.forest
  have hall := hasAt_self (boundedIPMRuntimeModule 0 P.dispatch ++ P.cycle ++ P.forest ++
    [Num.IPM.bitLengthBody b, integerQualityBody b P.qualityBudget])
  have hLayout := hasAt_append_left (hasAt_append_left (hasAt_append_left hall))
  have hQualityModule : P.solver.HasAt b
      [Num.IPM.bitLengthBody b, integerQualityBody b P.qualityBudget] := by
    simpa only [DataStructurePrograms.solver, linkedSolverProgram, b, linkedQualityBase, List.length_append, Nat.zero_add] using (Num.hasAt_append_right hall)
  have hBitModule := Num.hasAt_append_left (xs := [Num.IPM.bitLengthBody b])
    (ys := [integerQualityBody b P.qualityBudget]) hQualityModule
  have hw : 2 < 2^wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords := by
    have hc : 1 ≤ scratchWordMultiplier 1 P.scratchDegree := by
      unfold scratchWordMultiplier
      omega
    have hBase : 2 ≤ J.solverWords.length + J.solverWords.foldr max 0 + 2 := by omega
    exact (hBase.trans (Nat.le_self_pow (by omega) _)).trans_lt
      (pow_lt_two_pow_wordSize hc J.solverWords)
  have hBit := Num.IPM.bitLength_meetsContract hw hBitModule
  have hQualityAt := Num.hasAt_append_right (xs := [Num.IPM.bitLengthBody b]) hQualityModule
  have hQuality := integerQuality_meetsContract hQualityAt.head hBit
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at hQuality
  rw [show b+1=P.dispatch.quality from P.qualityAddress.symm] at hQuality
  exact boundedIPMRuntimeFixedPrecision_meetsCompressedContract P.runtimeResources P.dispatch P.forestModel P.forestSpec
    hLayout hQuality (P.supported J)

/-- The linked solver's scratch reservation satisfies the scaling bound. -/
theorem DataStructurePrograms.workspace_le (P : DataStructurePrograms) (n m : ℕ) :
    solverRuntimeWorkspace P.runtimeResources n m ≤ (n+m+2)^P.scratchDegree :=
  ipmRuntimeWorkspace_polynomial P.runtimeResources n m P.allocationCoefficient P.allocationDegree
    P.qualityLinearCoefficient P.qualityLinear (P.cycleSpace n m) (P.forestInitSpace n m) (P.forestOpSpace n m)

end MinCostFlow.Final
