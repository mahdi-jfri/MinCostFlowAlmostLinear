module

public import MinCostFlow.Final.IPMWorkspace
public import MinCostFlow.Final.Scratch
public import WordRAM.Entry
public import MinCostFlow.IPM.Machine.BoundedSolver
public import MinCostFlow.Final.ChainToolBounds
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.IPM.Machine.SolverInitialBounds
import Mathlib.Tactic

/-!
# Modules for the widened runtime solver

The graph data structures occupy fixed procedure slots after the
bounded IPM code. Their contracts use the precision of the actual
augmented instance. A common polynomial allocation bound fits
all of these calls in the scratch reserved by outer scaling.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine IPM IPM.Machine Chain

/-- Place the quality code directly after the two supplied data structures. -/
def linkedWidenedQualityBase (dispatch : SolverDispatch) (cycle forest : List Stmt) : ℕ :=
  (boundedIPMQualityRuntimeModule 0 dispatch).length + cycle.length + forest.length

/-- Put the runtime IPM at zero, then the data structures and the two
procedures for the integer quality calculation. -/
def linkedWidenedSolverProgram (A : ℕ) (dispatch : SolverDispatch)
    (cycle forest : List Stmt) : Program :=
  let b := linkedWidenedQualityBase dispatch cycle forest
  Program.mk (boundedIPMQualityRuntimeModule 0 dispatch ++ cycle ++ forest ++
    [Num.IPM.bitLengthBody b, integerQualityBody b A])

/-- The model's linear reciprocal-quality envelope gives a uniform
word multiplier for the program compiled at this tool budget. -/
noncomputable def QuantitativeChainTools.linearQualityCoefficient (T : QuantitativeChainTools) : ℕ :=
  Classical.choose (integerQualityExponent_linear T.budget)

theorem QuantitativeChainTools.linearQuality (T : QuantitativeChainTools) (M : ℕ) :
    2^integerQualityExponent T.budget M ≤ T.linearQualityCoefficient*(M+2) :=
  Classical.choose_spec (integerQualityExponent_linear T.budget) M

/-- The machine obligations at the selected format. The mathematical
min-ratio specification is supplied separately by Theorem 5.1. -/
structure SolverQualityMachinesAt (w : ℕ) (p : Program) (entry : SolverDispatch)
    (resources : SolverResources) (I : Instance) (V : ℕ)
    (hw : ipmQualityParameterWordBits I.m V resources.qualityExponent≤w)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (RC : DSRep C.State)
    (RD : DSRep D.State) : Prop where
  cycleMachine : RC.Implements w p entry.cycleInit entry.cycleOp
    (minRatioMachineContract (ipmQualityMinRatioFormat I.m V resources.qualityExponent hw) C
      (namedInstance I) I.m (1/(2:ℝ)^resources.qualityExponent) (Num.IPM.alphaPrime I.m V/8)
      resources.cycleRate (resources.cycleAllocation I.n I.m))
  cycleBound : ∀ j<4, ∀ args, resources.cycleAllocation I.n I.m j args≤resources.cycleSpace I.n I.m
  forestMachine : RD.Implements w p entry.forestInit entry.forestOp
    (forestMachineContract D w 4 (ipmQualityLimbs I.m V resources.qualityExponent)
      (ipmQualityPrecision I.m V resources.qualityExponent) resources.forestRate
      (resources.forestAllocation I.n I.m))
  forestInitBound : ∀ b, resources.forestAllocation I.n I.m 6
    [I.n,ipmQualityLimbs I.m V resources.qualityExponent,ipmQualityPrecision I.m V resources.qualityExponent,b]
      ≤ resources.forestInitSpace I.n I.m
  forestOpBound : ∀ j<6, ∀ args, resources.forestAllocation I.n I.m j args≤resources.forestOpSpace I.n I.m

/-- The two module implementations and their bounds at all canonical solver
widths. Entry addresses are absolute indices in the linked solver. -/
structure WidenedDataStructurePrograms where
  resources : SolverResources
  dispatch : SolverDispatch
  cycle : List Stmt
  forest : List Stmt
  cycleDeterministic : ∀ body ∈ cycle, body.NoRand
  forestDeterministic : ∀ body ∈ forest, body.NoRand
  cycleInitAddress : dispatch.cycleInit ∈ Finset.Ico
    (boundedIPMQualityRuntimeModule 0 dispatch).length
    ((boundedIPMQualityRuntimeModule 0 dispatch).length + cycle.length)
  cycleOpAddress : ∀ j < 4, dispatch.cycleOp j ∈ Finset.Ico
    (boundedIPMQualityRuntimeModule 0 dispatch).length
    ((boundedIPMQualityRuntimeModule 0 dispatch).length + cycle.length)
  forestInitAddress : dispatch.forestInit ∈ Finset.Ico
    ((boundedIPMQualityRuntimeModule 0 dispatch).length + cycle.length)
    ((boundedIPMQualityRuntimeModule 0 dispatch).length + cycle.length + forest.length)
  forestOpAddress : ∀ j < 6, dispatch.forestOp j ∈ Finset.Ico
    ((boundedIPMQualityRuntimeModule 0 dispatch).length + cycle.length)
    ((boundedIPMQualityRuntimeModule 0 dispatch).length + cycle.length + forest.length)
  tools : QuantitativeChainTools
  qualityAddress : dispatch.quality = linkedWidenedQualityBase dispatch cycle forest + 1
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
  supported : ∀ (source J : Circulation), J.n ≤ 2*J.m+1 → (hm : 0 < J.m) → J.CostsBounded (J.m^10) →
    (hc : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m^40) →
    ∀ hw : ipmQualityParameterWordBits (solverAugmented J).m (solverPenalty J.m)
      (integerQualityExponent tools.budget (solverAugmented J).m) ≤
      wordSize (scratchWordMultiplier 1
        (10*(Nat.clog 2 allocationCoefficient+allocationDegree+2*(Nat.clog 2 tools.linearQualityCoefficient+2)+240)))
        source.solverWords,
      let C := algorithm2_dsWithFailure (tools.config J hm (fun e => (hc e).1))
      ∃ (RC : DSRep C.State) (RD : DSRep forestModel.State),
        SolverQualityMachinesAt _ (linkedWidenedSolverProgram tools.budget dispatch cycle forest) dispatch
          ({resources with qualityExponent := integerQualityExponent tools.budget (solverAugmented J).m})
          (solverAugmented J) (solverPenalty J.m) hw C forestModel RC RD

/-- The runtime selection and its cost are fixed by the integer program. -/
noncomputable def WidenedDataStructurePrograms.runtimeResources (P : WidenedDataStructurePrograms) : SolverRuntimeResources :=
  ⟨P.resources, integerQualityExponent P.tools.budget, integerQualityCost⟩

/-- Subpolynomial coefficient of the selected reciprocal quality. -/
noncomputable def WidenedDataStructurePrograms.qualityConstant (P : WidenedDataStructurePrograms) : ℝ :=
  65536*((P.tools.budget:ℝ)+1)

theorem WidenedDataStructurePrograms.quality (P : WidenedDataStructurePrograms) (m : ℕ) :
    (2:ℝ)^P.runtimeResources.qualityExponent m ≤
      Chain.alg2TimeFactor P.qualityConstant (47/48) m :=
  (integerQualityExponent_bounds P.tools.budget m).2

/-- The polynomial degree sufficient for every bounded IPM call. -/
noncomputable def WidenedDataStructurePrograms.scratchDegree (P : WidenedDataStructurePrograms) : ℕ :=
  10*(Nat.clog 2 P.allocationCoefficient+P.allocationDegree+2*(Nat.clog 2 P.tools.linearQualityCoefficient+2)+240)

/-- The bounded solver with both supplied modules installed. -/
noncomputable def WidenedDataStructurePrograms.solver (P : WidenedDataStructurePrograms) : Program :=
  linkedWidenedSolverProgram P.tools.budget P.dispatch P.cycle P.forest

/-- Every solver procedure is deterministic after linking. -/
theorem WidenedDataStructurePrograms.solver_deterministic (P : WidenedDataStructurePrograms) :
    P.solver.IsDeterministic := by
  intro body hb
  let b := linkedWidenedQualityBase P.dispatch P.cycle P.forest
  change body ∈ boundedIPMQualityRuntimeModule 0 P.dispatch ++ P.cycle ++ P.forest ++
    [Num.IPM.bitLengthBody b, integerQualityBody b P.tools.budget] at hb
  rcases List.mem_append.mp hb with hb | hb
  · rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact boundedIPMQualityRuntimeModule_noRand _ _ body hb
      · exact P.cycleDeterministic body hb
    · exact P.forestDeterministic body hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact Num.IPM.bitLengthModule_noRand b _ List.mem_cons_self
    · exact integerQualityBody_noRand _ _

/-- At each selected guest width the linked program implements the
bounded-circulation solver contract on compressed inputs. -/
theorem WidenedDataStructurePrograms.solver_meetsContract (P : WidenedDataStructurePrograms) (J : Circulation) :
    let w := wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords
    MeetsContract w P.solver 0 (compressedSolverContract w
      (solverQualityRuntimeTime P.runtimeResources) (solverQualityRuntimeWorkspace P.runtimeResources)) := by
  dsimp only
  let b := linkedWidenedQualityBase P.dispatch P.cycle P.forest
  have hall := hasAt_self (boundedIPMQualityRuntimeModule 0 P.dispatch ++ P.cycle ++ P.forest ++
    [Num.IPM.bitLengthBody b, integerQualityBody b P.tools.budget])
  have hLayout := hasAt_append_left (hasAt_append_left (hasAt_append_left hall))
  have hQualityModule : P.solver.HasAt b
      [Num.IPM.bitLengthBody b, integerQualityBody b P.tools.budget] := by
    simpa only [WidenedDataStructurePrograms.solver, linkedWidenedSolverProgram, b, linkedWidenedQualityBase, List.length_append, Nat.zero_add] using (Num.hasAt_append_right hall)
  have hBitModule := Num.hasAt_append_left (xs := [Num.IPM.bitLengthBody b])
    (ys := [integerQualityBody b P.tools.budget]) hQualityModule
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
  exact boundedIPMRuntime_meetsCompressedContract P.runtimeResources P.dispatch P.forestModel P.forestSpec
    hLayout hQuality (by
      intro input hn hm hc hp hw'
      obtain ⟨RC,RD,hMachines⟩ := P.supported J input hn hm hc hp hw'
      exact ⟨_,RC,RD,P.tools.model_spec input hn hm (fun e => (hp e).1),
        hMachines.cycleMachine,hMachines.cycleBound,hMachines.forestMachine,
        hMachines.forestInitBound,hMachines.forestOpBound⟩)

/-- The linked solver's scratch reservation satisfies the scaling bound. -/
theorem WidenedDataStructurePrograms.workspace_le (P : WidenedDataStructurePrograms) (n m : ℕ) :
    solverQualityRuntimeWorkspace P.runtimeResources n m ≤ (n+m+2)^P.scratchDegree :=
  ipmQualityRuntimeWorkspace_polynomial P.runtimeResources n m P.allocationCoefficient P.allocationDegree
    P.tools.linearQualityCoefficient P.tools.linearQuality (P.cycleSpace n m) (P.forestInitSpace n m) (P.forestOpSpace n m)

end MinCostFlow.Final
