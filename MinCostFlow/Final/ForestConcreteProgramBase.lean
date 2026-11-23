module

public import MinCostFlow.Final.CappedConnectedProgram
public import MinCostFlow.Final.OrderedConcreteChainModel
public import MinCostFlow.Final.ConcreteChainModelWithLast
public import MinCostFlow.Final.ConnectedForestIPMWorkspace
public import MinCostFlow.Final.ConcretePrograms
public import MinCostFlow.Final.ConnectedLinkedProgram
public import MinCostFlow.Final.DynamicLctForest
import Mathlib.Tactic

/-!
# Shared module placement, a small-instance witness, and base infrastructure for forest-discharged solvers

Provides:
1. `mrdsCycleBase`, `boundedConnectedIPMRuntimeModule_length`, and `mrdsSolverDispatch`:
   fixed code placement offsets for the min-ratio cycle module and `dynLctForestBodies`.
2. `exists_compressed_limbs_ne`: small-instance witness (`m = 1` vs `m = 2`) showing why no
   fixed program can embed raw compile-time `lctForestBodies` across all reachable inputs.
3. `ForestConcreteProgramBase`: shared non-`supported` fields of `ForestConcretePrograms` and
   `DyadicForestConcretePrograms`, together with shared workspace bounds (`workspace_le`),
   linked solver contract glue (`solver_meetsContract_of`), and outer scaling execution
   (`program_runsTo_of`).
-/

@[expose] public noncomputable section
namespace MinCostFlow.Final
open Chain IPM IPM.Machine WordRAM Scaling Scaling.Machine LinkCut.Prog

section ModulePlacement

def placeholderDispatch : SolverDispatch :=
  ⟨0, fun _ => 0, 0, fun _ => 0, 0⟩

private theorem solverSearchControl_length (b init : ℕ) (op : ℕ → ℕ) :
    (solverSearchControl b init op).length = 33 := by
  simp [solverSearchControl]

private theorem solverSearchModule_length (b init : ℕ) (op : ℕ → ℕ) :
    (solverSearchModule b init op).length = 33 + (solverSearchAux (b + 33)).length := by
  simp [solverSearchModule, solverSearchControl_length]

private theorem solverRoundControl_length (b init : ℕ) (op : ℕ → ℕ) :
    (solverRoundControl b init op).length = 29 := by
  simp [solverRoundControl]

private theorem solverRoundModule_length (b init : ℕ) (op : ℕ → ℕ) :
    (solverRoundModule b init op).length = 29 + (solverRoundAux b).length := by
  simp [solverRoundModule, solverRoundControl_length]

/-- Fixed code offset at which the min-ratio cycle (`cycle`) module is placed after
`boundedConnectedIPMRuntimeModule 0`. Independent of `dispatch`. -/
def mrdsCycleBase : ℕ :=
  (boundedConnectedIPMRuntimeModule 0 placeholderDispatch).length

/-- `boundedConnectedIPMRuntimeModule 0 dispatch` has fixed length `mrdsCycleBase`,
independent of the dispatched procedure addresses. -/
theorem boundedConnectedIPMRuntimeModule_length (e : SolverDispatch) :
    (boundedConnectedIPMRuntimeModule 0 e).length = mrdsCycleBase := by
  have hc : ∀ e' : SolverDispatch, (connectedSolverControl 0 e').length = 13 := fun e' => by
    simp [connectedSolverControl]
  unfold mrdsCycleBase boundedConnectedIPMRuntimeModule
  simp only [List.length_append, hc, connectedSolverOwnModules, List.length_cons,
    solverSearchModule_length, solverRoundModule_length]

/-- `boundedConnectedIPMRuntimeModuleWithV 0 e` has the same fixed length `mrdsCycleBase`. -/
theorem boundedConnectedIPMRuntimeModuleWithV_length (e : SolverDispatch) :
    (boundedConnectedIPMRuntimeModuleWithV 0 e).length = mrdsCycleBase :=
  (boundedConnectedIPMRuntimeModuleWithV_eq_length e).trans (boundedConnectedIPMRuntimeModule_length e)

/-- Solver dispatch table assembled automatically from the min-ratio cycle entry points
and `cycle.length`, using `dynLctForestBodies 4 (mrdsCycleBase + cycle.length)` for
the forest and placing `quality` immediately after it. -/
def mrdsSolverDispatch (cycleInit : ℕ) (cycleOp : ℕ → ℕ) (cycleLen : ℕ) : SolverDispatch where
  cycleInit := cycleInit
  cycleOp := cycleOp
  forestInit := mrdsCycleBase + cycleLen
  forestOp := lctForestOp (mrdsCycleBase + cycleLen)
  quality := mrdsCycleBase + cycleLen + (dynLctForestBodies 4 (mrdsCycleBase + cycleLen)).length + 2

end ModulePlacement

section SmallInstanceObstruction

private def unitCirculation (m : ℕ) : Circulation where
  n := 1
  m := m
  tail _ := 0
  head _ := 0
  capacity _ := 1
  cost _ := 0

/-- Even on the tiny concrete inputs `m = 1` and `m = 2`, the solver's compressed
connected augmentations require strictly different limb counts `L = ipmQualityLimbs`,
so by `lctForestBodies_ne_of_limbs_ne` no fixed `Program` at a fixed base `b0` can
embed raw `lctForestBodies 4 L P b0` for all reachable inputs. -/
theorem exists_compressed_limbs_ne (threshold A b0 : ℕ) :
    ∃ (J₁ J₂ : Circulation),
      (J₁.n ≤ 2 * J₁.m + 1 ∧ 0 < J₁.m ∧ J₁.CostsBounded (J₁.m ^ 10) ∧
        ∀ e, 1 ≤ J₁.capacity e ∧ J₁.capacity e ≤ J₁.m ^ 40) ∧
      (J₂.n ≤ 2 * J₂.m + 1 ∧ 0 < J₂.m ∧ J₂.CostsBounded (J₂.m ^ 10) ∧
        ∀ e, 1 ≤ J₂.capacity e ∧ J₂.capacity e ≤ J₂.m ^ 40) ∧
      let I₁ := solverConnectedAugmented J₁
      let I₂ := solverConnectedAugmented J₂
      let V₁ := solverPenalty J₁.m
      let V₂ := solverPenalty J₂.m
      let L₁ := ipmQualityLimbs I₁.m V₁ (cappedQualityExponent threshold A I₁.m)
      let L₂ := ipmQualityLimbs I₂.m V₂ (cappedQualityExponent threshold A I₂.m)
      let P₁ := ipmQualityPrecision I₁.m V₁ (cappedQualityExponent threshold A I₁.m)
      let P₂ := ipmQualityPrecision I₂.m V₂ (cappedQualityExponent threshold A I₂.m)
      L₁ < L₂ ∧ lctForestBodies 4 L₁ P₁ b0 ≠ lctForestBodies 4 L₂ P₂ b0 := by
  let J₁ := unitCirculation 1
  let J₂ := unitCirculation 2
  have h1 : J₁.n ≤ 2 * J₁.m + 1 ∧ 0 < J₁.m ∧ J₁.CostsBounded (J₁.m ^ 10) ∧
      ∀ e, 1 ≤ J₁.capacity e ∧ J₁.capacity e ≤ J₁.m ^ 40 :=
    ⟨by decide, by decide, fun _ => by simp [J₁, unitCirculation],
      fun _ => ⟨le_rfl, by simp [J₁, unitCirculation]⟩⟩
  have h2 : J₂.n ≤ 2 * J₂.m + 1 ∧ 0 < J₂.m ∧ J₂.CostsBounded (J₂.m ^ 10) ∧
      ∀ e, 1 ≤ J₂.capacity e ∧ J₂.capacity e ≤ J₂.m ^ 40 :=
    ⟨by decide, by decide, fun _ => by simp [J₂, unitCirculation],
      fun _ => ⟨le_rfl, by simp [J₂, unitCirculation]⟩⟩
  refine ⟨J₁, J₂, h1, h2, ?_⟩
  dsimp only
  have hs1 := solverConnectedAugmented_size J₁ h1.1 h1.2.1 (fun e => (h1.2.2.2 e).1)
  have hs2 := solverConnectedAugmented_size J₂ h2.1 h2.2.1 (fun e => (h2.2.2.2 e).1)
  have hm1_ub : (solverConnectedAugmented J₁).m ≤ 3 := by
    have hs := connectedInitialInstance_m_le J₁.toInstance (solverPenalty J₁.m : ℤ)
    rw [Circulation.toInstance_m] at hs
    change (solverConnectedAugmented J₁).m ≤ J₁.m + 2 * J₁.n at hs
    simpa [J₁, unitCirculation] using hs
  have hm2_lb : 2 ≤ (solverConnectedAugmented J₂).m := hs2.1
  have hm2_sz : 2 ≤ (solverConnectedAugmented J₂).m.size := by
    by_contra hlt
    have hlt2 : (solverConnectedAugmented J₂).m < 2 ^ 1 :=
      (Nat.size_le).mp (by omega : (solverConnectedAugmented J₂).m.size ≤ 1)
    omega
  have hm_sz : (solverConnectedAugmented J₁).m.size ≤ (solverConnectedAugmented J₂).m.size := by
    have ha : (solverConnectedAugmented J₁).m.size ≤ 2 :=
      Nat.size_le.mpr (lt_of_le_of_lt hm1_ub (by decide))
    exact ha.trans hm2_sz
  have hk_le : cappedQualityExponent threshold A (solverConnectedAugmented J₁).m ≤
      cappedQualityExponent threshold A (solverConnectedAugmented J₂).m := by
    have hcap_sz : (max (solverConnectedAugmented J₁).m threshold).size ≤
        (max (solverConnectedAugmented J₂).m threshold).size := by
      rcases le_total threshold 3 with ht | ht
      · have hL : (max (solverConnectedAugmented J₁).m threshold).size ≤ 2 :=
          Nat.size_le.mpr (lt_of_le_of_lt (max_le hm1_ub ht) (by decide))
        have hR : 2 ≤ (max (solverConnectedAugmented J₂).m threshold).size :=
          hm2_sz.trans (Nat.size_le_size (le_max_left _ _))
        exact le_trans hL hR
      · have hle : max (solverConnectedAugmented J₁).m threshold ≤ max (solverConnectedAugmented J₂).m threshold :=
          max_le (hm1_ub.trans (ht.trans (le_max_right _ _))) (le_max_right _ _)
        exact Nat.size_le_size hle
    have hb := Nat.size_le_size (Nat.add_le_add_right hcap_sz 1)
    unfold cappedQualityExponent chainEdgeCap integerQualityExponent
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hb)
      (Nat.pow_le_pow_right (by decide)
        (Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left 47 hb) 47)))
  have hv1 : solverPenalty J₁.m = 16 := by
    simp [J₁, unitCirculation, solverPenalty, solverCapacityBound]
  have hv2 : 32 ≤ solverPenalty J₂.m := by
    have hcap : 2 ^ 40 ≤ solverCapacityBound 2 := le_max_right _ _
    have h2 : 4 ≤ solverCapacityBound 2 ^ 2 := by
      calc 4 ≤ (2 ^ 40) ^ 2 := by decide
        _ ≤ solverCapacityBound 2 ^ 2 := Nat.pow_le_pow_left hcap 2
    show 32 ≤ 4 * J₂.m * solverCapacityBound J₂.m ^ 2
    calc 32 = 4 * 2 * 4 := by decide
      _ ≤ 4 * 2 * solverCapacityBound 2 ^ 2 := Nat.mul_le_mul_left 8 h2
      _ = 4 * J₂.m * solverCapacityBound J₂.m ^ 2 := by rfl
  have hv_sz : (solverPenalty J₁.m).size < (solverPenalty J₂.m).size := by
    rw [hv1]
    have h16 : (16).size = 5 := by decide
    have h32 : 5 < (solverPenalty J₂.m).size := by
      by_contra hle
      have hlt : solverPenalty J₂.m < 2 ^ 5 := Nat.size_le.mp (by omega)
      omega
    omega
  have hslack : slackRangeExponent (solverConnectedAugmented J₁).m (solverPenalty J₁.m) ≤
      slackRangeExponent (solverConnectedAugmented J₂).m (solverPenalty J₂.m) := by
    unfold slackRangeExponent
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hgrad : gradientCoefficientExponent (solverConnectedAugmented J₁).m (solverPenalty J₁.m) <
      gradientCoefficientExponent (solverConnectedAugmented J₂).m (solverPenalty J₂.m) := by
    unfold gradientCoefficientExponent; omega
  have halpha : Num.IPM.alphaScale (solverConnectedAugmented J₁).m (solverPenalty J₁.m) <
      Num.IPM.alphaScale (solverConnectedAugmented J₂).m (solverPenalty J₂.m) := by
    unfold Num.IPM.alphaScale; omega
  have hq : qualitySlackExponent (solverConnectedAugmented J₁).m (solverPenalty J₁.m)
        (cappedQualityExponent threshold A (solverConnectedAugmented J₁).m) ≤
      qualitySlackExponent (solverConnectedAugmented J₂).m (solverPenalty J₂.m)
        (cappedQualityExponent threshold A (solverConnectedAugmented J₂).m) :=
    max_le (hslack.trans (le_max_left _ _)) (hk_le.trans (le_max_right _ _))
  have hrange : ipmQualityRangeExponent (solverConnectedAugmented J₁).m (solverPenalty J₁.m)
        (cappedQualityExponent threshold A (solverConnectedAugmented J₁).m) <
      ipmQualityRangeExponent (solverConnectedAugmented J₂).m (solverPenalty J₂.m)
        (cappedQualityExponent threshold A (solverConnectedAugmented J₂).m) := by
    unfold ipmQualityRangeExponent; omega
  have hprec : ipmQualityPrecision (solverConnectedAugmented J₁).m (solverPenalty J₁.m)
        (cappedQualityExponent threshold A (solverConnectedAugmented J₁).m) <
      ipmQualityPrecision (solverConnectedAugmented J₂).m (solverPenalty J₂.m)
        (cappedQualityExponent threshold A (solverConnectedAugmented J₂).m) := by
    unfold ipmQualityPrecision ipmQualityErrorBits; omega
  have hL : ipmQualityLimbs (solverConnectedAugmented J₁).m (solverPenalty J₁.m)
        (cappedQualityExponent threshold A (solverConnectedAugmented J₁).m) <
      ipmQualityLimbs (solverConnectedAugmented J₂).m (solverPenalty J₂.m)
        (cappedQualityExponent threshold A (solverConnectedAugmented J₂).m) := by
    unfold ipmQualityLimbs; omega
  exact ⟨hL, lctForestBodies_ne_of_limbs_ne hL.ne⟩

end SmallInstanceObstruction

/-- Uniform space coefficient covering both the min-ratio cycle module and the dynamic link-cut forest workspace. -/
def forestSpaceCoeff (c : ℕ) : ℕ := max c 2000000

/-- Uniform space polynomial degree covering both the min-ratio cycle module and the dynamic link-cut forest workspace. -/
def forestSpaceDeg (d : ℕ) : ℕ := max d 2

/-- Scratch exponent covering both the min-ratio cycle space (`c * (n+m+2)^d`) and the link-cut forest space. -/
def forestProgramsScratchDegree (c d Ck : ℕ) : ℕ :=
  forestScratchDegree (forestSpaceCoeff c * 8 ^ forestSpaceDeg d) (forestSpaceDeg d) Ck

/-- Linking and resource-bound core shared by `ForestConcretePrograms`,
`DyadicForestConcretePrograms`, and `DyadicWithVConcretePrograms` (`useV` selects whether
the cycle init receives `V = solverPenalty J.m` via `linkedCappedSolverProgramWithV`). -/
structure ForestConcreteProgramCore where
  useV : Bool
  edgeThreshold : ℕ
  edgeThreshold_ge_two : 2 ≤ edgeThreshold
  qualityBudget : ℕ
  cycleInit : ℕ
  cycleOp : ℕ → ℕ
  cycle : List Stmt
  cycleDeterministic : ∀ s ∈ cycle, s.NoRand
  cycleRate : ℕ → ℕ
  cycleAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ
  cycleSpace : ℕ → ℕ → ℕ
  allocationCoefficient : ℕ
  allocationDegree : ℕ
  cycleSpace_poly : ∀ n m, cycleSpace n m ≤ allocationCoefficient * (n + m + 2) ^ allocationDegree
  cycleRateExponent : ℝ
  cycleRateExponent_nonneg : 0 ≤ cycleRateExponent
  cycleRateConstant : ℝ
  cycleRateConstant_pos : 0 < cycleRateConstant
  cycleRate_subpoly : ∀ M, (cycleRate M : ℝ) ≤ cycleRateConstant * alg2TimeFactor cycleRateExponent (47 / 48) M

def ForestConcreteProgramCore.qualityLinearCoeff (P : ForestConcreteProgramCore) : ℕ :=
  concreteQualityLinearCoeff P.edgeThreshold P.qualityBudget

def ForestConcreteProgramCore.scratchDegree (P : ForestConcreteProgramCore) : ℕ :=
  forestProgramsScratchDegree P.allocationCoefficient P.allocationDegree P.qualityLinearCoeff

def ForestConcreteProgramCore.dispatch (P : ForestConcreteProgramCore) : SolverDispatch :=
  mrdsSolverDispatch P.cycleInit P.cycleOp P.cycle.length

def ForestConcreteProgramCore.forest (P : ForestConcreteProgramCore) : List Stmt :=
  dynLctForestBodies 4 (mrdsCycleBase + P.cycle.length)

def ForestConcreteProgramCore.resources (P : ForestConcreteProgramCore) : SolverForestResources where
  qualityExponent := 0
  cycleRate := P.cycleRate
  cycleAllocation := P.cycleAllocation
  cycleSpace := P.cycleSpace
  forestRate n L := lctForestRate L n
  forestAllocation w L N _ := lctForestAlloc w L N
  forestInitSpace n _ := lctArenaWords n + 10
  forestOpSpace L n _ := lctForestOpSpace L n

def ForestConcreteProgramCore.runtimeResources (P : ForestConcreteProgramCore) :
    SolverForestRuntimeResources :=
  ⟨P.resources, cappedQualityExponent P.edgeThreshold P.qualityBudget, cappedQualityCost⟩

def ForestConcreteProgramCore.solver (P : ForestConcreteProgramCore) : Program :=
  if P.useV then
    linkedCappedSolverProgramWithV P.edgeThreshold P.qualityBudget P.dispatch P.cycle P.forest
  else
    linkedCappedSolverProgram P.edgeThreshold P.qualityBudget P.dispatch P.cycle P.forest

theorem ForestConcreteProgramCore.solver_deterministic (P : ForestConcreteProgramCore) :
    P.solver.IsDeterministic := by
  unfold ForestConcreteProgramCore.solver
  split_ifs
  · exact linkedCappedSolverProgramWithV_deterministic P.edgeThreshold P.qualityBudget P.dispatch P.cycle P.forest
      P.cycleDeterministic (dynLctForestBodies_noRand 4 (mrdsCycleBase + P.cycle.length))
  · exact linkedCappedSolverProgram_deterministic P.edgeThreshold P.qualityBudget P.dispatch P.cycle P.forest
      P.cycleDeterministic (dynLctForestBodies_noRand 4 (mrdsCycleBase + P.cycle.length))

/-- Shared non-`supported` fields of `ForestConcretePrograms` and `DyadicForestConcretePrograms`.
They hold the degree-free ordered bundle chain witness, which carries no restart obligations. -/
structure ForestConcreteProgramBase where
  /-- The chain witness, given by the caller (see `ForestConcretePrograms.witness`). -/
  witness : OrderedConcreteChainWitness
  cycleInit : ℕ
  cycleOp : ℕ → ℕ
  cycle : List Stmt
  cycleDeterministic : ∀ s ∈ cycle, s.NoRand
  cycleRate : ℕ → ℕ
  cycleAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ
  cycleSpace : ℕ → ℕ → ℕ
  allocationCoefficient : ℕ
  allocationDegree : ℕ
  cycleSpace_poly : ∀ n m, cycleSpace n m ≤ allocationCoefficient * (n + m + 2) ^ allocationDegree
  cycleRateExponent : ℝ
  cycleRateExponent_nonneg : 0 ≤ cycleRateExponent
  cycleRateConstant : ℝ
  cycleRateConstant_pos : 0 < cycleRateConstant
  cycleRate_subpoly : ∀ M, (cycleRate M : ℝ) ≤ cycleRateConstant * alg2TimeFactor cycleRateExponent (47 / 48) M

def ForestConcreteProgramBase.qualityBudget (P : ForestConcreteProgramBase) : ℕ :=
  orderedConcreteQualityBudget P.witness

def ForestConcreteProgramBase.edgeThreshold (P : ForestConcreteProgramBase) : ℕ :=
  orderedConcreteEdgeThreshold P.witness

def ForestConcreteProgramBase.toCore (P : ForestConcreteProgramBase) : ForestConcreteProgramCore where
  useV := false
  edgeThreshold := P.edgeThreshold
  edgeThreshold_ge_two := orderedConcreteEdgeThreshold_ge_two P.witness
  qualityBudget := P.qualityBudget
  cycleInit := P.cycleInit
  cycleOp := P.cycleOp
  cycle := P.cycle
  cycleDeterministic := P.cycleDeterministic
  cycleRate := P.cycleRate
  cycleAllocation := P.cycleAllocation
  cycleSpace := P.cycleSpace
  allocationCoefficient := P.allocationCoefficient
  allocationDegree := P.allocationDegree
  cycleSpace_poly := P.cycleSpace_poly
  cycleRateExponent := P.cycleRateExponent
  cycleRateExponent_nonneg := P.cycleRateExponent_nonneg
  cycleRateConstant := P.cycleRateConstant
  cycleRateConstant_pos := P.cycleRateConstant_pos
  cycleRate_subpoly := P.cycleRate_subpoly

def ForestConcreteProgramBase.qualityLinearCoeff (P : ForestConcreteProgramBase) : ℕ := P.toCore.qualityLinearCoeff
def ForestConcreteProgramBase.scratchDegree (P : ForestConcreteProgramBase) : ℕ := P.toCore.scratchDegree
def ForestConcreteProgramBase.dispatch (P : ForestConcreteProgramBase) : SolverDispatch := P.toCore.dispatch
def ForestConcreteProgramBase.forest (P : ForestConcreteProgramBase) : List Stmt := P.toCore.forest
def ForestConcreteProgramBase.resources (P : ForestConcreteProgramBase) : SolverForestResources := P.toCore.resources
def ForestConcreteProgramBase.runtimeResources (P : ForestConcreteProgramBase) : SolverForestRuntimeResources := P.toCore.runtimeResources
def ForestConcreteProgramBase.solver (P : ForestConcreteProgramBase) : Program := P.toCore.solver

theorem ForestConcreteProgramBase.solver_deterministic (P : ForestConcreteProgramBase) :
    P.solver.IsDeterministic := P.toCore.solver_deterministic

/-- Monotone envelope of `forestConnectedSolverRuntimeTime`. -/
def linkedForestSolverTime (r : SolverForestRuntimeResources) (n m : ℕ) : ℕ :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (m + 1))).sup
    fun nm => forestConnectedSolverRuntimeTime r nm.1 nm.2

theorem forestConnectedSolverRuntimeTime_le_linkedForestSolverTime
    (r : SolverForestRuntimeResources) (n m : ℕ) :
    forestConnectedSolverRuntimeTime r n m ≤ linkedForestSolverTime r n m := by
  unfold linkedForestSolverTime
  apply Finset.le_sup (b := (n, m)) (f := fun nm => forestConnectedSolverRuntimeTime r nm.1 nm.2)
  simp

theorem linkedForestSolverTime_mono (r : SolverForestRuntimeResources) :
    SolverTimeMonotone (linkedForestSolverTime r) := by
  intro n n' m m' hn hm
  apply Finset.sup_mono
  exact Finset.product_subset_product (Finset.range_mono (by omega)) (Finset.range_mono (by omega))

/-- Core linked solver contract verification shared by `useV = false` (`linkedCappedSolverProgram`)
and `useV = true` (`linkedCappedSolverProgramWithV`). -/
theorem ForestConcreteProgramCore.solver_meetsContract_of
    (P : ForestConcreteProgramCore) (J : Circulation)
    (cycleModel : Circulation → MinRatioDataStructureWithFailure)
    (hSupported : ∀ (J' : Circulation), J'.n ≤ 2 * J'.m + 1 → 0 < J'.m → J'.CostsBounded (J'.m ^ 10) →
      (∀ e, 1 ≤ J'.capacity e ∧ J'.capacity e ≤ J'.m ^ 40) →
      let I := solverConnectedAugmented J'
      let V := solverPenalty J'.m
      let k := cappedQualityExponent P.edgeThreshold P.qualityBudget I.m
      MinRatioSpecWithFailureEdgeOnlyConnectedUpTo (cycleModel J')
        (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
        ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
        ((1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024) I.m I.n ∧
      ∀ hw : ipmQualityParameterWordBits I.m V k ≤
          wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords,
        ∃ RC : DSRep (cycleModel J').State,
          RC.Implements (wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords)
            P.solver P.cycleInit P.cycleOp
            (if P.useV then
              minRatioMachineContractWithV (ipmQualityMinRatioFormat I.m V k hw)
                (cycleModel J') (namedInstance I) I.m V
                (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
                P.cycleRate (P.cycleAllocation I.n I.m)
            else
              minRatioMachineContract (ipmQualityMinRatioFormat I.m V k hw)
                (cycleModel J') (namedInstance I) I.m
                (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
                P.cycleRate (P.cycleAllocation I.n I.m)) ∧
          (∀ j < 4, ∀ args, P.cycleAllocation I.n I.m j args ≤ P.cycleSpace I.n I.m)) :
    let w := wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords
    MeetsContract w P.solver 0 (compressedSolverContract w
      (forestConnectedSolverRuntimeTime P.runtimeResources)
      (forestConnectedSolverRuntimeWorkspace P.runtimeResources)) := by
  dsimp only
  let w := wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords
  have hw : 2 < 2 ^ w := by
    have hc : 1 ≤ scratchWordMultiplier 1 P.scratchDegree := by
      unfold scratchWordMultiplier; omega
    have hBase : 2 ≤ J.solverWords.length + J.solverWords.foldr max 0 + 2 := by omega
    exact (hBase.trans (Nat.le_self_pow (by omega) _)).trans_lt
      (pow_lt_two_pow_wordSize hc J.solverWords)
  have hQuality : P.dispatch.quality = linkedConnectedQualityBase P.dispatch P.cycle P.forest + 2 := by
    unfold ForestConcreteProgramCore.dispatch mrdsSolverDispatch linkedConnectedQualityBase ForestConcreteProgramCore.forest
    rw [boundedConnectedIPMRuntimeModule_length]
  let forestBase := mrdsCycleBase + P.cycle.length
  have hForestImp_of : ∀ (prog : Program),
      prog.HasAt forestBase (dynLctForestBodies 4 forestBase) →
      ∀ (J' : Circulation)
        (hwJ : ipmQualityParameterWordBits (solverConnectedAugmented J').m (solverPenalty J'.m)
          (cappedQualityExponent P.edgeThreshold P.qualityBudget (solverConnectedAugmented J').m) ≤ w),
        let I := solverConnectedAugmented J'
        let V := solverPenalty J'.m
        let k := cappedQualityExponent P.edgeThreshold P.qualityBudget I.m
        let L := ipmQualityLimbs I.m V k
        let Q := ipmQualityPrecision I.m V k
        (lctForestRep w 4 L Q I.n).Implements w prog forestBase (lctForestOp forestBase)
          (forestMachineContract lctForestModel w 4 L Q (lctForestRate L) (lctForestAlloc w L I.n)) := by
    intro prog hProg_has J' hwJ I V k L Q
    have hFit := ipm_quality_parameter_words_fit I.m V k hwJ
    exact dynLctForest_implements (by decide : 0 < 4) (by have := hFit.1; omega) hFit.2.1 hFit.2.2.1 hProg_has
  cases hV : P.useV
  · simp only [ForestConcreteProgramCore.solver, hV, Bool.false_eq_true, ↓reduceIte]
    change MeetsContract w (linkedCappedSolverProgram P.edgeThreshold P.qualityBudget P.dispatch P.cycle P.forest) 0
      (compressedSolverContract w
        (forestConnectedSolverRuntimeTime ⟨P.resources, cappedQualityExponent P.edgeThreshold P.qualityBudget, cappedQualityCost⟩)
        (forestConnectedSolverRuntimeWorkspace ⟨P.resources, cappedQualityExponent P.edgeThreshold P.qualityBudget, cappedQualityCost⟩))
    refine linkedCappedSolverProgram_meetsForestContract w P.edgeThreshold P.qualityBudget P.resources
      P.dispatch P.cycle P.forest lctForestModel lctForestModel_isSpec hw hQuality ?_
    intro J' hJn hm hCost hCap
    dsimp only
    intro hwJ
    let I := solverConnectedAugmented J'
    let V := solverPenalty J'.m
    let k := cappedQualityExponent P.edgeThreshold P.qualityBudget I.m
    obtain ⟨hMod, hSup⟩ := hSupported J' hJn hm hCost hCap
    obtain ⟨RC, hCycle, hCBound⟩ := hSup hwJ
    simp only [ForestConcreteProgramCore.solver, hV, Bool.false_eq_true, ↓reduceIte] at hCycle
    let prog := linkedCappedSolverProgram P.edgeThreshold P.qualityBudget P.dispatch P.cycle P.forest
    have hProg_has : prog.HasAt forestBase (dynLctForestBodies 4 forestBase) := by
      let b := linkedConnectedQualityBase P.dispatch P.cycle P.forest
      have hall := hasAt_self (boundedConnectedIPMRuntimeModule 0 P.dispatch ++ P.cycle ++ P.forest ++
        [Num.IPM.bitLengthBody b, integerQualityBody b P.qualityBudget,
         cappedQualityBody (b + 1) P.qualityBudget P.edgeThreshold])
      have hpre := Num.hasAt_append_right (Num.hasAt_append_left hall)
      rw [Nat.zero_add, List.length_append, boundedConnectedIPMRuntimeModule_length] at hpre
      exact hpre
    let L := ipmQualityLimbs I.m V k
    let Q := ipmQualityPrecision I.m V k
    refine ⟨cycleModel J', RC, lctForestRep w 4 L Q I.n, {
      cycleModel := hMod
      cycleMachine := hCycle
      cycleBound := hCBound
      forestMachine := hForestImp_of prog hProg_has J' hwJ
      forestInitBound := fun b => by
        change lctForestAlloc w L I.n 6 [I.n, L, Q, b] ≤ lctArenaWords I.n + 10
        simp [lctForestAlloc]
      forestOpBound := fun j hj args => by
        change lctForestAlloc w L I.n j args ≤ lctForestOpSpace L I.n
        simp [lctForestAlloc, show j ≠ 6 by omega] }⟩
  · simp only [ForestConcreteProgramCore.solver, hV, ↓reduceIte]
    change MeetsContract w (linkedCappedSolverProgramWithV P.edgeThreshold P.qualityBudget P.dispatch P.cycle P.forest) 0
      (compressedSolverContract w
        (forestConnectedSolverRuntimeTime ⟨P.resources, cappedQualityExponent P.edgeThreshold P.qualityBudget, cappedQualityCost⟩)
        (forestConnectedSolverRuntimeWorkspace ⟨P.resources, cappedQualityExponent P.edgeThreshold P.qualityBudget, cappedQualityCost⟩))
    refine linkedCappedSolverProgramWithV_meetsForestContract w P.edgeThreshold P.qualityBudget P.resources
      P.dispatch P.cycle P.forest lctForestModel lctForestModel_isSpec hw hQuality ?_
    intro J' hJn hm hCost hCap
    dsimp only
    intro hwJ
    let I := solverConnectedAugmented J'
    let V := solverPenalty J'.m
    let k := cappedQualityExponent P.edgeThreshold P.qualityBudget I.m
    obtain ⟨hMod, hSup⟩ := hSupported J' hJn hm hCost hCap
    obtain ⟨RC, hCycle, hCBound⟩ := hSup hwJ
    simp only [ForestConcreteProgramCore.solver, hV, ↓reduceIte] at hCycle
    let prog := linkedCappedSolverProgramWithV P.edgeThreshold P.qualityBudget P.dispatch P.cycle P.forest
    have hProg_has : prog.HasAt forestBase (dynLctForestBodies 4 forestBase) := by
      let b := linkedConnectedQualityBase P.dispatch P.cycle P.forest
      have hall := hasAt_self (boundedConnectedIPMRuntimeModuleWithV 0 P.dispatch ++ P.cycle ++ P.forest ++
        [Num.IPM.bitLengthBody b, integerQualityBody b P.qualityBudget,
         cappedQualityBody (b + 1) P.qualityBudget P.edgeThreshold])
      have hpre := Num.hasAt_append_right (Num.hasAt_append_left hall)
      rw [Nat.zero_add, List.length_append, boundedConnectedIPMRuntimeModuleWithV_length] at hpre
      exact hpre
    let L := ipmQualityLimbs I.m V k
    let Q := ipmQualityPrecision I.m V k
    refine ⟨cycleModel J', RC, lctForestRep w 4 L Q I.n, {
      cycleModel := hMod
      cycleMachine := hCycle
      cycleBound := hCBound
      forestMachine := hForestImp_of prog hProg_has J' hwJ
      forestInitBound := fun b => by
        change lctForestAlloc w L I.n 6 [I.n, L, Q, b] ≤ lctArenaWords I.n + 10
        simp [lctForestAlloc]
      forestOpBound := fun j hj args => by
        change lctForestAlloc w L I.n j args ≤ lctForestOpSpace L I.n
        simp [lctForestAlloc, show j ≠ 6 by omega] }⟩

theorem ForestConcreteProgramBase.solver_meetsContract_of
    (P : ForestConcreteProgramBase) (J : Circulation)
    (cycleModel : Circulation → MinRatioDataStructureWithFailure)
    (hModel : ∀ (J' : Circulation), J'.n ≤ 2 * J'.m + 1 → 0 < J'.m → (∀ e, 1 ≤ J'.capacity e) →
      let I := solverConnectedAugmented J'
      let V := solverPenalty J'.m
      let k := cappedQualityExponent P.edgeThreshold P.qualityBudget I.m
      MinRatioSpecWithFailureEdgeOnlyConnectedUpTo (cycleModel J')
        (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
        ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
        ((1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024) I.m I.n)
    (hSupported : ∀ (J' : Circulation), J'.n ≤ 2 * J'.m + 1 → 0 < J'.m → J'.CostsBounded (J'.m ^ 10) →
      (∀ e, 1 ≤ J'.capacity e ∧ J'.capacity e ≤ J'.m ^ 40) →
      let I := solverConnectedAugmented J'
      let V := solverPenalty J'.m
      let k := cappedQualityExponent P.edgeThreshold P.qualityBudget I.m
      ∀ hw : ipmQualityParameterWordBits I.m V k ≤
          wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords,
        ∃ RC : DSRep (cycleModel J').State,
          RC.Implements (wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords)
            P.solver P.cycleInit P.cycleOp
            (minRatioMachineContract (ipmQualityMinRatioFormat I.m V k hw)
              (cycleModel J') (namedInstance I) I.m
              (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
              P.cycleRate (P.cycleAllocation I.n I.m)) ∧
          (∀ j < 4, ∀ args, P.cycleAllocation I.n I.m j args ≤ P.cycleSpace I.n I.m)) :
    let w := wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords
    MeetsContract w P.solver 0 (compressedSolverContract w
      (forestConnectedSolverRuntimeTime P.runtimeResources)
      (forestConnectedSolverRuntimeWorkspace P.runtimeResources)) := by
  refine P.toCore.solver_meetsContract_of J cycleModel ?_
  intro J' hJn hm hCost hCap
  have hp : ∀ e, 1 ≤ J'.capacity e := fun e => (hCap e).1
  exact ⟨hModel J' hJn hm hp, fun hwJ => hSupported J' hJn hm hCost hCap hwJ⟩

/-- Polynomial scratch reservation bound covering both the min-ratio cycle module and the dynamic link-cut forest. -/
theorem ForestConcreteProgramCore.workspace_le (P : ForestConcreteProgramCore) (n m : ℕ) :
    forestConnectedSolverRuntimeWorkspace P.runtimeResources n m ≤ (n + m + 2) ^ P.scratchDegree := by
  let c' := forestSpaceCoeff P.allocationCoefficient
  let d' := forestSpaceDeg P.allocationDegree
  have hc' : P.allocationCoefficient ≤ c' := le_max_left _ _
  have hc2 : 2000000 ≤ c' := le_max_right _ _
  have hd' : P.allocationDegree ≤ d' := le_max_left _ _
  have hd2 : 2 ≤ d' := le_max_right _ _
  have hB1 : 1 ≤ n + m + 2 := by omega
  have h8d : 64 ≤ 8 ^ d' := by
    calc 64 = 8 ^ 2 := by decide
      _ ≤ 8 ^ d' := Nat.pow_le_pow_right (by decide) hd2
  refine connectedForestIPMRuntimeWorkspace_polynomial P.runtimeResources n m (c' * 8 ^ d') d'
    P.qualityLinearCoeff (fun M => cappedQuality_linear_spec P.edgeThreshold P.qualityBudget M) ?_ ?_ ?_
  · intro M hM
    have hMle : M ≤ 7 * m := (Finset.mem_Icc.mp hM).2
    have hsum : n + 1 + M + 2 ≤ 8 * (n + m + 2) := by omega
    calc P.cycleSpace (n + 1) M
        ≤ P.allocationCoefficient * (n + 1 + M + 2) ^ P.allocationDegree := P.cycleSpace_poly (n + 1) M
      _ ≤ c' * (n + 1 + M + 2) ^ d' :=
          Nat.mul_le_mul hc' (Nat.pow_le_pow_right (by omega) hd')
      _ ≤ c' * (8 * (n + m + 2)) ^ d' :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum d')
      _ = (c' * 8 ^ d') * (n + m + 2) ^ d' := by rw [Nat.mul_pow, mul_assoc]
  · intro _ _
    have hA : lctArenaWords (n + 1) + 10 ≤ 128 * (n + 2) := lctArenaWords_bound n
    have hn2 : n + 2 ≤ (n + m + 2) ^ d' := by
      calc n + 2 ≤ (n + m + 2) ^ 1 := by simp
        _ ≤ (n + m + 2) ^ d' := Nat.pow_le_pow_right hB1 (by omega)
    have hcoeff : 128 ≤ c' * 8 ^ d' := by nlinarith
    calc P.resources.forestInitSpace (n + 1) _ = lctArenaWords (n + 1) + 10 := rfl
      _ ≤ 128 * (n + 2) := hA
      _ ≤ (c' * 8 ^ d') * (n + m + 2) ^ d' := Nat.mul_le_mul hcoeff hn2
  · intro M _
    let L := ipmQualityLimbs M (solverPenalty m) (P.runtimeResources.qualityExponent M)
    have hOp := lctForestOpSpace_bound L (n + 1)
    have hsq : (n + 1 + 2) ^ 2 ≤ 4 * (n + m + 2) ^ d' := by
      have h1 : n + 1 + 2 ≤ 2 * (n + m + 2) := by omega
      have h2 : (n + m + 2) ^ 2 ≤ (n + m + 2) ^ d' := Nat.pow_le_pow_right hB1 hd2
      calc (n + 1 + 2) ^ 2 ≤ (2 * (n + m + 2)) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = 4 * (n + m + 2) ^ 2 := by ring
        _ ≤ 4 * (n + m + 2) ^ d' := Nat.mul_le_mul_left 4 h2
    have hc4 : 2000000 * 4 ≤ c' * 8 ^ d' := by nlinarith
    calc P.resources.forestOpSpace L (n + 1) M = lctForestOpSpace L (n + 1) := rfl
      _ ≤ 2000000 * (L + 1) * (n + 1 + 2) ^ 2 := hOp
      _ ≤ 2000000 * (L + 1) * (4 * (n + m + 2) ^ d') := Nat.mul_le_mul_left _ hsq
      _ = (2000000 * 4) * (L + 1) * (n + m + 2) ^ d' := by ring
      _ ≤ (c' * 8 ^ d') * (L + 1) * (n + m + 2) ^ d' :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc4)

theorem ForestConcreteProgramBase.workspace_le (P : ForestConcreteProgramBase) (n m : ℕ) :
    forestConnectedSolverRuntimeWorkspace P.runtimeResources n m ≤ (n + m + 2) ^ P.scratchDegree :=
  P.toCore.workspace_le n m

def ForestConcreteProgramCore.program (P : ForestConcreteProgramCore) : Program :=
  scratchOuterScalingProgram P.solver 0 1 P.scratchDegree

theorem ForestConcreteProgramCore.program_deterministic (P : ForestConcreteProgramCore) :
    P.program.IsDeterministic :=
  scratchOuterScalingProgram_deterministic _ _ _ _ P.solver_deterministic

def ForestConcreteProgramCore.timeConstant (P : ForestConcreteProgramCore) : ℕ :=
  scratchWholeScalingConstant P.solver 1 P.scratchDegree

theorem ForestConcreteProgramCore.program_runsTo_of (P : ForestConcreteProgramCore)
    (hSol : ∀ J : Circulation,
      let w := wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords
      MeetsContract w P.solver 0 (compressedSolverContract w
        (forestConnectedSolverRuntimeTime P.runtimeResources)
        (forestConnectedSolverRuntimeWorkspace P.runtimeResources)))
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost,
      RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧
      cost ≤ P.timeConstant * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (I.maxCapacity + 1) + 1) * Nat.clog 2 (I.maxCost + 2) *
        (linkedForestSolverTime P.runtimeResources (P.timeConstant * min I.n I.m) (P.timeConstant * I.m) + I.m) +
        P.timeConstant * I.n := by
  apply outerScaling_runsTo_compressedPolynomialScratch P.solver 0
    (linkedForestSolverTime P.runtimeResources) (forestConnectedSolverRuntimeWorkspace P.runtimeResources)
    1 P.scratchDegree
  · intro J
    exact solverContract_raise_time (hSol J)
      (forestConnectedSolverRuntimeTime_le_linkedForestSolverTime P.runtimeResources)
  · intro n m
    simpa only [Nat.one_mul] using P.workspace_le n m
  · exact P.solver_deterministic
  · exact linkedForestSolverTime_mono P.runtimeResources
  · exact hv

def ForestConcreteProgramBase.program (P : ForestConcreteProgramBase) : Program := P.toCore.program

theorem ForestConcreteProgramBase.program_deterministic (P : ForestConcreteProgramBase) :
    P.program.IsDeterministic := P.toCore.program_deterministic

def ForestConcreteProgramBase.timeConstant (P : ForestConcreteProgramBase) : ℕ := P.toCore.timeConstant

theorem ForestConcreteProgramBase.program_runsTo_of (P : ForestConcreteProgramBase)
    (hSol : ∀ J : Circulation,
      let w := wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords
      MeetsContract w P.solver 0 (compressedSolverContract w
        (forestConnectedSolverRuntimeTime P.runtimeResources)
        (forestConnectedSolverRuntimeWorkspace P.runtimeResources)))
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost,
      RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧
      cost ≤ P.timeConstant * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (I.maxCapacity + 1) + 1) * Nat.clog 2 (I.maxCost + 2) *
        (linkedForestSolverTime P.runtimeResources (P.timeConstant * min I.n I.m) (P.timeConstant * I.m) + I.m) +
        P.timeConstant * I.n :=
  P.toCore.program_runsTo_of hSol I hv ω

end MinCostFlow.Final
