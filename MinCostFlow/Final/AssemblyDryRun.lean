module

public import MinCostFlow.Final.AssemblyDryRunWitness
public import MinCostFlow.Final.AssemblyDryRunSolver
public import MinCostFlow.Final.SparsifyImplHyp
public import MinCostFlow.Final.Theorem1_1
public import MinCostFlow.SparseCore.Program.LSFWindowSpec
import Mathlib.Tactic

/-!
# Dry run of the final assembly of Theorem 1.1

Theorem 1.1 (page 2) follows from one value of the package `DyadicWithVConcretePrograms` by
`theorem_1_1_of_dyadic_withV_mrds_programs`. This file builds such a value, `dryPrograms`, from
the objects of the library and a short list of hypotheses on the parts that it does not build.
Then `theorem_1_1_dry_run` derives `MinCostFlowStatement` from those hypotheses. The later files
of `MinCostFlow/Final/` use the definitions of this file on the way to `theorem_1_1_proved`
(`Final/Theorem11Goals.lean`).

The fields are filled as follows.
* `lastTool`, `lastConstant`, `lastSpec`: the fixed-point tool of the last-level program
  (`Final/AssemblyDryRunWitness.lean`).
* `witness`: `dryWitnessUsed`, by `concreteChainWitnessWithLastOf`, with the library's canonical
  LSF initializer family `SparseCore.Program.canonicalLSFInit` (`canonicalLSFInit_spec`, P3) and
  `canonicalSparsify sparsifyImplUsed` (`sparsifyImplHyp_sparsifyImplUsed`, Algorithm 4, page 42).
* `cycleInit`, `cycleOp`, `cycle`, `cycleDeterministic`: `solverCycleInit` (`solverTailBase`),
  `solverOpsDispatch mrdsCycleBase`, and `dryCycle` (the 183 operation procedures `solverOpsProcs`
  at `mrdsCycleBase`, followed by `solverTail` at `solverTailBase` containing the 12 wired and
  helper bodies, the real relocated last-level bodies `packedLastLevelBodies`, the shifted
  sparse-core program `sc`, and the inner-level bodies `inner`).
* `cycleRate`, `cycleAllocation`, `cycleSpace` and their bounds: those of
  `OrdSolverInnerBounds` (`MinRatio/OrdSolverRateBounds.lean`) for given inner bounds `B`, with
  the rate constants chosen from `cycleRate_subpoly` and the allocation coefficient bumped by
  `dryWordCoeff` (from `concrete_solver_word_bounds_poly`) and `drySparseCoreWordCoeff` (from
  `concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize`) to discharge the shift-quota,
  `4 * M₀ + 3`, and sparse-core `(levelM i + N₀ + 2) ^ wordExp * (F.limbs + 1) < 2 ^ w` bounds.
* `supported`: `supported_of_wiredSpecs` (through `ordSolver_supported_full_wired` and
  `ordSolver_implements_full_wired`), using `SparseCoreOrdProgramUniform` at `capExp = 3` and
  `limbMul = concreteReadout2LimbMul dryWitnessUsed`, discharging `DrySparseCoreCapLevels` and
  `DrySparseCoreWordBound` (given `hWordExp : drySparseCoreWordExp hSC 3 ≤ 39`).

The hypotheses of `theorem_1_1_dry_run` are:
1. the external sparse-core code `sc` (`NoRand`), `hSC` (`SparseCoreOrdProgramUniform`), and
   `hWordExp : drySparseCoreWordExp hSC dryCapExp ≤ 39`;
2. the external inner-level code `inner` (`NoRand`);
3. the inner bounds `B` with `hB : InnerBoundsHyp B` and per-input sizes
   `sz : Circulation → Circulation → WiredInnerSizes`;
4. the six corrected inner `W` specs: `hInit` (`OrdInitConcreteSpecW`), `hCore`
   (`OrdChainUpdateCoreSpecW`), `hSelect` (`OrdCycleRouteSelectSpecW`), `hEval`
   (`OrdCycleRouteEvalSpecW`), `hTerm` (`ShiftTermChainSyncSpecW`), and `hDeep`
   (`ShiftDeepChainSyncSpecW`);
5. the per-input numeric and envelope bounds: `hCapBounds` (`DryFixedPointCapBounds`)
   and `hEnv` (`DryContractEnvelope`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM SparseCore SparseCore.Program DynSpanner.Program Chain MinRatio

/-- What the rate and the space of the solver need from the inner bounds `B`: the hypotheses of
`OrdSolverInnerBounds.cycleRate_subpoly` and `OrdSolverInnerBounds.cycleSpace_poly`. -/
def InnerBoundsHyp (B : OrdSolverInnerBounds) : Prop :=
  (SubpolyNat B.limbs ∧ SubpolyNat (fun M => Nat.log 2 (2 * B.verts M + 1)) ∧
      SubpolyNat (fun M => B.initBudget M / (M + 1)) ∧ SubpolyNat B.updateRate) ∧
    (PolyNat B.limbs ∧ PolyNat B.names ∧ PolyNat B.initSpace ∧ PolyNat B.updateSpace)

section Constants

variable (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)

/-- The rate constant, chosen from `cycleRate_subpoly`. It depends only on `B`. -/
def dryRateConstant : ℝ :=
  Classical.choose (B.cycleRate_subpoly hB.1.1 hB.1.2.1 hB.1.2.2.1 hB.1.2.2.2)

/-- The rate exponent, chosen from `cycleRate_subpoly`. It depends only on `B`. -/
def dryRateExponent : ℝ :=
  Classical.choose (Classical.choose_spec
    (B.cycleRate_subpoly hB.1.1 hB.1.2.1 hB.1.2.2.1 hB.1.2.2.2))

theorem dryRate_spec :
    0 < dryRateConstant B hB ∧ 0 ≤ dryRateExponent B hB ∧
      ∀ M, (B.cycleRate M : ℝ) ≤
        dryRateConstant B hB * alg2TimeFactor (dryRateExponent B hB) (47 / 48) M :=
  Classical.choose_spec (Classical.choose_spec
    (B.cycleRate_subpoly hB.1.1 hB.1.2.1 hB.1.2.2.1 hB.1.2.2.2))

/-- The allocation coefficient, chosen from `cycleSpace_poly`. It depends only on `B`. -/
def dryAllocCoeff : ℕ :=
  Classical.choose (B.cycleSpace_poly hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2)

/-- The allocation degree, chosen from `cycleSpace_poly`. It depends only on `B`. -/
def dryAllocDeg : ℕ :=
  Classical.choose (Classical.choose_spec
    (B.cycleSpace_poly hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2))

theorem dryAlloc_spec :
    ∀ n m, B.cycleSpace n m ≤ dryAllocCoeff B hB * (n + m + 2) ^ dryAllocDeg B hB :=
  Classical.choose_spec (Classical.choose_spec
    (B.cycleSpace_poly hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2))

end Constants

/-- The constant `C_sp` of the sparsifier program `sparsifyImplUsed`, chosen from
`sparsifyImplHyp_sparsifyImplUsed`. -/
def dryCSp : ℝ := Classical.choose sparsifyImplHyp_sparsifyImplUsed

theorem dryImplHyp : SparsifyImplHyp sparsifyImplUsed dryCSp :=
  Classical.choose_spec sparsifyImplHyp_sparsifyImplUsed

/-- The library's canonical LSF initializer family (`SparseCore.Program.canonicalLSFInit`)
instantiated on the `[AN19]` program `anProgram`. -/
def dryLSFInitUsed : ℕ → ℕ → LSFInit :=
  dryLSFInit SparseCore.Program.canonicalLSFInit

/-- Explicit value of `lemma55RhoConst anK` (`= 59045924790352281600`). -/
theorem anRhoConst_eq :
    MinCostFlow.LSF.Program.lemma55RhoConst anK = 59045924790352281600 := by
  unfold MinCostFlow.LSF.Program.lemma55RhoConst
  rw [anDefaultK_sigma_eq]

/-- Explicit upper bound `Nat.log 2 (lemma55RhoConst anK + 1) ≤ 65` on the constant term in
`canonLw anK`. -/
theorem anRhoConstLog_le :
    Nat.log 2 (MinCostFlow.LSF.Program.lemma55RhoConst anK + 1) ≤ 65 := by
  rw [anRhoConst_eq]
  have hlt : 59045924790352281600 + 1 < 2 ^ 66 := by norm_num
  have hlog := Nat.log_lt_of_lt_pow (by norm_num) hlt
  omega

/-- Concrete bound on P3's canonical stretch limb width `canonLw anK` with the `anK` term
eliminated (`Nat.log 2 (lemma55RhoConst anK + 1) + 8 ≤ 73`). -/
theorem canonLw_anK_le (L_in n0 k_nat : ℕ) :
    canonLw anK L_in n0 k_nat ≤
      L_in + Nat.log 2 (k_nat + 1) + 6 * Nat.log 2 (Nat.log 2 (n0 + 2) + 2) + 73 := by
  unfold canonLw
  have h := anRhoConstLog_le
  omega

/-- P3's canonical stretch limb width `canonLw anK` fits within the readout-2 limb budget
`L_in + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)` whenever `n0 ≤ N`
and `k_nat ≤ (M + N + 2) ^ capExp`. -/
theorem canonLw_anK_le_readout2 {L_in n0 k_nat M N capExp : ℕ}
    (hn : n0 ≤ N) (hk : k_nat ≤ (M + N + 2) ^ capExp) :
    canonLw anK L_in n0 k_nat ≤
      L_in + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) := by
  set B := M + N + 2
  set d := Nat.log 2 B + 1
  have hB2 : 2 ≤ B := by omega
  have hd1 : 1 ≤ d := by omega
  have hB_lt : B < 2 ^ d := Nat.lt_pow_succ_log_self (by decide) B
  have hk_log : Nat.log 2 (k_nat + 1) ≤ capExp * d + 1 := by
    have hpow_le : B ^ capExp ≤ (2 ^ d) ^ capExp := Nat.pow_le_pow_left hB_lt.le capExp
    have hpow_pos : 1 ≤ (2 ^ d) ^ capExp := Nat.one_le_pow _ _ (by positivity)
    have h1 : k_nat + 1 < 2 ^ (capExp * d + 2) := by
      have h3 : (2 ^ d) ^ capExp = 2 ^ (capExp * d) := by
        rw [← pow_mul, mul_comm]
      have h4 : 2 ^ (capExp * d + 2) = 4 * 2 ^ (capExp * d) := by
        rw [pow_succ, pow_succ]; ring
      omega
    have hlt := Nat.log_lt_of_lt_pow (by omega) h1
    omega
  have hn_log : Nat.log 2 (Nat.log 2 (n0 + 2) + 2) ≤ d := by
    have hle1 : Nat.log 2 (n0 + 2) ≤ Nat.log 2 B := Nat.log_mono_right (by omega)
    have hlog_le_self : Nat.log 2 B ≤ B := Nat.log_le_self 2 B
    have hlt2 : Nat.log 2 (n0 + 2) + 2 < 2 ^ (d + 1) := by
      have h4 : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ, mul_comm]
      omega
    have hlt := Nat.log_lt_of_lt_pow (by omega) hlt2
    omega
  have hbase := canonLw_anK_le L_in n0 k_nat
  have h74 : 74 ≤ 74 * d := Nat.le_mul_of_pos_right 74 hd1
  have h128 : (capExp + 80) * d ≤ (capExp + sparseCoreReadout2LimbConst) * d := by
    unfold sparseCoreReadout2LimbConst
    exact Nat.mul_le_mul_right d (by omega)
  have hexp : capExp * d + 6 * d + 74 * d = (capExp + 80) * d := by ring
  omega

/-- The uniform LSST constant `C_lsst` of `dryLSFInitUsed`, proved from
`SparseCore.Program.canonicalLSFInit_spec`. -/
def dryCLsstUsed : ℝ :=
  dryCLsst SparseCore.Program.canonicalLSFInit SparseCore.Program.canonicalLSFInit_spec

/-- The complete concrete chain witness built entirely from library theorems: `dryLastTool`,
`SparseCore.Program.canonicalLSFInit` (P3), and `sparsifyImplUsed` (Algorithm 4). -/
def dryWitnessUsed : ConcreteChainWitnessWithLast dryLastTool dryLastConstant dryLastSpec :=
  dryWitness SparseCore.Program.canonicalLSFInit SparseCore.Program.canonicalLSFInit_spec
    sparsifyImplUsed dryCSp dryImplHyp

/-- The witness-only word-size coefficient covering `hQuotaBoundW` and `4 * cfg.P.M₀ + 3 < 2 ^ w`. -/
def dryWordCoeff : ℕ :=
  Classical.choose (concrete_solver_word_bounds_poly dryWitnessUsed)

/-- The witness-only word-size coefficient covering
`(levelM i + N₀ + 2) ^ wordExp * (L + 1) < 2 ^ w` for every `wordExp ≤ 39` and every limb count
within `concreteReadout2LimbMul dryWitnessUsed`. -/
def drySparseCoreWordCoeff : ℕ :=
  Classical.choose (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed)

/-- Allocation coefficient bumped by `dryWordCoeff` and `drySparseCoreWordCoeff` so that
`cycleSpace_poly`, `concrete_solver_word_bounds_poly`, and
`concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize` all hold simultaneously. -/
def dryAllocCoeffFull (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B) : ℕ :=
  max (max (dryAllocCoeff B hB) dryWordCoeff) drySparseCoreWordCoeff

theorem dryAllocFull_spec (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B) :
    ∀ n m, B.cycleSpace n m ≤ dryAllocCoeffFull B hB * (n + m + 2) ^ dryAllocDeg B hB :=
  fun n m => (dryAlloc_spec B hB n m).trans
    (Nat.mul_le_mul_right _ ((le_max_left _ _).trans (le_max_left _ _)))

section Package

variable (sc : SparseCoreCode) (hsc : sc.prog.IsDeterministic)
  (hSC : SparseCoreOrdProgramUniform dryCLsstUsed dryLSFInitUsed sparsifyImplUsed
    sc.prog sc.init sc.op)
  (hWordExp : drySparseCoreWordExp hSC dryCapExp ≤ 39)
  (inner : SolverInnerCode) (hinner : inner.IsDeterministic)
  (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
  (stretchPrec : Scaling.Circulation → ℕ)
  (DeepInv : ∀ J, ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
    (concreteCirculationCfgWithLast dryWitnessUsed J).P → Prop)
  (hDeepInv : DryDeepShiftInv dryWitnessUsed sparsifyImplUsed sc hSC
    (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
    (concreteReadout2LimbMul dryWitnessUsed) stretchPrec DeepInv)
  (sz : Scaling.Circulation → Scaling.Circulation → WiredInnerSizes)
  (hInit : DryInitSpecW dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC inner
    (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
    (concreteReadout2LimbMul dryWitnessUsed) sz)
  (hCore : DryChainUpdateCoreSpecW dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC inner
    (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
    (concreteReadout2LimbMul dryWitnessUsed) sz)
  (hSelect : DryCycleRouteSelectSpecW dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC inner
    (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
    (concreteReadout2LimbMul dryWitnessUsed) sz)
  (hEval : DryCycleRouteEvalSpecW dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC inner
    (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
    (concreteReadout2LimbMul dryWitnessUsed) sz)
  (hTerm : DryShiftTermSpecW dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC inner
    (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
    (concreteReadout2LimbMul dryWitnessUsed) sz)
  (hDeep : DryShiftDeepSpecW dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC inner
    (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
    (concreteReadout2LimbMul dryWitnessUsed) stretchPrec sz)
  (hCapBounds : DryFixedPointCapBounds dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) sz)
  (hEnv : DryContractEnvelope dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC
    B.cycleRate B.cycleAllocation (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
    (concreteReadout2LimbMul dryWitnessUsed) sz)

/-- **The package of the dry run.** Every field is filled from the library and the hypotheses
of this section (`SparseCoreOrdProgramUniform` with `wordExp ≤ 39`, the six corrected inner `W`
specs, `DryFixedPointCapBounds`, and `DryContractEnvelope`). Both `DrySparseCoreCapLevels` (at
`capExp = 3`, `limbMul = concreteReadout2LimbMul dryWitnessUsed`) and `DrySparseCoreWordBound`
are discharged automatically. -/
def dryPrograms : DyadicWithVConcretePrograms where
  lastTool := dryLastTool
  lastConstant := dryLastConstant
  lastSpec := dryLastSpec
  witness := dryWitnessUsed
  cycleInit := solverCycleInit
  cycleOp := solverOpsDispatch mrdsCycleBase
  cycle := dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) sc inner
  cycleDeterministic := dryCycle_noRand _ _ hsc hinner
  cycleRate := B.cycleRate
  cycleAllocation := B.cycleAllocation
  cycleSpace := B.cycleSpace
  allocationCoefficient := dryAllocCoeffFull B hB
  allocationDegree := dryAllocDeg B hB
  cycleSpace_poly := dryAllocFull_spec B hB
  cycleRateExponent := dryRateExponent B hB
  cycleRateExponent_nonneg := (dryRate_spec B hB).2.1
  cycleRateConstant := dryRateConstant B hB
  cycleRateConstant_pos := (dryRate_spec B hB).1
  cycleRate_subpoly := (dryRate_spec B hB).2.2
  supported := supported_of_wiredSpecs dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC hWordExp
    inner B (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
    ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _) stretchPrec DeepInv hDeepInv sz
    hInit hCore hSelect hEval hTerm hDeep hCapBounds hEnv

end Package

/-- **Theorem 1.1 (page 2), dry run.** `MinCostFlowStatement` follows from the sparse-core uniform
statement (`hSC`, with `hWordExp : drySparseCoreWordExp hSC 3 ≤ 39`), the six corrected inner `W`
specs (`hInit`, `hCore`, `hSelect`, `hEval`, `hTerm`, `hDeep`), `hCapBounds`, and `hEnv`, through
`ordSolver_implements_full_wired` and `theorem_1_1_of_dyadic_withV_mrds_programs`. Both
`DrySparseCoreCapLevels` and `DrySparseCoreWordBound` are discharged automatically. -/
theorem theorem_1_1_dry_run
    (sc : SparseCoreCode) (hsc : sc.prog.IsDeterministic)
    (hSC : SparseCoreOrdProgramUniform dryCLsstUsed dryLSFInitUsed sparsifyImplUsed
      sc.prog sc.init sc.op)
    (hWordExp : drySparseCoreWordExp hSC dryCapExp ≤ 39)
    (inner : SolverInnerCode) (hinner : inner.IsDeterministic)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (stretchPrec : Scaling.Circulation → ℕ)
    (DeepInv : ∀ J, ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P → Prop)
    (hDeepInv : DryDeepShiftInv dryWitnessUsed sparsifyImplUsed sc hSC
      (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
      (concreteReadout2LimbMul dryWitnessUsed) stretchPrec DeepInv)
    (sz : Scaling.Circulation → Scaling.Circulation → WiredInnerSizes)
    (hInit : DryInitSpecW dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC inner
      (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
      (concreteReadout2LimbMul dryWitnessUsed) sz)
    (hCore : DryChainUpdateCoreSpecW dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC inner
      (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
      (concreteReadout2LimbMul dryWitnessUsed) sz)
    (hSelect : DryCycleRouteSelectSpecW dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC inner
      (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
      (concreteReadout2LimbMul dryWitnessUsed) sz)
    (hEval : DryCycleRouteEvalSpecW dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC inner
      (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
      (concreteReadout2LimbMul dryWitnessUsed) sz)
    (hTerm : DryShiftTermSpecW dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC inner
      (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
      (concreteReadout2LimbMul dryWitnessUsed) sz)
    (hDeep : DryShiftDeepSpecW dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC inner
      (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
      (concreteReadout2LimbMul dryWitnessUsed) stretchPrec sz)
    (hCapBounds : DryFixedPointCapBounds dryWitnessUsed (dryAllocCoeffFull B hB)
      (dryAllocDeg B hB) sz)
    (hEnv : DryContractEnvelope dryWitnessUsed sparsifyImplUsed rfl rfl rfl sc hSC
      B.cycleRate B.cycleAllocation (dryAllocCoeffFull B hB) (dryAllocDeg B hB) dryCapExp
      (concreteReadout2LimbMul dryWitnessUsed) sz) :
    MinCostFlowStatement :=
  theorem_1_1_of_dyadic_withV_mrds_programs
    (dryPrograms sc hsc hSC hWordExp inner hinner B hB stretchPrec DeepInv hDeepInv sz
      hInit hCore hSelect hEval hTerm hDeep hCapBounds hEnv)

end MinCostFlow.Final.DryRun
