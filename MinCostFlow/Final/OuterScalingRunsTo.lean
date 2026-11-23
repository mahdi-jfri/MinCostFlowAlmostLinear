module

public import MinCostFlow.Final.ScratchOuterPaperCost
public import MinCostFlow.Scaling.OuterScalingRunsTo
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Running outer scaling with polynomial scratch

The entry runs at the widened input width, then returns the exact
model answer. The cost includes the entry call and its padded
logarithmic factors.
-/

public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- The scaling reduction following Theorem 4.6 (page 15) runs on the
original encoding with an explicit word multiplier for polynomial scratch.
Its solver contract is used at the guest widths chosen from circulations. -/
theorem outerScaling_runsTo_compressedPolynomialScratch (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost,RunsTo (wordSize (scratchOuterMultiplier c d) I.encode) (scratchOuterScalingProgram solver entry c d) I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧
      cost≤scratchWholeScalingConstant solver c d*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (I.maxCapacity+1)+1)*Nat.clog 2 (I.maxCost+2)*
          (T (scratchWholeScalingConstant solver c d*min I.n I.m) (scratchWholeScalingConstant solver c d*I.m)+I.m)+
        scratchWholeScalingConstant solver c d*I.n := by
  let w := wordSize (scratchOuterMultiplier c d) I.encode
  let p := scratchOuterScalingProgram solver entry c d
  let answer := scalingAnswerWords (FlowReduction.arbitraryDemandScalingModel
    ((fun J : Circulation => compressedCanonicalSolverAt
      (wordSize (scratchWordMultiplier c d) J.solverWords) solver entry T S (hproc J) J)) I hv I.maxCost I.maxCapacity).value
  have hp : p.HasAt 0 (scratchOuterEntryModule solver entry 0 c d) := hasAt_self _
  have hk := scratchOuterEntry_meetsContract (w := w) hproc hScratch hdet hmono hp I hv
  have hin : I.encode.length<2^w := length_lt_two_pow_wordSize (by
    unfold scratchOuterMultiplier
    have h := scratchPhaseMultiplier_pos c d
    omega) _
  obtain ⟨body,hbody,o,st,steps,hr,hpost,hcost⟩ := hk [I.encode.length] (initMem I.encode) 0 ω
    (by intro x hx; have he : x=I.encode.length := List.mem_singleton.mp hx; exact he ▸ hin) ⟨rfl,rfl,rfl⟩
  change o.value=answer.length ∧ ListAt st.mem 0 answer at hpost
  have hlen : 1≤answer.length := by
    dsimp only [answer]
    cases (FlowReduction.arbitraryDemandScalingModel ((fun J : Circulation => compressedCanonicalSolverAt
      (wordSize (scratchWordMultiplier c d) J.solverWords) solver entry T S (hproc J) J)) I hv I.maxCost I.maxCapacity).value with
    | none => exact le_rfl
    | some f => rw [scalingAnswerWords_some_length]; omega
  have hc : ∀ e,(I.edge e).cost.natAbs≤I.maxCost := fun e =>
    Link.elem_le_foldr_max (List.mem_map.mpr ⟨I.edge e,List.getElem_mem e.isLt,rfl⟩)
  have hl : ∀ e,(I.edge e).lower.natAbs≤I.maxCapacity := fun e =>
    lower_natAbs_le_maxCapacity I _ (List.getElem_mem e.isLt)
  have hu : ∀ e,(I.edge e).upper.natAbs≤I.maxCapacity := fun e =>
    upper_natAbs_le_maxCapacity I _ (List.getElem_mem e.isLt)
  have hcorrect : I.IsCorrectAnswer answer := scratchArbitraryDemand_answer_correct solver entry T S c d hproc
    I hv I.maxCost I.maxCapacity hc hl hu
  have hpaper := scratchOuterEntry_cost_paper w solver entry T S c d hproc hScratch hmono I hv [I.encode.length] (initMem I.encode)
  cases o with
  | normal =>
    have hz : 0=answer.length := hpost.1
    omega
  | returned len =>
    have he : answer.length=len := hpost.1.symm
    refine ⟨answer,steps+2,runsTo_of_entry hbody hin hr he hpost.2,hcorrect,?_⟩
    exact (Nat.add_le_add_right hcost 2).trans hpaper

/-- An unrestricted solver is a special case of the compressed scaling theorem. -/
theorem outerScaling_runsTo_polynomialScratch (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (solverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost,RunsTo (wordSize (scratchOuterMultiplier c d) I.encode) (scratchOuterScalingProgram solver entry c d) I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧
      cost≤scratchWholeScalingConstant solver c d*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (I.maxCapacity+1)+1)*Nat.clog 2 (I.maxCost+2)*
          (T (scratchWholeScalingConstant solver c d*min I.n I.m) (scratchWholeScalingConstant solver c d*I.m)+I.m)+
        scratchWholeScalingConstant solver c d*I.n :=
  outerScaling_runsTo_compressedPolynomialScratch solver entry T S c d
    (fun J => meets_compressedSolverContract (hproc J)) hScratch hdet hmono I hv ω

/-- The original scratch policy gives the original whole-program cost constant. -/
theorem scratchWholeScalingConstant_original (solver : Program) :
    scratchWholeScalingConstant solver 1 4 = wholeScalingConstant solver := by
  unfold scratchWholeScalingConstant scratchOuterScalingConstant scratchWorkFactor
    wholeScalingConstant outerScalingConstant
  have h : scratchWidthFactor 1 4 = 1 := by decide
  rw [h, Nat.mul_one]

private theorem scratchZeroSolveModule_original (solver : Program) (entry b : ℕ) :
    scratchZeroSolveModule solver entry b 1 4 = zeroCapacitySolveModule solver entry b := by
  simp only [scratchZeroSolveModule, zeroCapacitySolveModule, scratchSolveModule_original]

private theorem scratchBottleneckTestModule_original (solver : Program) (entry b : ℕ) :
    scratchBottleneckTestModule solver entry b 1 4 = bottleneckTestModule solver entry b := by
  simp only [scratchBottleneckTestModule, bottleneckTestModule, scratchZeroSolveModule_original]

private theorem scratchBottleneckStepModule_original (solver : Program) (entry b : ℕ) :
    scratchBottleneckStepModule solver entry b 1 4 = bottleneckStepModule solver entry b := by
  simp only [scratchBottleneckStepModule, bottleneckStepModule, scratchBottleneckTestModule_original]

private theorem scratchBottleneckLoopModule_original (solver : Program) (entry b : ℕ) :
    scratchBottleneckLoopModule solver entry b 1 4 = bottleneckLoopModule solver entry b := by
  simp only [scratchBottleneckLoopModule, bottleneckLoopModule, scratchBottleneckStepModule_original]

private theorem scratchBottleneckSearchModule_original (solver : Program) (entry b : ℕ) :
    scratchBottleneckSearchModule solver entry b 1 4 = bottleneckSearchModule solver entry b := by
  simp only [scratchBottleneckSearchModule, bottleneckSearchModule, scratchBottleneckLoopModule_original]

private theorem scratchCapacityRoundedSolveModule_original (solver : Program) (entry b : ℕ) :
    scratchCapacityRoundedSolveModule solver entry b 1 4 = capacityRoundedSolveModule solver entry b := by
  simp only [scratchCapacityRoundedSolveModule, capacityRoundedSolveModule, scratchZeroSolveModule_original]

private theorem scratchPolyApproxModule_original (solver : Program) (entry b : ℕ) :
    scratchPolyApproxModule solver entry b 1 4 = polyApproxModule solver entry b := by
  simp only [scratchPolyApproxModule, polyApproxModule, scratchBottleneckSearchModule_original]

private theorem scratchCapacityStepModule_original (solver : Program) (entry b : ℕ) :
    scratchCapacityStepModule solver entry b 1 4 = capacityStepModule solver entry b := by
  simp only [scratchCapacityStepModule, capacityStepModule, scratchCapacityRoundedSolveModule_original, scratchPolyApproxModule_original]

private theorem scratchCapacityRoundsLoopModule_original (solver : Program) (entry b : ℕ) :
    scratchCapacityRoundsLoopModule solver entry b 1 4 = capacityRoundsLoopModule solver entry b := by
  simp only [scratchCapacityRoundsLoopModule, capacityRoundsLoopModule, scratchCapacityStepModule_original]

private theorem scratchCapacityLoopModule_original (solver : Program) (entry b : ℕ) :
    scratchCapacityLoopModule solver entry b 1 4 = capacityLoopModule solver entry b := by
  simp only [scratchCapacityLoopModule, capacityLoopModule, scratchCapacityRoundsLoopModule_original]

private theorem scratchCapacityScalingModule_original (solver : Program) (entry b : ℕ) :
    scratchCapacityScalingModule solver entry b 1 4 = capacityScalingModule solver entry b := by
  simp only [scratchCapacityScalingModule, capacityScalingModule, scratchCapacityLoopModule_original]

private theorem scratchCapacityPositiveModule_original (solver : Program) (entry b : ℕ) :
    scratchCapacityPositiveModule solver entry b 1 4 = capacityPositiveModule solver entry b := by
  simp only [scratchCapacityPositiveModule, capacityPositiveModule, scratchCapacityScalingModule_original]

private theorem scratchCapacityRoutingSolveModule_original (solver : Program) (entry b : ℕ) :
    scratchCapacityRoutingSolveModule solver entry b 1 4 = capacityRoutingSolveModule solver entry b := by
  simp only [scratchCapacityRoutingSolveModule, capacityRoutingSolveModule, scratchCapacityPositiveModule_original]

private theorem scratchCapacityRoutingOptimizeModule_original (solver : Program) (entry b : ℕ) :
    scratchCapacityRoutingOptimizeModule solver entry b 1 4 = capacityRoutingOptimizeModule solver entry b := by
  simp only [scratchCapacityRoutingOptimizeModule, capacityRoutingOptimizeModule, scratchCapacityRoutingSolveModule_original]

private theorem scratchCapacityRoutingLabelsModule_original (solver : Program) (entry b : ℕ) :
    scratchCapacityRoutingLabelsModule solver entry b 1 4 = capacityRoutingLabelsModule solver entry b := by
  simp only [scratchCapacityRoutingLabelsModule, capacityRoutingLabelsModule, scratchCapacityRoutingOptimizeModule_original]

private theorem scratchCapacityExtractDualModule_original (solver : Program) (entry b : ℕ) :
    scratchCapacityExtractDualModule solver entry b 1 4 = capacityExtractDualModule solver entry b := by
  simp only [scratchCapacityExtractDualModule, capacityExtractDualModule, scratchCapacityRoutingLabelsModule_original]

private theorem scratchCostStepModule_original (solver : Program) (entry b : ℕ) :
    scratchCostStepModule solver entry b 1 4 = costStepModule solver entry b := by
  simp only [scratchCostStepModule, costStepModule, scratchCapacityExtractDualModule_original, scratchCapacityPositiveModule_original]

private theorem scratchCostRoundsLoopModule_original (solver : Program) (entry b : ℕ) :
    scratchCostRoundsLoopModule solver entry b 1 4 = costRoundsLoopModule solver entry b := by
  simp only [scratchCostRoundsLoopModule, costRoundsLoopModule, scratchCostStepModule_original]

private theorem scratchCostLoopModule_original (solver : Program) (entry b : ℕ) :
    scratchCostLoopModule solver entry b 1 4 = costLoopModule solver entry b := by
  simp only [scratchCostLoopModule, costLoopModule, scratchCostRoundsLoopModule_original]

private theorem scratchCostScalingModule_original (solver : Program) (entry b : ℕ) :
    scratchCostScalingModule solver entry b 1 4 = costScalingModule solver entry b := by
  simp only [scratchCostScalingModule, costScalingModule, scratchCapacityPositiveModule_original, scratchCostLoopModule_original]

private theorem scratchCostCapacityModule_original (solver : Program) (entry b : ℕ) :
    scratchCostCapacityModule solver entry b 1 4 = costCapacityModule solver entry b := by
  simp only [scratchCostCapacityModule, costCapacityModule, scratchCostScalingModule_original]

private theorem scratchPrunedScalingModule_original (solver : Program) (entry b : ℕ) :
    scratchPrunedScalingModule solver entry b 1 4 = prunedScalingModule solver entry b := by
  simp only [scratchPrunedScalingModule, prunedScalingModule, scratchCostCapacityModule_original]

private theorem scratchFeasibilityPhaseModule_original (solver : Program) (entry b : ℕ) :
    scratchFeasibilityPhaseModule solver entry b 1 4 = feasibilityPhaseModule solver entry b := by
  simp only [scratchFeasibilityPhaseModule, feasibilityPhaseModule, scratchPrunedScalingModule_original]

private theorem scratchResidualOptimizationModule_original (solver : Program) (entry b : ℕ) :
    scratchResidualOptimizationModule solver entry b 1 4 = residualOptimizationModule solver entry b := by
  simp only [scratchResidualOptimizationModule, residualOptimizationModule, scratchPrunedScalingModule_original]

private theorem scratchTwoCallReductionModule_original (solver : Program) (entry b : ℕ) :
    scratchTwoCallReductionModule solver entry b 1 4 = twoCallReductionModule solver entry b := by
  simp only [scratchTwoCallReductionModule, twoCallReductionModule, scratchFeasibilityPhaseModule_original, scratchResidualOptimizationModule_original]

private theorem scratchGeneralScalingModule_original (solver : Program) (entry b : ℕ) :
    scratchGeneralScalingModule solver entry b 1 4 = generalScalingModule solver entry b := by
  simp only [scratchGeneralScalingModule, generalScalingModule, scratchTwoCallReductionModule_original]

private theorem scratchArbitraryDemandModule_original (solver : Program) (entry b : ℕ) :
    scratchArbitraryDemandModule solver entry b 1 4 = arbitraryDemandModule solver entry b := by
  simp only [scratchArbitraryDemandModule, arbitraryDemandModule, scratchGeneralScalingModule_original]

private theorem scratchOuterEntryModule_original (solver : Program) (entry b : ℕ) :
    scratchOuterEntryModule solver entry b 1 4 = outerEntryModule solver entry b := by
  simp only [scratchOuterEntryModule, outerEntryModule, scratchArbitraryDemandModule_original]

/-- The original scratch policy generates exactly the original outer program. -/
theorem scratchOuterScalingProgram_original (solver : Program) (entry : ℕ) :
    scratchOuterScalingProgram solver entry 1 4 = outerScalingProgram solver entry := by
  simp only [scratchOuterScalingProgram, outerScalingProgram, scratchOuterEntryModule_original]

/-- The general theorem specializes to the original program, word size,
scratch policy, and time bound on the same input. -/
theorem outerScaling_runsTo_originalScratch (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w, MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost, RunsTo (wordSize 131072 I.encode) (outerScalingProgram solver entry) I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧
      cost ≤ wholeScalingConstant solver*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (I.maxCapacity+1)+1)*Nat.clog 2 (I.maxCost+2)*
          (T (wholeScalingConstant solver*I.n) (wholeScalingConstant solver*I.m)+I.m)+
        wholeScalingConstant solver*I.n := by
  obtain ⟨out,cost,hr,hcorrect,hcost⟩ :=
    outerScaling_runsTo_polynomialScratch solver entry T solverScratch 1 4
      (fun J => hproc (wordSize (scratchWordMultiplier 1 4) J.solverWords))
      (fun n m => by simp only [solverScratch, Nat.one_mul]; exact le_rfl) hdet hmono I hv ω
  rw [scratchOuterMultiplier_original, scratchOuterScalingProgram_original] at hr
  rw [scratchWholeScalingConstant_original] at hcost
  have ht := hmono _ _ (wholeScalingConstant solver*I.m) (wholeScalingConstant solver*I.m)
    (Nat.mul_le_mul_left (wholeScalingConstant solver) (min_le_left I.n I.m)) le_rfl
  exact ⟨out,cost,hr,hcorrect,hcost.trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right ht I.m)) _)⟩

end MinCostFlow.Final
