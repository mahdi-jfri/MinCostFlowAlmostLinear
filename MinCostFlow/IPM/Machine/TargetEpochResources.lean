module

public import MinCostFlow.IPM.Machine.TargetEpochStartupCall
public import MinCostFlow.IPM.Machine.EpochCompleteProgram

/-!
# Space and cost of one target stage

A stage can leave a residual workspace, a copy of the flow, fresh
coefficient tables, the initialized data structure and its epoch
workspace. The stage keeps each allocation in the returned heap.
The running cost charges only executed operations and telescopes
the initialization, lazy calls and the full read.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- Space for the residual and copy, coefficient initialization,
each attempted iteration, full read and the returned status record. -/
def targetStageSpace {w : ℕ} (F : MinRatioFormat w) (m E B : ℕ) : ℕ :=
  (8*m+4)*F.limbs+m*F.limbs+
    (Num.IPM.lengthArraySpace m F.limbs F.fmt.precision E+
      Num.IPM.gradientArraySpace m F.limbs F.fmt.precision E+B)+m+4+
    (m+1)*budgetedIterationSpace F m E B+2

/-- All initialization and complete-epoch work after the residual
setup, including the caller's status handling. -/
def targetStageContinuationCost {w : ℕ} (F : MinRatioFormat w) (m E : ℕ)
    (rate : ℕ → ℕ) : ℕ :=
  Num.IPM.lengthArrayCost m F.limbs F.fmt.precision E+
  Num.IPM.gradientArrayCost m F.limbs F.fmt.precision E+rate m*(m+1)+
  m*(164*F.limbs+530)+7*m*budgetedIterationCharge F m E rate+
  46*m+m*reportedEdgesCharge F m E rate+1240

/-- The fixed reservation covers the full startup and complete epoch
even when the initialized allocation uses all allowed words. -/
theorem targetStage_space_split {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (old : EpochLayout) (heap B : ℕ) (allocation : ℕ → List ℕ → ℕ)
    (halloc : ∀ j<4,∀ args,allocation j args≤B) :
    let cur := epochResidualEnd I.m F.limbs heap+I.m*F.limbs
    cur+epochStartSpace F I old.exponent old.initGraph cur allocation+I.m+4+
      (I.m+1)*budgetedIterationSpace F I.m old.exponent B+2≤heap+targetStageSpace F I.m old.exponent B := by
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent
  let cur := epochResidualEnd I.m F.limbs heap+I.m*F.limbs
  have hB := halloc 3 (by decide) [old.initGraph,cur+la,cur,F.limbs,F.fmt.precision,cur+(la+ga)]
  change cur+(la+ga+allocation 3 [old.initGraph,cur+la,cur,F.limbs,F.fmt.precision,cur+(la+ga)])+I.m+4+
      (I.m+1)*budgetedIterationSpace F I.m old.exponent B+2≤heap+targetStageSpace F I.m old.exponent B
  simp only [cur,epochResidualEnd,targetStageSpace,la,ga] at hB ⊢
  omega

/-- There is space for a terminal residual and its status record even
if no startup takes place. -/
theorem targetStage_residual_space {w : ℕ} (F : MinRatioFormat w) (m E B heap : ℕ) :
    epochResidualEnd m F.limbs heap+2≤heap+targetStageSpace F m E B := by
  unfold epochResidualEnd targetStageSpace
  omega

end MinCostFlow.IPM.Machine
