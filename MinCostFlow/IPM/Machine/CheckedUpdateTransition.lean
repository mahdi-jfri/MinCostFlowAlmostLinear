module

public import MinCostFlow.IPM.Machine.CheckedUpdate

/-!
# The state trace of a checked Update

A rejected coefficient scan leaves the abstract state unchanged. An
accepted scan is followed by a batch writer and the parameter's exact
Update transition. The intermediate memories record the actual call
inputs, so the final state can be used with its concrete credit.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- The two possible abstract transitions of the checked driver, with
its concrete coefficient scan and batch preparation retained. -/
def checkedUpdateTransition {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (S : Finset ℕ)
    (b source report g l eta heap neg mx mn : ℕ) (s s' : A.State)
    (mem final : ℕ → ℕ) (v : ℕ) : Prop :=
  ∃ checkedEnd checkedMem,
    (coefficientRangeReportContract w F.fmt.limbBits S).post
      [report,g,l,neg,mx,mn,F.limbs,heap] mem checkedEnd checkedMem ∧
    if checkedMem (checkedEnd-1)=1 then
      ∃ batchEnd batchMem,
        (detectBatchContract w I S).post [source,report,checkedEnd] checkedMem batchEnd batchMem ∧
        (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).post
          0 s [b,checkedEnd,g,l,eta,batchEnd] batchMem s' final ∧ final (v-1)=final batchEnd
    else s'=s ∧ v=checkedEnd ∧ final=checkedMem

end MinCostFlow.IPM.Machine
