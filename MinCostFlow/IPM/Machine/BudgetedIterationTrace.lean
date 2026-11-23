module

public import MinCostFlow.IPM.Machine.BudgetedIterationResult
import MinCostFlow.IPM.Machine.DetectCheckedTraceSuccess
import Lean.Elab.Tactic.Omega

/-!
# The checked core of a successful budgeted iteration

The fresh budget record changes the returned endpoint. Recover the
actual checked core before that record, with its successful status and
its original state-indexed trace. The existing history-extension proof
then applies to that core, without identifying different represented
states or changing the data structure's credit.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Success selects a fitting report and the actual successful checked
core. The complete inner iteration trace retains the same returned state. -/
theorem budgetedIteration_success_trace {w : ℕ} {F : MinRatioFormat w}
    {A : MinRatioDataStructureWithFailure} {I : Instance} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {R : DSRep A.State}
    {b : ℕ} {s s' : A.State} {x : R.τ} {q K sourceEnd tableEnd : ℕ}
    {args : List ℕ} {mem final : ℕ → ℕ} {v : ℕ}
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      args mem v final)
    (haccept : final (v-1)=1) :
    (A.detect s).1.card≤mem (args.getD 8 0-3) ∧
    ∃ coreEnd coreMem,
      detectCheckedTransition F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
        args mem coreMem coreEnd ∧ coreMem (coreEnd-1)=1 ∧
      (epochBudgetRecordContract w).post
        [mem (args.getD 8 0-3)-(A.detect s).1.card,(A.detect s).1.card,1,coreEnd] coreMem v final := by
  obtain ⟨cEnd,cMem,mid,hC,_,_,hbranch⟩ := hout
  split_ifs at hbranch with hfit
  · obtain ⟨coreEnd,coreMem,hpre,_,htrace,hrecord⟩ := hbranch
    have hbit := (epochBudgetRecord_output hrecord).2.2
    have hcore : coreMem (coreEnd-1)=1 := hbit.symm.trans haccept
    refine ⟨hfit.2,coreEnd,coreMem,?_,hcore,?_⟩
    · refine ⟨cEnd,cMem,hC,?_⟩
      rw [ite_eq_left hfit.1]
      exact ⟨mid,hpre,htrace⟩
    · simpa only [hcore] using hrecord
  · obtain ⟨_,hrecord⟩ := hbranch
    have hbit := (epochBudgetRecord_output hrecord).2.2
    omega

/-- A successful actual Update returns a state fitting the fixed-point
format, as required by the next Detect call. The state is the same one
retained in the credited iteration trace. -/
theorem budgetedIteration_success_fits {w : ℕ} {F : MinRatioFormat w}
    {A : MinRatioDataStructureWithFailure} {I : Instance} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {R : DSRep A.State}
    {b : ℕ} {s s' : A.State} {x : R.τ} {q K sourceEnd tableEnd : ℕ}
    {args : List ℕ} {mem final : ℕ → ℕ} {v : ℕ}
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      args mem v final)
    (haccept : final (v-1)=1) :
    MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s' := by
  obtain ⟨_,coreEnd,coreMem,hcore,hcoreSuccess,_⟩ := budgetedIteration_success_trace hout haccept
  obtain ⟨_,_,_,_,_,_,hchecked⟩ := detectCheckedTransition_success F A I κ α rate allocation R hcore hcoreSuccess
  obtain ⟨_,_,_,_,_,_,_,hupdate,_⟩ := checkedUpdateTransition_success F A I κ α rate allocation _ hchecked hcoreSuccess
  obtain ⟨_,_,_,hfit,_⟩ := hupdate
  exact hfit

end MinCostFlow.IPM.Machine
