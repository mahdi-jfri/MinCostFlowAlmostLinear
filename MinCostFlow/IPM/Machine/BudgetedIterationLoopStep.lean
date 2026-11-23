module

public import MinCostFlow.IPM.Machine.BudgetedIterationOutput
public import MinCostFlow.IPM.Machine.BudgetedIteration
public import MinCostFlow.IPM.Machine.EpochIterationsStep

/-!
# Retaining budgeted results in the actual epoch caller

Lift the actual budgeted callee run through the epoch's call and status
check. The caller preserves its concrete final memory and DS credit,
so the decoded budget equation and history trace remain available.
Only the heap, result and status registers can change.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual epoch caller retains the same result trace, represented
state and credit, adding exactly thirty-seven operations on either branch. -/
theorem budgetedIteration_loop_step_runs {w : ℕ} {F : MinRatioFormat w}
    {A : MinRatioDataStructureWithFailure} {I : Instance} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {R : DSRep A.State}
    {b : ℕ} {s s' : A.State} {x final : R.τ} {q K sourceEnd tableEnd E : ℕ}
    {p : Program} {iteration detect checked record : ℕ} (parent : State) (ω : ℕ → Bool)
    {args : List ℕ} {oI : Outcome} {stI : State} {cost : ℕ}
    (hbody : p.procs[iteration]?=some (budgetedIterationBody detect checked record))
    (hargs : evalArgs w parent epochIterationsArgs=some args)
    (hrun : Runs w p ω (budgetedIterationBody detect checked record)
      (startState args parent.mem parent.pos) oI stI cost)
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      args parent.mem oI.value stI.mem)
    (hrep : R.rep b s' final stI.mem)
    (hcost : cost+R.phi b final stI.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m E rate+
      R.phi b x parent.mem)
    (hword : oI.value<2^w) (hOne : 1<2^w) :
    ∃ o st c,Runs w p ω (epochIterationsStep iteration) parent o st c ∧
      budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
        args parent.mem oI.value st.mem ∧ R.rep b s' final st.mem ∧
      c+R.phi b final st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m E rate+
        37+R.phi b x parent.mem ∧
      (if st.mem (oI.value-1)=1 then o=.normal ∧ st.regs 8=oI.value else o=.returned oI.value) ∧
      ∀ j,j≠8 → j≠27 → j≠28 → st.regs j=parent.regs j := by
  have hb := (budgetedIteration_status hout).1
  have hr := epochIterationsStep_runs hbody parent ω args hargs hrun hword hOne hb
  let called : State := ⟨stI.mem,Function.update parent.regs 27 oI.value,stI.pos⟩
  by_cases haccept : stI.mem (oI.value-1)=1
  · rw [ite_eq_left haccept] at hr
    refine ⟨.normal,{called with regs:=Function.update (Function.update called.regs 28 1) 8 oI.value},
      cost+37,hr,hout,hrep,?_,?_,?_⟩
    · dsimp only [called]
      omega
    · simp only [called,haccept,ite_true,Function.update_self,and_self]
    · intro j h8 h27 h28
      simp [called,Function.update_of_ne h8,Function.update_of_ne h27,Function.update_of_ne h28]
  · rw [ite_eq_right haccept] at hr
    refine ⟨.returned oI.value,{called with regs:=Function.update called.regs 28 0},
      cost+37,hr,hout,hrep,?_,?_,?_⟩
    · dsimp only [called]
      omega
    · simp only [called,haccept,ite_false]
    · intro j _ h27 h28
      simp [called,Function.update_of_ne h27,Function.update_of_ne h28]

end MinCostFlow.IPM.Machine
