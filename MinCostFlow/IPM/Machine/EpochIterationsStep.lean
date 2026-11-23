module

public import MinCostFlow.IPM.Machine.EpochIterationsTail
import WordRAM.Tactic

/-!
# Lifting an actual complete iteration into the epoch loop

Use the complete iteration's actual run as the callee. Its result bit
selects the proved heap-advance or immediate-return branch. The caller
adds exactly thirty-seven operations and leaves the callee's final
memory and tape position intact, so its retained credit is unchanged.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The loop's actual call and status continuation add exactly thirty-
seven operations. Both final states retain the callee memory and tape,
and preserve every parent register except 8, 27 and 28. -/
theorem epochIterationsStep_runs {w : ℕ} {p : Program} {iteration : ℕ} {body : Stmt}
    (hbody : p.procs[iteration]?=some body) (parent : State) (ω : ℕ → Bool)
    (args : List ℕ) (hargs : evalArgs w parent epochIterationsArgs=some args)
    {oI : Outcome} {stI : State} {cost : ℕ}
    (hrun : Runs w p ω body (startState args parent.mem parent.pos) oI stI cost)
    (hword : oI.value<2^w) (hOne : 1<2^w) (hbit : stI.mem (oI.value-1)≤1) :
    let called : State := ⟨stI.mem,Function.update parent.regs 27 oI.value,stI.pos⟩
    if stI.mem (oI.value-1)=1 then
      Runs w p ω (epochIterationsStep iteration) parent .normal
        {called with regs:=Function.update (Function.update called.regs 28 1) 8 oI.value} (cost+37)
    else
      Runs w p ω (epochIterationsStep iteration) parent (.returned oI.value)
        {called with regs:=Function.update called.regs 28 0} (cost+37) := by
  let called : State := ⟨stI.mem,Function.update parent.regs 27 oI.value,stI.pos⟩
  have hcall : Runs w p ω (.call 27 iteration epochIterationsArgs) parent .normal called
      (argsSize epochIterationsArgs+cost+1) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,oI,stI,cost,hargs,hbody,hrun,rfl,?_,rfl⟩
    cases stI
    rfl
  by_cases haccept : stI.mem (oI.value-1)=1
  · rw [ite_eq_left haccept]
    have ht := epochIterationsTail_success_runs p called ω oI.value hword hOne
      (by simp [called]) haccept
    unfold epochIterationsStep
    apply runs_seq_iff.mpr
    refine Or.inr ⟨called,argsSize epochIterationsArgs+cost+1,10,hcall,ht,?_⟩
    simp only [epochIterationsArgs,argsSize_cons,argsSize_nil,Expr.size_reg]
    omega
  · rw [ite_eq_right haccept]
    have hzero : stI.mem (oI.value-1)=0 := by omega
    have ht := epochIterationsTail_failure_runs p called ω oI.value hword hOne
      (by simp [called]) hzero
    unfold epochIterationsStep
    apply runs_seq_iff.mpr
    refine Or.inr ⟨called,argsSize epochIterationsArgs+cost+1,10,hcall,ht,?_⟩
    simp only [epochIterationsArgs,argsSize_cons,argsSize_nil,Expr.size_reg]
    omega

end MinCostFlow.IPM.Machine
