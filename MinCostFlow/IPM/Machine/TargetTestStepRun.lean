module

public import MinCostFlow.IPM.Machine.TargetTest
import WordRAM.Tactic

/-!
# One actual target-loop call and its continuation

The target loop forwards its current explicit-flow and heap registers.
It returns a noncontinuing stage's unchanged result. Only status
two changes either register and allows the loop counter to advance.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The caller executes a stage run and uses only the actual last two
words to decide between continuation and return. -/
theorem targetTestStep_runs {w epoch v cost status flow : ℕ} {p : Program}
    (st result : State) (ω : ℕ → Bool) {args : List ℕ} {body : Stmt}
    (hbody : p.procs[epoch]?=some body)
    (hargs : evalArgs w st ((List.range 23).map Expr.reg)=some args)
    (hrun : Runs w p ω body (startState args st.mem st.pos) (.returned v) result cost)
    (hv : v<2^w) (hTwo : 2<2^w)
    (hbit : result.mem (v-1)=status) (hstatus : status≤2)
    (hflow : result.mem (v-2)=flow) :
    ∃ o final c,
      Runs w p ω (targetTestStep epoch) st o final c ∧ final.mem=result.mem ∧
      (if status=2 then o=.normal ∧ final.regs 20=flow ∧ final.regs 21=v
        else o=.returned v) ∧
      (∀ j,j≠20 → j≠21 → j≠24 → j≠25 → final.regs j=st.regs j) ∧ c≤cost+50 := by
  let after : State := ⟨result.mem,Function.update st.regs 24 v,result.pos⟩
  let flagged : State := {after with regs:=Function.update after.regs 25 status}
  have hcall : Runs w p ω (.call 24 epoch ((List.range 23).map Expr.reg)) st .normal after (cost+24) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,.returned v,result,cost,hargs,hbody,hrun,rfl,?_,?_⟩
    · cases result
      rfl
    · change cost+24 =23+cost+1
      omega
  have hOne : 1<2^w := by omega
  have hs := hstatus.trans_lt hTwo
  have hslot : v-1<2^w := by omega
  have hslot2 : v-2<2^w := by omega
  have hread : Runs w p ω (.assign 25 (.load (.bin .sub (.reg 24) (.const 1)))) after .normal flagged 5 := by
    apply runs_assign_iff.mpr
    exact ⟨status,by dsimp only [after]; eval_expr,rfl,rfl,rfl⟩
  have hreadStatus : (Expr.reg 25).eval w flagged=some status := by simp [Expr.eval,flagged]
  have hconst : (Expr.const 2).eval w flagged=some 2 := by eval_expr
  by_cases hb : status=2
  · let next : State := {flagged with regs:=Function.update flagged.regs 20 flow}
    let final : State := {next with regs:=Function.update next.regs 21 v}
    have hflowSet : Runs w p ω (.assign 20 (.load (.bin .sub (.reg 24) (.const 2)))) flagged .normal next 5 := by
      apply runs_assign_iff.mpr
      exact ⟨flow,by dsimp only [flagged,after]; eval_expr,rfl,rfl,rfl⟩
    have hheap : Runs w p ω (.assign 21 (.reg 24)) next .normal final 2 := by
      apply runs_assign_iff.mpr
      exact ⟨v,by dsimp only [next,flagged,after]; eval_expr,rfl,rfl,rfl⟩
    have hcond : Runs w p ω (.cond (.bin .eq (.reg 25) (.const 2))
        (.assign 20 (.load (.bin .sub (.reg 24) (.const 2))) ;; .assign 21 (.reg 24))
        (.ret (.reg 24))) flagged .normal final 12 :=
      runs_cond_iff.mpr ⟨1,8,Expr.eval_eq_true hreadStatus hconst hb hOne,
      by simpa using runs_seq_iff.mpr (Or.inr ⟨next,5,2,hflowSet,hheap,rfl⟩),
      (show 12=(Expr.bin .eq (.reg 25) (.const 2)).size+8+1 from rfl)⟩
    refine ⟨.normal,final,cost+43,?_,rfl,?_,?_,by omega⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨after,cost+24,18,hcall,
        runs_seq_iff.mpr (Or.inr ⟨flagged,5,12,hread,hcond,rfl⟩),by omega⟩)
    · rw [ite_eq_left hb]
      exact ⟨rfl,by simp [final,next],by simp [final]⟩
    · intro j h20 h21 h24 h25
      simp [final,next,flagged,after,h20,h21,h24,h25]
  · have hret : Runs w p ω (.ret (.reg 24)) flagged (.returned v) flagged 2 :=
      runs_ret_iff.mpr ⟨v,by dsimp only [flagged,after]; eval_expr,rfl,rfl,rfl⟩
    have hcond : Runs w p ω (.cond (.bin .eq (.reg 25) (.const 2))
        (.assign 20 (.load (.bin .sub (.reg 24) (.const 2))) ;; .assign 21 (.reg 24))
        (.ret (.reg 24))) flagged (.returned v) flagged 6 :=
      runs_cond_iff.mpr ⟨0,2,Expr.eval_eq_false hreadStatus hconst hb hOne,
      by simpa using hret,(show 6=(Expr.bin .eq (.reg 25) (.const 2)).size+2+1 from rfl)⟩
    refine ⟨.returned v,flagged,cost+37,?_,rfl,?_,?_,by omega⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨after,cost+24,12,hcall,
        runs_seq_iff.mpr (Or.inr ⟨flagged,5,6,hread,hcond,rfl⟩),by omega⟩)
    · rw [ite_eq_right hb]
    · intro j _ _ h24 h25
      simp [flagged,after,h24,h25]

/-- Shared implementation of `targetTestStep_runs` and `targetTestStepWithV_runs`. -/
private theorem targetTestStep_runs_of_callArgs {w epoch v cost status flow callCost : ℕ} {p : Program}
    (st result : State) (ω : ℕ → Bool) {argsExpr : List Expr} {args : List ℕ} {body : Stmt}
    (hbody : p.procs[epoch]?=some body)
    (hargs : evalArgs w st argsExpr=some args)
    (hcallSize : argsSize argsExpr+1≤callCost)
    (hcallBound : callCost≤25)
    (hrun : Runs w p ω body (startState args st.mem st.pos) (.returned v) result cost)
    (hv : v<2^w) (hTwo : 2<2^w)
    (hbit : result.mem (v-1)=status) (hstatus : status≤2)
    (hflow : result.mem (v-2)=flow) :
    let step :=
      .call 24 epoch argsExpr ;;
      .assign 25 (.load (.bin .sub (.reg 24) (.const 1))) ;;
      .cond (.bin .eq (.reg 25) (.const 2))
        (.assign 20 (.load (.bin .sub (.reg 24) (.const 2))) ;;
         .assign 21 (.reg 24))
        (.ret (.reg 24))
    ∃ o final c,
      Runs w p ω step st o final c ∧ final.mem=result.mem ∧
      (if status=2 then o=.normal ∧ final.regs 20=flow ∧ final.regs 21=v
        else o=.returned v) ∧
      (∀ j,j≠20 → j≠21 → j≠24 → j≠25 → final.regs j=st.regs j) ∧ c≤cost+50 := by
  dsimp only
  let after : State := ⟨result.mem,Function.update st.regs 24 v,result.pos⟩
  let flagged : State := {after with regs:=Function.update after.regs 25 status}
  have hcall : Runs w p ω (.call 24 epoch argsExpr) st .normal after (cost+argsSize argsExpr+1) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,.returned v,result,cost,hargs,hbody,hrun,rfl,?_,by omega⟩
    cases result
    rfl
  have hOne : 1<2^w := by omega
  have hs := hstatus.trans_lt hTwo
  have hslot : v-1<2^w := by omega
  have hslot2 : v-2<2^w := by omega
  have hread : Runs w p ω (.assign 25 (.load (.bin .sub (.reg 24) (.const 1)))) after .normal flagged 5 := by
    apply runs_assign_iff.mpr
    exact ⟨status,by dsimp only [after]; eval_expr,rfl,rfl,rfl⟩
  have hreadStatus : (Expr.reg 25).eval w flagged=some status := by simp [Expr.eval,flagged]
  have hconst : (Expr.const 2).eval w flagged=some 2 := by eval_expr
  by_cases hb : status=2
  · let next : State := {flagged with regs:=Function.update flagged.regs 20 flow}
    let final : State := {next with regs:=Function.update next.regs 21 v}
    have hflowSet : Runs w p ω (.assign 20 (.load (.bin .sub (.reg 24) (.const 2)))) flagged .normal next 5 := by
      apply runs_assign_iff.mpr
      exact ⟨flow,by dsimp only [flagged,after]; eval_expr,rfl,rfl,rfl⟩
    have hheap : Runs w p ω (.assign 21 (.reg 24)) next .normal final 2 := by
      apply runs_assign_iff.mpr
      exact ⟨v,by dsimp only [next,flagged,after]; eval_expr,rfl,rfl,rfl⟩
    have hcond : Runs w p ω (.cond (.bin .eq (.reg 25) (.const 2))
        (.assign 20 (.load (.bin .sub (.reg 24) (.const 2))) ;; .assign 21 (.reg 24))
        (.ret (.reg 24))) flagged .normal final 12 :=
      runs_cond_iff.mpr ⟨1,8,Expr.eval_eq_true hreadStatus hconst hb hOne,
      by simpa using runs_seq_iff.mpr (Or.inr ⟨next,5,2,hflowSet,hheap,rfl⟩),
      (show 12=(Expr.bin .eq (.reg 25) (.const 2)).size+8+1 from rfl)⟩
    refine ⟨.normal,final,cost+argsSize argsExpr+20,?_,rfl,?_,?_,by omega⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨after,cost+argsSize argsExpr+1,18,hcall,
        runs_seq_iff.mpr (Or.inr ⟨flagged,5,12,hread,hcond,rfl⟩),by omega⟩)
    · rw [ite_eq_left hb]
      exact ⟨rfl,by simp [final,next],by simp [final]⟩
    · intro j h20 h21 h24 h25
      simp [final,next,flagged,after,h20,h21,h24,h25]
  · have hret : Runs w p ω (.ret (.reg 24)) flagged (.returned v) flagged 2 :=
      runs_ret_iff.mpr ⟨v,by dsimp only [flagged,after]; eval_expr,rfl,rfl,rfl⟩
    have hcond : Runs w p ω (.cond (.bin .eq (.reg 25) (.const 2))
        (.assign 20 (.load (.bin .sub (.reg 24) (.const 2))) ;; .assign 21 (.reg 24))
        (.ret (.reg 24))) flagged (.returned v) flagged 6 :=
      runs_cond_iff.mpr ⟨0,2,Expr.eval_eq_false hreadStatus hconst hb hOne,
      by simpa using hret,(show 6=(Expr.bin .eq (.reg 25) (.const 2)).size+2+1 from rfl)⟩
    refine ⟨.returned v,flagged,cost+argsSize argsExpr+14,?_,rfl,?_,?_,by omega⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨after,cost+argsSize argsExpr+1,12,hcall,
        runs_seq_iff.mpr (Or.inr ⟨flagged,5,6,hread,hcond,rfl⟩),by omega⟩)
    · rw [ite_eq_right hb]
    · intro j _ _ h24 h25
      simp [flagged,after,h24,h25]

/-- `V`-passing variant of `targetTestStep_runs`. -/
theorem targetTestStepWithV_runs {w epoch v cost status flow : ℕ} {p : Program}
    (st result : State) (ω : ℕ → Bool) {args : List ℕ} {body : Stmt}
    (hbody : p.procs[epoch]?=some body)
    (hargs : evalArgs w st ((List.range 23).map Expr.reg ++ [.reg 27])=some args)
    (hrun : Runs w p ω body (startState args st.mem st.pos) (.returned v) result cost)
    (hv : v<2^w) (hTwo : 2<2^w)
    (hbit : result.mem (v-1)=status) (hstatus : status≤2)
    (hflow : result.mem (v-2)=flow) :
    ∃ o final c,
      Runs w p ω (targetTestStepWithV epoch) st o final c ∧ final.mem=result.mem ∧
      (if status=2 then o=.normal ∧ final.regs 20=flow ∧ final.regs 21=v
        else o=.returned v) ∧
      (∀ j,j≠20 → j≠21 → j≠24 → j≠25 → final.regs j=st.regs j) ∧ c≤cost+50 := by
  have hSize : argsSize ((List.range 23).map Expr.reg ++ [.reg 27]) + 1 ≤ 25 := by decide
  exact targetTestStep_runs_of_callArgs st result ω hbody hargs hSize (le_refl 25) hrun hv hTwo
    hbit hstatus hflow

end MinCostFlow.IPM.Machine
