module

public import MinCostFlow.IPM.Machine.TargetEpochReturn
import WordRAM.Tactic
import Mathlib.Tactic.Positivity

/-!
# Target-stage branches after the full startup scan

A rejected startup returns failure before any lazy iteration. Otherwise
the actual finite epoch and materialization run once. The returned bit
decides whether their explicit flow becomes the next epoch's input.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Startup rejection stops before the complete epoch call. -/
theorem targetEpochAfterInit_reject_runs {w complete record source heap : ℕ}
    {p : Program} (st : State) (ω : ℕ → Bool)
    (hrecord : MeetsContract w p record (boundedStatusRecordContract w 2))
    (hsource : st.regs 20=source) (hheap : st.regs 25=heap) (hbit : st.regs 26=0)
    (hSource : source<2^w) (hspace : heap+2<2^w) (hz : ZeroFrom st.mem heap) :
    ∃ v final cost,
      Runs w p ω (targetEpochAfterInit complete record) st (.returned v) final cost ∧
      (boundedStatusRecordContract w 2).post [source,0,heap] st.mem v final.mem ∧
      v<2^w ∧ cost≤40 := by
  have hheapW : heap<2^w := by omega
  have hzero : 0<2^w := by positivity
  have hargs : evalArgs w st [.reg 20,.const 0,.reg 25]=some [source,0,heap] := by
    eval_expr
  obtain ⟨v,final,c,hr,hout,hw,hcost⟩ := targetEpochReturn_runs st ω (.reg 20) (.const 0) (.reg 25)
    hrecord hargs (by wram_words) (by decide) hz hspace
  have hRun : Runs w p ω (targetEpochAfterInit complete record) st (.returned v) final (c+2) := by
    apply runs_cond_iff.mpr
    exact ⟨0,c,by eval_expr,by simpa using hr,by change c+2=1+c+1; omega⟩
  have hc : c≤37 := hcost
  exact ⟨v,final,c+2,hRun,hout,hw,by omega⟩

/-- The successful startup runs the verified complete epoch. Its
actual output status is doubled to distinguish continuation from
the successful terminal residual test. -/
theorem targetEpochAfterInit_complete_runs {w complete record flow heap bit cost : ℕ}
    {p : Program} {ω : ℕ → Bool} (st afterEpoch : State) {args : List ℕ} {body : Stmt}
    (hbody : p.procs[complete]?=some body)
    (hargs : evalArgs w st targetEpochCompleteArgs=some args)
    (hRun : Runs w p ω body (startState args st.mem st.pos) (.returned heap) afterEpoch cost)
    (hrecord : MeetsContract w p record (boundedStatusRecordContract w 2))
    (hflow : st.regs 23=flow) (hStartBit : st.regs 26=1)
    (hFlow : flow<2^w) (hspace : heap+2<2^w) (hz : ZeroFrom afterEpoch.mem heap)
    (hbit : afterEpoch.mem (heap-1)=bit) (hb : bit≤1) :
    ∃ v final c,
      Runs w p ω (targetEpochAfterInit complete record) st (.returned v) final c ∧
      (boundedStatusRecordContract w 2).post [flow,2*bit,heap] afterEpoch.mem v final.mem ∧
      v<2^w ∧ c≤cost+argsSize targetEpochCompleteArgs+60 := by
  let after : State := ⟨afterEpoch.mem,Function.update st.regs 27 heap,afterEpoch.pos⟩
  let read : State := {after with regs := Function.update after.regs 28 bit}
  have hh : heap<2^w := by omega
  have hOne : 1<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hslot : heap-1<2^w := by omega
  have hbW := hb.trans_lt hOne
  have hstatus : 2*bit≤2 := by omega
  have hsW := hstatus.trans_lt hTwo
  have hCall : Runs w p ω (.call 27 complete targetEpochCompleteArgs) st .normal after
      (argsSize targetEpochCompleteArgs+cost+1) := by
    apply runs_call_iff.mpr
    exact ⟨args,body,.returned heap,afterEpoch,cost,hargs,hbody,hRun,rfl,by cases afterEpoch; rfl,rfl⟩
  have hRead : Runs w p ω (.assign 28 (.load (.bin .sub (.reg 27) (.const 1)))) after .normal read 5 := by
    apply runs_assign_iff.mpr
    exact ⟨bit,by dsimp only [after]; eval_expr,rfl,rfl,rfl⟩
  have hWriteArgs : evalArgs w read [.reg 23,.bin .mul (.const 2) (.reg 28),.reg 27]=
      some [flow,2*bit,heap] := by
    dsimp only [read,after]
    eval_expr
  obtain ⟨v,final,c,hr,hout,hw,hcost⟩ := targetEpochReturn_runs read ω (.reg 23)
    (.bin .mul (.const 2) (.reg 28)) (.reg 27) hrecord hWriteArgs (by wram_words) hstatus hz hspace
  have hThen := runs_seq_iff.mpr (Or.inr ⟨after,argsSize targetEpochCompleteArgs+cost+1,5+c+1,hCall,
    runs_seq_iff.mpr (Or.inr ⟨read,5,c,hRead,hr,rfl⟩),rfl⟩)
  have hActual : Runs w p ω (targetEpochAfterInit complete record) st (.returned v) final
      (argsSize targetEpochCompleteArgs+cost+c+10) := by
    apply runs_cond_iff.mpr
    refine ⟨1,_,by eval_expr,by simpa using hThen,?_⟩
    change argsSize targetEpochCompleteArgs+cost+c+10=1+(_+1)+1
    omega
  have hc : c≤39 := hcost
  exact ⟨v,final,_,hActual,hout,hw,by omega⟩

end MinCostFlow.IPM.Machine
