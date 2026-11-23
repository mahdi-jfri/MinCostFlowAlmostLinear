module

public import MinCostFlow.IPM.Machine.TargetEpoch
import WordRAM.Tactic

/-!
# The target stage calls startup at the prepared addresses

The residual endpoint is one scalar block beyond the held residual.
The caller computes that pointer, invokes the initialized epoch
procedure, and reads its actual coefficient-scan decision.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The already verified startup runs as the next actual target-stage
call. The returned bit and address agree with its exact post-memory. -/
theorem targetEpochInit_runs {w startup rp out bit cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st result : State} {args : List ℕ} {body : Stmt}
    (hbody : p.procs[startup]?=some body)
    (hrp : (Expr.bin .sub (.reg 23) (.reg 15)).eval w st=some rp)
    (hargs : evalArgs w {st with regs:=Function.update st.regs 24 rp} targetEpochStartupArgs=some args)
    (hrun : Runs w p ω body (startState args st.mem st.pos) (.returned out) result cost)
    (hout : out<2^w) (hOne : 1<2^w) (hbit : result.mem (out-1)=bit) (hb : bit≤1) :
    let saved := Function.update (Function.update st.regs 24 rp) 25 out
    Runs w p ω (targetEpochInit startup) st .normal
      ⟨result.mem,Function.update saved 26 bit,result.pos⟩ (cost+30) := by
  let first : State := {st with regs:=Function.update st.regs 24 rp}
  let after : State := ⟨result.mem,Function.update first.regs 25 out,result.pos⟩
  let final : State := {after with regs:=Function.update after.regs 26 bit}
  have hFirst : Runs w p ω (.assign 24 (.bin .sub (.reg 23) (.reg 15))) st .normal first 4 :=
    runs_assign_iff.mpr ⟨rp,hrp,rfl,rfl,rfl⟩
  have hCall : Runs w p ω (.call 25 startup targetEpochStartupArgs) first .normal after (cost+19) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,.returned out,result,cost,hargs,hbody,hrun,rfl,?_,?_⟩
    · cases result
      rfl
    · change cost+19=18+cost+1
      omega
  have hword : out-1<2^w := (Nat.sub_le _ _).trans_lt hout
  have hbword : bit<2^w := lt_of_le_of_lt hb hOne
  have hRead : Runs w p ω (.assign 26 (.load (.bin .sub (.reg 25) (.const 1)))) after .normal final 5 := by
    apply runs_assign_iff.mpr
    exact ⟨bit,by dsimp only [after]; eval_expr,rfl,rfl,rfl⟩
  unfold targetEpochInit
  refine runs_seq_iff.mpr (Or.inr ⟨first,4,cost+25,hFirst,?_,by omega⟩)
  exact runs_seq_iff.mpr (Or.inr ⟨after,cost+19,5,hCall,hRead,by omega⟩)

/-- `V`-passing variant of `targetEpochInit_runs` forwarding the 19-word startup packet. -/
theorem targetEpochInitWithV_runs {w startup rp out bit cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st result : State} {args : List ℕ} {body : Stmt}
    (hbody : p.procs[startup]?=some body)
    (hrp : (Expr.bin .sub (.reg 23) (.reg 15)).eval w st=some rp)
    (hargs : evalArgs w {st with regs:=Function.update st.regs 24 rp} targetEpochStartupArgsWithV=some args)
    (hrun : Runs w p ω body (startState args st.mem st.pos) (.returned out) result cost)
    (hout : out<2^w) (hOne : 1<2^w) (hbit : result.mem (out-1)=bit) (hb : bit≤1) :
    let saved := Function.update (Function.update st.regs 24 rp) 25 out
    Runs w p ω (targetEpochInitWithV startup) st .normal
      ⟨result.mem,Function.update saved 26 bit,result.pos⟩ (cost+31) := by
  let first : State := {st with regs:=Function.update st.regs 24 rp}
  let after : State := ⟨result.mem,Function.update first.regs 25 out,result.pos⟩
  let final : State := {after with regs:=Function.update after.regs 26 bit}
  have hFirst : Runs w p ω (.assign 24 (.bin .sub (.reg 23) (.reg 15))) st .normal first 4 :=
    runs_assign_iff.mpr ⟨rp,hrp,rfl,rfl,rfl⟩
  have hArgsSize : argsSize targetEpochStartupArgsWithV = 19 := rfl
  have hCall : Runs w p ω (.call 25 startup targetEpochStartupArgsWithV) first .normal after (cost+20) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,.returned out,result,cost,hargs,hbody,hrun,rfl,?_,?_⟩
    · cases result
      rfl
    · rw [hArgsSize]
      omega
  have hword : out-1<2^w := (Nat.sub_le _ _).trans_lt hout
  have hbword : bit<2^w := lt_of_le_of_lt hb hOne
  have hRead : Runs w p ω (.assign 26 (.load (.bin .sub (.reg 25) (.const 1)))) after .normal final 5 := by
    apply runs_assign_iff.mpr
    exact ⟨bit,by dsimp only [after]; eval_expr,rfl,rfl,rfl⟩
  unfold targetEpochInitWithV
  refine runs_seq_iff.mpr (Or.inr ⟨first,4,cost+26,hFirst,?_,by omega⟩)
  exact runs_seq_iff.mpr (Or.inr ⟨after,cost+20,5,hCall,hRead,by omega⟩)

end MinCostFlow.IPM.Machine
