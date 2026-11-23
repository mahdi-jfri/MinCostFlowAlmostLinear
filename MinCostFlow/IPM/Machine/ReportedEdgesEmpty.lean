module

public import MinCostFlow.IPM.Machine.ReportedEdges
public import MinCostFlow.IPM.Machine.FlagRecord
import WordRAM.Tactic

/-!
# The empty reported-list branch

Detect may return no edges. The reported-list entry then skips every
Query and coefficient call and appends a success bit. This is also the
base case for the list invariant: all caller memory and DS credit below
the heap are preserved by the single status write.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

private theorem empty_loop {w : ℕ} (p : Program) (st : State) (reported : ℕ)
    (hw : 1<2^w) (hc : st.regs 20=0) (hn : st.regs 2=0) :
    Triple w p (fun st' => st'=st)
      (forUp 20 (.reg 2) (reportedEdgesLoopBody reported))
      (normalPost (fun st' => st'=st)) (fun _ => 4) := by
  intro st' ω heq
  subst st'
  refine ⟨.normal,st,4,?_,rfl,le_rfl⟩
  apply runs_loop_iff.mpr
  refine Or.inl ⟨?_,rfl,rfl,rfl⟩
  exact Expr.eval_lt_false (x:=0) (y:=0) (by simp [Expr.eval,hc]) (by simp [Expr.eval,hn]) (by omega) hw

/-- With no reported names, the actual list entry calls only the status
writer. No validity or stability condition on the DS is needed for this
branch, and the cost bound includes loop control and the call. -/
theorem reportedEdges_empty_runs {w : ℕ} {p : Program} {reported flag : ℕ}
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (b names base lo up f L heap c r a one mn mx P E ld gd m pos : ℕ)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hw : 1<2^w) (hz : ZeroFrom mem heap)
    (hspace : heap+1<2^w) :
    ∃ o st cost,Runs w p ω (reportedEdgesBody reported flag)
      (startState [b,names,0,base,lo,up,f,L,heap,c,r,a,one,mn,mx,P,E,ld,gd,m] mem pos) o st cost ∧
      (flagRecordContract w).post [1,heap] mem o.value st.mem ∧ cost≤100 := by
  have hheap : heap<2^w := by omega
  apply runs_start_le
  unfold reportedEdgesBody reportedEdgesInit reportedEdgesFinish
  wram_step
  wram_step
  wram_step
  refine runs_seq_triple_le (empty_loop p _ reported hw ?_ ?_) rfl ?_
  · simp [startState]
  · simp [startState]
  intro st' heq
  subst st'
  refine runs_seq_call_le hflag (vs:=[1,heap]) (by eval_expr)
    (by wram_words) ?_ ?_
  · exact ⟨⟨1,heap,rfl,le_rfl⟩,hz,hspace⟩
  · intro v mem' pos' hout
    have hv := hout.2
    change v=heap+1 at hv
    have hvw : v<2^w := by omega
    refine runs_ret_le (v:=v) (by eval_expr) hout ?_
    simp only [flagRecordContract,heapContract,Expr.size_reg,Expr.size_const,
      argsSize_cons,argsSize_nil]
    omega

end MinCostFlow.IPM.Machine
