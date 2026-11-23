module

public import MinCostFlow.IPM.Machine.ReportedEdges
import WordRAM.Tactic

/-!
# Continuing or stopping after a reported edge

Read the final bit of the returned allocation endpoint. A one advances
the endpoint and continues the loop. A zero returns immediately. This
control step changes only registers and costs at most twenty operations,
so it preserves the represented DS and its amortized potential exactly.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual continuation checks the bit and either advances the heap
register or returns failure. Memory and the tape position are unchanged. -/
theorem reportedEdgesLoopTail_runs {w : ℕ} (p : Program) (parent : State)
    (v : ℕ) (ω : ℕ → Bool) (hw : 1<2^w) (hv : v<2^w)
    (hresult : parent.regs 24=v) (hbit : parent.mem (v-1)≤1) :
    ∃ o st cost,Runs w p ω reportedEdgesLoopTail parent o st cost ∧
      (st.mem=parent.mem ∧ st.pos=parent.pos ∧
        if parent.mem (v-1)=1 then
          o=.normal ∧ st.regs=Function.update (Function.update parent.regs 25 1) 21 v
        else o=.returned v ∧ st.regs=Function.update parent.regs 25 0) ∧ cost≤20 := by
  have hslot : v-1<2^w := by omega
  have hb : parent.mem (v-1)<2^w := by omega
  apply runs_start_le
  unfold reportedEdgesLoopTail
  wram_step
  refine runs_cond_le (v:=parent.mem (v-1)) (by eval_expr) ?_ ?_
  · intro hn
    have he : parent.mem (v-1)=1 := by omega
    refine runs_assign_le (v:=v) (by eval_expr) ?_ ?_
    · exact ⟨rfl,rfl,by simp [he]⟩
    · simp only [Expr.size_reg,Expr.size_load,Expr.size_bin,Expr.size_const]
      omega
  · intro hz
    refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
    · exact ⟨rfl,rfl,by simp [hz]⟩
    · simp only [Expr.size_reg,Expr.size_load,Expr.size_bin,Expr.size_const]
      omega

end MinCostFlow.IPM.Machine
