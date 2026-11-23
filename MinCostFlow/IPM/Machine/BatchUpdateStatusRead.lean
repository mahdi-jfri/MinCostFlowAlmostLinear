module

public import MinCostFlow.IPM.Machine.BatchUpdateStatus
import WordRAM.Tactic

/-!
# Saving the Update answer location before the call

Read the stable report count and compute the end of its serialized
batch. Both assignments preserve memory, the random-tape position and
all eight input registers. Their exact total cost is twelve operations.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual count read and header arithmetic take twelve operations.
The report can be overwritten by Update after this address is saved. -/
theorem batchUpdateStatusRead_runs {w report heap count : ℕ} {p : Program}
    (parent : State) (ω : ℕ → Bool) (hr : parent.regs 2=report) (hh : parent.regs 7=heap)
    (hc : parent.mem report=count) (hSix : 6<2^w)
    (hanswer : heap+(1+6*count)<2^w) :
    Runs w p ω batchUpdateStatusRead parent .normal
      ⟨parent.mem,Function.update (Function.update parent.regs 8 count) 9 (heap+(1+6*count)),parent.pos⟩ 12 := by
  have hcount : count<2^w := by omega
  have hproduct : 6*count<2^w := by omega
  have hone : 1+6*count<2^w := by omega
  have hheap : heap<2^w := by omega
  have h1 : 1<2^w := by omega
  let middle : State := {parent with regs:=Function.update parent.regs 8 count}
  unfold batchUpdateStatusRead
  apply runs_seq_iff.mpr
  refine Or.inr ⟨middle,3,8,?_,?_,rfl⟩
  · exact runs_assign_iff.mpr ⟨count,by eval_expr,rfl,rfl,rfl⟩
  · apply runs_assign_iff.mpr
    refine ⟨heap+(1+6*count),?_,rfl,rfl,rfl⟩
    dsimp only [middle]
    eval_expr

end MinCostFlow.IPM.Machine
