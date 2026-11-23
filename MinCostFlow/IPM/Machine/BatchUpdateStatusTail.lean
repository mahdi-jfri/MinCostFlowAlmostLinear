module

public import MinCostFlow.IPM.Machine.BatchUpdateStatus
import WordRAM.Tactic

/-!
# Executing the final Update status continuation

The reserved answer header is readable below the returned heap.
Load its bit, append the address/bit record, and return. The record
writer preserves the exact concrete state and potential below it,
including either success or failure of Update.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual final continuation appends the status in at most sixty
operations and preserves the same concrete DS credit. -/
theorem batchUpdateStatusTail_runs {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    {w record b answer heap : ℕ} {p : Program} {s : σ} {x : R.τ}
    (hrecord : MeetsContract w p record (reportStatusContract w)) (parent : State) (ω : ℕ → Bool)
    (hanswer : parent.regs 9=answer) (hheap : parent.regs 10=heap)
    (hbit : parent.mem answer≤1) (hbefore : answer<heap)
    (hspace : heap+2<2^w) (hzero : ZeroFrom parent.mem heap)
    (hrep : R.rep b s x parent.mem) (hfoot : ∀ z,R.foot b x z → z<heap) :
    ∃ o st cost,Runs w p ω (batchUpdateStatusTail record) parent o st cost ∧
      ((reportStatusContract w).post [answer,parent.mem answer,heap] parent.mem o.value st.mem ∧
        R.rep b s x st.mem ∧ R.phi b x parent.mem=R.phi b x st.mem ∧
        (∀ z,R.foot b x z → z<o.value)) ∧ cost≤60 := by
  have haWord : answer<2^w := by omega
  have hhWord : heap<2^w := by omega
  have hbWord : parent.mem answer<2^w := by omega
  apply runs_start_le
  unfold batchUpdateStatusTail
  wram_step
  refine runs_seq_call_le hrecord (vs:=[answer,parent.mem answer,heap]) (by eval_expr) (by wram_words)
    ⟨⟨answer,parent.mem answer,heap,rfl,hbit⟩,hzero,hspace⟩ ?_
  intro v mem' pos' hout
  have hv := hout.2
  change v=heap+2 at hv
  have hvWord : v<2^w := by omega
  have hs := reportStatus_preserves_state R hlocal hout hrep hfoot
  refine runs_ret_le (v:=v) (by eval_expr) ⟨hout,hs.1,hs.2,?_⟩ ?_
  · intro z hz
    change z<v
    have := hfoot z hz
    omega
  · simp only [reportStatusContract,boundedStatusRecordContract,heapContract,Expr.size_reg,argsSize_cons,argsSize_nil,
      Expr.size_load]
    omega

end MinCostFlow.IPM.Machine
