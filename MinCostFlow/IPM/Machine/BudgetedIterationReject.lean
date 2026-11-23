module

public import MinCostFlow.IPM.Machine.BudgetedIteration
import WordRAM.Tactic

/-!
# Exiting an epoch before an over-budget Update

The report-size comparison or a failed refresh selects this branch.
Append the actual report count and zero status, retaining the remaining
budget. Its only writes are the fresh metadata, so the post-Detect
concrete state and its full amortized credit are preserved.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual rejection branch makes no checked Update call, returns
its fresh budget/count/failure record and retains the same DS credit. -/
theorem budgetedIterationReject_runs {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    {w record : ℕ} {p : Program}
    (hrecord : MeetsContract w p record (epochBudgetRecordContract w))
    (parent : State) (ω : ℕ → Bool) (remaining count heap b : ℕ)
    (hregs : parent.regs 25=remaining ∧ parent.regs 28=count ∧ parent.regs 26=heap)
    (hwords : ∀ z∈[remaining,count,0,heap],z<2^w)
    (hz : ZeroFrom parent.mem heap) (hspace : heap+3<2^w)
    {s : σ} {x : R.τ} (hrep : R.rep b s x parent.mem) (hfoot : ∀ z,R.foot b x z → z<heap) :
    ∃ o st cost,Runs w p ω (budgetedIterationReject record) parent o st cost ∧
      (epochBudgetRecordContract w).post [remaining,count,0,heap] parent.mem o.value st.mem ∧
      R.rep b s x st.mem ∧ (∀ z,R.foot b x z → z<o.value) ∧
      cost+R.phi b x st.mem≤R.phi b x parent.mem+68 := by
  obtain ⟨h25,h28,h26⟩ := hregs
  have hpre : (epochBudgetRecordContract w).pre [remaining,count,0,heap] parent.mem :=
    ⟨⟨remaining,count,0,heap,rfl,by decide⟩,hz,hspace⟩
  obtain ⟨body,hbody,oR,stR,cR,hrR,hpost,hcost⟩ := hrecord _ _ parent.pos ω hwords hpre
  have hv : oR.value=heap+3 := hpost.2
  have hvWord : oR.value<2^w := by omega
  have hs := epochBudgetRecord_preserves_state R hlocal hpost hrep hfoot
  let after : State := ⟨stR.mem,Function.update parent.regs 33 oR.value,stR.pos⟩
  have hcall : Runs w p ω (.call 33 record [.reg 25,.reg 28,.const 0,.reg 26]) parent .normal after
      (4+cR+1) := by
    apply runs_call_iff.mpr
    refine ⟨[remaining,count,0,heap],body,oR,stR,cR,by eval_expr,hbody,hrR,rfl,?_,rfl⟩
    cases stR
    rfl
  have hret : Runs w p ω (.ret (.reg 33)) after (.returned oR.value) after 2 :=
    runs_ret_iff.mpr ⟨oR.value,by dsimp only [after]; eval_expr,rfl,rfl,rfl⟩
  refine ⟨.returned oR.value,after,cR+8,?_,hpost,hs.1,?_,?_⟩
  · unfold budgetedIterationReject
    exact runs_seq_iff.mpr (Or.inr ⟨after,4+cR+1,2,hcall,hret,by omega⟩)
  · intro z hz'
    have hh := hfoot z hz'
    change z<oR.value
    omega
  · change cR≤60 at hcost
    dsimp only [after]
    rw [← hs.2]
    omega

end MinCostFlow.IPM.Machine
