module

public import MinCostFlow.IPM.Machine.EpochIterations
import WordRAM.Tactic

/-!
# Returning the completed epoch's fresh success word

The finite loop has exhausted its counter. The final call writes a
one-word success flag beyond its current heap and returns the resulting
endpoint. The old data structure footprint and its credit survive.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Execute the success continuation at the actual ending loop state. -/
theorem epochIterations_finish_runs {w : ℕ} {p : Program} {flag b heap : ℕ}
    {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (parent : State) (ω : ℕ → Bool)
    (hheap : parent.regs 8=heap) (hz : ZeroFrom parent.mem heap)
    (hspace : heap+1<2^w) {s : σ} {x : R.τ}
    (hrep : R.rep b s x parent.mem) (hfoot : ∀ z,R.foot b x z → z<heap) :
    ∃ v st cost,
      Runs w p ω (.call 29 flag [.const 1,.reg 8] ;; .ret (.reg 29)) parent (.returned v) st cost ∧
      (flagRecordContract w).post [1,heap] parent.mem v st.mem ∧
      R.rep b s x st.mem ∧ cost+R.phi b x st.mem≤26+R.phi b x parent.mem := by
  have hOne : 1<2^w := by omega
  have hword : heap<2^w := by omega
  obtain ⟨body,hbody,oF,stF,cF,hrF,hout,hcost⟩ :=
    hflag [1,heap] parent.mem parent.pos ω (by wram_words) ⟨⟨1,heap,rfl,le_rfl⟩,hz,hspace⟩
  have hv : oF.value=heap+1 := hout.2
  have hvWord : oF.value<2^w := by omega
  let final : State := ⟨stF.mem,Function.update parent.regs 29 oF.value,stF.pos⟩
  have hcall : Runs w p ω (.call 29 flag [.const 1,.reg 8]) parent .normal final (cF+3) := by
    apply runs_call_iff.mpr
    refine ⟨[1,heap],body,oF,stF,cF,by eval_expr,hbody,hrF,rfl,?_,by simp [argsSize]; omega⟩
    cases stF
    rfl
  have hret : Runs w p ω (.ret (.reg 29)) final (.returned oF.value) final 2 :=
    runs_ret_iff.mpr ⟨oF.value,by dsimp only [final]; eval_expr,rfl,rfl,rfl⟩
  have hs := flagRecord_preserves_state R hlocal hout hrep hfoot
  refine ⟨oF.value,final,cF+6,runs_seq_iff.mpr (Or.inr ⟨final,cF+3,2,hcall,hret,rfl⟩),hout,hs.1,?_⟩
  change cF≤20 at hcost
  change cF+6+R.phi b x stF.mem≤26+R.phi b x parent.mem
  rw [← hs.2]
  omega

end MinCostFlow.IPM.Machine
