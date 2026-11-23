module

public import MinCostFlow.IPM.Machine.TargetEpoch
import WordRAM.Tactic

/-!
# Returning the stage's flow address and status

Convergence, rejection and continuation all use the same two-word
writer. Its final heap fits and its prefix frame preserves the flow
coordinates and original input words.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The machine's final two words are the actual selected flow
address and status, with the writer's exact endpoint. -/
theorem targetEpoch_record_output {w flow status heap v : ℕ} {mem final : ℕ → ℕ}
    (h : (boundedStatusRecordContract w 2).post [flow,status,heap] mem v final) :
    v=heap+2 ∧ final (v-2)=flow ∧ final (v-1)=status ∧
      ZeroFrom final v ∧ (∀ z<heap,final z=mem z) := by
  have hv : v=heap+2 := h.2
  have hh : final heap=flow ∧ final (heap+1)=status := h.1.2.2.2.2
  have h₁ : v-2=heap := by omega
  have h₂ : v-1=heap+1 := by omega
  exact ⟨hv,h₁.symm ▸ hh.1,h₂.symm ▸ hh.2,h.1.2.2.2.1,h.1.2.2.1⟩

/-- Call the verified writer and return its actual end address. -/
theorem targetEpochReturn_runs {w record flow status heap : ℕ} {p : Program}
    (st : State) (ω : ℕ → Bool) (f s h : Expr)
    (hrecord : MeetsContract w p record (boundedStatusRecordContract w 2))
    (hArgs : evalArgs w st [f,s,h]=some [flow,status,heap])
    (hWords : ∀ v∈[flow,status,heap],v<2^w)
    (hStatus : status≤2) (hz : ZeroFrom st.mem heap) (hspace : heap+2<2^w) :
    ∃ v final cost,
      Runs w p ω (targetEpochReturn record f s h) st (.returned v) final cost ∧
      (boundedStatusRecordContract w 2).post [flow,status,heap] st.mem v final.mem ∧
      v<2^w ∧ cost≤argsSize [f,s,h]+34 := by
  obtain ⟨body,hbody,o,R,c,hRun,hOut,hCost⟩ := hrecord [flow,status,heap] st.mem st.pos ω hWords
    ⟨⟨flow,status,heap,rfl,hStatus⟩,hz,hspace⟩
  let final : State := ⟨R.mem,Function.update st.regs 31 o.value,R.pos⟩
  have hcall : Runs w p ω (.call 31 record [f,s,h]) st .normal final (argsSize [f,s,h]+c+1) := by
    apply runs_call_iff.mpr
    refine ⟨[flow,status,heap],body,o,R,c,hArgs,hbody,hRun,rfl,?_,rfl⟩
    cases R
    rfl
  have hret : Runs w p ω (.ret (.reg 31)) final (.returned o.value) final 2 :=
    runs_ret_iff.mpr ⟨o.value,by simp [final,Expr.eval],rfl,rfl,rfl⟩
  have hv : o.value=heap+2 := hOut.2
  have hc : c≤30 := hCost
  exact ⟨o.value,final,argsSize [f,s,h]+c+4,
    runs_seq_iff.mpr (Or.inr ⟨final,_,2,hcall,hret,by omega⟩),hOut,by omega,by omega⟩

end MinCostFlow.IPM.Machine
