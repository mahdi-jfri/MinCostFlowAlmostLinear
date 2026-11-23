module

public import MinCostFlow.IPM.Machine.BudgetedIteration
public import MinCostFlow.IPM.Machine.CheckedUpdateOutput
import WordRAM.Tactic

/-!
# Recording a checked Update within the report budget

Lift the actual checked-driver run into its call, read its status and
subtract the actual report count. The explicit allocation margin covers
the three fresh result words. Their frame preserves the same returned
state and credit, so the caller adds only a constant amortized charge.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The fitting-budget continuation executes the actual checked run and
records its remaining budget, count and answer. The callee's concrete
state and credit survive, with at most ninety-two additional operations. -/
theorem budgetedIterationAccepted_runs {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State) (hlocal : R.Local)
    {p : Program} {checked record : ℕ} {body : Stmt}
    (hbody : p.procs[checked]?=some body)
    (hrecord : MeetsContract w p record (epochBudgetRecordContract w))
    (S : Finset ℕ) (b source report g l eta heap neg mx mn remaining count charge : ℕ)
    (parent : State) (ω : ℕ → Bool) (s : A.State) (x : R.τ)
    (hargs : evalArgs w parent budgetedIterationCheckedArgs=some
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn])
    (hregs : parent.regs 25=remaining ∧ parent.regs 28=count)
    (hremaining : remaining<2^w) (hcount : count<2^w) (hfits : count≤remaining)
    {oC : Outcome} {stC : State} {cC : ℕ} {s' : A.State} {final : R.τ}
    (hrC : Runs w p ω body
      (startState [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] parent.mem parent.pos) oC stC cC)
    (hCpost : (checkedUpdateContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] parent.mem oC.value stC.mem)
    (hrep : R.rep b s' final stC.mem) (hfoot : ∀ z,R.foot b final z → z<oC.value)
    (hcost : cC+R.phi b final stC.mem≤charge)
    (hspace : (heap+2)+(1+6*S.card)+updateAllocationBound w b g l eta allocation+(1+2*F.limbs)+2+3<2^w) :
    ∃ o st cost,Runs w p ω (budgetedIterationAccepted checked record) parent o st cost ∧
      (epochBudgetRecordContract w).post
        [remaining-count,count,stC.mem (oC.value-1),oC.value] stC.mem o.value st.mem ∧
      R.rep b s' final st.mem ∧ (∀ z,R.foot b final z → z<o.value) ∧
      cost+R.phi b final st.mem≤charge+92 ∧ remaining-count+count=remaining := by
  obtain ⟨h25,h28⟩ := hregs
  have hbound := checkedUpdate_end_le F A I κ α rate allocation R (by omega) hCpost
  have hrecordSpace : oC.value+3<2^w := by omega
  have hword : oC.value<2^w := by omega
  have hOne : 1<2^w := by omega
  have hleft : remaining-count<2^w := (Nat.sub_le _ _).trans_lt hremaining
  have hbit := (checkedUpdate_status F A I κ α rate allocation R hCpost).1
  have hzero := (checkedUpdate_status F A I κ α rate allocation R hCpost).2
  have hbitWord : stC.mem (oC.value-1)<2^w := by omega
  have hpre : (epochBudgetRecordContract w).pre
      [remaining-count,count,stC.mem (oC.value-1),oC.value] stC.mem :=
    ⟨⟨_,_,_,_,rfl,hbit⟩,hzero,hrecordSpace⟩
  obtain ⟨recordBody,hrecordBody,oR,stR,cR,hrR,hRpost,hRcost⟩ :=
    hrecord _ _ stC.pos ω (by wram_words) hpre
  have hfinalWord : oR.value<2^w := by
    have hv : oR.value=oC.value+3 := hRpost.2
    omega
  have hs := epochBudgetRecord_preserves_state R hlocal hRpost hrep hfoot
  let called : State := ⟨stC.mem,Function.update parent.regs 30 oC.value,stC.pos⟩
  let flagged : State := {called with regs:=Function.update called.regs 31 (stC.mem (oC.value-1))}
  let subtracted : State := {flagged with regs:=Function.update flagged.regs 32 (remaining-count)}
  let recorded : State := ⟨stR.mem,Function.update subtracted.regs 33 oR.value,stR.pos⟩
  have hcallC : Runs w p ω (.call 30 checked budgetedIterationCheckedArgs) parent .normal called (12+cC) := by
    apply runs_call_iff.mpr
    refine ⟨_,body,oC,stC,cC,hargs,hbody,hrC,rfl,?_,?_⟩
    · cases stC; rfl
    · simp only [budgetedIterationCheckedArgs,argsSize_cons,argsSize_nil,Expr.size_reg]
      omega
  have hread : Runs w p ω (.assign 31 (.load (.bin .sub (.reg 30) (.const 1)))) called .normal flagged 5 := by
    apply runs_assign_iff.mpr
    exact ⟨_,by dsimp only [called]; eval_expr,rfl,rfl,rfl⟩
  have hsub : Runs w p ω (.assign 32 (.bin .sub (.reg 25) (.reg 28))) flagged .normal subtracted 4 := by
    apply runs_assign_iff.mpr
    exact ⟨remaining-count,by dsimp only [flagged,called]; eval_expr,rfl,rfl,rfl⟩
  have hcallR : Runs w p ω (.call 33 record [.reg 32,.reg 28,.reg 31,.reg 30]) subtracted .normal recorded (5+cR) := by
    apply runs_call_iff.mpr
    refine ⟨[remaining-count,count,stC.mem (oC.value-1),oC.value],recordBody,oR,stR,cR,
      by dsimp only [subtracted,flagged,called]; eval_expr,hrecordBody,hrR,rfl,?_,by simp [argsSize]; omega⟩
    cases stR; rfl
  have hret : Runs w p ω (.ret (.reg 33)) recorded (.returned oR.value) recorded 2 :=
    runs_ret_iff.mpr ⟨oR.value,by dsimp only [recorded]; eval_expr,rfl,rfl,rfl⟩
  have hlast : Runs w p ω (.call 33 record [.reg 32,.reg 28,.reg 31,.reg 30] ;; .ret (.reg 33))
      subtracted (.returned oR.value) recorded (cR+8) :=
    runs_seq_iff.mpr (Or.inr ⟨recorded,5+cR,2,hcallR,hret,by omega⟩)
  refine ⟨.returned oR.value,recorded,cC+cR+32,?_,hRpost,hs.1,?_,?_,Nat.sub_add_cancel hfits⟩
  · unfold budgetedIterationAccepted
    apply runs_seq_iff.mpr
    refine Or.inr ⟨called,12+cC,5+(4+(cR+8)+1)+1,hcallC,?_,by omega⟩
    apply runs_seq_iff.mpr
    refine Or.inr ⟨flagged,5,4+(cR+8)+1,hread,?_,rfl⟩
    exact runs_seq_iff.mpr (Or.inr ⟨subtracted,4,cR+8,hsub,hlast,rfl⟩)
  · intro z hz
    have hh := hfoot z hz
    have hv : oR.value=oC.value+3 := hRpost.2
    change z<oR.value
    omega
  · change cR≤60 at hRcost
    dsimp only [recorded]
    rw [← hs.2]
    omega

end MinCostFlow.IPM.Machine
