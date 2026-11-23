module

public import MinCostFlow.IPM.Machine.DetectChecked
public import MinCostFlow.IPM.Machine.CheckedUpdateProgram
public import MinCostFlow.IPM.Machine.CheckedUpdateOutput
import WordRAM.Tactic

/-!
# Executing the accepted post-Detect continuation

A successful Detect/refresh result gives a stable report pointer.
Read that pointer, evaluate the checked driver's actual packet and run
the complete check-before-Update entry. The proof retains its final
concrete credit and counts every status read, pointer read, call and
branch. The matching rejection continuation is in `DetectChecked`.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

private theorem tail_cost {cost phi rest : ℕ} (h : cost+phi≤rest+1000) :
    cost+29+phi≤rest+1050 := by omega

/-- The accepted actual post-Detect continuation executes the complete
checked driver. Its full input is supplied by the proved refresh-to-driver
bridge. It retains the same final concrete credit as that driver. -/
theorem detectCheckedTail_success_runs_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init batch batchWriter update core record rangeReport scalarRange status checked b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A (namedInstance I) I.m κ α rate allocation initPre))
    (S : Finset ℕ) (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I S))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (op 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits S))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (s : A.State) (x : R.τ) (source report g l eta heap neg mx mn : ℕ)
    (parent : State) (ω : ℕ → Bool) (hw : 2<2^w)
    (hfixed : parent.regs 0=b ∧ parent.regs 20=source ∧ parent.regs 18=g ∧ parent.regs 17=l ∧
      parent.regs 21=eta ∧ parent.regs 7=F.limbs ∧ parent.regs 22=neg ∧ parent.regs 23=mx ∧ parent.regs 24=mn)
    (hheap : parent.regs 25=heap) (hbit : parent.mem (heap-1)=1) (hpointer : parent.mem (heap-2)=report)
    (hwords : ∀ z∈[b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn],z<2^w)
    (hpre : (checkedUpdateContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] parent.mem) :
    ∃ o st cost s' final,Runs w p ω (detectCheckedTail checked) parent o st cost ∧
      (checkedUpdateContract F A I κ α rate allocation R b s x S).post
        [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] parent.mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      checkedUpdateTransition F A I κ α rate allocation S b source report g l eta heap neg mx mn s s' parent.mem st.mem o.value ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤S.card*(164*F.limbs+680)+rate I.m*(1+2*S.card)+R.phi b x parent.mem+1050 := by
  obtain ⟨h0,h20,h18,h17,h21,h7,h22,h23,h24⟩ := hfixed
  have hhWord := hwords heap (by simp)
  have hrWord := hwords report (by simp)
  have h1 : 1<2^w := by omega
  obtain ⟨oC,stC,cC,s',final,hrC,hpost,hrep,htransition,hmeta,hcost⟩ :=
    checkedUpdate_runs_with_potential_at F A I κ α rate allocation R himpl S hbatchBody hbatch hupdate hcore hrecord
      hstatus hreportBody hreport s x source report g l eta heap neg mx mn parent.mem parent.pos ω hwords hpre
  have hvWord := checkedUpdate_value_lt F A I κ α rate allocation R hpre hpost
  let flagged : State := {parent with regs:=Function.update parent.regs 26 1}
  let pointed : State := {flagged with regs:=Function.update flagged.regs 28 report}
  let after : State := ⟨stC.mem,Function.update pointed.regs 27 oC.value,stC.pos⟩
  have hflag : Runs w p ω (.assign 26 (.load (.bin .sub (.reg 25) (.const 1)))) parent .normal flagged 5 :=
    runs_assign_iff.mpr ⟨1,by eval_expr,rfl,rfl,rfl⟩
  have hread : Runs w p ω (.assign 28 (.load (.bin .sub (.reg 25) (.const 2)))) flagged .normal pointed 5 := by
    apply runs_assign_iff.mpr
    refine ⟨report,?_,rfl,rfl,rfl⟩
    dsimp only [flagged]
    eval_expr
  have hcall : Runs w p ω (.call 27 checked detectCheckedArgs) pointed .normal after (11+cC+1) := by
    apply runs_call_iff.mpr
    refine ⟨[b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn],checkedUpdateBody rangeReport status,oC,stC,cC,
      ?_,hchecked,hrC,rfl,?_,rfl⟩
    · dsimp only [detectCheckedArgs,pointed,flagged]
      eval_expr
    · cases stC
      rfl
  have hret : Runs w p ω (.ret (.reg 27)) after (.returned oC.value) after 2 :=
    runs_ret_iff.mpr ⟨oC.value,by dsimp only [after]; eval_expr,rfl,rfl,rfl⟩
  have hcallRet : Runs w p ω (.call 27 checked detectCheckedArgs ;; .ret (.reg 27)) pointed
      (.returned oC.value) after (cC+15) :=
    runs_seq_iff.mpr (Or.inr ⟨after,11+cC+1,2,hcall,hret,by omega⟩)
  have hbranch : Runs w p ω
      (.assign 28 (.load (.bin .sub (.reg 25) (.const 2))) ;; .call 27 checked detectCheckedArgs ;; .ret (.reg 27))
      flagged (.returned oC.value) after (cC+21) :=
    runs_seq_iff.mpr (Or.inr ⟨pointed,5,cC+15,hread,hcallRet,by omega⟩)
  have hcond : Runs w p ω
      (.cond (.reg 26)
        (.assign 28 (.load (.bin .sub (.reg 25) (.const 2))) ;; .call 27 checked detectCheckedArgs ;; .ret (.reg 27))
        (.ret (.reg 25))) flagged (.returned oC.value) after (cC+23) := by
    apply runs_cond_iff.mpr
    exact ⟨1,cC+21,by dsimp only [flagged]; eval_expr,by simpa using hbranch,by simp [Expr.size_reg]; omega⟩
  refine ⟨.returned oC.value,after,cC+29,s',final,?_,hpost,hrep,htransition,hmeta,?_⟩
  · unfold detectCheckedTail
    exact runs_seq_iff.mpr (Or.inr ⟨flagged,5,cC+23,hflag,hcond,by omega⟩)
  · exact tail_cost hcost

theorem detectCheckedTail_success_runs {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init batch batchWriter update core record rangeReport scalarRange status checked b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (S : Finset ℕ) (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I S))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (op 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits S))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (s : A.State) (x : R.τ) (source report g l eta heap neg mx mn : ℕ)
    (parent : State) (ω : ℕ → Bool) (hw : 2<2^w)
    (hfixed : parent.regs 0=b ∧ parent.regs 20=source ∧ parent.regs 18=g ∧ parent.regs 17=l ∧
      parent.regs 21=eta ∧ parent.regs 7=F.limbs ∧ parent.regs 22=neg ∧ parent.regs 23=mx ∧ parent.regs 24=mn)
    (hheap : parent.regs 25=heap) (hbit : parent.mem (heap-1)=1) (hpointer : parent.mem (heap-2)=report)
    (hwords : ∀ z∈[b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn],z<2^w)
    (hpre : (checkedUpdateContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] parent.mem) :
    ∃ o st cost s' final,Runs w p ω (detectCheckedTail checked) parent o st cost ∧
      (checkedUpdateContract F A I κ α rate allocation R b s x S).post
        [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] parent.mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      checkedUpdateTransition F A I κ α rate allocation S b source report g l eta heap neg mx mn s s' parent.mem st.mem o.value ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤S.card*(164*F.limbs+680)+rate I.m*(1+2*S.card)+R.phi b x parent.mem+1050 :=
  detectCheckedTail_success_runs_at F A I κ α rate allocation R himpl S hbatchBody hbatch hupdate
    hcore hrecord hstatus hreportBody hreport hchecked s x source report g l eta heap neg mx mn
    parent ω hw hfixed hheap hbit hpointer hwords hpre

end MinCostFlow.IPM.Machine
