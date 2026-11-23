module

public import MinCostFlow.IPM.Machine.CheckedUpdate
public import MinCostFlow.IPM.Machine.CheckedUpdateTransition
public import MinCostFlow.IPM.Machine.BatchUpdateStatusProgram
public import MinCostFlow.IPM.Machine.BatchUpdateStatusOutput
import WordRAM.Tactic

/-!
# Complete branch proof of checked Update

Run the actual reported-coefficient check with its concrete credit.
Rejection returns immediately. On acceptance derive all Update inputs
from that actual result, then run the verified batch/Update/status
entry. Each call uses the preserved stored data. The intermediate
credit cancels, and the own work remains linear in the reported size.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

private theorem input_words {b source report g l eta L heap neg mx mn : ℕ} {z : ℕ}
    (hz : z∈[b,source,report,g,l,eta,L,heap] ∨ z∈[report,g,l,neg,mx,mn,L,heap]) :
    z∈[b,source,report,g,l,eta,L,heap,neg,mx,mn] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
  tauto

private theorem accepted_cost {count L update phi0 phi1 phi2 check run : ℕ}
    (hc : check+phi1≤count*(164*L+500)+200+phi0)
    (hu : run+phi2≤180*count+update+phi1+600) :
    check+run+30+phi2≤count*(164*L+680)+update+phi0+1000 := by
  simp only [Nat.mul_add] at hc ⊢
  omega

private theorem rejected_cost {count L update phi0 phi1 check : ℕ}
    (hc : check+phi1≤count*(164*L+500)+200+phi0) :
    check+20+phi1≤count*(164*L+680)+update+phi0+1000 := by
  simp only [Nat.mul_add] at hc ⊢
  omega

/-- The actual checked branch returns immediately on a rejected range
check. Acceptance derives every subsequent call premise and executes
one Update, retaining the final concrete state credit on either answer. -/
theorem checkedUpdate_runs_with_potential_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init batch batchWriter update core record rangeReport scalarRange status b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A (namedInstance I) I.m κ α rate allocation initPre))
    (S : Finset ℕ)
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I S))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (op 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits S))
    (s : A.State) (x : R.τ)
    (source report g l eta heap neg mx mn : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn],z<2^w)
    (hpre : (checkedUpdateContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem) :
    ∃ o st cost s' final,Runs w p ω (checkedUpdateBody rangeReport status)
      (startState [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem pos) o st cost ∧
      (checkedUpdateContract F A I κ α rate allocation R b s x S).post
        [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      checkedUpdateTransition F A I κ α rate allocation S b source report g l eta heap neg mx mn s s' mem st.mem o.value ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤S.card*(164*F.limbs+680)+rate I.m*(1+2*S.card)+R.phi b x mem+1000 := by
  obtain ⟨source',report',g',l',eta',heap',neg',mx',mn',heq,hBatchPre,hRptPre,hrep,hfoot,hfit,hk,hprec,hq,
    hgEnd,hlEnd,heEnd,heValid,heLo,heHi,hvalid,hn,hx,hm,hold,hspace,hdetected⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hbaseWords : ∀ z∈[b,source,report,g,l,eta,F.limbs,heap],z<2^w :=
    fun z hz => hwords z (input_words (Or.inl hz))
  have hRptWords : ∀ z∈[report,g,l,neg,mx,mn,F.limbs,heap],z<2^w :=
    fun z hz => hwords z (input_words (Or.inr hz))
  obtain ⟨oR,stR,cR,hrR,hRptPost,hRrep,hRfoot,hRcost⟩ :=
    coefficientRangeReport_runs_with_potential R himpl.1 hreportBody hreport pos ω hRptWords hRptPre hrep hfoot
  have hd := coefficientRangeReport_output hRptPre hRptPost
  have hvR := hd.2.2.2.2.1
  have hRptWord : oR.value<2^w := by omega
  have hbit := hd.2.1
  have hbitWord : stR.mem (oR.value-1)<2^w := by omega
  have h1 : 1<2^w := by omega
  let start := startState [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem pos
  let afterR : State := ⟨stR.mem,Function.update start.regs 11 oR.value,stR.pos⟩
  let flagged : State := {afterR with regs:=Function.update afterR.regs 12 (stR.mem (oR.value-1))}
  have hcallR : Runs w p ω
      (.call 11 rangeReport [.reg 2,.reg 3,.reg 4,.reg 8,.reg 9,.reg 10,.reg 6,.reg 7]) start .normal afterR (8+cR+1) := by
    apply runs_call_iff.mpr
    refine ⟨[report,g,l,neg,mx,mn,F.limbs,heap],coefficientRangeReportBody scalarRange record,oR,stR,cR,
      by dsimp only [start]; eval_expr,hreportBody,hrR,rfl,?_,rfl⟩
    cases stR
    rfl
  have hflagRead : Expr.MemAt afterR (heap+2-1) (stR.mem (oR.value-1)) := by
    change stR.mem (heap+2-1)=stR.mem (oR.value-1)
    rw [hvR]
  have hflag : Runs w p ω (.assign 12 (.load (.bin .sub (.reg 11) (.const 1)))) afterR .normal flagged 5 := by
    apply runs_assign_iff.mpr
    exact ⟨stR.mem (oR.value-1),by dsimp only [afterR]; eval_expr,rfl,rfl,rfl⟩
  by_cases haccept : stR.mem (oR.value-1)=1
  · have hrange := checkedUpdate_coefficient_ranges F I hBatchPre hRptPre hRptPost haccept hn hx hm hvalid hold
    have hnextSpace : oR.value+(1+6*S.card)+updateAllocationBound w b g l eta allocation+(1+2*F.limbs)+2<2^w := by
      rw [hvR]
      exact hspace
    obtain ⟨hStatusPre,hStatusWords⟩ := batchUpdateStatus_pre_after_coefficientRangeReport F A I κ α rate allocation R
      himpl.1 hBatchPre hRptPre hRptPost hrep hfoot hfit hk hprec hq hgEnd hlEnd heEnd heValid heLo heHi
      hvalid hrange hdetected hnextSpace hbaseWords
    rw [hd.1] at hStatusPre hStatusWords
    obtain ⟨oB,stB,cB,s',final,hrB,hBpost,hBrep,htransition,hBmeta,hBcost⟩ :=
      batchUpdateStatus_runs_with_potential_at F A I κ α rate allocation R himpl S hbatchBody hbatch hupdate
        hcore hrecord s x source report g l eta oR.value stR.mem stR.pos ω hStatusWords hStatusPre
    have hBword := batchUpdateStatus_value_lt F A I κ α rate allocation R hStatusPre hBpost
    have hBbit := batchUpdateStatus_bit F A I κ α rate allocation R hBpost
    have hBzero := (batchUpdateStatus_frame F A I κ α rate allocation R hBpost).1
    let afterB : State := ⟨stB.mem,Function.update flagged.regs 13 oB.value,stB.pos⟩
    have hcallB : Runs w p ω
        (.call 13 status [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 11]) flagged .normal afterB (8+cB+1) := by
      apply runs_call_iff.mpr
      refine ⟨[b,source,report,g,l,eta,F.limbs,oR.value],batchUpdateStatusBody core record,oB,stB,cB,
        by dsimp only [flagged,afterR,start]; eval_expr,hstatus,hrB,rfl,?_,rfl⟩
      cases stB
      rfl
    have hret : Runs w p ω (.ret (.reg 13)) afterB (.returned oB.value) afterB 2 :=
      runs_ret_iff.mpr ⟨oB.value,by dsimp only [afterB]; eval_expr,rfl,rfl,rfl⟩
    have hbranch : Runs w p ω
        (.call 13 status [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 11] ;; .ret (.reg 13))
        flagged (.returned oB.value) afterB (cB+12) := by
      apply runs_seq_iff.mpr
      exact Or.inr ⟨afterB,8+cB+1,2,hcallB,hret,by omega⟩
    have hcond : Runs w p ω
        (.cond (.reg 12) (.call 13 status [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 11] ;; .ret (.reg 13)) (.ret (.reg 11)))
        flagged (.returned oB.value) afterB (cB+14) := by
      apply runs_cond_iff.mpr
      exact ⟨1,cB+12,by dsimp only [flagged]; simp only [haccept]; eval_expr,by simpa using hbranch,by simp [Expr.size_reg]; omega⟩
    have hTail : Runs w p ω
        (.assign 12 (.load (.bin .sub (.reg 11) (.const 1))) ;;
          .cond (.reg 12) (.call 13 status [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 11] ;; .ret (.reg 13)) (.ret (.reg 11)))
        afterR (.returned oB.value) afterB (cB+20) :=
      runs_seq_iff.mpr (Or.inr ⟨flagged,5,cB+14,hflag,hcond,by omega⟩)
    refine ⟨.returned oB.value,afterB,cR+cB+30,s',final,?_,?_,hBrep,?_,?_,?_⟩
    · unfold checkedUpdateBody
      exact runs_seq_iff.mpr (Or.inr ⟨afterR,8+cR+1,cB+20,hcallR,hTail,by omega⟩)
    · simp only [checkedUpdateContract,List.getD_cons_zero,List.getD_cons_succ]
      refine ⟨oR.value,stR.mem,hRptPost,?_,hBbit,hBzero⟩
      rw [ite_eq_left haccept]
      exact hBpost
    · refine ⟨oR.value,stR.mem,hRptPost,?_⟩
      rw [ite_eq_left haccept]
      obtain ⟨batchEnd,batchMem,hBatch,hDpost⟩ := htransition
      have hvBatch : batchEnd=oR.value+(1+6*S.card) := hBatch.2
      refine ⟨batchEnd,batchMem,hBatch,hDpost,?_⟩
      rw [hvBatch]
      exact batchUpdateStatus_header F A I κ α rate allocation R hBpost
    · intro z hz
      refine ⟨(hBmeta z hz).1,?_⟩
      rcases (hBmeta z hz).2 with hold | hfresh
      · exact Or.inl hold
      · exact Or.inr (by omega)
    · exact accepted_cost hRcost hBcost
  · have hreject : stR.mem (oR.value-1)=0 := by omega
    have hret : Runs w p ω (.ret (.reg 11)) flagged (.returned oR.value) flagged 2 :=
      runs_ret_iff.mpr ⟨oR.value,by dsimp only [flagged,afterR]; eval_expr,rfl,rfl,rfl⟩
    have hcond : Runs w p ω
        (.cond (.reg 12) (.call 13 status [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 11] ;; .ret (.reg 13)) (.ret (.reg 11)))
        flagged (.returned oR.value) flagged 4 := by
      apply runs_cond_iff.mpr
      exact ⟨0,2,by dsimp only [flagged]; simp only [hreject]; eval_expr,by simpa using hret,rfl⟩
    have hTail : Runs w p ω
        (.assign 12 (.load (.bin .sub (.reg 11) (.const 1))) ;;
          .cond (.reg 12) (.call 13 status [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 11] ;; .ret (.reg 13)) (.ret (.reg 11)))
        afterR (.returned oR.value) flagged 10 :=
      runs_seq_iff.mpr (Or.inr ⟨flagged,5,4,hflag,hcond,rfl⟩)
    refine ⟨.returned oR.value,flagged,cR+20,s,x,?_,?_,hRrep,?_,?_,?_⟩
    · unfold checkedUpdateBody
      exact runs_seq_iff.mpr (Or.inr ⟨afterR,8+cR+1,10,hcallR,hTail,by omega⟩)
    · simp only [checkedUpdateContract,List.getD_cons_zero,List.getD_cons_succ]
      refine ⟨oR.value,stR.mem,hRptPost,?_,hbit,hd.2.2.2.2.2.1⟩
      simp only [haccept,ite_false]
      exact ⟨rfl,rfl⟩
    · refine ⟨oR.value,stR.mem,hRptPost,?_⟩
      rw [ite_eq_right haccept]
      exact ⟨rfl,rfl,rfl⟩
    · exact fun z hz => ⟨hRfoot z hz,Or.inl hz⟩
    · exact rejected_cost hRcost

theorem checkedUpdate_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init batch batchWriter update core record rangeReport scalarRange status b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (S : Finset ℕ)
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I S))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (op 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits S))
    (s : A.State) (x : R.τ)
    (source report g l eta heap neg mx mn : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn],z<2^w)
    (hpre : (checkedUpdateContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem) :
    ∃ o st cost s' final,Runs w p ω (checkedUpdateBody rangeReport status)
      (startState [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem pos) o st cost ∧
      (checkedUpdateContract F A I κ α rate allocation R b s x S).post
        [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      checkedUpdateTransition F A I κ α rate allocation S b source report g l eta heap neg mx mn s s' mem st.mem o.value ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤S.card*(164*F.limbs+680)+rate I.m*(1+2*S.card)+R.phi b x mem+1000 :=
  checkedUpdate_runs_with_potential_at F A I κ α rate allocation R himpl S hbatchBody hbatch hupdate
    hcore hrecord hstatus hreportBody hreport s x source report g l eta heap neg mx mn mem pos ω
    hwords hpre

/-- The complete linked check-before-Update driver satisfies its full
local contract on every random tape, with explicit reported-size cost. -/
theorem checkedUpdate_meetsContract_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init batch batchWriter update core record rangeReport scalarRange status entry b : ℕ} {op : ℕ → ℕ}
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
    (hp : p.procs[entry]?=some (checkedUpdateBody rangeReport status)) (s : A.State) (x : R.τ) :
    MeetsContract w p entry (checkedUpdateContract F A I κ α rate allocation R b s x S) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  have hpreCopy := hpre
  obtain ⟨source,report,g,l,eta,heap,neg,mx,mn,rfl,_⟩ := hpre
  obtain ⟨o,st,cost,_,_,hr,hpost,_,_,_,hc⟩ := checkedUpdate_runs_with_potential_at F A I κ α rate allocation R
    himpl S hbatchBody hbatch hupdate hcore hrecord hstatus hreportBody hreport
    s x source report g l eta heap neg mx mn mem pos ω hwords hpreCopy
  exact ⟨o,st,cost,hr,hpost,(Nat.le_add_right cost _).trans hc⟩

theorem checkedUpdate_meetsContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init batch batchWriter update core record rangeReport scalarRange status entry b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (S : Finset ℕ) (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I S))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (op 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits S))
    (hp : p.procs[entry]?=some (checkedUpdateBody rangeReport status)) (s : A.State) (x : R.τ) :
    MeetsContract w p entry (checkedUpdateContract F A I κ α rate allocation R b s x S) :=
  checkedUpdate_meetsContract_at F A I κ α rate allocation R himpl S hbatchBody hbatch hupdate hcore
    hrecord hstatus hreportBody hreport hp s x

end MinCostFlow.IPM.Machine
