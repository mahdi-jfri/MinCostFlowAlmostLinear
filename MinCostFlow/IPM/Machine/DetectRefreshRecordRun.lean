module

public import MinCostFlow.IPM.Machine.DetectRefreshRecord
public import MinCostFlow.IPM.Machine.DetectNamesOutput
import WordRAM.Tactic

/-!
# Executing the final combined-stage report/status continuation

Read the checked refresh's final bit, call the verified two-word record
writer and return its endpoint. The combined budget justifies the word
and allocation bounds on both guard outcomes. The record preserves the
same concrete final DS state and potential, so no credit is lost at the
interface to the next target-test stage.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual final status load, record call and return complete the
combined-stage output while preserving its concrete credit, in sixty
operations. No further numeric work occurs after a rejected refresh. -/
theorem detectRefreshRecordTail_runs {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State) (hlocal : R.Local)
    {p : Program} {record b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd dHeap rHeap : ℕ}
    {s : A.State} {x detected refreshed : R.τ} {mem dMem : ℕ → ℕ}
    (hrecord : MeetsContract w p record (reportStatusContract w)) (parent : State) (ω : ℕ → Bool)
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hdetect : (detectNamesContract F A G m κ α rate allocation R b s x).post [b,m,heap] mem dHeap dMem)
    (hDrep : R.rep b (A.detect s).2 detected dMem)
    (hDmeta : ∀ z,R.foot b detected z → z<dHeap ∧ (R.foot b x z ∨ heap≤z))
    (hDbefore : ∀ z,R.foot b detected z → z<dMem (dHeap-1))
    (hrefresh : (reportedEdgesContract F A G m rate allocation R b (A.detect s).2 detected q K sourceEnd tableEnd).post
      [b,dMem (dHeap-1)+1,(A.detect s).1.card,base,lo,up,f,F.limbs,dHeap,c,r,a,one,mn,mx,
        F.fmt.precision,E,ld,gd,m] dMem rHeap parent.mem)
    (hRrep : R.rep b (A.detect s).2 refreshed parent.mem)
    (hRmeta : ∀ z,R.foot b refreshed z → z<rHeap ∧ (R.foot b detected z ∨ dHeap≤z))
    (hheap : parent.regs 23=rHeap) (hpointer : parent.regs 21=dMem (dHeap-1)) :
    ∃ o st cost,Runs w p ω (detectRefreshRecordTail record) parent o st cost ∧
      ((detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).post
        [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem o.value st.mem ∧
        R.rep b (A.detect s).2 refreshed st.mem ∧ R.phi b refreshed parent.mem=R.phi b refreshed st.mem ∧
        (∀ z,R.foot b refreshed z → z<o.value ∧ (R.foot b x z ∨ heap≤z))) ∧ cost≤60 := by
  have hrefreshCopy := hrefresh
  have hspace := detectRefresh_remaining_space F A G m κ α rate allocation R hpre hdetect
  have hreport := detectNames_output F A G m κ α rate allocation R hdetect
  simp only [reportedEdgesContract,List.getD_cons_zero,List.getD_cons_succ] at hrefresh
  obtain ⟨_,_,_,hLoR,hHiR,hzero,hbit,_⟩ := hrefresh
  have hrW : rHeap<2^w := by omega
  have hr2W : rHeap+2<2^w := by omega
  have hslotW : rHeap-1<2^w := by omega
  have hpW : dMem (dHeap-1)<2^w := by omega
  have hbitW : parent.mem (rHeap-1)<2^w := by omega
  have hw : 1<2^w := by omega
  have hLoD : heap≤dHeap := by omega
  apply runs_start_le
  unfold detectRefreshRecordTail
  wram_step
  refine runs_seq_call_le hrecord (vs:=[dMem (dHeap-1),parent.mem (rHeap-1),rHeap])
    (by eval_expr) (by wram_words) ⟨⟨_,_,rHeap,rfl,hbit⟩,hzero,by change rHeap+2<2^w; exact hr2W⟩ ?_
  intro v mem' pos' hr
  have hv := hr.2
  change v=rHeap+2 at hv
  have hvW : v<2^w := by omega
  have hpost := detectRefresh_post_record F A G m κ α rate allocation R hlocal hpre hdetect hDrep
    hDmeta hDbefore hrefreshCopy hRrep hRmeta hr
  refine runs_ret_le (v:=v) (by eval_expr) ⟨hpost.1,hpost.2.1,hpost.2.2,?_⟩ ?_
  · intro z hz
    change z<v ∧ (R.foot b x z ∨ heap≤z)
    refine ⟨by have hh := (hRmeta z hz).1; omega,?_⟩
    rcases (hRmeta z hz).2 with hold | hfresh
    · exact (hDmeta z hold).2
    · exact Or.inr (hLoD.trans hfresh)
  · simp only [reportStatusContract,boundedStatusRecordContract,heapContract,Expr.size_reg,Expr.size_load,Expr.size_bin,
      Expr.size_const,argsSize_cons,argsSize_nil]
    omega

end MinCostFlow.IPM.Machine
