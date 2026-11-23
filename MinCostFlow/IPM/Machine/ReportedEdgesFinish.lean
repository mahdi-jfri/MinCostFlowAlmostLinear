module

public import MinCostFlow.IPM.Machine.ReportedEdgesAppend
public import MinCostFlow.IPM.Machine.ReportedEdges
import WordRAM.Tactic

/-!
# Executing the list entry's final success continuation

After normal loop completion, call the verified status writer and return
its fresh endpoint. The complete list postcondition survives. Locality
preserves the same concrete DS state and its credit, and the continuation
cost is bounded independently of the number of reported names.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual final call and return preserve the full list outputs and
concrete credit, using the reserved final word and at most fifty steps. -/
theorem reportedEdgesFinish_runs {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State) (hlocal : R.Local)
    {p : Program} {flag b q K sourceEnd tableEnd names count base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {s : A.State} {x mid : R.τ} {mem : ℕ → ℕ}
    (hflag : MeetsContract w p flag (flagRecordContract w)) (parent : State) (ω : ℕ → Bool)
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hcore : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v parent.mem)
    (hrep : R.rep b s mid parent.mem)
    (hmeta : ∀ z,R.foot b mid z → z<v ∧ (R.foot b x z ∨ heap≤z))
    (hspace : v≤heap+count*reportedEdgesScratch F m b E allocation)
    (hheap : parent.regs 21=v) (haccept : parent.mem (v-1)=1) :
    ∃ o st cost,Runs w p ω (reportedEdgesFinish flag) parent o st cost ∧
      ((reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
        [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m]
        mem o.value st.mem ∧ R.rep b s mid st.mem ∧ R.phi b mid parent.mem=R.phi b mid st.mem ∧
        (∀ z,R.foot b mid z → z<o.value ∧ (R.foot b x z ∨ heap≤z))) ∧ cost≤50 := by
  have hpreCopy := hpre
  have hcoreCopy := hcore
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',es,heq,
    _,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hw,hbudget⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  simp only [reportedEdgesContract,List.getD_cons_zero,List.getD_cons_succ] at hcore
  obtain ⟨_,_,_,_,_,hzero,_⟩ := hcore
  have hv : v<2^w := by omega
  have hv1 : v+1<2^w := by omega
  apply runs_start_le
  unfold reportedEdgesFinish
  refine runs_seq_call_le hflag (vs:=[1,v]) (by eval_expr) (by wram_words)
    ⟨⟨1,v,rfl,le_rfl⟩,hzero,by change v+1<2^w; exact hv1⟩ ?_
  intro u mem' pos' hf
  have hu := hf.2
  change u=v+1 at hu
  have huw : u<2^w := by omega
  have hpost := reportedEdges_post_append F A G m rate allocation R hlocal hpreCopy hcoreCopy hspace haccept hf
  have hstate := flagRecord_preserves_state R hlocal hf hrep (fun z hz => (hmeta z hz).1)
  refine runs_ret_le (v:=u) (by eval_expr) ⟨hpost,hstate.1,hstate.2,?_⟩ ?_
  · intro z hz
    change z<u ∧ (R.foot b x z ∨ heap≤z)
    exact ⟨by have hh := (hmeta z hz).1; omega,(hmeta z hz).2⟩
  · simp only [flagRecordContract,heapContract,Expr.size_const,Expr.size_reg,argsSize_cons,argsSize_nil]
    omega

end MinCostFlow.IPM.Machine
