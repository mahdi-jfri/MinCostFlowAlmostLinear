module

public import MinCostFlow.IPM.Machine.ReportedEdgeInputs
import WordRAM.Tactic

/-!
# The actual guarded continuation of a reported-edge step

A capacity rejection appends zero and returns immediately. Acceptance
runs the complete coefficient-status procedure. Its own slack guard may
still reject before powers. The source-layout proof supplies every call
precondition, and the same concrete DS representation and potential
survive either branch. This is the continuation after the actual Query.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Both actual continuation branches preserve the concrete DS credit and
meet the reported-edge postcondition, with a uniform numerical-work bound. -/
theorem reportedEdgeTail_runs {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {coefficient flag b q K sourceEnd : ℕ}
    (hlocal : R.Local)
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (s : A.State) (x xQ : R.τ)
    (e base lo up f c r a one mn mx E ld gd heap queryEnd : ℕ)
    (mem queryMem : ℕ → ℕ) (pos queryPos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hQ : (queryCoordinateContract F A G m κ α rate allocation R b s x).post
      [b,e,base,lo,up,f,F.limbs,heap] mem queryEnd queryMem)
    (hrepQ : R.rep b s xQ queryMem)
    (hmeta : ∀ z,R.foot b xQ z → z<queryEnd ∧ (R.foot b x z ∨ heap≤z)) :
    ∃ o st cost,Runs w p ω (reportedEdgeTail coefficient flag)
        ⟨queryMem,Function.update (startState
          [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem pos).regs
          19 queryEnd,queryPos⟩ o st cost ∧
      ((reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
        [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem o.value st.mem ∧
      R.rep b s xQ st.mem ∧ R.phi b xQ queryMem=R.phi b xQ st.mem ∧
      (∀ z,R.foot b xQ z → z<o.value ∧ (R.foot b x z ∨ heap≤z))) ∧
      cost≤Num.IPM.lengthCost F.limbs F.fmt.precision E+
        Num.IPM.gradientCost F.limbs F.fmt.precision E+434*F.limbs+1900 := by
  have hpreCopy := hpre
  obtain ⟨e',base',lo',up',f',c',r',a',one',mn',mx',E',ld',gd',heap',heq,_,_,_,_,_,_,_,_,_,
    hld,hgd,_,_,_,holdFoot,hspace⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  change heap+(minRatioMachineContract F A G m κ α rate allocation).space 1 s [b,e,heap] mem+
    16*F.limbs+Num.IPM.lengthSpace F.limbs F.fmt.precision E+
    Num.IPM.gradientSpace F.limbs F.fmt.precision E+4<2^w at hspace
  have hQframe := queryCoordinate_frame F A G m κ α rate allocation R hQ
  have hbit := queryCoordinate_status F A G m κ α rate allocation R hQ
  have hqueryW : queryEnd<2^w := by omega
  have hw4 : 4<2^w := by omega
  have hfourLW : 4*F.limbs<2^w := by omega
  have hoffsetW : 1+4*F.limbs<2^w := by omega
  have hindexW : queryEnd-(1+4*F.limbs)<2^w := by omega
  have hbitW : queryMem (queryEnd-(1+4*F.limbs))<2^w := by omega
  have hfoot : ∀ z,R.foot b xQ z → z<queryEnd ∧ (z<ld ∨ ld+F.limbs≤z) ∧ (z<gd ∨ gd+F.limbs≤z) := by
    intro z hz
    refine ⟨(hmeta z hz).1,?_⟩
    rcases (hmeta z hz).2 with hold | hfresh
    · exact holdFoot z hold
    · exact ⟨Or.inr (by omega),Or.inr (by omega)⟩
  apply runs_start_le
  unfold reportedEdgeTail
  wram_step
  refine runs_cond_le (v:=queryMem (queryEnd-(1+4*F.limbs))) (by eval_expr) ?_ ?_
  · intro hnonzero
    have haccept : queryMem (queryEnd-(1+4*F.limbs))=1 := by omega
    have hcp := reportedEdge_coefficient_pre F A G m κ α rate allocation R hpreCopy hQ haccept
    have hcpSpace := hcp.2
    change queryEnd+(4*F.limbs+1)+F.limbs+
      Num.IPM.lengthSpace F.limbs F.fmt.precision E+
      Num.IPM.gradientSpace F.limbs F.fmt.precision E+2<2^w at hcpSpace
    refine runs_seq_call_le hcoefficient
      (vs:=[m,c,r,lo,f,up,a,one,mn,mx,F.limbs,F.fmt.precision,E,ld,gd,queryEnd])
      (by eval_expr) ?_ hcp ?_
    · intro z hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | rfl
      all_goals first | exact hz ▸ hwords _ (by simp) | exact hqueryW
    · intro v mem1 pos1 hcpost
      have hkeep := coefficientStatus_preserves_state R hlocal hcpost hrepQ hfoot
      have hframe := coefficientStatus_frame hcpost
      have hvW : v<2^w := by omega
      have hfinalFoot : ∀ z,R.foot b xQ z → z<v ∧ (R.foot b x z ∨ heap≤z) := by
        intro z hz
        exact ⟨(hmeta z hz).1.trans_le hframe.1,(hmeta z hz).2⟩
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
          [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem1 ∧
          R.rep b s xQ mem1 ∧ R.phi b xQ queryMem=R.phi b xQ mem1 ∧
          (∀ z,R.foot b xQ z → z<v ∧ (R.foot b x z ∨ heap≤z))
        refine ⟨?_,hkeep.1,hkeep.2,hfinalFoot⟩
        refine ⟨queryEnd,queryMem,xQ,hQ,hrepQ,?_,hkeep.1,hfinalFoot⟩
        simp only [haccept,ite_true]
        exact hcpost
      · simp only [coefficientStatusContract,guardedCoefficientRefreshContract,
          List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,
          Expr.size_load,Expr.size_const,argsSize_cons,argsSize_nil]
        omega
  · intro hzero
    have hflagSpace : queryEnd+1<2^w := by omega
    refine runs_seq_call_le hflag (vs:=[0,queryEnd]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨0,queryEnd,rfl,by omega⟩,hQframe.2.2.1,hflagSpace⟩
    · intro v mem1 pos1 hfpost
      have hv := hfpost.2
      change v=queryEnd+1 at hv
      have hvW : v<2^w := by omega
      have hkeep := flagRecord_preserves_state R hlocal hfpost hrepQ (fun z hz => (hmeta z hz).1)
      have hfinalFoot : ∀ z,R.foot b xQ z → z<v ∧ (R.foot b x z ∨ heap≤z) := by
        intro z hz
        exact ⟨(hmeta z hz).1.trans_le (by omega),(hmeta z hz).2⟩
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
          [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem1 ∧
          R.rep b s xQ mem1 ∧ R.phi b xQ queryMem=R.phi b xQ mem1 ∧
          (∀ z,R.foot b xQ z → z<v ∧ (R.foot b x z ∨ heap≤z))
        refine ⟨?_,hkeep.1,hkeep.2,hfinalFoot⟩
        refine ⟨queryEnd,queryMem,xQ,hQ,hrepQ,?_,hkeep.1,hfinalFoot⟩
        simp only [hzero,zero_ne_one,ite_false]
        exact hfpost
      · simp only [flagRecordContract,heapContract,Expr.size_reg,Expr.size_bin,
          Expr.size_load,Expr.size_const,argsSize_cons,argsSize_nil]
        omega

end MinCostFlow.IPM.Machine
