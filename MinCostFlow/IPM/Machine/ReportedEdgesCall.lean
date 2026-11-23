module

public import MinCostFlow.IPM.Machine.ReportedEdgeCall
public import MinCostFlow.IPM.Machine.ReportedEdgeOutput
public import MinCostFlow.IPM.Machine.ReportedEdgesTail

/-!
# A reported-list call and its checked continuation

Compose the actual per-edge call with the status branch. Both rejection
paths stop the loop. Success advances the allocation endpoint. The
numeric tables and the represented DS have the per-edge postcondition,
and the same concrete potential is retained in the amortized bound.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual call and status check retain the DS credit and parent
registers used by later list iterations. Neither failure branch proceeds
to a later edge. The bound includes argument evaluation and control. -/
theorem reportedEdgesCallBody_runs_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init query store coefficient flag entry b q K sourceEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A G m κ α rate allocation initPre))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hp : p.procs[entry]?=some (reportedEdgeBody query coefficient flag))
    (s : A.State) (x : R.τ)
    (e base lo up f c r a one mn mx E ld gd heap : ℕ)
    (parent : State) (ω : ℕ → Bool) (hw : 1<2^w)
    (hargs : evalArgs w parent reportedEdgesCallArgs=some
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m])
    (hwords : ∀ z∈[b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem) :
    ∃ o st cost v x',Runs w p ω (reportedEdgesCallBody entry) parent o st cost ∧
      (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
        [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem v st.mem ∧
      R.rep b s x' st.mem ∧
      (∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heap≤z)) ∧
      (if st.mem (v-1)=1 then o=.normal ∧ st.regs 21=v else o=.returned v) ∧
      (∀ j<21,st.regs j=parent.regs j) ∧
      cost+R.phi b x' st.mem≤
        (minRatioMachineContract F A G m κ α rate allocation).cost 1 s [b,e,heap] parent.mem+
        R.phi b x parent.mem+Num.IPM.lengthCost F.limbs F.fmt.precision E+
        Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+3600 := by
  obtain ⟨v,after,cCall,x',hrCall,hpost,hregs,hrep,hfoot,hcost⟩ :=
    reportedEdge_call_with_potential_at F A G m κ α rate allocation R (result:=24) himpl hstore hquery
      hcoefficient hflag hp s x e base lo up f c r a one mn mx E ld gd heap
      reportedEdgesCallArgs parent ω hargs hwords hpre
  have hv := reportedEdge_endpoint_word F A G m κ α rate allocation R hpre hpost
  have hb := reportedEdge_status F A G m κ α rate allocation R hpost
  have hresult : after.regs 24=v := by rw [hregs]; simp
  obtain ⟨o,st,cTail,hrTail,⟨hmem,hpos,hbranch⟩,hcTail⟩ :=
    reportedEdgesLoopTail_runs p after v ω hw hv hresult hb
  refine ⟨o,st,cCall+cTail+1,v,x',?_,?_,?_,?_,?_,?_,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨after,cCall,cTail,hrCall,hrTail,rfl⟩)
  · simpa only [hmem] using hpost
  · simpa only [hmem] using hrep
  · simpa only [hmem] using hfoot
  · rw [hmem]
    split_ifs at hbranch ⊢ with hh
    · exact ⟨hbranch.1,by rw [hbranch.2]; simp⟩
    · exact hbranch.1
  · intro j hj
    split_ifs at hbranch
    · rw [hbranch.2,hregs]
      simp [show j≠21 by omega,show j≠24 by omega,show j≠25 by omega]
    · rw [hbranch.2,hregs]
      simp [show j≠24 by omega,show j≠25 by omega]
  · rw [hmem]
    simp only [reportedEdgesCallArgs,argsSize_cons,argsSize_nil,Expr.size_reg,Expr.size_bin] at hcost
    omega

theorem reportedEdgesCallBody_runs {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init query store coefficient flag entry b q K sourceEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A G m κ α rate allocation))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hp : p.procs[entry]?=some (reportedEdgeBody query coefficient flag))
    (s : A.State) (x : R.τ)
    (e base lo up f c r a one mn mx E ld gd heap : ℕ)
    (parent : State) (ω : ℕ → Bool) (hw : 1<2^w)
    (hargs : evalArgs w parent reportedEdgesCallArgs=some
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m])
    (hwords : ∀ z∈[b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem) :
    ∃ o st cost v x',Runs w p ω (reportedEdgesCallBody entry) parent o st cost ∧
      (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
        [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem v st.mem ∧
      R.rep b s x' st.mem ∧
      (∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heap≤z)) ∧
      (if st.mem (v-1)=1 then o=.normal ∧ st.regs 21=v else o=.returned v) ∧
      (∀ j<21,st.regs j=parent.regs j) ∧
      cost+R.phi b x' st.mem≤
        (minRatioMachineContract F A G m κ α rate allocation).cost 1 s [b,e,heap] parent.mem+
        R.phi b x parent.mem+Num.IPM.lengthCost F.limbs F.fmt.precision E+
        Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+3600 :=
  reportedEdgesCallBody_runs_at F A G m κ α rate allocation R himpl hstore hquery hcoefficient
    hflag hp s x e base lo up f c r a one mn mx E ld gd heap parent ω hw hargs hwords hpre

end MinCostFlow.IPM.Machine
