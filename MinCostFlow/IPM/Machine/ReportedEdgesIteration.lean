module

public import MinCostFlow.IPM.Machine.ReportedEdgesCall
public import MinCostFlow.IPM.Machine.ReportedEdgesRead

/-!
# One complete reported-list iteration

Read the next name in Detect's order, form its scalar-table offset,
then execute the checked per-edge call. The lookup changes no memory,
so the call consumes exactly the original source blocks and DS credit.
The counter and fixed argument registers are preserved on both branches.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A complete list iteration executes the actual name lookup and checked
refresh. Its word-fit and argument premises describe the concrete table
layout. Success advances the heap, while failure returns immediately. -/
theorem reportedEdgesLoopBody_runs_at {w : ℕ} (F : MinRatioFormat w)
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
    (e base lo up f c r a one mn mx E ld gd heap names i : ℕ)
    (parent : State) (ω : ℕ → Bool) (hw : 1<2^w)
    (hnames : parent.regs 1=names) (hi : parent.regs 20=i)
    (hL : parent.regs 7=F.limbs) (hread : parent.mem (names+i)=e)
    (hslot : names+i<2^w) (hoffset : e*F.limbs<2^w)
    (hargs : evalArgs w
      ⟨parent.mem,Function.update (Function.update parent.regs 22 e) 23 (e*F.limbs),parent.pos⟩
      reportedEdgesCallArgs=some
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m])
    (hwords : ∀ z∈[b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem) :
    ∃ o st cost v x',Runs w p ω (reportedEdgesLoopBody entry) parent o st cost ∧
      (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
        [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem v st.mem ∧
      R.rep b s x' st.mem ∧
      (∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heap≤z)) ∧
      (if st.mem (v-1)=1 then o=.normal ∧ st.regs 21=v else o=.returned v) ∧
      (∀ j<21,st.regs j=parent.regs j) ∧
      cost+R.phi b x' st.mem≤
        (minRatioMachineContract F A G m κ α rate allocation).cost 1 s [b,e,heap] parent.mem+
        R.phi b x parent.mem+Num.IPM.lengthCost F.limbs F.fmt.precision E+
        Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+3621 := by
  have hLw : F.limbs<2^w := hwords _ (by simp)
  have hew : e<2^w := hwords _ (by simp)
  obtain ⟨afterRead,cRead,hrRead,rfl,hcRead⟩ := reportedEdgesRead_runs p parent
    names i F.limbs e ω hnames hi hL hread hslot hLw hew hoffset
  obtain ⟨o,st,cCall,v,x',hrCall,hpost,hrep,hfoot,hbranch,hregs,hcost⟩ :=
    reportedEdgesCallBody_runs_at F A G m κ α rate allocation R himpl hstore hquery
      hcoefficient hflag hp s x e base lo up f c r a one mn mx E ld gd heap
      _ ω hw hargs hwords hpre
  refine ⟨o,st,cRead+cCall+1,v,x',?_,hpost,hrep,hfoot,hbranch,?_,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨_,cRead,cCall,hrRead,hrCall,rfl⟩)
  · intro j hj
    rw [hregs j hj]
    simp [show j≠22 by omega,show j≠23 by omega]
  · dsimp only at hcost
    omega

theorem reportedEdgesLoopBody_runs {w : ℕ} (F : MinRatioFormat w)
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
    (e base lo up f c r a one mn mx E ld gd heap names i : ℕ)
    (parent : State) (ω : ℕ → Bool) (hw : 1<2^w)
    (hnames : parent.regs 1=names) (hi : parent.regs 20=i)
    (hL : parent.regs 7=F.limbs) (hread : parent.mem (names+i)=e)
    (hslot : names+i<2^w) (hoffset : e*F.limbs<2^w)
    (hargs : evalArgs w
      ⟨parent.mem,Function.update (Function.update parent.regs 22 e) 23 (e*F.limbs),parent.pos⟩
      reportedEdgesCallArgs=some
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m])
    (hwords : ∀ z∈[b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem) :
    ∃ o st cost v x',Runs w p ω (reportedEdgesLoopBody entry) parent o st cost ∧
      (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
        [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem v st.mem ∧
      R.rep b s x' st.mem ∧
      (∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heap≤z)) ∧
      (if st.mem (v-1)=1 then o=.normal ∧ st.regs 21=v else o=.returned v) ∧
      (∀ j<21,st.regs j=parent.regs j) ∧
      cost+R.phi b x' st.mem≤
        (minRatioMachineContract F A G m κ α rate allocation).cost 1 s [b,e,heap] parent.mem+
        R.phi b x parent.mem+Num.IPM.lengthCost F.limbs F.fmt.precision E+
        Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+3621 :=
  reportedEdgesLoopBody_runs_at F A G m κ α rate allocation R himpl hstore hquery hcoefficient
    hflag hp s x e base lo up f c r a one mn mx E ld gd heap names i parent ω hw hnames hi hL
    hread hslot hoffset hargs hwords hpre

end MinCostFlow.IPM.Machine
