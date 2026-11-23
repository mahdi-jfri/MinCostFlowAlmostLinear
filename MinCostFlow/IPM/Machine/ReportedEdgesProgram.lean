module

public import MinCostFlow.IPM.Machine.ReportedEdgesCore
public import MinCostFlow.IPM.Machine.ReportedEdgesInit
public import MinCostFlow.IPM.Machine.ReportedEdgesFinish
public import MinCostFlow.IPM.Machine.ReportedEdgesEmpty

/-!
# Complete machine proof for the reported-list entry

Run the two initialization assignments, then the verified counter loop.
A rejected coordinate returns immediately. Normal completion appends a
fresh success record. The initially empty list uses its verified branch
without requiring an earlier status bit. The same concrete DS credit
is retained throughout, so Query's amortized charge is paid once per
reported name rather than once per accumulated potential.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The complete reported-list entry executes its actual linked calls,
meets the full cache and memory contract on both guard outcomes, and
retains its final concrete DS credit in the operation bound. -/
theorem reportedEdges_runs_with_potential_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init query store coefficient flag entry b q K sourceEnd tableEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A G m κ α rate allocation initPre))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hp : p.procs[entry]?=some (reportedEdgeBody query coefficient flag))
    (s : A.State) (x : R.τ)
    (names count base lo up f heap c r a one mn mx E ld gd : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem) :
    ∃ o st cost x',Runs w p ω (reportedEdgesBody entry flag)
        (startState [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem pos) o st cost ∧
      (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
        [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m]
        mem o.value st.mem ∧ R.rep b s x' st.mem ∧
      (∀ z,R.foot b x' z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b x' st.mem≤count*reportedEdgesCharge F m E rate+R.phi b x mem+100 := by
  have hpreCopy := hpre
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',es,heq,
    _,_,_,_,_,hrep,hfoot,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hz,hw,hbudget⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  cases count with
  | zero =>
    have hs : heap+1<2^w := by simpa only [Nat.zero_mul,Nat.add_zero] using hbudget
    obtain ⟨o,st,cost,hr,hflagPost,hcost⟩ := reportedEdges_empty_runs hflag
      b names base lo up f F.limbs heap c r a one mn mx F.fmt.precision E ld gd m pos mem ω hw hz hs
    have hstate := flagRecord_preserves_state R himpl.1 hflagPost hrep hfoot
    have hv := hflagPost.2
    change o.value=heap+1 at hv
    refine ⟨o,st,cost,x,hr,reportedEdges_post_empty F A G m rate allocation R himpl.1 hpreCopy hflagPost,
      hstate.1,?_,?_⟩
    · intro z hz0
      exact ⟨by have hh := hfoot z hz0; omega,Or.inl hz0⟩
    · rw [← hstate.2]
      simp only [Nat.zero_mul,Nat.zero_add]
      omega
  | succ k =>
    let start := startState
      [b,names,k+1,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem pos
    let afterInit : State := {start with regs:=Function.update (Function.update start.regs 21 heap) 20 0}
    have hh : heap<2^w := hwords _ (by simp)
    have hcountW : k+1<2^w := hwords _ (by simp)
    have hinit : Runs w p ω reportedEdgesInit start .normal afterInit 5 :=
      reportedEdgesInit_runs p start heap ω (by simp [start,startState]) hh
    have hfixed := reportedEdges_fixed_words hwords
    have hregs : ∀ j<20,j≠1 → j≠2 → j≠8 → afterInit.regs j=
        [b,names,k+1,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m].getD j 0 := by
      intro j hj _ _ _
      dsimp only [afterInit]
      rw [Function.update_of_ne (by omega : j≠20),Function.update_of_ne (by omega : j≠21)]
      rfl
    obtain ⟨oCore,stCore,cCore,v,final,hrCore,hpostCore,hrepCore,hmetaCore,hbranchCore,hregsCore,hspaceCore,hcostCore⟩ :=
      reportedEdgesCore_runs_at F A G m κ α rate allocation R himpl hstore hquery hcoefficient hflag hp
        s x names (k+1) base lo up f heap c r a one mn mx E ld gd 0 (k+1) afterInit ω hw hcountW
        hpreCopy hfixed hregs (by simp [afterInit,start,startState]) (by simp [afterInit])
        (by simp [afterInit,start,startState]) (by omega) (by simp [afterInit,start,startState]) (by omega)
    cases oCore with
    | returned u =>
      obtain ⟨rfl,_⟩ := hbranchCore
      have hrest : Runs w p ω
          (forUp 20 (.reg 2) (reportedEdgesLoopBody entry) ;; reportedEdgesFinish flag)
          afterInit (.returned u) stCore (cCore+1) :=
        runs_seq_iff.mpr (Or.inl ⟨u,cCore,hrCore,rfl,rfl⟩)
      refine ⟨.returned u,stCore,cCore+7,final,?_,hpostCore,hrepCore,hmetaCore,?_⟩
      · exact runs_seq_iff.mpr (Or.inr ⟨afterInit,5,cCore+1,hinit,hrest,by omega⟩)
      · dsimp only [afterInit,start,startState] at hcostCore
        omega
    | normal =>
      obtain ⟨hheapCore,hbitCore⟩ := hbranchCore
      obtain ⟨o,st,cFinish,hrFinish,⟨hpost,hrep',hphi,hmeta⟩,hcFinish⟩ :=
        reportedEdgesFinish_runs F A G m rate allocation R himpl.1 hflag stCore ω hpreCopy hpostCore
          hrepCore hmetaCore hspaceCore hheapCore hbitCore
      have hrest : Runs w p ω
          (forUp 20 (.reg 2) (reportedEdgesLoopBody entry) ;; reportedEdgesFinish flag)
          afterInit o st (cCore+cFinish+1) :=
        runs_seq_iff.mpr (Or.inr ⟨stCore,cCore,cFinish,hrCore,hrFinish,rfl⟩)
      refine ⟨o,st,cCore+cFinish+7,final,?_,hpost,hrep',hmeta,?_⟩
      · exact runs_seq_iff.mpr (Or.inr ⟨afterInit,5,cCore+cFinish+1,hinit,hrest,by omega⟩)
      · rw [← hphi]
        dsimp only [afterInit,start,startState] at hcostCore
        omega

theorem reportedEdges_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init query store coefficient flag entry b q K sourceEnd tableEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A G m κ α rate allocation))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hp : p.procs[entry]?=some (reportedEdgeBody query coefficient flag))
    (s : A.State) (x : R.τ)
    (names count base lo up f heap c r a one mn mx E ld gd : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem) :
    ∃ o st cost x',Runs w p ω (reportedEdgesBody entry flag)
        (startState [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem pos) o st cost ∧
      (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
        [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m]
        mem o.value st.mem ∧ R.rep b s x' st.mem ∧
      (∀ z,R.foot b x' z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b x' st.mem≤count*reportedEdgesCharge F m E rate+R.phi b x mem+100 :=
  reportedEdges_runs_with_potential_at F A G m κ α rate allocation R himpl hstore hquery
    hcoefficient hflag hp s x names count base lo up f heap c r a one mn mx E ld gd mem pos ω
    hwords hpre

/-- The complete linked reported-list entry meets its explicit machine
contract, with linear reported-name work and the parameter's amortized
Query charge. The strong theorem above retains final DS credit. -/
theorem reportedEdges_meetsContract_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init query store coefficient flag entry listEntry b q K sourceEnd tableEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A G m κ α rate allocation initPre))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hp : p.procs[entry]?=some (reportedEdgeBody query coefficient flag))
    (hlist : p.procs[listEntry]?=some (reportedEdgesBody entry flag)) (s : A.State) (x : R.τ) :
    MeetsContract w p listEntry
      (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd) := by
  apply meetsContract_of_runs hlist
  intro args mem pos ω hwords hpre
  have hpreCopy := hpre
  obtain ⟨names,count,base,lo,up,f,heap,c,r,a,one,mn,mx,E,ld,gd,es,heq,_⟩ := hpre
  subst args
  obtain ⟨o,st,cost,x',hr,hpost,_,_,hc⟩ := reportedEdges_runs_with_potential_at F A G m κ α rate allocation R
    himpl hstore hquery hcoefficient hflag hp s x names count base lo up f heap c r a one mn mx E ld gd
    mem pos ω hwords hpreCopy
  refine ⟨o,st,cost,hr,hpost,?_⟩
  change cost≤count*reportedEdgesCharge F m E rate+R.phi b x mem+100
  omega

theorem reportedEdges_meetsContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init query store coefficient flag entry listEntry b q K sourceEnd tableEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A G m κ α rate allocation))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hp : p.procs[entry]?=some (reportedEdgeBody query coefficient flag))
    (hlist : p.procs[listEntry]?=some (reportedEdgesBody entry flag)) (s : A.State) (x : R.τ) :
    MeetsContract w p listEntry
      (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd) :=
  reportedEdges_meetsContract_at F A G m κ α rate allocation R himpl hstore hquery hcoefficient
    hflag hp hlist s x

end MinCostFlow.IPM.Machine
