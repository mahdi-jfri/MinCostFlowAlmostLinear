module

public import MinCostFlow.IPM.Machine.ReportedEdgeTail
import WordRAM.Tactic

/-!
# Correctness and amortized cost of one reported-edge program

Call the actual Query-and-coordinate recovery entry, then run the proved
guarded continuation. The concrete state whose potential pays for Query
is the same state preserved by the numerical continuation. The resulting
bound counts every call and branch and is independent of whether either
guard rejects. The target-test loop can therefore stop on its final bit.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The complete reported-edge procedure executes actual linked calls,
meets its functional contract and retains the correct concrete DS credit
and footprint. Both guard failures have the same amortized upper bound. -/
theorem reportedEdge_runs_with_potential_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init query store coefficient flag b q K sourceEnd : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A G m κ α rate allocation initPre))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (s : A.State) (x : R.τ)
    (e base lo up f c r a one mn mx E ld gd heap : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem) :
    ∃ o st cost x',Runs w p ω (reportedEdgeBody query coefficient flag)
        (startState [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem pos) o st cost ∧
      (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
        [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem o.value st.mem ∧
      R.rep b s x' st.mem ∧
      (∀ z,R.foot b x' z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b x' st.mem≤
        (minRatioMachineContract F A G m κ α rate allocation).cost 1 s [b,e,heap] mem+
        R.phi b x mem+Num.IPM.lengthCost F.limbs F.fmt.precision E+
        Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+3500 := by
  have hpreCopy := hpre
  obtain ⟨e',base',lo',up',f',c',r',a',one',mn',mx',E',ld',gd',heap',heq,hQpre,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hQwords : ∀ z∈[b,e,base,lo,up,f,F.limbs,heap],z<2^w := by
    intro z hz
    apply hwords z
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
    tauto
  obtain ⟨oQ,stQ,cQ,xQ,hrQ,hQpost,hQrep,hQmeta,hQcost⟩ :=
    queryCoordinate_runs_with_potential_at F A G m κ α rate allocation R himpl hstore s x
      e base lo up f heap mem pos ω hQwords hQpre
  let start := startState [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem pos
  let afterQuery : State := ⟨stQ.mem,Function.update start.regs 19 oQ.value,stQ.pos⟩
  have hcall : Runs w p ω
      (.call 19 query [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7]) start .normal afterQuery
      (argsSize [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7]+cQ+1) := by
    apply runs_call_iff.mpr
    refine ⟨[b,e,base,lo,up,f,F.limbs,heap],queryCoordinateBody (op 1) store,oQ,stQ,cQ,
      by dsimp only [start]; eval_expr,hquery,hrQ,rfl,?_,rfl⟩
    cases stQ
    rfl
  obtain ⟨o,st,cTail,hrTail,⟨hpost,hrep,hphi,hmeta⟩,hTailCost⟩ :=
    reportedEdgeTail_runs F A G m κ α rate allocation R himpl.1 hcoefficient hflag s x xQ
      e base lo up f c r a one mn mx E ld gd heap oQ.value mem stQ.mem pos stQ.pos ω
      hwords hpreCopy hQpost hQrep hQmeta
  refine ⟨o,st,(argsSize [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7]+cQ+1)+cTail+1,
    xQ,?_,hpost,hrep,hmeta,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨afterQuery,_,cTail,hcall,hrTail,rfl⟩)
  · rw [← hphi]
    simp only [argsSize_cons,argsSize_nil,Expr.size_reg]
    omega

theorem reportedEdge_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init query store coefficient flag b q K sourceEnd : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A G m κ α rate allocation))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (s : A.State) (x : R.τ)
    (e base lo up f c r a one mn mx E ld gd heap : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem) :
    ∃ o st cost x',Runs w p ω (reportedEdgeBody query coefficient flag)
        (startState [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem pos) o st cost ∧
      (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
        [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem o.value st.mem ∧
      R.rep b s x' st.mem ∧
      (∀ z,R.foot b x' z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b x' st.mem≤
        (minRatioMachineContract F A G m κ α rate allocation).cost 1 s [b,e,heap] mem+
        R.phi b x mem+Num.IPM.lengthCost F.limbs F.fmt.precision E+
        Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+3500 :=
  reportedEdge_runs_with_potential_at F A G m κ α rate allocation R himpl hstore hquery
    hcoefficient hflag s x e base lo up f c r a one mn mx E ld gd heap mem pos ω hwords hpre

/-- The linked reported-edge entry meets its complete machine contract.
Its numerical and DS calls are the proved component procedures; the
strong run theorem above retains the credit used by the enclosing loop. -/
theorem reportedEdge_meetsContract_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init query store coefficient flag b q K sourceEnd entry : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A G m κ α rate allocation initPre))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hp : p.procs[entry]?=some (reportedEdgeBody query coefficient flag)) (s : A.State) (x : R.τ) :
    MeetsContract w p entry (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  have hpreCopy := hpre
  obtain ⟨e,base,lo,up,f,c,r,a,one,mn,mx,E,ld,gd,heap,heq,_⟩ := hpre
  subst args
  obtain ⟨o,st,cost,x',hr,hpost,_,_,hcost⟩ := reportedEdge_runs_with_potential_at F A G m κ α rate allocation R
    himpl hstore hquery hcoefficient hflag s x e base lo up f c r a one mn mx E ld gd heap mem pos ω hwords hpreCopy
  refine ⟨o,st,cost,hr,hpost,?_⟩
  change cost≤(minRatioMachineContract F A G m κ α rate allocation).cost 1 s [b,e,heap] mem+
    R.phi b x mem+Num.IPM.lengthCost F.limbs F.fmt.precision E+
    Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+3500
  omega

theorem reportedEdge_meetsContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init query store coefficient flag b q K sourceEnd entry : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A G m κ α rate allocation))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hp : p.procs[entry]?=some (reportedEdgeBody query coefficient flag)) (s : A.State) (x : R.τ) :
    MeetsContract w p entry (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd) :=
  reportedEdge_meetsContract_at F A G m κ α rate allocation R himpl hstore hquery hcoefficient hflag hp s x

end MinCostFlow.IPM.Machine
