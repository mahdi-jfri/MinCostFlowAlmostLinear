module

public import MinCostFlow.IPM.Machine.ReportedEdgeProgram

/-!
# Retaining DS credit across the reported-edge call

The reported-list loop calls the reported-edge procedure from a parent
register state. Lift the proved procedure run to that actual call,
including argument evaluation and call cost. The resulting state keeps
all parent registers except the result register. The same concrete DS
state supplies the retained potential, so later calls can telescope it.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Calling the verified reported-edge entry preserves its functional
postcondition and amortized credit, with the exact call overhead. -/
theorem reportedEdge_call_with_potential_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init query store coefficient flag entry result b q K sourceEnd : ℕ}
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
    (args : List Expr) (parent : State) (ω : ℕ → Bool)
    (hargs : evalArgs w parent args=some
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m])
    (hwords : ∀ z∈[b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem) :
    ∃ v after cost x',Runs w p ω (.call result entry args) parent .normal after cost ∧
      (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
        [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem v after.mem ∧
      after.regs=Function.update parent.regs result v ∧ R.rep b s x' after.mem ∧
      (∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b x' after.mem≤
        (minRatioMachineContract F A G m κ α rate allocation).cost 1 s [b,e,heap] parent.mem+
        R.phi b x parent.mem+Num.IPM.lengthCost F.limbs F.fmt.precision E+
        Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+3500+argsSize args+1 := by
  obtain ⟨o,st,cost,x',hr,hpost,hrep,hfoot,hcost⟩ :=
    reportedEdge_runs_with_potential_at F A G m κ α rate allocation R himpl hstore hquery
      hcoefficient hflag s x e base lo up f c r a one mn mx E ld gd heap parent.mem parent.pos
      ω hwords hpre
  let after : State := ⟨st.mem,Function.update parent.regs result o.value,st.pos⟩
  refine ⟨o.value,after,argsSize args+cost+1,x',?_,hpost,rfl,hrep,hfoot,by dsimp only [after]; omega⟩
  apply runs_call_iff.mpr
  refine ⟨_,reportedEdgeBody query coefficient flag,o,st,cost,hargs,hp,hr,rfl,?_,rfl⟩
  cases st
  rfl

theorem reportedEdge_call_with_potential {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init query store coefficient flag entry result b q K sourceEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A G m κ α rate allocation))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hp : p.procs[entry]?=some (reportedEdgeBody query coefficient flag))
    (s : A.State) (x : R.τ)
    (e base lo up f c r a one mn mx E ld gd heap : ℕ)
    (args : List Expr) (parent : State) (ω : ℕ → Bool)
    (hargs : evalArgs w parent args=some
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m])
    (hwords : ∀ z∈[b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem) :
    ∃ v after cost x',Runs w p ω (.call result entry args) parent .normal after cost ∧
      (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
        [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem v after.mem ∧
      after.regs=Function.update parent.regs result v ∧ R.rep b s x' after.mem ∧
      (∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b x' after.mem≤
        (minRatioMachineContract F A G m κ α rate allocation).cost 1 s [b,e,heap] parent.mem+
        R.phi b x parent.mem+Num.IPM.lengthCost F.limbs F.fmt.precision E+
        Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+3500+argsSize args+1 :=
  reportedEdge_call_with_potential_at F A G m κ α rate allocation R himpl hstore hquery hcoefficient
    hflag hp s x e base lo up f c r a one mn mx E ld gd heap args parent ω hargs hwords hpre

end MinCostFlow.IPM.Machine
