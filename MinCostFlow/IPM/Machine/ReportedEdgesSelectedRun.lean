module

public import MinCostFlow.IPM.Machine.ReportedEdgesIteration
public import MinCostFlow.IPM.Machine.ReportedEdgesMemberInput
public import MinCostFlow.IPM.Machine.ReportedEdgesMemberWords
public import MinCostFlow.IPM.Machine.ReportedEdgesArgs

/-!
# Executing an iteration from the full list input

Derive the selected call's numeric precondition, pointer bounds and
argument evaluation from the list input and fixed registers. The name
address may be expressed using the original counter and base or a
logical suffix of the same list. This lets the loop invariant advance
without modifying the fixed table registers.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A valid selected name in the full list layout executes the complete
checked iteration. No per-edge procedure precondition, word packet or
argument-evaluation premise is assumed independently. -/
theorem reportedEdges_selected_run_at {w : ℕ} (F : MinRatioFormat w)
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
    (names count base lo up f heap c r a one mn mx E ld gd i e : ℕ)
    (parent : State) (ω : ℕ → Bool) (hw : 1<2^w)
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem)
    (hwords : ∀ z∈[b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hregs : ∀ j<20,j≠1 → j≠2 → j≠8 → parent.regs j=
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m].getD j 0)
    (hheap : parent.regs 21=heap) (hi : i<count)
    (haddress : parent.regs 1+parent.regs 20=names+i) (hread : parent.mem (names+i)=e) :
    ∃ o st cost v x',Runs w p ω (reportedEdgesLoopBody entry) parent o st cost ∧
      (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
        [b,e,base+e*F.limbs,lo+e*F.limbs,up+e*F.limbs,f+e*F.limbs,F.limbs,heap,
          c+e*F.limbs,r,a,one,mn,mx,F.fmt.precision,E,ld+e*F.limbs,gd+e*F.limbs,m]
        parent.mem v st.mem ∧ R.rep b s x' st.mem ∧
      (∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heap≤z)) ∧
      (if st.mem (v-1)=1 then o=.normal ∧ st.regs 21=v else o=.returned v) ∧
      (∀ j<21,st.regs j=parent.regs j) ∧
      cost+R.phi b x' st.mem≤
        (minRatioMachineContract F A G m κ α rate allocation).cost 1 s [b,e,heap] parent.mem+
        R.phi b x parent.mem+Num.IPM.lengthCost F.limbs F.fmt.precision E+
        Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+3621 := by
  have hselected := reportedEdges_member_pre F A G m κ α rate allocation R hpre hi hread
  obtain ⟨hslot,hoff,hcalleeWords⟩ := reportedEdges_member_words F A G m rate allocation R hpre hwords hi hread
  let afterRead : State := ⟨parent.mem,
    Function.update (Function.update parent.regs 22 e) 23 (e*F.limbs),parent.pos⟩
  have hfixed : ∀ j<20,j≠1 → j≠2 → j≠8 → afterRead.regs j=
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m].getD j 0 := by
    intro j hj h1 h2 h8
    dsimp only [afterRead]
    simpa only [Function.update_of_ne (by omega : j≠23),Function.update_of_ne (by omega : j≠22)]
      using hregs j hj h1 h2 h8
  have hargs := reportedEdgesCallArgs_eval afterRead b names count base lo up f F.limbs heap
    c r a one mn mx F.fmt.precision E ld gd m heap e hfixed
    (by dsimp only [afterRead]; simpa using hheap)
    (by simp [afterRead]) (by simp [afterRead]) hcalleeWords
  have hL : parent.regs 7=F.limbs := by
    simpa only [List.getD_cons_zero,List.getD_cons_succ] using
      hregs 7 (by decide) (by decide) (by decide) (by decide)
  exact reportedEdgesLoopBody_runs_at F A G m κ α rate allocation R himpl hstore hquery hcoefficient
    hflag hp s x e (base+e*F.limbs) (lo+e*F.limbs) (up+e*F.limbs) (f+e*F.limbs)
    (c+e*F.limbs) r a one mn mx E (ld+e*F.limbs) (gd+e*F.limbs) heap
    (parent.regs 1) (parent.regs 20) parent ω hw rfl rfl hL
    (by rw [haddress]; exact hread) (by rw [haddress]; exact hslot) hoff hargs hcalleeWords hselected

theorem reportedEdges_selected_run {w : ℕ} (F : MinRatioFormat w)
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
    (names count base lo up f heap c r a one mn mx E ld gd i e : ℕ)
    (parent : State) (ω : ℕ → Bool) (hw : 1<2^w)
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] parent.mem)
    (hwords : ∀ z∈[b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hregs : ∀ j<20,j≠1 → j≠2 → j≠8 → parent.regs j=
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m].getD j 0)
    (hheap : parent.regs 21=heap) (hi : i<count)
    (haddress : parent.regs 1+parent.regs 20=names+i) (hread : parent.mem (names+i)=e) :
    ∃ o st cost v x',Runs w p ω (reportedEdgesLoopBody entry) parent o st cost ∧
      (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
        [b,e,base+e*F.limbs,lo+e*F.limbs,up+e*F.limbs,f+e*F.limbs,F.limbs,heap,
          c+e*F.limbs,r,a,one,mn,mx,F.fmt.precision,E,ld+e*F.limbs,gd+e*F.limbs,m]
        parent.mem v st.mem ∧ R.rep b s x' st.mem ∧
      (∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heap≤z)) ∧
      (if st.mem (v-1)=1 then o=.normal ∧ st.regs 21=v else o=.returned v) ∧
      (∀ j<21,st.regs j=parent.regs j) ∧
      cost+R.phi b x' st.mem≤
        (minRatioMachineContract F A G m κ α rate allocation).cost 1 s [b,e,heap] parent.mem+
        R.phi b x parent.mem+Num.IPM.lengthCost F.limbs F.fmt.precision E+
        Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+3621 :=
  reportedEdges_selected_run_at F A G m κ α rate allocation R himpl hstore hquery hcoefficient
    hflag hp s x names count base lo up f heap c r a one mn mx E ld gd i e parent ω hw hpre
    hwords hregs hheap hi haddress hread

end MinCostFlow.IPM.Machine
