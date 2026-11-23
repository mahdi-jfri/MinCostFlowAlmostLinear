module

public import MinCostFlow.IPM.Machine.DetectRefreshRead
public import MinCostFlow.IPM.Machine.DetectRefreshArgs
public import MinCostFlow.IPM.Machine.DetectRefreshRefreshInput
public import MinCostFlow.IPM.Machine.DetectRefreshRecordRun
public import MinCostFlow.IPM.Machine.ReportedEdgesProgram

/-!
# Executing checked refresh after the actual Detect result

Decode the stable report and derive the full checked-list input and
word packet from the combined-stage input. Call the actual verified
refresh entry, then its actual report/status continuation. Retain the
same concrete credit across the call, counting work by the actual
reported cardinality and stopping numeric work at the first rejection.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual post-Detect continuation meets the complete combined
output and retains final DS credit. Every refresh input and evaluated
argument follows from the original layout and actual Detect result. -/
theorem detectRefreshTail_runs_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init query store coefficient flag edge refresh record b q K sourceEnd tableEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A G m κ α rate allocation initPre))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hrefresh : p.procs[refresh]?=some (reportedEdgesBody edge flag))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (s : A.State) (x detected : R.τ)
    (names base lo up f heap c r a one mn mx E ld gd dHeap : ℕ)
    (mem : ℕ → ℕ) (parent : State) (ω : ℕ → Bool)
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hwords : ∀ z∈[b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hdetect : (detectNamesContract F A G m κ α rate allocation R b s x).post [b,m,heap] mem dHeap parent.mem)
    (hDrep : R.rep b (A.detect s).2 detected parent.mem)
    (hDmeta : ∀ z,R.foot b detected z → z<dHeap ∧ (R.foot b x z ∨ heap≤z))
    (hDbefore : ∀ z,R.foot b detected z → z<parent.mem (dHeap-1))
    (hregs : ∀ j<20,j≠1 → j≠2 → j≠8 → parent.regs j=
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m].getD j 0)
    (hendpoint : parent.regs 20=dHeap) :
    ∃ o st cost refreshed,Runs w p ω (detectRefreshTail refresh record) parent o st cost ∧
      (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).post
        [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem o.value st.mem ∧
      R.rep b (A.detect s).2 refreshed st.mem ∧
      (∀ z,R.foot b refreshed z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b refreshed st.mem≤
        (A.detect s).1.card*reportedEdgesCharge F m E rate+R.phi b detected parent.mem+200 := by
  have hRpre := detectRefresh_refresh_pre F A G m κ α rate allocation R hpre hdetect hDrep hDmeta hDbefore
  have hRwords := reportedEdges_input_words F A G m rate allocation R hRpre (reportedEdges_fixed_words hwords)
  have hmW : m<2^w := hwords _ (by simp)
  let pointer := parent.mem (dHeap-1)
  let afterRead : State := {parent with regs:=Function.update (Function.update parent.regs 21 pointer) 22 (A.detect s).1.card}
  have hrRead : Runs w p ω detectRefreshRead parent .normal afterRead 9 :=
    detectRefreshRead_runs F A G m κ α rate allocation R parent ω hpre hdetect hendpoint hmW
  have hfixedRead : ∀ j<20,j≠1 → j≠2 → j≠8 → afterRead.regs j=
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m].getD j 0 := by
    intro j hj h1 h2 h8
    dsimp only [afterRead]
    rw [Function.update_of_ne (by omega : j≠22),Function.update_of_ne (by omega : j≠21)]
    exact hregs j hj h1 h2 h8
  have hargs := detectRefreshArgs_eval afterRead b names base lo up f F.limbs heap c r a one mn mx
    F.fmt.precision E ld gd m dHeap pointer (A.detect s).1.card hfixedRead
    (by simpa only [afterRead,Function.update_of_ne (by decide : 20≠22),Function.update_of_ne (by decide : 20≠21)] using hendpoint)
    (by simp [afterRead]) (by simp [afterRead]) hRwords
  obtain ⟨oR,stR,cR,refreshed,hrR,hRpost,hRrep,hRmeta,hRcost⟩ :=
    reportedEdges_runs_with_potential_at F A G m κ α rate allocation R himpl hstore hquery hcoefficient
      hflag hedge (A.detect s).2 detected (pointer+1) (A.detect s).1.card base lo up f dHeap c r a one mn mx E ld gd
      parent.mem parent.pos ω hRwords hRpre
  let afterRefresh : State := ⟨stR.mem,Function.update afterRead.regs 23 oR.value,stR.pos⟩
  have hrCall : Runs w p ω (.call 23 refresh detectRefreshArgs) afterRead .normal afterRefresh
      (argsSize detectRefreshArgs+cR+1) := by
    apply runs_call_iff.mpr
    refine ⟨[b,pointer+1,(A.detect s).1.card,base,lo,up,f,F.limbs,dHeap,c,r,a,one,mn,mx,
      F.fmt.precision,E,ld,gd,m],reportedEdgesBody edge flag,oR,stR,cR,hargs,hrefresh,hrR,rfl,?_,rfl⟩
    cases stR
    rfl
  obtain ⟨o,st,cRecord,hrRecord,⟨hpost,hrep,hphi,hmeta⟩,hcRecord⟩ :=
    detectRefreshRecordTail_runs F A G m κ α rate allocation R himpl.1 hrecord afterRefresh ω
      hpre hdetect hDrep hDmeta hDbefore hRpost hRrep hRmeta
      (by simp [afterRefresh]) (by simp [afterRefresh,afterRead,pointer])
  have hrRest : Runs w p ω (.call 23 refresh detectRefreshArgs ;; detectRefreshRecordTail record)
      afterRead o st ((argsSize detectRefreshArgs+cR+1)+cRecord+1) :=
    runs_seq_iff.mpr (Or.inr ⟨afterRefresh,_,cRecord,hrCall,hrRecord,rfl⟩)
  refine ⟨o,st,9+(argsSize detectRefreshArgs+cR+1)+cRecord+2,refreshed,?_,hpost,hrep,hmeta,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨afterRead,9,_,hrRead,hrRest,by omega⟩)
  · rw [← hphi]
    dsimp only [afterRefresh]
    simp only [detectRefreshArgs_size]
    omega

theorem detectRefreshTail_runs {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init query store coefficient flag edge refresh record b q K sourceEnd tableEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A G m κ α rate allocation))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hrefresh : p.procs[refresh]?=some (reportedEdgesBody edge flag))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (s : A.State) (x detected : R.τ)
    (names base lo up f heap c r a one mn mx E ld gd dHeap : ℕ)
    (mem : ℕ → ℕ) (parent : State) (ω : ℕ → Bool)
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hwords : ∀ z∈[b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hdetect : (detectNamesContract F A G m κ α rate allocation R b s x).post [b,m,heap] mem dHeap parent.mem)
    (hDrep : R.rep b (A.detect s).2 detected parent.mem)
    (hDmeta : ∀ z,R.foot b detected z → z<dHeap ∧ (R.foot b x z ∨ heap≤z))
    (hDbefore : ∀ z,R.foot b detected z → z<parent.mem (dHeap-1))
    (hregs : ∀ j<20,j≠1 → j≠2 → j≠8 → parent.regs j=
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m].getD j 0)
    (hendpoint : parent.regs 20=dHeap) :
    ∃ o st cost refreshed,Runs w p ω (detectRefreshTail refresh record) parent o st cost ∧
      (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).post
        [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem o.value st.mem ∧
      R.rep b (A.detect s).2 refreshed st.mem ∧
      (∀ z,R.foot b refreshed z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b refreshed st.mem≤
        (A.detect s).1.card*reportedEdgesCharge F m E rate+R.phi b detected parent.mem+200 :=
  detectRefreshTail_runs_at F A G m κ α rate allocation R himpl hstore hquery hcoefficient hflag
    hedge hrefresh hrecord s x detected names base lo up f heap c r a one mn mx E ld gd dHeap mem
    parent ω hpre hwords hdetect hDrep hDmeta hDbefore hregs hendpoint

end MinCostFlow.IPM.Machine
