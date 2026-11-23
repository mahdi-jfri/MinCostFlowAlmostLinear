module

public import MinCostFlow.IPM.Machine.DetectRefreshTail
import MinCostFlow.IPM.Machine.DetectNamesProgram
import Mathlib.Tactic.Ring
import WordRAM.Tactic

/-!
# Complete machine proof for one Detect/refresh stage

Run actual stable Detect/name preparation, then the verified decode,
checked refresh and status-record continuation. The concrete post-Detect
credit is consumed only once. The final bound is linear in the actual
report cardinality, with the two DS charges and numerical work explicit.
No numeric computation follows a rejected refresh.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

private theorem combined_work_bound (r a n p₀ p₁ p₂ d t : ℕ)
    (hD : d+p₁≤r*(1+n)+p₀+17*n+200)
    (hT : t+p₂≤n*(r+a+3630)+p₁+200) :
    d+t+5+p₂≤(n+1)*(2*r+a+4200)+p₀ := by
  have hs : d+t+5+p₂≤r*(1+n)+p₀+17*n+200+n*(r+a+3630)+200+5 := by omega
  calc
    d+t+5+p₂≤r*(1+n)+p₀+17*n+200+n*(r+a+3630)+200+5 := hs
    _ ≤ (r*(1+n)+p₀+17*n+200+n*(r+a+3630)+200+5)+(553*n+r+a+3795) :=
      Nat.le_add_right _ _
    _ = (n+1)*(2*r+a+4200)+p₀ := by ring

/-- The complete actual Detect/refresh stage meets the composed output
protocol and retains final concrete DS credit. Its rate is linear in
`card+1`, with no extra factor of the graph's edge count. -/
theorem detectRefresh_runs_with_potential_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record b q K sourceEnd tableEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A G m κ α rate allocation initPre))
    (hrawDetect : p.procs[rawDetect]?=some (minRatioDetectBody (op 2)))
    (hdetect : p.procs[detect]?=some (detectNamesBody rawDetect snapshot))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hrefresh : p.procs[refresh]?=some (reportedEdgesBody edge flag))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (s : A.State) (x : R.τ)
    (hsnapshot : MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (names base lo up f heap c r a one mn mx E ld gd : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem) :
    ∃ o st cost final,Runs w p ω (detectRefreshBody detect refresh record)
        (startState [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem pos) o st cost ∧
      (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).post
        [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem o.value st.mem ∧
      R.rep b (A.detect s).2 final st.mem ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤
        (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).cost
          [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem := by
  have hDpre := (detectRefresh_detect_pre F A G m κ α rate allocation R hpre).1
  have hDwords : ∀ z∈[b,m,heap],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with hz | hz | hz
    all_goals subst z
    all_goals exact hwords _ (by simp)
  obtain ⟨oD,stD,cD,detected,hrD,hDpost,hDrep,hDmeta,hDbefore,hDcost⟩ :=
    detectNames_runs_with_potential_at F A G m κ α rate allocation R himpl hrawDetect s x hsnapshot
      heap mem pos ω hDwords hDpre
  let start := startState
    [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem pos
  let afterDetect : State := ⟨stD.mem,Function.update start.regs 20 oD.value,stD.pos⟩
  have hcall : Runs w p ω (.call 20 detect [.reg 0,.reg 19,.reg 8]) start .normal afterDetect
      (argsSize [.reg 0,.reg 19,.reg 8]+cD+1) := by
    apply runs_call_iff.mpr
    refine ⟨[b,m,heap],detectNamesBody rawDetect snapshot,oD,stD,cD,
      by dsimp only [start]; eval_expr,hdetect,hrD,rfl,?_,rfl⟩
    cases stD
    rfl
  have hregs : ∀ j<20,j≠1 → j≠2 → j≠8 → afterDetect.regs j=
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m].getD j 0 := by
    intro j hj _ _ _
    dsimp only [afterDetect]
    rw [Function.update_of_ne (by omega : j≠20)]
    rfl
  obtain ⟨o,st,cTail,final,hrTail,hpost,hrep,hmeta,hTailCost⟩ :=
    detectRefreshTail_runs_at F A G m κ α rate allocation R himpl hstore hquery hcoefficient hflag hedge
      hrefresh hrecord s x detected names base lo up f heap c r a one mn mx E ld gd oD.value mem afterDetect ω
      hpre hwords hDpost hDrep hDmeta hDbefore hregs (by simp [afterDetect])
  refine ⟨o,st,(argsSize [.reg 0,.reg 19,.reg 8]+cD+1)+cTail+1,final,?_,hpost,hrep,hmeta,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨afterDetect,_,cTail,hcall,hrTail,rfl⟩)
  · change cD+R.phi b detected stD.mem≤rate m*(1+(A.detect s).1.card)+R.phi b x mem+17*(A.detect s).1.card+200 at hDcost
    dsimp only [afterDetect] at hTailCost
    let work := Num.IPM.lengthCost F.limbs F.fmt.precision E+
      Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs
    have ht : cTail+R.phi b final st.mem≤(A.detect s).1.card*(rate m+work+3630)+R.phi b detected stD.mem+200 := by
      simpa only [reportedEdgesCharge,work,Nat.add_assoc] using hTailCost
    have hc := combined_work_bound (rate m) work (A.detect s).1.card
      (R.phi b x mem) (R.phi b detected stD.mem) (R.phi b final st.mem) cD cTail hDcost ht
    have hc' : cD+cTail+5+R.phi b final st.mem≤((A.detect s).1.card+1)*
        (2*rate m+Num.IPM.lengthCost F.limbs F.fmt.precision E+
          Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+4200)+R.phi b x mem := by
      simpa only [work,Nat.add_assoc] using hc
    change (argsSize [.reg 0,.reg 19,.reg 8]+cD+1)+cTail+1+R.phi b final st.mem≤_
    simp only [detectRefreshContract,List.getD_cons_zero,List.getD_cons_succ,
      argsSize_cons,argsSize_nil,Expr.size_reg]
    omega

theorem detectRefresh_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record b q K sourceEnd tableEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A G m κ α rate allocation))
    (hrawDetect : p.procs[rawDetect]?=some (minRatioDetectBody (op 2)))
    (hdetect : p.procs[detect]?=some (detectNamesBody rawDetect snapshot))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hrefresh : p.procs[refresh]?=some (reportedEdgesBody edge flag))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (s : A.State) (x : R.τ)
    (hsnapshot : MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (names base lo up f heap c r a one mn mx E ld gd : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem) :
    ∃ o st cost final,Runs w p ω (detectRefreshBody detect refresh record)
        (startState [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem pos) o st cost ∧
      (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).post
        [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem o.value st.mem ∧
      R.rep b (A.detect s).2 final st.mem ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤
        (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).cost
          [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem :=
  detectRefresh_runs_with_potential_at F A G m κ α rate allocation R himpl hrawDetect hdetect hstore
    hquery hcoefficient hflag hedge hrefresh hrecord s x hsnapshot names base lo up f heap c r a one
    mn mx E ld gd mem pos ω hwords hpre

/-- The complete linked combined stage meets its explicit machine
contract. All three components are the verified actual procedures. -/
theorem detectRefresh_meetsContract_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record entry b q K sourceEnd tableEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A G m κ α rate allocation initPre))
    (hrawDetect : p.procs[rawDetect]?=some (minRatioDetectBody (op 2)))
    (hdetect : p.procs[detect]?=some (detectNamesBody rawDetect snapshot))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hrefresh : p.procs[refresh]?=some (reportedEdgesBody edge flag))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hp : p.procs[entry]?=some (detectRefreshBody detect refresh record)) (s : A.State) (x : R.τ)
    (hsnapshot : MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1)) :
    MeetsContract w p entry (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  have hpreCopy := hpre
  obtain ⟨names,base,lo,up,f,heap,c,r,a,one,mn,mx,E,ld,gd,heq,_⟩ := hpre
  subst args
  obtain ⟨o,st,cost,final,hr,hpost,_,_,hc⟩ := detectRefresh_runs_with_potential_at F A G m κ α rate allocation R
    himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord s x hsnapshot
      names base lo up f heap c r a one mn mx E ld gd mem pos ω hwords hpreCopy
  refine ⟨o,st,cost,hr,hpost,?_⟩
  exact (Nat.le_add_right cost (R.phi b final st.mem)).trans hc

theorem detectRefresh_meetsContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record entry b q K sourceEnd tableEnd : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A G m κ α rate allocation))
    (hrawDetect : p.procs[rawDetect]?=some (minRatioDetectBody (op 2)))
    (hdetect : p.procs[detect]?=some (detectNamesBody rawDetect snapshot))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (op 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hrefresh : p.procs[refresh]?=some (reportedEdgesBody edge flag))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hp : p.procs[entry]?=some (detectRefreshBody detect refresh record)) (s : A.State) (x : R.τ)
    (hsnapshot : MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1)) :
    MeetsContract w p entry (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd) :=
  detectRefresh_meetsContract_at F A G m κ α rate allocation R himpl hrawDetect hdetect hstore
    hquery hcoefficient hflag hedge hrefresh hrecord hp s x hsnapshot

end MinCostFlow.IPM.Machine
