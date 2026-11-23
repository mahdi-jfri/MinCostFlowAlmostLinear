module

public import MinCostFlow.IPM.Machine.MinRatioQueryInput
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Querying and guarding one stored flow coordinate

Algorithm 7 of Chen et al., arXiv:2203.00671v2 (page 69), recovers a
reported coordinate as its base plus the accumulated data-structure flow.
This procedure performs the actual Query, reserves its full answer block,
and calls the wide guarded coordinate writer. Its proof keeps the new DS
potential through that write, so the call costs can telescope in the loop.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[handle,edge,base,lower,upper,destination,L,heap]`. -/
def queryCoordinateBody (query store : ℕ) : Stmt :=
  .call 8 query [.reg 0,.reg 1,.reg 7] ;;
  .assign 9 (.bin .add (.reg 8) (.reg 6)) ;;
  .call 10 store [.reg 2,.reg 7,.reg 3,.reg 4,.reg 5,.reg 6,.reg 9] ;;
  .ret (.reg 10)

/-- Query, answer reservation, and guarded coordinate recovery contain
no random instruction. -/
theorem queryCoordinateBody_noRand (query store : ℕ) : (queryCoordinateBody query store).NoRand := by
  simp [queryCoordinateBody,Stmt.NoRand]

/-- The exact Query and coordinate-write postconditions, together with
the preserved data-structure representation. Source and destination
blocks belong to the caller and avoid the old DS footprint. -/
def queryCoordinateContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (b : ℕ) (s : A.State) (x : R.τ) : Contract :=
  let D := minRatioMachineContract F A G m κ α rate allocation
  { pre := fun args mem => ∃ e base lo up dst heap,
      args=[b,e,base,lo,up,dst,F.limbs,heap] ∧
      (minRatioQueryContract w R D b s x).pre [b,e,F.limbs,heap] mem ∧
      Num.Valid mem base F.fmt.limbBits F.limbs ∧
      Num.Valid mem lo F.fmt.limbBits F.limbs ∧ Num.Valid mem up F.fmt.limbBits F.limbs ∧
      base+F.limbs≤heap ∧ lo+F.limbs≤heap ∧ up+F.limbs≤heap ∧ dst+F.limbs≤heap ∧
      (∀ i<F.limbs,¬ R.foot b x (base+i)) ∧
      (∀ i<F.limbs,¬ R.foot b x (lo+i)) ∧
      (∀ i<F.limbs,¬ R.foot b x (up+i)) ∧
      (∀ z,R.foot b x z → z<dst ∨ dst+F.limbs≤z) ∧
      heap+D.space 1 s [b,e,heap] mem+F.limbs+(1+10*F.limbs)<2^w
    post := fun args mem v mem' => ∃ pad queryMem x',
      (minRatioQueryContract w R D b s x).post
        [b,args.getD 1 0,F.limbs,heapArg args] mem pad queryMem ∧
      (storeCoordinateContract w F.fmt.limbBits).post
        [args.getD 2 0,heapArg args,args.getD 3 0,args.getD 4 0,args.getD 5 0,F.limbs,pad]
        queryMem v mem' ∧ R.rep b s x' queryMem ∧ R.rep b s x' mem' ∧
      (∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heapArg args≤z))
    cost := fun args mem => D.cost 1 s [b,args.getD 1 0,heapArg args] mem+
      R.phi b x mem+1100*F.limbs+1500 }

/-- The actual Query and guarded recovery preserve the new abstract DS
state and its potential. Both successful writes and rejected candidates
have the same explicit amortized cost bound. -/
theorem queryCoordinate_runs_with_potential_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init store b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A G m κ α rate allocation initPre))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (s : A.State) (x : R.τ) (e base lo up dst heap : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,e,base,lo,up,dst,F.limbs,heap],z<2^w)
    (hpre : (queryCoordinateContract F A G m κ α rate allocation R b s x).pre
      [b,e,base,lo,up,dst,F.limbs,heap] mem) :
    ∃ o st cost x',Runs w p ω (queryCoordinateBody (op 1) store)
        (startState [b,e,base,lo,up,dst,F.limbs,heap] mem pos) o st cost ∧
      (queryCoordinateContract F A G m κ α rate allocation R b s x).post
        [b,e,base,lo,up,dst,F.limbs,heap] mem o.value st.mem ∧
      R.rep b s x' st.mem ∧
      (∀ z,R.foot b x' z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b x' st.mem≤
        (minRatioMachineContract F A G m κ α rate allocation).cost 1 s [b,e,heap] mem+
        R.phi b x mem+1100*F.limbs+1500 := by
  let D := minRatioMachineContractAt F A G m κ α rate allocation initPre
  obtain ⟨e',base',lo',up',dst',heap',heq,hqp,hbase,hlo,hup,
    hbaseEnd,hloEnd,hupEnd,hdstEnd,hbaseFoot,hloFoot,hupFoot,hdstFoot,hspace⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨e',L',heap',heq,hrep,hoperation,hfoot,hzero,_⟩ := hqp
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  change heap+D.space 1 s [b,e,heap] mem+F.limbs+(1+10*F.limbs)<2^w at hspace
  have hcallWords : ∀ z∈[b,e,heap],z<2^w := by
    intro z hz
    apply hwords z
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
    tauto
  obtain ⟨vQ,memQ,posQ,cQ,sQ,xQ,hrQ,hrepQ,hpostQ,hrespect,hcostQ⟩ :=
    runs_operation_with_potential (R:=R) (D:=D) (r:=8) (i:=1)
      (args:=[.reg 0,.reg 1,.reg 7])
      (st:=startState [b,e,base,lo,up,dst,F.limbs,heap] mem pos)
      ω himpl (by eval_expr) hcallWords rfl hrep hoperation hfoot hzero
      (by change heap+D.space 1 s [b,e,heap] mem<2^w; omega)
  change R.rep b sQ xQ memQ at hrepQ
  change D.post 1 s [b,e,heap] mem sQ memQ at hpostQ
  have hstate : sQ=s := hpostQ.1
  subst sQ
  change R.Respects (R.foot b x) heap (D.space 1 s [b,e,heap] mem) mem vQ b xQ memQ at hrespect
  obtain ⟨hQlo,hQhi,hQzero,hQframe,hQfoot⟩ := hrespect
  have hpadW : vQ+F.limbs<2^w := by omega
  have hwrapped : (minRatioQueryContract w R D b s x).post
      [b,e,F.limbs,heap] mem (vQ+F.limbs) memQ := by
    refine ⟨vQ,s,xQ,rfl,hQlo,hQhi,hQzero.mono (by omega),hrepQ,hpostQ,hQframe,?_,hQfoot⟩
    intro z hz
    rcases hQfoot z hz with hh | hh
    · exact (hfoot z hh).trans_le (by omega)
    · omega
  have hnumeric := storeCoordinate_pre_after_query F A G m κ α rate allocation R hwrapped
    hbase hlo hup hbaseEnd hloEnd hupEnd hdstEnd hbaseFoot hloFoot hupFoot
    (by omega : vQ+F.limbs+(1+10*F.limbs)<2^w)
  let stQ : State := ⟨memQ,Function.update (startState [b,e,base,lo,up,dst,F.limbs,heap] mem pos).regs 8 vQ,posQ⟩
  let stPad : State := {stQ with regs:=Function.update stQ.regs 9 (vQ+F.limbs)}
  have hassign : Runs w p ω (.assign 9 (.bin .add (.reg 8) (.reg 6))) stQ .normal stPad 4 := by
    apply runs_assign_iff.mpr
    exact ⟨vQ+F.limbs,by dsimp only [stQ]; eval_expr,rfl,rfl,rfl⟩
  have hnumWords : ∀ z∈[base,heap,lo,up,dst,F.limbs,vQ+F.limbs],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with hz | hz | hz | hz | hz | hz | rfl
    all_goals first | exact hz ▸ hwords _ (by simp) | exact hpadW
  obtain ⟨stN,cN,vN,hrN,hpostN,hregN,_,hcostN⟩ :=
    runs_call_of_meetsContract (r:=10)
      (args:=[.reg 2,.reg 7,.reg 3,.reg 4,.reg 5,.reg 6,.reg 9]) (st:=stPad)
      hstore (by dsimp only [stPad,stQ]; eval_expr) hnumWords hnumeric ω
  change (storeCoordinateContract w F.fmt.limbBits).post
    [base,heap,lo,up,dst,F.limbs,vQ+F.limbs] memQ vN stN.mem at hpostN
  have hnewFoot : ∀ z,R.foot b xQ z → z<vQ+F.limbs ∧ (z<dst ∨ dst+F.limbs≤z) := by
    intro z hz
    rcases hQfoot z hz with hold | hnew
    · exact ⟨(hfoot z hold).trans_le (by omega),hdstFoot z hold⟩
    · exact ⟨by omega,Or.inr (by omega)⟩
  have hkeep := storeCoordinate_preserves_state R himpl.1 hpostN hrepQ hnewFoot
  have hret : Runs w p ω (.ret (.reg 10)) stN (.returned vN) stN 2 := by
    apply runs_ret_iff.mpr
    exact ⟨vN,by simp only [Expr.eval,hregN],rfl,rfl,rfl⟩
  have htail := runs_seq_iff.mpr (Or.inr ⟨stN,cN,2,hrN,hret,rfl⟩)
  have hrest := runs_seq_iff.mpr (Or.inr ⟨stPad,4,cN+2+1,hassign,htail,rfl⟩)
  refine ⟨.returned vN,stN,cQ+(4+(cN+2+1)+1)+1,xQ,?_,?_,hkeep.1,?_,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨stQ,cQ,4+(cN+2+1)+1,hrQ,hrest,rfl⟩)
  · refine ⟨vQ+F.limbs,memQ,xQ,hwrapped,hpostN,hrepQ,hkeep.1,?_⟩
    intro z hz
    have htop := (hnewFoot z hz).1
    have hretN := hpostN.1
    change vN=(vQ+F.limbs)+(1+10*F.limbs) at hretN
    refine ⟨by change z<vN; omega,?_⟩
    rcases hQfoot z hz with hold | hnew
    · exact Or.inl hold
    · exact Or.inr hnew.1
  · intro z hz
    have htop := (hnewFoot z hz).1
    have hretN := hpostN.1
    change vN=(vQ+F.limbs)+(1+10*F.limbs) at hretN
    refine ⟨by change z<vN; omega,?_⟩
    rcases hQfoot z hz with hold | hnew
    · exact Or.inl hold
    · exact Or.inr hnew.1
  · change cQ+(4+(cN+2+1)+1)+1+R.phi b xQ stN.mem≤
      D.cost 1 s [b,e,heap] mem+R.phi b x mem+1100*F.limbs+1500
    rw [← hkeep.2]
    change cQ+R.phi b xQ memQ≤argsSize [.reg 0,.reg 1,.reg 7]+1+
      D.cost 1 s [b,e,heap] mem+R.phi b x mem at hcostQ
    change cN≤argsSize [.reg 2,.reg 7,.reg 3,.reg 4,.reg 5,.reg 6,.reg 9]+
      (1100*F.limbs+1300)+1 at hcostN
    simp only [argsSize_cons,argsSize_nil,Expr.size_reg] at hcostQ hcostN
    omega

theorem queryCoordinate_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init store b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A G m κ α rate allocation))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (s : A.State) (x : R.τ) (e base lo up dst heap : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,e,base,lo,up,dst,F.limbs,heap],z<2^w)
    (hpre : (queryCoordinateContract F A G m κ α rate allocation R b s x).pre
      [b,e,base,lo,up,dst,F.limbs,heap] mem) :
    ∃ o st cost x',Runs w p ω (queryCoordinateBody (op 1) store)
        (startState [b,e,base,lo,up,dst,F.limbs,heap] mem pos) o st cost ∧
      (queryCoordinateContract F A G m κ α rate allocation R b s x).post
        [b,e,base,lo,up,dst,F.limbs,heap] mem o.value st.mem ∧
      R.rep b s x' st.mem ∧
      (∀ z,R.foot b x' z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b x' st.mem≤
        (minRatioMachineContract F A G m κ α rate allocation).cost 1 s [b,e,heap] mem+
        R.phi b x mem+1100*F.limbs+1500 :=
  queryCoordinate_runs_with_potential_at F A G m κ α rate allocation R himpl hstore s x e base lo up
    dst heap mem pos ω hwords hpre

/-- The one-coordinate entry meets its complete Query and guarded-write
contract under the two actual linked implementations. -/
theorem queryCoordinate_meetsContract_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init store b entry : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A G m κ α rate allocation initPre))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hp : p.procs[entry]?=some (queryCoordinateBody (op 1) store)) (s : A.State) (x : R.τ) :
    MeetsContract w p entry (queryCoordinateContract F A G m κ α rate allocation R b s x) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  have hpreCopy := hpre
  obtain ⟨e,base,lo,up,dst,heap,heq,_⟩ := hpre
  subst args
  obtain ⟨o,st,c,x',hr,hpost,_,_,hcost⟩ := queryCoordinate_runs_with_potential_at F A G m κ α rate allocation R
    himpl hstore s x e base lo up dst heap mem pos ω hwords hpreCopy
  refine ⟨o,st,c,hr,hpost,?_⟩
  change c≤(minRatioMachineContract F A G m κ α rate allocation).cost 1 s [b,e,heap] mem+
    R.phi b x mem+1100*F.limbs+1500
  omega

theorem queryCoordinate_meetsContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init store b entry : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A G m κ α rate allocation))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hp : p.procs[entry]?=some (queryCoordinateBody (op 1) store)) (s : A.State) (x : R.τ) :
    MeetsContract w p entry (queryCoordinateContract F A G m κ α rate allocation R b s x) :=
  queryCoordinate_meetsContract_at F A G m κ α rate allocation R himpl hstore hp s x

end MinCostFlow.IPM.Machine
