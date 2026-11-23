module

public import MinCostFlow.IPM.Machine.EpochCompleteCall
public import MinCostFlow.IPM.Machine.EpochMaterializationRun
public import MinCostFlow.IPM.Machine.EpochLoopTrace
import Mathlib.Tactic.IntervalCases

/-!
# Composing the finite epoch with its actual full-coordinate pass

The lazy loop's returned bit controls the next call. On success, keep
the precise intermediate history and use its one-word return as the
input to the full pass. On failure, return the same state and bit.
The amortized credits telescope over these actual calls.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The complete epoch result records whether an actual full pass was
performed. On success the full report uses the finite epoch's ending
history. Its bit may still reject an out-of-range candidate. -/
def EpochCompletePost {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space finish : ℕ) (mem : ℕ → ℕ)
    (loopEnd : ℕ) (loopState : State) (loopCredit : R.τ) (certified : EpochPoint R.τ → Prop) (v : ℕ) (final : State) (credit : R.τ) : Prop :=
  if loopState.mem (loopEnd-1)=1 then
    ∃ Q : EpochPoint R.τ,
      EpochConditions F A I κ α rate allocation R L q K mem heap space finish finish Q ∧
      loopCredit=Q.credit ∧ certified Q ∧
      (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem loopEnd loopState.mem ∧
      let s := minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)
      let C := reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle s Q.credit
        q K L.sourceEnd L.tableEnd
      let args := (L.packet F I loopEnd).take 20
      C.pre args loopState.mem ∧ (∀ e∈(namedInstance I).E,∃ j<I.m,loopState.mem (L.names+j)=e) ∧
      C.post args loopState.mem v final.mem ∧ R.rep L.handle s credit final.mem
  else
    v=loopEnd ∧ final.mem=loopState.mem ∧ credit=loopCredit ∧ final.mem (v-1)=0

private theorem reportedEdgesBody_not_normal {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {edge flag cost : ℕ} {initial final : State}
    (h : Runs w p ω (reportedEdgesBody edge flag) initial .normal final cost) : False := by
  unfold reportedEdgesBody at h
  rcases runs_seq_iff.mp h with ⟨_,_,_,heq,_⟩ | ⟨_,_,_,_,hTail,_⟩
  · cases heq
  rcases runs_seq_iff.mp hTail with ⟨_,_,_,heq,_⟩ | ⟨_,_,_,_,hFinish,_⟩
  · cases heq
  unfold reportedEdgesFinish at hFinish
  rcases runs_seq_iff.mp hFinish with ⟨_,_,_,heq,_⟩ | ⟨_,_,_,_,hRet,_⟩
  · cases heq
  obtain ⟨_,_,heq,_,_⟩ := runs_ret_iff.mp hRet
  cases heq

set_option maxHeartbeats 350000 in
/-- Given the actual verified loop run, follow the complete caller
through its first failure or full read. It pays at most one full pass
and 60 additional Word RAM operations beyond the loop cost. -/
theorem epochComplete_runs_of_loop_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space finish loopEnd cost : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (loopState : State) (loopCredit : R.τ)
    (certified : EpochPoint R.τ → Prop)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init query store coefficient flag edge iterations read : ℕ} {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop
      (minRatioMachineContractAt F A (namedInstance I) I.m κ α rate allocation initPre))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (dsop 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hread : p.procs[read]?=some (reportedEdgesBody edge flag))
    {loopBody : Stmt} (hloopBody : p.procs[iterations]?=some loopBody)
    (hloop : Runs w p ω loopBody (startState (L.packet F I heap++[finish]) mem pos)
      (.returned loopEnd) loopState cost)
    (hwords : ∀ z∈L.packet F I 0,z<2^w) (hOne : 1<2^w) (hword : loopEnd<2^w)
    (htrace :
      if loopState.mem (loopEnd-1)=1 then
        ∃ Q : EpochPoint R.τ,EpochConditions F A I κ α rate allocation R L q K mem heap space finish finish Q ∧
          loopCredit=Q.credit ∧ certified Q ∧ (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem loopEnd loopState.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) loopCredit loopState.mem
      else loopState.mem (loopEnd-1)=0) :
    ∃ v final cost' credit,
      Runs w p ω (epochCompleteBody iterations read) (startState (L.packet F I heap++[finish]) mem pos)
        (.returned v) final cost' ∧ v<2^w ∧
      EpochCompletePost F A I κ α rate allocation R L q K heap space finish mem loopEnd loopState loopCredit
        certified v final credit ∧
      cost'+R.phi L.handle credit final.mem≤
        cost+R.phi L.handle loopCredit loopState.mem+I.m*reportedEdgesCharge F I.m L.exponent rate+160 := by
  let start := startState (L.packet F I heap++[finish]) mem pos
  let parent : State := ⟨loopState.mem,Function.update start.regs 26 loopEnd,loopState.pos⟩
  have hcall : Runs w p ω (.call 26 iterations epochCompleteIterationArgs) start .normal parent (cost+27) :=
    epochComplete_call_runs F I L heap finish mem pos ω hloopBody hloop
  have hparent : parent.regs 26=loopEnd := by simp [parent]
  by_cases hbit : loopState.mem (loopEnd-1)=1
  · rw [ite_eq_left hbit] at htrace
    obtain ⟨Q,hcond,hcredit,hcert,hflagPost,hrep⟩ := htrace
    have hrepQ : R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) Q.credit loopState.mem :=
      hcredit ▸ hrep
    obtain ⟨o,st,c,nextCredit,hRun,hpre,hcover,hout,hrep',_,hCost⟩ :=
      epochMaterialization_runs_with_potential_at F A I κ α rate allocation R L q K finish loopEnd Q loopState.mem
        himpl hstore hquery hcoefficient hflag hedge hcond hflagPost hrepQ
        (L.packet_words F I loopEnd hwords hword) loopState.pos ω
    cases o with
    | normal =>
      exact False.elim (reportedEdgesBody_not_normal hRun)
    | returned v =>
      have hargs : evalArgs w parent epochCompleteReadArgs=some ((L.packet F I loopEnd).take 20) :=
        epochComplete_read_args F I L heap finish loopEnd mem loopState.mem pos loopState.pos
      have htail := epochCompleteTail_success_runs parent ω hread hword hOne hparent
        hbit hargs hRun
      let final : State := {st with regs:=Function.update (Function.update parent.regs 27 1) 28 v}
      have hv : v<2^w := by
        obtain ⟨names,count,base,lo,up,f,heap',c,r,a,one,mn,mx,E,ld,gd,es,heq,
          _,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hspace⟩ := hpre
        change [L.handle,L.names,I.m,L.base,L.lower,L.upper,L.flow,F.limbs,loopEnd,L.cost,L.residual,
          L.alpha,L.one,L.slackMin,L.slackMax,F.fmt.precision,L.exponent,L.lengths,L.gradient,I.m]=_ at heq
        simp only [List.cons.injEq,and_true,true_and] at heq
        obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
        obtain ⟨_,_,_,_,hEnd,_⟩ := hout
        change v≤loopEnd+I.m*reportedEdgesScratch F I.m L.handle L.exponent allocation+1 at hEnd
        exact hEnd.trans_lt hspace.2.2
      refine ⟨v,final,cost+27+(c+(argsSize epochCompleteReadArgs+12))+1,nextCredit,?_,hv,?_,?_⟩
      · exact runs_seq_iff.mpr (Or.inr ⟨parent,_,_,hcall,htail,rfl⟩)
      · unfold EpochCompletePost
        rw [ite_eq_left hbit]
        exact ⟨Q,hcond,hcredit,hcert,hflagPost,hpre,hcover,hout,hrep'⟩
      · change cost+27+(c+(20+12))+1+R.phi L.handle nextCredit st.mem≤_
        rw [← hcredit] at hCost
        omega
  · rw [ite_eq_right hbit] at htrace
    have ht := epochCompleteTail_failure_runs p read parent ω loopEnd hword hOne hparent htrace
    let final : State := {parent with regs:=Function.update parent.regs 27 0}
    refine ⟨loopEnd,final,cost+38,loopCredit,?_,hword,?_,?_⟩
    · exact runs_seq_iff.mpr (Or.inr ⟨parent,cost+27,10,hcall,ht,by omega⟩)
    · unfold EpochCompletePost
      rw [ite_eq_right hbit]
      exact ⟨rfl,rfl,rfl,htrace⟩
    · change cost+38+R.phi L.handle loopCredit loopState.mem≤_
      omega

theorem epochComplete_runs_of_loop {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap space finish loopEnd cost : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (loopState : State) (loopCredit : R.τ)
    (certified : EpochPoint R.τ → Prop)
    {p : Program} {init query store coefficient flag edge iterations read : ℕ} {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (dsop 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hread : p.procs[read]?=some (reportedEdgesBody edge flag))
    {loopBody : Stmt} (hloopBody : p.procs[iterations]?=some loopBody)
    (hloop : Runs w p ω loopBody (startState (L.packet F I heap++[finish]) mem pos)
      (.returned loopEnd) loopState cost)
    (hwords : ∀ z∈L.packet F I 0,z<2^w) (hOne : 1<2^w) (hword : loopEnd<2^w)
    (htrace :
      if loopState.mem (loopEnd-1)=1 then
        ∃ Q : EpochPoint R.τ,EpochConditions F A I κ α rate allocation R L q K mem heap space finish finish Q ∧
          loopCredit=Q.credit ∧ certified Q ∧ (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem loopEnd loopState.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) loopCredit loopState.mem
      else loopState.mem (loopEnd-1)=0) :
    ∃ v final cost' credit,
      Runs w p ω (epochCompleteBody iterations read) (startState (L.packet F I heap++[finish]) mem pos)
        (.returned v) final cost' ∧ v<2^w ∧
      EpochCompletePost F A I κ α rate allocation R L q K heap space finish mem loopEnd loopState loopCredit
        certified v final credit ∧
      cost'+R.phi L.handle credit final.mem≤
        cost+R.phi L.handle loopCredit loopState.mem+I.m*reportedEdgesCharge F I.m L.exponent rate+160 :=
  epochComplete_runs_of_loop_at F A I κ α rate allocation R L q K heap space finish loopEnd cost
    mem pos ω loopState loopCredit certified himpl hstore hquery hcoefficient hflag hedge hread
    hloopBody hloop hwords hOne hword htrace

end MinCostFlow.IPM.Machine
