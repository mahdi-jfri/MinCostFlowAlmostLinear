module

public import MinCostFlow.IPM.Machine.DataStructureCalls
public import WordRAM.Logic
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Querying a flow coordinate with a reserved answer block

The parameter data structure writes its answer at the incoming heap. Its
returned heap can precede the end of a zero-padded fixed-point block.
The caller therefore reserves another `L` words after that returned heap.
This preserves the parameter's exact postcondition and retains its
amortized potential for the next operation.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[handle,edge,L,heap]`. Query itself receives
`[handle,edge,heap]`, exactly as required by its parameter contract. -/
def minRatioQueryBody (query : ℕ) : Stmt :=
  .call 4 query [.reg 0,.reg 1,.reg 3] ;;
  .ret (.bin .add (.reg 4) (.reg 2))

/-- Reserving the answer suffix adds no random statements. -/
theorem minRatioQueryBody_noRand (query : ℕ) : (minRatioQueryBody query).NoRand := by
  simp [minRatioQueryBody,Stmt.NoRand]

/-- The caller reserves the whole fixed-point answer without strengthening
the parameter's Query operation or its abstract state transition. -/
def minRatioQueryContract {σ : Type} (w : ℕ) (R : DSRep σ) (D : DataStructure σ)
    (b : ℕ) (s : σ) (x : R.τ) : Contract where
  pre args mem := ∃ e L heap,args=[b,e,L,heap] ∧ R.rep b s x mem ∧
    D.pre 1 s [b,e,heap] mem ∧ (∀ a,R.foot b x a → a<heap) ∧
    ZeroFrom mem heap ∧ heap+D.space 1 s [b,e,heap] mem+L<2^w
  post args mem v mem' := ∃ queryEnd s' x',
    v=queryEnd+args.getD 2 0 ∧ heapArg args≤queryEnd ∧
    queryEnd≤heapArg args+D.space 1 s [b,args.getD 1 0,heapArg args] mem ∧
    ZeroFrom mem' v ∧ R.rep b s' x' mem' ∧
    D.post 1 s [b,args.getD 1 0,heapArg args] mem s' mem' ∧
    (∀ a<heapArg args,¬ R.foot b x a → mem' a=mem a) ∧
    (∀ a,R.foot b x' a → a<v) ∧
    (∀ a,R.foot b x' a → R.foot b x a ∨ heapArg args≤a ∧ a<queryEnd)
  cost args mem := D.cost 1 s [b,args.getD 1 0,heapArg args] mem+R.phi b x mem+40

/-- The actual parameter Query call returns with its answer reserved and
with the amortized inequality needed to telescope subsequent calls. -/
theorem minRatioQuery_runs_with_potential {σ : Type} (R : DSRep σ) (D : DataStructure σ)
    {w init b : ℕ} {p : Program} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op D) (s : σ) (x : R.τ)
    (e L heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a∈[b,e,L,heap],a<2^w)
    (hpre : (minRatioQueryContract w R D b s x).pre [b,e,L,heap] mem) :
    ∃ o st c s' x',Runs w p ω (minRatioQueryBody (op 1))
        (startState [b,e,L,heap] mem pos) o st c ∧
      (minRatioQueryContract w R D b s x).post [b,e,L,heap] mem o.value st.mem ∧
      R.rep b s' x' st.mem ∧ D.post 1 s [b,e,heap] mem s' st.mem ∧
      (∀ a,R.foot b x' a → a<o.value ∧ (R.foot b x a ∨ heap≤a)) ∧
      c+R.phi b x' st.mem ≤ D.cost 1 s [b,e,heap] mem+R.phi b x mem+40 := by
  obtain ⟨e',L',heap',heq,hrep,hoperation,hfoot,hz,hspace⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  have hcallWords : ∀ a∈[b,e,heap],a<2^w := by
    intro a ha
    apply hwords a
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
    tauto
  obtain ⟨v,mem1,pos1,c1,s',x',hr,hrep',hpost,hrespect,hcost⟩ :=
    runs_operation_with_potential (R:=R) (D:=D) (r:=4) (i:=1)
      (args:=[.reg 0,.reg 1,.reg 3]) (st:=startState [b,e,L,heap] mem pos)
      ω himpl (by eval_expr) hcallWords rfl hrep hoperation hfoot hz (by change heap+D.space 1 s [b,e,heap] mem<2^w; omega)
  change R.rep b s' x' mem1 at hrep'
  change D.post 1 s [b,e,heap] mem s' mem1 at hpost
  change R.Respects (R.foot b x) heap (D.space 1 s [b,e,heap] mem)
    mem v b x' mem1 at hrespect
  obtain ⟨hlo,hhi,hzero,hframe,hnewfoot⟩ := hrespect
  have hv : v+L<2^w := by omega
  let st1 : State := ⟨mem1,Function.update (startState [b,e,L,heap] mem pos).regs 4 v,pos1⟩
  have hret : Runs w p ω (.ret (.bin .add (.reg 4) (.reg 2))) st1
      (.returned (v+L)) st1 4 := by
    apply runs_ret_iff.mpr
    exact ⟨v+L,by dsimp only [st1]; eval_expr,rfl,rfl,rfl⟩
  refine ⟨.returned (v+L),st1,c1+4+1,s',x',?_,?_,hrep',hpost,?_,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨st1,c1,4,hr,hret,rfl⟩)
  · change (minRatioQueryContract w R D b s x).post [b,e,L,heap] mem (v+L) mem1
    simp only [minRatioQueryContract,List.getD_cons_zero,List.getD_cons_succ,heapArg,
      List.getLastD_cons,List.getLastD_nil]
    refine ⟨v,s',x',rfl,hlo,hhi,hzero.mono (by omega),hrep',hpost,hframe,?_,hnewfoot⟩
    intro a ha
    have hh := hnewfoot a ha
    rcases hh with hold | hnew
    · exact lt_of_lt_of_le (hfoot a hold) (by omega)
    · omega
  · change ∀ a,R.foot b x' a → a<v+L ∧ (R.foot b x a ∨ heap≤a)
    intro a ha
    rcases hnewfoot a ha with hold | hnew
    · exact ⟨(hfoot a hold).trans_le (by omega),Or.inl hold⟩
    · exact ⟨by omega,Or.inr hnew.1⟩
  · change c1+4+1+R.phi b x' mem1 ≤ D.cost 1 s [b,e,heap] mem+R.phi b x mem+40
    change c1+R.phi b x' mem1 ≤ argsSize [.reg 0,.reg 1,.reg 3]+1+
      D.cost 1 s [b,e,heap] mem+R.phi b x mem at hcost
    simp only [argsSize_cons,argsSize_nil,Expr.size_reg] at hcost
    omega

/-- The Query wrapper satisfies its functional, memory and cost contract
using only the shared implementation specification of its parameter. -/
theorem minRatioQuery_meetsContract {σ : Type} (R : DSRep σ) (D : DataStructure σ)
    {w init b entry : ℕ} {p : Program} {op : ℕ → ℕ} (s : σ) (x : R.τ)
    (hp : p.procs[entry]?=some (minRatioQueryBody (op 1)))
    (himpl : R.Implements w p init op D) :
    MeetsContract w p entry (minRatioQueryContract w R D b s x) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  have hpreCopy := hpre
  obtain ⟨e,L,heap,heq,_⟩ := hpre
  subst args
  obtain ⟨o,st,c,s',x',hr,hpost,_,_,_,hcost⟩ :=
    minRatioQuery_runs_with_potential R D himpl s x e L heap mem pos ω hwords hpreCopy
  exact ⟨o,st,c,hr,hpost,by change c≤D.cost 1 s [b,e,heap] mem+R.phi b x mem+40; omega⟩

end MinCostFlow.IPM.Machine
