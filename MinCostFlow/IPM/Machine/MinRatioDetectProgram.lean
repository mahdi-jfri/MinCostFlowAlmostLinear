module

public import MinCostFlow.IPM.Machine.DataStructureCalls
public import WordRAM.Logic
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Detecting changed edges with a reserved answer list

The parameter data structure writes its answer at the incoming heap. Its
returned heap can precede the end of a zero-padded count and edge-name list.
The caller therefore reserves another `padding` words after that returned heap.
This preserves the parameter's exact postcondition and retains its
amortized potential for the next operation.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[handle,padding,heap]`. Detect itself receives
`[handle,heap]`, exactly as required by its parameter contract. -/
def minRatioDetectBody (detect : ℕ) : Stmt :=
  .call 4 detect [.reg 0,.reg 2] ;;
  .ret (.bin .add (.reg 4) (.reg 1))

/-- Reserving the answer suffix adds no random statements. -/
theorem minRatioDetectBody_noRand (detect : ℕ) : (minRatioDetectBody detect).NoRand := by
  simp [minRatioDetectBody,Stmt.NoRand]

/-- The caller reserves its requested answer suffix without strengthening
the parameter's Detect operation or its abstract state transition. -/
def minRatioDetectContract {σ : Type} (w : ℕ) (R : DSRep σ) (D : DataStructure σ)
    (b : ℕ) (s : σ) (x : R.τ) : Contract where
  pre args mem := ∃ padding heap,args=[b,padding,heap] ∧ R.rep b s x mem ∧
    D.pre 2 s [b,heap] mem ∧ (∀ a,R.foot b x a → a<heap) ∧
    ZeroFrom mem heap ∧ heap+D.space 2 s [b,heap] mem+padding<2^w
  post args mem v mem' := ∃ detectEnd s' x',
    v=detectEnd+args.getD 1 0 ∧ heapArg args≤detectEnd ∧
    detectEnd≤heapArg args+D.space 2 s [b,heapArg args] mem ∧
    ZeroFrom mem' v ∧ R.rep b s' x' mem' ∧
    D.post 2 s [b,heapArg args] mem s' mem' ∧
    (∀ a<heapArg args,¬ R.foot b x a → mem' a=mem a) ∧
    (∀ a,R.foot b x' a → a<v) ∧
    (∀ a,R.foot b x' a → R.foot b x a ∨ heapArg args≤a ∧ a<detectEnd)
  cost args mem := D.cost 2 s [b,heapArg args] mem+R.phi b x mem+40

/-- The actual parameter Detect call returns with its answer reserved and
with the amortized inequality needed to telescope subsequent calls. -/
theorem minRatioDetect_runs_with_potential {σ : Type} (R : DSRep σ) (D : DataStructure σ)
    {w init b : ℕ} {p : Program} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op D) (s : σ) (x : R.τ)
    (padding heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a∈[b,padding,heap],a<2^w)
    (hpre : (minRatioDetectContract w R D b s x).pre [b,padding,heap] mem) :
    ∃ o st c s' x',Runs w p ω (minRatioDetectBody (op 2))
        (startState [b,padding,heap] mem pos) o st c ∧
      (minRatioDetectContract w R D b s x).post [b,padding,heap] mem o.value st.mem ∧
      R.rep b s' x' st.mem ∧ D.post 2 s [b,heap] mem s' st.mem ∧
      (∀ a,R.foot b x' a → a<o.value ∧ (R.foot b x a ∨ heap≤a)) ∧
      c+R.phi b x' st.mem ≤ D.cost 2 s [b,heap] mem+R.phi b x mem+40 := by
  obtain ⟨padding',heap',heq,hrep,hoperation,hfoot,hz,hspace⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl⟩ := heq
  have hcallWords : ∀ a∈[b,heap],a<2^w := by
    intro a ha
    apply hwords a
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
    tauto
  obtain ⟨v,mem1,pos1,c1,s',x',hr,hrep',hpost,hrespect,hcost⟩ :=
    runs_operation_with_potential (R:=R) (D:=D) (r:=4) (i:=2)
      (args:=[.reg 0,.reg 2]) (st:=startState [b,padding,heap] mem pos)
      ω himpl (by eval_expr) hcallWords rfl hrep hoperation hfoot hz (by change heap+D.space 2 s [b,heap] mem<2^w; omega)
  change R.rep b s' x' mem1 at hrep'
  change D.post 2 s [b,heap] mem s' mem1 at hpost
  change R.Respects (R.foot b x) heap (D.space 2 s [b,heap] mem)
    mem v b x' mem1 at hrespect
  obtain ⟨hlo,hhi,hzero,hframe,hnewfoot⟩ := hrespect
  have hv : v+padding<2^w := by omega
  let st1 : State := ⟨mem1,Function.update (startState [b,padding,heap] mem pos).regs 4 v,pos1⟩
  have hret : Runs w p ω (.ret (.bin .add (.reg 4) (.reg 1))) st1
      (.returned (v+padding)) st1 4 := by
    apply runs_ret_iff.mpr
    exact ⟨v+padding,by dsimp only [st1]; eval_expr,rfl,rfl,rfl⟩
  refine ⟨.returned (v+padding),st1,c1+4+1,s',x',?_,?_,hrep',hpost,?_,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨st1,c1,4,hr,hret,rfl⟩)
  · change (minRatioDetectContract w R D b s x).post [b,padding,heap] mem (v+padding) mem1
    simp only [minRatioDetectContract,List.getD_cons_zero,List.getD_cons_succ,heapArg,
      List.getLastD_cons,List.getLastD_nil]
    refine ⟨v,s',x',rfl,hlo,hhi,hzero.mono (by omega),hrep',hpost,hframe,?_,hnewfoot⟩
    intro a ha
    have hh := hnewfoot a ha
    rcases hh with hold | hnew
    · exact lt_of_lt_of_le (hfoot a hold) (by omega)
    · omega
  · change ∀ a,R.foot b x' a → a<v+padding ∧ (R.foot b x a ∨ heap≤a)
    intro a ha
    rcases hnewfoot a ha with hold | hnew
    · exact ⟨(hfoot a hold).trans_le (by omega),Or.inl hold⟩
    · exact ⟨by omega,Or.inr hnew.1⟩
  · change c1+4+1+R.phi b x' mem1 ≤ D.cost 2 s [b,heap] mem+R.phi b x mem+40
    change c1+R.phi b x' mem1 ≤ argsSize [.reg 0,.reg 2]+1+
      D.cost 2 s [b,heap] mem+R.phi b x mem at hcost
    simp only [argsSize_cons,argsSize_nil,Expr.size_reg] at hcost
    omega

/-- The Detect wrapper satisfies its functional, memory and cost contract
using only the shared implementation specification of its parameter. -/
theorem minRatioDetect_meetsContract {σ : Type} (R : DSRep σ) (D : DataStructure σ)
    {w init b entry : ℕ} {p : Program} {op : ℕ → ℕ} (s : σ) (x : R.τ)
    (hp : p.procs[entry]?=some (minRatioDetectBody (op 2)))
    (himpl : R.Implements w p init op D) :
    MeetsContract w p entry (minRatioDetectContract w R D b s x) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  have hpreCopy := hpre
  obtain ⟨padding,heap,heq,_⟩ := hpre
  subst args
  obtain ⟨o,st,c,s',x',hr,hpost,_,_,_,hcost⟩ :=
    minRatioDetect_runs_with_potential R D himpl s x padding heap mem pos ω hwords hpreCopy
  exact ⟨o,st,c,hr,hpost,by change c≤D.cost 2 s [b,heap] mem+R.phi b x mem+40; omega⟩

end MinCostFlow.IPM.Machine
