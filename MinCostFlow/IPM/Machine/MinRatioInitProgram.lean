module

public import MinCostFlow.IPM.Machine.DataStructureCalls
public import WordRAM.Logic
import WordRAM.Tactic

/-!
# The min-ratio initialization call

The epoch driver passes the serialized graph and computed coefficient
addresses to its parameter data structure. This entry calls Init and
returns its allocated heap. Its proof retains the initialization credit
for later Update, Query and Detect calls. The representation and
footprint are those of the shared data-structure interface.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[graph,gradient,length,L,P,heap]`. -/
def minRatioInitBody (init : ℕ) : Stmt :=
  .call 6 init [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5] ;;
  .ret (.reg 6)

/-- The graph/coefficient Init call is deterministic when linked with
its deterministic parameter implementation. -/
theorem minRatioInitBody_noRand (init : ℕ) : (minRatioInitBody init).NoRand := by
  simp [minRatioInitBody,Stmt.NoRand]

/-- The parameter's exact Init pre/postconditions and memory convention.
The representation is supplied by that parameter, not chosen by the IPM. -/
def minRatioInitContract {σ : Type} (w : ℕ) (R : DSRep σ) (D : DataStructure σ) : Contract :=
  heapContract w
    (fun args mem => ∃ graph g l L P heap,args=[graph,g,l,L,P,heap] ∧ D.initPre args mem)
    (fun args mem mem' => ∃ s x,R.rep (heapArg args) s x mem' ∧
      D.initPost args mem s mem' ∧
      ∀ a,R.foot (heapArg args) x a → heapArg args ≤ a)
    (fun args mem => D.initCost args mem+30) D.initSpace

/-- Init executes as an actual machine program. Its cost plus the new
state's potential is bounded by the parameter's Init cost and constant
overhead, so later calls retain the full amortized accounting. -/
theorem minRatioInit_runs_with_potential {σ : Type} (R : DSRep σ) (D : DataStructure σ)
    {w init : ℕ} {p : Program} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op D)
    (graph g l L P heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ [graph,g,l,L,P,heap],a < 2^w)
    (hpre : (minRatioInitContract w R D).pre [graph,g,l,L,P,heap] mem) :
    ∃ o st c s x,Runs w p ω (minRatioInitBody init)
        (startState [graph,g,l,L,P,heap] mem pos) o st c ∧
      (minRatioInitContract w R D).post [graph,g,l,L,P,heap] mem o.value st.mem ∧
      R.rep heap s x st.mem ∧ D.initPost [graph,g,l,L,P,heap] mem s st.mem ∧
      (∀ a,R.foot heap x a → heap≤a ∧ a<o.value) ∧
      c+R.phi heap x st.mem ≤ D.initCost [graph,g,l,L,P,heap] mem+30 := by
  obtain ⟨⟨_,_,_,_,_,_,_,hinit⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+D.initSpace [graph,g,l,L,P,heap] mem < 2^w at hspace
  obtain ⟨v,mem1,pos1,c1,s,x,hr,hrep,hpost,hrespect,hcost⟩ :=
    runs_init_with_potential (R:=R) (D:=D) (r:=6)
      (args:=[.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5]) (st:=startState [graph,g,l,L,P,heap] mem pos)
      ω himpl (by eval_expr) hwords hinit hz hspace
  change R.rep heap s x mem1 at hrep
  change D.initPost [graph,g,l,L,P,heap] mem s mem1 at hpost
  change R.Respects (fun _ => False) heap (D.initSpace [graph,g,l,L,P,heap] mem)
    mem v heap x mem1 at hrespect
  obtain ⟨hlo,hhi,hzero,hframe,hfoot⟩ := hrespect
  have hv : v < 2^w := by omega
  let st1 : State := ⟨mem1,Function.update (startState [graph,g,l,L,P,heap] mem pos).regs 6 v,pos1⟩
  have hret : Runs w p ω (.ret (.reg 6)) st1 (.returned v) st1 2 := by
    apply runs_ret_iff.mpr
    exact ⟨v,by dsimp only [st1]; eval_expr,rfl,rfl,rfl⟩
  refine ⟨.returned v,st1,c1+2+1,s,x,?_,?_,hrep,hpost,?_,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨st1,c1,2,hr,hret,rfl⟩)
  · change heap ≤ v ∧ v ≤ heap+D.initSpace [graph,g,l,L,P,heap] mem ∧
      (∀ a < heap,mem1 a=mem a) ∧ ZeroFrom mem1 v ∧
      ∃ s x,R.rep heap s x mem1 ∧ D.initPost [graph,g,l,L,P,heap] mem s mem1 ∧
        ∀ a,R.foot heap x a → heap ≤ a
    refine ⟨hlo,hhi,fun a ha => hframe a ha (by simp),hzero,s,x,hrep,hpost,?_⟩
    intro a ha
    exact (hfoot a ha).resolve_left id |>.1
  · intro a ha
    exact (hfoot a ha).resolve_left id
  · change c1+2+1+R.phi heap x mem1 ≤ D.initCost [graph,g,l,L,P,heap] mem+30
    change c1+R.phi heap x mem1 ≤ argsSize [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5]+1+
      D.initCost [graph,g,l,L,P,heap] mem at hcost
    simp only [argsSize_cons,argsSize_nil,Expr.size_reg] at hcost
    omega

/-- The Init entry meets the parameter's exact functional and memory
specification, with its initialization cost counted. -/
theorem minRatioInit_meetsContract {σ : Type} (R : DSRep σ) (D : DataStructure σ)
    {w init b : ℕ} {p : Program} {op : ℕ → ℕ}
    (hp : p.procs[b]?=some (minRatioInitBody init))
    (himpl : R.Implements w p init op D) :
    MeetsContract w p b (minRatioInitContract w R D) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  have ha := hpre.1
  obtain ⟨graph,g,l,L,P,heap,rfl,_⟩ := ha
  obtain ⟨o,st,c,s,x,hr,hpost,_,_,_,hcost⟩ :=
    minRatioInit_runs_with_potential R D himpl graph g l L P heap mem pos ω hwords hpre
  exact ⟨o,st,c,hr,hpost,by change c ≤ D.initCost _ _+30; omega⟩

/-- Arguments `[graph,gradient,length,L,P,V,heap]`. -/
def minRatioInitBodyWithV (init : ℕ) : Stmt :=
  .call 7 init [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6] ;;
  .ret (.reg 7)

/-- The 7-argument graph/coefficient Init call is deterministic when linked with
its deterministic parameter implementation. -/
theorem minRatioInitBodyWithV_noRand (init : ℕ) : (minRatioInitBodyWithV init).NoRand := by
  simp [minRatioInitBodyWithV,Stmt.NoRand]

/-- 7-argument version of `minRatioInitContract` passing `V` before `heap`. -/
def minRatioInitContractWithV {σ : Type} (w : ℕ) (R : DSRep σ) (D : DataStructure σ) : Contract :=
  heapContract w
    (fun args mem => ∃ graph g l L P V heap,args=[graph,g,l,L,P,V,heap] ∧ D.initPre args mem)
    (fun args mem mem' => ∃ s x,R.rep (heapArg args) s x mem' ∧
      D.initPost args mem s mem' ∧
      ∀ a,R.foot (heapArg args) x a → heapArg args ≤ a)
    (fun args mem => D.initCost args mem+30) D.initSpace

/-- Execute the 7-argument Init entry as an actual machine program. -/
theorem minRatioInit_runs_with_potential_withV {σ : Type} (R : DSRep σ) (D : DataStructure σ)
    {w init : ℕ} {p : Program} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op D)
    (graph g l L P V heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ [graph,g,l,L,P,V,heap],a < 2^w)
    (hpre : (minRatioInitContractWithV w R D).pre [graph,g,l,L,P,V,heap] mem) :
    ∃ o st c s x,Runs w p ω (minRatioInitBodyWithV init)
        (startState [graph,g,l,L,P,V,heap] mem pos) o st c ∧
      (minRatioInitContractWithV w R D).post [graph,g,l,L,P,V,heap] mem o.value st.mem ∧
      R.rep heap s x st.mem ∧ D.initPost [graph,g,l,L,P,V,heap] mem s st.mem ∧
      (∀ a,R.foot heap x a → heap≤a ∧ a<o.value) ∧
      c+R.phi heap x st.mem ≤ D.initCost [graph,g,l,L,P,V,heap] mem+30 := by
  obtain ⟨⟨_,_,_,_,_,_,_,_,hinit⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+D.initSpace [graph,g,l,L,P,V,heap] mem < 2^w at hspace
  obtain ⟨v,mem1,pos1,c1,s,x,hr,hrep,hpost,hrespect,hcost⟩ :=
    runs_init_with_potential (R:=R) (D:=D) (r:=7)
      (args:=[.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6])
      (st:=startState [graph,g,l,L,P,V,heap] mem pos)
      ω himpl (by eval_expr) hwords hinit hz hspace
  change R.rep heap s x mem1 at hrep
  change D.initPost [graph,g,l,L,P,V,heap] mem s mem1 at hpost
  change R.Respects (fun _ => False) heap (D.initSpace [graph,g,l,L,P,V,heap] mem)
    mem v heap x mem1 at hrespect
  obtain ⟨hlo,hhi,hzero,hframe,hfoot⟩ := hrespect
  have hv : v < 2^w := by omega
  let st1 : State := ⟨mem1,Function.update (startState [graph,g,l,L,P,V,heap] mem pos).regs 7 v,pos1⟩
  have hret : Runs w p ω (.ret (.reg 7)) st1 (.returned v) st1 2 := by
    apply runs_ret_iff.mpr
    exact ⟨v,by dsimp only [st1]; eval_expr,rfl,rfl,rfl⟩
  refine ⟨.returned v,st1,c1+2+1,s,x,?_,?_,hrep,hpost,?_,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨st1,c1,2,hr,hret,rfl⟩)
  · change heap ≤ v ∧ v ≤ heap+D.initSpace [graph,g,l,L,P,V,heap] mem ∧
      (∀ a < heap,mem1 a=mem a) ∧ ZeroFrom mem1 v ∧
      ∃ s x,R.rep heap s x mem1 ∧ D.initPost [graph,g,l,L,P,V,heap] mem s mem1 ∧
        ∀ a,R.foot heap x a → heap ≤ a
    refine ⟨hlo,hhi,fun a ha => hframe a ha (by simp),hzero,s,x,hrep,hpost,?_⟩
    intro a ha
    exact (hfoot a ha).resolve_left id |>.1
  · intro a ha
    exact (hfoot a ha).resolve_left id
  · change c1+2+1+R.phi heap x mem1 ≤ D.initCost [graph,g,l,L,P,V,heap] mem+30
    change c1+R.phi heap x mem1 ≤ argsSize [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6]+1+
      D.initCost [graph,g,l,L,P,V,heap] mem at hcost
    simp only [argsSize_cons,argsSize_nil,Expr.size_reg] at hcost
    omega

/-- The 7-argument Init entry meets its exact functional and memory specification. -/
theorem minRatioInit_meetsContract_withV {σ : Type} (R : DSRep σ) (D : DataStructure σ)
    {w init b : ℕ} {p : Program} {op : ℕ → ℕ}
    (hp : p.procs[b]?=some (minRatioInitBodyWithV init))
    (himpl : R.Implements w p init op D) :
    MeetsContract w p b (minRatioInitContractWithV w R D) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  have ha := hpre.1
  obtain ⟨graph,g,l,L,P,V,heap,rfl,_⟩ := ha
  obtain ⟨o,st,c,s,x,hr,hpost,_,_,_,hcost⟩ :=
    minRatioInit_runs_with_potential_withV R D himpl graph g l L P V heap mem pos ω hwords hpre
  exact ⟨o,st,c,hr,hpost,by change c ≤ D.initCost _ _+30; omega⟩

end MinCostFlow.IPM.Machine
