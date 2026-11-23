module

public import WordRAM.DataStructure
public import WordRAM.Exec

/-!
# Calling the IPM data structures with their amortized costs

The min-ratio and forest parameters use the shared data-structure
interface. These call rules retain its potential on both sides of the
cost inequality. Thus a sequence of calls can cancel intermediate
potentials instead of charging them again at each iteration. The rules
use the library call semantics and preserve its footprint guarantees.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Initialization as an actual call, retaining the new state's credit
and the shared representation and allocation guarantees. -/
theorem runs_init_with_potential {σ : Type} {R : DSRep σ} {D : DataStructure σ}
    {w init : ℕ} {p : Program} {op : ℕ → ℕ} {r : ℕ} {args : List Expr}
    {st : State} {vs : List ℕ} (ω : ℕ → Bool)
    (himpl : R.Implements w p init op D)
    (hargs : evalArgs w st args=some vs) (hwords : ∀ x ∈ vs,x < 2^w)
    (hpre : D.initPre vs st.mem) (hz : ZeroFrom st.mem (heapArg vs))
    (hspace : heapArg vs+D.initSpace vs st.mem < 2^w) :
    ∃ v mem' pos' c s' x',
      Runs w p ω (.call r init args) st .normal
        ⟨mem',Function.update st.regs r v,pos'⟩ c ∧
      R.rep (heapArg vs) s' x' mem' ∧ D.initPost vs st.mem s' mem' ∧
      R.Respects (fun _ => False) (heapArg vs) (D.initSpace vs st.mem)
        st.mem v (heapArg vs) x' mem' ∧
      c+R.phi (heapArg vs) x' mem' ≤ argsSize args+1+D.initCost vs st.mem := by
  obtain ⟨body,hbody,o,st1,c1,hr,s',x',hrep,hpost,hrespect,hcost⟩ :=
    himpl.2.1 vs st.mem st.pos ω hwords hpre hz hspace
  refine ⟨o.value,st1.mem,st1.pos,argsSize args+c1+1,s',x',?_,hrep,hpost,hrespect,?_⟩
  · apply runs_call_iff.mpr
    refine ⟨vs,body,o,st1,c1,hargs,hbody,hr,rfl,?_,rfl⟩
    cases st1
    rfl
  · omega

/-- An operation as an actual call. The old potential pays for the
operation, while the new potential remains available for later calls. -/
theorem runs_operation_with_potential {σ : Type} {R : DSRep σ} {D : DataStructure σ}
    {w init : ℕ} {p : Program} {op : ℕ → ℕ} {i b r : ℕ} {s : σ} {x : R.τ}
    {args : List Expr} {st : State} {vs : List ℕ} (ω : ℕ → Bool)
    (himpl : R.Implements w p init op D)
    (hargs : evalArgs w st args=some vs) (hwords : ∀ a ∈ vs,a < 2^w)
    (hhandle : vs.head?=some b) (hrep : R.rep b s x st.mem)
    (hpre : D.pre i s vs st.mem) (hfoot : ∀ a,R.foot b x a → a < heapArg vs)
    (hz : ZeroFrom st.mem (heapArg vs))
    (hspace : heapArg vs+D.space i s vs st.mem < 2^w) :
    ∃ v mem' pos' c s' x',
      Runs w p ω (.call r (op i) args) st .normal
        ⟨mem',Function.update st.regs r v,pos'⟩ c ∧
      R.rep b s' x' mem' ∧ D.post i s vs st.mem s' mem' ∧
      R.Respects (R.foot b x) (heapArg vs) (D.space i s vs st.mem)
        st.mem v b x' mem' ∧
      c+R.phi b x' mem' ≤ argsSize args+1+D.cost i s vs st.mem+R.phi b x st.mem := by
  obtain ⟨body,hbody,o,st1,c1,hr,s',x',hrep',hpost,hrespect,hcost⟩ :=
    himpl.2.2 i b s x vs st.mem st.pos ω hwords hhandle hrep hpre hfoot hz hspace
  refine ⟨o.value,st1.mem,st1.pos,argsSize args+c1+1,s',x',?_,hrep',hpost,hrespect,?_⟩
  · apply runs_call_iff.mpr
    refine ⟨vs,body,o,st1,c1,hargs,hbody,hr,rfl,?_,rfl⟩
    cases st1
    rfl
  · omega

end MinCostFlow.IPM.Machine
