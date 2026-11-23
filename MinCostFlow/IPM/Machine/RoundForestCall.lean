module

public import MinCostFlow.IPM.Machine.ForestContract
import WordRAM.Tactic

/-!
# Calling a dynamic-forest operation within the rounder

Forward the exact arguments to the parameter procedure. The parent
inherits its returned heap and concrete state, so the operation's
cost can be charged to the same potential as later calls.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- A linked forest operation preserves the caller's registers outside
the result slot and transfers its amortized guarantee. -/
theorem roundForest_call_runs {w h L P i dst b : ℕ} (D : DynForest)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (forestMachineContract D w h L P rate allocation))
    (parent : State) (ω : ℕ → Bool) (s : D.State) (x : R.τ)
    (exprs : List Expr) (args : List ℕ)
    (hargs : evalArgs w parent exprs=some args)
    (hwords : ∀ z∈args,z<2^w) (hhandle : args.head?=some b)
    (hrep : R.rep b s x parent.mem) (hpre : (forestMachineContract D w h L P rate allocation).pre i s args parent.mem)
    (hfoot : ∀ z,R.foot b x z → z<heapArg args) (hz : ZeroFrom parent.mem (heapArg args))
    (hspace : heapArg args+(forestMachineContract D w h L P rate allocation).space i s args parent.mem<2^w) :
    ∃ v final c s' y,
      Runs w p ω (.call dst (op i) exprs) parent .normal final c ∧
      final.regs dst=v ∧ (∀ j,j≠dst → final.regs j=parent.regs j) ∧
      (forestMachineContract D w h L P rate allocation).post i s args parent.mem s' final.mem ∧
      R.rep b s' y final.mem ∧ R.Respects (R.foot b x) (heapArg args)
        ((forestMachineContract D w h L P rate allocation).space i s args parent.mem) parent.mem v b y final.mem ∧
      c+R.phi b y final.mem≤rate (D.toForest s).n+argsSize exprs+1+R.phi b x parent.mem := by
  obtain ⟨body,hbody,o,st,c,hrun,s',y,hst,hpost,hframe,hcost⟩ :=
    himpl.2.2 i b s x args parent.mem parent.pos ω hwords hhandle hrep hpre hfoot hz hspace
  let final : State := ⟨st.mem,Function.update parent.regs dst o.value,st.pos⟩
  have hcall : Runs w p ω (.call dst (op i) exprs) parent .normal final (argsSize exprs+c+1) := by
    apply runs_call_iff.mpr
    refine ⟨args,body,o,st,c,hargs,hbody,hrun,rfl,?_,rfl⟩
    cases st
    rfl
  refine ⟨o.value,final,_,s',y,hcall,by simp [final],?_,hpost,hst,hframe,?_⟩
  · intro j hne
    exact Function.update_of_ne hne _ _
  · change c+R.phi b y st.mem≤rate (D.toForest s).n+R.phi b x parent.mem at hcost
    change argsSize exprs+c+1+R.phi b y st.mem≤_
    omega

/-- Removing a forest edge only restricts the set of fitting payloads. -/
theorem ForestFits.cut {D : DynForest} (hD : D.IsSpec) {h L P : ℕ}
    {s : D.State} {u v : ℕ} (hInv : D.Inv s) (hFit : ForestFits D h L P s) :
    ForestFits D h L P (D.cut s u v) := by
  have hc := (hD.2.2.2.2.1 s u v hInv).2
  intro e he
  have hmem := hc.2.mem_iff.mp he
  exact hFit e (List.mem_filter.mp hmem).1

end MinCostFlow.IPM.Machine
