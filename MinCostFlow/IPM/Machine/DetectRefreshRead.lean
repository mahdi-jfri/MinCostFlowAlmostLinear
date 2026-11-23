module

public import MinCostFlow.IPM.Machine.DetectRefreshDetectInput
public import MinCostFlow.IPM.Machine.DetectNamesOutput
import WordRAM.Tactic

/-!
# Reading the actual stable report pointer and count

Detect/name preparation returns its snapshot pointer in the last word.
Decode that word and the snapshot's count with two actual loads. The
combined allocation budget and model cardinality bound justify both
addresses and loaded words. No memory or tape position changes.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual two loads recover the stable pointer and exact model
report cardinality, with exact register frame and cost nine. -/
theorem detectRefreshRead_runs {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd dHeap : ℕ}
    {s : A.State} {x : R.τ} {mem : ℕ → ℕ}
    (parent : State) (ω : ℕ → Bool)
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectNamesContract F A G m κ α rate allocation R b s x).post [b,m,heap] mem dHeap parent.mem)
    (hendpoint : parent.regs 20=dHeap) (hm : m<2^w) :
    Runs w p ω detectRefreshRead parent .normal
      {parent with regs:=Function.update (Function.update parent.regs 21 (parent.mem (dHeap-1))) 22 (A.detect s).1.card} 9 := by
  have hspace := detectRefresh_remaining_space F A G m κ α rate allocation R hpre hout
  have hcard := (detectRefresh_detect_pre F A G m κ α rate allocation R hpre).2
  have hreport := detectNames_output F A G m κ α rate allocation R hout
  have hcount := hreport.1.count
  have hdW : dHeap<2^w := by omega
  have hslotW : dHeap-1<2^w := by omega
  have hpW : parent.mem (dHeap-1)<2^w := by omega
  have hcW : (A.detect s).1.card<2^w := hcard.trans_lt hm
  have hw : 1<2^w := by omega
  let mid : State := {parent with regs:=Function.update parent.regs 21 (parent.mem (dHeap-1))}
  have hfirst : Runs w p ω (.assign 21 (.load (.bin .sub (.reg 20) (.const 1)))) parent .normal mid 5 := by
    apply runs_assign_iff.mpr
    exact ⟨parent.mem (dHeap-1),by eval_expr,rfl,rfl,rfl⟩
  have hsecond : Runs w p ω (.assign 22 (.load (.reg 21))) mid .normal
      {parent with regs:=Function.update (Function.update parent.regs 21 (parent.mem (dHeap-1))) 22 (A.detect s).1.card} 3 := by
    apply runs_assign_iff.mpr
    exact ⟨(A.detect s).1.card,by eval_expr,rfl,rfl,rfl⟩
  exact runs_seq_iff.mpr (Or.inr ⟨mid,5,3,hfirst,hsecond,rfl⟩)

end MinCostFlow.IPM.Machine
