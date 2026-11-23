module

public import MinCostFlow.IPM.Machine.BudgetedIterationFrame
import MinCostFlow.IPM.Machine.DetectRefreshUnreportedFlow
import MinCostFlow.IPM.Machine.DetectRefreshUnreported
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Unreported cache entries through a budgeted iteration

The refresh changes only reported flow and coefficient blocks. Its
checked continuation and fresh budget metadata preserve all those
tables. Therefore an unreported edge retains every stored flow,
length and gradient word on every outcome of the complete iteration.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Unreported edges retain all three cache blocks through the actual
budgeted entry, including either early rejection and a failed Update. -/
theorem budgetedIteration_unreported_blocks {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v e : ℕ}
    {s s' : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v mem')
    (he : e<I.m) (hne : e∉(A.detect s).1) :
    ∀ p∈[f,ld,gd],∀ i<F.limbs,mem' (p+e*F.limbs+i)=mem (p+e*F.limbs+i) := by
  have hpreCopy := hpre
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,all,heq,
    _,_,_,_,_,_,_,hprefix,_,hsEnd,htEnd,hnEnd,hends,_,_,_,_,_,hldEnd,hgdEnd,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hbefore : tableEnd≤heap := by omega
  obtain ⟨cEnd,cMem,hCpost,_,hframe⟩ := budgetedIteration_tail_frame F A I κ α rate allocation R
    hout hbefore hprefix
  have hflow := detectRefresh_unreported_flow F A (namedInstance I) I.m κ α rate allocation R
    hpreCopy hCpost he hne
  have hcoef := detectRefresh_unreported_coefficients F A (namedInstance I) I.m κ α rate allocation R
    hpreCopy hCpost he hne
  intro p hp i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with hp | hp | hp
  all_goals subst p
  · have heEnd := (reported_entry_end f F.limbs e I.m he).trans (hends f (by simp))
    exact (hframe _ (by omega)).trans (hflow i hi)
  · have heEnd := (reported_entry_end ld F.limbs e I.m he).trans hldEnd
    exact (hframe _ (by omega)).trans (hcoef ld (by simp) i hi)
  · have heEnd := (reported_entry_end gd F.limbs e I.m he).trans hgdEnd
    exact (hframe _ (by omega)).trans (hcoef gd (by simp) i hi)

end MinCostFlow.IPM.Machine
