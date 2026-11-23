module

public import MinCostFlow.IPM.Machine.BudgetedIterationFrame
import MinCostFlow.IPM.Machine.DetectRefreshFullNames

/-!
# Reusing the full edge-name list across actual iterations

The Detect/refresh preserves the original names. The checked Update and
fresh budget metadata preserve all old caller words outside the DS
footprint, including those names. The full list can therefore be reused
at the next iteration without another graph-sized copy.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Every actual budgeted outcome preserves the original full edge list,
including an over-budget rejection and a failed Update. -/
theorem budgetedIteration_full_names {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s s' : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v mem')
 :
    ∀ i<I.m,mem' (names+i)=mem (names+i) := by
  have hpreCopy := hpre
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,all,heq,
    _,_,_,_,_,_,_,hprefix,hnameAvoid,hsEnd,htEnd,hnEnd,hends,_,_,_,_,_,hldEnd,hgdEnd,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨cEnd,cMem,hCpost,_,hframe⟩ := budgetedIteration_tail_frame_outside_foot F A I κ α rate allocation R hout
  have hnames := detectRefresh_full_names F A (namedInstance I) I.m κ α rate allocation R hpreCopy hCpost
  intro i hi
  exact (hframe (names+i) (by omega) (hnameAvoid i hi)).trans (hnames i hi)

end MinCostFlow.IPM.Machine
