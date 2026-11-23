module

public import MinCostFlow.IPM.Machine.DetectRefreshDetectInput
public import MinCostFlow.IPM.Machine.DetectRefreshInput

/-!
# The combined stage supplies the checked refresh call

Use the actual stable Detect result, with the same concrete state as in
its amortized proof. The combined input provides full-edge coverage and
cached source conditions, and its allocation budget leaves room for the
checked refresh. Every refresh precondition therefore follows from the
actual first call and original source layout.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual Detect/name call completes all input conditions of the
reported-list refresh inside the combined stage, for the exact retained
concrete state and the decoded reported subset. -/
theorem detectRefresh_refresh_pre {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {s : A.State} {x mid : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectNamesContract F A G m κ α rate allocation R b s x).post [b,m,heap] mem v mem')
    (hrep : R.rep b (A.detect s).2 mid mem')
    (hmeta : ∀ z,R.foot b mid z → z<v ∧ (R.foot b x z ∨ heap≤z))
    (hbefore : ∀ z,R.foot b mid z → z<mem' (v-1)) :
    (reportedEdgesContract F A G m rate allocation R b (A.detect s).2 mid q K sourceEnd tableEnd).pre
      [b,mem' (v-1)+1,(A.detect s).1.card,base,lo,up,f,F.limbs,v,c,r,a,one,mn,mx,
        F.fmt.precision,E,ld,gd,m] mem' := by
  have hspace := detectRefresh_remaining_space F A G m κ α rate allocation R hpre hout
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,hcover,hsubset,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  exact reportedEdges_pre_after_detectNames F A G m κ α rate allocation R hfull hcover hout hsubset
    hrep hmeta hbefore (by omega)

end MinCostFlow.IPM.Machine
