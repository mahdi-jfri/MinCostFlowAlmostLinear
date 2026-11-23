module

public import MinCostFlow.IPM.Machine.EpochResidual
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# The epoch guard tests the actual target residual

The exact dot-product bridge identifies the numerical output with
cost minus the guessed target. Its prefix frame preserves the range
constants and quarter threshold. Thus the returned guard code has its
intended meaning for the actual instance and explicit stored flow.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The complete entry's code is exactly the stopping/range decision for
the instance residual. The residual scalar is valid and exact, including
for lower target guesses that must stop at a numerical-range failure. -/
theorem epochResidual_output_instance (I : Instance) (f : Fin I.m → ℝ)
    {w h cp fp tp L P heap mn mx qp code : ℕ} {mem mem' : ℕ → ℕ}
    {target minimum maximum : ℝ}
    (hout : (epochResidualContract w h).post
      [cp,fp,I.m,tp,L,heap,mn,mx,qp] mem code mem')
    (hc : ∀ e : Fin I.m,Num.intVal mem (cp+e.val*L) h L=(I.edge e).cost)
    (hf : ∀ e : Fin I.m,Num.fixVal mem (fp+e.val*L) h L P=f e)
    (htarget : Num.fixVal mem tp h L P=target)
    (hmnEnd : mn+L≤heap) (hmxEnd : mx+L≤heap) (hqEnd : qp+L≤heap)
    (hmn : ScalarAt mem mn h L P minimum) (hmx : ScalarAt mem mx h L P maximum)
    (hq : ScalarAt mem qp h L P (1/4)) :
    ScalarAt mem' (heap+(8*I.m+3)*L) h L P (residual I target f) ∧
    code=(if residual I target f≤1/4 then 0 else
      if minimum<residual I target f ∧ residual I target f<maximum then 1 else 2) ∧
    WordRAM.ZeroFrom mem' (heap+(8*I.m+4)*L) := by
  obtain ⟨hRpost,hGpost⟩ := hout
  change (Num.IPM.residualContract w h).post [cp,fp,I.m,tp,L,heap] mem
    (heap+(8*I.m+4)*L) mem' at hRpost
  have hframe : ∀ z<heap,mem' z=mem z := hRpost.2.2.2.1
  have hres := Num.IPM.residual_output_instance I f hRpost hc hf htarget
  have hex : (8*I.m+4)*L=(8*I.m+3)*L+L := by
    simp only [Nat.add_mul]
    omega
  have hptr : heap+(8*I.m+4)*L-L=heap+(8*I.m+3)*L := by rw [hex]; omega
  rw [hptr] at hres
  have hscalar : ScalarAt mem' (heap+(8*I.m+3)*L) h L P (residual I target f) :=
    ⟨hRpost.2.2.2.2.2.1,hres⟩
  have hmn' : ScalarAt mem' mn h L P minimum :=
    ⟨Num.IPM.valid_frozen hframe hmnEnd hmn.1,(Num.IPM.fixVal_frozen hframe hmnEnd).trans hmn.2⟩
  have hmx' : ScalarAt mem' mx h L P maximum :=
    ⟨Num.IPM.valid_frozen hframe hmxEnd hmx.1,(Num.IPM.fixVal_frozen hframe hmxEnd).trans hmx.2⟩
  have hq' : ScalarAt mem' qp h L P (1/4) :=
    ⟨Num.IPM.valid_frozen hframe hqEnd hq.1,(Num.IPM.fixVal_frozen hframe hqEnd).trans hq.2⟩
  change (residualGuardContract w h).post
    [heap+(8*I.m+4)*L-L,mn,mx,qp,L] mem' code mem' at hGpost
  rw [hptr] at hGpost
  exact ⟨hscalar,residualGuard_output hGpost hscalar hmn' hmx' hq',hRpost.2.2.2.2.1⟩

end MinCostFlow.IPM.Machine
