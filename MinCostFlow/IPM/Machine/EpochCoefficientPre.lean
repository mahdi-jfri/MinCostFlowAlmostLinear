module

public import MinCostFlow.IPM.Machine.CoefficientRefresh

/-!
# Combining length and gradient array inputs

The two numerical procedures read the same fixed-point flow data.
The coefficient pass reserves their consecutive workspaces and
forwards their separate array preconditions.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The common inputs to both numerical array passes give the input
to their sequential wrapper. -/
theorem coefficientRefresh_pre_of_arrays
    {w h q K m cp rp lo fp up ap one L P E heap : ℕ} {mem : ℕ → ℕ}
    (hlen : (Num.IPM.lengthArrayContract w h q).pre [lo,fp,up,ap,one,m,L,P,E,heap] mem)
    (hgrad : (Num.IPM.gradientArrayContract w h q K).pre [m,cp,rp,lo,fp,up,ap,one,L,P,E,heap] mem)
    (hz : ZeroFrom mem heap)
    (hspace : heap+(Num.IPM.lengthArraySpace m L P E+Num.IPM.gradientArraySpace m L P E)<2^w) :
    (coefficientRefreshContract w h q K).pre
      [m,cp,rp,lo,fp,up,ap,one,L,P,E,Num.IPM.lengthArraySpace m L P E,
        Num.IPM.gradientArraySpace m L P E,heap] mem := by
  refine ⟨⟨m,cp,rp,lo,fp,up,ap,one,L,P,E,Num.IPM.lengthArraySpace m L P E,
    Num.IPM.gradientArraySpace m L P E,heap,rfl,rfl,rfl,hlen,hgrad⟩,hz,hspace⟩

end MinCostFlow.IPM.Machine
