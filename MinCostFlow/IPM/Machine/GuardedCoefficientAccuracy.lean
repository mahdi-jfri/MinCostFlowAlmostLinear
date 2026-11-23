module

public import MinCostFlow.IPM.Machine.GuardedCoefficientRefresh

/-!
# The accepted coefficient values refer to the original stored inputs

The slack guard preserves the original source prefix. Hence the scalar
refresh's errors, stated at its intermediate memory, are the same errors
for the caller's stored flow and held residual. This connects the actual
guarded program to the coefficient tolerances used in the epoch analysis.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Acceptance stores valid coefficients with the numerical length and
gradient tolerances for the caller's original stored edge and held residual. -/
theorem guardedCoefficientRefresh_accuracy
    {w h q K m c r lo f up a one mn mx L P E ld gd heap v : ℕ}
    {mem mem' : ℕ → ℕ}
    (hout : (guardedCoefficientRefreshContract w h q K).post
      [m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap] mem v mem')
    (haccept : mem' (heap+4*L)=1)
    (hc : c+L≤heap) (hr : r+L≤heap) (hlo : lo+L≤heap)
    (hf : f+L≤heap) (hup : up+L≤heap) (ha : a+L≤heap) :
    Num.Valid mem' ld h L ∧
      ScalarApprox (1+1/(2:ℝ)^q) (Num.fixVal mem' ld h L P)
        (Num.IPM.arrayLength mem lo f up a h L P 0) ∧
      Num.Valid mem' gd h L ∧
      |Num.fixVal mem' gd h L P-Num.IPM.arrayGradient mem m c r lo f up a h L P 0|≤
        (1/(2:ℝ)^q)*Num.IPM.arrayLength mem lo f up a h L P 0 := by
  obtain ⟨guardEnd,guardMem,hguard,hflag,hbranch⟩ := hout
  change mem' (heap+4*L)=guardMem (heap+4*L) at hflag
  have hgAccept : guardMem (heap+4*L)=1 := hflag.symm.trans haccept
  change (if guardMem (heap+4*L)=1 then _ else _) at hbranch
  simp only [hgAccept,ite_true] at hbranch
  obtain ⟨_,_,_,_,hvl,hl,hvg,hg⟩ := hbranch
  change ScalarApprox (1+1/(2:ℝ)^q) (Num.fixVal mem' ld h L P)
    (Num.IPM.arrayLength guardMem lo f up a h L P 0) at hl
  change |Num.fixVal mem' gd h L P-Num.IPM.arrayGradient guardMem m c r lo f up a h L P 0|≤
    (1/(2:ℝ)^q)*Num.IPM.arrayLength guardMem lo f up a h L P 0 at hg
  have hframe := hguard.1.2.2.1
  change ∀ z<heap,guardMem z=mem z at hframe
  have hlFrozen := Num.IPM.arrayLength_frozen (lo:=lo) (f:=f) (up:=up) (h:=h) (P:=P) (i:=0)
    hframe (by simpa using hlo) (by simpa using hf) (by simpa using hup) ha
  have hgFrozen := Num.IPM.arrayGradient_frozen (m:=m) (c:=c) (lo:=lo) (f:=f) (up:=up)
    (h:=h) (P:=P) (i:=0) hframe (by simpa using hc) hr
    (by simpa using hlo) (by simpa using hf) (by simpa using hup) ha
  rw [hlFrozen] at hl
  rw [hlFrozen,hgFrozen] at hg
  exact ⟨hvl,hl,hvg,hg⟩

end MinCostFlow.IPM.Machine
