module

public import MinCostFlow.IPM.Machine.CoefficientStatus
public import MinCostFlow.IPM.Machine.GuardedCoefficientAccuracy

/-!
# Memory and accuracy after appending the coefficient status

The final status write is above the coefficient computation's returned
heap. It preserves every old coefficient entry and the exact approximation
bounds. Both branches have one common scratch bound and frame, enabling
the reported-edge loop to carry earlier values and the DS footprint.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The status wrapper adds exactly one word to the guarded computation's
allocation and preserves the same old-memory frame. -/
theorem coefficientStatus_frame {w h q K m c r lo f up a one mn mx L P E ld gd heap v : ℕ}
    {mem mem' : ℕ → ℕ}
    (hout : (coefficientStatusContract w h q K).post
      [m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap] mem v mem') :
    heap≤v ∧ v≤heap+(4*L+1)+L+Num.IPM.lengthSpace L P E+Num.IPM.gradientSpace L P E+2 ∧
      ZeroFrom mem' v ∧
      (∀ z<heap,(z<ld ∨ ld+L≤z) → (z<gd ∨ gd+L≤z) → mem' z=mem z) := by
  obtain ⟨innerEnd,innerMem,hg,hf⟩ := hout
  have hgFrame := guardedCoefficientRefresh_frame hg
  have hv := hf.2
  change v=innerEnd+1 at hv
  have hflagFrame := hf.1.2.2.1
  change ∀ z < innerEnd,mem' z=innerMem z at hflagFrame
  refine ⟨by omega,by omega,hf.1.2.2.2.1,?_⟩
  intro z hz h0 h1
  exact (hflagFrame z (by omega)).trans (hgFrame.2.2.2.1 z hz h0 h1)

/-- On acceptance, the final table values still satisfy both numerical
error bounds for the caller's original stored edge and held residual. -/
theorem coefficientStatus_accuracy {w h q K m c r lo f up a one mn mx L P E ld gd heap v : ℕ}
    {mem mem' : ℕ → ℕ}
    (hout : (coefficientStatusContract w h q K).post
      [m,c,r,lo,f,up,a,one,mn,mx,L,P,E,ld,gd,heap] mem v mem')
    (haccept : mem' (v-1)=1)
    (hc : c+L≤heap) (hr : r+L≤heap) (hlo : lo+L≤heap)
    (hf : f+L≤heap) (hup : up+L≤heap) (ha : a+L≤heap)
    (hld : ld+L≤heap) (hgd : gd+L≤heap) :
    Num.Valid mem' ld h L ∧
      ScalarApprox (1+1/(2:ℝ)^q) (Num.fixVal mem' ld h L P)
        (Num.IPM.arrayLength mem lo f up a h L P 0) ∧
      Num.Valid mem' gd h L ∧
      |Num.fixVal mem' gd h L P-Num.IPM.arrayGradient mem m c r lo f up a h L P 0|≤
        (1/(2:ℝ)^q)*Num.IPM.arrayLength mem lo f up a h L P 0 := by
  obtain ⟨innerEnd,innerMem,hguard,hflag⟩ := hout
  have hbit := flagRecord_output hflag
  change mem' (v-1)=innerMem (heap+4*L) at hbit
  have hinnerAccept : innerMem (heap+4*L)=1 := hbit.symm.trans haccept
  have he := guardedCoefficientRefresh_accuracy hguard hinnerAccept hc hr hlo hf hup ha
  have hheap := (guardedCoefficientRefresh_frame hguard).1
  have hframe := hflag.1.2.2.1
  change ∀ z < innerEnd,mem' z=innerMem z at hframe
  have hld' : ld+L ≤ innerEnd := hld.trans hheap
  have hgd' : gd+L ≤ innerEnd := hgd.trans hheap
  refine ⟨Num.IPM.valid_frozen hframe hld' he.1,?_,Num.IPM.valid_frozen hframe hgd' he.2.2.1,?_⟩
  · rw [Num.IPM.fixVal_frozen hframe hld']
    exact he.2.1
  · rw [Num.IPM.fixVal_frozen hframe hgd']
    exact he.2.2.2

end MinCostFlow.IPM.Machine
