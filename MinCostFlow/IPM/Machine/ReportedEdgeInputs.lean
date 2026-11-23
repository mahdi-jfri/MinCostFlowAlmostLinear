module

public import MinCostFlow.IPM.Machine.ReportedEdge
public import MinCostFlow.IPM.Machine.CoefficientStatusOutput

/-!
# Supplying the second call of a reported-edge operation

Once actual Query recovery passes its capacity guard, the preserved
scalar sources and capacity-width bound supply the complete coefficient
status procedure. Its extra status word also fits in the combined
allocation. No positive lower-slack premise is assumed before that
procedure performs its own guard.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual accepted Query-and-write result supplies every numeric,
representation and allocation premise of the following coefficient call. -/
theorem reportedEdge_coefficient_pre {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd e base lo up f c r a one mn mx E ld gd heap queryEnd : ℕ}
    {s : A.State} {x : R.τ} {mem queryMem : ℕ → ℕ}
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (queryCoordinateContract F A G m κ α rate allocation R b s x).post
      [b,e,base,lo,up,f,F.limbs,heap] mem queryEnd queryMem)
    (haccept : queryMem (queryEnd-(1+4*F.limbs))=1) :
    (coefficientStatusContract w F.fmt.limbBits q K).pre
      [m,c,r,lo,f,up,a,one,mn,mx,F.limbs,F.fmt.precision,E,ld,gd,queryEnd] queryMem := by
  obtain ⟨e',base',lo',up',f',c',r',a',one',mn',mx',E',ld',gd',heap',heq,hQp,
    hs,hend,hmn,hmx,hbaseEnd,hsrcFoot,hsep,hwidth,hld,hgd,hdis,_,_,_,hspace⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨e',base',lo',up',f',heap',heq,_,hbaseValid,_⟩ := hQp
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  change heap+(minRatioMachineContract F A G m κ α rate allocation).space 1 s [b,e,heap] mem+
    16*F.limbs+Num.IPM.lengthSpace F.limbs F.fmt.precision E+
    Num.IPM.gradientSpace F.limbs F.fmt.precision E+4<2^w at hspace
  have hupper := (queryCoordinate_frame F A G m κ α rate allocation R hout).2.1
  have hstatusSpace : queryEnd+(4*F.limbs+1)+F.limbs+
      Num.IPM.lengthSpace F.limbs F.fmt.precision E+
      Num.IPM.gradientSpace F.limbs F.fmt.precision E+2<2^w := by omega
  have hgpre := guardedCoefficient_pre_after_query F A G m κ α rate allocation R hout haccept
    hs hend hmn hmx hsrcFoot hsep ⟨hbaseValid,rfl⟩ hbaseEnd hwidth hld hgd hdis
    (by omega : queryEnd+(4*F.limbs+1)+F.limbs+
      Num.IPM.lengthSpace F.limbs F.fmt.precision E+
      Num.IPM.gradientSpace F.limbs F.fmt.precision E+1<2^w)
  exact ⟨hgpre,hstatusSpace⟩

end MinCostFlow.IPM.Machine
