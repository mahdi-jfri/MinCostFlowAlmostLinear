module

public import MinCostFlow.IPM.Machine.ReportedEdgeOutput

/-!
# Successful refresh accuracy at the final stored coordinate

After Query recovery, the coefficient guard evaluates lengths and
gradients using the recovered coordinate. All later writes lie beyond
the numeric source prefix. Thus the accepted coefficient bounds refer
to the final cached flow and held residual. This supplies the local
numeric invariant for the reported-list loop.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Success stores the exact recovered coordinate and valid numerical
coefficients with the required tolerances for the final cached inputs. -/
theorem reportedEdge_accuracy {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    {b q K sourceEnd e base lo up f c r a one mn mx E ld gd heap v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ} {baseValue : ℝ}
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
    (hbase : ScalarAt mem base F.fmt.limbBits F.limbs F.fmt.precision baseValue)
    (haccept : mem' (v-1)=1) :
    ScalarAt mem' f F.fmt.limbBits F.limbs F.fmt.precision (baseValue+A.query s e) ∧
    Num.Valid mem' ld F.fmt.limbBits F.limbs ∧
    ScalarApprox (1+1/(2:ℝ)^q) (Num.fixVal mem' ld F.fmt.limbBits F.limbs F.fmt.precision)
      (Num.IPM.arrayLength mem' lo f up a F.fmt.limbBits F.limbs F.fmt.precision 0) ∧
    Num.Valid mem' gd F.fmt.limbBits F.limbs ∧
    |Num.fixVal mem' gd F.fmt.limbBits F.limbs F.fmt.precision-
      Num.IPM.arrayGradient mem' m c r lo f up a F.fmt.limbBits F.limbs F.fmt.precision 0|≤
      (1/(2:ℝ)^q)*Num.IPM.arrayLength mem' lo f up a F.fmt.limbBits F.limbs F.fmt.precision 0 := by
  obtain ⟨queryEnd,queryMem,hQ,_,hcoef,hflow⟩ :=
    reportedEdge_accepted F A G m κ α rate allocation R hpre hout hbase haccept
  obtain ⟨e',base',lo',up',f',c',r',a',one',mn',mx',E',ld',gd',heap',heq,_,hs,hend,_,_,_,_,_,_,
    hld,hgd,_,hsld,hsgd,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨_,_,_,_,_,_,_,hc,hr,hlo,hf,hup,ha,_⟩ := hs
  have hquery := (queryCoordinate_frame F A G m κ α rate allocation R hQ).1
  have hacc := coefficientStatus_accuracy hcoef haccept
    (hc.trans (hend.trans hquery)) (hr.trans (hend.trans hquery))
    (hlo.trans (hend.trans hquery)) (hf.trans (hend.trans hquery))
    (hup.trans (hend.trans hquery)) (ha.trans (hend.trans hquery))
    (hld.trans hquery) (hgd.trans hquery)
  have hframe : ∀ z<sourceEnd,mem' z=queryMem z := by
    intro z hz
    exact (coefficientStatus_frame hcoef).2.2.2 z (by omega)
      (Or.inl (by omega)) (Or.inl (by omega))
  have hl := Num.IPM.arrayLength_frozen (lo:=lo) (f:=f) (up:=up) (h:=F.fmt.limbBits)
    (P:=F.fmt.precision) (i:=0) hframe (by simpa using hlo) (by simpa using hf)
    (by simpa using hup) ha
  have hg := Num.IPM.arrayGradient_frozen (m:=m) (c:=c) (lo:=lo) (f:=f) (up:=up)
    (h:=F.fmt.limbBits) (P:=F.fmt.precision) (i:=0) hframe (by simpa using hc) hr
    (by simpa using hlo) (by simpa using hf) (by simpa using hup) ha
  refine ⟨hflow,?_⟩
  simpa only [hl,hg] using hacc

end MinCostFlow.IPM.Machine
