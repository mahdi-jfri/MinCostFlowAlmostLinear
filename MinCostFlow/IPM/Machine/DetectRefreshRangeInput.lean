module

public import MinCostFlow.IPM.Machine.DetectRefreshOutput
public import MinCostFlow.IPM.Machine.CoefficientRangeInput

/-!
# The actual refresh result supplies the coefficient-check input

On acceptance, the combined Detect/refresh program returns valid
coefficients for every reported name. Its preserved snapshot supplies
the iteration order. The original full-edge coverage gives fitting
edge offsets and table extents. Only the fixed range endpoints need to
be supplied by the caller's unchanged constant blocks.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Successful actual refresh gives the full next range-scan input.
No coefficient range assertion is assumed before that scan. -/
theorem coefficientRangeList_pre_after_detectRefresh {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v neg maximum minimum : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
    (haccept : mem' (v-1)=1) (hvWord : v<2^w) (hmWord : m<2^w)
    (hnEnd : neg+F.limbs<2^w) (hxEnd : maximum+F.limbs<2^w)
    (hmEnd : minimum+F.limbs<2^w)
    (hnValid : Num.Valid mem' neg F.fmt.limbBits F.limbs)
    (hxValid : Num.Valid mem' maximum F.fmt.limbBits F.limbs)
    (hmValid : Num.Valid mem' minimum F.fmt.limbBits F.limbs) :
    (coefficientRangeListContract w F.fmt.limbBits).pre
      [mem' (v-2)+1,(A.detect s).1.card,gd,ld,neg,maximum,minimum,F.limbs] mem' := by
  have hdata := detectRefresh_output F A G m κ α rate allocation R hpre hout
  have houtCopy := hout
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,hcover,hsubset,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,all,heq,
    hlen,_,hlist,hgraph,_,_,_,_,_,hsEnd,htEnd,hnEnd0,_,_,_,_,_,_,hldEnd,hgdEnd,
    _,_,_,_,_,hw,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hmember (e : ℕ) (he : e∈G.E) : e∈all := by
    obtain ⟨i,hi,hread⟩ := hcover e he
    exact List.mem_iff_getElem.mpr ⟨i,by omega,(hlist i (by omega)).symm.trans hread⟩
  have hem (e : ℕ) (he : e∈(A.detect s).1) : e<m :=
    (hgraph e (hmember e (hsubset he))).2
  simp only [detectRefreshContract,List.getD_cons_zero,List.getD_cons_succ] at houtCopy
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLo,_⟩ := houtCopy
  apply coefficientRangeList_pre_of_detect hdata.1 hdata.2.2.2.1 hvWord hw hmWord hem
    (hgEnd:=by omega) (hlEnd:=by omega) hnEnd hxEnd hmEnd hnValid hxValid hmValid
  intro e he
  have hc := hdata.2.2.2.2 haccept e he
  exact ⟨hc.2.2.2.2.1,hc.2.2.1⟩

end MinCostFlow.IPM.Machine
