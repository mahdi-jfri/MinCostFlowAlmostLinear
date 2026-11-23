module

public import MinCostFlow.IPM.Machine.DetectRefreshRangeInput
public import MinCostFlow.IPM.Machine.DetectRefreshFrame
public import MinCostFlow.IPM.Machine.CoefficientRangeReport
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Calling the checked coefficient report after actual refresh

The fixed range constants lie before the cached-flow table. The
combined refresh preserves that prefix and returns valid reported
coefficient blocks plus its stable report. These facts supply the
complete next checked-report input and every argument word bound,
without assuming that the new coefficient range checks accept.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The accepted actual Detect/refresh result supplies all inputs of the
checked-report entry, including unchanged range constants and workspace. -/
theorem coefficientRangeReport_pre_after_detectRefresh {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v neg maximum minimum : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
    (haccept : mem' (v-1)=1) (hmWord : m<2^w) (hspace : v+2<2^w)
    (hnEnd : neg+F.limbs≤f) (hxEnd : maximum+F.limbs≤f) (hmEnd : minimum+F.limbs≤f)
    (hnValid : Num.Valid mem neg F.fmt.limbBits F.limbs)
    (hxValid : Num.Valid mem maximum F.fmt.limbBits F.limbs)
    (hmValid : Num.Valid mem minimum F.fmt.limbBits F.limbs) :
    (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1).pre
      [mem' (v-2),gd,ld,neg,maximum,minimum,F.limbs,v] mem' ∧
    (∀ z∈[mem' (v-2),gd,ld,neg,maximum,minimum,F.limbs,v],z<2^w) := by
  have hdata := detectRefresh_output F A G m κ α rate allocation R hpre hout
  have hframe := detectRefresh_frame F A G m κ α rate allocation R hpre hout
  have hpreCopy := hpre
  have houtCopy := hout
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,_⟩ := hpreCopy
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,all,heq,
    _,_,_,_,_,_,_,_,_,hsEnd,htEnd,hnamesEnd,hends,_,_,_,_,_,hldEnd,hgdEnd,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hfEnd := hends f (by simp)
  simp only [detectRefreshContract,List.getD_cons_zero,List.getD_cons_succ] at houtCopy
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hzero,hLo,_⟩ := houtCopy
  have hfV : f≤v := by omega
  have hvWord : v<2^w := by omega
  have hnWord : neg+F.limbs<2^w := (hnEnd.trans hfV).trans_lt hvWord
  have hxWord : maximum+F.limbs<2^w := (hxEnd.trans hfV).trans_lt hvWord
  have hmWord' : minimum+F.limbs<2^w := (hmEnd.trans hfV).trans_lt hvWord
  have hrange := coefficientRangeList_pre_after_detectRefresh F A G m κ α rate allocation R hpre hout
    haccept hvWord hmWord hnWord hxWord hmWord'
    (Num.IPM.valid_frozen hframe hnEnd hnValid) (Num.IPM.valid_frozen hframe hxEnd hxValid)
    (Num.IPM.valid_frozen hframe hmEnd hmValid)
  refine ⟨⟨mem' (v-2),gd,ld,neg,maximum,minimum,F.limbs,v,rfl,hdata.1,hdata.2.2.2.1,hrange,hzero,hspace⟩,?_⟩
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with hz | hz | hz | hz | hz | hz | hz | hz
  all_goals subst z
  · have hh := hdata.2.2.2.1
    omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact F.parameters_fit.1
  · exact hvWord

end MinCostFlow.IPM.Machine
