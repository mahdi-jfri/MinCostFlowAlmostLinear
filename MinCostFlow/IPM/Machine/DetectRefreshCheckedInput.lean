module

public import MinCostFlow.IPM.Machine.DetectRefreshRangeReportInput
public import MinCostFlow.IPM.Machine.DetectRefreshBatchInput
public import MinCostFlow.IPM.Machine.DetectRefreshTableInput
public import MinCostFlow.IPM.Machine.CheckedUpdate
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Complete checked-driver input from the actual Detect/refresh result

The graph, normalization and range constants lie in the unchanged
source prefix. Successful refresh supplies valid new coefficient blocks
and leaves other entries unchanged. Transfer the old bounds only for
those other entries. Together with the established implicit-flow range
and one explicit budget, these facts supply every checked-driver input
and word bound without assuming its new range checks accept.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The gradient and length tables at `gd` and `ld` hold `g` and `l` on the
edges of the IPM graph. -/
@[expose] def CoefficientTablesAt {w : ℕ} (F : MinRatioFormat w) (I : Instance) (mem : ℕ → ℕ)
    (gd ld : ℕ) (g l : ℕ → ℝ) : Prop :=
  ∀ e∈(namedInstance I).E,
    readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision I.m e=g e ∧
    readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m e=l e

/-- The accepted actual combined refresh supplies the entire next
checked-driver packet. Its numerical and model premises are input
invariants, and the reported values' ranges are left for the program. -/
theorem checkedUpdate_pre_after_detectRefresh {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v source eta neg maximum minimum : ℕ}
    {s : A.State} {x final : R.τ} {mem mem' : ℕ → ℕ} {request : ℝ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem v mem')
    (haccept : mem' (v-1)=1)
    (hrep : R.rep b (A.detect s).2 final mem') (hfoot : ∀ z,R.foot b final z → z<v)
    (hbWord : b<2^w) (hmWord : I.m<2^w)
    (hI : I.IsValid) (hgraph : ListAt mem source (zeroLowerWords I))
    (hgraphEnd : source+(zeroLowerWords I).length≤f) (hgraphWords : ∀ z∈zeroLowerWords I,z<2^w)
    (heEnd : eta+F.limbs≤f) (hnEnd : neg+F.limbs≤f)
    (hxEnd : maximum+F.limbs≤f) (hmEnd : minimum+F.limbs≤f)
    (hrequest : ScalarAt mem eta F.fmt.limbBits F.limbs F.fmt.precision request)
    (heLo : (2:ℝ)^(-(F.rangeExponent:ℤ))≤request) (heHi : request≤(2:ℝ)^F.rangeExponent)
    (hn : ScalarAt mem neg F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hx : ScalarAt mem maximum F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hm : ScalarAt mem minimum F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hk : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α)
    (hprec : 5*F.rangeExponent+Nat.size I.m+30≤F.fmt.precision)
    (hq : ∀ e∈(namedInstance I).E,|A.query (A.detect s).2 e|≤(2:ℝ)^F.rangeExponent)
    (hvalid : ∀ e<I.m,Num.Valid mem (gd+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (ld+e*F.limbs) F.fmt.limbBits F.limbs)
    (hrange : ∀ e∈(namedInstance I).E,
      |readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)
    (hreached : MinRatioReachedWith A (namedInstance I) s
      (readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m))
    (hspace : (v+2)+(1+6*(A.detect s).1.card)+updateAllocationBound w b gd ld eta allocation+(1+2*F.limbs)+2<2^w) :
    (checkedUpdateContract F A I κ α rate allocation R b (A.detect s).2 final (A.detect s).1).pre
      [b,source,mem' (v-2),gd,ld,eta,F.limbs,v,neg,maximum,minimum] mem' ∧
    (∀ z∈[b,source,mem' (v-2),gd,ld,eta,F.limbs,v,neg,maximum,minimum],z<2^w) := by
  have hd := detectRefresh_output F A (namedInstance I) I.m κ α rate allocation R hpre hout
  have hf := detectRefresh_frame F A (namedInstance I) I.m κ α rate allocation R hpre hout
  have ht := detectRefresh_table_input F A (namedInstance I) I.m κ α rate allocation R hpre hout haccept hvalid
  have hRpt := coefficientRangeReport_pre_after_detectRefresh F A (namedInstance I) I.m κ α rate allocation R
    hpre hout haccept hmWord (by omega) hnEnd hxEnd hmEnd hn.1 hx.1 hm.1
  have hBatch := detectBatch_pre_after_detectRefresh F A I κ α rate allocation R hpre hout hI hgraph hgraphEnd hgraphWords (by omega)
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
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLo,_⟩ := houtCopy
  have hfV : f≤v := by omega
  have hvWord : v<2^w := by omega
  have scalar_same (p : ℕ) (hp : p+F.limbs≤f) {value : ℝ}
      (hv : ScalarAt mem p F.fmt.limbBits F.limbs F.fmt.precision value) :
      ScalarAt mem' p F.fmt.limbBits F.limbs F.fmt.precision value :=
    ⟨Num.IPM.valid_frozen hf hp hv.1,(Num.IPM.fixVal_frozen hf hp).trans hv.2⟩
  have hrequest' := scalar_same eta heEnd hrequest
  refine ⟨?_,?_⟩
  · refine ⟨source,mem' (v-2),gd,ld,eta,v,neg,maximum,minimum,rfl,hBatch,hRpt.1,hrep,hfoot,
      hd.2.2.1,hk,hprec,hq,by omega,by omega,heEnd.trans hfV,hrequest'.1,?_,?_,ht.1,
      scalar_same neg hnEnd hn,scalar_same maximum hxEnd hx,scalar_same minimum hmEnd hm,?_,hspace,?_⟩
    · rw [hrequest'.2]
      exact heLo
    · rw [hrequest'.2]
      exact heHi
    · intro e he hne
      have heM : e<I.m := Finset.mem_range.mp he
      have hs := ht.2 e heM hne
      rw [hs.1,hs.2]
      exact hrange e he
    · refine hreached.detectedWith (fun e he hne => ?_)
      exact ht.2 e (Finset.mem_range.mp he) hne
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz
    all_goals subst z
    · exact hbWord
    · omega
    · exact hRpt.2 _ (by simp)
    · exact hRpt.2 _ (by simp)
    · exact hRpt.2 _ (by simp)
    · omega
    · exact F.parameters_fit.1
    · exact hvWord
    · exact hRpt.2 _ (by simp)
    · exact hRpt.2 _ (by simp)
    · exact hRpt.2 _ (by simp)

end MinCostFlow.IPM.Machine
