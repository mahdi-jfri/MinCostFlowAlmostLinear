module

public import MinCostFlow.IPM.Machine.DetectRefreshOutput
public import MinCostFlow.IPM.Machine.DetectRefreshFrame
public import MinCostFlow.IPM.Machine.DetectBatchProgram
import WordRAM.Memory

/-!
# Preparing an Update batch from the checked Detect report

The serialized fixed graph lies before the cached-flow table and
survives Detect/refresh. The returned report still represents exactly
the original specification's set. These facts complete the verified
batch writer's input conditions, preserving the report's actual order.
The driver invokes this writer only after accepting the returned bit.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual combined-stage output supplies the complete fixed-graph
batch preparation input, with its source graph preserved by the prefix
frame and its stable report decoded from the result record. -/
theorem detectBatch_pre_after_detectRefresh {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v source : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem v mem')
    (hI : I.IsValid) (hgraph : ListAt mem source (zeroLowerWords I))
    (hgraphEnd : source+(zeroLowerWords I).length≤f)
    (hwords : ∀ z∈zeroLowerWords I,z<2^w)
    (hspace : v+(1+6*(A.detect s).1.card)<2^w) :
    (detectBatchContract w I (A.detect s).1).pre [source,mem' (v-2),v] mem' := by
  have hresult := detectRefresh_output F A (namedInstance I) I.m κ α rate allocation R hpre hout
  have hframe := detectRefresh_frame F A (namedInstance I) I.m κ α rate allocation R hpre hout
  have hgraph' := hgraph.of_agree_below hgraphEnd hframe
  have houtCopy := hout
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,_,hsubset,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,all,heq,
    _,_,_,_,_,_,_,_,_,hsEnd,htEnd,hnEnd,hends,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hfEnd := hends f (by simp)
  simp only [detectRefreshContract,List.getD_cons_zero,List.getD_cons_succ] at houtCopy
  obtain ⟨dHeap,dMem,detected,rHeap,rMem,final,hD,hDrep,hDmeta,hB,hRF,hRec,hR,hM,hzero,hLo,_⟩ := houtCopy
  exact ⟨⟨source,mem' (v-2),v,rfl,hI,hgraph',hresult.1,hsubset,by omega,
    hresult.2.2.2.1,hwords⟩,hzero,hspace⟩

end MinCostFlow.IPM.Machine
