module

public import MinCostFlow.IPM.Machine.DetectRefresh
import MinCostFlow.IPM.Machine.DetectNamesOutput
import WordRAM.Memory

/-!
# Preserving the source prefix through Detect and refresh

The numeric flow table begins after the serialized source graph. The
combined input separates its preceding prefix from the DS footprint.
Detect's concrete footprint grows only into fresh allocation, and the
checked refresh writes only the selected flow and coefficient entries.
The final metadata record is fresh as well. Thus the whole preceding
source prefix is unchanged, supplying the graph for batch preparation.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Every word preceding the cached flow table survives the complete
combined stage, including either checked-refresh rejection branch. -/
theorem detectRefresh_frame {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem') :
    ∀ z<f,mem' z=mem z := by
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,all,heq,
    _,_,_,_,_,_,_,hprefix,_,hsEnd,htEnd,hnEnd,hends,_,_,_,hsld,hsgd,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hfEnd := hends f (by simp)
  simp only [detectRefreshContract,List.getD_cons_zero,List.getD_cons_succ] at hout
  obtain ⟨dHeap,dMem,detected,rHeap,rMem,final,hD,_,hDmeta,_,hR,hrecord,_⟩ := hout
  have hdata := detectNames_output F A G m κ α rate allocation R hD
  obtain ⟨es,hnd,hset,_,hnames⟩ := hdata.1
  have hlen : es.length=(A.detect s).1.card := by rw [← hset,List.toFinset_card_of_nodup hnd]
  obtain ⟨reserved,detectMem,snapshotEnd,snapshotMem,other,hDD,hDS,hvD,hPD,hFD,hZD,hRD,hMD,hND,hNPD,hLoD,hHiD,hframeD⟩ := hD
  change heap≤dHeap at hLoD
  change ∀ z<heap,¬ R.foot b x z → dMem z=mem z at hframeD
  simp only [reportedEdgesContract,List.getD_cons_zero,List.getD_cons_succ] at hR
  obtain ⟨_,_,_,hLoR,_,_,_,hframeR,_⟩ := hR
  have hframeRecord := hrecord.1.2.2.1
  change ∀ z<rHeap,mem' z=rMem z at hframeRecord
  intro z hz
  have hnotOld : ¬ R.foot b x z := hprefix z (by omega)
  have hnotDetected : ¬ R.foot b detected z := by
    intro hfoot
    rcases (hDmeta z hfoot).2 with hold | hfresh
    · exact hnotOld hold
    · omega
  have hsameD := hframeD z (by omega) hnotOld
  have hsameR := hframeR es hnames hlen z (by omega) hnotDetected
    (fun e _ => ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩)
  exact (hframeRecord z (by omega)).trans (hsameR.trans hsameD)

end MinCostFlow.IPM.Machine
