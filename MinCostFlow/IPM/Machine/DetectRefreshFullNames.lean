module

public import MinCostFlow.IPM.Machine.DetectRefresh
import MinCostFlow.IPM.Machine.DetectNamesOutput
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Preserving the original full edge-name list

The full name list follows the coefficient tables and precedes the
incoming heap. Detect preserves those caller words, and its footprint
grows only into fresh memory. Every refresh writes below the original
name list or into fresh workspace. Thus the next iteration can reuse
that same full list on either guard outcome.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual Detect/refresh preserves every original full-list name,
independently of the order and size of the returned report. -/
theorem detectRefresh_full_names {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
 :
    ∀ i<m,mem' (names+i)=mem (names+i) := by
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,hcover,hsubset,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,all,heq,
    hlen,_,hlist,hgraph,_,_,_,hprefix,hnameAvoid,hsEnd,htEnd,hnEnd,hends,_,_,_,hsld,hsgd,hldEnd,hgdEnd,hdis,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hmember (j : ℕ) (hj : j∈G.E) : j∈all := by
    obtain ⟨i,hi,hread⟩ := hcover j hj
    exact List.mem_iff_getElem.mpr ⟨i,by omega,(hlist i (by omega)).symm.trans hread⟩
  have hjM (j : ℕ) (hj : j∈(A.detect s).1) : j<m :=
    (hgraph j (hmember j (hsubset hj))).2
  simp only [detectRefreshContract,List.getD_cons_zero,List.getD_cons_succ] at hout
  obtain ⟨dHeap,dMem,detected,rHeap,rMem,final,hD,_,hDmeta,_,hR,hrecord,_⟩ := hout
  have hdata := detectNames_output F A G m κ α rate allocation R hD
  obtain ⟨es,hnd,hset,_,hreport⟩ := hdata.1
  have hesLen : es.length=(A.detect s).1.card := by rw [← hset,List.toFinset_card_of_nodup hnd]
  have hes (j : ℕ) (hj : j∈es) : j∈(A.detect s).1 := by rw [← hset]; exact List.mem_toFinset.mpr hj
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLoD,_,hframeD⟩ := hD
  change heap≤dHeap at hLoD
  change ∀ z<heap,¬ R.foot b x z → dMem z=mem z at hframeD
  simp only [reportedEdgesContract,List.getD_cons_zero,List.getD_cons_succ] at hR
  obtain ⟨_,_,_,hLoR,_,_,_,hframeR,_⟩ := hR
  have hframeRecord := hrecord.1.2.2.1
  change ∀ z<rHeap,mem' z=rMem z at hframeRecord
  have hfEnd := hends f (by simp)
  intro i hi
  let z := names+i
  have hzHeap : z<heap := by dsimp only [z]; omega
  have hnotOld : ¬R.foot b x z := hnameAvoid i hi
  have hnotNew : ¬R.foot b detected z := by
    intro hz
    rcases (hDmeta z hz).2 with hold | hfresh
    · exact hnotOld hold
    · omega
  have hsameD := hframeD z hzHeap hnotOld
  have hsameR := hframeR es hreport hesLen z (by omega) hnotNew (by
    intro j hj
    have hjm := hjM j (hes j hj)
    have hf := (reported_entry_end f F.limbs j m hjm).trans hfEnd
    have hl := (reported_entry_end ld F.limbs j m hjm).trans hldEnd
    have hg := (reported_entry_end gd F.limbs j m hjm).trans hgdEnd
    dsimp only [z]
    exact ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (by omega)⟩)
  exact (hframeRecord z (by omega)).trans (hsameR.trans hsameD)

end MinCostFlow.IPM.Machine
