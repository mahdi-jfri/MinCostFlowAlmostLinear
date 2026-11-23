module

public import MinCostFlow.IPM.Machine.DetectRefresh
import MinCostFlow.IPM.Machine.DetectNamesOutput
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Unreported coefficient blocks survive Detect and refresh

Detect changes its own representation. Its footprint remains separate
from the caller's tables. The refresh stage writes only reported
entries, and the final record is fresh. Hence every other coefficient
block, including unused dense-table entries, keeps its exact words.
This lets Update's full-table invariant be maintained with work only
on reported entries.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The complete combined stage preserves both coefficient blocks of
any fitting edge name outside the actual Detect set, on either outcome. -/
theorem detectRefresh_unreported_coefficients {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v e : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
    (he : e<m) (hne : e∉(A.detect s).1) :
    ∀ p∈[ld,gd],∀ i<F.limbs,mem' (p+e*F.limbs+i)=mem (p+e*F.limbs+i) := by
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,hcover,hsubset,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,all,heq,
    hlen,_,hlist,hgraph,_,_,_,hprefix,_,hsEnd,htEnd,hnEnd,hends,_,_,_,hsld,hsgd,hldEnd,hgdEnd,hdis,_⟩ := hfull
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
  have same_block (p : ℕ) (hpEnd : p+e*F.limbs+F.limbs≤tableEnd)
      (hpStart : sourceEnd≤p)
      (hsep : ∀ j∈es,(p+e*F.limbs+F.limbs≤ld+j*F.limbs ∨ ld+j*F.limbs+F.limbs≤p+e*F.limbs) ∧
        (p+e*F.limbs+F.limbs≤gd+j*F.limbs ∨ gd+j*F.limbs+F.limbs≤p+e*F.limbs)) :
      ∀ i<F.limbs,mem' (p+e*F.limbs+i)=mem (p+e*F.limbs+i) := by
    intro i hi
    let z := p+e*F.limbs+i
    have hzTable : z<tableEnd := by dsimp only [z]; omega
    have hnotOld := hprefix z hzTable
    have hnotNew : ¬ R.foot b detected z := by
      intro hfoot
      rcases (hDmeta z hfoot).2 with hold | hfresh
      · exact hnotOld hold
      · omega
    have hsD := hframeD z (by omega) hnotOld
    have hsR := hframeR es hreport hesLen z (by omega) hnotNew (by
      intro j hj
      have hjEnd := (reported_entry_end f F.limbs j m (hjM j (hes j hj))).trans hfEnd
      obtain ⟨hsl,hsg⟩ := hsep j hj
      refine ⟨Or.inr ?_,?_,?_⟩
      · dsimp only [z]; omega
      · rcases hsl with hh | hh <;> dsimp only [z] <;> omega
      · rcases hsg with hh | hh <;> dsimp only [z] <;> omega)
    exact (hframeRecord z (by omega)).trans (hsR.trans hsD)
  have hneq (j : ℕ) (hj : j∈es) : e≠j := fun hh => hne (hh ▸ hes j hj)
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with hp | hp
  all_goals subst p
  · apply same_block ld ((reported_entry_end ld F.limbs e m he).trans hldEnd) hsld
    intro j hj
    exact ⟨reported_blocks_disjoint ld F.limbs e j (hneq j hj),
      reported_entries_separated ld gd F.limbs e j m he (hjM j (hes j hj)) hdis⟩
  · apply same_block gd ((reported_entry_end gd F.limbs e m he).trans hgdEnd) hsgd
    intro j hj
    exact ⟨reported_entries_separated gd ld F.limbs e j m he (hjM j (hes j hj)) (hdis.elim Or.inr Or.inl),
      reported_blocks_disjoint gd F.limbs e j (hneq j hj)⟩

end MinCostFlow.IPM.Machine
