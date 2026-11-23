module

public import MinCostFlow.IPM.Machine.DetectRefresh
import MinCostFlow.IPM.Machine.DetectNamesOutput
import MinCostFlow.IPM.Machine.ReportedCacheCongr
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Decoding the complete Detect/refresh result

The final two words return the original stable report and the checked
refresh bit. The refresh's fine frame preserves every copied name, and
the final metadata write preserves the numeric tables. Thus a successful
result supplies the full cache postcondition for exactly the reported
set, together with the next model state's format fit.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Decode the actual report/status result. Success gives exact cached
Query recovery and valid approximate coefficients for every reported
edge; the report remains available for preparing the next Update batch. -/
theorem detectRefresh_output {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem') :
    DetectAt mem' (mem' (v-2)) (A.detect s).1 ∧ mem' (v-1)≤1 ∧
      MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision (A.detect s).2 ∧
      mem' (v-2)+1+(A.detect s).1.card≤v ∧
      (mem' (v-1)=1 → ∀ e∈(A.detect s).1,
        reportedCachePost F A (A.detect s).2 m q base lo up f c r a ld gd e mem') := by
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,hcover,hsubset,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,all,heq,
    hlen,_,hlist,hgraph,_,_,_,_,_,hsEnd,htEnd,hnEnd,hends,hshared,_,_,_,_,hldEnd,hgdEnd,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hmember (e : ℕ) (he : e∈G.E) : e∈all := by
    obtain ⟨i,hi,hread⟩ := hcover e he
    exact List.mem_iff_getElem.mpr ⟨i,by omega,(hlist i (by omega)).symm.trans hread⟩
  simp only [detectRefreshContract,List.getD_cons_zero,List.getD_cons_succ] at hout
  obtain ⟨dHeap,dMem,detected,rHeap,rMem,final,hD,hDrep,hDmeta,hDbefore,hR,hrecord,_⟩ := hout
  have hDdata := detectNames_output F A G m κ α rate allocation R hD
  let pointer := dMem (dHeap-1)
  obtain ⟨es,hnd,hset,hheader,hnames⟩ := hDdata.1
  have hesLen : es.length=(A.detect s).1.card := by rw [← hset,List.toFinset_card_of_nodup hnd]
  have heG (e : ℕ) (he : e∈es) : e∈G.E :=
    hsubset (by rw [← hset]; exact List.mem_toFinset.mpr he)
  have heM (e : ℕ) (he : e∈es) : e<m := (hgraph e (hmember e (heG e he))).2
  simp only [reportedEdgesContract,List.getD_cons_zero,List.getD_cons_succ] at hR
  obtain ⟨_,_,_,hLoR,_,_,hbit,hframeR,hcacheR,_⟩ := hR
  have hframeRecord := hrecord.1.2.2.1
  change ∀ z<rHeap,mem' z=rMem z at hframeRecord
  have hrecordOut := reportStatus_output hrecord
  have hnamesSame : ∀ i<1+(A.detect s).1.card,mem' (pointer+i)=dMem (pointer+i) := by
    intro i hi
    have hnot : ¬ R.foot b detected (pointer+i) := by
      intro hz
      have hh := hDbefore (pointer+i) hz
      dsimp only [pointer] at hh ⊢
      omega
    have hsameR := hframeR es hnames hesLen (pointer+i) (by dsimp only [pointer]; omega) hnot
    have hsame : rMem (pointer+i)=dMem (pointer+i) := by
      apply hsameR
      intro j hj
      have hfEnd := (reported_entry_end f F.limbs j m (heM j hj)).trans (hends f (by simp))
      have hlEnd := (reported_entry_end ld F.limbs j m (heM j hj)).trans hldEnd
      have hgEnd := (reported_entry_end gd F.limbs j m (heM j hj)).trans hgdEnd
      dsimp only [pointer]
      exact ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (by omega)⟩
    exact (hframeRecord (pointer+i) (by dsimp only [pointer]; omega)).trans hsame
  have hreport : DetectAt mem' pointer (A.detect s).1 := by
    refine ⟨es,hnd,hset,?_,?_⟩
    · have hh : mem' pointer=dMem pointer := by
        simpa only [Nat.add_zero] using hnamesSame 0 (by omega)
      exact hh.trans hheader
    · intro i hi
      have hh := hnamesSame (1+i) (by omega)
      simp only [← Nat.add_assoc] at hh
      exact hh.trans (hnames i hi)
  refine ⟨by simpa only [hrecordOut.1] using hreport,?_,hDdata.2.2.2,?_,?_⟩
  · rw [hrecordOut.2]
    exact hbit
  · rw [hrecordOut.1]
    have hv := hrecord.2
    change v=rHeap+2 at hv
    omega
  · intro hb e he
    have heList : e∈es := List.mem_toFinset.mp (by rw [hset]; exact he)
    have hem := heM e heList
    have hcache := hcacheR (hrecordOut.2.symm.trans hb) es hnames hesLen e heList
    apply reportedCachePost_congr F A (A.detect s).2 (hpost:=hcache)
    intro p hp i hi
    have hblockEnd : p+F.limbs≤tableEnd := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp
      all_goals subst p
      · exact ((reported_entry_end base F.limbs e m hem).trans (hends base (by simp))).trans hsEnd
      · exact ((reported_entry_end c F.limbs e m hem).trans (hends c (by simp))).trans hsEnd
      · exact (hshared r (by simp)).trans hsEnd
      · exact ((reported_entry_end lo F.limbs e m hem).trans (hends lo (by simp))).trans hsEnd
      · exact ((reported_entry_end f F.limbs e m hem).trans (hends f (by simp))).trans hsEnd
      · exact ((reported_entry_end up F.limbs e m hem).trans (hends up (by simp))).trans hsEnd
      · exact (hshared a (by simp)).trans hsEnd
      · exact (reported_entry_end ld F.limbs e m hem).trans hldEnd
      · exact (reported_entry_end gd F.limbs e m hem).trans hgdEnd
    exact hframeRecord (p+i) (by omega)

end MinCostFlow.IPM.Machine
