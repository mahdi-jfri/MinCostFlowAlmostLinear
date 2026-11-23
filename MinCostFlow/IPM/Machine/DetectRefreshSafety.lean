module

public import MinCostFlow.IPM.Machine.DetectRefresh
import MinCostFlow.IPM.Machine.DetectNamesOutput
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Accepting the full Detect report when all its candidates are safe

Detect changes only its footprint and fresh workspace. It preserves
the base and capacity tables. The reported-list guard thus accepts
when the candidate slacks in the original memory are safe. The final
pointer record copies that actual status.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Safe candidate slacks for all actual reported names force the
complete Detect/refresh success bit. -/
theorem detectRefresh_accepts_safe {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {s : A.State} {x : R.τ} {mem final : ℕ → ℕ}
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v final)
    (hsafe : ∀ e∈(A.detect s).1,ReportedCandidateSafe F A (A.detect s).2 mem
      e (base+e*F.limbs) (lo+e*F.limbs) (up+e*F.limbs) E) : final (v-1)=1 := by
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,hcover,hsubset,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,all,heq,
    hlen,_,hlist,hgraph,_,_,_,hprefix,_,hsEnd,htEnd,hnEnd,hends,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  simp only [detectRefreshContract,List.getD_cons_zero,List.getD_cons_succ] at hout
  obtain ⟨dEnd,dMem,mid,rEnd,rMem,other,hD,_,_,_,hR,hRecord,_⟩ := hout
  obtain ⟨es,hnd,hset,_,hreport⟩ := (detectNames_output F A G m κ α rate allocation R hD).1
  have hlenR : es.length=(A.detect s).1.card := by rw [← hset,List.toFinset_card_of_nodup hnd]
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hDframe⟩ := hD
  have hmem : ∀ z<sourceEnd,dMem z=mem z := fun z hz =>
    hDframe.2 z (by change z<heap; omega) (hprefix z (hz.trans_le hsEnd))
  have hSafe (e : ℕ) (he : e∈es) : ReportedCandidateSafe F A (A.detect s).2 dMem
      e (base+e*F.limbs) (lo+e*F.limbs) (up+e*F.limbs) E := by
    have heD : e∈(A.detect s).1 := hset ▸ List.mem_toFinset.mpr he
    obtain ⟨j,hj,hread⟩ := hcover e (hsubset heD)
    have heAll : e∈all := List.mem_iff_getElem.mpr ⟨j,by omega,(hlist j (by omega)).symm.trans hread⟩
    have hem := (hgraph e heAll).2
    have hfix (ptr : ℕ) (hp : ptr∈[base,lo,up]) :
        Num.fixVal dMem (ptr+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
          Num.fixVal mem (ptr+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision :=
      Num.IPM.fixVal_frozen hmem ((reported_entry_end ptr F.limbs e m hem).trans
        (hends ptr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hp ⊢; tauto)))
    simpa only [ReportedCandidateSafe,hfix base (by simp),hfix lo (by simp),hfix up (by simp)] using hsafe e heD
  obtain ⟨_,_,_,_,_,_,_,_,_,hSafeR⟩ := hR
  have hbit := (hSafeR es hreport hlenR).mpr hSafe
  exact (reportStatus_output hRecord).2.trans hbit

end MinCostFlow.IPM.Machine
