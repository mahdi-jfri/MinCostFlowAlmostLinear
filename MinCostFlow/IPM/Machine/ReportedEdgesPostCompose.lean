module

import MinCostFlow.IPM.Machine.ReportedEdgeSafety

public import MinCostFlow.IPM.Machine.ReportedEdgesTailInput
public import MinCostFlow.IPM.Machine.ReportedEdgesSelectedAccuracy
public import MinCostFlow.IPM.Machine.ReportedEdgesUnlisted
public import MinCostFlow.IPM.Machine.ReportedEdgesPost
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Composing a successful first refresh with its tail

The tail contract preserves the first edge because Detect's names are
distinct. Its fine memory frame composes with the first call's frame.
The concrete footprints and allocation bounds also compose. Thus a
successful first refresh followed by any tail result has the complete
original list postcondition, including an early tail rejection.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 400000 in
/-- Compose the actual successful first-edge postcondition with the
complete tail postcondition, retaining the original list's frame and
cache guarantees on both possible tail outcomes. -/
theorem reportedEdges_post_cons {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names k base lo up f heap c r a one mn mx E ld gd e v u : ℕ}
    {s : A.State} {x mid : R.τ} {mem mem₁ mem₂ : ℕ → ℕ}
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,k+1,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hread : mem names=e)
    (hfirst : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
      [b,e,base+e*F.limbs,lo+e*F.limbs,up+e*F.limbs,f+e*F.limbs,F.limbs,heap,
        c+e*F.limbs,r,a,one,mn,mx,F.fmt.precision,E,ld+e*F.limbs,gd+e*F.limbs,m] mem v mem₁)
    (hrep₁ : R.rep b s mid mem₁)
    (hmeta₁ : ∀ z,R.foot b mid z → z<v ∧ (R.foot b x z ∨ heap≤z))
    (haccept : mem₁ (v-1)=1)
    (htail : (reportedEdgesContract F A G m rate allocation R b s mid q K sourceEnd tableEnd).post
      [b,names+1,k,base,lo,up,f,F.limbs,v,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem₁ u mem₂) :
    (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,k+1,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem u mem₂ := by
  have hpreCopy := hpre
  have htailCopy := htail
  have htailPre := reportedEdges_tail_pre F A G m κ α rate allocation R hpre hread hfirst hrep₁ hmeta₁ haccept
  have hcache₁ := reportedEdges_selected_accuracy F A G m κ α rate allocation R hpreCopy
    (i:=0) (by omega) (by simpa only [Nat.add_zero] using hread) hfirst haccept
  have hframe₁ := reportedEdge_frame F A G m κ α rate allocation R hfirst
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',es,heq,
    hlen,hnd,hlist,hgraph,_,_,_,hAvoid,hnFoot,hsEnd,htEnd,hnEnd,hends,_,hDis,_,_,_,hldEnd,hgdEnd,
    _,_,_,_,_,_,hspace⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  cases es with
  | nil => simp at hlen
  | cons first tail =>
    have hfirstName : first=e := (hlist 0 (by simp)).symm.trans (by simpa only [Nat.add_zero] using hread)
    subst first
    have hem := (hgraph e (by simp)).2
    have htailLen : tail.length=k := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hlen
    have hfEnd := (reported_entry_end f F.limbs e m hem).trans (hends f (by simp))
    have hlEnd := (reported_entry_end ld F.limbs e m hem).trans hldEnd
    have hgEnd := (reported_entry_end gd F.limbs e m hem).trans hgdEnd
    have hnamesSame : ∀ i<k+1,mem₁ (names+i)=mem (names+i) := by
      intro i hi
      exact hframe₁.2.2.2 _ (by omega) (hnFoot i hi) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inr (by omega))
    have hlist₁ : ListAt mem₁ names (e::tail) := by
      intro i hi
      exact (hnamesSame i (by simpa only [List.length_cons,htailLen] using hi)).trans (hlist i hi)
    have htailList : ListAt mem₁ (names+1) tail := by
      simpa only [List.drop_one,List.tail_cons] using hlist₁.drop 1
    have hcache₂ := reportedEdges_unlisted_cache F A G m rate allocation R tail htailPre htailCopy
      htailList htailLen hem (List.nodup_cons.mp hnd).1 hcache₁
    have hheapW : heap<2^w := by omega
    have halloc := query_allocation_le_bound (b:=b) allocation hem hheapW
    have hstepSpace : v≤heap+reportedEdgesScratch F m b E allocation := by
      have hu := hframe₁.2.1
      change v≤heap+allocation 1 [b,e,heap]+16*F.limbs+
        Num.IPM.lengthSpace F.limbs F.fmt.precision E+
        Num.IPM.gradientSpace F.limbs F.fmt.precision E+4 at hu
      unfold reportedEdgesScratch
      omega
    simp only [reportedEdgesContract,List.getD_cons_zero,List.getD_cons_succ] at htail
    obtain ⟨final,hrep₂,hmeta₂,hlo₂,hhi₂,hzero₂,hbit₂,hframe₂,hcacheTail,hSafeTail⟩ := htail
    refine reportedEdges_post_of_list F A G m rate allocation R (e::tail) hlist hlen hrep₂ ?_
      (hframe₁.1.trans hlo₂) ?_ hzero₂ hbit₂ ?_ ?_ ?_
    · intro z hz
      refine ⟨(hmeta₂ z hz).1,?_⟩
      rcases (hmeta₂ z hz).2 with hmid | hfresh
      · exact (hmeta₁ z hmid).2
      · exact Or.inr (hframe₁.1.trans hfresh)
    · simp only [Nat.add_mul,Nat.one_mul]
      omega
    · intro z hz hnot hsep
      have hhead := hsep e (by simp)
      have hsame₁ := hframe₁.2.2.2 z hz hnot hhead.1 hhead.2.1 hhead.2.2
      have hnotMid : ¬ R.foot b mid z := by
        intro hmid
        rcases (hmeta₁ z hmid).2 with hold | hfresh
        · exact hnot hold
        · omega
      have hsame₂ := hframe₂ tail htailList htailLen z (hz.trans_le hframe₁.1) hnotMid
        (fun j hj => hsep j (List.mem_cons_of_mem e hj))
      exact hsame₂.trans hsame₁
    · intro hb j hj
      rcases List.mem_cons.mp hj with hje | hj
      · subst j
        exact hcache₂
      · exact hcacheTail hb tail htailList htailLen j hj
    · have hsEq (j : ℕ) (hj : j∈tail) :
          ReportedCandidateSafe F A s mem₁ j (base+j*F.limbs) (lo+j*F.limbs) (up+j*F.limbs) E ↔
            ReportedCandidateSafe F A s mem j (base+j*F.limbs) (lo+j*F.limbs) (up+j*F.limbs) E := by
        have hjFull := List.mem_cons_of_mem e hj
        have hjm := (hgraph j hjFull).2
        have hblock (ptr : ℕ) (hp : ptr∈[base,lo,up]) :
            Num.fixVal mem₁ (ptr+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
              Num.fixVal mem (ptr+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := by
          have hp' : ptr∈[base,c,lo,up] := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hp ⊢
            tauto
          have hpEnd := (reported_entry_end ptr F.limbs j m hjm).trans
            (hends ptr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hp' ⊢; tauto))
          have hpSep := reported_entries_separated ptr f F.limbs j e m hjm hem (hDis ptr hp')
          unfold Num.fixVal
          apply congrArg (fun z : ℤ => (z : ℝ)/((2:ℝ)^F.fmt.precision))
          apply Num.intVal_congr
          intro t ht
          apply hframe₁.2.2.2 _ (by omega) (hAvoid _ (by omega))
          · rcases hpSep with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
          · exact Or.inl (by omega)
          · exact Or.inl (by omega)
        unfold ReportedCandidateSafe
        rw [hblock base (by simp),hblock lo (by simp),hblock up (by simp)]
      constructor
      · intro hb j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · have hs := reportedEdges_member_pre F A G m κ α rate allocation R hpreCopy
            (i:=0) (by omega) (by simpa only [Nat.add_zero] using hread)
          exact (reportedEdge_accepts_iff F A G m κ α rate allocation R hs hfirst).mp haccept
        · exact (hsEq j hj).mp ((hSafeTail tail htailList htailLen).mp hb j hj)
      · intro hs
        apply (hSafeTail tail htailList htailLen).mpr
        intro j hj
        exact (hsEq j hj).mpr (hs j (List.mem_cons_of_mem e hj))

end MinCostFlow.IPM.Machine
