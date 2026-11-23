module

public import MinCostFlow.IPM.Machine.ReportedEdgesMemberInput
public import MinCostFlow.IPM.Machine.ReportedEdgeAccuracy
public import MinCostFlow.IPM.Machine.ReportedSourcesFamily

/-!
# Advancing the reported-list input invariant

After a successful first refresh, the remaining names still lie outside
the DS footprint. The static tables are unchanged, the numeric source
family remains valid, and one iteration's scratch allocation has been
consumed. Construct the full input condition for the tail with the
returned endpoint. This is a preservation lemma for the actual checked
call, not an additional requirement on the parameter data structure.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A successful refresh of the first name leaves the full list input
conditions for its tail, with one fewer scratch allocation reserved. -/
theorem reportedEdges_tail_pre {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names k base lo up f heap c r a one mn mx E ld gd e v : ℕ}
    {s : A.State} {x x' : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,k+1,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hread : mem names=e)
    (hout : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
      [b,e,base+e*F.limbs,lo+e*F.limbs,up+e*F.limbs,f+e*F.limbs,F.limbs,heap,
        c+e*F.limbs,r,a,one,mn,mx,F.fmt.precision,E,ld+e*F.limbs,gd+e*F.limbs,m] mem v mem')
    (hrep' : R.rep b s x' mem')
    (hmeta : ∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heap≤z))
    (haccept : mem' (v-1)=1) :
    (reportedEdgesContract F A G m rate allocation R b s x' q K sourceEnd tableEnd).pre
      [b,names+1,k,base,lo,up,f,F.limbs,v,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem' := by
  have hselected := reportedEdges_member_pre F A G m κ α rate allocation R hpre
    (i:=0) (by omega) (by simpa only [Nat.add_zero] using hread)
  have hsourceFrame := reportedEdge_source_frame F A G m κ α rate allocation R hselected hout
  have hframe := reportedEdge_frame F A G m κ α rate allocation R hout
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',es,heq,
    hlen,hnd,hlist,hgraph,hfit,hrep,hfoot,hprefix,hnFoot,hsEnd,htEnd,hnEnd,hends,hshared,
    htables,hscalars,hsld,hsgd,hldEnd,hgdEnd,hdis,hfamily,hbase,hrange,hz,hw,hspace⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  cases es with
  | nil => simp at hlen
  | cons first tail =>
    have hfirst : first=e := (hlist 0 (by simp)).symm.trans (by simpa only [Nat.add_zero] using hread)
    subst first
    have heList : e∈e::tail := by simp
    have hem := (hgraph e heList).2
    have htailLen : tail.length=k := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hlen
    have hflow := (reportedEdge_accuracy F A G m κ α rate allocation R hselected hout
      ⟨hbase e heList,rfl⟩ haccept).1.1
    have hfamily' := reported_sources_family_after_write
      (S:=(e::tail).toFinset) (e:=e)
      (fun j hj => hfamily j (List.mem_toFinset.mp hj))
      (fun j hj => (hgraph j (List.mem_toFinset.mp hj)).2) hem hsourceFrame hflow
      (fun p hp => hends p (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using Or.inr hp))
      hshared (fun p hp => htables p (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using Or.inr hp)) hscalars
    have same_static (p : ℕ) (hp : p∈[base,c,lo,up]) (j : ℕ) (hj : j<m) :
        ∀ i<F.limbs,mem' (p+j*F.limbs+i)=mem (p+j*F.limbs+i) := by
      have hend := (reported_entry_end p F.limbs j m hj).trans (hends p (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hp ⊢
        tauto))
      have hd := reported_entries_separated p f F.limbs j e m hj hem (htables p hp)
      intro i hi
      apply hsourceFrame (p+j*F.limbs+i) (by omega)
      rcases hd with hh | hh <;> omega
    have fix_static (p : ℕ) (hp : p∈[base,c,lo,up]) (j : ℕ) (hj : j<m) :
        Num.fixVal mem' (p+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
          Num.fixVal mem (p+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := by
      unfold Num.fixVal
      rw [Num.intVal_congr (same_static p hp j hj)]
    have hfEnd := (reported_entry_end f F.limbs e m hem).trans (hends f (by simp))
    have hlEnd := (reported_entry_end ld F.limbs e m hem).trans hldEnd
    have hgEnd := (reported_entry_end gd F.limbs e m hem).trans hgdEnd
    have hnamesSame : ∀ i<k+1,mem' (names+i)=mem (names+i) := by
      intro i hi
      exact hframe.2.2.2 _ (by omega) (hnFoot i hi) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inr (by omega))
    have hlist' : ListAt mem' names (e::tail) := by
      intro i hi
      exact (hnamesSame i (by simpa only [List.length_cons,htailLen] using hi)).trans (hlist i hi)
    have hheapW : heap<2^w := by omega
    have halloc := query_allocation_le_bound (b:=b) allocation hem hheapW
    have hstepSpace : v≤heap+reportedEdgesScratch F m b E allocation := by
      have hu := hframe.2.1
      change v≤heap+allocation 1 [b,e,heap]+16*F.limbs+
        Num.IPM.lengthSpace F.limbs F.fmt.precision E+
        Num.IPM.gradientSpace F.limbs F.fmt.precision E+4 at hu
      unfold reportedEdgesScratch
      omega
    refine ⟨names+1,k,base,lo,up,f,v,c,r,a,one,mn,mx,E,ld,gd,tail,rfl,htailLen,
      hnd.tail,?_,?_,hfit,hrep',?_,?_,?_,hsEnd,by omega,by omega,hends,hshared,
      htables,hscalars,hsld,hsgd,hldEnd,hgdEnd,hdis,?_,?_,?_,hframe.2.2.1,hw,?_⟩
    · simpa only [List.drop_one,List.tail_cons] using hlist'.drop 1
    · intro j hj
      exact hgraph j (List.mem_cons_of_mem e hj)
    · intro z hz0
      exact (hmeta z hz0).1
    · intro z hz0 hzFoot
      rcases (hmeta z hzFoot).2 with hold | hfresh
      · exact hprefix z hz0 hold
      · omega
    · intro i hi hzFoot
      rcases (hmeta (names+1+i) hzFoot).2 with hold | hfresh
      · exact hnFoot (1+i) (by omega) (by simpa only [Nat.add_assoc] using hold)
      · omega
    · intro j hj
      exact hfamily' j (List.mem_toFinset.mpr (List.mem_cons_of_mem e hj))
    · intro j hj i hi
      rw [same_static base (by simp) j (hgraph j (List.mem_cons_of_mem e hj)).2 i hi]
      exact hbase j (List.mem_cons_of_mem e hj) i hi
    · intro j hj
      have hjm := (hgraph j (List.mem_cons_of_mem e hj)).2
      rw [fix_static up (by simp) j hjm,fix_static lo (by simp) j hjm]
      exact hrange j (List.mem_cons_of_mem e hj)
    · simp only [Nat.add_mul,Nat.one_mul] at hspace
      omega

end MinCostFlow.IPM.Machine
