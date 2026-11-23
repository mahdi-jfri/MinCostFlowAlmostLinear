module

public import MinCostFlow.IPM.Machine.ReportedEdgesPost
public import MinCostFlow.IPM.Machine.ReportedEdgeOutput
import MinCostFlow.IPM.Machine.ReportedEdgeSafety
import MinCostFlow.IPM.Machine.ReportedEdgesMemberInput

/-!
# Terminal postconditions of the reported-list loop

When the remaining list is empty, its inputs and the current success
bit already give the list postcondition. When the first edge rejects,
the actual checked call gives the whole list's failure postcondition.
Both cases retain the concrete representation and the fine memory frame.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- An empty remaining list with a current success bit has the identity
list postcondition, without modifying any memory or concrete DS state. -/
theorem reportedEdges_post_nil {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd : ℕ}
    {s : A.State} {x : R.τ} {mem : ℕ → ℕ}
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,0,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hbit : mem (heap-1)=1) :
    (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,0,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem heap mem := by
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',es,heq,
    _,_,_,_,_,hrep,hfoot,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hz,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  refine reportedEdges_post_of_list F A G m rate allocation R [] (by intro i hi; simp at hi)
    rfl hrep (fun z hz0 => ⟨hfoot z hz0,Or.inl hz0⟩) le_rfl ?_ hz ?_ ?_ ?_ ⟨fun _ e he => (List.not_mem_nil he).elim,fun _ => hbit⟩
  · simp only [Nat.zero_mul,Nat.add_zero]
    omega
  · rw [hbit]
  · intro z _ _ _
    rfl
  · intro _ e he
    exact False.elim (List.not_mem_nil he)

/-- A rejected first name already gives the complete list failure
postcondition. No subsequent name needs to be queried or refreshed. -/
theorem reportedEdges_post_reject {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names k base lo up f heap c r a one mn mx E ld gd e v : ℕ}
    {s : A.State} {x mid : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,k+1,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hread : mem names=e)
    (hfirst : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
      [b,e,base+e*F.limbs,lo+e*F.limbs,up+e*F.limbs,f+e*F.limbs,F.limbs,heap,
        c+e*F.limbs,r,a,one,mn,mx,F.fmt.precision,E,ld+e*F.limbs,gd+e*F.limbs,m] mem v mem')
    (hrep : R.rep b s mid mem')
    (hmeta : ∀ z,R.foot b mid z → z<v ∧ (R.foot b x z ∨ heap≤z))
    (hreject : mem' (v-1)=0) :
    (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,k+1,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem' := by
  have hsingle := reportedEdges_member_pre F A G m κ α rate allocation R hpre
    (i:=0) (by omega) (by simpa only [Nat.add_zero] using hread)
  have hframe := reportedEdge_frame F A G m κ α rate allocation R hfirst
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',es,heq,
    hlen,_,hlist,hgraph,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hspace⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have heList : e∈es := List.mem_iff_getElem.mpr
    ⟨0,by omega,(hlist 0 (by omega)).symm.trans (by simpa only [Nat.add_zero] using hread)⟩
  have hem := (hgraph e heList).2
  have hheapW : heap<2^w := by omega
  have halloc := query_allocation_le_bound (b:=b) allocation hem hheapW
  have hstep : v≤heap+reportedEdgesScratch F m b E allocation := by
    have hu := hframe.2.1
    change v≤heap+allocation 1 [b,e,heap]+16*F.limbs+
      Num.IPM.lengthSpace F.limbs F.fmt.precision E+
      Num.IPM.gradientSpace F.limbs F.fmt.precision E+4 at hu
    unfold reportedEdgesScratch
    omega
  have hmul : reportedEdgesScratch F m b E allocation≤(k+1)*reportedEdgesScratch F m b E allocation := by
    have hh := Nat.mul_le_mul_right (reportedEdgesScratch F m b E allocation) (Nat.succ_le_succ (Nat.zero_le k))
    simpa only [Nat.one_mul] using hh
  refine reportedEdges_post_of_list F A G m rate allocation R es hlist hlen hrep hmeta
    hframe.1 (by omega) hframe.2.2.1 (by rw [hreject]; exact Nat.zero_le 1) ?_ ?_ ?_
  · intro z hz hnot hsep
    have heSep := hsep e heList
    exact hframe.2.2.2 z hz hnot heSep.1 heSep.2.1 heSep.2.2
  · intro hb
    rw [hreject] at hb
    contradiction
  · refine ⟨fun hb => (by omega : False).elim,?_⟩
    intro safe
    exact reportedEdge_accepts_safe F A G m κ α rate allocation R hsingle hfirst (safe e heList)

end MinCostFlow.IPM.Machine
