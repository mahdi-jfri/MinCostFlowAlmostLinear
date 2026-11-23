module

public import MinCostFlow.IPM.Machine.ReportedEdgesContract
public import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Word bounds for a selected reported-edge call

The list's fixed arguments are words. Its table extents and allocation
budget bound every selected pointer and the name-list read address.
Together with graph membership this gives the complete callee word
packet and the intermediate product used to form table offsets.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The full list input implies all word bounds needed to read one name,
compute its offset and evaluate its actual reported-edge call arguments. -/
theorem reportedEdges_member_words {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names count base lo up f heap c r a one mn mx E ld gd i e : ℕ}
    {s : A.State} {x : R.τ} {mem : ℕ → ℕ}
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hwords : ∀ z∈[b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w)
    (hi : i<count) (hread : mem (names+i)=e) :
    names+i<2^w ∧ e*F.limbs<2^w ∧
    ∀ z∈[b,e,base+e*F.limbs,lo+e*F.limbs,up+e*F.limbs,f+e*F.limbs,F.limbs,heap,
      c+e*F.limbs,r,a,one,mn,mx,F.fmt.precision,E,ld+e*F.limbs,gd+e*F.limbs,m],z<2^w := by
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',es,heq,
    hlen,_,hlist,hgraph,_,_,_,_,_,hsEnd,htEnd,hnEnd,hends,_,_,_,_,_,hldEnd,hgdEnd,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have heList : e∈es := List.mem_iff_getElem.mpr
    ⟨i,by omega,(hlist i (by omega)).symm.trans hread⟩
  have hem := (hgraph e heList).2
  have hheap : heap<2^w := hwords _ (by simp)
  have hm : m<2^w := hwords _ (by simp)
  have hew : e<2^w := hem.trans hm
  have hsource : sourceEnd≤heap := by omega
  have htable : tableEnd≤heap := by omega
  have sourceWord (p : ℕ) (hp : p∈[base,c,lo,f,up]) :
      p+e*F.limbs<2^w ∧ e*F.limbs<2^w ∧ p+e*F.limbs+F.limbs≤heap :=
    reported_entry_words w p F.limbs e m heap hem ((hends p hp).trans hsource) hheap
  have hl := reported_entry_words w ld F.limbs e m heap hem (hldEnd.trans htable) hheap
  have hg := reported_entry_words w gd F.limbs e m heap hem (hgdEnd.trans htable) hheap
  refine ⟨by omega,(sourceWord base (by simp)).2.1,?_⟩
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz
  all_goals subst z
  · exact hwords _ (by simp)
  · exact hew
  · exact (sourceWord base (by simp)).1
  · exact (sourceWord lo (by simp)).1
  · exact (sourceWord up (by simp)).1
  · exact (sourceWord f (by simp)).1
  · exact hwords _ (by simp)
  · exact hwords _ (by simp)
  · exact (sourceWord c (by simp)).1
  · exact hwords _ (by simp)
  · exact hwords _ (by simp)
  · exact hwords _ (by simp)
  · exact hwords _ (by simp)
  · exact hwords _ (by simp)
  · exact hwords _ (by simp)
  · exact hwords _ (by simp)
  · exact hl.1
  · exact hg.1
  · exact hwords _ (by simp)

end MinCostFlow.IPM.Machine
