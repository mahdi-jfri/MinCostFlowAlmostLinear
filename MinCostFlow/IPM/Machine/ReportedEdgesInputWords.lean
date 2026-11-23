module

public import MinCostFlow.IPM.Machine.ReportedEdgesContract

/-!
# Word bounds when the logical remaining list advances

The fixed table and numeric arguments retain their word bounds. The
list precondition bounds the changing name pointer, remaining count and
allocation endpoint. Reconstruct the whole word packet for each logical
suffix without assuming those changing bounds separately.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Extract the fixed table and numeric word bounds from the full
runtime argument packet. The three changing suffix fields are omitted. -/
theorem reportedEdges_fixed_words
    {w b names count base lo up f L heap c r a one mn mx P E ld gd m : ℕ}
    (hwords : ∀ z∈[b,names,count,base,lo,up,f,L,heap,c,r,a,one,mn,mx,P,E,ld,gd,m],z<2^w) :
    ∀ z∈[b,base,lo,up,f,L,c,r,a,one,mn,mx,P,E,ld,gd,m],z<2^w := by
  intro z hz
  apply hwords z
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz ⊢
  tauto

/-- Fixed argument words and the full list input condition imply the
entire argument word packet, including all three changing arguments. -/
theorem reportedEdges_input_words {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names count base lo up f heap c r a one mn mx E ld gd : ℕ}
    {s : A.State} {x : R.τ} {mem : ℕ → ℕ}
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hfixed : ∀ z∈[b,base,lo,up,f,F.limbs,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w) :
    ∀ z∈[b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m],z<2^w := by
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',es,heq,
    _,_,_,_,_,_,_,_,_,_,_,hnEnd,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hspace⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hheap : heap<2^w := by omega
  have hnames : names<2^w := by omega
  have hcount : count<2^w := by omega
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz
  all_goals subst z
  · exact hfixed _ (by simp)
  · exact hnames
  · exact hcount
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)
  · exact hheap
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)

end MinCostFlow.IPM.Machine
