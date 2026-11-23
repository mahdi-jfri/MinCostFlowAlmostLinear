module

public import MinCostFlow.IPM.Machine.ReportedEdgesContract
public import MinCostFlow.IPM.Machine.ReportedCacheCongr
public import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# A tail refresh preserves an unlisted cached coordinate

The list contract frames exactly its listed entries. A distinct earlier
name therefore keeps its own flow and coefficient blocks. Whole-table
separation also keeps its base and numeric source blocks. Apply the
complete cache congruence lemma. This is the postcondition composition
needed when processing a list by its first name and remaining tail.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The full list frame preserves the complete cache postcondition of
any valid edge name that does not occur in the refreshed list. -/
theorem reportedEdges_unlisted_cache {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names count base lo up f heap c r a one mn mx E ld gd e v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ} (es : List ℕ)
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
    (hlist : ListAt mem names es) (hlen : es.length=count) (he : e<m) (hne : e∉es)
    (hcache : reportedCachePost F A s m q base lo up f c r a ld gd e mem) :
    reportedCachePost F A s m q base lo up f c r a ld gd e mem' := by
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',actual,heq,
    halen,_,halist,hgraph,_,_,_,hprefix,_,hsEnd,htEnd,hnEnd,hends,hshared,
    htables,hscalars,hsld,hsgd,hldEnd,hgdEnd,hdis,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hal : actual=es := List.ext_getElem (halen.trans hlen.symm)
    (fun i hi hj => (halist i hi).symm.trans (hlist i hj))
  subst actual
  simp only [reportedEdgesContract,List.getD_cons_zero,List.getD_cons_succ] at hout
  obtain ⟨_,_,_,_,_,_,_,hframe,_⟩ := hout
  have block_same (p : ℕ) (hend : p+F.limbs≤tableEnd)
      (hseparate : ∀ j∈es,(p+F.limbs≤f+j*F.limbs ∨ f+j*F.limbs+F.limbs≤p) ∧
        (p+F.limbs≤ld+j*F.limbs ∨ ld+j*F.limbs+F.limbs≤p) ∧
        (p+F.limbs≤gd+j*F.limbs ∨ gd+j*F.limbs+F.limbs≤p)) :
      ∀ i<F.limbs,mem' (p+i)=mem (p+i) := by
    intro i hi
    apply hframe es hlist hlen (p+i) (by omega) (hprefix _ (by omega))
    intro j hj
    obtain ⟨hf,hl,hg⟩ := hseparate j hj
    refine ⟨?_,?_,?_⟩
    · rcases hf with hh | hh <;> omega
    · rcases hl with hh | hh <;> omega
    · rcases hg with hh | hh <;> omega
  have source_same (p : ℕ) (hend : p+F.limbs≤sourceEnd)
      (hseparate : ∀ j∈es,p+F.limbs≤f+j*F.limbs ∨ f+j*F.limbs+F.limbs≤p) :
      ∀ i<F.limbs,mem' (p+i)=mem (p+i) := by
    apply block_same p (hend.trans hsEnd)
    intro j hj
    exact ⟨hseparate j hj,Or.inl (by omega),Or.inl (by omega)⟩
  have table_same (p : ℕ) (hp : p∈[base,c,lo,up]) :
      ∀ i<F.limbs,mem' (p+e*F.limbs+i)=mem (p+e*F.limbs+i) := by
    apply source_same (p+e*F.limbs) ((reported_entry_end p F.limbs e m he).trans
      (hends p (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hp ⊢; tauto)))
    intro j hj
    exact reported_entries_separated p f F.limbs e j m he (hgraph j hj).2 (htables p hp)
  have scalar_same (p : ℕ) (hp : p∈[r,a]) :
      ∀ i<F.limbs,mem' (p+i)=mem (p+i) := by
    apply source_same p (hshared p (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp ⊢; tauto))
    intro j hj
    exact reported_scalar_separated p f F.limbs j m (hgraph j hj).2
      (hscalars p (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hp ⊢; tauto))
  have hneq (j : ℕ) (hj : j∈es) : e≠j := fun hh => hne (hh ▸ hj)
  apply reportedCachePost_congr F A s (hpost:=hcache)
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp
  all_goals subst p
  · exact table_same base (by simp)
  · exact table_same c (by simp)
  · exact scalar_same r (by simp)
  · exact table_same lo (by simp)
  · apply source_same (f+e*F.limbs) ((reported_entry_end f F.limbs e m he).trans (hends f (by simp)))
    intro j hj
    exact reported_blocks_disjoint f F.limbs e j (hneq j hj)
  · exact table_same up (by simp)
  · exact scalar_same a (by simp)
  · apply block_same (ld+e*F.limbs) ((reported_entry_end ld F.limbs e m he).trans hldEnd)
    intro j hj
    have hfEnd := (reported_entry_end f F.limbs j m (hgraph j hj).2).trans (hends f (by simp))
    exact ⟨Or.inr (by omega),reported_blocks_disjoint ld F.limbs e j (hneq j hj),
      reported_entries_separated ld gd F.limbs e j m he (hgraph j hj).2 hdis⟩
  · apply block_same (gd+e*F.limbs) ((reported_entry_end gd F.limbs e m he).trans hgdEnd)
    intro j hj
    have hfEnd := (reported_entry_end f F.limbs j m (hgraph j hj).2).trans (hends f (by simp))
    exact ⟨Or.inr (by omega),
      reported_entries_separated gd ld F.limbs e j m he (hgraph j hj).2 (hdis.elim Or.inr Or.inl),
      reported_blocks_disjoint gd F.limbs e j (hneq j hj)⟩

end MinCostFlow.IPM.Machine
