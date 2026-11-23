module

public import MinCostFlow.IPM.Machine.ReportedEdgesPost
public import MinCostFlow.IPM.Machine.FlagRecord
import MinCostFlow.IPM.Machine.ReportedCacheCongr
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Appending the list entry's final success record

The counter loop already establishes the cache postcondition. Its final
success bit is followed by one fresh status record for the outer entry.
That record preserves the concrete DS and every cached scalar block,
while consuming the one extra word reserved by the full list contract.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A final fresh success record preserves the full list postcondition,
using exactly its reserved extra word and the DS locality condition. -/
theorem reportedEdges_post_append {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State) (hlocal : R.Local)
    {b q K sourceEnd tableEnd names count base lo up f heap c r a one mn mx E ld gd v u : ℕ}
    {s : A.State} {x : R.τ} {mem mem₁ mem₂ : ℕ → ℕ}
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hcore : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem₁)
    (hspace : v≤heap+count*reportedEdgesScratch F m b E allocation)
    (haccept : mem₁ (v-1)=1)
    (hflag : (flagRecordContract w).post [1,v] mem₁ u mem₂) :
    (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem u mem₂ := by
  have hu := hflag.2
  change u=v+1 at hu
  have hflagFrame := hflag.1.2.2.1
  change ∀ z<v,mem₂ z=mem₁ z at hflagFrame
  have hflagZero := hflag.1.2.2.2.1
  change ZeroFrom mem₂ u at hflagZero
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',es,heq,
    hlen,_,hlist,hgraph,_,_,_,_,_,hsEnd,htEnd,hnEnd,hends,hshared,_,_,_,_,hldEnd,hgdEnd,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  simp only [reportedEdgesContract,List.getD_cons_zero,List.getD_cons_succ] at hcore
  obtain ⟨final,hrep,hmeta,hlo,_,_,_,hframe,hcache,hSafe⟩ := hcore
  have hstate := flagRecord_preserves_state R hlocal hflag hrep (fun z hz => (hmeta z hz).1)
  refine reportedEdges_post_of_list F A G m rate allocation R es hlist hlen hstate.1 ?_
    (by omega) (by omega) hflagZero (by rw [flagRecord_output hflag]) ?_ ?_ ⟨(fun _ => (hSafe es hlist hlen).mp haccept),fun _ => flagRecord_output hflag⟩
  · intro z hz
    exact ⟨by have hh := (hmeta z hz).1; omega,(hmeta z hz).2⟩
  · intro z hz hnot hsep
    exact (hflagFrame z (hz.trans_le hlo)).trans (hframe es hlist hlen z hz hnot hsep)
  · intro _ e he
    have hem := (hgraph e he).2
    apply reportedCachePost_congr F A s (hpost:=hcache haccept es hlist hlen e he)
    intro p hp i hi
    have hendsBlock : p+F.limbs≤tableEnd := by
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
    exact hflagFrame (p+i) (by omega)

/-- An initially empty list obtains its complete output condition from
one fresh success record, without reading an earlier status word. -/
theorem reportedEdges_post_empty {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State) (hlocal : R.Local)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,0,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hflag : (flagRecordContract w).post [1,heap] mem v mem') :
    (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,0,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem' := by
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',es,heq,
    _,_,_,_,_,hrep,hfoot,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hstate := flagRecord_preserves_state R hlocal hflag hrep hfoot
  have hv := hflag.2
  change v=heap+1 at hv
  have hframe := hflag.1.2.2.1
  change ∀ z<heap,mem' z=mem z at hframe
  refine reportedEdges_post_of_list F A G m rate allocation R [] (by intro i hi; simp at hi)
    rfl hstate.1 (fun z hz => ⟨by have hh := hfoot z hz; omega,Or.inl hz⟩)
    (by omega) ?_ hflag.1.2.2.2.1 (by rw [flagRecord_output hflag]) ?_ ?_ ⟨fun _ e he => (List.not_mem_nil he).elim,fun _ => flagRecord_output hflag⟩
  · simpa only [Nat.zero_mul,Nat.add_zero] using hv.le
  · intro z hz _ _
    exact hframe z hz
  · intro _ e he
    exact False.elim (List.not_mem_nil he)

end MinCostFlow.IPM.Machine
