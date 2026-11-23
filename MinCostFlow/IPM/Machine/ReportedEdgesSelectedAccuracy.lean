module

public import MinCostFlow.IPM.Machine.ReportedEdgesMemberInput
public import MinCostFlow.IPM.Machine.ReportedEdgeAccuracy
import MinCostFlow.IPM.Machine.ReportedEdgeInside

/-!
# The selected name satisfies the list's cache postcondition

A successful checked refresh recovers the selected coordinate relative
to its initial base flow. The list layout keeps the base-flow table
separate from the changed flow block, so that base is still stored in
the final memory. Translate the scalar coefficient bounds to their
dense-table indices to obtain exactly the list output condition.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A successful selected call establishes the full cache postcondition
for its name, derived entirely from the list input and actual call. -/
theorem reportedEdges_selected_accuracy {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names count base lo up f heap c r a one mn mx E ld gd i e v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hi : i<count) (hread : mem (names+i)=e)
    (hout : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
      [b,e,base+e*F.limbs,lo+e*F.limbs,up+e*F.limbs,f+e*F.limbs,F.limbs,heap,
        c+e*F.limbs,r,a,one,mn,mx,F.fmt.precision,E,ld+e*F.limbs,gd+e*F.limbs,m] mem v mem')
    (haccept : mem' (v-1)=1) :
    reportedCachePost F A s m q base lo up f c r a ld gd e mem' := by
  have hselected := reportedEdges_member_pre F A G m κ α rate allocation R hpre hi hread
  have hframe := reportedEdge_source_frame F A G m κ α rate allocation R hselected hout
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',es,heq,
    hlen,_,hlist,hgraph,_,_,_,_,_,_,_,_,hends,_,htables,_,_,_,_,_,_,_,hbase,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have heList : e∈es := List.mem_iff_getElem.mpr
    ⟨i,by omega,(hlist i (by omega)).symm.trans hread⟩
  have hem := (hgraph e heList).2
  have hacc := reportedEdge_accuracy F A G m κ α rate allocation R hselected hout
    ⟨hbase e heList,rfl⟩ haccept
  have hbaseEnd := (reported_entry_end base F.limbs e m hem).trans (hends base (by simp))
  have hbaseDis := reported_entries_separated base f F.limbs e e m hem hem (htables base (by simp))
  have hbaseSame : ∀ j<F.limbs,mem' (base+e*F.limbs+j)=mem (base+e*F.limbs+j) := by
    intro j hj
    apply hframe _ (by omega)
    rcases hbaseDis with hh | hh <;> omega
  have hbaseFix : Num.fixVal mem' (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := by
    unfold Num.fixVal
    rw [Num.intVal_congr hbaseSame]
  have hin := reportedEdge_inside F A G m κ α rate allocation R hselected hout
    ⟨hbase e heList,rfl⟩ haccept
  refine ⟨hacc.1.1,?_,hacc.2.1,?_,hacc.2.2.2.1,?_,hin⟩
  · rw [hbaseFix]
    exact hacc.1.2
  · simpa only [Num.IPM.arrayLength,Nat.zero_mul,Nat.add_zero] using hacc.2.2.1
  · simpa only [Num.IPM.arrayLength,Num.IPM.arrayGradient,Nat.zero_mul,Nat.add_zero] using hacc.2.2.2.2

end MinCostFlow.IPM.Machine
