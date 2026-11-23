module

public import MinCostFlow.IPM.Machine.ReportedEdgesContract
public import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# A selected name has the complete per-edge input conditions

Use the actual name at a valid list index. The list input conditions
give its graph membership and numeric sources. Whole-table separation
implies separation of the selected entries, and the remaining allocation
budget covers its Query and numeric work. Thus no per-edge call
precondition is assumed independently of the list layout.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Every name read from the input list has the full checked per-edge
precondition, derived from the list contract and the actual memory read. -/
theorem reportedEdges_member_pre {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names count base lo up f heap c r a one mn mx E ld gd i e : ℕ}
    {s : A.State} {x : R.τ} {mem : ℕ → ℕ}
    (hpre : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,count,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hi : i<count) (hread : mem (names+i)=e) :
    (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base+e*F.limbs,lo+e*F.limbs,up+e*F.limbs,f+e*F.limbs,F.limbs,heap,
        c+e*F.limbs,r,a,one,mn,mx,F.fmt.precision,E,ld+e*F.limbs,gd+e*F.limbs,m] mem := by
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',es,heq,
    hlen,_,hlist,hgraph,hfit,hrep,hfoot,hprefix,_,hsEnd,htEnd,hnEnd,hends,hshared,
    htables,hscalars,hsld,hsgd,hldEnd,hgdEnd,hdis,hfamily,hbase,hrange,hz,_,hspace⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have heList : e∈es := by
    apply List.mem_iff_getElem.mpr
    exact ⟨i,by omega,(hlist i (by omega)).symm.trans hread⟩
  obtain ⟨heG,hem⟩ := hgraph e heList
  have hHeapW : heap<2^w := by omega
  have halloc := query_allocation_le_bound (b:=b) allocation hem hHeapW
  have hmul : reportedEdgesScratch F m b E allocation≤count*reportedEdgesScratch F m b E allocation := by
    have hh := Nat.mul_le_mul_right (reportedEdgesScratch F m b E allocation) (show 1≤count by omega)
    simpa only [Nat.one_mul] using hh
  have hsingle : heap+(minRatioMachineContract F A G m κ α rate allocation).space 1 s [b,e,heap] mem+
      16*F.limbs+Num.IPM.lengthSpace F.limbs F.fmt.precision E+
      Num.IPM.gradientSpace F.limbs F.fmt.precision E+4<2^w := by
    change heap+allocation 1 [b,e,heap]+16*F.limbs+
      Num.IPM.lengthSpace F.limbs F.fmt.precision E+
      Num.IPM.gradientSpace F.limbs F.fmt.precision E+4<2^w
    unfold reportedEdgesScratch at hmul hspace
    omega
  have hbaseEnd := (reported_entry_end base F.limbs e m hem).trans (hends base (by simp))
  have hldEntry := (reported_entry_end ld F.limbs e m hem).trans hldEnd
  have hgdEntry := (reported_entry_end gd F.limbs e m hem).trans hgdEnd
  refine reportedEdge_pre_of_sources F A G m κ α rate allocation R
    (hfamily e heList) hfit heG hem hrep hfoot hz (by omega)
    (hshared mn (by simp)) (hshared mx (by simp)) hbaseEnd (hbase e heList)
    (fun z hz0 => hprefix z (hz0.trans_le hsEnd)) ?_ (hrange e heList)
    (by omega) (by omega) (reported_entries_separated ld gd F.limbs e e m hem hem hdis)
    (by omega) (by omega) ?_ hsingle
  · intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with hp | hp | hp | hp | hp | hp | hp | hp
    all_goals subst p
    · exact reported_entries_separated c f F.limbs e e m hem hem (htables c (by simp))
    · exact reported_scalar_separated r f F.limbs e m hem (hscalars r (by simp))
    · exact reported_entries_separated lo f F.limbs e e m hem hem (htables lo (by simp))
    · exact reported_entries_separated up f F.limbs e e m hem hem (htables up (by simp))
    · exact reported_scalar_separated a f F.limbs e m hem (hscalars a (by simp))
    · exact reported_scalar_separated one f F.limbs e m hem (hscalars one (by simp))
    · exact reported_scalar_separated mn f F.limbs e m hem (hscalars mn (by simp))
    · exact reported_scalar_separated mx f F.limbs e m hem (hscalars mx (by simp))
  · intro z hz0
    have habove : tableEnd≤z := Nat.le_of_not_gt (fun hh => hprefix z hh hz0)
    exact ⟨Or.inr (hldEntry.trans habove),Or.inr (hgdEntry.trans habove)⟩

end MinCostFlow.IPM.Machine
