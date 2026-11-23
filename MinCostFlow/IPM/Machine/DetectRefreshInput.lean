module

public import MinCostFlow.IPM.Machine.DetectNamesOutput
public import MinCostFlow.IPM.Machine.ReportedEdgesContract
import MinCostFlow.IPM.Machine.GuardedRefreshSourceFrame
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Feeding the stable Detect report to the refresh entry

The caller keeps source conditions for all graph names in its explicit
full-edge list. Detect and snapshot preserve those numeric tables. The
reported subset selects their source conditions, and its new state fits
the format. Its stable copied names avoid the exact concrete DS
footprint whose credit is retained. Construct every refresh input
condition from these facts and the reserved remaining workspace.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual Detect/name preparation output supplies the complete
reported-list refresh input. Set inclusion comes from Definition 4.5
(`minRatioDetect_subset`), and the retained concrete state's snapshot
separation comes from `detectNames_runs_with_potential`. -/
theorem reportedEdges_pre_after_detectNames {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd allNames base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {s : A.State} {x mid : R.τ} {mem mem' : ℕ → ℕ}
    (hfull : (reportedEdgesContract F A G m rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,allNames,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hcover : ∀ e∈G.E,∃ i<m,mem (allNames+i)=e)
    (hout : (detectNamesContract F A G m κ α rate allocation R b s x).post [b,m,heap] mem v mem')
    (hsubset : (A.detect s).1 ⊆ G.E)
    (hrep : R.rep b (A.detect s).2 mid mem')
    (hmeta : ∀ z,R.foot b mid z → z<v ∧ (R.foot b x z ∨ heap≤z))
    (hbefore : ∀ z,R.foot b mid z → z<mem' (v-1))
    (hspace : v+(A.detect s).1.card*reportedEdgesScratch F m b E allocation+1<2^w) :
    (reportedEdgesContract F A G m rate allocation R b (A.detect s).2 mid q K sourceEnd tableEnd).pre
      [b,mem' (v-1)+1,(A.detect s).1.card,base,lo,up,f,F.limbs,v,c,r,a,one,mn,mx,
        F.fmt.precision,E,ld,gd,m] mem' := by
  have houtput := detectNames_output F A G m κ α rate allocation R hout
  obtain ⟨names',count',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',all,heq,
    hlen,_,hlist,hgraph,_,_,_,hprefix,_,hsEnd,htEnd,hnEnd,hends,hshared,htables,hscalars,
    hsld,hsgd,hldEnd,hgdEnd,hdis,hfamily,hbase,hrange,_,hw,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hmem : ∀ z<tableEnd,mem' z=mem z := by
    obtain ⟨reserved,detectMem,snapshotEnd,snapshotMem,other,hD,hS,hv,hP,hF,hZ,hR,hM,hN,hNP,hLo,hHi,hframe⟩ := hout
    intro z hz
    exact hframe z (by change z<heap; omega) (hprefix z hz)
  have hsourceFrame : ∀ z<sourceEnd,mem' z=mem z := fun z hz => hmem z (hz.trans_le hsEnd)
  have hmember (e : ℕ) (he : e∈G.E) : e∈all := by
    obtain ⟨i,hi,hread⟩ := hcover e he
    exact List.mem_iff_getElem.mpr ⟨i,by omega,(hlist i (by omega)).symm.trans hread⟩
  have hzero : ZeroFrom mem' v := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hz,_⟩ := hout
    exact hz
  obtain ⟨es,hnd,hset,hheader,hnames⟩ := houtput.1
  have hnewLen : es.length=(A.detect s).1.card := by rw [← hset,List.toFinset_card_of_nodup hnd]
  have hnewMember (e : ℕ) (he : e∈es) : e∈G.E :=
    hsubset (by rw [← hset]; exact List.mem_toFinset.mpr he)
  refine ⟨mem' (v-1)+1,(A.detect s).1.card,base,lo,up,f,v,c,r,a,one,mn,mx,E,ld,gd,es,
    rfl,hnewLen,hnd,hnames,?_,houtput.2.2.2,hrep,?_,?_,?_,hsEnd,by omega,by omega,
    hends,hshared,htables,hscalars,hsld,hsgd,hldEnd,hgdEnd,hdis,?_,?_,?_,hzero,hw,hspace⟩
  · intro e he
    exact hgraph e (hmember e (hnewMember e he))
  · intro z hz
    exact (hmeta z hz).1
  · intro z hz hzFoot
    rcases (hmeta z hzFoot).2 with hold | hfresh
    · exact hprefix z hz hold
    · omega
  · intro i _ hzFoot
    have hh := hbefore (mem' (v-1)+1+i) hzFoot
    omega
  · intro e he
    exact scalarCoefficientSourceConditions_frozen (hfamily e (hmember e (hnewMember e he)))
      hsourceFrame le_rfl (hshared mn (by simp)) (hshared mx (by simp))
  · intro e he
    have hem := (hgraph e (hmember e (hnewMember e he))).2
    exact Num.IPM.valid_frozen hsourceFrame
      ((reported_entry_end base F.limbs e m hem).trans (hends base (by simp)))
      (hbase e (hmember e (hnewMember e he)))
  · intro e he
    have hem := (hgraph e (hmember e (hnewMember e he))).2
    rw [Num.IPM.fixVal_frozen hsourceFrame
      ((reported_entry_end up F.limbs e m hem).trans (hends up (by simp))),
      Num.IPM.fixVal_frozen hsourceFrame
      ((reported_entry_end lo F.limbs e m hem).trans (hends lo (by simp)))]
    exact hrange e (hmember e (hnewMember e he))

end MinCostFlow.IPM.Machine
