module

public import MinCostFlow.IPM.Machine.ReportedEdge
public import MinCostFlow.IPM.Machine.CoefficientStatusOutput

/-!
# Results consumed by the reported-edge loop

Both branches return one status bit and obey the combined allocation and
frame bound. A final success bit forces the capacity check to have passed.
The subsequent coefficient writes lie beyond the scalar source prefix,
so they preserve the exact recovered flow coordinate. These facts let
the loop update its cache invariant without assuming hidden stability.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The final status is a bit whether capacity or slack checks reject. -/
theorem reportedEdge_status {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd e base lo up f c r a one mn mx E ld gd heap v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hout : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem') :
    mem' (v-1)≤1 := by
  simp only [reportedEdgeContract,List.getD_cons_zero,List.getD_cons_succ] at hout
  obtain ⟨queryEnd,queryMem,x',_,_,hbranch,_,_⟩ := hout
  split_ifs at hbranch
  · exact coefficientStatus_bit hbranch
  · rw [flagRecord_output hbranch]
    exact Nat.zero_le 1

/-- Every branch respects the combined workspace and old-memory frame:
only the DS footprint and the three caller table entries may change. -/
theorem reportedEdge_frame {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd e base lo up f c r a one mn mx E ld gd heap v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hout : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem') :
    heap≤v ∧ v≤heap+(minRatioMachineContract F A G m κ α rate allocation).space 1 s [b,e,heap] mem+
      16*F.limbs+Num.IPM.lengthSpace F.limbs F.fmt.precision E+
      Num.IPM.gradientSpace F.limbs F.fmt.precision E+4 ∧ ZeroFrom mem' v ∧
    (∀ z<heap,¬ R.foot b x z → (z<f ∨ f+F.limbs≤z) →
      (z<ld ∨ ld+F.limbs≤z) → (z<gd ∨ gd+F.limbs≤z) → mem' z=mem z) := by
  simp only [reportedEdgeContract,List.getD_cons_zero,List.getD_cons_succ] at hout
  obtain ⟨queryEnd,queryMem,x',hQ,_,hbranch,_,_⟩ := hout
  have hQframe := queryCoordinate_frame F A G m κ α rate allocation R hQ
  split_ifs at hbranch
  · have hframe := coefficientStatus_frame hbranch
    refine ⟨by omega,by omega,hframe.2.2.1,?_⟩
    intro z hz hfoot hf hl hg
    exact (hframe.2.2.2 z (by omega) hl hg).trans (hQframe.2.2.2 z hz hfoot hf)
  · have hv := hbranch.2
    change v=queryEnd+1 at hv
    have hframe := hbranch.1.2.2.1
    change ∀ z<queryEnd,mem' z=queryMem z at hframe
    refine ⟨by omega,by omega,hbranch.1.2.2.2.1,?_⟩
    intro z hz hfoot hf _ _
    exact (hframe z (by omega)).trans (hQframe.2.2.2 z hz hfoot hf)

/-- Final success implies a passed capacity guard and a complete guarded
coefficient call, while preserving the exact recovered flow coordinate
through all coefficient writes and the final status record. -/
theorem reportedEdge_accepted {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd e base lo up f c r a one mn mx E ld gd heap v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ} {baseValue : ℝ}
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
    (hbase : ScalarAt mem base F.fmt.limbBits F.limbs F.fmt.precision baseValue)
    (haccept : mem' (v-1)=1) :
    ∃ queryEnd queryMem,
      (queryCoordinateContract F A G m κ α rate allocation R b s x).post
        [b,e,base,lo,up,f,F.limbs,heap] mem queryEnd queryMem ∧
      queryMem (queryEnd-(1+4*F.limbs))=1 ∧
      (coefficientStatusContract w F.fmt.limbBits q K).post
        [m,c,r,lo,f,up,a,one,mn,mx,F.limbs,F.fmt.precision,E,ld,gd,queryEnd] queryMem v mem' ∧
      ScalarAt mem' f F.fmt.limbBits F.limbs F.fmt.precision (baseValue+A.query s e) := by
  simp only [reportedEdgeContract,List.getD_cons_zero,List.getD_cons_succ] at hout
  obtain ⟨e',base',lo',up',f',c',r',a',one',mn',mx',E',ld',gd',heap',heq,_,hs,hend,_,_,hbaseEnd,
    hsrcFoot,_,_,_,_,_,hldSource,hgdSource,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hfEnd := hs.2.2.2.2.2.2.2.2.2.2.1
  change f+F.limbs≤sourceEnd at hfEnd
  obtain ⟨queryEnd,queryMem,x',hQ,_,hbranch,_,_⟩ := hout
  have hQframe := queryCoordinate_frame F A G m κ α rate allocation R hQ
  have hcapacity : queryMem (queryEnd-(1+4*F.limbs))=1 := by
    by_contra hn
    simp only [hn,ite_false] at hbranch
    have hz := flagRecord_output hbranch
    change mem' (v-1)=0 at hz
    omega
  simp only [hcapacity,ite_true] at hbranch
  have hflow := queryCoordinate_output F A G m κ α rate allocation R hQ hbase
    (by omega) (fun i hi => hsrcFoot _ (by omega)) hcapacity
  have hframe := coefficientStatus_frame hbranch
  have hsame : ∀ i<F.limbs,mem' (f+i)=queryMem (f+i) := by
    intro i hi
    exact hframe.2.2.2 (f+i) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  refine ⟨queryEnd,queryMem,hQ,hcapacity,hbranch,?_,?_⟩
  · intro i hi
    rw [hsame i hi]
    exact hflow.1 i hi
  · unfold Num.fixVal
    rw [Num.intVal_congr hsame]
    exact hflow.2

/-- The combined workspace precondition bounds every returned endpoint,
including either rejection branch, by one machine word. -/
theorem reportedEdge_endpoint_word {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd e base lo up f c r a one mn mx E ld gd heap v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem') :
    v<2^w := by
  obtain ⟨e',base',lo',up',f',c',r',a',one',mn',mx',E',ld',gd',heap',heq,_,_,_,_,_,_,_,_,_,
    _,_,_,_,_,_,hspace⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  change heap+(minRatioMachineContract F A G m κ α rate allocation).space 1 s [b,e,heap] mem+
    16*F.limbs+Num.IPM.lengthSpace F.limbs F.fmt.precision E+
    Num.IPM.gradientSpace F.limbs F.fmt.precision E+4<2^w at hspace
  exact (reportedEdge_frame F A G m κ α rate allocation R hout).2.1.trans_lt hspace

/-- Inside the numeric source prefix, a reported-edge call can change
only its recovered flow block. Coefficient writes start beyond that
prefix and the old DS footprint avoids it. -/
theorem reportedEdge_source_frame {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd e base lo up f c r a one mn mx E ld gd heap v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem') :
    ∀ z<sourceEnd,(z<f ∨ f+F.limbs≤z) → mem' z=mem z := by
  obtain ⟨e',base',lo',up',f',c',r',a',one',mn',mx',E',ld',gd',heap',heq,_,_,hend,_,_,_,hfoot,
    _,_,_,_,_,hsld,hsgd,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  intro z hz hf
  exact (reportedEdge_frame F A G m κ α rate allocation R hout).2.2.2 z
    (hz.trans_le hend) (hfoot z hz) hf (Or.inl (hz.trans_le hsld)) (Or.inl (hz.trans_le hsgd))

/-- A caller block outside the old DS footprint and the three refreshed
entries retains its exact fixed-point value on either guard branch.
This preserves previously refreshed entries when Detect lists distinct
edge names, as well as every unreported entry. -/
theorem reportedEdge_preserves_block {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd e base lo up f c r a one mn mx E ld gd heap v p N precision : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hout : (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).post
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
    (hp : p+N≤heap) (hfoot : ∀ i<N,¬ R.foot b x (p+i))
    (hpf : p+N≤f ∨ f+F.limbs≤p)
    (hpl : p+N≤ld ∨ ld+F.limbs≤p) (hpg : p+N≤gd ∨ gd+F.limbs≤p)
    (hvalid : Num.Valid mem p F.fmt.limbBits N) :
    Num.Valid mem' p F.fmt.limbBits N ∧
      Num.fixVal mem' p F.fmt.limbBits N precision=
        Num.fixVal mem p F.fmt.limbBits N precision := by
  have hf := (reportedEdge_frame F A G m κ α rate allocation R hout).2.2.2
  have hsame : ∀ i<N,mem' (p+i)=mem (p+i) := by
    intro i hi
    apply hf (p+i) (by omega) (hfoot i hi)
    · rcases hpf with hh | hh <;> omega
    · rcases hpl with hh | hh <;> omega
    · rcases hpg with hh | hh <;> omega
  refine ⟨?_,?_⟩
  · intro i hi
    rw [hsame i hi]
    exact hvalid i hi
  · unfold Num.fixVal
    rw [Num.intVal_congr hsame]

end MinCostFlow.IPM.Machine
