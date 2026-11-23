module

public import MinCostFlow.IPM.Machine.DetectRefresh

/-!
# Deriving the Detect call and remaining refresh budget

The full explicit edge list covers the fixed graph. The original
specification's report inclusion therefore bounds Detect's cardinality
by that list's length. Together with the cached-table representation
and global allocation budget, this constructs the complete Detect/name
input. Its returned endpoint leaves room for all reported refresh work
and the final two-word pointer/status record.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The combined stage's full-edge input derives the actual Detect/name
call precondition and the report cardinality bound. -/
theorem detectRefresh_detect_pre {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd : ℕ}
    {s : A.State} {x : R.τ} {mem : ℕ → ℕ}
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem) :
    (detectNamesContract F A G m κ α rate allocation R b s x).pre [b,m,heap] mem ∧
      (A.detect s).1.card≤m := by
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,hcover,hsubset,hbudget⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,es,heq,
    hlen,hnd,hlist,_,hfit,hrep,hfoot,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hz,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hincluded : (A.detect s).1 ⊆ es.toFinset := by
    intro e he
    obtain ⟨i,hi,hread⟩ := hcover e (hsubset he)
    apply List.mem_toFinset.mpr
    exact List.mem_iff_getElem.mpr ⟨i,by omega,(hlist i (by omega)).symm.trans hread⟩
  have hcard : (A.detect s).1.card≤m := by
    have hh := Finset.card_le_card hincluded
    simpa only [List.toFinset_card_of_nodup hnd,hlen] using hh
  have hDpre : (minRatioMachineContract F A G m κ α rate allocation).pre 2 s [b,heap] mem :=
    ⟨hfit,b,heap,rfl⟩
  change heap+(minRatioMachineContract F A G m κ α rate allocation).space 2 s [b,heap] mem+
    2*(m+1)+m*reportedEdgesScratch F m b E allocation+4<2^w at hbudget
  refine ⟨⟨heap,rfl,?_,hcard,by omega⟩,hcard⟩
  exact ⟨m+1,heap,rfl,hrep,hDpre,hfoot,hz,by omega⟩

/-- The actual Detect/name output leaves room for its reported refresh
and final pointer/status record, from the combined stage's global budget. -/
theorem detectRefresh_remaining_space {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectNamesContract F A G m κ α rate allocation R b s x).post [b,m,heap] mem v mem') :
    v+(A.detect s).1.card*reportedEdgesScratch F m b E allocation+3<2^w := by
  have hcard := (detectRefresh_detect_pre F A G m κ α rate allocation R hpre).2
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,_,_,_,hbudget⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  change heap+(minRatioMachineContract F A G m κ α rate allocation).space 2 s [b,heap] mem+
    2*(m+1)+m*reportedEdgesScratch F m b E allocation+4<2^w at hbudget
  obtain ⟨reserved,detectMem,snapshotEnd,snapshotMem,mid,hD,hS,hv,hP,hF,hZ,hR,hM,hN,hNP,hLo,hHi,_⟩ := hout
  change v≤heap+(minRatioMachineContract F A G m κ α rate allocation).space 2 s [b,heap] mem+2*(m+1)+1 at hHi
  have hmul := Nat.mul_le_mul_right (reportedEdgesScratch F m b E allocation) hcard
  omega

end MinCostFlow.IPM.Machine
