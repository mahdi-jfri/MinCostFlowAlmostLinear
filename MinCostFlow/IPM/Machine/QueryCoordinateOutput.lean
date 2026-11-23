module

public import MinCostFlow.IPM.Machine.QueryCoordinateProgram

/-!
# Exact values and guards after coordinate recovery

The Query answer is the parameter's accumulated flow. The original base
and capacities survive the call outside its footprint. Thus acceptance
writes exactly base plus accumulated flow. The acceptance bit is readable
at a fixed offset from the returned heap, so the reported-edge loop can
stop at the first rejected coordinate without another data-structure call.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

private theorem scalar_outside_footprint {σ : Type} (R : DSRep σ)
    {b source h L P heap : ℕ} {x : R.τ} {mem mem' : ℕ → ℕ} {value : ℝ}
    (hframe : ∀ z<heap,¬ R.foot b x z → mem' z=mem z)
    (hend : source+L≤heap) (hfoot : ∀ i<L,¬ R.foot b x (source+i))
    (hv : ScalarAt mem source h L P value) : ScalarAt mem' source h L P value := by
  have hsame : ∀ i<L,mem' (source+i)=mem (source+i) := by
    intro i hi
    exact hframe _ (by omega) (hfoot i hi)
  refine ⟨?_,?_⟩
  · intro i hi
    rw [hsame i hi]
    exact hv.1 i hi
  · unfold Num.fixVal
    rw [Num.intVal_congr hsame]
    exact hv.2

/-- The accepted stored coordinate is exactly its original base plus the
parameter's accumulated flow, at the original fixed-point precision. -/
theorem queryCoordinate_output {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b e base lo up dst heap v : ℕ} {s : A.State} {x : R.τ}
    {mem mem' : ℕ → ℕ} {baseValue : ℝ}
    (hout : (queryCoordinateContract F A G m κ α rate allocation R b s x).post
      [b,e,base,lo,up,dst,F.limbs,heap] mem v mem')
    (hbase : ScalarAt mem base F.fmt.limbBits F.limbs F.fmt.precision baseValue)
    (hbaseEnd : base+F.limbs≤heap) (hbaseFoot : ∀ i<F.limbs,¬ R.foot b x (base+i))
    (haccept : mem' (v-(1+4*F.limbs))=1) :
    ScalarAt mem' dst F.fmt.limbBits F.limbs F.fmt.precision (baseValue+A.query s e) := by
  obtain ⟨pad,queryMem,x',hQ,hN,_,_,_⟩ := hout
  have hanswer := (minRatioQuery_scalar_output F A G m κ α rate allocation R hQ).1
  obtain ⟨_,_,_,_,_,_,_,_,_,hframe,_⟩ := hQ
  change ∀ z<heap,¬ R.foot b x z → queryMem z=mem z at hframe
  have hbaseQ := scalar_outside_footprint R hframe hbaseEnd hbaseFoot hbase
  have hv := hN.1
  change v=pad+(1+10*F.limbs) at hv
  have hslot : v-(1+4*F.limbs)=pad+6*F.limbs := by omega
  rw [hslot] at haccept
  exact storeCoordinate_output hN hbaseQ hanswer haccept

/-- The actual acceptance bit tests the real capacity interval of the
true base-plus-Query sum, including sums outside the ordinary signed range. -/
theorem queryCoordinate_acceptance {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b e base lo up dst heap v : ℕ} {s : A.State} {x : R.τ}
    {mem mem' : ℕ → ℕ} {baseValue lower upper : ℝ}
    (hout : (queryCoordinateContract F A G m κ α rate allocation R b s x).post
      [b,e,base,lo,up,dst,F.limbs,heap] mem v mem')
    (hbase : ScalarAt mem base F.fmt.limbBits F.limbs F.fmt.precision baseValue)
    (hlo : ScalarAt mem lo F.fmt.limbBits F.limbs F.fmt.precision lower)
    (hup : ScalarAt mem up F.fmt.limbBits F.limbs F.fmt.precision upper)
    (hbaseEnd : base+F.limbs≤heap) (hloEnd : lo+F.limbs≤heap) (hupEnd : up+F.limbs≤heap)
    (hbaseFoot : ∀ i<F.limbs,¬ R.foot b x (base+i))
    (hloFoot : ∀ i<F.limbs,¬ R.foot b x (lo+i))
    (hupFoot : ∀ i<F.limbs,¬ R.foot b x (up+i)) :
    mem' (v-(1+4*F.limbs))=
      if lower<baseValue+A.query s e ∧ baseValue+A.query s e<upper then 1 else 0 := by
  obtain ⟨pad,queryMem,x',hQ,hN,_,_,_⟩ := hout
  have hanswer := (minRatioQuery_scalar_output F A G m κ α rate allocation R hQ).1
  obtain ⟨_,_,_,_,_,_,_,_,_,hframe,_⟩ := hQ
  change ∀ z<heap,¬ R.foot b x z → queryMem z=mem z at hframe
  have hbaseQ := scalar_outside_footprint R hframe hbaseEnd hbaseFoot hbase
  have hloQ := scalar_outside_footprint R hframe hloEnd hloFoot hlo
  have hupQ := scalar_outside_footprint R hframe hupEnd hupFoot hup
  have hv := hN.1
  change v=pad+(1+10*F.limbs) at hv
  have hslot : v-(1+4*F.limbs)=pad+6*F.limbs := by omega
  rw [hslot]
  exact storeCoordinate_flag_output hN hbaseQ hanswer hloQ hupQ

/-- The capacity status is always a bit, without an approximation or
feasibility premise on the queried candidate. -/
theorem queryCoordinate_status {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b e base lo up dst heap v : ℕ} {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hout : (queryCoordinateContract F A G m κ α rate allocation R b s x).post
      [b,e,base,lo,up,dst,F.limbs,heap] mem v mem') :
    mem' (v-(1+4*F.limbs))≤1 := by
  obtain ⟨pad,queryMem,x',_,hN,_,_,_⟩ := hout
  have hv := hN.1
  change v=pad+(1+10*F.limbs) at hv
  have hslot : v-(1+4*F.limbs)=pad+6*F.limbs := by omega
  rw [hslot]
  have hflag := hN.2.2.2.1
  change mem' (pad+6*F.limbs)=(if _ then 1 else 0) at hflag
  split_ifs at hflag <;> omega

/-- Query and guarded writing preserve every old cell outside both the
old DS footprint and the caller's destination, and leave fresh memory. -/
theorem queryCoordinate_frame {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b e base lo up dst heap v : ℕ} {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hout : (queryCoordinateContract F A G m κ α rate allocation R b s x).post
      [b,e,base,lo,up,dst,F.limbs,heap] mem v mem') :
    heap≤v ∧ v≤heap+(minRatioMachineContract F A G m κ α rate allocation).space 1 s [b,e,heap] mem+
      F.limbs+(1+10*F.limbs) ∧ ZeroFrom mem' v ∧
    (∀ z<heap,¬ R.foot b x z → (z<dst ∨ dst+F.limbs≤z) → mem' z=mem z) := by
  obtain ⟨pad,queryMem,x',hQ,hN,_,_,_⟩ := hout
  obtain ⟨queryEnd,_,_,hpad,hlo,hhi,_,_,_,hQframe,_⟩ := hQ
  change pad=queryEnd+F.limbs at hpad
  change heap≤queryEnd at hlo
  change queryEnd≤heap+(minRatioMachineContract F A G m κ α rate allocation).space 1 s [b,e,heap] mem at hhi
  change ∀ z<heap,¬ R.foot b x z → queryMem z=mem z at hQframe
  have hv := hN.1
  change v=pad+(1+10*F.limbs) at hv
  have hNframe := hN.2.2.1
  change ∀ z<pad,(z<dst ∨ dst+F.limbs≤z) → mem' z=queryMem z at hNframe
  refine ⟨by omega,by omega,hN.2.1,?_⟩
  intro z hz hfoot hdst
  exact (hNframe z (by omega) hdst).trans (hQframe z hz hfoot)

end MinCostFlow.IPM.Machine
