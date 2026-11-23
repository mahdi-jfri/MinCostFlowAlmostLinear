module

public import MinCostFlow.IPM.Machine.MinRatioQueryProgram
public import MinCostFlow.IPM.Machine.MinRatioContract
public import MinCostFlow.IPM.Machine.StoreCoordinate

/-!
# Supplying a Query answer to guarded coordinate recovery

The Query wrapper reserves the complete fixed-point answer and preserves
caller blocks outside the data structure's footprint. Consequently the
base, capacities and cumulative increment meet the exact wide-addition
and guarded-write preconditions without a feasibility assumption on the
candidate sum. Lower-target tests can reject that sum safely.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The wrapped Query returns the parameter's exact represented answer,
and that full block ends below the caller's new heap. -/
theorem minRatioQuery_scalar_output {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep A.State) {b e heap v : ℕ} {s : A.State} {x : R.τ}
    {mem mem' : ℕ → ℕ}
    (hout : (minRatioQueryContract w R
      (minRatioMachineContract F A G m κ α rate allocation) b s x).post
      [b,e,F.limbs,heap] mem v mem') :
    ScalarAt mem' heap F.fmt.limbBits F.limbs F.fmt.precision (A.query s e) ∧
      heap+F.limbs≤v := by
  obtain ⟨queryEnd,s',x',hv,hlo,_,_,_,hq,_,_⟩ := hout
  change s'=s ∧ ScalarAt mem' heap F.fmt.limbBits F.limbs F.fmt.precision (A.query s e) at hq
  change v=queryEnd+F.limbs at hv
  change heap≤queryEnd at hlo
  exact ⟨hq.2,by omega⟩

/-- Exact Query output and preserved source blocks supply the complete
precondition of the guarded coordinate writer. No bound on the candidate
sum and no feasibility of the next flow is assumed here. -/
theorem storeCoordinate_pre_after_query {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep A.State) {b e heap v base lo up dst : ℕ} {s : A.State} {x : R.τ}
    {mem mem' : ℕ → ℕ}
    (hout : (minRatioQueryContract w R
      (minRatioMachineContract F A G m κ α rate allocation) b s x).post
      [b,e,F.limbs,heap] mem v mem')
    (hbase : Num.Valid mem base F.fmt.limbBits F.limbs)
    (hlo : Num.Valid mem lo F.fmt.limbBits F.limbs)
    (hup : Num.Valid mem up F.fmt.limbBits F.limbs)
    (hbaseEnd : base+F.limbs≤heap) (hloEnd : lo+F.limbs≤heap)
    (hupEnd : up+F.limbs≤heap) (hdstEnd : dst+F.limbs≤heap)
    (hbaseFoot : ∀ i<F.limbs,¬ R.foot b x (base+i))
    (hloFoot : ∀ i<F.limbs,¬ R.foot b x (lo+i))
    (hupFoot : ∀ i<F.limbs,¬ R.foot b x (up+i))
    (hspace : v+(1+10*F.limbs)<2^w) :
    (storeCoordinateContract w F.fmt.limbBits).pre
      [base,heap,lo,up,dst,F.limbs,v] mem' := by
  have hanswer := minRatioQuery_scalar_output F A G m κ α rate allocation R hout
  obtain ⟨queryEnd,s',x',hv,hbefore,_,hz,_,_,hframe,_⟩ := hout
  change heap≤queryEnd at hbefore
  change v=queryEnd+F.limbs at hv
  change ∀ z<heap,¬ R.foot b x z → mem' z=mem z at hframe
  have hbase' : Num.Valid mem' base F.fmt.limbBits F.limbs := by
    intro i hi
    rw [hframe (base+i) (by omega) (hbaseFoot i hi)]
    exact hbase i hi
  have hlo' : Num.Valid mem' lo F.fmt.limbBits F.limbs := by
    intro i hi
    rw [hframe (lo+i) (by omega) (hloFoot i hi)]
    exact hlo i hi
  have hup' : Num.Valid mem' up F.fmt.limbBits F.limbs := by
    intro i hi
    rw [hframe (up+i) (by omega) (hupFoot i hi)]
    exact hup i hi
  exact ⟨base,heap,lo,up,dst,F.limbs,v,rfl,by omega,
    ⟨⟨base,heap,lo,up,F.limbs,v,rfl,by omega,hanswer.2,by omega,by omega,
      hbase',hanswer.1.1,hlo',hup'⟩,hz,hspace⟩⟩

end MinCostFlow.IPM.Machine
