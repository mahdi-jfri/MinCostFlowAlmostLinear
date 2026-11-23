module

public import MinCostFlow.IPM.Machine.QueryCoordinateOutput
public import MinCostFlow.IPM.Machine.SourceFlowWriteFrame

/-!
# Entering coefficient guards after actual coordinate recovery

The accepted Query-and-write procedure replaces the stored flow block.
Its source prefix lies outside the old DS footprint, and the other scalar
inputs avoid that block. Their arithmetic conditions survive. Acceptance
also bounds both slack magnitudes by the capacity width, supplying exact
subtraction without assuming the positive lower slack tested next.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Raw numeric conditions survive the actual accepted Query-and-write
procedure, including the valid new flow and the unchanged held residual. -/
theorem coefficient_sources_after_query {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b e base c r lo f up a one mn mx q K E sourceEnd heap v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hout : (queryCoordinateContract F A G m κ α rate allocation R b s x).post
      [b,e,base,lo,up,f,F.limbs,heap] mem v mem')
    (haccept : mem' (v-(1+4*F.limbs))=1)
    (hs : scalarCoefficientSourceConditions w F.fmt.limbBits q K m c r lo f up a one mn mx
      F.limbs F.fmt.precision E sourceEnd mem)
    (hend : sourceEnd≤heap) (hmn : mn+F.limbs≤sourceEnd) (hmx : mx+F.limbs≤sourceEnd)
    (hfoot : ∀ z<sourceEnd,¬ R.foot b x z)
    (hseparate : ∀ p∈[c,r,lo,up,a,one,mn,mx],p+F.limbs≤f ∨ f+F.limbs≤p) :
    scalarCoefficientSourceConditions w F.fmt.limbBits q K m c r lo f up a one mn mx
      F.limbs F.fmt.precision E v mem' := by
  have hframe := queryCoordinate_frame F A G m κ α rate allocation R hout
  have hsourceFrame : ∀ z<sourceEnd,(z<f ∨ f+F.limbs≤z) → mem' z=mem z := by
    intro z hz hdis
    exact hframe.2.2.2 z (by omega) (hfoot z hz) hdis
  obtain ⟨pad,queryMem,x',_,hN,_,_,_⟩ := hout
  have hv := hN.1
  change v=pad+(1+10*F.limbs) at hv
  have hslot : v-(1+4*F.limbs)=pad+6*F.limbs := by omega
  rw [hslot] at haccept
  have hvalid := hN.2.2.2.2.1
  change mem' (pad+6*F.limbs)=1 → Num.Valid mem' f F.fmt.limbBits F.limbs ∧ _ at hvalid
  exact scalarCoefficientSourceConditions_after_flow_write hs hsourceFrame
    (by omega : sourceEnd≤v) hmn hmx hseparate (hvalid haccept).1

/-- Actual accepted coordinate recovery supplies every precondition of
the following guarded coefficient computation from raw source data and
a capacity-width bound. The minimum slack is still checked by that call. -/
theorem guardedCoefficient_pre_after_query {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b e base c r lo f up a one mn mx q K E ld gd sourceEnd heap v : ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ} {baseValue : ℝ}
    (hout : (queryCoordinateContract F A G m κ α rate allocation R b s x).post
      [b,e,base,lo,up,f,F.limbs,heap] mem v mem')
    (haccept : mem' (v-(1+4*F.limbs))=1)
    (hs : scalarCoefficientSourceConditions w F.fmt.limbBits q K m c r lo f up a one mn mx
      F.limbs F.fmt.precision E sourceEnd mem)
    (hend : sourceEnd≤heap) (hmn : mn+F.limbs≤sourceEnd) (hmx : mx+F.limbs≤sourceEnd)
    (hfoot : ∀ z<sourceEnd,¬ R.foot b x z)
    (hseparate : ∀ p∈[c,r,lo,up,a,one,mn,mx],p+F.limbs≤f ∨ f+F.limbs≤p)
    (hbase : ScalarAt mem base F.fmt.limbBits F.limbs F.fmt.precision baseValue)
    (hbaseEnd : base+F.limbs≤sourceEnd)
    (hwidth : Num.fixVal mem up F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem lo F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^E)
    (hld : ld+F.limbs≤heap) (hgd : gd+F.limbs≤heap)
    (hdis : ld+F.limbs≤gd ∨ gd+F.limbs≤ld)
    (hspace : v+(4*F.limbs+1)+F.limbs+
      Num.IPM.lengthSpace F.limbs F.fmt.precision E+
      Num.IPM.gradientSpace F.limbs F.fmt.precision E+1<2^w) :
    (guardedCoefficientRefreshContract w F.fmt.limbBits q K).pre
      [m,c,r,lo,f,up,a,one,mn,mx,F.limbs,F.fmt.precision,E,ld,gd,v] mem' := by
  have hsrc := coefficient_sources_after_query F A G m κ α rate allocation R hout haccept hs
    hend hmn hmx hfoot hseparate
  obtain ⟨_,_,_,_,_,_,_,_,_,hlo,_,hup,_,_,_,_,hvl,_,hvu,_⟩ := hs
  have hbaseFoot : ∀ i<F.limbs,¬ R.foot b x (base+i) := fun i hi => hfoot _ (by omega)
  have hloFoot : ∀ i<F.limbs,¬ R.foot b x (lo+i) := fun i hi => hfoot _ (by omega)
  have hupFoot : ∀ i<F.limbs,¬ R.foot b x (up+i) := fun i hi => hfoot _ (by omega)
  have hflow := queryCoordinate_output F A G m κ α rate allocation R hout hbase
    (by omega : base+F.limbs≤heap) hbaseFoot haccept
  have hflag := queryCoordinate_acceptance F A G m κ α rate allocation R hout hbase
    ⟨hvl,rfl⟩ ⟨hvu,rfl⟩ (by omega) (by omega) (by omega) hbaseFoot hloFoot hupFoot
  have hinside : Num.fixVal mem lo F.fmt.limbBits F.limbs F.fmt.precision<baseValue+A.query s e ∧
      baseValue+A.query s e<Num.fixVal mem up F.fmt.limbBits F.limbs F.fmt.precision := by
    by_contra hh
    simp only [hh,ite_false] at hflag
    rw [haccept] at hflag
    contradiction
  have hframe := queryCoordinate_frame F A G m κ α rate allocation R hout
  have hsame (p : ℕ) (hp : p+F.limbs≤sourceEnd) (hpDis : p+F.limbs≤f ∨ f+F.limbs≤p) :
      Num.fixVal mem' p F.fmt.limbBits F.limbs F.fmt.precision=
        Num.fixVal mem p F.fmt.limbBits F.limbs F.fmt.precision := by
    unfold Num.fixVal
    rw [Num.intVal_congr (show ∀ i<F.limbs,mem' (p+i)=mem (p+i) from by
      intro i hi
      apply hframe.2.2.2 (p+i) (by omega) (hfoot _ (by omega))
      rcases hpDis with hh | hh <;> omega)]
  have hslacks := slack_subtraction_bounds_of_inside hinside.1 hinside.2 hwidth
  have hupper : |Num.fixVal mem' up F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem' f F.fmt.limbBits F.limbs F.fmt.precision|≤(2:ℝ)^E := by
    rw [hsame up hup (hseparate up (by simp)),hflow.2]
    exact hslacks.1
  have hlower : |Num.fixVal mem' f F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem' lo F.fmt.limbBits F.limbs F.fmt.precision|≤(2:ℝ)^E := by
    rw [hsame lo hlo (hseparate lo (by simp)),hflow.2]
    exact hslacks.2
  exact guardedCoefficient_pre_of_source_conditions hsrc (by omega) (by omega) hupper hlower
    (by omega) (by omega) hdis hframe.2.2.1 hspace

end MinCostFlow.IPM.Machine
