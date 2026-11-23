module

public import MinCostFlow.IPM.Machine.ReportedEdge

/-!
# Building a reported-edge call's machine precondition

A list invariant stores the raw numeric source conditions, the fixed
instance membership and the concrete DS representation. Construct the
nested Query and guarded-refresh preconditions from those data and the
caller-memory layout. No capacity acceptance or minimum slack is assumed:
the actual guards decide whether the recovered coordinate can be used.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Source, footprint and workspace invariants suffice for the complete
reported-edge precondition, including the nested Query recovery call. -/
theorem reportedEdge_pre_of_sources {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd e base lo up f c r a one mn mx E ld gd heap : ℕ}
    {s : A.State} {x : R.τ} {mem : ℕ → ℕ}
    (hs : scalarCoefficientSourceConditions w F.fmt.limbBits q K m c r lo f up a one mn mx
      F.limbs F.fmt.precision E sourceEnd mem)
    (hfit : MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision s)
    (he : e∈G.E) (hem : e<m) (hrep : R.rep b s x mem)
    (hfoot : ∀ z,R.foot b x z → z<heap) (hz : ZeroFrom mem heap)
    (hsource : sourceEnd≤heap) (hmn : mn+F.limbs≤sourceEnd) (hmx : mx+F.limbs≤sourceEnd)
    (hbase : base+F.limbs≤sourceEnd) (hvbase : Num.Valid mem base F.fmt.limbBits F.limbs)
    (hsourceFoot : ∀ z<sourceEnd,¬ R.foot b x z)
    (hseparate : ∀ p∈[c,r,lo,up,a,one,mn,mx],p+F.limbs≤f ∨ f+F.limbs≤p)
    (hwidth : Num.fixVal mem up F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem lo F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^E)
    (hld : ld+F.limbs≤heap) (hgd : gd+F.limbs≤heap)
    (hdis : ld+F.limbs≤gd ∨ gd+F.limbs≤ld)
    (hsld : sourceEnd≤ld) (hsgd : sourceEnd≤gd)
    (hcoefFoot : ∀ z,R.foot b x z → (z<ld ∨ ld+F.limbs≤z) ∧ (z<gd ∨ gd+F.limbs≤z))
    (hspace : heap+(minRatioMachineContract F A G m κ α rate allocation).space 1 s [b,e,heap] mem+
      16*F.limbs+Num.IPM.lengthSpace F.limbs F.fmt.precision E+
      Num.IPM.gradientSpace F.limbs F.fmt.precision E+4<2^w) :
    (reportedEdgeContract F A G m κ α rate allocation R b s x q K sourceEnd).pre
      [b,e,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem := by
  have hsCopy := hs
  obtain ⟨_,_,_,_,_,_,_,_,_,hlo,hf,hup,_,_,_,_,hvlo,_,hvup,_⟩ := hs
  have hDpre : (minRatioMachineContract F A G m κ α rate allocation).pre 1 s [b,e,heap] mem := by
    exact ⟨hfit,b,e,heap,rfl,he,hem⟩
  have hMQpre : (minRatioQueryContract w R
      (minRatioMachineContract F A G m κ α rate allocation) b s x).pre
        [b,e,F.limbs,heap] mem := by
    exact ⟨e,F.limbs,heap,rfl,hrep,hDpre,hfoot,hz,by omega⟩
  have hQpre : (queryCoordinateContract F A G m κ α rate allocation R b s x).pre
      [b,e,base,lo,up,f,F.limbs,heap] mem := by
    refine ⟨e,base,lo,up,f,heap,rfl,hMQpre,hvbase,hvlo,hvup,
      hbase.trans hsource,hlo.trans hsource,hup.trans hsource,hf.trans hsource,
      ?_,?_,?_,?_,by omega⟩
    · intro i hi
      exact hsourceFoot _ (by omega)
    · intro i hi
      exact hsourceFoot _ (by omega)
    · intro i hi
      exact hsourceFoot _ (by omega)
    · intro z hz0
      by_cases hlt : z<f
      · exact Or.inl hlt
      · exact Or.inr (by
          by_contra hn
          exact hsourceFoot z (by omega) hz0)
  exact ⟨e,base,lo,up,f,c,r,a,one,mn,mx,E,ld,gd,heap,rfl,hQpre,hsCopy,hsource,hmn,hmx,
    hbase,hsourceFoot,hseparate,hwidth,hld,hgd,hdis,hsld,hsgd,hcoefFoot,hspace⟩

end MinCostFlow.IPM.Machine
