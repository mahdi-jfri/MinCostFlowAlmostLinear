module

public import MinCostFlow.IPM.Machine.CoefficientRefresh
public import MinCostFlow.IPM.Machine.MinRatioContract
public import MinCostFlow.IPM.NamedInstance
import WordRAM.Memory

/-!
# Feeding computed coefficient arrays to min-ratio initialization

The graph serializer writes the fixed named instance. Coefficient refresh
preserves it, writes valid dense arrays, and gives positive lengths.
These facts discharge the graph and coefficient clauses of the shared
Definition 4.5 machine interface. The numerical range and precision
clauses remain the explicit static conditions proved by parameter selection.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual two-array refresh output meets the min-ratio Init input
layout and positivity requirements, preserving the serialized graph.
The quality lower bound and precision margin are the interface's exact
static arithmetic conditions. -/
theorem minRatio_initPre_after_refresh {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    {graph cp rp lo fp up ap one E heap v : ℕ} {mem mem' : ℕ → ℕ}
    (hI : I.IsValid)
    (hgraph : GraphAt mem graph (namedInstance I))
    (hgraphWords : ∀ x ∈ graphWords (namedInstance I),x < 2^w)
    (hgraphEnd : graph+(graphWords (namedInstance I)).length ≤ heap)
    (hquality : (2:ℝ)^(-(F.rangeExponent:ℤ)) ≤ κ*α)
    (hprecision : 5*F.rangeExponent+Nat.size I.m+30 ≤ F.fmt.precision)
    (hout : (coefficientRefreshContract w F.fmt.limbBits q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap] mem v mem')
    (hlengths : LengthsWithin (namedInstance I) F.rangeExponent
      (readVector mem' heap F.fmt.limbBits F.limbs F.fmt.precision I.m)) :
    (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).initPre
      [graph,heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,heap,F.limbs,F.fmt.precision,v] mem' := by
  obtain ⟨⟨hloV,hhiV,hframe,hzero,hlength,hgradient⟩,hv⟩ := hout
  change ∀ x < heap,mem' x=mem x at hframe
  change v=heap+(Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E+
    Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E) at hv
  change ∀ i < I.m,Num.Valid mem' (heap+i*F.limbs) F.fmt.limbBits F.limbs ∧
    ScalarApprox (1+1/(2:ℝ)^q)
      (Num.fixVal mem' (heap+i*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision) _ at hlength
  change ∀ i < I.m,Num.Valid mem'
    (heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E+i*F.limbs)
      F.fmt.limbBits F.limbs ∧ _ at hgradient
  have hml : I.m*F.limbs ≤ (I.m+1)*F.limbs :=
    Nat.mul_le_mul_right _ (by omega)
  have hls : I.m*F.limbs ≤ Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E := by
    unfold Num.IPM.lengthArraySpace
    omega
  have hgs : I.m*F.limbs ≤ Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E := by
    unfold Num.IPM.gradientArraySpace
    omega
  refine ⟨graph,heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,heap,v,
    rfl,hquality,hprecision,hgraph.of_agree_below hgraphEnd hframe,hgraphWords,
    namedInstance_valid I hI,?_,by omega,by omega,by omega,?_,?_,hlengths⟩
  · intro e he
    exact Finset.mem_range.mp he
  · intro e he
    exact ⟨(hgradient e he).1,(hlength e he).1⟩
  · intro e he
    have hem : e < I.m := Finset.mem_range.mp he
    simp only [readVector,hem,↓reduceIte]
    exact (hlength e hem).2.1

/-- Refreshing lengths and gradients into the machine workspace prepares
the 7-argument `V`-passing Init precondition as well. -/
theorem minRatio_initPreWithV_after_refresh {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (V : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    {cp rp lo fp up ap one E heap v graph : ℕ} {mem mem' : ℕ → ℕ}
    (hI : I.IsValid) (hgraph : GraphAt mem graph (namedInstance I))
    (hwords : ∀ z∈graphWords (namedInstance I),z<2^w)
    (hgraphEnd : graph+(graphWords (namedInstance I)).length≤heap)
    (hk : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α)
    (hprec : 5*F.rangeExponent+Nat.size I.m+30≤F.fmt.precision)
    (hout : (coefficientRefreshContract w F.fmt.limbBits q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap] mem v mem')
    (hlengths : LengthsWithin (namedInstance I) F.rangeExponent
      (readVector mem' heap F.fmt.limbBits F.limbs F.fmt.precision I.m))
    (hgradients : ∀ e ∈ (namedInstance I).E,
      |readVector mem' (heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E)
        F.fmt.limbBits F.limbs F.fmt.precision I.m e| ≤ (2:ℝ)^F.rangeExponent) :
    (minRatioMachineContractWithV F A (namedInstance I) I.m V κ α rate allocation).initPre
      [graph,heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,heap,
        F.limbs,F.fmt.precision,V,v] mem' := by
  obtain ⟨g0,gl0,ll0,h0,heq,hk0,hprec0,hG,hGw,hGV,hEm,hGe,hge,hle,hVal,hlPos,hlW⟩ :=
    minRatio_initPre_after_refresh F A I κ α rate allocation
      hI hgraph hwords hgraphEnd hk hprec hout hlengths
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,_,_,rfl⟩ := heq
  exact ⟨graph,heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,heap,v,
    rfl,rfl,hk0,hprec0,hG,hGw,hGV,hEm,hGe,hge,hle,hVal,hlPos,hlW,hgradients⟩

end MinCostFlow.IPM.Machine
