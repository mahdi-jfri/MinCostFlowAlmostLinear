module

public import MinCostFlow.IPM.Machine.EpochStartupProgram
public import MinCostFlow.IPM.Machine.EpochStartNumericalInput

/-!
# Preparing the startup call after a residual test

The copied flow and held residual use the same chosen numerical format.
The graph, range margins and workspace then supply the initialization
precondition for this next epoch.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Supply startup's full input from its numerical coefficient input,
with the graph and precision margin in the actual caller layout. -/
theorem targetEpoch_startup_pre {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (mem : ℕ → ℕ)
    (hI : I.IsValid) (hgraph : GraphAt mem L.initGraph (namedInstance I))
    (hwords : ∀ z∈graphWords (namedInstance I),z<2^w)
    (hend : L.initGraph+(graphWords (namedInstance I)).length≤L.sourceEnd)
    (hquality : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α)
    (hprecision : 5*F.rangeExponent+I.m.size+30≤F.fmt.precision)
    (hnums : (coefficientRefreshContract w F.fmt.limbBits q K).pre ((L.startPacket F I).take 14) mem)
    (hspace : L.sourceEnd+epochStartSpace F I L.exponent L.initGraph L.sourceEnd allocation<2^w)
    (hlenRange : ∀ i<I.m,(2:ℝ)^(-(F.rangeExponent:ℤ))*2≤
      Num.IPM.arrayLength mem L.lower L.flow L.upper L.alpha F.fmt.limbBits F.limbs F.fmt.precision i ∧
      2*Num.IPM.arrayLength mem L.lower L.flow L.upper L.alpha F.fmt.limbBits F.limbs F.fmt.precision i≤
        (2:ℝ)^F.rangeExponent) :
    (epochStartContract F A I κ α rate allocation R q K).pre (L.startPacket F I) mem :=
  ⟨L.cost,L.residual,L.lower,L.flow,L.upper,L.alpha,L.one,L.exponent,L.initGraph,L.sourceEnd,
    rfl,hI,hgraph,hwords,hend,hquality,hprecision,hnums,hspace,hlenRange⟩

/-- The startup scan returns a bit. Its endpoint includes at most one
extra failure word after Init, the name list and the budget record. -/
theorem epochStartup_flag_and_space {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (old : EpochLayout) (base rp fp heap initEnd bit v : ℕ)
    (mem initialized started final : ℕ → ℕ)
    (hOut : (epochStartContract F A I κ α rate allocation R q K).post
      ((old.next F I base rp fp heap initEnd).startPacket F I) mem initEnd initialized)
    (hScan : let L := old.next F I base rp fp heap initEnd
      (coefficientRangeListContract w F.fmt.limbBits).post
        [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] started bit started)
    (hStatus : if bit=1 then v=initEnd+I.m+3 ∧ final=started else
      (flagRecordContract w).post [0,initEnd+I.m+3] started v final)
    (hz : ZeroFrom started (initEnd+I.m+3)) :
    bit≤1 ∧ ZeroFrom final v ∧
      heap≤v ∧ v≤heap+epochStartSpace F I old.exponent old.initGraph heap allocation+I.m+4 ∧
      (∀ z<heap,final z=started z) := by
  have hbit : bit≤1 := hScan.2.1
  obtain ⟨_,_,_,_,_,_,hLower,hUpper,_⟩ := epochStart_output F A I κ α rate allocation R hOut
  change heap+(Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent+
    Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent)≤ initEnd at hLower
  have hUpper' : initEnd≤heap+epochStartSpace F I old.exponent old.initGraph heap allocation := by
    simpa only [EpochLayout.startPacket,EpochLayout.next,epochStartSpace,Nat.add_assoc,
      List.getD_cons_zero,List.getD_cons_succ] using hUpper
  have hheap : heap ≤ initEnd := by omega
  by_cases hb : bit=1
  · rw [ite_eq_left hb] at hStatus
    obtain ⟨rfl,rfl⟩ := hStatus
    exact ⟨hbit,hz,by omega,by omega,fun _ _ => rfl⟩
  · rw [ite_eq_right hb] at hStatus
    have hv : v=initEnd+I.m+4 := hStatus.2
    exact ⟨hbit,hStatus.1.2.2.2.1,by omega,by omega,fun z hz' => hStatus.1.2.2.1 z (show z < initEnd+I.m+3 by omega)⟩

end MinCostFlow.IPM.Machine
