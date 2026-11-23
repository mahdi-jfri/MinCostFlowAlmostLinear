module

public import MinCostFlow.IPM.Machine.EpochLayout
public import MinCostFlow.IPM.Machine.PrecisionParameters
public import MinCostFlow.IPM.Machine.InitialEncodedInstance
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Fixed input words and numerical parameters within an epoch

The base, graph, capacities, cost, held residual, exponent, normalization
request and guard constants precede the mutable flow table. Their input
conditions therefore survive every actual iteration's prefix frame.
This predicate concerns those fixed input words and their layout only.
The changing cache and DS history belong to the separate epoch condition.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The permanent input conditions needed to execute an epoch iteration.
The stored values use the numerical procedures' existing fixed-point format. -/
def EpochStaticInputsAt {w : ℕ} (F : MinRatioFormat w) (I : Instance) (U R : ℕ)
    (κ α eps : ℝ) (L : EpochLayout) (capacity normalization : ℝ) (mem : ℕ → ℕ) : Prop :=
  (∀ z∈L.packet F I 0,z<2^w) ∧ I.IsValid ∧
  ListAt mem L.graph (zeroLowerWords I) ∧ L.graph+(zeroLowerWords I).length≤L.flow ∧
  (∀ z∈zeroLowerWords I,z<2^w) ∧
  (∀ p∈[L.base,L.cost,L.lower,L.upper],p+I.m*F.limbs≤L.flow) ∧
  (∀ p∈[L.residual,L.alpha,L.one,L.slackMin,L.slackMax],p+F.limbs≤L.flow) ∧
  (∀ p∈[L.request,L.gradientMin,L.gradientMax,L.lengthMin],p+F.limbs≤L.flow) ∧
  ScalarAt mem L.request F.fmt.limbBits F.limbs F.fmt.precision normalization ∧
  (2:ℝ)^(-(F.rangeExponent:ℤ))≤normalization ∧ normalization≤(2:ℝ)^F.rangeExponent ∧
  ScalarAt mem L.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent) ∧
  ScalarAt mem L.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent) ∧
  ScalarAt mem L.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))) ∧
  (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α ∧ 5*F.rangeExponent+Nat.size I.m+30≤F.fmt.precision ∧
  capacity≤(2:ℝ)^(slackRangeExponent I.m U) ∧
  (∀ e∈(namedInstance I).E,
    |Num.fixVal mem (L.base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
    |Num.fixVal mem (L.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
    |Num.fixVal mem (L.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity) ∧
  (∀ e∈(namedInstance I).E,0≤Num.fixVal mem (L.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision) ∧
  (0≤Num.fixVal mem L.alpha F.fmt.limbBits F.limbs F.fmt.precision ∧
    Num.fixVal mem L.alpha F.fmt.limbBits F.limbs F.fmt.precision≤1) ∧
  F.rangeExponent=R ∧ 0<eps ∧ eps≤1

/-- Permanent inputs at the original binary range. -/
def EpochStaticInputs {w : ℕ} (F : MinRatioFormat w) (I : Instance) (U : ℕ)
    (κ α eps : ℝ) (L : EpochLayout) (capacity normalization : ℝ) (mem : ℕ → ℕ) : Prop :=
  EpochStaticInputsAt F I U (ipmRangeExponent I.m U) κ α eps L capacity normalization mem

/-- Every permanent epoch input condition survives the actual prefix
frame preceding the mutable flow table. -/
theorem EpochStaticInputsAt.frozen {w : ℕ} {F : MinRatioFormat w} {I : Instance} {U R : ℕ}
    {κ α eps : ℝ} {L : EpochLayout} {capacity normalization : ℝ} {mem mem' : ℕ → ℕ}
    (h : EpochStaticInputsAt F I U R κ α eps L capacity normalization mem)
    (hframe : ∀ z<L.flow,mem' z=mem z) :
    EpochStaticInputsAt F I U R κ α eps L capacity normalization mem' := by
  obtain ⟨hwords,hI,hgraph,hgraphEnd,hgraphWords,harrays,hscalars,hguards,hrequest,hnormLo,hnormHi,
    hneg,hmax,hmin,hquality,hprecision,hcapacity,hsources,hlower,halpha,hformat,heps,hepsHi⟩ := h
  have scalar_frozen (p : ℕ) (hp : p+F.limbs≤L.flow) {value : ℝ}
      (hs : ScalarAt mem p F.fmt.limbBits F.limbs F.fmt.precision value) :
      ScalarAt mem' p F.fmt.limbBits F.limbs F.fmt.precision value :=
    ⟨Num.IPM.valid_frozen hframe hp hs.1,(Num.IPM.fixVal_frozen hframe hp).trans hs.2⟩
  have hentry (p e : ℕ) (hp : p∈[L.base,L.cost,L.lower,L.upper]) (he : e<I.m) :
      p+e*F.limbs+F.limbs≤L.flow := (reported_entry_end p F.limbs e I.m he).trans (harrays p hp)
  have hfix (p e : ℕ) (hp : p∈[L.base,L.cost,L.lower,L.upper]) (he : e<I.m) :
      Num.fixVal mem' (p+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
        Num.fixVal mem (p+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision :=
    Num.IPM.fixVal_frozen hframe (hentry p e hp he)
  refine ⟨hwords,hI,?_,hgraphEnd,hgraphWords,harrays,hscalars,hguards,
    scalar_frozen L.request (hguards _ (by simp)) hrequest,hnormLo,hnormHi,
    scalar_frozen L.gradientMin (hguards _ (by simp)) hneg,
    scalar_frozen L.gradientMax (hguards _ (by simp)) hmax,
    scalar_frozen L.lengthMin (hguards _ (by simp)) hmin,hquality,hprecision,hcapacity,?_,?_,?_,hformat,heps,hepsHi⟩
  · exact hgraph.congr (fun z _ hz => hframe z (hz.trans_le hgraphEnd))
  · intro e he
    have heM : e<I.m := Finset.mem_range.mp he
    rw [hfix L.base e (by simp) heM,hfix L.lower e (by simp) heM,hfix L.upper e (by simp) heM]
    exact hsources e he
  · intro e he
    rw [hfix L.lower e (by simp) (Finset.mem_range.mp he)]
    exact hlower e he
  · rw [Num.IPM.fixVal_frozen hframe (hscalars L.alpha (by simp))]
    exact halpha

/-- Every permanent epoch input condition survives the actual prefix
frame preceding the mutable flow table. -/
theorem EpochStaticInputs.frozen {w : ℕ} {F : MinRatioFormat w} {I : Instance} {U : ℕ}
    {κ α eps : ℝ} {L : EpochLayout} {capacity normalization : ℝ} {mem mem' : ℕ → ℕ}
    (h : EpochStaticInputs F I U κ α eps L capacity normalization mem)
    (hframe : ∀ z<L.flow,mem' z=mem z) :
    EpochStaticInputs F I U κ α eps L capacity normalization mem' :=
  EpochStaticInputsAt.frozen h hframe

end MinCostFlow.IPM.Machine
