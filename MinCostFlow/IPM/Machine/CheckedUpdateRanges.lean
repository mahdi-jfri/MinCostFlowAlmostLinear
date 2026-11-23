module

public import MinCostFlow.IPM.Machine.CheckedReportUpdateInput
public import MinCostFlow.IPM.Machine.CoefficientRangeListOutput
import Mathlib.Tactic.Positivity

/-!
# An accepted report check establishes all Update coefficient ranges

The branch into Update needs bounds for every graph edge. Its actual
scan certifies all reported entries, and the previous table invariant
supplies the unchanged entries. This proof splits membership in the
Detect set. The machine performs no scan over the unreported edges.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- An accepted actual checked-report result and the old bounds outside
its set supply the full real-vector range premise needed by Update. -/
theorem checkedUpdate_coefficient_ranges {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    {source report g l neg mx mn heap v : ℕ} {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hbatch : (detectBatchContract w I S).pre [source,report,heap] mem)
    (hpre : (coefficientRangeReportContract w F.fmt.limbBits S).pre
      [report,g,l,neg,mx,mn,F.limbs,heap] mem)
    (hout : (coefficientRangeReportContract w F.fmt.limbBits S).post
      [report,g,l,neg,mx,mn,F.limbs,heap] mem v mem') (haccept : mem' (v-1)=1)
    (hn : ScalarAt mem neg F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hx : ScalarAt mem mx F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hm : ScalarAt mem mn F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hvalid : ∀ e<I.m,Num.Valid mem (g+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (l+e*F.limbs) F.fmt.limbBits F.limbs)
    (hold : ∀ e∈(namedInstance I).E,e∉S →
      |readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent) :
    ∀ e∈(namedInstance I).E,
      |readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent := by
  have hd := coefficientRangeReport_output hpre hout
  obtain ⟨⟨source',report',heap',heq,_,_,hDetect,hsubset,_⟩,_,_⟩ := hbatch
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  have hranges := coefficientRangeList_accepted hDetect hd.2.2.2.1 hn hx hm
    (fun e he => hvalid e (Finset.mem_range.mp (hsubset he))) haccept
    (by positivity : (0:ℝ)<(2:ℝ)^(-(F.rangeExponent:ℤ)))
  intro e he
  by_cases hin : e∈S
  · have heM : e<I.m := Finset.mem_range.mp he
    simpa only [readVector,heM,↓reduceIte] using
      And.intro (hranges e hin).1 (And.intro (hranges e hin).2.1 (hranges e hin).2.2.1)
  · exact hold e he hin

end MinCostFlow.IPM.Machine
