module

public import MinCostFlow.IPM.Machine.CheckedReportBatchInput
public import MinCostFlow.IPM.Machine.BatchUpdateStatus
public import MinCostFlow.IPM.Machine.VectorFrame
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Full Update input after the checked coefficient record

The record preserves all checked coefficient and normalization blocks
and the same concrete DS state. Transfer the batch-writer input and
those numeric invariants to its new heap. The uniform allocation bound
then supplies the complete input and argument words of the actual
batch/Update/status entry.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Every batch/Update/status call premise follows from the actual checked
report output, the established numeric invariants, and one explicit
uniform workspace budget. All source blocks are preserved by its frame. -/
theorem batchUpdateStatus_pre_after_coefficientRangeReport {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State) (hlocal : R.Local)
    {source report heap v b g l eta neg mx mn : ℕ} {S : Finset ℕ}
    {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hbatch : (detectBatchContract w I S).pre [source,report,heap] mem)
    (hpre : (coefficientRangeReportContract w F.fmt.limbBits S).pre
      [report,g,l,neg,mx,mn,F.limbs,heap] mem)
    (hout : (coefficientRangeReportContract w F.fmt.limbBits S).post
      [report,g,l,neg,mx,mn,F.limbs,heap] mem v mem')
    (hrep : R.rep b s x mem) (hfoot : ∀ z,R.foot b x z → z<heap)
    (hfit : MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s)
    (hk : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α)
    (hprec : 5*F.rangeExponent+Nat.size I.m+30≤F.fmt.precision)
    (hq : ∀ e∈(namedInstance I).E,|A.query s e|≤(2:ℝ)^F.rangeExponent)
    (hgEnd : g+I.m*F.limbs≤heap) (hlEnd : l+I.m*F.limbs≤heap)
    (heEnd : eta+F.limbs≤heap) (heValid : Num.Valid mem eta F.fmt.limbBits F.limbs)
    (heLo : (2:ℝ)^(-(F.rangeExponent:ℤ))≤Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision)
    (heHi : Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^F.rangeExponent)
    (hvalid : ∀ e<I.m,Num.Valid mem (g+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (l+e*F.limbs) F.fmt.limbBits F.limbs)
    (hrange : ∀ e∈(namedInstance I).E,
      |readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)
    (hdetected : MinRatioDetectedWith A (namedInstance I) s (· ∈ S)
      (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m))
    (hspace : v+(1+6*S.card)+updateAllocationBound w b g l eta allocation+(1+2*F.limbs)+2<2^w)
    (hwords : ∀ z∈[b,source,report,g,l,eta,F.limbs,heap],z<2^w) :
    (batchUpdateStatusContract F A I κ α rate allocation R b s x S).pre
      [b,source,mem' (v-2),g,l,eta,F.limbs,v] mem' ∧
      (∀ z∈[b,source,mem' (v-2),g,l,eta,F.limbs,v],z<2^w) := by
  have hd := coefficientRangeReport_output hpre hout
  have hf := hd.2.2.2.2.2.2
  have hstate := coefficientRangeReport_preserves_state R hlocal hout hrep hfoot
  have hbatch' := detectBatch_pre_after_coefficientRangeReport hbatch hpre hout (by omega)
  have hg := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hf hgEnd
  have hl := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hf hlEnd
  have hgv := vector_valid_of_agree_below hf hgEnd (fun e he => (hvalid e he).1)
  have hlv := vector_valid_of_agree_below hf hlEnd (fun e he => (hvalid e he).2)
  have heta := Num.IPM.fixVal_frozen (h:=F.fmt.limbBits) (P:=F.fmt.precision) hf heEnd
  have hlocalSpace := batchUpdate_budget_of_uniform (w:=w) (b:=b) (g:=g) (l:=l) (eta:=eta) (L:=F.limbs)
    allocation (heap:=v) (count:=S.card) (by omega)
  refine ⟨⟨?_,?_⟩,?_⟩
  · refine ⟨source,mem' (v-2),g,l,eta,v,rfl,hbatch',hstate.1,hstate.2.2,hfit,hk,hprec,hq,
      ?_,?_,?_,Num.IPM.valid_frozen hf heEnd heValid,?_,?_,?_,?_,hlocalSpace,?_⟩
    · have hv := hd.2.2.2.2.1
      omega
    · have hv := hd.2.2.2.2.1
      omega
    · have hv := hd.2.2.2.2.1
      omega
    · rw [heta]
      exact heLo
    · rw [heta]
      exact heHi
    · exact fun e he => ⟨hgv e he,hlv e he⟩
    · intro e he
      rw [hg,hl]
      exact hrange e he
    · rw [hg,hl]
      exact hdetected
  · exact hspace
  · intro z hz
    rw [hd.1] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with hz | hz | hz | hz | hz | hz | hz | hz
    all_goals subst z
    · exact hwords _ (by simp)
    · exact hwords _ (by simp)
    · exact hwords _ (by simp)
    · exact hwords _ (by simp)
    · exact hwords _ (by simp)
    · exact hwords _ (by simp)
    · exact hwords _ (by simp)
    · omega

end MinCostFlow.IPM.Machine
