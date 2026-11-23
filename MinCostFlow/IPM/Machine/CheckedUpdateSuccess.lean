module

public import MinCostFlow.IPM.Machine.CheckedUpdateFrame
public import MinCostFlow.IPM.Machine.CheckedUpdateRanges

/-!
# Successful checked Updates retain valid coefficient ranges

A final success bit cannot come from a rejected coefficient scan. The
actual accepted scan bounds every reported entry, while the old input
invariant bounds all unreported entries. The caller-table frame keeps
these checked arrays intact through Update and its final status record.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A successful final status implies that the actual coefficient scan
accepted and that the complete batch/Update continuation ran. -/
theorem checkedUpdate_success_scan {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap neg mx mn v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hout : (checkedUpdateContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem v mem')
    (haccept : mem' (v-1)=1) :
    ∃ checkedEnd checkedMem,
      (coefficientRangeReportContract w F.fmt.limbBits S).post
        [report,g,l,neg,mx,mn,F.limbs,heap] mem checkedEnd checkedMem ∧
      checkedMem (checkedEnd-1)=1 ∧
      (batchUpdateStatusContract F A I κ α rate allocation R b s x S).post
        [b,source,report,g,l,eta,F.limbs,checkedEnd] checkedMem v mem' := by
  obtain ⟨checkedEnd,checkedMem,hReport,hbranch,_⟩ := hout
  by_cases hscan : checkedMem (checkedEnd-1)=1
  · rw [ite_eq_left hscan] at hbranch
    exact ⟨checkedEnd,checkedMem,hReport,hscan,hbranch⟩
  · rw [ite_eq_right hscan] at hbranch
    obtain ⟨rfl,rfl⟩ := hbranch
    exact False.elim (hscan haccept)

/-- On success both stored coefficient vectors retain their full range
invariant at the final actual memory, ready for the next iteration. -/
theorem checkedUpdate_success_ranges {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap neg mx mn v tableEnd : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hpre : (checkedUpdateContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem)
    (hout : (checkedUpdateContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem v mem')
    (haccept : mem' (v-1)=1)
    (havoid : ∀ z<tableEnd,¬ R.foot b x z) (hbefore : tableEnd≤heap)
    (hg : g+I.m*F.limbs≤tableEnd) (hl : l+I.m*F.limbs≤tableEnd) :
    ∀ e∈(namedInstance I).E,
      |readVector mem' g F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem' l F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem' l F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent := by
  obtain ⟨source',report',g',l',eta',heap',neg',mx',mn',heq,hbatch,hRpt,_,_,_,_,_,_,_,_,_,_,_,_,hvalid,hn,hx,hm,hold,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨checkedEnd,checkedMem,hReport,hscan,_⟩ := checkedUpdate_success_scan F A I κ α rate allocation R hout haccept
  have hranges := checkedUpdate_coefficient_ranges F I hbatch hRpt hReport hscan hn hx hm hvalid hold
  have hs := checkedUpdate_coefficient_vectors F A I κ α rate allocation R hout havoid hbefore hg hl
  simpa only [hs.1,hs.2] using hranges

end MinCostFlow.IPM.Machine
