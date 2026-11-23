module

public import MinCostFlow.IPM.Machine.CheckedUpdate
public import MinCostFlow.IPM.Machine.BatchUpdateStatusOutput

/-!
# Returned status and heap bounds of the checked driver

Both branches return a bit and a fresh suffix. The rejected check
returns its exact two-word-record endpoint. The accepted branch uses
the uniform Update budget, so the complete driver's returned endpoint
also fits a word. These facts justify the enclosing iteration's return.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Every checked-driver outcome has a uniform bit and fresh zero suffix. -/
theorem checkedUpdate_status {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap neg mx mn v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hout : (checkedUpdateContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem v mem') :
    mem' (v-1)≤1 ∧ ZeroFrom mem' v := by
  obtain ⟨_,_,_,_,hbit,hzero⟩ := hout
  exact ⟨hbit,hzero⟩

/-- The explicit checked-driver input budget covers either returned
endpoint, even when a coefficient check rejects before Update. -/
theorem checkedUpdate_value_lt {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap neg mx mn v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hpre : (checkedUpdateContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem)
    (hout : (checkedUpdateContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem v mem') : v<2^w := by
  obtain ⟨source',report',g',l',eta',heap',neg',mx',mn',heq,hdata⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hspace,_⟩ := hdata
  simp only [checkedUpdateContract,List.getD_cons_zero,List.getD_cons_succ] at hout
  obtain ⟨checkedEnd,checkedMem,hR,hbranch,_⟩ := hout
  obtain ⟨_,_,hrecord⟩ := hR
  have hv := hrecord.2
  change checkedEnd=heap+2 at hv
  split_ifs at hbranch
  · exact batchUpdateStatus_value_lt_of_budget F A I κ α rate allocation R (by rw [hv]; exact hspace) hbranch
  · obtain ⟨rfl,rfl⟩ := hbranch
    omega

/-- The uniform caller budget bounds either returned endpoint exactly,
so extra fresh metadata space can be reserved without changing the call. -/
theorem checkedUpdate_end_le {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap neg mx mn v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hspace : (heap+2)+(1+6*S.card)+updateAllocationBound w b g l eta allocation+(1+2*F.limbs)+2<2^w)
    (hout : (checkedUpdateContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem v mem') :
    v≤(heap+2)+(1+6*S.card)+updateAllocationBound w b g l eta allocation+(1+2*F.limbs)+2 := by
  obtain ⟨checkedEnd,checkedMem,hR,hbranch,_⟩ := hout
  obtain ⟨_,_,hrecord⟩ := hR
  have hv : checkedEnd=heap+2 := hrecord.2
  split_ifs at hbranch
  · have hh := batchUpdateStatus_end_le F A I κ α rate allocation R
      (by rw [hv]; exact hspace) hbranch
    simpa only [hv,List.getD_cons_zero,List.getD_cons_succ] using hh
  · obtain ⟨rfl,_⟩ := hbranch
    omega

/-- Every checked outcome advances beyond its input heap, including a
coefficient rejection before any Update. -/
theorem checkedUpdate_end_ge {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap neg mx mn v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hout : (checkedUpdateContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem v mem') : heap+2≤v := by
  obtain ⟨checkedEnd,checkedMem,hR,hbranch,_⟩ := hout
  obtain ⟨_,_,hscanRecord⟩ := hR
  have hend : checkedEnd=heap+2 := hscanRecord.2
  split_ifs at hbranch
  · obtain ⟨coreEnd,coreMem,hcore,hrecord⟩ := hbranch
    have hlo := (batchUpdate_end_le F A I κ α rate allocation R hcore).1
    have hv : v=coreEnd+2 := hrecord.2
    omega
  · obtain ⟨rfl,_⟩ := hbranch
    omega

/-- The checked input itself supplies the uniform allocation bound
needed to bound its actual returned endpoint. -/
theorem checkedUpdate_end_le_of_pre {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap neg mx mn v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hpre : (checkedUpdateContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem)
    (hout : (checkedUpdateContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem v mem') :
    v≤(heap+2)+(1+6*S.card)+updateAllocationBound w b g l eta allocation+(1+2*F.limbs)+2 := by
  obtain ⟨source',report',g',l',eta',heap',neg',mx',mn',heq,hdata⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hspace,_⟩ := hdata
  exact checkedUpdate_end_le F A I κ α rate allocation R hspace hout

end MinCostFlow.IPM.Machine
