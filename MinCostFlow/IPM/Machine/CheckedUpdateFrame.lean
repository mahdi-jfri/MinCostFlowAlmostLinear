module

public import MinCostFlow.IPM.Machine.CheckedUpdate
public import MinCostFlow.IPM.Machine.BatchUpdateStatusOutput
import MinCostFlow.IPM.Machine.VectorFrame

/-!
# The checked Update preserves caller coefficient tables

The coefficient scan is read-only and its status record is fresh.
Batch preparation and Update preserve the old caller prefix outside
the parameter's footprint. The final status is fresh too. Combining
these frames preserves every caller-owned coefficient block, on both
branches and on either Update answer.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The whole checked driver preserves every old caller word outside
the incoming DS footprint, including when the scan rejects. -/
theorem checkedUpdate_frame {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap neg mx mn v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hout : (checkedUpdateContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem v mem') :
    ∀ z<heap,¬ R.foot b x z → mem' z=mem z := by
  obtain ⟨checkedEnd,checkedMem,hReport,hbranch,_⟩ := hout
  obtain ⟨bit,_,hRecord⟩ := hReport
  have hframe : ∀ z<heap,checkedMem z=mem z := hRecord.1.2.2.1
  have hend : checkedEnd=heap+2 := hRecord.2
  intro z hz hn
  split_ifs at hbranch
  · have hf := (batchUpdateStatus_frame F A I κ α rate allocation R hbranch).2
    exact (hf z (by omega) hn).trans (hframe z hz)
  · obtain ⟨_,rfl⟩ := hbranch
    exact hframe z hz

/-- All dense coefficient entries remain exactly the checked inputs
through batch preparation, Update and the final status record. -/
theorem checkedUpdate_coefficient_vectors {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap neg mx mn v tableEnd : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hout : (checkedUpdateContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem v mem')
    (havoid : ∀ z<tableEnd,¬ R.foot b x z) (hbefore : tableEnd≤heap)
    (hg : g+I.m*F.limbs≤tableEnd) (hl : l+I.m*F.limbs≤tableEnd) :
    readVector mem' g F.fmt.limbBits F.limbs F.fmt.precision I.m=
      readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m ∧
    readVector mem' l F.fmt.limbBits F.limbs F.fmt.precision I.m=
      readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m := by
  have hframe : ∀ z<tableEnd,mem' z=mem z := fun z hz =>
    checkedUpdate_frame F A I κ α rate allocation R hout z (hz.trans_le hbefore) (havoid z hz)
  exact ⟨readVector_eq_of_agree_below hframe hg,readVector_eq_of_agree_below hframe hl⟩

end MinCostFlow.IPM.Machine
