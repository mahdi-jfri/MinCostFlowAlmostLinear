module

public import MinCostFlow.IPM.Machine.DetectSnapshot
public import WordRAM.DataStructure

/-!
# DS separation of a caller-owned Detect snapshot

Copying a Detect answer above the old footprint leaves its concrete DS
state and potential unchanged. The copied header and names avoid that
footprint. Subsequent operations may grow their footprint only above the
advanced heap, so the snapshot remains caller-owned.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A fresh snapshot preserves the same DS representation and credit,
and none of its output words belong to the old concrete footprint. -/
theorem detectSnapshot_preserves_state {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    {w report heap v b : ℕ} {S : Finset ℕ} {s : σ} {x : R.τ}
    {mem mem' : ℕ → ℕ}
    (hout : (detectSnapshotContract w S).post [report,heap] mem v mem')
    (hrep : R.rep b s x mem) (hfoot : ∀ z,R.foot b x z → z<heap) :
    R.rep b s x mem' ∧ R.phi b x mem=R.phi b x mem' ∧
      ∀ i<1+S.card,¬ R.foot b x (heap+i) := by
  have hframe := hout.1.2.2.1
  change ∀ z<heap,mem' z=mem z at hframe
  have hh := hlocal b s x mem mem' (fun z hz => (hframe z (hfoot z hz)).symm)
  refine ⟨hh.1 hrep,hh.2,?_⟩
  intro i _ hi
  have := hfoot (heap+i) hi
  omega

end MinCostFlow.IPM.Machine
