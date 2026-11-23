module

public import MinCostFlow.MinRatio.FreshRecordModel

/-!
# Preparing a fresh-name record call

A valid IPM refresh has only insertions and deletions. For a deletion the
live edge resolves to its internal name by the two maps of Algorithm 2.
For an insertion the fresh counter supplies the name. These facts give
the dispatcher precondition when the tables, record and output fit.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

/-- The record form and external-name bound for a fixed-graph refresh. -/
def FreshRecordFits (extCap : ℕ) : Update → Prop
  | .insert e _ _ | .delete e => e < extCap
  | .split .. => False

/-- The name selected for a refresh record by `translateUpdate`. -/
def freshRecordName (e2i : ℕ → ℕ) (next : ℕ) : Update → ℕ
  | .insert .. => next
  | .delete e => e2i e
  | .split .. => 0

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine

/-- Tables for the current state and a fitting input record supply all
arguments of its machine dispatch. -/
theorem freshRecord_pre_of_tables {w src fwd inv counter heap next extCap intCap : ℕ}
    {extG intG : MGraph} {e2i i2e : ℕ → ℕ} {record : Update} {mem : ℕ → ℕ}
    (hF : FreshInv extG intG e2i i2e next) (hu : extG.UpdateIsValid record)
    (htable : FreshTablesAt mem fwd inv counter extCap intCap e2i i2e next)
    (hrecord : ListAt mem src (updateWords record))
    (hfit : FreshRecordFits extCap record) (hn : next < intCap)
    (hwords : ∀ x ∈ updateWords record, x < 2 ^ w)
    (hsrc : src + (updateWords record).length ≤ heap)
    (hroom : heap + (updateWords record).length < 2 ^ w)
    (hf : fwd + extCap ≤ heap) (hi : inv + intCap ≤ heap) (hc : counter < heap)
    (hdisjoint : fwd + extCap ≤ inv ∨ inv + intCap ≤ fwd)
    (hfc : counter < fwd ∨ fwd + extCap ≤ counter)
    (hic : counter < inv ∨ inv + intCap ≤ counter)
    (hz : ZeroFrom mem heap) :
    (freshRecordContract w record (freshRecordName e2i next record)).pre
      [src, fwd, inv, counter, heap] mem := by
  refine ⟨src, fwd, inv, counter, heap, rfl, ?_⟩
  cases record with
  | split _ _ _ => cases hfit
  | delete e =>
    simp only [freshRecordName]
    have he : e < extCap := hfit
    have heMem : e ∈ extG.E := hu
    have hint : e2i e ∈ intG.E := by rw [hF.hE]; exact Finset.mem_image_of_mem e2i heMem
    have hlt := hF.hLtFresh (e2i e) hint
    change src + 2 ≤ heap at hsrc
    change heap + 2 < 2 ^ w at hroom
    refine ⟨⟨src, fwd, heap, rfl, hsrc, by omega, by omega, hrecord, htable.2.1 e he⟩, hz, hroom⟩
  | insert e u v =>
    simp only [freshRecordName]
    have he : e < extCap := hfit
    change src + 4 ≤ heap at hsrc
    change heap + 4 < 2 ^ w at hroom
    have hew := hwords e (by simp [updateWords])
    have huw := hwords u (by simp [updateWords])
    have hvw := hwords v (by simp [updateWords])
    refine ⟨hsrc, hrecord, hew, huw, hvw, fwd, inv, counter, heap, rfl, htable.1, ?_, hroom,
      ?_, ?_, hc, ?_, ?_, ?_, hz⟩ <;> omega

/-- Under the capacity bound, the chosen name meets the map-update
conditions used in the dispatcher's model postcondition. -/
theorem freshRecordName_model (e2i : ℕ → ℕ) {extCap intCap next : ℕ} {record : Update}
    (hfit : FreshRecordFits extCap record) (hn : next < intCap) :
    match (motive := Update → Prop) record with
    | .insert e _ _ => e < extCap ∧ next < intCap ∧ freshRecordName e2i next record = next
    | .delete e => freshRecordName e2i next record = e2i e
    | .split .. => False := by
  cases record with
  | split _ _ _ => exact hfit
  | insert e u v => exact ⟨hfit, hn, rfl⟩
  | delete e => rfl

/-- The two writes selected by an insertion fall within the name tables. -/
theorem freshRecordName_frame (e2i : ℕ → ℕ) {extCap intCap next : ℕ} {record : Update}
    (hfit : FreshRecordFits extCap record) (hn : next < intCap) :
    match (motive := Update → Prop) record with
    | .insert e _ _ => e < extCap ∧ freshRecordName e2i next record < intCap
    | .delete _ => True
    | .split .. => False := by
  cases record with
  | split _ _ _ => exact hfit
  | insert e u v => exact ⟨hfit, hn⟩
  | delete e => trivial

end MinCostFlow.MinRatio
