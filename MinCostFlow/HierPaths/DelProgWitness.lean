module

public import MinCostFlow.HierPaths.DelProgFields

/-!
# Choosing a concrete witness for Delete

The cursor functions are stored only on their finite index ranges. Choosing zero at unused
indices preserves the memory block, invariant and potential.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Use zero for indices outside the two stored cursor tables. -/
def HierConcrete.delCursorWitness (x : HierConcrete) : HierConcrete :=
  x.withSt { x.ms.st with
    supCur := fun v => if v < x.ms.abs.G.n then x.ms.st.supCur v else 0
    pairCur := fun q => if q < x.H.A.numPairs then x.ms.st.pairCur q else 0 }

private theorem tabList_clip (n : ℕ) (f : ℕ → ℕ) :
    tabList n (fun i => if i < n then f i else 0) = tabList n f := by
  unfold tabList
  exact List.map_congr_left fun i hi => ite_eq_left (List.mem_range.mp hi)

/-- The witness has the original encoded memory. -/
theorem HierConcrete.delCursorWitness_encode (x : HierConcrete) :
    x.delCursorWitness.encode = x.encode := by
  have he : x.delCursorWitness.sections =
      (x.sections.set 20 (tabList x.ms.abs.G.n
        (fun v => if v < x.ms.abs.G.n then x.ms.st.supCur v else 0))).set
      21 (tabList x.H.A.numPairs (fun q => if q < x.H.A.numPairs then x.ms.st.pairCur q else 0)) := rfl
  change layoutList x.delCursorWitness.sections = layoutList x.sections
  rw [he, tabList_clip, tabList_clip]
  rfl

/-- The witness has the original potential. -/
theorem HierConcrete.delCursorWitness_potential (x : HierConcrete) :
    x.delCursorWitness.potential = x.potential := by
  have hs : (∑ v ∈ Finset.range x.n, if v < x.ms.abs.G.n then x.ms.st.supCur v else 0) =
      ∑ v ∈ Finset.range x.n, x.ms.st.supCur v := by
    exact Finset.sum_congr rfl fun v hv => ite_eq_left (Finset.mem_range.mp hv)
  have hp : (∑ q ∈ Finset.range x.H.A.numPairs,
      if q < x.H.A.numPairs then x.ms.st.pairCur q else 0) =
      ∑ q ∈ Finset.range x.H.A.numPairs, x.ms.st.pairCur q := by
    exact Finset.sum_congr rfl fun q hq => ite_eq_left (Finset.mem_range.mp hq)
  change (∑ v ∈ Finset.range x.ms.abs.G.n, if v < x.ms.abs.G.n then x.ms.st.supCur v else 0) =
    ∑ v ∈ Finset.range x.ms.abs.G.n, x.ms.st.supCur v at hs
  simp only [potential, StaticArrays.potential, StaticArrays.events, delCursorWitness, withSt,
    n, hp]
  rw [hs]

/-- The same abstract state is represented by the witness. -/
theorem HierConcrete.delCursorWitness_rel {a : ℕ} (x : HierConcrete) (h : x.H.Rel a x.ms) :
    x.delCursorWitness.H.Rel a x.delCursorWitness.ms := by
  refine ⟨h.spec, h.fits, ⟨h.inv.loss, h.inv.failed_sub, h.inv.rule, h.inv.inelig_eq, ?_, ?_⟩,
    h.deleted, h.vhat⟩
  · intro v hv
    change CurInv (x.H.A.supValid (x.H.A.surv x.ms.st) v) (x.H.A.C.supportArray v).length
      (if v < x.ms.abs.G.n then x.ms.st.supCur v else 0)
    rw [ite_eq_left (show v < x.ms.abs.G.n from hv)]
    exact h.inv.supCur v hv
  · intro q hq
    change CurInv (x.H.A.pairValid (x.H.A.surv x.ms.st) q) (x.H.A.pairConns q).length
      (if q < x.H.A.numPairs then x.ms.st.pairCur q else 0)
    rw [ite_eq_left (show q < x.H.A.numPairs from hq)]
    exact h.inv.pairCur q hq

theorem HierConcrete.delCursorWitness_cur_le {a : ℕ} (x : HierConcrete) (h : x.H.Rel a x.ms) :
    (∀ v, x.delCursorWitness.ms.st.supCur v ≤ (x.H.A.C.supportArray v).length) ∧
      (∀ q, x.delCursorWitness.ms.st.pairCur q ≤ (x.H.A.pairConns q).length) := by
  constructor
  · intro v
    change (if v < x.ms.abs.G.n then x.ms.st.supCur v else 0) ≤ _
    split
    · rename_i hv
      exact (h.inv.supCur v hv).1
    · exact Nat.zero_le _
  · intro q
    change (if q < x.H.A.numPairs then x.ms.st.pairCur q else 0) ≤ _
    split
    · rename_i hq
      exact (h.inv.pairCur q hq).1
    · exact Nat.zero_le _

end MinCostFlow.HierPaths

end
