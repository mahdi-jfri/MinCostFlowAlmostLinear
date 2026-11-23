module

public import MinCostFlow.SparseCore.Program.RestartModelState
public import MinCostFlow.SparseCore.BundleTreeCore

import Mathlib.Tactic

/-!
# The model facts between the phases of the first step (`AssemblyFirstStepDriverModel`)

The first step of a branch runs four phases one after the other. Phase 1 scans the batch and
lists the components that the batch touches and that were not active, Phase 2 activates them,
and Phases 3 and 4 read the state that Phase 2 leaves. Phase 2 states its result for the state
`tr_mid`, which is `tr` with these components added to the active ones. This file shows that
`tr_mid` has the active pairs of the new state of the step (`activePairs_mid_eq`), so that the
later phases, which speak of the new state, can use what Phase 2 leaves.

* `newSet_eq_newlyActive`: the components that Phase 1 lists are exactly the components that the
  step newly activates (`touchedCompsBatch \ activeComps`).
* `activePairs_mid_eq`: with these components, `tr_mid` and the new state have the same active
  pairs.
* `touchedCompsBatch_subset`: every component that the batch touches is a component of the
  initial graph.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.SparseCore.Program.Restart

public section

/-- **The components that Phase 1 lists.** Phase 1 lists pairs `(c, v)`: the index `c` of a
component in the list `comps` and a vertex `v` of it. If the indices it lists are exactly those
of the components in `T \ A`, and every component of `T` is in the list, then the components it
lists are `T \ A`. -/
theorem newSet_eq_newlyActive {comps : List (Finset ℕ)} {newComps : List (ℕ × ℕ)}
    {T A : Finset (Finset ℕ)}
    (hlt : ∀ q ∈ newComps, q.1 < comps.length)
    (hiff : ∀ c (hc : c < comps.length), c ∈ newComps.map Prod.fst ↔ comps[c] ∈ T \ A)
    (hT : ∀ C ∈ T, C ∈ comps) :
    (newComps.map fun q => comps.getD q.1 ∅).toFinset = T \ A := by
  ext C
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hc := hlt q hq
    rw [List.getD_eq_getElem _ _ hc]
    exact (hiff q.1 hc).mp (List.mem_map.mpr ⟨q, hq, rfl⟩)
  · intro hC
    obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.mp (hT C (Finset.mem_sdiff.mp hC).1)
    obtain ⟨q, hq, hqc⟩ := List.mem_map.mp ((hiff c hc).mpr hC)
    refine ⟨q, hq, ?_⟩
    rw [hqc, List.getD_eq_getElem _ _ hc]

/-- **The state after Phase 2 has the active pairs of the new state.** The new state of the step
keeps the active buckets and adds the newly activated components to the active ones; so does
`tr_mid` when its new components are the newly activated ones. -/
theorem activePairs_mid_eq {L : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    {newSet : Finset (Finset ℕ)}
    (hnew : newSet = touchedCompsBatch tr.cs U \ tr.activeComps) :
    activePairs { tr with activeComps := tr.activeComps ∪ newSet } =
      activePairs (stepBundleTree sparsify tr U ord ord').state := by
  ext q
  rw [mem_activePairs, mem_activePairs, hnew]
  rfl

/-- Every component that the batch touches is a component of the initial graph. -/
theorem touchedCompsBatch_subset (cs : CompLSFState) (U : List Update) :
    touchedCompsBatch cs U ⊆ components cs.G₀ := by
  classical
  intro C hC
  unfold touchedCompsBatch at hC
  exact (Finset.mem_filter.mp hC).1

end

end MinCostFlow.SparseCore.Program
