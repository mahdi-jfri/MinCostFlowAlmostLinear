module

public import MinCostFlow.SparseCore.Program.AssemblyStatement

/-!
# The orders that the order store receives

The order store (piece P1, `ordStoreCapContract`) asks two things of the orders it receives. At
the initialization the order must have every end in at most one list, within the capacities
(`OrdUniqueWithin`). At an update every prefix of the edits must keep this (`OrdEditsUniqueWithin`).

* `ordUniqueWithin_of_rotation`: the order of a rotation of a valid graph whose vertices are below
  `vCap` and whose edges are below `eCap` has this property. An end `x` lies only in the list of
  its source vertex, the source is a vertex of the graph since the graph is valid, and each list
  has no repeated end. So the initialization of the sparse-core program can pass its input order to
  the order store as it is.
* `not_ordEditsUniqueWithin_of_orderedBatch`: the precondition of an update of the sparse-core
  contract does not give the condition on the edits. It speaks of the edits only through the order
  they produce. On the graph with one vertex and no edge, the edits that insert the end `(0, tail)`
  twice and then drop edge `0` produce the order they start from, so the empty batch is ordered
  from it to the result. But after two edits the list at vertex `0` repeats an end. This is why
  `sparseCoreOrdMachineContractKF` asks for `OrdEditsValidFor` in the precondition of an update.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle

/-- The order of a rotation of a valid graph, with vertices below `vCap` and edges below `eCap`, has
every end in at most one list and stays within the capacities. -/
theorem ordUniqueWithin_of_rotation {G : MGraph} {vCap eCap : ℕ} {ord : ℕ → List End}
    (hG : G.IsValid) (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap)
    (hrot : IsRotationOrder G ord) : OrdUniqueWithin vCap eCap ord := by
  obtain ⟨ρ, rfl⟩ := hrot
  have hsrc : ∀ x : End, x.1 ∈ G.E → G.src x < vCap := by
    intro x hx
    apply hV
    unfold MGraph.src
    split
    · exact (hG x.1 hx).1
    · exact (hG x.1 hx).2
  refine ⟨⟨ρ.nodup, fun v hv => ?_, fun v x hx => hE x.1 ((ρ.mem_order v x).mp hx).1⟩,
    fun u v x hu hv => ?_⟩
  · rcases hnil : ρ.order v with _ | ⟨x, xs⟩
    · rfl
    · have hx : x ∈ ρ.order v := by rw [hnil]; exact List.mem_cons_self
      obtain ⟨hxE, hxv⟩ := (ρ.mem_order v x).mp hx
      have := hsrc x hxE
      omega
  · rw [← ((ρ.mem_order u x).mp hu).2, ← ((ρ.mem_order v x).mp hv).2]

/-- The graph with the single vertex `0` and no edge. -/
def oneVertexGraph : MGraph where
  V := {0}
  E := ∅
  tail _ := 0
  head _ := 0

/-- The empty order is the order of a rotation of `oneVertexGraph`. -/
def oneVertexRotation : Rotation oneVertexGraph where
  order _ := []
  nodup _ := List.nodup_nil
  mem_order v x := by simp [oneVertexGraph]

/-- The edits that insert the end `(0, tail)` at vertex `0` twice and then drop edge `0`. -/
def twiceInsertEdits : List OrdEdit :=
  [.insertBefore 0 (0, true) none, .insertBefore 0 (0, true) none, .dropEdge 0]

/-- The edits `twiceInsertEdits` produce the order they start from. -/
theorem applyOrdEdits_twiceInsertEdits :
    applyOrdEdits (fun _ => []) twiceInsertEdits = fun _ => [] := by
  funext u
  by_cases hu : u = 0
  · subst hu
    simp [applyOrdEdits, twiceInsertEdits, applyOrdEdit, insertBeforeList]
  · simp [applyOrdEdits, twiceInsertEdits, applyOrdEdit, insertBeforeList,
      Function.update_of_ne hu]

/-- **The precondition of an update does not give `OrdEditsUniqueWithin`.** On `oneVertexGraph`,
the empty batch is ordered from the empty order to the result of `twiceInsertEdits`, and every edit
is within the capacities `1` and `1`, but after two edits the list at vertex `0` repeats an end. -/
theorem not_ordEditsUniqueWithin_of_orderedBatch :
    OrderedBatch oneVertexGraph [] (fun _ => []) (applyOrdEdits (fun _ => []) twiceInsertEdits) ∧
      OrdEditsWithin 1 1 twiceInsertEdits ∧
      ¬ OrdEditsUniqueWithin 1 1 (fun _ => []) twiceInsertEdits := by
  refine ⟨?_, ?_, ?_⟩
  · rw [applyOrdEdits_twiceInsertEdits]
    exact ⟨oneVertexRotation, oneVertexRotation, rfl, rfl, RotationBatch.refl _⟩
  · intro edit hedit
    simp only [twiceInsertEdits, List.mem_cons, List.not_mem_nil, or_false] at hedit
    rcases hedit with rfl | rfl | rfl <;> simp
  · intro h
    have h2 := (h 2 (by simp [twiceInsertEdits])).nodup 0
    simp [applyOrdEdits, twiceInsertEdits, applyOrdEdit, insertBeforeList] at h2

end MinCostFlow.SparseCore.Program
