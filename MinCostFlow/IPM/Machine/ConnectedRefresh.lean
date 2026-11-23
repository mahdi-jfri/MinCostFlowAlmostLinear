module

public import MinCostFlow.IPM.ConnectedInitialConstruction
public import MinCostFlow.IPM.Machine.RefreshLayout

/-!
# Connectivity between data structure calls

Definition 4.5 (page 14) applies each Update as a batch. The IPM
refreshes coefficients by deleting and reinserting edges in the same
batch. At every completed call the graph is the initial graph.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- A sequence of complete coefficient refreshes preserves the connected
augmented graph, including its edge names and endpoints. -/
theorem connectedInitial_refreshes (I : Instance) (K : ℤ) (hI : I.IsValid)
    (batches : List (List ℕ))
    (he : ∀ es ∈ batches, ∀ e ∈ es, e ∈ (namedInstance (connectedInitialInstance I K)).E) :
    let G := namedInstance (connectedInitialInstance I K)
    let H := batches.foldl (fun H es => H.applyBatch (refreshEdges G es)) G
    H = G ∧ ∀ u ∈ H.V, ∀ v ∈ H.V, H.Connected u v := by
  let G := namedInstance (connectedInitialInstance I K)
  have hG := namedInstance_valid _ (connectedInitialInstance_valid I K hI)
  have hsame : batches.foldl (fun H es => H.applyBatch (refreshEdges G es)) G = G := by
    induction batches with
    | nil => rfl
    | cons es batches ih =>
      rw [List.foldl_cons, (refreshEdges_isRefreshBatch G hG es (he es List.mem_cons_self)).2.1]
      exact ih (fun fs hfs => he fs (List.mem_cons_of_mem _ hfs))
  exact ⟨hsame, hsame.symm ▸ connectedInitialInstance_connected I K⟩

end MinCostFlow.IPM.Machine
