module

public import MinCostFlow.Basic.Dynamic
import Lean.Elab.Tactic.Omega

/-!
# Refreshing edge gradients and lengths

Algorithm 7 of Chen et al., arXiv:2203.00671v2 (Section 9, page 69),
changes only gradient and length entries on a fixed graph. To pass these
changes to Definition 4.5 (page 14 of arXiv:2309.16629v1), delete and
reinsert every changed edge with its original endpoints. The graph is
unchanged, each such refresh has encoding size two, and an edge is
explicitly inserted exactly when it was refreshed. Definition 4.4's
`NotInsertedBetween` therefore resets at every refresh. Fresh edge names
are unnecessary for this interface's item 4.
-/

@[expose] public section
namespace MinCostFlow.IPM

/-- A gradient or length refresh is encoded by a deletion and insertion
with unchanged edge name and endpoints. -/
def refreshEdge (G : MGraph) (e : ℕ) : List MinCostFlow.Update :=
  [.delete e, .insert e (G.tail e) (G.head e)]

/-- Refresh a list of edges. Every pair restores the original graph. -/
def refreshEdges (G : MGraph) : List ℕ → List MinCostFlow.Update
  | [] => []
  | e::es => refreshEdge G e ++ refreshEdges G es

/-- Validity of a concatenated update batch splits at its intermediate
graph, as required to combine fixed-graph refreshes. -/
theorem batchIsValid_append (G : MGraph) (us vs : List MinCostFlow.Update) :
    G.BatchIsValid (us++vs) ↔ G.BatchIsValid us ∧ (G.applyBatch us).BatchIsValid vs := by
  induction us generalizing G with
  | nil => simp only [List.nil_append, MGraph.BatchIsValid, MGraph.applyBatch, List.foldl_nil, true_and]
  | cons u us ih =>
    simp only [List.cons_append, MGraph.BatchIsValid, MGraph.applyBatch, List.foldl_cons]
    rw [ih]
    exact and_assoc.symm

/-- Applying concatenated batches agrees with applying them in sequence. -/
theorem applyBatch_append (G : MGraph) (us vs : List MinCostFlow.Update) :
    G.applyBatch (us++vs) = (G.applyBatch us).applyBatch vs := List.foldl_append

/-- A refresh preserves a well-formed graph and is a valid update batch. -/
theorem refreshEdge_spec (G : MGraph) (hG : G.IsValid) (e : ℕ) (he : e ∈ G.E) :
    G.BatchIsValid (refreshEdge G e) ∧ G.applyBatch (refreshEdge G e) = G := by
  constructor
  · simp only [refreshEdge, MGraph.BatchIsValid, MGraph.UpdateIsValid,
      MGraph.applyUpdate, Finset.mem_erase, not_and, and_true]
    exact ⟨he, ⟨fun h => False.elim (h rfl), (hG e he).1, (hG e he).2⟩⟩
  · simp only [refreshEdge, MGraph.applyBatch, List.foldl_cons, List.foldl_nil,
      MGraph.applyUpdate, Finset.insert_erase he, Function.update_eq_self]

/-- Refreshing any list of existing edges preserves the graph, is valid,
and uses exactly two primitive updates per list entry. -/
theorem refreshEdges_spec (G : MGraph) (hG : G.IsValid) (es : List ℕ)
    (hes : ∀ e ∈ es, e ∈ G.E) :
    G.BatchIsValid (refreshEdges G es) ∧ G.applyBatch (refreshEdges G es) = G ∧
      (refreshEdges G es).length = 2*es.length ∧ G.batchEnc (refreshEdges G es) = 2*es.length := by
  induction es with
  | nil => exact ⟨trivial, rfl, rfl, rfl⟩
  | cons e es ih =>
    have he := hes e List.mem_cons_self
    have hs := ih (fun j hj => hes j (List.mem_cons_of_mem _ hj))
    have hone := refreshEdge_spec G hG e he
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [refreshEdges, batchIsValid_append, hone.2]
      exact ⟨hone.1, hs.1⟩
    · rw [refreshEdges, applyBatch_append, hone.2, hs.2.1]
    · simp only [refreshEdges, List.length_append, refreshEdge, List.length_cons,
        List.length_nil, hs.2.2.1]
      omega
    · change 1+(1+((G.applyBatch (refreshEdge G e)).batchEnc (refreshEdges G es))) = 2*(e::es).length
      rw [hone.2, hs.2.2.2]
      simp only [List.length_cons]
      omega

/-- An edge is explicitly inserted by a refresh batch exactly when it
appears in the list of refreshed edges. This is the reset event in item 4
of Definition 4.4. -/
theorem refreshEdges_inserts (G : MGraph) (es : List ℕ) (e : ℕ) :
    (∃ u ∈ refreshEdges G es, u.Inserts e) ↔ e ∈ es := by
  induction es with
  | nil => simp [refreshEdges]
  | cons j es ih =>
    simp only [refreshEdges, List.mem_append, or_and_right, exists_or]
    rw [ih]
    simp [refreshEdge, MinCostFlow.Update.Inserts, eq_comm]

end MinCostFlow.IPM
