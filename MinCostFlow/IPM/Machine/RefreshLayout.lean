module

public import MinCostFlow.IPM.Machine.MinRatioContract
public import MinCostFlow.IPM.EdgeRefresh

/-!
# Serializing coefficient changes on the fixed graph

Definition 4.5 (page 14) refreshes a coefficient through graph updates.
The fixed-graph encoding from Algorithm 7 of Chen et al.,
arXiv:2203.00671v2 (page 69), deletes and reinserts each changed edge.
Each pair occupies six machine words after the batch's update count.
These lemmas identify that layout with the existing model batch and
prove the exact refresh condition required by the machine interface.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The six words of one delete/reinsert pair, without a batch header. -/
theorem refreshEdge_words (G : MGraph) (e : ℕ) :
    (refreshEdge G e).flatMap updateWords=[1,e,0,e,G.tail e,G.head e] := by
  rfl

private theorem refreshEdges_length (G : MGraph) (es : List ℕ) :
    (refreshEdges G es).length=2*es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [refreshEdges,List.length_append,refreshEdge,List.length_cons,List.length_nil,ih]
    omega

private theorem refreshEdges_flatMap (G : MGraph) (es : List ℕ) :
    (refreshEdges G es).flatMap updateWords=
      es.flatMap (fun e => [1,e,0,e,G.tail e,G.head e]) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [refreshEdges,List.flatMap_append,refreshEdge_words,List.flatMap_cons,ih]

/-- The batch header counts primitive updates, two for each changed edge.
The body is a sequence of six-word delete/reinsert records. -/
theorem batchWords_refreshEdges (G : MGraph) (es : List ℕ) :
    batchWords (refreshEdges G es)=
      (2*es.length)::es.flatMap (fun e => [1,e,0,e,G.tail e,G.head e]) := by
  simp only [batchWords,refreshEdges_length,refreshEdges_flatMap]

/-- The exact model batch meets every clause of the machine interface's
fixed-graph refresh predicate. Repeated edge names are also permitted:
each delete/reinsert pair restores the graph before the next pair. -/
theorem refreshEdges_isRefreshBatch (G : MGraph) (hG : G.IsValid) (es : List ℕ)
    (hes : ∀ e ∈ es,e ∈ G.E) : RefreshBatch G (refreshEdges G es) := by
  have hh := refreshEdges_spec G hG es hes
  refine ⟨hh.1,hh.2.1,?_⟩
  clear hh
  induction es with
  | nil => intro u hu; exact False.elim (List.not_mem_nil hu)
  | cons e es ih =>
    have he := hes e List.mem_cons_self
    have ht := ih (fun j hj => hes j (List.mem_cons_of_mem _ hj))
    intro u hu
    simp only [refreshEdges,List.mem_append,refreshEdge,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with (rfl | rfl) | hu
    · exact he
    · exact ⟨he,rfl,rfl⟩
    · exact ht u hu

end MinCostFlow.IPM.Machine
