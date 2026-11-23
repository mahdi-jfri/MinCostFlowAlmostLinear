module

public import MinCostFlow.HierPaths.BuildProgTags
public import MinCostFlow.ExpanderDecomp.OuterProgContracts

/-!
# Reading the sets and walks returned by the players

The caller reads a core set as a list and can access any individual matching or walk
directly through the router's offsets. It can thus consume each matching in its own
child without scanning the other children's matchings.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- A core reply stores its member list immediately after the tag. The last offset
leaves the length of this list available without a scan. -/
theorem coreSet_view {mem : ℕ → ℕ} {h tag : ℕ} {U : Finset ℕ}
    (hAt : ListAt mem h (layoutList [[tag], finsetWords U])) :
    ListAt mem (h + 4) (finsetWords U) ∧ mem (h + 2) = 1 + U.card := by
  have hSet := listAt_csrList_get hAt (i := 1) (by simp)
  refine ⟨hSet, ?_⟩
  simpa [List.range_succ, finsetWords] using (csrList_offset hAt (i := 2) (by simp))

/-- The two payload bases of a successful batch reply. -/
theorem routeMatched_view {mem : ℕ → ℕ} {h : ℕ} {Ms : List (List (ℕ × ℕ))}
    {emb : ℕ → List ℕ} (hAt : ListAt mem h (routeResultWords (.matched Ms emb))) :
    ListAt mem (h + 4 + mem (h + 1))
      (csrList Ms.length (fun i => (Ms.getD i []).flatMap fun e => [e.1, e.2])) ∧
    ListAt mem (h + 4 + mem (h + 2)) (csrList Ms.flatten.length emb) := by
  exact ⟨listAt_section hAt (i := 1) (by simp), listAt_section hAt (i := 2) (by simp)⟩

/-- The decomposition router's current output relation contains the matching endpoints.
It gives the same memory condition for every assignment of walks to those endpoints. -/
theorem routeOutAt_walks_irrel (mem : ℕ → ℕ) (out : ℕ)
    (Ms : List (List (ℕ × ℕ))) (emb emb' : ℕ → List ℕ) :
    RouteOutAt mem out (.matched Ms emb) ↔ RouteOutAt mem out (.matched Ms emb') := Iff.rfl

end MinCostFlow.HierPaths
