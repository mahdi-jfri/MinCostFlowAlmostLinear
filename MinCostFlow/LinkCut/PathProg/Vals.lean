module

public import MinCostFlow.LinkCut.PathTree.FindCorrect
public import MinCostFlow.LinkCut.ForestModelSplice
public import MinCostFlow.MinRatio.PathTreeExpose

/-!
# Only edges hold values, after every operation

Find-ready needs that vertices hold no value (`ValsOnEdges`). The model specifications describe
each operation by its evaluated pairs, so this file works with pairs. An evaluated pair holds no
value exactly when the node stores none (`evalPairs_none_stored`). So a state has values only on
edges exactly when its pairs at vertices hold none (`pairsVE_of_vals`, `vals_of_pairsVE`). Each
operation keeps the pairs at vertices: an expose permutes the pairs, a reroot reverses some
values, a path update shifts some, a link adds a pair at an edge slot, a cut removes one, and a
point write changes the pair at an edge slot.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.PathTree

/-- An evaluated pair holds no value only if the node stores none. -/
theorem evalPairs_none_stored (s : SplayState (Option PathEdgeValue) PathSummary PathTag) :
    ∀ (t : AuxTree) (flip : Bool) (acc : PathTag) {y : ℕ},
      (y, none) ∈ SplayState.evalPairs pathPayload s t flip acc → (s.nodes y).val = none
  | .leaf, _, _, _, h => by simp [SplayState.evalPairs] at h
  | .node id l r, flip, acc, y, h => by
    simp only [SplayState.evalPairs] at h
    split_ifs at h <;>
    · simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at h
      rcases h with (h | ⟨rfl, hv⟩) | h
      · exact evalPairs_none_stored s _ _ _ h
      · cases hval : (s.nodes y).val with
        | none => rfl
        | some e => simp [hval, pathPayload] at hv
      · exact evalPairs_none_stored s _ _ _ h

/-- The pairs at vertices hold no value. -/
def PairsVE (n : ℕ) (ps : List (ℕ × Option PathEdgeValue)) : Prop :=
  ∀ p ∈ ps, isVertex n p.1 → p.2 = none

theorem pairsVE_of_vals {s : PathTreeState} (hE : ValsOnEdges s) (ts : List AuxTree) :
    PairsVE s.n (forestPairs pathPayload s.splay ts) := by
  rintro ⟨x, e⟩ hp hx
  cases e with
  | none => rfl
  | some v =>
    obtain ⟨t, -, hpt⟩ := List.mem_flatMap.mp hp
    exact absurd (hE x hx) (evalPairs_some_stored s.splay t false _ hpt)

theorem vals_of_pairsVE {s : PathTreeState} {trees : List AuxTree} {free : List ℕ}
    {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth)
    (h : PairsVE s.n (forestPairs pathPayload s.splay trees)) : ValsOnEdges s := by
  intro x hx
  have hxa := isVertex_mem_active W hx
  have hm : x ∈ (forestPairs pathPayload s.splay trees).map Prod.fst :=
    (forestPairs_fst_perm s.splay trees).symm.subset hxa
  obtain ⟨⟨y, e⟩, hp, rfl⟩ := List.mem_map.mp hm
  have he := h _ hp hx
  simp only at he
  subst he
  obtain ⟨t, -, hpt⟩ := List.mem_flatMap.mp hp
  exact evalPairs_none_stored s.splay t false _ hpt

theorem PairsVE.perm {n : ℕ} {ps qs : List (ℕ × Option PathEdgeValue)} (h : PairsVE n qs)
    (hp : ps.Perm qs) : PairsVE n ps := fun p hm => h p (hp.subset hm)

theorem PairsVE.subset {n : ℕ} {ps qs : List (ℕ × Option PathEdgeValue)} (h : PairsVE n qs)
    (hp : ps ⊆ qs) : PairsVE n ps := fun p hm => h p (hp hm)

/-! ### The operations -/

theorem vals_expose {s : PathTreeState} {trees : List AuxTree} {free : List ℕ}
    {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth) (hE : ValsOnEdges s)
    {v : ℕ} (hv : v ∈ trees.flatMap AuxTree.toList) :
    ValsOnEdges (lctExpose pathPayload s v) := by
  obtain ⟨tv, htv, hvt⟩ := List.mem_flatMap.mp hv
  obtain ⟨trees', Lv, -, W', -, -, hpairs, -⟩ := lctExpose_spec pathPayload_laws W htv hvt
  exact vals_of_pairsVE W' ((pairsVE_of_vals hE trees).perm hpairs)

theorem vals_reroot {s : PathTreeState} {trees : List AuxTree} {free : List ℕ}
    {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth) (hE : ValsOnEdges s)
    {v : ℕ} (hv : isVertex s.n v) :
    ValsOnEdges (lctReroot pathPayload s v) := by
  obtain ⟨tv, htv, hvt⟩ := List.mem_flatMap.mp (isVertex_mem_active W hv)
  obtain ⟨trees', L, d', -, W', -, -, -, -, -, -, -, hsplit, hfp, -⟩ :=
    lctReroot_spec pathPayload_laws W htv hvt hv
  refine vals_of_pairsVE W' fun p hp hx => ?_
  have hp' := hfp.mem_iff.mp hp
  have hold := pairsVE_of_vals hE trees
  rcases List.mem_append.mp hp' with hp' | hp'
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hp')
    have := hold q (hsplit.mem_iff.mp (List.mem_append_left _ hq)) hx
    simp [this, pathPayload]
  · exact hold p (hsplit.mem_iff.mp (List.mem_append_right _ hp')) hx

end MinCostFlow.LinkCut.PathProg
