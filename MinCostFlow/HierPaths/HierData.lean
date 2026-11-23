module

public import MinCostFlow.HierPaths.Groups
public import MinCostFlow.ExpanderDecomp.Embedding

/-!
# The data of the static hierarchy

The initialization of the path data structure builds, over the groups of `HierPaths/Groups.lean`,
the following data:

* for every group of size above one, a *host* graph on its members (at the root, the host of
  `lemma_2`);
* for every child of size above one, an embedding of its host into the host of its parent: each
  edge of the child host goes to an edge-number walk of the parent host;
* for every two different children `c < c'` of a group, a list of *connectors*: a perfect
  matching between the members of `c` and those of `c'`, each pair `(y, z)` with an edge-number
  walk from `y` to `z` in the host of the parent.

The vertices of every host are terminal numbers, so a host of group `g` at depth `j` has its edges
inside `members x b j g`. This file fixes the shape of the data (`HierData`), the conditions that
make it a hierarchy (`HierData.IsValid`), and the numbers per depth that bound it
(`HierData.Bounds`): every local walk at depth `j` has at most `d j` edges, the embeddings of all
children of a group put load at most `ρ j` on each host edge, and the connector walks of one pair
of children put load at most `κ j` on each host edge. Loads count occurrences (`List.count`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The output of the static construction of the hierarchy. Depths and groups are those of
`HierPaths/Groups.lean`. -/
structure HierData where
  /-- The host graph of group `g` at depth `j`; its vertices are terminal numbers. -/
  host : ℕ → ℕ → Graph
  /-- `emb j c e` is the walk in the host of the parent (at depth `j`) of group `c` at depth
  `j + 1`, for edge `e` of the host of `c`. -/
  emb : ℕ → ℕ → ℕ → List ℕ
  /-- `conn j c c'` lists the connectors between the groups `c < c'` at depth `j + 1`, children
  of one group at depth `j`: each is `(y, z, walk)` with `y` in `c`, `z` in `c'`, and `walk` an
  edge-number walk from `y` to `z` in the host of the parent. -/
  conn : ℕ → ℕ → ℕ → List (ℕ × ℕ × List ℕ)

namespace HierData

variable (x b : ℕ) (H : HierData)

/-- The list is a perfect matching from the members of group `c` to those of group `c'` at depth
`j`: its first entries are the members of `c` without repetition, its second entries those of
`c'`. -/
def IsPerfectOn (j c c' : ℕ) (l : List (ℕ × ℕ × List ℕ)) : Prop :=
  (l.map Prod.fst).Nodup ∧ (l.map Prod.fst).toFinset = members x b j c ∧
    (l.map fun q => q.2.1).Nodup ∧ (l.map fun q => q.2.1).toFinset = members x b j c'

/-- The data form a hierarchy: hosts have their edges inside their groups, child hosts embed into
parent hosts, and connectors are perfect matchings with walks in the parent host. -/
structure IsValid : Prop where
  /-- Every edge of the host of a group of size above one has both ends in the group. -/
  host_inside : ∀ j g, 1 < groupSize x b j → g < numGroups x b j →
    ∀ i < (H.host j g).m, insideB (members x b j g) (edgeAt (H.host j g).edges i) = true
  /-- The host of a child of size above one embeds into the host of its parent. -/
  emb_ok : ∀ j c, 1 < groupSize x b (j + 1) → c < numGroups x b (j + 1) →
    IsEmbeddingOn (H.host (j + 1) c) (H.host j (parentGroup x b j c))
      (members x b j (parentGroup x b j c)) (H.emb j c)
  /-- Between two children `c < c'` of a group of size above one, the connectors form a perfect
  matching, with walks in the parent host. -/
  conn_perfect : ∀ j g, 1 < groupSize x b j → g < numGroups x b j →
    ∀ c ∈ childGroups x b j g, ∀ c' ∈ childGroups x b j g, c < c' →
      IsPerfectOn x b (j + 1) c c' (H.conn j c c')
  /-- Every connector walk is a walk of the parent host between the two matched terminals. -/
  conn_walk : ∀ j g, 1 < groupSize x b j → g < numGroups x b j →
    ∀ c ∈ childGroups x b j g, ∀ c' ∈ childGroups x b j g, c < c' →
      ∀ q ∈ H.conn j c c', IsEdgeWalk (H.host j g).edges q.1 q.2.1 q.2.2

/-- The numbers per depth that bound the hierarchy: walks at depth `j` (in hosts at depth `j`)
have at most `d j` edges; all child embeddings at a group at depth `j` together have load at most
`ρ j` on each host edge; the connector walks of one pair of children have load at most `κ j` on
each host edge. -/
structure Bounds (d ρ κ : ℕ → ℕ) : Prop where
  /-- Embedding walks into a host at depth `j` have at most `d j` edges. -/
  emb_length : ∀ j c, 1 < groupSize x b (j + 1) → c < numGroups x b (j + 1) →
    ∀ e < (H.host (j + 1) c).m, (H.emb j c e).length ≤ d j
  /-- Connector walks in a host at depth `j` have at most `d j` edges. -/
  conn_length : ∀ j g, 1 < groupSize x b j → g < numGroups x b j →
    ∀ c ∈ childGroups x b j g, ∀ c' ∈ childGroups x b j g, c < c' →
      ∀ q ∈ H.conn j c c', q.2.2.length ≤ d j
  /-- All child embeddings at a group at depth `j` put load at most `ρ j` on each host edge. -/
  emb_load : ∀ j g, 1 < groupSize x b (j + 1) → g < numGroups x b j →
    ∀ i < (H.host j g).m,
      ∑ c ∈ childGroups x b j g, ∑ e ∈ Finset.range (H.host (j + 1) c).m,
        (H.emb j c e).count i ≤ ρ j
  /-- The connectors of one pair of children at a group at depth `j` put load at most `κ j` on
  each host edge. -/
  conn_load : ∀ j g, 1 < groupSize x b j → g < numGroups x b j →
    ∀ c ∈ childGroups x b j g, ∀ c' ∈ childGroups x b j g, c < c' →
      ∀ i < (H.host j g).m, ((H.conn j c c').map fun q => q.2.2.count i).sum ≤ κ j

end HierData

end MinCostFlow.HierPaths
