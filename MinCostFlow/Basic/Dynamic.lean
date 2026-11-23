module

public import MinCostFlow.Basic.Graph

/-!
# Dynamic graphs (Section 2)

Section 2 (pages 5–6):

> In this paper, we say that `G` is a dynamic graph if it undergoes a sequence of updates. In this
> paper, the graphs we study will undergo three main types of updates.
> * **Edge insertion**: an edge `e = (u, v)` is added to the graph. The edge is encoded by its
>   endpoints, and when necessary, edge lengths and gradients will also be provided.
> * **Edge deletion**: an edge `e = (u, v)` is deleted from the graph. The edge is encoded by its
>   label in the graph.
> * **Vertex split**: a vertex `v` becomes two vertices `v_1` and `v_2`, and the edges adjacent to
>   `v` are split between `v_1` and `v_2`. Precisely, every edge `e_i = (v, u_i)` is assigned to
>   either `v_1` or `v_2`, becoming edge `(v_1, u_i)` or `(v_2, u_i)` respectively. This operation
>   is encoded by listing out the edges moved to the one of `v_1, v_2` with a smaller degree. Thus
>   the encoding size is approximately `min{deg(v_1), deg(v_2)}`.
>
> In this paper, instead of having our dynamic graphs undergo a single update at a time, we think
> of them as undergoing *batches* `U^{(1)}, U^{(2)}, …` of updates, where each batch `U^{(i)}`
> denotes a set of updates to apply. We let `|U^{(t)}|` denote the total number of updates in the
> batch, i.e., the total number of edge insertions, deletions, and vertex splits. `Enc(u)` of an
> update `u ∈ U^{(t)}` denotes its encoding size. […] the encoding size of a batch `U^{(t)}` is
> the sum of the encoding sizes of each of its updates.

How the definitions read it:

* An insertion names the new edge, its tail and its head; the name must not be an edge of the
  graph. A deletion names an edge of the graph.
* A split of `v` names the new vertex `v'` (not a vertex of the graph) and two edge sets `St`, `Sh`:
  the tails at `v` of edges in `St` move to `v'`, and the heads at `v` of edges in `Sh` move to
  `v'`. Moving the two ends separately means a self-loop `e = (v, v)` may become an edge
  `(v, v')` or `(v', v)` (when `e` lies in only one of `St`, `Sh`), as needed when splitting
  core-graph vertices in Lemma 5.14; taking `St = Sh` moves both ends together. Its encoding size
  is `min{deg(v_1), deg(v_2)} + 1`, the degrees after the split (counting ends, so a loop adds `2`);
  the `+ 1` (the names `v`, `v'`) makes every update cost at least `1`, as `Enc(U^{(t)}) =
  Ω(|U^{(t)}|)` on page 6 requires.
* A batch is a list of updates, applied in order.
-/

@[expose] public section

namespace MinCostFlow

/-- An update of a dynamic graph (Section 2, page 5). -/
inductive Update
  /-- Insert the edge `e = (u, v)`. -/
  | insert (e u v : ℕ)
  /-- Delete the edge `e`. -/
  | delete (e : ℕ)
  /-- Split `v`: `v'` receives the tails at `v` of edges in `St` and the heads at `v` of edges
  in `Sh`. -/
  | split (v v' : ℕ) (St Sh : Finset ℕ)

namespace MGraph

variable (G : MGraph)

/-- The graph after one update. -/
def applyUpdate : Update → MGraph
  | .insert e u v =>
    { G with E := insert e G.E, tail := Function.update G.tail e u,
             head := Function.update G.head e v }
  | .delete e => { G with E := G.E.erase e }
  | .split v v' St Sh =>
    { V := insert v' G.V, E := G.E,
      tail := fun e => if e ∈ St ∧ G.tail e = v then v' else G.tail e,
      head := fun e => if e ∈ Sh ∧ G.head e = v then v' else G.head e }

/-- The update can be applied to `G`: an inserted edge is new and its ends are vertices, a deleted
edge is an edge, and a split vertex is a vertex, the new vertex is new, and the moved edges are
edges at the split vertex. -/
def UpdateIsValid : Update → Prop
  | .insert e u v => e ∉ G.E ∧ u ∈ G.V ∧ v ∈ G.V
  | .delete e => e ∈ G.E
  | .split v v' St Sh =>
    v ∈ G.V ∧ v' ∉ G.V ∧ St ∪ Sh ⊆ G.E ∧ ∀ e ∈ St ∪ Sh, G.tail e = v ∨ G.head e = v

/-- The encoding size `Enc(u)` of an update of `G`: `1` for an insertion or a deletion, and
`min{deg(v_1), deg(v_2)} + 1` for a split, with the degrees after the split. -/
def updateEnc : Update → ℕ
  | .insert _ _ _ => 1
  | .delete _ => 1
  | .split v v' St Sh =>
    let G' := G.applyUpdate (.split v v' St Sh)
    min (G'.deg v) (G'.deg v') + 1

/-- The graph after a batch of updates, applied in order. -/
def applyBatch (U : List Update) : MGraph :=
  U.foldl applyUpdate G

/-- Every update of the batch can be applied when its turn comes. -/
def BatchIsValid : MGraph → List Update → Prop
  | _, [] => True
  | G, u :: U => G.UpdateIsValid u ∧ (G.applyUpdate u).BatchIsValid U

/-- The encoding size `Enc(U)` of a batch: the sum of the encoding sizes of its updates, each
taken in the graph it applies to. -/
def batchEnc : MGraph → List Update → ℕ
  | _, [] => 0
  | G, u :: U => G.updateEnc u + (G.applyUpdate u).batchEnc U

end MGraph

/-- `u` inserts the edge `e`. -/
def Update.Inserts (e : ℕ) : Update → Prop
  | .insert e' _ _ => e' = e
  | _ => False

end MinCostFlow
