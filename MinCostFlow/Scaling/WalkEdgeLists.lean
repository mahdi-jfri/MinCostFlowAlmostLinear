module

public import MinCostFlow.Scaling.SupportCycle
public import MinCostFlow.Scaling.ReverseWalkProperties

/-!
# Forward and reverse edge lists of directed walks

The stack and saved closed part in Lemma C.10's negative-cycle scan,
Chen et al., arXiv:2203.00671v2, Appendix C, store opposite edge orders.
This file gives the ordinary forward edge list and proves its count and
cost identities. Conversion of a stack walk reverses its concrete list.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.DirectedWalk
variable {I : Circulation} {a b c : Fin I.n}

/-- Directed edges in traversal order. -/
def edges {a b : Fin I.n} : I.DirectedWalk a b → List (Fin I.m)
  | .nil _ => []
  | .cons e _ p => e :: p.edges

/-- The concrete list and walk have the same edge counts. -/
theorem count_edges (p : I.DirectedWalk a b) (e : Fin I.m) : p.edges.count e = p.count e := by
  induction p with
  | nil => rfl
  | cons k hk p ih =>
    simp only [edges, List.count_cons, beq_iff_eq, ih, count]
    by_cases he : e = k <;> simp only [he, eq_comm, ↓reduceIte] <;> omega

/-- The concrete list and walk have the same cost. -/
theorem sum_cost_edges (p : I.DirectedWalk a b) : (p.edges.map I.cost).sum = p.cost := by
  induction p with
  | nil => rfl
  | cons e he p ih => simp only [edges, List.map_cons, List.sum_cons, ih, cost]

/-- Concatenating walks concatenates their edge lists in traversal order. -/
theorem edges_append (p : I.DirectedWalk a b) (q : I.DirectedWalk b c) :
    (p.append q).edges = p.edges ++ q.edges := by
  induction p with
  | nil => rfl
  | cons e he p ih => simp only [append, edges, ih, List.cons_append]

end MinCostFlow.Scaling.Circulation.DirectedWalk

namespace MinCostFlow.Scaling.Circulation.ReverseWalk
variable {I : Circulation} {a b : Fin I.n}

/-- A stack walk's interpretation lists its edges in the reverse stack order. -/
theorem edges_toDirectedWalk (p : I.ReverseWalk a b) :
    p.toDirectedWalk.edges = p.edges.reverse := by
  induction p with
  | nil => rfl
  | snoc e he p ih =>
    simp only [toDirectedWalk, DirectedWalk.edges_append, DirectedWalk.edges,
      ih, edges, List.reverse_cons]

/-- The stack edge list is duplicate-free when the path has no repeated vertex. -/
theorem edges_nodup_of_vertices_nodup (p : I.ReverseWalk a b) (hp : p.vertices.Nodup) :
    p.edges.Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro e
  rw [p.count_edges]
  exact p.count_le_one_of_nodup hp e

end MinCostFlow.Scaling.Circulation.ReverseWalk
