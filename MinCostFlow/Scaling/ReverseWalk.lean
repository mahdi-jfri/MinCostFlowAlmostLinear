module

public import MinCostFlow.Scaling.DirectedWalk
import Mathlib.Tactic.Ring

/-!
# Directed walks stored as edge stacks

The negative-cycle extraction used in Lemma C.10 of Chen et al.,
arXiv:2203.00671v2, Appendix C, pushes the newest edge onto a stack and pops
edges from the end of the directed walk. The walk representation here adds
edges at their heads, matching that integer stack exactly. Conversion to
ordinary directed walks preserves the cost and every edge count.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- A directed walk stored with its last edge first. -/
inductive ReverseWalk (I : Circulation) : Fin I.n → Fin I.n → Type
  | nil (v : Fin I.n) : ReverseWalk I v v
  | snoc (e : Fin I.m) (active : 0 < I.capacity e) {v : Fin I.n}
      (rest : ReverseWalk I v (I.tail e)) : ReverseWalk I v (I.head e)

namespace ReverseWalk
variable {I : Circulation}

/-- The integer stack, most recent edge first. -/
def edges {a b : Fin I.n} : I.ReverseWalk a b → List (Fin I.m)
  | .nil _ => []
  | .snoc e _ p => e :: p.edges

/-- Visited vertices, endpoint first. -/
def vertices {a b : Fin I.n} : I.ReverseWalk a b → List (Fin I.n)
  | .nil v => [v]
  | .snoc e _ p => I.head e :: p.vertices

/-- The integral cost of a stack walk. -/
def cost {a b : Fin I.n} : I.ReverseWalk a b → ℤ
  | .nil _ => 0
  | .snoc e _ p => I.cost e + p.cost

/-- Number of occurrences of one edge in the stack walk. -/
def count {a b : Fin I.n} : I.ReverseWalk a b → Fin I.m → ℕ
  | .nil _, _ => 0
  | .snoc e _ p, k => (if k = e then 1 else 0) + p.count k

/-- Interpret a stack walk as an ordinary directed walk. -/
def toDirectedWalk {a b : Fin I.n} : I.ReverseWalk a b → I.DirectedWalk a b
  | .nil v => .nil v
  | .snoc e he p => p.toDirectedWalk.append (.cons e he (.nil (I.head e)))

/-- The endpoint is the first recorded vertex. -/
theorem end_mem_vertices {a b : Fin I.n} (p : I.ReverseWalk a b) : b ∈ p.vertices := by
  cases p <;> exact List.mem_cons_self

/-- The start vertex remains in the visited list. -/
theorem start_mem_vertices {a b : Fin I.n} (p : I.ReverseWalk a b) : a ∈ p.vertices := by
  induction p with
  | nil => exact List.mem_cons_self
  | snoc e he p ih => exact List.mem_cons_of_mem _ ih

/-- Stack interpretation preserves the integral cost. -/
theorem cost_toDirectedWalk {a b : Fin I.n} (p : I.ReverseWalk a b) :
    p.toDirectedWalk.cost = p.cost := by
  induction p with
  | nil => rfl
  | snoc e he p ih =>
    simp only [toDirectedWalk, DirectedWalk.cost_append, DirectedWalk.cost, ih, add_zero, cost]
    exact add_comm _ _

/-- Counts add when ordinary directed walks are concatenated. -/
theorem _root_.MinCostFlow.Scaling.Circulation.DirectedWalk.count_append
    {I : Circulation} {a b c : Fin I.n} (p : I.DirectedWalk a b) (q : I.DirectedWalk b c)
    (e : Fin I.m) : (p.append q).count e = p.count e + q.count e := by
  induction p with
  | nil => simp only [DirectedWalk.append, DirectedWalk.count, zero_add]
  | cons k hk p ih => simp only [DirectedWalk.append, DirectedWalk.count, ih, Nat.add_assoc]

/-- Stack interpretation preserves all edge counts. -/
theorem count_toDirectedWalk {a b : Fin I.n} (p : I.ReverseWalk a b) (e : Fin I.m) :
    p.toDirectedWalk.count e = p.count e := by
  induction p with
  | nil => rfl
  | snoc k hk p ih =>
    simp only [toDirectedWalk, DirectedWalk.count_append, DirectedWalk.count, ih, count, Nat.add_zero]
    exact Nat.add_comm _ _

end ReverseWalk
end MinCostFlow.Scaling.Circulation
