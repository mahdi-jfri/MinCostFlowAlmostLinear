module

public import MinCostFlow.Scaling.CycleNormalSteps
public import MinCostFlow.Scaling.StackWalkBalance
import Mathlib.Tactic.Ring

/-!
# Flow and cycle facts for complete scan steps

The proof of the unit-flow extraction in Lemma C.10 of Chen et al.,
arXiv:2203.00671v2, Appendix C, combines exact stack states with conservation
of unused arcs. Removing one outgoing arc moves the positive balance to its
head. Splitting the stack splits its cost, and its closed suffix uses every
edge at most once. Remaining candidate coverage is preserved by deleting an
outgoing-list head.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation
variable {I : Circulation}

/-- Removing an unused outgoing arc moves the endpoint balance to its head. -/
theorem adjacencyFlow_pop_endpoint_balance (out : Fin I.n → List (Fin I.m))
    (root : Fin I.n) (e : Fin I.m) (rest : List (Fin I.m))
    (ho : out (I.tail e) = e :: rest)
    (hb : ∀ v, I.balance (I.adjacencyFlow out) v =
      (if v = I.tail e then 1 else 0) - (if v = root then 1 else 0)) :
    ∀ v, I.balance (I.adjacencyFlow (Function.update out (I.tail e) rest)) v =
      (if v = I.head e then 1 else 0) - (if v = root then 1 else 0) := by
  intro v
  rw [I.adjacencyFlow_pop_balance out (I.tail e) e rest ho rfl, hb]
  simp only [incidence]
  ring

/-- Removing an adjacency head preserves stored-edge properties. -/
theorem outgoing_pop_property (out : Fin I.n → List (Fin I.m))
    (e : Fin I.m) (rest : List (Fin I.m)) (ho : out (I.tail e) = e :: rest)
    (P : Fin I.n → Fin I.m → Prop) (hP : ∀ v a, a ∈ out v → P v a) :
    ∀ v a, a ∈ Function.update out (I.tail e) rest v → P v a := by
  classical
  intro v a ha
  by_cases hv : v = I.tail e
  · subst v
    rw [Function.update_self] at ha
    exact hP _ a (by rw [ho]; exact List.mem_cons_of_mem _ ha)
  · rw [Function.update_of_ne hv] at ha
    exact hP v a ha

/-- Deleting an outgoing-list head preserves the candidate coverage needed
while the same component root is active. -/
theorem outgoing_pop_coverage (out : Fin I.n → List (Fin I.m))
    (e : Fin I.m) (rest : List (Fin I.m)) (ho : out (I.tail e) = e :: rest)
    (root : Fin I.n) (candidates : List (Fin I.m))
    (hc : ∀ v, out v ≠ [] → v = root ∨ ∃ a ∈ candidates, I.tail a = v) :
    ∀ v, Function.update out (I.tail e) rest v ≠ [] →
      v = root ∨ ∃ a ∈ candidates, I.tail a = v := by
  classical
  intro v hv
  apply hc v
  by_cases he : v = I.tail e
  · subst v
    rw [ho]
    exact List.cons_ne_nil _ _
  · simpa only [Function.update_of_ne he] using hv

/-- Splitting a stack's edge list also splits its integral cost. -/
theorem ReverseWalk.cost_eq_of_split {I : Circulation} {root target current : Fin I.n}
    (path : I.ReverseWalk root current) (p : I.ReverseWalk root target)
    (q : I.ReverseWalk target current) (he : path.edges = q.edges ++ p.edges) :
    path.cost = q.cost + p.cost := by
  have hh := congrArg (fun es : List (Fin I.m) => (es.map I.cost).sum) he
  simpa only [List.map_append, List.sum_append, ReverseWalk.sum_cost_edges] using hh

/-- The closed list tested after a repeated vertex is a closed walk with
no repeated edge. -/
theorem ReverseWalk.closed_list_of_suffix {I : Circulation} (e : Fin I.m)
    (he : 0 < I.capacity e) (q : I.ReverseWalk (I.head e) (I.tail e))
    (hq : q.vertices.Nodup) :
    ∃ v : Fin I.n, ∃ p : I.DirectedWalk v v,
      p.edges = q.toDirectedWalk.edges ++ [e] ∧ ∀ a, p.count a ≤ 1 := by
  let p := ReverseWalk.snoc e he q
  refine ⟨I.head e, p.toDirectedWalk, ?_, ?_⟩
  · simp only [p, ReverseWalk.toDirectedWalk, DirectedWalk.edges_append, DirectedWalk.edges]
  · intro a
    rw [p.count_toDirectedWalk]
    exact q.count_closed_snoc_le_one hq e he rfl rfl a

end MinCostFlow.Scaling.Circulation
