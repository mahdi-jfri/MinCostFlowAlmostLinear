module

public import MinCostFlow.Scaling.PeelFrameStep

/-!
# Completing the closed-suffix peel

The negative-cycle scan used by Lemma C.10 of Chen et al.,
arXiv:2203.00671v2, Appendix C, peels one saved suffix edge at a time.
Induction on that suffix proves that exactly its edge-count many steps
finish the closed-part test. The saved list is the suffix in forward order
followed by the already saved edges. The retained prefix and its markers
are unchanged, so a nonnegative test resumes the canonical walking state.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.ReverseWalk
variable {I : Circulation} {a b : Fin I.n}

/-- An empty stack walk has equal endpoints. -/
theorem end_eq_start_of_edges_nil (p : I.ReverseWalk a b) (hp : p.edges = []) : b = a := by
  cases p with
  | nil => rfl
  | snoc e he q => simp only [edges, List.cons_ne_nil] at hp

end MinCostFlow.Scaling.Circulation.ReverseWalk

namespace MinCostFlow.Scaling.Circulation.CycleState
variable {I : Circulation} {root target current : Fin I.n}

/-- Peeling a simple nonempty suffix takes exactly one step per suffix edge
and returns or discards precisely that completed closed part. -/
theorem run_peelFrame (out : Fin I.n → List (Fin I.m)) (candidates : List (Fin I.m))
    (p : I.ReverseWalk root target) (q : I.ReverseWalk target current)
    (saved : List (Fin I.m)) (hq : q.vertices.Nodup)
    (hdisj : ∀ v ∈ q.heads, v ∉ p.vertices) (hne : q.edges ≠ []) :
    (run q.edges.length (peelFrame out candidates p q saved)).1 =
      finishPeelFrame out candidates p (q.toDirectedWalk.edges ++ saved) := by
  induction q generalizing saved with
  | nil => exact False.elim (hne rfl)
  | @snoc e he v q ih =>
    have hqn := (List.nodup_cons.mp hq).2
    have hdq : ∀ v ∈ q.heads, v ∉ p.vertices := by
      intro v hv
      exact hdisj v (List.mem_cons_of_mem _ hv)
    have hs := peelFrame_snoc_step out candidates p e he q saved hq hdisj
    have hm : (peelFrame out candidates p (ReverseWalk.snoc e he q) saved).mode ≠ .done := by
      intro h
      cases h
    change (run (q.edges.length + 1) (peelFrame out candidates p (ReverseWalk.snoc e he q) saved)).1 = _
    rw [run, ite_eq_right hm]
    dsimp only
    rw [hs]
    by_cases ht : I.tail e = v
    · rw [ite_eq_left ht]
      have hqnil : q.edges = [] := by
        cases ht
        exact q.edges_eq_nil_of_nodup_closed hqn
      have hqforward : q.toDirectedWalk.edges = [] := by
        rw [q.edges_toDirectedWalk, hqnil, List.reverse_nil]
      simp only [hqnil, List.length_nil, run, ReverseWalk.toDirectedWalk,
        DirectedWalk.edges_append, DirectedWalk.edges, hqforward, List.nil_append,
        List.singleton_append]
    · rw [ite_eq_right ht]
      have hqne : q.edges ≠ [] := by
        intro hz
        exact ht (q.end_eq_start_of_edges_nil hz)
      rw [ih p (e :: saved) hqn hdq hqne]
      simp only [ReverseWalk.toDirectedWalk, DirectedWalk.edges_append, DirectedWalk.edges,
        List.append_assoc, List.singleton_append]

end MinCostFlow.Scaling.Circulation.CycleState
