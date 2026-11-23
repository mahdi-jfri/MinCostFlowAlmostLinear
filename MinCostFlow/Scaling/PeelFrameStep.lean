module

public import MinCostFlow.Scaling.CycleFrames

/-!
# One step of peeling a closed suffix

In the extraction used by Lemma C.10 of Chen et al., arXiv:2203.00671v2,
Appendix C, peeling removes the newest remaining suffix edge and prepends it
to the saved closed part. The marker for its head is cleared. At the target,
the complete closed part is tested and the retained prefix resumes or the
scan returns it. This file proves the exact state identity for that step.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.CycleState
variable {I : Circulation} {root target : Fin I.n}

/-- Popping one suffix edge has precisely the canonical next-frame form. -/
theorem peelFrame_snoc_step (out : Fin I.n → List (Fin I.m)) (candidates : List (Fin I.m))
    (p : I.ReverseWalk root target) (e : Fin I.m) (he : 0 < I.capacity e)
    (q : I.ReverseWalk target (I.tail e)) (saved : List (Fin I.m))
    (hq : (ReverseWalk.snoc e he q).vertices.Nodup)
    (hdisj : ∀ v ∈ (ReverseWalk.snoc e he q).heads, v ∉ p.vertices) :
    (peelFrame out candidates p (ReverseWalk.snoc e he q) saved).step =
      if I.tail e = target then finishPeelFrame out candidates p (e :: saved)
      else peelFrame out candidates p q (e :: saved) := by
  classical
  have hnot := (List.nodup_cons.mp hq).1
  have hhead : I.head e ≠ target := by
    intro hh
    exact hnot (hh.symm ▸ q.start_mem_vertices)
  have hnotrest : I.head e ∉ q.heads ++ p.vertices := by
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · apply hnot
      rw [q.vertices_eq_heads]
      exact List.mem_append_left _ hm
    · exact hdisj (I.head e) (by exact List.mem_cons_self) hm
  have hmark : Function.update (markers ((ReverseWalk.snoc e he q).heads ++ p.vertices))
      (I.head e) false = markers (q.heads ++ p.vertices) := by
    simp only [ReverseWalk.heads, ReverseWalk.edges, List.map_cons, List.cons_append]
    exact markers_remove _ _ hnotrest
  by_cases ht : I.tail e = target
  · have hqnil : q.edges = [] := by
      cases ht
      exact q.edges_eq_nil_of_nodup_closed (List.nodup_cons.mp hq).2
    have hheads : q.heads = [] := by simp only [ReverseWalk.heads, hqnil, List.map_nil]
    simp only [peelFrame, step, ReverseWalk.edges, List.cons_append, hhead, ↓reduceIte]
    rw [hmark]
    simp only [ht, ↓reduceIte, hqnil, hheads, List.nil_append, finishPeelFrame,
      walkFrame, List.map_cons, List.sum_cons]
    rw [Int.add_comm ((saved.map I.cost).sum) (I.cost e)]
  · simp only [peelFrame, step, ReverseWalk.edges, List.cons_append, hhead, ht, ↓reduceIte]
    rw [hmark]
    simp only [List.map_cons, List.sum_cons]
    rw [Int.add_comm ((saved.map I.cost).sum) (I.cost e)]

end MinCostFlow.Scaling.Circulation.CycleState
