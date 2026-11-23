module

public import MinCostFlow.Scaling.LabelTraversal
public import MinCostFlow.Scaling.AdjacencyMembership

/-!
# Coverage of positive-support label traversal

Lemma C.8 of Chen et al., arXiv:2203.00671v2, Appendix C, extracts a tree
from positive routing arcs. An unvisited vertex retains its full adjacency
list. Every positive arc leaving a visited vertex either reaches another
visited vertex or is pending. These facts are preserved by the explicit
traversal. Once the queue is empty, the visited set is closed under positive
flow, and all vertices reachable from the root have been visited.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation.LabelState
variable {I : Circulation}

/-- Visiting more vertices never clears a visited flag. -/
theorem step_seen (s : LabelState I) (v : Fin I.n) (hv : s.seen v = true) :
    s.step.1.seen v = true := by
  classical
  cases hp : s.pending with
  | nil => simpa only [step, hp] using hv
  | cons e rest =>
    simp only [step, hp]
    split
    · exact hv
    · dsimp only
      by_cases he : v = I.head e
      · subst v; exact Function.update_self _ _ _
      · simpa only [Function.update_of_ne he] using hv

/-- Unvisited adjacency lists stay complete and positive outgoing arcs stay
covered by visited heads or by the pending queue. -/
theorem step_coverage (s : LabelState I) (flow : Fin I.m → ℤ)
    (hfull : ∀ v, s.seen v = false → s.outgoing v = I.buildAdjacency flow v)
    (hcover : ∀ a, 0 < flow a → s.seen (I.tail a) = true →
      s.seen (I.head a) = true ∨ a ∈ s.pending) :
    (∀ v, s.step.1.seen v = false → s.step.1.outgoing v = I.buildAdjacency flow v) ∧
    (∀ a, 0 < flow a → s.step.1.seen (I.tail a) = true →
      s.step.1.seen (I.head a) = true ∨ a ∈ s.step.1.pending) := by
  classical
  cases hp : s.pending with
  | nil =>
    have hs := And.intro hfull hcover
    simpa only [step, hp] using hs
  | cons e rest =>
    simp only [step, hp]
    split
    · rename_i hseen
      dsimp only
      refine ⟨hfull, ?_⟩
      intro a hpos ht
      rcases hcover a hpos ht with hh | ha
      · exact Or.inl hh
      · rw [hp] at ha
        rcases List.mem_cons.mp ha with ha | ha
        · subst a; exact Or.inl hseen
        · exact Or.inr ha
    · rename_i hseen
      dsimp only
      have hunseen : s.seen (I.head e) = false := Bool.eq_false_iff.mpr hseen
      constructor
      · intro v hv
        have he : v ≠ I.head e := by
          intro he
          subst v
          rw [Function.update_self] at hv
          cases hv
        rw [Function.update_of_ne he] at hv ⊢
        exact hfull v hv
      · intro a hpos ht
        by_cases htail : I.tail a = I.head e
        · right
          apply List.mem_append_left
          rw [hfull _ hunseen]
          exact (I.buildAdjacency_mem flow a (I.head e)).mpr ⟨hpos, htail.symm⟩
        · rw [Function.update_of_ne htail] at ht
          rcases hcover a hpos ht with hh | ha
          · left
            by_cases hhead : I.head a = I.head e
            · rw [hhead, Function.update_self]
            · simpa only [Function.update_of_ne hhead] using hh
          · rw [hp] at ha
            rcases List.mem_cons.mp ha with ha | ha
            · subst a
              left
              rw [Function.update_self]
            · right
              exact List.mem_append_right _ ha

/-- The coverage and complete-adjacency properties hold after every finite run. -/
theorem run_coverage (fuel : ℕ) (s : LabelState I) (flow : Fin I.m → ℤ)
    (hfull : ∀ v, s.seen v = false → s.outgoing v = I.buildAdjacency flow v)
    (hcover : ∀ a, 0 < flow a → s.seen (I.tail a) = true →
      s.seen (I.head a) = true ∨ a ∈ s.pending) :
    (∀ v, (run fuel s).1.seen v = false →
      (run fuel s).1.outgoing v = I.buildAdjacency flow v) ∧
    (∀ a, 0 < flow a → (run fuel s).1.seen (I.tail a) = true →
      (run fuel s).1.seen (I.head a) = true ∨ a ∈ (run fuel s).1.pending) := by
  induction fuel generalizing s with
  | zero => exact ⟨hfull, hcover⟩
  | succ fuel ih =>
    rw [run]
    split
    · exact ⟨hfull, hcover⟩
    · have hs := s.step_coverage flow hfull hcover
      exact ih s.step.1 hs.1 hs.2

/-- A finite run preserves every initially visited vertex. -/
theorem run_seen (fuel : ℕ) (s : LabelState I) (v : Fin I.n) (hv : s.seen v = true) :
    (run fuel s).1.seen v = true := by
  induction fuel generalizing s with
  | zero => exact hv
  | succ fuel ih =>
    rw [run]
    split
    · exact hv
    · exact ih s.step.1 (s.step_seen v hv)

end MinCostFlow.Scaling.Circulation.LabelState
