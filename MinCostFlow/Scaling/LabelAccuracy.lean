module

public import MinCostFlow.Scaling.LabelTraversal
public import MinCostFlow.Scaling.AdjacencyMembership
import Mathlib.Tactic.Tauto

/-!
# Accuracy of labels assigned along tight arcs

The shortest-tree step of Lemma C.8 of Chen et al., arXiv:2203.00671v2,
Appendix C, propagates labels through an optimal routing's positive support.
If a potential is tight on every used arc, each first-visit assignment agrees
with that potential. We prove this directly for each step and the finite
traversal. No shortest-path routine or dual solver is assumed.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation
namespace LabelState
variable {I : Circulation}

/-- One traversal step preserves accurate visited labels and the source of
all queued arcs. Stored adjacency entries remain at their tails. -/
theorem step_labels (s : LabelState I) (flow : Fin I.m → ℤ) (y : Fin I.n → ℤ)
    (htight : ∀ e, 0 < flow e → y (I.head e) = y (I.tail e) - I.cost e)
    (hlabels : ∀ v, s.seen v = true → s.labels v = y v)
    (hpending : ∀ e ∈ s.pending, s.seen (I.tail e) = true ∧ 0 < flow e)
    (hout : ∀ v e, e ∈ s.outgoing v → I.tail e = v ∧ 0 < flow e) :
    (∀ v, s.step.1.seen v = true → s.step.1.labels v = y v) ∧
    (∀ e ∈ s.step.1.pending, s.step.1.seen (I.tail e) = true ∧ 0 < flow e) ∧
    (∀ v e, e ∈ s.step.1.outgoing v → I.tail e = v ∧ 0 < flow e) := by
  classical
  cases hp : s.pending with
  | nil =>
    simp only [step, hp]
    exact ⟨hlabels, by simp, hout⟩
  | cons e rest =>
    have he := hpending e (by rw [hp]; exact List.mem_cons_self)
    simp only [step, hp]
    split
    · dsimp only
      refine ⟨hlabels, ?_, hout⟩
      intro a ha
      exact hpending a (by rw [hp]; exact List.mem_cons_of_mem _ ha)
    · dsimp only
      refine ⟨?_, ?_, ?_⟩
      · intro v hv
        by_cases hvw : v = I.head e
        · subst v
          simp only [Function.update_self]
          rw [hlabels _ he.1, ← htight e he.2]
        · simp only [Function.update_of_ne hvw] at hv ⊢
          exact hlabels v hv
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨ht, hpos⟩ := hout (I.head e) a ha
          exact ⟨by rw [ht, Function.update_self], hpos⟩
        · obtain ⟨ht, hpos⟩ := hpending a (by rw [hp]; exact List.mem_cons_of_mem _ ha)
          refine ⟨?_, hpos⟩
          by_cases hh : I.tail a = I.head e
          · rw [hh, Function.update_self]
          · simpa only [Function.update_of_ne hh] using ht
      · intro v a ha
        by_cases hv : v = I.head e
        · subst v
          simp only [Function.update_self, List.not_mem_nil] at ha
        · simp only [Function.update_of_ne hv] at ha
          exact hout v a ha

/-- Every finite run preserves the same accuracy and adjacency properties. -/
theorem run_labels (fuel : ℕ) (s : LabelState I) (flow : Fin I.m → ℤ) (y : Fin I.n → ℤ)
    (htight : ∀ e, 0 < flow e → y (I.head e) = y (I.tail e) - I.cost e)
    (hlabels : ∀ v, s.seen v = true → s.labels v = y v)
    (hpending : ∀ e ∈ s.pending, s.seen (I.tail e) = true ∧ 0 < flow e)
    (hout : ∀ v e, e ∈ s.outgoing v → I.tail e = v ∧ 0 < flow e) :
    ∀ v, (run fuel s).1.seen v = true → (run fuel s).1.labels v = y v := by
  induction fuel generalizing s with
  | zero => exact hlabels
  | succ fuel ih =>
    rw [run]
    split
    · exact hlabels
    · have hs := s.step_labels flow y htight hlabels hpending hout
      exact ih s.step.1 hs.1 hs.2.1 hs.2.2

end LabelState

/-- Every label assigned by the concrete traversal agrees with any potential
zero at the root and tight on all positive-flow arcs. -/
theorem propagateLabels_accuracy (I : Circulation) (flow : Fin I.m → ℤ)
    (root : Fin I.n) (y : Fin I.n → ℤ) (hroot : y root = 0)
    (htight : ∀ e, 0 < flow e → y (I.head e) = y (I.tail e) - I.cost e) :
    ∀ v, (I.propagateLabels flow root).1.seen v = true →
      (I.propagateLabels flow root).1.labels v = y v := by
  apply LabelState.run_labels I.m (I.initialLabelState flow root) flow y htight
  · intro v hv
    change decide (v = root) = true at hv
    have he : v = root := of_decide_eq_true hv
    subst v
    exact hroot.symm
  · intro e he
    change e ∈ I.buildAdjacency flow root at he
    have hh := (I.buildAdjacency_mem flow e root).mp he
    constructor
    · change decide (I.tail e = root) = true
      exact decide_eq_true hh.2.symm
    · exact hh.1
  · intro v e he
    change e ∈ Function.update (I.buildAdjacency flow) root [] v at he
    by_cases hv : v = root
    · subst v
      simp only [Function.update_self, List.not_mem_nil] at he
    · rw [Function.update_of_ne hv] at he
      have hh := (I.buildAdjacency_mem flow e v).mp he
      exact ⟨hh.2.symm, hh.1⟩

end MinCostFlow.Scaling.Circulation
