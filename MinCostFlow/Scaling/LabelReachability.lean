module

public import MinCostFlow.Scaling.LabelCoverage
public import MinCostFlow.Scaling.PositiveSupport

/-!
# All reachable support vertices receive labels

For the traversal used in Lemma C.8 of Chen et al., arXiv:2203.00671v2,
Appendix C, the pending queue is exhausted within the supplied edge budget.
The coverage invariant then makes the visited set closed under every
positive-flow arc. The root starts visited, so every vertex reachable from
it in the positive support is visited as well.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Once label propagation completes, every positive arc out of a visited
vertex has a visited head. -/
theorem propagateLabels_closed (I : Circulation) (flow : Fin I.m → ℤ)
    (root : Fin I.n) :
    ∀ e, 0 < flow e → (I.propagateLabels flow root).1.seen (I.tail e) = true →
      (I.propagateLabels flow root).1.seen (I.head e) = true := by
  have hfull : ∀ v, (I.initialLabelState flow root).seen v = false →
      (I.initialLabelState flow root).outgoing v = I.buildAdjacency flow v := by
    intro v hv
    change decide (v = root) = false at hv
    have hne : v ≠ root := of_decide_eq_false hv
    exact Function.update_of_ne hne _ _
  have hcover : ∀ e, 0 < flow e → (I.initialLabelState flow root).seen (I.tail e) = true →
      (I.initialLabelState flow root).seen (I.head e) = true ∨
        e ∈ (I.initialLabelState flow root).pending := by
    intro e he ht
    change decide (I.tail e = root) = true at ht
    have htail : I.tail e = root := of_decide_eq_true ht
    right
    exact (I.buildAdjacency_mem flow e root).mpr ⟨he, htail.symm⟩
  have hh := LabelState.run_coverage I.m (I.initialLabelState flow root) flow hfull hcover
  intro e he ht
  rcases hh.2 e he ht with hs | hp
  · exact hs
  · change e ∈ (I.propagateLabels flow root).1.pending at hp
    rw [I.propagateLabels_done flow root] at hp
    cases hp

/-- The root remains visited after the complete traversal. -/
theorem propagateLabels_root_seen (I : Circulation) (flow : Fin I.m → ℤ)
    (root : Fin I.n) : (I.propagateLabels flow root).1.seen root = true := by
  apply LabelState.run_seen I.m (I.initialLabelState flow root) root
  change decide (root = root) = true
  exact decide_eq_true rfl

/-- Walk reachability preserves any vertex predicate closed under active arcs. -/
theorem DirectedWalk.end_seen {I : Circulation} {a b : Fin I.n}
    (p : I.DirectedWalk a b) (seen : Fin I.n → Bool)
    (hclosed : ∀ e, 0 < I.capacity e → seen (I.tail e) = true → seen (I.head e) = true)
    (ha : seen a = true) : seen b = true := by
  induction p with
  | nil => exact ha
  | cons e he p ih => exact ih (hclosed e he ha)

/-- Every positive-support walk from a visited vertex ends at a visited vertex. -/
theorem support_walk_seen (I : Circulation) (flow : Fin I.m → ℤ)
    (seen : Fin I.n → Bool)
    (hclosed : ∀ e, 0 < flow e → seen (I.tail e) = true → seen (I.head e) = true)
    {a b : Fin I.n} (p : (I.positiveSupport (fun e => (flow e : ℝ))).DirectedWalk a b)
    (ha : seen a = true) : seen b = true := by
  apply DirectedWalk.end_seen (I := I.positiveSupport (fun e => (flow e : ℝ))) p seen _ ha
  intro e he hs
  have hpos : 0 < flow e := by
    change 0 < if 0 < (flow e : ℝ) then 1 else 0 at he
    split at he
    · rename_i h
      exact Int.cast_pos.mp h
    · contradiction
  exact hclosed e hpos hs

/-- The concrete traversal visits every vertex reachable from its root by
positive-flow arcs. -/
theorem propagateLabels_seen_of_reachable (I : Circulation) (flow : Fin I.m → ℤ)
    (root v : Fin I.n)
    (hp : Nonempty ((I.positiveSupport (fun e => (flow e : ℝ))).DirectedWalk root v)) :
    (I.propagateLabels flow root).1.seen v = true := by
  obtain ⟨p⟩ := hp
  exact I.support_walk_seen flow _ (I.propagateLabels_closed flow root) p
    (I.propagateLabels_root_seen flow root)

end MinCostFlow.Scaling.Circulation
