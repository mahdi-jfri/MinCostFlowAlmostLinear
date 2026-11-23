module

public import MinCostFlow.Scaling.CostLoopCorrectness
public import MinCostFlow.Scaling.CostScalingModel

/-!
# Correctness of the complete cost-scaling function

Lemma C.3 of Chen et al., arXiv:2203.00671v2, Appendix C, reduces arbitrary
integer costs to polynomially bounded costs. The complete model compresses
vertices once, directly solves costs already within the polynomial bound,
and otherwise runs the proved scaling loop. Empty graphs are solved by zero.
The capacity budget explicitly includes the finite shortest-routing reduction
of Lemma C.8. Its call and work bounds are proved in `CostScalingModel`.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Lemma C.3 (Appendix C): the complete integer cost-scaling model returns
an exact optimum against all feasible real circulations. The explicit C.8
capacity budget is `max U (2*m+1)` after vertex compression. -/
theorem lemma_C_3 (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C U : ℕ) (hU : 1 ≤ U)
    (hc : I.CostsBounded C) (hu : ∀ e, I.capacity e ≤ U)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ max U (2 * I.m + 1)) →
      J.Optimal (fun e => (solve J e : ℝ))) :
    I.Optimal (fun e => ((costScalingModel solve I C).value e : ℝ)) := by
  unfold costScalingModel
  split
  · rename_i hm
    simp only [Int.cast_zero]
    change I.Optimal (fun _ => 0)
    refine ⟨I.zero_feasible, ?_⟩
    intro g _
    have he : g = fun _ => 0 := by
      funext e
      have hh := e.isLt
      omega
    rw [he]
  · rename_i hm
    dsimp only
    apply (I.compress_optimal_iff _).mp
    have hbudget : max U (I.compress.n + 1) ≤ max U (2 * I.m + 1) :=
      max_le_max le_rfl (Nat.add_le_add_right I.endpointLabels_count_le 1)
    have hs : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
        (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ max U (I.compress.n + 1)) →
        J.Optimal (fun e => (solve J e : ℝ)) := by
      intro J hc hcap
      exact hsolve J hc (fun e => ⟨(hcap e).1, le_trans (hcap e).2 hbudget⟩)
    split
    · rename_i hC
      apply Circulation.solveWithZeroCapacities_correct solve (max U (I.compress.n + 1))
        (le_trans hU (le_max_left _ _)) hs
      · intro e
        exact le_trans (hc e) hC
      · exact fun e => le_trans (hu e) (le_max_left _ _)
    · exact costLoop_optimal solve I.compress C U hU (Nat.pos_of_ne_zero hm)
        (by
          have hh := I.endpointLabels_count_le
          change I.compress.n ≤ 2 * I.m at hh
          change I.compress.n ≤ I.m + I.m
          omega)
        hs hc hu

end MinCostFlow.Scaling
