module

public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.Scaling.ResidualBounds

/-!
# Word bounds for the exact residual encoding

Residual capacities do not exceed the source capacity of their edge when
the supplied integral flow lies within its capacities. Reversal only swaps
endpoints and negates costs. Thus a fitting source encoding and doubled
edge count suffice for all words of the constructed residual graph.
-/

public section
namespace MinCostFlow.Scaling.Machine

/-- Dimension, capacity, magnitude, and sign bounds cover every word of the
common circulation encoding. -/
theorem solverWords_fit_of_bounds (J : Circulation) (w : ℕ)
    (hn : J.n < 2^w) (hm : J.m < 2^w) (hone : 1 < 2^w)
    (hu : ∀ e,J.capacity e < 2^w) (hc : ∀ e,(J.cost e).natAbs < 2^w) :
    ∀ x ∈ J.solverWords,x < 2^w := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hn
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hm
  obtain ⟨e,_,hx⟩ := List.mem_flatMap.mp hx
  simp only [Circulation.solverEdgeWords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact (J.tail e).isLt.trans hn
  · exact (J.head e).isLt.trans hn
  · exact hu e
  · split <;> omega
  · exact hc e

/-- Every residual word fits from fitting source words, a fitting doubled
edge count, and the original integral flow's capacity constraints. -/
theorem residual_words_fit (J : Circulation) (flow : Fin J.m → ℤ) (w : ℕ)
    (hf : ∀ e,0 ≤ flow e ∧ flow e ≤ (J.capacity e : ℤ))
    (hinput : ∀ x ∈ J.solverWords,x < 2^w) (hm : J.m+J.m < 2^w) (hone : 1 < 2^w) :
    ∀ x ∈ (J.residual flow).solverWords,x < 2^w := by
  have hn : J.n < 2^w := hinput _ List.mem_cons_self
  have hu : ∀ e,J.capacity e < 2^w := by
    intro e
    exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
  have hc : ∀ e,(J.cost e).natAbs < 2^w := by
    intro e
    exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
  apply solverWords_fit_of_bounds (J.residual flow) w hn hm hone
  · intro e
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e
    · have hsub : (J.capacity e : ℤ)-flow e ≤ (J.capacity e : ℤ) := sub_le_self _ (hf e).1
      have hnat : ((J.capacity e : ℤ)-flow e).toNat ≤ J.capacity e := by
        simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hsub
      simpa only [Fin.addCases_left] using hnat.trans_lt (hu e)
    · have hnat : (flow e).toNat ≤ J.capacity e := by
        simpa only [Int.toNat_natCast] using Int.toNat_le_toNat (hf e).2
      simpa only [Fin.addCases_right] using hnat.trans_lt (hu e)
  · intro e
    refine Fin.addCases (fun e => ?_) (fun e => ?_) e
    · simpa only [Fin.addCases_left] using hc e
    · simpa only [Fin.addCases_right,Int.natAbs_neg] using hc e

end MinCostFlow.Scaling.Machine
