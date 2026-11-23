module

public import MinCostFlow.Scaling.ShiftedInputLayout
public import MinCostFlow.Scaling.DemandScan
public import MinCostFlow.Scaling.ReductionCapacityBounds
import Mathlib.Tactic.NormNum

/-!
# Word bounds for the lower-capacity reduction

The general-flow reduction of Lemma C.1 of Chen et al., arXiv:2203.00671v2,
subtracts bounded capacities and accumulates their incidence contributions.
If original demands and capacities have magnitude at most `U`, a word bound
covering `(2*m+2)*U` covers both the signed demand scan and the unsigned
capacity differences. Costs and endpoints are copied from the original input.
These facts discharge the arithmetic premises of the executable reductions.
-/

public section
namespace MinCostFlow.Scaling.Machine

/-- Every word of an original edge belongs to the complete encoded input. -/
theorem inputEdge_word_mem (I : Instance) (e : Edge) (he : e ∈ I.edges)
    {x : ℕ} (hx : x ∈ e.encode) : x ∈ I.encode :=
  instance_edges_word_mem I (List.mem_flatMap.mpr ⟨e, he, hx⟩)

/-- One common word budget covers subtracting any two original capacities. -/
theorem capacity_sum_words {w U : ℕ} (I : Instance)
    (hl : ∀ e ∈ I.edges, e.lower.natAbs ≤ U)
    (hu : ∀ e ∈ I.edges, e.upper.natAbs ≤ U)
    (hbudget : (2 * I.m + 2) * U < 2 ^ w) :
    ∀ e ∈ I.edges, e.lower.natAbs + e.upper.natAbs < 2 ^ w := by
  have htwo : 2 * U ≤ (2 * I.m + 2) * U :=
    Nat.mul_le_mul_right U (by omega)
  intro e he
  have hl' := hl e he
  have hu' := hu e he
  omega

/-- The common word budget covers the full demand-scan allowance. -/
theorem demand_scan_words {w U : ℕ} (I : Instance)
    (hbudget : (2 * I.m + 2) * U < 2 ^ w) : U + 2 * I.m * U < 2 ^ w := by
  rw [Nat.add_mul] at hbudget
  omega

/-- All words in the shifted graph fit whenever the original words and
capacity-difference arithmetic fit. -/
theorem shiftedGraph_words {w U : ℕ} (I : Instance) (hv : I.IsValid)
    (hinput : ∀ x ∈ I.encode, x < 2 ^ w)
    (hl : ∀ e ∈ I.edges, e.lower.natAbs ≤ U)
    (hu : ∀ e ∈ I.edges, e.upper.natAbs ≤ U)
    (hbudget : (2 * I.m + 2) * U < 2 ^ w) :
    ∀ x ∈ (FlowReduction.shiftedGraph I hv).solverWords, x < 2 ^ w := by
  have hsum := capacity_sum_words I hl hu hbudget
  rw [shiftedGraph_solverWords]
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hinput _ (List.mem_cons_self)
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact hinput _ (List.mem_cons_of_mem _ (List.mem_cons_self))
    · obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
      have hewords : ∀ y ∈ e.encode, y < 2 ^ w := fun y hy => hinput y (inputEdge_word_mem I e he hy)
      simp only [shiftedEdgeWords, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact hewords _ (by simp [Edge.encode])
      · exact hewords _ (by simp [Edge.encode])
      · have hb := hsum e he
        omega
      · exact hewords _ (by simp [Edge.encode, encodeInt])
      · exact hewords _ (by simp [Edge.encode, encodeInt])

/-- The computed shifted demand table fits the same common word budget. -/
theorem buildShiftedDemands_words {w U : ℕ} (I : Instance) (hv : I.IsValid)
    (hd : ∀ v : Fin I.n, (I.d v).natAbs ≤ U)
    (hl : ∀ e : Fin I.m, (I.edge e).lower.natAbs ≤ U)
    (hbudget : (2 * I.m + 2) * U < 2 ^ w) :
    ∀ v, (FlowReduction.buildShiftedDemands I hv v).natAbs < 2 ^ w := by
  rw [FlowReduction.buildShiftedDemands_eq]
  have hfactor : (I.m + 1) * U ≤ (2 * I.m + 2) * U :=
    Nat.mul_le_mul_right U (by omega)
  intro v
  exact lt_of_le_of_lt ((FlowReduction.shiftedDemand_natAbs_le I U hd hl v).trans hfactor) hbudget

end MinCostFlow.Scaling.Machine
