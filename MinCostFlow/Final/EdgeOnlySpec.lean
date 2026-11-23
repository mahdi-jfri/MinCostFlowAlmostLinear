module

public import MinCostFlow.IPM.EdgeOnly
public import MinCostFlow.IPM.Machine.ConnectedSolverInitialize
import Mathlib.Tactic

/-!
# Edge-only min-ratio interface for the final assembly

Bridges the ordered Theorem 5.1 conclusion (`MinRatioHistoryValid` + `HistoryEdgeOnly` + size and
connectivity bounds) to `MinRatioSpecWithFailureEdgeOnlyConnectedUpTo` and to
`MinRatioSpecWithFailureUpToOn` on the connected augmented instance `solverConnectedAugmented J`.
Also records an edge-only example, showing that even on a
fixed-graph edge-only history, validity and hidden stability alone do not imply size bounds.
-/

public section
namespace MinCostFlow.Final

open IPM IPM.Machine Scaling Chain.Ordered

/-- The named graph of `solverConnectedAugmented J` is connected. -/
theorem solverConnectedAugmented_graphConnected (J : Circulation) :
    MinRatioGraphConnected (namedInstance (solverConnectedAugmented J)) :=
  connectedInitialInstance_connected J.toInstance (solverPenalty J.m : ℤ)

/-- The named graph of `solverConnectedAugmented J` satisfies `MinRatioGraphConnectedFixedV`
with its own vertex set. -/
theorem solverConnectedAugmented_graphConnectedFixedV (J : Circulation) :
    MinRatioGraphConnectedFixedV (namedInstance (solverConnectedAugmented J)).V
      (namedInstance (solverConnectedAugmented J)) :=
  ⟨rfl, solverConnectedAugmented_graphConnected J⟩

/-- Package the query/update/detect guarantees of ordered Theorem 5.1 (page 15) on graphs with
`m ≤ M₀`, `n ≤ N₀`, connectivity, and lengths in the range `Ψ` into `MinRatioSpecWithFailureEdgeOnlyConnectedUpTo` at any
smaller size limits `(M, N)`. -/
theorem minRatioSpecWithFailureEdgeOnlyConnectedUpTo_of_ordered
    {A : MinRatioDataStructureWithFailure} {κ α Ψ ε : ℝ} {M N M₀ N₀ : ℕ}
    (hM : M ≤ M₀) (hN : N ≤ N₀)
    (hSpec : ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
      MinRatioHistoryValid D isUpdate T →
      HistoryEdgeOnly D T →
      MinRatioHistoryLengthsInRange D T Ψ →
      (∀ t ≤ T, (D.G t).m ≤ M₀) →
      (∀ t ≤ T, (D.G t).n ≤ N₀) →
      (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
      (∀ t ≤ T, ∀ e ∈ (D.G t).E,
        A.query (minRatioState A.eraseFailure D η isUpdate t) e =
          minRatioFlow A.eraseFailure D η isUpdate t e) ∧
      (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
        (D.G (t + 1)).IsCirculation
          (minRatioDirection A.eraseFailure D η isUpdate t) ∧
        (D.HiddenStable (t + 1) α Ψ →
          (minRatioFailureDirection A D η isUpdate t).isSome = true ∧
          (D.G (t + 1)).inner (D.g (t + 1))
              (minRatioDirection A.eraseFailure D η isUpdate t) /
            (D.G (t + 1)).lnorm (D.ℓ (t + 1))
              (minRatioDirection A.eraseFailure D η isUpdate t) ≤ -(κ * α))) ∧
      (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
        (A.detect (minRatioState A.eraseFailure D η isUpdate t)).1 =
          minRatioDetectSet A.eraseFailure D η isUpdate ε t)) :
    MinRatioSpecWithFailureEdgeOnlyConnectedUpTo A κ α Ψ ε M N := by
  intro D η op T hValid hEdge hBounded hConn hLen
  have hmM₀ : ∀ t ≤ T, (D.G t).m ≤ M₀ := fun t ht => (hBounded.1 t ht).trans hM
  have hnN₀ : ∀ t ≤ T, (D.G t).n ≤ N₀ := fun t ht => (hBounded.2 t ht).trans hN
  obtain ⟨hQuery, hUpdate, hDetect⟩ := hSpec hValid hEdge hLen hmM₀ hnN₀ hConn
  refine ⟨⟨hQuery, fun t ht hop => ⟨(hUpdate t ht hop).1, fun hHid => ?_⟩, hDetect⟩,
    fun t ht hop hHid => ((hUpdate t ht hop).2 hHid).1⟩
  rw [neg_mul]
  exact ((hUpdate t ht hop).2 hHid).2

/-- Same packaging as `minRatioSpecWithFailureEdgeOnlyConnectedUpTo_of_ordered`, but allowing a
weaker quality `κ' ≤ κ` (matching the `algorithm2_dsWithFailureOwn` reduction). -/
theorem minRatioSpecWithFailureEdgeOnlyConnectedUpTo_of_ordered_le
    {A : MinRatioDataStructureWithFailure} {κ κ' α Ψ ε : ℝ} {M N M₀ N₀ : ℕ}
    (hα : 0 ≤ α) (hκ : κ' ≤ κ) (hM : M ≤ M₀) (hN : N ≤ N₀)
    (hSpec : ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
      MinRatioHistoryValid D isUpdate T →
      HistoryEdgeOnly D T →
      MinRatioHistoryLengthsInRange D T Ψ →
      (∀ t ≤ T, (D.G t).m ≤ M₀) →
      (∀ t ≤ T, (D.G t).n ≤ N₀) →
      (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
      (∀ t ≤ T, ∀ e ∈ (D.G t).E,
        A.query (minRatioState A.eraseFailure D η isUpdate t) e =
          minRatioFlow A.eraseFailure D η isUpdate t e) ∧
      (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
        (D.G (t + 1)).IsCirculation
          (minRatioDirection A.eraseFailure D η isUpdate t) ∧
        (D.HiddenStable (t + 1) α Ψ →
          (minRatioFailureDirection A D η isUpdate t).isSome = true ∧
          (D.G (t + 1)).inner (D.g (t + 1))
              (minRatioDirection A.eraseFailure D η isUpdate t) /
            (D.G (t + 1)).lnorm (D.ℓ (t + 1))
              (minRatioDirection A.eraseFailure D η isUpdate t) ≤ -(κ * α))) ∧
      (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
        (A.detect (minRatioState A.eraseFailure D η isUpdate t)).1 =
          minRatioDetectSet A.eraseFailure D η isUpdate ε t)) :
    MinRatioSpecWithFailureEdgeOnlyConnectedUpTo A κ' α Ψ ε M N := by
  apply minRatioSpecWithFailureEdgeOnlyConnectedUpTo_of_ordered hM hN
  intro D η isUpdate T hValid hEdge hLen hmM₀ hnN₀ hConn
  obtain ⟨hQuery, hUpdate, hDetect⟩ := hSpec hValid hEdge hLen hmM₀ hnN₀ hConn
  refine ⟨hQuery, fun t ht hop => ⟨(hUpdate t ht hop).1, fun hHid => ?_⟩, hDetect⟩
  have hU := (hUpdate t ht hop).2 hHid
  refine ⟨hU.1, hU.2.trans ?_⟩
  exact neg_le_neg (mul_le_mul_of_nonneg_right hκ hα)

/-- Directly derive `MinRatioSpecWithFailureUpToOn (MinRatioStageFixed (namedInstance (solverConnectedAugmented J)) Ψ)`
from `MinRatioSpecWithFailureEdgeOnlyConnectedUpTo` on `solverConnectedAugmented J`. -/
theorem solverConnectedAugmented_edgeOnly_to_fixedGraph
    {A : MinRatioDataStructureWithFailure} {κ α Ψ ε : ℝ} (J : Circulation)
    (hA : MinRatioSpecWithFailureEdgeOnlyConnectedUpTo A κ α Ψ ε
      (solverConnectedAugmented J).m (solverConnectedAugmented J).n) :
    MinRatioSpecWithFailureUpToOn
      (MinRatioStageFixed (namedInstance (solverConnectedAugmented J)) Ψ)
      A κ α Ψ ε (solverConnectedAugmented J).m (solverConnectedAugmented J).n :=
  hA.toUpToOn_fixedGraph (namedInstance (solverConnectedAugmented J))
    (solverConnectedAugmented_graphConnected J)

/-- Directly derive `MinRatioSpecWithFailureUpToOn (MinRatioStageConnectedFixedV (namedInstance (solverConnectedAugmented J)).V Ψ)`
from `MinRatioSpecWithFailureEdgeOnlyConnectedUpTo` on `solverConnectedAugmented J`. -/
theorem solverConnectedAugmented_edgeOnly_to_fixedV
    {A : MinRatioDataStructureWithFailure} {κ α Ψ ε : ℝ} (J : Circulation)
    (hA : MinRatioSpecWithFailureEdgeOnlyConnectedUpTo A κ α Ψ ε
      (solverConnectedAugmented J).m (solverConnectedAugmented J).n) :
    MinRatioSpecWithFailureUpToOn
      (MinRatioStageConnectedFixedV (namedInstance (solverConnectedAugmented J)).V Ψ)
      A κ α Ψ ε (solverConnectedAugmented J).m (solverConnectedAugmented J).n :=
  hA.toUpToOn_fixedV (namedInstance (solverConnectedAugmented J)).V

private def edgeOnlyLoopHistory (n m : ℕ) (α : ℝ) : DynamicInstance where
  G _ := ⟨Finset.range (n + 1), Finset.range (m + 1), fun _ => 0, fun _ => 0⟩
  U _ := []
  g _ _ := -α
  ℓ _ _ := 1

/-- Companion to `MinRatioHistoryBounds.exists_hiddenStable_history_above_bounds`: even on a
fixed-graph edge-only history, validity and hidden stability alone give neither graph size bound
used by Theorem 5.1 (page 15). -/
theorem exists_hiddenStable_edgeOnly_history_above_bounds (n m : ℕ) (α Ψ : ℝ) (hΨ : 0 ≤ Ψ) :
    ∃ D : DynamicInstance, MinRatioHistoryValid D (fun _ => true) 1 ∧
      HistoryEdgeOnly D 1 ∧
      (∀ t ≤ 1, D.G t = D.G 0) ∧
      D.HiddenStable 1 α Ψ ∧ n < (D.G 1).n ∧ m < (D.G 1).m := by
  refine ⟨edgeOnlyLoopHistory n m α, ?_, ?_, fun _ _ => rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _ _
      exact ⟨trivial, rfl⟩
    · intro t _
      constructor
      · intro e _
        simp [edgeOnlyLoopHistory]
      · intro e _
        norm_num [edgeOnlyLoopHistory]
    · intro t _ _ h
      cases h
    · intro t _ _ e _ _
      exact ⟨rfl, rfl⟩
  · intro t _ _ u hu
    exact False.elim (List.not_mem_nil hu)
  · refine ⟨fun _ _ => 1, fun _ _ => 1, ?_⟩
    intro t _
    simp [DynamicInstance.HiddenStableAt, IsValidPair, edgeOnlyLoopHistory,
      MGraph.IsCirculation, MGraph.demand, MGraph.b, MGraph.inner, MGraph.norm1, hΨ]
    constructor
    · intro v _
      exact sub_self _
    · apply (div_le_iff₀ (show 0 < (m : ℝ) + 1 by positivity)).mpr
      ring_nf
      exact le_rfl
  · simp [edgeOnlyLoopHistory, MGraph.n]
  · simp [edgeOnlyLoopHistory, MGraph.m]

end MinCostFlow.Final
