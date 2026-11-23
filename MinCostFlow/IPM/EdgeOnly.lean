module

public import MinCostFlow.Bundle.Ordered
public import MinCostFlow.Chain.Ordered.Algorithm2
public import MinCostFlow.IPM.EdgeRefresh
public import MinCostFlow.IPM.LazyAlgorithm
public import MinCostFlow.IPM.TargetInstances
public import MinCostFlow.IPM.SearchInstances
public import MinCostFlow.IPM.FailureInstances
public import MinCostFlow.IPM.HiddenParameters
import MinCostFlow.IPM.MinRatioReference
import Lean.Elab.Tactic.Omega

/-!
# Edge-only updates in the IPM's min-ratio histories

The ordered dynamic tree chain requires every level-`0` update batch to consist solely of edge
insertions and deletions (`Bundle.IsEdgeUpdate` and `Chain.Ordered.HistoryEdgeOnly`). This file
establishes three facts for the IPM's dynamic instances:

1. **Structural vertex-set criterion**: valid dynamic updates never remove vertices, and any valid
   vertex split strictly enlarges the vertex set. Consequently, any valid batch or dynamic
   instance whose vertex set does not grow (in particular, any fixed-vertex-set or fixed-graph
   min-ratio history) consists exclusively of edge updates.
2. **Model IPM histories**: every update in `refreshEdge G e` and `refreshEdges G es` satisfies
   `Bundle.IsEdgeUpdate`, and every history produced by `epochInstance`, `boundedTargetInstances`,
   `dataStructureSearchInstances`, `boundedFailureTargetInstances`, and `scaleInstanceGradient`
   satisfies `Chain.Ordered.HistoryEdgeOnly`.
3. **Edge-only min-ratio interface**: `MinRatioSpecWithFailureEdgeOnlyConnectedUpTo` packages the
   exact history hypotheses of ordered Theorem 5.1 (page 15), and converts directly to
   `MinRatioSpecWithFailureUpToOn` on any fixed-vertex-set or fixed-graph predicate, reusing the
   entire parameterized machine-IPM proof stack unchanged.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

open MinCostFlow.Bundle MinCostFlow.Chain.Ordered

/-! ### Structural criterion: constant vertex set implies edge-only updates -/

/-- No primitive update removes vertices from a graph. -/
theorem applyUpdate_V_subset (G : MGraph) (u : MinCostFlow.Update) :
    G.V ⊆ (G.applyUpdate u).V := by
  cases u with
  | insert _ _ _ => exact Finset.Subset.refl _
  | delete _ => exact Finset.Subset.refl _
  | split _ v' _ _ => exact Finset.subset_insert v' G.V

/-- No update batch removes vertices from a graph. -/
theorem applyBatch_V_subset (G : MGraph) (U : List MinCostFlow.Update) :
    G.V ⊆ (G.applyBatch U).V := by
  induction U generalizing G with
  | nil => exact Finset.Subset.refl _
  | cons u U ih => exact (applyUpdate_V_subset G u).trans (ih (G.applyUpdate u))

/-- Edge insertions and deletions leave the vertex set unchanged. -/
theorem applyUpdate_V_eq_of_isEdgeUpdate {G : MGraph} {u : MinCostFlow.Update}
    (h : IsEdgeUpdate u) : (G.applyUpdate u).V = G.V := by
  cases u with
  | insert _ _ _ => rfl
  | delete _ => rfl
  | split _ _ _ _ => exact h.elim

/-- A valid batch whose final vertex set is contained in its initial vertex set contains only
edge insertions and deletions. -/
theorem isEdgeUpdate_of_applyBatch_V_subset {G : MGraph} {U : List MinCostFlow.Update}
    (hv : G.BatchIsValid U) (hsub : (G.applyBatch U).V ⊆ G.V) :
    ∀ u ∈ U, IsEdgeUpdate u := by
  induction U generalizing G with
  | nil => intro u hu; exact False.elim (List.not_mem_nil hu)
  | cons u U ih =>
    have hu : IsEdgeUpdate u := by
      cases u with
      | insert _ _ _ => trivial
      | delete _ => trivial
      | split v v' St Sh =>
        have hnotmem : v' ∉ G.V := hv.1.2.1
        have hmem_step : v' ∈ (G.applyUpdate (.split v v' St Sh)).V :=
          Finset.mem_insert_self v' G.V
        have hmem_end : v' ∈ (G.applyBatch (.split v v' St Sh :: U)).V :=
          applyBatch_V_subset (G.applyUpdate (.split v v' St Sh)) U hmem_step
        exact False.elim (hnotmem (hsub hmem_end))
    have hVeq : (G.applyUpdate u).V = G.V := applyUpdate_V_eq_of_isEdgeUpdate hu
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact hu
    · exact ih hv.2 (hVeq.symm ▸ hsub) w hw'

/-- A valid batch that does not increase the vertex count contains only edge updates. -/
theorem isEdgeUpdate_of_applyBatch_n_le {G : MGraph} {U : List MinCostFlow.Update}
    (hv : G.BatchIsValid U) (hn : (G.applyBatch U).n ≤ G.n) :
    ∀ u ∈ U, IsEdgeUpdate u := by
  have heq : G.V = (G.applyBatch U).V :=
    Finset.eq_of_subset_of_card_le (applyBatch_V_subset G U) hn
  exact isEdgeUpdate_of_applyBatch_V_subset hv (heq ▸ Finset.Subset.refl _)

/-- A valid batch that leaves the graph unchanged contains only edge updates. -/
theorem isEdgeUpdate_of_applyBatch_eq {G : MGraph} {U : List MinCostFlow.Update}
    (hv : G.BatchIsValid U) (heq : G.applyBatch U = G) :
    ∀ u ∈ U, IsEdgeUpdate u :=
  isEdgeUpdate_of_applyBatch_V_subset hv (by rw [heq])

/-- Along any valid dynamic-instance prefix, vertex sets are monotone under inclusion. -/
theorem dynamicInstance_V_subset_of_le {D : DynamicInstance} {T : ℕ}
    (hv : D.IsValid T) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ T) :
    (D.G s).V ⊆ (D.G t).V := by
  induction t with
  | zero =>
    have hs : s = 0 := Nat.eq_zero_of_le_zero hst
    subst hs
    exact Finset.Subset.refl _
  | succ t ih =>
    rcases Nat.eq_or_lt_of_le hst with rfl | hlt
    · exact Finset.Subset.refl _
    · have hs_le : s ≤ t := Nat.le_of_lt_succ hlt
      have hstep := hv (t + 1) (Nat.succ_pos t) ht
      rw [Nat.add_sub_cancel] at hstep
      exact (ih hs_le (Nat.le_of_succ_le ht)).trans (hstep.2 ▸ applyBatch_V_subset (D.G t) (D.U (t + 1)))

/-- Any valid dynamic instance whose vertex count at horizon `T` is at most its initial vertex
count has only edge insertions and deletions through stage `T`. -/
theorem historyEdgeOnly_of_isValid_n_le {D : DynamicInstance} {T : ℕ}
    (hv : D.IsValid T) (hn : (D.G T).n ≤ (D.G 0).n) :
    HistoryEdgeOnly D T := by
  have hVT : (D.G 0).V = (D.G T).V :=
    Finset.eq_of_subset_of_card_le (dynamicInstance_V_subset_of_le hv (Nat.zero_le T) le_rfl) hn
  intro t ht1 htT
  have hstep := hv t ht1 htT
  have hsub : ((D.G (t - 1)).applyBatch (D.U t)).V ⊆ (D.G (t - 1)).V := by
    rw [← hstep.2]
    exact (dynamicInstance_V_subset_of_le hv htT le_rfl).trans
      (hVT ▸ dynamicInstance_V_subset_of_le hv (Nat.zero_le (t - 1)) (by omega))
  exact isEdgeUpdate_of_applyBatch_V_subset hstep.1 hsub

/-- Any valid dynamic instance with a constant vertex set through stage `T` has only edge updates. -/
theorem historyEdgeOnly_of_isValid_fixedV {D : DynamicInstance} {T : ℕ} {V₀ : Finset ℕ}
    (hv : D.IsValid T) (hV : ∀ t ≤ T, (D.G t).V = V₀) :
    HistoryEdgeOnly D T :=
  historyEdgeOnly_of_isValid_n_le hv (by simp [MGraph.n, hV T le_rfl, hV 0 (Nat.zero_le T)])

/-- Any valid min-ratio history whose vertex set stays constant has only edge updates. -/
theorem historyEdgeOnly_of_minRatioHistoryValid_fixedV {D : DynamicInstance}
    {op : ℕ → Bool} {T : ℕ} {V₀ : Finset ℕ}
    (hvalid : MinRatioHistoryValid D op T) (hV : ∀ t ≤ T, (D.G t).V = V₀) :
    HistoryEdgeOnly D T :=
  historyEdgeOnly_of_isValid_fixedV hvalid.1 hV

/-- Any valid min-ratio history on a fixed graph has only edge updates. -/
theorem historyEdgeOnly_of_minRatioHistoryValid_fixedGraph {D : DynamicInstance}
    {op : ℕ → Bool} {T : ℕ} {G₀ : MGraph}
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ t ≤ T, D.G t = G₀) :
    HistoryEdgeOnly D T :=
  historyEdgeOnly_of_minRatioHistoryValid_fixedV hvalid (fun t ht => congrArg MGraph.V (hG t ht))

/-- Any valid min-ratio history whose final vertex count does not exceed its initial vertex count
has only edge updates. -/
theorem historyEdgeOnly_of_minRatioHistoryValid_n_le {D : DynamicInstance}
    {op : ℕ → Bool} {T : ℕ}
    (hvalid : MinRatioHistoryValid D op T) (hn : (D.G T).n ≤ (D.G 0).n) :
    HistoryEdgeOnly D T :=
  historyEdgeOnly_of_isValid_n_le hvalid.1 hn

/-! ### Refresh batches and model IPM histories -/

/-- Every primitive update of `refreshEdge G e` is an edge deletion or insertion. -/
theorem refreshEdge_isEdgeUpdate (G : MGraph) (e : ℕ) :
    ∀ u ∈ refreshEdge G e, IsEdgeUpdate u := by
  intro u hu
  simp only [refreshEdge, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl <;> trivial

/-- Every primitive update of `refreshEdges G es` is an edge deletion or insertion. -/
theorem refreshEdges_isEdgeUpdate (G : MGraph) (es : List ℕ) :
    ∀ u ∈ refreshEdges G es, IsEdgeUpdate u := by
  induction es with
  | nil => intro u hu; exact False.elim (List.not_mem_nil hu)
  | cons e es ih =>
    intro u hu
    rcases List.mem_append.mp hu with h1 | h2
    · exact refreshEdge_isEdgeUpdate G e u h1
    · exact ih u h2

/-- Every batch of `epochInstance` consists solely of edge insertions and deletions, for every
horizon `T`. -/
theorem epochInstance_historyEdgeOnly (I : Instance) (U κ r : ℝ)
    (A : MinRatioDataStructure) (base : Fin I.m → ℝ) (T : ℕ) :
    HistoryEdgeOnly (epochInstance I U κ r A base) T := by
  intro t _ _ u hu
  dsimp only [epochInstance] at hu
  split_ifs at hu with hodd
  · exact refreshEdges_isEdgeUpdate _ _ u hu
  · exact False.elim (List.not_mem_nil hu)

/-- Every dynamic-instance prefix evaluated by `boundedTargetInstances` has only edge updates. -/
theorem boundedTargetInstances_historyEdgeOnly (I : Instance) (U F κ : ℝ)
    (A : MinRatioDataStructure) (fuel : ℕ) (base : Fin I.m → ℝ) :
    ∀ p ∈ boundedTargetInstances I U F κ A fuel base, HistoryEdgeOnly p.1 p.2 := by
  classical
  induction fuel generalizing base with
  | zero => intro p hp; exact False.elim (List.not_mem_nil hp)
  | succ fuel ih =>
    intro p hp
    unfold boundedTargetInstances at hp
    split_ifs at hp with hstop
    · exact False.elim (List.not_mem_nil hp)
    · rcases List.mem_cons.mp hp with rfl | htail
      · exact epochInstance_historyEdgeOnly I U κ (residual I F base) A base _
      · cases hfail : epochFirstFailure I U κ (residual I F base) A base I.m with
        | some k =>
          rw [hfail] at htail
          exact False.elim (List.not_mem_nil htail)
        | none =>
          rw [hfail] at htail
          exact ih _ p htail

/-- Every dynamic-instance prefix evaluated by `dataStructureSearchInstances` has only edge updates. -/
theorem dataStructureSearchInstances_historyEdgeOnly (I : Instance) (U κ : ℝ)
    (A : MinRatioDataStructure) (base : Fin I.m → ℝ) (B : ℕ) :
    ∀ p ∈ dataStructureSearchInstances I U κ A base B, HistoryEdgeOnly p.1 p.2 := by
  intro p hp
  unfold dataStructureSearchInstances at hp
  rcases List.mem_append.mp hp with h1 | h2
  · obtain ⟨F, _, hpF⟩ := List.mem_flatMap.mp h1
    exact boundedTargetInstances_historyEdgeOnly I U F κ A _ base p hpF
  · exact boundedTargetInstances_historyEdgeOnly I U _ κ A _ base p h2

/-- Every dynamic-instance prefix evaluated by `boundedFailureTargetInstances` (Theorem 4.6,
page 15) has only edge updates. -/
theorem boundedFailureTargetInstances_historyEdgeOnly (I : Instance) (U F κ : ℝ)
    (A : MinRatioDataStructureWithFailure) (fuel : ℕ) (base : Fin I.m → ℝ) :
    ∀ p ∈ boundedFailureTargetInstances I U F κ A fuel base, HistoryEdgeOnly p.1 p.2 := by
  classical
  induction fuel generalizing base with
  | zero => intro p hp; exact False.elim (List.not_mem_nil hp)
  | succ fuel ih =>
    intro p hp
    unfold boundedFailureTargetInstances at hp
    split_ifs at hp with hstop
    · exact False.elim (List.not_mem_nil hp)
    · rcases List.mem_cons.mp hp with rfl | htail
      · exact epochInstance_historyEdgeOnly I U κ (residual I F base) A.eraseFailure base _
      · cases hfail : epochFirstFailureWithAnswer I U κ (residual I F base) A base I.m with
        | some k =>
          rw [hfail] at htail
          exact False.elim (List.not_mem_nil htail)
        | none =>
          rw [hfail] at htail
          exact ih _ p htail

/-- Gradient scaling does not change the update batches, so it preserves `HistoryEdgeOnly`. -/
theorem scaleInstanceGradient_historyEdgeOnly_iff (D : DynamicInstance) (s : ℝ) (T : ℕ) :
    HistoryEdgeOnly (scaleInstanceGradient D s) T ↔ HistoryEdgeOnly D T :=
  Iff.rfl

/-! ### Fixed-graph / edge-only min-ratio interface -/

/-- Graph invariant asserting that the current graph equals a fixed graph `G₀`. -/
def MinRatioGraphFixed (G₀ : MGraph) (G : MGraph) : Prop :=
  G = G₀

/-- Graph invariant asserting that the current graph has fixed vertex set `V₀` and is connected. -/
def MinRatioGraphConnectedFixedV (V₀ : Finset ℕ) (G : MGraph) : Prop :=
  G.V = V₀ ∧ MinRatioGraphConnected G

/-- Stage invariant: the graph is the fixed graph `G₀`, and the lengths meet the range
`|log ℓ_e| ≤ Ψ` of Definition 4.4, item 5 (page 14). -/
def MinRatioStageFixed (G₀ : MGraph) (Ψ : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) : Prop :=
  G = G₀ ∧ MinRatioLengthsInRange Ψ G ℓ

/-- Stage invariant: the graph has vertex set `V₀` and is connected, and the lengths meet the
range `|log ℓ_e| ≤ Ψ` of Definition 4.4, item 5 (page 14). -/
def MinRatioStageConnectedFixedV (V₀ : Finset ℕ) (Ψ : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) : Prop :=
  MinRatioGraphConnectedFixedV V₀ G ∧ MinRatioLengthsInRange Ψ G ℓ

/-- On `G₀`, lengths in `[2^{-E}, 2^E]` meet the range `|log ℓ_e| ≤ Ψ` once `E ≤ Ψ`. -/
theorem MinRatioStageFixed.admits (G₀ : MGraph) {E : ℕ} {Ψ : ℝ} (hE : (E : ℝ) ≤ Ψ) :
    StageAdmits (MinRatioStageFixed G₀ Ψ) G₀ E :=
  fun _ hl => ⟨rfl, MinRatioLengthsInRange.of_lengthsWithin hE hl⟩

/-- Definition 4.5 (page 14) with failure, restricted to connected edge-only histories within
the size limits `(M, N)` whose lengths meet `|log ℓ_e| ≤ Ψ` at every stage. These are the history
hypotheses of ordered Theorem 5.1 (page 15). The length range is the quasi-polynomial bound of
Definition 4.4, item 5 (page 14), which Algorithm 2 uses to set its parameter `Ψ`. -/
def MinRatioSpecWithFailureEdgeOnlyConnectedUpTo (A : MinRatioDataStructureWithFailure)
    (κ α Ψ ε : ℝ) (M N : ℕ) : Prop :=
  ∀ (D : DynamicInstance) (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ),
    MinRatioHistoryValid D op T →
    HistoryEdgeOnly D T →
    MinRatioHistoryBounded D T M N →
    (∀ t ≤ T, MinRatioGraphConnected (D.G t)) →
    MinRatioHistoryLengthsInRange D T Ψ →
    MinRatioSpecOn A.eraseFailure κ α Ψ ε D η op T ∧
    (∀ t, t + 1 ≤ T → op (t + 1) = true → D.HiddenStable (t + 1) α Ψ →
      (minRatioFailureDirection A D η op t).isSome = true)

/-- Any edge-only connected specification satisfies `MinRatioSpecWithFailureUpToOn` for the
stage predicate `MinRatioStageConnectedFixedV V₀ Ψ`. -/
theorem MinRatioSpecWithFailureEdgeOnlyConnectedUpTo.toUpToOn_fixedV
    {A : MinRatioDataStructureWithFailure} {κ α Ψ ε : ℝ} {M N : ℕ}
    (hA : MinRatioSpecWithFailureEdgeOnlyConnectedUpTo A κ α Ψ ε M N)
    (V₀ : Finset ℕ) :
    MinRatioSpecWithFailureUpToOn (MinRatioStageConnectedFixedV V₀ Ψ) A κ α Ψ ε M N := by
  intro D η op T hvalid hsize hP
  have hEdge : HistoryEdgeOnly D T :=
    historyEdgeOnly_of_minRatioHistoryValid_fixedV hvalid (fun t ht => (hP t ht).1.1)
  exact hA D η op T hvalid hEdge hsize (fun t ht => (hP t ht).1.2) (fun t ht => (hP t ht).2)

/-- Any edge-only connected specification satisfies `MinRatioSpecWithFailureUpToOn` for the
stage predicate `MinRatioStageFixed G₀ Ψ` whenever `G₀` is connected. -/
theorem MinRatioSpecWithFailureEdgeOnlyConnectedUpTo.toUpToOn_fixedGraph
    {A : MinRatioDataStructureWithFailure} {κ α Ψ ε : ℝ} {M N : ℕ}
    (hA : MinRatioSpecWithFailureEdgeOnlyConnectedUpTo A κ α Ψ ε M N)
    (G₀ : MGraph) (hConn : MinRatioGraphConnected G₀) :
    MinRatioSpecWithFailureUpToOn (MinRatioStageFixed G₀ Ψ) A κ α Ψ ε M N :=
  (hA.toUpToOn_fixedV G₀.V).mono (fun G ℓ hG => by
    obtain ⟨rfl, hℓ⟩ := hG
    exact ⟨⟨rfl, hConn⟩, hℓ⟩)

/-- Any connected specification (allowing splits) restricts to edge-only connected histories. -/
theorem MinRatioSpecWithFailureConnectedUpTo.toEdgeOnly
    {A : MinRatioDataStructureWithFailure} {κ α Ψ ε : ℝ} {M N : ℕ}
    (hA : MinRatioSpecWithFailureConnectedUpTo A κ α Ψ ε M N) :
    MinRatioSpecWithFailureEdgeOnlyConnectedUpTo A κ α Ψ ε M N :=
  fun D η op T hvalid _ hsize hConn _ => hA D η op T hvalid hsize hConn

/-- Any unrestricted bounded specification restricts to edge-only connected histories. -/
theorem MinRatioSpecWithFailureUpTo.toEdgeOnlyConnected
    {A : MinRatioDataStructureWithFailure} {κ α Ψ ε : ℝ} {M N : ℕ}
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ ε M N) :
    MinRatioSpecWithFailureEdgeOnlyConnectedUpTo A κ α Ψ ε M N :=
  hA.connectedUpTo.toEdgeOnly

/-- Any all-history specification restricts to edge-only connected histories at any size limits. -/
theorem MinRatioSpecWithFailure.toEdgeOnlyConnectedUpTo
    {A : MinRatioDataStructureWithFailure} {κ α Ψ ε : ℝ}
    (hA : MinRatioSpecWithFailure A κ α Ψ ε) (M N : ℕ) :
    MinRatioSpecWithFailureEdgeOnlyConnectedUpTo A κ α Ψ ε M N :=
  (hA.upTo M N).toEdgeOnlyConnected

/-- Existence example showing that `MinRatioSpecWithFailureEdgeOnlyConnectedUpTo`,
`MinRatioStageFixed`, and `MinRatioStageConnectedFixedV` hold simultaneously on a genuinely
hidden-stable edge-only input history. -/
theorem minRatioSpecWithFailureEdgeOnlyConnectedUpTo_exists_example :
    ∃ (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (G₀ : MGraph),
      MinRatioSpecWithFailureEdgeOnlyConnectedUpTo A 1 1 0 1 1 1 ∧
      MinRatioSpecWithFailureUpToOn (MinRatioStageFixed G₀ 0) A 1 1 0 1 1 1 ∧
      MinRatioSpecWithFailureUpToOn (MinRatioStageConnectedFixedV G₀.V 0) A 1 1 0 1 1 1 ∧
      MinRatioGraphConnected G₀ ∧
      ∀ T, D.HiddenStable T 1 0 ∧
        MinRatioHistoryValid D (fun _ => true) T ∧
        HistoryEdgeOnly D T ∧
        MinRatioHistoryBounded D T 1 1 ∧
        (∀ t ≤ T, MinRatioStageFixed G₀ 0 (D.G t) (D.ℓ t)) ∧
        (∀ t ≤ T, MinRatioStageConnectedFixedV G₀.V 0 (D.G t) (D.ℓ t)) := by
  obtain ⟨A, hA, hex⟩ := minRatioSpecWithFailure_exists_example
  let G₀ : MGraph := minRatioExample.G 0
  have hConn : MinRatioGraphConnected G₀ := by
    intro u hu v hv
    have hu0 : u = 0 := Finset.mem_singleton.mp hu
    have hv0 : v = 0 := Finset.mem_singleton.mp hv
    subst hu0 hv0
    exact ⟨[], MGraph.IsWalk.nil 0⟩
  have hEdgeSpec : MinRatioSpecWithFailureEdgeOnlyConnectedUpTo A 1 1 0 1 1 1 :=
    hA.toEdgeOnlyConnectedUpTo 1 1
  refine ⟨A, minRatioExample, G₀, hEdgeSpec, hEdgeSpec.toUpToOn_fixedGraph G₀ hConn,
    hEdgeSpec.toUpToOn_fixedV G₀.V, hConn, fun T => ?_⟩
  have hLen : ∀ t, MinRatioLengthsInRange 0 (minRatioExample.G t) (minRatioExample.ℓ t) := by
    intro t e _
    simp [minRatioExample]
  refine ⟨(hex T).1, (hex T).2, ?_, ?_, fun t _ => ⟨rfl, hLen t⟩,
    fun t _ => ⟨⟨rfl, hConn⟩, hLen t⟩⟩
  · intro t _ _ u hu
    exact False.elim (List.not_mem_nil hu)
  · constructor
    · intro t _
      change ({0} : Finset ℕ).card ≤ 1
      simp
    · intro t _
      change ({0} : Finset ℕ).card ≤ 1
      simp

end MinCostFlow.IPM
