module

public import MinCostFlow.IPM.MinRatioWitness
import Lean.Elab.Tactic.Omega

/-!
# A mathematical implementation of Definition 4.5

The data structure records every scaled increment and every last Detect
report. Update chooses a qualifying circulation using only the current
instance. Query sums the stored increments. Detect computes the exact
set in Definition 4.5 (page 14). No efficiency is claimed for this
implementation. It shows the operation specification can hold, including
on prefixes that actually have a hidden witness.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- Mathematical storage for the reference data structure: the current
graph and lengths, the current operation index, all past increments,
and the most recent Detect report of each edge. -/
structure MinRatioReferenceState where
  G : MGraph
  ℓ : ℕ → ℝ
  clock : ℕ
  changes : ℕ → ℕ → ℝ
  last : ℕ → ℕ

/-- Exact detection from stored history, with no change at the detection
operation itself. -/
def referenceDetectSet (ε : ℝ) (s : MinRatioReferenceState) : Finset ℕ :=
  s.G.E.filter fun e => ε ≤ s.ℓ e * ∑ r ∈ Finset.Ioc (s.last e) s.clock, |s.changes r e|

/-- The actual scaled circulation on the current edge set, extended by
zero off the graph. -/
def referenceIncrement (G : MGraph) (g d : ℕ → ℝ) (η : ℝ) (e : ℕ) : ℝ :=
  if e ∈ G.E then -(η/G.inner g d)*d e else 0

/-- Update records the scaled increment with the sign of Definition 4.5. -/
def referenceUpdate (κ α : ℝ) (s : MinRatioReferenceState) (U : List MinCostFlow.Update)
    (g ℓ : ℕ → ℝ) (η : ℝ) : MinRatioReferenceState × (ℕ → ℝ) :=
  let G := s.G.applyBatch U
  let d := chooseMinRatioDirection G g ℓ κ α
  ({ G := G, ℓ := ℓ, clock := s.clock+1,
     changes := Function.update s.changes (s.clock+1) (referenceIncrement G g d η),
     last := s.last }, d)

/-- A causal mathematical implementation of the three operations in
Definition 4.5. The fixed parameters are captured by the operations. -/
def referenceMinRatio (κ α ε : ℝ) : MinRatioDataStructure where
  State := MinRatioReferenceState
  init G _ ℓ := ⟨G, ℓ, 0, fun _ _ => 0, fun _ => 0⟩
  update := referenceUpdate κ α
  query s e := ∑ r ∈ Finset.range (s.clock+1), s.changes r e
  detect s :=
    let S := referenceDetectSet ε s
    (S, {s with clock := s.clock+1, last := fun e => if e ∈ S then s.clock+1 else s.last e})

/-- At a Detect stage the shared dynamic instance has the same graph. -/
theorem detectStage_graph_eq (D : DynamicInstance) (op : ℕ → Bool) (T t : ℕ)
    (h : MinRatioHistoryValid D op T) (ht : t+1 ≤ T) (hop : op (t+1) = false) :
    D.G (t+1) = D.G t := by
  have hg := (h.1 (t+1) (by omega) ht).2
  have hu := (h.2.2.1 (t+1) (by omega) ht hop).1
  simpa only [Nat.add_sub_cancel, hu, MGraph.applyBatch, List.foldl_nil] using hg

/-- Stored history, graph, lengths, clock and last reports agree with the
abstract execution history. This invariant is proved for every prefix. -/
theorem referenceMinRatio_invariants (κ α ε : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) (h : MinRatioHistoryValid D op T) :
    ∀ t ≤ T,
      let s := minRatioState (referenceMinRatio κ α ε) D η op t
      s.G = D.G t ∧ s.ℓ = D.ℓ t ∧ s.clock = t ∧
      (∀ r e, s.changes r e = if r ≤ t then minRatioIncrement (referenceMinRatio κ α ε) D η op r e else 0) ∧
      (∀ e, s.last e = minRatioLast (referenceMinRatio κ α ε) D η op t e) := by
  classical
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨rfl, rfl, rfl, ?_, fun _ => rfl⟩
    intro r e
    by_cases hr : r = 0
    · subst r; rfl
    · change (0 : ℝ) = _
      simp only [Nat.le_zero, hr, ↓reduceIte]
  | succ t ih =>
    intro ht
    have hi := ih (Nat.le_of_succ_le ht)
    let s := minRatioState (referenceMinRatio κ α ε) D η op t
    change s.G = _ ∧ s.ℓ = _ ∧ s.clock = _ ∧ _ ∧ _ at hi
    have hgraph : s.G.applyBatch (D.U (t+1)) = D.G (t+1) := by
      rw [hi.1]
      exact (by simpa only [Nat.add_sub_cancel] using (h.1 (t+1) (by omega) ht).2.symm)
    cases hop : op (t+1) with
    | true =>
      have hstate : minRatioState (referenceMinRatio κ α ε) D η op (t+1) =
          (referenceUpdate κ α s (D.U (t+1)) (D.g (t+1)) (D.ℓ (t+1)) (η (t+1))).1 := by
        simp only [minRatioState, hop, ↓reduceIte]
        rfl
      rw [hstate]
      refine ⟨hgraph, rfl, by simpa only [referenceUpdate] using congrArg (·+1) hi.2.2.1, ?_, ?_⟩
      · intro r e
        change (Function.update s.changes (s.clock+1)
          (referenceIncrement (s.G.applyBatch (D.U (t+1))) (D.g (t+1))
            (chooseMinRatioDirection (s.G.applyBatch (D.U (t+1))) (D.g (t+1)) (D.ℓ (t+1)) κ α)
            (η (t+1)))) r e = _
        rw [hi.2.2.1]
        by_cases hr : r = t+1
        · subst r
          simp only [Function.update_self, le_refl, ↓reduceIte]
          have hdir : minRatioDirection (referenceMinRatio κ α ε) D η op t =
              chooseMinRatioDirection (D.G (t+1)) (D.g (t+1)) (D.ℓ (t+1)) κ α := by
            change chooseMinRatioDirection (s.G.applyBatch (D.U (t+1))) _ _ _ _ = _
            rw [hgraph]
          simp only [minRatioIncrement, hop, true_and, hdir,
            referenceIncrement, hgraph]
        · rw [Function.update_of_ne hr, hi.2.2.2.1]
          have heq : (r ≤ t) ↔ r ≤ t+1 := by omega
          simp only [heq]
      · intro e
        change s.last e = _
        simp only [minRatioLast, hop, Bool.true_eq_false, false_and, ↓reduceIte]
        exact hi.2.2.2.2 e
    | false =>
      have hstate : minRatioState (referenceMinRatio κ α ε) D η op (t+1) =
          ({s with clock := s.clock+1, last := fun e => if e ∈ referenceDetectSet ε s then s.clock+1 else s.last e} : MinRatioReferenceState) := by
        simp only [minRatioState, hop, Bool.false_eq_true, ↓reduceIte]
        rfl
      rw [hstate]
      refine ⟨hi.1.trans (detectStage_graph_eq D op T t h ht hop).symm, ?_,
        by change s.clock+1 = t+1; exact congrArg (·+1) hi.2.2.1, ?_, ?_⟩
      · exact hi.2.1.trans (h.2.2.1 (t+1) (by omega) ht hop).2.2.symm
      · intro r e
        change s.changes r e = _
        rw [hi.2.2.2.1]
        by_cases hr : r = t+1
        · subst r
          simp only [Nat.not_succ_le_self, ↓reduceIte, le_refl, minRatioIncrement,
            hop, Bool.false_eq_true, false_and]
        · have heq : (r ≤ t) ↔ r ≤ t+1 := by omega
          simp only [heq]
      · intro e
        change (if e ∈ referenceDetectSet ε s then s.clock+1 else s.last e) = _
        conv_rhs => unfold minRatioLast
        simp only [hop, true_and]
        change (if e ∈ referenceDetectSet ε s then s.clock+1 else s.last e) =
          if e ∈ referenceDetectSet ε s then t+1 else minRatioLast (referenceMinRatio κ α ε) D η op t e
        rw [hi.2.2.1]
        split_ifs
        · rfl
        · exact hi.2.2.2.2 e

/-- The reference implementation meets every operation guarantee of
Definition 4.5 (page 14). In particular, its ratio guarantee uses only
the hidden stability of the current prefix. -/
theorem referenceMinRatio_spec (κ α Ψ ε : ℝ) (ha : 0 < α) (hk : κ ≤ 1) :
    MinRatioSpec (referenceMinRatio κ α ε) κ α Ψ ε := by
  classical
  intro D η op T h
  have hinv := referenceMinRatio_invariants κ α ε D η op T h
  refine ⟨?_, ?_, ?_⟩
  · intro t ht e _
    have hi := hinv t ht
    change (∑ r ∈ Finset.range ((minRatioState (referenceMinRatio κ α ε) D η op t).clock+1),
        (minRatioState (referenceMinRatio κ α ε) D η op t).changes r e) = _
    rw [hi.2.2.1]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hi.2.2.2.1 r e, ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hr))]
  · intro t ht hop
    have hi := hinv t (Nat.le_of_succ_le ht)
    have hgraph : (minRatioState (referenceMinRatio κ α ε) D η op t).G.applyBatch (D.U (t+1)) = D.G (t+1) := by
      rw [hi.1]
      simpa only [Nat.add_sub_cancel] using (h.1 (t+1) (by omega) ht).2.symm
    have hdir : minRatioDirection (referenceMinRatio κ α ε) D η op t =
        chooseMinRatioDirection (D.G (t+1)) (D.g (t+1)) (D.ℓ (t+1)) κ α := by
      change chooseMinRatioDirection ((minRatioState (referenceMinRatio κ α ε) D η op t).G.applyBatch (D.U (t+1))) _ _ _ _ = _
      rw [hgraph]
    rw [hdir]
    exact ⟨chooseMinRatioDirection_circulation _ _ _ κ α,
      chooseMinRatioDirection_quality D (t+1) α Ψ κ ha hk⟩
  · intro t ht hop
    have hi := hinv t (Nat.le_of_succ_le ht)
    have hG := detectStage_graph_eq D op T t h ht hop
    have hℓ : (minRatioState (referenceMinRatio κ α ε) D η op t).ℓ = D.ℓ (t+1) :=
      hi.2.1.trans (h.2.2.1 (t+1) (by omega) ht hop).2.2.symm
    change referenceDetectSet ε (minRatioState (referenceMinRatio κ α ε) D η op t) = _
    unfold referenceDetectSet minRatioDetectSet
    rw [hi.1, ← hG, hℓ, hi.2.2.1]
    apply Finset.filter_congr
    intro e _
    have hsum : (∑ r ∈ Finset.Ioc ((minRatioState (referenceMinRatio κ α ε) D η op t).last e) t,
          |(minRatioState (referenceMinRatio κ α ε) D η op t).changes r e|) =
        ∑ r ∈ Finset.Ioc (minRatioLast (referenceMinRatio κ α ε) D η op t e) (t+1),
          |minRatioIncrement (referenceMinRatio κ α ε) D η op r e| := by
      rw [hi.2.2.2.2 e, Finset.sum_Ioc_succ_top (minRatioLast_le _ _ _ _ t e)]
      have hzero : minRatioIncrement (referenceMinRatio κ α ε) D η op (t+1) e = 0 := by
        simp only [minRatioIncrement, hop, Bool.false_eq_true, false_and, ↓reduceIte]
      rw [hzero, abs_zero, add_zero]
      apply Finset.sum_congr rfl
      intro r hr
      rw [hi.2.2.2.1 r e, ite_eq_left (Finset.mem_Ioc.mp hr).2]
    rw [hsum]

/-- A one-loop dynamic instance with a negative gradient and unit lengths.
The loop flow one is a hidden witness at every prefix. -/
def minRatioExample : DynamicInstance where
  G _ := { V := {0}, E := {0}, tail := fun _ => 0, head := fun _ => 0 }
  U _ := []
  g _ _ := -1
  ℓ _ _ := 1

/-- The reference contract is inhabited on an actual hidden stable input,
with all scalar parameters positive and no ratio hypothesis vacuous. -/
theorem minRatioSpec_exists_example :
    ∃ A : MinRatioDataStructure, MinRatioSpec A 1 1 0 1 ∧
      ∀ T, minRatioExample.HiddenStable T 1 0 ∧
        MinRatioHistoryValid minRatioExample (fun _ => true) T := by
  refine ⟨referenceMinRatio 1 1 1, referenceMinRatio_spec 1 1 0 1 (by norm_num) le_rfl, ?_⟩
  intro T
  constructor
  · refine ⟨fun _ _ => 1, fun _ _ => 1, ?_⟩
    intro t _
    simp [DynamicInstance.HiddenStableAt, IsValidPair, minRatioExample,
      MGraph.IsCirculation, MGraph.demand, MGraph.b, MGraph.inner, MGraph.norm1]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _ _
      exact ⟨trivial, rfl⟩
    · intro t _
      simp [minRatioExample, MGraph.IsValid]
    · intro t _ _ hfalse
      contradiction
    · intro t _ _ e _ _
      exact ⟨rfl, rfl⟩

/-- The same causal reference implementation meets the restated
Definition 4.5 by reporting success on every Update. -/
theorem referenceMinRatio_spec_withFailure (κ α Ψ ε : ℝ) (ha : 0 < α) (hk : κ ≤ 1) :
    MinRatioSpecWithFailure (referenceMinRatio κ α ε).withFailureAnswer κ α Ψ ε :=
  MinRatioSpec.withFailureAnswer _ κ α Ψ ε (referenceMinRatio_spec κ α Ψ ε ha hk)

/-- The extended operation contract is inhabited on a genuinely hidden
stable input, with all scalar parameters positive, just as the original
contract is. No failure is needed by this reference implementation. -/
theorem minRatioSpecWithFailure_exists_example :
    ∃ A : MinRatioDataStructureWithFailure, MinRatioSpecWithFailure A 1 1 0 1 ∧
      ∀ T, minRatioExample.HiddenStable T 1 0 ∧
        MinRatioHistoryValid minRatioExample (fun _ => true) T := by
  obtain ⟨A, hA, hex⟩ := minRatioSpec_exists_example
  exact ⟨A.withFailureAnswer, MinRatioSpec.withFailureAnswer A 1 1 0 1 hA, hex⟩

end MinCostFlow.IPM
