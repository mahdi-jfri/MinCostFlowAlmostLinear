module

public import MinCostFlow.IPM.FailureEpoch
import Lean.Elab.Tactic.Omega

/-!
# Counts for epochs stopped by an explicit failure

A failed Update is counted, but it is not followed by Detect or Query.
The completed-pair index therefore differs from the attempted-Update
index by at most one. The existing guarded-epoch counters bound the
new counts because explicit failure can only shorten the guarded
prefix. This proves the per-epoch bounds used in the restated Theorem 4.6,
including failed tests, without a hidden-stability hypothesis.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- Completed Detect calls in a failure-aware epoch. The last Update
contributes none if its answer was an explicit failure. -/
def epochCompletedWithAnswer (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructureWithFailure)
    (base : Fin I.m → ℝ) (n : ℕ) : ℕ := by
  classical
  exact match epochFirstFailureWithAnswer I U κ r A base n with
  | none => n
  | some k =>
    if (epochUpdateWithFailure I U κ r A (epochState I U κ r A.eraseFailure base (k-1))).2.isNone = true
    then k-1 else k

/-- Detect never follows the failed Update. In particular its call
count is no greater than the number of attempted Updates. -/
theorem epochCompletedWithAnswer_le (I : Instance) (U κ r : ℝ)
    (A : MinRatioDataStructureWithFailure) (base : Fin I.m → ℝ) (n : ℕ) :
    epochCompletedWithAnswer I U κ r A base n ≤ epochProcessedWithAnswer I U κ r A base n := by
  classical
  unfold epochCompletedWithAnswer epochProcessedWithAnswer
  cases h : epochFirstFailureWithAnswer I U κ r A base n with
  | none => exact le_rfl
  | some k => simp only [Option.getD_some]; split_ifs <;> omega

/-- All three recorded edge-operation counters are monotone in a
completed-pair prefix. This is purely a property of the causal loop. -/
theorem epoch_counters_mono (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t n : ℕ) (htn : t ≤ n) :
    (epochState I U κ r A base t).queries ≤ (epochState I U κ r A base n).queries ∧
      (epochState I U κ r A base t).detected ≤ (epochState I U κ r A base n).detected ∧
      (epochState I U κ r A base t).updateSize ≤ (epochState I U κ r A base n).updateSize := by
  induction n, htn using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl, le_rfl⟩
  | succ n _ ih =>
    have hq : (epochState I U κ r A base n).queries ≤ (epochState I U κ r A base (n+1)).queries := by
      change _ ≤ (epochState I U κ r A base n).queries+_
      omega
    have hd : (epochState I U κ r A base n).detected ≤ (epochState I U κ r A base (n+1)).detected := by
      change _ ≤ (epochState I U κ r A base n).detected+_
      omega
    have hu : (epochState I U κ r A base n).updateSize ≤ (epochState I U κ r A base (n+1)).updateSize := by
      change _ ≤ (epochState I U κ r A base n).updateSize+_
      omega
    exact ⟨ih.1.trans hq, ih.2.1.trans hd, ih.2.2.trans hu⟩

/-- Queries performed by the completed Detect calls. A full flow read
is added only when the whole scan succeeds, not after a failure. -/
def failureEpochQueryCount (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructureWithFailure)
    (base : Fin I.m → ℝ) (n : ℕ) : ℕ :=
  (epochState I U κ r A.eraseFailure base (epochCompletedWithAnswer I U κ r A base n)).queries+
    if (epochFirstFailureWithAnswer I U κ r A base n).isNone then I.m else 0

/-- Total output size of Detect calls actually completed. -/
def failureEpochDetectSize (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructureWithFailure)
    (base : Fin I.m → ℝ) (n : ℕ) : ℕ :=
  (epochState I U κ r A.eraseFailure base (epochCompletedWithAnswer I U κ r A base n)).detected

/-- Primitive coefficient updates include the batch delivered to the
last Update even when that Update returns failure. -/
def failureEpochUpdateSize (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructureWithFailure)
    (base : Fin I.m → ℝ) (n : ℕ) : ℕ :=
  (epochState I U κ r A.eraseFailure base (epochProcessedWithAnswer I U κ r A base n)).updateSize

/-- An attempted epoch has at most `n` Update and Detect calls, `7m`
Queries including its final read, `6m` Detect output entries, and `12m`
primitive coefficient updates. Failure answers and wrong guesses are
included. The bounds use only the unconditional operation clauses. -/
theorem failureEpoch_operation_bounds (I : Instance) (U κ r α Ψ ε : ℝ)
    (A : MinRatioDataStructureWithFailure) (base : Fin I.m → ℝ) (n : ℕ)
    (hI : I.IsValid) (hbase : StrictlyInside I base) (hA : MinRatioSpecWithFailure A κ α Ψ ε) :
    epochProcessedWithAnswer I U κ r A base n ≤ n ∧
      epochCompletedWithAnswer I U κ r A base n ≤ n ∧
      failureEpochQueryCount I U κ r A base n ≤ 7*I.m ∧
      failureEpochDetectSize I U κ r A base n ≤ 6*I.m ∧
      failureEpochUpdateSize I U κ r A base n ≤ 12*I.m := by
  have hu := epochProcessedWithAnswer_le I U κ r A base n
  have hd := epochCompletedWithAnswer_le I U κ r A base n
  have hp := epochProcessed_le I U κ r A.eraseFailure base n
  have hqueries := guardedEpoch_queries_le I U κ r A.eraseFailure base n
  have hcounts := guardedEpoch_operation_bounds I U κ r α Ψ ε A.eraseFailure base n hI hbase hA.1
  have hm := epoch_counters_mono I U κ r A.eraseFailure base _ _ (hd.trans hu)
  have hum := epoch_counters_mono I U κ r A.eraseFailure base _ _ hu
  refine ⟨hu.trans hp, hd.trans (hu.trans hp), ?_, ?_, ?_⟩
  · unfold failureEpochQueryCount
    have hq := hm.1.trans hqueries
    split_ifs <;> omega
  · exact hm.2.1.trans hcounts.2.1
  · exact hum.2.2.trans hcounts.2.2

end MinCostFlow.IPM
