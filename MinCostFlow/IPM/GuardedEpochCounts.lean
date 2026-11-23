module

public import MinCostFlow.IPM.GuardedEpoch
import Lean.Elab.Tactic.Omega

/-!
# Counts for target epochs that may fail

The guarded epoch stops at its first failed coordinate or Query-budget
check. Before that operation, all remembered coordinates are interior,
so the operation-history contract applies even to a wrong target guess.
The last operation can return at most `m` edges. Thus it overruns the
`5m` Query cap by at most `m`, and all counts remain linear in `m`.
No hidden-stability claim is made here for guesses below the optimum.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- Number of Update--Detect pairs actually evaluated by a guarded scan. -/
def epochProcessed (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n : ℕ) : ℕ :=
  (epochFirstFailure I U κ r A base n).getD n

/-- The guarded scan never evaluates more pairs than its requested prefix. -/
theorem epochProcessed_le (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n : ℕ) : epochProcessed I U κ r A base n ≤ n := by
  unfold epochProcessed
  cases h : epochFirstFailure I U κ r A base n with
  | none => exact le_rfl
  | some k => exact (epochFirstFailure_some_spec I U κ r A base n k h).2.1

/-- All operations actually evaluated by the guarded scan have a valid
input history, including the final operation on which a check fails. -/
theorem guardedEpoch_history_valid (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n : ℕ) (hI : I.IsValid) (hbase : StrictlyInside I base) :
    MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate
      (2*epochProcessed I U κ r A base n) := by
  cases h : epochFirstFailure I U κ r A base n with
  | none =>
    have hg := (epochFirstFailure_none_iff I U κ r A base n).mp h
    have hs := epoch_guards_stored I U κ r A base n hbase (fun j hj => (hg j hj).1)
    apply epoch_history_valid_prefix I U κ r A base _ hI
    intro j hj
    exact hs j (by simp only [epochProcessed, h, Option.getD_none] at hj; omega)
  | some k =>
    have hk := epochFirstFailure_some_spec I U κ r A base n k h
    have hs := epoch_guards_stored I U κ r A base (k-1) hbase
      (fun j hj => (hk.2.2.2 j (by omega)).1)
    apply epoch_history_valid_prefix I U κ r A base _ hI
    intro j hj
    exact hs j (by simp only [epochProcessed, h, Option.getD_some] at hj; omega)

/-- The last returned edge list can exceed the Query cap by at most `m`
entries, since pending names are distinct graph edges. -/
theorem guardedEpoch_queries_le (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n : ℕ) :
    (epochState I U κ r A base (epochProcessed I U κ r A base n)).queries ≤ 6*I.m := by
  unfold epochProcessed
  cases h : epochFirstFailure I U κ r A base n with
  | none =>
    have hh := ((epochFirstFailure_none_iff I U κ r A base n).mp h n le_rfl).2
    exact hh.trans (by omega)
  | some k =>
    have hk := epochFirstFailure_some_spec I U κ r A base n k h
    cases k with
    | zero => omega
    | succ k =>
      have hprev := (hk.2.2.2 k (Nat.lt_succ_self k)).2
      have hcard : (epochState I U κ r A base (k+1)).pending.card ≤ I.m := by
        have hs : (epochState I U κ r A base (k+1)).pending ⊆ Finset.range I.m := by
          intro e he
          exact Finset.mem_range.mpr (epoch_pending_mem I U κ r A base (k+1) e he)
        exact (Finset.card_le_card hs).trans_eq (Finset.card_range I.m)
      have hrec : (epochState I U κ r A base (k+1)).queries =
          (epochState I U κ r A base k).queries+(epochState I U κ r A base (k+1)).pending.card := by rfl
      change (epochState I U κ r A base (k+1)).queries ≤ _
      rw [hrec]
      omega

/-- Arbitrary target guesses have bounded actual epoch counts, even when
a local check fails. There are at most `6m` Queries and Detect output
entries, and at most `12m` primitive coefficient-refresh updates. -/
theorem guardedEpoch_operation_bounds (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n : ℕ) (hI : I.IsValid) (hbase : StrictlyInside I base)
    (hA : MinRatioSpec A κ α Ψ ε) :
    let t := epochProcessed I U κ r A base n
    (epochState I U κ r A base t).queries ≤ 6*I.m ∧
      (epochState I U κ r A base t).detected ≤ 6*I.m ∧
      (epochState I U κ r A base t).updateSize ≤ 12*I.m := by
  dsimp only
  have hv := guardedEpoch_history_valid I U κ r A base n hI hbase
  have hq := guardedEpoch_queries_le I U κ r A base n
  have hd := epoch_detected_eq_queries I U κ r α Ψ ε A base _ _ hA hv le_rfl
  have hu := epoch_updateSize_le I U κ r A base (epochProcessed I U κ r A base n)
  exact ⟨hq, by rw [hd]; exact hq, by omega⟩

end MinCostFlow.IPM
