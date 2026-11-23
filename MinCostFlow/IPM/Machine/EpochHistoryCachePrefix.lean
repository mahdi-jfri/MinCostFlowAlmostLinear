module

public import MinCostFlow.IPM.Machine.EpochHistoryCache

/-!
# Holding a coordinate until its edge is inserted again

The Detect input keeps all its old coordinates. The next Update
refreshes exactly the copied report. The same property for earlier
stages survives when this pair is appended to the history.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM.Machine

/-- Cached coordinates can change only across stages whose batch
inserts the corresponding edge. -/
def EpochHistoryCacheStable (I : Instance) (A : MinRatioDataStructureWithFailure)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (base : Fin I.m → ℝ) : Prop :=
  ∀ t<T,∀ e : Fin I.m,D.NotInsertedBetween e t (t+1) →
    epochHistoryCache I A D eta op (t+1) base e=epochHistoryCache I A D eta op t base e

/-- The initial cache has no earlier stage. -/
theorem epochHistoryCacheStable_zero (I : Instance) (A : MinRatioDataStructureWithFailure)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (base : Fin I.m → ℝ) :
    EpochHistoryCacheStable I A D eta op 0 base :=
  fun _ ht => (Nat.not_lt_zero _ ht).elim

/-- The coordinate invariance in Definition 4.4, item 4 (page 14), holds
through the new pair. The actual copied Detect list is essential for
the even stage. -/
theorem epochHistoryCacheStable_append (I : Instance) (A : MinRatioDataStructureWithFailure)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (i : ℕ)
    (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ) (base : Fin I.m → ℝ)
    (hset : es.toFinset=(A.detect (minRatioState A.eraseFailure D eta op (2*i))).1)
    (hold : EpochHistoryCacheStable I A D eta op (2*i) base) :
    EpochHistoryCacheStable I A (appendHistoryIteration D (2*i) es g l)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) (2*i+1+1) base := by
  intro t ht e hnot
  by_cases htOld : t<2*i
  · rw [epochHistoryCache_past I A D eta op (2*i) es g l actual base (t+1) (by omega),
      epochHistoryCache_past I A D eta op (2*i) es g l actual base t htOld.le]
    apply hold t htOld e
    intro j hj hj' u hu
    have hU : (appendHistoryIteration D (2*i) es g l).U j=D.U j := by
      simp only [appendHistoryIteration,appendHistoryStage,Function.update_of_ne (by omega : j≠2*i+1),
        Function.update_of_ne (by omega : j≠2*i+1+1)]
    exact hnot j hj hj' u (hU.symm ▸ hu)
  · by_cases htDetect : t=2*i
    · subst t
      rw [epochHistoryCache_detect,epochHistoryCache_past I A D eta op (2*i) es g l actual base (2*i) le_rfl]
    · have htUpdate : t=2*i+1 := by omega
      subst t
      exact epochHistoryCache_update_of_notInserted I A D eta op i es g l actual base e hset hnot

end MinCostFlow.IPM.Machine
