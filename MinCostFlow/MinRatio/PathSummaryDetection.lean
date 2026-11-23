module

public import MinCostFlow.MinRatio.PathPayloadLaws
public import MinCostFlow.MinRatio.PathPayloadFits

/-!
# Detection through path summaries

The proof of Theorem 5.1 (pages 29–30) finds edges with nonnegative
accounts using dynamic trees. A segment maximum is nonnegative exactly
when some edge in that segment is ready. The proofs below include vertex
nodes and empty paths, which have no detector entry. They justify skipping
a whole segment whose summary is below the reporting threshold.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

/-- Summary of a path's vertex and edge values. -/
def summarizePath : List (Option PathEdgeValue) → PathSummary
  | [] => .empty
  | v :: rest => (PathSummary.single v).combine (summarizePath rest)

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

/-- A combined segment has a ready detector exactly when either part does. -/
theorem detectorMax_ready (a b : Option ℤ) :
    (∃ z, detectorMax a b = some z ∧ 0 ≤ z) ↔
      (∃ z, a = some z ∧ 0 ≤ z) ∨ (∃ z, b = some z ∧ 0 ≤ z) := by
  cases a <;> cases b <;> simp [detectorMax, le_max_iff]

/-- A path summary reports precisely the existence of a ready edge. -/
theorem summarizePath_ready (values : List (Option PathEdgeValue)) :
    (∃ z, (summarizePath values).detector = some z ∧ 0 ≤ z) ↔
      ∃ v, some v ∈ values ∧ 0 ≤ v.detector := by
  induction values with
  | nil => simp [summarizePath, PathSummary.empty]
  | cons value rest ih =>
    change (∃ z, detectorMax (PathSummary.single value).detector (summarizePath rest).detector =
      some z ∧ 0 ≤ z) ↔ _
    rw [detectorMax_ready, ih]
    cases value with
    | none => simp [PathSummary.single, PathSummary.empty]
    | some v => simp [PathSummary.single, eq_comm]

/-- A path without a ready detector can be skipped without missing an edge. -/
theorem summarizePath_no_ready {values : List (Option PathEdgeValue)}
    (h : ¬ ∃ z, (summarizePath values).detector = some z ∧ 0 ≤ z) :
    ∀ v, some v ∈ values → v.detector < 0 := by
  intro v hv
  apply lt_of_not_ge
  intro hn
  exact h ((summarizePath_ready values).mpr ⟨v, hv, hn⟩)

/-- Every present segment detector is an account from the segment. -/
theorem summarizePath_detector_mem {values : List (Option PathEdgeValue)} {z : ℤ}
    (hz : (summarizePath values).detector = some z) :
    ∃ v, some v ∈ values ∧ v.detector = z := by
  induction values generalizing z with
  | nil => simp [summarizePath, PathSummary.empty] at hz
  | cons value rest ih =>
    cases value with
    | none =>
      obtain ⟨v, hv, hdet⟩ := ih (by simpa [summarizePath, PathSummary.single,
        PathSummary.empty, PathSummary.combine, detectorMax] using hz)
      exact ⟨v, List.mem_cons_of_mem _ hv, hdet⟩
    | some v =>
      cases hrest : (summarizePath rest).detector with
      | none =>
        exact ⟨v, List.mem_cons_self, by
          simpa [summarizePath, PathSummary.single, PathSummary.combine, detectorMax, hrest] using hz⟩
      | some y =>
        have hm : max v.detector y = z := by
          simpa [summarizePath, PathSummary.single, PathSummary.combine, detectorMax, hrest] using hz
        by_cases hy : y ≤ v.detector
        · exact ⟨v, List.mem_cons_self, (max_eq_left hy).symm.trans hm⟩
        · obtain ⟨x, hx, hdet⟩ := ih hrest
          exact ⟨x, List.mem_cons_of_mem _ hx, hdet.trans
            ((max_eq_right (le_of_lt (lt_of_not_ge hy))).symm.trans hm)⟩

/-- Path sums fit when the format has room for the length of the segment
times a uniform absolute bound on its gradients and lengths. The detector
maximum needs only the width of one account. -/
theorem summarizePath_fits_of_bound {h L : ℕ} {values : List (Option PathEdgeValue)}
    (B : ℤ) (hB : 0 ≤ B)
    (hRoom : 2 * ((values.length : ℤ) * B) < (Num.capacity h L : ℤ))
    (hEdge : ∀ v, some v ∈ values →
      -B ≤ v.gradient ∧ v.gradient ≤ B ∧ -B ≤ v.length ∧ v.length ≤ B ∧
        Num.Fits h L v.detector) :
    PathSummaryFits h L (summarizePath values) := by
  have hsum (xs : List (Option PathEdgeValue))
      (hb : ∀ v, some v ∈ xs → -B ≤ v.gradient ∧ v.gradient ≤ B ∧
        -B ≤ v.length ∧ v.length ≤ B) :
      let S := (xs.length : ℤ) * B
      (-S) ≤ (summarizePath xs).gradient ∧ (summarizePath xs).gradient ≤ S ∧
      (-S) ≤ (summarizePath xs).length ∧ (summarizePath xs).length ≤ S := by
    induction xs with
    | nil => simp [summarizePath, PathSummary.empty]
    | cons x xs ih =>
      obtain ⟨hglo, hghi, hllo, hlhi⟩ := ih (fun v hv => hb v (List.mem_cons_of_mem _ hv))
      cases x with
      | none =>
        simp only [summarizePath, PathSummary.single, PathSummary.empty, PathSummary.combine,
          zero_add, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        exact ⟨by omega, by omega, by omega, by omega⟩
      | some v =>
        obtain ⟨hglo', hghi', hllo', hlhi'⟩ := hb v List.mem_cons_self
        simp only [summarizePath, PathSummary.single, PathSummary.combine,
          List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        exact ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨hglo, hghi, hllo, hlhi⟩ := hsum values fun v hv =>
    ⟨(hEdge v hv).1, (hEdge v hv).2.1, (hEdge v hv).2.2.1, (hEdge v hv).2.2.2.1⟩
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
  cases hz : (summarizePath values).detector with
  | none => trivial
  | some z =>
    obtain ⟨v, hv, hdet⟩ := summarizePath_detector_mem hz
    exact hdet ▸ (hEdge v hv).2.2.2.2

end MinCostFlow.MinRatio
