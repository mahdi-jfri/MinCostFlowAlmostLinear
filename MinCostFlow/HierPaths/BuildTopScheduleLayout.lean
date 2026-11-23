module

public import MinCostFlow.HierPaths.BuildTopScheduleAt

/-!
# Address layout for the depth schedule

The schedule is followed by one pointer cell per depth boundary and then
by the reply directories. Reserving the padded terminal count for each
reply directory makes the addresses independent of the returned graphs.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-- The pointer cell at depth zero is initialized with the root directory. -/
def buildTopSchedulePointer (table n j : ℕ) : ℕ := table + 13 * n + j

/-- Each reply directory reserves at most the number of padded terminals. -/
def buildTopScheduleReplies (table n x j : ℕ) : ℕ :=
  buildTopSchedulePointer table n (n + 1) + j * 2 ^ x

/-- The initial heap lies beyond the schedule and all its directories. -/
def buildTopScheduleEnd (table n x : ℕ) : ℕ := buildTopScheduleReplies table n x n

/-- A stride of one terminal count covers all the parent replies at a depth. -/
theorem buildTopSchedule_replySpan (x b j : ℕ) : numGroups x b j ≤ 2 ^ x := by
  rw [← numGroups_mul_groupSize (b := b) (j := j)]
  exact Nat.le_mul_of_pos_right _ groupSize_pos

/-- Each row, both of its pointer cells, and its reply directory fit below the heap. -/
theorem buildTopSchedule_disjoint {table n x b j : ℕ} (hj : j < n) :
    table + 13 * j + 13 ≤ buildTopSchedulePointer table n j ∧
    buildTopSchedulePointer table n j + 1 = buildTopSchedulePointer table n (j + 1) ∧
    buildTopSchedulePointer table n (j + 1) < buildTopScheduleReplies table n x j ∧
    buildTopScheduleReplies table n x j + numGroups x b j ≤ buildTopScheduleEnd table n x := by
  have hspan := buildTopSchedule_replySpan x b j
  have hnext : (j + 1) * 2 ^ x ≤ n * 2 ^ x := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hnext
  unfold buildTopScheduleEnd buildTopScheduleReplies buildTopSchedulePointer
  omega

/-- The next depth cannot overwrite an earlier reply directory. -/
theorem buildTopSchedule_replyOrder {table n x b i j : ℕ} (hij : i < j) :
    buildTopScheduleReplies table n x i + numGroups x b i ≤
      buildTopScheduleReplies table n x j := by
  have hspan := buildTopSchedule_replySpan x b i
  have hnext : (i + 1) * 2 ^ x ≤ j * 2 ^ x := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hnext
  unfold buildTopScheduleReplies
  omega

end MinCostFlow.HierPaths

end
