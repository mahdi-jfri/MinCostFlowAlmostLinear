module

public import MinCostFlow.HierPaths.BuildProgGameLoop

/-!
# Scheduling the memory for the model's child game

The original graph addresses stay fixed. The active table names a subsequence
of the original children. Each round that runs places a record at the arena
end, and the next round starts above that record.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Constant inputs of the game at one parent. The per-round jobs and core level
are computed from the model game. -/
structure BuildGameSchedule where
  base : BuildRoundData
  addrs : BuildRoundAddrs
  count : ℕ
  start : ℕ
  childAddr : ℕ → ℕ
  saved : ℕ
  directory : ℕ
  L' : ℕ

namespace BuildGameSchedule

/-- The children's initial intervals are consecutive and of equal length. -/
def offset (S : BuildGameSchedule) (c : ℕ) : ℕ := S.start + c * S.base.childSize

/-- Model after the given number of rounds. -/
def states (S : BuildGameSchedule) (t : ℕ) : ℕ → ChildState :=
  gameRun S.base.route S.base.host S.base.verts S.base.Δ S.base.L S.base.core S.base.M S.base.r
    S.base.childSize S.count S.offset t

/-- The active child at this position of the scan. -/
def child (S : BuildGameSchedule) (t i : ℕ) : ℕ :=
  (activeChildren S.count (S.states t)).getD i 0

/-- The active jobs at this round. -/
def round (S : BuildGameSchedule) (t : ℕ) : BuildRoundData :=
  { S.base with jobs := modelGameJobs S.base.childSize S.count S.offset S.childAddr (S.states t)
                q := coreLevel S.base.M S.base.r S.base.childSize }

/-- The next free address after a prefix of rounds. -/
def heap (S : BuildGameSchedule) : ℕ → ℕ
  | 0 => S.addrs.heap
  | t + 1 =>
    let B := S.round t
    let A := { S.addrs with heap := S.heap t }
    if B.jobs.count = 0 then A.heap else B.record A + 2 + B.jobs.count

/-- This schedule has a fixed round directory and a growing arena. -/
def data (S : BuildGameSchedule) : BuildGameLoopData :=
  ⟨S.round,fun t => { S.addrs with heap := S.heap t }, S.child, S.start, S.saved,
    S.directory,49*S.L'+1⟩

/-- The next count is exactly the number of cut replies. -/
theorem count_succ (S : BuildGameSchedule) (t : ℕ) :
    (S.round (t+1)).jobs.count = (S.round t).indices.length := by
  unfold round
  change (activeChildren S.count (S.states (t+1))).length = _
  rw [show S.states (t+1) = gameRound S.base.route S.base.host S.base.verts S.base.Δ S.base.L
    S.base.core S.base.M S.base.r S.base.childSize S.count S.offset (S.states t) from rfl,
    activeChildren_gameRound]
  have he := modelGameJobs_indices S.base.core S.base.M S.base.r S.base.childSize S.count
    S.offset S.childAddr (S.states t)
  simpa [BuildRoundData.indices] using (congrArg List.length he).symm

/-- No cuts are selected from an empty active table. -/
theorem indices_empty (S : BuildGameSchedule) {t : ℕ} (h : (S.round t).jobs.count = 0) :
    (S.round t).indices = [] := by
  rw [BuildRoundData.indices, batchJobIndices, cutReplyIndices, h]
  rfl

/-- The final count is zero as soon as every child has a certificate. -/
theorem count_eq_zero (S : BuildGameSchedule) {t : ℕ}
    (h : ∀ c < S.count, ∃ C, (S.states t c).saved = some C) :
    (S.round t).jobs.count = 0 := by
  change (activeChildren S.count (S.states t)).length = 0
  rw [List.length_eq_zero_iff, activeChildren, List.filter_eq_nil_iff]
  intro c hc hNone
  obtain ⟨C,hC⟩ := h c (List.mem_range.mp hc)
  simp [hC] at hNone

/-- The word-level loop uses the model counts, the exact round sizes, and
the same addresses other than the heap cursor. -/
theorem loopFit_of_bounds {w : ℕ} {S : BuildGameSchedule} {mem : ℕ → ℕ}
    (hWord : 3 < 2^w) (hLimit : S.directory + S.data.limit < 2^w)
    (hDone : ∀ c < S.count, ∃ C, (S.states S.data.limit c).saved = some C)
    (hDir : S.directory + S.data.limit ≤ S.addrs.replies)
    (hPre : ∀ t < S.data.limit, ∀ before, GameLoopTrace w S.data mem t before →
      (S.round t).jobs.count ≠ 0 →
      (buildGameStepContract w (S.round t) (S.data.addrs t) S.start S.saved (S.child t)).pre
        ((S.round t).stepArgs (S.data.addrs t) S.start S.saved) before) :
    GameLoopFit w S.data mem := by
  refine ⟨hWord,by omega,hLimit,?_,S.count_eq_zero hDone,?_,?_,?_,hPre⟩
  · intro t _ j hj h₃ h₆
    have hft : ∀ a ∈ List.range 19, a ≠ 3 → a ≠ 6 →
        (S.data.args (t+1)).getD a 0 = (S.data.args t).getD a 0 := by
      simp [List.range_succ,BuildGameLoopData.args,data,BuildRoundData.stepArgs,BuildRoundData.args,round]
    exact hft j (List.mem_range.mpr hj) h₃ h₆
  · intro t _ h
    change (S.round t).jobs.count = 0 at h
    refine ⟨(S.count_succ t).trans (congrArg List.length (S.indices_empty h)),?_⟩
    change S.heap (t+1) = S.heap t
    simp only [heap,h,ite_true]
  · intro t _ h
    change (S.round t).jobs.count ≠ 0 at h
    refine ⟨S.count_succ t,?_⟩
    change S.heap (t+1) = _
    simp only [heap,h,ite_false]
    rfl
  · intro t ht
    change S.directory + t < S.addrs.replies
    omega

end BuildGameSchedule

end MinCostFlow.HierPaths
