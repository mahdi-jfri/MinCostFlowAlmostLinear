module

public import MinCostFlow.HierPaths.BuildProgBatchSpec

/-!
# From the active-child replies to the batched router input

The core's tag selects the children that need matching edges in this round.
For each selected child the two packed sides agree with the request in the
game model. Reading the selected replies in order gives the router batch.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- A cut reply requests a matching between its padded sides. -/
def batchJobPair (J : BuildGameJobs) (core : ℕ → Graph → CoreResult) (q s i : ℕ) :
    Finset ℕ × Finset ℕ :=
  match J.answer core q i with
  | .cut U => (shiftSet (J.offset i) (bisectOf s U),
    shiftSet (J.offset i) (Finset.range s \ bisectOf s U))
  | .expander _ => (∅, ∅)

/-- The active children that received cuts, in the order of the scan. -/
def batchJobIndices (J : BuildGameJobs) (core : ℕ → Graph → CoreResult) (q : ℕ) : List ℕ :=
  cutReplyIndices (fun i => J.answer core q i) J.count

/-- The pairs used by the single common call in this round. -/
def batchJobPairs (J : BuildGameJobs) (core : ℕ → Graph → CoreResult) (q s : ℕ) :
    List (Finset ℕ × Finset ℕ) :=
  (batchJobIndices J core q).map (batchJobPair J core q s)

/-- The pointer table after the scan (`replies[0..J.count]`, ending with the prepared block
end `replies[J.count] = J.prepPrefix core q h J.count`), together with all prepared child blocks. -/
def GameRepliesAt (J : BuildGameJobs) (core : ℕ → Graph → CoreResult) (q h replies : ℕ)
    (mem : ℕ → ℕ) : Prop :=
  mem (replies + J.count) = J.prepPrefix core q h J.count ∧
  ∀ i < J.count, mem (replies + i) = J.prepPrefix core q h i ∧
    PreparedChildAt mem (J.prepPrefix core q h i) (J.prepPrefix core q h (i + 1))
      (J.graph i).n (J.offset i) (J.answer core q i)

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- A selected index is in range and its reply is a cut. -/
theorem mem_batchJobIndices {J : BuildGameJobs} {core : ℕ → Graph → CoreResult} {q i : ℕ} :
    i ∈ batchJobIndices J core q ↔ i < J.count ∧ ∃ U, J.answer core q i = .cut U := by
  simp only [batchJobIndices, cutReplyIndices, List.mem_filter, List.mem_range, decide_eq_true_eq]
  cases hc : J.answer core q i <;> simp [coreTag]

/-- The prepared replies provide the tags needed by the selection pass. -/
theorem GameRepliesAt.tags {J : BuildGameJobs} {core : ℕ → Graph → CoreResult}
    {q h replies out : ℕ} {mem : ℕ → ℕ}
    (hAt : GameRepliesAt J core q h replies mem)
    (hEnd : J.prepPrefix core q h J.count ≤ out) :
    ReplyTagsAt mem replies J.count out fun i => J.answer core q i := by
  intro i hi
  obtain ⟨hPtr, hBlock⟩ := hAt.2 i hi
  have hSpan := hBlock.core_end_le
  have hBound := J.prepPrefix_mono core q h (show i + 1 ≤ J.count by omega)
  let start := J.prepPrefix core q h i
  let ans := J.answer core q i
  have hCore : ListAt mem start (coreResultWords ans) := hBlock.1
  have hTag := coreTag_at hCore
  have hLen := coreTag_lt_length ans
  rw [hPtr]
  exact ⟨by dsimp [ans] at hLen; omega, hTag⟩

/-- The cut requests are stored at the addresses read by the gather loop (`mem[replies + j + 1] - 2 * s`). -/
theorem GameRepliesAt.batchRows {J : BuildGameJobs} {core : ℕ → Graph → CoreResult}
    {q h replies cuts out s : ℕ} {mem : ℕ → ℕ}
    (hAt : GameRepliesAt J core q h replies mem)
    (hCuts : ListAt mem cuts (batchJobIndices J core q))
    (hBelow : replies + J.count + 1 ≤ out)
    (hEnd : J.prepPrefix core q h J.count ≤ out)
    (hSizes : ∀ i < J.count, (J.graph i).n = s)
    (hU : ∀ i < J.count, ∀ U, J.answer core q i = .cut U → U ⊆ Finset.range s)
    (hEven : 2 * (s / 2) = s) :
    BatchRowsAt mem replies cuts out s (batchJobPairs J core q s) ∧
      ∀ i < (batchJobPairs J core q s).length,
        (buildBatchRow (batchJobPairs J core q s) i).length = s := by
  let idxs := batchJobIndices J core q
  let pairs := batchJobPairs J core q s
  have hLen : pairs.length = idxs.length := List.length_map _
  have hRow : ∀ i (hi : i < pairs.length),
      ∃ U, let j := idxs[i]'(hLen ▸ hi)
      j < J.count ∧ J.answer core q j = .cut U ∧
      buildBatchRow pairs i = (requestSides s (J.offset j) U).1 ++ (requestSides s (J.offset j) U).2 := by
    intro i hi
    have hj : idxs[i]'(hLen ▸ hi) ∈ idxs := List.getElem_mem _
    obtain ⟨hj, U, hu⟩ := mem_batchJobIndices.mp hj
    refine ⟨U, hj, hu, ?_⟩
    have hp : pairs.getD i (∅, ∅) = batchJobPair J core q s (idxs[i]'(hLen ▸ hi)) := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_map ..
    simp only [buildBatchRow, hp, requestSides, batchJobPair, hu]
  constructor
  · intro i hi
    dsimp only
    change i < pairs.length at hi
    obtain ⟨U, hj, hAns, hEq⟩ := hRow i hi
    let j := idxs[i]'(hLen ▸ hi)
    have hIdx : mem (cuts + i) = j := hCuts _ _
    obtain ⟨_, hBlock⟩ := hAt.2 j hj
    change J.answer core q j = .cut U at hAns
    rw [hAns, hSizes j hj] at hBlock
    obtain ⟨_, e, _, hEndRep, hPayload⟩ := hBlock
    have hNextPtr : mem (replies + j + 1) = J.prepPrefix core q h (j + 1) := by
      have hAdd : replies + j + 1 = replies + (j + 1) := by omega
      rw [hAdd]
      by_cases hlt : j + 1 < J.count
      · exact (hAt.2 (j + 1) hlt).1
      · have heq : j + 1 = J.count := by omega
        rw [heq]; exact hAt.1
    have hLe := (J.prepPrefix_mono core q h (show j + 1 ≤ J.count by omega)).trans hEnd
    rw [hIdx, hNextPtr, hEndRep]
    have hSub : e + 3 * s - 2 * s = e + s := by omega
    rw [hSub, hEq]
    exact ⟨by omega, by omega, by omega, hPayload⟩
  · intro i hi
    obtain ⟨U, hj, hu, hEq⟩ := hRow i hi
    have hSide := requestSides_lengths (off := J.offset (idxs[i]'(hLen ▸ hi))) (hU _ hj U hu) hEven
    rw [hEq, List.length_append, hSide.1, hSide.2]
    omega

/-- Every row in a nonempty batch has two sides of half the child size. -/
theorem batchJobPairs_halves {J : BuildGameJobs} {core : ℕ → Graph → CoreResult}
    {q s : ℕ} (hU : ∀ i < J.count, ∀ U, J.answer core q i = .cut U → U ⊆ Finset.range s)
    (hEven : 2 * (s / 2) = s) :
    ∀ p ∈ batchJobPairs J core q s, p.1.card = s / 2 ∧ p.2.card = s / 2 := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  obtain ⟨hi, U, hu⟩ := mem_batchJobIndices.mp hi
  have hLen := requestSides_lengths (off := J.offset i) (hU i hi U hu) hEven
  simp only [batchJobPair, hu]
  simpa only [requestSides, finsetWords, Finset.length_sort] using hLen

/-- The router receives one pair per selected child. -/
theorem length_batchJobPairs (J : BuildGameJobs) (core : ℕ → Graph → CoreResult) (q s : ℕ) :
    (batchJobPairs J core q s).length = (batchJobIndices J core q).length := List.length_map _

end MinCostFlow.HierPaths
