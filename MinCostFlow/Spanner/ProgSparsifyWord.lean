module

public import MinCostFlow.Spanner.ProgSparsifyCore

@[expose] public section

/-!
# The Word Size of the Sparsify Core

The pre of `sparsifyCoreContract` asks for `SparsifyCoreWordOK`: the word size fits Tasks 2 and 3
on every output of Tasks 1 and 2. The word bounds of Tasks 2 and 3 grow with the heap ends `v1`
and `v2` that the tasks before return, and they grow by exactly that amount. So it is enough to
check the two word bounds at heap end `0` plus the caps on `v1` and `v2`. This is
`sparsifyCoreWordOK_of_width`.

The cap on `v1` is `Task1Input.maxHeapEnd`, from the post of `task1Contract`. The cap on `v2` is
`Task2Input.maxHeapEnd`, from `Task2OutAt`, and it is the cap at heap end `0` plus `v1`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited

/-- The Task 2 heap end cap moves with `v1`. -/
lemma toT2_maxHeapEnd (impl : SpannerToolImpl) (inp : Task1Input) (v1 : ℕ) :
    Task2Input.maxHeapEnd impl (inp.toT2 v1) = Task2Input.maxHeapEnd impl (inp.toT2 0) + v1 := by
  simp only [Task2Input.maxHeapEnd, Task2Input.staticEndCap, Task2Input.embVertSum,
    Task2Input.nodesAddr, Task2Input.queueAddr, Task2Input.eWVertStampAddr,
    Task2Input.procStampAddr, Task2Input.vcongNumAddr, Task2Input.vHeadAddr,
    Task2Input.vhatStampAddr, Task2Input.compEdgeDelRoundAddr, Task2Input.vhatOffsetAddr,
    Task2Input.compEdgeBaseAddr, Task2Input.dsHandlesAddr, Task2Input.embWJAddr, Task1Input.toT2]
  omega

/-- The Task 2 word bound grows by at most `v1`. -/
lemma toT2_maxWordBound_le (impl : SpannerToolImpl) (inp : Task1Input) (v1 : ℕ) :
    Task2Input.maxWordBound impl (inp.toT2 v1) ≤ Task2Input.maxWordBound impl (inp.toT2 0) + v1 := by
  unfold Task2Input.maxWordBound
  rw [toT2_maxHeapEnd]
  simp only [Task2Input.embVertSum, Task1Input.toT2]
  refine max_le ?_ (le_trans (le_max_right _ _) (Nat.le_add_right _ _))
  have := le_max_left (Task2Input.maxHeapEnd impl (inp.toT2 0) + 3)
    (max (Task2Input.eta1Cap impl inp.J *
      (2 * Task2Input.gammaExpCap impl inp.J *
        max (impl.pathDS.params.gDel (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m)
          (impl.pathDS.params.gDel (WitnessCoreInput.dWInt impl.constructExpander)
            (Task1Input.mwCap impl inp.J)) *
        max (impl.pathDS.params.phiOutDen (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m)
          (impl.pathDS.params.phiOutDen (WitnessCoreInput.dWInt impl.constructExpander)
            (Task1Input.mwCap impl inp.J)) *
        (length inp.J inp.embJH + 1) * (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1)) *
      Task1Input.phiDenCap impl inp.J +
      2 * Task1Input.mwCap impl inp.J * maxDeg inp.J * Task1Input.phiDenCap impl inp.J + 2)
    (max (Task1Input.mwCap impl inp.J * Task2Input.gammaExpCap impl inp.J * (length inp.J inp.embJH + 1) +
        ∑ eJ ∈ Finset.range inp.J.m, (inp.embJH eJ).verts.length + 4)
      (Task2Input.eta1Cap impl inp.J * inp.J.m + 2 * Task1Input.mwCap impl inp.J + 2)))
  omega

/-- The Task 3 word bound grows by at most `v2`. -/
lemma toT3_maxWordBound_le (impl : SpannerToolImpl) (inp : Task1Input) (v2 : ℕ) :
    Task3Input.maxWordBound impl (inp.toT3 v2) ≤ Task3Input.maxWordBound impl (inp.toT3 0) + v2 := by
  have hH : Task3Input.maxHeapEnd impl (inp.toT3 v2) =
      Task3Input.maxHeapEnd impl (inp.toT3 0) + v2 := by
    simp only [Task3Input.maxHeapEnd, Task3Input.staticEndCap, Task1Input.toT3]
    omega
  unfold Task3Input.maxWordBound
  simp only [Task1Input.toT3] at hH ⊢
  rw [hH]
  refine max_le ?_ (le_trans (le_max_right _ _) (Nat.le_add_right _ _))
  have := le_max_left (Task3Input.maxHeapEnd impl (inp.toT3 0) + 3)
    (max (eta2Bound inp.J * Task1Input.tau2Cap impl inp.J * maxDeg inp.J *
        Task1Input.phiDenCap impl inp.J + 2)
      (max (inp.J.m * Task1Input.phiDenCap impl inp.J + 2)
        (3 * Task1Input.mwCap impl inp.J + 2 * inp.J.m + 4)))
  simp only [Task1Input.toT3] at this
  omega

/-- `SparsifyCoreWordOK` from the word bounds of Tasks 2 and 3 at heap end `0`, shifted by the
heap-end caps of Tasks 1 and 2. The condition mentions only `w` and the input. -/
theorem sparsifyCoreWordOK_of_width {impl : SpannerToolImpl} {inp : Task1Input} {w : ℕ}
    (hw2 : (inp.toT2 0).WordWidthOK impl w ∧
      Task2Input.maxWordBound impl (inp.toT2 0) + inp.maxHeapEnd impl < 2 ^ w)
    (hw3 : (inp.toT3 0).WordWidthOK impl w ∧
      Task3Input.maxWordBound impl (inp.toT3 0) + Task2Input.maxHeapEnd impl (inp.toT2 0) +
        inp.maxHeapEnd impl < 2 ^ w) :
    SparsifyCoreWordOK impl inp w := by
  intro memPre mem1 v1 hT1 hv1
  obtain ⟨⟨h2a, h2b, -⟩, h2c⟩ := hw2
  obtain ⟨⟨h3a, h3b, -⟩, h3c⟩ := hw3
  refine ⟨⟨h2a, h2b, ?_⟩, fun mem2 v2 hT2 => ⟨h3a, h3b, ?_⟩⟩
  · exact lt_of_le_of_lt (toT2_maxWordBound_le impl inp v1) (by omega)
  · have hv2 : v2 ≤ Task2Input.maxHeapEnd impl (inp.toT2 v1) := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, -⟩ := hT2
      exact h
    rw [toT2_maxHeapEnd] at hv2
    exact lt_of_le_of_lt (toT3_maxWordBound_le impl inp v2) (by omega)

end MinCostFlow.Spanner
