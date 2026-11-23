module

public import MinCostFlow.DynSpanner.Program.DynSpannerUpdateLoopDefs

/-!
# The model up to time `k` sees only the first `k` updates

The data structure of Theorem 8.2 keeps the list of updates it has applied so far. When a new
batch `U` comes, the batch loop runs on the list `us ++ U` from time `us.length`. This file shows
that the facts the data structure keeps about `us` stay true for `us ++ U`, since the model at a
time `k ≤ us.length` reads only the first `k` updates.

* `runState_append`, `runStepOut_append`: the state and the step output at time `k`.
* `revHistoryInv_append`: the reverse walk lists of `RevHistoryInv`.
* `dsStepGenAt_append`: the bound on the growth of the generation word in one step.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-- The state of the model at time `k ≤ us.length` does not depend on updates after `us`. -/
theorem runState_append {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) (us vs : List Update) :
    ∀ k ≤ us.length,
      runState (L := L) G₀ q sparsify (us ++ vs) k = runState (L := L) G₀ q sparsify us k
  | 0, _ => rfl
  | k + 1, hk => by
    have hlt : k < us.length := hk
    have hget : (us ++ vs)[k]? = us[k]? := List.getElem?_append_left hlt
    simp only [runState, hget, runState_append G₀ q sparsify us vs k (Nat.le_of_lt hlt)]

/-- The step output at time `k < us.length` does not depend on updates after `us`. -/
theorem runStepOut_append {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) (us vs : List Update) {k : ℕ}
    (hk : k < us.length) :
    runStepOut (L := L) G₀ q sparsify (us ++ vs) k = runStepOut (L := L) G₀ q sparsify us k := by
  have hget : (us ++ vs)[k]? = us[k]? := List.getElem?_append_left hk
  simp only [runStepOut, hget, runState_append G₀ q sparsify us vs k (Nat.le_of_lt hk)]

/-- `RevHistoryInv` at a time `k ≤ us.length` reads the model only at the times of the last
rebuilds, which are at most `k`. -/
theorem revHistoryInv_append {L : ℕ} {G₀ : MGraph} {q : ℕ}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut} {us : List Update} (vs : List Update)
    {k : ℕ} {x : DynSpannerMeta L} (hk : k ≤ us.length)
    (h : RevHistoryInv G₀ q sparsify us k x) :
    RevHistoryInv G₀ q sparsify (us ++ vs) k x := by
  intro i
  have hle : lastRebuild q L i.1 k ≤ us.length := le_trans (lastRebuild_le q L i.1 k) hk
  have hst := runState_append (L := L) G₀ q sparsify us vs _ hle
  have hi := h i
  simp only at hi ⊢
  rw [hst]
  exact hi

/-- The bound `dsStepGenAt` of step `k < us.length` does not depend on updates after `us`. -/
theorem dsStepGenAt_append (G₀ : MGraph) (impl : SparsifyImpl) (L q : ℕ)
    (us vs : List Update) {k : ℕ} (hk : k < us.length) :
    dsStepGenAt G₀ impl L q (us ++ vs) k = dsStepGenAt G₀ impl L q us k := by
  have hget : (us ++ vs)[k]? = us[k]? := List.getElem?_append_left hk
  simp only [dsStepGenAt, hget,
    runState_append (L := L) G₀ q (canonicalSparsify impl) us vs k (Nat.le_of_lt hk)]

end

end MinCostFlow.DynSpanner.Program
