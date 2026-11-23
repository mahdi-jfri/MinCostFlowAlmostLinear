module

public import MinCostFlow.DynSpanner.Program.DynSpannerAmortSum
public import MinCostFlow.DynSpanner.Program.DynSpannerDSPrefix

/-!
# The cost of a step does not change when updates are appended

The potential of the data structure of Theorem 8.2 (`DynSpannerDSBank.lean`) subtracts the costs
`dsStepAmortCost` of the steps run so far. A new batch appends updates to the list `us`. We show
that the cost of a step `k < |us|` stays the same (`dsStepAmortCost_append`): the step reads only
`us[k]` and model states `runState us t` for `t ≤ k`, and these do not change when updates are
appended (`runState_append`). We also bound the cost of a step that reads a record of `len` words
by the cost with `len = 0` plus `1350 len` (`dsStepCostAt_le`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-- The cost bound of a step with `0 < j` depends on the list of updates only through the model
states up to step `k`. -/
theorem dsStepPosCostModel_congr_us (G₀ : MGraph) (impl : SparsifyImpl) (L q k : ℕ)
    (us us' : List Update) (u : Update) (mMax vCap eCap len : ℕ)
    (h : ∀ t ≤ k, runState (L := L) G₀ q (canonicalSparsify impl) us' t =
      runState (L := L) G₀ q (canonicalSparsify impl) us t) :
    dsStepPosCostModel ⟨G₀, impl, L, q, k, us', u⟩ mMax vCap eCap len =
      dsStepPosCostModel ⟨G₀, impl, L, q, k, us, u⟩ mMax vCap eCap len := by
  have hk := h k le_rfl
  have hlr : ∀ i, runState (L := L) G₀ q (canonicalSparsify impl) us' (lastRebuild q L i k) =
      runState (L := L) G₀ q (canonicalSparsify impl) us (lastRebuild q L i k) :=
    fun i => h _ (lastRebuild_le q L i k)
  have hRev : ∀ i v, modelRevSet ⟨G₀, impl, L, q, k, us', u⟩ i v =
      modelRevSet ⟨G₀, impl, L, q, k, us, u⟩ i v := fun i v => by
    simp only [modelRevSet, hlr]
  have hHm : (⟨G₀, impl, L, q, k, us', u⟩ : StepPosModel).H_mid =
      (⟨G₀, impl, L, q, k, us, u⟩ : StepPosModel).H_mid := by
    funext i
    simp only [StepPosModel.H_mid, StepPosModel.st, hk]
  have hDm : (⟨G₀, impl, L, q, k, us', u⟩ : StepPosModel).inDom_mid =
      (⟨G₀, impl, L, q, k, us, u⟩ : StepPosModel).inDom_mid := by
    funext i
    simp only [StepPosModel.inDom_mid, StepPosModel.G', StepPosModel.st, hk]
  have hCS : modelCandSet ⟨G₀, impl, L, q, k, us', u⟩ =
      modelCandSet ⟨G₀, impl, L, q, k, us, u⟩ := by
    ext e
    simp only [modelCandSet, Finset.mem_filter, hRev, StepPosModel.S_prev, StepPosModel.G',
      StepPosModel.st, StepPosModel.j, hk]
  simp only [dsStepPosCostModel, dsStepPosAffCostModel, modelCandRevSum, hCS, hRev,
    modelOldSum, StepPosModel.st, StepPosModel.res, StepPosModel.G',
    StepPosModel.S_prev, StepPosModel.H_lt, hHm, StepPosModel.piLt_mid,
    hDm, StepPosModel.E_aff, StepPosModel.J, StepPosModel.embJH,
    StepPosModel.j, hk]

/-- **The cost of a step is stable under appending updates.** For `k < |us|`, the cost
`dsStepAmortCost` of step `k` on `us ++ vs` is its cost on `us`. -/
theorem dsStepAmortCost_append (G₀ : MGraph) (impl : SparsifyImpl) (mMax L q vCap eCap : ℕ)
    (us vs : List Update) {k : ℕ} (hk : k < us.length) :
    dsStepAmortCost G₀ impl mMax L q vCap eCap (us ++ vs) k =
      dsStepAmortCost G₀ impl mMax L q vCap eCap us k := by
  have hget : (us ++ vs)[k]? = us[k]? := List.getElem?_append_left hk
  have hst : ∀ t ≤ k, runState (L := L) G₀ q (canonicalSparsify impl) (us ++ vs) t =
      runState (L := L) G₀ q (canonicalSparsify impl) us t :=
    fun t ht => runState_append G₀ q (canonicalSparsify impl) us vs t (by omega)
  have hres : runStepOut (L := L) G₀ q (canonicalSparsify impl) (us ++ vs) k =
      runStepOut (L := L) G₀ q (canonicalSparsify impl) us k := by
    simp only [runStepOut, hget, hst k le_rfl]
  have hreemb : runStepReembSet (L := L) G₀ q (canonicalSparsify impl) (us ++ vs) k =
      runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us k := by
    simp only [runStepReembSet, hget, hst k le_rfl]
  have hcost : dsStepCostAt G₀ impl mMax L q vCap eCap (us ++ vs) k 0 =
      dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 := by
    unfold dsStepCostAt
    rw [hget]
    rcases us[k]? with _ | u
    · rfl
    · simp only [hst k le_rfl]
      split_ifs
      · rfl
      · exact dsStepPosCostModel_congr_us G₀ impl L q k us (us ++ vs) u mMax vCap eCap 0 hst
  rw [dsStepAmortCost_eq, dsStepAmortCost_eq, hres, hreemb, hcost]

/-- The cost of a step that reads a record of `len` words is at most its cost with `len = 0`
plus `1350 len`. -/
theorem dsStepCostAt_le (G₀ : MGraph) (impl : SparsifyImpl) (mMax L q vCap eCap : ℕ)
    (us : List Update) (k len : ℕ) :
    dsStepCostAt G₀ impl mMax L q vCap eCap us k len ≤
      dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 + 1350 * len := by
  unfold dsStepCostAt
  rcases us[k]? with _ | u
  · simp
  · split_ifs
    · simp only [dsStepZeroCost]
      omega
    · simp only [dsStepPosCostModel, dsStepPosCost, dsStepPosEpilogueCost]
      omega

/-- A sum of the first `n` entries of a list (with `0` past its end) is at most its sum. -/
theorem sum_range_getD_le_sum : ∀ (l : List ℕ) (n : ℕ),
    ∑ r ∈ Finset.range n, l.getD r 0 ≤ l.sum
  | [], n => by simp
  | a :: l, 0 => by simp
  | a :: l, n + 1 => by
    rw [Finset.sum_range_succ']
    have ih := sum_range_getD_le_sum l n
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.sum_cons]
    omega

/-- **The batch loop in terms of `dsStepAmortCost`.** The bound of the loop on the slice `U`
from `k₀` is at most the sum of the costs `dsStepAmortCost` of its steps, plus `1410` per word of
the records and `820`. -/
theorem dsUpdateLoopCost_le (G₀ : MGraph) (impl : SparsifyImpl) (mMax L q vCap eCap : ℕ)
    (us U : List Update) (lens : List ℕ) (k₀ : ℕ) :
    dsUpdateLoopCost G₀ impl mMax L q vCap eCap us U lens k₀ ≤
      ∑ r ∈ Finset.range U.length, dsStepAmortCost G₀ impl mMax L q vCap eCap us (k₀ + r) +
        1410 * lens.sum + 820 := by
  have hstep : ∀ r ∈ Finset.range U.length,
      dsStepCostAt G₀ impl mMax L q vCap eCap us (k₀ + r) (lens.getD r 0) + 35 * L + 520 ≤
        dsStepCostAt G₀ impl mMax L q vCap eCap us (k₀ + r) 0 + 35 * L + 520 +
          1350 * lens.getD r 0 := fun r _ => by
    have := dsStepCostAt_le G₀ impl mMax L q vCap eCap us (k₀ + r) (lens.getD r 0)
    omega
  have h1 := Finset.sum_le_sum hstep
  have hlens := sum_range_getD_le_sum lens U.length
  have hsplit :
      ∑ r ∈ Finset.range U.length, dsStepAmortCost G₀ impl mMax L q vCap eCap us (k₀ + r) =
      ∑ r ∈ Finset.range U.length,
          (dsStepCostAt G₀ impl mMax L q vCap eCap us (k₀ + r) 0 + 35 * L + 520) +
        90 * ∑ r ∈ Finset.range U.length,
          (runStepOut (L := L) G₀ q (canonicalSparsify impl) us (k₀ + r)).D.card +
        90 * ∑ r ∈ Finset.range U.length,
          (runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us (k₀ + r)).card +
        240 * ∑ r ∈ Finset.range U.length,
          (runStepOut (L := L) G₀ q (canonicalSparsify impl) us (k₀ + r)).UH.length +
        240 * U.length := by
    simp only [dsStepAmortCost_eq, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
      Finset.card_range, smul_eq_mul]
    ring
  have h2 : ∑ r ∈ Finset.range U.length,
      (dsStepCostAt G₀ impl mMax L q vCap eCap us (k₀ + r) 0 + 35 * L + 520 +
        1350 * lens.getD r 0) =
      ∑ r ∈ Finset.range U.length,
          (dsStepCostAt G₀ impl mMax L q vCap eCap us (k₀ + r) 0 + 35 * L + 520) +
        1350 * ∑ r ∈ Finset.range U.length, lens.getD r 0 := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  unfold dsUpdateLoopCost
  omega

end

end MinCostFlow.DynSpanner.Program
