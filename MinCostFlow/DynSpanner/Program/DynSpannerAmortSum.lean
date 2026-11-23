module

public import MinCostFlow.DynSpanner.Program.DynSpannerAmortZero

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The amortized cost of the batch loop, summed over the updates

The batch loop of the program runs one step per update. For step `k` it pays the cost bound of
the step `dsStepCostAt … k 0` and an overhead of `35 L + 420 + 90 |D| + 240 |U_H| + 160`
(`dsStepAmortCost`; the term `1350 len` or `1320 len` for reading the update is paid separately,
by the length of the input). We want the total over the first `T` updates to be the time bound of
Theorem 8.2 (page 39), `45 L q K₁ E_L Δ₁ Λ · Enc(us[0, T))`, times a constant `C` free of the
input, plus `1440` times the potential `Φ = Σ_i |E(H_i)|` of the start.

The plan is the sum of Lemma 5.9 (`lemma_5_9_sum_of_step_bounds`) applied to
`f k = (g k - 1440 (Φ_k - Φ_{k+1})) / C`: the potential terms telescope to `1440 (Φ_0 - Φ_T)`.
* For a restart the per-step bound is `stepZero_budget`.
* For a step with `0 < j` the per-step bound is the hypothesis `hpos` of
  `updateLoop_amortized_sum`.
The totals of `|U_H|` and `|D|` that the sum needs come from `lemma_5_9`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-- The cost bound that the batch loop pays for step `k`, without the term for reading the
update: the bound of the step with `len = 0` and the overhead of the loop. -/
noncomputable def dsStepAmortCost (G₀ : MGraph) (impl : SparsifyImpl) (mMax L q vCap eCap : ℕ)
    (us : List Update) (k : ℕ) : ℕ :=
  let res := runStepOut (L := L) G₀ q (canonicalSparsify impl) us k
  dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 + 35 * L + 520 + 90 * res.D.card +
    90 * (runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us k).card +
    240 * res.UH.length + 240

/-- The definition of `dsStepAmortCost`, for use in other files. -/
lemma dsStepAmortCost_eq (G₀ : MGraph) (impl : SparsifyImpl) (mMax L q vCap eCap : ℕ)
    (us : List Update) (k : ℕ) :
    dsStepAmortCost G₀ impl mMax L q vCap eCap us k =
      dsStepCostAt G₀ impl mMax L q vCap eCap us k 0 + 35 * L + 520 +
        90 * (runStepOut (L := L) G₀ q (canonicalSparsify impl) us k).D.card +
        90 * (runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us k).card +
        240 * (runStepOut (L := L) G₀ q (canonicalSparsify impl) us k).UH.length + 240 := by
  unfold dsStepAmortCost; rfl

/-- Under deletions and splits, the graph after `k' ≤ T` updates has at most
`n₀ + (number of splits in the first T updates)` vertices. -/
lemma n_take_le {G₀ : MGraph} {us : List Update} (hBV : G₀.BatchIsValid us)
    (hds : ∀ u ∈ us, isDelOrSplit u) {T k' : ℕ} (hk' : k' ≤ T) :
    (G₀.applyBatch (us.take k')).n ≤ G₀.n + batchSplitCount (us.take T) := by
  obtain ⟨hBVk, hdsk, -⟩ := batchIsValid_take us G₀ k' hBV hds
  rw [n_applyBatch_of_delOrSplit _ G₀ hBVk hdsk]
  have h : us.take k' = (us.take T).take k' := by rw [List.take_take, min_eq_left hk']
  rw [h]
  exact Nat.add_le_add_left (batchSplitCount_take_le _ _) _

/-- **The amortized cost of the batch loop.** Let `C ≥ dsInitCostFactor impl + 3000`, and
assume that every step with `0 < j` costs at most `C` times its budget in the sum of Lemma 5.9
plus `1440` times the drop of the potential `levelPot` (`hpos`). Then the cost of the first `T`
steps is at most `C` times the time bound of Theorem 8.2 plus `1440 Φ_0`. The restarts are
handled by `stepZero_budget`, which uses `1 ≤ max p_s p_t` (`hp`). -/
theorem updateLoop_amortized_sum (impl : SparsifyImpl) {G₀ : MGraph} {mMax L q vCap eCap : ℕ}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 2 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {T nMax : ℕ} (hT : T ≤ us.length) (hnMax : G₀.n + batchSplitCount (us.take T) ≤ nMax)
    (hn_pow : max nMax 1 ≤ q ^ L) (hp : 1 ≤ max impl.p_s impl.p_t)
    (C : ℝ) (hC : (dsInitCostFactor impl : ℝ) + 3000 ≤ C)
    (hpos : ∀ k (hk : k < T), 0 < chooseLevel L q (k + 1) →
      let P := (canonicalSparsifyParams impl mMax).absorbTime
      let res := runStepOut (L := L) G₀ q (canonicalSparsify impl) us k
      (dsStepAmortCost G₀ impl mMax L q vCap eCap us k : ℝ) ≤
        C * (((L : ℝ) + 1) *
            ((G₀.applyBatch (us.take k)).updateEnc (us[k]'(lt_of_lt_of_le hk hT)) : ℝ) +
          (res.UH.length : ℝ) + (res.D.card : ℝ) +
          ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ) *
            (22 * (P.K_t + P.K_s + 1) *
              (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
                P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) * ((G₀.maxDeg : ℝ) + 1) *
              (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t))) +
        1440 * ((levelPot (runState (L := L) G₀ q (canonicalSparsify impl) us k) : ℝ) -
          (levelPot (runState (L := L) G₀ q (canonicalSparsify impl) us (k + 1)) : ℝ))) :
    let P := (canonicalSparsifyParams impl mMax).absorbTime
    ∑ k ∈ Finset.range T, (dsStepAmortCost G₀ impl mMax L q vCap eCap us k : ℝ) ≤
      C * (45 * (L : ℝ) * (q : ℝ) * (P.K_t + P.K_s + 1) *
        (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
          P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) * ((G₀.maxDeg : ℝ) + 1) *
        (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t) *
        (G₀.batchEnc (us.take T) : ℝ)) +
      1440 * (levelPot (runState (L := L) G₀ q (canonicalSparsify impl) us 0) : ℝ) := by
  intro P
  set sp := canonicalSparsify impl
  set g : ℕ → ℝ := fun k => (dsStepAmortCost G₀ impl mMax L q vCap eCap us k : ℝ) with hg
  set Φ : ℕ → ℝ := fun k => (levelPot (runState (L := L) G₀ q sp us k) : ℝ) with hΦ
  have hq1 : 1 ≤ q := by omega
  have hSpec : SparsifySpec mMax P sp := canonicalSparsify_spec_absorb impl mMax
  obtain ⟨-, -, hUH, -, hD, -⟩ := lemma_5_9 hVG₀ hL hq hGm₀ hSpec hBV hds hT hnMax hn_pow
  have hF0 : (0 : ℝ) < (dsInitCostFactor impl : ℝ) + 3000 := by positivity
  have hCpos : 0 < C := lt_of_lt_of_le hF0 hC
  -- Nonnegativity of the factor of the budget.
  obtain ⟨hEL1, -, -, -⟩ := expFactor_bounds P.hγ_c P.hγ_ℓ L G₀.maxDeg
  have hK1 : 0 ≤ P.K_t + P.K_s + 1 := by linarith [P.hK_t, P.hK_s]
  have h1nm : (1 : ℝ) ≤ (nMax : ℝ) + (G₀.m : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) G₀.m]
  have hΛ0 : 0 ≤ (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t) :=
    pow_nonneg (by linarith [Real.log_nonneg h1nm]) _
  set f : ℕ → ℝ := fun k => (g k - 1440 * (Φ k - Φ (k + 1))) / C with hf
  have hsum := lemma_5_9_sum_of_step_bounds (P := P) (sparsify := sp) (G₀ := G₀) hL hq hT
    hn_pow hUH hD f
    (fun k hk hj0 => by
      have hn : ∀ k' ≤ k + 1, (G₀.applyBatch (us.take k')).n ≤ nMax := fun k' hk' =>
        le_trans (n_take_le hBV hds (le_trans hk' hk)) hnMax
      have h := stepZero_budget (vCap := vCap) (eCap := eCap) impl hVG₀ hL hq hGm₀ hBV hds
        (lt_of_lt_of_le hk hT) hj0 hn hp
      simp only at h
      rw [hf]
      dsimp only
      rw [div_le_iff₀ hCpos]
      have hB : 0 ≤ ((L : ℝ) + 1) *
            ((G₀.applyBatch (us.take k)).updateEnc (us[k]'(lt_of_lt_of_le hk hT)) : ℝ) +
          ((runStepOut (L := L) G₀ q sp us k).UH.length : ℝ) +
          ((runStepOut (L := L) G₀ q sp us k).D.card : ℝ) +
          ((max nMax 1 : ℕ) : ℝ) * (12 * ((L : ℝ) * (q : ℝ)) * (P.K_t + P.K_s + 1) *
            (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
              P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) * ((G₀.maxDeg : ℝ) + 1) *
            (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t)) := by
        have : (0 : ℝ) ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
            P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) := by linarith
        positivity
      have hmono := mul_le_mul_of_nonneg_right hC hB
      simp only [hg, hΦ, dsStepAmortCost]
      linarith [h, hmono])
    (fun k hk hj => by
      have h := hpos k hk hj
      simp only at h
      rw [hf]
      dsimp only
      rw [div_le_iff₀ hCpos]
      simp only [hg, hΦ]
      linarith [h])
  simp only at hsum
  -- Telescoping.
  have hgf : ∀ k, g k = C * f k + 1440 * (Φ k - Φ (k + 1)) := fun k => by
    simp only [hf]; field_simp; ring
  have htel : ∑ k ∈ Finset.range T, (Φ k - Φ (k + 1)) = Φ 0 - Φ T :=
    Finset.sum_range_sub' Φ T
  have hsplit : ∑ k ∈ Finset.range T, g k =
      C * ∑ k ∈ Finset.range T, f k + 1440 * (Φ 0 - Φ T) := by
    rw [Finset.sum_congr rfl fun k _ => hgf k, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, htel]
  have hΦT : 0 ≤ Φ T := by simp only [hΦ]; positivity
  have hCs := mul_le_mul_of_nonneg_left hsum hCpos.le
  change ∑ k ∈ Finset.range T, g k ≤ _
  rw [hsplit]
  simp only [hΦ] at hΦT ⊢
  linarith [hCs, hΦT]

end

end MinCostFlow.DynSpanner.Program
