module

public import MinCostFlow.SparseCore.SparseCoreRecourseBase

/-!
# Size and recourse constants of the sparse core on bundle graphs

These replace the constants of `SparseCoreRunBounds` and `SparseCoreRecourseBase` for the branch
on bundle graphs (`BundleTreeState`). None of them depends on a degree.

* Each bucket spanner starts on a bundle graph with at most `2 M` vertices, since every bundle
  holds an end of an edge, and it receives at most `bundleSplitBudget k M ≤ 2 (56 M + 1)` vertex
  splits. So `bundleNMax M = 2 M + 2 (56 M + 1)` bounds its vertex population.
* One input update causes at most one deletion and, through at most `56 log² (N + 2)` new roots
  per update (paper Lemma 5.4, page 18), at most two bundle splits per new root in each bucket. This
  gives the ratio `bundleUCRatio N`, which replaces `coreUCRatio N Δ₀`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.DynSpanner

/-- A bound on the vertex population of every bucket spanner of an epoch. -/
def bundleNMax (M : ℕ) : ℕ :=
  2 * M + 2 * (56 * M + 1)

/-- The factor `n^{1/L}` of Theorem 8.2 at the population bound `bundleNMax M`. -/
noncomputable def bundleNRoot (L M : ℕ) : ℝ :=
  ((max (bundleNMax M) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))

/-- The polylogarithmic size factor of the static sparsifier at the population bound. -/
noncomputable def bundleLambdaS (P_b : SparsifyParams) (M : ℕ) : ℝ :=
  (1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2)) ^ P_b.p_s

/-- The polylogarithmic size and time factor of the static sparsifier at the population bound. -/
noncomputable def bundleLambda (P_b : SparsifyParams) (M : ℕ) : ℝ :=
  (1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2)) ^ (max P_b.p_s P_b.p_t)

/-- Bundle-graph updates per input update in one bucket: one deletion and two splits for each
of at most `56 log² (N + 2)` new roots. -/
noncomputable def bundleUCRatio (N : ℕ) : ℝ :=
  1 + 112 * (Real.log ((N : ℝ) + 2)) ^ 2

/-- Spanner output updates per bundle-graph update (Theorem 8.2, page 39). -/
noncomputable def bundleBucketRecUH (L : ℕ) (P_b : SparsifyParams) (M : ℕ) : ℝ :=
  2 + 12 * (L : ℝ) * bundleNRoot L M * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M

/-- Re-embedded spanner edges per bundle-graph update (Theorem 8.2, page 39). -/
noncomputable def bundleBucketRecD (L : ℕ) (P_b : SparsifyParams) (M : ℕ) : ℝ :=
  6 * (L : ℝ) * bundleNRoot L M * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) *
    bundleLambdaS P_b M

/-- Output updates of one branch per input update, with `B` length buckets per component. It has
the shape of `coreRecoursePerQ` with `bundleUCRatio N` in place of `coreUCRatio N Δ₀`. -/
noncomputable def bundleRecoursePerQ (L : ℕ) (P_b : SparsifyParams) (M N B : ℕ) : ℝ :=
  (B : ℝ) * ((3 + 2 * coreE82Len L P_b) * bundleBucketRecUH L P_b M +
    2 * bundleBucketRecD L P_b M) * (2 * bundleUCRatio N) +
    22 * (B : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M +
    7 + 224 * (Real.log ((N : ℝ) + 2)) ^ 2

/-- The size factor of the sparsified core of one branch: its edges number at most
`bundleSizeFactor L P_b M B * M / k`. The spanner outputs count `(L + 1) K_s γ_ℓ Λ_s` edges per
spanner vertex (Theorem 8.2, page 39). The spanner vertices of all buckets number at most
`B` times the number of roots plus `2 M / k` at the start, plus two splits per new root in each
bucket, and the roots number `O(M / k)` under the update threshold (paper Lemma 5.4, page 18).
The constant `1000` covers these counts and the edges outside the bundle graphs. -/
noncomputable def bundleSizeFactor (L : ℕ) (P_b : SparsifyParams) (M B : ℕ) : ℝ :=
  ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M * (B : ℝ) * 1000 + 115

end MinCostFlow.SparseCore
