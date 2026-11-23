module

public import MinCostFlow.SparseCore.Program.AssemblyFirstCharge

/-!
# The charge of a spanner batch in the step charge of a branch

The new walks of a batch of a bucket spanner are paid by the bank of the spanner and the charge
`dsBatchCharge` of the batch (`dsHist_reemb_walks_add_bank_le`, `AssemblyFirstWalkBank.lean`).
This file puts that charge into the step charge of the branch.

* `spanBatchRate_mono`, `dsBatchCharge_le_spanBatchChargeWith`: P6's charge, with the constant
  `dsAmortConst impl` and the parameters `(canonicalSparsifyParams impl mMax).absorbTime`, is at
  most the model's charge `spanBatchChargeWith` with a larger constant and larger parameters. The
  bundle side of a branch keeps both comparisons (`AsmBrSideModel`).
* `spanCharges_le_branchStepCharge`: the charges of the bucket spanners of the active pairs, summed,
  are at most the step charge `branchStepCharge`, since they are one of its terms and the log
  factor is at least one.
-/

public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

/-- The rate of the spanner charge grows with the parameters of the sparsifier. -/
theorem spanBatchRate_mono {P₁ P₂ : SparsifyParams} (hP : SparsifyParamsLe P₁ P₂) (L nMax : ℕ)
    (G₀ : MGraph) : spanBatchRate P₁ L nMax G₀ ≤ spanBatchRate P₂ L nMax G₀ := by
  unfold spanBatchRate
  have hK : P₁.K_t + P₁.K_s + 1 ≤ P₂.K_t + P₂.K_s + 1 := by linarith [hP.2.2.1, hP.2.2.2.2.1]
  have hgc0 : 0 ≤ P₁.γ_c := by linarith [P₁.hγ_c]
  have hgl0 : 0 ≤ P₁.γ_ℓ := by linarith [P₁.hγ_ℓ]
  have hKs0 : 0 ≤ P₁.K_s := P₁.hK_s
  have hKt0 : 0 ≤ P₁.K_t := P₁.hK_t
  have hgc2 : 0 ≤ P₂.γ_c := by linarith [P₂.hγ_c]
  have hgl2 : 0 ≤ P₂.γ_ℓ := by linarith [P₂.hγ_ℓ]
  have hKs2 : 0 ≤ P₂.K_s := P₂.hK_s
  have hKt2 : 0 ≤ P₂.K_t := P₂.hK_t
  have hE : (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) * P₁.γ_c ^ (L + 1) *
        P₁.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) ≤
      (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) * P₂.γ_c ^ (L + 1) *
        P₂.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) := by
    have := hP.1; have := hP.2.1; gcongr
  have hlog1 : 1 ≤ 1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (nMax : ℝ) + (G₀.m : ℝ) + 2 by
      linarith [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) G₀.m])
    linarith
  have hlam : (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ max P₁.p_s P₁.p_t ≤
      (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ max P₂.p_s P₂.p_t :=
    pow_le_pow_right₀ hlog1 (max_le_max hP.2.2.2.1 hP.2.2.2.2.2)
  gcongr

/-- **P6's charge is at most the model's charge** with a larger constant and larger parameters. -/
theorem dsBatchCharge_le_spanBatchChargeWith (impl : SparsifyImpl) (mMax L nMax : ℕ)
    (G₀ G : MGraph) (U : List Update) {c : ℕ} {P_b : SparsifyParams}
    (hc : dsAmortConst impl ≤ c)
    (hP : SparsifyParamsLe (canonicalSparsifyParams impl mMax).absorbTime P_b) :
    dsBatchCharge impl mMax L nMax G₀ G U ≤ spanBatchChargeWith c P_b L nMax G₀ G U := by
  unfold dsBatchCharge spanBatchChargeWith
  refine Nat.ceil_mono ?_
  have hc' : (dsAmortConst impl : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hr := spanBatchRate_mono hP L nMax G₀
  have hr0 := spanBatchRate_nonneg (canonicalSparsifyParams impl mMax).absorbTime L nMax G₀
  have hrate : dsBatchRate impl mMax L nMax G₀ =
      spanBatchRate (canonicalSparsifyParams impl mMax).absorbTime L nMax G₀ := rfl
  rw [hrate]
  have henc : (0 : ℝ) ≤ (G.batchEnc U : ℝ) := Nat.cast_nonneg _
  have h1 : (dsAmortConst impl : ℝ) *
      spanBatchRate (canonicalSparsifyParams impl mMax).absorbTime L nMax G₀ ≤
      (c : ℝ) * spanBatchRate P_b L nMax G₀ :=
    mul_le_mul hc' hr hr0 (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right h1 henc

/-- **The spanner charges of a step are in the step charge.** The charges `spanBatchChargeWith`
of the bucket spanners of the active pairs, summed, are at most `branchStepCharge`. -/
theorem spanCharges_le_branchStepCharge {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    ((stepBundleTree sparsify tr U ord ord').state.activeComps.sum fun C =>
      (tr.activeBuckets C).sum fun b =>
        spanBatchChargeWith tr.spanConst tr.spanParams L
          ((tr.initBunG (C, b)).n + tr.splitBound) (tr.initBunG (C, b)) (tr.dyn (C, b)).G
          ((stepBundleTree sparsify tr U ord ord').U_B (C, b))) ≤
      branchStepCharge sparsify tr U ord ord' := by
  dsimp only [branchStepCharge]
  refine le_trans ?_ (Nat.le_mul_of_pos_right _ (one_le_bundleLogFactor _ _))
  omega

end MinCostFlow.SparseCore.Program
