module

public import MinCostFlow.Final.AssemblyDryRunSC
public import MinCostFlow.MinRatio.WireParamMath
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Dry-run integer formulas and threshold for solver parameter setup

Specializes `MinRatio/WireParamMath.lean` to the dry-run witness `dryWitnessUsed`:
1. Extracts the concrete decomposition constants (`dryDecompK`, `dryDecompThr`) and expander
   conductance denominator (`dryWitnessDen`), and proves that the monotone sparsifier envelope's
   length factor equals the exact natural number `drySparsifyG M` (`drySparsifyEnvelope_gamma_l_eq`).
2. `exists_dryLevelM_threshold`: proves there is a witness-only cutoff `M_cut` above which the
   first branch `3 ^ L * g ^ (L + 1)` dominates `11 * bundleSizeFactor` in `bundleGammaLEnv`, so
   `cfg.TP.γ_ℓ (M₀ ^ 2) = (dryGammaNat M₀ : ℝ)`, `levelM cfg.TP cfg.P i` equals the exact integer
   ceiling division `(M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i - 1) / cfg.P.k ^ i`, and both
   `pathDSBoundsContract` argument sums are bounded by `J.m ^ 3`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio DynSpanner.Program

/-! ## Concrete sparsifier integer constants for `dryWitnessUsed` -/

/-- Integer decomposition parameter `K_nat` of `decomposeImplUsed expanderDecompositionUsed_holds`. -/
def dryDecompK : ℕ :=
  max 1 ⌈Classical.choose ExpanderDecomp.expanderDecompositionUsed_holds⌉₊

/-- Integer decomposition threshold `thr` of `decomposeImplUsed expanderDecompositionUsed_holds`. -/
def dryDecompThr : ℕ :=
  max 200 (Expander.thresholdB1
    (Classical.choose (Classical.choose_spec ExpanderDecomp.expanderDecompositionUsed_holds)))

/-- Exact conductance denominator of `constructExpanderImpl`. -/
def dryWitnessDen : ℕ := Expander.constructExpanderImpl.phiDen

/-- Exact conductance denominator `maxPhiDenOf dryDecompK dryDecompThr (M ^ 2)`. -/
def drySparsifyDen (M : ℕ) : ℕ :=
  Expander.maxPhiDenOf dryDecompK dryDecompThr (M ^ 2)

/-- Exact witness edge cap `36 * M ^ 2 * drySparsifyDen M + 1`. -/
def drySparsifyCap (M : ℕ) : ℕ :=
  36 * M ^ 2 * drySparsifyDen M + 1

/-- Exact squared path-length factor of `sparsifyImplUsed` at `M ^ 2`. -/
def drySparsifyG (M : ℕ) : ℕ :=
  (max (sparsifyPathDSUsed.params.gExp (drySparsifyDen M) (M ^ 2))
    (sparsifyPathDSUsed.params.gExp dryWitnessDen (drySparsifyCap M))) ^ 2

/-- Exact integer length factor `3 ^ L * g ^ (L + 1)` at `L = chosenL (M ^ 2)`. -/
def dryGammaNat (M : ℕ) : ℕ :=
  3 ^ Expander.chosenL (M ^ 2) * drySparsifyG M ^ (Expander.chosenL (M ^ 2) + 1)

theorem one_le_dryDecompK : 1 ≤ dryDecompK := le_max_left 1 _

theorem one_le_dryWitnessDen : 1 ≤ dryWitnessDen :=
  le_trans Expander.constructExpanderImpl.hphi_pos Expander.constructExpanderImpl.hphi_le

theorem dryDecomp_maxPhiDen_eq :
    (Expander.decomposeImplUsed ExpanderDecomp.expanderDecompositionUsed_holds).maxPhiDen =
      Expander.maxPhiDenOf dryDecompK dryDecompThr := rfl

theorem dryDecomp_phi_lb_eq (m : ℕ) :
    (Expander.decomposeImplUsed ExpanderDecomp.expanderDecompositionUsed_holds).φ_lb m =
      1 / (Expander.maxPhiDenOf dryDecompK dryDecompThr m : ℝ) := rfl

theorem dryWitness_phi_Const_eq :
    Expander.constructExpanderImpl.φ_Const = 1 / (dryWitnessDen : ℝ) := by
  unfold Spanner.ConstructExpanderImpl.φ_Const dryWitnessDen
  have h1 : Expander.constructExpanderImpl.phiNum = 1 := rfl
  rw [h1]; norm_num

private lemma ceil_inv_roundPhi_of_inv_nat {d : ℕ} (hd : 1 ≤ d) :
    Nat.ceil (1 / Spanner.roundPhi (1 / (d : ℝ))) = d := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have h1 : 1 / (1 / (d : ℝ)) = (d : ℝ) := one_div_one_div (d : ℝ)
  have h2 : Nat.ceil (1 / (1 / (d : ℝ))) = d := by rw [h1, Nat.ceil_natCast]
  unfold Spanner.roundPhi
  rw [h2, one_div_one_div, Nat.ceil_natCast]

private lemma capM_W_of_inv_nat (c j d : ℕ) :
    Spanner.capM_W (c : ℝ) (1 / (d : ℝ)) j = c * j * d + 1 := by
  unfold Spanner.capM_W
  have h1 : (c : ℝ) * (j : ℝ) / (1 / (d : ℝ)) = ((c * j * d : ℕ) : ℝ) := by
    rw [div_div_eq_mul_div, div_one]; push_cast; ring
  rw [h1, Nat.ceil_natCast]

/-- Exact integer formula for `(canonicalSparsifyParams sparsifyImplUsed j).γ_ℓ`. -/
theorem drySparsifyImpl_gamma_l_eq (j : ℕ) :
    (canonicalSparsifyParams sparsifyImplUsed j).γ_ℓ =
      (((max (sparsifyPathDSUsed.params.gExp (Expander.maxPhiDenOf dryDecompK dryDecompThr j) j)
        (sparsifyPathDSUsed.params.gExp dryWitnessDen
          (36 * j * Expander.maxPhiDenOf dryDecompK dryDecompThr j + 1))) ^ 2 : ℕ) : ℝ) := by
  change sparsifyImplUsed.γ_ℓ j = _
  rw [sparsifyImplUsed_γ_ℓ j]
  unfold Spanner.capGammaL Spanner.capGammaExpPath Spanner.pathDSTool_of_impl
    Spanner.PathDSParams.γ_ExpPath
  dsimp only
  have h36 : (36 : ℝ) = ((36 : ℕ) : ℝ) := by norm_num
  rw [h36, dryWitness_phi_Const_eq, dryDecomp_phi_lb_eq,
    ceil_inv_roundPhi_of_inv_nat (Expander.maxPhiDenOf_pos dryDecompK dryDecompThr j),
    ceil_inv_roundPhi_of_inv_nat one_le_dryWitnessDen,
    capM_W_of_inv_nat 36 j _]
  push_cast
  rfl

/-- `(canonicalSparsifyParams sparsifyImplUsed j).γ_ℓ` is monotone in `j`. -/
theorem drySparsifyImpl_gamma_l_mono :
    Monotone (fun j => (canonicalSparsifyParams sparsifyImplUsed j).γ_ℓ) := by
  intro j₁ j₂ hj
  dsimp only
  rw [drySparsifyImpl_gamma_l_eq j₁, drySparsifyImpl_gamma_l_eq j₂]
  have hd1 := Expander.maxPhiDenOf_pos dryDecompK dryDecompThr j₁
  have hdm := Expander.maxPhiDenOf_mono dryDecompK dryDecompThr hj
  have hcap : 36 * j₁ * Expander.maxPhiDenOf dryDecompK dryDecompThr j₁ + 1 ≤
      36 * j₂ * Expander.maxPhiDenOf dryDecompK dryDecompThr j₂ + 1 := by
    have h1 := Nat.mul_le_mul (Nat.mul_le_mul_left 36 hj) hdm
    omega
  have hg1 := sparsifyPathDSUsed.params.hgExp_mono hd1 hdm hj
  have hg2 := sparsifyPathDSUsed.params.hgExp_mono one_le_dryWitnessDen le_rfl hcap
  exact_mod_cast Nat.pow_le_pow_left (max_le_max hg1 hg2) 2

/-- The monotone envelope's `γ_ℓ` at `M ^ 2` equals the exact natural number `drySparsifyG M`. -/
theorem drySparsifyEnvelope_gamma_l_eq (M : ℕ) :
    (SparseCore.monoSparsifyParamsEnvelope (canonicalSparsifyParams sparsifyImplUsed) (M ^ 2)).γ_ℓ =
      (drySparsifyG M : ℝ) := by
  unfold SparseCore.monoSparsifyParamsEnvelope
  dsimp only
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun j hj => ?_
    have hjle : j ≤ M ^ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact (drySparsifyImpl_gamma_l_mono hjle).trans_eq (drySparsifyImpl_gamma_l_eq (M ^ 2))
  · exact (drySparsifyImpl_gamma_l_eq (M ^ 2)).symm.trans_le
      (Finset.le_sup' (fun j => (canonicalSparsifyParams sparsifyImplUsed j).γ_ℓ)
        (Finset.mem_range.mpr (Nat.lt_succ_self (M ^ 2))))

/-! ## Threshold `M_cut`: above `M_cut`, `coreE82Len` dominates `11 * bundleSizeFactor` and
both `boundsProcs` argument sums are at most `J.m ^ 3` -/

private lemma size_le_log2_four_sq_add_two {M : ℕ} (hM : 2 ≤ M) :
    M.size ≤ Nat.log 2 (4 * M ^ 2 + 2) + 2 := by
  have h1 : 2 ^ (M.size - 1) ≤ M := by
    have hpos : 0 < M.size := Nat.size_pos.mpr (by omega)
    exact Nat.lt_size.mp (by omega)
  have h2 : 2 ^ M.size ≤ 4 * M ^ 2 + 2 := by
    have hsq : M ≤ M ^ 2 := Nat.le_self_pow (by decide) M
    have h3 : 2 ^ M.size = 2 * 2 ^ (M.size - 1) := by
      have hpos : 0 < M.size := Nat.size_pos.mpr (by omega)
      rw [← pow_succ', Nat.sub_add_cancel hpos]
    omega
  have h3 : M.size ≤ Nat.log 2 (4 * M ^ 2 + 2) := Nat.le_log_of_pow_le (by decide) h2
  omega

private lemma rOf_four_sq_ge_four {M : ℕ} (hM : 2 ^ 32 ≤ M) :
    4 ≤ Expander.rOf (4 * M ^ 2) := by
  have hpow : 2 ^ 64 ≤ 4 * M ^ 2 := by
    calc 2 ^ 64 = (2 ^ 32) ^ 2 := by norm_num
      _ ≤ M ^ 2 := Nat.pow_le_pow_left hM 2
      _ ≤ 4 * M ^ 2 := by omega
  have hlog : 64 ≤ Nat.log 2 (4 * M ^ 2) := Nat.le_log_of_pow_le (by decide) hpow
  have hlt := Expander.lt_rOf_succ_pow (4 * M ^ 2)
  by_contra hnot
  have hle : Expander.rOf (4 * M ^ 2) + 1 ≤ 4 := by omega
  have hcube : (Expander.rOf (4 * M ^ 2) + 1) ^ 3 ≤ 4 ^ 3 := Nat.pow_le_pow_left hle 3
  omega

private lemma size_pow_32_le_drySparsifyG {M : ℕ} (hM : 2 ^ 32 ≤ M) :
    M.size ^ 32 ≤ drySparsifyG M := by
  have hr4 : 4 ≤ Expander.rOf (4 * M ^ 2) := rOf_four_sq_ge_four hM
  have hexp : 16 ≤ dryDecompK * Expander.rOf (4 * M ^ 2) ^ 2 := by
    have h1 : 16 ≤ Expander.rOf (4 * M ^ 2) ^ 2 := by nlinarith
    have hK := one_le_dryDecompK
    nlinarith
  have hsz : M.size ≤ Nat.log 2 (4 * M ^ 2 + 2) + 2 := size_le_log2_four_sq_add_two (by omega)
  have hden : M.size ^ 16 ≤ drySparsifyDen M := by
    unfold drySparsifyDen Expander.maxPhiDenOf Expander.phiDenHalf
    have h1 : M.size ^ 16 ≤ (Nat.log 2 (4 * M ^ 2 + 2) + 2) ^ 16 := Nat.pow_le_pow_left hsz 16
    have h2 : (Nat.log 2 (4 * M ^ 2 + 2) + 2) ^ 16 ≤
        (Nat.log 2 (4 * M ^ 2 + 2) + 2) ^ (dryDecompK * Expander.rOf (4 * M ^ 2) ^ 2) :=
      Nat.pow_le_pow_right (by omega) hexp
    have h3 : (Nat.log 2 (4 * M ^ 2 + 2) + 2) ^ (dryDecompK * Expander.rOf (4 * M ^ 2) ^ 2) ≤
        200 * dryDecompK * (Nat.log 2 (4 * M ^ 2 + 2) + 2) ^ (dryDecompK * Expander.rOf (4 * M ^ 2) ^ 2) :=
      Nat.le_mul_of_pos_left _ (by have := one_le_dryDecompK; omega)
    have h4 := le_max_right (dryDecompThr + 1)
      (200 * dryDecompK * (Nat.log 2 (4 * M ^ 2 + 2) + 2) ^ (dryDecompK * Expander.rOf (4 * M ^ 2) ^ 2))
    omega
  have hg1 : drySparsifyDen M ≤ sparsifyPathDSUsed.params.gExp (drySparsifyDen M) (M ^ 2) := by
    have hd1 := Expander.maxPhiDenOf_pos dryDecompK dryDecompThr (M ^ 2)
    exact (le_max_right 2 _).trans
      ((sparsifyPathDSUsed.params.hphiOutDen_ge _ _ hd1).trans
        (sparsifyPathDSUsed.params.hgExp_ge _ _ hd1))
  have hg : drySparsifyDen M ^ 2 ≤ drySparsifyG M :=
    Nat.pow_le_pow_left (hg1.trans (le_max_left _ _)) 2
  calc M.size ^ 32 = (M.size ^ 16) ^ 2 := by ring
    _ ≤ drySparsifyDen M ^ 2 := Nat.pow_le_pow_left hden 2
    _ ≤ drySparsifyG M := hg

private lemma real_log_le_size_nat (n : ℕ) : Real.log ((n : ℝ) + 2) ≤ ((n + 2).size : ℝ) := by
  have h1 : ((n : ℝ) + 2) ≤ (2 : ℝ) ^ (n + 2).size := by exact_mod_cast (Nat.lt_size_self (n + 2)).le
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  nlinarith [Nat.cast_nonneg (α := ℝ) (n + 2).size]

private lemma size_add_le_of_mul_pow {a c e M : ℕ} (ha : a ≤ c * M ^ e) :
    a.size ≤ c.size + e * M.size := by
  have hc : c < 2 ^ c.size := Nat.lt_size_self c
  have hMs : M ≤ 2 ^ M.size := (Nat.lt_size_self M).le
  have hpow : M ^ e ≤ 2 ^ (e * M.size) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left hMs e
  have hlt : a < 2 ^ (c.size + e * M.size) := by
    rw [pow_add]
    exact lt_of_le_of_lt ha (lt_of_le_of_lt (Nat.mul_le_mul_left c hpow)
      (Nat.mul_lt_mul_of_pos_right hc (Nat.two_pow_pos _)))
  exact Nat.size_le.mpr hlt

private lemma exists_size_cut (C : ℕ) : ∃ N : ℕ, ∀ M, N ≤ M → C ≤ M.size := by
  refine ⟨2 ^ C, fun M hM => ?_⟩
  by_contra hlt
  have h1 : M < 2 ^ M.size := Nat.lt_size_self M
  have h2 : 2 ^ M.size ≤ 2 ^ C := Nat.pow_le_pow_right (by decide) (by omega)
  omega

private lemma subpoly_exp_le_rpow_nat {C a δ : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n →
      Real.exp (C * Real.log ((n : ℝ) + 2) ^ a) ≤ B * ((n : ℝ) + 2) ^ δ := by
  obtain ⟨B, hB, hbd⟩ := Chain.exp_subpoly_mul_loglog_le_rpow (a := a) (C := max 0 C) (δ := δ) ha0 ha1 hδ
  refine ⟨B, hB, fun n hn => ?_⟩
  have hn3 : (3 : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast (show 3 ≤ n + 2 by omega)
  have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := by
    have h3 : Real.exp 1 ≤ (n : ℝ) + 2 := le_trans Real.exp_one_lt_three.le hn3
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3
  have hLL1 : 1 ≤ Real.log (Real.log ((n : ℝ) + 2) + 2) := by
    have h3 : Real.exp 1 ≤ Real.log ((n : ℝ) + 2) + 2 := by linarith [Real.exp_one_lt_three]
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3
  have hpow0 : 0 ≤ Real.log ((n : ℝ) + 2) ^ a := Real.rpow_nonneg (by linarith) a
  have h1 : C * Real.log ((n : ℝ) + 2) ^ a ≤
      max 0 C * Real.log ((n : ℝ) + 2) ^ a * Real.log (Real.log ((n : ℝ) + 2) + 2) := by
    have hle : C * Real.log ((n : ℝ) + 2) ^ a ≤ max 0 C * Real.log ((n : ℝ) + 2) ^ a :=
      mul_le_mul_of_nonneg_right (le_max_right 0 C) hpow0
    have hnn : 0 ≤ max 0 C * Real.log ((n : ℝ) + 2) ^ a := mul_nonneg (le_max_left 0 C) hpow0
    exact hle.trans (le_mul_of_one_le_right hnn hLL1)
  exact (Real.exp_le_exp.mpr h1).trans (hbd ((n : ℝ) + 2) hn3)

private lemma concreteBucketCap_le_poly {C_lsstN psiN kn dn M₀ A : ℕ}
    (hsz_ge32 : 32 ≤ M₀.size)
    (hd_le : dn ≤ 2 * M₀.size) (hk_le : kn ≤ 2 * M₀)
    (hPsi_le : psiN ≤ 10 ^ 10 * (A + 1) * M₀.size ^ 2) :
    max 1 (Chain.concreteBucketCap C_lsstN psiN kn dn (4 * M₀)) ≤
      (3 * 10 ^ 10 * (A + 1) + 100 * (6272 * max 1 C_lsstN).size + 10 ^ 10) * M₀.size ^ 2 := by
  unfold Chain.concreteBucketCap Chain.concreteBucketStretch
  have hclog_N : Nat.clog 2 (4 * M₀ + 2) ≤ M₀.size + 3 := by
    apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    have hm := Nat.lt_size_self M₀
    rw [pow_add]; norm_num; omega
  have hclog_S : Nat.clog 2 (max 2 (6272 * max 1 C_lsstN * kn * Nat.clog 2 (4 * M₀ + 2) ^ 6)) ≤
      (6272 * max 1 C_lsstN).size + 8 * M₀.size := by
    apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    apply max_le
    · exact le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega))
    · have h1 : 6272 * max 1 C_lsstN < 2 ^ (6272 * max 1 C_lsstN).size := Nat.lt_size_self _
      have h2 : kn ≤ 2 ^ (M₀.size + 1) := by
        have hm := Nat.lt_size_self M₀; rw [pow_succ 2]; omega
      have h3 : Nat.clog 2 (4 * M₀ + 2) ^ 6 ≤ 2 ^ (6 * M₀.size) := by
        have ha : Nat.clog 2 (4 * M₀ + 2) ≤ 2 ^ M₀.size := by
          have h1 := Nat.lt_two_pow_self (n := M₀.size - 1)
          have h2 : 2 ^ M₀.size = 2 * 2 ^ (M₀.size - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel (by omega)]
          omega
        calc Nat.clog 2 (4 * M₀ + 2) ^ 6 ≤ (2 ^ M₀.size) ^ 6 := Nat.pow_le_pow_left ha 6
          _ = 2 ^ (6 * M₀.size) := by rw [← pow_mul, mul_comm]
      have h4 : 2 ^ ((6272 * max 1 C_lsstN).size + (M₀.size + 1) + 6 * M₀.size) ≤
          2 ^ ((6272 * max 1 C_lsstN).size + 8 * M₀.size) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      calc 6272 * max 1 C_lsstN * kn * Nat.clog 2 (4 * M₀ + 2) ^ 6
          ≤ 2 ^ (6272 * max 1 C_lsstN).size * 2 ^ (M₀.size + 1) * 2 ^ (6 * M₀.size) :=
            Nat.mul_le_mul (Nat.mul_le_mul h1.le h2) h3
        _ = 2 ^ ((6272 * max 1 C_lsstN).size + (M₀.size + 1) + 6 * M₀.size) := by
            rw [← pow_add, ← pow_add]
        _ ≤ 2 ^ ((6272 * max 1 C_lsstN).size + 8 * M₀.size) := h4
  set cS := Nat.clog 2 (max 2 (6272 * max 1 C_lsstN * kn * Nat.clog 2 (4 * M₀ + 2) ^ 6))
  set X := (6272 * max 1 C_lsstN).size
  have hprod_d : dn * cS ≤ (2 * X + 16) * M₀.size ^ 2 := by
    have h1 : dn * cS ≤ (2 * M₀.size) * (X + 8 * M₀.size) := Nat.mul_le_mul hd_le hclog_S
    have h2 : X * M₀.size ≤ X * M₀.size ^ 2 :=
      Nat.mul_le_mul_left X (Nat.le_self_pow (by decide : 2 ≠ 0) M₀.size)
    calc dn * cS ≤ (2 * M₀.size) * (X + 8 * M₀.size) := h1
      _ = 2 * (X * M₀.size) + 16 * M₀.size ^ 2 := by ring
      _ ≤ 2 * (X * M₀.size ^ 2) + 16 * M₀.size ^ 2 := by omega
      _ = (2 * X + 16) * M₀.size ^ 2 := by ring
  have hsq : 1 ≤ M₀.size ^ 2 := Nat.one_le_pow 2 _ (by omega)
  apply max_le
  · nlinarith only [hsq]
  · nlinarith only [hPsi_le, hprod_d, hsq]

private lemma bundleSizeFactor_le_coreE82Len_of_bounds {L : ℕ} {Ks lam : ℝ} {g B sz C_B C_fac : ℕ}
    (hL1 : 1 ≤ L) (hg1 : 1 ≤ g) (hsz1 : 1 ≤ sz)
    (hEL : L + 1 ≤ 10 * sz) (hKs0 : 0 ≤ Ks) (hKs : Ks ≤ 60)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 10 * (sz : ℝ))
    (hB : B ≤ C_B * sz ^ 2) (hsz32 : sz ^ 32 ≤ g) (hszC : C_fac ≤ sz)
    (hCf : 11 * (10 * 60 * 10 * C_B * 1000 + 115) ≤ C_fac) :
    11 * (((L : ℝ) + 1) * Ks * (g : ℝ) * lam * (B : ℝ) * 1000 + 115) ≤
      (3 : ℝ) ^ L * (g : ℝ) ^ (L + 1) := by
  have hg_r1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg1
  have hEL_r : (L : ℝ) + 1 ≤ 10 * (sz : ℝ) := by exact_mod_cast hEL
  have hB_r : (B : ℝ) ≤ (C_B : ℝ) * (sz : ℝ) ^ 2 := by exact_mod_cast hB
  have hsz4 : (1 : ℝ) ≤ (sz : ℝ) ^ 4 := by exact_mod_cast Nat.one_le_pow 4 sz hsz1
  have h115 : (115 : ℝ) ≤ 115 * (g : ℝ) * (sz : ℝ) ^ 4 := by nlinarith only [hg_r1, hsz4]
  have hterm : ((L : ℝ) + 1) * Ks * (g : ℝ) * lam * (B : ℝ) * 1000 ≤
      (10 * 60 * 10 * (C_B : ℝ) * 1000) * (g : ℝ) * (sz : ℝ) ^ 4 := by
    calc ((L : ℝ) + 1) * Ks * (g : ℝ) * lam * (B : ℝ) * 1000
        ≤ (10 * (sz : ℝ)) * 60 * (g : ℝ) * (10 * (sz : ℝ)) * ((C_B : ℝ) * (sz : ℝ) ^ 2) * 1000 := by
          gcongr
      _ = (10 * 60 * 10 * (C_B : ℝ) * 1000) * (g : ℝ) * (sz : ℝ) ^ 4 := by ring
  have hCf_r : (11 * (10 * 60 * 10 * (C_B : ℝ) * 1000 + 115) : ℝ) ≤ (C_fac : ℝ) := by
    exact_mod_cast hCf
  have hT2_ub : 11 * (((L : ℝ) + 1) * Ks * (g : ℝ) * lam * (B : ℝ) * 1000 + 115) ≤
      (C_fac : ℝ) * (g : ℝ) * (sz : ℝ) ^ 4 := by
    calc 11 * (((L : ℝ) + 1) * Ks * (g : ℝ) * lam * (B : ℝ) * 1000 + 115)
        ≤ 11 * ((10 * 60 * 10 * (C_B : ℝ) * 1000) * (g : ℝ) * (sz : ℝ) ^ 4 +
            115 * (g : ℝ) * (sz : ℝ) ^ 4) := by linarith only [hterm, h115]
      _ = (11 * (10 * 60 * 10 * (C_B : ℝ) * 1000 + 115)) * ((g : ℝ) * (sz : ℝ) ^ 4) := by ring
      _ ≤ (C_fac : ℝ) * ((g : ℝ) * (sz : ℝ) ^ 4) := mul_le_mul_of_nonneg_right hCf_r (by positivity)
      _ = (C_fac : ℝ) * (g : ℝ) * (sz : ℝ) ^ 4 := by ring
  have hsz5 : (C_fac : ℝ) * (sz : ℝ) ^ 4 ≤ (g : ℝ) := by
    have h1 : C_fac * sz ^ 4 ≤ sz ^ 5 :=
      (Nat.mul_le_mul_right _ hszC).trans_eq (by ring)
    have h2 : sz ^ 5 ≤ sz ^ 32 := Nat.pow_le_pow_right hsz1 (by decide)
    exact_mod_cast (h1.trans h2).trans hsz32
  have h3L : (1 : ℝ) ≤ (3 : ℝ) ^ L := one_le_pow₀ (by norm_num)
  have hgpow : (g : ℝ) ^ 2 ≤ (g : ℝ) ^ (L + 1) := pow_le_pow_right₀ hg_r1 (by omega)
  calc 11 * (((L : ℝ) + 1) * Ks * (g : ℝ) * lam * (B : ℝ) * 1000 + 115)
      ≤ (C_fac : ℝ) * (g : ℝ) * (sz : ℝ) ^ 4 := hT2_ub
    _ = (g : ℝ) * ((C_fac : ℝ) * (sz : ℝ) ^ 4) := by ring
    _ ≤ (g : ℝ) * (g : ℝ) := mul_le_mul_of_nonneg_left hsz5 (by positivity)
    _ = 1 * (g : ℝ) ^ 2 := by ring
    _ ≤ (3 : ℝ) ^ L * (g : ℝ) ^ (L + 1) := mul_le_mul h3L hgpow (by positivity) (by positivity)

private lemma exists_dryGamma_dominates :
    ∃ M₁ : ℕ, max (concreteEdgeThresholdWithLast dryWitnessUsed) (2 ^ 32) ≤ M₁ ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        M₁ ≤ (solverConnectedAugmented J).m →
        let I := solverConnectedAugmented J
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let M₀ := cfg.P.M₀
        M₀ = I.m ∧
        cfg.TP.γ_ℓ (M₀ ^ 2) = (dryGammaNat M₀ : ℝ) ∧
        (∀ i, Chain.levelM cfg.TP cfg.P i =
          (M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i - 1) / cfg.P.k ^ i) := by
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let C_lsstN : ℕ := ⌈dryWitnessUsed.C_lsst⌉₊
  let C_B : ℕ := 3 * 10 ^ 10 * (A + 1) + 100 * (6272 * max 1 C_lsstN).size + 10 ^ 10
  let C_fac : ℕ := 11 * (1000 * 10 * 60 * 10 * C_B + 115) + 1000
  obtain ⟨M_fac, hMfac⟩ := exists_size_cut C_fac
  refine ⟨max (max threshold (2 ^ 32)) M_fac, le_max_left _ _, fun J hJn hJm hCap hMcut => ?_⟩
  intro I cfg M₀
  have hthr_le : threshold ≤ I.m :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMcut
  have h232_le : 2 ^ 32 ≤ I.m :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMcut
  have hMfac_le : M_fac ≤ I.m := le_trans (le_max_right _ _) hMcut
  have hM0_eq : M₀ = I.m := max_eq_left hthr_le
  have hM0_ge232 : 2 ^ 32 ≤ M₀ := hM0_eq ▸ h232_le
  have hM0_pos : 1 ≤ M₀ := by omega
  have hsz_ge : C_fac ≤ M₀.size := hMfac M₀ (hM0_eq ▸ hMfac_le)
  have hsz_ge32 : 32 ≤ M₀.size := by
    by_contra hlt
    have h2 : M₀ < 2 ^ M₀.size := Nat.lt_size_self M₀
    have h3 : 2 ^ M₀.size ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  -- Part 1: prove `11 * bundleSizeFactor ≤ coreE82Len`
  let E := Chain.Ordered.concreteEnv dryWitnessUsed.C_lsst dryWitnessUsed.params
    dryWitnessUsed.hp_s dryWitnessUsed.hp_t M₀
    (Chain.concreteBucketCapacity true dryWitnessUsed.C_lsst cfg.Ψ M₀ cfg.N₀ hM0_pos)
  have hTP_eq : cfg.TP.γ_ℓ (M₀ ^ 2) = SparseCore.bundleGammaLEnv E (M₀ ^ 2) := rfl
  have hPfn_gamma : (E.P_fn (M₀ ^ 2)).γ_ℓ = (drySparsifyG M₀ : ℝ) :=
    drySparsifyEnvelope_gamma_l_eq M₀
  have hdw_params : dryWitnessUsed.params = canonicalSparsifyParams sparsifyImplUsed := rfl
  have hPfn_ps : (E.P_fn (M₀ ^ 2)).p_s = 1 := by
    unfold E Chain.Ordered.concreteEnv SparseCore.monoSparsifyParamsEnvelope
    dsimp only
    rw [hdw_params]
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun j _ => by simp [canonicalSparsifyParams, sparsifyImplUsed_p_s]
    · exact (by simp [canonicalSparsifyParams, sparsifyImplUsed_p_s] :
        (1 : ℕ) = (canonicalSparsifyParams sparsifyImplUsed 0).p_s).le.trans
        (Finset.le_sup' (fun j => (canonicalSparsifyParams sparsifyImplUsed j).p_s)
          (Finset.mem_range.mpr (Nat.zero_lt_succ _)))
  have hPfn_Ks : (E.P_fn (M₀ ^ 2)).K_s = 1 + 36 / Real.log 2 := by
    unfold E Chain.Ordered.concreteEnv SparseCore.monoSparsifyParamsEnvelope
    dsimp only
    rw [hdw_params]
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun j _ => by
        simp [canonicalSparsifyParams, sparsifyImplUsed_K_s]
    · exact (by simp [canonicalSparsifyParams, sparsifyImplUsed_K_s] :
        1 + 36 / Real.log 2 = (canonicalSparsifyParams sparsifyImplUsed 0).K_s).le.trans
        (Finset.le_sup' (fun j => (canonicalSparsifyParams sparsifyImplUsed j).K_s)
          (Finset.mem_range.mpr (Nat.zero_lt_succ _)))
  have hEL_le : E.L + 1 ≤ 10 * M₀.size := by
    have hL : E.L = Expander.chosenL (M₀ ^ 2) := rfl
    rw [hL]
    have h1 : Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) ^ (1 / 24 : ℝ) ≤ Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) := by
      have hge1 : 1 ≤ Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) := by
        have h3 : Real.exp 1 ≤ ((M₀ ^ 2 : ℕ) : ℝ) + 2 := by
          have : (3 : ℝ) ≤ ((M₀ ^ 2 : ℕ) : ℝ) + 2 := by exact_mod_cast (show 3 ≤ M₀ ^ 2 + 2 by nlinarith)
          linarith [Real.exp_one_lt_three]
        simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3
      calc Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) ^ (1 / 24 : ℝ)
          ≤ Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hge1 (by norm_num)
        _ = Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) := Real.rpow_one _
    have h2 : Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) ≤ ((M₀ ^ 2 + 2).size : ℝ) := real_log_le_size_nat (M₀ ^ 2)
    have h3 : (M₀ ^ 2 + 2).size ≤ 2 * M₀.size + 1 := by
      have hlt : M₀ ^ 2 + 2 < 2 ^ (2 * M₀.size + 1) := by
        have hm := Nat.lt_size_self M₀
        have hsq : M₀ ^ 2 < (2 ^ M₀.size) ^ 2 := Nat.pow_lt_pow_left hm (by decide)
        rw [← pow_mul, mul_comm M₀.size 2] at hsq
        have h2p : 2 ≤ 2 ^ (2 * M₀.size) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (2 * M₀.size) := Nat.pow_le_pow_right (by decide) (by omega)
        rw [pow_succ 2]; omega
      exact Nat.size_le.mpr hlt
    have h4 : Expander.chosenL (M₀ ^ 2) ≤ (M₀ ^ 2 + 2).size := Nat.ceil_le.mpr (h1.trans h2)
    omega
  have hKs_le : (E.P_fn (M₀ ^ 2)).K_s ≤ 60 := by
    rw [hPfn_Ks]
    have hlog2 : (65 / 100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hdiv : 36 / Real.log 2 ≤ 36 / (65 / 100 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlog2
    linarith
  have hlam_le : SparseCore.bundleLambdaS (E.P_fn (M₀ ^ 2)) (M₀ ^ 2) ≤ 10 * (M₀.size : ℝ) := by
    unfold SparseCore.bundleLambdaS SparseCore.bundleNMax
    rw [hPfn_ps, pow_one]
    have hsum : ((2 * M₀ ^ 2 + 2 * (56 * M₀ ^ 2 + 1) : ℕ) : ℝ) + ((M₀ ^ 2 : ℕ) : ℝ) + 2 =
        ((115 * M₀ ^ 2 + 2 : ℕ) : ℝ) + 2 := by push_cast; ring
    rw [hsum]
    have h1 := real_log_le_size_nat (115 * M₀ ^ 2 + 2)
    have h2 : (115 * M₀ ^ 2 + 4).size ≤ 2 * M₀.size + 8 := by
      apply Nat.size_le.mpr
      have hm := Nat.lt_size_self M₀
      have hsq : M₀ ^ 2 < 2 ^ (2 * M₀.size) := by
        calc M₀ ^ 2 < (2 ^ M₀.size) ^ 2 := Nat.pow_lt_pow_left hm (by decide)
          _ = 2 ^ (2 * M₀.size) := by rw [← pow_mul, mul_comm]
      have h128 : 115 * M₀ ^ 2 + 4 < 256 * 2 ^ (2 * M₀.size) := by omega
      rwa [show 256 * 2 ^ (2 * M₀.size) = 2 ^ (2 * M₀.size + 8) by rw [pow_add]; ring] at h128
    have h3 : (1 : ℝ) + ((115 * M₀ ^ 2 + 4).size : ℝ) ≤ 10 * (M₀.size : ℝ) := by
      exact_mod_cast (show 1 + (115 * M₀ ^ 2 + 4).size ≤ 10 * M₀.size by omega)
    linarith
  -- Bound `E.B_fn (M₀ ^ 2) ≤ C_B * M₀.size ^ 2`
  have hIm_ge_Jm : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap).1
  have hV_le : solverPenalty J.m ≤ 16 * M₀ ^ 81 :=
    (solverPenalty_le J.m hJm).trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (hM0_eq ▸ hIm_ge_Jm) 81))
  have hVsz_le : (solverPenalty J.m).size ≤ 82 * M₀.size := by
    have h1 := size_add_le_of_mul_pow hV_le
    have h16 : (16 : ℕ).size = 5 := by decide
    omega
  have hk_le : cappedQualityExponent threshold A I.m ≤ 512 * (A + 1) * M₀.size ^ 2 := by
    unfold cappedQualityExponent chainEdgeCap integerQualityExponent
    have hmax : max I.m threshold = M₀ := rfl
    rw [hmax]
    set b := (M₀.size + 1).size
    have hb_le : b ≤ M₀.size + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
    have h2b : 2 ^ ((47 * b + 47) / 48) ≤ 2 ^ b := by
      apply Nat.pow_le_pow_right (by decide)
      have hb1 : 1 ≤ b := Nat.size_pos.mpr (by omega)
      omega
    have h2b_le : 2 ^ b ≤ 2 * (M₀.size + 1) := by
      have hb1 : 1 ≤ b := Nat.size_pos.mpr (by omega)
      have h1 : 2 ^ (b - 1) ≤ M₀.size + 1 := Nat.lt_size.mp (by omega)
      have h2 : 2 ^ b = 2 * 2 ^ (b - 1) := by rw [← pow_succ', Nat.sub_add_cancel hb1]
      omega
    have h1 : b * 2 ^ ((47 * b + 47) / 48) ≤ (M₀.size + 1) * (2 * (M₀.size + 1)) :=
      Nat.mul_le_mul hb_le (h2b.trans h2b_le)
    have h2 : (M₀.size + 1) * (2 * (M₀.size + 1)) ≤ 4 * M₀.size ^ 2 := by nlinarith only [hsz_ge32]
    calc 128 * (A + 1) * b * 2 ^ ((47 * b + 47) / 48)
        = 128 * (A + 1) * (b * 2 ^ ((47 * b + 47) / 48)) := by ring
      _ ≤ 128 * (A + 1) * (4 * M₀.size ^ 2) := Nat.mul_le_mul_left _ (h1.trans h2)
      _ = 512 * (A + 1) * M₀.size ^ 2 := by ring
  have hPsi_le : ⌈cfg.Ψ⌉₊ ≤ 10 ^ 10 * (A + 1) * M₀.size ^ 2 := by
    have hPsi_eq : ⌈cfg.Ψ⌉₊ = paramPsi threshold A I.m (solverPenalty J.m) :=
      (concreteCfg_scalars_eq dryWitnessUsed I.m (solverPenalty J.m)).2.2.1
    rw [hPsi_eq]
    unfold paramPsi ipmQualityRangeExponent qualitySlackExponent slackRangeExponent
      gradientCoefficientExponent paramQuality
    have hsum : I.m.size + (solverPenalty J.m).size ≤ 83 * M₀.size := by rw [← hM0_eq]; omega
    have hsq : (I.m.size + (solverPenalty J.m).size) ^ 2 ≤ 6889 * M₀.size ^ 2 := by
      nlinarith only [hsum]
    have hmax : max (220000 * (I.m.size + (solverPenalty J.m).size) ^ 2)
        (cappedQualityExponent threshold A I.m) ≤
        220000 * (6889 * M₀.size ^ 2) + 512 * (A + 1) * M₀.size ^ 2 := by
      apply max_le
      · exact (Nat.mul_le_mul_left 220000 hsq).trans (Nat.le_add_right _ _)
      · exact le_trans hk_le (Nat.le_add_left _ _)
    nlinarith only [hsum, hsq, hmax, hsz_ge32]
  have hB_le : E.B_fn (M₀ ^ 2) ≤ C_B * M₀.size ^ 2 := by
    change max 1 (Chain.concreteBucketCap C_lsstN ⌈cfg.Ψ⌉₊ cfg.P.k cfg.P.d (4 * M₀)) ≤ C_B * M₀.size ^ 2
    have hd_le : cfg.P.d ≤ 2 * M₀.size := by
      have h1 : cfg.P.d ≤ (M₀ + 2).size := chosenD_le_size_add_two hM0_pos
      have h2 : (M₀ + 2).size ≤ M₀.size + 1 := by
        apply Nat.size_le.mpr
        have hm := Nat.lt_size_self M₀
        rw [pow_succ 2]; omega
      omega
    have hk_le_M : cfg.P.k ≤ 2 * M₀ := by
      have hM1 : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM0_pos
      have hd1 : (1 : ℝ) ≤ (cfg.P.d : ℝ) := by exact_mod_cast cfg.P.hd
      have hinv : 1 / (cfg.P.d : ℝ) ≤ 1 := div_le_one_of_le₀ hd1 (by linarith)
      have h2 : (M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) ≤ (M₀ : ℝ) := by
        calc (M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) ≤ (M₀ : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hM1 hinv
          _ = (M₀ : ℝ) := Real.rpow_one _
      have h3 : (cfg.P.k : ℝ) ≤ ((2 * M₀ : ℕ) : ℝ) := by push_cast; linarith [cfg.P.hk_upper]
      exact_mod_cast h3
    exact concreteBucketCap_le_poly hsz_ge32 hd_le hk_le_M hPsi_le
  have hg_pos_nat : 1 ≤ drySparsifyG M₀ := by
    have h := size_pow_32_le_drySparsifyG hM0_ge232
    have h1 : 1 ≤ M₀.size ^ 32 := Nat.one_le_pow _ _ (by omega)
    omega
  have hT2_le_T1 : 11 * SparseCore.bundleSizeFactor E.L (E.P_fn (M₀ ^ 2)) (M₀ ^ 2) (E.B_fn (M₀ ^ 2)) ≤
      SparseCore.coreE82Len E.L (E.P_fn (M₀ ^ 2)) := by
    unfold SparseCore.bundleSizeFactor SparseCore.coreE82Len
    rw [hPfn_gamma]
    have hCf : 11 * (10 * 60 * 10 * C_B * 1000 + 115) ≤ C_fac := by
      dsimp only [C_fac]
      exact (le_of_eq (by ring : 11 * (10 * 60 * 10 * C_B * 1000 + 115) =
        11 * (1000 * 10 * 60 * 10 * C_B + 115))).trans (Nat.le_add_right _ _)
    exact bundleSizeFactor_le_coreE82Len_of_bounds E.hL hg_pos_nat (by omega) hEL_le
      (by rw [hPfn_Ks]; positivity) hKs_le (SparseCore.bundleParams_lambdaS_pos _ _) hlam_le
      hB_le (size_pow_32_le_drySparsifyG hM0_ge232) hsz_ge hCf
  have hγ_eq : cfg.TP.γ_ℓ (M₀ ^ 2) = (dryGammaNat M₀ : ℝ) := by
    rw [hTP_eq, SparseCore.bundleGammaLEnv, max_eq_left hT2_le_T1, SparseCore.coreE82Len, hPfn_gamma]
    dsimp only [dryGammaNat, E, Chain.Ordered.concreteEnv]
    push_cast; rfl
  have hγ_ge1 : 1 ≤ dryGammaNat M₀ :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos hg_pos_nat)
  have hlvlM_eq : ∀ i, Chain.levelM cfg.TP cfg.P i =
      (M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i - 1) / cfg.P.k ^ i :=
    fun i => levelM_eq_nat_div hγ_ge1 hγ_eq i
  exact ⟨hM0_eq, hγ_eq, hlvlM_eq⟩

private lemma exists_dryBoundsSums_le_cube :
    ∃ M₂ : ℕ, max (concreteEdgeThresholdWithLast dryWitnessUsed) (2 ^ 32) ≤ M₂ ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        M₂ ≤ (solverConnectedAugmented J).m →
        let M₀ := (concreteCirculationCfgWithLast dryWitnessUsed J).P.M₀
        let pds := sparsifyPathDSUsed.params
        drySparsifyDen M₀ + M₀ ^ 2 + pds.gExp (drySparsifyDen M₀) (M₀ ^ 2) +
          pds.gDel (drySparsifyDen M₀) (M₀ ^ 2) + 2 ≤ J.m ^ 3 ∧
        dryWitnessDen + drySparsifyCap M₀ + pds.gExp dryWitnessDen (drySparsifyCap M₀) +
          pds.gDel dryWitnessDen (drySparsifyCap M₀) + 2 ≤ J.m ^ 3 := by
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let pds := sparsifyPathDSUsed.params
  obtain ⟨C₀_p, C₁_p, hC₀p, hC₁p, hden_sb⟩ :=
    Expander.decomposeImpl_phi_lb_subpoly ExpanderDecomp.expanderDecompositionUsed_holds
  have hgExp_reg := sparsifyPathDSUsed_gExp_regimes
  have hgDel_reg := sparsifyPathDSUsed_gDel_regimes
  obtain ⟨C_ge1, _, hge1⟩ := hgExp_reg.1 C₀_p C₁_p hC₀p (by linarith)
  obtain ⟨C_ge2, _, hge2⟩ := hgExp_reg.2
  obtain ⟨C_gd1, _, hgd1⟩ := hgDel_reg.1 C₀_p C₁_p hC₀p (by linarith)
  obtain ⟨C_gd2, _, hgd2⟩ := hgDel_reg.2
  obtain ⟨B_den, _, hBden_le⟩ :=
    Chain.exp_subpoly_mul_loglog_le_rpow (a := 2 / 3) (C := C₀_p) (δ := 1 / 8)
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨B_ge1, _, hBge1_le⟩ := subpoly_exp_le_rpow_nat (C := C_ge1) (a := 7 / 8) (δ := 1 / 8)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨B_gd1, _, hBgd1_le⟩ := subpoly_exp_le_rpow_nat (C := C_gd1) (a := 7 / 8) (δ := 1 / 8)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨B_ge2, _, hBge2_le⟩ := subpoly_exp_le_rpow_nat (C := C_ge2) (a := 7 / 8) (δ := 1 / 8)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨B_gd2, _, hBgd2_le⟩ := subpoly_exp_le_rpow_nat (C := C_gd2) (a := 7 / 8) (δ := 1 / 8)
    (by norm_num) (by norm_num) (by norm_num)
  let K_den : ℕ := max 1 ⌈C₁_p * B_den⌉₊
  let K_cap : ℕ := 72 * K_den + 2
  let K_sum : ℕ := dryWitnessDen + K_den + 2 * K_cap +
    ⌈B_ge1⌉₊ + ⌈B_gd1⌉₊ + ⌈B_ge2⌉₊ * K_cap + ⌈B_gd2⌉₊ * K_cap + 100
  refine ⟨max (max threshold (2 ^ 32)) (7 * (49 * K_sum) ^ 4 + 7), le_max_left _ _,
    fun J hJn hJm hCap hMcut => ?_⟩
  intro M₀ pds'
  set I := solverConnectedAugmented J
  have hthr_le : threshold ≤ I.m :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMcut
  have h232_le : 2 ^ 32 ≤ I.m :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMcut
  have hKsum_le : 7 * (49 * K_sum) ^ 4 + 7 ≤ I.m := le_trans (le_max_right _ _) hMcut
  have hM0_eq : M₀ = I.m := max_eq_left hthr_le
  have hM0_pos : 1 ≤ M₀ := by omega
  have hIm_le_7Jm : I.m ≤ 7 * J.m := (solverConnectedAugmented_size J hJn hJm hCap).2
  have hM0_le_7Jm : M₀ ≤ 7 * J.m := hM0_eq ▸ hIm_le_7Jm
  have hJm_big : (49 * K_sum) ^ 4 < J.m := by omega
  have hJm_ge2 : 2 ≤ J.m := by
    have hKpos : 1 ≤ K_sum := by dsimp only [K_sum]; omega
    have : 1 ≤ (49 * K_sum) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hM2_pos : 1 ≤ M₀ ^ 2 := Nat.one_le_pow _ _ hM0_pos
  have hM2_3 : (3 : ℝ) ≤ ((M₀ ^ 2 : ℕ) : ℝ) + 2 := by exact_mod_cast (show 3 ≤ M₀ ^ 2 + 2 by omega)
  have hM2_add2_le : ((M₀ ^ 2 : ℕ) : ℝ) + 2 ≤ 50 * (J.m : ℝ) ^ 2 := by
    have h1 : M₀ ^ 2 + 2 ≤ 50 * J.m ^ 2 := by nlinarith only [hM0_le_7Jm, hJm_ge2]
    exact_mod_cast h1
  have hM2_rpow : (((M₀ ^ 2 : ℕ) : ℝ) + 2) ^ (1 / 8 : ℝ) ≤ 2 * (J.m : ℝ) ^ (1 / 4 : ℝ) := by
    have h50 : (50 : ℝ) ^ (1 / 8 : ℝ) ≤ 2 := by
      rw [← Real.rpow_le_rpow_iff (z := (8 : ℝ)) (by positivity) (by norm_num) (by norm_num)]
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    have hsq : ((J.m : ℝ) ^ 2) ^ (1 / 8 : ℝ) = (J.m : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast (J.m : ℝ) 2, ← Real.rpow_mul (Nat.cast_nonneg _)]; congr 1; norm_num
    calc (((M₀ ^ 2 : ℕ) : ℝ) + 2) ^ (1 / 8 : ℝ)
        ≤ (50 * (J.m : ℝ) ^ 2) ^ (1 / 8 : ℝ) := Real.rpow_le_rpow (by positivity) hM2_add2_le (by norm_num)
      _ = (50 : ℝ) ^ (1 / 8 : ℝ) * ((J.m : ℝ) ^ 2) ^ (1 / 8 : ℝ) := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 * (J.m : ℝ) ^ (1 / 4 : ℝ) := by rw [hsq]; exact mul_le_mul_of_nonneg_right h50 (by positivity)
  have hden_le_r : (drySparsifyDen M₀ : ℝ) ≤ 2 * (K_den : ℝ) * (J.m : ℝ) ^ (1 / 4 : ℝ) := by
    have h1 : (drySparsifyDen M₀ : ℝ) ≤ C₁_p * Expander.subpolyB1 C₀_p (M₀ ^ 2) := by
      have hsb := hden_sb (M₀ ^ 2)
      rwa [dryDecomp_phi_lb_eq, one_div_one_div] at hsb
    have h2 : Expander.subpolyB1 C₀_p (M₀ ^ 2) ≤ B_den * (((M₀ ^ 2 : ℕ) : ℝ) + 2) ^ (1 / 8 : ℝ) :=
      hBden_le (((M₀ ^ 2 : ℕ) : ℝ) + 2) hM2_3
    have h3 : C₁_p * B_den ≤ (K_den : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈C₁_p * B_den⌉₊)
    calc (drySparsifyDen M₀ : ℝ)
        ≤ C₁_p * (B_den * (((M₀ ^ 2 : ℕ) : ℝ) + 2) ^ (1 / 8 : ℝ)) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith only [hC₁p]))
      _ = (C₁_p * B_den) * (((M₀ ^ 2 : ℕ) : ℝ) + 2) ^ (1 / 8 : ℝ) := by ring
      _ ≤ (K_den : ℝ) * (2 * (J.m : ℝ) ^ (1 / 4 : ℝ)) :=
          mul_le_mul h3 hM2_rpow (by positivity) (by positivity)
      _ = 2 * (K_den : ℝ) * (J.m : ℝ) ^ (1 / 4 : ℝ) := by ring
  have hden_cond : (drySparsifyDen M₀ : ℝ) ≤ C₁_p * Expander.subpolyB1 C₀_p (M₀ ^ 2) + 1 := by
    have hsb := hden_sb (M₀ ^ 2)
    rw [dryDecomp_phi_lb_eq, one_div_one_div] at hsb
    change (drySparsifyDen M₀ : ℝ) ≤ _ at hsb
    linarith only [hsb]
  have hge1_le : (pds.gExp (drySparsifyDen M₀) (M₀ ^ 2) : ℝ) ≤ 2 * (⌈B_ge1⌉₊ : ℝ) * (J.m : ℝ) ^ (1 / 4 : ℝ) :=
    ((hge1 _ _ (Expander.maxPhiDenOf_pos _ _ _) hden_cond).trans (hBge1_le _ hM2_pos)).trans
      ((mul_le_mul (Nat.le_ceil _) hM2_rpow (by positivity) (by positivity)).trans_eq (by ring))
  have hgd1_le : (pds.gDel (drySparsifyDen M₀) (M₀ ^ 2) : ℝ) ≤ 2 * (⌈B_gd1⌉₊ : ℝ) * (J.m : ℝ) ^ (1 / 4 : ℝ) :=
    ((hgd1 _ _ (Expander.maxPhiDenOf_pos _ _ _) hden_cond).trans (hBgd1_le _ hM2_pos)).trans
      ((mul_le_mul (Nat.le_ceil _) hM2_rpow (by positivity) (by positivity)).trans_eq (by ring))
  have hJm_ge1_r : (1 : ℝ) ≤ (J.m : ℝ) := by exact_mod_cast hJm
  have hJ14_le : (J.m : ℝ) ^ (1 / 4 : ℝ) ≤ (J.m : ℝ) ^ (9 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hJm_ge1_r (by norm_num)
  have hJ2_le : (J.m : ℝ) ^ 2 ≤ (J.m : ℝ) ^ (9 / 4 : ℝ) := by
    rw [← Real.rpow_natCast (J.m : ℝ) 2]
    exact Real.rpow_le_rpow_of_exponent_le hJm_ge1_r (by norm_num)
  have hJ94_ge1 : (1 : ℝ) ≤ (J.m : ℝ) ^ (9 / 4 : ℝ) := Real.one_le_rpow hJm_ge1_r (by norm_num)
  have hcap_le_r : (drySparsifyCap M₀ : ℝ) + 2 ≤ 49 * (K_cap : ℝ) * (J.m : ℝ) ^ (9 / 4 : ℝ) := by
    unfold drySparsifyCap
    have hM2_49 : ((M₀ ^ 2 : ℕ) : ℝ) ≤ 49 * (J.m : ℝ) ^ 2 := by
      exact_mod_cast (show M₀ ^ 2 ≤ 49 * J.m ^ 2 by nlinarith only [hM0_le_7Jm])
    have hpow94 : (J.m : ℝ) ^ 2 * (J.m : ℝ) ^ (1 / 4 : ℝ) = (J.m : ℝ) ^ (9 / 4 : ℝ) := by
      rw [← Real.rpow_natCast (J.m : ℝ) 2, ← Real.rpow_add (by positivity)]; congr 1; norm_num
    have h1 : 36 * (M₀ : ℝ) ^ 2 * (drySparsifyDen M₀ : ℝ) ≤
        36 * (49 * (J.m : ℝ) ^ 2) * (2 * (K_den : ℝ) * (J.m : ℝ) ^ (1 / 4 : ℝ)) := by
      simpa using mul_le_mul (mul_le_mul_of_nonneg_left hM2_49 (by norm_num)) hden_le_r (by positivity) (by positivity)
    push_cast
    calc 36 * (M₀ : ℝ) ^ 2 * (drySparsifyDen M₀ : ℝ) + 1 + 2
        ≤ 36 * (49 * (J.m : ℝ) ^ 2) * (2 * (K_den : ℝ) * (J.m : ℝ) ^ (1 / 4 : ℝ)) +
            49 * (J.m : ℝ) ^ (9 / 4 : ℝ) := by linarith only [h1, hJ94_ge1]
      _ = 49 * (72 * (K_den : ℝ) + 1) * (J.m : ℝ) ^ (9 / 4 : ℝ) := by rw [← hpow94]; ring
      _ ≤ 49 * (K_cap : ℝ) * (J.m : ℝ) ^ (9 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (by dsimp only [K_cap]; push_cast; linarith only []) (by positivity)
  have hcap_rpow : ((drySparsifyCap M₀ : ℝ) + 2) ^ (1 / 8 : ℝ) ≤
      49 * (K_cap : ℝ) * (J.m : ℝ) ^ (9 / 4 : ℝ) := by
    have hKcap1 : (1 : ℝ) ≤ (K_cap : ℝ) := by dsimp only [K_cap]; exact_mod_cast (by omega : 1 ≤ 72 * K_den + 2)
    calc ((drySparsifyCap M₀ : ℝ) + 2) ^ (1 / 8 : ℝ)
        ≤ (49 * (K_cap : ℝ) * (J.m : ℝ) ^ (9 / 4 : ℝ)) ^ (1 / 8 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hcap_le_r (by norm_num)
      _ ≤ (49 * (K_cap : ℝ) * (J.m : ℝ) ^ (9 / 4 : ℝ)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith only [hKcap1, hJ94_ge1]) (by norm_num)
      _ = 49 * (K_cap : ℝ) * (J.m : ℝ) ^ (9 / 4 : ℝ) := Real.rpow_one _
  have hwit_le_ceil : dryWitnessDen ≤ Nat.ceil (1 / Expander.constructExpanderImpl.φ_Const) := by
    rw [dryWitness_phi_Const_eq, one_div_one_div, Nat.ceil_natCast]
  have hcap_pos : 1 ≤ drySparsifyCap M₀ := by unfold drySparsifyCap; omega
  have hge2_le : (pds.gExp dryWitnessDen (drySparsifyCap M₀) : ℝ) ≤
      49 * (⌈B_ge2⌉₊ : ℝ) * (K_cap : ℝ) * (J.m : ℝ) ^ (9 / 4 : ℝ) :=
    ((hge2 _ _ one_le_dryWitnessDen hwit_le_ceil).trans (hBge2_le _ hcap_pos)).trans
      ((mul_le_mul (Nat.le_ceil _) hcap_rpow (by positivity) (by positivity)).trans_eq (by ring))
  have hgd2_le : (pds.gDel dryWitnessDen (drySparsifyCap M₀) : ℝ) ≤
      49 * (⌈B_gd2⌉₊ : ℝ) * (K_cap : ℝ) * (J.m : ℝ) ^ (9 / 4 : ℝ) :=
    ((hgd2 _ _ one_le_dryWitnessDen hwit_le_ceil).trans (hBgd2_le _ hcap_pos)).trans
      ((mul_le_mul (Nat.le_ceil _) hcap_rpow (by positivity) (by positivity)).trans_eq (by ring))
  have hKsum_mul : 49 * (K_sum : ℝ) * (J.m : ℝ) ^ (9 / 4 : ℝ) ≤ (J.m : ℝ) ^ 3 := by
    have hJ4_r' : (49 * (K_sum : ℝ)) ^ (1 : ℝ) ≤ (J.m : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_le_rpow_iff (z := (4 : ℝ)) (by positivity) (by positivity) (by norm_num),
        ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
      norm_num; exact_mod_cast (by omega : (49 * K_sum) ^ 4 ≤ J.m)
    have hle : 49 * (K_sum : ℝ) ≤ (J.m : ℝ) ^ (3 / 4 : ℝ) :=
      (Real.rpow_one _ ▸ hJ4_r').trans (Real.rpow_le_rpow_of_exponent_le hJm_ge1_r (by norm_num))
    calc 49 * (K_sum : ℝ) * (J.m : ℝ) ^ (9 / 4 : ℝ)
        ≤ (J.m : ℝ) ^ (3 / 4 : ℝ) * (J.m : ℝ) ^ (9 / 4 : ℝ) := mul_le_mul_of_nonneg_right hle (by positivity)
      _ = (J.m : ℝ) ^ ((3 / 4 : ℝ) + 9 / 4) := (Real.rpow_add (by positivity) _ _).symm
      _ = (J.m : ℝ) ^ 3 := by norm_num
  have hcoef1_nat : 2 * K_den + 49 + 2 * ⌈B_ge1⌉₊ + 2 * ⌈B_gd1⌉₊ + 2 ≤ 49 * K_sum := by
    dsimp only [K_sum]; omega
  have hcoef2_nat : dryWitnessDen + 49 * K_cap + 49 * ⌈B_ge2⌉₊ * K_cap + 49 * ⌈B_gd2⌉₊ * K_cap ≤
      49 * K_sum := by
    dsimp only [K_sum]; nlinarith
  have hsum1 : drySparsifyDen M₀ + M₀ ^ 2 + pds.gExp (drySparsifyDen M₀) (M₀ ^ 2) +
      pds.gDel (drySparsifyDen M₀) (M₀ ^ 2) + 2 ≤ J.m ^ 3 := by
    have hM2_49 : (M₀ : ℝ) ^ 2 ≤ 49 * (J.m : ℝ) ^ (9 / 4 : ℝ) := by
      have hsq : (M₀ : ℝ) ^ 2 ≤ 49 * (J.m : ℝ) ^ 2 := by
        exact_mod_cast (show M₀ ^ 2 ≤ 49 * J.m ^ 2 by nlinarith only [hM0_le_7Jm])
      linarith only [hsq, hJ2_le]
    have hden' := hden_le_r.trans (mul_le_mul_of_nonneg_left hJ14_le (by positivity))
    have hge1' := hge1_le.trans (mul_le_mul_of_nonneg_left hJ14_le (by positivity))
    have hgd1' := hgd1_le.trans (mul_le_mul_of_nonneg_left hJ14_le (by positivity))
    have hcoef : (2 * (K_den : ℝ) + 49 + 2 * (⌈B_ge1⌉₊ : ℝ) + 2 * (⌈B_gd1⌉₊ : ℝ) + 2) ≤
        49 * (K_sum : ℝ) := by exact_mod_cast hcoef1_nat
    have hcomb : ((drySparsifyDen M₀ + M₀ ^ 2 + pds.gExp (drySparsifyDen M₀) (M₀ ^ 2) +
        pds.gDel (drySparsifyDen M₀) (M₀ ^ 2) + 2 : ℕ) : ℝ) ≤
        (2 * (K_den : ℝ) + 49 + 2 * (⌈B_ge1⌉₊ : ℝ) + 2 * (⌈B_gd1⌉₊ : ℝ) + 2) *
          (J.m : ℝ) ^ (9 / 4 : ℝ) := by
      push_cast; linarith only [hden', hM2_49, hge1', hgd1', hJ94_ge1]
    exact_mod_cast hcomb.trans ((mul_le_mul_of_nonneg_right hcoef (by positivity)).trans hKsum_mul)
  have hsum2 : dryWitnessDen + drySparsifyCap M₀ + pds.gExp dryWitnessDen (drySparsifyCap M₀) +
      pds.gDel dryWitnessDen (drySparsifyCap M₀) + 2 ≤ J.m ^ 3 := by
    have hcoef : ((dryWitnessDen : ℝ) + 49 * (K_cap : ℝ) +
        49 * (⌈B_ge2⌉₊ : ℝ) * (K_cap : ℝ) + 49 * (⌈B_gd2⌉₊ : ℝ) * (K_cap : ℝ)) ≤
        49 * (K_sum : ℝ) := by exact_mod_cast hcoef2_nat
    have hwit_le : (dryWitnessDen : ℝ) ≤ (dryWitnessDen : ℝ) * (J.m : ℝ) ^ (9 / 4 : ℝ) :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) hJ94_ge1
    have hcomb : ((dryWitnessDen + drySparsifyCap M₀ +
        pds.gExp dryWitnessDen (drySparsifyCap M₀) +
        pds.gDel dryWitnessDen (drySparsifyCap M₀) + 2 : ℕ) : ℝ) ≤
        ((dryWitnessDen : ℝ) + 49 * (K_cap : ℝ) +
          49 * (⌈B_ge2⌉₊ : ℝ) * (K_cap : ℝ) + 49 * (⌈B_gd2⌉₊ : ℝ) * (K_cap : ℝ)) *
          (J.m : ℝ) ^ (9 / 4 : ℝ) := by
      push_cast; linarith only [hwit_le, hcap_le_r, hge2_le, hgd2_le]
    exact_mod_cast hcomb.trans ((mul_le_mul_of_nonneg_right hcoef (by positivity)).trans hKsum_mul)
  exact ⟨hsum1, hsum2⟩

/-- **Exact threshold theorem for `levelM`**: there exists a fixed threshold `M_cut` (depending
only on `dryWitnessUsed`, with `max threshold (2 ^ 32) ≤ M_cut`) such that for every valid
circulation `J` with `M_cut ≤ (solverConnectedAugmented J).m`:
1. `cfg.TP.γ_ℓ (M₀ ^ 2) = (dryGammaNat M₀ : ℝ)` (`3 ^ L * g ^ (L + 1)` dominates `11 * bundleSizeFactor`);
2. `levelM cfg.TP cfg.P i = (M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i - 1) / cfg.P.k ^ i`;
3. Both `pathDSBoundsContract` argument sums are at most `J.m ^ 3`. -/
theorem exists_dryLevelM_threshold :
    ∃ M_cut : ℕ,
      max (concreteEdgeThresholdWithLast dryWitnessUsed) (2 ^ 32) ≤ M_cut ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        M_cut ≤ (solverConnectedAugmented J).m →
        let I := solverConnectedAugmented J
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let M₀ := cfg.P.M₀
        let pds := sparsifyPathDSUsed.params
        M₀ = I.m ∧
        cfg.TP.γ_ℓ (M₀ ^ 2) = (dryGammaNat M₀ : ℝ) ∧
        (∀ i, Chain.levelM cfg.TP cfg.P i =
          (M₀ * dryGammaNat M₀ ^ (i + 1) + cfg.P.k ^ i - 1) / cfg.P.k ^ i) ∧
        drySparsifyDen M₀ + M₀ ^ 2 + pds.gExp (drySparsifyDen M₀) (M₀ ^ 2) +
          pds.gDel (drySparsifyDen M₀) (M₀ ^ 2) + 2 ≤ J.m ^ 3 ∧
        dryWitnessDen + drySparsifyCap M₀ + pds.gExp dryWitnessDen (drySparsifyCap M₀) +
          pds.gDel dryWitnessDen (drySparsifyCap M₀) + 2 ≤ J.m ^ 3 := by
  obtain ⟨M₁, hM₁, h1⟩ := exists_dryGamma_dominates
  obtain ⟨M₂, _, h2⟩ := exists_dryBoundsSums_le_cube
  refine ⟨max M₁ M₂, hM₁.trans (le_max_left _ _), fun J hJn hJm hCap hle => ?_⟩
  obtain ⟨hm, hγ, hl⟩ := h1 J hJn hJm hCap (le_trans (le_max_left _ _) hle)
  obtain ⟨hs1, hs2⟩ := h2 J hJn hJm hCap (le_trans (le_max_right _ _) hle)
  exact ⟨hm, hγ, hl, hs1, hs2⟩

end MinCostFlow.Final.DryRun

end
