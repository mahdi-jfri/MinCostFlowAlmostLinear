module

public import MinCostFlow.Final.AssemblyDryRunSCOpen
import MinCostFlow.Final.AssemblyDryRunSCFitsBounds
import MinCostFlow.Final.RuntimeQualityBounds
import MinCostFlow.Final.TimeFactorBounds
import MinCostFlow.MinRatio.ShiftDepositAsymptotics
import MinCostFlow.Chain.Theorem5_1Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# `SubpolyNat` and `PolyNat` bounds for `dryLastMult` and solver parameters (`AssemblyDryRunSCLastMult`)

Proves that evaluating `dryLastMult` at `levelM cfg.TP cfg.P cfg.P.d` (`Final/AssemblyDryRunSCOpen`)
gives a bound that depends on `M` alone: `dryLastMult J` is dominated by the `M`-only function `dryLastMultOfM I.m`,
and `SubpolyNat dryLastMultOfM` holds.

Also provides reusable `SubpolyNat` and `PolyNat` closure lemmas (`SubpolyNat.toPolyNat`,
`SubpolyNat.pow`, `SubpolyNat.max`, `subpolyNat_log_add_two`, `subpolyNat_log_of_poly`,
`subpolyNat_two_pow_dryKOfM`, `dryLimbsOfM_subpoly`, `dryLevelMd_le_two_pow_dryKOfM`,
`dryLastMultBound_le_poly`) used in `Final/AssemblyDryRunSCBounds.lean` to construct `B` and prove
`InnerBoundsHyp B`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program WideWord

/-! ## 1. Reusable `SubpolyNat` and `PolyNat` closure lemmas -/

theorem SubpolyNat.pow {f : ℕ → ℕ} (hf : SubpolyNat f) (q : ℕ) :
    SubpolyNat (fun M => (f M) ^ q) := by
  induction q with
  | zero => exact SubpolyNat.mono (fun M => by simp) (SubpolyNat.const 1)
  | succ q ih => exact SubpolyNat.mono (fun M => by rw [pow_succ]) (ih.mul hf)

theorem SubpolyNat.max_fn {f g : ℕ → ℕ} (hf : SubpolyNat f) (hg : SubpolyNat g) :
    SubpolyNat (fun M => Nat.max (f M) (g M)) :=
  SubpolyNat.mono (fun _ => Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩) (hf.add hg)

theorem PolyNat.max_fn {f g : ℕ → ℕ} (hf : PolyNat f) (hg : PolyNat g) :
    PolyNat (fun M => Nat.max (f M) (g M)) :=
  PolyNat.mono (fun _ => Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩) (hf.add hg)

theorem PolyNat.pow {f : ℕ → ℕ} (hf : PolyNat f) (q : ℕ) :
    PolyNat (fun M => (f M) ^ q) := by
  induction q with
  | zero => exact PolyNat.mono (fun M => by simp) (PolyNat.const 1)
  | succ q ih => exact PolyNat.mono (fun M => by rw [pow_succ]) (ih.mul hf)

theorem PolyNat.add_const {f : ℕ → ℕ} (hf : PolyNat f) (c : ℕ) :
    PolyNat (fun M => f M + c) :=
  hf.add (PolyNat.const c)

theorem PolyNat.const_mul {f : ℕ → ℕ} (hf : PolyNat f) (c : ℕ) :
    PolyNat (fun M => c * f M) :=
  (PolyNat.const c).mul hf

/-- Every `SubpolyNat` function is `PolyNat` (via `Chain.exp_subpoly_mul_loglog_le_rpow` at `δ = 1`). -/
theorem SubpolyNat.toPolyNat {f : ℕ → ℕ} (hf : SubpolyNat f) : PolyNat f := by
  obtain ⟨c, e, he, hbd⟩ := hf
  obtain ⟨B_exp, hBpos, hExpLe⟩ :=
    Chain.exp_subpoly_mul_loglog_le_rpow (a := 47 / 48) (C := e) (δ := 1)
      (by norm_num) (by norm_num) (by norm_num)
  let c₀ : ℝ := max c 0
  have hc₀ : 0 ≤ c₀ := le_max_right c 0
  let K : ℕ := max (f 0) (⌈c₀ * B_exp⌉₊ + 1)
  refine ⟨K, 1, fun M => ?_⟩
  cases M with
  | zero =>
    have h1 : f 0 ≤ K := le_max_left _ _
    have h2 : K ≤ K * (0 + 2) ^ 1 := by omega
    exact h1.trans h2
  | succ m =>
    have hM3 : (3 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) + 2 := by
      have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
      linarith
    have hTF : alg2TimeFactor e (47 / 48) (m + 1) ≤ B_exp * (((m + 1 : ℕ) : ℝ) + 2) := by
      rw [alg2TimeFactor_eq_exp_logShape, logShape, ← mul_assoc]
      simpa only [Real.rpow_one] using hExpLe (((m + 1 : ℕ) : ℝ) + 2) hM3
    have hfR : (f (m + 1) : ℝ) ≤ (K : ℝ) * (((m + 1 : ℕ) : ℝ) + 2) := by
      have h1 := hbd (m + 1)
      have h2 : c * alg2TimeFactor e (47 / 48) (m + 1) ≤ c₀ * alg2TimeFactor e (47 / 48) (m + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left c 0) (alg2TimeFactor_pos e (47 / 48) (m + 1)).le
      have h3 : c₀ * alg2TimeFactor e (47 / 48) (m + 1) ≤
          (c₀ * B_exp) * (((m + 1 : ℕ) : ℝ) + 2) := by
        have := mul_le_mul_of_nonneg_left hTF hc₀
        linarith
      have h4 : c₀ * B_exp ≤ (K : ℝ) := by
        have hc1 : c₀ * B_exp ≤ (⌈c₀ * B_exp⌉₊ : ℝ) := Nat.le_ceil _
        have hc2 : (⌈c₀ * B_exp⌉₊ : ℝ) ≤ (K : ℝ) := by
          exact_mod_cast le_trans (Nat.le_succ _) (le_max_right (f 0) _)
        linarith
      have h5 : (c₀ * B_exp) * (((m + 1 : ℕ) : ℝ) + 2) ≤ (K : ℝ) * (((m + 1 : ℕ) : ℝ) + 2) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      linarith
    have hfin : (f (m + 1) : ℝ) ≤ ((K * ((m + 1) + 2) ^ 1 : ℕ) : ℝ) := by
      simpa only [pow_one, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hfR
    exact_mod_cast hfin

/-- `Nat.log 2 (M + 2) + 1` is `SubpolyNat`. -/
theorem subpolyNat_log_add_two : SubpolyNat (fun M => Nat.log 2 (M + 2) + 1) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE : 0 ≤ (1 : ℝ) / (Real.log 2) ^ (47 / 48 : ℝ) := by positivity
  refine ⟨2, (1 : ℝ) / (Real.log 2) ^ (47 / 48 : ℝ), hE, fun M => ?_⟩
  have hlog_le : ((Nat.log 2 (M + 2) + 1 : ℕ) : ℝ) ≤ 2 * (Real.log ((M : ℝ) + 2) + 2) := by
    have hpow : 2 ^ Nat.log 2 (M + 2) ≤ M + 2 := Nat.pow_log_le_self 2 (by omega)
    have hpowR : (2 : ℝ) ^ Nat.log 2 (M + 2) ≤ (M : ℝ) + 2 := by exact_mod_cast hpow
    have hl := Real.log_le_log (by positivity) hpowR
    rw [Real.log_pow] at hl
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hnn : (0 : ℝ) ≤ Nat.log 2 (M + 2) := Nat.cast_nonneg _
    push_cast
    nlinarith
  have hpad := Final.paddedLog_pow_le_timeFactor 1 M
  simp only [pow_one, Nat.cast_one] at hpad
  linarith

/-- Any polynomial function `f` has `Nat.log 2 (f M + 2) + 1` in `SubpolyNat`. -/
theorem subpolyNat_log_of_poly {f : ℕ → ℕ} (hf : PolyNat f) :
    SubpolyNat (fun M => Nat.log 2 (f M + 2) + 1) := by
  obtain ⟨a, q, hbd⟩ := hf
  have hlog : ∀ M, Nat.log 2 (f M + 2) + 1 ≤ (a + 2).size + q * (Nat.log 2 (M + 2) + 1) + 2 := by
    intro M
    have h1 : f M + 2 ≤ (a + 2) * (M + 2) ^ q := by
      have hp1 : 1 ≤ (M + 2) ^ q := Nat.one_le_pow q (M + 2) (by omega)
      have := hbd M
      nlinarith
    have h2 : a + 2 < 2 ^ (a + 2).size := Nat.lt_size_self (a + 2)
    have h3 : (M + 2) ^ q ≤ 2 ^ (q * (Nat.log 2 (M + 2) + 1)) := by
      have hm : M + 2 ≤ 2 ^ (Nat.log 2 (M + 2) + 1) := (Nat.lt_pow_succ_log_self (by decide) _).le
      rw [mul_comm, pow_mul]
      exact Nat.pow_le_pow_left hm q
    have hlt : f M + 2 < 2 ^ ((a + 2).size + q * (Nat.log 2 (M + 2) + 1)) := by
      rw [pow_add]
      have hpos : 0 < 2 ^ (q * (Nat.log 2 (M + 2) + 1)) := Nat.two_pow_pos _
      exact lt_of_le_of_lt h1 (lt_of_le_of_lt (Nat.mul_le_mul_left (a + 2) h3)
        (Nat.mul_lt_mul_of_pos_right h2 hpos))
    have hl := (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr hlt
    omega
  exact SubpolyNat.mono hlog
    (((subpolyNat_log_add_two.const_mul q).add_const (a + 2).size).add_const 2 |>.mono
      (fun M => by omega))

theorem subpolyNat_size_of_poly {f : ℕ → ℕ} (hf : PolyNat f) :
    SubpolyNat (fun M => (f M + 2).size) := by
  have hle : ∀ M, (f M + 2).size ≤ Nat.log 2 (f M + 2) + 1 := fun M =>
    Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide) (f M + 2))
  exact SubpolyNat.mono hle (subpolyNat_log_of_poly hf)

/-! ## 2. Canonical `M`-only bounds for `dryWitnessUsed` -/

/-- Edge-count threshold `max M threshold` as a function of `M`. -/
def dryM0OfM (M : ℕ) : ℕ :=
  max M (concreteEdgeThresholdWithLast dryWitnessUsed)

/-- Quality exponent `cappedQualityExponent threshold A M` as a function of `M`. -/
def dryKOfM (M : ℕ) : ℕ :=
  cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) M

/-- Upper bound on the solver limb count as a function of `M`. -/
def dryLimbsOfM (M : ℕ) : ℕ :=
  ipmQualityLimbs M (solverPenalty M) (dryKOfM M)

/-- Upper bound on `dryLastMult` as a function of `M`, using `2 ^ dryKOfM M` as the
subpolynomial cap on `levelM cfg.TP cfg.P cfg.P.d`. -/
def dryLastMultOfM (M : ℕ) : ℕ :=
  dryLastMultBound (dryLimbsOfM M) (2 ^ dryKOfM M)

theorem dryM0OfM_poly : PolyNat dryM0OfM := by
  let thr := concreteEdgeThresholdWithLast dryWitnessUsed
  refine ⟨thr + 1, 1, fun M => ?_⟩
  change max M thr ≤ (thr + 1) * (M + 2) ^ 1
  rw [pow_one]
  rcases le_total M thr with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

/-- `2 ^ dryKOfM M` is `SubpolyNat`. -/
theorem subpolyNat_two_pow_dryKOfM : SubpolyNat (fun M => 2 ^ dryKOfM M) := by
  let thr := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let E : ℝ := 65536 * ((A : ℝ) + 1)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨alg2TimeFactor E (47 / 48) thr, E, hE, fun M => ?_⟩
  have h1 : ((2 ^ dryKOfM M : ℕ) : ℝ) ≤ alg2TimeFactor E (47 / 48) (max M thr) := by
    push_cast
    exact (Final.integerQualityExponent_bounds A (max M thr)).2
  exact h1.trans (alg2TimeFactor_max_le hE M thr)

/-- `dryKOfM` is `SubpolyNat`. -/
theorem dryKOfM_subpoly : SubpolyNat dryKOfM :=
  SubpolyNat.mono (fun _ => Nat.lt_two_pow_self.le) subpolyNat_two_pow_dryKOfM

/-- `dryLimbsOfM` is `SubpolyNat`. -/
theorem dryLimbsOfM_subpoly : SubpolyNat dryLimbsOfM := by
  have hPenPoly : PolyNat solverPenalty := by
    refine ⟨16, 81, fun M => ?_⟩
    cases M with
    | zero => simp [solverPenalty]
    | succ m =>
      have h1 := solverPenalty_le (m + 1) (Nat.succ_pos m)
      have h2 : (m + 1) ^ 81 ≤ ((m + 1) + 2) ^ 81 := Nat.pow_le_pow_left (by omega) 81
      exact h1.trans (Nat.mul_le_mul_left 16 h2)
  have hMsz : SubpolyNat (fun M => M.size) :=
    SubpolyNat.mono (fun M => Nat.size_le_size (by omega)) (subpolyNat_size_of_poly PolyNat.id)
  have hUsz : SubpolyNat (fun M => (solverPenalty M).size) :=
    SubpolyNat.mono (fun M => Nat.size_le_size (by omega)) (subpolyNat_size_of_poly hPenPoly)
  have hLe : ∀ M, dryLimbsOfM M ≤
      116 * dryKOfM M + 30000000 * (M.size + (solverPenalty M).size) ^ 2 +
      500000 * (M.size + (solverPenalty M).size) + 500000 := by
    intro M
    unfold dryLimbsOfM
    have h1 := ipmQualityLimbs_le M (solverPenalty M) (dryKOfM M)
    have hclog : Num.IPM.alphaExponent M (solverPenalty M) ≤ Num.IPM.alphaScale M (solverPenalty M) := by
      unfold Num.IPM.alphaExponent
      exact (Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self.le
    have hsq : (1000 * (M.size + (solverPenalty M).size)) ^ 2 =
        1000000 * (M.size + (solverPenalty M).size) ^ 2 := by ring
    unfold ipmLimbs ipmPrecision ipmErrorBits ipmRangeExponent slackRangeExponent
      gradientCoefficientExponent at h1
    unfold Num.IPM.alphaScale at h1 hclog
    omega
  exact SubpolyNat.mono hLe
    ((((dryKOfM_subpoly.const_mul 116).add
      ((SubpolyNat.pow (hMsz.add hUsz) 2).const_mul 30000000)).add
      ((hMsz.add hUsz).const_mul 500000)).add_const 500000)

/-- Monotonicity of `solverPenalty` in `m`. -/
private theorem solverPenalty_mono {a b : ℕ} (h : a ≤ b) : solverPenalty a ≤ solverPenalty b := by
  unfold solverPenalty solverCapacityBound
  have hpow : a ^ 40 ≤ b ^ 40 := Nat.pow_le_pow_left h 40
  have hmax : max 2 (a ^ 40) ≤ max 2 (b ^ 40) := max_le_max_left 2 hpow
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 h) (Nat.pow_le_pow_left hmax 2)

/-- Monotonicity of `ipmQualityLimbs` in its capacity bound `U`. -/
private theorem ipmQualityLimbs_mono_U {m U₁ U₂ k : ℕ} (hU : U₁ ≤ U₂) :
    ipmQualityLimbs m U₁ k ≤ ipmQualityLimbs m U₂ k := by
  have hsz : U₁.size ≤ U₂.size := Nat.size_le_size hU
  have hsq : (m.size + U₁.size) ^ 2 ≤ (m.size + U₂.size) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hα : Num.IPM.alphaExponent m U₁ ≤ Num.IPM.alphaExponent m U₂ := by
    unfold Num.IPM.alphaExponent Num.IPM.alphaScale
    exact Nat.clog_mono_right 2 (by omega)
  unfold ipmQualityLimbs ipmQualityPrecision ipmQualityErrorBits ipmQualityRangeExponent
    qualitySlackExponent slackRangeExponent gradientCoefficientExponent Num.IPM.alphaScale
  omega

/-- On every valid circulation `J`, the solver's limb count is at most `dryLimbsOfM I.m`. -/
theorem dryLimbs_le_ofM (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    ipmQualityLimbs I.m (solverPenalty J.m) k ≤ dryLimbsOfM I.m :=
  ipmQualityLimbs_mono_U (solverPenalty_mono (solverConnectedAugmented_size J hJn hJm hCap).1)

/-- Monotonicity of `dryLastMultBound L M` in `M` (at fixed `L`) and in `L` via `packedNonLoopDispatchMultiplier`
is not needed directly; instead we bound `dryLastMultBound L N` by an explicit polynomial in `L + N + 2`. -/
theorem dryLastMultBound_mono_M {L M₁ M₂ : ℕ} (hM : M₁ ≤ M₂) :
    dryLastMultBound L M₁ ≤ dryLastMultBound L M₂ := by
  unfold dryLastMultBound
  apply Finset.sup_mono
  intro nm hnm
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hnm
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp h1; omega),
    Finset.mem_range.mpr (by have := Finset.mem_range.mp h2; omega)⟩

/-! ## 3. Polynomial-in-`(L + N + 2)` upper bound on `dryLastMultBound L N` -/

private theorem log_le_self_add (x : ℕ) : Nat.log 2 x ≤ x :=
  Nat.log_le_self 2 x

private theorem size_le_self_add (x : ℕ) : x.size ≤ x :=
  Nat.size_le.mpr Nat.lt_two_pow_self

private theorem real_log_le_nat (x : ℕ) : Real.log ((x : ℝ) + 2) ≤ (x : ℝ) + 2 :=
  (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)

private theorem lsstOverheadFactor_le_poly (Q : Program) (c : ℕ) (K : ℝ) :
    ∃ C : ℕ, ∀ n m B : ℕ,
      ⌈lsstOverheadFactor Q c K n m B⌉₊ ≤ C * (n + m + B + 2) ^ 4 := by
  let S : ℕ := max 1 (simScale Q)
  let K0 : ℕ := ⌈max K 1⌉₊ + 1
  let c1 : ℕ := max 1 c
  let Wc : ℕ := c1 * 25
  refine ⟨Wc ^ 2 + S * Wc ^ 2 * (K0 * (2 + Wc + 4) + 1) + 2, fun n m B => ?_⟩
  set Z : ℕ := n + m + B + 2
  have hZ1 : 1 ≤ Z := by omega
  have hZ_sq : Z ≤ Z ^ 2 := Nat.le_self_pow (by decide) Z
  have hZ_4 : Z ^ 2 ≤ Z ^ 4 := Nat.pow_le_pow_right hZ1 (by decide)
  have hZ_3_4 : Z ^ 3 ≤ Z ^ 4 := Nat.pow_le_pow_right hZ1 (by decide)
  have hkw : kWidthOf m B ≤ 5 * Z := by
    unfold kWidthOf
    have hl := Nat.log_le_self 2 (4 * m + 2)
    omega
  have hw' : w'Max c n m B 1 ≤ Wc * Z := by
    unfold w'Max
    have hl := Nat.log_le_self 2 (6 + 16 * m)
    have h1 : Nat.log 2 (6 + 16 * m) + kWidthOf m B * 1 + 3 ≤ 25 * Z := by omega
    have hc : c ≤ c1 := le_max_right 1 c
    calc c * (Nat.log 2 (6 + 16 * m) + kWidthOf m B * 1 + 3)
        ≤ c1 * (25 * Z) := Nat.mul_le_mul hc h1
      _ = Wc * Z := by dsimp only [Wc]; ring
  have hLsim : lsstLSimMin c n m B 1 ≤ Wc * Z := by
    unfold lsstLSimMin
    have h5 : 5 ≤ Wc := by dsimp only [Wc, c1]; have : 1 ≤ max 1 c := le_max_left 1 c; omega
    exact max_le (hkw.trans (Nat.mul_le_mul_right Z h5)) hw'
  have hLsimR : (lsstLSimMin c n m B 1 : ℝ) ≤ (Wc : ℝ) * (Z : ℝ) := by exact_mod_cast hLsim
  have hw'R : (w'Max c n m B 1 : ℝ) ≤ (Wc : ℝ) * (Z : ℝ) := by exact_mod_cast hw'
  have hll : Cited.logLogFactor n ≤ (Z : ℝ) ^ 2 := by
    unfold Cited.logLogFactor
    have h1 : Real.log ((n : ℝ) + 2) ≤ (Z : ℝ) := by
      have := real_log_le_nat n
      have hle : (n : ℝ) + 2 ≤ (Z : ℝ) := by exact_mod_cast (show n + 2 ≤ Z by omega)
      linarith
    have h0 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have h2 : Real.log (Real.log ((n : ℝ) + 2)) ≤ (Z : ℝ) := by
      by_cases hpos : 0 < Real.log ((n : ℝ) + 2)
      · exact ((Real.log_le_sub_one_of_pos hpos).trans (by linarith)).trans h1
      · have hzero : Real.log ((n : ℝ) + 2) = 0 := le_antisymm (not_lt.mp hpos) h0
        rw [hzero, Real.log_zero]; positivity
    have hmul := mul_le_mul_of_nonneg_left h2 h0
    have hsq : Real.log ((n : ℝ) + 2) * (Z : ℝ) ≤ (Z : ℝ) * (Z : ℝ) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    linarith [sq (Z : ℝ)]
  have hwf : Cited.weightFactor n (2 ^ lsstLSimMin c n m B 1) ≤ (Z : ℝ) * ((Wc : ℝ) * (Z : ℝ) + 4) := by
    unfold Cited.weightFactor
    have h1 : Real.log ((n : ℝ) + 2) ≤ (Z : ℝ) := by
      have := real_log_le_nat n
      have hle : (n : ℝ) + 2 ≤ (Z : ℝ) := by exact_mod_cast (show n + 2 ≤ Z by omega)
      linarith
    have h0 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hpow : ((2 ^ lsstLSimMin c n m B 1 : ℕ) : ℝ) + 2 ≤ (2 : ℝ) ^ (lsstLSimMin c n m B 1 + 2) := by
      push_cast
      have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ lsstLSimMin c n m B 1 := one_le_pow₀ (by norm_num)
      rw [pow_add]; norm_num; linarith
    have hlog1 : Real.log (((2 ^ lsstLSimMin c n m B 1 : ℕ) : ℝ) + 2) ≤ (lsstLSimMin c n m B 1 : ℝ) + 2 := by
      have hl := Real.log_le_log (by positivity) hpow
      rw [Real.log_pow] at hl
      have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      push_cast at hl ⊢
      nlinarith [Nat.cast_nonneg (α := ℝ) (lsstLSimMin c n m B 1)]
    have hlog2 : Real.log (Real.log (((2 ^ lsstLSimMin c n m B 1 : ℕ) : ℝ) + 2) + 2) ≤
        (Wc : ℝ) * (Z : ℝ) + 4 := by
      have hp : 0 < Real.log (((2 ^ lsstLSimMin c n m B 1 : ℕ) : ℝ) + 2) + 2 := by
        have h1 : (1 : ℝ) ≤ ((2 ^ lsstLSimMin c n m B 1 : ℕ) : ℝ) + 2 := by
          have : (0 : ℝ) ≤ ((2 ^ lsstLSimMin c n m B 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        have := Real.log_nonneg h1
        linarith
      exact (Real.log_le_sub_one_of_pos hp).trans (by linarith)
    have hlog2_nn : 0 ≤ (Wc : ℝ) * (Z : ℝ) + 4 := by positivity
    calc Real.log ((n : ℝ) + 2) * Real.log (Real.log (((2 ^ lsstLSimMin c n m B 1 : ℕ) : ℝ) + 2) + 2)
        ≤ Real.log ((n : ℝ) + 2) * ((Wc : ℝ) * (Z : ℝ) + 4) := mul_le_mul_of_nonneg_left hlog2 h0
      _ ≤ (Z : ℝ) * ((Wc : ℝ) * (Z : ℝ) + 4) := mul_le_mul_of_nonneg_right h1 hlog2_nn
  have hK0 : max K 1 ≤ (K0 : ℝ) := by
    have : max K 1 ≤ (⌈max K 1⌉₊ : ℝ) := Nat.le_ceil _
    have : (⌈max K 1⌉₊ : ℝ) ≤ (K0 : ℝ) := by exact_mod_cast Nat.le_succ _
    linarith
  have hS : (simScale Q : ℝ) ≤ (S : ℝ) := by exact_mod_cast le_max_right 1 (simScale Q)
  have hZR1 : (1 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ1
  have hZR2 : (Z : ℝ) ^ 2 ≤ (Z : ℝ) ^ 4 := by exact_mod_cast hZ_4
  have hZR3 : (Z : ℝ) ^ 3 ≤ (Z : ℝ) ^ 4 := by exact_mod_cast hZ_3_4
  have hinner : max K 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ lsstLSimMin c n m B 1)) + 1 ≤
      ((K0 * (2 + Wc + 4) + 1 : ℕ) : ℝ) * (Z : ℝ) ^ 2 := by
    have hsum : Cited.logLogFactor n + Cited.weightFactor n (2 ^ lsstLSimMin c n m B 1) ≤
        ((2 + Wc + 4 : ℕ) : ℝ) * (Z : ℝ) ^ 2 := by
      push_cast; nlinarith
    have hmul : max K 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ lsstLSimMin c n m B 1)) ≤
        (K0 : ℝ) * (((2 + Wc + 4 : ℕ) : ℝ) * (Z : ℝ) ^ 2) := by
      have hKnn : 0 ≤ max K 1 := le_trans zero_le_one (le_max_right K 1)
      have h1 := mul_le_mul_of_nonneg_left hsum hKnn
      have h2 := mul_le_mul_of_nonneg_right hK0 (by positivity : 0 ≤ ((2 + Wc + 4 : ℕ) : ℝ) * (Z : ℝ) ^ 2)
      linarith
    have hZ2_ge1 : (1 : ℝ) ≤ (Z : ℝ) ^ 2 := by nlinarith
    push_cast at hmul ⊢
    nlinarith
  have hov : lsstOverheadFactor Q c K n m B ≤
      (((Wc ^ 2 + S * Wc ^ 2 * (K0 * (2 + Wc + 4) + 1)) : ℕ) : ℝ) * (Z : ℝ) ^ 4 := by
    unfold lsstOverheadFactor
    have hsq1 : (lsstLSimMin c n m B 1 : ℝ) ^ 2 ≤ (Wc : ℝ) ^ 2 * (Z : ℝ) ^ 2 := by
      calc (lsstLSimMin c n m B 1 : ℝ) ^ 2 ≤ ((Wc : ℝ) * (Z : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hLsimR 2
        _ = (Wc : ℝ) ^ 2 * (Z : ℝ) ^ 2 := by ring
    have hprod : (simScale Q : ℝ) * (lsstLSimMin c n m B 1 : ℝ) * (w'Max c n m B 1 : ℝ) ≤
        (S : ℝ) * (Wc : ℝ) ^ 2 * (Z : ℝ) ^ 2 := by
      have h1 : (lsstLSimMin c n m B 1 : ℝ) * (w'Max c n m B 1 : ℝ) ≤
          ((Wc : ℝ) * (Z : ℝ)) * ((Wc : ℝ) * (Z : ℝ)) :=
        mul_le_mul hLsimR hw'R (Nat.cast_nonneg _) (by positivity)
      have h2 : (simScale Q : ℝ) * ((lsstLSimMin c n m B 1 : ℝ) * (w'Max c n m B 1 : ℝ)) ≤
          (S : ℝ) * (((Wc : ℝ) * (Z : ℝ)) * ((Wc : ℝ) * (Z : ℝ))) :=
        mul_le_mul hS h1 (by positivity) (by positivity)
      linarith
    have hterm2 : (simScale Q : ℝ) * (lsstLSimMin c n m B 1 : ℝ) * (w'Max c n m B 1 : ℝ) *
        (max K 1 * (Cited.logLogFactor n + Cited.weightFactor n (2 ^ lsstLSimMin c n m B 1)) + 1) ≤
        ((S * Wc ^ 2 * (K0 * (2 + Wc + 4) + 1) : ℕ) : ℝ) * (Z : ℝ) ^ 4 := by
      have h1 := mul_le_mul_of_nonneg_left hinner
        (by positivity : 0 ≤ (simScale Q : ℝ) * (lsstLSimMin c n m B 1 : ℝ) * (w'Max c n m B 1 : ℝ))
      have h2 := mul_le_mul_of_nonneg_right hprod
        (by positivity : 0 ≤ ((K0 * (2 + Wc + 4) + 1 : ℕ) : ℝ) * (Z : ℝ) ^ 2)
      push_cast at h1 h2 ⊢
      nlinarith
    have hWcSq : (Wc : ℝ) ^ 2 * (Z : ℝ) ^ 2 ≤ (Wc : ℝ) ^ 2 * (Z : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left hZR2 (sq_nonneg _)
    push_cast at hterm2 ⊢
    linarith
  refine Nat.ceil_le.mpr ?_
  have h1 : (((Wc ^ 2 + S * Wc ^ 2 * (K0 * (2 + Wc + 4) + 1)) : ℕ) : ℝ) * (Z : ℝ) ^ 4 ≤
      (((Wc ^ 2 + S * Wc ^ 2 * (K0 * (2 + Wc + 4) + 1) + 2) * Z ^ 4 : ℕ) : ℝ) := by
    push_cast; nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) Z) 4]
  exact hov.trans h1

private lemma nat_size_le_self (n : ℕ) : n.size ≤ n :=
  Nat.size_le.mpr Nat.lt_two_pow_self

/-- Polynomial-in-`(L + N + 2)` bound on `representativePackedDispatchMultiplier` + scalar cost,
abstract in `guest` so `lsstModule lastGuest` is never unfolded by tactics. -/
private theorem repPackedDispatch_le_poly (guest : Program) (c D : ℕ) (K : ℝ) :
    ∃ C : ℕ, ∀ L N n m : ℕ, n ≤ N + 1 → m ≤ N →
      representativePackedDispatchMultiplier guest c D K L n m +
        (argsSize collectionGuestFormatArgs + 40 * (Nat.log 2 (n + 2) + 1) +
          40 * ((1024 * D).size + 3 * (m + 1).size) +
          40 * (Nat.log 2 (4 * m + 2) + Nat.log 2 (16 * m + 6) + 2) + 169 +
          argsSize packedControllerInputArgs + 4) ≤
      C * (L + N + 2) ^ 6 := by
  obtain ⟨C_ov, hOv⟩ := lsstOverheadFactor_le_poly guest c K
  generalize hR_eq : (Program.mk (lsstModule guest 0 1)).regBound = R
  generalize hgE_eq : (guestWorkspaceExpr guest D (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 4)).size = gE
  generalize ha1 : argsSize paddedWidthArgs = a1
  generalize ha2 : argsSize stagedGuestWeightsArgs = a2
  generalize ha3 : argsSize (stagedConvertedTreeArgs R) = a3
  generalize ha4 : stagedConvertedGuestCursor.size = a4
  generalize ha5 : argsSize collectionGuestFormatArgs = a5
  generalize ha6 : argsSize packedControllerInputArgs = a6
  generalize ha7 : (1024 * D).size = a7
  generalize hsc : simScale guest = sG
  let gConst : ℕ := gE + a1 + a2 + a3 + a4 + a5 + a6 + a7 + argsSize publishedRoundArgs + 50000
  let Bmul : ℕ := 20 + a7
  let Smul : ℕ := max 1 c * 25 * Bmul
  let C_gw : ℕ := 10000 + (D * 100 + 2000) * Smul ^ 2 + sG * Smul * (D * 100 * Smul ^ 2 + 50)
  let C_tot : ℕ :=
    (R + 6) * 48000 * C_ov * (Bmul + 2) ^ 4 + 40 * C_gw + 500000 * Bmul ^ 2 + 4 * gConst + 50000
  refine ⟨C_tot, fun L N n m hn hm => ?_⟩
  set Z : ℕ := L + N + 2
  have hZ_eq : Z = L + N + 2 := rfl
  have hZ1 : 1 ≤ Z := by omega
  have hZ_pow : ∀ a b : ℕ, a ≤ b → Z ^ a ≤ Z ^ b := fun a b hab => Nat.pow_le_pow_right hZ1 hab
  have hZ12 : Z ≤ Z ^ 2 := by simpa only [pow_one] using hZ_pow 1 2 (by decide)
  have hZ13 : Z ≤ Z ^ 3 := by simpa only [pow_one] using hZ_pow 1 3 (by decide)
  have hZ15 : Z ≤ Z ^ 5 := by simpa only [pow_one] using hZ_pow 1 5 (by decide)
  have hZ16 : Z ≤ Z ^ 6 := by simpa only [pow_one] using hZ_pow 1 6 (by decide)
  have hZ23 : Z ^ 2 ≤ Z ^ 3 := hZ_pow 2 3 (by decide)
  have hZ26 : Z ^ 2 ≤ Z ^ 6 := hZ_pow 2 6 (by decide)
  have hZ34 : Z ^ 3 ≤ Z ^ 4 := hZ_pow 3 4 (by decide)
  have hZ45 : Z ^ 4 ≤ Z ^ 5 := hZ_pow 4 5 (by decide)
  have hZ46 : Z ^ 4 ≤ Z ^ 6 := hZ_pow 4 6 (by decide)
  have hZ56 : Z ^ 5 ≤ Z ^ 6 := hZ_pow 5 6 (by decide)
  unfold representativePackedDispatchMultiplier
    representativePackedRuntimeMultiplier representativePackedSetupRoundsMultiplier
    runtimeEndpointMultiplier representativeInputMultiplier representativeGuestSetupMultiplier
    representativePackedRoundMultiplier representativeStagedRoundMultiplier
    representativeSelectorMultiplier
  dsimp only
  rw [hR_eq]
  set B := representativeGuestWidthBound D L m
  have hBmul1 : 1 ≤ Bmul := by dsimp only [Bmul]; omega
  have hBmul2 : Bmul ≤ Bmul ^ 2 := Nat.le_self_pow (by decide) Bmul
  have hB_le : B ≤ Bmul * Z := by
    unfold B representativeGuestWidthBound
    have hs1 := nat_size_le_self (2 * m)
    have hs2 := nat_size_le_self (m + 1)
    have hBm : 20 + a7 ≤ Bmul := by dsimp only [Bmul]; omega
    have hm1 : max (2 * m).size (4 * L) ≤ 2 * m + 4 * L :=
      max_le (hs1.trans (Nat.le_add_right _ _)) (Nat.le_add_left _ _)
    have hm2 : max (4 * L) (a7 + 3 * (m + 1).size) ≤ 4 * L + a7 + 3 * (m + 1) :=
      max_le (by omega) (by omega)
    have hsum : B ≤ 8 * L + 5 * m + a7 + 4 := by
      unfold B representativeGuestWidthBound; rw [ha7]; omega
    have hsumZ : 8 * L + 5 * m + a7 + 4 ≤ (20 + a7) * Z := by
      have h1 : 8 * L + 5 * m + 4 ≤ 20 * Z := by omega
      have h2 : a7 ≤ a7 * Z := Nat.le_mul_of_pos_right a7 hZ1
      nlinarith only [h1, h2]
    exact hsum.trans (hsumZ.trans (Nat.mul_le_mul_right Z hBm))
  have hSim_le : lsstLSimMin c n m B 1 ≤ Smul * Z := by
    unfold lsstLSimMin w'Max kWidthOf
    have hl1 := Nat.log_le_self 2 (6 + 16 * m)
    have hl2 := Nat.log_le_self 2 (4 * m + 2)
    have h1 : B + (Nat.log 2 (4 * m + 2) + 1) + 2 ≤ 5 * Bmul * Z := by
      have h4m : Nat.log 2 (4 * m + 2) + 1 + 2 ≤ 4 * Z := by omega
      nlinarith only [hB_le, h4m, hBmul1, hZ1]
    have h2 : c * (Nat.log 2 (6 + 16 * m) +
        (B + (Nat.log 2 (4 * m + 2) + 1) + 2) * 1 + 3) ≤ Smul * Z := by
      have h16m : Nat.log 2 (6 + 16 * m) + 3 ≤ 16 * Z := by omega
      have h3 : Nat.log 2 (6 + 16 * m) + (B + (Nat.log 2 (4 * m + 2) + 1) + 2) * 1 + 3 ≤
          25 * Bmul * Z := by nlinarith only [h1, h16m, hBmul1, hZ1]
      have hc : c ≤ max 1 c := le_max_right _ _
      calc c * _ ≤ max 1 c * (25 * Bmul * Z) := Nat.mul_le_mul hc h3
        _ = Smul * Z := by dsimp only [Smul]; ring
    have h1' : B + (Nat.log 2 (4 * m + 2) + 1) + 2 ≤ Smul * Z := by
      have hle : 5 * Bmul ≤ Smul := by
        dsimp only [Smul]; have h1c : 1 ≤ max 1 c := le_max_left _ _; nlinarith only [h1c, hBmul1]
      exact h1.trans (Nat.mul_le_mul_right Z hle)
    exact max_le h1' h2
  have hOv_le : ⌈lsstOverheadFactor guest c K n m B⌉₊ ≤ C_ov * (Bmul + 2) ^ 4 * Z ^ 4 := by
    have h1 := hOv n m B
    have harg : n + m + B + 2 ≤ (Bmul + 2) * Z := by
      have hnm : n + m + 2 ≤ 2 * Z := by omega
      nlinarith only [hnm, hB_le]
    have hpow : (n + m + B + 2) ^ 4 ≤ (Bmul + 2) ^ 4 * Z ^ 4 := by
      rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left harg 4
    exact h1.trans (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left C_ov hpow)
  have hSmul1 : 1 ≤ Smul := by
    dsimp only [Smul]; have h1c : 1 ≤ max 1 c := le_max_left _ _; nlinarith only [h1c, hBmul1]
  have hSm2 : Smul ≤ Smul ^ 2 := Nat.le_self_pow (by decide) Smul
  have hS2 : 2 ≤ Smul := by
    dsimp only [Smul]; have h1c : 1 ≤ max 1 c := le_max_left _ _; nlinarith only [h1c, hBmul1]
  have hBmul_Smul : Bmul ≤ Smul := by
    dsimp only [Smul]; have h1c : 1 ≤ max 1 c := le_max_left _ _; nlinarith only [h1c, hBmul1]
  have hGW_le : guestWorkspaceCost guest D n (lsstLSimMin c n m B 1) +
      40 * paddedGuestWidth guest D n m (lsstLSimMin c n m B 1)
        ((2 + 2 * B) * m + 3 * n + 2) ≤
      40 * C_gw * Z ^ 5 + gConst := by
    have h1 : guestWorkspaceCost guest D n (lsstLSimMin c n m B 1) ≤
        40 * (Z + Smul * Z + 6) + gConst := by
      unfold guestWorkspaceCost
      rw [hgE_eq]
      have hs1 := nat_size_le_self (n + 2)
      have hs2 := nat_size_le_self (lsstLSimMin c n m B 1 + 4)
      have hg : gE + 80 ≤ gConst := by dsimp only [gConst]; omega
      omega
    have h2 : paddedGuestWidth guest D n m (lsstLSimMin c n m B 1)
        ((2 + 2 * B) * m + 3 * n + 2) ≤
        5 + ((2 + 2 * B) * m + 3 * n + 2) +
          guestWorkspace guest D n m (lsstLSimMin c n m B 1) + 1 := by
      unfold paddedGuestWidth
      have hl := Nat.log_le_self 2
        (((2 + 2 * B) * m + 3 * n + 2) + guestWorkspace guest D n m (lsstLSimMin c n m B 1))
      omega
    have h3 : ((2 + 2 * B) * m + 3 * n + 2) +
        guestWorkspace guest D n m (lsstLSimMin c n m B 1) ≤
        (C_gw - (2 * Smul + 100)) * Z ^ 5 := by
      set sim := lsstLSimMin c n m B 1
      unfold guestWorkspace weightsSpace Num.integerDivideSpace Num.unsignedDivideSpace
        simDecodeSpace guestCitedCostBound
      dsimp only
      rw [hsc]
      have hs1 : (n + 2).size ≤ 2 * Z := (nat_size_le_self _).trans (by omega)
      have hs2 : (sim + 4).size ≤ (Smul + 4) * Z := by
        have hss := nat_size_le_self (sim + 4)
        nlinarith only [hss, hSim_le, hZ1]
      have hSim2 : sim ^ 2 ≤ Smul ^ 2 * Z ^ 2 := by
        rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left hSim_le 2
      have hdiv : 5 * (2 * sim) * (2 * sim + 1) ≤ 30 * Smul ^ 2 * Z ^ 2 := by
        have hSZ : Smul * Z ≤ Smul ^ 2 * Z ^ 2 := Nat.mul_le_mul hSm2 hZ12
        nlinarith only [hSim_le, hSim2, hSZ]
      have hcost_le : D * (4 * m + 1) * (n + 2).size * ((n + 2).size + (sim + 4).size) ≤
          D * 100 * Smul * Z ^ 3 := by
        have ha : 4 * m + 1 ≤ 4 * Z := by omega
        have hb : (n + 2).size + (sim + 4).size ≤ 7 * Smul * Z := by
          nlinarith only [hs1, hs2, hSmul1, hZ1]
        calc D * (4 * m + 1) * (n + 2).size * ((n + 2).size + (sim + 4).size)
            ≤ D * (4 * Z) * (2 * Z) * (7 * Smul * Z) := by gcongr
          _ = D * 56 * Smul * Z ^ 3 := by ring
          _ ≤ D * 100 * Smul * Z ^ 3 := by gcongr; omega
      have hsim_cost : sG * sim * 2 ^ 1 *
          (D * (4 * m + 1) * (n + 2).size * ((n + 2).size + (sim + 4).size) +
            (2 + 3 * (4 * m)) + 1) ≤
          sG * Smul * (D * 100 * Smul ^ 2 + 50) * Z ^ 4 := by
        have h1' : D * (4 * m + 1) * (n + 2).size * ((n + 2).size + (sim + 4).size) +
            (2 + 3 * (4 * m)) + 1 ≤ (D * 100 * Smul + 15) * Z ^ 3 := by
          have hm15 : 2 + 3 * (4 * m) + 1 ≤ 15 * Z := by omega
          nlinarith only [hcost_le, hm15, hZ13]
        have h2' : sG * sim * 2 ^ 1 ≤ 2 * sG * Smul * Z := by
          have := Nat.mul_le_mul_left sG hSim_le
          nlinarith only [this]
        have h3' : 2 * (D * 100 * Smul + 15) ≤ D * 100 * Smul ^ 2 + 50 := by
          have hDS : 2 * Smul ≤ Smul ^ 2 := by nlinarith only [hS2]
          have := Nat.mul_le_mul_left (D * 100) hDS
          nlinarith only [this]
        calc sG * sim * 2 ^ 1 * _
            ≤ (2 * sG * Smul * Z) * ((D * 100 * Smul + 15) * Z ^ 3) := Nat.mul_le_mul h2' h1'
          _ = sG * Smul * (2 * (D * 100 * Smul + 15)) * Z ^ 4 := by ring
          _ ≤ sG * Smul * (D * 100 * Smul ^ 2 + 50) * Z ^ 4 := by gcongr
      have hrest : (2 + 2 * B) * m + 3 * n + 2 +
          ((4 + 9 * n + 4 * m + m * sim) +
            (13 * sim + m * (18 * sim + 2 * (3 * (2 * sim) + 2 + 5 * (2 * sim) * (2 * sim + 1) + 3 * (2 * sim)))) +
            2 * m + (2 + 3 * (4 * m)) * sim +
            (5 + (1 + 2 * m) * sim + sim + (2 + 3 * (4 * m)) * (sim * 2 ^ 1 + sim))) ≤
          1000 * Smul ^ 2 * Z ^ 3 := by
        have hB1 : B ≤ Smul * Z := hB_le.trans (Nat.mul_le_mul_right Z hBmul_Smul)
        have hnZ : n ≤ Z := by omega
        have hmZ : m ≤ Z := by omega
        have hSZ : Smul * Z ≤ Smul ^ 2 * Z ^ 2 := Nat.mul_le_mul hSm2 hZ12
        have hdiv_m : m * (18 * sim + 2 * (3 * (2 * sim) + 2 + 5 * (2 * sim) * (2 * sim + 1) + 3 * (2 * sim))) ≤
            120 * Smul ^ 2 * Z ^ 3 := by
          have hinner' : 18 * sim + 2 * (3 * (2 * sim) + 2 + 5 * (2 * sim) * (2 * sim + 1) + 3 * (2 * sim)) ≤
              120 * Smul ^ 2 * Z ^ 2 := by
            nlinarith only [hdiv, hSim_le, hSZ, hSmul1, hSm2, hZ1, hZ12]
          calc m * _ ≤ Z * (120 * Smul ^ 2 * Z ^ 2) := Nat.mul_le_mul hmZ hinner'
            _ = 120 * Smul ^ 2 * Z ^ 3 := by ring
        nlinarith only [hB1, hSim_le, hSmul1, hSm2, hZ1, hZ12, hZ13, hZ23, hnZ, hmZ, hdiv_m]
      have hCgw_ge : 1000 * Smul ^ 2 + sG * Smul * (D * 100 * Smul ^ 2 + 50) + (2 * Smul + 100) ≤ C_gw := by
        have h1000 : 2000 * Smul ^ 2 ≤ (D * 100 + 2000) * Smul ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
        dsimp only [C_gw]; omega
      have hsum3 : 1000 * Smul ^ 2 * Z ^ 3 + sG * Smul * (D * 100 * Smul ^ 2 + 50) * Z ^ 4 ≤
          (C_gw - (2 * Smul + 100)) * Z ^ 5 := by
        calc 1000 * Smul ^ 2 * Z ^ 3 + sG * Smul * (D * 100 * Smul ^ 2 + 50) * Z ^ 4
            ≤ 1000 * Smul ^ 2 * Z ^ 5 + sG * Smul * (D * 100 * Smul ^ 2 + 50) * Z ^ 5 :=
              Nat.add_le_add (Nat.mul_le_mul_left _ (hZ_pow 3 5 (by decide)))
                (Nat.mul_le_mul_left _ hZ45)
          _ = (1000 * Smul ^ 2 + sG * Smul * (D * 100 * Smul ^ 2 + 50)) * Z ^ 5 := by ring
          _ ≤ (C_gw - (2 * Smul + 100)) * Z ^ 5 := Nat.mul_le_mul_right _ (by omega)
      omega
    have h100 : 2 * Smul + 100 ≤ C_gw := by
      have h1000 : 2000 * Smul ^ 2 ≤ (D * 100 + 2000) * Smul ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
      dsimp only [C_gw]; omega
    have hSubEq : (C_gw - (2 * Smul + 100)) * Z ^ 5 + (2 * Smul + 100) * Z ^ 5 = C_gw * Z ^ 5 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel h100]
    have hSmul_le_C : Z + Smul * Z + 12 ≤ (2 * Smul + 100) * Z ^ 5 := by
      nlinarith only [hZ1, hZ15, hSmul1]
    nlinarith only [h1, h2, h3, hSubEq, hSmul_le_C]
  have hStaged : stagedNumericFactor L (n + 2).size +
      stagedNumericFactor (2 * L + (n + 2).size + 1) (n + 2).size ≤ 300000 * Z ^ 2 := by
    unfold stagedNumericFactor edgeStretchCost stretchFromLengthCost narrowWeightCost
      widenWeightCost weightUpdateCost
    dsimp only
    have hs := nat_size_le_self (n + 2)
    have h1 : (n + 2).size ≤ 2 * Z := hs.trans (by omega)
    have h2 : L ≤ Z := by omega
    nlinarith only [h1, h2, hZ1]
  have hlog1 := Nat.log_le_self 2 (2 * m + 1)
  have hlog2 := Nat.log_le_self 2 (m + 1)
  have hlog3 := Nat.log_le_self 2 (n + 2)
  have hlog4 := Nat.log_le_self 2 (4 * m + 2)
  have hlog5 := Nat.log_le_self 2 (16 * m + 6)
  have hs1 := nat_size_le_self (2 * m)
  have hs2 := nat_size_le_self (n + 2)
  have hs3 := nat_size_le_self (m + 1)
  have hCtot_ge :
      (R + 6) * 48000 * C_ov * (Bmul + 2) ^ 4 * Z ^ 4 +
      40 * C_gw * Z ^ 5 + 300000 * Z ^ 2 +
      5000 * (Bmul * Z) + 4 * gConst + 20000 ≤ C_tot * Z ^ 6 := by
    have h1 : 300000 * Z ^ 2 + 5000 * (Bmul * Z) + 4 * gConst + 20000 ≤
        (500000 * Bmul ^ 2 + 4 * gConst + 50000) * Z ^ 6 := by
      have h16 : 1 ≤ Z ^ 6 := Nat.one_le_pow 6 Z hZ1
      nlinarith only [hZ1, hZ16, hZ26, hBmul1, hBmul2, h16]
    have h2 : (R + 6) * 48000 * C_ov * (Bmul + 2) ^ 4 * Z ^ 4 ≤
        (R + 6) * 48000 * C_ov * (Bmul + 2) ^ 4 * Z ^ 6 :=
      Nat.mul_le_mul_left _ hZ46
    have h3 : 40 * C_gw * Z ^ 5 ≤ 40 * C_gw * Z ^ 6 :=
      Nat.mul_le_mul_left _ hZ56
    have h4 : C_tot * Z ^ 6 =
        (R + 6) * 48000 * C_ov * (Bmul + 2) ^ 4 * Z ^ 6 +
        40 * C_gw * Z ^ 6 + (500000 * Bmul ^ 2 + 4 * gConst + 50000) * Z ^ 6 := by
      change ((R + 6) * 48000 * C_ov * (Bmul + 2) ^ 4 + 40 * C_gw +
        500000 * Bmul ^ 2 + 4 * gConst + 50000) * Z ^ 6 = _
      simp only [Nat.add_mul, Nat.add_assoc]
    linarith only [h1, h2, h3, h4]
  rw [ha1, ha2, ha3, ha4]
  have hZ_BmulZ : Z ≤ Bmul * Z := Nat.le_mul_of_pos_left Z hBmul1
  have hMulOv : (R + 6) * (48000 * ⌈lsstOverheadFactor guest c K n m B⌉₊) ≤
      (R + 6) * 48000 * C_ov * (Bmul + 2) ^ 4 * Z ^ 4 := by
    calc (R + 6) * (48000 * ⌈lsstOverheadFactor guest c K n m B⌉₊)
        ≤ (R + 6) * (48000 * (C_ov * (Bmul + 2) ^ 4 * Z ^ 4)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hOv_le)
      _ = (R + 6) * 48000 * C_ov * (Bmul + 2) ^ 4 * Z ^ 4 := by ring
  have ha7_le : 40 * a7 ≤ 40 * (Bmul * Z) := by
    have : a7 ≤ Bmul := by dsimp only [Bmul]; omega
    nlinarith only [this, hZ1]
  have hg_parts' : a1 + a2 + a3 + a4 + a5 + a6 + argsSize publishedRoundArgs ≤ gConst := by
    dsimp only [gConst]; omega
  refine le_trans ?_ hCtot_ge
  linarith only [hGW_le, hStaged, hMulOv, hB_le, hZ_BmulZ, ha7_le, hg_parts',
    hlog1, hlog2, hlog3, hlog4, hlog5, hs1, hs2, hs3, hn, hm, hZ_eq, hZ1]

/-- Polynomial-in-`(L + N + 2)` upper bound on `dryLastMultBound L N`. -/
theorem dryLastMultBound_le_poly :
    ∃ C q : ℕ, ∀ L N : ℕ, dryLastMultBound L N ≤ C * (L + N + 2) ^ q := by
  obtain ⟨C_rep, hRep⟩ := repPackedDispatch_le_poly lastGuest lastWordConst ⌈max 1 lastCanonConst⌉₊ lastK
  refine ⟨C_rep + 300, 6, fun L N => ?_⟩
  unfold dryLastMultBound
  refine Finset.sup_le fun nm hnm => ?_
  obtain ⟨hnLt, hmLt⟩ := Finset.mem_product.mp hnm
  have hn : nm.1 ≤ N + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hnLt)
  have hm : nm.2 ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmLt)
  set Z : ℕ := L + N + 2
  have hZ1 : 1 ≤ Z := by omega
  have hZ12 : Z ≤ Z ^ 2 := by simpa only [pow_one] using Nat.pow_le_pow_right hZ1 (by decide : 1 ≤ 2)
  have hZ26 : Z ^ 2 ≤ Z ^ 6 := Nat.pow_le_pow_right hZ1 (by decide : 2 ≤ 6)
  apply max_le
  · have hUnf : packedNonLoopDispatchMultiplier lastGuest lastWordConst ⌈max 1 lastCanonConst⌉₊
        lastK L nm.1 nm.2 ≤
        representativePackedDispatchMultiplier lastGuest lastWordConst ⌈max 1 lastCanonConst⌉₊
          lastK L nm.1 nm.2 +
          (argsSize collectionGuestFormatArgs + 40 * (Nat.log 2 (nm.1 + 2) + 1) +
            40 * ((1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (nm.2 + 1).size) +
            40 * (Nat.log 2 (4 * nm.2 + 2) + Nat.log 2 (16 * nm.2 + 6) + 2) + 169 +
            argsSize packedControllerInputArgs + 4) := by
      unfold packedNonLoopDispatchMultiplier packedFormatScalarCost
      exact le_rfl
    exact (hUnf.trans (hRep L N nm.1 nm.2 hn hm)).trans
      (Nat.mul_le_mul_right _ (Nat.le_add_right C_rep 300))
  · unfold loopOnlyMultiplier
    have hL : L ≤ Z := by omega
    have hnm1 : nm.1 ≤ Z := by omega
    have hnm2 : nm.2 ≤ Z := by omega
    have h1 : (130 * nm.1 + (17 * L + 37) * nm.2 + 275) / 2 + (29 * nm.2 + 81) / 2 ≤ 300 * Z ^ 2 := by
      have h2 : (17 * L + 37) * nm.2 ≤ 54 * Z ^ 2 := by nlinarith only [hL, hnm2, hZ1, hZ12]
      have h3 : 130 * nm.1 + (17 * L + 37) * nm.2 + 275 ≤ 460 * Z ^ 2 := by
        nlinarith only [hnm1, h2, hZ1, hZ12]
      have h4 : 29 * nm.2 + 81 ≤ 110 * Z ^ 2 := by nlinarith only [hnm2, hZ1, hZ12]
      omega
    exact h1.trans (Nat.mul_le_mul (Nat.le_add_left 300 C_rep) hZ26)

/-- **`dryLastMultBound` is `SubpolyNat`** whenever both its limb count and edge cap are `SubpolyNat`. -/
theorem dryLastMultBound_subpoly
    {fL fN : ℕ → ℕ} (hL : SubpolyNat fL) (hN : SubpolyNat fN) :
    SubpolyNat (fun M => dryLastMultBound (fL M) (fN M)) := by
  obtain ⟨C, q, hbd⟩ := dryLastMultBound_le_poly
  exact SubpolyNat.mono (fun M => hbd (fL M) (fN M))
    (SubpolyNat.const_mul (SubpolyNat.pow (SubpolyNat.add_const (SubpolyNat.add hL hN) 2) q) C)

/-- **`dryLastMultOfM` is `SubpolyNat`.** -/
theorem dryLastMultOfM_subpoly : SubpolyNat dryLastMultOfM :=
  dryLastMultBound_subpoly dryLimbsOfM_subpoly subpolyNat_two_pow_dryKOfM

/-- On every valid circulation `J`, `dryLastMult J` is bounded by a `SubpolyNat` function of
`(solverConnectedAugmented J).m`. -/
theorem dryLastMult_le_subpoly :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryLastMult J ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨C, q, hbd⟩ := dryLastMultBound_le_poly
  refine ⟨fun M => C * (dryLimbsOfM M + 2 ^ dryKOfM M + 2) ^ q,
    SubpolyNat.const_mul
      (SubpolyNat.pow (SubpolyNat.add_const (SubpolyNat.add dryLimbsOfM_subpoly subpolyNat_two_pow_dryKOfM) 2) q) C,
    fun J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hL := dryLimbs_le_ofM J hJn hJm hCap
  have hMd : levelM cfg.TP cfg.P cfg.P.d ≤ 2 ^ dryKOfM I.m :=
    le_of_lt (lt_of_le_of_lt (Nat.le_succ _) (dryWitnessUsed_lastCanonConst_and_levelM_lt J hJn hJm hCap).2)
  have h1 := hbd (ipmQualityLimbs I.m (solverPenalty J.m) k) (levelM cfg.TP cfg.P cfg.P.d)
  have h2 : ipmQualityLimbs I.m (solverPenalty J.m) k + levelM cfg.TP cfg.P cfg.P.d + 2 ≤
      dryLimbsOfM I.m + 2 ^ dryKOfM I.m + 2 :=
    Nat.add_le_add_right (Nat.add_le_add hL hMd) 2
  exact h1.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left h2 q))

end MinCostFlow.Final.DryRun

end
