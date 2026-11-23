module

public import MinCostFlow.Final.BoundedChainModel
public import MinCostFlow.IPM.Machine.SolverInitialBounds
import MinCostFlow.Chain.Theorem5_1Asymptotics
import MinCostFlow.Chain.Algorithm2PsiGame
import MinCostFlow.IPM.Machine.PrecisionPolynomialBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Quantitative certificates for the tree-chain tools

Lemma 5.17 (page 23) bounds the dynamic sparsified core parameters.
The last-level tool in Definition 5.8 (pages 19–20) has a separate
stretch and total construction charge. Theorem 5.1 (page 15) uses
these bounds at the caps in the chain configuration.
-/

public noncomputable section
namespace MinCostFlow.Final
open Chain IPM IPM.Machine Scaling

/-- The padded logarithm used in the uniform tool bounds. -/
@[expose] def chainLog (M : ℕ) : ℝ := Real.log ((M:ℝ)+2)

/-- The common shape of the logarithm of a tool bound. -/
@[expose] def chainLogPower (β : ℝ) (M : ℕ) : ℝ :=
  (chainLog M)^β * Real.log (chainLog M+2)

private theorem chainLog_ge_one {M : ℕ} (hm : 0 < M) : 1 ≤ chainLog M := by
  unfold chainLog
  have hm' : (1:ℝ) ≤ M := by exact_mod_cast hm
  simpa only [Real.log_exp] using
    Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ (M:ℝ)+2 by linarith [Real.exp_one_lt_three])

private theorem chainLogPower_ge_log {M : ℕ} (hm : 0 < M) {β : ℝ} (hβ : 0≤β) :
    Real.log (chainLog M+2) ≤ chainLogPower β M := by
  have h := chainLog_ge_one hm
  exact le_mul_of_one_le_left (Real.log_nonneg (by linarith)) (Real.one_le_rpow h hβ)

/-- The constants in the quantitative certificate are uniform in the
input size. The low-stretch tree constant enters the stretch bound. -/
structure ChainToolConstants where
  C_lsst : ℝ
  core : ℝ
  stretch : ℝ
  construction : ℝ

/-- A single constant for the size-dependent inequalities in Theorem 5.1. -/
@[expose] def ChainToolConstants.common (c : ChainToolConstants) (TP : SparseCoreParams)
    (LP : LastLevelParams) : ℝ :=
  max 1 c.C_lsst + max 0 c.core + max 0 c.stretch + max 0 c.construction +
    3 * (max TP.p_T LP.p_last + 3 : ℕ)

private theorem ChainToolConstants.common_nonneg (c : ChainToolConstants)
    (TP : SparseCoreParams) (LP : LastLevelParams) : 0 ≤ c.common TP LP := by
  unfold ChainToolConstants.common
  positivity

/-- An integer budget for the read-only quality procedure. -/
@[expose] def chainQualityBudget (c : ChainToolConstants) (TP : SparseCoreParams) (LP : LastLevelParams) : ℕ :=
  ⌈15+5*c.common TP LP⌉₊

/-- Reciprocal quality at the computed budget, in the exponent of Theorem 5.1. -/
theorem chainQualityBudget_bound (c : ChainToolConstants) (TP : SparseCoreParams)
    (LP : LastLevelParams) (M : ℕ) :
    (2:ℝ)^integerQualityExponent (chainQualityBudget c TP LP) M ≤
      alg2TimeFactor (65536*((chainQualityBudget c TP LP:ℝ)+1)) (47/48) M :=
  (integerQualityExponent_bounds _ M).2

/-- Bounds used for the core, stretch and construction terms in Theorem 5.1
(page 15). The cap is the input edge count. The reduction comparison and
the two stretch bounds refer to the arguments used by that theorem. -/
structure ChainToolBounds (c : ChainToolConstants) (TP : SparseCoreParams)
    (LP : LastLevelParams) (σ : ℕ → ℝ) : Prop where
  length : ∀ M, 0 < M → TP.γ_ℓ (M^2) ≤ Real.exp (c.core*chainLogPower (23/24) M)
  recourse : ∀ M, 0 < M → TP.γ_r (M^2) ≤ Real.exp (c.core*chainLogPower (23/24) M)
  sparseStretch : ∀ M N (hm : 0 < M), N ≤ 2*M+2 →
    TP.σ (mkChainParams (chosenD (23/24) M) M
      (chosenD_bounds (by norm_num : (23:ℝ)/24 < 1) hm).1 hm).k N ≤
      Real.exp ((max 1 c.C_lsst+c.stretch)*chainLogPower (23/24) M)
  lastStretch : ∀ M N, 0 < M → N ≤ 2*M+2 →
    LP.σ_last N ≤ Real.exp ((max 1 c.C_lsst+c.stretch)*chainLogPower (23/24) M)
  averageStretch : ∀ M N, 0 < M → N ≤ 2*M+2 →
    max 0 (σ N) ≤ Real.exp ((max 1 c.C_lsst+c.stretch)*chainLogPower (23/24) M)
  sparseConstruction : ∀ M, 0 < M → TP.c_T ≤ Real.exp (c.construction*chainLogPower (23/24) M)
  lastConstruction : ∀ M, 0 < M → LP.c_last ≤ Real.exp (c.construction*chainLogPower (23/24) M)
  reduction : ∀ M (hm : 0 < M), TP.γ_ℓ (M^2) ≤ (M:ℝ) ∧
    TP.γ_ℓ (M^2) ≤ (mkChainParams (chosenD (23/24) M) M
      (chosenD_bounds (by norm_num : (23:ℝ)/24 < 1) hm).1 hm).k

private theorem chain_exp_mono {C D β : ℝ} {M : ℕ} (hm : 0 < M) (h : C≤D) :
    Real.exp (C*chainLogPower β M) ≤ Real.exp (D*chainLogPower β M) := by
  have hL := chainLog_ge_one hm
  apply Real.exp_le_exp.mpr
  refine mul_le_mul_of_nonneg_right h ?_
  unfold chainLogPower
  exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg (by linarith))

private theorem chain_logFactor_pow (P : ChainParams) (N p : ℕ) (hN : N≤2*P.M₀+2) :
    (2*logFactor P N)^p ≤ Real.exp ((3*p:ℝ)*chainLogPower (47/48) P.M₀) := by
  let L := chainLog P.M₀
  have hL : 1 ≤ L := chainLog_ge_one P.hM₀
  have hN' : (N:ℝ)≤2*(P.M₀:ℝ)+2 := by exact_mod_cast hN
  have hBase : (P.M₀:ℝ)+N+2≤3*((P.M₀:ℝ)+2) := by linarith
  have hlog := Real.log_le_log (by positivity : 0 < (P.M₀:ℝ)+N+2) hBase
  rw [Real.log_mul (by norm_num) (by positivity)] at hlog
  have h3 : Real.log 3 ≤ L := by
    change Real.log 3 ≤ Real.log ((P.M₀:ℝ)+2)
    apply Real.log_le_log (by norm_num)
    have hM : (1:ℝ) ≤ P.M₀ := by exact_mod_cast P.hM₀
    linarith
  have hF : 2*logFactor P N ≤ 4*L := by unfold logFactor; change _ ≤ Real.log 3+L at hlog; linarith
  have hD : 4*L ≤ (L+2)^3 := by nlinarith only [hL,sq_nonneg L,mul_nonneg (show 0≤L by linarith) (sq_nonneg L)]
  have hF0 : 0≤2*logFactor P N := by
    unfold logFactor
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    linarith [Nat.cast_nonneg (α:=ℝ) P.M₀, Nat.cast_nonneg (α:=ℝ) N]
  refine (pow_le_pow_left₀ hF0 (hF.trans hD) _).trans ?_
  rw [←pow_mul, ←Real.exp_log (show 0<L+2 by linarith), ←Real.exp_nat_mul, Real.exp_le_exp]
  push_cast
  exact mul_le_mul_of_nonneg_left (chainLogPower_ge_log P.hM₀ (by norm_num)) (by positivity)

/-- The additional word width follows the exponent of Theorem 5.1. -/
theorem integerQualityExponent_le_chainLogPower (A M : ℕ) :
    (integerQualityExponent A M:ℝ) ≤ 131072*((A:ℝ)+1)*chainLogPower (47/48) M := by
  have hlog2 : (1/2:ℝ)≤Real.log 2 := Real.log_two_gt_d9.le.trans' (by norm_num)
  have h := (integerQualityExponent_bounds A M).2
  unfold alg2TimeFactor at h
  have he : (2:ℝ)^integerQualityExponent A M =
      Real.exp ((integerQualityExponent A M:ℝ)*Real.log 2) := by
    rw [←Real.log_pow, Real.exp_log (by positivity)]
  rw [he, Real.exp_le_exp] at h
  change (integerQualityExponent A M:ℝ)*Real.log 2 ≤
    65536*((A:ℝ)+1)*(chainLog M)^(47/48:ℝ)*Real.log (chainLog M+2) at h
  have hlo := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (integerQualityExponent A M))
  unfold chainLogPower
  nlinarith only [h,hlo]

/-- The rounded quality exponent adds at most a squared-log term to
the numerical range, with explicit dependence on the tool budget. -/
theorem integerQualityExponent_le_log_square (A M : ℕ) (hm : 0 < M) :
    (integerQualityExponent A M:ℝ) ≤ (262144*((A:ℝ)+1))*(chainLog M)^2 := by
  let L := chainLog M
  have hL : 1≤L := chainLog_ge_one hm
  have hp : L^(47/48:ℝ)≤L := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL
      (by norm_num : (47:ℝ)/48≤1)
  have hl : Real.log (L+2)≤2*L := by
    have hh := Real.log_le_sub_one_of_pos (show 0<L+2 by linarith)
    linarith
  have hPower : chainLogPower (47/48) M≤L*(2*L) :=
    mul_le_mul hp hl (Real.log_nonneg (by linarith)) (by linarith)
  refine (integerQualityExponent_le_chainLogPower A M).trans ?_
  calc
    _ ≤ (131072*((A:ℝ)+1))*(L*(2*L)) := mul_le_mul_of_nonneg_left hPower (by positivity)
    _ = _ := by change _ = _ * L^2; ring

private theorem chain_input_log_bound (M V : ℕ) (hm : 0<M) (hV : 0<V) (hp : V≤16*M^81) :
    Real.log ((M*V:ℕ):ℝ) ≤ 86*chainLog M := by
  have hmul : M*V ≤ 16*M^82 := calc
    _ ≤ M*(16*M^81) := Nat.mul_le_mul_left _ hp
    _ = _ := by rw [pow_succ]; ring
  have h := Real.log_le_log (by exact_mod_cast Nat.mul_pos hm hV)
    (show ((M*V:ℕ):ℝ)≤16*(M:ℝ)^82 by exact_mod_cast hmul)
  have hpos : (0:ℝ)<M := by exact_mod_cast hm
  rw [Real.log_mul (by norm_num) (pow_pos hpos _).ne',Real.log_pow] at h
  have hmL : Real.log (M:ℝ) ≤ chainLog M := Real.log_le_log hpos (by linarith)
  have h16 : (16:ℝ)≤((M:ℝ)+2)^4 := by
    have hh : (2:ℝ)≤(M:ℝ)+2 := by linarith [Nat.cast_nonneg (α:=ℝ) M]
    exact (show (16:ℝ)=2^4 by norm_num) ▸ pow_le_pow_left₀ (by norm_num) hh 4
  have hlog16 := Real.log_le_log (by norm_num : (0:ℝ)<16) h16
  rw [Real.log_pow] at hlog16
  change Real.log 16≤4*chainLog M at hlog16
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, hmL, hlog16]

/-- A constant controlling the game weight at the widened precision. -/
@[expose] def chainPsiConstant (A : ℕ) : ℝ := 500000000000+3000000*((A:ℝ)+1)+2

/-- The game weight bound follows from the polynomial IPM penalty and
the computed quality, without a further hypothesis on the tools. -/
theorem widened_chain_game_bound_at (M V A qSize cap : ℕ) (hm : 0<M) (hsize : 2≤M*V)
    (hp : V≤16*M^81) (hcap : M≤cap) (hqPos : 0<qSize) (hqCap : qSize≤cap) :
    alg2PsiGame ((ipmQualityRangeExponent M V (integerQualityExponent A qSize)+
      slackRangeExponent M V+6 : ℕ) : ℝ) cap ≤
      Real.exp (chainPsiConstant A*chainLogPower (23/24) cap) := by
  let k := integerQualityExponent A qSize
  let L := chainLog cap
  let Ψ := ((ipmQualityRangeExponent M V k+slackRangeExponent M V+6 : ℕ) : ℝ)
  have hcapPos := hm.trans_le hcap
  have hL : 1≤L := chainLog_ge_one hcapPos
  have hlogMono : chainLog M ≤ L := by
    unfold L chainLog
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hcap 2)
  have hV : 0<V := by
    by_contra h
    have he : V=0 := by omega
    simp [he] at hsize
  have hpsi := precisionHiddenPsi_le_log_square M V hsize
  have hlog := chain_input_log_bound M V hm hV hp
  have hnonneg : 0≤Real.log ((M*V:ℕ):ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1≤M*V by omega))
  have hsq := pow_le_pow_left₀ hnonneg
    (hlog.trans (mul_le_mul_of_nonneg_left hlogMono (by norm_num))) 2
  have hdiff : Ψ ≤ precisionHiddenPsi M V+4*(k:ℝ) := by
    have h : qualitySlackExponent M V k ≤ slackRangeExponent M V+k := by
      unfold qualitySlackExponent
      omega
    have hd : ipmQualityRangeExponent M V k+slackRangeExponent M V+6 ≤
        ipmRangeExponent M V+slackRangeExponent M V+6+4*k := by
      unfold ipmQualityRangeExponent ipmRangeExponent
      omega
    unfold Ψ precisionHiddenPsi
    exact_mod_cast hd
  have hk := integerQualityExponent_le_log_square A qSize hqPos
  have hqLog : chainLog qSize ≤ L := by
    unfold L chainLog
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hqCap 2)
  have hA : (0:ℝ)≤A := Nat.cast_nonneg A
  have hBound : Ψ ≤ (210000000000+1048576*((A:ℝ)+1))*L^2 := by
    change _ ≤ (86*L)^2 at hsq
    have hksq := pow_le_pow_left₀ (show 0≤chainLog qSize from
      le_trans (by norm_num) (chainLog_ge_one hqPos)) hqLog 2
    have hk' := hk.trans (mul_le_mul_of_nonneg_left hksq (by positivity))
    nlinarith only [hpsi,hsq,hdiff,hk',sq_nonneg L]
  have hlogM : Real.log ((cap:ℝ)+1) ≤ L := Real.log_le_log (by positivity) (by linarith)
  have hlog2 : (1/2:ℝ)≤Real.log 2 := Real.log_two_gt_d9.le.trans' (by norm_num)
  have hdiv : Real.log ((cap:ℝ)+1)/Real.log 2 ≤ 2*Real.log ((cap:ℝ)+1) := by
    have hlog1 := Real.log_nonneg (show (1:ℝ)≤(cap:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) cap])
    apply (div_le_iff₀ (by linarith : 0<Real.log 2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hlog2 hlog1]
  let C := chainPsiConstant A
  have hC : 2≤C := by unfold C chainPsiConstant; linarith
  have hTail : 2*(Ψ+Real.log ((cap:ℝ)+1))+4 ≤ C*L^2 := by
    have hL2 : L≤L^2 := by nlinarith only [hL,sq_nonneg (L-1)]
    have hOne : 1≤L^2 := le_trans hL hL2
    unfold C chainPsiConstant
    nlinarith only [hBound,hlogM,hL2,hOne,mul_nonneg hA (sq_nonneg L)]
  have hLog : Real.log (L+2)≤chainLogPower (23/24) cap := chainLogPower_ge_log hcapPos (by norm_num)
  have hPow : L^2 ≤ Real.exp (2*chainLogPower (23/24) cap) := by
    have h0 : 0<L+2 := by linarith
    refine (pow_le_pow_left₀ (by linarith : 0≤L) (show L≤L+2 by linarith) 2).trans ?_
    rw [←Real.exp_log h0, ←Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by norm_num; linarith)
  have hE : 1≤chainLogPower (23/24) cap := by
    have hLL : 1≤Real.log (L+2) := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
        (show Real.exp 1≤L+2 by linarith [Real.exp_one_lt_three])
    exact hLL.trans hLog
  have hCoef : C ≤ Real.exp ((C-2)*chainLogPower (23/24) cap) := by
    have hC3 : 3≤C := by unfold C chainPsiConstant; linarith
    have hLogC : Real.log C ≤ C-2 := by
      have hbase : Real.log C ≤ C/2 := by
        have hc : 0<C/2 := by linarith
        have hh := Real.log_le_sub_one_of_pos hc
        rw [Real.log_div (by linarith : C≠0) (by norm_num)] at hh
        have hlog2' := Real.log_two_lt_d9.le
        linarith
      linarith [show 4≤C by unfold C chainPsiConstant; linarith]
    calc
      C = Real.exp (Real.log C) := (Real.exp_log (show 0<C by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.mpr
        (hLogC.trans (le_mul_of_one_le_right (show 0≤C-2 by linarith) hE))
  have hMain : C*L^2≤Real.exp (C*chainLogPower (23/24) cap) := by
    refine (mul_le_mul hCoef hPow (sq_nonneg L) (Real.exp_nonneg _)).trans_eq ?_
    rw [←Real.exp_add]
    congr 1
    ring
  have hup := alg2PsiGame_le Ψ cap
  rw [max_eq_right (show (0:ℝ)≤Ψ from Nat.cast_nonneg _)] at hup
  exact (show alg2PsiGame Ψ cap ≤ C*L^2 by linarith only [hup,hdiv,hTail]).trans hMain

/-- The game weight bound when the cap is the current edge count. -/
theorem widened_chain_game_bound (M V A : ℕ) (hm : 0<M) (hsize : 2≤M*V) (hp : V≤16*M^81) :
    alg2PsiGame ((ipmQualityRangeExponent M V (integerQualityExponent A M)+
      slackRangeExponent M V+6 : ℕ) : ℝ) M ≤
      Real.exp (chainPsiConstant A*chainLogPower (23/24) M) :=
  widened_chain_game_bound_at M V A M M hm hsize hp le_rfl hm le_rfl

/-- The certified per-operation factor of Theorem 5.1, with the
compressed vertex comparison and the widened numerical game weight. -/
@[expose] def chainTimeConstant (c : ChainToolConstants) (TP : SparseCoreParams)
    (LP : LastLevelParams) : ℝ :=
  66+21*c.common TP LP+4*chainPsiConstant (chainQualityBudget c TP LP)

/-- Theorem 5.1 (page 15) gives both the widened solver model and the
collapsed time factor from the quantitative tool certificates. -/
theorem widened_chain_model_and_time (I : Instance) (V : ℕ) (hm : 0<I.m)
    (hn : I.n≤2*I.m+2) (hsize : 2≤I.m*V) (hV : V≤16*I.m^81)
    (T : SparseCoreRestartTool) (L : LastLevelTool) (TP : SparseCoreParams)
    (LP : LastLevelParams) (σ : ℕ → ℝ) (c : ChainToolConstants)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP) (hL : L.IsSpec LP)
    (hσmono : Monotone σ) (hσnn : ∀ n, 0≤σ n) (hMWU : T.ToolMWURestart σ)
    (hEmb : T.ToolEmbedsSurvivingRestart) (hNoReins : T.ToolNoReinsertRestart)
    (hBounds : ChainToolBounds c TP LP σ) :
    let A := chainQualityBudget c TP LP
    let k := integerQualityExponent A I.m
    let cfg := ipmWidenedChainConfig I V A hm T L TP LP σ
    MinRatioSpecWithFailureUpTo (algorithm2_dsWithFailure cfg) (1/(2:ℝ)^k)
      (Num.IPM.alphaPrime I.m V/8)
      ((ipmQualityRangeExponent I.m V k+slackRangeExponent I.m V+6 : ℕ) : ℝ)
      ((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m V/1024) I.m I.n ∧
      alg2CollapsedFactor cfg ≤ alg2TimeFactor (chainTimeConstant c TP LP) (47/48) I.m := by
  dsimp only
  let A := chainQualityBudget c TP LP
  let cfg := ipmWidenedChainConfig I V A hm T L TP LP σ
  let C := c.common TP LP
  let Cψ := chainPsiConstant A
  obtain ⟨hCap,hReduction⟩ := hBounds.reduction I.m hm
  have valid : cfg.Valid := {
    hTP := hTP
    hLP := hLP
    hT := hT
    hL := hL
    hσ_mwu_mono := fun _ _ h => hσmono h
    hσ_mwu_nn := hσnn I.n
    hMWU := hMWU
    hEmb := hEmb
    hNoReins := hNoReins
    hγM₀ := hCap
    hγk := hReduction
    hα := by
      change 0 < Num.IPM.alphaPrime I.m V/8
      unfold Num.IPM.alphaPrime
      positivity }
  have hC : 0≤C := c.common_nonneg TP LP
  have hCψ : 0≤Cψ := by unfold Cψ chainPsiConstant; positivity
  have hcore : c.core≤C := by
    have hc := le_max_right 0 c.core
    unfold C ChainToolConstants.common
    linarith [le_max_left (1:ℝ) c.C_lsst, le_max_left (0:ℝ) c.stretch,
      le_max_left (0:ℝ) c.construction, Nat.cast_nonneg (α:=ℝ) (max TP.p_T LP.p_last+3)]
  have hstretch : max 1 c.C_lsst+c.stretch≤C := by
    unfold C ChainToolConstants.common
    linarith [le_max_right (0:ℝ) c.stretch, le_max_left (0:ℝ) c.core,
      le_max_left (0:ℝ) c.construction, Nat.cast_nonneg (α:=ℝ) (max TP.p_T LP.p_last+3)]
  have hconstruction : c.construction≤C := by
    unfold C ChainToolConstants.common
    linarith [le_max_left (1:ℝ) c.C_lsst, le_max_left (0:ℝ) c.stretch,
      le_max_left (0:ℝ) c.core, le_max_right (0:ℝ) c.construction,
      Nat.cast_nonneg (α:=ℝ) (max TP.p_T LP.p_last+3)]
  have hpoly : 3 * (max TP.p_T LP.p_last + 3 : ℕ) ≤ C := by
    unfold C ChainToolConstants.common
    linarith [le_max_left (1:ℝ) c.C_lsst, le_max_left (0:ℝ) c.stretch,
      le_max_left (0:ℝ) c.core, le_max_left (0:ℝ) c.construction]
  have hLen := (hBounds.length I.m hm).trans (chain_exp_mono hm (β:=23/24) hcore)
  have hRec := (hBounds.recourse I.m hm).trans (chain_exp_mono hm (β:=23/24) hcore)
  have hST := (hBounds.sparseStretch I.m I.n hm hn).trans (chain_exp_mono hm (β:=23/24) hstretch)
  have hSL := (hBounds.lastStretch I.m I.n hm hn).trans (chain_exp_mono hm (β:=23/24) hstretch)
  have hSM := (hBounds.averageStretch I.m I.n hm hn).trans (chain_exp_mono hm (β:=23/24) hstretch)
  have hcT := (hBounds.sparseConstruction I.m hm).trans (chain_exp_mono hm (β:=23/24) hconstruction)
  have hcL := (hBounds.lastConstruction I.m hm).trans (chain_exp_mono hm (β:=23/24) hconstruction)
  have hPsi := widened_chain_game_bound I.m V A hm hsize hV
  have hlogF' := chain_logFactor_pow cfg.P I.n (max TP.p_T LP.p_last+3) hn
  have hlogF := hlogF'.trans (chain_exp_mono hm (β:=47/48) hpoly)
  have hlogN := chain_logVertexComparison_add_two hn
  have hA : 15+5*C ≤ (A:ℝ) := Nat.le_ceil _
  simp only [chainLogPower, chainLog, ← mul_assoc] at hLen hRec hST hSL hSM hcT hcL hPsi hlogF
  refine ⟨ipmWidenedChainConfig_spec I V A hm T L TP LP σ valid hC hCψ
    (by norm_num : (1:ℝ)≤4) hLen hRec hST hSL hSM hcT hcL hPsi hlogF hlogN hA, ?_⟩
  have h := (theorem_5_1_asymptotic_exponents (cfg:=cfg) (β:=23/24)
    (by norm_num) (by norm_num) hm rfl hTP hLP hC hCψ (by norm_num : (1:ℝ)≤4)
    hLen hRec hST hSL hSM hcT hcL hPsi
    (by
      rw [show ((1+(23:ℝ)/24)/2)=47/48 by norm_num]
      exact hlogF) hlogN).2
  change alg2CollapsedFactor cfg ≤ _
  unfold alg2TimeFactor chainTimeConstant
  rw [show cfg.P.M₀=I.m from rfl, show ((1+(23:ℝ)/24)/2)=47/48 by norm_num] at h
  convert h using 2; dsimp only [C,Cψ,A]; ring

/-- A length cap of at least three at four edges fails the reduction
premise for the two-edge cap, independently of the quality word width. -/
theorem chainToolBounds_not_of_small_reduction (c : ChainToolConstants)
    (TP : SparseCoreParams) (LP : LastLevelParams) (σ : ℕ → ℝ)
    (h : 3≤TP.γ_ℓ 4) : ¬ ChainToolBounds c TP LP σ := by
  intro hb
  have hh := (hb.reduction 2 (by decide)).1
  norm_num at hh
  linarith

/-- The polynomial stretch certificate of the last-level builder cannot
supply the subpolynomial bound when evaluated at the top-level vertex cap. -/
theorem chainToolBounds_not_of_root_last_stretch (c : ChainToolConstants)
    (TP : SparseCoreParams) (LP : LastLevelParams) (σ : ℕ → ℝ)
    (h : ∀ n : ℕ, 2*max 1 c.C_lsst*(n:ℝ)^2*(chainLog n)^2≤LP.σ_last n) :
    ¬ ChainToolBounds c TP LP σ := by
  intro hb
  let C := max 1 c.C_lsst+c.stretch
  obtain ⟨B,hB,hRate⟩ := alg2TimeFactor_le_rpow (C:=C) (a:=23/24)
    (by norm_num) (by norm_num) (δ:=1) (by norm_num)
  obtain ⟨M,hM⟩ := exists_nat_gt B
  have hm : 0<M := Nat.cast_pos.mp (lt_of_lt_of_le zero_lt_one (hB.trans hM.le))
  have hL := chainLog_ge_one hm
  have hTop : LP.σ_last M ≤ B*(M:ℝ) := by
    have hCap := hb.lastStretch M M hm (by omega)
    have hRate' := hRate M hm
    rw [Real.rpow_one] at hRate'
    exact hCap.trans (by simpa only [alg2TimeFactor,chainLogPower,chainLog,mul_assoc,C] using hRate')
  have hm0 : (0:ℝ)<M := Nat.cast_pos.mpr hm
  have hLower : (M:ℝ)^2≤LP.σ_last M := by
    apply le_trans _ (h M)
    have hC : (1:ℝ)≤max 1 c.C_lsst := le_max_left _ _
    have hSq : (1:ℝ)≤(chainLog M)^2 := one_le_pow₀ hL
    calc
      (M:ℝ)^2 = 1*(M:ℝ)^2*1 := by ring
      _ ≤ 2*max 1 c.C_lsst*(M:ℝ)^2*(chainLog M)^2 := by
        have hTwo : (1:ℝ)≤2*max 1 c.C_lsst := by linarith
        gcongr
  have hstrict : B*(M:ℝ)<(M:ℝ)^2 := by
    rw [pow_two]
    exact mul_lt_mul_of_pos_right hM hm0
  exact (not_lt_of_ge (hLower.trans hTop)) hstrict

/-- The tools from Lemma 5.17 and the final level of Definition 5.8,
with the specifications and bounds needed by Theorem 5.1. -/
structure QuantitativeChainTools where
  core : SparseCoreRestartTool
  last : LastLevelTool
  coreParams : SparseCoreParams
  lastParams : LastLevelParams
  averageStretch : ℕ → ℝ
  constants : ChainToolConstants
  coreParamsValid : coreParams.Valid
  lastParamsValid : lastParams.Valid
  coreSpec : core.IsSpecRestart coreParams
  lastSpec : last.IsSpec lastParams
  averageStretchMono : Monotone averageStretch
  averageStretchNonneg : ∀ n, 0≤averageStretch n
  mwu : core.ToolMWURestart averageStretch
  embedding : core.ToolEmbedsSurvivingRestart
  noReinsert : core.ToolNoReinsertRestart
  quantitative : ChainToolBounds constants coreParams lastParams averageStretch

/-- The quality program's constant depends only on the tool certificates. -/
@[expose] def QuantitativeChainTools.budget (T : QuantitativeChainTools) : ℕ :=
  chainQualityBudget T.constants T.coreParams T.lastParams

/-- The Section 5 configuration on the augmented input. -/
@[expose] def QuantitativeChainTools.config (T : QuantitativeChainTools) (J : Circulation)
    (hm : 0<J.m) (hp : ∀ e, 1≤J.capacity e) : Alg2Config :=
  ipmWidenedChainConfig (solverAugmented J) (solverPenalty J.m) T.budget
    (hm.trans_le (solverAugmented_size J hp).1) T.core T.last T.coreParams T.lastParams T.averageStretch

/-- Theorem 5.1 (page 15) fills the widened model field at every
compressed input, with the same threshold the machine uses. -/
theorem QuantitativeChainTools.model_spec (T : QuantitativeChainTools) (J : Circulation)
    (hn : J.n≤2*J.m+1) (hm : 0<J.m) (hp : ∀ e, 1≤J.capacity e) :
    let I := solverAugmented J
    let V := solverPenalty J.m
    let k := integerQualityExponent T.budget I.m
    MinRatioSpecWithFailureUpTo (algorithm2_dsWithFailure (T.config J hm hp)) (1/(2:ℝ)^k)
      (Num.IPM.alphaPrime I.m V/8)
      ((ipmQualityRangeExponent I.m V k+slackRangeExponent I.m V+6 : ℕ) : ℝ)
      ((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m V/1024) I.m I.n := by
  dsimp only
  let I := solverAugmented J
  let V := solverPenalty J.m
  have hM := (solverAugmented_size J hp).1
  have hN : I.n≤2*I.m+2 := by
    change J.n+1≤2*I.m+2
    change J.m≤I.m at hM
    omega
  have hV : 2≤V := by
    have hCap : 2≤solverCapacityBound J.m := le_max_left _ _
    have hPow : 0<(solverCapacityBound J.m)^2 := pow_pos (by omega) _
    have hh := Nat.le_mul_of_pos_right (4*J.m) hPow
    change 4*J.m≤V at hh
    omega
  have hSize : 2≤I.m*V := hV.trans (by
    have hh := Nat.mul_le_mul_right V (hm.trans_le hM)
    simpa only [Nat.one_mul] using hh)
  have hPenalty : V≤16*I.m^81 :=
    (solverPenalty_le J.m hm).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM _))
  exact (widened_chain_model_and_time I V (hm.trans_le hM) hN hSize hPenalty
    T.core T.last T.coreParams T.lastParams T.averageStretch T.constants
    T.coreParamsValid T.lastParamsValid T.coreSpec T.lastSpec T.averageStretchMono
    T.averageStretchNonneg T.mwu T.embedding T.noReinsert T.quantitative).1

end MinCostFlow.Final
