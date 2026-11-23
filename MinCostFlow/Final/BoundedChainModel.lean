module

public import MinCostFlow.Chain.Theorem5_1
public import MinCostFlow.Final.RuntimeQualityBounds
public import MinCostFlow.IPM.Machine.PrecisionHiddenRange
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Theorem 5.1 on bounded min-ratio histories

The guarantees of Theorem 5.1 (page 15) give Definition 4.5 (page 14)
at the configured edge and vertex limits. A dyadic quality no larger
than the theorem's quality preserves the Update ratio inequality.
-/

public section
namespace MinCostFlow.Final
open Chain IPM

/-- Theorem 5.1 (page 15) supplies the bounded min-ratio model, with the
same hidden stability and Detect parameters and a smaller quality. -/
theorem theorem_5_1_specWithFailureUpTo_of_quality {cfg : Alg2Config} (hV : cfg.Valid)
    {Cγ Cψ CN : ℝ}
    (hD : cfg.P.d = chosenD (23 / 24) cfg.P.M₀)
    (hCγ : 0 ≤ Cγ) (hCψ : 0 ≤ Cψ) (hCN : 1 ≤ CN)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last cfg.N₀ ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (Cψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ CN * Real.log ((cfg.P.M₀ : ℝ) + 2))
    {M N k : ℕ} (hM : M ≤ cfg.P.M₀) (hN : N ≤ cfg.N₀)
    (hk : alg2KappaLower (15+5*Cγ) (47/48) cfg.P.M₀ ≤
      alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ →
      1/(2:ℝ)^k ≤ alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) :
    MinRatioSpecWithFailureUpTo (algorithm2_dsWithFailure cfg) (1/(2:ℝ)^k)
      cfg.α cfg.Ψ cfg.ε M N := by
  intro D η op T hvalid hsize
  obtain ⟨hQuality, _, hq, hu, hd, _⟩ :=
    theorem_5_1 hV hD hCγ hCψ hCN hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF hlogN hvalid
      (fun t ht => (hsize.1 t ht).trans hM) (fun t ht => (hsize.2 t ht).trans hN)
  refine ⟨⟨fun t ht => (hq t ht).2, ?_, hd⟩, ?_⟩
  · intro t ht hop
    refine ⟨(hu t ht hop).1, fun hhidden => ((hu t ht hop).2.1 hhidden).2.trans ?_⟩
    rw [neg_mul]
    exact neg_le_neg (mul_le_mul_of_nonneg_right (hk hQuality.2) hV.hα.le)
  · exact fun t ht hop hs => ((hu t ht hop).2.1 hs).1


/-- Theorem 5.1 (page 15) supplies the bounded min-ratio model, with the
same hidden stability and Detect parameters and a smaller quality. -/
theorem theorem_5_1_specWithFailureUpTo {cfg : Alg2Config} (hV : cfg.Valid)
    {Cγ Cψ CN : ℝ}
    (hD : cfg.P.d = chosenD (23 / 24) cfg.P.M₀)
    (hCγ : 0 ≤ Cγ) (hCψ : 0 ≤ Cψ) (hCN : 1 ≤ CN)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last cfg.N₀ ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (Cψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ CN * Real.log ((cfg.P.M₀ : ℝ) + 2))
    {M N k : ℕ} (hM : M ≤ cfg.P.M₀) (hN : N ≤ cfg.N₀)
    (hk : 1/(2:ℝ)^k ≤ alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) :
    MinRatioSpecWithFailureUpTo (algorithm2_dsWithFailure cfg) (1/(2:ℝ)^k)
      cfg.α cfg.Ψ cfg.ε M N :=
  theorem_5_1_specWithFailureUpTo_of_quality hV hD hCγ hCψ hCN hγℓ hγr hσT hσL hσM hcT hcL
    hΨ hlogF hlogN hM hN (fun _ => hk)


/-- Section 5's chain parameters at the actual augmented graph size.
The threshold and hidden stability parameters are those of the fixed-point IPM. -/
@[expose] noncomputable def ipmChainConfig (I : Instance) (V A : ℕ) (hm : 0 < I.m)
    (T : SparseCoreRestartTool) (L : LastLevelTool) (TP : SparseCoreParams)
    (LP : LastLevelParams) (σ : ℕ → ℝ) : Alg2Config where
  T := T
  L := L
  TP := TP
  LP := LP
  P := mkChainParams (chosenD (23/24) I.m) I.m
    (chosenD_bounds (by norm_num : (23:ℝ)/24 < 1) hm).1 hm
  σ_mwu := σ
  N₀ := I.n
  α := Num.IPM.alphaPrime I.m V/8
  Ψ := IPM.Machine.precisionHiddenPsi I.m V
  ε := (1/(2:ℝ)^integerQualityExponent A I.m)*Num.IPM.alphaPrime I.m V/1024

/-- The vertex comparison of Theorem 5.1 holds with constant four
when the augmented vertex count is at most twice its edge count plus two. -/
theorem chain_logVertexComparison_add_two {M N : ℕ} (h : N ≤ 2*M+2) :
    1 + Real.log ((N:ℝ)+2) ≤ 4*Real.log ((M:ℝ)+2) := by
  have hcast : (N:ℝ) ≤ 2*(M:ℝ)+2 := by exact_mod_cast h
  have hbound : (N:ℝ)+2 ≤ 2*((M:ℝ)+2) := by linarith only [hcast]
  have hlog := Real.log_le_log (by positivity) hbound
  rw [Real.log_mul (by norm_num) (by positivity)] at hlog
  have hmono : Real.log 2 ≤ Real.log ((M:ℝ)+2) :=
    Real.log_le_log (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg M))
  have hhalf : (1/2:ℝ) ≤ Real.log 2 := Real.log_two_gt_d9.le.trans' (by norm_num)
  linarith only [hlog,hmono,hhalf]

/-- The vertex comparison of Theorem 5.1 holds with constant four
when the augmented vertex count is at most twice its edge count plus one. -/
theorem chain_logVertexComparison {M N : ℕ} (h : N ≤ 2*M+1) :
    1 + Real.log ((N:ℝ)+2) ≤ 4*Real.log ((M:ℝ)+2) :=
  chain_logVertexComparison_add_two (h.trans (by omega))

/-- The model part of the runtime interface on an instance satisfying
Theorem 5.1's parameter inequalities. The tool validity and the
logarithmic vertex comparison enter as hypotheses. -/
theorem ipmChainConfig_spec (I : Instance) (V A : ℕ) (hm : 0 < I.m)
    (T : SparseCoreRestartTool) (L : LastLevelTool) (TP : SparseCoreParams)
    (LP : LastLevelParams) (σ : ℕ → ℝ) :
    let cfg := ipmChainConfig I V A hm T L TP LP σ
    ∀ (_hV : cfg.Valid) {Cγ Cψ CN : ℝ}
    (_hCγ : 0 ≤ Cγ) (_hCψ : 0 ≤ Cψ) (_hCN : 1 ≤ CN)
    (_hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hσL : cfg.LP.σ_last cfg.N₀ ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hcT : cfg.TP.c_T ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hcL : cfg.LP.c_last ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (Cψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ CN * Real.log ((cfg.P.M₀ : ℝ) + 2))
    (_hA : 15+5*Cγ ≤ (A:ℝ)),
    MinRatioSpecWithFailureUpTo (algorithm2_dsWithFailure cfg)
      (1/(2:ℝ)^integerQualityExponent A I.m) (Num.IPM.alphaPrime I.m V/8)
      (IPM.Machine.precisionHiddenPsi I.m V)
      ((1/(2:ℝ)^integerQualityExponent A I.m)*Num.IPM.alphaPrime I.m V/1024) I.m I.n := by
  dsimp only
  intro hV Cγ Cψ CN hCγ hCψ hCN hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF hlogN hA
  apply theorem_5_1_specWithFailureUpTo_of_quality hV rfl hCγ hCψ hCN
    hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF hlogN le_rfl le_rfl
  intro hLower
  refine (integerQualityExponent_bounds A I.m).1.trans (le_trans ?_ hLower)
  unfold alg2KappaLower
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  have hlog : 0 ≤ Real.log ((I.m:ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) I.m])
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hlog _))
    (Real.log_nonneg (by change 1 ≤ Real.log ((I.m:ℝ)+2)+2; linarith only [hlog]))



/-- Theorem 5.1 gives the IPM model on compressed dimensions using the
tool bounds and a quality budget within the fixed numerical range. -/
theorem ipmChainConfig_compressed_spec (I : Instance) (V A : ℕ) (hm : 0 < I.m)
    (hn : I.n ≤ 2*I.m+2) (hVpos : 0 < V) (hAfit : A ≤ 858)
    (T : SparseCoreRestartTool) (L : LastLevelTool) (TP : SparseCoreParams)
    (LP : LastLevelParams) (σ : ℕ → ℝ) :
    let cfg := ipmChainConfig I V A hm T L TP LP σ
    ∀ (_hV : cfg.Valid) {Cγ Cψ : ℝ}
    (_hCγ : 0 ≤ Cγ) (_hCψ : 0 ≤ Cψ)
    (_hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hσL : cfg.LP.σ_last cfg.N₀ ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hcT : cfg.TP.c_T ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hcL : cfg.LP.c_last ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (Cψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hA : 15+5*Cγ ≤ (A:ℝ)),
    integerQualityExponent A I.m ≤ IPM.Machine.slackRangeExponent I.m V ∧
    MinRatioSpecWithFailureUpTo (algorithm2_dsWithFailure cfg)
      (1/(2:ℝ)^integerQualityExponent A I.m) (Num.IPM.alphaPrime I.m V/8)
      (IPM.Machine.precisionHiddenPsi I.m V)
      ((1/(2:ℝ)^integerQualityExponent A I.m)*Num.IPM.alphaPrime I.m V/1024) I.m I.n := by
  dsimp only
  intro hV Cγ Cψ hCγ hCψ hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF hA
  exact ⟨integerQualityExponent_le_slackRange A I.m V hAfit hVpos,
    ipmChainConfig_spec I V A hm T L TP LP σ hV hCγ hCψ (by norm_num : (1:ℝ) ≤ 4)
      hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF (chain_logVertexComparison_add_two hn) hA⟩

/-- Section 5's parameters for the wider format selected by the
runtime IPM. The graph bounds and threshold are unchanged. -/
@[expose] noncomputable def ipmWidenedChainConfig (I : Instance) (V A : ℕ) (hm : 0 < I.m)
    (T : SparseCoreRestartTool) (L : LastLevelTool) (TP : SparseCoreParams)
    (LP : LastLevelParams) (σ : ℕ → ℝ) : Alg2Config :=
  {ipmChainConfig I V A hm T L TP LP σ with
    Ψ := ((IPM.Machine.ipmQualityRangeExponent I.m V (integerQualityExponent A I.m)+
      IPM.Machine.slackRangeExponent I.m V+6 : ℕ) : ℝ)}

/-- The model part of the runtime interface on an instance satisfying
Theorem 5.1's parameter inequalities. The tool validity and the
logarithmic vertex comparison enter as hypotheses. -/
theorem ipmWidenedChainConfig_spec (I : Instance) (V A : ℕ) (hm : 0 < I.m)
    (T : SparseCoreRestartTool) (L : LastLevelTool) (TP : SparseCoreParams)
    (LP : LastLevelParams) (σ : ℕ → ℝ) :
    let cfg := ipmWidenedChainConfig I V A hm T L TP LP σ
    ∀ (_hV : cfg.Valid) {Cγ Cψ CN : ℝ}
    (_hCγ : 0 ≤ Cγ) (_hCψ : 0 ≤ Cψ) (_hCN : 1 ≤ CN)
    (_hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hσL : cfg.LP.σ_last cfg.N₀ ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hcT : cfg.TP.c_T ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hcL : cfg.LP.c_last ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (Cψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((23 : ℝ) / 24) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (Cγ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((47 : ℝ) / 48) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (_hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ CN * Real.log ((cfg.P.M₀ : ℝ) + 2))
    (_hA : 15+5*Cγ ≤ (A:ℝ)),
    MinRatioSpecWithFailureUpTo (algorithm2_dsWithFailure cfg)
      (1/(2:ℝ)^integerQualityExponent A I.m) (Num.IPM.alphaPrime I.m V/8)
      ((IPM.Machine.ipmQualityRangeExponent I.m V (integerQualityExponent A I.m)+
        IPM.Machine.slackRangeExponent I.m V+6 : ℕ) : ℝ)
      ((1/(2:ℝ)^integerQualityExponent A I.m)*Num.IPM.alphaPrime I.m V/1024) I.m I.n := by
  dsimp only
  intro hV Cγ Cψ CN hCγ hCψ hCN hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF hlogN hA
  apply theorem_5_1_specWithFailureUpTo_of_quality hV rfl hCγ hCψ hCN
    hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF hlogN le_rfl le_rfl
  intro hLower
  refine (integerQualityExponent_bounds A I.m).1.trans (le_trans ?_ hLower)
  unfold alg2KappaLower
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  have hlog : 0 ≤ Real.log ((I.m:ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) I.m])
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hlog _))
    (Real.log_nonneg (by change 1 ≤ Real.log ((I.m:ℝ)+2)+2; linarith only [hlog]))



end MinCostFlow.Final
