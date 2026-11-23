module

public import MinCostFlow.Chain.ConcreteInstantiation
public import MinCostFlow.HierPaths.BuildFinal
public import MinCostFlow.Final.CappedQuality
public import MinCostFlow.Final.RuntimeQualityBounds
public import MinCostFlow.IPM.Machine.SolverDataStructures
import MinCostFlow.IPM.Machine.ConnectedSolverFinish
import MinCostFlow.Chain.Algorithm2PsiGame
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Concrete chain model instantiation from Theorem 5.1

Unpacks `Chain.concrete_theorem_5_1` at `C_ψ = 1`, `C_N = 4` (with an
abstract subpolynomial degree cap `degCap` of constant `C_D`; the ordered version
in `OrderedConcreteChainModel` has no degree cap), and
derives `MinRatioSpecWithFailureConnectedUpTo` on `solverConnectedAugmented J`
using the capped dyadic quality exponent and the exact restart hypotheses
of `concrete_theorem_5_1`.
-/

@[expose] public noncomputable section
namespace MinCostFlow.Final
open Chain IPM IPM.Machine WordRAM Scaling LSF

/-- Witness bundle unpacked from `Chain.concrete_theorem_5_1` at fixed
asymptotic constants `C_ψ = 1` and `C_N = 4`, keeping `C_D` and the
restart hypotheses untouched. -/
structure ConcreteChainWitness
    (C_D : ℝ) (hCD : 0 ≤ C_D) where
  oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph
  C_lsst : ℝ
  sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut
  params : ℕ → DynSpanner.SparsifyParams
  hp_s : ∀ m, (params m).p_s ≤ 1
  hp_t : ∀ m, (params m).p_t ≤ 1
  C_γ : ℝ
  M_thresh : ℕ
  hlsst : HasLSSTSpec oracle C_lsst
  hsparsify : ∀ mMax, DynSpanner.SparsifySpec mMax (params mMax) sparsify
  hCγ : 3 ≤ C_γ
  hM_thresh : 2 ≤ M_thresh
  spec : ∀ (M₀ N₀ D_cap : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
    M_thresh ≤ M₀ →
    1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) →
    (D_cap : ℝ) ≤ Real.exp (C_D * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
    alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
    0 < α →
    let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
    let cfg := concreteAlg2Cfg oracle C_lsst sparsify params hp_s hp_t
      M₀ N₀ B_cap D_cap hM₀1 α Ψ ε
    cfg.T.IsSpecRestart cfg.TP → cfg.T.ToolMWURestart cfg.σ_mwu →
    cfg.T.ToolEmbedsSurvivingRestart → cfg.T.ToolNoReinsertRestart →
    ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
      MinRatioHistoryValid D isUpdate T → (∀ t ≤ T, (D.G t).m ≤ M₀) →
      (∀ t ≤ T, (D.G t).n ≤ N₀) →
      (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
      let A := algorithm2_dsWithFailureOwn cfg
      let κ := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
      let C_κ := 15 + 5 * C_γ
      (0 < κ ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ) ∧
      (∀ t ≤ T, ∀ e ∈ (D.G t).E,
        A.query (minRatioState A.eraseFailure D η isUpdate t) e =
          minRatioFlow A.eraseFailure D η isUpdate t e) ∧
      (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
        (D.G (t + 1)).IsCirculation
          (minRatioDirection A.eraseFailure D η isUpdate t) ∧
        (D.HiddenStable (t + 1) α Ψ →
          (minRatioFailureDirection A D η isUpdate t).isSome = true ∧
          (D.G (t + 1)).inner (D.g (t + 1))
              (minRatioDirection A.eraseFailure D η isUpdate t) /
            (D.G (t + 1)).lnorm (D.ℓ (t + 1))
              (minRatioDirection A.eraseFailure D η isUpdate t) ≤ -(κ * α))) ∧
      (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
        (A.detect (minRatioState A.eraseFailure D η isUpdate t)).1 =
          minRatioDetectSet A.eraseFailure D η isUpdate ε t)
  specWith : ∀ (M₀ N₀ D_cap : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
    M_thresh ≤ M₀ →
    1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) →
    (D_cap : ℝ) ≤ Real.exp (C_D * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
    alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
    0 < α →
    let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
    let cfg := concreteAlg2Cfg oracle C_lsst sparsify params hp_s hp_t
      M₀ N₀ B_cap D_cap hM₀1 α Ψ ε
    cfg.T.IsSpecRestart cfg.TP → cfg.T.ToolMWURestart cfg.σ_mwu →
    cfg.T.ToolEmbedsSurvivingRestart → cfg.T.ToolNoReinsertRestart →
    let κ_own := alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀
    let C_κ := 15 + 5 * C_γ
    (0 < κ_own ∧ alg2KappaLower C_κ (47 / 48) M₀ ≤ κ_own) ∧
    ∀ (κ : ℝ), 0 < κ → κ ≤ κ_own →
      ∀ {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ},
        MinRatioHistoryValid D isUpdate T → (∀ t ≤ T, (D.G t).m ≤ M₀) →
        (∀ t ≤ T, (D.G t).n ≤ N₀) →
        (∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v) →
        let A := algorithm2_dsWithFailureWith cfg κ
        (∀ t ≤ T, ∀ e ∈ (D.G t).E,
          A.query (minRatioState A.eraseFailure D η isUpdate t) e =
            minRatioFlow A.eraseFailure D η isUpdate t e) ∧
        (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
          (D.G (t + 1)).IsCirculation
            (minRatioDirection A.eraseFailure D η isUpdate t) ∧
          (D.HiddenStable (t + 1) α Ψ →
            (minRatioFailureDirection A D η isUpdate t).isSome = true ∧
            (D.G (t + 1)).inner (D.g (t + 1))
                (minRatioDirection A.eraseFailure D η isUpdate t) /
              (D.G (t + 1)).lnorm (D.ℓ (t + 1))
                (minRatioDirection A.eraseFailure D η isUpdate t) ≤ -(κ * α))) ∧
        (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
          (A.detect (minRatioState A.eraseFailure D η isUpdate t)).1 =
            minRatioDetectSet A.eraseFailure D η isUpdate ε t)

/-- The witness exists. The proof is that of `Chain.concrete_theorem_5_1_with`, with the
unconditional sparsifier `HierPaths.theorem_8_1_concrete_unconditional`, so neither the expander
decomposition nor decremental expander paths is a hypothesis. -/
theorem concreteChainWitness_nonempty
    (C_D : ℝ) (hCD : 0 ≤ C_D) :
    Nonempty (ConcreteChainWitness C_D hCD) := by
  obtain ⟨oracle, C_lsst, hlsst⟩ := LSF.theorem_2_2
  obtain ⟨sparsify, params, C_sp, K_s, K_t, hCsp, _, hKs, hKt, h81⟩ :=
    HierPaths.theorem_8_1_concrete_unconditional
  have hp_spec : ∀ m,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧
      (params m).K_t = K_t ∧ (params m).p_t = 1 ∧
      (params m).γ_ℓ ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params m).γ_c ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
    fun m => ⟨(h81 m).1, (h81 m).2.1, (h81 m).2.2.1,
      (h81 m).2.2.2.1, (h81 m).2.2.2.2.1, (h81 m).2.2.2.2.2.1⟩
  have hp_s : ∀ m, (params m).p_s ≤ 1 := fun m => le_of_eq (h81 m).2.1
  have hp_t : ∀ m, (params m).p_t ≤ 1 := fun m => le_of_eq (h81 m).2.2.2.1
  have hsparsify := fun mMax => (h81 mMax).2.2.2.2.2.2
  obtain ⟨C_γ, M_thresh, hCγ, hM_thresh, hspec⟩ :=
    concrete_theorem_5_1_with_last_core oracle C_lsst (SparseCore.lastLevelTool oracle C_lsst) C_lsst
      (SparseCore.lastLevelTool_isSpec oracle C_lsst hlsst) sparsify params
      C_sp K_s K_t hCsp hKs hKt hp_spec C_D 1 4 hCD zero_le_one (by norm_num) false
  refine ⟨{
    oracle := oracle
    C_lsst := C_lsst
    sparsify := sparsify
    params := params
    hp_s := hp_s
    hp_t := hp_t
    C_γ := C_γ
    M_thresh := M_thresh
    hlsst := hlsst
    hsparsify := hsparsify
    hCγ := hCγ
    hM_thresh := hM_thresh
    spec := fun M₀ N₀ D_cap α Ψ ε hM₀1 hM hN hD hΨ hα hr1 hr2 hr3 hr4
        {D η isUpdate T} hHist hmBound hnBound hConn => by
      have hAll := hspec M₀ N₀ D_cap α Ψ ε hM₀1 hM hN hD hΨ hα hr1 hr2 hr3 hr4
      have hKappa := hAll.1
      obtain ⟨_, _, hQuery, hUpdate, hDetect, _⟩ :=
        hAll.2 _ hKappa.1 le_rfl hHist hmBound hnBound hConn
      simpa only [algorithm2_dsWithFailureOwn] using
        ⟨hKappa, fun t ht e he => (hQuery t ht).2 e he,
          fun t ht hop => ⟨(hUpdate t ht hop).1, (hUpdate t ht hop).2.1⟩, hDetect⟩
    specWith := fun M₀ N₀ D_cap α Ψ ε hM₀1 hM hN hD hΨ hα hr1 hr2 hr3 hr4 =>
      let hAll := hspec M₀ N₀ D_cap α Ψ ε hM₀1 hM hN hD hΨ hα hr1 hr2 hr3 hr4
      ⟨hAll.1, fun κ hκ0 hκ_le {D η isUpdate T} hHist hmBound hnBound hConn => by
        obtain ⟨_, _, hQuery, hUpdate, hDetect, _⟩ :=
          hAll.2 κ hκ0 hκ_le hHist hmBound hnBound hConn
        refine ⟨fun t ht e he => (hQuery t ht).2 e he, ?_, hDetect⟩
        intro t ht hop
        exact ⟨(hUpdate t ht hop).1, (hUpdate t ht hop).2.1⟩⟩
  }⟩

/-- Extract `ConcreteChainWitness` directly from `concrete_theorem_5_1`. -/
def concreteChainWitness
    (C_D : ℝ) (hCD : 0 ≤ C_D) :
    ConcreteChainWitness C_D hCD :=
  Classical.choice (concreteChainWitness_nonempty C_D hCD)

/-- Quality budget `A ≥ 15 + 5 * C_γ` matched to `concrete_theorem_5_1`. -/
def concreteQualityBudget
    {C_D : ℝ} {hCD : 0 ≤ C_D}
    (W : ConcreteChainWitness C_D hCD) : ℕ :=
  Nat.ceil (15 + 5 * W.C_γ)

theorem concreteQualityBudget_ge
    {C_D : ℝ} {hCD : 0 ≤ C_D}
    (W : ConcreteChainWitness C_D hCD) :
    15 + 5 * W.C_γ ≤ (concreteQualityBudget W : ℝ) :=
  Nat.le_ceil _

def psiPolyConst (A : ℕ) : ℝ :=
  80000000000 + 40000 * ((A : ℝ) + 1)

def concretePsiThreshold (A : ℕ) : ℕ :=
  Nat.ceil (Real.exp ((2 * (Real.log (psiPolyConst A) + 96 / 23 + 1)) ^ (48 / 23 : ℝ)))

/-- Edge threshold combining `W.M_thresh` from `concrete_theorem_5_1` with
the explicit logarithmic threshold for `alg2PsiGame ≤ exp(1 * L^{23/24} * LL)`. -/
def concreteEdgeThreshold
    {C_D : ℝ} {hCD : 0 ≤ C_D}
    (W : ConcreteChainWitness C_D hCD) : ℕ :=
  max W.M_thresh (concretePsiThreshold (concreteQualityBudget W))

theorem concreteEdgeThreshold_ge_two
    {C_D : ℝ} {hCD : 0 ≤ C_D}
    (W : ConcreteChainWitness C_D hCD) :
    2 ≤ concreteEdgeThreshold W :=
  W.hM_thresh.trans (le_max_left _ _)

private theorem nat_size_le_two_log_add_one {n : ℕ} (hn : 0 < n) :
    (n.size : ℝ) ≤ 2 * Real.log (n : ℝ) + 1 := by
  have hk : 0 < n.size := Nat.size_pos.mpr hn
  have hp : (2 : ℝ) ^ (n.size - 1) ≤ (n : ℝ) := by exact_mod_cast Nat.lt_size.mp (by omega)
  have hl := Real.log_le_log (by positivity) hp
  rw [Real.log_pow, Nat.cast_sub (by omega : 1 ≤ n.size), Nat.cast_one] at hl
  have hHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hz : 0 ≤ (n.size : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hk)
  have hmul := (mul_le_mul_of_nonneg_left hHalf hz).trans hl
  linarith only [hmul]

private theorem poly_log_sq_le_exp_23_24 (C : ℝ) (hC : 1 ≤ C) (M₀ : ℕ)
    (hM₀ : Nat.ceil (Real.exp ((2 * (Real.log C + 96 / 23 + 1)) ^ (48 / 23 : ℝ))) ≤ M₀) :
    C * (Real.log ((M₀ : ℝ) + 2)) ^ 2 ≤
      Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) := by
  set u0 : ℝ := 2 * (Real.log C + 96 / 23 + 1)
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hu0 : 2 ≤ u0 := by dsimp [u0]; linarith
  have hu0_pos : 0 < u0 := by linarith
  have hexp_le : Real.exp (u0 ^ (48 / 23 : ℝ)) ≤ (M₀ : ℝ) + 2 := by
    have h1 : Real.exp (u0 ^ (48 / 23 : ℝ)) ≤
        (Nat.ceil (Real.exp (u0 ^ (48 / 23 : ℝ))) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (Real.exp (u0 ^ (48 / 23 : ℝ))) : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀
    linarith
  set L : ℝ := Real.log ((M₀ : ℝ) + 2)
  have hM2_pos : 0 < (M₀ : ℝ) + 2 := by positivity
  have hL_ge_u0pow : u0 ^ (48 / 23 : ℝ) ≤ L := by
    simpa [L, Real.log_exp] using Real.log_le_log (Real.exp_pos _) hexp_le
  have h1_le_u0pow : 1 ≤ u0 ^ (48 / 23 : ℝ) := Real.one_le_rpow (by linarith) (by positivity)
  have hL1 : 1 ≤ L := h1_le_u0pow.trans hL_ge_u0pow
  have hL_pos : 0 < L := by linarith
  have hu0_le_rpow : u0 ≤ L ^ (23 / 48 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hL_ge_u0pow (by norm_num : (0 : ℝ) ≤ 23 / 48)
    rw [← Real.rpow_mul hu0_pos.le] at h
    simpa [show (48 / 23 : ℝ) * (23 / 48 : ℝ) = 1 by norm_num] using h
  have hLrpow1 : 1 ≤ L ^ (23 / 48 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hLrpow_pos : 0 < L ^ (23 / 48 : ℝ) := by linarith
  have hlog_sub : Real.log (L ^ (23 / 48 : ℝ)) ≤ L ^ (23 / 48 : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hLrpow_pos]
  rw [Real.log_rpow hL_pos] at hlog_sub
  have h2logL : 2 * Real.log L ≤ (96 / 23 : ℝ) * L ^ (23 / 48 : ℝ) := by
    linarith [mul_le_mul_of_nonneg_left hlog_sub (by norm_num : (0 : ℝ) ≤ 96 / 23)]
  have h96_le : (96 / 23 : ℝ) ≤ (1 / 2 : ℝ) * L ^ (23 / 48 : ℝ) := by
    dsimp [u0] at hu0_le_rpow
    linarith
  have hlogC_le : Real.log C ≤ (1 / 2 : ℝ) * L ^ (23 / 48 : ℝ) := by
    dsimp [u0] at hu0_le_rpow
    linarith
  have hrpow_sq : L ^ (23 / 48 : ℝ) * L ^ (23 / 48 : ℝ) = L ^ (23 / 24 : ℝ) := by
    rw [← Real.rpow_add hL_pos]
    norm_num
  have h23_le : L ^ (23 / 48 : ℝ) ≤ L ^ (23 / 24 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hpart1 : Real.log C ≤ (1 / 2 : ℝ) * L ^ (23 / 24 : ℝ) :=
    hlogC_le.trans (mul_le_mul_of_nonneg_left h23_le (by norm_num))
  have hpart2 : 2 * Real.log L ≤ (1 / 2 : ℝ) * L ^ (23 / 24 : ℝ) := by
    calc 2 * Real.log L ≤ (96 / 23 : ℝ) * L ^ (23 / 48 : ℝ) := h2logL
      _ ≤ ((1 / 2 : ℝ) * L ^ (23 / 48 : ℝ)) * L ^ (23 / 48 : ℝ) :=
          mul_le_mul_of_nonneg_right h96_le hLrpow_pos.le
      _ = (1 / 2 : ℝ) * L ^ (23 / 24 : ℝ) := by rw [mul_assoc, hrpow_sq]
  have hLL1 : 1 ≤ Real.log (L + 2) := by
    have h3 : Real.exp 1 ≤ L + 2 := by linarith [Real.exp_one_lt_three]
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3
  have h23_nn : 0 ≤ L ^ (23 / 24 : ℝ) := Real.rpow_nonneg hL_pos.le _
  have hsum : Real.log (C * L ^ 2) ≤
      1 * L ^ (23 / 24 : ℝ) * Real.log (L + 2) := by
    rw [Real.log_mul (by linarith) (pow_ne_zero 2 hL_pos.ne'), Real.log_pow]
    push_cast
    calc Real.log C + 2 * Real.log L ≤ L ^ (23 / 24 : ℝ) := by linarith
      _ = 1 * L ^ (23 / 24 : ℝ) * 1 := by ring
      _ ≤ 1 * L ^ (23 / 24 : ℝ) * Real.log (L + 2) :=
          mul_le_mul_of_nonneg_left hLL1 (by linarith)
  have hpos : 0 < C * L ^ 2 := by positivity
  simpa [Real.exp_log hpos] using Real.exp_le_exp.mpr hsum

theorem alg2PsiGame_le_exp_of_dims (M V A M₀ : ℕ)
    (hM₀1 : 1 ≤ M₀) (hM_le : M ≤ M₀) (hV_le : V ≤ 16 * M₀ ^ 81)
    (hThresh : concretePsiThreshold A ≤ M₀) :
    let k := integerQualityExponent A M₀
    let Ψ := ((ipmQualityRangeExponent M V k + slackRangeExponent M V + 6 : ℕ) : ℝ)
    alg2PsiGame Ψ M₀ ≤
      Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) := by
  intro k Ψ
  set L : ℝ := Real.log ((M₀ : ℝ) + 2)
  have hL1 : 1 ≤ L := by
    have h3 : Real.exp 1 ≤ (M₀ : ℝ) + 2 := by
      have : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀1
      linarith [Real.exp_one_lt_three]
    simpa [L, Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3
  have hL_nn : 0 ≤ L := by linarith
  have hL_sq : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hL_le_sq : L ≤ L ^ 2 := by nlinarith
  have hlog2_le : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hM₀size : (M₀.size : ℝ) ≤ 3 * L := by
    have hs := nat_size_le_two_log_add_one hM₀1
    have hlogM : Real.log (M₀ : ℝ) ≤ L :=
      Real.log_le_log (by exact_mod_cast hM₀1) (by linarith)
    linarith
  have hMsize : (M.size : ℝ) ≤ 3 * L :=
    (show (M.size : ℝ) ≤ (M₀.size : ℝ) by exact_mod_cast Nat.size_le_size hM_le).trans hM₀size
  have hVsize : (V.size : ℝ) ≤ 171 * L := by
    by_cases hV0 : V = 0
    · simp only [hV0, Nat.size_zero, Nat.cast_zero]; positivity
    · have hVp := Nat.pos_of_ne_zero hV0
      have hs := nat_size_le_two_log_add_one hVp
      have hcast : (V : ℝ) ≤ 16 * (M₀ : ℝ) ^ 81 := by exact_mod_cast hV_le
      have hM₀ne : (M₀ : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM₀1
      have hlogV : Real.log (V : ℝ) ≤ 85 * L := by
        have h1 : Real.log (V : ℝ) ≤ Real.log ((16 : ℝ) * (M₀ : ℝ) ^ 81) :=
          Real.log_le_log (by exact_mod_cast hVp) hcast
        rw [Real.log_mul (by norm_num) (pow_ne_zero 81 hM₀ne), Real.log_pow] at h1
        have h16 : Real.log (16 : ℝ) ≤ 4 := by
          rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow]
          push_cast
          linarith only [hlog2_le]
        have hlogM : Real.log (M₀ : ℝ) ≤ L :=
          Real.log_le_log (by exact_mod_cast hM₀1) (by linarith)
        push_cast at h1
        linarith
      linarith
  have hk_le : (k : ℝ) ≤ 4096 * ((A : ℝ) + 1) * L ^ 2 := by
    let Lc := M₀.size + 1
    let b := Lc.size
    let q := (47 * b + 47) / 48
    have hLc_pos : 0 < Lc := by unfold Lc; omega
    have hb_pos : 0 < b := Nat.size_pos.mpr hLc_pos
    have hq_le : q ≤ b := by unfold q; omega
    have hLc_le : (Lc : ℝ) ≤ 4 * L := by
      unfold Lc
      push_cast
      linarith
    have hb_le : (b : ℝ) ≤ 4 * L :=
      (show (b : ℝ) ≤ (Lc : ℝ) by exact_mod_cast Num.IPM.size_le_value Lc).trans hLc_le
    have h2b_le : (2 : ℝ) ^ b ≤ 2 * (Lc : ℝ) := by
      have hp : 2 ^ (b - 1) ≤ Lc := Nat.lt_size.mp (by omega)
      have he : b = (b - 1) + 1 := by omega
      have hNat : 2 ^ b ≤ 2 * Lc := by
        conv_lhs => rw [he, pow_succ, Nat.mul_comm]
        exact Nat.mul_le_mul_left 2 hp
      exact_mod_cast hNat
    have h2q_le : (2 : ℝ) ^ q ≤ 8 * L :=
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hq_le).trans (h2b_le.trans (by linarith))
    have hK_eq : (k : ℝ) = 128 * ((A : ℝ) + 1) * (b : ℝ) * (2 : ℝ) ^ q := by
      simp only [k, integerQualityExponent, Lc, b, q, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat, Nat.cast_pow]
    rw [hK_eq]
    have hmul1 : 128 * ((A : ℝ) + 1) * (b : ℝ) ≤ 128 * ((A : ℝ) + 1) * (4 * L) := by gcongr
    have h2q_nn : 0 ≤ (2 : ℝ) ^ q := by positivity
    calc 128 * ((A : ℝ) + 1) * (b : ℝ) * (2 : ℝ) ^ q
        ≤ 128 * ((A : ℝ) + 1) * (4 * L) * (8 * L) := mul_le_mul hmul1 h2q_le h2q_nn (by positivity)
      _ = 4096 * ((A : ℝ) + 1) * L ^ 2 := by ring
  set SR : ℝ := (slackRangeExponent M V : ℝ)
  set GC : ℝ := (gradientCoefficientExponent M V : ℝ)
  have hslack_le : SR ≤ 6660720000 * L ^ 2 := by
    have hs : (M.size : ℝ) + (V.size : ℝ) ≤ 174 * L := by linarith
    have hsq : ((M.size : ℝ) + (V.size : ℝ)) ^ 2 ≤ (174 * L) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hs 2
    have hcast : SR = 220000 * ((M.size : ℝ) + (V.size : ℝ)) ^ 2 := by
      simp only [SR, slackRangeExponent, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
    rw [hcast]
    nlinarith only [hsq]
  have hgrad_le : GC ≤ 179 * L ^ 2 := by
    have hcast : GC = (M.size : ℝ) + (V.size : ℝ) + 5 := by
      simp only [GC, gradientCoefficientExponent, Nat.cast_add, Nat.cast_ofNat]
    rw [hcast]
    linarith only [hMsize, hVsize, hL_sq, hL_le_sq]
  set QS : ℝ := (qualitySlackExponent M V k : ℝ)
  have hqslack_le : QS ≤ (6660720000 + 4096 * ((A : ℝ) + 1)) * L ^ 2 := by
    have hcast : QS = max SR (k : ℝ) := by
      simp only [QS, SR, qualitySlackExponent, Nat.cast_max]
    rw [hcast]
    refine max_le ?_ ?_
    · have hA0 : 0 ≤ ((A : ℝ) + 1) * L ^ 2 := by positivity
      linarith
    · exact hk_le.trans (by linarith [hL_sq])
  set QR : ℝ := (ipmQualityRangeExponent M V k : ℝ)
  have hrange_le : QR ≤ (26642880458 + 16384 * ((A : ℝ) + 1)) * L ^ 2 := by
    have hcast : QR = 4 * QS + 2 * GC + 100 := by
      simp only [QR, QS, GC, ipmQualityRangeExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [hcast]
    linarith only [hqslack_le, hgrad_le, hL_sq]
  have hPsi_le : Ψ ≤ (33303600464 + 16384 * ((A : ℝ) + 1)) * L ^ 2 := by
    have hcast : Ψ = QR + SR + 6 := by
      simp only [Ψ, QR, SR, Nat.cast_add, Nat.cast_ofNat]
    rw [hcast]
    linarith only [hrange_le, hslack_le, hL_sq]
  have hgame_le : alg2PsiGame Ψ M₀ ≤ psiPolyConst A * L ^ 2 := by
    have hlog_M1 : Real.log ((M₀ : ℝ) + 1) ≤ L :=
      Real.log_le_log (by positivity) (by linarith)
    have hPsi_nn : 0 ≤ Ψ := Nat.cast_nonneg _
    have hlog_nn : 0 ≤ Real.log ((M₀ : ℝ) + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M₀])
    have hdiv : Real.log ((M₀ : ℝ) + 1) / Real.log 2 ≤ 2 * Real.log ((M₀ : ℝ) + 1) := by
      rw [div_le_iff₀ (by linarith only [hlog2_ge] : 0 < Real.log 2)]
      nlinarith only [hlog2_ge, hlog_nn]
    have hup := alg2PsiGame_le Ψ M₀
    rw [max_eq_right hPsi_nn] at hup
    unfold psiPolyConst
    have hAL : 0 ≤ ((A : ℝ) + 1) * L ^ 2 := by positivity
    linarith only [hup, hdiv, hPsi_le, hlog_M1, hL_sq, hL_le_sq, hAL]
  have hC1 : 1 ≤ psiPolyConst A := by
    unfold psiPolyConst
    linarith [Nat.cast_nonneg (α := ℝ) A]
  exact hgame_le.trans (poly_log_sq_le_exp_23_24 (psiPolyConst A) hC1 M₀ hThresh)

theorem concrete_N0_log_le {M₀ : ℕ} (hM₀ : 1 ≤ M₀) :
    1 + Real.log (((4 * M₀ : ℕ) : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) := by
  have hM1 : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀
  have h3 : Real.exp 1 ≤ (M₀ : ℝ) + 2 := by linarith [Real.exp_one_lt_three]
  have hL1 : 1 ≤ Real.log ((M₀ : ℝ) + 2) := by
    simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3
  have hle : ((4 * M₀ : ℕ) : ℝ) + 2 ≤ 4 * ((M₀ : ℝ) + 2) := by
    push_cast
    linarith
  have hlog : Real.log (((4 * M₀ : ℕ) : ℝ) + 2) ≤ Real.log 4 + Real.log ((M₀ : ℝ) + 2) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) hle
  have h4 : Real.log (4 : ℝ) ≤ 2 := by
    have h2 := Real.log_two_lt_d9.le.trans (by norm_num : (0.6931471808 : ℝ) ≤ 1)
    have h4eq : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    rw [h4eq, Real.log_pow]
    push_cast
    linarith
  linarith

theorem concrete_kappa_le_alg2KappaOwn_of (A : ℕ) {C_γ : ℝ}
    (hA : 15 + 5 * C_γ ≤ (A : ℝ)) (M₀ : ℕ) {κ : ℝ}
    (hκ : alg2KappaLower (15 + 5 * C_γ) (47 / 48) M₀ ≤ κ) :
    1 / (2 : ℝ) ^ integerQualityExponent A M₀ ≤ κ := by
  refine (integerQualityExponent_bounds A M₀).1.trans (le_trans ?_ hκ)
  unfold alg2KappaLower
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · exact hA
    · exact Real.rpow_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M₀])) _
  · exact Real.log_nonneg (by
      have hlog : 0 ≤ Real.log ((M₀ : ℝ) + 2) :=
        Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M₀])
      linarith)

private theorem concrete_kappa_le_alg2KappaOwn
    {C_D : ℝ} {hCD : 0 ≤ C_D}
    (W : ConcreteChainWitness C_D hCD)
    (M₀ : ℕ) {κ : ℝ}
    (hκ : alg2KappaLower (15 + 5 * W.C_γ) (47 / 48) M₀ ≤ κ) :
    1 / (2 : ℝ) ^ integerQualityExponent (concreteQualityBudget W) M₀ ≤ κ :=
  concrete_kappa_le_alg2KappaOwn_of (concreteQualityBudget W) (concreteQualityBudget_ge W) M₀ hκ

/-- Connected `concreteAlg2Cfg` built for a circulation `J` under `concreteChainWitness`. -/
def concreteCirculationCfg
    {C_D : ℝ} {hCD : 0 ≤ C_D}
    (W : ConcreteChainWitness C_D hCD)
    (degCap : ℕ → ℕ) (J : Circulation) :
    Alg2Config :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThreshold W
  let A := concreteQualityBudget W
  let M₀ := max I.m threshold
  let N₀ := 4 * M₀
  let hM₀1 : 1 ≤ M₀ := (by omega : 1 ≤ 2).trans ((concreteEdgeThreshold_ge_two W).trans (le_max_right _ _))
  let k := cappedQualityExponent threshold A I.m
  let α := Num.IPM.alphaPrime I.m V / 8
  let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  let ε := (1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024
  let B_cap := concreteBCap W.C_lsst Ψ M₀ N₀ hM₀1
  concreteAlg2Cfg W.oracle W.C_lsst W.sparsify W.params W.hp_s W.hp_t
    M₀ N₀ B_cap (degCap M₀) hM₀1 α Ψ ε

theorem concreteCirculation_bounds_of
    {M_thresh threshold A : ℕ}
    (hMth : M_thresh ≤ threshold) (hPsiTh : concretePsiThreshold A ≤ threshold)
    (hTh2 : 2 ≤ threshold)
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hm : 0 < J.m) (hp : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let M₀ := max I.m threshold
    let N₀ := 4 * M₀
    let k := cappedQualityExponent threshold A I.m
    let α := Num.IPM.alphaPrime I.m V / 8
    let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    M_thresh ≤ M₀ ∧
    1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) ∧
    alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) ∧
    0 < α ∧ I.n ≤ N₀ := by
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let M₀ := max I.m threshold
  let N₀ := 4 * M₀
  let hM₀1 : 1 ≤ M₀ := (by omega : 1 ≤ 2).trans (hTh2.trans (le_max_right _ _))
  let k := cappedQualityExponent threshold A I.m
  let α := Num.IPM.alphaPrime I.m V / 8
  let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  have hThresh : M_thresh ≤ M₀ := hMth.trans (le_max_right I.m threshold)
  have hN₀ : 1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) := concrete_N0_log_le hM₀1
  have hJm_le : J.m ≤ I.m :=
    connectedInitial_circulation_m_ge J hp (solverPenalty J.m : ℤ)
  have hV_le : V ≤ 16 * M₀ ^ 81 := by
    calc V ≤ 16 * J.m ^ 81 := solverPenalty_le J.m hm
      _ ≤ 16 * I.m ^ 81 := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hJm_le 81)
      _ ≤ 16 * M₀ ^ 81 := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (le_max_left _ _) 81)
  have hPsi : alg2PsiGame Ψ M₀ ≤
      Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) := by
    rw [show Ψ = ((ipmQualityRangeExponent I.m V (integerQualityExponent A M₀) +
        slackRangeExponent I.m V + 6 : ℕ) : ℝ) from rfl]
    exact alg2PsiGame_le_exp_of_dims I.m V A M₀ hM₀1 (le_max_left _ _) hV_le
      (hPsiTh.trans (le_max_right I.m threshold))
  have hα : 0 < α := by unfold α Num.IPM.alphaPrime; positivity
  have hIn_le : I.n ≤ N₀ := by
    have hIn_eq : I.n = J.n + 1 := rfl
    have hIm_le : I.m ≤ M₀ := le_max_left _ _
    omega
  exact ⟨hThresh, hN₀, hPsi, hα, hIn_le⟩

private theorem concreteCirculation_bounds
    {C_D : ℝ} {hCD : 0 ≤ C_D}
    (W : ConcreteChainWitness C_D hCD)
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hm : 0 < J.m) (hp : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let threshold := concreteEdgeThreshold W
    let A := concreteQualityBudget W
    let M₀ := max I.m threshold
    let N₀ := 4 * M₀
    let k := cappedQualityExponent threshold A I.m
    let α := Num.IPM.alphaPrime I.m V / 8
    let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    W.M_thresh ≤ M₀ ∧
    1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) ∧
    alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
      Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) ∧
    0 < α ∧ I.n ≤ N₀ :=
  concreteCirculation_bounds_of (le_max_left _ _) (le_max_right _ _) (concreteEdgeThreshold_ge_two W)
    J hJn hm hp

/-- Under the four restart hypotheses (`hr1` to `hr4`) of `concrete_theorem_5_1_with`, the dyadic
Algorithm 2 structure `algorithm2_dsWithFailureWith (concreteCirculationCfg W degCap J) (1 / 2 ^ k)`
satisfies `MinRatioSpecWithFailureConnectedUpTo` at the capped dyadic quality `1 / 2 ^ k`. -/
theorem concrete_minRatioSpecWithFailureConnectedUpTo_with
    {C_D : ℝ} {hCD : 0 ≤ C_D}
    (W : ConcreteChainWitness C_D hCD)
    (degCap : ℕ → ℕ)
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hm : 0 < J.m) (hp : ∀ e, 1 ≤ J.capacity e)
    (hD_cap : (degCap (max (solverConnectedAugmented J).m (concreteEdgeThreshold W)) : ℝ) ≤
      Real.exp (C_D * Real.log (((max (solverConnectedAugmented J).m (concreteEdgeThreshold W) : ℕ) : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log (((max (solverConnectedAugmented J).m (concreteEdgeThreshold W) : ℕ) : ℝ) + 2) + 2)))
    (hr1 : (concreteCirculationCfg W degCap J).T.IsSpecRestart
      (concreteCirculationCfg W degCap J).TP)
    (hr2 : (concreteCirculationCfg W degCap J).T.ToolMWURestart
      (concreteCirculationCfg W degCap J).σ_mwu)
    (hr3 : (concreteCirculationCfg W degCap J).T.ToolEmbedsSurvivingRestart)
    (hr4 : (concreteCirculationCfg W degCap J).T.ToolNoReinsertRestart) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let threshold := concreteEdgeThreshold W
    let A := concreteQualityBudget W
    let k := cappedQualityExponent threshold A I.m
    MinRatioSpecWithFailureConnectedUpTo
      (algorithm2_dsWithFailureWith (concreteCirculationCfg W degCap J) (1 / (2 : ℝ) ^ k))
      (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
      ((1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024) I.m I.n := by
  dsimp only
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThreshold W
  let A := concreteQualityBudget W
  let M₀ := max I.m threshold
  let N₀ := 4 * M₀
  let hM₀1 : 1 ≤ M₀ := (by omega : 1 ≤ 2).trans ((concreteEdgeThreshold_ge_two W).trans (le_max_right _ _))
  let k := cappedQualityExponent threshold A I.m
  let α := Num.IPM.alphaPrime I.m V / 8
  let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  let ε := (1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024
  obtain ⟨hThresh, hN₀, hPsi, hα, hIn_le⟩ := concreteCirculation_bounds W J hJn hm hp
  obtain ⟨⟨_, hKappa⟩, hWith⟩ :=
    W.specWith M₀ N₀ (degCap M₀) α Ψ ε hM₀1 hThresh hN₀ hD_cap hPsi hα hr1 hr2 hr3 hr4
  have hk_pos : (0 : ℝ) < 1 / (2 : ℝ) ^ k := by positivity
  have hk_le_κ : 1 / (2 : ℝ) ^ k ≤
      alg2KappaOwn (concreteCirculationCfg W degCap J).TP (concreteCirculationCfg W degCap J).LP
        (concreteCirculationCfg W degCap J).P (concreteCirculationCfg W degCap J).σ_mwu
        (concreteCirculationCfg W degCap J).N₀ :=
    concrete_kappa_le_alg2KappaOwn W M₀ hKappa
  intro D η op T hValid hBounded hConn
  have hmM₀ : ∀ t ≤ T, (D.G t).m ≤ M₀ := fun t ht => (hBounded.1 t ht).trans (le_max_left _ _)
  have hnN₀ : ∀ t ≤ T, (D.G t).n ≤ N₀ := fun t ht => (hBounded.2 t ht).trans hIn_le
  obtain ⟨hQuery, hUpdate, hDetect⟩ :=
    hWith (1 / (2 : ℝ) ^ k) hk_pos hk_le_κ hValid hmM₀ hnN₀ hConn
  refine ⟨⟨hQuery, fun t ht hop => ⟨(hUpdate t ht hop).1, fun hHid => ?_⟩, hDetect⟩,
    fun t ht hop hHid => ((hUpdate t ht hop).2 hHid).1⟩
  rw [neg_mul]
  exact ((hUpdate t ht hop).2 hHid).2

/-- Under the four restart hypotheses (`hr1` to `hr4`) of `concrete_theorem_5_1`, the
concrete Algorithm 2 structure satisfies `MinRatioSpecWithFailureConnectedUpTo`
at the capped dyadic quality exponent `cappedQualityExponent`. -/
theorem concrete_minRatioSpecWithFailureConnectedUpTo
    {C_D : ℝ} {hCD : 0 ≤ C_D}
    (W : ConcreteChainWitness C_D hCD)
    (degCap : ℕ → ℕ)
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hm : 0 < J.m) (hp : ∀ e, 1 ≤ J.capacity e)
    (hD_cap : (degCap (max (solverConnectedAugmented J).m (concreteEdgeThreshold W)) : ℝ) ≤
      Real.exp (C_D * Real.log (((max (solverConnectedAugmented J).m (concreteEdgeThreshold W) : ℕ) : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log (((max (solverConnectedAugmented J).m (concreteEdgeThreshold W) : ℕ) : ℝ) + 2) + 2)))
    (hr1 : (concreteCirculationCfg W degCap J).T.IsSpecRestart
      (concreteCirculationCfg W degCap J).TP)
    (hr2 : (concreteCirculationCfg W degCap J).T.ToolMWURestart
      (concreteCirculationCfg W degCap J).σ_mwu)
    (hr3 : (concreteCirculationCfg W degCap J).T.ToolEmbedsSurvivingRestart)
    (hr4 : (concreteCirculationCfg W degCap J).T.ToolNoReinsertRestart) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let threshold := concreteEdgeThreshold W
    let A := concreteQualityBudget W
    let k := cappedQualityExponent threshold A I.m
    MinRatioSpecWithFailureConnectedUpTo
      (algorithm2_dsWithFailureOwn (concreteCirculationCfg W degCap J))
      (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
      ((1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024) I.m I.n := by
  dsimp only
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThreshold W
  let A := concreteQualityBudget W
  let M₀ := max I.m threshold
  let N₀ := 4 * M₀
  let hM₀1 : 1 ≤ M₀ := (by omega : 1 ≤ 2).trans ((concreteEdgeThreshold_ge_two W).trans (le_max_right _ _))
  let k := cappedQualityExponent threshold A I.m
  let α := Num.IPM.alphaPrime I.m V / 8
  let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  let ε := (1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024
  obtain ⟨hThresh, hN₀, hPsi, hα, hIn_le⟩ := concreteCirculation_bounds W J hJn hm hp
  intro D η op T hValid hBounded hConn
  have hmM₀ : ∀ t ≤ T, (D.G t).m ≤ M₀ := fun t ht => (hBounded.1 t ht).trans (le_max_left _ _)
  have hnN₀ : ∀ t ≤ T, (D.G t).n ≤ N₀ := fun t ht => (hBounded.2 t ht).trans hIn_le
  obtain ⟨⟨_, hKappa⟩, hQuery, hUpdate, hDetect⟩ :=
    W.spec M₀ N₀ (degCap M₀) α Ψ ε hM₀1 hThresh hN₀ hD_cap hPsi hα hr1 hr2 hr3 hr4
      hValid hmM₀ hnN₀ hConn
  have hk_le_κ := concrete_kappa_le_alg2KappaOwn W M₀ hKappa
  refine ⟨⟨hQuery, fun t ht hop => ⟨(hUpdate t ht hop).1, fun hHid => ?_⟩, hDetect⟩, ?_⟩
  · have hRatio := ((hUpdate t ht hop).2 hHid).2
    have hmul := neg_le_neg (mul_le_mul_of_nonneg_right hk_le_κ hα.le)
    rw [neg_mul]
    exact hRatio.trans hmul
  · intro t ht hop hHid
    exact ((hUpdate t ht hop).2 hHid).1

end MinCostFlow.Final
