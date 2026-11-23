module

public import MinCostFlow.Chain.Ordered.ConcreteDefs
public import MinCostFlow.Chain.Ordered.SpecOn
public import MinCostFlow.Chain.Ordered.BudgetHelpers
public import MinCostFlow.Chain.Ordered.LevelInvariants
public import MinCostFlow.Chain.Ordered.MachSpecOn
public import MinCostFlow.Chain.Ordered.ConcreteLSFInit
public import MinCostFlow.Chain.RestartSpecOn
public import MinCostFlow.Chain.BundleRestartInv
public import MinCostFlow.Chain.BundleRestartFull
public import MinCostFlow.Chain.LevelInvariants
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Restricted `IsSpecOrdRestartOn` Specification and Degree-Free Field Bridges

Ports `Chain/RestartSpecOn.lean` and a bucket-cap bridge to
the ordered bundle chain (`MinCostFlow.Chain.Ordered`). The
core tool is `sparseCoreBundleRestartToolMachWith lsfInit` with `bundleCoreParamsMach`, for an LSF
initializer that fits `C_lsst` (`IsConcreteLSFInit`, `Chain/Ordered/ConcreteLSFInit.lean`).
1. `concreteChainToolPred_hB_bound`: discharges the bucket-count clause
   `BundleCoreHypsAtWith.hB_bound` on `(initBundleTreeWith ...).activeBuckets` from
   `IsConcreteLSFInit` and `concreteChainToolPred` (via `initBundleTreeWith_bucket_bound`).
2. `chainInv_satisfies_concreteChainToolPred_noThresh` and
   `chainInv_satisfies_concreteChainToolPred`: every level `i < P.d` under the ordered `ChainInv`
   and level-`0` length bounds satisfies `concreteChainToolPred`.
3. `hB_bound_of_concreteBCap_le` and `chainInv_hB_bound_of_concreteBCap_le`: bucket-cap
   monotonicity for any `cap ≥ concreteBCap` (covering both `concreteBCap` and
   `concreteBucketCap`).
4. `concreteRestartSpecOn_withLast_of_cap`, `concreteRestartSpecOn_forest`, and
   `concreteRestartSpecOn_programs`: degree-free field bridges discharging
   `cfg.T.IsSpecOrdRestartOn cfg.TP (concreteChainToolPred ...)` from
   `sparseCoreBundleRestartToolMachWith_isSpecOrdRestartOn` (`Chain/Ordered/MachSpecOn.lean`) with
   **no** `D_cap` and **no** `hDeg_bound`.
5. `concreteRestartEmbeds`, `concreteRestartNoReinsert`, `concreteMachMWU_le`,
   `concreteRestartMWU_of_pred` and `concreteRestartMWULe`: discharge the side predicates
   (`ToolEmbedsSurvivingOrdRestart`, `ToolNoReinsertOrdRestart`, and the MWU bound
   `concreteSigmaMWUMach`) from `Chain/BundleRestartMachSpec.lean` and
   `Chain/Ordered/MachSpecOn.lean`.
6. `concreteChainToolSupply_withLast_of_cap`: the concrete tool meets the chain's supply
   hypothesis `ChainToolSupply` with `Λ = max 0 Ψ`, through
   `concreteChainToolPred_of_levelLenRange`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.Expander MinCostFlow.Bundle

section OconcBucketBounds

/-- `concreteChainToolPred` discharges `BundleCoreHypsAt.hB_bound` at
`concreteBCap C_lsst Ψ M₀ N₀ hM₀1` directly via `initBundleTree_bucket_bound`. -/
lemma concreteChainToolPred_hB_bound
    (lsfInit : LSFInit) {C_lsst : ℝ}
    (hInit : IsConcreteLSFInit lsfInit C_lsst) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (M₀ N₀ : ℕ) (hM₀1 : 1 ≤ M₀) (Ψ : ℝ)
    {k τ M N : ℕ} {D : DynamicInstance}
    (hG₀ : (D.G 0).IsValid) (hN : (D.G 0).n ≤ N)
    (hPred : concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ k τ M N D) :
    ∀ j < k, ∀ C ∈ components (D.G 0),
      ((initBundleTreeWith lsfInit L sparsify k M 0 (D.G 0) (D.ℓ 0) (fun _ => []) j).activeBuckets
        C).card ≤ concreteBCap C_lsst Ψ M₀ N₀ hM₀1 := by
  rcases hPred with ⟨hk_eq, _, hN_le, hℓ_bd⟩
  let P := concreteChainParams M₀ hM₀1
  let σ_cap := max (2 : ℝ) (max 1 (mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6))
  have hσ_ge2 : (2 : ℝ) ≤ σ_cap := le_max_left _ _
  have hlogσ_nn : 0 ≤ Real.log σ_cap := Real.log_nonneg (by linarith)
  have hΨ_nn : 0 ≤ max 0 Ψ := le_max_left _ _
  have hB_nn : 0 ≤ max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap := by positivity
  have hG₀n_le : (D.G 0).n ≤ N₀ := le_trans hN hN_le
  have hσ_mwu : mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 6 ≤ σ_cap := by
    rw [hk_eq]
    have hn_r : ((D.G 0).n : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hG₀n_le
    have hlog_le : Real.log (((D.G 0).n : ℝ) + 2) ≤ Real.log ((N₀ : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog_nn : 0 ≤ Real.log (((D.G 0).n : ℝ) + 2) := by
      linarith [half_lt_log_add_two (D.G 0).n]
    have hK_nn : 0 ≤ mwuK0 C_lsst := (mwuK0_pos C_lsst).le
    have h1 : mwuK0 C_lsst * (P.k : ℝ) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 6 ≤
        mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6 := by gcongr
    exact le_trans h1 (le_trans (le_max_right _ _) (le_max_right _ _))
  intro j hj C hC
  have hk1 : 1 ≤ k := hk_eq ▸ P.hk
  have hbd := initBundleTreeWith_bucket_bound lsfInit L sparsify (M := M) (N := 0) hk1
    (hInit.validFor hj) hG₀ hΨ_nn hB_nn hσ_ge2 hσ_mwu hℓ_bd (fun _ => []) C hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd_cast : ((P.d - 1 : ℕ) : ℝ) + 1 = (P.d : ℝ) := by
    have hd1 : 1 ≤ P.d := P.hd
    rw [Nat.cast_sub hd1, Nat.cast_one]
    ring
  have hnum_eq :
      (max 0 Ψ + (max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap) + Real.log σ_cap) / Real.log 2 =
      (2 * max 0 Ψ + (P.d : ℝ) * Real.log σ_cap) / Real.log 2 := by
    congr 1
    calc
      max 0 Ψ + (max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap) + Real.log σ_cap
          = 2 * max 0 Ψ + (((P.d - 1 : ℕ) : ℝ) + 1) * Real.log σ_cap := by ring
      _ = 2 * max 0 Ψ + (P.d : ℝ) * Real.log σ_cap := by rw [hd_cast]
  unfold concreteBCap
  simpa only [P, σ_cap, hnum_eq] using hbd

/-- Any bucket cap `cap ≥ concreteBCap C_lsst Ψ M₀ N₀ hM₀1` (covering both `concreteBCap` and
`concreteBucketCap`) discharges `BundleCoreHypsAt.hB_bound` for `concreteEnv` on every valid
graph `G` with `G.n ≤ N₀`, `1 ≤ k ≤ (concreteChainParams M₀ hM₀1).k`, and edge lengths within
`[exp (-max 0 Ψ), exp (max 0 Ψ + (d - 1) * log σ_cap)]`. -/
theorem hB_bound_of_concreteBCap_le
    (lsfInit : LSFInit) {C_lsst : ℝ}
    (hInit : IsConcreteLSFInit lsfInit C_lsst) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (M₀ N₀ cap : ℕ) (hM₀1 : 1 ≤ M₀) (Ψ : ℝ)
    (hCap : concreteBCap C_lsst Ψ M₀ N₀ hM₀1 ≤ cap)
    {k M N : ℕ} (hk1 : 1 ≤ k) (hk_le : k ≤ (concreteChainParams M₀ hM₀1).k)
    {G : MGraph} (hG : G.IsValid) (hGn : G.n ≤ N₀) {ℓ : ℕ → ℝ}
    (hℓ :
      let P := concreteChainParams M₀ hM₀1
      let σ_cap := max (2 : ℝ) (max 1 (mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6))
      ∀ e ∈ G.E, Real.exp (-max 0 Ψ) ≤ ℓ e ∧
        ℓ e ≤ Real.exp (max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap)) :
    ∀ (ord : ℕ → List End), ∀ j < k, ∀ C ∈ components G,
      ((initBundleTreeWith lsfInit L sparsify k M N G ℓ ord j).activeBuckets C).card ≤
        max 1 cap := by
  intro ord j hj C hC
  set P := concreteChainParams M₀ hM₀1
  set σ_cap := max (2 : ℝ) (max 1 (mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6))
  have hσ_ge2 : (2 : ℝ) ≤ σ_cap := le_max_left _ _
  have hlogσ_nn : 0 ≤ Real.log σ_cap := Real.log_nonneg (by linarith)
  have hA_nn : 0 ≤ max 0 Ψ := le_max_left 0 Ψ
  have hB_nn : 0 ≤ max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap := by positivity
  have hσ_mwu : mwuK0 C_lsst * (k : ℝ) * (Real.log ((G.n : ℝ) + 2)) ^ 6 ≤ σ_cap := by
    have hkR : (k : ℝ) ≤ (P.k : ℝ) := by exact_mod_cast hk_le
    have hnR : (G.n : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hGn
    have hlog_le : Real.log ((G.n : ℝ) + 2) ≤ Real.log ((N₀ : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog_nn : 0 ≤ Real.log ((G.n : ℝ) + 2) := by linarith [half_lt_log_add_two G.n]
    have hK_nn : 0 ≤ mwuK0 C_lsst := (mwuK0_pos C_lsst).le
    have h1 : mwuK0 C_lsst * (k : ℝ) * (Real.log ((G.n : ℝ) + 2)) ^ 6 ≤
        mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6 := by gcongr
    exact le_trans h1 (le_trans (le_max_right _ _) (le_max_right _ _))
  have hbd := initBundleTreeWith_bucket_bound lsfInit L sparsify (M := M) (N := N) hk1
    (hInit.validFor hj) hG hA_nn hB_nn hσ_ge2 hσ_mwu hℓ ord C hC
  have hd1 : 1 ≤ P.d := P.hd
  have hdm1 : ((P.d - 1 : ℕ) : ℝ) + 1 = (P.d : ℝ) := by exact_mod_cast Nat.sub_add_cancel hd1
  have hnum_eq :
      (max 0 Ψ + (max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap) + Real.log σ_cap) / Real.log 2 =
        (2 * max 0 Ψ + (P.d : ℝ) * Real.log σ_cap) / Real.log 2 := by
    rw [← hdm1]; ring
  rw [hnum_eq] at hbd
  have hEq : Nat.ceil ((2 * max 0 Ψ + (P.d : ℝ) * Real.log σ_cap) / Real.log 2) + 2 =
      concreteBCap C_lsst Ψ M₀ N₀ hM₀1 := rfl
  rw [hEq] at hbd
  exact le_trans hbd (le_trans hCap (le_max_right 1 cap))

end OconcBucketBounds

section OconcChainPredicate

/-- Local helper deriving level-by-level length bounds under the ordered `ChainInv` directly from
`level_bounds_aux_noHidden` (`Chain/Ordered/BudgetHelpers.lean`). -/
private lemma oconc_chainInv_length_bounds
    {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    {Ψ_ℓ : ℝ} (hℓ_bounds : ∀ e ∈ (st.G 0).E, Real.exp (-Ψ_ℓ) ≤ st.ℓ e ∧ st.ℓ e ≤ Real.exp Ψ_ℓ) :
    let σ_cap := max (2 : ℝ) (TP.σ P.k N₀)
    ∀ i ≤ P.d, ∀ e ∈ (st.G i).E,
      Real.exp (-Ψ_ℓ) ≤ st.toTreeChain.chainLen st.ℓ i e ∧
      st.toTreeChain.chainLen st.ℓ i e ≤ Real.exp Ψ_ℓ * σ_cap ^ i := by
  intro σ_cap i hi e he
  have hLvl := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInv
  have hσ_le_cap : TP.σ P.k (st.G 0).n ≤ σ_cap := by
    have hn : (st.G 0).n ≤ N₀ := hInv.hG0n
    exact le_trans (hTP.2.1 _ _ _ _ le_rfl hn) (le_max_right _ _)
  have hσ_cap_pos : 0 ≤ σ_cap := by positivity
  induction i generalizing e with
  | zero =>
    simpa [TreeChain.chainLen] using hℓ_bounds e he
  | succ i ih =>
    have hi_lt : i < P.d := hi
    have hBi := (hLvl i (Nat.le_of_lt hi_lt)).2.2.2.2 hi_lt (st.bran i) (hInv.hBran i hi_lt)
    rw [hInv.hGSucc i hi_lt] at he
    have heCore : e ∈ (coreGraph (st.G i) (T.lsfs (st.scState i) (st.bran i))).E :=
      hBi.2.1.2.1 he
    have heGi : e ∈ (st.G i).E := (Finset.mem_sdiff.mp heCore).1
    have hPrev := ih (Nat.le_of_lt hi_lt) e heGi
    have hℓ_pos : ∀ f ∈ (st.G i).E, 0 ≤ st.toTreeChain.chainLen st.ℓ i f := fun f hf =>
      (hLvl i (Nat.le_of_lt hi_lt)).2.2.2.1 f hf |>.le
    have hstr1 : 1 ≤ (T.lsfs (st.scState i) (st.bran i)).wstr e :=
      le_trans (one_le_stretch hBi.1.2.1.2.2.2.2 hℓ_pos heGi) (hBi.1.2.2.2 e heGi).1
    have hw_le : (T.lsfs (st.scState i) (st.bran i)).wstr e ≤ σ_cap :=
      le_trans (hBi.1.2.2.2 e heGi).2 hσ_le_cap
    have hcl_eq : st.toTreeChain.chainLen st.ℓ (i + 1) e =
        (T.lsfs (st.scState i) (st.bran i)).wstr e * st.toTreeChain.chainLen st.ℓ i e := by
      simp [TreeChain.chainLen, coreLen, TreeChain.activeLSF, ChainState.toTreeChain, hi_lt]
    rw [hcl_eq]
    refine ⟨?_, ?_⟩
    · have h0 : 0 ≤ st.toTreeChain.chainLen st.ℓ i e := le_trans (Real.exp_pos _).le hPrev.1
      calc Real.exp (-Ψ_ℓ) = 1 * Real.exp (-Ψ_ℓ) := by ring
        _ ≤ 1 * st.toTreeChain.chainLen st.ℓ i e := mul_le_mul_of_nonneg_left hPrev.1 zero_le_one
        _ ≤ (T.lsfs (st.scState i) (st.bran i)).wstr e * st.toTreeChain.chainLen st.ℓ i e :=
            mul_le_mul_of_nonneg_right hstr1 h0
    · have h0 : 0 ≤ st.toTreeChain.chainLen st.ℓ i e := le_trans (Real.exp_pos _).le hPrev.1
      calc (T.lsfs (st.scState i) (st.bran i)).wstr e * st.toTreeChain.chainLen st.ℓ i e
          ≤ σ_cap * (Real.exp Ψ_ℓ * σ_cap ^ i) := mul_le_mul hw_le hPrev.2 h0 hσ_cap_pos
        _ = Real.exp Ψ_ℓ * σ_cap ^ (i + 1) := by rw [pow_succ]; ring

/-- Under the ordered `ChainInv` and level-`0` length bounds
`exp (-max 0 Ψ) ≤ st.ℓ e ≤ exp (max 0 Ψ)`, every level `i < P.d` satisfies the clauses of
`concreteChainToolPred` (`k = P.k`, `levelM ≤ M₀ ^ 2`, `N₀ ≤ N₀`, and the initial-length range
bound discharging `hB_bound`). -/
theorem chainInv_satisfies_concreteChainToolPred_noThresh
    {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams}
    {C_lsst : ℝ} {M₀ N₀ : ℕ} {hM₀1 : 1 ≤ M₀} {Ψ : ℝ}
    (hTP : TP.Valid)
    (hσ_eq : ∀ k n, TP.σ k n = max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log ((n : ℝ) + 2)) ^ 6))
    (hγM₀ : TP.γ_ℓ (M₀ ^ 2) ≤ M₀)
    (hγk : TP.γ_ℓ (M₀ ^ 2) ≤ (concreteChainParams M₀ hM₀1).k)
    {st : ChainState T (concreteChainParams M₀ hM₀1)}
    (hInv : ChainInv T L TP LP (concreteChainParams M₀ hM₀1) N₀ st)
    (hℓ0 : ∀ e ∈ (st.G 0).E, Real.exp (-max 0 Ψ) ≤ st.ℓ e ∧ st.ℓ e ≤ Real.exp (max 0 Ψ)) :
    let P := concreteChainParams M₀ hM₀1
    let σ_cap := max (2 : ℝ) (max 1 (mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6))
    ∀ i < P.d,
      P.k = P.k ∧
      levelM TP P i ≤ M₀ ^ 2 ∧
      N₀ ≤ N₀ ∧
      (∀ e ∈ (st.G i).E,
        Real.exp (-max 0 Ψ) ≤ st.toTreeChain.chainLen st.ℓ i e ∧
        st.toTreeChain.chainLen st.ℓ i e ≤
          Real.exp (max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap)) := by
  intro P σ_cap i hi
  have hM₀_eq : P.M₀ = M₀ := rfl
  have hγM₀' : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀ := by simpa only [hM₀_eq] using hγM₀
  have hγk' : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k := by simpa only [hM₀_eq] using hγk
  refine ⟨rfl, by simpa only [hM₀_eq] using levelM_le_sq hTP hγM₀' hγk' i, le_rfl, ?_⟩
  have hlen := oconc_chainInv_length_bounds hTP hγM₀' hγk' hInv hℓ0
    i (Nat.le_of_lt hi)
  have hσ_eq' : max (2 : ℝ) (TP.σ P.k N₀) = σ_cap := by simp only [σ_cap, hσ_eq]
  have hσ_ge2 : (2 : ℝ) ≤ σ_cap := le_max_left _ _
  have hσ_pos : 0 < σ_cap := by linarith
  have hlogσ_nn : 0 ≤ Real.log σ_cap := Real.log_nonneg (by linarith)
  have hi_le_nat : i ≤ P.d - 1 := Nat.le_sub_one_of_lt hi
  have hi_le : (i : ℝ) ≤ ((P.d - 1 : ℕ) : ℝ) := by exact_mod_cast hi_le_nat
  intro e he
  have hle := hlen e he
  rw [hσ_eq'] at hle
  refine ⟨hle.1, ?_⟩
  calc
    st.toTreeChain.chainLen st.ℓ i e ≤ Real.exp (max 0 Ψ) * σ_cap ^ i := hle.2
    _ = Real.exp (max 0 Ψ) * Real.exp ((i : ℝ) * Real.log σ_cap) := by
      conv_lhs => rw [← Real.exp_log hσ_pos, ← Real.exp_nat_mul]
    _ = Real.exp (max 0 Ψ + (i : ℝ) * Real.log σ_cap) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap) :=
      Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonneg_right hi_le hlogσ_nn))

/-- Under the ordered `ChainInv` and level-`0` length bounds
`exp (-max 0 Ψ) ≤ st.ℓ e ≤ exp (max 0 Ψ)`, every level `i < P.d` satisfies the **entire**
`concreteChainToolPred` for any dynamic instance `D` initialized at
`(st.G i, st.toTreeChain.chainLen st.ℓ i)`. -/
theorem chainInv_satisfies_concreteChainToolPred
    {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams}
    {C_lsst : ℝ} {M₀ N₀ : ℕ} {hM₀1 : 1 ≤ M₀} {Ψ : ℝ}
    (hTP : TP.Valid)
    (hσ_eq : ∀ k n, TP.σ k n = max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log ((n : ℝ) + 2)) ^ 6))
    (hγM₀ : TP.γ_ℓ (M₀ ^ 2) ≤ M₀)
    (hγk : TP.γ_ℓ (M₀ ^ 2) ≤ (concreteChainParams M₀ hM₀1).k)
    {st : ChainState T (concreteChainParams M₀ hM₀1)}
    (hInv : ChainInv T L TP LP (concreteChainParams M₀ hM₀1) N₀ st)
    (hℓ0 : ∀ e ∈ (st.G 0).E, Real.exp (-max 0 Ψ) ≤ st.ℓ e ∧ st.ℓ e ≤ Real.exp (max 0 Ψ)) :
    let P := concreteChainParams M₀ hM₀1
    ∀ i < P.d, ∀ (τ : ℕ) (D : DynamicInstance),
      D.G 0 = st.G i → D.ℓ 0 = st.toTreeChain.chainLen st.ℓ i →
      concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ P.k τ (levelM TP P i) N₀ D := by
  intro P i hi τ D hG0 hℓi
  have h := chainInv_satisfies_concreteChainToolPred_noThresh
    hTP hσ_eq hγM₀ hγk hInv hℓ0 i hi
  refine ⟨h.1, h.2.1, h.2.2.1, fun e he => ?_⟩
  rw [hG0] at he
  rw [hℓi]
  exact h.2.2.2 e he

/-- Under the ordered `ChainInv` for `concreteAlg2Cfg` with any bucket cap
`cap ≥ concreteBCap C_lsst Ψ M₀ N₀ hM₀1`, every level `i < P.d`, branch `j < P.k`, and component
`C ∈ components (st.G i)` satisfies `BundleCoreHypsAt.hB_bound` with cap `max 1 cap`. -/
theorem chainInv_hB_bound_of_concreteBCap_le
    (lsfInit : LSFInit) (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ}
    (hInit : IsConcreteLSFInit lsfInit C_lsst)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (M₀ N₀ cap : ℕ) (hM₀1 : 1 ≤ M₀) (α Ψ ε : ℝ)
    (hCap : concreteBCap C_lsst Ψ M₀ N₀ hM₀1 ≤ cap) :
    let cfg := concreteAlg2Cfg lsfInit oracle C_lsst sparsify params hp_s hp_t
      M₀ N₀ cap hM₀1 α Ψ ε
    cfg.TP.γ_ℓ (M₀ ^ 2) ≤ M₀ →
    cfg.TP.γ_ℓ (M₀ ^ 2) ≤ cfg.P.k →
    ∀ {st : ChainState cfg.T cfg.P},
      ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P N₀ st →
      (∀ e ∈ (st.G 0).E, Real.exp (-max 0 Ψ) ≤ st.ℓ e ∧ st.ℓ e ≤ Real.exp (max 0 Ψ)) →
      ∀ i < cfg.P.d, ∀ (M N : ℕ) (ord : ℕ → List End), ∀ j < cfg.P.k,
        ∀ C ∈ components (st.G i),
          ((initBundleTreeWith lsfInit (chosenL (M₀ ^ 2)) (fun _ => sparsify) cfg.P.k M N
            (st.G i) (st.toTreeChain.chainLen st.ℓ i) ord j).activeBuckets C).card ≤
            max 1 cap := by
  intro cfg hγM₀ hγk st hInv hℓ0 i hi M N ord j hj C hC
  have hM₀_eq : cfg.P.M₀ = M₀ := rfl
  have hγM₀' : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.M₀ := by simpa only [hM₀_eq] using hγM₀
  have hγk' : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k := by simpa only [hM₀_eq] using hγk
  have hTP : cfg.TP.Valid :=
    bundleCoreParamsMach_valid (concreteEnv C_lsst params hp_s hp_t M₀ cap)
  have hLvl := level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P N₀ hTP hγM₀' hγk' hInv
  have hGi_val := (hLvl i (Nat.le_of_lt hi)).1
  have hGin : (st.G i).n ≤ N₀ := le_trans (Finset.card_le_card (hLvl i (Nat.le_of_lt hi)).2.1) hInv.hG0n
  have hσ_eq : ∀ k n, cfg.TP.σ k n = max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log ((n : ℝ) + 2)) ^ 6) :=
    fun _ _ => rfl
  have hPred := chainInv_satisfies_concreteChainToolPred_noThresh
    hTP hσ_eq hγM₀ hγk hInv hℓ0 i hi
  exact hB_bound_of_concreteBCap_le lsfInit hInit (chosenL (M₀ ^ 2)) (fun _ => sparsify)
    M₀ N₀ cap hM₀1 Ψ hCap cfg.P.hk le_rfl hGi_val hGin hPred.2.2.2 ord j hj C hC

end OconcChainPredicate

section OconcFieldBridge

/-- Degree-free generic field bridge for `concreteAlg2CfgWithLast` with any bucket cap
`cap ≥ concreteBCap`, discharging the initializer validity, `hSp`, and `hB_bound` of
`BundleCoreHypsAtWith` completely (no `D_cap` and no `hDeg_bound`). -/
theorem concreteRestartSpecOn_withLast_of_cap
    (lsfInit : LSFInit) (C_lsst : ℝ)
    (hInit : IsConcreteLSFInit lsfInit C_lsst)
    (lastTool : LastLevelTool) (lastConstant : ℝ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (hSp : ∀ mMax, SparsifySpec mMax (params mMax) sparsify)
    (cap : ∀ (M₀ : ℕ), ℕ → ℝ → 1 ≤ M₀ → ℕ)
    (hCap : ∀ (M₀ N₀ : ℕ) (Ψ : ℝ) (hM₀1 : 1 ≤ M₀),
      concreteBCap C_lsst Ψ M₀ N₀ hM₀1 ≤ cap M₀ N₀ Ψ hM₀1)
    (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀)
    (spanConst : ℕ := 1) (hConst : 1 ≤ spanConst := by omega) :
    let B_cap := cap M₀ N₀ Ψ hM₀1
    let cfg := concreteAlg2CfgWithLast lsfInit C_lsst lastTool lastConstant sparsify
      params hp_s hp_t M₀ N₀ B_cap hM₀1 α Ψ ε spanConst
    cfg.T.IsSpecOrdRestartOn cfg.TP (concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ) := by
  intro B_cap cfg
  let E := concreteEnv C_lsst params hp_s hp_t M₀ B_cap
  change (sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L (fun _ => sparsify) params
      spanConst).IsSpecOrdRestartOn
    (bundleCoreParamsMachWith E spanConst) (concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ)
  refine sparseCoreBundleRestartToolMachWith_isSpecOrdRestartOn E lsfInit (fun _ => sparsify)
    params spanConst hConst (concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ)
    (fun _ _ _ _ _ hPred => le_monoSparsifyParamsEnvelope params hPred.2.1) ?_
  intro k τ M N D _ _ hG₀ _ _ _ _ _ hN _ hPred
  have hM_sq : M ≤ M₀ ^ 2 := hPred.2.1
  have hB := concreteChainToolPred_hB_bound lsfInit hInit E.L (fun _ => sparsify)
    M₀ N₀ hM₀1 Ψ hG₀ hN hPred
  exact
    { hInit := fun _ hj => hInit.validFor hj
      hSp := sparsifySpec_mono_mMax hM_sq
        (monoSparsifyParamsEnvelope_sparsifySpec params sparsify hSp (M₀ ^ 2))
      hB_bound := fun j hj C hC =>
        le_trans (hB j hj C hC) (le_trans (hCap M₀ N₀ Ψ hM₀1) (le_max_right 1 B_cap)) }

/-- Degree-free specialization for `DyadicWithVConcretePrograms.restartSpec` using
`B_cap := concreteBucketCapacity true`, discharging `IsSpecOrdRestartOn` completely with no
`degCap`, `degConstant`, or `hDeg_bound`. -/
theorem concreteRestartSpecOn_forest
    (lsfInit : LSFInit) (C_lsst : ℝ)
    (hInit : IsConcreteLSFInit lsfInit C_lsst)
    (lastTool : LastLevelTool) (lastConstant : ℝ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (hSp : ∀ mMax, SparsifySpec mMax (params mMax) sparsify)
    (M_thresh : ℝ) :
    ∀ (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
      M_thresh ≤ M₀ →
      1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) →
      alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
      0 < α →
      let B_cap := concreteBucketCapacity true C_lsst Ψ M₀ N₀ hM₀1
      let cfg := concreteAlg2CfgWithLast lsfInit C_lsst lastTool lastConstant sparsify
        params hp_s hp_t M₀ N₀ B_cap hM₀1 α Ψ ε
      cfg.T.IsSpecOrdRestartOn cfg.TP (concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ) := by
  intro M₀ N₀ α Ψ ε hM₀1 _ _ _ _
  exact concreteRestartSpecOn_withLast_of_cap
    lsfInit C_lsst hInit lastTool lastConstant sparsify params hp_s hp_t hSp
    (fun m n ψ hm => concreteBucketCapacity true C_lsst ψ m n hm)
    (fun m n ψ hm => concreteBCap_le_bucketCap_ceil C_lsst ψ m n hm)
    M₀ N₀ α Ψ ε hM₀1

/-- Degree-free specialization for `ConcreteDataStructurePrograms.restartSpec` using
`B_cap := concreteBCap` and `concreteAlg2Cfg`, discharging `IsSpecOrdRestartOn` completely with no
`D_cap`, `degConstant`, or `hDeg_bound`. -/
theorem concreteRestartSpecOn_programs
    (lsfInit : LSFInit) (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hInit : IsConcreteLSFInit lsfInit C_lsst)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (hSp : ∀ mMax, SparsifySpec mMax (params mMax) sparsify)
    (M_thresh : ℝ) :
    ∀ (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
      M_thresh ≤ M₀ →
      1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) →
      alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
      0 < α →
      let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
      let cfg := concreteAlg2Cfg lsfInit oracle C_lsst sparsify params hp_s hp_t
        M₀ N₀ B_cap hM₀1 α Ψ ε
      cfg.T.IsSpecOrdRestartOn cfg.TP (concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ) := by
  intro M₀ N₀ α Ψ ε hM₀1 _ _ _ _
  exact concreteRestartSpecOn_withLast_of_cap
    lsfInit C_lsst hInit (lastLevelTool oracle C_lsst) C_lsst sparsify params hp_s hp_t hSp
    (fun m n ψ hm => concreteBCap C_lsst ψ m n hm)
    (fun _ _ _ _ => le_rfl)
    M₀ N₀ α Ψ ε hM₀1

/-- Unconditional `ToolEmbedsSurvivingOrdRestart` for `concreteAlg2CfgWithLast`. -/
theorem concreteRestartEmbeds
    (lsfInit : LSFInit) (C_lsst : ℝ)
    (lastTool : LastLevelTool) (lastConstant : ℝ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (M₀ N₀ B_cap : ℕ) (hM₀1 : 1 ≤ M₀) (α Ψ ε : ℝ) (spanConst : ℕ := 1) :
    (concreteAlg2CfgWithLast lsfInit C_lsst lastTool lastConstant sparsify params hp_s hp_t
      M₀ N₀ B_cap hM₀1 α Ψ ε spanConst).T.ToolEmbedsSurvivingOrdRestart :=
  sparseCoreBundleRestartToolMachWith_embedsSurvivingOrdRestart lsfInit C_lsst (chosenL (M₀ ^ 2))
    (fun _ => sparsify) params spanConst

/-- Unconditional `ToolNoReinsertOrdRestart` for `concreteAlg2CfgWithLast` from `hInit` and
`hSp`. -/
theorem concreteRestartNoReinsert
    (lsfInit : LSFInit) (C_lsst : ℝ)
    (hInit : IsConcreteLSFInit lsfInit C_lsst)
    (lastTool : LastLevelTool) (lastConstant : ℝ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (hSp : ∀ mMax, SparsifySpec mMax (params mMax) sparsify)
    (M₀ N₀ B_cap : ℕ) (hM₀1 : 1 ≤ M₀) (α Ψ ε : ℝ) (spanConst : ℕ := 1) :
    (concreteAlg2CfgWithLast lsfInit C_lsst lastTool lastConstant sparsify params hp_s hp_t
      M₀ N₀ B_cap hM₀1 α Ψ ε spanConst).T.ToolNoReinsertOrdRestart :=
  sparseCoreBundleRestartToolMachWith_toolNoReinsertOrdRestart lsfInit C_lsst (chosenL (M₀ ^ 2))
    (one_le_chosenL (M₀ ^ 2)) params (fun _ => sparsify) params spanConst
    (fun _ _ _ hj => hInit.validFor hj) hSp

/-- The MWU average-stretch bound of the machine-cost tool on a fitting initializer is at most
`concreteSigmaMWUMach C_lsst M₀`. The tool's bound is `μ · 3 K_ρ K₀ · log⁷`
(`sparseCoreBundleRestartToolMachWith_toolMWUOrdRestart`, with the constants of
`IsApproxMWUInit`), and `3 K_ρ K₀ ≤ 30 · mwuK0 C_lsst` by `IsConcreteLSFInit`. The exponent
`μ = ⌈log(M₀^2 + 2) / log 3⌉ + 1` works since `m ≤ M₀^2` (`concrete_m_poly_of_le_sq`). -/
theorem concreteMachMWU_le
    (lsfInit : LSFInit) (C_lsst : ℝ) (hInit : IsConcreteLSFInit lsfInit C_lsst)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (M₀ : ℕ)
    {k M N τ : ℕ} {D : DynamicInstance} (hG₀ : (D.G 0).IsValid) (hM_sq : (D.G 0).m ≤ M₀ ^ 2)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hD : D.IsValid τ) (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) :
    let T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst (chosenL (M₀ ^ 2))
      (fun _ => sparsify) params spanConst
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts t) j).wstr e) /
          (k : ℝ) ≤ concreteSigmaMWUMach C_lsst M₀ (D.G t).n := by
  intro T t ht e he
  obtain ⟨C₀, α, K_σ, K_ρ, hA, hKρ, hK⟩ := hInit.mwu
  have hpoly := concrete_m_poly_of_le_sq hG₀ hM_sq
  have hbd := sparseCoreBundleRestartToolMachWith_toolMWUOrdRestart lsfInit C₀ α K_σ K_ρ
    (chosenL (M₀ ^ 2)) (Nat.ceil (Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) / Real.log 3) + 1)
    (fun _ => sparsify) params spanConst hKρ hA (M := M) (N := N) ord restarts hk hG₀ hD hℓ hpoly
    t ht e he
  refine le_trans hbd ?_
  dsimp only [concreteSigmaMWUMach]
  have hlog : 0 ≤ Real.log (((D.G t).n : ℝ) + 2) := by linarith [half_lt_log_add_two (D.G t).n]
  gcongr

/-- MWU average-stretch bound for `concreteAlg2CfgWithLast` on every valid dynamic instance
satisfying `concreteChainToolPred` (so `(D.G 0).m ≤ M ≤ M₀ ^ 2`). -/
theorem concreteRestartMWU_of_pred
    (lsfInit : LSFInit) (C_lsst : ℝ)
    (hInit : IsConcreteLSFInit lsfInit C_lsst)
    (lastTool : LastLevelTool) (lastConstant : ℝ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (M₀ N₀ B_cap : ℕ) (hM₀1 : 1 ≤ M₀) (α Ψ ε : ℝ) (spanConst : ℕ := 1) :
    let cfg := concreteAlg2CfgWithLast lsfInit C_lsst lastTool lastConstant sparsify params
      hp_s hp_t M₀ N₀ B_cap hM₀1 α Ψ ε spanConst
    ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
      (D.G 0).m ≤ M →
      concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ k τ M N D →
      ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
        (∑ j ∈ Finset.range k,
          (cfg.T.lsfs (cfg.T.runOrdAfterRestarts k M N D ord restarts t) j).wstr e) / (k : ℝ) ≤
          cfg.σ_mwu (D.G t).n := by
  intro cfg k τ M N D ord restarts hk hG₀ hD hLen hℓ hM hPred t ht e he
  have hM_sq : (D.G 0).m ≤ M₀ ^ 2 := le_trans hM hPred.2.1
  exact concreteMachMWU_le lsfInit C_lsst hInit sparsify params spanConst M₀ hG₀ hM_sq ord restarts
    hk hD hℓ t ht e he

/-- A level-`i` length range gives `concreteChainToolPred` for every history that starts at those
lengths. The upper end `e^Λ σ^i` is at most `e^{Λ + (d - 1) log σ}` because `i ≤ d - 1` and
`σ ≥ 2`. -/
theorem concreteChainToolPred_of_levelLenRange {TP : SparseCoreParams}
    {C_lsst : ℝ} {M₀ N₀ : ℕ} {hM₀1 : 1 ≤ M₀} {Ψ : ℝ} (hTP : TP.Valid)
    (hσ_eq : ∀ k n, TP.σ k n = max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log ((n : ℝ) + 2)) ^ 6))
    (hγM₀ : TP.γ_ℓ (M₀ ^ 2) ≤ M₀)
    (hγk : TP.γ_ℓ (M₀ ^ 2) ≤ (concreteChainParams M₀ hM₀1).k)
    {i : ℕ} (hi : i < (concreteChainParams M₀ hM₀1).d) {G : MGraph} {ℓ : ℕ → ℝ}
    (hR : LevelLenRange TP (concreteChainParams M₀ hM₀1) N₀ (max 0 Ψ) i G ℓ)
    {τ : ℕ} {D : DynamicInstance} (hG : D.G 0 = G) (hℓ : D.ℓ 0 = ℓ) :
    concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ (concreteChainParams M₀ hM₀1).k τ
      (levelM TP (concreteChainParams M₀ hM₀1) i) N₀ D := by
  set P := concreteChainParams M₀ hM₀1
  set σ_cap := max (2 : ℝ) (max 1 (mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6))
  have hM₀_eq : P.M₀ = M₀ := rfl
  have hγM₀' : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀ := by simpa only [hM₀_eq] using hγM₀
  have hγk' : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k := by simpa only [hM₀_eq] using hγk
  refine ⟨rfl, by simpa only [hM₀_eq] using levelM_le_sq hTP hγM₀' hγk' i, le_rfl, ?_⟩
  have hσ_eq' : max (2 : ℝ) (TP.σ P.k N₀) = σ_cap := by simp only [σ_cap, hσ_eq]
  have hσ_pos : 0 < σ_cap := by linarith [le_max_left (2 : ℝ) (max 1 (mwuK0 C_lsst * (P.k : ℝ) *
    (Real.log ((N₀ : ℝ) + 2)) ^ 6))]
  have hlogσ_nn : 0 ≤ Real.log σ_cap :=
    Real.log_nonneg (by linarith [le_max_left (2 : ℝ) (max 1 (mwuK0 C_lsst * (P.k : ℝ) *
      (Real.log ((N₀ : ℝ) + 2)) ^ 6))])
  have hi_le : (i : ℝ) ≤ ((P.d - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_sub_one_of_lt hi
  intro e he
  rw [hG] at he
  rw [hℓ]
  have hle := hR e he
  rw [hσ_eq'] at hle
  refine ⟨hle.1, ?_⟩
  calc
    ℓ e ≤ Real.exp (max 0 Ψ) * σ_cap ^ i := hle.2
    _ = Real.exp (max 0 Ψ) * Real.exp ((i : ℝ) * Real.log σ_cap) := by
      conv_lhs => rw [← Real.exp_log hσ_pos, ← Real.exp_nat_mul]
    _ = Real.exp (max 0 Ψ + (i : ℝ) * Real.log σ_cap) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap) :=
      Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonneg_right hi_le hlogσ_nn))

/-- The concrete tool of `concreteAlg2CfgWithLast` meets the chain's supply hypothesis with
`Λ = max 0 Ψ`: every start the chain can build satisfies `concreteChainToolPred`
(`concreteChainToolPred_of_levelLenRange`), and the tool meets its specification there
(`concreteRestartSpecOn_withLast_of_cap`). -/
theorem concreteChainToolSupply_withLast_of_cap
    (lsfInit : LSFInit) (C_lsst : ℝ)
    (hInit : IsConcreteLSFInit lsfInit C_lsst)
    (lastTool : LastLevelTool) (lastConstant : ℝ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (hSp : ∀ mMax, SparsifySpec mMax (params mMax) sparsify)
    (cap : ∀ (M₀ : ℕ), ℕ → ℝ → 1 ≤ M₀ → ℕ)
    (hCap : ∀ (M₀ N₀ : ℕ) (Ψ : ℝ) (hM₀1 : 1 ≤ M₀),
      concreteBCap C_lsst Ψ M₀ N₀ hM₀1 ≤ cap M₀ N₀ Ψ hM₀1)
    (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀)
    (spanConst : ℕ := 1) (hConst : 1 ≤ spanConst := by omega) :
    let B_cap := cap M₀ N₀ Ψ hM₀1
    let cfg := concreteAlg2CfgWithLast lsfInit C_lsst lastTool lastConstant sparsify
      params hp_s hp_t M₀ N₀ B_cap hM₀1 α Ψ ε spanConst
    cfg.TP.γ_ℓ (M₀ ^ 2) ≤ M₀ → cfg.TP.γ_ℓ (M₀ ^ 2) ≤ cfg.P.k →
    ChainToolSupply cfg.T cfg.TP cfg.P cfg.N₀ (max 0 cfg.Ψ) := by
  intro B_cap cfg hγM₀ hγk i hi G ℓ _ _ hR
  have hTP : cfg.TP.Valid :=
    bundleCoreParamsMachWith_valid (concreteEnv C_lsst params hp_s hp_t M₀ B_cap) spanConst
  exact SparseCoreRestartTool.toolOKAt_of_on
    (concreteRestartSpecOn_withLast_of_cap lsfInit C_lsst hInit lastTool lastConstant sparsify
      params hp_s hp_t hSp cap hCap M₀ N₀ α Ψ ε hM₀1 spanConst hConst)
    (fun _ _ hG hℓ => concreteChainToolPred_of_levelLenRange hTP (fun _ _ => rfl) hγM₀ hγk hi hR
      hG hℓ)

/-- The MWU average-stretch bound of `concreteAlg2CfgWithLast` on every history whose size
parameter is at most `M₀ ^ 2`. -/
theorem concreteRestartMWULe
    (lsfInit : LSFInit) (C_lsst : ℝ)
    (hInit : IsConcreteLSFInit lsfInit C_lsst)
    (lastTool : LastLevelTool) (lastConstant : ℝ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (M₀ N₀ B_cap : ℕ) (hM₀1 : 1 ≤ M₀) (α Ψ ε : ℝ) (spanConst : ℕ := 1) :
    let cfg := concreteAlg2CfgWithLast lsfInit C_lsst lastTool lastConstant sparsify params
      hp_s hp_t M₀ N₀ B_cap hM₀1 α Ψ ε spanConst
    cfg.T.ToolMWUOrdRestartNoHiddenLe cfg.σ_mwu (cfg.P.M₀ ^ 2) := by
  intro cfg k τ M N D ord restarts hMle hk hG₀ hD _ hℓ _ hM _ _ _ t ht e he
  exact concreteMachMWU_le lsfInit C_lsst hInit sparsify params spanConst M₀ hG₀ (le_trans hM hMle)
    ord restarts hk hD hℓ t ht e he

end OconcFieldBridge

end MinCostFlow.Chain.Ordered
