module

public import MinCostFlow.ExpanderDecomp.RouteMeets
public import MinCostFlow.ExpanderDecomp.CorePlayer
public import MinCostFlow.ExpanderDecomp.OuterCost
public import MinCostFlow.ExpanderDecomp.ProgRemoveFake
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concrete Expander-Decomposition Model with No Player Hypotheses

Instantiates all player and primitive-cost parameters of the outer expander decomposition
(`OuterDecomp.lean`, `OuterCost.lean`) with the concrete constructions proved in this directory:
* Router: `routeOrCut` and `routeOrCutCost` (`RouteOrCut.lean`, `RouteMeets.lean`), proving
  `routeOrCutCost_bounded : RouteCostBounded routeOrCutCost 20` (`20 ≤ 39`).
* Trimming model cost: `coreRemoveFakeCost` (meeting `RemoveFakeCostBounded` with `C_trim = 1 ≤ 2^20`)
  and `outerRemoveFakeCost` (meeting `IsRemoveFakeCost` with `trimC = 1 ≤ 2^36`), together with
  explicit constant-factor upper bounds relating the Word-RAM step bound
  `ProgRemoveFake.removeFakeCost` to both (`progRemoveFakeCost_le_coreRemoveFakeCost` and
  `progRemoveFakeCost_le_outerRemoveFakeCost`).
* Cloud expander: `ExplicitExpander.explicitGraph` (`isCloudExpander_explicitGraph_default`).
* Core cut player: `concreteCore` / `concreteCoreCost`, meeting `IsCorePlayer ParamConfig.default M
  (rOf M)` with no hypotheses (`concreteCore_isCorePlayer`).

Main theorems (only hypotheses are on `G`):
* `decompModelLabels_spec`: for a valid loopless graph `G` with `thresholdB1 envelopeCr ≤ G.m`,
  `decompModelLabels G` is a `(1 / 200, phiOut ParamConfig.default G.m (rOf G.m))`-expander
  decomposition of `G`.
* `decompModelCost_le_used`: for the same `G`, `decompModelCost G` meets the target envelope of
  `outerDecompCost_le_used` (`ExpanderDecompositionUsed`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- Model trimming cost for Step D of `OneShot` / `Core`:
`(|X| + |E(G[X])| + |F| + 1) · L² · P_q²`. -/
def coreRemoveFakeCost (L : ℕ) : RemoveFakeCostFn :=
  fun G X F P_q => (X.card + (G.inside X).length + F.length + 1) * L ^ 2 * P_q ^ 2

/-- Model trimming cost for the fake-edge removal step of the outer recursion:
`|V(H)| + |F'| + (|E(H)| + |F'|) · Λ² · L²`. -/
def outerRemoveFakeCost (M : ℕ) (H : CompactSubgraph) (F' : List (ℕ × ℕ)) (Λ : ℕ) : ℕ :=
  H.verts.length + F'.length + (H.edges.length + F'.length) * Λ ^ 2 * (LParam M) ^ 2

/-- Concrete recursive core cut player at `cfg = ParamConfig.default`, `r = rOf M`, router
`routeOrCut`, and cloud family `ExplicitExpander.explicitGraph`. -/
noncomputable def concreteCore (M : ℕ) : ℕ → Graph → CoreResult :=
  coreForParam ParamConfig.default M (rOf M) routeOrCut ExplicitExpander.explicitGraph

/-- Operation count of `concreteCore`. -/
noncomputable def concreteCoreCost (M : ℕ) : ℕ → Graph → ℕ :=
  coreCostForParam ParamConfig.default M (rOf M) routeOrCut routeOrCutCost
    (coreRemoveFakeCost (LParam M)) ExplicitExpander.explicitGraph

/-- Complete expander-decomposition model labels with all players fixed to concrete models. -/
noncomputable def decompModelLabels (G : Graph) : List ℕ :=
  outerDecompLabels ParamConfig.default G.m (rOf G.m)
    ExplicitExpander.explicitGraph (concreteCore G.m) routeOrCut G

/-- Complete expander-decomposition model operation count with all players and costs fixed. -/
noncomputable def decompModelCost (G : Graph) : ℕ :=
  outerDecompCost ParamConfig.default G.m (rOf G.m)
    ExplicitExpander.explicitGraph (concreteCore G.m) (concreteCoreCost G.m)
    routeOrCut routeOrCutCost (outerRemoveFakeCost G.m) G

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### 1. Concrete cost bounds for the router and `RemoveFake` -/

/-- `routeOrCutCost` satisfies `RouteCostBounded` with constant `routeCostConst = 20 ≤ 39`. -/
theorem routeOrCutCost_bounded : RouteCostBounded routeOrCutCost 20 := by
  intro G X pairs Δ L b z _hX _hloop hΔ hdeg hL hcard hb hvalid
  have hle := routeOrCutCost_le G pairs (routeTerminalPairs_of_validTerminalPairs hvalid)
    (z := z) hΔ hb hL hdeg hcard
  have hmul :
      routeCostConst * pairs.length * (X.card + (G.inside X).length + 1) *
        (routeD Δ b L + 1) * routeR Δ b L =
      20 * (pairs.length * (X.card + (G.inside X).length + 1) *
        (routePathLen Δ b L + 1) * routeCong Δ b L) := by
    unfold routeCostConst routeD routeR
    ring
  rw [hmul] at hle
  exact le_trans hle (Nat.mul_le_mul_left 20 (Nat.le_succ _))

/-- `coreRemoveFakeCost L` satisfies `RemoveFakeCostBounded` with constant `C_trim = 1 ≤ 2 ^ 20`. -/
theorem coreRemoveFakeCost_bounded (L : ℕ) :
    RemoveFakeCostBounded (coreRemoveFakeCost L) L 1 := by
  intro G X F P_q _
  simp [coreRemoveFakeCost]

/-- `outerRemoveFakeCost M` satisfies `IsRemoveFakeCost` with constant `trimC = 1 ≤ 2 ^ 36`. -/
theorem outerRemoveFakeCost_isRemoveFakeCost (M : ℕ) :
    IsRemoveFakeCost M 1 (outerRemoveFakeCost M) := by
  intro H F' Λ _ _
  simp [outerRemoveFakeCost]

/-- Under the Step D size/degree regime (`4 ≤ L`, `|X| < 2^L`, `|E(G[X])| ≤ 512 L |X|`,
`|F| ≤ |X|`, `12 ≤ P_q`), the Word-RAM step bound `ProgRemoveFake.removeFakeCost` at `ρ = 12 / P_q`
is within a fixed constant factor (`200000000`) of the model cost `coreRemoveFakeCost L`. -/
theorem progRemoveFakeCost_le_coreRemoveFakeCost {L : ℕ} (hL4 : 4 ≤ L)
    {G : Graph} {X : Finset ℕ} {F : List (ℕ × ℕ)} {P_q : ℕ}
    (hXL : X.card < 2 ^ L) (hmH : (G.inside X).length ≤ 512 * L * X.card)
    (hmF : F.length ≤ X.card) (hP12 : 12 ≤ P_q) :
    removeFakeCost X.card (G.inside X).length F.length 12 P_q ≤
      200000000 * coreRemoveFakeCost L G X F P_q := by
  set k := X.card
  set mH := (G.inside X).length
  set mF := F.length
  have hLrf_le : Nat.log 2 (2 * (mH + 2 * mF) + 1) + 1 ≤ 5 * L := by
    have hlt : 2 * (mH + 2 * mF) + 1 < 2 ^ (5 * L) := by
      have hLpow : L < 2 ^ L := Nat.lt_two_pow_self
      have h1 : 2 * (mH + 2 * mF) + 1 ≤ 2 * (512 * L * k + 2 * k) + 1 := by omega
      have h2 : 2 * (512 * L * k + 2 * k) + 1 ≤ 2048 * L * 2 ^ L := by
        have hLk : 512 * L * k + 2 * k ≤ 514 * L * k := by
          have h2k : 2 * k ≤ 2 * L * k := by
            calc 2 * k = 2 * 1 * k := by ring
              _ ≤ 2 * L * k := Nat.mul_le_mul_right k (Nat.mul_le_mul_left 2 (by omega))
          have h514 : 512 * L * k + 2 * L * k = 514 * L * k := by ring
          omega
        have hk2 : k + 1 ≤ 2 ^ L := hXL
        have h1028 : 2 * (514 * L * k) + 1 ≤ 1028 * L * 2 ^ L := by
          have h1' : 1 ≤ 1028 * L := by omega
          have h2' : 1028 * L * k + 1028 * L ≤ 1028 * L * 2 ^ L := by
            calc 1028 * L * k + 1028 * L = 1028 * L * (k + 1) := by ring
              _ ≤ 1028 * L * 2 ^ L := Nat.mul_le_mul_left _ hk2
          have hmul : 2 * (514 * L * k) = 1028 * L * k := by ring
          omega
        have : 1028 * L * 2 ^ L ≤ 2048 * L * 2 ^ L :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right L (by decide))
        omega
      have h3 : 2048 * L * 2 ^ L < 2 ^ (5 * L) := by
        calc 2048 * L * 2 ^ L
            < 2048 * 2 ^ L * 2 ^ L := by
              exact Nat.mul_lt_mul_of_pos_right
                (Nat.mul_lt_mul_of_pos_left hLpow (by decide)) (Nat.two_pow_pos L)
          _ = 2 ^ (2 * L + 11) := by
              rw [show (2048 : ℕ) = 2 ^ 11 by decide, ← pow_add, ← pow_add]; congr 1; omega
          _ ≤ 2 ^ (5 * L) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hlog : Nat.log 2 (2 * (mH + 2 * mF) + 1) < 5 * L :=
      Nat.log_lt_of_lt_pow (by omega) hlt
    omega
  have hasym := removeFakeCost_le_asymptotic k mH mF 12 P_q (by decide) hP12
  dsimp only at hasym
  set Lrf : ℕ := Nat.log 2 (2 * (mH + 2 * mF) + 1) + 1
  have hρ_sq : ((12 : ℝ) / (P_q : ℝ)) ^ 2 = 144 / ((P_q : ℝ) ^ 2) := by
    rw [div_pow]; norm_num
  have hterm1 : (k : ℝ) + mF ≤ ((k : ℝ) + mH + mF + 1) * (L : ℝ) ^ 2 * (P_q : ℝ) ^ 2 := by
    have hLP : (1 : ℝ) ≤ (L : ℝ) ^ 2 * (P_q : ℝ) ^ 2 := by
      have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
      have hP1 : (1 : ℝ) ≤ P_q := by exact_mod_cast (by omega : 1 ≤ P_q)
      have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
      have hP2 : (1 : ℝ) ≤ (P_q : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hkm : (k : ℝ) + mF ≤ (k : ℝ) + mH + mF + 1 := by linarith
    calc (k : ℝ) + mF ≤ ((k : ℝ) + mH + mF + 1) * 1 := by linarith
      _ ≤ ((k : ℝ) + mH + mF + 1) * ((L : ℝ) ^ 2 * (P_q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hLP (by positivity)
      _ = ((k : ℝ) + mH + mF + 1) * (L : ℝ) ^ 2 * (P_q : ℝ) ^ 2 := by ring
  have hterm2 : ((mH : ℝ) + mF + 1) * (Lrf : ℝ) ^ 2 / ((12 : ℝ) / (P_q : ℝ)) ^ 2 ≤
      ((k : ℝ) + mH + mF + 1) * (L : ℝ) ^ 2 * (P_q : ℝ) ^ 2 := by
    rw [hρ_sq, div_div_eq_mul_div]
    have hLrf_r : (Lrf : ℝ) ≤ 5 * (L : ℝ) := by exact_mod_cast hLrf_le
    have hLrf_sq : (Lrf : ℝ) ^ 2 ≤ 25 * (L : ℝ) ^ 2 := by nlinarith
    have hnum : ((mH : ℝ) + mF + 1) * (Lrf : ℝ) ^ 2 * (P_q : ℝ) ^ 2 ≤
        ((k : ℝ) + mH + mF + 1) * (25 * (L : ℝ) ^ 2) * (P_q : ℝ) ^ 2 := by
      have hm_le : (mH : ℝ) + mF + 1 ≤ (k : ℝ) + mH + mF + 1 := by linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hm_le hLrf_sq (by positivity) (by positivity)) (by positivity)
    have hnn : (0 : ℝ) ≤ ((k : ℝ) + mH + mF + 1) * (L : ℝ) ^ 2 * (P_q : ℝ) ^ 2 := by positivity
    linarith
  have hreal : (removeFakeCost k mH mF 12 P_q : ℝ) ≤
      (200000000 * coreRemoveFakeCost L G X F P_q : ℕ) := by
    unfold coreRemoveFakeCost
    push_cast
    linarith
  exact_mod_cast hreal

/-- In the regime of the outer fake-edge removal step (`|E(H)| + |F'| ≤ 2 M`, `1 ≤ Λ`, `1 ≤ |E(H)|`), the Word-RAM
step bound `ProgRemoveFake.removeFakeCost` at `ρ = 1 / Λ` is within a fixed constant factor
(`200000000`) of the outer model cost `outerRemoveFakeCost M`. -/
theorem progRemoveFakeCost_le_outerRemoveFakeCost {M : ℕ}
    {H : CompactSubgraph} {F' : List (ℕ × ℕ)} {Λ : ℕ}
    (hm : H.edges.length + F'.length ≤ 2 * M) (hΛ : 1 ≤ Λ) (hHpos : 1 ≤ H.edges.length) :
    removeFakeCost H.verts.length H.edges.length F'.length 1 Λ ≤
      200000000 * outerRemoveFakeCost M H F' Λ := by
  set k := H.verts.length
  set mH := H.edges.length
  set mF := F'.length
  have hLrf_le : Nat.log 2 (2 * (mH + 2 * mF) + 1) + 1 ≤ LParam M := by
    have hlt : 2 * (mH + 2 * mF) + 1 < 2 ^ LParam M := by
      have h1 : 2 * (mH + 2 * mF) + 1 < 4 * (2 * M + 2) := by omega
      have h2 : 2 * M + 2 ≤ 2 ^ ell M := Nat.le_pow_clog (by decide) (2 * M + 2)
      have hell : 1 ≤ ell M := one_le_ell M
      have h3 : 4 * (2 * M + 2) ≤ 2 ^ LParam M := by
        unfold LParam
        calc 4 * (2 * M + 2) ≤ 2 ^ 2 * 2 ^ ell M := Nat.mul_le_mul_left 4 h2
          _ = 2 ^ (2 + ell M) := (pow_add 2 2 (ell M)).symm
          _ ≤ 2 ^ (4 * ell M) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hlog : Nat.log 2 (2 * (mH + 2 * mF) + 1) < LParam M :=
      Nat.log_lt_of_lt_pow (by omega) hlt
    omega
  have hasym := removeFakeCost_le_asymptotic k mH mF 1 Λ (le_refl 1) hΛ
  dsimp only at hasym
  set Lrf : ℕ := Nat.log 2 (2 * (mH + 2 * mF) + 1) + 1
  have hρ_sq : ((1 : ℝ) / (Λ : ℝ)) ^ 2 = 1 / ((Λ : ℝ) ^ 2) := by
    rw [div_pow]; norm_num
  have hterm2 : ((mH : ℝ) + mF + 1) * (Lrf : ℝ) ^ 2 / ((1 : ℝ) / (Λ : ℝ)) ^ 2 ≤
      2 * (((mH : ℝ) + mF) * (Λ : ℝ) ^ 2 * (LParam M : ℝ) ^ 2) := by
    rw [hρ_sq, div_div_eq_mul_div, div_one]
    have hLrf_r : (Lrf : ℝ) ≤ LParam M := by exact_mod_cast hLrf_le
    have hLrf_sq : (Lrf : ℝ) ^ 2 ≤ (LParam M : ℝ) ^ 2 := by nlinarith
    have hm1 : (mH : ℝ) + mF + 1 ≤ 2 * ((mH : ℝ) + mF) := by
      have : (1 : ℝ) ≤ mH := by exact_mod_cast hHpos
      linarith
    calc ((mH : ℝ) + mF + 1) * (Lrf : ℝ) ^ 2 * (Λ : ℝ) ^ 2
        ≤ (2 * ((mH : ℝ) + mF)) * (LParam M : ℝ) ^ 2 * (Λ : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hm1 hLrf_sq (by positivity) (by positivity)) (by positivity)
      _ = 2 * (((mH : ℝ) + mF) * (Λ : ℝ) ^ 2 * (LParam M : ℝ) ^ 2) := by ring
  have hreal : (removeFakeCost k mH mF 1 Λ : ℝ) ≤
      (200000000 * outerRemoveFakeCost M H F' Λ : ℕ) := by
    unfold outerRemoveFakeCost
    push_cast
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) + mF := by positivity
    linarith
  exact_mod_cast hreal

/-! ### 2. Concrete core player and full expander decomposition with no player hypotheses -/

/-- `concreteCore` / `concreteCoreCost` satisfies `IsCorePlayer ParamConfig.default M (rOf M)`
with no player or primitive-cost hypotheses. -/
theorem concreteCore_isCorePlayer (M : ℕ) :
    IsCorePlayer ParamConfig.default M (rOf M) (concreteCore M) (concreteCoreCost M) :=
  core_isCorePlayer_default_rOf (by decide) (by decide)
    routeOrCut_isMatchingPlayer routeOrCutCost_bounded (coreRemoveFakeCost_bounded (LParam M))

/-- **Full expander-decomposition correctness with no player hypotheses**: for every valid
loopless graph `G` with `thresholdB1 envelopeCr ≤ G.m`, `decompModelLabels G` is a
`(1 / 200, phiOut ParamConfig.default G.m (rOf G.m))`-expander decomposition of `G`. -/
theorem decompModelLabels_spec {G : Graph}
    (hv : G.IsValid) (hl : G.IsLoopless) (hm : thresholdB1 envelopeCr ≤ G.m) :
    IsExpanderDecomposition G (1 / 200) (phiOut ParamConfig.default G.m (rOf G.m))
      (decompModelLabels G) :=
  outerDecompLabels_default_spec isCloudExpander_explicitGraph
    (by norm_num [ExplicitExpander.alpha0]) hv hl hm
    (concreteCore_isCorePlayer G.m) routeOrCut_isMatchingPlayer

/-- **Full expander-decomposition operation-count envelope with no player hypotheses**: for every
valid loopless graph `G` with `thresholdB1 envelopeCr ≤ G.m`, `decompModelCost G` meets the target
envelope of `outerDecompCost_le_used` (`ExpanderDecompositionUsed`). -/
theorem decompModelCost_le_used {G : Graph}
    (hv : G.IsValid) (_hl : G.IsLoopless) (hm : thresholdB1 envelopeCr ≤ G.m) :
    (decompModelCost G : ℝ) ≤
      envelopeK ParamConfig.default * (G.n + ((G.m : ℝ) + 2) ^ (1 + envelopeK ParamConfig.default / rOf G.m) *
        Real.log ((G.m : ℝ) + 2) ^ (envelopeK ParamConfig.default * (rOf G.m : ℝ) ^ 2) /
          (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2) :=
  outerDecompCost_le_used (cfg := ParamConfig.default) (routeC := 20) (trimC := 1)
    isCloudExpander_explicitGraph
    (by norm_num [ParamConfig.default, ExplicitExpander.alpha0])
    (by decide) hv hm
    (concreteCore_isCorePlayer G.m)
    routeOrCut_isMatchingPlayer
    routeOrCutCost_bounded
    (outerRemoveFakeCost_isRemoveFakeCost G.m)
    (by decide) (by decide)

end MinCostFlow.ExpanderDecomp
