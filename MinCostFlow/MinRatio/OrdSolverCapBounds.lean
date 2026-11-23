module

public import MinCostFlow.MinRatio.OrdSolverRepFull
public import MinCostFlow.MinRatio.WireSpecBase
public import MinCostFlow.Final.ConcreteChainModelWithLast
import Mathlib.Tactic

/-!
# Cap and limb bounds for `SparseCoreCapHyp` and `WireCapFacts`

This file proves two facts about the caps and limb counts of the solver:

1. **Cap bound (`vCap + eCap + 2 ≤ (lvlM i + N₀ + 2) ^ capExp`)**:
   From `OrdSolverReachedInv` (its name bound `model.nextFresh ≤ alg2NameBase cfg G +
   intRebuildThreshold cfg.P cfg.N₀ 0`), we prove `model.nextFresh ≤ 2 * cfg.P.M₀`
   (`reached_nextFresh_le_two_M0`). Consequently, every vertex cap `vCap ≤ cfg.N₀` and edge cap
   `eCap ≤ 8 * cfg.P.M₀ + 2` (covering `nextFresh`, doubled `intCap ≤ 4 * nextFresh ≤ 8 * M₀`, and
   level capacities) satisfies:
   - `vCap + eCap + 2 ≤ (lvlM i + cfg.N₀ + 2) ^ 2` (`capExp = 2`) whenever `cfg.N₀ = 4 * cfg.P.M₀`
     (`reached_cap_bound_sq`);
   - `vCap + eCap + 2 ≤ (lvlM i + cfg.N₀ + 2) ^ 3` (`capExp = 3`) whenever `cfg.P.M₀ ≤ cfg.N₀`
     (`reached_cap_bound_cube`).
   We also export `reached_wireCapFacts_of_limbBound` to build `WireCapFacts 2 L (12 * M₀ + 4) model`
   given any linear limb bound `L ≤ 2 * (Nat.log 2 (lvlM i + N₀ + 2) + 1)`.

2. **Limb bound counterexample (`not_sparseCoreCapHyp_limbs`) and true quadratic bound
   (`concrete_ipmQualityLimbs_le_bundleLogFactor`)**:
   On the concrete solver format (`ipmQualityLimbs I.m V k`), `SparseCoreCapHyp`'s second conjunct
   `L ≤ capExp * (Nat.log 2 (M + N + 2) + 1)` is **false** for every constant `capExp : ℕ`:
   `ipmQualityLimbs I.m V k ≥ slackRangeExponent I.m V = 220000 * (I.m.size + V.size)^2 =
   Θ((log₂ M₀)^2)`, while `Nat.log 2 (levelM cfg.TP cfg.P 0 + cfg.N₀ + 2) + 1 = O(log₂ M₀)`
   (`not_sparseCoreCapHyp_limbs`).
   The true bound is quadratic in the log, matching `SparseCore.bundleLogFactor`: there is a
   constant `C_L` depending only on `W` such that
   `ipmQualityLimbs I.m V k ≤ C_L * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P i) cfg.N₀`
   for every valid circulation `J` and every level `i` (`concrete_ipmQualityLimbs_le_bundleLogFactor`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Final

/-! ## 1. Cap bounds from `OrdSolverReachedInv` -/

private theorem sup_id_add_one_le_of_lt {E : Finset ℕ} {m : ℕ} (hm : 0 < m)
    (hE : ∀ e ∈ E, e < m) :
    E.sup id + 1 ≤ m := by
  by_cases hne : E = ∅
  · subst hne; simp; omega
  · have hsup : E.sup id ≤ m - 1 := by
      refine Finset.sup_le fun e he => ?_
      have := hE e he
      simp only [id_eq]; omega
    omega

/-- From `OrdSolverReachedInv`, `model.nextFresh ≤ 2 * cfg.P.M₀`. -/
theorem reached_nextFresh_le_two_M0 {cfg : Alg2Config} {L P m : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {κ : ℝ} {G : MGraph}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    (hInv : OrdSolverReachedInv κ G P model tok)
    (hmPos : 0 < m) (hE : ∀ e ∈ G.E, e < m) (hmM0 : m ≤ cfg.P.M₀) :
    model.nextFresh ≤ 2 * cfg.P.M₀ := by
  have hnf := hInv.2.2.1
  have hbase : Ordered.alg2NameBase cfg G ≤ cfg.P.M₀ := by
    unfold Ordered.alg2NameBase
    exact max_le ((sup_id_add_one_le_of_lt hmPos hE).trans hmM0) le_rfl
  have hthr : intRebuildThreshold cfg.P cfg.N₀ 0 ≤ cfg.P.M₀ := by
    unfold intRebuildThreshold
    exact Nat.div_le_self _ _
  omega

/-- With `N₀ = 4 * M₀` (the concrete solver choice), `capExp = 2` covers every vertex cap
`vCap ≤ N₀` and edge cap `eCap ≤ 8 * M₀ + 2` at every level `i`. -/
theorem reached_cap_bound_sq {M₀ N₀ lvlM vCap eCap : ℕ}
    (hN₀ : N₀ = 4 * M₀) (hv : vCap ≤ N₀) (he : eCap ≤ 8 * M₀ + 2) :
    vCap + eCap + 2 ≤ (lvlM + N₀ + 2) ^ 2 := by
  have h1 : vCap + eCap + 2 ≤ 12 * M₀ + 4 := by omega
  have h2 : 12 * M₀ + 4 ≤ (4 * M₀ + 2) ^ 2 := by nlinarith
  have h3 : (4 * M₀ + 2) ^ 2 ≤ (lvlM + N₀ + 2) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  exact h1.trans (h2.trans h3)

/-- Unconditionally whenever `M₀ ≤ N₀`, `capExp = 3` covers every vertex cap `vCap ≤ N₀` and
edge cap `eCap ≤ 8 * M₀ + 2` at every level `i`. -/
theorem reached_cap_bound_cube {M₀ N₀ lvlM vCap eCap : ℕ}
    (hMN : M₀ ≤ N₀) (hv : vCap ≤ N₀) (he : eCap ≤ 8 * M₀ + 2) :
    vCap + eCap + 2 ≤ (lvlM + N₀ + 2) ^ 3 := by
  have h1 : vCap + eCap + 2 ≤ 9 * N₀ + 4 := by omega
  have h2 : 9 * N₀ + 4 ≤ (N₀ + 2) ^ 3 := by
    have hexp : (N₀ + 2) ^ 3 = N₀ ^ 3 + 6 * N₀ ^ 2 + 12 * N₀ + 8 := by ring
    omega
  have h3 : (N₀ + 2) ^ 3 ≤ (lvlM + N₀ + 2) ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  exact h1.trans (h2.trans h3)

/-- Builds `WireCapFacts 2 L (12 * cfg.P.M₀ + 4) model` from `cfg.N₀ = 4 * cfg.P.M₀` and any
linear limb bound `L ≤ 2 * (Nat.log 2 (model.chain.lvlM i + cfg.N₀ + 2) + 1)`. -/
theorem reached_wireCapFacts_of_limbBound {cfg : Alg2Config} {L : ℕ} {model : Alg2State cfg}
    (hN₀ : cfg.N₀ = 4 * cfg.P.M₀) (hChainN₀ : model.chain.N₀ = cfg.N₀)
    (hLimb : ∀ i < cfg.P.d, L ≤ 2 * (Nat.log 2 (model.chain.lvlM i + cfg.N₀ + 2) + 1)) :
    WireCapFacts 2 2 L (12 * cfg.P.M₀ + 4) model := by
  refine wireCapFacts_of_le fun i hi => ?_
  rw [hChainN₀]
  refine ⟨?_, hLimb i hi⟩
  have hsq : 12 * cfg.P.M₀ + 4 ≤ (4 * cfg.P.M₀ + 2) ^ 2 := by nlinarith
  have hmon : (4 * cfg.P.M₀ + 2) ^ 2 ≤ (model.chain.lvlM i + cfg.N₀ + 2) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  exact hsq.trans hmon

/-! ## 2. Quadratic limb bound (`bundleLogFactor`) and counterexample to linear `SparseCoreCapHyp` -/

private theorem size_le_log_add_one (n : ℕ) : n.size ≤ Nat.log 2 n + 1 := by
  rw [Nat.size_le]
  exact Nat.lt_pow_succ_log_self (by decide) n

private theorem size_eq_log_add_one {n : ℕ} (hn : 0 < n) : n.size = Nat.log 2 n + 1 := by
  have hle := size_le_log_add_one n
  have hlt : 2 ^ Nat.log 2 n < 2 ^ n.size :=
    lt_of_le_of_lt (Nat.pow_log_le_self 2 (by omega)) (Nat.lt_size_self n)
  have hgt : Nat.log 2 n < n.size := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
  omega

private theorem log_le_size (n : ℕ) : Nat.log 2 n ≤ n.size := by
  by_cases h0 : n = 0
  · subst h0; simp
  · have := size_eq_log_add_one (Nat.pos_of_ne_zero h0); omega

private theorem size_le_self (n : ℕ) : n.size ≤ n := by
  by_cases h0 : n = 0
  · subst h0; simp
  · rw [size_eq_log_add_one (Nat.pos_of_ne_zero h0)]
    have hlt : Nat.log 2 n < n := Nat.log_lt_self 2 h0
    omega

private theorem size_pow_le (m k : ℕ) : (m ^ k).size ≤ k * m.size + 1 := by
  rw [Nat.size_le]
  have hm : m < 2 ^ m.size := Nat.lt_size_self m
  calc m ^ k ≤ (2 ^ m.size) ^ k := Nat.pow_le_pow_left hm.le k
    _ = 2 ^ (m.size * k) := (pow_mul 2 m.size k).symm
    _ = 2 ^ (k * m.size) := by rw [mul_comm]
    _ < 2 ^ (k * m.size + 1) := Nat.pow_lt_pow_right (by decide) (by omega)

private theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rw [Nat.size_le]
  have ha : a < 2 ^ a.size := Nat.lt_size_self a
  have hb : b < 2 ^ b.size := Nat.lt_size_self b
  calc a * b < 2 ^ a.size * 2 ^ b.size := Nat.mul_lt_mul'' ha hb
    _ = 2 ^ (a.size + b.size) := (pow_add 2 a.size b.size).symm

private theorem integerQualityExponent_le_sq (A M : ℕ) :
    integerQualityExponent A M ≤ 512 * (A + 1) * (M.size + 1) ^ 2 := by
  unfold integerQualityExponent
  set b := (M.size + 1).size
  have hbLe : b ≤ M.size + 1 := size_le_self (M.size + 1)
  have hpowExp : (47 * b + 47) / 48 ≤ b + 1 := by omega
  have hpow1 : 2 ^ ((47 * b + 47) / 48) ≤ 2 ^ (b + 1) :=
    Nat.pow_le_pow_right (by decide) hpowExp
  have h2b : 2 ^ b ≤ 2 * (M.size + 1) := by
    have hbEq : b = Nat.log 2 (M.size + 1) + 1 := size_eq_log_add_one (by omega)
    rw [hbEq, pow_succ']
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
  have hpow2 : 2 ^ (b + 1) ≤ 4 * (M.size + 1) := by
    rw [pow_succ]; omega
  calc 128 * (A + 1) * b * 2 ^ ((47 * b + 47) / 48)
      ≤ 128 * (A + 1) * (M.size + 1) * (4 * (M.size + 1)) := by
        refine Nat.mul_le_mul (Nat.mul_le_mul_left _ hbLe) (hpow1.trans hpow2)
    _ = 512 * (A + 1) * (M.size + 1) ^ 2 := by ring

/-- **True quadratic limb bound (`bundleLogFactor`)**: for every concrete chain witness `W`, there
is a constant `C_L` (independent of `J` and `i`) such that the solver's limb count
`ipmQualityLimbs I.m V k` is at most `C_L * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P i) cfg.N₀`. -/
theorem concrete_ipmQualityLimbs_le_bundleLogFactor
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) :
    ∃ C_L : ℕ, ∀ (J : Circulation),
      J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let threshold := concreteEdgeThresholdWithLast W
      let A := concreteQualityBudgetWithLast W
      let k := cappedQualityExponent threshold A I.m
      let cfg := concreteCirculationCfgWithLast W J
      ∀ i : ℕ,
        ipmQualityLimbs I.m V k ≤ C_L * bundleLogFactor (levelM cfg.TP cfg.P i) cfg.N₀ := by
  let A := concreteQualityBudgetWithLast W
  let C_L := 29 * (4 * (220000 * 88 ^ 2 + 2048 * (A + 1)) + 2 * 93 + 100) +
      4 * (1 + 88000 + 110) + 93 + 40
  refine ⟨C_L, fun J hJn hJm hCap => ?_⟩
  dsimp only
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast W
  let k := cappedQualityExponent threshold A I.m
  let cfg := concreteCirculationCfgWithLast W J
  intro i
  have hM0Eq : cfg.P.M₀ = max I.m threshold := rfl
  have hN0Eq : cfg.N₀ = 4 * cfg.P.M₀ := rfl
  have hImLeM0 : I.m ≤ cfg.P.M₀ := by rw [hM0Eq]; exact le_max_left _ _
  have hJmLeIm : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap).1
  have hVle : V ≤ 16 * cfg.P.M₀ ^ 81 := by
    have h1 := solverPenalty_le J.m hJm
    exact h1.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (hJmLeIm.trans hImLeM0) 81))
  set B := Nat.log 2 (levelM cfg.TP cfg.P i + cfg.N₀ + 2) + 1 with hBdef
  have hB1 : 1 ≤ B := by omega
  have hM0Size : cfg.P.M₀.size ≤ B := by
    have h1 : cfg.P.M₀.size ≤ Nat.log 2 cfg.P.M₀ + 1 := size_le_log_add_one cfg.P.M₀
    have h2 : Nat.log 2 cfg.P.M₀ ≤ Nat.log 2 (levelM cfg.TP cfg.P i + cfg.N₀ + 2) :=
      Nat.log_mono_right (by omega)
    omega
  have hImSize : I.m.size ≤ B := (Nat.size_le_size hImLeM0).trans hM0Size
  have hVSize : V.size ≤ 81 * B + 6 := by
    have h1 : V.size ≤ (16 * cfg.P.M₀ ^ 81).size := Nat.size_le_size hVle
    have h2 : (16 * cfg.P.M₀ ^ 81).size ≤ (16 : ℕ).size + (cfg.P.M₀ ^ 81).size := size_mul_le _ _
    have h3 : (cfg.P.M₀ ^ 81).size ≤ 81 * cfg.P.M₀.size + 1 := size_pow_le _ 81
    have h16 : (16 : ℕ).size = 5 := by decide
    omega
  have hSlack : slackRangeExponent I.m V ≤ 220000 * (88 * B) ^ 2 := by
    unfold slackRangeExponent
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hkLe : k ≤ 512 * (A + 1) * (2 * B) ^ 2 := by
    have h1 : k = integerQualityExponent A cfg.P.M₀ := rfl
    rw [h1]
    exact (integerQualityExponent_le_sq A cfg.P.M₀).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hQSlack : qualitySlackExponent I.m V k ≤ (220000 * 88 ^ 2 + 2048 * (A + 1)) * B ^ 2 := by
    unfold qualitySlackExponent
    have h1 : 220000 * (88 * B) ^ 2 = (220000 * 88 ^ 2) * B ^ 2 := by ring
    have h2 : 512 * (A + 1) * (2 * B) ^ 2 = (2048 * (A + 1)) * B ^ 2 := by ring
    rw [h1] at hSlack
    rw [h2] at hkLe
    exact max_le (hSlack.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
      (hkLe.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))
  have hGrad : gradientCoefficientExponent I.m V ≤ 93 * B := by
    unfold gradientCoefficientExponent; omega
  have hAlpha : Num.IPM.alphaScale I.m V ≤ 88000 * B := by
    unfold Num.IPM.alphaScale; omega
  have hB_le_sq : B ≤ B ^ 2 := by nlinarith
  have h1_le_sq : 1 ≤ B ^ 2 := by nlinarith
  have hRange : ipmQualityRangeExponent I.m V k ≤
      (4 * (220000 * 88 ^ 2 + 2048 * (A + 1)) + 2 * 93 + 100) * B ^ 2 := by
    unfold ipmQualityRangeExponent
    have hG2 : gradientCoefficientExponent I.m V ≤ 93 * B ^ 2 :=
      hGrad.trans (Nat.mul_le_mul_left 93 hB_le_sq)
    nlinarith only [hQSlack, hG2, h1_le_sq]
  have hPrec : ipmQualityPrecision I.m V k ≤
      (24 * (4 * (220000 * 88 ^ 2 + 2048 * (A + 1)) + 2 * 93 + 100) + 4 * (1 + 88000 + 110)) * B ^ 2 := by
    unfold ipmQualityPrecision ipmQualityErrorBits
    have hI2 : I.m.size ≤ B ^ 2 := hImSize.trans hB_le_sq
    have hA2 : Num.IPM.alphaScale I.m V ≤ 88000 * B ^ 2 :=
      hAlpha.trans (Nat.mul_le_mul_left 88000 hB_le_sq)
    nlinarith only [hRange, hI2, hA2, h1_le_sq]
  have hLimbs : ipmQualityLimbs I.m V k ≤ C_L * B ^ 2 := by
    unfold ipmQualityLimbs
    dsimp only [C_L]
    have hG2 : gradientCoefficientExponent I.m V ≤ 93 * B ^ 2 :=
      hGrad.trans (Nat.mul_le_mul_left 93 hB_le_sq)
    nlinarith only [hPrec, hG2, hRange, h1_le_sq]
  exact hLimbs

/-- A valid 2-vertex, `m`-edge unit-capacity zero-cost circulation. -/
private def unitCirculation (m : ℕ) : Circulation where
  n := 2
  m := m
  tail := fun _ => ⟨0, by decide⟩
  head := fun _ => ⟨1, by decide⟩
  capacity := fun _ => 1
  cost := fun _ => 0

/-- **Counterexample to `SparseCoreCapHyp`'s linear limb bound**: for every constant `capExp : ℕ`
and every concrete chain witness `W`, there exists a valid circulation `J` (meeting every
dimension, cost, and capacity hypothesis of the solver) on which the concrete limb count
`ipmQualityLimbs I.m V k` violates `SparseCoreCapHyp capExp L (levelM cfg.TP cfg.P 0) cfg.N₀ vCap eCap`. -/
theorem not_sparseCoreCapHyp_limbs
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast)
    (capExp : ℕ) :
    ∃ (J : Circulation),
      J.n ≤ 2 * J.m + 1 ∧ 0 < J.m ∧ J.CostsBounded (J.m ^ 10) ∧
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) ∧
      ∀ (_vCap _eCap : ℕ),
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
          (concreteQualityBudgetWithLast W) I.m
        let cfg := concreteCirculationCfgWithLast W J
        ¬ (ipmQualityLimbs I.m V k ≤
            capExp * (Nat.log 2 (levelM cfg.TP cfg.P 0 + cfg.N₀ + 2) + 1)) := by
  let m := max (2 ^ (capExp + 20)) (concreteEdgeThresholdWithLast W + 1)
  let J := unitCirculation m
  have hmPos : 0 < m := lt_of_lt_of_le (Nat.two_pow_pos (capExp + 20)) (le_max_left _ _)
  have hJn : J.n ≤ 2 * J.m + 1 := by dsimp only [J, unitCirculation]; omega
  have hJm : 0 < J.m := hmPos
  have hCost : J.CostsBounded (J.m ^ 10) := fun _ => by
    dsimp only [J, unitCirculation]; simp
  have hCap : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40 := fun _ => by
    dsimp only [J, unitCirculation]
    exact ⟨le_rfl, Nat.one_le_pow _ _ hmPos⟩
  refine ⟨J, hJn, hJm, hCost, hCap, fun vCap eCap hHyp => ?_⟩
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast W
  let k := cappedQualityExponent threshold (concreteQualityBudgetWithLast W) I.m
  let cfg := concreteCirculationCfgWithLast W J
  have hImGe : m ≤ I.m := (solverConnectedAugmented_size J hJn hJm (fun e => (hCap e).1)).1
  have hM0Eq : cfg.P.M₀ = I.m := by
    change max I.m threshold = I.m
    exact max_eq_left (by omega)
  have hN0Eq : cfg.N₀ = 4 * I.m := by
    change 4 * cfg.P.M₀ = 4 * I.m; rw [hM0Eq]
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm (fun e => (hCap e).1)
  have hlvl0 : levelM cfg.TP cfg.P 0 ≤ I.m ^ 2 := by
    unfold levelM
    rw [pow_zero, mul_one]
    have hγ := hVcfg.hγM₀
    rw [hM0Eq] at hγ ⊢
    refine Nat.ceil_le.mpr ?_
    have hprod : (I.m : ℝ) * cfg.TP.γ_ℓ (I.m ^ 2) ≤ (I.m : ℝ) * (I.m : ℝ) :=
      mul_le_mul_of_nonneg_left hγ (Nat.cast_nonneg _)
    simpa only [Nat.cast_pow, sq, Nat.cast_mul] using hprod
  have hImGe2 : 2 ≤ I.m := le_trans (by
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ (capExp + 20) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ m := le_max_left _ _) hImGe
  have hSumLe : levelM cfg.TP cfg.P 0 + cfg.N₀ + 2 ≤ 4 * I.m ^ 2 := by
    rw [hN0Eq]; nlinarith
  have hLogLe : Nat.log 2 (levelM cfg.TP cfg.P 0 + cfg.N₀ + 2) + 1 ≤ 2 * I.m.size + 5 := by
    have h1 : Nat.log 2 (levelM cfg.TP cfg.P 0 + cfg.N₀ + 2) ≤ Nat.log 2 (4 * I.m ^ 2) :=
      Nat.log_mono_right hSumLe
    have h2 : Nat.log 2 (4 * I.m ^ 2) ≤ (4 * I.m ^ 2).size := log_le_size _
    have h3 : (4 * I.m ^ 2).size ≤ (4 : ℕ).size + (I.m ^ 2).size := size_mul_le _ _
    have h4 : (I.m ^ 2).size ≤ 2 * I.m.size + 1 := size_pow_le _ 2
    have h4sz : (4 : ℕ).size = 3 := by decide
    omega
  have hImSizeGe : capExp + 21 ≤ I.m.size := by
    have hpow : 2 ^ (capExp + 20) ≤ I.m := (le_max_left _ _).trans hImGe
    have hlog : capExp + 20 ≤ Nat.log 2 I.m :=
      (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr hpow
    have hsz : Nat.log 2 I.m + 1 ≤ I.m.size := by
      rw [size_eq_log_add_one (by omega)]
    omega
  have hLge : 220000 * I.m.size ^ 2 ≤ ipmQualityLimbs I.m V k := by
    have h1 : slackRangeExponent I.m V ≤ qualitySlackExponent I.m V k :=
      slackRangeExponent_le_qualitySlackExponent I.m V k
    have h2 : qualitySlackExponent I.m V k ≤ ipmQualityRangeExponent I.m V k := by
      unfold ipmQualityRangeExponent; omega
    have h3 : ipmQualityRangeExponent I.m V k ≤ ipmQualityLimbs I.m V k := by
      unfold ipmQualityLimbs; omega
    have h4 : 220000 * I.m.size ^ 2 ≤ slackRangeExponent I.m V := by
      unfold slackRangeExponent
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_add_right _ _) 2)
    omega
  have hUpper : ipmQualityLimbs I.m V k ≤ capExp * (2 * I.m.size + 5) :=
    hHyp.trans (Nat.mul_le_mul_left capExp hLogLe)
  nlinarith

end MinCostFlow.MinRatio
