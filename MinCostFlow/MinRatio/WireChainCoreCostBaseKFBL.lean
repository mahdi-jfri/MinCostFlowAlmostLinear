module

public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
public import MinCostFlow.MinRatio.WireShiftDeepCostKFBL
public import MinCostFlow.MinRatio.WireChainCorePreAux
import MinCostFlow.MinRatio.WireChainAlgebra
import Mathlib.Tactic

/-!
# Chain-update core live cost discharge under `KFBL` (`WireChainCoreCostBaseKFBL`)

Discharges the `levelCostDom`, `costTotalBranchA`, and `costTotalBranchB` fields of
`UpdateCoreOpsHypKFBL` (`WireChainCoreSpecKFBL.lean`) with explicit bounds that contain **no**
terms in `m`, `N₀`, `intCapMax`, `capLimit`, `fcap`, or `forestEdgeCap` outside `bundleLogFactor`,
`ordLevelLwMax`, and `levelM d`:

* `updateCoreFixedBound`: explicit `coreFixed uLen` bound — linear in `uLen` with `SubpolyNat`
  coefficients (polynomial in `d`, `k`, `L`, `Psc.mul`, `Psc.readout`, `B₀^d`, `LwMax₀`, `edMul^d`,
  `lastMul`, `levelM d`, `drainUnit`, `wireTreeSyncEditCost L drainUnit`, `wireRefreshOneCost L`).
* `updateCoreToolMulBound`: explicit `toolMul` bound (`SubpolyNat`), absorbing all level-0
  compaction/rebuild work (Branch A), all suffix live copies/rebuilds/packs (Branch B Case 1), and
  all forwarded non-rebuilt step costs (Branch B Cases 1–3) into `toolMul · Δ totalRuntime`.
* `updateCoreTreeMulBound`: explicit `treeMul` bound (`wireTreeSyncEditCost L drainUnit + 60`).
* `updateCore_levelCostDom`, `updateCore_costTotalBranchA`, `updateCore_costTotalBranchB`, and
  their concrete `sparseCoreBundleRestartToolMachWith` specializations `*_mach`.
-/

public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered
open MinCostFlow.DynSpanner MinCostFlow.SparseCore MinCostFlow.SparseCore.Program
open MinCostFlow.IPM.Machine

/-! ### 1. Explicit `coreFixed`, `toolMul`, and `treeMul` bounds -/

/-- Geometric growth base per non-rebuilt level for `bW_j + eW_j + 1`:
`(edMul + 6) * B₀ + 2`. Across `d` levels, `R^d = (O(log^2 m))^d = m^{o(1)}`. -/
@[expose] def updateCoreStepRatio (edMul M₀ N₀ : ℕ) : ℕ :=
  (edMul + 6) * SparseCore.bundleLogFactor M₀ N₀ + 2

/-- Explicit `coreFixed uLen` bound for `UpdateCoreOpsHypKFBL`: contains zero `m`, `N₀`,
`intCapMax`, `capLimit`, `fcap`, or `forestEdgeCap` terms. `mThresh` is the constant edge-count
threshold (`concreteEdgeThresholdWithLast`) so `480 * mThresh` is `O(1)` in `m`. -/
@[expose] def updateCoreFixedBound
    (L capExp drainUnit edMul lastMul mThresh : ℕ) (Psc : SparseCoreOrdParams)
    (k d M₀ Md N₀ uLen : ℕ) : ℕ :=
  let B₀ := SparseCore.bundleLogFactor M₀ N₀
  let LwMax₀ := ordLevelLwMax L capExp M₀ N₀
  let R := updateCoreStepRatio edMul M₀ N₀
  let stepMul := Psc.mul * (k + 1) * B₀ + 730
  let prefixLin :=
    wireRefreshOneCost L + wireTreeSyncEditCost L drainUnit + 17 * L + drainUnit + 3200 +
      14 * (d * R ^ d * stepMul + (670 + 155 * (d + 1)) * R ^ d)
  let termRebuildFixed :=
    2 * Psc.readout + (290 * Md + 240) + Md * (wireCoreLenEdgeCost LwMax₀ + 30) +
      Psc.mul * (4 * Md + 4) * B₀ + lastMul + 310 * Md + 1200
  uLen * prefixLin +
    3 * (d * R ^ d * stepMul + (670 + 155 * (d + 1)) * R ^ d) +
    d * (5 * Psc.mul + 4 * Psc.mul * B₀ + 5 * Psc.readout + 2000) +
    4 * Psc.mul * B₀ + 2 * Psc.readout + 71 * L + 600 * (d + 1) +
    termRebuildFixed + 510 * mThresh + 8500

/-- Explicit `toolMul` bound for `UpdateCoreOpsHypKFBL` (`SubpolyNat`): absorbs Branch A compaction
and suffix rebuilds, Branch B forwarded step costs, and Branch B interior suffix rebuilds. -/
@[expose] def updateCoreToolMulBound
    (L capExp drainUnit edMul lastMul : ℕ) (Psc : SparseCoreOrdParams)
    (k d M₀ N₀ : ℕ) : ℕ :=
  let B₀ := SparseCore.bundleLogFactor M₀ N₀
  let LwMax₀ := ordLevelLwMax L capExp M₀ N₀
  let R := updateCoreStepRatio edMul M₀ N₀
  let stepMul := Psc.mul * (k + 1) * B₀ + 730
  let branchAMul :=
    2 * (d + 1) * (wireTreeSyncEditCost L drainUnit + 172) +
      17 * L + drainUnit + 3100 +
      (5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 320)
  let branchBMul :=
    Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120 +
      (d * R ^ d * stepMul + (670 + 155 * (d + 1)) * R ^ d) +
      (5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 320) +
      4 * Psc.mul * B₀ + 310 * (d + 1)
  max lastMul (max branchAMul branchBMul)

/-- Explicit `treeMul` bound for `UpdateCoreOpsHypKFBL` (`SubpolyNat`). -/
@[expose] def updateCoreTreeMulBound (L drainUnit : ℕ) : ℕ :=
  wireTreeSyncEditCost L drainUnit + 120

/-! ### 2. Shared helpers -/

theorem one_le_bLog (M N : ℕ) : 1 ≤ SparseCore.bundleLogFactor M N := by
  unfold SparseCore.bundleLogFactor
  have h1 : 1 ≤ Nat.log 2 (M + N + 2) + 1 := Nat.succ_pos _
  nlinarith

theorem bLog_mono {M₁ M₂ N : ℕ} (h : M₁ ≤ M₂) :
    SparseCore.bundleLogFactor M₁ N ≤ SparseCore.bundleLogFactor M₂ N := by
  unfold SparseCore.bundleLogFactor
  exact Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1) 2

theorem lwMax_mono {L capExp M₁ M₂ N : ℕ} (h : M₁ ≤ M₂) :
    ordLevelLwMax L capExp M₁ N ≤ ordLevelLwMax L capExp M₂ N := by
  unfold ordLevelLwMax
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1)) _

theorem coreLenEdgeCost_mono {K₁ K₂ : ℕ} (h : K₁ ≤ K₂) :
    wireCoreLenEdgeCost K₁ ≤ wireCoreLenEdgeCost K₂ := by
  unfold wireCoreLenEdgeCost
  have hsq : K₁ ^ 2 ≤ K₂ ^ 2 := Nat.pow_le_pow_left h 2
  omega

/-- Geometric recurrence for forwarded `(bW, eW)` word counts along non-rebuilt levels `[0, i₀)`. -/
theorem branchB_words_geom_bound {edMul B₀ uLen i₀ : ℕ} {bW eW Δc : ℕ → ℕ}
    (hB0 : 1 ≤ B₀)
    (hb0 : bW 0 ≤ 4 * uLen + 1) (he0 : eW 0 ≤ 10 * uLen + 1)
    (hStep : ∀ j < i₀, bW (j + 1) ≤ 6 * Δc j + 1 ∧
      eW (j + 1) ≤ edMul * (Δc j + (bW j + eW j + 1) * B₀)) :
    let R := (edMul + 6) * B₀ + 2
    ∀ j ≤ i₀, bW j + eW j + 1 ≤ R ^ j * (14 * uLen + 3 + (Finset.range j).sum Δc) := by
  intro R j
  induction j with
  | zero =>
    intro _
    simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, add_zero]
    omega
  | succ j ih =>
    intro hj
    have hjLt : j < i₀ := by omega
    have hIH := ih (le_of_lt hjLt)
    obtain ⟨hb1, he1⟩ := hStep j hjLt
    have hR1 : 1 ≤ R := by dsimp [R]; omega
    have hRpow : 1 ≤ R ^ j := Nat.one_le_pow j R hR1
    set X := bW j + eW j + 1
    have hX1 : 1 ≤ X := by dsimp [X]; omega
    have hEdB : edMul * B₀ * X + 2 ≤ R * X := by
      have h1 : 2 ≤ 2 * X := by omega
      have h2 : edMul * B₀ * X + 2 * X = (edMul * B₀ + 2) * X := by ring
      have h3 : (edMul * B₀ + 2) * X ≤ R * X := by
        refine Nat.mul_le_mul_right X ?_
        dsimp [R]; nlinarith
      omega
    have hDc : (6 + edMul) * Δc j ≤ R * (R ^ j * Δc j) := by
      have h1 : 6 + edMul ≤ R := by dsimp [R]; nlinarith
      calc (6 + edMul) * Δc j ≤ R * Δc j := Nat.mul_le_mul_right _ h1
        _ = R * (1 * Δc j) := by ring
        _ ≤ R * (R ^ j * Δc j) := Nat.mul_le_mul_left R (Nat.mul_le_mul_right _ hRpow)
    have hMulIH : R * X ≤ R * (R ^ j * (14 * uLen + 3 + (Finset.range j).sum Δc)) :=
      Nat.mul_le_mul_left R hIH
    have hComb : bW (j + 1) + eW (j + 1) + 1 ≤ (6 + edMul) * Δc j + (edMul * B₀ * X + 2) := by
      have hmul : edMul * (Δc j + X * B₀) = edMul * Δc j + edMul * B₀ * X := by ring
      have h6e : (6 + edMul) * Δc j = 6 * Δc j + edMul * Δc j := by ring
      omega
    have hRange : (Finset.range (j + 1)).sum Δc = (Finset.range j).sum Δc + Δc j :=
      Finset.sum_range_succ Δc j
    rw [hRange]
    have hEq : R * (R ^ j * Δc j) + R * (R ^ j * (14 * uLen + 3 + (Finset.range j).sum Δc)) =
        R ^ (j + 1) * (14 * uLen + 3 + ((Finset.range j).sum Δc + Δc j)) := by
      rw [pow_succ']; ring
    omega

/-- Summing the geometric bound over `j ∈ Finset.range i₀` (`i₀ ≤ d`). -/
theorem branchB_words_sum_le {edMul B₀ uLen i₀ d : ℕ} {bW eW Δc : ℕ → ℕ}
    (hB0 : 1 ≤ B₀) (hiLe : i₀ ≤ d)
    (hb0 : bW 0 ≤ 4 * uLen + 1) (he0 : eW 0 ≤ 10 * uLen + 1)
    (hStep : ∀ j < i₀, bW (j + 1) ≤ 6 * Δc j + 1 ∧
      eW (j + 1) ≤ edMul * (Δc j + (bW j + eW j + 1) * B₀)) :
    let R := (edMul + 6) * B₀ + 2
    (Finset.range i₀).sum (fun j => bW j + eW j + 1) ≤
      d * R ^ d * (14 * uLen + 3 + (Finset.range i₀).sum Δc) := by
  intro R
  have hG := branchB_words_geom_bound hB0 hb0 he0 hStep
  have hR1 : 1 ≤ R := by dsimp [R]; omega
  have hEach : ∀ j ∈ Finset.range i₀,
      bW j + eW j + 1 ≤ R ^ d * (14 * uLen + 3 + (Finset.range i₀).sum Δc) := by
    intro j hj
    have hjLt := Finset.mem_range.mp hj
    have h1 := hG j (le_of_lt hjLt)
    have hPow : R ^ j ≤ R ^ d := Nat.pow_le_pow_right hR1 (by omega)
    have hSum : (Finset.range j).sum Δc ≤ (Finset.range i₀).sum Δc :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (le_of_lt hjLt))
    exact h1.trans (Nat.mul_le_mul hPow (by omega))
  calc (Finset.range i₀).sum (fun j => bW j + eW j + 1)
      ≤ (Finset.range i₀).sum (fun _ => R ^ d * (14 * uLen + 3 + (Finset.range i₀).sum Δc)) :=
        Finset.sum_le_sum hEach
    _ = i₀ * (R ^ d * (14 * uLen + 3 + (Finset.range i₀).sum Δc)) := by
        simp [Finset.sum_const]
    _ ≤ d * (R ^ d * (14 * uLen + 3 + (Finset.range i₀).sum Δc)) :=
        Nat.mul_le_mul_right _ hiLe
    _ = d * R ^ d * (14 * uLen + 3 + (Finset.range i₀).sum Δc) := by ring

/-- Single rebuilt level `j < d`: bounds `updateCoreRebuildLevelCost + 9` by
`perFixed + (5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 320) * cfg.T.cost (next.scState j)`. -/
theorem rebuildLevel_cost_le {L capExp : ℕ} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {next : ChainState cfg.T cfg.P} {j : ℕ}
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (hjLt : j < cfg.P.d)
    (hLvlN : ShiftLoopLevelFacts cfg next)
    (hSub : (next.G (j + 1)).E ⊆ (next.G j).E)
    (hInitCost : 3 * (next.G j).m * SparseCore.bundleLogFactor (next.lvlM j) next.N₀ ≤
      cfg.T.cost (next.scState j)) :
    let M₀ := levelM cfg.TP cfg.P 0
    let B₀ := SparseCore.bundleLogFactor M₀ cfg.N₀
    let LwMax₀ := ordLevelLwMax L capExp M₀ cfg.N₀
    updateCoreRebuildLevelCost L capExp cfg Psc next j + 9 ≤
      (5 * Psc.mul + 4 * Psc.mul * B₀ + 2 * Psc.readout + 475) +
        (5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 320) * cfg.T.cost (next.scState j) := by
  dsimp only
  set M₀ := levelM cfg.TP cfg.P 0
  set B₀ := SparseCore.bundleLogFactor M₀ cfg.N₀
  set LwMax₀ := ordLevelLwMax L capExp M₀ cfg.N₀
  set cj := cfg.T.cost (next.scState j)
  set Gj := next.G j
  set Hj := next.G (j + 1)
  set Bj := SparseCore.bundleLogFactor (next.lvlM j) next.N₀
  have hLvlM : next.lvlM = levelM cfg.TP cfg.P := hLvlN.2.1
  have hN0 : next.N₀ = cfg.N₀ := hLvlN.2.2.1
  have hBj1 : 1 ≤ Bj := one_le_bLog _ _
  have h3Gm : 3 * Gj.m ≤ cj := (Nat.le_mul_of_pos_right _ (by omega : 0 < Bj)).trans hInitCost
  have hGm : Gj.m ≤ cj := by omega
  have hBjLe : Bj ≤ B₀ := by
    dsimp only [Bj]; rw [hLvlM, hN0]
    exact bLog_mono (levelM_le_levelM_zero hTP hγk j)
  have hLwLe : wireCoreLenEdgeCost (ordLevelLwMax L capExp (next.lvlM j) next.N₀) ≤
      wireCoreLenEdgeCost LwMax₀ := by
    rw [hLvlM, hN0]
    exact coreLenEdgeCost_mono (lwMax_mono (levelM_le_levelM_zero hTP hγk j))
  have hGn : Gj.n ≤ Gj.m + 1 := hLvlN.1 j (le_of_lt hjLt)
  have hHm : Hj.m ≤ Gj.m := Finset.card_le_card hSub
  have hHn : Hj.n ≤ Gj.m + 1 := (hLvlN.1 (j + 1) (by omega)).trans (Nat.add_le_add_right hHm 1)
  have hInTerm : Psc.mul * (Gj.n + Gj.m + (2 * Gj.n + 2 * Gj.m + 1) + 1) ≤
      2 * Psc.mul * cj + 5 * Psc.mul := by
    have h1 : Gj.n + Gj.m + (2 * Gj.n + 2 * Gj.m + 1) + 1 ≤ 2 * (3 * Gj.m) + 5 := by omega
    have h2 := Nat.mul_le_mul_left Psc.mul h1
    have h3 : Psc.mul * (2 * (3 * Gj.m) + 5) = 2 * Psc.mul * (3 * Gj.m) + 5 * Psc.mul := by ring
    have h4 : 2 * Psc.mul * (3 * Gj.m) ≤ 2 * Psc.mul * cj := Nat.mul_le_mul_left _ h3Gm
    omega
  have hOutTerm : Psc.mul * (2 * Hj.n + 2 * Hj.m + 1 + 1) * Bj ≤
      2 * Psc.mul * cj + 4 * Psc.mul * B₀ := by
    have h1 : 2 * Hj.n + 2 * Hj.m + 1 + 1 ≤ 4 * Gj.m + 4 := by omega
    have h2 : Psc.mul * (2 * Hj.n + 2 * Hj.m + 1 + 1) * Bj ≤ Psc.mul * (4 * Gj.m + 4) * Bj :=
      Nat.mul_le_mul_right Bj (Nat.mul_le_mul_left Psc.mul h1)
    have h3 : Psc.mul * (4 * Gj.m + 4) * Bj = 4 * Psc.mul * (Gj.m * Bj) + 4 * Psc.mul * Bj := by ring
    have h4 : 4 * Psc.mul * (Gj.m * Bj) ≤ 2 * Psc.mul * (3 * Gj.m * Bj) := by
      have h46 : 4 * (Gj.m * Bj) ≤ 6 * (Gj.m * Bj) := Nat.mul_le_mul_right _ (by decide)
      have h6eq : 2 * (3 * Gj.m * Bj) = 6 * (Gj.m * Bj) := by ring
      calc 4 * Psc.mul * (Gj.m * Bj) = Psc.mul * (4 * (Gj.m * Bj)) := by ring
        _ ≤ Psc.mul * (2 * (3 * Gj.m * Bj)) := Nat.mul_le_mul_left _ (h6eq ▸ h46)
        _ = 2 * Psc.mul * (3 * Gj.m * Bj) := by ring
    have h5 : 2 * Psc.mul * (3 * Gj.m * Bj) ≤ 2 * Psc.mul * cj := Nat.mul_le_mul_left _ hInitCost
    have h6 : 4 * Psc.mul * Bj ≤ 4 * Psc.mul * B₀ := Nat.mul_le_mul_left _ hBjLe
    omega
  have hCopyHj : copyGraphLiveCost Hj.n Hj.m ≤ 290 * cj + 240 := by
    unfold copyGraphLiveCost; omega
  have hLenHj : Hj.m * (wireCoreLenEdgeCost (ordLevelLwMax L capExp (next.lvlM j) next.N₀) + 30) ≤
      (wireCoreLenEdgeCost LwMax₀ + 30) * cj := by
    calc Hj.m * (wireCoreLenEdgeCost (ordLevelLwMax L capExp (next.lvlM j) next.N₀) + 30)
        ≤ cj * (wireCoreLenEdgeCost LwMax₀ + 30) := Nat.mul_le_mul (hHm.trans hGm) (by omega)
      _ = (wireCoreLenEdgeCost LwMax₀ + 30) * cj := Nat.mul_comm _ _
  have hExpand : (5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 320) * cj =
      Psc.mul * cj + 2 * Psc.mul * cj + 2 * Psc.mul * cj + 290 * cj +
        (wireCoreLenEdgeCost LwMax₀ + 30) * cj := by ring
  dsimp only [updateCoreRebuildLevelCost, ordLevelLiveCost]
  change Psc.mul * cj +
    (Psc.mul * (Gj.n + Gj.m + (2 * Gj.n + 2 * Gj.m + 1) + 1) +
      Psc.mul * (2 * Hj.n + 2 * Hj.m + 1 + 1) * Bj +
      2 * Psc.readout + copyGraphLiveCost Hj.n Hj.m +
      Hj.m * (wireCoreLenEdgeCost (ordLevelLwMax L capExp (next.lvlM j) next.N₀) + 30) + 200) +
    26 + 9 ≤ _
  omega

/-- `rebuildSuffix` returns `LT.cost (G' (idx + rem))` as its last component. -/
private lemma rebuildSuffix_lastCost {T : SparseCoreRestartTool} {LT : LastLevelTool}
    {P : ChainParams} {lvlM : ℕ → ℕ} {N₀ : ℕ} {ℓ₀ g₀ : ℕ → ℝ} :
    ∀ rem idx G sc bran upd cEnc cDec cFwd,
      let res := Chain.Ordered.rebuildSuffix T LT P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd
      res.2.2.2.2.2.2.2.2 = LT.cost (res.1 (idx + rem))
  | 0, _, _, _, _, _, _, _, _ => by simp [Chain.Ordered.rebuildSuffix]
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd => by
    dsimp only [Chain.Ordered.rebuildSuffix]
    rw [show idx + (rem + 1) = (idx + 1) + rem by omega]
    exact rebuildSuffix_lastCost rem (idx + 1) _ _ _ _ _ _ _

/-- Exact runtime rise for `algorithm1_rebuild` at level `0`. -/
private theorem algorithm1_rebuild_0_runtime_ge {T : SparseCoreRestartTool} {LT : LastLevelTool}
    {P : ChainParams} {st : ChainState T P} {Gnew : MGraph} {extraEnc : ℕ} (hd : 0 < P.d) :
    let next := (Chain.Ordered.algorithm1_rebuild T LT P st 0 Gnew extraEnc).1
    (Finset.range P.d).sum (fun j => T.cost (next.scState j)) + LT.cost (next.G P.d) ≤
      next.totalRuntime - st.totalRuntime := by
  dsimp only
  set next := (Chain.Ordered.algorithm1_rebuild T LT P st 0 Gnew extraEnc).1
  unfold ChainState.totalRuntime
  have hCl : next.closedRuntime =
      st.closedRuntime + (Finset.range P.d).sum (fun j => T.cost (st.scState j) + st.curEnc j) +
        st.curLastCost + extraEnc := by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hd, ↓reduceDIte]
    have hIco : Finset.Ico 0 P.d = Finset.range P.d := by ext x; simp
    rw [hIco]
  have hLC : next.curLastCost = LT.cost (next.G P.d) := by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hd, ↓reduceDIte]
    simpa [Nat.zero_add, Nat.sub_zero] using
      rebuildSuffix_lastCost (T := T) (LT := LT) (P := P) (lvlM := st.lvlM) (N₀ := st.N₀)
        (ℓ₀ := st.ℓ) (g₀ := st.g) (P.d - 0) 0 (fun j => if j = 0 then Gnew else st.G j)
        st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd
  have hSumLe : (Finset.range P.d).sum (fun j => T.cost (next.scState j)) ≤
      (Finset.range P.d).sum (fun j => T.cost (next.scState j) + next.curEnc j) :=
    Finset.sum_le_sum fun _ _ => Nat.le_add_right _ _
  rw [hCl, hLC]; omega

/-! ### 3. Discharging `UpdateCoreOpsHypKFBL` cost fields -/

/-- `updateCoreRebuildLevelCost` discharges `UpdateCoreOpsHypKFBL.levelCostDom` identically. -/
theorem updateCore_levelCostDom (L capExp : ℕ) (cfg : Alg2Config) (Psc : SparseCoreOrdParams)
    (next : ChainState cfg.T cfg.P) (j : ℕ) :
    updateCoreRebuildLevelCost L capExp cfg Psc next j ≤
      updateCoreRebuildLevelCost L capExp cfg Psc next j :=
  le_rfl

/-- Upper bound on `initTargetCap cfg G` in terms of `G.m` and a threshold slack `mThresh`:
the `4 * G.m` part scales with `mNew` (paid by `toolMul · Δ totalRuntime`), while `2 * mThresh + 1`
is a constant paid by `updateCoreFixedBound`. -/
theorem initTargetCap_le_four_m_add {cfg : Alg2Config} {G : MGraph} {mThresh : ℕ}
    (hSup : G.E.sup id ≤ G.m) (hM0 : cfg.P.M₀ ≤ G.m + mThresh) :
    initTargetCap cfg G ≤ 4 * G.m + 2 * mThresh + 1 := by
  unfold initTargetCap Chain.Ordered.alg2NameBase
  have hTh : intRebuildThreshold cfg.P cfg.N₀ 0 ≤ cfg.P.M₀ := Nat.div_le_self _ _
  have hMax : max (G.E.sup id + 1) cfg.P.M₀ ≤ G.m + mThresh + 1 :=
    max_le (by omega) (by omega)
  omega

set_option maxHeartbeats 800000 in
/-- Discharges `UpdateCoreOpsHypKFBL.costTotalBranchA` with `updateCoreFixedBound` and
`updateCoreToolMulBound` for any tool meeting `hInitLower`. -/
theorem updateCore_costTotalBranchA
    (L capExp drainUnit edMul lastMul mThresh m : ℕ) (cfg : Alg2Config) (G : MGraph)
    (Psc : SparseCoreOrdParams)
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (hInitLower : ∀ {M N : ℕ} {G : MGraph} {ℓ g : ℕ → ℝ} {ord : ℕ → List End},
      G.IsValid →
      3 * G.m * SparseCore.bundleLogFactor M N ≤ cfg.T.cost (cfg.T.initOrd cfg.P.k M N G ℓ g ord))
    (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ) (intCap rootECap : ℕ)
    (hdPos : 0 < cfg.P.d)
    (hOver0 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      intRebuildThreshold cfg.P model.chain.N₀ 0 < model.chain.updCount 0 + tr.2.2.2.2.length)
    (hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh)
    (hRef : RefreshBatch model.extG U)
    (hModelK : UpdateCoreModelInvKFBL model U gVec lVec)
    (hExtM : model.extG.m = m)
    (hRLeI : rootECap ≤ intCap)
    (hIntLe : intCap ≤ initTargetCap cfg G)
    (hGSup : G.E.sup id ≤ G.m)
    (hGM : G.m = m)
    (hM0Le : cfg.P.M₀ ≤ m + mThresh) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let n := model.extG.n
    let mNew := (modelPre.chain.G 0).m
    let sumOld := graphListEdgeSum (chainSuffixForests model.chain 0)
    let sumNew := graphListEdgeSum (chainSuffixForests modelPre.chain 0)
    let M₀ := levelM cfg.TP cfg.P 0
    let Md := levelM cfg.TP cfg.P cfg.P.d
    cfg.P.d * (Psc.readout + 48) +
      (230 * (cfg.P.d + 1) + 85 * sumOld + 300) +
      sumOld * (wireTreeSyncEditCost L drainUnit + 2) +
      (U.length * (wireRefreshOneCost L + 120) + 71 * L + 220) +
      (670 * (4 * U.length + 1) + 30) +
      (U.length * (17 * L + 70) + 80) +
      (85 * intCap + 40 * m + 110) +
      wireCompactLevel0Cost n rootECap intCap L mNew +
      (150 * rootECap + 60 * n + 120) + 150 +
      (Finset.range cfg.P.d).sum (fun j => updateCoreRebuildLevelCost L capExp cfg Psc modelPre.chain j + 9) +
      lastMul * (cfg.L.cost (modelPre.chain.G cfg.P.d) + 1) +
      cfg.P.d * (Psc.readout + 48) + 40 * cfg.P.d +
      (230 * (cfg.P.d + 1) + 85 * sumNew + 260) +
      sumNew * (wireTreeSyncEditCost L drainUnit + 2) +
      (80 * mNew + mNew * drainUnit + 120) + 1500 ≤
      updateCoreFixedBound L capExp drainUnit edMul lastMul mThresh Psc cfg.P.k cfg.P.d M₀ Md cfg.N₀ U.length +
        updateCoreToolMulBound L capExp drainUnit edMul lastMul Psc cfg.P.k cfg.P.d M₀ cfg.N₀ *
          (modelPre.chain.totalRuntime - model.chain.totalRuntime) := by
  dsimp only
  set d := cfg.P.d
  set M₀ := levelM cfg.TP cfg.P 0
  set Md := levelM cfg.TP cfg.P d
  set B₀ := SparseCore.bundleLogFactor M₀ cfg.N₀
  set LwMax₀ := ordLevelLwMax L capExp M₀ cfg.N₀
  set tMul := updateCoreToolMulBound L capExp drainUnit edMul lastMul Psc cfg.P.k d M₀ cfg.N₀
  set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  set U_int := tr.2.2.2.2
  set G0' := (model.chain.G 0).applyBatch U_int
  set modelPre := alg2PreResetState cfg model U gVec lVec
  set st0 : ChainState cfg.T cfg.P :=
    { model.chain with
      recUpdates := fun j => if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
  set ℓ' := fun e' => lVec (tr.2.2.1 e')
  set g' := fun e' => gVec (tr.2.2.1 e')
  set stLG : ChainState cfg.T cfg.P :=
    { st0 with ℓ := fun j => ℓ' (compactUnrank G0'.E j), g := fun j => g' (compactUnrank G0'.E j) }
  rcases hModelK with ⟨hLvl0, hLvlN, hValid, _, _, hSub, hLastOld, hLastNew, _, _, _, _, _⟩
  have hNextEq : modelPre.chain =
      (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stLG 0 G0'.compact ((model.chain.G 0).batchEnc U_int)).1 := by
    dsimp only [modelPre, alg2PreResetState, Chain.Ordered.algorithm1_update]
    rw [← hLvl0.2.2.1]
    cases hd : cfg.P.d with
    | zero => omega
    | succ d' =>
      change (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P model.chain.N₀ ℓ' g' (d' + 1) 0 st0 G0' U_int
        ((model.chain.G 0).batchEnc U_int)).1 = _
      unfold Chain.Ordered.updateLoop
      have hCond : intRebuildThreshold cfg.P model.chain.N₀ 0 < st0.updCount 0 + U_int.length := hOver0
      simp only [hCond, ↓reduceIte]
      rfl
  -- Equalities of edge counts `m = G0.m = G0'.m = mNew`
  obtain ⟨hTr1Eq, hFreshTr, _, _, _⟩ := refreshBatch_edge_dichotomy hFresh hRef
  have hG0m : (model.chain.G 0).m = m := by
    rw [← hExtM]; dsimp only [MGraph.m]; rw [hFresh.hE]
    exact Finset.card_image_of_injOn fun x hx y hy hxy => by
      have h1 := hFresh.hLeft x hx; have h2 := hFresh.hLeft y hy; rw [hxy] at h1; omega
  have hG0'm : G0'.m = m := by
    rw [← hExtM]; dsimp only [MGraph.m]; rw [hFreshTr.hE]
    exact Finset.card_image_of_injOn fun x hx y hy hxy => by
      have h1 := hFreshTr.hLeft x hx; have h2 := hFreshTr.hLeft y hy; rw [hxy] at h1; omega
  have hPreG0 : modelPre.chain.G 0 = G0'.compact := by
    rw [hNextEq]
    simp only [Chain.Ordered.algorithm1_rebuild, show 0 < cfg.P.d from hdPos, ↓reduceDIte]
    have hSuf := (ordRebuildSuffix_prefix_and_coreAt cfg.T cfg.L cfg.P stLG.lvlM stLG.N₀ stLG.ℓ stLG.g
      (d - 0) 0 (by omega) (fun j => if j = 0 then G0'.compact else stLG.G j) stLG.scState
      stLG.bran stLG.updCount stLG.curEnc stLG.curDecUpdates stLG.curFwd).1 0 le_rfl
    simpa using hSuf
  have hmNewEq : (modelPre.chain.G 0).m = m := by
    rw [hPreG0, compact_m, hG0'm]
  have hnEq : model.extG.n = (modelPre.chain.G 0).n := by
    rw [hPreG0, compact_n]; dsimp only [MGraph.n]
    have hV : G0'.V = (model.chain.G 0).V := by
      have h1 : G0'.V = model.extG.V := hFreshTr.hV.symm
      have h2 : (model.chain.G 0).V = model.extG.V := hFresh.hV.symm
      rw [h1, h2]
    rw [hV, hFresh.hV]
  have hnLe : model.extG.n ≤ (modelPre.chain.G 0).m + 1 := by
    rw [hnEq]; exact hLvlN.1 0 (Nat.zero_le _)
  -- Runtime rise decomposition and per-level init lower bounds
  have hDelta : (Finset.range d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) +
      cfg.L.cost (modelPre.chain.G d) ≤ modelPre.chain.totalRuntime - model.chain.totalRuntime := by
    have h := algorithm1_rebuild_0_runtime_ge (T := cfg.T) (LT := cfg.L) (P := cfg.P)
      (st := stLG) (Gnew := G0'.compact) (extraEnc := (model.chain.G 0).batchEnc U_int) hdPos
    have hStTot : stLG.totalRuntime = model.chain.totalRuntime := rfl
    rw [← hNextEq, hStTot] at h; exact h
  have hScInit : ∀ j < d, 3 * (modelPre.chain.G j).m *
      SparseCore.bundleLogFactor (modelPre.chain.lvlM j) modelPre.chain.N₀ ≤
      cfg.T.cost (modelPre.chain.scState j) := by
    intro j hj
    have hCoreAt := (ordRebuildSuffix_prefix_and_coreAt cfg.T cfg.L cfg.P stLG.lvlM stLG.N₀
      stLG.ℓ stLG.g d 0 (by omega) (fun r => if r = 0 then G0'.compact else stLG.G r)
      stLG.scState stLG.bran stLG.updCount stLG.curEnc stLG.curDecUpdates stLG.curFwd).2.2 j
      (Nat.zero_le _) (by omega)
    dsimp only at hCoreAt
    have hscj : ∃ ℓj gj ordj, modelPre.chain.scState j = cfg.T.initOrd cfg.P.k
        (modelPre.chain.lvlM j) modelPre.chain.N₀ (modelPre.chain.G j) ℓj gj ordj := by
      rw [hNextEq]
      simp only [Chain.Ordered.algorithm1_rebuild, show 0 < cfg.P.d from hdPos, ↓reduceDIte, Nat.sub_zero]
      exact ⟨_, _, _, hCoreAt.1⟩
    obtain ⟨ℓj, gj, ordj, hscj⟩ := hscj
    rw [hscj]
    exact hInitLower (hValid j (le_of_lt hj)).2
  have hc0Ge : (modelPre.chain.G 0).m ≤ cfg.T.cost (modelPre.chain.scState 0) := by
    have h1 := hScInit 0 hdPos
    have hB1 : 1 ≤ SparseCore.bundleLogFactor (modelPre.chain.lvlM 0) modelPre.chain.N₀ := one_le_bLog _ _
    have h2 : 3 * (modelPre.chain.G 0).m ≤ cfg.T.cost (modelPre.chain.scState 0) :=
      (Nat.le_mul_of_pos_right _ (by omega : 0 < SparseCore.bundleLogFactor _ _)).trans h1
    omega
  have hc0LeSum : cfg.T.cost (modelPre.chain.scState 0) ≤
      (Finset.range d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) :=
    Finset.single_le_sum (f := fun j => cfg.T.cost (modelPre.chain.scState j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hdPos)
  -- Bound suffix forest sums by `(d + 1) * mNew`
  set mNew := (modelPre.chain.G 0).m
  have hSumOld : graphListEdgeSum (chainSuffixForests model.chain 0) ≤ (d + 1) * mNew := by
    have h := graphListEdgeSum_chainSuffixForests_le (Nat.zero_le d)
      (fun j _ hj => ⟨(hSub j hj).2.1, (hSub j hj).2.2.1⟩) hLastOld
    rwa [hG0m, ← hmNewEq] at h
  have hSumNew : graphListEdgeSum (chainSuffixForests modelPre.chain 0) ≤ (d + 1) * mNew :=
    graphListEdgeSum_chainSuffixForests_le (Nat.zero_le d)
      (fun j _ hj => ⟨(hSub j hj).2.2.2.1, (hSub j hj).2.2.2.2⟩) hLastNew
  -- Bound level rebuild sum
  set perFixed := 5 * Psc.mul + 4 * Psc.mul * B₀ + 2 * Psc.readout + 475
  set lvlMul := 5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 320
  have hLevelSum :
      (Finset.range d).sum (fun j => updateCoreRebuildLevelCost L capExp cfg Psc modelPre.chain j + 9) ≤
        d * perFixed + lvlMul * (Finset.range d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) := by
    calc (Finset.range d).sum (fun j => updateCoreRebuildLevelCost L capExp cfg Psc modelPre.chain j + 9)
        ≤ (Finset.range d).sum (fun j => perFixed + lvlMul * cfg.T.cost (modelPre.chain.scState j)) :=
          Finset.sum_le_sum fun j hj =>
            rebuildLevel_cost_le hTP hγk (Finset.mem_range.mp hj) hLvlN
              (hSub j (Finset.mem_range.mp hj)).2.2.2.2 (hScInit j (Finset.mem_range.mp hj))
      _ = d * perFixed + lvlMul * (Finset.range d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
            ← Finset.mul_sum]
  -- Bound all linear-in-`mNew` terms by `extraMul * c0 + 510 * mThresh + 4000`
  have hIntCapBound : intCap ≤ 4 * mNew + 2 * mThresh + 1 := by
    have h1 := initTargetCap_le_four_m_add hGSup (hGM.symm ▸ hM0Le)
    omega
  set extraMul := 2 * (d + 1) * (wireTreeSyncEditCost L drainUnit + 172) + 17 * L + drainUnit + 3100
  have hLinBound :
      85 * graphListEdgeSum (chainSuffixForests model.chain 0) +
        graphListEdgeSum (chainSuffixForests model.chain 0) * (wireTreeSyncEditCost L drainUnit + 2) +
        (85 * intCap + 40 * m + 110) +
        wireCompactLevel0Cost model.extG.n rootECap intCap L mNew +
        (150 * rootECap + 60 * model.extG.n + 120) +
        85 * graphListEdgeSum (chainSuffixForests modelPre.chain 0) +
        graphListEdgeSum (chainSuffixForests modelPre.chain 0) * (wireTreeSyncEditCost L drainUnit + 2) +
        (80 * mNew + mNew * drainUnit + 120) ≤
      extraMul * cfg.T.cost (modelPre.chain.scState 0) + 510 * mThresh + 4000 := by
    unfold wireCompactLevel0Cost
    have hS1 : graphListEdgeSum (chainSuffixForests model.chain 0) * (wireTreeSyncEditCost L drainUnit + 2) ≤
        (d + 1) * (wireTreeSyncEditCost L drainUnit + 2) * mNew := by
      calc graphListEdgeSum (chainSuffixForests model.chain 0) * (wireTreeSyncEditCost L drainUnit + 2)
          ≤ ((d + 1) * mNew) * (wireTreeSyncEditCost L drainUnit + 2) := Nat.mul_le_mul_right _ hSumOld
        _ = (d + 1) * (wireTreeSyncEditCost L drainUnit + 2) * mNew := by ring
    have hS1' : graphListEdgeSum (chainSuffixForests modelPre.chain 0) * (wireTreeSyncEditCost L drainUnit + 2) ≤
        (d + 1) * (wireTreeSyncEditCost L drainUnit + 2) * mNew := by
      calc graphListEdgeSum (chainSuffixForests modelPre.chain 0) * (wireTreeSyncEditCost L drainUnit + 2)
          ≤ ((d + 1) * mNew) * (wireTreeSyncEditCost L drainUnit + 2) := Nat.mul_le_mul_right _ hSumNew
        _ = (d + 1) * (wireTreeSyncEditCost L drainUnit + 2) * mNew := by ring
    have hS2 : 85 * graphListEdgeSum (chainSuffixForests model.chain 0) +
        85 * graphListEdgeSum (chainSuffixForests modelPre.chain 0) ≤ 340 * (d + 1) * mNew := by
      have h1 : 85 * ((d + 1) * mNew) + 85 * ((d + 1) * mNew) = 170 * ((d + 1) * mNew) := by ring
      have h1' : 340 * (d + 1) * mNew = 340 * ((d + 1) * mNew) := by ring
      have h2 := Nat.mul_le_mul_left 85 hSumOld
      have h3 := Nat.mul_le_mul_left 85 hSumNew
      omega
    have hMLe : extraMul * mNew ≤ extraMul * cfg.T.cost (modelPre.chain.scState 0) :=
      Nat.mul_le_mul_left extraMul hc0Ge
    have hProd1 : mNew * (17 * L + 1300) = (17 * L) * mNew + 1300 * mNew := by ring
    have hProd2 : mNew * drainUnit = drainUnit * mNew := Nat.mul_comm _ _
    have hProd3 : extraMul * mNew =
        2 * (d + 1) * (wireTreeSyncEditCost L drainUnit + 2) * mNew + 340 * (d + 1) * mNew +
          (17 * L) * mNew + drainUnit * mNew + 3100 * mNew := by
      dsimp only [extraMul]; ring
    have hProd4 : 2 * (d + 1) * (wireTreeSyncEditCost L drainUnit + 2) * mNew =
        (d + 1) * (wireTreeSyncEditCost L drainUnit + 2) * mNew +
        (d + 1) * (wireTreeSyncEditCost L drainUnit + 2) * mNew := by ring
    omega
  -- Combine into `tMul * Δ totalRuntime`
  have htLast : lastMul ≤ tMul := le_max_left _ _
  have htA : extraMul + lvlMul ≤ tMul :=
    le_trans le_rfl (le_trans (le_max_left _ _) (le_max_right _ _))
  have hToolPart :
      extraMul * cfg.T.cost (modelPre.chain.scState 0) +
        lvlMul * (Finset.range d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) +
        lastMul * cfg.L.cost (modelPre.chain.G d) ≤
      tMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) := by
    have h1 : extraMul * cfg.T.cost (modelPre.chain.scState 0) ≤
        extraMul * (Finset.range d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) :=
      Nat.mul_le_mul_left extraMul hc0LeSum
    have h2 : (extraMul + lvlMul) * (Finset.range d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) ≤
        tMul * (Finset.range d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) :=
      Nat.mul_le_mul_right _ htA
    have h3 : lastMul * cfg.L.cost (modelPre.chain.G d) ≤ tMul * cfg.L.cost (modelPre.chain.G d) :=
      Nat.mul_le_mul_right _ htLast
    have h4 : tMul * ((Finset.range d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) +
        cfg.L.cost (modelPre.chain.G d)) ≤
        tMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) :=
      Nat.mul_le_mul_left tMul hDelta
    rw [Nat.mul_add] at h4
    have h5 : (extraMul + lvlMul) * (Finset.range d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) =
        extraMul * (Finset.range d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) +
        lvlMul * (Finset.range d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) := by ring
    omega
  -- Combine fixed part
  have hUpart :
      U.length * (wireRefreshOneCost L + 120) + 670 * (4 * U.length + 1) + U.length * (17 * L + 70) ≤
      U.length * (wireRefreshOneCost L + wireTreeSyncEditCost L drainUnit + 17 * L + drainUnit + 3000) + 670 := by
    have h1 : U.length * (wireRefreshOneCost L + 120) + 670 * (4 * U.length + 1) + U.length * (17 * L + 70) =
        U.length * (wireRefreshOneCost L + 17 * L + 2870) + 670 := by ring
    have h2 : U.length * (wireRefreshOneCost L + 17 * L + 2870) ≤
        U.length * (wireRefreshOneCost L + wireTreeSyncEditCost L drainUnit + 17 * L + drainUnit + 3000) :=
      Nat.mul_le_mul_left U.length (Nat.le_of_lt (by linarith [Nat.zero_le (wireTreeSyncEditCost L drainUnit), Nat.zero_le drainUnit]))
    linarith
  have hFixLe :
      d * (Psc.readout + 48) + 230 * (d + 1) + 300 +
        U.length * (wireRefreshOneCost L + wireTreeSyncEditCost L drainUnit + 17 * L + drainUnit + 3000) + 670 +
        71 * L + 220 + 30 + 80 + 150 + d * perFixed + lastMul +
        d * (Psc.readout + 48) + 40 * d + 230 * (d + 1) + 260 + 1500 + 510 * mThresh + 4000 ≤
      updateCoreFixedBound L capExp drainUnit edMul lastMul mThresh Psc cfg.P.k d M₀ Md cfg.N₀ U.length := by
    unfold updateCoreFixedBound
    dsimp only [perFixed, M₀, Md, B₀, LwMax₀, d]
    have hU : U.length * (wireRefreshOneCost L + wireTreeSyncEditCost L drainUnit + 17 * L + drainUnit + 3000) ≤
        U.length * (wireRefreshOneCost L + wireTreeSyncEditCost L drainUnit + 17 * L + drainUnit + 3200 +
          14 * (cfg.P.d * updateCoreStepRatio edMul (levelM cfg.TP cfg.P 0) cfg.N₀ ^ cfg.P.d *
            (Psc.mul * (cfg.P.k + 1) * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ + 730) +
            (670 + 155 * (cfg.P.d + 1)) * updateCoreStepRatio edMul (levelM cfg.TP cfg.P 0) cfg.N₀ ^ cfg.P.d)) :=
      Nat.mul_le_mul_left U.length (Nat.le_trans (Nat.add_le_add_left (by norm_num : 3000 ≤ 3200) _) (Nat.le_add_right _ _))
    have hD : cfg.P.d * (Psc.readout + 48) + cfg.P.d * (5 * Psc.mul + 4 * Psc.mul *
          SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ + 2 * Psc.readout + 475) +
        cfg.P.d * (Psc.readout + 48) + 40 * cfg.P.d ≤
        cfg.P.d * (5 * Psc.mul + 4 * Psc.mul *
          SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ + 5 * Psc.readout + 2000) := by
      have h1 : cfg.P.d * (Psc.readout + 48) + cfg.P.d * (5 * Psc.mul + 4 * Psc.mul *
            SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ + 2 * Psc.readout + 475) +
          cfg.P.d * (Psc.readout + 48) + 40 * cfg.P.d =
          cfg.P.d * (5 * Psc.mul + 4 * Psc.mul *
            SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ + 4 * Psc.readout + 611) := by ring
      rw [h1]
      exact Nat.mul_le_mul_left cfg.P.d (by linarith [Nat.zero_le Psc.readout])
    have hZ1 : 0 ≤ 3 * (cfg.P.d * updateCoreStepRatio edMul (levelM cfg.TP cfg.P 0) cfg.N₀ ^ cfg.P.d *
        (Psc.mul * (cfg.P.k + 1) * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ + 730) +
        (670 + 155 * (cfg.P.d + 1)) * updateCoreStepRatio edMul (levelM cfg.TP cfg.P 0) cfg.N₀ ^ cfg.P.d) :=
      Nat.zero_le _
    have hZ2 : 0 ≤ 4 * Psc.mul * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ := Nat.zero_le _
    have hZ3 : 0 ≤ levelM cfg.TP cfg.P cfg.P.d *
        (wireCoreLenEdgeCost (ordLevelLwMax L capExp (levelM cfg.TP cfg.P 0) cfg.N₀) + 30) := Nat.zero_le _
    have hZ4 : 0 ≤ Psc.mul * (4 * levelM cfg.TP cfg.P cfg.P.d + 4) *
        SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ := Nat.zero_le _
    linarith [hU, hD, hZ1, hZ2, hZ3, hZ4]
  have hLastExp : lastMul * (cfg.L.cost (modelPre.chain.G d) + 1) =
      lastMul * cfg.L.cost (modelPre.chain.G d) + lastMul := by ring
  linarith


/-- Concrete specialization of `updateCore_costTotalBranchA` to `sparseCoreBundleRestartToolMachWith`. -/
theorem updateCore_costTotalBranchA_mach
    (lsfInit : LSFInit) (C_lsst : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (L capExp drainUnit edMul lastMul mThresh m : ℕ) (cfg : Alg2Config) (G : MGraph)
    (Psc : SparseCoreOrdParams)
    (hT : cfg.T = sparseCoreBundleRestartToolMachWith lsfInit C_lsst depth sparsify params spanConst)
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ) (intCap rootECap : ℕ)
    (hdPos : 0 < cfg.P.d)
    (hOver0 :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      intRebuildThreshold cfg.P model.chain.N₀ 0 < model.chain.updCount 0 + tr.2.2.2.2.length)
    (hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh)
    (hRef : RefreshBatch model.extG U)
    (hModelK : UpdateCoreModelInvKFBL model U gVec lVec)
    (hExtM : model.extG.m = m)
    (hRLeI : rootECap ≤ intCap)
    (hIntLe : intCap ≤ initTargetCap cfg G)
    (hGSup : G.E.sup id ≤ G.m)
    (hGM : G.m = m)
    (hM0Le : cfg.P.M₀ ≤ m + mThresh) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let n := model.extG.n
    let mNew := (modelPre.chain.G 0).m
    let sumOld := graphListEdgeSum (chainSuffixForests model.chain 0)
    let sumNew := graphListEdgeSum (chainSuffixForests modelPre.chain 0)
    let M₀ := levelM cfg.TP cfg.P 0
    let Md := levelM cfg.TP cfg.P cfg.P.d
    cfg.P.d * (Psc.readout + 48) +
      (230 * (cfg.P.d + 1) + 85 * sumOld + 300) +
      sumOld * (wireTreeSyncEditCost L drainUnit + 2) +
      (U.length * (wireRefreshOneCost L + 120) + 71 * L + 220) +
      (670 * (4 * U.length + 1) + 30) +
      (U.length * (17 * L + 70) + 80) +
      (85 * intCap + 40 * m + 110) +
      wireCompactLevel0Cost n rootECap intCap L mNew +
      (150 * rootECap + 60 * n + 120) + 150 +
      (Finset.range cfg.P.d).sum (fun j => updateCoreRebuildLevelCost L capExp cfg Psc modelPre.chain j + 9) +
      lastMul * (cfg.L.cost (modelPre.chain.G cfg.P.d) + 1) +
      cfg.P.d * (Psc.readout + 48) + 40 * cfg.P.d +
      (230 * (cfg.P.d + 1) + 85 * sumNew + 260) +
      sumNew * (wireTreeSyncEditCost L drainUnit + 2) +
      (80 * mNew + mNew * drainUnit + 120) + 1500 ≤
      updateCoreFixedBound L capExp drainUnit edMul lastMul mThresh Psc cfg.P.k cfg.P.d M₀ Md cfg.N₀ U.length +
        updateCoreToolMulBound L capExp drainUnit edMul lastMul Psc cfg.P.k cfg.P.d M₀ cfg.N₀ *
          (modelPre.chain.totalRuntime - model.chain.totalRuntime) := by
  refine updateCore_costTotalBranchA L capExp drainUnit edMul lastMul mThresh m cfg G Psc hTP hγk
    (fun hG => ?_) model U gVec lVec intCap rootECap hdPos hOver0 hFresh hRef hModelK hExtM hRLeI
    hIntLe hGSup hGM hM0Le
  cases cfg with | mk T L_t TP LP P σ_mwu N₀ α Ψ ε =>
    dsimp only at hT ⊢; subst hT
    exact sparseCoreBundleRestartToolMachWith_init_lower lsfInit C_lsst depth sparsify params
      spanConst P.hk hG


end MinCostFlow.MinRatio
