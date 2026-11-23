module

public import MinCostFlow.MinRatio.WireChainCoreCostBaseKFBL
import Mathlib.Tactic

/-!
# Chain-update core Branch B live cost discharge under `KFBL` (`WireChainCoreCostKFBL`)

Discharges all three cases of `UpdateCoreOpsHypKFBL.costTotalBranchB` with `updateCoreFixedBound`
and `updateCoreToolMulBound` (`WireChainCoreCostBaseKFBL.lean`), both for general tools satisfying
`hInitLower` (`updateCore_costTotalBranchB`) and concretely for
`sparseCoreBundleRestartToolMachWith` (`updateCore_costTotalBranchB_mach`).
-/

public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered
open MinCostFlow.DynSpanner MinCostFlow.SparseCore MinCostFlow.SparseCore.Program

set_option maxHeartbeats 1200000 in
/-- Discharges all three cases of `UpdateCoreOpsHypKFBL.costTotalBranchB` with
`updateCoreFixedBound` and `updateCoreToolMulBound` for any tool meeting `hInitLower`. -/
theorem updateCore_costTotalBranchB
    (L capExp drainUnit edMul lastMul mThresh : ℕ) (cfg : Alg2Config) (Psc : SparseCoreOrdParams)
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (hInitLower : ∀ {M N : ℕ} {G : MGraph} {ℓ g : ℕ → ℝ} {ord : ℕ → List End},
      G.IsValid →
      3 * G.m * SparseCore.bundleLogFactor M N ≤ cfg.T.cost (cfg.T.initOrd cfg.P.k M N G ℓ g ord))
    (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ)
    (bW eW nextULen Δc : ℕ → ℕ) (i₀ : ℕ)
    (hdPos : 0 < cfg.P.d) (hiLe : i₀ ≤ cfg.P.d)
    (hModelK : UpdateCoreModelInvKFBL model U gVec lVec)
    (hb0 : bW 0 ≤ 4 * U.length + 1) (he0 : eW 0 ≤ 10 * U.length + 1)
    (hStep : ∀ j < i₀, nextULen j ≤ Δc j ∧ bW (j + 1) ≤ 6 * Δc j + 1 ∧
      eW (j + 1) ≤ edMul * (Δc j + (bW j + eW j + 1) *
        SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀)) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let d := cfg.P.d
    let M₀ := levelM cfg.TP cfg.P 0
    let Md := levelM cfg.TP cfg.P d
    let B₀ := SparseCore.bundleLogFactor M₀ cfg.N₀
    let LwMax₀ := ordLevelLwMax L capExp M₀ cfg.N₀
    let prefixCost :=
      (134 * U.length + 65) + U.length * (wireTreeSyncEditCost L drainUnit + 2) +
      (U.length * (wireRefreshOneCost L + 120) + 71 * L + 220) +
      (670 * (4 * U.length + 1) + 30) +
      (U.length * (17 * L + 70) + 80) +
      (Finset.range i₀).sum (fun j =>
        updateCoreNoRebuildStepCost L capExp Psc cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀
          (bW j) (eW j) (nextULen j) (Δc j) + 30) +
      (130 * U.length + U.length * drainUnit + 100) + 100 * d + 1000
    let rhs :=
      updateCoreFixedBound L capExp drainUnit edMul lastMul mThresh Psc cfg.P.k d M₀ Md cfg.N₀ U.length +
        updateCoreToolMulBound L capExp drainUnit edMul lastMul Psc cfg.P.k d M₀ cfg.N₀ *
          (modelPre.chain.totalRuntime - model.chain.totalRuntime)
    ((0 < i₀ → i₀ < d →
      (∀ j, i₀ ≤ j → j < d → ∃ ℓj gj ordj,
        modelPre.chain.scState j =
          cfg.T.initOrd cfg.P.k (modelPre.chain.lvlM j) modelPre.chain.N₀ (modelPre.chain.G j) ℓj gj ordj) →
      (Finset.range i₀).sum Δc +
        (Finset.Ico i₀ d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) +
        cfg.L.cost (modelPre.chain.G d) ≤
        modelPre.chain.totalRuntime - model.chain.totalRuntime →
      (model.chain.G i₀).m ≤ (modelPre.chain.G i₀).m + bW i₀ →
      let sumOldSuf := graphListEdgeSum (chainSuffixForests model.chain i₀)
      let sumNewSuf := graphListEdgeSum (chainSuffixForests modelPre.chain i₀)
      prefixCost +
        670 * bW i₀ +
        Psc.mul * (2 * (modelPre.chain.G i₀).n + 2 * (modelPre.chain.G i₀).m + 2) * B₀ +
        2 * Psc.readout + 200 +
        (Finset.Ico i₀ d).sum (fun j => updateCoreRebuildLevelCost L capExp cfg Psc modelPre.chain j + 9) +
        lastMul * (cfg.L.cost (modelPre.chain.G d) + 1) +
        2 * d * (Psc.readout + 68) +
        (230 * (d + 1) + 85 * (sumOldSuf + sumNewSuf) + 260) +
        70 * (sumOldSuf + sumNewSuf) + 300 ≤ rhs) ∧
     (i₀ = d →
      (Finset.range d).sum Δc + cfg.L.cost (modelPre.chain.G d) ≤
        modelPre.chain.totalRuntime - model.chain.totalRuntime →
      let Gd := modelPre.chain.G d
      let oldLastF := (model.chain.lastLSFs model.chain.lastBran).F.F
      let newLastF := (modelPre.chain.lastLSFs modelPre.chain.lastBran).F.F
      prefixCost +
        3 * Psc.readout + copyGraphLiveCost Gd.n Gd.m +
        Gd.m * (wireCoreLenEdgeCost LwMax₀ + 30) +
        Psc.mul * (2 * Gd.n + 2 * Gd.m + 2) * B₀ +
        lastMul * (cfg.L.cost Gd + 1) +
        (230 * 2 + 85 * (oldLastF.m + newLastF.m) + 260) +
        70 * (oldLastF.m + newLastF.m) + 400 ≤ rhs) ∧
     (i₀ = d →
      (Finset.range d).sum Δc ≤ modelPre.chain.totalRuntime - model.chain.totalRuntime →
      prefixCost + 600 ≤ rhs)) := by
  dsimp only
  set d := cfg.P.d
  set M₀ := levelM cfg.TP cfg.P 0
  set Md := levelM cfg.TP cfg.P d
  set B₀ := SparseCore.bundleLogFactor M₀ cfg.N₀
  set LwMax₀ := ordLevelLwMax L capExp M₀ cfg.N₀
  set R := updateCoreStepRatio edMul M₀ cfg.N₀
  set stepMul := Psc.mul * (cfg.P.k + 1) * B₀ + 730
  set tMul := updateCoreToolMulBound L capExp drainUnit edMul lastMul Psc cfg.P.k d M₀ cfg.N₀
  set modelPre := alg2PreResetState cfg model U gVec lVec
  set SΔ := (Finset.range i₀).sum Δc
  rcases hModelK with ⟨hLvl0, hLvlN, hValid, _, _, hSub, hLastOld, hLastNew, hOldGdm, hNewGdm, _, _, _⟩
  have hB1 : 1 ≤ B₀ := one_le_bLog _ _
  have hStepBW : ∀ j < i₀, bW (j + 1) ≤ 6 * Δc j + 1 ∧
      eW (j + 1) ≤ edMul * (Δc j + (bW j + eW j + 1) * B₀) := fun j hj =>
    ⟨(hStep j hj).2.1, (hStep j hj).2.2⟩
  have hWordsSum : (Finset.range i₀).sum (fun j => bW j + eW j + 1) ≤
      d * R ^ d * (14 * U.length + 3 + SΔ) :=
    branchB_words_sum_le hB1 hiLe hb0 he0 hStepBW
  have hBi0 : bW i₀ ≤ R ^ d * (14 * U.length + 3 + SΔ) := by
    have h1 : bW i₀ + eW i₀ + 1 ≤ R ^ i₀ * (14 * U.length + 3 + SΔ) :=
      branchB_words_geom_bound hB1 hb0 he0 hStepBW i₀ le_rfl
    have hRpow : R ^ i₀ ≤ R ^ d := Nat.pow_le_pow_right (by dsimp [R, updateCoreStepRatio]; omega) hiLe
    have h2 : R ^ i₀ * (14 * U.length + 3 + SΔ) ≤ R ^ d * (14 * U.length + 3 + SΔ) :=
      Nat.mul_le_mul_right _ hRpow
    omega
  -- Bound the non-rebuilt prefix loop sum
  have hStepSum :
      (Finset.range i₀).sum (fun j =>
        updateCoreNoRebuildStepCost L capExp Psc cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀
          (bW j) (eW j) (nextULen j) (Δc j) + 30) ≤
      (Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120 + d * R ^ d * stepMul) * SΔ +
        (d * R ^ d * stepMul) * (14 * U.length + 3) + d * (Psc.readout + 940) := by
    have hEach : ∀ j ∈ Finset.range i₀,
        updateCoreNoRebuildStepCost L capExp Psc cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀
          (bW j) (eW j) (nextULen j) (Δc j) + 30 ≤
        (Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120) * Δc j +
          stepMul * (bW j + eW j + 1) + (Psc.readout + 940) := by
      intro j hj
      have hjLt := Finset.mem_range.mp hj
      have hMj := levelM_le_levelM_zero hTP hγk j
      have hBj : SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀ ≤ B₀ := bLog_mono hMj
      have hLwj : wireCoreLenEdgeCost (ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀) ≤
          wireCoreLenEdgeCost LwMax₀ := coreLenEdgeCost_mono (lwMax_mono hMj)
      have hT1 : Psc.mul * ((cfg.P.k + 1) * (bW j + eW j + 1) *
            SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) ≤
          Psc.mul * (cfg.P.k + 1) * B₀ * (bW j + eW j + 1) := by
        have h1 : (cfg.P.k + 1) * (bW j + eW j + 1) *
              SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀ ≤
            (cfg.P.k + 1) * (bW j + eW j + 1) * B₀ := Nat.mul_le_mul_left _ hBj
        have h2 := Nat.mul_le_mul_left Psc.mul h1
        have h3 : Psc.mul * ((cfg.P.k + 1) * (bW j + eW j + 1) * B₀) =
            Psc.mul * (cfg.P.k + 1) * B₀ * (bW j + eW j + 1) := by ring
        omega
      have hT2 : 730 * bW j ≤ 730 * (bW j + eW j + 1) := Nat.mul_le_mul_left 730 (by omega)
      have hT3 : nextULen j * (wireCoreLenEdgeCost (ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀) + 120) ≤
          (wireCoreLenEdgeCost LwMax₀ + 120) * Δc j := by
        calc nextULen j * (wireCoreLenEdgeCost (ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀) + 120)
            ≤ Δc j * (wireCoreLenEdgeCost LwMax₀ + 120) :=
              Nat.mul_le_mul (hStep j hjLt).1 (by omega)
          _ = (wireCoreLenEdgeCost LwMax₀ + 120) * Δc j := Nat.mul_comm _ _
      unfold updateCoreNoRebuildStepCost
      dsimp only
      have hExp1 : Psc.mul * (Δc j + (cfg.P.k + 1) * (bW j + eW j + 1) *
            SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) =
          Psc.mul * Δc j + Psc.mul * ((cfg.P.k + 1) * (bW j + eW j + 1) *
            SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀) := by ring
      have hExp2 : (Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120) * Δc j =
          Psc.mul * Δc j + (wireCoreLenEdgeCost LwMax₀ + 120) * Δc j := by ring
      have hExp3 : stepMul * (bW j + eW j + 1) =
          Psc.mul * (cfg.P.k + 1) * B₀ * (bW j + eW j + 1) + 730 * (bW j + eW j + 1) := by
        dsimp only [stepMul]; ring
      omega
    have hS1 := Finset.sum_le_sum hEach
    rw [Finset.sum_add_distrib (s := Finset.range i₀)
          (f := fun j => (Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120) * Δc j + stepMul * (bW j + eW j + 1)),
        Finset.sum_add_distrib (s := Finset.range i₀)
          (f := fun j => (Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120) * Δc j),
        ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, smul_eq_mul] at hS1
    have hSΔDef : (Finset.range i₀).sum Δc = SΔ := rfl
    rw [hSΔDef] at hS1
    have hS2 : stepMul * (Finset.range i₀).sum (fun j => bW j + eW j + 1) ≤
        stepMul * (d * R ^ d * (14 * U.length + 3 + SΔ)) := Nat.mul_le_mul_left stepMul hWordsSum
    have hS3 : i₀ * (Psc.readout + 940) ≤ d * (Psc.readout + 940) := Nat.mul_le_mul_right _ hiLe
    have hExp : stepMul * (d * R ^ d * (14 * U.length + 3 + SΔ)) =
        (d * R ^ d * stepMul) * SΔ + (d * R ^ d * stepMul) * (14 * U.length + 3) := by ring
    have hExp2 : (Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120 + d * R ^ d * stepMul) * SΔ =
        (Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120) * SΔ + (d * R ^ d * stepMul) * SΔ := by ring
    omega
  -- Bound U-linear terms of `prefixCost`
  have hPrefixBase :
      (134 * U.length + 65) + U.length * (wireTreeSyncEditCost L drainUnit + 2) +
        (U.length * (wireRefreshOneCost L + 120) + 71 * L + 220) +
        (670 * (4 * U.length + 1) + 30) +
        (U.length * (17 * L + 70) + 80) +
        (130 * U.length + U.length * drainUnit + 100) + 100 * d + 1000 ≤
      U.length * (wireRefreshOneCost L + wireTreeSyncEditCost L drainUnit + 17 * L + drainUnit + 3200) +
        71 * L + 100 * d + 2200 := by
    have h1 : (134 * U.length + 65) + U.length * (wireTreeSyncEditCost L drainUnit + 2) +
        (U.length * (wireRefreshOneCost L + 120) + 71 * L + 220) +
        (670 * (4 * U.length + 1) + 30) +
        (U.length * (17 * L + 70) + 80) +
        (130 * U.length + U.length * drainUnit + 100) + 100 * d + 1000 =
        U.length * (wireRefreshOneCost L + wireTreeSyncEditCost L drainUnit + 17 * L + drainUnit + 3136) +
          71 * L + 100 * d + 2165 := by ring
    have h2 : U.length * (wireRefreshOneCost L + wireTreeSyncEditCost L drainUnit + 17 * L + drainUnit + 3136) ≤
        U.length * (wireRefreshOneCost L + wireTreeSyncEditCost L drainUnit + 17 * L + drainUnit + 3200) :=
      Nat.mul_le_mul_left U.length (by omega)
    omega
  -- Common `tMul` lower bounds for Branch B
  set prefToolMul := Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120 +
    (d * R ^ d * stepMul + (670 + 155 * (d + 1)) * R ^ d)
  set sufLvlMul := 5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 320
  have htPref : prefToolMul ≤ tMul := by
    dsimp only [tMul, updateCoreToolMulBound, prefToolMul, stepMul, R, M₀, B₀, LwMax₀, d]
    exact le_trans (by omega) (le_trans (le_max_right _ _) (le_max_right _ _))
  have htSuf : sufLvlMul + 4 * Psc.mul * B₀ + 310 * (d + 1) ≤ tMul := by
    dsimp only [tMul, updateCoreToolMulBound, sufLvlMul, B₀, d]
    refine le_trans ?_ (le_trans (le_max_right _ _) (le_max_right _ _))
    linarith [Nat.zero_le (cfg.P.d * updateCoreStepRatio edMul (levelM cfg.TP cfg.P 0) cfg.N₀ ^ cfg.P.d *
        (Psc.mul * (cfg.P.k + 1) * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ + 730) +
        (670 + 155 * (cfg.P.d + 1)) * updateCoreStepRatio edMul (levelM cfg.TP cfg.P 0) cfg.N₀ ^ cfg.P.d)]
  have htLast : lastMul ≤ tMul := le_max_left _ _
  set extraU := d * R ^ d * stepMul + (670 + 155 * (d + 1)) * R ^ d
  have hFixEq :
      U.length * (wireRefreshOneCost L + wireTreeSyncEditCost L drainUnit + 17 * L + drainUnit + 3200) +
        extraU * (14 * U.length + 3) =
      U.length * (wireRefreshOneCost L + wireTreeSyncEditCost L drainUnit + 17 * L + drainUnit + 3200 +
        14 * extraU) + 3 * extraU := by ring
  refine ⟨?_, ?_, ?_⟩
  · -- Case 1: Interior rebuild at `0 < i₀ < d`
    intro hi0Pos hi0Lt hScInit hDelta hOldGm
    set Gi0 := modelPre.chain.G i₀
    set ci0 := cfg.T.cost (modelPre.chain.scState i₀)
    have hInitJ : ∀ j, i₀ ≤ j → j < d →
        3 * (modelPre.chain.G j).m * SparseCore.bundleLogFactor (modelPre.chain.lvlM j) modelPre.chain.N₀ ≤
          cfg.T.cost (modelPre.chain.scState j) := by
      intro j hj1 hj2
      obtain ⟨ℓj, gj, ordj, hscj⟩ := hScInit j hj1 hj2
      rw [hscj]; exact hInitLower (hValid j (le_of_lt hj2)).2
    have hci0Ge : 3 * Gi0.m * SparseCore.bundleLogFactor (modelPre.chain.lvlM i₀) modelPre.chain.N₀ ≤ ci0 :=
      hInitJ i₀ le_rfl hi0Lt
    have hBi0_1 : 1 ≤ SparseCore.bundleLogFactor (modelPre.chain.lvlM i₀) modelPre.chain.N₀ := one_le_bLog _ _
    have hGi0m : Gi0.m ≤ ci0 := by
      have h1 : 3 * Gi0.m ≤ ci0 :=
        (Nat.le_mul_of_pos_right _ (by omega : 0 < SparseCore.bundleLogFactor _ _)).trans hci0Ge
      omega
    have hci0LeSum : ci0 ≤ (Finset.Ico i₀ d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) :=
      Finset.single_le_sum (f := fun j => cfg.T.cost (modelPre.chain.scState j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_Ico.mpr ⟨le_rfl, hi0Lt⟩)
    -- Bound `Psc.mul * (2 * Gi0.n + 2 * Gi0.m + 2) * B₀`
    have hGi0n : Gi0.n ≤ Gi0.m + 1 := hLvlN.1 i₀ (le_of_lt hi0Lt)
    have hOrdI0 : Psc.mul * (2 * Gi0.n + 2 * Gi0.m + 2) * B₀ ≤
        4 * Psc.mul * B₀ * ci0 + 4 * Psc.mul * B₀ := by
      have h1 : 2 * Gi0.n + 2 * Gi0.m + 2 ≤ 4 * Gi0.m + 4 := by omega
      have h2 := Nat.mul_le_mul_right B₀ (Nat.mul_le_mul_left Psc.mul h1)
      have h3 : Psc.mul * (4 * Gi0.m + 4) * B₀ = 4 * Psc.mul * B₀ * Gi0.m + 4 * Psc.mul * B₀ := by ring
      have h4 : 4 * Psc.mul * B₀ * Gi0.m ≤ 4 * Psc.mul * B₀ * ci0 := Nat.mul_le_mul_left _ hGi0m
      omega
    -- Bound suffix forest edge sums
    have hOldSuf : graphListEdgeSum (chainSuffixForests model.chain i₀) ≤ (d + 1) * (Gi0.m + bW i₀) :=
      (graphListEdgeSum_chainSuffixForests_le (le_of_lt hi0Lt)
        (fun j _ hj => ⟨(hSub j hj).2.1, (hSub j hj).2.2.1⟩) hLastOld).trans
        (Nat.mul_le_mul_left (d + 1) hOldGm)
    have hNewSuf : graphListEdgeSum (chainSuffixForests modelPre.chain i₀) ≤ (d + 1) * Gi0.m :=
      graphListEdgeSum_chainSuffixForests_le (le_of_lt hi0Lt)
        (fun j _ hj => ⟨(hSub j hj).2.2.2.1, (hSub j hj).2.2.2.2⟩) hLastNew
    have hSufForestCost :
        670 * bW i₀ + 85 * (graphListEdgeSum (chainSuffixForests model.chain i₀) +
          graphListEdgeSum (chainSuffixForests modelPre.chain i₀)) +
        70 * (graphListEdgeSum (chainSuffixForests model.chain i₀) +
          graphListEdgeSum (chainSuffixForests modelPre.chain i₀)) ≤
        310 * (d + 1) * ci0 + (670 + 155 * (d + 1)) * R ^ d * (14 * U.length + 3 + SΔ) := by
      have h1 : graphListEdgeSum (chainSuffixForests model.chain i₀) +
          graphListEdgeSum (chainSuffixForests modelPre.chain i₀) ≤
          2 * (d + 1) * Gi0.m + (d + 1) * bW i₀ := by
        have hmul : (d + 1) * (Gi0.m + bW i₀) + (d + 1) * Gi0.m =
            2 * (d + 1) * Gi0.m + (d + 1) * bW i₀ := by ring
        omega
      have h2 := Nat.mul_le_mul_left 155 h1
      have h3 : 155 * (2 * (d + 1) * Gi0.m + (d + 1) * bW i₀) =
          310 * (d + 1) * Gi0.m + 155 * (d + 1) * bW i₀ := by ring
      have h4 : 310 * (d + 1) * Gi0.m ≤ 310 * (d + 1) * ci0 := Nat.mul_le_mul_left _ hGi0m
      have h5 : (670 + 155 * (d + 1)) * bW i₀ ≤
          (670 + 155 * (d + 1)) * (R ^ d * (14 * U.length + 3 + SΔ)) :=
        Nat.mul_le_mul_left _ hBi0
      have h6 : 670 * bW i₀ + 155 * (d + 1) * bW i₀ = (670 + 155 * (d + 1)) * bW i₀ := by ring
      have h7 : (670 + 155 * (d + 1)) * (R ^ d * (14 * U.length + 3 + SΔ)) =
          (670 + 155 * (d + 1)) * R ^ d * (14 * U.length + 3 + SΔ) := by ring
      omega
    -- Bound suffix rebuild level sum
    set perFixed := 5 * Psc.mul + 4 * Psc.mul * B₀ + 2 * Psc.readout + 475
    have hSufLvlSum :
        (Finset.Ico i₀ d).sum (fun j => updateCoreRebuildLevelCost L capExp cfg Psc modelPre.chain j + 9) ≤
          d * perFixed + sufLvlMul * (Finset.Ico i₀ d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) := by
      have hS : (Finset.Ico i₀ d).sum (fun j => updateCoreRebuildLevelCost L capExp cfg Psc modelPre.chain j + 9) ≤
          (Finset.Ico i₀ d).sum (fun j => perFixed + sufLvlMul * cfg.T.cost (modelPre.chain.scState j)) :=
        Finset.sum_le_sum fun j hj => by
          obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
          exact rebuildLevel_cost_le hTP hγk hj2 hLvlN (hSub j hj2).2.2.2.2 (hInitJ j hj1 hj2)
      rw [Finset.sum_add_distrib (s := Finset.Ico i₀ d) (f := fun _ => perFixed),
          Finset.sum_const, Nat.card_Ico, smul_eq_mul, ← Finset.mul_sum] at hS
      have hCard : (d - i₀) * perFixed ≤ d * perFixed := Nat.mul_le_mul_right _ (Nat.sub_le d i₀)
      linarith [hS, hCard]
    -- Combine tool-cost terms
    set SSuf := (Finset.Ico i₀ d).sum (fun j => cfg.T.cost (modelPre.chain.scState j))
    have hToolComb :
        prefToolMul * SΔ + (sufLvlMul + 4 * Psc.mul * B₀ + 310 * (d + 1)) * SSuf +
          lastMul * cfg.L.cost (modelPre.chain.G d) ≤
        tMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) := by
      have h1 := Nat.mul_le_mul_right SΔ htPref
      have h2 := Nat.mul_le_mul_right SSuf htSuf
      have h3 := Nat.mul_le_mul_right (cfg.L.cost (modelPre.chain.G d)) htLast
      have h4 := Nat.mul_le_mul_left tMul hDelta
      rw [Nat.mul_add, Nat.mul_add] at h4
      omega
    have hSufExp :
        sufLvlMul * SSuf + 4 * Psc.mul * B₀ * ci0 + 310 * (d + 1) * ci0 ≤
          (sufLvlMul + 4 * Psc.mul * B₀ + 310 * (d + 1)) * SSuf := by
      have h1 : 4 * Psc.mul * B₀ * ci0 ≤ 4 * Psc.mul * B₀ * SSuf := Nat.mul_le_mul_left _ hci0LeSum
      have h2 : 310 * (d + 1) * ci0 ≤ 310 * (d + 1) * SSuf := Nat.mul_le_mul_left _ hci0LeSum
      have h3 : (sufLvlMul + 4 * Psc.mul * B₀ + 310 * (d + 1)) * SSuf =
          sufLvlMul * SSuf + 4 * Psc.mul * B₀ * SSuf + 310 * (d + 1) * SSuf := by ring
      omega
    have hPrefExp :
        (Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120 + d * R ^ d * stepMul) * SΔ +
          (670 + 155 * (d + 1)) * R ^ d * (14 * U.length + 3 + SΔ) +
          (d * R ^ d * stepMul) * (14 * U.length + 3) =
        prefToolMul * SΔ + extraU * (14 * U.length + 3) := by
      dsimp only [prefToolMul, extraU]; ring
    have hDcomb :
        100 * d + d * (Psc.readout + 940) + d * perFixed + 2 * d * (Psc.readout + 68) ≤
        d * (5 * Psc.mul + 4 * Psc.mul * B₀ + 5 * Psc.readout + 2000) := by
      have h1 : 100 * d + d * (Psc.readout + 940) + d * perFixed + 2 * d * (Psc.readout + 68) =
          d * (5 * Psc.mul + 4 * Psc.mul * B₀ + 5 * Psc.readout + 1651) := by
        dsimp only [perFixed]; ring
      rw [h1]
      exact Nat.mul_le_mul_left d (by linarith [Nat.zero_le Psc.mul, Nat.zero_le (4 * Psc.mul * B₀), Nat.zero_le Psc.readout])
    have hLastExp : lastMul * (cfg.L.cost (modelPre.chain.G d) + 1) =
        lastMul * cfg.L.cost (modelPre.chain.G d) + lastMul := by ring
    have hZ4 : 0 ≤ 2 * Psc.readout + (290 * Md + 240) + Md * (wireCoreLenEdgeCost LwMax₀ + 30) +
        Psc.mul * (4 * Md + 4) * B₀ + 310 * Md + 1200 := Nat.zero_le _
    have hZm : 0 ≤ 510 * mThresh := Nat.zero_le _
    unfold updateCoreFixedBound
    dsimp only [extraU, stepMul, R, M₀, Md, B₀, LwMax₀, d] at hFixEq hDcomb hPrefExp hToolComb hSufExp hSufLvlSum hSufForestCost hOrdI0 hStepSum hPrefixBase hLastExp hZ4 ⊢
    linarith [hFixEq, hDcomb, hPrefExp, hToolComb, hSufExp, hSufLvlSum, hSufForestCost, hOrdI0, hStepSum, hPrefixBase, hLastExp, hZ4, hZm]
  · -- Case 2: Non-empty terminal rebuild at `i₀ = d`
    intro hiEq hDelta
    subst hiEq
    have hSΔEq : SΔ = (Finset.range d).sum Δc := rfl
    rw [← hSΔEq] at hDelta
    set Gd := modelPre.chain.G d
    have hGdn : Gd.n ≤ Md + 1 := (hLvlN.1 d le_rfl).trans (Nat.add_le_add_right hNewGdm 1)
    have hOldFm : (model.chain.lastLSFs model.chain.lastBran).F.F.m ≤ Md :=
      (Finset.card_le_card hLastOld).trans hOldGdm
    have hNewFm : (modelPre.chain.lastLSFs modelPre.chain.lastBran).F.F.m ≤ Md :=
      (Finset.card_le_card hLastNew).trans hNewGdm
    have hCopyGd : copyGraphLiveCost Gd.n Gd.m ≤ 290 * Md + 240 := by
      unfold copyGraphLiveCost; linarith [hGdn, hNewGdm]
    have hLenGd : Gd.m * (wireCoreLenEdgeCost LwMax₀ + 30) ≤
        Md * (wireCoreLenEdgeCost LwMax₀ + 30) := Nat.mul_le_mul_right _ hNewGdm
    have hOrdGd : Psc.mul * (2 * Gd.n + 2 * Gd.m + 2) * B₀ ≤ Psc.mul * (4 * Md + 4) * B₀ :=
      Nat.mul_le_mul_right B₀ (Nat.mul_le_mul_left Psc.mul (by linarith [hGdn, hNewGdm]))
    have hToolComb :
        (Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120 + d * R ^ d * stepMul) * SΔ +
          lastMul * cfg.L.cost Gd ≤
        tMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) := by
      have h1 : Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120 + d * R ^ d * stepMul ≤ tMul := by
        refine le_trans ?_ htPref
        dsimp only [prefToolMul]; rw [← Nat.add_assoc]; exact Nat.le_add_right _ _
      have h2 := Nat.mul_le_mul_right SΔ h1
      have h3 := Nat.mul_le_mul_right (cfg.L.cost Gd) htLast
      have h4 := Nat.mul_le_mul_left tMul hDelta
      rw [Nat.mul_add] at h4
      linarith
    have hExtraLe : (d * R ^ d * stepMul) * (14 * U.length + 3) ≤ extraU * (14 * U.length + 3) :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    have hDcomb : 100 * d + d * (Psc.readout + 940) + Psc.readout ≤
        d * (5 * Psc.mul + 4 * Psc.mul * B₀ + 5 * Psc.readout + 2000) := by
      have hdr : Psc.readout ≤ d * Psc.readout := Nat.le_mul_of_pos_left _ hdPos
      have h1 : 100 * d + d * (Psc.readout + 940) + Psc.readout =
          d * Psc.readout + 1040 * d + Psc.readout := by ring
      have h2 : d * (5 * Psc.mul + 4 * Psc.mul * B₀ + 5 * Psc.readout + 2000) =
          5 * (d * Psc.mul) + 4 * (d * Psc.mul * B₀) + 5 * (d * Psc.readout) + 2000 * d := by
        ring
      rw [h1, h2]
      linarith [Nat.zero_le (d * Psc.mul), Nat.zero_le (d * Psc.mul * B₀)]
    have hLastExp : lastMul * (cfg.L.cost Gd + 1) = lastMul * cfg.L.cost Gd + lastMul := by ring
    have hF2 : 85 * ((model.chain.lastLSFs model.chain.lastBran).F.F.m +
          (modelPre.chain.lastLSFs modelPre.chain.lastBran).F.F.m) +
        70 * ((model.chain.lastLSFs model.chain.lastBran).F.F.m +
          (modelPre.chain.lastLSFs modelPre.chain.lastBran).F.F.m) ≤ 310 * Md := by
      linarith [hOldFm, hNewFm]
    have hZ1 : 0 ≤ 4 * Psc.mul * B₀ := Nat.zero_le _
    have hZ2 : 0 ≤ 2 * Psc.readout := Nat.zero_le _
    have hZ3 : 0 ≤ 600 * (d + 1) := Nat.zero_le _
    have hZm : 0 ≤ 510 * mThresh := Nat.zero_le _
    unfold updateCoreFixedBound
    dsimp only [extraU, stepMul, R, M₀, Md, B₀, LwMax₀, d] at hFixEq hExtraLe hDcomb hToolComb hStepSum hCopyGd hLenGd hOrdGd hF2 hLastExp hZ1 hZ2 hZ3 ⊢
    linarith [hFixEq, hExtraLe, hDcomb, hToolComb, hStepSum, hCopyGd, hLenGd, hOrdGd, hF2, hLastExp, hZ1, hZ2, hZ3, hZm]
  · -- Case 3: Empty terminal step at `i₀ = d`
    intro hiEq hDelta
    subst hiEq
    have hSΔEq : SΔ = (Finset.range d).sum Δc := rfl
    rw [← hSΔEq] at hDelta
    have hToolComb :
        (Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120 + d * R ^ d * stepMul) * SΔ ≤
        tMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) := by
      have h1 : Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120 + d * R ^ d * stepMul ≤ prefToolMul := by
        dsimp only [prefToolMul]; rw [← Nat.add_assoc]; exact Nat.le_add_right _ _
      calc (Psc.mul + wireCoreLenEdgeCost LwMax₀ + 120 + d * R ^ d * stepMul) * SΔ
          ≤ prefToolMul * SΔ := Nat.mul_le_mul_right _ h1
        _ ≤ tMul * SΔ := Nat.mul_le_mul_right _ htPref
        _ ≤ tMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) := Nat.mul_le_mul_left _ hDelta
    have hExtraLe : (d * R ^ d * stepMul) * (14 * U.length + 3) ≤ extraU * (14 * U.length + 3) :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    have hDcomb : 100 * d + d * (Psc.readout + 940) ≤
        d * (5 * Psc.mul + 4 * Psc.mul * B₀ + 5 * Psc.readout + 2000) := by
      have h1 : 100 * d + d * (Psc.readout + 940) = d * (Psc.readout + 1040) := by ring
      rw [h1]
      exact Nat.mul_le_mul_left d (by linarith [Nat.zero_le Psc.mul, Nat.zero_le (4 * Psc.mul * B₀), Nat.zero_le Psc.readout])
    have hZ1 : 0 ≤ 4 * Psc.mul * B₀ := Nat.zero_le _
    have hZ2 : 0 ≤ 2 * Psc.readout := Nat.zero_le _
    have hZ3 : 0 ≤ 600 * (d + 1) := Nat.zero_le _
    have hZ4 : 0 ≤ 2 * Psc.readout + (290 * Md + 240) + Md * (wireCoreLenEdgeCost LwMax₀ + 30) +
        Psc.mul * (4 * Md + 4) * B₀ + lastMul + 310 * Md + 1200 := Nat.zero_le _
    have hZm : 0 ≤ 510 * mThresh := Nat.zero_le _
    unfold updateCoreFixedBound
    dsimp only [extraU, stepMul, R, M₀, Md, B₀, LwMax₀, d] at hFixEq hExtraLe hDcomb hToolComb hStepSum hZ1 hZ2 hZ3 hZ4 ⊢
    linarith [hFixEq, hExtraLe, hDcomb, hToolComb, hStepSum, hZ1, hZ2, hZ3, hZ4, hZm]


/-- Concrete specialization of `updateCore_costTotalBranchB` to `sparseCoreBundleRestartToolMachWith`. -/
theorem updateCore_costTotalBranchB_mach
    (lsfInit : LSFInit) (C_lsst : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (L capExp drainUnit edMul lastMul mThresh : ℕ) (cfg : Alg2Config) (Psc : SparseCoreOrdParams)
    (hT : cfg.T = sparseCoreBundleRestartToolMachWith lsfInit C_lsst depth sparsify params spanConst)
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ)
    (bW eW nextULen Δc : ℕ → ℕ) (i₀ : ℕ)
    (hdPos : 0 < cfg.P.d) (hiLe : i₀ ≤ cfg.P.d)
    (hModelK : UpdateCoreModelInvKFBL model U gVec lVec)
    (hb0 : bW 0 ≤ 4 * U.length + 1) (he0 : eW 0 ≤ 10 * U.length + 1)
    (hStep : ∀ j < i₀, nextULen j ≤ Δc j ∧ bW (j + 1) ≤ 6 * Δc j + 1 ∧
      eW (j + 1) ≤ edMul * (Δc j + (bW j + eW j + 1) *
        SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀)) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let d := cfg.P.d
    let M₀ := levelM cfg.TP cfg.P 0
    let Md := levelM cfg.TP cfg.P d
    let B₀ := SparseCore.bundleLogFactor M₀ cfg.N₀
    let LwMax₀ := ordLevelLwMax L capExp M₀ cfg.N₀
    let prefixCost :=
      (134 * U.length + 65) + U.length * (wireTreeSyncEditCost L drainUnit + 2) +
      (U.length * (wireRefreshOneCost L + 120) + 71 * L + 220) +
      (670 * (4 * U.length + 1) + 30) +
      (U.length * (17 * L + 70) + 80) +
      (Finset.range i₀).sum (fun j =>
        updateCoreNoRebuildStepCost L capExp Psc cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀
          (bW j) (eW j) (nextULen j) (Δc j) + 30) +
      (130 * U.length + U.length * drainUnit + 100) + 100 * d + 1000
    let rhs :=
      updateCoreFixedBound L capExp drainUnit edMul lastMul mThresh Psc cfg.P.k d M₀ Md cfg.N₀ U.length +
        updateCoreToolMulBound L capExp drainUnit edMul lastMul Psc cfg.P.k d M₀ cfg.N₀ *
          (modelPre.chain.totalRuntime - model.chain.totalRuntime)
    ((0 < i₀ → i₀ < d →
      (∀ j, i₀ ≤ j → j < d → ∃ ℓj gj ordj,
        modelPre.chain.scState j =
          cfg.T.initOrd cfg.P.k (modelPre.chain.lvlM j) modelPre.chain.N₀ (modelPre.chain.G j) ℓj gj ordj) →
      (Finset.range i₀).sum Δc +
        (Finset.Ico i₀ d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) +
        cfg.L.cost (modelPre.chain.G d) ≤
        modelPre.chain.totalRuntime - model.chain.totalRuntime →
      (model.chain.G i₀).m ≤ (modelPre.chain.G i₀).m + bW i₀ →
      let sumOldSuf := graphListEdgeSum (chainSuffixForests model.chain i₀)
      let sumNewSuf := graphListEdgeSum (chainSuffixForests modelPre.chain i₀)
      prefixCost +
        670 * bW i₀ +
        Psc.mul * (2 * (modelPre.chain.G i₀).n + 2 * (modelPre.chain.G i₀).m + 2) * B₀ +
        2 * Psc.readout + 200 +
        (Finset.Ico i₀ d).sum (fun j => updateCoreRebuildLevelCost L capExp cfg Psc modelPre.chain j + 9) +
        lastMul * (cfg.L.cost (modelPre.chain.G d) + 1) +
        2 * d * (Psc.readout + 68) +
        (230 * (d + 1) + 85 * (sumOldSuf + sumNewSuf) + 260) +
        70 * (sumOldSuf + sumNewSuf) + 300 ≤ rhs) ∧
     (i₀ = d →
      (Finset.range d).sum Δc + cfg.L.cost (modelPre.chain.G d) ≤
        modelPre.chain.totalRuntime - model.chain.totalRuntime →
      let Gd := modelPre.chain.G d
      let oldLastF := (model.chain.lastLSFs model.chain.lastBran).F.F
      let newLastF := (modelPre.chain.lastLSFs modelPre.chain.lastBran).F.F
      prefixCost +
        3 * Psc.readout + copyGraphLiveCost Gd.n Gd.m +
        Gd.m * (wireCoreLenEdgeCost LwMax₀ + 30) +
        Psc.mul * (2 * Gd.n + 2 * Gd.m + 2) * B₀ +
        lastMul * (cfg.L.cost Gd + 1) +
        (230 * 2 + 85 * (oldLastF.m + newLastF.m) + 260) +
        70 * (oldLastF.m + newLastF.m) + 400 ≤ rhs) ∧
     (i₀ = d →
      (Finset.range d).sum Δc ≤ modelPre.chain.totalRuntime - model.chain.totalRuntime →
      prefixCost + 600 ≤ rhs)) := by
  refine updateCore_costTotalBranchB L capExp drainUnit edMul lastMul mThresh cfg Psc hTP hγk
    (fun hG => ?_) model U gVec lVec bW eW nextULen Δc i₀ hdPos hiLe hModelK hb0 he0 hStep
  cases cfg with | mk T L_t TP LP P σ_mwu N₀ α Ψ ε =>
    dsimp only at hT ⊢; subst hT
    exact sparseCoreBundleRestartToolMachWith_init_lower lsfInit C_lsst depth sparsify params
      spanConst P.hk hG

end MinCostFlow.MinRatio
