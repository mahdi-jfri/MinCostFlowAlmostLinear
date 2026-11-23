module

public import MinCostFlow.MinRatio.WireShiftDeepSpecKFBL
public import MinCostFlow.MinRatio.OrdSolverToolMono
public import MinCostFlow.SparseCore.Program.AssemblyModel
public import MinCostFlow.SparseCore.Program.AssemblyEmpty
public import MinCostFlow.SparseCore.LSFInsertNonTree
import MinCostFlow.MinRatio.WireChainAlgebra
import MinCostFlow.Chain.Ordered.BudgetHelpers
import Mathlib.Tactic

/-!
# Deep-shift live cost discharge and model-invariant bridge (`WireShiftDeepCostKFBL`)

Discharges the `levelCostDom` and `costTotal` fields of `DeepShiftOpsHypKFBL`
(`WireShiftDeepSpecKFBL.lean`) with explicit `deepFixed` (`deepShiftFixedBound`) and `toolMul`
(`deepShiftToolMulBound`) that contain no `m`, `N₀`, `capLimit`, `fcap`, or `forestEdgeCap`
factors outside `bundleLogFactor` and `ordLevelLwMax`:

* `deepShiftLevelCost`: exact per-level live cost bound for `DeepShiftOpsHypKFBL.levelCostDom`.
* `deepShiftFixedBound`: explicit `deepFixed` bound, polynomial in `d`, `Psc.mul`, `Psc.readout`,
  `bundleLogFactor (levelM 0) N₀`, and `lastMul`.
* `deepShiftToolMulBound`: explicit `toolMul` bound, `max lastMul (5 * Psc.mul +
  wireCoreLenEdgeCost (ordLevelLwMax L capExp M₀ N₀) + 170 * (d + 1) + 610)`.
* `sparseCoreBundleRestartToolMachWith_restart_lower` and
  `sparseCoreBundleRestartToolMachWith_init_lower`: lower bounds charging level-`i` graph/forest
  work to the restart cost delta and rebuilt level-`j` work to `T.cost (next.scState j)`.
* `deepShift_costTotal` and `deepShift_costTotal_mach`: discharge `DeepShiftOpsHypKFBL.costTotal`
  for any tool meeting those two lower bounds and concretely for
  `sparseCoreBundleRestartToolMachWith`.
* `shiftDeepModelInvKFBL_of_shiftLoopChainInv`: derives `ShiftDeepModelInvKFBL` from
  `Chain.Ordered.ShiftLoopChainInv` and `cfg.ValidOrdNoHidden`.
-/

public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered
open MinCostFlow.DynSpanner MinCostFlow.SparseCore MinCostFlow.SparseCore.Program

/-! ## Explicit `levelCost`, `deepFixed`, and `toolMul` -/

/-- Per-level live rebuild cost matching the left-hand side of `DeepShiftOpsHypKFBL.levelCostDom`. -/
@[expose] noncomputable def deepShiftLevelCost (L capExp : ℕ) (cfg : Alg2Config)
    (Psc : SparseCoreOrdParams) (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)) (j : ℕ) : ℕ :=
  let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
  Psc.mul * cfg.T.cost (next.scState j) +
    ordLevelLiveCost L capExp Psc (next.lvlM j) next.N₀
      (next.G j).n (next.G j).m (next.G (j + 1)).n (next.G (j + 1)).m
      (2 * (next.G j).n + 2 * (next.G j).m + 1)
      (2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m + 1) + 26

/-- Explicit `deepFixed` bound for `DeepShiftOpsHypKFBL.costTotal`: depends only on `d`,
`Psc.mul`, `Psc.readout`, `bundleLogFactor M₀ N₀`, and `lastMul` (no linear `m`, `N₀`, `capLimit`,
`fcap`, or `forestEdgeCap` terms). -/
@[expose] def deepShiftFixedBound (Psc : SparseCoreOrdParams) (M₀ N₀ d lastMul : ℕ) : ℕ :=
  let B₀ := SparseCore.bundleLogFactor M₀ N₀
  Psc.mul + 4 * Psc.mul * B₀ + 2 * Psc.readout +
    d * (5 * Psc.mul + 4 * Psc.mul * B₀ + 2 * Psc.readout + 475) +
    lastMul + 2 * d * (Psc.readout + 48) + 210 * (d + 1) + 1580

/-- Explicit `toolMul` bound for `DeepShiftOpsHypKFBL.costTotal`: absorbs all level-size-growing
terms into `toolMul * (next.totalRuntime - model.chain.totalRuntime)`. -/
@[expose] def deepShiftToolMulBound (L capExp : ℕ) (Psc : SparseCoreOrdParams)
    (M₀ N₀ d lastMul : ℕ) : ℕ :=
  let LwMax₀ := ordLevelLwMax L capExp M₀ N₀
  max lastMul (5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 170 * (d + 1) + 610)

/-! ## Monotonicity and edge-sum helpers -/

/-- Level sizes are bounded by `levelM TP P 0` whenever `γ_ℓ(M₀²) ≤ k`. -/
theorem levelM_le_levelM_zero {TP : SparseCoreParams} {P : ChainParams}
    (hTP : TP.Valid) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k) (j : ℕ) :
    levelM TP P j ≤ levelM TP P 0 := by
  unfold levelM
  have hk : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγnn : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hTP.2.2.1 (P.M₀ ^ 2))
  have hdiv_nn : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ) := div_nonneg hγnn hk.le
  have hdiv_le : TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ) ≤ 1 := (div_le_one hk).mpr hγk
  have hpow : (TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ)) ^ j ≤ 1 := pow_le_one₀ hdiv_nn hdiv_le
  refine Nat.ceil_mono ?_
  have hbase_nn : 0 ≤ (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) :=
    mul_nonneg (Nat.cast_nonneg _) hγnn
  simpa [pow_zero, mul_one] using mul_le_mul_of_nonneg_left hpow hbase_nn

private lemma one_le_bundleLogFactor (M N : ℕ) : 1 ≤ SparseCore.bundleLogFactor M N := by
  unfold SparseCore.bundleLogFactor
  have h1 : 1 ≤ Nat.log 2 (M + N + 2) + 1 := Nat.succ_pos _
  nlinarith

private lemma bundleLogFactor_mono {M₁ M₂ N : ℕ} (h : M₁ ≤ M₂) :
    SparseCore.bundleLogFactor M₁ N ≤ SparseCore.bundleLogFactor M₂ N := by
  unfold SparseCore.bundleLogFactor
  have hlog : Nat.log 2 (M₁ + N + 2) ≤ Nat.log 2 (M₂ + N + 2) :=
    Nat.log_mono_right (by omega)
  exact Nat.pow_le_pow_left (by omega) 2

private lemma ordLevelLwMax_mono {L capExp M₁ M₂ N : ℕ} (h : M₁ ≤ M₂) :
    ordLevelLwMax L capExp M₁ N ≤ ordLevelLwMax L capExp M₂ N := by
  unfold ordLevelLwMax
  have hlog : Nat.log 2 (M₁ + N + 2) ≤ Nat.log 2 (M₂ + N + 2) :=
    Nat.log_mono_right (by omega)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _

private lemma wireCoreLenEdgeCost_mono {K₁ K₂ : ℕ} (h : K₁ ≤ K₂) :
    wireCoreLenEdgeCost K₁ ≤ wireCoreLenEdgeCost K₂ := by
  unfold wireCoreLenEdgeCost
  have hsq : K₁ ^ 2 ≤ K₂ ^ 2 := Nat.pow_le_pow_left h 2
  omega

/-- Under level-by-level subgraph inclusions on `[first, d]`, every suffix graph `chain.G j`
(`first ≤ j ≤ d`) has edge set contained in `(chain.G first).E`. -/
private lemma chain_G_E_subset_of_step {T : SparseCoreRestartTool} {P : ChainParams}
    {chain : ChainState T P} {first : ℕ}
    (hStep : ∀ j, first ≤ j → j < P.d → (chain.G (j + 1)).E ⊆ (chain.G j).E) :
    ∀ j, first ≤ j → j ≤ P.d → (chain.G j).E ⊆ (chain.G first).E := by
  intro j h1 h2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h1
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih =>
    have hlt : first + k < P.d := by omega
    exact (hStep (first + k) (by omega) hlt).trans (ih (by omega) (by omega))

/-- Every forest in `chainSuffixForests chain first` is an edge-subgraph of `chain.G first`, so
the total edge sum across the suffix forests is at most `(P.d + 1) * (chain.G first).m`. -/
theorem graphListEdgeSum_chainSuffixForests_le {T : SparseCoreRestartTool} {P : ChainParams}
    {chain : ChainState T P} {first : ℕ} (hfirst : first ≤ P.d)
    (hStep : ∀ j, first ≤ j → j < P.d →
      (T.lsfs (chain.scState j) (chain.bran j)).F.F.E ⊆ (chain.G j).E ∧
      (chain.G (j + 1)).E ⊆ (chain.G j).E)
    (hLast : (chain.lastLSFs chain.lastBran).F.F.E ⊆ (chain.G P.d).E) :
    graphListEdgeSum (chainSuffixForests chain first) ≤ (P.d + 1) * (chain.G first).m := by
  have hSubG := chain_G_E_subset_of_step (fun j h1 h2 => (hStep j h1 h2).2)
  have hMemLe : ∀ F ∈ chainSuffixForests chain first, F.m ≤ (chain.G first).m := by
    intro F hF
    simp only [chainSuffixForests, List.mem_append, List.mem_map, List.mem_range,
      List.mem_singleton] at hF
    rcases hF with ⟨t, ht, rfl⟩ | rfl
    · have hj1 : first ≤ first + t := by omega
      have hj2 : first + t < P.d := by omega
      exact Finset.card_le_card ((hStep (first + t) hj1 hj2).1.trans (hSubG (first + t) hj1 (le_of_lt hj2)))
    · exact Finset.card_le_card (hLast.trans (hSubG P.d hfirst le_rfl))
  have hSumLe : ∀ (L : List MGraph), (∀ F ∈ L, F.m ≤ (chain.G first).m) →
      graphListEdgeSum L ≤ L.length * (chain.G first).m := by
    intro L
    induction L with
    | nil => intro _; simp [graphListEdgeSum]
    | cons F rest ih =>
      intro hAll
      simp only [graphListEdgeSum, List.map_cons, List.sum_cons, List.length_cons]
      have hF : F.m ≤ (chain.G first).m := hAll F (List.mem_cons_self ..)
      have hRest := ih (fun G hG => hAll G (List.mem_cons_of_mem F hG))
      dsimp only [graphListEdgeSum] at hRest
      have hmul : (rest.length + 1) * (chain.G first).m =
          (chain.G first).m + rest.length * (chain.G first).m := by ring
      omega
  have hLen : (chainSuffixForests chain first).length ≤ P.d + 1 := by
    simp only [chainSuffixForests, List.length_append, List.length_map, List.length_range,
      List.length_singleton]
    omega
  exact (hSumLe _ hMemLe).trans (Nat.mul_le_mul_right _ hLen)

/-! ## Concrete tool lower bounds for `sparseCoreBundleRestartToolMachWith` -/

/-- For `sparseCoreBundleRestartToolMachWith`, restarting branch `b < k` on a reached state
`SparseCoreOrdInput` increases `T.cost` by at least `G.m * bundleLogFactor M N`. -/
theorem sparseCoreBundleRestartToolMachWith_restart_lower
    (lsfInit : LSFInit) (C_lsst : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    {k M N n b : ℕ}
    {st : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst depth sparsify params spanConst).State}
    {G : MGraph} {ord : ℕ → List End}
    (hIn : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst depth sparsify params spanConst)
      k M N st G ord n)
    (hb : b < k) :
    let T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst depth sparsify params spanConst
    G.m * SparseCore.bundleLogFactor M N ≤ T.cost (T.restart st b) - T.cost st := by
  intro T
  by_cases hne : SparseCoreBundleState.isNonempty (L := depth) st = true
  · obtain ⟨hk, _, hmn⟩ := asm_input_inv lsfInit C_lsst depth sparsify params spanConst hIn
    have hGeq : (SparseCoreBundleState.trees (L := depth) st b).cs.G = G :=
      sparseCoreOrdInput_cs_G_eq hIn hne b
    have hReq := bundleRestartToolMachWith_restart_cost_eq lsfInit C_lsst depth sparsify
      params spanConst st b hne (hk.symm ▸ hb)
    change T.cost (T.restart st b) =
      T.cost st + singleBundleRestartMachCost depth sparsify (st.trees b) st.ord at hReq
    rw [hReq, Nat.add_sub_cancel_left]
    unfold singleBundleRestartMachCost
    rw [hGeq, (hmn b).1, (hmn b).2.1]
    exact Nat.mul_le_mul_right _ (by omega)
  · have hem : SparseCoreBundleState.isNonempty (L := depth) st = false :=
      Bool.eq_false_iff.mpr hne
    obtain ⟨_, hE⟩ := asmEmpty_inv hIn hem
    have hm0 : G.m = 0 := by simp [MGraph.m, hE]
    rw [hm0, Nat.zero_mul]
    exact Nat.zero_le _

/-- For `sparseCoreBundleRestartToolMachWith` with `0 < k`, initializing on a valid graph `G`
pays at least `3 * G.m * bundleLogFactor M N`. -/
theorem sparseCoreBundleRestartToolMachWith_init_lower
    (lsfInit : LSFInit) (C_lsst : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    {k M N : ℕ} {G : MGraph} {ℓ g : ℕ → ℝ} {ord : ℕ → List End}
    (hk : 0 < k) (hG : G.IsValid) :
    let T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst depth sparsify params spanConst
    3 * G.m * SparseCore.bundleLogFactor M N ≤ T.cost (T.initOrd k M N G ℓ g ord) := by
  intro T
  rw [asm_init_cost_eq lsfInit C_lsst depth sparsify params spanConst k M N G ℓ g ord]
  by_cases hne : G.V.Nonempty
  · rw [ite_eq_left hne]
    have h0 : 0 ∈ Finset.range k := Finset.mem_range.mpr hk
    have hsingle :
        (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ ord 0).machCost ≤
        (Finset.range k).sum fun j =>
          (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ ord j).machCost :=
      Finset.single_le_sum
        (f := fun j => (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ ord j).machCost)
        (fun _ _ => Nat.zero_le _) h0
    refine le_trans ?_ hsingle
    rw [initBundleTreeWithParams_machCost]
    exact Nat.mul_le_mul_right _ (by omega)
  · have hV : G.V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hE : G.E = ∅ := by
      ext e
      simp only [Finset.notMem_empty, iff_false]
      intro he
      have ht := (hG e he).1
      rw [hV] at ht
      exact Finset.notMem_empty _ ht
    have hm0 : G.m = 0 := by simp [MGraph.m, hE]
    rw [hm0]
    simp

/-! ## Discharging `DeepShiftOpsHypKFBL.levelCostDom` and `costTotal` -/

/-- `deepShiftLevelCost` discharges `DeepShiftOpsHypKFBL.levelCostDom` identically. -/
theorem deepShift_levelCostDom (L capExp : ℕ) (cfg : Alg2Config) (Psc : SparseCoreOrdParams)
    (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)) (j : ℕ) :
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    Psc.mul * cfg.T.cost (next.scState j) +
      ordLevelLiveCost L capExp Psc (next.lvlM j) next.N₀
        (next.G j).n (next.G j).m (next.G (j + 1)).n (next.G (j + 1)).m
        (2 * (next.G j).n + 2 * (next.G j).m + 1)
        (2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m + 1) + 26 ≤
      deepShiftLevelCost L capExp cfg Psc model i j :=
  le_rfl

/-- Discharges `DeepShiftOpsHypKFBL.costTotal` with `deepShiftLevelCost`, `deepShiftFixedBound`,
and `deepShiftToolMulBound` for any tool satisfying `ToolCostMono` and the restart/init lower
bounds. -/
theorem deepShift_costTotal
    (L capExp lastMul : ℕ) (cfg : Alg2Config) (Psc : SparseCoreOrdParams)
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (hMono : ToolCostMono cfg.T)
    (hRestartLower : ∀ {M N n b : ℕ} {st : cfg.T.State} {G : MGraph} {ord : ℕ → List End},
      SparseCoreOrdInput cfg.T cfg.P.k M N st G ord n → b < cfg.P.k →
      G.m * SparseCore.bundleLogFactor M N ≤ cfg.T.cost (cfg.T.restart st b) - cfg.T.cost st)
    (hInitLower : ∀ {M N : ℕ} {G : MGraph} {ℓ g : ℕ → ℝ} {ord : ℕ → List End},
      G.IsValid →
      3 * G.m * SparseCore.bundleLogFactor M N ≤ cfg.T.cost (cfg.T.initOrd cfg.P.k M N G ℓ g ord))
    (model : Alg2State cfg) (i : Fin (cfg.P.d + 1))
    (hiLt : i.val < cfg.P.d)
    (hInI : SparseCoreOrdInput cfg.T cfg.P.k (model.chain.lvlM i.val) model.chain.N₀
      (model.chain.scState i.val) (model.chain.G i.val) (model.chain.levelOrd i.val)
      (model.chain.updCount i.val))
    (hModelK : ShiftDeepModelInvKFBL model i) :
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    let Fi0 := (cfg.T.lsfs (model.chain.scState i.val) (model.chain.bran i.val)).F.F
    let H1 := next.G (i.val + 1)
    let LwMax := ordLevelLwMax L capExp (model.chain.lvlM i.val) model.chain.N₀
    let M₀ := levelM cfg.TP cfg.P 0
    copyGraphLiveCost Fi0.n Fi0.m +
      Psc.mul * (cfg.T.cost (next.scState i.val) - cfg.T.cost (model.chain.scState i.val) + 1) +
      Psc.mul * (2 * H1.n + 2 * H1.m + 2) *
        SparseCore.bundleLogFactor (model.chain.lvlM i.val) model.chain.N₀ +
      2 * Psc.readout + copyGraphLiveCost H1.n H1.m +
      H1.m * (wireCoreLenEdgeCost LwMax + 30) +
      (Finset.Ico (i.val + 1) cfg.P.d).sum
        (fun j => deepShiftLevelCost L capExp cfg Psc model i j + 9) +
      lastMul * (cfg.L.cost (next.G cfg.P.d) + 1) +
      2 * cfg.P.d * (Psc.readout + 48) + 210 * (cfg.P.d + 1) +
      85 * (graphListEdgeSum (chainSuffixForests model.chain i.val) +
        graphListEdgeSum (chainSuffixForests next i.val)) + 1100 ≤
      deepShiftFixedBound Psc M₀ cfg.N₀ cfg.P.d lastMul +
        deepShiftToolMulBound L capExp Psc M₀ cfg.N₀ cfg.P.d lastMul *
          (next.totalRuntime - model.chain.totalRuntime) := by
  dsimp only
  let chain := model.chain
  let d := cfg.P.d
  let i0 := i.val
  set next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P chain i0).1
  set M₀ := levelM cfg.TP cfg.P 0
  set B₀ := SparseCore.bundleLogFactor M₀ cfg.N₀
  set LwMax₀ := ordLevelLwMax L capExp M₀ cfg.N₀
  set tMul := deepShiftToolMulBound L capExp Psc M₀ cfg.N₀ d lastMul
  set Δi := cfg.T.cost (next.scState i0) - cfg.T.cost (chain.scState i0)
  set Fi0 := (cfg.T.lsfs (chain.scState i0) (chain.bran i0)).F.F
  set H1 := next.G (i0 + 1)
  have hNextEq : (alg2LoopShiftStep cfg model i).chain = next := rfl
  rcases hModelK with ⟨hLvl0, hLvlN, _, _, hSub, hLastOld, hLastNew, hValidN, _, _, _⟩
  rw [hNextEq] at hLvlN hSub hLastNew hValidN
  have hEx := ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P chain hiLt
  have hLvlM0 : chain.lvlM = levelM cfg.TP cfg.P := hLvl0.2.1
  have hN0Eq : chain.N₀ = cfg.N₀ := hLvl0.2.2.1
  have hLvlMN : next.lvlM = levelM cfg.TP cfg.P := hLvlN.2.1
  have hN0N : next.N₀ = cfg.N₀ := hLvlN.2.2.1
  have hNewBranLt : (chain.bran i0 + 1) % cfg.P.k < cfg.P.k := Nat.mod_lt _ cfg.P.hk
  have hDeltaEq :
      next.totalRuntime - chain.totalRuntime =
        Δi + (Finset.Ico (i0 + 1) d).sum (fun j => cfg.T.cost (next.scState j)) +
        cfg.L.cost (next.G d) :=
    shiftDeep_totalRuntime_sub cfg.T cfg.L cfg.P chain hiLt
      (hMono.2 (chain.scState i0) ((chain.bran i0 + 1) % cfg.P.k))
  -- Lower bound on Δi
  have hΔi_ge : (chain.G i0).m * SparseCore.bundleLogFactor (chain.lvlM i0) chain.N₀ ≤ Δi := by
    have h := hRestartLower hInI hNewBranLt
    dsimp only [Δi]
    rw [hEx.2.2.1]
    exact h
  have hB1_i : 1 ≤ SparseCore.bundleLogFactor (chain.lvlM i0) chain.N₀ :=
    one_le_bundleLogFactor _ _
  have hGi_le_Δi : (chain.G i0).m ≤ Δi :=
    (Nat.le_mul_of_pos_right _ (by omega : 0 < SparseCore.bundleLogFactor _ _)).trans hΔi_ge
  have hBi_le_B0 : SparseCore.bundleLogFactor (chain.lvlM i0) chain.N₀ ≤ B₀ := by
    rw [hLvlM0, hN0Eq]
    exact bundleLogFactor_mono (levelM_le_levelM_zero hTP hγk i0)
  have hLw_i_le : wireCoreLenEdgeCost (ordLevelLwMax L capExp (chain.lvlM i0) chain.N₀) ≤
      wireCoreLenEdgeCost LwMax₀ := by
    rw [hLvlM0, hN0Eq]
    exact wireCoreLenEdgeCost_mono (ordLevelLwMax_mono (levelM_le_levelM_zero hTP hγk i0))
  -- Bounds on Fi0 and H1
  have hFi0_n : Fi0.n ≤ (chain.G i0).m + 1 :=
    (Finset.card_le_card (hSub i0 le_rfl hiLt).1).trans (hLvl0.1 i0 (le_of_lt hiLt))
  have hFi0_m : Fi0.m ≤ (chain.G i0).m := Finset.card_le_card (hSub i0 le_rfl hiLt).2.1
  have hCopyFi0 : copyGraphLiveCost Fi0.n Fi0.m ≤ 290 * Δi + 240 := by
    unfold copyGraphLiveCost; omega
  have hH1_m : H1.m ≤ (chain.G i0).m := by
    have hsub : (next.G (i0 + 1)).E ⊆ (next.G i0).E := (hSub i0 le_rfl hiLt).2.2.2.2
    rw [hEx.1 i0 le_rfl] at hsub
    exact Finset.card_le_card hsub
  have hH1_n : H1.n ≤ (chain.G i0).m + 1 :=
    (hLvlN.1 (i0 + 1) (by omega)).trans (Nat.add_le_add_right hH1_m 1)
  have hCopyH1 : copyGraphLiveCost H1.n H1.m ≤ 290 * Δi + 240 := by
    unfold copyGraphLiveCost; omega
  have hOrdH1 : Psc.mul * (2 * H1.n + 2 * H1.m + 2) *
      SparseCore.bundleLogFactor (chain.lvlM i0) chain.N₀ ≤
      4 * Psc.mul * Δi + 4 * Psc.mul * B₀ := by
    set Bi := SparseCore.bundleLogFactor (chain.lvlM i0) chain.N₀
    have h1 : 2 * H1.n + 2 * H1.m + 2 ≤ 4 * (chain.G i0).m + 4 := by omega
    have h2 : Psc.mul * (2 * H1.n + 2 * H1.m + 2) * Bi ≤
        Psc.mul * (4 * (chain.G i0).m + 4) * Bi :=
      Nat.mul_le_mul_right Bi (Nat.mul_le_mul_left Psc.mul h1)
    have h3 : Psc.mul * (4 * (chain.G i0).m + 4) * Bi =
        4 * Psc.mul * ((chain.G i0).m * Bi) + 4 * Psc.mul * Bi := by ring
    have h4 : 4 * Psc.mul * ((chain.G i0).m * Bi) ≤ 4 * Psc.mul * Δi :=
      Nat.mul_le_mul_left (4 * Psc.mul) hΔi_ge
    have h5 : 4 * Psc.mul * Bi ≤ 4 * Psc.mul * B₀ :=
      Nat.mul_le_mul_left (4 * Psc.mul) hBi_le_B0
    omega
  have hLenH1 : H1.m * (wireCoreLenEdgeCost (ordLevelLwMax L capExp (chain.lvlM i0) chain.N₀) + 30) ≤
      (wireCoreLenEdgeCost LwMax₀ + 30) * Δi := by
    calc H1.m * (wireCoreLenEdgeCost (ordLevelLwMax L capExp (chain.lvlM i0) chain.N₀) + 30)
        ≤ Δi * (wireCoreLenEdgeCost LwMax₀ + 30) :=
          Nat.mul_le_mul (hH1_m.trans hGi_le_Δi) (by omega)
      _ = (wireCoreLenEdgeCost LwMax₀ + 30) * Δi := Nat.mul_comm _ _
  -- Suffix forest edge sum
  have hOldForests : graphListEdgeSum (chainSuffixForests chain i0) ≤ (d + 1) * (chain.G i0).m :=
    graphListEdgeSum_chainSuffixForests_le (le_of_lt hiLt)
      (fun j hj1 hj2 => ⟨(hSub j hj1 hj2).2.1, (hSub j hj1 hj2).2.2.1⟩) hLastOld
  have hNewForests : graphListEdgeSum (chainSuffixForests next i0) ≤ (d + 1) * (chain.G i0).m := by
    have h := graphListEdgeSum_chainSuffixForests_le (le_of_lt hiLt)
      (fun j hj1 hj2 => ⟨(hSub j hj1 hj2).2.2.2.1, (hSub j hj1 hj2).2.2.2.2⟩) hLastNew
    rwa [hEx.1 i0 le_rfl] at h
  have hForestCost : 85 * (graphListEdgeSum (chainSuffixForests chain i0) +
      graphListEdgeSum (chainSuffixForests next i0)) ≤ 170 * (d + 1) * Δi := by
    have hsum : graphListEdgeSum (chainSuffixForests chain i0) +
        graphListEdgeSum (chainSuffixForests next i0) ≤ 2 * (d + 1) * Δi := by
      have h1 : (d + 1) * (chain.G i0).m ≤ (d + 1) * Δi := Nat.mul_le_mul_left _ hGi_le_Δi
      have h2eq : (d + 1) * Δi + (d + 1) * Δi = 2 * (d + 1) * Δi := by ring
      omega
    calc 85 * (graphListEdgeSum (chainSuffixForests chain i0) +
            graphListEdgeSum (chainSuffixForests next i0))
        ≤ 85 * (2 * (d + 1) * Δi) := Nat.mul_le_mul_left 85 hsum
      _ = 170 * (d + 1) * Δi := by ring
  -- Per-level bound for j ∈ Ico (i0 + 1) d
  have hLevelSum :
      (Finset.Ico (i0 + 1) d).sum (fun j => deepShiftLevelCost L capExp cfg Psc model i j + 9) ≤
        d * (5 * Psc.mul + 4 * Psc.mul * B₀ + 2 * Psc.readout + 475) +
        tMul * (Finset.Ico (i0 + 1) d).sum (fun j => cfg.T.cost (next.scState j)) := by
    set perFixed := 5 * Psc.mul + 4 * Psc.mul * B₀ + 2 * Psc.readout + 475
    have hEach : ∀ j ∈ Finset.Ico (i0 + 1) d,
        deepShiftLevelCost L capExp cfg Psc model i j + 9 ≤
          perFixed + tMul * cfg.T.cost (next.scState j) := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      set cj := cfg.T.cost (next.scState j)
      set Gj := next.G j
      set Hj := next.G (j + 1)
      set Bj := SparseCore.bundleLogFactor (next.lvlM j) next.N₀
      have hscj := (hEx.2.2.2.2.2.2.2.2.1 j hj1 hj2).1
      have hcj_ge : 3 * Gj.m * Bj ≤ cj := by
        have h := hInitLower (M := chain.lvlM j) (N := chain.N₀) (G := Gj)
          (ℓ := next.toTreeChain.chainLen chain.ℓ j)
          (g := next.toTreeChain.chainGrad chain.g j) (ord := next.levelOrd j)
          (hValidN j (le_of_lt hj2))
        dsimp only [cj, Bj]
        rw [hscj, hLvlMN, hN0N, ← hLvlM0, ← hN0Eq]
        exact h
      have hBj1 : 1 ≤ Bj := one_le_bundleLogFactor _ _
      have h3Gm_le : 3 * Gj.m ≤ cj :=
        (Nat.le_mul_of_pos_right _ (by omega : 0 < Bj)).trans hcj_ge
      have hGm_le : Gj.m ≤ cj := by omega
      have hBj_le_B0 : Bj ≤ B₀ := by
        dsimp only [Bj]; rw [hLvlMN, hN0N]
        exact bundleLogFactor_mono (levelM_le_levelM_zero hTP hγk j)
      have hLw_j_le : wireCoreLenEdgeCost (ordLevelLwMax L capExp (next.lvlM j) next.N₀) ≤
          wireCoreLenEdgeCost LwMax₀ := by
        rw [hLvlMN, hN0N]
        exact wireCoreLenEdgeCost_mono (ordLevelLwMax_mono (levelM_le_levelM_zero hTP hγk j))
      have hGn : Gj.n ≤ Gj.m + 1 := hLvlN.1 j (le_of_lt hj2)
      have hHm : Hj.m ≤ Gj.m := Finset.card_le_card (hSub j (by omega) hj2).2.2.2.2
      have hHn : Hj.n ≤ Gj.m + 1 := (hLvlN.1 (j + 1) (by omega)).trans (Nat.add_le_add_right hHm 1)
      have hInTerm : Psc.mul * (Gj.n + Gj.m + (2 * Gj.n + 2 * Gj.m + 1) + 1) ≤
          2 * Psc.mul * cj + 5 * Psc.mul := by
        have h1 : Gj.n + Gj.m + (2 * Gj.n + 2 * Gj.m + 1) + 1 ≤ 2 * (3 * Gj.m) + 5 := by omega
        have h2 : Psc.mul * (Gj.n + Gj.m + (2 * Gj.n + 2 * Gj.m + 1) + 1) ≤
            Psc.mul * (2 * (3 * Gj.m) + 5) := Nat.mul_le_mul_left _ h1
        have h3 : Psc.mul * (2 * (3 * Gj.m) + 5) = 2 * Psc.mul * (3 * Gj.m) + 5 * Psc.mul := by ring
        have h4 : 2 * Psc.mul * (3 * Gj.m) ≤ 2 * Psc.mul * cj := Nat.mul_le_mul_left _ h3Gm_le
        omega
      have hOutTerm : Psc.mul * (2 * Hj.n + 2 * Hj.m + 1 + 1) * Bj ≤
          2 * Psc.mul * cj + 4 * Psc.mul * B₀ := by
        have h1 : 2 * Hj.n + 2 * Hj.m + 1 + 1 ≤ 4 * Gj.m + 4 := by omega
        have h2 : Psc.mul * (2 * Hj.n + 2 * Hj.m + 1 + 1) * Bj ≤
            Psc.mul * (4 * Gj.m + 4) * Bj :=
          Nat.mul_le_mul_right Bj (Nat.mul_le_mul_left Psc.mul h1)
        have h3 : Psc.mul * (4 * Gj.m + 4) * Bj = 4 * Psc.mul * (Gj.m * Bj) + 4 * Psc.mul * Bj := by ring
        have h4 : 4 * Psc.mul * (Gj.m * Bj) ≤ 2 * Psc.mul * (3 * Gj.m * Bj) := by
          have h46 : 4 * (Gj.m * Bj) ≤ 6 * (Gj.m * Bj) := Nat.mul_le_mul_right _ (by decide)
          have h6eq : 2 * (3 * Gj.m * Bj) = 6 * (Gj.m * Bj) := by ring
          calc 4 * Psc.mul * (Gj.m * Bj) = Psc.mul * (4 * (Gj.m * Bj)) := by ring
            _ ≤ Psc.mul * (2 * (3 * Gj.m * Bj)) := Nat.mul_le_mul_left _ (h6eq ▸ h46)
            _ = 2 * Psc.mul * (3 * Gj.m * Bj) := by ring
        have h5 : 2 * Psc.mul * (3 * Gj.m * Bj) ≤ 2 * Psc.mul * cj := Nat.mul_le_mul_left _ hcj_ge
        have h6 : 4 * Psc.mul * Bj ≤ 4 * Psc.mul * B₀ := Nat.mul_le_mul_left _ hBj_le_B0
        omega
      have hCopyHj : copyGraphLiveCost Hj.n Hj.m ≤ 290 * cj + 240 := by
        unfold copyGraphLiveCost; omega
      have hLenHj : Hj.m * (wireCoreLenEdgeCost (ordLevelLwMax L capExp (next.lvlM j) next.N₀) + 30) ≤
          (wireCoreLenEdgeCost LwMax₀ + 30) * cj := by
        calc Hj.m * (wireCoreLenEdgeCost (ordLevelLwMax L capExp (next.lvlM j) next.N₀) + 30)
            ≤ cj * (wireCoreLenEdgeCost LwMax₀ + 30) :=
              Nat.mul_le_mul (hHm.trans hGm_le) (by omega)
          _ = (wireCoreLenEdgeCost LwMax₀ + 30) * cj := Nat.mul_comm _ _
      have htMulGe : 5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 320 ≤ tMul := by
        change 5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 320 ≤
          max lastMul (5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 170 * (d + 1) + 610)
        exact le_trans (by omega) (le_max_right _ _)
      have htMulCj : (5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 320) * cj ≤ tMul * cj :=
        Nat.mul_le_mul_right cj htMulGe
      have hExpand : (5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 320) * cj =
          Psc.mul * cj + 2 * Psc.mul * cj + 2 * Psc.mul * cj + 290 * cj +
            (wireCoreLenEdgeCost LwMax₀ + 30) * cj := by ring
      dsimp only [deepShiftLevelCost, ordLevelLiveCost]
      change Psc.mul * cj +
        (Psc.mul * (Gj.n + Gj.m + (2 * Gj.n + 2 * Gj.m + 1) + 1) +
          Psc.mul * (2 * Hj.n + 2 * Hj.m + 1 + 1) * Bj +
          2 * Psc.readout + copyGraphLiveCost Hj.n Hj.m +
          Hj.m * (wireCoreLenEdgeCost (ordLevelLwMax L capExp (next.lvlM j) next.N₀) + 30) + 200) +
        26 + 9 ≤ perFixed + tMul * cj
      omega
    calc (Finset.Ico (i0 + 1) d).sum (fun j => deepShiftLevelCost L capExp cfg Psc model i j + 9)
        ≤ (Finset.Ico (i0 + 1) d).sum (fun j => perFixed + tMul * cfg.T.cost (next.scState j)) :=
          Finset.sum_le_sum hEach
      _ = (Finset.Ico (i0 + 1) d).card * perFixed +
          tMul * (Finset.Ico (i0 + 1) d).sum (fun j => cfg.T.cost (next.scState j)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum]
      _ ≤ d * perFixed +
          tMul * (Finset.Ico (i0 + 1) d).sum (fun j => cfg.T.cost (next.scState j)) := by
          refine Nat.add_le_add_right (Nat.mul_le_mul_right _ ?_) _
          rw [Nat.card_Ico]; omega
  -- Combine Δi, rebuilt levels, and last level
  have htMul_i : 5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 170 * (d + 1) + 610 ≤ tMul :=
    le_max_right _ _
  have htMul_last : lastMul ≤ tMul := le_max_left _ _
  have hΔi_sum :
      290 * Δi + Psc.mul * Δi + 4 * Psc.mul * Δi + 290 * Δi +
        (wireCoreLenEdgeCost LwMax₀ + 30) * Δi + 170 * (d + 1) * Δi ≤ tMul * Δi := by
    have heq : 290 * Δi + Psc.mul * Δi + 4 * Psc.mul * Δi + 290 * Δi +
        (wireCoreLenEdgeCost LwMax₀ + 30) * Δi + 170 * (d + 1) * Δi =
        (5 * Psc.mul + wireCoreLenEdgeCost LwMax₀ + 170 * (d + 1) + 610) * Δi := by ring
    rw [heq]
    exact Nat.mul_le_mul_right Δi htMul_i
  have hLastCost : lastMul * (cfg.L.cost (next.G d) + 1) ≤ lastMul + tMul * cfg.L.cost (next.G d) := by
    have hmul := Nat.mul_le_mul_right (cfg.L.cost (next.G d)) htMul_last
    have hexp : lastMul * (cfg.L.cost (next.G d) + 1) = lastMul * cfg.L.cost (next.G d) + lastMul := by
      ring
    omega
  have hMulSplit : tMul * (next.totalRuntime - chain.totalRuntime) =
      tMul * Δi + tMul * (Finset.Ico (i0 + 1) d).sum (fun j => cfg.T.cost (next.scState j)) +
      tMul * cfg.L.cost (next.G d) := by
    rw [hDeltaEq]; ring
  have hPscMul1 : Psc.mul * (Δi + 1) = Psc.mul * Δi + Psc.mul := by ring
  rw [hMulSplit]
  have hB0_eq : B₀ = SparseCore.bundleLogFactor M₀ cfg.N₀ := rfl
  rw [hB0_eq] at hOrdH1 hLevelSum
  dsimp only [chain, d, i0, deepShiftFixedBound] at hCopyFi0 hCopyH1 hOrdH1 hLenH1 hForestCost hLevelSum hΔi_sum hLastCost hPscMul1 ⊢
  omega

/-- Concrete specialization of `deepShift_costTotal` to `sparseCoreBundleRestartToolMachWith`. -/
theorem deepShift_costTotal_mach
    (lsfInit : LSFInit) (C_lsst : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (L capExp lastMul : ℕ) (cfg : Alg2Config) (Psc : SparseCoreOrdParams)
    (hT : cfg.T = sparseCoreBundleRestartToolMachWith lsfInit C_lsst depth sparsify params spanConst)
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (model : Alg2State cfg) (i : Fin (cfg.P.d + 1))
    (hiLt : i.val < cfg.P.d)
    (hInI : SparseCoreOrdInput cfg.T cfg.P.k (model.chain.lvlM i.val) model.chain.N₀
      (model.chain.scState i.val) (model.chain.G i.val) (model.chain.levelOrd i.val)
      (model.chain.updCount i.val))
    (hModelK : ShiftDeepModelInvKFBL model i) :
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    let Fi0 := (cfg.T.lsfs (model.chain.scState i.val) (model.chain.bran i.val)).F.F
    let H1 := next.G (i.val + 1)
    let LwMax := ordLevelLwMax L capExp (model.chain.lvlM i.val) model.chain.N₀
    let M₀ := levelM cfg.TP cfg.P 0
    copyGraphLiveCost Fi0.n Fi0.m +
      Psc.mul * (cfg.T.cost (next.scState i.val) - cfg.T.cost (model.chain.scState i.val) + 1) +
      Psc.mul * (2 * H1.n + 2 * H1.m + 2) *
        SparseCore.bundleLogFactor (model.chain.lvlM i.val) model.chain.N₀ +
      2 * Psc.readout + copyGraphLiveCost H1.n H1.m +
      H1.m * (wireCoreLenEdgeCost LwMax + 30) +
      (Finset.Ico (i.val + 1) cfg.P.d).sum
        (fun j => deepShiftLevelCost L capExp cfg Psc model i j + 9) +
      lastMul * (cfg.L.cost (next.G cfg.P.d) + 1) +
      2 * cfg.P.d * (Psc.readout + 48) + 210 * (cfg.P.d + 1) +
      85 * (graphListEdgeSum (chainSuffixForests model.chain i.val) +
        graphListEdgeSum (chainSuffixForests next i.val)) + 1100 ≤
      deepShiftFixedBound Psc M₀ cfg.N₀ cfg.P.d lastMul +
        deepShiftToolMulBound L capExp Psc M₀ cfg.N₀ cfg.P.d lastMul *
          (next.totalRuntime - model.chain.totalRuntime) := by
  rcases cfg with ⟨T, Lc, TP, LP, P, N₀, Ψ, α, f9, f10⟩
  dsimp only at hT hTP hγk hiLt hInI hModelK ⊢
  subst hT
  exact deepShift_costTotal L capExp lastMul ⟨_, Lc, TP, LP, P, N₀, Ψ, α, f9, f10⟩ Psc hTP hγk
    (sparseCoreBundleRestartToolMachWith_costMono lsfInit C_lsst depth sparsify params spanConst)
    (fun hIn hb => sparseCoreBundleRestartToolMachWith_restart_lower lsfInit C_lsst depth sparsify
      params spanConst hIn hb)
    (fun hG => sparseCoreBundleRestartToolMachWith_init_lower lsfInit C_lsst depth sparsify params
      spanConst P.hk hG)
    model i hiLt hInI hModelK

/-! ## Deriving `ShiftDeepModelInvKFBL` from `ShiftLoopChainInv` -/

/-- Under `ChainInv` and `cfg.ValidOrdNoHidden`, the output rotation order `cfg.T.rot` on the
active branch of level `j < d` is a rotation order of `ch.G (j + 1)`, so its word length is
`2 * (ch.G (j + 1)).n + 2 * (ch.G (j + 1)).m + 1`. -/
private lemma ordRotWords_le_of_chainInv {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {ch : ChainState cfg.T cfg.P} (hInv : Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    {j : ℕ} (hj : j < cfg.P.d) :
    ordRotWords (chainLevelOrdAbs ch j) (ch.bran j) ≤
      1 + 2 * (ch.G (j + 1)).n + 2 * (ch.G (j + 1)).m := by
  have hLvl := level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hInv
  have hG1Valid : (ch.G (j + 1)).IsValid := (hLvl (j + 1) (by omega)).1
  have hGeq : cfg.T.S (ch.scState j) (ch.bran j) = ch.G (j + 1) := (hInv.hGSucc j hj).symm
  obtain ⟨H⟩ := hInv.hHist j hj
  have hSpec := H.hOK.noHidden cfg.P.k H.len (levelM cfg.TP cfg.P j) cfg.N₀ H.D H.ord H.restarts
    cfg.P.hk H.hG0 H.hD H.hLen H.hℓPos H.hOrd H.hInitMBound H.hInitNBound H.hRestartsLt
    (by rw [H.hUpd]; exact H.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hOut := hSpec.2.2.2.2.1 H.s₀ H.len H.hs₀ le_rfl (ch.bran j) (hInv.hBran j hj)
    H.hS0Fresh H.hNoRestartAfterS0
  have hRot0 := Chain.Ordered.rotation_of_orderedUpTo hOut (le_refl (H.len - H.s₀))
  have hadd : H.s₀ + (H.len - H.s₀) = H.len := by have := H.hs₀; omega
  have hRot : IsRotationOrder (ch.G (j + 1)) (cfg.T.rot (ch.scState j) (ch.bran j)) := by
    refine Chain.Ordered.exists_rotation_of_eq ?_ ?_ hRot0
    · simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hadd, ← H.hRun, hGeq]
    · simp only [hadd, ← H.hRun]
  unfold ordRotWords chainLevelOrdAbs
  dsimp only
  rw [hGeq, ordWordsOn_eq_of_isRotationOrder hG1Valid hRot]
  omega

/-- Derives all fields of `ShiftDeepModelInvKFBL model i` from `ShiftLoopChainInv cfg model.chain`
and `cfg.ValidOrdNoHidden`. -/
theorem shiftDeepModelInvKFBL_of_shiftLoopChainInv {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {model : Alg2State cfg} (h : Ordered.ShiftLoopChainInv cfg model.chain)
    (i : Fin (cfg.P.d + 1)) :
    ShiftDeepModelInvKFBL model i := by
  have hNext : Ordered.ShiftLoopChainInv cfg (alg2LoopShiftStep cfg model i).chain :=
    h.shift hV i.val (Nat.lt_succ_iff.mp i.isLt)
  set next := (alg2LoopShiftStep cfg model i).chain
  have hLvl0 := level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk h.1
  have hLvlN := level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hNext.1
  refine ⟨shiftLoopLevelFacts_of_inv hV h, shiftLoopLevelFacts_of_inv hV hNext,
    fun j _ hj => ordRotWords_le_of_chainInv hV hNext.1 hj,
    fun j hj => ?_, fun j _ hj => ?_, ?_, ?_, fun j hj => (hLvlN j hj).1,
    fun j hj => by exact_mod_cast (hLvlN j hj).2.2.1,
    (ChainInv.levels_connected hV.hTP hV.hγM₀ hV.hγk hNext.1 hNext.2.2.2 cfg.P.d le_rfl).1, ?_⟩
  · exact (Finset.card_le_card (hLvlN j hj).2.1).trans (hNext.1.hN0 ▸ hNext.1.hG0n)
  · have hAct0 := (hLvl0 j (le_of_lt hj)).2.2.2.2 hj (model.chain.bran j) (h.1.hBran j hj)
    have hActN := (hLvlN j (le_of_lt hj)).2.2.2.2 hj (next.bran j) (hNext.1.hBran j hj)
    have hV0 : (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.V ⊆
        (model.chain.G j).V := le_of_eq hAct0.1.2.1.2.1
    have hE0 : (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.E ⊆
        (model.chain.G j).E := hAct0.1.2.1.2.2.2.2.2.1
    have hG0 : (model.chain.G (j + 1)).E ⊆ (model.chain.G j).E := by
      rw [h.1.hGSucc j hj]
      exact hAct0.2.1.2.1.trans Finset.sdiff_subset
    have hEN : (cfg.T.lsfs (next.scState j) (next.bran j)).F.F.E ⊆ (next.G j).E :=
      hActN.1.2.1.2.2.2.2.2.1
    have hGN : (next.G (j + 1)).E ⊆ (next.G j).E := by
      rw [hNext.1.hGSucc j hj]
      exact hActN.2.1.2.1.trans Finset.sdiff_subset
    exact ⟨hV0, hE0, hG0, hEN, hGN⟩
  · exact (h.1.hLastHolds model.chain.lastBran h.1.hLastBran).2.1.2.2.2.2.2.1
  · exact (hNext.1.hLastHolds next.lastBran hNext.1.hLastBran).2.1.2.2.2.2.2.1
  · have hSub0 : ∀ j ≤ cfg.P.d, (next.G j).E ⊆ (next.G 0).E := by
      intro j
      induction j with
      | zero => intro _; exact Finset.Subset.refl _
      | succ j ih =>
        intro hj
        have hActN := (hLvlN j (le_of_lt hj)).2.2.2.2 hj (next.bran j) (hNext.1.hBran j hj)
        have hGN : (next.G (j + 1)).E ⊆ (next.G j).E := by
          rw [hNext.1.hGSucc j hj]
          exact hActN.2.1.2.1.trans Finset.sdiff_subset
        exact hGN.trans (ih (Nat.le_of_lt hj))
    have hG0Eq : next.G 0 = model.chain.G 0 := by
      by_cases hiLt : i.val < cfg.P.d
      · exact (ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P model.chain hiLt).1 0 (Nat.zero_le _)
      · simp [next, alg2LoopShiftStep, Ordered.algorithm1_shift, hiLt]
    exact hG0Eq ▸ Finset.card_le_card (hSub0 cfg.P.d le_rfl)

/-! ## Discharging `DeepShiftOpsHypKFBL.restartSpaceDom` and `levelSpaceDom` -/

private lemma wireCoreLenEdgeSpace_mono {K₁ K₂ : ℕ} (h : K₁ ≤ K₂) :
    wireCoreLenEdgeSpace K₁ ≤ wireCoreLenEdgeSpace K₂ := by
  unfold wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
  have hmul : 5 * (2 * K₁) * (2 * K₁ + 1) ≤ 5 * (2 * K₂) * (2 * K₂ + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 5 (by omega)) (by omega)
  omega

/-- `ordLevelSpace` is monotone in `initSp`, `M`, `N`, and `nextM`. -/
theorem ordLevelSpace_mono {L capExp capLimit initSp₁ initSp₂ M₁ M₂ N₁ N₂ nextM₁ nextM₂ : ℕ}
    (hSp : initSp₁ ≤ initSp₂) (hM : M₁ ≤ M₂) (hN : N₁ ≤ N₂) (hNext : nextM₁ ≤ nextM₂) :
    ordLevelSpace L capExp capLimit initSp₁ M₁ N₁ nextM₁ ≤
      ordLevelSpace L capExp capLimit initSp₂ M₂ N₂ nextM₂ := by
  unfold ordLevelSpace
  dsimp only
  have hLw : ordLevelLwMax L capExp M₁ N₁ ≤ ordLevelLwMax L capExp M₂ N₂ := by
    unfold ordLevelLwMax
    have hlog : Nat.log 2 (M₁ + N₁ + 2) ≤ Nat.log 2 (M₂ + N₂ + 2) :=
      Nat.log_mono_right (by omega)
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  have hEdge := Nat.mul_le_mul hNext (wireCoreLenEdgeSpace_mono hLw)
  omega

/-- Discharges `DeepShiftOpsHypKFBL.restartSpaceDom` at
`ordLevelSpace L capExp capLimit op1Space (levelM cfg.TP cfg.P 0) cfg.N₀ (levelM cfg.TP cfg.P 0)`
from a uniform upper bound `op1Space` on op `1`'s allocation. -/
theorem deepShift_restartSpaceDom
    {L capExp capLimit op1Space : ℕ} {cfg : Alg2Config} {allocation : ℕ → List ℕ → ℕ}
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (hAlloc1 : ∀ coreH b h, allocation 1 [coreH, b, h] ≤ op1Space)
    (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)) (coreH h : ℕ)
    (hiLt : i.val < cfg.P.d)
    (hN0 : model.chain.N₀ = cfg.N₀)
    (hLvlM : ∀ j < cfg.P.d, model.chain.lvlM j = levelM cfg.TP cfg.P j)
    (hModelK : ShiftDeepModelInvKFBL model i) :
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    let newBran := (model.chain.bran i.val + 1) % cfg.P.k
    ordLevelSpace L capExp capLimit (allocation 1 [coreH, newBran, h])
      (model.chain.lvlM i.val) model.chain.N₀ (next.G (i.val + 1)).m ≤
      ordLevelSpace L capExp capLimit op1Space (levelM cfg.TP cfg.P 0) cfg.N₀
        (levelM cfg.TP cfg.P 0) := by
  dsimp only
  have hNextM : ((Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1.G
      (i.val + 1)).m ≤ levelM cfg.TP cfg.P (i.val + 1) :=
    hModelK.2.2.2.2.2.2.2.2.1 (i.val + 1) (by omega)
  exact ordLevelSpace_mono (hAlloc1 coreH _ h)
    ((hLvlM i.val hiLt).symm ▸ levelM_le_levelM_zero hTP hγk i.val)
    (le_of_eq hN0)
    (hNextM.trans (levelM_le_levelM_zero hTP hγk (i.val + 1)))

/-- Discharges `DeepShiftOpsHypKFBL.levelSpaceDom` at
`ordLevelSpace L capExp capLimit (initSpace j) (levelM cfg.TP cfg.P j) cfg.N₀ (levelM cfg.TP cfg.P (j + 1))`
from a per-level upper bound `initSpace j` on op `6`'s allocation. -/
theorem deepShift_levelSpaceDom
    {w L capExp capLimit : ℕ} {fmt : Num.Format w} {cfg : Alg2Config}
    {allocation : ℕ → List ℕ → ℕ} (initSpace : ℕ → ℕ)
    (hAlloc6 : ∀ j < cfg.P.d, ∀ g l gr o h,
      allocation 6 [g, l, gr, o, cfg.P.k, levelM cfg.TP cfg.P j, cfg.N₀, L, fmt.precision,
        Expander.chosenL (cfg.P.M₀ ^ 2), h] ≤ initSpace j)
    (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)) (j g l gr o h : ℕ)
    (hiLt : i.val < cfg.P.d) (_hj1 : i.val + 1 ≤ j) (hj2 : j < cfg.P.d)
    (hN0 : model.chain.N₀ = cfg.N₀)
    (hLvlM : ∀ r < cfg.P.d, model.chain.lvlM r = levelM cfg.TP cfg.P r)
    (hModelK : ShiftDeepModelInvKFBL model i) :
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    ordLevelSpace L capExp capLimit
      (allocation 6 [g, l, gr, o, cfg.P.k, next.lvlM j, next.N₀, L, fmt.precision,
        Expander.chosenL (cfg.P.M₀ ^ 2), h])
      (next.lvlM j) next.N₀ (next.G (j + 1)).m ≤
      ordLevelSpace L capExp capLimit (initSpace j) (levelM cfg.TP cfg.P j) cfg.N₀
        (levelM cfg.TP cfg.P (j + 1)) := by
  dsimp only
  have hEx := ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P model.chain hiLt
  have hNextLvlM : (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1.lvlM j =
      levelM cfg.TP cfg.P j := by
    rw [hEx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    exact hLvlM j hj2
  have hNextN0 : (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1.N₀ =
      cfg.N₀ :=
    hEx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.trans hN0
  have hNextM : ((Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1.G
      (j + 1)).m ≤ levelM cfg.TP cfg.P (j + 1) :=
    hModelK.2.2.2.2.2.2.2.2.1 (j + 1) (by omega)
  rw [hNextLvlM, hNextN0]
  exact ordLevelSpace_mono (hAlloc6 j hj2 g l gr o h) le_rfl le_rfl hNextM

/-- Assembles a complete `DeepShiftOpsHypKFBL` witness for `sparseCoreBundleRestartToolMachWith`
at `deepShiftLevelCost`, `deepShiftFixedBound`, `deepShiftToolMulBound`, and per-level space
bounds `ordLevelSpace`. -/
theorem deepShiftOpsHypKFBL_of_mach
    (lsfInit : LSFInit) (C_lsst : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    {w L capExp capLimit fcap lastMul intCapMax forestEdgeCap deepSpace op1Space lastSpace : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {allocation : ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    (initSpace : ℕ → ℕ)
    (hT : cfg.T = sparseCoreBundleRestartToolMachWith lsfInit C_lsst depth sparsify params spanConst)
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (hAlloc1 : ∀ coreH b h, allocation 1 [coreH, b, h] ≤ op1Space)
    (hAlloc6 : ∀ j < cfg.P.d, ∀ g l gr o h,
      allocation 6 [g, l, gr, o, cfg.P.k, levelM cfg.TP cfg.P j, cfg.N₀, L, fmt.precision,
        Expander.chosenL (cfg.P.M₀ ^ 2), h] ≤ initSpace j)
    (hLastSp : ∀ gB lB h, lastAlloc 1 [gB, lB, L, fmt.precision, h] ≤ lastSpace)
    (hSpaceTot :
      2 * (cfg.P.d + 1) + (5 + fcap + 5 * cfg.P.d) +
        ordLevelSpace L capExp capLimit op1Space (levelM cfg.TP cfg.P 0) cfg.N₀
          (levelM cfg.TP cfg.P 0) +
        (Finset.range cfg.P.d).sum (fun j =>
          ordLevelSpace L capExp capLimit (initSpace j) (levelM cfg.TP cfg.P j) cfg.N₀
            (levelM cfg.TP cfg.P (j + 1))) +
        lastSpace + 5 * cfg.P.d +
        3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L) ≤ deepSpace) :
    DeepShiftOpsHypKFBL (w := w) (L := L) (capExp := capExp) (capLimit := capLimit)
      (fcap := fcap) (lastMul := lastMul) (intCapMax := intCapMax)
      (forestEdgeCap := forestEdgeCap) (deepSpace := deepSpace)
      (deepFixed := deepShiftFixedBound Psc (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d lastMul)
      (toolMul := deepShiftToolMulBound L capExp Psc (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d lastMul)
      (fmt := fmt) (cfg := cfg) (Psc := Psc) (allocation := allocation) (lastAlloc := lastAlloc)
      (ordLevelSpace L capExp capLimit op1Space (levelM cfg.TP cfg.P 0) cfg.N₀
        (levelM cfg.TP cfg.P 0))
      (fun j => ordLevelSpace L capExp capLimit (initSpace j) (levelM cfg.TP cfg.P j) cfg.N₀
        (levelM cfg.TP cfg.P (j + 1)))
      (deepShiftLevelCost L capExp cfg Psc) lastSpace where
  restartSpaceDom := fun model i coreH h hiLt hN0 hLvlM hModelK =>
    deepShift_restartSpaceDom hTP hγk hAlloc1 model i coreH h hiLt hN0 hLvlM hModelK
  levelSpaceDom := fun model i j g l gr o h hiLt hj1 hj2 hN0 hLvlM hModelK =>
    deepShift_levelSpaceDom initSpace hAlloc6 model i j g l gr o h hiLt hj1 hj2 hN0 hLvlM hModelK
  lastSpaceDom := hLastSp
  spaceTotal := hSpaceTot
  levelCostDom := fun model i j _ _ _ => deepShift_levelCostDom L capExp cfg Psc model i j
  costTotal := fun model i hiLt _ hInI hModelK =>
    deepShift_costTotal_mach lsfInit C_lsst depth sparsify params spanConst L capExp lastMul
      cfg Psc hT hTP hγk model i hiLt hInI hModelK

end MinCostFlow.MinRatio

end
