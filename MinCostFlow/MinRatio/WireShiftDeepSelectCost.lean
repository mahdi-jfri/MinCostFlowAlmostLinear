module

public import MinCostFlow.MinRatio.WireShiftDeepSelectFinalize
public import MinCostFlow.MinRatio.WireShiftDeepCostKFBL
public import MinCostFlow.MinRatio.WireSelectUpdate
import Mathlib.Tactic

/-!
# Space and amortized cost bounds for deep-shift select refresh (`WireShiftDeepSelectCost`)

Bounds the scratch space and amortized step cost (including the re-embedding potential change
`K * (chainReembPot pot next - chainReembPot pot chain)`) of refreshing the select region after a
deep shift at level `i < d` (`WireShiftDeepSelect.lean`):

* `shiftDeepSelectSpaceBound`: closed-form `PolyNat` scratch bound independent of `mem`, `model`,
  and `i`, dominating the interior refresh loop, terminal `op 3`, terminal level fill, and
  suffix finalize (`shiftDeepSelectSpace_le_bound`).
* `shiftDeepSelectFixedBound`: closed-form `SubpolyNat` fixed-cost bound with zero factor of `m`.
* `shiftDeepSelectToolMulBound`: per-tool-cost multiplier `4 * K + (18 * slot + 80) +
  1800 * (d + 1) * (L + 1) + 2 * (selCoreLenEdgeCost L LwMax₀ + 40) + 70 * d + 2310`, fitting
  strictly inside `3 * dryKeyCost + drySelectToolMulExtra` (`WireSelectSizes.lean`).
* `shiftDeepSelect_amortized_cost_le`: discharges the full amortized select-refresh cost into
  `shiftDeepSelectFixedBound + shiftDeepSelectToolMulBound * (next.totalRuntime - chain.totalRuntime)`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

/-- Closed-form scratch-space upper bound for the deep-shift select refresh tail (after
`shiftDeepChainProc` finishes). -/
def shiftDeepSelectSpaceBound (d vCap eCap cap L capExp M₀ N₀ evalSpace : ℕ) : ℕ :=
  let LwMax₀ := ordLevelLwMax L capExp M₀ N₀
  d * (7 + eCap * (selCoreLenEdgeSpace L LwMax₀ + 4)) + 1 +
    eCap * (6 + selCoreLenEdgeSpace L LwMax₀) +
    (d + 1) * selectPhiFillSpace d vCap L +
    eCap * heapRebalanceSpace cap L +
    (d + 1) * eCap * selectProcessEdgeSpace cap L evalSpace

/-- Closed-form fixed-cost upper bound for the deep-shift select refresh tail (depends only on
`readoutCost`, `d`, and `L`; no linear `m` factor). -/
def shiftDeepSelectFixedBound (readoutCost d L : ℕ) : ℕ :=
  (2 * d + 1) * readoutCost +
    (d + 1) * (1800 * (d + 1) * (L + 1) + 1700) + 2800

/-- Per-tool-cost multiplier for the deep-shift select refresh tail (including
`K * (chainReembPot pot next - chainReembPot pot chain)`). -/
def shiftDeepSelectToolMulBound (d L capExp M₀ N₀ slot K : ℕ) : ℕ :=
  let LwMax₀ := ordLevelLwMax L capExp M₀ N₀
  4 * K + (18 * slot + 80) + 1800 * (d + 1) * (L + 1) +
    2 * (selCoreLenEdgeCost L LwMax₀ + 40) + 70 * d + 2310

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

private lemma one_le_bundleLogFactor_sel (M N : ℕ) : 1 ≤ SparseCore.bundleLogFactor M N := by
  unfold SparseCore.bundleLogFactor
  have h1 : 1 ≤ Nat.log 2 (M + N + 2) + 1 := Nat.succ_pos _
  nlinarith

private lemma ordLevelLwMax_mono_sel {L capExp M₁ M₂ N : ℕ} (h : M₁ ≤ M₂) :
    ordLevelLwMax L capExp M₁ N ≤ ordLevelLwMax L capExp M₂ N := by
  unfold ordLevelLwMax
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1)) _

private lemma selCoreLenEdgeSpace_mono_sel {L Lw₁ Lw₂ : ℕ} (h : Lw₁ ≤ Lw₂) :
    selCoreLenEdgeSpace L Lw₁ ≤ selCoreLenEdgeSpace L Lw₂ := by
  unfold selCoreLenEdgeSpace wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
  have hm := max_le_max_left L h
  have := Nat.mul_le_mul (show 5 * (2 * max L Lw₁) ≤ 5 * (2 * max L Lw₂) by omega)
    (show 2 * max L Lw₁ + 1 ≤ 2 * max L Lw₂ + 1 by omega)
  omega

private lemma selCoreLenEdgeCost_mono_sel {L Lw₁ Lw₂ : ℕ} (h : Lw₁ ≤ Lw₂) :
    selCoreLenEdgeCost L Lw₁ ≤ selCoreLenEdgeCost L Lw₂ := by
  unfold selCoreLenEdgeCost wireCoreLenEdgeCost
  have hm := max_le_max_left L h
  have := Nat.mul_le_mul hm hm
  nlinarith

private lemma selectPhiFillSpace_mono {j₁ j₂ n₁ n₂ L : ℕ} (hj : j₁ ≤ j₂) (hn : n₁ ≤ n₂) :
    selectPhiFillSpace j₁ n₁ L ≤ selectPhiFillSpace j₂ n₂ L := by
  unfold selectPhiFillSpace phiFillEdgeStepSpace
  have hmul : n₁ * ((3 * j₁ + 3) * L) ≤ n₂ * ((3 * j₂ + 3) * L) :=
    Nat.mul_le_mul hn (Nat.mul_le_mul_right L (by omega))
  omega

private lemma chain_G_E_subset_sel {T : SparseCoreRestartTool} {P : ChainParams}
    {chain : ChainState T P} {first : ℕ}
    (hStep : ∀ j, first ≤ j → j < P.d → (chain.G (j + 1)).E ⊆ (chain.G j).E) :
    ∀ j, first ≤ j → j ≤ P.d → (chain.G j).E ⊆ (chain.G first).E := by
  intro j h1 h2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h1
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih =>
    exact (hStep (first + k) (by omega) (by omega)).trans (ih (by omega) (by omega))

private lemma dgCopyRefillCost_le_linear {nOld mOld nNew mNew : ℕ}
    (hnO : nOld ≤ mOld + 1) (hnN : nNew ≤ mNew + 1) :
    dgCopyRefillCost nOld mOld nNew mNew ≤ 70 * mOld + 710 * mNew + 530 := by
  unfold dgCopyRefillCost dgRefillFromListsCost
  omega

/-- The actual scratch space used by the deep-shift select refresh tail is bounded by the
closed-form `shiftDeepSelectSpaceBound`. -/
theorem shiftDeepSelectSpace_le_bound
    {cfg : Alg2Config} {G₀ G₀' : MGraph} {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {P vCap eCap L capExp evalSpace sizeOld : ℕ} {loc : SelectHeapLoc}
    {mem : ℕ → ℕ} {model : Alg2State cfg} {i : Fin (cfg.P.d + 1)}
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (_hiLt : i.val < cfg.P.d)
    (hModelK : ShiftDeepModelInvKFBL model i)
    (hmodOld : SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c)
    (hmodNew : SelectModelInv (alg2LoopShiftStep cfg model i) G₀' σ' σ'_mwu γ'_ℓ γ'_c)
    (hMatchOld : SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain model.chain.g
      model.chain.ℓ sizeOld)
    (hOldEcap : (model.chain.G i.val).m ≤ eCap)
    (hNewEcap : ∀ j ≤ cfg.P.d, ((alg2LoopShiftStep cfg model i).chain.G j).m ≤ eCap)
    (hNewVcap : ∀ j ≤ cfg.P.d, ((alg2LoopShiftStep cfg model i).chain.G j).n ≤ vCap)
    (hLocLk : loc.Lk = L) :
    let next := (alg2LoopShiftStep cfg model i).chain
    let M₀ := levelM cfg.TP cfg.P 0
    selectInitInteriorLoopSpace next i.val L capExp + 1 +
      selectFillLastLevelSpace (next.G cfg.P.d).m (next.lastLSFs next.lastBran).F.F.m L +
      selectRefreshFinalizeSpace mem loc next.toTreeChain i.val L evalSpace ≤
      shiftDeepSelectSpaceBound cfg.P.d vCap eCap loc.cap L capExp M₀ cfg.N₀ evalSpace := by
  intro next M₀
  let i0 := i.val
  let d := cfg.P.d
  set LwMax₀ := ordLevelLwMax L capExp M₀ cfg.N₀
  rcases hModelK with ⟨_, hLvlN, _, _, hSub, _, hLastNew, _, _, _, _⟩
  have hLvlMN : next.lvlM = levelM cfg.TP cfg.P := hLvlN.2.1
  have hN0N : next.N₀ = cfg.N₀ := hLvlN.2.2.1
  have hLwLe : ∀ j < d,
      L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (next.lvlM j + next.N₀ + 2) + 1) ≤
        LwMax₀ := fun j _ => by
    change ordLevelLwMax L capExp (next.lvlM j) next.N₀ ≤ ordLevelLwMax L capExp M₀ cfg.N₀
    rw [hLvlMN, hN0N]
    exact ordLevelLwMax_mono_sel (levelM_le_levelM_zero hTP hγk j)
  -- 1. Interior loop space
  have hIntLe : selectInitInteriorLoopSpace next i0 L capExp ≤
      d * (7 + eCap * (selCoreLenEdgeSpace L LwMax₀ + 4)) := by
    unfold selectInitInteriorLoopSpace
    calc (Finset.Ico i0 d).sum (fun j =>
          selectFillInteriorLevelSpace (next.G j).m (next.toTreeChain.activeLSF j).F.F.m L
            (L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (next.lvlM j + next.N₀ + 2) + 1)))
        ≤ (Finset.Ico i0 d).sum (fun _ => 7 + eCap * (selCoreLenEdgeSpace L LwMax₀ + 4)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
          unfold selectFillInteriorLevelSpace
          have hGm : (next.G j).m ≤ eCap := hNewEcap j (le_of_lt hj2)
          have hFm : (next.toTreeChain.activeLSF j).F.F.m ≤ (next.G j).m := by
            have hact : next.toTreeChain.activeLSF j = cfg.T.lsfs (next.scState j) (next.bran j) := by
              simp [TreeChain.activeLSF, ChainState.toTreeChain, show j < cfg.P.d from hj2]
            rw [hact]
            exact Finset.card_le_card (hSub j hj1 hj2).2.2.2.1
          have hSp := selCoreLenEdgeSpace_mono_sel (L := L) (hLwLe j hj2)
          have hmul : (next.G j).m * selCoreLenEdgeSpace L
              (L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (next.lvlM j + next.N₀ + 2) + 1)) ≤
              eCap * selCoreLenEdgeSpace L LwMax₀ := Nat.mul_le_mul hGm hSp
          have hEq : eCap * (selCoreLenEdgeSpace L LwMax₀ + 4) =
              eCap * selCoreLenEdgeSpace L LwMax₀ + 4 * eCap := by ring
          omega
      _ = (d - i0) * (7 + eCap * (selCoreLenEdgeSpace L LwMax₀ + 4)) := by simp
      _ ≤ d * (7 + eCap * (selCoreLenEdgeSpace L LwMax₀ + 4)) :=
          Nat.mul_le_mul_right _ (Nat.sub_le d i0)
  -- 2. Last-level fill space
  have hLastLe : selectFillLastLevelSpace (next.G d).m (next.lastLSFs next.lastBran).F.F.m L ≤
      eCap * (6 + selCoreLenEdgeSpace L LwMax₀) := by
    unfold selectFillLastLevelSpace
    have hGm : (next.G d).m ≤ eCap := hNewEcap d le_rfl
    have hFm : (next.lastLSFs next.lastBran).F.F.m ≤ (next.G d).m := Finset.card_le_card hLastNew
    have hLw0 : L ≤ LwMax₀ := by unfold LwMax₀ ordLevelLwMax; omega
    have hSp := selCoreLenEdgeSpace_mono_sel (L := L) hLw0
    have hmul : (next.G d).m * selCoreLenEdgeSpace L L ≤ eCap * selCoreLenEdgeSpace L LwMax₀ :=
      Nat.mul_le_mul hGm hSp
    have hEq : eCap * (6 + selCoreLenEdgeSpace L LwMax₀) =
        6 * eCap + eCap * selCoreLenEdgeSpace L LwMax₀ := by ring
    omega
  -- 3. Phi-loop space
  have hPhiLe : selectPhiLoopSpace next.toTreeChain i0 L ≤ (d + 1) * selectPhiFillSpace d vCap L := by
    unfold selectPhiLoopSpace
    have hEach : ∀ j ∈ Finset.Icc i0 d,
        selectPhiFillSpace j (next.toTreeChain.activeLSF j).F.F.n L ≤ selectPhiFillSpace d vCap L := by
      intro j hj
      have hjLe : j ≤ d := (Finset.mem_Icc.mp hj).2
      have hFn : (next.toTreeChain.activeLSF j).F.F.n ≤ vCap := by
        have hVeq : (next.toTreeChain.activeLSF j).F.F.V = (next.G j).V := by
          by_cases hlt : j < d
          · have hBr := (hmodNew.1.2.2.2.2.1 j hlt).1
            have hHlsf := ((hmodNew.1.2.2.2.2.1 j hlt).2.1 (next.bran j) hBr).1
            simpa [TreeChain.activeLSF, ChainState.toTreeChain, d, hlt] using hHlsf.2.1.2.1
          · have hjd : j = d := by omega
            subst hjd
            have hBr := hmodNew.1.2.2.2.2.2.1
            have hHlsf := hmodNew.1.2.2.2.2.2.2.1 next.lastBran hBr
            simpa [TreeChain.activeLSF, ChainState.toTreeChain, d] using hHlsf.2.1.2.1
        change (next.toTreeChain.activeLSF j).F.F.V.card ≤ vCap
        rw [hVeq]; exact hNewVcap j hjLe
      exact selectPhiFillSpace_mono hjLe hFn
    calc (Finset.Icc i0 next.toTreeChain.d).sum (fun j => selectPhiFillSpace j (next.toTreeChain.activeLSF j).F.F.n L)
        ≤ (Finset.Icc i0 d).sum (fun _ => selectPhiFillSpace d vCap L) := Finset.sum_le_sum hEach
      _ = (d + 1 - i0) * selectPhiFillSpace d vCap L := by simp
      _ ≤ (d + 1) * selectPhiFillSpace d vCap L := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  -- 4. Rebuild-suffix space
  have hOldSub : ∀ j, i0 ≤ j → j ≤ d → (model.chain.toTreeChain.G j).E ⊆ (model.chain.toTreeChain.G i0).E :=
    chain_G_E_subset_sel fun j hj1 hj2 => (hSub j hj1 hj2).2.2.1
  have hCandSum : (Finset.Icc i0 d).sum (fun j => levelCandCount mem loc j) ≤ eCap :=
    (selectHeapMatchesChain_levelCandCount_sum_le hmodOld.1 hMatchOld hOldSub).trans hOldEcap
  have hSufLe : selectRebuildSuffixSpace mem loc next.toTreeChain i0 evalSpace ≤
      eCap * heapRebalanceSpace loc.cap L + (d + 1) * eCap * selectProcessEdgeSpace loc.cap L evalSpace := by
    unfold selectRebuildSuffixSpace selectRebuildLevelSpace heapClearLevelSpace selectProcessListSpace
    rw [Finset.sum_add_distrib, hLocLk]
    have h1 : (Finset.Icc i0 d).sum (fun j => levelCandCount mem loc j * heapRebalanceSpace loc.cap L) ≤
        eCap * heapRebalanceSpace loc.cap L := by
      rw [← Finset.sum_mul]
      exact Nat.mul_le_mul_right _ hCandSum
    have h2 : (Finset.Icc i0 d).sum (fun j => (next.toTreeChain.G j).E.card *
          selectProcessEdgeSpace loc.cap L evalSpace) ≤
        (d + 1) * eCap * selectProcessEdgeSpace loc.cap L evalSpace := by
      rw [← Finset.sum_mul]
      refine Nat.mul_le_mul_right _ ?_
      calc (Finset.Icc i0 d).sum (fun j => (next.toTreeChain.G j).E.card)
          ≤ (Finset.Icc i0 d).sum (fun _ => eCap) :=
            Finset.sum_le_sum fun j hj => hNewEcap j (Finset.mem_Icc.mp hj).2
        _ = (d + 1 - i0) * eCap := by simp
        _ ≤ (d + 1) * eCap := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    exact Nat.add_le_add h1 h2
  unfold selectRefreshFinalizeSpace shiftDeepSelectSpaceBound
  dsimp only [LwMax₀, i0, d] at hIntLe hLastLe hPhiLe hSufLe ⊢
  omega

/-- Amortized cost bound for the deep-shift select refresh tail (wrapper + `selTableWrite` +
interior refresh loop + `op 3` + terminal level fill + suffix finalize + re-embedding potential
change `K * (chainReembPot pot next - chainReembPot pot chain)`), charging all graph-size terms
into `shiftDeepSelectToolMulBound * (next.totalRuntime - chain.totalRuntime)` and all remaining
terms into `shiftDeepSelectFixedBound`. -/
theorem shiftDeepSelect_amortized_cost_le
    {cfg : Alg2Config} {G₀ G₀' : MGraph} {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {pot : cfg.T.State → ℕ}
    {P readoutCost L capExp slot evalCost K sizeOld : ℕ} {loc : SelectHeapLoc}
    {mem : ℕ → ℕ} {model : Alg2State cfg} {i : Fin (cfg.P.d + 1)}
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (hMono : ToolCostMono cfg.T)
    (hPot : ToolReembPotFacts cfg.T pot)
    (hRestartLower : ∀ {M N n b : ℕ} {st : cfg.T.State} {G : MGraph} {ord : ℕ → List End},
      SparseCoreOrdInput cfg.T cfg.P.k M N st G ord n → b < cfg.P.k →
      G.m * SparseCore.bundleLogFactor M N ≤ cfg.T.cost (cfg.T.restart st b) - cfg.T.cost st)
    (hInitLower : ∀ {M N : ℕ} {G : MGraph} {ℓ g : ℕ → ℝ} {ord : ℕ → List End},
      G.IsValid →
      3 * G.m * SparseCore.bundleLogFactor M N ≤ cfg.T.cost (cfg.T.initOrd cfg.P.k M N G ℓ g ord))
    (hiLt : i.val < cfg.P.d)
    (hInI : SparseCoreOrdInput cfg.T cfg.P.k (model.chain.lvlM i.val) model.chain.N₀
      (model.chain.scState i.val) (model.chain.G i.val) (model.chain.levelOrd i.val)
      (model.chain.updCount i.val))
    (hModelK : ShiftDeepModelInvKFBL model i)
    (hmodOld : SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c)
    (hmodNew : SelectModelInv (alg2LoopShiftStep cfg model i) G₀' σ' σ'_mwu γ'_ℓ γ'_c)
    (hMatchOld : SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain model.chain.g
      model.chain.ℓ sizeOld)
    (hLocLk : loc.Lk = L)
    (hK : selectProcessEdgeCost loc.cap L evalCost + 60 ≤ K) :
    let chain := model.chain
    let next := (alg2LoopShiftStep cfg model i).chain
    let oldF := fun j => (chain.toTreeChain.activeLSF j).F.F
    let M₀ := levelM cfg.TP cfg.P 0
    (240 * cfg.P.d + 840) +
      selectRefreshInteriorLoopCost oldF next readoutCost i.val L capExp slot +
      readoutCost +
      selectFillLastLevelCost (chain.G cfg.P.d).n (chain.G cfg.P.d).m
        (oldF cfg.P.d).n (oldF cfg.P.d).m
        (next.G cfg.P.d).n (next.G cfg.P.d).m
        (next.lastLSFs next.lastBran).F.F.n (next.lastLSFs next.lastBran).F.F.m L +
      selectRefreshFinalizeCost mem loc next.toTreeChain i.val L evalCost +
      400 +
      K * chainReembPot pot next ≤
      shiftDeepSelectFixedBound readoutCost cfg.P.d L +
        shiftDeepSelectToolMulBound cfg.P.d L capExp M₀ cfg.N₀ slot K *
          (next.totalRuntime - chain.totalRuntime) +
        K * chainReembPot pot chain := by
  intro chain next oldF M₀
  let i0 := i.val
  let d := cfg.P.d
  set LwMax₀ := ordLevelLwMax L capExp M₀ cfg.N₀
  set Δi := cfg.T.cost (next.scState i0) - cfg.T.cost (chain.scState i0)
  set Δrt := next.totalRuntime - chain.totalRuntime
  have hNextEq : next = (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P chain i0).1 := rfl
  rcases hModelK with ⟨hLvl0, hLvlN, _, _, hSub, hLastOld, hLastNew, hValidN, _, _, _⟩
  have hEx := ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P chain hiLt
  have hLvlMN : next.lvlM = levelM cfg.TP cfg.P := hLvlN.2.1
  have hN0N : next.N₀ = cfg.N₀ := hLvlN.2.2.1
  have hNewBranLt : (chain.bran i0 + 1) % cfg.P.k < cfg.P.k := Nat.mod_lt _ cfg.P.hk
  have hDeltaEq :
      Δrt = Δi + (Finset.Ico (i0 + 1) d).sum (fun j => cfg.T.cost (next.scState j)) +
        cfg.L.cost (next.G d) :=
    shiftDeep_totalRuntime_sub cfg.T cfg.L cfg.P chain hiLt
      (hMono.2 (chain.scState i0) ((chain.bran i0 + 1) % cfg.P.k))
  -- Lower bounds on Δi and per-level costs
  have hGi_le_Δi : (chain.G i0).m ≤ Δi := by
    have h1 := hRestartLower hInI hNewBranLt
    have hB := one_le_bundleLogFactor_sel (chain.lvlM i0) chain.N₀
    change (chain.G i0).m ≤
      cfg.T.cost ((Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P chain i0).1.scState i0) -
        cfg.T.cost (chain.scState i0)
    rw [hEx.2.2.1]
    exact (Nat.le_mul_of_pos_right _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hB)).trans h1
  have hNewGi_eq : (next.G i0).E = (chain.G i0).E := by
    change ((Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P chain i0).1.G i0).E = (chain.G i0).E
    rw [hEx.1 i0 le_rfl]
  have hOldSub : ∀ j, i0 ≤ j → j ≤ d → (chain.G j).E ⊆ (chain.G i0).E :=
    chain_G_E_subset_sel fun j hj1 hj2 => (hSub j hj1 hj2).2.2.1
  have hNewSub : ∀ j, i0 ≤ j → j ≤ d → (next.G j).E ⊆ (next.G i0).E :=
    chain_G_E_subset_sel fun j hj1 hj2 => (hSub j hj1 hj2).2.2.2.2
  have hNewGj_le_cost : ∀ j ∈ Finset.Ico (i0 + 1) d, (next.G j).m ≤ cfg.T.cost (next.scState j) := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
    have hscj := (hEx.2.2.2.2.2.2.2.2.1 j hj1 hj2).1
    have h1 := hInitLower (M := chain.lvlM j) (N := chain.N₀) (G := next.G j)
      (ℓ := next.toTreeChain.chainLen chain.ℓ j)
      (g := next.toTreeChain.chainGrad chain.g j) (ord := next.levelOrd j) (hValidN j (le_of_lt hj2))
    have hB := one_le_bundleLogFactor_sel (chain.lvlM j) chain.N₀
    have hscj' : next.scState j = cfg.T.initOrd cfg.P.k (chain.lvlM j) chain.N₀ (next.G j)
        (next.toTreeChain.chainLen chain.ℓ j) (next.toTreeChain.chainGrad chain.g j)
        (next.levelOrd j) := hscj
    rw [hscj']
    have h3 : 3 * (next.G j).m ≤ cfg.T.cost (cfg.T.initOrd cfg.P.k (chain.lvlM j) chain.N₀ (next.G j)
        (next.toTreeChain.chainLen chain.ℓ j) (next.toTreeChain.chainGrad chain.g j) (next.levelOrd j)) :=
      (Nat.le_mul_of_pos_right _ (by omega)).trans h1
    omega
  have hSumIco_le_Δrt : (Finset.Ico i0 d).sum (fun j => (next.G j).m) ≤ Δrt := by
    have hsplit : Finset.Ico i0 d = insert i0 (Finset.Ico (i0 + 1) d) := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have h1 : (next.G i0).m ≤ Δi := by unfold MGraph.m; rw [hNewGi_eq]; exact hGi_le_Δi
    have h2 : (Finset.Ico (i0 + 1) d).sum (fun j => (next.G j).m) ≤
        (Finset.Ico (i0 + 1) d).sum (fun j => cfg.T.cost (next.scState j)) :=
      Finset.sum_le_sum hNewGj_le_cost
    omega
  have hNewGd_le_Δi : (next.G d).m ≤ Δi := by
    have h1 : (next.G d).E ⊆ (chain.G i0).E := hNewGi_eq ▸ hNewSub d (le_of_lt hiLt) le_rfl
    exact (Finset.card_le_card h1).trans hGi_le_Δi
  have hSumIcc_le_2Δrt : (Finset.Icc i0 d).sum (fun j => (next.G j).m) ≤ 2 * Δrt := by
    have hsplit : Finset.Icc i0 d = insert d (Finset.Ico i0 d) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    omega
  -- Monotonicity of LwMax
  have hLwLe : ∀ j < d,
      L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (next.lvlM j + next.N₀ + 2) + 1) ≤
        LwMax₀ := fun j _ => by
    change ordLevelLwMax L capExp (next.lvlM j) next.N₀ ≤ ordLevelLwMax L capExp M₀ cfg.N₀
    rw [hLvlMN, hN0N]
    exact ordLevelLwMax_mono_sel (levelM_le_levelM_zero hTP hγk j)
  -- 1. Interior loop cost
  have hIntCost : selectRefreshInteriorLoopCost oldF next readoutCost i0 L capExp slot ≤
      2 * d * readoutCost + 1110 * d + 10 +
        (70 * d + 750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) * Δrt := by
    unfold selectRefreshInteriorLoopCost
    have hEach : ∀ j ∈ Finset.Ico i0 d,
        selectFillInteriorLevelCost readoutCost (oldF j).n (oldF j).m
          (next.toTreeChain.activeLSF j).F.F.n (next.toTreeChain.activeLSF j).F.F.m (next.G j).m L
          (L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (next.lvlM j + next.N₀ + 2) + 1)) slot + 60 ≤
        (2 * readoutCost + 1110) + 70 * Δi +
          (750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) * (next.G j).m := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      unfold selectFillInteriorLevelCost
      have hactOld : oldF j = (cfg.T.lsfs (chain.scState j) (chain.bran j)).F.F := by
        simp [oldF, TreeChain.activeLSF, ChainState.toTreeChain, show j < cfg.P.d from hj2]
      have hactNew : (next.toTreeChain.activeLSF j).F.F = (cfg.T.lsfs (next.scState j) (next.bran j)).F.F := by
        simp [TreeChain.activeLSF, ChainState.toTreeChain, show j < cfg.P.d from hj2]
      have holdM : (oldF j).m ≤ Δi := by
        rw [hactOld]
        exact (Finset.card_le_card ((hSub j hj1 hj2).2.1.trans (hOldSub j hj1 (le_of_lt hj2)))).trans hGi_le_Δi
      have holdN' : (oldF j).n ≤ Δi + 1 := by
        have hV : (oldF j).V ⊆ (chain.G j).V := hactOld ▸ (hSub j hj1 hj2).1
        have hGm : (chain.G j).m ≤ Δi := (Finset.card_le_card (hOldSub j hj1 (le_of_lt hj2))).trans hGi_le_Δi
        exact (Finset.card_le_card hV).trans ((hLvl0.1 j (le_of_lt hj2)).trans (Nat.add_le_add_right hGm 1))
      have hnewM : (next.toTreeChain.activeLSF j).F.F.m ≤ (next.G j).m := by
        rw [hactNew]; exact Finset.card_le_card (hSub j hj1 hj2).2.2.2.1
      have hnewN : (next.toTreeChain.activeLSF j).F.F.n ≤ (next.G j).m + 1 := by
        have hBr := (hmodNew.1.2.2.2.2.1 j hj2).1
        have hHlsf := ((hmodNew.1.2.2.2.2.1 j hj2).2.1 (next.bran j) hBr).1
        have hVeq : (next.toTreeChain.activeLSF j).F.F.V = (next.G j).V := by
          rw [hactNew]; exact hHlsf.2.1.2.1
        change (next.toTreeChain.activeLSF j).F.F.V.card ≤ (next.G j).m + 1
        rw [hVeq]
        exact hLvlN.1 j (le_of_lt hj2)
      have hDG : dgCopyRefillCost (oldF j).n (oldF j).m
          (next.toTreeChain.activeLSF j).F.F.n (next.toTreeChain.activeLSF j).F.F.m ≤
          70 * Δi + 710 * (next.G j).m + 530 := by
        unfold dgCopyRefillCost dgRefillFromListsCost; omega
      have hCL := Nat.mul_le_mul_left (next.G j).m (Nat.add_le_add_right
        (selCoreLenEdgeCost_mono_sel (L := L) (hLwLe j hj2)) 40)
      have hEq : (750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) * (next.G j).m =
          710 * (next.G j).m + 40 * (next.G j).m +
            (next.G j).m * (selCoreLenEdgeCost L LwMax₀ + 40) + (next.G j).m * (18 * slot + 80) := by ring
      omega
    have hSum := Finset.sum_le_sum hEach
    conv_rhs at hSum =>
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
        ← Finset.mul_sum]
    simp only [Nat.card_Ico, smul_eq_mul] at hSum
    have h1 : (d - i0) * (2 * readoutCost + 1110) ≤ 2 * d * readoutCost + 1110 * d := by
      have := Nat.mul_le_mul_right (2 * readoutCost + 1110) (Nat.sub_le d i0); nlinarith
    have h2 : (d - i0) * (70 * Δi) ≤ 70 * d * Δrt := by
      have hdi : d - i0 ≤ d := Nat.sub_le d i0
      have hΔ : Δi ≤ Δrt := by omega
      calc (d - i0) * (70 * Δi) ≤ d * (70 * Δrt) := Nat.mul_le_mul hdi (Nat.mul_le_mul_left 70 hΔ)
        _ = 70 * d * Δrt := by ring
    have h3 : (750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) *
          (Finset.Ico i0 d).sum (fun j => (next.G j).m) ≤
        (750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) * Δrt :=
      Nat.mul_le_mul_left _ hSumIco_le_Δrt
    have hEq : (70 * d + 750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) * Δrt =
        70 * d * Δrt + (750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) * Δrt := by ring
    have hSum' : (Finset.Ico i0 cfg.P.d).sum (fun j =>
        let LwMax := L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (next.lvlM j + next.N₀ + 2) + 1)
        selectFillInteriorLevelCost readoutCost (oldF j).n (oldF j).m
          (next.toTreeChain.activeLSF j).F.F.n (next.toTreeChain.activeLSF j).F.F.m (next.G j).m L LwMax slot + 60) ≤
        (d - i0) * (2 * readoutCost + 1110) + (d - i0) * (70 * Δi) +
          (750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) *
            (Finset.Ico i0 d).sum (fun j => (next.G j).m) := hSum
    omega
  -- 2. Terminal level fill cost
  have hLastCost :
      selectFillLastLevelCost (chain.G d).n (chain.G d).m (oldF d).n (oldF d).m
        (next.G d).n (next.G d).m
        (next.lastLSFs next.lastBran).F.F.n (next.lastLSFs next.lastBran).F.F.m L ≤
      1380 + (1560 + (selCoreLenEdgeCost L LwMax₀ + 40)) * Δrt := by
    unfold selectFillLastLevelCost
    have hOldGdM : (chain.G d).m ≤ Δi :=
      (Finset.card_le_card (hOldSub d (le_of_lt hiLt) le_rfl)).trans hGi_le_Δi
    have hOldGdN : (chain.G d).n ≤ Δi + 1 :=
      (hLvl0.1 d le_rfl).trans (by change (chain.G d).m + 1 ≤ Δi + 1; omega)
    have hNewGdN : (next.G d).n ≤ Δi + 1 :=
      (hLvlN.1 d le_rfl).trans (by change (next.G d).m + 1 ≤ Δi + 1; omega)
    have hOldFdM : (oldF d).m ≤ Δi := by
      have hact : oldF d = (chain.lastLSFs chain.lastBran).F.F := by
        simp [oldF, TreeChain.activeLSF, ChainState.toTreeChain, d]
      rw [hact]; exact (Finset.card_le_card hLastOld).trans hOldGdM
    have hOldFdN : (oldF d).n ≤ Δi + 1 := by
      have hact : oldF d = (chain.lastLSFs chain.lastBran).F.F := by
        simp [oldF, TreeChain.activeLSF, ChainState.toTreeChain, d]
      have hBr := hmodOld.1.2.2.2.2.2.1
      have hHlsf := hmodOld.1.2.2.2.2.2.2.1 chain.lastBran hBr
      have hVeq : (oldF d).V = (chain.G d).V := by rw [hact]; exact hHlsf.2.1.2.1
      change (oldF d).V.card ≤ Δi + 1
      rw [hVeq]; exact hOldGdN
    have hNewFdM : (next.lastLSFs next.lastBran).F.F.m ≤ Δi :=
      (Finset.card_le_card hLastNew).trans hNewGd_le_Δi
    have hNewFdN : (next.lastLSFs next.lastBran).F.F.n ≤ Δi + 1 := by
      have hBr := hmodNew.1.2.2.2.2.2.1
      have hHlsf := hmodNew.1.2.2.2.2.2.2.1 next.lastBran hBr
      have hVeq : (next.lastLSFs next.lastBran).F.F.V = (next.G d).V := hHlsf.2.1.2.1
      change (next.lastLSFs next.lastBran).F.F.V.card ≤ Δi + 1
      rw [hVeq]; exact hNewGdN
    have hDG1 : dgCopyRefillCost (chain.G d).n (chain.G d).m (next.G d).n (next.G d).m ≤
        780 * Δi + 530 := by unfold dgCopyRefillCost dgRefillFromListsCost; omega
    have hDG2 : dgCopyRefillCost (oldF d).n (oldF d).m
        (next.lastLSFs next.lastBran).F.F.n (next.lastLSFs next.lastBran).F.F.m ≤
        780 * Δi + 530 := by unfold dgCopyRefillCost dgRefillFromListsCost; omega
    have hCL : (next.G d).m * (selCoreLenEdgeCost L L + 40) ≤
        (selCoreLenEdgeCost L LwMax₀ + 40) * Δrt := by
      have hLw0 : L ≤ LwMax₀ := by unfold LwMax₀ ordLevelLwMax; omega
      calc (next.G d).m * (selCoreLenEdgeCost L L + 40)
          ≤ Δrt * (selCoreLenEdgeCost L LwMax₀ + 40) :=
            Nat.mul_le_mul (by omega) (Nat.add_le_add_right (selCoreLenEdgeCost_mono_sel hLw0) 40)
        _ = (selCoreLenEdgeCost L LwMax₀ + 40) * Δrt := Nat.mul_comm _ _
    have hEq : (1560 + (selCoreLenEdgeCost L LwMax₀ + 40)) * Δrt =
        1560 * Δrt + (selCoreLenEdgeCost L LwMax₀ + 40) * Δrt := by ring
    omega
  -- 3. Phi-loop cost
  have hPhiCost : selectPhiLoopCost next.toTreeChain i0 L ≤
      (d + 1) * (1800 * (d + 1) * (L + 1) + 40) + 20 + 1800 * (d + 1) * (L + 1) * Δrt := by
    unfold selectPhiLoopCost
    have hEach : ∀ j ∈ Finset.Icc i0 d,
        selectPhiFillCost j (next.toTreeChain.activeLSF j).F.F.n L + 40 ≤
        (1800 * (d + 1) * (L + 1) + 40) + 900 * (d + 1) * (L + 1) * (next.G j).m := by
      intro j hj
      have hjLe : j ≤ d := (Finset.mem_Icc.mp hj).2
      have hFnEq : (next.toTreeChain.activeLSF j).F.F.n = (next.G j).n := by
        have hVeq : (next.toTreeChain.activeLSF j).F.F.V = (next.G j).V := by
          by_cases hlt : j < d
          · have hBr := (hmodNew.1.2.2.2.2.1 j hlt).1
            have hHlsf := ((hmodNew.1.2.2.2.2.1 j hlt).2.1 (next.bran j) hBr).1
            simpa [TreeChain.activeLSF, ChainState.toTreeChain, d, hlt] using hHlsf.2.1.2.1
          · have hjd : j = d := by omega
            subst hjd
            have hBr := hmodNew.1.2.2.2.2.2.1
            have hHlsf := hmodNew.1.2.2.2.2.2.2.1 next.lastBran hBr
            simpa [TreeChain.activeLSF, ChainState.toTreeChain, d] using hHlsf.2.1.2.1
        unfold MGraph.n; rw [hVeq]
      rw [hFnEq]
      have hpf := selectPhiFillCost_paper_form j (next.G j).n L
      have hGn : (next.G j).n + 1 ≤ (next.G j).m + 2 := by
        have h1 : (next.G j).n ≤ (next.G j).m + 1 := hLvlN.1 j hjLe; omega
      have h1 : 900 * ((next.G j).n + 1) * (j + 1) * (L + 1) ≤
          900 * ((next.G j).m + 2) * (d + 1) * (L + 1) := by
        have h1a := Nat.mul_le_mul_left 900 hGn
        have h1b := Nat.mul_le_mul h1a (Nat.add_le_add_right hjLe 1)
        exact Nat.mul_le_mul_right (L + 1) h1b
      have hEq : 900 * ((next.G j).m + 2) * (d + 1) * (L + 1) =
          1800 * (d + 1) * (L + 1) + 900 * (d + 1) * (L + 1) * (next.G j).m := by ring
      omega
    have hSum := Finset.sum_le_sum hEach
    conv_rhs at hSum => rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum]
    simp only [Nat.card_Icc, smul_eq_mul] at hSum
    have h1 : (d + 1 - i0) * (1800 * (d + 1) * (L + 1) + 40) ≤
        (d + 1) * (1800 * (d + 1) * (L + 1) + 40) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have h2 : 900 * (d + 1) * (L + 1) * (Finset.Icc i0 d).sum (fun j => (next.G j).m) ≤
        1800 * (d + 1) * (L + 1) * Δrt := by
      calc 900 * (d + 1) * (L + 1) * (Finset.Icc i0 d).sum (fun j => (next.G j).m)
          ≤ 900 * (d + 1) * (L + 1) * (2 * Δrt) := Nat.mul_le_mul_left _ hSumIcc_le_2Δrt
        _ = 1800 * (d + 1) * (L + 1) * Δrt := by ring
    change (Finset.Icc i0 d).sum _ + 20 ≤ _
    omega
  -- 4. Rebuild-suffix cost + re-embedding potential
  have hCandSum : (Finset.Icc i0 d).sum (fun j => levelCandCount mem loc j) ≤ Δrt :=
    (selectHeapMatchesChain_levelCandCount_sum_le hmodOld.1 hMatchOld hOldSub).trans
      (by change (chain.G i0).m ≤ Δrt; omega)
  have hSufCost : selectRebuildSuffixCost mem loc next.toTreeChain i0 evalCost ≤
      240 * (d + 1) + 20 + 3 * K * Δrt := by
    unfold selectRebuildSuffixCost
    have hEach : ∀ j ∈ Finset.Icc i0 d,
        selectRebuildLevelCost (levelCandCount mem loc j) (next.toTreeChain.G j).E.card
          loc.cap loc.Lk evalCost + 40 ≤
        240 + (levelCandCount mem loc j + (next.G j).m) * K := by
      intro j _
      rw [hLocLk]
      have hlin := selectRebuildLevelCost_le_linear (levelCandCount mem loc j) (next.G j).m
        loc.cap L evalCost
      have hmul := Nat.mul_le_mul_left (levelCandCount mem loc j + (next.G j).m) hK
      change selectRebuildLevelCost (levelCandCount mem loc j) (next.G j).m loc.cap L evalCost + 40 ≤ _
      omega
    have hSum := Finset.sum_le_sum hEach
    conv_rhs at hSum => rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul, Finset.sum_add_distrib]
    simp only [Nat.card_Icc, smul_eq_mul] at hSum
    have h1 : (d + 1 - i0) * 240 ≤ 240 * (d + 1) := by
      have := Nat.mul_le_mul_right 240 (Nat.sub_le (d + 1) i0); linarith
    have h2 : ((Finset.Icc i0 d).sum (fun j => levelCandCount mem loc j) +
          (Finset.Icc i0 d).sum (fun j => (next.G j).m)) * K ≤ 3 * K * Δrt := by
      calc _ ≤ (Δrt + 2 * Δrt) * K := Nat.mul_le_mul_right K (Nat.add_le_add hCandSum hSumIcc_le_2Δrt)
        _ = 3 * K * Δrt := by ring
    change (Finset.Icc i0 d).sum _ + 20 ≤ _
    omega
  have hPotStep : K * chainReembPot pot next ≤ K * chainReembPot pot chain + K * Δrt := by
    have h1 := chainReembPot_shift_le hPot cfg.L cfg.P chain hiLt
      (hMono.2 (chain.scState i0) ((chain.bran i0 + 1) % cfg.P.k))
    have h2 := Nat.mul_le_mul_left K h1
    rw [Nat.mul_add] at h2
    exact h2
  -- Combine all pieces
  unfold selectRefreshFinalizeCost shiftDeepSelectFixedBound shiftDeepSelectToolMulBound
  dsimp only [LwMax₀] at hIntCost hLastCost ⊢
  have hMulSplit :
      (4 * K + (18 * slot + 80) + 1800 * (d + 1) * (L + 1) +
        2 * (selCoreLenEdgeCost L LwMax₀ + 40) + 70 * d + 2310) * Δrt =
      (70 * d + 750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) * Δrt +
      (1560 + (selCoreLenEdgeCost L LwMax₀ + 40)) * Δrt +
      1800 * (d + 1) * (L + 1) * Δrt + 3 * K * Δrt + K * Δrt := by ring
  have hFixSplit :
      (2 * d + 1) * readoutCost + (d + 1) * (1800 * (d + 1) * (L + 1) + 1700) + 2800 =
      2 * d * readoutCost + readoutCost +
      (d + 1) * (1800 * (d + 1) * (L + 1) + 40) + 1660 * (d + 1) + 2800 := by ring
  linarith

end MinCostFlow.MinRatio
