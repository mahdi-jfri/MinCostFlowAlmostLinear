module

public import MinCostFlow.MinRatio.SelectUpdatePostCoreAux
public import MinCostFlow.MinRatio.WireShiftDeepSelectCost
import Mathlib.Tactic

/-!
# Space and amortized cost bounds for post-core select update (`SelectUpdatePostCoreCost`)

Bounds the scratch space (`selectUpdatePostCoreRawSpace`) and amortized step cost
(`selectUpdatePostCoreRawCost + 40 * ∑_{j < lim} |reemb_j| + K * Δ chainReembPot`) of
`selectUpdatePostCoreBody` (`SelectUpdatePostCoreAux.lean`) by closed-form bounds:

* `selectUpdatePostCoreSpaceBound`: `PolyNat` scratch bound dominating Phases 2, 3a-1, 3a-2, 3b, 4
  for all `firstReb ≤ d + 1` (`selectUpdatePostCoreSpace_le_bound`).
* `selectUpdatePostCoreFixedBound`: `SubpolyNat` fixed-cost bound with zero factor of `m`.
* `selectUpdatePostCoreToolMulBound`: per-tool-runtime multiplier.
* `selectUpdatePostCoreTreeMulBound`: per-tree-update multiplier `K + 18 * slot + 650`.
* `selectUpdatePostCore_amortized_cost_le`: uniform amortized bound covering all four cases
  `firstReb = 0`, `0 < firstReb < d`, `firstReb = d`, and `firstReb = d + 1`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

/-- Closed-form scratch-space upper bound for `selectUpdatePostCoreBody`. -/
def selectUpdatePostCoreSpaceBound (d vCap eCap cap L capExp M₀ N₀ evalSpace coreSp : ℕ) : ℕ :=
  let LwMax₀ := ordLevelLwMax L capExp M₀ N₀
  coreSp +
    d * (coreSp + coreSp * selCoreLenEdgeSpace L LwMax₀) +
    d * (2 + 8 * coreSp) +
    shiftDeepSelectSpaceBound d vCap eCap cap L capExp M₀ N₀ evalSpace +
    d * (4 * coreSp * selectProcessEdgeSpace cap L evalSpace)

/-- Closed-form fixed-cost upper bound for `selectUpdatePostCoreBody` (zero linear `m` factor;
includes the subpolynomial terminal-level rebuild budget at `mD := levelM cfg.TP cfg.P d`). -/
def selectUpdatePostCoreFixedBound (readoutCost d L capExp M₀ N₀ slot K c uWordsFix mD : ℕ) : ℕ :=
  let LwMax₀ := ordLevelLwMax L capExp M₀ N₀
  shiftDeepSelectFixedBound readoutCost d L +
    80 +
    d * (readoutCost + K * c + 1600) +
    670 * uWordsFix + 700 +
    mD * (4 * K + (18 * slot + 80) + 1800 * (d + 1) * (L + 1) +
      2 * (selCoreLenEdgeCost L LwMax₀ + 40) + 140 * d + 2450)

/-- Per-tool-runtime multiplier for `selectUpdatePostCoreBody` (including the core's
`40 * ∑ |reemb|` charge and `K * (chainReembPot pot newCh - chainReembPot pot oldCh)`). -/
def selectUpdatePostCoreToolMulBound (d L capExp M₀ N₀ slot K c uWordsMul : ℕ) : ℕ :=
  let LwMax₀ := ordLevelLwMax L capExp M₀ N₀
  (9 + c) * K + 670 * uWordsMul + (90 * slot + 720) +
    1800 * (d + 1) * (L + 1) + 4 * (selCoreLenEdgeCost L LwMax₀ + 40) +
    140 * d + 126 * L + 3210

/-- Per-tree-update multiplier for `selectUpdatePostCoreBody` (paying `fDel` across Phases 3a-1,
3a-2, and 4a). -/
def selectUpdatePostCoreTreeMulBound (slot K : ℕ) : ℕ :=
  K + 18 * slot + 650

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.Chain.Ordered MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

private lemma ordLevelLwMax_mono_pc {L capExp M₁ M₂ N : ℕ} (h : M₁ ≤ M₂) :
    ordLevelLwMax L capExp M₁ N ≤ ordLevelLwMax L capExp M₂ N := by
  unfold ordLevelLwMax
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1)) _

private lemma selCoreLenEdgeSpace_mono_pc {L Lw₁ Lw₂ : ℕ} (h : Lw₁ ≤ Lw₂) :
    selCoreLenEdgeSpace L Lw₁ ≤ selCoreLenEdgeSpace L Lw₂ := by
  unfold selCoreLenEdgeSpace wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
  have hm := max_le_max_left L h
  have := Nat.mul_le_mul (show 5 * (2 * max L Lw₁) ≤ 5 * (2 * max L Lw₂) by omega)
    (show 2 * max L Lw₁ + 1 ≤ 2 * max L Lw₂ + 1 by omega)
  omega

private lemma selCoreLenEdgeCost_mono_pc {L Lw₁ Lw₂ : ℕ} (h : Lw₁ ≤ Lw₂) :
    selCoreLenEdgeCost L Lw₁ ≤ selCoreLenEdgeCost L Lw₂ := by
  unfold selCoreLenEdgeCost wireCoreLenEdgeCost
  have hm := max_le_max_left L h
  have := Nat.mul_le_mul hm hm
  nlinarith

private lemma selectPhiFillSpace_mono_pc {j₁ j₂ n₁ n₂ L : ℕ} (hj : j₁ ≤ j₂) (hn : n₁ ≤ n₂) :
    selectPhiFillSpace j₁ n₁ L ≤ selectPhiFillSpace j₂ n₂ L := by
  unfold selectPhiFillSpace phiFillEdgeStepSpace
  have hmul : n₁ * ((3 * j₁ + 3) * L) ≤ n₂ * ((3 * j₂ + 3) * L) :=
    Nat.mul_le_mul hn (Nat.mul_le_mul_right L (by omega))
  omega

private lemma chain_G_E_subset_pc {T : SparseCoreRestartTool} {P : ChainParams}
    {chain : ChainState T P} {first : ℕ}
    (hStep : ∀ j, first ≤ j → j < P.d → (chain.G (j + 1)).E ⊆ (chain.G j).E) :
    ∀ j, first ≤ j → j ≤ P.d → (chain.G j).E ⊆ (chain.G first).E := by
  intro j h1 h2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h1
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih => exact (hStep (first + k) (by omega) (by omega)).trans (ih (by omega) (by omega))

/-- The raw scratch space of `selectUpdatePostCoreBody` is bounded by the closed-form
`selectUpdatePostCoreSpaceBound` for all `firstReb ≤ cfg.P.d + 1`. -/
theorem selectUpdatePostCoreSpace_le_bound
    {cfg : Alg2Config} {G₀ G₀' : MGraph} {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {P vCap eCap L capExp evalSpace coreSp firstReb sizeOld : ℕ} {loc : SelectHeapLoc}
    {mem : ℕ → ℕ} {model modelPre : Alg2State cfg}
    {diffLists : ℕ → LevelDiffLists} {stLw : ℕ → ℕ}
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (hdPos : 0 < cfg.P.d) (hFR : firstReb ≤ cfg.P.d + 1)
    (hLvlN : ShiftLoopLevelFacts cfg modelPre.chain)
    (hSubOld : ∀ j < cfg.P.d, (model.chain.G (j + 1)).E ⊆ (model.chain.G j).E)
    (hmodOld : SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c)
    (hmodNew : SelectModelInv modelPre G₀' σ' σ'_mwu γ'_ℓ γ'_c)
    (hMatchOld : SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain model.chain.g
      model.chain.ℓ sizeOld)
    (hLocLk : loc.Lk = L)
    (hOldEcap : ∀ j ≤ cfg.P.d, (model.chain.G j).m ≤ eCap)
    (hNewVcap : ∀ j ≤ cfg.P.d, (modelPre.chain.G j).n ≤ vCap)
    (hNewEcap : ∀ j ≤ cfg.P.d, (modelPre.chain.G j).m ≤ eCap)
    (hDiffLe : ∀ j < min firstReb cfg.P.d,
      (diffLists j).uG.length ≤ coreSp ∧
      (diffLists j).fDel.length ≤ coreSp ∧
      (diffLists j).uS.length ≤ coreSp ∧
      (diffLists j).reemb.length ≤ coreSp)
    (hStLwLe : ∀ j < min firstReb cfg.P.d,
      stLw j ≤ ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀) :
    selectUpdatePostCoreRawSpace mem loc modelPre.chain diffLists stLw firstReb L capExp evalSpace ≤
      selectUpdatePostCoreSpaceBound cfg.P.d vCap eCap loc.cap L capExp
        (levelM cfg.TP cfg.P 0) cfg.N₀ evalSpace coreSp := by
  set d := cfg.P.d
  set lim := min firstReb d
  set M₀ := levelM cfg.TP cfg.P 0
  set LwMax₀ := ordLevelLwMax L capExp M₀ cfg.N₀
  have hLwLe : ∀ j < d,
      L + (capExp + sparseCoreReadout2LimbConst) *
        (Nat.log 2 (modelPre.chain.lvlM j + modelPre.chain.N₀ + 2) + 1) ≤ LwMax₀ := fun j _ => by
    change ordLevelLwMax L capExp (modelPre.chain.lvlM j) modelPre.chain.N₀ ≤
      ordLevelLwMax L capExp M₀ cfg.N₀
    rw [hLvlN.2.1, hLvlN.2.2.1]
    exact ordLevelLwMax_mono_pc (levelM_le_levelM_zero hTP hγk j)
  have hLimLe : lim ≤ d := Nat.min_le_right firstReb d
  have hSpG0 : selUpdateG0Space firstReb (diffLists 0).uG.length ≤ coreSp := by
    unfold selUpdateG0Space; split_ifs with h0
    · exact Nat.zero_le _
    · exact (hDiffLe 0 (by omega)).1
  have hSpFPL : selectUpdateFPhiLenLoopSpace diffLists stLw 0 lim L ≤
      d * (coreSp + coreSp * selCoreLenEdgeSpace L LwMax₀) := by
    unfold selectUpdateFPhiLenLoopSpace
    have hEach : ∀ j ∈ Finset.Ico 0 lim,
        selectUpdateFPhiLenSpace (diffLists j).uG.length L (stLw j) ≤
          coreSp + coreSp * selCoreLenEdgeSpace L LwMax₀ := fun j hj => by
      have hjLt : j < lim := (Finset.mem_Ico.mp hj).2
      have hLw : stLw j ≤ LwMax₀ :=
        (hStLwLe j hjLt).trans (ordLevelLwMax_mono_pc (levelM_le_levelM_zero hTP hγk j))
      unfold selectUpdateFPhiLenSpace
      exact Nat.add_le_add (hDiffLe j hjLt).1 (Nat.mul_le_mul (hDiffLe j hjLt).1 (selCoreLenEdgeSpace_mono_pc hLw))
    exact ((Finset.sum_le_sum hEach).trans (by simp [Finset.sum_const, smul_eq_mul])).trans
      (Nat.mul_le_mul_right _ hLimLe)
  have hSpEmb : selectUpdateEmbLoopSpace diffLists 0 lim ≤ d * (2 + 8 * coreSp) := by
    unfold selectUpdateEmbLoopSpace
    have hEach : ∀ j ∈ Finset.Ico 0 lim,
        selectUpdateEmbSpace (diffLists j).uG.length (diffLists j).fDel.length
          (diffLists j).uS.length (diffLists j).reemb.length ≤
          2 + 8 * coreSp := fun j hj => by
      have hD := hDiffLe j (Finset.mem_Ico.mp hj).2; unfold selectUpdateEmbSpace; omega
    exact ((Finset.sum_le_sum hEach).trans
      (by simp [Finset.sum_const, smul_eq_mul])).trans (Nat.mul_le_mul_right _ hLimLe)
  have hSpPrefHeap : selectUpdateHeapPrefixLoopSpace diffLists 0 lim loc.cap loc.Lk evalSpace ≤
      d * (4 * coreSp * selectProcessEdgeSpace loc.cap L evalSpace) := by
    unfold selectUpdateHeapPrefixLoopSpace; rw [hLocLk]
    have hEach : ∀ j ∈ Finset.Ico 0 lim,
        selectUpdateLevelSpace (diffLists j) loc.cap L evalSpace ≤
          4 * coreSp * selectProcessEdgeSpace loc.cap L evalSpace := fun j hj => by
      have hD := hDiffLe j (Finset.mem_Ico.mp hj).2
      unfold selectUpdateLevelSpace selectProcessListSpace LevelDiffLists.totalLen
      exact Nat.mul_le_mul_right _ (by omega)
    exact ((Finset.sum_le_sum hEach).trans
      (by simp [Finset.sum_const, smul_eq_mul])).trans (Nat.mul_le_mul_right _ hLimLe)
  have hSpSuf :
      selectUpdateSuffixBlocksSpace modelPre.chain firstReb L capExp +
        selectRebuildSuffixSpace mem loc modelPre.chain.toTreeChain firstReb evalSpace ≤
      shiftDeepSelectSpaceBound d vCap eCap loc.cap L capExp M₀ cfg.N₀ evalSpace := by
    unfold shiftDeepSelectSpaceBound selectUpdateSuffixBlocksSpace
    split_ifs with hReb
    · have hIntSp : selectInitInteriorLoopSpace modelPre.chain firstReb L capExp ≤
          d * (7 + eCap * (selCoreLenEdgeSpace L LwMax₀ + 4)) := by
        unfold selectInitInteriorLoopSpace
        have hEach : ∀ j ∈ Finset.Ico firstReb d,
            selectFillInteriorLevelSpace (modelPre.chain.G j).m (modelPre.chain.toTreeChain.activeLSF j).F.F.m L
              (L + (capExp + sparseCoreReadout2LimbConst) *
                (Nat.log 2 (modelPre.chain.lvlM j + modelPre.chain.N₀ + 2) + 1)) ≤
            7 + eCap * (selCoreLenEdgeSpace L LwMax₀ + 4) := fun j hj => by
          have hjLt : j < d := (Finset.mem_Ico.mp hj).2
          unfold selectFillInteriorLevelSpace
          have hm : (modelPre.chain.G j).m ≤ eCap := hNewEcap j (le_of_lt hjLt)
          have hmF : (modelPre.chain.toTreeChain.activeLSF j).F.F.m ≤ eCap := by
            have hSub := ((hmodNew.1.2.2.2.2.1 j hjLt).2.1 (modelPre.chain.bran j)
              (hmodNew.1.2.2.2.2.1 j hjLt).1).1.2.1.2.2.2.2.2.1
            have hAct : modelPre.chain.toTreeChain.activeLSF j =
                cfg.T.lsfs (modelPre.chain.scState j) (modelPre.chain.bran j) := by
              simp [TreeChain.activeLSF, ChainState.toTreeChain, show j < cfg.P.d from hjLt]
            rw [hAct]; exact (Finset.card_le_card hSub).trans hm
          have h1 := Nat.mul_le_mul hm (selCoreLenEdgeSpace_mono_pc (L := L) (hLwLe j hjLt))
          have hEq : eCap * (selCoreLenEdgeSpace L LwMax₀ + 4) =
              eCap * selCoreLenEdgeSpace L LwMax₀ + 4 * eCap := by ring
          omega
        exact ((Finset.sum_le_sum hEach).trans
          (by simp [Finset.sum_const, Nat.card_Ico, smul_eq_mul])).trans (Nat.mul_le_mul_right _ (Nat.sub_le d firstReb))
      have hLastSp : selectFillLastLevelSpace (modelPre.chain.G d).m
            (modelPre.chain.toTreeChain.activeLSF d).F.F.m L ≤ eCap * (6 + selCoreLenEdgeSpace L LwMax₀) := by
        unfold selectFillLastLevelSpace
        have hmG : (modelPre.chain.G d).m ≤ eCap := hNewEcap d le_rfl
        have hmF : (modelPre.chain.toTreeChain.activeLSF d).F.F.m ≤ eCap := by
          have hSub := (hmodNew.1.2.2.2.2.2.2.1 modelPre.chain.lastBran hmodNew.1.2.2.2.2.2.1).2.1.2.2.2.2.2.1
          have hAct : modelPre.chain.toTreeChain.activeLSF d = modelPre.chain.lastLSFs modelPre.chain.lastBran := by
            simp [TreeChain.activeLSF, ChainState.toTreeChain, d]
          rw [hAct]; exact (Finset.card_le_card hSub).trans hmG
        have hmul := Nat.mul_le_mul hmG (selCoreLenEdgeSpace_mono_pc (L := L) (show L ≤ LwMax₀ by unfold LwMax₀ ordLevelLwMax; omega))
        have hEq : eCap * (6 + selCoreLenEdgeSpace L LwMax₀) = 3 * eCap + 3 * eCap + eCap * selCoreLenEdgeSpace L LwMax₀ := by ring
        omega
      have hPhiSp : selectPhiLoopSpace modelPre.chain.toTreeChain firstReb L ≤ (d + 1) * selectPhiFillSpace d vCap L := by
        unfold selectPhiLoopSpace
        have hEach : ∀ j ∈ Finset.Icc firstReb d,
            selectPhiFillSpace j (modelPre.chain.toTreeChain.activeLSF j).F.F.n L ≤ selectPhiFillSpace d vCap L := fun j hj => by
          have hjLe : j ≤ cfg.P.d := (Finset.mem_Icc.mp hj).2
          have hVeq : (modelPre.chain.toTreeChain.activeLSF j).F.F.V = (modelPre.chain.G j).V := by
            by_cases hlt : j < cfg.P.d
            · simpa [TreeChain.activeLSF, ChainState.toTreeChain, hlt] using
                ((hmodNew.1.2.2.2.2.1 j hlt).2.1 (modelPre.chain.bran j) (hmodNew.1.2.2.2.2.1 j hlt).1).1.2.1.2.1
            · have hjd : j = cfg.P.d := by omega
              subst hjd
              simpa [TreeChain.activeLSF, ChainState.toTreeChain] using
                (hmodNew.1.2.2.2.2.2.2.1 modelPre.chain.lastBran hmodNew.1.2.2.2.2.2.1).2.1.2.1
          exact selectPhiFillSpace_mono_pc hjLe
            (by change (modelPre.chain.toTreeChain.activeLSF j).F.F.V.card ≤ vCap; rw [hVeq]; exact hNewVcap j hjLe)
        exact ((Finset.sum_le_sum hEach).trans
          (by simp [Finset.sum_const, Nat.card_Icc, smul_eq_mul])).trans (Nat.mul_le_mul_right _ (Nat.sub_le (d + 1) firstReb))
      have hRebSp : selectRebuildSuffixSpace mem loc modelPre.chain.toTreeChain firstReb evalSpace ≤
          eCap * heapRebalanceSpace loc.cap L + (d + 1) * eCap * selectProcessEdgeSpace loc.cap L evalSpace := by
        unfold selectRebuildSuffixSpace; rw [hLocLk]
        have hCandSum : (Finset.Icc firstReb d).sum (fun j => levelCandCount mem loc j) ≤ eCap :=
          (selectHeapMatchesChain_levelCandCount_sum_le hmodOld.1 hMatchOld
            (chain_G_E_subset_pc fun j _ hj => hSubOld j hj)).trans (hOldEcap firstReb hReb)
        have hSplit :
            (Finset.Icc firstReb d).sum (fun j =>
              selectRebuildLevelSpace (levelCandCount mem loc j) (modelPre.chain.toTreeChain.G j).E.card loc.cap L evalSpace) =
            (Finset.Icc firstReb d).sum (fun j => levelCandCount mem loc j) * heapRebalanceSpace loc.cap L +
            (Finset.Icc firstReb d).sum (fun j => (modelPre.chain.G j).m) * selectProcessEdgeSpace loc.cap L evalSpace := by
          simp only [selectRebuildLevelSpace, heapClearLevelSpace, selectProcessListSpace, Finset.sum_add_distrib, ← Finset.sum_mul]; rfl
        change (Finset.Icc firstReb d).sum _ ≤ _; rw [hSplit]
        have h1 := Nat.mul_le_mul_right (heapRebalanceSpace loc.cap L) hCandSum
        have h2 : (Finset.Icc firstReb d).sum (fun j => (modelPre.chain.G j).m) ≤ (d + 1) * eCap :=
          ((Finset.sum_le_sum fun j hj => hNewEcap j (Finset.mem_Icc.mp hj).2).trans
            (by simp [Finset.sum_const, Nat.card_Icc, smul_eq_mul])).trans (Nat.mul_le_mul_right _ (Nat.sub_le (d + 1) firstReb))
        have h3 := Nat.mul_le_mul_right (selectProcessEdgeSpace loc.cap L evalSpace) h2
        omega
      change selectInitInteriorLoopSpace modelPre.chain firstReb L capExp + 1 +
          selectFillLastLevelSpace (modelPre.chain.G d).m (modelPre.chain.toTreeChain.activeLSF d).F.F.m L +
          selectPhiLoopSpace modelPre.chain.toTreeChain firstReb L +
          selectRebuildSuffixSpace mem loc modelPre.chain.toTreeChain firstReb evalSpace ≤ _
      dsimp only [LwMax₀] at hIntSp hLastSp ⊢; omega
    · have hEmpty : Finset.Icc firstReb d = ∅ := Finset.Icc_eq_empty (by omega)
      unfold selectRebuildSuffixSpace; change 0 + (Finset.Icc firstReb d).sum _ ≤ _; rw [hEmpty]; simp
  unfold selectUpdatePostCoreRawSpace selectUpdatePostCoreSpaceBound selectUpdateHeapPhaseSpace
  change selUpdateG0Space firstReb (diffLists 0).uG.length +
      selectUpdateFPhiLenLoopSpace diffLists stLw 0 lim L + selectUpdateEmbLoopSpace diffLists 0 lim +
      selectUpdateSuffixBlocksSpace modelPre.chain firstReb L capExp +
      (selectUpdateHeapPrefixLoopSpace diffLists 0 lim loc.cap loc.Lk evalSpace +
        selectRebuildSuffixSpace mem loc modelPre.chain.toTreeChain firstReb evalSpace) ≤ _
  dsimp only [LwMax₀] at hSpFPL ⊢; omega

set_option maxHeartbeats 1000000 in
/-- Uniform amortized cost bound for `selectUpdatePostCoreBody`, including the core's
`40 * ∑_{j < lim} |reemb_j|` charge and the re-embedding potential change
`K * (chainReembPot pot modelPre.chain - chainReembPot pot model.chain)`.
Covers all four cases `firstReb = 0`, `0 < firstReb < d`, `firstReb = d`, and `firstReb = d + 1`. -/
theorem selectUpdatePostCore_amortized_cost_le
    {cfg : Alg2Config} {G₀ G₀' : MGraph} {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {pot : cfg.T.State → ℕ}
    {P readoutCost L capExp slot evalCost K c uWordsMul uWordsFix mD firstReb sizeOld : ℕ}
    {loc : SelectHeapLoc} {mem : ℕ → ℕ} {model modelPre : Alg2State cfg}
    {levelU : ℕ → List Update} {diffLists : ℕ → LevelDiffLists} {uWords stLw : ℕ → ℕ}
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (hPot : ToolReembPotFacts cfg.T pot)
    (hdPos : 0 < cfg.P.d) (hFR : firstReb ≤ cfg.P.d + 1)
    (hLvlOld : ShiftLoopLevelFacts cfg model.chain)
    (hLvlNew : ShiftLoopLevelFacts cfg modelPre.chain)
    (hSubOld : ∀ j < cfg.P.d,
      (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.V ⊆ (model.chain.G j).V ∧
      (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.E ⊆ (model.chain.G j).E ∧
      (model.chain.G (j + 1)).E ⊆ (model.chain.G j).E)
    (hSubNew : ∀ j < cfg.P.d,
      (cfg.T.lsfs (modelPre.chain.scState j) (modelPre.chain.bran j)).F.F.E ⊆ (modelPre.chain.G j).E ∧
      (modelPre.chain.G (j + 1)).E ⊆ (modelPre.chain.G j).E)
    (hLastOld : (model.chain.lastLSFs model.chain.lastBran).F.F.E ⊆ (model.chain.G cfg.P.d).E)
    (hLastNew : (modelPre.chain.lastLSFs modelPre.chain.lastBran).F.F.E ⊆ (modelPre.chain.G cfg.P.d).E)
    (hmodOld : SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c)
    (hmodNew : SelectModelInv modelPre G₀' σ' σ'_mwu γ'_ℓ γ'_c)
    (hMatchOld : SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain model.chain.g
      model.chain.ℓ sizeOld)
    (hLocLk : loc.Lk = L)
    (hK : selectProcessEdgeCost loc.cap L evalCost + (18 * slot + 160) + 80 ≤ K)
    -- Prefix per-level list, stretch-width, and re-embedding bounds
    (hStLwLe : ∀ j < min firstReb cfg.P.d,
      stLw j ≤ ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
    (hUGLe : ∀ j < min firstReb cfg.P.d, (diffLists j).uG.length ≤ (levelU j).length)
    (hReemb : ∀ j < min firstReb cfg.P.d,
      ReembCostBound (diffLists j).reemb
        (cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j)) c
        (pot (model.chain.scState j)) (pot (modelPre.chain.scState j)))
    -- Aggregate runtime & tree-update accounting across prefix and rebuilt suffix
    (hUWordsSum :
      (Finset.range (min firstReb cfg.P.d)).sum uWords ≤
        uWordsMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) + uWordsFix)
    (hULenSum :
      (Finset.range (min firstReb cfg.P.d)).sum (fun j => (levelU j).length) ≤
        2 * (modelPre.chain.totalRuntime - model.chain.totalRuntime))
    (hUSSum :
      (Finset.range (min firstReb cfg.P.d)).sum (fun j => (diffLists j).uS.length) ≤
        2 * (modelPre.chain.totalRuntime - model.chain.totalRuntime))
    (hFDelSum :
      (Finset.range (min firstReb cfg.P.d)).sum (fun j => (diffLists j).fDel.length) ≤
        modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates)
    (hCostSum :
      (Finset.range (min firstReb cfg.P.d)).sum
          (fun j => cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j)) +
        (Finset.Ico firstReb cfg.P.d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) ≤
        modelPre.chain.totalRuntime - model.chain.totalRuntime)
    (hSufNewM : firstReb < cfg.P.d →
      (Finset.Ico firstReb cfg.P.d).sum (fun j => (modelPre.chain.G j).m) ≤
        modelPre.chain.totalRuntime - model.chain.totalRuntime ∧
      (modelPre.chain.G cfg.P.d).m ≤ modelPre.chain.totalRuntime - model.chain.totalRuntime)
    (hSufOldM : firstReb < cfg.P.d →
      (model.chain.G firstReb).m ≤ 2 * (modelPre.chain.totalRuntime - model.chain.totalRuntime))
    (hLastM : (model.chain.G cfg.P.d).m ≤ mD ∧ (modelPre.chain.G cfg.P.d).m ≤ mD)
    (hBranchA0 : firstReb = 0 →
      (modelPre.chain.G 0).m ≤ modelPre.chain.totalRuntime - model.chain.totalRuntime) :
    let oldCh := model.chain
    let newCh := modelPre.chain
    let d := cfg.P.d
    let lim := min firstReb d
    let M₀ := levelM cfg.TP cfg.P 0
    selectUpdatePostCoreRawCost mem loc oldCh newCh levelU diffLists uWords stLw
        readoutCost firstReb L capExp slot evalCost +
      40 * (Finset.range lim).sum (fun j => (diffLists j).reemb.length) +
      K * chainReembPot pot newCh ≤
      selectUpdatePostCoreFixedBound readoutCost d L capExp M₀ cfg.N₀ slot K c uWordsFix mD +
        selectUpdatePostCoreToolMulBound d L capExp M₀ cfg.N₀ slot K c uWordsMul *
          (newCh.totalRuntime - oldCh.totalRuntime) +
        selectUpdatePostCoreTreeMulBound slot K *
          (newCh.totalTreeUpdates - oldCh.totalTreeUpdates) +
        K * chainReembPot pot oldCh := by
  intro oldCh newCh d lim M₀
  set Δrt := newCh.totalRuntime - oldCh.totalRuntime
  set Δtu := newCh.totalTreeUpdates - oldCh.totalTreeUpdates
  set LwMax₀ := ordLevelLwMax L capExp M₀ cfg.N₀
  have hLimLe : lim ≤ d := Nat.min_le_right _ _
  have hIcoEq : Finset.Ico 0 lim = Finset.range lim := by ext j; simp
  have hLwLe : ∀ j < d,
      L + (capExp + sparseCoreReadout2LimbConst) *
        (Nat.log 2 (newCh.lvlM j + newCh.N₀ + 2) + 1) ≤ LwMax₀ := fun j _ => by
    change ordLevelLwMax L capExp (newCh.lvlM j) newCh.N₀ ≤ ordLevelLwMax L capExp M₀ cfg.N₀
    rw [hLvlNew.2.1, hLvlNew.2.2.1]
    exact ordLevelLwMax_mono_pc (levelM_le_levelM_zero hTP hγk j)
  have hUGSum : (Finset.range lim).sum (fun j => (diffLists j).uG.length) ≤ 2 * Δrt :=
    (Finset.sum_le_sum fun j hj => hUGLe j (Finset.mem_range.mp hj)).trans hULenSum
  -- 1. Phase 2 (`selUpdateG0Cost`)
  have hCostG0 : selUpdateG0Cost firstReb (newCh.G 0).m (diffLists 0).uG.length L ≤
      80 + (90 * L + 420) * Δrt := by
    unfold selUpdateG0Cost
    split_ifs with h0
    · have h1 : (newCh.G 0).m * (45 * L + 160) ≤ Δrt * (45 * L + 160) :=
        Nat.mul_le_mul_right (45 * L + 160) (hBranchA0 h0)
      have h2 : Δrt * (45 * L + 160) ≤ (90 * L + 420) * Δrt := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_right Δrt (by omega)
      omega
    · have h0Lim : 0 ∈ Finset.range lim := Finset.mem_range.mpr (by omega)
      have huG0 : (diffLists 0).uG.length ≤ 2 * Δrt :=
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h0Lim).trans hUGSum
      have h1 : (diffLists 0).uG.length * (45 * L + 210) ≤ (2 * Δrt) * (45 * L + 210) :=
        Nat.mul_le_mul_right (45 * L + 210) huG0
      have h2 : (2 * Δrt) * (45 * L + 210) = (90 * L + 420) * Δrt := by ring
      omega
  -- 2. Phase 3a-1 (`selectUpdateFPhiLenLoopCost`)
  have hCostFPL : selectUpdateFPhiLenLoopCost levelU uWords diffLists stLw 0 lim L ≤
      (460 * d + 10 + 670 * uWordsFix) +
        (670 * uWordsMul + 2 * (18 * L + 130) + 2 * (selCoreLenEdgeCost L LwMax₀ + 80)) * Δrt +
        490 * Δtu := by
    unfold selectUpdateFPhiLenLoopCost
    rw [hIcoEq]
    have hEach : ∀ j ∈ Finset.range lim,
        selectUpdateFPhiLenCost (uWords j) (levelU j).length (diffLists j).uG.length
          (diffLists j).fDel.length L (stLw j) + 70 ≤
        460 + 670 * uWords j + (18 * L + 130) * (levelU j).length +
          (selCoreLenEdgeCost L LwMax₀ + 80) * (diffLists j).uG.length +
          490 * (diffLists j).fDel.length := by
      intro j hj
      have hjLt : j < lim := Finset.mem_range.mp hj
      have hLw : stLw j ≤ LwMax₀ :=
        (hStLwLe j hjLt).trans (ordLevelLwMax_mono_pc (levelM_le_levelM_zero hTP hγk j))
      have hCL := Nat.mul_le_mul_left (diffLists j).uG.length
        (Nat.add_le_add_right (selCoreLenEdgeCost_mono_pc (L := L) hLw) 40)
      unfold selectUpdateFPhiLenCost
      have hEq1 : (selCoreLenEdgeCost L LwMax₀ + 80) * (diffLists j).uG.length =
          40 * (diffLists j).uG.length + (diffLists j).uG.length * (selCoreLenEdgeCost L LwMax₀ + 40) := by ring
      have hEq2 : (18 * L + 130) * (levelU j).length = (levelU j).length * (18 * L + 130) := Nat.mul_comm _ _
      have hEq3 : 490 * (diffLists j).fDel.length = (diffLists j).fDel.length * 490 := Nat.mul_comm _ _
      omega
    have hSum := Finset.sum_le_sum hEach
    conv_rhs at hSum =>
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum]
    have h1 : lim * 460 ≤ 460 * d := by nlinarith
    have h2 : 670 * (Finset.range lim).sum uWords ≤ 670 * uWordsMul * Δrt + 670 * uWordsFix := by
      have hUW : (Finset.range lim).sum uWords ≤ uWordsMul * Δrt + uWordsFix := hUWordsSum
      have := Nat.mul_le_mul_left 670 hUW; rw [Nat.mul_add, ← Nat.mul_assoc] at this; exact this
    have h3 : (18 * L + 130) * (Finset.range lim).sum (fun j => (levelU j).length) ≤
        2 * (18 * L + 130) * Δrt := by
      calc _ ≤ (18 * L + 130) * (2 * Δrt) := Nat.mul_le_mul_left _ hULenSum
        _ = 2 * (18 * L + 130) * Δrt := by ring
    have h4 : (selCoreLenEdgeCost L LwMax₀ + 80) * (Finset.range lim).sum (fun j => (diffLists j).uG.length) ≤
        2 * (selCoreLenEdgeCost L LwMax₀ + 80) * Δrt := by
      calc _ ≤ (selCoreLenEdgeCost L LwMax₀ + 80) * (2 * Δrt) := Nat.mul_le_mul_left _ hUGSum
        _ = 2 * (selCoreLenEdgeCost L LwMax₀ + 80) * Δrt := by ring
    have h5 : 490 * (Finset.range lim).sum (fun j => (diffLists j).fDel.length) ≤ 490 * Δtu :=
      Nat.mul_le_mul_left _ hFDelSum
    have hMul : (670 * uWordsMul + 2 * (18 * L + 130) + 2 * (selCoreLenEdgeCost L LwMax₀ + 80)) * Δrt =
        670 * uWordsMul * Δrt + 2 * (18 * L + 130) * Δrt + 2 * (selCoreLenEdgeCost L LwMax₀ + 80) * Δrt := by ring
    change (Finset.range lim).sum _ + 10 ≤ _; linarith
  have hCostEmbHeapPot :
      selectUpdateEmbLoopCost readoutCost diffLists 0 lim slot +
        selectUpdateHeapPrefixLoopCost diffLists 0 lim loc.cap loc.Lk evalCost +
        40 * (Finset.range lim).sum (fun j => (diffLists j).reemb.length) + K * chainReembPot pot newCh ≤
      (d * (readoutCost + K * c + 1070) + 20) + ((5 + c) * K + 4 * (18 * slot + 160)) * Δrt +
        (K + 18 * slot + 160) * Δtu + K * chainReembPot pot oldCh := by
    have hPotSplit : ∀ ch : ChainState cfg.T cfg.P,
        chainReembPot pot ch = (Finset.range lim).sum (fun j => pot (ch.scState j)) +
          (Finset.Ico lim d).sum (fun j => pot (ch.scState j)) := fun ch => by
      unfold chainReembPot; exact (Finset.sum_range_add_sum_Ico _ hLimLe).symm
    have hReembPotPref :
        (Finset.range lim).sum (fun j => (diffLists j).reemb.length) +
          (Finset.range lim).sum (fun j => pot (newCh.scState j)) ≤
        c * (Finset.range lim).sum (fun j => cfg.T.cost (newCh.scState j) - cfg.T.cost (oldCh.scState j)) +
          c * d + (Finset.range lim).sum (fun j => pot (oldCh.scState j)) := by
      rw [← Finset.sum_add_distrib]
      have hEach : ∀ j ∈ Finset.range lim,
          (diffLists j).reemb.length + pot (newCh.scState j) ≤
          c * (cfg.T.cost (newCh.scState j) - cfg.T.cost (oldCh.scState j)) + c + pot (oldCh.scState j) := fun j hj => by
        have hR := hReemb j (Finset.mem_range.mp hj); unfold ReembCostBound at hR; rw [Nat.mul_add, Nat.mul_one] at hR; exact hR
      have hSum := Finset.sum_le_sum hEach
      conv_rhs at hSum =>
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum]
      have : lim * c ≤ c * d := by nlinarith
      omega
    have hPotSuf : (Finset.Ico lim d).sum (fun j => pot (newCh.scState j)) ≤
        (Finset.Ico firstReb d).sum (fun j => cfg.T.cost (newCh.scState j)) := by
      have hIcoSub : Finset.Ico lim d = Finset.Ico firstReb d := by ext j; simp only [Finset.mem_Ico]; omega
      rw [hIcoSub]; exact Finset.sum_le_sum fun j _ => hPot.le_cost _
    have hAllReembPot :
        K * (Finset.range lim).sum (fun j => (diffLists j).reemb.length) + K * chainReembPot pot newCh ≤
        d * (K * c) + K * (c + 1) * Δrt + K * chainReembPot pot oldCh := by
      rw [hPotSplit newCh, hPotSplit oldCh]
      have h1 : (Finset.range lim).sum (fun j => (diffLists j).reemb.length) +
            (Finset.range lim).sum (fun j => pot (newCh.scState j)) +
            (Finset.Ico lim d).sum (fun j => pot (newCh.scState j)) ≤
          c * d + (c + 1) * Δrt + (Finset.range lim).sum (fun j => pot (oldCh.scState j)) := by
        have hcs : (Finset.range lim).sum (fun j => cfg.T.cost (newCh.scState j) - cfg.T.cost (oldCh.scState j)) +
            (Finset.Ico firstReb d).sum (fun j => cfg.T.cost (newCh.scState j)) ≤ Δrt := hCostSum
        have hmul : c * (Finset.range lim).sum (fun j => cfg.T.cost (newCh.scState j) - cfg.T.cost (oldCh.scState j)) +
            (Finset.Ico firstReb d).sum (fun j => cfg.T.cost (newCh.scState j)) ≤ (c + 1) * Δrt := by
          have : (c + 1) * Δrt = c * Δrt + Δrt := by ring
          have hc1 := Nat.mul_le_mul_left c (show (Finset.range lim).sum
            (fun j => cfg.T.cost (newCh.scState j) - cfg.T.cost (oldCh.scState j)) ≤ Δrt by omega)
          omega
        omega
      have h2 := Nat.mul_le_mul_left K h1
      have hEq1 : K * (c * d + (c + 1) * Δrt + (Finset.range lim).sum (fun j => pot (oldCh.scState j))) =
          d * (K * c) + K * (c + 1) * Δrt + K * (Finset.range lim).sum (fun j => pot (oldCh.scState j)) := by ring
      have hEq2 : K * ((Finset.range lim).sum (fun j => (diffLists j).reemb.length) +
            (Finset.range lim).sum (fun j => pot (newCh.scState j)) +
            (Finset.Ico lim d).sum (fun j => pot (newCh.scState j))) =
          K * (Finset.range lim).sum (fun j => (diffLists j).reemb.length) +
            K * ((Finset.range lim).sum (fun j => pot (newCh.scState j)) + (Finset.Ico lim d).sum (fun j => pot (newCh.scState j))) := by ring
      have hEq3 : K * ((Finset.range lim).sum (fun j => pot (oldCh.scState j)) +
            (Finset.Ico lim d).sum (fun j => pot (oldCh.scState j))) =
          K * (Finset.range lim).sum (fun j => pot (oldCh.scState j)) +
            K * (Finset.Ico lim d).sum (fun j => pot (oldCh.scState j)) := by ring
      omega
    unfold selectUpdateEmbLoopCost selectUpdateHeapPrefixLoopCost; rw [hIcoEq, hLocLk]
    have hEmbSum :
        (Finset.range lim).sum (fun j =>
          selectUpdateEmbCost readoutCost (diffLists j).uG.length (diffLists j).fDel.length
            (diffLists j).uS.length (diffLists j).reemb.length slot + 70) ≤
        lim * (readoutCost + 870) +
          (18 * slot + 160) * (Finset.range lim).sum (fun j => (diffLists j).uG.length) +
          (18 * slot + 160) * (Finset.range lim).sum (fun j => (diffLists j).fDel.length) +
          (18 * slot + 160) * (Finset.range lim).sum (fun j => (diffLists j).uS.length) +
          (18 * slot + 160) * (Finset.range lim).sum (fun j => (diffLists j).reemb.length) := by
      have hEach : ∀ j ∈ Finset.range lim,
          selectUpdateEmbCost readoutCost (diffLists j).uG.length (diffLists j).fDel.length
            (diffLists j).uS.length (diffLists j).reemb.length slot + 70 ≤
          (readoutCost + 870) + (18 * slot + 160) * (diffLists j).uG.length +
            (18 * slot + 160) * (diffLists j).fDel.length +
            (18 * slot + 160) * (diffLists j).uS.length +
            (18 * slot + 160) * (diffLists j).reemb.length := fun j _ => by
        unfold selectUpdateEmbCost selEmbUpdateFromListCost
        have := Nat.mul_comm (diffLists j).uG.length (18 * slot + 160)
        have := Nat.mul_comm (diffLists j).fDel.length (18 * slot + 160)
        have := Nat.mul_comm (diffLists j).uS.length (18 * slot + 160)
        have := Nat.mul_comm (diffLists j).reemb.length (18 * slot + 160); omega
      have hSum := Finset.sum_le_sum hEach
      conv_rhs at hSum =>
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum]
      rw [Nat.mul_add]; exact hSum
    have hHeapSum :
        (Finset.range lim).sum (fun j => selectUpdateLevelCost (diffLists j) loc.cap L evalCost + 60) ≤
        lim * 200 + K * (Finset.range lim).sum (fun j => (diffLists j).uG.length) +
          K * (Finset.range lim).sum (fun j => (diffLists j).fDel.length) +
          K * (Finset.range lim).sum (fun j => (diffLists j).uS.length) +
          (selectProcessEdgeCost loc.cap L evalCost + 40) * (Finset.range lim).sum (fun j => (diffLists j).reemb.length) := by
      have hEach : ∀ j ∈ Finset.range lim,
          selectUpdateLevelCost (diffLists j) loc.cap L evalCost + 60 ≤
          200 + K * (diffLists j).uG.length + K * (diffLists j).fDel.length + K * (diffLists j).uS.length +
            (selectProcessEdgeCost loc.cap L evalCost + 40) * (diffLists j).reemb.length := fun j _ => by
        unfold selectUpdateLevelCost selectProcessListCost LevelDiffLists.totalLen
        have hK1 : selectProcessEdgeCost loc.cap L evalCost + 40 ≤ K := by omega
        have h1 := Nat.mul_le_mul_left (diffLists j).uG.length hK1
        have h2 := Nat.mul_le_mul_left (diffLists j).fDel.length hK1
        have h3 := Nat.mul_le_mul_left (diffLists j).uS.length hK1
        have hEq : ((diffLists j).uG.length + (diffLists j).fDel.length + (diffLists j).uS.length +
              (diffLists j).reemb.length) * (selectProcessEdgeCost loc.cap L evalCost + 40) =
            (diffLists j).uG.length * (selectProcessEdgeCost loc.cap L evalCost + 40) +
            (diffLists j).fDel.length * (selectProcessEdgeCost loc.cap L evalCost + 40) +
            (diffLists j).uS.length * (selectProcessEdgeCost loc.cap L evalCost + 40) +
            (selectProcessEdgeCost loc.cap L evalCost + 40) * (diffLists j).reemb.length := by ring
        have := Nat.mul_comm (diffLists j).uG.length K
        have := Nat.mul_comm (diffLists j).fDel.length K
        have := Nat.mul_comm (diffLists j).uS.length K; omega
      have hSum := Finset.sum_le_sum hEach
      conv_rhs at hSum =>
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum]
      exact hSum
    have hReembCoeff :
        ((18 * slot + 160) + (selectProcessEdgeCost loc.cap L evalCost + 40) + 40) *
          (Finset.range lim).sum (fun j => (diffLists j).reemb.length) ≤
        K * (Finset.range lim).sum (fun j => (diffLists j).reemb.length) := Nat.mul_le_mul_right _ (by omega)
    have hReembSplit :
        ((18 * slot + 160) + (selectProcessEdgeCost loc.cap L evalCost + 40) + 40) *
          (Finset.range lim).sum (fun j => (diffLists j).reemb.length) =
        (18 * slot + 160) * (Finset.range lim).sum (fun j => (diffLists j).reemb.length) +
        (selectProcessEdgeCost loc.cap L evalCost + 40) * (Finset.range lim).sum (fun j => (diffLists j).reemb.length) +
        40 * (Finset.range lim).sum (fun j => (diffLists j).reemb.length) := by ring
    have hLimC : lim * (readoutCost + 870) + lim * 200 ≤ d * (readoutCost + 1070) := by nlinarith
    have hUG1 := Nat.mul_le_mul_left (18 * slot + 160) hUGSum
    have hUG2 := Nat.mul_le_mul_left K hUGSum
    have hUS1 : (18 * slot + 160) * (Finset.range lim).sum (fun j => (diffLists j).uS.length) ≤
        (18 * slot + 160) * (2 * Δrt) := Nat.mul_le_mul_left (18 * slot + 160) hUSSum
    have hUS2 : K * (Finset.range lim).sum (fun j => (diffLists j).uS.length) ≤ K * (2 * Δrt) := Nat.mul_le_mul_left K hUSSum
    have hFD1 : (18 * slot + 160) * (Finset.range lim).sum (fun j => (diffLists j).fDel.length) ≤ (18 * slot + 160) * Δtu :=
      Nat.mul_le_mul_left (18 * slot + 160) hFDelSum
    have hFD2 : K * (Finset.range lim).sum (fun j => (diffLists j).fDel.length) ≤ K * Δtu := Nat.mul_le_mul_left K hFDelSum
    have hEqR : ((5 + c) * K + 4 * (18 * slot + 160)) * Δrt =
        K * (c + 1) * Δrt + K * (2 * Δrt) + K * (2 * Δrt) + (18 * slot + 160) * (2 * Δrt) + (18 * slot + 160) * (2 * Δrt) := by ring
    have hEqT : (K + 18 * slot + 160) * Δtu = K * Δtu + (18 * slot + 160) * Δtu := by ring
    have hEqD : d * (readoutCost + K * c + 1070) = d * (readoutCost + 1070) + d * (K * c) := by ring
    linarith
  set Csuf := 4 * K + (18 * slot + 80) + 1800 * (d + 1) * (L + 1) +
    2 * (selCoreLenEdgeCost L LwMax₀ + 40) + 140 * d + 2450
  have hCostSuf :
      (240 * d + 840) +
        selectUpdateSuffixBlocksCost (fun j => (oldCh.toTreeChain.activeLSF j).F.F) (oldCh.G d)
          newCh readoutCost firstReb L capExp slot +
        selectRebuildSuffixCost mem loc newCh.toTreeChain firstReb evalCost ≤
      shiftDeepSelectFixedBound readoutCost d L + mD * Csuf + Csuf * Δrt := by
    unfold selectUpdateSuffixBlocksCost
    split_ifs with hReb
    · set X := if firstReb < d then Δrt else mD
      have hXLe : Csuf * X ≤ mD * Csuf + Csuf * Δrt := by
        dsimp only [X]; split_ifs
        · exact Nat.le_add_left _ _
        · rw [Nat.mul_comm Csuf mD]; exact Nat.le_add_right _ _
      have hSumIco' : (Finset.Ico firstReb d).sum (fun j => (newCh.G j).m) ≤ X := by
        dsimp only [X]; split_ifs with hlt
        · exact (hSufNewM hlt).1
        · have heq : firstReb = d := by omega
          subst heq; simp
      have hNewGd' : (newCh.G d).m ≤ X := by
        dsimp only [X]; split_ifs with hlt
        · exact (hSufNewM hlt).2
        · exact hLastM.2
      have hOldFirst : (oldCh.G firstReb).m ≤ 2 * X := by
        dsimp only [X]; split_ifs with hlt
        · exact hSufOldM hlt
        · have heq : firstReb = d := by omega
          rw [heq]; have h1 : (oldCh.G d).m ≤ mD := hLastM.1; omega
      have hOldSub : ∀ j, firstReb ≤ j → j ≤ d → (oldCh.G j).E ⊆ (oldCh.G firstReb).E :=
        chain_G_E_subset_pc fun j _ hj => (hSubOld j hj).2.2
      have hSumIcc : (Finset.Icc firstReb d).sum (fun j => (newCh.G j).m) ≤ 2 * X := by
        have hsp : Finset.Icc firstReb d = insert d (Finset.Ico firstReb d) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
        rw [hsp, Finset.sum_insert (by simp)]; omega
      have hIntCost : selectRefreshInteriorLoopCost (fun j => (oldCh.toTreeChain.activeLSF j).F.F)
            newCh readoutCost firstReb L capExp slot ≤
          2 * d * readoutCost + 1110 * d + 10 +
            (140 * d + 750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) * X := by
        unfold selectRefreshInteriorLoopCost
        have hEach : ∀ j ∈ Finset.Ico firstReb d,
            selectFillInteriorLevelCost readoutCost (oldCh.toTreeChain.activeLSF j).F.F.n
              (oldCh.toTreeChain.activeLSF j).F.F.m (newCh.toTreeChain.activeLSF j).F.F.n
              (newCh.toTreeChain.activeLSF j).F.F.m (newCh.G j).m L
              (L + (capExp + sparseCoreReadout2LimbConst) *
                (Nat.log 2 (newCh.lvlM j + newCh.N₀ + 2) + 1)) slot + 60 ≤
            (2 * readoutCost + 1110) + 140 * X +
              (750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) * (newCh.G j).m := fun j hj => by
          obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
          unfold selectFillInteriorLevelCost
          have hactOld : (oldCh.toTreeChain.activeLSF j).F.F = (cfg.T.lsfs (oldCh.scState j) (oldCh.bran j)).F.F := by
            simp [TreeChain.activeLSF, ChainState.toTreeChain, show j < cfg.P.d from hj2]
          have hactNew : (newCh.toTreeChain.activeLSF j).F.F = (cfg.T.lsfs (newCh.scState j) (newCh.bran j)).F.F := by
            simp [TreeChain.activeLSF, ChainState.toTreeChain, show j < cfg.P.d from hj2]
          have holdM : (oldCh.toTreeChain.activeLSF j).F.F.m ≤ 2 * X := by
            rw [hactOld]; exact (Finset.card_le_card ((hSubOld j hj2).2.1.trans (hOldSub j hj1 (le_of_lt hj2)))).trans hOldFirst
          have holdN : (oldCh.toTreeChain.activeLSF j).F.F.n ≤ 2 * X + 1 := by
            have hGm : (oldCh.G j).m ≤ 2 * X := (Finset.card_le_card (hOldSub j hj1 (le_of_lt hj2))).trans hOldFirst
            rw [hactOld]; exact (Finset.card_le_card (hSubOld j hj2).1).trans ((hLvlOld.1 j (le_of_lt hj2)).trans (Nat.add_le_add_right hGm 1))
          have hnewM : (newCh.toTreeChain.activeLSF j).F.F.m ≤ (newCh.G j).m := by
            rw [hactNew]; exact Finset.card_le_card (hSubNew j hj2).1
          have hnewN : (newCh.toTreeChain.activeLSF j).F.F.n ≤ (newCh.G j).m + 1 := by
            have hV : (cfg.T.lsfs (newCh.scState j) (newCh.bran j)).F.F.V = (newCh.G j).V := by
              simpa [ChainState.toTreeChain, show j < cfg.P.d from hj2] using
                ((hmodNew.1.2.2.2.2.1 j hj2).2.1 (newCh.bran j) (hmodNew.1.2.2.2.2.1 j hj2).1).1.2.1.2.1
            have hVn : (newCh.toTreeChain.activeLSF j).F.F.n = (newCh.G j).n := by unfold MGraph.n; rw [hactNew, hV]
            rw [hVn]; exact hLvlNew.1 j (le_of_lt hj2)
          have hDG : dgCopyRefillCost (oldCh.toTreeChain.activeLSF j).F.F.n (oldCh.toTreeChain.activeLSF j).F.F.m
              (newCh.toTreeChain.activeLSF j).F.F.n (newCh.toTreeChain.activeLSF j).F.F.m ≤
              140 * X + 710 * (newCh.G j).m + 530 := by unfold dgCopyRefillCost dgRefillFromListsCost; omega
          have hCL := Nat.mul_le_mul_left (newCh.G j).m (Nat.add_le_add_right (selCoreLenEdgeCost_mono_pc (L := L) (hLwLe j hj2)) 40)
          have hEq : (750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) * (newCh.G j).m =
              710 * (newCh.G j).m + 40 * (newCh.G j).m + (newCh.G j).m * (selCoreLenEdgeCost L LwMax₀ + 40) +
                (newCh.G j).m * (18 * slot + 80) := by ring
          omega
        have hSum := Finset.sum_le_sum hEach
        conv_rhs at hSum => rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, ← Finset.mul_sum]
        simp only [Nat.card_Ico, smul_eq_mul] at hSum
        have h1 : (d - firstReb) * (2 * readoutCost + 1110) ≤ 2 * d * readoutCost + 1110 * d := by
          have := Nat.mul_le_mul_right (2 * readoutCost + 1110) (Nat.sub_le d firstReb); nlinarith
        have h2 : (d - firstReb) * (140 * X) ≤ 140 * d * X := by
          calc (d - firstReb) * (140 * X) ≤ d * (140 * X) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
            _ = 140 * d * X := by ring
        have h3 := Nat.mul_le_mul_left (750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) hSumIco'
        have hEq : (140 * d + 750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) * X =
            140 * d * X + (750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) * X := by ring
        linarith
      have hLastCost :
          selectFillLastLevelCost (oldCh.G d).n (oldCh.G d).m (oldCh.toTreeChain.activeLSF d).F.F.n
            (oldCh.toTreeChain.activeLSF d).F.F.m (newCh.G d).n (newCh.G d).m
            (newCh.toTreeChain.activeLSF d).F.F.n (newCh.toTreeChain.activeLSF d).F.F.m L ≤
          1380 + (1700 + (selCoreLenEdgeCost L LwMax₀ + 40)) * X := by
        unfold selectFillLastLevelCost
        have hOldGdM : (oldCh.G d).m ≤ 2 * X := (Finset.card_le_card (hOldSub d hReb le_rfl)).trans hOldFirst
        have hOldGdN : (oldCh.G d).n ≤ 2 * X + 1 := (hLvlOld.1 d le_rfl).trans (by change (oldCh.G d).m + 1 ≤ 2 * X + 1; omega)
        have hNewGdN : (newCh.G d).n ≤ X + 1 := (hLvlNew.1 d le_rfl).trans (by change (newCh.G d).m + 1 ≤ X + 1; omega)
        have hActO : (oldCh.toTreeChain.activeLSF d).F.F = (oldCh.lastLSFs oldCh.lastBran).F.F := by simp [TreeChain.activeLSF, ChainState.toTreeChain, d]
        have hActN : (newCh.toTreeChain.activeLSF d).F.F = (newCh.lastLSFs newCh.lastBran).F.F := by simp [TreeChain.activeLSF, ChainState.toTreeChain, d]
        have hOldFdM : (oldCh.toTreeChain.activeLSF d).F.F.m ≤ 2 * X := by rw [hActO]; exact (Finset.card_le_card hLastOld).trans hOldGdM
        have hOldFdN : (oldCh.toTreeChain.activeLSF d).F.F.n ≤ 2 * X + 1 := by
          have hV : (oldCh.lastLSFs oldCh.lastBran).F.F.V = (oldCh.G d).V := by
            simpa [ChainState.toTreeChain, d] using (hmodOld.1.2.2.2.2.2.2.1 oldCh.lastBran hmodOld.1.2.2.2.2.2.1).2.1.2.1
          have hVn : (oldCh.toTreeChain.activeLSF d).F.F.n = (oldCh.G d).n := by unfold MGraph.n; rw [hActO, hV]
          rw [hVn]; exact hOldGdN
        have hNewFdM : (newCh.toTreeChain.activeLSF d).F.F.m ≤ X := by rw [hActN]; exact (Finset.card_le_card hLastNew).trans hNewGd'
        have hNewFdN : (newCh.toTreeChain.activeLSF d).F.F.n ≤ X + 1 := by
          have hV : (newCh.lastLSFs newCh.lastBran).F.F.V = (newCh.G d).V := by
            simpa [ChainState.toTreeChain, d] using (hmodNew.1.2.2.2.2.2.2.1 newCh.lastBran hmodNew.1.2.2.2.2.2.1).2.1.2.1
          have hVn : (newCh.toTreeChain.activeLSF d).F.F.n = (newCh.G d).n := by unfold MGraph.n; rw [hActN, hV]
          rw [hVn]; exact hNewGdN
        have hDG1 : dgCopyRefillCost (oldCh.G d).n (oldCh.G d).m (newCh.G d).n (newCh.G d).m ≤ 850 * X + 530 := by
          unfold dgCopyRefillCost dgRefillFromListsCost; omega
        have hDG2 : dgCopyRefillCost (oldCh.toTreeChain.activeLSF d).F.F.n (oldCh.toTreeChain.activeLSF d).F.F.m
            (newCh.toTreeChain.activeLSF d).F.F.n (newCh.toTreeChain.activeLSF d).F.F.m ≤ 850 * X + 530 := by
          unfold dgCopyRefillCost dgRefillFromListsCost; omega
        have hCL : (newCh.G d).m * (selCoreLenEdgeCost L L + 40) ≤ (selCoreLenEdgeCost L LwMax₀ + 40) * X := by
          calc _ ≤ X * (selCoreLenEdgeCost L LwMax₀ + 40) :=
                Nat.mul_le_mul hNewGd' (Nat.add_le_add_right (selCoreLenEdgeCost_mono_pc (show L ≤ LwMax₀ by unfold LwMax₀ ordLevelLwMax; omega)) 40)
            _ = (selCoreLenEdgeCost L LwMax₀ + 40) * X := Nat.mul_comm _ _
        have hEq : (1700 + (selCoreLenEdgeCost L LwMax₀ + 40)) * X = 1700 * X + (selCoreLenEdgeCost L LwMax₀ + 40) * X := by ring
        omega
      have hPhiCost : selectPhiLoopCost newCh.toTreeChain firstReb L ≤
          (d + 1) * (1800 * (d + 1) * (L + 1) + 40) + 20 + 1800 * (d + 1) * (L + 1) * X := by
        unfold selectPhiLoopCost
        have hEach : ∀ j ∈ Finset.Icc firstReb d,
            selectPhiFillCost j (newCh.toTreeChain.activeLSF j).F.F.n L + 40 ≤
            (1800 * (d + 1) * (L + 1) + 40) + 900 * (d + 1) * (L + 1) * (newCh.G j).m := fun j hj => by
          have hjLe : j ≤ cfg.P.d := (Finset.mem_Icc.mp hj).2
          have hFnEq : (newCh.toTreeChain.activeLSF j).F.F.n = (newCh.G j).n := by
            have hV : (newCh.toTreeChain.activeLSF j).F.F.V = (newCh.G j).V := by
              by_cases hlt : j < cfg.P.d
              · simpa [TreeChain.activeLSF, ChainState.toTreeChain, hlt] using
                  ((hmodNew.1.2.2.2.2.1 j hlt).2.1 (newCh.bran j) (hmodNew.1.2.2.2.2.1 j hlt).1).1.2.1.2.1
              · have hjd : j = cfg.P.d := by omega
                subst hjd
                simpa [TreeChain.activeLSF, ChainState.toTreeChain] using
                  (hmodNew.1.2.2.2.2.2.2.1 newCh.lastBran hmodNew.1.2.2.2.2.2.1).2.1.2.1
            unfold MGraph.n; rw [hV]
          rw [hFnEq]
          have hpf := selectPhiFillCost_paper_form j (newCh.G j).n L
          have hGn : (newCh.G j).n + 1 ≤ (newCh.G j).m + 2 := by
            have := hLvlNew.1 j hjLe; change (newCh.G j).n ≤ (newCh.G j).m + 1 at this; omega
          have h1 : 900 * ((newCh.G j).n + 1) * (j + 1) * (L + 1) ≤ 900 * ((newCh.G j).m + 2) * (d + 1) * (L + 1) :=
            Nat.mul_le_mul_right (L + 1) (Nat.mul_le_mul (Nat.mul_le_mul_left 900 hGn) (Nat.add_le_add_right hjLe 1))
          have hEq : 900 * ((newCh.G j).m + 2) * (d + 1) * (L + 1) =
              1800 * (d + 1) * (L + 1) + 900 * (d + 1) * (L + 1) * (newCh.G j).m := by ring
          omega
        have hSum := Finset.sum_le_sum hEach
        conv_rhs at hSum => rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum]
        simp only [Nat.card_Icc, smul_eq_mul] at hSum
        have h1 : (d + 1 - firstReb) * (1800 * (d + 1) * (L + 1) + 40) ≤ (d + 1) * (1800 * (d + 1) * (L + 1) + 40) :=
          Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        have h2 : 900 * (d + 1) * (L + 1) * (Finset.Icc firstReb d).sum (fun j => (newCh.G j).m) ≤
            1800 * (d + 1) * (L + 1) * X := by
          calc _ ≤ 900 * (d + 1) * (L + 1) * (2 * X) := Nat.mul_le_mul_left _ hSumIcc
            _ = 1800 * (d + 1) * (L + 1) * X := by ring
        change (Finset.Icc firstReb d).sum _ + 20 ≤ _; omega
      have hCandSum : (Finset.Icc firstReb d).sum (fun j => levelCandCount mem loc j) ≤ 2 * X :=
        (selectHeapMatchesChain_levelCandCount_sum_le hmodOld.1 hMatchOld hOldSub).trans hOldFirst
      have hRebSufCost : selectRebuildSuffixCost mem loc newCh.toTreeChain firstReb evalCost ≤
          240 * (d + 1) + 20 + 4 * K * X := by
        unfold selectRebuildSuffixCost
        have hK60 : selectProcessEdgeCost loc.cap L evalCost + 60 ≤ K := by omega
        have hEach : ∀ j ∈ Finset.Icc firstReb d,
            selectRebuildLevelCost (levelCandCount mem loc j) (newCh.G j).m loc.cap loc.Lk evalCost + 40 ≤
            240 + (levelCandCount mem loc j + (newCh.G j).m) * K := fun j _ => by
          rw [hLocLk]
          have := selectRebuildLevelCost_le_linear (levelCandCount mem loc j) (newCh.G j).m loc.cap L evalCost
          have := Nat.mul_le_mul_left (levelCandCount mem loc j + (newCh.G j).m) hK60; omega
        have hSum := Finset.sum_le_sum hEach
        conv_rhs at hSum => rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul, Finset.sum_add_distrib]
        simp only [Nat.card_Icc, smul_eq_mul] at hSum
        have h1 : (d + 1 - firstReb) * 240 ≤ 240 * (d + 1) := by
          have := Nat.mul_le_mul_right 240 (Nat.sub_le (d + 1) firstReb); linarith
        have h2 : ((Finset.Icc firstReb d).sum (fun j => levelCandCount mem loc j) +
              (Finset.Icc firstReb d).sum (fun j => (newCh.G j).m)) * K ≤ 4 * K * X :=
          (Nat.mul_le_mul_right K (Nat.add_le_add hCandSum hSumIcc)).trans (le_of_eq (by ring))
        change (Finset.Icc firstReb d).sum (fun j =>
          selectRebuildLevelCost (levelCandCount mem loc j) (newCh.G j).m loc.cap loc.Lk evalCost + 40) + 20 ≤ _
        omega
      unfold shiftDeepSelectFixedBound
      have hMulSplit : Csuf * X = (140 * d + 750 + (selCoreLenEdgeCost L LwMax₀ + 40) + (18 * slot + 80)) * X +
          (1700 + (selCoreLenEdgeCost L LwMax₀ + 40)) * X + 1800 * (d + 1) * (L + 1) * X + 4 * K * X := by
        dsimp only [Csuf]; ring
      have hFixSplit : (2 * d + 1) * readoutCost + (d + 1) * (1800 * (d + 1) * (L + 1) + 1700) + 2800 =
          2 * d * readoutCost + readoutCost + (d + 1) * (1800 * (d + 1) * (L + 1) + 40) + 1660 * (d + 1) + 2800 := by ring
      linarith
    · have hEmpty : Finset.Icc firstReb d = ∅ := Finset.Icc_eq_empty (by omega)
      have hReb0 : selectRebuildSuffixCost mem loc newCh.toTreeChain firstReb evalCost = 20 := by
        unfold selectRebuildSuffixCost; change (Finset.Icc firstReb d).sum _ + 20 = 20; rw [hEmpty]; simp
      rw [hReb0]; unfold shiftDeepSelectFixedBound
      have h1 : 1700 * (d + 1) ≤ (d + 1) * (1800 * (d + 1) * (L + 1) + 1700) := by
        rw [Nat.mul_comm 1700 (d + 1)]; exact Nat.mul_le_mul_left (d + 1) (Nat.le_add_left _ _)
      omega
  unfold selectUpdatePostCoreRawCost selectUpdateHeapPhaseCost
    selectUpdatePostCoreFixedBound selectUpdatePostCoreToolMulBound selectUpdatePostCoreTreeMulBound
  change (240 * d + 840) + selUpdateG0Cost firstReb (newCh.G 0).m (diffLists 0).uG.length L +
      selectUpdateFPhiLenLoopCost levelU uWords diffLists stLw 0 lim L +
      selectUpdateEmbLoopCost readoutCost diffLists 0 lim slot +
      selectUpdateSuffixBlocksCost (fun j => (oldCh.toTreeChain.activeLSF j).F.F) (oldCh.G d)
        newCh readoutCost firstReb L capExp slot +
      (selectUpdateHeapPrefixLoopCost diffLists 0 lim loc.cap loc.Lk evalCost +
        selectRebuildSuffixCost mem loc newCh.toTreeChain firstReb evalCost + 50) +
      600 + 40 * (Finset.range lim).sum (fun j => (diffLists j).reemb.length) + K * chainReembPot pot newCh ≤ _
  have hToolSplit : (90 * L + 420) * Δrt +
      (670 * uWordsMul + 2 * (18 * L + 130) + 2 * (selCoreLenEdgeCost L LwMax₀ + 80)) * Δrt +
      ((5 + c) * K + 4 * (18 * slot + 160)) * Δrt + Csuf * Δrt ≤
      ((9 + c) * K + 670 * uWordsMul + (90 * slot + 720) + 1800 * (d + 1) * (L + 1) +
        4 * (selCoreLenEdgeCost L LwMax₀ + 40) + 140 * d + 126 * L + 3210) * Δrt := by
    rw [← Nat.add_mul, ← Nat.add_mul, ← Nat.add_mul]; apply Nat.mul_le_mul_right Δrt
    dsimp only [Csuf]; set A := 1800 * (d + 1) * (L + 1); set B := selCoreLenEdgeCost L LwMax₀
    have hK5 : (5 + c) * K = 5 * K + c * K := by ring
    have hK9 : (9 + c) * K = 9 * K + c * K := by ring
    linarith
  have hTreeSplit : (K + 18 * slot + 650) * Δtu = 490 * Δtu + (K + 18 * slot + 160) * Δtu := by ring
  have hFixSplit : d * (readoutCost + K * c + 1600) = d * (readoutCost + K * c + 1070) + 460 * d + 70 * d := by ring
  dsimp only [Csuf] at hCostSuf hToolSplit; linarith

end MinCostFlow.MinRatio
