module

public import MinCostFlow.MinRatio.WireShiftDeepSpecKFBL
public import MinCostFlow.MinRatio.OrdSolverToolMono
public import MinCostFlow.MinRatio.WireInitBase
import MinCostFlow.MinRatio.InitPathTreeChainHelpers
import MinCostFlow.Chain.Ordered.BudgetHelpersCost
import MinCostFlow.LSF.Components

/-!
# Model facts of the deep shift from `ShiftLoopChainInv` (`ShiftDeepModelFacts`)

Derives the model premises of `ShiftDeepChainSyncSpecWExtKFBL` (`WireShiftDeepSpecKFBL.lean`) for a
non-terminal shift `i < cfg.P.d` from `Chain.Ordered.ShiftLoopChainInv cfg model.chain`:

* `levelHistory_sparseCoreOrdInput`: every level `j < cfg.P.d` of a chain satisfying `ChainInv`
  meets `SparseCoreOrdInput` (by induction along `LevelHistory`).
* `chainInv_rot_isRotationOrder` and `chainInv_ordRotWords_le`: at every level `j < cfg.P.d` of a
  chain satisfying `ChainInv`, the output order `cfg.T.rot (ch.scState j) (ch.bran j)` is a valid
  rotation of `ch.G (j + 1)`, so `ordRotWords (chainLevelOrdAbs ch j) (ch.bran j) ≤
  1 + 2 * ch.N₀ + 2 * (ch.G (j + 1)).m` via `ordWordsOn_eq_of_isRotationOrder` (no extra tool
  hypothesis is needed).
* `shiftDeepModelInvKFBL_of_loopInv`: proves all three conjuncts of `ShiftDeepModelInvKFBL`
  directly from `cfg.ValidOrdNoHidden` and `ShiftLoopChainInv`.
* `chainSuffixForests_edgeSum_le` and `shiftDeep_forestEdgeSum_le`: bounds
  `graphListEdgeSum (chainSuffixForests model.chain i.val) +
   graphListEdgeSum (chainSuffixForests model'.chain i.val)` by `2 * (cfg.P.d + 1) * (model.chain.G 0).n`
  (and `2 * (cfg.P.d + 1) * cfg.N₀`).
* `shiftDeepModelInv_of_loopInv`: proves `ShiftDeepModelInv` and `ShiftDeepModelInvKFBL` from
  `cfg.ValidOrdNoHidden`, `ShiftLoopChainInv`, and the five named non-chain hypotheses:
  1. `hMono : ToolCostMono cfg.T` (tool cost monotonicity under restart);
  2. `hLastEq : LastLevelBuildEqOnE cfg.L` (last-level tool extensionality on `G.E`);
  3. `hWordLvl` (word-size bounds `levelM j < 2 ^ w` and `(levelM j + N₀ + 2) ^ wordExp * (L + 1) < 2 ^ w`);
  4. `hCoreLenFits` (fixed-point `Num.Fits 4 L` for `chainLen` at levels `i + 1, …, d` of `next`);
  5. `hLastStretchFits` (last-level stretch capacity bound at level `d` of `next`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain Bundle SparseCore.Program

private theorem foldl_restart_sparseCoreOrdInput {T : SparseCoreRestartTool} {k M N : ℕ}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ} :
    ∀ (rs : List ℕ) (st : T.State),
      SparseCoreOrdInput T k M N st G ord n →
      (∀ j ∈ rs, j < k) →
      SparseCoreOrdInput T k M N (rs.foldl T.restart st) G ord n
  | [], _, hIn, _ => hIn
  | j :: rs, st, hIn, hrs => by
    simp only [List.foldl_cons]
    exact foldl_restart_sparseCoreOrdInput rs (T.restart st j)
      (SparseCoreOrdInput.restart hIn j (hrs j (List.mem_cons_self ..)))
      (fun b hb => hrs b (List.mem_cons_of_mem j hb))

private theorem rotation_cast_order {G₁ G₂ : MGraph} (hEq : G₁ = G₂) (ρ : Rotation G₁) :
    (hEq ▸ ρ).order = ρ.order := by
  subst hEq; rfl

/-- From a `LevelHistory` at level `i`, the tool state, graph, order, and update count satisfy
`SparseCoreOrdInput`. -/
theorem levelHistory_sparseCoreOrdInput {T : SparseCoreRestartTool} {TP : SparseCoreParams}
    {P : ChainParams} {N₀ : ℕ} {ch : ChainState T P} {i : ℕ}
    (H : Ordered.LevelHistory T TP P N₀ ch i) :
    SparseCoreOrdInput T P.k (levelM TP P i) N₀ (ch.scState i) (ch.G i) (ch.levelOrd i)
      (ch.updCount i) := by
  have hStep : ∀ t ≤ H.len,
      SparseCoreOrdInput T P.k (levelM TP P i) N₀
        (T.runOrdAfterRestarts P.k (levelM TP P i) N₀ H.D H.ord H.restarts t)
        (H.D.G t) (H.ord t) ((Finset.Icc 1 t).sum fun s => (H.D.U s).length) := by
    intro t
    induction t with
    | zero =>
      intro _
      have hSum0 : ((Finset.Icc 1 0).sum fun s => (H.D.U s).length) = 0 := by
        simp
      rw [hSum0]
      unfold SparseCoreRestartTool.runOrdAfterRestarts SparseCoreRestartTool.runOrdAfterUpdate
      dsimp only
      refine foldl_restart_sparseCoreOrdInput (H.restarts 0) _ ?_ (H.hRestartsLt 0 (Nat.zero_le _))
      exact SparseCoreOrdInput.init (H.D.G 0) (H.D.ℓ 0) (H.D.g 0) (H.ord 0)
        H.hG0 H.hInitMBound H.hInitNBound (H.hℓPos 0 (Nat.zero_le _))
        (Ordered.rotation_of_orderedUpTo H.hOrd (Nat.zero_le _))
    | succ t ih =>
      intro ht
      have hPrev := ih (Nat.le_of_succ_le ht)
      obtain ⟨hValidU, hEqG⟩ := H.hD (t + 1) (Nat.succ_pos t) ht
      simp only [Nat.add_sub_cancel] at hValidU hEqG
      have hOrdBatch : OrderedBatch (H.D.G t) (H.D.U (t + 1)) (H.ord t) (H.ord (t + 1)) := by
        obtain ⟨ρ, hρ, hRB⟩ := H.hOrd
        obtain ⟨hEq', hBatch⟩ := hRB t (Nat.lt_of_succ_le ht)
        refine ⟨ρ t, hEq' ▸ ρ (t + 1), hρ t (Nat.le_of_succ_le ht), ?_, hBatch⟩
        rw [rotation_cast_order hEq']
        exact hρ (t + 1) ht
      have hSumEq : ((Finset.Icc 1 t).sum fun s => (H.D.U s).length) + (H.D.U (t + 1)).length =
          (Finset.Icc 1 (t + 1)).sum fun s => (H.D.U s).length := by
        rw [Finset.sum_Icc_succ_top (Nat.succ_pos t)]
      have hSumLe : ((Finset.Icc 1 t).sum fun s => (H.D.U s).length) + (H.D.U (t + 1)).length ≤
          ch.updCount i := by
        rw [hSumEq, ← H.hUpd]
        exact Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right ht)
      have hThr : ((((Finset.Icc 1 t).sum fun s => (H.D.U s).length) + (H.D.U (t + 1)).length : ℕ) : ℝ) ≤
          SparseCoreTool.updateThreshold P.k (levelM TP P i) N₀ :=
        le_trans (by exact_mod_cast hSumLe) H.hThresh
      have hPos' : ∀ e ∈ ((H.D.G t).applyBatch (H.D.U (t + 1))).E, 0 < H.D.ℓ (t + 1) e := by
        rw [← hEqG]
        exact H.hℓPos (t + 1) ht
      have hUpdIn : SparseCoreOrdInput T P.k (levelM TP P i) N₀
          (T.runOrdAfterUpdate P.k (levelM TP P i) N₀ H.D H.ord H.restarts (t + 1)).1
          (H.D.G (t + 1)) (H.ord (t + 1))
          ((Finset.Icc 1 (t + 1)).sum fun s => (H.D.U s).length) := by
        rw [SparseCoreRestartTool.runOrdAfterUpdate_succ, hEqG, ← hSumEq]
        exact SparseCoreOrdInput.update hPrev (H.D.U (t + 1)) (H.D.ℓ (t + 1)) (H.D.g (t + 1))
          (H.ord (t + 1)) hValidU hPos' hOrdBatch hThr
      unfold SparseCoreRestartTool.runOrdAfterRestarts
      exact foldl_restart_sparseCoreOrdInput (H.restarts (t + 1)) _ hUpdIn
        (H.hRestartsLt (t + 1) ht)
  have hAt := hStep H.len le_rfl
  rw [← H.hRun, H.hEndG, H.hEndOrd, H.hUpd] at hAt
  exact hAt

/-- Under `ChainInv`, the input order `ch.levelOrd j` at every level `j < cfg.P.d` is a valid
rotation of `ch.G j`. -/
theorem chainInv_levelOrd_isRotationOrder {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    {ch : ChainState T P} (hInv : Ordered.ChainInv T L TP LP P N₀ ch) {j : ℕ} (hj : j < P.d) :
    IsRotationOrder (ch.G j) (ch.levelOrd j) := by
  obtain ⟨H⟩ := hInv.hHist j hj
  exact Ordered.exists_rotation_of_eq H.hEndG H.hEndOrd (Ordered.rotation_of_orderedUpTo H.hOrd le_rfl)

/-- Under `ChainInv`, the output order `T.rot (ch.scState j) (ch.bran j)` of the active branch at
level `j < P.d` is a valid rotation of `ch.G (j + 1)`. -/
theorem chainInv_rot_isRotationOrder {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    {ch : ChainState T P} (hInv : Ordered.ChainInv T L TP LP P N₀ ch) {j : ℕ} (hj : j < P.d) :
    IsRotationOrder (ch.G (j + 1)) (T.rot (ch.scState j) (ch.bran j)) := by
  obtain ⟨H⟩ := hInv.hHist j hj
  have hSpec := H.hOK.noHidden P.k H.len (levelM TP P j) N₀ H.D H.ord H.restarts
    P.hk H.hG0 H.hD H.hLen H.hℓPos H.hOrd H.hInitMBound H.hInitNBound H.hRestartsLt
    (H.hUpd.symm ▸ H.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hOrdOut := hSpec.2.2.2.2.1 H.s₀ H.len H.hs₀ le_rfl (ch.bran j) (hInv.hBran j hj)
    H.hS0Fresh H.hNoRestartAfterS0
  have hRot := Ordered.rotation_of_orderedUpTo hOrdOut (le_refl (H.len - H.s₀))
  have hAdd : H.s₀ + (H.len - H.s₀) = H.len := Nat.add_sub_of_le H.hs₀
  refine Ordered.exists_rotation_of_eq ?_ ?_ hRot
  · simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hAdd, ← H.hRun]
    exact (hInv.hGSucc j hj).symm
  · dsimp only
    rw [hAdd, ← H.hRun]

/-- Under `ChainInv` and `cfg.ValidOrdNoHidden`, the word length of the active output rotation
order at level `j < cfg.P.d` is at most `1 + 2 * ch.N₀ + 2 * (ch.G (j + 1)).m`. -/
theorem chainInv_ordRotWords_le {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {ch : ChainState cfg.T cfg.P}
    (hInv : Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch) {j : ℕ} (hj : j < cfg.P.d) :
    ordRotWords (chainLevelOrdAbs ch j) (ch.bran j) ≤
      1 + 2 * ch.N₀ + 2 * (ch.G (j + 1)).m := by
  have hB := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hInv
  have hValid := (hB (j + 1) hj).1
  have hVsub := (hB (j + 1) hj).2.1
  have hnLe : (ch.G (j + 1)).n ≤ ch.N₀ := by
    rw [hInv.hN0]
    exact (Finset.card_le_card hVsub).trans hInv.hG0n
  have hRot := chainInv_rot_isRotationOrder hInv hj
  unfold ordRotWords chainLevelOrdAbs
  dsimp only
  rw [← hInv.hGSucc j hj, ordWordsOn_eq_of_isRotationOrder hValid hRot]
  omega

/-- Under `ChainInv` and `cfg.ValidOrdNoHidden`, the word length of the active output rotation
order at level `j < cfg.P.d` is at most `1 + 2 * (ch.G (j + 1)).n + 2 * (ch.G (j + 1)).m`. -/
theorem chainInv_ordRotWords_live_le {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {ch : ChainState cfg.T cfg.P}
    (hInv : Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch) {j : ℕ} (hj : j < cfg.P.d) :
    ordRotWords (chainLevelOrdAbs ch j) (ch.bran j) ≤
      1 + 2 * (ch.G (j + 1)).n + 2 * (ch.G (j + 1)).m := by
  have hB := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hInv
  have hValid := (hB (j + 1) hj).1
  have hRot := chainInv_rot_isRotationOrder hInv hj
  unfold ordRotWords chainLevelOrdAbs
  dsimp only
  rw [← hInv.hGSucc j hj, ordWordsOn_eq_of_isRotationOrder hValid hRot]
  omega

/-- All conjuncts of `ShiftDeepModelInvKFBL` follow directly from `cfg.ValidOrdNoHidden`
and `ShiftLoopChainInv` with no additional hypotheses. -/
theorem shiftDeepModelInvKFBL_of_loopInv {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {model : Alg2State cfg} (hLoopInv : Ordered.ShiftLoopChainInv cfg model.chain)
    {i : Fin (cfg.P.d + 1)} (hiLt : i.val < cfg.P.d) :
    ShiftDeepModelInvKFBL model i := by
  have hLoopInv' : Ordered.ShiftLoopChainInv cfg (alg2LoopShiftStep cfg model i).chain := by
    change Ordered.ShiftLoopChainInv cfg (Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    exact hLoopInv.shift hV i.val hiLt.le
  set next := (alg2LoopShiftStep cfg model i).chain
  have hB0 := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hLoopInv.1
  have hBN := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hLoopInv'.1
  refine ⟨shiftLoopLevelFacts_of_inv hV hLoopInv, shiftLoopLevelFacts_of_inv hV hLoopInv',
    fun j _ hj => chainInv_ordRotWords_live_le hV hLoopInv'.1 hj,
    fun j hj => (Finset.card_le_card (hBN j hj).2.1).trans (hLoopInv'.1.hN0 ▸ hLoopInv'.1.hG0n),
    fun j _ hj => ?_, ?_, ?_, fun j hj => (hBN j hj).1,
    fun j hj => by exact_mod_cast (hBN j hj).2.2.1,
    (Ordered.ChainInv.levels_connected hV.hTP hV.hγM₀ hV.hγk hLoopInv'.1 hLoopInv'.2.2.2
      cfg.P.d le_rfl).1, ?_⟩
  · have hAct0 := (hB0 j (Nat.le_of_lt hj)).2.2.2.2 hj (model.chain.bran j) (hLoopInv.1.hBran j hj)
    have hActN := (hBN j (Nat.le_of_lt hj)).2.2.2.2 hj (next.bran j) (hLoopInv'.1.hBran j hj)
    refine ⟨le_of_eq hAct0.1.2.1.2.1, hAct0.1.2.1.2.2.2.2.2.1, ?_, hActN.1.2.1.2.2.2.2.2.1, ?_⟩
    · rw [hLoopInv.1.hGSucc j hj]; exact hAct0.2.1.2.1.trans Finset.sdiff_subset
    · rw [hLoopInv'.1.hGSucc j hj]; exact hActN.2.1.2.1.trans Finset.sdiff_subset
  · exact (hLoopInv.1.hLastHolds model.chain.lastBran hLoopInv.1.hLastBran).2.1.2.2.2.2.2.1
  · exact (hLoopInv'.1.hLastHolds next.lastBran hLoopInv'.1.hLastBran).2.1.2.2.2.2.2.1
  · have hSub0 : ∀ j ≤ cfg.P.d, (next.G j).E ⊆ (next.G 0).E := by
      intro j
      induction j with
      | zero => intro _; exact Finset.Subset.refl _
      | succ j ih =>
        intro hj
        have hActN := (hBN j (Nat.le_of_lt hj)).2.2.2.2 hj (next.bran j) (hLoopInv'.1.hBran j hj)
        have hGN : (next.G (j + 1)).E ⊆ (next.G j).E := by
          rw [hLoopInv'.1.hGSucc j hj]; exact hActN.2.1.2.1.trans Finset.sdiff_subset
        exact hGN.trans (ih (Nat.le_of_lt hj))
    have hG0Eq : next.G 0 = model.chain.G 0 :=
      (ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P model.chain hiLt).1 0 (Nat.zero_le _)
    exact hG0Eq ▸ Finset.card_le_card (hSub0 cfg.P.d le_rfl)

/-- Each edge set in the chain satisfies `(ch.G (j + 1)).E ⊆ (ch.G j).E` for `j < cfg.P.d`. -/
theorem chainInv_G_succ_E_subset {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {ch : ChainState cfg.T cfg.P}
    (hInv : Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch) {j : ℕ} (hj : j < cfg.P.d) :
    (ch.G (j + 1)).E ⊆ (ch.G j).E := by
  have hB := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hInv
  have hSp := ((hB j (Nat.le_of_lt hj)).2.2.2.2 hj (ch.bran j) (hInv.hBran j hj)).2
  rw [hInv.hGSucc j hj]
  exact hSp.1.2.1.trans Finset.sdiff_subset

/-- Under `ChainInv` and `cfg.ValidOrdNoHidden`, each active LSF forest at level `j ≤ cfg.P.d`
has at most `(ch.G 0).n` edges. -/
theorem activeLSF_m_le_G0_n {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {ch : ChainState cfg.T cfg.P}
    (hInv : Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch) {j : ℕ} (hj : j ≤ cfg.P.d) :
    (ch.toTreeChain.activeLSF j).F.F.m ≤ (ch.G 0).n := by
  have hB := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hInv
  have hHolds : (ch.toTreeChain.activeLSF j).Holds (ch.G j)
      (ch.toTreeChain.chainLen ch.ℓ j)
      (if j < cfg.P.d then cfg.TP.σ cfg.P.k (ch.G 0).n else cfg.LP.σ_last (ch.G cfg.P.d).n) := by
    by_cases hlt : j < cfg.P.d
    · simp only [TreeChain.activeLSF, ChainState.toTreeChain, hlt, ↓reduceIte]
      exact ((hB j hj).2.2.2.2 hlt (ch.bran j) (hInv.hBran j hlt)).1
    · have hjeq : j = cfg.P.d := by omega
      subst hjeq
      simp only [TreeChain.activeLSF, ChainState.toTreeChain, lt_irrefl, ↓reduceIte]
      exact hInv.hLastHolds ch.lastBran hInv.hLastBran
  have hForest : (ch.toTreeChain.activeLSF j).F.F.IsForest := hHolds.2.1.1
  have hFCard : (ch.toTreeChain.activeLSF j).F.F.E.card ≤ (ch.toTreeChain.activeLSF j).F.F.V.card := by
    have hc := LSF.forest_components_add_edges (ch.toTreeChain.activeLSF j).F.F hForest
    omega
  have hVsub : (ch.toTreeChain.activeLSF j).F.F.V ⊆ (ch.G j).V := hHolds.2.1.2.2.2.2.1
  exact le_trans hFCard (Finset.card_le_card (hVsub.trans (hB j hj).2.1))

/-- The total edge count of `chainSuffixForests ch first` is at most
`(cfg.P.d - first + 1) * (ch.G 0).n` (hence at most `(cfg.P.d + 1) * cfg.N₀`). -/
theorem chainSuffixForests_edgeSum_le {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {ch : ChainState cfg.T cfg.P}
    (hInv : Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch) {first : ℕ} (hfirst : first ≤ cfg.P.d) :
    graphListEdgeSum (chainSuffixForests ch first) ≤ (cfg.P.d - first + 1) * (ch.G 0).n := by
  have hAll : ∀ F ∈ chainSuffixForests ch first, F.m ≤ (ch.G 0).n := by
    intro F hF
    simp only [chainSuffixForests, List.mem_append, List.mem_map, List.mem_range,
      List.mem_singleton] at hF
    rcases hF with ⟨t, ht, rfl⟩ | rfl
    · have hlt : first + t < cfg.P.d := by omega
      have h := activeLSF_m_le_G0_n hV hInv (Nat.le_of_lt hlt)
      simpa [TreeChain.activeLSF, ChainState.toTreeChain, hlt] using h
    · have h := activeLSF_m_le_G0_n hV hInv (le_refl cfg.P.d)
      simpa [TreeChain.activeLSF, ChainState.toTreeChain] using h
  have hSum : ∀ (Fs : List MGraph), (∀ F ∈ Fs, F.m ≤ (ch.G 0).n) →
      graphListEdgeSum Fs ≤ Fs.length * (ch.G 0).n := by
    intro Fs
    induction Fs with
    | nil => intro _; simp [graphListEdgeSum]
    | cons F rest ih =>
      intro hmem
      have h1 := hmem F (List.mem_cons_self ..)
      have h2 := ih (fun G hG => hmem G (List.mem_cons_of_mem F hG))
      simp only [graphListEdgeSum, List.map_cons, List.sum_cons, List.length_cons] at h2 ⊢
      rw [Nat.succ_mul]
      omega
  simpa [chainSuffixForests_length] using hSum (chainSuffixForests ch first) hAll

/-- Combined old and new suffix forest edge count across a deep shift `i < cfg.P.d`:
at most `2 * (cfg.P.d + 1) * (model.chain.G 0).n` (and at most `2 * (cfg.P.d + 1) * cfg.N₀`). -/
theorem shiftDeep_forestEdgeSum_le {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {model : Alg2State cfg} (hLoopInv : Ordered.ShiftLoopChainInv cfg model.chain)
    {i : Fin (cfg.P.d + 1)} (hiLt : i.val < cfg.P.d) :
    let model' := alg2LoopShiftStep cfg model i
    graphListEdgeSum (chainSuffixForests model.chain i.val) +
      graphListEdgeSum (chainSuffixForests model'.chain i.val) ≤
      2 * (cfg.P.d + 1) * (model.chain.G 0).n ∧
    graphListEdgeSum (chainSuffixForests model.chain i.val) +
      graphListEdgeSum (chainSuffixForests model'.chain i.val) ≤
      2 * (cfg.P.d + 1) * cfg.N₀ := by
  dsimp only
  set model' := alg2LoopShiftStep cfg model i
  have hLoopInv' : Ordered.ShiftLoopChainInv cfg model'.chain := by
    change Ordered.ShiftLoopChainInv cfg (Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    exact hLoopInv.shift hV i.val hiLt.le
  have hEx := ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P model.chain hiLt
  have hG0Eq : model'.chain.G 0 = model.chain.G 0 := hEx.1 0 (Nat.zero_le _)
  have h1 := chainSuffixForests_edgeSum_le hV hLoopInv.1 hiLt.le
  have h2 := chainSuffixForests_edgeSum_le hV hLoopInv'.1 hiLt.le
  rw [hG0Eq] at h2
  have hlenLe : cfg.P.d - i.val + 1 ≤ cfg.P.d + 1 := by omega
  have h1' := h1.trans (Nat.mul_le_mul_right _ hlenLe)
  have h2' := h2.trans (Nat.mul_le_mul_right _ hlenLe)
  have hnLe : (model.chain.G 0).n ≤ cfg.N₀ := hLoopInv.1.hG0n
  have hBoth : graphListEdgeSum (chainSuffixForests model.chain i.val) +
      graphListEdgeSum (chainSuffixForests model'.chain i.val) ≤
      2 * (cfg.P.d + 1) * (model.chain.G 0).n := by
    have : 2 * (cfg.P.d + 1) * (model.chain.G 0).n =
        (cfg.P.d + 1) * (model.chain.G 0).n + (cfg.P.d + 1) * (model.chain.G 0).n := by ring
    omega
  exact ⟨hBoth, hBoth.trans (Nat.mul_le_mul_left _ hnLe)⟩

/-- Pairwise edge-disjointness of the active forests along a chain implies that the sum of edge
counts in `chainSuffixForests ch first` equals the cardinality of their union, hence is at most
`(ch.G 0).n` (closing the `(cfg.P.d + 1)` slack in `chainSuffixForests_edgeSum_le`). -/
theorem chainSuffixForests_edgeSum_le_G0_n {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {ch : ChainState cfg.T cfg.P}
    (hInv : Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    {first : ℕ} (hfirst : first ≤ cfg.P.d) :
    graphListEdgeSum (chainSuffixForests ch first) ≤ (ch.G 0).n := by
  have hHolds := (hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hSub := ch.toTreeChain.forestsAreSubgraphs_of_holds hHolds
  have hTreeForest : ch.toTreeChain.chainTree.IsForest :=
    ch.toTreeChain.chainTree_isForest hHolds hSub
  have hTreeCard : ch.toTreeChain.chainTree.E.card ≤ (ch.G 0).n := by
    have hc := LSF.forest_components_add_edges ch.toTreeChain.chainTree hTreeForest
    have hVeq : ch.toTreeChain.chainTree.V = (ch.G 0).V := rfl
    rw [hVeq] at hc
    change ch.toTreeChain.chainTree.E.card ≤ (ch.G 0).V.card
    omega
  have hDisjPair : ∀ a b, a < b → b ≤ cfg.P.d →
      Disjoint (ch.toTreeChain.activeLSF a).F.F.E (ch.toTreeChain.activeLSF b).F.F.E := by
    intro a b hab hbd
    have hPref := initChain_prefix_disjoint hHolds hbd
    have hSubA : (ch.toTreeChain.activeLSF a).F.F.E ⊆
        (Finset.range b).biUnion (fun j => (ch.toTreeChain.activeLSF j).F.F.E) :=
      Finset.subset_biUnion_of_mem (fun j => (ch.toTreeChain.activeLSF j).F.F.E)
        (Finset.mem_range.mpr hab)
    exact Finset.disjoint_of_subset_left hSubA hPref
  have hRangeEq :
      ((List.range (cfg.P.d - first)).map
        (fun t => ((cfg.T.lsfs (ch.scState (first + t)) (ch.bran (first + t))).F.F).m)).sum =
      ∑ t ∈ Finset.range (cfg.P.d - first),
        ((ch.toTreeChain.activeLSF (first + t)).F.F.E).card := by
    rw [← List.sum_toFinset _ (List.nodup_range)]
    · rw [List.toFinset_range]
      refine Finset.sum_congr rfl fun t ht => ?_
      have hlt : first + t < cfg.P.d := by have := Finset.mem_range.mp ht; omega
      simp [TreeChain.activeLSF, ChainState.toTreeChain, hlt, MGraph.m]
  have hSumEq : graphListEdgeSum (chainSuffixForests ch first) =
      ∑ j ∈ Finset.Ico first (cfg.P.d + 1), (ch.toTreeChain.activeLSF j).F.F.E.card := by
    unfold graphListEdgeSum chainSuffixForests
    rw [List.map_append, List.sum_append, List.map_map, List.map_singleton, List.sum_singleton]
    have h1 : ((List.range (cfg.P.d - first)).map
        (MGraph.m ∘ fun t => (cfg.T.lsfs (ch.scState (first + t)) (ch.bran (first + t))).F.F)).sum =
        ∑ t ∈ Finset.range (cfg.P.d - first), (ch.toTreeChain.activeLSF (first + t)).F.F.E.card :=
      hRangeEq
    rw [h1]
    have hIco : Finset.Ico first (cfg.P.d + 1) =
        insert cfg.P.d ((Finset.range (cfg.P.d - first)).image (first + ·)) := by
      ext j
      simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      constructor
      · intro ⟨h1, h2⟩
        rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h2) with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ⟨j - first, by omega, by omega⟩
      · rintro (rfl | ⟨t, ht, rfl⟩) <;> omega
    rw [hIco, Finset.sum_insert (by simp; omega),
      Finset.sum_image (fun a _ b _ h => by omega)]
    have hLast : (ch.lastLSFs ch.lastBran).F.F.m =
        (ch.toTreeChain.activeLSF cfg.P.d).F.F.E.card := by
      simp [TreeChain.activeLSF, ChainState.toTreeChain, MGraph.m]
    rw [hLast, Nat.add_comm]
  have hCardEq :
      (∑ j ∈ Finset.Ico first (cfg.P.d + 1), (ch.toTreeChain.activeLSF j).F.F.E.card) =
      ((Finset.Ico first (cfg.P.d + 1)).biUnion
        fun j => (ch.toTreeChain.activeLSF j).F.F.E).card := by
    symm
    refine Finset.card_biUnion fun a ha b hb hne => ?_
    have ha' := Finset.mem_Ico.mp ha
    have hb' := Finset.mem_Ico.mp hb
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hDisjPair a b hlt (by omega)
    · exact (hDisjPair b a hgt (by omega)).symm
  have hSubTree : ((Finset.Ico first (cfg.P.d + 1)).biUnion
        fun j => (ch.toTreeChain.activeLSF j).F.F.E) ⊆ ch.toTreeChain.chainTree.E := by
    intro e he
    obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp he
    have hj' := Finset.mem_Ico.mp hj
    simp only [TreeChain.chainTree, TreeChain.chainTreeEdges, ChainState.toTreeChain,
      Finset.mem_biUnion, Finset.mem_range]
    exact ⟨j, hj'.2, hej⟩
  rw [hSumEq, hCardEq]
  exact (Finset.card_le_card hSubTree).trans hTreeCard

/-- Tight combined old and new suffix forest edge count across a deep shift `i < cfg.P.d`:
at most `2 * (model.chain.G 0).n` (and at most `2 * cfg.N₀`). -/
theorem shiftDeep_forestEdgeSum_le_two_G0_n {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {model : Alg2State cfg} (hLoopInv : Ordered.ShiftLoopChainInv cfg model.chain)
    {i : Fin (cfg.P.d + 1)} (hiLt : i.val < cfg.P.d) :
    let model' := alg2LoopShiftStep cfg model i
    graphListEdgeSum (chainSuffixForests model.chain i.val) +
      graphListEdgeSum (chainSuffixForests model'.chain i.val) ≤
      2 * (model.chain.G 0).n ∧
    graphListEdgeSum (chainSuffixForests model.chain i.val) +
      graphListEdgeSum (chainSuffixForests model'.chain i.val) ≤
      2 * cfg.N₀ := by
  dsimp only
  set model' := alg2LoopShiftStep cfg model i
  have hLoopInv' : Ordered.ShiftLoopChainInv cfg model'.chain := by
    change Ordered.ShiftLoopChainInv cfg (Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    exact hLoopInv.shift hV i.val hiLt.le
  have hEx := ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P model.chain hiLt
  have hG0Eq : model'.chain.G 0 = model.chain.G 0 := hEx.1 0 (Nat.zero_le _)
  have h1 := chainSuffixForests_edgeSum_le_G0_n hV hLoopInv.1 hiLt.le
  have h2 := chainSuffixForests_edgeSum_le_G0_n hV hLoopInv'.1 hiLt.le
  rw [hG0Eq] at h2
  have hnLe : (model.chain.G 0).n ≤ cfg.N₀ := hLoopInv.1.hG0n
  exact ⟨by omega, by omega⟩

/-- Helper: when `1 ≤ wordExp`, the single word-size inequality
`(M + N + 2) ^ wordExp * (L + 1) < 2 ^ w` implies `M < 2 ^ w`. -/
theorem wordLvl_of_wordExp_pos {w L wordExp M N : ℕ} (hwe : 1 ≤ wordExp)
    (h : (M + N + 2) ^ wordExp * (L + 1) < 2 ^ w) :
    M < 2 ^ w := by
  have h1 : M ≤ M + N + 2 := by omega
  have h2 : M + N + 2 ≤ (M + N + 2) ^ wordExp := Nat.le_self_pow (by omega) _
  have h3 : (M + N + 2) ^ wordExp ≤ (M + N + 2) ^ wordExp * (L + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos L)
  exact lt_of_le_of_lt (h1.trans (h2.trans h3)) h

/-- **Model facts of a deep shift (`ShiftDeepModelInv` and `ShiftDeepModelInvKFBL`) from
`ShiftLoopChainInv`.** All chain, history, rotation-order, forest, inclusion, and prefix-disjointness
clauses (including every conjunct of `ShiftDeepModelInvKFBL`) follow from `cfg.ValidOrdNoHidden`
and `ShiftLoopChainInv`. The other five non-chain clauses are hypotheses of the theorem:
1. `hMono : ToolCostMono cfg.T`
2. `hLastEq : LastLevelBuildEqOnE cfg.L`
3. `hWordLvl`: per-level word-size bounds `levelM j < 2 ^ w` and
   `(levelM j + N₀ + 2) ^ wordExp * (L + 1) < 2 ^ w`
4. `hCoreLenFits`: fixed-point `Num.Fits 4 L` for `chainLen` on levels `i + 1, …, d` of `next`
5. `hLastStretchFits`: last-level stretch bound at level `d` of `next`. -/
theorem shiftDeepModelInv_of_loopInv {w L P wordExp stretchPrec : ℕ} {cfg : Alg2Config}
    {model : Alg2State cfg} {i : Fin (cfg.P.d + 1)}
    (hV : cfg.ValidOrdNoHidden)
    (hLoopInv : Ordered.ShiftLoopChainInv cfg model.chain)
    (hiLt : i.val < cfg.P.d)
    (hMono : ToolCostMono cfg.T)
    (hLastEq : LastLevelBuildEqOnE cfg.L)
    (hWordLvl : ∀ j < cfg.P.d,
      levelM cfg.TP cfg.P j < 2 ^ w ∧
      (levelM cfg.TP cfg.P j + cfg.N₀ + 2) ^ wordExp * (L + 1) < 2 ^ w)
    (hCoreLenFits :
      let next := (alg2LoopShiftStep cfg model i).chain
      ∀ j, i.val ≤ j → j < cfg.P.d → ∀ e ∈ (next.G (j + 1)).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P =
          next.toTreeChain.chainLen next.ℓ (j + 1) e)
    (hLastStretchFits :
      let next := (alg2LoopShiftStep cfg model i).chain
      ∀ e ∈ (next.G cfg.P.d).E,
        2 * (2 : ℝ) ^ stretchPrec *
          lastLevelStretchBound (next.G cfg.P.d)
            (next.toTreeChain.chainLen next.ℓ cfg.P.d) e <
          Num.capacity 4 L) :
    ShiftDeepModelInv w L P wordExp stretchPrec model i ∧
    ShiftDeepModelInvKFBL model i := by
  set model' := alg2LoopShiftStep cfg model i
  have hChain' : model'.chain = (Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1 := rfl
  have hInv : Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ model.chain := hLoopInv.1
  have hLoopInv' : Ordered.ShiftLoopChainInv cfg model'.chain := hChain' ▸ hLoopInv.shift hV i.val hiLt.le
  have hInv' : Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ model'.chain := hLoopInv'.1
  have hEx := ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P model.chain hiLt
  have hB' := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hInv'
  have hHolds := (hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hSub := model.chain.toTreeChain.forestsAreSubgraphs_of_holds hHolds
  have hHolds' := (hInv'.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hSub' := model'.chain.toTreeChain.forestsAreSubgraphs_of_holds hHolds'
  have hG0Eq : model'.chain.G 0 = model.chain.G 0 := hEx.1 0 (Nat.zero_le _)
  have hGiEq : model'.chain.G i.val = model.chain.G i.val := hEx.1 i.val le_rfl
  have hℓEq : model'.chain.ℓ = model.chain.ℓ := hEx.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hOldSubG0 : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E :=
    (model.chain.toTreeChain.chainTree_isSubgraph hHolds hSub).2.1
  have hNewSubG0 : model'.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E :=
    hG0Eq ▸ (model'.chain.toTreeChain.chainTree_isSubgraph hHolds' hSub').2.1
  have hActiveSub (ch : ChainState cfg.T cfg.P) (j : ℕ) (hj : j ≤ cfg.P.d) :
      (ch.toTreeChain.activeLSF j).F.F.E ⊆ ch.toTreeChain.chainTree.E := by
    intro e he
    simp only [TreeChain.chainTree, TreeChain.chainTreeEdges, ChainState.toTreeChain,
      Finset.mem_biUnion, Finset.mem_range]
    exact ⟨j, Nat.lt_succ_of_le hj, he⟩
  have hCostMono : cfg.T.cost (model.chain.scState i.val) ≤ cfg.T.cost (model'.chain.scState i.val) := by
    have hScI : model'.chain.scState i.val =
        cfg.T.restart (model.chain.scState i.val) ((model.chain.bran i.val + 1) % cfg.P.k) :=
      hEx.2.2.1
    rw [hScI]
    exact hMono.2 _ _
  have hDisjPref :
      Disjoint
        ((Finset.range i.val).biUnion fun j => (model.chain.toTreeChain.activeLSF j).F.F.E)
        (graphListEdgeUnion (chainSuffixForests model.chain i.val) ∪
          graphListEdgeUnion (chainSuffixForests model'.chain i.val)) := by
    rw [Finset.disjoint_union_right, graphListEdgeUnion_chainSuffixForests model.chain hiLt.le,
      graphListEdgeUnion_chainSuffixForests model'.chain hiLt.le]
    constructor
    · rw [Finset.disjoint_biUnion_right]
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      have hDisjJ := initChain_prefix_disjoint hHolds (Nat.lt_succ_iff.mp hj2)
      exact Finset.disjoint_of_subset_left
        (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono hj1)) hDisjJ
    · have hPrefEq :
          (Finset.range i.val).biUnion (fun j => (model.chain.toTreeChain.activeLSF j).F.F.E) =
          (Finset.range i.val).biUnion (fun j => (model'.chain.toTreeChain.activeLSF j).F.F.E) := by
        refine Finset.biUnion_congr rfl fun j hj => ?_
        have hji : j < i.val := Finset.mem_range.mp hj
        have hjd : j < cfg.P.d := lt_trans hji hiLt
        obtain ⟨hsc, hbr, _⟩ := hEx.2.1 j hji
        simp only [TreeChain.activeLSF, ChainState.toTreeChain, hjd, ↓reduceIte, hChain', hsc, hbr]
      rw [hPrefEq, Finset.disjoint_biUnion_right]
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      have hDisjJ := initChain_prefix_disjoint hHolds' (Nat.lt_succ_iff.mp hj2)
      exact Finset.disjoint_of_subset_left
        (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono hj1)) hDisjJ
  refine ⟨?_, shiftDeepModelInvKFBL_of_loopInv hV hLoopInv hiLt⟩
  refine ⟨⟨hInv.hLastBran, hInv'.hLastK⟩, ?_, hCostMono, ?_, ?_, ?_, ?_, ?_, hLastStretchFits,
    model'.chain.toTreeChain.chainTree_isForest hHolds' hSub', hOldSubG0, hNewSubG0, ?_, ?_, ?_,
    hDisjPref⟩
  · intro j _ hj
    obtain ⟨H⟩ := hInv.hHist j hj
    rw [hInv.hLvlM, hInv.hN0]
    exact levelHistory_sparseCoreOrdInput H
  · exact hGiEq ▸ chainInv_G_succ_E_subset hV hInv' hiLt
  · intro e he
    simpa [hℓEq] using hCoreLenFits i.val le_rfl hiLt e he
  · intro j hj1 hj2
    have hBj := hB' j (Nat.le_of_lt hj2)
    have hGm : (model'.chain.G j).m ≤ model'.chain.lvlM j := by
      rw [hInv'.hLvlM]; exact_mod_cast hBj.2.2.1
    have hGn : (model'.chain.G j).n ≤ model'.chain.N₀ := by
      rw [hInv'.hN0]; exact (Finset.card_le_card hBj.2.1).trans hInv'.hG0n
    have hW := hWordLvl j hj2
    refine ⟨hGm, hGn, hInv'.hLvlM ▸ hW.1, by rw [hInv'.hLvlM, hInv'.hN0]; exact hW.2,
      chainInv_levelOrd_isRotationOrder hInv' hj2, hBj.2.2.2.1,
      chainInv_G_succ_E_subset hV hInv' hj2, hCoreLenFits j (Nat.le_of_succ_le hj1) hj2⟩
  · exact hLastEq (model'.chain.G cfg.P.d) _ _ (fun e he => by
      change (if e ∈ (model'.chain.G cfg.P.d).E then _ else 0) = _
      exact ite_eq_left he)
  · exact (hB' cfg.P.d le_rfl).2.2.2.1
  · intro j _ hj
    have h1 : (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.E ⊆
        model.chain.toTreeChain.chainTree.E := by
      simpa [TreeChain.activeLSF, ChainState.toTreeChain, hj] using
        hActiveSub model.chain j (Nat.le_of_lt hj)
    have h2 : (cfg.T.lsfs (model'.chain.scState j) (model'.chain.bran j)).F.F.E ⊆
        model'.chain.toTreeChain.chainTree.E := by
      simpa [TreeChain.activeLSF, ChainState.toTreeChain, hj] using
        hActiveSub model'.chain j (Nat.le_of_lt hj)
    exact ⟨h1.trans hOldSubG0, h2.trans hNewSubG0⟩
  · have h1 : (model.chain.lastLSFs model.chain.lastBran).F.F.E ⊆
        model.chain.toTreeChain.chainTree.E := by
      simpa [TreeChain.activeLSF, ChainState.toTreeChain, lt_irrefl] using
        hActiveSub model.chain cfg.P.d le_rfl
    exact h1.trans hOldSubG0
  · have h2 : (model'.chain.lastLSFs model'.chain.lastBran).F.F.E ⊆
        model'.chain.toTreeChain.chainTree.E := by
      simpa [TreeChain.activeLSF, ChainState.toTreeChain, lt_irrefl] using
        hActiveSub model'.chain cfg.P.d le_rfl
    exact h2.trans hNewSubG0

end MinCostFlow.MinRatio
