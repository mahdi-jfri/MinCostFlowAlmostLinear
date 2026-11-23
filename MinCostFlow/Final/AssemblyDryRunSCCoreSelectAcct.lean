module

public import MinCostFlow.Final.WireTermSelectFits
public import MinCostFlow.MinRatio.WireSelectFwdCost
public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
public import MinCostFlow.MinRatio.SelectUpdateModel
public import MinCostFlow.MinRatio.SelectUpdatePostCoreP123a
import MinCostFlow.MinRatio.WireChainCoreAlgebra
import MinCostFlow.MinRatio.OrdSolverToolMono
import MinCostFlow.Chain.BundleRestartMach
import Mathlib.Tactic

/-!
# Runtime, tree-update, and last-level length-fit accounting for select-aware `Update`
(`AssemblyDryRunSCCoreSelectAcct`)

Proves the pure chain-level accounting and terminal length-fit helpers needed to discharge
`hLenFitLast` and the 8 aggregate accounting conjuncts of `hLinkFacts` in
`ordChainUpdateCoreSelBody_runs` (`MinRatio/WireUpdateSelect.lean`):

1. `dryCoreSel_hLenFitLast`: discharges `hLenFitLast` from `ShiftLoopChainInv` and
   `DryChainLenGridInv` via `dry_levelD_lenFits_of_shiftLoop` and `dryLastWstrDyadic_of_gridInv`.
2. `updateLoop_select_acct_aux`: single induction over `Chain.Ordered.updateLoop` proving
   the combined prefix+suffix tool-cost bound (`∑_{j < lim} Δ T.cost j + ∑_{j ∈ Ico firstReb d}
   T.cost (newCh.scState j) ≤ Δ totalRuntime`), the prefix forest-deletion bound
   (`∑_{j < lim} |oldF_j \ newF_j| ≤ Δ totalTreeUpdates`), and `init_lower` on rebuilt levels
   `j ∈ Ico firstReb d`.
3. `dryCoreSel_update_accounting`: proves all 8 aggregate accounting inequalities of `hLinkFacts`
   (`hUWordsSum` at `uWordsMul = 10, uWordsFix = cfg.P.d`, `hULenSum` at `2 * Δrt`, `hUSSum` at
   `2 * Δrt`, `hFDelSum`, `hCostSum`, `hSufNewM`, `hSufOldM`, `hBranchA0`) directly from
   `UpdateCoreLevelLink` and `UpdateCoreSelectOutAt` (`SmallBatchAt`).
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Post-update terminal length fit (`dryCoreSel_hLenFitLast`) -/

/-- Discharges `hLenFitLast` of `ordChainUpdateCoreSelBody_runs` for any post-update chain
meeting `ShiftLoopChainInv` and `DryChainLenGridInv`. -/
theorem dryCoreSel_hLenFitLast (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {ch' : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hShift' : Ordered.ShiftLoopChainInv (concreteCirculationCfgWithLast dryWitnessUsed J) ch')
    (hGrid' : DryChainLenGridInv J ch') :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let P := ipmQualityPrecision I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    ∀ (Bblk : SelectBlocksLoc) (firstReb : ℕ), firstReb ≤ cfg.P.d →
      ∀ e ∈ (ch'.G cfg.P.d).E, ∀ prevM : ℕ → ℕ,
        EdgeValuesAt prevM (Bblk.lenPtr (cfg.P.d - 1)) 4 L P (ch'.G cfg.P.d).E
          (ch'.toTreeChain.chainLen ch'.ℓ cfg.P.d) →
        Num.Fits 4 L (Num.intVal prevM (Bblk.lenPtr (cfg.P.d - 1) + e * L) 4 L *
          (2 : ℤ) ^ dryLastStretchP J) ∧
        ∃ q : ℤ, Num.Fits 4 L q ∧
          (q : ℝ) / (2 : ℝ) ^ (P + dryLastStretchP J) =
            ch'.toTreeChain.chainLen ch'.ℓ (cfg.P.d + 1) e := by
  intro I V k L P cfg Bblk firstReb _ e he prevM hEv
  have hDy : DryLastWstrDyadic J ch' := dryLastWstrDyadic_of_gridInv J hGrid'
  obtain ⟨⟨qp, hqpFit, hqpEq⟩, ⟨q, hqFit, hqEq⟩⟩ :=
    dry_levelD_lenFits_of_shiftLoop J hJn hJm hCap hShift' hGrid' hDy e he
  have hValEq : ((Num.intVal prevM (Bblk.lenPtr (cfg.P.d - 1) + e * L) 4 L : ℤ) : ℝ) /
      (2 : ℝ) ^ P = (qp : ℝ) / (2 : ℝ) ^ P := (hEv e he).2.trans hqpEq.symm
  have h2ne : ((2 : ℝ) ^ P) ≠ 0 := by positivity
  have hIntEq : Num.intVal prevM (Bblk.lenPtr (cfg.P.d - 1) + e * L) 4 L = qp := by
    have hR : ((Num.intVal prevM (Bblk.lenPtr (cfg.P.d - 1) + e * L) 4 L : ℤ) : ℝ) = (qp : ℝ) :=
      (div_left_inj' h2ne).mp hValEq
    exact_mod_cast hR
  rw [hIntEq]
  exact ⟨hqpFit, q, hqFit, hqEq⟩

/-! ## 2. Basic batch and `sparseCoreProgTool` helpers -/

private lemma applyBatch_V_subset : ∀ {U : List Update} {G : MGraph}, G.V ⊆ (G.applyBatch U).V
  | [], _ => Finset.Subset.refl _
  | u :: rest, G => by
    have h1 : G.V ⊆ (G.applyUpdate u).V := by
      cases u with
      | insert _ _ _ => exact Finset.Subset.refl _
      | delete _ => exact Finset.Subset.refl _
      | split _ v' _ _ => exact Finset.subset_insert v' G.V
    exact h1.trans (applyBatch_V_subset (U := rest) (G := G.applyUpdate u))

/-- Any valid batch preserving the vertex set `G.V` contains only edge updates (`insert`/`delete`). -/
theorem isEdgeUpdate_of_applyBatch_V_eq :
    ∀ {U : List Update} {G : MGraph},
      G.BatchIsValid U → (G.applyBatch U).V = G.V → ∀ u ∈ U, IsEdgeUpdate u
  | [], _, _, _, _, h => by cases h
  | u :: rest, G, hBV, hVeq, x, hx => by
    have hEdgeU : IsEdgeUpdate u := by
      cases u with
      | insert _ _ _ => trivial
      | delete _ => trivial
      | split v v' St Sh =>
        exfalso
        have hv'Not : v' ∉ G.V := hBV.1.2.1
        have hv'In1 : v' ∈ (G.applyUpdate (.split v v' St Sh)).V := Finset.mem_insert_self v' G.V
        have hv'InEnd : v' ∈ (G.applyBatch (.split v v' St Sh :: rest)).V :=
          applyBatch_V_subset (U := rest) (G := G.applyUpdate (.split v v' St Sh)) hv'In1
        rw [hVeq] at hv'InEnd
        exact hv'Not hv'InEnd
    have hV1 : (G.applyUpdate u).V = G.V := by
      cases u <;> simp [IsEdgeUpdate, MGraph.applyUpdate] at hEdgeU ⊢
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hEdgeU
    · exact isEdgeUpdate_of_applyBatch_V_eq hBV.2 (hVeq.trans hV1.symm) x hx'

/-- Every edge-only batch has `G.batchEnc U = U.length`. -/
theorem batchEnc_eq_length_of_isEdgeUpdate :
    ∀ {U : List Update} {G : MGraph}, (∀ u ∈ U, IsEdgeUpdate u) → G.batchEnc U = U.length
  | [], _, _ => rfl
  | u :: rest, G, hEdge => by
    have hu := hEdge u List.mem_cons_self
    have h1 : G.updateEnc u = 1 := by
      cases u <;> simp [IsEdgeUpdate, MGraph.updateEnc] at hu ⊢
    have hrest := batchEnc_eq_length_of_isEdgeUpdate (U := rest) (G := G.applyUpdate u)
      (fun x hx => hEdge x (List.mem_cons_of_mem _ hx))
    simp [MGraph.batchEnc, h1, hrest, Nat.add_comm]

/-- Applying any batch `U` reduces the edge count by at most `U.length`. -/
theorem graph_m_le_applyBatch_m_add_len :
    ∀ {U : List Update} {G : MGraph}, G.m ≤ (G.applyBatch U).m + U.length
  | [], _ => by simp [MGraph.applyBatch]
  | u :: rest, G => by
    have ih := graph_m_le_applyBatch_m_add_len (U := rest) (G := G.applyUpdate u)
    have h1 : G.m ≤ (G.applyUpdate u).m + 1 := by
      cases u with
      | insert e _ _ =>
        change G.E.card ≤ (insert e G.E).card + 1
        exact (Finset.card_le_card (Finset.subset_insert e G.E)).trans (Nat.le_succ _)
      | delete e =>
        change G.E.card ≤ (G.E.erase e).card + 1
        by_cases hm : e ∈ G.E
        · have := Finset.card_erase_add_one hm; omega
        · rw [Finset.erase_eq_of_notMem hm]; omega
      | split _ _ _ _ =>
        change G.E.card ≤ G.E.card + 1; omega
    simp only [MGraph.applyBatch, List.foldl_cons, List.length_cons] at ih ⊢
    omega

/-- On a nonempty state of `sparseCoreProgTool` with `0 < st.k`, the input batch length `U.length`
is at most the single-step growth of `T.cost`. -/
theorem progTool_updateOrd_len_le_cost_sub {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} (st : SparseCoreBundleState depth) (hne : st.isNonempty = true)
    (hk : 0 < st.k) (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    U.length ≤ T.cost (T.updateOrd st U ℓ g ord').1 - T.cost st := by
  intro T
  have hup := progTool_updateOrd_of_nonempty (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl)
    st hne U ℓ g ord'
  have hGrow := progTool_cost_growth_ge (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl)
    st hne U ℓ g ord' hk
  dsimp only at hGrow
  have hmc := stepBundleTree_machCost (fun _ => canonicalSparsify impl) (st.trees 0) U st.ord ord'
  have hlog : 1 ≤ bundleLogFactor (st.trees 0).m₀ (st.trees 0).n₀ := by
    unfold bundleLogFactor; exact Nat.one_le_pow 2 _ (Nat.succ_pos _)
  have hULe : U.length ≤
      (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees 0) U st.ord ord').state.machCost -
        (st.trees 0).machCost := by
    have h1 : U.length ≤
        U.length +
        ((stepBundleTree (fun _ => canonicalSparsify impl) (st.trees 0) U st.ord ord').state.activeComps.sum
          fun C => ((st.trees 0).activeBuckets C).sum fun b =>
            ((st.trees 0).dyn (C, b)).G.batchEnc
              ((stepBundleTree (fun _ => canonicalSparsify impl) (st.trees 0) U st.ord ord').U_B (C, b))) +
        (st.trees 0).S_cur.batchEnc
          ((stepBundleTree (fun _ => canonicalSparsify impl) (st.trees 0) U st.ord ord').U_S) +
        ((stepBundleTree (fun _ => canonicalSparsify impl) (st.trees 0) U st.ord ord').state.activeComps.sum
          fun C => ((st.trees 0).activeBuckets C).sum fun b =>
            spanBatchChargeWith (st.trees 0).spanConst (st.trees 0).spanParams depth
              (((st.trees 0).initBunG (C, b)).n + (st.trees 0).splitBound)
              ((st.trees 0).initBunG (C, b)) ((st.trees 0).dyn (C, b)).G
              ((stepBundleTree (fun _ => canonicalSparsify impl) (st.trees 0) U st.ord ord').U_B (C, b))) +
        lsfBatchSize (st.trees 0).cs U +
        (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees 0) U st.ord ord').newlyActive.sum
          fun C => (st.trees 0).lazyMachInitCost C := by omega
    have h2 := h1.trans (Nat.le_mul_of_pos_right _ hlog)
    omega
  have htr0 : (((T.updateOrd st U ℓ g ord').1).trees 0).machCost =
      (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees 0) U st.ord ord').state.machCost := by
    change ((((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1).trees 0).machCost = _
    rw [hup]
  rw [htr0] at hGrow
  dsimp only [T] at hGrow ⊢
  omega

private lemma applyBatch_V_empty_of_empty :
    ∀ {U : List Update} {G : MGraph}, G.V = ∅ → G.BatchIsValid U → (G.applyBatch U).V = ∅
  | [], _, hG, _ => hG
  | u :: rest, G, hG, hB => by
    have hV1 : (G.applyUpdate u).V = ∅ := by
      cases u with
      | insert _ _ _ => exact hG
      | delete _ => exact hG
      | split v _ _ _ =>
        have hv : v ∈ G.V := hB.1.1
        rw [hG] at hv; cases hv
    exact applyBatch_V_empty_of_empty (U := rest) (G := G.applyUpdate u) hV1 hB.2

/-- If `ch` meets `Ordered.ChainInv` for `sparseCoreProgTool` and `(ch.G 0).V.Nonempty`, then
`(ch.scState 0).isNonempty = true`. -/
theorem progTool_chainInv_scState0_isNonempty {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ}
    {impl : SparsifyImpl} {L : LastLevelTool} {TP : SparseCoreParams} {LP : LastLevelParams}
    {P : ChainParams} {N₀ : ℕ}
    {ch : ChainState (sparseCoreProgTool lsfInit C_lsst depth impl) P}
    (hInv : Ordered.ChainInv (sparseCoreProgTool lsfInit C_lsst depth impl) L TP LP P N₀ ch)
    (hdPos : 0 < P.d) (hV0 : (ch.G 0).V.Nonempty) :
    (ch.scState 0).isNonempty = true := by
  obtain ⟨H⟩ := hInv.hHist 0 hdPos
  have hNM := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst depth
    (fun _ => canonicalSparsify impl) (canonicalSparsifyParams impl) (dsAmortConst impl)
    P.k (levelM TP P 0) N₀ H.D H.ord H.restarts H.len).2.2
  have hne := (runOrdAfterRestarts_isNonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    P.k (levelM TP P 0) N₀ H.D H.ord H.restarts H.len).2.1
  have hG0ne : (H.D.G 0).V.Nonempty := by
    by_contra hE
    have hVSub : ∀ t ≤ H.len, (H.D.G t).V = ∅ := by
      intro t ht
      induction t with
      | zero => exact Finset.not_nonempty_iff_eq_empty.mp hE
      | succ k ih =>
        have hkV : (H.D.G k).V = ∅ := ih (Nat.le_of_succ_le ht)
        have hStep := H.hD (k + 1) (Nat.succ_pos k) ht
        rw [hStep.2]
        exact applyBatch_V_empty_of_empty hkV hStep.1
    have hEndEmpty := hVSub H.len le_rfl
    rw [H.hEndG] at hEndEmpty
    exact (Finset.not_nonempty_iff_eq_empty.mpr hEndEmpty) hV0
  rw [H.hRun, hNM.isNonempty, hne, decide_eq_true hG0ne]

/-! ## 3. Core `updateLoop` runtime, tree-update, and rebuild-cost induction -/

private lemma updateLoop_select_acct_aux
    (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ)
    (hCostMono : ∀ s U ℓ g ord', T.cost s ≤ T.cost (T.updateOrd s U ℓ g ord').1)
    (hInitLower : ∀ M N (G' : MGraph) ℓ g ord, G'.IsValid →
      3 * G'.m * bundleLogFactor M N ≤ T.cost (T.initOrd P.k M N G' ℓ g ord))
    (stOrig : ChainState T P) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ),
      idx + rem = P.d →
      st.rebuildCount = stOrig.rebuildCount →
      (∀ j ≤ P.d, ((Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1.G j).IsValid) →
      let stEnd := (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1
      (∀ j < idx, stEnd.scState j = st.scState j ∧ stEnd.bran j = st.bran j) ∧
      ∃ r ≤ P.d + 1,
        idx ≤ r ∧
        (r < P.d → firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount = some r) ∧
        (P.d ≤ r → firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount = none) ∧
        st.totalTreeUpdates ≤ stEnd.totalTreeUpdates ∧
        (Finset.Ico idx (min r P.d)).sum (fun j =>
          ((T.lsfs (st.scState j) (st.bran j)).F.F.E \
            (T.lsfs (stEnd.scState j) (stEnd.bran j)).F.F.E).card) ≤
          stEnd.totalTreeUpdates - st.totalTreeUpdates ∧
        st.totalRuntime ≤ stEnd.totalRuntime ∧
        (Finset.Ico idx (min r P.d)).sum (fun j => T.cost (stEnd.scState j) - T.cost (st.scState j)) +
          (Finset.Ico r P.d).sum (fun j => T.cost (stEnd.scState j)) ≤
          stEnd.totalRuntime - st.totalRuntime ∧
        (r < P.d → ∀ j ∈ Finset.Ico r P.d, (stEnd.G j).m ≤ T.cost (stEnd.scState j)) := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU curEncAcc hsum hReb _
    have hidx : idx = P.d := by omega
    subst hidx
    dsimp only [Ordered.updateLoop]
    have hNoReb : firstRebuiltLevel P.d stOrig.rebuildCount st.rebuildCount = none := by
      rw [hReb]; exact firstRebuiltLevel_eq_of_eq _
    split_ifs with hEmpty
    · refine ⟨fun _ _ => ⟨rfl, rfl⟩, P.d + 1, le_rfl, Nat.le_succ _, fun h => by omega, fun _ => hNoReb,
        le_rfl, by simp, le_rfl, by simp, fun h => by omega⟩
    · refine ⟨fun _ _ => ⟨rfl, rfl⟩, P.d, Nat.le_succ _, le_rfl, fun h => by omega, fun _ => hNoReb,
        ?_, ?_, ?_, ?_, fun h => by omega⟩
      · unfold ChainState.totalTreeUpdates; dsimp only; omega
      · simp
      · unfold ChainState.totalRuntime; dsimp only; omega
      · simp
  | succ rem' ih =>
    intro idx st curG curU curEncAcc hsum hReb hValidEnd
    have hidxLt : idx < P.d := by omega
    by_cases hOver : intRebuildThreshold P N₀ idx < st.updCount idx + curU.length
    · set stLG : ChainState T P :=
        { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
      have hEndEq : (Ordered.updateLoop T L TP P N₀ ℓ' g' (rem' + 1) idx st curG curU curEncAcc).1 =
          (Ordered.algorithm1_rebuild T L P stLG idx (rebuildStartGraph idx curG) curEncAcc).1 := by
        conv_lhs => unfold Ordered.updateLoop
        rw [ite_eq_left hOver]
      set stEnd := (Ordered.algorithm1_rebuild T L P stLG idx (rebuildStartGraph idx curG) curEncAcc).1
      have hValidEnd' : ∀ j ≤ P.d, (stEnd.G j).IsValid := by rwa [hEndEq] at hValidEnd
      set G0 := fun m => if m = idx then rebuildStartGraph idx curG else stLG.G m
      have hBase := ordRebuildSuffix_prefix_and_coreAt T L P stLG.lvlM stLG.N₀ stLG.ℓ stLG.g
        (P.d - idx) idx (by omega) G0 stLG.scState stLG.bran stLG.updCount stLG.curEnc
        stLG.curDecUpdates stLG.curFwd
      have hPreEq : ∀ j < idx, stEnd.scState j = st.scState j ∧ stEnd.bran j = st.bran j := fun j hj => by
        have h := hBase.2.1 j hj
        refine ⟨?_, ?_⟩
        · simpa [stEnd, Ordered.algorithm1_rebuild, hidxLt, G0, stLG] using h.1
        · simpa [stEnd, Ordered.algorithm1_rebuild, hidxLt, G0, stLG] using h.2.1
      have hFirst : firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount = some idx := by
        rw [← hReb]
        simp only [stEnd, Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
        simpa [stLG] using Chain.firstRebuiltLevel_eq_of_inc hidxLt stLG.rebuildCount
      have hRtLe : st.totalRuntime ≤ stEnd.totalRuntime :=
        algorithm1_rebuild_totalRuntime_le T L P stLG hidxLt (rebuildStartGraph idx curG) curEncAcc
      have hRtSub := rebuild_totalRuntime_sub T L P stLG hidxLt (rebuildStartGraph idx curG) curEncAcc
      have hTuLe : st.totalTreeUpdates ≤ stEnd.totalTreeUpdates := by
        have h := ordUpdateLoop_treeUpdates_bound T L TP P N₀ ℓ' g' (rem' + 1) idx st curG curU curEncAcc (by omega)
        rw [hEndEq] at h
        exact h.1
      have hInitEach : ∀ j ∈ Finset.Ico idx P.d, (stEnd.G j).m ≤ T.cost (stEnd.scState j) := by
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
        have hCore := hBase.2.2 j hj1 (by omega)
        have hScEq : ∃ ℓj gj ordj,
            stEnd.scState j = T.initOrd P.k (stLG.lvlM j) stLG.N₀ (stEnd.G j) ℓj gj ordj :=
          ⟨_, _, _, by simpa [stEnd, Ordered.algorithm1_rebuild, hidxLt, G0] using hCore.1⟩
        obtain ⟨ℓj, gj, ordj, hScEq⟩ := hScEq
        rw [hScEq]
        have hLog : 1 ≤ bundleLogFactor (stLG.lvlM j) stLG.N₀ := by
          unfold bundleLogFactor; exact Nat.one_le_pow 2 _ (Nat.succ_pos _)
        have hLow := hInitLower (stLG.lvlM j) stLG.N₀ (stEnd.G j) ℓj gj ordj (hValidEnd' j hj2.le)
        nlinarith
      refine ⟨by simpa [hEndEq] using hPreEq, idx, by omega, le_rfl,
        fun _ => by rwa [hEndEq], fun h => by omega,
        by rwa [hEndEq], ?_, by rwa [hEndEq], ?_, fun _ => by rwa [hEndEq]⟩
      · rw [Nat.min_eq_left hidxLt.le, Finset.Ico_self, Finset.sum_empty]; exact Nat.zero_le _
      · rw [hEndEq, Nat.min_eq_left hidxLt.le, Finset.Ico_self, Finset.sum_empty, Nat.zero_add]
        change (Finset.Ico idx P.d).sum (fun j => T.cost (stEnd.scState j)) ≤
          stEnd.totalRuntime - stLG.totalRuntime
        dsimp only [stEnd] at hRtSub ⊢
        rw [hRtSub]; omega
    · set Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
      set res := T.updateOrd (st.scState idx) curU (Cpartial.chainLen ℓ' idx)
        (Cpartial.chainGrad g' idx)
        (Ordered.chainLevelOrd T (fun j => if j = idx then curG else st.G j) st.scState st.bran idx)
      set fiChanges := diffTreeChanges (T.lsfs (st.scState idx) (st.bran idx)).F.F.E
        (T.lsfs res.1 (st.bran idx)).F.F.E
      set nextU := res.2 (st.bran idx)
      set nextEnc := (st.G (idx + 1)).batchEnc nextU
      set stNext : ChainState T P :=
        { st with
          G := fun j => if j = idx then curG else st.G j
          scState := fun j => if j = idx then res.1 else st.scState j
          updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
          recUpdates := fun j =>
            if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
          curFwd := fun j =>
            if j = idx then st.curFwd idx + nextU.length else st.curFwd j
          curEnc := fun j =>
            if j = idx then st.curEnc idx + curEncAcc
            else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc
            else st.curEnc j
          curDecUpdates := fun j =>
            if j = idx then st.curDecUpdates idx + fiChanges.length else st.curDecUpdates j }
      have hLoopEq : (Ordered.updateLoop T L TP P N₀ ℓ' g' (rem' + 1) idx st curG curU curEncAcc).1 =
          (Ordered.updateLoop T L TP P N₀ ℓ' g' rem' (idx + 1) stNext
            (T.S res.1 (st.bran idx)) nextU 0).1 := by
        conv_lhs => unfold Ordered.updateLoop
        rw [ite_eq_right hOver]
      have hRtStep : stNext.totalRuntime =
          st.totalRuntime + (T.cost res.1 - T.cost (st.scState idx)) + curEncAcc +
            (if idx + 1 < P.d then nextEnc else 0) :=
        updateLoop_step_totalRuntime_eq st hidxLt curG res.1 curU nextU curEncAcc nextEnc
          fiChanges.length (hCostMono _ _ _ _ _)
      have hTuStep : stNext.totalTreeUpdates = st.totalTreeUpdates + fiChanges.length := by
        unfold ChainState.totalTreeUpdates
        have hmemIdx : idx ∈ Finset.range P.d := Finset.mem_range.mpr hidxLt
        have hSum : (Finset.range P.d).sum stNext.curDecUpdates =
            (Finset.range P.d).sum st.curDecUpdates + fiChanges.length := by
          rw [← Finset.add_sum_erase _ _ hmemIdx, ← Finset.add_sum_erase _ st.curDecUpdates hmemIdx]
          have hRest : ((Finset.range P.d).erase idx).sum stNext.curDecUpdates =
              ((Finset.range P.d).erase idx).sum st.curDecUpdates :=
            Finset.sum_congr rfl fun j hj => by
              simp [stNext, (Finset.mem_erase.mp hj).1]
          have hIdxEq : stNext.curDecUpdates idx = st.curDecUpdates idx + fiChanges.length := by
            simp [stNext]
          rw [hRest, hIdxEq]; ring
        change st.closedTreeUpdates + (Finset.range P.d).sum stNext.curDecUpdates + st.curLastTreeUpdates =
          st.closedTreeUpdates + (Finset.range P.d).sum st.curDecUpdates + st.curLastTreeUpdates + fiChanges.length
        omega
      obtain ⟨hPreRec, r, hrLe, hidx1Le, hRebLt, hRebGe, hTuRecLe, hTuRecSum, hRtRecLe, hRtRecSum,
          hInitRec⟩ :=
        ih (idx + 1) stNext (T.S res.1 (st.bran idx)) nextU 0 (by omega) hReb (by rwa [← hLoopEq])
      set stEnd := (Ordered.updateLoop T L TP P N₀ ℓ' g' rem' (idx + 1) stNext
        (T.S res.1 (st.bran idx)) nextU 0).1
      have hIdxLtMin : idx < min r P.d := by omega
      have hIcoSplit : Finset.Ico idx (min r P.d) = insert idx (Finset.Ico (idx + 1) (min r P.d)) := by
        ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hNotMem : idx ∉ Finset.Ico (idx + 1) (min r P.d) := by simp
      have hEndIdx : stEnd.scState idx = res.1 ∧ stEnd.bran idx = st.bran idx := by
        have h := hPreRec idx (Nat.lt_succ_self idx)
        simpa [stNext] using h
      have hCardLeFi : ((T.lsfs (st.scState idx) (st.bran idx)).F.F.E \
          (T.lsfs (stEnd.scState idx) (stEnd.bran idx)).F.F.E).card ≤ fiChanges.length := by
        rw [hEndIdx.1, hEndIdx.2]
        have hlen := diffTreeChanges_length_eq (T.lsfs (st.scState idx) (st.bran idx)).F.F.E
          (T.lsfs res.1 (st.bran idx)).F.F.E
        change _ ≤ (diffTreeChanges _ _).length
        omega
      have hTuTailEq :
          (Finset.Ico (idx + 1) (min r P.d)).sum (fun j =>
            ((T.lsfs (st.scState j) (st.bran j)).F.F.E \
              (T.lsfs (stEnd.scState j) (stEnd.bran j)).F.F.E).card) =
          (Finset.Ico (idx + 1) (min r P.d)).sum (fun j =>
            ((T.lsfs (stNext.scState j) (stNext.bran j)).F.F.E \
              (T.lsfs (stEnd.scState j) (stEnd.bran j)).F.F.E).card) :=
        Finset.sum_congr rfl fun j hj => by
          have hne : j ≠ idx := by have := (Finset.mem_Ico.mp hj).1; omega
          simp [stNext, hne]
      have hRtTailEq :
          (Finset.Ico (idx + 1) (min r P.d)).sum (fun j => T.cost (stEnd.scState j) - T.cost (st.scState j)) =
          (Finset.Ico (idx + 1) (min r P.d)).sum (fun j => T.cost (stEnd.scState j) - T.cost (stNext.scState j)) :=
        Finset.sum_congr rfl fun j hj => by
          have hne : j ≠ idx := by have := (Finset.mem_Ico.mp hj).1; omega
          simp [stNext, hne]
      refine ⟨fun j hj => ?_, r, hrLe, by omega,
        fun h => by rw [hLoopEq]; exact hRebLt h,
        fun h => by rw [hLoopEq]; exact hRebGe h,
        by rw [hLoopEq]; omega, ?_, by rw [hLoopEq]; omega, ?_,
        fun h => by rw [hLoopEq]; exact hInitRec h⟩
      · rw [hLoopEq]
        have h := hPreRec j (by omega)
        have hne : j ≠ idx := by omega
        simpa [stNext, hne] using h
      · rw [hLoopEq, hIcoSplit, Finset.sum_insert hNotMem, hTuTailEq]
        omega
      · rw [hLoopEq, hIcoSplit, Finset.sum_insert hNotMem, hRtTailEq, hEndIdx.1]
        omega

/-! ## 4. Full 8-clause aggregate accounting for `hLinkFacts` -/

/-- Proves all 8 aggregate runtime, tree-update, and batch-size inequalities required by `hLinkFacts`
in `ordChainUpdateCoreSelBody_runs` (`WireUpdateSelect.lean`) at `uWordsMul = 10` and
`uWordsFix = cfg.P.d`. -/
theorem dryCoreSel_update_accounting
    {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}
    {cfg : Alg2Config} {w P L capExp vCap eCap heap midHeap firstReb : ℕ}
    {foot : ℕ → Prop} {memCore : ℕ → ℕ}
    {model : Alg2State cfg} {U : List Update} {gVec lVec : ℕ → ℝ}
    {levelU levelUS : ℕ → List Update} {diffLists : ℕ → LevelDiffLists}
    (hT : cfg.T = sparseCoreProgTool lsfInit C_lsst depth impl)
    (hV : cfg.ValidOrdNoHidden)
    (hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh)
    (hRef : RefreshBatch model.extG U)
    (hV0 : (model.chain.G 0).V.Nonempty)
    (hShift0 : ShiftLoopChainInv cfg model.chain)
    (hShift1 : ShiftLoopChainInv cfg (alg2PreResetState cfg model U gVec lVec).chain)
    (hLink : UpdateCoreLevelLink model.chain (alg2PreResetState cfg model U gVec lVec).chain
      firstReb levelU levelUS)
    (hOut : UpdateCoreSelectOutAt w P L capExp vCap eCap (hT ▸ progReemb lsfInit C_lsst depth impl)
      foot memCore heap midHeap firstReb model.chain
      (alg2PreResetState cfg model U gVec lVec).chain levelU levelUS diffLists) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let lim := min firstReb cfg.P.d
    let Δrt := modelPre.chain.totalRuntime - model.chain.totalRuntime
    let Δtu := modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates
    ((Finset.range lim).sum (fun j => memCore (heap + 1 + 12 * j + 11)) ≤ 10 * Δrt + cfg.P.d) ∧
    ((Finset.range lim).sum (fun j => (levelU j).length) ≤ 2 * Δrt) ∧
    ((Finset.range lim).sum (fun j => (diffLists j).uS.length) ≤ 2 * Δrt) ∧
    ((Finset.range lim).sum (fun j => (diffLists j).fDel.length) ≤ Δtu) ∧
    ((Finset.range lim).sum
        (fun j => cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j)) +
      (Finset.Ico firstReb cfg.P.d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) ≤ Δrt) ∧
    (firstReb < cfg.P.d →
      (Finset.Ico firstReb cfg.P.d).sum (fun j => (modelPre.chain.G j).m) ≤ Δrt ∧
      (modelPre.chain.G cfg.P.d).m ≤ Δrt) ∧
    (firstReb < cfg.P.d → (model.chain.G firstReb).m ≤ 2 * Δrt) ∧
    (firstReb = 0 → (modelPre.chain.G 0).m ≤ Δrt) := by
  rcases cfg with ⟨T, Ltool, TP, LP, Pch, σ_mwu, N₀, α, Ψ, ε⟩
  dsimp only at hT hV hFresh hRef hV0 hShift0 hShift1 hLink hOut ⊢
  subst hT
  let cfg : Alg2Config := ⟨sparseCoreProgTool lsfInit C_lsst depth impl, Ltool, TP, LP, Pch, σ_mwu, N₀, α, Ψ, ε⟩
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let modelPre := alg2PreResetState cfg model U gVec lVec
  let lim := min firstReb Pch.d
  let Δrt := modelPre.chain.totalRuntime - model.chain.totalRuntime
  let Δtu := modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates
  have hB1 := Ordered.level_bounds_aux_noHidden cfg.T Ltool TP LP Pch N₀
    hV.hTP hV.hγM₀ hV.hγk hShift1.1
  -- 1. Extract the unconditional `updateLoop` runtime/tree/init bounds
  set st0 : ChainState cfg.T Pch :=
    { model.chain with
      recUpdates := fun j =>
        if j = 0 then model.chain.recUpdates 0 + tr.2.2.2.2.length else model.chain.recUpdates j }
  have hAcct := updateLoop_select_acct_aux cfg.T Ltool TP Pch N₀
    (fun e' => lVec (tr.2.2.1 e')) (fun e' => gVec (tr.2.2.1 e'))
    (fun s U' ℓ' g' ord' => progTool_updateOrd_cost_mono s U' ℓ' g' ord')
    (fun M N G' ℓ' g' ord' hGv =>
      sparseCoreBundleRestartToolMachWith_init_lower _ _ _ _ _ _ Pch.hk hGv)
    model.chain Pch.d 0 st0 ((model.chain.G 0).applyBatch tr.2.2.2.2) tr.2.2.2.2
    ((model.chain.G 0).batchEnc tr.2.2.2.2) (Nat.zero_add Pch.d) rfl
    (fun j hj => (hB1 j hj).1)
  obtain ⟨_, r, hrLe, _, hrLt, hrGe, _, hTuSumR, _, hRtSumR, hInitR⟩ := hAcct
  have hMinEq : min r Pch.d = lim := by
    by_cases hfr : firstReb < Pch.d
    · have h1 := hLink.2.1 hfr
      have hrlt : r < Pch.d := by
        by_contra hge
        have h2 := hrGe (by omega)
        change firstRebuiltLevel Pch.d model.chain.rebuildCount modelPre.chain.rebuildCount = none at h2
        rw [h1] at h2; cases h2
      have h2 := hrLt hrlt
      change firstRebuiltLevel Pch.d model.chain.rebuildCount modelPre.chain.rebuildCount = some r at h2
      rw [h1] at h2
      have hEq : firstReb = r := Option.some.inj h2
      dsimp only [lim]; omega
    · have hfrGe : Pch.d ≤ firstReb := by omega
      have h1 := hLink.2.2.1 hfrGe
      have hrge : Pch.d ≤ r := by
        by_contra hlt
        have h2 := hrLt (by omega)
        change firstRebuiltLevel Pch.d model.chain.rebuildCount modelPre.chain.rebuildCount = some r at h2
        rw [h1] at h2; cases h2
      dsimp only [lim]; omega
  have hIcoEq : Finset.Ico r Pch.d = Finset.Ico firstReb Pch.d := by
    ext j; simp only [Finset.mem_Ico]
    by_cases hfr : firstReb < Pch.d
    · have : r = firstReb := by omega
      rw [this]
    · have : Pch.d ≤ r := by omega
      omega
  have hIco0 : Finset.Ico 0 lim = Finset.range lim := by ext j; simp
  have hCostSum :
      (Finset.range lim).sum
          (fun j => cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j)) +
        (Finset.Ico firstReb Pch.d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) ≤ Δrt := by
    rw [hMinEq, hIco0, hIcoEq] at hRtSumR
    exact hRtSumR
  have hFDelSum : (Finset.range lim).sum (fun j => (diffLists j).fDel.length) ≤ Δtu := by
    rw [hMinEq, hIco0] at hTuSumR
    have hEq : (Finset.range lim).sum (fun j => (diffLists j).fDel.length) =
        (Finset.range lim).sum (fun j =>
          ((cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.E \
            (cfg.T.lsfs (modelPre.chain.scState j) (modelPre.chain.bran j)).F.F.E).card) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjLt : j < lim := Finset.mem_range.mp hj
      have hS := hOut.2.2 j hjLt
      rw [← List.toFinset_card_of_nodup hS.2.2.1, hS.2.2.2.1]
    rw [hEq]
    exact hTuSumR
  -- 2. Per-level forwarded batch and input batch bounds
  have hFwdEnc : ∀ j < lim,
      (model.chain.G (j + 1)).batchEnc (levelUS j) ≤
        cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j) := by
    intro j hj
    have hjd : j < Pch.d := lt_of_lt_of_le hj (Nat.min_le_right _ _)
    obtain ⟨_, ℓj, gj, ordj, hsc', hUS⟩ := hLink.2.2.2.2.1 j hj
    have hbr := (progTool_chainInv_bran_lt_k hShift0.1 hjd).2
    rw [hShift0.1.hGSucc j hjd, hUS, hsc']
    exact progTool_updateOrd_batchEnc_le_cost_sub (model.chain.scState j) (levelU j) ℓj gj ordj hbr
  have hFwdLen : ∀ j < lim,
      (levelUS j).length ≤
        cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j) := fun j hj =>
    (MinCostFlow.DynSpanner.length_le_batchEnc _ _).trans (hFwdEnc j hj)
  have hUSSum : (Finset.range lim).sum (fun j => (diffLists j).uS.length) ≤ 2 * Δrt := by
    have h1 : (Finset.range lim).sum (fun j => (diffLists j).uS.length) ≤
        (Finset.range lim).sum (fun j => (levelUS j).length) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjLt : j < lim := Finset.mem_range.mp hj
      rw [(hOut.2.2 j hjLt).2.2.2.2.1, coreBatchTouchedEdges_eq_batchTouchedEdges]
      exact batchTouchedEdges_length_le (levelUS j)
    have h2 : (Finset.range lim).sum (fun j => (levelUS j).length) ≤
        (Finset.range lim).sum
          (fun j => cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j)) :=
      Finset.sum_le_sum fun j hj => hFwdLen j (Finset.mem_range.mp hj)
    omega
  have hBatchEncSum :
      (Finset.range lim).sum (fun j => (model.chain.G j).batchEnc (levelU j)) ≤ 2 * Δrt := by
    by_cases hlim0 : lim = 0
    · simp [hlim0]
    · have hlimPos : 0 < lim := Nat.pos_of_ne_zero hlim0
      have hfrPos : 0 < firstReb := by omega
      have hdPos : 0 < Pch.d := by omega
      -- Level `0`: `levelU 0` is edge-only, so `batchEnc = length ≤ Δ T.cost 0`
      have hNR := hLink.2.2.2.1 hfrPos
      obtain ⟨hG0Eq, hB0⟩ := hNR.2.2.1 0 (Nat.zero_le _)
      have hEdgeInt : ∀ u ∈ tr.2.2.2.2, IsEdgeUpdate u :=
        translateBatch_isEdgeUpdate model.extG model.extToInt model.intToExt model.nextFresh U
          (fun u hu => by
            have hns := hRef.2.2 u hu
            cases u with
            | insert _ _ _ => trivial
            | delete _ => trivial
            | split _ _ _ _ => exact absurd hns id)
      have hV0Pre : (modelPre.chain.G 0).V = (model.chain.G 0).V := by
        rcases algorithm1_update_G0_and_g cfg.T Ltool TP Pch N₀ model.chain tr.2.2.2.2
            (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e')) with
          ⟨h0, _, _⟩ | ⟨_, hG0', _⟩
        · exfalso
          have h0' : firstRebuiltLevel Pch.d model.chain.rebuildCount modelPre.chain.rebuildCount =
              some 0 := h0
          by_cases hfrD : firstReb < Pch.d
          · have h1 : firstRebuiltLevel Pch.d model.chain.rebuildCount modelPre.chain.rebuildCount =
                some firstReb := hLink.2.1 hfrD
            rw [h1] at h0'; exact absurd (Option.some.inj h0') (by omega)
          · have hfrGe : Pch.d ≤ firstReb := by omega
            have h1 : firstRebuiltLevel Pch.d model.chain.rebuildCount modelPre.chain.rebuildCount =
                none := hLink.2.2.1 hfrGe
            rw [h1] at h0'; cases h0'
        · have hG0'' : modelPre.chain.G 0 = (model.chain.G 0).applyBatch tr.2.2.2.2 := hG0'
          rw [hG0'']
          clear hG0' hG0''
          have hAux : ∀ {U' : List Update} {G' : MGraph}, (∀ u ∈ U', IsEdgeUpdate u) →
              (G'.applyBatch U').V = G'.V := by
            intro U'
            induction U' with
            | nil => intro _ _; rfl
            | cons u rest ihU =>
              intro G' hE
              have h1 : (G'.applyUpdate u).V = G'.V := by
                have hu := hE u List.mem_cons_self
                cases u <;> simp [IsEdgeUpdate, MGraph.applyUpdate] at hu ⊢
              exact (ihU fun x hx => hE x (List.mem_cons_of_mem _ hx)).trans h1
          exact hAux hEdgeInt
      have hEdgeLvl0 : ∀ u ∈ levelU 0, IsEdgeUpdate u :=
        isEdgeUpdate_of_applyBatch_V_eq hB0 ((congrArg MGraph.V hG0Eq.symm).trans hV0Pre)
      have hEnc0 : (model.chain.G 0).batchEnc (levelU 0) ≤
          cfg.T.cost (modelPre.chain.scState 0) - cfg.T.cost (model.chain.scState 0) := by
        rw [batchEnc_eq_length_of_isEdgeUpdate hEdgeLvl0]
        obtain ⟨_, ℓ0, g0, ord0, hsc0, _⟩ := hLink.2.2.2.2.1 0 hlimPos
        have hne0 := progTool_chainInv_scState0_isNonempty hShift0.1 hdPos hV0
        have hk0 : 0 < (model.chain.scState 0).k := by
          rw [(progTool_chainInv_bran_lt_k hShift0.1 hdPos).1]; exact Pch.hk
        rw [hsc0]
        exact progTool_updateOrd_len_le_cost_sub (model.chain.scState 0) hne0 hk0
          (levelU 0) ℓ0 g0 ord0
      -- Split `range lim` into `0` and `1 .. lim - 1`
      have hSplit : (Finset.range lim).sum (fun j => (model.chain.G j).batchEnc (levelU j)) =
          (model.chain.G 0).batchEnc (levelU 0) +
          (Finset.range (lim - 1)).sum (fun j => (model.chain.G (j + 1)).batchEnc (levelU (j + 1))) := by
        have hlimEq : lim = (lim - 1) + 1 := by omega
        conv_lhs => rw [hlimEq, Finset.sum_range_succ']
        rw [Nat.add_comm]
      have hTail : (Finset.range (lim - 1)).sum
            (fun j => (model.chain.G (j + 1)).batchEnc (levelU (j + 1))) ≤
          (Finset.range lim).sum
            (fun j => cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j)) := by
        have h1 : (Finset.range (lim - 1)).sum
              (fun j => (model.chain.G (j + 1)).batchEnc (levelU (j + 1))) ≤
            (Finset.range (lim - 1)).sum
              (fun j => cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjLt : j < lim := by have := Finset.mem_range.mp hj; omega
          rw [(hLink.2.2.2.2.1 j hjLt).1]
          exact hFwdEnc j hjLt
        exact h1.trans (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le _ _)))
      have h0In : cfg.T.cost (modelPre.chain.scState 0) - cfg.T.cost (model.chain.scState 0) ≤
          (Finset.range lim).sum
            (fun j => cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j)) :=
        Finset.single_le_sum (f := fun j =>
            cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j))
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hlimPos)
      rw [hSplit]; omega
  have hULenSum : (Finset.range lim).sum (fun j => (levelU j).length) ≤ 2 * Δrt :=
    (Finset.sum_le_sum fun j _ => MinCostFlow.DynSpanner.length_le_batchEnc _ _).trans hBatchEncSum
  have hUWordsSum : (Finset.range lim).sum (fun j => memCore (heap + 1 + 12 * j + 11)) ≤
      10 * Δrt + Pch.d := by
    have hEach : ∀ j ∈ Finset.range lim,
        memCore (heap + 1 + 12 * j + 11) ≤ 5 * (model.chain.G j).batchEnc (levelU j) + 1 := fun j hj =>
      (hOut.2.2 j (Finset.mem_range.mp hj)).2.2.2.2.2.2.2.2.2.2.1.2
    have hSum := Finset.sum_le_sum hEach
    conv_rhs at hSum =>
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hlimLe : lim ≤ Pch.d := Nat.min_le_right _ _
    omega
  -- 3. Rebuilt-suffix edge bounds (`firstReb < Pch.d`)
  have hSufNewM : firstReb < Pch.d →
      (Finset.Ico firstReb Pch.d).sum (fun j => (modelPre.chain.G j).m) ≤ Δrt ∧
      (modelPre.chain.G Pch.d).m ≤ Δrt := by
    intro hfr
    have hrEq : r = firstReb := by omega
    have hSum : (Finset.Ico firstReb Pch.d).sum (fun j => (modelPre.chain.G j).m) ≤
        (Finset.Ico firstReb Pch.d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) :=
      Finset.sum_le_sum fun j hj => by
        rw [← hrEq] at hj
        exact hInitR (by omega) j hj
    have hSumLe : (Finset.Ico firstReb Pch.d).sum (fun j => (modelPre.chain.G j).m) ≤ Δrt := by
      omega
    have hLastLe : (modelPre.chain.G Pch.d).m ≤ (modelPre.chain.G (Pch.d - 1)).m := by
      have hSub := chainInv_G_succ_E_subset hV hShift1.1 (show Pch.d - 1 < Pch.d by omega)
      rw [Nat.sub_add_cancel (by omega)] at hSub
      exact Finset.card_le_card hSub
    have hMem : Pch.d - 1 ∈ Finset.Ico firstReb Pch.d := Finset.mem_Ico.mpr (by omega)
    have hSingle : (modelPre.chain.G (Pch.d - 1)).m ≤
        (Finset.Ico firstReb Pch.d).sum (fun j => (modelPre.chain.G j).m) :=
      Finset.single_le_sum (f := fun j => (modelPre.chain.G j).m) (fun _ _ => Nat.zero_le _) hMem
    exact ⟨hSumLe, hLastLe.trans (hSingle.trans hSumLe)⟩
  have hBranchA0 : firstReb = 0 → (modelPre.chain.G 0).m ≤ Δrt := by
    intro h0
    have hdPos : 0 < Pch.d := Pch.hd
    have hSum := (hSufNewM (by omega)).1
    have hMem : 0 ∈ Finset.Ico firstReb Pch.d := Finset.mem_Ico.mpr (by omega)
    exact (Finset.single_le_sum (f := fun j => (modelPre.chain.G j).m)
      (fun _ _ => Nat.zero_le _) hMem).trans hSum
  have hSufOldM : firstReb < Pch.d → (model.chain.G firstReb).m ≤ 2 * Δrt := by
    intro hfr
    by_cases h0 : firstReb = 0
    · subst h0
      have hTr := translateBatch_preserves U model.extG (model.chain.G 0)
        model.extToInt model.intToExt model.nextFresh hFresh hRef.1
      dsimp only at hTr
      have hExtEq : tr.1 = model.extG := hTr.1.trans hRef.2.1
      have hM0Eq : (model.chain.G 0).m = (modelPre.chain.G 0).m := by
        rcases algorithm1_update_G0_and_g cfg.T Ltool TP Pch N₀ model.chain tr.2.2.2.2
            (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e')) with
          ⟨_, hG0', _⟩ | ⟨_, hG0', _⟩
        · have hG0'' : modelPre.chain.G 0 = ((model.chain.G 0).applyBatch tr.2.2.2.2).compact := hG0'
          rw [hG0'']
          change (model.chain.G 0).m = ((model.chain.G 0).applyBatch tr.2.2.2.2).compact.E.card
          have hComp : ((model.chain.G 0).applyBatch tr.2.2.2.2).compact.E.card =
              ((model.chain.G 0).applyBatch tr.2.2.2.2).m := by
            simp [MGraph.compact, MGraph.m]
          rw [hComp, hTr.2.1.m_eq, hExtEq, ← hFresh.m_eq]
        · have hG0'' : modelPre.chain.G 0 = (model.chain.G 0).applyBatch tr.2.2.2.2 := hG0'
          rw [hG0'', hTr.2.1.m_eq, hExtEq, ← hFresh.m_eq]
      have h1 := hBranchA0 rfl
      omega
    · have hPos : 0 < firstReb := Nat.pos_of_ne_zero h0
      set prev := firstReb - 1
      have hPrevLim : prev < lim := by dsimp only [lim, prev]; omega
      have hPrevD : prev < Pch.d := by dsimp only [prev]; omega
      have hPrevSucc : prev + 1 = firstReb := Nat.sub_add_cancel hPos
      have hNR := hLink.2.2.2.1 hPos
      have hbrEq : modelPre.chain.bran prev = model.chain.bran prev :=
        (hNR.2.2.2.1 prev le_rfl hPrevD).1
      obtain ⟨_, ℓp, gp, ordp, hsc', hUS⟩ := hLink.2.2.2.2.1 prev hPrevLim
      have hNewG : modelPre.chain.G firstReb = (model.chain.G firstReb).applyBatch (levelUS prev) := by
        rw [← hPrevSucc, hShift1.1.hGSucc prev hPrevD, hShift0.1.hGSucc prev hPrevD,
          hbrEq, hsc', hUS]
        exact progTool_S_updateOrd (model.chain.scState prev) (levelU prev) ℓp gp ordp
          (model.chain.bran prev)
      have hMLoss : (model.chain.G firstReb).m ≤ (modelPre.chain.G firstReb).m + (levelUS prev).length := by
        rw [hNewG]; exact graph_m_le_applyBatch_m_add_len
      have hNewSingle : (modelPre.chain.G firstReb).m ≤ Δrt :=
        (Finset.single_le_sum (f := fun j => (modelPre.chain.G j).m) (fun _ _ => Nat.zero_le _)
          (Finset.mem_Ico.mpr ⟨le_rfl, hfr⟩)).trans (hSufNewM hfr).1
      have hFwdSingle : (levelUS prev).length ≤ Δrt := by
        have h1 : cfg.T.cost (modelPre.chain.scState prev) - cfg.T.cost (model.chain.scState prev) ≤
            (Finset.range lim).sum
              (fun j => cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j)) :=
          Finset.single_le_sum (f := fun j =>
              cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j))
            (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hPrevLim)
        have h2 := hFwdLen prev hPrevLim
        omega
      omega
  exact ⟨hUWordsSum, hULenSum, hUSSum, hFDelSum, hCostSum, hSufNewM, hSufOldM, hBranchA0⟩

end MinCostFlow.Final.DryRun

end
