module

public import MinCostFlow.LSF.Program.LSFModuleBase

/-!
# Complete Deterministic WordRAM Module for Dynamic LSF (`Lemma 5.4`, `LSFModule`)

Proves the relocatable execution theorems `lsfInit_runs_of_hasAt_for`, `lsfInit_runs_of_hasAt`,
and `lsfApplyBatch_runs_of_hasAt`, full `DSRep.Implements` for `lsfDataStructure`
(`lsfModule_implements`, `lsfModule_from_cited`, Lemma 5.4 page 17 of `arXiv:2309.16629v1`), and
non-vacuity witnesses `lsfInitPre_nonvacuous` and `lsfBatchPre_nonvacuous`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  MinCostFlow.Num

@[expose] public section

/-! ## Relocatable `Initialize` and `ApplyBatch` execution theorems -/

/-- Relocatable `Initialize` execution theorem for a fixed initial graph `G₀`, also witnessing
`s'.G₀ = G₀`. -/
theorem lsfInit_runs_of_hasAt_for {w h b c_AN : ℕ} {p Q_AN : Program} {K_AN : ℝ} {G₀ : MGraph}
    (hp : p.HasAt b (lsfModuleProcs Q_AN c_AN K_AN b h))
    (hQ : ∀ (G_a : Cited.WGraph), G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
      (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
      ∃ out cost,
        RunsTo (wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
          G_a.IsSpanningTree out ∧
          G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n ∧
          (cost : ℝ) ≤ K_AN * (G_a.m + 1) *
            (Cited.logLogFactor G_a.n + Cited.weightFactor G_a.n G_a.maxWeight))
    {args : List ℕ} {mem : ℕ → ℕ} (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ args, a < 2 ^ w) (hpre : lsfInitPreFor c_AN K_AN w h G₀ args mem)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + lsfInitSpace Q_AN K_AN c_AN h args mem < 2 ^ w) :
    ∃ body, p.procs[b + lsfIdxInit]? = some body ∧
      ∃ o st' c, Runs w p ω body (startState args mem pos) o st' c ∧
        ∃ s' x', s'.G₀ = G₀ ∧ (LSFRep h).rep (heapArg args) s' x' st'.mem ∧
          lsfInitPost K_AN h args mem s' st'.mem ∧
          (LSFRep h).Respects (fun _ => False) (heapArg args)
            (lsfInitSpace Q_AN K_AN c_AN h args mem) mem o.value (heapArg args) x' st'.mem ∧
          c + (LSFRep h).phi (heapArg args) x' st'.mem ≤ lsfInitCost Q_AN c_AN K_AN h args mem := by
  have hh1 : 1 ≤ h := by rcases hpre with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hh, _⟩; exact hh
  have hhw : 3 * h + 2 ≤ w := by rcases hpre with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hhw, _⟩; exact hhw
  have hw2h : 2 * h + 2 ≤ w := by omega
  have hw5 : 5 ≤ w := by omega
  have hw1 : 1 < 2 ^ w := lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (by omega : 1 ≤ w))
  have hw2 : 2 < 2 ^ w := lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (by omega : 2 ≤ w))
  have M := lsfModuleHasAt_of_hasAt hp
  -- Shared utility contracts
  have hCopy := lsfMemCopy_meetsContract hw1 M.hShared
  have hFill := lsfMemFill_meetsContract hw1 M.hShared
  have hEmit : MeetsContract w p (lsfBaseUtils b + idxUtilEmitDefaultC)
      (emitNatContract w (defaultC_ceil K_AN) h) := by
    rw [← defaultC_ceil_lsfKNat K_AN]
    exact lsfEmitDefaultC_meetsContract (K_AN := lsfKNat K_AN) M.hShared
  have hAdd := lsfAddTo_meetsContract (w := w) M.hShared
  have hSub := lsfSubFrom_meetsContract (w := w) M.hShared
  have hLog := lsfLog2_meetsContract hw2 M.hShared
  have hSort := lsfKeyedMergeSort_meetsContract hw1 M.hShared
  have hULess := unsignedLess_meetsContract (h := h) hw1 (lsfHasAt_unsignedLess M.hShared)
  have hDg := lsfHasAt_dg M.hShared
  have gA1 : ∀ (i : ℕ) (hi : i < 14), p.procs[lsfBaseA1 Q_AN b + i]? = some ((lsfProcsA1 Q_AN c_AN b h)[i]'(by rw [lsfProcsA1_length]; exact hi)) :=
    fun i hi => M.hA1.get (by rw [lsfProcsA1_length]; exact hi)
  have gA2 : ∀ (i : ℕ) (hi : i < 4), p.procs[lsfBaseA2 Q_AN b + i]? = some ((lsfProcsA2 Q_AN b h)[i]'(by rw [lsfProcsA2_length]; exact hi)) :=
    fun i hi => M.hA2.get (by rw [lsfProcsA2_length]; exact hi)
  have gB1 : ∀ (i : ℕ) (hi : i < 11), p.procs[lsfBaseB1 Q_AN b + i]? = some ((lsfProcsB1 Q_AN b)[i]'(by rw [lsfProcsB1_length]; exact hi)) :=
    fun i hi => M.hB1.get (by rw [lsfProcsB1_length]; exact hi)
  have gB2 : ∀ (i : ℕ) (hi : i < 12), p.procs[lsfBaseB2 Q_AN b + i]? = some ((lsfProcsB2 Q_AN b h)[i]'(by rw [lsfProcsB2_length]; exact hi)) :=
    fun i hi => M.hB2.get (by rw [lsfProcsB2_length]; exact hi)
  have gC1 : ∀ (i : ℕ) (hi : i < 15), p.procs[lsfBaseC1 Q_AN b + i]? = some ((lsfProcsC1 Q_AN b h)[i]'(by rw [lsfProcsC1_length]; exact hi)) :=
    fun i hi => M.hC1.get (by rw [lsfProcsC1_length]; exact hi)
  have gC2 : ∀ (i : ℕ) (hi : i < 14), p.procs[lsfBaseC2 Q_AN b + i]? = some ((lsfProcsC2 Q_AN b)[i]'(by rw [lsfProcsC2_length]; exact hi)) :=
    fun i hi => M.hC2.get (by rw [lsfProcsC2_length]; exact hi)
  have gD : ∀ (i : ℕ) (hi : i < 15), p.procs[lsfBaseD Q_AN b + i]? = some ((lsfProcsD Q_AN b h)[i]'(by rw [lsfProcsD_length]; exact hi)) :=
    fun i hi => M.hD.get (by rw [lsfProcsD_length]; exact hi)
  have gOne : ∀ (i : ℕ) (hi : i < 3), p.procs[lsfBaseOne Q_AN b + i]? = some ((lsfProcsOne h)[i]'(by rw [lsfProcsOne_length]; exact hi)) :=
    fun i hi => M.hOne.get (by rw [lsfProcsOne_length]; exact hi)
  -- Prep & Widths
  have hPar := initParams_meetsContract (gA1 0 (by decide)) hLog
  have hPrep : ∀ G₀, MeetsContract w p (lsfBaseA1 Q_AN b + 3) (prepStageContract w G₀) := fun G₀ =>
    prepStage_meetsContract (gA1 3 (by decide)) hPar
      (initScan_meetsContract (gA1 1 (by decide)))
      (fun _ _ _ _ _ _ => initCopyG_meetsContract (gA1 2 (by decide)) hDg)
  have hWid := widths_meetsContract (gA1 4 (by decide)) hLog
  -- Tree phase
  have hSW : MeetsContract w p (lsfBaseA1 Q_AN b + 6) (sumWeightsContract w h) :=
    sumWeights_meetsContract M.hShared (gA1 6 (by decide))
  have hMQ : MeetsContract w p (lsfBaseA1 Q_AN b + 7) (multQNatStepContract w h) :=
    multQNatStep_meetsContract M.hShared (gA1 5 (by decide)) (gA1 7 (by decide))
  have hEC : MeetsContract w p (lsfBaseA1 Q_AN b + 9) (emitEdgeCopiesContract w) :=
    emitEdgeCopies_meetsContract M.hShared (gA1 9 (by decide))
  have hLsim : MeetsContract w p (lsfBaseA1 Q_AN b + 13) (lsimContract w c_AN h) :=
    lsim_meetsContract (gA1 13 (by decide)) hLog
  have hT0 : MeetsContract w p (lsfBaseA2 Q_AN b + 1) (t0EdgesContract w) :=
    t0Edges_meetsContract (gA2 1 (by decide))
  have hTree : ∀ G₀ v ℓ₀ P_fp vList eList, MeetsContract w p (lsfBaseA2 Q_AN b + 3)
      (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList) := fun G₀ v ℓ₀ P_fp vList eList =>
    treePhase_meetsContract (gA2 3 (by decide))
      (treeCopies_meetsContract (gA1 12 (by decide))
        (initTreeQNat_meetsContract M.hShared hSW hMQ (gA1 8 (by decide)))
        hFill
        (initTreeCopies_meetsContract M.hShared hEC (gA1 10 (by decide)))
        (initMarkBridges_meetsContract (gA1 11 (by decide)) hFill))
      hLsim
      (treeLsst_meetsContract (gA2 2 (by decide))
        (lsstFrontier_meetsContract (gA2 0 (by decide)) M.hLsst hQ)
        hT0)
  -- Order phase
  have hRootSt := rootStage_meetsContract (gB1 2 (by decide))
    (rootTree_meetsContract (gB1 0 (by decide))) hCopy
    (upV_meetsContract (gB1 1 (by decide)))
  have hStoreW := storeWord_meetsContract (w := w) (gB1 3 (by decide))
  have hEndIdx := endpointIdx_meetsContract (w := w) (gB1 4 (by decide))
  have hLca := lca_meetsContract (w := w) (gB1 5 (by decide))
  have hScatter := congScatter_meetsContract (gB1 6 (by decide)) hLca hFill hCopy hAdd hSub
  have hSubtree := subtreeSum_meetsContract (gB1 7 (by decide)) hAdd
  have hRank := congRank_meetsContract (gB1 8 (by decide)) hSort
  have hCong := congOrder_meetsContract (gB1 9 (by decide)) hFill hScatter hSubtree hRank
  have hUpMin := upMin_meetsContract (w := w) (gB1 10 (by decide))
  have hTBF := tBlockFill_meetsContract (w := w) (gB2 1 (by decide))
  have hTTr := tTrack_meetsContract (w := w) (gB2 2 (by decide)) hDg
  have hTH := thProc_meetsContract (w := w) (gB2 9 (by decide))
    (thSize_meetsContract (gB2 4 (by decide)))
    (thHeavy_meetsContract (gB2 5 (by decide)))
    (thOff_meetsContract (gB2 6 (by decide)))
    (thPlace_meetsContract (gB2 7 (by decide)))
    (thDepth_meetsContract (gB2 8 (by decide)))
  have hOrd : ∀ G₀ T₀ vList eList, MeetsContract w p (lsfBaseB2 Q_AN b + 11)
      (orderPhaseContract w h G₀ T₀ vList eList
        (lsfBaseB1 Q_AN b + 2) (lsfBaseB1 Q_AN b + 3)
        (lsfBaseB2 Q_AN b + 0) (lsfBaseB2 Q_AN b + 3) (lsfBaseB2 Q_AN b + 10)) := fun G₀ T₀ vList eList =>
    orderPhase_meetsContract (gB2 11 (by decide))
      hRootSt hStoreW
      (orderStage_meetsContract (gB2 0 (by decide)) hEndIdx hCong hUpMin)
      (tStage_meetsContract (gB2 3 (by decide)) hCopy hTBF hTTr)
      (thStage_meetsContract (gB2 10 (by decide)) hTH hCopy)
  -- Wstr & Decomp phase
  have hUAcc := uAcc_meetsContract hh1 hw2h (gC1 0 (by decide))
  have hULoad := uLoadWord_meetsContract hw2h (gC1 1 (by decide))
  have hUMul := uMul_meetsContract hUAcc hw2h (gC1 2 (by decide))
  have hUExt := uExt_meetsContract hw2h (gC1 3 (by decide))
  have hIdFill := idFill_meetsContract (w := w) (gC1 4 (by decide))
  have hBlkExt := blkExtLoop_meetsContract hUExt (gC1 5 (by decide))
  have hWDep := wDepth_meetsContract hUAcc hh1 hw2h (gC1 6 (by decide))
  have hTDist := treeDist_meetsContract hUAcc hLca hh1 hw2h (gC1 7 (by decide))
  have hDuv := duv_meetsContract hTDist (gC1 8 (by decide))
  have hAccE := accEdge_meetsContract hUAcc hh1 hw2h (gC1 9 (by decide))
  have hAccL := accLevel_meetsContract hAccE (gC1 10 (by decide))
  have hLFlag := levelFlag_meetsContract (w := w) (gC1 11 (by decide))
  have hFrMp := frMp_meetsContract (w := w) (gC1 12 (by decide))
  have hFrOwn := frOwn_meetsContract (w := w) (gC1 13 (by decide))
  have hFrRt := frRt_meetsContract (w := w) (gC1 14 (by decide))
  have hThresh := thresh_meetsContract hLog hULoad hUMul hEmit hh1 hw2h (gC2 0 (by decide))
  have hWPrep := wstrPrep_meetsContract hIdFill hBlkExt hFill hWDep hDuv (gC2 1 (by decide))
  have hLStep := levelStep_meetsContract hLFlag hFrMp hFrOwn hFrRt hDuv hAccL (gC2 2 (by decide))
  have hLevs := levels_meetsContract hLStep (gC2 3 (by decide))
  have hWEdge := wstrEdge_meetsContract hULoad hUAcc hUMul hULess hUExt hh1 hw2h (gC2 4 (by decide))
  have hWOut := wstrOut_meetsContract hWEdge (gC2 5 (by decide))
  have hWstr := wstr_meetsContract hThresh hWPrep hLevs hBlkExt hWOut (gC2 6 (by decide))
  have hWstrSt := wstrStage_meetsContract (gC2 7 (by decide)) hWstr
  have hDecompWT := decompWT_meetsContract (w := w) (gC2 13 (by decide))
    (decompDeg_meetsContract (gC2 8 (by decide)))
    (decompGreedy_meetsContract (gC2 9 (by decide)))
    (decompLabel_meetsContract (gC2 10 (by decide)))
    (decompMark_meetsContract (gC2 11 (by decide)))
    (decompClosure_meetsContract (gC2 12 (by decide)))
  have hLB := wstrLB_meetsContract (gD 0 (by decide)) hLog
  have hFlagM := flagMerge_meetsContract (w := w) (gD 1 (by decide))
  have hUpCl := upClosure_meetsContract (w := w) (gD 3 (by decide))
    (upLevel_meetsContract (gD 2 (by decide)))
  have hRootsSt := rootsStage_meetsContract (gD 4 (by decide)) hUpCl hFrMp hFrOwn hFrRt
  have hDec : MeetsContract w p (lsfBaseD Q_AN b + 5)
      (decompPhaseContract w h (defaultC_ceil K_AN)
        (lsfBaseC2 Q_AN b + 13) (lsfBaseD Q_AN b + 0) (lsfBaseC2 Q_AN b + 7)
        (lsfBaseUtils b + idxUtilMemCopy) (lsfBaseD Q_AN b + 1) (lsfBaseD Q_AN b + 4)
        decompPhaseCost) :=
    decompPhase_meetsContract (gD 5 (by decide)) hDecompWT hLB hWstrSt hCopy hFlagM hRootsSt
  -- Forest phase & storeArgs & one-vertex
  have hFG := fGraph_meetsContract (w := w) (gD 6 (by decide)) hDg
  have hFA := fAncFill_meetsContract (w := w) (gD 7 (by decide))
  have hWB := wBlock_meetsContract (gD 11 (by decide))
    (wKeys_meetsContract (gD 8 (by decide)) hULoad)
    hSort
    (wScan_meetsContract (w := w) (gD 10 (by decide)) (wAddV_meetsContract (gD 9 (by decide))))
  have hF : MeetsContract w p (lsfBaseD Q_AN b + 12)
      (fPhaseContract w h (lsfBaseD Q_AN b + 6) (lsfBaseD Q_AN b + 7) (lsfBaseD Q_AN b + 11)) :=
    fPhase_meetsContract (gD 12 (by decide)) hFG hFA hWB
  have hS20 := storeArgs_meetsContract (w := w) (m := 20) (gD 13 (by decide))
  have hS24 := storeArgs_meetsContract (w := w) (m := 24) (gD 14 (by decide))
  have hOneB := initOneBlocks_meetsContract (w := w) (gOne 0 (by decide))
  have hOneW := initOneWstr_meetsContract (w := w) (h := h) (gOne 1 (by decide))
  have hS8 := storeArgs_meetsContract (w := w) (m := 8) (gOne 2 (by decide))
  exact ⟨_, M.hInit, lsfInit_runs_for hLog hPrep hWid hTree hOrd hLB hDec hF hOneB hOneW hS8 hS20 hS24
    pos ω hwords hpre hz hsp⟩

/-- Relocatable `Initialize` execution theorem for any host program containing `lsfModuleProcs`
at index `b`. -/
theorem lsfInit_runs_of_hasAt {w h b c_AN : ℕ} {p Q_AN : Program} {K_AN : ℝ}
    (hp : p.HasAt b (lsfModuleProcs Q_AN c_AN K_AN b h))
    (hQ : ∀ (G_a : Cited.WGraph), G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
      (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
      ∃ out cost,
        RunsTo (wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
          G_a.IsSpanningTree out ∧
          G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n ∧
          (cost : ℝ) ≤ K_AN * (G_a.m + 1) *
            (Cited.logLogFactor G_a.n + Cited.weightFactor G_a.n G_a.maxWeight))
    {args : List ℕ} {mem : ℕ → ℕ} (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ args, a < 2 ^ w) (hpre : lsfInitPre c_AN K_AN w h args mem)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + lsfInitSpace Q_AN K_AN c_AN h args mem < 2 ^ w) :
    ∃ body, p.procs[b + lsfIdxInit]? = some body ∧
      ∃ o st' c, Runs w p ω body (startState args mem pos) o st' c ∧
        ∃ s' x', (LSFRep h).rep (heapArg args) s' x' st'.mem ∧
          lsfInitPost K_AN h args mem s' st'.mem ∧
          (LSFRep h).Respects (fun _ => False) (heapArg args)
            (lsfInitSpace Q_AN K_AN c_AN h args mem) mem o.value (heapArg args) x' st'.mem ∧
          c + (LSFRep h).phi (heapArg args) x' st'.mem ≤ lsfInitCost Q_AN c_AN K_AN h args mem := by
  obtain ⟨G₀, hpre'⟩ := hpre
  obtain ⟨body, hbody, o, st', c, hr, s', x', -, hrep, hpost, hresp, hc⟩ :=
    lsfInit_runs_of_hasAt_for hp hQ pos ω hwords hpre' hz hsp
  exact ⟨body, hbody, o, st', c, hr, s', x', hrep, hpost, hresp, hc⟩

/-- Relocatable `ApplyBatch` (`op 0`) execution theorem for any host program containing
`lsfModuleProcs` at index `b`. -/
theorem lsfApplyBatch_runs_of_hasAt {w h b c_AN bState : ℕ} {p Q_AN : Program} {K_AN : ℝ}
    {S : LSFState} {x : LSFConcrete} {args : List ℕ} {mem : ℕ → ℕ}
    (hp : p.HasAt b (lsfModuleProcs Q_AN c_AN K_AN b h))
    (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ args, a < 2 ^ w)
    (hhead : args.head? = some bState)
    (hrep : (LSFRep h).rep bState S x mem)
    (hpre : lsfBatchPre w S args mem)
    (hfoot : ∀ a, (LSFRep h).foot bState x a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + 0 < 2 ^ w) :
    ∃ body, p.procs[b + lsfIdxBatch]? = some body ∧
      ∃ o st' c, Runs w p ω body (startState args mem pos) o st' c ∧
        ∃ s' x', (LSFRep h).rep bState s' x' st'.mem ∧
          lsfBatchPost S args mem s' st'.mem ∧
          (LSFRep h).Respects ((LSFRep h).foot bState x) (heapArg args) 0 mem o.value bState x' st'.mem ∧
          c + (LSFRep h).phi bState x' st'.mem ≤ lsfBatchCost args mem + (LSFRep h).phi bState x mem := by
  have M := lsfModuleHasAt_of_hasAt hp
  have hDg := lsfHasAt_dg M.hShared
  have hOps := dgReloc_hasAt_ops hDg
  have hEdge := dgReloc_hasAt_edge hDg
  have hSplit := dgReloc_hasAt_split hDg
  have hBatch := dgReloc_hasAt_batch hDg
  have gBat : ∀ (i : ℕ) (hi : i < 10), p.procs[lsfBaseBat Q_AN b + i]? = some ((lsfProcsBat Q_AN b)[i]'(by rw [lsfProcsBat_length]; exact hi)) :=
    fun i hi => M.hBat.get (by rw [lsfProcsBat_length]; exact hi)
  have hpIns := gBat 7 (by decide)
  have hpDel := gBat 8 (by decide)
  have hpSplit := gBat 9 (by decide)
  have hpAdd := gBat 2 (by decide)
  have hMinUp : ∀ S', MeetsContract w p (lsfBaseBat Q_AN b + 0)
      (minEdgeUpContract w S' x.vList x.tOrigList) := fun _ =>
    minEdgeUp_meetsContract (gBat 0 (by decide))
  have hDgDelF : ∀ H, MeetsContract w p (lsfBaseDg b + 7 + dgIdxDeleteEdge)
      (dgDeleteEdgeContract w x.vCap (fECap x.eCap x.n0) H) := fun _ =>
    dgDeleteEdge_meetsContract hEdge hOps
  have hDgInsG : ∀ G, MeetsContract w p (lsfBaseDg b + 7 + dgIdxInsertEdge)
      (dgInsertEdgeContract w x.vCap x.eCap G) := fun _ =>
    dgInsertEdge_meetsContract hEdge hOps
  have hDgDelG : ∀ G, MeetsContract w p (lsfBaseDg b + 7 + dgIdxDeleteEdge)
      (dgDeleteEdgeContract w x.vCap x.eCap G) := fun _ =>
    dgDeleteEdge_meetsContract hEdge hOps
  have hDgUpdF : ∀ G H v v' St Sh len, MeetsContract w p (lsfBaseDg b + 12 + dgIdxApplyUpdate)
      (dgApplyUpdateContract w x.vCap (fECap x.eCap x.n0) G H (.split v v' St Sh) len) := fun _ _ _ _ _ _ _ =>
    dgApplyUpdate_meetsContract hBatch hEdge hSplit hOps
  have hDgUpdG : ∀ G v v' St Sh len, MeetsContract w p (lsfBaseDg b + 12 + dgIdxApplyUpdate)
      (dgApplyUpdateContract w x.vCap x.eCap G G (.split v v' St Sh) len) := fun _ _ _ _ _ _ =>
    dgApplyUpdate_meetsContract hBatch hEdge hSplit hOps
  have hBFS : ∀ F, MeetsContract w p (lsfBaseBat Q_AN b + 1) (splitCompBFSContract w F) := fun _ =>
    splitCompBFS_meetsContract (gBat 1 (by decide))
  have hTIns : ∀ G T_cur T₀ π, MeetsContract w p (lsfBaseBat Q_AN b + 4)
      (lsfTBlockInsertContract w x.vCap x.eCap x.tM G T_cur T₀ π x.tOrigList) := fun _ _ _ _ =>
    lsfTBlockInsert_meetsContract (gBat 4 (by decide))
      (fun _ => dgInsertEdge_meetsContract hEdge hOps)
  have hTDel : ∀ G T_cur T₀ π, MeetsContract w p (lsfBaseBat Q_AN b + 5)
      (lsfTBlockDeleteContract w x.vCap x.eCap x.tM G T_cur T₀ π x.tOrigList) := fun _ _ _ _ =>
    lsfTBlockDelete_meetsContract (gBat 5 (by decide))
      (fun _ => dgDeleteEdge_meetsContract hEdge hOps)
  have hTSplit : ∀ G T_cur T₀ π v v' St Sh len, MeetsContract w p (lsfBaseBat Q_AN b + 6)
      (lsfTBlockSplitContract w x.vCap x.eCap x.tM G T_cur T₀ π x.tOrigList v v' St Sh len) :=
    fun _ _ _ _ _ _ _ _ _ =>
      lsfTBlockSplit_meetsContract (gBat 6 (by decide))
        (fun _ => dgAddVertex_meetsContract hOps)
        (fun _ _ _ _ _ => dgMoveSlotLoop_meetsContract hSplit hOps)
  have hSetWstr : MeetsContract w p (lsfBaseBat Q_AN b + 3) (lsfSetWstrOneContract w h) :=
    lsfSetWstrOne_meetsContract (gBat 3 (by decide))
  exact ⟨_, M.hBatch, lsfApplyBatch_runs pos ω hwords hhead hrep hpre hfoot hz hsp
    hpIns hpDel hpSplit hpAdd hMinUp hDgDelF hDgInsG hDgDelG hDgUpdF hDgUpdG
    hBFS hTIns hTDel hTSplit hSetWstr⟩

/-! ## `DSRep.Implements` for `lsfDataStructure` (Lemma 5.4) -/

/-- `lsfModule Q_AN c_AN K_AN h` implements `lsfDataStructure Q_AN c_AN K_AN w h` under `LSFRep h`
at every word size `w` and limb width `h` (including `h = 1` and `h = 4`). -/
theorem lsfModule_implements {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    (hQ : ∀ (G_a : Cited.WGraph), G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
      (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
      ∃ out cost,
        RunsTo (wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
          G_a.IsSpanningTree out ∧
          G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n ∧
          (cost : ℝ) ≤ K_AN * (G_a.m + 1) *
            (Cited.logLogFactor G_a.n + Cited.weightFactor G_a.n G_a.maxWeight))
    (w h : ℕ) :
    DSRep.Implements (LSFRep h) w (lsfModule Q_AN c_AN K_AN h) lsfIdxInit (fun _ => lsfIdxBatch)
      (lsfDataStructure Q_AN c_AN K_AN w h) := by
  have hp : (lsfModule Q_AN c_AN K_AN h).HasAt 0 (lsfModuleProcs Q_AN c_AN K_AN 0 h) := by
    intro i hi
    simp [lsfModule, hi]
  refine ⟨lsfRep_local h, ?_, ?_⟩
  · intro args mem pos ω hwords hpre hz hsp
    dsimp only [lsfDataStructure] at hpre hsp ⊢
    simpa only [Nat.zero_add] using lsfInit_runs_of_hasAt hp hQ pos ω hwords hpre hz hsp
  · intro i b s x args mem pos ω hwords hhead hrep hpre hfoot hz hsp
    dsimp only [lsfDataStructure] at hpre hsp ⊢
    rcases hpre with ⟨rfl, hpre_b⟩
    obtain ⟨body, hbody, o, st', c, hrun, s', x', hrep', hpost', hresp', hc'⟩ :=
      lsfApplyBatch_runs_of_hasAt hp pos ω hwords hhead hrep hpre_b hfoot hz hsp
    exact ⟨body, by simpa only [Nat.zero_add] using hbody,
      o, st', c, hrun, s', x', hrep', ⟨rfl, hpost'⟩, hresp', hc'⟩

/-- End-to-end unconditional WordRAM realization of **Lemma 5.4** (page 17 of `arXiv:2309.16629v1`)
using the verified low-stretch spanning tree program (`cited_c_pos_of_lsst`), working for any limb
width `h ≥ 1` (in particular both `h = 1` and `h = 4`). -/
theorem lsfModule_from_cited (h : ℕ) :
    ∃ (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ),
      1 ≤ c_AN ∧
      (lsfModule Q_AN c_AN K_AN h).IsDeterministic ∧
      ∀ w, DSRep.Implements (LSFRep h) w (lsfModule Q_AN c_AN K_AN h)
        lsfIdxInit (fun _ => lsfIdxBatch) (lsfDataStructure Q_AN c_AN K_AN w h) := by
  obtain ⟨Q_AN, c_AN, K_AN, hc_pos, hQ⟩ := cited_c_pos_of_lsst
  exact ⟨Q_AN, c_AN, K_AN, hc_pos, lsfModule_isDeterministic Q_AN c_AN K_AN h,
    fun w => lsfModule_implements hQ w h⟩

/-! ## Non-vacuity of `lsfInitPre` and `lsfBatchPre` -/

/-- `lsfInitPre` together with `ZeroFrom` and the word-size space bound is satisfiable for every
`Q_AN`, `c_AN ≥ 1`, `K_AN`, and `h ≥ 1` (witnessed on a 1-vertex, 0-edge graph). -/
theorem lsfInitPre_nonvacuous (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (h : ℕ)
    (hc : 1 ≤ c_AN) (hh : 1 ≤ h) :
    ∃ w args mem,
      (∀ a ∈ args, a < 2 ^ w) ∧
      lsfInitPre c_AN K_AN w h args mem ∧
      ZeroFrom mem (heapArg args) ∧
      heapArg args + lsfInitSpace Q_AN K_AN c_AN h args mem < 2 ^ w := by
  let G₀ : MGraph := { V := {0}, E := ∅, tail := fun _ => 0, head := fun _ => 0 }
  let g0Ptr : ℕ := 0
  let vCap0 : ℕ := 1
  let eCap0 : ℕ := 1
  let b : ℕ := dynGraphSize vCap0 eCap0
  let L_in : ℕ := 2
  let P_fp : ℕ := 0
  let k_nat : ℕ := 1
  let L_w : ℕ := L_in + Nat.log 2 (defaultThreshNat K_AN 1 1 + 1) + 2
  let args : List ℕ := [g0Ptr, 0, 0, L_in, P_fp, k_nat, L_w, vCap0, eCap0, b]
  let mem : ℕ → ℕ :=
    Function.update
      (Function.update
        (Function.update
          (Function.update (fun _ => 0) 0 1)
          1 1)
        2 1)
      4 1
  have hmem_z : ZeroFrom mem b := by
    intro a ha
    have ha20 : 20 ≤ a := by dsimp only [b, vCap0, eCap0, dynGraphSize] at ha; omega
    dsimp only [mem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hGn : G₀.n = 1 := by simp [G₀, MGraph.n]
  have hGm : G₀.m = 0 := by simp [G₀, MGraph.m]
  have hGval : G₀.IsValid := fun _ he => absurd he (Finset.notMem_empty _)
  have hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀ := by
    refine ⟨hGval,
      fun u hu => by simp [G₀] at hu; omega,
      fun _ he => absurd he (Finset.notMem_empty _),
      by decide, by decide, by rw [hGn]; decide, by rw [hGm]; decide,
      fun v hv => by
        have hv0 : v = 0 := by omega
        subst hv0; simp [G₀, mem, g0Ptr, dgVPresBase],
      ⟨[0], by simp [hGn], by decide, fun v => by simp [G₀],
       fun i hi => by
         have hi0 : i = 0 := by simp at hi; omega
         subst hi0; simp [mem, g0Ptr, vCap0, dgVListBase],
       fun i hi => by
         have hi0 : i = 0 := by simp at hi; omega
         subst hi0; simp [mem, g0Ptr, vCap0, dgVPosBase]⟩,
      fun v hv => by
        have hv0 : v = 0 := by simp [G₀] at hv; exact hv
        subst hv0; simp [G₀, mem, g0Ptr, vCap0, dgExtToIntBase, dgIntToExtBase],
      fun s hs => by
        have hs0 : s = 0 := by simp [G₀] at hs; exact hs
        subst hs0; simp [G₀, mem, g0Ptr, vCap0, dgExtToIntBase, dgIntToExtBase],
      fun e he => by
        have he0 : e = 0 := by omega
        subst he0; simp [G₀, mem, g0Ptr, vCap0, dgEPresBase],
      ⟨[], by simp [hGm], by decide, fun e => by simp [G₀],
       fun i hi => by simp at hi, fun i hi => by simp at hi⟩,
      fun _ he => absurd he (Finset.notMem_empty _),
      ⟨fun _ => [], fun s hs => by
        have hs0 : s = 0 := by omega
        subst hs0
        refine ⟨?_, by simp [mem, g0Ptr, vCap0, dgSlotDegBase],
          fun h => by simp [G₀]⟩
        simp [IsDoublyLinkedList, mem, g0Ptr, vCap0, eCap0, dgIncHeadBase]⟩⟩
  let S_sp := b + lsfInitSpace Q_AN K_AN c_AN h args mem
  let B_all := max (S_sp + 1) (max (3 * (4 * k_nat * (hldDepthBound 1 + 1)) + 1)
    (max (L_w + 1) (b + 1)))
  let w : ℕ := max (3 * h + 2) (Nat.log 2 B_all + 1)
  have hB_lt : B_all < 2 ^ w :=
    lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by decide) B_all)
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  have hsp : heapArg args + lsfInitSpace Q_AN K_AN c_AN h args mem < 2 ^ w := by
    change S_sp < 2 ^ w
    have : S_sp < B_all := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    omega
  have hwords : ∀ a ∈ args, a < 2 ^ w := by
    intro a ha
    have hb_lt : b < 2 ^ w := by
      have : b < B_all := lt_of_lt_of_le (Nat.lt_succ_self _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      omega
    have hLw_lt : L_w < 2 ^ w := by
      have : L_w < B_all := lt_of_lt_of_le (Nat.lt_succ_self _)
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      omega
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp only [g0Ptr, L_in, P_fp, k_nat, vCap0, eCap0, b, dynGraphSize] at hb_lt hLw_lt ⊢; omega
  have hth_lt : defaultThreshNat K_AN G₀.n k_nat < 2 ^ (h * (L_w - L_in)) := by
    rw [hGn]
    have h1 : defaultThreshNat K_AN 1 1 < 2 ^ (Nat.log 2 (defaultThreshNat K_AN 1 1 + 1) + 1) := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by decide) (defaultThreshNat K_AN 1 1 + 1)
      omega
    have h2 : Nat.log 2 (defaultThreshNat K_AN 1 1 + 1) + 1 ≤ h * (L_w - L_in) := by
      have hsub : L_w - L_in = Nat.log 2 (defaultThreshNat K_AN 1 1 + 1) + 2 := by
        dsimp only [L_w]; omega
      rw [hsub]
      calc Nat.log 2 (defaultThreshNat K_AN 1 1 + 1) + 1
          ≤ 1 * (Nat.log 2 (defaultThreshNat K_AN 1 1 + 1) + 2) := by omega
        _ ≤ h * (Nat.log 2 (defaultThreshNat K_AN 1 1 + 1) + 2) := Nat.mul_le_mul_right _ hh
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h2)
  have h2_hLw : 2 ≤ h * L_w := by
    calc 2 = 1 * 2 := by decide
      _ ≤ h * L_w := Nat.mul_le_mul hh (by dsimp only [L_w, L_in]; omega)
  refine ⟨w, args, mem, hwords, ?_, hmem_z, hsp⟩
  refine ⟨G₀, fun _ => 1, fun _ => 1, g0Ptr, vCap0, eCap0, 0, 0, L_in, P_fp, k_nat, L_w,
    vCap0, eCap0, b, rfl, hc, hh, le_max_left _ _, hGval,
    ⟨0, Finset.mem_singleton_self 0⟩, hdg0, le_rfl, le_rfl, le_rfl, by decide,
    by dsimp only [b, vCap0, eCap0, L_in, dynGraphSize]; omega,
    by dsimp only [b, vCap0, eCap0, L_in, dynGraphSize]; omega,
    by decide, by dsimp only [L_in]; omega, dvd_zero h, by decide, ?_,
    by dsimp only [L_w]; omega, h2_hLw, hth_lt,
    fun _ he => absurd he (Finset.notMem_empty _),
    fun _ he => absurd he (Finset.notMem_empty _)⟩
  rw [hGn]
  have : 3 * (4 * k_nat * (hldDepthBound 1 + 1)) < B_all :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_left _ _) (le_max_right _ _))
  omega

/-- `lsfBatchPre` is satisfiable on any represented LSF state (witnessed by an empty batch at
`x.endAddr b` below `heap`). -/
theorem lsfBatchPre_nonvacuous {w h b heap : ℕ} {S : LSFState} {x : LSFConcrete} {mem : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hrep : (LSFRep h).rep b S x mem)
    (hend : x.endAddr b + 1 ≤ heap) (hz : ZeroFrom mem (x.endAddr b)) :
    lsfBatchPre w S [b, x.endAddr b, heap] mem := by
  have hhdr := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hend_m : mem (b + lsfOffEnd) = x.endAddr b := hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨b, x.endAddr b, heap, [], 1, rfl, hw16,
    ⟨le_rfl, hz (x.endAddr b) le_rfl, rfl⟩, trivial,
    fun _ hu => absurd hu (List.not_mem_nil),
    fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0; rw [Nat.add_zero, hz (x.endAddr b) le_rfl]; omega,
    hend, fun i _ => Or.inr (by rw [hend_m]; omega)⟩

end

end MinCostFlow.LSF.Program
