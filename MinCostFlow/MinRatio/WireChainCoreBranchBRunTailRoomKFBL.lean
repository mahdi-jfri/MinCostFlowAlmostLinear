module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailPartGoalsKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailPhaseKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBFrontRepKFBL
import MinCostFlow.MinRatio.WireChainCoreSyncDefs
import WordRAM.Tactic

/-!
# The room of the suffix of Branch B on a head (`WireChainCoreBranchBRunTailRoomKFBL`)

`BranchBTailRoomGoalKFBL` bounds the heap pointer after the exit plus the space of the suffix by
`heap + coreSpace U.length`. The proof is the one of `branchBSpace_space`
(`WireChainCoreBranchBSpaceProofSpace.lean`) without its last step: the heap of the prefix (Sync 1
and the refresh), of the front (the batch copy, at most `4 |U| + 1` words), of the loop (the step
spaces) and of the exit (in each of its three cases) add up to the pointer `sX.regs 4`, the edge
counts `T` and `S` of the suffix are at most `forestEdgeCap` (`start.forestCap`), and
`spaceTotalBranchB` of the environment bounds the sum.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

private lemma rebuildSuffix_lt (T : SparseCoreRestartTool) (L : LastLevelTool) (P : ChainParams)
    (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ)
      {j : ℕ}, j < idx →
      let res := Chain.Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec
        cFwd
      res.1 j = G j ∧ res.2.1 j = sc j ∧ res.2.2.1 j = bran j
  | 0, _, _, _, _, _, _, _, _, _, _ => ⟨rfl, rfl, rfl⟩
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd, j, hj => by
    dsimp only [Chain.Ordered.rebuildSuffix]
    have hne1 : j ≠ idx + 1 := by omega
    have hne0 : j ≠ idx := by omega
    refine (fun h => ⟨h.1.trans (ite_eq_right hne1), h.2.1.trans (ite_eq_right hne0),
      h.2.2.trans (ite_eq_right hne0)⟩)
      (rebuildSuffix_lt T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1) _ _ _ _ _ _ _ (by omega))

private lemma list_sum_map_range (f : ℕ → ℕ) :
    ∀ n, ((List.range n).map f).sum = ∑ t ∈ Finset.range n, f t
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      Finset.sum_range_succ, list_sum_map_range f n]

private lemma graphListEdgeSum_chainSuffixForests_eq {T : SparseCoreRestartTool} {P : ChainParams}
    (c : ChainState T P) (first : ℕ) :
    graphListEdgeSum (chainSuffixForests c first) =
      (∑ t ∈ Finset.range (P.d - first), (T.lsfs (c.scState (first + t)) (c.bran (first + t))).F.F.m) +
      (c.lastLSFs c.lastBran).F.F.m := by
  unfold graphListEdgeSum chainSuffixForests
  rw [List.map_append, List.sum_append, List.map_map, List.map_singleton, List.sum_singleton,
    list_sum_map_range]
  rfl

private lemma sum_range_shift_le (f : ℕ → ℕ) {first d : ℕ} (hfd : first ≤ d) :
    ∑ t ∈ Finset.range (d - first), f (first + t) ≤ ∑ j ∈ Finset.range d, f j := by
  have h1 : ∑ t ∈ Finset.range (d - first), f (first + t) = ∑ j ∈ Finset.Ico first d, f j := by
    refine Finset.sum_nbij' (fun t => first + t) (fun j => j - first) ?_ ?_ ?_ ?_ ?_
    · intro t ht
      rw [Finset.mem_range] at ht
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · intro j hj
      rw [Finset.mem_Ico] at hj
      exact Finset.mem_range.mpr (by omega)
    · intro t _; omega
    · intro j hj; rw [Finset.mem_Ico] at hj; omega
    · intro _ _; rfl
  rw [h1]
  refine Finset.sum_le_sum_of_subset fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  exact Finset.mem_range.mpr hj.2

private lemma graphListEdgeSum_chainSuffixForests_le_zero {T : SparseCoreRestartTool} {P : ChainParams}
    (c : ChainState T P) {first : ℕ} (hfd : first ≤ P.d) :
    graphListEdgeSum (chainSuffixForests c first) ≤ graphListEdgeSum (chainSuffixForests c 0) := by
  rw [graphListEdgeSum_chainSuffixForests_eq, graphListEdgeSum_chainSuffixForests_eq, Nat.sub_zero]
  simp only [Nat.zero_add]
  exact Nat.add_le_add_right
    (sum_range_shift_le (fun j => (T.lsfs (c.scState j) (c.bran j)).F.F.m) hfd) _

private lemma room_combine {heap d uLen treeSp refSp L stepSum levelSum lastSpace
    termUpdSpace forestCap intCapMax fcap N0 M0 coreSp hS1 heap2 sF0r4 sEr4 sXr4 bW T S
    intCap : ℕ}
    (hhS1 : hS1 ≤ heap + 1 + 12 * d + 3 * (d + 1) + 4 + (3 * uLen + uLen * treeSp))
    (hheap2 : heap2 ≤ hS1 + 3 * L + uLen * refSp)
    (hsF0 : sF0r4 = heap2 + bW)
    (hbW : bW ≤ 4 * uLen + 1)
    (hsE : sEr4 ≤ sF0r4 + stepSum)
    (hsX : sXr4 ≤ sEr4 + (10 * d + 2 * N0 + 2 * M0 + 10 + levelSum + lastSpace) + termUpdSpace)
    (hT : T ≤ forestCap) (hS : S ≤ forestCap) (hCap : intCap ≤ intCapMax)
    (hTot : (1 + 12 * d) + 3 * (d + 1) + 4 + (3 * uLen + uLen * treeSp) +
        (3 * L + uLen * refSp) + (4 * uLen + 1) + stepSum +
        (10 * d + 2 * N0 + 2 * M0 + 10 + levelSum + lastSpace) + termUpdSpace +
        (2 * forestCap + forestCap * treeSp + 1) +
        (3 * intCapMax + 4 * forestCap + forestCap * treeSp + 1) +
        (5 + fcap + 5 * d) ≤ coreSp) :
    sXr4 + (2 * T + T * treeSp) + (3 * intCap + 4 * S + S * treeSp) + 1 ≤ heap + coreSp := by
  have hTmul : T * treeSp ≤ forestCap * treeSp := Nat.mul_le_mul_right treeSp hT
  have hSmul : S * treeSp ≤ forestCap * treeSp := Nat.mul_le_mul_right treeSp hS
  omega

namespace BranchBRunHeadKFBL

variable {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
      collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {stepCap : ℕ → ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}

variable (Hd : BranchBRunHeadKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)

/-- Levels below `min fr d` are the same in the model `chE` at the end of the loop and in the
model `X` after the exit, in the three exits of Branch B. -/
theorem chain_lt_eq
    {j : ℕ} (hj : j < min Hd.fr cfg.P.d) :
    Hd.chE.G j = Hd.X.G j ∧ Hd.chE.scState j = Hd.X.scState j ∧ Hd.chE.bran j = Hd.X.bran j := by
  rcases Hd.exitCase with hInt | hTerm | hEmpty
  · obtain ⟨_, hiLt, hfr, _, _, hX, _, _, _⟩ := hInt
    have hjI : j < Hd.i₀ := by omega
    rw [hX]
    simp only [Chain.Ordered.algorithm1_rebuild, dite_eq_left_of_eq_true (eq_true hiLt)]
    have hR := rebuildSuffix_lt cfg.T cfg.L cfg.P Hd.chE.lvlM Hd.chE.N₀ Hd.ℓ' Hd.g'
      (cfg.P.d - Hd.i₀) Hd.i₀
      (fun k => if k = Hd.i₀ then Hd.curGE else Hd.chE.G k) Hd.chE.scState Hd.chE.bran Hd.chE.updCount
      Hd.chE.curEnc Hd.chE.curDecUpdates Hd.chE.curFwd hjI
    have hne : j ≠ Hd.i₀ := by omega
    exact ⟨by rw [hR.1, ite_eq_right hne], hR.2.1.symm, hR.2.2.symm⟩
  · obtain ⟨hiEq, hneU, _, _, _, hX, _, _, _, _⟩ := hTerm
    have hjd : j < cfg.P.d := by omega
    rw [hX]
    simp [Chain.Ordered.updateLoop, ite_eq_right hneU, hjd.ne]
  · obtain ⟨hiEq, hEmp, _, _, _, hX, _, _, _, _, _, _, _⟩ := hEmpty
    have hjd : j < cfg.P.d := by omega
    rw [hX]
    simp [Chain.Ordered.updateLoop, ite_eq_left hEmp, hjd.ne]

/-- **The room of the suffix on a head.** -/
theorem room :
    let T := ∑ j ∈ Finset.range Hd.i₀, (Hd.D j).fDel.length
    let S := graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else []) +
      graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.X Hd.fr else [])
    Hd.sX.regs 4 + (2 * T + T * wireTreeSyncEditSpace L) +
        (3 * tok.intCap + 4 * S + S * wireTreeSyncEditSpace L) + 1 ≤
      heap + coreSpace U.length := by
  intro T S
  -- 1. Prefix heap bounds
  have hPre := Hd.pre
  have hhS1 : Hd.hS1 ≤ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 +
      (3 * U.length + U.length * wireTreeSyncEditSpace L) := by
    have := hPre.2.2.2.2.1; omega
  have hheap2 : Hd.heap2 ≤ Hd.hS1 + 3 * L + U.length * wireRefreshOneSpace L := hPre.2.2.2.2.2.2.1
  -- 2. Front heap bound (`editsPtr - d - uIntBuf ≤ 4 * U.length + 1`)
  have hsF0 : Hd.sF0.regs 4 = Hd.heap2 + (editsPtr - cfg.P.d - uIntBuf) := Hd.front.2.2.1
  have hbW : editsPtr - cfg.P.d - uIntBuf ≤ 4 * U.length + 1 := by
    have hEdits := branchBLevel0Edits_of_rep Hd.start.rep0 Hd.start.caps0 Hd.start.modelInv
      Hd.start.refresh
    have hEdge : ∀ u ∈ (translateBatch model.extG model.extToInt model.intToExt
        model.nextFresh U).2.2.2.2, IsEdgeUpdate u := hEdits.2.2.1
    have hLe := smallBatchAt_words_le_edgeOnly Hd.start.small hEdge
    have hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt
        model.nextFresh := Hd.start.rep0.2.2.2.2.1
    have hLen : (translateBatch model.extG model.extToInt model.intToExt
        model.nextFresh U).2.2.2.2.length = U.length :=
      (translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt model.intToExt
        model.nextFresh hFresh Hd.start.refresh.1).2.2.2.2.1
    rw [hLen] at hLe
    exact hLe
  -- 3. Loop heap bound
  have hi₀Le : Hd.i₀ ≤ cfg.P.d := Hd.loop.2.2.1
  have hsE : Hd.sE.regs 4 ≤ Hd.sF0.regs 4 +
      (Finset.range cfg.P.d).sum (fun j => updStepSpace j U.length) := by
    have hL := Hd.loop.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hSub : Finset.Ico 0 Hd.i₀ ⊆ Finset.range cfg.P.d := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      exact Finset.mem_range.mpr (lt_of_lt_of_le hj.2 hi₀Le)
    exact hL.trans (Nat.add_le_add_left (Finset.sum_le_sum_of_subset hSub) _)
  -- 4. Exit heap bound (all three cases)
  have hsX : Hd.sX.regs 4 ≤ Hd.sE.regs 4 +
      (10 * cfg.P.d + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P 0 + 10 +
        (Finset.range cfg.P.d).sum levelSpace + lastSpace) + termUpdSpace := by
    rcases Hd.exitCase with hInt | hTerm | hEmpty
    · obtain ⟨hiPos, hiLt, hfr, _, _, _, _, hXLe, _⟩ := hInt
      have hSub : Finset.Ico Hd.i₀ cfg.P.d ⊆ Finset.range cfg.P.d := fun j hj =>
        Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
      have hSumLe : (Finset.Ico Hd.i₀ cfg.P.d).sum levelSpace ≤
          (Finset.range cfg.P.d).sum levelSpace := Finset.sum_le_sum_of_subset hSub
      have hEq := chain_lt_eq Hd (j := Hd.i₀ - 1) (by omega)
      have hRotEq : ordRotWords (chainLevelOrdAbs Hd.chE (Hd.i₀ - 1)) (Hd.chE.bran (Hd.i₀ - 1)) =
          ordRotWords (chainLevelOrdAbs Hd.X (Hd.i₀ - 1)) (Hd.X.bran (Hd.i₀ - 1)) := by
        unfold ordRotWords chainLevelOrdAbs
        dsimp only
        rw [hEq.2.1, hEq.2.2]
      have hModKFBL := Hd.start.modelInvKFBL
      have hXEq : Hd.X = (alg2PreResetState cfg model U
          (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
          (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
        rw [Hd.modelEq, Hd.gVec_eq, Hd.lVec_eq]
      have hFacts : ShiftLoopLevelFacts cfg Hd.X := hXEq ▸ hModKFBL.2.1
      have hNLe : (Hd.X.G Hd.i₀).n ≤ cfg.N₀ := by
        have h1 : (Hd.X.G Hd.i₀).n ≤ Hd.X.N₀ := hXEq ▸ hModKFBL.2.2.2.1 Hd.i₀ hiLt.le
        rw [hFacts.2.2.1] at h1
        exact h1
      have hMLe : (Hd.X.G Hd.i₀).m ≤ levelM cfg.TP cfg.P 0 := by
        have h0 : (Hd.X.G 0).m ≤ levelM cfg.TP cfg.P 0 :=
          hXEq ▸ hModKFBL.2.2.2.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
        exact (hFacts.2.2.2 Hd.i₀ hiLt.le).trans h0
      have hRotBd : ordRotWords (chainLevelOrdAbs Hd.X (Hd.i₀ - 1)) (Hd.X.bran (Hd.i₀ - 1)) ≤
          1 + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P 0 := by
        have h1 : ordRotWords (chainLevelOrdAbs Hd.X (Hd.i₀ - 1)) (Hd.X.bran (Hd.i₀ - 1)) ≤
            1 + 2 * (Hd.X.G (Hd.i₀ - 1 + 1)).n + 2 * (Hd.X.G (Hd.i₀ - 1 + 1)).m :=
          hXEq ▸ hModKFBL.2.2.2.2.1 (Hd.i₀ - 1) (by omega)
        rw [show Hd.i₀ - 1 + 1 = Hd.i₀ by omega] at h1
        omega
      rw [hRotEq] at hXLe
      omega
    · obtain ⟨_, _, _, _, _, _, _, _, ⟨h1, _, hh1, hXr4⟩, _⟩ := hTerm
      have hTD := Hd.envA.ops.termUpdSpaceDom
      omega
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hXr4, _⟩ := hEmpty
      omega
  have hTLe : ∑ j ∈ Finset.range Hd.i₀, (Hd.D j).fDel.length ≤ forestEdgeCap := by
    have hInv := Hd.loop.2.2.2.2.1
    have hStep : ∀ j ∈ Finset.range Hd.i₀,
        (Hd.D j).fDel.length ≤ (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.m := by
      intro j hj
      have hjLt : j < Hd.i₀ := Finset.mem_range.mp hj
      have hsm := hInv.slotModel j hjLt
      have hNodup : (Hd.D j).fDel.Nodup := hsm.2.2.1
      have hFin : (Hd.D j).fDel.toFinset =
          (cfg.T.lsfs (Hd.st0.scState j) (Hd.st0.bran j)).F.F.E \
          (cfg.T.lsfs (Hd.chE.scState j) (Hd.chE.bran j)).F.F.E := hsm.2.2.2.1
      have hCard : (Hd.D j).fDel.length = (Hd.D j).fDel.toFinset.card :=
        (List.toFinset_card_of_nodup hNodup).symm
      have hSt0Sc : Hd.st0.scState j = model.chain.scState j := by rw [Hd.st0_eq]
      have hSt0Br : Hd.st0.bran j = model.chain.bran j := by rw [Hd.st0_eq]
      rw [hCard, hFin, hSt0Sc, hSt0Br]
      exact Finset.card_le_card Finset.sdiff_subset
    have hSum1 : ∑ j ∈ Finset.range Hd.i₀, (Hd.D j).fDel.length ≤
        ∑ j ∈ Finset.range Hd.i₀,
          (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.m :=
      Finset.sum_le_sum hStep
    have hSub : Finset.range Hd.i₀ ⊆ Finset.range cfg.P.d := Finset.range_mono hi₀Le
    have hSum2 : ∑ j ∈ Finset.range Hd.i₀,
          (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.m ≤
        ∑ j ∈ Finset.range cfg.P.d,
          (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.m :=
      Finset.sum_le_sum_of_subset hSub
    have hEq0 : graphListEdgeSum (chainSuffixForests model.chain 0) =
        (∑ j ∈ Finset.range cfg.P.d,
          (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.m) +
        (model.chain.lastLSFs model.chain.lastBran).F.F.m := by
      simpa [Nat.sub_zero, Nat.zero_add] using graphListEdgeSum_chainSuffixForests_eq model.chain 0
    have hFC := Hd.start.forestCap
    omega
  have hSLe : S ≤ forestEdgeCap := by
    have hOldEq : (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else []) =
        if Hd.fr ≤ cfg.P.d then chainSuffixForests model.chain Hd.fr else [] := by
      split_ifs
      · unfold chainSuffixForests
        have hSc : Hd.st0.scState = model.chain.scState := by rw [Hd.st0_eq]
        have hBr : Hd.st0.bran = model.chain.bran := by rw [Hd.st0_eq]
        have hLs : Hd.st0.lastLSFs = model.chain.lastLSFs := by rw [Hd.st0_eq]
        have hLb : Hd.st0.lastBran = model.chain.lastBran := by rw [Hd.st0_eq]
        rw [hSc, hBr, hLs, hLb]
      · rfl
    have hXEq : Hd.X = (alg2PreResetState cfg model U
        (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
        (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
      rw [Hd.modelEq, Hd.gVec_eq, Hd.lVec_eq]
    show graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else []) +
      graphListEdgeSum (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.X Hd.fr else []) ≤ _
    rw [hOldEq, hXEq]
    split_ifs with hfr
    · exact (Nat.add_le_add (graphListEdgeSum_chainSuffixForests_le_zero model.chain hfr)
        (graphListEdgeSum_chainSuffixForests_le_zero _ hfr)).trans Hd.start.forestCap
    · simp [graphListEdgeSum]
  exact room_combine hhS1 hheap2 hsF0 hbW hsE hsX hTLe hSLe Hd.start.intCapLe
    (Hd.envA.ops.spaceTotalBranchB U.length)

end BranchBRunHeadKFBL

/-- The room goal of the tail (`BranchBTailRoomGoalKFBL`) holds: `room`. -/
theorem branchBTailRoomGoalKFBL_proved : BranchBTailRoomGoalKFBL :=
  fun Hd => BranchBRunHeadKFBL.room Hd

end MinCostFlow.MinRatio

end
