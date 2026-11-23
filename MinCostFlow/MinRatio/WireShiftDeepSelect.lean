module

public import MinCostFlow.MinRatio.WireShiftDeepSelectAux
import WordRAM.Tactic

/-!
# Main deep-shift select-refresh theorem (`WireShiftDeepSelect`)

Proves `shiftDeepSelectBody_runs` for `shiftDeepSelectBody` (`WireShiftDeepSelectAux.lean`):
wraps a deep-shift chain-synchronization procedure (`ShiftDeepChainSyncSpecWExtKFBL`) with an
in-place refresh of the select region `[sb, B.endAddr)` for levels `i .. d`, preserving
`solverStateRep`, `SolverLevelCapsInv`, `PathTreeNumericInv`, `OffTreeRecInv`, `OffTreeRecBound`,
`SelectRegionAt`, and `SolverSelectInv` in space `deepSpace + shiftDeepSelectSpaceBound` and
amortized cost `(deepFixed + shiftDeepSelectFixedBound) + (deepToolMul +
shiftDeepSelectToolMulBound) * Δrt + treeMul * Δtu`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Bundle Chain Chain.Ordered IPM.Machine Num DynSpanner.Program SparseCore.Program

set_option maxHeartbeats 1600000 in
/-- End-to-end verification of `shiftDeepSelectBody`: runs `deepProc` via
`ShiftDeepChainSyncSpecWExtKFBL` and refreshes the select metadata table, interior blocks `i .. d-1`,
terminal blocks `G_d / F_d / coreLen_d`, frozen potentials `φ_i .. φ_d`, and select-heap
candidates `i .. d`, preserving `solverStateRep`, `SolverLevelCapsInv`, `PathTreeNumericInv`,
`OffTreeRecInv`, `OffTreeRecBound`, `SelectRegionAt`, and `SolverSelectInv` in space
`deepSpace + shiftDeepSelectSpaceBound` and amortized cost
`(deepFixed + shiftDeepSelectFixedBound) + (deepToolMul + shiftDeepSelectToolMulBound) * Δrt +
treeMul * Δtu`. -/
theorem shiftDeepSelectBody_runs
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap pLast sb metaBase depth evalSpace evalCost K
      deepSpace deepFixed deepToolMul treeMul
      deepProc tableWriteProc intLoopProc fillIntProc fillLastProc finalizeProc
      phiLoopProc phiFillProc rebuildSuffixProc rebuildLvlProc
      dgCopyProc coreLenProc filterProc embCopyProc : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G G₀' : MGraph} {initialGraph : ℕ → MGraph}
    {σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {pot : cfg.T.State → ℕ}
    {p : Program} {op : ℕ → ℕ} {ω : ℕ → Bool}
    {root heap pos : ℕ} {i : Fin (cfg.P.d + 1)} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {sg : SelectGhost}
    {B : SelectBlocksLoc} {B_t R_t : ℤ} {PhiBd : (ℕ → ℕ → ℝ) → ℕ → Prop}
    -- Word/format/config facts
    (hlocalCore : Rcore.Local)
    (hfmt4 : fmt.limbBits = 4) (hfmtP : fmt.precision = P)
    (hw16 : 16 < 2 ^ w) (hw10 : 10 ≤ w) (hLkW : L < 2 ^ w) (hpLastW : pLast < 2 ^ w)
    (hkW : cfg.P.k < 2 ^ w) (hSlotW : B.slot < 2 ^ w) (heCapPos : 0 < eCap)
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (hMono : ToolCostMono cfg.T) (hPot : ToolReembPotFacts cfg.T pot)
    (hRestartLower : ∀ {M N n b : ℕ} {st : cfg.T.State} {G' : MGraph} {ord : ℕ → List End},
      SparseCoreOrdInput cfg.T cfg.P.k M N st G' ord n → b < cfg.P.k →
      G'.m * SparseCore.bundleLogFactor M N ≤ cfg.T.cost (cfg.T.restart st b) - cfg.T.cost st)
    (hInitLower : ∀ {M N : ℕ} {G' : MGraph} {ℓ' g' : ℕ → ℝ} {ord : ℕ → List End},
      G'.IsValid →
      3 * G'.m * SparseCore.bundleLogFactor M N ≤ cfg.T.cost (cfg.T.initOrd cfg.P.k M N G' ℓ' g' ord))
    (hK : selectProcessEdgeCost sg.loc.cap L evalCost + 60 ≤ K)
    -- Sub-procedure specifications
    (hDeepSpec : ShiftDeepChainSyncSpecWExtKFBL w L P m V psi k epsExp drainUnit capExp limbMul
      capLimit wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg Rcore p deepProc
      deepSpace deepFixed deepToolMul treeMul)
    (hTableWrite : ∀ lvlMeta,
      MeetsContract w p tableWriteProc (selTableWriteContract w B metaBase lvlMeta pLast))
    (hpIntLoop : p.procs[intLoopProc]? = some (selectInitInteriorLoopBody intLoopProc fillIntProc))
    (hpFillInt : p.procs[fillIntProc]? =
      some (selectFillInteriorLevelBody (op 2) (op 4) dgCopyProc coreLenProc filterProc embCopyProc))
    (hpFillLast : p.procs[fillLastProc]? =
      some (selectFillLastLevelBody dgCopyProc coreLenProc))
    (hpFinalize : p.procs[finalizeProc]? =
      some (selectRefreshFinalizeBody phiLoopProc rebuildSuffixProc))
    (hpPhiLoop : p.procs[phiLoopProc]? = some (selectPhiLoopBody phiLoopProc phiFillProc))
    (hpRebSuf : p.procs[rebuildSuffixProc]? =
      some (selectRebuildSuffixBody rebuildSuffixProc rebuildLvlProc))
    (hFootAt : ∀ j, i.val ≤ j → j < cfg.P.d →
      SparseCoreReadoutFootAt fmt L depth cfg.T (initialGraph j) cfg.P.k
        ((alg2LoopShiftStep cfg model i).chain.lvlM j)
        (alg2LoopShiftStep cfg model i).chain.N₀ vCap eCap capExp Psc allocation Rcore p op)
    (hDgCopy : ∀ vcF ecF (Fold Fnew : MGraph),
      MeetsContract w p dgCopyProc (dgCopyRefillContract w vCap eCap vcF ecF Fold Fnew))
    (hCoreLen : ∀ eL : List ℕ, MeetsContract w p coreLenProc (selCoreLenFillContract w P eCap eL))
    (hFilter : ∀ eL : List ℕ, MeetsContract w p filterProc (selFilterAbsentContract w eL))
    (hEmbCopy : ∀ j, i.val ≤ j → j < cfg.P.d → ∀ eL : List ℕ,
      MeetsContract w p embCopyProc
        (selEmbCopyContract w eL ((alg2LoopShiftStep cfg model i).chain.toTreeChain.activeEmb j)))
    (hPhiFill : ∀ (solverG : ℕ → ℕ) (φ : ℕ → ℕ → ℝ),
      MeetsContract w p phiFillProc
        (selectPhiFillContract w 4 P (selectMlocOf B metaBase solverG pLast)
          (alg2LoopShiftStep cfg model i).chain.toTreeChain G₀'
          (alg2LoopShiftStep cfg model i).chain.g (alg2LoopShiftStep cfg model i).chain.ℓ
          σ' σ'_mwu γ'_ℓ γ'_c φ))
    (hRebLvl : ∀ (solverG : ℕ → ℕ) (φ : ℕ → ℕ → ℝ),
      MeetsContract w p rebuildLvlProc
        (selectRebuildLevelNoRoomContract w 4 P sg.loc (selectMlocOf B metaBase solverG pLast)
          (alg2LoopShiftStep cfg model i).chain.toTreeChain
          (alg2LoopShiftStep cfg model i).chain.g (alg2LoopShiftStep cfg model i).chain.ℓ
          φ (fun j => (alg2LoopShiftStep cfg model i).chain.toTreeChain.chainLen
            (alg2LoopShiftStep cfg model i).chain.ℓ (j + 1)) evalSpace evalCost))
    -- Pre-state hypotheses (deep shift + select region)
    (hiLt : i.val < cfg.P.d)
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hMemEq : ∀ a, tok.tag a ≠ 5 → mem a = mem0 a)
    (hSched' : SolverScheduleAt mem tok.levelsEnd (alg2LoopShiftStep cfg model i))
    (hNum0 : PathTreeNumericInv tok.tree tok.trees B_t R_t)
    (hOffInv0 : OffTreeRecInv model L mem0 tok.edgeRecords B_t)
    (hOffBd0 : OffTreeRecBound model L mem0 tok.edgeRecords B_t)
    (hCapFacts : WireCapFacts capExp limbMul L capLimit model)
    (hBranLt : ∀ j < cfg.P.d, model.chain.bran j < cfg.P.k)
    (hModelInv : ShiftDeepModelInv w L P wordExp stretchPrec model i)
    (hModelK : ShiftDeepModelInvKFBL model i)
    (hIntCapLe : tok.intCap ≤ intCapMax)
    (hForestCap : graphListEdgeSum (chainSuffixForests model.chain i.val) +
      graphListEdgeSum (chainSuffixForests (alg2LoopShiftStep cfg model i).chain i.val) ≤ forestEdgeCap)
    (hLogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hCapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B_t + R_t) < (Num.capacity 4 L : ℤ))
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < heap)
    (hzHeap : ZeroFrom mem heap)
    -- Select pre-state & post-shift fit hypotheses
    (hRegAt0 : SelectRegionAt G P m vCap eCap pLast sb metaBase B model tok sg mem0)
    (hReembPot0 : sg.reembPot = chainReembPot pot model.chain)
    (hOwnDisj0 : ∀ a, sb ≤ a → a < B.endAddr →
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a)
    (hEndHeap : B.endAddr ≤ heap)
    (hModNew : SelectModelInv (alg2LoopShiftStep cfg model i) G₀' σ' σ'_mwu γ'_ℓ γ'_c)
    (hOldEcap : (model.chain.G i.val).m ≤ eCap)
    (hNewVcap : ∀ j ≤ cfg.P.d, ∀ v ∈ ((alg2LoopShiftStep cfg model i).chain.G j).V, v < vCap)
    (hNewEcap : ∀ j ≤ cfg.P.d, ∀ e ∈ ((alg2LoopShiftStep cfg model i).chain.G j).E, e < eCap)
    (hNewEcapHeap : ∀ j ≤ cfg.P.d, ∀ e ∈ ((alg2LoopShiftStep cfg model i).chain.G j).E, e < sg.loc.cap)
    (hLenFitInt : ∀ j, i.val ≤ j → j < cfg.P.d →
      ∀ e ∈ ((alg2LoopShiftStep cfg model i).chain.G j).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧
          (q : ℝ) / (2 : ℝ) ^ P =
            (alg2LoopShiftStep cfg model i).chain.toTreeChain.chainLen
              (alg2LoopShiftStep cfg model i).chain.ℓ (j + 1) e)
    (hEmbSlot : ∀ j, i.val ≤ j → j < cfg.P.d →
      ∀ e ∈ ((alg2LoopShiftStep cfg model i).chain.toTreeChain.activeCore j).E,
        (mWalkEncode ((alg2LoopShiftStep cfg model i).chain.toTreeChain.activeEmb j e)).length ≤ B.slot)
    (hLenFitLast : ∀ e ∈ ((alg2LoopShiftStep cfg model i).chain.G cfg.P.d).E,
      (∀ (prevLen : ℕ) (m' : ℕ → ℕ),
        EdgeValuesAt m' prevLen 4 L P ((alg2LoopShiftStep cfg model i).chain.G cfg.P.d).E
          ((alg2LoopShiftStep cfg model i).chain.toTreeChain.chainLen
            (alg2LoopShiftStep cfg model i).chain.ℓ cfg.P.d) →
        Num.Fits 4 L (Num.intVal m' (prevLen + e * L) 4 L * (2 : ℤ) ^ pLast)) ∧
      ∃ q : ℤ, Num.Fits 4 L q ∧
        (q : ℝ) / (2 : ℝ) ^ (P + pLast) =
          (alg2LoopShiftStep cfg model i).chain.toTreeChain.chainLen
            (alg2LoopShiftStep cfg model i).chain.ℓ (cfg.P.d + 1) e)
    (hPhiBdPref : ∀ r < i.val, PhiBd sg.φ r)
    (hPhiBdStep : ∀ j ≤ cfg.P.d, ∀ (φ : ℕ → ℕ → ℝ) (φj : ℕ → ℝ),
      (∀ r < j, SelectPotInvAt (alg2LoopShiftStep cfg model i).chain.toTreeChain
        (alg2LoopShiftStep cfg model i).chain.g φ r) →
      (∀ r < j, PhiBd φ r) →
      (∀ v ∈ ((alg2LoopShiftStep cfg model i).chain.toTreeChain.activeLSF j).F.F.V,
        ∃ r ∈ ((alg2LoopShiftStep cfg model i).chain.toTreeChain.activeLSF j).F.F.V,
          ((alg2LoopShiftStep cfg model i).chain.toTreeChain.activeLSF j).F.F.Connected v r ∧
          φj v = walkInner (potGrad (alg2LoopShiftStep cfg model i).chain.toTreeChain
            (alg2LoopShiftStep cfg model i).chain.g φ j)
            (((alg2LoopShiftStep cfg model i).chain.toTreeChain.activeLSF j).F.F.forestPath v r)) →
      ∀ r < j + 1, PhiBd (Function.update φ j φj) r)
    (hFitPhi : ∀ j ≤ cfg.P.d, ∀ φ' : ℕ → ℕ → ℝ,
      (∀ r < j, SelectPotInvAt (alg2LoopShiftStep cfg model i).chain.toTreeChain
        (alg2LoopShiftStep cfg model i).chain.g φ' r) →
      (∀ r < j, PhiBd φ' r) →
      (∀ e ∈ ((alg2LoopShiftStep cfg model i).chain.toTreeChain.activeLSF j).F.F.E,
        PotGradEvalFits 4 L P (alg2LoopShiftStep cfg model i).chain.toTreeChain
          (alg2LoopShiftStep cfg model i).chain.g φ' j e) ∧
      ForestWalkFits 4 L P ((alg2LoopShiftStep cfg model i).chain.toTreeChain.activeLSF j).F.F
        (potGrad (alg2LoopShiftStep cfg model i).chain.toTreeChain
          (alg2LoopShiftStep cfg model i).chain.g φ' j))
    (hroom : heap + deepSpace + shiftDeepSelectSpaceBound cfg.P.d vCap eCap sg.loc.cap L capExp
        (levelM cfg.TP cfg.P 0) cfg.N₀ evalSpace < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let model' := alg2LoopShiftStep cfg model i
    let M₀ := levelM cfg.TP cfg.P 0
    ∃ nextHeap cost out tok' sg',
      Runs w p ω (shiftDeepSelectBody deepProc tableWriteProc intLoopProc (op 3) fillLastProc finalizeProc)
        (startState [root, i.val, heap] mem pos) (.returned nextHeap) out cost ∧
      heap ≤ nextHeap ∧
      nextHeap ≤ heap + deepSpace + shiftDeepSelectSpaceBound cfg.P.d vCap eCap sg.loc.cap L capExp M₀ cfg.N₀ evalSpace ∧
      tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
      tok'.table = tok.table ∧ tok'.rootECap = tok.rootECap ∧
      out.mem (solverSelectHeapAddr tok.table cfg.P.d) = mem0 (solverSelectHeapAddr tok.table cfg.P.d) ∧
      out.mem (solverSelectBlocksAddr tok.table cfg.P.d) = mem0 (solverSelectBlocksAddr tok.table cfg.P.d) ∧
      Rrep.rep root model' tok' out.mem ∧ SolverLevelMetaAt P V model' tok' out.mem ∧
      SolverLevelCapsAt vCap eCap model' tok' out.mem ∧
      (SolverLevelLayoutAt vCap eCap tok mem0 → SolverLevelLayoutAt vCap eCap tok' out.mem) ∧
      PathTreeNumericInv tok'.tree tok'.trees B_t R_t ∧
      OffTreeRecInv model' L out.mem tok'.edgeRecords B_t ∧ OffTreeRecBound model' L out.mem tok'.edgeRecords B_t ∧
      sg'.loc = sg.loc ∧ sg'.owned = sg.owned ∧ sg'.reembPot = chainReembPot pot model'.chain ∧
      SelectRegionAt G P m vCap eCap pLast sb metaBase B model' tok' sg' out.mem ∧
      SolverSelectInv G L P m 4 2 tok'.table model' (Rrep.foot root tok') (LevelMetaFoot tok') sg' out.mem ∧
      (∀ j ≤ cfg.P.d, PhiBd sg'.φ j) ∧ ZeroFrom out.mem nextHeap ∧
      (∀ a < heap, ¬ Rrep.foot root tok a → ¬ sg.owned a → out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
      (∀ a, sg'.owned a → ¬ Rrep.foot root tok' a) ∧
      cost + (Rrep.phi root tok' out.mem + K * sg'.reembPot) ≤
        (deepFixed + shiftDeepSelectFixedBound Psc.readout cfg.P.d L) +
          (deepToolMul + shiftDeepSelectToolMulBound cfg.P.d L capExp M₀ cfg.N₀ B.slot K) *
            (model'.chain.totalRuntime - model.chain.totalRuntime) +
          treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
          (Rrep.phi root tok mem0 + K * sg.reembPot) := by
  intro Rrep model' M₀
  let d := cfg.P.d
  let i0 := i.val
  let C := model.chain.toTreeChain
  let C' := model'.chain.toTreeChain
  let loc := sg.loc
  have hdPos : 0 < d := by omega
  obtain ⟨hreg, hcap, hBd, hBv, hBe, hBLk, hOwnEq, hhb0, hBlk0, hmloc0, htab0, hblk0, hMatch0,
    hPot0, hCoreLen0, G₀, σ, σ_mwu, γ_ℓ, γ_c, hModOld⟩ := hRegAt0
  have hsbLeMeta : sb ≤ metaBase := by
    have h1 := hreg.1; have h2 := hreg.2.1; have h3 := hreg.2.2.1; have h4 := sg.loc.endAddr_eq; omega
  have hMetaEnd : metaBase + selectLevelMetaSize B.d = B.base := hreg.2.2.2.1.symm
  have hBaseLeEnd : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
  have hsbLtEnd : sb < B.endAddr := by
    have h1 := hreg.1; have h2 := hreg.2.1; have h3 := hreg.2.2.1
    have h4 : sg.loc.hb < sg.loc.endAddr := by
      rw [sg.loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega
    omega
  have hLocLk : loc.Lk = L := hreg.2.2.2.2.2.1.trans hBLk
  -- Prefix agreement
  obtain ⟨hPrefG, hPrefLSF, hPrefS, hPrefEmb, hPrefCore, hgEq, hℓEq, hPrefLen, hPrefPot⟩ :=
    shiftDeep_prefix_agree model i hiLt
  -- Step 1: call `deepProc [root, i0, heap]`
  obtain ⟨bDeep, hbDeep, hDeepRun⟩ := hDeepSpec
  obtain ⟨sc0, cDeep, st0, tok0, hrDeep, hsc0Lo, hsc0Hi, hlev0, hint0, htab0Eq, hrec0,
      hhb0', hBlk0', hRep0', hMeta0', hCaps0', hLay0', hNum0', hOffInv0', hOffBd0', hz0,
      hFr0, hFt0, hCostDeep⟩ :=
    hDeepRun root heap pos i ω mem0 mem model tok B_t R_t hiLt hRep0 hMeta0 hCaps0 hMemEq hSched'
      hNum0 hOffInv0 hOffBd0 hCapFacts hBranLt hModelInv hModelK hIntCapLe hForestCap hLogW hCapT
      hFootLt hzHeap (by omega)
  have hCapsInv0' : SolverLevelCapsInv P V vCap eCap model' tok0 st0.mem := ⟨hMeta0', hCaps0'⟩
  -- `[sb, B.endAddr)` is untouched by `mem vs mem0` and by `deepProc`, and disjoint from `Rrep.foot root tok0`
  have hOwnOfTag0 := hRep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRegEq0 : ∀ a, sb ≤ a → a < B.endAddr → st0.mem a = mem0 a := fun a h1 h2 => by
    have hnf := hOwnDisj0 a h1 h2
    have htag0 : tok.tag a = 0 := by by_contra hne; exact hnf (Or.inl (hOwnOfTag0 a hne))
    exact (hFr0 a (by omega) hnf).trans (hMemEq a (by omega))
  have hFootDisj0 : ∀ a, sb ≤ a → a < B.endAddr → ¬ Rrep.foot root tok0 a := fun a h1 h2 ha =>
    (hFt0 a ha).elim (hOwnDisj0 a h1 h2) (fun hnew => by omega)
  have hFootSc0 : ∀ a, Rrep.foot root tok0 a → a < sc0 := fun a ha =>
    (hFt0 a ha).elim (fun h0 => lt_of_lt_of_le (hFootLt a h0) hsc0Lo) (fun hnew => hnew.2)
  have hTab0Old : SelectMetaTableAt st0.mem (selectMlocOf B metaBase (solverLevelG tok mem0) pLast) :=
    htab0.of_agree fun a ha1 ha2 => hRegEq0 a (by simp only [selectMlocOf] at ha1; omega)
      (by simp only [selectMlocOf] at ha2; omega)
  have hBlk0Old : SelBlocksDataAt st0.mem B P (SelBlocksData.ofChain C B.d model.chain.g model.chain.ℓ sg.φ) pLast :=
    (selectBlocksAt_iff_data.mp hblk0).of_agree fun a ha1 ha2 => hRegEq0 a (by omega) ha2
  have hMatch0' : SelectHeapMatchesChain st0.mem loc 4 P C model.chain.g model.chain.ℓ sg.size :=
    hMatch0.of_agree fun a ha1 ha2 => hRegEq0 a (by have := hreg.1; omega) (by have := hreg.2.1; have := hreg.2.2.1; omega)
  have hNewVcapCard : ∀ j ≤ d, (model'.chain.G j).n ≤ vCap := fun j hj =>
    (Finset.card_le_card fun v hv => Finset.mem_range.mpr (hNewVcap j hj v hv)).trans (by simp)
  have hNewEcapCard : ∀ j ≤ d, (model'.chain.G j).m ≤ eCap := fun j hj =>
    (Finset.card_le_card fun e he => Finset.mem_range.mpr (hNewEcap j hj e he)).trans (by simp)
  have hSpBound0 := shiftDeepSelectSpace_le_bound (capExp := capExp) (evalSpace := evalSpace)
    hTP hγk hiLt hModelK hModOld hModNew hMatch0' hOldEcap hNewEcapCard hNewVcapCard hLocLk
  -- Word bounds and header reads from `st0.mem`
  have hOwnOfTag0' := hRep0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hT1_0 := hRep0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hT2_0 := hRep0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hT3_0 := hRep0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hT4_0 := hRep0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRootDir0 := hRep0'.1
  have hInitPar0 := hRep0'.2.2.2.1
  have hRootLt : root + 16 ≤ sc0 := by
    have := hFootSc0 (root + 15) (Or.inl (hOwnOfTag0' _ (by rw [hT1_0 15 (by omega)]; decide))); omega
  have hHndLt : tok0.handle + 18 ≤ sc0 := by
    have := hFootSc0 (tok0.handle + 17) (Or.inl (hOwnOfTag0' _ (by rw [hT2_0 17 (by omega)]; decide))); omega
  have hLvlMetaDisj :
      solverLevelMetaAddr tok0.table d + 2 * d ≤ metaBase ∨
      metaBase + selectLevelMetaSize B.d ≤ solverLevelMetaAddr tok0.table d := by
    have hD := interval_disj_region (a := solverLevelMetaAddr tok0.table d) (len := 2 * d)
      (by omega) hsbLtEnd fun x hx1 hx2 hx => by
        have htg := hCapsInv0'.1.2.2.2.2.1 (x - solverLevelMetaAddr tok0.table d) (by omega)
        have hax : solverLevelMetaAddr tok0.table d + (x - solverLevelMetaAddr tok0.table d) = x := by omega
        rw [hax] at htg
        exact hFootDisj0 x hx1 hx2 (Or.inl (hOwnOfTag0' x (by omega)))
    rcases hD with h1 | h2
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hLvlMetaEndSc : solverLevelMetaAddr tok0.table d + 2 * d + 1 ≤ sc0 := by
    have htg : tok0.tag (solverSelectHeapAddr tok0.table d) = 21 + d := hCapsInv0'.1.1.2.2.1
    have haddr : solverSelectHeapAddr tok0.table d = solverLevelMetaAddr tok0.table d + 2 * d := by
      unfold solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega
    have hlt := hFootSc0 (solverSelectHeapAddr tok0.table d) (Or.inl (hOwnOfTag0' _ (by rw [htg]; omega)))
    omega
  have hBlkCellSc : solverSelectBlocksAddr tok0.table d < sc0 := by
    have htg : tok0.tag (solverSelectBlocksAddr tok0.table d) = 21 + d := hCapsInv0'.1.1.2.2.2
    exact hFootSc0 _ (Or.inl (hOwnOfTag0' _ (by rw [htg]; omega)))
  have hReadHnd : st0.mem root = tok0.handle := by simpa using hRootDir0 0 (by simp)
  have hReadTab : st0.mem (root + 1) = tok0.table := by simpa using hRootDir0 1 (by simp)
  have hReadD : st0.mem (tok0.handle + 11) = d := by simpa [Nat.add_assoc] using hInitPar0 2 (by simp)
  have hReadSb : st0.mem (solverSelectHeapAddr tok0.table d) = sb := by rw [htab0Eq, hhb0', hhb0]
  have hReadBlk : st0.mem (solverSelectBlocksAddr tok0.table d) = B.base := by rw [htab0Eq, hBlk0', hBlk0]
  have hReadMeta : st0.mem (sb + 13) = metaBase := by
    have h13 := hMatch0'.1.1 13 (by simp); rw [hreg.1] at h13; exact h13.trans hreg.2.2.1.symm
  have hReadL : st0.mem (sb + 3) = L := by
    have h3 := hMatch0'.1.1 3 (by simp); rw [hreg.1] at h3; exact h3.trans hLocLk
  have hReadVCap : st0.mem (metaBase + 2 + (d + 1)) = vCap := by
    simpa [smEntryAddr, smTableOff, selectMlocOf, hBd, hBv] using (hTab0Old.2.2 0 (Nat.zero_le _)).2.1
  have hReadECap : st0.mem (metaBase + 2 + 2 * (d + 1)) = eCap := by
    simpa [smEntryAddr, smTableOff, selectMlocOf, hBd, hBe] using (hTab0Old.2.2 0 (Nat.zero_le _)).2.2.1
  have hReadPLast : st0.mem (metaBase + 2 + 7 * (d + 1) + d) = pLast := by
    simpa [smEntryAddr, smTableOff, selectMlocOf, hBd, d] using
      (hTab0Old.2.2 d (by simp only [selectMlocOf, hBd]; exact le_rfl)).2.2.2.2.2.2.2
  have hReadEmb0 : st0.mem (metaBase + 2 + 5 * (d + 1)) = B.embPtr 0 := by
    simpa [smEntryAddr, smTableOff, selectMlocOf, hBd] using (hTab0Old.2.2 0 (Nat.zero_le _)).2.2.2.2.2.1
  have hReadF1 : st0.mem (metaBase + 2 + 6 * (d + 1) + 1) = B.fPtr 1 := by
    simpa [smEntryAddr, smTableOff, selectMlocOf, hBd] using
      (hTab0Old.2.2 1 (by simp only [selectMlocOf, hBd]; omega)).2.2.2.2.2.2.1
  have hSlotEq : ((B.fPtr 1 - B.embPtr 0) - eCap) / eCap = B.slot := by
    rw [← hBe]; exact slot_div_formula (hBe.symm ▸ heCapPos)
  have hF1LeEnd : B.fPtr 1 ≤ B.endAddr := by
    have h1 := B.blk_le_last (j := 1) (by rw [hBd]; omega)
    have h2 : B.lastGPtr ≤ B.endAddr := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
    omega
  have hEmb0LeF1 : B.embPtr 0 + eCap ≤ B.fPtr 1 := by
    rw [← hBe]; unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr
      SelectBlocksLoc.fPtr SelectBlocksLoc.levelSize; simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero]; omega
  have hvCapW : vCap < 2 ^ w := by
    have h1 := B.endAddr_eq; unfold selectBlocksSize dynGraphSize at h1; rw [hBv] at h1; omega
  have heCapW : eCap < 2 ^ w := by
    have h1 := B.endAddr_eq; unfold selectBlocksSize dynGraphSize at h1; rw [hBe] at h1; omega
  -- Step 2: `selTableWrite` refreshing `[metaBase, metaBase + selectLevelMetaSize B.d)`
  have hLvlMetaDisjD : solverLevelMetaAddr tok0.table d + 2 * d ≤ metaBase ∨
      metaBase + selectLevelMetaSize d ≤ solverLevelMetaAddr tok0.table d := by
    rwa [hBd] at hLvlMetaDisj
  have hTablePre : (selTableWriteContract w B metaBase (solverLevelMetaAddr tok0.table d) pLast).pre
      [metaBase, B.base, d, vCap, eCap, L, B.slot, solverLevelMetaAddr tok0.table d, pLast] st0.mem :=
    ⟨by rw [hBd, hBv, hBe, hBLk], hw16, by omega, by omega, by rw [hBd]; omega,
      by rw [hBd]; exact hLvlMetaDisjD⟩
  obtain ⟨bTW, hbTW, oTW, stTW, cTW, hrTW, hpTW, hcTW⟩ :=
    hTableWrite (solverLevelMetaAddr tok0.table d)
      [metaBase, B.base, d, vCap, eCap, L, B.slot, solverLevelMetaAddr tok0.table d, pLast]
      st0.mem st0.pos ω
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro v (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
          all_goals first | exact hLkW | exact hpLastW | exact hSlotW | exact hvCapW | exact heCapW | omega)
      hTablePre
  obtain ⟨hTWret, hTabTW_raw, hFrTW⟩ := hpTW
  have hTabTW : SelectMetaTableAt stTW.mem (selectMlocOf B metaBase (solverLevelG tok0 stTW.mem) pLast) := by
    have hEq : selTableOf B metaBase (solverLevelMetaAddr tok0.table d) pLast st0.mem =
        selectMlocOf B metaBase (solverLevelG tok0 stTW.mem) pLast := by
      unfold selTableOf selectMlocOf
      have hBdeq : B.d = d := hBd
      have hg : (fun j => if j < B.d then st0.mem (solverLevelMetaAddr tok0.table d + B.d + j) else B.lastGPtr) =
          (fun j => if j < B.d then solverLevelG tok0 stTW.mem j else B.lastGPtr) := by
        funext j; split_ifs with hj
        · unfold solverLevelG; rw [hBdeq] at hj ⊢
          symm; refine hFrTW _ ?_
          rcases hLvlMetaDisjD with h1 | h2
          · dsimp only [d] at h1; exact Or.inl (by omega)
          · dsimp only [d] at h2; exact Or.inr (by rw [hBd]; omega)
        · rfl
      have hs : (fun j => if j + 1 < B.d then st0.mem (solverLevelMetaAddr tok0.table d + B.d + (j + 1))
            else if j < B.d then B.lastGPtr else pLast) =
          (fun j => if j + 1 < B.d then solverLevelG tok0 stTW.mem (j + 1)
            else if j < B.d then B.lastGPtr else pLast) := by
        funext j; split_ifs with hj2
        · unfold solverLevelG; rw [hBdeq] at hj2 ⊢
          symm; refine hFrTW _ ?_
          rcases hLvlMetaDisjD with h1 | h2
          · dsimp only [d] at h1; exact Or.inl (by omega)
          · dsimp only [d] at h2; exact Or.inr (by rw [hBd]; omega)
        · rfl
        · rfl
      exact congrArg₂ (fun gp sp =>
        ({ metaBase := metaBase, d := B.d, Lk := B.Lk, g0Ptr := B.g0Ptr, GPtr := gp,
           vCap := fun _ => B.vCap, eCap := fun _ => B.eCap, phiPtr := B.phiPtr,
           coreLenPtr := B.lenPtr, embPtr := B.embPtr, fPtr := B.fPtr, sPtr := sp,
           pLast := pLast } : SelectLevelMetaLoc)) hg hs
    rwa [hEq] at hTabTW_raw
  have hFrTW_offReg : ∀ a, (a < sb ∨ B.endAddr ≤ a) → stTW.mem a = st0.mem a := fun a h =>
    hFrTW a (by rcases h with h1 | h2 <;> [left; right] <;> omega)
  have hFrTW_foot : ∀ a, Rrep.foot root tok0 a → stTW.mem a = st0.mem a := fun a ha =>
    hFrTW a (by
      by_contra h; push Not at h
      exact hFootDisj0 a (by omega) (by omega) ha)
  have hLocal := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
  have hRepTW : Rrep.rep root model' tok0 stTW.mem :=
    (hLocal root model' tok0 st0.mem stTW.mem fun a ha => (hFrTW_foot a ha).symm).1 hRep0'
  have hPhiTW : Rrep.phi root tok0 stTW.mem = Rrep.phi root tok0 st0.mem :=
    ((hLocal root model' tok0 st0.mem stTW.mem fun a ha => (hFrTW_foot a ha).symm).2).symm
  have hCapsTW : SolverLevelCapsInv P V vCap eCap model' tok0 stTW.mem :=
    hCapsInv0'.preserve rfl hCapsInv0'.1.2.1
      (fun a ha => ⟨rfl, hFrTW_foot a (Or.inl (hOwnOfTag0' a (by rcases ha with h | h | h | h <;> omega)))⟩)
      (fun j hj => (SolverLevelMetaAt.atCaps hCapsInv0'.1 hCapsInv0'.2 j hj).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hHeapTW : SelectHeapAt stTW.mem loc 4 sg.size :=
    hMatch0'.1.of_agree fun a _ ha2 => hFrTW a (Or.inl (by
      have := hreg.2.1; have := hreg.2.2.1; dsimp only [loc] at ha2; omega))
  have hMatchTW : SelectHeapMatchesChain stTW.mem loc 4 P C model.chain.g model.chain.ℓ sg.size :=
    hMatch0'.of_agree fun a _ ha2 => hFrTW a (Or.inl (by
      have := hreg.2.1; have := hreg.2.2.1; dsimp only [loc] at ha2; omega))
  have hBlkTW : SelBlocksDataAt stTW.mem B P
      (SelBlocksData.ofChain C B.d model.chain.g model.chain.ℓ sg.φ) pLast :=
    hBlk0Old.of_agree fun a ha1 _ => hFrTW a (Or.inr (by omega))
  have hzTW : ZeroFrom stTW.mem sc0 := fun a ha => (hFrTW a (Or.inr (by omega))).trans (hz0 a ha)
  -- Step 3: `selectRefreshInteriorLoop_runs` starting at `cur = i0`
  have hDInit_V : ∀ j, i0 ≤ j → j < d → ∀ v ∈ (C'.activeLSF j).F.F.V, v < vCap := fun j _ hj v hv => by
    have hBr := (hModNew.1.2.2.2.2.1 j hj).1
    have hVeq : (C'.activeLSF j).F.F.V = (C'.G j).V := by
      have hHlsf := ((hModNew.1.2.2.2.2.1 j hj).2.1 (model'.chain.bran j) hBr).1
      simp only [C', ChainState.toTreeChain, TreeChain.activeLSF, show j < cfg.P.d from hj, ↓reduceIte]
      exact hHlsf.2.1.2.1
    rw [hVeq] at hv; exact hNewVcap j (le_of_lt hj) v hv
  have hDInit_E : ∀ j, i0 ≤ j → j < d → ∀ e ∈ (C'.activeLSF j).F.F.E, e < eCap := fun j hj1 hj2 e he => by
    have hact : (C'.activeLSF j).F.F = (cfg.T.lsfs (model'.chain.scState j) (model'.chain.bran j)).F.F := by
      simp [C', ChainState.toTreeChain, TreeChain.activeLSF, show j < cfg.P.d from hj2]
    rw [hact] at he
    exact hNewEcap j (le_of_lt hj2) e ((hModelK.2.2.2.2.1 j hj1 hj2).2.2.2.1 he)
  have hIntSpaceLe : sc0 + selectInitInteriorLoopSpace model'.chain i0 L capExp < 2 ^ w := by
    dsimp only [model', i0, d, loc, M₀] at hSpBound0 hsc0Hi hroom ⊢; omega
  obtain ⟨sc1, cInt, st1, tok1, hrInt, hsc1Lo, hsc1Hi, hRep1, htab1Eq, hhnd1Eq, hlev1Eq, hint1Eq,
      hrec1Eq, htree1Eq, htrees1Eq, hedg1Eq, hth1Eq, htt1Eq, hvc1Eq, hec1Eq,
      hFt1, hOwn1, hTagLt1, hTag1, hCaps1, hTab1, hHeap1, hBlk1, hz1, hFr1, hCostInt⟩ :=
    selectRefreshInteriorLoop_runs hfmt4 hfmtP hlocalCore hw16 hLkW hSlotW hkW (le_of_lt hiLt)
      hreg hBd hBv hBe hBLk hRepTW hFootSc0 hFootDisj0 (by omega) hCapsTW hTabTW
      hHeapTW hBlkTW (fun j _ hj => hModNew.2.2.2.1 j hj) (fun j _ hj => hModNew.2.2.1 j hj)
      hDInit_V hDInit_E hLenFitInt hEmbSlot hpIntLoop hpFillInt hFootAt
      (fun j _ _ vcF ecF => hDgCopy vcF ecF _ _) hCoreLen hFilter hEmbCopy hzTW hIntSpaceLe
  have hFootSc1 : ∀ a, Rrep.foot root tok1 a → a < sc1 := fun a ha => by
    rcases hFt1 a ha with h0 | hnew
    · exact lt_of_lt_of_le (hFootSc0 a h0) hsc1Lo
    · exact hnew.2
  have hFootDisj1 : ∀ a, sb ≤ a → a < B.endAddr → ¬ Rrep.foot root tok1 a := fun a h1 h2 ha => by
    rcases hFt1 a ha with h0 | hnew
    · exact hFootDisj0 a h1 h2 h0
    · omega
  -- Step 4: `op 3` on core `d - 1` (`op3_gd_disj_runs`)
  have hOp3Room : sc1 + 1 < 2 ^ w := by
    dsimp only [model', i0, d, loc, M₀] at hSpBound0 hsc0Hi hsc1Hi hroom ⊢; omega
  obtain ⟨b3, o3, st2, cOp3, tok2, hb3, hr3, hsc2Lo, hsc2Hi, hRep2, htab2Eq, hhnd2Eq, hlev2Eq,
      hint2Eq, hrec2Eq, htree2Eq, htrees2Eq, hedg2Eq, hth2Eq, htt2Eq, hvc2Eq, hec2Eq,
      hCaps2, hTab2, hHeap2, hBlk2, hGdAt2, hGdEnd2, hGdDisj2, hFr2, hFt2, hOwn2, hTagLt2,
      hTag2, hz2, hCostOp3⟩ :=
    op3_gd_disj_runs hlocalCore hkW hdPos hreg hBd hBv hBe hRep1 hFootSc1 hFootDisj1 (by omega)
      hCaps1 hModNew hTab1 hHeap1 hBlk1 (hFootAt (d - 1) (by omega) (by omega)) hz1 hOp3Room
  set sc2 := o3.value
  have hFootSc2 : ∀ a, Rrep.foot root tok2 a → a < sc2 := fun a ha => by
    rcases hFt2 a ha with h1 | hnew
    · exact lt_of_lt_of_le (hFootSc1 a h1) hsc2Lo
    · exact hnew.2
  have hFootDisj2 : ∀ a, sb ≤ a → a < B.endAddr → ¬ Rrep.foot root tok2 a := fun a h1 h2 ha => by
    rcases hFt2 a ha with h1' | hnew
    · exact hFootDisj1 a h1 h2 h1'
    · omega
  -- Step 5: `selectFillLastLevel_runs_disj`
  have hTermRep2 := hRep2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTags2 := hRep2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hOwn2' := hTags2.1
  have hT19 := hTags2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTermDisj2 : tok2.termTok ≤ B.base ∨ (B.endAddr ≤ tok2.termHandle ∧ tok2.termTok ≤ sc2) := by
    have hTermPos : tok2.termHandle < tok2.termTok := by
      have := hTermRep2.1; have := hModNew.1.2.2.2.1; omega
    have hD := interval_disj_region (a := tok2.termHandle) (len := tok2.termTok - tok2.termHandle)
      (by omega) hsbLtEnd fun x hx1 hx2 hx => by
        have hft : (LastLevelProgram.lastLevelRepresentation tok2.vcLast tok2.ecLast 4 L 0
            (model'.chain.G d).E).foot tok2.termHandle tok2.termTok x := ⟨hx.1, by omega⟩
        exact hFootDisj2 x hx1 hx2 (Or.inl (hOwn2' x (by rw [hT19 x hft]; decide)))
    have hTokLeSc2 : tok2.termTok ≤ sc2 := by
      have hft : (LastLevelProgram.lastLevelRepresentation tok2.vcLast tok2.ecLast 4 L 0
          (model'.chain.G d).E).foot tok2.termHandle tok2.termTok (tok2.termTok - 1) :=
        ⟨by omega, by omega⟩
      have hlt := hFootSc2 (tok2.termTok - 1) (Or.inl (hOwn2' _ (by rw [hT19 _ hft]; decide)))
      omega
    rcases hD with h1 | h2
    · left; omega
    · right; exact ⟨h2, hTokLeSc2⟩
  have hFdV : ∀ v ∈ (model'.chain.lastLSFs model'.chain.lastBran).F.F.V, v < B.vCap := fun v hv => by
    have hBr := hModNew.1.2.2.2.2.2.1
    have hVeq : (model'.chain.lastLSFs model'.chain.lastBran).F.F.V = (model'.chain.G d).V :=
      (hModNew.1.2.2.2.2.2.2.1 model'.chain.lastBran hBr).2.1.2.1
    rw [hVeq] at hv; rw [hBv]; exact hNewVcap d le_rfl v hv
  have hFdE : ∀ e ∈ (model'.chain.lastLSFs model'.chain.lastBran).F.F.E, e < B.eCap := fun e he => by
    rw [hBe]; exact hNewEcap d le_rfl e (hModelK.2.2.2.2.2.2.1 he)
  have hPrevLenD_val : EdgeValuesAt st2.mem (B.lenPtr (d - 1)) 4 B.Lk P (model'.chain.G d).E
      (C'.chainLen model'.chain.ℓ d) := by
    have hSubLast : (model'.chain.G d).E ⊆ (model'.chain.G (d - 1)).E := by
      have h := (hModelK.2.2.2.2.1 (d - 1) (by omega) (by omega)).2.2.2.2
      rwa [show d - 1 + 1 = d by omega] at h
    have hLenPrev := hBlk2.2.2.1 (d - 1) (by rw [hBd]; omega)
    have hcond : i.val ≤ d - 1 ∧ d - 1 < cfg.P.d := ⟨by omega, by omega⟩
    have hltBd : d - 1 < B.d := by rw [hBd]; omega
    simp only [hcond, and_self, ↓reduceIte, show d - 1 + 1 = d by omega] at hLenPrev
    intro e he
    have hpr := hLenPrev.2 e (hSubLast he)
    simp only [coreLenPrec, hltBd, ↓reduceIte] at hpr
    exact hpr
  have hPrevD_le_lenD : B.lenPtr (d - 1) + B.eCap * B.Lk ≤ B.fPtr B.d := by
    have h1 := B.blk_le_of_lt (j := d - 1) (j' := B.d) (by rw [hBd]; omega)
    unfold SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr
    unfold SelectBlocksLoc.levelSize at h1
    omega
  have hPrevD_le_last : B.lenPtr (d - 1) + B.eCap * B.Lk ≤ B.lastGPtr := by
    have h1 := B.blk_le_last (j := d - 1) (by rw [hBd]; omega)
    unfold SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr
    unfold SelectBlocksLoc.levelSize at h1
    omega
  have hPrevD_le_sc2 : B.lenPtr (d - 1) + B.eCap * B.Lk ≤ sc2 := by
    have h1 : B.lastGPtr ≤ B.endAddr := by unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
    omega
  have hPrevD_le_lenBD : B.lenPtr (d - 1) + B.eCap * B.Lk ≤ B.lenPtr B.d := by
    have h1 : B.fPtr B.d ≤ B.lenPtr B.d := by unfold SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr; omega
    omega
  have hLastSpW : sc2 + selectFillLastLevelSpace (model'.chain.G d).m
      (model'.chain.lastLSFs model'.chain.lastBran).F.F.m B.Lk < 2 ^ w := by
    rw [hBLk]; dsimp only [model', i0, d, loc, M₀] at hSpBound0 hsc0Hi hsc1Hi hsc2Hi hroom ⊢; omega
  have hTermRep2B : (LastLevelProgram.lastLevelRepresentation tok2.vcLast tok2.ecLast 4 B.Lk P
      (model'.chain.G d).E).rep tok2.termHandle (model'.chain.lastK, model'.chain.lastLSFs)
      tok2.termTok st2.mem := by rw [hBLk]; exact hTermRep2
  obtain ⟨sc3, cLast, st3, hrLast, hsc3Eq, hBlk3, hz3, hFr3, hCostLast⟩ :=
    selectFillLastLevel_runs_disj (termBran := model'.chain.lastBran)
      hw16 hpLastW (hBLk.symm ▸ hLkW) hTab2 hBlk2
      (by omega) (by omega) hGdAt2 hGdDisj2
      (by omega) (fun v hv => hBv ▸ hNewVcap d le_rfl v hv) (fun e he => hBe ▸ hNewEcap d le_rfl e he)
      hTermRep2B hModNew.1.2.2.2.2.2.1 hTermDisj2 hFdV hFdE
      hPrevD_le_sc2 (Or.inl hPrevD_le_lenBD)
      (Or.inl hPrevD_le_lenD) (Or.inl hPrevD_le_last) hPrevLenD_val
      (fun e he => by
        have hF := hLenFitLast e he
        refine ⟨hBLk.symm ▸ hF.1 (B.lenPtr (d - 1)) st2.mem (hBLk ▸ hPrevLenD_val), ?_⟩
        obtain ⟨q, hq1, hq2⟩ := hF.2
        refine ⟨q, hBLk.symm ▸ hq1, ?_⟩
        rw [hq2]
        have hactD : C'.activeLSF cfg.P.d = model'.chain.lastLSFs model'.chain.lastBran := by
          simp [C', TreeChain.activeLSF, ChainState.toTreeChain]
        change (C'.activeLSF cfg.P.d).wstr e * C'.chainLen model'.chain.ℓ cfg.P.d e = _
        rw [hactD])
      (by rw [hBv, hBe]; exact hDgCopy vCap eCap _ _)
      (by rw [hBv, hBe]; exact hDgCopy tok2.vcLast tok2.ecLast _ _)
      (hBe ▸ hCoreLen) hz2 hLastSpW
  have hBaseLeLast : B.base ≤ B.lastGPtr := by
    have := B.blk_le_last (j := 0) (Nat.zero_le _); unfold SelectBlocksLoc.fPtr at this; omega
  have hLastEndAddr : B.lastGPtr + dynGraphSize B.vCap B.eCap ≤ B.endAddr := by
    unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  have hFr3_offBlk : ∀ a < sc2, (a < B.base ∨ B.endAddr ≤ a) → st3.mem a = st2.mem a := fun a ha h =>
    hFr3 a ha
      (by unfold SelectBlocksLoc.regLast SelectBlocksLoc.g0Ptr; rcases h with h1 | h2 <;> omega)
      (by unfold SelectBlocksLoc.regF SelectBlocksLoc.phiPtr
          have h1 := B.blk_le_last (j := B.d) le_rfl
          have h2 : B.base ≤ B.fPtr B.d := by unfold SelectBlocksLoc.fPtr; omega
          unfold SelectBlocksLoc.levelSize at h1
          rcases h with h3 | h4 <;> omega)
      (by unfold SelectBlocksLoc.regLen SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr
            SelectBlocksLoc.phiPtr
          have h1 := B.blk_le_last (j := B.d) le_rfl
          have h2 : B.base ≤ B.fPtr B.d := by unfold SelectBlocksLoc.fPtr; omega
          unfold SelectBlocksLoc.levelSize at h1
          rcases h with h3 | h4 <;> omega)
  have hFr3_foot : ∀ a, Rrep.foot root tok2 a → st3.mem a = st2.mem a := fun a ha =>
    hFr3_offBlk a (hFootSc2 a ha) (by
      by_contra h; push Not at h
      exact hFootDisj2 a (by omega) (by omega) ha)
  have hRep3 : Rrep.rep root model' tok2 st3.mem :=
    (hLocal root model' tok2 st2.mem st3.mem fun a ha => (hFr3_foot a ha).symm).1 hRep2
  have hPhi3 : Rrep.phi root tok2 st3.mem = Rrep.phi root tok2 st2.mem :=
    ((hLocal root model' tok2 st2.mem st3.mem fun a ha => (hFr3_foot a ha).symm).2).symm
  have hCaps3 : SolverLevelCapsInv P V vCap eCap model' tok2 st3.mem :=
    hCaps2.preserve rfl hCaps2.1.2.1
      (fun a ha => ⟨rfl, hFr3_foot a (Or.inl (hOwn2' a (by rcases ha with h | h | h | h <;> omega)))⟩)
      (fun j hj => (SolverLevelMetaAt.atCaps hCaps2.1 hCaps2.2 j hj).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hMlocEq3 : selectMlocOf B metaBase (solverLevelG tok2 st3.mem) pLast =
      selectMlocOf B metaBase (solverLevelG tok2 st2.mem) pLast := by
    have hEq : ∀ j < B.d, solverLevelG tok2 st3.mem j = solverLevelG tok2 st2.mem j := fun j hj => by
      rw [hBd] at hj
      have htg : tok2.tag (solverLevelMetaAddr tok2.table cfg.P.d + cfg.P.d + j) = 22 + cfg.P.d := by
        simpa [Nat.add_assoc] using hCaps2.1.2.2.2.2.1 (cfg.P.d + j) (by omega)
      exact hFr3_foot _ (Or.inl (hOwn2' _ (by rw [htg]; omega)))
    unfold selectMlocOf
    congr 1
    · funext j; split_ifs with hj; exact hEq j hj; rfl
    · funext j; split_ifs with hj2; exact hEq (j + 1) hj2; rfl; rfl
  have hTab3 : SelectMetaTableAt st3.mem (selectMlocOf B metaBase (solverLevelG tok2 st3.mem) pLast) := by
    rw [hMlocEq3]
    exact hTab2.of_agree fun a _ ha2 => hFr3_offBlk a (by simp only [selectMlocOf] at ha2; omega)
      (Or.inl (by simp only [selectMlocOf] at ha2; omega))
  -- Heap still matches `model` on `st3.mem` (untouched since `st0`)
  have hHeapEq_0_to_3 : ∀ a, loc.hb ≤ a → a < loc.endAddr → st3.mem a = st0.mem a := fun a h1 h2 => by
    dsimp only [loc] at h1 h2
    have hltBase : a < B.base := by have := hreg.2.1; have := hreg.2.2.1; omega
    have h32 : st3.mem a = st2.mem a := hFr3_offBlk a (by omega) (Or.inl hltBase)
    have h21 : st2.mem a = st1.mem a :=
      hFr2 a (by omega) (fun hc => hFootDisj1 a (by have := hreg.1; omega) (by omega) (Or.inr (Or.inr ⟨d - 1, by omega, hc⟩)))
    have h1TW : st1.mem a = stTW.mem a :=
      hFr1 a (by omega) (by omega) fun ⟨j, _, hj2, hc⟩ =>
        hFootDisj0 a (by have := hreg.1; omega) (by omega) (Or.inr (Or.inr ⟨j, hj2, hc⟩))
    have hTW0 : stTW.mem a = st0.mem a := hFrTW a (Or.inl (by have := hreg.2.1; have := hreg.2.2.1; omega))
    exact ((h32.trans h21).trans h1TW).trans hTW0
  have hMatch3 : SelectHeapMatchesChain st3.mem loc 4 P C model.chain.g model.chain.ℓ sg.size :=
    hMatch0'.of_agree hHeapEq_0_to_3
  have ⟨hFinSpEq, hFinCostEq⟩ := selectRefreshFinalize_congr_mem (C := C') (cur := i0) (L := L)
    (evalSpace := evalSpace) (evalCost := evalCost) hHeapEq_0_to_3
  -- Step 6: `selectDeepFinalize_runs` starting at `cur = i0`
  have hTagOwn3 : ∀ a, tok0.tag a ≠ 0 → (∀ j < d, tok0.tag a ≠ 21 + j) → st3.mem a = st0.mem a := by
    intro a hne hnotC
    have hlt0 : a < sc0 := hFootSc0 a (Or.inl (hOwnOfTag0' a hne))
    have hnotReg : ¬ (sb ≤ a ∧ a < B.endAddr) := fun h => hFootDisj0 a h.1 h.2 (Or.inl (hOwnOfTag0' a hne))
    have hnotBlk : ¬ (B.base ≤ a ∧ a < B.endAddr) := fun h => hnotReg ⟨by omega, h.2⟩
    have h32 : st3.mem a = st2.mem a :=
      hFr3_offBlk a (by omega) (by by_contra h; push Not at h; exact hnotBlk h)
    have hTags1 := hRep1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hTags0 := hRep0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hT21_1 := hTags1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hT21_0 := hTags0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have h21 : st2.mem a = st1.mem a :=
      hFr2 a (by omega) (fun hc => by
        have ht1 := hT21_1 (d - 1) (by omega) a hc
        have ht0 := hTag1 a hne
        have := hnotC (d - 1) (by omega); omega)
    have h1TW : st1.mem a = stTW.mem a :=
      hFr1 a hlt0 hnotBlk fun ⟨j, _, hj2, hc⟩ => by
        have ht0 := hT21_0 j hj2 a hc
        exact hnotC j hj2 ht0
    have hTW0 : stTW.mem a = st0.mem a := hFrTW_offReg a (by by_contra h; push Not at h; exact hnotReg h)
    exact ((h32.trans h21).trans h1TW).trans hTW0
  have hhbRd3 : st3.mem (solverSelectHeapAddr tok2.table d) = sb := by
    rw [htab2Eq, htab1Eq]
    have htg : tok0.tag (solverSelectHeapAddr tok0.table d) = 21 + d := hCapsInv0'.1.1.2.2.1
    exact (hTagOwn3 _ (by rw [htg]; omega) (fun j hj => by rw [htg]; omega)).trans hReadSb
  have hBlkRd3 : st3.mem (solverSelectBlocksAddr tok2.table d) = B.base := by
    rw [htab2Eq, htab1Eq]
    have htg : tok0.tag (solverSelectBlocksAddr tok0.table d) = 21 + d := hCapsInv0'.1.1.2.2.2
    exact (hTagOwn3 _ (by rw [htg]; omega) (fun j hj => by rw [htg]; omega)).trans hReadBlk
  -- Extract `hF3`, `hLen3`, `hEmb3`, `hLastG3`, `hG0_3`, `hPhiPref3` from `hBlk3`
  have hF3 : ∀ j ≤ d, SelPartF st3.mem B j (C'.activeLSF j).F.F := fun j hj => by
    by_cases hjd : j = d
    · subst hjd
      have h := hBlk3.1 B.d le_rfl; dsimp only at h; simp only [Function.update_self] at h
      rw [hBd] at h; simpa [C', ChainState.toTreeChain, TreeChain.activeLSF, d] using h
    · have h := hBlk3.1 j (by rw [hBd]; omega); dsimp only at h
      have hjLt : j < cfg.P.d := by omega
      rw [Function.update_of_ne (by rw [hBd]; omega)] at h
      by_cases hji : i.val ≤ j
      · simp only [hji, hjLt, and_self, ↓reduceIte] at h; exact h
      · simp only [hji, false_and, ↓reduceIte, SelBlocksData.ofChain] at h; rwa [hPrefLSF j (by omega)]
  have hLen3 : ∀ j ≤ d, SelPartLen st3.mem B P j (C'.G j).E (C'.chainLen model'.chain.ℓ (j + 1)) pLast := fun j hj => by
    by_cases hjd : j = d
    · subst hjd
      have h := hBlk3.2.2.1 B.d le_rfl; dsimp only at h; simp only [Function.update_self] at h
      rw [hBd] at h
      have heq : (fun e => (model'.chain.lastLSFs model'.chain.lastBran).wstr e * C'.chainLen model'.chain.ℓ d e) =
          C'.chainLen model'.chain.ℓ (d + 1) := funext fun e => by
        have hactD : C'.activeLSF cfg.P.d = model'.chain.lastLSFs model'.chain.lastBran := by
          simp [C', TreeChain.activeLSF, ChainState.toTreeChain]
        change (model'.chain.lastLSFs model'.chain.lastBran).wstr e * C'.chainLen model'.chain.ℓ cfg.P.d e =
          (C'.activeLSF cfg.P.d).wstr e * C'.chainLen model'.chain.ℓ cfg.P.d e
        rw [hactD]
      rwa [heq] at h
    · have h := hBlk3.2.2.1 j (by rw [hBd]; omega); dsimp only at h
      have hjLt : j < cfg.P.d := by omega
      rw [Function.update_of_ne (by rw [hBd]; omega), Function.update_of_ne (by rw [hBd]; omega)] at h
      by_cases hji : i.val ≤ j
      · simp only [hji, hjLt, and_self, ↓reduceIte] at h; exact h
      · simp only [hji, false_and, ↓reduceIte, SelBlocksData.ofChain] at h
        rw [hPrefG j (by omega), hPrefLen (j + 1) (by omega)]; exact h
  have hEmb3 : ∀ j < d, SelPartEmb st3.mem B j (C'.activeCore j).E (C'.activeEmb j) := fun j hj => by
    have h := hBlk3.2.2.2.1 j (by rw [hBd]; omega); dsimp only at h
    have hjLt : j < cfg.P.d := hj
    by_cases hji : i.val ≤ j
    · simp only [hji, hjLt, and_self, ↓reduceIte] at h; exact h
    · simp only [hji, false_and, ↓reduceIte, SelBlocksData.ofChain] at h
      rw [hPrefCore j (by omega), hPrefEmb j (by omega)]; exact h
  have hLastG3 : SelPartLast st3.mem B (C'.G d) := hBlk3.2.2.2.2.1
  have hG0_3 : SelPartG0 st3.mem B P (C'.G 0).E model'.chain.g := by
    rw [hPrefG 0 (Nat.zero_le _), funext hgEq]; exact hBlk3.2.2.2.2.2
  have hPhiPref3 : ∀ j < i0, SelPartPhi st3.mem B P j (C'.G j).V (sg.φ j) := fun j hj => by
    rw [hPrefG j (le_of_lt hj)]; exact hBlk3.2.1 j (by rw [hBd]; omega)
  have hFinRoom : sc3 + selectRefreshFinalizeSpace st3.mem loc C' i0 L evalSpace < 2 ^ w := by
    rw [hFinSpEq, hsc3Eq, hBLk]
    dsimp only [sc2, C', model', i0, d, loc, M₀] at hSpBound0 hsc0Hi hsc1Hi hsc2Hi hroom ⊢; omega
  obtain ⟨sc4, cFin, st4, sg', hrFin, hsc4Lo, hsc4Hi, hz4, hsgLoc, hsgOwn, hsgPot,
      hRep4, hPhi4, hCaps4, hRegAt4, hPhiBd4, hFr4, hCostFin⟩ :=
    selectDeepFinalize_runs hlocalCore hw16 hw10 hLkW hpLastW (le_of_lt hiLt) hreg hcap
      hBd hBv hBe hBLk hRep3
      (fun a ha => lt_of_lt_of_le (hFootSc2 a ha) (by rw [hsc3Eq]; dsimp only [sc2]; omega))
      hFootDisj2 hhbRd3 hBlkRd3 hCaps3 hModOld hModNew
      (fun j hj => hPrefG j (le_of_lt hj)) hPrefLSF hPrefS hPrefEmb hgEq hℓEq
      hMatch3 hPhiPref3 (fun j hj => hPrefPot sg.φ j hj (hPot0 j (by change j ≤ cfg.P.d; omega)))
      hPhiBdPref hPhiBdStep
      hTab3 hF3 hLen3 hEmb3 hLastG3 hG0_3 hNewVcap hNewEcapHeap hFitPhi
      hpPhiLoop (hPhiFill (solverLevelG tok2 st3.mem))
      hpRebSuf (hRebLvl (solverLevelG tok2 st3.mem))
      (by rw [hsc3Eq]; omega) hz3 hFinRoom
  -- Stitch the Word-RAM execution of `shiftDeepSelectBody`
  have hFootFinal : ∀ a, Rrep.foot root tok2 a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < sc4) := fun a ha => by
    rcases hFt2 a ha with h1 | hnew2
    · rcases hFt1 a h1 with h0 | hnew1
      · rcases hFt0 a h0 with hinit | hnew0
        · exact Or.inl hinit
        · exact Or.inr ⟨hnew0.1, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hFrFinal : ∀ a < heap, ¬ Rrep.foot root tok a → ¬ sg.owned a → st4.mem a = mem a := by
    intro a ha hnf hno; rw [hOwnEq] at hno
    have hoff : a < sb ∨ B.endAddr ≤ a := by by_contra h; push Not at h; exact hno h
    have h43 : st4.mem a = st3.mem a := hFr4 a (by rw [hsc3Eq]; omega) hoff
    have h32 : st3.mem a = st2.mem a := hFr3_offBlk a (by omega) (by rcases hoff with h1 | h2 <;> [left; right] <;> omega)
    have hnotF0 : ¬ Rrep.foot root tok0 a := fun hf0 => by rcases hFt0 a hf0 with h0 | hnew; exact hnf h0; omega
    have hnotF1 : ¬ Rrep.foot root tok1 a := fun hf1 => by rcases hFt1 a hf1 with h0 | hnew; exact hnotF0 h0; omega
    have h21 : st2.mem a = st1.mem a := hFr2 a (by omega) fun hc => hnotF1 (Or.inr (Or.inr ⟨d - 1, by omega, hc⟩))
    have h1TW : st1.mem a = stTW.mem a :=
      hFr1 a (by omega) (by rcases hoff with h1 | h2 <;> omega) fun ⟨j, _, hj2, hc⟩ => hnotF0 (Or.inr (Or.inr ⟨j, hj2, hc⟩))
    exact ((((h43.trans h32).trans h21).trans h1TW).trans (hFrTW_offReg a hoff)).trans (hFr0 a ha hnf)
  have hTagOwn4 : ∀ a, tok0.tag a ≠ 0 → (∀ j < d, tok0.tag a ≠ 21 + j) → st4.mem a = st0.mem a := by
    intro a hne hnotC
    have hlt0 : a < sc0 := hFootSc0 a (Or.inl (hOwnOfTag0' a hne))
    have hnotReg : ¬ (sb ≤ a ∧ a < B.endAddr) := fun h => hFootDisj0 a h.1 h.2 (Or.inl (hOwnOfTag0' a hne))
    exact (hFr4 a (by rw [hsc3Eq]; omega) (by by_contra h; push Not at h; exact hnotReg h)).trans (hTagOwn3 a hne hnotC)
  obtain ⟨hOffInv4', hOffBd4'⟩ := offTreeRec_preserve_nonCore hRep0' hOffInv0' hOffBd0' hTagOwn4
  have hOffInv4 : OffTreeRecInv model' L st4.mem tok2.edgeRecords B_t := hedg2Eq ▸ hedg1Eq ▸ hOffInv4'
  have hOffBd4 : OffTreeRecBound model' L st4.mem tok2.edgeRecords B_t := hedg2Eq ▸ hedg1Eq ▸ hOffBd4'
  have hLvlMetaEq : tok0.table + 2 * d + 2 = solverLevelMetaAddr tok0.table d := by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega
  have hSbAddrEq : tok0.table + 4 * d + 2 = solverSelectHeapAddr tok0.table d := by unfold solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega
  have hBlkAddrEq : tok0.table + 4 * d + 3 = solverSelectBlocksAddr tok0.table d := by unfold solverSelectBlocksAddr solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega
  have hLvlTabEnd0 : tok0.handle + 18 + 2 * (d + 1) ≤ sc0 := by
    have h := hT4_0 (2 * d + 1) (by omega); have := hFootSc0 _ (Or.inl (hOwnOfTag0' _ (by rw [h]; decide))); omega
  have hReadCoreLast : st1.mem (tok0.handle + 18 + (d - 1)) = tok1.coreHandle (d - 1) := by
    have h := (hRep1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (d - 1) (by omega)).1; rwa [hhnd1Eq] at h
  have hReadBranLast : st1.mem (tok0.handle + 18 + (d + 1) + (d - 1)) = model'.chain.bran (d - 1) := by
    have h := (hRep1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (d - 1) (by omega)).2.1; rwa [hhnd1Eq] at h
  have hReadTermH : st2.mem (tok0.handle + 18 + d) = tok2.termHandle := by
    have h := hRep2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; rwa [hhnd2Eq, hhnd1Eq] at h
  have hReadTermB : st2.mem (tok0.handle + 18 + (d + 1) + d) = model'.chain.lastBran := by
    have h := hRep2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; rwa [hhnd2Eq, hhnd1Eq] at h
  have hReadPrevLenD : st2.mem (metaBase + 2 + 4 * (d + 1) + (d - 1)) = B.lenPtr (d - 1) := by
    simpa [smEntryAddr, smTableOff, selectMlocOf, hBd] using
      (hTab2.2.2 (d - 1) (by simp only [selectMlocOf, hBd]; omega)).2.2.2.2.1
  have hMetaW : metaBase + 2 + 8 * (d + 1) < 2 ^ w := by
    have h1 := hMetaEnd; unfold selectLevelMetaSize at h1; rw [hBd] at h1; omega
  have hrLast' : Runs w p ω (selectFillLastLevelBody dgCopyProc coreLenProc)
      (startState [metaBase, d, tok2.termHandle, model'.chain.lastBran, B.lenPtr (d - 1),
        L, pLast, st2.mem sc1, o3.value] st2.mem st2.pos) (.returned sc3) st3 cLast := by
    simpa only [hBd, hBLk] using hrLast
  have hRunBody : ∃ outF cBody,
      Runs w p ω
        (shiftDeepSelectBody deepProc tableWriteProc intLoopProc (op 3) fillLastProc finalizeProc)
        (startState [root, i0, heap] mem pos) (.returned sc4) outF cBody ∧
      outF.mem = st4.mem ∧ cBody ≤ cDeep + cTW + cInt + cOp3 + cLast + cFin + 400 :=
    shiftDeepSelectBody_stitch hw16 hdPos heCapPos (by omega) (by omega) (by omega)
      (by omega) (by rw [hBlkAddrEq]; omega) (by omega) (by omega) (by omega) hMetaW
      hLkW hvCapW heCapW hpLastW hEmb0LeF1 (by omega) hSlotW hSlotEq rfl
      hReadHnd hReadTab hReadD (hSbAddrEq.symm ▸ hReadSb) (hBlkAddrEq.symm ▸ hReadBlk)
      hReadMeta hReadL hReadVCap hReadECap hReadPLast hReadEmb0 hReadF1
      hReadCoreLast hReadBranLast hReadTermH hReadTermB hReadPrevLenD
      hbDeep hrDeep hbTW (hLvlMetaEq.symm ▸ hrTW) hpIntLoop (hLvlMetaEq.symm ▸ hrInt)
      hb3 hr3 hpFillLast hrLast' hpFinalize hrFin
  obtain ⟨outF, cBody, hrBody, hmemF, hcBody⟩ := hRunBody
  have hAmort := shiftDeepSelect_amortized_cost_le (readoutCost := Psc.readout)
    (capExp := capExp) (slot := B.slot) hTP hγk hMono hPot hRestartLower hInitLower
    hiLt (hModOld.2.2.2.1 i0 hiLt) hModelK hModOld hModNew hMatch0' hLocLk hK
  have hcTW' : cTW ≤ 240 * d + 840 := by simpa [selTableWriteContract, hBd] using hcTW
  have hInv4 : SolverSelectInv G L P m 4 2 tok2.table model' (Rrep.foot root tok2) (LevelMetaFoot tok2)
      sg' outF.mem := (hmemF.symm ▸ hRegAt4).to_solverSelectInv (hmemF.symm ▸ hCaps4) hFootDisj2
  refine ⟨sc4, cBody, outF, tok2, sg', hrBody, by rw [hsc3Eq] at hsc4Lo; omega, ?_,
    hlev2Eq.trans (hlev1Eq.trans hlev0), hint2Eq.trans (hint1Eq.trans hint0),
    htab2Eq.trans (htab1Eq.trans htab0Eq), hrec2Eq.trans (hrec1Eq.trans hrec0),
    ?_, ?_, hmemF.symm ▸ hRep4, (hmemF.symm ▸ hCaps4).1, (hmemF.symm ▸ hCaps4).2,
    fun hL => hmemF.symm ▸ (hLay0' hL).of_nonCore_agree hRep0' hRep4 hMeta0' (htab2Eq.trans htab1Eq) hTagOwn4,
    htree2Eq ▸ htrees2Eq ▸ htree1Eq ▸ htrees1Eq ▸ hNum0',
    hmemF.symm ▸ hOffInv4, hmemF.symm ▸ hOffBd4,
    hsgLoc, hsgOwn.trans hOwnEq.symm, hsgPot,
    hmemF.symm ▸ hRegAt4, hInv4, hPhiBd4, hmemF.symm ▸ hz4,
    fun a ha hnf hno => hmemF.symm ▸ hFrFinal a ha hnf hno,
    hFootFinal, fun a ha => hFootDisj2 a (hsgOwn ▸ ha).1 (hsgOwn ▸ ha).2, ?_⟩
  · rw [hFinSpEq] at hsc4Hi; rw [hsc3Eq, hBLk] at hsc4Hi
    dsimp only [sc2, C', model', i0, d, loc, M₀] at hSpBound0 hsc0Hi hsc1Hi hsc2Hi hsc4Hi ⊢; omega
  · have h := hRegAt4.2.2.2.2.2.2.2.1; rw [htab2Eq, htab1Eq, htab0Eq] at h; rw [hmemF]; exact h.trans hhb0.symm
  · have h := hRegAt4.2.2.2.2.2.2.2.2.1; rw [htab2Eq, htab1Eq, htab0Eq] at h; rw [hmemF]; exact h.trans hBlk0.symm
  · rw [hmemF, hPhi4, hPhi3, hsgPot, hReembPot0]
    rw [hPhiTW] at hCostInt
    rw [hFinCostEq] at hCostFin
    simp only [hBd, lt_irrefl, and_false, ↓reduceIte, SelBlocksData.ofChain] at hCostInt hCostLast
    rw [hBLk] at hCostLast
    have hCostInt' : cInt + Rrep.phi root tok1 st1.mem ≤
        selectRefreshInteriorLoopCost (fun j => (model.chain.toTreeChain.activeLSF j).F.F)
          model'.chain Psc.readout i.val L capExp B.slot + Rrep.phi root tok0 st0.mem := hCostInt
    have hCostLast' : cLast ≤
        selectFillLastLevelCost (model.chain.G cfg.P.d).n (model.chain.G cfg.P.d).m
          ((model.chain.toTreeChain.activeLSF cfg.P.d).F.F).n
          ((model.chain.toTreeChain.activeLSF cfg.P.d).F.F).m
          (model'.chain.G cfg.P.d).n (model'.chain.G cfg.P.d).m
          (model'.chain.lastLSFs model'.chain.lastBran).F.F.n
          (model'.chain.lastLSFs model'.chain.lastBran).F.F.m L := hCostLast
    have hMulDist : (deepToolMul + shiftDeepSelectToolMulBound d L capExp M₀ cfg.N₀ B.slot K) *
        (model'.chain.totalRuntime - model.chain.totalRuntime) =
        deepToolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
        shiftDeepSelectToolMulBound d L capExp M₀ cfg.N₀ B.slot K *
          (model'.chain.totalRuntime - model.chain.totalRuntime) := Nat.add_mul ..
    dsimp only [Rrep, C, C', model', i0, d, loc, M₀] at hAmort hCostInt' hCostOp3 hCostLast' hCostFin hCostDeep hMulDist hcTW' ⊢
    omega

end MinCostFlow.MinRatio
