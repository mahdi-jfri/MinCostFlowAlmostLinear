module

public import MinCostFlow.MinRatio.UpdateAssemblyGood
public import MinCostFlow.MinRatio.OrdSolverHistory
import WordRAM.Tactic

/-!
# End-to-end Word-RAM `Update` assembly (`minRatioMachineContractWithV` op 0)

Assembles `solverUpdateBody` against `solverStateRep` and `minRatioMachineContractWithV`
operation 0 (`Update(U, g', ℓ', η)`):
1. Runs `solverUpdatePrepBody` (`UpdateAssemblyPrep.lean`) to copy `eta` and `batch`,
   copy the caller's `g` and `l` entries at the inserted edges, grow internal tables, and
   translate `U` to `U_int`. The chain refresh reads `g` and `l` only through these copies and
   the stored vectors (`updateOverlay`). The two agree with the caller's arrays because the
   precondition says the caller's arrays match the history outside the inserted edges
   (`ordAlg2_detectedWith_agree`). So `Update` reads the caller's arrays only at the inserted
   edges, at cost `O(|U| · L)`.
2. Calls `chainRefreshProc` (`Chain.Ordered.algorithm1_update`, periodic `Rebuild`, pass reset, tree
   edits, detector threshold refresh, shift-quota table refresh).
3. Runs `updateCycleLoopBody` (`Chain.Ordered.algorithm2_loopWith cfg (1 / 2^k)`).
4. Branches on `foundBit`:
   - `1` (good cycle): negates `inner` via `Num.subtractContract` and invokes
     `updateGoodApplyBody`, writing `1` and `actual` (`NormalizationWithin requested actual`)
     at `heap` and updating LCT/off-tree flow and detector accounts.
   - `0` (failure): invokes `updateFailOutputBody`, writing `0` and exact shifted `requested`
     at `heap` while preserving `solverStateRep`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

set_option maxHeartbeats 1000000 in
/-- Generic credit-bearing execution of `solverUpdateBody`, parameterized by an update-carried
invariant `Inv` preserved across prep, chain refresh, `FindCycle`, memory agreement on the solver's
foot, level shift, good apply, and fail output. -/
theorem solverUpdateBody_runs_credit_gen
    {w m U_cap V psi k epsExp drainUnit capExp limbMul capLimit
      growTables copyWords freshBatch chainRefresh cycleLoop subtract goodApply failOut
      findCycleProc updateQualityProc shiftCheckProc shiftLevelProc
      initTree goodNormOut applyPaths applyOffTree pathNorm pathFlowTag explicitRouteUpdate offTreePush isNeg
      findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths toolMul treeMul
      root batch g l eta heap pos : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {opTree : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg F.limbs Rcore}
    {B_bound R_bound : ℤ}
    {refreshSpace refreshBudget : ℕ → ℕ} {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ}
    (Inv : Alg2State cfg → SolverToken cfg F.limbs Rcore → (ℕ → ℕ) → Prop)
    (hInvMeta : ∀ stM1 stM2 t t' m1 m2,
      (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit Rcore).rep root stM1 t m1 →
      Inv stM1 t m1 → PreservesLevelMeta t t' m1 m2 → stM2.chain = stM1.chain →
      (t'.intCap = t.intCap ∨
        (stM2 = model ∧ t = tok ∧ ∃ U, BatchAt mem batch U ∧
          t'.intCap = if t.intCap < model.nextFresh + U.length then 2 * (model.nextFresh + U.length) else t.intCap)) →
      Inv stM2 t' m2)
    (hInvMem : ∀ stM t m1 m2,
      (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit Rcore).rep root stM t m1 →
      Inv stM t m1 →
      (∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit Rcore).foot root t a →
        m2 a = m1 a) →
      Inv stM t m2)
    (hMono : toolMul = 0 ∨ ToolCostMono cfg.T) (hV : cfg.ValidOrdNoHidden)
    (hfmt4 : F.fmt.limbBits = 4)
    (hPL : F.fmt.precision ≤ 4 * F.limbs)
    (hα : cfg.α = Num.IPM.alphaPrime m U_cap / 8)
    (hepsExp : epsExp = k + Num.IPM.alphaExponent m U_cap + 10)
    (hGrow : p.procs[growTables]? = some (growIntTablesBody copyWords))
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hFresh : ∀ r G' H' f' g' next' U',
      MeetsContract w p freshBatch (freshBatchEntryContract w r G' H' f' g' next' U'))
    (hRefresh :
      let L := F.limbs; let P := F.fmt.precision
      let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
      ∃ body, p.procs[chainRefresh]? = some body ∧
        ∀ (root uIntBuf g l quotaBase heap pos : ℕ) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
          (stM : Alg2State cfg) (tok : SolverToken cfg L Rcore) (U : List Update),
          let tr := translateBatch stM.extG stM.extToInt stM.intToExt stM.nextFresh U
          let gVec := updateOverlay stM.extG.E U (readVector mem0 g 4 L P m) stM.extg
          let lVec := updateOverlay stM.extG.E U (readVector mem0 l 4 L P m) stM.extℓ
          let model1 := alg2PreLoopState cfg stM U gVec lVec
          stM = model →
          Rrep.rep root stM tok mem0 →
          Inv stM tok mem0 →
          WireCapFacts capExp limbMul L capLimit stM →
          (∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a) →
          FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
            tr.2.1 tr.2.2.1 tr.2.2.2.1 →
          tr.2.2.2.1 ≤ tok.intCap →
          BatchAt mem uIntBuf tr.2.2.2.2 →
          DynSpanner.Program.SmallBatchAt mem uIntBuf (stM.chain.G 0) tr.2.2.2.2 (heap - uIntBuf) →
          RefreshBatch stM.extG U →
          (∀ x ∈ batchWords U, x < 2 ^ w) →
          2 * (stM.nextFresh + U.length) + 1 < 2 ^ w →
          (∀ i ≤ cfg.P.d,
            shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i < 2 ^ w) →
          (∀ a, Rrep.foot root tok a → a < uIntBuf) →
          g + m * L ≤ uIntBuf → l + m * L ≤ uIntBuf →
          quotaBase + cfg.P.d + 1 < uIntBuf →
          (∀ i ≤ cfg.P.d + 1, ¬ Rrep.foot root tok (quotaBase + i)) →
          uIntBuf ≤ heap →
          ZeroFrom mem heap →
          heap + refreshSpace U.length < 2 ^ w →
          (∀ e ∈ stM.extG.E, (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ lVec e ∧ lVec e ≤ (2 : ℝ) ^ F.rangeExponent) →
          (∀ e ∈ stM.extG.E, ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P = lVec e) →
          ∃ nextHeap cost out tok' B' R',
            Runs w p ω body (startState [root, uIntBuf, g, l, quotaBase, heap] mem pos)
              (.returned nextHeap) out cost ∧
            heap ≤ nextHeap ∧ nextHeap ≤ heap + refreshSpace U.length ∧
            tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
            B' ≤ B_bound ∧ R' ≤ R_bound ∧
            Rrep.rep root model1 tok' out.mem ∧
            Inv model1 tok' out.mem ∧
            PathTreeNumericInv tok'.tree tok'.trees B' R' ∧
            OffTreeRecInv model1 L out.mem tok'.edgeRecords B' ∧
            OffTreeRecBound model1 L out.mem tok'.edgeRecords B' ∧
            (∀ i ≤ cfg.P.d, out.mem (quotaBase + i) =
              shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i) ∧
            out.mem (quotaBase + (cfg.P.d + 1)) = ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ ∧
            ZeroFrom out.mem nextHeap ∧
            (∀ a < heap, ¬ Rrep.foot root tok a → (a < quotaBase ∨ quotaBase + cfg.P.d + 1 < a) →
              out.mem a = mem a) ∧
            (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
            cost + Rrep.phi root tok' out.mem ≤
              refreshBudget U.length +
                toolMul * (model1.chain.totalRuntime - stM.chain.totalRuntime) +
                treeMul * (model1.chain.totalTreeUpdates - stM.chain.totalTreeUpdates) +
                Rrep.phi root tok mem0)
    (hLoop : p.procs[cycleLoop]? = some (updateCycleLoopBody findCycleProc updateQualityProc shiftCheckProc shiftLevelProc))
    (hFind : FindCycleStepSpecW w F.limbs F.fmt.precision m V psi k epsExp drainUnit
      capExp limbMul capLimit cfg Rcore p findCycleProc findSpace findBudget maxEdges maxPaths)
    (hQual : ∀ inner norm, MeetsContract w p updateQualityProc
      (updateQualityFromNormContract w 4 m U_cap k F.fmt.precision inner norm))
    (hCheck : p.procs[shiftCheckProc]? = some shiftCheckBody)
    (hShift :
      let L := F.limbs; let P := F.fmt.precision
      let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
      ∃ body, p.procs[shiftLevelProc]? = some body ∧
        ∀ (root heap pos : ℕ) (i : Fin (cfg.P.d + 1)) (ω : ℕ → Bool) (mem : ℕ → ℕ)
          (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
          let model' := alg2LoopShiftStep cfg model i
          (model.chain.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val →
          (if i.val < cfg.P.d then model.chain.bran i.val else model.branD) < cfg.P.k →
          (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
          shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val < 2 ^ w →
          model.passes i + 1 < 2 ^ w →
          Rrep.rep root model tok mem →
          Inv model tok mem →
          Chain.Ordered.ShiftLoopChainInv cfg model.chain →
          Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
          2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
          PathTreeNumericInv tok.tree tok.trees B R →
          OffTreeRecInv model L mem tok.edgeRecords B →
          OffTreeRecBound model L mem tok.edgeRecords B →
          WireCapFacts capExp limbMul L capLimit model →
          (∀ a, Rrep.foot root tok a → a < heap) →
          ZeroFrom mem heap →
          heap + shiftSpace < 2 ^ w →
          ∃ nextHeap cost out tok',
            Runs w p ω body (startState [root, i.val, heap] mem pos) (.returned nextHeap) out cost ∧
            heap ≤ nextHeap ∧ nextHeap ≤ heap + shiftSpace ∧
            tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
            Rrep.rep root model' tok' out.mem ∧
            Inv model' tok' out.mem ∧
            PathTreeNumericInv tok'.tree tok'.trees B R ∧
            OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
            OffTreeRecBound model' L out.mem tok'.edgeRecords B ∧
            ZeroFrom out.mem nextHeap ∧
            (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
            (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
            cost + Rrep.phi root tok' out.mem ≤
              shiftBudget +
                toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
                treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
                Rrep.phi root tok mem)
    (hSub : MeetsContract w p subtract (Num.subtractContract w 4))
    (hGoodApply : p.procs[goodApply]? = some (updateGoodApplyBody goodNormOut applyPaths applyOffTree))
    (hGoodNorm : p.procs[goodNormOut]? = some (updateGoodNormOutBody pathNorm copyWords pathFlowTag))
    (hApplyPaths : p.procs[applyPaths]? = some (updateGoodApplyPathsBody (opTree 2)))
    (hApplyOff : p.procs[applyOffTree]? = some (updateGoodApplyOffTreeBody explicitRouteUpdate offTreePush))
    (hNorm : ∀ req mag, MeetsContract w p pathNorm (pathNormalizationContract w 4 req mag))
    (hTag : ∀ mult, MeetsContract w p pathFlowTag (pathFlowTagContract w 4 mult))
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract F.fmt F.limbs LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc F.limbs)))
    (hRoute : ExplicitRouteUpdateSpec w F.limbs p explicitRouteUpdate)
    (hPush : p.procs[offTreePush]? = some (offTreePushBody isNeg))
    (hIsNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hFailOut : p.procs[failOut]? = some (updateFailOutputBody copyWords))
    (hBridge : GoodCycleNumericBridge F cfg G m V psi k epsExp drainUnit
      Rcore maxEdges maxPaths B_bound R_bound)
    (hrep : (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit
      Rcore).rep root model tok mem)
    (hInv : Inv model tok mem)
    (hCapFacts : WireCapFacts capExp limbMul F.limbs capLimit model)
    (hpre : (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
      G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc).pre 0 model [root, batch, g, l, eta, heap] mem)
    (hextEq : model.extG = G)
    (hBr : BranchesLtK cfg model)
    (hbelow : ∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit
      Rcore).foot root tok a → a < heap)
    (hGE : ∀ e < m, e ∈ G.E)
    (hz : ZeroFrom mem heap)
    (hmPos : 0 < m)
    (hcapPos : 0 < tok.intCap) (hnfLe : model.nextFresh ≤ tok.intCap)
    (hw16 : 16 < 2 ^ w) (h5L1W : 5 * F.limbs + 1 < 2 ^ w)
    (hPW : F.fmt.precision < 2 ^ w) (hdW : cfg.P.d + 1 < 2 ^ w)
    (hepsW : epsExp < 2 ^ w)
    (hpsiLimW : ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ < 2 ^ w)
    (h2nW : 2 * G.n + 1 < 2 ^ w) (hlogW : Nat.log 2 (2 * G.n + 1) ≤ 4 * F.limbs)
    (hsizeM : Nat.size m ≤ F.rangeExponent + 8)
    (hmaxEP : maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20))
    (hcapEvalB : 2 * (((maxEdges + maxPaths * G.n : ℕ) : ℤ) * B_bound) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapTreeB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) *
      ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
        (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapOffB : B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
      (Num.capacity 4 F.limbs : ℤ))
    (hroom : ∀ U, BatchAt mem batch U →
      let gVec := readVector mem g 4 F.limbs F.fmt.precision m
      let lVec := readVector mem l 4 F.limbs F.fmt.precision m
      let NS := loopStepBound cfg (alg2PreLoopState cfg model U gVec lVec)
      heap + updateSpaceBound F.limbs m cfg.P.d model.nextFresh U.length NS findSpace shiftSpace
        maxEdges maxPaths (refreshSpace U.length) + 2 < 2 ^ w)
    (hquotasW : ∀ U, BatchAt mem batch U →
      let model1 := alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m) (readVector mem l 4 F.limbs F.fmt.precision m)
      ∀ i ≤ cfg.P.d,
        shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i < 2 ^ w)
    (hLoopInv : ∀ U, BatchAt mem batch U →
      Chain.Ordered.ShiftLoopChainInv cfg (alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m)
        (readVector mem l 4 F.limbs F.fmt.precision m)).chain) :
    let L := F.limbs
    let P := F.fmt.precision
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let C := minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
      G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc
    ∃ ret cost out model' tok',
      Runs w p ω
        (solverUpdateBody growTables copyWords freshBatch chainRefresh cycleLoop subtract goodApply failOut)
        (startState [root, batch, g, l, eta, heap] mem pos) (.returned ret) out cost ∧
      C.post 0 model [root, batch, g, l, eta, heap] mem model' out.mem ∧
      Rrep.rep root model' tok' out.mem ∧
      Inv model' tok' out.mem ∧
      (∀ U, BatchAt mem batch U →
        tok'.intCap =
          (if tok.intCap < model.nextFresh + U.length then 2 * (model.nextFresh + U.length) else tok.intCap)) ∧
      ZeroFrom out.mem ret ∧ heap ≤ ret ∧
      (∀ U, BatchAt mem batch U →
        let gVec := readVector mem g 4 L P m
        let lVec := readVector mem l 4 L P m
        let N := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
          (alg2PreLoopState cfg model U gVec lVec).chain
        let NS := loopStepBound cfg (alg2PreLoopState cfg model U gVec lVec)
        ret ≤ heap + updateSpaceBound L m cfg.P.d model.nextFresh U.length NS findSpace shiftSpace
          maxEdges maxPaths (refreshSpace U.length) ∧
        cost + Rrep.phi root tok' out.mem +
            shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model'.chain *
              cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
            toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
          updateBudgetBound L cfg.P.d G.n tok.intCap model.nextFresh U.length N findBudget shiftBudget
            maxEdges maxPaths drainUnit (refreshBudget U.length) +
          Rrep.phi root tok mem +
          toolMul * model'.chain.totalRuntime + treeMul * model'.chain.totalTreeUpdates) ∧
      (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < ret)) ∧
      ∃ B R : ℤ, PathTreeNumericInv tok'.tree tok'.trees B R ∧
        B ≤ B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) ∧
        R ≤ R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) := by
  dsimp only
  let L := F.limbs
  let P := F.fmt.precision
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  have hlocR := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
  have hP4 : 4 ∣ P := hfmt4 ▸ F.fmt.precision_aligned
  have hqExpEq : epsExp - 7 = k + Num.IPM.alphaExponent m U_cap + 3 := by omega
  have hqW : k + Num.IPM.alphaExponent m U_cap + 3 < 2 ^ w := by omega
  obtain ⟨hFits0, handle_, batch_, g_, l_, eta_, heap_, U, hargsEq, hκα, hprec, hflow0,
    hbatch0, hwordsU, hRefreshU, hbatchEnd, hgEnd, hlEnd, hetaEnd, hetaValid,
    hetaLo, hetaHi, _, hglIn, _, hdet⟩ := hpre
  injection hargsEq with hrEq hrest1; injection hrest1 with hbEq hrest2
  injection hrest2 with hgEq hrest3; injection hrest3 with hlEq hrest4
  injection hrest4 with heEq hrest5; injection hrest5 with hhEq _
  subst hrEq; subst hbEq; subst hgEq; subst hlEq; subst heEq; subst hhEq
  rw [hfmt4] at hFits0 hetaValid hetaLo hetaHi hglIn hdet
  have hagree := ordAlg2_detectedWith_agree hdet
  let gVec := readVector mem g 4 L P m
  let lVec := readVector mem l 4 L P m
  let model1 := alg2PreLoopState cfg model U gVec lVec
  let N := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain
  let NS := loopStepBound cfg model1
  have hroomU : heap + updateSpaceBound L m cfg.P.d model.nextFresh U.length NS findSpace shiftSpace
      maxEdges maxPaths (refreshSpace U.length) + 2 < 2 ^ w := hroom U hbatch0
  let descOut := heap + 1 + 2 * L
  let quotaBase := descOut + 2
  let zeroBlock := quotaBase + (cfg.P.d + 2)
  let etaCopy := zeroBlock + L
  let copyLen := 4 * U.length + 1
  let gCopy := etaCopy + L + 2 * copyLen
  let h0 := gCopy + 2 * (m * L)
  have hh0_ge : heap + 1 + 2 * L + 2 + (cfg.P.d + 2) + L + L + 2 * copyLen + 2 * (m * L) = h0 := rfl
  have hh0W : h0 < 2 ^ w := by
    dsimp only [copyLen, updateSpaceBound] at hroomU hh0_ge ⊢; omega
  -- Steps 0–3: run `solverUpdatePrepBody`
  obtain ⟨s9, cPrep, memC2, tokG, h2, h3, hrPrep, hs9r0, hs9r2, hs9r3, hs9r5, hs9r7, hs9r8,
      hs9r9, hs9r11, hs9r13, hs9r14, hs9r15, hs9r16, hs9r18, hs9r31, hs9r41, hs9r42,
      hh2Lo, hh3GeH2, hh3Hi, hrepC2, hpresPrep, hphiC2, hglCopy, hfrF_tags, hfreshTabF,
      hbatchInt, hsmallF, hzF, hftG, hetaCopyF, hfrF_ltEta, hcPrep, hnfCapG, hcapGLe⟩ :=
    solverUpdatePrepBody_runs (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (growTables := growTables) (copyWords := copyWords)
      (freshBatch := freshBatch) (root := root) (batch := batch) (g := g) (l := l) (eta := eta)
      (heap := heap) (pos := pos) hlocalCore hGrow hCopy hFresh hrep hextEq hbatch0 hwordsU hRefreshU
      hbatchEnd hgEnd hlEnd hetaEnd hbelow hz hmPos hcapPos hnfLe hw16
      (by omega) hepsW (by dsimp only [updateSpaceBound] at hroomU; omega)
  have hInvC2 : Inv model tokG memC2 :=
    hInvMeta model model tok tokG mem memC2 hrep hInv hpresPrep rfl (Or.inr ⟨rfl, rfl, U, hbatch0, hcapGLe.1⟩)
  have hh2GeH0 : h0 + copyLen ≤ h2 := hh2Lo
  have hh3LeBound : h3 ≤ h0 + 12 * (model.nextFresh + U.length) + 2 * copyLen := hh3Hi
  replace hftG : ∀ a, Rrep.foot root tokG a → Rrep.foot root tok a ∨ (h0 ≤ a ∧ a < h2 - copyLen) :=
    hftG
  have hgCopyLe : gCopy + m * L + m * L ≤ h2 :=
    le_trans (by dsimp only [h0]; omega) (le_trans (Nat.le_add_right _ _) hh2GeH0)
  -- The vectors handed to `chainRefresh` are the caller's vectors
  have hoverlay (src : ℕ) (stored : ℕ → ℝ) (v : ℕ → ℝ)
      (hst : ∀ e ∈ model.extG.E, ¬ (∃ u ∈ U, u.Inserts e) → v e = stored e)
      (hv0 : ∀ e, m ≤ e → v e = 0)
      (hcp : ∀ e, (∃ u ∈ U, u.Inserts e) → readVector memC2 src 4 L P m e = v e) :
      updateOverlay model.extG.E U (readVector memC2 src 4 L P m) stored = v := by
    refine updateOverlay_eq hst fun e he => ?_
    by_cases hins : ∃ u ∈ U, u.Inserts e
    · exact hcp e hins
    · have hnE : e ∉ model.extG.E := fun hE => he ⟨hE, hins⟩
      have hme : m ≤ e := by
        by_contra hlt
        exact hnE (hextEq ▸ hGE e (by omega))
      rw [hv0 e hme]
      unfold readVector
      rw [if_neg (by omega)]
  have hgVecEq : updateOverlay model.extG.E U (readVector memC2 gCopy 4 L P m) model.extg =
      readVector mem g 4 L P m :=
    hoverlay gCopy model.extg _ (fun e he hn => (hagree e (hextEq ▸ he) hn).1)
      (fun e he => by unfold readVector; rw [if_neg (by omega)]) (fun e he => (hglCopy e he).1)
  have hlVecEq : updateOverlay model.extG.E U (readVector memC2 (gCopy + m * L) 4 L P m) model.extℓ =
      readVector mem l 4 L P m :=
    hoverlay (gCopy + m * L) model.extℓ _ (fun e he hn => (hagree e (hextEq ▸ he) hn).2)
      (fun e he => by unfold readVector; rw [if_neg (by omega)]) (fun e he => (hglCopy e he).2)
  -- Step 4: call `chainRefresh`
  obtain ⟨bRef, hbRef, hRefSpec⟩ := hRefresh
  have hfootG_ltH2 (a : ℕ) (ha : Rrep.foot root tokG a) : a < h2 := by
    rcases hftG a ha with h0' | ⟨_, hhi⟩
    · have := hbelow a h0'; omega
    · omega
  have hqOutG (i : ℕ) (hi : i ≤ cfg.P.d + 1) : ¬ Rrep.foot root tokG (quotaBase + i) := by
    intro hf; rcases hftG _ hf with h0' | ⟨hlo, _⟩
    · have := hbelow _ h0'; dsimp only [quotaBase, descOut] at this; omega
    · dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hlo; omega
  obtain ⟨h4, cR, stR, tokR, B1, R1, hrR, hh4Lo, hh4Hi, _hlevR, hintCapR, hB1Le, hR1Le,
      hrepR, hInvR, hnumR, hoffR, hBdR, hquotasR, hpsiLimR, hzR, hfrR, hftR, hcR⟩ :=
    hRefSpec root h2 gCopy (gCopy + m * L) quotaBase h3 s9.pos ω memC2 s9.mem model tokG U
      rfl hrepC2 hInvC2 hCapFacts hfrF_tags
      hfreshTabF hnfCapG hbatchInt hsmallF (hextEq ▸ hRefreshU) hwordsU
      (by dsimp only [updateSpaceBound] at hroomU; omega)
      (by rw [hgVecEq, hlVecEq]; exact hquotasW U hbatch0)
      hfootG_ltH2 (le_trans (Nat.le_add_right _ _) hgCopyLe) hgCopyLe
      (by dsimp only [quotaBase, descOut, gCopy, etaCopy, zeroBlock] at hgCopyLe ⊢; omega) hqOutG hh3GeH2 hzF
      (by dsimp only [copyLen, updateSpaceBound] at hh3LeBound hroomU hh0_ge ⊢; omega)
      (fun e he => by rw [hlVecEq]; exact (hglIn e (hextEq ▸ he)).2)
      (fun e _ => by
        rw [hlVecEq]; unfold readVector; split_ifs
        · exact ⟨Num.intVal mem (l + e * L) 4 L, rfl⟩
        · exact ⟨0, by simp⟩)
  rw [hgVecEq, hlVecEq] at hrepR hInvR hoffR hBdR hquotasR hcR
  let s10 : State := { regs := Function.update s9.regs 16 h4, mem := stR.mem, pos := stR.pos }
  have rCallR : Runs w p ω (.call 16 chainRefresh [.reg 0, .reg 18, .reg 41, .reg 42, .reg 14, .reg 16]) s9 .normal s10 (cR + 7) :=
    runs_call_iff.mpr ⟨[root, h2, gCopy, gCopy + m * L, quotaBase, h3], bRef, .returned h4, stR, cR,
      by simp [evalArgs, Expr.eval, hs9r0, hs9r18, hs9r41, hs9r42, hs9r14, hs9r16, quotaBase, descOut,
        gCopy, etaCopy, zeroBlock, copyLen],
      hbRef, hrR, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  -- Load `passLimit := stR.mem (quotaBase + (d + 1)) = ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊` into `reg 10`
  let s10p : State := { s10 with regs := Function.update s10.regs 10 ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ }
  have rLoadPsi : Runs w p ω (.assign 10 (.load (.bin .add (.reg 14) (.bin .add (.reg 9) (.const 1))))) s10 .normal s10p 7 :=
    runs_assign_iff.mpr ⟨⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊, by
      simp [Expr.eval, BinOp.eval, s10, hs9r14, hs9r9, show 1 < 2 ^ w by omega, hdW,
        show quotaBase + (cfg.P.d + 1) < 2 ^ w by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hh0W ⊢; omega,
        quotaBase, descOut, hpsiLimR],
      rfl, rfl, rfl⟩
  -- Step 5: call `updateCycleLoopBody`
  have hfootR_lt (a : ℕ) (ha : Rrep.foot root tokR a) : a < h4 := by
    rcases hftR a ha with h0' | ⟨_, hhi⟩
    · exact lt_of_lt_of_le (hfootG_ltH2 a h0') (by omega)
    · exact hhi
  have hqOutR (i : ℕ) (hi : i ≤ cfg.P.d) : ¬ Rrep.foot root tokR (quotaBase + i) := by
    intro hf; rcases hftR _ hf with h0' | ⟨hlo, _⟩
    · exact hqOutG i (by omega) h0'
    · dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hh2GeH0 hlo; omega
  have hdescOutR (j : ℕ) (hj : j ≤ 1) : ¬ Rrep.foot root tokR (descOut + j) := by
    intro hf; rcases hftR _ hf with h0' | ⟨hlo, _⟩
    · rcases hftG _ h0' with h0'' | ⟨hlo', _⟩
      · have := hbelow _ h0''; dsimp only [descOut] at this; omega
      · dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hlo'; omega
    · dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hh2GeH0 hlo; omega
  have hmodel1ExtG : model1.extG = G := by
    dsimp only [model1, alg2PreLoopState]
    rw [(translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt model.intToExt
      model.nextFresh hrep.2.2.2.2.1 (hextEq ▸ hRefreshU.1)).1, hextEq, hRefreshU.2.1]
  have hCapFacts1 : WireCapFacts capExp limbMul L capLimit model1 :=
    hCapFacts.congr (fun j _ => congrFun (alg2PreLoopState_lvlM_N0 cfg model U _ _).1 j)
      (alg2PreLoopState_lvlM_N0 cfg model U _ _).2
  have hlogW1 : Nat.log 2 (2 * model1.extG.n + 1) ≤ 4 * L := by
    rw [hmodel1ExtG]; exact hlogW
  have hlenNN1 : ∀ e ∈ model1.extG.E, 0 ≤ model1.extℓ e := fun e he => by
    rw [hmodel1ExtG] at he
    exact le_of_lt (lt_of_lt_of_le (by positivity) (hglIn e he).2.1)
  have hcapEval1 : 2 * (((maxEdges + maxPaths * model1.extG.n : ℕ) : ℤ) * B1) <
      (Num.capacity 4 L : ℤ) := by
    rw [hmodel1ExtG]
    have hcoeff : (0 : ℤ) ≤ ((maxEdges + maxPaths * G.n : ℕ) : ℤ) := Int.natCast_nonneg _
    have hmul : ((maxEdges + maxPaths * G.n : ℕ) : ℤ) * B1 ≤
        ((maxEdges + maxPaths * G.n : ℕ) : ℤ) * B_bound :=
      mul_le_mul_of_nonneg_left hB1Le hcoeff
    linarith
  have hcapTree1 : 2 * ((2 * model1.extG.n + 1 : ℕ) : ℤ) * (B1 + R1) <
      (Num.capacity 4 L : ℤ) := by
    rw [hmodel1ExtG]
    have hXnn : (0 : ℤ) ≤ (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) :=
      mul_nonneg (Int.natCast_nonneg _) (pow_nonneg (by norm_num) _)
    have hcoeff : (0 : ℤ) ≤ 2 * ((2 * G.n + 1 : ℕ) : ℤ) := by omega
    have hsum : B1 + R1 ≤
        (B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
        (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) := by
      linarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsum hcoeff) hcapTreeB
  obtain ⟨h5, cL, stL, tokL, hrL, hh5Lo, hh5Hi, hfoundL, hrepL, hInvL, hintCapL, hnumL, hoffL, hdescL, hzL, hfrL,
      hftL, hcL⟩ :=
    updateCycleLoopBody_runs_credit_gen (w := w) (L := L) (P := P) (m := m) (U := U_cap) (V := V) (psi := psi)
      (k := k) (qHdr := k) (epsExp := epsExp) (drainUnit := drainUnit)
      (capExp := capExp) (limbMul := limbMul) (capLimit := capLimit) (findCycleProc := findCycleProc)
      (updateQualityProc := updateQualityProc) (shiftCheckProc := shiftCheckProc)
      (shiftLevelProc := shiftLevelProc) (findSpace := findSpace) (findBudget := findBudget)
      (shiftSpace := shiftSpace) (shiftBudget := shiftBudget) (maxEdges := maxEdges) (maxPaths := maxPaths)
      (toolMul := toolMul) (treeMul := treeMul)
      (root := root) (quotaBase := quotaBase) (descOut := descOut) (heap := h4) (pos := s10p.pos)
      (lctOps := model1.lctUpdateOps)
      hlocalCore Inv (fun stM t t' m1 m2 hr hi hp hc => hInvMeta stM stM t t' m1 m2 hr hi hp rfl (Or.inl hc))
      hInvMem hMono hV hα hFind hQual hCheck hShift (by omega) h5L1W hdW hqW hpsiLimW
      hrepR hInvR (hLoopInv U hbatch0) hnumR hoffR hBdR hCapFacts1 hcapEval1 hcapTree1 hlogW1 hlenNN1
      hfootR_lt (by dsimp only [quotaBase, descOut]; omega) hquotasR
      (hquotasW U hbatch0) (branchesLtK_preLoop hBr) hqOutR
      (by dsimp only [descOut]; omega) (by simpa using hdescOutR 0 (by decide)) (hdescOutR 1 (by decide)) hzR
      (by
        have hN_eq : loopStepBound cfg
            (alg2PreLoopState cfg model U (readVector mem g 4 L P m) (readVector mem l 4 L P m)) = NS := rfl
        rw [hN_eq]; dsimp only [copyLen, updateSpaceBound] at hh4Hi hh3LeBound hroomU hh0_ge ⊢; omega)
  have hcapL : ∀ U', BatchAt mem batch U' →
      tokL.intCap =
        (if tok.intCap < model.nextFresh + U'.length then 2 * (model.nextFresh + U'.length) else tok.intCap) := by
    intro U' hB'
    obtain rfl := batchAt_unique_of_refresh hRefreshU hbatch0 hB'
    rw [hintCapL, hintCapR]
    exact hcapGLe.1
  let s11 : State := { regs := Function.update s10p.regs 16 h5, mem := stL.mem, pos := stL.pos }
  have rCallL : Runs w p ω (.call 16 cycleLoop [.reg 0, .reg 14, .reg 10, .reg 11, .reg 13, .reg 16]) s10p .normal s11 (cL + 7) :=
    runs_call_iff.mpr ⟨[root, quotaBase, ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊, k + Num.IPM.alphaExponent m U_cap + 3, descOut, h4],
      updateCycleLoopBody findCycleProc updateQualityProc shiftCheckProc shiftLevelProc, .returned h5, stL, cL,
      by simp [evalArgs, Expr.eval, s10p, s10, hs9r0, hs9r14, hs9r11, hs9r13, quotaBase, descOut, hqExpEq],
      hLoop, hrL, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  -- Shared frame & footprint helpers up to `s11`
  let loopRes := Chain.Ordered.algorithm2_loopWith cfg (1 / (2 : ℝ) ^ k) model1.extG model1.extToInt
    model1.extg model1.extℓ model1.chain model1.branD model1.passes model1.lctUpdateOps
  let modelLoop : Alg2State cfg :=
    { model1 with
      chain := loopRes.1
      branD := loopRes.2.1
      passes := loopRes.2.2.1
      lctUpdateOps := loopRes.2.2.2.1 }
  have hrepL' : Rrep.rep root modelLoop tokL stL.mem := hrepL
  have hInvL' : Inv modelLoop tokL stL.mem :=
    hInvMeta _ modelLoop tokL tokL stL.mem stL.mem hrepL hInvL
      (PreservesLevelMeta.refl _ _) rfl (Or.inl rfl)
  have hfootL_range (a : ℕ) (ha : Rrep.foot root tokL a) : Rrep.foot root tok a ∨ (h0 ≤ a ∧ a < h5) := by
    rcases hftL a ha with h1' | ⟨hlo, hhi⟩
    · rcases hftR a h1' with h2' | ⟨hlo, hhi⟩
      · exact (hftG a h2').imp_right (fun ⟨hlo', hhi'⟩ => ⟨hlo', by omega⟩)
      · exact Or.inr ⟨by omega, lt_of_lt_of_le hhi hh5Lo⟩
    · exact Or.inr ⟨by omega, hhi⟩
  have hfrL_toS9 (a : ℕ) (ha : a < h0) (hnf : ¬ Rrep.foot root tok a)
      (hnDesc0 : a ≠ descOut) (hnDesc1 : a ≠ descOut + 1)
      (hnQuota : a < quotaBase ∨ quotaBase + cfg.P.d + 1 < a) : stL.mem a = s9.mem a := by
    have hnfG : ¬ Rrep.foot root tokG a := fun hf => by
      rcases hftG a hf with h' | ⟨hlo, _⟩
      · exact hnf h'
      · omega
    have hah3 : a < h3 := lt_of_lt_of_le ha (le_trans (le_trans (Nat.le_add_right _ _) hh2GeH0) hh3GeH2)
    have hnfR : ¬ Rrep.foot root tokR a := fun hf => by
      rcases hftR a hf with h' | ⟨hlo, _⟩
      · exact hnfG h'
      · exact absurd hah3 (not_lt.mpr hlo)
    exact (hfrL a (lt_of_lt_of_le hah3 hh4Lo) hnfR hnDesc0 hnDesc1).trans
      (hfrR a hah3 hnfG hnQuota)
  have hnotFoot_geHeap (a : ℕ) (ha : heap ≤ a) : ¬ Rrep.foot root tok a :=
    fun hf => absurd (hbelow a hf) (by omega)
  have hetaCopyL (j : ℕ) (hj : j < L) : stL.mem (etaCopy + j) = mem (eta + j) := by
    rw [hfrL_toS9 (etaCopy + j) (by dsimp only [h0, gCopy]; omega)
      (hnotFoot_geHeap _ (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega))
      (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega)
      (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega)
      (Or.inr (by dsimp only [etaCopy, zeroBlock, quotaBase]; omega))]
    exact hetaCopyF j hj
  have hzeroBlockL : PathIntAt stL.mem zeroBlock 4 L 0 :=
    pathIntAt_zero_of_zeroFrom fun j hj => by
      rw [hfrL_toS9 (zeroBlock + j) (by dsimp only [h0, gCopy, etaCopy]; omega)
        (hnotFoot_geHeap _ (by dsimp only [zeroBlock, quotaBase, descOut]; omega))
        (by dsimp only [zeroBlock, quotaBase, descOut]; omega)
        (by dsimp only [zeroBlock, quotaBase, descOut]; omega)
        (Or.inr (by dsimp only [zeroBlock, quotaBase]; omega)),
        hfrF_ltEta (zeroBlock + j) (by dsimp only [zeroBlock, quotaBase, descOut]; omega)
          (hnotFoot_geHeap _ (by dsimp only [zeroBlock, quotaBase, descOut]; omega))]
      exact hz (zeroBlock + j) (by dsimp only [zeroBlock, quotaBase, descOut]; omega)
  have hfrL_ltHeap (a : ℕ) (ha : a < heap) (hnf : ¬ Rrep.foot root tok a) : stL.mem a = mem a := by
    have hlt_h0 : a < h0 := lt_of_lt_of_le ha (by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut]; omega)
    have hlt_eta : a < etaCopy := lt_of_lt_of_le ha (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega)
    have hlt_desc : a < descOut := lt_of_lt_of_le ha (by dsimp only [descOut]; omega)
    exact (hfrL_toS9 a hlt_h0 hnf (Nat.ne_of_lt hlt_desc) (by omega)
      (Or.inl (lt_of_lt_of_le hlt_desc (by dsimp only [quotaBase]; omega)))).trans (hfrF_ltEta a hlt_eta hnf)
  -- Step 6: load `foundBit := stL.mem descOut` and branch
  let foundBit := if loopRes.2.2.2.2.isSome then 1 else 0
  have hfoundEq : stL.mem descOut = foundBit := hfoundL
  let s12 : State := { s11 with regs := Function.update s11.regs 22 foundBit }
  have rLoadFound : Runs w p ω (.assign 22 (.load (.reg 13))) s11 .normal s12 3 :=
    runs_assign_iff.mpr ⟨foundBit, by simp [Expr.eval, s11, s10p, s10, hs9r13, descOut, hfoundEq], rfl, rfl, rfl⟩
  let goodBranch : Stmt :=
    .assign 23 (.load (.bin .add (.reg 13) (.const 1))) ;;
    .assign 24 (.load (.reg 23)) ;;
    .assign 25 (.load (.bin .add (.reg 23) (.const 2))) ;;
    .assign 26 (.load (.bin .add (.reg 23) (.const 3))) ;;
    .assign 27 (.load (.bin .add (.reg 23) (.const 4))) ;;
    .assign 28 (.load (.bin .add (.reg 23) (.const 5))) ;;
    .assign 29 (.bin .add (.reg 16) (.reg 7)) ;;
    .call 16 subtract [.reg 15, .reg 24, .reg 7, .reg 16] ;;
    .call 16 goodApply [.reg 0, .reg 31, .reg 29, .reg 25, .reg 26, .reg 27, .reg 28, .reg 5, .reg 16] ;;
    .ret (.reg 16)
  let failBranch : Stmt :=
    .call 30 failOut [.reg 31, .reg 7, .reg 8, .reg 5] ;;
    .ret (.reg 16)
  have hchainAll {retEnd cTail : ℕ} {outEnd : State}
      (hTail : Runs w p ω (.cond (.reg 22) goodBranch failBranch) s12 (.returned retEnd) outEnd cTail) :
      Runs w p ω
        (solverUpdateBody growTables copyWords freshBatch chainRefresh cycleLoop subtract goodApply failOut)
        (startState [root, batch, g, l, eta, heap] mem pos) (.returned retEnd) outEnd
        (cPrep + ((cR + 7) + (7 + ((cL + 7) + (3 + cTail + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s9, cPrep, _, hrPrep,
    runs_seq_iff.mpr (Or.inr ⟨s10, cR + 7, _, rCallR,
    runs_seq_iff.mpr (Or.inr ⟨s10p, 7, _, rLoadPsi,
    runs_seq_iff.mpr (Or.inr ⟨s11, cL + 7, _, rCallL,
    runs_seq_iff.mpr (Or.inr ⟨s12, 3, cTail, rLoadFound, hTail, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  cases hOpt : loopRes.2.2.2.2 with
  | none =>
    have hfb0 : foundBit = 0 := by simp [foundBit, hOpt]
    have hetaCopyValid : Num.Valid stL.mem etaCopy 4 L := numValid_congr hetaValid hetaCopyL
    have hetaCopyVal : Num.fixVal stL.mem etaCopy 4 L P = Num.fixVal mem eta 4 L P := by
      unfold Num.fixVal; rw [numIntVal_congr hetaCopyL]
    have hposReq : 0 < Num.fixVal stL.mem etaCopy 4 L P := by
      rw [hetaCopyVal]; exact lt_of_lt_of_le (by positivity) hetaLo
    have hzeroOut : ∀ j < 2 * L, stL.mem (heap + 1 + j) = 0 := fun j hj => by
      rw [hfrL_toS9 (heap + 1 + j) (by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut]; omega)
        (hnotFoot_geHeap _ (by omega)) (by dsimp only [descOut]; omega) (by dsimp only [descOut]; omega)
        (Or.inl (by dsimp only [quotaBase, descOut]; omega)),
        hfrF_ltEta (heap + 1 + j) (by omega) (hnotFoot_geHeap _ (by omega))]
      exact hz (heap + 1 + j) (by omega)
    obtain ⟨cFail, stFail, hrFail, hcFail, hAnsF, hScalF, hNormF, hfrFail⟩ :=
      updateFailOutputBody_runs (w := w) (copyWords := copyWords) (eta := etaCopy) (L := L) (P := P)
        (heap := heap) (pos := s12.pos) (p := p) (ω := ω) (mem := stL.mem) hCopy hP4 hPL
        (Or.inr (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega))
        (by dsimp only [h0, gCopy] at hh0W; omega) hetaCopyValid hposReq hzeroOut
        (by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hh0W; omega) (by omega)
    let s13 : State := { regs := Function.update s12.regs 30 (heap + 1 + 2 * L), mem := stFail.mem, pos := stFail.pos }
    have rCallFail : Runs w p ω (.call 30 failOut [.reg 31, .reg 7, .reg 8, .reg 5]) s12 .normal s13 (cFail + 5) :=
      runs_call_iff.mpr ⟨[etaCopy, L, P, heap], updateFailOutputBody copyWords, .returned (heap + 1 + 2 * L), stFail, cFail,
        by simp [evalArgs, Expr.eval, s12, s11, s10p, s10, hs9r31, hs9r7, hs9r8, hs9r5, etaCopy, zeroBlock, quotaBase, descOut],
        hFailOut, hrFail, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    have rRetFail : Runs w p ω (.ret (.reg 16)) s13 (.returned h5) s13 2 :=
      runs_ret_iff.mpr ⟨h5, by simp [Expr.eval, s13, s12, s11], rfl, rfl, rfl⟩
    have rCondFail : Runs w p ω (.cond (.reg 22) goodBranch failBranch) s12 (.returned h5) s13 (1 + ((cFail + 5) + 2 + 1) + 1) :=
      runs_cond_iff.mpr ⟨0, (cFail + 5) + 2 + 1, by simp [Expr.eval, s12, hfb0],
        by simp only [↓reduceIte]; exact runs_seq_iff.mpr (Or.inr ⟨s13, cFail + 5, 2, rCallFail, rRetFail, rfl⟩),
        by simp [Expr.size]⟩
    have hagFail (a : ℕ) (ha : Rrep.foot root tokL a) : stL.mem a = stFail.mem a := by
      rcases hfootL_range a ha with h0' | ⟨hlo, _⟩
      · exact (hfrFail a (Or.inl (hbelow a h0'))).symm
      · exact (hfrFail a (Or.inr (by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hlo; omega))).symm
    have hrepFail : Rrep.rep root modelLoop tokL stFail.mem := (hlocR root modelLoop tokL stL.mem stFail.mem hagFail).1 hrepL'
    have hInvFail : Inv modelLoop tokL stFail.mem :=
      hInvMem modelLoop tokL stL.mem stFail.mem hrepL' hInvL' (fun a ha => (hagFail a ha).symm)
    have hphiFail : Rrep.phi root tokL stFail.mem = Rrep.phi root tokL stL.mem :=
      ((hlocR root modelLoop tokL stL.mem stFail.mem hagFail).2).symm
    have hxNN : (0 : ℤ) ≤ (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) :=
      mul_nonneg (Int.natCast_nonneg _) (pow_nonneg (by norm_num) _)
    refine ⟨h5, _, s13, modelLoop, tokL, hchainAll rCondFail, ?_, hrepFail, hInvFail, hcapL,
      fun a ha => by rw [hfrFail a (Or.inr (by omega))]; exact hzL a ha, by omega,
      fun U' hB' => ?_, ?_, fun a ha => (hfootL_range a ha).imp_right (fun ⟨h1', h2'⟩ => ⟨by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at h1'; omega, h2'⟩),
      B1, R1, hnumL, le_add_of_le_of_nonneg hB1Le hxNN, le_add_of_le_of_nonneg hR1Le hxNN⟩
    · refine ⟨Num.fixVal mem eta 4 L P, by rw [hfmt4]; exact hetaCopyVal ▸ hScalF,
        by rw [hfmt4]; exact hetaCopyVal ▸ hNormF,
        by rw [hfmt4]; exact fun e he => hFits0 e he,
        fun U' hB' => ?_⟩
      have hUeq : U' = U := batchAt_unique_of_refresh hRefreshU hbatch0 hB'
      rw [hUeq]
      dsimp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [hfmt4, algorithm2_dsWithFailureWith_update_none cfg (1 / (2 : ℝ) ^ k) model U gVec lVec _ hOpt]
      exact ⟨rfl, by simpa [heapArg] using hAnsF⟩
    · have hUeq : U' = U := batchAt_unique_of_refresh hRefreshU hbatch0 hB'
      rw [hUeq]
      have hh5Hi' : h5 ≤ h4 + (NS + 1) * cycleLoopIterSpace L findSpace shiftSpace := hh5Hi
      obtain ⟨hcR', hcL', hsubAC'⟩ :=
        update_credit_telescope (L := L) (B0 := cycleLoopIterBudget L cfg.P.d findBudget shiftBudget)
          (N0 := N) (N1 := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) loopRes.1)
          (refBud := refreshBudget U.length) (phi0 := Rrep.phi root tok mem)
          (phiR := Rrep.phi root tokR stR.mem) (phiL := Rrep.phi root tokL stFail.mem)
          (k := k) (gVec := gVec) (lVec := lVec) hMono
          (by rw [← hphiC2]; exact hcR) (by rw [hphiFail]; exact hcL)
      have htot := updateBudgetBound_fail_le (n := G.n) (maxEdges := maxEdges)
        (maxPaths := maxPaths) (drainUnit := drainUnit) hcPrep hcR' hcL' hcFail
      refine ⟨updateSpaceBound_good_le hh0_ge hh3LeBound hh4Hi hh5Hi' (by omega), ?_⟩
      change _ + Rrep.phi root tokL stFail.mem +
          shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) loopRes.1 *
            cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
          toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
        updateBudgetBound L cfg.P.d G.n tok.intCap model.nextFresh U.length N findBudget shiftBudget
          maxEdges maxPaths drainUnit (refreshBudget U.length) +
          Rrep.phi root tok mem +
          toolMul * loopRes.1.totalRuntime + treeMul * loopRes.1.totalTreeUpdates
      dsimp only [loopRes, model1] at htot hsubAC' ⊢
      omega
    · intro a ha hnf
      exact (hfrFail a (Or.inl ha)).trans (hfrL_ltHeap a ha hnf)
  | some Δ =>
    have hfb1 : foundBit = 1 := by simp [foundBit, hOpt]
    obtain ⟨inner, norm, edges, paths, hdescL', hedMax, hptMax, htagEd, htagPt, htag18, hcurDescLo, hcurDescHi⟩ :=
      hdescL (by rw [hOpt]; rfl)
    have ⟨hΔEq, hΔGood⟩ := algorithm2_loopWith_some_spec cfg (1 / (2 : ℝ) ^ k)
      model1.extG model1.extToInt model1.extg model1.extℓ model1.chain model1.branD model1.passes
      model1.lctUpdateOps Δ hOpt
    have htrFst : (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).1 = G := by
      have h1 : ∀ (Us : List Update) (G0 : MGraph) (f0 g0 : ℕ → ℕ) (nf0 : ℕ),
          (translateBatch G0 f0 g0 nf0 Us).1 = G0.applyBatch Us := by
        intro Us; induction Us with
        | nil => intro _ _ _ _; rfl
        | cons u us ih =>
          intro G0 f0 g0 nf0; cases u with
          | insert _ _ _ => exact ih _ _ _ _
          | delete _ => exact ih _ _ _ _
          | split _ _ _ _ => exact ih _ _ _ _
      rw [h1, hextEq, hRefreshU.2.1]
    have hExtEqL : modelLoop.extG = G := htrFst
    let request := Num.intVal mem eta 4 L
    have hetaCopyAt : PathIntAt s12.mem etaCopy 4 L request :=
      ⟨numValid_congr hetaValid hetaCopyL, numIntVal_congr hetaCopyL⟩
    have hh5Hi' : h5 ≤ h4 + (NS + 1) * cycleLoopIterSpace L findSpace shiftSpace := hh5Hi
    obtain ⟨hEnd, cGood, stGA, tokEnd, rGoodSeq, hout1, houtScal, hnormWithin, hFitsEnd, hrepEnd,
        hpresGood, hintCapGood, hzEnd, hhEndLo, hhEndHi, hfrGA, hftGA, hcGood, hnumGood⟩ :=
      solverUpdateGoodBranch_runs (psi := psi) (k := k) (epsExp := epsExp) (drainUnit := drainUnit)
        (copyWords := copyWords) (subtract := subtract) (goodApply := goodApply) (initTree := initTree)
        (goodNormOut := goodNormOut) (applyPaths := applyPaths) (applyOffTree := applyOffTree)
        (pathNorm := pathNorm) (pathFlowTag := pathFlowTag) (explicitRouteUpdate := explicitRouteUpdate)
        (offTreePush := offTreePush) (isNeg := isNeg) (maxEdges := maxEdges) (maxPaths := maxPaths)
        (root := root) (heap := heap) (descOut := descOut) (zeroBlock := zeroBlock)
        (etaCopy := etaCopy) (h0 := h0) (h5 := h5) (F := F) (G := G) (s12 := s12)
        hlocalCore hfmt4 hCopy hSub
        hGoodApply hGoodNorm hApplyPaths hApplyOff hNorm hTag hTreeImpl hRoute hPush hIsNeg hBridge
        hExtEqL hFits0 hflow0 hκα hprec hglIn
        hrepL' hnumL hoffL hB1Le hR1Le hdescL' hedMax hptMax htagEd htagPt htag18
        hΔEq hΔGood hetaCopyAt hetaLo hetaHi hzeroBlockL hzL
        (fun a ha => (hfootL_range a ha).imp_left (hbelow a))
        ⟨by simp [s12, s11, s10p, s10, hs9r0], by simp [s12, s11, s10p, s10, hs9r5], by simp [s12, s11, s10p, s10, hs9r7, L],
         by simp [s12, s11, s10p, s10, hs9r13, descOut], by simp [s12, s11, s10p, s10, hs9r15, zeroBlock, quotaBase, descOut],
         by simp [s12, s11], by simp [s12, s11, s10p, s10, hs9r31, etaCopy, zeroBlock, quotaBase, descOut]⟩
        ⟨rfl, by dsimp only [zeroBlock, quotaBase, descOut]; omega, rfl, by dsimp only [h0, gCopy]; omega, by omega,
         by change h0 ≤ stL.mem (descOut + 1); omega, hcurDescHi⟩
        (by omega) hPW h2nW hlogW hsizeM hmaxEP hcapTreeB hcapOffB (by
          change h5 + 2 * L + goodApplySpace L maxPaths maxEdges + 2 < 2 ^ w
          dsimp only [copyLen, updateSpaceBound] at hh5Hi' hh4Hi hh3LeBound hroomU hh0_ge ⊢; omega)
    have rCondGood : Runs w p ω (.cond (.reg 22) goodBranch failBranch) s12 (.returned hEnd) stGA (1 + cGood + 1) :=
      runs_cond_iff.mpr ⟨1, cGood, by simp [Expr.eval, s12, hfb1],
        by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact rGoodSeq, by simp [Expr.size]⟩
    let mult := pathMultiplier P request (-inner)
    let actual := -(((mult : ℝ) / (2 : ℝ) ^ P) * ((inner : ℝ) / (2 : ℝ) ^ P))
    let inc : ℕ → ℝ := fun e =>
      if e ∈ modelLoop.extG.E then -(actual / modelLoop.extG.inner modelLoop.extg Δ) * Δ e else 0
    let modelEnd : Alg2State cfg :=
      { modelLoop with
        flow := fun e => modelLoop.flow e + inc e
        detectAccum := fun e => modelLoop.detectAccum e + |inc e| }
    have hInvEnd : Inv modelEnd tokEnd stGA.mem :=
      hInvMeta modelLoop modelEnd tokL tokEnd stL.mem stGA.mem hrepL' hInvL' hpresGood rfl (Or.inl hintCapGood)
    refine ⟨hEnd, _, stGA, modelEnd, tokEnd, hchainAll rCondGood, ?_, hrepEnd, hInvEnd,
      fun U' hB' => hintCapGood.trans (hcapL U' hB'), hzEnd, by omega,
      fun U' hB' => ?_, ?_, ?_, ?_⟩
    rotate_right
    · obtain ⟨B, R, hnB, hBle, hRle, _⟩ := hnumGood
      exact ⟨B, R, hnB, hBle, hRle⟩
    · refine ⟨actual, by rw [hfmt4]; exact houtScal, by rw [hfmt4]; exact hnormWithin,
        by rw [hfmt4]; exact hFitsEnd, fun U' hB' => ?_⟩
      have hUeq : U' = U := batchAt_unique_of_refresh hRefreshU hbatch0 hB'
      rw [hUeq]
      dsimp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [hfmt4, algorithm2_dsWithFailureWith_update_some cfg (1 / (2 : ℝ) ^ k) model U gVec lVec actual Δ hOpt]
      exact ⟨rfl, by simp [AnswerAt, heapArg, hout1]⟩
    · have hUeq : U' = U := batchAt_unique_of_refresh hRefreshU hbatch0 hB'
      rw [hUeq]
      obtain ⟨hcR', hcL', hsubAC'⟩ :=
        update_credit_telescope (L := L) (B0 := cycleLoopIterBudget L cfg.P.d findBudget shiftBudget)
          (N0 := N) (N1 := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) loopRes.1)
          (refBud := refreshBudget U.length) (phi0 := Rrep.phi root tok mem)
          (phiR := Rrep.phi root tokR stR.mem) (phiL := Rrep.phi root tokL stL.mem)
          (k := k) (gVec := gVec) (lVec := lVec) hMono
          (by rw [← hphiC2]; exact hcR) hcL
      change cGood + Rrep.phi root tokEnd stGA.mem ≤
        updateGoodBranchBudget L G.n maxEdges maxPaths drainUnit + Rrep.phi root tokL stL.mem at hcGood
      have htot := updateBudgetBound_good_le (n := G.n) (maxEdges := maxEdges)
        (maxPaths := maxPaths) (drainUnit := drainUnit) hcPrep hcR' hcL' hcGood
      refine ⟨updateSpaceBound_good_le hh0_ge hh3LeBound hh4Hi hh5Hi' hhEndHi, ?_⟩
      change _ + Rrep.phi root tokEnd stGA.mem +
          shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) loopRes.1 *
            cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
          toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
        updateBudgetBound L cfg.P.d G.n tok.intCap model.nextFresh U.length N findBudget shiftBudget
          maxEdges maxPaths drainUnit (refreshBudget U.length) +
          Rrep.phi root tok mem +
          toolMul * loopRes.1.totalRuntime + treeMul * loopRes.1.totalTreeUpdates
      dsimp only [loopRes, model1] at htot hsubAC' ⊢
      omega
    · intro a ha hnf
      have hnfL : ¬ Rrep.foot root tokL a := fun hf => by
        rcases hfootL_range a hf with h0' | ⟨hlo, _⟩
        · exact hnf h0'
        · have : heap ≤ h0 := by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut]; omega
          exact absurd (lt_of_lt_of_le ha this) (not_lt_of_ge hlo)
      exact (hfrGA a (by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hh2GeH0 hh3GeH2 hh4Lo hh5Lo ⊢; omega) (Or.inl ha) hnfL).trans (hfrL_ltHeap a ha hnf)
    · intro a ha
      have hheap_h0 : heap ≤ h0 := by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut]; omega
      have hheap_h5 : heap ≤ h5 := le_trans hheap_h0 (le_trans (le_trans (Nat.le_add_right _ _) hh2GeH0)
        (le_trans hh3GeH2 (le_trans hh4Lo hh5Lo)))
      rcases hftGA a ha with h0' | ⟨hlo, hhi⟩
      · exact (hfootL_range a h0').imp_right fun ⟨h1', h2'⟩ =>
          ⟨le_trans hheap_h0 h1', lt_of_lt_of_le h2' (le_trans (Nat.le_add_right _ _) hhEndLo)⟩
      · exact Or.inr ⟨le_trans hheap_h5 (le_trans (Nat.le_add_right _ _) hlo), hhi⟩

end MinCostFlow.MinRatio
