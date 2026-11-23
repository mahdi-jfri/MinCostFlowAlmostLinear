module

public import MinCostFlow.MinRatio.WireChainCoreBranchBIntOldKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBIntSuffixKFBL
public import MinCostFlow.MinRatio.WireChainCoreAlgebra
public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
import WordRAM.Tactic

/-!
# The suffix rebuild of the interior step after the Branch B loop (`WireChainCoreBranchBIntRebKFBL`)

After its first part (`wireBranchBIntOldKFBL_runs`), the interior step rebuilds the levels from
`i₀` on: it runs `wireBranchBIntSuffixKFBL` on the graph of level `i₀` (which now carries the
batch), the lengths of level `i₀` and the order list of level `i₀ - 1`. In the model this is
`algorithm1_rebuild` at level `i₀` on the graph `curG`, from the chain `ch` of the loop with the
lengths `ℓ'` and gradients `g'`.

* `branchBIntNext_facts`: the facts of the rebuilt chain `next` that the run needs. The levels
  below `i₀` do not change, the start data of level `i₀` (graph, lengths and order) are those that
  the first part left, and every rebuilt level is a fresh start of the tool
  (`ordAlgorithm1_rebuild_exact` and `UpdateRebuildModelInv`).
* `wireBranchBIntRebKFBL_runs`: the run from the state after the first part. It is
  `wireBranchBIntSuffixKFBL_runs` with the heap floor at the heap pointer of that state, so the new
  cores and the new last level lie in fresh heap. Below that pointer it writes only the cells of
  the rebuilt levels.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- The facts of the chain `next` after the rebuild of the levels from `i₀` on, with `0 < i₀`.
The levels below `i₀` keep their state, level `i₀` starts on `curG` with the order of the active
spanner of level `i₀ - 1` and the lengths of the chain with `curG` at level `i₀`, and every level
from `i₀` on is a fresh start of the tool with the bounds of `UpdateRebuildModelInv`. -/
theorem branchBIntNext_facts {w L P wordExp stretchPrec : ℕ} {fmt : Num.Format w}
    {cfg : Alg2Config} {Psc : SparseCoreOrdParams} (ch : ChainState cfg.T cfg.P) (curG : MGraph)
    (ℓ' g' : ℕ → ℝ) (curEnc i₀ : ℕ) (next : ChainState cfg.T cfg.P)
    (hNext : next = (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
      { ch with ℓ := ℓ', g := g' } i₀ curG curEnc).1)
    (hPos : 0 < i₀) (hLt : i₀ < cfg.P.d)
    (hReb : UpdateRebuildModelInv w L P wordExp stretchPrec ch i₀ curG ℓ' g' curEnc)
    (hWordExpEq : Psc.wordExp = wordExp) (hPrec : fmt.precision = P)
    (hInitOrdEq : ToolInitOrdEqOnE cfg.T)
    (hNextN : ∀ j ≤ cfg.P.d, (next.G j).n ≤ next.N₀)
    (hNextRot : ∀ j < cfg.P.d, ordRotWords (chainLevelOrdAbs next j) (next.bran j) ≤
      1 + 2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m) :
    (∀ m < i₀, next.G m = ch.G m ∧ next.scState m = ch.scState m ∧ next.bran m = ch.bran m ∧
      next.updCount m = ch.updCount m ∧ next.rebuildCount m = ch.rebuildCount m) ∧
    next.G i₀ = curG ∧ next.ℓ = ℓ' ∧ next.lvlM = ch.lvlM ∧ next.N₀ = ch.N₀ ∧
    (∀ j, next.rebuildCount j = if j = i₀ then ch.rebuildCount i₀ + 1 else ch.rebuildCount j) ∧
    ch.rebuildCount i₀ + 1 < 2 ^ w ∧
    (∀ j < i₀, chainLevelOrdAbs next j = chainLevelOrdAbs ch j) ∧
    next.levelOrd i₀ = cfg.T.rot (ch.scState (i₀ - 1)) (ch.bran (i₀ - 1)) ∧
    (∀ j < i₀, next.toTreeChain.chainLen next.ℓ j = ch.toTreeChain.chainLen ℓ' j) ∧
    next.toTreeChain.chainLen next.ℓ i₀ =
      ({ ch.toTreeChain with G := fun j => if j = i₀ then curG else ch.G j } : TreeChain).chainLen
        ℓ' i₀ ∧
    (∀ j, i₀ ≤ j → j < cfg.P.d →
      let Gj := next.G j
      let ℓj := next.toTreeChain.chainLen next.ℓ j
      next.scState j = cfg.T.initOrd cfg.P.k (next.lvlM j) next.N₀ Gj
        (fun e => if e ∈ Gj.E then ℓj e else 0)
        (fun e => if e ∈ Gj.E then ℓj e else 0)
        (next.levelOrd j) ∧
      next.G (j + 1) = cfg.T.S (next.scState j) 0 ∧
      next.bran j = 0 ∧ next.updCount j = 0 ∧
      (next.G j).m ≤ next.lvlM j ∧ (next.G j).n ≤ next.N₀ ∧
      next.lvlM j < 2 ^ w ∧ (next.lvlM j + next.N₀ + 2) ^ Psc.wordExp * (L + 1) < 2 ^ w ∧
      IsRotationOrder (next.G j) (next.levelOrd j) ∧
      (∀ e ∈ (next.G j).E, 0 < ℓj e) ∧
      (next.G (j + 1)).E ⊆ (next.G j).E ∧
      (∀ e ∈ (next.G (j + 1)).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
          next.toTreeChain.chainLen next.ℓ (j + 1) e) ∧
      (next.G (j + 1)).m ≤ (next.G (j + 1)).m ∧
      (next.G (j + 1)).n ≤ next.N₀ ∧
      ordRotWords (chainLevelOrdAbs next j) 0 ≤
        1 + 2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m ∧
      (j + 1 < cfg.P.d → (next.G (j + 1)).m ≤ next.lvlM (j + 1))) ∧
    ((next.lastK, next.lastLSFs) =
        cfg.L.build (next.G cfg.P.d) (next.toTreeChain.chainLen next.ℓ cfg.P.d) ∧
      next.lastBran = 0 ∧
      cfg.L.build (next.G cfg.P.d) (fun e => if e ∈ (next.G cfg.P.d).E then
        next.toTreeChain.chainLen next.ℓ cfg.P.d e else 0) =
        cfg.L.build (next.G cfg.P.d) (next.toTreeChain.chainLen next.ℓ cfg.P.d) ∧
      (∀ e ∈ (next.G cfg.P.d).E, 0 < next.toTreeChain.chainLen next.ℓ cfg.P.d e) ∧
      (∀ e ∈ (next.G cfg.P.d).E,
        2 * (2 : ℝ) ^ stretchPrec *
          lastLevelStretchBound (next.G cfg.P.d) (next.toTreeChain.chainLen next.ℓ cfg.P.d) e <
          Num.capacity 4 L)) := by
  subst hNext
  set next := (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
    { ch with ℓ := ℓ', g := g' } i₀ curG curEnc).1 with hNextDef
  obtain ⟨hRCNext, _, hRebLvls, hLastAgree, hLastPos, hLastStr⟩ := hReb
  obtain ⟨hExPre, hExG, hExLvls, hExLast, hExLastBr, hExRC, hExEll, _, hExLvlM, hExN0, _⟩ :=
    ordAlgorithm1_rebuild_exact cfg.T cfg.L cfg.P { ch with ℓ := ℓ', g := g' } hLt curG curEnc
  have hNextN0 : next.N₀ = ch.N₀ := hExN0
  have hNextLvlM : next.lvlM = ch.lvlM := hExLvlM
  have hNextEll : next.ℓ = ℓ' := hExEll
  have hPre : ∀ m < i₀, next.G m = ch.G m ∧ next.scState m = ch.scState m ∧
      next.bran m = ch.bran m ∧ next.updCount m = ch.updCount m ∧
      next.rebuildCount m = ch.rebuildCount m := hExPre
  have hPrevAbsEq : ∀ j < i₀, chainLevelOrdAbs next j = chainLevelOrdAbs ch j := by
    intro j hj
    have hp := hPre j hj
    have hOrdPrev : next.levelOrd j = ch.levelOrd j := by
      unfold ChainState.levelOrd Chain.Ordered.chainLevelOrd
      split_ifs with h0
      · rw [(hPre 0 hPos).1]
      · have hp2 := hPre (j - 1) (by omega)
        rw [hp2.2.1, hp2.2.2.1]
    unfold chainLevelOrdAbs
    rw [hp.1, hp.2.1, hp.2.2.2.1, hOrdPrev]
  have hLenLt : ∀ j < i₀, next.toTreeChain.chainLen next.ℓ j = ch.toTreeChain.chainLen ℓ' j := by
    intro j hj
    rw [hNextEll]
    refine chainLen_congr_lt _ _ ℓ' j (fun m hm => ?_)
    have hp := hPre m (by omega)
    simp only [TreeChain.activeLSF, ChainState.toTreeChain, show m < cfg.P.d by omega,
      ↓reduceIte, hp.2.1, hp.2.2.1]
  have hNextOrd : next.levelOrd i₀ = cfg.T.rot (ch.scState (i₀ - 1)) (ch.bran (i₀ - 1)) := by
    have hne0 : i₀ ≠ 0 := by omega
    have hp := hPre (i₀ - 1) (by omega)
    simp only [ChainState.levelOrd, Chain.Ordered.chainLevelOrd, hne0, ↓reduceIte]
    rw [hp.2.1, hp.2.2.1]
  have hLenEq : next.toTreeChain.chainLen next.ℓ i₀ =
      ({ ch.toTreeChain with G := fun j => if j = i₀ then curG else ch.G j } :
        TreeChain).chainLen ℓ' i₀ := by
    rw [hNextEll]
    refine chainLen_congr_lt _ _ ℓ' i₀ (fun m hm => ?_)
    have hp := hPre m hm
    simp only [TreeChain.activeLSF, ChainState.toTreeChain, show m < cfg.P.d by omega,
      ↓reduceIte, hp.2.1, hp.2.2.1]
  refine ⟨hPre, hExG, hNextEll, hNextLvlM, hNextN0, hExRC, hRCNext, hPrevAbsEq, hNextOrd, hLenLt,
    hLenEq, fun j hj1 hj2 => ?_, ⟨hExLast.trans (by rw [hNextEll]), hExLastBr, hLastAgree,
      hLastPos, hLastStr⟩⟩
  obtain ⟨hScJ, hGJ1, hBrJ, hUpdJ⟩ := hExLvls j hj1 hj2
  obtain ⟨hmLe, hnLe, hMW, hWordE, hRot, hPosJ, hSub, hFits⟩ := hRebLvls j hj1 hj2
  refine ⟨?_, hGJ1, hBrJ, hUpdJ, hmLe, hnLe, hMW, hWordExpEq ▸ hWordE, hRot, hPosJ, hSub,
    hPrec ▸ hFits, le_rfl, hNextN (j + 1) (by omega), hBrJ ▸ hNextRot j hj2,
    fun hj1' => (hRebLvls (j + 1) (by omega) hj1').1⟩
  rw [hScJ, hNextLvlM, hNextN0, hNextEll]
  exact hInitOrdEq cfg.P.k (ch.lvlM j) ch.N₀ (next.G j) _ _ _ _ (next.levelOrd j)
    (fun e he => by simp only [he, ↓reduceIte]; rfl)

set_option maxHeartbeats 1600000 in
/-- **The suffix rebuild of the interior step.** From the state `s` after the first part, with
the mid facts `M` and the loop invariant `I` at the exit state `sE`, the run of
`wireBranchBIntSuffixKFBL` rebuilds the levels `i₀, …, d - 1` and the last level of the chain
`next`. The post is that of `wireBranchBIntSuffixKFBL_runs` with the heap floor at `s.regs 4`:
the new cores, their graphs and lengths and the new last level lie in `[s.regs 4, out.regs 4)`,
and below `s.regs 4` the run writes only the handle, branch and length cells of the rebuilt
levels. -/
theorem wireBranchBIntRebKFBL_runs
    {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy N0 oldPtrs i₀ ordPtr ordWords wordExp stretchPrec
      capLimit coreLenProc lastInit lastMul lastSpace : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {opCore opLast : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ}
    {ℓ' g' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ}
    {ch : ChainState cfg.T cfg.P} {curG : MGraph} {curU : List Update}
    {curEditsList : List OrdEdit} {curEnc : ℕ} {oldOrd : ℕ → List End} {sE s : State}
    {tok tokM : ℕ → Rcore.τ} {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists} {levelSpace levelCost : ℕ → ℕ}
    (E : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore
      p opCore)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hOldLo : A.selBase + 1 + 12 * cfg.P.d ≤ oldPtrs)
    (hOldHi : oldPtrs + (cfg.P.d + 1) ≤ A.heapFloor)
    (hPos : 0 < i₀) (hLt : i₀ < cfg.P.d)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
      EWc ULc ch0 termTok i₀ ch curG curU curEditsList oldOrd sE tok curBatch curBatchWords
      curEdits curEditsWords levelU levelUS D)
    (M : BranchBIntMidKFBL (w := w) (vCap := vCap) (eCap := eCap) A oldPtrs i₀ ch0 ch curG sE s
      tok tokM ordPtr ordWords)
    (next : ChainState cfg.T cfg.P)
    (hNext : next = (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
      { ch with ℓ := ℓ', g := g' } i₀ curG curEnc).1)
    (hReb : UpdateRebuildModelInv w L P wordExp stretchPrec ch i₀ curG ℓ' g' curEnc)
    (hWordExpEq : Psc.wordExp = wordExp) (hInitOrdEq : ToolInitOrdEqOnE cfg.T)
    (hNextN : ∀ j ≤ cfg.P.d, (next.G j).n ≤ next.N₀)
    (hNextRot : ∀ j < cfg.P.d, ordRotWords (chainLevelOrdAbs next j) (next.bran j) ≤
      1 + 2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m)
    (hImpl : ∀ j, i₀ ≤ j → j < cfg.P.d →
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth cfg.T (next.G j) cfg.P.k (next.lvlM j)
          next.N₀ vCap eCap capExp Psc alloc) ∧
      SparseCoreReadoutFootAt fmt L depth cfg.T (next.G j) cfg.P.k (next.lvlM j) next.N₀ vCap
        eCap capExp Psc alloc Rcore p opCore)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hLastImpl :
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
        (next.G cfg.P.d).E).Implements w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L (next.G cfg.P.d) vCap eCap lastMul
          stretchPrec lastAlloc))
    (hLevelSpaceDom : ∀ j gB lB grB oB h, i₀ ≤ j → j < cfg.P.d →
      ordLevelSpace L capExp capLimit
        (alloc 6 [gB, lB, grB, oB, cfg.P.k, next.lvlM j, next.N₀, L, fmt.precision, depth, h])
        (next.lvlM j) next.N₀ (next.G (j + 1)).m ≤ levelSpace j)
    (hLevelCostDom : ∀ j, i₀ ≤ j → j < cfg.P.d →
      updateCoreRebuildLevelCost L capExp cfg Psc next j ≤ levelCost j)
    (hLastSpaceDom : ∀ gB lB h, lastAlloc 1 [gB, lB, L, fmt.precision, h] ≤ lastSpace)
    (hLWord : L < 2 ^ w) (hPWord : P < 2 ^ w) (hWidth : P ≤ 4 * L) (hDepthW : depth < 2 ^ w)
    (hNW : N0 < 2 ^ w)
    (hRoom : s.regs 4 + (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace < 2 ^ w) :
    ∃ (out : State) (cost termTokN : ℕ) (coreTok : ℕ → Rcore.τ),
      Runs w p ω
        (wireBranchBIntSuffixKFBL initCore (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit)
        s .normal out cost ∧
      (∀ r, 70 ≤ r → out.regs r = s.regs r) ∧
      s.regs 4 ≤ out.regs 4 ∧
      out.regs 4 ≤ s.regs 4 + (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ j, i₀ ≤ j → j < cfg.P.d →
        out.mem (A.branchBase + j) = next.bran j ∧
        s.regs 4 ≤ out.mem (A.handleBase + j) ∧ out.mem (A.handleBase + j) ≤ out.regs 4 ∧
        Rcore.rep (out.mem (A.handleBase + j)) (chainLevelOrdAbs next j) (coreTok j) out.mem ∧
        (∀ a, Rcore.foot (out.mem (A.handleBase + j)) (coreTok j) a →
          s.regs 4 ≤ a ∧ a < out.regs 4)) ∧
      (∀ j₁ j₂, i₀ ≤ j₁ → j₁ < cfg.P.d → i₀ ≤ j₂ → j₂ < cfg.P.d → j₁ ≠ j₂ →
        ∀ a, Rcore.foot (out.mem (A.handleBase + j₁)) (coreTok j₁) a →
          ¬ Rcore.foot (out.mem (A.handleBase + j₂)) (coreTok j₂) a) ∧
      (∀ j, i₀ + 1 ≤ j → j < cfg.P.d →
        DynGraphAt out.mem (out.mem (A.levelMeta + cfg.P.d + j)) vCap eCap (next.G j) ∧
        s.regs 4 ≤ out.mem (A.levelMeta + cfg.P.d + j) ∧
        out.mem (A.levelMeta + cfg.P.d + j) + dynGraphSize vCap eCap ≤ out.regs 4 ∧
        EdgeValuesAt out.mem (out.mem (A.levelMeta + j)) 4 L fmt.precision (next.G j).E
          (next.toTreeChain.chainLen next.ℓ j) ∧
        s.regs 4 ≤ out.mem (A.levelMeta + j) ∧
        out.mem (A.levelMeta + j) + eCap * L ≤ out.regs 4 ∧
        (∀ r, i₀ ≤ r → r < cfg.P.d →
          (∀ a, out.mem (A.levelMeta + j) ≤ a → a < out.mem (A.levelMeta + j) + eCap * L →
            ¬ Rcore.foot (out.mem (A.handleBase + r)) (coreTok r) a) ∧
          (∀ a, out.mem (A.levelMeta + cfg.P.d + j) ≤ a →
            a < out.mem (A.levelMeta + cfg.P.d + j) + dynGraphSize vCap eCap →
            ¬ Rcore.foot (out.mem (A.handleBase + r)) (coreTok r) a)) ∧
        (∀ a, out.mem (A.levelMeta + j) ≤ a → a < out.mem (A.levelMeta + j) + eCap * L →
          ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
            (next.G cfg.P.d).E).foot (out.mem (A.handleBase + cfg.P.d)) termTokN a) ∧
        (∀ a, out.mem (A.levelMeta + cfg.P.d + j) ≤ a →
          a < out.mem (A.levelMeta + cfg.P.d + j) + dynGraphSize vCap eCap →
          ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
            (next.G cfg.P.d).E).foot (out.mem (A.handleBase + cfg.P.d)) termTokN a)) ∧
      out.mem (A.branchBase + cfg.P.d) = next.lastBran ∧
      s.regs 4 ≤ out.mem (A.handleBase + cfg.P.d) ∧
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
        (next.G cfg.P.d).E).rep
        (out.mem (A.handleBase + cfg.P.d)) (next.lastK, next.lastLSFs) termTokN out.mem ∧
      (∀ a, (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
        (next.G cfg.P.d).E).foot (out.mem (A.handleBase + cfg.P.d)) termTokN a →
          s.regs 4 ≤ a ∧ a < out.regs 4) ∧
      (∀ j, i₀ ≤ j → j < cfg.P.d → ∀ a,
        (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
          (next.G cfg.P.d).E).foot (out.mem (A.handleBase + cfg.P.d)) termTokN a →
        ¬ Rcore.foot (out.mem (A.handleBase + j)) (coreTok j) a) ∧
      (∀ a < s.regs 4,
        (a < A.handleBase + i₀ ∨ A.handleBase + cfg.P.d < a) →
        (a < A.branchBase + i₀ ∨ A.branchBase + cfg.P.d < a) →
        ((a < A.levelMeta + (i₀ + 1) ∨ A.levelMeta + cfg.P.d ≤ a) ∧
         (a < A.levelMeta + cfg.P.d + (i₀ + 1) ∨ A.levelMeta + 2 * cfg.P.d ≤ a)) →
        out.mem a = s.mem a) ∧
      cost + (Finset.Ico i₀ cfg.P.d).sum
          (fun j => Rcore.phi (out.mem (A.handleBase + j)) (coreTok j) out.mem) ≤
        (Finset.Ico i₀ cfg.P.d).sum (fun j => levelCost j + 9) +
          lastMul * (cfg.L.cost (next.G cfg.P.d) + 1) + 89 := by
  obtain ⟨hFloor, _, _, _, _, _, hr73, _, hr75, hr76, hr77, hr78, hr82, hr83, _, _, hr94, hr95,
    hr96, _, hr98, _⟩ := I.regs
  obtain ⟨hPre, hNG, _, hNLvlM, hNN0, _, _, hPrevAbsEq, hNOrd, _, hLenEq, hModelLevel,
    hModelLast⟩ :=
    branchBIntNext_facts (fmt := fmt) (Psc := Psc) ch curG ℓ' g' curEnc i₀ next hNext hPos hLt
      hReb hWordExpEq E.prec hInitOrdEq hNextN hNextRot
  have hN : ch.N₀ = N0 := I.modelFrame.2.2.2.2.2.1
  have hPrevBr : next.bran (i₀ - 1) = ch.bran (i₀ - 1) := (hPre (i₀ - 1) (by omega)).2.2.1
  -- the layout facts
  have hHLt := S.handleLt
  have hHBLt := S.hbLt
  have hBBLt := S.bbLt
  have hLvlMLt := S.lvlMLt
  have hMetaLt := S.metaLt
  have hRCLt := S.rcLt
  have hGLt := S.gLt i₀ hLt
  have hLLt := S.lLt i₀ hLt
  have hRCH := S.sepRCH
  have hRCM := S.sepRCM
  have hRCLM := S.sepRCLM
  have hsE4 : sE.regs 4 < s.regs 4 := by have := M.heapLo; have := M.ord.2.2.1; omega
  have hSelLt : A.selBase < sE.regs 4 := by omega
  have hs4W : s.regs 4 < 2 ^ w := by omega
  -- the words below the select base that the first part kept
  have hKeepS (z : ℕ) (hz : z < A.selBase)
      (hnf : ∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) z)
      (hg : ¬ (A.gPtr0 i₀ ≤ z ∧ z < A.gPtr0 i₀ + dynGraphSize vCap eCap))
      (hrc : z ≠ A.rcBase + i₀) : s.mem z = sE.mem z :=
    M.frame z (by omega) (fun j _ hj => hnf j hj) (by omega) hrc (Or.inl (by omega))
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := I.cells i₀ hLt
  have hkPos : 0 < cfg.P.k := by omega
  -- the start data of level `i₀`
  obtain ⟨hN0Pos, hN0Foot, hN0Sep⟩ := I.n0Word
  have hCellN : s.mem (A.lvlMTable - 1) = next.N₀ := by
    rw [hKeepS _ (by omega) hN0Foot
      (fun ⟨h1, h2⟩ => by rcases (hN0Sep i₀ hLt).1 with h | h <;> omega)
      (hN0Sep i₀ hLt).2.2.2, I.hdrCell, hNN0, hN]
  have hCellL : s.mem (A.levelMeta + i₀) = A.lPtr0 i₀ := by
    rw [hKeepS _ (by omega) (fun r hr => ((I.static r hr).2.2.2.1 i₀ hLt).2.1)
      (fun ⟨h1, h2⟩ => by obtain ⟨_, _, _, _, _, g6, _⟩ := S.gSep i₀ hLt _ h1 h2; omega)
      (by omega), c8]
  have hLvlMs : ∀ j, i₀ ≤ j → j < cfg.P.d → s.mem (A.lvlMTable + j) = next.lvlM j :=
    fun j _ hj => by
      rw [hKeepS _ (by omega) (fun r hr => ((I.static r hr).2.2.2.1 j hj).1)
        (fun ⟨h1, h2⟩ => by obtain ⟨_, _, _, _, g5, _⟩ := S.gSep i₀ hLt _ h1 h2; omega)
        (by omega), (I.cells j hj).2.1, hNLvlM]
  have hG0 : DynGraphAt s.mem (A.gPtr0 i₀) vCap eCap (next.G i₀) := hNG ▸ M.graph
  have hLen0 : EdgeValuesAt s.mem (A.lPtr0 i₀) 4 L fmt.precision (next.G i₀).E
      (next.toTreeChain.chainLen next.ℓ i₀) := by
    rw [hNG, hLenEq, E.prec]
    refine (I.lensEq hLt).congr (fun e he t ht => ?_)
    have heL : e * L + L ≤ eCap * L := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (M.graph.2.2.1 e he))
    have hb1 : A.lPtr0 i₀ ≤ A.lPtr0 i₀ + e * L + t := by omega
    have hb2 : A.lPtr0 i₀ + e * L + t < A.lPtr0 i₀ + eCap * L := by omega
    obtain ⟨_, _, _, _, _, _, l7, _⟩ := S.lSep i₀ hLt _ hb1 hb2
    exact hKeepS _ (by omega) (fun r hr => (I.static r hr).2.2.2.2.2 i₀ hLt _ hb1 hb2)
      (fun ⟨h1, h2⟩ => by
        obtain ⟨_, _, _, _, _, _, _, _, g9⟩ := S.gSep i₀ hLt _ h1 h2
        have := (g9 i₀ hLt).1; omega) (by omega)
  have hOrd0 : i₀ < cfg.P.d → ∃ oWords,
      OrdListAt s.mem ordPtr (next.levelOrd i₀) oWords ∧
      (∀ j < oWords, s.mem (ordPtr + j) < 2 ^ w) ∧
      ordPtr + oWords ≤ s.regs 4 ∧
      oWords ≤ 2 * (next.G i₀).n + 2 * (next.G i₀).m + 1 := fun _ => by
    refine ⟨ordWords, hNOrd ▸ M.ord.1, M.ord.2.2.2, M.ord.2.2.1, ?_⟩
    have h1 := M.ord.2.1
    have h2 := hNextRot (i₀ - 1) (by omega)
    rw [hPrevAbsEq (i₀ - 1) (by omega), hPrevBr, show i₀ - 1 + 1 = i₀ by omega] at h2
    omega
  -- the space of each rebuilt level
  let restSp : ℕ → ℕ := fun j =>
    ordLevelSpace L capExp capLimit 0 (next.lvlM j) next.N₀ (next.G (j + 1)).m
  let coreInitSpace : ℕ → ℕ := fun j => levelSpace j - restSp j
  have hOrdSpaceAdd : ∀ x j,
      ordLevelSpace L capExp capLimit x (next.lvlM j) next.N₀ (next.G (j + 1)).m =
        x + restSp j := fun x j => by
    unfold restSp ordLevelSpace
    simp only [Nat.zero_add, Nat.add_assoc]
  have hInitSpaceLe : ∀ j, i₀ ≤ j → j < cfg.P.d → ∀ gB lB grB oB h,
      alloc 6 [gB, lB, grB, oB, cfg.P.k, next.lvlM j, next.N₀, L, fmt.precision, depth, h] ≤
        coreInitSpace j := fun j hj1 hj2 gB lB grB oB h => by
    have hdom := hLevelSpaceDom j gB lB grB oB h hj1 hj2
    rw [hOrdSpaceAdd] at hdom
    dsimp only [coreInitSpace]; omega
  have hLvlSpaceLe : ∀ j, i₀ ≤ j → j < cfg.P.d →
      ordLevelSpace L capExp capLimit (coreInitSpace j) (next.lvlM j) next.N₀
        (next.G (j + 1)).m ≤ levelSpace j := fun j hj1 hj2 => by
    have hdom := hLevelSpaceDom j 0 0 0 0 0 hj1 hj2
    rw [hOrdSpaceAdd] at hdom ⊢
    dsimp only [coreInitSpace]; omega
  have hR (r : ℕ) (h70 : 70 ≤ r) (h99 : r ≠ 99) : s.regs r = sE.regs r := M.regs r h70 h99
  exact wireBranchBIntSuffixKFBL_runs (w := w) (L := L) (depth := depth) (vCap := vCap)
    (eCap := eCap) (capExp := capExp) (capLimit := capLimit) (init := initCore)
    (coreLenProc := coreLenProc) (edgeProc := edgeProc) (signExt := signExt) (mul := mul)
    (intDiv := intDiv) (copy := copy) (lastInit := lastInit) (first := i₀)
    (handleBase := A.handleBase) (branchBase := A.branchBase) (lvlMTable := A.lvlMTable)
    (levelLens := A.levelMeta) (heapFloor := s.regs 4) (lastMul := lastMul)
    (stretchPrec := stretchPrec) (cur := s.regs 4) (gPtr := A.gPtr0 i₀) (lPtr := A.lPtr0 i₀)
    (ordPtr := ordPtr) (handle := A.handle) (fmt := fmt) (T := cfg.T) (LT := cfg.L)
    (CP := cfg.P) (P := Psc) (allocation := alloc) (lastAlloc := lastAlloc)
    (coreInitSpace := coreInitSpace) (nextM := fun j => (next.G (j + 1)).m) (Rcore := Rcore)
    (p := p) (op := opCore) (opLast := opLast) (st := s) (ω := ω)
    next levelSpace levelCost lastSpace (le_of_lt hLt) E.loc E.four (E.prec ▸ hWidth) hLWord
    (E.prec ▸ hPWord) hDepthW E.dW hkPos E.kW (by rw [hNN0, hN]; exact hNW)
    (by have := E.w16; omega)
    ⟨rfl, M.r6, M.r9, (hR 73 (by decide) (by decide)).trans hr73,
      (hR 75 (by decide) (by decide)).trans hr75, (hR 76 (by decide) (by decide)).trans hr76,
      (hR 77 (by decide) (by decide)).trans hr77, (hR 78 (by decide) (by decide)).trans hr78,
      (hR 82 (by decide) (by decide)).trans hr82, (hR 83 (by decide) (by decide)).trans hr83,
      (hR 94 (by decide) (by decide)).trans hr94,
      (hR 95 (by decide) (by decide)).trans (hr95.trans E.prec.symm),
      (hR 96 (by decide) (by decide)).trans hr96, (hR 98 (by decide) (by decide)).trans hr98⟩
    ⟨hCellN, hCellL⟩ ⟨by omega, by omega, by omega, by omega⟩ le_rfl (by omega) (by omega)
    (by omega) (by omega) S.sepHB S.sepHM S.sepBM S.sepHL S.sepBL S.sepML hLvlMs hG0 hLen0 hOrd0
    (by omega) (by omega)
    (fun a h1 h2 => by
      obtain ⟨_, _, g3, g4, _, g6, _⟩ := S.gSep i₀ hLt a h1 h2
      exact ⟨by omega, by omega, by omega⟩)
    (fun a h1 h2 => by
      obtain ⟨_, _, l3, l4, _, l6, _⟩ := S.lSep i₀ hLt a h1 h2
      exact ⟨by omega, by omega, by omega⟩)
    M.zero hImpl hcapLim hInitSpaceLe hCoreLenProc E.edgeP E.signC E.mulC E.divC E.copyC
    hLastImpl hModelLevel hModelLast hLvlSpaceLe hLevelCostDom hLastSpaceDom hRoom (tok 0)

end MinCostFlow.MinRatio

end
