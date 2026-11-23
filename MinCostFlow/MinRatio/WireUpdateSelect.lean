module

public import MinCostFlow.MinRatio.SelectUpdatePostCore
public import MinCostFlow.MinRatio.SelectUpdatePostCoreCost
public import MinCostFlow.MinRatio.OrdSelSpecs
public import MinCostFlow.MinRatio.WireChainCoreBodyKFBL
public import MinCostFlow.MinRatio.WireShiftDeepSelectAux
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Composition of `OrdChainUpdateCoreSpecWExtKFBL` and `selectUpdatePostCoreBody` (`WireUpdateSelect`)

Defines the 7-argument deterministic wrapper `ordChainUpdateCoreSelBody coreProc postCoreProc`
matching the calling convention of `OrdChainUpdateCoreSpecWKFBLSel` (`[root, uIntBuf, editsPtr,
editWords, g, l, heap]`):

1. Calls `coreProc [root, uIntBuf, editsPtr, editWords, g, l, heap]` to obtain `midHeap`,
   establishing `Rrep.rep`, `SolverLevelCapsInv`, `PathTreeNumericInv`/`OffTreeRecInv`/
   `OffTreeRecBound` at `(B', R') ≤ (B, R)`, `UpdateCoreLevelLink`, and `UpdateCoreSelectOutAt`
   at `selOutBase := heap`.
2. Calls `postCoreProc [root, heap, midHeap]` (`selectUpdatePostCoreBody`) to refresh the select
   metadata table, level-0 gradients, non-rebuilt interior blocks, rebuilt suffix blocks and
   potentials, and the select heap, returning `nextHeap`.

Proves `ordChainUpdateCoreSelBody_runs`: given `OrdChainUpdateCoreSpecWExtKFBL` for `coreProc`
(instantiated at `B_bound := B`, `R_bound := R`), the post-core procedure contracts, the model/fit
callbacks, and the `uWords` sum bound, `ordChainUpdateCoreSelBody` satisfies every postcondition
of `OrdChainUpdateCoreSpecWKFBLSel` (including `SolverSelectRegionInv`, `SolverSelectInv`,
`PathTreeNumericInv`/`OffTreeRecInv`/`OffTreeRecBound` at `(B, R)`, full frame, footprint, and
amortized potential bound).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM.Machine Num DynSpanner.Program
  SparseCore SparseCore.Program

/-- Deterministic 7-argument select-aware chain-update wrapper calling `coreProc` followed by
`postCoreProc [root, heap, midHeap]` (`selectUpdatePostCoreBody`). -/
def ordChainUpdateCoreSelBody (coreProc postCoreProc : ℕ) : Stmt :=
  .seq (.call 10 coreProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6])
  (.seq (.call 11 postCoreProc [.reg 0, .reg 6, .reg 10])
    (.ret (.reg 11)))

theorem ordChainUpdateCoreSelBody_noRand (coreProc postCoreProc : ℕ) :
    (ordChainUpdateCoreSelBody coreProc postCoreProc).NoRand := by
  simp [ordChainUpdateCoreSelBody, Stmt.NoRand]

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM.Machine Num DynSpanner.Program
  SparseCore SparseCore.Program

private lemma offTreeRecInv_mono_B {cfg : Alg2Config} {model : Alg2State cfg} {L : ℕ}
    {mem : ℕ → ℕ} {edgeRecords : ℕ} {B₁ B₂ : ℤ}
    (h : OffTreeRecInv model L mem edgeRecords B₁) (hle : B₁ ≤ B₂) :
    OffTreeRecInv model L mem edgeRecords B₂ :=
  ⟨fun e he hnt val hv => (h.1 e he hnt val hv).trans hle, h.2⟩

private lemma offTreeRecBound_mono_B {cfg : Alg2Config} {model : Alg2State cfg} {L : ℕ}
    {mem : ℕ → ℕ} {edgeRecords : ℕ} {B₁ B₂ : ℤ}
    (h : OffTreeRecBound model L mem edgeRecords B₁) (hle : B₁ ≤ B₂) :
    OffTreeRecBound model L mem edgeRecords B₂ := fun e he hnt val hv =>
  let ⟨h1, h2, h3⟩ := h e he hnt val hv
  ⟨h1.trans hle, h2.trans hle, h3.trans hle⟩

private lemma selectMetaTableAt_of_agree_pc {m₁ m₂ : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    (h : SelectMetaTableAt m₁ mloc)
    (hag : ∀ a, mloc.metaBase ≤ a → a < mloc.metaBase + selectLevelMetaSize mloc.d → m₂ a = m₁ a) :
    SelectMetaTableAt m₂ mloc :=
  h.of_agree hag

private lemma selOutWordsAt_len_le {foot : ℕ → Prop} {lo hi ptr len : ℕ}
    (h : SelOutWordsAt foot lo hi ptr len) : len ≤ hi - lo := by
  rcases h with ⟨h1, h2, _⟩
  omega

private lemma ordChainUpdateCoreSelBody_stitch {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {coreProc postCoreProc root uIntBuf editsPtr editWords g l heap midHeap nextHeap pos
      cCore cPost : ℕ}
    {bCore bPost : Stmt} {mem : ℕ → ℕ} {stCore stPost : State}
    (hCoreAt : p.procs[coreProc]? = some bCore)
    (hPostAt : p.procs[postCoreProc]? = some bPost)
    (hrCore : Runs w p ω bCore
      (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
      (.returned midHeap) stCore cCore)
    (hrPost : Runs w p ω bPost
      (startState [root, heap, midHeap] stCore.mem stCore.pos)
      (.returned nextHeap) stPost cPost) :
    ∃ out cost,
      Runs w p ω (ordChainUpdateCoreSelBody coreProc postCoreProc)
        (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
        (.returned nextHeap) out cost ∧
      out.mem = stPost.mem ∧
      cost ≤ cCore + cPost + 40 := by
  let s0 := startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos
  have hr1 : Runs w p ω
      (.call 10 coreProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6])
      s0 .normal { stCore with regs := Function.update s0.regs 10 midHeap } (cCore + 8) :=
    runs_call_iff.mpr ⟨[root, uIntBuf, editsPtr, editWords, g, l, heap], bCore,
      .returned midHeap, stCore, cCore,
      by simp [evalArgs, Expr.eval, s0, startState],
      hCoreAt, hrCore, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  let s1 : State := { stCore with regs := Function.update s0.regs 10 midHeap }
  have hr2 : Runs w p ω (.call 11 postCoreProc [.reg 0, .reg 6, .reg 10])
      s1 .normal { stPost with regs := Function.update s1.regs 11 nextHeap } (cPost + 4) :=
    runs_call_iff.mpr ⟨[root, heap, midHeap], bPost, .returned nextHeap, stPost, cPost,
      by simp [evalArgs, Expr.eval, s1, s0, startState],
      hPostAt, hrPost, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  let s2 : State := { stPost with regs := Function.update s1.regs 11 nextHeap }
  have hr3 : Runs w p ω (.ret (.reg 11)) s2 (.returned nextHeap) s2 2 :=
    runs_ret_iff.mpr ⟨nextHeap, by simp [Expr.eval, s2], rfl, rfl, rfl⟩
  have hr23 := runs_seq_iff.mpr (Or.inr ⟨s2, _, _, hr2, hr3, rfl⟩)
  have hrAll := runs_seq_iff.mpr (Or.inr ⟨s1, _, _, hr1, hr23, rfl⟩)
  exact ⟨s2, (cCore + 8) + ((cPost + 4) + 2 + 1) + 1, hrAll, rfl, by omega⟩

set_option maxHeartbeats 1600000 in
/-- End-to-end composition of any inner chain-core run satisfying `OrdChainCoreExtPost`
(`coreProc`, at budget `(B, R)` and inner sizes `innerSpace, innerFixed, innerToolMul,
innerTreeMul`) with `selectUpdatePostCoreBody` (`postCoreProc`) via `ordChainUpdateCoreSelBody`.
Proves every postcondition of `OrdChainUpdateCoreSpecWKFBLSel` (including `SolverSelectRegionInv`,
`SolverSelectInv`, `SolverLevelCapsInv`, `PathTreeNumericInv`/`OffTreeRecInv`/`OffTreeRecBound` at
`(B, R)`, full frame, footprint, and amortized potential bound). -/
theorem ordChainUpdateCoreSelBody_runs_of_corePost
    {w L P E m V psi k epsExp drainUnit capExp vCap eCap pLast slot K c uWordsMul evalSpace evalCost
      coreProc postCoreProc tableWriteProc g0Proc copyOne filterPres
      fPhiLenLoopProc fPhiLenLvlProc dgApplyBatch delEdgeList batchCopySplits coreLenFill coreLenEdge
      embLoopProc embLvlProc embUpdateFromList
      sufBlocksProc initIntLoop fillIntProc dgCopyProc filterAbs embCopyProc fillLast phiLoop phiFillProc
      heapPhaseProc heapPrefLoop updLvlProc rebSufProc : ℕ}
    {innerSpace innerFixed uWordsFix : ℕ → ℕ} {innerToolMul innerTreeMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G G₀' : MGraph}
    {σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {initialGraph : ℕ → MGraph} {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {reembFn : ToolReembFn cfg.T} {pot : cfg.T.State → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {op : ℕ → ℕ} {ω : ℕ → Bool}
    {bCore : Stmt}
    {root uIntBuf editsPtr editWords g l heap pos : ℕ}
    {mem0 mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {sg : SelectGhost} {U : List Update} {B R : ℤ}
    (hTP : cfg.TP.Valid) (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (hPot : ToolReembPotFacts cfg.T pot)
    (hfmt4 : fmt.limbBits = 4) (hfmtP : fmt.precision = P) (hlocalCore : Rcore.Local)
    (hw16 : 16 < 2 ^ w) (hw10 : 10 ≤ w) (hLpos : 0 < L) (hLkW : L < 2 ^ w)
    (hpLastW : pLast < 2 ^ w) (hkW : cfg.P.k < 2 ^ w) (hSlotW : slot < 2 ^ w)
    (hdPos : 0 < cfg.P.d) (heCapPos : 0 < eCap) (heCapLeHeap : eCap ≤ sg.loc.cap)
    (hK : selectProcessEdgeCost sg.loc.cap L evalCost + (18 * slot + 160) + 80 ≤ K)
    -- Inner chain-core placement, `OrdChainCoreExtPost` at `(B, R)`, and meta-disjointness
    (hbCore : p.procs[coreProc]? = some bCore)
    (hCorePost : OrdChainCoreExtPost w L P m V psi k epsExp drainUnit capExp vCap eCap cfg reembFn
      Rcore p innerSpace innerFixed innerToolMul innerTreeMul B R bCore root uIntBuf editsPtr
      editWords g l heap pos ω mem0 mem model tok U)
    (hCoreDisj : ∀ (nextHeap cost : ℕ) (out : State) (tok' : SolverToken cfg L Rcore),
      Runs w p ω bCore (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
        (.returned nextHeap) out cost →
      tok'.table = tok.table →
      SolverLevelMetaDisjAt vCap eCap tok' out.mem)
    -- Post-core procedure placement
    (hpPostCore : p.procs[postCoreProc]? =
      some (selectUpdatePostCoreBody tableWriteProc g0Proc fPhiLenLoopProc embLoopProc
        sufBlocksProc heapPhaseProc))
    -- Pre-state select, frame, and KFBL chain invariants
    (hrep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hPot0 : sg.reembPot = chainReembPot pot model.chain)
    (hReg0 : SolverSelectRegionInv G L P m E pLast slot vCap eCap model
      ((solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok) tok sg mem0)
    (hTags0 : ∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a)
    (hFootLt : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a ∨ sg.owned a →
      a < uIntBuf)
    (huLeHeap : uIntBuf ≤ heap)
    (hCoreKFBL :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      UpdateCoreModelInvKFBL model U gVec lVec)
    -- Post-core model, fit, and amortized-cost facts at `modelPre`
    (hModNew :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      SelectModelInv (alg2PreResetState cfg model U gVec lVec) G₀' σ' σ'_mwu γ'_ℓ γ'_c)
    (hgBoundNew :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ e ∈ (modelPre.chain.G 0).E, |modelPre.chain.g e| ≤ (2 : ℝ) ^ E)
    (hgEqNew :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ e ∈ (modelPre.chain.G 0).E, modelPre.chain.g e = modelPre.extg (modelPre.intToExt e))
    (hgFitNew :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ e ∈ (modelPre.chain.G 0).E, ∀ z : ℤ,
        (z : ℝ) / (2 : ℝ) ^ P = modelPre.chain.g e → Num.Fits 4 L z ∧ Num.Fits 4 L (-z))
    (hVcap :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ j ≤ cfg.P.d, ∀ v ∈ (modelPre.chain.G j).V, v < vCap)
    (hEcap :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ j ≤ cfg.P.d, ∀ e ∈ (modelPre.chain.G j).E, e < eCap)
    (hOldEcap : ∀ j ≤ cfg.P.d, (model.chain.G j).m ≤ eCap)
    (hNewVcap :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ j ≤ cfg.P.d, (modelPre.chain.G j).n ≤ vCap)
    (hNewEcap :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ j ≤ cfg.P.d, (modelPre.chain.G j).m ≤ eCap)
    (hLwMaxW : ordLevelLwMax L capExp (levelM cfg.TP cfg.P 0) cfg.N₀ < 2 ^ w)
    (hLenFitAll :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ j < cfg.P.d, ∀ e ∈ (modelPre.chain.G j).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧
          (q : ℝ) / (2 : ℝ) ^ P = modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (j + 1) e)
    (hLenFitLast :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ (Bblk : SelectBlocksLoc) (firstReb : ℕ), firstReb ≤ cfg.P.d →
        ∀ e ∈ (modelPre.chain.G cfg.P.d).E, ∀ prevM : ℕ → ℕ,
          EdgeValuesAt prevM (Bblk.lenPtr (cfg.P.d - 1)) 4 L P (modelPre.chain.G cfg.P.d).E
            (modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ cfg.P.d) →
          Num.Fits 4 L (Num.intVal prevM (Bblk.lenPtr (cfg.P.d - 1) + e * L) 4 L * (2 : ℤ) ^ pLast) ∧
          ∃ q : ℤ, Num.Fits 4 L q ∧
            (q : ℝ) / (2 : ℝ) ^ (P + pLast) =
              modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (cfg.P.d + 1) e)
    (hEmbSlot :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ j < cfg.P.d, ∀ e ∈ (modelPre.chain.toTreeChain.activeCore j).E,
        (mWalkEncode (modelPre.chain.toTreeChain.activeEmb j e)).length ≤ slot)
    (hPhiBdStep :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      let PhiBd := fun φ j =>
        SelectPhiBoundedAt modelPre.chain.toTreeChain φ (2 * m + 2) ((2 : ℝ) ^ E) j
      ∀ j ≤ cfg.P.d, ∀ (φ : ℕ → ℕ → ℝ) (φj : ℕ → ℝ),
        (∀ k < j, SelectPotInvAt modelPre.chain.toTreeChain modelPre.chain.g φ k) →
        (∀ k < j, PhiBd φ k) →
        (∀ v ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.V,
          ∃ r ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.V,
            (modelPre.chain.toTreeChain.activeLSF j).F.F.Connected v r ∧
            φj v = walkInner (potGrad modelPre.chain.toTreeChain modelPre.chain.g φ j)
              ((modelPre.chain.toTreeChain.activeLSF j).F.F.forestPath v r)) →
        ∀ k < j + 1, PhiBd (Function.update φ j φj) k)
    (hPhiFit :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      let PhiBd := fun φ j =>
        SelectPhiBoundedAt modelPre.chain.toTreeChain φ (2 * m + 2) ((2 : ℝ) ^ E) j
      ∀ j ≤ cfg.P.d, ∀ φ' : ℕ → ℕ → ℝ,
        (∀ k < j, SelectPotInvAt modelPre.chain.toTreeChain modelPre.chain.g φ' k) →
        (∀ k < j, PhiBd φ' k) →
        (∀ e ∈ (modelPre.chain.toTreeChain.activeLSF j).F.F.E,
          PotGradEvalFits 4 L P modelPre.chain.toTreeChain modelPre.chain.g φ' j e) ∧
        ForestWalkFits 4 L P (modelPre.chain.toTreeChain.activeLSF j).F.F
          (potGrad modelPre.chain.toTreeChain modelPre.chain.g φ' j))
    -- Post-core link & amortized-cost callbacks given `(firstReb, levelU, levelUS, diffLists)`
    (hLinkFacts :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      let PhiBd := fun φ j =>
        SelectPhiBoundedAt modelPre.chain.toTreeChain φ (2 * m + 2) ((2 : ℝ) ^ E) j
      ∀ (memCore : ℕ → ℕ) (midHeap firstReb : ℕ)
        (levelU levelUS : ℕ → List Update) (diffLists : ℕ → LevelDiffLists)
        (tok' : SolverToken cfg L Rcore),
        UpdateCoreLevelLink model.chain modelPre.chain firstReb levelU levelUS →
        UpdateCoreSelectOutAt w P L capExp vCap eCap reembFn
          ((solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok')
          memCore heap midHeap firstReb model.chain modelPre.chain levelU levelUS diffLists →
        ∃ ins : ℕ → ℕ → Prop,
          (firstReb = 0 → (modelPre.chain.G 0).E = Finset.range (modelPre.chain.G 0).m) ∧
          (0 < firstReb → ∀ e ∈ (modelPre.chain.G 0).E, e ∈ (model.chain.G 0).E →
            modelPre.chain.g e = model.chain.g e) ∧
          (0 < firstReb → ∀ e ∈ (modelPre.chain.G 0).E, e ∈ (model.chain.G 0).E →
            modelPre.chain.ℓ e = model.chain.ℓ e) ∧
          (∀ j < min firstReb cfg.P.d,
            let C := model.chain.toTreeChain
            let C' := modelPre.chain.toTreeChain
            (∀ e ∈ (C'.activeLSF j).F.F.E, Update.delete e ∉ levelU j) ∧
            (C'.activeLSF j).F.F.E ⊆ (C.activeLSF j).F.F.E ∧
            (∀ e ∈ (diffLists j).uS, e < eCap) ∧
            (∀ e ∈ (diffLists j).reemb, e < eCap) ∧
            (∀ e ∈ (C'.G j).E, e ∉ (diffLists j).uG →
              e ∈ (C.G j).E ∧ C'.chainLen modelPre.chain.ℓ (j + 1) e = C.chainLen model.chain.ℓ (j + 1) e) ∧
            (∀ e ∈ (C'.activeCore j).E,
              e ∉ (diffLists j).uG → e ∉ (diffLists j).fDel → e ∉ (diffLists j).uS →
              e ∉ (diffLists j).reemb →
              e ∈ (C.activeCore j).E ∧ C'.activeEmb j e = C.activeEmb j e) ∧
            SparseCoreOrdInput cfg.T cfg.P.k (modelPre.chain.lvlM j) modelPre.chain.N₀
              (modelPre.chain.scState j) (modelPre.chain.G j) (modelPre.chain.levelOrd j)
              (modelPre.chain.updCount j) ∧
            modelPre.chain.bran j < cfg.P.k ∧
            LevelDiffCovers C C' j ins (diffLists j)) ∧
          (∀ j, j < firstReb → j ≤ cfg.P.d →
            ∀ f ∈ (modelPre.chain.G j).E, f ∈ (model.chain.G j).E → ¬ ins j f →
              (modelPre.chain.toTreeChain.activeLSF j).wstr f =
                (model.chain.toTreeChain.activeLSF j).wstr f) ∧
          (∀ j, j + 1 < firstReb → j < cfg.P.d →
            ∀ f ∈ (modelPre.chain.G (j + 1)).E, f ∈ (model.chain.G (j + 1)).E →
              ins j f → ins (j + 1) f) ∧
          (let φS := fun j =>
            if j < min firstReb cfg.P.d then splitPot (sg.φ j) (batchSplits (levelU j)) else sg.φ j
           0 < firstReb → EndPotAgree model.chain.toTreeChain modelPre.chain.toTreeChain sg.φ φS (firstReb - 1)) ∧
          (let φS := fun j =>
            if j < min firstReb cfg.P.d then splitPot (sg.φ j) (batchSplits (levelU j)) else sg.φ j
           ∀ j < firstReb, j ≤ cfg.P.d →
            SelectPotInvAt modelPre.chain.toTreeChain modelPre.chain.g φS j) ∧
          (let φS := fun j =>
            if j < min firstReb cfg.P.d then splitPot (sg.φ j) (batchSplits (levelU j)) else sg.φ j
           ∀ j < firstReb, j ≤ cfg.P.d → PhiBd φS j) ∧
          (firstReb = cfg.P.d + 1 →
            modelPre.chain.G cfg.P.d = model.chain.G cfg.P.d ∧
            modelPre.chain.toTreeChain.activeLSF cfg.P.d = model.chain.toTreeChain.activeLSF cfg.P.d ∧
            (∀ e ∈ (modelPre.chain.G cfg.P.d).E,
              modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (cfg.P.d + 1) e =
                model.chain.toTreeChain.chainLen model.chain.ℓ (cfg.P.d + 1) e) ∧
            (∀ f ∈ (modelPre.chain.G cfg.P.d).E, ¬ ins cfg.P.d f)) ∧
          (∀ j < min firstReb cfg.P.d, (diffLists j).uG.length ≤ (levelU j).length) ∧
          (∀ j < min firstReb cfg.P.d,
            ReembCostBound (diffLists j).reemb
              (cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j)) c
              (pot (model.chain.scState j)) (pot (modelPre.chain.scState j))) ∧
          ((Finset.range (min firstReb cfg.P.d)).sum (fun j => memCore (heap + 1 + 12 * j + 11)) ≤
            uWordsMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) + uWordsFix U.length) ∧
          ((Finset.range (min firstReb cfg.P.d)).sum (fun j => (levelU j).length) ≤
            2 * (modelPre.chain.totalRuntime - model.chain.totalRuntime)) ∧
          ((Finset.range (min firstReb cfg.P.d)).sum (fun j => (diffLists j).uS.length) ≤
            2 * (modelPre.chain.totalRuntime - model.chain.totalRuntime)) ∧
          ((Finset.range (min firstReb cfg.P.d)).sum (fun j => (diffLists j).fDel.length) ≤
            modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates) ∧
          ((Finset.range (min firstReb cfg.P.d)).sum
              (fun j => cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (model.chain.scState j)) +
            (Finset.Ico firstReb cfg.P.d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) ≤
            modelPre.chain.totalRuntime - model.chain.totalRuntime) ∧
          (firstReb < cfg.P.d →
            (Finset.Ico firstReb cfg.P.d).sum (fun j => (modelPre.chain.G j).m) ≤
              modelPre.chain.totalRuntime - model.chain.totalRuntime ∧
            (modelPre.chain.G cfg.P.d).m ≤ modelPre.chain.totalRuntime - model.chain.totalRuntime) ∧
          (firstReb < cfg.P.d →
            (model.chain.G firstReb).m ≤ 2 * (modelPre.chain.totalRuntime - model.chain.totalRuntime)) ∧
          (firstReb = 0 →
            (modelPre.chain.G 0).m ≤ modelPre.chain.totalRuntime - model.chain.totalRuntime))
    -- Post-core sub-procedure placements and contracts
    (hTableWrite : ∀ (Bblk : SelectBlocksLoc) (metaBase : ℕ),
      MeetsContract w p tableWriteProc
        (selTableWriteContract w Bblk metaBase (solverLevelMetaAddr tok.table cfg.P.d) pLast))
    (hpG0 : p.procs[g0Proc]? = some (selUpdateG0Body copyOne filterPres))
    (hCopyOne : ∀ val : ℤ, MeetsContract w p copyOne (selCopyG0OneContract w eCap val))
    (hFilterPres : ∀ L' : List ℕ, MeetsContract w p filterPres (selFilterPresentContract w L'))
    (hpFPLLoop : p.procs[fPhiLenLoopProc]? = some (selectUpdateFPhiLenLoopBody fPhiLenLoopProc fPhiLenLvlProc))
    (hpFPLLvl : p.procs[fPhiLenLvlProc]? =
      some (selectUpdateFPhiLenLevelBody dgApplyBatch delEdgeList batchCopySplits filterPres coreLenFill))
    (hDgBatch : ∀ (G0 F0 : MGraph) (U0 : List Update) (uW : ℕ),
      MeetsContract w p dgApplyBatch (dgApplyBatchContract w vCap eCap G0 F0 U0 uW))
    (hDelList : ∀ (F0 : MGraph) (fDel : List ℕ),
      MeetsContract w p delEdgeList (dgDeleteEdgeListContract w vCap eCap F0 fDel))
    (hSplits : ∀ (G0 : MGraph) (U0 : List Update) (uW : ℕ) (φ0 : ℕ → ℝ),
      MeetsContract w p batchCopySplits (selBatchCopySplitsContract w vCap P G0 U0 uW φ0))
    (hpCoreLen : p.procs[coreLenFill]? = some (selCoreLenFillBody coreLenEdge))
    (hCoreLenEdge : MeetsContract w p coreLenEdge (selCoreLenEdgeContract w P))
    (hCoreLen : ∀ eL : List ℕ, MeetsContract w p coreLenFill (selCoreLenFillContract w P eCap eL))
    (hpEmbLoop : p.procs[embLoopProc]? = some (selectUpdateEmbLoopBody embLoopProc embLvlProc))
    (hpEmbLvl : p.procs[embLvlProc]? = some (selectUpdateEmbLevelBody (op 4) embUpdateFromList))
    (hEmbUpd :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ j < cfg.P.d, ∀ L' : List ℕ,
        MeetsContract w p embUpdateFromList
          (selEmbUpdateFromListContract w vCap eCap (modelPre.chain.G j)
            (modelPre.chain.toTreeChain.activeLSF j).F.F L'
            (modelPre.chain.toTreeChain.activeEmb j)))
    (hpSufBlocks : p.procs[sufBlocksProc]? =
      some (selectUpdateSuffixBlocksBody initIntLoop (op 3) fillLast phiLoop))
    (hpInitInt : p.procs[initIntLoop]? = some (selectInitInteriorLoopBody initIntLoop fillIntProc))
    (hpFillInt : p.procs[fillIntProc]? =
      some (selectFillInteriorLevelBody (op 2) (op 4) dgCopyProc coreLenFill filterAbs embCopyProc))
    (hpFillLast : p.procs[fillLast]? = some (selectFillLastLevelBody dgCopyProc coreLenFill))
    (hpPhiLoop : p.procs[phiLoop]? = some (selectPhiLoopBody phiLoop phiFillProc))
    (hFootAt :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ j < cfg.P.d,
        SparseCoreReadoutFootAt fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T (initialGraph j) cfg.P.k
          (modelPre.chain.lvlM j) modelPre.chain.N₀ vCap eCap capExp Psc allocation Rcore p op)
    (hDgCopy : ∀ vcF ecF (Fold Fnew : MGraph),
      MeetsContract w p dgCopyProc (dgCopyRefillContract w vCap eCap vcF ecF Fold Fnew))
    (hFilterAbs : ∀ eL : List ℕ, MeetsContract w p filterAbs (selFilterAbsentContract w eL))
    (hEmbCopy :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ j < cfg.P.d, ∀ eL : List ℕ,
        MeetsContract w p embCopyProc
          (selEmbCopyContract w eL (modelPre.chain.toTreeChain.activeEmb j)))
    (hPhiFill :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ (Bblk : SelectBlocksLoc) (metaBase : ℕ) (solverG : ℕ → ℕ) (φ : ℕ → ℕ → ℝ),
        MeetsContract w p phiFillProc
          (selectPhiFillContract w 4 P (selectMlocOf Bblk metaBase solverG pLast)
            modelPre.chain.toTreeChain G₀' modelPre.chain.g modelPre.chain.ℓ
            σ' σ'_mwu γ'_ℓ γ'_c φ))
    (hpHeapPhase : p.procs[heapPhaseProc]? = some (selectUpdateHeapPhaseBody heapPrefLoop rebSufProc))
    (hpHeapPref : p.procs[heapPrefLoop]? = some (selectUpdateHeapPrefixLoopBody heapPrefLoop updLvlProc))
    (hUpdLvl :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ (Bblk : SelectBlocksLoc) (metaBase : ℕ) (solverG : ℕ → ℕ) (φ : ℕ → ℕ → ℝ) (DL : LevelDiffLists),
        MeetsContract w p updLvlProc
          (selectUpdateLevelNoRoomContract w 4 P sg.loc (selectMlocOf Bblk metaBase solverG pLast)
            modelPre.chain.toTreeChain modelPre.chain.g modelPre.chain.ℓ φ
            (fun k => modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (k + 1))
            DL evalSpace evalCost))
    (hRebSuf :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      ∀ (Bblk : SelectBlocksLoc) (metaBase : ℕ) (solverG : ℕ → ℕ) (φ : ℕ → ℕ → ℝ),
        MeetsContract w p rebSufProc
          (selectRebuildSuffixNoRoomContract w 4 P sg.loc (selectMlocOf Bblk metaBase solverG pLast)
            modelPre.chain.toTreeChain G₀' modelPre.chain.g modelPre.chain.ℓ
            σ' σ'_mwu γ'_ℓ γ'_c φ
            (fun k => modelPre.chain.toTreeChain.chainLen modelPre.chain.ℓ (k + 1))
            evalSpace evalCost))
    -- Combined room bound
    (hroom :
      heap + (innerSpace U.length +
        selectUpdatePostCoreSpaceBound cfg.P.d vCap eCap sg.loc.cap L capExp
          (levelM cfg.TP cfg.P 0) cfg.N₀ evalSpace (innerSpace U.length)) < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let totalSpace := innerSpace U.length +
      selectUpdatePostCoreSpaceBound cfg.P.d vCap eCap sg.loc.cap L capExp
        (levelM cfg.TP cfg.P 0) cfg.N₀ evalSpace (innerSpace U.length)
    let totalFixed := innerFixed U.length +
      selectUpdatePostCoreFixedBound Psc.readout cfg.P.d L capExp (levelM cfg.TP cfg.P 0) cfg.N₀
        slot K c (uWordsFix U.length) (levelM cfg.TP cfg.P cfg.P.d) + 40
    let totalToolMul := innerToolMul +
      selectUpdatePostCoreToolMulBound cfg.P.d L capExp (levelM cfg.TP cfg.P 0) cfg.N₀ slot K c uWordsMul
    let totalTreeMul := innerTreeMul + selectUpdatePostCoreTreeMulBound slot K
    ∃ (nextHeap cost : ℕ) (out : State) (tokFinal : SolverToken cfg L Rcore) (sg' : SelectGhost),
      Runs w p ω (ordChainUpdateCoreSelBody coreProc postCoreProc)
        (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
        (.returned nextHeap) out cost ∧
      heap ≤ nextHeap ∧ nextHeap ≤ heap + totalSpace ∧
      tokFinal.levelsEnd = tok.levelsEnd ∧ tokFinal.intCap = tok.intCap ∧
      tokFinal.rootECap = tok.rootECap ∧ tokFinal.table = tok.table ∧
      Rrep.rep root modelPre tokFinal out.mem ∧
      SolverLevelMetaAt P V modelPre tokFinal out.mem ∧
      SolverLevelCapsAt vCap eCap modelPre tokFinal out.mem ∧
      SolverLevelLayoutAt vCap eCap tokFinal out.mem ∧
      SolverSelectInv G L P m 4 2 tokFinal.table modelPre (Rrep.foot root tokFinal)
        (LevelMetaFoot tokFinal) sg' out.mem ∧
      sg'.reembPot = chainReembPot pot modelPre.chain ∧
      SolverSelectRegionInv G L P m E pLast slot vCap eCap modelPre (Rrep.foot root tokFinal)
        tokFinal sg' out.mem ∧
      PathTreeNumericInv tokFinal.tree tokFinal.trees B R ∧
      OffTreeRecInv modelPre L out.mem tokFinal.edgeRecords B ∧
      OffTreeRecBound modelPre L out.mem tokFinal.edgeRecords B ∧
      ZeroFrom out.mem nextHeap ∧
      (∀ a < heap, ¬ (Rrep.foot root tok a ∨ sg.owned a) → out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tokFinal a ∨ sg'.owned a →
        (Rrep.foot root tok a ∨ sg.owned a) ∨ (heap ≤ a ∧ a < nextHeap)) ∧
      cost + Rrep.phi root tokFinal out.mem + K * sg'.reembPot ≤
        totalFixed +
          totalToolMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) +
          totalTreeMul * (modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
          Rrep.phi root tok mem0 + K * sg.reembPot := by
  intro Rrep gVec lVec modelPre totalSpace totalFixed totalToolMul totalTreeMul
  -- 1. Extract select-region block layout `Bblk` from `hReg0`
  obtain ⟨⟨Bblk, hBSlot, hBlkInv0⟩, hPhiBd0, _⟩ := hReg0
  obtain ⟨hRegAt0, hDisj0⟩ := SelectRegionAt.of_solverSelectBlocksInv hBlkInv0
  obtain ⟨hreg0, hcap0, hBd, hBv, hBe, hBLk, hOwnEq, hhbAt0, hBlkAt0, _, hTabOld0, hBlkOld0,
    hMatchOld0, hPotOld0, _, ⟨G₀, σ, σ_mwu, γ_ℓ, γ_c, hModOld0⟩⟩ := hRegAt0
  -- 2. Unpack inner core postcondition `hCorePost`
  obtain ⟨midHeap, cCore, stCore, tok', B', R', firstReb, levelU, levelUS, diffLists,
      hrCore, hMidLo, hMidHi, hLevEq1, hICapEq1, hRECapEq1, hTabEq1, hB'Le, hR'Le,
      hRepCore, hMetaCore, hCapsCore, hRootGCore, hTreeNumCore, hOffInvCore, hOffBdCore,
      hhbCoreEq, hBlkCoreEq, hLink, hOutAt, hZCore, hFrCore, hFtCore, hcCore⟩ := hCorePost
  -- 3. Transfer old select region across the core run (`[sb, Bblk.endAddr)` untouched)
  have hOwn0 := hrep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSbEq : sg.loc.hb = sg.loc.hb := rfl
  have hMetaEq : sg.loc.metaPtr = sg.loc.metaPtr := rfl
  have hLocEnd : sg.loc.endAddr = sg.loc.metaPtr := hreg0.2.1.symm
  have hMetaEnd : sg.loc.metaPtr + selectLevelMetaSize Bblk.d = Bblk.base := hreg0.2.2.2.1.symm
  have hBaseLeEnd : Bblk.base ≤ Bblk.endAddr := by rw [Bblk.endAddr_eq]; omega
  have hLocHbLtEnd : sg.loc.hb < sg.loc.endAddr := by
    rw [sg.loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega
  have hEndLtU : Bblk.endAddr ≤ uIntBuf := by
    have hlt := hFootLt (Bblk.endAddr - 1) (Or.inr (by rw [hOwnEq]; omega))
    omega
  have hCoreAgOwn : ∀ a, sg.loc.hb ≤ a → a < Bblk.endAddr → stCore.mem a = mem0 a := fun a h1 h2 => by
    have hnf : ¬ Rrep.foot root tok a := hDisj0 a h1 h2
    have htag0 : tok.tag a = 0 := by by_contra hne; exact hnf (Or.inl (hOwn0 a hne))
    have hlt : a < uIntBuf := hFootLt a (Or.inr (by rw [hOwnEq]; exact ⟨h1, h2⟩))
    exact (hFrCore a (by omega) hnf).trans (hTags0 a hlt (by omega) (by omega) (by omega))
  have hFootCoreSc : ∀ a, Rrep.foot root tok' a → a < midHeap := fun a ha =>
    (hFtCore a ha).elim (fun h0 => lt_of_lt_of_le (hFootLt a (Or.inl h0)) (by omega)) (fun hn => hn.2)
  have hFootCoreDisj : ∀ a, sg.loc.hb ≤ a → a < Bblk.endAddr → ¬ Rrep.foot root tok' a := fun a h1 h2 ha =>
    (hFtCore a ha).elim (hDisj0 a h1 h2) (fun hn => by omega)
  have hTabCore : SelectMetaTableAt stCore.mem
      (selectMlocOf Bblk sg.loc.metaPtr (solverLevelG tok mem0) pLast) :=
    hTabOld0.of_agree fun a h1 h2 => hCoreAgOwn a (by dsimp only [selectMlocOf] at h1; omega)
      (by dsimp only [selectMlocOf] at h2; omega)
  have hBlkCore : SelectBlocksAt stCore.mem Bblk P model.chain.toTreeChain model.chain.g
      model.chain.ℓ sg.φ pLast :=
    selectBlocksAt_iff_data.mpr ((selectBlocksAt_iff_data.mp hBlkOld0).of_agree fun a h1 h2 =>
      hCoreAgOwn a (by omega) h2)
  have hMatchCore : SelectHeapMatchesChain stCore.mem sg.loc 4 P model.chain.toTreeChain
      model.chain.g model.chain.ℓ sg.size :=
    hMatchOld0.of_agree fun a h1 h2 => hCoreAgOwn a h1 (by omega)
  -- 4. Unpack link/cost facts and verify space bound for `selectUpdatePostCore_runs`
  obtain ⟨ins, hBranchA, hgSurv, hℓSurv, hPrefModel, hWstr, hInsFwd, hEP, hPotPref, hPhiBdPref,
      hNoRebLast, hUGLe, hReemb, hUWordsSum, hULenSum, hUSSum, hFDelSum, hCostSum,
      hSufNewM, hSufOldM, hBranchA0⟩ :=
    hLinkFacts stCore.mem midHeap firstReb levelU levelUS diffLists tok' hLink hOutAt
  have hFR : firstReb ≤ cfg.P.d + 1 := hLink.1
  have hDiffLe : ∀ j < min firstReb cfg.P.d,
      (diffLists j).uG.length ≤ innerSpace U.length ∧
      (diffLists j).fDel.length ≤ innerSpace U.length ∧
      (diffLists j).uS.length ≤ innerSpace U.length ∧
      (diffLists j).reemb.length ≤ innerSpace U.length := fun j hj => by
    have hS := hOutAt.2.2 j hj
    exact ⟨(selOutWordsAt_len_le hS.2.2.2.2.2.2.1).trans (by omega),
      (selOutWordsAt_len_le hS.2.2.2.2.2.2.2.1).trans (by omega),
      (selOutWordsAt_len_le hS.2.2.2.2.2.2.2.2.1).trans (by omega),
      (selOutWordsAt_len_le hS.2.2.2.2.2.2.2.2.2.1).trans (by omega)⟩
  have hStLwLe : ∀ j < min firstReb cfg.P.d,
      stCore.mem (heap + 1 + 12 * j + 9) ≤
        ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀ := fun j hj =>
    (hOutAt.2.2 j hj).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hStLwW : ∀ j < min firstReb cfg.P.d, stCore.mem (heap + 1 + 12 * j + 9) < 2 ^ w := fun j hj => by
    have h1 := hStLwLe j hj
    have h2 : ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀ ≤
        ordLevelLwMax L capExp (levelM cfg.TP cfg.P 0) cfg.N₀ := by
      unfold ordLevelLwMax
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _
        (Nat.add_le_add_right (Nat.log_mono_right (by have := levelM_le_levelM_zero hTP hγk j; omega)) 1)) _
    omega
  have hSpBound := selectUpdatePostCoreSpace_le_bound (mem := stCore.mem) (loc := sg.loc)
    (model := model) (modelPre := modelPre) (diffLists := diffLists)
    (stLw := fun j => stCore.mem (heap + 1 + 12 * j + 9))
    (coreSp := innerSpace U.length) (evalSpace := evalSpace)
    hTP hγk hdPos hFR hCoreKFBL.2.1 (fun j hj => (hCoreKFBL.2.2.2.2.2.1 j hj).2.2.1)
    hModOld0 hModNew hMatchCore (hreg0.2.2.2.2.2.1.trans hBLk) hOldEcap hNewVcap hNewEcap
    hDiffLe hStLwLe
  -- 5. Run `selectUpdatePostCoreBody` (`selectUpdatePostCore_runs`)
  have hPostRoom : midHeap + selectUpdatePostCoreRawSpace stCore.mem sg.loc modelPre.chain diffLists
      (fun j => stCore.mem (heap + 1 + 12 * j + 9)) firstReb L capExp evalSpace < 2 ^ w := by
    omega
  obtain ⟨nextHeap, cPost, stPost, tokFinal, sg', hrPost, hNextLo, hNextHi, hRepFinal,
      hTabEq2, _, hLevEq2, hICapEq2, hRECapEq2, hTreeEq2, hTreesEq2, hEdgeRecEq2,
      _, _, _, _, hFtPost, _, _, _, hCapsFinal, hSgLocEq, hSgOwnEq, hSgPotEq,
      _, hBlkInvFinal, hSelInvFinal, hPhiBdFinal, _, hZFinal, hNonCorePost, hcPost⟩ :=
    selectUpdatePostCore_runs (G := G) (G₀ := G₀) (G₀' := G₀')
      (σ := σ) (σ_mwu := σ_mwu) (γ_ℓ := γ_ℓ) (γ_c := γ_c)
      (σ' := σ') (σ'_mwu := σ'_mwu) (γ'_ℓ := γ'_ℓ) (γ'_c := γ'_c)
      (initialGraph := initialGraph) (Psc := Psc) (allocation := allocation)
      (reembFn := reembFn) (pot := pot) (solverGOld := solverLevelG tok mem0)
      (levelU := levelU) (levelUS := levelUS) (diffLists := diffLists) (ins := ins)
      (PhiBd := fun φ j => SelectPhiBoundedAt modelPre.chain.toTreeChain φ (2 * m + 2) ((2 : ℝ) ^ E) j)
      hfmt4 hfmtP hlocalCore hw16 hw10 hLpos hLkW hpLastW hkW (hBSlot.symm ▸ hSlotW)
      hdPos heCapPos heCapLeHeap hRepCore ⟨hMetaCore, hCapsCore⟩ hFootCoreSc hFootCoreDisj
      (by omega) hreg0 hcap0 hBd hBv hBe hBLk hOwnEq
      (by rw [hTabEq1, hhbCoreEq]; exact hhbAt0)
      (by rw [hTabEq1, hBlkCoreEq]; exact hBlkAt0)
      hTabCore hBlkCore hMatchCore hPotOld0 hModOld0 hModNew hLink hOutAt hStLwW
      hgEqNew hgFitNew hBranchA hgSurv hℓSurv hPrefModel hWstr hInsFwd hEP hPotPref hPhiBdPref
      hNoRebLast hVcap hEcap hLenFitAll (hLenFitLast Bblk firstReb) (hBSlot.symm ▸ hEmbSlot)
      hPhiBdStep hPhiFit (hTabEq1.symm ▸ hTableWrite Bblk sg.loc.metaPtr)
      hpG0 hCopyOne hFilterPres hpFPLLoop hpFPLLvl
      (fun j _ => hDgBatch _ _ _ _) (fun j _ => hDelList _ _) (fun j _ => hSplits _ _ _ _)
      hpCoreLen hCoreLenEdge hCoreLen hpEmbLoop hpEmbLvl
      (fun j hj L' => hEmbUpd j (lt_of_lt_of_le hj (Nat.min_le_right _ _)) L')
      hpSufBlocks hpInitInt hpFillInt hpFillLast hpPhiLoop hFootAt hDgCopy hFilterAbs
      (fun j _ hj => hEmbCopy j hj) (hPhiFill Bblk sg.loc.metaPtr)
      hpHeapPhase hpHeapPref
      (fun solverG φ j _ => hUpdLvl Bblk sg.loc.metaPtr solverG φ (diffLists j))
      (hRebSuf Bblk sg.loc.metaPtr) hZCore hPostRoom
  -- 6. Stitch `coreProc` + `postCoreProc` into `ordChainUpdateCoreSelBody`
  have hNextHiBound : nextHeap ≤ heap + totalSpace := by
    have h2 : nextHeap ≤ midHeap + selectUpdatePostCoreRawSpace stCore.mem sg.loc modelPre.chain
        diffLists (fun j => stCore.mem (heap + 1 + 12 * j + 9)) firstReb L capExp evalSpace := hNextHi
    exact h2.trans ((Nat.add_le_add hMidHi hSpBound).trans (by dsimp only [totalSpace]; omega))
  obtain ⟨out, cost, hrBody, hOutMem, hcBody⟩ :=
    ordChainUpdateCoreSelBody_stitch hbCore hpPostCore hrCore hrPost
  -- 7. Preserve `PathTreeNumericInv`, `OffTreeRecInv`, `OffTreeRecBound` at `(B, R)`
  have hTreeNumFinal : PathTreeNumericInv tokFinal.tree tokFinal.trees B R := by
    rw [hTreeEq2, hTreesEq2]
    exact PathTreeNumericInv.mono hTreeNumCore hB'Le hR'Le
  have hOwnCore := hRepCore.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hOffInvCore', hOffBdCore'⟩ :=
    offTreeRec_preserve_nonCore hRepCore hOffInvCore hOffBdCore fun a hne hnc => by
      have hf : Rrep.foot root tok' a := Or.inl (hOwnCore a hne)
      exact hNonCorePost a (hFootCoreSc a hf) (fun h => hFootCoreDisj a h.1 h.2 hf) hnc
  have hOffInvFinal : OffTreeRecInv modelPre L out.mem tokFinal.edgeRecords B := by
    rw [hOutMem, hEdgeRecEq2]; exact offTreeRecInv_mono_B hOffInvCore' hB'Le
  have hOffBdFinal : OffTreeRecBound modelPre L out.mem tokFinal.edgeRecords B := by
    rw [hOutMem, hEdgeRecEq2]; exact offTreeRecBound_mono_B hOffBdCore' hB'Le
  -- 8. Amortized cost bound
  have hAmort := selectUpdatePostCore_amortized_cost_le (mem := stCore.mem) (loc := sg.loc)
    (model := model) (modelPre := modelPre) (levelU := levelU) (diffLists := diffLists)
    (uWords := fun j => stCore.mem (heap + 1 + 12 * j + 11))
    (stLw := fun j => stCore.mem (heap + 1 + 12 * j + 9))
    (readoutCost := Psc.readout) (uWordsFix := uWordsFix U.length)
    (mD := levelM cfg.TP cfg.P cfg.P.d)
    (slot := Bblk.slot) (evalCost := evalCost) (K := K) (c := c) (uWordsMul := uWordsMul)
    hTP hγk hPot hdPos hFR hCoreKFBL.1 hCoreKFBL.2.1
    (fun j hj => ⟨(hCoreKFBL.2.2.2.2.2.1 j hj).1, (hCoreKFBL.2.2.2.2.2.1 j hj).2.1,
      (hCoreKFBL.2.2.2.2.2.1 j hj).2.2.1⟩)
    (fun j hj => ⟨(hCoreKFBL.2.2.2.2.2.1 j hj).2.2.2.1, (hCoreKFBL.2.2.2.2.2.1 j hj).2.2.2.2⟩)
    hCoreKFBL.2.2.2.2.2.2.1 hCoreKFBL.2.2.2.2.2.2.2.1 hModOld0 hModNew hMatchCore
    (hreg0.2.2.2.2.2.1.trans hBLk) (hBSlot.symm ▸ hK) hStLwLe hUGLe hReemb hUWordsSum
    hULenSum hUSSum hFDelSum hCostSum hSufNewM hSufOldM
    ⟨hCoreKFBL.2.2.2.2.2.2.2.2.1, hCoreKFBL.2.2.2.2.2.2.2.2.2.1⟩ hBranchA0
  rw [hBSlot] at hAmort hcPost
  -- 9. Final frame, foot, and `SolverSelectRegionInv`
  have hFrameFinal : ∀ a < heap, ¬ (Rrep.foot root tok a ∨ sg.owned a) → out.mem a = mem a := by
    intro a ha hnf
    rw [hOutMem]
    have hnfTok : ¬ Rrep.foot root tok a := fun h => hnf (Or.inl h)
    have hnsb : ¬ (sg.loc.hb ≤ a ∧ a < Bblk.endAddr) := fun h =>
      hnf (Or.inr (by rw [hOwnEq]; exact h))
    have hnc : ∀ j < cfg.P.d, tok'.tag a ≠ 21 + j := fun j _ htag => by
      have hf : Rrep.foot root tok' a := Or.inl (hOwnCore a (by rw [htag]; omega))
      rcases hFtCore a hf with h0 | ⟨hlo, _⟩
      · exact hnfTok h0
      · omega
    exact (hNonCorePost a (by omega) hnsb hnc).trans (hFrCore a ha hnfTok)
  have hFootFinal : ∀ a, Rrep.foot root tokFinal a ∨ sg'.owned a →
      (Rrep.foot root tok a ∨ sg.owned a) ∨ (heap ≤ a ∧ a < nextHeap) := by
    rintro a (hf | ho)
    · rcases hFtPost a hf with hCore' | ⟨hlo, hhi⟩
      · rcases hFtCore a hCore' with h0 | ⟨hlo0, hhi0⟩
        · exact Or.inl (Or.inl h0)
        · exact Or.inr ⟨hlo0, by omega⟩
      · exact Or.inr ⟨by omega, hhi⟩
    · exact Or.inl (Or.inr (hSgOwnEq ▸ ho))
  have hLayFinal : SolverLevelLayoutAt vCap eCap tokFinal out.mem := by
    rw [hOutMem]
    have hLayCore : SolverLevelLayoutAt vCap eCap tok' stCore.mem :=
      SolverLevelLayoutAt.of_root_and_disj hRootGCore (hCoreDisj _ _ _ _ hrCore hTabEq1)
    refine hLayCore.of_nonCore_agree hRepCore hRepFinal hMetaCore hTabEq2 (fun a hnz hnc => ?_)
    have hf : Rrep.foot root tok' a := Or.inl (hOwnCore a hnz)
    exact hNonCorePost a (hFootCoreSc a hf) (fun h => hFootCoreDisj a h.1 h.2 hf) hnc
  have hRegFinal : SolverSelectRegionInv G L P m E pLast slot vCap eCap modelPre
      (Rrep.foot root tokFinal) tokFinal sg' out.mem :=
    ⟨⟨Bblk, hBSlot, hOutMem ▸ hBlkInvFinal⟩, hPhiBdFinal, hgBoundNew⟩
  refine ⟨nextHeap, cost, out, tokFinal, sg', hrBody, by omega, hNextHiBound,
    hLevEq2.trans hLevEq1, hICapEq2.trans hICapEq1, hRECapEq2.trans hRECapEq1,
    hTabEq2.trans hTabEq1, hOutMem ▸ hRepFinal, hOutMem ▸ hCapsFinal.1, hOutMem ▸ hCapsFinal.2,
    hLayFinal, hOutMem ▸ hSelInvFinal, hSgPotEq, hRegFinal, hTreeNumFinal, hOffInvFinal, hOffBdFinal,
    hOutMem ▸ hZFinal, hFrameFinal, hFootFinal, ?_⟩
  rw [hOutMem, hSgPotEq, hPot0]
  have hToolMulAdd :
      totalToolMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) =
      innerToolMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) +
      selectUpdatePostCoreToolMulBound cfg.P.d L capExp (levelM cfg.TP cfg.P 0) cfg.N₀ slot K c uWordsMul *
        (modelPre.chain.totalRuntime - model.chain.totalRuntime) := by
    dsimp only [totalToolMul]; ring
  have hTreeMulAdd :
      totalTreeMul * (modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates) =
      innerTreeMul * (modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
      selectUpdatePostCoreTreeMulBound slot K *
        (modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates) := by
    dsimp only [totalTreeMul]; ring
  dsimp only [totalFixed]
  linarith

end MinCostFlow.MinRatio
