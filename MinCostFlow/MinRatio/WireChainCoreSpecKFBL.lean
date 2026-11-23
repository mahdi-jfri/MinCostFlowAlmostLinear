module

public import MinCostFlow.MinRatio.WireChainCoreSelectOutKFBL
public import MinCostFlow.MinRatio.WireShiftDeepSpecKFBL
public import MinCostFlow.MinRatio.WireChainCoreCompact
public import MinCostFlow.MinRatio.WireChainCoreRefreshLoop
public import MinCostFlow.MinRatio.MinRatioMachineAssemblyBase
public import MinCostFlow.MinRatio.WireSelectSplitPotModel
import Mathlib.Tactic

/-!
# Chain-update core hypotheses and specification under `KFBL` (`WireChainCoreSpecKFBL`)

Restates the chain-update core operational envelope and extended specification of the `K`
contract (`WireChainCoreOps.lean`, `WireChainSpecs.lean`) to the layout contract
`sparseCoreOrdMachineContractKFBL` (`AssemblyContractLayout.lean`):

1. **Branch B live cost and Branch A `level0Rebuilt` guard:**
   * Branch B never copies or packs the forests of non-rebuilt levels `[0, i₀)`: tree edits for
     `j < i₀` come directly from `Read.LSFChangeAt` (`BranchOutFChgAt`, `wireEmitLSFChangeEditsBody`),
     paid by `treeMul · Δ totalTreeUpdates`.
   * Only the rebuilt suffix `[i₀, d]` is copied (`copyGraphLiveFromHeader`) and packed
     (`wireSuffixPackEditsBody`), paid by `toolMul · Δ totalRuntime` (plus `O(levelM d)` at `i₀ = d`).
   * All per-level update step costs (`bW_j`, `eW_j`, `nextU_j`) are charged to
     `coreFixed U.length + toolMul · Δ totalRuntime`, with zero `m`, `N₀`, cap, or `forestEdgeCap`
     terms in `coreFixed`.
   * `costTotalBranchA` carries the `level0Rebuilt` guard (`intRebuildThreshold 0 < updCount 0 + |U_int|`).
2. **Bounded quantifiers on `KFBL`:**
   * Eliminates `op0Placement`, `op2Placement`, `op3Placement`, `op5Placement`, and `ordRotCap`
     (all supplied directly by `SparseCoreReadoutFootAt`, `SparseCoreForestCapAt`, and
     `SparseCoreUpdateOutFootAt`).
   * Bounds every space and cost quantifier by reached-state facts (`ShiftLoopLevelFacts`,
     `UpdateCoreModelInvKFBL`, `model.chain.N₀ = cfg.N₀`, `model.chain.lvlM = levelM`).
3. **Extended specification and select-block outputs:**
   * Omits `hNewInOff0`.
   * Gives `OrdChainUpdateCoreSpecWExtKFBL` all reached-state preconditions its postcondition needs
     (`SolverLevelMetaAt`, `SolverLevelCapsAt`, `PathTreeNumericInv`, `OffTreeRecInv`,
     `OffTreeRecBound`, `ShiftLoopChainInv`, `UpdateCoreModelInvKFBL`).
   * Defines `UpdateCoreSelectOutAt`, the memory outputs that the select part of `Update` reads at
     each non-rebuilt level (the four lists, the stretch tables of the new forest, and the batch of
     the level, with their places), and `UpdateCoreLevelLink`, which ties the first rebuilt level
     and the batches to the model (`firstRebuiltLevel`, `NonRebuiltBatches`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-! ### 1. Core, forest-cap, and op-`0` output hypotheses under `KFBL` -/

/-- Uniform `KFBL` + `SparseCoreReadoutFootAt` hypothesis for all levels `j < d` of the chain
update core. Mirrors `DeepShiftCoreKFBL` (`WireShiftDeepSpecKFBL.lean`). -/
@[expose] def UpdateCoreCoreKFBL {w : ℕ} (fmt : Num.Format w) (L m vCap eCap capExp : ℕ)
    (cfg : Alg2Config) (Psc : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  DeepShiftCoreKFBL fmt L m vCap eCap capExp cfg Psc allocation Rcore p init op

/-- Uniform `KFRBL` + `SparseCoreReadoutFootAt` hypothesis for all levels `j < d` of the chain
update core, exposing per-branch `reemb` lists on `op 0` alongside the `KFBL` layout contract. -/
@[expose] def UpdateCoreCoreKFRBL {w : ℕ} (fmt : Num.Format w) (L m vCap eCap capExp : ℕ)
    (cfg : Alg2Config) (reemb : ToolReembFn cfg.T) (Psc : SparseCoreOrdParams)
    (allocation : ℕ → List ℕ → ℕ) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (p : Program) (init : ℕ) (op : ℕ → ℕ) : Prop :=
  ∀ j < cfg.P.d, ∀ G : MGraph, G.n ≤ G.m + 1 → G.m ≤ m →
    Rcore.Implements w p init op
      (sparseCoreOrdMachineContractKFRBL fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T reemb G
        cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀ vCap eCap capExp Psc allocation) ∧
    SparseCoreReadoutFootAt fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T G cfg.P.k
      (levelM cfg.TP cfg.P j) cfg.N₀ vCap eCap capExp Psc allocation Rcore p op

theorem UpdateCoreCoreKFRBL.toKFBL {w L m vCap eCap capExp : ℕ} {fmt : Num.Format w}
    {cfg : Alg2Config} {reemb : ToolReembFn cfg.T} {Psc : SparseCoreOrdParams}
    {allocation : ℕ → List ℕ → ℕ} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (h : UpdateCoreCoreKFRBL fmt L m vCap eCap capExp cfg reemb Psc allocation Rcore p init op) :
    UpdateCoreCoreKFBL fmt L m vCap eCap capExp cfg Psc allocation Rcore p init op := fun j hj G hG hGm =>
  ⟨dsRep_implements_kfbl_of_kfrbl (h j hj G hG hGm).1, (h j hj G hG hGm).2⟩

/-- Uniform `SparseCoreForestCapAt` hypothesis for all levels `j < d`. -/
@[expose] def UpdateCoreForestCapKFBL {w : ℕ} (fmt : Num.Format w) (L vCap eCap capExp : ℕ)
    (cfg : Alg2Config) (Psc : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) (fcap : ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program) (op : ℕ → ℕ) : Prop :=
  DeepShiftForestCapKFBL fmt L vCap eCap capExp cfg Psc allocation fcap Rcore p initOp
where
  initOp := op

/-- Uniform `SparseCoreUpdateOutFootAt` hypothesis for `op 0` at every level `j < d`. -/
@[expose] def UpdateCoreOp0FootKFBL {w : ℕ} (fmt : Num.Format w) (L vCap eCap capExp : ℕ)
    (cfg : Alg2Config) (Psc : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) (edMul : ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program) (op : ℕ → ℕ) : Prop :=
  ∀ j < cfg.P.d, ∀ G : MGraph, G.n ≤ G.m + 1 →
    SparseCoreUpdateOutFootAt fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T G cfg.P.k
      (levelM cfg.TP cfg.P j) cfg.N₀ vCap eCap capExp Psc allocation edMul Rcore p op

/-- Companion per-run footprint guarantees needed to preserve select-block outputs (`reemb`,
`fDel` change records, and `StretchValuesAt`) across subsequent chain-update operations:
* `op0_runs`: extends `SparseCoreUpdateOutFootAt.op0_runs` with heap-range and core-footprint
  disjointness for each branch's `reemb` list (`heap + 1 + 4 * k + 2 * j`) and `fDel` change
  record (`BranchOutFChgAt`);
* `op2_runs`: extends `SparseCoreReadoutFootAt.op2_runs` with core-footprint containment of the
  returned stretch descriptor `stDesc .. stDesc + 2` and stretch limb tables for all `e ∈ a.G.E`.

No proof of the sparse core gives these extra facts, so the chain-core proof does not take this
structure. The core copies the lists and the descriptor into its own heap instead. Only a few
Branch A files use the structure. -/
structure SparseCoreSelectFootAt {w : ℕ} (fmt : Num.Format w) (L depth : ℕ)
    (tool : SparseCoreRestartTool) (initialGraph : MGraph) (k M N vCap eCap capExp : ℕ)
    (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) (edMul : ℕ)
    (R : DSRep (SparseCoreOrdAbs tool)) (p : Program) (op : ℕ → ℕ) : Prop where
  op0_runs :
    let D := sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation
    ∀ (b : ℕ) (a : SparseCoreOrdAbs tool) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some b →
      R.rep b a x mem → D.pre 0 a args mem → (∀ addr, R.foot b x addr → addr < heapArg args) →
      ZeroFrom mem (heapArg args) → heapArg args + D.space 0 a args mem < 2 ^ w →
      ∃ body, p.procs[op 0]? = some body ∧ ∃ o st' c x',
        let h := heapArg args
        let words := args.getD 3 0
        let editWords := args.getD 5 0
        let a' := ordUpdateNext fmt L a args mem
        let batches := (ordUpdateModel fmt L a args mem).2
        Runs w p ω body (startState args mem pos) o st' c ∧
        R.rep b a' x' st'.mem ∧
        D.post 0 a args mem a' st'.mem ∧
        BranchOutFChgAt w st'.mem h o.value k (tool.lsfs a.st) (tool.lsfs a'.st) ∧
        (let fChgPtr := st'.mem (h + 1 + 6 * k)
         ∀ j < k, ∃ chg : Read.LSFChange,
           let chgPtr := st'.mem (fChgPtr + j)
           Read.LSFChangeAt st'.mem chgPtr chg ∧
           chg.Exact (tool.lsfs a.st j) (tool.lsfs a'.st j) ∧
           h ≤ chgPtr ∧ chgPtr + chg.words ≤ o.value ∧
           (∀ e ∈ chg.fDel, e < 2 ^ w) ∧
           (∀ t < chg.words, ¬ R.foot b x' (chgPtr + t))) ∧
        (∀ j < k,
          let base := h + 1 + 4 * j
          let bPtr := st'.mem base
          let bW := st'.mem (base + 1)
          let ePtr := st'.mem (base + 2)
          let eW := st'.mem (base + 3)
          let rPtr := st'.mem (h + 1 + 4 * k + 2 * j)
          let rLen := st'.mem (h + 2 + 4 * k + 2 * j)
          h + 1 + 4 * j + 3 < o.value ∧
          h + 2 + 4 * k + 2 * j < o.value ∧
          h ≤ bPtr ∧ bPtr + bW ≤ o.value ∧
          h ≤ ePtr ∧ ePtr + eW ≤ o.value ∧
          h ≤ rPtr ∧ rPtr + rLen ≤ o.value ∧
          (∀ t < bW, st'.mem (bPtr + t) < 2 ^ w) ∧
          (∀ t < eW, st'.mem (ePtr + t) < 2 ^ w) ∧
          (∀ t < bW, ¬ R.foot b x' (bPtr + t)) ∧
          (∀ t < eW, ¬ R.foot b x' (ePtr + t)) ∧
          (∀ t < rLen, ¬ R.foot b x' (rPtr + t)) ∧
          (decodeBatch st'.mem bPtr (tool.S a.st j)).1 = batches j ∧
          eW ≤ edMul * (tool.cost a'.st - tool.cost a.st +
            (words + editWords + 1) * SparseCore.bundleLogFactor M N)) ∧
        R.Respects (R.foot b x) h (D.space 0 a args mem) mem o.value b x' st'.mem ∧
        c + R.phi b x' st'.mem ≤ D.cost 0 a args mem + R.phi b x mem
  op2_runs :
    let D := sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation
    ∀ (b : ℕ) (a : SparseCoreOrdAbs tool) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some b →
      R.rep b a x mem → D.pre 2 a args mem → (∀ addr, R.foot b x addr → addr < heapArg args) →
      ZeroFrom mem (heapArg args) → heapArg args + D.space 2 a args mem < 2 ^ w →
      ∃ body, p.procs[op 2]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState args mem pos) o st' c ∧
        R.rep b a x' st'.mem ∧
        (let cur := heapArg args
         let br := args.getD 1 0
         let fBase := st'.mem (cur + 1)
         let stDesc := st'.mem (cur + 3)
         let Lw := st'.mem (cur + 4)
         ∃ forestVCap forestECap,
           Lw ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
           LSFAt st'.mem cur forestVCap forestECap fmt.limbBits Lw fmt.precision a.G.E
             (tool.lsfs a.st br) ∧
           fBase + dynGraphSize forestVCap forestECap ≤ cur ∧
           (∀ addr, fBase ≤ addr → addr < fBase + dynGraphSize forestVCap forestECap →
             R.foot b x' addr ∨ (cur ≤ addr ∧ addr < o.value)) ∧
           stDesc + 2 ≤ cur ∧
           (∀ addr, stDesc ≤ addr → addr < stDesc + 2 → R.foot b x' addr) ∧
           (∀ e ∈ a.G.E,
             st'.mem stDesc + e * Lw + Lw ≤ cur ∧
             st'.mem (stDesc + 1) + e * Lw + Lw ≤ cur ∧
             ∀ t < Lw,
               R.foot b x' (st'.mem stDesc + e * Lw + t) ∧
               R.foot b x' (st'.mem (stDesc + 1) + e * Lw + t)) ∧
           dynGraphSize forestVCap forestECap ≤ dynGraphSize vCap (2 * (vCap + eCap + 2) ^ 2)) ∧
        R.Respects (R.foot b x) (heapArg args) (D.space 2 a args mem) mem o.value b x' st'.mem ∧
        c + R.phi b x' st'.mem ≤ D.cost 2 a args mem + R.phi b x mem

theorem SparseCoreSelectFootAt.toUpdateOutFootAt
    {w L depth k M N vCap eCap capExp edMul : ℕ} {fmt : Num.Format w}
    {tool : SparseCoreRestartTool} {initialGraph : MGraph} {P : SparseCoreOrdParams}
    {allocation : ℕ → List ℕ → ℕ} {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ}
    (h : SparseCoreSelectFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation edMul R p op) :
    SparseCoreUpdateOutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation edMul R p op where
  op0_runs := fun b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp => by
    obtain ⟨body, hbody, o, st', c, x', hrun, hrep', hpost, hFChg, _, hSlots, hResp, hCost⟩ :=
      h.op0_runs b a x args mem pos ω hargs hhead hrep hpre hfoot hz hsp
    refine ⟨body, hbody, o, st', c, x', hrun, hrep', hpost, hFChg, fun j hj => ?_, hResp, hCost⟩
    obtain ⟨h1, _, h2, h3, h4, h5, _, _, h6, h7, h8, h9, _, h10, h11⟩ := hSlots j hj
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- Uniform `SparseCoreSelectFootAt` hypothesis for every level `j < d`. -/
@[expose] def UpdateCoreSelectFootKFBL {w : ℕ} (fmt : Num.Format w) (L vCap eCap capExp : ℕ)
    (cfg : Alg2Config) (Psc : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) (edMul : ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program) (op : ℕ → ℕ) : Prop :=
  ∀ j < cfg.P.d, ∀ G : MGraph, G.n ≤ G.m + 1 →
    SparseCoreSelectFootAt fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T G cfg.P.k
      (levelM cfg.TP cfg.P j) cfg.N₀ vCap eCap capExp Psc allocation edMul Rcore p op

/-! ### 2. Reached-state model invariant under `KFBL` -/

/-- Reached-state model facts for the chain update core under `KFBL`: `ShiftLoopLevelFacts` before
and after `Update`, level validity and vertex bounds, live rotation-order word bounds, suffix
forest/graph inclusions, and decremental forest updates on non-rebuilt levels. -/
@[expose] def UpdateCoreModelInvKFBL {cfg : Alg2Config}
    (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ) : Prop :=
  let modelPre := alg2PreResetState cfg model U gVec lVec
  let d := cfg.P.d
  ShiftLoopLevelFacts cfg model.chain ∧
  ShiftLoopLevelFacts cfg modelPre.chain ∧
  (∀ j ≤ d, (model.chain.G j).IsValid ∧ (modelPre.chain.G j).IsValid) ∧
  (∀ j ≤ d, (modelPre.chain.G j).n ≤ modelPre.chain.N₀) ∧
  (∀ j < d,
    ordRotWords (chainLevelOrdAbs modelPre.chain j) (modelPre.chain.bran j) ≤
      1 + 2 * (modelPre.chain.G (j + 1)).n + 2 * (modelPre.chain.G (j + 1)).m) ∧
  (∀ j < d,
    (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.V ⊆ (model.chain.G j).V ∧
    (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.E ⊆ (model.chain.G j).E ∧
    (model.chain.G (j + 1)).E ⊆ (model.chain.G j).E ∧
    (cfg.T.lsfs (modelPre.chain.scState j) (modelPre.chain.bran j)).F.F.E ⊆ (modelPre.chain.G j).E ∧
    (modelPre.chain.G (j + 1)).E ⊆ (modelPre.chain.G j).E) ∧
  (model.chain.lastLSFs model.chain.lastBran).F.F.E ⊆ (model.chain.G d).E ∧
  (modelPre.chain.lastLSFs modelPre.chain.lastBran).F.F.E ⊆ (modelPre.chain.G d).E ∧
  (model.chain.G d).m ≤ levelM cfg.TP cfg.P d ∧
  (modelPre.chain.G d).m ≤ levelM cfg.TP cfg.P d ∧
  (∀ j < d, model.chain.bran j < cfg.P.k) ∧
  (∀ j₁ ≤ d, ∀ j₂ ≤ d, j₁ ≠ j₂ →
    Disjoint (model.chain.toTreeChain.activeLSF j₁).F.F.E
      (model.chain.toTreeChain.activeLSF j₂).F.F.E) ∧
  (∀ j₁ ≤ d, ∀ j₂ ≤ d, j₁ ≠ j₂ →
    Disjoint (modelPre.chain.toTreeChain.activeLSF j₁).F.F.E
      (modelPre.chain.toTreeChain.activeLSF j₂).F.F.E) ∧
  (∀ j ≤ d, (modelPre.chain.G j).m ≤ levelM cfg.TP cfg.P j) ∧
  (∀ u ∈ (modelPre.chain.G d).V, ∀ v ∈ (modelPre.chain.G d).V, (modelPre.chain.G d).Connected u v)

/-! ### 3. Trace of non-rebuilt prefix sizes in Branch B -/

/-- Exact recursive trace of non-rebuilt levels in `Chain.Ordered.updateLoop`: given the batch
`U_j` at level `j`, returns the batch length, graph encoding size, and single-step `T.cost` delta
for each non-rebuilt level `j < i₀`. -/
@[expose] noncomputable def updateLoopStepTrace (cfg : Alg2Config) (ℓ' g' : ℕ → ℝ) :
    (rem idx : ℕ) → ChainState cfg.T cfg.P → MGraph → List Update →
      List (ℕ × ℕ × ℕ × ℕ)
  | 0, _, _, _, _ => []
  | rem + 1, idx, st, curG, curU =>
    if intRebuildThreshold cfg.P st.N₀ idx < st.updCount idx + curU.length then
      []
    else
      let Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
      let ℓi := Cpartial.chainLen ℓ' idx
      let gi := Cpartial.chainGrad g' idx
      let updRes := cfg.T.updateOrd (st.scState idx) curU ℓi gi
        (Chain.Ordered.chainLevelOrd cfg.T (fun j => if j = idx then curG else st.G j)
          st.scState st.bran idx)
      let sc' := updRes.1
      let nextG := cfg.T.S sc' (st.bran idx)
      let nextU := updRes.2 (st.bran idx)
      let stNext : ChainState cfg.T cfg.P :=
        { st with
          G := fun j => if j = idx then curG else st.G j
          scState := fun j => if j = idx then sc' else st.scState j
          updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j }
      (idx, curU.length, nextU.length, cfg.T.cost sc' - cfg.T.cost (st.scState idx)) ::
        updateLoopStepTrace cfg ℓ' g' rem (idx + 1) stNext nextG nextU

/-- Level-by-level step cost bound for a non-rebuilt level `idx < i₀` with input word lengths
`(bW, eW)`, output batch length `nextULen`, and single-step `T.cost` delta `Δc`. -/
@[expose] def updateCoreNoRebuildStepCost (L capExp : ℕ) (Psc : SparseCoreOrdParams)
    (k lvlM N0 bW eW nextULen Δc : ℕ) : ℕ :=
  let LwMax := ordLevelLwMax L capExp lvlM N0
  Psc.mul * (Δc + (k + 1) * (bW + eW + 1) * SparseCore.bundleLogFactor lvlM N0) +
    730 * bW + Psc.readout + nextULen * (wireCoreLenEdgeCost LwMax + 120) + 910

/-- Cap on the length of the batch that enters level `j` of the update loop of Branch B, when the
outer batch has `u` updates. Level `0` gets the internal batch (`u` updates). Level `j + 1` gets
the batch that level `j` forwards. Its length is at most the change of tool cost at level `j`,
and `stepCap j b` bounds that change when the batch that enters level `j` has at most `b`
updates. -/
@[expose] def branchBCapUL (stepCap : ℕ → ℕ → ℕ) (u : ℕ) : ℕ → ℕ
  | 0 => u
  | j + 1 => stepCap j (branchBCapUL stepCap u j)

/-- Cap on the batch words that enter level `j` of the update loop of Branch B: `4 u + 1` at
level `0` (a refresh batch), and `5 c + 1` for a forwarded batch of encoding at most `c`. -/
@[expose] def branchBCapBW (stepCap : ℕ → ℕ → ℕ) (u : ℕ) : ℕ → ℕ
  | 0 => 4 * u + 1
  | j + 1 => 5 * branchBCapUL stepCap u (j + 1) + 1

/-- Cap on the edit words that enter level `j` of the update loop of Branch B: `10 u + 1` at
level `0`, and the bound of the machine contract of the step at level `j` after that. -/
@[expose] noncomputable def branchBCapEW (edMul : ℕ) (cfg : Alg2Config) (stepCap : ℕ → ℕ → ℕ) (u : ℕ) :
    ℕ → ℕ
  | 0 => 10 * u + 1
  | j + 1 => edMul * (branchBCapUL stepCap u (j + 1) +
      (branchBCapBW stepCap u j + branchBCapEW edMul cfg stepCap u j + 1) *
        SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀)

/-- Level-by-level suffix rebuild cost matching `ordRebuildLevelBodyKFBL_runs_live`. -/
@[expose] noncomputable def updateCoreRebuildLevelCost (L capExp : ℕ) (cfg : Alg2Config)
    (Psc : SparseCoreOrdParams) (next : ChainState cfg.T cfg.P) (j : ℕ) : ℕ :=
  Psc.mul * cfg.T.cost (next.scState j) +
    ordLevelLiveCost L capExp Psc (next.lvlM j) next.N₀
      (next.G j).n (next.G j).m (next.G (j + 1)).n (next.G (j + 1)).m
      (2 * (next.G j).n + 2 * (next.G j).m + 1)
      (2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m + 1) + 26

/-! ### 4. Bounded `KFBL` operational space & cost envelope (`UpdateCoreOpsHypKFBL`) -/

/-- Operational space and cost domination hypotheses for `ordChainUpdateCoreBody` under
`sparseCoreOrdMachineContractKFBL`.

Compared to `UpdateCoreOpsHyp` (`WireChainCoreOps.lean`):
* all 5 placement/cap fields (`op0/2/3/5Placement`, `ordRotCap`) are removed;
* every space and cost quantifier is bounded by reached-state facts (`ShiftLoopLevelFacts`,
  `UpdateCoreModelInvKFBL`, `model.chain.N₀ = cfg.N₀`, `model.chain.lvlM = levelM`);
* `costTotalBranchA` carries the `level0Rebuilt` guard;
* `costTotalBranchB` omits `collectCopyLSFForestsLoop` over `[0, d)` and non-rebuilt forest packing,
  charging `fiChanges` tree edits to `treeMul · Δ totalTreeUpdates`, live suffix copies/rebuilds
  and forwarded step costs to `toolMul · Δ totalRuntime`, and leaving `coreFixed` completely free
  of `m`, `N₀`, caps, and `forestEdgeCap`. -/
structure UpdateCoreOpsHypKFBL
    {w L P m capExp capLimit fcap lastMul intCapMax forestEdgeCap drainUnit edMul mThresh : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {allocation lastAlloc : ℕ → List ℕ → ℕ}
    (levelSpace : ℕ → ℕ)
    (levelCost : ChainState cfg.T cfg.P → ℕ → ℕ)
    (updStepSpace : ℕ → ℕ → ℕ)
    (lastSpace termUpdSpace : ℕ) (stepCap : ℕ → ℕ → ℕ) : Prop where
  /-- Suffix level rebuild space for `j < d` on reached states (`lvlM = levelM`, `N₀ = cfg.N₀`). -/
  levelSpaceDom : ∀ (next : ChainState cfg.T cfg.P) (j gB lB grB oB h : ℕ),
    j < cfg.P.d →
    ShiftLoopLevelFacts cfg next →
    (next.G (j + 1)).m ≤ levelM cfg.TP cfg.P (j + 1) →
    ordLevelSpace L capExp capLimit
      (allocation 6 [gB, lB, grB, oB, cfg.P.k, next.lvlM j, next.N₀, L, fmt.precision,
        Expander.chosenL (cfg.P.M₀ ^ 2), h])
      (next.lvlM j) next.N₀ (next.G (j + 1)).m ≤ levelSpace j
  /-- Terminal level rebuild space. -/
  lastSpaceDom : ∀ (gB lB h : ℕ),
    lastAlloc 1 [gB, lB, L, fmt.precision, h] ≤ lastSpace
  /-- Space of the plain step of the update loop at level `idx < d`, for inputs within the caps
  `branchBCapBW`, `branchBCapEW`, `branchBCapUL` of an outer batch of `uLen` updates (the form of
  the step space of `wireBranchBLoopKFBL_runs`). -/
  updStepSpaceDom : ∀ (idx uLen coreH gB bPtr bW ePtr eW lB h nU uL : ℕ),
    idx < cfg.P.d →
    bW ≤ branchBCapBW stepCap uLen idx →
    eW ≤ branchBCapEW edMul cfg stepCap uLen idx →
    nU ≤ branchBCapUL stepCap uLen (idx + 1) →
    uL ≤ branchBCapUL stepCap uLen idx →
    3 * allocation 0 [coreH, gB, bPtr, bW, ePtr, eW, lB, lB, h] + 7 +
      nU * wireCoreLenEdgeSpace (ordLevelLwMax L capExp (levelM cfg.TP cfg.P idx) cfg.N₀) +
      uL + nU ≤ updStepSpace idx uLen
  /-- Space of the terminal exit of the update loop when the last level gets a non-empty batch
  (the room of `wireBranchBTermKFBL_runs_exit` at `nextM = levelM d`, and the `7` words after it). -/
  termUpdSpaceDom :
    1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
      levelM cfg.TP cfg.P cfg.P.d * wireCoreLenEdgeSpace
        (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) +
      (2 + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P cfg.P.d) + lastSpace + 7 ≤ termUpdSpace
  /-- Live per-level suffix rebuild cost domination. -/
  levelCostDom : ∀ (next : ChainState cfg.T cfg.P) (j : ℕ),
    j < cfg.P.d →
    updateCoreRebuildLevelCost L capExp cfg Psc next j ≤ levelCost next j
  /-- Total space budget for Branch A (level-0 rebuild). -/
  spaceTotalBranchA : ∀ (n rootECap uLen mNew : ℕ),
    n ≤ cfg.N₀ → rootECap ≤ intCapMax → mNew ≤ intCapMax →
    (1 + 12 * cfg.P.d) + 3 * (cfg.P.d + 1) + 4 + cfg.P.d * 5 +
      (3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L)) +
      (3 * L + uLen * wireRefreshOneSpace L) +
      (2 * intCapMax) + wireCompactLevel0Space n rootECap L mNew +
      (1 + 4 * n + 2 * rootECap) +
      (Finset.range cfg.P.d).sum levelSpace + lastSpace + 5 * cfg.P.d +
      (3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L)) + 1 ≤ coreSpace uLen
  /-- Total space budget for Branch B: Phase 0 and the dispatch, Sync 1, the refresh of level
  `0`, the copy of the level-`0` batch, the plain steps, the interior exit, the terminal exit,
  Sync 2a, Sync 2b, and a margin. -/
  spaceTotalBranchB : ∀ (uLen : ℕ),
    (1 + 12 * cfg.P.d) + 3 * (cfg.P.d + 1) + 4 +
      (3 * uLen + uLen * wireTreeSyncEditSpace L) +
      (3 * L + uLen * wireRefreshOneSpace L) + (4 * uLen + 1) +
      (Finset.range cfg.P.d).sum (fun j => updStepSpace j uLen) +
      (10 * cfg.P.d + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P 0 + 10 +
        (Finset.range cfg.P.d).sum levelSpace + lastSpace) +
      termUpdSpace +
      (2 * forestEdgeCap + forestEdgeCap * wireTreeSyncEditSpace L + 1) +
      (3 * intCapMax + 4 * forestEdgeCap + forestEdgeCap * wireTreeSyncEditSpace L + 1) +
      (5 + fcap + 5 * cfg.P.d) ≤ coreSpace uLen
  /-- Total non-tree-update cost for Branch A (guarded by `level0Rebuilt = true`). -/
  costTotalBranchA : ∀ (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ)
    (intCap rootECap : ℕ),
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let U_int := tr.2.2.2.2
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let n := model.extG.n
    let mNew := (modelPre.chain.G 0).m
    let sumOld := graphListEdgeSum (chainSuffixForests model.chain 0)
    let sumNew := graphListEdgeSum (chainSuffixForests modelPre.chain 0)
    0 < cfg.P.d →
    intRebuildThreshold cfg.P model.chain.N₀ 0 < model.chain.updCount 0 + U_int.length →
    FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh →
    RefreshBatch model.extG U →
    UpdateCoreModelInvKFBL model U gVec lVec →
    model.extG.m = m →
    rootECap ≤ intCap →
    intCap ≤ initTargetCap cfg G →
    G.E.sup id ≤ G.m →
    G.m = m →
    cfg.P.M₀ ≤ m + mThresh →
    cfg.P.d * (Psc.readout + 48) +
      (230 * (cfg.P.d + 1) + 85 * sumOld + 300) +
      sumOld * (wireTreeSyncEditCost L drainUnit + 2) +
      (U.length * (wireRefreshOneCost L + 120) + 71 * L + 220) +
      (670 * (4 * U.length + 1) + 30) +
      (U.length * (17 * L + 70) + 80) +
      (85 * intCap + 40 * m + 110) +
      wireCompactLevel0Cost n rootECap intCap L mNew +
      (150 * rootECap + 60 * n + 120) + 150 +
      (Finset.range cfg.P.d).sum (fun j => levelCost modelPre.chain j + 9) +
      lastMul * (cfg.L.cost (modelPre.chain.G cfg.P.d) + 1) +
      cfg.P.d * (Psc.readout + 48) + 40 * cfg.P.d +
      (230 * (cfg.P.d + 1) + 85 * sumNew + 260) +
      sumNew * (wireTreeSyncEditCost L drainUnit + 2) +
      (80 * mNew + mNew * drainUnit + 120) + 1500 ≤
      coreFixed U.length + toolMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime)
  /-- Total non-tree-update cost for Branch B (no non-rebuilt forest copies or packing; `fiChanges`
  edits paid by `treeMul · Δ totalTreeUpdates`). Covers all three outcomes:
  1. Interior rebuild at `0 < i₀ < d` (live copy + suffix rebuild + suffix-only forest packing);
  2. Non-empty terminal rebuild at `i₀ = d` (live copy + terminal rebuild + terminal-only packing);
  3. Empty terminal step at `i₀ = d` (no suffix rebuild, no forest packing). -/
  costTotalBranchB : ∀ (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ)
    (bW eW nextULen Δc : ℕ → ℕ) (i₀ : ℕ),
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let U_int := tr.2.2.2.2
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let d := cfg.P.d
    let B₀ := SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀
    let LwMax₀ := ordLevelLwMax L capExp (levelM cfg.TP cfg.P 0) cfg.N₀
    0 < d → i₀ ≤ d →
    ¬ (intRebuildThreshold cfg.P model.chain.N₀ 0 < model.chain.updCount 0 + U_int.length) →
    UpdateCoreModelInvKFBL model U gVec lVec →
    -- Level-0 input batch/edit word bounds from `RefreshBatch`
    bW 0 ≤ 4 * U.length + 1 →
    eW 0 ≤ 10 * U.length + 1 →
    -- Inductive step bounds on forwarded batch/edit word counts along `[0, i₀)`
    (∀ j < i₀, nextULen j ≤ Δc j ∧ bW (j + 1) ≤ 6 * Δc j + 1 ∧
      eW (j + 1) ≤ edMul * (Δc j + (bW j + eW j + 1) * B₀)) →
    let prefixCost :=
      (134 * U.length + 65) + U.length * (wireTreeSyncEditCost L drainUnit + 2) +
      (U.length * (wireRefreshOneCost L + 120) + 71 * L + 220) +
      (670 * (4 * U.length + 1) + 30) +
      (U.length * (17 * L + 70) + 80) +
      (Finset.range i₀).sum (fun j =>
        updateCoreNoRebuildStepCost L capExp Psc cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀
          (bW j) (eW j) (nextULen j) (Δc j) + 30) +
      (130 * U.length + U.length * drainUnit + 100) + 100 * d + 1000
    let rhs := coreFixed U.length + toolMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime)
    -- Case 1: Interior rebuild at `0 < i₀ < d`
    ((0 < i₀ → i₀ < d →
      (∀ j, i₀ ≤ j → j < d → ∃ ℓj gj ordj,
        modelPre.chain.scState j =
          cfg.T.initOrd cfg.P.k (modelPre.chain.lvlM j) modelPre.chain.N₀ (modelPre.chain.G j) ℓj gj ordj) →
      (Finset.range i₀).sum Δc +
        (Finset.Ico i₀ d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) +
        cfg.L.cost (modelPre.chain.G d) ≤
        modelPre.chain.totalRuntime - model.chain.totalRuntime →
      (model.chain.G i₀).m ≤ (modelPre.chain.G i₀).m + bW i₀ →
      let sumOldSuf := graphListEdgeSum (chainSuffixForests model.chain i₀)
      let sumNewSuf := graphListEdgeSum (chainSuffixForests modelPre.chain i₀)
      prefixCost +
        670 * bW i₀ +
        Psc.mul * (2 * (modelPre.chain.G i₀).n + 2 * (modelPre.chain.G i₀).m + 2) * B₀ +
        2 * Psc.readout + 200 +
        (Finset.Ico i₀ d).sum (fun j => levelCost modelPre.chain j + 9) +
        lastMul * (cfg.L.cost (modelPre.chain.G d) + 1) +
        2 * d * (Psc.readout + 68) +
        (230 * (d + 1) + 85 * (sumOldSuf + sumNewSuf) + 260) +
        70 * (sumOldSuf + sumNewSuf) + 300 ≤ rhs) ∧
     -- Case 2: Non-empty terminal rebuild at `i₀ = d`
     (i₀ = d →
      (Finset.range d).sum Δc + cfg.L.cost (modelPre.chain.G d) ≤
        modelPre.chain.totalRuntime - model.chain.totalRuntime →
      let Gd := modelPre.chain.G d
      let oldLastF := (model.chain.lastLSFs model.chain.lastBran).F.F
      let newLastF := (modelPre.chain.lastLSFs modelPre.chain.lastBran).F.F
      prefixCost +
        3 * Psc.readout + copyGraphLiveCost Gd.n Gd.m +
        Gd.m * (wireCoreLenEdgeCost LwMax₀ + 30) +
        Psc.mul * (2 * Gd.n + 2 * Gd.m + 2) * B₀ +
        lastMul * (cfg.L.cost Gd + 1) +
        (230 * 2 + 85 * (oldLastF.m + newLastF.m) + 260) +
        70 * (oldLastF.m + newLastF.m) + 400 ≤ rhs) ∧
     -- Case 3: Empty terminal step at `i₀ = d`
     (i₀ = d →
      (Finset.range d).sum Δc ≤ modelPre.chain.totalRuntime - model.chain.totalRuntime →
      prefixCost + 600 ≤ rhs))

/-! ### 5. Select-block hook outputs (12 words per level) -/

/-- The `n` words at `a` lie in `[lo, hi)` and off the footprint `foot`. -/
@[expose] def SelOutWordsAt (foot : ℕ → Prop) (lo hi a n : ℕ) : Prop :=
  lo ≤ a ∧ a + n ≤ hi ∧ ∀ t < n, ¬ foot (a + t)

/-- A table of `Lw` words per edge of `E` with base `mem a`: the base is a machine word, each row
ends below `hi`, and each word lies in the footprint `foot` or in `[lo, hi)`. -/
@[expose] def SelOutTableAt (w : ℕ) (foot : ℕ → Prop) (lo hi : ℕ) (mem : ℕ → ℕ) (a Lw : ℕ)
    (E : Finset ℕ) : Prop :=
  mem a < 2 ^ w ∧
  ∀ e ∈ E, mem a + e * Lw + Lw ≤ hi ∧
    ∀ t < Lw, foot (mem a + e * Lw + t) ∨ (lo ≤ mem a + e * Lw + t ∧ mem a + e * Lw + t < hi)

/-- The tie of the first rebuilt level `firstReb`, of the batches `levelU j` that enter the
levels, and of the batches `levelUS j` that the non-rebuilt levels forward, to the model step
`oldCh ↦ newCh` of `Update`. The value `firstReb = 0` means that level `0` is rebuilt (Branch A),
`0 < firstReb < d` that the levels from `firstReb` on are rebuilt, `firstReb = d` that only the last
level is rebuilt, and `firstReb = d + 1` that no level is rebuilt. -/
@[expose] def UpdateCoreLevelLink {cfg : Alg2Config} (oldCh newCh : ChainState cfg.T cfg.P)
    (firstReb : ℕ) (levelU levelUS : ℕ → List Update) : Prop :=
  let d := cfg.P.d
  firstReb ≤ d + 1 ∧
  (firstReb < d →
    firstRebuiltLevel d oldCh.rebuildCount newCh.rebuildCount = some firstReb) ∧
  (d ≤ firstReb → firstRebuiltLevel d oldCh.rebuildCount newCh.rebuildCount = none) ∧
  (0 < firstReb → NonRebuiltBatches cfg.T oldCh newCh levelU (firstReb - 1)) ∧
  (∀ j < min firstReb d,
    levelU (j + 1) = levelUS j ∧
    ∃ ℓj gj ordj,
      newCh.scState j = (cfg.T.updateOrd (oldCh.scState j) (levelU j) ℓj gj ordj).1 ∧
      levelUS j = (cfg.T.updateOrd (oldCh.scState j) (levelU j) ℓj gj ordj).2 (oldCh.bran j)) ∧
  (firstReb = d → levelU d ≠ [])

/-- Memory layout of the chain-update outputs that the select part of `Update` reads after
`ordChainUpdateCoreBody`. The word `mem selOutBase` is `firstReb`, and the `1 + 12 min(firstReb, d)`
words from `selOutBase` lie below `nextHeap` and off the footprint `foot`. For each non-rebuilt level
`j < min firstReb d`, the 12-word slot at `slot := selOutBase + 1 + 12 * j` holds:
* words `slot + 0 .. slot + 7`: `LevelDiffListsAt mem slot (diffLists j)`, where
  `uG = coreBatchTouchedEdges (levelU j)`, `fDel` lists the edges that leave the forest of the level
  (without repeats), `uS = coreBatchTouchedEdges (levelUS j)`, and `reemb` is the re-embedding list
  of the sparse core (`reembFn`);
* words `slot + 8, slot + 9`: a 2-word descriptor `stDesc` and the width `stLw` of the stretch
  tables of the new forest, with `StretchValuesAt`;
* words `slot + 10, slot + 11`: the batch `levelU j` at `uPtr` in `uWords` words, against the old
  graph of the level, in the compact encoding (`SmallBatchAt`: at most
  `5 * (oldCh.G j).batchEnc (levelU j) + 1` words), so that the words of all the batches sum to
  `O(Δ totalRuntime)`.
The four lists, the batch and the descriptor lie in `[selOutBase, nextHeap)` and off `foot`; the
two stretch tables lie in `foot` or in `[selOutBase, nextHeap)`. Rebuilt levels have no slot
content, since the select part refills them from the sparse core. -/
@[expose] def UpdateCoreSelectOutAt (w P L capExp vCap eCap : ℕ) {cfg : Alg2Config}
    (reembFn : ToolReembFn cfg.T) (foot : ℕ → Prop) (mem : ℕ → ℕ)
    (selOutBase nextHeap firstReb : ℕ) (oldCh newCh : ChainState cfg.T cfg.P)
    (levelU levelUS : ℕ → List Update) (diffLists : ℕ → LevelDiffLists) : Prop :=
  let d := cfg.P.d
  mem selOutBase = firstReb ∧
  SelOutWordsAt foot selOutBase nextHeap selOutBase (1 + 12 * min firstReb d) ∧
  ∀ j < min firstReb d,
    let slot := selOutBase + 1 + 12 * j
    let D := diffLists j
    let stDesc := mem (slot + 8)
    let stLw := mem (slot + 9)
    let uPtr := mem (slot + 10)
    let uWords := mem (slot + 11)
    LevelDiffListsAt mem slot D ∧
    D.uG = coreBatchTouchedEdges (levelU j) ∧
    D.fDel.Nodup ∧
    D.fDel.toFinset = (cfg.T.lsfs (oldCh.scState j) (oldCh.bran j)).F.F.E \
      (cfg.T.lsfs (newCh.scState j) (newCh.bran j)).F.F.E ∧
    D.uS = coreBatchTouchedEdges (levelUS j) ∧
    D.reemb = reembFn (oldCh.scState j) (levelU j) (newCh.levelOrd j) (oldCh.bran j) ∧
    SelOutWordsAt foot selOutBase nextHeap (mem (slot + 0)) D.uG.length ∧
    SelOutWordsAt foot selOutBase nextHeap (mem (slot + 2)) D.fDel.length ∧
    SelOutWordsAt foot selOutBase nextHeap (mem (slot + 4)) D.uS.length ∧
    SelOutWordsAt foot selOutBase nextHeap (mem (slot + 6)) D.reemb.length ∧
    SmallBatchAt mem uPtr (oldCh.G j) (levelU j) uWords ∧
    BatchWithinCaps vCap eCap (levelU j) ∧
    (∀ t < uWords, mem (uPtr + t) < 2 ^ w) ∧
    SelOutWordsAt foot selOutBase nextHeap uPtr uWords ∧
    SelOutWordsAt foot selOutBase nextHeap stDesc 2 ∧
    stLw ≤ ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀ ∧
    StretchValuesAt mem stDesc 4 stLw P (newCh.G j).E
      (cfg.T.lsfs (newCh.scState j) (newCh.bran j)).wstr ∧
    SelOutTableAt w foot selOutBase nextHeap mem stDesc stLw (newCh.G j).E ∧
    SelOutTableAt w foot selOutBase nextHeap mem (stDesc + 1) stLw (newCh.G j).E

/-! ### 6. Extended `KFBL`/`KFRBL` chain-update specification (`OrdChainUpdateCoreSpecWExtKFBL`) -/

/-- Extended chain-update core contract under `sparseCoreOrdMachineContractKFRBL`:
* carries every reached-state precondition its postcondition needs (`SolverLevelMetaAt`,
  `SolverLevelCapsAt`, `PathTreeNumericInv`, `OffTreeRecInv`, `OffTreeRecBound`,
  `ShiftLoopChainInv`, `UpdateCoreModelInv`, `UpdateCoreModelInvKFBL`);
* omits `hNewInOff0` (newly inserted tree edges need not be absent from `inOffReady`), and does
  not ask that the `inOffReady` bits of the fresh names be zero: the off-tree push
  (`offTreePushBody`) skips a name whose bit is set, and `OffReadyInv` then says that the name is
  already in the list;
* needs only `tok.rootECap ≤ tok.intCap` (part of `UpdateCoreModelInv`), not a fixed root cap;
* asks `model.extG.m = m`, so that the rename and the compaction of Branch A, which cost
  about `intCap + m`, are paid by the rebuild of level `0`;
* preserves `SolverLevelMetaAt` and `SolverLevelCapsAt` across `Update`, and keeps the table and
  the two select addresses (`solverSelectHeapAddr`, `solverSelectBlocksAddr`);
* exposes `UpdateCoreSelectOutAt` at `selOutBase := heap` (12 words per non-rebuilt level) and
  ties it to the model with `UpdateCoreLevelLink`;
* charges `40` steps per entry of the re-embedding lists it copies, on top of the usual budget,
  so that the select-aware wrapper pays them from its re-embedding potential. -/
@[expose] def OrdChainUpdateCoreSpecWExtKFBL
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap : ℕ)
    (cfg : Alg2Config) (G : MGraph) (reembFn : ToolReembFn cfg.T)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (ordChainCoreProc : ℕ) (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ)
    (B_bound R_bound : ℤ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[ordChainCoreProc]? = some body ∧
    ∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
      (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore)
      (U : List Update) (B R : ℤ),
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      Rrep.rep root model tok mem0 →
      SolverLevelMetaAt P V model tok mem0 →
      SolverLevelCapsAt vCap eCap model tok mem0 →
      tok.intCap = initTargetCap cfg G →
      model.extG.m = m →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem0 tok.edgeRecords B →
      OffTreeRecBound model L mem0 tok.edgeRecords B →
      B ≤ B_bound → R ≤ R_bound →
      Chain.Ordered.ShiftLoopChainInv cfg model.chain →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
      UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B →
      UpdateCoreModelInvKFBL model U gVec lVec →
      tok.intCap ≤ intCapMax →
      graphListEdgeSum (chainSuffixForests model.chain 0) +
        graphListEdgeSum (chainSuffixForests modelPre.chain 0) ≤ forestEdgeCap →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      (∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a) →
      FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        tr.2.1 tr.2.2.1 tr.2.2.2.1 →
      tr.2.2.2.1 ≤ tok.intCap →
      BatchAt mem uIntBuf tr.2.2.2.2 →
      SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf) →
      OrdEditsAt mem editsPtr (batchToOrdEdits tr.2.2.2.2) editWords →
      (∀ j < editWords, mem (editsPtr + j) < 2 ^ w) →
      editsPtr + editWords = heap →
      RefreshBatch model.extG U →
      (∀ a, Rrep.foot root tok a → a < uIntBuf) →
      g + m * L ≤ uIntBuf → l + m * L ≤ uIntBuf →
      uIntBuf + cfg.P.d ≤ editsPtr →
      ZeroFrom mem heap →
      heap + coreSpace U.length < 2 ^ w →
      ∃ nextHeap cost out tok' B' R' firstReb levelU levelUS diffLists,
        Runs w p ω body (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
          (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + coreSpace U.length ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        tok'.rootECap = tok.rootECap ∧ tok'.table = tok.table ∧
        B' ≤ B_bound ∧ R' ≤ R_bound ∧
        Rrep.rep root modelPre tok' out.mem ∧
        SolverLevelMetaAt P V modelPre tok' out.mem ∧
        SolverLevelCapsAt vCap eCap modelPre tok' out.mem ∧
        out.mem (solverLevelMetaAddr tok'.table cfg.P.d + cfg.P.d) = tok'.rootGraph ∧
        PathTreeNumericInv tok'.tree tok'.trees B' R' ∧
        OffTreeRecInv modelPre L out.mem tok'.edgeRecords B' ∧
        OffTreeRecBound modelPre L out.mem tok'.edgeRecords B' ∧
        out.mem (solverSelectHeapAddr tok.table cfg.P.d) =
          mem0 (solverSelectHeapAddr tok.table cfg.P.d) ∧
        out.mem (solverSelectBlocksAddr tok.table cfg.P.d) =
          mem0 (solverSelectBlocksAddr tok.table cfg.P.d) ∧
        UpdateCoreLevelLink model.chain modelPre.chain firstReb levelU levelUS ∧
        UpdateCoreSelectOutAt w P L capExp vCap eCap reembFn (Rrep.foot root tok') out.mem heap
          nextHeap firstReb model.chain modelPre.chain levelU levelUS diffLists ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          coreFixed U.length +
            toolMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            40 * (Finset.range (min firstReb cfg.P.d)).sum (fun j => (diffLists j).reemb.length) +
            Rrep.phi root tok mem0

end MinCostFlow.MinRatio
