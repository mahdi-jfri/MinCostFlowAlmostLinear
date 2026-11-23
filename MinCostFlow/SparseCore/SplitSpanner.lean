module

public import MinCostFlow.SparseCore.SplitSpannerBuildUS

import Mathlib.Tactic.Linarith

/-!
# Concrete `SparseCoreTool` via vertex-split core graphs and `DynSpanner`

Implements `sparseCoreTool` following `algo:dynasparsecore` ([chen2022maximum] v2, Algorithm 4 /
Lemma 7.5 + Lemma 5.17, pages 22–24):
* Maintains `k` independent component-wise online LSFs (`initCompLSF` / `compLSFBatch`) and
  their per-component vertex-split quotients `ts : Finset ℕ → TildeState` (`tildeStepBatch`),
  initializing `DynSpanner` buckets eagerly on `largeComps k G₀` and lazily when a tiny/isolated
  component is first touched.
* Splits initial quotient edges into length-doubling buckets (`bucketOf`) on active subgraphs and
  maintains one `DynSpannerState L` per `(C, b)` (`filterBucketBatch`), using `DynSpanner.theorem_8_2`
  and `DynSpanner.sparsity_H`.
* Emits `U_S` via `buildUSReinsert` (with `D_total` re-insertion in `sparseCoreTool`).
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 4. Concrete `SparseCoreTool` definition and trajectory theorem -/

/-- Per-branch state maintained by `sparseCoreTool` for `j < k`. -/
structure TreeCoreState (L : ℕ) where
  m₀ : ℕ
  n₀ : ℕ
  Δ₀ : ℕ
  splitBound : ℕ
  cs : CompLSFState
  activeComps : Finset (Finset ℕ)
  ts : Finset ℕ → TildeState
  origBucket : ℕ → ℤ
  activeBuckets : Finset ℕ → Finset ℤ
  lazyInitCost : Finset ℕ → ℕ
  dyn : Finset ℕ × ℤ → DynSpannerState L
  S_cur : MGraph
  cost : ℕ

/-- Embedding maintained for branch `j`: surviving edges in `S_cur` embed as themselves,
missing active-component quotient edges use `piTotal (dyn (C, origBucket e))`, and core self-loops
(including edges in untouched tiny components) embed as `[]`. -/
noncomputable def TreeCoreState.emb {L : ℕ} (st : TreeCoreState L) : Embedding :=
  open Classical in
  fun e =>
    if e ∈ st.S_cur.E then [(e, true)]
    else if h : ∃ C ∈ st.activeComps, e ∈ (st.ts C).C.E then
      piTotal (st.dyn (h.choose, st.origBucket e)) e
    else []

/-- Initialize one branch `j < k` on `(G₀, ℓ₀)` with size upper bounds `(M, N)`. Edge lengths are
masked to `G₀.E` via `safeLen G₀ ℓ₀`, so the initial state depends only on `ℓ₀` restricted to `G₀.E`. -/
noncomputable def initTreeCore
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (j : ℕ) : TreeCoreState L :=
  open Classical in
  let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
  let actComps₀ := largeComps k G₀
  let ts₀ : Finset ℕ → TildeState := fun C => initTildeState (cs₀.compSt C)
  let origB : ℕ → ℤ := fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e)
  let actB : Finset ℕ → Finset ℤ := fun C => (ts₀ C).C.E.image origB
  let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) * (G₀.maxDeg + 1) +
    Nat.ceil (56 * (M : ℝ) / (k : ℝ))
  let initCB : Finset ℕ → ℤ → InitOut L := fun C b =>
    let Hb₀ := initBucketGraph (cs₀.compSt C) ℓ₀ b
    DynSpanner.init Hb₀ L (phaseBase (Hb₀.n + splitB) L) (sparsify M)
  let lazyC : Finset ℕ → ℕ := fun C => (actB C).sum fun b => (initCB C b).cost
  let C₀ := coreGraph G₀ cs₀.lsf
  let S₀_E := actComps₀.biUnion fun C => (actB C).biUnion fun b => (initCB C b).state.H.E
  let S₀_cur : MGraph := { V := cs₀.RF.R, E := S₀_E, tail := C₀.tail, head := C₀.head }
  let initCost := G₀.m + (activeSubgraph G₀).n + 1 + actComps₀.sum lazyC
  { m₀ := M
    n₀ := N
    Δ₀ := G₀.maxDeg
    splitBound := splitB
    cs := cs₀
    activeComps := actComps₀
    ts := ts₀
    origBucket := origB
    activeBuckets := actB
    lazyInitCost := lazyC
    dyn := fun p => (initCB p.1 p.2).state
    S_cur := S₀_cur
    cost := initCost }

/-- Per-branch step data returned by `stepTreeCoreAux` for proof bookkeeping alongside state/batch. -/
structure TreeStepInfo (L : ℕ) where
  state : TreeCoreState L
  U_S : List Update
  U_C : Finset ℕ → List Update
  U_b : Finset ℕ × ℤ → List Update
  stepOut : Finset ℕ × ℤ → StepOut L
  newlyActive : Finset (Finset ℕ)
  D_spanner : Finset ℕ
  D_leftS : Finset ℕ
  D_total : Finset ℕ

/-- Update one branch `j < k` on batch `U` and produce `(nextState, U_S)` plus diagnostics.
When `reinsertD = true`, surviving edges in `D_total` are deleted and reinserted in `U_S`
(`jtree.tex` line 425); `reinsertD = false` keeps `D_total` un-reinserted (`sparseCoreToolKeep`). -/
noncomputable def stepTreeCoreAuxWith {L : ℕ} (reinsertD : Bool)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : TreeCoreState L) (U : List Update) : TreeStepInfo L :=
  open Classical in
  let touched := touchedCompsBatch st.cs U
  let newlyActive := touched \ st.activeComps
  let active' := st.activeComps ∪ newlyActive
  let cs' := compLSFBatch st.cs U
  let U_proj : Finset ℕ → List Update := fun C => projCompBatchG st.cs.G (st.cs.compSt C).G U
  let td : Finset ℕ → List Update × TildeState × LSFState := fun C =>
    tildeStepBatch (st.cs.compSt C) (st.ts C) (U_proj C)
  let fB : Finset ℕ × ℤ → List Update := fun p =>
    (filterBucketBatch (st.dyn p).G (td p.1).1).2
  let spOut : Finset ℕ × ℤ → StepOut L := fun p =>
    DynSpanner.update (st.dyn p) (fB p) (sparsify st.m₀)
  let dynUnionE' := active'.biUnion fun C =>
    (st.activeBuckets C).biUnion fun b => (spOut (C, b)).state.H.E
  let extraComps' := active'.biUnion fun C =>
    ((cs'.compSt C).G.E \ (cs'.compSt C).RF.F.E) \ (td C).2.1.C.E
  let targetE' := dynUnionE' ∪ extraComps' ∪ cs'.crossEdges
  let D_sp := active'.biUnion fun C =>
    (st.activeBuckets C).biUnion fun b => (spOut (C, b)).D
  let D_left := active'.biUnion fun C =>
    (st.activeBuckets C).biUnion fun b =>
      (((st.dyn (C, b)).H.E ∩ (spOut (C, b)).state.G.E) \ (spOut (C, b)).state.H.E).biUnion
        fun e => walkEdges (piTotal (spOut (C, b)).state e)
  let D_tot := D_sp ∪ D_left
  let D_reins := if reinsertD then D_tot else ∅
  let U_S := buildUSReinsert st.cs U cs' st.S_cur targetE' D_reins
  let S_cur' := st.S_cur.applyBatch U_S
  let dynCost := active'.sum fun C =>
    (st.activeBuckets C).sum fun b => (spOut (C, b)).cost
  let lazyCost := newlyActive.sum fun C => st.lazyInitCost C
  let qCCost := active'.sum fun C => (td C).1.length
  let cStep := U.length + qCCost + U_S.length + dynCost + lazyCost
  let st' : TreeCoreState L :=
    { st with
      cs := cs'
      activeComps := active'
      ts := fun C => (td C).2.1
      dyn := fun p => (spOut p).state
      S_cur := S_cur'
      cost := st.cost + cStep }
  { state := st'
    U_S := U_S
    U_C := fun C => (td C).1
    U_b := fB
    stepOut := spOut
    newlyActive := newlyActive
    D_spanner := D_sp
    D_leftS := D_left
    D_total := D_tot }

@[reducible] noncomputable def stepTreeCoreAux {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : TreeCoreState L) (U : List Update) : TreeStepInfo L :=
  stepTreeCoreAuxWith true sparsify st U

@[reducible] noncomputable def stepTreeCoreAuxKeep {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : TreeCoreState L) (U : List Update) : TreeStepInfo L :=
  stepTreeCoreAuxWith false sparsify st U

lemma stepTreeCoreAuxWith_noReinsertPropagates {L : ℕ} (reinsertD : Bool)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (stPrev : TreeCoreState L) (U : List Update)
    (hBU : stPrev.cs.G.BatchIsValid U)
    (hS_sub : (coreGraph stPrev.cs.G stPrev.cs.lsf).IsSubgraph stPrev.S_cur)
    {actB : Finset ℕ → Finset ℤ} (hactB : stPrev.activeBuckets = actB)
    (hS_cur_E :
      let stCur := (stepTreeCoreAuxWith reinsertD sparsify stPrev U).state
      stCur.S_cur.E =
        (stCur.activeComps.biUnion fun C => (actB C).biUnion fun b => (stCur.dyn (C, b)).H.E) ∪
          (stCur.activeComps.biUnion fun C =>
            ((stCur.cs.compSt C).G.E \ (stCur.cs.compSt C).RF.F.E) \ (stCur.ts C).C.E) ∪
          stCur.cs.crossEdges) :
    ∀ e ∈ stPrev.S_cur.E,
      e ∈ (stepTreeCoreAuxWith reinsertD sparsify stPrev U).state.S_cur.E →
      (∀ u ∈ (stepTreeCoreAuxWith reinsertD sparsify stPrev U).U_S, ¬ u.Inserts e) →
      (reinsertD = true → e ∉ (stepTreeCoreAuxWith reinsertD sparsify stPrev U).D_total) ∧
        ∀ u ∈ U, ¬ u.Inserts e := by
  classical
  intro e hePrev heCur hNoIns
  let info := stepTreeCoreAuxWith reinsertD sparsify stPrev U
  let targetE' :=
    (info.state.activeComps.biUnion fun C => (stPrev.activeBuckets C).biUnion fun b =>
      (info.state.dyn (C, b)).H.E) ∪
      (info.state.activeComps.biUnion fun C =>
        ((info.state.cs.compSt C).G.E \ (info.state.cs.compSt C).RF.F.E) \ (info.state.ts C).C.E) ∪
      info.state.cs.crossEdges
  have hTgt : e ∈ targetE' := by
    have hE := hS_cur_E
    dsimp only at hE
    rw [hE] at heCur
    simpa only [targetE', hactB, info] using heCur
  have hUS : info.U_S = buildUSReinsert stPrev.cs U info.state.cs stPrev.S_cur targetE'
      (if reinsertD then info.D_total else ∅) := by
    dsimp only [info, stepTreeCoreAuxWith, targetE']
  have hProp := buildUSReinsert_noReinsertPropagates hBU hS_sub hePrev hTgt (hUS ▸ hNoIns)
  exact ⟨fun hr => by subst hr; exact hProp.1, hProp.2⟩

lemma stepTreeCoreAux_noReinsertPropagates {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (stPrev : TreeCoreState L) (U : List Update)
    (hBU : stPrev.cs.G.BatchIsValid U)
    (hS_sub : (coreGraph stPrev.cs.G stPrev.cs.lsf).IsSubgraph stPrev.S_cur)
    {actB : Finset ℕ → Finset ℤ} (hactB : stPrev.activeBuckets = actB)
    (hS_cur_E :
      let stCur := (stepTreeCoreAux sparsify stPrev U).state
      stCur.S_cur.E =
        (stCur.activeComps.biUnion fun C => (actB C).biUnion fun b => (stCur.dyn (C, b)).H.E) ∪
          (stCur.activeComps.biUnion fun C =>
            ((stCur.cs.compSt C).G.E \ (stCur.cs.compSt C).RF.F.E) \ (stCur.ts C).C.E) ∪
          stCur.cs.crossEdges) :
    ∀ e ∈ stPrev.S_cur.E,
      e ∈ (stepTreeCoreAux sparsify stPrev U).state.S_cur.E →
      (∀ u ∈ (stepTreeCoreAux sparsify stPrev U).U_S, ¬ u.Inserts e) →
      e ∉ (stepTreeCoreAux sparsify stPrev U).D_total ∧ ∀ u ∈ U, ¬ u.Inserts e := by
  intro e hePrev heCur hNoIns
  have h := stepTreeCoreAuxWith_noReinsertPropagates true sparsify stPrev U hBU hS_sub hactB
    hS_cur_E e hePrev heCur hNoIns
  exact ⟨h.1 rfl, h.2⟩

/-- Full state of `sparseCoreTool`. -/
structure SparseCoreState (L : ℕ) where
  isNonempty : Bool
  k : ℕ
  trees : ℕ → TreeCoreState L

/-- Concrete `SparseCoreTool` parameterized by `reinsertD : Bool` (`jtree.tex` line 425 when
`reinsertD = true`). -/
noncomputable def sparseCoreToolWith (reinsertD : Bool)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) : SparseCoreTool where
  State := SparseCoreState L
  init k M N G₀ ℓ₀ _g₀ :=
    open Classical in
    if G₀.V.Nonempty then
      { isNonempty := true
        k := k
        trees := fun j => initTreeCore oracle C_lsst L sparsify k M N G₀ ℓ₀ j }
    else
      { isNonempty := false
        k := k
        trees := fun j => initTreeCore oracle C_lsst L sparsify k M N G₀ ℓ₀ j }
  update st U _ℓ _g :=
    if st.isNonempty then
      let res := fun j => stepTreeCoreAuxWith reinsertD sparsify (st.trees j) U
      ({ st with trees := fun j => (res j).state }, fun j => (res j).U_S)
    else
      (st, fun _ => [])
  lsfs st j := if st.isNonempty then (st.trees j).cs.lsf else emptyLSF
  S st j := if st.isNonempty then (st.trees j).S_cur else emptyGraph
  emb st j := if st.isNonempty then (st.trees j).emb else fun _ => []
  cost st := if st.isNonempty then (Finset.range st.k).sum fun j => (st.trees j).cost else 0

/-- Concrete `SparseCoreTool` implementing **Algorithm 4 / Lemma 5.17** with `D_total`
re-insertion (`jtree.tex` line 425). -/
@[reducible] noncomputable def sparseCoreTool
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) : SparseCoreTool :=
  sparseCoreToolWith true oracle C_lsst L sparsify

/-- Non-reinserting specialization `sparseCoreToolKeep := sparseCoreToolWith false` retained for
historical Clause 3 counterexample witnesses. -/
@[reducible] noncomputable def sparseCoreToolKeep
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) : SparseCoreTool :=
  sparseCoreToolWith false oracle C_lsst L sparsify

/-- Trajectory of `TreeStepInfo` for fixed branch `j < k` over `t = 0, 1, …` at size bounds `(M, N)`. -/
noncomputable def treeRunSeqWith (reinsertD : Bool)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (j : ℕ) : ℕ → TreeCoreState L × List Update
  | 0 => (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j, [])
  | t + 1 =>
    let info := stepTreeCoreAuxWith reinsertD sparsify
      (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j t).1 (D.U (t + 1))
    (info.state, info.U_S)

@[reducible] noncomputable def treeRunSeq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (j : ℕ) : ℕ → TreeCoreState L × List Update :=
  treeRunSeqWith true oracle C_lsst L sparsify k M N D j

@[reducible] noncomputable def treeRunSeqKeep
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (j : ℕ) : ℕ → TreeCoreState L × List Update :=
  treeRunSeqWith false oracle C_lsst L sparsify k M N D j

lemma sparseCoreToolWith_runAt_eq_treeRunSeqWith (reinsertD : Bool)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (hV₀ : (D.G 0).V.Nonempty) :
    ∀ t,
      let r := (sparseCoreToolWith reinsertD oracle C_lsst L sparsify).runAt k M N D t
      r.1.isNonempty = true ∧
      r.1.k = k ∧
      (∀ j, r.1.trees j = (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j t).1) ∧
      (∀ t', 1 ≤ t' → ∀ j, ((sparseCoreToolWith reinsertD oracle C_lsst L sparsify).runAt k M N D t').2 j =
        (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j t').2) := by
  intro t
  suffices h : ∀ t',
      let r := (sparseCoreToolWith reinsertD oracle C_lsst L sparsify).runAt k M N D t'
      r.1.isNonempty = true ∧ r.1.k = k ∧
        (∀ j, r.1.trees j = (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j t').1) ∧
        (∀ j, (1 ≤ t' → r.2 j = (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j t').2)) from
    ⟨(h t).1, (h t).2.1, (h t).2.2.1, fun t' ht' j => (h t').2.2.2 j ht'⟩
  intro t'
  induction t' with
  | zero =>
    dsimp only [SparseCoreTool.runAt, sparseCoreToolWith, treeRunSeqWith]
    simp only [hV₀, ↓reduceIte]
    refine ⟨trivial, trivial, fun _ => trivial, fun _ h => by omega⟩
  | succ s ih =>
    dsimp only [SparseCoreTool.runAt]
    rcases ih with ⟨hne, hk, htr, _⟩
    dsimp only [sparseCoreToolWith] at hne hk htr ⊢
    simp only [hne, ↓reduceIte]
    refine ⟨trivial, hk, fun j => by rw [htr j]; rfl, fun j _ => by rw [htr j]; rfl⟩

lemma sparseCoreToolWith_run_eq_treeRunSeqWith (reinsertD : Bool)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k : ℕ) (D : DynamicInstance) (hV₀ : (D.G 0).V.Nonempty) :
    ∀ t,
      let r := (sparseCoreToolWith reinsertD oracle C_lsst L sparsify).run k D t
      r.1.isNonempty = true ∧
      r.1.k = k ∧
      (∀ j, r.1.trees j = (treeRunSeqWith reinsertD oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D j t).1) ∧
      (∀ t', 1 ≤ t' → ∀ j, ((sparseCoreToolWith reinsertD oracle C_lsst L sparsify).run k D t').2 j =
        (treeRunSeqWith reinsertD oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D j t').2) :=
  sparseCoreToolWith_runAt_eq_treeRunSeqWith reinsertD oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D hV₀

lemma sparseCoreTool_runAt_eq_treeRunSeq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (hV₀ : (D.G 0).V.Nonempty) :
    ∀ t,
      let r := (sparseCoreTool oracle C_lsst L sparsify).runAt k M N D t
      r.1.isNonempty = true ∧
      r.1.k = k ∧
      (∀ j, r.1.trees j = (treeRunSeq oracle C_lsst L sparsify k M N D j t).1) ∧
      (∀ t', 1 ≤ t' → ∀ j, ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D t').2 j =
        (treeRunSeq oracle C_lsst L sparsify k M N D j t').2) :=
  sparseCoreToolWith_runAt_eq_treeRunSeqWith true oracle C_lsst L sparsify k M N D hV₀

lemma sparseCoreTool_run_eq_treeRunSeq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k : ℕ) (D : DynamicInstance) (hV₀ : (D.G 0).V.Nonempty) :
    ∀ t,
      let r := (sparseCoreTool oracle C_lsst L sparsify).run k D t
      r.1.isNonempty = true ∧
      r.1.k = k ∧
      (∀ j, r.1.trees j = (treeRunSeq oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D j t).1) ∧
      (∀ t', 1 ≤ t' → ∀ j, ((sparseCoreTool oracle C_lsst L sparsify).run k D t').2 j =
        (treeRunSeq oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D j t').2) :=
  sparseCoreToolWith_run_eq_treeRunSeqWith true oracle C_lsst L sparsify k D hV₀

lemma treeRunSeqWith_fields_eq (reinsertD : Bool)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (j t : ℕ) :
    let stW := (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j t).1
    let st := (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
    stW.m₀ = st.m₀ ∧
    stW.n₀ = st.n₀ ∧
    stW.Δ₀ = st.Δ₀ ∧
    stW.splitBound = st.splitBound ∧
    stW.origBucket = st.origBucket ∧
    stW.activeBuckets = st.activeBuckets ∧
    stW.lazyInitCost = st.lazyInitCost ∧
    stW.cs = st.cs ∧
    stW.activeComps = st.activeComps ∧
    stW.ts = st.ts ∧
    stW.dyn = st.dyn := by
  induction t with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ s ih =>
    rcases ih with ⟨hm₀, hn₀, hΔ₀, hsb, horig, hactB, hlazy, hcs, hact, hts, hdyn⟩
    refine ⟨hm₀, hn₀, hΔ₀, hsb, horig, hactB, hlazy, ?_, ?_, ?_, ?_⟩
    · dsimp only [treeRunSeq, treeRunSeqWith, stepTreeCoreAux, stepTreeCoreAuxWith]; rw [hcs]
    · dsimp only [treeRunSeq, treeRunSeqWith, stepTreeCoreAux, stepTreeCoreAuxWith]; rw [hcs, hact]
    · funext C
      dsimp only [treeRunSeq, treeRunSeqWith, stepTreeCoreAux, stepTreeCoreAuxWith]
      rw [hcs, hts]
    · funext p
      dsimp only [treeRunSeq, treeRunSeqWith, stepTreeCoreAux, stepTreeCoreAuxWith]
      rw [hcs, hts, hdyn, hm₀]

lemma stepTreeCoreAuxWith_fields_eq (reinsertD : Bool) {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st₁ st₂ : TreeCoreState L) (U : List Update)
    (hm₀ : st₁.m₀ = st₂.m₀) (hcs : st₁.cs = st₂.cs) (hact : st₁.activeComps = st₂.activeComps)
    (hactB : st₁.activeBuckets = st₂.activeBuckets) (hts : st₁.ts = st₂.ts) (hdyn : st₁.dyn = st₂.dyn) :
    let i₁ := stepTreeCoreAuxWith reinsertD sparsify st₁ U
    let i₂ := stepTreeCoreAux sparsify st₂ U
    i₁.newlyActive = i₂.newlyActive ∧
    i₁.U_C = i₂.U_C ∧
    i₁.U_b = i₂.U_b ∧
    i₁.stepOut = i₂.stepOut ∧
    i₁.D_spanner = i₂.D_spanner ∧
    i₁.D_leftS = i₂.D_leftS ∧
    i₁.D_total = i₂.D_total := by
  dsimp only [stepTreeCoreAux, stepTreeCoreAuxWith]
  rw [hm₀, hcs, hact, hactB, hts, hdyn]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Per-`(C, b)` batch sequence `Us_{C, b}` of length `τ` sent to `DynSpanner` at size bounds `(M, N)`. -/
noncomputable def bucketBatchList
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (j : ℕ) (C : Finset ℕ) (b : ℤ) : List (List Update) :=
  (List.range τ).map fun t =>
    (stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j t).1 (D.U (t + 1))).U_b (C, b)

lemma bucketBatchList_getElem?
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (j : ℕ) (C : Finset ℕ) (b : ℤ) {t : ℕ} (ht : t < τ) :
    (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b)[t]? =
      some ((stepTreeCoreAux sparsify
        (treeRunSeq oracle C_lsst L sparsify k M N D j t).1 (D.U (t + 1))).U_b (C, b)) := by
  simp [bucketBatchList, ht]

/-- `initBucketGraph` on a component state depends only on edge lengths on `G₀.E`. -/
lemma initBucketGraph_eq_of_eq_on_E {S₀ : LSFState} {G₀ : MGraph}
    (hSub : S₀.G.E ⊆ G₀.E) {ℓ₀ ℓ₁ : ℕ → ℝ} (h : ∀ a ∈ G₀.E, ℓ₀ a = ℓ₁ a) (b : ℤ) :
    initBucketGraph S₀ ℓ₀ b = initBucketGraph S₀ ℓ₁ b := by
  classical
  unfold initBucketGraph
  dsimp only
  have hraw : rawBucket (initTildeState S₀).C (fun e => bucketOf (coreLen S₀.lsf ℓ₀ e)) b =
      rawBucket (initTildeState S₀).C (fun e => bucketOf (coreLen S₀.lsf ℓ₁ e)) b := by
    unfold rawBucket
    congr 1
    refine Finset.filter_congr fun e he => ?_
    have heG : e ∈ G₀.E := hSub (Finset.mem_sdiff.mp he).1
    simp only [coreLen, h e heG]
  rw [hraw]

/-- `initTreeCore` depends only on `ℓ₀` restricted to `G₀.E`. -/
theorem initTreeCore_eq_of_eq_on_E
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) {ℓ₀ ℓ₁ : ℕ → ℝ} (h : ∀ a ∈ G₀.E, ℓ₀ a = ℓ₁ a) (j : ℕ) :
    initTreeCore oracle C_lsst L sparsify k M N G₀ ℓ₀ j =
      initTreeCore oracle C_lsst L sparsify k M N G₀ ℓ₁ j := by
  classical
  have hsafe := safeLen_eq_of_eq_on_E h
  have hcs := initCompLSF_eq_of_eq_on_E oracle C_lsst G₀ h k j
  have hHb : ∀ C b,
      initBucketGraph ((initCompLSF oracle C_lsst G₀ ℓ₁ k j).compSt C) ℓ₀ b =
        initBucketGraph ((initCompLSF oracle C_lsst G₀ ℓ₁ k j).compSt C) ℓ₁ b := fun C b =>
    initBucketGraph_eq_of_eq_on_E (Finset.filter_subset _ _) h b
  unfold initTreeCore
  simp only [hcs, hsafe, hHb]

/-- `sparseCoreToolWith.init` depends only on `ℓ₀` restricted to `G₀.E` (and ignores `g₀`). -/
theorem sparseCoreToolWith_init_eq_of_eq_on_E (reinsertD : Bool)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) {ℓ₀ ℓ₁ : ℕ → ℝ} (h : ∀ a ∈ G₀.E, ℓ₀ a = ℓ₁ a) (g₀ g₁ : ℕ → ℝ) :
    (sparseCoreToolWith reinsertD oracle C_lsst L sparsify).init k M N G₀ ℓ₀ g₀ =
      (sparseCoreToolWith reinsertD oracle C_lsst L sparsify).init k M N G₀ ℓ₁ g₁ := by
  have htr : (fun j => initTreeCore oracle C_lsst L sparsify k M N G₀ ℓ₀ j) =
      (fun j => initTreeCore oracle C_lsst L sparsify k M N G₀ ℓ₁ j) :=
    funext fun j => initTreeCore_eq_of_eq_on_E oracle C_lsst L sparsify k M N G₀ h j
  change (if G₀.V.Nonempty then _ else _) = (if G₀.V.Nonempty then _ else _)
  split_ifs <;> simp only [htr]

/-- `sparseCoreToolWith.init` agrees identically with its zero-extension outside `G₀.E`. -/
theorem sparseCoreToolWith_init_eq_zeroExtension (reinsertD : Bool)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ) :
    (sparseCoreToolWith reinsertD oracle C_lsst L sparsify).init k M N G₀ ℓ₀ g₀ =
      (sparseCoreToolWith reinsertD oracle C_lsst L sparsify).init k M N G₀
        (fun a => if a ∈ G₀.E then ℓ₀ a else 0) g₀ :=
  sparseCoreToolWith_init_eq_of_eq_on_E reinsertD oracle C_lsst L sparsify k M N G₀
    (fun a ha => by simp [ha]) g₀ g₀

end

end MinCostFlow.SparseCore

