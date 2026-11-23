module

public import MinCostFlow.SparseCore.SplitSpanner
public import MinCostFlow.SparseCore.SplitSpannerBounds
public import MinCostFlow.Chain.SparseCoreTool
import MinCostFlow.SparseCore.Lemma517
import MinCostFlow.DynSpanner.StepTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Concrete Restartable `SparseCoreRestartTool`

Defines `sparseCoreRestartTool`, extending `MinCostFlow.SparseCore.sparseCoreTool` (Algorithm 4 /
Lemma 5.17, `jtree.tex` page 23) with a concrete branch restart operation
`restartTreeCore` (`jtree.tex` repair of `Shift(i)`): restarting branch `j` re-initializes the
bucketed `DynSpanner` instances `dyn (C, b)` on the current active component core quotient graphs
`activeSubgraph (rawBucket (tr.ts C).C tr.origBucket b)` via Theorem 8.2 (`DynSpanner.init`),
rebuilds `S_cur` for branch `j`, and leaves the branch's LSFs `(T_j, F_j, wstr_j)` as well as
every other branch `b ≠ j` completely untouched.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner

/-- Current bucket subgraph for `(C, b)` on tree state `tr` during a branch restart, obtained from
`(tr.ts C).C` by keeping edges in original length bucket `b` and dropping isolated vertices. -/
noncomputable def restartBucketGraph {L : ℕ} (tr : TreeCoreState L) (C : Finset ℕ) (b : ℤ) :
    MGraph :=
  activeSubgraph (rawBucket (tr.ts C).C tr.origBucket b)

/-- Restart one branch state `tr : TreeCoreState L` onto its current core graph `C(G, F_j)`:
re-initialize `dyn (C, b)` on `restartBucketGraph tr C b` for each active component `C` and bucket
`b`, update `S_cur` from surviving edges plus `extraComps` and `crossEdges`, add the restart
work to `cost`, and keep `cs` (`lsf`, `F`, `RF`), `ts`, `origBucket`, `activeComps`, and
`activeBuckets` unchanged. -/
noncomputable def restartTreeCore (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : TreeCoreState L) : TreeCoreState L :=
  open Classical in
  let initCB : Finset ℕ → ℤ → InitOut L := fun C b =>
    let Hb := restartBucketGraph tr C b
    DynSpanner.init Hb L (phaseBase (Hb.n + tr.splitBound) L) (sparsify tr.m₀)
  let dyn' : Finset ℕ × ℤ → DynSpannerState L := fun p =>
    if p.1 ∈ tr.activeComps then (initCB p.1 p.2).state else tr.dyn p
  let dynUnionE' : Finset ℕ := tr.activeComps.biUnion fun C =>
    (tr.activeBuckets C).biUnion fun b => (initCB C b).state.H.E
  let extraComps' : Finset ℕ := tr.activeComps.biUnion fun C =>
    ((tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E) \ (tr.ts C).C.E
  let targetE' : Finset ℕ := dynUnionE' ∪ extraComps' ∪ tr.cs.crossEdges
  let C_cur := coreGraph tr.cs.G tr.cs.lsf
  let S_cur' : MGraph :=
    { V := tr.cs.RF.R
      E := targetE'
      tail := C_cur.tail
      head := C_cur.head }
  let restartCost : ℕ :=
    tr.cs.G.m + 1 + tr.activeComps.sum fun C =>
      (tr.activeBuckets C).sum fun b => (initCB C b).cost
  { tr with
    dyn := dyn'
    S_cur := S_cur'
    cost := tr.cost + restartCost }

/-- Concrete `SparseCoreRestartTool` obtained by equipping `sparseCoreTool` (`SplitSpanner.lean`)
with `restartTreeCore` on branch `j`. -/
noncomputable def sparseCoreRestartTool
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) :
    SparseCoreRestartTool :=
  open Classical in
  { sparseCoreTool oracle C_lsst L sparsify with
    restart := fun st j =>
      if st.isNonempty then
        { st with trees := Function.update st.trees j (restartTreeCore L sparsify (st.trees j)) }
      else st }

lemma sparseCoreRestartTool_toSparseCoreTool
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).toSparseCoreTool =
      sparseCoreTool oracle C_lsst L sparsify :=
  rfl

lemma sparseCoreRestartTool_restart_lsfs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreState L) (j b : ℕ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).lsfs
        ((sparseCoreRestartTool oracle C_lsst L sparsify).restart st j) b =
      (sparseCoreRestartTool oracle C_lsst L sparsify).lsfs st b := by
  by_cases hne : st.isNonempty = true
  · by_cases hbj : b = j
    · subst hbj
      simp [sparseCoreRestartTool, sparseCoreTool, sparseCoreToolWith, hne, restartTreeCore]
    · simp [sparseCoreRestartTool, sparseCoreTool, sparseCoreToolWith, hne, hbj]
  · simp [sparseCoreRestartTool, sparseCoreTool, sparseCoreToolWith, hne]

lemma sparseCoreRestartTool_restart_cs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreState L) (j b : ℕ) :
    (((sparseCoreRestartTool oracle C_lsst L sparsify).restart st j).trees b).cs =
      (st.trees b).cs := by
  by_cases hne : st.isNonempty = true
  · by_cases hbj : b = j
    · subst hbj
      simp [sparseCoreRestartTool, sparseCoreTool, sparseCoreToolWith, hne, restartTreeCore]
    · simp [sparseCoreRestartTool, sparseCoreTool, sparseCoreToolWith, hne, hbj]
  · simp [sparseCoreRestartTool, sparseCoreTool, sparseCoreToolWith, hne]

lemma sparseCoreRestartTool_restart_other
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreState L) {j b : ℕ} (hbj : b ≠ j) :
    ((sparseCoreRestartTool oracle C_lsst L sparsify).restart st j).trees b = st.trees b ∧
    (sparseCoreRestartTool oracle C_lsst L sparsify).S
        ((sparseCoreRestartTool oracle C_lsst L sparsify).restart st j) b =
      (sparseCoreRestartTool oracle C_lsst L sparsify).S st b ∧
    (sparseCoreRestartTool oracle C_lsst L sparsify).emb
        ((sparseCoreRestartTool oracle C_lsst L sparsify).restart st j) b =
      (sparseCoreRestartTool oracle C_lsst L sparsify).emb st b := by
  by_cases hne : st.isNonempty = true
  · simp [sparseCoreRestartTool, sparseCoreTool, sparseCoreToolWith, hne, hbj]
  · simp [sparseCoreRestartTool, sparseCoreTool, sparseCoreToolWith, hne]

lemma sparseCoreRestartTool_cost_le_restart
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreState L) (j : ℕ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).cost st ≤
      (sparseCoreRestartTool oracle C_lsst L sparsify).cost
        ((sparseCoreRestartTool oracle C_lsst L sparsify).restart st j) := by
  by_cases hne : st.isNonempty = true
  · simp only [sparseCoreRestartTool, sparseCoreTool, sparseCoreToolWith, hne, ↓reduceIte]
    refine Finset.sum_le_sum fun b _ => ?_
    by_cases hbj : b = j
    · subst hbj
      simp [restartTreeCore]
    · simp [hbj]
  · simp [sparseCoreRestartTool, sparseCoreTool, sparseCoreToolWith, hne]

private lemma sparseCoreRestartTool_init_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).init k M N G₀ ℓ₀ g₀ =
      if G₀.V.Nonempty then
        { isNonempty := true, k := k,
          trees := fun j => initTreeCore oracle C_lsst L sparsify k M N G₀ ℓ₀ j }
      else
        { isNonempty := false, k := k,
          trees := fun j => initTreeCore oracle C_lsst L sparsify k M N G₀ ℓ₀ j } := rfl

lemma sparseCoreRestartTool_init_trees
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ) (j : ℕ) :
    (SparseCoreState.trees ((sparseCoreRestartTool oracle C_lsst L sparsify).init k M N G₀ ℓ₀ g₀) j) =
      initTreeCore oracle C_lsst L sparsify k M N G₀ ℓ₀ j := by
  rw [sparseCoreRestartTool_init_eq]
  by_cases h : G₀.V.Nonempty <;> simp [h]

lemma sparseCoreRestartTool_update_of_nonempty
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : (sparseCoreRestartTool oracle C_lsst L sparsify).State}
    (hne : SparseCoreState.isNonempty st = true) (U : List Update) (ℓ g : ℕ → ℝ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).update st U ℓ g =
      ({ isNonempty := true, k := SparseCoreState.k st,
         trees := fun j => (stepTreeCoreAuxWith true sparsify (SparseCoreState.trees st j) U).state },
       fun j => (stepTreeCoreAuxWith true sparsify (SparseCoreState.trees st j) U).U_S) := by
  dsimp only [sparseCoreRestartTool, sparseCoreTool, sparseCoreToolWith]
  simp only [hne, ↓reduceIte]

private lemma sparseCoreRestartTool_update_of_empty
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : (sparseCoreRestartTool oracle C_lsst L sparsify).State}
    (hem : SparseCoreState.isNonempty st = false) (U : List Update) (ℓ g : ℕ → ℝ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).update st U ℓ g = (st, fun _ => []) := by
  dsimp only [sparseCoreRestartTool, sparseCoreTool, sparseCoreToolWith]
  simp only [hem, Bool.false_eq_true, ↓reduceIte]

lemma sparseCoreRestartTool_restart_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreState L) (j : ℕ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).restart st j =
      if st.isNonempty = true then
        { isNonempty := st.isNonempty, k := st.k,
          trees := Function.update st.trees j (restartTreeCore L sparsify (st.trees j)) }
      else st := rfl

lemma sparseCoreRestartTool_lsfs_of_nonempty
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : (sparseCoreRestartTool oracle C_lsst L sparsify).State}
    (hne : SparseCoreState.isNonempty st = true) (j : ℕ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).lsfs st j =
      (SparseCoreState.trees st j).cs.lsf := by
  change (if SparseCoreState.isNonempty st = true then _ else _) = _
  simp only [hne, ↓reduceIte]

lemma sparseCoreRestartTool_lsfs_of_empty
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : (sparseCoreRestartTool oracle C_lsst L sparsify).State}
    (hem : SparseCoreState.isNonempty st = false) (j : ℕ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).lsfs st j = emptyLSF := by
  change (if SparseCoreState.isNonempty st = true then _ else _) = _
  simp only [hem, Bool.false_eq_true, ↓reduceIte]

lemma sparseCoreTool_lsfs_of_nonempty
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : (sparseCoreTool oracle C_lsst L sparsify).State}
    (hne : SparseCoreState.isNonempty st = true) (j : ℕ) :
    (sparseCoreTool oracle C_lsst L sparsify).lsfs st j =
      (SparseCoreState.trees st j).cs.lsf := by
  change (if SparseCoreState.isNonempty st = true then _ else _) = _
  simp only [hne, ↓reduceIte]

lemma sparseCoreTool_lsfs_of_empty
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {st : (sparseCoreTool oracle C_lsst L sparsify).State}
    (hem : SparseCoreState.isNonempty st = false) (j : ℕ) :
    (sparseCoreTool oracle C_lsst L sparsify).lsfs st j = emptyLSF := by
  change (if SparseCoreState.isNonempty st = true then _ else _) = _
  simp only [hem, Bool.false_eq_true, ↓reduceIte]

lemma sparseCoreRestartTool_S_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : (sparseCoreRestartTool oracle C_lsst L sparsify).State) (j : ℕ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).S st j =
      if SparseCoreState.isNonempty st = true then (SparseCoreState.trees st j).S_cur else emptyGraph := rfl

lemma sparseCoreRestartTool_emb_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : (sparseCoreRestartTool oracle C_lsst L sparsify).State) (j : ℕ) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).emb st j =
      if SparseCoreState.isNonempty st = true then (SparseCoreState.trees st j).emb else fun _ => [] := rfl

private lemma sparseCoreRestartTool_cost_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreState L) :
    (sparseCoreRestartTool oracle C_lsst L sparsify).cost st =
      if st.isNonempty = true then ∑ j ∈ Finset.range st.k, (st.trees j).cost else 0 := rfl

/-! ## 1. Structural invariants of `restartTreeCore` and `runAfterRestarts` -/

open MinCostFlow.LSF

/-- Equality of all restart-invariant ("base") fields between two `TreeCoreState` values. -/
structure TreeBaseFieldsEq {L : ℕ} (tr₁ tr₂ : TreeCoreState L) : Prop where
  m₀ : tr₁.m₀ = tr₂.m₀
  n₀ : tr₁.n₀ = tr₂.n₀
  Δ₀ : tr₁.Δ₀ = tr₂.Δ₀
  splitBound : tr₁.splitBound = tr₂.splitBound
  cs : tr₁.cs = tr₂.cs
  activeComps : tr₁.activeComps = tr₂.activeComps
  ts : tr₁.ts = tr₂.ts
  origBucket : tr₁.origBucket = tr₂.origBucket
  activeBuckets : tr₁.activeBuckets = tr₂.activeBuckets
  lazyInitCost : tr₁.lazyInitCost = tr₂.lazyInitCost

lemma TreeBaseFieldsEq.refl {L : ℕ} (tr : TreeCoreState L) : TreeBaseFieldsEq tr tr :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma TreeBaseFieldsEq.trans {L : ℕ} {a b c : TreeCoreState L}
    (h₁ : TreeBaseFieldsEq a b) (h₂ : TreeBaseFieldsEq b c) : TreeBaseFieldsEq a c :=
  ⟨h₁.m₀.trans h₂.m₀, h₁.n₀.trans h₂.n₀, h₁.Δ₀.trans h₂.Δ₀,
   h₁.splitBound.trans h₂.splitBound, h₁.cs.trans h₂.cs,
   h₁.activeComps.trans h₂.activeComps, h₁.ts.trans h₂.ts,
   h₁.origBucket.trans h₂.origBucket, h₁.activeBuckets.trans h₂.activeBuckets,
   h₁.lazyInitCost.trans h₂.lazyInitCost⟩

lemma restartTreeCore_base_fields {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (tr : TreeCoreState L) :
    TreeBaseFieldsEq (restartTreeCore L sparsify tr) tr :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma restartBucketGraph_restartTreeCore {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : TreeCoreState L) (C : Finset ℕ) (b : ℤ) :
    restartBucketGraph (restartTreeCore L sparsify tr) C b = restartBucketGraph tr C b :=
  rfl

lemma activeSubgraph_rawBucket_spec {C : MGraph} (hC : C.IsValid) (origB : ℕ → ℤ) (b : ℤ) :
    let Hb := activeSubgraph (rawBucket C origB b)
    Hb.IsValid ∧ C.IsSubgraph Hb ∧ Hb.E = C.E.filter (fun e => origB e = b) ∧
      Hb.n ≤ 2 * Hb.m ∧ Hb.maxDeg ≤ C.maxDeg := by
  intro Hb
  have hRaw_val : (rawBucket C origB b).IsValid := fun e he => by
    rw [rawBucket, Finset.mem_filter] at he
    exact hC e he.1
  have hAct_sub := activeSubgraph_isSubgraph (rawBucket C origB b)
  have hAct_val : Hb.IsValid := activeSubgraph_isValid hRaw_val
  have hC_sub_H : C.IsSubgraph Hb :=
    ⟨Finset.Subset.trans hAct_sub.1 Finset.Subset.rfl,
      Finset.Subset.trans hAct_sub.2.1 (Finset.filter_subset _ _),
      fun e he => hAct_sub.2.2 e he⟩
  have hE_eq : Hb.E = C.E.filter (fun e => origB e = b) := rfl
  have hRaw_deg_le : ∀ v, (rawBucket C origB b).deg v ≤ C.deg v := fun v => by
    unfold MGraph.deg
    exact Nat.add_le_add
      (Finset.card_le_card fun e he => by
        rw [Finset.mem_filter] at he ⊢
        exact ⟨(Finset.mem_filter.mp he.1).1, he.2⟩)
      (Finset.card_le_card fun e he => by
        rw [Finset.mem_filter] at he ⊢
        exact ⟨(Finset.mem_filter.mp he.1).1, he.2⟩)
  have hRaw_maxDeg : (rawBucket C origB b).maxDeg ≤ C.maxDeg := by
    unfold MGraph.maxDeg
    exact Finset.sup_le fun v hv => le_trans (hRaw_deg_le v) (Finset.le_sup (f := C.deg) hv)
  refine ⟨hAct_val, hC_sub_H, hE_eq, activeSubgraph_n_le_two_m hRaw_val,
    le_trans (activeSubgraph_maxDeg_le _) hRaw_maxDeg⟩

lemma restartTreeCore_S_cur_spec {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {tr : TreeCoreState L} {G₀ : MGraph}
    {cs_init : Finset ℕ → LSFState}
    (hG₀_eq : tr.cs.G₀ = G₀) (hI : CompLSFInv C_lsst ℓ₀ tr.cs)
    (hAct : tr.activeComps ⊆ components G₀)
    (hT : ∀ C ∈ components G₀, TildeInv (cs_init C) (tr.cs.compSt C) (tr.ts C))
    {actB : Finset ℕ → Finset ℤ} (hactB : tr.activeBuckets = actB)
    (hInit_sub : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      ((DynSpanner.init (restartBucketGraph tr C b) L
        (phaseBase ((restartBucketGraph tr C b).n + tr.splitBound) L) (sparsify tr.m₀)).state.H.E ⊆
        (restartBucketGraph tr C b).E)) :
    let tr' := restartTreeCore L sparsify tr
    tr'.S_cur.IsValid ∧ tr'.S_cur.V = tr.cs.RF.R ∧
    tr'.S_cur.E =
      (tr.activeComps.biUnion fun C => (actB C).biUnion fun b => (tr'.dyn (C, b)).H.E) ∪
        (tr.activeComps.biUnion fun C => extraSet (tr.cs.compSt C) (tr.ts C)) ∪
        tr.cs.crossEdges ∧
    (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph tr'.S_cur := by
  intro tr'
  have hRF := compLSF_RF_isRSF hI
  have hTgt_sub : tr'.S_cur.E ⊆ tr.cs.G.E \ tr.cs.RF.F.E := by
    intro e he
    change e ∈ (tr.activeComps.biUnion fun C => (tr.activeBuckets C).biUnion fun b =>
      (DynSpanner.init (restartBucketGraph tr C b) L
        (phaseBase ((restartBucketGraph tr C b).n + tr.splitBound) L)
        (sparsify tr.m₀)).state.H.E) ∪
      (tr.activeComps.biUnion fun C =>
        ((tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E) \ (tr.ts C).C.E) ∪
      tr.cs.crossEdges at he
    rcases Finset.mem_union.mp he with he12 | heX
    · rcases Finset.mem_union.mp he12 with heD | heEx
      · rw [Finset.mem_biUnion] at heD
        rcases heD with ⟨C, hCA, heB⟩
        have hC := hAct hCA
        rw [Finset.mem_biUnion] at heB
        rcases heB with ⟨b, hb, heb⟩
        have heHb := hInit_sub C hC b (hactB ▸ hb) heb
        have heC := (hT C hC).hCE_sub (Finset.filter_subset _ _ heHb)
        exact compLSF_comp_sdiff_sub hI (hG₀_eq ▸ hC) heC
      · rw [Finset.mem_biUnion] at heEx
        rcases heEx with ⟨C, hCA, heExC⟩
        exact compLSF_comp_sdiff_sub hI (hG₀_eq ▸ hAct hCA) (Finset.mem_sdiff.mp heExC).1
    · exact compLSF_crossEdges_sub hI heX
  have hVal : tr'.S_cur.IsValid := by
    intro e he
    have heG := (Finset.mem_sdiff.mp (hTgt_sub he)).1
    have hth := hI.hG_val e heG
    dsimp only [tr', restartTreeCore, coreGraph]
    exact ⟨(root_mem_R hRF hth.1).1, (root_mem_R hRF hth.2).1⟩
  have hSubC : (coreGraph tr.cs.G tr.cs.lsf).IsSubgraph tr'.S_cur := by
    refine ⟨Finset.Subset.rfl, hTgt_sub, fun _ _ => ⟨rfl, rfl⟩⟩
  refine ⟨hVal, rfl, ?_, hSubC⟩
  dsimp only [tr', restartTreeCore]
  congr 1; congr 1
  refine Finset.biUnion_congr rfl fun C hCA => ?_
  rw [hactB]
  exact Finset.biUnion_congr rfl fun b _ => by simp [hCA]

lemma foldl_restart_props
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : SparseCoreState L) (xs : List ℕ) :
    let T := sparseCoreRestartTool oracle C_lsst L sparsify
    let st' := xs.foldl T.restart st
    st'.isNonempty = st.isNonempty ∧ st'.k = st.k ∧
    T.cost st ≤ T.cost st' ∧
    (∀ j, TreeBaseFieldsEq (st'.trees j) (st.trees j)) ∧
    (∀ j, j ∉ xs → st'.trees j = st.trees j) := by
  intro T
  induction xs generalizing st with
  | nil => exact ⟨rfl, rfl, le_rfl, fun j => TreeBaseFieldsEq.refl (st.trees j), fun _ _ => rfl⟩
  | cons x xs ih =>
    intro st'
    have h1 := ih (T.restart st x)
    have hne1 : (T.restart st x).isNonempty = st.isNonempty := by
      rw [sparseCoreRestartTool_restart_eq]
      by_cases hne : st.isNonempty = true <;> simp [hne]
    have hk1 : (T.restart st x).k = st.k := by
      rw [sparseCoreRestartTool_restart_eq]
      by_cases hne : st.isNonempty = true <;> simp [hne]
    have hc1 : T.cost st ≤ T.cost (T.restart st x) :=
      sparseCoreRestartTool_cost_le_restart oracle C_lsst L sparsify st x
    have hf1 : ∀ j, TreeBaseFieldsEq ((T.restart st x).trees j) (st.trees j) := fun j => by
      rw [sparseCoreRestartTool_restart_eq]
      by_cases hne : st.isNonempty = true
      · simp only [hne, ↓reduceIte]
        by_cases hjx : j = x
        · subst hjx; simp only [Function.update_self]; exact restartTreeCore_base_fields sparsify _
        · simp only [Function.update_of_ne hjx]; exact TreeBaseFieldsEq.refl _
      · simp only [hne, Bool.false_eq_true, ↓reduceIte]; exact TreeBaseFieldsEq.refl _
    refine ⟨h1.1.trans hne1, h1.2.1.trans hk1, le_trans hc1 h1.2.2.1,
      fun j => (h1.2.2.2.1 j).trans (hf1 j), fun j hj => ?_⟩
    have hne_x : j ≠ x := fun h => hj (h ▸ List.mem_cons_self)
    have hni_xs : j ∉ xs := fun h => hj (List.mem_cons_of_mem x h)
    have htx : (T.restart st x).trees j = st.trees j := by
      rw [sparseCoreRestartTool_restart_eq]
      by_cases hne : st.isNonempty = true <;> simp [hne, Function.update_of_ne hne_x]
    exact (h1.2.2.2.2 j hni_xs).trans htx

lemma runAfterRestarts_isNonempty
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) :
    let T := sparseCoreRestartTool oracle C_lsst L sparsify
    ∀ t, (T.runAfterUpdate k M N D restarts t).1.isNonempty = decide (D.G 0).V.Nonempty ∧
      (T.runAfterRestarts k M N D restarts t).isNonempty = decide (D.G 0).V.Nonempty ∧
      (T.runAfterUpdate k M N D restarts t).1.k = k ∧
      (T.runAfterRestarts k M N D restarts t).k = k := by
  intro T t
  induction t with
  | zero =>
    have h0 : (T.runAfterUpdate k M N D restarts 0).1.isNonempty = decide (D.G 0).V.Nonempty ∧
        (T.runAfterUpdate k M N D restarts 0).1.k = k := by
      dsimp only [T, SparseCoreRestartTool.runAfterUpdate, sparseCoreRestartTool,
        sparseCoreTool, sparseCoreToolWith]
      split_ifs with hV <;> simp [hV]
    have hf := foldl_restart_props oracle C_lsst L sparsify
      (T.runAfterUpdate k M N D restarts 0).1 (restarts 0)
    exact ⟨h0.1, hf.1.trans h0.1, h0.2, hf.2.1.trans h0.2⟩
  | succ s ih =>
    have hu : (T.runAfterUpdate k M N D restarts (s + 1)).1.isNonempty =
        (T.runAfterRestarts k M N D restarts s).isNonempty ∧
        (T.runAfterUpdate k M N D restarts (s + 1)).1.k =
        (T.runAfterRestarts k M N D restarts s).k := by
      rw [T.runAfterUpdate_succ]
      dsimp only [T, sparseCoreRestartTool, sparseCoreTool, sparseCoreToolWith]
      split_ifs <;> simp
    have hpre_ne : (T.runAfterUpdate k M N D restarts (s + 1)).1.isNonempty =
        decide (D.G 0).V.Nonempty := hu.1.trans ih.2.1
    have hpre_k : (T.runAfterUpdate k M N D restarts (s + 1)).1.k = k := hu.2.trans ih.2.2.2
    have hf := foldl_restart_props oracle C_lsst L sparsify
      (T.runAfterUpdate k M N D restarts (s + 1)).1 (restarts (s + 1))
    exact ⟨hpre_ne, hf.1.trans hpre_ne, hpre_k, hf.2.1.trans hpre_k⟩

lemma runAfterRestarts_empty_case
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (hV₀ : ¬ (D.G 0).V.Nonempty) :
    let T := sparseCoreRestartTool oracle C_lsst L sparsify
    ∀ t, (T.runAfterUpdate k M N D restarts t).1.isNonempty = false ∧
      (T.runAfterRestarts k M N D restarts t).isNonempty = false ∧
      (T.runAfterUpdate k M N D restarts t).2 = (fun _ => []) := by
  intro T t
  have hne := runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts t
  have hfalse : decide (D.G 0).V.Nonempty = false := decide_eq_false hV₀
  refine ⟨hne.1.trans hfalse, hne.2.1.trans hfalse, ?_⟩
  cases t with
  | zero => rfl
  | succ s =>
    rw [T.runAfterUpdate_succ]
    have hs := (runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts s).2.1.trans hfalse
    dsimp only [T]
    rw [sparseCoreRestartTool_update_of_empty hs]

private lemma stepTreeCoreAux_congr_base {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {st₁ st₂ : TreeCoreState L} (h : TreeBaseFieldsEq st₁ st₂) (U : List Update) :
    let i₁ := stepTreeCoreAux sparsify st₁ U
    let i₂ := stepTreeCoreAux sparsify st₂ U
    TreeBaseFieldsEq i₁.state i₂.state ∧ i₁.U_C = i₂.U_C ∧ i₁.newlyActive = i₂.newlyActive := by
  intro i₁ i₂
  dsimp only [i₁, i₂, stepTreeCoreAux, stepTreeCoreAuxWith]
  rw [h.m₀, h.n₀, h.Δ₀, h.splitBound, h.cs, h.activeComps, h.ts, h.origBucket,
    h.activeBuckets, h.lazyInitCost]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

lemma runAfterRestarts_base_proj
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (hV₀ : (D.G 0).V.Nonempty) (j : ℕ) :
    let T := sparseCoreRestartTool oracle C_lsst L sparsify
    ∀ t,
      let trPre := (T.runAfterUpdate k M N D restarts t).1.trees j
      let trPost := (T.runAfterRestarts k M N D restarts t).trees j
      let trBase := (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
      TreeBaseFieldsEq trPre trBase ∧ TreeBaseFieldsEq trPost trBase := by
  intro T t
  have hne : ∀ s, (T.runAfterRestarts k M N D restarts s).isNonempty = true := fun s =>
    (runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts s).2.1.trans
      (decide_eq_true hV₀)
  induction t with
  | zero =>
    have hpre0 : (T.runAfterUpdate k M N D restarts 0).1.trees j =
        (treeRunSeq oracle C_lsst L sparsify k M N D j 0).1 := by
      dsimp only [T, SparseCoreRestartTool.runAfterUpdate, treeRunSeq, treeRunSeqWith]
      exact sparseCoreRestartTool_init_trees oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) (D.g 0) j
    have hf := (foldl_restart_props oracle C_lsst L sparsify
      (T.runAfterUpdate k M N D restarts 0).1 (restarts 0)).2.2.2.1 j
    rw [hpre0] at hf ⊢
    exact ⟨TreeBaseFieldsEq.refl _, hf⟩
  | succ s ih =>
    have hpre_eq : (T.runAfterUpdate k M N D restarts (s + 1)).1.trees j =
        (stepTreeCoreAux sparsify ((T.runAfterRestarts k M N D restarts s).trees j)
          (D.U (s + 1))).state := by
      rw [T.runAfterUpdate_succ]
      dsimp only [T]
      rw [sparseCoreRestartTool_update_of_nonempty (hne s)]
    have hcon := stepTreeCoreAux_congr_base sparsify ih.2 (D.U (s + 1))
    have hpre_p : TreeBaseFieldsEq ((T.runAfterUpdate k M N D restarts (s + 1)).1.trees j)
        (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1 := by
      rw [hpre_eq]
      exact hcon.1
    have hf := (foldl_restart_props oracle C_lsst L sparsify
      (T.runAfterUpdate k M N D restarts (s + 1)).1 (restarts (s + 1))).2.2.2.1 j
    exact ⟨hpre_p, hf.trans hpre_p⟩

/-- Last restart step `≤ t` for branch `j` (`0` if `j` never restarted on `[1, t]`). -/
def lastRestart (restarts : ℕ → List ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => if j ∈ restarts (s + 1) then s + 1 else lastRestart restarts j s

lemma lastRestart_spec (restarts : ℕ → List ℕ) (j t : ℕ) :
    lastRestart restarts j t ≤ t ∧
    (lastRestart restarts j t = 0 ∨ j ∈ restarts (lastRestart restarts j t)) ∧
    ∀ r, lastRestart restarts j t < r → r ≤ t → j ∉ restarts r := by
  induction t with
  | zero =>
    refine ⟨le_rfl, Or.inl rfl, fun r hr1 hr0 => by omega⟩
  | succ s ih =>
    dsimp only [lastRestart]
    split_ifs with hj
    · refine ⟨le_rfl, Or.inr hj, fun r hr1 hr2 => by omega⟩
    · refine ⟨Nat.le_succ_of_le ih.1, ih.2.1, fun r hr1 hr2 => ?_⟩
      by_cases hrs : r = s + 1
      · subst hrs; exact hj
      · exact ih.2.2 r hr1 (by omega)

/-- Epoch state sequence on `[s₀, t]` for branch `j` when `∀ r, s₀ < r → r < t → j ∉ restarts r`:
uses `(post (s₀ + δ)).trees j` on `0 ≤ δ` except `(pre t).trees j` at `s₀ + δ = t` (`s₀ < t`). -/
noncomputable def epochTreeSeq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (s₀ t j δ : ℕ) : TreeCoreState L :=
  let T := sparseCoreRestartTool oracle C_lsst L sparsify
  if s₀ + δ = t ∧ s₀ < t then (T.runAfterUpdate k M N D restarts t).1.trees j
  else (T.runAfterRestarts k M N D restarts (s₀ + δ)).trees j

lemma epochTreeSeq_steps
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (hV₀ : (D.G 0).V.Nonempty) (s₀ t j : ℕ) (hst : s₀ ≤ t)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let T := sparseCoreRestartTool oracle C_lsst L sparsify
    let st := epochTreeSeq oracle C_lsst L sparsify k M N D restarts s₀ t j
    (∀ δ ≤ t - s₀, TreeBaseFieldsEq (st δ) (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + δ)).1) ∧
    (∀ δ < t - s₀,
      st (δ + 1) = (stepTreeCoreAux sparsify (st δ) (D.U (s₀ + δ + 1))).state ∧
      (T.runAfterUpdate k M N D restarts (s₀ + δ + 1)).2 j =
        (stepTreeCoreAux sparsify (st δ) (D.U (s₀ + δ + 1))).U_S) := by
  intro T st
  have hne : ∀ s, (T.runAfterRestarts k M N D restarts s).isNonempty = true := fun s =>
    (runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts s).2.1.trans
      (decide_eq_true hV₀)
  refine ⟨fun δ _ => ?_, fun δ hδ => ?_⟩
  · have hb := runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j (s₀ + δ)
    dsimp only [st, epochTreeSeq]
    split_ifs with hEq
    · rw [hEq.1] at hb ⊢; exact hb.1
    · exact hb.2
  · have hδ_ne : ¬ (s₀ + δ = t ∧ s₀ < t) := by omega
    have hst_δ : st δ = (T.runAfterRestarts k M N D restarts (s₀ + δ)).trees j := by
      dsimp only [st, epochTreeSeq, T]
      simp only [hδ_ne, ↓reduceIte]
    have hpre_s1 : (T.runAfterUpdate k M N D restarts (s₀ + δ + 1)).1.trees j =
        (stepTreeCoreAux sparsify (st δ) (D.U (s₀ + δ + 1))).state ∧
        (T.runAfterUpdate k M N D restarts (s₀ + δ + 1)).2 j =
        (stepTreeCoreAux sparsify (st δ) (D.U (s₀ + δ + 1))).U_S := by
      rw [T.runAfterUpdate_succ]
      dsimp only [T] at hst_δ ⊢
      rw [sparseCoreRestartTool_update_of_nonempty (hne (s₀ + δ))]
      dsimp only
      rw [← hst_δ]
      exact ⟨rfl, rfl⟩
    rw [Nat.add_assoc] at hpre_s1
    refine ⟨?_, hpre_s1.2⟩
    dsimp only [T] at hpre_s1 ⊢
    by_cases ht_eq : s₀ + (δ + 1) = t
    · have hlt : s₀ < t := by omega
      have h1 : st (δ + 1) = ((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate
          k M N D restarts t).1.trees j := by
        dsimp only [st, epochTreeSeq, T]
        simp only [ht_eq, hlt, and_self, ↓reduceIte]
      rw [h1, show ((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts t).1.trees j =
          ((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts
            (s₀ + (δ + 1))).1.trees j by rw [ht_eq], hpre_s1.1, Nat.add_assoc]
    · have hnot : ¬ (s₀ + (δ + 1) = t ∧ s₀ < t) := fun h => ht_eq h.1
      have hni : j ∉ restarts (s₀ + (δ + 1)) := hNoRest (s₀ + (δ + 1)) (by omega) (by omega)
      have h1 : st (δ + 1) = ((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterRestarts
          k M N D restarts (s₀ + (δ + 1))).trees j := by
        dsimp only [st, epochTreeSeq, T]
        simp only [hnot, ↓reduceIte]
      have hf := (foldl_restart_props oracle C_lsst L sparsify
        ((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterUpdate k M N D restarts
          (s₀ + (δ + 1))).1 (restarts (s₀ + (δ + 1)))).2.2.2.2 j hni
      rw [h1]
      change ((sparseCoreRestartTool oracle C_lsst L sparsify).runAfterRestarts k M N D restarts
        (s₀ + (δ + 1))).trees j = _
      unfold SparseCoreRestartTool.runAfterRestarts
      rw [hf, hpre_s1.1, Nat.add_assoc]

lemma foldl_restart_dyn_inactive
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (xs : List ℕ) (st : SparseCoreState L) (j : ℕ) {C : Finset ℕ} {b : ℤ}
    (hna : C ∉ (st.trees j).activeComps) :
    (((xs.foldl (sparseCoreRestartTool oracle C_lsst L sparsify).restart st).trees j).dyn (C, b)) =
      (st.trees j).dyn (C, b) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
    have hx_act : C ∉ (((sparseCoreRestartTool oracle C_lsst L sparsify).restart st x).trees j).activeComps := by
      rw [sparseCoreRestartTool_restart_eq]
      split_ifs with hne
      · dsimp only
        by_cases hjx : j = x
        · subst hjx
          rw [Function.update_self, (restartTreeCore_base_fields sparsify _).activeComps]
          exact hna
        · rw [Function.update_of_ne hjx]; exact hna
      · exact hna
    have hx_dyn : (((sparseCoreRestartTool oracle C_lsst L sparsify).restart st x).trees j).dyn (C, b) =
        (st.trees j).dyn (C, b) := by
      rw [sparseCoreRestartTool_restart_eq]
      split_ifs with hne
      · dsimp only
        by_cases hjx : j = x
        · subst hjx
          rw [Function.update_self]
          dsimp only [restartTreeCore]
          simp [hna]
        · rw [Function.update_of_ne hjx]
      · rfl
    exact (ih ((sparseCoreRestartTool oracle C_lsst L sparsify).restart st x) hx_act).trans hx_dyn

lemma foldl_restart_dyn_active
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (xs : List ℕ) (st : SparseCoreState L) (j : ℕ) {C : Finset ℕ} {b : ℤ}
    (hne : st.isNonempty = true) (hact : C ∈ (st.trees j).activeComps) (hj : j ∈ xs) :
    let st' := xs.foldl (sparseCoreRestartTool oracle C_lsst L sparsify).restart st
    restartBucketGraph (st'.trees j) C b = restartBucketGraph (st.trees j) C b ∧
    (st'.trees j).dyn (C, b) = (DynSpanner.init (restartBucketGraph (st.trees j) C b) L
      (phaseBase ((restartBucketGraph (st.trees j) C b).n + (st.trees j).splitBound) L)
      (sparsify (st.trees j).m₀)).state := by
  induction xs generalizing st with
  | nil => cases hj
  | cons x xs ih =>
    have hx_ne : ((sparseCoreRestartTool oracle C_lsst L sparsify).restart st x).isNonempty = true := by
      rw [sparseCoreRestartTool_restart_eq]
      simp only [hne, ↓reduceIte]
    have hf1 := (foldl_restart_props oracle C_lsst L sparsify st [x]).2.2.2.1 j
    dsimp only [List.foldl] at hf1
    have hx_act : C ∈ (((sparseCoreRestartTool oracle C_lsst L sparsify).restart st x).trees j).activeComps := by
      rw [hf1.activeComps]; exact hact
    have hx_rb : restartBucketGraph
        (((sparseCoreRestartTool oracle C_lsst L sparsify).restart st x).trees j) C b =
        restartBucketGraph (st.trees j) C b := by
      dsimp only [restartBucketGraph]
      rw [hf1.ts, hf1.origBucket]
    have hx_spB : (((sparseCoreRestartTool oracle C_lsst L sparsify).restart st x).trees j).splitBound =
        (st.trees j).splitBound := hf1.splitBound
    have hx_m0 : (((sparseCoreRestartTool oracle C_lsst L sparsify).restart st x).trees j).m₀ =
        (st.trees j).m₀ := hf1.m₀
    by_cases hmem : j ∈ xs
    · have h1 := ih ((sparseCoreRestartTool oracle C_lsst L sparsify).restart st x) hx_ne hx_act hmem
      dsimp only at h1 ⊢
      rw [hx_rb, hx_spB, hx_m0] at h1
      exact h1
    · have hjx : j = x := (List.mem_cons.mp hj).resolve_right hmem
      subst hjx
      have hni := (foldl_restart_props oracle C_lsst L sparsify
        ((sparseCoreRestartTool oracle C_lsst L sparsify).restart st j) xs).2.2.2.2 j hmem
      dsimp only [List.foldl] at hni ⊢
      rw [hni]
      refine ⟨hx_rb, ?_⟩
      rw [sparseCoreRestartTool_restart_eq]
      simp only [hne, ↓reduceIte, Function.update_self]
      dsimp only [restartTreeCore]
      simp [hact]

lemma runBatchState_take_eq {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (Us : List (List Update)) :
    ∀ k d, k ≤ d →
      DynSpanner.runBatchState (L := L) G₀ q sparsify Us k =
        DynSpanner.runBatchState (L := L) G₀ q sparsify (Us.take d) k := by
  intro k d hkd
  induction k with
  | zero => rfl
  | succ m ih =>
    have hm_lt : m < d := hkd
    have ih' := ih (Nat.le_of_lt hm_lt)
    dsimp only [DynSpanner.runBatchState]
    rw [List.getElem?_take_of_lt hm_lt, ← ih']

private lemma runBatchStepOut_take_eq {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (Us : List (List Update)) {k d : ℕ} (hkd : k < d) :
    DynSpanner.runBatchStepOut (L := L) G₀ q sparsify Us k =
      DynSpanner.runBatchStepOut (L := L) G₀ q sparsify (Us.take d) k := by
  dsimp only [DynSpanner.runBatchStepOut]
  rw [List.getElem?_take_of_lt hkd, ← runBatchState_take_eq G₀ q sparsify Us k d (Nat.le_of_lt hkd)]

lemma initLSF_cov0
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    {k j : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} {ℓ₀ : ℕ → ℝ}
    (hG₀ : G₀.IsValid) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) {C : Finset ℕ} (hC : C ∈ components G₀)
    (hLSST : HasLSSTSpec oracle C_lsst) :
    let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
    (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) = (cs₀.compSt C).RF.F.E :=
  (initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC).2.2

/-- On every edge of the initial component tilde graph, `safeLen G₀ ℓ₀` agrees with `ℓ₀`,
so the bucket computed from `safeLen G₀ ℓ₀` equals the bucket computed from `ℓ₀`. -/
lemma initCompLSF_safeLen_origBucket_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    {k j : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} {ℓ₀ : ℕ → ℝ}
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    {C : Finset ℕ} (hC : C ∈ components G₀)
    (hLSST : HasLSSTSpec oracle C_lsst)
    {e : ℕ} (he : e ∈ (initTildeState ((initCompLSF oracle C_lsst G₀ ℓ₀ k j).compSt C)).C.E) :
    bucketOf (coreLen (initCompLSF oracle C_lsst G₀ ℓ₀ k j).lsf (safeLen G₀ ℓ₀) e) =
      bucketOf (coreLen (initCompLSF oracle C_lsst G₀ ℓ₀ k j).lsf ℓ₀ e) := by
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hT₀ := initTildeState_inv (hI₀.hCompLSF C hC).1
    (initLSF_cov0 oracle C_lsst hk hG₀ hℓ₀ hC hLSST)
  have heG₀ : e ∈ G₀.E :=
    (Finset.mem_sdiff.mp (compLSF_comp_sdiff_sub hI₀ hC (hT₀.hCE_sub he))).1
  simp [coreLen, safeLen, heG₀]

/-- Filtering any subset of the initial tilde edge set by `safeLen`-masked `origBucket`
coincides with filtering by unmasked `origBucket`. -/
lemma origBucket_filter_safe_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    {k j : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} {ℓ₀ : ℕ → ℝ}
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    {C : Finset ℕ} (hC : C ∈ components G₀)
    (hLSST : HasLSSTSpec oracle C_lsst)
    {E : Finset ℕ}
    (hE : E ⊆ (initTildeState ((initCompLSF oracle C_lsst G₀ ℓ₀ k j).compSt C)).C.E)
    {ob : ℕ → ℤ}
    (hob : ob = fun e => bucketOf (coreLen (initCompLSF oracle C_lsst G₀ ℓ₀ k j).lsf
      (safeLen G₀ ℓ₀) e))
    (b : ℤ) :
    E.filter (fun e => ob e = b) =
      E.filter (fun e => bucketOf (coreLen (initCompLSF oracle C_lsst G₀ ℓ₀ k j).lsf ℓ₀ e) = b) :=
  Finset.filter_congr fun e he => by
    rw [hob]; dsimp only
    rw [initCompLSF_safeLen_origBucket_eq oracle C_lsst hk hG₀ hV₀ hℓ₀ hC hLSST (hE he)]


end MinCostFlow.Chain
