module

public import MinCostFlow.MinRatio.WireReembKFRBL
import Mathlib.Tactic

/-!
# The re-embedded list of the sparse-core program at one level (`WireReembModel`)

Op `0` of the sparse core under `sparseCoreOrdMachineContractKFRBL` writes, for every branch `j`,
the list `reemb a.st U ord' j` (`WireReembKFRBL.lean`). For the program of the sparse core the
list is `bundleToolReemb (stepBundleTree_reembList sp)`: on a nonempty state it is the list
`stepBundleTree_reembList` for the step of branch `j` (`SparseCore/BundleTreeCore.lean`). Here
`sp = fun _ => canonicalSparsify impl` is the sparsifier of the tool `sparseCoreProgTool`.

The select heap asks two things of this list at a level `i` that the update does not rebuild
(`WireSelectUpdate.lean`): `ReembCovers` (every surviving candidate whose embedding changed is in
the list) and `ReembCostBound` (the length, amortized with a potential of the tool state, is at
most a constant times the growth of the tool cost plus one). This file proves the coverage and the
bound for one branch. `WireReembPot.lean` gives `ReembCostBound` with the potential
`Σ_j (machCost_j - cost_j)`.

* `progTool_updateOrd_of_nonempty`, `progTool_emb_of_nonempty`, `progTool_S_of_nonempty`: the
  tool on a nonempty state, branch by branch.
* `BranchReembFacts`: the five facts of one branch step that the coverage lemma
  `mem_stepBundleTree_reembList_of_emb_ne` asks for one edge.
* `progReemb_mem_of_emb_ne`: on the tool, an edge off the new sparsified core whose embedding
  changed is in the list of its branch.
* `reembCovers_of_progTool`: `ReembCovers` at a level of a chain, from these facts at every edge
  that is a candidate before and after the step.
* `progReemb_length_le_cost`: the length of the list is at most the growth of the model cost
  `cost` of the branch (from `stepBundleTree_reembList_length_le_cost`).
* `progReemb_amortized`: if the model cost of the branch is at most its machine cost before and
  after the step, then the list is paid by the growth of the tool cost `T.cost` (the machine cost)
  with the potential `machCost - cost` of the branch.

**A bound per step against the tool cost does not follow, so `ReembCostBound` is amortized.**
The tool cost of the solver is the machine cost (`T.cost st` is the sum of `machCost` over the branches). The
machine cost of a step charges the bucket spanners with the amortized charge
`spanBatchChargeWith`, which is a rate times the encoding of the bundle batch. The list of a step
holds every edge that a bucket spanner re-embeds (`DynSpanner.updateReembSet`), and a step of the
dynamic spanner at a full rebuild (`chooseLevel L q (t + 1) = 0`) re-embeds every edge of its graph
(`DynSpanner.stepReembSet`). So the list of one step can hold all edges of a bundle graph while the
machine cost of the step grows by the charge of a batch of a few updates. The bound holds against
the model cost `cost` (`progReemb_length_le_cost`), and, with the potential `machCost - cost`,
against the machine cost (`progReemb_amortized`), once the model cost is at most the machine cost
on every reached state (`BranchCostLeMach`). That last fact is a statement of the model of the
sparse core (Theorem 8.2 bounds the cost of a bucket spanner over an epoch by the sum of its
charges, `Theorem82Clauses`), not of the contract.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

/-- The re-embedded list of the sparse-core program: the list `stepBundleTree_reembList` for the
step of each branch, with the sparsifier `canonicalSparsify impl` of `sparseCoreProgTool`. -/
noncomputable abbrev progReemb (lsfInit : LSFInit) (C_lsst : ℝ) (depth : ℕ)
    (impl : SparsifyImpl) : ToolReembFn (sparseCoreProgTool lsfInit C_lsst depth impl) :=
  bundleToolReemb (stepBundleTree_reembList (L := depth) (fun _ => canonicalSparsify impl))

section Tool

variable {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}

/-- On a nonempty state the update of the tool steps every branch by `stepBundleTree` and keeps
the new order. -/
theorem progTool_updateOrd_of_nonempty (st : SparseCoreBundleState depth)
    (hne : st.isNonempty = true) (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) :
    ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1 =
      { st with ord := ord', trees := fun j =>
          (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees j) U st.ord ord').state } := by
  change (updateBundleCore (fun _ => canonicalSparsify impl) st U ord').1 = _
  rw [updateBundleCore_of_nonempty hne]

/-- On a nonempty state the embedding of branch `j` is the embedding of its tree. -/
theorem progTool_emb_of_nonempty (st : SparseCoreBundleState depth)
    (hne : st.isNonempty = true) (j : ℕ) :
    (sparseCoreProgTool lsfInit C_lsst depth impl).emb st j = (st.trees j).emb := by
  change (if st.isNonempty then (st.trees j).emb else fun _ => []) = _
  simp [hne]

/-- On a nonempty state the sparsified core of branch `j` is `S_cur` of its tree. -/
theorem progTool_S_of_nonempty (st : SparseCoreBundleState depth)
    (hne : st.isNonempty = true) (j : ℕ) :
    (sparseCoreProgTool lsfInit C_lsst depth impl).S st j = (st.trees j).S_cur := by
  change (if st.isNonempty then (st.trees j).S_cur else emptyGraph) = _
  simp [hne]

/-- On a nonempty state the tool cost is the sum of the machine costs of the branches. -/
theorem progTool_cost_of_nonempty (st : SparseCoreBundleState depth)
    (hne : st.isNonempty = true) :
    (sparseCoreProgTool lsfInit C_lsst depth impl).cost st =
      (Finset.range st.k).sum fun j => (st.trees j).machCost := by
  change (if st.isNonempty then (Finset.range st.k).sum fun j => (st.trees j).machCost else 0) = _
  simp [hne]

/-- On a nonempty state the list of branch `j` is the list `stepBundleTree_reembList` for its
step. -/
theorem progReemb_of_nonempty (st : SparseCoreBundleState depth)
    (hne : st.isNonempty = true) (U : List Update) (ord' : ℕ → List End) (j : ℕ) :
    progReemb lsfInit C_lsst depth impl st U ord' j =
      stepBundleTree_reembList (fun _ => canonicalSparsify impl) (st.trees j) U st.ord ord' := by
  change (if st.isNonempty then _ else []) = _
  simp [hne]

end Tool

/-! ## Coverage -/

/-- The five facts about the step of one branch that `mem_stepBundleTree_reembList_of_emb_ne`
asks for an edge `e`:
1. the bundles only lose edges;
2. an active bundle that holds `e` before the step holds it after;
3. at most one active bundle holds `e`;
4. after the step, the graph of the bucket spanner of an active bundle has the edges of the bundle;
5. if the spanner of an active bundle changes the path of `e`, then `e` is in the set of edges it
   re-embeds. -/
def BranchReembFacts {L : ℕ} (sp : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) (e : ℕ) : Prop :=
  let info := stepBundleTree sp tr U ord ord'
  (∀ p : Finset ℕ × ℤ, (info.state.bun p).edges ⊆ (tr.bun p).edges) ∧
  (∀ p : Finset ℕ × ℤ, p.1 ∈ tr.activeComps → p.2 ∈ tr.activeBuckets p.1 →
    e ∈ (tr.bun p).edges → e ∈ (info.state.bun p).edges) ∧
  (∀ p₁ p₂ : Finset ℕ × ℤ,
    p₁.1 ∈ tr.activeComps → p₁.2 ∈ tr.activeBuckets p₁.1 →
    p₂.1 ∈ tr.activeComps → p₂.2 ∈ tr.activeBuckets p₂.1 →
    e ∈ (tr.bun p₁).edges → e ∈ (tr.bun p₂).edges → p₁ = p₂) ∧
  (∀ p : Finset ℕ × ℤ, p.1 ∈ tr.activeComps → p.2 ∈ tr.activeBuckets p.1 →
    (info.stepOut p).state.G.E = (info.state.bun p).edges) ∧
  (∀ p : Finset ℕ × ℤ, p.1 ∈ tr.activeComps → p.2 ∈ tr.activeBuckets p.1 →
    e ∈ (info.stepOut p).state.G.E →
    DynSpanner.piTotal (info.stepOut p).state e ≠ DynSpanner.piTotal (tr.dyn p) e →
    e ∈ DynSpanner.updateReembSet (tr.dyn p) (info.U_B p) (sp tr.m₀))

section Tool

variable {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}

/-- **Coverage on the tool.** Let `st'` be the state after an update of a nonempty state `st`. An
edge `e` outside the new sparsified core of branch `j` whose embedding in branch `j` changed is in
the list of branch `j`, given `BranchReembFacts` of the step of branch `j` at `e`. -/
theorem progReemb_mem_of_emb_ne (st : SparseCoreBundleState depth)
    (hne : st.isNonempty = true) (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End)
    (j e : ℕ)
    (hOff' : e ∉ ((sparseCoreProgTool lsfInit C_lsst depth impl).S
      ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1 j).E)
    (hNe : (sparseCoreProgTool lsfInit C_lsst depth impl).emb
        ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1 j e ≠
      (sparseCoreProgTool lsfInit C_lsst depth impl).emb st j e)
    (hF : BranchReembFacts (fun _ => canonicalSparsify impl) (st.trees j) U st.ord ord' e) :
    e ∈ progReemb lsfInit C_lsst depth impl st U ord' j := by
  have hup := progTool_updateOrd_of_nonempty (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) st hne U ℓ g
    ord'
  have hne' : ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1.isNonempty
      = true := by
    rw [hup]; exact hne
  rw [progTool_S_of_nonempty _ hne', hup] at hOff'
  rw [progTool_emb_of_nonempty _ hne', progTool_emb_of_nonempty _ hne, hup] at hNe
  rw [progReemb_of_nonempty st hne]
  obtain ⟨hBunSub, hSurv, hDisj, hDynG, hDynCov⟩ := hF
  exact mem_stepBundleTree_reembList_of_emb_ne _ _ U st.ord ord' hOff' hNe hBunSub hSurv hDisj
    hDynG hDynCov

/-- **`ReembCovers` at a level.** Let `C` and `C'` be the chains before and after an update that
does not rebuild level `i`: the level keeps its active branch `b`, its tool state goes from `st` to
the update `st'` of `st`, and its sparsified cores and embeddings are those of the tool. Then the
list of branch `b` covers level `i`, given `BranchReembFacts` at every edge that is a candidate of
level `i` before and after the step. -/
theorem reembCovers_of_progTool {C C' : TreeChain} {i : ℕ} (hi : i < C.d) (hi' : i < C'.d)
    (hbran : C'.bran i = C.bran i)
    (st : SparseCoreBundleState depth) (hne : st.isNonempty = true) (U : List Update)
    (ℓ g : ℕ → ℝ) (ord' : ℕ → List End)
    (hS' : C'.S i = (sparseCoreProgTool lsfInit C_lsst depth impl).S
      ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1)
    (hemb : C.emb i = (sparseCoreProgTool lsfInit C_lsst depth impl).emb st)
    (hemb' : C'.emb i = (sparseCoreProgTool lsfInit C_lsst depth impl).emb
      ((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1)
    (hF : ∀ e, e ∈ (C.activeCore i).E \ (C.activeS i).E →
      e ∈ (C'.activeCore i).E \ (C'.activeS i).E →
      BranchReembFacts (fun _ => canonicalSparsify impl) (st.trees (C.bran i)) U st.ord ord' e) :
    ReembCovers C C' i (progReemb lsfInit C_lsst depth impl st U ord' (C.bran i)) := by
  intro e he he' hNe
  have hS'i : C'.activeS i = C'.S i (C'.bran i) := by simp [TreeChain.activeS, hi']
  have hembi : C.activeEmb i = C.emb i (C.bran i) := by simp [TreeChain.activeEmb, hi]
  have hembi' : C'.activeEmb i = C'.emb i (C'.bran i) := by simp [TreeChain.activeEmb, hi']
  have hOff' : e ∉ (C'.activeS i).E := (Finset.mem_sdiff.mp he').2
  rw [hS'i, hS', hbran] at hOff'
  rw [hembi, hembi', hemb, hemb', hbran] at hNe
  exact progReemb_mem_of_emb_ne st hne U ℓ g ord' (C.bran i) e hOff' hNe (hF e he he')

/-! ## Length -/

/-- The lazy-initialization fact of `stepBundleTree_reembList_length_le_cost`: the lazy cost of
every component that the step activates covers the edges of its bundles. -/
def BranchLazyCovers {L : ℕ} (sp : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) : Prop :=
  ∀ C ∈ (stepBundleTree sp tr U ord ord').newlyActive,
    ((tr.activeBuckets C).sum fun b => (tr.bun (C, b)).edges.card) ≤ tr.lazyInitCost C

/-- **The length against the model cost.** The list of branch `j` is at most the growth of the
model cost `cost` of the tree of branch `j` in the step. -/
theorem progReemb_length_le_cost (st : SparseCoreBundleState depth)
    (hne : st.isNonempty = true) (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) (j : ℕ)
    (hLazy : BranchLazyCovers (fun _ => canonicalSparsify impl) (st.trees j) U st.ord ord') :
    (st.trees j).cost + (progReemb lsfInit C_lsst depth impl st U ord' j).length ≤
      (((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1.trees j).cost := by
  rw [progTool_updateOrd_of_nonempty st hne, progReemb_of_nonempty st hne]
  exact stepBundleTree_reembList_length_le_cost _ _ U st.ord ord' hLazy

/-- The model cost of a branch is at most its machine cost. This is the model fact that the
amortized bound `progReemb_amortized` needs on the reached states of the sparse core. -/
def BranchCostLeMach {L : ℕ} (tr : BundleTreeState L) : Prop := tr.cost ≤ tr.machCost

/-- In a step of the tool, the tool cost grows by at least the growth of the machine cost of any
one branch `j < k`: the machine cost of every branch only grows (`stepBundleTree_machCost`). -/
theorem progTool_cost_growth_ge (st : SparseCoreBundleState depth)
    (hne : st.isNonempty = true) (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) {j : ℕ}
    (hj : j < st.k) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let st' := (T.updateOrd st U ℓ g ord').1
    T.cost st + (st'.trees j).machCost ≤ T.cost st' + (st.trees j).machCost := by
  intro T st'
  have hup := progTool_updateOrd_of_nonempty (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) st hne U ℓ g
    ord'
  have hne' : st'.isNonempty = true := by
    change ((T.updateOrd st U ℓ g ord').1).isNonempty = true
    rw [hup]; exact hne
  have hk' : st'.k = st.k := by
    change ((T.updateOrd st U ℓ g ord').1).k = st.k
    rw [hup]
  have htr' : ∀ i, st'.trees i =
      (stepBundleTree (fun _ => canonicalSparsify impl) (st.trees i) U st.ord ord').state := by
    intro i
    change ((T.updateOrd st U ℓ g ord').1).trees i = _
    rw [hup]
  have hmono : ∀ i, (st.trees i).machCost ≤ (st'.trees i).machCost := by
    intro i
    rw [htr' i, stepBundleTree_machCost]
    exact Nat.le_add_right _ _
  rw [progTool_cost_of_nonempty st hne, progTool_cost_of_nonempty st' hne', hk']
  have hjmem : j ∈ Finset.range st.k := Finset.mem_range.mpr hj
  rw [← Finset.add_sum_erase _ _ hjmem, ← Finset.add_sum_erase _ _ hjmem]
  have hrest : ((Finset.range st.k).erase j).sum (fun i => (st.trees i).machCost) ≤
      ((Finset.range st.k).erase j).sum (fun i => (st'.trees i).machCost) :=
    Finset.sum_le_sum fun i _ => hmono i
  omega

/-- **The length against the machine cost, amortized.** If the model cost of branch `j` is at most
its machine cost before and after the step (`BranchCostLeMach`), then the list of branch `j` and
the new potential `machCost - cost` of the branch are paid by the growth of the tool cost and the
old potential. -/
theorem progReemb_amortized (st : SparseCoreBundleState depth)
    (hne : st.isNonempty = true) (U : List Update) (ℓ g : ℕ → ℝ) (ord' : ℕ → List End) {j : ℕ}
    (hj : j < st.k)
    (hLazy : BranchLazyCovers (fun _ => canonicalSparsify impl) (st.trees j) U st.ord ord')
    (hle : BranchCostLeMach (st.trees j))
    (hle' : BranchCostLeMach
      (((sparseCoreProgTool lsfInit C_lsst depth impl).updateOrd st U ℓ g ord').1.trees j)) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let st' := (T.updateOrd st U ℓ g ord').1
    (progReemb lsfInit C_lsst depth impl st U ord' j).length +
        ((st'.trees j).machCost - (st'.trees j).cost) ≤
      (T.cost st' - T.cost st) + ((st.trees j).machCost - (st.trees j).cost) := by
  intro T st'
  have hlen := progReemb_length_le_cost (lsfInit := lsfInit) (C_lsst := C_lsst) st hne U ℓ g
    ord' j hLazy
  have hgrow := progTool_cost_growth_ge (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) st hne U ℓ g
    ord' hj
  unfold BranchCostLeMach at hle hle'
  change (st.trees j).cost + _ ≤ (st'.trees j).cost at hlen
  change T.cost st + (st'.trees j).machCost ≤ T.cost st' + (st.trees j).machCost at hgrow
  change (st'.trees j).cost ≤ (st'.trees j).machCost at hle'
  omega

end Tool

end MinCostFlow.MinRatio
