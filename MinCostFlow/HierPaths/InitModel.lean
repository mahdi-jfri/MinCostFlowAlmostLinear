module

public import MinCostFlow.HierPaths.InitModelCount
public import MinCostFlow.Spanner.PathDSContract

/-!
# The `Init` model: the initial state

After the static construction (a `HierData` with its `Bounds`), `Init`
flattens the connectors and builds the arrays (`staticArrays`, `HierPaths/IndexStatic.lean`).
Its dynamic state starts as `DelState.init`: nothing failed, nothing deleted, all cursors at the
start. This file proves the facts the data structure needs right after `Init`:

* `initModel_delInv`: the invariant of `Delete` holds (`delInv_init`);
* `initModel_prunedSet`: the pruned set is empty, since every vertex owns a terminal (each vertex
  has positive degree and owns at least its degree in terminals, as `lemma_2` gives);
* `initModel_valid`: the abstract state with `Vhat = ∅` and `deleted = ∅` is `Valid` for any
  parameters, in particular for `hierParams`, under the precondition of `Init`.

The operation count of this part of `Init` is in `HierPaths/InitModelCost.lean`.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner HierData

variable {x b : ℕ} {H : HierData}

/-- The surviving terminals of the initial state are all terminals. -/
theorem surv_init (A : StaticArrays) : A.surv DelState.init = Finset.range A.C.numTerm := by
  simp [StaticArrays.surv, DelState.init, LossState.init]

/-- **The invariant of `Delete` holds after `Init`.** -/
theorem initModel_delInv {G : Graph} {owner : ℕ → ℕ} {label : ℕ → Option ℕ} {ξ κ : ℕ}
    (hA : (staticArrays H x b owner label).Spec G ξ κ) :
    (staticArrays H x b owner label).DelInv G DelState.init :=
  StaticArrays.delInv_init _ hA

/-- **The pruned set is empty after `Init`**, when every vertex of `G` has positive degree and
owns at least its degree in terminals. -/
theorem initModel_prunedSet {G : Graph} {owner : ℕ → ℕ} {label : ℕ → Option ℕ}
    (hdeg : ∀ v, G.deg v ≤ ((Finset.range (2 ^ x)).filter fun p => owner p = v).card)
    (hpos : ∀ w < G.n, 1 ≤ G.deg w) :
    (staticArrays H x b owner label).C.prunedSet G
      ((staticArrays H x b owner label).surv DelState.init) = ∅ := by
  rw [surv_init]
  exact ConnectorSystem.prunedSet_initial _ (connSystem_owner_surj hdeg hpos)

/-- **The initial abstract state is valid.** Under the precondition of `Init`, the abstract state
with no pruned vertex and no deleted edge satisfies `PathDSAbsState.Valid p` for any parameters
`p`, in particular for `hierParams`. -/
theorem initModel_valid (p : PathDSParams) {phiNum phiDen M : ℕ} {G : Graph}
    (h1 : 1 ≤ phiNum) (h2 : phiNum ≤ phiDen) (hG : G.IsValid) (hm : 1 ≤ G.m) (hmM : G.m ≤ M)
    (hpos : ∀ v < G.n, 1 ≤ G.deg v)
    (hcond : G.IsConductanceExpanderOn G.verts ((phiNum : ℝ) / (phiDen : ℝ))) :
    PathDSAbsState.Valid p ⟨phiNum, phiDen, M, G, ∅, ∅⟩ := by
  refine ⟨h1, h2, hG, hm, hmM, hpos, hcond, Finset.empty_subset _, Finset.empty_subset _, ?_⟩
  have hvol : G.vol ∅ = 0 := by simp [Graph.vol, Graph.volIn]
  simp [hvol]

end MinCostFlow.HierPaths
