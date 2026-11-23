module

public import MinCostFlow.SparseCore.BundleCompStep
public import MinCostFlow.SparseCore.SplitSpannerBuildUS
public import MinCostFlow.SparseCore.CanonCoreDefs

/-!
# The output batch of the sparse core follows the ordered core batch

A level passes its output graph to the next level together with an order of ends at each vertex,
the forest tours restricted to the output edges. For this
order to change by ordered updates, every vertex split of the output must be a split of the core
graph with its moved ends restricted to the output edges. The old output batch `buildUSReinsert`
splits each new root off its parent root in an arbitrary order, which need not move an arc.

This file defines the output batch that follows the ordered core batch instead. A batch of the
component-wise LSF changes the global core graph by an ordered core batch, with one split per new
root and at most one deletion per update (`orderedCore_compLSFBatch`). `coreBatchOf` is the
canonical such batch, `canonCoreBatch`, which depends only on the state and the input batch. `buildUSOrd` deletes the output edges that do
not stay, then applies the splits of that core batch restricted to the kept edges, then inserts
the new output edges. Only the definitions are here.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Bundle MinCostFlow.DynSpanner

/-- What the chosen core batch must satisfy: it is an ordered core batch with split bound two
between the core rotations before and after the batch, for the rotations with the given orders, it
has one split per new root, at most one deletion per update, and every edge it deletes is deleted by
the input batch `U`. -/
def CoreBatchSpec (cs : CompLSFState) (ord ord' : ℕ → List End) (U UC : List Update) : Prop :=
  (∀ (ρ : Rotation cs.G) (σ : Rotation (compLSFBatch cs U).G) (hG : cs.G.IsValid)
      (hF : cs.RF.IsRootedSpanningForestOf cs.G) (hG' : (compLSFBatch cs U).G.IsValid)
      (hF' : (compLSFBatch cs U).RF.IsRootedSpanningForestOf (compLSFBatch cs U).G),
      ρ.order = ord → σ.order = ord' →
      OrderedCoreBatch 2 (coreRotation (L := cs.lsf) ρ hG hF)
        (coreRotation (L := (compLSFBatch cs U).lsf) σ hG' hF') UC) ∧
  batchSplitCount UC = ((compLSFBatch cs U).RF.R \ cs.RF.R).card ∧
  UC.countP deleteTag ≤ U.length ∧
  batchDeletes UC ⊆ batchDeletes U

/-- The core batch of one step: the canonical core batch `canonCoreBatch` of the batch. It does
not depend on the orders, which only enter its specification `CoreBatchSpec`. -/
noncomputable def coreBatchOf (cs : CompLSFState) (_ord _ord' : ℕ → List End)
    (U : List Update) : List Update :=
  canonCoreBatch cs U

theorem coreBatchOf_eq (cs : CompLSFState) (ord ord' : ℕ → List End) (U : List Update) :
    coreBatchOf cs ord ord' U = canonCoreBatch cs U := rfl

/-- The splits of a core batch with their moved edges restricted to `keep`, in batch order. -/
def restrictSplits (keep : Finset ℕ) : List Update → List Update
  | [] => []
  | .split v v' St Sh :: UC => .split v v' (St ∩ keep) (Sh ∩ keep) :: restrictSplits keep UC
  | _ :: UC => restrictSplits keep UC

/-- The output batch that follows the core batch `UC`: delete the edges of `S_prev` that do not
stay, apply the splits of `UC` restricted to the kept edges, and insert the new edges of
`targetE` at the roots of their endpoints. The kept edges are those of `S_prev` in `targetE` that
the input batch does not delete and that are not re-embedded (`D_reins`, paper page 24, line 425
of the source). It has the same deletions and insertions as `buildUSReinsert`. -/
noncomputable def buildUSOrd (UC : List Update) (U : List Update) (cs_new : CompLSFState)
    (S_prev : MGraph) (targetE D_reins : Finset ℕ) : List Update :=
  let keepSet := ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins
  let delList := ((S_prev.E \ keepSet).sort (· ≤ ·)).map Update.delete
  let insList := ((targetE \ keepSet).sort (· ≤ ·)).map fun e =>
    Update.insert e (cs_new.RF.root (cs_new.G.tail e)) (cs_new.RF.root (cs_new.G.head e))
  delList ++ restrictSplits keepSet UC ++ insList

end MinCostFlow.SparseCore
