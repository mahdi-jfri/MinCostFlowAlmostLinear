module

public import MinCostFlow.Bundle.ForestStep
public import MinCostFlow.SparseCore.CompLSF

/-!
# The canonical core batch

A batch of the component-wise LSF changes the global core graph by an ordered core batch. The proof
of that fact goes through intermediate forests: the forest after the input edit, and then the forest
after each released edge. Each intermediate forest needs roots, one per component, and the proof
only asks that the old roots stay and that every new root is a final root. A machine cannot match a
root chosen by `Classical.choose`, so this file fixes the choice: in each component of an
intermediate forest, keep the old root if there is one, and otherwise take the least final root in
it (`canonRoots`).

With this choice the core batch of one update is a function of the state and the update
(`canonStepCore`): the core edit of the input update, then one core split and one insertion for
each released forest edge, in increasing order of edge names. The core batch of a batch is the
concatenation along the batch (`canonCoreBatch`). It does not depend on the orders of ends.
Only the definitions are here. `CanonCoreSpec.lean` proves that this batch is ordered.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Bundle

/-- The root of a component `A` of an intermediate forest: the least old root in `A` if `A` has
one, and otherwise the least final root in `A`. -/
noncomputable def canonPick (old final A : Finset ℕ) : ℕ :=
  if h : (A ∩ old).Nonempty then (A ∩ old).min' h
  else if h' : (A ∩ final).Nonempty then (A ∩ final).min' h' else 0

/-- The roots of an intermediate forest `F`: one root per component, chosen by `canonPick`. -/
noncomputable def canonRoots (F : MGraph) (old final : Finset ℕ) : Finset ℕ :=
  (components F).image (canonPick old final)

/-- The root that a refinement adds, when it adds exactly one. -/
def newRoot (R old : Finset ℕ) : ℕ := (R \ old).sup id

/-- The core split of a forest refinement from core graph `C` to `C'`: the root `r` keeps its
name, and the ends whose endpoint in `C'` is `fresh` move to `fresh`. -/
def refineSplit (C C' : MGraph) (r fresh : ℕ) : Update :=
  .split r fresh (C.E.filter fun e => C'.tail e = fresh) (C.E.filter fun e => C'.head e = fresh)

/-- The core batch of releasing the forest edges `cuts` in this order, on the graph `G`, from the
LSF `L`, with final roots `final`. Each release is a core split followed by the insertion of the
released edge. -/
noncomputable def releasesBatch (G : MGraph) (final : Finset ℕ) (L : LSF) :
    List ℕ → List Update
  | [] => []
  | e :: cuts =>
    let K := eraseForestEdge L.F.F e
    let L' : LSF := ⟨L.T, ⟨K, canonRoots K L.F.R final⟩, L.wstr⟩
    refineSplit (coreGraph G L) (coreGraph (G.applyUpdate (.delete e)) L')
        (L.F.root (L.F.F.tail e)) (newRoot L'.F.R L.F.R) ::
      .insert e (L'.F.root (G.tail e)) (L'.F.root (G.head e)) :: releasesBatch G final L' cuts

/-- The LSF after the input edit of `u` and before the released edges. An insertion and the
deletion of a non-forest edge keep the forest. Otherwise the forest is `forestAfterInput`, with
the roots of `canonRoots`. -/
noncomputable def inputMid (cs : CompLSFState) (u : Update) : LSF :=
  let K := forestAfterInput cs.RF.F u
  let refined : LSF := ⟨cs.lsf.T, ⟨K, canonRoots K cs.RF.R (compLSFStepSingle cs u).RF.R⟩,
    cs.lsf.wstr⟩
  match u with
  | .insert .. => cs.lsf
  | .delete e => if e ∈ cs.RF.F.E then refined else cs.lsf
  | .split .. => refined

/-- The core edit of the input update `u`: an insertion between the
roots of its endpoints, the deletion of a non-forest edge, or one core split for a deleted
forest edge or a vertex split. -/
noncomputable def inputCoreBatch (cs : CompLSFState) (u : Update) : List Update :=
  let M := inputMid cs u
  match u with
  | .insert e a b => [.insert e (cs.RF.root a) (cs.RF.root b)]
  | .delete e =>
    if e ∈ cs.RF.F.E then
      [refineSplit (coreGraph cs.G cs.lsf) (coreGraph (cs.G.applyUpdate (.delete e)) M)
        (cs.RF.root (cs.RF.F.tail e)) (newRoot M.F.R cs.RF.R)]
    else [.delete e]
  | .split v v' At Ah =>
    [refineSplit (coreGraph cs.G cs.lsf) (coreGraph (cs.G.applyUpdate (.split v v' At Ah)) M)
      (cs.RF.root v) (newRoot M.F.R cs.RF.R)]

/-- The canonical core batch of one update: the core edit of the input, then the releases of the
forest edges that the LSF update cuts, in increasing order of names. -/
noncomputable def canonStepCore (cs : CompLSFState) (u : Update) : List Update :=
  inputCoreBatch cs u ++
    releasesBatch (cs.G.applyUpdate u) (compLSFStepSingle cs u).RF.R (inputMid cs u)
      (((forestAfterInput cs.RF.F u).E \ (compLSFStepSingle cs u).RF.F.E).sort (· ≤ ·))

/-- The canonical core batch of a batch: the canonical core batches of its updates, each taken
in the state that the earlier updates reach. -/
noncomputable def canonCoreBatch : CompLSFState → List Update → List Update
  | _, [] => []
  | cs, u :: U => canonStepCore cs u ++ canonCoreBatch (compLSFStepSingle cs u) U

end MinCostFlow.SparseCore
