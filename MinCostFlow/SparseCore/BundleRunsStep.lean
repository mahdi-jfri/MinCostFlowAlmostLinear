module

public import MinCostFlow.SparseCore.BundleRunsList
public import MinCostFlow.SparseCore.CompLSF
public import MinCostFlow.SparseCore.SplitSpannerBuckets
public import MinCostFlow.Bundle.CoreCongr

/-!
# The canonical bundle step

The bundles of one bucket must stay arcs of the core rotation after a batch. The existence proof
runs the bundle step through the intermediate rotations of the ordered core batch, which a machine
does not have. This file defines a bundle step that uses only the core rotation after the batch.

First delete the bundle edges that the input batch deletes. Then, for each bundle `b` in
increasing order, list its runs: at each core vertex after the batch, in increasing order, the
maximal arcs of the ends of `b` in the order at that vertex restricted to the kept bundle edges
(`bundleRunsOf`). The first run keeps the name `b`. The other runs get fresh names in order
(`runsFoldStep`, which uses `bundleSplitFoldStep` and sets the parent of each run to its core
vertex). A run has at most as many ends as `b`, so no run needs to be cut to the size bound.

`coreOrderOf` reads the order of the core rotation off the input order. It does not depend on the
rotation or the proofs that give it (`coreOrderOf_eq`). Only definitions and that lemma are here.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Bundle MinCostFlow.DynSpanner

/-- The order of the core rotation of a component-wise LSF state, for an input rotation with
order `ord`. It is empty when no such rotation exists or the LSF does not root the graph. -/
noncomputable def coreOrderOf (cs : CompLSFState) (ord : ℕ → List End) : ℕ → List End :=
  open Classical in
  if h : ∃ (σ : Rotation cs.G) (_ : cs.G.IsValid) (_ : cs.RF.IsRootedSpanningForestOf cs.G),
      σ.order = ord then
    (coreRotation (L := cs.lsf) h.choose h.choose_spec.choose
      h.choose_spec.choose_spec.choose).order
  else fun _ => []

/-- The order of a core rotation depends only on the order of the input rotation. -/
theorem coreOrderOf_eq {cs : CompLSFState} {ord : ℕ → List End} (σ : Rotation cs.G)
    (hG : cs.G.IsValid) (hF : cs.RF.IsRootedSpanningForestOf cs.G) (hσ : σ.order = ord) :
    (coreRotation (L := cs.lsf) σ hG hF).order = coreOrderOf cs ord := by
  have h : ∃ (σ : Rotation cs.G) (_ : cs.G.IsValid) (_ : cs.RF.IsRootedSpanningForestOf cs.G),
      σ.order = ord := ⟨σ, hG, hF, hσ⟩
  have key : ∀ (σ₁ σ₂ : Rotation cs.G) (hG₁ hG₂ : cs.G.IsValid)
      (hF₁ hF₂ : cs.RF.IsRootedSpanningForestOf cs.G), σ₁.order = σ₂.order →
      (coreRotation (L := cs.lsf) σ₁ hG₁ hF₁).order =
        (coreRotation (L := cs.lsf) σ₂ hG₂ hF₂).order := by
    intro σ₁ σ₂ hG₁ hG₂ hF₁ hF₂ he
    have := Rotation.ext_order he
    subst this
    rfl
  unfold coreOrderOf
  rw [dite_eq_left h]
  exact key _ _ _ _ _ _ (hσ.trans h.choose_spec.choose_spec.choose_spec.symm)

/-- Index of the first run in `L` with maximum `.2.length` (0 when `L` is empty). -/
def maxRunIdx : List (ℕ × List End) → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
    let j := maxRunIdx (b :: rest)
    if ((b :: rest).getD j (0, [])).2.length > a.2.length then j + 1 else 0

/-- Move the first run with maximum length to the front, preserving the relative order of all
remaining runs (so the largest run keeps the old bundle name `b`, breaking ties by smallest core
vertex, and all moved runs remain in increasing core-vertex order). -/
def promoteLargestRun (L : List (ℕ × List End)) : List (ℕ × List End) :=
  match L with
  | [] => []
  | _ :: _ =>
    let j := maxRunIdx L
    L.getD j (0, []) :: L.eraseIdx j

/-- The raw runs of bundle `b`, each with its core vertex, ordered by increasing core vertex. -/
noncomputable def rawBundleRunsOf (R : Finset ℕ) (cord : ℕ → List End) (E : Finset ℕ)
    (B : BundleState) (b : ℕ) : List (ℕ × List End) :=
  (R.sort (· ≤ ·)).flatMap fun v =>
    (cycRuns (fun x => decide (B.bundleOf x = b)) ((cord v).filter fun x => decide (x.1 ∈ E))).map
      fun r => (v, r)

/-- The runs of bundle `b`, each with its core vertex: the largest run (breaking ties by smallest
core vertex) is placed first so it keeps the old bundle name `b`, followed by the remaining runs in
increasing core-vertex order. -/
noncomputable def bundleRunsOf (R : Finset ℕ) (cord : ℕ → List End) (E : Finset ℕ)
    (B : BundleState) (b : ℕ) : List (ℕ × List End) :=
  promoteLargestRun (rawBundleRunsOf R cord E B b)

/-- The core vertex of the run that a bundle name `w` gets when bundle `b` with runs `vruns` is
processed and the fresh names start at `next`. -/
def runParent (b next : ℕ) (vruns : List (ℕ × List End)) (old : ℕ → ℕ) (w : ℕ) : ℕ :=
  match (if w = b then vruns.head? else if next ≤ w then vruns[w - next + 1]? else none) with
  | none => old w
  | some vr => vr.1

/-- Process one bundle: the first run keeps the name `b`, the other runs get fresh names, and
each run gets its core vertex as parent. -/
noncomputable def runsFoldStep :
    List Update × BundleState → ℕ × List (ℕ × List End) → List Update × BundleState
  | s, (b, vruns) =>
    let r := bundleSplitFoldStep 0 0 (fun _ => false) s (b, vruns.map Prod.snd)
    (r.1, { r.2 with parent := runParent b (s.2.vertices.sup id + 1) vruns s.2.parent })

/-- The canonical bundle step of one bucket: delete the
bundle edges that `U` deletes, then cut every bundle into its runs in the core rotation after
the batch, given by the order `ord'` of the input after the batch. -/
noncomputable def bundleRunsStep (cs : CompLSFState) (B : BundleState) (_k : ℕ)
    (ord' : ℕ → List End) (U : List Update) : List Update × BundleState :=
  let cs' := compLSFBatch cs U
  let E := B.edges \ batchDeletes U
  let cord := coreOrderOf cs' ord'
  let dels := ((B.edges ∩ batchDeletes U).sort (· ≤ ·)).map Update.delete
  let plan := (B.vertices.sort (· ≤ ·)).map fun b => (b, bundleRunsOf cs'.RF.R cord E B b)
  plan.foldl runsFoldStep (dels, { B with edges := E })

end MinCostFlow.SparseCore
