module

public import MinCostFlow.SparseCore.Program.RestartModelState

/-!
# The bundle-side record and step invariants (`AssemblyBranchSideInv`)

Defines the concrete bundle-side record `AsmBrSide`, its bucket-spanner parameters `asmBrSP`, and
the two step invariants carried by `AsmBrSideModel` (`AssemblyBranchSide.lean`):

* `AsmFirstSideSlotInv`: reserves enough slot capacity in both the bundle table (`slotCap`) and
  the bucket-spanner table (`cap`) for every component-bucket pair of `G₀`, pins `y.slots` to
  `List.range y.slots.length`, and ensures every unused slot is `none` in both `y.bunS` and
  `y.spanS`, so a step can allocate newly active pairs sequentially starting at `y.slots.length`.
* `AsmFirstInactiveCompInv`: for every still-inactive component `C ∈ components tr.cs.G₀` with
  `C ∉ tr.activeComps`, `C` still has a single root, its core edges lie in `tr.cs.G₀.E`,
  `tr.activeBuckets C` equals its core-edge buckets, and each lazy pair `(C, b)` matches
  `initBundleFor` and satisfies `SpanGraphOK`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart

/-- The concrete state of the bundle side: the caps of the two tables, the spanner parameters,
and for each part its handle, its abstract state and its concrete state; the slot list and the
slot of each pair; the addresses of the maps, the list of the components of `G₀` in the order of
their indices, and the address and the content of the slot list of each component; and the value
`walkPot` of the walk potential, which the program does not store. -/
structure AsmBrSide (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (depth : ℕ) where
  kB : ℕ
  slotCap : ℕ
  vCap5 : ℕ
  eCap5 : ℕ
  cap : ℕ
  splitB : ℕ
  spV : ℕ
  spE : ℕ
  mMax : ℕ
  bunH : ℕ
  bunS : Fin slotCap → Option BundleState
  xBun : (B5 kB slotCap vCap5 eCap5).τ
  spanH : ℕ
  spanS : BucketSpannerState cap
  xSpan : BucketSpannerMeta depth cap
  slotsPtr : ℕ
  slots : List ℕ
  slotsCap : ℕ
  slotOf : Finset ℕ × ℤ → ℕ
  cmpH : ℕ
  bktH : ℕ
  ctH : ℕ
  comps : List (Finset ℕ)
  cslPtr : ℕ → ℕ
  cslL : ℕ → List (ℤ × ℕ)
  walkPot : ℕ
  lgFac : ℕ

/-- The parameters of the bucket spanners of the bundle side: the sparsifier `impl`, the word size
`w` and the level count `depth` are those of the representation, the rest is stored. -/
def asmBrSP {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    (impl : SparsifyImpl) (w depth : ℕ) (y : AsmBrSide B5 depth) : DSParams :=
  ⟨impl, y.mMax, w, depth, y.spV, y.spE, y.splitB⟩

/-- **Slot-capacity and sequential-allocation invariant of the bundle side**:
reserves enough slot capacity (in the bundle table `slotCap`, the bucket-spanner table `cap`, and
the active slot list buffer `slotsCap`) for every component-bucket pair of `G₀`, pins `y.slots` to
`List.range y.slots.length`, and ensures every unused slot is `none` in both `y.bunS` and
`y.spanS` so newly active pairs can be allocated sequentially starting at `y.slots.length`. -/
def AsmFirstSideSlotInv {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {depth : ℕ} (tr : BundleTreeState depth) (y : AsmBrSide B5 depth) : Prop :=
  (components tr.cs.G₀).sum (fun C => (tr.activeBuckets C).card) ≤
      min (min y.slotCap y.cap) y.slotsCap ∧
  y.slots = List.range y.slots.length ∧
  (∀ j : Fin y.slotCap, j.1 ∉ y.slots → y.bunS j = none) ∧
  (∀ j : Fin y.cap, j.1 ∉ y.slots → y.spanS j = none)

/-- **Inactive-component invariant of the bundle side**:
for every still-inactive component `C ∈ components tr.cs.G₀ \ tr.activeComps`, `C` still has a
single root (so `tourOp 4` at `tr.cs.RF.root v` lists all core ends of `C` in
`O((|coreEdges(C)| + 1) * log eCap)` time, paying `0` extra for tree components), every core edge
of `C` lies in `tr.cs.G₀.E` (so `bktH[e]` is defined), `tr.activeBuckets C` equals its core-edge
buckets, and each lazy `(C, b)` matches `initBundleFor` and satisfies `SpanGraphOK`. -/
def AsmFirstInactiveCompInv {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    (impl : SparsifyImpl) (w depth : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
    (y : AsmBrSide B5 depth) : Prop :=
  ∀ C ∈ components tr.cs.G₀, C ∉ tr.activeComps →
    (tr.cs.compSt C).R.card = 1 ∧
    tr.activeBuckets C = ((coreGraph tr.cs.G tr.cs.lsf).E.filter fun e =>
      (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ C).image tr.origBucket ∧
    (∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E,
      (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ C → e ∈ tr.cs.G₀.E) ∧
    4 * (tr.cs.compSt C).G.m < tr.k ∧
    ∀ b ∈ tr.activeBuckets C,
      BunAgree (initBundleFor tr.cs ord
        (bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket C b) tr.k) (tr.bun (C, b)) ∧
      tr.initBunG (C, b) = normGraph (tr.bun (C, b)).graph ∧
      SpanGraphOK (asmBrSP impl w depth y) (tr.initBunG (C, b))

/-- Every still-inactive component `C ∈ components tr.cs.G₀ \ tr.activeComps` has no cross edges
and no endpoint of any cross edge. Holds trivially at init (`crossEdges = ∅`) and is preserved by
`stepBundleTree` and `restartBundleTree`. -/
def AsmFirstCrossInactiveInv {depth : ℕ} (tr : BundleTreeState depth) : Prop :=
  ∀ C ∈ components tr.cs.G₀, C ∉ tr.activeComps →
    Disjoint (tr.cs.compSt C).G.E tr.cs.crossEdges ∧
    ∀ e ∈ tr.cs.crossEdges,
      tr.cs.G.tail e ∉ (tr.cs.compSt C).G.V ∧ tr.cs.G.head e ∉ (tr.cs.compSt C).G.V

/-- `initBundleTreeWithParams` trivially satisfies `AsmFirstCrossInactiveInv` (`crossEdges = ∅`). -/
theorem asmFirstCrossInactiveInv_init (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ)
    (ord : ℕ → List End) (j : ℕ) :
    AsmFirstCrossInactiveInv
      (initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G₀ ℓ₀ ord j) := by
  intro C _ _
  have h0 :
      (initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G₀ ℓ₀ ord j).cs.crossEdges =
        ∅ := rfl
  rw [h0]
  exact ⟨Finset.disjoint_empty_right _, fun _ he => by cases he⟩

/-- `restartBundleTree` trivially preserves `AsmFirstCrossInactiveInv`. -/
theorem asmFirstCrossInactiveInv_restart (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState L} {ord : ℕ → List End}
    (hInv : AsmFirstCrossInactiveInv tr) :
    AsmFirstCrossInactiveInv (restartBundleTree L sparsify tr ord) :=
  hInv

/-- **Inactive-component spanner invariant (`AsmFirstInactiveDynInv`)**: for every still-inactive component
`C ∈ components tr.cs.G₀ \ tr.activeComps` and every active bucket `b ∈ tr.activeBuckets C`,
the model spanner `tr.dyn (C, b)` is the fresh spanner state on `tr.initBunG (C, b)`. -/
def AsmFirstInactiveDynInv
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    (impl : SparsifyImpl) (w depth : ℕ) (tr : BundleTreeState depth)
    (y : AsmBrSide B5 depth) : Prop :=
  ∀ C ∈ components tr.cs.G₀, C ∉ tr.activeComps →
    ∀ b ∈ tr.activeBuckets C,
      tr.dyn (C, b) = DSHist.state (asmBrSP impl w depth y) ⟨tr.initBunG (C, b), []⟩

/-- **Active-bundle partition invariant (`AsmFirstActiveBunPartInv`)**: for every active component
`C ∈ tr.activeComps` and active bucket `b ∈ tr.activeBuckets C`, `tr.bun (C, b)` is a
`tr.k`-bundle partition for the core rotation of every rotation of `tr.cs.G` with order `ord`. -/
def AsmFirstActiveBunPartInv {depth : ℕ} (tr : BundleTreeState depth)
    (ord : ℕ → List End) : Prop :=
  ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
    ∀ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (ρ : Rotation tr.cs.G),
      ρ.order = ord →
      (tr.bun (C, b)).IsPartition
        (coreRotation (L := tr.cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) tr.k

/-- **Active-spanner graph equivalence invariant (`AsmFirstActiveDynGraphInv`)**: for every active component
`C ∈ tr.activeComps` and active bucket `b ∈ tr.activeBuckets C`, the dynamic spanner graph
`(tr.dyn (C, b)).G` agrees with `(tr.bun (C, b)).graph` on `(V, E, tail|_E, head|_E)` (`GraphEq`).
Raw record equality `(tr.dyn (C, b)).G = normGraph (tr.bun (C, b)).graph` fails after deleting a
bundle edge with a nonzero endpoint because `MGraph.applyUpdate (.delete e)` leaves `tail`/`head`
unchanged outside `E`; `GraphEq` is the exact invariant preserved by init, restart, and
`stepBundleTree`. -/
def AsmFirstActiveDynGraphInv {depth : ℕ} (tr : BundleTreeState depth) : Prop :=
  ∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
    GraphEq (tr.dyn (C, b)).G (tr.bun (C, b)).graph

end MinCostFlow.SparseCore.Program
