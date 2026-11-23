module

public import MinCostFlow.SparseCore.Program.AssemblyBranchRep
public import MinCostFlow.SparseCore.Program.AssemblyBranchSideInv
public import MinCostFlow.SparseCore.Program.RestartModelCost
public import MinCostFlow.SparseCore.Program.AssemblyBranchFacts
public import MinCostFlow.SparseCore.Program.BunRestartIface

import MinCostFlow.SparseCore.Program.SpanBucketInit

/-!
# The bundle side of a branch (`AssemblyBranchSide`)

A branch of the sparse-core program (`AssemblyBranchRep.lean`) keeps its bundles and bucket
spanners in a part of its own, the *bundle side*. This file fixes its memory layout as a
representation `asmBrSideRep` of the abstract state of the branch, and proves that it is local
(`asmBrSideRep_local`). The main representation `asmBrRep` takes it as its part `X`.

**The parts.** The bundle side has a record of `16` words at its handle `s`, and three parts:
* the bundle table of piece P5, the table `Fin slotCap → Option BundleState`
  in a representation `B5 kB slotCap vCap₅ eCap₅` chosen by that piece, for the bundle cap `kB`
  of the state. Its vertex cap `vCap₅` and `kB` are not words of the record: P5 keeps them in its
  own table;
* the bucket spanners of piece P6 (`bucketSpannerRep`), with the parameters of the
  spanners `asmBrSP`;
* the list of the slots that hold the active pairs of a component and a bucket (`ListAt`), and
  the maps from vertices and edges to components and slots (`AsmSdMapsAt`). The list has one
  cell more than its length, so that its address lies below the heap pointer even when the list
  is empty.

| word | content |
| --- | --- |
| `s + 0` to `s + 3` | handles of the bundle table, the spanners and the slot list; its length |
| `s + 4`, `s + 5`, `s + 6` | `slotCap`, `eCap₅`, `cap` |
| `s + 7` .. `s + 11` | the spanner parameters `L`, `splitBound`, `vCap`, `eCap`, `mMax` |
| `s + 12` .. `s + 15` | the addresses of the three maps; the number of components |

**The maps.** The first phase of a step routes the updates to the bundles. For that it must find,
for a vertex, its component of `G₀`, for an edge, its bucket `origBucket`, and for a component,
whether it is active and the slots of its active pairs. The bundle side keeps these as arrays
(`AsmSdMapsAt`): a vertex array, an edge array, a table with three words per component (the
active flag, the address and the length of its slot list), and for each component a list of the
pairs `(bucket, slot)` of its active pairs. They are written at the init. A restart keeps them,
since it changes neither the components, nor the active pairs, nor their slots
(`asmSdMaps_restart`).

**What the bundle side keeps true** (`AsmBrSideModel`). The slots of the list hold the active
pairs one to one (`SlotMapOK`), the bundle table agrees with the bundles of the model
(`BunTableMatches`), and the spanner of the slot of an active pair is the spanner of the model,
with the start graph `initBunG` of the pair as its start graph.
It also keeps the facts on the model state that a restart of the branch needs
(`restartBranch_model_runs`, `RestartModelCost.lean`): the invariant `RestartScurModelInv`, the
conditions of the spanner initializations on the new bundle graphs (`SpanGraphOK`), a rotation of
the input graph with the input order, and the bounds on the spanner parameters. It keeps
`BunDisjointInv` too: distinct active bundles share no edge, and no bundle edge is a cross edge.
The refresh of the embedding table after a restart needs it (`AssemblyBranchEmbLink.lean`).
Except for the last one, these are facts about the model state alone; the operations that change
the state keep them. The last one is P5's invariant `bunRestartInv` between its table and the core
lists `outCoreOrder` of the tour: every bundle of the table lies in the core list of its parent,
and the core lists sit below the caps. P5's restart and P5's parent query ask it.
Two more facts are for the step. The lazy init charge `lazyMachInitCost C` of an inactive
component holds `spanConst · spanInitBound` for the start graph of each of its buckets. A step that
makes the component active pays the init of its slots from it.
The last facts bound the caps `spV`, `spE` of the bucket spanners by the caps of the branch,
give the bundle cap `kB` of the table as the cap `k` of the state, and carry the two step
invariants `AsmFirstSideSlotInv` and `AsmFirstInactiveCompInv` (`AssemblyBranchSideInv.lean`):
slot capacity for every component-bucket pair of `G₀` with sequential free slots in both tables,
and the single-root / bucket / lazy-bundle / `SpanGraphOK` facts for still-inactive components.
P10's restart reads the spanners and needs `spE ≤ eCap` (`readBranchAt_readRep`). P5's restart cuts
the bundles with the cap of its table, so it cuts them with `k`.

**The potential** (`asmBrSideRep`) has three terms: the potential of the bundle table, three times
the banks of the bucket spanners, and the walk potential `Ψ` of the model state. A step spends the
banks three times: in the update of the spanners in P6, for the new table walks, and for the new
list of edges and its sort. `Ψ` is the total length of the table walks of the edges of `S_cur`
that lie in the graph of an active bucket spanner. It pays the new walk of an edge that leaves
`S_cur` but stays in a spanner graph. Here `Ψ` is a parameter, a function of the model state. The
bundle side holds its value as a number `walkPot` that the program does not store, and
`AsmBrSideModel` ties it to `Ψ`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart

/-! ## The record -/

/-- Offset of the handle of the bundle table. -/
def ASM_SD_BUN : ℕ := 0
/-- Offset of the handle of the bucket spanners. -/
def ASM_SD_SPAN : ℕ := 1
/-- Offset of the address of the slot list. -/
def ASM_SD_SLOTS : ℕ := 2
/-- Offset of the length of the slot list. -/
def ASM_SD_NSLOTS : ℕ := 3
/-- Offset of the number of slots of the bundle table. -/
def ASM_SD_SLOTCAP : ℕ := 4
/-- Offset of the edge cap of the bundle table. -/
def ASM_SD_ECAP5 : ℕ := 5
/-- Offset of the number of slots of the bucket spanners. -/
def ASM_SD_CAP : ℕ := 6
/-- Offset of the level count `L` of the spanners. -/
def ASM_SD_SPL : ℕ := 7
/-- Offset of the split bound of the spanners. -/
def ASM_SD_SPLIT : ℕ := 8
/-- Offset of the vertex cap of the spanners. -/
def ASM_SD_SPV : ℕ := 9
/-- Offset of the edge cap of the spanners. -/
def ASM_SD_SPE : ℕ := 10
/-- Offset of the edge bound `mMax` of the spanners. -/
def ASM_SD_MMAX : ℕ := 11
/-- Offset of the address of the array from vertices to their component. -/
def ASM_SD_CMP : ℕ := 12
/-- Offset of the address of the array from edges to their bucket. -/
def ASM_SD_BKT : ℕ := 13
/-- Offset of the address of the table of the components. -/
def ASM_SD_CT : ℕ := 14
/-- Offset of the number of components. -/
def ASM_SD_NCOMP : ℕ := 15
/-- The number of words of the record. -/
def ASM_SD_SIZE : ℕ := 16

/-! ## The maps -/

/-- The word of a bucket: `2 b` for `b ≥ 0` and `2 |b| - 1` for `b < 0`. -/
def bucketCode (b : ℤ) : ℕ := if 0 ≤ b then 2 * b.toNat else 2 * (-b).toNat - 1

/-- The cells of block `i` of the maps of the bundle side: the array from vertices to their
component (`0`, one word per vertex below `vCap₅`), the array from edges to their bucket (`1`, one
word per edge below `eCap₅`), the table of the components (`2`, three words per component), and the
slot list of component `c` (`c + 3`, two words per entry). -/
def asmSdMapPart {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {depth : ℕ} (y : AsmBrSide B5 depth) : ℕ → ℕ → Prop
  | 0, a => y.cmpH ≤ a ∧ a < y.cmpH + y.vCap5
  | 1, a => y.bktH ≤ a ∧ a < y.bktH + y.eCap5
  | 2, a => y.ctH ≤ a ∧ a < y.ctH + 3 * y.comps.length
  | c + 3, a => c < y.comps.length ∧ y.cslPtr c ≤ a ∧ a < y.cslPtr c + 2 * (y.cslL c).length

/-- The cells of the maps of the bundle side. -/
def asmSdMapCell {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {depth : ℕ} (y : AsmBrSide B5 depth) (a : ℕ) : Prop :=
  ∃ i, asmSdMapPart y i a

/-- The cells of part `i` of the bundle side with handle `s`: the record (`0`), the bundle table
(`1`), the bucket spanners (`2`), and the slot list with the maps (`3`). -/
def asmSdPart
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {depth : ℕ}
    (s : ℕ) (y : AsmBrSide B5 depth) : ℕ → ℕ → Prop
  | 0, a => s ≤ a ∧ a < s + ASM_SD_SIZE
  | 1, a => (B5 y.kB y.slotCap y.vCap5 y.eCap5).foot y.bunH y.xBun a
  | 2, a => bucketFoot y.spanH y.xSpan a
  | 3, a => (y.slotsPtr ≤ a ∧ a < y.slotsPtr + y.slotsCap + 1) ∨ asmSdMapCell y a
  | _, _ => False

/-- The cells of the bundle side: the union of its four parts. -/
def asmSdFoot
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {depth : ℕ}
    (s : ℕ) (y : AsmBrSide B5 depth) (a : ℕ) : Prop :=
  ∃ i < 4, asmSdPart s y i a

/-- **What the bundle side keeps true of the model state** `a` (see the module docstring), for the
walk potential `Ψ`. The spanner parameters are `asmBrSP impl w depth y`. -/
def AsmBrSideModel {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    (impl : SparsifyImpl) (w depth L capExp limbMul : ℕ) (Ψ : BundleTreeState depth → ℕ)
    (a : AsmBranchAbs depth) (y : AsmBrSide B5 depth) : Prop :=
  SlotMapOK a.tr y.slotCap y.cap y.slots y.slotOf ∧
  BunTableMatches a.tr y.slotOf y.bunS ∧
  (∀ q ∈ activePairs a.tr, ∃ (hs : y.slotOf q < y.cap) (d : DSHist),
    y.spanS ⟨y.slotOf q, hs⟩ = some d ∧ d.state (asmBrSP impl w depth y) = a.tr.dyn q ∧
    d.G₀ = a.tr.initBunG q ∧
    (∀ u ∈ d.flat, isDelOrSplit u) ∧ d.G₀.BatchIsValid d.flat ∧
    (∀ B ∈ d.Us, B ≠ [])) ∧
  RestartScurModelInv a.tr ∧
  (∀ s ∈ y.slots, SpanGraphOK (asmBrSP impl w depth y)
    (restartSlotGraph y.bunS a.tr.cs a.ord a.tr.k s)) ∧
  1 ≤ a.tr.k ∧
  (∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (_ : CompLSFInv C_lsst ℓ₀ a.tr.cs) (ρ : Rotation a.tr.cs.G),
    ρ.order = a.ord) ∧
  SparsifyParamsLe (canonicalSparsifyParams impl y.mMax).absorbTime a.tr.spanParams ∧
  dsAmortConst impl ≤ a.tr.spanConst ∧
  y.splitB = a.tr.splitBound ∧
  SparseCoreCapHyp (capExp + 7) limbMul L a.tr.m₀ a.tr.n₀ y.spV y.spE ∧
  BunDisjointInv a.tr ∧
  bunRestartInv a.vCap a.eCap y.bunS (outCoreOrder a.tr a.ord) ∧
  y.walkPot = Ψ a.tr ∧
  (∀ C ∉ a.tr.activeComps, ((a.tr.activeBuckets C).sum fun b => a.tr.spanConst *
    spanInitBound a.tr.spanParams depth a.tr.splitBound (a.tr.initBunG (C, b))) ≤
      a.tr.lazyMachInitCost C) ∧
  y.spV ≤ a.vCap + 2 * a.eCap + y.splitB + 1 ∧ y.spE ≤ a.eCap ∧ y.kB = a.tr.k ∧
  AsmFirstSideSlotInv a.tr y ∧
  AsmFirstInactiveCompInv impl w depth a.tr a.ord y ∧
  AsmFirstCrossInactiveInv a.tr ∧
  AsmFirstInactiveDynInv impl w depth a.tr y ∧
  AsmFirstActiveBunPartInv a.tr a.ord ∧
  AsmFirstActiveDynGraphInv a.tr ∧
  y.lgFac = bundleLogFactor a.tr.m₀ a.tr.n₀ ∧
  y.mMax = a.tr.m₀ ∧
  2 * a.eCap + y.splitB + 1 ≤ y.spV ∧
  a.eCap ≤ y.spE

/-- **The maps of the bundle side** at handle `s` for the state `a`. The record holds the addresses
of the maps and the number of components. The list `y.comps` names each component of `G₀` once;
its index is the index of the component. Then:
* the vertex array holds, at each vertex of the graph of the LSF of a component, the index of the
  component;
* the edge array holds, at each edge `e` of `G₀`, the word of its bucket `origBucket e`, and
  `e < eCap₅`;
* the table of the components holds, for component `c`, an active flag (`1` when the component is
  active, `0` otherwise), the address of its slot list and its length;
* the slot list of component `c` holds, once each, the pairs `(bucket, slot)` of its active pairs,
  two words per pair;
* the cells of the maps hold words, the blocks of the maps are pairwise apart, and they are apart
  from the slot list. -/
def AsmSdMapsAt {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    (w : ℕ) {depth : ℕ} (s : ℕ) (a : AsmBranchAbs depth) (y : AsmBrSide B5 depth)
    (mem : ℕ → ℕ) : Prop :=
  mem (s + ASM_SD_CMP) = y.cmpH ∧ mem (s + ASM_SD_BKT) = y.bktH ∧ mem (s + ASM_SD_CT) = y.ctH ∧
  mem (s + ASM_SD_NCOMP) = y.comps.length ∧
  y.comps.Nodup ∧ (∀ C, C ∈ y.comps ↔ C ∈ components a.tr.cs.G₀) ∧
  (∀ c (hc : c < y.comps.length), ∀ v ∈ (a.tr.cs.compSt y.comps[c]).G.V,
    v < y.vCap5 ∧ mem (y.cmpH + v) = c) ∧
  (∀ e ∈ a.tr.cs.G₀.E, e < y.eCap5 ∧ mem (y.bktH + e) = bucketCode (a.tr.origBucket e)) ∧
  (∀ c (hc : c < y.comps.length),
    mem (y.ctH + 3 * c) = (if y.comps[c] ∈ a.tr.activeComps then 1 else 0) ∧
    mem (y.ctH + 3 * c + 1) = y.cslPtr c ∧ mem (y.ctH + 3 * c + 2) = (y.cslL c).length ∧
    (y.cslL c).Nodup ∧
    (∀ i (hi : i < (y.cslL c).length), mem (y.cslPtr c + 2 * i) = bucketCode (y.cslL c)[i].1 ∧
      mem (y.cslPtr c + 2 * i + 1) = (y.cslL c)[i].2) ∧
    ∀ b t, (b, t) ∈ y.cslL c ↔
      (y.comps[c], b) ∈ activePairs a.tr ∧ t = y.slotOf (y.comps[c], b)) ∧
  (∀ a', asmSdMapCell y a' → mem a' < 2 ^ w) ∧
  (∀ i j, i ≠ j → ∀ a', asmSdMapPart y i a' → ¬ asmSdMapPart y j a') ∧
  (∀ a', asmSdMapCell y a' → ¬ (y.slotsPtr ≤ a' ∧ a' < y.slotsPtr + y.slotsCap + 1))

/-- **The memory of the bundle side** at handle `s`: the record holds the handles, the caps and
the spanner parameters, all words; the bundle table holds `y.bunS`, the bucket spanners hold
`y.spanS`, the slot list holds `y.slots`; the four parts are pairwise disjoint; the maps hold
(`AsmSdMapsAt`); and `AsmBrSideModel` holds. -/
def AsmBrSideAt (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (impl : SparsifyImpl) (w depth L capExp limbMul : ℕ) (Ψ : BundleTreeState depth → ℕ) (s : ℕ)
    (a : AsmBranchAbs depth) (y : AsmBrSide B5 depth) (mem : ℕ → ℕ) : Prop :=
  mem (s + ASM_SD_BUN) = y.bunH ∧ mem (s + ASM_SD_SPAN) = y.spanH ∧
  mem (s + ASM_SD_SLOTS) = y.slotsPtr ∧ mem (s + ASM_SD_NSLOTS) = y.slots.length ∧
  mem (s + ASM_SD_SLOTCAP) = y.slotCap ∧ mem (s + ASM_SD_ECAP5) = y.eCap5 ∧
  mem (s + ASM_SD_CAP) = y.cap ∧ mem (s + ASM_SD_SPL) = depth ∧
  mem (s + ASM_SD_SPLIT) = y.splitB ∧ mem (s + ASM_SD_SPV) = y.spV ∧
  mem (s + ASM_SD_SPE) = y.spE ∧ mem (s + ASM_SD_MMAX) = y.mMax ∧
  (∀ i < ASM_SD_SIZE, mem (s + i) < 2 ^ w) ∧
  (B5 y.kB y.slotCap y.vCap5 y.eCap5).rep y.bunH y.bunS y.xBun mem ∧
  (bucketSpannerRep (asmBrSP impl w depth y) y.cap).rep y.spanH y.spanS y.xSpan mem ∧
  ListAt mem y.slotsPtr y.slots ∧
  y.slots.length ≤ y.slotsCap ∧
  (∀ i < 4, ∀ j < 4, i ≠ j → ∀ c, asmSdPart s y i c → ¬ asmSdPart s y j c) ∧
  AsmSdMapsAt w s a y mem ∧
  AsmBrSideModel impl w depth L capExp limbMul Ψ a y

/-- **The representation of the bundle side**, for the bundle tables `B5` of piece P5, the
sparsifier `impl`, the word size `w`, the level count `depth`, the limb count `L`, the cap
exponent `capExp` and the walk potential `Ψ`. The potential is the potential of the bundle table,
plus three times the banks of the bucket spanners (`bucketPhi`), plus the value of `Ψ` (see the
module docstring). -/
noncomputable def asmBrSideRep
    (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (impl : SparsifyImpl) (w depth L capExp limbMul : ℕ) (Ψ : BundleTreeState depth → ℕ) :
    DSRep (AsmBranchAbs depth) where
  τ := AsmBrSide B5 depth
  rep s a y mem := AsmBrSideAt B5 impl w depth L capExp limbMul Ψ s a y mem
  phi _ y mem := (B5 y.kB y.slotCap y.vCap5 y.eCap5).phi y.bunH y.xBun mem +
    320 * (capExp + 1) * y.lgFac * bucketPhi (asmBrSP impl w depth y) y.xSpan + 300 * y.walkPot
  foot s y a := asmSdFoot s y a

theorem asmBrSideRep_rep
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth L capExp limbMul s : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {a : AsmBranchAbs depth}
    {y : AsmBrSide B5 depth} {mem : ℕ → ℕ} :
    (asmBrSideRep B5 impl w depth L capExp limbMul Ψ).rep s a y mem ↔
      AsmBrSideAt B5 impl w depth L capExp limbMul Ψ s a y mem :=
  Iff.rfl

theorem asmBrSideRep_foot
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth L capExp limbMul s : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {y : AsmBrSide B5 depth} {a : ℕ} :
    (asmBrSideRep B5 impl w depth L capExp limbMul Ψ).foot s y a ↔ asmSdFoot s y a :=
  Iff.rfl

theorem asmBrSideRep_phi
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth L capExp limbMul s : ℕ} {Ψ : BundleTreeState depth → ℕ}
    {y : AsmBrSide B5 depth} {mem : ℕ → ℕ} :
    (asmBrSideRep B5 impl w depth L capExp limbMul Ψ).phi s y mem =
      (B5 y.kB y.slotCap y.vCap5 y.eCap5).phi y.bunH y.xBun mem +
        320 * (capExp + 1) * y.lgFac * bucketPhi (asmBrSP impl w depth y) y.xSpan +
        300 * y.walkPot :=
  rfl

/-- **The maps survive a change of memory** that keeps the record and the cells of the maps. -/
theorem asmSdMaps_of_agree
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {w depth s : ℕ}
    {a : AsmBranchAbs depth} {y : AsmBrSide B5 depth} {mem mem' : ℕ → ℕ}
    (hrec : ∀ i < ASM_SD_SIZE, mem' (s + i) = mem (s + i))
    (hcell : ∀ c, asmSdMapCell y c → mem' c = mem c) (h : AsmSdMapsAt w s a y mem) :
    AsmSdMapsAt w s a y mem' := by
  obtain ⟨h0, h1, h2, h3, hnd, hC, hV, hE, hT, hW, hD, hL⟩ := h
  refine ⟨(hrec _ (by decide)).trans h0, (hrec _ (by decide)).trans h1,
    (hrec _ (by decide)).trans h2, (hrec _ (by decide)).trans h3, hnd, hC, ?_, ?_, ?_,
    fun c hc => (hcell c hc).symm ▸ hW c hc, hD, hL⟩
  · intro c hc v hv
    obtain ⟨hlt, heq⟩ := hV c hc v hv
    exact ⟨hlt, (hcell _ ⟨0, by omega, by omega⟩).trans heq⟩
  · intro e he
    obtain ⟨hlt, heq⟩ := hE e he
    exact ⟨hlt, (hcell _ ⟨1, by omega, by omega⟩).trans heq⟩
  · intro c hc
    obtain ⟨t0, t1, t2, tnd, tL, tiff⟩ := hT c hc
    refine ⟨(hcell _ ⟨2, by omega, by omega⟩).trans t0, (hcell _ ⟨2, by omega, by omega⟩).trans t1,
      (hcell _ ⟨2, by omega, by omega⟩).trans t2, tnd, fun i hi => ?_, tiff⟩
    obtain ⟨l0, l1⟩ := tL i hi
    exact ⟨(hcell _ ⟨c + 3, hc, by omega, by omega⟩).trans l0,
      (hcell _ ⟨c + 3, hc, by omega, by omega⟩).trans l1⟩

/-- **The restart keeps the maps.** A restart of the branch changes only the bundle table and the
spanners of the bundle side. The restarted model state (`restartBundleTree`) has the same LSF
state, active components, active buckets and buckets of the edges, so the maps hold for it as
they are, when the memory keeps the record and the cells of the maps. -/
theorem asmSdMaps_restart
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {w depth s : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) {tr : BundleTreeState depth}
    {ord : ℕ → List End} {vCap eCap wp : ℕ} {y : AsmBrSide B5 depth}
    {bS : Fin y.slotCap → Option BundleState} {xb : (B5 y.kB y.slotCap y.vCap5 y.eCap5).τ}
    {S6 : BucketSpannerState y.cap} {x6 : BucketSpannerMeta depth y.cap} {mem mem' : ℕ → ℕ}
    (hrec : ∀ i < ASM_SD_SIZE, mem' (s + i) = mem (s + i))
    (hcell : ∀ c, asmSdMapCell y c → mem' c = mem c)
    (h : AsmSdMapsAt w s ⟨tr, ord, vCap, eCap⟩ y mem) :
    AsmSdMapsAt w s ⟨restartBundleTree depth sparsify tr ord, ord, vCap, eCap⟩
      { y with bunS := bS, xBun := xb, spanS := S6, xSpan := x6, walkPot := wp } mem' :=
  asmSdMaps_of_agree (y := y) hrec hcell h

/-- **Locality of the bundle side**, when the bundle tables are local. -/
theorem asmBrSideRep_local
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local) (impl : SparsifyImpl)
    (w depth L capExp limbMul : ℕ) (Ψ : BundleTreeState depth → ℕ) :
    (asmBrSideRep B5 impl w depth L capExp limbMul Ψ).Local := by
  intro s a y mem mem' hag
  have hpart : ∀ i < 4, ∀ c, asmSdPart s y i c → mem c = mem' c :=
    fun i hi c hc => hag c ⟨i, hi, hc⟩
  have hb := hB5 y.kB y.slotCap y.vCap5 y.eCap5 y.bunH y.bunS y.xBun mem mem'
    (fun c hc => hpart 1 (by decide) c hc)
  have hsp := bucketSpannerRep_local (asmBrSP impl w depth y) y.cap y.spanH y.spanS y.xSpan
    mem mem' (fun c hc => hpart 2 (by decide) c hc)
  have hrec : ∀ i < ASM_SD_SIZE, mem (s + i) = mem' (s + i) := fun i hi =>
    hpart 0 (by decide) (s + i) ⟨by omega, by omega⟩
  refine ⟨fun hrep => ?_, ?_⟩
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hwd, hB, hS, hL, hSCap, hdisj, hmaps,
      hmod⟩ := hrep
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb.1 hB, hsp.1 hS, ?_, hSCap, hdisj,
      asmSdMaps_of_agree (fun i hi => (hrec i hi).symm)
        (fun c hc => (hpart 3 (by decide) c (Or.inr hc)).symm) hmaps, hmod⟩
    · rw [← hrec ASM_SD_BUN (by decide)]; exact h0
    · rw [← hrec ASM_SD_SPAN (by decide)]; exact h1
    · rw [← hrec ASM_SD_SLOTS (by decide)]; exact h2
    · rw [← hrec ASM_SD_NSLOTS (by decide)]; exact h3
    · rw [← hrec ASM_SD_SLOTCAP (by decide)]; exact h4
    · rw [← hrec ASM_SD_ECAP5 (by decide)]; exact h5
    · rw [← hrec ASM_SD_CAP (by decide)]; exact h6
    · rw [← hrec ASM_SD_SPL (by decide)]; exact h7
    · rw [← hrec ASM_SD_SPLIT (by decide)]; exact h8
    · rw [← hrec ASM_SD_SPV (by decide)]; exact h9
    · rw [← hrec ASM_SD_SPE (by decide)]; exact h10
    · rw [← hrec ASM_SD_MMAX (by decide)]; exact h11
    · intro i hi; rw [← hrec i hi]; exact hwd i hi
    · intro i hi
      rw [← hpart 3 (by decide) (y.slotsPtr + i) (Or.inl ⟨by omega, by omega⟩)]
      exact hL i hi
  · show (B5 y.kB y.slotCap y.vCap5 y.eCap5).phi y.bunH y.xBun mem + _ + _ =
      (B5 y.kB y.slotCap y.vCap5 y.eCap5).phi y.bunH y.xBun mem' + _ + _
    rw [hb.2]

/-- **The lazy init charges at the init of the model.** At the init, the lazy init charge of
each component is the sum over its buckets of `spanConst · spanInitBound` at their start graphs
(`initBundleTreeWithParams`). So the last fact of `AsmBrSideModel` holds at the init, with
equality. -/
theorem lazyMachInitCost_initBundleTree (lsfInit : LSFInit) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ)
    (C : Finset ℕ) :
    let tr := initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G₀ ℓ₀ ord j
    ((tr.activeBuckets C).sum fun b => tr.spanConst *
      spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b))) =
      tr.lazyMachInitCost C :=
  rfl

/-- The record of the bundle side lies below `h` when its cells do. -/
theorem asmSd_record_lt {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {depth s h : ℕ} {y : AsmBrSide B5 depth} (hfoot : ∀ a, asmSdFoot s y a → a < h) :
    s + ASM_SD_SIZE ≤ h := by
  have := hfoot (s + (ASM_SD_SIZE - 1)) ⟨0, by decide, by simp [asmSdPart, ASM_SD_SIZE]⟩
  simp only [ASM_SD_SIZE] at this ⊢
  omega

/-- **Cap bound for bucket-spanner caps** when `spV` leaves room for up to `2 * eCap + splitB + 1`
bundle names (`splitB = bundleSplitBudget k M ≤ 112 * M` for `1 ≤ k`): from
`SparseCoreCapHyp capExp limbMul L M N vCap eCap` we get `SparseCoreCapHyp (capExp + 7)`. -/
theorem sparseCoreCapHyp_spV {capExp limbMul L M N vCap eCap k spV spE : ℕ}
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap) (hk : 1 ≤ k)
    (hspV : spV ≤ vCap + 2 * eCap + bundleSplitBudget k M + 1) (hspE : spE ≤ eCap) :
    SparseCoreCapHyp (capExp + 7) limbMul L M N spV spE := by
  refine ⟨?_, hcap.2⟩
  have h1 : 1 ≤ capExp := by
    by_contra h0
    have hc0 : capExp = 0 := by omega
    have hle := hcap.1
    rw [hc0, pow_zero] at hle
    omega
  have hMN : M + N + 2 ≤ (M + N + 2) ^ capExp := by
    calc M + N + 2 = (M + N + 2) ^ 1 := (pow_one _).symm
      _ ≤ (M + N + 2) ^ capExp := Nat.pow_le_pow_right (by omega) h1
  have hsb : bundleSplitBudget k M ≤ 112 * M := by
    unfold bundleSplitBudget
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hdiv : 56 * (M : ℝ) / (k : ℝ) ≤ (56 * M : ℕ) := by
      push_cast
      exact div_le_self (by positivity) hkR
    have hceil : Nat.ceil (56 * (M : ℝ) / (k : ℝ)) ≤ 56 * M := Nat.ceil_le.mpr hdiv
    omega
  have hpow7 : 128 ≤ (M + N + 2) ^ 7 := by
    calc 128 = 2 ^ 7 := by decide
      _ ≤ (M + N + 2) ^ 7 := Nat.pow_le_pow_left (by omega) 7
  have hcap1 := hcap.1
  calc spV + spE + 2
      ≤ 3 * (vCap + eCap + 2) + 112 * M := by omega
    _ ≤ 3 * (M + N + 2) ^ capExp + 112 * (M + N + 2) ^ capExp := by omega
    _ ≤ 128 * (M + N + 2) ^ capExp := by omega
    _ ≤ (M + N + 2) ^ 7 * (M + N + 2) ^ capExp := Nat.mul_le_mul_right _ hpow7
    _ = (M + N + 2) ^ (capExp + 7) := by rw [← pow_add, Nat.add_comm 7 capExp]

end MinCostFlow.SparseCore.Program
