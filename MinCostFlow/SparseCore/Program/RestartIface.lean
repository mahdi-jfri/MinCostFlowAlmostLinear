module

public import MinCostFlow.SparseCore.Program.SpanBridge
public import MinCostFlow.SparseCore.Program.SpanBucketDefs
public import MinCostFlow.SparseCore.Program.OrdStoreContract
public import MinCostFlow.SparseCore.CompLSFBridge
public import MinCostFlow.Bundle.CoreRotation

/-!
# The restart of a branch: interfaces and statement (`RestartIface`)

A restart of branch `j` (`restartBundleTree`) rebuilds three fields of the
branch: the bundle state `bun (C, b)` and the spanner `dyn (C, b)` of every active pair of a
component and a bucket, and the sparsified core `S_cur`. The machine does it in three steps.

1. The bundle piece (P5) cuts the tours of the core rotation into new bundles,
   for every listed slot, keeping the edges of the slot. It writes, for each slot, the new bundle
   graph in the layout that the spanner initialization reads (`ExportAt`).
2. For each slot, operation `0` of `bucketSpannerDS` (P6) initializes a fresh spanner on
   that graph.
3. The readout-data piece (P10) rebuilds `S_cur` and its other branch data from
   the new spanners.

This file states two pieces as small interfaces (`BunRestartAt`,
`ScurRebuildAt`), defines the program `restartBranchStmt`, and states what it does
(`RestartBranchSpec`). The theorem `restartBranch_runs` (`RestartMain.lean`) proves the statement.

**Bundle graphs up to the names that are not edges.** The bundle graph `B.graph` has
`tail e = B.bundleOf (e, true)` also when `e` is not an edge, and the bundle piece keeps
`bundleOf` exact only on the ends of edges (`BunAgree`). The spanner reads a graph from lists
(`graphOfLists`), which puts `0` there. So the machine spanner is initialized on
`normGraph B.graph`, the same graph with `0` at the names that are not edges. It depends only on
the vertices, the edges and their ends, so it is the same for every bundle state that agrees with
the model on these.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

@[expose] public section

/-! ## Graphs, bundles and exported graphs -/

/-- The graph `G` with `tail` and `head` set to `0` at every name that is not an edge. -/
def normGraph (G : MGraph) : MGraph where
  V := G.V
  E := G.E
  tail e := if e ∈ G.E then G.tail e else 0
  head e := if e ∈ G.E then G.head e else 0

/-- Two bundle states agree on everything a program can see: the bundles, the edges, the parents
and the bundle of every end of an edge. -/
def BunAgree (B B' : BundleState) : Prop :=
  B.vertices = B'.vertices ∧ B.edges = B'.edges ∧ B.parent = B'.parent ∧
    ∀ x : End, x.1 ∈ B.edges → B.bundleOf x = B'.bundleOf x

/-- The descriptor at `d` gives a graph `G` in the layout of the spanner initialization: `[nV,
V_ptr, nE, E_ptr]` at `d`, a list of the `nV` vertices at `V_ptr` and a list of the `nE` triples
`(e, tail e, head e)` of the edges at `E_ptr`, each edge once, all above `d` and below `hEnd`. -/
def ExportAt (mem : ℕ → ℕ) (d hEnd : ℕ) (G : MGraph) : Prop :=
  let vL := readList mem (mem (d + 1)) (mem d)
  let eT := readTriples mem (mem (d + 3)) (mem (d + 2))
  mem d = G.n ∧ mem (d + 2) = G.m ∧ vL.Nodup ∧ (∀ v, v ∈ vL ↔ v ∈ G.V) ∧
    (eT.map Prod.fst).Nodup ∧
    (∀ t ∈ eT, t.1 ∈ G.E ∧ t.2.1 = G.tail t.1 ∧ t.2.2 = G.head t.1) ∧
    (∀ e ∈ G.E, ∃ t ∈ eT, t.1 = e) ∧
    d + 4 ≤ hEnd ∧ d ≤ mem (d + 1) ∧ d ≤ mem (d + 3) ∧
    mem (d + 1) + mem d ≤ hEnd ∧ mem (d + 3) + 3 * mem (d + 2) ≤ hEnd

/-- The tour order `cord` is the order of the core rotation of the branch: the rotation of the
core graph of `cs` built from a rotation of `cs.G` whose order is `ord` (`initBundleFor`). -/
def CoreCordOf (cs : CompLSFState) (ord cord : ℕ → List End) : Prop :=
  ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (hI : CompLSFInv C_lsst ℓ₀ cs) (ρ : Rotation cs.G),
    ρ.order = ord ∧ cord = (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)).order

/-! ## The interface of the bundle piece (P5) -/

/-- **Interface of the bundle restart (piece P5).** Procedure `f` of `p`, called
as `[tbl, tourH, n, slotsPtr, h]` on a bundle table `S` (`Fin slotCap → Option BundleState`, the
state of `BundleLayout.lean`) and a tour holding `cord` (the state of `BundleTourInterface.lean`),
with the `n` distinct slots `slots` listed at `slotsPtr`, where the invariant `inv S cord` of P5
between its table and the tour holds:
* replaces the bundles of every listed slot by `initBundleFor cs ord B.edges k` (up to `BunAgree`),
  keeping the edges `B.edges`, and leaves the other slots, so that `inv` holds again;
* writes at `h + 4 i` the descriptor of the graph of the new bundles of slot `i` (`ExportAt`);
* costs at most `mul · (m + n + 1) · ordStoreLog eCap` with `m = cs.G.m`, amortized against the
  potentials of the table and of the tour.
The bound `m + n + 1` holds because each tour list at a core vertex is scanned once for all slots,
and the lists hold the ends of the core edges, at most `2 m` in all. The bundle cap `k` is a
parameter: a fixed procedure cuts the tours into chunks of one size. -/
structure BunRestartAt (w slotCap eCap k : ℕ) (p : Program) (f : ℕ) where
  rep : DSRep (Fin slotCap → Option BundleState)
  tour : DSRep (ℕ → List End)
  inv : (Fin slotCap → Option BundleState) → (ℕ → List End) → Prop
  mul : ℕ
  space : ℕ → ℕ
  rep_local : rep.Local
  tour_local : tour.Local
  runs : ∀ (tbl tourH slotsPtr h : ℕ) (slots : List ℕ) (S : Fin slotCap → Option BundleState)
      (x : rep.τ) (cord : ℕ → List End) (tx : tour.τ) (cs : CompLSFState) (ord : ℕ → List End)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      tbl < 2 ^ w → tourH < 2 ^ w → slots.length < 2 ^ w → slotsPtr < 2 ^ w → h < 2 ^ w →
      ListAt mem slotsPtr slots → slotsPtr + slots.length ≤ h → slots.Nodup →
      (∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B ∧
        B.edges ⊆ (coreGraph cs.G cs.lsf).E) →
      1 ≤ k → CoreCordOf cs ord cord → inv S cord →
      rep.rep tbl S x mem → tour.rep tourH cord tx mem →
      (∀ a, rep.foot tbl x a → a < h) → (∀ a, tour.foot tourH tx a → a < h) →
      (∀ a, rep.foot tbl x a → ¬ tour.foot tourH tx a) →
      ZeroFrom mem h → h + space (cs.G.m + slots.length) < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c S' x' tx',
        Runs w p ω body (startState [tbl, tourH, slots.length, slotsPtr, h] mem pos) o st' c ∧
        rep.rep tbl S' x' st'.mem ∧ tour.rep tourH cord tx' st'.mem ∧ inv S' cord ∧
        (∀ j : Fin slotCap, j.1 ∉ slots → S' j = S j) ∧
        (∀ i (hi : i < slots.length), ∃ (hs : slots[i] < slotCap) (B B' : BundleState),
          S ⟨slots[i], hs⟩ = some B ∧ S' ⟨slots[i], hs⟩ = some B' ∧
          BunAgree B' (initBundleFor cs ord B.edges k) ∧
          ExportAt st'.mem (h + 4 * i) o.value B'.graph) ∧
        h + 4 * slots.length ≤ o.value ∧ o.value ≤ h + space (cs.G.m + slots.length) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ rep.foot tbl x a → ¬ tour.foot tourH tx a → st'.mem a = mem a) ∧
        (∀ a, rep.foot tbl x' a → rep.foot tbl x a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ a, tour.foot tourH tx' a → tour.foot tourH tx a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ a, rep.foot tbl x' a → ¬ tour.foot tourH tx' a) ∧
        c + rep.phi tbl x' st'.mem + tour.phi tourH tx' st'.mem ≤
          mul * (cs.G.m + slots.length + 1) * ordStoreLog eCap +
            rep.phi tbl x mem + tour.phi tourH tx mem

/-! ## The data that a restart rebuilds: `S_cur` (kept by P10) -/

/-- What the sparsified-core piece keeps of a branch: the graph `S` (the field `S_cur`), and the
data from which a restart rebuilds it: its vertices `V` (the roots `cs.RF.R`), the ends `tail`,
`head` of the core graph, and the set `X` of edges that are not spanner edges (the non-forest
edges of the active components outside the bundle graphs, and the cross edges). -/
structure ScurView where
  V : Finset ℕ
  tail : ℕ → ℕ
  head : ℕ → ℕ
  X : Finset ℕ
  S : MGraph

/-- The view after a rebuild with spanner edges `E`: `S` has the vertices `V`, the edges
`E ∪ X` and the ends `tail`, `head` (`restartBundleTree`). -/
def ScurView.rebuild (v : ScurView) (E : Finset ℕ) : ScurView :=
  { v with S := { V := v.V, E := E ∪ v.X, tail := v.tail, head := v.head } }

/-- The edges of the spanner `H` of slot `s` of a bucket spanner table (empty if the slot is
empty). -/
noncomputable def slotHE (P : DSParams) {cap : ℕ} (S : BucketSpannerState cap) (s : ℕ) :
    Finset ℕ :=
  if hs : s < cap then
    match S ⟨s, hs⟩ with
    | some d => (d.state P).H.E
    | none => ∅
  else ∅

/-- The union of the spanner edges of the listed slots. -/
noncomputable def slotsHE (P : DSParams) {cap : ℕ} (S : BucketSpannerState cap)
    (slots : List ℕ) : Finset ℕ :=
  slots.toFinset.biUnion (slotHE P S)

/-- **Interface of the rebuild of the branch data after a restart (piece
P10).** The piece keeps branch data of some type `α` (at least `S_cur`; P10 also
keeps the LSF view and the stretch tables) and queries the roots of branch `j` through P4's
representation `rep4 : DSRep σ4` (at handle `b4`, query cost `rootCost`, root condition
`rootsOK v s4 j`). `rebuild v S6 slots` is the data after the restart, from the old data `v` and
the new bucket spanner table `S6`; `size v S6 slots` is the word count the rebuild may pay for.
Procedure `f` of `p`, called as `[scurH, spanTbl, n, slotsPtr, b4, j, h]` with the listed slots of
`S6` active and `rootsOK v s4 j`, leaves `rebuild v S6 slots` and keeps `s4`. It writes below `h`
only to its own footprint and P4's footprint (it only reads the spanners). It costs at most
`(mul + 2 * rootCost) · (size + n + 1) · ordStoreLog eCap`. For `S_cur` alone, `scurViewRebuild`
and `scurViewSize` are the intended `rebuild` and `size`. -/
structure ScurRebuildAt (P : DSParams) (cap : ℕ) (p : Program) (f : ℕ) where
  α : Type
  rebuild : α → BucketSpannerState cap → List ℕ → α
  size : α → BucketSpannerState cap → List ℕ → ℕ
  rep : DSRep α
  mul : ℕ
  space : ℕ → ℕ
  rep_local : rep.Local
  σ4 : Type
  rep4 : DSRep σ4
  rep4_local : rep4.Local
  rootCost : ℕ
  rootsOK : α → σ4 → ℕ → Prop
  runs : ∀ (scurH spanTbl slotsPtr h b4 j : ℕ) (slots : List ℕ) (v : α) (y : rep.τ)
      (S6 : BucketSpannerState cap) (x6 : (bucketSpannerRep P cap).τ) (s4 : σ4) (x4 : rep4.τ)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      scurH < 2 ^ P.w → spanTbl < 2 ^ P.w → slots.length < 2 ^ P.w → slotsPtr < 2 ^ P.w →
      b4 < 2 ^ P.w → j < 2 ^ P.w → h < 2 ^ P.w →
      ListAt mem slotsPtr slots → slotsPtr + slots.length ≤ h →
      (∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome) →
      rep.rep scurH v y mem → (bucketSpannerRep P cap).rep spanTbl S6 x6 mem →
      rep4.rep b4 s4 x4 mem → rootsOK v s4 j →
      (∀ a, rep.foot scurH y a → a < h) →
      (∀ a, (bucketSpannerRep P cap).foot spanTbl x6 a → a < h) →
      (∀ a, rep4.foot b4 x4 a → a < h) →
      (∀ a, rep.foot scurH y a → ¬ (bucketSpannerRep P cap).foot spanTbl x6 a) →
      (∀ a, rep.foot scurH y a → ¬ rep4.foot b4 x4 a) →
      (∀ a, (bucketSpannerRep P cap).foot spanTbl x6 a → ¬ rep4.foot b4 x4 a) →
      (∀ a, slotsPtr ≤ a → a < slotsPtr + slots.length → ¬ rep.foot scurH y a) →
      ZeroFrom mem h → h + space (size v S6 slots + slots.length) < 2 ^ P.w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c y' x4',
        Runs P.w p ω body
          (startState [scurH, spanTbl, slots.length, slotsPtr, b4, j, h] mem pos) o st' c ∧
        rep.rep scurH (rebuild v S6 slots) y' st'.mem ∧
        rep4.rep b4 s4 x4' st'.mem ∧
        h ≤ o.value ∧ o.value ≤ h + space (size v S6 slots + slots.length) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ rep.foot scurH y a → ¬ rep4.foot b4 x4 a → st'.mem a = mem a) ∧
        (∀ a, rep.foot scurH y' a → rep.foot scurH y a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ a, rep4.foot b4 x4' a → rep4.foot b4 x4 a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ a, rep.foot scurH y' a → ¬ rep4.foot b4 x4' a) ∧
        c + rep.phi scurH y' st'.mem + rep4.phi b4 x4' st'.mem ≤
          (mul + 2 * rootCost) * (size v S6 slots + slots.length + 1) * ordStoreLog P.eCap +
            rep.phi scurH y mem + rep4.phi b4 x4 mem


/-- The rebuild of `S_cur` alone, as `restartBundleTree` does it: the spanner edges of the listed
slots together with `X`. -/
noncomputable def scurViewRebuild (P : DSParams) {cap : ℕ} (v : ScurView)
    (S6 : BucketSpannerState cap) (slots : List ℕ) : ScurView :=
  v.rebuild (slotsHE P S6 slots)

/-- The word count of the rebuild of `S_cur` alone: the old and the new edges. -/
noncomputable def scurViewSize (P : DSParams) {cap : ℕ} (v : ScurView)
    (S6 : BucketSpannerState cap) (slots : List ℕ) : ℕ :=
  v.S.m + v.X.card + (slots.map fun s => (slotHE P S6 s).card).sum

/-! ## The program -/

/-- The arguments of the call of operation `0` of the bucket spanners in round `i` (register
`14`) of the loop: the spanner table (register `2`), the slot `mem[slotsPtr + i]`, the level
count `L` (register `12`), the instance parameters `splitBound`, `vCap`, `eCap` (registers `9`,
`10`, `11`), the descriptor `mem[h + 4 i .. h + 4 i + 3]` and the heap pointer (register `13`). -/
def restartLoopArgs : List Expr :=
  [.reg 2, .load (.bin .add (.reg 5) (.reg 14)), .reg 12, .reg 9, .reg 10, .reg 11,
    .load (.bin .add (.reg 6) (.bin .mul (.const 4) (.reg 14))),
    .load (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 4) (.reg 14))) (.const 1)),
    .load (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 4) (.reg 14))) (.const 2)),
    .load (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 4) (.reg 14))) (.const 3)),
    .reg 13]

/-- One round of the loop of `restartBranchStmt`: operation `0` of the bucket spanners. -/
def restartLoopBody (fAct : ℕ) : Stmt :=
  .call 13 fAct restartLoopArgs

/-- The restart of a branch, `args = [bunTbl, tourH, spanTbl, scurH, n, slotsPtr, h, b4, j,
splitBound, vCap, eCap, L]`:
1. call the bundle restart (`fBun`) on the `n` slots listed at `slotsPtr`, which writes the
   descriptors of the new bundle graphs at `h, h + 4, …` and returns the heap pointer in
   register `13`;
2. for each `i < n`, call operation `0` of the bucket spanners (`fAct`) on slot `slots[i]` with
   the graph of descriptor `i`, the level count `L` (register `12`), and `splitBound`, `vCap`,
   `eCap` from registers `9`, `10`, `11`;
3. call the rebuild of `S_cur` (`fScur`) with P4's handle `b4` and branch number `j`, and return
   the heap pointer.
All spanner parameters (`L`, `splitBound`, `vCap`, `eCap`) are passed at run time in registers. -/
def restartBranchStmt (fBun fAct fScur : ℕ) : Stmt :=
  .call 13 fBun [.reg 0, .reg 1, .reg 4, .reg 5, .reg 6] ;;
  forRange 14 (.const 0) (.reg 4) (restartLoopBody fAct) ;;
  .call 13 fScur [.reg 3, .reg 2, .reg 4, .reg 5, .reg 7, .reg 8, .reg 13] ;;
  .ret (.reg 13)

/-! ## Costs, space and the conditions of a spanner initialization -/

/-- The cost bound of operation `0` of `bucketSpannerDS P` on the graph `G`: the phase base, the
initialization of `dynSpannerDS` (`dsInitContract`) and its first potential `dsInitBank`, and the
wrapper. -/
noncomputable def spanActivateCost (P : DSParams) (G : MGraph) : ℕ :=
  phaseBaseCost (G.n + P.splitBound) P.L +
    (dsInitCoreCost P.impl P.mMax G + 140 * G.n + 500 * G.m + 420 + dsInitBank P G) + 35

/-- The space bound of operation `0` of `bucketSpannerDS P` on the graph `G`. -/
noncomputable def spanActivateSpace (P : DSParams) (G : MGraph) : ℕ :=
  dsFixedSize P.L P.vCap P.eCap + dsInitCoreSpaceBound P.impl P.mMax P.vCap P.eCap G

/-- The conditions of a spanner initialization on `G` that do not concern memory: those of
`dsInitContract` and of `BucketActivatePre` on the graph and the word size. -/
def SpanGraphOK (P : DSParams) (G : MGraph) : Prop :=
  1 ≤ P.L ∧ 1 ≤ max P.impl.p_s P.impl.p_t ∧ 16 ≤ 2 ^ P.w ∧
    G.n + P.splitBound + 2 < 2 ^ P.w ∧ 1 + G.m < 2 ^ P.w ∧
    (G.E.Nonempty →
      wordSize P.impl.cw (canonSparsifyInput (activeSubgraph G) (activeSubgraph G) idEmb) ≤
        P.w) ∧
    G.IsValid ∧ G.m ≤ P.mMax ∧ (∀ v ∈ G.V, v < P.vCap) ∧ (∀ e ∈ G.E, e < P.eCap)

/-- The new bundle state of slot `i` that the bundle piece must produce: `initBundleFor` on the
edges of the old bundles of the slot. -/
noncomputable def restartSlotBundle {slotCap : ℕ} (S : Fin slotCap → Option BundleState)
    (cs : CompLSFState) (ord : ℕ → List End) (k s : ℕ) : BundleState :=
  if hs : s < slotCap then
    match S ⟨s, hs⟩ with
    | some B => initBundleFor cs ord B.edges k
    | none => ⟨∅, ∅, fun _ => 0, fun _ => 0⟩
  else ⟨∅, ∅, fun _ => 0, fun _ => 0⟩

/-- The graph on which the spanner of slot `s` is initialized. -/
noncomputable def restartSlotGraph {slotCap : ℕ} (S : Fin slotCap → Option BundleState)
    (cs : CompLSFState) (ord : ℕ → List End) (k s : ℕ) : MGraph :=
  normGraph (restartSlotBundle S cs ord k s).graph

/-- The bucket spanner table after the restart: every listed slot holds a fresh spanner on its
new graph. -/
noncomputable def restartSpanState {slotCap cap : ℕ} (S6 : BucketSpannerState cap)
    (S : Fin slotCap → Option BundleState) (cs : CompLSFState) (ord : ℕ → List End) (k : ℕ)
    (slots : List ℕ) : BucketSpannerState cap :=
  fun j => if j.1 ∈ slots then some ⟨restartSlotGraph S cs ord k j.1, []⟩ else S6 j

/-! ## The statement -/

/-- The footprints of the four states that a restart touches are pairwise disjoint. -/
def FeetDisjoint (f₁ f₂ f₃ f₄ : ℕ → Prop) : Prop :=
  (∀ a, f₁ a → ¬ f₂ a) ∧ (∀ a, f₁ a → ¬ f₃ a) ∧ (∀ a, f₁ a → ¬ f₄ a) ∧
    (∀ a, f₂ a → ¬ f₃ a) ∧ (∀ a, f₂ a → ¬ f₄ a) ∧ (∀ a, f₃ a → ¬ f₄ a)

/-- **What a restart of a branch does** (`restartBranch_runs`, `RestartMain.lean`). Let the
program `p` hold `restartBranchStmt` at `f`, the bucket spanner procedures at `bSpan`, and the two
interfaced procedures `fBun` and `fScur`. Call it as
`[bunTbl, tourH, spanTbl, scurH, n, slotsPtr, h, b4, j, P.splitBound, P.vCap, P.eCap]` with the `n`
distinct slots `slots` at `slotsPtr`, where the bundle table `S`, the tour `cord` (the core
rotation of `cs` and `ord`), the bucket spanners `S6`, the branch data `v` of P10, and P4's state
`s4` (satisfying `I7.rootsOK v s4 j`) are in memory below `h` with disjoint footprints (and apart
from the slot list), every listed slot is active in `S` and in `S6`, the invariant `I5.inv S cord`
of the bundle piece holds, and the graph of each new slot meets `SpanGraphOK`. Then the run ends
with:
* the bundle table holding the new bundles of the listed slots (up to `BunAgree`), and the old
  bundles of the other slots, with `I5.inv` again;
* the bucket spanners `restartSpanState`: a fresh spanner on `restartSlotGraph` in each listed
  slot;
* the branch data of P10 rebuilt from the new spanners (`I7.rebuild`), and P4's state `s4` kept;
* the tour unchanged, the four branch footprints pairwise disjoint and all four disjoint from P4's
  footprint, and memory below `h` outside all five footprints unchanged;
* cost plus the new potentials at most the bound below plus the old potentials: the two
  interface bounds, `spanActivateCost` for each slot, and `200` per slot and `200` in all for the
  calls and the loop. -/
def RestartBranchSpec {slotCap eCap k : ℕ} (P : DSParams) (cap : ℕ) (p : Program)
    (f fBun bSpan fScur : ℕ) (I5 : BunRestartAt P.w slotCap eCap k p fBun)
    (I7 : ScurRebuildAt P cap p fScur) : Prop :=
  ∀ (bunTbl tourH spanTbl scurH slotsPtr h b4 j : ℕ) (slots : List ℕ)
    (S : Fin slotCap → Option BundleState) (x : I5.rep.τ) (cord : ℕ → List End) (tx : I5.tour.τ)
    (S6 : BucketSpannerState cap) (x6 : (bucketSpannerRep P cap).τ) (v : I7.α)
    (y : I7.rep.τ) (s4 : I7.σ4) (x4 : I7.rep4.τ) (cs : CompLSFState) (ord : ℕ → List End)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (spaceBound : ℕ),
    p.procs[f]? = some (restartBranchStmt fBun (bSpan + bsIdxOp0 + 0) fScur) →
    p.HasAt bSpan (bucketSpannerProcs P.impl bSpan) →
    bunTbl < 2 ^ P.w → tourH < 2 ^ P.w → spanTbl < 2 ^ P.w → scurH < 2 ^ P.w →
    slotsPtr < 2 ^ P.w → h < 2 ^ P.w → b4 < 2 ^ P.w → j < 2 ^ P.w →
    P.L < 2 ^ P.w → P.splitBound < 2 ^ P.w →
    P.vCap < 2 ^ P.w → P.eCap < 2 ^ P.w → 16 ≤ 2 ^ P.w →
    ListAt mem slotsPtr slots → slotsPtr + slots.length ≤ h → slots.Nodup →
    (∀ a, slotsPtr ≤ a → a < slotsPtr + slots.length →
      ¬ I5.rep.foot bunTbl x a ∧ ¬ I5.tour.foot tourH tx a ∧
        ¬ (bucketSpannerRep P cap).foot spanTbl x6 a ∧ ¬ I7.rep.foot scurH y a) →
    (∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B ∧
      B.edges ⊆ (coreGraph cs.G cs.lsf).E) →
    (∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome) →
    (∀ s ∈ slots, SpanGraphOK P (restartSlotGraph S cs ord k s)) →
    1 ≤ k → CoreCordOf cs ord cord → I5.inv S cord →
    I5.rep.rep bunTbl S x mem → I5.tour.rep tourH cord tx mem →
    (bucketSpannerRep P cap).rep spanTbl S6 x6 mem → I7.rep.rep scurH v y mem →
    I7.rep4.rep b4 s4 x4 mem → I7.rootsOK v s4 j →
    FeetDisjoint (I5.rep.foot bunTbl x) (I5.tour.foot tourH tx)
      ((bucketSpannerRep P cap).foot spanTbl x6) (I7.rep.foot scurH y) →
    (∀ a, I5.rep.foot bunTbl x a → ¬ I7.rep4.foot b4 x4 a) →
    (∀ a, I5.tour.foot tourH tx a → ¬ I7.rep4.foot b4 x4 a) →
    (∀ a, (bucketSpannerRep P cap).foot spanTbl x6 a → ¬ I7.rep4.foot b4 x4 a) →
    (∀ a, I7.rep.foot scurH y a → ¬ I7.rep4.foot b4 x4 a) →
    (∀ a, I5.rep.foot bunTbl x a → a < h) → (∀ a, I5.tour.foot tourH tx a → a < h) →
    (∀ a, (bucketSpannerRep P cap).foot spanTbl x6 a → a < h) →
    (∀ a, I7.rep.foot scurH y a → a < h) → (∀ a, I7.rep4.foot b4 x4 a → a < h) →
    ZeroFrom mem h →
    I5.space (cs.G.m + slots.length) +
        (slots.map fun s => spanActivateSpace P (restartSlotGraph S cs ord k s)).sum +
        I7.space (I7.size v (restartSpanState S6 S cs ord k slots) slots + slots.length) ≤
      spaceBound →
    h + spaceBound < 2 ^ P.w →
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' c S' x' tx' x6' y' x4',
      Runs P.w p ω body
        (startState [bunTbl, tourH, spanTbl, scurH, slots.length, slotsPtr, h, b4, j,
          P.splitBound, P.vCap, P.eCap, P.L] mem pos)
        o st' c ∧
      I5.rep.rep bunTbl S' x' st'.mem ∧ I5.tour.rep tourH cord tx' st'.mem ∧ I5.inv S' cord ∧
      (bucketSpannerRep P cap).rep spanTbl (restartSpanState S6 S cs ord k slots) x6' st'.mem ∧
      I7.rep.rep scurH (I7.rebuild v (restartSpanState S6 S cs ord k slots) slots) y' st'.mem ∧
      I7.rep4.rep b4 s4 x4' st'.mem ∧
      (∀ i : Fin slotCap, i.1 ∉ slots → S' i = S i) ∧
      (∀ s ∈ slots, ∃ (hs : s < slotCap) (B' : BundleState), S' ⟨s, hs⟩ = some B' ∧
        BunAgree B' (restartSlotBundle S cs ord k s)) ∧
      h ≤ o.value ∧ o.value ≤ h + spaceBound ∧ ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ I5.rep.foot bunTbl x a → ¬ I5.tour.foot tourH tx a →
        ¬ (bucketSpannerRep P cap).foot spanTbl x6 a → ¬ I7.rep.foot scurH y a →
        ¬ I7.rep4.foot b4 x4 a → st'.mem a = mem a) ∧
      (∀ a, I5.rep.foot bunTbl x' a → I5.rep.foot bunTbl x a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a, I5.tour.foot tourH tx' a → I5.tour.foot tourH tx a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a, (bucketSpannerRep P cap).foot spanTbl x6' a →
        (bucketSpannerRep P cap).foot spanTbl x6 a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a, I7.rep.foot scurH y' a → I7.rep.foot scurH y a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a, I7.rep4.foot b4 x4' a → I7.rep4.foot b4 x4 a ∨ (h ≤ a ∧ a < o.value)) ∧
      FeetDisjoint (I5.rep.foot bunTbl x') (I5.tour.foot tourH tx')
        ((bucketSpannerRep P cap).foot spanTbl x6') (I7.rep.foot scurH y') ∧
      (∀ a, I5.rep.foot bunTbl x' a → ¬ I7.rep4.foot b4 x4' a) ∧
      (∀ a, I5.tour.foot tourH tx' a → ¬ I7.rep4.foot b4 x4' a) ∧
      (∀ a, (bucketSpannerRep P cap).foot spanTbl x6' a → ¬ I7.rep4.foot b4 x4' a) ∧
      (∀ a, I7.rep.foot scurH y' a → ¬ I7.rep4.foot b4 x4' a) ∧
      c + I5.rep.phi bunTbl x' st'.mem + I5.tour.phi tourH tx' st'.mem +
          (bucketSpannerRep P cap).phi spanTbl x6' st'.mem + I7.rep.phi scurH y' st'.mem +
          I7.rep4.phi b4 x4' st'.mem ≤
        I5.mul * (cs.G.m + slots.length + 1) * ordStoreLog eCap +
          (slots.map fun s => spanActivateCost P (restartSlotGraph S cs ord k s)).sum +
          (I7.mul + 2 * I7.rootCost) *
            (I7.size v (restartSpanState S6 S cs ord k slots) slots + slots.length + 1) *
            ordStoreLog P.eCap +
          200 * slots.length + 200 +
          (I5.rep.phi bunTbl x mem + I5.tour.phi tourH tx mem +
            (bucketSpannerRep P cap).phi spanTbl x6 mem + I7.rep.phi scurH y mem +
            I7.rep4.phi b4 x4 mem)

end

end MinCostFlow.SparseCore.Program.Restart
