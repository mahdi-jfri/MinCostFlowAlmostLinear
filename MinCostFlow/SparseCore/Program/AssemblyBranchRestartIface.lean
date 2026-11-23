module

public import MinCostFlow.SparseCore.Program.AssemblyBranchSide
public import MinCostFlow.SparseCore.Program.OutReset

/-!
# The restart of a branch: interfaces and program (`AssemblyBranchRestartIface`)

A restart of branch `j` of the sparse-core program (`restartBundleTree`)
rebuilds its bundles, its bucket spanners and its graph `S_cur`. On the machine, the branch runs
four steps (`asmBrRestartStmt`):
1. the restart of piece P8 (`restartBranchStmt`, `RestartIface.lean`), which calls the bundle
   piece P5, the bucket spanners P6 and the readout data P10, and leaves the new `S_cur` in P10;
2. the reset of piece P7 (`outResetBody`, `OutReset.lean`): the output graph becomes the new
   `S_cur` of P10, and the marks of the tour become its ends;
3. the refresh of the embedding table (readout `4`): every edge of a restarted bundle graph gets
   its walk in the new spanner of its slot (`EmbView.refresh`);
4. return the heap pointer.

This file states what the branch takes from the other pieces, as small
interfaces, and defines the program.
* `cordRepM`: a tour seen as the core lists alone, with the marks `mk` fixed. P5's view of P2's
  tour of the branch is `asmTourCordView T vo vf vc mk`, the core lists of P7's view
  `asmTourView T vo vf vc` (`AssemblyBranchTour.lean`). It is the tour that the bundle piece P5
  reads (`BunRestartAt.tour`).
* `AsmBrBunAt`: the restart of the bundle piece P5 on the bundle tables `B5` of the bundle side
  and on the tour of the branch, with P5's invariant `bunRestartInv`. `AsmBrBunAt.toBR` turns it
  into the interface `BunRestartAt` that P8 takes, with the representations of the branch.
* `embRefreshSize`: the words that a refresh of the embedding table may pay for. The refresh
  itself is `AsmBrEmbRefreshDisjAt` (`EmbRefresh.lean`), which pays for the smaller
  `embRefreshSizeAt`.

It also proves that the memory forms of a graph depend only on its vertices, edges and the ends of
its edges (`dynGraphAt_of_graphEq`, `outGraphRep_of_graphEq`, `readRep_of_graphEq_S`). P10
rebuilds `S_cur` up to `GraphEq` (`readViewRebuild_graphEq_restart_S_cur`), so these lemmas let the
branch keep the model's `S_cur` itself in its representation.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## Graphs that agree on their edges -/

/-- The memory form `DynGraphAt` of a graph depends only on its vertices, its edges and the ends
of its edges. -/
theorem dynGraphAt_of_graphEq {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G G' : MGraph}
    (hG : GraphEq G G') (h : DynGraphAt mem a vCap eCap G) : DynGraphAt mem a vCap eCap G' := by
  obtain ⟨hV, hE, hte⟩ := hG
  have hn : G'.n = G.n := by simp only [MGraph.n, hV]
  have hm : G'.m = G.m := by simp only [MGraph.m, hE]
  obtain ⟨hval, hvlt, helt, h1, h2, h3, h4, hpres, hvL, hext, hint, hepres, heL, hslot, hinc⟩ := h
  refine ⟨?_, ?_, ?_, h1, h2, hn ▸ h3, hm ▸ h4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [← hE] at he
    rw [← (hte e he).1, ← (hte e he).2, ← hV]
    exact hval e he
  · intro v hv; rw [← hV] at hv; exact hvlt v hv
  · intro e he; rw [← hE] at he; exact helt e he
  · intro v hv; rw [hpres v hv, hV]
  · obtain ⟨vL, hlen, hnd, hmem, hL, hpos⟩ := hvL
    exact ⟨vL, hn ▸ hlen, hnd, fun v => (hmem v).trans (by rw [hV]), hL, hpos⟩
  · intro v hv; rw [← hV] at hv ⊢; exact hext v hv
  · intro s hs; rw [← hV] at hs ⊢; exact hint s hs
  · intro e he; rw [hepres e he, hE]
  · obtain ⟨eL, hlen, hnd, hmem, hL, hpos⟩ := heL
    exact ⟨eL, hm ▸ hlen, hnd, fun e => (hmem e).trans (by rw [hE]), hL, hpos⟩
  · intro e he
    rw [← hE] at he
    rw [← (hte e he).1, ← (hte e he).2]
    exact hslot e he
  · obtain ⟨incL, hincL⟩ := hinc
    refine ⟨incL, fun s hs => ?_⟩
    obtain ⟨hdl, hdeg, hiff⟩ := hincL s hs
    exact ⟨hdl, hdeg, fun h => (hiff h).trans (by rw [hE])⟩

/-- The output graph of piece P7 holds every graph that agrees with its graph on the edges. -/
theorem outGraphRep_of_graphEq {vCap eCap outH g : ℕ} {mem : ℕ → ℕ} {G G' : MGraph}
    (hG : GraphEq G G') (h : (outGraphRep vCap eCap).rep outH G g mem) :
    (outGraphRep vCap eCap).rep outH G' g mem :=
  ⟨h.1, h.2.1, dynGraphAt_of_graphEq hG h.2.2⟩

/-- The readout data with its graph `S` replaced by a graph that agrees with it on the edges. -/
def Read.ReadConc.withS (y : ReadConc) (S : MGraph) : ReadConc :=
  { y with view := { y.view with S := S } }

/-- The readout data of piece P10 hold every view whose graph `S` agrees with theirs on the
edges, with the same cells and the same potential. -/
theorem readRep_of_graphEq_S {vCap eCap tCap L_w P r : ℕ} {v : ReadView} {y : ReadConc}
    {mem : ℕ → ℕ} {S : MGraph} (hS : GraphEq v.S S)
    (h : (readRep vCap eCap tCap L_w P).rep r v y mem) :
    (readRep vCap eCap tCap L_w P).rep r { v with S := S } (y.withS S) mem := by
  obtain ⟨hview, hlay, hkeep, hrec, h9, h10, hlive, hfrz⟩ := h
  subst hview
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, hT, hF, hR, hSV, hPr, hSc, hG⟩ := hrec
  exact ⟨rfl, hlay, hkeep, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, hT, hF, hR, hSV, hPr,
    dynGraphAt_of_graphEq hS hSc, hG⟩, h9, h10, hlive, hfrz⟩

/-- The cells of the readout data do not depend on the view. -/
theorem readFoot_withS {vCap eCap tCap L_w r : ℕ} {y : ReadConc} {S : MGraph} {a : ℕ} :
    readFoot vCap eCap tCap L_w r (y.withS S) a ↔ readFoot vCap eCap tCap L_w r y a :=
  Iff.rfl

/-! ## The tour seen by the bundle piece -/

/-- The tour `T` seen as its core lists alone, with the marks fixed to `mk`. The bundle piece P5
and the restart P8 read the tour in this form (`BunRestartAt.tour`). A call that keeps the core
lists in this view also keeps the marks. -/
def cordRepM (T : DSRep OutTourAbs) (mk : Finset End) : DSRep (ℕ → List End) where
  τ := T.τ
  rep b c x mem := T.rep b ⟨c, mk⟩ x mem
  phi := T.phi
  foot := T.foot

theorem cordRepM_local {T : DSRep OutTourAbs} (hT : T.Local) (mk : Finset End) :
    (cordRepM T mk).Local :=
  fun b c x mem mem' hag => hT b ⟨c, mk⟩ x mem mem' hag

/-- **P5's view of P2's tour** for the order `vo`, the forest `vf`, the core lists `vc` and the
marks `mk`: P7's view `asmTourView` seen as core lists alone. -/
def asmTourCordView (T : DSRep AsmTourAbs) (vo : ℕ → List End) (vf : RootedForest)
    (vc : ℕ → List End) (mk : Finset End) : DSRep (ℕ → List End) :=
  cordRepM (asmTourView T vo vf vc) mk

theorem asmTourCordView_local {T : DSRep AsmTourAbs} (hT : T.Local) (vo : ℕ → List End)
    (vf : RootedForest) (vc : ℕ → List End) (mk : Finset End) :
    (asmTourCordView T vo vf vc mk).Local :=
  cordRepM_local (asmTourView_local hT vo vf vc) mk

/-! ## The bundle piece -/

/-- **Interface of the restart of the bundle piece (P5) in a branch.** It is
`BunRestartAt` (`RestartIface.lean`) with the bundle table in the representation
`B5 k slotCap vCap₅ eCap₅` of the bundle side, the tour in P5's view
`asmTourCordView (TR vCap eCap) vo vf vc mk` of P2's tour of the branch, and P5's invariant
`bunRestartInv vCap eCap` between the two, for all caps, orders `vo`, forests `vf`, core lists
`vc` and marks `mk`. The caps of the table are those of the tour. The bundle piece reads the tour
through operations of the tour contract (P2), which keep the order, the forest and the marks, so
one proof gives all of them. The bundle cap `k` is a binder of `runs`, as in P5's `BunRestartAtK`
(`BunRestartIface.lean`): one procedure serves every `k`, and the table `B5 k …` holds `k` in a
word of its own. The heap space is linear in the number of edges and slots, with a factor
`slotCap + 1` (`space_le`), so that the space of the restart of a branch is a polynomial in the
sizes when `slotCap` is. -/
structure AsmBrBunAt (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)) (w : ℕ)
    (p : Program) (f : ℕ) where
  mul : ℕ
  space : ℕ → ℕ → ℕ
  space_le : ∀ slotCap n, space slotCap n ≤ mul * (slotCap + 1) * (n + 1)
  rep_local : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local
  runs : ∀ (k slotCap vCap₅ eCap₅ vCap eCap : ℕ) (vo : ℕ → List End) (vf : RootedForest)
      (vc : ℕ → List End) (mk : Finset End),
      vCap₅ = vCap → eCap₅ = eCap → 2 * eCap < 2 ^ w → vCap ≤ 2 ^ w →
      ∀ (tbl tourH slotsPtr h : ℕ) (slots : List ℕ) (S : Fin slotCap → Option BundleState)
      (x : (B5 k slotCap vCap₅ eCap₅).τ) (cord : ℕ → List End) (tx : (TR vCap eCap).τ)
      (cs : CompLSFState) (ord : ℕ → List End) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      tbl < 2 ^ w → tourH < 2 ^ w → slots.length < 2 ^ w → slotsPtr < 2 ^ w → h < 2 ^ w →
      ListAt mem slotsPtr slots → slotsPtr + slots.length ≤ h → slots.Nodup →
      (∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B ∧
        B.edges ⊆ (coreGraph cs.G cs.lsf).E) →
      1 ≤ k → CoreCordOf cs ord cord → bunRestartInv vCap eCap S cord →
      (B5 k slotCap vCap₅ eCap₅).rep tbl S x mem →
      (asmTourCordView (TR vCap eCap) vo vf vc mk).rep tourH cord tx mem →
      (∀ a, (B5 k slotCap vCap₅ eCap₅).foot tbl x a → a < h) →
      (∀ a, (asmTourCordView (TR vCap eCap) vo vf vc mk).foot tourH tx a → a < h) →
      (∀ a, (B5 k slotCap vCap₅ eCap₅).foot tbl x a →
        ¬ (asmTourCordView (TR vCap eCap) vo vf vc mk).foot tourH tx a) →
      ZeroFrom mem h → h + space slotCap (cs.G.m + slots.length) < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c S' x' tx',
        Runs w p ω body (startState [tbl, tourH, slots.length, slotsPtr, h] mem pos) o st' c ∧
        (B5 k slotCap vCap₅ eCap₅).rep tbl S' x' st'.mem ∧
        (asmTourCordView (TR vCap eCap) vo vf vc mk).rep tourH cord tx' st'.mem ∧
        bunRestartInv vCap eCap S' cord ∧
        (∀ j : Fin slotCap, j.1 ∉ slots → S' j = S j) ∧
        (∀ i (hi : i < slots.length), ∃ (hs : slots[i] < slotCap) (B B' : BundleState),
          S ⟨slots[i], hs⟩ = some B ∧ S' ⟨slots[i], hs⟩ = some B' ∧
          BunAgree B' (initBundleFor cs ord B.edges k) ∧
          ExportAt st'.mem (h + 4 * i) o.value B'.graph) ∧
        h + 4 * slots.length ≤ o.value ∧ o.value ≤ h + space slotCap (cs.G.m + slots.length) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ (B5 k slotCap vCap₅ eCap₅).foot tbl x a →
          ¬ (asmTourCordView (TR vCap eCap) vo vf vc mk).foot tourH tx a → st'.mem a = mem a) ∧
        (∀ a, (B5 k slotCap vCap₅ eCap₅).foot tbl x' a → (B5 k slotCap vCap₅ eCap₅).foot tbl x a ∨
          (h ≤ a ∧ a < o.value)) ∧
        (∀ a, (asmTourCordView (TR vCap eCap) vo vf vc mk).foot tourH tx' a →
          (asmTourCordView (TR vCap eCap) vo vf vc mk).foot tourH tx a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ a, (B5 k slotCap vCap₅ eCap₅).foot tbl x' a →
          ¬ (asmTourCordView (TR vCap eCap) vo vf vc mk).foot tourH tx' a) ∧
        c + (B5 k slotCap vCap₅ eCap₅).phi tbl x' st'.mem +
            (asmTourCordView (TR vCap eCap) vo vf vc mk).phi tourH tx' st'.mem ≤
          mul * (cs.G.m + slots.length + 1) * ordStoreLog eCap₅ +
            (B5 k slotCap vCap₅ eCap₅).phi tbl x mem +
            (asmTourCordView (TR vCap eCap) vo vf vc mk).phi tourH tx mem

/-- The interface `BunRestartAt` of P8 from `AsmBrBunAt`, at the caps of a branch, the order `vo`,
the forest `vf`, the core lists `vc` and the marks `mk`, at the bundle cap `k`: the bundle table
is `B5 k slotCap vCap₅ eCap₅`, the tour is `asmTourCordView (TR vCap eCap) vo vf vc mk`, and the
invariant is `bunRestartInv vCap eCap`. -/
def AsmBrBunAt.toBR {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {w : ℕ}
    {p : Program} {f : ℕ} (J : AsmBrBunAt TR B5 w p f) (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (k slotCap vCap₅ eCap₅ vCap eCap : ℕ) (vo : ℕ → List End) (vf : RootedForest)
    (vc : ℕ → List End) (mk : Finset End) (hv : vCap₅ = vCap) (he : eCap₅ = eCap)
    (heW : 2 * eCap < 2 ^ w) (hvW : vCap ≤ 2 ^ w) : BunRestartAt w slotCap eCap₅ k p f where
  rep := B5 k slotCap vCap₅ eCap₅
  tour := asmTourCordView (TR vCap eCap) vo vf vc mk
  inv := bunRestartInv vCap eCap
  mul := J.mul
  space := J.space slotCap
  rep_local := J.rep_local k slotCap vCap₅ eCap₅
  tour_local := asmTourCordView_local (hTR vCap eCap) vo vf vc mk
  runs := J.runs k slotCap vCap₅ eCap₅ vCap eCap vo vf vc mk hv he heW hvW

/-! ## The refresh of the embedding table -/

/-- The walk that a restart gives to edge `e` of the graph of slot `s`: the edge itself when it is
an edge of the new spanner, and its walk `piTotal` in the spanner otherwise
(`BundleTreeState.emb`). -/
noncomputable def slotWalk (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (s e : ℕ) :
    List (ℕ × Bool) :=
  if hs : s < cap then
    match S6 ⟨s, hs⟩ with
    | some d => if e ∈ (d.state P).H.E then [(e, true)] else piTotal (d.state P) e
    | none => []
  else []

/-- The embedding table after a restart: every edge of the graph of a listed slot gets its walk in
the spanner of that slot (`slotWalk`), and the other edges keep theirs. -/
noncomputable def Read.EmbView.refresh (v : EmbView) (P : DSParams) {cap : ℕ}
    (S6 : BucketSpannerState cap) (slots : List ℕ) : EmbView :=
  open Classical in
  ⟨fun e => if h : ∃ s ∈ slots, e ∈ slotGE P S6 s then slotWalk P S6 h.choose e else v.emb e,
    v.dom ∪ slotsGE P S6 slots⟩

/-- The words that a refresh may pay for: for each listed slot and each edge of its graph, the
words of the new walk and a search over the `L + 1` levels of the spanner, and one per slot. -/
noncomputable def embRefreshSize (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (slots : List ℕ) : ℕ :=
  (slots.map fun s =>
    ((slotGE P S6 s).sum fun e => Read.walkWords (slotWalk P S6 s e) + P.L + 2) + 1).sum

/-! ## The program -/

/-- The word of the record of the readout data of P10 that points to its graph `S`
(`ReadRecAt`). -/
def ASM_READ_S : ℕ := 5

/-- **The restart of a branch**, `[b, b4, j, h]`, with the branch at `b`, the handle `b4` of P4
and the branch number `j`. Registers: `4` the bundle side, `5` the bundle table, `6` the tour,
`7` the spanners, `8` the readout data, `9` the number of slots, `10` the slot list.
1. call the restart of P8 (`f8`) on `[bunTbl, tourH, spanTbl, readH, n, slotsPtr, h, b4, j,
   splitB, spV, spE]`, the last three read from the record of the bundle side;
2. call the reset of P7 (`fReset`) on the output graph, the tour, the graph `S` of P10 and the
   heap pointer;
3. call the refresh of the embedding table (`fEmb`) on the table, the spanners and the slots;
4. return the heap pointer. -/
def asmBrRestartStmt (f8 fReset fEmb : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const ASM_BR_REST))) ;;
  .assign 5 (.load (.bin .add (.reg 4) (.const ASM_SD_BUN))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const ASM_BR_TOUR))) ;;
  .assign 7 (.load (.bin .add (.reg 4) (.const ASM_SD_SPAN))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const ASM_BR_READ))) ;;
  .assign 9 (.load (.bin .add (.reg 4) (.const ASM_SD_NSLOTS))) ;;
  .assign 10 (.load (.bin .add (.reg 4) (.const ASM_SD_SLOTS))) ;;
  .call 11 f8 [.reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 3, .reg 1, .reg 2,
    .load (.bin .add (.reg 4) (.const ASM_SD_SPLIT)),
    .load (.bin .add (.reg 4) (.const ASM_SD_SPV)),
    .load (.bin .add (.reg 4) (.const ASM_SD_SPE)),
    .load (.bin .add (.reg 4) (.const ASM_SD_SPL))] ;;
  .call 12 fReset [.load (.bin .add (.reg 0) (.const ASM_BR_OUT)), .reg 6,
    .load (.bin .add (.reg 8) (.const ASM_READ_S)), .reg 11] ;;
  .call 13 fEmb [.load (.bin .add (.reg 0) (.const ASM_BR_EMB)), .reg 7, .reg 10, .reg 9,
    .reg 12] ;;
  .ret (.reg 13)

/-- The restart of a branch never reads random bits. -/
theorem asmBrRestartStmt_noRand (f8 fReset fEmb : ℕ) :
    (asmBrRestartStmt f8 fReset fEmb).NoRand := by
  simp [asmBrRestartStmt, Stmt.NoRand]

end MinCostFlow.SparseCore.Program
