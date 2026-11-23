module

public import MinCostFlow.SparseCore.Program.RestartIface
public import MinCostFlow.SparseCore.Program.BundleLayout
public import MinCostFlow.SparseCore.Program.BundleCapHeadroomDefs

/-!
# The restart of the bundles: the interface proved here (`BunRestartIface`)

The restart of a branch (`restartBranchStmt`, `RestartIface.lean`) calls the bundle piece (P5)
through the interface `BunRestartAt`. P5's `BunRestartAtK` matches `BunRestartAt` with an invariant
`inv` between the table and the tour:

1. The bundle cap `k` is stored in the fixed table block (`btBunCapAddr`), written once when the
   table is initialized and read at run time by `bundleInitSlotsStmt` and `bunRestartStmt`. The
   table representation `rep` is indexed by `k`, and `runs` quantifies over `k` with a single
   fixed program `p` for every `k`.
2. P5's initialization of slots (`bundleInitSlots_runs`) needs that every bundle of the table lies
   in the tour list of its parent (`BundleTableCordMatch`), and the tour query of an owner needs
   the core vertices below `vCap`. The interface carries this invariant `inv S cord` as a pre and
   a post of the run.

The file also gives P5's representation of the table (`bunTableRep slotCap vCap eCap k`:
`BundleTableRepAt` together with `mem (btBunCapAddr tbl slotCap eCap) = k`, footprint
`bundleTableFoot`, and potential `bunPhiMul` per bundle vertex) and P5's invariant
(`bunRestartInv`).
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

@[expose] public section

/-- **The bundle restart, with an invariant between the table and the tour.** The bundle cap `k`
is stored in the fixed table block and read at run time; `rep k` is the table representation for
bundle cap `k`, and `runs` quantifies over `k` with a single fixed program. Procedure `f` of `p`,
called as `[tbl, tourH, n, slotsPtr, h]` on a bundle table `S` and a tour holding `cord`, with the
`n` distinct slots `slots` listed at `slotsPtr`:
* replaces the bundles of every listed slot by `initBundleFor cs ord B.edges k` (up to
  `BunAgree`), keeping the edges `B.edges`, and leaves the other slots;
* writes at `h + 4 i` the descriptor of the graph of the new bundles of slot `i` (`ExportAt`);
* costs at most `mul · (m + n + 1) · ordStoreLog eCap` with `m = cs.G.m`, amortized against the
  potentials of the table and of the tour. -/
structure BunRestartAtK (w slotCap eCap : ℕ) (p : Program) (f : ℕ) where
  rep : ℕ → DSRep (Fin slotCap → Option BundleState)
  tour : DSRep (ℕ → List End)
  inv : (Fin slotCap → Option BundleState) → (ℕ → List End) → Prop
  mul : ℕ
  space : ℕ → ℕ
  rep_local : ∀ k, (rep k).Local
  tour_local : tour.Local
  runs : ∀ (k tbl tourH slotsPtr h : ℕ) (slots : List ℕ) (S : Fin slotCap → Option BundleState)
      (x : (rep k).τ) (cord : ℕ → List End) (tx : tour.τ) (cs : CompLSFState) (ord : ℕ → List End)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      tbl < 2 ^ w → tourH < 2 ^ w → slots.length < 2 ^ w → slotsPtr < 2 ^ w → h < 2 ^ w →
      ListAt mem slotsPtr slots → slotsPtr + slots.length ≤ h → slots.Nodup →
      (∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B ∧
        B.edges ⊆ (coreGraph cs.G cs.lsf).E) →
      1 ≤ k → CoreCordOf cs ord cord → inv S cord →
      (rep k).rep tbl S x mem → tour.rep tourH cord tx mem →
      (∀ a, (rep k).foot tbl x a → a < h) → (∀ a, tour.foot tourH tx a → a < h) →
      (∀ a, (rep k).foot tbl x a → ¬ tour.foot tourH tx a) →
      ZeroFrom mem h → h + space (cs.G.m + slots.length) < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c S' x' tx',
        Runs w p ω body (startState [tbl, tourH, slots.length, slotsPtr, h] mem pos) o st' c ∧
        (rep k).rep tbl S' x' st'.mem ∧ tour.rep tourH cord tx' st'.mem ∧ inv S' cord ∧
        (∀ j : Fin slotCap, j.1 ∉ slots → S' j = S j) ∧
        (∀ i (hi : i < slots.length), ∃ (hs : slots[i] < slotCap) (B B' : BundleState),
          S ⟨slots[i], hs⟩ = some B ∧ S' ⟨slots[i], hs⟩ = some B' ∧
          BunAgree B' (initBundleFor cs ord B.edges k) ∧
          ExportAt st'.mem (h + 4 * i) o.value B'.graph) ∧
        h + 4 * slots.length ≤ o.value ∧ o.value ≤ h + space (cs.G.m + slots.length) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ (rep k).foot tbl x a → ¬ tour.foot tourH tx a → st'.mem a = mem a) ∧
        (∀ a, (rep k).foot tbl x' a → (rep k).foot tbl x a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ a, tour.foot tourH tx' a → tour.foot tourH tx a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ a, (rep k).foot tbl x' a → ¬ tour.foot tourH tx' a) ∧
        c + (rep k).phi tbl x' st'.mem + tour.phi tourH tx' st'.mem ≤
          mul * (cs.G.m + slots.length + 1) * ordStoreLog eCap +
            (rep k).phi tbl x mem + tour.phi tourH tx mem

/-! ## P5's representation of the table -/

/-- The potential paid per bundle vertex of an active slot. A restart walks every bundle of the
listed slots, also the empty ones; this potential pays for that walk. -/
def bunPhiMul : ℕ := 300

/-- The bundle count `nB` stored in the block of slot `j` (`0` for an inactive slot). -/
def bunBlockNB {slotCap : ℕ} (m : BundleTableMeta slotCap) (mem : ℕ → ℕ) (j : Fin slotCap) : ℕ :=
  match m.slotBlocks j with
  | some pb => mem (pb.1 + 1)
  | none => 0

/-- The bundle count of the abstract slot `j` (`0` for an inactive slot). -/
def bunSlotNB {slotCap : ℕ} (S : Fin slotCap → Option BundleState) (j : Fin slotCap) : ℕ :=
  match S j with
  | some B => B.vertices.card
  | none => 0

/-- **P5's representation of a bundle table** (`BundleLayout.lean`): the concrete state is the
block metadata, the representation is `BundleTableRepAt` together with the bundle cap `k` stored at
`btBunCapAddr`, the footprint is `bundleTableFoot`, and the potential is `bunPhiMul` times the
number of bundle vertices of all active slots. -/
def bunTableRep (slotCap vCap eCap k : ℕ) : DSRep (Fin slotCap → Option BundleState) where
  τ := BundleTableMeta slotCap
  rep tbl S m mem := BundleTableRepAt slotCap vCap eCap tbl S m mem ∧
    mem (btBunCapAddr tbl slotCap eCap) = k
  phi _ m mem := bunPhiMul * ∑ j, bunBlockNB m mem j
  foot tbl m a := bundleTableFoot eCap tbl m a

/-- **P5's representation of a bundle table with the slot-block headroom invariant**: extends
`bunTableRep` with `bunTableHeadroomInv S m`, ensuring every active slot block has room for all
future deletions and splits (discharging `hcap_ok` of `bundleStep`). -/
def bunTableHeadroomRep (slotCap vCap eCap k : ℕ) : DSRep (Fin slotCap → Option BundleState) where
  τ := BundleTableMeta slotCap
  rep tbl S m mem := BundleTableRepAt slotCap vCap eCap tbl S m mem ∧
    mem (btBunCapAddr tbl slotCap eCap) = k ∧
    bunTableHeadroomInv S m
  phi _ m mem := bunPhiMul * ∑ j, bunBlockNB m mem j
  foot tbl m a := bundleTableFoot eCap tbl m a

/-- **P5's invariant between its table and the tour.** Every bundle of the table lies in the tour
list of its parent, which is below `vCap` (`BundleTableCordMatch`), and every end in a tour list
belongs to an edge below `eCap` and sits at a vertex below `vCap`. -/
def bunRestartInv {slotCap : ℕ} (vCap eCap : ℕ) (S : Fin slotCap → Option BundleState)
    (cord : ℕ → List End) : Prop :=
  BundleTableCordMatch vCap S cord ∧ ∀ v x, x ∈ cord v → v < vCap ∧ x.1 < eCap

end

public section

/-- The representation of the table depends only on its footprint, and so does its potential. -/
theorem bunTableRep_local (slotCap vCap eCap k : ℕ) : (bunTableRep slotCap vCap eCap k).Local := by
  intro tbl S m mem mem' hag
  refine ⟨fun ⟨hrep, hk⟩ => ⟨BundleTableRepAt.of_agree hrep hag,
    (hag _ (btBunCap_in_foot (m := m))).symm.trans hk⟩, ?_⟩
  show bunPhiMul * ∑ j, bunBlockNB m mem j = bunPhiMul * ∑ j, bunBlockNB m mem' j
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold bunBlockNB
  rcases hm : m.slotBlocks j with _ | ⟨p, c⟩
  · rfl
  · exact hag _ (bsAddr_in_foot (j := j) hm (by unfold bundleSlotBlockSize; omega))

/-- Where the table is represented, the stored bundle count of a slot is its number of bundle
vertices. -/
theorem bunBlockNB_eq {slotCap vCap eCap tbl : ℕ} {S : Fin slotCap → Option BundleState}
    {m : BundleTableMeta slotCap} {mem : ℕ → ℕ}
    (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem) (j : Fin slotCap) :
    bunBlockNB m mem j = bunSlotNB S j := by
  have hslot := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j
  unfold bunBlockNB bunSlotNB
  rcases hS : S j with _ | B <;> rcases hm : m.slotBlocks j with _ | ⟨p, c⟩ <;>
    simp only [hS, hm] at hslot ⊢
  all_goals first
    | exact hslot.elim
    | (obtain ⟨nB, hV, -, -, -, -, -, h1, -⟩ := hslot.2.1
       rw [hV, Finset.card_range]
       exact h1)

/-- The potential of the table is that of its abstract state. -/
theorem bunTablePhi_eq {slotCap vCap eCap k tbl : ℕ} {S : Fin slotCap → Option BundleState}
    {m : BundleTableMeta slotCap} {mem : ℕ → ℕ}
    (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem) :
    (bunTableRep slotCap vCap eCap k).phi tbl m mem = bunPhiMul * ∑ j, bunSlotNB S j := by
  show bunPhiMul * ∑ j, bunBlockNB m mem j = _
  rw [Finset.sum_congr rfl fun j _ => bunBlockNB_eq hrep j]

/-- `bunTableHeadroomRep` depends only on its footprint, and so does its potential. -/
theorem bunTableHeadroomRep_local (slotCap vCap eCap k : ℕ) :
    (bunTableHeadroomRep slotCap vCap eCap k).Local := by
  intro tbl S m mem mem' hag
  have hloc := bunTableRep_local slotCap vCap eCap k tbl S m mem mem' hag
  exact ⟨fun ⟨hrep, hk, hh⟩ => ⟨BundleTableRepAt.of_agree hrep hag,
    (hag _ (btBunCap_in_foot (m := m))).symm.trans hk, hh⟩, hloc.2⟩

/-- The potential of `bunTableHeadroomRep` equals that of `bunTableRep`. -/
theorem bunTableHeadroomPhi_eq {slotCap vCap eCap k tbl : ℕ} {S : Fin slotCap → Option BundleState}
    {m : BundleTableMeta slotCap} {mem : ℕ → ℕ}
    (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem) :
    (bunTableHeadroomRep slotCap vCap eCap k).phi tbl m mem = bunPhiMul * ∑ j, bunSlotNB S j :=
  bunTablePhi_eq (k := k) hrep

end

end MinCostFlow.SparseCore.Program.Restart
