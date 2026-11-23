module

public import MinCostFlow.SparseCore.Program.BundleLayout

/-!
# Definitions for the bundle slot-block capacity headroom invariant (`BundleCapHeadroomDefs`)

Lightweight definitions module (importing only `BundleLayout`) so `BunRestartIface` and
downstream branch files can state `bunTableHeadroomInv` and `bunTableHeadroomRep` without pulling
`BundleStep*` or `BundleInit*` into their public import closure.

See `BundleCapHeadroom.lean` for all preservation and `hcap_ok`-discharge proofs.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle

@[expose] public section

/-- Number of nonempty bundles of `B : BundleState`. -/
noncomputable def bunNonEmpty (B : BundleState) : ℕ :=
  open Classical in (B.vertices.filter fun b => (B.ends b).Nonempty).card

/-- Deletion- and split-preserved slot-block capacity invariant:
`B.vertices.card + (2 * B.edges.card - bunNonEmpty B) + 2 * B.edges.card ≤ bunCap`.
Holds at `bunCap = 4 * B.edges.card` on initialization/restart, never increases under edge
deletions or bundle splits, and always implies `B.vertices.card + slotCandEndsSum ≤ bunCap`. -/
def bunCapHeadroomInv (B : BundleState) (bunCap : ℕ) : Prop :=
  B.vertices.card + (2 * B.edges.card - bunNonEmpty B) + 2 * B.edges.card ≤ bunCap

/-- Table-level headroom invariant: every active slot `(B, (p, bunCap))` satisfies
`bunCapHeadroomInv B bunCap`. -/
def bunTableHeadroomInv {slotCap : ℕ} (S : BundleTableState slotCap)
    (m : BundleTableMeta slotCap) : Prop :=
  ∀ (j : Fin slotCap) (B : BundleState) (p bunCap : ℕ),
    S j = some B → m.slotBlocks j = some (p, bunCap) → bunCapHeadroomInv B bunCap

end

end MinCostFlow.SparseCore.Program
