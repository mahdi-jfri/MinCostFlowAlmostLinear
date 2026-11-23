module

public import MinCostFlow.SparseCore.Program.BundleModelBridge
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import WordRAM.DataStructure

/-!
# Memory layout and representation invariants for the bundle manager (`BundleLayout`)

Defines the flat Word-RAM memory layout of a branch-level bundle table (`BundleTableRepAt`)
managing up to `slotCap` active `(component, bucket)` `BundleState` slots whose edge sets are
pairwise disjoint:

* **Fixed branch header and shared global arrays** (`bundleTableFixedSize slotCap eCap =
  12 + 4 * slotCap + 8 * eCap` words at handle `tbl`):
  - `12`-word header storing `slotCap`, `vCap`, `eCap`, and the base addresses of all 9 global
    arrays (`slotPtr`, `edgeSlot`, `endBundle`, `endPrev`, `endNext`, `slotTouched`,
    `slotDelHead`, `slotDelNext`, `slotCandHead`).
  - Because every live core edge `e < eCap` belongs to at most one `(component, bucket)` slot,
    `edgeSlot[e]` (`0` = absent, `s + 1` = slot `s`), `endBundle[key]`, and the 1-indexed
    doubly-linked list links `endPrev[key]` / `endNext[key]` are shared across all slots in
    `O(slotCap + eCap)` total space (avoiding any `slotCap * eCap` blowup).
* **Per-slot blocks** (`bundleSlotBlockSize bunCap = 3 + 6 * bunCap` words at `p = slotPtr[s]`):
  - `3`-word header `[bunCap, nB, nE]` followed by 6 arrays of length `bunCap`: `head`, `size`,
    `storedParent`, and three scratch arrays `seen`, `inCand`, `candNext` (kept zero between calls).
  - For every nonempty bundle `b < nB`, its ends are stored in a 1-indexed doubly-linked list
    (`IsDoublyLinkedList`) of `endKey` values at `head[b]` of length `size[b]`, and its parent is
    the unique core vertex containing its ends in the current tour (`BundleTableCordMatch`).
  - For every empty bundle `b < nB`, `storedParent[b] = B.parent b`.

Keeping `BundleTableRepAt` independent of `cord` lets the tour update from `cord` to `cord'`
between calls without invalidating the bundle table's representation invariant.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Branch table offsets and base addresses -/

def btOffSlotCap : ℕ := 0
def btOffVCap : ℕ := 1
def btOffECap : ℕ := 2
def btOffSlotPtr : ℕ := 3
def btOffEdgeSlot : ℕ := 4
def btOffEndBundle : ℕ := 5
def btOffEndPrev : ℕ := 6
def btOffEndNext : ℕ := 7
def btOffSlotTouched : ℕ := 8
def btOffSlotDelHead : ℕ := 9
def btOffSlotDelNext : ℕ := 10
def btOffSlotCandHead : ℕ := 11
def btHdrSize : ℕ := 12

def btSlotPtrBase (tbl : ℕ) : ℕ := tbl + 12
def btEdgeSlotBase (tbl slotCap : ℕ) : ℕ := tbl + 12 + slotCap
def btEndBundleBase (tbl slotCap eCap : ℕ) : ℕ := tbl + 12 + slotCap + eCap
def btEndPrevBase (tbl slotCap eCap : ℕ) : ℕ := tbl + 12 + slotCap + 3 * eCap
def btEndNextBase (tbl slotCap eCap : ℕ) : ℕ := tbl + 12 + slotCap + 5 * eCap
def btSlotTouchedBase (tbl slotCap eCap : ℕ) : ℕ := tbl + 12 + slotCap + 7 * eCap
def btSlotDelHeadBase (tbl slotCap eCap : ℕ) : ℕ := tbl + 12 + 2 * slotCap + 7 * eCap
def btSlotDelNextBase (tbl slotCap eCap : ℕ) : ℕ := tbl + 12 + 3 * slotCap + 7 * eCap
def btSlotCandHeadBase (tbl slotCap eCap : ℕ) : ℕ := tbl + 12 + 3 * slotCap + 8 * eCap

/-- Word size of the core branch table header and original 9 global arrays. -/
def bundleTableCoreSize (slotCap eCap : ℕ) : ℕ := 12 + 4 * slotCap + 8 * eCap

/-- Table-resident scratch arrays for `bundleInitSlotsStmt` (`curBun[slotCap]`, `curTag[slotCap]`,
kept zero between calls) and `bundleStepStmt` (`touchedBuf[slotCap]`, `touchedCnt[1]`), followed by
the bundle cap word `k` (`btBunCapAddr`, written once at table init). -/
def btCurBunBase (tbl slotCap eCap : ℕ) : ℕ := tbl + 12 + 4 * slotCap + 8 * eCap
def btCurTagBase (tbl slotCap eCap : ℕ) : ℕ := tbl + 12 + 5 * slotCap + 8 * eCap
def btTouchedBufBase (tbl slotCap eCap : ℕ) : ℕ := tbl + 12 + 6 * slotCap + 8 * eCap
def btTouchedCntAddr (tbl slotCap eCap : ℕ) : ℕ := tbl + 12 + 7 * slotCap + 8 * eCap
def btBunCapAddr (tbl slotCap eCap : ℕ) : ℕ := tbl + 13 + 7 * slotCap + 8 * eCap

/-- Total word size of the fixed branch table header, shared global arrays, table-resident
scratch arrays (`curBun`, `curTag`, `touchedBuf`, `touchedCnt`), and the bundle cap word `k`. -/
def bundleTableFixedSize (slotCap eCap : ℕ) : ℕ := 14 + 7 * slotCap + 8 * eCap

/-! ## 2. Per-slot block offsets and base addresses -/

def bsOffBunCap : ℕ := 0
def bsOffNB : ℕ := 1
def bsOffNE : ℕ := 2
def bsHdrSize : ℕ := 3

def bsHeadBase (p : ℕ) : ℕ := p + 3
def bsSizeBase (p bunCap : ℕ) : ℕ := p + 3 + bunCap
def bsParentBase (p bunCap : ℕ) : ℕ := p + 3 + 2 * bunCap
def bsSeenBase (p bunCap : ℕ) : ℕ := p + 3 + 3 * bunCap
def bsInCandBase (p bunCap : ℕ) : ℕ := p + 3 + 4 * bunCap
def bsCandNextBase (p bunCap : ℕ) : ℕ := p + 3 + 5 * bunCap

/-- Total word size of one per-slot block with bundle vertex capacity `bunCap`. -/
def bundleSlotBlockSize (bunCap : ℕ) : ℕ := 3 + 6 * bunCap

/-! ## 3. Abstract state, concrete metadata, and footprint -/

/-- Abstract state of a branch bundle manager with `slotCap` slots: each slot holds either `none`
(uninitialized) or `some B` (`B : BundleState`). -/
abbrev BundleTableState (slotCap : ℕ) := Fin slotCap → Option BundleState

/-- Concrete memory metadata: for each slot, either `none` or `(blockPtr, bunCap)`. -/
structure BundleTableMeta (slotCap : ℕ) where
  slotBlocks : Fin slotCap → Option (ℕ × ℕ)

/-- Core footprint of a bundle table: the header + 9 core global arrays
`[tbl, tbl + bundleTableCoreSize)` together with `[p, p + bundleSlotBlockSize bunCap)` for every
active slot block (excluding the table-resident scratch arrays `curBun`, `curTag`, `touchedBuf`,
`touchedCnt`). -/
def bundleTableCoreFoot {slotCap : ℕ} (eCap tbl : ℕ) (m : BundleTableMeta slotCap) (a : ℕ) : Prop :=
  (tbl ≤ a ∧ a < tbl + bundleTableCoreSize slotCap eCap) ∨
  ∃ j : Fin slotCap, ∃ p bunCap,
    m.slotBlocks j = some (p, bunCap) ∧ p ≤ a ∧ a < p + bundleSlotBlockSize bunCap

/-- Footprint of a bundle table: the fixed branch block `[tbl, tbl + bundleTableFixedSize)`
together with `[p, p + bundleSlotBlockSize bunCap)` for every active slot block. -/
def bundleTableFoot {slotCap : ℕ} (eCap tbl : ℕ) (m : BundleTableMeta slotCap) (a : ℕ) : Prop :=
  (tbl ≤ a ∧ a < tbl + bundleTableFixedSize slotCap eCap) ∨
  ∃ j : Fin slotCap, ∃ p bunCap,
    m.slotBlocks j = some (p, bunCap) ∧ p ≤ a ∧ a < p + bundleSlotBlockSize bunCap

/-! ## 4. Representation invariants -/

/-- In-memory representation of one active slot's `BundleState` `B` at block `(p, bunCap)`, using
shared doubly-linked end arrays `(prevBase, nextBase)` of end-key capacity `2 * eCap`. -/
def BundleSlotRepAt (eCap prevBase nextBase p bunCap : ℕ) (B : BundleState) (mem : ℕ → ℕ) : Prop :=
  ∃ nB : ℕ,
    B.vertices = Finset.range nB ∧
    nB ≤ bunCap ∧
    (∀ e ∈ B.edges, e < eCap) ∧
    (∀ x ∈ edgeEnds B.edges, B.bundleOf x < nB) ∧
    (∀ b, nB ≤ b → B.parent b = 0) ∧
    mem (p + bsOffBunCap) = bunCap ∧
    mem (p + bsOffNB) = nB ∧
    mem (p + bsOffNE) = B.edges.card ∧
    (∀ b < nB, ∃ L : List ℕ,
      IsDoublyLinkedList mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) L ∧
      mem (bsSizeBase p bunCap + b) = L.length ∧
      (∀ k, k ∈ L ↔ endOfKey k ∈ B.ends b)) ∧
    (∀ b < nB, B.ends b = ∅ → mem (bsParentBase p bunCap + b) = B.parent b) ∧
    (∀ b, nB ≤ b → b < bunCap →
      mem (bsHeadBase p + b) = 0 ∧ mem (bsSizeBase p bunCap + b) = 0 ∧
      mem (bsParentBase p bunCap + b) = 0) ∧
    (∀ b < bunCap,
      mem (bsSeenBase p bunCap + b) = 0 ∧
      mem (bsInCandBase p bunCap + b) = 0 ∧
      mem (bsCandNextBase p bunCap + b) = 0)

/-- Full in-memory representation of a branch bundle table `S : BundleTableState slotCap` at handle
`tbl` with capacities `(slotCap, vCap, eCap)` and metadata `m`. -/
def BundleTableRepAt (slotCap vCap eCap tbl : ℕ) (S : BundleTableState slotCap)
    (m : BundleTableMeta slotCap) (mem : ℕ → ℕ) : Prop :=
  let prevBase := btEndPrevBase tbl slotCap eCap
  let nextBase := btEndNextBase tbl slotCap eCap
  mem (tbl + btOffSlotCap) = slotCap ∧
  mem (tbl + btOffVCap) = vCap ∧
  mem (tbl + btOffECap) = eCap ∧
  mem (tbl + btOffSlotPtr) = btSlotPtrBase tbl ∧
  mem (tbl + btOffEdgeSlot) = btEdgeSlotBase tbl slotCap ∧
  mem (tbl + btOffEndBundle) = btEndBundleBase tbl slotCap eCap ∧
  mem (tbl + btOffEndPrev) = prevBase ∧
  mem (tbl + btOffEndNext) = nextBase ∧
  mem (tbl + btOffSlotTouched) = btSlotTouchedBase tbl slotCap eCap ∧
  mem (tbl + btOffSlotDelHead) = btSlotDelHeadBase tbl slotCap eCap ∧
  mem (tbl + btOffSlotDelNext) = btSlotDelNextBase tbl slotCap eCap ∧
  mem (tbl + btOffSlotCandHead) = btSlotCandHeadBase tbl slotCap eCap ∧
  (∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
    S j₁ = some B₁ → S j₂ = some B₂ → Disjoint B₁.edges B₂.edges) ∧
  (∀ e < eCap,
    (∀ (j : Fin slotCap) (B : BundleState), S j = some B → e ∈ B.edges →
      mem (btEdgeSlotBase tbl slotCap + e) = j.1 + 1) ∧
    ((∀ (j : Fin slotCap) (B : BundleState), S j = some B → e ∉ B.edges) →
      mem (btEdgeSlotBase tbl slotCap + e) = 0)) ∧
  (∀ (j : Fin slotCap) (B : BundleState), S j = some B →
    ∀ x ∈ edgeEnds B.edges,
      mem (btEndBundleBase tbl slotCap eCap + endKey x) = B.bundleOf x) ∧
  (∀ j : Fin slotCap,
    match S j, m.slotBlocks j with
    | none, none => mem (btSlotPtrBase tbl + j.1) = 0
    | some B, some (p, bunCap) =>
        mem (btSlotPtrBase tbl + j.1) = p ∧
        BundleSlotRepAt eCap prevBase nextBase p bunCap B mem ∧
        (p + bundleSlotBlockSize bunCap ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ p)
    | _, _ => False) ∧
  (∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ p₁ c₁ p₂ c₂,
    m.slotBlocks j₁ = some (p₁, c₁) → m.slotBlocks j₂ = some (p₂, c₂) →
    p₁ + bundleSlotBlockSize c₁ ≤ p₂ ∨ p₂ + bundleSlotBlockSize c₂ ≤ p₁) ∧
  (∀ s < slotCap,
    mem (btSlotTouchedBase tbl slotCap eCap + s) = 0 ∧
    mem (btSlotDelHeadBase tbl slotCap eCap + s) = 0 ∧
    mem (btSlotCandHeadBase tbl slotCap eCap + s) = 0) ∧
  (∀ e < eCap, mem (btSlotDelNextBase tbl slotCap eCap + e) = 0) ∧
  (∀ s < slotCap,
    mem (btCurBunBase tbl slotCap eCap + s) = 0 ∧
    mem (btCurTagBase tbl slotCap eCap + s) = 0)

/-- Consistency between a bundle table state `S` and a core rotation order `cord`: every nonempty
bundle's ends belong to `cord (B.parent b)` with `B.parent b < vCap`, and `cord` places each end at
a unique core vertex `< vCap`. -/
def BundleTableCordMatch {slotCap : ℕ} (vCap : ℕ) (S : BundleTableState slotCap)
    (cord : ℕ → List End) : Prop :=
  (∀ v₁ v₂ x, x ∈ cord v₁ → x ∈ cord v₂ → v₁ = v₂) ∧
  (∀ j : Fin slotCap, ∀ B, S j = some B →
    ∀ b ∈ B.vertices, B.parent b < vCap ∧ ∀ x ∈ B.ends b, x ∈ cord (B.parent b))

end

/-! ## 5. Address-range and locality lemmas -/

public section

lemma btHeader_in_foot {slotCap eCap tbl off : ℕ} {m : BundleTableMeta slotCap}
    (hoff : off < btHdrSize) :
    bundleTableFoot eCap tbl m (tbl + off) :=
  Or.inl ⟨Nat.le_add_right _ _, by unfold bundleTableFixedSize btHdrSize at *; omega⟩

lemma btSlotPtr_in_foot {slotCap eCap tbl s : ℕ} {m : BundleTableMeta slotCap}
    (hs : s < slotCap) :
    bundleTableFoot eCap tbl m (btSlotPtrBase tbl + s) :=
  Or.inl ⟨by unfold btSlotPtrBase; omega, by unfold btSlotPtrBase bundleTableFixedSize; omega⟩

lemma btEdgeSlot_in_foot {slotCap eCap tbl e : ℕ} {m : BundleTableMeta slotCap}
    (he : e < eCap) :
    bundleTableFoot eCap tbl m (btEdgeSlotBase tbl slotCap + e) :=
  Or.inl ⟨by unfold btEdgeSlotBase; omega, by unfold btEdgeSlotBase bundleTableFixedSize; omega⟩

lemma btEndBundle_in_foot {slotCap eCap tbl k : ℕ} {m : BundleTableMeta slotCap}
    (hk : k < 2 * eCap) :
    bundleTableFoot eCap tbl m (btEndBundleBase tbl slotCap eCap + k) :=
  Or.inl ⟨by unfold btEndBundleBase; omega, by unfold btEndBundleBase bundleTableFixedSize; omega⟩

lemma btEndPrev_in_foot {slotCap eCap tbl k : ℕ} {m : BundleTableMeta slotCap}
    (hk : k < 2 * eCap) :
    bundleTableFoot eCap tbl m (btEndPrevBase tbl slotCap eCap + k) :=
  Or.inl ⟨by unfold btEndPrevBase; omega, by unfold btEndPrevBase bundleTableFixedSize; omega⟩

lemma btEndNext_in_foot {slotCap eCap tbl k : ℕ} {m : BundleTableMeta slotCap}
    (hk : k < 2 * eCap) :
    bundleTableFoot eCap tbl m (btEndNextBase tbl slotCap eCap + k) :=
  Or.inl ⟨by unfold btEndNextBase; omega, by unfold btEndNextBase bundleTableFixedSize; omega⟩

lemma btSlotTouched_in_foot {slotCap eCap tbl s : ℕ} {m : BundleTableMeta slotCap}
    (hs : s < slotCap) :
    bundleTableFoot eCap tbl m (btSlotTouchedBase tbl slotCap eCap + s) :=
  Or.inl ⟨by unfold btSlotTouchedBase; omega, by unfold btSlotTouchedBase bundleTableFixedSize; omega⟩

lemma btSlotDelHead_in_foot {slotCap eCap tbl s : ℕ} {m : BundleTableMeta slotCap}
    (hs : s < slotCap) :
    bundleTableFoot eCap tbl m (btSlotDelHeadBase tbl slotCap eCap + s) :=
  Or.inl ⟨by unfold btSlotDelHeadBase; omega, by unfold btSlotDelHeadBase bundleTableFixedSize; omega⟩

lemma btSlotDelNext_in_foot {slotCap eCap tbl e : ℕ} {m : BundleTableMeta slotCap}
    (he : e < eCap) :
    bundleTableFoot eCap tbl m (btSlotDelNextBase tbl slotCap eCap + e) :=
  Or.inl ⟨by unfold btSlotDelNextBase; omega, by unfold btSlotDelNextBase bundleTableFixedSize; omega⟩

lemma btSlotCandHead_in_foot {slotCap eCap tbl s : ℕ} {m : BundleTableMeta slotCap}
    (hs : s < slotCap) :
    bundleTableFoot eCap tbl m (btSlotCandHeadBase tbl slotCap eCap + s) :=
  Or.inl ⟨by unfold btSlotCandHeadBase; omega, by unfold btSlotCandHeadBase bundleTableFixedSize; omega⟩

lemma btCurBun_in_foot {slotCap eCap tbl s : ℕ} {m : BundleTableMeta slotCap}
    (hs : s < slotCap) :
    bundleTableFoot eCap tbl m (btCurBunBase tbl slotCap eCap + s) :=
  Or.inl ⟨by unfold btCurBunBase; omega, by unfold btCurBunBase bundleTableFixedSize; omega⟩

lemma btCurTag_in_foot {slotCap eCap tbl s : ℕ} {m : BundleTableMeta slotCap}
    (hs : s < slotCap) :
    bundleTableFoot eCap tbl m (btCurTagBase tbl slotCap eCap + s) :=
  Or.inl ⟨by unfold btCurTagBase; omega, by unfold btCurTagBase bundleTableFixedSize; omega⟩

lemma btTouchedBuf_in_foot {slotCap eCap tbl s : ℕ} {m : BundleTableMeta slotCap}
    (hs : s < slotCap) :
    bundleTableFoot eCap tbl m (btTouchedBufBase tbl slotCap eCap + s) :=
  Or.inl ⟨by unfold btTouchedBufBase; omega, by unfold btTouchedBufBase bundleTableFixedSize; omega⟩

lemma btTouchedCnt_in_foot {slotCap eCap tbl : ℕ} {m : BundleTableMeta slotCap} :
    bundleTableFoot eCap tbl m (btTouchedCntAddr tbl slotCap eCap) :=
  Or.inl ⟨by unfold btTouchedCntAddr; omega, by unfold btTouchedCntAddr bundleTableFixedSize; omega⟩

lemma btBunCap_in_foot {slotCap eCap tbl : ℕ} {m : BundleTableMeta slotCap} :
    bundleTableFoot eCap tbl m (btBunCapAddr tbl slotCap eCap) :=
  Or.inl ⟨by unfold btBunCapAddr; omega, by unfold btBunCapAddr bundleTableFixedSize; omega⟩

lemma bsAddr_in_coreFoot {slotCap eCap tbl p bunCap off : ℕ} {m : BundleTableMeta slotCap}
    {j : Fin slotCap} (hj : m.slotBlocks j = some (p, bunCap))
    (hoff : off < bundleSlotBlockSize bunCap) :
    bundleTableCoreFoot eCap tbl m (p + off) :=
  Or.inr ⟨j, p, bunCap, hj, Nat.le_add_right _ _, by omega⟩

lemma bundleTableCoreFoot_subset_foot {slotCap eCap tbl : ℕ} {m : BundleTableMeta slotCap} {a : ℕ}
    (h : bundleTableCoreFoot eCap tbl m a) : bundleTableFoot eCap tbl m a := by
  rcases h with ⟨h1, h2⟩ | hblk
  · exact Or.inl ⟨h1, by unfold bundleTableCoreSize bundleTableFixedSize at *; omega⟩
  · exact Or.inr hblk

lemma btHeader_in_coreFoot {slotCap eCap tbl off : ℕ} {m : BundleTableMeta slotCap}
    (hoff : off < btHdrSize) :
    bundleTableCoreFoot eCap tbl m (tbl + off) :=
  Or.inl ⟨Nat.le_add_right _ _, by unfold bundleTableCoreSize btHdrSize at *; omega⟩

lemma btSlotPtr_in_coreFoot {slotCap eCap tbl s : ℕ} {m : BundleTableMeta slotCap}
    (hs : s < slotCap) :
    bundleTableCoreFoot eCap tbl m (btSlotPtrBase tbl + s) :=
  Or.inl ⟨by unfold btSlotPtrBase; omega, by unfold btSlotPtrBase bundleTableCoreSize; omega⟩

lemma btEdgeSlot_in_coreFoot {slotCap eCap tbl e : ℕ} {m : BundleTableMeta slotCap}
    (he : e < eCap) :
    bundleTableCoreFoot eCap tbl m (btEdgeSlotBase tbl slotCap + e) :=
  Or.inl ⟨by unfold btEdgeSlotBase; omega, by unfold btEdgeSlotBase bundleTableCoreSize; omega⟩

lemma btEndBundle_in_coreFoot {slotCap eCap tbl k : ℕ} {m : BundleTableMeta slotCap}
    (hk : k < 2 * eCap) :
    bundleTableCoreFoot eCap tbl m (btEndBundleBase tbl slotCap eCap + k) :=
  Or.inl ⟨by unfold btEndBundleBase; omega, by unfold btEndBundleBase bundleTableCoreSize; omega⟩

lemma btEndPrev_in_coreFoot {slotCap eCap tbl k : ℕ} {m : BundleTableMeta slotCap}
    (hk : k < 2 * eCap) :
    bundleTableCoreFoot eCap tbl m (btEndPrevBase tbl slotCap eCap + k) :=
  Or.inl ⟨by unfold btEndPrevBase; omega, by unfold btEndPrevBase bundleTableCoreSize; omega⟩

lemma btEndNext_in_coreFoot {slotCap eCap tbl k : ℕ} {m : BundleTableMeta slotCap}
    (hk : k < 2 * eCap) :
    bundleTableCoreFoot eCap tbl m (btEndNextBase tbl slotCap eCap + k) :=
  Or.inl ⟨by unfold btEndNextBase; omega, by unfold btEndNextBase bundleTableCoreSize; omega⟩

lemma btSlotTouched_in_coreFoot {slotCap eCap tbl s : ℕ} {m : BundleTableMeta slotCap}
    (hs : s < slotCap) :
    bundleTableCoreFoot eCap tbl m (btSlotTouchedBase tbl slotCap eCap + s) :=
  Or.inl ⟨by unfold btSlotTouchedBase; omega, by unfold btSlotTouchedBase bundleTableCoreSize; omega⟩

lemma btSlotDelHead_in_coreFoot {slotCap eCap tbl s : ℕ} {m : BundleTableMeta slotCap}
    (hs : s < slotCap) :
    bundleTableCoreFoot eCap tbl m (btSlotDelHeadBase tbl slotCap eCap + s) :=
  Or.inl ⟨by unfold btSlotDelHeadBase; omega, by unfold btSlotDelHeadBase bundleTableCoreSize; omega⟩

lemma btSlotDelNext_in_coreFoot {slotCap eCap tbl e : ℕ} {m : BundleTableMeta slotCap}
    (he : e < eCap) :
    bundleTableCoreFoot eCap tbl m (btSlotDelNextBase tbl slotCap eCap + e) :=
  Or.inl ⟨by unfold btSlotDelNextBase; omega, by unfold btSlotDelNextBase bundleTableCoreSize; omega⟩

lemma btSlotCandHead_in_coreFoot {slotCap eCap tbl s : ℕ} {m : BundleTableMeta slotCap}
    (hs : s < slotCap) :
    bundleTableCoreFoot eCap tbl m (btSlotCandHeadBase tbl slotCap eCap + s) :=
  Or.inl ⟨by unfold btSlotCandHeadBase; omega, by unfold btSlotCandHeadBase bundleTableCoreSize; omega⟩

lemma bsAddr_in_foot {slotCap eCap tbl p bunCap off : ℕ} {m : BundleTableMeta slotCap}
    {j : Fin slotCap} (hj : m.slotBlocks j = some (p, bunCap))
    (hoff : off < bundleSlotBlockSize bunCap) :
    bundleTableFoot eCap tbl m (p + off) :=
  Or.inr ⟨j, p, bunCap, hj, Nat.le_add_right _ _, by omega⟩

lemma BundleSlotRepAt.of_agree {eCap prevBase nextBase p bunCap : ℕ} {B : BundleState}
    {mem mem' : ℕ → ℕ}
    (hrep : BundleSlotRepAt eCap prevBase nextBase p bunCap B mem)
    (hblock : ∀ a, p ≤ a → a < p + bundleSlotBlockSize bunCap → mem a = mem' a)
    (hprev : ∀ k < 2 * eCap, mem (prevBase + k) = mem' (prevBase + k))
    (hnext : ∀ k < 2 * eCap, mem (nextBase + k) = mem' (nextBase + k)) :
    BundleSlotRepAt eCap prevBase nextBase p bunCap B mem' := by
  rcases hrep with ⟨nB, hV, hnB, hE, hbo, hpar0, h0, h1, h2, hdll, hpar, htail, hscr⟩
  have hb : ∀ off < bundleSlotBlockSize bunCap, mem' (p + off) = mem (p + off) :=
    fun off hoff => (hblock (p + off) (Nat.le_add_right _ _) (by omega)).symm
  refine ⟨nB, hV, hnB, hE, hbo, hpar0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb bsOffBunCap (by unfold bsOffBunCap bundleSlotBlockSize; omega)]; exact h0
  · rw [hb bsOffNB (by unfold bsOffNB bundleSlotBlockSize; omega)]; exact h1
  · rw [hb bsOffNE (by unfold bsOffNE bundleSlotBlockSize; omega)]; exact h2
  · intro b hb_lt
    obtain ⟨L, hL, hlen, hmem⟩ := hdll b hb_lt
    have hlt_cap : b < bunCap := lt_of_lt_of_le hb_lt hnB
    refine ⟨L, hL.of_agree ?_ ?_ ?_, ?_, hmem⟩
    · have := hb (3 + b) (by unfold bundleSlotBlockSize; omega)
      simpa only [bsHeadBase, Nat.add_assoc] using this
    · intro k hk; exact (hprev k (hL.2.1 k hk)).symm
    · intro k hk; exact (hnext k (hL.2.1 k hk)).symm
    · have := hb (3 + bunCap + b) (by unfold bundleSlotBlockSize; omega)
      simpa only [bsSizeBase, Nat.add_assoc] using this.trans (by simpa [bsSizeBase, Nat.add_assoc] using hlen)
  · intro b hb_lt hem
    have hlt_cap : b < bunCap := lt_of_lt_of_le hb_lt hnB
    have := hb (3 + 2 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    simpa only [bsParentBase, Nat.add_assoc] using this.trans
      (by simpa [bsParentBase, Nat.add_assoc] using hpar b hb_lt hem)
  · intro b hge hlt
    have hA := hb (3 + b) (by unfold bundleSlotBlockSize; omega)
    have hB := hb (3 + bunCap + b) (by unfold bundleSlotBlockSize; omega)
    have hC := hb (3 + 2 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    obtain ⟨t1, t2, t3⟩ := htail b hge hlt
    refine ⟨?_, ?_, ?_⟩
    · simpa only [bsHeadBase, Nat.add_assoc] using hA.trans (by simpa [bsHeadBase, Nat.add_assoc] using t1)
    · simpa only [bsSizeBase, Nat.add_assoc] using hB.trans (by simpa [bsSizeBase, Nat.add_assoc] using t2)
    · simpa only [bsParentBase, Nat.add_assoc] using hC.trans (by simpa [bsParentBase, Nat.add_assoc] using t3)
  · intro b hb_lt
    have hA := hb (3 + 3 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    have hB := hb (3 + 4 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    have hC := hb (3 + 5 * bunCap + b) (by unfold bundleSlotBlockSize; omega)
    obtain ⟨s1, s2, s3⟩ := hscr b hb_lt
    refine ⟨?_, ?_, ?_⟩
    · simpa only [bsSeenBase, Nat.add_assoc] using hA.trans (by simpa [bsSeenBase, Nat.add_assoc] using s1)
    · simpa only [bsInCandBase, Nat.add_assoc] using hB.trans (by simpa [bsInCandBase, Nat.add_assoc] using s2)
    · simpa only [bsCandNextBase, Nat.add_assoc] using hC.trans (by simpa [bsCandNextBase, Nat.add_assoc] using s3)

/-- Locality of `BundleTableRepAt`: changing memory outside `bundleTableFoot` preserves the
representation invariant. -/
theorem BundleTableRepAt.of_agree {slotCap vCap eCap tbl : ℕ} {S : BundleTableState slotCap}
    {m : BundleTableMeta slotCap} {mem mem' : ℕ → ℕ}
    (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem)
    (hagree : ∀ a, bundleTableFoot eCap tbl m a → mem a = mem' a) :
    BundleTableRepAt slotCap vCap eCap tbl S m mem' := by
  rcases hrep with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    hdisjE, hedgeSlot, hendBun, hslots, hdisjB, hscrS, hscrE, hcur0⟩
  have hhdr : ∀ off < btHdrSize, mem' (tbl + off) = mem (tbl + off) :=
    fun off hoff => (hagree _ (btHeader_in_foot hoff)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdisjE, ?_, ?_, ?_, hdisjB, ?_, ?_, ?_⟩
  · rw [hhdr btOffSlotCap (by decide)]; exact h0
  · rw [hhdr btOffVCap (by decide)]; exact h1
  · rw [hhdr btOffECap (by decide)]; exact h2
  · rw [hhdr btOffSlotPtr (by decide)]; exact h3
  · rw [hhdr btOffEdgeSlot (by decide)]; exact h4
  · rw [hhdr btOffEndBundle (by decide)]; exact h5
  · rw [hhdr btOffEndPrev (by decide)]; exact h6
  · rw [hhdr btOffEndNext (by decide)]; exact h7
  · rw [hhdr btOffSlotTouched (by decide)]; exact h8
  · rw [hhdr btOffSlotDelHead (by decide)]; exact h9
  · rw [hhdr btOffSlotDelNext (by decide)]; exact h10
  · rw [hhdr btOffSlotCandHead (by decide)]; exact h11
  · intro e he
    have heq := (hagree _ (btEdgeSlot_in_foot he)).symm
    obtain ⟨ha, hb⟩ := hedgeSlot e he
    exact ⟨fun j B hS heB => heq.trans (ha j B hS heB), fun hnone => heq.trans (hb hnone)⟩
  · intro j B hS x hx
    have heB : x.1 ∈ B.edges := (mem_edgeEnds _ _).mp hx
    have hlt : endKey x < 2 * eCap := by
      have hslot := hslots j
      rw [hS] at hslot
      cases hm : m.slotBlocks j with
      | none => rw [hm] at hslot; exact False.elim hslot
      | some pb =>
        rw [hm] at hslot
        have he_lt := hslot.2.1.choose_spec.2.2.1 x.1 heB
        rcases x with ⟨e, side⟩
        cases side <;> simp [endKey] <;> omega
    exact (hagree _ (btEndBundle_in_foot hlt)).symm.trans (hendBun j B hS x hx)
  · intro j
    have hslot := hslots j
    cases hS : S j with
    | none =>
      rw [hS] at hslot
      cases hm : m.slotBlocks j with
      | none =>
        rw [hm] at hslot
        exact (hagree _ (btSlotPtr_in_foot j.2)).symm.trans hslot
      | some pb => rw [hm] at hslot; exact False.elim hslot
    | some B =>
      rw [hS] at hslot
      cases hm : m.slotBlocks j with
      | none => rw [hm] at hslot; exact False.elim hslot
      | some pb =>
        rcases pb with ⟨p, bunCap⟩
        rw [hm] at hslot
        refine ⟨(hagree _ (btSlotPtr_in_foot j.2)).symm.trans hslot.1, ?_, hslot.2.2⟩
        exact hslot.2.1.of_agree
          (fun a ha1 ha2 => hagree a (Or.inr ⟨j, p, bunCap, hm, ha1, ha2⟩))
          (fun k hk => hagree _ (btEndPrev_in_foot hk))
          (fun k hk => hagree _ (btEndNext_in_foot hk))
  · intro s hs
    obtain ⟨s1, s2, s3⟩ := hscrS s hs
    exact ⟨(hagree _ (btSlotTouched_in_foot hs)).symm.trans s1,
      (hagree _ (btSlotDelHead_in_foot hs)).symm.trans s2,
      (hagree _ (btSlotCandHead_in_foot hs)).symm.trans s3⟩
  · intro e he
    exact (hagree _ (btSlotDelNext_in_foot he)).symm.trans (hscrE e he)
  · intro s hs
    obtain ⟨c1, c2⟩ := hcur0 s hs
    exact ⟨(hagree _ (btCurBun_in_foot hs)).symm.trans c1,
      (hagree _ (btCurTag_in_foot hs)).symm.trans c2⟩

end

end MinCostFlow.SparseCore.Program
