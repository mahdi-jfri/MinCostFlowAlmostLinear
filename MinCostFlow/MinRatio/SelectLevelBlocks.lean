module

public import MinCostFlow.MinRatio.WireSelectUpdateEdge
import Mathlib.Tactic

/-!
# The owned level blocks of the select state (`SelectLevelBlocks`)

The select procedures read, at every level `j ≤ d`, the data of `SelectLevelMetaAt`
(`WireSelectKeyEval.lean`): the graph `G_j`, the active forest `F_j`, the active sparsifier `S_j`
(for `j < d`), the embedding of the active core (for `j < d`), the frozen potentials `φ_j`, the
core lengths `C.chainLen ℓ (j + 1)` on `G_j` (`SelectCoreLenInv`), and `g` on `G_0`. The solver
holds only `G_j` for `j < d` (`SolverLevelMetaAt`). This file fixes where the rest lives: in blocks
that the select state owns, made once at Init at the global caps `(vCap, eCap)`, so that no update
pays for a block of size `m`. The core lengths are owned too, since the solver stores
`C.chainLen ℓ j` on `G_j`, one level too early for the keys.

**Layout.** The level blocks start at `B.base`. Level `j ≤ d` has one block of
`B.levelSize = dynGraphSize vCap eCap + vCap · Lk + eCap · Lk + eCap + eCap · slot` words:
* `F_j` as a `DynGraphAt` at the caps (`B.fPtr j`);
* `φ_j` as `Lk`-limb values indexed by vertex names (`B.phiPtr j`);
* the core lengths `C.chainLen ℓ (j + 1)` as `Lk`-limb values indexed by edge names (`B.lenPtr j`);
* the embedding table, one pointer per edge name (`B.embPtr j`), and one slot of `slot` words per
  edge name for its walk (`B.slotPtr j e`), so that a re-embedded edge is written in place.
After the `d + 1` level blocks come the graph `G_d` (`B.lastGPtr`) and `g` on `G_0`
(`B.g0Ptr`). The total is `selectBlocksSize`.

**The table.** `selectMlocOf B metaBase solverG` is the metadata layout that the select
procedures read: `G_j` of `j < d` points into the solver (`solverG j`), `S_j` points at the graph of level `j + 1` (`activeS j = G (j + 1)`
on reached states, a hypothesis of `selectLevelMetaAt_of_blocks`), and the rest points into
the blocks.

* `SelectMetaTableAt`: the words of the metadata block.
* `SelectBlocksAt`: the facts the blocks hold at one memory.
* `selectLevelMetaAt_of_blocks`: the table, the blocks, the solver's level graphs,
  `activeS j = G (j + 1)`, and `SelectPotInv` give `SelectLevelMetaAt`, with the core lengths
  `fun j => C.chainLen ℓ (j + 1)` (so `SelectCoreLenInv` holds by definition).
* `SelectMetaTableAt.of_agree` and `SelectBlocksAt.of_agree`: the table and the blocks depend
  only on their own words.
* `SelectRegion`: the heap block, the metadata block and the level blocks placed one after the
  other from one base, and `selectMetaDisjoint_of_region`: the hypothesis `SelectMetaDisjoint`
  of the select procedures.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. The layout of the level blocks -/

/-- The layout of the owned level blocks: the base address, the depth `d`, the global caps, the
limb count `Lk`, and the words `slot` of one embedding slot. -/
structure SelectBlocksLoc where
  base : ℕ
  d : ℕ
  vCap : ℕ
  eCap : ℕ
  Lk : ℕ
  slot : ℕ

namespace SelectBlocksLoc

/-- The words of the block of one level. -/
def levelSize (B : SelectBlocksLoc) : ℕ :=
  dynGraphSize B.vCap B.eCap + B.vCap * B.Lk + B.eCap * B.Lk + B.eCap + B.eCap * B.slot

/-- The forest `F_j`, at the start of the block of level `j`. -/
def fPtr (B : SelectBlocksLoc) (j : ℕ) : ℕ := B.base + j * B.levelSize

/-- The frozen potentials `φ_j`. -/
def phiPtr (B : SelectBlocksLoc) (j : ℕ) : ℕ := B.fPtr j + dynGraphSize B.vCap B.eCap

/-- The core lengths `C.chainLen ℓ (j + 1)` on the edges of `G_j`. -/
def lenPtr (B : SelectBlocksLoc) (j : ℕ) : ℕ := B.phiPtr j + B.vCap * B.Lk

/-- The embedding table of level `j`. -/
def embPtr (B : SelectBlocksLoc) (j : ℕ) : ℕ := B.lenPtr j + B.eCap * B.Lk

/-- The slot of the walk of edge `e` at level `j`. -/
def slotPtr (B : SelectBlocksLoc) (j e : ℕ) : ℕ := B.embPtr j + B.eCap + e * B.slot

/-- The graph `G_d` of the last level, after the `d + 1` level blocks. -/
def lastGPtr (B : SelectBlocksLoc) : ℕ := B.base + (B.d + 1) * B.levelSize

/-- The gradient `g` on `G_0`. -/
def g0Ptr (B : SelectBlocksLoc) : ℕ := B.lastGPtr + dynGraphSize B.vCap B.eCap

/-- The end of the level blocks. -/
def endAddr (B : SelectBlocksLoc) : ℕ := B.g0Ptr + B.eCap * B.Lk

end SelectBlocksLoc

/-- The words of the level blocks: `d + 1` level blocks, the last graph, and `g` on `G_0`. -/
def selectBlocksSize (d vCap eCap Lk slot : ℕ) : ℕ :=
  (d + 1) * (dynGraphSize vCap eCap + vCap * Lk + eCap * Lk + eCap + eCap * slot) +
    dynGraphSize vCap eCap + eCap * Lk

theorem SelectBlocksLoc.endAddr_eq (B : SelectBlocksLoc) :
    B.endAddr = B.base + selectBlocksSize B.d B.vCap B.eCap B.Lk B.slot := by
  simp only [endAddr, g0Ptr, lastGPtr, levelSize, selectBlocksSize]
  ring

/-- The metadata layout that the select procedures read. `G_j` of `j < d` points into the solver,
`S_j` of `j < d` points at the graph of level `j + 1`, the unused terminal slot `sPtr d` stores
`pLast` (the level-`d` stretch-rounding precision), and the rest points into the blocks. All levels
have the global caps. -/
def selectMlocOf (B : SelectBlocksLoc) (metaBase : ℕ) (solverG : ℕ → ℕ) (pLast : ℕ := 0) :
    SelectLevelMetaLoc where
  metaBase := metaBase
  d := B.d
  Lk := B.Lk
  g0Ptr := B.g0Ptr
  GPtr := fun j => if j < B.d then solverG j else B.lastGPtr
  vCap := fun _ => B.vCap
  eCap := fun _ => B.eCap
  phiPtr := B.phiPtr
  coreLenPtr := B.lenPtr
  embPtr := B.embPtr
  fPtr := B.fPtr
  sPtr := fun j => if j + 1 < B.d then solverG (j + 1) else if j < B.d then B.lastGPtr else pLast
  pLast := pLast

/-! ## 2. The facts of the table and of the blocks -/

/-- The words of the metadata block: the gradient pointer, the depth, and the eight pointer
arrays of `SelectLevelMetaAt`. -/
def SelectMetaTableAt (mem : ℕ → ℕ) (mloc : SelectLevelMetaLoc) : Prop :=
  mem (mloc.metaBase + smG0Off) = mloc.g0Ptr ∧
  mem (mloc.metaBase + smDOff) = mloc.d ∧
  ∀ j ≤ mloc.d,
    mem (smEntryAddr mloc.metaBase mloc.d 0 j) = mloc.GPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 1 j) = mloc.vCap j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 2 j) = mloc.eCap j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 4 j) = mloc.coreLenPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 5 j) = mloc.embPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 6 j) = mloc.fPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 7 j) = mloc.sPtr j

/-- The facts that the level blocks hold for the chain `C`, the gradient `g`, the lengths `ℓ`
and the frozen potentials `φ`, at precision `P` with limbs of `4` bits:
* vertex names and edge names of every level are below the caps;
* `F_j` at every level `j ≤ d`;
* `φ_j` on the vertices of `G_j`;
* the core lengths `C.chainLen ℓ (j + 1)` on the edges of `G_j`;
* for `j < d`, every edge of the active core points at its slot, and the slot holds its walk;
* `G_d`;
* `g` on `G_0`. -/
def SelectBlocksAt (mem : ℕ → ℕ) (B : SelectBlocksLoc) (P : ℕ) (C : TreeChain)
    (g ℓ : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) (pLast : ℕ := 0) : Prop :=
  (∀ j ≤ B.d, ∀ v ∈ (C.G j).V, v < B.vCap) ∧
  (∀ j ≤ B.d, ∀ e ∈ (C.G j).E, e < B.eCap) ∧
  (∀ j ≤ B.d, DynGraphAt mem (B.fPtr j) B.vCap B.eCap (C.activeLSF j).F.F) ∧
  (∀ j ≤ B.d, EdgeValuesAt mem (B.phiPtr j) 4 B.Lk P (C.G j).V (φ j)) ∧
  (∀ j ≤ B.d, EdgeValuesAt mem (B.lenPtr j) 4 B.Lk (coreLenPrec B.d P pLast j) (C.G j).E
    (C.chainLen ℓ (j + 1))) ∧
  (∀ j < B.d, ∀ e ∈ (C.activeCore j).E,
    e < B.eCap ∧ mem (B.embPtr j + e) = B.slotPtr j e ∧
    (mWalkEncode (C.activeEmb j e)).length ≤ B.slot ∧
    MWalkAt mem (B.slotPtr j e) (C.activeEmb j e)) ∧
  DynGraphAt mem B.lastGPtr B.vCap B.eCap (C.G B.d) ∧
  EdgeValuesAt mem B.g0Ptr 4 B.Lk P (C.G 0).E g

/-! ## 3. The blocks give `SelectLevelMetaAt` -/

/-- **The level data of select.** The table, the blocks, the solver's level graphs at the global
caps (for `j < d`), and `activeS j = G (j + 1)` give `SelectLevelMetaAt`, with the core lengths
`fun j => C.chainLen ℓ (j + 1)` of the blocks. `SelectPotInv` is a fact of the model that the fills
keep (a hypothesis here). -/
theorem selectLevelMetaAt_of_blocks {mem : ℕ → ℕ} {B : SelectBlocksLoc} {metaBase P pLast : ℕ}
    {solverG : ℕ → ℕ} {C : TreeChain} {g ℓ : ℕ → ℝ} {φ : ℕ → ℕ → ℝ}
    (hd : C.d = B.d)
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase solverG pLast))
    (hG : ∀ j < B.d, DynGraphAt mem (solverG j) B.vCap B.eCap (C.G j))
    (hS : ∀ j < B.d, C.activeS j = C.G (j + 1))
    (hblk : SelectBlocksAt mem B P C g ℓ φ pLast)
    (hPot : SelectPotInv C g φ) :
    SelectLevelMetaAt mem (selectMlocOf B metaBase solverG pLast) 4 P C g ℓ φ
      (fun j => C.chainLen ℓ (j + 1)) := by
  obtain ⟨hg0w, hdw, hent⟩ := htab
  obtain ⟨_, _, hF, hPhi, hLen, hEmb, hLastG, hg0⟩ := hblk
  refine ⟨hd.symm, hg0w, hdw, fun j hj => hent j (by rw [hd] at hj; exact hj), hg0,
    fun j hj => ?_, fun j hj => hPhi j (by rw [hd] at hj; exact hj),
    fun j hj => by
      have hj' : j ≤ B.d := by rw [hd] at hj; exact hj
      simpa [hd, selectMlocOf] using hLen j hj',
    fun j hj => ?_, fun j hj => hF j (by rw [hd] at hj; exact hj), fun j hj => ?_, hPot,
    fun _ _ _ _ => rfl, ?_⟩
  · -- `G_j`: the solver's graph below `d`, the last graph at `d`.
    rw [hd] at hj
    simp only [selectMlocOf]
    split_ifs with h
    · exact hG j h
    · have hjd : j = B.d := by omega
      subst hjd
      exact hLastG
  · -- The embedding table: each entry points at its slot.
    rw [hd] at hj
    intro e he
    obtain ⟨h1, h2, _, h4⟩ := hEmb j hj e he
    refine ⟨h1, ?_⟩
    change MWalkAt mem (mem (B.embPtr j + e)) (C.activeEmb j e)
    rw [h2]
    exact h4
  · -- `S_j = G (j + 1)`: the solver's graph of level `j + 1`, or the last graph.
    rw [hd] at hj
    rw [hS j hj]
    simp only [selectMlocOf, hj, ↓reduceIte]
    split_ifs with h1
    · exact hG (j + 1) h1
    · have hjd : j + 1 = B.d := by omega
      rw [hjd]
      exact hLastG
  · simp [selectMlocOf]

/-! ## 4. Frames -/

private theorem mul_add_lt_mul {v c L i : ℕ} (hv : v < c) (hi : i < L) : v * L + i < c * L := by
  have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hv)
  rw [Nat.succ_mul] at this
  omega

private theorem blk_end_le {j d S : ℕ} (hj : j ≤ d) : j * S + S ≤ (d + 1) * S := by
  have := Nat.mul_le_mul_right S (Nat.succ_le_succ hj)
  rw [Nat.succ_mul] at this
  exact this

/-- The table depends only on the words of the metadata block. -/
theorem SelectMetaTableAt.of_agree {mem mem' : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    (h : SelectMetaTableAt mem mloc)
    (hag : ∀ a, mloc.metaBase ≤ a → a < mloc.metaBase + selectLevelMetaSize mloc.d →
      mem' a = mem a) :
    SelectMetaTableAt mem' mloc := by
  obtain ⟨h0, h1, h2⟩ := h
  have hE : ∀ blk ≤ 7, ∀ j ≤ mloc.d,
      mem' (smEntryAddr mloc.metaBase mloc.d blk j) =
        mem (smEntryAddr mloc.metaBase mloc.d blk j) := fun blk hb j hj => by
    have hmul : blk * (mloc.d + 1) + j < 8 * (mloc.d + 1) := by
      have := Nat.mul_le_mul_right (mloc.d + 1) hb
      omega
    unfold smEntryAddr smTableOff
    apply hag
    · omega
    · unfold selectLevelMetaSize; omega
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · rw [hag _ (by unfold smG0Off; omega) (by unfold smG0Off selectLevelMetaSize; omega)]
    exact h0
  · rw [hag _ (by unfold smDOff; omega) (by unfold smDOff selectLevelMetaSize; omega)]
    exact h1
  · obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := h2 j hj
    exact ⟨(hE 0 (by omega) j hj).trans a0, (hE 1 (by omega) j hj).trans a1,
      (hE 2 (by omega) j hj).trans a2, (hE 3 (by omega) j hj).trans a3,
      (hE 4 (by omega) j hj).trans a4, (hE 5 (by omega) j hj).trans a5,
      (hE 6 (by omega) j hj).trans a6, (hE 7 (by omega) j hj).trans a7⟩

/-- The blocks depend only on the words in `[B.base, B.endAddr)`. -/
theorem SelectBlocksAt.of_agree {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P pLast : ℕ}
    {C : TreeChain} {g ℓ : ℕ → ℝ} {φ : ℕ → ℕ → ℝ}
    (h : SelectBlocksAt mem B P C g ℓ φ pLast)
    (hag : ∀ a, B.base ≤ a → a < B.endAddr → mem' a = mem a) :
    SelectBlocksAt mem' B P C g ℓ φ pLast := by
  obtain ⟨hV, hE, hF, hPhi, hLen, hEmb, hLastG, hg0⟩ := h
  -- Every level block ends below the last graph.
  have hblk : ∀ j ≤ B.d, B.fPtr j + B.levelSize ≤ B.lastGPtr := fun j hj => by
    have := blk_end_le (S := B.levelSize) hj
    unfold SelectBlocksLoc.fPtr SelectBlocksLoc.lastGPtr; omega
  have hlastEnd : B.lastGPtr + dynGraphSize B.vCap B.eCap + B.eCap * B.Lk = B.endAddr := by
    unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  have hbase : ∀ j, B.base ≤ B.fPtr j := fun j => by unfold SelectBlocksLoc.fPtr; omega
  have hlastBase : B.base ≤ B.lastGPtr := by unfold SelectBlocksLoc.lastGPtr; omega
  refine ⟨hV, hE, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj e he => ?_, ?_, ?_⟩
  · -- `F_j`
    refine DynGraphAt.of_agree (hF j hj) fun a h1 h2 => hag a (le_trans (hbase j) h1) ?_
    have := hblk j hj
    unfold SelectBlocksLoc.levelSize at this; omega
  · -- `φ_j`
    refine EdgeValuesAt.congr (hPhi j hj) fun v hv i hi => hag _ ?_ ?_
    · have := hbase j; unfold SelectBlocksLoc.phiPtr; omega
    · have hlt := mul_add_lt_mul (hV j hj v hv) hi
      have := hblk j hj
      unfold SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize at *; omega
  · -- the core lengths of level `j`
    refine EdgeValuesAt.congr (hLen j hj) fun e he i hi => hag _ ?_ ?_
    · have := hbase j; unfold SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr; omega
    · have hlt := mul_add_lt_mul (hE j hj e he) hi
      have := hblk j hj
      unfold SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize at *; omega
  · -- the embedding entry and its slot
    obtain ⟨h1, h2, h3, h4⟩ := hEmb j hj e he
    have hjd : j ≤ B.d := Nat.le_of_lt hj
    have hb := hblk j hjd
    have hbj := hbase j
    have hslot : ∀ i < B.slot, B.slotPtr j e + i < B.fPtr j + B.levelSize := fun i hi => by
      have hlt := mul_add_lt_mul h1 hi
      unfold SelectBlocksLoc.slotPtr SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr
        SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize; omega
    have hentry : B.embPtr j + e < B.fPtr j + B.levelSize := by
      unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr
        SelectBlocksLoc.levelSize; omega
    have hentryLo : B.fPtr j ≤ B.embPtr j + e := by
      unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr; omega
    have hslotLo : B.fPtr j ≤ B.slotPtr j e := by
      unfold SelectBlocksLoc.slotPtr SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr
        SelectBlocksLoc.phiPtr; omega
    refine ⟨h1, ?_, h3, fun i hi => ?_⟩
    · rw [hag _ (le_trans hbj hentryLo) (by omega)]; exact h2
    · have hi' : i < B.slot := lt_of_lt_of_le hi h3
      rw [hag _ (by omega) (by have := hslot i hi'; omega)]
      exact h4 i hi
  · -- the last graph
    exact DynGraphAt.of_agree hLastG fun a h1 h2 => hag a (le_trans hlastBase h1) (by omega)
  · -- `g` on `G_0`
    refine EdgeValuesAt.congr hg0 fun e he i hi => hag _ ?_ ?_
    · unfold SelectBlocksLoc.g0Ptr; omega
    · have hlt := mul_add_lt_mul (hE 0 (Nat.zero_le _) e he) hi
      unfold SelectBlocksLoc.g0Ptr; omega

/-! ## 5. The select region -/

/-- The select region from one base `sb`: the heap block at `sb`, the metadata block right after
it, and the level blocks right after that. -/
def SelectRegion (sb : ℕ) (loc : SelectHeapLoc) (B : SelectBlocksLoc) (metaBase : ℕ) : Prop :=
  loc.hb = sb ∧ loc.metaPtr = loc.endAddr ∧ metaBase = loc.metaPtr ∧
  B.base = metaBase + selectLevelMetaSize B.d ∧ loc.d = B.d ∧ loc.Lk = B.Lk ∧
  loc.g0Ptr = B.g0Ptr

/-- The words of the select region. -/
def selectRegionSize (cap d vCap eCap Lk slot : ℕ) : ℕ :=
  selectHeapSize cap d Lk + selectLevelMetaSize d + selectBlocksSize d vCap eCap Lk slot

theorem SelectRegion.endAddr_eq {sb metaBase : ℕ} {loc : SelectHeapLoc} {B : SelectBlocksLoc}
    (h : SelectRegion sb loc B metaBase) :
    B.endAddr = sb + selectRegionSize loc.cap B.d B.vCap B.eCap B.Lk B.slot := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := h
  rw [B.endAddr_eq, h4, h3, h2, loc.endAddr_eq, h1, h5, h6]
  unfold selectRegionSize; omega

/-- **The disjointness that the select procedures ask** (`SelectMetaDisjoint`). In the select
region, the metadata block and the level blocks come after the heap block. If the solver's level
graphs end below `hi` and lie off the heap block, and the region ends below `hi`, then
`SelectMetaDisjoint` holds for the table of the blocks. -/
theorem selectMetaDisjoint_of_region {sb metaBase hi pLast : ℕ} {loc : SelectHeapLoc}
    {B : SelectBlocksLoc} {solverG : ℕ → ℕ}
    (hreg : SelectRegion sb loc B metaBase)
    (hend : B.endAddr ≤ hi)
    (hG : ∀ j < B.d, solverG j + dynGraphSize B.vCap B.eCap ≤ hi ∧
      (solverG j + dynGraphSize B.vCap B.eCap ≤ loc.hb ∨ loc.endAddr ≤ solverG j)) :
    SelectMetaDisjoint (selectMlocOf B metaBase solverG pLast) loc hi := by
  obtain ⟨_, h2, h3, h4, _, h6, _⟩ := hreg
  -- The level blocks start after the heap block, and every level block ends below `hi`.
  have hbase : loc.endAddr ≤ B.base := by omega
  have hlastEnd : B.lastGPtr + dynGraphSize B.vCap B.eCap ≤ B.endAddr := by
    unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  have hlastLo : B.base ≤ B.lastGPtr := by unfold SelectBlocksLoc.lastGPtr; omega
  have hblk : ∀ j ≤ B.d, B.fPtr j + B.levelSize ≤ hi ∧ B.base ≤ B.fPtr j := fun j hj => by
    have := blk_end_le (S := B.levelSize) hj
    unfold SelectBlocksLoc.fPtr at *
    unfold SelectBlocksLoc.lastGPtr at hlastLo hlastEnd
    constructor <;> omega
  have hF : ∀ j ≤ B.d, B.fPtr j + dynGraphSize B.vCap B.eCap ≤ hi ∧ B.base ≤ B.fPtr j :=
    fun j hj => by
      have := hblk j hj
      unfold SelectBlocksLoc.levelSize at this
      constructor <;> omega
  refine ⟨h6.symm, ?_, Or.inr (by simp only [selectMlocOf]; omega), fun j hj => ?_, ?_⟩
  · simp only [selectMlocOf]; omega
  · simp only [selectMlocOf]
    refine ⟨?_, ?_, (hF j hj).1, Or.inr (by have := (hF j hj).2; omega), fun hjd => ?_⟩
    · split_ifs with h
      · exact (hG j h).1
      · omega
    · split_ifs with h
      · exact (hG j h).2
      · exact Or.inr (by omega)
    · split_ifs with h
      · exact hG (j + 1) h
      · exact ⟨by omega, Or.inr (by omega)⟩
  · -- The value tables and the embedding table: inside the blocks, or `g` at the end.
    refine ⟨?_, fun j hj => ?_⟩
    · simp only [selectMlocOf]; unfold SelectBlocksLoc.endAddr at hend; omega
    · have := (hblk j hj).1
      simp only [selectMlocOf]
      unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr
        SelectBlocksLoc.levelSize at *
      refine ⟨by omega, by omega, by omega⟩

end MinCostFlow.MinRatio
