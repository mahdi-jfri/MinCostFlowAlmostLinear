module

public import MinCostFlow.MinRatio.WireSelectKeyMath
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import MinCostFlow.Num.Representation
import Mathlib.Tactic.Linarith

/-!
# Memory layout and pure invariants for the indexed candidate-key max-heap

Defines the contiguous Word-RAM memory layout `SelectHeapLoc` and invariants `SelectHeapAt` /
`SelectHeapMatchesChain` for the cycle-query heap (`jtree.tex`, pages
21 and 24):

1. `SelectHeapLoc`: contiguous allocation `[hb, hb + selectHeapSize cap d Lk)` holding the 14-word
   header, the 0-indexed binary max-heap (`arr`, `pos`, `lvl`), the per-level doubly-linked
   candidate lists (`candHead`, `candPrev`, `candNext`), and the flat `Lk`-limb key tables
   (`numBase`, `denBase`).
2. `SelectHeapBijection`, `SelectHeapKeysValid`, `SelectHeapOrder`, `SelectHeapCandLists`, and
   `SelectHeapAt`.
3. `SelectHeapMatchesChain` and `selectHeapMatchesChain_root`: proves that when `size = 0` the
   off-tree candidate set is empty, and when `size > 0` the root `arr[0]` is
   `leastArgmax S (heapCycleRatio C g ℓ) hne`, `lvl[arr[0]] = C.edgeLevel arr[0]`, and the sign
   of `N_{arr[0]}` matches `walkInner g (C.fundChainCycle arr[0]) ≤ 0`.
4. Pure transition invariants `SelectHeapOrderExceptUp` and `SelectHeapOrderExceptDown` for
   `siftUp`, `siftDown`, insert, update, and delete.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM Chain DynSpanner.Program MinCostFlow.Num

/-! ## 1. Contiguous layout constants and descriptor -/

def shSizeOff : ℕ := 0
def shCapOff : ℕ := 1
def shDOff : ℕ := 2
def shLkOff : ℕ := 3
def shArrOff : ℕ := 4
def shPosOff : ℕ := 5
def shLvlOff : ℕ := 6
def shNumOff : ℕ := 7
def shDenOff : ℕ := 8
def shCandHeadOff : ℕ := 9
def shCandPrevOff : ℕ := 10
def shCandNextOff : ℕ := 11
def shG0Off : ℕ := 12
def shMetaOff : ℕ := 13
def shHdrSize : ℕ := 14

/-- Total word footprint of a contiguous select-heap block of capacity `cap`, `d + 1` levels,
and `Lk`-limb keys. -/
def selectHeapSize (cap d Lk : ℕ) : ℕ :=
  shHdrSize + (d + 1) + 5 * cap + 2 * (cap * Lk)

/-- Contiguous layout descriptor for an indexed select-heap rooted at `hb`. -/
structure SelectHeapLoc where
  hb : ℕ
  cap : ℕ
  d : ℕ
  Lk : ℕ
  g0Ptr : ℕ
  metaPtr : ℕ

namespace SelectHeapLoc

def arrPtr (loc : SelectHeapLoc) : ℕ := loc.hb + shHdrSize
def posPtr (loc : SelectHeapLoc) : ℕ := loc.arrPtr + loc.cap
def lvlPtr (loc : SelectHeapLoc) : ℕ := loc.posPtr + loc.cap
def candHead (loc : SelectHeapLoc) : ℕ := loc.lvlPtr + loc.cap
def candPrev (loc : SelectHeapLoc) : ℕ := loc.candHead + (loc.d + 1)
def candNext (loc : SelectHeapLoc) : ℕ := loc.candPrev + loc.cap
def numBase (loc : SelectHeapLoc) : ℕ := loc.candNext + loc.cap
def denBase (loc : SelectHeapLoc) : ℕ := loc.numBase + loc.cap * loc.Lk
def endAddr (loc : SelectHeapLoc) : ℕ := loc.denBase + loc.cap * loc.Lk

theorem endAddr_eq (loc : SelectHeapLoc) :
    loc.endAddr = loc.hb + selectHeapSize loc.cap loc.d loc.Lk := by
  simp only [endAddr, denBase, numBase, candNext, candPrev, candHead, lvlPtr, posPtr, arrPtr,
    selectHeapSize, shHdrSize]
  omega

/-- Read the signed numerator of edge `e` in `loc`. -/
def readNum (loc : SelectHeapLoc) (mem : ℕ → ℕ) (h e : ℕ) : ℤ :=
  Num.intVal mem (loc.numBase + e * loc.Lk) h loc.Lk

/-- Read the signed denominator of edge `e` in `loc`. -/
def readDen (loc : SelectHeapLoc) (mem : ℕ → ℕ) (h e : ℕ) : ℤ :=
  Num.intVal mem (loc.denBase + e * loc.Lk) h loc.Lk

/-- Compare two edges `e₁, e₂` using their stored keys in `loc`. -/
def edgeBetter (loc : SelectHeapLoc) (mem : ℕ → ℕ) (h e₁ e₂ : ℕ) : Bool :=
  keyBetter e₁ (loc.readNum mem h e₁) (loc.readDen mem h e₁)
    e₂ (loc.readNum mem h e₂) (loc.readDen mem h e₂)

end SelectHeapLoc

/-! ## 2. Core heap invariants -/

/-- The 14-word header at `loc.hb` matches `loc` and current heap size `size`. -/
def SelectHeapHeaderAt (mem : ℕ → ℕ) (loc : SelectHeapLoc) (size : ℕ) : Prop :=
  ListAt mem loc.hb
    [size, loc.cap, loc.d, loc.Lk, loc.arrPtr, loc.posPtr, loc.lvlPtr,
     loc.numBase, loc.denBase, loc.candHead, loc.candPrev, loc.candNext,
     loc.g0Ptr, loc.metaPtr]

/-- Bijection between heap indices `0 .. size - 1` (`arr`) and active edge IDs `< cap` (`pos`). -/
def SelectHeapBijection (mem : ℕ → ℕ) (loc : SelectHeapLoc) (size : ℕ) : Prop :=
  size ≤ loc.cap ∧
  (∀ p < size, mem (loc.arrPtr + p) < loc.cap) ∧
  (∀ p < size, mem (loc.posPtr + mem (loc.arrPtr + p)) = p + 1) ∧
  (∀ e < loc.cap, mem (loc.posPtr + e) = 0 ∨
    (mem (loc.posPtr + e) ≤ size ∧ mem (loc.arrPtr + (mem (loc.posPtr + e) - 1)) = e))

/-- Every edge currently in the heap has valid `lvl ≤ d` and valid `Lk`-limb keys with `0 < den`. -/
def SelectHeapKeysValid (mem : ℕ → ℕ) (loc : SelectHeapLoc) (h : ℕ) : Prop :=
  ∀ e < loc.cap, mem (loc.posPtr + e) ≠ 0 →
    mem (loc.lvlPtr + e) ≤ loc.d ∧
    Num.Valid mem (loc.numBase + e * loc.Lk) h loc.Lk ∧
    Num.Valid mem (loc.denBase + e * loc.Lk) h loc.Lk ∧
    0 < loc.readDen mem h e

/-- Binary max-heap order: every non-root position `0 < p < size` is beaten by its parent `(p - 1) / 2`. -/
def SelectHeapOrder (mem : ℕ → ℕ) (loc : SelectHeapLoc) (h size : ℕ) : Prop :=
  ∀ p, 0 < p → p < size →
    loc.edgeBetter mem h (mem (loc.arrPtr + (p - 1) / 2)) (mem (loc.arrPtr + p)) = true

/-- Per-level 1-indexed doubly-linked candidate lists `candHead[0..d]` partitioning the active
edges in the heap by their stored level `lvl[e]`. -/
def SelectHeapCandLists (mem : ℕ → ℕ) (loc : SelectHeapLoc) : Prop :=
  ∃ lists : ℕ → List ℕ, ∀ i ≤ loc.d,
    IsDoublyLinkedList mem loc.candPrev loc.candNext (loc.candHead + i) loc.cap (lists i) ∧
    ∀ e, e ∈ lists i ↔ e < loc.cap ∧ mem (loc.posPtr + e) ≠ 0 ∧ mem (loc.lvlPtr + e) = i

/-- Complete structural invariant of the indexed select-heap at `loc` with `size` candidates. -/
def SelectHeapAt (mem : ℕ → ℕ) (loc : SelectHeapLoc) (h size : ℕ) : Prop :=
  SelectHeapHeaderAt mem loc size ∧
  SelectHeapBijection mem loc size ∧
  SelectHeapKeysValid mem loc h ∧
  SelectHeapOrder mem loc h size ∧
  SelectHeapCandLists mem loc

/-- Semantic agreement between the select-heap at `loc` and a tree chain `(C, g, ℓ)`:
each stored candidate key `(readNum, readDen)` represents `(walkInner, wlen)` up to a positive
common scale (`SelectKeyRepresents`), accommodating precision `P` on levels `< d` and
`P + pLast` on level `d`. -/
def SelectHeapMatchesChain (mem : ℕ → ℕ) (loc : SelectHeapLoc) (h _P : ℕ)
    (C : TreeChain) (g ℓ : ℕ → ℝ) (size : ℕ) : Prop :=
  SelectHeapAt mem loc h size ∧
  loc.d = C.d ∧
  (∀ e, (e < loc.cap ∧ mem (loc.posPtr + e) ≠ 0) ↔ e ∈ (C.G 0).E \ C.chainTree.E) ∧
  ∀ e ∈ (C.G 0).E \ C.chainTree.E,
    mem (loc.lvlPtr + e) = C.edgeLevel e ∧
    SelectKeyRepresents (loc.readNum mem h e) (loc.readDen mem h e)
      (walkInner (C.chainGrad g (C.edgeLevel e + 1)) (C.sparsifierCycle (C.edgeLevel e) e))
      (C.wlen ℓ e)

/-! ## 3. Partial-order invariants for `siftUp` and `siftDown` -/

/-- Heap order holding everywhere except possibly between `k` and its parent `(k - 1) / 2`,
while `(k - 1) / 2` already beats any child of `k`. -/
def SelectHeapOrderExceptUp (mem : ℕ → ℕ) (loc : SelectHeapLoc) (h size k : ℕ) : Prop :=
  k < size ∧
  (∀ p, 0 < p → p < size → p ≠ k →
    loc.edgeBetter mem h (mem (loc.arrPtr + (p - 1) / 2)) (mem (loc.arrPtr + p)) = true) ∧
  (0 < k → ∀ c, c < size → (c - 1) / 2 = k →
    loc.edgeBetter mem h (mem (loc.arrPtr + (k - 1) / 2)) (mem (loc.arrPtr + c)) = true)

/-- Heap order holding everywhere except possibly between `k` and its children `c` with `(c - 1) / 2 = k`,
while if `0 < k`, `parent(k)` already beats every child of `k`. -/
def SelectHeapOrderExceptDown (mem : ℕ → ℕ) (loc : SelectHeapLoc) (h size k : ℕ) : Prop :=
  k < size ∧
  (∀ p, 0 < p → p < size → (p - 1) / 2 ≠ k →
    loc.edgeBetter mem h (mem (loc.arrPtr + (p - 1) / 2)) (mem (loc.arrPtr + p)) = true) ∧
  (0 < k → ∀ c, c < size → (c - 1) / 2 = k →
    loc.edgeBetter mem h (mem (loc.arrPtr + (k - 1) / 2)) (mem (loc.arrPtr + c)) = true)

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain DynSpanner.Program MinCostFlow.Num

/-! ## 4. Basic bijection, framing, and root-optimality theorems -/

theorem SelectHeapBijection.arr_inj {mem : ℕ → ℕ} {loc : SelectHeapLoc} {size : ℕ}
    (hb : SelectHeapBijection mem loc size) {p q : ℕ} (hp : p < size) (hq : q < size)
    (heq : mem (loc.arrPtr + p) = mem (loc.arrPtr + q)) : p = q := by
  have h1 := hb.2.2.1 p hp
  have h2 := hb.2.2.1 q hq
  rw [heq] at h1
  omega

theorem SelectHeapBijection.pos_ne_zero_iff {mem : ℕ → ℕ} {loc : SelectHeapLoc} {size e : ℕ}
    (hb : SelectHeapBijection mem loc size) (he : e < loc.cap) :
    mem (loc.posPtr + e) ≠ 0 ↔ ∃ p < size, mem (loc.arrPtr + p) = e := by
  constructor
  · intro hnz
    rcases hb.2.2.2 e he with h0 | ⟨hle, harr⟩
    · exact absurd h0 hnz
    · exact ⟨mem (loc.posPtr + e) - 1, by omega, harr⟩
  · rintro ⟨p, hp, rfl⟩
    rw [hb.2.2.1 p hp]
    omega

theorem SelectHeapBijection.pos_arr_ne_zero {mem : ℕ → ℕ} {loc : SelectHeapLoc} {size p : ℕ}
    (hb : SelectHeapBijection mem loc size) (hp : p < size) :
    mem (loc.posPtr + mem (loc.arrPtr + p)) ≠ 0 := by
  rw [hb.2.2.1 p hp]; omega

/-- By strong induction along parent links, the root `arr[0]` beats every other element `arr[p]`
(`0 < p < size`). -/
theorem selectHeapOrder_root_best {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h size : ℕ}
    (hb : SelectHeapBijection mem loc size)
    (hk : SelectHeapKeysValid mem loc h)
    (ho : SelectHeapOrder mem loc h size)
    {p : ℕ} (hp0 : 0 < p) (hp : p < size) :
    loc.edgeBetter mem h (mem loc.arrPtr) (mem (loc.arrPtr + p)) = true := by
  have hrec : ∀ q, 0 < q → q < size →
      loc.edgeBetter mem h (mem loc.arrPtr) (mem (loc.arrPtr + q)) = true := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro hq0 hq
      let par := (q - 1) / 2
      have hpar_lt : par < q := by dsimp only [par]; omega
      have hstep : loc.edgeBetter mem h (mem (loc.arrPtr + par)) (mem (loc.arrPtr + q)) = true :=
        ho q hq0 hq
      by_cases hpar0 : par = 0
      · simpa [hpar0] using hstep
      · have htop := ih par hpar_lt (by omega) (lt_trans hpar_lt hq)
        have hd0 : 0 < loc.readDen mem h (mem loc.arrPtr) := by
          have := hk (mem (loc.arrPtr + 0)) (hb.2.1 0 (by omega)) (hb.pos_arr_ne_zero (by omega))
          simpa using this.2.2.2
        have hdPar : 0 < loc.readDen mem h (mem (loc.arrPtr + par)) :=
          (hk _ (hb.2.1 par (lt_trans hpar_lt hq)) (hb.pos_arr_ne_zero (lt_trans hpar_lt hq))).2.2.2
        have hdQ : 0 < loc.readDen mem h (mem (loc.arrPtr + q)) :=
          (hk _ (hb.2.1 q hq) (hb.pos_arr_ne_zero hq)).2.2.2
        exact keyBetter_trans_pos hd0 hdPar hdQ htop hstep
  exact hrec p hp0 hp

/-- **Root-selection theorem for `SelectHeapMatchesChain`**:
1. `size = 0` iff the candidate set `(C.G 0).E \ C.chainTree.E` is empty.
2. Whenever `0 < size`, `eBest = mem loc.arrPtr` equals `leastArgmax S (heapCycleRatio C g ℓ) hne`,
   `mem (loc.lvlPtr + eBest) = C.edgeLevel eBest`, and `readNum eBest ≤ 0` iff
   `walkInner g (C.fundChainCycle eBest) ≤ 0`. -/
theorem selectHeapMatchesChain_root {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h P size : ℕ}
    {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    (hm : SelectHeapMatchesChain mem loc h P C g ℓ size) :
    (size = 0 ↔ (C.G 0).E \ C.chainTree.E = ∅) ∧
    (∀ _ : 0 < size,
      let S := (C.G 0).E \ C.chainTree.E
      ∃ hne : S.Nonempty,
        let eBest := mem loc.arrPtr
        eBest = leastArgmax S (heapCycleRatio C g ℓ) hne ∧
        mem (loc.lvlPtr + eBest) = C.edgeLevel eBest ∧
        (loc.readNum mem h eBest ≤ 0 ↔ walkInner g (C.fundChainCycle eBest) ≤ 0)) := by
  obtain ⟨⟨_, hb, hk, ho, _⟩, _, hmem, hvals⟩ := hm
  have hEmpty : size = 0 ↔ (C.G 0).E \ C.chainTree.E = ∅ := by
    constructor
    · intro hs0
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      obtain ⟨heCap, hnz⟩ := (hmem e).mpr he
      obtain ⟨p, hp, _⟩ := (hb.pos_ne_zero_iff heCap).mp hnz
      omega
    · intro hE
      by_contra hnz
      have hpos : 0 < size := Nat.pos_of_ne_zero hnz
      have he0 : mem (loc.arrPtr + 0) ∈ (C.G 0).E \ C.chainTree.E :=
        (hmem _).mp ⟨hb.2.1 0 hpos, hb.pos_arr_ne_zero hpos⟩
      rw [hE] at he0
      exact Finset.notMem_empty _ he0
  refine ⟨hEmpty, fun hpos => ?_⟩
  have he0Mem : mem loc.arrPtr ∈ (C.G 0).E \ C.chainTree.E := by
    have := (hmem (mem (loc.arrPtr + 0))).mp ⟨hb.2.1 0 hpos, hb.pos_arr_ne_zero hpos⟩
    simpa using this
  have hne : ((C.G 0).E \ C.chainTree.E).Nonempty := ⟨mem loc.arrPtr, he0Mem⟩
  refine ⟨hne, ?_, (hvals _ he0Mem).1, ?_⟩
  · refine heapTop_eq_leastArgmax C g ℓ 0 _ hne (mem loc.arrPtr) he0Mem
      (loc.readNum mem h) (loc.readDen mem h) ?_ ?_ ?_
    · intro e he
      obtain ⟨heCap, hnz⟩ := (hmem e).mpr he
      exact (hk e heCap hnz).2.2.2
    · intro e he
      obtain ⟨_, hrep⟩ := hvals e he
      unfold heapCycleRatio
      simpa using hrep.ratio_eq.symm
    · intro e he hneE
      obtain ⟨heCap, hnz⟩ := (hmem e).mpr he
      obtain ⟨p, hp, hpArr⟩ := (hb.pos_ne_zero_iff heCap).mp hnz
      have hp0 : 0 < p := by
        by_contra h0
        have hpz : p = 0 := by omega
        subst hpz
        exact hneE (by simpa using hpArr.symm)
      simpa [SelectHeapLoc.edgeBetter, hpArr] using selectHeapOrder_root_best hb hk ho hp0 hp
  · rw [walkInner_fundChainCycle_nonpos_iff C hH hSpan he0Mem]
    exact (hvals _ he0Mem).2.nonpos_iff

/-- Framing lemma: if `mem'` agrees with `mem` on `[loc.hb, loc.endAddr)`, then `SelectHeapAt`
and `SelectHeapMatchesChain` are preserved. -/
theorem SelectHeapAt.of_agree {mem mem' : ℕ → ℕ} {loc : SelectHeapLoc} {h size : ℕ}
    (hs : SelectHeapAt mem loc h size)
    (hag : ∀ a, loc.hb ≤ a → a < loc.endAddr → mem' a = mem a) :
    SelectHeapAt mem' loc h size := by
  have hag_hdr : ∀ j < 14, mem' (loc.hb + j) = mem (loc.hb + j) := fun j hj =>
    hag (loc.hb + j) (by omega) (by rw [loc.endAddr_eq]; unfold selectHeapSize shHdrSize; omega)
  have hag_arr : ∀ p < loc.cap, mem' (loc.arrPtr + p) = mem (loc.arrPtr + p) := fun p hp =>
    hag _ (by unfold SelectHeapLoc.arrPtr; omega)
      (by rw [loc.endAddr_eq]; unfold SelectHeapLoc.arrPtr selectHeapSize shHdrSize; omega)
  have hag_pos : ∀ e < loc.cap, mem' (loc.posPtr + e) = mem (loc.posPtr + e) := fun e he =>
    hag _ (by unfold SelectHeapLoc.posPtr SelectHeapLoc.arrPtr; omega)
      (by rw [loc.endAddr_eq]; unfold SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize; omega)
  have hag_lvl : ∀ e < loc.cap, mem' (loc.lvlPtr + e) = mem (loc.lvlPtr + e) := fun e he =>
    hag _ (by unfold SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr; omega)
      (by rw [loc.endAddr_eq]; unfold SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize; omega)
  have hag_ch : ∀ i ≤ loc.d, mem' (loc.candHead + i) = mem (loc.candHead + i) := fun i hi =>
    hag _ (by unfold SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr; omega)
      (by rw [loc.endAddr_eq]; unfold SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize; omega)
  have hag_cp : ∀ e < loc.cap, mem' (loc.candPrev + e) = mem (loc.candPrev + e) := fun e he =>
    hag _ (by unfold SelectHeapLoc.candPrev SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr; omega)
      (by rw [loc.endAddr_eq]; unfold SelectHeapLoc.candPrev SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize; omega)
  have hag_cn : ∀ e < loc.cap, mem' (loc.candNext + e) = mem (loc.candNext + e) := fun e he =>
    hag _ (by unfold SelectHeapLoc.candNext SelectHeapLoc.candPrev SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr; omega)
      (by rw [loc.endAddr_eq]; unfold SelectHeapLoc.candNext SelectHeapLoc.candPrev SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize; omega)
  have hag_num : ∀ e < loc.cap, ∀ k < loc.Lk,
      mem' (loc.numBase + e * loc.Lk + k) = mem (loc.numBase + e * loc.Lk + k) := fun e he k hk => by
    have hmul : e * loc.Lk + k < loc.cap * loc.Lk := by
      have h1 : (e + 1) * loc.Lk ≤ loc.cap * loc.Lk := Nat.mul_le_mul_right _ he
      rw [Nat.add_mul, Nat.one_mul] at h1; omega
    exact hag _
      (by unfold SelectHeapLoc.numBase SelectHeapLoc.candNext SelectHeapLoc.candPrev
            SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr; omega)
      (by unfold SelectHeapLoc.endAddr SelectHeapLoc.denBase; omega)
  have hag_den : ∀ e < loc.cap, ∀ k < loc.Lk,
      mem' (loc.denBase + e * loc.Lk + k) = mem (loc.denBase + e * loc.Lk + k) := fun e he k hk => by
    have hmul : e * loc.Lk + k < loc.cap * loc.Lk := by
      have h1 : (e + 1) * loc.Lk ≤ loc.cap * loc.Lk := Nat.mul_le_mul_right _ he
      rw [Nat.add_mul, Nat.one_mul] at h1; omega
    exact hag _
      (by unfold SelectHeapLoc.denBase SelectHeapLoc.numBase SelectHeapLoc.candNext
            SelectHeapLoc.candPrev SelectHeapLoc.candHead SelectHeapLoc.lvlPtr
            SelectHeapLoc.posPtr SelectHeapLoc.arrPtr; omega)
      (by unfold SelectHeapLoc.endAddr; omega)
  obtain ⟨hhdr, hbij, hkeys, hord, hcand⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; exact (hag_hdr j (by simpa using hj)).trans (hhdr j hj)
  · refine ⟨hbij.1, fun p hp => by rw [hag_arr p (lt_of_lt_of_le hp hbij.1)]; exact hbij.2.1 p hp,
      fun p hp => by
        rw [hag_arr p (lt_of_lt_of_le hp hbij.1), hag_pos _ (hbij.2.1 p hp)]
        exact hbij.2.2.1 p hp,
      fun e he => by
        rw [hag_pos e he]
        rcases hbij.2.2.2 e he with h0 | ⟨hle, harr⟩
        · exact Or.inl h0
        · have hsizeCap := hbij.1
          exact Or.inr ⟨hle, by rw [hag_arr _ (by omega)]; exact harr⟩⟩
  · intro e he hnz
    rw [hag_pos e he] at hnz
    obtain ⟨hlvl, hvn, hvd, hdp⟩ := hkeys e he hnz
    refine ⟨(hag_lvl e he).trans_le hlvl,
      fun k hk => (hag_num e he k hk).trans_lt (hvn k hk),
      fun k hk => (hag_den e he k hk).trans_lt (hvd k hk), ?_⟩
    unfold SelectHeapLoc.readDen
    rw [Num.intVal_congr (hag_den e he)]
    exact hdp
  · intro p hp0 hp
    have hpar_lt : (p - 1) / 2 < loc.cap := lt_of_lt_of_le (by omega) hbij.1
    have hp_lt : p < loc.cap := lt_of_lt_of_le hp hbij.1
    rw [hag_arr _ hpar_lt, hag_arr p hp_lt]
    have he1 := hbij.2.1 _ (by omega : (p - 1) / 2 < size)
    have he2 := hbij.2.1 p hp
    unfold SelectHeapLoc.edgeBetter SelectHeapLoc.readNum SelectHeapLoc.readDen
    rw [Num.intVal_congr (hag_num _ he1), Num.intVal_congr (hag_den _ he1),
        Num.intVal_congr (hag_num _ he2), Num.intVal_congr (hag_den _ he2)]
    exact hord p hp0 hp
  · obtain ⟨lists, hlists⟩ := hcand
    refine ⟨lists, fun i hi => ?_⟩
    obtain ⟨hdll, hiff⟩ := hlists i hi
    refine ⟨hdll.of_agree (hag_ch i hi) (fun e he => hag_cp e (hdll.2.1 e he))
      (fun e he => hag_cn e (hdll.2.1 e he)), fun e => ?_⟩
    rw [hiff e]
    constructor
    · rintro ⟨heCap, hnz, hlvl⟩
      exact ⟨heCap, by rwa [hag_pos e heCap], (hag_lvl e heCap).trans hlvl⟩
    · rintro ⟨heCap, hnz, hlvl⟩
      exact ⟨heCap, by rwa [← hag_pos e heCap], (hag_lvl e heCap).symm.trans hlvl⟩

theorem SelectHeapMatchesChain.of_agree {mem mem' : ℕ → ℕ} {loc : SelectHeapLoc} {h P size : ℕ}
    {C : TreeChain} {g ℓ : ℕ → ℝ}
    (hm : SelectHeapMatchesChain mem loc h P C g ℓ size)
    (hag : ∀ a, loc.hb ≤ a → a < loc.endAddr → mem' a = mem a) :
    SelectHeapMatchesChain mem' loc h P C g ℓ size := by
  have hag_pos : ∀ e < loc.cap, mem' (loc.posPtr + e) = mem (loc.posPtr + e) := fun e he =>
    hag _ (by unfold SelectHeapLoc.posPtr SelectHeapLoc.arrPtr; omega)
      (by rw [loc.endAddr_eq]; unfold SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize; omega)
  have hag_lvl : ∀ e < loc.cap, mem' (loc.lvlPtr + e) = mem (loc.lvlPtr + e) := fun e he =>
    hag _ (by unfold SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr; omega)
      (by rw [loc.endAddr_eq]; unfold SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize; omega)
  have hag_num : ∀ e < loc.cap, ∀ k < loc.Lk,
      mem' (loc.numBase + e * loc.Lk + k) = mem (loc.numBase + e * loc.Lk + k) := fun e he k hk => by
    have hmul : e * loc.Lk + k < loc.cap * loc.Lk := by
      have h1 : (e + 1) * loc.Lk ≤ loc.cap * loc.Lk := Nat.mul_le_mul_right _ he
      rw [Nat.add_mul, Nat.one_mul] at h1; omega
    exact hag _
      (by unfold SelectHeapLoc.numBase SelectHeapLoc.candNext SelectHeapLoc.candPrev
            SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr; omega)
      (by unfold SelectHeapLoc.endAddr SelectHeapLoc.denBase; omega)
  have hag_den : ∀ e < loc.cap, ∀ k < loc.Lk,
      mem' (loc.denBase + e * loc.Lk + k) = mem (loc.denBase + e * loc.Lk + k) := fun e he k hk => by
    have hmul : e * loc.Lk + k < loc.cap * loc.Lk := by
      have h1 : (e + 1) * loc.Lk ≤ loc.cap * loc.Lk := Nat.mul_le_mul_right _ he
      rw [Nat.add_mul, Nat.one_mul] at h1; omega
    exact hag _
      (by unfold SelectHeapLoc.denBase SelectHeapLoc.numBase SelectHeapLoc.candNext
            SelectHeapLoc.candPrev SelectHeapLoc.candHead SelectHeapLoc.lvlPtr
            SelectHeapLoc.posPtr SelectHeapLoc.arrPtr; omega)
      (by unfold SelectHeapLoc.endAddr; omega)
  obtain ⟨hs, hd, hmem, hvals⟩ := hm
  refine ⟨hs.of_agree hag, hd, fun e => ?_, fun e he => ?_⟩
  · rw [← hmem e]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [← hag_pos e h1]⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hag_pos e h1]⟩
  · have heCap := ((hmem e).mpr he).1
    obtain ⟨hlvl, hrep⟩ := hvals e he
    refine ⟨(hag_lvl e heCap).trans hlvl, ?_⟩
    unfold SelectHeapLoc.readNum SelectHeapLoc.readDen
    rw [Num.intVal_congr (hag_num e heCap), Num.intVal_congr (hag_den e heCap)]
    exact hrep

/-! ## 5. Pure heap-swap and sift-step lemmas -/

/-- Memory resulting from swapping heap positions `p` and `q` (`arr[p] ↔ arr[q]`, updating `pos`). -/
@[expose] def heapSwapMem (mem : ℕ → ℕ) (loc : SelectHeapLoc) (p q : ℕ) : ℕ → ℕ :=
  let ep := mem (loc.arrPtr + p)
  let eq := mem (loc.arrPtr + q)
  Function.update
    (Function.update
      (Function.update
        (Function.update mem (loc.arrPtr + p) eq)
        (loc.arrPtr + q) ep)
      (loc.posPtr + eq) (p + 1))
    (loc.posPtr + ep) (q + 1)

theorem heapSwapMem_eq_of_outside {mem : ℕ → ℕ} {loc : SelectHeapLoc} {p q a : ℕ}
    (hp : p < loc.cap) (hq : q < loc.cap)
    (hep : mem (loc.arrPtr + p) < loc.cap) (heq : mem (loc.arrPtr + q) < loc.cap)
    (hout : a < loc.arrPtr ∨ loc.lvlPtr ≤ a) :
    heapSwapMem mem loc p q a = mem a := by
  unfold heapSwapMem
  have h1 : a ≠ loc.posPtr + mem (loc.arrPtr + p) := by
    unfold SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr at *; omega
  have h2 : a ≠ loc.posPtr + mem (loc.arrPtr + q) := by
    unfold SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr at *; omega
  have h3 : a ≠ loc.arrPtr + q := by
    unfold SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr at *; omega
  have h4 : a ≠ loc.arrPtr + p := by
    unfold SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr at *; omega
  rw [Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4]

theorem heapSwapMem_arr {mem : ℕ → ℕ} {loc : SelectHeapLoc} {p q r : ℕ}
    (hr : r < loc.cap) (hpq : p ≠ q) :
    heapSwapMem mem loc p q (loc.arrPtr + r) =
      if r = q then mem (loc.arrPtr + p)
      else if r = p then mem (loc.arrPtr + q)
      else mem (loc.arrPtr + r) := by
  unfold heapSwapMem
  have hne1 : loc.arrPtr + r ≠ loc.posPtr + mem (loc.arrPtr + p) := by
    unfold SelectHeapLoc.posPtr; omega
  have hne2 : loc.arrPtr + r ≠ loc.posPtr + mem (loc.arrPtr + q) := by
    unfold SelectHeapLoc.posPtr; omega
  rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
  by_cases hrq : r = q
  · subst hrq; simp
  · rw [Function.update_of_ne (by omega), ite_eq_right hrq]
    by_cases hrp : r = p
    · subst hrp; simp
    · rw [Function.update_of_ne (by omega), ite_eq_right hrp]

theorem heapSwapMem_pos {mem : ℕ → ℕ} {loc : SelectHeapLoc} {size p q e : ℕ}
    (hb : SelectHeapBijection mem loc size) (hp : p < size) (hq : q < size) (he : e < loc.cap)
    (hpq : p ≠ q) :
    heapSwapMem mem loc p q (loc.posPtr + e) =
      if e = mem (loc.arrPtr + p) then q + 1
      else if e = mem (loc.arrPtr + q) then p + 1
      else mem (loc.posPtr + e) := by
  unfold heapSwapMem
  have hneE : mem (loc.arrPtr + p) ≠ mem (loc.arrPtr + q) := fun h => hpq (hb.arr_inj hp hq h)
  by_cases hep : e = mem (loc.arrPtr + p)
  · subst hep; simp
  · rw [Function.update_of_ne (by omega), ite_eq_right hep]
    by_cases heq : e = mem (loc.arrPtr + q)
    · subst heq; simp
    · rw [Function.update_of_ne (by omega), ite_eq_right heq]
      have h1 : loc.posPtr + e ≠ loc.arrPtr + q := by
        unfold SelectHeapLoc.posPtr; have := hb.1; omega
      have h2 : loc.posPtr + e ≠ loc.arrPtr + p := by
        unfold SelectHeapLoc.posPtr; have := hb.1; omega
      rw [Function.update_of_ne h1, Function.update_of_ne h2]

/-- Swapping two distinct valid positions `p ≠ q` preserves `SelectHeapBijection`, `SelectHeapKeysValid`,
`SelectHeapHeaderAt`, and `SelectHeapCandLists`. -/
theorem heapSwapMem_preserves_struct {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h size p q : ℕ}
    (hhdr : SelectHeapHeaderAt mem loc size)
    (hb : SelectHeapBijection mem loc size)
    (hk : SelectHeapKeysValid mem loc h)
    (hc : SelectHeapCandLists mem loc)
    (hp : p < size) (hq : q < size) (hpq : p ≠ q) :
    let m' := heapSwapMem mem loc p q
    SelectHeapHeaderAt m' loc size ∧
    SelectHeapBijection m' loc size ∧
    SelectHeapKeysValid m' loc h ∧
    SelectHeapCandLists m' loc := by
  dsimp only
  have hpCap : p < loc.cap := lt_of_lt_of_le hp hb.1
  have hqCap : q < loc.cap := lt_of_lt_of_le hq hb.1
  have hepCap : mem (loc.arrPtr + p) < loc.cap := hb.2.1 p hp
  have heqCap : mem (loc.arrPtr + q) < loc.cap := hb.2.1 q hq
  have hout (a : ℕ) (ha : a < loc.arrPtr ∨ loc.lvlPtr ≤ a) : heapSwapMem mem loc p q a = mem a :=
    heapSwapMem_eq_of_outside hpCap hqCap hepCap heqCap ha
  have hpos_nz (e : ℕ) (he : e < loc.cap) :
      heapSwapMem mem loc p q (loc.posPtr + e) ≠ 0 ↔ mem (loc.posPtr + e) ≠ 0 := by
    rw [heapSwapMem_pos hb hp hq he hpq]
    split_ifs with h1 h2
    · subst h1; simp [hb.pos_arr_ne_zero hp]
    · subst h2; simp [hb.pos_arr_ne_zero hq]
    · rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    exact (hout _ (Or.inl (by unfold SelectHeapLoc.arrPtr shHdrSize; simpa using hj))).trans (hhdr j hj)
  · refine ⟨hb.1, ?_, ?_, ?_⟩
    · intro r hr
      rw [heapSwapMem_arr (lt_of_lt_of_le hr hb.1) hpq]
      split_ifs <;> [exact hepCap; exact heqCap; exact hb.2.1 r hr]
    · intro r hr
      rw [heapSwapMem_arr (lt_of_lt_of_le hr hb.1) hpq]
      by_cases hrq : r = q
      · subst r; simp only [↓reduceIte]; rw [heapSwapMem_pos hb hp hq hepCap hpq]; simp
      · rw [ite_eq_right hrq]
        by_cases hrp : r = p
        · subst r; simp only [↓reduceIte]; rw [heapSwapMem_pos hb hp hq heqCap hpq]
          have hne : mem (loc.arrPtr + q) ≠ mem (loc.arrPtr + p) := fun h => hpq (hb.arr_inj hp hq h.symm)
          simp [hne]
        · rw [ite_eq_right hrp]
          have hrCap := hb.2.1 r hr
          rw [heapSwapMem_pos hb hp hq hrCap hpq]
          have hne1 : mem (loc.arrPtr + r) ≠ mem (loc.arrPtr + p) := fun h => hrp (hb.arr_inj hr hp h)
          have hne2 : mem (loc.arrPtr + r) ≠ mem (loc.arrPtr + q) := fun h => hrq (hb.arr_inj hr hq h)
          simp [hne1, hne2, hb.2.2.1 r hr]
    · intro e he
      rw [heapSwapMem_pos hb hp hq he hpq]
      by_cases h1 : e = mem (loc.arrPtr + p)
      · subst h1; simp only [↓reduceIte]
        refine Or.inr ⟨by omega, ?_⟩
        rw [Nat.add_sub_cancel, heapSwapMem_arr hqCap hpq]; simp
      · rw [ite_eq_right h1]
        by_cases h2 : e = mem (loc.arrPtr + q)
        · subst h2; simp only [↓reduceIte]
          refine Or.inr ⟨by omega, ?_⟩
          rw [Nat.add_sub_cancel, heapSwapMem_arr hpCap hpq]
          simp [hpq]
        · rw [ite_eq_right h2]
          rcases hb.2.2.2 e he with h0 | ⟨hle, harr⟩
          · exact Or.inl h0
          · refine Or.inr ⟨hle, ?_⟩
            have hsizeCap := hb.1
            have hidx_ne_p : mem (loc.posPtr + e) - 1 ≠ p := by
              intro heq; rw [heq] at harr; exact h1 harr.symm
            have hidx_ne_q : mem (loc.posPtr + e) - 1 ≠ q := by
              intro heq; rw [heq] at harr; exact h2 harr.symm
            rw [heapSwapMem_arr (by omega) hpq]
            simp [hidx_ne_q, hidx_ne_p, harr]
  · intro e he hnz
    have hnz0 := (hpos_nz e he).mp hnz
    obtain ⟨hlvl, hvn, hvd, hdp⟩ := hk e he hnz0
    have hlvlEq : heapSwapMem mem loc p q (loc.lvlPtr + e) = mem (loc.lvlPtr + e) :=
      hout _ (Or.inr (by omega))
    have hnumEq : ∀ k < loc.Lk, heapSwapMem mem loc p q (loc.numBase + e * loc.Lk + k) =
        mem (loc.numBase + e * loc.Lk + k) := fun k _ =>
      hout _ (Or.inr (by unfold SelectHeapLoc.numBase SelectHeapLoc.candNext SelectHeapLoc.candPrev
                          SelectHeapLoc.candHead; omega))
    have hdenEq : ∀ k < loc.Lk, heapSwapMem mem loc p q (loc.denBase + e * loc.Lk + k) =
        mem (loc.denBase + e * loc.Lk + k) := fun k _ =>
      hout _ (Or.inr (by unfold SelectHeapLoc.denBase SelectHeapLoc.numBase SelectHeapLoc.candNext
                          SelectHeapLoc.candPrev SelectHeapLoc.candHead; omega))
    refine ⟨hlvlEq.trans_le hlvl,
      fun k hk => (hnumEq k hk).trans_lt (hvn k hk),
      fun k hk => (hdenEq k hk).trans_lt (hvd k hk), ?_⟩
    unfold SelectHeapLoc.readDen; rw [Num.intVal_congr hdenEq]; exact hdp
  · obtain ⟨lists, hlists⟩ := hc
    refine ⟨lists, fun i hi => ?_⟩
    obtain ⟨hdll, hiff⟩ := hlists i hi
    refine ⟨hdll.of_agree
      (hout _ (Or.inr (by unfold SelectHeapLoc.candHead; omega)))
      (fun e _ => hout _ (Or.inr (by unfold SelectHeapLoc.candPrev SelectHeapLoc.candHead; omega)))
      (fun e _ => hout _ (Or.inr (by unfold SelectHeapLoc.candNext SelectHeapLoc.candPrev SelectHeapLoc.candHead; omega))),
      fun e => ?_⟩
    rw [hiff e]
    constructor
    · rintro ⟨heCap, hnz, hlvl⟩
      exact ⟨heCap, (hpos_nz e heCap).mpr hnz, (hout _ (Or.inr (by omega))).trans hlvl⟩
    · rintro ⟨heCap, hnz, hlvl⟩
      exact ⟨heCap, (hpos_nz e heCap).mp hnz, (hout _ (Or.inr (by omega))).symm.trans hlvl⟩

private lemma heapSwapMem_edgeBetter {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h p q : ℕ}
    (hpCap : p < loc.cap) (hqCap : q < loc.cap)
    (hepCap : mem (loc.arrPtr + p) < loc.cap) (heqCap : mem (loc.arrPtr + q) < loc.cap)
    (e₁ e₂ : ℕ) :
    loc.edgeBetter (heapSwapMem mem loc p q) h e₁ e₂ = loc.edgeBetter mem h e₁ e₂ := by
  have hnumEq (e j : ℕ) :
      heapSwapMem mem loc p q (loc.numBase + e * loc.Lk + j) = mem (loc.numBase + e * loc.Lk + j) :=
    heapSwapMem_eq_of_outside hpCap hqCap hepCap heqCap (Or.inr (by
      unfold SelectHeapLoc.numBase SelectHeapLoc.candNext SelectHeapLoc.candPrev SelectHeapLoc.candHead
      omega))
  have hdenEq (e j : ℕ) :
      heapSwapMem mem loc p q (loc.denBase + e * loc.Lk + j) = mem (loc.denBase + e * loc.Lk + j) :=
    heapSwapMem_eq_of_outside hpCap hqCap hepCap heqCap (Or.inr (by
      unfold SelectHeapLoc.denBase SelectHeapLoc.numBase SelectHeapLoc.candNext SelectHeapLoc.candPrev
        SelectHeapLoc.candHead
      omega))
  unfold SelectHeapLoc.edgeBetter SelectHeapLoc.readNum SelectHeapLoc.readDen
  rw [Num.intVal_congr (fun j _ => hnumEq e₁ j), Num.intVal_congr (fun j _ => hdenEq e₁ j),
      Num.intVal_congr (fun j _ => hnumEq e₂ j), Num.intVal_congr (fun j _ => hdenEq e₂ j)]

/-- One sift-up swap of `k > 0` with `par = (k - 1) / 2` when `arr[k]` beats `arr[par]`
advances `SelectHeapOrderExceptUp` from `k` to `par`. -/
theorem siftUp_swap_step {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h size k : ℕ}
    (hb : SelectHeapBijection mem loc size) (hk : SelectHeapKeysValid mem loc h)
    (hexc : SelectHeapOrderExceptUp mem loc h size k) (hk0 : 0 < k)
    (hbeat : loc.edgeBetter mem h (mem (loc.arrPtr + k)) (mem (loc.arrPtr + (k - 1) / 2)) = true) :
    SelectHeapOrderExceptUp (heapSwapMem mem loc ((k - 1) / 2) k) loc h size ((k - 1) / 2) := by
  let par := (k - 1) / 2
  have hpar_lt_k : par < k := by dsimp only [par]; omega
  have hpar_lt : par < size := lt_trans hpar_lt_k hexc.1
  have hne : par ≠ k := ne_of_lt hpar_lt_k
  have hpCap : par < loc.cap := lt_of_lt_of_le hpar_lt hb.1
  have hkCap : k < loc.cap := lt_of_lt_of_le hexc.1 hb.1
  have hepCap := hb.2.1 par hpar_lt
  have hekCap := hb.2.1 k hexc.1
  have hEdgeEq := heapSwapMem_edgeBetter (h := h) hpCap hkCap hepCap hekCap
  refine ⟨hpar_lt, ?_, ?_⟩
  · intro p hp0 hp hppar
    rw [hEdgeEq, heapSwapMem_arr (lt_of_lt_of_le (by omega : (p - 1) / 2 < size) hb.1) hne,
        heapSwapMem_arr (lt_of_lt_of_le hp hb.1) hne]
    by_cases hpk : p = k
    · subst p
      have h1 : (k - 1) / 2 = par := rfl
      simp only [h1, hne, ↓reduceIte]
      exact hbeat
    · rw [ite_eq_right hpk, ite_eq_right hppar]
      by_cases hppk : (p - 1) / 2 = k
      · simp only [hppk, ↓reduceIte]
        exact hexc.2.2 hk0 p hp hppk
      · rw [ite_eq_right hppk]
        by_cases hppp : (p - 1) / 2 = par
        · simp only [hppp, ↓reduceIte]
          have h1 := hexc.2.1 p hp0 hp hpk
          rw [hppp] at h1
          have hdK := (hk _ hekCap (hb.pos_arr_ne_zero hexc.1)).2.2.2
          have hdPar := (hk _ hepCap (hb.pos_arr_ne_zero hpar_lt)).2.2.2
          have hdP := (hk _ (hb.2.1 p hp) (hb.pos_arr_ne_zero hp)).2.2.2
          exact keyBetter_trans_pos hdK hdPar hdP hbeat h1
        · rw [ite_eq_right hppp]
          exact hexc.2.1 p hp0 hp hpk
  · intro hpar0 c hc hcp
    rw [hEdgeEq,
        heapSwapMem_arr (lt_of_lt_of_le (by omega : (par - 1) / 2 < size) hb.1) hne,
        heapSwapMem_arr (lt_of_lt_of_le hc hb.1) hne]
    have hgp_ne_k : (par - 1) / 2 ≠ k := by omega
    have hgp_ne_par : (par - 1) / 2 ≠ par := by omega
    rw [ite_eq_right hgp_ne_k, ite_eq_right hgp_ne_par]
    have hc_ne_par : c ≠ par := by omega
    rw [ite_eq_right hc_ne_par]
    by_cases hck : c = k
    · simp only [hck, ↓reduceIte]
      exact hexc.2.1 par hpar0 hpar_lt hne
    · rw [ite_eq_right hck]
      have h1 := hexc.2.1 par hpar0 hpar_lt hne
      have h2 := hexc.2.1 c (by omega) hc hck
      rw [hcp] at h2
      have hdGP := (hk _ (hb.2.1 _ (by omega : (par - 1) / 2 < size))
        (hb.pos_arr_ne_zero (by omega))).2.2.2
      have hdPar := (hk _ hepCap (hb.pos_arr_ne_zero hpar_lt)).2.2.2
      have hdC := (hk _ (hb.2.1 c hc) (hb.pos_arr_ne_zero hc)).2.2.2
      exact keyBetter_trans_pos hdGP hdPar hdC h1 h2

/-- When `siftUp` stops (either `k = 0` or `arr[k]` does not beat `arr[(k - 1) / 2]`),
`SelectHeapOrderExceptUp` implies full `SelectHeapOrder`. -/
theorem selectHeapOrder_of_exceptUp_stop {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h size k : ℕ}
    (hb : SelectHeapBijection mem loc size)
    (hexc : SelectHeapOrderExceptUp mem loc h size k)
    (hstop : k = 0 ∨ loc.edgeBetter mem h (mem (loc.arrPtr + k)) (mem (loc.arrPtr + (k - 1) / 2)) = false) :
    SelectHeapOrder mem loc h size := by
  intro p hp0 hp
  by_cases hpk : p = k
  · subst hpk
    rcases hstop with rfl | hfalse
    · omega
    · have hne : mem (loc.arrPtr + (p - 1) / 2) ≠ mem (loc.arrPtr + p) := fun heq => by
        have := hb.arr_inj (by omega) hp heq; omega
      rcases keyBetter_total_of_ne (n₁ := loc.readNum mem h (mem (loc.arrPtr + (p - 1) / 2)))
          (d₁ := loc.readDen mem h (mem (loc.arrPtr + (p - 1) / 2)))
          (n₂ := loc.readNum mem h (mem (loc.arrPtr + p)))
          (d₂ := loc.readDen mem h (mem (loc.arrPtr + p))) hne with h1 | h2
      · exact h1
      · change loc.edgeBetter mem h (mem (loc.arrPtr + p)) (mem (loc.arrPtr + (p - 1) / 2)) = true at h2
        rw [hfalse] at h2; cases h2
  · exact hexc.2.1 p hp0 hp hpk

/-- One sift-down swap of `k` with its best child `best` (which satisfies `(best - 1) / 2 = k`,
beats `arr[k]`, and beats any sibling child of `k`) advances `SelectHeapOrderExceptDown` from `k`
to `best`. -/
theorem siftDown_swap_step {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h size k best : ℕ}
    (hb : SelectHeapBijection mem loc size)
    (hexc : SelectHeapOrderExceptDown mem loc h size k)
    (hbest0 : 0 < best) (hbest_lt : best < size) (hbest_par : (best - 1) / 2 = k)
    (hbeatK : loc.edgeBetter mem h (mem (loc.arrPtr + best)) (mem (loc.arrPtr + k)) = true)
    (hbeatSib : ∀ c, c < size → (c - 1) / 2 = k → c ≠ best →
      loc.edgeBetter mem h (mem (loc.arrPtr + best)) (mem (loc.arrPtr + c)) = true) :
    SelectHeapOrderExceptDown (heapSwapMem mem loc k best) loc h size best := by
  have hk_lt_best : k < best := by omega
  have hne : k ≠ best := ne_of_lt hk_lt_best
  have hkCap : k < loc.cap := lt_of_lt_of_le hexc.1 hb.1
  have hbCap : best < loc.cap := lt_of_lt_of_le hbest_lt hb.1
  have hekCap := hb.2.1 k hexc.1
  have hebCap := hb.2.1 best hbest_lt
  have hEdgeEq := heapSwapMem_edgeBetter (h := h) hkCap hbCap hekCap hebCap
  refine ⟨hbest_lt, ?_, ?_⟩
  · intro p hp0 hp hpp_ne_best
    rw [hEdgeEq,
        heapSwapMem_arr (lt_of_lt_of_le (by omega : (p - 1) / 2 < size) hb.1) hne,
        heapSwapMem_arr (lt_of_lt_of_le hp hb.1) hne]
    rw [ite_eq_right hpp_ne_best]
    by_cases hppk : (p - 1) / 2 = k
    · simp only [hppk, ↓reduceIte]
      by_cases hpb : p = best
      · subst hpb; simp only [↓reduceIte]; exact hbeatK
      · rw [ite_eq_right hpb, ite_eq_right (by omega : p ≠ k)]
        exact hbeatSib p hp hppk hpb
    · rw [ite_eq_right hppk]
      have hpb : p ≠ best := fun h => hppk (h ▸ hbest_par)
      rw [ite_eq_right hpb]
      by_cases hpk : p = k
      · subst hpk; simp only [↓reduceIte]
        exact hexc.2.2 hp0 best hbest_lt hbest_par
      · rw [ite_eq_right hpk]
        exact hexc.2.1 p hp0 hp hppk
  · intro _ c hc hcb
    rw [hEdgeEq,
        heapSwapMem_arr (lt_of_lt_of_le (by omega : (best - 1) / 2 < size) hb.1) hne,
        heapSwapMem_arr (lt_of_lt_of_le hc hb.1) hne]
    rw [hbest_par]
    simp only [hne, ↓reduceIte]
    have hcb_ne : c ≠ best := by omega
    have hck_ne : c ≠ k := by omega
    rw [ite_eq_right hcb_ne, ite_eq_right hck_ne]
    have h1 := hexc.2.1 c (by omega) hc (by omega)
    rw [hcb] at h1
    exact h1

/-- When `siftDown` stops (no child of `k` beats `arr[k]`), `SelectHeapOrderExceptDown` implies
full `SelectHeapOrder`. -/
theorem selectHeapOrder_of_exceptDown_stop {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h size k : ℕ}
    (hb : SelectHeapBijection mem loc size)
    (hexc : SelectHeapOrderExceptDown mem loc h size k)
    (hstop : ∀ c, c < size → (c - 1) / 2 = k →
      loc.edgeBetter mem h (mem (loc.arrPtr + c)) (mem (loc.arrPtr + k)) = false) :
    SelectHeapOrder mem loc h size := by
  intro p hp0 hp
  by_cases hppk : (p - 1) / 2 = k
  · rw [hppk]
    have hfalse := hstop p hp hppk
    have hne : mem (loc.arrPtr + k) ≠ mem (loc.arrPtr + p) := fun heq => by
      have := hb.arr_inj hexc.1 hp heq; omega
    rcases keyBetter_total_of_ne (n₁ := loc.readNum mem h (mem (loc.arrPtr + k)))
        (d₁ := loc.readDen mem h (mem (loc.arrPtr + k)))
        (n₂ := loc.readNum mem h (mem (loc.arrPtr + p)))
        (d₂ := loc.readDen mem h (mem (loc.arrPtr + p))) hne with h1 | h2
    · exact h1
    · change loc.edgeBetter mem h (mem (loc.arrPtr + p)) (mem (loc.arrPtr + k)) = true at h2
      rw [hfalse] at h2; cases h2
  · exact hexc.2.1 p hp0 hp hppk

end MinCostFlow.MinRatio
