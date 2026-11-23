module

public import MinCostFlow.DynSpanner.Defs
public import MinCostFlow.DynSpanner.PrefixWalk
public import MinCostFlow.DynSpanner.RebuildSpec
public import MinCostFlow.DynSpanner.StepInv
public import MinCostFlow.DynSpanner.StepTransition
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import MinCostFlow.DynSpanner.Program.EmbLayouts

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dynamic Spanner Memory Layout (`StateLayout`)

Defines the Word-RAM memory layout `DynSpannerStateAt` representing `DynSpannerState L` inside
a contiguous fixed block `[b, b + dsFixedSize L vCap eCap)` plus dynamically allocated walks and
intrusive/linked lists inside `metaFoot b x`:

* Scalar header (`dsHdrSize = 6`): `q, t, L, vCap, eCap, genCnt`.
* Embedded dynamic graphs (`DynGraphAt`): `G` at `dsGPtr`, `H` at `dsHPtr`, scratch `aux` at
  `dsAuxPtr`.
* Partitioned level spanner buckets (`minH`, `hNext`, `hPrev`, `hHead`, `hDegDummy`): `minH[e]` is
  `0` if `e ∉ H.E` and `i + 1` for the minimum level `i` with `e ∈ (H_level i).E`; each bucket is a
  1-indexed `IsDoublyLinkedList` maintaining `⋃_{i ≥ j} hBuckets i = H_mid_union.E \ H_{< j}.E`.
* Generation-stamped domains `inDom` (`domGen`, `edgeDomGen`), walk pointers `Pi_level` (`piPtr`),
  per-level reverse vertex incidence buckets (`revGen`, `revHead`), and generation-stamped touched
  vertex sets `S_level` (`sGen`, `vSGen`, `sHead`).
* Reusable `O(1)`-cleared scratch stamps (`sBit`, `vStamp`, `eStamp`, `keptStamp`, `mEmbTemp`).

Also proves `DynSpannerStateAt.of_agree`, `unionEdgesLt_iff_minH`, and the `RevHistoryInv`
theorems connecting `revLists` to `affectedEdges` coverage and `vcongBound` geometric sums.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## Layout offsets and sizes -/

def dsQOff : ℕ := 0
def dsTOff : ℕ := 1
def dsLOff : ℕ := 2
def dsVCapOff : ℕ := 3
def dsECapOff : ℕ := 4
def dsGenOff : ℕ := 5
def dsHdrSize : ℕ := 6

def dsGPtr (b : ℕ) : ℕ := b + dsHdrSize

def dsHPtr (b vCap eCap : ℕ) : ℕ := dsGPtr b + dynGraphSize vCap eCap

def dsAuxPtr (b vCap eCap : ℕ) : ℕ := dsHPtr b vCap eCap + dynGraphSize vCap eCap

def dsMinHBase (b vCap eCap : ℕ) : ℕ := dsAuxPtr b vCap eCap + dynGraphSize vCap eCap

def dsHNextBase (b vCap eCap : ℕ) : ℕ := dsMinHBase b vCap eCap + eCap

def dsHPrevBase (b vCap eCap : ℕ) : ℕ := dsHNextBase b vCap eCap + eCap

def dsHHeadBase (b vCap eCap : ℕ) : ℕ := dsHPrevBase b vCap eCap + eCap

def dsHDegDummyBase (b L vCap eCap : ℕ) : ℕ := dsHHeadBase b vCap eCap + (L + 1)

def dsDomGenBase (b L vCap eCap : ℕ) : ℕ := dsHDegDummyBase b L vCap eCap + (L + 1)

def dsEdgeDomGenBase (b L vCap eCap : ℕ) : ℕ := dsDomGenBase b L vCap eCap + (L + 1)

def dsPiPtrBase (b L vCap eCap : ℕ) : ℕ := dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap

def dsRevGenBase (b L vCap eCap : ℕ) : ℕ := dsPiPtrBase b L vCap eCap + (L + 1) * eCap

def dsRevHeadBase (b L vCap eCap : ℕ) : ℕ := dsRevGenBase b L vCap eCap + (L + 1) * vCap

def dsSGenBase (b L vCap eCap : ℕ) : ℕ := dsRevHeadBase b L vCap eCap + (L + 1) * vCap

def dsVSGenBase (b L vCap eCap : ℕ) : ℕ := dsSGenBase b L vCap eCap + (L + 1)

def dsSHeadBase (b L vCap eCap : ℕ) : ℕ := dsVSGenBase b L vCap eCap + (L + 1) * vCap

def dsSBitBase (b L vCap eCap : ℕ) : ℕ := dsSHeadBase b L vCap eCap + (L + 1)

def dsVStampBase (b L vCap eCap : ℕ) : ℕ := dsSBitBase b L vCap eCap + vCap

def dsEStampBase (b L vCap eCap : ℕ) : ℕ := dsVStampBase b L vCap eCap + vCap

def dsKeptStampBase (b L vCap eCap : ℕ) : ℕ := dsEStampBase b L vCap eCap + eCap

def dsMEmbTempBase (b L vCap eCap : ℕ) : ℕ := dsKeptStampBase b L vCap eCap + eCap

def dsFixedSize (L vCap eCap : ℕ) : ℕ := dsMEmbTempBase 0 L vCap eCap + eCap

lemma dsFixedSize_add (b L vCap eCap : ℕ) :
    dsMEmbTempBase b L vCap eCap + eCap = b + dsFixedSize L vCap eCap := by
  simp only [dsFixedSize, dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
    dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase,
    dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase, dsMinHBase, dsAuxPtr,
    dsHPtr, dsGPtr]
  omega

lemma dsGPtr_ge (b : ℕ) : b ≤ dsGPtr b := by simp [dsGPtr]

lemma dsFixedSize_ge_aux (b L vCap eCap : ℕ) :
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap := by
  rw [← dsFixedSize_add]
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase, dsSHeadBase,
    dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase,
    dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase, dsMinHBase]
  omega

lemma dsFixedSize_pos (L vCap eCap : ℕ) : 16 ≤ dsFixedSize L vCap eCap := by
  simp only [dsFixedSize, dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
    dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase,
    dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase, dsMinHBase, dsAuxPtr,
    dsHPtr, dsGPtr, dsHdrSize, dynGraphSize]
  omega

lemma dsMinHBase_eq (b vCap eCap : ℕ) :
    dsMinHBase b vCap eCap = b + dsHdrSize + 3 * dynGraphSize vCap eCap := by
  simp only [dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega

lemma dsDomGenBase_eq (b L vCap eCap : ℕ) :
    dsDomGenBase b L vCap eCap = dsMinHBase b vCap eCap + (3 * eCap + 2 * (L + 1)) := by
  simp only [dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase]; omega

lemma dsRevGenBase_eq (b L vCap eCap : ℕ) :
    dsRevGenBase b L vCap eCap =
      dsDomGenBase b L vCap eCap + ((L + 1) + 2 * ((L + 1) * eCap)) := by
  simp only [dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; omega

lemma dsRevHeadBase_eq (b L vCap eCap : ℕ) :
    dsRevHeadBase b L vCap eCap = dsRevGenBase b L vCap eCap + (L + 1) * vCap := rfl

lemma dsVStampBase_eq (b L vCap eCap : ℕ) :
    dsVStampBase b L vCap eCap =
      dsRevHeadBase b L vCap eCap + (2 * ((L + 1) * vCap) + (2 * (L + 1) + vCap)) := by
  simp only [dsVStampBase, dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase]; omega

/-! ## Concrete metadata, footprint, and linked lists -/

/-- Empty `MGraph` used for scratch `auxPtr` between calls. -/
def emptyMGraph : MGraph :=
  { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 }

lemma emptyMGraph_isValid : emptyMGraph.IsValid := by
  intro _ he; cases he

/-- Singly-linked list of 2-word `[val, next]` nodes (`0` = nil) whose cells all satisfy
`foot`. -/
def LinkedListIn (foot : ℕ → Prop) (mem : ℕ → ℕ) (head : ℕ) : List ℕ → Prop
  | [] => head = 0
  | x :: xs => 0 < head ∧ foot head ∧ foot (head + 1) ∧ mem head = x ∧
      LinkedListIn foot mem (mem (head + 1)) xs

lemma LinkedListIn.of_agree {foot : ℕ → Prop} {mem mem' : ℕ → ℕ}
    (hagree : ∀ a, foot a → mem' a = mem a) :
    ∀ {head : ℕ} {xs : List ℕ},
      LinkedListIn foot mem head xs → LinkedListIn foot mem' head xs
  | _, [], rfl => rfl
  | head, _ :: xs, ⟨hpos, hf0, hf1, hval, hrest⟩ => by
    refine ⟨hpos, hf0, hf1, (hagree head hf0).trans hval, ?_⟩
    rw [hagree (head + 1) hf1]
    exact LinkedListIn.of_agree hagree hrest

lemma LinkedListIn.mono {foot₁ foot₂ : ℕ → Prop} {mem : ℕ → ℕ}
    (hsub : ∀ a, foot₁ a → foot₂ a) :
    ∀ {head : ℕ} {xs : List ℕ},
      LinkedListIn foot₁ mem head xs → LinkedListIn foot₂ mem head xs
  | _, [], rfl => rfl
  | _, _ :: _, ⟨hpos, hf0, hf1, hval, hrest⟩ =>
    ⟨hpos, hsub _ hf0, hsub _ hf1, hval, LinkedListIn.mono hsub hrest⟩

lemma LinkedListIn.cons_disjoint {foot : ℕ → Prop} {mem mem' : ℕ → ℕ} {p x oldHead : ℕ}
    {xs : List ℕ}
    (hL : LinkedListIn foot mem oldHead xs)
    (hp0 : 0 < p) (hvx : mem' p = x) (hvn : mem' (p + 1) = oldHead)
    (hagree : ∀ a, foot a → mem' a = mem a) :
    LinkedListIn (fun a => foot a ∨ a = p ∨ a = p + 1) mem' p (x :: xs) := by
  refine ⟨hp0, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), hvx, ?_⟩
  rw [hvn]
  exact (hL.of_agree hagree).mono fun _ h => Or.inl h

/-- Ghost metadata accompanying a `DynSpannerState L` in memory. -/
structure DynSpannerMeta (L : ℕ) where
  vCap : ℕ
  eCap : ℕ
  intervals : List (ℕ × ℕ)
  hBuckets : Fin (L + 1) → List ℕ
  memInDom : Fin (L + 1) → Finset ℕ
  revLists : Fin (L + 1) → ℕ → List ℕ
  sLists : Fin (L + 1) → List ℕ

/-- Dynamic heap footprint of `x : DynSpannerMeta L`: cells allocated in `[b + dsFixedSize, ∞)`
recorded by `x.intervals` (`MWalkAt` and `LinkedListIn` nodes live strictly here). -/
def heapFoot {L : ℕ} (x : DynSpannerMeta L) (a : ℕ) : Prop :=
  ∃ iv ∈ x.intervals, iv.1 ≤ a ∧ a < iv.2

/-- Footprint of `x : DynSpannerMeta L` rooted at `b`: fixed array block `[b, b + dsFixedSize)`
together with all dynamic heap intervals in `x.intervals`. -/
def metaFoot {L : ℕ} (b : ℕ) (x : DynSpannerMeta L) (a : ℕ) : Prop :=
  (b ≤ a ∧ a < b + dsFixedSize L x.vCap x.eCap) ∨ heapFoot x a

lemma heapFoot_subset_metaFoot {L : ℕ} {b : ℕ} {x : DynSpannerMeta L} {a : ℕ}
    (ha : heapFoot x a) : metaFoot b x a := Or.inr ha

/-- Every cell `[lo, hi)` belongs to `heapFoot x`. -/
def RangeInHeapFoot {L : ℕ} (x : DynSpannerMeta L) (lo hi : ℕ) : Prop :=
  ∀ a, lo ≤ a → a < hi → heapFoot x a

lemma rangeInHeapFoot_of_interval {L : ℕ} {lo hi lo0 hi0 : ℕ} {x : DynSpannerMeta L}
    (hiv : (lo0, hi0) ∈ x.intervals) (hlo : lo0 ≤ lo) (hhi : hi ≤ hi0) :
    RangeInHeapFoot x lo hi := fun _ ha0 ha1 =>
  ⟨(lo0, hi0), hiv, le_trans hlo ha0, lt_of_lt_of_le ha1 hhi⟩

lemma metaFoot_append_mono {L : ℕ} {b : ℕ} {x x' : DynSpannerMeta L}
    (hv : x'.vCap = x.vCap) (he : x'.eCap = x.eCap)
    (hsub : ∀ iv ∈ x.intervals, iv ∈ x'.intervals) :
    ∀ a, metaFoot b x a → metaFoot b x' a := fun a ha => by
  rcases ha with ⟨h1, h2⟩ | ⟨iv, hiv, h1, h2⟩
  · exact Or.inl ⟨h1, by rw [hv, he]; exact h2⟩
  · exact Or.inr ⟨iv, hsub iv hiv, h1, h2⟩

/-! ## Complete state representation invariant `DynSpannerStateAt` -/

/-- Full Word-RAM memory invariant tying `DynSpannerState L` (`q, t, G, H_level, Pi_level, inDom,
S_level, H`) and metadata `x : DynSpannerMeta L` to base pointer `b` in memory `mem`. -/
def DynSpannerStateAt (L vCap eCap b : ℕ) (mem : ℕ → ℕ)
    (x : DynSpannerMeta L) (st : DynSpannerState L) : Prop :=
  x.vCap = vCap ∧
  x.eCap = eCap ∧
  (∀ iv ∈ x.intervals, b + dsFixedSize L vCap eCap ≤ iv.1) ∧
  1 ≤ b ∧
  st.G.IsValid ∧
  st.H.IsValid ∧
  st.H.V = st.G.V ∧
  st.H.E ⊆ st.G.E ∧
  (∀ e ∈ st.H.E, st.H.tail e = st.G.tail e ∧ st.H.head e = st.G.head e) ∧
  (∀ v ∈ st.G.V, v < vCap) ∧
  (∀ e ∈ st.G.E, e < eCap) ∧
  -- Header scalars
  mem (b + dsQOff) = st.q ∧
  mem (b + dsTOff) = st.t ∧
  mem (b + dsLOff) = L ∧
  mem (b + dsVCapOff) = vCap ∧
  mem (b + dsECapOff) = eCap ∧
  1 ≤ mem (b + dsGenOff) ∧
  -- Dynamic graphs `G`, `H`, and empty scratch `aux`
  DynGraphAt mem (dsGPtr b) vCap eCap st.G ∧
  DynGraphAt mem (dsHPtr b vCap eCap) vCap eCap st.H ∧
  DynGraphAt mem (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph ∧
  -- Partitioned `minH` and doubly-linked `hBuckets`
  (∀ e < eCap,
    (mem (dsMinHBase b vCap eCap + e) = 0 ↔ e ∉ st.H.E) ∧
    (e ∈ st.H.E → ∃ i : Fin (L + 1),
      mem (dsMinHBase b vCap eCap + e) = i.1 + 1 ∧
      e ∈ (st.H_level i).E ∧
      ∀ k : Fin (L + 1), k.1 < i.1 → e ∉ (st.H_level k).E)) ∧
  (∀ i : Fin (L + 1),
    IsDoublyLinkedList mem (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
      (dsHHeadBase b vCap eCap + i.1) eCap (x.hBuckets i) ∧
    mem (dsHDegDummyBase b L vCap eCap + i.1) = (x.hBuckets i).length ∧
    (∀ e, e ∈ x.hBuckets i ↔ e ∈ st.H.E ∧ mem (dsMinHBase b vCap eCap + e) = i.1 + 1)) ∧
  -- Generation-stamped `inDom`, `Pi_level`, and `revLists`
  (∀ i : Fin (L + 1),
    mem (dsDomGenBase b L vCap eCap + i.1) ≤ mem (b + dsGenOff) ∧
    (∀ e < eCap,
      mem (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) ≤ mem (b + dsGenOff) ∧
      ((0 < mem (dsDomGenBase b L vCap eCap + i.1) ∧
        mem (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) =
          mem (dsDomGenBase b L vCap eCap + i.1)) ↔ e ∈ x.memInDom i)) ∧
    (∀ e ∈ x.memInDom i, e < eCap) ∧
    st.inDom i = x.memInDom i ∩ st.G.E ∧
    (∀ e ∈ st.inDom i,
      let ptr := mem (dsPiPtrBase b L vCap eCap + i.1 * eCap + e)
      MWalkAt mem ptr (st.Pi_level i e) ∧
      RangeInHeapFoot x ptr (ptr + (mWalkEncode (st.Pi_level i e)).length)) ∧
    (∀ v < vCap,
      mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem (b + dsGenOff) ∧
      (x.revLists i v).Nodup ∧
      (∀ e ∈ x.revLists i v, e < eCap ∧ e ∈ x.memInDom i) ∧
      (if 0 < mem (dsDomGenBase b L vCap eCap + i.1) ∧
          mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) =
            mem (dsDomGenBase b L vCap eCap + i.1)
       then LinkedListIn (heapFoot x) mem
              (mem (dsRevHeadBase b L vCap eCap + i.1 * vCap + v)) (x.revLists i v)
       else x.revLists i v = []))) ∧
  -- Generation-stamped `S_level` and `sLists`
  (∀ i : Fin (L + 1),
    mem (dsSGenBase b L vCap eCap + i.1) ≤ mem (b + dsGenOff) ∧
    (∀ v ∈ st.S_level i, v < vCap) ∧
    (∀ v < vCap,
      mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem (b + dsGenOff) ∧
      ((0 < mem (dsSGenBase b L vCap eCap + i.1) ∧
        mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
          mem (dsSGenBase b L vCap eCap + i.1)) ↔ v ∈ st.S_level i)) ∧
    (x.sLists i).Nodup ∧
    (∀ v, v ∈ x.sLists i ↔ v ∈ st.S_level i) ∧
    (if 0 < mem (dsSGenBase b L vCap eCap + i.1)
     then LinkedListIn (heapFoot x) mem
            (mem (dsSHeadBase b L vCap eCap + i.1)) (x.sLists i)
     else x.sLists i = [])) ∧
  -- Clean temporary arrays
  (∀ v < vCap, mem (dsSBitBase b L vCap eCap + v) = 0 ∧
    mem (dsVStampBase b L vCap eCap + v) ≤ mem (b + dsGenOff)) ∧
  (∀ e < eCap, mem (dsEStampBase b L vCap eCap + e) ≤ mem (b + dsGenOff) ∧
    mem (dsKeptStampBase b L vCap eCap + e) ≤ mem (b + dsGenOff))

/-! ## Agreement & footprint frame lemmas -/

lemma dynGraphAt_of_agree {mem mem' : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vCap eCap G)
    (hagree : ∀ addr, a ≤ addr → addr < a + dynGraphSize vCap eCap → mem' addr = mem addr) :
    DynGraphAt mem' a vCap eCap G := by
  have hlt : ∀ d, d < dynGraphSize vCap eCap → mem' (a + d) = mem (a + d) := fun d hd =>
    hagree (a + d) (Nat.le_add_right _ _) (by omega)
  rcases hG with ⟨hval, hvC, heC, h0, h1', h2, h3, hvp, ⟨vL, hv1, hv2, hv3, hv4, hv5⟩,
    heti, hite, hep, ⟨eL, he1, he2, he3, he4, he5⟩, hets, ⟨incL, hincL⟩⟩
  have hGn : G.n ≤ vCap := by
    have hsub : G.V ⊆ Finset.range vCap := fun v hv => Finset.mem_range.mpr (hvC v hv)
    simpa [MGraph.n] using Finset.card_le_card hsub
  have hGm : G.m ≤ eCap := by
    have hsub : G.E ⊆ Finset.range eCap := fun e he => Finset.mem_range.mpr (heC e he)
    simpa [MGraph.m] using Finset.card_le_card hsub
  refine ⟨hval, hvC, heC, ?_, ?_, ?_, ?_, ?_, ⟨vL, hv1, hv2, hv3, ?_, ?_⟩,
    ?_, ?_, ?_, ⟨eL, he1, he2, he3, ?_, ?_⟩, ?_, ⟨incL, fun s hs => ?_⟩⟩
  · simpa [dgVCapOff] using (hlt dgVCapOff (by simp [dgVCapOff, dynGraphSize]; try omega)).trans h0
  · simpa [dgECapOff] using (hlt dgECapOff (by simp [dgECapOff, dynGraphSize]; try omega)).trans h1'
  · simpa [dgNOff] using (hlt dgNOff (by simp [dgNOff, dynGraphSize]; try omega)).trans h2
  · simpa [dgMOff] using (hlt dgMOff (by simp [dgMOff, dynGraphSize]; try omega)).trans h3
  · intro v hv
    simpa only [dgVPresBase, Nat.add_assoc] using
      (hlt (4 + v) (by simp [dynGraphSize]; omega)).trans
        (by simpa [dgVPresBase, Nat.add_assoc] using hvp v hv)
  · intro i hi
    have hi_v : i < vCap := by omega
    simpa only [dgVListBase, Nat.add_assoc] using
      (hlt (4 + vCap + i) (by simp [dynGraphSize]; omega)).trans
        (by simpa [dgVListBase, Nat.add_assoc] using hv4 i hi)
  · intro i hi
    have hv : vL[i] < vCap := hvC _ ((hv3 _).mp (List.getElem_mem hi))
    simpa only [dgVPosBase, Nat.add_assoc] using
      (hlt (4 + 2 * vCap + vL[i]) (by simp [dynGraphSize]; omega)).trans
        (by simpa [dgVPosBase, Nat.add_assoc] using hv5 i hi)
  · intro v hv
    have hvlt := hvC v hv
    have hs1 : mem' (dgExtToIntBase a vCap + v) = mem (dgExtToIntBase a vCap + v) := by
      simpa [dgExtToIntBase, Nat.add_assoc] using hlt (4 + 3 * vCap + v) (by simp [dynGraphSize]; omega)
    rw [hs1]
    have hsi := (heti v hv).1
    have hsilt := hvC _ hsi
    have hs2 : mem' (dgIntToExtBase a vCap + mem (dgExtToIntBase a vCap + v)) =
        mem (dgIntToExtBase a vCap + mem (dgExtToIntBase a vCap + v)) := by
      simpa [dgIntToExtBase, Nat.add_assoc] using
        hlt (4 + 4 * vCap + mem (dgExtToIntBase a vCap + v)) (by simp [dynGraphSize]; omega)
    exact ⟨hsi, hs2.trans (heti v hv).2⟩
  · intro s hs
    have hslt := hvC s hs
    have hs1 : mem' (dgIntToExtBase a vCap + s) = mem (dgIntToExtBase a vCap + s) := by
      simpa [dgIntToExtBase, Nat.add_assoc] using hlt (4 + 4 * vCap + s) (by simp [dynGraphSize]; omega)
    rw [hs1]
    have hsi := (hite s hs).1
    have hsilt := hvC _ hsi
    have hs2 : mem' (dgExtToIntBase a vCap + mem (dgIntToExtBase a vCap + s)) =
        mem (dgExtToIntBase a vCap + mem (dgIntToExtBase a vCap + s)) := by
      simpa [dgExtToIntBase, Nat.add_assoc] using
        hlt (4 + 3 * vCap + mem (dgIntToExtBase a vCap + s)) (by simp [dynGraphSize]; omega)
    exact ⟨hsi, hs2.trans (hite s hs).2⟩
  · intro e he
    simpa only [dgEPresBase, Nat.add_assoc] using
      (hlt (4 + 7 * vCap + e) (by simp [dynGraphSize]; omega)).trans
        (by simpa [dgEPresBase, Nat.add_assoc] using hep e he)
  · intro i hi
    have hi_e : i < eCap := by omega
    simpa only [dgEListBase, Nat.add_assoc] using
      (hlt (4 + 7 * vCap + eCap + i) (by simp [dynGraphSize]; omega)).trans
        (by simpa [dgEListBase, Nat.add_assoc] using he4 i hi)
  · intro i hi
    have he := heC _ ((he3 _).mp (List.getElem_mem hi))
    simpa only [dgEPosBase, Nat.add_assoc] using
      (hlt (4 + 7 * vCap + 2 * eCap + eL[i]) (by simp [dynGraphSize]; omega)).trans
        (by simpa [dgEPosBase, Nat.add_assoc] using he5 i hi)
  · intro e he
    have helt := heC e he
    have htlt := hvC _ (hval e he).1
    have hhlt := hvC _ (hval e he).2
    have h1a : mem' (dgETailSlotBase a vCap eCap + e) = mem (dgETailSlotBase a vCap eCap + e) := by
      simpa [dgETailSlotBase, Nat.add_assoc] using
        hlt (4 + 7 * vCap + 3 * eCap + e) (by simp [dynGraphSize]; omega)
    have h2a : mem' (dgEHeadSlotBase a vCap eCap + e) = mem (dgEHeadSlotBase a vCap eCap + e) := by
      simpa [dgEHeadSlotBase, Nat.add_assoc] using
        hlt (4 + 7 * vCap + 4 * eCap + e) (by simp [dynGraphSize]; omega)
    have h3a : mem' (dgExtToIntBase a vCap + G.tail e) = mem (dgExtToIntBase a vCap + G.tail e) := by
      simpa [dgExtToIntBase, Nat.add_assoc] using
        hlt (4 + 3 * vCap + G.tail e) (by simp [dynGraphSize]; omega)
    have h4a : mem' (dgExtToIntBase a vCap + G.head e) = mem (dgExtToIntBase a vCap + G.head e) := by
      simpa [dgExtToIntBase, Nat.add_assoc] using
        hlt (4 + 3 * vCap + G.head e) (by simp [dynGraphSize]; omega)
    rw [h1a, h2a, h3a, h4a]
    exact hets e he
  · rcases hincL s hs with ⟨hdll, hdeg, hmem⟩
    have hh : mem' (dgIncHeadBase a vCap + s) = mem (dgIncHeadBase a vCap + s) := by
      simpa [dgIncHeadBase, Nat.add_assoc] using hlt (4 + 6 * vCap + s) (by simp [dynGraphSize]; omega)
    have hd : mem' (dgSlotDegBase a vCap + s) = mem (dgSlotDegBase a vCap + s) := by
      simpa [dgSlotDegBase, Nat.add_assoc] using hlt (4 + 5 * vCap + s) (by simp [dynGraphSize]; omega)
    have hdll' : IsDoublyLinkedList mem' (dgHePrevBase a vCap eCap) (dgHeNextBase a vCap eCap)
        (dgIncHeadBase a vCap + s) (2 * eCap) (incL s) := by
      refine hdll.of_agree hh (fun h hh_mem => ?_) (fun h hh_mem => ?_)
      · have hhlt := hdll.2.1 h hh_mem
        simpa [dgHePrevBase, Nat.add_assoc] using
          hlt (4 + 7 * vCap + 5 * eCap + h) (by simp [dynGraphSize]; omega)
      · have hhlt := hdll.2.1 h hh_mem
        simpa [dgHeNextBase, Nat.add_assoc] using
          hlt (4 + 7 * vCap + 7 * eCap + h) (by simp [dynGraphSize]; omega)
    refine ⟨hdll', hd.trans hdeg, fun h => ?_⟩
    rw [hmem h]
    by_cases hhlt : h < 2 * eCap
    · have hh2lt : h / 2 < eCap := by omega
      have hts : mem' (dgETailSlotBase a vCap eCap + h / 2) =
          mem (dgETailSlotBase a vCap eCap + h / 2) := by
        simpa [dgETailSlotBase, Nat.add_assoc] using
          hlt (4 + 7 * vCap + 3 * eCap + h / 2) (by simp [dynGraphSize]; omega)
      have hhs : mem' (dgEHeadSlotBase a vCap eCap + h / 2) =
          mem (dgEHeadSlotBase a vCap eCap + h / 2) := by
        simpa [dgEHeadSlotBase, Nat.add_assoc] using
          hlt (4 + 7 * vCap + 4 * eCap + h / 2) (by simp [dynGraphSize]; omega)
      simp [hhlt, hts, hhs]
    · simp [hhlt]

/-- `DynSpannerStateAt` is local to `metaFoot b x`: changing memory outside `metaFoot b x`
preserves the full representation. -/
theorem DynSpannerStateAt.of_agree {L vCap eCap b : ℕ} {mem mem' : ℕ → ℕ}
    {x : DynSpannerMeta L} {st : DynSpannerState L}
    (hS : DynSpannerStateAt L vCap eCap b mem x st)
    (hagree : ∀ a, metaFoot b x a → mem' a = mem a) :
    DynSpannerStateAt L vCap eCap b mem' x st := by
  rcases hS with ⟨hxV, hxE, hiv_min, hb1, hGV, hHV, hHVG, hHEG, hHEnds, hvC, heC,
    hq, ht, hL, hvCm, heCm, hgen1, hG, hH, hAux, hminH, hhB, hInDom, hSL, hSBit, hES⟩
  have hfx : ∀ a, b ≤ a → a < b + dsFixedSize L vCap eCap → mem' a = mem a := fun a ha1 ha2 =>
    hagree a (Or.inl ⟨ha1, by rw [hxV, hxE]; exact ha2⟩)
  have hagree_heap : ∀ a, heapFoot x a → mem' a = mem a := fun a ha =>
    hagree a (Or.inr ha)
  have hgen_eq : mem' (b + dsGenOff) = mem (b + dsGenOff) :=
    hfx _ (by simp [dsGenOff]) (by have := dsFixedSize_pos L vCap eCap; simp [dsGenOff]; omega)
  refine ⟨hxV, hxE, hiv_min, hb1, hGV, hHV, hHVG, hHEG, hHEnds, hvC, heC, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hfx _ (by simp [dsQOff]) (by have := dsFixedSize_pos L vCap eCap; simp [dsQOff]; omega)).trans hq
  · exact (hfx _ (by simp [dsTOff]) (by have := dsFixedSize_pos L vCap eCap; simp [dsTOff]; omega)).trans ht
  · exact (hfx _ (by simp [dsLOff]) (by have := dsFixedSize_pos L vCap eCap; simp [dsLOff]; omega)).trans hL
  · exact (hfx _ (by simp [dsVCapOff]) (by have := dsFixedSize_pos L vCap eCap; simp [dsVCapOff]; omega)).trans hvCm
  · exact (hfx _ (by simp [dsECapOff]) (by have := dsFixedSize_pos L vCap eCap; simp [dsECapOff]; omega)).trans heCm
  · rwa [hgen_eq]
  · refine dynGraphAt_of_agree hG fun a ha1 ha2 => hfx a (le_trans (by simp [dsGPtr]) ha1) ?_
    have : dsGPtr b + dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap := by
      rw [← dsFixedSize_add]
      simp only [dsGPtr, dsHPtr, dsAuxPtr, dsMinHBase, dsHNextBase, dsHPrevBase, dsHHeadBase,
        dsHDegDummyBase, dsDomGenBase, dsEdgeDomGenBase, dsPiPtrBase, dsRevGenBase, dsRevHeadBase,
        dsSGenBase, dsVSGenBase, dsSHeadBase, dsSBitBase, dsVStampBase, dsEStampBase,
        dsKeptStampBase, dsMEmbTempBase]
      omega
    omega
  · refine dynGraphAt_of_agree hH fun a ha1 ha2 => hfx a ?_ ?_
    · have : b ≤ dsHPtr b vCap eCap := by simp only [dsHPtr, dsGPtr]; omega
      omega
    · have : dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap := by
        rw [← dsFixedSize_add]
        simp only [dsHPtr, dsAuxPtr, dsMinHBase, dsHNextBase, dsHPrevBase, dsHHeadBase,
          dsHDegDummyBase, dsDomGenBase, dsEdgeDomGenBase, dsPiPtrBase, dsRevGenBase, dsRevHeadBase,
          dsSGenBase, dsVSGenBase, dsSHeadBase, dsSBitBase, dsVStampBase, dsEStampBase,
          dsKeptStampBase, dsMEmbTempBase]
        omega
      omega
  · refine dynGraphAt_of_agree hAux fun a ha1 ha2 => hfx a ?_ ?_
    · have : b ≤ dsAuxPtr b vCap eCap := by simp only [dsAuxPtr, dsHPtr, dsGPtr]; omega
      omega
    · have := dsFixedSize_ge_aux b L vCap eCap
      omega
  · intro e he
    have hm : mem' (dsMinHBase b vCap eCap + e) = mem (dsMinHBase b vCap eCap + e) := by
      refine hfx _ ?_ ?_
      · simp only [dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
      · rw [← dsFixedSize_add]
        simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
          dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
          dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase]
        omega
    rw [hm]; exact hminH e he
  · intro i
    rcases hhB i with ⟨hdll, hdeg, hmem⟩
    have hh : mem' (dsHHeadBase b vCap eCap + i.1) = mem (dsHHeadBase b vCap eCap + i.1) := by
      refine hfx _ ?_ ?_
      · simp only [dsHHeadBase, dsHPrevBase, dsHNextBase, dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
      · rw [← dsFixedSize_add]
        simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
          dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
          dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase]
        have hi := i.2
        omega
    have hd : mem' (dsHDegDummyBase b L vCap eCap + i.1) = mem (dsHDegDummyBase b L vCap eCap + i.1) := by
      refine hfx _ ?_ ?_
      · simp only [dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase, dsMinHBase, dsAuxPtr,
          dsHPtr, dsGPtr]; omega
      · rw [← dsFixedSize_add]
        simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
          dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
          dsEdgeDomGenBase, dsDomGenBase]
        have hi := i.2
        omega
    refine ⟨?_, hd.trans hdeg, fun e => ?_⟩
    · refine hdll.of_agree hh (fun e he => ?_) (fun e he => ?_)
      · have helt := hdll.2.1 e he
        refine hfx _ ?_ ?_
        · simp only [dsHPrevBase, dsHNextBase, dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
        · rw [← dsFixedSize_add]
          simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
            dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
            dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase]
          omega
      · have helt := hdll.2.1 e he
        refine hfx _ ?_ ?_
        · simp only [dsHNextBase, dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
        · rw [← dsFixedSize_add]
          simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
            dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
            dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase]
          omega
    · rw [hmem e]
      by_cases he : e ∈ st.H.E
      · have helt := heC e (hHEG he)
        have hm : mem' (dsMinHBase b vCap eCap + e) = mem (dsMinHBase b vCap eCap + e) := by
          refine hfx _ ?_ ?_
          · simp only [dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
          · rw [← dsFixedSize_add]
            simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
              dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
              dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase]
            omega
        simp [he, hm]
      · simp [he]
  · intro i
    rcases hInDom i with ⟨hdg, hed, hmSub, hInEq, hWalks, hRev⟩
    have hi : i.1 < L + 1 := i.2
    have hdg_eq : mem' (dsDomGenBase b L vCap eCap + i.1) = mem (dsDomGenBase b L vCap eCap + i.1) := by
      refine hfx _ ?_ ?_
      · simp only [dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase,
          dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
      · rw [← dsFixedSize_add]
        simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
          dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
          dsEdgeDomGenBase]
        omega
    refine ⟨?_, ?_, hmSub, hInEq, ?_, ?_⟩
    · rwa [hdg_eq, hgen_eq]
    · intro e he
      have hedge_eq : mem' (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) =
          mem (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) := by
        refine hfx _ ?_ ?_
        · simp only [dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase,
            dsHNextBase, dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
        · rw [← dsFixedSize_add]
          simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
            dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase]
          have hmul : i.1 * eCap + e < (L + 1) * eCap := by
            nlinarith [i.2]
          omega
      rw [hedge_eq, hgen_eq, hdg_eq]
      exact hed e he
    · intro e he
      have helt : e < eCap := hmSub e (Finset.mem_inter.mp (hInEq ▸ he)).1
      have hptr_eq : mem' (dsPiPtrBase b L vCap eCap + i.1 * eCap + e) =
          mem (dsPiPtrBase b L vCap eCap + i.1 * eCap + e) := by
        refine hfx _ ?_ ?_
        · simp only [dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase,
            dsHPrevBase, dsHNextBase, dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
        · rw [← dsFixedSize_add]
          simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
            dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase]
          have hmul : i.1 * eCap + e < (L + 1) * eCap := by nlinarith [i.2]
          omega
      rcases hWalks e he with ⟨hw, hr⟩
      dsimp only
      rw [hptr_eq]
      refine ⟨?_, hr⟩
      intro j hj
      have ha : heapFoot x (mem (dsPiPtrBase b L vCap eCap + i.1 * eCap + e) + j) :=
        hr _ (Nat.le_add_right _ _) (by omega)
      rw [hagree_heap _ ha]
      exact hw j hj
    · intro v hv
      rcases hRev v hv with ⟨hrg, hnd, hmem, hll⟩
      have hrg_eq : mem' (dsRevGenBase b L vCap eCap + i.1 * vCap + v) =
          mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) := by
        refine hfx _ ?_ ?_
        · simp only [dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase,
            dsHHeadBase, dsHPrevBase, dsHNextBase, dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
        · rw [← dsFixedSize_add]
          simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
            dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase]
          have hmul : i.1 * vCap + v < (L + 1) * vCap := by nlinarith [i.2]
          omega
      have hrh_eq : mem' (dsRevHeadBase b L vCap eCap + i.1 * vCap + v) =
          mem (dsRevHeadBase b L vCap eCap + i.1 * vCap + v) := by
        refine hfx _ ?_ ?_
        · simp only [dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase,
            dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase, dsMinHBase, dsAuxPtr, dsHPtr,
            dsGPtr]; omega
        · rw [← dsFixedSize_add]
          simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
            dsSHeadBase, dsVSGenBase, dsSGenBase]
          have hmul : i.1 * vCap + v < (L + 1) * vCap := by nlinarith [i.2]
          omega
      refine ⟨by rwa [hrg_eq, hgen_eq], hnd, hmem, ?_⟩
      rw [hdg_eq, hrg_eq, hrh_eq]
      split_ifs at hll ⊢ with hcond
      · exact hll.of_agree hagree_heap
      · exact hll
  · intro i
    rcases hSL i with ⟨hsg, hvS, hvsg, hnd, hmem, hll⟩
    have hi : i.1 < L + 1 := i.2
    have hsg_eq : mem' (dsSGenBase b L vCap eCap + i.1) = mem (dsSGenBase b L vCap eCap + i.1) := by
      refine hfx _ ?_ ?_
      · simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase,
          dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase, dsMinHBase,
          dsAuxPtr, dsHPtr, dsGPtr]; omega
      · rw [← dsFixedSize_add]
        simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
          dsSHeadBase, dsVSGenBase]
        omega
    have hsh_eq : mem' (dsSHeadBase b L vCap eCap + i.1) = mem (dsSHeadBase b L vCap eCap + i.1) := by
      refine hfx _ ?_ ?_
      · simp only [dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
          dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase,
          dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
      · rw [← dsFixedSize_add]
        simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase]
        omega
    refine ⟨by rwa [hsg_eq, hgen_eq], hvS, ?_, hnd, hmem, ?_⟩
    · intro v hv
      have hv_eq : mem' (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
          mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) := by
        refine hfx _ ?_ ?_
        · simp only [dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
            dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase,
            dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
        · rw [← dsFixedSize_add]
          simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
            dsSHeadBase]
          have hmul : i.1 * vCap + v < (L + 1) * vCap := by nlinarith [i.2]
          omega
      rw [hv_eq, hgen_eq, hsg_eq]
      exact hvsg v hv
    · rw [hsg_eq, hsh_eq]
      split_ifs at hll ⊢ with hcond
      · exact hll.of_agree hagree_heap
      · exact hll
  · intro v hv
    have hs_eq : mem' (dsSBitBase b L vCap eCap + v) = mem (dsSBitBase b L vCap eCap + v) := by
      refine hfx _ ?_ ?_
      · simp only [dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase,
          dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase,
          dsHNextBase, dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
      · rw [← dsFixedSize_add]
        simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase]; omega
    have hv_eq : mem' (dsVStampBase b L vCap eCap + v) = mem (dsVStampBase b L vCap eCap + v) := by
      refine hfx _ ?_ ?_
      · simp only [dsVStampBase, dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase,
          dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase,
          dsHPrevBase, dsHNextBase, dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
      · rw [← dsFixedSize_add]
        simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase]; omega
    rw [hs_eq, hv_eq, hgen_eq]; exact hSBit v hv
  · intro e he
    have he1 : mem' (dsEStampBase b L vCap eCap + e) = mem (dsEStampBase b L vCap eCap + e) := by
      refine hfx _ ?_ ?_
      · simp only [dsEStampBase, dsVStampBase, dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase,
          dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase,
          dsHHeadBase, dsHPrevBase, dsHNextBase, dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr]; omega
      · rw [← dsFixedSize_add]
        simp only [dsMEmbTempBase, dsKeptStampBase]; omega
    have he2 : mem' (dsKeptStampBase b L vCap eCap + e) = mem (dsKeptStampBase b L vCap eCap + e) := by
      refine hfx _ ?_ ?_
      · simp only [dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase, dsSHeadBase, dsVSGenBase,
          dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase,
          dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase, dsMinHBase, dsAuxPtr, dsHPtr,
          dsGPtr]; omega
      · rw [← dsFixedSize_add]
        simp only [dsMEmbTempBase]; omega
    rw [he1, he2, hgen_eq]; exact hES e he

/-! ## Level union and reverse-index bridge lemmas -/

lemma unionEdgesLt_iff_minH {L vCap eCap b : ℕ} {mem : ℕ → ℕ}
    {st : DynSpannerState L}
    (hH_eq : st.H.E = unionEdgesLt st.H_level (L + 1))
    (hminH : ∀ e < eCap,
      (mem (dsMinHBase b vCap eCap + e) = 0 ↔ e ∉ st.H.E) ∧
      (e ∈ st.H.E → ∃ i : Fin (L + 1),
        mem (dsMinHBase b vCap eCap + e) = i.1 + 1 ∧
        e ∈ (st.H_level i).E ∧
        ∀ k : Fin (L + 1), k.1 < i.1 → e ∉ (st.H_level k).E))
    {e j : ℕ} (he : e < eCap) :
    e ∈ unionEdgesLt st.H_level j ↔
      0 < mem (dsMinHBase b vCap eCap + e) ∧ mem (dsMinHBase b vCap eCap + e) ≤ j := by
  constructor
  · intro heu
    simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at heu
    rcases heu with ⟨k, hkj, hek⟩
    have heH : e ∈ st.H.E := by
      rw [hH_eq]
      simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨k, k.2, hek⟩
    obtain ⟨i, hi_eq, _, hi_min⟩ := (hminH e he).2 heH
    have hik : ¬ k.1 < i.1 := fun hlt => hi_min k hlt hek
    rw [hi_eq]
    omega
  · rintro ⟨hm_pos, hm_le⟩
    have heH : e ∈ st.H.E := by
      by_contra hnot
      have := (hminH e he).1.mpr hnot
      omega
    obtain ⟨i, hi_eq, hei, _⟩ := (hminH e he).2 heH
    rw [hi_eq] at hm_le
    simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, by omega, hei⟩

/-- History invariant tying each active level `i`'s memory `memInDom i` and reverse vertex buckets
`revLists i v` to the exact build timestamp `lastRebuild q L i k`. -/
def RevHistoryInv {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (us : List Update) (k : ℕ) (x : DynSpannerMeta L) : Prop :=
  ∀ i : Fin (L + 1),
    let ti := lastRebuild q L i.1 k
    let st_ti := runState (L := L) G₀ q sparsify us ti
    x.memInDom i = st_ti.inDom i ∧
    ∀ v < x.vCap, ∀ e,
      e ∈ x.revLists i v ↔
        e ∈ st_ti.inDom i ∧ v ∈ st_ti.H.walkVertices (st_ti.G.tail e) (st_ti.Pi_level i e)

/-- At `k = 0`, `lastRebuild q L i 0 = 0`, so level `0` covers `G₀.E` with `Pi₀` walks in `H₀`
and levels `i > 0` have `memInDom i = ∅` and `revLists i v = []`. -/
theorem revHistoryInv_zero {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (us : List Update) {x : DynSpannerMeta L}
    (hm0 : x.memInDom ⟨0, Nat.zero_lt_succ L⟩ = G₀.E)
    (hr0 : ∀ v < x.vCap, ∀ e,
      e ∈ x.revLists ⟨0, Nat.zero_lt_succ L⟩ v ↔
        e ∈ G₀.E ∧
        v ∈ (init G₀ L q sparsify).state.H.walkVertices (G₀.tail e)
              ((init G₀ L q sparsify).state.Pi_level ⟨0, Nat.zero_lt_succ L⟩ e))
    (hmi : ∀ i : Fin (L + 1), 0 < i.1 → x.memInDom i = ∅)
    (hri : ∀ i : Fin (L + 1), 0 < i.1 → ∀ v < x.vCap, x.revLists i v = []) :
    RevHistoryInv G₀ q sparsify us 0 x := by
  intro i
  have hti : lastRebuild q L i.1 0 = 0 := by simp [lastRebuild]
  change x.memInDom i = (runState G₀ q sparsify us (lastRebuild q L i.1 0)).inDom i ∧ _
  rw [hti]
  by_cases hi0 : i.1 = 0
  · have hi_eq : i = ⟨0, Nat.zero_lt_succ L⟩ := Fin.ext hi0
    subst hi_eq
    simpa [runState, init, initAt] using ⟨hm0, hr0⟩
  · have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero hi0
    have hi_ne : i ≠ 0 := fun h => hi0 (congrArg Fin.val h)
    constructor
    · rw [hmi i hi_pos]
      simp [runState, init, initAt, hi_ne]
    · intro v hv e
      rw [hri i hi_pos v hv]
      simp [runState, init, initAt, hi_ne]

/-- Under `RevHistoryInv` and `SnapInv` at all `≤ k`, each reverse bucket length is bounded by
`vcongBound P.γ_c P.γ_ℓ G₀.maxDeg i.1`. -/
theorem revLists_card_le_vcongBound {L q mMax : ℕ} {P : SparsifyParams}
    {G₀ : MGraph} {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    {us : List Update} {k : ℕ} {x : DynSpannerMeta L}
    (hVG₀ : G₀.IsValid) (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    (hq1 : 1 ≤ q)
    (hAll : ∀ s ≤ k, SnapInv G₀ L q mMax P sparsify us s)
    (hRev : RevHistoryInv G₀ q sparsify us k x)
    {i : Fin (L + 1)} {v : ℕ} (hv : v < x.vCap)
    (hnd : (x.revLists i v).Nodup) :
    ((x.revLists i v).length : ℝ) ≤ vcongBound P.γ_c P.γ_ℓ G₀.maxDeg i.1 := by
  have hγc : 0 ≤ P.γ_c := by linarith [P.hγ_c]
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  have hv_nn : 0 ≤ vcongBound P.γ_c P.γ_ℓ G₀.maxDeg i.1 :=
    vcongBound_nonneg hγc hγl G₀.maxDeg i.1
  set ti := lastRebuild q L i.1 k
  have hti_le : ti ≤ k := lastRebuild_le q L i.1 k
  have hSnap := hAll ti hti_le
  set st_ti := runState (L := L) G₀ q sparsify us ti
  obtain ⟨_, hmem⟩ := hRev i
  have hcho := lastRebuild_chooseLevel_le (q := q) (L := L) (i := i.1) (t := k) hq1 (by omega)
  have hGti_valid : st_ti.G.IsValid := by
    rw [hSnap.G_eq]
    obtain ⟨hBV_ti, hds_ti, _⟩ := batchIsValid_take us G₀ ti hBV hds
    exact (batch_delOrSplit_invariants (us.take ti) G₀ hVG₀ hBV_ti hds_ti).1
  have hG_eq : st_ti.G = G₀.applyBatch (us.take ti) := hSnap.G_eq
  have hHV_eq : st_ti.H.V = st_ti.G.V := by rw [hSnap.H_V, ← hG_eq]
  have hH_sub_G : st_ti.G.IsSubgraph st_ti.H := by
    have h := hSnap.H_sub
    change (G₀.applyBatch (us.take ti)).IsSubgraph st_ti.H at h
    rwa [← hG_eq] at h
  have hinDom_sub : st_ti.inDom i ⊆ st_ti.G.E := by
    have h := hSnap.inDom_sub i
    change st_ti.inDom i ⊆ (G₀.applyBatch (us.take ti)).E at h
    rwa [← hG_eq] at h
  have hinDom0 : st_ti.inDom ⟨0, Nat.zero_lt_succ L⟩ = st_ti.G.E := by
    have h := hSnap.inDom0
    change st_ti.inDom ⟨0, Nat.zero_lt_succ L⟩ = (G₀.applyBatch (us.take ti)).E at h
    rwa [← hG_eq] at h
  set H_le := unionGraphLt st_ti.G st_ti.H_level (i.1 + 1)
  have hEmb : Embedding.IsEmbedding (piLe st_ti i.1) st_ti.G H_le := by
    have h := hSnap.emb_at i hcho
    change Embedding.IsEmbedding (piLe st_ti i.1) (G₀.applyBatch (us.take ti))
      (unionGraphLt (G₀.applyBatch (us.take ti)) st_ti.H_level (i.1 + 1)) at h
    rwa [← hG_eq] at h
  have hVc : Embedding.vcong (piLe st_ti i.1) st_ti.G H_le (fun _ => 1) ≤
      vcongBound P.γ_c P.γ_ℓ G₀.maxDeg i.1 := by
    have h := hSnap.vcong_at i hcho
    change Embedding.vcong (piLe st_ti i.1) (G₀.applyBatch (us.take ti))
      (unionGraphLt (G₀.applyBatch (us.take ti)) st_ti.H_level (i.1 + 1)) (fun _ => 1) ≤
      vcongBound P.γ_c P.γ_ℓ G₀.maxDeg i.1 at h
    rwa [← hG_eq] at h
  have hH_sub_Hle : st_ti.H.IsSubgraph H_le := by
    refine ⟨hHV_eq.symm.subset, ?_, ?_⟩
    · intro e he
      rw [hSnap.H_E]
      exact unionEdgesLt_mono _ (Nat.succ_le_of_lt i.2) he
    · intro e he
      have heH : e ∈ st_ti.H.E := by
        rw [hSnap.H_E]
        exact unionEdgesLt_mono _ (Nat.succ_le_of_lt i.2) he
      exact ⟨(hH_sub_G.2.2 e heH).1.symm, (hH_sub_G.2.2 e heH).2.symm⟩
  by_cases hvG : v ∈ st_ti.H.V
  · have hsub : (x.revLists i v).toFinset ⊆
        st_ti.G.E.filter fun e => v ∈ H_le.walkVertices (st_ti.G.tail e) (piLe st_ti i.1 e) := by
      intro e he
      rw [List.mem_toFinset] at he
      obtain ⟨he_dom, hv_w⟩ := (hmem v hv e).mp he
      have heG : e ∈ st_ti.G.E := hinDom_sub he_dom
      have he_eq : st_ti.Pi_level i e = piLe st_ti i.1 e := by
        by_cases hi0 : i.1 = 0
        · have hi_eq : i = ⟨0, Nat.zero_lt_succ L⟩ := Fin.ext hi0
          subst hi_eq
          simp [piLe, piLt, piLtFrom_one]
        · exact (piLtFrom_eq_self_of_mem st_ti.Pi_level st_ti.inDom
            (hinDom0 ▸ heG) he_dom).symm
      rw [he_eq] at hv_w
      have hw := hEmb.2 e heG
      have hvw : st_ti.H.walkVertices (st_ti.G.tail e) (piLe st_ti i.1 e) =
          H_le.walkVertices (st_ti.G.tail e) (piLe st_ti i.1 e) :=
        walkVertices_of_isSubgraph hH_sub_Hle hw
      refine Finset.mem_filter.mpr ⟨heG, ?_⟩
      rwa [← hvw]
    have hv_Hle : v ∈ H_le.V := hHV_eq ▸ hvG
    have hcard_le : ((x.revLists i v).length : ℝ) ≤
        Embedding.vcongAt (piLe st_ti i.1) st_ti.G H_le (fun _ => 1) v := by
      have hc1 : (x.revLists i v).length = (x.revLists i v).toFinset.card :=
        (List.toFinset_card_of_nodup hnd).symm
      have hc2 : (x.revLists i v).toFinset.card ≤
          (st_ti.G.E.filter fun e => v ∈ H_le.walkVertices (st_ti.G.tail e) (piLe st_ti i.1 e)).card :=
        Finset.card_le_card hsub
      have hc3 : ((st_ti.G.E.filter fun e =>
          v ∈ H_le.walkVertices (st_ti.G.tail e) (piLe st_ti i.1 e)).card : ℝ) =
          Embedding.vcongAt (piLe st_ti i.1) st_ti.G H_le (fun _ => 1) v := by
        simp [Embedding.vcongAt]
      exact le_trans (Nat.cast_le.mpr (hc1 ▸ hc2)) (le_of_eq hc3)
    have hvc_le : Embedding.vcongAt (piLe st_ti i.1) st_ti.G H_le (fun _ => 1) v ≤
        Embedding.vcong (piLe st_ti i.1) st_ti.G H_le (fun _ => 1) := by
      unfold Embedding.vcong
      have hVne : H_le.V.Nonempty := ⟨v, hv_Hle⟩
      simp only [hVne, ↓reduceDIte]
      exact Finset.le_sup' (fun z => Embedding.vcongAt (piLe st_ti i.1) st_ti.G H_le (fun _ => 1) z)
        hv_Hle
    exact le_trans hcard_le (le_trans hvc_le hVc)
  · have hnil : x.revLists i v = [] := by
      by_contra hne
      rcases List.exists_mem_of_ne_nil _ hne with ⟨e, he⟩
      obtain ⟨he_dom, hv_w⟩ := (hmem v hv e).mp he
      have heG := hinDom_sub he_dom
      have he_eq : st_ti.Pi_level i e = piLe st_ti i.1 e := by
        by_cases hi0 : i.1 = 0
        · have hi_eq : i = ⟨0, Nat.zero_lt_succ L⟩ := Fin.ext hi0
          subst hi_eq; simp [piLe, piLt, piLtFrom_one]
        · exact (piLtFrom_eq_self_of_mem st_ti.Pi_level st_ti.inDom
            (hinDom0 ▸ heG) he_dom).symm
      have hw := hEmb.2 e heG
      have hvw : st_ti.H.walkVertices (st_ti.G.tail e) (piLe st_ti i.1 e) =
          H_le.walkVertices (st_ti.G.tail e) (piLe st_ti i.1 e) :=
        walkVertices_of_isSubgraph hH_sub_Hle hw
      have hv_Hle : v ∈ H_le.walkVertices (st_ti.G.tail e) (piLe st_ti i.1 e) := by
        rw [← hvw, ← he_eq]; exact hv_w
      have hVH : H_le.IsValid := by
        intro e' he'
        have he'' : e' ∈ st_ti.H.E := by
          rw [hSnap.H_E]; exact unionEdgesLt_mono _ (Nat.succ_le_of_lt i.2) he'
        have hv1 := hSnap.H_valid e' he''
        change st_ti.H.tail e' ∈ st_ti.H.V ∧ st_ti.H.head e' ∈ st_ti.H.V at hv1
        have hte := (hH_sub_G.2.2 e' he'').1
        have hhe := (hH_sub_G.2.2 e' he'').2
        change st_ti.G.tail e' ∈ st_ti.G.V ∧ st_ti.G.head e' ∈ st_ti.G.V
        rw [← hte, ← hhe, ← hHV_eq]
        exact hv1
      have hmemV := IsWalk.walkVertices_mem_V hVH hw (hEmb.1 (hGti_valid e heG).1) v hv_Hle
      exact hvG (hHV_eq ▸ hmemV)
    rw [hnil]
    simpa using hv_nn

end

end MinCostFlow.DynSpanner.Program
