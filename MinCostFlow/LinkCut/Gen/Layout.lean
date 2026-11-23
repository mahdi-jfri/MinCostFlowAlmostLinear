module

public import MinCostFlow.LinkCut.SplayModel
public import WordRAM.Contract

/-!
# Node records in memory, for any payload

The functional model `SplayState α σ τ` keeps, for each node, four pointers (`left`, `right`,
`par`, `ppar`), a size, a reversal bit, and three payload fields: the value (`α`), the summary
(`σ`) and the lazy tag (`τ`). This file fixes how a machine program keeps these nodes in memory,
for any payload, so that the tree programs (rotate, splay, expose, …) can be written and proved
once.

A `NodeLayout` says how wide each payload field is and which memory blocks hold which payload
value. The first three words of every value block hold the record width, the value width and the
tag width (`val_hdr`). The programs read these words from the record of node `0`, so one program
text serves every width. Node `x` is a record of `nodeStride` words at `nodeAddr nb x`; the six control words come
first, then the value, summary and tag blocks. `NodeAt` says that the record of `x` holds a given
`SplayNode`, and `NodesAt` says that the records of nodes `0 .. cap` hold the nodes of a state.
The size is kept capped at `4` (`min sz 4`). The only test of a size in the model is `sz ≠ 3` in
`lctCut`, and capped sizes can be added without leaving the word range.

The main results are the update lemmas: writing one control word of node `x` turns `NodesAt` for
`st` into `NodesAt` for `st.setLeft x _` (and so on), and writes outside all records keep
`NodesAt`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM

/-- How payload fields of type `α`, `σ`, `τ` are kept in memory: each field is a block of fixed
width, and a predicate says which value a block holds. A block's value depends only on the cells
of the block, and a copy of the block at another address holds the same value. -/
structure NodeLayout (α σ τ : Type*) where
  valW : ℕ
  sumW : ℕ
  tagW : ℕ
  ValAt : (ℕ → ℕ) → ℕ → α → Prop
  SumAt : (ℕ → ℕ) → ℕ → σ → Prop
  TagAt : (ℕ → ℕ) → ℕ → τ → Prop
  val_move : ∀ m m' a b v, ValAt m a v → (∀ i < valW, m' (b + i) = m (a + i)) → ValAt m' b v
  sum_move : ∀ m m' a b s, SumAt m a s → (∀ i < sumW, m' (b + i) = m (a + i)) → SumAt m' b s
  tag_move : ∀ m m' a b t, TagAt m a t → (∀ i < tagW, m' (b + i) = m (a + i)) → TagAt m' b t
  /-- A value block starts with three layout words: the record width, the value width, and the
  tag width. The programs read them at run time, so their text does not depend on the widths. -/
  val_hdr : ∀ m a v, ValAt m a v →
    m a = 6 + valW + sumW + tagW ∧ m (a + 1) = valW ∧ m (a + 2) = tagW
  val_three : 3 ≤ valW

namespace NodeLayout

variable {α σ τ : Type*} (Lay : NodeLayout α σ τ)

theorem val_congr (m m' : ℕ → ℕ) (a : ℕ) (v : α) (h : Lay.ValAt m a v)
    (hag : ∀ i < Lay.valW, m' (a + i) = m (a + i)) : Lay.ValAt m' a v :=
  Lay.val_move m m' a a v h hag

theorem sum_congr (m m' : ℕ → ℕ) (a : ℕ) (s : σ) (h : Lay.SumAt m a s)
    (hag : ∀ i < Lay.sumW, m' (a + i) = m (a + i)) : Lay.SumAt m' a s :=
  Lay.sum_move m m' a a s h hag

theorem tag_congr (m m' : ℕ → ℕ) (a : ℕ) (t : τ) (h : Lay.TagAt m a t)
    (hag : ∀ i < Lay.tagW, m' (a + i) = m (a + i)) : Lay.TagAt m' a t :=
  Lay.tag_move m m' a a t h hag

/-! Offsets of the fields inside a node record. -/

def OFF_LEFT : ℕ := 0
def OFF_RIGHT : ℕ := 1
def OFF_PAR : ℕ := 2
def OFF_PPAR : ℕ := 3
def OFF_SZ : ℕ := 4
def OFF_REV : ℕ := 5
def OFF_VAL : ℕ := 6
def offSum : ℕ := 6 + Lay.valW
def offTag : ℕ := 6 + Lay.valW + Lay.sumW

/-- Words of one node record. -/
def nodeStride : ℕ := 6 + Lay.valW + Lay.sumW + Lay.tagW

/-- Address of the record of node `x`, with records starting at `nb`. -/
def nodeAddr (nb x : ℕ) : ℕ := nb + Lay.nodeStride * x

/-- The record of node `x` holds `nd`. -/
def NodeAt (mem : ℕ → ℕ) (nb x : ℕ) (nd : SplayNode α σ τ) : Prop :=
  mem (Lay.nodeAddr nb x + OFF_LEFT) = nd.left ∧
  mem (Lay.nodeAddr nb x + OFF_RIGHT) = nd.right ∧
  mem (Lay.nodeAddr nb x + OFF_PAR) = nd.par ∧
  mem (Lay.nodeAddr nb x + OFF_PPAR) = nd.ppar ∧
  mem (Lay.nodeAddr nb x + OFF_SZ) = min nd.sz 4 ∧
  mem (Lay.nodeAddr nb x + OFF_REV) = (if nd.rev then 1 else 0) ∧
  Lay.ValAt mem (Lay.nodeAddr nb x + OFF_VAL) nd.val ∧
  Lay.SumAt mem (Lay.nodeAddr nb x + Lay.offSum) nd.sum ∧
  Lay.TagAt mem (Lay.nodeAddr nb x + Lay.offTag) nd.tag

/-- The records of nodes `0 .. cap` hold the nodes of `st`. -/
def NodesAt (mem : ℕ → ℕ) (nb cap : ℕ) (st : SplayState α σ τ) : Prop :=
  ∀ x ≤ cap, Lay.NodeAt mem nb x (st.nodes x)

/-- The cells of the records of nodes `0 .. cap`. -/
def InRecords (nb cap a : ℕ) : Prop := nb ≤ a ∧ a < Lay.nodeAddr nb (cap + 1)

theorem stride_pos : 6 ≤ Lay.nodeStride := by unfold nodeStride; omega

theorem stride_nine : 9 ≤ Lay.nodeStride := by have := Lay.val_three; unfold nodeStride; omega

/-- A cell of a record lies in exactly one record. -/
theorem addr_disjoint {nb x y i j : ℕ} (hi : i < Lay.nodeStride) (hj : j < Lay.nodeStride)
    (h : Lay.nodeAddr nb x + i = Lay.nodeAddr nb y + j) : x = y ∧ i = j := by
  unfold nodeAddr at h
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have : Lay.nodeStride * x + Lay.nodeStride ≤ Lay.nodeStride * y := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hxy
    omega
  · exact ⟨rfl, by omega⟩
  · have : Lay.nodeStride * y + Lay.nodeStride ≤ Lay.nodeStride * x := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hxy
    omega

/-- The payload blocks of a record depend only on the cells from offset `6` on. -/
theorem payload_keep {mem mem' : ℕ → ℕ} {A : ℕ} {v : α} {sm : σ} {t : τ}
    (hag : ∀ k, 6 ≤ k → k < Lay.nodeStride → mem' (A + k) = mem (A + k))
    (hv : Lay.ValAt mem (A + OFF_VAL) v) (hs : Lay.SumAt mem (A + Lay.offSum) sm)
    (ht : Lay.TagAt mem (A + Lay.offTag) t) :
    Lay.ValAt mem' (A + OFF_VAL) v ∧ Lay.SumAt mem' (A + Lay.offSum) sm ∧
      Lay.TagAt mem' (A + Lay.offTag) t := by
  unfold nodeStride at hag
  refine ⟨Lay.val_congr _ _ _ _ hv fun i hi => ?_, Lay.sum_congr _ _ _ _ hs fun i hi => ?_,
    Lay.tag_congr _ _ _ _ ht fun i hi => ?_⟩
  · have := hag (OFF_VAL + i) (by unfold OFF_VAL; omega) (by unfold OFF_VAL; omega)
    rwa [← Nat.add_assoc] at this
  · have := hag (Lay.offSum + i) (by unfold offSum; omega) (by unfold offSum; omega)
    rwa [← Nat.add_assoc] at this
  · have := hag (Lay.offTag + i) (by unfold offTag; omega) (by unfold offTag; omega)
    rwa [← Nat.add_assoc] at this

/-- A record depends only on its own cells. -/
theorem NodeAt.congr {mem mem' : ℕ → ℕ} {nb x : ℕ} {nd : SplayNode α σ τ}
    (h : Lay.NodeAt mem nb x nd)
    (hag : ∀ i < Lay.nodeStride, mem' (Lay.nodeAddr nb x + i) = mem (Lay.nodeAddr nb x + i)) :
    Lay.NodeAt mem' nb x nd := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hv, hs, ht⟩ := h
  have hS := Lay.stride_pos
  refine ⟨(hag _ (by simp [OFF_LEFT]; omega)).trans h0, (hag _ (by simp [OFF_RIGHT]; omega)).trans h1,
    (hag _ (by simp [OFF_PAR]; omega)).trans h2, (hag _ (by simp [OFF_PPAR]; omega)).trans h3,
    (hag _ (by simp [OFF_SZ]; omega)).trans h4, (hag _ (by simp [OFF_REV]; omega)).trans h5,
    Lay.payload_keep (fun k _ hk => hag k hk) hv hs ht⟩

/-- Writes outside the records keep `NodesAt`. -/
theorem NodesAt.congr {mem mem' : ℕ → ℕ} {nb cap : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hag : ∀ a, Lay.InRecords nb cap a → mem' a = mem a) :
    Lay.NodesAt mem' nb cap st := by
  intro x hx
  refine (h x hx).congr Lay fun i hi => hag _ ⟨by unfold nodeAddr; omega, ?_⟩
  unfold nodeAddr
  have : Lay.nodeStride * x + Lay.nodeStride ≤ Lay.nodeStride * (cap + 1) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- Changing node `x` of the state and the record of `x` in memory, where the new record holds
the new node and all other cells are unchanged, keeps `NodesAt`. -/
theorem NodesAt.update {mem mem' : ℕ → ℕ} {nb cap x : ℕ} {st : SplayState α σ τ}
    {f : SplayNode α σ τ → SplayNode α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap)
    (hnew : Lay.NodeAt mem' nb x (f (st.nodes x)))
    (hother : ∀ a, (∀ i < Lay.nodeStride, a ≠ Lay.nodeAddr nb x + i) → mem' a = mem a) :
    Lay.NodesAt mem' nb cap (st.updateNode x f) := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; simpa using hnew
  · rw [SplayState.nodes_updateNode_ne _ hyx]
    refine (h y hy).congr Lay fun i hi => hother _ fun j hj heq => hyx ?_
    exact (Lay.addr_disjoint hi hj heq).1

/-- Reading a cell of a record after writing one of its cells. -/
theorem upd_read (mem : ℕ → ℕ) (A off v k : ℕ) :
    Function.update mem (A + off) v (A + k) = if k = off then v else mem (A + k) := by
  by_cases h : k = off <;> simp [Function.update_apply, h]

/-- Writing a control word of node `x` keeps every other record. -/
theorem update_other {mem : ℕ → ℕ} {nb x off v a : ℕ} (hoff : off < 6)
    (ha : ∀ i < Lay.nodeStride, a ≠ Lay.nodeAddr nb x + i) :
    Function.update mem (Lay.nodeAddr nb x + off) v a = mem a :=
  Function.update_of_ne (ha off (by have := Lay.stride_pos; omega)) _ _

theorem payload_upd {mem : ℕ → ℕ} {A off v : ℕ} (hoff : off < 6) :
    ∀ k, 6 ≤ k → k < Lay.nodeStride → Function.update mem (A + off) v (A + k) = mem (A + k) :=
  fun k hk _ => by rw [upd_read]; simp only [show k ≠ off by omega, ↓reduceIte]

/-- Writing the capped size `min sz 4` into the size word of `x` represents setting the size of
`x` to `sz`. -/
theorem NodesAt.setSz {mem : ℕ → ℕ} {nb cap x sz : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) :
    Lay.NodesAt (Function.update mem (Lay.nodeAddr nb x + OFF_SZ) (min sz 4)) nb cap
      (st.updateNode x fun nd => { nd with sz := sz }) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hv, hs, ht⟩ := h x hx
  refine h.update Lay hx ?_ fun _ ha => Lay.update_other (by decide) ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Lay.payload_keep (Lay.payload_upd (by decide)) hv hs ht⟩ <;>
    simp only [upd_read] <;> simp [OFF_LEFT, OFF_RIGHT, OFF_PAR, OFF_PPAR, OFF_SZ, OFF_REV] at * <;>
    assumption

/-- Writing `0` into the reversal word of `x` represents clearing the reversal bit of `x`. -/
theorem NodesAt.clearRev {mem : ℕ → ℕ} {nb cap x : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) :
    Lay.NodesAt (Function.update mem (Lay.nodeAddr nb x + OFF_REV) 0) nb cap
      (st.updateNode x fun nd => { nd with rev := false }) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hv, hs, ht⟩ := h x hx
  refine h.update Lay hx ?_ fun _ ha => Lay.update_other (by decide) ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Lay.payload_keep (Lay.payload_upd (by decide)) hv hs ht⟩ <;>
    simp only [upd_read] <;> simp [OFF_LEFT, OFF_RIGHT, OFF_PAR, OFF_PPAR, OFF_SZ, OFF_REV] at * <;>
    assumption

/-- Writing the `left` word of `x` represents `st.setLeft x v`. -/
theorem NodesAt.setLeft {mem : ℕ → ℕ} {nb cap x v : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) :
    Lay.NodesAt (Function.update mem (Lay.nodeAddr nb x + OFF_LEFT) v) nb cap (st.setLeft x v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hv, hs, ht⟩ := h x hx
  refine h.update Lay hx ?_ fun _ ha => Lay.update_other (by decide) ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Lay.payload_keep (Lay.payload_upd (by decide)) hv hs ht⟩ <;>
    simp only [upd_read] <;> simp [OFF_LEFT, OFF_RIGHT, OFF_PAR, OFF_PPAR, OFF_SZ, OFF_REV] at * <;>
    assumption

theorem NodesAt.setRight {mem : ℕ → ℕ} {nb cap x v : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) :
    Lay.NodesAt (Function.update mem (Lay.nodeAddr nb x + OFF_RIGHT) v) nb cap
      (st.setRight x v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hv, hs, ht⟩ := h x hx
  refine h.update Lay hx ?_ fun _ ha => Lay.update_other (by decide) ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Lay.payload_keep (Lay.payload_upd (by decide)) hv hs ht⟩ <;>
    simp only [upd_read] <;> simp [OFF_LEFT, OFF_RIGHT, OFF_PAR, OFF_PPAR, OFF_SZ, OFF_REV] at * <;>
    assumption

theorem NodesAt.setPar {mem : ℕ → ℕ} {nb cap x v : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) :
    Lay.NodesAt (Function.update mem (Lay.nodeAddr nb x + OFF_PAR) v) nb cap (st.setPar x v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hv, hs, ht⟩ := h x hx
  refine h.update Lay hx ?_ fun _ ha => Lay.update_other (by decide) ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Lay.payload_keep (Lay.payload_upd (by decide)) hv hs ht⟩ <;>
    simp only [upd_read] <;> simp [OFF_LEFT, OFF_RIGHT, OFF_PAR, OFF_PPAR, OFF_SZ, OFF_REV] at * <;>
    assumption

theorem NodesAt.setPpar {mem : ℕ → ℕ} {nb cap x v : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) :
    Lay.NodesAt (Function.update mem (Lay.nodeAddr nb x + OFF_PPAR) v) nb cap
      (st.setPpar x v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, hv, hs, ht⟩ := h x hx
  refine h.update Lay hx ?_ fun _ ha => Lay.update_other (by decide) ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Lay.payload_keep (Lay.payload_upd (by decide)) hv hs ht⟩ <;>
    simp only [upd_read] <;> simp [OFF_LEFT, OFF_RIGHT, OFF_PAR, OFF_PPAR, OFF_SZ, OFF_REV] at * <;>
    assumption

/-- The layout words, read from the record of node `0`. -/
theorem NodesAt.stride {mem : ℕ → ℕ} {nb cap : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) : mem (nb + 6) = Lay.nodeStride := by
  have := (Lay.val_hdr _ _ _ (h 0 (Nat.zero_le _)).2.2.2.2.2.2.1).1
  simpa [nodeAddr, OFF_VAL, nodeStride] using this

theorem NodesAt.valW {mem : ℕ → ℕ} {nb cap : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) : mem (nb + 7) = Lay.valW := by
  have := (Lay.val_hdr _ _ _ (h 0 (Nat.zero_le _)).2.2.2.2.2.2.1).2.1
  simpa [nodeAddr, OFF_VAL] using this

theorem NodesAt.tagW {mem : ℕ → ℕ} {nb cap : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) : mem (nb + 8) = Lay.tagW := by
  have := (Lay.val_hdr _ _ _ (h 0 (Nat.zero_le _)).2.2.2.2.2.2.1).2.2
  simpa [nodeAddr, OFF_VAL] using this

/-- Reading the control fields of a represented node. -/
theorem NodesAt.left {mem : ℕ → ℕ} {nb cap x : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) :
    mem (Lay.nodeAddr nb x + OFF_LEFT) = (st.nodes x).left := (h x hx).1

theorem NodesAt.right {mem : ℕ → ℕ} {nb cap x : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) :
    mem (Lay.nodeAddr nb x + OFF_RIGHT) = (st.nodes x).right := (h x hx).2.1

theorem NodesAt.par {mem : ℕ → ℕ} {nb cap x : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) :
    mem (Lay.nodeAddr nb x + OFF_PAR) = (st.nodes x).par := (h x hx).2.2.1

theorem NodesAt.ppar {mem : ℕ → ℕ} {nb cap x : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) :
    mem (Lay.nodeAddr nb x + OFF_PPAR) = (st.nodes x).ppar := (h x hx).2.2.2.1

theorem NodesAt.sz {mem : ℕ → ℕ} {nb cap x : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) :
    mem (Lay.nodeAddr nb x + OFF_SZ) = min (st.nodes x).sz 4 := (h x hx).2.2.2.2.1

theorem NodesAt.rev {mem : ℕ → ℕ} {nb cap x : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) :
    mem (Lay.nodeAddr nb x + OFF_REV) = (if (st.nodes x).rev then 1 else 0) :=
  (h x hx).2.2.2.2.2.1

/-- Writing word `if s then 1 else 0` of `x` sets the right child of `x` if `s`, else the left
child. -/
theorem NodesAt.setSide {mem : ℕ → ℕ} {nb cap x v : ℕ} {st : SplayState α σ τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) (s : Bool) :
    Lay.NodesAt (Function.update mem (Lay.nodeAddr nb x + if s then 1 else 0) v) nb cap
      (if s then st.setRight x v else st.setLeft x v) := by
  cases s
  · exact h.setLeft Lay hx (v := v)
  · exact h.setRight Lay hx (v := v)

end NodeLayout

end MinCostFlow.LinkCut.Gen
