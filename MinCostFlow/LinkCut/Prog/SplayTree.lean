module

public import Mathlib.Data.Nat.Log

namespace MinCostFlow.LinkCut.Prog

/-!
This file develops the pure mathematical theory of generic binary splay trees with
external node weights `vSize : ℕ → ℕ`, lazy reversal, vertex counts, mass sums,
and two-sided minimum-key aggregates (`MinAgg`).

It defines `AuxTree`, subtree sizes `treeSize`, potential `treePhi` using integer
logarithms `Nat.log 2`, rotation steps (`zig`, `zigZig`, `zigZag`), and proves the
integer Sleator–Tarjan potential inequalities via `nat_log_add_le_of_add_le`.
-/

@[expose] public section

/-- Algebraic skeleton of a binary auxiliary tree with node identifiers `id`. -/
inductive AuxTree where
  | leaf : AuxTree
  | node (id : ℕ) (left right : AuxTree) : AuxTree
deriving DecidableEq

/-- Number of internal nodes in an `AuxTree`. -/
def AuxTree.countNodes : AuxTree → ℕ
  | .leaf => 0
  | .node _ l r => 1 + l.countNodes + r.countNodes

/-- List of node identifiers appearing in `t` (in structural left-node-right order). -/
def AuxTree.toList : AuxTree → List ℕ
  | .leaf => []
  | .node id l r => l.toList ++ [id] ++ r.toList

theorem AuxTree.length_toList (t : AuxTree) : t.toList.length = t.countNodes := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr => simp [toList, countNodes, ihl, ihr]; omega

/-- Logical in-order traversal of `t` given node reversal flags `rev` and an inherited
reversal parity `flip`. Under pre-flipped semantics, a node with `rev id = true` has
already had its physical children swapped, so its own reversal parity only complements
the parity inherited by its children. -/
def AuxTree.evalInorder (rev : ℕ → Bool) : AuxTree → Bool → List ℕ
  | .leaf, _ => []
  | .node id l r, false =>
      evalInorder rev l (rev id) ++ [id] ++ evalInorder rev r (rev id)
  | .node id l r, true =>
      evalInorder rev r (!(rev id)) ++ [id] ++ evalInorder rev l (!(rev id))

theorem AuxTree.evalInorder_true (rev : ℕ → Bool) (t : AuxTree) :
    t.evalInorder rev true = (t.evalInorder rev false).reverse := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
      cases h : rev id <;>
        simp [evalInorder, h, ihl, ihr, List.reverse_append, List.append_assoc]

theorem AuxTree.evalInorder_perm (rev : ℕ → Bool) (t : AuxTree) (b : Bool) :
    (t.evalInorder rev b).Perm t.toList := by
  induction t generalizing b with
  | leaf => simp [evalInorder, toList]
  | node id l r ihl ihr =>
      cases b
      · simp only [evalInorder, toList]
        exact ((ihl (rev id)).append_right [id]).append (ihr (rev id))
      · simp only [evalInorder, toList]
        have hstep1 : ((r.evalInorder rev (!(rev id)) ++ [id]) ++ l.evalInorder rev (!(rev id))).Perm
            (l.evalInorder rev (!(rev id)) ++ (r.evalInorder rev (!(rev id)) ++ [id])) :=
          List.perm_append_comm
        have hstep2 : (l.evalInorder rev (!(rev id)) ++ (r.evalInorder rev (!(rev id)) ++ [id])).Perm
            (l.evalInorder rev (!(rev id)) ++ [id] ++ r.evalInorder rev (!(rev id))) := by
          rw [List.append_assoc]
          exact List.Perm.append_left _ List.perm_append_comm
        exact (hstep1.trans hstep2).trans (((ihl (!(rev id))).append_right [id]).append (ihr (!(rev id))))

/-- The in-order evaluation of a tree has one entry per node. -/
theorem AuxTree.length_evalInorder (rev : ℕ → Bool) (t : AuxTree) (b : Bool) :
    (t.evalInorder rev b).length = t.countNodes := by
  induction t generalizing b with
  | leaf => rfl
  | node id l r ihl ihr =>
      cases b <;> simp [evalInorder, countNodes, ihl, ihr] <;> omega

/-- Aggregate storing whether any finite key exists, the minimum finite value, and
the earliest/latest node IDs attaining that minimum in logical order. -/
structure MinAgg where
  hasMin : Bool
  minVal : ℕ
  minFirst : ℕ
  minLast : ℕ
deriving DecidableEq

/-- Empty-subtree aggregate (`+∞`). -/
def leafMinAgg : MinAgg :=
  ⟨false, 0, 0, 0⟩

/-- Single-node aggregate from an optional key. -/
def singleMinAgg (id : ℕ) : Option ℕ → MinAgg
  | none => leafMinAgg
  | some k => ⟨true, k, id, id⟩

/-- Reverse earliest and latest ties when a segment is reversed. -/
def flipMinAgg (m : MinAgg) : MinAgg :=
  ⟨m.hasMin, m.minVal, m.minLast, m.minFirst⟩

/-- Associative merge of left and right `MinAgg` segments. -/
def combineMinAgg (a b : MinAgg) : MinAgg :=
  if !a.hasMin then b
  else if !b.hasMin then a
  else if a.minVal < b.minVal then a
  else if b.minVal < a.minVal then b
  else ⟨true, a.minVal, a.minFirst, b.minLast⟩

def MinAgg.Canonical (m : MinAgg) : Prop :=
  m.hasMin = false → m = leafMinAgg

theorem leafMinAgg_canonical : leafMinAgg.Canonical := fun _ => rfl

theorem singleMinAgg_canonical (id : ℕ) (ok : Option ℕ) : (singleMinAgg id ok).Canonical := by
  cases ok <;> simp [singleMinAgg, MinAgg.Canonical, leafMinAgg]

theorem flipMinAgg_canonical {m : MinAgg} (hm : m.Canonical) : (flipMinAgg m).Canonical := by
  intro h
  rcases m with ⟨hb, v, f, l⟩
  cases hb
  · have heq := hm rfl; cases heq; rfl
  · simp [flipMinAgg] at h

theorem combineMinAgg_canonical {a b : MinAgg} (ha : a.Canonical) (hb : b.Canonical) :
    (combineMinAgg a b).Canonical := by
  rcases a with ⟨ha0, va, fa, la⟩
  rcases b with ⟨hb0, vb, fb, lb⟩
  cases ha0
  · intro h; simp [combineMinAgg] at *; exact hb h
  · cases hb0
    · intro h; simp [combineMinAgg] at h
    · simp [combineMinAgg]; split_ifs <;> simp [MinAgg.Canonical]

theorem combineMinAgg_leaf_left (b : MinAgg) : combineMinAgg leafMinAgg b = b := by
  simp [combineMinAgg, leafMinAgg]

theorem combineMinAgg_leaf_right {a : MinAgg} (ha : a.Canonical) :
    combineMinAgg a leafMinAgg = a := by
  rcases a with ⟨h, v, f, l⟩
  cases h
  · have := ha rfl; rw [this]; rfl
  · rfl

private theorem combineMinAgg_true {va fa la vb fb lb : ℕ} :
    combineMinAgg ⟨true, va, fa, la⟩ ⟨true, vb, fb, lb⟩ =
      ⟨true, min va vb, if va ≤ vb then fa else fb, if vb ≤ va then lb else la⟩ := by
  simp only [combineMinAgg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rcases lt_trichotomy va vb with hlt | heq | hgt
  · have h2 : va ≤ vb := by omega
    have h3 : ¬ vb ≤ va := by omega
    have hmin : min va vb = va := Nat.min_eq_left h2
    simp [hlt, h2, h3, hmin]
  · subst heq
    simp
  · have h1 : ¬ va < vb := by omega
    have h2 : ¬ va ≤ vb := by omega
    have h3 : vb ≤ va := by omega
    have hmin : min va vb = vb := Nat.min_eq_right h3
    simp [h1, hgt, h2, h3, hmin]

theorem combineMinAgg_assoc (a b c : MinAgg) :
    combineMinAgg (combineMinAgg a b) c = combineMinAgg a (combineMinAgg b c) := by
  rcases a with ⟨ha, va, fa, la⟩
  rcases b with ⟨hb, vb, fb, lb⟩
  rcases c with ⟨hc, vc, fc, lc⟩
  cases ha
  · simp [combineMinAgg]
  cases hb
  · simp [combineMinAgg]
  cases hc
  · have h2 : combineMinAgg ⟨true, vb, fb, lb⟩ ⟨false, vc, fc, lc⟩ = ⟨true, vb, fb, lb⟩ := by
      simp [combineMinAgg]
    have h1 : combineMinAgg (combineMinAgg ⟨true, va, fa, la⟩ ⟨true, vb, fb, lb⟩)
        ⟨false, vc, fc, lc⟩ = combineMinAgg ⟨true, va, fa, la⟩ ⟨true, vb, fb, lb⟩ := by
      rw [combineMinAgg_true]; simp [combineMinAgg]
    rw [h1, h2]
  simp only [combineMinAgg_true, Nat.min_assoc]
  have hf : (if min va vb ≤ vc then if va ≤ vb then fa else fb else fc) =
      (if va ≤ min vb vc then fa else if vb ≤ vc then fb else fc) := by
    simp only [Nat.min_def]; split_ifs <;> first | rfl | omega
  have hl : (if vc ≤ min va vb then lc else if vb ≤ va then lb else la) =
      (if min vb vc ≤ va then if vc ≤ vb then lc else lb else la) := by
    simp only [Nat.min_def]; split_ifs <;> first | rfl | omega
  rw [hf, hl]

theorem flipMinAgg_combine {a b : MinAgg} (ha : a.Canonical) (hb : b.Canonical) :
    flipMinAgg (combineMinAgg a b) = combineMinAgg (flipMinAgg b) (flipMinAgg a) := by
  rcases a with ⟨ha0, va, fa, la⟩
  rcases b with ⟨hb0, vb, fb, lb⟩
  cases ha0
  · cases hb0
    · have ha' := ha rfl; have hb' := hb rfl
      rw [ha', hb']; rfl
    · rfl
  cases hb0
  · rfl
  simp only [flipMinAgg, combineMinAgg_true, Nat.min_comm]

/-- Aggregate over a node list with respect to key map `kOf`. -/
def listMinAgg (kOf : ℕ → Option ℕ) : List ℕ → MinAgg
  | [] => leafMinAgg
  | id :: ids => combineMinAgg (singleMinAgg id (kOf id)) (listMinAgg kOf ids)

theorem listMinAgg_canonical (kOf : ℕ → Option ℕ) (L : List ℕ) :
    (listMinAgg kOf L).Canonical := by
  induction L with
  | nil => exact leafMinAgg_canonical
  | cons x xs ih => exact combineMinAgg_canonical (singleMinAgg_canonical x (kOf x)) ih

theorem listMinAgg_append (kOf : ℕ → Option ℕ) (L₁ L₂ : List ℕ) :
    listMinAgg kOf (L₁ ++ L₂) = combineMinAgg (listMinAgg kOf L₁) (listMinAgg kOf L₂) := by
  induction L₁ with
  | nil => simp [listMinAgg, combineMinAgg_leaf_left]
  | cons x xs ih => simp [listMinAgg, ih, combineMinAgg_assoc]

theorem listMinAgg_reverse (kOf : ℕ → Option ℕ) (L : List ℕ) :
    listMinAgg kOf L.reverse = flipMinAgg (listMinAgg kOf L) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.reverse_cons, listMinAgg_append, ih, listMinAgg,
        combineMinAgg_leaf_right (singleMinAgg_canonical _ _),
        flipMinAgg_combine (singleMinAgg_canonical _ _) (listMinAgg_canonical _ _)]
      cases kOf x <;> rfl

/-- Total tree weight `s(t)` including external virtual weights `vSize : ℕ → ℕ`. -/
def AuxTree.treeSize (vSize : ℕ → ℕ) : AuxTree → ℕ
  | .leaf => 0
  | .node id l r => 1 + l.treeSize vSize + r.treeSize vSize + vSize id

theorem AuxTree.countNodes_le_treeSize (vSize : ℕ → ℕ) (t : AuxTree) :
    t.countNodes ≤ t.treeSize vSize := by
  induction t with
  | leaf => exact Nat.le_refl 0
  | node id l r ihl ihr => simp [countNodes, treeSize]; omega

theorem AuxTree.one_le_treeSize (vSize : ℕ → ℕ) {id : ℕ} {l r : AuxTree} :
    1 ≤ (AuxTree.node id l r).treeSize vSize := by
  simp [treeSize]; omega

/-- Rank `⌊log₂ s(t)⌋` (or `0` for `leaf`). -/
def AuxTree.rank (vSize : ℕ → ℕ) (t : AuxTree) : ℕ :=
  Nat.log 2 (t.treeSize vSize)

/-- Splay potential `Φ(t) = ∑_{u ∈ t} rank(u)` (unscaled by word-step constant). -/
def AuxTree.treePhi (vSize : ℕ → ℕ) : AuxTree → ℕ
  | .leaf => 0
  | .node id l r => (AuxTree.node id l r).rank vSize + l.treePhi vSize + r.treePhi vSize

theorem AuxTree.rank_mono_sub {a b : ℕ} (hle : a ≤ b) :
    Nat.log 2 a ≤ Nat.log 2 b :=
  Nat.log_mono_right hle

/-- Core integer logarithm inequality used in zig-zig and zig-zag steps:
if `1 ≤ a`, `1 ≤ b`, and `a + b ≤ c`, then `Nat.log 2 a + Nat.log 2 b + 1 ≤ 2 * Nat.log 2 c`. -/
theorem nat_log_add_le_of_add_le {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hsum : a + b ≤ c) :
    Nat.log 2 a + Nat.log 2 b + 1 ≤ 2 * Nat.log 2 c := by
  have hac : Nat.log 2 a ≤ Nat.log 2 c := Nat.log_mono_right (by omega)
  have hbc : Nat.log 2 b ≤ Nat.log 2 c := Nat.log_mono_right (by omega)
  by_cases h1 : Nat.log 2 a = Nat.log 2 c
  · by_cases h2 : Nat.log 2 b = Nat.log 2 c
    · have ha_pow : 2 ^ Nat.log 2 c ≤ a := by
        simpa [h1] using Nat.pow_log_le_self 2 (by omega : a ≠ 0)
      have hb_pow : 2 ^ Nat.log 2 c ≤ b := by
        simpa [h2] using Nat.pow_log_le_self 2 (by omega : b ≠ 0)
      have hc_lt : c < 2 ^ (Nat.log 2 c + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) c
      rw [Nat.pow_succ, Nat.mul_two] at hc_lt
      omega
    · omega
  · omega

/-- Upper bound `treePhi vSize t ≤ t.countNodes * Nat.log 2 (t.treeSize vSize + 2)`. -/
theorem AuxTree.treePhi_le (vSize : ℕ → ℕ) (t : AuxTree) :
    t.treePhi vSize ≤ t.countNodes * Nat.log 2 (t.treeSize vSize + 2) := by
  induction t with
  | leaf => simp [treePhi, countNodes]
  | node id l r ihl ihr =>
      have hl_le : l.treeSize vSize + 2 ≤ (AuxTree.node id l r).treeSize vSize + 2 := by
        simp [treeSize]; omega
      have hr_le : r.treeSize vSize + 2 ≤ (AuxTree.node id l r).treeSize vSize + 2 := by
        simp [treeSize]; omega
      have hrk : (AuxTree.node id l r).rank vSize ≤
          Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) :=
        Nat.log_mono_right (by omega)
      have hrl : Nat.log 2 (l.treeSize vSize + 2) ≤
          Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) := Nat.log_mono_right hl_le
      have hrr : Nat.log 2 (r.treeSize vSize + 2) ≤
          Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) := Nat.log_mono_right hr_le
      have h1 : l.treePhi vSize ≤ l.countNodes * Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) :=
        Nat.le_trans ihl (Nat.mul_le_mul_left _ hrl)
      have h2 : r.treePhi vSize ≤ r.countNodes * Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) :=
        Nat.le_trans ihr (Nat.mul_le_mul_left _ hrr)
      simp only [treePhi, countNodes]
      have hmul : (1 + l.countNodes + r.countNodes) *
          Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) =
          Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) +
          l.countNodes * Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) +
          r.countNodes * Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) := by
        simp only [Nat.add_mul, Nat.one_mul]
      omega

/-- Zig step (single right rotation at root `p` bringing left child `x` to root).
Left rotation is symmetric; proved in one shared theorem using tree children! -/
theorem zig_right_phi_le (vSize : ℕ → ℕ) (x p : ℕ) (A B C : AuxTree) :
    let t := AuxTree.node p (AuxTree.node x A B) C
    let t' := AuxTree.node x A (AuxTree.node p B C)
    t'.treePhi vSize + 3 * (AuxTree.node x A B).rank vSize ≤
      t.treePhi vSize + 3 * t'.rank vSize := by
  intro t t'
  have hs_eq : t'.treeSize vSize = t.treeSize vSize := by
    simp [t, t', AuxTree.treeSize]; omega
  have hr_eq : t'.rank vSize = t.rank vSize := by simp [AuxTree.rank, hs_eq]
  have hp'_le : (AuxTree.node p B C).treeSize vSize ≤ t'.treeSize vSize := by
    simp [t', AuxTree.treeSize]; omega
  have hrx_le : (AuxTree.node x A B).rank vSize ≤ t.rank vSize :=
    Nat.log_mono_right (by simp [t, AuxTree.treeSize]; omega)
  have hrp'_le : (AuxTree.node p B C).rank vSize ≤ t'.rank vSize :=
    Nat.log_mono_right hp'_le
  dsimp only [t, t', AuxTree.treePhi]
  rw [show (AuxTree.node x A (AuxTree.node p B C)).rank vSize = t'.rank vSize from rfl,
      show (AuxTree.node p (AuxTree.node x A B) C).rank vSize = t.rank vSize from rfl,
      hr_eq]
  omega

/-- Symmetric single left rotation (right child `x` rotated above `p`). -/
theorem zig_left_phi_le (vSize : ℕ → ℕ) (p x : ℕ) (A B C : AuxTree) :
    let t := AuxTree.node p A (AuxTree.node x B C)
    let t' := AuxTree.node x (AuxTree.node p A B) C
    t'.treePhi vSize + 3 * (AuxTree.node x B C).rank vSize ≤
      t.treePhi vSize + 3 * t'.rank vSize := by
  intro t t'
  have hs_eq : t'.treeSize vSize = t.treeSize vSize := by
    simp [t, t', AuxTree.treeSize]; omega
  have hr_eq : t'.rank vSize = t.rank vSize := by simp [AuxTree.rank, hs_eq]
  have hrp'_le : (AuxTree.node p A B).rank vSize ≤ t'.rank vSize :=
    Nat.log_mono_right (by simp [t', AuxTree.treeSize]; omega)
  have hrx_le : (AuxTree.node x B C).rank vSize ≤ t.rank vSize :=
    Nat.log_mono_right (by simp [t, AuxTree.treeSize]; omega)
  dsimp only [t, t', AuxTree.treePhi]
  rw [show (AuxTree.node x (AuxTree.node p A B) C).rank vSize = t'.rank vSize from rfl,
      show (AuxTree.node p A (AuxTree.node x B C)).rank vSize = t.rank vSize from rfl,
      hr_eq]
  omega

/-- Helper encapsulating the algebraic core of all zig-zig cases (`a = s(x)`, `b = s'(g)`,
`c = s'(x) = s(g)` with `a + b ≤ c`). -/
private theorem zigZig_arith {rx rp rg rx' rp' rg' : ℕ}
    (hrg : rg = rx') (hrx_rp : rx ≤ rp) (hrx_rx' : rx ≤ rx')
    (hrp'_rx' : rp' ≤ rx') (hrg'_rx' : rg' ≤ rx') (hlog : rx + rg' + 1 ≤ 2 * rx') :
    rx' + rp' + rg' + 3 * rx + 1 ≤ rx + rp + rg + 3 * rx' := by
  by_cases hrx : rx = rx'
  · omega
  · have hrx_lt : rx + 1 ≤ rx' := by omega
    have hrg'_le : rg' ≤ rx' := hrg'_rx'
    omega

/-- Zig-zig right (left-left): `g -> left p -> left x` becomes `x -> right p -> right g`.
Saves at least `1` unit of unscaled potential relative to `3 * (r'(x) - r(x))`. -/
theorem zigZig_right_phi_le (vSize : ℕ → ℕ) (x p g : ℕ) (A B C D : AuxTree) :
    let t := AuxTree.node g (AuxTree.node p (AuxTree.node x A B) C) D
    let t' := AuxTree.node x A (AuxTree.node p B (AuxTree.node g C D))
    t'.treePhi vSize + 3 * (AuxTree.node x A B).rank vSize + 1 ≤
      t.treePhi vSize + 3 * t'.rank vSize := by
  intro t t'
  have hs_eq : t'.treeSize vSize = t.treeSize vSize := by
    simp [t, t', AuxTree.treeSize]; omega
  have hsum : (AuxTree.node x A B).treeSize vSize + (AuxTree.node g C D).treeSize vSize ≤
      t'.treeSize vSize := by
    simp [t', AuxTree.treeSize]; omega
  have hlog := nat_log_add_le_of_add_le
    (AuxTree.one_le_treeSize vSize) (AuxTree.one_le_treeSize vSize) hsum
  have har := zigZig_arith
    (rg := t.rank vSize) (rx' := t'.rank vSize)
    (rp := (AuxTree.node p (AuxTree.node x A B) C).rank vSize)
    (rx := (AuxTree.node x A B).rank vSize)
    (rp' := (AuxTree.node p B (AuxTree.node g C D)).rank vSize)
    (rg' := (AuxTree.node g C D).rank vSize)
    (by simp [AuxTree.rank, hs_eq])
    (Nat.log_mono_right (by simp [AuxTree.treeSize]; omega))
    (Nat.log_mono_right (by dsimp only [t']; simp [AuxTree.treeSize]; omega))
    (Nat.log_mono_right (by dsimp only [t']; simp [AuxTree.treeSize]; omega))
    (Nat.log_mono_right (by dsimp only [t']; simp [AuxTree.treeSize]; omega))
    hlog
  dsimp only [t, t', AuxTree.treePhi]
  rw [show (AuxTree.node g (AuxTree.node p (AuxTree.node x A B) C) D).rank vSize =
        t.rank vSize from rfl,
      show (AuxTree.node x A (AuxTree.node p B (AuxTree.node g C D))).rank vSize =
        t'.rank vSize from rfl]
  omega

/-- Zig-zig left (right-right): `g -> right p -> right x` becomes `x -> left p -> left g`. -/
theorem zigZig_left_phi_le (vSize : ℕ → ℕ) (g p x : ℕ) (A B C D : AuxTree) :
    let t := AuxTree.node g A (AuxTree.node p B (AuxTree.node x C D))
    let t' := AuxTree.node x (AuxTree.node p (AuxTree.node g A B) C) D
    t'.treePhi vSize + 3 * (AuxTree.node x C D).rank vSize + 1 ≤
      t.treePhi vSize + 3 * t'.rank vSize := by
  intro t t'
  have hs_eq : t'.treeSize vSize = t.treeSize vSize := by
    simp [t, t', AuxTree.treeSize]; omega
  have hsum : (AuxTree.node x C D).treeSize vSize + (AuxTree.node g A B).treeSize vSize ≤
      t'.treeSize vSize := by
    simp [t', AuxTree.treeSize]; omega
  have hlog := nat_log_add_le_of_add_le
    (AuxTree.one_le_treeSize vSize) (AuxTree.one_le_treeSize vSize) hsum
  have har := zigZig_arith
    (rg := t.rank vSize) (rx' := t'.rank vSize)
    (rp := (AuxTree.node p B (AuxTree.node x C D)).rank vSize)
    (rx := (AuxTree.node x C D).rank vSize)
    (rp' := (AuxTree.node p (AuxTree.node g A B) C).rank vSize)
    (rg' := (AuxTree.node g A B).rank vSize)
    (by simp [AuxTree.rank, hs_eq])
    (Nat.log_mono_right (by simp [AuxTree.treeSize]; omega))
    (Nat.log_mono_right (by dsimp only [t']; simp [AuxTree.treeSize]; omega))
    (Nat.log_mono_right (by dsimp only [t']; simp [AuxTree.treeSize]; omega))
    (Nat.log_mono_right (by dsimp only [t']; simp [AuxTree.treeSize]; omega))
    hlog
  dsimp only [t, t', AuxTree.treePhi]
  rw [show (AuxTree.node g A (AuxTree.node p B (AuxTree.node x C D))).rank vSize =
        t.rank vSize from rfl,
      show (AuxTree.node x (AuxTree.node p (AuxTree.node g A B) C) D).rank vSize =
        t'.rank vSize from rfl]
  omega

/-- Helper encapsulating the algebraic core of both zig-zag cases
(`rp' + rg' + 1 ≤ 2 * rx'`). -/
private theorem zigZag_arith {rx rp rg rx' rp' rg' : ℕ}
    (hrg : rg = rx') (hrx_rp : rx ≤ rp) (hrx_rx' : rx ≤ rx') (hlog : rp' + rg' + 1 ≤ 2 * rx') :
    rx' + rp' + rg' + 3 * rx + 1 ≤ rx + rp + rg + 3 * rx' := by
  omega

/-- Zig-zag left-right: `g -> left p -> right x` becomes `x (left p, right g)`. -/
theorem zigZag_lr_phi_le (vSize : ℕ → ℕ) (p x g : ℕ) (A B C D : AuxTree) :
    let t := AuxTree.node g (AuxTree.node p A (AuxTree.node x B C)) D
    let t' := AuxTree.node x (AuxTree.node p A B) (AuxTree.node g C D)
    t'.treePhi vSize + 3 * (AuxTree.node x B C).rank vSize + 1 ≤
      t.treePhi vSize + 3 * t'.rank vSize := by
  intro t t'
  have hs_eq : t'.treeSize vSize = t.treeSize vSize := by
    simp [t, t', AuxTree.treeSize]; omega
  have hsum : (AuxTree.node p A B).treeSize vSize + (AuxTree.node g C D).treeSize vSize ≤
      t'.treeSize vSize := by
    simp [t', AuxTree.treeSize]; omega
  have hlog := nat_log_add_le_of_add_le
    (AuxTree.one_le_treeSize vSize) (AuxTree.one_le_treeSize vSize) hsum
  have har := zigZag_arith
    (rg := t.rank vSize) (rx' := t'.rank vSize)
    (rp := (AuxTree.node p A (AuxTree.node x B C)).rank vSize)
    (rx := (AuxTree.node x B C).rank vSize)
    (rp' := (AuxTree.node p A B).rank vSize)
    (rg' := (AuxTree.node g C D).rank vSize)
    (by simp [AuxTree.rank, hs_eq])
    (Nat.log_mono_right (by simp [AuxTree.treeSize]; omega))
    (Nat.log_mono_right (by dsimp only [t']; simp [AuxTree.treeSize]; omega))
    hlog
  dsimp only [t, t', AuxTree.treePhi]
  rw [show (AuxTree.node g (AuxTree.node p A (AuxTree.node x B C)) D).rank vSize =
        t.rank vSize from rfl,
      show (AuxTree.node x (AuxTree.node p A B) (AuxTree.node g C D)).rank vSize =
        t'.rank vSize from rfl]
  omega

/-- Zig-zag right-left: `g -> right p -> left x` becomes `x (left g, right p)`. -/
theorem zigZag_rl_phi_le (vSize : ℕ → ℕ) (g x p : ℕ) (A B C D : AuxTree) :
    let t := AuxTree.node g A (AuxTree.node p (AuxTree.node x B C) D)
    let t' := AuxTree.node x (AuxTree.node g A B) (AuxTree.node p C D)
    t'.treePhi vSize + 3 * (AuxTree.node x B C).rank vSize + 1 ≤
      t.treePhi vSize + 3 * t'.rank vSize := by
  intro t t'
  have hs_eq : t'.treeSize vSize = t.treeSize vSize := by
    simp [t, t', AuxTree.treeSize]; omega
  have hsum : (AuxTree.node g A B).treeSize vSize + (AuxTree.node p C D).treeSize vSize ≤
      t'.treeSize vSize := by
    simp [t', AuxTree.treeSize]; omega
  have hlog := nat_log_add_le_of_add_le
    (AuxTree.one_le_treeSize vSize) (AuxTree.one_le_treeSize vSize) hsum
  have har := zigZag_arith
    (rg := t.rank vSize) (rx' := t'.rank vSize)
    (rp := (AuxTree.node p (AuxTree.node x B C) D).rank vSize)
    (rx := (AuxTree.node x B C).rank vSize)
    (rp' := (AuxTree.node g A B).rank vSize)
    (rg' := (AuxTree.node p C D).rank vSize)
    (by simp [AuxTree.rank, hs_eq])
    (Nat.log_mono_right (by simp [AuxTree.treeSize]; omega))
    (Nat.log_mono_right (by dsimp only [t']; simp [AuxTree.treeSize]; omega))
    hlog
  dsimp only [t, t', AuxTree.treePhi]
  rw [show (AuxTree.node g A (AuxTree.node p (AuxTree.node x B C) D)).rank vSize =
        t.rank vSize from rfl,
      show (AuxTree.node x (AuxTree.node g A B) (AuxTree.node p C D)).rank vSize =
        t'.rank vSize from rfl]
  omega

end

end MinCostFlow.LinkCut.Prog
