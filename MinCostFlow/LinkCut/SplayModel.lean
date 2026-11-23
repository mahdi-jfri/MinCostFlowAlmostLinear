module

public import MinCostFlow.LinkCut.Payload
public import MinCostFlow.LinkCut.SplayTree
import Mathlib.Tactic

/-!
# Generic stateful splay trees with directional payloads

This file implements a stateful array-like model (`SplayState α σ τ`) over 1-based node IDs
for an arbitrary directional payload `P : LctPayload α σ τ`, together with invariants
(`TreeInv P st t`) linking `st` to an algebraic skeleton `t : AuxTree`.

Operations implemented and proved here:
- `revNode`, `applyTagNode`, `pull`, `pushDown`, `pushPath`
- `rotate`, `splayStep`, `splayLoop`, `splay`
- `leftmostWalk`, `findLeftmost`

All correctness and Sleator–Tarjan amortized potential bounds are proved generically for any
`P` satisfying `P.Laws` and any virtual weight function `vSize : ℕ → ℕ`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

/-- State of one splay-tree node (node ID `0` is the null sentinel). -/
structure SplayNode (α σ τ : Type*) where
  left : ℕ
  right : ℕ
  par : ℕ
  ppar : ℕ
  sz : ℕ
  val : α
  sum : σ
  tag : τ
  rev : Bool

theorem SplayNode.ext_fields {α σ τ : Type*} {a b : SplayNode α σ τ}
    (h1 : a.val = b.val) (h2 : a.rev = b.rev) (h3 : a.tag = b.tag)
    (h4 : a.par = b.par) (h5 : a.ppar = b.ppar) (h6 : a.sz = b.sz)
    (h7 : a.sum = b.sum) (h8 : a.left = b.left) (h9 : a.right = b.right) : a = b := by
  cases a; cases b; cases h1; cases h2; cases h3; cases h4; cases h5
  cases h6; cases h7; cases h8; cases h9; rfl

/-- Total map from 1-based node IDs to `SplayNode` records. -/
structure SplayState (α σ τ : Type*) where
  nodes : ℕ → SplayNode α σ τ

namespace SplayState

variable {α σ τ : Type*}

/-- Update node `x` using `f`, leaving all other IDs unchanged. -/
def updateNode (st : SplayState α σ τ) (x : ℕ) (f : SplayNode α σ τ → SplayNode α σ τ) :
    SplayState α σ τ where
  nodes i := if i = x then f (st.nodes x) else st.nodes i

@[simp]
theorem nodes_updateNode_self (st : SplayState α σ τ) (x : ℕ)
    (f : SplayNode α σ τ → SplayNode α σ τ) :
    (st.updateNode x f).nodes x = f (st.nodes x) := by
  simp [updateNode]

@[simp]
theorem nodes_updateNode_ne (st : SplayState α σ τ) {x i : ℕ} (hne : i ≠ x)
    (f : SplayNode α σ τ → SplayNode α σ τ) :
    (st.updateNode x f).nodes i = st.nodes i := by
  simp [updateNode, hne]

theorem nodes_updateNode (st : SplayState α σ τ) (x i : ℕ)
    (f : SplayNode α σ τ → SplayNode α σ τ) :
    (st.updateNode x f).nodes i = if i = x then f (st.nodes x) else st.nodes i := rfl

/-- Overwrite node `x` cleanly (`setNode`). -/
def setNode (st : SplayState α σ τ) (x : ℕ) (nd : SplayNode α σ τ) : SplayState α σ τ :=
  st.updateNode x fun _ => nd

def setLeft (st : SplayState α σ τ) (x l : ℕ) : SplayState α σ τ :=
  st.updateNode x fun nd => { nd with left := l }

def setRight (st : SplayState α σ τ) (x r : ℕ) : SplayState α σ τ :=
  st.updateNode x fun nd => { nd with right := r }

def setPar (st : SplayState α σ τ) (x p : ℕ) : SplayState α σ τ :=
  st.updateNode x fun nd => { nd with par := p }

def setPpar (st : SplayState α σ τ) (x pp : ℕ) : SplayState α σ τ :=
  st.updateNode x fun nd => { nd with ppar := pp }

/-! ### Logical `(nodeId, val)` sequence `evalPairs` -/

/-- Logical in-order sequence of `(nodeId, α)` pairs represented by subtree `t` in `st`, under
accumulated parent reversal parity `flip` and accumulated ancestor tag `acc` (already in the
post-`flip` orientation). -/
def evalPairs (P : LctPayload α σ τ) (st : SplayState α σ τ) :
    AuxTree → Bool → τ → List (ℕ × α)
  | .leaf, _, _ => []
  | .node id l r, flip, acc =>
      let nd := st.nodes id
      let v₀ := if flip then P.revVal nd.val else nd.val
      let v := P.actVal acc v₀
      let flip' := flip ^^ nd.rev
      let tLocal := if flip then P.revTag nd.tag else nd.tag
      let acc' := P.compTag acc tLocal
      if flip then
        evalPairs P st r flip' acc' ++ [(id, v)] ++ evalPairs P st l flip' acc'
      else
        evalPairs P st l flip' acc' ++ [(id, v)] ++ evalPairs P st r flip' acc'

theorem evalPairs_length (P : LctPayload α σ τ) (st : SplayState α σ τ)
    (t : AuxTree) (flip : Bool) (acc : τ) :
    (evalPairs P st t flip acc).length = t.countNodes := by
  induction t generalizing flip acc with
  | leaf => rfl
  | node id l r ihl ihr =>
      cases flip <;> simp [evalPairs, AuxTree.countNodes, ihl, ihr] <;> omega

theorem evalPairs_map_fst (P : LctPayload α σ τ) (st : SplayState α σ τ)
    (t : AuxTree) (flip : Bool) (acc : τ) :
    (evalPairs P st t flip acc).map Prod.fst =
      t.evalInorder (fun id => (st.nodes id).rev) flip := by
  induction t generalizing flip acc with
  | leaf => rfl
  | node id l r ihl ihr =>
      cases flip <;> simp [evalPairs, AuxTree.evalInorder, ihl, ihr]

theorem evalPairs_agree (P : LctPayload α σ τ) {st₁ st₂ : SplayState α σ τ}
    {t : AuxTree} (h : ∀ u ∈ t.toList, st₁.nodes u = st₂.nodes u)
    (flip : Bool) (acc : τ) :
    evalPairs P st₁ t flip acc = evalPairs P st₂ t flip acc := by
  induction t generalizing flip acc with
  | leaf => rfl
  | node id l r ihl ihr =>
      have hid := h id (by simp [AuxTree.toList])
      have hl : ∀ u ∈ l.toList, st₁.nodes u = st₂.nodes u :=
        fun u hu => h u (by simp [AuxTree.toList, hu])
      have hr : ∀ u ∈ r.toList, st₁.nodes u = st₂.nodes u :=
        fun u hu => h u (by simp [AuxTree.toList, hu])
      cases flip <;> simp only [evalPairs, hid, ihl hl, ihr hr]

theorem evalPairs_compTag {P : LctPayload α σ τ} (hL : P.Laws)
    (st : SplayState α σ τ) (t : AuxTree) (flip : Bool) (t₁ t₂ : τ) :
    evalPairs P st t flip (P.compTag t₁ t₂) =
      (evalPairs P st t flip t₂).map (fun p => (p.1, P.actVal t₁ p.2)) := by
  induction t generalizing flip t₁ t₂ with
  | leaf => rfl
  | node id l r ihl ihr =>
      cases flip
      · simp only [evalPairs, Bool.false_eq_true, ↓reduceIte,
          List.map_append, List.map_cons, List.map_nil, hL.actVal_comp, hL.compTag_assoc, ihl, ihr]
      · simp only [evalPairs, ↓reduceIte,
          List.map_append, List.map_cons, List.map_nil, hL.actVal_comp, hL.compTag_assoc, ihl, ihr]

theorem evalPairs_flip {P : LctPayload α σ τ} (hL : P.Laws)
    (st : SplayState α σ τ) (t : AuxTree) (flip : Bool) (acc : τ) :
    evalPairs P st t (!flip) (P.revTag acc) =
      (evalPairs P st t flip acc).reverse.map (fun p => (p.1, P.revVal p.2)) := by
  induction t generalizing flip acc with
  | leaf => rfl
  | node id l r ihl ihr =>
      cases flip
      · simp only [evalPairs, Bool.not_false, Bool.true_xor, Bool.false_xor, Bool.false_eq_true,
          ↓reduceIte, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.map_append, List.map_cons, List.map_nil, List.append_assoc,
          ← hL.revTag_comp, ← hL.revVal_actVal, ihl, ihr]
      · simp only [evalPairs, Bool.not_true, Bool.false_xor, Bool.true_xor, Bool.false_eq_true,
          ↓reduceIte, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.map_append, List.map_cons, List.map_nil, List.append_assoc]
        have hl := ihl (!(st.nodes id).rev) (P.compTag acc (P.revTag (st.nodes id).tag))
        have hr := ihr (!(st.nodes id).rev) (P.compTag acc (P.revTag (st.nodes id).tag))
        simp only [Bool.not_not, hL.revTag_comp, hL.revTag_revTag] at hl hr
        rw [hl, hr, hL.revVal_actVal, hL.revVal_revVal]

theorem evalPairs_true_idTag {P : LctPayload α σ τ} (hL : P.Laws)
    (st : SplayState α σ τ) (t : AuxTree) :
    evalPairs P st t true P.idTag =
      (evalPairs P st t false P.idTag).reverse.map (fun p => (p.1, P.revVal p.2)) := by
  simpa [hL.revTag_id] using evalPairs_flip hL st t false P.idTag

/-! ### Lazy operations: `revNode`, `applyTagNode`, `pull`, `pushDown`, `pushPath` -/

/-- Pre-reverse node `x` (swapping its physical children, toggling `rev`, and transforming
`val`, `sum`, `tag`). Does nothing if `x = 0`. -/
def revNode (P : LctPayload α σ τ) (st : SplayState α σ τ) (x : ℕ) : SplayState α σ τ :=
  if x = 0 then st
  else
    st.updateNode x fun nd =>
      { nd with
        left := nd.right
        right := nd.left
        rev := !nd.rev
        val := P.revVal nd.val
        sum := P.revSum nd.sum
        tag := P.revTag nd.tag }

/-- Apply lazy tag `t` to node `x` (pre-applying `t` to `x.val` and `x.sum`, and composing into
`x.tag` for `x`'s children). Does nothing if `x = 0`. -/
def applyTagNode (P : LctPayload α σ τ) (st : SplayState α σ τ) (x : ℕ) (t : τ) :
    SplayState α σ τ :=
  if x = 0 then st
  else
    st.updateNode x fun nd =>
      { nd with
        val := P.actVal t nd.val
        sum := P.actSum t nd.sum
        tag := P.compTag t nd.tag }

/-- Recompute `sz` and `sum` of node `x` from its children's summaries and `x.val`.
Assumes `x` already has `rev = false` and `tag = P.idTag`. -/
def pull (P : LctPayload α σ τ) (st : SplayState α σ τ) (x : ℕ) : SplayState α σ τ :=
  if x = 0 then st
  else
    let nd := st.nodes x
    let szL := if nd.left = 0 then 0 else (st.nodes nd.left).sz
    let szR := if nd.right = 0 then 0 else (st.nodes nd.right).sz
    let sumL := if nd.left = 0 then P.empty else (st.nodes nd.left).sum
    let sumR := if nd.right = 0 then P.empty else (st.nodes nd.right).sum
    let sum' := P.combine sumL (P.combine (P.single x nd.val) sumR)
    st.updateNode x fun cur => { cur with sz := 1 + szL + szR, sum := sum' }

/-- Push only lazy `rev` from `x` down to its physical children `left` and `right`. -/
def pushDownRev (P : LctPayload α σ τ) (st : SplayState α σ τ) (x : ℕ) : SplayState α σ τ :=
  if x = 0 then st
  else
    let nd := st.nodes x
    if nd.rev then
      let st₀ := st.updateNode x fun cur => { cur with rev := false }
      let stL := revNode P st₀ nd.left
      revNode P stL nd.right
    else st

/-- Push only lazy `tag` from `x` down to its physical children `left` and `right`. -/
def pushDownTag (P : LctPayload α σ τ) (st : SplayState α σ τ) (x : ℕ) : SplayState α σ τ :=
  if x = 0 then st
  else
    let nd := st.nodes x
    if P.isIdTag nd.tag then st
    else
      let t := nd.tag
      let st₀ := st.updateNode x fun cur => { cur with tag := P.idTag }
      let stL := applyTagNode P st₀ nd.left t
      applyTagNode P stL nd.right t

/-- Push lazy `rev` and `tag` from `x` down to its physical children `left` and `right`. -/
def pushDown (P : LctPayload α σ τ) (st : SplayState α σ τ) (x : ℕ) : SplayState α σ τ :=
  pushDownTag P (pushDownRev P st x) x

/-- Push all lazy flags along the ancestor path from root down to `x`, bounded by `fuel`. -/
def pushPath (P : LctPayload α σ τ) (st : SplayState α σ τ) : ℕ → ℕ → SplayState α σ τ
  | 0, _ => st
  | k + 1, x =>
      if x = 0 then st
      else
        let p := (st.nodes x).par
        let st₁ := if p = 0 then st else pushPath P st k p
        pushDown P st₁ x

/-- Single splay rotation moving `x` one step toward its auxiliary-tree root, assuming `x` and
its parent `p` already have `rev = false` and `tag = P.idTag`. -/
def rotate (P : LctPayload α σ τ) (st : SplayState α σ τ) (x : ℕ) : SplayState α σ τ :=
  if x = 0 then st
  else
    let p := (st.nodes x).par
    if p = 0 then st
    else
      let g := (st.nodes p).par
      let pp := (st.nodes p).ppar
      let isLeft := (x == (st.nodes p).left)
      let b := if isLeft then (st.nodes x).right else (st.nodes x).left
      let st1 := if isLeft then st.setRight x p else st.setLeft x p
      let st2 := if isLeft then st1.setLeft p b else st1.setRight p b
      let st3 := if b = 0 then st2 else st2.setPar b p
      let st4 := st3.setPar p x
      let st5 := st4.setPar x g
      let st6 := st5.setPpar x pp
      let st7 := st6.setPpar p 0
      let st8 :=
        if g = 0 then st7
        else if p == (st7.nodes g).left then st7.setLeft g x
        else st7.setRight g x
      pull P (pull P st8 p) x

/-- One splay step (zig, zig-zig, or zig-zag) moving `x` toward its auxiliary-tree root.
Assumes `pushPath` has already cleared `rev` and `tag` along `x`'s ancestor path. -/
def splayStep (P : LctPayload α σ τ) (st : SplayState α σ τ) (x : ℕ) : SplayState α σ τ :=
  if x = 0 then st
  else
    let p := (st.nodes x).par
    if p = 0 then st
    else
      let g := (st.nodes p).par
      if g = 0 then rotate P st x
      else
        let leftX := (x == (st.nodes p).left)
        let leftP := (p == (st.nodes g).left)
        if leftX == leftP then rotate P (rotate P st p) x
        else rotate P (rotate P st x) x

/-- Repeatedly splay `x` to the root using `splayStep`, bounded by `fuel`. -/
def splayLoop (P : LctPayload α σ τ) (st : SplayState α σ τ) : ℕ → ℕ → SplayState α σ τ
  | 0, _ => st
  | k + 1, x =>
      if x = 0 then st
      else if (st.nodes x).par = 0 then st
      else splayLoop P (splayStep P st x) k x

/-- Full splay of `x`: push lazy flags along the ancestor path to `x`, then splay `x` to the
root of its auxiliary tree. -/
def splay (P : LctPayload α σ τ) (st : SplayState α σ τ) (fuel x : ℕ) : SplayState α σ τ :=
  if x = 0 then st
  else splayLoop P (pushPath P st fuel x) fuel x

/-- Walk down left children while calling `pushDown`, returning `(st', leftmost)`. -/
def leftmostWalk (P : LctPayload α σ τ) (st : SplayState α σ τ) : ℕ → ℕ → SplayState α σ τ × ℕ
  | 0, x => (st, x)
  | k + 1, x =>
      if x = 0 then (st, 0)
      else
        let st1 := pushDown P st x
        let l := (st1.nodes x).left
        if l = 0 then (st1, x)
        else leftmostWalk P st1 k l

/-- Walk down to the leftmost node `r` from `x` and splay `r` to the root. -/
def findLeftmost (P : LctPayload α σ τ) (st : SplayState α σ τ) (fuel x : ℕ) :
    SplayState α σ τ × ℕ :=
  let (st1, r) := leftmostWalk P st fuel x
  (splay P st1 fuel r, r)

/-! ### Tree invariants -/

/-- Structural and payload invariant on a subtree `t`, whose root has expected `par = rootPar`.
Any strict descendant (`rootPar ≠ 0`) must have `ppar = 0`. -/
def SubtreeInv (P : LctPayload α σ τ) (st : SplayState α σ τ) (rootPar : ℕ) : AuxTree → Prop
  | .leaf => True
  | .node id l r =>
      let nd := st.nodes id
      id ≠ 0 ∧
      nd.left = l.rootId ∧ nd.right = r.rootId ∧
      nd.par = rootPar ∧
      (rootPar ≠ 0 → nd.ppar = 0) ∧
      nd.sz = (AuxTree.node id l r).countNodes ∧
      nd.sum = P.listSummary (evalPairs P st (.node id l r) false P.idTag) ∧
      SubtreeInv P st id l ∧ SubtreeInv P st id r

/-- Full invariant for an auxiliary splay tree `t` stored in `st`. -/
structure TreeInv (P : LctPayload α σ τ) (st : SplayState α σ τ) (t : AuxTree) : Prop where
  nodup : t.toList.Nodup
  sub : SubtreeInv P st 0 t

theorem SubtreeInv_nonZero {P : LctPayload α σ τ} {st : SplayState α σ τ} {rp : ℕ}
    {t : AuxTree} (h : SubtreeInv P st rp t) {u : ℕ} (hu : u ∈ t.toList) : u ≠ 0 := by
  induction t generalizing rp with
  | leaf => simp [AuxTree.toList] at hu
  | node id l r ihl ihr =>
      rcases h with ⟨hid, _, _, _, _, _, _, hl, hr⟩
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
      rcases hu with (h1 | rfl) | h2
      · exact ihl hl h1
      · exact hid
      · exact ihr hr h2

theorem SubtreeInv_agree {P : LctPayload α σ τ} {st₁ st₂ : SplayState α σ τ}
    {rp : ℕ} {t : AuxTree}
    (hsub : SubtreeInv P st₁ rp t)
    (heq : ∀ u ∈ t.toList, st₁.nodes u = st₂.nodes u) :
    SubtreeInv P st₂ rp t := by
  induction t generalizing rp with
  | leaf => trivial
  | node id l r ihl ihr =>
      rcases hsub with ⟨hid, hl_eq, hr_eq, hpar, hpp, hsz, hsum, hl, hr⟩
      have hid_eq := heq id (by simp [AuxTree.toList])
      refine ⟨hid, ?_, ?_, ?_, ?_, ?_, ?_,
        ihl hl (fun u hu => heq u (by simp [AuxTree.toList, hu])),
        ihr hr (fun u hu => heq u (by simp [AuxTree.toList, hu]))⟩
      · simpa [hid_eq] using hl_eq
      · simpa [hid_eq] using hr_eq
      · simpa [hid_eq] using hpar
      · intro hrp; simpa [hid_eq] using hpp hrp
      · simpa [hid_eq] using hsz
      · have hev := evalPairs_agree P heq false P.idTag
        simpa [hid_eq, hev] using hsum

theorem TreeInv_agree {P : LctPayload α σ τ} {st₁ st₂ : SplayState α σ τ} {t : AuxTree}
    (ht : TreeInv P st₁ t) (heq : ∀ u ∈ t.toList, st₁.nodes u = st₂.nodes u) :
    TreeInv P st₂ t :=
  ⟨ht.nodup, SubtreeInv_agree ht.sub heq⟩

theorem SubtreeInv_par_eq_parentIn {P : LctPayload α σ τ} {st : SplayState α σ τ}
    {rp : ℕ} {t : AuxTree} (hnd : t.toList.Nodup) (hsub : SubtreeInv P st rp t)
    {x : ℕ} (hx : x ∈ t.toList) :
    (st.nodes x).par = t.parentIn x rp := by
  induction t generalizing rp with
  | leaf => simp [AuxTree.toList] at hx
  | node id l r ihl ihr =>
      rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, hid_nl, hr_nd, hid_nr, hdisj_lr⟩
      rcases hsub with ⟨_, _, _, hpar, _, _, _, hl, hr⟩
      simp only [AuxTree.parentIn]
      by_cases heq : id = x
      · subst heq; simp [hpar]
      · simp only [heq, ↓reduceIte]
        by_cases hxl : x ∈ l.toList
        · simp only [hxl, ↓reduceIte]; exact ihl hl_nd hl hxl
        · have hxr : x ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hx
            rcases hx with (h | rfl) | h
            · exact absurd h hxl
            · exact absurd rfl heq
            · exact h
          simp only [hxl, ↓reduceIte]; exact ihr hr_nd hr hxr

theorem SubtreeInv_ppar_zero_of_ne_root {P : LctPayload α σ τ} {st : SplayState α σ τ}
    {rp : ℕ} {t : AuxTree} (hnd : t.toList.Nodup) (hsub : SubtreeInv P st rp t)
    {x : ℕ} (hx : x ∈ t.toList) (hxr : rp ≠ 0 ∨ x ≠ t.rootId) :
    (st.nodes x).ppar = 0 := by
  induction t generalizing rp with
  | leaf => simp [AuxTree.toList] at hx
  | node id l r ihl ihr =>
      rcases hsub with ⟨hid, _, _, _, hpp, _, _, hl, hr⟩
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hx
      rcases hx with (h | rfl) | h
      · exact ihl (AuxTree.nodup_node_unfold hnd).1 hl h (Or.inl hid)
      · rcases hxr with hrp | hne
        · exact hpp hrp
        · exact absurd rfl hne
      · exact ihr (AuxTree.nodup_node_unfold hnd).2.2.1 hr h (Or.inl hid)

theorem SubtreeInv_findSubtree {P : LctPayload α σ τ} {st : SplayState α σ τ}
    {rp : ℕ} {t : AuxTree} (hnd : t.toList.Nodup) (hsub : SubtreeInv P st rp t)
    {x : ℕ} (hx : x ∈ t.toList) :
    SubtreeInv P st (t.parentIn x rp) (t.findSubtree x) := by
  induction t generalizing rp with
  | leaf => simp [AuxTree.toList] at hx
  | node id l r ihl ihr =>
      rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, _, hr_nd, _, _⟩
      rcases hsub with ⟨hid, hl_eq, hr_eq, hpar, hpp, hsz, hsum, hl, hr⟩
      simp only [AuxTree.findSubtree, AuxTree.parentIn]
      by_cases heq : id = x
      · subst heq
        simp only [↓reduceIte]
        exact ⟨hid, hl_eq, hr_eq, hpar, hpp, hsz, hsum, hl, hr⟩
      · simp only [heq, ↓reduceIte]
        by_cases hxl : x ∈ l.toList
        · simp only [hxl, ↓reduceIte]; exact ihl hl_nd hl hxl
        · have hxr : x ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hx
            rcases hx with (h | rfl) | h
            · exact absurd h hxl
            · exact absurd rfl heq
            · exact h
          simp only [hxl, ↓reduceIte]; exact ihr hr_nd hr hxr

theorem evalPairs_agree_vrt (P : LctPayload α σ τ) {st₁ st₂ : SplayState α σ τ}
    {t : AuxTree}
    (h : ∀ u ∈ t.toList, (st₁.nodes u).val = (st₂.nodes u).val ∧
      (st₁.nodes u).rev = (st₂.nodes u).rev ∧ (st₁.nodes u).tag = (st₂.nodes u).tag)
    (flip : Bool) (acc : τ) :
    evalPairs P st₁ t flip acc = evalPairs P st₂ t flip acc := by
  induction t generalizing flip acc with
  | leaf => rfl
  | node id l r ihl ihr =>
      rcases h id (by simp [AuxTree.toList]) with ⟨hv, hr, ht⟩
      have hl : ∀ u ∈ l.toList, _ := fun u hu => h u (by simp [AuxTree.toList, hu])
      have hrr : ∀ u ∈ r.toList, _ := fun u hu => h u (by simp [AuxTree.toList, hu])
      cases flip <;> simp only [evalPairs, hv, hr, ht, ihl hl, ihr hrr]

theorem evalPairs_replaceSubtree_clean {P : LctPayload α σ τ} (hL : P.Laws)
    {st st' : SplayState α σ τ} {t s' : AuxTree} {rSub : ℕ}
    (hnd : t.toList.Nodup) (hr : rSub ∈ t.toList)
    (hs'_eval : evalPairs P st' s' false P.idTag =
      evalPairs P st (t.findSubtree rSub) false P.idTag)
    (hanc : ∀ u ∈ t.pathTo rSub, u ≠ rSub → (st.nodes u).rev = false ∧ (st.nodes u).tag = P.idTag)
    (hother : ∀ u ∈ t.toList, u ∉ (t.findSubtree rSub).toList →
      (st'.nodes u).val = (st.nodes u).val ∧
      (st'.nodes u).rev = (st.nodes u).rev ∧
      (st'.nodes u).tag = (st.nodes u).tag) :
    evalPairs P st' (t.replaceSubtree rSub s') false P.idTag =
      evalPairs P st t false P.idTag := by
  induction t with
  | leaf => simp [AuxTree.toList] at hr
  | node id l r ihl ihr =>
      rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, _, hr_nd, _, hdisj_lr⟩
      by_cases hid : id = rSub
      · subst hid; simpa [AuxTree.replaceSubtree, AuxTree.findSubtree] using hs'_eval
      · have hroot_path : id ∈ (AuxTree.node id l r).pathTo rSub := by
          rw [AuxTree.pathTo]
          simp only [Ne.symm hid, ↓reduceIte]
          by_cases hrl : rSub ∈ l.toList
          · simp [hrl]
          · have hrr : rSub ∈ r.toList := by
              simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hr
              rcases hr with (h | rfl) | h
              · exact absurd h hrl
              · exact absurd rfl hid
              · exact h
            simp [hrl, hrr]
        have hanc_self := hanc id hroot_path hid
        have hself_notin : id ∉ ((AuxTree.node id l r).findSubtree rSub).toList := by
          intro h
          have hdep0 : (AuxTree.node id l r).depthOf id = 0 := AuxTree.depthOf_root id l r
          have hdep_r : (AuxTree.node id l r).depthOf rSub ≠ 0 := fun h0 =>
            hid ((AuxTree.depthOf_zero_iff_root hr).mp h0).symm
          exact AuxTree.not_mem_findSubtree_of_ancestor hnd (by simp [AuxTree.toList]) hr
            (by omega) (AuxTree.self_mem_pathTo (by simp [AuxTree.toList])) h
        have hod := hother id (by simp [AuxTree.toList]) hself_notin
        have hrev_id' : (st'.nodes id).rev = false := hod.2.1 ▸ hanc_self.1
        have htag_id' : (st'.nodes id).tag = P.idTag := hod.2.2 ▸ hanc_self.2
        simp only [AuxTree.replaceSubtree, hid, ↓reduceIte]
        by_cases hrl : rSub ∈ l.toList
        · have hnr : rSub ∉ r.toList := hdisj_lr rSub hrl
          rw [AuxTree.replaceSubtree_not_mem hnr]
          have hfind_eq : (AuxTree.node id l r).findSubtree rSub = l.findSubtree rSub := by
            simp [AuxTree.findSubtree, hid, hrl]
          have heval_r : evalPairs P st' r false P.idTag = evalPairs P st r false P.idTag := by
            refine evalPairs_agree_vrt P (fun u hu => hother u (by simp [AuxTree.toList, hu]) ?_) false P.idTag
            rw [hfind_eq]
            intro hmem; exact hdisj_lr u (AuxTree.findSubtree_subset hmem) hu
          have hanc_l : ∀ u ∈ l.pathTo rSub, u ≠ rSub →
              (st.nodes u).rev = false ∧ (st.nodes u).tag = P.idTag := by
            intro u hu hne
            exact hanc u (by rw [AuxTree.pathTo]; simp [Ne.symm hid, hrl, hu]) hne
          have hother_l : ∀ u ∈ l.toList, u ∉ (l.findSubtree rSub).toList →
              (st'.nodes u).val = (st.nodes u).val ∧
              (st'.nodes u).rev = (st.nodes u).rev ∧
              (st'.nodes u).tag = (st.nodes u).tag := by
            intro u hu hnin
            refine hother u (by simp [AuxTree.toList, hu]) ?_
            simpa [hfind_eq] using hnin
          have heval_l := ihl hl_nd hrl (by simpa [hfind_eq] using hs'_eval) hanc_l hother_l
          simp only [evalPairs, hod.1, hrev_id', htag_id', hanc_self.1, hanc_self.2,
            Bool.false_xor, Bool.false_eq_true, ↓reduceIte, hL.compTag_id_left, heval_l, heval_r]
        · have hrr : rSub ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hr
            rcases hr with (h | rfl) | h
            · exact absurd h hrl
            · exact absurd rfl hid
            · exact h
          rw [AuxTree.replaceSubtree_not_mem hrl]
          have hfind_eq : (AuxTree.node id l r).findSubtree rSub = r.findSubtree rSub := by
            simp [AuxTree.findSubtree, hid, hrl]
          have heval_l : evalPairs P st' l false P.idTag = evalPairs P st l false P.idTag := by
            refine evalPairs_agree_vrt P (fun u hu => hother u (by simp [AuxTree.toList, hu]) ?_) false P.idTag
            rw [hfind_eq]
            intro hmem; exact hdisj_lr u hu (AuxTree.findSubtree_subset hmem)
          have hanc_r : ∀ u ∈ r.pathTo rSub, u ≠ rSub →
              (st.nodes u).rev = false ∧ (st.nodes u).tag = P.idTag := by
            intro u hu hne
            exact hanc u (by rw [AuxTree.pathTo]; simp [Ne.symm hid, hrl, hrr, hu]) hne
          have hother_r : ∀ u ∈ r.toList, u ∉ (r.findSubtree rSub).toList →
              (st'.nodes u).val = (st.nodes u).val ∧
              (st'.nodes u).rev = (st.nodes u).rev ∧
              (st'.nodes u).tag = (st.nodes u).tag := by
            intro u hu hnin
            refine hother u (by simp [AuxTree.toList, hu]) ?_
            simpa [hfind_eq] using hnin
          have heval_r := ihr hr_nd hrr (by simpa [hfind_eq] using hs'_eval) hanc_r hother_r
          simp only [evalPairs, hod.1, hrev_id', htag_id', hanc_self.1, hanc_self.2,
            Bool.false_xor, Bool.false_eq_true, ↓reduceIte, hL.compTag_id_left, heval_l, heval_r]

theorem SubtreeInv_replaceSubtree_clean {P : LctPayload α σ τ} (hL : P.Laws)
    {st st' : SplayState α σ τ} {rp : ℕ} {t s' : AuxTree} {rSub : ℕ}
    (hnd : t.toList.Nodup) (hsub : SubtreeInv P st rp t) (hr : rSub ∈ t.toList)
    (hs'_ne : s' ≠ .leaf) (hs'_perm : s'.toList.Perm (t.findSubtree rSub).toList)
    (hs'_sub : SubtreeInv P st' (t.parentIn rSub rp) s')
    (hs'_eval : evalPairs P st' s' false P.idTag =
      evalPairs P st (t.findSubtree rSub) false P.idTag)
    (hanc : ∀ u ∈ t.pathTo rSub, u ≠ rSub → (st.nodes u).rev = false ∧ (st.nodes u).tag = P.idTag)
    (hother : ∀ u ∈ t.toList, u ∉ (t.findSubtree rSub).toList →
      (st'.nodes u).val = (st.nodes u).val ∧
      (st'.nodes u).rev = (st.nodes u).rev ∧
      (st'.nodes u).tag = (st.nodes u).tag ∧
      (st'.nodes u).par = (st.nodes u).par ∧
      (st'.nodes u).ppar = (st.nodes u).ppar ∧
      (st'.nodes u).sz = (st.nodes u).sz ∧
      (st'.nodes u).sum = (st.nodes u).sum ∧
      (u ≠ t.parentIn rSub rp →
        (st'.nodes u).left = (st.nodes u).left ∧ (st'.nodes u).right = (st.nodes u).right) ∧
      (u = t.parentIn rSub rp →
        (st'.nodes u).left = (if (st.nodes u).left = rSub then s'.rootId else (st.nodes u).left) ∧
        (st'.nodes u).right = (if (st.nodes u).right = rSub then s'.rootId else (st.nodes u).right))) :
    SubtreeInv P st' rp (t.replaceSubtree rSub s') := by
  have heval_vrt : ∀ u ∈ t.toList, u ∉ (t.findSubtree rSub).toList →
      (st'.nodes u).val = (st.nodes u).val ∧
      (st'.nodes u).rev = (st.nodes u).rev ∧
      (st'.nodes u).tag = (st.nodes u).tag := fun u hu hnin =>
    let ho := hother u hu hnin
    ⟨ho.1, ho.2.1, ho.2.2.1⟩
  have heval_t := evalPairs_replaceSubtree_clean hL hnd hr hs'_eval hanc heval_vrt
  induction t generalizing rp with
  | leaf => simp [AuxTree.toList] at hr
  | node id l r ihl ihr =>
      rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, hid_nl, hr_nd, hid_nr, hdisj_lr⟩
      rcases hsub with ⟨hid, hl_eq, hr_eq, hpar, hpp, hsz, hsum, hl, hr_sub⟩
      by_cases hid_r : id = rSub
      · subst hid_r
        simp only [AuxTree.replaceSubtree, ↓reduceIte]
        simpa [AuxTree.parentIn] using hs'_sub
      · simp only [AuxTree.replaceSubtree, hid_r, ↓reduceIte]
        have hself_notin : id ∉ ((AuxTree.node id l r).findSubtree rSub).toList := by
          intro h
          have hdep0 : (AuxTree.node id l r).depthOf id = 0 := AuxTree.depthOf_root id l r
          have hdep_r : (AuxTree.node id l r).depthOf rSub ≠ 0 := fun h0 =>
            hid_r ((AuxTree.depthOf_zero_iff_root hr).mp h0).symm
          exact AuxTree.not_mem_findSubtree_of_ancestor hnd (by simp [AuxTree.toList]) hr
            (by omega) (AuxTree.self_mem_pathTo (by simp [AuxTree.toList])) h
        have hod := hother id (by simp [AuxTree.toList]) hself_notin
        have hcnt : ((AuxTree.node id l r).replaceSubtree rSub s').countNodes =
            (AuxTree.node id l r).countNodes := by
          rw [← AuxTree.length_toList, ← AuxTree.length_toList]
          exact (AuxTree.replaceSubtree_perm hnd hr hs'_perm).length_eq
        simp only [AuxTree.replaceSubtree, hid_r, ↓reduceIte] at hcnt heval_t
        by_cases hrl : rSub ∈ l.toList
        · have hnr : rSub ∉ r.toList := hdisj_lr rSub hrl
          rw [AuxTree.replaceSubtree_not_mem hnr] at hcnt heval_t ⊢
          have hfind_eq : (AuxTree.node id l r).findSubtree rSub = l.findSubtree rSub := by
            simp [AuxTree.findSubtree, hid_r, hrl]
          have hpar_eq : (AuxTree.node id l r).parentIn rSub rp = l.parentIn rSub id := by
            simp [AuxTree.parentIn, hid_r, hrl]
          have hleft' : (st'.nodes id).left = (l.replaceSubtree rSub s').rootId := by
            by_cases hlr_root : l.rootId = rSub
            · have hid_p : id = (AuxTree.node id l r).parentIn rSub rp := by
                cases l with
                | leaf => simp [AuxTree.toList] at hrl
                | node lid _ _ =>
                    simp only [AuxTree.rootId] at hlr_root; subst hlr_root
                    simp [AuxTree.parentIn, hid_r, AuxTree.toList]
              have hcl := (hod.2.2.2.2.2.2.2.2 hid_p).1
              rw [hl_eq, hlr_root] at hcl; simp only [↓reduceIte] at hcl
              have hl_ne : l ≠ .leaf := fun h => by subst h; simp [AuxTree.toList] at hrl
              rw [hcl, AuxTree.replaceSubtree_rootId hl_ne hs'_ne, ite_eq_left hlr_root]
            · have hl_ne : l ≠ .leaf := fun h => by subst h; simp [AuxTree.toList] at hrl
              have hroot_rep : (l.replaceSubtree rSub s').rootId = l.rootId := by
                rw [AuxTree.replaceSubtree_rootId hl_ne hs'_ne, ite_eq_right hlr_root]
              rw [hroot_rep]
              by_cases hid_p : id = (AuxTree.node id l r).parentIn rSub rp
              · have hcl := (hod.2.2.2.2.2.2.2.2 hid_p).1
                rw [hl_eq] at hcl; simp only [hlr_root, ↓reduceIte] at hcl; rw [hcl]
              · rw [(hod.2.2.2.2.2.2.2.1 hid_p).1, hl_eq]
          have hright' : (st'.nodes id).right = r.rootId := by
            have hr_ne_rSub : r.rootId ≠ rSub := by
              cases r with
              | leaf => exact fun h => by subst h; exact absurd hrl (by
                  intro hm; exact SubtreeInv_nonZero hl hm rfl)
              | node rid _ _ =>
                  intro h; simp only [AuxTree.rootId] at h; subst h; exact hnr (by simp [AuxTree.toList])
            by_cases hid_p : id = (AuxTree.node id l r).parentIn rSub rp
            · have hcr := (hod.2.2.2.2.2.2.2.2 hid_p).2
              rw [hr_eq] at hcr; simp only [hr_ne_rSub, ↓reduceIte] at hcr; rw [hcr]
            · rw [(hod.2.2.2.2.2.2.2.1 hid_p).2, hr_eq]
          have hr_sub' : SubtreeInv P st' id r := by
            refine SubtreeInv_agree hr_sub (fun u hu => ?_)
            have hu_notin : u ∉ ((AuxTree.node id l r).findSubtree rSub).toList := by
              rw [hfind_eq]
              intro hm; exact hdisj_lr u (AuxTree.findSubtree_subset hm) hu
            have hu_ne_p : u ≠ (AuxTree.node id l r).parentIn rSub rp := by
              rw [hpar_eq]
              by_cases hlr_root : rSub = l.rootId
              · cases l with
                | leaf => simp [AuxTree.toList] at hrl
                | node lid _ _ =>
                    simp only [AuxTree.rootId] at hlr_root; subst hlr_root
                    simp only [AuxTree.parentIn, ↓reduceIte]
                    intro heq; exact hid_nr (heq ▸ hu)
              · have hp_mem_l : l.parentIn rSub id ∈ l.toList :=
                  (AuxTree.parentIn_mem_and_depth hl_nd hrl hlr_root).1
                intro heq; exact hdisj_lr u (heq ▸ hp_mem_l) hu
            have ho_u := hother u (by simp [AuxTree.toList, hu]) hu_notin
            rcases ho_u with ⟨h1, h2, h3, h4, h5, h6, h7, hlr_u, _⟩
            rcases hlr_u hu_ne_p with ⟨h8, h9⟩
            exact (SplayNode.ext_fields h1 h2 h3 h4 h5 h6 h7 h8 h9).symm
          have hs'_perm_l : s'.toList.Perm (l.findSubtree rSub).toList := by
            simpa [hfind_eq] using hs'_perm
          have hs'_sub_l : SubtreeInv P st' (l.parentIn rSub id) s' := by
            simpa [hpar_eq] using hs'_sub
          have hs'_eval_l : evalPairs P st' s' false P.idTag =
              evalPairs P st (l.findSubtree rSub) false P.idTag := by
            simpa [hfind_eq] using hs'_eval
          have hanc_l : ∀ u ∈ l.pathTo rSub, u ≠ rSub →
              (st.nodes u).rev = false ∧ (st.nodes u).tag = P.idTag := fun u hu hne =>
            hanc u (by rw [AuxTree.pathTo]; simp [Ne.symm hid_r, hrl, hu]) hne
          have hl' := ihl hl_nd hl hrl hs'_perm_l hs'_sub_l hs'_eval_l hanc_l
            (fun u hu hnin => by
              have ho_u := hother u (by simp [AuxTree.toList, hu]) (by simpa [hfind_eq] using hnin)
              simpa [hpar_eq] using ho_u)
            (fun u hu hnin => by
              have ho_u := hother u (by simp [AuxTree.toList, hu]) (by simpa [hfind_eq] using hnin)
              exact ⟨ho_u.1, ho_u.2.1, ho_u.2.2.1⟩)
            (evalPairs_replaceSubtree_clean hL hl_nd hrl hs'_eval_l hanc_l
              (fun u hu hnin => by
                have ho_u := hother u (by simp [AuxTree.toList, hu]) (by simpa [hfind_eq] using hnin)
                exact ⟨ho_u.1, ho_u.2.1, ho_u.2.2.1⟩))
          refine ⟨hid, hleft', hright', hod.2.2.2.1.trans hpar,
            fun hrp => hod.2.2.2.2.1.trans (hpp hrp),
            hod.2.2.2.2.2.1.trans (hsz.trans hcnt.symm),
            hod.2.2.2.2.2.2.1.trans (by rw [hsum, heval_t]), hl', hr_sub'⟩
        · have hrr : rSub ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hr
            rcases hr with (h | rfl) | h
            · exact absurd h hrl
            · exact absurd rfl hid_r
            · exact h
          rw [AuxTree.replaceSubtree_not_mem hrl] at hcnt heval_t ⊢
          have hfind_eq : (AuxTree.node id l r).findSubtree rSub = r.findSubtree rSub := by
            simp [AuxTree.findSubtree, hid_r, hrl]
          have hpar_eq : (AuxTree.node id l r).parentIn rSub rp = r.parentIn rSub id := by
            simp [AuxTree.parentIn, hid_r, hrl]
          have hleft' : (st'.nodes id).left = l.rootId := by
            have hl_ne_rSub : l.rootId ≠ rSub := by
              cases l with
              | leaf => exact fun h => by subst h; exact absurd hrr (by
                  intro hm; exact SubtreeInv_nonZero hr_sub hm rfl)
              | node lid _ _ =>
                  intro h; simp only [AuxTree.rootId] at h; subst h; exact hrl (by simp [AuxTree.toList])
            by_cases hid_p : id = (AuxTree.node id l r).parentIn rSub rp
            · have hcl := (hod.2.2.2.2.2.2.2.2 hid_p).1
              rw [hl_eq] at hcl; simp only [hl_ne_rSub, ↓reduceIte] at hcl; rw [hcl]
            · rw [(hod.2.2.2.2.2.2.2.1 hid_p).1, hl_eq]
          have hright' : (st'.nodes id).right = (r.replaceSubtree rSub s').rootId := by
            by_cases hrr_root : r.rootId = rSub
            · have hid_p : id = (AuxTree.node id l r).parentIn rSub rp := by
                cases r with
                | leaf => simp [AuxTree.toList] at hrr
                | node rid _ _ =>
                    simp only [AuxTree.rootId] at hrr_root; subst hrr_root
                    simp [AuxTree.parentIn, hid_r, hrl]
              have hcr := (hod.2.2.2.2.2.2.2.2 hid_p).2
              rw [hr_eq, hrr_root] at hcr; simp only [↓reduceIte] at hcr
              have hr_ne : r ≠ .leaf := fun h => by subst h; simp [AuxTree.toList] at hrr
              rw [hcr, AuxTree.replaceSubtree_rootId hr_ne hs'_ne, ite_eq_left hrr_root]
            · have hr_ne : r ≠ .leaf := fun h => by subst h; simp [AuxTree.toList] at hrr
              have hroot_rep : (r.replaceSubtree rSub s').rootId = r.rootId := by
                rw [AuxTree.replaceSubtree_rootId hr_ne hs'_ne, ite_eq_right hrr_root]
              rw [hroot_rep]
              by_cases hid_p : id = (AuxTree.node id l r).parentIn rSub rp
              · have hcr := (hod.2.2.2.2.2.2.2.2 hid_p).2
                rw [hr_eq] at hcr; simp only [hrr_root, ↓reduceIte] at hcr; rw [hcr]
              · rw [(hod.2.2.2.2.2.2.2.1 hid_p).2, hr_eq]
          have hl_sub' : SubtreeInv P st' id l := by
            refine SubtreeInv_agree hl (fun u hu => ?_)
            have hu_notin : u ∉ ((AuxTree.node id l r).findSubtree rSub).toList := by
              rw [hfind_eq]
              intro hm; exact hdisj_lr u hu (AuxTree.findSubtree_subset hm)
            have hu_ne_p : u ≠ (AuxTree.node id l r).parentIn rSub rp := by
              rw [hpar_eq]
              by_cases hrr_root : rSub = r.rootId
              · cases r with
                | leaf => simp [AuxTree.toList] at hrr
                | node rid _ _ =>
                    simp only [AuxTree.rootId] at hrr_root; subst hrr_root
                    simp only [AuxTree.parentIn, ↓reduceIte]
                    intro heq; exact hid_nl (heq ▸ hu)
              · have hp_mem_r : r.parentIn rSub id ∈ r.toList :=
                  (AuxTree.parentIn_mem_and_depth hr_nd hrr hrr_root).1
                intro heq; exact hdisj_lr u hu (heq ▸ hp_mem_r)
            have ho_u := hother u (by simp [AuxTree.toList, hu]) hu_notin
            rcases ho_u with ⟨h1, h2, h3, h4, h5, h6, h7, hlr_u, _⟩
            rcases hlr_u hu_ne_p with ⟨h8, h9⟩
            exact (SplayNode.ext_fields h1 h2 h3 h4 h5 h6 h7 h8 h9).symm
          have hs'_perm_r : s'.toList.Perm (r.findSubtree rSub).toList := by
            simpa [hfind_eq] using hs'_perm
          have hs'_sub_r : SubtreeInv P st' (r.parentIn rSub id) s' := by
            simpa [hpar_eq] using hs'_sub
          have hs'_eval_r : evalPairs P st' s' false P.idTag =
              evalPairs P st (r.findSubtree rSub) false P.idTag := by
            simpa [hfind_eq] using hs'_eval
          have hanc_r : ∀ u ∈ r.pathTo rSub, u ≠ rSub →
              (st.nodes u).rev = false ∧ (st.nodes u).tag = P.idTag := fun u hu hne =>
            hanc u (by rw [AuxTree.pathTo]; simp [Ne.symm hid_r, hrl, hrr, hu]) hne
          have hr' := ihr hr_nd hr_sub hrr hs'_perm_r hs'_sub_r hs'_eval_r hanc_r
            (fun u hu hnin => by
              have ho_u := hother u (by simp [AuxTree.toList, hu]) (by simpa [hfind_eq] using hnin)
              simpa [hpar_eq] using ho_u)
            (fun u hu hnin => by
              have ho_u := hother u (by simp [AuxTree.toList, hu]) (by simpa [hfind_eq] using hnin)
              exact ⟨ho_u.1, ho_u.2.1, ho_u.2.2.1⟩)
            (evalPairs_replaceSubtree_clean hL hr_nd hrr hs'_eval_r hanc_r
              (fun u hu hnin => by
                have ho_u := hother u (by simp [AuxTree.toList, hu]) (by simpa [hfind_eq] using hnin)
                exact ⟨ho_u.1, ho_u.2.1, ho_u.2.2.1⟩))
          refine ⟨hid, hleft', hright', hod.2.2.2.1.trans hpar,
            fun hrp => hod.2.2.2.2.1.trans (hpp hrp),
            hod.2.2.2.2.2.1.trans (hsz.trans hcnt.symm),
            hod.2.2.2.2.2.2.1.trans (by rw [hsum, heval_t]), hl_sub', hr'⟩

end SplayState

end MinCostFlow.LinkCut
