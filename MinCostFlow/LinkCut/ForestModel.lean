module

public import MinCostFlow.LinkCut.SplayQuery
import Mathlib.Tactic

/-!
# Subdivided Link-Cut Tree Model over `SplayState`

This file defines the pure Link-Cut Tree model (`LctState`) over subdivided auxiliary splay
trees (`SplayState`), its invariant (`LctInv` / `LctInvWith`), and its Sleator–Tarjan plus
heavy-light potential components (`sumTreePhi`, `heavyCount`):

- Vertices `0 .. n - 1` map to 1-based node IDs `vid v = v + 1` in `1 .. n`.
- Edge slots occupy `n + 1 .. 2 * n - 1` and unused slots form a singly-linked free list
  threaded through `(splay.nodes e).par` starting at `freeHead`.
- Active nodes partition into disjoint nonempty auxiliary trees (`TreeInv P st.splay t`), whose
  in-order sequences (`treeIds`) together with root `ppar` links define the parent function
  `inducedSubPar` of a rooted subdivided forest.
- Virtual subtree weights `vSize` make `t.treeSize vSize` equal the represented subtree size
  `repSize` of `t`'s logical topmost node, giving exact `sumTreePhi` conservation under
  `detachRight` and `attachRight`.

This generic layer supports both the pure `DynForest` model (`RoundingPayload`) and the
Word-RAM Link-Cut Tree procedures.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

variable {α σ τ : Type*}

/-! ### Node classification, state, and free-list invariants -/

/-- 1-based node ID for vertex `v` (`0 ≤ v < n`). -/
def vid (v : ℕ) : ℕ := v + 1

/-- Whether `x` is a valid vertex node ID (`1 ≤ x ≤ n`). -/
def isVertex (n x : ℕ) : Prop := 1 ≤ x ∧ x ≤ n

/-- Whether `x` is a valid edge-slot node ID (`n + 1 ≤ x < 2 * n`). -/
def isEdgeSlot (n x : ℕ) : Prop := n + 1 ≤ x ∧ x < 2 * n

/-- Whether `x` is a valid node ID (`1 ≤ x < 2 * n`). -/
def isNode (n x : ℕ) : Prop := 1 ≤ x ∧ x < 2 * n

theorem vid_isVertex {n v : ℕ} (hv : v < n) : isVertex n (vid v) :=
  ⟨by simp [vid], by simp [vid]; omega⟩

theorem isNode_iff_vertex_or_edge {n x : ℕ} :
    isNode n x ↔ isVertex n x ∨ isEdgeSlot n x := by
  simp only [isNode, isVertex, isEdgeSlot]
  omega

theorem not_vertex_and_edge {n x : ℕ} : ¬ (isVertex n x ∧ isEdgeSlot n x) := by
  simp only [isVertex, isEdgeSlot]
  omega

/-- Stateful Link-Cut Tree configuration on `n` vertices. -/
structure LctState (α σ τ : Type*) where
  n : ℕ
  splay : SplayState α σ τ
  freeHead : ℕ

/-- Invariant for the singly-linked free list of edge slots threaded via `.par`. -/
def FreeListInv (s : SplayState α σ τ) (h : ℕ) : List ℕ → Prop
  | [] => h = 0
  | e :: rest => h ≠ 0 ∧ h = e ∧ FreeListInv s (s.nodes h).par rest

theorem FreeListInv_agree {s₁ s₂ : SplayState α σ τ} {h : ℕ} {fl : List ℕ}
    (hinv : FreeListInv s₁ h fl)
    (hag : ∀ e ∈ fl, (s₂.nodes e).par = (s₁.nodes e).par) :
    FreeListInv s₂ h fl := by
  induction fl generalizing h with
  | nil => exact hinv
  | cons e rest ih =>
      rcases hinv with ⟨hnz, rfl, hrest⟩
      refine ⟨hnz, rfl, ?_⟩
      rw [hag h (by simp)]
      exact ih hrest (fun x hx => hag x (by simp [hx]))

/-- Canonical free-list traversal from `h` bounded by `k` steps. -/
def canonFreeList (s : SplayState α σ τ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, h => if h = 0 then [] else h :: canonFreeList s k (s.nodes h).par

theorem canonFreeList_eq_of_FreeListInv {s : SplayState α σ τ} {h : ℕ} {fl : List ℕ} {k : ℕ}
    (hinv : FreeListInv s h fl) (hk : fl.length ≤ k) :
    canonFreeList s k h = fl := by
  induction fl generalizing h k with
  | nil =>
      have hh : h = 0 := hinv
      cases k <;> simp [canonFreeList, hh]
  | cons e rest ih =>
      cases k with
      | zero => simp at hk
      | succ k' =>
          rcases hinv with ⟨hnz, rfl, hrest⟩
          simp only [canonFreeList, hnz, ↓reduceIte]
          congr 1
          exact ih hrest (by simp at hk; omega)

/-- Reconstruct an `AuxTree` from `left`/`right` pointers in `s` up to depth `k`. -/
def buildAuxTree (s : SplayState α σ τ) : ℕ → ℕ → AuxTree
  | 0, _ => .leaf
  | k + 1, x =>
      if x = 0 then .leaf
      else
        let nd := s.nodes x
        .node x (buildAuxTree s k nd.left) (buildAuxTree s k nd.right)

theorem buildAuxTree_eq {P : LctPayload α σ τ} {s : SplayState α σ τ} {rp k : ℕ} {t : AuxTree}
    (hsub : SplayState.SubtreeInv P s rp t) (hk : t.countNodes ≤ k) :
    buildAuxTree s k t.rootId = t := by
  induction t generalizing rp k with
  | leaf =>
      cases k <;> simp [buildAuxTree, AuxTree.rootId]
  | node id l r ihl ihr =>
      cases k with
      | zero => simp [AuxTree.countNodes] at hk
      | succ k' =>
          rcases hsub with ⟨hid, hl, hr, _, _, _, _, hsub_l, hsub_r⟩
          simp only [AuxTree.countNodes] at hk
          simp only [AuxTree.rootId, buildAuxTree, hid, ↓reduceIte]
          congr 1
          · rw [hl]; exact ihl hsub_l (by omega)
          · rw [hr]; exact ihr hsub_r (by omega)

/-! ### Canonical active list, roots, induced parent map, and represented sizes -/

/-- Canonical list of active node IDs derived purely from `st`. -/
def canonActive (st : LctState α σ τ) : List ℕ :=
  (List.range' 1 (2 * st.n - 1)).filter
    (· ∉ canonFreeList st.splay st.n st.freeHead)

/-- Canonical list of auxiliary-tree roots derived purely from `st`. -/
def canonRoots (st : LctState α σ τ) : List ℕ :=
  (canonActive st).filter (fun r => (st.splay.nodes r).par == 0)

/-- Canonical list of auxiliary trees derived purely from `st`. -/
def canonTrees (st : LctState α σ τ) : List AuxTree :=
  (canonRoots st).map (buildAuxTree st.splay (2 * st.n))

/-- Logical in-order list of node IDs in `t` (`flip = false, acc = P.idTag`). -/
def treeIds (P : LctPayload α σ τ) (s : SplayState α σ τ) (t : AuxTree) : List ℕ :=
  (SplayState.evalPairs P s t false P.idTag).map Prod.fst

theorem mem_treeIds_iff (P : LctPayload α σ τ) (s : SplayState α σ τ) (t : AuxTree) (x : ℕ) :
    x ∈ treeIds P s t ↔ x ∈ t.toList := by
  simp only [treeIds, SplayState.evalPairs_map_fst]
  exact (AuxTree.evalInorder_perm _ _ _).mem_iff

theorem treeIds_nodup {P : LctPayload α σ τ} {s : SplayState α σ τ} {t : AuxTree}
    (ht : SplayState.TreeInv P s t) : (treeIds P s t).Nodup := by
  have hp : (treeIds P s t).Perm t.toList := by
    simp only [treeIds, SplayState.evalPairs_map_fst]
    exact AuxTree.evalInorder_perm _ _ _
  exact hp.nodup_iff.mpr ht.nodup

theorem treeIds_ne_nil {P : LctPayload α σ τ} {s : SplayState α σ τ} {t : AuxTree}
    (hne : t ≠ .leaf) : treeIds P s t ≠ [] := by
  intro h
  have hlen : (treeIds P s t).length = t.countNodes := by
    simp only [treeIds, List.length_map, SplayState.evalPairs_length]
  rw [h, List.length_nil] at hlen
  cases t with
  | leaf => exact absurd rfl hne
  | node _ _ _ => simp [AuxTree.countNodes] at hlen; omega

/-- Topmost node (head of `ids`) in a nonempty list `ids`, defaulting to `0` on `[]`. -/
def listHead0 : List ℕ → ℕ
  | [] => 0
  | x :: _ => x

/-- Predecessor of `x` along a list `xs` whose head has predecessor `prev` (`0` if `x ∉ xs`). -/
def chainPred (prev : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: rest, x => if x = a then prev else chainPred a rest x

theorem chainPred_mem_append_left {prev : ℕ} {xs₁ xs₂ : List ℕ} {x : ℕ}
    (hx : x ∈ xs₁) : chainPred prev (xs₁ ++ xs₂) x = chainPred prev xs₁ x := by
  induction xs₁ generalizing prev with
  | nil => simp at hx
  | cons a rest ih =>
      simp only [List.cons_append, chainPred]
      by_cases hxa : x = a
      · simp [hxa]
      · simp only [hxa, ↓reduceIte]
        exact ih (by simpa [hxa] using hx)

theorem chainPred_mem_append_right {prev b : ℕ} {xs₁ xs₂ : List ℕ} {x : ℕ}
    (hnd : (xs₁ ++ xs₂).Nodup) (hx : x ∈ xs₂) (hl : xs₁.getLast? = some b) :
    chainPred prev (xs₁ ++ xs₂) x = chainPred b xs₂ x := by
  induction xs₁ generalizing prev with
  | nil => simp at hl
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hl
          subst hl
          have hxa : x ≠ a := fun h => by
            have := hnd; simp [List.nodup_cons, h ▸ hx] at this
          simp [chainPred, hxa]
      | cons c cs =>
          have hxa : x ≠ a := fun h => by
            have := hnd; simp [List.nodup_cons, h ▸ hx] at this
          simp only [List.cons_append, chainPred, hxa, ↓reduceIte]
          have hnd' : ((c :: cs) ++ xs₂).Nodup := by
            simpa [List.nodup_cons] using hnd.of_cons
          have hl' : (c :: cs).getLast? = some b := by simpa using hl
          exact ih hnd' hl'

theorem chainPred_eq_zero_of_not_mem {prev : ℕ} {xs : List ℕ} {x : ℕ}
    (hx : x ∉ xs) : chainPred prev xs x = 0 := by
  induction xs generalizing prev with
  | nil => rfl
  | cons a rest ih =>
      have hxa : x ≠ a := fun h => hx (by simp [h])
      simp only [chainPred, hxa, ↓reduceIte]
      exact ih (fun h => hx (by simp [h]))

theorem chainPred_mem_or_prev {prev : ℕ} {xs : List ℕ} {x : ℕ}
    (hx : x ∈ xs) :
    chainPred prev xs x = prev ∨ chainPred prev xs x ∈ xs := by
  induction xs generalizing prev with
  | nil => simp at hx
  | cons a rest ih =>
      by_cases hxa : x = a
      · left; simp [chainPred, hxa]
      · simp only [chainPred, hxa, ↓reduceIte]
        rcases ih (by simpa [hxa] using hx) with h | h
        · right; rw [h]; exact List.mem_cons_self
        · right; exact List.mem_cons_of_mem a h

theorem chainPred_head {prev a : ℕ} {rest : List ℕ} :
    chainPred prev (a :: rest) a = prev := by
  simp [chainPred]

theorem chainPred_reverse_iff {xs : List ℕ} (hnd : xs.Nodup) (hz : 0 ∉ xs)
    {x y : ℕ} (hx : x ∈ xs) (hy : y ∈ xs) :
    chainPred 0 xs.reverse x = y ↔ chainPred 0 xs y = x := by
  induction xs generalizing x y with
  | nil => simp at hx
  | cons a rest ih =>
      rcases List.nodup_cons.mp hnd with ⟨ha_nrest, hrest_nd⟩
      have ha_nz : 0 ≠ a := fun h => hz (by simp [h])
      have hz_rest : 0 ∉ rest := fun h => hz (by simp [h])
      cases rest with
      | nil =>
          have hxa : x = a := by simpa using hx
          have hya : y = a := by simpa using hy
          rw [hxa, hya]
          simp [chainPred, ha_nz]
      | cons b bs =>
          have hrev_last : (b :: bs).reverse.getLast? = some b := by
            simp [List.getLast?_reverse]
          have hnd_rev : ((b :: bs).reverse ++ [a]).Nodup := by
            rw [← List.reverse_cons]
            exact List.nodup_reverse.mpr hnd
          by_cases hxa : x = a
          · rw [hxa]
            have hlhs : chainPred 0 ((b :: bs).reverse ++ [a]) a = b := by
              rw [chainPred_mem_append_right hnd_rev (by simp) hrev_last]
              simp [chainPred]
            rw [List.reverse_cons, hlhs]
            by_cases hya : y = a
            · rw [hya]
              have hba : b ≠ a := fun h => ha_nrest (by simp [h])
              simp [chainPred, hba, ha_nz]
            · by_cases hyb : y = b
              · rw [hyb]
                have hba : b ≠ a := fun h => ha_nrest (by simp [h])
                simp [chainPred, hba]
              · have hy_bs : y ∈ bs := by
                  rcases List.mem_cons.mp hy with hy1 | hy1
                  · exact absurd hy1 hya
                  · rcases List.mem_cons.mp hy1 with hy2 | hy2
                    · exact absurd hy2 hyb
                    · exact hy2
                simp only [chainPred, hya, hyb, ↓reduceIte]
                constructor
                · intro h; exact absurd h (Ne.symm hyb)
                · intro h
                  rcases chainPred_mem_or_prev (prev := b) hy_bs with h1 | h1
                  · exact absurd h1 (h.symm ▸ fun hb => ha_nrest (by simp [hb]))
                  · exact absurd (h ▸ h1) (fun hm => ha_nrest (by simp [hm]))
          · have hx_rest : x ∈ b :: bs := by simpa [hxa] using hx
            have hlhs : chainPred 0 ((b :: bs).reverse ++ [a]) x =
                chainPred 0 (b :: bs).reverse x :=
              chainPred_mem_append_left (List.mem_reverse.mpr hx_rest)
            rw [List.reverse_cons, hlhs]
            by_cases hya : y = a
            · rw [hya]
              simp only [chainPred, ↓reduceIte]
              constructor
              · intro h
                have hx_nz : x ≠ 0 := fun h0 => hz_rest (h0 ▸ hx_rest)
                rcases chainPred_mem_or_prev (prev := 0) (xs := (b :: bs).reverse)
                    (List.mem_reverse.mpr hx_rest) with h1 | h1
                · rw [h1] at h; exact absurd h ha_nz
                · rw [h] at h1; exact absurd (List.mem_reverse.mp h1) ha_nrest
              · intro h; exact absurd h.symm (fun h0 => hz_rest (h0 ▸ hx_rest))
            · have hy_rest : y ∈ b :: bs := by simpa [hya] using hy
              have ih_xy := ih hrest_nd hz_rest hx_rest hy_rest
              by_cases hyb : y = b
              · rw [hyb] at ih_xy ⊢
                have hx_nz : x ≠ 0 := fun h0 => hz_rest (h0 ▸ hx_rest)
                have hba : b ≠ a := fun h => ha_nrest (by simp [h])
                rw [ih_xy]
                simp [chainPred, hba, Ne.symm hxa, Ne.symm hx_nz]
              · have hy_bs : y ∈ bs := by simpa [hyb] using hy_rest
                rw [ih_xy]
                simp [chainPred, hya, hyb]

/-! ### Induced parent map, reachability, represented sizes, heavy-light count, and potential -/

/-- Subdivided forest parent of `x` induced by auxiliary trees `ts` in `s` (`0` if root or outside). -/
def inducedSubPar (P : LctPayload α σ τ) (s : SplayState α σ τ) : List AuxTree → ℕ → ℕ
  | [], _ => 0
  | t :: ts, x =>
      let ids := treeIds P s t
      if x ∈ ids then chainPred (s.nodes t.rootId).ppar ids x
      else inducedSubPar P s ts x

/-- Walk `k` steps up `par` to test if `x` is in the subtree rooted at `u`. -/
def reaches (par : ℕ → ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, u, x => x == u
  | k + 1, u, x =>
      if x == u then true
      else if par x == 0 then false
      else reaches par k u (par x)

/-- Walk `k` steps up `par` to find the root of `x`'s component. -/
def subRoot (par : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => if par x = 0 then x else subRoot par k (par x)

/-- Represented subtree size of `u` within active list `active` under parent map `par`. -/
def repSize (active : List ℕ) (par : ℕ → ℕ) (u : ℕ) : ℕ :=
  (active.filter (fun x => reaches par active.length u x)).length

/-- Virtual subtree weight of `u` across auxiliary trees `ts` (sum of `repSize` of dashed children). -/
def vSize (P : LctPayload α σ τ) (s : SplayState α σ τ) (active : List ℕ)
    (par : ℕ → ℕ) (ts : List AuxTree) (u : ℕ) : ℕ :=
  ((ts.filter (fun t => (s.nodes t.rootId).ppar == u)).map
    (fun t => repSize active par (listHead0 (treeIds P s t)))).sum

/-- Whether auxiliary tree `t`'s outgoing dashed edge `(topmost(t) → ppar(t.rootId))` is heavy:
`p ≠ 0` and `2 * repSize (head! (treeIds t)) > repSize p`. -/
def isHeavyEdge (P : LctPayload α σ τ) (s : SplayState α σ τ) (active : List ℕ)
    (par : ℕ → ℕ) (t : AuxTree) : Bool :=
  let p := (s.nodes t.rootId).ppar
  p != 0 && decide (2 * repSize active par (listHead0 (treeIds P s t)) > repSize active par p)

/-- Number of heavy dashed edges across auxiliary trees `ts`. -/
def heavyCountList (P : LctPayload α σ τ) (s : SplayState α σ τ) (active : List ℕ)
    (par : ℕ → ℕ) (ts : List AuxTree) : ℕ :=
  (ts.filter (isHeavyEdge P s active par)).length

/-- Sum of Sleator–Tarjan splay potentials `AuxTree.treePhi v` across `ts`. -/
def sumTreePhiList (v : ℕ → ℕ) (ts : List AuxTree) : ℕ :=
  (ts.map (AuxTree.treePhi v)).sum

/-- Canonical `heavyCount` computed deterministically from `st`. -/
def heavyCount (P : LctPayload α σ τ) (st : LctState α σ τ) : ℕ :=
  let active := canonActive st
  let ts := canonTrees st
  let par := inducedSubPar P st.splay ts
  heavyCountList P st.splay active par ts

/-- Canonical `sumTreePhi` computed deterministically from `st`. -/
def sumTreePhi (P : LctPayload α σ τ) (st : LctState α σ τ) : ℕ :=
  let active := canonActive st
  let ts := canonTrees st
  let par := inducedSubPar P st.splay ts
  let v := vSize P st.splay active par ts
  sumTreePhiList v ts

/-! ### Link-Cut Tree Invariant (`LctInvWith` and `LctInv`) -/

/-- Witnessed subdivided Link-Cut Tree invariant for `(st, trees, freeList, depth)`. -/
structure LctInvWith (P : LctPayload α σ τ) (st : LctState α σ τ)
    (trees : List AuxTree) (freeList : List ℕ) (depth : ℕ → ℕ) : Prop where
  treesNonEmpty : ∀ t ∈ trees, t ≠ .leaf
  treesInv : ∀ t ∈ trees, SplayState.TreeInv P st.splay t
  activeNodup : (trees.flatMap AuxTree.toList).Nodup
  activeValid : ∀ x ∈ trees.flatMap AuxTree.toList, isNode st.n x
  verticesActive : ∀ v < st.n, vid v ∈ trees.flatMap AuxTree.toList
  freeNodup : freeList.Nodup
  freeValid : ∀ e ∈ freeList, isEdgeSlot st.n e
  partitionSlots : ∀ e, isEdgeSlot st.n e →
    (e ∈ trees.flatMap AuxTree.toList ↔ e ∉ freeList)
  freeListInv : FreeListInv st.splay st.freeHead freeList
  pparActive : ∀ t ∈ trees, (st.splay.nodes t.rootId).ppar ≠ 0 →
    (st.splay.nodes t.rootId).ppar ∈ trees.flatMap AuxTree.toList
  acyclic : ∀ x ∈ trees.flatMap AuxTree.toList,
    inducedSubPar P st.splay trees x ≠ 0 →
      depth (inducedSubPar P st.splay trees x) < depth x
  vertexParEdge : ∀ x, isVertex st.n x →
    inducedSubPar P st.splay trees x ≠ 0 →
      isEdgeSlot st.n (inducedSubPar P st.splay trees x)
  edgeParVertex : ∀ e ∈ trees.flatMap AuxTree.toList, isEdgeSlot st.n e →
    inducedSubPar P st.splay trees e ≠ 0 ∧
      isVertex st.n (inducedSubPar P st.splay trees e)
  edgeUniqueChild : ∀ e ∈ trees.flatMap AuxTree.toList, isEdgeSlot st.n e →
    ∃! w, w ∈ trees.flatMap AuxTree.toList ∧
      inducedSubPar P st.splay trees w = e ∧
      isVertex st.n w ∧ w ≠ inducedSubPar P st.splay trees e

/-- Exists-witness Link-Cut Tree invariant on `st`. -/
def LctInv (P : LctPayload α σ τ) (st : LctState α σ τ) : Prop :=
  ∃ trees freeList depth, LctInvWith P st trees freeList depth

/-! ### Canonical tree correspondence and edge-slot availability -/

private theorem nodup_length_le_of_subset {α : Type*} [DecidableEq α] {l₁ l₂ : List α}
    (hnd : l₁.Nodup) (hsub : ∀ x ∈ l₁, x ∈ l₂) : l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a as ih =>
      rcases List.nodup_cons.mp hnd with ⟨ha_n, has_nd⟩
      have ha2 : a ∈ l₂ := hsub a (by simp)
      have hlen_erase : (l₂.erase a).length + 1 = l₂.length :=
        (List.length_erase_of_mem ha2).symm ▸ Nat.sub_add_cancel
          (List.length_pos_of_mem ha2)
      have hsub' : ∀ x ∈ as, x ∈ l₂.erase a := fun x hx => by
        have hxa : x ≠ a := fun h => ha_n (h ▸ hx)
        exact List.mem_erase_of_ne hxa |>.mpr (hsub x (by simp [hx]))
      have := ih has_nd hsub'
      simp only [List.length_cons]
      omega

private theorem range'_nodup (s len : ℕ) : (List.range' s len).Nodup := by
  induction len generalizing s with
  | zero => simp [List.range']
  | succ m ih =>
      simp only [List.range', List.nodup_cons, List.mem_range']
      refine ⟨?_, ih (s + 1)⟩
      omega

theorem flatMap_mem_unique {ts : List AuxTree} (hnd : (ts.flatMap AuxTree.toList).Nodup)
    {t₁ t₂ : AuxTree} (ht₁ : t₁ ∈ ts) (ht₂ : t₂ ∈ ts) {x : ℕ}
    (hx₁ : x ∈ t₁.toList) (hx₂ : x ∈ t₂.toList) : t₁ = t₂ := by
  induction ts with
  | nil => simp at ht₁
  | cons a rest ih =>
      simp only [List.flatMap_cons, List.nodup_append] at hnd
      rcases hnd with ⟨ha_nd, hrest_nd, hdisj⟩
      rcases List.mem_cons.mp ht₁ with rfl | ht₁' <;>
        rcases List.mem_cons.mp ht₂ with rfl | ht₂'
      · rfl
      · exact absurd (List.mem_flatMap.mpr ⟨t₂, ht₂', hx₂⟩) (fun hm => hdisj x hx₁ x hm rfl)
      · exact absurd (List.mem_flatMap.mpr ⟨t₁, ht₁', hx₁⟩) (fun hm => hdisj x hx₂ x hm rfl)
      · exact ih hrest_nd ht₁' ht₂'

theorem LctInvWith.active_of_freeList_disjoint {P : LctPayload α σ τ}
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {e : ℕ} (he : e ∈ freeList) :
    e ∉ trees.flatMap AuxTree.toList := by
  have he_slot := W.freeValid e he
  exact (W.partitionSlots e he_slot).not.mpr (not_not.mpr he)

private theorem inducedSubPar_mem_active_aux {P : LctPayload α σ τ} {s : SplayState α σ τ}
    {ts tsAll : List AuxTree}
    (hpp : ∀ t ∈ ts, (s.nodes t.rootId).ppar ≠ 0 →
      (s.nodes t.rootId).ppar ∈ tsAll.flatMap AuxTree.toList)
    (hsub : ∀ t ∈ ts, ∀ y ∈ t.toList, y ∈ tsAll.flatMap AuxTree.toList)
    {x : ℕ} (hx : x ∈ ts.flatMap AuxTree.toList)
    (hp : inducedSubPar P s ts x ≠ 0) :
    inducedSubPar P s ts x ∈ tsAll.flatMap AuxTree.toList := by
  induction ts with
  | nil => simp at hx
  | cons t rest ih =>
      simp only [List.flatMap_cons, List.mem_append] at hx
      simp only [inducedSubPar] at hp ⊢
      have hm : x ∈ treeIds P s t ↔ x ∈ t.toList := mem_treeIds_iff P s t x
      by_cases hxt : x ∈ treeIds P s t
      · simp only [hxt, ↓reduceIte] at hp ⊢
        rcases chainPred_mem_or_prev hxt with hroot | hin
        · rw [hroot] at hp ⊢
          exact hpp t (by simp) hp
        · exact hsub t (by simp) _ ((mem_treeIds_iff P s t _).mp hin)
      · simp only [hxt, ↓reduceIte] at hp ⊢
        rcases hx with hx1 | hx2
        · exact absurd (hm.mpr hx1) hxt
        · exact ih (fun a ha => hpp a (by simp [ha]))
            (fun a ha => hsub a (by simp [ha])) hx2 hp

theorem LctInvWith.subPar_mem_active {P : LctPayload α σ τ}
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {x : ℕ}
    (hx : x ∈ trees.flatMap AuxTree.toList)
    (hp : inducedSubPar P st.splay trees x ≠ 0) :
    inducedSubPar P st.splay trees x ∈ trees.flatMap AuxTree.toList :=
  inducedSubPar_mem_active_aux W.pparActive (fun t ht _ hy => List.mem_flatMap.mpr ⟨t, ht, hy⟩) hx hp

theorem inducedSubPar_eq_of_mem {P : LctPayload α σ τ} {s : SplayState α σ τ}
    {ts : List AuxTree} (hnd : (ts.flatMap AuxTree.toList).Nodup)
    {t : AuxTree} (ht : t ∈ ts) {x : ℕ} (hx : x ∈ t.toList) :
    inducedSubPar P s ts x = chainPred (s.nodes t.rootId).ppar (treeIds P s t) x := by
  induction ts with
  | nil => simp at ht
  | cons a rest ih =>
      simp only [List.flatMap_cons, List.nodup_append] at hnd
      rcases hnd with ⟨_, hrest_nd, hdisj⟩
      simp only [inducedSubPar]
      rcases List.mem_cons.mp ht with rfl | ht_rest
      · have hxt : x ∈ treeIds P s t := (mem_treeIds_iff P s t x).mpr hx
        simp [hxt]
      · have hx_rest : x ∈ rest.flatMap AuxTree.toList := List.mem_flatMap.mpr ⟨t, ht_rest, hx⟩
        have hx_na : x ∉ a.toList := fun hm => hdisj x hm x hx_rest rfl
        have hx_nids : x ∉ treeIds P s a := fun hm => hx_na ((mem_treeIds_iff P s a x).mp hm)
        simp only [hx_nids, ↓reduceIte]
        exact ih hrest_nd ht_rest

theorem inducedSubPar_eq_zero_of_not_mem {P : LctPayload α σ τ} {s : SplayState α σ τ}
    {ts : List AuxTree} {x : ℕ} (hx : x ∉ ts.flatMap AuxTree.toList) :
    inducedSubPar P s ts x = 0 := by
  induction ts with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.flatMap_cons, List.mem_append, not_or] at hx
      have hna : x ∉ treeIds P s a := fun hm => hx.1 ((mem_treeIds_iff P s a x).mp hm)
      simp [inducedSubPar, hna, ih hx.2]

theorem inducedSubPar_perm {P : LctPayload α σ τ} {s : SplayState α σ τ}
    {ts₁ ts₂ : List AuxTree} (hperm : ts₁.Perm ts₂)
    (hnd : (ts₁.flatMap AuxTree.toList).Nodup) (x : ℕ) :
    inducedSubPar P s ts₁ x = inducedSubPar P s ts₂ x := by
  have hfm : (ts₁.flatMap AuxTree.toList).Perm (ts₂.flatMap AuxTree.toList) :=
    hperm.flatMap (fun _ _ => List.Perm.refl _)
  have hnd₂ : (ts₂.flatMap AuxTree.toList).Nodup := hfm.nodup_iff.mp hnd
  by_cases hx : x ∈ ts₁.flatMap AuxTree.toList
  · obtain ⟨t, ht₁, hxt⟩ := List.mem_flatMap.mp hx
    have ht₂ : t ∈ ts₂ := hperm.mem_iff.mp ht₁
    rw [inducedSubPar_eq_of_mem hnd ht₁ hxt, inducedSubPar_eq_of_mem hnd₂ ht₂ hxt]
  · have hx₂ : x ∉ ts₂.flatMap AuxTree.toList := fun hm => hx (hfm.mem_iff.mpr hm)
    rw [inducedSubPar_eq_zero_of_not_mem hx, inducedSubPar_eq_zero_of_not_mem hx₂]

private theorem subPar_par_eq_of_mem {P : LctPayload α σ τ}
    {ts : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    {st : LctState α σ τ} (W : LctInvWith P st ts freeList depth)
    {r : ℕ} (hr : r ∈ ts.flatMap AuxTree.toList) :
    (st.splay.nodes r).par = 0 ↔ r ∈ ts.map AuxTree.rootId := by
  obtain ⟨t, ht_in, hrt⟩ := List.mem_flatMap.mp hr
  have ht_inv := W.treesInv t ht_in
  have ht_ne := W.treesNonEmpty t ht_in
  constructor
  · intro hpar0
    by_cases hrt_root : r = t.rootId
    · exact List.mem_map.mpr ⟨t, ht_in, hrt_root.symm⟩
    · have hp := SplayState.SubtreeInv_par_eq_parentIn ht_inv.nodup ht_inv.sub hrt
      rw [hpar0] at hp
      have hnz := SplayState.SubtreeInv_nonZero ht_inv.sub
        (AuxTree.parentIn_mem_and_depth (p₀ := 0) ht_inv.nodup hrt hrt_root).1
      exact absurd hp.symm hnz
  · intro hrm
    rcases List.mem_map.mp hrm with ⟨t', ht'_in, hr_eq⟩
    have ht'_root_mem : t'.rootId ∈ t'.toList := AuxTree.rootId_mem (W.treesNonEmpty t' ht'_in)
    have htt' : t = t' :=
      flatMap_mem_unique W.activeNodup ht_in ht'_in hrt (hr_eq ▸ ht'_root_mem)
    subst htt'
    cases ht_c : t with
    | leaf => exact absurd ht_c ht_ne
    | node rid l rch =>
        have hsub := ht_inv.sub
        rw [ht_c] at hsub hr_eq
        simp only [AuxTree.rootId] at hr_eq
        rw [← hr_eq]
        exact hsub.2.2.2.1

private theorem trees_map_rootId_nodup {ts : List AuxTree}
    (hne : ∀ t ∈ ts, t ≠ .leaf) (hnd : (ts.flatMap AuxTree.toList).Nodup) :
    (ts.map AuxTree.rootId).Nodup := by
  induction ts with
  | nil => simp
  | cons t rest ih =>
      simp only [List.flatMap_cons, List.nodup_append] at hnd
      simp only [List.map_cons, List.nodup_cons, List.mem_map]
      refine ⟨?_, ih (fun a ha => hne a (by simp [ha])) hnd.2.1⟩
      rintro ⟨a, ha, ha_eq⟩
      exact hnd.2.2 t.rootId (AuxTree.rootId_mem (hne t (by simp))) t.rootId
        (List.mem_flatMap.mpr ⟨a, ha, ha_eq ▸ AuxTree.rootId_mem (hne a (by simp [ha]))⟩) rfl

theorem LctInvWith_canon_perm {P : LctPayload α σ τ}
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) :
    canonFreeList st.splay st.n st.freeHead = freeList ∧
    (canonActive st).Perm (trees.flatMap AuxTree.toList) ∧
    (canonRoots st).Perm (trees.map AuxTree.rootId) ∧
    (canonTrees st).Perm trees := by
  have hfl_len : freeList.length ≤ st.n := by
    have hsub : ∀ e ∈ freeList, e ∈ List.range' (st.n + 1) (st.n - 1) := by
      intro e he
      have hes := W.freeValid e he
      rcases hes with ⟨h1, h2⟩
      exact List.mem_range'.mpr ⟨e - (st.n + 1), by omega, by omega⟩
    have hle := nodup_length_le_of_subset W.freeNodup hsub
    simp only [List.length_range'] at hle
    omega
  have hfl_eq : canonFreeList st.splay st.n st.freeHead = freeList :=
    canonFreeList_eq_of_FreeListInv W.freeListInv hfl_len
  have hact_nd : (canonActive st).Nodup := (range'_nodup _ _).filter _
  have hact_iff : ∀ x, x ∈ canonActive st ↔ x ∈ trees.flatMap AuxTree.toList := by
    intro x
    simp only [canonActive, List.mem_filter, List.mem_range', decide_eq_true_eq, hfl_eq]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hx_nfl⟩
      rcases (by simp only [isVertex, isEdgeSlot]; omega :
          isVertex st.n (1 + 1 * i) ∨ isEdgeSlot st.n (1 + 1 * i)) with hv | he
      · rcases hv with ⟨_, hxn⟩
        have hlt : 1 + 1 * i - 1 < st.n := by omega
        have hvid := W.verticesActive (1 + 1 * i - 1) hlt
        dsimp only [vid] at hvid
        rwa [show 1 + 1 * i - 1 + 1 = 1 + 1 * i by omega] at hvid
      · exact (W.partitionSlots _ he).mpr hx_nfl
    · intro hx_act
      have hnd := W.activeValid x hx_act
      rcases hnd with ⟨hx1, hx2⟩
      refine ⟨⟨x - 1, by omega, by omega⟩, fun hfl => ?_⟩
      exact W.active_of_freeList_disjoint hfl hx_act
  have hact_perm : (canonActive st).Perm (trees.flatMap AuxTree.toList) :=
    (List.perm_ext_iff_of_nodup hact_nd W.activeNodup).mpr hact_iff
  have hroots_nd_left : (canonRoots st).Nodup := hact_nd.filter _
  have hroots_nd_right : (trees.map AuxTree.rootId).Nodup :=
    trees_map_rootId_nodup W.treesNonEmpty W.activeNodup
  have hroots_iff : ∀ r, r ∈ canonRoots st ↔ r ∈ trees.map AuxTree.rootId := by
    intro r
    simp only [canonRoots, List.mem_filter, beq_iff_eq, hact_iff]
    constructor
    · rintro ⟨hr_act, hpar0⟩
      exact (subPar_par_eq_of_mem W hr_act).mp hpar0
    · intro hr_m
      have hr_act : r ∈ trees.flatMap AuxTree.toList := by
        rcases List.mem_map.mp hr_m with ⟨t, ht_in, rfl⟩
        exact List.mem_flatMap.mpr ⟨t, ht_in, AuxTree.rootId_mem (W.treesNonEmpty t ht_in)⟩
      exact ⟨hr_act, (subPar_par_eq_of_mem W hr_act).mpr hr_m⟩
  have hroots_perm : (canonRoots st).Perm (trees.map AuxTree.rootId) :=
    (List.perm_ext_iff_of_nodup hroots_nd_left hroots_nd_right).mpr hroots_iff
  have hact_len : (trees.flatMap AuxTree.toList).length ≤ 2 * st.n := by
    have hsub : ∀ x ∈ trees.flatMap AuxTree.toList, x ∈ List.range' 1 (2 * st.n - 1) := by
      intro x hx
      rcases W.activeValid x hx with ⟨hx1, hx2⟩
      exact List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩
    have hle := nodup_length_le_of_subset W.activeNodup hsub
    simp only [List.length_range'] at hle
    omega
  have hbuild_eq : (trees.map AuxTree.rootId).map (buildAuxTree st.splay (2 * st.n)) = trees := by
    rw [List.map_map]
    have hmap : trees.map (fun t => buildAuxTree st.splay (2 * st.n) t.rootId) = trees.map id := by
      refine List.map_congr_left ?_
      intro t ht
      have ht_inv := W.treesInv t ht
      have hcnt : t.countNodes ≤ 2 * st.n := by
        have hle : t.toList.length ≤ (trees.flatMap AuxTree.toList).length := by
          have hsub : ∀ x ∈ t.toList, x ∈ trees.flatMap AuxTree.toList := fun x hx =>
            List.mem_flatMap.mpr ⟨t, ht, hx⟩
          exact nodup_length_le_of_subset ht_inv.nodup hsub
        rw [AuxTree.length_toList] at hle
        omega
      exact buildAuxTree_eq ht_inv.sub hcnt
    have hmap' : trees.map (fun t => buildAuxTree st.splay (2 * st.n) t.rootId) = trees := by
      simpa using hmap
    exact hmap'
  have htrees_perm : (canonTrees st).Perm trees := by
    dsimp only [canonTrees]
    rw [← hbuild_eq]
    exact hroots_perm.map _
  exact ⟨hfl_eq, hact_perm, hroots_perm, htrees_perm⟩

theorem LctInvWith_canon_potentials {P : LctPayload α σ τ}
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) :
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    let v := vSize P st.splay active par trees
    heavyCount P st = heavyCountList P st.splay active par trees ∧
    sumTreePhi P st = sumTreePhiList v trees := by
  rcases LctInvWith_canon_perm W with ⟨_, hact_perm, _, htrees_perm⟩
  have hfm : ((canonTrees st).flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList) :=
    htrees_perm.flatMap (fun _ _ => List.Perm.refl _)
  have hpar : inducedSubPar P st.splay (canonTrees st) = inducedSubPar P st.splay trees := by
    funext x
    exact inducedSubPar_perm htrees_perm (hfm.nodup_iff.mpr W.activeNodup) x
  have hrep : ∀ u, repSize (canonActive st) (inducedSubPar P st.splay (canonTrees st)) u =
      repSize (trees.flatMap AuxTree.toList) (inducedSubPar P st.splay trees) u := by
    intro u
    simp only [repSize, hpar, hact_perm.length_eq]
    exact (hact_perm.filter _).length_eq
  have hv : vSize P st.splay (canonActive st) (inducedSubPar P st.splay (canonTrees st))
      (canonTrees st) =
      vSize P st.splay (trees.flatMap AuxTree.toList) (inducedSubPar P st.splay trees) trees := by
    funext u
    simp only [vSize]
    have hmap : ((canonTrees st).filter (fun t => (st.splay.nodes t.rootId).ppar == u)).map
        (fun t => repSize (canonActive st) (inducedSubPar P st.splay (canonTrees st))
          (listHead0 (treeIds P st.splay t))) =
        ((canonTrees st).filter (fun t => (st.splay.nodes t.rootId).ppar == u)).map
          (fun t => repSize (trees.flatMap AuxTree.toList) (inducedSubPar P st.splay trees)
            (listHead0 (treeIds P st.splay t))) :=
      List.map_congr_left (fun t _ => hrep _)
    rw [hmap]
    exact ((htrees_perm.filter _).map _).sum_eq
  have hheavy_f : isHeavyEdge P st.splay (canonActive st) (inducedSubPar P st.splay (canonTrees st)) =
      isHeavyEdge P st.splay (trees.flatMap AuxTree.toList) (inducedSubPar P st.splay trees) := by
    funext t
    simp only [isHeavyEdge, hrep]
  refine ⟨?_, ?_⟩
  · dsimp only [heavyCount, heavyCountList]
    rw [hheavy_f]
    exact (htrees_perm.filter _).length_eq
  · dsimp only [sumTreePhi, sumTreePhiList]
    rw [hv]
    exact (htrees_perm.map _).sum_eq

/-! ### Component roots (`subRoot`) and free-slot availability -/

private theorem subRoot_prop_aux {par : ℕ → ℕ} {active : List ℕ} {depth : ℕ → ℕ}
    (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x) :
    ∀ k x, x ∈ active →
      subRoot par k x ∈ active ∧
      (depth x ≤ k → par (subRoot par k x) = 0) := by
  intro k
  induction k with
  | zero =>
      intro x hx
      refine ⟨hx, fun hd => ?_⟩
      by_cases hp : par x = 0
      · exact hp
      · have := hdec x hx hp; omega
  | succ k ih =>
      intro x hx
      simp only [subRoot]
      by_cases hp : par x = 0
      · simp [hp, hx]
      · simp only [hp, ↓reduceIte]
        rcases ih (par x) (hmem x hx hp) with ⟨hm, h0⟩
        refine ⟨hm, fun hd => h0 ?_⟩
        have := hdec x hx hp
        omega

private theorem depth_subRoot_le {par : ℕ → ℕ} {active : List ℕ} {depth : ℕ → ℕ}
    (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x) :
    ∀ k x, x ∈ active → depth (subRoot par k x) ≤ depth x := by
  intro k
  induction k with
  | zero => intro x _; simp [subRoot]
  | succ k ih =>
      intro x hx
      by_cases hx0 : par x = 0
      · simp [subRoot, hx0]
      · simp only [subRoot, hx0, ↓reduceIte]
        have := ih (par x) (hmem x hx hx0)
        have := hdec x hx hx0
        omega

/-- Under `LctInvWith`, walking `par` up from any active node `x` for `k ≥ active.length`
steps always reaches a component root with `par = 0`. -/
private theorem walkUp_eq_of_nodup {par : ℕ → ℕ} {active : List ℕ} {depth : ℕ → ℕ}
    (_hnd : active.Nodup)
    (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x) :
    ∀ {k x}, x ∈ active → active.length ≤ k →
      par (subRoot par k x) = 0 := by
  -- Define explicit prefix list of visited nodes up to `k` and note strict depth decrease => Nodup.
  suffices h : ∀ (m : ℕ) (x : ℕ), x ∈ active →
      par (subRoot par m x) ≠ 0 →
      ∃ vis : List ℕ, vis.Nodup ∧
        (∀ y ∈ vis, y ∈ active ∧ depth y ≤ depth x ∧ depth (par (subRoot par m x)) < depth y) ∧
        vis.length = m + 1 by
    intro k x hx hk
    by_contra hp
    rcases h k x hx hp with ⟨vis, hvis_nd, hvis_sub, hvis_len⟩
    have hle := nodup_length_le_of_subset hvis_nd (fun y hy => (hvis_sub y hy).1)
    omega
  intro m
  induction m with
  | zero =>
      intro x hx hp
      refine ⟨[x], List.nodup_singleton x, ?_, by simp⟩
      intro y hy
      rw [List.mem_singleton.mp hy]
      exact ⟨hx, le_rfl, hdec x hx hp⟩
  | succ m ih =>
      intro x hx hp
      by_cases hx0 : par x = 0
      · simp [subRoot, hx0] at hp
      · have hsub_eq : subRoot par (m + 1) x = subRoot par m (par x) := by
          simp [subRoot, hx0]
        have hp' : par (subRoot par m (par x)) ≠ 0 := hsub_eq ▸ hp
        rcases ih (par x) (hmem x hx hx0) hp' with ⟨vis, hvis_nd, hvis_sub, hvis_len⟩
        have hpx_lt : depth (par x) < depth x := hdec x hx hx0
        have hx_nvis : x ∉ vis := fun hxm => by
          have := (hvis_sub x hxm).2.1
          omega
        refine ⟨x :: vis, List.nodup_cons.mpr ⟨hx_nvis, hvis_nd⟩, ?_, by simp [hvis_len]⟩
        intro y hy
        rcases List.mem_cons.mp hy with hyx | hy'
        · rw [hyx]
          have hdr2 := hdec _ (subRoot_prop_aux hmem hdec m (par x) (hmem x hx hx0)).1 hp'
          have hdr_le := depth_subRoot_le hmem hdec m (par x) (hmem x hx hx0)
          rw [hsub_eq]
          exact ⟨hx, le_rfl, by omega⟩
        · have hy_info := hvis_sub y hy'
          rw [hsub_eq]
          exact ⟨hy_info.1, by omega, hy_info.2.2⟩

theorem LctInvWith.subRoot_isRoot {P : LctPayload α σ τ}
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {x : ℕ}
    (hx : x ∈ trees.flatMap AuxTree.toList) :
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    let r := subRoot par active.length x
    r ∈ active ∧ par r = 0 ∧ isVertex st.n r := by
  intro active par r
  have hr_act : r ∈ active :=
    (subRoot_prop_aux (fun y hy hp => W.subPar_mem_active hy hp) W.acyclic active.length x hx).1
  have hr_par : par r = 0 :=
    walkUp_eq_of_nodup W.activeNodup (fun y hy hp => W.subPar_mem_active hy hp) W.acyclic hx le_rfl
  have hr_node := W.activeValid r hr_act
  have hr_vtx : isVertex st.n r := by
    rcases isNode_iff_vertex_or_edge.mp hr_node with hv | he
    · exact hv
    · exact absurd hr_par (W.edgeParVertex r hr_act he).1
  exact ⟨hr_act, hr_par, hr_vtx⟩

/-- If two vertices have distinct component roots under `inducedSubPar`, then the free list is
nonempty (`freeHead ≠ 0`), so allocating a fresh edge slot for `link` always succeeds! -/
theorem LctInvWith.freeHead_ne_zero_of_two_roots {P : LctPayload α σ τ}
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {u v : ℕ} (hu : u < st.n) (hv : v < st.n)
    (hdiff : subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length (vid u) ≠
      subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length (vid v)) :
    freeList ≠ [] ∧ st.freeHead ≠ 0 := by
  let active := trees.flatMap AuxTree.toList
  let par := inducedSubPar P st.splay trees
  have hru := W.subRoot_isRoot (W.verticesActive u hu)
  have hrv := W.subRoot_isRoot (W.verticesActive v hv)
  let ru := subRoot par active.length (vid u)
  let rv := subRoot par active.length (vid v)
  have hru_rng : ru ∈ List.range' 1 st.n := by
    rcases hru.2.2 with ⟨h1, h2⟩
    refine List.mem_range'.mpr ⟨ru - 1, ?_, ?_⟩ <;> dsimp only [ru, par, active] <;> omega
  have hrv_rng : rv ∈ List.range' 1 st.n := by
    rcases hrv.2.2 with ⟨h1, h2⟩
    refine List.mem_range'.mpr ⟨rv - 1, ?_, ?_⟩ <;> dsimp only [rv, par, active] <;> omega
  let nonRootVerts := (List.range' 1 st.n).filter (fun w => par w != 0)
  have hnr_sub : ∀ w ∈ nonRootVerts, w ∈ ((List.range' 1 st.n).erase ru).erase rv := by
    intro w hw
    simp only [nonRootVerts, List.mem_filter, bne_iff_ne] at hw
    have hw_ne_ru : w ≠ ru := fun h => hw.2 (h ▸ hru.2.1)
    have hw_ne_rv : w ≠ rv := fun h => hw.2 (h ▸ hrv.2.1)
    exact (List.mem_erase_of_ne hw_ne_rv).mpr
      ((List.mem_erase_of_ne hw_ne_ru).mpr hw.1)
  have hnr_len : nonRootVerts.length ≤ st.n - 2 := by
    have hle := nodup_length_le_of_subset ((range'_nodup 1 st.n).filter _) hnr_sub
    have hlen1 : ((List.range' 1 st.n).erase ru).length = st.n - 1 := by
      have := List.length_erase_of_mem hru_rng
      simp only [List.length_range'] at this
      exact this
    have hrv_er : rv ∈ (List.range' 1 st.n).erase ru :=
      (List.mem_erase_of_ne (Ne.symm hdiff)).mpr hrv_rng
    have hlen2 : (((List.range' 1 st.n).erase ru).erase rv).length = st.n - 2 := by
      have := List.length_erase_of_mem hrv_er
      rw [hlen1] at this
      omega
    dsimp only [nonRootVerts] at hle ⊢
    omega
  let activeEdges := active.filter (fun x => st.n + 1 ≤ x)
  have hae_sub : ∀ e ∈ activeEdges, e ∈ nonRootVerts.map par := by
    intro e he
    simp only [activeEdges, List.mem_filter, decide_eq_true_eq] at he
    have he_slot : isEdgeSlot st.n e := by
      have hn := W.activeValid e he.1
      simp only [isNode, isEdgeSlot] at hn ⊢
      omega
    rcases (W.edgeUniqueChild e he.1 he_slot).exists with ⟨w, _, hw_par, hw_vtx, _⟩
    refine List.mem_map.mpr ⟨w, ?_, hw_par⟩
    simp only [nonRootVerts, List.mem_filter, bne_iff_ne]
    rcases hw_vtx with ⟨h1, h2⟩
    rcases he_slot with ⟨h3, h4⟩
    refine ⟨List.mem_range'.mpr ⟨w - 1, by omega, by omega⟩, ?_⟩
    change inducedSubPar P st.splay trees w ≠ 0
    rw [hw_par]; omega
  have hae_len : activeEdges.length ≤ st.n - 2 := by
    have hle := nodup_length_le_of_subset (W.activeNodup.filter _) hae_sub
    rw [List.length_map] at hle
    dsimp only [activeEdges, active] at hle ⊢
    omega
  have hslots_sub : ∀ e ∈ List.range' (st.n + 1) (st.n - 1), e ∈ activeEdges ++ freeList := by
    intro e he
    rcases List.mem_range'.mp he with ⟨i, hi, rfl⟩
    have he_slot : isEdgeSlot st.n (st.n + 1 + 1 * i) := by simp only [isEdgeSlot]; omega
    by_cases hfl : (st.n + 1 + 1 * i) ∈ freeList
    · exact List.mem_append_right _ hfl
    · refine List.mem_append_left _ ?_
      simp only [activeEdges, List.mem_filter, decide_eq_true_eq]
      exact ⟨(W.partitionSlots _ he_slot).mpr hfl, by omega⟩
  have hfl_pos : 1 ≤ freeList.length := by
    have hle := nodup_length_le_of_subset (range'_nodup (st.n + 1) (st.n - 1)) hslots_sub
    simp only [List.length_range', List.length_append] at hle
    have hru1 := hru.2.2
    have hrv1 := hrv.2.2
    have hne : ru ≠ rv := hdiff
    have hn2 : 2 ≤ st.n := by rcases hru1 with ⟨_, h1⟩; rcases hrv1 with ⟨_, h2⟩; omega
    omega
  have hfl_ne : freeList ≠ [] := by
    intro h; rw [h] at hfl_pos; simp at hfl_pos
  have hhead_nz : st.freeHead ≠ 0 := by
    cases hfl_c : freeList with
    | nil => exact absurd hfl_c hfl_ne
    | cons e rest =>
        have hfl_inv := W.freeListInv
        rw [hfl_c] at hfl_inv
        simp only [FreeListInv] at hfl_inv
        exact hfl_inv.1
  exact ⟨hfl_ne, hhead_nz⟩

end MinCostFlow.LinkCut


