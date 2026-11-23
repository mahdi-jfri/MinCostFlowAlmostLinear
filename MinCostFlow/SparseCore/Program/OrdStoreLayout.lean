module

public import MinCostFlow.SparseCore.Program.OrdStoreInv
public import WordRAM.Layout
import Mathlib.Tactic

/-!
# Memory layout of the order store

This file fixes the fixed-size arena layout at handle `b` for an order store with capacities
`vCap` and `eCap`:

* Header (8 words at `b + 0 .. b + 7`): `vCap`, `eCap`, `vRootBase`, `eNodeBase`, `nodesBase`,
  `nextNode`, `freeHead`, and one unused word.
* Vertex root table (`vCap` words at `b + 8 ..`): `vRoot[v]` is the root node ID of vertex `v`'s
  splay tree (`0` if empty).
* End-key node table (`2 * eCap` words at `b + 8 + vCap ..`): `eNode[k]` is the live node ID
  holding end key `k` (`0` if absent).
* Node pool (`(2 * eCap + 1) * 8` words at `nodesBase ..`): 8-word records for node IDs
  `0 .. 2 * eCap`, with offsets `0: left`, `1: right`, `2: par`, `3: ppar`, `4: sz`, `5: key`,
  `6: mark`, `7: nextFree`.

Total size is `ordArenaSize vCap eCap = 16 + vCap + 18 * eCap`. The footprint `ordFoot b vCap eCap`
is fixed at initialization and never grows.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.LinkCut

/-! ### Offsets and addresses -/

def ORD_HDR_VCAP : ℕ := 0
def ORD_HDR_ECAP : ℕ := 1
def ORD_HDR_VROOT : ℕ := 2
def ORD_HDR_ENODE : ℕ := 3
def ORD_HDR_NODES : ℕ := 4
def ORD_HDR_NEXT : ℕ := 5
def ORD_HDR_FREE : ℕ := 6
def ORD_HDR_SIZE : ℕ := 8

def ORD_ND_LEFT : ℕ := 0
def ORD_ND_RIGHT : ℕ := 1
def ORD_ND_PAR : ℕ := 2
def ORD_ND_PPAR : ℕ := 3
def ORD_ND_SZ : ℕ := 4
def ORD_ND_KEY : ℕ := 5
def ORD_ND_MARK : ℕ := 6
def ORD_ND_NFREE : ℕ := 7
def ORD_ND_STRIDE : ℕ := 8

def ordVRootBase (b : ℕ) : ℕ := b + 8
def ordENodeBase (b vCap : ℕ) : ℕ := b + 8 + vCap
def ordNodesBase (b vCap eCap : ℕ) : ℕ := b + 8 + vCap + 2 * eCap
def ordNodeAddr (nb x : ℕ) : ℕ := nb + 8 * x

/-- Total words of the fixed-size order-store arena. -/
def ordArenaSize (vCap eCap : ℕ) : ℕ := 16 + vCap + 18 * eCap

/-- The cells belonging to the order store at handle `b`. -/
def ordFoot (b vCap eCap a : ℕ) : Prop := b ≤ a ∧ a < b + ordArenaSize vCap eCap

theorem ordNodesBase_end (b vCap eCap : ℕ) :
    ordNodesBase b vCap eCap + (2 * eCap + 1) * 8 = b + ordArenaSize vCap eCap := by
  unfold ordNodesBase ordArenaSize; omega

theorem ordFoot_hdr {b vCap eCap i : ℕ} (hi : i < 8) :
    ordFoot b vCap eCap (b + i) := by
  unfold ordFoot ordArenaSize; omega

theorem ordFoot_vRoot {b vCap eCap v : ℕ} (hv : v < vCap) :
    ordFoot b vCap eCap (ordVRootBase b + v) := by
  unfold ordFoot ordVRootBase ordArenaSize; omega

theorem ordFoot_eNode {b vCap eCap k : ℕ} (hk : k < 2 * eCap) :
    ordFoot b vCap eCap (ordENodeBase b vCap + k) := by
  unfold ordFoot ordENodeBase ordArenaSize; omega

theorem ordFoot_node {b vCap eCap x i : ℕ} (hx : x ≤ 2 * eCap) (hi : i < 8) :
    ordFoot b vCap eCap (ordNodeAddr (ordNodesBase b vCap eCap) x + i) := by
  unfold ordFoot ordNodeAddr ordNodesBase ordArenaSize; omega

theorem ordNodeAddr_disjoint {nb x y i j : ℕ} (hi : i < 8) (hj : j < 8)
    (h : ordNodeAddr nb x + i = ordNodeAddr nb y + j) : x = y ∧ i = j := by
  unfold ordNodeAddr at h; omega

/-! ### Memory representation predicate -/

/-- Node record `x` at `nb` holds `nd`, has mark `0`, and has nextFree `nf`. -/
def OrdNodeAt (mem : ℕ → ℕ) (nb x : ℕ) (nd : SplayNode ℕ Unit Unit) (nf : ℕ) : Prop :=
  mem (ordNodeAddr nb x + 0) = nd.left ∧
  mem (ordNodeAddr nb x + 1) = nd.right ∧
  mem (ordNodeAddr nb x + 2) = nd.par ∧
  mem (ordNodeAddr nb x + 3) = nd.ppar ∧
  mem (ordNodeAddr nb x + 4) = nd.sz ∧
  mem (ordNodeAddr nb x + 5) = nd.val ∧
  mem (ordNodeAddr nb x + 6) = 0 ∧
  mem (ordNodeAddr nb x + 7) = nf

/-- Full arena representation of `S` at handle `b`. -/
structure OrdArenaAt (b : ℕ) (S : OrdStoreState) (mem : ℕ → ℕ) : Prop where
  hdr_vCap : mem (b + 0) = S.vCap
  hdr_eCap : mem (b + 1) = S.eCap
  hdr_vRoot : mem (b + 2) = ordVRootBase b
  hdr_eNode : mem (b + 3) = ordENodeBase b S.vCap
  hdr_nodes : mem (b + 4) = ordNodesBase b S.vCap S.eCap
  hdr_next : mem (b + 5) = S.nextNode
  hdr_free : mem (b + 6) = S.freeHead
  vRoot_at : ∀ v < S.vCap, mem (ordVRootBase b + v) = S.vRoot v
  eNode_at : ∀ k < 2 * S.eCap, mem (ordENodeBase b S.vCap + k) = S.eNode k
  nodes_at : ∀ x ≤ S.nextNode,
    OrdNodeAt mem (ordNodesBase b S.vCap S.eCap) x (S.splay.nodes x) (S.nextFree x)

/-- Frame preserved by internal operations: memory from `heap` on is zero, and cells below `heap`
outside the arena are unchanged. -/
def OrdFrame (b vCap eCap heap : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  ZeroFrom mem' heap ∧ ∀ a < heap, ¬ ordFoot b vCap eCap a → mem' a = mem a

theorem OrdFrame.refl {b vCap eCap heap : ℕ} {mem : ℕ → ℕ} (hz : ZeroFrom mem heap) :
    OrdFrame b vCap eCap heap mem mem :=
  ⟨hz, fun _ _ _ => rfl⟩

theorem OrdFrame.trans {b vCap eCap heap : ℕ} {m₁ m₂ m₃ : ℕ → ℕ}
    (h₁ : OrdFrame b vCap eCap heap m₁ m₂) (h₂ : OrdFrame b vCap eCap heap m₂ m₃) :
    OrdFrame b vCap eCap heap m₁ m₃ :=
  ⟨h₂.1, fun a ha hf => (h₂.2 a ha hf).trans (h₁.2 a ha hf)⟩

theorem OrdFrame.of_store_in_foot {b vCap eCap heap addr val : ℕ} {mem : ℕ → ℕ}
    (hz : ZeroFrom mem heap) (hfoot : ordFoot b vCap eCap addr)
    (hle : b + ordArenaSize vCap eCap ≤ heap) :
    OrdFrame b vCap eCap heap mem (Function.update mem addr val) := by
  refine ⟨fun a ha => ?_, fun a _ hnf => Function.update_of_ne ?_ _ _⟩
  · rw [Function.update_of_ne (by unfold ordFoot at hfoot; omega)]
    exact hz a ha
  · rintro rfl; exact hnf hfoot

theorem OrdNodeAt.congr {mem mem' : ℕ → ℕ} {nb x nf : ℕ} {nd : SplayNode ℕ Unit Unit}
    (h : OrdNodeAt mem nb x nd nf)
    (hag : ∀ i < 8, mem' (ordNodeAddr nb x + i) = mem (ordNodeAddr nb x + i)) :
    OrdNodeAt mem' nb x nd nf := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨(hag 0 (by decide)).trans h0, (hag 1 (by decide)).trans h1,
    (hag 2 (by decide)).trans h2, (hag 3 (by decide)).trans h3,
    (hag 4 (by decide)).trans h4, (hag 5 (by decide)).trans h5,
    (hag 6 (by decide)).trans h6, (hag 7 (by decide)).trans h7⟩

theorem OrdArenaAt.congr {b : ℕ} {S : OrdStoreState} {mem mem' : ℕ → ℕ}
    (h : OrdArenaAt b S mem) (hnext : S.nextNode ≤ 2 * S.eCap)
    (hag : ∀ a, ordFoot b S.vCap S.eCap a → mem' a = mem a) :
    OrdArenaAt b S mem' where
  hdr_vCap := (hag _ (ordFoot_hdr (by decide))).trans h.hdr_vCap
  hdr_eCap := (hag _ (ordFoot_hdr (by decide))).trans h.hdr_eCap
  hdr_vRoot := (hag _ (ordFoot_hdr (by decide))).trans h.hdr_vRoot
  hdr_eNode := (hag _ (ordFoot_hdr (by decide))).trans h.hdr_eNode
  hdr_nodes := (hag _ (ordFoot_hdr (by decide))).trans h.hdr_nodes
  hdr_next := (hag _ (ordFoot_hdr (by decide))).trans h.hdr_next
  hdr_free := (hag _ (ordFoot_hdr (by decide))).trans h.hdr_free
  vRoot_at v hv := (hag _ (ordFoot_vRoot hv)).trans (h.vRoot_at v hv)
  eNode_at k hk := (hag _ (ordFoot_eNode hk)).trans (h.eNode_at k hk)
  nodes_at x hx := (h.nodes_at x hx).congr fun i hi =>
    hag _ (ordFoot_node (le_trans hx hnext) hi)

/-! ### Single-cell update lemmas for `OrdArenaAt` -/

theorem OrdArenaAt.setVRoot {b v r : ℕ} {S : OrdStoreState} {mem : ℕ → ℕ}
    (h : OrdArenaAt b S mem) (hv : v < S.vCap) :
    OrdArenaAt b { S with vRoot := Function.update S.vRoot v r }
      (Function.update mem (ordVRootBase b + v) r) := by
  have hne_hdr : ∀ i < 8, b + i ≠ ordVRootBase b + v := fun i hi => by
    unfold ordVRootBase; omega
  have hne_eNode : ∀ k < 2 * S.eCap, ordENodeBase b S.vCap + k ≠ ordVRootBase b + v :=
    fun k _ => by unfold ordENodeBase ordVRootBase; omega
  have hne_nd : ∀ x i, ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + i ≠ ordVRootBase b + v :=
    fun x i => by unfold ordNodeAddr ordNodesBase ordVRootBase; omega
  refine
    { hdr_vCap := by rw [Function.update_of_ne (hne_hdr 0 (by decide))]; exact h.hdr_vCap
      hdr_eCap := by rw [Function.update_of_ne (hne_hdr 1 (by decide))]; exact h.hdr_eCap
      hdr_vRoot := by rw [Function.update_of_ne (hne_hdr 2 (by decide))]; exact h.hdr_vRoot
      hdr_eNode := by rw [Function.update_of_ne (hne_hdr 3 (by decide))]; exact h.hdr_eNode
      hdr_nodes := by rw [Function.update_of_ne (hne_hdr 4 (by decide))]; exact h.hdr_nodes
      hdr_next := by rw [Function.update_of_ne (hne_hdr 5 (by decide))]; exact h.hdr_next
      hdr_free := by rw [Function.update_of_ne (hne_hdr 6 (by decide))]; exact h.hdr_free
      vRoot_at := fun u hu => by
        dsimp only at hu ⊢
        by_cases huv : u = v
        · subst huv; simp
        · rw [Function.update_of_ne (by omega), Function.update_of_ne huv]; exact h.vRoot_at u hu
      eNode_at := fun k hk => by
        rw [Function.update_of_ne (hne_eNode k hk)]; exact h.eNode_at k hk
      nodes_at := fun x hx => (h.nodes_at x hx).congr fun i _ =>
        Function.update_of_ne (hne_nd x i) _ _ }

theorem OrdArenaAt.setENode {b k u : ℕ} {S : OrdStoreState} {mem : ℕ → ℕ}
    (h : OrdArenaAt b S mem) (hk : k < 2 * S.eCap) :
    OrdArenaAt b { S with eNode := Function.update S.eNode k u }
      (Function.update mem (ordENodeBase b S.vCap + k) u) := by
  have hne_hdr : ∀ i < 8, b + i ≠ ordENodeBase b S.vCap + k := fun i hi => by
    unfold ordENodeBase; omega
  have hne_vRoot : ∀ v < S.vCap, ordVRootBase b + v ≠ ordENodeBase b S.vCap + k :=
    fun v hv => by unfold ordVRootBase ordENodeBase; omega
  have hne_nd : ∀ x i, ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + i ≠ ordENodeBase b S.vCap + k :=
    fun x i => by unfold ordNodeAddr ordNodesBase ordENodeBase; omega
  refine
    { hdr_vCap := by rw [Function.update_of_ne (hne_hdr 0 (by decide))]; exact h.hdr_vCap
      hdr_eCap := by rw [Function.update_of_ne (hne_hdr 1 (by decide))]; exact h.hdr_eCap
      hdr_vRoot := by rw [Function.update_of_ne (hne_hdr 2 (by decide))]; exact h.hdr_vRoot
      hdr_eNode := by rw [Function.update_of_ne (hne_hdr 3 (by decide))]; exact h.hdr_eNode
      hdr_nodes := by rw [Function.update_of_ne (hne_hdr 4 (by decide))]; exact h.hdr_nodes
      hdr_next := by rw [Function.update_of_ne (hne_hdr 5 (by decide))]; exact h.hdr_next
      hdr_free := by rw [Function.update_of_ne (hne_hdr 6 (by decide))]; exact h.hdr_free
      vRoot_at := fun v hv => by
        rw [Function.update_of_ne (hne_vRoot v hv)]; exact h.vRoot_at v hv
      eNode_at := fun j hj => by
        dsimp only at hj ⊢
        by_cases hjk : j = k
        · subst hjk; simp
        · rw [Function.update_of_ne (by omega), Function.update_of_ne hjk]; exact h.eNode_at j hj
      nodes_at := fun x hx => (h.nodes_at x hx).congr fun i _ =>
        Function.update_of_ne (hne_nd x i) _ _ }

theorem OrdArenaAt.setFreeHead {b fh : ℕ} {S : OrdStoreState} {mem : ℕ → ℕ}
    (h : OrdArenaAt b S mem) :
    OrdArenaAt b { S with freeHead := fh } (Function.update mem (b + 6) fh) := by
  have hne_vRoot : ∀ v < S.vCap, ordVRootBase b + v ≠ b + 6 := fun v _ => by unfold ordVRootBase; omega
  have hne_eNode : ∀ k < 2 * S.eCap, ordENodeBase b S.vCap + k ≠ b + 6 := fun k _ => by unfold ordENodeBase; omega
  have hne_nd : ∀ x i, ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + i ≠ b + 6 := fun x i => by
    unfold ordNodeAddr ordNodesBase; omega
  refine
    { hdr_vCap := by rw [Function.update_of_ne (by omega)]; exact h.hdr_vCap
      hdr_eCap := by rw [Function.update_of_ne (by omega)]; exact h.hdr_eCap
      hdr_vRoot := by rw [Function.update_of_ne (by omega)]; exact h.hdr_vRoot
      hdr_eNode := by rw [Function.update_of_ne (by omega)]; exact h.hdr_eNode
      hdr_nodes := by rw [Function.update_of_ne (by omega)]; exact h.hdr_nodes
      hdr_next := by rw [Function.update_of_ne (by omega)]; exact h.hdr_next
      hdr_free := by simp
      vRoot_at := fun v hv => by rw [Function.update_of_ne (hne_vRoot v hv)]; exact h.vRoot_at v hv
      eNode_at := fun k hk => by rw [Function.update_of_ne (hne_eNode k hk)]; exact h.eNode_at k hk
      nodes_at := fun x hx => (h.nodes_at x hx).congr fun i _ =>
        Function.update_of_ne (hne_nd x i) _ _ }

theorem OrdArenaAt.updateNodeField {b x off val : ℕ} {S : OrdStoreState} {mem : ℕ → ℕ}
    {f : SplayNode ℕ Unit Unit → SplayNode ℕ Unit Unit} {nf' : ℕ → ℕ}
    (h : OrdArenaAt b S mem) (hx : x ≤ S.nextNode) (hoff : off < 8)
    (hnd_x : OrdNodeAt (Function.update mem (ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + off) val)
      (ordNodesBase b S.vCap S.eCap) x (f (S.splay.nodes x)) (nf' x))
    (hnf_oth : ∀ y ≤ S.nextNode, y ≠ x → nf' y = S.nextFree y) :
    OrdArenaAt b { S with splay := S.splay.updateNode x f, nextFree := nf' }
      (Function.update mem (ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + off) val) := by
  have hne_hdr : ∀ i < 8, b + i ≠ ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + off :=
    fun i hi => by unfold ordNodeAddr ordNodesBase; omega
  have hne_vRoot : ∀ v < S.vCap, ordVRootBase b + v ≠ ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + off :=
    fun v hv => by unfold ordVRootBase ordNodeAddr ordNodesBase; omega
  have hne_eNode : ∀ k < 2 * S.eCap, ordENodeBase b S.vCap + k ≠ ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + off :=
    fun k hk => by unfold ordENodeBase ordNodeAddr ordNodesBase; omega
  refine
    { hdr_vCap := by rw [Function.update_of_ne (hne_hdr 0 (by decide))]; exact h.hdr_vCap
      hdr_eCap := by rw [Function.update_of_ne (hne_hdr 1 (by decide))]; exact h.hdr_eCap
      hdr_vRoot := by rw [Function.update_of_ne (hne_hdr 2 (by decide))]; exact h.hdr_vRoot
      hdr_eNode := by rw [Function.update_of_ne (hne_hdr 3 (by decide))]; exact h.hdr_eNode
      hdr_nodes := by rw [Function.update_of_ne (hne_hdr 4 (by decide))]; exact h.hdr_nodes
      hdr_next := by rw [Function.update_of_ne (hne_hdr 5 (by decide))]; exact h.hdr_next
      hdr_free := by rw [Function.update_of_ne (hne_hdr 6 (by decide))]; exact h.hdr_free
      vRoot_at := fun v hv => by rw [Function.update_of_ne (hne_vRoot v hv)]; exact h.vRoot_at v hv
      eNode_at := fun k hk => by rw [Function.update_of_ne (hne_eNode k hk)]; exact h.eNode_at k hk
      nodes_at := fun y hy => by
        dsimp only at hy ⊢
        by_cases hyx : y = x
        · subst hyx; simpa using hnd_x
        · rw [SplayState.nodes_updateNode_ne _ hyx, hnf_oth y hy hyx]
          exact (h.nodes_at y hy).congr fun i hi => Function.update_of_ne (fun heq =>
            hyx (ordNodeAddr_disjoint hi hoff heq).1) _ _ }

theorem OrdArenaAt.setLeft {b x v : ℕ} {S : OrdStoreState} {mem : ℕ → ℕ}
    (h : OrdArenaAt b S mem) (hx : x ≤ S.nextNode) :
    OrdArenaAt b { S with splay := S.splay.setLeft x v }
      (Function.update mem (ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + 0) v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h.nodes_at x hx
  refine h.updateNodeField hx (by decide) ?_ (fun _ _ _ => rfl)
  refine ⟨by simp, by rw [Function.update_of_ne (by omega)]; exact h1,
    by rw [Function.update_of_ne (by omega)]; exact h2,
    by rw [Function.update_of_ne (by omega)]; exact h3,
    by rw [Function.update_of_ne (by omega)]; exact h4,
    by rw [Function.update_of_ne (by omega)]; exact h5,
    by rw [Function.update_of_ne (by omega)]; exact h6,
    by rw [Function.update_of_ne (by omega)]; exact h7⟩

theorem OrdArenaAt.setRight {b x v : ℕ} {S : OrdStoreState} {mem : ℕ → ℕ}
    (h : OrdArenaAt b S mem) (hx : x ≤ S.nextNode) :
    OrdArenaAt b { S with splay := S.splay.setRight x v }
      (Function.update mem (ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + 1) v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h.nodes_at x hx
  refine h.updateNodeField hx (by decide) ?_ (fun _ _ _ => rfl)
  refine ⟨by rw [Function.update_of_ne (by omega)]; exact h0, by simp,
    by rw [Function.update_of_ne (by omega)]; exact h2,
    by rw [Function.update_of_ne (by omega)]; exact h3,
    by rw [Function.update_of_ne (by omega)]; exact h4,
    by rw [Function.update_of_ne (by omega)]; exact h5,
    by rw [Function.update_of_ne (by omega)]; exact h6,
    by rw [Function.update_of_ne (by omega)]; exact h7⟩

theorem OrdArenaAt.setPar {b x v : ℕ} {S : OrdStoreState} {mem : ℕ → ℕ}
    (h : OrdArenaAt b S mem) (hx : x ≤ S.nextNode) :
    OrdArenaAt b { S with splay := S.splay.setPar x v }
      (Function.update mem (ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + 2) v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h.nodes_at x hx
  refine h.updateNodeField hx (by decide) ?_ (fun _ _ _ => rfl)
  refine ⟨by rw [Function.update_of_ne (by omega)]; exact h0,
    by rw [Function.update_of_ne (by omega)]; exact h1, by simp,
    by rw [Function.update_of_ne (by omega)]; exact h3,
    by rw [Function.update_of_ne (by omega)]; exact h4,
    by rw [Function.update_of_ne (by omega)]; exact h5,
    by rw [Function.update_of_ne (by omega)]; exact h6,
    by rw [Function.update_of_ne (by omega)]; exact h7⟩

theorem OrdArenaAt.setPpar {b x v : ℕ} {S : OrdStoreState} {mem : ℕ → ℕ}
    (h : OrdArenaAt b S mem) (hx : x ≤ S.nextNode) :
    OrdArenaAt b { S with splay := S.splay.setPpar x v }
      (Function.update mem (ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + 3) v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h.nodes_at x hx
  refine h.updateNodeField hx (by decide) ?_ (fun _ _ _ => rfl)
  refine ⟨by rw [Function.update_of_ne (by omega)]; exact h0,
    by rw [Function.update_of_ne (by omega)]; exact h1,
    by rw [Function.update_of_ne (by omega)]; exact h2, by simp,
    by rw [Function.update_of_ne (by omega)]; exact h4,
    by rw [Function.update_of_ne (by omega)]; exact h5,
    by rw [Function.update_of_ne (by omega)]; exact h6,
    by rw [Function.update_of_ne (by omega)]; exact h7⟩

theorem OrdArenaAt.setSz {b x v : ℕ} {S : OrdStoreState} {mem : ℕ → ℕ}
    (h : OrdArenaAt b S mem) (hx : x ≤ S.nextNode) :
    OrdArenaAt b { S with splay := S.splay.updateNode x fun nd => { nd with sz := v } }
      (Function.update mem (ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + 4) v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h.nodes_at x hx
  refine h.updateNodeField hx (by decide) ?_ (fun _ _ _ => rfl)
  refine ⟨by rw [Function.update_of_ne (by omega)]; exact h0,
    by rw [Function.update_of_ne (by omega)]; exact h1,
    by rw [Function.update_of_ne (by omega)]; exact h2,
    by rw [Function.update_of_ne (by omega)]; exact h3, by simp,
    by rw [Function.update_of_ne (by omega)]; exact h5,
    by rw [Function.update_of_ne (by omega)]; exact h6,
    by rw [Function.update_of_ne (by omega)]; exact h7⟩

theorem OrdArenaAt.setNextFree {b x v : ℕ} {S : OrdStoreState} {mem : ℕ → ℕ}
    (h : OrdArenaAt b S mem) (hx : x ≤ S.nextNode) :
    OrdArenaAt b { S with nextFree := Function.update S.nextFree x v }
      (Function.update mem (ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + 7) v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h.nodes_at x hx
  have hnd : OrdNodeAt (Function.update mem (ordNodeAddr (ordNodesBase b S.vCap S.eCap) x + 7) v)
      (ordNodesBase b S.vCap S.eCap) x (id (S.splay.nodes x))
      (Function.update S.nextFree x v x) :=
    ⟨by rw [Function.update_of_ne (by omega)]; exact h0,
     by rw [Function.update_of_ne (by omega)]; exact h1,
     by rw [Function.update_of_ne (by omega)]; exact h2,
     by rw [Function.update_of_ne (by omega)]; exact h3,
     by rw [Function.update_of_ne (by omega)]; exact h4,
     by rw [Function.update_of_ne (by omega)]; exact h5,
     by rw [Function.update_of_ne (by omega)]; exact h6, by simp⟩
  have hupd := h.updateNodeField (off := 7) (val := v) (f := id)
    (nf' := Function.update S.nextFree x v) hx (by decide) hnd
    (fun y _ hyx => Function.update_of_ne hyx _ _)
  have hst : ({ S with splay := S.splay.updateNode x id, nextFree := Function.update S.nextFree x v } : OrdStoreState) =
      { S with nextFree := Function.update S.nextFree x v } := by
    have hsp : S.splay.updateNode x id = S.splay := by
      cases S.splay with
      | mk nodes =>
        simp only [SplayState.updateNode, SplayState.mk.injEq]
        funext y
        by_cases hyx : y = x <;> simp [hyx]
    rw [hsp]
  rwa [hst] at hupd

end MinCostFlow.SparseCore.Program
