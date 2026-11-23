module

public import MinCostFlow.SparseCore.Program.OrdStoreModel
import Mathlib.Tactic

/-!
# Order-store state invariant and Sleator–Tarjan potential

This file defines `OrdStoreState`, the invariant `OrdInv ord S` linking `S` to an abstract
order `ord : ℕ → List End`, and the amortized potential `ordPhi C_phi C_del S`. It proves the
node-count / pigeonhole lemmas and `ordInv_splay` (splaying a live node preserves `OrdInv`,
keeps `ord`, and drops `sumTreePhi` by `depth / 2 - 3 * ordStoreLog eCap`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

/-! ### Free-list chain and order-store state invariant -/

/-- `FreeChain head nxt fl` says `fl` is the linked list starting at `head` following `nxt`,
terminating at `0`, with all entries nonzero. -/
def FreeChain (head : ℕ) (nxt : ℕ → ℕ) : List ℕ → Prop
  | [] => head = 0
  | x :: xs => head = x ∧ x ≠ 0 ∧ FreeChain (nxt x) nxt xs

/-- Mathematical state of the order store. -/
structure OrdStoreState where
  vCap : ℕ
  eCap : ℕ
  splay : SplayState ℕ Unit Unit
  vRoot : ℕ → ℕ
  eNode : ℕ → ℕ
  trees : ℕ → AuxTree
  nextNode : ℕ
  freeHead : ℕ
  freeList : List ℕ
  nextFree : ℕ → ℕ

/-- Invariant linking an `OrdStoreState` to the abstract order `ord : ℕ → List End`. -/
structure OrdInv (ord : ℕ → List End) (S : OrdStoreState) : Prop where
  ord_unique : OrdUniqueWithin S.vCap S.eCap ord
  next_le : S.nextNode ≤ 2 * S.eCap
  clean : ∀ u, (S.splay.nodes u).rev = false
  null_node : S.splay.nodes 0 = ordNullNode
  tree_inv : ∀ v < S.vCap, TreeInv ordPayload S.splay (S.trees v)
  tree_out : ∀ v, S.vCap ≤ v → S.trees v = .leaf
  vRoot_eq : ∀ v < S.vCap, S.vRoot v = (S.trees v).rootId
  root_ppar : ∀ v < S.vCap, S.trees v ≠ .leaf → (S.splay.nodes (S.trees v).rootId).ppar = v + 1
  list_eq : ∀ v < S.vCap,
    (S.trees v).toList.map (fun u => endOfKey (S.splay.nodes u).val) = ord v
  disj_trees : ∀ u v, u ≠ v → ∀ x, x ∈ (S.trees u).toList → x ∉ (S.trees v).toList
  free_nodup : S.freeList.Nodup
  free_disj : ∀ v < S.vCap, ∀ x ∈ S.freeList, x ∉ (S.trees v).toList
  free_chain : FreeChain S.freeHead S.nextFree S.freeList
  nodes_range : ∀ x,
    (x ∈ S.freeList ∨ ∃ v < S.vCap, x ∈ (S.trees v).toList) ↔ 1 ≤ x ∧ x ≤ S.nextNode
  key_lt : ∀ v < S.vCap, ∀ x ∈ (S.trees v).toList, (S.splay.nodes x).val < 2 * S.eCap
  eNode_spec : ∀ k < 2 * S.eCap,
    (S.eNode k = 0 ∧ ∀ v < S.vCap, ∀ x ∈ (S.trees v).toList, (S.splay.nodes x).val ≠ k) ∨
    (∃ v < S.vCap, S.eNode k ∈ (S.trees v).toList ∧ (S.splay.nodes (S.eNode k)).val = k)

/-- Total Sleator–Tarjan potential across all vertex splay trees. -/
def sumTreePhi (S : OrdStoreState) : ℕ :=
  ∑ v ∈ Finset.range S.vCap, (S.trees v).treePhi (fun _ => 0)

/-- Total number of live nodes across all vertex splay trees. -/
def sumCountNodes (S : OrdStoreState) : ℕ :=
  ∑ v ∈ Finset.range S.vCap, (S.trees v).countNodes

/-- Amortized potential of the order store. -/
def ordPhi (C_phi C_del : ℕ) (S : OrdStoreState) : ℕ :=
  C_phi * sumTreePhi S + C_del * sumCountNodes S

/-! ### Consequence lemmas of `OrdInv` -/

theorem OrdInv.live_le_nextNode {ord : ℕ → List End} {S : OrdStoreState} (h : OrdInv ord S)
    {v x : ℕ} (hv : v < S.vCap) (hx : x ∈ (S.trees v).toList) :
    1 ≤ x ∧ x ≤ S.nextNode :=
  (h.nodes_range x).mp (Or.inr ⟨v, hv, hx⟩)

theorem OrdInv.free_le_nextNode {ord : ℕ → List End} {S : OrdStoreState} (h : OrdInv ord S)
    {x : ℕ} (hx : x ∈ S.freeList) :
    1 ≤ x ∧ x ≤ S.nextNode :=
  (h.nodes_range x).mp (Or.inl hx)

theorem OrdInv.eNode_eq_of_mem {ord : ℕ → List End} {S : OrdStoreState} (h : OrdInv ord S)
    {v x : ℕ} (hv : v < S.vCap) (hx : x ∈ (S.trees v).toList) :
    S.eNode (S.splay.nodes x).val = x := by
  set k := (S.splay.nodes x).val
  have hk : k < 2 * S.eCap := h.key_lt v hv x hx
  rcases h.eNode_spec k hk with ⟨_, hnone⟩ | ⟨v', hv', hx', hval'⟩
  · exact absurd rfl (hnone v hv x hx)
  · have hmem1 : endOfKey k ∈ ord v := by
      rw [← h.list_eq v hv]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    have hmem2 : endOfKey k ∈ ord v' := by
      rw [← h.list_eq v' hv']
      exact List.mem_map.mpr ⟨S.eNode k, hx', by rw [hval']⟩
    have hvv' : v' = v := h.ord_unique.unique_v hmem2 hmem1
    subst hvv'
    have hnd_ord : (ord v').Nodup := h.ord_unique.nodup v'
    rw [← h.list_eq v' hv'] at hnd_ord
    by_contra hne
    rcases List.getElem_of_mem hx with ⟨i, hi_lt, hgi⟩
    rcases List.getElem_of_mem hx' with ⟨j, hj_lt, hgj⟩
    have hij : i = j := by
      have hmap_eq : ((S.trees v').toList.map fun u => endOfKey (S.splay.nodes u).val)[i]'(by simp [hi_lt]) =
          ((S.trees v').toList.map fun u => endOfKey (S.splay.nodes u).val)[j]'(by simp [hj_lt]) := by
        simp [hgi, hgj, k, hval']
      have hfin : (⟨i, by simp [hi_lt]⟩ : Fin ((S.trees v').toList.map fun u => endOfKey (S.splay.nodes u).val).length) =
          ⟨j, by simp [hj_lt]⟩ := (List.nodup_iff_injective_getElem.mp hnd_ord) hmap_eq
      exact Fin.mk_eq_mk.mp hfin
    subst hij
    exact hne (hgj.symm.trans hgi)

theorem OrdInv.eNode_ne_zero_iff {ord : ℕ → List End} {S : OrdStoreState} (h : OrdInv ord S)
    {k : ℕ} (hk : k < 2 * S.eCap) :
    S.eNode k ≠ 0 ↔ ∃ v < S.vCap, endOfKey k ∈ ord v := by
  constructor
  · intro hnz
    rcases h.eNode_spec k hk with ⟨h0, _⟩ | ⟨v, hv, hx, hval⟩
    · exact absurd h0 hnz
    · refine ⟨v, hv, ?_⟩
      rw [← h.list_eq v hv]
      exact List.mem_map.mpr ⟨S.eNode k, hx, by rw [hval]⟩
  · rintro ⟨v, hv, hmem⟩
    rw [← h.list_eq v hv] at hmem
    rcases List.mem_map.mp hmem with ⟨x, hx, hxval⟩
    have hkeq : (S.splay.nodes x).val = k := endOfKey_injective hxval
    have heq := h.eNode_eq_of_mem hv hx
    rw [hkeq] at heq
    rw [heq]
    exact SplayState.SubtreeInv_nonZero (h.tree_inv v hv).sub hx

theorem OrdInv.sumCountNodes_add_free {ord : ℕ → List End} {S : OrdStoreState}
    (h : OrdInv ord S) :
    sumCountNodes S + S.freeList.length = S.nextNode := by
  let treeSet : ℕ → Finset ℕ := fun v => (S.trees v).toList.toFinset
  have hcard_t : ∀ v < S.vCap, (treeSet v).card = (S.trees v).countNodes := fun v hv => by
    rw [List.toFinset_card_of_nodup (h.tree_inv v hv).nodup, AuxTree.length_toList]
  have hdisj_t : (Finset.range S.vCap : Set ℕ).PairwiseDisjoint treeSet := by
    intro u hu v hv huv
    change Disjoint (treeSet u) (treeSet v)
    rw [Finset.disjoint_left]
    intro x hxu hxv
    exact h.disj_trees u v huv x (List.mem_toFinset.mp hxu) (List.mem_toFinset.mp hxv)
  have hdisj_f : Disjoint ((Finset.range S.vCap).biUnion treeSet) S.freeList.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxt hxf
    rcases Finset.mem_biUnion.mp hxt with ⟨v, hv, hxv⟩
    exact h.free_disj v (Finset.mem_range.mp hv) x (List.mem_toFinset.mp hxf) (List.mem_toFinset.mp hxv)
  have hunion : ((Finset.range S.vCap).biUnion treeSet) ∪ S.freeList.toFinset =
      Finset.Icc 1 S.nextNode := by
    ext x
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, List.mem_toFinset,
      Finset.mem_Icc, treeSet]
    rw [or_comm]
    exact h.nodes_range x
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj_f, Finset.card_biUnion hdisj_t,
      List.toFinset_card_of_nodup h.free_nodup, Nat.card_Icc] at hcard
  have hsum : ∑ v ∈ Finset.range S.vCap, (treeSet v).card = sumCountNodes S := by
    unfold sumCountNodes
    exact Finset.sum_congr rfl fun v hv => hcard_t v (Finset.mem_range.mp hv)
  rw [hsum] at hcard
  omega

theorem OrdInv.sumCountNodes_le {ord : ℕ → List End} {S : OrdStoreState} (h : OrdInv ord S) :
    sumCountNodes S ≤ 2 * S.eCap := by
  have := h.sumCountNodes_add_free
  have := h.next_le
  omega

/-- If there is a key `k < 2 * S.eCap` not currently live, then `sumCountNodes S < 2 * S.eCap`. -/
theorem OrdInv.sumCountNodes_lt_of_unused_key {ord : ℕ → List End} {S : OrdStoreState}
    (h : OrdInv ord S) {k : ℕ} (hk : k < 2 * S.eCap) (h0 : S.eNode k = 0) :
    sumCountNodes S < 2 * S.eCap := by
  let keySet : ℕ → Finset ℕ := fun v => ((S.trees v).toList.map fun u => (S.splay.nodes u).val).toFinset
  have hcard_k : ∀ v < S.vCap, (keySet v).card = (S.trees v).countNodes := fun v hv => by
    have hnd : ((S.trees v).toList.map fun u => (S.splay.nodes u).val).Nodup := by
      have hnd_ord := h.ord_unique.nodup v
      rw [← h.list_eq v hv] at hnd_ord
      have : (S.trees v).toList.map (fun u => endOfKey (S.splay.nodes u).val) =
          ((S.trees v).toList.map fun u => (S.splay.nodes u).val).map endOfKey := by
        rw [List.map_map]; rfl
      rw [this] at hnd_ord
      exact List.Nodup.of_map _ hnd_ord
    rw [List.toFinset_card_of_nodup hnd, List.length_map, AuxTree.length_toList]
  have hdisj_k : (Finset.range S.vCap : Set ℕ).PairwiseDisjoint keySet := by
    intro u hu v hv huv
    change Disjoint (keySet u) (keySet v)
    rw [Finset.disjoint_left]
    intro m hmu hmv
    rcases List.mem_map.mp (List.mem_toFinset.mp hmu) with ⟨xu, hxu, hval_u⟩
    rcases List.mem_map.mp (List.mem_toFinset.mp hmv) with ⟨xv, hxv, hval_v⟩
    have hm_u : endOfKey m ∈ ord u := by
      rw [← h.list_eq u (Finset.mem_range.mp hu)]
      exact List.mem_map.mpr ⟨xu, hxu, by rw [hval_u]⟩
    have hm_v : endOfKey m ∈ ord v := by
      rw [← h.list_eq v (Finset.mem_range.mp hv)]
      exact List.mem_map.mpr ⟨xv, hxv, by rw [hval_v]⟩
    exact huv (h.ord_unique.unique_v hm_u hm_v)
  have hsub : (Finset.range S.vCap).biUnion keySet ⊆ (Finset.range (2 * S.eCap)).erase k := by
    intro m hm
    rcases Finset.mem_biUnion.mp hm with ⟨v, hv, hmv⟩
    have hv' := Finset.mem_range.mp hv
    rcases List.mem_map.mp (List.mem_toFinset.mp hmv) with ⟨x, hx, hval⟩
    rw [Finset.mem_erase, Finset.mem_range]
    refine ⟨?_, hval ▸ h.key_lt v hv' x hx⟩
    intro hmk
    subst hmk
    rcases h.eNode_spec m hk with ⟨_, hnone⟩ | ⟨v', hv', hx', _⟩
    · exact hnone v hv' x hx hval
    · rw [h0] at hx'
      exact SplayState.SubtreeInv_nonZero (h.tree_inv v' hv').sub hx' rfl
  have hcard_le := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj_k, Finset.card_erase_of_mem (Finset.mem_range.mpr hk),
      Finset.card_range] at hcard_le
  have hsum : ∑ v ∈ Finset.range S.vCap, (keySet v).card = sumCountNodes S := by
    unfold sumCountNodes
    exact Finset.sum_congr rfl fun v hv => hcard_k v (Finset.mem_range.mp hv)
  rw [hsum] at hcard_le
  omega

/-- Updating a single vertex's tree in `sumTreePhi` / `sumCountNodes`. -/
theorem sumTreePhi_update {S S' : OrdStoreState} {v : ℕ}
    (hv : v < S.vCap) (hvc : S'.vCap = S.vCap)
    (hoth : ∀ u < S.vCap, u ≠ v → S'.trees u = S.trees u) :
    sumTreePhi S' + (S.trees v).treePhi (fun _ => 0) =
      sumTreePhi S + (S'.trees v).treePhi (fun _ => 0) := by
  unfold sumTreePhi
  rw [hvc]
  have hmem : v ∈ Finset.range S.vCap := Finset.mem_range.mpr hv
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase (s := Finset.range S.vCap)
      (f := fun u => (S.trees u).treePhi (fun _ => 0)) hmem]
  have hrest : ∑ u ∈ (Finset.range S.vCap).erase v, (S'.trees u).treePhi (fun _ => 0) =
      ∑ u ∈ (Finset.range S.vCap).erase v, (S.trees u).treePhi (fun _ => 0) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_erase, Finset.mem_range] at hu
    rw [hoth u hu.2 hu.1]
  rw [hrest]
  omega

theorem sumCountNodes_update {S S' : OrdStoreState} {v : ℕ}
    (hv : v < S.vCap) (hvc : S'.vCap = S.vCap)
    (hoth : ∀ u < S.vCap, u ≠ v → S'.trees u = S.trees u) :
    sumCountNodes S' + (S.trees v).countNodes =
      sumCountNodes S + (S'.trees v).countNodes := by
  unfold sumCountNodes
  rw [hvc]
  have hmem : v ∈ Finset.range S.vCap := Finset.mem_range.mpr hv
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase (s := Finset.range S.vCap)
      (f := fun u => (S.trees u).countNodes) hmem]
  have hrest : ∑ u ∈ (Finset.range S.vCap).erase v, (S'.trees u).countNodes =
      ∑ u ∈ (Finset.range S.vCap).erase v, (S.trees u).countNodes := by
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_erase, Finset.mem_range] at hu
    rw [hoth u hu.2 hu.1]
  rw [hrest]
  omega

theorem sumTreePhi_update2 {S S' : OrdStoreState} {v v' : ℕ}
    (hv : v < S.vCap) (hv' : v' < S.vCap) (hne : v ≠ v') (hvc : S'.vCap = S.vCap)
    (hoth : ∀ u < S.vCap, u ≠ v → u ≠ v' → S'.trees u = S.trees u) :
    sumTreePhi S' + (S.trees v).treePhi (fun _ => 0) + (S.trees v').treePhi (fun _ => 0) =
      sumTreePhi S + (S'.trees v).treePhi (fun _ => 0) + (S'.trees v').treePhi (fun _ => 0) := by
  unfold sumTreePhi
  rw [hvc]
  have hm1 : v ∈ Finset.range S.vCap := Finset.mem_range.mpr hv
  have hm2 : v' ∈ (Finset.range S.vCap).erase v := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_range.mpr hv'⟩
  rw [← Finset.add_sum_erase _ _ hm1, ← Finset.add_sum_erase _ _ hm2]
  rw [← Finset.add_sum_erase (s := Finset.range S.vCap) (f := fun u => (S.trees u).treePhi (fun _ => 0)) hm1,
      ← Finset.add_sum_erase (s := (Finset.range S.vCap).erase v) (f := fun u => (S.trees u).treePhi (fun _ => 0)) hm2]
  have hrest : ∑ u ∈ ((Finset.range S.vCap).erase v).erase v', (S'.trees u).treePhi (fun _ => 0) =
      ∑ u ∈ ((Finset.range S.vCap).erase v).erase v', (S.trees u).treePhi (fun _ => 0) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_range] at hu
    rw [hoth u hu.2.2 hu.2.1 hu.1]
  rw [hrest]
  omega

theorem sumCountNodes_update2 {S S' : OrdStoreState} {v v' : ℕ}
    (hv : v < S.vCap) (hv' : v' < S.vCap) (hne : v ≠ v') (hvc : S'.vCap = S.vCap)
    (hoth : ∀ u < S.vCap, u ≠ v → u ≠ v' → S'.trees u = S.trees u) :
    sumCountNodes S' + (S.trees v).countNodes + (S.trees v').countNodes =
      sumCountNodes S + (S'.trees v).countNodes + (S'.trees v').countNodes := by
  unfold sumCountNodes
  rw [hvc]
  have hm1 : v ∈ Finset.range S.vCap := Finset.mem_range.mpr hv
  have hm2 : v' ∈ (Finset.range S.vCap).erase v := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_range.mpr hv'⟩
  rw [← Finset.add_sum_erase _ _ hm1, ← Finset.add_sum_erase _ _ hm2]
  rw [← Finset.add_sum_erase (s := Finset.range S.vCap) (f := fun u => (S.trees u).countNodes) hm1,
      ← Finset.add_sum_erase (s := (Finset.range S.vCap).erase v) (f := fun u => (S.trees u).countNodes) hm2]
  have hrest : ∑ u ∈ ((Finset.range S.vCap).erase v).erase v', (S'.trees u).countNodes =
      ∑ u ∈ ((Finset.range S.vCap).erase v).erase v', (S.trees u).countNodes := by
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_range] at hu
    rw [hoth u hu.2.2 hu.2.1 hu.1]
  rw [hrest]
  omega

/-- Splaying a live node `x` of vertex `v`'s tree inside `S` preserves `OrdInv`, keeps `ord`,
places `x` at the root of `v`'s tree, and gives the Sleator–Tarjan potential inequality. -/
theorem ordInv_splay {ord : ℕ → List End} {S : OrdStoreState} {v x : ℕ}
    (h : OrdInv ord S) (hv : v < S.vCap) (hx : x ∈ (S.trees v).toList) :
    let fuel := (S.trees v).countNodes
    let sp' := SplayState.splayLoop ordPayload S.splay fuel x
    ∃ t',
      let S' : OrdStoreState :=
        { S with
          splay := sp'
          vRoot := Function.update S.vRoot v x
          trees := Function.update S.trees v t' }
      OrdInv ord S' ∧
      t' ≠ .leaf ∧
      t'.rootId = x ∧
      t'.toList = (S.trees v).toList ∧
      t'.countNodes = (S.trees v).countNodes ∧
      sumCountNodes S' = sumCountNodes S ∧
      sumTreePhi S' + (S.trees v).depthOf x / 2 ≤ sumTreePhi S + 3 * ordStoreLog S.eCap := by
  dsimp only
  have hfuel : (S.trees v).depthOf x < (S.trees v).countNodes := depthOf_lt_countNodes hx
  obtain ⟨t', ht', hne, hroot, htoList, hclean', hval, hpp, hout, hcnt, hphi⟩ :=
    ord_splay_spec (h.tree_inv v hv) h.clean hx hfuel
  refine ⟨t', ?_, hne, hroot, htoList, hcnt, ?_, ?_⟩
  · have hzero_nmem : 0 ∉ (S.trees v).toList := fun h0 =>
      SplayState.SubtreeInv_nonZero (h.tree_inv v hv).sub h0 rfl
    refine
      { ord_unique := h.ord_unique
        next_le := h.next_le
        clean := hclean'
        null_node := (hout 0 hzero_nmem).trans h.null_node
        tree_inv := fun u hu => by
          by_cases huv : u = v
          · subst huv; simpa using ht'
          · simp only [Function.update_of_ne huv]
            exact SplayState.TreeInv_agree (h.tree_inv u hu) fun z hz =>
              (hout z (h.disj_trees u v huv z hz)).symm
        tree_out := fun u hu => by
          have huv : u ≠ v := fun heq => by subst heq; exact absurd hv (Nat.not_lt.mpr hu)
          simp [Function.update_of_ne huv, h.tree_out u hu]
        vRoot_eq := fun u hu => by
          by_cases huv : u = v
          · subst huv; simp [hroot]
          · simp [Function.update_of_ne huv, h.vRoot_eq u hu]
        root_ppar := fun u hu hune => by
          by_cases huv : u = v
          · subst huv
            simp only [Function.update_self, hroot] at hune ⊢
            have hvt_ne : S.trees u ≠ .leaf := fun hleaf => by
              rw [hleaf] at hx; exact List.not_mem_nil hx
            exact hpp.trans (h.root_ppar u hu hvt_ne)
          · simp only [Function.update_of_ne huv] at hune ⊢
            rw [hout _ (h.disj_trees u v huv _ (AuxTree.rootId_mem hune))]
            exact h.root_ppar u hu hune
        list_eq := fun u hu => by
          by_cases huv : u = v
          · subst huv
            simp only [Function.update_self]
            rw [← h.list_eq u hu, htoList]
            exact List.map_congr_left fun z hz => congrArg endOfKey (hval z hz)
          · simp only [Function.update_of_ne huv]
            rw [← h.list_eq u hu]
            exact List.map_congr_left fun z hz =>
              congrArg (fun nd => endOfKey nd.val) (hout z (h.disj_trees u v huv z hz))
        disj_trees := fun u₁ u₂ hne' z hz1 hz2 => by
          by_cases h1 : u₁ = v
          · subst h1
            simp only [Function.update_self, htoList] at hz1
            simp only [Function.update_of_ne (Ne.symm hne')] at hz2
            exact h.disj_trees u₁ u₂ hne' z hz1 hz2
          · by_cases h2 : u₂ = v
            · subst h2
              simp only [Function.update_of_ne h1] at hz1
              simp only [Function.update_self, htoList] at hz2
              exact h.disj_trees u₁ u₂ hne' z hz1 hz2
            · simp only [Function.update_of_ne h1] at hz1
              simp only [Function.update_of_ne h2] at hz2
              exact h.disj_trees u₁ u₂ hne' z hz1 hz2
        free_nodup := h.free_nodup
        free_disj := fun u hu z hzf hzt => by
          by_cases huv : u = v
          · subst huv; simp only [Function.update_self, htoList] at hzt; exact h.free_disj u hu z hzf hzt
          · simp only [Function.update_of_ne huv] at hzt; exact h.free_disj u hu z hzf hzt
        free_chain := h.free_chain
        nodes_range := fun z => by
          rw [← h.nodes_range z]
          constructor <;> rintro (hf | ⟨u, hu, hzu⟩)
          · exact Or.inl hf
          · refine Or.inr ⟨u, hu, ?_⟩
            by_cases huv : u = v
            · subst huv; simpa [htoList] using hzu
            · simpa [Function.update_of_ne huv] using hzu
          · exact Or.inl hf
          · refine Or.inr ⟨u, hu, ?_⟩
            by_cases huv : u = v
            · subst huv; simpa [htoList] using hzu
            · simpa [Function.update_of_ne huv] using hzu
        key_lt := fun u hu z hz => by
          by_cases huv : u = v
          · subst huv
            simp only [Function.update_self, htoList] at hz
            rw [hval z hz]; exact h.key_lt u hu z hz
          · simp only [Function.update_of_ne huv] at hz
            rw [hout z (h.disj_trees u v huv z hz)]; exact h.key_lt u hu z hz
        eNode_spec := fun k hk => by
          rcases h.eNode_spec k hk with ⟨h0, hnone⟩ | ⟨u, hu, hxu, hval_u⟩
          · refine Or.inl ⟨h0, fun u hu z hz => ?_⟩
            by_cases huv : u = v
            · subst huv
              simp only [Function.update_self, htoList] at hz
              rw [hval z hz]; exact hnone u hu z hz
            · simp only [Function.update_of_ne huv] at hz
              rw [hout z (h.disj_trees u v huv z hz)]; exact hnone u hu z hz
          · refine Or.inr ⟨u, hu, ?_, ?_⟩
            · by_cases huv : u = v
              · subst huv; simpa [htoList] using hxu
              · simpa [Function.update_of_ne huv] using hxu
            · by_cases huv : u = v
              · subst huv; rw [hval _ hxu]; exact hval_u
              · rw [hout _ (h.disj_trees u v huv _ hxu)]; exact hval_u }
  · have hsc := sumCountNodes_update (S := S)
      (S' := { S with splay := SplayState.splayLoop ordPayload S.splay (S.trees v).countNodes x,
                      vRoot := Function.update S.vRoot v x,
                      trees := Function.update S.trees v t' }) hv rfl
      (fun u _ huv => Function.update_of_ne huv _ _)
    simp only [Function.update_self] at hsc
    omega
  · have hsp_eq := sumTreePhi_update (S := S)
      (S' := { S with splay := SplayState.splayLoop ordPayload S.splay (S.trees v).countNodes x,
                      vRoot := Function.update S.vRoot v x,
                      trees := Function.update S.trees v t' }) hv rfl
      (fun u _ huv => Function.update_of_ne huv _ _)
    simp only [Function.update_self] at hsp_eq
    have hcnt_le : t'.countNodes ≤ 2 * S.eCap := by
      rw [hcnt]
      have h1 : (S.trees v).countNodes ≤ sumCountNodes S :=
        Finset.single_le_sum (f := fun u => (S.trees u).countNodes)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hv)
      exact le_trans h1 h.sumCountNodes_le
    have hrk := rank_zero_le_ordStoreLog hcnt_le
    omega

end MinCostFlow.SparseCore.Program
