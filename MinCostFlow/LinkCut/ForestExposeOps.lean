module

public import MinCostFlow.LinkCut.ForestExpose
import MinCostFlow.LinkCut.ForestReversals
import MinCostFlow.LinkCut.ForestCutLink

namespace MinCostFlow.LinkCut

@[expose] public section

variable {α : Type*} {σ : Type*} {τ : Type*}

/-- Initial `SplayNode` array with vertices `1..n` as singleton trees and `n+1..2n` chained on the free list. -/
def lctInitNodes (P : LctPayload α σ τ) (n : ℕ) (defVal : α) : ℕ → SplayNode α σ τ :=
  fun i =>
    if 1 ≤ i ∧ i ≤ n then
      { left := 0, right := 0, par := 0, ppar := 0, sz := 1,
        val := defVal, sum := P.single i defVal, tag := P.idTag, rev := false }
    else if n + 1 ≤ i ∧ i < 2 * n then
      { left := 0, right := 0, par := if i + 1 < 2 * n then i + 1 else 0, ppar := 0, sz := 1,
        val := defVal, sum := P.empty, tag := P.idTag, rev := false }
    else
      { left := 0, right := 0, par := 0, ppar := 0, sz := 1,
        val := defVal, sum := P.empty, tag := P.idTag, rev := false }

/-- Initialize an `n`-vertex link-cut forest state with `n` isolated vertices and `n - 1` free edge slots. -/
def lctInit (P : LctPayload α σ τ) (n : ℕ) (defVal : α) : LctState α σ τ :=
  { n := n
    splay := { nodes := lctInitNodes P n defVal }
    freeHead := if n ≤ 1 then 0 else n + 1 }

/-- Follow `par` pointers for at most `fuel` steps to measure a node's depth in its auxiliary tree. -/
def splayDepth (st : SplayState α σ τ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, x =>
      let p := (st.nodes x).par
      if p == 0 then 0 else 1 + splayDepth st fuel p

/-- All `(nodeId, effectiveVal)` pairs across a list of auxiliary trees, ordered top-to-bottom within each tree. -/
def forestPairs (P : LctPayload α σ τ) (s : SplayState α σ τ) (ts : List AuxTree) : List (ℕ × α) :=
  ts.flatMap (fun t => SplayState.evalPairs P s t false P.idTag)

/-- Single bottom-up `expose` splice step from `last` into its path parent `p = (st.nodes last).ppar`. -/
def lctExposeStep (P : LctPayload α σ τ) (st : LctState α σ τ) (last : ℕ) :
    LctState α σ τ × ℕ × ℕ :=
  let p := (st.splay.nodes last).ppar
  let d := splayDepth st.splay (2 * st.n + 1) p
  let s1 := SplayState.splay P st.splay (2 * st.n + 1) p
  let s2 := SplayState.detachRight P s1 p
  let s3 := SplayState.attachRight P s2 p last
  ({ n := st.n, splay := s3, freeHead := st.freeHead }, p, d / 2)

/-- Loop of `lctExposeStep` up to `fuel` iterations until `(st.splay.nodes last).ppar = 0`. -/
def lctExposeLoop (P : LctPayload α σ τ) (st : LctState α σ τ) :
    ℕ → ℕ → LctState α σ τ × ℕ × ℕ × ℕ
  | 0, last => (st, last, 0, 0)
  | fuel + 1, last =>
      if (st.splay.nodes last).ppar == 0 then
        (st, last, 0, 0)
      else
        let r1 := lctExposeStep P st last
        let r2 := lctExposeLoop P r1.1 fuel r1.2.1
        (r2.1, r2.2.1, r1.2.2 + r2.2.2.1, 1 + r2.2.2.2)

/-- Expose `v`, returning `(st', splayHalves, spliceIters)`.
Ref: Lemma 4.1 (arXiv:2309.16629v1, p. 13), citing [KangP15] Section 4. -/
def lctExposeCost (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    LctState α σ τ × ℕ × ℕ :=
  let d0 := splayDepth st.splay (2 * st.n + 1) v
  let s0 := SplayState.splay P st.splay (2 * st.n + 1) v
  let s1 := SplayState.detachRight P s0 v
  let st1 : LctState α σ τ := { n := st.n, splay := s1, freeHead := st.freeHead }
  let rLoop := lctExposeLoop P st1 (2 * st.n + 1) v
  let dFin := splayDepth rLoop.1.splay (2 * st.n + 1) v
  let sFin := SplayState.splay P rLoop.1.splay (2 * st.n + 1) v
  ({ n := st.n, splay := sFin, freeHead := rLoop.1.freeHead },
    d0 / 2 + rLoop.2.2.1 + dFin / 2,
    1 + rLoop.2.2.2)

/-- Expose node `v` so the represented root-to-`v` path becomes a single root auxiliary tree with `v` splayed to root. -/
def lctExpose (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) : LctState α σ τ :=
  (lctExposeCost P st v).1

theorem lctExposeLoop_n (P : LctPayload α σ τ) :
    ∀ fuel st last, (lctExposeLoop P st fuel last).1.n = st.n
  | 0, _, _ => rfl
  | fuel + 1, st, last => by
      dsimp only [lctExposeLoop]
      split_ifs
      · rfl
      · exact (lctExposeLoop_n P fuel _ _).trans rfl

theorem lctExposeLoop_freeHead (P : LctPayload α σ τ) :
    ∀ fuel st last, (lctExposeLoop P st fuel last).1.freeHead = st.freeHead
  | 0, _, _ => rfl
  | fuel + 1, st, last => by
      dsimp only [lctExposeLoop]
      split_ifs
      · rfl
      · exact (lctExposeLoop_freeHead P fuel _ _).trans rfl

/-! ### `lctInit` specification -/

private theorem nodup_map_of_inj {β γ : Type*} {f : β → γ}
    (hinj : ∀ a b, f a = f b → a = b) : ∀ {xs : List β}, xs.Nodup → (xs.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hnd => by
      rcases List.nodup_cons.mp hnd with ⟨hx, hxs⟩
      refine List.nodup_cons.mpr ⟨fun hm => hx ?_, nodup_map_of_inj hinj hxs⟩
      rcases List.mem_map.mp hm with ⟨y, hy, hyx⟩
      exact hinj y x hyx ▸ hy

private theorem list_sum_nat_eq_zero : ∀ xs : List ℕ, (∀ x ∈ xs, x = 0) → xs.sum = 0
  | [], _ => rfl
  | x :: xs, hx => by
      simp [hx x List.mem_cons_self, list_sum_nat_eq_zero xs (fun y hy => hx y (List.mem_cons_of_mem _ hy))]

private theorem flatMap_singleton_map {β γ : Type*} (f : β → γ) :
    ∀ xs : List β, xs.flatMap (fun x => [f x]) = xs.map f
  | [] => rfl
  | x :: xs => by simp [flatMap_singleton_map f xs]

private theorem freeListInv_range (P : LctPayload α σ τ) (n : ℕ) (defVal : α) :
    ∀ k a, a + k = n - 1 →
      FreeListInv { nodes := lctInitNodes P n defVal }
        (if k = 0 then 0 else n + 1 + a)
        ((List.range k).map (fun i => n + 1 + (a + i))) := by
  intro k
  induction k with
  | zero => intro a _; simp [FreeListInv]
  | succ k ih =>
      intro a hak
      have h_node : n + 1 ≤ n + 1 + a ∧ n + 1 + a < 2 * n := by omega
      have h_not_v : ¬ (1 ≤ n + 1 + a ∧ n + 1 + a ≤ n) := by omega
      have hnext_par : (lctInitNodes P n defVal (n + 1 + a)).par =
          if k = 0 then 0 else n + 1 + (a + 1) := by
        dsimp only [lctInitNodes]
        simp only [eq_false h_not_v, eq_true h_node, ↓reduceIte]
        split_ifs <;> omega
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero, eq_false (Nat.succ_ne_zero k), ↓reduceIte]
      refine ⟨by omega, rfl, ?_⟩
      rw [hnext_par]
      rw [show ((fun x => n + 1 + (a + x)) ∘ Nat.succ) = (fun i => n + 1 + (a + 1 + i)) by
        funext i; dsimp; omega]
      exact ih (a + 1) (by omega)

private theorem freeList_init_eq (P : LctPayload α σ τ) (n : ℕ) (defVal : α) :
    FreeListInv { nodes := lctInitNodes P n defVal }
      (if n ≤ 1 then 0 else n + 1)
      ((List.range (n - 1)).map (fun i => n + 1 + i)) := by
  have h := freeListInv_range P n defVal (n - 1) 0 (by omega)
  by_cases hn : n ≤ 1
  · have hm : n - 1 = 0 := by omega
    simpa [hn, hm] using h
  · have hm : n - 1 ≠ 0 := by omega
    simpa [hn, hm] using h

private theorem lctInitNodes_eval_singleton {P : LctPayload α σ τ} (hL : P.Laws)
    {n i : ℕ} (hi : i < n) (defVal : α) :
    SplayState.evalPairs P { nodes := lctInitNodes P n defVal }
      (AuxTree.node (vid i) AuxTree.leaf AuxTree.leaf) false P.idTag = [(vid i, defVal)] := by
  have h1 : 1 ≤ vid i ∧ vid i ≤ n := by simp [vid]; omega
  simp [SplayState.evalPairs, lctInitNodes, h1, hL.actVal_id]

private theorem lctInit_sum_singleton {P : LctPayload α σ τ} (hL : P.Laws)
    {n i : ℕ} (hi : i < n) (defVal : α) :
    ((lctInitNodes P n defVal (vid i)).sum) =
      P.listSummary (SplayState.evalPairs P { nodes := lctInitNodes P n defVal }
        (AuxTree.node (vid i) AuxTree.leaf AuxTree.leaf) false P.idTag) := by
  rw [lctInitNodes_eval_singleton hL hi defVal]
  have h1 : 1 ≤ vid i ∧ vid i ≤ n := by simp [vid]; omega
  simp [lctInitNodes, h1, LctPayload.listSummary, hL.combine_empty_right]

private theorem inducedSubPar_init {P : LctPayload α σ τ} (n : ℕ) (defVal : α) :
    let trees := (List.range n).map (fun i => AuxTree.node (vid i) AuxTree.leaf AuxTree.leaf)
    ∀ z, inducedSubPar P { nodes := lctInitNodes P n defVal } trees z = 0 := by
  intro trees z
  suffices ∀ (k a : ℕ), a + k ≤ n →
      inducedSubPar P { nodes := lctInitNodes P n defVal }
        ((List.range k).map (fun i => AuxTree.node (vid (a + i)) AuxTree.leaf AuxTree.leaf)) z = 0 by
    simpa using this n 0 (by omega)
  intro k
  induction k with
  | zero => intro a _; simp [inducedSubPar]
  | succ k ih =>
      intro a hak
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [inducedSubPar, Nat.add_zero]
      have h_not_v : 1 ≤ vid a ∧ vid a ≤ n := by simp [vid]; omega
      have h_ids : treeIds P { nodes := lctInitNodes P n defVal }
          (AuxTree.node (vid a) AuxTree.leaf AuxTree.leaf) = [vid a] := by
        simp [treeIds, SplayState.evalPairs]
      rw [h_ids]
      by_cases hza : z = vid a
      · subst hza
        simp [chainPred, AuxTree.rootId, lctInitNodes, h_not_v]
      · simp only [List.mem_singleton, eq_false hza, ↓reduceIte]
        rw [show ((fun i => AuxTree.node (vid (a + i)) AuxTree.leaf AuxTree.leaf) ∘ Nat.succ) =
            (fun i => AuxTree.node (vid (a + 1 + i)) AuxTree.leaf AuxTree.leaf) by
          funext i; dsimp [vid]; congr 2; omega]
        exact ih (a + 1) (by omega)

theorem lctInit_spec {P : LctPayload α σ τ} (hL : P.Laws) (n : ℕ) (defVal : α) :
    let st := lctInit P n defVal
    let trees := (List.range n).map (fun i => AuxTree.node (vid i) AuxTree.leaf AuxTree.leaf)
    let freeList := (List.range (n - 1)).map (fun i => n + 1 + i)
    let depth := fun (_ : ℕ) => (1 : ℕ)
    LctInvWith P st trees freeList depth ∧
      sumTreePhi P st = 0 ∧
      heavyCount P st = 0 ∧
      (∀ i < n, SplayState.evalPairs P st.splay (AuxTree.node (vid i) AuxTree.leaf AuxTree.leaf)
        false P.idTag = [(vid i, defVal)]) ∧
      ∀ z, inducedSubPar P st.splay trees z = 0 := by
  intro st trees freeList depth
  have hflat_trees : trees.flatMap AuxTree.toList = (List.range n).map vid := by
    dsimp only [trees]
    rw [List.flatMap_map]
    exact flatMap_singleton_map vid (List.range n)
  have hnd_trees : (trees.flatMap AuxTree.toList).Nodup := by
    rw [hflat_trees]
    exact nodup_map_of_inj (fun a b h => by simp [vid] at h; omega) List.nodup_range
  have hpar0 : ∀ z, inducedSubPar P st.splay trees z = 0 := inducedSubPar_init n defVal
  have hW : LctInvWith P st trees freeList depth :=
    { treesNonEmpty := fun t ht => by
        rcases List.mem_map.mp ht with ⟨i, _, rfl⟩; simp
      treesInv := fun t ht => by
        rcases List.mem_map.mp ht with ⟨i, hi, rfl⟩
        have hi_lt := List.mem_range.mp hi
        have hv : 1 ≤ vid i ∧ vid i ≤ n := by simp [vid]; omega
        refine ⟨by simp [AuxTree.toList], ?_⟩
        rw [SplayState.SubtreeInv.eq_2]
        refine ⟨by simp [vid], by simp [lctInit, st, lctInitNodes, hv, AuxTree.rootId],
          by simp [lctInit, st, lctInitNodes, hv, AuxTree.rootId],
          by simp [lctInit, st, lctInitNodes, hv], fun h => by omega,
          by simp [lctInit, st, lctInitNodes, hv, AuxTree.countNodes],
          lctInit_sum_singleton hL hi_lt defVal, by simp [SplayState.SubtreeInv], by simp [SplayState.SubtreeInv]⟩
      activeNodup := hnd_trees
      activeValid := fun x hx => by
        rw [hflat_trees] at hx
        rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
        have hi_lt := List.mem_range.mp hi
        dsimp only [st, lctInit]
        simp [isNode, vid]; omega
      verticesActive := fun v hv => by
        rw [hflat_trees]; exact List.mem_map.mpr ⟨v, List.mem_range.mpr hv, rfl⟩
      freeNodup := nodup_map_of_inj (fun a b h => by omega) List.nodup_range
      freeValid := fun e he => by
        rcases List.mem_map.mp he with ⟨i, hi, rfl⟩
        have hi_lt := List.mem_range.mp hi
        dsimp only [st, lctInit]
        simp [isEdgeSlot]; omega
      partitionSlots := fun e he => by
        rw [hflat_trees]
        dsimp only [st, lctInit, isEdgeSlot] at he
        constructor
        · intro hmem _
          rcases List.mem_map.mp hmem with ⟨i, hi, hid⟩
          have hi_lt := List.mem_range.mp hi
          simp [vid] at hid; omega
        · intro hnin
          exfalso; apply hnin
          exact List.mem_map.mpr ⟨e - (n + 1), List.mem_range.mpr (by omega), by omega⟩
      freeListInv := freeList_init_eq P n defVal
      pparActive := fun t ht hp => by
        rcases List.mem_map.mp ht with ⟨i, hi, rfl⟩
        have hi_lt := List.mem_range.mp hi
        have hv : 1 ≤ vid i ∧ vid i ≤ n := by simp [vid]; omega
        simp [st, lctInit, lctInitNodes, hv, AuxTree.rootId] at hp
      acyclic := fun x _ hx => absurd (hpar0 x) hx
      vertexParEdge := fun x _ hx => absurd (hpar0 x) hx
      edgeParVertex := fun e he hes => by
        rw [hflat_trees] at he
        rcases List.mem_map.mp he with ⟨i, hi, hid⟩
        have hi_lt := List.mem_range.mp hi
        dsimp only [st, lctInit, isEdgeSlot] at hes
        simp [vid] at hid; omega
      edgeUniqueChild := fun e he hes => by
        rw [hflat_trees] at he
        rcases List.mem_map.mp he with ⟨i, hi, hid⟩
        have hi_lt := List.mem_range.mp hi
        dsimp only [st, lctInit, isEdgeSlot] at hes
        simp [vid] at hid; omega }
  have hpot := LctInvWith_canon_potentials hW
  have hsum_zero : sumTreePhiList (vSize P st.splay (trees.flatMap AuxTree.toList)
      (inducedSubPar P st.splay trees) trees) trees = 0 := by
    dsimp only [sumTreePhiList]
    refine list_sum_nat_eq_zero _ (fun y hy => ?_)
    rcases List.mem_map.mp hy with ⟨t, ht, rfl⟩
    rcases List.mem_map.mp ht with ⟨i, hi, rfl⟩
    have hi_lt := List.mem_range.mp hi
    have hv_eq_0 : vSize P st.splay (trees.flatMap AuxTree.toList)
        (inducedSubPar P st.splay trees) trees (vid i) = 0 := by
      dsimp only [vSize]
      suffices List.filter (fun t => (st.splay.nodes t.rootId).ppar == vid i) trees = [] by
        simp [this]
      rw [List.filter_eq_nil_iff]
      intro c hc
      rcases List.mem_map.mp hc with ⟨j, hj, rfl⟩
      have hj_lt := List.mem_range.mp hj
      have hvj : 1 ≤ j + 1 ∧ j + 1 ≤ n := by omega
      simp [st, lctInit, lctInitNodes, hvj, AuxTree.rootId, vid]
    simp [AuxTree.treePhi, AuxTree.rank, AuxTree.treeSize, hv_eq_0]
  have hheavy_zero : heavyCountList P st.splay (trees.flatMap AuxTree.toList)
      (inducedSubPar P st.splay trees) trees = 0 := by
    dsimp only [heavyCountList, trees]
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro t ht
    rcases List.mem_map.mp ht with ⟨i, hi, rfl⟩
    have hi_lt := List.mem_range.mp hi
    have hv : 1 ≤ i + 1 ∧ i + 1 ≤ n := by omega
    simp [isHeavyEdge, st, lctInit, lctInitNodes, hv, AuxTree.rootId, vid]
  refine ⟨hW, hpot.2.trans hsum_zero, hpot.1.trans hheavy_zero,
    fun i hi => lctInitNodes_eval_singleton hL hi defVal, hpar0⟩

/-! ### `splayDepth`, tree sizes, `listLast0`, and `reaches` helpers -/

private theorem depthOf_lt_length : ∀ {t : AuxTree} {x : ℕ}, x ∈ t.toList → t.depthOf x < t.toList.length
  | .leaf, _, hx => by simp [AuxTree.toList] at hx
  | .node id l r, x, hx => by
      by_cases hxi : x = id
      · subst hxi; simp [AuxTree.depthOf, AuxTree.toList]; omega
      · simp only [AuxTree.toList, List.mem_append, List.mem_singleton, eq_false hxi, or_false] at hx
        rw [AuxTree.depthOf.eq_2]
        simp only [eq_false hxi, ↓reduceIte, AuxTree.toList, List.length_append, List.length_singleton]
        by_cases hxl : x ∈ l.toList
        · have h1 := depthOf_lt_length hxl
          simp only [eq_true hxl, ↓reduceIte]; omega
        · have hxr : x ∈ r.toList := hx.resolve_left hxl
          have h1 := depthOf_lt_length hxr
          simp only [eq_false hxl, eq_true hxr, ↓reduceIte]; omega

theorem tree_length_le_active {ts : List AuxTree} {t : AuxTree} (ht : t ∈ ts) :
    t.toList.length ≤ (ts.flatMap AuxTree.toList).length := by
  have hperm := (List.perm_cons_erase ht).flatMap_right AuxTree.toList
  rw [hperm.length_eq, List.flatMap_cons, List.length_append]
  omega

private theorem splayDepth_subtree {P : LctPayload α σ τ} {st : SplayState α σ τ} :
    ∀ {t : AuxTree} {rp x k : ℕ},
      t.toList.Nodup →
      SplayState.SubtreeInv P st rp t →
      x ∈ t.toList →
      t.depthOf x < k →
      splayDepth st k x =
        t.depthOf x + (if rp == 0 then 0 else 1 + splayDepth st (k - t.depthOf x - 1) rp) := by
  intro t
  induction t with
  | leaf => intro rp x k _ _ hx; simp [AuxTree.toList] at hx
  | node id l r ihl ihr =>
      intro rp x k hnd hinv hx hk
      rw [SplayState.SubtreeInv.eq_2] at hinv
      rcases hinv with ⟨hid_nz, _, _, hpar_id, _, _, _, hl, hr⟩
      rcases AuxTree.nodup_node_unfold hnd with ⟨hnd_l, hid_l, hnd_r, hid_r, hdisj⟩
      by_cases hxi : x = id
      · subst hxi
        have hd0 : (AuxTree.node x l r).depthOf x = 0 := by simp [AuxTree.depthOf]
        cases k with
        | zero => omega
        | succ k' =>
            rw [hd0]
            simp only [splayDepth, hpar_id, Nat.zero_add, Nat.sub_zero]
            split_ifs with hrp <;> simp
      · simp only [AuxTree.toList, List.mem_append, List.mem_singleton, eq_false hxi, or_false] at hx
        by_cases hxl : x ∈ l.toList
        · have hd_eq : (AuxTree.node id l r).depthOf x = l.depthOf x + 1 := by
            rw [AuxTree.depthOf.eq_2]; simp [eq_false hxi, hxl]
          have ih_k := ihl hnd_l hl hxl (by omega : l.depthOf x < k)
          have hrem : k - l.depthOf x - 1 = (k - (l.depthOf x + 1) - 1) + 1 := by omega
          rw [ih_k, hd_eq, beq_false_of_ne hid_nz, hrem]
          simp only [Bool.false_eq_true, ↓reduceIte, splayDepth, hpar_id]
          split_ifs <;> omega
        · have hxr : x ∈ r.toList := hx.resolve_left hxl
          have hd_eq : (AuxTree.node id l r).depthOf x = r.depthOf x + 1 := by
            rw [AuxTree.depthOf.eq_2]; simp [eq_false hxi, eq_false hxl, hxr]
          have ih_k := ihr hnd_r hr hxr (by omega : r.depthOf x < k)
          have hrem : k - r.depthOf x - 1 = (k - (r.depthOf x + 1) - 1) + 1 := by omega
          rw [ih_k, hd_eq, beq_false_of_ne hid_nz, hrem]
          simp only [Bool.false_eq_true, ↓reduceIte, splayDepth, hpar_id]
          split_ifs <;> omega

theorem splayDepth_eq_depthOf {P : LctPayload α σ τ} {st : SplayState α σ τ} {t : AuxTree}
    {x fuel : ℕ} (ht : SplayState.TreeInv P st t) (hx : x ∈ t.toList) (hf : t.depthOf x < fuel) :
    splayDepth st fuel x = t.depthOf x := by
  have h := splayDepth_subtree ht.nodup ht.sub hx hf
  simpa using h

theorem listLast0_append_of_ne_nil {xs ys : List ℕ} (hys : ys ≠ []) :
    listLast0 (xs ++ ys) = listLast0 ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have hne : xs ++ ys ≠ [] := by intro h; simp_all
      simp only [List.cons_append]
      cases hxs : xs ++ ys with
      | nil => exact absurd hxs hne
      | cons b rest => simpa [listLast0, hxs] using ih

theorem evalPairs_of_rev_false {P : LctPayload α σ τ} (hL : P.Laws) {s : SplayState α σ τ}
    {x : ℕ} {l r : AuxTree} (hrev : (s.nodes x).rev = false) (htag : (s.nodes x).tag = P.idTag) :
    SplayState.evalPairs P s (AuxTree.node x l r) false P.idTag =
      SplayState.evalPairs P s l false P.idTag ++ [(x, (s.nodes x).val)] ++
        SplayState.evalPairs P s r false P.idTag := by
  rw [SplayState.evalPairs.eq_2]
  simp [hrev, htag, hL.compTag_id_left, hL.actVal_id]

theorem treeIds_of_rev_false {P : LctPayload α σ τ} (hL : P.Laws) {s : SplayState α σ τ}
    {x : ℕ} {l r : AuxTree} (hrev : (s.nodes x).rev = false) (htag : (s.nodes x).tag = P.idTag) :
    treeIds P s (AuxTree.node x l r) = treeIds P s l ++ [x] ++ treeIds P s r := by
  simp [treeIds, evalPairs_of_rev_false hL hrev htag]

theorem listLast0_eq_root_of_right_leaf {P : LctPayload α σ τ} (hL : P.Laws) {s : SplayState α σ τ}
    {x : ℕ} {l : AuxTree} (hrev : (s.nodes x).rev = false) (htag : (s.nodes x).tag = P.idTag) :
    listLast0 (treeIds P s (AuxTree.node x l AuxTree.leaf)) = x := by
  rw [treeIds_of_rev_false hL hrev htag]
  simp only [treeIds, SplayState.evalPairs.eq_1, List.map_nil, List.append_nil]
  rw [listLast0_append_of_ne_nil (by simp)]
  simp [listLast0]

theorem right_eq_leaf_of_listLast0 {P : LctPayload α σ τ} (hL : P.Laws) {s : SplayState α σ τ}
    {x : ℕ} {l r : AuxTree} (ht : SplayState.TreeInv P s (AuxTree.node x l r))
    (hrev : (s.nodes x).rev = false) (htag : (s.nodes x).tag = P.idTag)
    (hlast : listLast0 (treeIds P s (AuxTree.node x l r)) = x) :
    r = AuxTree.leaf ∧ (s.nodes x).right = 0 := by
  have hr_leaf : r = AuxTree.leaf := by
    cases r with
    | leaf => rfl
    | node y ly ry =>
        exfalso
        have hr_ne_leaf : AuxTree.node y ly ry ≠ AuxTree.leaf := by simp
        have hr_nil : treeIds P s (AuxTree.node y ly ry) ≠ [] := treeIds_ne_nil hr_ne_leaf
        have hids := treeIds_of_rev_false hL hrev htag (l := l) (r := AuxTree.node y ly ry)
        have hlast' := listLast0_append_of_ne_nil (xs := treeIds P s l ++ [x]) hr_nil
        rw [← hids, hlast] at hlast'
        have hx_mem := mem_treeIds_of_listLast0 hr_ne_leaf (P := P) (s := s)
        rw [← hlast'] at hx_mem
        have hx_r : x ∈ (AuxTree.node y ly ry).toList := (mem_treeIds_iff P s (AuxTree.node y ly ry) x).mp hx_mem
        exact (AuxTree.nodup_node_unfold ht.nodup).2.2.2.1 hx_r
  have hinv := ht.sub
  rw [SplayState.SubtreeInv.eq_2] at hinv
  exact ⟨hr_leaf, by rw [hr_leaf] at hinv; simpa [AuxTree.rootId] using hinv.2.2.1⟩

theorem depth_le_of_reaches {par depth : ℕ → ℕ} {active : List ℕ}
    (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x) :
    ∀ k u x, reaches par k u x = true → x ∈ active → depth u ≤ depth x := by
  intro k
  induction k with
  | zero =>
      intro u x hr _
      simp only [reaches, beq_iff_eq] at hr
      subst hr; omega
  | succ k ih =>
      intro u x hr hx
      simp only [reaches] at hr
      by_cases hxu : x = u
      · subst hxu; omega
      · simp only [beq_false_of_ne hxu, Bool.false_eq_true, ↓reduceIte] at hr
        by_cases hpx : par x = 0
        · simp [hpx] at hr
        · simp only [beq_false_of_ne hpx, Bool.false_eq_true, ↓reduceIte] at hr
          have h1 := hdec x hx hpx
          have h2 := ih u (par x) hr (hmem x hx hpx)
          omega

private theorem reaches_step_tail (par : ℕ → ℕ) :
    ∀ k u x, reaches par k u x = true → par u ≠ 0 → reaches par (k + 1) (par u) x = true := by
  intro k
  induction k with
  | zero =>
      intro u x hr hpu
      simp only [reaches, beq_iff_eq] at hr
      subst hr
      by_cases h : x = par x
      · rw [← h]; exact reaches_self par 1 x
      · rw [reaches.eq_2]; simp [h, hpu, reaches_self]
  | succ k ih =>
      intro u x hr hpu
      simp only [reaches] at hr
      by_cases hxu : x = u
      · subst hxu
        by_cases h : x = par x
        · rw [← h]; exact reaches_self par (k + 2) x
        · exact reaches_mono (Nat.le_add_left 1 (k + 1)) (by rw [reaches.eq_2]; simp [h, hpu, reaches_self])
      · simp only [beq_false_of_ne hxu, Bool.false_eq_true, ↓reduceIte] at hr
        by_cases hpx : par x = 0
        · simp [hpx] at hr
        · simp only [beq_false_of_ne hpx, Bool.false_eq_true, ↓reduceIte] at hr
          by_cases hxp : x = par u
          · rw [hxp]; exact reaches_self par (k + 2) (par u)
          · have ih' := ih u (par x) hr hpu
            rw [reaches.eq_2]; simp [hxp, hpx, ih']

theorem reaches_agree_of_mem {f g : ℕ → ℕ} {xs : List ℕ}
    (hag : ∀ y ∈ xs, f y = g y) (hout : ∀ y ∉ xs, f y = 0) :
    ∀ k u x, reaches f k u x = true → u ∈ xs → reaches g k u x = true := by
  intro k
  induction k with
  | zero =>
      intro u x hr _
      simp only [reaches, beq_iff_eq] at hr
      subst hr; exact reaches_self g 0 x
  | succ k ih =>
      intro u x hr hu
      simp only [reaches] at hr
      by_cases hxu : x = u
      · subst hxu; exact reaches_self g (k + 1) x
      · simp only [beq_false_of_ne hxu, Bool.false_eq_true, ↓reduceIte] at hr
        by_cases hfx : f x = 0
        · simp [hfx] at hr
        · simp only [beq_false_of_ne hfx, Bool.false_eq_true, ↓reduceIte] at hr
          have hx_mem : x ∈ xs := by
            by_contra hx_nin
            exact hfx (hout x hx_nin)
          have hgx : g x = f x := (hag x hx_mem).symm
          simp only [reaches, beq_false_of_ne hxu, Bool.false_eq_true, ↓reduceIte, hgx, beq_false_of_ne hfx]
          exact ih u (f x) hr hu

theorem reaches_chainPred_last :
    ∀ (xs : List ℕ) (prev z : ℕ), xs.Nodup → 0 ∉ xs → z ∈ xs →
      reaches (chainPred prev xs) xs.length z (listLast0 xs) = true := by
  intro xs
  induction xs with
  | nil => intro prev z _ _ hz; simp at hz
  | cons a xs ih =>
      intro prev z hnd hz0 hz
      have ha_nin : a ∉ xs := (List.nodup_cons.mp hnd).1
      have hnd_xs : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hxs0 : 0 ∉ xs := fun h => hz0 (List.mem_cons_of_mem _ h)
      have ha0 : a ≠ 0 := fun h => hz0 (h ▸ List.mem_cons_self)
      cases xs with
      | nil =>
          simp only [List.mem_singleton] at hz
          subst hz; simp [listLast0, reaches]
      | cons b rest =>
          have hlast_eq : listLast0 (a :: b :: rest) = listLast0 (b :: rest) := rfl
          rw [hlast_eq]
          have hag : ∀ y ∈ b :: rest, chainPred a (b :: rest) y = chainPred prev (a :: b :: rest) y := by
            intro y hy
            have hya : y ≠ a := fun h => ha_nin (h ▸ hy)
            conv_rhs => rw [chainPred]
            simp [hya]
          have hout : ∀ y ∉ b :: rest, chainPred a (b :: rest) y = 0 := fun y hy =>
            chainPred_eq_zero_of_not_mem hy
          have hsub_reach : ∀ w ∈ b :: rest,
              reaches (chainPred prev (a :: b :: rest)) (b :: rest).length w (listLast0 (b :: rest)) = true := by
            intro w hw
            exact reaches_agree_of_mem hag hout (b :: rest).length w (listLast0 (b :: rest))
              (ih a w hnd_xs hxs0 hw) hw
          rcases List.mem_cons.mp hz with hza | hzm
          · have hb_reach := hsub_reach b List.mem_cons_self
            have hpb : chainPred prev (a :: b :: rest) b = a := by
              have hba : b ≠ a := fun h => ha_nin (h ▸ List.mem_cons_self)
              simp [chainPred, hba]
            rw [List.length_cons, hza]
            have hst := reaches_step_tail (chainPred prev (a :: b :: rest))
              (b :: rest).length b (listLast0 (b :: rest)) hb_reach (by rw [hpb]; exact ha0)
            rwa [hpb] at hst
          · exact reaches_mono (Nat.le_succ _) (hsub_reach z hzm)

theorem reaches_chainPred_head :
    ∀ (xs : List ℕ) (prev z : ℕ), xs.Nodup → 0 ∉ xs → z ∈ xs →
      reaches (chainPred prev xs) xs.length (listHead0 xs) z = true := by
  intro xs
  induction xs with
  | nil => intro prev z _ _ hz; simp at hz
  | cons a xs ih =>
      intro prev z hnd hz0 hz
      have ha_nin : a ∉ xs := (List.nodup_cons.mp hnd).1
      have hnd_xs : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hxs0 : 0 ∉ xs := fun h => hz0 (List.mem_cons_of_mem _ h)
      have ha0 : a ≠ 0 := fun h => hz0 (h ▸ List.mem_cons_self)
      cases xs with
      | nil =>
          simp only [List.mem_singleton] at hz
          subst hz; simp [listHead0, reaches]
      | cons b rest =>
          simp only [listHead0]
          rcases List.mem_cons.mp hz with rfl | hzm
          · exact reaches_self _ _ _
          · have hag : ∀ y ∈ b :: rest, chainPred a (b :: rest) y = chainPred prev (a :: b :: rest) y := by
              intro y hy
              have hya : y ≠ a := fun h => ha_nin (h ▸ hy)
              conv_rhs => rw [chainPred]
              simp [hya]
            have hout : ∀ y ∉ b :: rest, chainPred a (b :: rest) y = 0 := fun y hy =>
              chainPred_eq_zero_of_not_mem hy
            have ih' := reaches_agree_of_mem hag hout (b :: rest).length b z (ih a z hnd_xs hxs0 hzm) List.mem_cons_self
            have hpb : chainPred prev (a :: b :: rest) b = a := by
              have hba : b ≠ a := fun h => ha_nin (h ▸ List.mem_cons_self)
              simp [chainPred, hba]
            rw [List.length_cons]
            have hst := reaches_step_tail (chainPred prev (a :: b :: rest))
              (b :: rest).length b z ih' (by rw [hpb]; exact ha0)
            rwa [hpb] at hst

theorem evalPairs_length {P : LctPayload α σ τ} {s : SplayState α σ τ} :
    ∀ (t : AuxTree) (flip : Bool) (acc : τ),
      (SplayState.evalPairs P s t flip acc).length = t.toList.length
  | .leaf, _, _ => by simp [SplayState.evalPairs, AuxTree.toList]
  | .node _ l r, flip, acc => by
      rw [SplayState.evalPairs.eq_2]
      split_ifs <;> (simp [AuxTree.toList, evalPairs_length l, evalPairs_length r]; try omega)

theorem tree_reaches_head {P : LctPayload α σ τ}
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {t : AuxTree} {z : ℕ} (ht : t ∈ trees) (hz : z ∈ t.toList) :
    reaches (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length
      (listHead0 (treeIds P st.splay t)) z = true := by
  have hnd : (treeIds P st.splay t).Nodup := treeIds_nodup (W.treesInv t ht)
  have h0 : 0 ∉ treeIds P st.splay t := fun h0 => by
    have hm := W.activeValid 0 (List.mem_flatMap.mpr ⟨t, ht, (mem_treeIds_iff P st.splay t 0).mp h0⟩)
    simp [isNode] at hm
  have hz_ids : z ∈ treeIds P st.splay t := (mem_treeIds_iff P st.splay t z).mpr hz
  have hrc := reaches_chainPred_head (treeIds P st.splay t) (st.splay.nodes t.rootId).ppar z hnd h0 hz_ids
  have hag : ∀ y ∈ treeIds P st.splay t,
      chainPred (st.splay.nodes t.rootId).ppar (treeIds P st.splay t) y = inducedSubPar P st.splay trees y :=
    fun y hy => (inducedSubPar_eq_of_mem W.activeNodup ht ((mem_treeIds_iff P st.splay t y).mp hy)).symm
  have hout : ∀ y ∉ treeIds P st.splay t,
      chainPred (st.splay.nodes t.rootId).ppar (treeIds P st.splay t) y = 0 := fun y hy =>
    chainPred_eq_zero_of_not_mem hy
  have hrc' := reaches_agree_of_mem hag hout (treeIds P st.splay t).length
    (listHead0 (treeIds P st.splay t)) z hrc
    ((mem_treeIds_iff P st.splay t (listHead0 (treeIds P st.splay t))).mpr (listHead0_mem_of_ne_nil (W.treesNonEmpty t ht)))
  have hlen : (treeIds P st.splay t).length ≤ (trees.flatMap AuxTree.toList).length := by
    have h1 := tree_length_le_active ht
    have h2 : (treeIds P st.splay t).length = t.toList.length := by simp [treeIds, evalPairs_length]
    omega
  exact reaches_mono hlen hrc'

/-! ### `forestPairs` preservation -/

private theorem flatMap_congr_mem {β γ : Type*} {xs : List β} {f g : β → List γ}
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.flatMap_cons]
      rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem forestPairs_perm_cons_erase {P : LctPayload α σ τ} {s₁ s₂ : SplayState α σ τ}
    {ts ts' : List AuxTree} {t t' : AuxTree}
    (ht : t ∈ ts) (hts' : ts' = t' :: ts.erase t)
    (hev : SplayState.evalPairs P s₂ t' false P.idTag = SplayState.evalPairs P s₁ t false P.idTag)
    (hout : ∀ u ∉ t.toList, s₂.nodes u = s₁.nodes u)
    (hnd : (ts.flatMap AuxTree.toList).Nodup) :
    (forestPairs P s₂ ts').Perm (forestPairs P s₁ ts) := by
  have hperm_ts := List.perm_cons_erase ht
  have hdisj := erase_flatMap_disjoint_of_nodup ht hnd
  have heq_er : (ts.erase t).flatMap (fun c => SplayState.evalPairs P s₂ c false P.idTag) =
      (ts.erase t).flatMap (fun c => SplayState.evalPairs P s₁ c false P.idTag) :=
    flatMap_congr_mem (fun c hc => SplayState.evalPairs_agree P (fun w hw =>
      hout w (fun hm => hdisj w (List.mem_flatMap.mpr ⟨c, hc, hw⟩) hm)) false P.idTag)
  dsimp only [forestPairs]
  rw [hts', List.flatMap_cons, hev, heq_er]
  change ((t :: ts.erase t).flatMap (fun c => SplayState.evalPairs P s₁ c false P.idTag)).Perm
    (ts.flatMap (fun c => SplayState.evalPairs P s₁ c false P.idTag))
  exact List.Perm.flatMap_right _ hperm_ts.symm

theorem forestPairs_perm_detachRight {P : LctPayload α σ τ} (hL : P.Laws)
    {s : SplayState α σ τ} {ts : List AuxTree} {x : ℕ} {L R : AuxTree}
    (ht : AuxTree.node x L R ∈ ts) (ht_inv : SplayState.TreeInv P s (AuxTree.node x L R))
    (hrev : (s.nodes x).rev = false) (htag : (s.nodes x).tag = P.idTag)
    (hnd : (ts.flatMap AuxTree.toList).Nodup) :
    let s' := SplayState.detachRight P s x
    let ts' := if R = AuxTree.leaf then ts else AuxTree.node x L AuxTree.leaf :: R :: ts.erase (AuxTree.node x L R)
    (forestPairs P s' ts').Perm (forestPairs P s ts) := by
  intro s' ts'
  have hdet := SplayState.detachRight_preserves hL ht_inv hrev htag
  rcases hdet with ⟨_, _, _, _, _, hev_L, hev_R, hout⟩
  have hev_orig := evalPairs_of_rev_false hL hrev htag (l := L) (r := R)
  by_cases hR : R = AuxTree.leaf
  · subst hR
    dsimp only [ts']
    simp only [↓reduceIte]
    refine List.Perm.of_eq ?_
    exact flatMap_congr_mem (fun c hc => by
      by_cases hct : c = AuxTree.node x L AuxTree.leaf
      · subst hct; rw [hev_L, hev_orig]; simp [SplayState.evalPairs]
      · have hdisj := erase_flatMap_disjoint_of_nodup ht hnd
        have hc_er : c ∈ ts.erase (AuxTree.node x L AuxTree.leaf) := (List.mem_erase_of_ne hct).mpr hc
        exact SplayState.evalPairs_agree P (fun w hw =>
          hout w (fun hm => hdisj w (List.mem_flatMap.mpr ⟨c, hc_er, hw⟩) hm)) false P.idTag)
  · dsimp only [ts']
    simp only [eq_false hR, ↓reduceIte]
    have hdisj := erase_flatMap_disjoint_of_nodup ht hnd
    have heq_er : (ts.erase (AuxTree.node x L R)).flatMap (fun c => SplayState.evalPairs P s' c false P.idTag) =
        (ts.erase (AuxTree.node x L R)).flatMap (fun c => SplayState.evalPairs P s c false P.idTag) :=
      flatMap_congr_mem (fun c hc => SplayState.evalPairs_agree P (fun w hw =>
        hout w (fun hm => hdisj w (List.mem_flatMap.mpr ⟨c, hc, hw⟩) hm)) false P.idTag)
    dsimp only [forestPairs]
    rw [List.flatMap_cons, List.flatMap_cons, hev_L, (hev_R hR).2.2, heq_er]
    have hcat : (SplayState.evalPairs P s L false P.idTag ++ [(x, (s.nodes x).val)]) ++
        (SplayState.evalPairs P s R false P.idTag ++
          (ts.erase (AuxTree.node x L R)).flatMap (fun c => SplayState.evalPairs P s c false P.idTag)) =
        ((AuxTree.node x L R :: ts.erase (AuxTree.node x L R)).flatMap
          (fun c => SplayState.evalPairs P s c false P.idTag)) := by
      rw [List.flatMap_cons, hev_orig]; simp only [List.append_assoc]
    rw [hcat]
    exact List.Perm.flatMap_right _ (List.perm_cons_erase ht).symm

theorem forestPairs_perm_attachRight {P : LctPayload α σ τ} (hL : P.Laws)
    {s : SplayState α σ τ} {ts : List AuxTree} {u : ℕ} {Lu tx : AuxTree}
    (hne_mem : ∀ c ∈ ts, c ≠ AuxTree.leaf)
    (hu : AuxTree.node u Lu AuxTree.leaf ∈ ts) (htx : tx ∈ ts)
    (hne : AuxTree.node u Lu AuxTree.leaf ≠ tx)
    (hu_inv : SplayState.TreeInv P s (AuxTree.node u Lu AuxTree.leaf))
    (hrev : (s.nodes u).rev = false) (htag : (s.nodes u).tag = P.idTag)
    (htx_inv : SplayState.TreeInv P s tx) (htx_ne : tx ≠ AuxTree.leaf)
    (hnd : (ts.flatMap AuxTree.toList).Nodup) :
    let x := tx.rootId
    let s' := SplayState.attachRight P s u x
    let ts' := AuxTree.node u Lu tx :: (ts.erase (AuxTree.node u Lu AuxTree.leaf)).erase tx
    (forestPairs P s' ts').Perm (forestPairs P s ts) := by
  intro x s' ts'
  have htx_er : tx ∈ ts.erase (AuxTree.node u Lu AuxTree.leaf) :=
    (List.mem_erase_of_ne hne.symm).mpr htx
  have hperm_ts : ts.Perm (AuxTree.node u Lu AuxTree.leaf :: tx ::
      (ts.erase (AuxTree.node u Lu AuxTree.leaf)).erase tx) :=
    (List.perm_cons_erase hu).trans (List.Perm.cons _ (List.perm_cons_erase htx_er))
  have hdisj_utx : ∀ a ∈ (AuxTree.node u Lu AuxTree.leaf).toList, a ∉ tx.toList := fun a ha hm =>
    hne (flatMap_mem_unique hnd hu htx ha hm)
  have hatt := SplayState.attachRight_preserves hL hu_inv hrev htag htx_inv htx_ne rfl hdisj_utx
  rcases hatt with ⟨_, _, _, _, hev_new, hout⟩
  have hnd_both := hperm_ts.nodup_iff.mp (nodup_of_flatMap_nodup ts hnd hne_mem)
  have heq_er : ((ts.erase (AuxTree.node u Lu AuxTree.leaf)).erase tx).flatMap
        (fun c => SplayState.evalPairs P s' c false P.idTag) =
      ((ts.erase (AuxTree.node u Lu AuxTree.leaf)).erase tx).flatMap
        (fun c => SplayState.evalPairs P s c false P.idTag) := by
    refine flatMap_congr_mem (fun c hc => SplayState.evalPairs_agree P (fun w hw => ?_) false P.idTag)
    have hc_er1 : c ∈ ts.erase (AuxTree.node u Lu AuxTree.leaf) := List.mem_of_mem_erase hc
    have hc_ts : c ∈ ts := List.mem_of_mem_erase hc_er1
    have hcu : c ≠ AuxTree.node u Lu AuxTree.leaf := fun h =>
      (List.nodup_cons.mp hnd_both).1 (List.mem_cons_of_mem _
        ((congrArg (· ∈ (ts.erase (AuxTree.node u Lu AuxTree.leaf)).erase tx) h).mp hc))
    have hctx : c ≠ tx := fun h =>
      (List.nodup_cons.mp (List.nodup_cons.mp hnd_both).2).1 (h ▸ hc)
    refine hout w (fun hm => ?_)
    simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hm
    rcases hm with (hl | rfl) | hr
    · exact hcu (flatMap_mem_unique hnd hu hc_ts (by simp [AuxTree.toList, hl]) hw).symm
    · exact hcu (flatMap_mem_unique hnd hu hc_ts (by simp [AuxTree.toList]) hw).symm
    · exact hctx (flatMap_mem_unique hnd htx hc_ts hr hw).symm
  have hev_u := evalPairs_of_rev_false hL hrev htag (l := Lu) (r := AuxTree.leaf)
  dsimp only [forestPairs, ts']
  rw [List.flatMap_cons, hev_new, heq_er]
  have hev_u_nil : SplayState.evalPairs P s (AuxTree.node u Lu AuxTree.leaf) false P.idTag =
      SplayState.evalPairs P s Lu false P.idTag ++ [(u, (s.nodes u).val)] := by
    simpa [SplayState.evalPairs.eq_1] using hev_u
  have hcat : (SplayState.evalPairs P s Lu false P.idTag ++ [(u, (s.nodes u).val)] ++
        SplayState.evalPairs P s tx false P.idTag) ++
      ((ts.erase (AuxTree.node u Lu AuxTree.leaf)).erase tx).flatMap
        (fun c => SplayState.evalPairs P s c false P.idTag) =
      ((AuxTree.node u Lu AuxTree.leaf :: tx ::
        (ts.erase (AuxTree.node u Lu AuxTree.leaf)).erase tx).flatMap
          (fun c => SplayState.evalPairs P s c false P.idTag)) := by
    rw [List.flatMap_cons, List.flatMap_cons, hev_u_nil]; simp only [List.append_assoc]
  rw [hcat]
  exact List.Perm.flatMap_right _ hperm_ts.symm

/-! ### `lctSplayTree_spec` -/

theorem reaches_congr {f g : ℕ → ℕ} (h : ∀ y, f y = g y) :
    ∀ k u x, reaches f k u x = reaches g k u x := by
  intro k
  induction k with
  | zero => intro u x; rfl
  | succ k ih =>
      intro u x
      simp only [reaches, h x]
      split_ifs
      · rfl
      · rfl
      · exact ih u (g x)

theorem lctSplayTree_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {t : AuxTree} {x : ℕ} (ht : t ∈ trees) (hx : x ∈ t.toList) :
    let d := splayDepth st.splay (2 * st.n + 1) x
    let s' := SplayState.splay P st.splay (2 * st.n + 1) x
    let st' : LctState α σ τ := { n := st.n, splay := s', freeHead := st.freeHead }
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    let v := vSize P st.splay active par trees
    ∃ t',
      let trees' := t' :: trees.erase t
      let active' := trees'.flatMap AuxTree.toList
      let par' := inducedSubPar P s' trees'
      let v' := vSize P s' active' par' trees'
      t' ≠ AuxTree.leaf ∧
        t'.rootId = x ∧
        t'.toList.Perm t.toList ∧
        (s'.nodes x).ppar = (st.splay.nodes t.rootId).ppar ∧
        (s'.nodes x).rev = false ∧
        (s'.nodes x).tag = P.idTag ∧
        LctInvWith P st' trees' freeList depth ∧
        heavyCount P st' = heavyCount P st ∧
        (forestPairs P s' trees').Perm (forestPairs P st.splay trees) ∧
        (∀ z, par' z = par z) ∧
        (∀ u ∉ t.toList, s'.nodes u = st.splay.nodes u) ∧
        SplayState.evalPairs P s' t' false P.idTag = SplayState.evalPairs P st.splay t false P.idTag ∧
        t'.treeSize v = t.treeSize v ∧
        t'.rank v' = t'.rank v ∧
        d / 2 + sumTreePhi P st' + 3 * (t.findSubtree x).rank v ≤ sumTreePhi P st + 3 * t'.rank v := by
  intro d s' st' active par v
  have hact_le : active.length ≤ 2 * st.n :=
    active_length_le_two_mul W.activeNodup W.activeValid
  have hdep_lt : t.depthOf x < 2 * st.n + 1 := by
    have h1 := depthOf_lt_length hx
    have h2 := tree_length_le_active ht
    dsimp only [active] at hact_le
    omega
  have hd_eq : d = t.depthOf x := splayDepth_eq_depthOf (W.treesInv t ht) hx hdep_lt
  rcases SplayState.splay_preserves_and_phi hL (W.treesInv t ht) hx hdep_lt with
    ⟨t', ht'_inv, ht'_ne, ht'_rt, ht'_perm, hev, hpp, hrev, htag, hout, hpot⟩
  refine ⟨t', ?_⟩
  have hrep := replaceSameIds_spec W ht ht'_ne ht'_inv ht'_perm hev (by rw [ht'_rt]; exact hpp) hout
  rcases hrep with ⟨hW', hH', hPhi_eq, hpar_mem⟩
  have hpar_all : ∀ z, inducedSubPar P s' (t' :: trees.erase t) z = par z := by
    intro z
    by_cases hz : z ∈ (t' :: trees.erase t).flatMap AuxTree.toList
    · exact hpar_mem z hz
    · have hz_old : z ∉ active := fun hm =>
        hz ((flatMap_perm_of_replace ht ht'_perm).symm.mem_iff.mp hm)
      rw [inducedSubPar_eq_zero_of_not_mem hz]
      dsimp only [par]
      rw [inducedSubPar_eq_zero_of_not_mem hz_old]
  have hpairs := forestPairs_perm_cons_erase ht rfl hev hout W.activeNodup
  have htsz_eq := (hpot v).1
  have hphi_splay := (hpot v).2
  have hrank_v' : t'.rank (vSize P s' ((t' :: trees.erase t).flatMap AuxTree.toList)
      (inducedSubPar P s' (t' :: trees.erase t)) (t' :: trees.erase t)) = t'.rank v := by
    have h_v' := treeSize_vSize_eq_repSize hW' (by simp : t' ∈ t' :: trees.erase t)
    have h_v := treeSize_vSize_eq_repSize W ht
    have h_ids : treeIds P s' t' = treeIds P st.splay t := treeIds_eq_of_evalPairs hev
    have hrep_eq : repSize ((t' :: trees.erase t).flatMap AuxTree.toList)
          (inducedSubPar P s' (t' :: trees.erase t)) (listHead0 (treeIds P s' t')) =
        repSize active par (listHead0 (treeIds P st.splay t)) := by
      rw [h_ids]
      dsimp only [repSize]
      have hact_perm := flatMap_perm_of_replace ht ht'_perm
      have hlen_eq : (List.flatMap AuxTree.toList (t' :: trees.erase t)).length = active.length :=
        hact_perm.length_eq
      have hfilt_congr : ((t' :: trees.erase t).flatMap AuxTree.toList).filter
            (fun w => reaches (inducedSubPar P s' (t' :: trees.erase t))
              (List.flatMap AuxTree.toList (t' :: trees.erase t)).length (listHead0 (treeIds P st.splay t)) w) =
          ((t' :: trees.erase t).flatMap AuxTree.toList).filter
            (fun w => reaches par active.length (listHead0 (treeIds P st.splay t)) w) :=
        List.filter_congr (fun w _ => by
          rw [hlen_eq, reaches_congr hpar_all])
      rw [hfilt_congr, (hact_perm.filter _).length_eq]
    have hsz_v' : t'.treeSize (vSize P s' ((t' :: trees.erase t).flatMap AuxTree.toList)
        (inducedSubPar P s' (t' :: trees.erase t)) (t' :: trees.erase t)) = t'.treeSize v := by
      rw [h_v', hrep_eq, ← h_v, htsz_eq]
    simp only [AuxTree.rank, hsz_v']
  refine ⟨ht'_ne, ht'_rt, ht'_perm, hpp, hrev, htag, hW', hH', hpairs, hpar_all, hout, hev, htsz_eq, hrank_v', ?_⟩
  rw [hd_eq]
  have hPhi_eq' : sumTreePhi P st' + t.treePhi v = sumTreePhi P st + t'.treePhi v := hPhi_eq
  have hphi_splay' : t'.treePhi v + 3 * (t.findSubtree x).rank v + t.depthOf x / 2 ≤
      t.treePhi v + 3 * t'.rank v := hphi_splay
  omega

end

end MinCostFlow.LinkCut
