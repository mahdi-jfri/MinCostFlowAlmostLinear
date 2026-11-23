module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import Mathlib.Data.Finset.Sort

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Induced subgraphs, vertex relabeling, and degree counting

This file provides graph infrastructure over `Cited.Graph` for Algorithm 4:
1. Degree, volume, and cut identities (`volIn X X = 2 * (G.inside X).length`, edge counting via
   vertex degrees, `maxDeg`).
2. Self-loop stripping (`stripLoops`), separating self-loops from `J` before `Decompose`.
3. Induced subgraphs on vertex subsets `X : Finset ℕ` (`inducedSubgraph`), re-indexing `X` onto
   `{0, …, |X| - 1}` via `X.sort (· ≤ ·)` while preserving degrees, cuts, volumes, conductance
   expansion, and walks.
4. Decomposition level degree/edge-sum lemmas for `DecomposeTool`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## General list, degree, volume, and maximum-degree lemmas -/

private theorem map_filter_range_getD {α : Type*} (L : List α) (d : α) (p : α → Bool) :
    ((List.range L.length).filter (fun j => p (L.getD j d))).map (fun j => L.getD j d) =
      L.filter p := by
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append,
        List.map_append, List.filter_append]
    have hprefix : (List.range xs.length).filter (fun j => p ((xs ++ [x]).getD j d)) =
        (List.range xs.length).filter (fun j => p (xs.getD j d)) := by
      refine List.filter_congr fun j hj => ?_
      rw [List.mem_range] at hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    have hmap : ((List.range xs.length).filter (fun j => p ((xs ++ [x]).getD j d))).map
        (fun j => (xs ++ [x]).getD j d) =
        ((List.range xs.length).filter (fun j => p (xs.getD j d))).map (fun j => xs.getD j d) := by
      rw [hprefix]
      refine List.map_congr_left fun j hj => ?_
      have hj' : j < xs.length := List.mem_range.mp (List.mem_filter.mp hj).1
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj']
    rw [hmap, ih]
    have hlast : (xs ++ [x]).getD xs.length d = x := by simp [List.getD_eq_getElem?_getD]
    simp only [List.filter_cons, List.filter_nil, hlast]
    cases p x <;> simp

/-- Helper converting the length of a filtered list into a filtered `Finset.range` cardinality. -/
theorem list_filter_length_eq_range_card {α : Type*} (l : List α) (d : α) (p : α → Bool) :
    (l.filter p).length =
      ((Finset.range l.length).filter (fun j => p (l.getD j d))).card := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    rw [List.filter_append, List.length_append, List.length_append, List.length_singleton,
        Finset.range_add_one, Finset.filter_insert, ih]
    have hlast : (xs ++ [x]).getD xs.length d = x := by
      simp [List.getD_eq_getElem?_getD]
    have hprefix : ∀ j ∈ Finset.range xs.length, (xs ++ [x]).getD j d = xs.getD j d := by
      intro j hj
      rw [Finset.mem_range] at hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    have hcong : (Finset.range xs.length).filter (fun j => p ((xs ++ [x]).getD j d)) =
        (Finset.range xs.length).filter (fun j => p (xs.getD j d)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun ⟨hj, hp⟩ => ⟨hj, by rwa [← hprefix j (Finset.mem_range.mpr hj)]⟩,
             fun ⟨hj, hp⟩ => ⟨hj, by rwa [hprefix j (Finset.mem_range.mpr hj)]⟩⟩
    rw [hlast]
    cases hpx : p x
    · simp only [List.filter_cons, List.filter_nil, hpx, Bool.false_eq_true, ↓reduceIte,
        List.length_nil, add_zero, hcong]
    · have hnotin : xs.length ∉ (Finset.range xs.length).filter (fun j => p (xs.getD j d)) := by
        simp [Finset.mem_filter, Finset.mem_range]
      simp only [List.filter_cons, List.filter_nil, hpx, ↓reduceIte, List.length_singleton, hcong,
        Finset.card_insert_of_notMem hnotin]

private theorem filter_sublist_filter {α : Type*} {p q : α → Bool} (l : List α)
    (hpq : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).Sublist (l.filter q) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih (fun y hy => hpq y (List.mem_cons_of_mem x hy))
    simp only [List.filter_cons]
    cases hpx : p x <;> cases hqx : q x
    · exact ih'
    · exact List.Sublist.cons _ ih'
    · exact absurd (hpq x List.mem_cons_self hpx) (by simp [hqx])
    · exact List.Sublist.cons_cons _ ih'

/-- Maximum degree `Δ_max(G)` of a graph `G` (`prelims.tex`, Section 2, page 5). -/
def maxDeg (G : Graph) : ℕ :=
  (Finset.range G.n).fold max 0 G.deg

theorem deg_le_maxDeg {G : Graph} {v : ℕ} (hv : v < G.n) : G.deg v ≤ maxDeg G :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨v, Finset.mem_range.mpr hv, le_rfl⟩)

theorem maxDeg_le_iff {G : Graph} {B : ℕ} :
    maxDeg G ≤ B ↔ ∀ v < G.n, G.deg v ≤ B := by
  simp [maxDeg, Finset.fold_max_le, Finset.mem_range]

theorem inside_verts_eq_edges {G : Graph} (hG : G.IsValid) : G.inside G.verts = G.edges := by
  unfold Graph.inside
  rw [List.filter_eq_self]
  intro e he
  have hv := hG e he
  simp [Graph.verts, Finset.mem_range, hv.1, hv.2]

theorem deg_eq_filter_edges {G : Graph} (hG : G.IsValid) (v : ℕ) :
    G.deg v = (G.edges.filter fun e => e.1 = v).length + (G.edges.filter fun e => e.2 = v).length := by
  simp [Graph.deg, Graph.degIn, inside_verts_eq_edges hG]

private theorem sum_filter_fst_eq_length (L : List (ℕ × ℕ)) (X : Finset ℕ)
    (hL : ∀ e ∈ L, e.1 ∈ X) :
    ∑ v ∈ X, (L.filter fun e => decide (e.1 = v)).length = L.length := by
  induction L with
  | nil => simp
  | cons e es ih =>
    have he : e.1 ∈ X := hL e List.mem_cons_self
    have hes : ∀ e' ∈ es, e'.1 ∈ X := fun e' he' => hL e' (List.mem_cons_of_mem e he')
    have ih' := ih hes
    simp only [List.filter_cons]
    simp_rw [apply_ite List.length, List.length_cons]
    have hsum : ∑ v ∈ X, (if decide (e.1 = v) = true then (es.filter fun e' => decide (e'.1 = v)).length + 1
        else (es.filter fun e' => decide (e'.1 = v)).length) =
        ∑ v ∈ X, ((es.filter fun e' => decide (e'.1 = v)).length + if e.1 = v then 1 else 0) := by
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases h : e.1 = v <;> simp [h]
    rw [hsum, Finset.sum_add_distrib, ih']
    simp [he]

private theorem sum_filter_snd_eq_length (L : List (ℕ × ℕ)) (X : Finset ℕ)
    (hL : ∀ e ∈ L, e.2 ∈ X) :
    ∑ v ∈ X, (L.filter fun e => decide (e.2 = v)).length = L.length := by
  induction L with
  | nil => simp
  | cons e es ih =>
    have he : e.2 ∈ X := hL e List.mem_cons_self
    have hes : ∀ e' ∈ es, e'.2 ∈ X := fun e' he' => hL e' (List.mem_cons_of_mem e he')
    have ih' := ih hes
    simp only [List.filter_cons]
    simp_rw [apply_ite List.length, List.length_cons]
    have hsum : ∑ v ∈ X, (if decide (e.2 = v) = true then (es.filter fun e' => decide (e'.2 = v)).length + 1
        else (es.filter fun e' => decide (e'.2 = v)).length) =
        ∑ v ∈ X, ((es.filter fun e' => decide (e'.2 = v)).length + if e.2 = v then 1 else 0) := by
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases h : e.2 = v <;> simp [h]
    rw [hsum, Finset.sum_add_distrib, ih']
    simp [he]

theorem volIn_self_eq_two_mul_inside (G : Graph) (X : Finset ℕ) :
    G.volIn X X = 2 * (G.inside X).length := by
  unfold Graph.volIn Graph.degIn
  rw [Finset.sum_add_distrib]
  have h1 : ∀ e ∈ G.inside X, e.1 ∈ X := fun e he => by
    simp only [Graph.inside, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at he
    exact he.2.1
  have h2 : ∀ e ∈ G.inside X, e.2 ∈ X := fun e he => by
    simp only [Graph.inside, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at he
    exact he.2.2
  rw [sum_filter_fst_eq_length _ X h1, sum_filter_snd_eq_length _ X h2]
  omega

theorem vol_verts_eq_two_mul_m {G : Graph} (hG : G.IsValid) :
    G.vol G.verts = 2 * G.m := by
  unfold Graph.vol Graph.m
  rw [volIn_self_eq_two_mul_inside, inside_verts_eq_edges hG]

theorem degIn_mono_right {G : Graph} {X Y : Finset ℕ} (hXY : X ⊆ Y) (v : ℕ) :
    G.degIn X v ≤ G.degIn Y v := by
  unfold Graph.degIn Graph.inside
  rw [List.filter_filter, List.filter_filter, List.filter_filter, List.filter_filter]
  have hp1 : ∀ e ∈ G.edges, (decide (e.1 = v) && (decide (e.1 ∈ X) && decide (e.2 ∈ X))) = true →
      (decide (e.1 = v) && (decide (e.1 ∈ Y) && decide (e.2 ∈ Y))) = true := by
    intro e _ h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨h.1, hXY h.2.1, hXY h.2.2⟩
  have hp2 : ∀ e ∈ G.edges, (decide (e.2 = v) && (decide (e.1 ∈ X) && decide (e.2 ∈ X))) = true →
      (decide (e.2 = v) && (decide (e.1 ∈ Y) && decide (e.2 ∈ Y))) = true := by
    intro e _ h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨h.1, hXY h.2.1, hXY h.2.2⟩
  exact Nat.add_le_add
    (List.Sublist.length_le (filter_sublist_filter G.edges hp1))
    (List.Sublist.length_le (filter_sublist_filter G.edges hp2))

theorem degIn_eq_deg_of_closed {G : Graph} {X : Finset ℕ} (hG : G.IsValid)
    (hclosed : ∀ e ∈ G.edges, e.1 ∈ X ↔ e.2 ∈ X) {v : ℕ} (hv : v ∈ X) :
    G.degIn X v = G.deg v := by
  unfold Graph.deg Graph.degIn
  rw [inside_verts_eq_edges hG, Graph.inside, List.filter_filter, List.filter_filter]
  have h1 : (G.edges.filter fun e => decide (e.1 = v) && (decide (e.1 ∈ X) && decide (e.2 ∈ X))) =
      G.edges.filter fun e => decide (e.1 = v) := by
    refine List.filter_congr fun e he => ?_
    by_cases he1 : e.1 = v
    · have hex1 : e.1 ∈ X := he1 ▸ hv
      have hex2 : e.2 ∈ X := (hclosed e he).mp hex1
      simp [he1, hv, hex2]
    · simp [he1]
  have h2 : (G.edges.filter fun e => decide (e.2 = v) && (decide (e.1 ∈ X) && decide (e.2 ∈ X))) =
      G.edges.filter fun e => decide (e.2 = v) := by
    refine List.filter_congr fun e he => ?_
    by_cases he2 : e.2 = v
    · have hex2 : e.2 ∈ X := he2 ▸ hv
      have hex1 : e.1 ∈ X := (hclosed e he).mpr hex2
      simp [he2, hv, hex1]
    · simp [he2]
  rw [h1, h2]

theorem volIn_subset_le {G : Graph} {X S : Finset ℕ} (hS : S ⊆ X) :
    G.volIn X S ≤ G.volIn X X :=
  Finset.sum_le_sum_of_subset hS

/-- Count of edges in `E_idx ⊆ range G.m` having both ends in `X` and at least one end in `S`
is at most `G.volIn X S`. -/
theorem card_edges_touching_le_volIn (G : Graph) (X S E_idx : Finset ℕ)
    (hE : E_idx ⊆ Finset.range G.m)
    (hX : ∀ j ∈ E_idx, (G.edges.getD j (0, 0)).1 ∈ X ∧ (G.edges.getD j (0, 0)).2 ∈ X)
    (hS : ∀ j ∈ E_idx, (G.edges.getD j (0, 0)).1 ∈ S ∨ (G.edges.getD j (0, 0)).2 ∈ S) :
    E_idx.card ≤ G.volIn X S := by
  have hsplit : E_idx ⊆
      E_idx.filter (fun j => (G.edges.getD j (0, 0)).1 ∈ S) ∪
      E_idx.filter (fun j => (G.edges.getD j (0, 0)).2 ∈ S) := by
    intro j hj
    rcases hS j hj with h1 | h2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj, h2⟩)
  have hc1 : (E_idx.filter (fun j => (G.edges.getD j (0, 0)).1 ∈ S)).card ≤
      ∑ v ∈ S, ((G.inside X).filter fun e => e.1 = v).length := by
    have hsub : E_idx.filter (fun j => (G.edges.getD j (0, 0)).1 ∈ S) ⊆
        S.biUnion fun v => (Finset.range G.m).filter
          (fun j => (G.edges.getD j (0, 0)).1 ∈ X ∧ (G.edges.getD j (0, 0)).2 ∈ X ∧
            (G.edges.getD j (0, 0)).1 = v) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      refine Finset.mem_biUnion.mpr ⟨(G.edges.getD j (0, 0)).1, hj.2, ?_⟩
      exact Finset.mem_filter.mpr ⟨hE hj.1, (hX j hj.1).1, (hX j hj.1).2, rfl⟩
    calc (E_idx.filter (fun j => (G.edges.getD j (0, 0)).1 ∈ S)).card
        ≤ (S.biUnion fun v => (Finset.range G.m).filter
            (fun j => (G.edges.getD j (0, 0)).1 ∈ X ∧ (G.edges.getD j (0, 0)).2 ∈ X ∧
              (G.edges.getD j (0, 0)).1 = v)).card := Finset.card_le_card hsub
      _ ≤ ∑ v ∈ S, ((Finset.range G.m).filter
            (fun j => (G.edges.getD j (0, 0)).1 ∈ X ∧ (G.edges.getD j (0, 0)).2 ∈ X ∧
              (G.edges.getD j (0, 0)).1 = v)).card := Finset.card_biUnion_le
      _ = ∑ v ∈ S, ((G.inside X).filter fun e => e.1 = v).length := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Graph.inside, List.filter_filter, list_filter_length_eq_range_card _ (0, 0)]
          congr 1; ext j
          simp [Graph.m, Bool.and_eq_true, and_comm, and_left_comm]
  have hc2 : (E_idx.filter (fun j => (G.edges.getD j (0, 0)).2 ∈ S)).card ≤
      ∑ v ∈ S, ((G.inside X).filter fun e => e.2 = v).length := by
    have hsub : E_idx.filter (fun j => (G.edges.getD j (0, 0)).2 ∈ S) ⊆
        S.biUnion fun v => (Finset.range G.m).filter
          (fun j => (G.edges.getD j (0, 0)).1 ∈ X ∧ (G.edges.getD j (0, 0)).2 ∈ X ∧
            (G.edges.getD j (0, 0)).2 = v) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      refine Finset.mem_biUnion.mpr ⟨(G.edges.getD j (0, 0)).2, hj.2, ?_⟩
      exact Finset.mem_filter.mpr ⟨hE hj.1, (hX j hj.1).1, (hX j hj.1).2, rfl⟩
    calc (E_idx.filter (fun j => (G.edges.getD j (0, 0)).2 ∈ S)).card
        ≤ (S.biUnion fun v => (Finset.range G.m).filter
            (fun j => (G.edges.getD j (0, 0)).1 ∈ X ∧ (G.edges.getD j (0, 0)).2 ∈ X ∧
              (G.edges.getD j (0, 0)).2 = v)).card := Finset.card_le_card hsub
      _ ≤ ∑ v ∈ S, ((Finset.range G.m).filter
            (fun j => (G.edges.getD j (0, 0)).1 ∈ X ∧ (G.edges.getD j (0, 0)).2 ∈ X ∧
              (G.edges.getD j (0, 0)).2 = v)).card := Finset.card_biUnion_le
      _ = ∑ v ∈ S, ((G.inside X).filter fun e => e.2 = v).length := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Graph.inside, List.filter_filter, list_filter_length_eq_range_card _ (0, 0)]
          congr 1; ext j
          simp [Graph.m, Bool.and_eq_true, and_comm, and_left_comm]
  unfold Graph.volIn Graph.degIn
  rw [Finset.sum_add_distrib]
  calc E_idx.card
      ≤ (E_idx.filter (fun j => (G.edges.getD j (0, 0)).1 ∈ S) ∪
          E_idx.filter (fun j => (G.edges.getD j (0, 0)).2 ∈ S)).card := Finset.card_le_card hsplit
    _ ≤ (E_idx.filter (fun j => (G.edges.getD j (0, 0)).1 ∈ S)).card +
        (E_idx.filter (fun j => (G.edges.getD j (0, 0)).2 ∈ S)).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add hc1 hc2

theorem card_edges_touching_le_vol (G : Graph) (S E_idx : Finset ℕ) (hG : G.IsValid)
    (hE : E_idx ⊆ Finset.range G.m)
    (hS : ∀ j ∈ E_idx, (G.edges.getD j (0, 0)).1 ∈ S ∨ (G.edges.getD j (0, 0)).2 ∈ S) :
    E_idx.card ≤ G.vol S := by
  apply card_edges_touching_le_volIn G G.verts S E_idx hE _ hS
  intro j hj
  have hjm : j < G.m := Finset.mem_range.mp (hE hj)
  have hmem : G.edges.getD j (0, 0) ∈ G.edges := by
    rw [List.getD_eq_getElem _ _ hjm]
    exact List.getElem_mem hjm
  have hv := hG _ hmem
  exact ⟨Finset.mem_range.mpr hv.1, Finset.mem_range.mpr hv.2⟩

/-! ## Self-loop stripping -/

/-- Edge indices of non-loop edges of `J`. -/
def nonloopIndices (J : Graph) : List ℕ :=
  (List.range J.m).filter fun j => decide (let e := J.edges.getD j (0, 0); e.1 ≠ e.2)

/-- The loopless multigraph obtained by keeping only non-loop edges of `J`. -/
def stripLoops (J : Graph) : Graph :=
  ⟨J.n, (nonloopIndices J).map fun j => J.edges.getD j (0, 0)⟩

theorem nonloopIndices_nodup (J : Graph) : (nonloopIndices J).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem mem_nonloopIndices {J : Graph} {j : ℕ} :
    j ∈ nonloopIndices J ↔ j < J.m ∧ (J.edges.getD j (0, 0)).1 ≠ (J.edges.getD j (0, 0)).2 := by
  simp [nonloopIndices, List.mem_filter, List.mem_range]

theorem stripLoops_edges_eq (J : Graph) :
    (stripLoops J).edges = J.edges.filter (fun e => decide (e.1 ≠ e.2)) :=
  map_filter_range_getD J.edges (0, 0) (fun e => decide (e.1 ≠ e.2))

theorem stripLoops_isValid {J : Graph} (hJ : J.IsValid) : (stripLoops J).IsValid := by
  intro e he
  rw [stripLoops_edges_eq] at he
  exact hJ e (List.mem_filter.mp he).1

theorem stripLoops_isLoopless (J : Graph) : (stripLoops J).IsLoopless := by
  intro e he
  rw [stripLoops_edges_eq] at he
  simpa using (List.mem_filter.mp he).2

theorem stripLoops_m_le (J : Graph) : (stripLoops J).m ≤ J.m := by
  unfold Graph.m
  rw [stripLoops_edges_eq]
  exact List.length_filter_le _ _

theorem stripLoops_deg_le {J : Graph} (hJ : J.IsValid) (v : ℕ) :
    (stripLoops J).deg v ≤ J.deg v := by
  rw [deg_eq_filter_edges (stripLoops_isValid hJ) v, deg_eq_filter_edges hJ v, stripLoops_edges_eq]
  exact Nat.add_le_add
    (List.Sublist.length_le (List.Sublist.filter _ List.filter_sublist))
    (List.Sublist.length_le (List.Sublist.filter _ List.filter_sublist))

theorem stripLoops_maxDeg_le {J : Graph} (hJ : J.IsValid) :
    maxDeg (stripLoops J) ≤ maxDeg J := by
  rw [maxDeg_le_iff]
  intro v hv
  exact le_trans (stripLoops_deg_le hJ v) (deg_le_maxDeg hv)

/-! ## Induced subgraphs on `X : Finset ℕ` -/

/-- The sorted list of vertices of `X`. -/
def vertsOf (X : Finset ℕ) : List ℕ :=
  X.sort (· ≤ ·)

/-- Original edge indices of `G` with both endpoints in `X`. -/
def insideIndices (G : Graph) (X : Finset ℕ) : List ℕ :=
  (List.range G.m).filter fun j =>
    decide (let e := G.edges.getD j (0, 0); e.1 ∈ X ∧ e.2 ∈ X)

/-- Induced subgraph `G[X]` re-indexed onto vertices `{0, …, |X| - 1}` via `X.sort (· ≤ ·)`. -/
def inducedSubgraph (G : Graph) (X : Finset ℕ) : Graph :=
  let vs := vertsOf X
  ⟨X.card, (insideIndices G X).map fun j =>
    let e := G.edges.getD j (0, 0)
    (vs.idxOf e.1, vs.idxOf e.2)⟩

theorem vertsOf_length (X : Finset ℕ) : (vertsOf X).length = X.card :=
  Finset.length_sort (r := (· ≤ ·))

theorem vertsOf_nodup (X : Finset ℕ) : (vertsOf X).Nodup :=
  Finset.sort_nodup X (r := (· ≤ ·))

theorem mem_vertsOf {X : Finset ℕ} {v : ℕ} : v ∈ vertsOf X ↔ v ∈ X :=
  Finset.mem_sort (r := (· ≤ ·))

theorem idxOf_lt_card {X : Finset ℕ} {v : ℕ} (hv : v ∈ X) :
    (vertsOf X).idxOf v < X.card := by
  rw [← vertsOf_length X]
  exact List.idxOf_lt_length_iff.mpr (mem_vertsOf.mpr hv)

theorem getD_vertsOf_idxOf {X : Finset ℕ} {v : ℕ} (hv : v ∈ X) :
    (vertsOf X).getD ((vertsOf X).idxOf v) 0 = v := by
  rw [List.getD_eq_getElem _ _ (by rw [vertsOf_length]; exact idxOf_lt_card hv)]
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (mem_vertsOf.mpr hv))

theorem idxOf_getD_vertsOf {X : Finset ℕ} {k : ℕ} (hk : k < X.card) :
    (vertsOf X).idxOf ((vertsOf X).getD k 0) = k := by
  have hk' : k < (vertsOf X).length := by rw [vertsOf_length]; exact hk
  rw [List.getD_eq_getElem _ _ hk']
  exact (vertsOf_nodup X).idxOf_getElem k hk'

theorem getD_vertsOf_mem {X : Finset ℕ} {k : ℕ} (hk : k < X.card) :
    (vertsOf X).getD k 0 ∈ X := by
  rw [← mem_vertsOf, List.getD_eq_getElem _ _ (by rw [vertsOf_length]; exact hk)]
  exact List.getElem_mem _

theorem mem_insideIndices {G : Graph} {X : Finset ℕ} {j : ℕ} :
    j ∈ insideIndices G X ↔
      j < G.m ∧ (G.edges.getD j (0, 0)).1 ∈ X ∧ (G.edges.getD j (0, 0)).2 ∈ X := by
  simp [insideIndices, List.mem_filter, List.mem_range]

theorem insideIndices_nodup (G : Graph) (X : Finset ℕ) : (insideIndices G X).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem insideIndices_map_eq_inside (G : Graph) (X : Finset ℕ) :
    (insideIndices G X).map (fun j => G.edges.getD j (0, 0)) = G.inside X :=
  map_filter_range_getD G.edges (0, 0) (fun e => decide (e.1 ∈ X ∧ e.2 ∈ X))

theorem inducedSubgraph_edges_eq (G : Graph) (X : Finset ℕ) :
    (inducedSubgraph G X).edges = (G.inside X).map (fun e =>
      ((vertsOf X).idxOf e.1, (vertsOf X).idxOf e.2)) := by
  unfold inducedSubgraph
  rw [← insideIndices_map_eq_inside G X, List.map_map]
  rfl

theorem inducedSubgraph_isValid (G : Graph) (X : Finset ℕ) : (inducedSubgraph G X).IsValid := by
  intro e he
  simp only [inducedSubgraph, List.mem_map] at he
  obtain ⟨j, hj, rfl⟩ := he
  have h12 := (mem_insideIndices.mp hj).2
  exact ⟨idxOf_lt_card h12.1, idxOf_lt_card h12.2⟩

theorem inducedSubgraph_isLoopless {G : Graph} (hL : G.IsLoopless) (X : Finset ℕ) :
    (inducedSubgraph G X).IsLoopless := by
  intro e he
  simp only [inducedSubgraph, List.mem_map] at he
  obtain ⟨j, hj, rfl⟩ := he
  have hj' := mem_insideIndices.mp hj
  have hmem : G.edges.getD j (0, 0) ∈ G.edges := by
    rw [List.getD_eq_getElem _ _ hj'.1]
    exact List.getElem_mem hj'.1
  have hne := hL _ hmem
  intro heq
  apply hne
  have h1 := getD_vertsOf_idxOf hj'.2.1
  have h2 := getD_vertsOf_idxOf hj'.2.2
  dsimp only at heq
  rw [heq] at h1
  exact h1.symm.trans h2

theorem inducedSubgraph_m (G : Graph) (X : Finset ℕ) :
    (inducedSubgraph G X).m = (G.inside X).length := by
  unfold Graph.m
  rw [inducedSubgraph_edges_eq, List.length_map]

private theorem mem_inside_iff_mem {G : Graph} {X : Finset ℕ} {e : ℕ × ℕ} (he : e ∈ G.inside X) :
    e.1 ∈ X ∧ e.2 ∈ X := by
  simp only [Graph.inside, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at he
  exact he.2

theorem inducedSubgraph_deg {G : Graph} {X : Finset ℕ} {k : ℕ} (hk : k < X.card) :
    (inducedSubgraph G X).deg k = G.degIn X ((vertsOf X).getD k 0) := by
  rw [deg_eq_filter_edges (inducedSubgraph_isValid G X) k, inducedSubgraph_edges_eq]
  unfold Graph.degIn
  rw [List.filter_map, List.filter_map, List.length_map, List.length_map]
  congr 1
  · congr 1
    refine List.filter_congr fun e he => ?_
    have he1 := (mem_inside_iff_mem he).1
    simp only [Function.comp_apply, decide_eq_decide]
    constructor
    · intro h
      rw [← h, getD_vertsOf_idxOf he1]
    · intro h
      rw [h, idxOf_getD_vertsOf hk]
  · congr 1
    refine List.filter_congr fun e he => ?_
    have he2 := (mem_inside_iff_mem he).2
    simp only [Function.comp_apply, decide_eq_decide]
    constructor
    · intro h
      rw [← h, getD_vertsOf_idxOf he2]
    · intro h
      rw [h, idxOf_getD_vertsOf hk]

theorem inducedSubgraph_vol {G : Graph} {X S' : Finset ℕ}
    (hS : S' ⊆ (inducedSubgraph G X).verts) :
    (inducedSubgraph G X).vol S' = G.volIn X (S'.image fun k => (vertsOf X).getD k 0) := by
  unfold Graph.vol Graph.volIn
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < X.card := Finset.mem_range.mp (hS hk)
    rw [← inducedSubgraph_deg hk']
    rfl
  · intro a ha b hb hab
    dsimp only at hab
    have ha' : a < X.card := Finset.mem_range.mp (hS ha)
    have hb' : b < X.card := Finset.mem_range.mp (hS hb)
    rw [← idxOf_getD_vertsOf ha', hab, idxOf_getD_vertsOf hb']

theorem inducedSubgraph_cut {G : Graph} {X S' : Finset ℕ}
    (hS : S' ⊆ (inducedSubgraph G X).verts) :
    (inducedSubgraph G X).cut S' = G.cutIn X (S'.image fun k => (vertsOf X).getD k 0) := by
  unfold Graph.cut Graph.cutIn
  rw [inside_verts_eq_edges (inducedSubgraph_isValid G X), inducedSubgraph_edges_eq,
      List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun e he => ?_
  have he12 := mem_inside_iff_mem he
  have hmem1 : (vertsOf X).idxOf e.1 ∈ S' ↔ e.1 ∈ S'.image (fun k => (vertsOf X).getD k 0) := by
    constructor
    · intro h
      exact Finset.mem_image.mpr ⟨_, h, getD_vertsOf_idxOf he12.1⟩
    · intro h
      rcases Finset.mem_image.mp h with ⟨k, hk, hkv⟩
      have hk' : k < X.card := Finset.mem_range.mp (hS hk)
      rw [← hkv, idxOf_getD_vertsOf hk']
      exact hk
  have hmem2 : (vertsOf X).idxOf e.2 ∈ S' ↔ e.2 ∈ S'.image (fun k => (vertsOf X).getD k 0) := by
    constructor
    · intro h
      exact Finset.mem_image.mpr ⟨_, h, getD_vertsOf_idxOf he12.2⟩
    · intro h
      rcases Finset.mem_image.mp h with ⟨k, hk, hkv⟩
      have hk' : k < X.card := Finset.mem_range.mp (hS hk)
      rw [← hkv, idxOf_getD_vertsOf hk']
      exact hk
  simp only [Function.comp_apply]
  congr 1 <;> simp [hmem1, hmem2]

theorem inducedSubgraph_isConductanceExpander {G : Graph} {X : Finset ℕ} {φ : ℝ}
    (hExp : G.IsConductanceExpanderOn X φ) :
    (inducedSubgraph G X).IsConductanceExpanderOn (inducedSubgraph G X).verts φ := by
  intro S' hS' hne hne_top
  let S := S'.image fun k => (vertsOf X).getD k 0
  have hSX : S ⊆ X := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨k, hk, rfl⟩
    exact getD_vertsOf_mem (Finset.mem_range.mp (hS' hk))
  have hSne : S.Nonempty := hne.image _
  have hSneX : S ≠ X := by
    intro heq
    apply hne_top
    apply Finset.Subset.antisymm hS'
    intro k hkV
    have hk : k < X.card := Finset.mem_range.mp hkV
    have hmem : (vertsOf X).getD k 0 ∈ S := by rw [heq]; exact getD_vertsOf_mem hk
    rcases Finset.mem_image.mp hmem with ⟨k', hk', heqk⟩
    have hk'c : k' < X.card := Finset.mem_range.mp (hS' hk')
    have hinj : k' = k := by
      rw [← idxOf_getD_vertsOf hk'c, heqk, idxOf_getD_vertsOf hk]
    rwa [← hinj]
  have hcomp : ((inducedSubgraph G X).verts \ S').image (fun k => (vertsOf X).getD k 0) = X \ S := by
    ext v
    simp only [Finset.mem_image, Finset.mem_sdiff, Graph.verts, inducedSubgraph, Finset.mem_range, S]
    constructor
    · rintro ⟨k, ⟨hk, hkS'⟩, rfl⟩
      refine ⟨getD_vertsOf_mem hk, ?_⟩
      rintro ⟨k', hk', heqk⟩
      have hk'c : k' < X.card := Finset.mem_range.mp (hS' hk')
      have : k' = k := by rw [← idxOf_getD_vertsOf hk'c, heqk, idxOf_getD_vertsOf hk]
      exact hkS' (this ▸ hk')
    · rintro ⟨hvX, hvS⟩
      refine ⟨(vertsOf X).idxOf v, ⟨idxOf_lt_card hvX, ?_⟩, getD_vertsOf_idxOf hvX⟩
      intro hmem
      exact hvS ⟨(vertsOf X).idxOf v, hmem, getD_vertsOf_idxOf hvX⟩
  have hMain := hExp S hSX hSne hSneX
  have hv1 := inducedSubgraph_vol hS'
  have hv2 := inducedSubgraph_vol (G := G) (X := X) (Finset.sdiff_subset (s := (inducedSubgraph G X).verts) (t := S'))
  rw [hcomp] at hv2
  have hc := inducedSubgraph_cut hS'
  unfold Graph.vol at hv1 hv2
  unfold Graph.cut at hc
  rw [← hv1, ← hv2, ← hc] at hMain
  exact hMain

/-- Lift a walk in `inducedSubgraph G X` back to a walk in `G` (along `insideIndices G X`). -/
def liftInducedWalk (G : Graph) (X : Finset ℕ) (P : Walk) : Walk :=
  ⟨P.verts.map (fun k => (vertsOf X).getD k 0),
   P.edges.map (fun j => (insideIndices G X).getD j 0)⟩

theorem isWalk_liftInducedWalk {G : Graph} {X : Finset ℕ} (hX : X ⊆ G.verts)
    {u' v' : ℕ} {P : Walk} (hP : P.IsWalk (inducedSubgraph G X) u' v') :
    (liftInducedWalk G X P).IsWalk G ((vertsOf X).getD u' 0) ((vertsOf X).getD v' 0) := by
  have hu' : u' < X.card := hP.1
  have hv' : v' < X.card := hP.2.1
  have huG : (vertsOf X).getD u' 0 < G.n := Finset.mem_range.mp (hX (getD_vertsOf_mem hu'))
  have hvG : (vertsOf X).getD v' 0 < G.n := Finset.mem_range.mp (hX (getD_vertsOf_mem hv'))
  refine ⟨huG, hvG, ?_⟩
  rcases hP.2.2 with ⟨hPv, hPe, rfl⟩ | ⟨hne, hlen, hhead, hlast, hedges, hstep⟩
  · exact Or.inl ⟨by simp [liftInducedWalk, hPv], by simp [liftInducedWalk, hPe], rfl⟩
  · refine Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [liftInducedWalk] using hne
    · simp [liftInducedWalk, hlen]
    · simp [liftInducedWalk, List.head?_map, hhead]
    · simp [liftInducedWalk, List.getLast?_map, hlast]
    · intro j hj
      simp only [liftInducedWalk, List.mem_map] at hj
      obtain ⟨j', hj', rfl⟩ := hj
      have hj'm : j' < (insideIndices G X).length := by
        have := hedges j' hj'
        simpa [Graph.m, inducedSubgraph] using this
      rw [List.getD_eq_getElem _ _ hj'm]
      exact (mem_insideIndices.mp (List.getElem_mem hj'm)).1
    · intro i hi
      simp only [liftInducedWalk, List.length_map] at hi ⊢
      have hPi := hedges _ (List.getElem_mem hi)
      have hPm : P.edges.getD i 0 < (insideIndices G X).length := by
        rw [List.getD_eq_getElem _ _ hi]
        simpa [Graph.m, inducedSubgraph] using hPi
      have hEdge_sub : (insideIndices G X).getD (P.edges.getD i 0) 0 ∈ insideIndices G X := by
        rw [List.getD_eq_getElem _ _ hPm]
        exact List.getElem_mem hPm
      have h12 := (mem_insideIndices.mp hEdge_sub).2
      have hsub_step := hstep i hi
      have hInd_edge : (inducedSubgraph G X).edges.getD (P.edges.getD i 0) (0, 0) =
          ((vertsOf X).idxOf (G.edges.getD ((insideIndices G X).getD (P.edges.getD i 0) 0) (0, 0)).1,
           (vertsOf X).idxOf (G.edges.getD ((insideIndices G X).getD (P.edges.getD i 0) 0) (0, 0)).2) := by
        simp only [inducedSubgraph]
        rw [List.getD_eq_getElem _ _ (by simpa using hPm),
            List.getD_eq_getElem _ _ hPm, List.getElem_map]
      rw [hInd_edge] at hsub_step
      have hVlt : ∀ x ∈ P.verts, x < X.card :=
        Walk.isWalk_verts_lt (inducedSubgraph_isValid G X) hP
      have hvi1 : P.verts.getD i 0 < X.card := by
        rw [List.getD_eq_getElem _ _ (by omega : i < P.verts.length)]
        exact hVlt _ (List.getElem_mem _)
      have hvi2 : P.verts.getD (i + 1) 0 < X.card := by
        rw [List.getD_eq_getElem _ _ (by omega : i + 1 < P.verts.length)]
        exact hVlt _ (List.getElem_mem _)
      have hmap_e : (P.edges.map fun j => (insideIndices G X).getD j 0).getD i 0 =
          (insideIndices G X).getD (P.edges.getD i 0) 0 := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi),
            List.getD_eq_getElem _ _ hi, List.getElem_map]
      have hmap_v1 : (P.verts.map fun k => (vertsOf X).getD k 0).getD i 0 =
          (vertsOf X).getD (P.verts.getD i 0) 0 := by
        rw [List.getD_eq_getElem _ _ (by simp; omega),
            List.getD_eq_getElem _ _ (by omega : i < P.verts.length), List.getElem_map]
      have hmap_v2 : (P.verts.map fun k => (vertsOf X).getD k 0).getD (i + 1) 0 =
          (vertsOf X).getD (P.verts.getD (i + 1) 0) 0 := by
        rw [List.getD_eq_getElem _ _ (by simp; omega),
            List.getD_eq_getElem _ _ (by omega : i + 1 < P.verts.length), List.getElem_map]
      rw [hmap_e, hmap_v1, hmap_v2]
      rcases hsub_step with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · left
        exact ⟨by rw [← ha, getD_vertsOf_idxOf h12.1], by rw [← hb, getD_vertsOf_idxOf h12.2]⟩
      · right
        exact ⟨by rw [← ha, getD_vertsOf_idxOf h12.2], by rw [← hb, getD_vertsOf_idxOf h12.1]⟩

/-! ## Level partition sums for `DecomposeOutput` -/

private theorem list_range_filter_length (n : ℕ) (q : ℕ → Bool) :
    ((List.range n).filter q).length = ((Finset.range n).filter (fun j => q j = true)).card := by
  rw [list_filter_length_eq_range_card (List.range n) 0 q, List.length_range]
  congr 1; ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hq⟩
    have hj' : j < (List.range n).length := by simpa using hj
    rw [List.getD_eq_getElem _ _ hj', List.getElem_range] at hq
    exact ⟨hj, hq⟩
  · rintro ⟨hj, hq⟩
    have hj' : j < (List.range n).length := by simpa using hj
    refine ⟨hj, ?_⟩
    rw [List.getD_eq_getElem _ _ hj', List.getElem_range]
    exact hq

theorem sum_graphAt_m {G : Graph} {d : DecomposeOutput}
    (hlevel : ∀ j < G.m, d.level j ≤ d.ℓ) :
    ∑ i ∈ Finset.range (d.ℓ + 1), (d.graphAt G i).m = G.m := by
  have hm : ∀ i, (d.graphAt G i).m =
      ((Finset.range G.m).filter (fun j => d.level j = i)).card := by
    intro i
    simp only [DecomposeOutput.graphAt, DecomposeOutput.edgesAt, Graph.m, List.length_map,
      list_range_filter_length, decide_eq_true_eq]
  simp_rw [hm]
  rw [← Finset.card_biUnion]
  · have hunion : (Finset.range (d.ℓ + 1)).biUnion
        (fun i => (Finset.range G.m).filter (fun j => d.level j = i)) = Finset.range G.m := by
      ext j
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      constructor
      · rintro ⟨i, _, hj, _⟩; exact hj
      · intro hj
        exact ⟨d.level j, Nat.lt_succ_of_le (hlevel j hj), hj, rfl⟩
    rw [hunion, Finset.card_range]
  · intro i _ k _ hik
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro j hji hjk
    simp only [Finset.mem_filter] at hji hjk
    exact hik (hji.2.symm.trans hjk.2)

theorem graphAt_isValid {G : Graph} (hG : G.IsValid) (d : DecomposeOutput) (i : ℕ) :
    (d.graphAt G i).IsValid := by
  intro e he
  simp only [DecomposeOutput.graphAt, DecomposeOutput.edgesAt, List.mem_map, List.mem_filter,
    List.mem_range, decide_eq_true_eq] at he
  obtain ⟨j, ⟨hj, _⟩, rfl⟩ := he
  rw [List.getD_eq_getElem _ _ hj]
  exact hG _ (List.getElem_mem hj)

theorem graphAt_isLoopless {G : Graph} (hL : G.IsLoopless) (d : DecomposeOutput) (i : ℕ) :
    (d.graphAt G i).IsLoopless := by
  intro e he
  simp only [DecomposeOutput.graphAt, DecomposeOutput.edgesAt, List.mem_map, List.mem_filter,
    List.mem_range, decide_eq_true_eq] at he
  obtain ⟨j, ⟨hj, _⟩, rfl⟩ := he
  rw [List.getD_eq_getElem _ _ hj]
  exact hL _ (List.getElem_mem hj)

private theorem graphAt_filter_edges_length (G : Graph) (d : DecomposeOutput) (i : ℕ)
    (p : ℕ × ℕ → Bool) :
    ((d.graphAt G i).edges.filter p).length =
      ((Finset.range G.m).filter (fun j => p (G.edges.getD j (0, 0)) = true ∧ d.level j = i)).card := by
  unfold DecomposeOutput.graphAt DecomposeOutput.edgesAt
  rw [List.filter_map, List.length_map, List.filter_filter, list_range_filter_length]
  congr 2; ext j
  simp [Bool.and_eq_true, and_comm]

theorem graphAt_deg_le {G : Graph} (hG : G.IsValid) (d : DecomposeOutput) (i v : ℕ) :
    (d.graphAt G i).deg v ≤ G.deg v := by
  rw [deg_eq_filter_edges (graphAt_isValid hG d i) v, deg_eq_filter_edges hG v]
  rw [graphAt_filter_edges_length, graphAt_filter_edges_length]
  have h1 : ((Finset.range G.m).filter (fun j => (G.edges.getD j (0, 0)).1 = v ∧ d.level j = i)).card ≤
      (G.edges.filter fun e => e.1 = v).length := by
    rw [list_filter_length_eq_range_card _ (0, 0)]
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq] at hj ⊢
    exact ⟨hj.1, hj.2.1⟩
  have h2 : ((Finset.range G.m).filter (fun j => (G.edges.getD j (0, 0)).2 = v ∧ d.level j = i)).card ≤
      (G.edges.filter fun e => e.2 = v).length := by
    rw [list_filter_length_eq_range_card _ (0, 0)]
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq] at hj ⊢
    exact ⟨hj.1, hj.2.1⟩
  exact Nat.add_le_add h1 h2

theorem maxDeg_graphAt_le {G : Graph} (hG : G.IsValid) (d : DecomposeOutput) (i : ℕ) :
    maxDeg (d.graphAt G i) ≤ maxDeg G := by
  rw [maxDeg_le_iff]
  intro v hv
  exact le_trans (graphAt_deg_le hG d i v) (deg_le_maxDeg hv)

theorem sum_graphAt_deg {G : Graph} (hG : G.IsValid) {d : DecomposeOutput}
    (hlevel : ∀ j < G.m, d.level j ≤ d.ℓ) (v : ℕ) :
    ∑ i ∈ Finset.range (d.ℓ + 1), (d.graphAt G i).deg v = G.deg v := by
  have hdeg : ∀ i, (d.graphAt G i).deg v =
      ((Finset.range G.m).filter (fun j => (G.edges.getD j (0, 0)).1 = v ∧ d.level j = i)).card +
      ((Finset.range G.m).filter (fun j => (G.edges.getD j (0, 0)).2 = v ∧ d.level j = i)).card := by
    intro i
    rw [deg_eq_filter_edges (graphAt_isValid hG d i) v,
        graphAt_filter_edges_length, graphAt_filter_edges_length]
    simp
  simp_rw [hdeg, Finset.sum_add_distrib]
  rw [← Finset.card_biUnion, ← Finset.card_biUnion]
  · rw [deg_eq_filter_edges hG v,
        list_filter_length_eq_range_card G.edges (0, 0) (fun e => decide (e.1 = v)),
        list_filter_length_eq_range_card G.edges (0, 0) (fun e => decide (e.2 = v))]
    congr 1
    · congr 1; ext j
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, decide_eq_true_eq]
      exact ⟨fun ⟨i, _, hj, hv1, _⟩ => ⟨hj, hv1⟩,
             fun ⟨hj, hv1⟩ => ⟨d.level j, Nat.lt_succ_of_le (hlevel j hj), hj, hv1, rfl⟩⟩
    · congr 1; ext j
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, decide_eq_true_eq]
      exact ⟨fun ⟨i, _, hj, hv2, _⟩ => ⟨hj, hv2⟩,
             fun ⟨hj, hv2⟩ => ⟨d.level j, Nat.lt_succ_of_le (hlevel j hj), hj, hv2, rfl⟩⟩
  · intro i _ k _ hik
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro j hji hjk
    simp only [Finset.mem_filter] at hji hjk
    exact hik (hji.2.2.symm.trans hjk.2.2)
  · intro i _ k _ hik
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro j hji hjk
    simp only [Finset.mem_filter] at hji hjk
    exact hik (hji.2.2.symm.trans hjk.2.2)

end MinCostFlow.Spanner
