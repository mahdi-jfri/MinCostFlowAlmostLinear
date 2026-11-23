module

public import MinCostFlow.Machine.WideWord.LSSTModelBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Constructive edge/vertex filters and BFS bridge vertices for Theorem 2.2

This file provides the deterministic graph preprocessing and constructive component-bridging
BFS used by both the pure LSST reduction (`LSSTReduction.lean`) and the WordRAM program:

* `nonloopEdges`, `activeVertsList`, `inactiveVertsList`: computable edge/vertex filters.
* `IsBridgeVerts`: structural specification of bridging representatives for `(G_v, V_act, r₀)`.
* `computeBridgeVerts`: constructive iterative BFS returning a bridge list `B` and proving
  `computeBridgeVerts_isBridgeVerts` and `isBridgeVerts_length_le`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open MinCostFlow
open MinCostFlow.LSF

/-! ### Edge/vertex filters and constructive component BFS -/

/-- Ascending list of non-loop edge indices `e < G.m` (`G.tail e ≠ G.head e`). -/
def nonloopEdges (G : IndexedGraph) : List ℕ :=
  (List.range G.m).filter (fun e => G.tail e != G.head e)

theorem nonloopEdges_nodup (G : IndexedGraph) : (nonloopEdges G).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem mem_nonloopEdges_iff {G : IndexedGraph} {e : ℕ} :
    e ∈ nonloopEdges G ↔ e < G.m ∧ G.tail e ≠ G.head e := by
  simp [nonloopEdges]

/-- Ascending list of active vertices (`u < G.n` incident to at least one non-loop edge). -/
def activeVertsList (G : IndexedGraph) : List ℕ :=
  (List.range G.n).filter (fun u =>
    (nonloopEdges G).any (fun e => G.tail e == u || G.head e == u))

theorem activeVertsList_nodup (G : IndexedGraph) : (activeVertsList G).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem mem_activeVertsList_iff {G : IndexedGraph} {u : ℕ} :
    u ∈ activeVertsList G ↔ u < G.n ∧ ∃ e ∈ nonloopEdges G, G.tail e = u ∨ G.head e = u := by
  simp [activeVertsList]

/-- Ascending list of vertices `u < n` not in `V_list`. -/
def inactiveVertsList (n : ℕ) (V_list : List ℕ) : List ℕ :=
  (List.range n).filter (fun u => !(V_list.contains u))

theorem inactiveVertsList_nodup (n : ℕ) (V_list : List ℕ) :
    (inactiveVertsList n V_list).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem mem_inactiveVertsList_iff {n : ℕ} {V_list : List ℕ} {u : ℕ} :
    u ∈ inactiveVertsList n V_list ↔ u < n ∧ u ∉ V_list := by
  simp [inactiveVertsList]

/-- Predicate capturing the five structural requirements of a component-bridging vertex list `B`
for `(G_v, V_act, r₀)` used in Theorem 2.2. -/
def IsBridgeVerts (G_v : MGraph) (V_act : Finset ℕ) (r₀ : ℕ) (B : List ℕ) : Prop :=
  B.Nodup ∧ (∀ b ∈ B, b ∈ V_act) ∧ r₀ ∉ B ∧
    (∀ x ∈ V_act, x ≠ r₀ → (gvWithBridges G_v V_act r₀ B).Connected r₀ x) ∧
    (∀ a ∈ r₀ :: B, ∀ b ∈ r₀ :: B, a ≠ b → ¬ G_v.Connected a b)

/-- Pure neighbor list of `u` in `nonloopEdges G` (nodup). -/
def neighborsOf (G : IndexedGraph) (u : ℕ) : List ℕ :=
  ((nonloopEdges G).filterMap fun e =>
    if G.tail e == u then some (G.head e)
    else if G.head e == u then some (G.tail e)
    else none).dedup

private lemma mem_neighborsOf_iff {G : IndexedGraph} {u v : ℕ} :
    v ∈ neighborsOf G u ↔ ∃ e ∈ nonloopEdges G,
      (G.tail e = u ∧ G.head e = v) ∨ (G.head e = u ∧ G.tail e = v) := by
  simp only [neighborsOf, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hite⟩
    by_cases h1 : G.tail e = u
    · simp only [h1, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hite
      exact ⟨e, he, Or.inl ⟨h1, hite⟩⟩
    · have hb1 : (G.tail e == u) = false := beq_false_of_ne h1
      simp only [hb1, Bool.false_eq_true, ↓reduceIte] at hite
      by_cases h2 : G.head e = u
      · simp only [h2, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hite
        exact ⟨e, he, Or.inr ⟨h2, hite⟩⟩
      · have hb2 : (G.head e == u) = false := beq_false_of_ne h2
        simp [hb2] at hite
  · rintro ⟨e, he, ⟨ht, hh⟩ | ⟨hh, ht⟩⟩
    · exact ⟨e, he, by simp [ht, hh]⟩
    · refine ⟨e, he, ?_⟩
      by_cases h1 : G.tail e = u
      · exact absurd (h1.trans hh.symm) (mem_nonloopEdges_iff.mp he).2
      · have hb1 : (G.tail e == u) = false := beq_false_of_ne h1
        have hb2 : (G.head e == u) = true := beq_iff_eq.mpr hh
        simp only [hb1, Bool.false_eq_true, ↓reduceIte, hb2, Option.some.injEq]
        exact ht

/-- Pure fuel-bounded BFS expanding `vis` across non-loop edges of `G`. -/
def bfsExpand (G : IndexedGraph) : ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, vis => vis
  | _ + 1, [], vis => vis
  | fuel + 1, q :: qs, vis =>
    let nbrs := (neighborsOf G q).filter (fun v => !(vis.contains v))
    bfsExpand G fuel (qs ++ nbrs) (vis ++ nbrs)

private lemma bfsExpand_sub {G : IndexedGraph} :
    ∀ fuel queue vis, ∀ x ∈ vis, x ∈ bfsExpand G fuel queue vis
  | 0, _, _vis, _x, hx => hx
  | _ + 1, [], _vis, _x, hx => hx
  | fuel + 1, _q :: _qs, _vis, _x, hx =>
    bfsExpand_sub fuel _ _ _ (List.mem_append_left _ hx)

private lemma bfsExpand_spec {G : IndexedGraph} (hG : G.Valid) :
    ∀ fuel queue vis,
      queue.Nodup →
      (∀ x ∈ queue, x ∈ vis) →
      (∀ x ∈ vis, x < G.n) →
      G.n + queue.length ≤ fuel + vis.toFinset.card →
      (∀ x ∈ vis, x ∉ queue → ∀ y ∈ neighborsOf G x, y ∈ vis) →
      let vis' := bfsExpand G fuel queue vis
      (∀ x ∈ vis, x ∈ vis') ∧
      (∀ x ∈ vis', x < G.n) ∧
      (∀ x ∈ vis', ∀ y ∈ neighborsOf G x, y ∈ vis') ∧
      (∀ x ∈ vis', x ∈ vis ∨ ∃ u ∈ queue, G.toMGraph.Connected u x) := by
  intro fuel
  induction fuel with
  | zero =>
    intro queue vis _ hq_sub hvis_lt hfuel hclosed
    have hcard_le : vis.toFinset.card ≤ G.n := by
      calc vis.toFinset.card ≤ (Finset.range G.n).card :=
            Finset.card_le_card fun x hx => Finset.mem_range.mpr (hvis_lt x (List.mem_toFinset.mp hx))
        _ = G.n := Finset.card_range G.n
    have hq0 : queue.length = 0 := by omega
    have hq_nil : queue = [] := List.eq_nil_of_length_eq_zero hq0
    subst hq_nil
    refine ⟨fun x hx => hx, hvis_lt, ?_, fun x hx => Or.inl hx⟩
    intro x hx y hy
    exact hclosed x hx List.not_mem_nil y hy
  | succ fuel ih =>
    intro queue vis hq_nd hq_sub hvis_lt hfuel hclosed
    cases queue with
    | nil =>
      refine ⟨fun x hx => hx, hvis_lt, ?_, fun x hx => Or.inl hx⟩
      intro x hx y hy
      exact hclosed x hx List.not_mem_nil y hy
    | cons q qs =>
      dsimp only [bfsExpand]
      let nbrs := (neighborsOf G q).filter (fun v => !(vis.contains v))
      have hnbrs_nd : nbrs.Nodup := List.Nodup.filter _ (List.nodup_dedup _)
      have hnbrs_nvis : ∀ v ∈ nbrs, v ∉ vis := fun v hv => by
        simp [nbrs] at hv; exact hv.2
      have hnbrs_nbr : ∀ v ∈ nbrs, v ∈ neighborsOf G q := fun v hv => by
        simp [nbrs] at hv; exact hv.1
      have hnbrs_lt : ∀ v ∈ nbrs, v < G.n := fun v hv => by
        obtain ⟨e, he, ⟨_, hh⟩ | ⟨_, ht⟩⟩ := mem_neighborsOf_iff.mp (hnbrs_nbr v hv)
        · rw [← hh]; exact (hG.2 e (mem_nonloopEdges_iff.mp he).1).2
        · rw [← ht]; exact (hG.2 e (mem_nonloopEdges_iff.mp he).1).1
      have hqs_nd : qs.Nodup := (List.nodup_cons.mp hq_nd).2
      have hdisj_qs_nbrs : List.Disjoint qs nbrs := fun v hv_qs hv_nbrs =>
        hnbrs_nvis v hv_nbrs (hq_sub v (List.mem_cons_of_mem _ hv_qs))
      have hq'_nd : (qs ++ nbrs).Nodup :=
        List.nodup_append.mpr ⟨hqs_nd, hnbrs_nd, fun a ha b hb heq => hdisj_qs_nbrs ha (heq ▸ hb)⟩
      have hq'_sub : ∀ x ∈ qs ++ nbrs, x ∈ vis ++ nbrs := fun x hx => by
        rcases List.mem_append.mp hx with h1 | h2
        · exact List.mem_append_left _ (hq_sub x (List.mem_cons_of_mem _ h1))
        · exact List.mem_append_right _ h2
      have hvis'_lt : ∀ x ∈ vis ++ nbrs, x < G.n := fun x hx => by
        rcases List.mem_append.mp hx with h1 | h2
        · exact hvis_lt x h1
        · exact hnbrs_lt x h2
      have hcard_eq : (vis ++ nbrs).toFinset.card = vis.toFinset.card + nbrs.length := by
        rw [List.toFinset_append, Finset.card_union_of_disjoint, List.toFinset_card_of_nodup hnbrs_nd]
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact hnbrs_nvis x (List.mem_toFinset.mp hx2) (List.mem_toFinset.mp hx1)
      have hfuel' : G.n + (qs ++ nbrs).length ≤ fuel + (vis ++ nbrs).toFinset.card := by
        rw [List.length_append, hcard_eq]
        simp only [List.length_cons] at hfuel
        omega
      have hclosed' : ∀ x ∈ vis ++ nbrs, x ∉ qs ++ nbrs → ∀ y ∈ neighborsOf G x, y ∈ vis ++ nbrs := by
        intro x hx hnx y hy
        have hnx_qs : x ∉ qs := fun h => hnx (List.mem_append_left _ h)
        have hnx_nbrs : x ∉ nbrs := fun h => hnx (List.mem_append_right _ h)
        have hx_vis : x ∈ vis := by
          rcases List.mem_append.mp hx with h | h
          · exact h
          · exact absurd h hnx_nbrs
        by_cases hxq : x = q
        · subst hxq
          by_cases hy_vis : y ∈ vis
          · exact List.mem_append_left _ hy_vis
          · exact List.mem_append_right _ (by simp [nbrs, hy, hy_vis])
        · have hx_nq : x ∉ q :: qs := by
            rw [List.mem_cons]; rintro (rfl | h); exact hxq rfl; exact hnx_qs h
          exact List.mem_append_left _ (hclosed x hx_vis hx_nq y hy)
      obtain ⟨ih_sub, ih_lt, ih_closed, ih_reach⟩ :=
        ih (qs ++ nbrs) (vis ++ nbrs) hq'_nd hq'_sub hvis'_lt hfuel' hclosed'
      refine ⟨fun x hx => ih_sub x (List.mem_append_left _ hx), ih_lt, ih_closed, ?_⟩
      intro x hx
      rcases ih_reach x hx with hx0 | ⟨u, hu, hconn⟩
      · rcases List.mem_append.mp hx0 with h1 | h2
        · exact Or.inl h1
        · refine Or.inr ⟨q, List.mem_cons_self, ?_⟩
          obtain ⟨e, he, ⟨ht, hh⟩ | ⟨hh, ht⟩⟩ := mem_neighborsOf_iff.mp (hnbrs_nbr x h2)
          · have heG : e ∈ G.toMGraph.E := Finset.mem_range.mpr (mem_nonloopEdges_iff.mp he).1
            exact ⟨[(e, true)], .cons heG (by simp [MGraph.src, IndexedGraph.toMGraph, ht])
              (by simpa [MGraph.dst, IndexedGraph.toMGraph, hh] using .nil x)⟩
          · have heG : e ∈ G.toMGraph.E := Finset.mem_range.mpr (mem_nonloopEdges_iff.mp he).1
            exact ⟨[(e, false)], .cons heG (by simp [MGraph.src, IndexedGraph.toMGraph, hh])
              (by simpa [MGraph.dst, IndexedGraph.toMGraph, ht] using .nil x)⟩
      · rcases List.mem_append.mp hu with h1 | h2
        · exact Or.inr ⟨u, List.mem_cons_of_mem _ h1, hconn⟩
        · obtain ⟨e, he, ⟨ht, hh⟩ | ⟨hh, ht⟩⟩ := mem_neighborsOf_iff.mp (hnbrs_nbr u h2)
          · have heG : e ∈ G.toMGraph.E := Finset.mem_range.mpr (mem_nonloopEdges_iff.mp he).1
            have hqu : G.toMGraph.Connected q u := ⟨[(e, true)], .cons heG
              (by simp [MGraph.src, IndexedGraph.toMGraph, ht])
              (by simpa [MGraph.dst, IndexedGraph.toMGraph, hh] using .nil u)⟩
            exact Or.inr ⟨q, List.mem_cons_self, connected_trans hqu hconn⟩
          · have heG : e ∈ G.toMGraph.E := Finset.mem_range.mpr (mem_nonloopEdges_iff.mp he).1
            have hqu : G.toMGraph.Connected q u := ⟨[(e, false)], .cons heG
              (by simp [MGraph.src, IndexedGraph.toMGraph, hh])
              (by simpa [MGraph.dst, IndexedGraph.toMGraph, ht] using .nil u)⟩
            exact Or.inr ⟨q, List.mem_cons_self, connected_trans hqu hconn⟩

/-- Constructively computes one representative per non-root component of `(V_list, G_nl)` by
scanning `V_list` in order and running `bfsExpand` whenever an unvisited vertex is reached. -/
def computeBridgeVertsAux (G : IndexedGraph) (fuel : ℕ) :
    List ℕ → List ℕ → List ℕ → List ℕ
  | [], _, acc => acc.reverse
  | u :: us, vis, acc =>
    if vis.contains u then
      computeBridgeVertsAux G fuel us vis acc
    else
      computeBridgeVertsAux G fuel us (bfsExpand G fuel [u] (u :: vis)) (u :: acc)

/-- Constructive bridge-vertex list for `(G, V_list)`. -/
def computeBridgeVerts (G : IndexedGraph) (V_list : List ℕ) : List ℕ :=
  match V_list with
  | [] => []
  | r₀ :: rest => computeBridgeVertsAux G G.n rest (bfsExpand G G.n [r₀] [r₀]) []

private lemma connected_mem_closed_of_gv {G : IndexedGraph} {v : ℕ → ℝ}
    {G_nl G_v : MGraph}
    (hG_nl_eq : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    {S : ℕ → Prop} (hclosed : ∀ x, S x → ∀ y ∈ neighborsOf G x, S y) :
    ∀ {a b : ℕ} {P : List (ℕ × Bool)}, G_v.IsWalk a b P → S a → S b := by
  intro a b P hW ha
  induction hW with
  | nil _ => exact ha
  | @cons s _ x xs hxE hsrc _ ih =>
    have hnl_ne' : G_nl.E.Nonempty := by rw [hG_nl_eq]; exact hnl_ne
    have hnl_tail : G_nl.tail = G.tail := by rw [hG_nl_eq]; rfl
    have hnl_head : G_nl.head = G.head := by rw [hG_nl_eq]; rfl
    have hnl_E : G_nl.E = (nonloopEdges G).toFinset := by rw [hG_nl_eq]
    have hm := weightedCopyGraph_origEdge_mem hnl_ne' (hG_v_eq ▸ hxE)
    have ht_eq : G_v.tail x.1 = G.tail (origEdge (copyMod G_nl) x.1) := by
      rw [hG_v_eq, hm.2.1, hnl_tail]
    have hh_eq : G_v.head x.1 = G.head (origEdge (copyMod G_nl) x.1) := by
      rw [hG_v_eq, hm.2.2, hnl_head]
    have he_nl : origEdge (copyMod G_nl) x.1 ∈ nonloopEdges G := by
      have h1 := hm.1
      rw [hnl_E] at h1
      exact List.mem_toFinset.mp h1
    have hdst_S : S (G_v.dst x) := by
      cases hx2 : x.2
      · simp only [MGraph.src, MGraph.dst, hx2, Bool.false_eq_true, ↓reduceIte] at hsrc ⊢
        have hsn : G_v.head x.1 = s := hsrc
        have hnbr : G_v.tail x.1 ∈ neighborsOf G s := mem_neighborsOf_iff.mpr
          ⟨origEdge (copyMod G_nl) x.1, he_nl, Or.inr ⟨hh_eq.symm.trans hsn, ht_eq.symm⟩⟩
        exact hclosed s ha _ hnbr
      · simp only [MGraph.src, MGraph.dst, hx2, ↓reduceIte] at hsrc ⊢
        have hsn : G_v.tail x.1 = s := hsrc
        have hnbr : G_v.head x.1 ∈ neighborsOf G s := mem_neighborsOf_iff.mpr
          ⟨origEdge (copyMod G_nl) x.1, he_nl, Or.inl ⟨ht_eq.symm.trans hsn, hh_eq.symm⟩⟩
        exact hclosed s ha _ hnbr
    exact ih hdst_S

private lemma gv_connected_of_toMGraph {G : IndexedGraph} {v : ℕ → ℝ}
    {G_nl G_v : MGraph}
    (hG_nl_eq : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hv : ∀ e ∈ G.toMGraph.E, 0 < v e)
    {a b : ℕ} (hconn : G.toMGraph.Connected a b)
    (hloop_only : ∀ {u w : ℕ} {P : List (ℕ × Bool)}, G.toMGraph.IsWalk u w P →
      ∃ Q, G_nl.IsWalk u w Q) :
    G_v.Connected a b := by
  obtain ⟨P, hP⟩ := hconn
  obtain ⟨Q, hQ⟩ := hloop_only hP
  have hnl_ne' : G_nl.E.Nonempty := by rw [hG_nl_eq]; exact hnl_ne
  have hsub := weightedCopyGraph_subgraph (G := G_nl) (v := v) fun e he => by
    have he_nl : e ∈ (nonloopEdges G).toFinset := by
      have := he; rwa [hG_nl_eq] at this
    exact hv e (Finset.mem_range.mpr (mem_nonloopEdges_iff.mp (List.mem_toFinset.mp he_nl)).1)
  rw [← hG_v_eq] at hsub
  exact connected_of_subgraph hsub ⟨Q, hQ⟩

private lemma gvWithBridges_connected_of_toMGraph {G : IndexedGraph} {v : ℕ → ℝ}
    {V_act : Finset ℕ} {r₀ : ℕ} {B : List ℕ} {G_nl G_v : MGraph}
    (hG_nl_eq : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hv : ∀ e ∈ G.toMGraph.E, 0 < v e)
    {u x : ℕ} (hconn_ux : G.toMGraph.Connected u x) :
    (gvWithBridges G_v V_act r₀ B).Connected u x := by
  have hgv_ux : G_v.Connected u x :=
    gv_connected_of_toMGraph hG_nl_eq hG_v_eq hnl_ne hv hconn_ux fun {a b} P hWP => by
      induction hWP with
      | nil s => exact ⟨[], .nil s⟩
      | @cons s _ y ys hyE hsy _ ih =>
        obtain ⟨Q, hQ⟩ := ih
        by_cases hloop : G.tail y.1 = G.head y.1
        · have heq_sd : G.toMGraph.src y = G.toMGraph.dst y := by
            cases y.2 <;> simp [MGraph.src, MGraph.dst, IndexedGraph.toMGraph, hloop]
          rw [← heq_sd, hsy] at hQ
          exact ⟨Q, hQ⟩
        · have hy_nl : y.1 ∈ G_nl.E := by
            rw [hG_nl_eq, List.mem_toFinset]
            exact mem_nonloopEdges_iff.mpr ⟨Finset.mem_range.mp hyE, hloop⟩
          have hs' : G_nl.src y = G.toMGraph.src y := by
            cases y.2 <;> simp [MGraph.src, hG_nl_eq]
          have hd' : G_nl.dst y = G.toMGraph.dst y := by
            cases y.2 <;> simp [MGraph.dst, hG_nl_eq]
          exact ⟨y :: Q, .cons hy_nl (hs'.trans hsy) (hd'.symm ▸ hQ)⟩
  clear hconn_ux
  obtain ⟨P_gv, hWP_gv⟩ := hgv_ux
  refine ⟨P_gv, ?_⟩
  induction hWP_gv with
  | nil s => exact .nil s
  | @cons s _ y ys hyE hsy _ ih =>
    have hsrc : (gvWithBridges G_v V_act r₀ B).src y = G_v.src y := by
      cases y.2 <;> simp [gvWithBridges, MGraph.src, ite_eq_left hyE]
    have hdst : (gvWithBridges G_v V_act r₀ B).dst y = G_v.dst y := by
      cases y.2 <;> simp [gvWithBridges, MGraph.dst, ite_eq_left hyE]
    rw [← hdst] at ih
    exact .cons (Finset.mem_union_left _ hyE) (hsrc.trans hsy) ih

private lemma acc_sub_computeBridgeVertsAux (G : IndexedGraph) (fuel : ℕ) :
    ∀ (rest vis acc : List ℕ) {b : ℕ}, b ∈ acc → b ∈ computeBridgeVertsAux G fuel rest vis acc
  | [], _, _, _, hb => List.mem_reverse.mpr hb
  | u :: us, vis, acc, b, hb => by
    dsimp only [computeBridgeVertsAux]
    split_ifs
    · exact acc_sub_computeBridgeVertsAux G fuel us vis acc hb
    · exact acc_sub_computeBridgeVertsAux G fuel us _ (u :: acc) (List.mem_cons_of_mem _ hb)

private lemma computeBridgeVertsAux_props {G : IndexedGraph} {v : ℕ → ℝ}
    {V_act : Finset ℕ} {G_nl G_v : MGraph} (hG : G.Valid)
    (hG_nl_eq : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hv : ∀ e ∈ G.toMGraph.E, 0 < v e)
    (hV_sub : ∀ x ∈ V_act, x < G.n)
    {r₀ : ℕ} :
    ∀ (rest vis acc : List ℕ),
      rest.Nodup →
      (∀ x ∈ rest, x ∈ V_act) →
      (∀ x ∈ vis, x < G.n) →
      (∀ x ∈ vis, ∀ y ∈ neighborsOf G x, y ∈ vis) →
      r₀ ∈ vis →
      (∀ b ∈ acc, b ∈ V_act ∧ b ≠ r₀ ∧ b ∈ vis) →
      acc.Nodup →
      (∀ x ∈ acc, x ∉ rest) →
      (∀ a ∈ r₀ :: acc, ∀ b ∈ r₀ :: acc, a ≠ b → ¬ G_v.Connected a b) →
      (∀ x ∈ vis, x ∈ V_act → (gvWithBridges G_v V_act r₀ acc.reverse).Connected r₀ x) →
      let B := computeBridgeVertsAux G G.n rest vis acc
      B.Nodup ∧ (∀ b ∈ B, b ∈ V_act) ∧ r₀ ∉ B ∧
      (∀ x ∈ rest, (gvWithBridges G_v V_act r₀ B).Connected r₀ x) ∧
      (∀ a ∈ r₀ :: B, ∀ b ∈ r₀ :: B, a ≠ b → ¬ G_v.Connected a b) := by
  intro rest
  induction rest with
  | nil =>
    intro vis acc _ _ _ _ hr₀_vis hacc_mem hacc_nd _ hacc_disj hvis_conn
    dsimp only [computeBridgeVertsAux]
    refine ⟨List.nodup_reverse.mpr hacc_nd, ?_, ?_, fun x hx => absurd hx List.not_mem_nil, ?_⟩
    · intro b hb; exact (hacc_mem b (List.mem_reverse.mp hb)).1
    · intro hmem; exact (hacc_mem r₀ (List.mem_reverse.mp hmem)).2.1 rfl
    · intro a ha b hb hne
      have ha' : a ∈ r₀ :: acc := by simpa [List.mem_cons, List.mem_reverse] using ha
      have hb' : b ∈ r₀ :: acc := by simpa [List.mem_cons, List.mem_reverse] using hb
      exact hacc_disj a ha' b hb' hne
  | cons u us ih =>
    intro vis acc hrest_nd hrest_mem hvis_lt hclosed hr₀_vis hacc_mem hacc_nd hacc_nrest hacc_disj hvis_conn
    have hu_Vact : u ∈ V_act := hrest_mem u List.mem_cons_self
    have hus_nd : us.Nodup := (List.nodup_cons.mp hrest_nd).2
    have hu_nus : u ∉ us := (List.nodup_cons.mp hrest_nd).1
    have hus_mem : ∀ x ∈ us, x ∈ V_act := fun x hx => hrest_mem x (List.mem_cons_of_mem _ hx)
    dsimp only [computeBridgeVertsAux]
    by_cases hu_vis : u ∈ vis
    · simp only [List.contains_iff_mem, hu_vis, ↓reduceIte]
      obtain ⟨hB_nd, hB_Vact, hr₀_nB, hus_conn, hB_disj⟩ :=
        ih vis acc hus_nd hus_mem hvis_lt hclosed hr₀_vis hacc_mem hacc_nd
          (fun x hx hxus => hacc_nrest x hx (List.mem_cons_of_mem _ hxus)) hacc_disj hvis_conn
      refine ⟨hB_nd, hB_Vact, hr₀_nB, fun x hx => ?_, hB_disj⟩
      rw [List.mem_cons] at hx
      rcases hx with hxu | hx
      · rw [hxu]
        have hsubB : (gvWithBridges G_v V_act r₀ (computeBridgeVertsAux G G.n us vis acc)).IsSubgraph
            (gvWithBridges G_v V_act r₀ acc.reverse) := by
          refine ⟨Finset.Subset.refl _, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
          refine Finset.union_subset Finset.subset_union_left fun f hf => ?_
          rw [Finset.mem_image] at hf
          obtain ⟨c, hcB, rfl⟩ := hf
          have hcin : c ∈ acc := List.mem_reverse.mp (List.mem_toFinset.mp hcB)
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr
            (acc_sub_computeBridgeVertsAux G G.n us vis acc hcin)))
        exact connected_of_subgraph hsubB (hvis_conn u hu_vis hu_Vact)
      · exact hus_conn x hx
    · have hfalse : vis.contains u = false := by simp [hu_vis]
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
      have hu_lt : u < G.n := hV_sub u hu_Vact
      let vis' := bfsExpand G G.n [u] (u :: vis)
      have hbfs := bfsExpand_spec hG G.n [u] (u :: vis) (List.nodup_singleton u)
        (fun x hx => by simp at hx; subst hx; exact List.mem_cons_self)
        (fun x hx => by
          rw [List.mem_cons] at hx
          exact hx.elim (· ▸ hu_lt) (hvis_lt x))
        (by
          have hle1 : 1 ≤ (u :: vis).toFinset.card := Finset.card_pos.mpr ⟨u, List.mem_toFinset.mpr List.mem_cons_self⟩
          simp only [List.length_singleton]; omega)
        (fun x hx hnx y hy => by
          rw [List.mem_cons] at hx
          rcases hx with hxu | hx
          · rw [hxu] at hnx; exact absurd List.mem_cons_self hnx
          · exact List.mem_cons_of_mem _ (hclosed x hx y hy))
      dsimp only at hbfs
      obtain ⟨hsub', hvis'_lt, hclosed', hreach'⟩ := hbfs
      have hr₀_ne_u : r₀ ≠ u := fun h => hu_vis (h ▸ hr₀_vis)
      have hr₀_vis' : r₀ ∈ vis' := hsub' r₀ (List.mem_cons_of_mem _ hr₀_vis)
      have hu_vis' : u ∈ vis' := hsub' u List.mem_cons_self
      have hu_nacc : u ∉ acc := fun h => hacc_nrest u h List.mem_cons_self
      have hacc'_mem : ∀ b ∈ u :: acc, b ∈ V_act ∧ b ≠ r₀ ∧ b ∈ vis' := by
        intro b hb
        rw [List.mem_cons] at hb
        rcases hb with hbu | hb
        · rw [hbu]; exact ⟨hu_Vact, hr₀_ne_u.symm, hu_vis'⟩
        · have hb' := hacc_mem b hb
          exact ⟨hb'.1, hb'.2.1, hsub' b (List.mem_cons_of_mem _ hb'.2.2)⟩
      have hacc'_nrest : ∀ x ∈ u :: acc, x ∉ us := by
        intro x hx hxus
        rw [List.mem_cons] at hx
        rcases hx with hxu | hx
        · rw [hxu] at hxus; exact hu_nus hxus
        · exact hacc_nrest x hx (List.mem_cons_of_mem _ hxus)
      have hacc'_disj : ∀ a ∈ r₀ :: u :: acc, ∀ b ∈ r₀ :: u :: acc, a ≠ b → ¬ G_v.Connected a b := by
        have hdisj_u : ∀ a ∈ r₀ :: acc, ¬ G_v.Connected a u := by
          intro a ha hconn_au
          have ha_vis : a ∈ vis := by
            rw [List.mem_cons] at ha
            exact ha.elim (· ▸ hr₀_vis) fun ha' => (hacc_mem a ha').2.2
          exact hu_vis (connected_mem_closed_of_gv hG_nl_eq hG_v_eq hnl_ne hclosed hconn_au.choose_spec ha_vis)
        intro a ha b hb hne
        rw [List.mem_cons] at ha hb
        rcases ha with ha0 | ha <;> rcases hb with hb0 | hb
        · exact absurd (ha0.trans hb0.symm) hne
        · rw [ha0]
          rw [List.mem_cons] at hb
          rcases hb with hbu | hb
          · rw [hbu]; exact hdisj_u r₀ List.mem_cons_self
          · exact hacc_disj r₀ List.mem_cons_self b (List.mem_cons_of_mem _ hb) (ha0 ▸ hne)
        · rw [hb0]
          rw [List.mem_cons] at ha
          rcases ha with hau | ha
          · rw [hau]; exact fun hc => hdisj_u r₀ List.mem_cons_self (connected_symm hc)
          · exact hacc_disj a (List.mem_cons_of_mem _ ha) r₀ List.mem_cons_self (hb0 ▸ hne)
        · rw [List.mem_cons] at ha hb
          rcases ha with hau | ha <;> rcases hb with hbu | hb
          · exact absurd (hau.trans hbu.symm) hne
          · rw [hau]; exact fun hc => hdisj_u b (List.mem_cons_of_mem _ hb) (connected_symm hc)
          · rw [hbu]; exact hdisj_u a (List.mem_cons_of_mem _ ha)
          · exact hacc_disj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hne
      have hvis'_conn : ∀ x ∈ vis', x ∈ V_act →
          (gvWithBridges G_v V_act r₀ (u :: acc).reverse).Connected r₀ x := by
        intro x hx hxV
        have hmono : ∀ a b, (gvWithBridges G_v V_act r₀ acc.reverse).Connected a b →
            (gvWithBridges G_v V_act r₀ (u :: acc).reverse).Connected a b := fun a b hc => by
          have hsubB : (gvWithBridges G_v V_act r₀ (u :: acc).reverse).IsSubgraph
              (gvWithBridges G_v V_act r₀ acc.reverse) := by
            refine ⟨Finset.Subset.refl _, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
            refine Finset.union_subset Finset.subset_union_left fun f hf => ?_
            rw [Finset.mem_image] at hf
            obtain ⟨c, hcB, rfl⟩ := hf
            exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr
              (by simpa [List.mem_reverse] using Or.inl (List.mem_reverse.mp (List.mem_toFinset.mp hcB)))))
          exact connected_of_subgraph hsubB hc
        rcases hreach' x hx with hx_init | ⟨w, hw, hconn_wx⟩
        · rw [List.mem_cons] at hx_init
          rcases hx_init with hxu | hx_vis
          · rw [hxu]
            have hu_inB : u ∈ (u :: acc).reverse := by simp [List.mem_reverse]
            have he_nG : copyMod G_v + u ∉ G_v.E := fun h =>
              Nat.not_lt_of_ge (Nat.le_add_right _ _) (lt_copyMod h)
            have he_mem : copyMod G_v + u ∈ (gvWithBridges G_v V_act r₀ (u :: acc).reverse).E :=
              Finset.mem_union_right _ (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hu_inB))
            exact ⟨[(copyMod G_v + u, true)], .cons he_mem
              (by simp [gvWithBridges, MGraph.src, ite_eq_right he_nG])
              (by simpa [gvWithBridges, MGraph.dst, ite_eq_right he_nG] using .nil u)⟩
          · exact hmono r₀ x (hvis_conn x hx_vis hxV)
        · simp only [List.mem_singleton] at hw
          rw [hw] at hconn_wx
          have hu_inB : u ∈ (u :: acc).reverse := by simp [List.mem_reverse]
          have he_nG : copyMod G_v + u ∉ G_v.E := fun h =>
              Nat.not_lt_of_ge (Nat.le_add_right _ _) (lt_copyMod h)
          have he_mem : copyMod G_v + u ∈ (gvWithBridges G_v V_act r₀ (u :: acc).reverse).E :=
            Finset.mem_union_right _ (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hu_inB))
          have hconn_ru : (gvWithBridges G_v V_act r₀ (u :: acc).reverse).Connected r₀ u :=
            ⟨[(copyMod G_v + u, true)], .cons he_mem
              (by simp [gvWithBridges, MGraph.src, ite_eq_right he_nG])
              (by simpa [gvWithBridges, MGraph.dst, ite_eq_right he_nG] using .nil u)⟩
          have hconn_ux : (gvWithBridges G_v V_act r₀ (u :: acc).reverse).Connected u x :=
            gvWithBridges_connected_of_toMGraph hG_nl_eq hG_v_eq hnl_ne hv hconn_wx
          exact connected_trans hconn_ru hconn_ux
      obtain ⟨hB_nd, hB_Vact, hr₀_nB, hus_conn, hB_disj⟩ :=
        ih vis' (u :: acc) hus_nd hus_mem hvis'_lt hclosed' hr₀_vis' hacc'_mem
          (List.nodup_cons.mpr ⟨hu_nacc, hacc_nd⟩) hacc'_nrest hacc'_disj hvis'_conn
      refine ⟨hB_nd, hB_Vact, hr₀_nB, fun x hx => ?_, hB_disj⟩
      rw [List.mem_cons] at hx
      rcases hx with hxu | hx
      · rw [hxu]
        have hu_inB : u ∈ computeBridgeVertsAux G G.n us vis' (u :: acc) :=
          acc_sub_computeBridgeVertsAux G G.n us vis' (u :: acc) List.mem_cons_self
        have he_nG : copyMod G_v + u ∉ G_v.E := fun h =>
          Nat.not_lt_of_ge (Nat.le_add_right _ _) (lt_copyMod h)
        have he_mem : copyMod G_v + u ∈
            (gvWithBridges G_v V_act r₀ (computeBridgeVertsAux G G.n us vis' (u :: acc))).E :=
          Finset.mem_union_right _ (Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hu_inB))
        exact ⟨[(copyMod G_v + u, true)], .cons he_mem
          (by simp [gvWithBridges, MGraph.src, ite_eq_right he_nG])
          (by simpa [gvWithBridges, MGraph.dst, ite_eq_right he_nG] using .nil u)⟩
      · exact hus_conn x hx

theorem activeVertsList_nonempty_of_nonloop {G : IndexedGraph} (hG : G.Valid)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty) :
    activeVertsList G ≠ [] := by
  obtain ⟨e, he⟩ := hnl_ne
  rw [List.mem_toFinset] at he
  have hlt := (hG.2 e (mem_nonloopEdges_iff.mp he).1).1
  have hmem : G.tail e ∈ activeVertsList G :=
    mem_activeVertsList_iff.mpr ⟨hlt, e, he, Or.inl rfl⟩
  exact List.ne_nil_of_mem hmem

theorem activeVertsList_card_bounds {G : IndexedGraph} (hG : G.Valid)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty) :
    2 ≤ (activeVertsList G).length ∧
      (activeVertsList G).length ≤ G.n ∧
      (activeVertsList G).length ≤ 2 * (nonloopEdges G).length := by
  obtain ⟨e₀, he₀⟩ := hnl_ne
  rw [List.mem_toFinset] at he₀
  have hnl₀ := mem_nonloopEdges_iff.mp he₀
  have htails : G.tail e₀ ∈ activeVertsList G :=
    mem_activeVertsList_iff.mpr ⟨(hG.2 e₀ hnl₀.1).1, e₀, he₀, Or.inl rfl⟩
  have hheads : G.head e₀ ∈ activeVertsList G :=
    mem_activeVertsList_iff.mpr ⟨(hG.2 e₀ hnl₀.1).2, e₀, he₀, Or.inr rfl⟩
  have hnd := activeVertsList_nodup G
  have hge2 : 2 ≤ (activeVertsList G).length := by
    have hsub : ({G.tail e₀, G.head e₀} : Finset ℕ) ⊆ (activeVertsList G).toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [List.mem_toFinset]
      exact hx.elim (· ▸ htails) (· ▸ hheads)
    have hcard2 : ({G.tail e₀, G.head e₀} : Finset ℕ).card = 2 :=
      Finset.card_pair hnl₀.2
    rw [← List.toFinset_card_of_nodup hnd]
    exact hcard2 ▸ Finset.card_le_card hsub
  have hle_n : (activeVertsList G).length ≤ G.n := by
    rw [← List.toFinset_card_of_nodup hnd, ← Finset.card_range G.n]
    exact Finset.card_le_card fun x hx =>
      Finset.mem_range.mpr (mem_activeVertsList_iff.mp (List.mem_toFinset.mp hx)).1
  have hle_2m : (activeVertsList G).length ≤ 2 * (nonloopEdges G).length := by
    let ep := (nonloopEdges G).flatMap fun e => [G.tail e, G.head e]
    have hsub : (activeVertsList G).toFinset ⊆ ep.toFinset := by
      intro x hx
      rw [List.mem_toFinset] at hx ⊢
      obtain ⟨_, e, he, ht | hh⟩ := mem_activeVertsList_iff.mp hx
      · exact List.mem_flatMap.mpr ⟨e, he, by simp [ht]⟩
      · exact List.mem_flatMap.mpr ⟨e, he, by simp [hh]⟩
    calc (activeVertsList G).length = (activeVertsList G).toFinset.card :=
          (List.toFinset_card_of_nodup hnd).symm
      _ ≤ ep.toFinset.card := Finset.card_le_card hsub
      _ ≤ ep.length := List.toFinset_card_le ep
      _ = 2 * (nonloopEdges G).length := by
          dsimp only [ep]
          rw [List.length_flatMap]
          simp [List.map_const', Nat.mul_comm]
  exact ⟨hge2, hle_n, hle_2m⟩

theorem computeBridgeVerts_isBridgeVerts {G : IndexedGraph} {v : ℕ → ℝ}
    {V_act : Finset ℕ} {G_nl G_v : MGraph} (hG : G.Valid)
    (hG_nl_eq : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hv : ∀ e ∈ G.toMGraph.E, 0 < v e)
    (hV_act : ∀ x, x ∈ activeVertsList G ↔ x ∈ V_act)
    {r₀ : ℕ} {rest : List ℕ} (hV_eq : activeVertsList G = r₀ :: rest) :
    IsBridgeVerts G_v V_act r₀ (computeBridgeVerts G (activeVertsList G)) := by
  have hr₀ : r₀ ∈ V_act := (hV_act r₀).mp (hV_eq ▸ List.mem_cons_self)
  have hnd : (activeVertsList G).Nodup := activeVertsList_nodup G
  rw [hV_eq] at hnd
  have hrest_nd : rest.Nodup := (List.nodup_cons.mp hnd).2
  have hrest_mem : ∀ x ∈ rest, x ∈ V_act := fun x hx =>
    (hV_act x).mp (hV_eq ▸ List.mem_cons_of_mem _ hx)
  have hV_sub : ∀ x ∈ V_act, x < G.n := fun x hx =>
    (mem_activeVertsList_iff.mp ((hV_act x).mpr hx)).1
  have hr₀_lt : r₀ < G.n := hV_sub r₀ hr₀
  have hbfs := bfsExpand_spec hG G.n [r₀] [r₀] (List.nodup_singleton r₀)
    (fun _ hx => hx) (fun x hx => by simp at hx; subst hx; exact hr₀_lt)
    (by simp) (fun x hx hnx => absurd hx hnx)
  dsimp only at hbfs
  obtain ⟨hsub0, hvis0_lt, hclosed0, hreach0⟩ := hbfs
  have hr₀_vis0 : r₀ ∈ bfsExpand G G.n [r₀] [r₀] := hsub0 r₀ List.mem_cons_self
  have hvis0_conn : ∀ x ∈ bfsExpand G G.n [r₀] [r₀], x ∈ V_act →
      (gvWithBridges G_v V_act r₀ [].reverse).Connected r₀ x := by
    intro x hx _
    rcases hreach0 x hx with hxr₀ | ⟨w, hw, hconn⟩
    · simp only [List.mem_singleton] at hxr₀
      subst hxr₀
      exact connected_refl _ _
    · simp only [List.mem_singleton] at hw
      subst hw
      exact gvWithBridges_connected_of_toMGraph hG_nl_eq hG_v_eq hnl_ne hv hconn
  have hres := computeBridgeVertsAux_props hG hG_nl_eq hG_v_eq hnl_ne hv hV_sub
    rest (bfsExpand G G.n [r₀] [r₀]) [] hrest_nd hrest_mem hvis0_lt hclosed0 hr₀_vis0
    (fun _ h => absurd h List.not_mem_nil) List.nodup_nil
    (fun _ h => absurd h List.not_mem_nil)
    (fun a ha b hb hne => by
      simp only [List.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hne)
    hvis0_conn
  dsimp only at hres
  have hB_eq : computeBridgeVerts G (activeVertsList G) =
      computeBridgeVertsAux G G.n rest (bfsExpand G G.n [r₀] [r₀]) [] := by
    rw [hV_eq]; rfl
  rw [hB_eq]
  refine ⟨hres.1, hres.2.1, hres.2.2.1, fun x hxV hxne => ?_, hres.2.2.2.2⟩
  have hx_act : x ∈ activeVertsList G := (hV_act x).mpr hxV
  rw [hV_eq, List.mem_cons] at hx_act
  exact hres.2.2.2.1 x (hx_act.elim (fun h => absurd h hxne) id)

theorem isBridgeVerts_length_le {G : IndexedGraph} {v : ℕ → ℝ}
    {V_act : Finset ℕ} {G_nl G_v : MGraph} {r₀ : ℕ} {B : List ℕ}
    (hG_nl_eq : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hv : ∀ e ∈ G.toMGraph.E, 0 < v e)
    (hV_act : ∀ x, x ∈ activeVertsList G ↔ x ∈ V_act)
    (hr₀ : r₀ ∈ V_act) (hB : IsBridgeVerts G_v V_act r₀ B) :
    B.length + 1 ≤ (nonloopEdges G).length ∧ (nonloopEdges G).length ≤ G_v.E.card := by
  let pick : ℕ → ℕ := fun b =>
    ((nonloopEdges G).find? fun e => (G.tail e == b) || (G.head e == b)).getD 0
  have hpick_spec : ∀ b ∈ r₀ :: B, pick b ∈ nonloopEdges G ∧
      (G.tail (pick b) = b ∨ G.head (pick b) = b) := by
    intro b hb
    have hb_act : b ∈ activeVertsList G := by
      rw [List.mem_cons] at hb
      exact (hV_act b).mpr (hb.elim (· ▸ hr₀) (hB.2.1 b))
    obtain ⟨_, e₀, he₀, hinc₀⟩ := mem_activeVertsList_iff.mp hb_act
    have hpred₀ : ((G.tail e₀ == b) || (G.head e₀ == b)) = true := by
      rcases hinc₀ with ht | hh
      · simp [ht]
      · simp [hh]
    cases hfd : (nonloopEdges G).find? fun e => (G.tail e == b) || (G.head e == b) with
    | none => exact absurd (List.find?_eq_none.mp hfd e₀ he₀) (by simp [hpred₀])
    | some e =>
      have he_mem := List.mem_of_find?_eq_some hfd
      have he_pred := List.find?_some hfd
      have hpick_eq : pick b = e := by simp [pick, hfd]
      rw [hpick_eq]
      refine ⟨he_mem, ?_⟩
      simpa [Bool.or_eq_true, beq_iff_eq] using he_pred
  have hpick_inj : Set.InjOn pick (r₀ :: B).toFinset := by
    intro a ha b hb hEq
    by_contra hne
    rw [Finset.mem_coe, List.mem_toFinset] at ha hb
    have ha' := hpick_spec a ha
    have hb' := hpick_spec b hb
    rw [hEq] at ha'
    let e := pick b
    have hnl_ne' : G_nl.E.Nonempty := by rw [hG_nl_eq]; exact hnl_ne
    have hnl_tail : G_nl.tail = G.tail := by rw [hG_nl_eq]; rfl
    have hnl_head : G_nl.head = G.head := by rw [hG_nl_eq]; rfl
    have he_nl : e ∈ G_nl.E := by rw [hG_nl_eq, List.mem_toFinset]; exact hb'.1
    have hv_nl : ∀ f ∈ G_nl.E, 0 < v f := fun f hf => by
      have hf' : f ∈ (nonloopEdges G).toFinset := by
        have := hf; rw [hG_nl_eq] at this; exact this
      exact hv f (Finset.mem_range.mpr (mem_nonloopEdges_iff.mp (List.mem_toFinset.mp hf')).1)
    have hmult : 1 ≤ edgeMult G_nl v e := edgeMult_pos hnl_ne' hv_nl he_nl
    let e' := copyId (copyMod G_nl) e 0
    have he'_mem : e' ∈ G_v.E := by
      rw [hG_v_eq, weightedCopyGraph, ite_eq_left hnl_ne']
      exact Finset.mem_biUnion.mpr ⟨e, he_nl,
        Finset.mem_image_of_mem _ (Finset.mem_range.mpr hmult)⟩
    have htail : G_v.tail e' = G.tail e := by
      rw [hG_v_eq, weightedCopyGraph, ite_eq_left hnl_ne']
      dsimp only [e']
      rw [origEdge_copyId he_nl, hnl_tail]
    have hhead : G_v.head e' = G.head e := by
      rw [hG_v_eq, weightedCopyGraph, ite_eq_left hnl_ne']
      dsimp only [e']
      rw [origEdge_copyId he_nl, hnl_head]
    have hconn_end : ∀ x, (G.tail e = x ∨ G.head e = x) → G_v.Connected (G.tail e) x := by
      intro x hx
      rcases hx with rfl | rfl
      · exact connected_refl G_v _
      · exact ⟨[(e', true)], .cons he'_mem (by simp [MGraph.src, htail])
          (by simpa [MGraph.dst, hhead] using .nil (G.head e))⟩
    have hconn_ab : G_v.Connected a b :=
      connected_trans (connected_symm (hconn_end a ha'.2)) (hconn_end b hb'.2)
    exact hB.2.2.2.2 a ha b hb hne hconn_ab
  have hr₀B_nd : (r₀ :: B).Nodup := List.nodup_cons.mpr ⟨hB.2.2.1, hB.1⟩
  have h1 : B.length + 1 ≤ (nonloopEdges G).length := by
    calc B.length + 1 = (r₀ :: B).length := rfl
      _ = (r₀ :: B).toFinset.card := (List.toFinset_card_of_nodup hr₀B_nd).symm
      _ ≤ (nonloopEdges G).toFinset.card :=
          Finset.card_le_card_of_injOn pick
            (fun x hx => List.mem_toFinset.mpr
              (hpick_spec x (List.mem_toFinset.mp (Finset.mem_coe.mp hx))).1)
            hpick_inj
      _ = (nonloopEdges G).length := List.toFinset_card_of_nodup (nonloopEdges_nodup G)
  have h2 : (nonloopEdges G).length ≤ G_v.E.card := by
    have hnl_ne' : G_nl.E.Nonempty := by rw [hG_nl_eq]; exact hnl_ne
    let f : ℕ → ℕ := fun e => copyId (copyMod G_nl) e 0
    have hfinj : Set.InjOn f (nonloopEdges G).toFinset := fun a ha b hb hEq => by
      have ha_nl : a ∈ G_nl.E := by rw [hG_nl_eq]; exact ha
      have hb_nl : b ∈ G_nl.E := by rw [hG_nl_eq]; exact hb
      exact (copyId_inj ha_nl hb_nl hEq).1
    have hfmem : ∀ e ∈ (nonloopEdges G).toFinset, f e ∈ G_v.E := fun e he => by
      have he_nl : e ∈ G_nl.E := by rw [hG_nl_eq]; exact he
      have hv_nl : ∀ f ∈ G_nl.E, 0 < v f := fun g hg => by
        have hg' : g ∈ (nonloopEdges G).toFinset := by
          have := hg; rw [hG_nl_eq] at this; exact this
        exact hv g (Finset.mem_range.mpr (mem_nonloopEdges_iff.mp (List.mem_toFinset.mp hg')).1)
      have hm := edgeMult_pos hnl_ne' hv_nl he_nl
      rw [hG_v_eq, weightedCopyGraph, ite_eq_left hnl_ne']
      exact Finset.mem_biUnion.mpr ⟨e, he_nl,
        Finset.mem_image_of_mem _ (Finset.mem_range.mpr hm)⟩
    calc (nonloopEdges G).length = (nonloopEdges G).toFinset.card :=
          (List.toFinset_card_of_nodup (nonloopEdges_nodup G)).symm
      _ ≤ G_v.E.card := Finset.card_le_card_of_injOn f hfmem hfinj
  exact ⟨h1, h2⟩

end MinCostFlow.WideWord
