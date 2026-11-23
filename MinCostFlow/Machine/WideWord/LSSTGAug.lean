module

public import MinCostFlow.Machine.WideWord.LSSTModel
import Mathlib.Tactic.Linarith

/-!
# Augmented graph construction and `[AN19]` output decoding

This file defines the weighted-copy enumeration, the augmented `Cited.WGraph` passed to `[AN19]`,
its validity/looplessness/connectivity/weight properties, and deterministic projection of `[AN19]`'s
output back into `(origEdges, bridgePairs)` (`decodeAN19Output`, `concreteLSSTTree`).
-/

@[expose] public section

namespace MinCostFlow.WideWord

open MinCostFlow
open MinCostFlow.LSF

/-- Enumerates all weighted-copy edge IDs `copyId (copyMod G_nl) e k` for `e ∈ nonloopEdges G`
and `k < mult e`. -/
def copyEdgeList (G : IndexedGraph) (mult : ℕ → ℕ) : List ℕ :=
  let G_nl : MGraph := { G.toMGraph with E := (nonloopEdges G).toFinset }
  (nonloopEdges G).flatMap fun e => (List.range (mult e)).map fun k => copyId (copyMod G_nl) e k

/-- Parallel array recording the original edge index `e` for each entry of `copyEdgeList`. -/
def origOfCopy (G : IndexedGraph) (mult : ℕ → ℕ) : List ℕ :=
  (nonloopEdges G).flatMap fun e => List.replicate (mult e) e

theorem copyEdgeList_length (G : IndexedGraph) (mult : ℕ → ℕ) :
    (copyEdgeList G mult).length = ((nonloopEdges G).map mult).sum := by
  simp [copyEdgeList, List.length_flatMap]

theorem origOfCopy_length (G : IndexedGraph) (mult : ℕ → ℕ) :
    (origOfCopy G mult).length = (copyEdgeList G mult).length := by
  simp [origOfCopy, copyEdgeList, List.length_flatMap]

private lemma flatMap_origEdge_eq (G_nl : MGraph) (mult : ℕ → ℕ) :
    ∀ l : List ℕ, (∀ e ∈ l, e ∈ G_nl.E) →
      (l.flatMap fun e => (List.range (mult e)).map fun k => copyId (copyMod G_nl) e k).map
          (origEdge (copyMod G_nl)) =
        l.flatMap fun e => List.replicate (mult e) e
  | [], _ => rfl
  | e :: es, h => by
    have he : e ∈ G_nl.E := h e List.mem_cons_self
    have hes : ∀ x ∈ es, x ∈ G_nl.E := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.flatMap_cons, List.map_append, List.map_map]
    congr 1
    · calc (List.range (mult e)).map (origEdge (copyMod G_nl) ∘ copyId (copyMod G_nl) e)
          = (List.range (mult e)).map (fun _ => e) :=
            List.map_congr_left fun k _ => origEdge_copyId he
        _ = List.replicate (mult e) e := by simp [List.map_const']
    · exact flatMap_origEdge_eq G_nl mult es hes

theorem origOfCopy_eq_map (G : IndexedGraph) (mult : ℕ → ℕ) :
    let G_nl : MGraph := { G.toMGraph with E := (nonloopEdges G).toFinset }
    (copyEdgeList G mult).map (origEdge (copyMod G_nl)) = origOfCopy G mult :=
  flatMap_origEdge_eq _ mult (nonloopEdges G) fun _ he => List.mem_toFinset.mpr he

theorem mem_origOfCopy_iff {G : IndexedGraph} {mult : ℕ → ℕ} {e : ℕ}
    (hmult : ∀ x ∈ nonloopEdges G, 1 ≤ mult x) :
    e ∈ origOfCopy G mult ↔ e ∈ nonloopEdges G := by
  simp only [origOfCopy, List.mem_flatMap, List.mem_replicate]
  constructor
  · rintro ⟨x, hx, _, rfl⟩; exact hx
  · intro he; exact ⟨e, he, Nat.ne_of_gt (hmult e he), rfl⟩

theorem copyEdgeList_nodup (G : IndexedGraph) (mult : ℕ → ℕ) :
    (copyEdgeList G mult).Nodup := by
  let G_nl : MGraph := { G.toMGraph with E := (nonloopEdges G).toFinset }
  dsimp only [copyEdgeList]
  refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
  · intro e he
    have he_nl : e ∈ G_nl.E := List.mem_toFinset.mpr he
    exact List.nodup_range.map (fun {_ _ h} => (copyId_inj he_nl he_nl h).2)
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hlt x hx₁ hx₂
    simp only [List.mem_map, List.mem_range] at hx₁ hx₂
    obtain ⟨k₁, _, rfl⟩ := hx₁
    obtain ⟨k₂, _, hEq⟩ := hx₂
    have he₁ : (nonloopEdges G)[i]'hi ∈ G_nl.E := List.mem_toFinset.mpr (List.getElem_mem hi)
    have he₂ : (nonloopEdges G)[j]'hj ∈ G_nl.E := List.mem_toFinset.mpr (List.getElem_mem hj)
    have he_eq := (copyId_inj he₂ he₁ hEq).1
    have hij := ((nonloopEdges_nodup G).getElem_inj_iff).mp he_eq
    omega

theorem mem_copyEdgeList_iff {G : IndexedGraph} {v : ℕ → ℝ} {G_nl G_v : MGraph}
    (hG_nl_eq : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    {mult : ℕ → ℕ} (hmult : ∀ e ∈ nonloopEdges G, mult e = edgeMult G_nl v e)
    {e' : ℕ} :
    e' ∈ copyEdgeList G mult ↔ e' ∈ G_v.E := by
  rw [hG_v_eq, weightedCopyGraph, ite_eq_left (hG_nl_eq ▸ hnl_ne)]
  simp only [copyEdgeList, List.mem_flatMap, List.mem_map, List.mem_range,
    Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨e, he, k, hk, rfl⟩
    have he_nl : e ∈ G_nl.E := by rw [hG_nl_eq, List.mem_toFinset]; exact he
    exact ⟨e, he_nl, k, hmult e he ▸ hk, hG_nl_eq ▸ rfl⟩
  · rintro ⟨e, he_nl, k, hk, rfl⟩
    have he : e ∈ nonloopEdges G := by rw [hG_nl_eq, List.mem_toFinset] at he_nl; exact he_nl
    exact ⟨e, he, k, (hmult e he).symm ▸ hk, hG_nl_eq ▸ rfl⟩

/-- Augmented weighted graph passed to `[AN19]`'s WordRAM program. -/
def buildGAug (G : IndexedGraph) (V_list B : List ℕ) (mult w_orig : ℕ → ℕ) : Cited.WGraph :=
  { n := V_list.length
    edges :=
      ((nonloopEdges G).flatMap fun e =>
        List.replicate (mult e) (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e)) ++
      (B.map fun b => (0, V_list.idxOf b, 1)) }

private lemma flatMap_buildGAug_edges_eq (G : IndexedGraph) (V_list : List ℕ)
    (mult w_orig : ℕ → ℕ) {v : ℕ → ℝ} (G_nl G_v : MGraph)
    (hG_nl_eq : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty) :
    ∀ l : List ℕ, (∀ e ∈ l, e ∈ nonloopEdges G) →
      (l.flatMap fun e => (List.range (mult e)).map fun k => copyId (copyMod G_nl) e k).map
          (fun e' => (V_list.idxOf (G_v.tail e'), V_list.idxOf (G_v.head e'),
            w_orig (origEdge (copyMod G_nl) e'))) =
        l.flatMap fun e => List.replicate (mult e)
          (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e)
  | [], _ => rfl
  | e :: es, h => by
    have he : e ∈ nonloopEdges G := h e List.mem_cons_self
    have he_nl : e ∈ G_nl.E := by rw [hG_nl_eq, List.mem_toFinset]; exact he
    have hnl_ne' : G_nl.E.Nonempty := by rw [hG_nl_eq]; exact hnl_ne
    have hnl_tail : G_nl.tail = G.tail := by rw [hG_nl_eq]; rfl
    have hnl_head : G_nl.head = G.head := by rw [hG_nl_eq]; rfl
    have hes : ∀ x ∈ es, x ∈ nonloopEdges G := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.flatMap_cons, List.map_append, List.map_map]
    congr 1
    · calc (List.range (mult e)).map
            ((fun e' => (V_list.idxOf (G_v.tail e'), V_list.idxOf (G_v.head e'),
              w_orig (origEdge (copyMod G_nl) e'))) ∘ copyId (copyMod G_nl) e)
          = (List.range (mult e)).map (fun _ =>
              (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e)) := by
            refine List.map_congr_left fun k _ => ?_
            simp only [Function.comp_def, hG_v_eq, weightedCopyGraph,
              ite_eq_left hnl_ne', origEdge_copyId he_nl, hnl_tail, hnl_head]
        _ = List.replicate (mult e)
              (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e) := by
            simp [List.map_const']
    · exact flatMap_buildGAug_edges_eq G V_list mult w_orig G_nl G_v
        hG_nl_eq hG_v_eq hnl_ne es hes

theorem buildGAug_n (G : IndexedGraph) (V_list B : List ℕ) (mult w_orig : ℕ → ℕ) :
    (buildGAug G V_list B mult w_orig).n = V_list.length := rfl

theorem buildGAug_m (G : IndexedGraph) (V_list B : List ℕ) (mult w_orig : ℕ → ℕ) :
    (buildGAug G V_list B mult w_orig).m = (copyEdgeList G mult).length + B.length := by
  simp only [Cited.WGraph.m, buildGAug, List.length_append, List.length_flatMap,
    List.length_replicate, List.length_map, copyEdgeList_length]

theorem buildGAug_edge_E {G : IndexedGraph} {V_list B : List ℕ} {mult w_orig : ℕ → ℕ}
    {v : ℕ → ℝ} {G_nl G_v : MGraph}
    (hG_nl_eq : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (j : ℕ) (hj : j < (copyEdgeList G mult).length) :
    let E_list := copyEdgeList G mult
    let w_int := fun e' => w_orig (origEdge (copyMod G_nl) e')
    (buildGAug G V_list B mult w_orig).edges[j]'(by
      rw [← Cited.WGraph.m, buildGAug_m]; omega) =
      (V_list.idxOf (G_v.tail (E_list[j]'hj)),
       V_list.idxOf (G_v.head (E_list[j]'hj)), w_int (E_list[j]'hj)) := by
  intro E_list w_int
  have hed := flatMap_buildGAug_edges_eq G V_list mult w_orig G_nl G_v hG_nl_eq hG_v_eq hnl_ne
    (nonloopEdges G) (fun _ h => h)
  have hed' : (E_list.map fun e' =>
        (V_list.idxOf (G_v.tail e'), V_list.idxOf (G_v.head e'), w_int e')) =
      ((nonloopEdges G).flatMap fun e =>
        List.replicate (mult e) (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e)) := by
    have hE_eq : E_list = (nonloopEdges G).flatMap fun e =>
        (List.range (mult e)).map fun k => copyId (copyMod G_nl) e k := by
      dsimp only [E_list, copyEdgeList]
      rw [← hG_nl_eq]
    rw [hE_eq]
    exact hed
  have hj_lt : j < ((nonloopEdges G).flatMap fun e =>
      List.replicate (mult e) (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e)).length := by
    rw [← hed', List.length_map]; exact hj
  have hleft : (buildGAug G V_list B mult w_orig).edges[j]'(by
      rw [← Cited.WGraph.m, buildGAug_m]; omega) =
      ((nonloopEdges G).flatMap fun e =>
        List.replicate (mult e)
          (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e))[j]'hj_lt :=
    List.getElem_append_left hj_lt
  rw [hleft]
  have hget : (((E_list.map fun e' =>
        (V_list.idxOf (G_v.tail e'), V_list.idxOf (G_v.head e'), w_int e'))))[j]'(by
      rw [List.length_map]; exact hj) =
      (V_list.idxOf (G_v.tail (E_list[j]'hj)),
       V_list.idxOf (G_v.head (E_list[j]'hj)), w_int (E_list[j]'hj)) :=
    List.getElem_map _
  rw [← hget]
  congr 1
  exact hed'.symm

theorem buildGAug_edge_B (G : IndexedGraph) (V_list B : List ℕ) (mult w_orig : ℕ → ℕ)
    (k : ℕ) (hk : k < B.length) :
    (buildGAug G V_list B mult w_orig).edges[(copyEdgeList G mult).length + k]'(by
      rw [← Cited.WGraph.m, buildGAug_m]; omega) = (0, V_list.idxOf (B[k]'hk), 1) := by
  let lhs := (nonloopEdges G).flatMap fun e =>
    List.replicate (mult e) (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e)
  let rhs := B.map fun b => (0, V_list.idxOf b, 1)
  have hlen : lhs.length = (copyEdgeList G mult).length := by
    simp [lhs, copyEdgeList, List.length_flatMap]
  have hmem_lt : (copyEdgeList G mult).length + k < (lhs ++ rhs).length := by
    rw [List.length_append, hlen]; simp [rhs, hk]
  change (lhs ++ rhs)[(copyEdgeList G mult).length + k]'hmem_lt = (0, V_list.idxOf (B[k]'hk), 1)
  have hle : lhs.length ≤ (copyEdgeList G mult).length + k := by omega
  rw [List.getElem_append_right hle]
  have hsub : (copyEdgeList G mult).length + k - lhs.length = k := by omega
  simp [rhs, hsub]

theorem headD_eq_getElem_zero : ∀ (xs : List ℕ) (h : 0 < xs.length),
    xs.headD 0 = xs[0]'h
  | _ :: _, _ => rfl

theorem buildGAug_graph_isValid {G : IndexedGraph} {V_act : Finset ℕ}
    {G_v : MGraph} {V_list B : List ℕ} {mult w_orig : ℕ → ℕ}
    (hG : G.Valid) (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hV_mem : ∀ x, x ∈ V_list ↔ x ∈ activeVertsList G)
    (hV_act : ∀ x, x ∈ activeVertsList G ↔ x ∈ V_act)
    (hB : IsBridgeVerts G_v V_act (V_list.headD 0) B) :
    (buildGAug G V_list B mult w_orig).graph.IsValid := by
  intro ep hep
  rw [Cited.WGraph.graph, List.mem_map] at hep
  obtain ⟨e, he_edges, rfl⟩ := hep
  dsimp only [buildGAug] at he_edges
  rw [List.mem_append] at he_edges
  rcases he_edges with he_E | he_B
  · rw [List.mem_flatMap] at he_E
    obtain ⟨orig, horig, hrep⟩ := he_E
    have hlt : orig < G.m := (mem_nonloopEdges_iff.mp horig).1
    have htail_mem : G.tail orig ∈ V_list :=
      (hV_mem _).mpr (mem_activeVertsList_iff.mpr ⟨(hG.2 orig hlt).1, orig, horig, Or.inl rfl⟩)
    have hhead_mem : G.head orig ∈ V_list :=
      (hV_mem _).mpr (mem_activeVertsList_iff.mpr ⟨(hG.2 orig hlt).2, orig, horig, Or.inr rfl⟩)
    rw [List.mem_replicate] at hrep
    rcases hrep with ⟨_, rfl⟩
    exact ⟨List.idxOf_lt_length_of_mem htail_mem, List.idxOf_lt_length_of_mem hhead_mem⟩
  · rw [List.mem_map] at he_B
    obtain ⟨b, hbB, rfl⟩ := he_B
    have hV_ne : V_list ≠ [] := by
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (activeVertsList_nonempty_of_nonloop hG hnl_ne)
      exact List.ne_nil_of_mem ((hV_mem x).mpr hx)
    have hb_mem : b ∈ V_list := (hV_mem b).mpr ((hV_act b).mpr (hB.2.1 b hbB))
    exact ⟨List.length_pos_of_ne_nil hV_ne, List.idxOf_lt_length_of_mem hb_mem⟩

theorem buildGAug_graph_isLoopless {G : IndexedGraph} {V_act : Finset ℕ}
    {G_v : MGraph} {V_list B : List ℕ} {mult w_orig : ℕ → ℕ}
    (hG : G.Valid) (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hV_nd : V_list.Nodup) (hV_mem : ∀ x, x ∈ V_list ↔ x ∈ activeVertsList G)
    (hV_act : ∀ x, x ∈ activeVertsList G ↔ x ∈ V_act)
    (hB : IsBridgeVerts G_v V_act (V_list.headD 0) B) :
    (buildGAug G V_list B mult w_orig).graph.IsLoopless := by
  intro ep hep hEq
  rw [Cited.WGraph.graph, List.mem_map] at hep
  obtain ⟨e, he_edges, rfl⟩ := hep
  dsimp only [buildGAug] at he_edges
  rw [List.mem_append] at he_edges
  rcases he_edges with he_E | he_B
  · rw [List.mem_flatMap] at he_E
    obtain ⟨orig, horig, hrep⟩ := he_E
    have hnl := mem_nonloopEdges_iff.mp horig
    have htail_mem : G.tail orig ∈ V_list :=
      (hV_mem _).mpr (mem_activeVertsList_iff.mpr ⟨(hG.2 orig hnl.1).1, orig, horig, Or.inl rfl⟩)
    have hhead_mem : G.head orig ∈ V_list :=
      (hV_mem _).mpr (mem_activeVertsList_iff.mpr ⟨(hG.2 orig hnl.1).2, orig, horig, Or.inr rfl⟩)
    rw [List.mem_replicate] at hrep
    rcases hrep with ⟨_, rfl⟩
    exact hnl.2 (idxOf_inj_of_mem htail_mem hhead_mem hEq)
  · rw [List.mem_map] at he_B
    obtain ⟨b, hbB, rfl⟩ := he_B
    have hV_ne : V_list ≠ [] := by
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (activeVertsList_nonempty_of_nonloop hG hnl_ne)
      exact List.ne_nil_of_mem ((hV_mem x).mpr hx)
    have hlen_pos : 0 < V_list.length := List.length_pos_of_ne_nil hV_ne
    have hr₀_eq : V_list.headD 0 = V_list[0]'hlen_pos := headD_eq_getElem_zero V_list hlen_pos
    have hr₀_mem : V_list.headD 0 ∈ V_list := hr₀_eq ▸ List.getElem_mem hlen_pos
    have hidx0 : V_list.idxOf (V_list.headD 0) = 0 := by
      rw [hr₀_eq]; exact idxOf_getElem_of_nodup hV_nd hlen_pos
    have hb_mem : b ∈ V_list := (hV_mem b).mpr ((hV_act b).mpr (hB.2.1 b hbB))
    have hEq' : V_list.idxOf (V_list.headD 0) = V_list.idxOf b := hidx0.trans hEq
    exact hB.2.2.1 ((idxOf_inj_of_mem hr₀_mem hb_mem hEq') ▸ hbB)

theorem buildGAug_weight_ge_one {G : IndexedGraph} {V_list B : List ℕ} {mult w_orig : ℕ → ℕ}
    (hw_pos : ∀ e ∈ nonloopEdges G, 1 ≤ w_orig e) :
    ∀ e ∈ (buildGAug G V_list B mult w_orig).edges, 1 ≤ e.2.2 := by
  intro e he
  dsimp only [buildGAug] at he
  rw [List.mem_append] at he
  rcases he with he_E | he_B
  · rw [List.mem_flatMap] at he_E
    obtain ⟨orig, horig, hrep⟩ := he_E
    rw [List.mem_replicate] at hrep
    rcases hrep with ⟨_, rfl⟩
    exact hw_pos orig horig
  · rw [List.mem_map] at he_B
    obtain ⟨_, _, rfl⟩ := he_B
    exact le_rfl

theorem buildGAug_maxWeight_le {G : IndexedGraph} {V_list B : List ℕ} {mult w_orig : ℕ → ℕ}
    {W : ℕ} (hW1 : 1 ≤ W) (hWw : ∀ e ∈ nonloopEdges G, w_orig e ≤ W) :
    (buildGAug G V_list B mult w_orig).maxWeight ≤ W := by
  unfold Cited.WGraph.maxWeight
  have hle : ∀ es : List (ℕ × ℕ × ℕ), (∀ e ∈ es, e.2.2 ≤ W) →
      List.foldr max 0 (es.map fun e => e.2.2) ≤ W := by
    intro es hes
    induction es with
    | nil => exact Nat.zero_le W
    | cons x xs ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact max_le (hes x List.mem_cons_self) (ih fun y hy => hes y (List.mem_cons_of_mem _ hy))
  refine hle _ fun e he => ?_
  dsimp only [buildGAug] at he
  rw [List.mem_append] at he
  rcases he with he_E | he_B
  · rw [List.mem_flatMap] at he_E
    obtain ⟨orig, horig, hrep⟩ := he_E
    rw [List.mem_replicate] at hrep
    rcases hrep with ⟨_, rfl⟩
    exact hWw orig horig
  · rw [List.mem_map] at he_B
    obtain ⟨_, _, rfl⟩ := he_B
    exact hW1

theorem buildGAug_isConnected {G : IndexedGraph} {v : ℕ → ℝ} {V_act : Finset ℕ}
    {G_nl G_v : MGraph} {V_list B : List ℕ} {mult w_orig : ℕ → ℕ}
    (hG : G.Valid) (hG_nl_eq : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v_eq : G_v = weightedCopyGraph G_nl v)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hV_nd : V_list.Nodup) (hV_mem : ∀ x, x ∈ V_list ↔ x ∈ activeVertsList G)
    (hV_act : ∀ x, x ∈ activeVertsList G ↔ x ∈ V_act)
    (hB : IsBridgeVerts G_v V_act (V_list.headD 0) B)
    (hmult_pos : ∀ e ∈ nonloopEdges G, 1 ≤ mult e) :
    (buildGAug G V_list B mult w_orig).IsConnected := by
  let G_aug := buildGAug G V_list B mult w_orig
  let r₀ := V_list.headD 0
  let H := gvWithBridges G_v V_act r₀ B
  have hV_ne : V_list ≠ [] := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (activeVertsList_nonempty_of_nonloop hG hnl_ne)
    exact List.ne_nil_of_mem ((hV_mem x).mpr hx)
  have hlen_pos : 0 < V_list.length := List.length_pos_of_ne_nil hV_ne
  have hr₀_eq : r₀ = V_list[0]'hlen_pos := headD_eq_getElem_zero V_list hlen_pos
  have hidx0 : V_list.idxOf r₀ = 0 := by
    rw [hr₀_eq]; exact idxOf_getElem_of_nodup hV_nd hlen_pos
  have hr₀_Vact : r₀ ∈ V_act := (hV_act r₀).mp ((hV_mem r₀).mp (hr₀_eq ▸ List.getElem_mem hlen_pos))
  have hlift : ∀ {a b : ℕ} {P : List (ℕ × Bool)}, H.IsWalk a b P →
      ∃ es, G_aug.IsWalkIn (List.range G_aug.m) (V_list.idxOf a) (V_list.idxOf b) es := by
    intro a b P hP
    induction hP with
    | nil s => exact ⟨[], .nil _⟩
    | @cons s _ y ys hyE hsy _ ih =>
      obtain ⟨es, hes⟩ := ih
      by_cases hyG : y.1 ∈ G_v.E
      · have hnl_ne' : G_nl.E.Nonempty := by rw [hG_nl_eq]; exact hnl_ne
        have hnl_E : G_nl.E = (nonloopEdges G).toFinset := by rw [hG_nl_eq]
        have hnl_tail : G_nl.tail = G.tail := by rw [hG_nl_eq]; rfl
        have hnl_head : G_nl.head = G.head := by rw [hG_nl_eq]; rfl
        have hm := weightedCopyGraph_origEdge_mem hnl_ne' (hG_v_eq ▸ hyG)
        let orig := origEdge (copyMod G_nl) y.1
        have horig : orig ∈ nonloopEdges G := by
          have h1 := hm.1; rw [hnl_E] at h1; exact List.mem_toFinset.mp h1
        have htail_y : H.tail y.1 = G.tail orig := by
          dsimp only [H, gvWithBridges]; rw [ite_eq_left hyG, hG_v_eq, hm.2.1, hnl_tail]
        have hhead_y : H.head y.1 = G.head orig := by
          dsimp only [H, gvWithBridges]; rw [ite_eq_left hyG, hG_v_eq, hm.2.2, hnl_head]
        have he_edge_mem :
            (V_list.idxOf (G.tail orig), V_list.idxOf (G.head orig), w_orig orig) ∈ G_aug.edges := by
          dsimp only [G_aug, buildGAug]
          refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨orig, horig, ?_⟩)
          exact List.mem_replicate.mpr ⟨Nat.ne_of_gt (hmult_pos orig horig), rfl⟩
        obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp he_edge_mem
        have hj_m : j < G_aug.m := hj
        have hjeq' : G_aug.edges[j]'hj_m =
            (V_list.idxOf (G.tail orig), V_list.idxOf (G.head orig), w_orig orig) := hjeq
        refine ⟨j :: es, .cons (List.mem_range.mpr hj_m) hj_m ?_ hes⟩
        cases hy2 : y.2 <;>
          simp only [MGraph.src, MGraph.dst, hy2, Bool.false_eq_true, ↓reduceIte,
            htail_y, hhead_y] at hsy ⊢
        · right; simp [hjeq', hsy]
        · left; simp [hjeq', hsy]
      · have hyE' : y.1 ∈ H.E := hyE
        dsimp only [H, gvWithBridges] at hyE'
        rw [Finset.mem_union] at hyE'
        have hyB : y.1 ∈ (B.toFinset.image fun b => copyMod G_v + b) :=
          hyE'.elim (fun h => absurd h hyG) id
        rw [Finset.mem_image] at hyB
        obtain ⟨b, hbB, hy_eq⟩ := hyB
        rw [List.mem_toFinset] at hbB
        have htail_y : H.tail y.1 = r₀ := by
          dsimp only [H, gvWithBridges]; exact ite_eq_right hyG
        have hhead_y : H.head y.1 = b := by
          dsimp only [H, gvWithBridges]; rw [ite_eq_right hyG, ← hy_eq]; omega
        have he_edge_mem : (V_list.idxOf r₀, V_list.idxOf b, 1) ∈ G_aug.edges := by
          rw [hidx0]
          dsimp only [G_aug, buildGAug]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨b, hbB, rfl⟩)
        obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp he_edge_mem
        have hj_m : j < G_aug.m := hj
        have hjeq' : G_aug.edges[j]'hj_m = (V_list.idxOf r₀, V_list.idxOf b, 1) := hjeq
        refine ⟨j :: es, .cons (List.mem_range.mpr hj_m) hj_m ?_ hes⟩
        cases hy2 : y.2 <;>
          simp only [MGraph.src, MGraph.dst, hy2, Bool.false_eq_true, ↓reduceIte,
            htail_y, hhead_y] at hsy ⊢
        · right; simp [hjeq', hsy]
        · left; simp [hjeq', hsy]
  refine ⟨hlen_pos, fun u hu v' hv' => ?_⟩
  have hu_act : V_list[u]'hu ∈ V_act := (hV_act _).mp ((hV_mem _).mp (List.getElem_mem hu))
  have hv_act : V_list[v']'hv' ∈ V_act := (hV_act _).mp ((hV_mem _).mp (List.getElem_mem hv'))
  have hconn_H : ∀ x ∈ V_act, H.Connected r₀ x := fun x hx =>
    if hxeq : x = r₀ then hxeq ▸ connected_refl H r₀ else hB.2.2.2.1 x hx hxeq
  have hconn_uv : H.Connected (V_list[u]'hu) (V_list[v']'hv') :=
    connected_trans (connected_symm (hconn_H _ hu_act)) (hconn_H _ hv_act)
  obtain ⟨P, hP⟩ := hconn_uv
  obtain ⟨es, hes⟩ := hlift hP
  rw [idxOf_getElem_of_nodup hV_nd hu, idxOf_getElem_of_nodup hV_nd hv'] at hes
  exact ⟨es, hes⟩

/-- Deterministic decoding of `[AN19]`'s edge list `out` into `(origEdges, bridgePairs)`. -/
def decodeAN19Output (G : IndexedGraph) (V_list B : List ℕ) (mult : ℕ → ℕ)
    (out : List ℕ) : List ℕ × List (ℕ × ℕ) :=
  let m₁ := ((nonloopEdges G).map mult).sum
  let origs := origOfCopy G mult
  let r₀ := V_list.headD 0
  let origEdges := (out.filter (· < m₁)).map fun j => origs.getD j 0
  let bridgeOut := (out.filter fun j => decide (m₁ ≤ j ∧ j < m₁ + B.length)).map
    fun j => (r₀, B.getD (j - m₁) 0)
  let bridgeInact := (inactiveVertsList G.n V_list).map fun w => (r₀, w)
  (origEdges, bridgeOut ++ bridgeInact)

/-- Explicit deterministic spanning tree constructed from `(V_list, B, mult, out)`. -/
def concreteLSSTTree (G : IndexedGraph) (V_list B : List ℕ) (mult : ℕ → ℕ)
    (out : List ℕ) : MGraph :=
  if (nonloopEdges G).isEmpty then
    decodedTree G.n G.m G.tail G.head [] ((List.range (G.n - 1)).map fun i => (0, i + 1))
  else
    let res := decodeAN19Output G V_list B mult out
    decodedTree G.n G.m G.tail G.head res.1 res.2

/-! ### Linear size bounds for `buildGAug` -/

/-- Because all input weights `v e` share one fixed-point binary denominator `2 ^ P`, the
scale cancels identically in `‖v‖₁` and `weightsProc` computes the exact integer multiplicity
`edgeMult G_nl v e = ⌈|E_nl| · v_e / ‖v‖₁⌉₊` with zero rounding error. By
`MinCostFlow.LSF.weightedCopyGraph_card_le`, these multiplicities sum to at most
`2 * (nonloopEdges G).length`. -/
theorem mult_sum_le_two_mul_nl {G : IndexedGraph} {v : ℕ → ℝ} {mult : ℕ → ℕ}
    (hv : ∀ e ∈ nonloopEdges G, 0 < v e)
    (hmult : ∀ e ∈ nonloopEdges G,
      mult e = edgeMult { G.toMGraph with E := (nonloopEdges G).toFinset } v e) :
    ((nonloopEdges G).map mult).sum ≤ 2 * (nonloopEdges G).length := by
  let nl := nonloopEdges G
  by_cases hnil : nl = []
  · simp [nl, hnil]
  · have hnl_ne : ({ G.toMGraph with E := nl.toFinset } : MGraph).E.Nonempty := by
      rw [List.toFinset_nonempty_iff]
      exact hnil
    have hnd : nl.Nodup := nonloopEdges_nodup G
    have hsum_cast : (nl.map mult).sum =
        ∑ e ∈ nl.toFinset, edgeMult { G.toMGraph with E := nl.toFinset } v e := by
      rw [← List.sum_toFinset _ hnd]
      exact Finset.sum_congr rfl fun e he => hmult e (List.mem_toFinset.mp he)
    have hsum_real := weightedCopyGraph_sum_eq hnl_ne v (fun _ => (1 : ℝ))
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at hsum_real
    have hcard := weightedCopyGraph_card_le (G := { G.toMGraph with E := nl.toFinset })
      (by simpa [List.mem_toFinset] using hv)
    have hle_real : ((nl.map mult).sum : ℝ) ≤ 2 * (nl.length : ℝ) := by
      have h1 : ((nl.map mult).sum : ℝ) =
          ∑ e ∈ ({ G.toMGraph with E := nl.toFinset } : MGraph).E,
            (edgeMult { G.toMGraph with E := nl.toFinset } v e : ℝ) := by
        exact_mod_cast hsum_cast
      have hcard_eq : (({ G.toMGraph with E := nl.toFinset } : MGraph).E.card : ℝ) = (nl.length : ℝ) := by
        exact_mod_cast List.toFinset_card_of_nodup hnd
      linarith only [h1, hsum_real, hcard, hcard_eq]
    exact_mod_cast hle_real

/-- Every active vertex is an endpoint of some non-loop edge, so `(activeVertsList G).length ≤
2 * (nonloopEdges G).length` (unconditionally, even when `nonloopEdges G = []`). -/
theorem activeVertsList_length_le_two_mul_nl (G : IndexedGraph) :
    (activeVertsList G).length ≤ 2 * (nonloopEdges G).length := by
  let ep := (nonloopEdges G).flatMap fun e => [G.tail e, G.head e]
  have hsub : (activeVertsList G).toFinset ⊆ ep.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    obtain ⟨_, e, he, ht | hh⟩ := mem_activeVertsList_iff.mp hx
    · exact List.mem_flatMap.mpr ⟨e, he, by simp [ht]⟩
    · exact List.mem_flatMap.mpr ⟨e, he, by simp [hh]⟩
  have hep_len : ep.length = 2 * (nonloopEdges G).length := by
    dsimp only [ep]
    rw [List.length_flatMap]
    simp [List.map_const', Nat.mul_comm]
  calc (activeVertsList G).length
      = (activeVertsList G).toFinset.card := (List.toFinset_card_of_nodup (activeVertsList_nodup G)).symm
    _ ≤ ep.toFinset.card := Finset.card_le_card hsub
    _ ≤ ep.length := List.toFinset_card_le ep
    _ = 2 * (nonloopEdges G).length := hep_len

/-- Linear vertex and edge bounds on `buildGAug`: `G_aug` has at most `2 * nl.length ≤ 2 * G.m`
active vertices and at most `4 * nl.length ≤ 4 * G.m` total edges (`≤ 2 * nl.length` copy edges
plus `≤ 2 * nl.length` bridging edges). -/
theorem buildGAug_linear_bounds {G : IndexedGraph} {v : ℕ → ℝ} {V_list B : List ℕ}
    {mult w_orig : ℕ → ℕ}
    (hv : ∀ e ∈ nonloopEdges G, 0 < v e)
    (hmult : ∀ e ∈ nonloopEdges G,
      mult e = edgeMult { G.toMGraph with E := (nonloopEdges G).toFinset } v e)
    (hV_len : V_list.length ≤ (activeVertsList G).length)
    (hB_len : B.length ≤ V_list.length) :
    let nl := nonloopEdges G
    let G_aug := buildGAug G V_list B mult w_orig
    (nl.map mult).sum ≤ 2 * nl.length ∧
      V_list.length ≤ 2 * nl.length ∧
      B.length ≤ 2 * nl.length ∧
      (nl.map mult).sum + B.length ≤ 4 * nl.length ∧
      G_aug.n ≤ min G.n (2 * G.m) ∧
      G_aug.m ≤ 4 * G.m := by
  have hm1 := mult_sum_le_two_mul_nl hv hmult
  have hnl_m : (nonloopEdges G).length ≤ G.m := by
    dsimp only [nonloopEdges]
    exact (List.length_filter_le _ _).trans (by simp [List.length_range])
  have hact_2nl : (activeVertsList G).length ≤ 2 * (nonloopEdges G).length :=
    activeVertsList_length_le_two_mul_nl G
  have hact_n : (activeVertsList G).length ≤ G.n := by
    dsimp only [activeVertsList]
    exact (List.length_filter_le _ _).trans (by simp [List.length_range])
  have hV_2nl : V_list.length ≤ 2 * (nonloopEdges G).length := le_trans hV_len hact_2nl
  have hB_2nl : B.length ≤ 2 * (nonloopEdges G).length := le_trans hB_len hV_2nl
  refine ⟨hm1, hV_2nl, hB_2nl, by omega, ?_, ?_⟩
  · simp only [buildGAug_n]
    exact le_min (le_trans hV_len hact_n) (le_trans hV_2nl (by omega))
  · rw [buildGAug_m, copyEdgeList_length]
    omega

end MinCostFlow.WideWord
