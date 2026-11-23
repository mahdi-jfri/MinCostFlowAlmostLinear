module

public import MinCostFlow.LastLevelProgram.IndexGraph
import Mathlib.Tactic
import MinCostFlow.LSF.Walks

/-!
# Restoring graph names after the low-stretch tree call

Theorem 2.2 (page 7) returns original edge indices and may also return
bridges between components. Restore the names of original edges and
put every bridge above the largest live edge name.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WideWord

/-- Restore an original edge name or give a bridge a fresh name. -/
def treeEdgeName (G : MGraph) (i : ℕ) : ℕ :=
  if i < G.m then edgeName G i else G.E.sup id + 1 + (i - G.m)

/-- Recover the compact index of a restored tree edge. -/
def treeEdgeIndex (G : MGraph) (e : ℕ) : ℕ :=
  if e ∈ G.E then edgeIndex G e else G.m + (e - (G.E.sup id + 1))

/-- Only original edges restore to names in the source graph. -/
theorem treeEdgeName_mem_iff (G : MGraph) (i : ℕ) : treeEdgeName G i ∈ G.E ↔ i < G.m := by
  by_cases hi : i < G.m
  · simp [treeEdgeName, hi, edgeName_mem hi]
  · rw [treeEdgeName, ite_eq_right hi]
    refine ⟨fun hm => False.elim ?_, fun h => (hi h).elim⟩
    have hle := Finset.le_sup (f := id) hm
    change G.E.sup id + 1 + (i - G.m) ≤ G.E.sup id at hle
    omega

/-- Restoring tree edge names is injective, including on bridge indices. -/
theorem treeEdgeIndex_name (G : MGraph) (i : ℕ) :
    treeEdgeIndex G (treeEdgeName G i) = i := by
  by_cases hi : i < G.m
  · rw [treeEdgeIndex, ite_eq_left ((treeEdgeName_mem_iff G i).2 hi),
      treeEdgeName, ite_eq_left hi, edgeIndex_name hi]
  · have hout : treeEdgeName G i ∉ G.E := fun h => hi ((treeEdgeName_mem_iff G i).1 h)
    rw [treeEdgeIndex, ite_eq_right hout, treeEdgeName, ite_eq_right hi]
    omega

/-- Restore vertex and edge names in an LSST tree. -/
def restoreTreeNames (G T : MGraph) : MGraph where
  V := G.V
  E := T.E.image (treeEdgeName G)
  tail f := vertexName G (T.tail (treeEdgeIndex G f))
  head f := vertexName G (T.head (treeEdgeIndex G f))

/-- The original names of tree vertices and edges are injective on
the domains on which the indexed tree uses them. -/
theorem restoreTreeNames_injective (G : MGraph) :
    (∀ i < G.n, ∀ j < G.n, vertexName G i = vertexName G j → i = j) ∧
      Function.Injective (treeEdgeName G) := by
  refine ⟨?_, Function.LeftInverse.injective (treeEdgeIndex_name G)⟩
  intro i hi j hj hname
  rw [← vertexIndex_name hi, ← vertexIndex_name hj, hname]

/-- Restoring names preserves validity when all indexed vertices belong
to the compact vertex range. -/
theorem restoreTreeNames_valid {G T : MGraph} (hT : T.IsValid)
    (hvertices : T.V ⊆ Finset.range G.n) : (restoreTreeNames G T).IsValid := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨ht, hh⟩ := hT i hi
  change vertexName G (T.tail (treeEdgeIndex G (treeEdgeName G i))) ∈ G.V ∧
    vertexName G (T.head (treeEdgeIndex G (treeEdgeName G i))) ∈ G.V
  rw [treeEdgeIndex_name]
  exact ⟨vertexName_mem (Finset.mem_range.mp (hvertices ht)),
    vertexName_mem (Finset.mem_range.mp (hvertices hh))⟩

/-- Restore the edge names in an oriented walk. -/
def restoreWalkNames (G : MGraph) (P : List (ℕ × Bool)) : List (ℕ × Bool) :=
  P.map fun step => (treeEdgeName G step.1, step.2)

/-- Every indexed walk gives a walk with the restored vertex names. -/
theorem restoreWalkNames_isWalk {G T : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (h : T.IsWalk u v P) :
    (restoreTreeNames G T).IsWalk (vertexName G u) (vertexName G v) (restoreWalkNames G P) := by
  induction h with
  | nil _ => exact .nil _
  | @cons a z step rest hedge hsrc _ ih =>
    have hends : (restoreTreeNames G T).src (treeEdgeName G step.1, step.2) =
          vertexName G (T.src step) ∧
        (restoreTreeNames G T).dst (treeEdgeName G step.1, step.2) =
          vertexName G (T.dst step) := by
      rcases step with ⟨_, _ | _⟩ <;>
        simp [MGraph.src, MGraph.dst, restoreTreeNames, treeEdgeIndex_name]
    exact .cons (Finset.mem_image_of_mem _ hedge)
      (hends.1.trans (congrArg (vertexName G) hsrc)) (hends.2.symm ▸ ih)

/-- Vertex name restoration preserves connectivity. -/
theorem restoreTreeNames_connected {G T : MGraph} {u v : ℕ} (h : T.Connected u v) :
    (restoreTreeNames G T).Connected (vertexName G u) (vertexName G v) := by
  obtain ⟨P, hp⟩ := h
  exact ⟨restoreWalkNames G P, restoreWalkNames_isWalk hp⟩

private theorem pullBackWalk {G T : MGraph} (hT : T.IsValid)
    (hV : T.V ⊆ Finset.range G.n) {u v : ℕ} {P : List (ℕ × Bool)}
    (h : (restoreTreeNames G T).IsWalk u v P) :
    ∃ Q, T.IsWalk (vertexIndex G u) (vertexIndex G v) Q ∧ restoreWalkNames G Q = P := by
  induction h with
  | nil _ => exact ⟨[], .nil _, rfl⟩
  | @cons a z step rest he hsrc _ ih =>
    obtain ⟨i, hi, hiName⟩ := Finset.mem_image.mp he
    let old := (i, step.2)
    have ht := Finset.mem_range.mp (hV (hT i hi).1)
    have hh := Finset.mem_range.mp (hV (hT i hi).2)
    have hends : T.src old = vertexIndex G ((restoreTreeNames G T).src step) ∧
        T.dst old = vertexIndex G ((restoreTreeNames G T).dst step) := by
      rcases step with ⟨f, b⟩
      change treeEdgeName G i = f at hiName
      subst f
      cases b <;> simp [old, MGraph.src, MGraph.dst, restoreTreeNames, treeEdgeIndex_name,
        vertexIndex_name ht, vertexIndex_name hh]
    obtain ⟨Q, hQ, hQnames⟩ := ih
    refine ⟨old :: Q, .cons hi (hends.1.trans (congrArg (vertexIndex G) hsrc))
      (hends.2.symm ▸ hQ), ?_⟩
    simp only [restoreWalkNames, List.map_cons, old]
    rw [show Q.map (fun step => (treeEdgeName G step.1, step.2)) = rest from hQnames]
    exact congrArg (· :: rest) (Prod.ext hiName rfl)

/-- Restoring names carries an indexed spanning tree to a spanning tree
on the named vertex set. -/
theorem restoreTreeNames_spanning {G T : MGraph} (hT : T.IsSpanningTreeOn (Finset.range G.n)) :
    (restoreTreeNames G T).IsSpanningTreeOn G.V := by
  have hV : T.V ⊆ Finset.range G.n := hT.2.1.le
  refine ⟨⟨restoreTreeNames_valid hT.1.1 hV, ?_⟩, rfl, ?_⟩
  · intro P ⟨hne, hnodup, u, hwalk⟩
    obtain ⟨Q, hQ, hnames⟩ := pullBackWalk hT.1.1 hV hwalk
    apply hT.1.2 Q
    refine ⟨fun hnil => hne (hnames.symm.trans (by simp [hnil, restoreWalkNames])),
      ?_, vertexIndex G u, hQ⟩
    rw [← hnames, restoreWalkNames, List.map_map] at hnodup
    have hmap : (Q.map Prod.fst).map (treeEdgeName G) =
        Q.map (Prod.fst ∘ fun step => (treeEdgeName G step.1, step.2)) := by
      rw [List.map_map]
      rfl
    exact List.Nodup.of_map _ (hmap.symm ▸ hnodup)
  · intro u hu v hv
    have hc := hT.2.2 _ (Finset.mem_range.mpr (vertexIndex_lt hu))
      _ (Finset.mem_range.mpr (vertexIndex_lt hv))
    simpa only [vertexName_index hu, vertexName_index hv] using
      (restoreTreeNames_connected (G := G) hc)

/-- Every original edge of an indexed tree keeps its original endpoints
after restoring names. -/
theorem restoreTreeNames_endpoints {G T : MGraph} {ℓ v : ℕ → ℝ} {γ : ℝ}
    (hG : G.IsValid) (hT : LSF.IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    {i : ℕ} (hi : i < G.m) (hit : i ∈ T.E) :
    (restoreTreeNames G T).tail (treeEdgeName G i) = G.tail (edgeName G i) ∧
      (restoreTreeNames G T).head (treeEdgeName G i) = G.head (edgeName G i) := by
  have hi' : i ∈ (indexedGraph G).toMGraph.E := Finset.mem_range.mpr hi
  have hends := hT.2.1 i hit hi'
  have hend' := indexedGraph_endpoints hG hi
  simpa only [restoreTreeNames, treeEdgeIndex_name, hends.1, hends.2, IndexedGraph.toMGraph] using hend'

/-- The vertex list of a restored walk is the restored original vertex list. -/
theorem restoreWalkNames_vertices (G T : MGraph) (u : ℕ) (P : List (ℕ × Bool)) :
    (restoreTreeNames G T).walkVertices (vertexName G u) (restoreWalkNames G P) =
      (T.walkVertices u P).map (vertexName G) := by
  simp only [MGraph.walkVertices, restoreWalkNames, List.map_map, List.map_cons]
  congr 1
  apply List.map_congr_left
  rintro ⟨e, b⟩ _
  cases b <;> simp [MGraph.dst, restoreTreeNames, treeEdgeIndex_name]

/-- Restoring the names of a path preserves its distinct vertices. -/
theorem restoreWalkNames_isPath {G T : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hT : T.IsValid) (hV : T.V ⊆ Finset.range G.n) (hu : u ∈ T.V)
    (hP : T.IsPath u v P) :
    (restoreTreeNames G T).IsPath (vertexName G u) (vertexName G v) (restoreWalkNames G P) := by
  refine ⟨restoreWalkNames_isWalk hP.1, ?_⟩
  rw [restoreWalkNames_vertices, List.nodup_map_iff_inj_on hP.2]
  intro a ha b hb hab
  have hvertices := (LSF.IsWalk_vertices_mem hT hu hP.1).2
  exact (restoreTreeNames_injective G).1 a (Finset.mem_range.mp (hV (hvertices a ha)))
    b (Finset.mem_range.mp (hV (hvertices b hb))) hab

/-- Name restoration commutes with taking the edge set of a walk. -/
theorem restoreWalkNames_edges (G : MGraph) (P : List (ℕ × Bool)) :
    walkEdges (restoreWalkNames G P) = (walkEdges P).image (treeEdgeName G) := by
  ext e
  simp only [walkEdges, restoreWalkNames, List.map_map, List.mem_toFinset,
    List.mem_map, Finset.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨step, hstep, rfl⟩
    exact ⟨step.1, ⟨step, hstep, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨step, hstep, rfl⟩, rfl⟩
    exact ⟨step, hstep, rfl⟩

end MinCostFlow.LastLevelProgram
