module

public import MinCostFlow.Machine.WideWord.LSSTModelBase
public import Mathlib.Data.Finset.Sort

/-!
# Compact indexing for last-level tree calls

Theorem 2.2 (page 7) uses consecutive edge and vertex indices. Sorting
the live names gives bijections to those indices and makes the array
order independent of the input graph's sparse-set order.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WideWord

/-- The vertex index in increasing name order. -/
def vertexIndex (G : MGraph) (v : ℕ) : ℕ :=
  if hv : v ∈ G.V then ((G.V.orderIsoOfFin rfl).symm ⟨v, hv⟩ : ℕ) else 0

/-- The original edge name at a compact index, with zero outside the array. -/
def edgeName (G : MGraph) (i : ℕ) : ℕ :=
  if hi : i < G.m then (G.E.orderIsoOfFin rfl ⟨i, hi⟩ : ℕ) else 0

/-- The original vertex name at a compact index, with zero outside the array. -/
def vertexName (G : MGraph) (i : ℕ) : ℕ :=
  if hi : i < G.n then (G.V.orderIsoOfFin rfl ⟨i, hi⟩ : ℕ) else 0

/-- Compact arrays for the representative graph. -/
def indexedGraph (G : MGraph) : IndexedGraph where
  n := G.n
  m := G.m
  tail i := vertexIndex G (G.tail (edgeName G i))
  head i := vertexIndex G (G.head (edgeName G i))

/-- The compact edge index in increasing name order. -/
def edgeIndex (G : MGraph) (e : ℕ) : ℕ :=
  if he : e ∈ G.E then ((G.E.orderIsoOfFin rfl).symm ⟨e, he⟩ : ℕ) else 0

/-- Every live edge index decodes to an edge of the named graph. -/
theorem edgeName_mem {G : MGraph} {i : ℕ} (hi : i < G.m) : edgeName G i ∈ G.E := by
  rw [edgeName, dite_eq_left hi]
  exact (G.E.orderIsoOfFin rfl ⟨i, hi⟩).property

/-- The compact index of the edge at a live position is that position. -/
theorem edgeIndex_name {G : MGraph} {i : ℕ} (hi : i < G.m) :
    edgeIndex G (edgeName G i) = i := by
  let iso : Fin G.m ≃o G.E := G.E.orderIsoOfFin rfl
  have hname : edgeName G i = (iso ⟨i, hi⟩ : ℕ) := by
    rw [edgeName, dite_eq_left hi]
    rfl
  rw [hname, edgeIndex, dite_eq_left (iso ⟨i, hi⟩).property]
  exact congrArg Fin.val (iso.symm_apply_apply ⟨i, hi⟩)

/-- The index of a live vertex lies in the vertex array. -/
theorem vertexIndex_lt {G : MGraph} {v : ℕ} (hv : v ∈ G.V) : vertexIndex G v < G.n := by
  rw [vertexIndex, dite_eq_left hv]
  exact ((G.V.orderIsoOfFin rfl).symm ⟨v, hv⟩).isLt

/-- Decoding the compact index recovers the original vertex name. -/
theorem vertexName_index {G : MGraph} {v : ℕ} (hv : v ∈ G.V) :
    vertexName G (vertexIndex G v) = v := by
  let iso : Fin G.n ≃o G.V := G.V.orderIsoOfFin rfl
  have hi : vertexIndex G v = (iso.symm ⟨v, hv⟩ : ℕ) := by
    rw [vertexIndex, dite_eq_left hv]
    rfl
  rw [hi]
  unfold vertexName
  rw [dite_eq_left (iso.symm ⟨v, hv⟩).isLt]
  exact congrArg Subtype.val (iso.apply_symm_apply ⟨v, hv⟩)

/-- Each live compact vertex index has a name in the graph. -/
theorem vertexName_mem {G : MGraph} {i : ℕ} (hi : i < G.n) :
    vertexName G i ∈ G.V := by
  rw [vertexName, dite_eq_left hi]
  exact (G.V.orderIsoOfFin rfl ⟨i, hi⟩).property

/-- The compact index of the vertex at a live position is that position. -/
theorem vertexIndex_name {G : MGraph} {i : ℕ} (hi : i < G.n) :
    vertexIndex G (vertexName G i) = i := by
  let iso : Fin G.n ≃o G.V := G.V.orderIsoOfFin rfl
  have hname : vertexName G i = (iso ⟨i, hi⟩ : ℕ) := by
    rw [vertexName, dite_eq_left hi]
    rfl
  rw [hname, vertexIndex, dite_eq_left (iso ⟨i, hi⟩).property]
  exact congrArg Fin.val (iso.symm_apply_apply ⟨i, hi⟩)

/-- The graph arrays meet the graph validity premise of Theorem 2.2. -/
theorem indexedGraph_valid {G : MGraph} (hG : G.IsValid) (hne : G.V.Nonempty) :
    (indexedGraph G).Valid := by
  refine ⟨Finset.card_pos.mpr hne, fun i hi => ?_⟩
  have he := hG _ (edgeName_mem hi)
  exact ⟨vertexIndex_lt he.1, vertexIndex_lt he.2⟩

/-- The compact tail and head recover the original edge's endpoints. -/
theorem indexedGraph_endpoints {G : MGraph} (hG : G.IsValid) {i : ℕ} (hi : i < G.m) :
    vertexName G ((indexedGraph G).tail i) = G.tail (edgeName G i) ∧
      vertexName G ((indexedGraph G).head i) = G.head (edgeName G i) := by
  have he := hG _ (edgeName_mem hi)
  exact ⟨vertexName_index he.1, vertexName_index he.2⟩

/-- Every live edge occurs at its compact index in the name array. -/
theorem edgeIndex_live {G : MGraph} {e : ℕ} (he : e ∈ G.E) :
    edgeIndex G e < G.m ∧ edgeName G (edgeIndex G e) = e := by
  let iso : Fin G.m ≃o G.E := G.E.orderIsoOfFin rfl
  have hidx : edgeIndex G e = (iso.symm ⟨e, he⟩ : ℕ) := by
    rw [edgeIndex, dite_eq_left he]
    rfl
  rw [hidx]
  refine ⟨(iso.symm ⟨e, he⟩).isLt, ?_⟩
  rw [edgeName, dite_eq_left (iso.symm ⟨e, he⟩).isLt]
  exact congrArg Subtype.val (iso.apply_symm_apply ⟨e, he⟩)

/-- A walk keeps its endpoints and edge orientations under compact
indexing, as required by the connected LSST traversal. -/
theorem indexedGraph_walk {G : MGraph} {u v : ℕ} {path : List (ℕ × Bool)}
    (hp : G.IsWalk u v path) :
    (indexedGraph G).toMGraph.IsWalk (vertexIndex G u) (vertexIndex G v)
      (path.map fun e => (edgeIndex G e.1, e.2)) := by
  induction hp with
  | nil => exact .nil _
  | @cons a z x rest he hs _ ih =>
    obtain ⟨hi, heq⟩ := edgeIndex_live he
    have hx : edgeIndex G x.1 ∈ (indexedGraph G).toMGraph.E := Finset.mem_range.mpr hi
    have hsrc : (indexedGraph G).toMGraph.src (edgeIndex G x.1, x.2) =
        vertexIndex G (G.src x) := by
      cases x with
      | mk e dir => cases dir <;> simp [MGraph.src, IndexedGraph.toMGraph, indexedGraph, heq]
    have hdst : (indexedGraph G).toMGraph.dst (edgeIndex G x.1, x.2) =
        vertexIndex G (G.dst x) := by
      cases x with
      | mk e dir => cases dir <;> simp [MGraph.dst, IndexedGraph.toMGraph, indexedGraph, heq]
    exact .cons hx (hsrc.trans (congrArg (vertexIndex G) hs)) (hdst.symm ▸ ih)

/-- Connectivity among the live vertices is preserved by the compact
array representation. -/
theorem indexedGraph_connected {G : MGraph}
    (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) :
    ∀ u ∈ (indexedGraph G).toMGraph.V, ∀ v ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected u v := by
  intro u hu v hv
  have hu' : u < G.n := Finset.mem_range.mp hu
  have hv' : v < G.n := Finset.mem_range.mp hv
  obtain ⟨path, hp⟩ := hconn _ (vertexName_mem hu') _ (vertexName_mem hv')
  exact ⟨_, by simpa only [vertexIndex_name hu', vertexIndex_name hv'] using indexedGraph_walk hp⟩

end MinCostFlow.LastLevelProgram
