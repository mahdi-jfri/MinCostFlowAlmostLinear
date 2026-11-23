module

public import MinCostFlow.HierPaths.InitProgFlatEnd
public import MinCostFlow.HierPaths.InitProgAppend

/-!
# Ordered chunks in a substitution pass

The input walk supplies the edge numbers in order. The terminal at index `i`
comes from following exactly the first `i` edges. The resulting chunks
concatenate to the substitution of the walk.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The terminal after the first `i` edges of the walk. -/
def initFlatTerminal (G : Graph) (u : ℕ) (es : List ℕ) (i : ℕ) : ℕ :=
  (es.take i).foldl (fun x e => otherEnd G.edges e x) u

theorem initFlatTerminal_succ (G : Graph) (u : ℕ) (es : List ℕ) (i : ℕ)
    (hi : i < es.length) :
    initFlatTerminal G u es (i + 1) =
      otherEnd G.edges (es[i]'hi) (initFlatTerminal G u es i) := by
  simp only [initFlatTerminal, List.take_succ_eq_append_getElem hi, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- The directed embedding appended at index `i`. -/
def initFlatChunk (G : Graph) (emb : ℕ → List ℕ) (u : ℕ) (es : List ℕ) (i : ℕ) : List ℕ :=
  initFlatEdgeWords G emb es[i]! (initFlatTerminal G u es i)

theorem initFlatPass_eq_substWalk (G : Graph) (emb : ℕ → List ℕ) (u : ℕ) (es : List ℕ) :
    initAppendPrefix (initFlatChunk G emb u es) es.length = substWalk G.edges emb u es := by
  induction es generalizing u with
  | nil => rfl
  | cons e es ih =>
    rw [List.length_cons]
    change (List.range (es.length + 1)).flatMap (initFlatChunk G emb u (e :: es)) = _
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    change initFlatEdgeWords G emb e u ++
      initAppendPrefix (initFlatChunk G emb (otherEnd G.edges e u) es) es.length = _
    rw [ih]
    rfl

theorem initFlatChunk_length (G : Graph) (emb : ℕ → List ℕ) (u : ℕ) (es : List ℕ) (i : ℕ) :
    (initFlatChunk G emb u es i).length = (emb es[i]!).length := by
  simp only [initFlatChunk, initFlatEdgeWords]
  split <;> simp

end MinCostFlow.HierPaths

end
