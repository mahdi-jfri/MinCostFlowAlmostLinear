module

public import MinCostFlow.DynSpanner.Program.DynSpannerInitCost

/-!
# The size of the canonical input of the sparsifier

The program calls the sparsifier (Theorem 8.1, page 39) on the flat buffer
`x = canonSparsifyInput H' J emb`, and runs the guest at the word size
`wordSize cw x = cw · (log₂(|x| + max x + 2) + 1)`. The cost of the translation
(`sparsifyTransCost_le`) is linear in `|x|` and in this word size. Here we bound both by the size
of `J` with its walks, `|V(J)| + |E(J)| · (length(emb) + 1)`, for any host graph `H'`:
* `canonSparsifyInput_length_le'`: `|x| ≤ 7 + 6 |E(J)| (length + 1)`, since the part of `H'`
  that is copied has at most `|E(J)| · length` edges and each walk takes at most `2 length + 3`
  words;
* `canonSparsifyInput_max_le`: every word of `x` is a length, an offset into `x`, or the index of
  a vertex or an edge of the copied graphs, so `max x ≤ |x| + 2 (|V(J)| + |E(J)| (length + 1))`;
* `canonSparsifyInput_size_le`: together, `|x| + max x + 2 ≤ 18 (|V(J)| + |E(J)| (length + 1) + 1)`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

public section

/-- The encoding of the walk of the `j`-th edge of `J` has at most `2 length + 3` words. -/
lemma embToCited_encode_length_le (H' J : MGraph) (emb : MinCostFlow.Embedding) {j : ℕ}
    (hj : j < J.m) :
    (Walk.encode (embToCited H' J emb j)).length ≤ 2 * emb.length J + 3 := by
  have heJ : (vertsOf J.E).getD j 0 ∈ J.E := getD_vertsOf_mem hj
  have hle : (emb ((vertsOf J.E).getD j 0)).length ≤ emb.length J :=
    Finset.le_sup (f := fun e => (emb e).length) heJ
  rw [walk_encode_length]
  unfold embToCited walkToCited
  dsimp only at hle ⊢
  split_ifs
  · simp [Walk.empty]
  · simp only [MGraph.walkVertices, List.length_map, List.length_cons]
    omega

/-- The walks of the canonical input take at most `|E(J)| (2 length + 3)` words. -/
lemma canonWalks_length_le (H' J : MGraph) (emb : MinCostFlow.Embedding) :
    (((List.range J.m).map (embToCited H' J emb)).flatMap Walk.encode).length ≤
      J.m * (2 * emb.length J + 3) := by
  have h : ∀ n ≤ J.m, (((List.range n).map (embToCited H' J emb)).flatMap Walk.encode).length ≤
      n * (2 * emb.length J + 3) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.map_append, List.map_singleton, List.flatMap_append,
        List.flatMap_singleton, List.length_append, Nat.succ_mul]
      have h1 := ih (by omega)
      have h2 := embToCited_encode_length_le H' J emb (j := k) (by omega)
      omega
  exact h _ le_rfl

/-- The length of the canonical input is linear in the size of `J` with its walks. -/
theorem canonSparsifyInput_length_le' (H' J : MGraph) (emb : MinCostFlow.Embedding) :
    (canonSparsifyInput H' J emb).length ≤ 7 + 6 * (J.m * (emb.length J + 1)) := by
  rw [canonSparsifyInput_length, toCitedH_m]
  have h1 := hEdges_length_le J emb
  have h2 := canonWalks_length_le H' J emb
  have e1 : J.m * (2 * emb.length J + 3) = 2 * (J.m * emb.length J) + 3 * J.m := by ring
  have e2 : J.m * (emb.length J + 1) = J.m * emb.length J + J.m := by ring
  rw [e1] at h2
  rw [e2]
  omega

private lemma mem_canonWalkOffsets_le' {a base : ℕ} :
    ∀ {ws : List Walk}, a ∈ canonWalkOffsets base ws →
      a ≤ base + (ws.flatMap Walk.encode).length
  | [], ha => by simp [canonWalkOffsets] at ha
  | w :: ws, ha => by
    simp only [canonWalkOffsets, List.mem_cons] at ha
    rcases ha with rfl | hrest
    · exact Nat.le_add_right _ _
    · have ih := mem_canonWalkOffsets_le' hrest
      simp only [List.flatMap_cons, List.length_append]
      omega

/-- Every word of the canonical input is at most `|x| + 2 (|V(J)| + |E(J)| (length + 1))`. -/
theorem canonSparsifyInput_max_le (H' J : MGraph) (emb : MinCostFlow.Embedding) :
    (canonSparsifyInput H' J emb).foldr max 0 ≤
      (canonSparsifyInput H' J emb).length + 2 * (J.n + J.m * (emb.length J + 1)) := by
  have hlen := canonSparsifyInput_length H' J emb
  have hHn : (toCitedH H' J emb).n ≤ J.n + J.m * (emb.length J + 1) := by
    have := hVerts_length_le H' J emb
    simpa [toCitedH] using this
  have hHm : (toCitedH H' J emb).m ≤ J.m * emb.length J := by
    rw [toCitedH_m]; exact hEdges_length_le J emb
  have hJn : (toCitedJ J).n = J.n := by simp [toCitedJ, vertsOf, MGraph.n]
  have hmono : J.m * emb.length J ≤ J.m * (emb.length J + 1) :=
    Nat.mul_le_mul_left _ (Nat.le_succ _)
  have hgH := graph_encode_length (toCitedH H' J emb)
  have hgJ := graph_encode_length (toCitedJ J)
  rw [toCitedJ_m] at hgJ
  have hv : ∀ v, (hVerts H' J emb).idxOf v ≤ (toCitedH H' J emb).n := fun v => by
    simpa [toCitedH] using List.idxOf_le_length (a := v) (l := hVerts H' J emb)
  have he : ∀ e, (hEdges J emb).idxOf e ≤ (toCitedH H' J emb).m := fun e => by
    rw [toCitedH_m]; exact List.idxOf_le_length
  refine foldr_max_le_of_forall fun a ha => ?_
  dsimp only [canonSparsifyInput] at ha
  simp only [List.mem_append] at ha
  rcases ha with (((ha | ha) | ha) | ha) | ha
  · -- The three offsets of the header.
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  · -- The copy of `H'`.
    simp only [Cited.Graph.encode, List.mem_cons, List.mem_flatMap] at ha
    rcases ha with rfl | rfl | ⟨ePair, hePair, hzPair⟩
    · omega
    · omega
    · simp only [toCitedH, List.mem_map] at hePair
      rcases hePair with ⟨e, -, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzPair
      rcases hzPair with rfl | rfl
      · have := hv (H'.tail e); omega
      · have := hv (H'.head e); omega
  · -- The copy of `J`.
    simp only [Cited.Graph.encode, List.mem_cons, List.mem_flatMap] at ha
    rcases ha with rfl | rfl | ⟨ePair, hePair, hzPair⟩
    · omega
    · rw [toCitedJ_m]; omega
    · simp only [toCitedJ, List.mem_map] at hePair
      rcases hePair with ⟨e, -, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzPair
      have hvJ : ∀ v, (vertsOf J.V).idxOf v ≤ J.n := fun v => by
        simpa [vertsOf, MGraph.n] using List.idxOf_le_length (a := v) (l := vertsOf J.V)
      rcases hzPair with rfl | rfl
      · have := hvJ (J.tail e); omega
      · have := hvJ (J.head e); omega
  · -- The offsets of the walks.
    have h := mem_canonWalkOffsets_le' ha
    rw [toCitedJ_m] at h
    omega
  · -- The walks.
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at ha
    rcases ha with ⟨w, ⟨j, hj, rfl⟩, hza⟩
    rw [toCitedJ_m] at hj
    have heJ : (vertsOf J.E).getD j 0 ∈ J.E := getD_vertsOf_mem hj
    have hle : (emb ((vertsOf J.E).getD j 0)).length ≤ emb.length J :=
      Finset.le_sup (f := fun e => (emb e).length) heJ
    have hm1 : emb.length J + 1 ≤ J.m * (emb.length J + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    unfold embToCited walkToCited at hza
    dsimp only at hza
    split_ifs at hza
    · simp only [Walk.encode, Walk.empty, List.length_nil, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false] at hza
      omega
    · rw [Walk.encode] at hza
      dsimp only at hza
      simp only [List.mem_cons, List.mem_append] at hza
      rcases hza with (h | h) | (h | h)
      · rw [h, List.length_map, MGraph.walkVertices, List.length_cons, List.length_map]
        omega
      · obtain ⟨v, -, rfl⟩ := List.mem_map.mp h
        have := hv v; omega
      · rw [h, List.length_map, List.length_map]
        omega
      · obtain ⟨e, -, rfl⟩ := List.mem_map.mp h
        have := he e; omega

/-- The length and the largest word of the canonical input, together. -/
theorem canonSparsifyInput_size_le (H' J : MGraph) (emb : MinCostFlow.Embedding) :
    (canonSparsifyInput H' J emb).length + (canonSparsifyInput H' J emb).foldr max 0 + 2 ≤
      18 * (J.n + J.m * (emb.length J + 1) + 1) := by
  have h1 := canonSparsifyInput_length_le' H' J emb
  have h2 := canonSparsifyInput_max_le H' J emb
  omega

end

end MinCostFlow.DynSpanner.Program
