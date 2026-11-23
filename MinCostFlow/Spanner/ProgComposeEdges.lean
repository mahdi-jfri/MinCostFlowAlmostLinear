module

public import MinCostFlow.Spanner.Embedding

@[expose] public section

/-!
# The Edge List of a Composed Walk

The last output of `Sparsify` is the composed embedding `compose W embWJtilde embJW`. A program
for it can write the edges of the composed walk one step at a time, because the edge list of
`P.append Q` is always `P.edges ++ Q.edges`, whatever the empty cases of `Walk.append` do. This
file proves that, and gives the edge list of `composeAux` as a list of steps
(`composeAux_edges`).
-/

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

namespace Walk

/-- The edge list of `P.append Q` is `P.edges ++ Q.edges`. -/
lemma append_edges (P Q : Walk) : (P.append Q).edges = P.edges ++ Q.edges := by
  unfold append
  by_cases hP : P.edges.isEmpty
  · rw [ite_eq_left hP, List.isEmpty_iff.mp hP, List.nil_append]
  · rw [ite_eq_right hP]
    by_cases hQ : Q.edges.isEmpty
    · rw [ite_eq_left hQ, List.isEmpty_iff.mp hQ, List.append_nil]
    · rw [ite_eq_right hQ]

end Walk

/-- One step of `composeAux`: the walk of edge `j` of `B`, turned around when edge `j` of `B` does
not go from `u` to `v`. -/
def composeStep (B : Graph) (embBC : ℕ → Walk) (u v j : ℕ) : Walk :=
  if (B.edges.getD j (0, 0)).1 = u ∧ (B.edges.getD j (0, 0)).2 = v then embBC j
  else (embBC j).reverse

/-- The edges of `composeAux B embBC vs js` are the edges of the steps along `vs` and `js`, one
step after the other. -/
lemma composeAux_edges (B : Graph) (embBC : ℕ → Walk) :
    ∀ (vs js : List ℕ), (composeAux B embBC vs js).edges =
      (List.range (min (vs.length - 1) js.length)).flatMap fun i =>
        (composeStep B embBC (vs.getD i 0) (vs.getD (i + 1) 0) (js.getD i 0)).edges
  | u :: v :: vs, j :: js => by
    rw [composeAux, Walk.append_edges, composeAux_edges B embBC (v :: vs) js]
    simp only [List.length_cons, Nat.add_sub_cancel]
    rw [show min (vs.length + 1) (js.length + 1) = min vs.length js.length + 1 by omega,
      List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.getD_cons_zero, List.getD_cons_succ, composeStep]
  | [], _ => by simp [composeAux, Walk.empty]
  | [_], _ => by simp [composeAux, Walk.empty]
  | _ :: _ :: _, [] => by simp [composeAux, Walk.empty]

/-- The walk `S₀.append (S₁.append (⋯ (S_{k-1}.append empty)))`, which is what `composeAux`
builds from its steps (`composeAux_eq_foldApp`). -/
def foldApp : List Walk → Walk
  | [] => Walk.empty
  | S :: rest => S.append (foldApp rest)

lemma foldApp_edges : ∀ l : List Walk, (foldApp l).edges = l.flatMap Walk.edges
  | [] => rfl
  | S :: rest => by rw [foldApp, Walk.append_edges, foldApp_edges rest, List.flatMap_cons]

/-- `composeAux` is the fold of its steps. -/
lemma composeAux_eq_foldApp (B : Graph) (embBC : ℕ → Walk) :
    ∀ (vs js : List ℕ), composeAux B embBC vs js =
      foldApp ((List.range (min (vs.length - 1) js.length)).map fun i =>
        composeStep B embBC (vs.getD i 0) (vs.getD (i + 1) 0) (js.getD i 0))
  | u :: v :: vs, j :: js => by
    rw [composeAux, composeAux_eq_foldApp B embBC (v :: vs) js]
    simp only [List.length_cons, Nat.add_sub_cancel]
    rw [show min (vs.length + 1) (js.length + 1) = min vs.length js.length + 1 by omega,
      List.range_succ_eq_map, List.map_cons, List.map_map, foldApp]
    simp only [List.getD_cons_zero, List.getD_cons_succ, composeStep, Function.comp_def]
  | [], _ => by simp [composeAux, foldApp]
  | [_], _ => by simp [composeAux, foldApp]
  | _ :: _ :: _, [] => by simp [composeAux, foldApp]

/-- The vertex list of a list of walks whose edge lists are not empty: the vertices of the first
walk, then the vertices of each later walk without its first vertex. -/
def joinVerts : List Walk → List ℕ
  | [] => []
  | S :: rest => S.verts ++ rest.flatMap fun T => T.verts.tail

/-- The vertices of `foldApp l` come from the walks of `l` with at least one edge. The hypothesis
says that such walks have at least one vertex, which holds for every valid walk. -/
lemma foldApp_verts : ∀ (l : List Walk), (∀ S ∈ l, S.edges ≠ [] → S.verts ≠ []) →
    (foldApp l).verts = joinVerts (l.filter fun S => !S.edges.isEmpty)
  | [], _ => rfl
  | S :: rest, hv => by
    have ih := foldApp_verts rest fun T hT => hv T (List.mem_cons_of_mem _ hT)
    rw [foldApp, Walk.append]
    by_cases hS : S.edges.isEmpty
    · rw [ite_eq_left hS, List.filter_cons_of_neg (by simp [hS])]
      exact ih
    · rw [ite_eq_right hS, List.filter_cons_of_pos (by simp [hS])]
      by_cases hR : (foldApp rest).edges.isEmpty
      · -- No later walk has an edge.
        rw [ite_eq_left hR]
        have hnil : rest.filter (fun S => !S.edges.isEmpty) = [] := by
          rw [List.filter_eq_nil_iff]
          intro T hT
          rw [foldApp_edges, List.isEmpty_iff, List.flatMap_eq_nil_iff] at hR
          simp [hR T hT]
        simp [joinVerts, hnil]
      · rw [ite_eq_right hR]
        dsimp only
        rw [ih]
        obtain ⟨T, rest', hTr⟩ : ∃ T rest', rest.filter (fun S => !S.edges.isEmpty) =
            T :: rest' := by
          cases hf : rest.filter (fun S => !S.edges.isEmpty) with
          | nil =>
            exfalso; apply hR
            rw [foldApp_edges, List.isEmpty_iff, List.flatMap_eq_nil_iff]
            intro T hT
            have := List.filter_eq_nil_iff.mp hf T hT
            simpa using this
          | cons T rest' => exact ⟨T, rest', rfl⟩
        have hTmem : T ∈ rest.filter (fun S => !S.edges.isEmpty) := by rw [hTr]; simp
        rw [List.mem_filter] at hTmem
        have hTv : T.verts ≠ [] := hv T (List.mem_cons_of_mem _ hTmem.1)
          (by simpa using hTmem.2)
        rw [hTr]
        simp only [joinVerts, List.flatMap_cons]
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hTv
        rw [hx, List.cons_append, List.tail_cons, List.tail_cons]

/-- Adding one walk at the end of `joinVerts`: the walk gives all its vertices when it is the
first walk, and all but its first vertex otherwise. A program can build the vertex list of a
composed walk one step at a time with this. -/
lemma joinVerts_append_single (L : List Walk) (S : Walk) :
    joinVerts (L ++ [S]) = if L = [] then S.verts else joinVerts L ++ S.verts.tail := by
  cases L with
  | nil => simp [joinVerts]
  | cons T rest => simp [joinVerts, List.flatMap_append]

/-- The walks with at least one edge among the first `k + 1` steps. -/
lemma filter_range_succ (f : ℕ → Walk) (k : ℕ) :
    ((List.range (k + 1)).map f).filter (fun S => !S.edges.isEmpty) =
      ((List.range k).map f).filter (fun S => !S.edges.isEmpty) ++
        (if (f k).edges.isEmpty then [] else [f k]) := by
  rw [List.range_succ, List.map_append, List.filter_append]
  by_cases h : (f k).edges.isEmpty <;> simp [h]

end MinCostFlow.Spanner
