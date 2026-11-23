module

public import MinCostFlow.ExpanderDecomp.Embedding
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Substituting walks through embeddings

The hierarchy of the path data structure stores, for every edge of a child host, a walk in its
parent host. To read a walk of a deep host as a walk of the root host, we replace each edge `j` by
its stored walk `emb j`, reversed when the walk crosses `j` backwards. This file defines that
substitution for edge-number walks (`ExpanderDecomp.IsEdgeWalk`) and proves the facts that the
composition part of the flattening bounds (`Flat.lean`) needs.

* `substWalk_isEdgeWalk`: the substituted walk is a walk of the lower graph with the same ends.
* `length_substWalk_le`: its length is at most the length of the walk times the longest `emb j`.
* `occLoad_substFamily_le`: if the edges of the upper graph occur at most `r₁` times in total in a
  family of walks, and an edge `i` of the lower graph occurs at most `r₂` times in total in the
  walks `emb j`, then `i` occurs at most `r₁ r₂` times in the substituted family. The proof counts
  pairs made of an occurrence of `j` in the family and an occurrence of `i` in `emb j`.
* `substDown_isEdgeWalk`, `length_substDown_le`, `occLoad_substDownFamily_le`: the same along a
  chain of embeddings, with product bounds. The load of the family itself enters once.

We count occurrences with `List.count`, not walks: `ExpanderDecomp.congestion` counts walks.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The end of edge `j` of `E` that a walk reaches when it enters `j` at `x`: the second end when
`x` is the first end, and the first end otherwise. -/
def otherEnd (E : List (ℕ × ℕ)) (j x : ℕ) : ℕ :=
  if (edgeAt E j).1 = x then (edgeAt E j).2 else (edgeAt E j).1

/-- Substitute the edge walk `es` of the edge list `E`, started at `x`, through `emb`: each edge
`j` becomes `emb j` when the walk crosses `j` from its first end, and the reverse of `emb j`
otherwise. -/
def substWalk (E : List (ℕ × ℕ)) (emb : ℕ → List ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | x, j :: es =>
    (if (edgeAt E j).1 = x then emb j else (emb j).reverse) ++ substWalk E emb (otherEnd E j x) es

/-- The number of occurrences of edge number `i` in a family of walks, each given by its start
vertex and its edge list. -/
def occLoad (F : List (ℕ × List ℕ)) (i : ℕ) : ℕ :=
  (F.map fun p => p.2.count i).sum

/-- Substitute every walk of a family through `emb`, keeping the start vertices. -/
def substFamily (E : List (ℕ × ℕ)) (emb : ℕ → List ℕ) (F : List (ℕ × List ℕ)) :
    List (ℕ × List ℕ) :=
  F.map fun p => (p.1, substWalk E emb p.1 p.2)

/-- The number of steps of the substitution: one per edge of the input walk and one per edge of
the output walk. -/
def substSteps (emb : ℕ → List ℕ) (es : List ℕ) : ℕ :=
  es.length + (es.map fun j => (emb j).length).sum

/-- Substitution along a chain of edge lists `E 0, E 1, …, E t`, where `emb k j` is a walk in
`E k` for edge `j` of `E (k + 1)`. A walk of `E t` is substituted first through `emb (t - 1)`,
then down to `E 0`. -/
def substDown (E : ℕ → List (ℕ × ℕ)) (emb : ℕ → ℕ → List ℕ) : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, es => es
  | t + 1, x, es => substDown E emb t x (substWalk (E (t + 1)) (emb t) x es)

/-- Substitute every walk of a family down a chain of length `t`, keeping the start vertices. -/
def substDownFamily (E : ℕ → List (ℕ × ℕ)) (emb : ℕ → ℕ → List ℕ) (t : ℕ)
    (F : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  F.map fun p => (p.1, substDown E emb t p.1 p.2)

/-- `emb` is a chain of embeddings of length `t`: for every `k < t`, each edge `j` of `E (k + 1)`
goes to a walk `emb k j` of `E k` between the two ends of `j`. -/
def IsEmbChain (E : ℕ → List (ℕ × ℕ)) (emb : ℕ → ℕ → List ℕ) (t : ℕ) : Prop :=
  ∀ k < t, ∀ j < (E (k + 1)).length,
    IsEdgeWalk (E k) (edgeAt (E (k + 1)) j).1 (edgeAt (E (k + 1)) j).2 (emb k j)

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-! ### Edge walks: appending and reversing -/

/-- Two edge walks that meet at `w` append to one walk. -/
theorem isEdgeWalk_append {E : List (ℕ × ℕ)} {u w v : ℕ} {l₁ l₂ : List ℕ}
    (h₁ : IsEdgeWalk E u w l₁) (h₂ : IsEdgeWalk E w v l₂) : IsEdgeWalk E u v (l₁ ++ l₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons hj hend _ ih => exact IsEdgeWalk.cons hj hend (ih h₂)

/-- A single edge is a walk between its two ends, in either direction. -/
theorem isEdgeWalk_single {E : List (ℕ × ℕ)} {u x j : ℕ} (hj : j < E.length)
    (hend : ((edgeAt E j).1 = u ∧ (edgeAt E j).2 = x) ∨
      ((edgeAt E j).1 = x ∧ (edgeAt E j).2 = u)) : IsEdgeWalk E u x [j] :=
  IsEdgeWalk.cons hj hend (IsEdgeWalk.nil x)

/-- The reverse of an edge walk from `u` to `v` is an edge walk from `v` to `u`. -/
theorem isEdgeWalk_reverse {E : List (ℕ × ℕ)} {u v : ℕ} {l : List ℕ}
    (h : IsEdgeWalk E u v l) : IsEdgeWalk E v u l.reverse := by
  induction h with
  | nil u => exact IsEdgeWalk.nil u
  | cons hj hend _ ih =>
    rw [List.reverse_cons]
    refine isEdgeWalk_append ih (isEdgeWalk_single hj ?_)
    rcases hend with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- In a walk that starts with edge `j` at `u`, the second vertex is `otherEnd E j u`. -/
theorem isEdgeWalk_tail_otherEnd {E : List (ℕ × ℕ)} {u v j : ℕ} {es : List ℕ}
    (h : IsEdgeWalk E u v (j :: es)) : IsEdgeWalk E (otherEnd E j u) v es := by
  cases h with
  | cons hj hend hrest =>
    rename_i x
    have hx : otherEnd E j u = x := by
      unfold otherEnd
      rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [h1, h2, ite_true]
      · split_ifs with h3
        · rw [h2, ← h3, h1]
        · exact h1
    rw [hx]
    exact hrest

/-! ### One substitution -/

/-- **Substitution keeps walks.** If `es` is a walk of `EW` from `u` to `v`, and each of its edges
`j` goes to a walk `emb j` of `EK` between the ends of `j`, then the substituted walk is a walk of
`EK` from `u` to `v`. -/
theorem substWalk_isEdgeWalk {EW EK : List (ℕ × ℕ)} {emb : ℕ → List ℕ} {u v : ℕ} {es : List ℕ}
    (hW : IsEdgeWalk EW u v es)
    (hemb : ∀ j ∈ es, IsEdgeWalk EK (edgeAt EW j).1 (edgeAt EW j).2 (emb j)) :
    IsEdgeWalk EK u v (substWalk EW emb u es) := by
  induction es generalizing u with
  | nil =>
    cases hW
    exact IsEdgeWalk.nil _
  | cons j es ih =>
    have hrest := isEdgeWalk_tail_otherEnd hW
    have hihr := ih hrest fun j' hj' => hemb j' (List.mem_cons_of_mem _ hj')
    have hj := hemb j List.mem_cons_self
    unfold substWalk
    refine isEdgeWalk_append ?_ hihr
    cases hW with
    | cons _ hend _ =>
      unfold otherEnd
      split_ifs with h1
      · rw [← h1]
        exact hj
      · have h2 : (edgeAt EW j).2 = u := by
          rcases hend with ⟨h, _⟩ | ⟨_, h⟩
          · exact absurd h h1
          · exact h
        rw [← h2]
        exact isEdgeWalk_reverse hj

/-- Every edge of the substituted walk lies on `emb j` for an edge `j` of the walk. -/
theorem mem_substWalk {E : List (ℕ × ℕ)} {emb : ℕ → List ℕ} {x i : ℕ} {es : List ℕ}
    (hi : i ∈ substWalk E emb x es) : ∃ j ∈ es, i ∈ emb j := by
  induction es generalizing x with
  | nil => simp [substWalk] at hi
  | cons j es ih =>
    unfold substWalk at hi
    rcases List.mem_append.mp hi with h | h
    · refine ⟨j, List.mem_cons_self, ?_⟩
      split_ifs at h
      · exact h
      · exact List.mem_reverse.mp h
    · obtain ⟨j', hj', hi'⟩ := ih h
      exact ⟨j', List.mem_cons_of_mem _ hj', hi'⟩

/-- Substitution through an embedding on `X` (`ExpanderDecomp.IsEmbeddingOn`): a walk of `W` whose
edges have both ends in `X` becomes a walk of `K` with the same ends whose edges have both ends in
`X`. -/
theorem substWalk_isEdgeWalk_of_embedding {W K : Graph} {X : Finset ℕ} {emb : ℕ → List ℕ}
    (hemb : IsEmbeddingOn W K X emb) {u v : ℕ} {es : List ℕ} (hW : IsEdgeWalk W.edges u v es)
    (hin : ∀ j ∈ es, insideB X (edgeAt W.edges j) = true) :
    IsEdgeWalk K.edges u v (substWalk W.edges emb u es) ∧
      ∀ i ∈ substWalk W.edges emb u es, insideB X (edgeAt K.edges i) = true := by
  refine ⟨substWalk_isEdgeWalk hW fun j hj => (hemb j (hW.lt_length j hj) (hin j hj)).1, ?_⟩
  intro i hi
  obtain ⟨j, hj, hij⟩ := mem_substWalk hi
  exact (hemb j (hW.lt_length j hj) (hin j hj)).2 i hij

/-- The length of the substituted walk is the sum of the lengths of the walks `emb j` over the
edges `j` of the walk, counted with repetition. -/
theorem length_substWalk (E : List (ℕ × ℕ)) (emb : ℕ → List ℕ) (x : ℕ) (es : List ℕ) :
    (substWalk E emb x es).length = (es.map fun j => (emb j).length).sum := by
  induction es generalizing x with
  | nil => simp [substWalk]
  | cons j es ih =>
    unfold substWalk
    rw [List.length_append, ih, List.map_cons, List.sum_cons]
    split_ifs <;> simp

/-- A sum over a list of terms that are each at most `L` is at most `L` times its length. -/
private theorem sum_map_le_length_mul {l : List ℕ} {f : ℕ → ℕ} {L : ℕ}
    (h : ∀ j ∈ l, f j ≤ L) : (l.map f).sum ≤ l.length * L := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
    omega

/-- **Length of a substitution.** If every walk `emb j` for an edge `j` of `es` has at most `L`
edges, the substituted walk has at most `|es| · L` edges. -/
theorem length_substWalk_le {E : List (ℕ × ℕ)} {emb : ℕ → List ℕ} {x L : ℕ} {es : List ℕ}
    (hL : ∀ j ∈ es, (emb j).length ≤ L) : (substWalk E emb x es).length ≤ es.length * L := by
  rw [length_substWalk]
  exact sum_map_le_length_mul hL

/-- The step count of the substitution is at most `|es| · (1 + L)` when every walk `emb j` for an
edge `j` of `es` has at most `L` edges. -/
theorem substSteps_le {emb : ℕ → List ℕ} {L : ℕ} {es : List ℕ}
    (hL : ∀ j ∈ es, (emb j).length ≤ L) : substSteps emb es ≤ es.length * (1 + L) := by
  unfold substSteps
  have := sum_map_le_length_mul hL
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The number of occurrences of `i` in the substituted walk is the sum, over the edges `j` of the
walk counted with repetition, of the occurrences of `i` in `emb j`. Reversal does not change a
count. -/
theorem count_substWalk (E : List (ℕ × ℕ)) (emb : ℕ → List ℕ) (x : ℕ) (es : List ℕ) (i : ℕ) :
    (substWalk E emb x es).count i = (es.map fun j => (emb j).count i).sum := by
  induction es generalizing x with
  | nil => simp [substWalk]
  | cons j es ih =>
    unfold substWalk
    rw [List.count_append, ih, List.map_cons, List.sum_cons]
    split_ifs <;> simp [List.count_reverse]

/-- A sum over a list of numbers below `N` regroups by value: `∑_{j ∈ l} g j` equals
`∑_{j < N} (count of j in l) · g j`. -/
theorem sum_map_eq_sum_range_count {l : List ℕ} {N : ℕ} (hl : ∀ j ∈ l, j < N) (g : ℕ → ℕ) :
    (l.map g).sum = ∑ j ∈ Finset.range N, l.count j * g j := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih fun j hj => hl j (List.mem_cons_of_mem _ hj)]
    have ha : a < N := hl a List.mem_cons_self
    have hsplit : ∀ j, (a :: l).count j * g j =
        l.count j * g j + (if a = j then g j else 0) := by
      intro j
      rw [List.count_cons]
      by_cases h : a = j
      · subst h
        simp [Nat.add_mul]
      · have : (a == j) = false := beq_eq_false_iff_ne.mpr h
        simp [this, h]
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp [ha, Nat.add_comm]

/-- The load of the substituted family regroups by the edges of the upper graph:
`load(i) = ∑_{j < N} load_F(j) · count_i(emb j)`. -/
theorem occLoad_substFamily {E : List (ℕ × ℕ)} {emb : ℕ → List ℕ} {F : List (ℕ × List ℕ)} {N : ℕ}
    (hF : ∀ p ∈ F, ∀ j ∈ p.2, j < N) (i : ℕ) :
    occLoad (substFamily E emb F) i =
      ∑ j ∈ Finset.range N, occLoad F j * (emb j).count i := by
  induction F with
  | nil => simp [occLoad, substFamily]
  | cons p F ih =>
    have ih' := ih fun q hq => hF q (List.mem_cons_of_mem _ hq)
    unfold occLoad substFamily at ih' ⊢
    rw [List.map_cons, List.map_cons, List.sum_cons, ih']
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    rw [Finset.sum_add_distrib, count_substWalk,
      sum_map_eq_sum_range_count (hF p List.mem_cons_self)]

/-- **The load bound of flattened walks (composition).** Let the walks of `F` use only edges below `N`. If
each edge `j < N` occurs at most `r₁` times in total in `F`, and edge `i` occurs at most `r₂`
times in total in the walks `emb j` for `j < N`, then `i` occurs at most `r₁ r₂` times in the
substituted family. -/
theorem occLoad_substFamily_le {E : List (ℕ × ℕ)} {emb : ℕ → List ℕ} {F : List (ℕ × List ℕ)}
    {N r₁ r₂ i : ℕ} (hF : ∀ p ∈ F, ∀ j ∈ p.2, j < N) (hr₁ : ∀ j < N, occLoad F j ≤ r₁)
    (hr₂ : ∑ j ∈ Finset.range N, (emb j).count i ≤ r₂) :
    occLoad (substFamily E emb F) i ≤ r₁ * r₂ := by
  rw [occLoad_substFamily hF]
  calc ∑ j ∈ Finset.range N, occLoad F j * (emb j).count i
      ≤ ∑ j ∈ Finset.range N, r₁ * (emb j).count i :=
        Finset.sum_le_sum fun j hj => Nat.mul_le_mul_right _ (hr₁ j (Finset.mem_range.mp hj))
    _ = r₁ * ∑ j ∈ Finset.range N, (emb j).count i := by rw [Finset.mul_sum]
    _ ≤ r₁ * r₂ := Nat.mul_le_mul_left _ hr₂

/-! ### Chains of embeddings -/

/-- A chain of length `t + 1` restricts to its first `t` levels. -/
theorem IsEmbChain.of_succ {E : ℕ → List (ℕ × ℕ)} {emb : ℕ → ℕ → List ℕ} {t : ℕ}
    (h : IsEmbChain E emb (t + 1)) : IsEmbChain E emb t :=
  fun k hk => h k (by omega)

/-- **Substitution down a chain keeps walks.** A walk of `E t` from `u` to `v` becomes a walk of
`E 0` from `u` to `v`. -/
theorem substDown_isEdgeWalk {E : ℕ → List (ℕ × ℕ)} {emb : ℕ → ℕ → List ℕ} {t : ℕ}
    (hchain : IsEmbChain E emb t) {u v : ℕ} {es : List ℕ} (hW : IsEdgeWalk (E t) u v es) :
    IsEdgeWalk (E 0) u v (substDown E emb t u es) := by
  induction t generalizing es with
  | zero => exact hW
  | succ t ih =>
    unfold substDown
    apply ih hchain.of_succ
    exact substWalk_isEdgeWalk hW fun j hj => hchain t (by omega) j (hW.lt_length j hj)

/-- **Length down a chain.** If for every `k < t` each walk `emb k j` has at most `L k` edges,
a walk `es` of `E t` becomes a walk of `E 0` with at most `|es| · ∏_{k < t} L k` edges. -/
theorem length_substDown_le {E : ℕ → List (ℕ × ℕ)} {emb : ℕ → ℕ → List ℕ} {t : ℕ}
    (hchain : IsEmbChain E emb t) {L : ℕ → ℕ}
    (hL : ∀ k < t, ∀ j < (E (k + 1)).length, (emb k j).length ≤ L k)
    {u v : ℕ} {es : List ℕ} (hW : IsEdgeWalk (E t) u v es) :
    (substDown E emb t u es).length ≤ es.length * ∏ k ∈ Finset.range t, L k := by
  induction t generalizing es with
  | zero => simp [substDown]
  | succ t ih =>
    unfold substDown
    have hW' := substWalk_isEdgeWalk hW fun j hj => hchain t (by omega) j (hW.lt_length j hj)
    have h1 := ih hchain.of_succ (fun k hk => hL k (by omega)) hW'
    have h2 : (substWalk (E (t + 1)) (emb t) u es).length ≤ es.length * L t :=
      length_substWalk_le fun j hj => hL t (by omega) j (hW.lt_length j hj)
    calc (substDown E emb t u (substWalk (E (t + 1)) (emb t) u es)).length
        ≤ (substWalk (E (t + 1)) (emb t) u es).length * ∏ k ∈ Finset.range t, L k := h1
      _ ≤ es.length * L t * ∏ k ∈ Finset.range t, L k := Nat.mul_le_mul_right _ h2
      _ = es.length * ∏ k ∈ Finset.range (t + 1), L k := by
        rw [Finset.prod_range_succ]; ring

/-- **The load bound of flattened walks down a chain.** Let the walks of `F` use only edges of `E t`, and
let each edge of `E t` occur at most `r` times in total in `F`. If for every `k < t` each edge of
`E k` occurs at most `R k` times in total in the walks `emb k j`, then each edge of `E 0` occurs at
most `r · ∏_{k < t} R k` times in total in the substituted family. The family's own load `r` enters
once. -/
theorem occLoad_substDownFamily_le {E : ℕ → List (ℕ × ℕ)} {emb : ℕ → ℕ → List ℕ} {t : ℕ}
    (hchain : IsEmbChain E emb t) {R : ℕ → ℕ}
    (hR : ∀ k < t, ∀ i < (E k).length,
      ∑ j ∈ Finset.range (E (k + 1)).length, (emb k j).count i ≤ R k)
    {F : List (ℕ × List ℕ)} {r : ℕ} (hF : ∀ p ∈ F, ∀ j ∈ p.2, j < (E t).length)
    (hr : ∀ j < (E t).length, occLoad F j ≤ r) :
    ∀ i < (E 0).length, occLoad (substDownFamily E emb t F) i ≤ r * ∏ k ∈ Finset.range t, R k := by
  induction t generalizing F r with
  | zero =>
    intro i hi
    simpa [substDownFamily, substDown] using hr i hi
  | succ t ih =>
    have hF' : ∀ p ∈ substFamily (E (t + 1)) (emb t) F, ∀ j ∈ p.2, j < (E t).length := by
      intro p hp j hj
      simp only [substFamily, List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      obtain ⟨j', hj', hjj'⟩ := mem_substWalk hj
      exact (hchain t (by omega) j' (hF q hq j' hj')).lt_length j hjj'
    have hr' : ∀ i < (E t).length, occLoad (substFamily (E (t + 1)) (emb t) F) i ≤ r * R t :=
      fun i hi => occLoad_substFamily_le hF hr (hR t (by omega) i hi)
    have key := ih hchain.of_succ (fun k hk => hR k (by omega)) hF' hr'
    intro i hi
    have heq : substDownFamily E emb (t + 1) F =
        substDownFamily E emb t (substFamily (E (t + 1)) (emb t) F) := by
      simp [substDownFamily, substFamily, substDown]
    rw [heq, Finset.prod_range_succ]
    calc occLoad (substDownFamily E emb t (substFamily (E (t + 1)) (emb t) F)) i
        ≤ r * R t * ∏ k ∈ Finset.range t, R k := key i hi
      _ = r * ((∏ k ∈ Finset.range t, R k) * R t) := by ring

end MinCostFlow.HierPaths
