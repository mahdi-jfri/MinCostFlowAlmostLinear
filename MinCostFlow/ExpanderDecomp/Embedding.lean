module

public import MinCostFlow.Statement.Cited.Graphs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Embeddings of a witness graph, and the transfer of expansion

A cut-matching game certifies that a host graph `K` expands by building a *witness* graph `W` that
is known to expand, and by routing every edge of `W` along a walk of `K`. If each edge of `K` lies
on at most `η` of these walks, then every cut of `K` has at least `1/η` times as many edges as the
same cut of `W`. The reason is that each witness edge across the cut has an edge of its walk across
the cut, and each edge of `K` is charged by at most `η` witness edges. This is the
embedding lemma.

The graphs are multigraphs, so walks are lists of edge numbers, not of vertices. All statements are
relative to a vertex set `X`, as the notions `cutIn`, `volIn` and `degIn` of
`MinCostFlow/Statement/Cited/Graphs.lean` are.

Main results:
* `cutIn_eq_card`: the cut of `S` in `G[X]` counted by edge numbers.
* `IsEdgeWalk.exists_crossesB`: a walk between the two sides of a cut uses an edge of the cut.
* `cutIn_le_mul_of_embedding`: `cut_W(S) ≤ η · cut_K(S)`.
* `isExpansionExpanderOn_of_embedding`, `isConductanceExpanderOn_of_embedding`: `W` of expansion
  `β` gives `K` expansion `β/η`, and conductance `β/(ηD)` when the degrees of `K[X]` are at most
  `D`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- The ends of edge number `j` of the edge list `E`, or `(0, 0)` when `j` is past the end. -/
def edgeAt (E : List (ℕ × ℕ)) (j : ℕ) : ℕ × ℕ :=
  E.getD j (0, 0)

/-- Edge `e` has both ends in `X`. This is the test of `Graph.inside`. -/
def insideB (X : Finset ℕ) (e : ℕ × ℕ) : Bool :=
  decide (e.1 ∈ X) && decide (e.2 ∈ X)

/-- Edge `e` has exactly one end in `S`. This is the test of `Graph.cutIn`. -/
def crossesB (S : Finset ℕ) (e : ℕ × ℕ) : Bool :=
  decide (e.1 ∈ S) != decide (e.2 ∈ S)

/-- `es` is a walk from `u` to `v` along the edge list `E`: a list of edge numbers of `E` such that
the first edge has `u` as an end, each edge shares its other end with the next one, and the last
edge ends at `v`. The empty list is the walk from `u` to `u`. -/
inductive IsEdgeWalk (E : List (ℕ × ℕ)) : ℕ → ℕ → List ℕ → Prop
  | nil (u : ℕ) : IsEdgeWalk E u u []
  | cons {u x v j : ℕ} {es : List ℕ} (hj : j < E.length)
      (hend : ((edgeAt E j).1 = u ∧ (edgeAt E j).2 = x) ∨
        ((edgeAt E j).1 = x ∧ (edgeAt E j).2 = u))
      (hrest : IsEdgeWalk E x v es) : IsEdgeWalk E u v (j :: es)

/-- An embedding of the witness `W` into the host `K` on the vertex set `X`: every edge `j` of `W`
with both ends in `X` goes to a walk `emb j` of `K` between the ends of `j`, and every edge of that
walk has both ends in `X`. -/
def IsEmbeddingOn (W K : Graph) (X : Finset ℕ) (emb : ℕ → List ℕ) : Prop :=
  ∀ j < W.m, insideB X (edgeAt W.edges j) = true →
    IsEdgeWalk K.edges (edgeAt W.edges j).1 (edgeAt W.edges j).2 (emb j) ∧
      ∀ i ∈ emb j, insideB X (edgeAt K.edges i) = true

/-- The congestion of edge `i` of the host: the number of edges of the witness `W` whose walk
`emb j` uses it. -/
def congestion (W : Graph) (emb : ℕ → List ℕ) (i : ℕ) : ℕ :=
  ((Finset.range W.m).filter fun j => i ∈ emb j).card

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-! ### Counting edges by their numbers -/

/-- The length of a filtered list is the number of positions whose entry passes the test. -/
theorem length_filter_eq_card_range {α : Type*} (l : List α) (p : α → Bool) (d : α) :
    (l.filter p).length = ((Finset.range l.length).filter fun j => p (l.getD j d) = true).card := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [Finset.card_filter] at ih ⊢
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [← ih, List.filter_cons]
    cases p a <;> simp

/-- The cut of `S` in `G[X]` is the number of edge numbers whose edge has both ends in `X` and
exactly one end in `S`. -/
theorem cutIn_eq_card (G : Graph) (X S : Finset ℕ) :
    G.cutIn X S = ((Finset.range G.m).filter fun j =>
      insideB X (edgeAt G.edges j) = true ∧ crossesB S (edgeAt G.edges j) = true).card := by
  unfold Graph.cutIn Graph.inside
  rw [List.filter_filter, length_filter_eq_card_range _ _ (0, 0)]
  unfold Graph.m
  congr 1
  apply Finset.filter_congr
  intro j _
  simp only [edgeAt, insideB, crossesB, Bool.and_eq_true]
  tauto

/-! ### Walks -/

/-- Every edge number on a walk is a number of an edge of `E`. -/
theorem IsEdgeWalk.lt_length {E : List (ℕ × ℕ)} {u v : ℕ} {es : List ℕ}
    (h : IsEdgeWalk E u v es) : ∀ i ∈ es, i < E.length := by
  induction h with
  | nil => simp
  | cons hj _ _ ih =>
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hj
    · exact ih i hi

/-- A walk whose two ends lie on different sides of `S` uses an edge with exactly one end in `S`. -/
theorem IsEdgeWalk.exists_crossesB {E : List (ℕ × ℕ)} {u v : ℕ} {es : List ℕ}
    (h : IsEdgeWalk E u v es) (S : Finset ℕ) :
    decide (u ∈ S) ≠ decide (v ∈ S) → ∃ i ∈ es, crossesB S (edgeAt E i) = true := by
  induction h with
  | nil u => intro huv; exact absurd rfl huv
  | cons hj hend hrest ih =>
    rename_i u x v j es
    intro huv
    by_cases hx : decide (x ∈ S) = decide (u ∈ S)
    · obtain ⟨i, hi, hc⟩ := ih (by rw [hx]; exact huv)
      exact ⟨i, List.mem_cons_of_mem _ hi, hc⟩
    · refine ⟨j, List.mem_cons_self, ?_⟩
      unfold crossesB
      rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, bne_iff_ne]; exact fun h => hx h.symm
      · rw [h1, h2, bne_iff_ne]; exact hx

/-! ### The transfer of cuts -/

/-- **Embedding lemma** (cuts). If `emb` embeds `W` into `K` on `X` and each edge of `K` has
congestion at most `η`, then every cut of `W[X]` has at most `η` times as many edges as the same
cut of `K[X]`. Each witness edge across the cut has an edge of its walk across the cut, and each
edge of `K` is charged by at most `η` witness edges. -/
theorem cutIn_le_mul_of_embedding {W K : Graph} {X : Finset ℕ} {emb : ℕ → List ℕ} {η : ℕ}
    (hemb : IsEmbeddingOn W K X emb) (hcong : ∀ i < K.m, congestion W emb i ≤ η)
    (S : Finset ℕ) : W.cutIn X S ≤ K.cutIn X S * η := by
  classical
  rw [cutIn_eq_card, cutIn_eq_card]
  set A := (Finset.range W.m).filter fun j =>
    insideB X (edgeAt W.edges j) = true ∧ crossesB S (edgeAt W.edges j) = true
  set B := (Finset.range K.m).filter fun i =>
    insideB X (edgeAt K.edges i) = true ∧ crossesB S (edgeAt K.edges i) = true
  have hmain := Finset.card_mul_le_card_mul (fun j i => i ∈ emb j) (s := A) (t := B) (m := 1)
    (n := η) ?_ ?_
  · simpa using hmain
  · intro j hj
    simp only [A, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjm, hin, hcr⟩ := hj
    obtain ⟨hwalk, hall⟩ := hemb j hjm hin
    have hends : decide ((edgeAt W.edges j).1 ∈ S) ≠ decide ((edgeAt W.edges j).2 ∈ S) := by
      unfold crossesB at hcr
      simpa [bne_iff_ne] using hcr
    obtain ⟨i, hi, hc⟩ := hwalk.exists_crossesB S hends
    have hiB : i ∈ B := by
      simp only [B, Finset.mem_filter, Finset.mem_range]
      exact ⟨hwalk.lt_length i hi, hall i hi, hc⟩
    apply Finset.one_le_card.mpr
    exact ⟨i, (Finset.mem_bipartiteAbove _).mpr ⟨hiB, hi⟩⟩
  · intro i hi
    simp only [B, Finset.mem_filter, Finset.mem_range] at hi
    refine le_trans (Finset.card_le_card ?_) (hcong i hi.1)
    intro j hj
    rw [Finset.mem_bipartiteBelow] at hj
    simp only [A, Finset.mem_filter, Finset.mem_range] at hj
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hj.1.1, hj.2⟩

/-- **Embedding lemma** (expansion). If `W[X]` has expansion at least `β` and embeds into
`K` on `X` with congestion at most `η > 0`, then `K[X]` has expansion at least `β / η`. -/
theorem isExpansionExpanderOn_of_embedding {W K : Graph} {X : Finset ℕ} {emb : ℕ → List ℕ}
    {η : ℕ} (hemb : IsEmbeddingOn W K X emb) (hcong : ∀ i < K.m, congestion W emb i ≤ η)
    (hη : 0 < η) {β : ℝ} (hW : W.IsExpansionExpanderOn X β) :
    K.IsExpansionExpanderOn X (β / η) := by
  intro S hS hne hneX
  have h1 := hW S hS hne hneX
  have h2 : (W.cutIn X S : ℝ) ≤ K.cutIn X S * η := by
    exact_mod_cast cutIn_le_mul_of_embedding hemb hcong S
  have hηr : (0 : ℝ) < η := by exact_mod_cast hη
  rw [div_mul_eq_mul_div, div_le_iff₀ hηr]
  linarith

/-- The volume of `S ⊆ X` in `G[X]` is at most `D · |S|` when every degree in `G[X]` is at most
`D`. -/
theorem volIn_le_mul_card {G : Graph} {X S : Finset ℕ} (hS : S ⊆ X) {D : ℕ}
    (hdeg : ∀ v ∈ X, G.degIn X v ≤ D) : G.volIn X S ≤ D * S.card := by
  unfold Graph.volIn
  calc ∑ v ∈ S, G.degIn X v ≤ ∑ _v ∈ S, D := Finset.sum_le_sum fun v hv => hdeg v (hS hv)
    _ = D * S.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Embedding lemma** (conductance). If moreover every degree in `K[X]` is at most `D > 0`
and `β ≥ 0`, then `K[X]` has conductance at least `β / (η · D)`, since the volume of a set is at
most `D` times its size. -/
theorem isConductanceExpanderOn_of_embedding {W K : Graph} {X : Finset ℕ} {emb : ℕ → List ℕ}
    {η : ℕ} (hemb : IsEmbeddingOn W K X emb) (hcong : ∀ i < K.m, congestion W emb i ≤ η)
    (hη : 0 < η) {β : ℝ} (hβ : 0 ≤ β) (hW : W.IsExpansionExpanderOn X β) {D : ℕ} (hD : 0 < D)
    (hdeg : ∀ v ∈ X, K.degIn X v ≤ D) :
    K.IsConductanceExpanderOn X (β / (η * D)) := by
  intro S hS hne hneX
  have hexp := isExpansionExpanderOn_of_embedding hemb hcong hη hW S hS hne hneX
  have hv1 : (K.volIn X S : ℝ) ≤ D * S.card := by exact_mod_cast volIn_le_mul_card hS hdeg
  have hv2 : (K.volIn X (X \ S) : ℝ) ≤ D * (X \ S).card := by
    exact_mod_cast volIn_le_mul_card Finset.sdiff_subset hdeg
  have hηr : (0 : ℝ) < η := by exact_mod_cast hη
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hmin : min (K.volIn X S : ℝ) (K.volIn X (X \ S)) ≤
      D * min (S.card : ℝ) ((X \ S).card) := by
    rw [mul_min_of_nonneg _ _ hDr.le]
    exact min_le_min hv1 hv2
  have hcoef : 0 ≤ β / (η * D) := div_nonneg hβ (by positivity)
  calc β / (η * D) * min (K.volIn X S : ℝ) (K.volIn X (X \ S))
      ≤ β / (η * D) * (D * min (S.card : ℝ) ((X \ S).card)) :=
        mul_le_mul_of_nonneg_left hmin hcoef
    _ = β / η * min (S.card : ℝ) ((X \ S).card) := by
        field_simp
    _ ≤ K.cutIn X S := hexp

end MinCostFlow.ExpanderDecomp
