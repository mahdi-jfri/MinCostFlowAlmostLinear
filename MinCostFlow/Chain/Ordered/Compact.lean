module

public import MinCostFlow.Basic.Graph
public import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# Renaming the edges of a graph to `0, …, |E| - 1`

A rebuild of level `0` of Algorithm 1 (page 20) starts every level from scratch, so it may give the
edges of the level-`0` graph new names. Algorithm 2 gives every inserted edge a fresh internal
name, so without such a renaming the names grow with the number of updates. This file defines the
renaming that a rebuild of level `0` uses: the live edges get the names `0, …, |E| - 1`, in
increasing order of their old names.

* `compactRank E e` is the number of elements of `E` below `e`. On `E` it is strictly monotone and
  maps `E` onto `range |E|`.
* `compactUnrank E j` is the `j`-th smallest element of `E` for `j < |E|`, and `j` otherwise. It
  is the inverse of `compactRank E` on `range |E|`.
* `MGraph.compact G` is `G` with each edge `e` named `compactRank G.E e`.
* `rebuildStartGraph idx G` and `rebuildStartFn idx G f` are the graph and the edge vectors that a
  rebuild of level `idx` starts from: renamed at level `0`, unchanged above.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

/-- The rank of `e` in `E`: the number of elements of `E` below `e`. -/
def compactRank (E : Finset ℕ) (e : ℕ) : ℕ :=
  (E.filter (· < e)).card

/-- The `j`-th smallest element of `E` (counting from `0`) for `j < |E|`, and `j` otherwise. -/
def compactUnrank (E : Finset ℕ) (j : ℕ) : ℕ :=
  if h : j < E.card then E.orderEmbOfFin rfl ⟨j, h⟩ else j

/-- The graph `G` with each edge `e` renamed to `compactRank G.E e`: its edges are
`0, …, |E(G)| - 1`, and edge `j` has the ends of the old edge `compactUnrank G.E j`. -/
def _root_.MinCostFlow.MGraph.compact (G : MGraph) : MGraph where
  V := G.V
  E := Finset.range G.E.card
  tail := fun j => G.tail (compactUnrank G.E j)
  head := fun j => G.head (compactUnrank G.E j)

/-- The graph that a rebuild of level `idx` starts from: `G` with its edges renamed to
`0, …, |E| - 1` at level `0`, and `G` above. -/
def rebuildStartGraph (idx : ℕ) (G : MGraph) : MGraph :=
  if idx = 0 then G.compact else G

/-- An edge vector `f` of `G` in the names of `rebuildStartGraph idx G`. -/
def rebuildStartFn {α : Type*} (idx : ℕ) (G : MGraph) (f : ℕ → α) : ℕ → α :=
  if idx = 0 then fun j => f (compactUnrank G.E j) else f

section Lemmas

variable {E : Finset ℕ}

lemma compactUnrank_of_lt {j : ℕ} (h : j < E.card) :
    compactUnrank E j = E.orderEmbOfFin rfl ⟨j, h⟩ := by
  simp [compactUnrank, h]

lemma compactUnrank_mem {j : ℕ} (h : j < E.card) : compactUnrank E j ∈ E := by
  rw [compactUnrank_of_lt h]
  exact Finset.orderEmbOfFin_mem E rfl _

/-- The elements of `E` below the `i`-th smallest one are the `j`-th smallest ones for `j < i`. -/
private lemma filter_lt_orderEmbOfFin (i : Fin E.card) :
    E.filter (· < E.orderEmbOfFin rfl i) = (Finset.Iio i).map (E.orderEmbOfFin rfl).toEmbedding := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio,
    RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨hx, hlt⟩
    have hrange : x ∈ Set.range (E.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨j, rfl⟩ := hrange
    exact ⟨j, (E.orderEmbOfFin rfl).lt_iff_lt.mp hlt, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Finset.orderEmbOfFin_mem E rfl j, (E.orderEmbOfFin rfl).lt_iff_lt.mpr hj⟩

lemma compactRank_unrank {j : ℕ} (h : j < E.card) : compactRank E (compactUnrank E j) = j := by
  rw [compactUnrank_of_lt h, compactRank, filter_lt_orderEmbOfFin, Finset.card_map, Fin.card_Iio]

lemma compactRank_lt {e : ℕ} (he : e ∈ E) : compactRank E e < E.card := by
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
  have := Finset.mem_filter.mp (hsub he)
  exact lt_irrefl e this.2

/-- Every element of `E` is the `j`-th smallest one for some `j < |E|`. -/
lemma exists_compactUnrank_eq {e : ℕ} (he : e ∈ E) :
    ∃ j < E.card, compactUnrank E j = e := by
  have hrange : e ∈ Set.range (E.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact he
  obtain ⟨j, hj⟩ := hrange
  exact ⟨j.val, j.isLt, by rw [compactUnrank_of_lt j.isLt]; exact hj⟩

lemma compactUnrank_rank {e : ℕ} (he : e ∈ E) : compactUnrank E (compactRank E e) = e := by
  obtain ⟨j, hj, rfl⟩ := exists_compactUnrank_eq he
  rw [compactRank_unrank hj]

lemma compactRank_injOn : Set.InjOn (compactRank E) E := by
  intro a ha b hb hab
  have h := congrArg (compactUnrank E) hab
  rwa [compactUnrank_rank ha, compactUnrank_rank hb] at h

/-- `compactRank E` is strictly monotone on `E`: the renaming keeps the order of the names. -/
lemma compactRank_lt_compactRank {a b : ℕ} (ha : a ∈ E) (hab : a < b) :
    compactRank E a < compactRank E b := by
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx'.1, lt_trans hx'.2 hab⟩
  · have := Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨ha, hab⟩))
    exact lt_irrefl a this.2

lemma compactRank_lt_iff {a b : ℕ} (ha : a ∈ E) (hb : b ∈ E) :
    compactRank E a < compactRank E b ↔ a < b := by
  constructor
  · intro h
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact hlt
    · subst heq; exact absurd h (lt_irrefl _)
    · exact absurd (compactRank_lt_compactRank hb hgt) (not_lt.mpr h.le)
  · exact compactRank_lt_compactRank ha

lemma image_compactRank : E.image (compactRank E) = Finset.range E.card := by
  ext j
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact compactRank_lt he
  · intro hj
    exact ⟨compactUnrank E j, compactUnrank_mem hj, compactRank_unrank hj⟩

end Lemmas

section GraphLemmas

variable (G : MGraph)

@[simp] lemma compact_V : G.compact.V = G.V := rfl

@[simp] lemma compact_E : G.compact.E = Finset.range G.E.card := rfl

lemma mem_compact_E {j : ℕ} : j ∈ G.compact.E ↔ j < G.m := by
  simp [MGraph.m]

@[simp] lemma compact_m : G.compact.m = G.m := by
  simp [MGraph.m]

@[simp] lemma compact_n : G.compact.n = G.n := rfl

lemma compact_tail (j : ℕ) : G.compact.tail j = G.tail (compactUnrank G.E j) := rfl

lemma compact_head (j : ℕ) : G.compact.head j = G.head (compactUnrank G.E j) := rfl

variable {G}

lemma compact_isValid (h : G.IsValid) : G.compact.IsValid := by
  intro j hj
  have hj' : j < G.E.card := by simpa using hj
  exact h _ (compactUnrank_mem hj')

lemma compactUnrank_mem_of_mem_compact {j : ℕ} (hj : j ∈ G.compact.E) :
    compactUnrank G.E j ∈ G.E :=
  compactUnrank_mem (by simpa using hj)

lemma compactRank_mem_compact {e : ℕ} (he : e ∈ G.E) : compactRank G.E e ∈ G.compact.E := by
  simpa using compactRank_lt he

end GraphLemmas

section RebuildStart

lemma rebuildStartGraph_zero (G : MGraph) : rebuildStartGraph 0 G = G.compact := rfl

lemma rebuildStartGraph_pos {idx : ℕ} (h : idx ≠ 0) (G : MGraph) : rebuildStartGraph idx G = G := by
  simp [rebuildStartGraph, h]

lemma rebuildStartFn_zero {α : Type*} (G : MGraph) (f : ℕ → α) :
    rebuildStartFn 0 G f = fun j => f (compactUnrank G.E j) := rfl

lemma rebuildStartFn_pos {α : Type*} {idx : ℕ} (h : idx ≠ 0) (G : MGraph) (f : ℕ → α) :
    rebuildStartFn idx G f = f := by
  simp [rebuildStartFn, h]

@[simp] lemma rebuildStartGraph_V (idx : ℕ) (G : MGraph) : (rebuildStartGraph idx G).V = G.V := by
  unfold rebuildStartGraph; split <;> rfl

@[simp] lemma rebuildStartGraph_m (idx : ℕ) (G : MGraph) : (rebuildStartGraph idx G).m = G.m := by
  unfold rebuildStartGraph; split <;> simp

@[simp] lemma rebuildStartGraph_n (idx : ℕ) (G : MGraph) : (rebuildStartGraph idx G).n = G.n := by
  unfold rebuildStartGraph; split <;> rfl

lemma rebuildStartGraph_isValid (idx : ℕ) {G : MGraph} (h : G.IsValid) :
    (rebuildStartGraph idx G).IsValid := by
  unfold rebuildStartGraph; split
  · exact compact_isValid h
  · exact h

/-- Each edge of the start graph corresponds to an edge of `G`, and the start vectors take the
values of the vectors of `G` there. -/
lemma rebuildStartFn_exists {α : Type*} (idx : ℕ) {G : MGraph} {j : ℕ}
    (hj : j ∈ (rebuildStartGraph idx G).E) :
    ∃ e ∈ G.E, ∀ f : ℕ → α, rebuildStartFn idx G f j = f e := by
  unfold rebuildStartGraph at hj
  unfold rebuildStartFn
  split at hj
  · rename_i h0
    simp only [h0, ↓reduceIte]
    exact ⟨compactUnrank G.E j, compactUnrank_mem_of_mem_compact hj, fun _ => rfl⟩
  · rename_i h0
    simp only [h0, ↓reduceIte]
    exact ⟨j, hj, fun _ => rfl⟩

end RebuildStart

end MinCostFlow.Chain.Ordered
