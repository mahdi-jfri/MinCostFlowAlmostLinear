module

public import MinCostFlow.Expander.ExpanderPruning
public import MinCostFlow.ExpanderDecomp.Embedding
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Removing fake edges

The cut-matching game sometimes fails to route a pair. It then adds a *fake* edge, so that its
witness still expands. In the end we know that `K = H + F` has conductance at least `ρ`, where `H`
is the real graph and `F` is a short list of fake edges. We want a large set `R` on which the real
graph `H` alone has good conductance. This is the fake-edge removal `RemoveFake`.

The idea is to make the fake edges look like a small boundary, so that the existing pruning
theorem `pruneExpander_spec` cuts them off. Replace each fake edge `uv` by a path `u b v` through a
new midpoint `b`. Call the result `J` and the set of midpoints `B`. Then:
* `J` still has conductance at least `ρ / 3` (`isConductanceExpanderOn_subdivGraph`);
* `B` has volume `2|F|` and cut at most `2|F|` in `J` (`volIn_midpoints_le`);
* on a set `R` without midpoints, `J` and `H` have the same edges (`inside_subdivGraph`).

Pruning `J` with forbidden set `B` gives `R` with conductance at least `ρ / 9` in `H`, and the
removed volume is at most `4 C |F|` for the pruning constant `C ≤ 15 / ρ` (`removeFake_spec`).

Vertices and midpoints share one numbering: the real vertices are below `n`, and the midpoint of
fake edge number `j` is `n + j`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- Subdivide each edge of `F`: edge number `j` becomes the two edges `(u, m + j)` and
`(m + j, v)`. -/
def subdiv : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | _, [] => []
  | m, e :: F => (e.1, m) :: (m, e.2) :: subdiv (m + 1) F

/-- The real edges `H` together with the subdivided fake edges `F`, on `n + |F|` vertices. -/
def subdivGraph (n : ℕ) (H F : List (ℕ × ℕ)) : Graph :=
  ⟨n + F.length, H ++ subdiv n F⟩

/-- The midpoints `n, …, n + |F| - 1` of the subdivided fake edges. -/
def midpoints (n : ℕ) (F : List (ℕ × ℕ)) : Finset ℕ :=
  Finset.Ico n (n + F.length)

/-- The set kept by fake-edge removal: prune `J = subdivGraph n H F` on `X ∪ B`, with the
midpoints `B` forbidden, conductance `ρ / 3` and degree threshold `1`. -/
noncomputable def removeFake (n : ℕ) (H F : List (ℕ × ℕ)) (X : Finset ℕ) (ρ : ℝ) : Finset ℕ :=
  pruneExpander (subdivGraph n H F) (X ∪ midpoints n F) (midpoints n F) (ρ / 3) 1

/-- The term of edge `e` in the cut of `S` in `G[X]`. -/
def cutTerm (X S : Finset ℕ) (e : ℕ × ℕ) : ℕ :=
  if insideB X e then (if crossesB S e then 1 else 0) else 0

/-- The term of edge `e` in the volume of `S` in `G[X]`. -/
def volTerm (X S : Finset ℕ) (e : ℕ × ℕ) : ℕ :=
  if insideB X e then (if e.1 ∈ S then 1 else 0) + (if e.2 ∈ S then 1 else 0) else 0

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Sums over the edge list -/

private theorem sum_map_filter {α : Type*} (l : List α) (p : α → Bool) (f : α → ℕ) :
    ((l.filter p).map f).sum = (l.map fun x => if p x then f x else 0).sum := by
  induction l with
  | nil => simp
  | cons a t ih => by_cases hp : p a <;> simp [hp, ih]

private theorem sum_map_two_mul {α : Type*} (l : List α) (f : α → ℕ) :
    (l.map fun x => 2 * f x).sum = 2 * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- The cut as a sum over all edges. -/
theorem cutIn_eq_sum_edges (G : Graph) (X S : Finset ℕ) :
    G.cutIn X S = (G.edges.map (cutTerm X S)).sum := by
  rw [cutIn_eq_sum_map]
  unfold Graph.inside
  rw [sum_map_filter]
  rfl

/-- The volume as a sum over all edges. -/
theorem volIn_eq_sum_edges (G : Graph) (X S : Finset ℕ) :
    G.volIn X S = (G.edges.map (volTerm X S)).sum := by
  rw [volIn_eq_sum_map]
  unfold Graph.inside
  rw [sum_map_filter]
  rfl

/-! ### The subdivided edges -/

/-- Each subdivided edge joins an end of a fake edge to a midpoint. -/
theorem mem_subdiv {m : ℕ} {F : List (ℕ × ℕ)} {e : ℕ × ℕ} (he : e ∈ subdiv m F) :
    ∃ f ∈ F, ∃ b, m ≤ b ∧ b < m + F.length ∧ (e = (f.1, b) ∨ e = (b, f.2)) := by
  induction F generalizing m with
  | nil => simp [subdiv] at he
  | cons f F ih =>
    simp only [subdiv, List.mem_cons] at he
    rcases he with rfl | rfl | he
    · exact ⟨f, List.mem_cons_self, m, le_rfl, by simp, Or.inl rfl⟩
    · exact ⟨f, List.mem_cons_self, m, le_rfl, by simp, Or.inr rfl⟩
    · obtain ⟨g, hg, b, hb1, hb2, hb⟩ := ih he
      refine ⟨g, List.mem_cons_of_mem _ hg, b, by omega, ?_, hb⟩
      simp only [List.length_cons]
      omega

/-- Summing over the subdivided edges, with the two halves of each fake edge compared to one term
of that fake edge. -/
private theorem sum_subdiv_le {F : List (ℕ × ℕ)} {m : ℕ} {φK φJ ψJ : ℕ × ℕ → ℕ}
    (h : ∀ e ∈ F, ∀ b, m ≤ b → b < m + F.length →
      φJ (e.1, b) + φJ (b, e.2) ≤ φK e + (ψJ (e.1, b) + ψJ (b, e.2))) :
    ((subdiv m F).map φJ).sum ≤ (F.map φK).sum + ((subdiv m F).map ψJ).sum := by
  induction F generalizing m with
  | nil => simp [subdiv]
  | cons e F ih =>
    have h1 := h e List.mem_cons_self m le_rfl (by simp)
    have h2 := ih (m := m + 1) fun f hf b hb1 hb2 =>
      h f (List.mem_cons_of_mem _ hf) b (by omega) (by simp only [List.length_cons]; omega)
    simp only [subdiv, List.map_cons, List.sum_cons]
    omega

/-- The reverse comparison: one term of each fake edge against its two halves. -/
private theorem le_sum_subdiv {F : List (ℕ × ℕ)} {m : ℕ} {φK φJ : ℕ × ℕ → ℕ}
    (h : ∀ e ∈ F, ∀ b, m ≤ b → b < m + F.length → φK e ≤ φJ (e.1, b) + φJ (b, e.2)) :
    (F.map φK).sum ≤ ((subdiv m F).map φJ).sum := by
  induction F generalizing m with
  | nil => simp [subdiv]
  | cons e F ih =>
    have h1 := h e List.mem_cons_self m le_rfl (by simp)
    have h2 := ih (m := m + 1) fun f hf b hb1 hb2 =>
      h f (List.mem_cons_of_mem _ hf) b (by omega) (by simp only [List.length_cons]; omega)
    simp only [subdiv, List.map_cons, List.sum_cons]
    omega

/-! ### Membership in `X ∪ B` -/

private theorem mem_union_midpoints_of_lt {n : ℕ} {F : List (ℕ × ℕ)} {X : Finset ℕ} {v : ℕ}
    (hv : v < n) : v ∈ X ∪ midpoints n F ↔ v ∈ X := by
  simp only [midpoints, Finset.mem_union, Finset.mem_Ico]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact h
    · omega
  · exact Or.inl

private theorem not_mem_of_ge {n : ℕ} {X : Finset ℕ} (hX : X ⊆ Finset.range n) {b : ℕ}
    (hb : n ≤ b) : b ∉ X := fun h => by
  have := Finset.mem_range.mp (hX h)
  omega

/-! ### Comparing the terms of one edge -/

/-- A real edge has the same cut term in `J` as in `K`. -/
private theorem cutTerm_real {n : ℕ} {F : List (ℕ × ℕ)} {X W : Finset ℕ} {e : ℕ × ℕ}
    (he : e.1 < n ∧ e.2 < n) :
    cutTerm (X ∪ midpoints n F) W e = cutTerm X (W ∩ X) e := by
  have h1 := mem_union_midpoints_of_lt (F := F) (X := X) he.1
  have h2 := mem_union_midpoints_of_lt (F := F) (X := X) he.2
  unfold cutTerm insideB crossesB
  by_cases a1 : e.1 ∈ X <;> by_cases a2 : e.2 ∈ X <;> by_cases b1 : e.1 ∈ W <;>
    by_cases b2 : e.2 ∈ W <;> simp [h1, h2, a1, a2, b1, b2]

/-- A real edge has the same volume term in `J` as in `K`. -/
private theorem volTerm_real {n : ℕ} {F : List (ℕ × ℕ)} {X W : Finset ℕ} {e : ℕ × ℕ}
    (he : e.1 < n ∧ e.2 < n) :
    volTerm (X ∪ midpoints n F) W e = volTerm X (W ∩ X) e := by
  have h1 := mem_union_midpoints_of_lt (F := F) (X := X) he.1
  have h2 := mem_union_midpoints_of_lt (F := F) (X := X) he.2
  unfold volTerm insideB
  by_cases a1 : e.1 ∈ X <;> by_cases a2 : e.2 ∈ X <;> by_cases b1 : e.1 ∈ W <;>
    by_cases b2 : e.2 ∈ W <;> simp [h1, h2, a1, a2, b1, b2]

/-- The facts about a fake edge `e` and its midpoint `b` that the term comparisons use. -/
private theorem fake_mem {n : ℕ} {F : List (ℕ × ℕ)} {X : Finset ℕ} (hX : X ⊆ Finset.range n)
    {e : ℕ × ℕ} (he : e.1 ∈ X ∧ e.2 ∈ X) {b : ℕ} (hb1 : n ≤ b) (hb2 : b < n + F.length) :
    e.1 ∈ X ∪ midpoints n F ∧ e.2 ∈ X ∪ midpoints n F ∧ b ∈ X ∪ midpoints n F ∧ b ∉ X := by
  refine ⟨Finset.mem_union_left _ he.1, Finset.mem_union_left _ he.2, ?_, not_mem_of_ge hX hb1⟩
  exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨hb1, hb2⟩)

/-- A fake edge across `W ∩ X` has a half across `W`. -/
private theorem cutTerm_fake {n : ℕ} {F : List (ℕ × ℕ)} {X W : Finset ℕ}
    (hX : X ⊆ Finset.range n) {e : ℕ × ℕ} (he : e.1 ∈ X ∧ e.2 ∈ X) {b : ℕ} (hb1 : n ≤ b)
    (hb2 : b < n + F.length) :
    cutTerm X (W ∩ X) e ≤
      cutTerm (X ∪ midpoints n F) W (e.1, b) + cutTerm (X ∪ midpoints n F) W (b, e.2) := by
  obtain ⟨y1, y2, yb, xb⟩ := fake_mem (F := F) hX he hb1 hb2
  unfold cutTerm insideB crossesB
  by_cases b1 : e.1 ∈ W <;> by_cases b2 : e.2 ∈ W <;> by_cases bb : b ∈ W <;>
    simp [y1, y2, yb, he.1, he.2, b1, b2, bb]

/-- The two halves of a fake edge have volume at most twice that of the fake edge plus the
number of halves across `W`. A midpoint in `W` adds two to the volume, and each of its halves
whose other end is outside `W` is a cut edge. -/
private theorem volTerm_fake_le {n : ℕ} {F : List (ℕ × ℕ)} {X W : Finset ℕ}
    (hX : X ⊆ Finset.range n) {e : ℕ × ℕ} (he : e.1 ∈ X ∧ e.2 ∈ X) {b : ℕ} (hb1 : n ≤ b)
    (hb2 : b < n + F.length) :
    volTerm (X ∪ midpoints n F) W (e.1, b) + volTerm (X ∪ midpoints n F) W (b, e.2) ≤
      2 * volTerm X (W ∩ X) e +
        (cutTerm (X ∪ midpoints n F) W (e.1, b) + cutTerm (X ∪ midpoints n F) W (b, e.2)) := by
  obtain ⟨y1, y2, yb, xb⟩ := fake_mem (F := F) hX he hb1 hb2
  unfold cutTerm volTerm insideB crossesB
  by_cases b1 : e.1 ∈ W <;> by_cases b2 : e.2 ∈ W <;> by_cases bb : b ∈ W <;>
    simp [y1, y2, yb, he.1, he.2, b1, b2, bb]

/-- The fake edge has volume at most that of its two halves. -/
private theorem le_volTerm_fake {n : ℕ} {F : List (ℕ × ℕ)} {X W : Finset ℕ}
    (hX : X ⊆ Finset.range n) {e : ℕ × ℕ} (he : e.1 ∈ X ∧ e.2 ∈ X) {b : ℕ} (hb1 : n ≤ b)
    (hb2 : b < n + F.length) :
    volTerm X (W ∩ X) e ≤
      volTerm (X ∪ midpoints n F) W (e.1, b) + volTerm (X ∪ midpoints n F) W (b, e.2) := by
  obtain ⟨y1, y2, yb, xb⟩ := fake_mem (F := F) hX he hb1 hb2
  unfold volTerm insideB
  by_cases b1 : e.1 ∈ W <;> by_cases b2 : e.2 ∈ W <;> by_cases bb : b ∈ W <;>
    simp [y1, y2, yb, he.1, he.2, b1, b2, bb]

/-! ### Cuts and volumes in `J` against those in `K` -/

/-- Every cut of `K = H + F` in `X` is at most the cut in `J` of any set with the same real
vertices. -/
theorem cutIn_le_subdiv {n : ℕ} {H F : List (ℕ × ℕ)} {X : Finset ℕ} (hX : X ⊆ Finset.range n)
    (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n) (hF : ∀ e ∈ F, e.1 ∈ X ∧ e.2 ∈ X) (W : Finset ℕ) :
    (Graph.mk n (H ++ F)).cutIn X (W ∩ X) ≤
      (subdivGraph n H F).cutIn (X ∪ midpoints n F) W := by
  rw [cutIn_eq_sum_edges, cutIn_eq_sum_edges]
  simp only [subdivGraph, List.map_append, List.sum_append]
  have hreal : (H.map (cutTerm X (W ∩ X))).sum = (H.map (cutTerm (X ∪ midpoints n F) W)).sum := by
    congr 1
    exact List.map_congr_left fun e he => (cutTerm_real (hH e he)).symm
  have hfake : (F.map (cutTerm X (W ∩ X))).sum ≤
      ((subdiv n F).map (cutTerm (X ∪ midpoints n F) W)).sum :=
    le_sum_subdiv fun e he b hb1 hb2 => cutTerm_fake hX (hF e he) hb1 hb2
  omega

/-- The volume of `W` in `J` is at most twice the volume of its real vertices in `K`, plus the
cut of `W` in `J`. -/
theorem volIn_le_subdiv {n : ℕ} {H F : List (ℕ × ℕ)} {X : Finset ℕ} (hX : X ⊆ Finset.range n)
    (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n) (hF : ∀ e ∈ F, e.1 ∈ X ∧ e.2 ∈ X) (W : Finset ℕ) :
    (subdivGraph n H F).volIn (X ∪ midpoints n F) W ≤
      2 * (Graph.mk n (H ++ F)).volIn X (W ∩ X) +
        (subdivGraph n H F).cutIn (X ∪ midpoints n F) W := by
  rw [cutIn_eq_sum_edges, volIn_eq_sum_edges, volIn_eq_sum_edges]
  simp only [subdivGraph, List.map_append, List.sum_append]
  have hreal : (H.map (volTerm (X ∪ midpoints n F) W)).sum = (H.map (volTerm X (W ∩ X))).sum := by
    congr 1
    exact List.map_congr_left fun e he => volTerm_real (hH e he)
  have hfake := sum_subdiv_le (m := n) (φK := fun e => 2 * volTerm X (W ∩ X) e)
    (φJ := volTerm (X ∪ midpoints n F) W) (ψJ := cutTerm (X ∪ midpoints n F) W)
    fun e he b hb1 hb2 => volTerm_fake_le hX (hF e he) hb1 hb2
  rw [sum_map_two_mul] at hfake
  omega

/-- The volume of the real vertices of `W` in `K` is at most the volume of `W` in `J`. -/
theorem volIn_le_volIn_subdiv {n : ℕ} {H F : List (ℕ × ℕ)} {X : Finset ℕ}
    (hX : X ⊆ Finset.range n) (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n)
    (hF : ∀ e ∈ F, e.1 ∈ X ∧ e.2 ∈ X) (W : Finset ℕ) :
    (Graph.mk n (H ++ F)).volIn X (W ∩ X) ≤ (subdivGraph n H F).volIn (X ∪ midpoints n F) W := by
  rw [volIn_eq_sum_edges, volIn_eq_sum_edges]
  simp only [subdivGraph, List.map_append, List.sum_append]
  have hreal : (H.map (volTerm X (W ∩ X))).sum = (H.map (volTerm (X ∪ midpoints n F) W)).sum := by
    congr 1
    exact List.map_congr_left fun e he => (volTerm_real (hH e he)).symm
  have hfake : (F.map (volTerm X (W ∩ X))).sum ≤
      ((subdiv n F).map (volTerm (X ∪ midpoints n F) W)).sum :=
    le_sum_subdiv fun e he b hb1 hb2 => le_volTerm_fake hX (hF e he) hb1 hb2
  omega

/-- The midpoints have volume at most `2|F|` in `J`: each half of a fake edge has exactly one end
at a midpoint, and the real edges have none. -/
theorem volIn_midpoints_le {n : ℕ} {H F : List (ℕ × ℕ)} {X : Finset ℕ}
    (hX : X ⊆ Finset.range n) (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n)
    (hF : ∀ e ∈ F, e.1 ∈ X ∧ e.2 ∈ X) :
    (subdivGraph n H F).volIn (X ∪ midpoints n F) (midpoints n F) ≤ 2 * F.length := by
  rw [volIn_eq_sum_edges]
  simp only [subdivGraph, List.map_append, List.sum_append]
  have hreal : (H.map (volTerm (X ∪ midpoints n F) (midpoints n F))).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    have h1 := (hH e he).1
    have h2 := (hH e he).2
    unfold volTerm
    simp only [midpoints, Finset.mem_Ico]
    split_ifs <;> omega
  have hfake := sum_subdiv_le (m := n) (φK := fun _ => 2)
    (φJ := volTerm (X ∪ midpoints n F) (midpoints n F)) (ψJ := fun _ => 0)
    fun e he b hb1 hb2 => by
      have h1 := Finset.mem_range.mp (hX (hF e he).1)
      have h2 := Finset.mem_range.mp (hX (hF e he).2)
      unfold volTerm
      simp only [midpoints, Finset.mem_Ico]
      split_ifs <;> omega
  rw [sum_map_const, sum_map_const] at hfake
  omega

/-- On a set of real vertices, `J` and `H` have the same edges: every half of a fake edge has a
midpoint as an end. -/
theorem inside_subdivGraph {n : ℕ} {H F : List (ℕ × ℕ)} {R : Finset ℕ}
    (hR : R ⊆ Finset.range n) :
    (subdivGraph n H F).inside R = (Graph.mk n H).inside R := by
  simp only [Graph.inside, subdivGraph, List.filter_append]
  have hnil : (subdiv n F).filter (fun e => decide (e.1 ∈ R) && decide (e.2 ∈ R)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    obtain ⟨f, _, b, hb1, _, hb⟩ := mem_subdiv he
    have hbR : b ∉ R := not_mem_of_ge hR hb1
    rcases hb with rfl | rfl <;> simp [hbR]
  rw [hnil, List.append_nil]

/-- `J` is a valid graph on `n + |F|` vertices. -/
theorem subdivGraph_isValid {n : ℕ} {H F : List (ℕ × ℕ)} {X : Finset ℕ}
    (hX : X ⊆ Finset.range n) (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n)
    (hF : ∀ e ∈ F, e.1 ∈ X ∧ e.2 ∈ X) : (subdivGraph n H F).IsValid := by
  intro e he
  simp only [subdivGraph, List.mem_append] at he ⊢
  rcases he with he | he
  · have := hH e he
    omega
  · obtain ⟨f, hf, b, _, hb2, hb⟩ := mem_subdiv he
    have h1 := Finset.mem_range.mp (hX (hF f hf).1)
    have h2 := Finset.mem_range.mp (hX (hF f hf).2)
    rcases hb with rfl | rfl <;> simp only <;> omega

/-! ### The conductance of `J` -/

/-- The conductance bound holds for every subset, including `∅` and `X`, where both sides are
zero. -/
theorem IsConductanceExpanderOn.mul_min_le {G : Graph} {X : Finset ℕ} {φ : ℝ}
    (h : G.IsConductanceExpanderOn X φ) {S : Finset ℕ} (hS : S ⊆ X) :
    φ * min (G.volIn X S : ℝ) (G.volIn X (X \ S)) ≤ G.cutIn X S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [show G.volIn X ∅ = 0 from Finset.sum_empty, Nat.cast_zero,
      min_eq_left (Nat.cast_nonneg _), mul_zero]
    exact Nat.cast_nonneg _
  · by_cases heq : S = X
    · subst heq
      rw [Finset.sdiff_self, show G.volIn S ∅ = 0 from Finset.sum_empty, Nat.cast_zero,
        min_eq_right (Nat.cast_nonneg _), mul_zero]
      exact Nat.cast_nonneg _
    · exact h S hS hne heq

/-- If `K = H + F` has conductance at least `ρ ≤ 1` on `X`, then `J` has conductance at least
`ρ / 3` on `X ∪ B`. For a cut `W` of `J`, let `a` and `a'` be the `K`-volumes of the real vertices
on the two sides and `c` the cut of `W` in `J`. The cut of the real vertices in `K` is at most
`c`, so `ρ min(a, a') ≤ c`. The two sides of `W` have `J`-volume at most `2a + c` and `2a' + c`.
Hence `(ρ/3) min(vol W, vol W̄) ≤ (ρ/3)(2 min(a, a') + c) ≤ c`. -/
theorem isConductanceExpanderOn_subdivGraph {n : ℕ} {H F : List (ℕ × ℕ)} {X : Finset ℕ}
    (hX : X ⊆ Finset.range n) (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n)
    (hF : ∀ e ∈ F, e.1 ∈ X ∧ e.2 ∈ X) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hK : (Graph.mk n (H ++ F)).IsConductanceExpanderOn X ρ) :
    (subdivGraph n H F).IsConductanceExpanderOn (X ∪ midpoints n F) (ρ / 3) := by
  intro W hWY _ _
  have hXY : X ⊆ X ∪ midpoints n F := Finset.subset_union_left
  have hc : (subdivGraph n H F).cutIn (X ∪ midpoints n F) ((X ∪ midpoints n F) \ W) =
      (subdivGraph n H F).cutIn (X ∪ midpoints n F) W := cutIn_sdiff _ _ W hWY
  have hSc : ((X ∪ midpoints n F) \ W) ∩ X = X \ (W ∩ X) := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨_, h⟩, hv⟩
      exact ⟨hv, fun h' => h h'.1⟩
    · rintro ⟨hv, h⟩
      exact ⟨⟨hXY hv, fun h' => h ⟨h', hv⟩⟩, hv⟩
  have hA := cutIn_le_subdiv hX hH hF W
  have hB1 := volIn_le_subdiv hX hH hF W
  have hB2 := volIn_le_subdiv hX hH hF ((X ∪ midpoints n F) \ W)
  rw [hSc, hc] at hB2
  have hK' := IsConductanceExpanderOn.mul_min_le hK (Finset.inter_subset_right : W ∩ X ⊆ X)
  set a := (Graph.mk n (H ++ F)).volIn X (W ∩ X)
  set a' := (Graph.mk n (H ++ F)).volIn X (X \ (W ∩ X))
  set c := (subdivGraph n H F).cutIn (X ∪ midpoints n F) W
  have hAr : ((Graph.mk n (H ++ F)).cutIn X (W ∩ X) : ℝ) ≤ c := by exact_mod_cast hA
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hρc : ρ * (c : ℝ) ≤ c := by nlinarith
  have hρ3 : (0 : ℝ) ≤ ρ / 3 := by positivity
  rcases le_total a a' with hab | hab
  · have hm : min (a : ℝ) a' = a := min_eq_left (by exact_mod_cast hab)
    rw [hm] at hK'
    have hB1r : ((subdivGraph n H F).volIn (X ∪ midpoints n F) W : ℝ) ≤ 2 * a + c := by
      exact_mod_cast hB1
    calc ρ / 3 * min ((subdivGraph n H F).volIn (X ∪ midpoints n F) W : ℝ)
          ((subdivGraph n H F).volIn (X ∪ midpoints n F) ((X ∪ midpoints n F) \ W))
        ≤ ρ / 3 * (2 * a + c) :=
          mul_le_mul_of_nonneg_left (le_trans (min_le_left _ _) hB1r) hρ3
      _ ≤ c := by linarith
  · have hm : min (a : ℝ) a' = a' := min_eq_right (by exact_mod_cast hab)
    rw [hm] at hK'
    have hB2r : ((subdivGraph n H F).volIn (X ∪ midpoints n F) ((X ∪ midpoints n F) \ W) : ℝ) ≤
        2 * a' + c := by
      exact_mod_cast hB2
    calc ρ / 3 * min ((subdivGraph n H F).volIn (X ∪ midpoints n F) W : ℝ)
          ((subdivGraph n H F).volIn (X ∪ midpoints n F) ((X ∪ midpoints n F) \ W))
        ≤ ρ / 3 * (2 * a' + c) :=
          mul_le_mul_of_nonneg_left (le_trans (min_le_right _ _) hB2r) hρ3
      _ ≤ c := by linarith

/-! ### Removing fake edges keeps a conductance expander (`removeFake_spec`) -/

/-- The degree of a real vertex in `J` is at least its degree in `K`. -/
theorem degIn_le_subdiv {n : ℕ} {H F : List (ℕ × ℕ)} {X : Finset ℕ} (hX : X ⊆ Finset.range n)
    (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n) (hF : ∀ e ∈ F, e.1 ∈ X ∧ e.2 ∈ X) {v : ℕ} (hv : v ∈ X) :
    (Graph.mk n (H ++ F)).degIn X v ≤ (subdivGraph n H F).degIn (X ∪ midpoints n F) v := by
  have h := volIn_le_volIn_subdiv hX hH hF {v}
  rw [Finset.singleton_inter_of_mem hv] at h
  simpa [Graph.volIn] using h

/-- **Fake-edge removal**, for any set `R` with the guarantees of pruning `J`. Let `R ⊆ X ∪ B`
avoid the midpoints, let `J` have conductance at least `φ` on `R` and degrees at least `θ` in
`J[R]`, and let `vol_J((X ∪ B) \ B \ R) + 2C cut_J(R) ≤ 2C cut_J(B)`. Then `R ⊆ X`, the real graph
`H` has conductance at least `φ` and degrees at least `θ` on `R`, and the removed volume in `K` is
at most `4C|F|`. The first claims hold because `J[R] = H[R]` (`inside_subdivGraph`). The last
holds because `cut_J(B) ≤ vol_J(B) ≤ 2|F|`. -/
theorem removeFake_of_pruned {n : ℕ} {H F : List (ℕ × ℕ)} {X : Finset ℕ}
    (hX : X ⊆ Finset.range n) (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n)
    (hF : ∀ e ∈ F, e.1 ∈ X ∧ e.2 ∈ X) {R : Finset ℕ} {φ θ : ℝ} {C : ℕ}
    (hRB : R ⊆ (X ∪ midpoints n F) \ midpoints n F)
    (hRφ : (subdivGraph n H F).IsConductanceExpanderOn R φ)
    (hRθ : ∀ v ∈ R, θ ≤ ((subdivGraph n H F).degIn R v : ℝ))
    (hRvol : (subdivGraph n H F).volIn (X ∪ midpoints n F)
        (((X ∪ midpoints n F) \ midpoints n F) \ R) +
        2 * C * (subdivGraph n H F).cutIn (X ∪ midpoints n F) R ≤
      2 * C * (subdivGraph n H F).cutIn (X ∪ midpoints n F) (midpoints n F)) :
    R ⊆ X ∧ (Graph.mk n H).IsConductanceExpanderOn R φ ∧
      (∀ v ∈ R, θ ≤ ((Graph.mk n H).degIn R v : ℝ)) ∧
      (Graph.mk n (H ++ F)).volIn X (X \ R) ≤ 4 * C * F.length := by
  have hYB : (X ∪ midpoints n F) \ midpoints n F = X := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hB⟩
      · exact h
      · exact absurd h hB
    · intro hv
      refine ⟨Or.inl hv, fun hB => ?_⟩
      have h1 := Finset.mem_range.mp (hX hv)
      simp only [midpoints, Finset.mem_Ico] at hB
      omega
  rw [hYB] at hRB hRvol
  have hRn : R ⊆ Finset.range n := hRB.trans hX
  have hins := inside_subdivGraph (H := H) (F := F) hRn
  refine ⟨hRB, ?_, ?_, ?_⟩
  · intro S hS hne hneR
    have h := hRφ S hS hne hneR
    simpa only [Graph.cutIn, Graph.volIn, Graph.degIn, hins] using h
  · intro v hv
    have h := hRθ v hv
    simpa only [Graph.degIn, hins] using h
  · have h1 := volIn_le_volIn_subdiv hX hH hF (X \ R)
    rw [show (X \ R) ∩ X = X \ R from Finset.inter_eq_left.mpr Finset.sdiff_subset] at h1
    have h2 := cutIn_le_volIn (subdivGraph n H F) (X ∪ midpoints n F) (midpoints n F)
    have h3 := volIn_midpoints_le hX hH hF
    have h4 : 2 * C * (subdivGraph n H F).cutIn (X ∪ midpoints n F) (midpoints n F) ≤
        2 * C * (2 * F.length) := Nat.mul_le_mul_left _ (h2.trans h3)
    have h5 : 2 * C * (2 * F.length) = 4 * C * F.length := by ring
    omega

/-- The pruning constant at `φ₀ = ρ / 3` is at most `15 / ρ` when `0 < ρ ≤ 1`. -/
theorem cap_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ((max 7 (Nat.ceil (4 / (ρ / 3)) + 2) : ℕ) : ℝ) ≤ 15 / ρ := by
  have h4 : 4 / (ρ / 3) = 12 / ρ := by field_simp; ring
  have hceil : (Nat.ceil (4 / (ρ / 3)) : ℝ) < 12 / ρ + 1 := by
    rw [← h4]
    exact Nat.ceil_lt_add_one (by positivity)
  have h1 : (1 : ℝ) ≤ 1 / ρ := by rw [le_div_iff₀ hρ0]; linarith
  have h12 : 12 / ρ = 12 * (1 / ρ) := by ring
  have h15 : 15 / ρ = 15 * (1 / ρ) := by ring
  push_cast
  apply max_le
  · rw [h15]; linarith
  · rw [h15]; rw [h12] at hceil; linarith

/-- **`RemoveFake` (fake-edge removal).** Let `X ⊆ {0, …, n - 1}`, let the real edges `H` lie
below `n` and the fake edges `F` inside `X`. Suppose `K = H + F` has conductance at least `ρ` on
`X`, with `0 < ρ ≤ 1`, and that every vertex of `X` has positive degree in `K[X]`. Then the set
`R = removeFake n H F X ρ` lies in `X`, `H` has conductance at least `ρ / 9` on `R`, every vertex
of `R` has positive degree in `H[R]`, and the removed volume `vol_K(X \ R)` is at most
`60 |F| / ρ`. -/
theorem removeFake_spec {n : ℕ} {H F : List (ℕ × ℕ)} {X : Finset ℕ} (hX : X ⊆ Finset.range n)
    (hH : ∀ e ∈ H, e.1 < n ∧ e.2 < n) (hF : ∀ e ∈ F, e.1 ∈ X ∧ e.2 ∈ X) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hK : (Graph.mk n (H ++ F)).IsConductanceExpanderOn X ρ)
    (hdeg : ∀ v ∈ X, 1 ≤ (Graph.mk n (H ++ F)).degIn X v) :
    removeFake n H F X ρ ⊆ X ∧
      (Graph.mk n H).IsConductanceExpanderOn (removeFake n H F X ρ) (ρ / 9) ∧
      (∀ v ∈ removeFake n H F X ρ, 1 ≤ (Graph.mk n H).degIn (removeFake n H F X ρ) v) ∧
      ((Graph.mk n (H ++ F)).volIn X (X \ removeFake n H F X ρ) : ℝ) ≤ 60 / ρ * F.length := by
  unfold removeFake
  have hJ := subdivGraph_isValid hX hH hF
  have hexp := isConductanceExpanderOn_subdivGraph hX hH hF hρ0 hρ1 hK
  have hθ : ∀ v ∈ X ∪ midpoints n F, v ∉ midpoints n F →
      (1 : ℝ) ≤ ((subdivGraph n H F).degIn (X ∪ midpoints n F) v : ℝ) := by
    intro v hv hvB
    have hvX : v ∈ X := by
      rcases Finset.mem_union.mp hv with h | h
      · exact h
      · exact absurd h hvB
    have h1 := hdeg v hvX
    have h2 := degIn_le_subdiv hX hH hF hvX
    exact_mod_cast h1.trans h2
  obtain ⟨hR1, hR2, hR3, hR4, -, -⟩ := pruneExpander_spec hJ Finset.subset_union_right hexp
    (by positivity) hθ
  obtain ⟨hsub, hφ, hdegR, hvol⟩ := removeFake_of_pruned hX hH hF hR1 hR2 hR3 hR4
  refine ⟨hsub, ?_, ?_, ?_⟩
  · rw [show ρ / 9 = ρ / 3 / 3 by ring]
    exact hφ
  · intro v hv
    have h := hdegR v hv
    by_contra hlt
    rw [Nat.lt_one_iff.mp (not_le.mp hlt), Nat.cast_zero] at h
    linarith
  · have hcap := cap_le hρ0 hρ1
    have hvol' : ((Graph.mk n (H ++ F)).volIn X (X \ pruneExpander (subdivGraph n H F)
        (X ∪ midpoints n F) (midpoints n F) (ρ / 3) 1) : ℝ) ≤
        4 * ((max 7 (Nat.ceil (4 / (ρ / 3)) + 2) : ℕ) : ℝ) * F.length := by
      exact_mod_cast hvol
    have hf : (0 : ℝ) ≤ F.length := Nat.cast_nonneg _
    calc ((Graph.mk n (H ++ F)).volIn X (X \ pruneExpander (subdivGraph n H F)
          (X ∪ midpoints n F) (midpoints n F) (ρ / 3) 1) : ℝ)
        ≤ 4 * ((max 7 (Nat.ceil (4 / (ρ / 3)) + 2) : ℕ) : ℝ) * F.length := hvol'
      _ ≤ 4 * (15 / ρ) * F.length := by gcongr
      _ = 60 / ρ * F.length := by ring

/-- If every vertex of `S` has degree at least one in `G[X]`, then `|S|` is at most the volume of
`S`. -/
theorem card_le_volIn {G : Graph} {X S : Finset ℕ} (h : ∀ v ∈ S, 1 ≤ G.degIn X v) :
    S.card ≤ G.volIn X S := by
  unfold Graph.volIn
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum h

end MinCostFlow.ExpanderDecomp
