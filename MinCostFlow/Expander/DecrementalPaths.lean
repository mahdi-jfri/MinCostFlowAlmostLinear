module

public import MinCostFlow.Statement.Cited.ChuzhoySaranurak

import MinCostFlow.Expander.GraphHelpers
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 8.6: Reduction from Multigraphs with Self-Loops to [CS21]

Formalizes the mathematical reduction and parameter derivation for Theorem 8.6
(van den Brand et al., arXiv:2309.16629v1, page 41) from `Cited.DecrementalExpanderPaths`
([CS21] Theorem 3.9, `MinCostFlow/Statement/Cited/ChuzhoySaranurak.lean`).

The cited data structure requires a simple, valid graph with at least one edge, no isolated
vertices, and conductance `≥ csPhi Kγ c m = 1 / (c · csGamma Kγ m)`. Algorithm 4 applies this tool
to multigraphs `J_i[X]` and witness graphs `W_{J_i[X]}` (`Theorem 8.4`), which may have parallel
edges and self-loops, and have conductance `φ ≥ 1 / (C₁ · exp(C₀ · log^{2/3}(m+2) · log log(m+2)))`.

## Reduction
For any valid multigraph `G` (possibly with parallel edges and self-loops) having `1 ≤ G.m` and no
isolated vertices (`∀ v < G.n, 1 ≤ G.deg v`):
1. **`subdivGraph G`**: 2-subdivides each edge `j < G.m` with endpoints `(u_j, v_j)` into a length-3
   path `u_j — (n + 2j) — (n + 2j + 1) — v_j`. This yields a valid simple graph with `n + 2m`
   vertices, `3m` edges, `deg_{G_s}(u) = deg_G(u)` for original vertices, `deg_{G_s}(w) = 2` for
   subdivision vertices, and conductance `≥ φ / 10` whenever `G` is a `φ`-expander (`0 ≤ φ ≤ 1`).
2. **`subdivDel`**: translates edge deletion index `j` in `G` to middle edge `3j + 1` in `G_s`.
3. **`projSet`**: intersects `S_s` with `G.verts`, preserving `(G.vol (projSet G.n S_s) ≤ G_s.vol S_s)`.
4. **`projPath`**: filters any simple path `P_s` in `(G_s \ subdivDel del) \ S_s` between original
   vertices `u, v < G.n` to `G.verts`, yielding a simple path in `(graphAfterDel G del) \ V̂` of
   length `(P_s.length - 1) / 3 ≤ P_s.length - 1`.
5. **`csGamma_dominates_sb` / `theorem_8_6`**: shows `csPhi Kγ c (3 * m) ≤ φ(m) / 10` for large
   enough constant `c ≥ c₀` (since `log^{3/4}` dominates `log^{2/3} log log`), yielding
   path length / query bound `exp(O(q · log^{3/4}(m + 2)))`, as in the README ("Where the proof
   departs from the paper").
-/

namespace MinCostFlow.Expander

@[expose] public section

/-- Three-edge 2-subdivision gadget for edge index `j` (`(u, v)`) in a graph on `n` vertices. -/
def subdivEdge (n j : ℕ) (e : ℕ × ℕ) : List (ℕ × ℕ) :=
  [(e.1, n + 2 * j), (n + 2 * j, n + 2 * j + 1), (n + 2 * j + 1, e.2)]

/-- The 2-subdivision `G_s` of a valid multigraph `G` (possibly with parallel edges and
self-loops). -/
def subdivGraph (G : Cited.Graph) : Cited.Graph :=
  ⟨G.n + 2 * G.m,
    (List.range G.m).flatMap fun j => subdivEdge G.n j (G.edges.getD j (0, 0))⟩

/-- Translates a list of deleted edge indices in `G` to the middle edges `3j + 1` of
`subdivGraph G`. -/
def subdivDel (deleted : List ℕ) : List ℕ :=
  deleted.map fun j => 3 * j + 1

/-- Intersects the pruned vertex set `S_s ⊆ (subdivGraph G).verts` with `G.verts`. -/
def projSet (n : ℕ) (S_s : Finset ℕ) : Finset ℕ :=
  S_s.filter (· < n)

/-- Filters a path `P_s` in `subdivGraph G` down to original vertices `< n`. -/
def projPath (n : ℕ) (P_s : List ℕ) : List ℕ :=
  P_s.filter (· < n)

/-- Extracts the original edge indices `(y - n) / 2` traversed by a path `P_s` in
`subdivGraph G` between original vertices `< n`. -/
def projEdges (n : ℕ) : List ℕ → List ℕ
  | _ :: y :: _ :: w :: rest => (y - n) / 2 :: projEdges n (w :: rest)
  | _ => []

/-- The subgraph obtained from `G` after deleting edge indices `deleted` (analogous to
`Cited.PrunedExpander.current`). -/
def graphAfterDel (G : Cited.Graph) (deleted : List ℕ) : Cited.Graph :=
  ⟨G.n, ((List.range G.m).filter fun j => j ∉ deleted).map fun j => G.edges.getD j (0, 0)⟩

end

section

private lemma length_flatMap_three {α β : Type*} (l : List α) (g : α → List β)
    (hg : ∀ a ∈ l, (g a).length = 3) :
    (l.flatMap g).length = 3 * l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have ha := hg a List.mem_cons_self
    have ih' := ih fun x hx => hg x (List.mem_cons_of_mem _ hx)
    simp only [List.flatMap_cons, List.length_append, ha, ih', List.length_cons]
    ring

private lemma sum_map_flatMap {α β : Type*} (l : List α) (g : α → List β) (f : β → ℕ) :
    ((l.flatMap g).map f).sum = (l.map fun a => ((g a).map f).sum).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]

private lemma edges_eq_map_range (L : List (ℕ × ℕ)) :
    ((List.range L.length).map fun j => L.getD j (0, 0)) = L := by
  induction L with
  | nil => simp
  | cons a as ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.getD_cons_zero]
    congr 1

private lemma subdivGraph_getD_aux (n : ℕ) (F : ℕ → ℕ × ℕ) :
    ∀ (m k : ℕ), k < 3 * m →
      ((List.range m).flatMap fun j => subdivEdge n j (F j)).getD k (0, 0) =
        let j := k / 3
        if k % 3 = 0 then ( (F j).1, n + 2 * j )
        else if k % 3 = 1 then (n + 2 * j, n + 2 * j + 1)
        else (n + 2 * j + 1, (F j).2)
  | 0, k, hk => by omega
  | m + 1, k, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    set L₀ := (List.range m).flatMap fun j => subdivEdge n j (F j)
    have hlen : L₀.length = 3 * m := by
      have h := length_flatMap_three (List.range m) (fun j => subdivEdge n j (F j))
        (fun _ _ => by simp [subdivEdge])
      rw [List.length_range] at h
      exact h
    by_cases hklt : k < 3 * m
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
      exact subdivGraph_getD_aux n F m k hklt
    · have hkge : 3 * m ≤ k := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
      have hdiv : k / 3 = m := by omega
      rcases show k - 3 * m = 0 ∨ k - 3 * m = 1 ∨ k - 3 * m = 2 by omega with h0 | h1 | h2
      · have hmod : k % 3 = 0 := by omega
        simp [h0, hdiv, hmod, subdivEdge]
      · have hmod : k % 3 = 1 := by omega
        simp [h1, hdiv, hmod, subdivEdge]
      · have hmod : k % 3 = 2 := by omega
        simp [h2, hdiv, hmod, subdivEdge]

private lemma subdivGraph_sum_map (G : Cited.Graph) (f : ℕ × ℕ → ℕ) :
    ((subdivGraph G).edges.map f).sum =
      ((List.range G.m).map fun j =>
        let e := G.edges.getD j (0, 0)
        f (e.1, G.n + 2 * j) + f (G.n + 2 * j, G.n + 2 * j + 1) +
          f (G.n + 2 * j + 1, e.2)).sum := by
  dsimp only [subdivGraph]
  rw [sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [subdivEdge, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

private lemma graph_sum_map_eq_range (G : Cited.Graph) (f : ℕ × ℕ → ℕ) :
    (G.edges.map f).sum =
      ((List.range G.m).map fun j => f (G.edges.getD j (0, 0))).sum := by
  have h : G.edges = (List.range G.m).map fun j => G.edges.getD j (0, 0) :=
    (edges_eq_map_range G.edges).symm
  conv_lhs => rw [h, List.map_map]
  rfl

private lemma graph_deg_sum_range (G : Cited.Graph) (hV : G.IsValid) (u : ℕ) :
    G.deg u =
      ((List.range G.m).map fun j =>
        let e := G.edges.getD j (0, 0)
        (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)).sum := by
  unfold Cited.Graph.deg
  rw [degIn_eq_sum_map, inside_verts_of_isValid hV]
  exact graph_sum_map_eq_range G _

private lemma graph_vol_sum_range (G : Cited.Graph) (hV : G.IsValid) (S : Finset ℕ) :
    G.vol S =
      ((List.range G.m).map fun j =>
        let e := G.edges.getD j (0, 0)
        (if e.1 ∈ S then 1 else 0) + (if e.2 ∈ S then 1 else 0)).sum := by
  unfold Cited.Graph.vol
  rw [volIn_eq_sum_map, inside_verts_of_isValid hV]
  exact graph_sum_map_eq_range G _

private lemma graph_cut_sum_range (G : Cited.Graph) (hV : G.IsValid) (S : Finset ℕ) :
    G.cut S =
      ((List.range G.m).map fun j =>
        let e := G.edges.getD j (0, 0)
        if (decide (e.1 ∈ S) != decide (e.2 ∈ S)) then 1 else 0).sum := by
  unfold Cited.Graph.cut
  rw [cutIn_eq_sum_map, inside_verts_of_isValid hV]
  exact graph_sum_map_eq_range G _

private lemma getD_mem_edges_of_lt {G : Cited.Graph} {j : ℕ} (hj : j < G.m) :
    G.edges.getD j (0, 0) ∈ G.edges := by
  rw [List.getD_eq_getElem?_getD]
  have hsome : G.edges[j]? = some G.edges[j] := List.getElem?_eq_getElem hj
  rw [hsome]
  exact List.getElem_mem hj

private lemma getD_valid_of_lt {G : Cited.Graph} (hV : G.IsValid) {j : ℕ} (hj : j < G.m) :
    (G.edges.getD j (0, 0)).1 < G.n ∧ (G.edges.getD j (0, 0)).2 < G.n :=
  hV _ (getD_mem_edges_of_lt hj)

private lemma indicator_range_sum_two (k : ℕ) :
    ∀ (m : ℕ), k < m →
      ((List.range m).map fun j => if j = k then (2 : ℕ) else 0).sum = 2
  | 0, hk => by omega
  | m + 1, hk => by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · have ih := indicator_range_sum_two k m hlt
      have hne : m ≠ k := by omega
      simp [ih, hne]
    · have hz : ((List.range k).map fun j => if j = k then (2 : ℕ) else 0) =
          (List.range k).map fun _ => 0 := by
        apply List.map_congr_left
        intro j hj
        rw [List.mem_range] at hj
        simp [show j ≠ k by omega]
      rw [hz, sum_map_const]
      simp

end

public section

lemma subdivGraph_n (G : Cited.Graph) : (subdivGraph G).n = G.n + 2 * G.m := rfl

lemma subdivGraph_m (G : Cited.Graph) : (subdivGraph G).m = 3 * G.m := by
  dsimp only [Cited.Graph.m, subdivGraph]
  have h := length_flatMap_three (List.range G.m)
    (fun j => subdivEdge G.n j (G.edges.getD j (0, 0)))
    (fun _ _ => by simp [subdivEdge])
  rw [List.length_range] at h
  exact h

lemma subdivGraph_edges_getD (G : Cited.Graph) {k : ℕ} (hk : k < 3 * G.m) :
    (subdivGraph G).edges.getD k (0, 0) =
      let j := k / 3
      let e := G.edges.getD j (0, 0)
      if k % 3 = 0 then (e.1, G.n + 2 * j)
      else if k % 3 = 1 then (G.n + 2 * j, G.n + 2 * j + 1)
      else (G.n + 2 * j + 1, e.2) :=
  subdivGraph_getD_aux G.n (fun j => G.edges.getD j (0, 0)) G.m k hk

lemma subdivGraph_isValid {G : Cited.Graph} (hV : G.IsValid) :
    (subdivGraph G).IsValid := by
  intro e he
  dsimp only [subdivGraph] at he ⊢
  simp only [List.mem_flatMap, List.mem_range, subdivEdge,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ⟨j, hj, rfl | rfl | rfl⟩
  · have := getD_valid_of_lt hV hj; omega
  · omega
  · have := getD_valid_of_lt hV hj; omega

lemma subdivGraph_isSimple {G : Cited.Graph} (hV : G.IsValid) :
    (subdivGraph G).IsSimple := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [subdivGraph, List.mem_flatMap, List.mem_range, subdivEdge,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with ⟨j, hj, rfl | rfl | rfl⟩
    · have := getD_valid_of_lt hV hj; omega
    · omega
    · have := getD_valid_of_lt hV hj; omega
  · have hpair : ∀ (m : ℕ), m ≤ G.m →
        List.Pairwise (fun e f : ℕ × ℕ => s(e.1, e.2) ≠ s(f.1, f.2))
          ((List.range m).flatMap fun j => subdivEdge G.n j (G.edges.getD j (0, 0))) := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
        have ihm := ih (by omega)
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
        apply List.pairwise_append.mpr
        have hvm := getD_valid_of_lt hV (by omega : m < G.m)
        refine ⟨ihm, ?_, ?_⟩
        · dsimp only [subdivEdge]
          rw [List.pairwise_cons, List.pairwise_cons]
          refine ⟨?_, ?_, List.pairwise_singleton _ _⟩
          · intro x hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · intro h; rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
            · intro h; rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
          · intro x hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl
            intro h; rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        · intro e he f hf
          simp only [List.mem_flatMap, List.mem_range, subdivEdge,
            List.mem_cons, List.not_mem_nil, or_false] at he hf
          rcases he with ⟨j, hj, rfl | rfl | rfl⟩ <;>
            rcases hf with rfl | rfl | rfl <;>
            intro h <;> rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    exact hpair G.m (le_refl _)

lemma subdivGraph_deg_orig {G : Cited.Graph} (hV : G.IsValid) {u : ℕ} (hu : u < G.n) :
    (subdivGraph G).deg u = G.deg u := by
  have hSV := subdivGraph_isValid hV
  unfold Cited.Graph.deg
  rw [degIn_eq_sum_map, inside_verts_of_isValid hSV,
    subdivGraph_sum_map]
  have hR := graph_deg_sum_range G hV u
  unfold Cited.Graph.deg at hR
  rw [hR]
  congr 1
  apply List.map_congr_left
  intro j _
  have hne1 : G.n + 2 * j ≠ u := by omega
  have hne2 : G.n + 2 * j + 1 ≠ u := by omega
  simp [hne1, hne2]

lemma subdivGraph_deg_mid {G : Cited.Graph} (hV : G.IsValid) {k : ℕ} (hk : k < G.m) :
    (subdivGraph G).deg (G.n + 2 * k) = 2 ∧ (subdivGraph G).deg (G.n + 2 * k + 1) = 2 := by
  have hSV := subdivGraph_isValid hV
  unfold Cited.Graph.deg
  rw [degIn_eq_sum_map, inside_verts_of_isValid hSV,
    subdivGraph_sum_map,
    degIn_eq_sum_map, inside_verts_of_isValid hSV,
    subdivGraph_sum_map]
  constructor
  · have hcongr :
        ((List.range G.m).map fun j =>
          let e := G.edges.getD j (0, 0)
          ((if e.1 = G.n + 2 * k then 1 else 0) + (if G.n + 2 * j = G.n + 2 * k then 1 else 0)) +
          ((if G.n + 2 * j = G.n + 2 * k then 1 else 0) + (if G.n + 2 * j + 1 = G.n + 2 * k then 1 else 0)) +
          ((if G.n + 2 * j + 1 = G.n + 2 * k then 1 else 0) + (if e.2 = G.n + 2 * k then 1 else 0))) =
        ((List.range G.m).map fun j => if j = k then (2 : ℕ) else 0) := by
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      have hv := getD_valid_of_lt hV hj
      have h1 : (G.edges.getD j (0, 0)).1 ≠ G.n + 2 * k := by omega
      have h2 : (G.edges.getD j (0, 0)).2 ≠ G.n + 2 * k := by omega
      have h3 : G.n + 2 * j + 1 ≠ G.n + 2 * k := by omega
      have h4 : G.n + 2 * j = G.n + 2 * k ↔ j = k := by omega
      dsimp only
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
      by_cases hjk : j = k
      · rw [ite_eq_left (h4.mpr hjk), ite_eq_left hjk]
      · rw [ite_eq_right (fun hh => hjk (h4.mp hh)), ite_eq_right hjk]
    rw [hcongr]
    exact indicator_range_sum_two k G.m hk
  · have hcongr :
        ((List.range G.m).map fun j =>
          let e := G.edges.getD j (0, 0)
          ((if e.1 = G.n + 2 * k + 1 then 1 else 0) + (if G.n + 2 * j = G.n + 2 * k + 1 then 1 else 0)) +
          ((if G.n + 2 * j = G.n + 2 * k + 1 then 1 else 0) +
            (if G.n + 2 * j + 1 = G.n + 2 * k + 1 then 1 else 0)) +
          ((if G.n + 2 * j + 1 = G.n + 2 * k + 1 then 1 else 0) +
            (if e.2 = G.n + 2 * k + 1 then 1 else 0))) =
        ((List.range G.m).map fun j => if j = k then (2 : ℕ) else 0) := by
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      have hv := getD_valid_of_lt hV hj
      have h1 : (G.edges.getD j (0, 0)).1 ≠ G.n + 2 * k + 1 := by omega
      have h2 : (G.edges.getD j (0, 0)).2 ≠ G.n + 2 * k + 1 := by omega
      have h3 : G.n + 2 * j ≠ G.n + 2 * k + 1 := by omega
      have h4 : G.n + 2 * j + 1 = G.n + 2 * k + 1 ↔ j = k := by omega
      dsimp only
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
      by_cases hjk : j = k
      · rw [ite_eq_left (h4.mpr hjk), ite_eq_left hjk]
      · rw [ite_eq_right (fun hh => hjk (h4.mp hh)), ite_eq_right hjk]
    rw [hcongr]
    exact indicator_range_sum_two k G.m hk

lemma subdivGraph_no_isolated {G : Cited.Graph} (hV : G.IsValid)
    (hno : ∀ v < G.n, 1 ≤ G.deg v) :
    ∀ w < (subdivGraph G).n, 1 ≤ (subdivGraph G).deg w := by
  intro w hw
  rw [subdivGraph_n] at hw
  by_cases hlt : w < G.n
  · rw [subdivGraph_deg_orig hV hlt]
    exact hno w hlt
  · have hge : G.n ≤ w := by omega
    have hk : (w - G.n) / 2 < G.m := by omega
    rcases Nat.mod_two_eq_zero_or_one (w - G.n) with hev | hod
    · have hw_eq : w = G.n + 2 * ((w - G.n) / 2) := by omega
      rw [hw_eq, (subdivGraph_deg_mid hV hk).1]
      omega
    · have hw_eq : w = G.n + 2 * ((w - G.n) / 2) + 1 := by omega
      rw [hw_eq, (subdivGraph_deg_mid hV hk).2]
      omega

/-- Conductance preservation under 2-subdivision: if `G` is a `φ`-expander (`0 ≤ φ ≤ 1`), then
`subdivGraph G` is a `(φ / 10)`-expander on `(subdivGraph G).verts`. -/
lemma subdivGraph_expander {G : Cited.Graph} (hV : G.IsValid) {φ : ℝ}
    (hφ₀ : 0 ≤ φ) (hφ₁ : φ ≤ 1)
    (hexp : G.IsConductanceExpanderOn G.verts φ) :
    (subdivGraph G).IsConductanceExpanderOn (subdivGraph G).verts (φ / 10) := by
  set G_s := subdivGraph G
  have hSV : G_s.IsValid := subdivGraph_isValid hV
  intro A hAV hAne hAneV
  set B := G_s.verts \ A
  set A₀ := A ∩ G.verts
  set B₀ := G.verts \ A₀
  let eOf (j : ℕ) := G.edges.getD j (0, 0)
  let aOf (j : ℕ) := G.n + 2 * j
  let bOf (j : ℕ) := G.n + 2 * j + 1
  let volOrigA (j : ℕ) :=
    (if (eOf j).1 ∈ A₀ then 1 else 0) + (if (eOf j).2 ∈ A₀ then 1 else 0)
  let volOrigB (j : ℕ) :=
    (if (eOf j).1 ∈ B₀ then 1 else 0) + (if (eOf j).2 ∈ B₀ then 1 else 0)
  let volMidA (j : ℕ) :=
    2 * (if aOf j ∈ A then 1 else 0) + 2 * (if bOf j ∈ A then 1 else 0)
  let volMidB (j : ℕ) :=
    2 * (if aOf j ∈ B then 1 else 0) + 2 * (if bOf j ∈ B then 1 else 0)
  let badA (j : ℕ) :=
    if (eOf j).1 ∉ A₀ ∧ (eOf j).2 ∉ A₀ ∧ (aOf j ∈ A ∨ bOf j ∈ A) then 1 else 0
  let badB (j : ℕ) :=
    if (eOf j).1 ∈ A₀ ∧ (eOf j).2 ∈ A₀ ∧ (aOf j ∈ B ∨ bOf j ∈ B) then 1 else 0
  let mix (j : ℕ) :=
    if (decide ((eOf j).1 ∈ A₀) != decide ((eOf j).2 ∈ A₀)) then 1 else 0
  let cutGad (j : ℕ) :=
    (if (decide ((eOf j).1 ∈ A) != decide (aOf j ∈ A)) then 1 else 0) +
    (if (decide (aOf j ∈ A) != decide (bOf j ∈ A)) then 1 else 0) +
    (if (decide (bOf j ∈ A) != decide ((eOf j).2 ∈ A)) then 1 else 0)
  have hmemA₀ : ∀ {j : ℕ}, j ∈ List.range G.m →
      (((eOf j).1 ∈ A₀ ↔ (eOf j).1 ∈ A) ∧ ((eOf j).2 ∈ A₀ ↔ (eOf j).2 ∈ A)) := by
    intro j hj
    rw [List.mem_range] at hj
    have hv := getD_valid_of_lt hV hj
    refine ⟨?_, ?_⟩
    · simp only [A₀, Cited.Graph.verts, Finset.mem_inter, Finset.mem_range]
      exact ⟨fun h => h.1, fun h => ⟨h, hv.1⟩⟩
    · simp only [A₀, Cited.Graph.verts, Finset.mem_inter, Finset.mem_range]
      exact ⟨fun h => h.1, fun h => ⟨h, hv.2⟩⟩
  have hmemB : ∀ {w : ℕ}, w ∈ G_s.verts → (w ∈ B ↔ w ∉ A) := by
    intro w hw; simp [B, hw]
  have hmemB₀ : ∀ {j : ℕ}, j ∈ List.range G.m →
      (((eOf j).1 ∈ B₀ ↔ (eOf j).1 ∉ A) ∧ ((eOf j).2 ∈ B₀ ↔ (eOf j).2 ∉ A)) := by
    intro j hj
    rw [List.mem_range] at hj
    have hv := getD_valid_of_lt hV hj
    have hm := hmemA₀ (List.mem_range.mpr hj)
    refine ⟨?_, ?_⟩
    · simp only [B₀, Cited.Graph.verts, Finset.mem_sdiff, Finset.mem_range]
      exact ⟨fun h => hm.1.not.mp h.2, fun h => ⟨hv.1, hm.1.not.mpr h⟩⟩
    · simp only [B₀, Cited.Graph.verts, Finset.mem_sdiff, Finset.mem_range]
      exact ⟨fun h => hm.2.not.mp h.2, fun h => ⟨hv.2, hm.2.not.mpr h⟩⟩
  have hvolA_eq : G_s.vol A = ((List.range G.m).map fun j => volOrigA j + volMidA j).sum := by
    unfold Cited.Graph.vol
    rw [volIn_eq_sum_map, inside_verts_of_isValid hSV,
      subdivGraph_sum_map]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hm := hmemA₀ hj
    simp only [volOrigA, volMidA, eOf, aOf, bOf, hm.1, hm.2]
    ring
  have hvolB_eq : G_s.vol B = ((List.range G.m).map fun j => volOrigB j + volMidB j).sum := by
    unfold Cited.Graph.vol
    rw [volIn_eq_sum_map, inside_verts_of_isValid hSV,
      subdivGraph_sum_map]
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    have hv := getD_valid_of_lt hV hj
    have hm := hmemB₀ (List.mem_range.mpr hj)
    have hbv1 : (eOf j).1 ∈ B ↔ (eOf j).1 ∉ A :=
      hmemB (by
        simp only [Cited.Graph.verts, G_s, subdivGraph_n, Finset.mem_range]
        exact Nat.lt_of_lt_of_le hv.1 (by omega))
    have hbv2 : (eOf j).2 ∈ B ↔ (eOf j).2 ∉ A :=
      hmemB (by
        simp only [Cited.Graph.verts, G_s, subdivGraph_n, Finset.mem_range]
        exact Nat.lt_of_lt_of_le hv.2 (by omega))
    simp only [volOrigB, volMidB, eOf, aOf, bOf, hm.1, hm.2, hbv1, hbv2]
    ring
  have hcut_eq : G_s.cut A = ((List.range G.m).map cutGad).sum := by
    unfold Cited.Graph.cut
    rw [cutIn_eq_sum_map, inside_verts_of_isValid hSV,
      subdivGraph_sum_map]
  have hvolA_orig : G.vol A₀ = ((List.range G.m).map volOrigA).sum := graph_vol_sum_range G hV A₀
  have hvolB_orig : G.vol B₀ = ((List.range G.m).map volOrigB).sum := graph_vol_sum_range G hV B₀
  have hcut_orig : G.cut A₀ = ((List.range G.m).map mix).sum := graph_cut_sum_range G hV A₀
  set K_badA := ((List.range G.m).map badA).sum
  set K_badB := ((List.range G.m).map badB).sum
  have hpt_volA : ∀ j ∈ List.range G.m, volOrigA j + volMidA j ≤ 5 * volOrigA j + 4 * badA j := by
    intro j hj
    have hm := hmemA₀ hj
    simp only [volOrigA, volMidA, badA, hm.1, hm.2]
    by_cases p1 : (eOf j).1 ∈ A <;> by_cases p2 : (eOf j).2 ∈ A <;>
      by_cases pa : aOf j ∈ A <;> by_cases pb : bOf j ∈ A <;>
      simp [p1, p2, pa, pb]
  have hpt_volB : ∀ j ∈ List.range G.m, volOrigB j + volMidB j ≤ 5 * volOrigB j + 4 * badB j := by
    intro j hj
    rw [List.mem_range] at hj
    have hm := hmemB₀ (List.mem_range.mpr hj)
    have hmA := hmemA₀ (List.mem_range.mpr hj)
    have haB : aOf j ∈ B ↔ aOf j ∉ A := hmemB (by simp [Cited.Graph.verts, G_s, subdivGraph_n, aOf]; omega)
    have hbB : bOf j ∈ B ↔ bOf j ∉ A := hmemB (by simp [Cited.Graph.verts, G_s, subdivGraph_n, bOf]; omega)
    simp only [volOrigB, volMidB, badB, hm.1, hm.2, hmA.1, hmA.2, haB, hbB]
    by_cases p1 : (eOf j).1 ∈ A <;> by_cases p2 : (eOf j).2 ∈ A <;>
      by_cases pa : aOf j ∈ A <;> by_cases pb : bOf j ∈ A <;>
      simp [p1, p2, pa, pb]
  have hpt_cut : ∀ j ∈ List.range G.m, mix j + 2 * badA j + 2 * badB j ≤ cutGad j := by
    intro j hj
    rw [List.mem_range] at hj
    have hmA := hmemA₀ (List.mem_range.mpr hj)
    have haB : aOf j ∈ B ↔ aOf j ∉ A := hmemB (by simp [Cited.Graph.verts, G_s, subdivGraph_n, aOf]; omega)
    have hbB : bOf j ∈ B ↔ bOf j ∉ A := hmemB (by simp [Cited.Graph.verts, G_s, subdivGraph_n, bOf]; omega)
    simp only [mix, badA, badB, cutGad, hmA.1, hmA.2, haB, hbB]
    by_cases p1 : (eOf j).1 ∈ A <;> by_cases p2 : (eOf j).2 ∈ A <;>
      by_cases pa : aOf j ∈ A <;> by_cases pb : bOf j ∈ A <;>
      simp [p1, p2, pa, pb]
  have hsumA : G_s.vol A ≤ 5 * G.vol A₀ + 4 * K_badA := by
    rw [hvolA_eq, hvolA_orig]
    calc ((List.range G.m).map fun j => volOrigA j + volMidA j).sum
        ≤ ((List.range G.m).map fun j => 5 * volOrigA j + 4 * badA j).sum :=
          sum_map_le_sum_map hpt_volA
      _ = 5 * ((List.range G.m).map volOrigA).sum + 4 * K_badA := by
          clear hpt_volA hpt_volB hpt_cut hvolA_eq hvolB_eq hcut_eq
          dsimp only [K_badA]
          induction (List.range G.m) with
          | nil => simp
          | cons j js ih => simp only [List.map_cons, List.sum_cons] at ih ⊢; omega
  have hsumB : G_s.vol B ≤ 5 * G.vol B₀ + 4 * K_badB := by
    rw [hvolB_eq, hvolB_orig]
    calc ((List.range G.m).map fun j => volOrigB j + volMidB j).sum
        ≤ ((List.range G.m).map fun j => 5 * volOrigB j + 4 * badB j).sum :=
          sum_map_le_sum_map hpt_volB
      _ = 5 * ((List.range G.m).map volOrigB).sum + 4 * K_badB := by
          clear hpt_volA hpt_volB hpt_cut hvolA_eq hvolB_eq hcut_eq hsumA
          dsimp only [K_badB]
          induction (List.range G.m) with
          | nil => simp
          | cons j js ih => simp only [List.map_cons, List.sum_cons] at ih ⊢; omega
  have hsumCut : G.cut A₀ + 2 * K_badA + 2 * K_badB ≤ G_s.cut A := by
    rw [hcut_eq, hcut_orig]
    calc ((List.range G.m).map mix).sum + 2 * K_badA + 2 * K_badB
        = ((List.range G.m).map fun j => mix j + 2 * badA j + 2 * badB j).sum := by
          clear hpt_volA hpt_volB hpt_cut hvolA_eq hvolB_eq hcut_eq hsumA hsumB
          dsimp only [K_badA, K_badB]
          induction (List.range G.m) with
          | nil => simp
          | cons j js ih => simp only [List.map_cons, List.sum_cons] at ih ⊢; omega
      _ ≤ ((List.range G.m).map cutGad).sum :=
          sum_map_le_sum_map hpt_cut
  have hcut_eq_orig : G_s.cutIn G_s.verts A = G_s.cut A := rfl
  rw [hcut_eq_orig]
  set μ : ℝ := min (G_s.vol A : ℝ) (G_s.vol B : ℝ)
  change φ / 10 * μ ≤ (G_s.cut A : ℝ)
  have hμ_nn : 0 ≤ μ := le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hφ_le_half : φ / 10 * μ ≤ (1 / 4 : ℝ) * μ := by
    calc φ / 10 * μ ≤ 1 / 10 * μ := mul_le_mul_of_nonneg_right (by linarith) hμ_nn
      _ ≤ (1 / 4 : ℝ) * μ := by linarith
  have hsumA_R : (G_s.vol A : ℝ) ≤ 5 * (G.vol A₀ : ℝ) + 4 * (K_badA : ℝ) := by exact_mod_cast hsumA
  have hsumB_R : (G_s.vol B : ℝ) ≤ 5 * (G.vol B₀ : ℝ) + 4 * (K_badB : ℝ) := by exact_mod_cast hsumB
  have hsumCut_R : (G.cut A₀ : ℝ) + 2 * (K_badA : ℝ) + 2 * (K_badB : ℝ) ≤ (G_s.cut A : ℝ) := by
    exact_mod_cast hsumCut
  by_cases hA0 : A₀ = ∅
  · have hvolA0 : G.vol A₀ = 0 := by simp [hA0, Cited.Graph.vol, Cited.Graph.volIn]
    have hμA : μ ≤ 4 * (K_badA : ℝ) := by
      have h1 := min_le_left (G_s.vol A : ℝ) (G_s.vol B : ℝ)
      rw [hvolA0, Nat.cast_zero] at hsumA_R
      linarith
    have hbadA_le : 2 * (K_badA : ℝ) ≤ (G_s.cut A : ℝ) := by
      have h0 : (0 : ℝ) ≤ (G.cut A₀ : ℝ) := Nat.cast_nonneg _
      have h0b : (0 : ℝ) ≤ (K_badB : ℝ) := Nat.cast_nonneg _
      linarith
    linarith
  · by_cases hB0 : B₀ = ∅
    · have hvolB0 : G.vol B₀ = 0 := by simp [hB0, Cited.Graph.vol, Cited.Graph.volIn]
      have hμB : μ ≤ 4 * (K_badB : ℝ) := by
        have h1 := min_le_right (G_s.vol A : ℝ) (G_s.vol B : ℝ)
        rw [hvolB0, Nat.cast_zero] at hsumB_R
        linarith
      have hbadB_le : 2 * (K_badB : ℝ) ≤ (G_s.cut A : ℝ) := by
        have h0 : (0 : ℝ) ≤ (G.cut A₀ : ℝ) := Nat.cast_nonneg _
        have h0a : (0 : ℝ) ≤ (K_badA : ℝ) := Nat.cast_nonneg _
        linarith
      linarith
    · have hA₀ne : A₀.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA0
      have hA₀sub : A₀ ⊆ G.verts := Finset.inter_subset_right
      have hA₀neV : A₀ ≠ G.verts := by
        intro hEq
        apply hB0
        simp [B₀, hEq]
      have hexpA₀ : φ * min (G.vol A₀ : ℝ) (G.vol B₀ : ℝ) ≤ (G.cut A₀ : ℝ) := by
        exact hexp A₀ hA₀sub hA₀ne hA₀neV
      by_cases hbig : μ / 2 ≤ 4 * (K_badA : ℝ) + 4 * (K_badB : ℝ)
      · have hcut2 : μ / 4 ≤ (G_s.cut A : ℝ) := by
          have h0 : (0 : ℝ) ≤ (G.cut A₀ : ℝ) := Nat.cast_nonneg _
          linarith
        linarith
      · have hsmall : 4 * (K_badA : ℝ) + 4 * (K_badB : ℝ) < μ / 2 := lt_of_not_ge hbig
        have hKA_nn : (0 : ℝ) ≤ (K_badA : ℝ) := Nat.cast_nonneg _
        have hKB_nn : (0 : ℝ) ≤ (K_badB : ℝ) := Nat.cast_nonneg _
        have hA_low : μ / 10 ≤ (G.vol A₀ : ℝ) := by
          have h1 := min_le_left (G_s.vol A : ℝ) (G_s.vol B : ℝ)
          linarith
        have hB_low : μ / 10 ≤ (G.vol B₀ : ℝ) := by
          have h1 := min_le_right (G_s.vol A : ℝ) (G_s.vol B : ℝ)
          linarith
        have hmin_low : μ / 10 ≤ min (G.vol A₀ : ℝ) (G.vol B₀ : ℝ) := le_min hA_low hB_low
        have hexp_sub : φ / 10 * μ ≤ (G.cut A₀ : ℝ) := by
          calc φ / 10 * μ = φ * (μ / 10) := by ring
            _ ≤ φ * min (G.vol A₀ : ℝ) (G.vol B₀ : ℝ) :=
              mul_le_mul_of_nonneg_left hmin_low hφ₀
            _ ≤ (G.cut A₀ : ℝ) := hexpA₀
        linarith

lemma subdivDel_spec {G : Cited.Graph} (del : List ℕ) (hdel : ∀ j ∈ del, j < G.m) :
    (subdivDel del).length = del.length ∧
    (∀ k ∈ subdivDel del, k < (subdivGraph G).m) ∧
    (del.Nodup → (subdivDel del).Nodup) := by
  refine ⟨List.length_map _, ?_, ?_⟩
  · intro k hk
    rw [subdivDel, List.mem_map] at hk
    rcases hk with ⟨j, hj, rfl⟩
    rw [subdivGraph_m]
    have := hdel j hj
    omega
  · intro hnd
    exact hnd.map (fun _ _ h => by omega)

lemma projSet_spec {G : Cited.Graph} (hV : G.IsValid) (S_s : Finset ℕ) :
    projSet G.n S_s ⊆ G.verts ∧ G.vol (projSet G.n S_s) ≤ (subdivGraph G).vol S_s := by
  refine ⟨?_, ?_⟩
  · intro v hv
    rw [projSet, Finset.mem_filter] at hv
    simp [Cited.Graph.verts, hv.2]
  · unfold Cited.Graph.vol Cited.Graph.volIn
    calc ∑ v ∈ projSet G.n S_s, G.degIn G.verts v
        = ∑ v ∈ projSet G.n S_s, G.deg v := rfl
      _ = ∑ v ∈ projSet G.n S_s, (subdivGraph G).deg v := by
          refine Finset.sum_congr rfl fun v hv => ?_
          rw [projSet, Finset.mem_filter] at hv
          exact (subdivGraph_deg_orig hV hv.2).symm
      _ ≤ ∑ v ∈ S_s, (subdivGraph G).deg v := by
          exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

private lemma mem_currentEdges_subdiv_iff {G : Cited.Graph} {del : List ℕ} {a b : ℕ} :
    (a, b) ∈ (Cited.PrunedExpander.currentEdges ⟨subdivGraph G, 2, subdivDel del, ∅⟩) ↔
      ∃ k < 3 * G.m, k ∉ subdivDel del ∧
        (subdivGraph G).edges.getD k (0, 0) = (a, b) := by
  unfold Cited.PrunedExpander.currentEdges
  simp only [subdivGraph_m, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨k, ⟨hk, hnd⟩, he⟩
    exact ⟨k, hk, hnd, he⟩
  · rintro ⟨k, hk, hnd, he⟩
    exact ⟨k, ⟨hk, hnd⟩, he⟩

private lemma projPath_aux {G : Cited.Graph} (hV : G.IsValid) (del : List ℕ) (S_s : Finset ℕ)
    {v : ℕ} (hv : v < G.n) :
    ∀ (nlen : ℕ) (P_s : List ℕ) (u : ℕ),
      P_s.length = nlen →
      u < G.n →
      P_s.Nodup →
      Cited.IsPathAlong
        (Cited.PrunedExpander.currentEdges ⟨subdivGraph G, 2, subdivDel del, S_s⟩) u v P_s →
      Cited.IsPathAlong (graphAfterDel G del).edges u v (projPath G.n P_s) ∧
        3 * ((projPath G.n P_s).length - 1) = P_s.length - 1 ∧
        (projPath G.n P_s).length = (projEdges G.n P_s).length + 1 ∧
        (∀ j ∈ projEdges G.n P_s, j < G.m ∧ j ∉ del) ∧
        (∀ i : ℕ, i < (projEdges G.n P_s).length →
          let j := (projEdges G.n P_s).getD i 0
          let a := (projPath G.n P_s).getD i 0
          let b := (projPath G.n P_s).getD (i + 1) 0
          let e := G.edges.getD j (0, 0)
          (e.1 = a ∧ e.2 = b) ∨ (e.2 = a ∧ e.1 = b)) := by
  intro nlen
  induction nlen using Nat.strong_induction_on with
  | h nlen ih =>
    intro P_s u hlen hu hnd hP
    cases P_s with
    | nil => simp [Cited.IsPathAlong] at hP
    | cons x rest =>
      have hx : x = u := by simpa [Cited.IsPathAlong] using hP.1
      rw [hx] at hlen hnd hP ⊢
      cases rest with
      | nil =>
        have huv : u = v := by simpa [Cited.IsPathAlong] using hP.2.1
        rw [huv] at hu ⊢
        have hfp : projPath G.n [v] = [v] := by simp [projPath, hu]
        rw [hfp]
        refine ⟨isPathAlong_singleton _ v, rfl, ?_, by simp [projEdges], by simp [projEdges]⟩
        simp [projEdges]
      | cons y rest1 =>
        rcases hP with ⟨_, hlast, hch⟩
        rw [List.isChain_cons_cons] at hch
        have hce_eq : (Cited.PrunedExpander.currentEdges ⟨subdivGraph G, 2, subdivDel del, S_s⟩) =
            (Cited.PrunedExpander.currentEdges ⟨subdivGraph G, 2, subdivDel del, ∅⟩) := rfl
        have hy_edge : ∃ k < 3 * G.m, k ∉ subdivDel del ∧
            ((subdivGraph G).edges.getD k (0, 0) = (u, y) ∨
              (subdivGraph G).edges.getD k (0, 0) = (y, u)) := by
          rcases hch.1 with hm | hm
          · rw [hce_eq, mem_currentEdges_subdiv_iff] at hm
            rcases hm with ⟨k, hk, hnd_k, he⟩
            exact ⟨k, hk, hnd_k, Or.inl he⟩
          · rw [hce_eq, mem_currentEdges_subdiv_iff] at hm
            rcases hm with ⟨k, hk, hnd_k, he⟩
            exact ⟨k, hk, hnd_k, Or.inr he⟩
        rcases hy_edge with ⟨k1, hk1, hk1_nd, he1⟩
        rw [subdivGraph_edges_getD G hk1] at he1
        set j := k1 / 3
        have hj : j < G.m := by omega
        have hvj := getD_valid_of_lt hV hj
        have hstep_edge : (∃ w < G.n, ∃ rest2 : List ℕ, ∃ z : ℕ,
            rest1 = z :: w :: rest2 ∧ ¬ y < G.n ∧ ¬ z < G.n ∧
              (y - G.n) / 2 = j ∧ j < G.m ∧ j ∉ del ∧
              (G.edges.getD j (0, 0) = (u, w) ∨ G.edges.getD j (0, 0) = (w, u)) ∧
              ((u, w) ∈ (graphAfterDel G del).edges ∨ (w, u) ∈ (graphAfterDel G del).edges)) := by
          by_cases hm0 : k1 % 3 = 0
          · simp only [hm0, ↓reduceIte] at he1
            have hy_eq : u = (G.edges.getD j (0, 0)).1 ∧ y = G.n + 2 * j := by
              rcases he1 with h | h <;> have h1 := congrArg Prod.fst h <;>
                have h2 := congrArg Prod.snd h <;> omega
            rcases hy_eq with ⟨hu_ej, rfl⟩
            cases rest1 with
            | nil =>
              simp at hlast
              omega
            | cons z rest1' =>
              rw [List.isChain_cons_cons] at hch
              have hne_zu : z ≠ u := by
                have hnd' := List.nodup_cons.mp hnd
                intro hzu; apply hnd'.1; simp [hzu]
              have hz_edge : ∃ k2 < 3 * G.m, k2 ∉ subdivDel del ∧
                  ((subdivGraph G).edges.getD k2 (0, 0) = (G.n + 2 * j, z) ∨
                    (subdivGraph G).edges.getD k2 (0, 0) = (z, G.n + 2 * j)) := by
                rcases hch.2.1 with hm | hm
                · rw [hce_eq, mem_currentEdges_subdiv_iff] at hm
                  rcases hm with ⟨k, hk, hndk, hek⟩
                  exact ⟨k, hk, hndk, Or.inl hek⟩
                · rw [hce_eq, mem_currentEdges_subdiv_iff] at hm
                  rcases hm with ⟨k, hk, hndk, hek⟩
                  exact ⟨k, hk, hndk, Or.inr hek⟩
              rcases hz_edge with ⟨k2, hk2, hk2_nd, he2⟩
              rw [subdivGraph_edges_getD G hk2] at he2
              have hv2 := getD_valid_of_lt hV (by omega : k2 / 3 < G.m)
              have hj2 : k2 / 3 = j ∧ k2 % 3 = 1 ∧ z = G.n + 2 * j + 1 := by
                by_cases h0 : k2 % 3 = 0
                · simp only [h0, ↓reduceIte] at he2
                  rcases he2 with h | h
                  · have hf := congrArg Prod.fst h; omega
                  · have hf := congrArg Prod.fst h
                    have hs := congrArg Prod.snd h
                    have hdiv : k2 / 3 = j := by omega
                    rw [hdiv] at hf
                    omega
                · by_cases h1 : k2 % 3 = 1
                  · simp only [h1, Nat.one_ne_zero, ↓reduceIte] at he2
                    rcases he2 with h | h <;> have hf := congrArg Prod.fst h <;>
                      have hs := congrArg Prod.snd h <;> omega
                  · simp only [h0, h1, ↓reduceIte] at he2
                    rcases he2 with h | h <;> have hf := congrArg Prod.fst h <;>
                      have hs := congrArg Prod.snd h <;> omega
              have hk2_eq : k2 = 3 * j + 1 := by omega
              have hj_nd : j ∉ del := by
                intro hjd
                apply hk2_nd
                rw [hk2_eq, subdivDel, List.mem_map]
                exact ⟨j, hjd, rfl⟩
              rw [hj2.2.2] at hlast hch hnd ⊢
              cases rest1' with
              | nil =>
                simp at hlast
                omega
              | cons w rest2 =>
                rw [List.isChain_cons_cons] at hch
                have hne_wy : w ≠ G.n + 2 * j := by
                  have hnd1 := (List.nodup_cons.mp hnd).2
                  have hnd2 := List.nodup_cons.mp hnd1
                  intro hwy; apply hnd2.1; simp [hwy]
                have hw_edge : ∃ k3 < 3 * G.m, k3 ∉ subdivDel del ∧
                    ((subdivGraph G).edges.getD k3 (0, 0) = (G.n + 2 * j + 1, w) ∨
                      (subdivGraph G).edges.getD k3 (0, 0) = (w, G.n + 2 * j + 1)) := by
                  rcases hch.2.2.1 with hm | hm
                  · rw [hce_eq, mem_currentEdges_subdiv_iff] at hm
                    rcases hm with ⟨k, hk, hndk, hek⟩
                    exact ⟨k, hk, hndk, Or.inl hek⟩
                  · rw [hce_eq, mem_currentEdges_subdiv_iff] at hm
                    rcases hm with ⟨k, hk, hndk, hek⟩
                    exact ⟨k, hk, hndk, Or.inr hek⟩
                rcases hw_edge with ⟨k3, hk3, _, he3⟩
                rw [subdivGraph_edges_getD G hk3] at he3
                have hv3 := getD_valid_of_lt hV (by omega : k3 / 3 < G.m)
                have hw_eq : w = (G.edges.getD j (0, 0)).2 := by
                  by_cases h0 : k3 % 3 = 0
                  · simp only [h0, ↓reduceIte] at he3
                    rcases he3 with h | h <;> have hf := congrArg Prod.fst h <;>
                      have hs := congrArg Prod.snd h <;> omega
                  · by_cases h1 : k3 % 3 = 1
                    · simp only [h1, Nat.one_ne_zero, ↓reduceIte] at he3
                      rcases he3 with h | h <;> have hf := congrArg Prod.fst h <;>
                        have hs := congrArg Prod.snd h <;> omega
                    · simp only [h0, h1, ↓reduceIte] at he3
                      rcases he3 with h | h
                      · have hf := congrArg Prod.fst h
                        have hs := congrArg Prod.snd h
                        have hdiv : k3 / 3 = j := by omega
                        rw [hdiv] at hs
                        omega
                      · have hf := congrArg Prod.fst h
                        have hs := congrArg Prod.snd h
                        omega
                have hw_lt : w < G.n := hw_eq ▸ hvj.2
                have heG_eq : G.edges.getD j (0, 0) = (u, w) := Prod.ext hu_ej.symm hw_eq.symm
                have heG : (u, w) ∈ (graphAfterDel G del).edges := by
                  simp only [graphAfterDel, List.mem_map, List.mem_filter, List.mem_range,
                    decide_eq_true_eq]
                  exact ⟨j, ⟨hj, hj_nd⟩, heG_eq⟩
                exact ⟨w, hw_lt, rest2, G.n + 2 * j + 1, rfl, by omega, by omega,
                  by omega, hj, hj_nd, Or.inl heG_eq, Or.inl heG⟩
          · by_cases hm1 : k1 % 3 = 1
            · simp only [hm1, Nat.one_ne_zero, ↓reduceIte] at he1
              rcases he1 with h | h <;> have hf := congrArg Prod.fst h <;>
                have hs := congrArg Prod.snd h <;> omega
            · simp only [hm0, hm1, ↓reduceIte] at he1
              have hy_eq : u = (G.edges.getD j (0, 0)).2 ∧ y = G.n + 2 * j + 1 := by
                rcases he1 with h | h <;> have hf := congrArg Prod.fst h <;>
                  have hs := congrArg Prod.snd h <;> omega
              rcases hy_eq with ⟨hu_ej, rfl⟩
              cases rest1 with
              | nil =>
                simp at hlast
                omega
              | cons z rest1' =>
                rw [List.isChain_cons_cons] at hch
                have hne_zu : z ≠ u := by
                  have hnd' := List.nodup_cons.mp hnd
                  intro hzu; apply hnd'.1; simp [hzu]
                have hz_edge : ∃ k2 < 3 * G.m, k2 ∉ subdivDel del ∧
                    ((subdivGraph G).edges.getD k2 (0, 0) = (G.n + 2 * j + 1, z) ∨
                      (subdivGraph G).edges.getD k2 (0, 0) = (z, G.n + 2 * j + 1)) := by
                  rcases hch.2.1 with hm | hm
                  · rw [hce_eq, mem_currentEdges_subdiv_iff] at hm
                    rcases hm with ⟨k, hk, hndk, hek⟩
                    exact ⟨k, hk, hndk, Or.inl hek⟩
                  · rw [hce_eq, mem_currentEdges_subdiv_iff] at hm
                    rcases hm with ⟨k, hk, hndk, hek⟩
                    exact ⟨k, hk, hndk, Or.inr hek⟩
                rcases hz_edge with ⟨k2, hk2, hk2_nd, he2⟩
                rw [subdivGraph_edges_getD G hk2] at he2
                have hv2 := getD_valid_of_lt hV (by omega : k2 / 3 < G.m)
                have hj2 : k2 / 3 = j ∧ k2 % 3 = 1 ∧ z = G.n + 2 * j := by
                  by_cases h0 : k2 % 3 = 0
                  · simp only [h0, ↓reduceIte] at he2
                    rcases he2 with h | h <;> have hf := congrArg Prod.fst h <;>
                      have hs := congrArg Prod.snd h <;> omega
                  · by_cases h1 : k2 % 3 = 1
                    · simp only [h1, Nat.one_ne_zero, ↓reduceIte] at he2
                      rcases he2 with h | h <;> have hf := congrArg Prod.fst h <;>
                        have hs := congrArg Prod.snd h <;> omega
                    · simp only [h0, h1, ↓reduceIte] at he2
                      rcases he2 with h | h
                      · have hf := congrArg Prod.fst h
                        have hs := congrArg Prod.snd h
                        have hdiv : k2 / 3 = j := by omega
                        rw [hdiv] at hs
                        omega
                      · have hf := congrArg Prod.fst h
                        have hs := congrArg Prod.snd h
                        omega
                have hk2_eq : k2 = 3 * j + 1 := by omega
                have hj_nd : j ∉ del := by
                  intro hjd
                  apply hk2_nd
                  rw [hk2_eq, subdivDel, List.mem_map]
                  exact ⟨j, hjd, rfl⟩
                rw [hj2.2.2] at hlast hch hnd ⊢
                cases rest1' with
                | nil =>
                  simp at hlast
                  omega
                | cons w rest2 =>
                  rw [List.isChain_cons_cons] at hch
                  have hne_wy : w ≠ G.n + 2 * j + 1 := by
                    have hnd1 := (List.nodup_cons.mp hnd).2
                    have hnd2 := List.nodup_cons.mp hnd1
                    intro hwy; apply hnd2.1; simp [hwy]
                  have hw_edge : ∃ k3 < 3 * G.m, k3 ∉ subdivDel del ∧
                      ((subdivGraph G).edges.getD k3 (0, 0) = (G.n + 2 * j, w) ∨
                        (subdivGraph G).edges.getD k3 (0, 0) = (w, G.n + 2 * j)) := by
                    rcases hch.2.2.1 with hm | hm
                    · rw [hce_eq, mem_currentEdges_subdiv_iff] at hm
                      rcases hm with ⟨k, hk, hndk, hek⟩
                      exact ⟨k, hk, hndk, Or.inl hek⟩
                    · rw [hce_eq, mem_currentEdges_subdiv_iff] at hm
                      rcases hm with ⟨k, hk, hndk, hek⟩
                      exact ⟨k, hk, hndk, Or.inr hek⟩
                  rcases hw_edge with ⟨k3, hk3, _, he3⟩
                  rw [subdivGraph_edges_getD G hk3] at he3
                  have hv3 := getD_valid_of_lt hV (by omega : k3 / 3 < G.m)
                  have hw_eq : w = (G.edges.getD j (0, 0)).1 := by
                    by_cases h0 : k3 % 3 = 0
                    · simp only [h0, ↓reduceIte] at he3
                      rcases he3 with h | h
                      · have hf := congrArg Prod.fst h; omega
                      · have hf := congrArg Prod.fst h
                        have hs := congrArg Prod.snd h
                        have hdiv : k3 / 3 = j := by omega
                        rw [hdiv] at hf
                        omega
                    · by_cases h1 : k3 % 3 = 1
                      · simp only [h1, Nat.one_ne_zero, ↓reduceIte] at he3
                        rcases he3 with h | h <;> have hf := congrArg Prod.fst h <;>
                          have hs := congrArg Prod.snd h <;> omega
                      · simp only [h0, h1, ↓reduceIte] at he3
                        rcases he3 with h | h <;> have hf := congrArg Prod.fst h <;>
                          have hs := congrArg Prod.snd h <;> omega
                  have hw_lt : w < G.n := hw_eq ▸ hvj.1
                  have heG_eq : G.edges.getD j (0, 0) = (w, u) := Prod.ext hw_eq.symm hu_ej.symm
                  have heG : (w, u) ∈ (graphAfterDel G del).edges := by
                    simp only [graphAfterDel, List.mem_map, List.mem_filter, List.mem_range,
                      decide_eq_true_eq]
                    exact ⟨j, ⟨hj, hj_nd⟩, heG_eq⟩
                  exact ⟨w, hw_lt, rest2, G.n + 2 * j, rfl, by omega, by omega,
                    by omega, hj, hj_nd, Or.inr heG_eq, Or.inr heG⟩
        rcases hstep_edge with ⟨w, hw, rest2, z, rfl, hy_n, hz_n, hj_div, hj_lt, hj_nd, hmatch, huw⟩
        have hP_sub : Cited.IsPathAlong
            (Cited.PrunedExpander.currentEdges ⟨subdivGraph G, 2, subdivDel del, S_s⟩)
            w v (w :: rest2) := by
          rw [List.isChain_cons_cons, List.isChain_cons_cons] at hch
          refine ⟨rfl, ?_, hch.2.2.2⟩
          simpa using hlast
        have hnd_sub : (w :: rest2).Nodup := by
          have h1 := (List.nodup_cons.mp hnd).2
          have h2 := (List.nodup_cons.mp h1).2
          exact (List.nodup_cons.mp h2).2
        have hrec := ih (w :: rest2).length (by simp only [← hlen, List.length_cons]; omega)
          (w :: rest2) w rfl hw hnd_sub hP_sub
        have hproj_eq : projPath G.n (u :: y :: z :: w :: rest2) = u :: projPath G.n (w :: rest2) := by
          simp only [projPath, List.filter_cons, decide_eq_true hu, ↓reduceIte,
            show decide (y < G.n) = false from decide_eq_false hy_n,
            show decide (z < G.n) = false from decide_eq_false hz_n,
            Bool.false_eq_true]
        have hproj_edges : projEdges G.n (u :: y :: z :: w :: rest2) =
            j :: projEdges G.n (w :: rest2) := by
          simp [projEdges, hj_div]
        rw [hproj_eq, hproj_edges]
        rcases hrec with ⟨hrec_path, hrec_3len, hrec_elen, hrec_mem, hrec_match⟩
        refine ⟨isPathAlong_cons huw hrec_path, ?_, ?_, ?_, ?_⟩
        · have hlen_pos : 1 ≤ (projPath G.n (w :: rest2)).length := by
            simp only [projPath, List.filter_cons, decide_eq_true hw, ↓reduceIte, List.length_cons]
            omega
          have hlen_rec := hrec_3len
          have hlen_w : (w :: rest2).length - 1 = rest2.length := by simp
          have hlen_lhs : (u :: projPath G.n (w :: rest2)).length - 1 =
              ((projPath G.n (w :: rest2)).length - 1) + 1 := by
            simp only [List.length_cons]; omega
          have hlen_rhs : (u :: y :: z :: w :: rest2).length - 1 = rest2.length + 3 := by
            simp only [List.length_cons]; omega
          rw [hlen_lhs, hlen_rhs, Nat.mul_add, hlen_rec, hlen_w]
        · simp only [List.length_cons]
          omega
        · intro j' hj'
          rcases List.mem_cons.mp hj' with rfl | hj'rest
          · exact ⟨hj_lt, hj_nd⟩
          · exact hrec_mem j' hj'rest
        · intro idx hidx
          cases idx with
          | zero =>
            have hpw : projPath G.n (w :: rest2) = w :: projPath G.n rest2 := by
              simp [projPath, hw]
            simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
              Nat.zero_add, List.getElem?_cons_succ, hpw]
            rcases hmatch with hm | hm
            · exact Or.inl ⟨congrArg Prod.fst hm, congrArg Prod.snd hm⟩
            · exact Or.inr ⟨congrArg Prod.snd hm, congrArg Prod.fst hm⟩
          | succ idx' =>
            have hidx' : idx' < (projEdges G.n (w :: rest2)).length := by
              simp only [List.length_cons] at hidx
              omega
            simpa [List.getD_eq_getElem?_getD] using hrec_match idx' hidx'

lemma projPath_spec {G : Cited.Graph} (hV : G.IsValid) {q : ℕ} (del : List ℕ) (S_s : Finset ℕ)
    {u v : ℕ} (hu : u < G.n) (hv : v < G.n) {P_s : List ℕ}
    (hnd : P_s.Nodup) (hnotS : ∀ w ∈ P_s, w ∉ S_s)
    (hP : Cited.IsPathAlong
      (Cited.PrunedExpander.currentEdges ⟨subdivGraph G, q, subdivDel del, S_s⟩) u v P_s) :
    let P := projPath G.n P_s
    P.Nodup ∧ (∀ x ∈ P, x ∉ projSet G.n S_s) ∧
    Cited.IsPathAlong (graphAfterDel G del).edges u v P ∧
    3 * (P.length - 1) = P_s.length - 1 ∧ P.length ≤ P_s.length := by
  have hce : (Cited.PrunedExpander.currentEdges ⟨subdivGraph G, q, subdivDel del, S_s⟩) =
      (Cited.PrunedExpander.currentEdges ⟨subdivGraph G, 2, subdivDel del, S_s⟩) := rfl
  rw [hce] at hP
  have haux := projPath_aux hV del S_s hv P_s.length P_s u rfl hu hnd hP
  refine ⟨hnd.filter _, ?_, haux.1, haux.2.1, List.length_filter_le _ _⟩
  intro x hx
  rw [projPath, List.mem_filter] at hx
  intro hxS
  rw [projSet, Finset.mem_filter] at hxS
  exact hnotS x hx.1 hxS.1

/-- Edge-index specification accompanying `projPath_spec`: `projEdges G.n P_s` gives the exact
list of surviving (`< G.m`, `∉ del`) edge indices connecting consecutive vertices of
`projPath G.n P_s`. -/
lemma projEdges_spec {G : Cited.Graph} (hV : G.IsValid) {q : ℕ} (del : List ℕ) (S_s : Finset ℕ)
    {u v : ℕ} (hu : u < G.n) (hv : v < G.n) {P_s : List ℕ}
    (hnd : P_s.Nodup)
    (hP : Cited.IsPathAlong
      (Cited.PrunedExpander.currentEdges ⟨subdivGraph G, q, subdivDel del, S_s⟩) u v P_s) :
    let vs := projPath G.n P_s
    let es := projEdges G.n P_s
    vs.length = es.length + 1 ∧
    (∀ j ∈ es, j < G.m ∧ j ∉ del) ∧
    (∀ i : ℕ, i < es.length →
      let j := es.getD i 0
      let a := vs.getD i 0
      let b := vs.getD (i + 1) 0
      let e := G.edges.getD j (0, 0)
      (e.1 = a ∧ e.2 = b) ∨ (e.2 = a ∧ e.1 = b)) := by
  have hce : (Cited.PrunedExpander.currentEdges ⟨subdivGraph G, q, subdivDel del, S_s⟩) =
      (Cited.PrunedExpander.currentEdges ⟨subdivGraph G, 2, subdivDel del, S_s⟩) := rfl
  rw [hce] at hP
  have haux := projPath_aux hV del S_s hv P_s.length P_s u rfl hu hnd hP
  exact ⟨haux.2.2.1, haux.2.2.2.1, haux.2.2.2.2⟩

private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
  exact (Real.log_le_iff_le_exp (by norm_num)).mpr this

/-- For any positive integer `Kγ` and constants `C₀, C₁ > 0`, `csGamma Kγ (3 * m)` dominates
`10 * C₁ * exp(C₀ * log^{2/3}(m + 2) * log(log(m + 2) + 2))` up to a constant factor `c ≥ 1`, so
`csPhi Kγ c (3 * m) ≤ φ(m) / 10` for all `m : ℕ`. -/
theorem csGamma_dominates_sb {Kγ : ℕ} (hKγ : 1 ≤ Kγ) (C₀ C₁ : ℝ)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ c : ℕ, 1 ≤ c ∧
      ∀ m : ℕ,
        1 / ((c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ)) ≤
          (1 / (C₁ * Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
            Real.log (Real.log ((m : ℝ) + 2) + 2)))) / 10 := by
  have hl2_pos : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  set M := (96 * C₀ / ((Kγ : ℝ) * Real.log 2) + 10)
  have hM_ge : 10 ≤ M := by
    have : 0 ≤ 96 * C₀ / ((Kγ : ℝ) * Real.log 2) := by positivity
    linarith
  set A := M ^ (24 : ℕ)
  have hA_ge : 10 ^ 24 ≤ A := pow_le_pow_left₀ (by norm_num) hM_ge 24
  have hA_pos : 0 < A := by positivity
  set B_small := Real.exp (C₀ * A ^ (2 / 3 : ℝ) * Real.log A)
  have hB_pos : 0 < B_small := Real.exp_pos _
  let c := max 1 (Nat.ceil (10 * C₁ * B_small))
  refine ⟨c, le_max_left _ _, ?_⟩
  intro m
  have hcs_pos : (0 : ℝ) < (Cited.csGamma Kγ (3 * m) : ℝ) := by
    unfold Cited.csGamma; positivity
  set L := Real.log ((m : ℝ) + 2)
  have hL_pos : 0 < L := Real.log_pos (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  have hll_pos : 0 < Real.log (L + 2) := Real.log_pos (by linarith)
  set sb_val := Real.exp (C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2))
  have hsb_pos : 0 < sb_val := Real.exp_pos _
  suffices hdom : 10 * C₁ * sb_val ≤ (c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ) by
    have hc_pos : (0 : ℝ) < c := by positivity
    have hden_pos : 0 < (c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ) := mul_pos hc_pos hcs_pos
    rw [div_div, one_div_le_one_div hden_pos (by positivity)]
    linarith
  by_cases hsmall : L + 2 ≤ A ∨ m = 0
  · have hL_leA : L ≤ A := by
      rcases hsmall with h | rfl
      · linarith
      · have : Real.log ((0 : ℕ) + 2 : ℝ) ≤ 1 := by simpa using log_two_le_one
        linarith [show (10 : ℝ) ≤ 10 ^ 24 by norm_num]
    have hL2_leA : L + 2 ≤ A := by
      rcases hsmall with h | rfl
      · exact h
      · have : Real.log ((0 : ℕ) + 2 : ℝ) ≤ 1 := by simpa using log_two_le_one
        linarith [show (10 : ℝ) ≤ 10 ^ 24 by norm_num]
    have hsb_le : sb_val ≤ B_small := by
      rw [Real.exp_le_exp]
      have hrp : L ^ (2 / 3 : ℝ) ≤ A ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow hL_pos.le hL_leA (by norm_num)
      have hll : Real.log (L + 2) ≤ Real.log A := Real.log_le_log (by linarith) hL2_leA
      exact mul_le_mul (mul_le_mul_of_nonneg_left hrp hC₀.le) hll hll_pos.le (by positivity)
    have hcs_ge1 : (1 : ℝ) ≤ (Cited.csGamma Kγ (3 * m) : ℝ) := by
      unfold Cited.csGamma
      exact_mod_cast Nat.one_le_pow _ 2 (by norm_num)
    have hc_ge : 10 * C₁ * B_small ≤ (c : ℝ) := by
      have h1 : 10 * C₁ * B_small ≤ (Nat.ceil (10 * C₁ * B_small) : ℝ) :=
        Nat.le_ceil _
      have h2 : (Nat.ceil (10 * C₁ * B_small) : ℝ) ≤ (c : ℝ) := by
        exact_mod_cast le_max_right 1 (Nat.ceil (10 * C₁ * B_small))
      exact le_trans h1 h2
    calc 10 * C₁ * sb_val ≤ 10 * C₁ * B_small := by
          exact mul_le_mul_of_nonneg_left hsb_le (by positivity)
      _ ≤ (c : ℝ) * 1 := by linarith
      _ ≤ (c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ) :=
          mul_le_mul_of_nonneg_left hcs_ge1 (Nat.cast_nonneg _)
  · push Not at hsmall
    have hLA : A < L + 2 := hsmall.1
    have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hsmall.2
    have hc_ge : 10 * C₁ * 1 ≤ (c : ℝ) := by
      have hB1 : 1 ≤ B_small := by
        rw [Real.one_le_exp_iff]
        have hA1 : 1 ≤ A := by linarith [show (10 : ℝ) ≤ 10 ^ 24 by norm_num]
        have : 0 ≤ A ^ (2 / 3 : ℝ) := Real.rpow_nonneg hA_pos.le _
        have : 0 ≤ Real.log A := Real.log_nonneg hA1
        positivity
      have h1 : 10 * C₁ * B_small ≤ (Nat.ceil (10 * C₁ * B_small) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (10 * C₁ * B_small) : ℝ) ≤ (c : ℝ) := by
        exact_mod_cast le_max_right 1 _
      nlinarith
    suffices hsb_cs : sb_val ≤ (Cited.csGamma Kγ (3 * m) : ℝ) by
      calc 10 * C₁ * sb_val ≤ 10 * C₁ * (Cited.csGamma Kγ (3 * m) : ℝ) :=
            mul_le_mul_of_nonneg_left hsb_cs (by positivity)
        _ ≤ (c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) hcs_pos.le
    set N := Nat.log 2 (3 * m) + 1
    set s := Nat.sqrt (Nat.sqrt (N ^ 3))
    have hm2_lt : m + 2 ≤ 3 * m := by omega
    have h3m_lt : 3 * m < 2 ^ N := Nat.lt_pow_succ_log_self (by norm_num) (3 * m)
    have hL_leN : L ≤ (N : ℝ) := by
      have hpow : (m : ℝ) + 2 ≤ (2 : ℝ) ^ N := by exact_mod_cast (by omega : m + 2 ≤ 2 ^ N)
      have hlog : L ≤ (N : ℝ) * Real.log 2 := by
        calc L ≤ Real.log ((2 : ℝ) ^ N) := Real.log_le_log (by positivity) hpow
          _ = (N : ℝ) * Real.log 2 := Real.log_pow 2 N
      have : (N : ℝ) * Real.log 2 ≤ (N : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left log_two_le_one (Nat.cast_nonneg _)
      linarith
    have hs4 : N ^ 3 < (s + 1) ^ 4 := by
      have h1 : N ^ 3 < (Nat.sqrt (N ^ 3) + 1) ^ 2 := by
        have := Nat.lt_succ_sqrt (N ^ 3); rw [sq]; exact this
      have h2 : Nat.sqrt (N ^ 3) < (s + 1) ^ 2 := by
        have := Nat.lt_succ_sqrt (Nat.sqrt (N ^ 3)); rw [sq]; exact this
      have h3 : Nat.sqrt (N ^ 3) + 1 ≤ (s + 1) ^ 2 := by omega
      have h4 : (Nat.sqrt (N ^ 3) + 1) ^ 2 ≤ ((s + 1) ^ 2) ^ 2 :=
        Nat.pow_le_pow_left h3 2
      have h5 : ((s + 1) ^ 2) ^ 2 = (s + 1) ^ 4 := by ring
      omega
    have hL34_le : L ^ (3 / 4 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
      have hpow4 : (L ^ (3 / 4 : ℝ)) ^ (4 : ℕ) ≤ (((s + 1 : ℕ) : ℝ)) ^ (4 : ℕ) := by
        have h1 : (L ^ (3 / 4 : ℝ)) ^ (4 : ℕ) = L ^ (3 : ℕ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]
          norm_num
        have h2 : L ^ (3 : ℕ) ≤ (N : ℝ) ^ (3 : ℕ) :=
          pow_le_pow_left₀ hL_pos.le hL_leN 3
        have h3 : (N : ℝ) ^ (3 : ℕ) ≤ (((s + 1 : ℕ) : ℝ)) ^ (4 : ℕ) := by
          exact_mod_cast hs4.le
        linarith
      exact le_of_pow_le_pow_left₀ (by norm_num) (Nat.cast_nonneg _) hpow4
    have hL_ge10 : 10 ≤ L := by
      have h10_24 : (10 ^ 24 : ℝ) < L + 2 := lt_of_le_of_lt hA_ge hLA
      have : (100 : ℝ) ≤ 10 ^ 24 := by norm_num
      linarith
    have hL2_le_2L : L + 2 ≤ 2 * L := by linarith
    have h2_34 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := by norm_num
    have hL34_lower : (L + 2) ^ (3 / 4 : ℝ) / 2 ≤ L ^ (3 / 4 : ℝ) := by
      have h1 : (L + 2) ^ (3 / 4 : ℝ) ≤ (2 * L) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hL2_le_2L (by norm_num)
      have h2 : (2 * L) ^ (3 / 4 : ℝ) = (2 : ℝ) ^ (3 / 4 : ℝ) * L ^ (3 / 4 : ℝ) :=
        Real.mul_rpow (by norm_num) hL_pos.le
      nlinarith [Real.rpow_nonneg hL_pos.le (3 / 4 : ℝ)]
    have hlog_root : Real.log (L + 2) ≤ 24 * (L + 2) ^ (1 / 24 : ℝ) := by
      have hrpos : 0 < (L + 2) ^ (1 / 24 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
      have h1 : Real.log (L + 2) = 24 * Real.log ((L + 2) ^ (1 / 24 : ℝ)) := by
        rw [Real.log_rpow (by linarith)]
        ring
      have h2 : Real.log ((L + 2) ^ (1 / 24 : ℝ)) ≤ (L + 2) ^ (1 / 24 : ℝ) := by
        linarith [Real.log_le_sub_one_of_pos hrpos]
      linarith
    have hM_le_root : M ≤ (L + 2) ^ (1 / 24 : ℝ) := by
      have hA_rpow : M = A ^ (1 / 24 : ℝ) := by
        dsimp only [A]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        norm_num
      rw [hA_rpow]
      exact Real.rpow_le_rpow hA_pos.le hLA.le (by norm_num)
    have hrp_sum : (L + 2) ^ (17 / 24 : ℝ) * (L + 2) ^ (1 / 24 : ℝ) = (L + 2) ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add (by linarith)]
      norm_num
    have hexp_lhs : C₀ * L ^ (2 / 3 : ℝ) * Real.log (L + 2) ≤
        24 * C₀ * (L + 2) ^ (17 / 24 : ℝ) := by
      have h1 : L ^ (2 / 3 : ℝ) ≤ (L + 2) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow hL_pos.le (by linarith) (by norm_num)
      have h2 : L ^ (2 / 3 : ℝ) * Real.log (L + 2) ≤
          (L + 2) ^ (2 / 3 : ℝ) * (24 * (L + 2) ^ (1 / 24 : ℝ)) :=
        mul_le_mul h1 hlog_root hll_pos.le (by positivity)
      have h3 : (L + 2) ^ (2 / 3 : ℝ) * (L + 2) ^ (1 / 24 : ℝ) = (L + 2) ^ (17 / 24 : ℝ) := by
        rw [← Real.rpow_add (by linarith)]
        norm_num
      nlinarith
    have hKγR : (0 : ℝ) < (Kγ : ℝ) * Real.log 2 := mul_pos (by exact_mod_cast hKγ) hl2_pos
    have h48 : 48 * C₀ / ((Kγ : ℝ) * Real.log 2) ≤ (L + 2) ^ (1 / 24 : ℝ) := by
      have : 48 * C₀ / ((Kγ : ℝ) * Real.log 2) ≤ M := by
        dsimp only [M]
        rw [mul_div_assoc, mul_div_assoc]
        have hnn : 0 ≤ C₀ / ((Kγ : ℝ) * Real.log 2) := by positivity
        linarith
      exact le_trans this hM_le_root
    have h24_le_rhs : 24 * C₀ * (L + 2) ^ (17 / 24 : ℝ) ≤
        ((Kγ : ℝ) * Real.log 2) * L ^ (3 / 4 : ℝ) := by
      have h1 : (48 * C₀ / ((Kγ : ℝ) * Real.log 2)) * ((Kγ : ℝ) * Real.log 2) = 48 * C₀ := by
        field_simp
      have h2 : 48 * C₀ * (L + 2) ^ (17 / 24 : ℝ) ≤
          ((Kγ : ℝ) * Real.log 2) * ((L + 2) ^ (17 / 24 : ℝ) * (L + 2) ^ (1 / 24 : ℝ)) := by
        have hnn17 : 0 ≤ (L + 2) ^ (17 / 24 : ℝ) := Real.rpow_nonneg (by linarith) _
        have hmul := mul_le_mul_of_nonneg_right h48 hKγR.le
        rw [h1] at hmul
        calc 48 * C₀ * (L + 2) ^ (17 / 24 : ℝ)
            ≤ ((L + 2) ^ (1 / 24 : ℝ) * ((Kγ : ℝ) * Real.log 2)) * (L + 2) ^ (17 / 24 : ℝ) :=
              mul_le_mul_of_nonneg_right hmul hnn17
          _ = ((Kγ : ℝ) * Real.log 2) * ((L + 2) ^ (17 / 24 : ℝ) * (L + 2) ^ (1 / 24 : ℝ)) := by
              ring
      rw [hrp_sum] at h2
      have h3 : ((Kγ : ℝ) * Real.log 2) * ((L + 2) ^ (3 / 4 : ℝ)) ≤
          2 * (((Kγ : ℝ) * Real.log 2) * L ^ (3 / 4 : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hL34_lower hKγR.le
        linarith
      have hnn17 : 0 ≤ (L + 2) ^ (17 / 24 : ℝ) := Real.rpow_nonneg (by linarith) _
      have h24_nonneg : 0 ≤ C₀ * (L + 2) ^ (17 / 24 : ℝ) := mul_nonneg hC₀.le hnn17
      linarith
    have hcs_eq : (Cited.csGamma Kγ (3 * m) : ℝ) =
        Real.exp ((Kγ : ℝ) * ((s + 1 : ℕ) : ℝ) * Real.log 2) := by
      unfold Cited.csGamma
      change ((2 ^ (Kγ * (s + 1)) : ℕ) : ℝ) = Real.exp ((Kγ : ℝ) * ((s + 1 : ℕ) : ℝ) * Real.log 2)
      push_cast
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
      congr 1
      push_cast
      ring
    rw [hcs_eq, Real.exp_le_exp]
    have h3 : ((Kγ : ℝ) * Real.log 2) * L ^ (3 / 4 : ℝ) ≤
        (Kγ : ℝ) * ((s + 1 : ℕ) : ℝ) * Real.log 2 := by
      have := mul_le_mul_of_nonneg_left hL34_le hKγR.le
      linarith
    linarith

lemma csGamma_le_exp_three_quarters (Kγ : ℕ) :
    ∃ C_γ : ℝ, 0 < C_γ ∧ ∀ m : ℕ,
      (Cited.csGamma Kγ (3 * m) : ℝ) ≤
        Real.exp (C_γ * Real.log ((m : ℝ) + 2) ^ (3 / 4 : ℝ)) := by
  refine ⟨12 * ((Kγ : ℝ) + 1), by positivity, ?_⟩
  intro m
  set L := Real.log ((m : ℝ) + 2)
  have hL_ge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg _; linarith)
  have hl2 : (0.5 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL_pos : 0 < L := by linarith
  set k := Nat.log 2 (3 * m)
  have hk_le : (k : ℝ) ≤ 8 * L := by
    by_cases hm0 : m = 0
    · simp [k, hm0]; positivity
    · have hpow : 2 ^ k ≤ 3 * m := Nat.pow_log_le_self 2 (by omega)
      have hpowR : (2 : ℝ) ^ k ≤ 4 * ((m : ℝ) + 2) := by
        exact_mod_cast (show 2 ^ k ≤ 4 * (m + 2) by omega)
      have hlog : (k : ℝ) * Real.log 2 ≤ Real.log ((2 : ℝ) ^ 2) + L := by
        calc (k : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ k) := (Real.log_pow 2 k).symm
          _ ≤ Real.log (4 * ((m : ℝ) + 2)) := Real.log_le_log (by positivity) hpowR
          _ = Real.log ((2 : ℝ) ^ 2) + L := by
              rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
              exact Real.log_mul (by norm_num) (by positivity)
      have hlog4 : Real.log ((2 : ℝ) ^ 2) = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
      have h2le : (2 : ℝ) ≤ 4 * L := by linarith
      have hmul : (k : ℝ) * 0.5 ≤ (k : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg _)
      have hl2_le1 := log_two_le_one
      nlinarith
  have hN_le : ((k + 1 : ℕ) : ℝ) ≤ 10 * L := by
    push_cast
    linarith
  set s := Nat.sqrt (Nat.sqrt ((k + 1) ^ 3))
  have hs_le : (s : ℝ) ≤ (10 * L) ^ (3 / 4 : ℝ) := by
    have hs4 : s ^ 4 ≤ (k + 1) ^ 3 := by
      have h1 := Nat.sqrt_le ((k + 1) ^ 3)
      have h2 := Nat.sqrt_le (Nat.sqrt ((k + 1) ^ 3))
      calc s ^ 4 = (s * s) * (s * s) := by ring
        _ ≤ Nat.sqrt ((k + 1) ^ 3) * Nat.sqrt ((k + 1) ^ 3) :=
            Nat.mul_le_mul h2 h2
        _ ≤ (k + 1) ^ 3 := h1
    have hs4R : (s : ℝ) ^ 4 ≤ ((10 * L) ^ (3 / 4 : ℝ)) ^ 4 := by
      have h1 : (s : ℝ) ^ (4 : ℕ) ≤ ((k + 1 : ℕ) : ℝ) ^ (3 : ℕ) := by exact_mod_cast hs4
      have h2 : ((k + 1 : ℕ) : ℝ) ^ (3 : ℕ) ≤ (10 * L) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hN_le 3
      have h3 : ((10 * L) ^ (3 / 4 : ℝ)) ^ (4 : ℕ) = (10 * L) ^ (3 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        norm_num
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg (by linarith) _) hs4R
  have h10_34 : (10 : ℝ) ^ (3 / 4 : ℝ) ≤ 10 := by
    calc (10 : ℝ) ^ (3 / 4 : ℝ) ≤ (10 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 10 := by norm_num
  have hs_le' : (s : ℝ) ≤ 10 * L ^ (3 / 4 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hL_pos.le] at hs_le
    exact le_trans hs_le (mul_le_mul_of_nonneg_right h10_34 (Real.rpow_nonneg hL_pos.le _))
  have h1_le_L34 : 1 ≤ 2 * L ^ (3 / 4 : ℝ) := by
    have hhalfL : (0.5 : ℝ) ≤ L := by linarith
    have hhalf4 : (1 / 2 : ℝ) ^ 4 ≤ L ^ 3 := by
      have : (1 / 2 : ℝ) ^ 4 = (1 / 16 : ℝ) := by norm_num
      have : (0.5 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hhalfL 3
      linarith
    have hpow4 : (1 / 2 : ℝ) ^ (4 : ℕ) ≤ (L ^ (3 / 4 : ℝ)) ^ (4 : ℕ) := by
      have : (L ^ (3 / 4 : ℝ)) ^ (4 : ℕ) = L ^ (3 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]
        norm_num
      linarith
    have := le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hL_pos.le _) hpow4
    linarith
  have hs1_le : ((s + 1 : ℕ) : ℝ) ≤ 12 * L ^ (3 / 4 : ℝ) := by
    push_cast
    linarith
  have hcs_eq : (Cited.csGamma Kγ (3 * m) : ℝ) =
      Real.exp ((Kγ : ℝ) * ((s + 1 : ℕ) : ℝ) * Real.log 2) := by
    unfold Cited.csGamma
    change ((2 ^ (Kγ * (s + 1)) : ℕ) : ℝ) = Real.exp ((Kγ : ℝ) * ((s + 1 : ℕ) : ℝ) * Real.log 2)
    push_cast
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    push_cast
    ring
  rw [hcs_eq, Real.exp_le_exp]
  have hKγ_le : (Kγ : ℝ) * Real.log 2 ≤ (Kγ : ℝ) + 1 := by
    have := mul_le_mul_of_nonneg_left log_two_le_one (Nat.cast_nonneg Kγ)
    linarith
  have hnn : 0 ≤ 12 * L ^ (3 / 4 : ℝ) := by positivity
  calc (Kγ : ℝ) * ((s + 1 : ℕ) : ℝ) * Real.log 2
      = ((Kγ : ℝ) * Real.log 2) * ((s + 1 : ℕ) : ℝ) := by ring
    _ ≤ ((Kγ : ℝ) + 1) * (12 * L ^ (3 / 4 : ℝ)) :=
        mul_le_mul hKγ_le hs1_le (Nat.cast_nonneg _) (by positivity)
    _ = 12 * ((Kγ : ℝ) + 1) * L ^ (3 / 4 : ℝ) := by ring

/-- **Theorem 8.6 mathematical bundle** (arXiv:2309.16629v1, page 41): from
`Cited.DecrementalExpanderPaths` and any subexponential conductance lower bound
`φ(m) ≥ 1 / (C₁ · exp(C₀ · log^{2/3}(m+2) · log log(m+2)))`, there exist `[CS21]` parameters
`(Kγ, c₀, c, K, cw, mk, R)` and `C_γ > 0` such that:
1. `c ≥ c₀` implements `prunedExpanderDS Kγ c K cw w` at every word size `w`,
2. `Cited.csPhi Kγ c (3 * m) ≤ φ(m) / 10` and `Cited.csGamma Kγ (3 * m) ≤ exp(C_γ · log^{3/4}(m+2))`,
3. for any valid multigraph `G` (possibly with parallel edges and self-loops) having `1 ≤ G.m`,
   no isolated vertices, and `G.IsConductanceExpanderOn G.verts φ_G` (`φ(G.m) ≤ φ_G ≤ 1`),
   `G_s := subdivGraph G` satisfies all structural preconditions of `prunedExpanderDS.initPre`,
   and deletions / `S_s` / `GetPath` translate cleanly back to `G` via `subdivDel`, `projSet`, and
   `projPath`. -/
theorem theorem_8_6 (hCS : Cited.DecrementalExpanderPaths) {C₀ C₁ : ℝ}
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ (Kγ c₀ c : ℕ) (K C_γ : ℝ) (cw : ℕ) (mk : ℕ → List WordRAM.Stmt)
      (R : WordRAM.DSRep Cited.PrunedExpander),
      0 < Kγ ∧ 0 < c₀ ∧ c₀ ≤ c ∧ 1 ≤ c ∧ 0 < C_γ ∧
      (∀ (w b : ℕ) (p : WordRAM.Program), p.HasAt b (mk b) →
        R.Implements w p b (fun i => b + 1 + i) (Cited.prunedExpanderDS Kγ c K cw w)) ∧
      (∀ m : ℕ,
        Cited.csPhi Kγ c (3 * m) ≤
          (1 / (C₁ * Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
            Real.log (Real.log ((m : ℝ) + 2) + 2)))) / 10 ∧
        (Cited.csGamma Kγ (3 * m) : ℝ) ≤
          Real.exp (C_γ * Real.log ((m : ℝ) + 2) ^ (3 / 4 : ℝ))) ∧
      (∀ (G : Cited.Graph) (φ_G : ℝ),
        G.IsValid → 1 ≤ G.m → (∀ v < G.n, 1 ≤ G.deg v) →
        1 / (C₁ * Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((G.m : ℝ) + 2) + 2))) ≤ φ_G → φ_G ≤ 1 →
        G.IsConductanceExpanderOn G.verts φ_G →
        let G_s := subdivGraph G
        G_s.IsValid ∧ G_s.IsSimple ∧ 1 ≤ G_s.m ∧ G_s.m = 3 * G.m ∧
          (∀ v < G_s.n, 1 ≤ G_s.deg v) ∧
          G_s.IsConductanceExpanderOn G_s.verts (Cited.csPhi Kγ c G_s.m)) := by
  rcases hCS with ⟨Kγ, c₀, hKγ, hc₀, hCS_body⟩
  rcases csGamma_dominates_sb hKγ C₀ C₁ hC₀ hC₁ with ⟨c₁, hc₁, hdom⟩
  set c := max c₀ c₁
  have hc_ge_c₀ : c₀ ≤ c := le_max_left _ _
  have hc_ge_c₁ : c₁ ≤ c := le_max_right _ _
  have hc1 : 1 ≤ c := le_trans hc₀ hc_ge_c₀
  rcases hCS_body c hc_ge_c₀ with ⟨K, cw, mk, R, hImpl⟩
  rcases csGamma_le_exp_three_quarters Kγ with ⟨C_γ, hC_γ, hγ_up⟩
  refine ⟨Kγ, c₀, c, K, C_γ, cw, mk, R, hKγ, hc₀, hc_ge_c₀, hc1, hC_γ, hImpl, ?_, ?_⟩
  · intro m
    have hcR : (c₁ : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_ge_c₁
    have hcs_pos : (0 : ℝ) < (Cited.csGamma Kγ (3 * m) : ℝ) := by unfold Cited.csGamma; positivity
    have hphi_le : Cited.csPhi Kγ c (3 * m) ≤ Cited.csPhi Kγ c₁ (3 * m) := by
      unfold Cited.csPhi
      exact one_div_le_one_div_of_le (mul_pos (by exact_mod_cast hc₁) hcs_pos)
        (mul_le_mul_of_nonneg_right hcR hcs_pos.le)
    exact ⟨le_trans hphi_le (hdom m), hγ_up m⟩
  · intro G φ_G hV hm hnoIso hφ_low hφ_high hexp
    set G_s := subdivGraph G
    have hSV : G_s.IsValid := subdivGraph_isValid hV
    have hSS : G_s.IsSimple := subdivGraph_isSimple hV
    have hSm : G_s.m = 3 * G.m := subdivGraph_m G
    have hSm1 : 1 ≤ G_s.m := by omega
    have hSno : ∀ v < G_s.n, 1 ≤ G_s.deg v := subdivGraph_no_isolated hV hnoIso
    have hSexp : G_s.IsConductanceExpanderOn G_s.verts (Cited.csPhi Kγ c G_s.m) := by
      have hexp10 : G_s.IsConductanceExpanderOn G_s.verts (φ_G / 10) :=
        subdivGraph_expander hV (le_trans (by positivity) hφ_low) hφ_high hexp
      have hcs_le : Cited.csPhi Kγ c G_s.m ≤ φ_G / 10 := by
        rw [hSm]
        have hcR : (c₁ : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_ge_c₁
        have hcs_pos : (0 : ℝ) < (Cited.csGamma Kγ (3 * G.m) : ℝ) := by
          unfold Cited.csGamma; positivity
        have hphi_le : Cited.csPhi Kγ c (3 * G.m) ≤ Cited.csPhi Kγ c₁ (3 * G.m) := by
          unfold Cited.csPhi
          exact one_div_le_one_div_of_le (mul_pos (by exact_mod_cast hc₁) hcs_pos)
            (mul_le_mul_of_nonneg_right hcR hcs_pos.le)
        exact le_trans hphi_le (le_trans (hdom G.m) (by linarith))
      exact isConductanceExpanderOn_mono hcs_le hexp10
    exact ⟨hSV, hSS, hSm1, hSm, hSno, hSexp⟩

end

end MinCostFlow.Expander
