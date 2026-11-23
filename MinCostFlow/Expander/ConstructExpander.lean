module

public import MinCostFlow.Statement.Cited.ChuzhoyEtAl
public import MinCostFlow.Expander.GraphHelpers
import MinCostFlow.ExplicitExpander.Program
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Ring

/-!
# Explicit weighted expanders (Theorem 8.4)

Constructs an unweighted multigraph `W` (possibly with self-loops) on `n` vertices satisfying
`w v ≤ W.deg v ≤ 18 * w v` and conductance `φ_Const = α₀ / 9 ∈ (0, 1]` from
`Cited.ExplicitExpander` (Chuzhoy et al. [CGLNPS21], Theorem 2.4), which is proved as
`MinCostFlow.ExplicitExpander.explicitExpander`.

For `n > 1`, we set `N = ∑_{v < n} ⌈w v⌉₊ ≥ n > 1`, obtain the `α₀`-expander `H_N` of degree
`≤ 9`, and merge `⌈w v⌉₊` vertices of `H_N` into each vertex `v` (edges inside a group become
self-loops). For `n = 1`, we place `⌈w 0⌉₊` self-loops at vertex `0`; for `n = 0`, the empty
graph.
-/

public section

namespace MinCostFlow.Expander

open MinCostFlow.Cited

/-! ### Grouping vertices and merging `H_N` into `W` -/

/-- Vertex counts `⌈w 0⌉₊, …, ⌈w (n - 1)⌉₊` for rational weights `w`. -/
def countsOfWeights (n : ℕ) (w : ℕ → ℚ) : List ℕ :=
  (List.range n).map fun v => Nat.ceil (w v)

/-- Lookup table mapping each vertex `u < counts.sum` of `H_N` to its target vertex `v < counts.length`. -/
@[expose] def groupTable (counts : List ℕ) : List ℕ :=
  (List.range counts.length).flatMap fun v => List.replicate (counts.getD v 0) v

/-- Merge groups of sizes `counts` in `H` into a graph on `counts.length` vertices.
For `counts.length = 1`, creates `counts.getD 0 1` self-loops at `0` (so `N = 1` works too). -/
@[expose] def mergeExpander (counts : List ℕ) (H : Graph) : Graph :=
  match counts.length with
  | 0 => ⟨0, []⟩
  | 1 => ⟨1, List.replicate (counts.getD 0 1) (0, 0)⟩
  | n =>
    let grp := groupTable counts
    ⟨n, H.edges.map fun e => (grp.getD e.1 0, grp.getD e.2 0)⟩

lemma countsOfWeights_length (n : ℕ) (w : ℕ → ℚ) :
    (countsOfWeights n w).length = n := by
  simp [countsOfWeights]

lemma countsOfWeights_getD {n : ℕ} {w : ℕ → ℚ} {v : ℕ} (hv : v < n) :
    (countsOfWeights n w).getD v 0 = Nat.ceil (w v) := by
  simp [countsOfWeights, List.getD, hv]

lemma countsOfWeights_sum {n : ℕ} {w : ℕ → ℚ} :
    (countsOfWeights n w).sum = ∑ v ∈ Finset.range n, Nat.ceil (w v) := by
  unfold countsOfWeights
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero, Finset.sum_range_succ, ih]

private lemma list_flatMap_replicate_length (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).flatMap fun v => List.replicate (f v) v).length =
      ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.length_append, List.length_replicate, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero, ih]

lemma groupTable_length (counts : List ℕ) :
    (groupTable counts).length = counts.sum := by
  unfold groupTable
  rw [list_flatMap_replicate_length]
  congr 1
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  simp only [List.length_map, List.length_range] at hi1
  simp [List.getD, hi1]

private lemma mem_flatMap_replicate_lt {n : ℕ} {f : ℕ → ℕ} {x : ℕ}
    (hx : x ∈ (List.range n).flatMap fun v => List.replicate (f v) v) : x < n := by
  rw [List.mem_flatMap] at hx
  obtain ⟨v, hv, hxv⟩ := hx
  rw [List.mem_replicate] at hxv
  rw [hxv.2]
  exact List.mem_range.mp hv

lemma groupTable_getD_lt {counts : List ℕ} {u : ℕ} (hu : u < (groupTable counts).length) :
    (groupTable counts).getD u 0 < counts.length := by
  unfold groupTable at hu ⊢
  rw [List.getD_eq_getElem _ _ hu]
  exact mem_flatMap_replicate_lt (List.getElem_mem hu)

private lemma count_flatMap_replicate (n : ℕ) (f : ℕ → ℕ) (v : ℕ) :
    ((List.range n).flatMap fun i => List.replicate (f i) i).count v =
      if v < n then f v else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.count_append, ih, List.count_replicate]
    by_cases hv : v = n
    · subst hv; simp
    · have h1 : v < n + 1 ↔ v < n := by omega
      simp [h1, Ne.symm hv]

private lemma count_eq_card_filter_getD (l : List ℕ) (v : ℕ) :
    ((Finset.range l.length).filter fun u => l.getD u 0 = v).card = l.count v := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    simp only [List.length_append, List.length_singleton, List.count_append, List.count_singleton]
    have hsplit : (Finset.range (xs.length + 1)).filter (fun u => (xs ++ [x]).getD u 0 = v) =
        ((Finset.range xs.length).filter fun u => xs.getD u 0 = v) ∪
          (if x = v then {xs.length} else ∅) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
      by_cases hu : u < xs.length
      · have hne : u ≠ xs.length := by omega
        have hget : (xs ++ [x]).getD u 0 = xs.getD u 0 := by
          simp [List.getD, List.getElem?_append_left hu]
        rw [hget]
        split_ifs <;> simp [hu, hne, Nat.lt_succ_of_lt hu]
      · by_cases hueq : u = xs.length
        · subst hueq
          have hget : (xs ++ [x]).getD xs.length 0 = x := by
            simp [List.getD]
          rw [hget]
          split_ifs with hxv
          · simp [hxv]
          · simp [hxv]
        · have hnot : ¬ u < xs.length + 1 := by omega
          split_ifs <;> simp [hu, hueq, hnot]
    have hdisj : Disjoint ((Finset.range xs.length).filter fun u => xs.getD u 0 = v)
        (if x = v then {xs.length} else ∅) := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      have hult := (Finset.mem_filter.mp hu1).1
      rw [Finset.mem_range] at hult
      split_ifs at hu2
      · simp at hu2; omega
      · simp at hu2
    rw [hsplit, Finset.card_union_of_disjoint hdisj, ih]
    by_cases hxv : x = v <;> simp [hxv]

lemma card_groupTable_preimage {counts : List ℕ} {v : ℕ} (hv : v < counts.length) :
    ((Finset.range (groupTable counts).length).filter
      fun u => (groupTable counts).getD u 0 = v).card = counts.getD v 0 := by
  rw [count_eq_card_filter_getD]
  unfold groupTable
  rw [count_flatMap_replicate]
  simp [hv]

lemma exists_groupTable_eq {counts : List ℕ} {v : ℕ} (hv : v < counts.length)
    (hpos : 1 ≤ counts.getD v 0) :
    ∃ u < (groupTable counts).length, (groupTable counts).getD u 0 = v := by
  have hcard := card_groupTable_preimage hv
  have hne : ((Finset.range (groupTable counts).length).filter
      fun u => (groupTable counts).getD u 0 = v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro heq
    rw [heq, Finset.card_empty] at hcard
    omega
  obtain ⟨u, hu⟩ := hne
  rw [Finset.mem_filter, Finset.mem_range] at hu
  exact ⟨u, hu.1, hu.2⟩

/-! ### Properties of `mergeExpander` -/

lemma mergeExpander_n (counts : List ℕ) (H : Graph) :
    (mergeExpander counts H).n = counts.length := by
  unfold mergeExpander
  split <;> simp_all

lemma mergeExpander_isValid {counts : List ℕ} {H : Graph}
    (hH_n : H.n = counts.sum) (hH_v : H.IsValid) :
    (mergeExpander counts H).IsValid := by
  unfold mergeExpander
  split
  · intro e he; simp at he
  · intro e he
    rw [List.mem_replicate] at he
    rw [he.2]
    simp
  · intro e he
    rw [List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    have hlt := hH_v e' he'
    have hlen : (groupTable counts).length = H.n := by rw [groupTable_length, hH_n]
    exact ⟨groupTable_getD_lt (hlen ▸ hlt.1), groupTable_getD_lt (hlen ▸ hlt.2)⟩

private lemma mergeExpander_deg_eq_sum {counts : List ℕ} {H : Graph}
    (hlen : 1 < counts.length) (hH_n : H.n = counts.sum) (hH_v : H.IsValid)
    {v : ℕ} (_hv : v < counts.length) :
    (mergeExpander counts H).deg v =
      ∑ u ∈ H.verts.filter (fun u => (groupTable counts).getD u 0 = v), H.deg u := by
  have hm_eq : mergeExpander counts H = ⟨counts.length,
      H.edges.map fun e => ((groupTable counts).getD e.1 0, (groupTable counts).getD e.2 0)⟩ := by
    unfold mergeExpander
    cases h : counts.length with
    | zero => omega
    | succ k =>
      cases k with
      | zero => omega
      | succ k' => simp
  have hv_m : (mergeExpander counts H).IsValid := mergeExpander_isValid hH_n hH_v
  conv_lhs =>
    unfold Graph.deg
    rw [degIn_eq_sum_map, inside_verts_of_isValid hv_m, hm_eq]
  simp only [List.map_map]
  have hdeg_u : ∀ u, H.deg u =
      (H.edges.map fun e => (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)).sum := by
    intro u
    unfold Graph.deg
    rw [degIn_eq_sum_map, inside_verts_of_isValid hH_v]
  simp_rw [hdeg_u]
  let Gv := H.verts.filter (fun u => (groupTable counts).getD u 0 = v)
  have hvalid : ∀ e ∈ H.edges, e.1 ∈ H.verts ∧ e.2 ∈ H.verts := by
    intro e he
    have h := hH_v e he
    simp [Graph.verts, h.1, h.2]
  suffices hgen : ∀ es : List (ℕ × ℕ), (∀ e ∈ es, e.1 ∈ H.verts ∧ e.2 ∈ H.verts) →
      (es.map fun x => (if (groupTable counts).getD x.1 0 = v then 1 else 0) +
          (if (groupTable counts).getD x.2 0 = v then 1 else 0)).sum =
        ∑ u ∈ Gv, (es.map fun e => (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)).sum by
    exact hgen H.edges hvalid
  intro es hes
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ← ih (fun e' he' => hes e' (by simp [he']))]
    have hev := hes e (by simp)
    have h1 : (∑ u ∈ Gv, if e.1 = u then 1 else 0) =
        if (groupTable counts).getD e.1 0 = v then 1 else 0 := by
      have hiff : e.1 ∈ Gv ↔ (groupTable counts).getD e.1 0 = v := by
        simp [Gv, hev.1]
      rw [Finset.sum_ite_eq]
      simp only [hiff]
    have h2 : (∑ u ∈ Gv, if e.2 = u then 1 else 0) =
        if (groupTable counts).getD e.2 0 = v then 1 else 0 := by
      have hiff : e.2 ∈ Gv ↔ (groupTable counts).getD e.2 0 = v := by
        simp [Gv, hev.2]
      rw [Finset.sum_ite_eq]
      simp only [hiff]
    omega

lemma one_le_deg_of_expansion {H : Graph} {α₀ : ℝ}
    (hHn : 1 < H.n) (hHv : H.IsValid) (hHl : H.IsLoopless)
    (hα : 0 < α₀) (hExp : H.IsExpansionExpanderOn H.verts α₀) :
    ∀ u < H.n, 1 ≤ H.deg u := by
  intro u hu
  have hS_sub : ({u} : Finset ℕ) ⊆ H.verts := by
    intro z hz
    simp only [Finset.mem_singleton] at hz
    subst hz
    exact Finset.mem_range.mpr hu
  have hS_ne : ({u} : Finset ℕ) ≠ H.verts := by
    intro hEq
    have hcard := congrArg Finset.card hEq
    simp [Graph.verts] at hcard
    omega
  have hexp := hExp {u} hS_sub ⟨u, Finset.mem_singleton_self u⟩ hS_ne
  have hcard_min : min (({u} : Finset ℕ).card : ℝ) ((H.verts \ {u}).card : ℝ) = 1 := by
    have h1 : ({u} : Finset ℕ).card = 1 := Finset.card_singleton u
    have h2 : 1 ≤ (H.verts \ {u}).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS_sub, Finset.card_singleton]
      simp [Graph.verts]
      omega
    have h2r : (1 : ℝ) ≤ ((H.verts \ {u}).card : ℝ) := by exact_mod_cast h2
    rw [h1]
    simp [min_eq_left h2r]
  rw [hcard_min, mul_one] at hexp
  have hcut_eq : H.cut {u} = H.deg u := (deg_eq_cut_singleton hHv hHl hu).symm
  unfold Graph.cut at hcut_eq
  rw [hcut_eq] at hexp
  have hpos : (0 : ℝ) < (H.deg u : ℝ) := lt_of_lt_of_le hα hexp
  exact_mod_cast (by
    by_contra hlt
    have hz : H.deg u = 0 := by omega
    rw [hz] at hpos
    simp at hpos)

lemma mergeExpander_deg_bounds {counts : List ℕ} {H : Graph} {α₀ : ℝ}
    (hcounts : ∀ v < counts.length, 1 ≤ counts.getD v 0)
    (hH_n : H.n = counts.sum) (hH_v : H.IsValid) (hH_l : H.IsLoopless)
    (hα : 0 < α₀) (hExp : H.IsExpansionExpanderOn H.verts α₀)
    (hdeg : ∀ u < H.n, H.deg u ≤ 9) :
    ∀ v < counts.length,
      counts.getD v 0 ≤ (mergeExpander counts H).deg v ∧
        (mergeExpander counts H).deg v ≤ 9 * counts.getD v 0 := by
  intro v hv
  rcases Nat.lt_trichotomy counts.length 1 with h0 | h1 | hgt
  · omega
  · have hv0 : v = 0 := by omega
    subst hv0
    have hmeq : mergeExpander counts H = ⟨1, List.replicate (counts.getD 0 1) (0, 0)⟩ := by
      unfold mergeExpander
      simp [h1]
    have hdeg0 : (⟨1, List.replicate (counts.getD 0 1) (0, 0)⟩ : Graph).deg 0 =
        2 * counts.getD 0 1 := by
      unfold Graph.deg Graph.degIn Graph.inside Graph.verts
      simp
      ring
    rw [hmeq, hdeg0]
    have hc_eq : counts.getD 0 1 = counts.getD 0 0 := by
      simp [List.getD, show 0 < counts.length by omega]
    rw [← hc_eq]
    omega
  · have hHn_gt : 1 < H.n := by
      rw [hH_n]
      have : 2 ≤ counts.sum := by
        clear hH_n hH_v hH_l hExp hdeg
        have h0 := hcounts 0 (by omega)
        have h1' := hcounts 1 hgt
        cases counts with
        | nil => simp at hgt
        | cons a t =>
          cases t with
          | nil => simp at hgt
          | cons b bs =>
            simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
              Option.getD_some] at h0 h1'
            simp only [List.sum_cons]
            omega
      omega
    have hmin : ∀ u < H.n, 1 ≤ H.deg u := one_le_deg_of_expansion hHn_gt hH_v hH_l hα hExp
    rw [mergeExpander_deg_eq_sum hgt hH_n hH_v hv]
    let Gv := H.verts.filter (fun u => (groupTable counts).getD u 0 = v)
    have hcard : Gv.card = counts.getD v 0 := by
      dsimp [Gv]
      unfold Graph.verts
      rw [hH_n, ← groupTable_length counts]
      exact card_groupTable_preimage hv
    have hlo : ∑ u ∈ Gv, 1 ≤ ∑ u ∈ Gv, H.deg u := by
      apply Finset.sum_le_sum
      intro u hu
      have huV := (Finset.mem_filter.mp hu).1
      exact hmin u (Finset.mem_range.mp huV)
    have hhi : ∑ u ∈ Gv, H.deg u ≤ ∑ u ∈ Gv, 9 := by
      apply Finset.sum_le_sum
      intro u hu
      have huV := (Finset.mem_filter.mp hu).1
      exact hdeg u (Finset.mem_range.mp huV)
    simp only [Finset.sum_const, smul_eq_mul, hcard, mul_one] at hlo hhi
    dsimp only [Gv] at hlo hhi
    exact ⟨hlo, by omega⟩

lemma mergeExpander_conductance {counts : List ℕ} {H : Graph} {α₀ : ℝ}
    (hcounts : ∀ v < counts.length, 1 ≤ counts.getD v 0)
    (hH_n : H.n = counts.sum) (hH_v : H.IsValid)
    (hα : 0 < α₀) (hExp : H.IsExpansionExpanderOn H.verts α₀)
    (hdeg : ∀ u < H.n, H.deg u ≤ 9) :
    (mergeExpander counts H).IsConductanceExpanderOn (mergeExpander counts H).verts (α₀ / 9) := by
  by_cases hle : counts.length ≤ 1
  · apply isConductanceExpanderOn_of_card_le_one
    rw [Graph.verts, Finset.card_range, mergeExpander_n]
    exact hle
  have hgt : 1 < counts.length := by omega
  have hm_eq : mergeExpander counts H = ⟨counts.length,
      H.edges.map fun e => ((groupTable counts).getD e.1 0, (groupTable counts).getD e.2 0)⟩ := by
    unfold mergeExpander
    cases h : counts.length with
    | zero => omega
    | succ k =>
      cases k with
      | zero => omega
      | succ k' => simp
  have hmv : (mergeExpander counts H).IsValid := mergeExpander_isValid hH_n hH_v
  intro S hSV hSne hSneV
  rw [Graph.verts, mergeExpander_n] at hSV hSneV
  let grp := groupTable counts
  have hgrplen : grp.length = H.n := by rw [groupTable_length, hH_n]
  let S' : Finset ℕ := H.verts.filter fun u => grp.getD u 0 ∈ S
  have hS'_sub : S' ⊆ H.verts := Finset.filter_subset _ _
  have hS'_ne : S'.Nonempty := by
    obtain ⟨v, hvS⟩ := hSne
    have hv_lt : v < counts.length := Finset.mem_range.mp (hSV hvS)
    obtain ⟨u, hu_len, hu_eq⟩ := exists_groupTable_eq hv_lt (hcounts v hv_lt)
    refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hgrplen ▸ hu_len), ?_⟩⟩
    rw [hu_eq]
    exact hvS
  have hS'_neV : S' ≠ H.verts := by
    have hnot : ∃ v ∈ (mergeExpander counts H).verts, v ∉ S := by
      by_contra hall
      push Not at hall
      exact hSneV (Finset.Subset.antisymm hSV fun z hz =>
        hall z (by simpa [Graph.verts, mergeExpander_n] using hz))
    obtain ⟨v, hvV, hvS⟩ := hnot
    rw [Graph.verts, mergeExpander_n, Finset.mem_range] at hvV
    obtain ⟨u, hu_len, hu_eq⟩ := exists_groupTable_eq hvV (hcounts v hvV)
    intro hEq
    have huV : u ∈ H.verts := Finset.mem_range.mpr (hgrplen ▸ hu_len)
    have huS' : u ∈ S' := hEq ▸ huV
    have : grp.getD u 0 ∈ S := (Finset.mem_filter.mp huS').2
    rw [hu_eq] at this
    exact hvS this
  have hcut_eq : (mergeExpander counts H).cutIn (mergeExpander counts H).verts S = H.cutIn H.verts S' := by
    rw [cutIn_eq_sum_map, cutIn_eq_sum_map, inside_verts_of_isValid hmv, inside_verts_of_isValid hH_v, hm_eq]
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro e he
    have hev := hH_v e he
    have h1 : grp.getD e.1 0 ∈ S ↔ e.1 ∈ S' := by
      simp [S', Graph.verts, hev.1]
    have h2 : grp.getD e.2 0 ∈ S ↔ e.2 ∈ S' := by
      simp [S', Graph.verts, hev.2]
    change (if decide (grp.getD e.1 0 ∈ S) != decide (grp.getD e.2 0 ∈ S) then 1 else 0) =
      if decide (e.1 ∈ S') != decide (e.2 ∈ S') then 1 else 0
    simp only [h1, h2]
  have hvol_eq : ∀ T ⊆ (mergeExpander counts H).verts,
      (mergeExpander counts H).volIn (mergeExpander counts H).verts T =
        H.volIn H.verts (H.verts.filter fun u => grp.getD u 0 ∈ T) := by
    intro T _
    rw [volIn_eq_sum_map, volIn_eq_sum_map, inside_verts_of_isValid hmv, inside_verts_of_isValid hH_v, hm_eq]
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro e he
    have hev := hH_v e he
    have h1 : grp.getD e.1 0 ∈ T ↔ e.1 ∈ H.verts.filter fun u => grp.getD u 0 ∈ T := by
      simp [Graph.verts, hev.1]
    have h2 : grp.getD e.2 0 ∈ T ↔ e.2 ∈ H.verts.filter fun u => grp.getD u 0 ∈ T := by
      simp [Graph.verts, hev.2]
    change (if grp.getD e.1 0 ∈ T then 1 else 0) + (if grp.getD e.2 0 ∈ T then 1 else 0) =
      (if e.1 ∈ H.verts.filter (fun u => grp.getD u 0 ∈ T) then 1 else 0) +
      (if e.2 ∈ H.verts.filter (fun u => grp.getD u 0 ∈ T) then 1 else 0)
    simp only [h1, h2]
  have hvol1 : (mergeExpander counts H).volIn (mergeExpander counts H).verts S = H.volIn H.verts S' :=
    hvol_eq S (by simpa [Graph.verts, mergeExpander_n] using hSV)
  have hvol2 : (mergeExpander counts H).volIn (mergeExpander counts H).verts ((mergeExpander counts H).verts \ S) =
      H.volIn H.verts (H.verts \ S') := by
    rw [hvol_eq _ Finset.sdiff_subset]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_sdiff, Graph.verts, mergeExpander_n, Finset.mem_range]
    constructor
    · rintro ⟨hu, hlt, hn⟩
      exact ⟨hu, fun h => hn (Finset.mem_filter.mp h).2⟩
    · rintro ⟨hu, hn⟩
      refine ⟨hu, groupTable_getD_lt (hgrplen.symm ▸ hu), fun h => hn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu, h⟩)⟩
  have hvolS_le : (H.volIn H.verts S' : ℝ) ≤ 9 * (S'.card : ℝ) := by
    have hnat : H.volIn H.verts S' ≤ 9 * S'.card := by
      unfold Graph.volIn
      calc ∑ u ∈ S', H.degIn H.verts u
          ≤ ∑ _u ∈ S', 9 := Finset.sum_le_sum fun u hu => hdeg u (Finset.mem_range.mp (hS'_sub hu))
        _ = 9 * S'.card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
    exact_mod_cast hnat
  have hvolSc_le : (H.volIn H.verts (H.verts \ S') : ℝ) ≤ 9 * ((H.verts \ S').card : ℝ) := by
    have hnat : H.volIn H.verts (H.verts \ S') ≤ 9 * (H.verts \ S').card := by
      unfold Graph.volIn
      calc ∑ u ∈ H.verts \ S', H.degIn H.verts u
          ≤ ∑ _u ∈ H.verts \ S', 9 :=
            Finset.sum_le_sum fun u hu => hdeg u (Finset.mem_range.mp (Finset.sdiff_subset hu))
        _ = 9 * (H.verts \ S').card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
    exact_mod_cast hnat
  have hmin : min ((mergeExpander counts H).volIn (mergeExpander counts H).verts S : ℝ)
      ((mergeExpander counts H).volIn (mergeExpander counts H).verts ((mergeExpander counts H).verts \ S) : ℝ) ≤
      9 * min (S'.card : ℝ) ((H.verts \ S').card : ℝ) := by
    rw [hvol1, hvol2]
    calc min (H.volIn H.verts S' : ℝ) (H.volIn H.verts (H.verts \ S') : ℝ)
        ≤ min (9 * (S'.card : ℝ)) (9 * ((H.verts \ S').card : ℝ)) := min_le_min hvolS_le hvolSc_le
      _ = 9 * min (S'.card : ℝ) ((H.verts \ S').card : ℝ) := by
          rw [← mul_min_of_nonneg _ _ (by norm_num)]
  have hexp := hExp S' hS'_sub hS'_ne hS'_neV
  rw [hcut_eq]
  have hdiv : (α₀ / 9) * min ((mergeExpander counts H).volIn (mergeExpander counts H).verts S : ℝ)
      ((mergeExpander counts H).volIn (mergeExpander counts H).verts ((mergeExpander counts H).verts \ S) : ℝ) ≤
      α₀ * min (S'.card : ℝ) ((H.verts \ S').card : ℝ) := by
    calc (α₀ / 9) * min _ _
        ≤ (α₀ / 9) * (9 * min (S'.card : ℝ) ((H.verts \ S').card : ℝ)) :=
          mul_le_mul_of_nonneg_left hmin (by positivity)
      _ = α₀ * min (S'.card : ℝ) ((H.verts \ S').card : ℝ) := by ring
  exact le_trans hdiv hexp

/-! ### Theorem 8.4 from `Cited.ExplicitExpander` -/

lemma explicitExpander_alpha_le_nine {α₀ : ℝ} {P : WordRAM.Program} {c : ℕ} {K : ℝ}
    (hspec : ∀ n : ℕ, 1 < n → ∀ ω, ∃ out cost,
      WordRAM.RunsTo (WordRAM.wordSize c [n]) P [n] ω out cost ∧
      (∃ H : Graph, out = H.encode ∧ H.n = n ∧ H.IsValid ∧ H.IsLoopless ∧
        H.IsExpansionExpanderOn H.verts α₀ ∧ ∀ v < n, H.deg v ≤ 9) ∧
      (cost : ℝ) ≤ K * n) :
    α₀ ≤ 9 := by
  obtain ⟨_, _, _, ⟨H, _, hHn, _, _, hExp, hdeg⟩, _⟩ := hspec 2 (by norm_num) (fun _ => false)
  have hS_sub : ({0} : Finset ℕ) ⊆ H.verts := by
    intro x hx; simp only [Finset.mem_singleton] at hx; subst hx; simp [Graph.verts, hHn]
  have hS_neV : ({0} : Finset ℕ) ≠ H.verts := by
    intro hEq
    have hc := congrArg Finset.card hEq
    simp [Graph.verts, hHn] at hc
  have hexp := hExp {0} hS_sub ⟨0, Finset.mem_singleton_self 0⟩ hS_neV
  have hcard : min (({0} : Finset ℕ).card : ℝ) ((H.verts \ {0}).card : ℝ) = 1 := by
    have h1 : ({0} : Finset ℕ).card = 1 := Finset.card_singleton 0
    have h2 : (H.verts \ {0}).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS_sub, Finset.card_singleton]
      simp [Graph.verts, hHn]
    rw [h1, h2]; norm_num
  rw [hcard, mul_one] at hexp
  have hcut : H.cutIn H.verts {0} ≤ H.deg 0 := by
    unfold Graph.deg
    exact cutIn_le_volIn H H.verts {0} |>.trans (by simp [Graph.volIn])
  have hdeg0 : H.deg 0 ≤ 9 := hdeg 0 (by norm_num)
  have hcut_r : (H.cutIn H.verts {0} : ℝ) ≤ 9 := by exact_mod_cast le_trans hcut hdeg0
  exact le_trans hexp hcut_r

/-- Weighted expander model `ConstructExpander(n, w)` built from an explicit expander family `buildH`. -/
@[expose] def constructExpanderModel (buildH : (N : ℕ) → 1 < N → Graph) (n : ℕ)
    (w : ℕ → ℚ) : Graph :=
  let counts := countsOfWeights n w
  if hN : 1 < counts.sum then
    mergeExpander counts (buildH counts.sum hN)
  else
    mergeExpander counts ⟨counts.sum, []⟩

/-- Explicit operation count of `constructExpanderModel`: counts `n` weight ceilings,
`counts.sum` vertex-table / self-loop entries, plus the cited Word-RAM cost of `buildH` and
remapping `H.m` edges when `1 < counts.sum`. -/
@[expose] def constructExpanderCost (buildH : (N : ℕ) → 1 < N → Graph)
    (citedCost : (N : ℕ) → 1 < N → ℕ) (n : ℕ) (w : ℕ → ℚ) : ℕ :=
  let counts := countsOfWeights n w
  n + counts.sum +
    if hN : 1 < counts.sum then citedCost counts.sum hN + (buildH counts.sum hN).m else 0

/-- **Theorem 8.4** (page 40), derived from `Cited.ExplicitExpander`.
Returns `(φ_Const, P, c_w, K_cited, K_run, buildH, citedCost)` with `0 < φ_Const ≤ 1` such that
for any `n : ℕ` and rational weight vector `w : ℕ → ℚ` with `∀ v < n, 1 ≤ w v`,
`W := constructExpanderModel buildH n w` is a valid `φ_Const`-expander on `n` vertices with
`(w v : ℝ) ≤ W.deg v ≤ 18 * (w v : ℝ)`, `W.m ≤ 18 * ∑ v < n, (w v : ℝ)`, and the defined
operation count `constructExpanderCost buildH citedCost n w` (including the cited `RunsTo` cost of
`P` on `[N]`) is at most `K_run * (n + ∑ v < n, w v)`. -/
theorem theorem_8_4 :
    ∃ (φ_Const : ℝ) (P : WordRAM.Program) (c_w : ℕ) (K_cited K_run : ℝ)
      (buildH : (N : ℕ) → 1 < N → Graph) (citedCost : (N : ℕ) → 1 < N → ℕ),
      0 < φ_Const ∧ φ_Const ≤ 1 ∧ 0 ≤ K_cited ∧ 0 ≤ K_run ∧
      (∀ (N : ℕ) (hN : 1 < N),
        WordRAM.RunsTo (WordRAM.wordSize c_w [N]) P [N] (fun _ => false)
          (buildH N hN).encode (citedCost N hN) ∧
        (citedCost N hN : ℝ) ≤ K_cited * N) ∧
      ∀ (n : ℕ) (w : ℕ → ℚ), (∀ v < n, 1 ≤ w v) →
        let W := constructExpanderModel buildH n w
        let cost := constructExpanderCost buildH citedCost n w
        W.n = n ∧ W.IsValid ∧ W.IsConductanceExpanderOn W.verts φ_Const ∧
        (∀ v < n, (w v : ℝ) ≤ (W.deg v : ℝ) ∧ (W.deg v : ℝ) ≤ 18 * (w v : ℝ)) ∧
        ((W.m : ℝ) ≤ 18 * ∑ v ∈ Finset.range n, (w v : ℝ)) ∧
        (cost : ℝ) ≤ K_run * (n + ∑ v ∈ Finset.range n, (w v : ℝ)) := by
  classical
  rcases MinCostFlow.ExplicitExpander.explicitExpander with ⟨α₀, P, c, K, hα₀, hspec⟩
  have hα_le : α₀ ≤ 9 := explicitExpander_alpha_le_nine hspec
  have hspec' : ∀ (N : ℕ), 1 < N →
      ∃ (H : Graph) (cost : ℕ),
        WordRAM.RunsTo (WordRAM.wordSize c [N]) P [N] (fun _ => false) H.encode cost ∧
        H.n = N ∧ H.IsValid ∧ H.IsLoopless ∧ H.IsExpansionExpanderOn H.verts α₀ ∧
        (∀ u < N, H.deg u ≤ 9) ∧ (cost : ℝ) ≤ K * N := by
    intro N hN
    obtain ⟨_, cost, hruns, ⟨H, henc, hHn, hHv, hHl, hHexp, hHdeg⟩, hcost⟩ :=
      hspec N hN (fun _ => false)
    exact ⟨H, cost, henc ▸ hruns, hHn, hHv, hHl, hHexp, hHdeg, hcost⟩
  let buildH : (N : ℕ) → 1 < N → Graph := fun N hN =>
    Classical.choose (hspec' N hN)
  let citedCost : (N : ℕ) → 1 < N → ℕ := fun N hN =>
    Classical.choose (Classical.choose_spec (hspec' N hN))
  have hbuildH : ∀ (N : ℕ) (hN : 1 < N),
      WordRAM.RunsTo (WordRAM.wordSize c [N]) P [N] (fun _ => false)
        (buildH N hN).encode (citedCost N hN) ∧
      (buildH N hN).n = N ∧ (buildH N hN).IsValid ∧ (buildH N hN).IsLoopless ∧
      (buildH N hN).IsExpansionExpanderOn (buildH N hN).verts α₀ ∧
      (∀ u < N, (buildH N hN).deg u ≤ 9) ∧
      (citedCost N hN : ℝ) ≤ K * N := by
    intro N hN
    exact Classical.choose_spec (Classical.choose_spec (hspec' N hN))
  let K_cited := max K 0
  let K_run := 12 + 2 * K_cited
  refine ⟨α₀ / 9, P, c, K_cited, K_run, buildH, citedCost,
    by positivity, by linarith, le_max_right _ _, by dsimp [K_run]; positivity, ?_, ?_⟩
  · intro N hN
    obtain ⟨hruns, _, _, _, _, _, hcost⟩ := hbuildH N hN
    refine ⟨hruns, le_trans hcost ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
  · intro n w hw
    dsimp only [constructExpanderModel, constructExpanderCost]
    set counts := countsOfWeights n w
    have hcounts_len : counts.length = n := countsOfWeights_length n w
    have hcounts_ge : ∀ v < counts.length, 1 ≤ counts.getD v 0 := by
      intro v hv
      rw [hcounts_len] at hv
      rw [countsOfWeights_getD hv]
      exact Nat.ceil_pos.mpr (lt_of_lt_of_le (by norm_num) (hw v hv))
    have hceil_bounds : ∀ v < n, (w v : ℝ) ≤ (Nat.ceil (w v) : ℝ) ∧
        (Nat.ceil (w v) : ℝ) ≤ 2 * (w v : ℝ) := by
      intro v hv
      have hw1 : (1 : ℝ) ≤ (w v : ℝ) := by exact_mod_cast hw v hv
      have hle : w v ≤ (Nat.ceil (w v) : ℚ) := Nat.le_ceil (w v)
      have hlt : (Nat.ceil (w v) : ℚ) < w v + 1 :=
        Nat.ceil_lt_add_one (le_trans zero_le_one (hw v hv))
      have hle_r : (w v : ℝ) ≤ (Nat.ceil (w v) : ℝ) := by exact_mod_cast hle
      have hlt_r : (Nat.ceil (w v) : ℝ) < (w v : ℝ) + 1 := by exact_mod_cast hlt
      exact ⟨hle_r, by linarith⟩
    have hsum_le : (counts.sum : ℝ) ≤ 2 * ∑ v ∈ Finset.range n, (w v : ℝ) := by
      rw [countsOfWeights_sum, Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v hv
      exact (hceil_bounds v (Finset.mem_range.mp hv)).2
    have hsum_nonneg : 0 ≤ ∑ v ∈ Finset.range n, (w v : ℝ) := by
      apply Finset.sum_nonneg
      intro v hv
      exact_mod_cast le_trans zero_le_one (hw v (Finset.mem_range.mp hv))
    have hcost_branch : ∀ (hN : 1 < counts.sum),
        (citedCost counts.sum hN : ℝ) + ((buildH counts.sum hN).m : ℝ) ≤
          (10 + 2 * K_cited) * ∑ v ∈ Finset.range n, (w v : ℝ) := by
      intro hN
      obtain ⟨_, hHn, hHv, _, _, hHdeg, hcost⟩ := hbuildH counts.sum hN
      have hcited : (citedCost counts.sum hN : ℝ) ≤ K_cited * (counts.sum : ℝ) :=
        le_trans hcost (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
      have hcited_w : (citedCost counts.sum hN : ℝ) ≤ 2 * K_cited * ∑ v ∈ Finset.range n, (w v : ℝ) := by
        calc (citedCost counts.sum hN : ℝ)
            ≤ K_cited * (counts.sum : ℝ) := hcited
          _ ≤ K_cited * (2 * ∑ v ∈ Finset.range n, (w v : ℝ)) :=
              mul_le_mul_of_nonneg_left hsum_le (le_max_right _ _)
          _ = 2 * K_cited * ∑ v ∈ Finset.range n, (w v : ℝ) := by ring
      have hHm : 2 * (buildH counts.sum hN).m ≤ 9 * counts.sum := by
        have hvol : (buildH counts.sum hN).vol (buildH counts.sum hN).verts =
            2 * (buildH counts.sum hN).m := vol_verts_of_isValid hHv
        have hvol_deg : (buildH counts.sum hN).vol (buildH counts.sum hN).verts =
            ∑ u ∈ Finset.range counts.sum, (buildH counts.sum hN).deg u := by
          unfold Graph.vol Graph.volIn Graph.deg Graph.verts
          rw [hHn]
        have hsum_deg : ∑ u ∈ Finset.range counts.sum, (buildH counts.sum hN).deg u ≤ 9 * counts.sum := by
          calc ∑ u ∈ Finset.range counts.sum, (buildH counts.sum hN).deg u
              ≤ ∑ _u ∈ Finset.range counts.sum, 9 :=
                Finset.sum_le_sum fun u hu => hHdeg u (Finset.mem_range.mp hu)
            _ = 9 * counts.sum := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
        omega
      have hHm_r : ((buildH counts.sum hN).m : ℝ) ≤ 5 * (counts.sum : ℝ) := by
        exact_mod_cast (show (buildH counts.sum hN).m ≤ 5 * counts.sum by omega)
      have hHm_w : ((buildH counts.sum hN).m : ℝ) ≤ 10 * ∑ v ∈ Finset.range n, (w v : ℝ) := by
        linarith
      linarith
    have hcost_total : ((n + counts.sum +
        if hN : 1 < counts.sum then citedCost counts.sum hN + (buildH counts.sum hN).m else 0 : ℕ) : ℝ) ≤
        K_run * ((n : ℝ) + ∑ v ∈ Finset.range n, (w v : ℝ)) := by
      rw [Nat.cast_add, Nat.cast_add]
      have htail : ((if hN : 1 < counts.sum then citedCost counts.sum hN + (buildH counts.sum hN).m else 0 : ℕ) : ℝ) ≤
          (10 + 2 * K_cited) * ∑ v ∈ Finset.range n, (w v : ℝ) := by
        split_ifs with hN
        · push_cast
          exact hcost_branch hN
        · push_cast
          positivity
      dsimp only [K_run]
      have hK_cited_nn : 0 ≤ K_cited := le_max_right _ _
      have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      nlinarith
    by_cases hgt1 : 1 < n
    · have hN_gt : 1 < counts.sum := by
        have h0 := hcounts_ge 0 (by omega)
        have h1 := hcounts_ge 1 (by omega)
        rw [countsOfWeights_getD (by omega)] at h0
        rw [countsOfWeights_getD (by omega)] at h1
        have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range n := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
        have hsum2 : ∑ v ∈ ({0, 1} : Finset ℕ), Nat.ceil (w v) ≤ counts.sum := by
          rw [countsOfWeights_sum]
          exact Finset.sum_le_sum_of_subset hsub
        have h01 : ∑ v ∈ ({0, 1} : Finset ℕ), Nat.ceil (w v) = Nat.ceil (w 0) + Nat.ceil (w 1) := by
          simp [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
        omega
      rw [dite_eq_left_of_eq_true (eq_true hN_gt)]
      obtain ⟨_, hHn, hHv, hHl, hHexp, hHdeg, _⟩ := hbuildH counts.sum hN_gt
      have hWn : (mergeExpander counts (buildH counts.sum hN_gt)).n = n := by
        rw [mergeExpander_n, hcounts_len]
      have hWv := mergeExpander_isValid hHn hHv
      have hHdeg' : ∀ u < (buildH counts.sum hN_gt).n, (buildH counts.sum hN_gt).deg u ≤ 9 := by
        simpa [hHn] using hHdeg
      have hWcond := mergeExpander_conductance hcounts_ge hHn hHv hα₀ hHexp hHdeg'
      have hWdeg := mergeExpander_deg_bounds hcounts_ge hHn hHv hHl hα₀ hHexp hHdeg'
      refine ⟨hWn, hWv, hWcond, ?_, ?_, hcost_total⟩
      · intro v hv
        have hdv := hWdeg v (hcounts_len.symm ▸ hv)
        rw [countsOfWeights_getD hv] at hdv
        have hcb := hceil_bounds v hv
        have hd1 : (Nat.ceil (w v) : ℝ) ≤ ((mergeExpander counts (buildH counts.sum hN_gt)).deg v : ℝ) := by
          exact_mod_cast hdv.1
        have hd2 : ((mergeExpander counts (buildH counts.sum hN_gt)).deg v : ℝ) ≤ 9 * (Nat.ceil (w v) : ℝ) := by
          exact_mod_cast hdv.2
        exact ⟨le_trans hcb.1 hd1, le_trans hd2 (by linarith [hcb.2])⟩
      · have hvol : (mergeExpander counts (buildH counts.sum hN_gt)).vol
            (mergeExpander counts (buildH counts.sum hN_gt)).verts =
            2 * (mergeExpander counts (buildH counts.sum hN_gt)).m :=
          vol_verts_of_isValid hWv
        have hvol_le : (mergeExpander counts (buildH counts.sum hN_gt)).m ≤ 9 * counts.sum := by
          have hsum_deg : ∑ v ∈ Finset.range n, (mergeExpander counts (buildH counts.sum hN_gt)).deg v ≤
              9 * counts.sum := by
            calc ∑ v ∈ Finset.range n, (mergeExpander counts (buildH counts.sum hN_gt)).deg v
                ≤ ∑ v ∈ Finset.range n, 9 * counts.getD v 0 :=
                  Finset.sum_le_sum fun v hv => (hWdeg v (hcounts_len.symm ▸ Finset.mem_range.mp hv)).2
              _ = 9 * ∑ v ∈ Finset.range n, Nat.ceil (w v) := by
                  rw [← Finset.mul_sum]
                  congr 1
                  apply Finset.sum_congr rfl
                  intro v hv
                  exact countsOfWeights_getD (Finset.mem_range.mp hv)
              _ = 9 * counts.sum := by rw [← countsOfWeights_sum]
          have hvol_eq : (mergeExpander counts (buildH counts.sum hN_gt)).vol
              (mergeExpander counts (buildH counts.sum hN_gt)).verts =
              ∑ v ∈ Finset.range n, (mergeExpander counts (buildH counts.sum hN_gt)).deg v := by
            unfold Graph.vol Graph.volIn Graph.deg Graph.verts
            rw [hWn]
          omega
        have hm_r : ((mergeExpander counts (buildH counts.sum hN_gt)).m : ℝ) ≤ 9 * (counts.sum : ℝ) := by
          exact_mod_cast hvol_le
        linarith
    · -- `n ≤ 1`: handle `n = 0` and `n = 1` uniformly
      have hcommon : ∀ (H0 : Graph), H0.n = counts.sum →
          (mergeExpander counts H0).n = n ∧ (mergeExpander counts H0).IsValid ∧
          (mergeExpander counts H0).IsConductanceExpanderOn (mergeExpander counts H0).verts (α₀ / 9) ∧
          (∀ v < n, (w v : ℝ) ≤ ((mergeExpander counts H0).deg v : ℝ) ∧
            ((mergeExpander counts H0).deg v : ℝ) ≤ 18 * (w v : ℝ)) ∧
          ((mergeExpander counts H0).m : ℝ) ≤ 18 * ∑ v ∈ Finset.range n, (w v : ℝ) := by
        intro H0 _hH0n
        have hWn : (mergeExpander counts H0).n = n := by rw [mergeExpander_n, hcounts_len]
        have hWv : (mergeExpander counts H0).IsValid := by
          unfold mergeExpander
          cases hlen_c : counts.length with
          | zero => intro e he; simp at he
          | succ k =>
            cases k with
            | zero =>
              intro e he
              change e ∈ List.replicate (counts.getD 0 1) (0, 0) at he
              change e.1 < 1 ∧ e.2 < 1
              rw [List.mem_replicate] at he
              rw [he.2]; omega
            | succ k' =>
              exfalso
              rw [hcounts_len] at hlen_c
              omega
        have hWcond : (mergeExpander counts H0).IsConductanceExpanderOn (mergeExpander counts H0).verts (α₀ / 9) := by
          apply isConductanceExpanderOn_of_card_le_one
          rw [Graph.verts, Finset.card_range, hWn]
          omega
        refine ⟨hWn, hWv, hWcond, ?_, ?_⟩
        · intro v hv
          have hn1 : n = 1 := by omega
          have hv0 : v = 0 := by omega
          subst hv0
          have hlen1 : counts.length = 1 := by rw [hcounts_len, hn1]
          have hmeq : mergeExpander counts H0 = ⟨1, List.replicate (counts.getD 0 1) (0, 0)⟩ := by
            unfold mergeExpander; simp [hlen1]
          have hdeg0 : (mergeExpander counts H0).deg 0 = 2 * counts.getD 0 1 := by
            rw [hmeq]
            unfold Graph.deg Graph.degIn Graph.inside Graph.verts
            simp
            ring
          have hce : counts.getD 0 1 = Nat.ceil (w 0) := by
            have : counts.getD 0 1 = counts.getD 0 0 := by
              simp [List.getD, show 0 < counts.length by omega]
            rw [this]
            exact countsOfWeights_getD hv
          rw [hdeg0, hce]
          have hcb := hceil_bounds 0 hv
          have hd_r : ((2 * Nat.ceil (w 0) : ℕ) : ℝ) = 2 * (Nat.ceil (w 0) : ℝ) := by push_cast; ring
          rw [hd_r]
          exact ⟨by linarith [hcb.1], by linarith [hcb.2]⟩
        · rcases Nat.eq_zero_or_pos n with rfl | hn_pos
          · have hlen0 : counts.length = 0 := by rw [hcounts_len]
            have hm0 : (mergeExpander counts H0).m = 0 := by
              unfold mergeExpander Graph.m
              simp [hlen0]
            simp [hm0]
          · have hn1 : n = 1 := by omega
            have hlen1 : counts.length = 1 := by rw [hcounts_len, hn1]
            have hm1 : (mergeExpander counts H0).m = Nat.ceil (w 0) := by
              unfold mergeExpander Graph.m
              simp only [hlen1, List.length_replicate]
              have : counts.getD 0 1 = counts.getD 0 0 := by
                simp [List.getD, show 0 < counts.length by omega]
              rw [this]
              exact countsOfWeights_getD (by omega)
            rw [hm1, hn1, Finset.sum_range_one]
            have hcb := hceil_bounds 0 (by omega)
            linarith [hcb.2]
      by_cases hyes : 1 < counts.sum
      · rw [dite_eq_left_of_eq_true (eq_true hyes)]
        have hres := hcommon (buildH counts.sum hyes) (hbuildH counts.sum hyes).2.1
        exact ⟨hres.1, hres.2.1, hres.2.2.1, hres.2.2.2.1, hres.2.2.2.2, hcost_total⟩
      · rw [dite_eq_right_of_eq_false (eq_false hyes)]
        have hres := hcommon ⟨counts.sum, []⟩ rfl
        exact ⟨hres.1, hres.2.1, hres.2.2.1, hres.2.2.2.1, hres.2.2.2.2, hcost_total⟩

end MinCostFlow.Expander
