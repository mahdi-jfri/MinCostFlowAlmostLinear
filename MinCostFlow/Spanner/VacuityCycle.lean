module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Basic.Graph
public import MinCostFlow.Basic.Embedding
public import MinCostFlow.DynSpanner.Tools
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.ToolCosts
public import MinCostFlow.Spanner.Subgraph
public import MinCostFlow.Spanner.Algorithm
public import MinCostFlow.Spanner.WitnessBounds
public import MinCostFlow.Spanner.Runtime
public import MinCostFlow.Spanner.Theorem81
public import MinCostFlow.Spanner.MGraphTranslate
public import MinCostFlow.Spanner.MGraphSpec

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Non-Vacuity Witnesses: the Cycle Expander

This file holds the first part of the material of `Vacuity.lean`, split off to keep files
small. `Vacuity.lean` gives the overview.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Section 1: Explicit `BoundedConstructExpanderTool` (Cycle + Self-Loops) -/

private noncomputable def cycleLoopsGraph (n : ℕ) (w : ℕ → ℝ) : Graph :=
  ⟨n, (List.range n).map (fun i => (i, (i + 1) % n)) ++
      (List.range n).flatMap (fun v => List.replicate (Nat.ceil (w v)) (v, v))⟩

private theorem cycleLoopsGraph_isValid (n : ℕ) (hn : 0 < n) (w : ℕ → ℝ) :
    (cycleLoopsGraph n w).IsValid := by
  intro e he
  dsimp only [cycleLoopsGraph] at he
  rw [List.mem_append] at he
  rcases he with hcyc | hloop
  · rw [List.mem_map] at hcyc
    rcases hcyc with ⟨i, hi, rfl⟩
    exact ⟨List.mem_range.mp hi, Nat.mod_lt _ hn⟩
  · rw [List.mem_flatMap] at hloop
    rcases hloop with ⟨v, hv, hrep⟩
    have hv' : v < n := List.mem_range.mp hv
    have heq := List.eq_of_mem_replicate hrep
    rw [heq]
    exact ⟨hv', hv'⟩

private theorem filter_range_card_eq {n : ℕ} (p : ℕ → Bool) (huniq : ∃! u, u < n ∧ p u = true) :
    ((Finset.range n).filter (fun i => p i = true)).card = 1 := by
  rcases huniq with ⟨u, ⟨hun, hpu⟩, hother⟩
  have heq : (Finset.range n).filter (fun i => p i = true) = {u} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    exact ⟨fun h => hother i h, by rintro rfl; exact ⟨hun, hpu⟩⟩
  rw [heq, Finset.card_singleton]

private theorem sum_filter_replicate_self (l : List ℕ) (f : ℕ → ℕ) (v : ℕ) (p : (ℕ × ℕ) → Bool)
    (hp : ∀ u, p (u, u) = decide (u = v)) :
    ((l.flatMap fun u => List.replicate (f u) (u, u)).filter p).length =
      (l.map fun u => if u = v then f u else 0).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.flatMap_cons, List.filter_append, List.length_append, ih, List.map_cons, List.sum_cons]
    congr 1
    by_cases hav : a = v
    · subst hav
      have hpu : p (a, a) = true := by rw [hp a]; simp
      simp only [↓reduceIte, List.filter_replicate, hpu, List.length_replicate]
    · have hpu : p (a, a) = false := by rw [hp a]; simp [hav]
      simp only [hav, ↓reduceIte, List.filter_replicate, hpu, Bool.false_eq_true, List.length_nil]

private theorem list_sum_range_ite_eq {n v : ℕ} (hv : v < n) (f : ℕ → ℕ) :
    ((List.range n).map fun u => if u = v then f u else 0).sum = f v := by
  have h1 : ((List.range n).map fun u => if u = v then f u else 0).sum =
      ∑ u ∈ Finset.range n, if u = v then f u else 0 := by
    clear hv
    induction n with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
          ih, Finset.sum_range_succ]
  rw [h1, Finset.sum_ite_eq']
  simp [Finset.mem_range.mpr hv]

private theorem cycleLoopsGraph_deg {n : ℕ} (hn : 1 < n) (w : ℕ → ℝ) {v : ℕ} (hv : v < n) :
    (cycleLoopsGraph n w).deg v = 2 + 2 * Nat.ceil (w v) := by
  have hvalid := cycleLoopsGraph_isValid n (by omega) w
  rw [deg_eq_filter_edges hvalid v]
  dsimp only [cycleLoopsGraph]
  rw [List.filter_append, List.filter_append, List.length_append, List.length_append]
  have hcyc1 : (((List.range n).map fun i => (i, (i + 1) % n)).filter fun e => decide (e.1 = v)).length = 1 := by
    rw [List.filter_map, List.length_map, list_filter_length_eq_range_card _ 0]
    have hrl : (List.range n).length = n := List.length_range
    refine filter_range_card_eq _ ⟨v, ⟨hrl.symm ▸ hv, ?_⟩, fun i hi => ?_⟩
    · simp only [Function.comp_apply, List.getD_eq_getElem _ _ (hrl.symm ▸ hv),
        List.getElem_range, decide_eq_true_eq]
    · have hin : i < n := hrl ▸ hi.1
      have hid := hi.2
      simp only [Function.comp_apply, List.getD_eq_getElem _ _ hi.1,
        List.getElem_range, decide_eq_true_eq] at hid
      exact hid
  have hcyc2 : (((List.range n).map fun i => (i, (i + 1) % n)).filter fun e => decide (e.2 = v)).length = 1 := by
    rw [List.filter_map, List.length_map, list_filter_length_eq_range_card _ 0]
    let u₀ := if v = 0 then n - 1 else v - 1
    have hu₀_n : u₀ < n := by dsimp [u₀]; split_ifs <;> omega
    have hmod_iff : ∀ i < n, (i + 1) % n = v ↔ i = u₀ := by
      intro i hin
      dsimp [u₀]
      by_cases hi1 : i + 1 < n
      · rw [Nat.mod_eq_of_lt hi1]
        split_ifs with hv0 <;> omega
      · have hin1 : i + 1 = n := by omega
        rw [hin1, Nat.mod_self]
        split_ifs with hv0
        · subst hv0; omega
        · omega
    have hrl : (List.range n).length = n := List.length_range
    refine filter_range_card_eq _ ⟨u₀, ⟨hrl.symm ▸ hu₀_n, ?_⟩, fun i hi => ?_⟩
    · simp only [Function.comp_apply, List.getD_eq_getElem _ _ (hrl.symm ▸ hu₀_n),
        List.getElem_range, decide_eq_true_eq]
      exact (hmod_iff u₀ hu₀_n).mpr rfl
    · have hin : i < n := hrl ▸ hi.1
      have hid := hi.2
      simp only [Function.comp_apply, List.getD_eq_getElem _ _ hi.1,
        List.getElem_range, decide_eq_true_eq] at hid
      exact (hmod_iff i hin).mp hid
  have hloop1 : (((List.range n).flatMap fun u => List.replicate (Nat.ceil (w u)) (u, u)).filter
      fun e => decide (e.1 = v)).length = Nat.ceil (w v) := by
    rw [sum_filter_replicate_self _ _ v _ (fun u => rfl), list_sum_range_ite_eq hv]
  have hloop2 : (((List.range n).flatMap fun u => List.replicate (Nat.ceil (w u)) (u, u)).filter
      fun e => decide (e.2 = v)).length = Nat.ceil (w v) := by
    rw [sum_filter_replicate_self _ _ v _ (fun u => rfl), list_sum_range_ite_eq hv]
  rw [hcyc1, hcyc2, hloop1, hloop2]
  omega

private theorem cycle_cut_exists {n : ℕ} (hn : 0 < n) {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) (hne : S.Nonempty) (hneq : S ≠ Finset.range n) :
    ∃ i < n, i ∈ S ∧ (i + 1) % n ∉ S := by
  by_contra hnone
  push Not at hnone
  rcases hne with ⟨u, huS⟩
  have hu_n : u < n := Finset.mem_range.mp (hS huS)
  have hwalk : ∀ k : ℕ, (u + k) % n ∈ S := by
    intro k
    induction k with
    | zero => simpa [Nat.mod_eq_of_lt hu_n] using huS
    | succ k ih =>
      have hk_n : (u + k) % n < n := Nat.mod_lt _ hn
      have hnxt : ((u + k) % n + 1) % n ∈ S := hnone ((u + k) % n) hk_n ih
      have hmod : ((u + k) % n + 1) % n = (u + (k + 1)) % n := by
        rw [← Nat.add_assoc, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rwa [← hmod]
  have hsub : Finset.range n ⊆ S := by
    intro v hv
    have hv_n : v < n := Finset.mem_range.mp hv
    have heq : (u + (n - u + v)) % n = v := by
      have hsum : u + (n - u + v) = v + n := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hv_n]
    rw [← heq]
    exact hwalk (n - u + v)
  exact hneq (Finset.Subset.antisymm hS hsub)

/-- Explicit `BoundedConstructExpanderTool` witnessing that `LocalSpannerTools`'s expander
constructor requirement is satisfiable for all `(N_max, W_max)`. -/
theorem exists_boundedConstructExpanderTool (N_max : ℕ) (W_max : ℝ) :
    Nonempty (BoundedConstructExpanderTool N_max W_max) := by
  let Wcap : ℝ := max W_max 1
  have hWcap_pos : 0 < Wcap := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let φ_Const : ℝ := 1 / (6 * Wcap + 1)
  have hφ_pos : 0 < φ_Const := by positivity
  have hφ_le : φ_Const ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  refine ⟨⟨φ_Const, 6, cycleLoopsGraph, hφ_pos, hφ_le, by norm_num, ?_⟩⟩
  intro n w hn _ hw_ge hw_sum
  set W := cycleLoopsGraph n w
  have hvalid := cycleLoopsGraph_isValid n (by omega) w
  have hdeg : ∀ v < n, w v ≤ (W.deg v : ℝ) ∧ (W.deg v : ℝ) ≤ 6 * w v := by
    intro v hv
    rw [cycleLoopsGraph_deg hn w hv]
    have hwv : 1 ≤ w v := hw_ge v hv
    have hle : w v ≤ (Nat.ceil (w v) : ℝ) := Nat.le_ceil _
    have hlt : (Nat.ceil (w v) : ℝ) < w v + 1 := Nat.ceil_lt_add_one (by linarith)
    constructor <;> push_cast <;> linarith
  refine ⟨rfl, hvalid, ?_, hdeg⟩
  intro S hS hne hneq
  have hS_range : S ⊆ Finset.range n := hS
  obtain ⟨i, hi_n, hiS, hi1nS⟩ := cycle_cut_exists (by omega) hS_range hne hneq
  have he_mem : (i, (i + 1) % n) ∈ W.inside W.verts := by
    rw [inside_verts_eq_edges hvalid]
    dsimp only [W, cycleLoopsGraph]
    refine List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi_n, rfl⟩)
  have hcut_pos : 1 ≤ W.cutIn W.verts S := by
    unfold Graph.cutIn
    rw [Nat.succ_le_iff, List.length_pos_iff_exists_mem]
    refine ⟨(i, (i + 1) % n), List.mem_filter.mpr ⟨he_mem, ?_⟩⟩
    simp [hiS, hi1nS]
  have hvol_W : (W.volIn W.verts W.verts : ℝ) ≤ 6 * Wcap := by
    have h1 : W.volIn W.verts W.verts = ∑ v ∈ Finset.range n, W.deg v := rfl
    rw [h1, Nat.cast_sum]
    calc ∑ v ∈ Finset.range n, (W.deg v : ℝ)
        ≤ ∑ v ∈ Finset.range n, 6 * w v := by
            refine Finset.sum_le_sum fun v hv => (hdeg v (Finset.mem_range.mp hv)).2
      _ = 6 * ∑ v ∈ Finset.range n, w v := (Finset.mul_sum _ _ _).symm
      _ ≤ 6 * Wcap := mul_le_mul_of_nonneg_left (le_trans hw_sum (le_max_left _ _)) (by norm_num)
  have hmin_le : min (W.volIn W.verts S : ℝ) (W.volIn W.verts (W.verts \ S) : ℝ) ≤ 6 * Wcap := by
    refine le_trans (min_le_left _ _) ?_
    exact le_trans (by exact_mod_cast volIn_subset_le hS) hvol_W
  have hcut_real : (1 : ℝ) ≤ (W.cutIn W.verts S : ℝ) := by exact_mod_cast hcut_pos
  calc φ_Const * min (W.volIn W.verts S : ℝ) (W.volIn W.verts (W.verts \ S) : ℝ)
      ≤ φ_Const * (6 * Wcap) := mul_le_mul_of_nonneg_left hmin_le hφ_pos.le
    _ = (6 * Wcap) / (6 * Wcap + 1) := by dsimp [φ_Const]; ring
    _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    _ ≤ (W.cutIn W.verts S : ℝ) := hcut_real

end MinCostFlow.Spanner
