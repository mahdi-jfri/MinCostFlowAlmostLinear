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
public import MinCostFlow.Spanner.VacuityCycle

/-!
# Non-Vacuity Witnesses: Reachability

This file continues the material of `Vacuity.lean`, split off to keep files small.
`Vacuity.lean` gives the overview.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Section 2: Reachability, Simple Walks, `DecomposeTool`, and `PathDSTool` -/

def stepReach (G : Graph) (S : Finset ℕ) : Finset ℕ :=
  S ∪ ((G.edges.filter fun e => decide (e.1 ∈ S)).map Prod.snd).toFinset ∪
      ((G.edges.filter fun e => decide (e.2 ∈ S)).map Prod.fst).toFinset

theorem mem_stepReach {G : Graph} {S : Finset ℕ} {x : ℕ} :
    x ∈ stepReach G S ↔ x ∈ S ∨ ∃ e ∈ G.edges, (e.1 ∈ S ∧ e.2 = x) ∨ (e.2 ∈ S ∧ e.1 = x) := by
  simp only [stepReach, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ((h | ⟨e, ⟨he, h1⟩, rfl⟩) | ⟨e, ⟨he, h2⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, he, Or.inl ⟨h1, rfl⟩⟩
    · exact Or.inr ⟨e, he, Or.inr ⟨h2, rfl⟩⟩
  · rintro (h | ⟨e, he, ⟨h1, rfl⟩ | ⟨h2, rfl⟩⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨e, ⟨he, h1⟩, rfl⟩)
    · exact Or.inr ⟨e, ⟨he, h2⟩, rfl⟩

theorem subset_stepReach (G : Graph) (S : Finset ℕ) : S ⊆ stepReach G S :=
  fun _ hx => mem_stepReach.mpr (Or.inl hx)

theorem stepReach_mono (G : Graph) {S T : Finset ℕ} (hST : S ⊆ T) :
    stepReach G S ⊆ stepReach G T := by
  intro x hx
  rw [mem_stepReach] at hx ⊢
  rcases hx with h | ⟨e, he, ⟨h1, rfl⟩ | ⟨h2, rfl⟩⟩
  · exact Or.inl (hST h)
  · exact Or.inr ⟨e, he, Or.inl ⟨hST h1, rfl⟩⟩
  · exact Or.inr ⟨e, he, Or.inr ⟨hST h2, rfl⟩⟩

theorem iter_stepReach_mono (G : Graph) :
    ∀ k {S T : Finset ℕ}, S ⊆ T → (stepReach G)^[k] S ⊆ (stepReach G)^[k] T := by
  intro k
  induction k with
  | zero => intro S T hST; exact hST
  | succ k ih =>
    intro S T hST
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact stepReach_mono G (ih hST)

theorem stepReach_subset_verts {G : Graph} (hG : G.IsValid) {S : Finset ℕ}
    (hS : S ⊆ G.verts) : stepReach G S ⊆ G.verts := by
  intro x hx
  rw [mem_stepReach] at hx
  rcases hx with h | ⟨e, he, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩
  · exact hS h
  · exact Finset.mem_range.mpr (hG e he).2
  · exact Finset.mem_range.mpr (hG e he).1

theorem iter_stepReach_subset_verts {G : Graph} (hG : G.IsValid) {S : Finset ℕ}
    (hS : S ⊆ G.verts) : ∀ k, (stepReach G)^[k] S ⊆ G.verts := by
  intro k
  induction k with
  | zero => exact hS
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact stepReach_subset_verts hG ih

theorem iter_stepReach_fixpoint {G : Graph} (hG : G.IsValid) {u : ℕ} (hu : u < G.n) :
    stepReach G ((stepReach G)^[G.n] {u}) = (stepReach G)^[G.n] {u} := by
  have hu_sub : ({u} : Finset ℕ) ⊆ G.verts := Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr hu)
  have hmono : ∀ k, (stepReach G)^[k] {u} ⊆ (stepReach G)^[k + 1] {u} := by
    intro k
    rw [Function.iterate_succ_apply']
    exact subset_stepReach G _
  by_cases hex : ∃ k < G.n, (stepReach G)^[k + 1] {u} = (stepReach G)^[k] {u}
  · rcases hex with ⟨k, hk, hfix⟩
    have hconst : ∀ m, (stepReach G)^[k + m] {u} = (stepReach G)^[k] {u} := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have hadd : k + (m + 1) = (k + m) + 1 := by omega
        rw [hadd, Function.iterate_succ_apply', ih, ← Function.iterate_succ_apply' (stepReach G) k, hfix]
    have hn1 : G.n = k + (G.n - k) := by omega
    have hn2 : G.n + 1 = k + (G.n - k + 1) := by omega
    rw [← Function.iterate_succ_apply' (stepReach G) G.n {u}, Nat.succ_eq_add_one]
    conv_lhs => rw [hn2]
    conv_rhs => rw [hn1]
    rw [hconst, hconst]
  · push Not at hex
    have hcard : ∀ k ≤ G.n, k + 1 ≤ ((stepReach G)^[k] {u}).card := by
      intro k hk
      induction k with
      | zero => simp
      | succ m ih =>
        have hm_lt : m < G.n := by omega
        have hss : (stepReach G)^[m] {u} ⊂ (stepReach G)^[m + 1] {u} :=
          ssubset_iff_subset_ne.mpr ⟨hmono m, Ne.symm (hex m hm_lt)⟩
        have hlt := Finset.card_lt_card hss
        have := ih (by omega)
        omega
    have hsub : (stepReach G)^[G.n] {u} ⊆ G.verts := iter_stepReach_subset_verts hG hu_sub G.n
    have hle : ((stepReach G)^[G.n] {u}).card ≤ G.n := by
      simpa [Graph.verts, Finset.card_range] using Finset.card_le_card hsub
    have hge := hcard G.n le_rfl
    omega

def compOf (G : Graph) (u : ℕ) : Finset ℕ :=
  (stepReach G)^[G.n] {u}

theorem mem_compOf_self {G : Graph} (u : ℕ) : u ∈ compOf G u := by
  dsimp only [compOf]
  induction G.n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact subset_stepReach G _ ih

theorem compOf_edge_closed {G : Graph} (hG : G.IsValid) {u : ℕ} (hu : u < G.n) :
    ∀ e ∈ G.edges, e.1 ∈ compOf G u ↔ e.2 ∈ compOf G u := by
  intro e he
  have hfix := iter_stepReach_fixpoint hG hu
  dsimp only [compOf]
  constructor <;> intro hmem
  · rw [← hfix, mem_stepReach]
    exact Or.inr ⟨e, he, Or.inl ⟨hmem, rfl⟩⟩
  · rw [← hfix, mem_stepReach]
    exact Or.inr ⟨e, he, Or.inr ⟨hmem, rfl⟩⟩

theorem iter_stepReach_subset_iter_stepReach {G : Graph} {S : Finset ℕ} :
    ∀ k₁ k₂, k₁ ≤ k₂ → (stepReach G)^[k₁] S ⊆ (stepReach G)^[k₂] S := by
  intro k₁ k₂ hle
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, Function.iterate_succ_apply']
    exact Finset.Subset.trans ih (subset_stepReach G _)

theorem iter_stepReach_of_mem_iter {G : Graph} {S : Finset ℕ} {x : ℕ} (hx : x ∈ S) :
    ∀ k, x ∈ (stepReach G)^[k] S := by
  intro k
  exact iter_stepReach_subset_iter_stepReach 0 k (Nat.zero_le k) hx

theorem mem_iter_stepReach_of_walk {G : Graph} (hG : G.IsValid) :
    ∀ (k u v : ℕ) (S : Finset ℕ), u ∈ S →
      (∃ P : Walk, P.IsWalk G u v ∧ P.edges.length ≤ k) →
      v ∈ (stepReach G)^[k] S := by
  intro k
  induction k with
  | zero =>
    intro u v S hu ⟨P, hP, hlen0⟩
    rw [Nat.le_zero] at hlen0
    rcases hP with ⟨_, _, ⟨_, _, rfl⟩ | ⟨hne, _⟩⟩
    · simpa using hu
    · exact absurd (List.length_eq_zero_iff.mp hlen0) hne
  | succ k ih =>
    intro u v S hu ⟨P, hP, hlen⟩
    rcases P with ⟨vs, es⟩
    rcases hP with ⟨_, hv_lt, ⟨_, hPe, rfl⟩ | ⟨hne, hlenv, hhead, hlast, hedges, hstep⟩⟩
    · simp only [Function.iterate_succ_apply]
      have : u ∈ stepReach G S := subset_stepReach G S hu
      exact iter_stepReach_of_mem_iter this k
    · cases es with
      | nil => contradiction
      | cons j js =>
        cases vs with
        | nil => simp at hhead
        | cons u' vs' =>
          cases vs' with
          | nil => simp at hlenv
          | cons w vs'' =>
            simp only [List.head?_cons, Option.some.injEq] at hhead
            subst hhead
            have hj_m : j < G.m := hedges j List.mem_cons_self
            have hj_mem : G.edges[j]'hj_m ∈ G.edges := List.getElem_mem hj_m
            have hstep0 := hstep 0 (by simp)
            simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
              List.getElem?_cons_succ, Option.getD_some] at hstep0
            rw [← List.getD_eq_getElem?_getD, List.getD_eq_getElem _ _ hj_m] at hstep0
            have hw_step : w ∈ stepReach G S := by
              rw [mem_stepReach]
              rcases hstep0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact Or.inr ⟨G.edges[j]'hj_m, hj_mem, Or.inl ⟨by rw [h1]; exact hu, h2⟩⟩
              · exact Or.inr ⟨G.edges[j]'hj_m, hj_mem, Or.inr ⟨by rw [h1]; exact hu, h2⟩⟩
            have hw_lt : w < G.n := by
              rcases hstep0 with ⟨_, h2⟩ | ⟨_, h1⟩
              · exact h2 ▸ (hG _ hj_mem).2
              · exact h1 ▸ (hG _ hj_mem).1
            cases js with
            | nil =>
              cases vs'' with
              | nil =>
                simp only [List.getLast?_singleton, List.getLast?_cons_cons,
                  Option.some.injEq] at hlast
                rw [Function.iterate_succ_apply]
                exact iter_stepReach_of_mem_iter (by rw [← hlast]; exact hw_step) k
              | cons _ _ => simp at hlenv
            | cons j2 js2 =>
              have htail_walk : (⟨w :: vs'', j2 :: js2⟩ : Walk).IsWalk G w v := by
                refine ⟨hw_lt, hv_lt, Or.inr ⟨List.cons_ne_nil _ _, by simpa using hlenv,
                  rfl, ?_, fun m hm => hedges m (List.mem_cons_of_mem j hm), fun i hi => ?_⟩⟩
                · simpa [List.getLast?_cons_cons] using hlast
                · have := hstep (i + 1) (by simpa using Nat.succ_lt_succ hi)
                  simpa [List.getD_eq_getElem?_getD] using this
              have htail_len : (⟨w :: vs'', j2 :: js2⟩ : Walk).edges.length ≤ k := by
                simpa using Nat.le_of_succ_le_succ hlen
              rw [Function.iterate_succ_apply]
              exact ih w v (stepReach G S) hw_step ⟨⟨w :: vs'', j2 :: js2⟩, htail_walk, htail_len⟩

theorem walk_of_mem_iter_stepReach {G : Graph} (hG : G.IsValid) {u : ℕ} (hu : u < G.n) :
    ∀ k v, v ∈ (stepReach G)^[k] {u} → ∃ P : Walk, P.IsWalk G u v ∧ P.edges.length ≤ k := by
  intro k
  induction k with
  | zero =>
    intro v hv
    simp only [Function.iterate_zero, id_eq, Finset.mem_singleton] at hv
    subst hv
    exact ⟨Walk.empty, ⟨hu, hu, Or.inl ⟨rfl, rfl, rfl⟩⟩, le_rfl⟩
  | succ k ih =>
    intro v hv
    rw [Function.iterate_succ_apply', mem_stepReach] at hv
    rcases hv with hprev | ⟨e, he, ⟨h1, rfl⟩ | ⟨h2, rfl⟩⟩
    · obtain ⟨P, hP, hlen⟩ := ih v hprev
      exact ⟨P, hP, Nat.le_succ_of_le hlen⟩
    · obtain ⟨j, hj_lt, rfl⟩ := List.mem_iff_getElem.mp he
      obtain ⟨P, hP, hlen⟩ := ih (G.edges[j]'hj_lt).1 h1
      have hv1 := (hG _ he).1
      have hv2 := (hG _ he).2
      have hstep : (Walk.single (G.edges[j]'hj_lt).1 (G.edges[j]'hj_lt).2 j).IsWalk G
          (G.edges[j]'hj_lt).1 (G.edges[j]'hj_lt).2 := by
        refine Walk.isWalk_single hv1 hv2 hj_lt ?_
        rw [List.getD_eq_getElem _ _ hj_lt]
        exact Or.inl ⟨rfl, rfl⟩
      refine ⟨P.append (Walk.single _ _ j), Walk.isWalk_append hP hstep, ?_⟩
      rw [Walk.edges_append, List.length_append]
      simp [Walk.single]
      omega
    · obtain ⟨j, hj_lt, rfl⟩ := List.mem_iff_getElem.mp he
      obtain ⟨P, hP, hlen⟩ := ih (G.edges[j]'hj_lt).2 h2
      have hv1 := (hG _ he).1
      have hv2 := (hG _ he).2
      have hstep : (Walk.single (G.edges[j]'hj_lt).2 (G.edges[j]'hj_lt).1 j).IsWalk G
          (G.edges[j]'hj_lt).2 (G.edges[j]'hj_lt).1 := by
        refine Walk.isWalk_single hv2 hv1 hj_lt ?_
        rw [List.getD_eq_getElem _ _ hj_lt]
        exact Or.inr ⟨rfl, rfl⟩
      refine ⟨P.append (Walk.single _ _ j), Walk.isWalk_append hP hstep, ?_⟩
      rw [Walk.edges_append, List.length_append]
      simp [Walk.single]
      omega

theorem exists_dup_indices {α : Type*} (l : List α) (h : ¬ l.Nodup) :
    ∃ i j, i < j ∧ ∃ hi : i < l.length, ∃ hj : j < l.length, l[i]'hi = l[j]'hj := by
  induction l with
  | nil => simp at h
  | cons a xs ih =>
    rw [List.nodup_cons] at h
    by_cases ha : a ∈ xs
    · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
      exact ⟨0, k + 1, Nat.zero_lt_succ k, by simp, Nat.succ_lt_succ hk, rfl⟩
    · have hxs : ¬ xs.Nodup := fun hn => h ⟨ha, hn⟩
      obtain ⟨i, j, hij, hi, hj, heq⟩ := ih hxs
      exact ⟨i + 1, j + 1, Nat.succ_lt_succ hij, Nat.succ_lt_succ hi, Nat.succ_lt_succ hj, heq⟩

theorem walk_shortcut {G : Graph} {u v : ℕ} {P : Walk}
    (hP : P.IsWalk G u v) (hdup : ¬ P.verts.Nodup) :
    ∃ Q : Walk, Q.IsWalk G u v ∧ Q.edges.length < P.edges.length := by
  rcases hP with ⟨hu, hv, ⟨hPv, _, _⟩ | ⟨hne, hlen, hhead, hlast, hedges, hstep⟩⟩
  · simp [hPv] at hdup
  obtain ⟨i, j, hij, hi_v, hj_v, heq_v⟩ := exists_dup_indices P.verts hdup
  have hpos_e : 0 < P.edges.length := List.length_pos_of_ne_nil hne
  by_cases hfull : i = 0 ∧ j = P.edges.length
  · have hu_eq_i : P.verts[0]'(by omega) = u := by
      have hh := List.head?_eq_getElem? (l := P.verts)
      rw [hhead, List.getElem?_eq_getElem (by omega)] at hh
      exact Option.some.inj hh.symm
    have hv_eq_j : P.verts[P.edges.length]'(by omega) = v := by
      have hl := List.getLast?_eq_getElem? (l := P.verts)
      rw [hlast, hlen, Nat.add_sub_cancel, List.getElem?_eq_getElem (by omega)] at hl
      exact Option.some.inj hl.symm
    have huv : u = v := by
      have h0i : P.verts[0]'(by omega) = P.verts[i]'hi_v := by congr 1; exact hfull.1.symm
      have hj_e : P.verts[j]'hj_v = P.verts[P.edges.length]'(by omega) := by congr 1; exact hfull.2
      rw [← hu_eq_i, ← hv_eq_j, h0i, heq_v, hj_e]
    exact ⟨Walk.empty, ⟨hu, hv, Or.inl ⟨rfl, rfl, huv⟩⟩, hpos_e⟩
  · let vs' := P.verts.take (i + 1) ++ P.verts.drop (j + 1)
    let es' := P.edges.take i ++ P.edges.drop j
    have htake_v : (P.verts.take (i + 1)).length = i + 1 := by simp; omega
    have hdrop_v : (P.verts.drop (j + 1)).length = P.verts.length - (j + 1) := by simp
    have htake_e : (P.edges.take i).length = i := by simp; omega
    have hdrop_e : (P.edges.drop j).length = P.edges.length - j := by simp
    have hvs'_len : vs'.length = es'.length + 1 := by
      dsimp only [vs', es']
      rw [List.length_append, List.length_append, htake_v, hdrop_v, htake_e, hdrop_e]
      omega
    have hes'_lt : es'.length < P.edges.length := by
      dsimp only [es']
      rw [List.length_append, htake_e, hdrop_e]
      omega
    have hes'_ne : es' ≠ [] := by
      intro hnil
      have hlen0 : es'.length = 0 := by simp [hnil]
      dsimp only [es'] at hlen0
      rw [List.length_append, htake_e, hdrop_e] at hlen0
      omega
    have hhead' : vs'.head? = some u := by
      dsimp only [vs']
      have hnt : P.verts.take (i + 1) ≠ [] := by
        intro hnil
        have hlen_nil := congrArg List.length hnil
        simp only [List.length_take, List.length_nil] at hlen_nil
        omega
      rw [List.head?_append_of_ne_nil _ hnt]
      cases hPv : P.verts with
      | nil => simp [hPv] at hhead
      | cons x xs => simp [hPv] at hhead ⊢; exact hhead
    have hlast' : vs'.getLast? = some v := by
      dsimp only [vs']
      by_cases hdrop_ne : P.verts.drop (j + 1) = []
      · have hj_last : j = P.edges.length := by
          have := List.drop_eq_nil_iff.mp hdrop_ne
          omega
        rw [hdrop_ne, List.append_nil, List.getLast?_eq_getElem?, htake_v, Nat.add_sub_cancel,
            List.getElem?_take_of_lt (Nat.lt_succ_self i), List.getElem?_eq_getElem hi_v]
        have hl := List.getLast?_eq_getElem? (l := P.verts)
        rw [hlast, hlen, Nat.add_sub_cancel, List.getElem?_eq_getElem (by omega)] at hl
        have hj_eq : P.verts[i]'hi_v = P.verts[P.edges.length]'(by omega) := by
          rw [heq_v]; congr 1
        rw [hj_eq]
        exact hl.symm
      · rw [List.getLast?_append_of_ne_nil _ hdrop_ne]
        have hdl : 0 < (P.verts.drop (j + 1)).length := List.length_pos_of_ne_nil hdrop_ne
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega : (P.verts.drop (j + 1)).length - 1 < (P.verts.drop (j + 1)).length), List.getElem_drop]
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
        rw [← hlast]
        congr 2; rw [hdrop_v]; omega
    have hedges' : ∀ m ∈ es', m < G.m := by
      intro m hm
      dsimp only [es'] at hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · exact hedges m (List.mem_of_mem_take hm)
      · exact hedges m (List.mem_of_mem_drop hm)
    have hstep' : ∀ k < es'.length, Walk.EdgeMatches (G.edges.getD (es'.getD k 0) (0, 0))
        (vs'.getD k 0) (vs'.getD (k + 1) 0) := by
      intro k hk
      have hvk_len : k < vs'.length := by rw [hvs'_len]; omega
      have hvk1_len : k + 1 < vs'.length := by rw [hvs'_len]; omega
      by_cases hki : k < i
      · have hek : es'.getD k 0 = P.edges.getD k 0 := by
          rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ (by omega : k < P.edges.length)]
          dsimp only [es']
          rw [List.getElem_append_left (by omega), List.getElem_take]
        have hvk1 : vs'.getD k 0 = P.verts.getD k 0 := by
          rw [List.getD_eq_getElem _ _ hvk_len, List.getD_eq_getElem _ _ (by omega : k < P.verts.length)]
          dsimp only [vs']
          rw [List.getElem_append_left (by omega), List.getElem_take]
        have hvk2 : vs'.getD (k + 1) 0 = P.verts.getD (k + 1) 0 := by
          rw [List.getD_eq_getElem _ _ hvk1_len, List.getD_eq_getElem _ _ (by omega : k + 1 < P.verts.length)]
          dsimp only [vs']
          rw [List.getElem_append_left (by omega), List.getElem_take]
        rw [hek, hvk1, hvk2]
        exact hstep k (by omega)
      · have hik : i ≤ k := Nat.le_of_not_lt hki
        let m := j + (k - i)
        have hm_lt : m < P.edges.length := by
          have : es'.length = i + (P.edges.length - j) := by
            dsimp only [es']; rw [List.length_append, htake_e, hdrop_e]
          omega
        have hek : es'.getD k 0 = P.edges.getD m 0 := by
          rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hm_lt]
          dsimp only [es']
          rw [List.getElem_append_right (by omega)]
          simp only [htake_e, List.getElem_drop]
          congr 1
        have hvk1 : vs'.getD k 0 = P.verts.getD m 0 := by
          rw [List.getD_eq_getElem _ _ hvk_len, List.getD_eq_getElem _ _ (by omega : m < P.verts.length)]
          by_cases hkeq : k = i
          · subst hkeq
            dsimp only [vs']
            rw [List.getElem_append_left (by omega), List.getElem_take]
            dsimp only [m]; simp only [Nat.sub_self, Nat.add_zero]
            exact heq_v
          · dsimp only [vs']
            rw [List.getElem_append_right (by omega)]
            simp only [htake_v, List.getElem_drop]
            congr 1; omega
        have hvk2 : vs'.getD (k + 1) 0 = P.verts.getD (m + 1) 0 := by
          rw [List.getD_eq_getElem _ _ hvk1_len, List.getD_eq_getElem _ _ (by omega : m + 1 < P.verts.length)]
          dsimp only [vs']
          rw [List.getElem_append_right (by omega)]
          simp only [htake_v, List.getElem_drop]
          congr 1; omega
        rw [hek, hvk1, hvk2]
        exact hstep m hm_lt
    exact ⟨⟨vs', es'⟩, ⟨hu, hv, Or.inr ⟨hes'_ne, hvs'_len, hhead', hlast', hedges', hstep'⟩⟩, hes'_lt⟩

theorem exists_simple_walk_of_walk {G : Graph} {u v : ℕ} {P : Walk}
    (hP : P.IsWalk G u v) : ∃ Q : Walk, Q.IsWalk G u v ∧ Q.verts.Nodup := by
  classical
  have hex : ∃ n, ∃ Q : Walk, Q.IsWalk G u v ∧ Q.edges.length = n := ⟨P.edges.length, P, hP, rfl⟩
  let n₀ := Nat.find hex
  obtain ⟨Q, hQ, hlen⟩ := Nat.find_spec hex
  refine ⟨Q, hQ, ?_⟩
  by_contra hdup
  obtain ⟨Q', hQ', hlt⟩ := walk_shortcut hQ hdup
  exact Nat.find_min hex (by rw [← hlen]; exact hlt) ⟨Q', hQ', rfl⟩

theorem walk_nodup_length_le {G : Graph} (hG : G.IsValid) {u v : ℕ} {Q : Walk}
    (hQ : Q.IsWalk G u v) (hnodup : Q.verts.Nodup) : Q.edges.length ≤ G.n := by
  have hsub : Q.verts.toFinset ⊆ G.verts := by
    intro x hx
    exact Finset.mem_range.mpr (Walk.isWalk_verts_lt hG hQ x (List.mem_toFinset.mp hx))
  have hcard : Q.verts.length ≤ G.n := by
    rw [← List.toFinset_card_of_nodup hnodup]
    simpa [Graph.verts, Finset.card_range] using Finset.card_le_card hsub
  rcases hQ.2.2 with ⟨_, hPe, _⟩ | ⟨_, hlen, _⟩
  · simp [hPe]
  · omega

theorem mem_compOf_iff_walk {G : Graph} (hG : G.IsValid) {u v : ℕ} (hu : u < G.n) :
    v ∈ compOf G u ↔ ∃ P : Walk, P.IsWalk G u v := by
  constructor
  · intro hv
    obtain ⟨P, hP, _⟩ := walk_of_mem_iter_stepReach hG hu G.n v hv
    exact ⟨P, hP⟩
  · rintro ⟨P, hP⟩
    obtain ⟨Q, hQ, hnodup⟩ := exists_simple_walk_of_walk hP
    have hlen := walk_nodup_length_le hG hQ hnodup
    exact mem_iter_stepReach_of_walk hG G.n u v {u} (Finset.mem_singleton_self u) ⟨Q, hQ, hlen⟩

theorem compOf_eq_of_mem {G : Graph} (hG : G.IsValid) {u v : ℕ}
    (hu : u < G.n) (hv : v < G.n) (hmem : v ∈ compOf G u) : compOf G v = compOf G u := by
  obtain ⟨P, hP⟩ := (mem_compOf_iff_walk hG hu).mp hmem
  ext w
  rw [mem_compOf_iff_walk hG hv, mem_compOf_iff_walk hG hu]
  exact ⟨fun ⟨Q, hQ⟩ => ⟨P.append Q, Walk.isWalk_append hP hQ⟩,
         fun ⟨Q, hQ⟩ => ⟨P.reverse.append Q, Walk.isWalk_append (Walk.isWalk_reverse hP) hQ⟩⟩

theorem list_exists_adj_crossing (vs : List ℕ) (S : Finset ℕ) (a b : ℕ)
    (hhead : vs.head? = some a) (hlast : vs.getLast? = some b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ i, i + 1 < vs.length ∧ vs.getD i 0 ∈ S ∧ vs.getD (i + 1) 0 ∉ S := by
  induction vs generalizing a with
  | nil => simp at hhead
  | cons x xs ih =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases xs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      exact absurd (hlast ▸ ha) hb
    | cons y ys =>
      by_cases hy : y ∈ S
      · have hlast' : (y :: ys).getLast? = some b := by simpa [List.getLast?_cons_cons] using hlast
        obtain ⟨i, hi_len, hi1, hi2⟩ := ih y rfl hlast' hy
        refine ⟨i + 1, by simpa using Nat.succ_lt_succ hi_len, ?_, ?_⟩
        · simpa [List.getD_eq_getElem?_getD] using hi1
        · simpa [List.getD_eq_getElem?_getD] using hi2
      · exact ⟨0, by simp, by simp [List.getD_eq_getElem?_getD, ha], by simp [List.getD_eq_getElem?_getD, hy]⟩

theorem cut_pos_of_mem_compOf {G : Graph} (hG : G.IsValid) {u : ℕ} (hu : u < G.n)
    {S : Finset ℕ} (hS : S ⊆ compOf G u) (hne : S.Nonempty) (hneq : S ≠ compOf G u) :
    1 ≤ G.cutIn (compOf G u) S := by
  rcases hne with ⟨a, haS⟩
  have ha_comp : a ∈ compOf G u := hS haS
  have ha_n : a < G.n := Finset.mem_range.mp (iter_stepReach_subset_verts hG
    (Finset.singleton_subset_iff.mpr (Finset.mem_range.mpr hu)) G.n ha_comp)
  have hex_b : ∃ b ∈ compOf G u, b ∉ S := by
    by_contra hnone
    push Not at hnone
    exact hneq (Finset.Subset.antisymm hS hnone)
  rcases hex_b with ⟨b, hb_comp, hb_nS⟩
  have hcomp_a : compOf G a = compOf G u := compOf_eq_of_mem hG hu ha_n ha_comp
  have hb_a : b ∈ compOf G a := hcomp_a ▸ hb_comp
  obtain ⟨P, hP⟩ := (mem_compOf_iff_walk hG ha_n).mp hb_a
  rcases hP with ⟨_, _, ⟨_, hPe, rfl⟩ | ⟨hneP, hlen, hhead, hlast, hedges, hstep⟩⟩
  · exact absurd haS hb_nS
  · obtain ⟨i, hi_v, hiS, hi1nS⟩ := list_exists_adj_crossing P.verts S a b hhead hlast haS hb_nS
    have hi_e : i < P.edges.length := by omega
    let j := P.edges.getD i 0
    have hj_mem : j ∈ P.edges := by
      dsimp only [j]
      rw [List.getD_eq_getElem _ _ hi_e]
      exact List.getElem_mem hi_e
    have hj_m : j < G.m := hedges j hj_mem
    have hmatch : Walk.EdgeMatches (G.edges.getD j (0, 0)) (P.verts.getD i 0)
        (P.verts.getD (i + 1) 0) := hstep i hi_e
    have he_mem : G.edges.getD j (0, 0) ∈ G.edges := by
      rw [List.getD_eq_getElem _ _ hj_m]; exact List.getElem_mem hj_m
    have hclosed := compOf_edge_closed hG hu _ he_mem
    have hu_in_comp : P.verts.getD i 0 ∈ compOf G u := hS hiS
    have hboth_in_X : (G.edges.getD j (0, 0)).1 ∈ compOf G u ∧
        (G.edges.getD j (0, 0)).2 ∈ compOf G u := by
      rcases hmatch with ⟨h1, _⟩ | ⟨h1, _⟩
      · have h1' : (G.edges.getD j (0, 0)).1 ∈ compOf G u := by rw [h1]; exact hu_in_comp
        exact ⟨h1', hclosed.mp h1'⟩
      · have h2' : (G.edges.getD j (0, 0)).2 ∈ compOf G u := by rw [h1]; exact hu_in_comp
        exact ⟨hclosed.mpr h2', h2'⟩
    have hins : G.edges.getD j (0, 0) ∈ G.inside (compOf G u) := by
      rw [Graph.inside, List.mem_filter]
      exact ⟨he_mem, by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hboth_in_X⟩
    have hdiff : (decide ((G.edges.getD j (0, 0)).1 ∈ S) !=
        decide ((G.edges.getD j (0, 0)).2 ∈ S)) = true := by
      rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; simp only [hiS, hi1nS]; decide
      · rw [h1, h2]; simp only [hiS, hi1nS]; decide
    unfold Graph.cutIn
    rw [Nat.succ_le_iff, List.length_pos_iff_exists_mem]
    exact ⟨G.edges.getD j (0, 0), List.mem_filter.mpr ⟨hins, hdiff⟩⟩

end MinCostFlow.Spanner
