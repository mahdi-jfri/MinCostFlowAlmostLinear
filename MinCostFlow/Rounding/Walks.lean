module

public import Mathlib.Data.List.Nodup

/-!
# Multigraph walks and acyclicity

This file defines walks, simple (`Nodup`) walks, and acyclicity for multigraphs that allow
self-loops and parallel edges. Each edge carries an identifier `eid` and endpoints `(u, v)`.

Both the cycle-cancelling lemmas of Kang–Payor Section 3 (`MinCostFlow/Rounding/Rounding.lean`)
and the mathematical dynamic forest of Section 4 (`MinCostFlow/Rounding/Forest.lean`) build on
these lemmas: walk pruning to simple walks, uniqueness of simple paths in a forest, existence of a
leaf in a nonempty forest, acyclicity preservation under `Link`, and path splitting under `Cut`.
-/

@[expose] public section

namespace MinCostFlow.Rounding

/-- A multigraph edge with identifier `eid` and endpoints `u`, `v`. -/
structure RawEdge where
  /-- Edge identifier (unique per edge in an instance or forest). -/
  eid : ℕ
  /-- Tail endpoint. -/
  u : ℕ
  /-- Head endpoint. -/
  v : ℕ
  deriving DecidableEq

namespace RawEdge

/-- Endpoints `(a, b)` are joined by `e` in either orientation. -/
def Connects (e : RawEdge) (a b : ℕ) : Prop :=
  (e.u = a ∧ e.v = b) ∨ (e.u = b ∧ e.v = a)

/-- The other endpoint of `e` when starting at `a`. -/
def other (e : RawEdge) (a : ℕ) : ℕ :=
  if a = e.u then e.v else e.u

theorem connects_symm {e : RawEdge} {a b : ℕ} (h : e.Connects a b) : e.Connects b a := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

theorem other_eq_of_connects {e : RawEdge} {a b : ℕ} (hne : e.u ≠ e.v) (h : e.Connects a b) :
    e.other a = b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [other]
  · simp [other, hne.symm]

end RawEdge

/-- An undirected edge-list walk from `a` to `b` using edges in `edges`. -/
inductive IsWalk (edges : List RawEdge) : ℕ → ℕ → List RawEdge → Prop where
  | nil (a : ℕ) : IsWalk edges a a []
  | cons {a b c : ℕ} {e : RawEdge} {es : List RawEdge} :
      e ∈ edges → e.Connects a b → IsWalk edges b c es → IsWalk edges a c (e :: es)

namespace IsWalk

theorem subset {edges : List RawEdge} {a b : ℕ} {es : List RawEdge}
    (h : IsWalk edges a b es) : ∀ e ∈ es, e ∈ edges := by
  induction h with
  | nil _ => simp
  | cons he _ _ ih =>
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact he
    · exact ih x hx

theorem mono {edges₁ edges₂ : List RawEdge} (hsub : ∀ e ∈ edges₁, e ∈ edges₂)
    {a b : ℕ} {es : List RawEdge} (h : IsWalk edges₁ a b es) : IsWalk edges₂ a b es := by
  induction h with
  | nil a => exact .nil a
  | cons he hc _ ih => exact .cons (hsub _ he) hc ih

theorem mono_of_mem {edges₁ edges₂ : List RawEdge} {a b : ℕ} {es : List RawEdge}
    (h : IsWalk edges₁ a b es) (hsub : ∀ e ∈ es, e ∈ edges₂) : IsWalk edges₂ a b es := by
  induction h with
  | nil a => exact .nil a
  | cons he hc _ ih =>
    exact .cons (hsub _ List.mem_cons_self) hc
      (ih fun x hx => hsub x (List.mem_cons_of_mem _ hx))

theorem append {edges : List RawEdge} {a b c : ℕ} {p q : List RawEdge}
    (hp : IsWalk edges a b p) (hq : IsWalk edges b c q) : IsWalk edges a c (p ++ q) := by
  induction hp with
  | nil _ => exact hq
  | cons he hc _ ih => exact .cons he hc (ih hq)

theorem split_append {edges : List RawEdge} {a c : ℕ} {p q : List RawEdge}
    (h : IsWalk edges a c (p ++ q)) : ∃ b, IsWalk edges a b p ∧ IsWalk edges b c q := by
  induction p generalizing a with
  | nil => exact ⟨a, .nil a, h⟩
  | cons e p ih =>
    cases h with
    | cons he hc hrest =>
      obtain ⟨b, hp, hq⟩ := ih hrest
      exact ⟨b, .cons he hc hp, hq⟩

theorem reverse {edges : List RawEdge} {a b : ℕ} {p : List RawEdge}
    (h : IsWalk edges a b p) : IsWalk edges b a p.reverse := by
  induction h with
  | nil a => exact .nil a
  | cons he hc _ ih =>
    simpa only [List.reverse_cons] using
      ih.append (.cons he (RawEdge.connects_symm hc) (.nil _))

theorem single_iff {edges : List RawEdge} {a b : ℕ} {e : RawEdge} :
    IsWalk edges a b [e] ↔ e ∈ edges ∧ e.Connects a b := by
  constructor
  · intro h
    cases h with
    | cons he hc hnil =>
      cases hnil
      exact ⟨he, hc⟩
  · rintro ⟨he, hc⟩
    exact .cons he hc (.nil _)

theorem cons_iff {edges : List RawEdge} {a c : ℕ} {e : RawEdge} {es : List RawEdge} :
    IsWalk edges a c (e :: es) ↔
      ∃ b, e ∈ edges ∧ e.Connects a b ∧ IsWalk edges b c es := by
  constructor
  · intro h
    cases h with
    | cons he hc hrest => exact ⟨_, he, hc, hrest⟩
  · rintro ⟨b, he, hc, hrest⟩
    exact .cons he hc hrest

theorem nil_iff {edges : List RawEdge} {a c : ℕ} :
    IsWalk edges a c [] ↔ a = c := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil a

theorem verts_lt {edges : List RawEdge} {n : ℕ}
    (hn : ∀ e ∈ edges, e.u < n ∧ e.v < n) {a b : ℕ} {es : List RawEdge}
    (ha : a < n) (h : IsWalk edges a b es) : b < n := by
  induction h with
  | nil _ => exact ha
  | cons he hc _ ih =>
    have ⟨hu, hv⟩ := hn _ he
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ih hv
    · exact ih hu

end IsWalk

/-- If `es` is not `Nodup`, it splits around two occurrences of some element `e`. -/
private theorem exists_split_dup {α : Type*} {es : List α} (h : ¬ es.Nodup) :
    ∃ p e q r, es = p ++ e :: q ++ e :: r := by
  induction es with
  | nil => exact (h List.nodup_nil).elim
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    by_cases hx : x ∈ xs
    · obtain ⟨q, r, rfl⟩ := List.append_of_mem hx
      exact ⟨[], x, q, r, rfl⟩
    · have hxs : ¬ xs.Nodup := fun hnd => h ⟨hx, hnd⟩
      obtain ⟨p, e, q, r, rfl⟩ := ih hxs
      exact ⟨x :: p, e, q, r, rfl⟩

/-- Any walk `es` from `a` to `b` contains a `Nodup` walk from `a` to `b`. -/
theorem exists_nodup_walk_of_walk {edges : List RawEdge} {a b : ℕ} {es : List RawEdge}
    (h : IsWalk edges a b es) :
    ∃ es', IsWalk edges a b es' ∧ es'.Nodup ∧ ∀ e ∈ es', e ∈ es := by
  suffices key : ∀ (k : ℕ) (es : List RawEdge), es.length ≤ k → IsWalk edges a b es →
      ∃ es', IsWalk edges a b es' ∧ es'.Nodup ∧ ∀ e ∈ es', e ∈ es from
    key es.length es (Nat.le_refl _) h
  intro k
  induction k with
  | zero =>
    intro es hlen hw
    have hnil : es = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hnil
    exact ⟨[], hw, List.nodup_nil, by simp⟩
  | succ k ih =>
    intro es hlen hw
    by_cases hnd : es.Nodup
    · exact ⟨es, hw, hnd, fun _ hx => hx⟩
    · obtain ⟨p, e, q, r, rfl⟩ := exists_split_dup hnd
      have hp_split : (p ++ e :: q ++ e :: r) = p ++ (e :: (q ++ e :: r)) := by simp
      rw [hp_split] at hw
      obtain ⟨x₁, hp, hw1⟩ := hw.split_append
      obtain ⟨y₁, he₁, hc₁, hw2⟩ := IsWalk.cons_iff.mp hw1
      obtain ⟨x₂, _, hw3⟩ := hw2.split_append
      obtain ⟨y₂, _, hc₂, hr⟩ := IsWalk.cons_iff.mp hw3
      have hsub_pr : ∀ z ∈ p ++ r, z ∈ (p ++ e :: q ++ e :: r) := by
        intro z hz
        rw [List.mem_append] at hz
        rcases hz with hz | hz
        · simp [hz]
        · simp [hz]
      have hsub_per : ∀ z ∈ p ++ e :: r, z ∈ (p ++ e :: q ++ e :: r) := by
        intro z hz
        rw [List.mem_append, List.mem_cons] at hz
        rcases hz with hz | rfl | hz
        · simp [hz]
        · simp
        · simp [hz]
      have hlen_pr : (p ++ r).length ≤ k := by
        simp only [List.length_append, List.length_cons] at hlen ⊢
        omega
      have hlen_per : (p ++ e :: r).length ≤ k := by
        simp only [List.length_append, List.length_cons] at hlen ⊢
        omega
      rcases hc₁ with ⟨hu1, hv1⟩ | ⟨hu1, hv1⟩ <;> rcases hc₂ with ⟨hu2, hv2⟩ | ⟨hu2, hv2⟩
      · have hy : y₁ = y₂ := hv1.symm.trans hv2
        have hw' : IsWalk edges a b (p ++ e :: r) :=
          hp.append (.cons he₁ (Or.inl ⟨hu1, hv1⟩) (hy ▸ hr))
        obtain ⟨es', hes', hnd', hmem'⟩ := ih (p ++ e :: r) hlen_per hw'
        exact ⟨es', hes', hnd', fun z hz => hsub_per z (hmem' z hz)⟩
      · have hxy : x₁ = y₂ := hu1.symm.trans hu2
        have hw' : IsWalk edges a b (p ++ r) := hp.append (hxy ▸ hr)
        obtain ⟨es', hes', hnd', hmem'⟩ := ih (p ++ r) hlen_pr hw'
        exact ⟨es', hes', hnd', fun z hz => hsub_pr z (hmem' z hz)⟩
      · have hxy : x₁ = y₂ := hv1.symm.trans hv2
        have hw' : IsWalk edges a b (p ++ r) := hp.append (hxy ▸ hr)
        obtain ⟨es', hes', hnd', hmem'⟩ := ih (p ++ r) hlen_pr hw'
        exact ⟨es', hes', hnd', fun z hz => hsub_pr z (hmem' z hz)⟩
      · have hy : y₁ = y₂ := hu1.symm.trans hu2
        have hw' : IsWalk edges a b (p ++ e :: r) :=
          hp.append (.cons he₁ (Or.inr ⟨hu1, hv1⟩) (hy ▸ hr))
        obtain ⟨es', hes', hnd', hmem'⟩ := ih (p ++ e :: r) hlen_per hw'
        exact ⟨es', hes', hnd', fun z hz => hsub_per z (hmem' z hz)⟩

/-- A multigraph edge list is acyclic (forms a forest) if it has no nonempty `Nodup` closed walk.
This forbids self-loops (length 1), parallel edges (length 2), and longer cycles. -/
def IsAcyclic (edges : List RawEdge) : Prop :=
  ∀ a es, IsWalk edges a a es → es.Nodup → es = []

namespace IsAcyclic

theorem mono {edges₁ edges₂ : List RawEdge} (hsub : ∀ e ∈ edges₁, e ∈ edges₂)
    (h : IsAcyclic edges₂) : IsAcyclic edges₁ := by
  intro a es hw hnd
  exact h a es (hw.mono hsub) hnd

theorem no_selfLoop {edges : List RawEdge} (h : IsAcyclic edges) {e : RawEdge} (he : e ∈ edges) :
    e.u ≠ e.v := by
  intro heq
  have hw : IsWalk edges e.u e.u [e] := .cons he (Or.inl ⟨rfl, heq.symm⟩) (.nil _)
  have := h e.u [e] hw (List.nodup_singleton e)
  simp at this

theorem no_parallel {edges : List RawEdge} (h : IsAcyclic edges) {e₁ e₂ : RawEdge}
    (h₁ : e₁ ∈ edges) (h₂ : e₂ ∈ edges) (hne : e₁ ≠ e₂) :
    ¬ e₁.Connects e₂.u e₂.v := by
  intro hc
  have hw : IsWalk edges e₂.u e₂.u [e₁, e₂] :=
    .cons h₁ hc (.cons h₂ (Or.inr ⟨rfl, rfl⟩) (.nil _))
  have hnd : ([e₁, e₂] : List RawEdge).Nodup := by simp [hne]
  have := h e₂.u [e₁, e₂] hw hnd
  simp at this

/-- In an acyclic multigraph, there is at most one `Nodup` walk between any two vertices. -/
theorem walk_unique {edges : List RawEdge} (hacyc : IsAcyclic edges) :
    ∀ {u v : ℕ} {p₁ p₂ : List RawEdge},
      IsWalk edges u v p₁ → p₁.Nodup → IsWalk edges u v p₂ → p₂.Nodup → p₁ = p₂ := by
  intro u v p₁
  induction p₁ generalizing u with
  | nil =>
    intro p₂ hp₁ _ hp₂ hnd₂
    rw [IsWalk.nil_iff] at hp₁
    subst hp₁
    exact (hacyc u p₂ hp₂ hnd₂).symm
  | cons e₁ rest₁ ih =>
    intro p₂ hp₁ hnd₁ hp₂ hnd₂
    obtain ⟨w₁, he₁, hc₁, hrest₁⟩ := IsWalk.cons_iff.mp hp₁
    rw [List.nodup_cons] at hnd₁
    by_cases hmem : e₁ ∈ p₂
    · obtain ⟨a, b, rfl⟩ := List.append_of_mem hmem
      obtain ⟨x, ha, hw_eb⟩ := hp₂.split_append
      obtain ⟨y, _, hc_e₁, hb⟩ := IsWalk.cons_iff.mp hw_eb
      have hnd_a : a.Nodup := hnd₂.of_append_left
      have hnd_b : b.Nodup := (hnd₂.of_append_right).of_cons
      have he₁_not_a : e₁ ∉ a := fun hmem_a =>
        List.disjoint_of_nodup_append hnd₂ hmem_a List.mem_cons_self
      have hxy : (x = u ∧ y = w₁) ∨ (x = w₁ ∧ y = u) := by
        rcases hc₁ with ⟨hu1, hw1⟩ | ⟨hw1, hu1⟩ <;>
          rcases hc_e₁ with ⟨hx, hy⟩ | ⟨hy, hx⟩
        · exact Or.inl ⟨hx.symm.trans hu1, hy.symm.trans hw1⟩
        · exact Or.inr ⟨hx.symm.trans hw1, hy.symm.trans hu1⟩
        · exact Or.inr ⟨hx.symm.trans hw1, hy.symm.trans hu1⟩
        · exact Or.inl ⟨hx.symm.trans hu1, hy.symm.trans hw1⟩
      rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [hx] at ha
        rw [hy] at hb
        have ha_nil : a = [] := hacyc u a ha hnd_a
        subst ha_nil
        have hrest_eq : rest₁ = b := ih hrest₁ hnd₁.2 hb hnd_b
        simp [hrest_eq]
      · rw [hx] at ha
        have hc_rev : IsWalk edges u u (a ++ [e₁]) :=
          ha.append (.cons he₁ hc₁.symm (.nil _))
        have hnd_rev : (a ++ [e₁]).Nodup :=
          List.nodup_append.mpr ⟨hnd_a, List.nodup_singleton _, fun z hz b hb heq => by
            rw [List.mem_singleton] at hb
            subst hb heq
            exact he₁_not_a hz⟩
        have hnil := hacyc u (a ++ [e₁]) hc_rev hnd_rev
        exact absurd hnil (List.append_ne_nil_of_right_ne_nil a (List.cons_ne_nil _ _))
    · have hw_comb : IsWalk edges w₁ u (rest₁ ++ p₂.reverse) :=
        hrest₁.append hp₂.reverse
      obtain ⟨q, hq, hq_nd, hq_mem⟩ := exists_nodup_walk_of_walk hw_comb
      have he₁_not_q : e₁ ∉ q := by
        intro hmq
        have := hq_mem e₁ hmq
        simp only [List.mem_append, List.mem_reverse] at this
        rcases this with h1 | h2
        · exact hnd₁.1 h1
        · exact hmem h2
      have hcyc : IsWalk edges u u (e₁ :: q) := .cons he₁ hc₁ hq
      have hcyc_nd : (e₁ :: q).Nodup := List.nodup_cons.mpr ⟨he₁_not_q, hq_nd⟩
      have := hacyc u (e₁ :: q) hcyc hcyc_nd
      simp at this

end IsAcyclic

private theorem exists_max_len {B : ℕ} (P : ℕ → Prop) (hbound : ∀ k, P k → k ≤ B) :
    ∀ d k, B - k ≤ d → 1 ≤ k → P k → ∃ L, 1 ≤ L ∧ P L ∧ ¬ P (L + 1) := by
  intro d
  induction d with
  | zero =>
    intro k hdk hk1 hk
    refine ⟨k, hk1, hk, fun hsucc => ?_⟩
    have := hbound _ hsucc
    omega
  | succ d ih =>
    intro k hdk hk1 hk
    by_cases hsucc : P (k + 1)
    · have := hbound _ hsucc
      exact ih (k + 1) (by omega) (by omega) hsucc
    · exact ⟨k, hk1, hk, hsucc⟩

/-- Existence of a leaf vertex in any nonempty acyclic multigraph: there is a vertex `v`
incident to a unique edge `e` in `edges`, and `e` is not a self-loop. -/
theorem exists_leaf_of_acyclic {edges : List RawEdge} (hacyc : IsAcyclic edges)
    (hne : edges ≠ []) :
    ∃ v e, e ∈ edges ∧ e.u ≠ e.v ∧ (e.u = v ∨ e.v = v) ∧
      ∀ e' ∈ edges, (e'.u = v ∨ e'.v = v) → e' = e := by
  let HasWalkOfLen (k : ℕ) : Prop :=
    ∃ a b es, IsWalk edges a b es ∧ es.Nodup ∧ es.length = k
  have h1 : HasWalkOfLen 1 := by
    cases edges with
    | nil => exact absurd rfl hne
    | cons e₀ _ =>
      exact ⟨e₀.u, e₀.v, [e₀], .cons List.mem_cons_self (Or.inl ⟨rfl, rfl⟩) (.nil _),
        List.nodup_singleton _, rfl⟩
  have hbound : ∀ k, HasWalkOfLen k → k ≤ edges.length := by
    rintro k ⟨a, b, es, hw, hnd, rfl⟩
    exact hnd.length_le_of_subset hw.subset
  obtain ⟨L, hL_pos, ⟨a, b, es, hw, hnd, hlen⟩, hL_succ⟩ :=
    exists_max_len HasWalkOfLen hbound edges.length 1 (by omega) (Nat.le_refl 1) h1
  have hes_ne : es ≠ [] := by
    intro heq
    subst heq
    simp at hlen
    omega
  obtain ⟨e_last, front, hes_eq⟩ := List.exists_cons_of_ne_nil (by simp [hes_ne] : es.reverse ≠ [])
  have hes_app : es = front.reverse ++ [e_last] := by
    have := congrArg List.reverse hes_eq
    simpa using this
  rw [hes_app] at hw hnd
  obtain ⟨w, hfront, hlast⟩ := hw.split_append
  obtain ⟨he_mem, he_conn⟩ := IsWalk.single_iff.mp hlast
  have he_noloop : e_last.u ≠ e_last.v := hacyc.no_selfLoop he_mem
  have he_inc : e_last.u = b ∨ e_last.v = b := by
    rcases he_conn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  refine ⟨b, e_last, he_mem, he_noloop, he_inc, fun e' he'_mem he'_inc => ?_⟩
  by_contra hne_e
  by_cases he'_in : e' ∈ front.reverse
  · obtain ⟨p, q, hpq⟩ := List.append_of_mem he'_in
    have hfront_eq : front.reverse = p ++ e' :: q := hpq
    rw [hfront_eq] at hfront
    obtain ⟨x, _, hq_rest⟩ := hfront.split_append
    obtain ⟨y, _, hc', hq⟩ := IsWalk.cons_iff.mp hq_rest
    have hnd_pq : (p ++ (e' :: (q ++ [e_last]))).Nodup := by
      simpa [hfront_eq, List.append_assoc] using hnd
    have hnd_eqe : (e' :: (q ++ [e_last])).Nodup := hnd_pq.of_append_right
    have hnd_qe : (q ++ [e_last]).Nodup := hnd_eqe.of_cons
    have hxe : x = b ∨ y = b := by
      rcases hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact he'_inc
      · exact he'_inc.symm
    rcases hxe with rfl | rfl
    · have hcyc : IsWalk edges x x (e' :: (q ++ [e_last])) := by
        simpa [List.append_assoc] using IsWalk.cons he'_mem hc' (hq.append hlast)
      have hzero := hacyc x (e' :: (q ++ [e_last])) hcyc hnd_eqe
      exact absurd hzero (List.cons_ne_nil _ _)
    · have hcyc : IsWalk edges y y (q ++ [e_last]) := hq.append hlast
      have hzero := hacyc y (q ++ [e_last]) hcyc hnd_qe
      exact absurd hzero (List.append_ne_nil_of_right_ne_nil q (List.cons_ne_nil _ _))
  · have he'_not_es : e' ∉ front.reverse ++ [e_last] := by
      simp [he'_in, hne_e]
    let b' := e'.other b
    have hc' : e'.Connects b b' := by
      rcases he'_inc with h1 | h2
      · exact Or.inl ⟨h1, by simp [b', RawEdge.other, h1]⟩
      · have hne' := hacyc.no_selfLoop he'_mem
        have hbne : b ≠ e'.u := fun heq => hne' (heq.symm.trans h2.symm)
        exact Or.inr ⟨by simp [b', RawEdge.other, hbne], h2⟩
    have hw_ext : IsWalk edges a b' ((front.reverse ++ [e_last]) ++ [e']) :=
      hw.append (.cons he'_mem hc' (.nil b'))
    have hnd_ext : ((front.reverse ++ [e_last]) ++ [e']).Nodup :=
      List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, fun z hz b hb heq => by
        rw [List.mem_singleton] at hb
        subst hb heq
        exact he'_not_es hz⟩
    have hlen_front : (front.reverse ++ [e_last]).length = L := by
      rw [← hes_app]
      exact hlen
    have hlen_ext : ((front.reverse ++ [e_last]) ++ [e']).length = L + 1 := by
      rw [List.length_append, hlen_front]
      rfl
    exact hL_succ ⟨a, b', (front.reverse ++ [e_last]) ++ [e'], hw_ext, hnd_ext, hlen_ext⟩

/-- Adding an edge between two disconnected vertices preserves acyclicity. -/
theorem IsAcyclic.link {edges : List RawEdge} (hacyc : IsAcyclic edges) {e : RawEdge}
    (hne : e.u ≠ e.v) (hdisc : ∀ es, ¬ IsWalk edges e.u e.v es) :
    IsAcyclic (e :: edges) := by
  intro a cyc hwalk hnd
  by_cases hmem : e ∈ cyc
  · obtain ⟨p, q, rfl⟩ := List.append_of_mem hmem
    obtain ⟨x, hp, hq_rest⟩ := hwalk.split_append
    obtain ⟨y, _, hc, hq⟩ := IsWalk.cons_iff.mp hq_rest
    have he_not_p : e ∉ p := fun hm =>
      List.disjoint_of_nodup_append hnd hm List.mem_cons_self
    have he_not_q : e ∉ q := (List.nodup_cons.mp hnd.of_append_right).1
    have hqp_mem : ∀ z ∈ q ++ p, z ∈ edges := by
      intro z hz
      have hmem_cyc : z ∈ p ++ e :: q := by
        simp only [List.mem_append, List.mem_cons] at hz ⊢
        rcases hz with hz | hz
        · exact Or.inr (Or.inr hz)
        · exact Or.inl hz
      have := hwalk.subset z hmem_cyc
      simp only [List.mem_cons] at this
      rcases this with rfl | hmem_e
      · simp only [List.mem_append] at hz
        rcases hz with hz | hz
        · exact (he_not_q hz).elim
        · exact (he_not_p hz).elim
      · exact hmem_e
    have hqp_walk : IsWalk edges y x (q ++ p) :=
      (hq.append hp).mono_of_mem hqp_mem
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (hdisc _ hqp_walk.reverse).elim
    · exact (hdisc _ hqp_walk).elim
  · have hsub : ∀ z ∈ cyc, z ∈ edges := by
      intro z hz
      have := hwalk.subset z hz
      simp only [List.mem_cons] at this
      rcases this with rfl | hz'
      · exact (hmem hz).elim
      · exact hz'
    exact hacyc a cyc (hwalk.mono_of_mem hsub) hnd

/-- Cutting an edge `e` on a `Nodup` walk `p = p₁ ++ e :: p₂` from `a` to `b` splits it into
walks `p₁` and `p₂` and disconnects `a` from `b`. -/
theorem IsAcyclic.cut_splits {edges edges' : List RawEdge} (hacyc : IsAcyclic edges)
    (e : RawEdge) (hsub : ∀ z ∈ edges', z ∈ edges) (hno_e : ∀ z ∈ edges', z ≠ e)
    (hkeep : ∀ z ∈ edges, z ≠ e → z ∈ edges')
    {a b : ℕ} {p₁ p₂ : List RawEdge}
    (hp : IsWalk edges a b (p₁ ++ e :: p₂)) (hnd : (p₁ ++ e :: p₂).Nodup) :
    ∃ x y, e.Connects x y ∧ IsWalk edges' a x p₁ ∧ p₁.Nodup ∧
      IsWalk edges' y b p₂ ∧ p₂.Nodup ∧ (∀ q, ¬ IsWalk edges' a b q) := by
  obtain ⟨x, hp₁, hrest⟩ := hp.split_append
  obtain ⟨y, _, hc, hp₂⟩ := IsWalk.cons_iff.mp hrest
  have hnd₁ : p₁.Nodup := hnd.of_append_left
  have hnd₂ : p₂.Nodup := (hnd.of_append_right).of_cons
  have he_not_p₁ : e ∉ p₁ := fun hm =>
    List.disjoint_of_nodup_append hnd hm List.mem_cons_self
  have he_not_p₂ : e ∉ p₂ := (List.nodup_cons.mp hnd.of_append_right).1
  have hp₁' : IsWalk edges' a x p₁ := hp₁.mono_of_mem fun z hz =>
    hkeep z (hp₁.subset z hz) (fun heq => he_not_p₁ (heq ▸ hz))
  have hp₂' : IsWalk edges' y b p₂ := hp₂.mono_of_mem fun z hz =>
    hkeep z (hp₂.subset z hz) (fun heq => he_not_p₂ (heq ▸ hz))
  refine ⟨x, y, hc, hp₁', hnd₁, hp₂', hnd₂, fun q hq => ?_⟩
  obtain ⟨q', hq', hq'_nd, _⟩ := exists_nodup_walk_of_walk hq
  have hq'_edges : IsWalk edges a b q' := hq'.mono hsub
  have heq := hacyc.walk_unique hp hnd hq'_edges hq'_nd
  have he_in_q' : e ∈ q' := by
    rw [← heq]
    simp
  exact hno_e e (hq'.subset e he_in_q') rfl

/-- Vertex sequence visited along a walk starting at `a`. -/
def walkVerts : ℕ → List RawEdge → List ℕ
  | a, [] => [a]
  | a, e :: es => a :: walkVerts (e.other a) es

theorem walkVerts_length (a : ℕ) (es : List RawEdge) :
    (walkVerts a es).length = es.length + 1 := by
  induction es generalizing a with
  | nil => rfl
  | cons e es ih => simp [walkVerts, ih]

private theorem walkVerts_mem_split {edges : List RawEdge} {a b x : ℕ} {es : List RawEdge}
    (hacyc : IsAcyclic edges) (hw : IsWalk edges a b es) (hx : x ∈ walkVerts a es) :
    ∃ p, (∀ z ∈ p, z ∈ es) ∧ p.Nodup ∧ IsWalk edges a x p ∧
      (x ≠ a → p ≠ []) := by
  induction es generalizing a with
  | nil =>
    simp only [walkVerts, List.mem_singleton] at hx
    subst hx
    exact ⟨[], by simp, List.nodup_nil, .nil x, fun h => (h rfl).elim⟩
  | cons e es ih =>
    obtain ⟨w, he, hc, hrest⟩ := IsWalk.cons_iff.mp hw
    have hne := hacyc.no_selfLoop he
    have hw_eq : e.other a = w := RawEdge.other_eq_of_connects hne hc
    simp only [walkVerts, hw_eq, List.mem_cons] at hx
    rcases hx with rfl | hx_tail
    · exact ⟨[], by simp, List.nodup_nil, .nil x, fun h => (h rfl).elim⟩
    · obtain ⟨p, hp_sub, hp_nd, hp_w, _⟩ := ih hrest hx_tail
      by_cases he_in : e ∈ p
      · obtain ⟨q₁, q₂, rfl⟩ := List.append_of_mem he_in
        obtain ⟨z, _, hq₂_rest⟩ := hp_w.split_append
        obtain ⟨z', _, hc₂, hq₂⟩ := IsWalk.cons_iff.mp hq₂_rest
        have hq₂_nd : q₂.Nodup := (hp_nd.of_append_right).of_cons
        have hsub_q₂ : ∀ u ∈ q₂, u ∈ e :: es := fun u hu =>
          List.mem_cons_of_mem _ (hp_sub u (by simp [hu]))
        have he_not_q₂ : e ∉ q₂ := (List.nodup_cons.mp hp_nd.of_append_right).1
        have hzz' : (z = a ∧ z' = w) ∨ (z = w ∧ z' = a) := by
          rcases hc with ⟨ha1, hw1⟩ | ⟨hw1, ha1⟩ <;>
            rcases hc₂ with ⟨hz1, hz2⟩ | ⟨hz2, hz1⟩
          · exact Or.inl ⟨hz1.symm.trans ha1, hz2.symm.trans hw1⟩
          · exact Or.inr ⟨hz1.symm.trans hw1, hz2.symm.trans ha1⟩
          · exact Or.inr ⟨hz1.symm.trans hw1, hz2.symm.trans ha1⟩
          · exact Or.inl ⟨hz1.symm.trans ha1, hz2.symm.trans hw1⟩
        rcases hzz' with ⟨hz_eq, hz'_eq⟩ | ⟨hz_eq, hz'_eq⟩
        · rw [hz'_eq] at hq₂
          exact ⟨e :: q₂, fun u hu => by
            simp only [List.mem_cons] at hu
            rcases hu with rfl | hu
            · exact List.mem_cons_self
            · exact hsub_q₂ u hu,
            List.nodup_cons.mpr ⟨he_not_q₂, hq₂_nd⟩, .cons he hc hq₂, fun _ => List.cons_ne_nil _ _⟩
        · rw [hz'_eq] at hq₂
          exact ⟨q₂, hsub_q₂, hq₂_nd, hq₂, fun hne_xa => by
            intro hnil
            subst hnil
            rw [IsWalk.nil_iff] at hq₂
            exact hne_xa hq₂.symm⟩
      · exact ⟨e :: p, fun u hu => by
          simp only [List.mem_cons] at hu
          rcases hu with rfl | hu
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hp_sub u hu),
          List.nodup_cons.mpr ⟨he_in, hp_nd⟩, .cons he hc hp_w, fun _ => List.cons_ne_nil _ _⟩

theorem IsAcyclic.walkVerts_nodup {edges : List RawEdge} (hacyc : IsAcyclic edges)
    {a b : ℕ} {es : List RawEdge} (hw : IsWalk edges a b es) (hnd : es.Nodup) :
    (walkVerts a es).Nodup := by
  induction es generalizing a with
  | nil => simp [walkVerts]
  | cons e es ih =>
    obtain ⟨w, he, hc, hrest⟩ := IsWalk.cons_iff.mp hw
    rw [List.nodup_cons] at hnd
    have hne := hacyc.no_selfLoop he
    have hw_eq : e.other a = w := RawEdge.other_eq_of_connects hne hc
    simp only [walkVerts, hw_eq, List.nodup_cons]
    refine ⟨fun ha_mem => ?_, ih hrest hnd.2⟩
    obtain ⟨p, hp_sub, hp_nd, hp_w, _⟩ := walkVerts_mem_split hacyc hrest ha_mem
    have he_not_p : e ∉ p := fun hm => hnd.1 (hp_sub e hm)
    have hcyc : IsWalk edges a a (e :: p) := .cons he hc hp_w
    have hcyc_nd : (e :: p).Nodup := List.nodup_cons.mpr ⟨he_not_p, hp_nd⟩
    have := hacyc a (e :: p) hcyc hcyc_nd
    simp at this

theorem IsAcyclic.walk_length_lt {edges : List RawEdge} {n : ℕ} (hacyc : IsAcyclic edges)
    (hn : ∀ e ∈ edges, e.u < n ∧ e.v < n) {a b : ℕ} {es : List RawEdge}
    (ha : a < n) (hw : IsWalk edges a b es) (hnd : es.Nodup) :
    es.length < n := by
  have hnodup := hacyc.walkVerts_nodup hw hnd
  have hsub : walkVerts a es ⊆ List.range n := by
    intro x hx
    rw [List.mem_range]
    obtain ⟨p, _, _, hp_w, _⟩ := walkVerts_mem_split hacyc hw hx
    exact hp_w.verts_lt hn ha
  have hlen := hnodup.length_le_of_subset hsub
  rw [walkVerts_length, List.length_range] at hlen
  omega

end MinCostFlow.Rounding
