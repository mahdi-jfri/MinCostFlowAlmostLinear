module

public import MinCostFlow.Statement.Problem
public import MinCostFlow.Rounding.Walks
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Cycle-cancelling rounding lemmas (Kang–Payor Section 3)

This file formalizes Section 3 of D. Kang and J. Payor, *Flow Rounding* (arXiv:1507.08139v1,
pages 4–5), adapted directly to feasible flows of a min-cost flow `Instance`
(`MinCostFlow/Statement/Problem.lean`) with integral vertex demands and integral lower/upper
capacities.

Rather than adding a dummy vertex and fixed-flow edges as in Section 2.2 of the source, we prove
Lemmas 3.1–3.3 and the costed cycle-cancelling step directly for flows routing integral demands:
since the demands `I.d v` are integers, any leaf vertex incident to a single fractional edge still
forces that edge's flow to be integral, and self-loops and parallel edges are excluded by
multigraph acyclicity (`IsAcyclic`).
-/

@[expose] public section

namespace MinCostFlow.Rounding

/-- A flow `f` is integral if every edge carries an integer amount of flow. -/
def IsIntegral {I : Instance} (f : Fin I.m → ℝ) : Prop :=
  ∀ j : Fin I.m, ∃ z : ℤ, f j = z

/-- The `RawEdge` corresponding to edge index `j` of `I`. -/
def rawEdge (I : Instance) (j : Fin I.m) : RawEdge :=
  ⟨j.1, (I.edge j).tail, (I.edge j).head⟩

/-- The list of fractional edges of `f` in `I`, represented as `RawEdge`s. -/
noncomputable def fracEdges (I : Instance) (f : Fin I.m → ℝ) : List RawEdge :=
  letI := Classical.propDecidable
  (List.finRange I.m).filterMap fun j =>
    if ∃ z : ℤ, f j = z then none else some (rawEdge I j)

theorem mem_fracEdges_iff {I : Instance} {f : Fin I.m → ℝ} {e : RawEdge} :
    e ∈ fracEdges I f ↔ ∃ j : Fin I.m, e = rawEdge I j ∧ ¬ ∃ z : ℤ, f j = z := by
  classical
  unfold fracEdges
  simp only [List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, hj⟩
    split_ifs at hj with h
    simp only [Option.some.injEq] at hj
    exact ⟨j, hj.symm, h⟩
  · rintro ⟨j, rfl, hj⟩
    refine ⟨j, ?_⟩
    simp [hj]

/-- Forward availability of edge `j` from initial flow `f` to current flow `f'`:
`⌈f_j⌉ - f'_j` (Kang–Payor Section 3.1). -/
noncomputable def availFwd {I : Instance} (f f' : Fin I.m → ℝ) (j : Fin I.m) : ℝ :=
  (⌈f j⌉ : ℝ) - f' j

/-- Backward availability of edge `j` from initial flow `f` to current flow `f'`:
`f'_j - ⌊f_j⌋`, matching `⌈-f_j⌉ - (-f'_j)` in Kang–Payor Section 3.1. -/
noncomputable def availBwd {I : Instance} (f f' : Fin I.m → ℝ) (j : Fin I.m) : ℝ :=
  f' j - (⌊f j⌋ : ℝ)

theorem availBwd_eq_neg_availFwd {I : Instance} (f f' : Fin I.m → ℝ) (j : Fin I.m) :
    availBwd f f' j = (⌈-f j⌉ : ℝ) - (-f' j) := by
  simp only [availBwd, Int.ceil_neg, Int.cast_neg]
  ring

/-- Helper: if `e.b v * x` is an integer whenever `x` is integral or `e` is not incident to `v`. -/
private theorem edge_b_mul_int_of_mem {e : Edge} {v : ℕ} {x : ℝ} (z : ℤ) (hx : x = z) :
    ∃ k : ℤ, e.b v * x = k := by
  subst hx
  simp only [Edge.b]
  split_ifs with h1 h2
  · exact ⟨0, by norm_num⟩
  · exact ⟨z, by norm_num⟩
  · exact ⟨-z, by norm_num⟩
  · exact ⟨0, by norm_num⟩

/-- **Kang–Payor Lemma 3.1** (arXiv:1507.08139v1, Section 3.1, extended directly to flows routing
integral demands on an `Instance`): if `f` routes integral demands and the subgraph of all
fractional edges forms a forest (`IsAcyclic`), then `f` is integral. -/
theorem lemma_3_1 {I : Instance} (hValid : I.IsValid) {f : Fin I.m → ℝ}
    (hRoutes : I.Routes f) (hForest : IsAcyclic (fracEdges I f)) :
    IsIntegral f := by
  classical
  by_contra hnot
  unfold IsIntegral at hnot
  push Not at hnot
  obtain ⟨j_ex, hj_ex⟩ := hnot
  have hne : fracEdges I f ≠ [] := by
    intro hnil
    have hmem : rawEdge I j_ex ∈ fracEdges I f :=
      mem_fracEdges_iff.mpr ⟨j_ex, rfl, fun ⟨z, hz⟩ => hj_ex z hz⟩
    rw [hnil] at hmem
    simp at hmem
  obtain ⟨v, e, he_mem, he_noloop, he_inc, he_uniq⟩ := exists_leaf_of_acyclic hForest hne
  obtain ⟨j₀, rfl, hj₀_frac⟩ := mem_fracEdges_iff.mp he_mem
  have hv_lt : v < I.n := by
    have hmem_e : I.edge j₀ ∈ I.edges := List.getElem_mem j₀.2
    have ⟨ht, hh⟩ := hValid.1 (I.edge j₀) hmem_e
    dsimp [rawEdge] at he_inc
    rcases he_inc with h1 | h2
    · rw [← h1]; exact ht
    · rw [← h2]; exact hh
  let vFin : Fin I.n := ⟨v, hv_lt⟩
  have hcons := hRoutes vFin
  have hother_int : ∀ j ∈ Finset.univ.erase j₀, ∃ k : ℤ, (I.edge j).b v * f j = k := by
    intro j hj
    have hj_ne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
    by_cases hfj : ∃ z : ℤ, f j = z
    · obtain ⟨z, hz⟩ := hfj
      exact edge_b_mul_int_of_mem z hz
    · have hj_mem : rawEdge I j ∈ fracEdges I f := mem_fracEdges_iff.mpr ⟨j, rfl, hfj⟩
      have hnot_inc : ¬ ((rawEdge I j).u = v ∨ (rawEdge I j).v = v) := by
        intro hinc
        have heq := he_uniq (rawEdge I j) hj_mem hinc
        have heid : j.1 = j₀.1 := congrArg RawEdge.eid heq
        exact hj_ne (Fin.ext heid)
      have htail : v ≠ (I.edge j).tail := fun h => hnot_inc (Or.inl h.symm)
      have hhead : v ≠ (I.edge j).head := fun h => hnot_inc (Or.inr h.symm)
      exact ⟨0, by simp [Edge.b, htail, hhead]⟩
  have hsum_int : ∃ S : ℤ,
      ∑ j ∈ Finset.univ.erase j₀, (I.edge j).b v * f j = (S : ℝ) := by
    have : ∀ s : Finset (Fin I.m), (∀ j ∈ s, ∃ k : ℤ, (I.edge j).b v * f j = k) →
        ∃ S : ℤ, ∑ j ∈ s, (I.edge j).b v * f j = (S : ℝ) := by
      intro s hs
      induction s using Finset.induction_on with
      | empty => exact ⟨0, by simp⟩
      | @insert a s ha ih =>
        obtain ⟨ka, hka⟩ := hs a (Finset.mem_insert_self a s)
        obtain ⟨Ks, hKs⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
        refine ⟨ka + Ks, ?_⟩
        rw [Finset.sum_insert ha, hka, hKs, Int.cast_add]
    exact this (Finset.univ.erase j₀) hother_int
  obtain ⟨S, hS⟩ := hsum_int
  have hsplit : (I.edge j₀).b v * f j₀ +
      ∑ j ∈ Finset.univ.erase j₀, (I.edge j).b v * f j =
      ∑ j : Fin I.m, (I.edge j).b v * f j :=
    Finset.add_sum_erase Finset.univ (fun j => (I.edge j).b v * f j) (Finset.mem_univ j₀)
  have hcons' : (I.edge j₀).b v * f j₀ + (S : ℝ) = (I.d v : ℝ) := by
    change ∑ j : Fin I.m, (I.edge j).b vFin * f j = (I.d vFin : ℝ) at hcons
    dsimp [vFin] at hcons
    linarith [hsplit, hS, hcons]
  dsimp [rawEdge] at he_inc he_noloop
  rcases he_inc with hv_tail | hv_head
  · have hvt : v = (I.edge j₀).tail := hv_tail.symm
    have hvh : v ≠ (I.edge j₀).head := by
      intro h
      exact he_noloop (hv_tail.trans h)
    have hb : (I.edge j₀).b v = 1 := by
      rw [Edge.b, ite_eq_left hvt, ite_eq_right hvh]
      norm_num
    rw [hb, one_mul] at hcons'
    exact hj₀_frac ⟨I.d v - S, by push_cast; linarith⟩
  · have hvh : v = (I.edge j₀).head := hv_head.symm
    have hvt : v ≠ (I.edge j₀).tail := by
      intro h
      exact he_noloop (h.symm.trans hv_head.symm)
    have hb : (I.edge j₀).b v = -1 := by
      rw [Edge.b, ite_eq_right hvt, ite_eq_left hvh]
      norm_num
    rw [hb] at hcons'
    exact hj₀_frac ⟨S - I.d v, by push_cast; linarith⟩

/-- **Kang–Payor Lemma 3.2** (arXiv:1507.08139v1, Section 3.1): if a flow `f` routing integral
demands contains no cycle of edges with fractional flow, then `f` is integral. -/
theorem lemma_3_2 {I : Instance} (hValid : I.IsValid) {f : Fin I.m → ℝ}
    (hRoutes : I.Routes f)
    (hNoCycle : ∀ a es, IsWalk (fracEdges I f) a a es → es.Nodup → es = []) :
    IsIntegral f :=
  lemma_3_1 hValid hRoutes hNoCycle

/-- **Kang–Payor Lemma 3.3** (arXiv:1507.08139v1, Section 3.1): if `f` obeys the integral
capacity constraints of `I` and `f'` satisfies `availFwd f f' j ≥ 0` and `availBwd f f' j ≥ 0` on
every edge, then `f'` obeys all capacity constraints of `I`. -/
theorem lemma_3_3 {I : Instance} {f f' : Fin I.m → ℝ}
    (hCap : ∀ j, ((I.edge j).lower : ℝ) ≤ f j ∧ f j ≤ (I.edge j).upper)
    (hAvail : ∀ j, 0 ≤ availFwd f f' j ∧ 0 ≤ availBwd f f' j) :
    ∀ j, ((I.edge j).lower : ℝ) ≤ f' j ∧ f' j ≤ (I.edge j).upper := by
  intro j
  obtain ⟨hlo, hhi⟩ := hCap j
  obtain ⟨hfwd, hbwd⟩ := hAvail j
  simp only [availFwd, sub_nonneg] at hfwd
  simp only [availBwd, sub_nonneg] at hbwd
  have hfloor : ((I.edge j).lower : ℝ) ≤ (⌊f j⌋ : ℝ) := by
    exact_mod_cast Int.le_floor.mpr hlo
  have hceil : (⌈f j⌉ : ℝ) ≤ ((I.edge j).upper : ℝ) := by
    exact_mod_cast Int.ceil_le.mpr hhi
  exact ⟨hfloor.trans hbwd, hfwd.trans hceil⟩

/-- Corollary of Lemma 3.3: if `f` is feasible and `f'` routes the demands with nonnegative
forward and backward availabilities everywhere, then `f'` is feasible. -/
theorem lemma_3_3_feasible {I : Instance} {f f' : Fin I.m → ℝ}
    (hFeas : I.IsFeasible f) (hRoutes : I.Routes f')
    (hAvail : ∀ j, 0 ≤ availFwd f f' j ∧ 0 ≤ availBwd f f' j) :
    I.IsFeasible f' :=
  ⟨hRoutes, lemma_3_3 hFeas.2 hAvail⟩

/-- A circulation on `I` is a flow vector routing zero demand at every vertex. -/
def IsCirculation (I : Instance) (Δ : Fin I.m → ℝ) : Prop :=
  ∀ v : Fin I.n, ∑ j : Fin I.m, (I.edge j).b v * Δ j = 0

/-- **Kang–Payor Section 3.2 (Costed Flow Rounding)**: pushing a nonnegative amount `δ ≥ 0`
along a circulation `Δ` in the direction of non-negative cost saving (`I.cost Δ ≤ 0` or
`I.cost (-Δ) ≤ 0`) preserves demand routing and does not increase `I.cost`. -/
theorem costed_cycle_cancel {I : Instance} {f' Δ : Fin I.m → ℝ}
    (hRoutes : I.Routes f') (hCirc : IsCirculation I Δ) {δ : ℝ} (hδ : 0 ≤ δ) :
    let s : ℝ := if I.cost Δ ≤ 0 then 1 else -1
    let f'' : Fin I.m → ℝ := fun j => f' j + (s * δ) * Δ j
    I.Routes f'' ∧ I.cost f'' ≤ I.cost f' ∧ 0 ≤ -(s * I.cost Δ) := by
  intro s f''
  have hR'' : I.Routes f'' := by
    intro v
    have hv1 := hRoutes v
    have hv2 := hCirc v
    calc
      ∑ j : Fin I.m, (I.edge j).b v * (f' j + (s * δ) * Δ j)
          = ∑ j : Fin I.m, ((I.edge j).b v * f' j + (s * δ) * ((I.edge j).b v * Δ j)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
      _ = (∑ j : Fin I.m, (I.edge j).b v * f' j) +
            (s * δ) * (∑ j : Fin I.m, (I.edge j).b v * Δ j) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (I.d v : ℝ) := by rw [hv1, hv2, mul_zero, add_zero]
  have hs_cost : s * I.cost Δ ≤ 0 := by
    dsimp [s]
    split_ifs with h
    · linarith
    · push Not at h
      linarith
  have hcost'' : I.cost f'' = I.cost f' + (s * δ) * I.cost Δ := by
    simp only [Instance.cost, f'']
    calc
      ∑ j : Fin I.m, ((I.edge j).cost : ℝ) * (f' j + (s * δ) * Δ j)
          = ∑ j : Fin I.m, (((I.edge j).cost : ℝ) * f' j +
              (s * δ) * (((I.edge j).cost : ℝ) * Δ j)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
      _ = (∑ j : Fin I.m, ((I.edge j).cost : ℝ) * f' j) +
            (s * δ) * (∑ j : Fin I.m, ((I.edge j).cost : ℝ) * Δ j) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hle : I.cost f'' ≤ I.cost f' := by
    rw [hcost'']
    have hmul : (s * δ) * I.cost Δ = δ * (s * I.cost Δ) := by ring
    rw [hmul]
    have : δ * (s * I.cost Δ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδ hs_cost
    linarith
  exact ⟨hR'', hle, by linarith⟩

end MinCostFlow.Rounding
