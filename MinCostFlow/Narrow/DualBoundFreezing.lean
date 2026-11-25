module

public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Scaling.EpsilonOptimal
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import MinCostFlow.Narrow.CostUnitsClip
import MinCostFlow.Scaling.LabelPotential
import MinCostFlow.Scaling.ShortestRoutingPotential
import MinCostFlow.Scaling.ShortestRoutingDemands
import MinCostFlow.Scaling.DualExtractionCorrectness
import MinCostFlow.Scaling.ExpensiveArcs
import MinCostFlow.Scaling.ResidualReduction
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Dual potential magnitude bound and freezing (Lemma 4)

This file proves:
1. `extractDualModel_bounds`: on any circulation `J` with costs `≥ -C_lo` and
   integral optimum `f`, the dual potential returned by `J.extractDualModel`
   satisfies `0 ≤ dy v ≤ (J.n - 1) * C_lo` for every vertex `v`. The upper
   bound is proved by taking a vertex-simple shortest path `P` in
   `J.residual f`, forming the unit-demand flow `f + 1_P` in `J`, extracting a
   vertex-simple path `Q` in its positive support, and comparing the remaining
   feasible circulation `f + 1_P - 1_Q` with the optimum `f`.
2. Lemma 4 (freezing): on compressed instances `I.n ≤ 2 * I.m`, once an edge's
   half-unit reduced cost crosses `±freezeThreshold I.m`, its reduced cost
   satisfies the margin `freezeMargin I.m L p j`, its flow is fixed at `0` (or
   `I.capacity e`), and the margin is preserved across all subsequent rounds,
   keeping the edge above `upperClip I.m * δ_k` forever.
-/

public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling

private lemma tail_mem_vertices_of_count_pos {I : Circulation} {a b : Fin I.n}
    (p : I.DirectedWalk a b) (e : Fin I.m) (h : 0 < p.count e) :
    I.tail e ∈ p.vertices := by
  induction p with
  | nil => simp [Circulation.DirectedWalk.count] at h
  | cons k hk rest ih =>
    by_cases he : e = k
    · subst he
      exact List.mem_cons_self
    · simp only [Circulation.DirectedWalk.count, he, ↓reduceIte, zero_add] at h
      exact List.mem_cons_of_mem _ (ih h)

private lemma count_le_one_of_nodup {I : Circulation} {a b : Fin I.n}
    (p : I.DirectedWalk a b) (hp : p.vertices.Nodup) (e : Fin I.m) :
    p.count e ≤ 1 := by
  induction p with
  | nil => simp [Circulation.DirectedWalk.count]
  | cons k hk rest ih =>
    have ⟨hnot, hnod⟩ := List.nodup_cons.mp hp
    by_cases he : e = k
    · subst he
      have hz : rest.count e = 0 := by
        by_contra hne
        exact hnot (tail_mem_vertices_of_count_pos rest e (Nat.pos_of_ne_zero hne))
      simp [Circulation.DirectedWalk.count, hz]
    · simp only [Circulation.DirectedWalk.count, he, ↓reduceIte, zero_add]
      exact ih hnod

private lemma extract_original_walk {R : Circulation} {x y : Fin (R.n + 1)}
    (p : R.shortestRoutingGraph.DirectedWalk x y)
    (hlast : Fin.last R.n ∉ p.vertices)
    (a b : Fin R.n) (ha : x = a.castSucc) (hb : y = b.castSucc) :
    ∃ q : R.DirectedWalk a b,
      q.cost = p.cost ∧ ∀ e, q.count e = p.count (Fin.castAdd R.n e) := by
  induction p using Circulation.DirectedWalk.rec (I := R.shortestRoutingGraph) generalizing a b with
  | nil v =>
    have hab : a = b := Fin.castSucc_injective R.n (ha.symm.trans hb)
    subst hab
    exact ⟨Circulation.DirectedWalk.nil (I := R) a, rfl, fun _ => rfl⟩
  | cons k hk rest ih =>
    have htail_ne : R.shortestRoutingGraph.tail k ≠ Fin.last R.n := fun heq =>
      hlast (heq ▸ List.mem_cons_self)
    have hrest_last : Fin.last R.n ∉ rest.vertices := fun hmem =>
      hlast (List.mem_cons_of_mem _ hmem)
    have hk_isLt : k.val < R.m + R.n := k.isLt
    by_cases hk_lt : k.val < R.m
    · let e : Fin R.m := ⟨k.val, hk_lt⟩
      have hkeq : k = Fin.castAdd R.n e := Fin.ext rfl
      have htail_eq : R.tail e = a := by
        have h1 : (R.tail e).castSucc = a.castSucc := by
          rw [hkeq] at ha
          simpa only [Fin.addCases_left] using ha
        exact Fin.castSucc_injective R.n h1
      have hhead_eq : R.shortestRoutingGraph.head k = (R.head e).castSucc := by
        rw [hkeq]
        simp only [Fin.addCases_left]
      have he_cap : 0 < R.capacity e := by
        rw [hkeq] at hk
        simp only [Fin.addCases_left] at hk
        split at hk
        · assumption
        · omega
      obtain ⟨q', hcost', hcnt'⟩ := ih hrest_last (R.head e) b hhead_eq hb
      subst htail_eq
      refine ⟨Circulation.DirectedWalk.cons (I := R) e he_cap q', ?_, ?_⟩
      · simp only [Circulation.DirectedWalk.cost, hkeq, Fin.addCases_left, hcost']
      · intro e'
        have hinj : (Fin.castAdd R.n e' = Fin.castAdd R.n e) ↔ e' = e := by
          constructor
          · intro h; exact Fin.ext (by simpa [Fin.ext_iff] using h)
          · intro h; rw [h]
        simp only [Circulation.DirectedWalk.count, hkeq, hcnt', hinj]
    · let u : Fin R.n := ⟨k.val - R.m, by omega⟩
      have hkeq : k = Fin.natAdd R.m u := Fin.ext (by dsimp [u]; omega)
      rw [hkeq] at htail_ne
      simp only [Fin.addCases_right] at htail_ne
      exact False.elim (htail_ne rfl)

private lemma split_rooted_routing_walk_aux {R : Circulation} {x y : Fin (R.n + 1)}
    (p : R.shortestRoutingGraph.DirectedWalk x y)
    (hp : p.vertices.Nodup) (v : Fin R.n)
    (hx : x = Fin.last R.n) (hy : y = v.castSucc) :
    ∃ (u₀ : Fin R.n) (q : R.DirectedWalk u₀ v),
      q.cost = p.cost ∧ ∀ e, q.count e ≤ 1 := by
  match p with
  | .nil w =>
    exact False.elim (Fin.castSucc_ne_last v (hy.symm.trans hx))
  | .cons k hk rest =>
    have ⟨hnot, hnod⟩ := List.nodup_cons.mp hp
    have hk_isLt : k.val < R.m + R.n := k.isLt
    by_cases hk_lt : k.val < R.m
    · exfalso
      let e : Fin R.m := ⟨k.val, hk_lt⟩
      have hkeq : k = Fin.castAdd R.n e := Fin.ext rfl
      rw [hkeq] at hx
      simp only [Fin.addCases_left] at hx
      exact Fin.castSucc_ne_last (R.tail e) hx
    · let u₀ : Fin R.n := ⟨k.val - R.m, by omega⟩
      have hkeq : k = Fin.natAdd R.m u₀ := Fin.ext (by dsimp [u₀]; omega)
      have hhead : R.shortestRoutingGraph.head k = u₀.castSucc := by
        rw [hkeq]; simp only [Fin.addCases_right]
      have hlast : Fin.last R.n ∉ rest.vertices := hx ▸ hnot
      obtain ⟨q, hcost, hcnt⟩ := extract_original_walk rest hlast u₀ v hhead hy
      refine ⟨u₀, q, ?_, fun e => ?_⟩
      · simp only [Circulation.DirectedWalk.cost, hkeq, Fin.addCases_right, zero_add, hcost]
      · rw [hcnt e]
        exact count_le_one_of_nodup rest hnod (Fin.castAdd R.n e)

private lemma split_rooted_routing_walk {R : Circulation} {v : Fin R.n}
    (p : R.shortestRoutingGraph.DirectedWalk (Fin.last R.n) v.castSucc)
    (hp : p.vertices.Nodup) :
    ∃ (u₀ : Fin R.n) (q : R.DirectedWalk u₀ v),
      q.cost = p.cost ∧ ∀ e, q.count e ≤ 1 :=
  split_rooted_routing_walk_aux p hp v rfl rfl

private lemma exists_support_path_of_unit_demand (J : Circulation)
    (g : Fin J.m → ℝ) (u₀ v : Fin J.n)
    (hg_nonneg : ∀ e, 0 ≤ g e)
    (hbal : ∀ x, J.balance g x = (if x = u₀ then 1 else 0) - (if x = v then 1 else 0)) :
    Nonempty ((J.positiveSupport g).DirectedWalk u₀ v) := by
  classical
  let S : Finset (Fin J.n) :=
    Finset.univ.filter (fun x => Nonempty ((J.positiveSupport g).DirectedWalk u₀ x))
  have hmem (x : Fin J.n) : x ∈ S ↔ Nonempty ((J.positiveSupport g).DirectedWalk u₀ x) := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hu₀ : u₀ ∈ S := (hmem u₀).mpr ⟨Circulation.DirectedWalk.nil (I := J.positiveSupport g) u₀⟩
  have hclosed : ∀ e, J.tail e ∈ S → 0 < g e → J.head e ∈ S := by
    intro e he hpos
    obtain ⟨p⟩ := (hmem _).mp he
    apply (hmem _).mpr
    have hact : 0 < (J.positiveSupport g).capacity e := by
      change 0 < if 0 < g e then 1 else 0
      rw [ite_eq_left hpos]
      decide
    exact ⟨p.append (Circulation.DirectedWalk.cons (I := J.positiveSupport g) e hact
      (Circulation.DirectedWalk.nil (I := J.positiveSupport g) (J.head e)))⟩
  by_contra hv_not
  have hv : v ∉ S := fun h => hv_not ((hmem v).mp h)
  let y : Fin J.n → ℝ := fun x => if x ∈ S then 1 else 0
  have hpair := J.potential_pairing g y
  have hrhs : (∑ x, y x * J.balance g x) = 1 := by
    have hterm : ∀ x, y x * J.balance g x = if x = u₀ then 1 else 0 := by
      intro x
      rw [hbal x]
      by_cases hxS : x ∈ S
      · by_cases hxu : x = u₀
        · subst x
          have hne : u₀ ≠ v := fun heq => hv (heq ▸ hu₀)
          simp [y, hxS, hne]
        · have hxv : x ≠ v := fun heq => hv (heq ▸ hxS)
          simp [y, hxS, hxu, hxv]
      · have hxu : x ≠ u₀ := fun heq => hxS (heq ▸ hu₀)
        simp [y, hxS, hxu]
    simp [hterm]
  have hlhs : (∑ e, J.potentialDifference y e * g e) ≤ 0 := by
    apply Finset.sum_nonpos
    intro e _
    have hge := hg_nonneg e
    by_cases ht : J.tail e ∈ S <;> by_cases hh : J.head e ∈ S
    · simp only [Circulation.potentialDifference, y, ht, hh, ↓reduceIte, sub_self, zero_mul, le_refl]
    · have hz : g e = 0 := by
        by_contra hne
        exact hh (hclosed e ht (lt_of_le_of_ne hge (Ne.symm hne)))
      rw [hz, mul_zero]
    · simp only [Circulation.potentialDifference, y, ht, hh, ↓reduceIte, zero_sub, neg_mul, one_mul]
      exact neg_nonpos.mpr hge
    · simp only [Circulation.potentialDifference, y, ht, hh, ↓reduceIte, sub_self, zero_mul, le_refl]
  linarith only [hpair, hrhs, hlhs]

private lemma walk_of_positiveSupport_bounded {J : Circulation} {g : Fin J.m → ℝ}
    (hg : ∀ e, g e ≤ J.capacity e) {a b : Fin J.n}
    (p : (J.positiveSupport g).DirectedWalk a b) :
    ∃ w : J.DirectedWalk a b,
      w.vertices = p.vertices ∧ w.cost = p.cost ∧
      (∀ e, w.count e = p.count e) ∧ ∀ e, 0 < w.count e → 0 < g e := by
  induction p using Circulation.DirectedWalk.rec (I := J.positiveSupport g) with
  | nil v =>
    exact ⟨Circulation.DirectedWalk.nil (I := J) v, rfl, rfl, fun _ => rfl,
      fun _ h => by simp [Circulation.DirectedWalk.count] at h⟩
  | cons e he rest ih =>
    have hpos : 0 < g e := by
      change 0 < if 0 < g e then 1 else 0 at he
      split at he
      · assumption
      · omega
    have hcap : 0 < J.capacity e := by
      have : (0 : ℝ) < (J.capacity e : ℝ) := lt_of_lt_of_le hpos (hg e)
      exact_mod_cast this
    obtain ⟨w', hverts, hcost, hcnt, hsupp⟩ := ih
    refine ⟨Circulation.DirectedWalk.cons (I := J) e hcap w', ?_, ?_, ?_, ?_⟩
    · simp [Circulation.DirectedWalk.vertices, hverts]
    · simp [Circulation.DirectedWalk.cost, hcost]
    · intro k; simp [Circulation.DirectedWalk.count, hcnt k]
    · intro k hk
      by_cases hke : k = e
      · exact hke ▸ hpos
      · simp only [Circulation.DirectedWalk.count, hke, ↓reduceIte, zero_add] at hk
        exact hsupp k hk

/-- Dual magnitude bound (Lemma 4 prerequisite): on any circulation `J` whose
arc costs are all at least `-C_lo`, if `f` is an integral optimum of `J` and
the routing subproblem is solved optimally, then the dual potential returned by
`J.extractDualModel solve f` satisfies `0 ≤ dy v ≤ (J.n - 1) * C_lo` for every
vertex `v`. -/
theorem extractDualModel_bounds (solve : (K : Circulation) → Fin K.m → ℤ)
    (J : Circulation) (C_lo : ℕ) (hC : ∀ e, -(C_lo : ℤ) ≤ J.cost e)
    (f : Fin J.m → ℤ) (hf : J.Optimal (fun e => (f e : ℝ)))
    (hQ : let R := J.residual f
      let Q := R.shortestRoutingGraph.residual R.shortestRoutingStart
      Q.Optimal (fun e => (Circulation.solveWithZeroCapacities solve Q e : ℝ))) :
    ∀ v : Fin J.n,
      0 ≤ (J.extractDualModel solve f).value v ∧
      (J.extractDualModel solve f).value v ≤ ((J.n - 1 : ℕ) : ℤ) * (C_lo : ℤ) := by
  classical
  let R := J.residual f
  let S := R.shortestRoutingGraph
  let start := R.shortestRoutingStart
  let Q := S.residual start
  let delta := Circulation.solveWithZeroCapacities solve Q
  let routing : Fin S.m → ℤ := fun e =>
    start e + delta (Fin.castAdd S.m e) - delta (Fin.natAdd S.m e)
  have hcast : (fun e => (routing e : ℝ)) = S.augment start (fun e => (delta e : ℝ)) := by
    funext e
    simp only [routing, Circulation.augment, Circulation.project, Int.cast_add, Int.cast_sub]
    ring
  have haug := S.augment_optimal_with_demands start R.shortestRoutingStart_bounds
    (fun e => (delta e : ℝ)) hQ
  have hbalance : ∀ w, S.balance (fun e => (routing e : ℝ)) w =
      (S.n : ℝ) * (if w = Fin.last J.n then 1 else 0) - 1 := by
    intro w
    rw [hcast, haug.1 w]
    exact R.shortestRoutingStart_balance w
  have hbounds : ∀ e, 0 ≤ (routing e : ℝ) ∧ (routing e : ℝ) ≤ S.capacity e := by
    intro e
    rw [congrFun hcast e]
    exact haug.2.1 e
  have hopt : ∀ g : Fin S.m → ℝ,
      (∀ w, S.balance g w = (S.n : ℝ) * (if w = Fin.last J.n then 1 else 0) - 1) →
      (∀ e, 0 ≤ g e ∧ g e ≤ S.capacity e) →
      S.objective (fun e => (routing e : ℝ)) ≤ S.objective g := by
    intro g hb hg
    rw [hcast]
    apply haug.2.2 g _ hg
    intro w
    rw [hb, R.shortestRoutingStart_balance w]
  have hzero := J.zero_residual_optimal f hf
  have hclosed : ∀ w : Fin R.n, ∀ p : R.DirectedWalk w w, 0 ≤ p.cost :=
    fun _ p => p.cost_nonneg_of_zero_optimal hzero
  have hSclosed := R.shortestRoutingGraph_closed_nonneg hclosed
  obtain ⟨d, hd0, htri, hpaths⟩ := S.exists_rooted_distances (Fin.last J.n) hSclosed
    R.shortestRoutingGraph_reachable
  choose paths hnodup hcost using hpaths
  have hbounds_p := S.rootedPathsFlow_bounds (Fin.last J.n) paths hnodup
    R.shortestRoutingGraph_active_capacity
  have hbal_p := S.rootedPathsFlow_balance (Fin.last J.n) paths
  have hcompare := hopt (S.rootedPathsFlow (Fin.last J.n) paths) hbal_p hbounds_p
  have htight := S.rooted_routing_tight (Fin.last J.n) d hd0 htri paths hcost
    (fun e => (routing e : ℝ)) hbalance hbounds hcompare
  have hseen := S.propagateLabels_all_seen routing (Fin.last J.n) (fun e => (hbounds e).1) hbalance
  have hlabels : ∀ w, (S.propagateLabels routing (Fin.last J.n)).1.labels w = -d w := by
    intro w
    apply S.propagateLabels_accuracy routing (Fin.last J.n) (fun x => -d x) (by rw [hd0, neg_zero])
      (fun e he => htight e (Int.cast_pos.mpr he)) w (hseen w)
  intro v
  have hval : (J.extractDualModel solve f).value v = -d v.castSucc := hlabels v.castSucc
  rw [hval]
  constructor
  · -- Upper bound `d v.castSucc ≤ 0` from the direct zero-cost arc `Fin.last J.n → v.castSucc`.
    have hact : 0 < S.capacity (Fin.natAdd R.m v) := by
      simp only [S, Fin.addCases_right]
      exact Nat.zero_lt_succ _
    have hstep := htri (Fin.natAdd R.m v) hact
    simp only [S, Fin.addCases_right] at hstep
    rw [hd0, zero_add] at hstep
    omega
  · -- Lower bound `-((J.n - 1) * C_lo) ≤ d v.castSucc` via `f + 1_q - 1_w`.
    obtain ⟨u₀, q, hq_cost, hq_le1⟩ :=
      split_rooted_routing_walk (paths v.castSucc) (hnodup v.castSucc)
    let g : Fin J.m → ℤ := fun e =>
      f e + (q.count (Fin.castAdd J.m e) : ℤ) - (q.count (Fin.natAdd J.m e) : ℤ)
    have hg_cast : (fun e => (g e : ℝ)) = J.augment f (fun a => (q.count a : ℝ)) := by
      funext e
      simp only [g, Circulation.augment, Circulation.project, Int.cast_add, Int.cast_sub,
        Int.cast_natCast]
      ring
    have hq_cap : ∀ a, 0 ≤ (q.count a : ℝ) ∧ (q.count a : ℝ) ≤ R.capacity a := by
      intro a
      refine ⟨Nat.cast_nonneg _, ?_⟩
      by_cases hz : q.count a = 0
      · simp only [hz, Nat.cast_zero]; exact Nat.cast_nonneg _
      · have hpos : 0 < q.count a := Nat.pos_of_ne_zero hz
        have hact : 0 < R.capacity a := q.active_of_count_pos a hpos
        have h1 : q.count a ≤ 1 := hq_le1 a
        have hle : q.count a ≤ R.capacity a := by omega
        exact_mod_cast hle
    have hg_bounds : ∀ e, 0 ≤ (g e : ℝ) ∧ (g e : ℝ) ≤ J.capacity e := by
      intro e
      rw [congrFun hg_cast e]
      have ha := hq_cap (Fin.castAdd J.m e)
      have hb := hq_cap (Fin.natAdd J.m e)
      rw [(J.residual_capacity_cast f hf.1.2 e).1] at ha
      rw [(J.residual_capacity_cast f hf.1.2 e).2] at hb
      dsimp only [Circulation.augment, Circulation.project]
      constructor <;> linarith only [ha.1, ha.2, hb.1, hb.2]
    have hg_bal : ∀ x, J.balance (fun e => (g e : ℝ)) x =
        (if x = u₀ then 1 else 0) - (if x = v then 1 else 0) := by
      intro x
      rw [hg_cast, J.augment_balance, hf.1.1 x, zero_add]
      exact q.balance_count x
    have hg_obj : J.objective (fun e => (g e : ℝ)) =
        J.objective (fun e => (f e : ℝ)) + (q.cost : ℝ) := by
      rw [hg_cast, J.augment_objective, q.objective_count]
    obtain ⟨p_supp⟩ := exists_support_path_of_unit_demand J (fun e => (g e : ℝ)) u₀ v
      (fun e => (hg_bounds e).1) hg_bal
    obtain ⟨p_nodup, hp_nodup⟩ := p_supp.exists_nodup
    obtain ⟨w, hw_verts, hw_cost, hw_cnt, hw_supp⟩ :=
      walk_of_positiveSupport_bounded (fun e => (hg_bounds e).2) p_nodup
    have hw_nodup : w.vertices.Nodup := hw_verts ▸ hp_nodup
    have hw_le1 : ∀ e, w.count e ≤ 1 := count_le_one_of_nodup w hw_nodup
    let c : Fin J.m → ℝ := fun e => (g e : ℝ) - (w.count e : ℝ)
    have hc_feas : J.Feasible c := by
      constructor
      · intro x
        have hsub : J.balance c x = J.balance (fun e => (g e : ℝ)) x -
            J.balance (fun e => (w.count e : ℝ)) x := J.balance_sub _ _ x
        rw [hsub, hg_bal x, w.balance_count x, sub_self]
      · intro e
        refine ⟨?_, ?_⟩
        · by_cases hz : w.count e = 0
          · simp only [c, hz, Nat.cast_zero, sub_zero]
            exact (hg_bounds e).1
          · have hpos_r : 0 < (g e : ℝ) := hw_supp e (Nat.pos_of_ne_zero hz)
            have hpos_z : 0 < g e := Int.cast_pos.mp hpos_r
            have h1 : w.count e ≤ 1 := hw_le1 e
            have hle : (w.count e : ℤ) ≤ g e := by omega
            have hle_r : (w.count e : ℝ) ≤ (g e : ℝ) := by exact_mod_cast hle
            dsimp only [c]
            linarith only [hle_r]
        · have h0 : (0 : ℝ) ≤ (w.count e : ℝ) := Nat.cast_nonneg _
          dsimp only [c]
          linarith only [(hg_bounds e).2, h0]
    have hopt_cmp := hf.2 c hc_feas
    have hc_obj : J.objective c = J.objective (fun e => (g e : ℝ)) - (w.cost : ℝ) := by
      have hsub : J.objective c = J.objective (fun e => (g e : ℝ)) -
          J.objective (fun e => (w.count e : ℝ)) := by
        simp only [Circulation.objective, c, mul_sub, Finset.sum_sub_distrib]
      rw [hsub, w.objective_count]
    rw [hc_obj, hg_obj] at hopt_cmp
    have hw_le_q : w.cost ≤ q.cost := by
      have : (w.cost : ℝ) ≤ (q.cost : ℝ) := by linarith only [hopt_cmp]
      exact_mod_cast this
    have hw_len : w.length < J.n := w.length_lt_vertices_of_nodup hw_nodup
    have hw_len_le : (w.length : ℤ) ≤ ((J.n - 1 : ℕ) : ℤ) := by
      have hv_pos : 0 < J.n := Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt
      omega
    have hw_lower := w.cost_ge_neg_length_mul (C_lo : ℤ) hC
    have hC0 : (0 : ℤ) ≤ (C_lo : ℤ) := Int.natCast_nonneg C_lo
    have hmul : -((J.n - 1 : ℕ) : ℤ) * (C_lo : ℤ) ≤ -(w.length : ℤ) * (C_lo : ℤ) :=
      mul_le_mul_of_nonneg_right (neg_le_neg hw_len_le) hC0
    have hq_eq : q.cost = d v.castSucc := hq_cost.trans (hcost v.castSucc)
    linarith only [hmul, hw_lower, hw_le_q, hq_eq]

/-- One-round reduced-cost drift bound: if `0 ≤ dy v ≤ (I.n - 1) * lowerClip I.m`
on a compressed instance `I.n ≤ 2 * I.m`, then adding `δ_j * dy` changes every
edge's reduced cost by at most `2 * I.m * ε_j`. -/
theorem reducedCost_drift_le (I : Circulation) (hn : I.n ≤ 2 * I.m)
    (L j : ℕ) (y : Fin I.n → ℝ) (dy : Fin I.n → ℤ)
    (hdy : ∀ v, 0 ≤ dy v ∧ dy v ≤ ((I.n - 1 : ℕ) : ℤ) * (lowerClip I.m : ℤ))
    (e : Fin I.m) :
    |I.reducedCost (fun v => y v + stageDelta L j * (dy v : ℝ)) e - I.reducedCost y e| ≤
      2 * (I.m : ℝ) * stageEps L (costPrecisionExp I.m) j := by
  have hδ : 0 < stageDelta L j := stageDelta_pos L j
  have hdiff : I.reducedCost (fun v => y v + stageDelta L j * (dy v : ℝ)) e - I.reducedCost y e =
      -(stageDelta L j * ((dy (I.tail e) : ℝ) - (dy (I.head e) : ℝ))) := by
    simp only [Circulation.reducedCost, Circulation.potentialDifference]
    ring
  have hbound_int : ∀ v, 0 ≤ dy v ∧ dy v ≤ (2 * (I.m : ℤ)) * (lowerClip I.m : ℤ) := by
    intro v
    refine ⟨(hdy v).1, le_trans (hdy v).2 ?_⟩
    exact mul_le_mul_of_nonneg_right (by omega) (Int.natCast_nonneg _)
  have ht := hbound_int (I.tail e)
  have hh := hbound_int (I.head e)
  have hsub_lo : -((2 * (I.m : ℤ)) * (lowerClip I.m : ℤ)) ≤ dy (I.tail e) - dy (I.head e) := by
    omega
  have hsub_hi : dy (I.tail e) - dy (I.head e) ≤ (2 * (I.m : ℤ)) * (lowerClip I.m : ℤ) := by
    omega
  have hsub_lo_r : -(2 * (I.m : ℝ) * (lowerClip I.m : ℝ)) ≤
      (dy (I.tail e) : ℝ) - (dy (I.head e) : ℝ) := by
    have : ((-((2 * (I.m : ℤ)) * (lowerClip I.m : ℤ)) : ℤ) : ℝ) ≤
        ((dy (I.tail e) - dy (I.head e) : ℤ) : ℝ) := by exact_mod_cast hsub_lo
    push_cast at this
    linarith only [this]
  have hsub_hi_r : (dy (I.tail e) : ℝ) - (dy (I.head e) : ℝ) ≤
      2 * (I.m : ℝ) * (lowerClip I.m : ℝ) := by
    have : ((dy (I.tail e) - dy (I.head e) : ℤ) : ℝ) ≤
        (((2 * (I.m : ℤ)) * (lowerClip I.m : ℤ) : ℤ) : ℝ) := by exact_mod_cast hsub_hi
    push_cast at this
    linarith only [this]
  rw [hdiff, stageEps_eq_lowerClip_mul_delta, abs_le]
  constructor <;> nlinarith only [hδ, hsub_lo_r, hsub_hi_r]

/-- The freezing margin dominates `upperClip m * δ_j`. -/
theorem freezeMargin_ge_upperClip_mul_delta (m L j : ℕ) :
    (upperClip m : ℝ) * stageDelta L j ≤ freezeMargin m L (costPrecisionExp m) j := by
  have heps := stageEps_eq_lowerClip_mul_delta L m j
  have hδ : 0 < stageDelta L j := stageDelta_pos L j
  have huc : (upperClip m : ℝ) = ((2 ^ costClipExp m : ℕ) : ℝ) * (lowerClip m : ℝ) := by
    unfold upperClip lowerClip
    rw [pow_add, Nat.mul_comm]
    push_cast
    rfl
  unfold freezeMargin
  rw [heps, huc]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hlo0 : (0 : ℝ) ≤ (lowerClip m : ℝ) := Nat.cast_nonneg _
  have hextra : 0 ≤ 4 * (m : ℝ) * ((lowerClip m : ℝ) * stageDelta L j) :=
    mul_nonneg (mul_nonneg (by norm_num) hm0) (mul_nonneg hlo0 hδ.le)
  linarith only [hextra]

/-- The freezing margin strictly exceeds `ε_j` for `0 < m`. -/
theorem freezeMargin_gt_eps (m L j : ℕ) (hm : 0 < m) :
    stageEps L (costPrecisionExp m) j < freezeMargin m L (costPrecisionExp m) j := by
  have heps : 0 < stageEps L (costPrecisionExp m) j := stageEps_pos L (costPrecisionExp m) j
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hq0 : (0 : ℝ) ≤ ((2 ^ costClipExp m : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold freezeMargin
  nlinarith only [heps, hm1, hq0]

/-- Crossing `+freezeThreshold m` establishes the positive freezing margin. -/
theorem freezeMargin_of_threshold_pos (m L j : ℕ) (c : ℝ)
    (hge : (freezeThreshold m : ℤ) ≤ Int.floor (2 * c / stageDelta L j)) :
    freezeMargin m L (costPrecisionExp m) j ≤ c := by
  have hδ : 0 < stageDelta L j := stageDelta_pos L j
  have hfl : ((freezeThreshold m : ℤ) : ℝ) ≤ 2 * c / stageDelta L j :=
    le_trans (by exact_mod_cast hge) (Int.floor_le _)
  have hc : ((freezeThreshold m : ℕ) : ℝ) * stageDelta L j ≤ 2 * c := by
    simpa only [Int.cast_natCast] using (le_div_iff₀ hδ).mp hfl
  have hth : ((freezeThreshold m : ℕ) : ℝ) * stageDelta L j =
      8 * ((2 ^ costClipExp m : ℕ) : ℝ) * stageEps L (costPrecisionExp m) j := by
    rw [stageEps_eq_lowerClip_mul_delta]
    unfold freezeThreshold upperClip lowerClip
    rw [pow_add]
    push_cast
    ring
  have hq : 2 * (m : ℝ) ≤ ((2 ^ costClipExp m : ℕ) : ℝ) := by
    exact_mod_cast two_mul_le_two_pow_clipExp m
  have heps : 0 < stageEps L (costPrecisionExp m) j := stageEps_pos L (costPrecisionExp m) j
  unfold freezeMargin
  rw [hth] at hc
  nlinarith only [hc, hq, heps]

/-- Crossing `-freezeThreshold m` establishes the negative freezing margin. -/
theorem freezeMargin_of_threshold_neg (m L j : ℕ) (hm : 0 < m) (c : ℝ)
    (hle : Int.floor (2 * c / stageDelta L j) ≤ -(freezeThreshold m : ℤ)) :
    freezeMargin m L (costPrecisionExp m) j ≤ -c := by
  have hδ : 0 < stageDelta L j := stageDelta_pos L j
  have hlt : 2 * c / stageDelta L j < (-(freezeThreshold m : ℤ) : ℝ) + 1 :=
    lt_of_lt_of_le (Int.lt_floor_add_one _)
      (by exact_mod_cast (show Int.floor (2 * c / stageDelta L j) + 1 ≤
        -(freezeThreshold m : ℤ) + 1 by omega))
  have hc : 2 * c < (-((freezeThreshold m : ℕ) : ℝ) + 1) * stageDelta L j := by
    have := (div_lt_iff₀ hδ).mp hlt
    push_cast at this
    exact this
  have hth : ((freezeThreshold m : ℕ) : ℝ) * stageDelta L j =
      8 * ((2 ^ costClipExp m : ℕ) : ℝ) * stageEps L (costPrecisionExp m) j := by
    rw [stageEps_eq_lowerClip_mul_delta]
    unfold freezeThreshold upperClip lowerClip
    rw [pow_add]
    push_cast
    ring
  have hq : 2 * (m : ℝ) ≤ ((2 ^ costClipExp m : ℕ) : ℝ) := by
    exact_mod_cast two_mul_le_two_pow_clipExp m
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have heps : 0 < stageEps L (costPrecisionExp m) j := stageEps_pos L (costPrecisionExp m) j
  have hδ_le_eps : stageDelta L j ≤ stageEps L (costPrecisionExp m) j := by
    rw [stageEps_eq_lowerClip_mul_delta]
    have h1 : (1 : ℝ) ≤ (lowerClip m : ℝ) := by exact_mod_cast lowerClip_pos m
    nlinarith only [hδ, h1]
  unfold freezeMargin
  nlinarith only [hc, hth, hq, hm1, heps, hδ_le_eps]

/-- Lemma 4 preservation: a reduced cost of at least `freezeMargin` (or at most
`-freezeMargin`) stays past `freezeMargin` in the next round under any drift of
at most `2 * m * ε_j`. -/
theorem freezeMargin_preserved (m L j : ℕ) (c c' : ℝ)
    (hprev : freezeMargin m L (costPrecisionExp m) j ≤ c)
    (hdrift : |c' - c| ≤ 2 * (m : ℝ) * stageEps L (costPrecisionExp m) j) :
    freezeMargin m L (costPrecisionExp m) (j + 1) ≤ c' := by
  have habs := (abs_le.mp hdrift).1
  have hsucc := stageEps_succ L (costPrecisionExp m) j
  have heps : 0 < stageEps L (costPrecisionExp m) j := stageEps_pos L (costPrecisionExp m) j
  have hq0 : (0 : ℝ) ≤ ((2 ^ costClipExp m : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold freezeMargin at hprev ⊢
  rw [hsucc]
  nlinarith only [hprev, habs, heps, hq0]

/-- In an `ε_j`-optimal state, a positive freezing margin forces zero flow on
the edge, and a negative freezing margin forces flow equal to capacity. -/
theorem flow_eq_of_freezeMargin (I : Circulation) (hm : 0 < I.m) (L j : ℕ)
    (f : Fin I.m → ℤ) (y : Fin I.n → ℝ)
    (hopt : I.EpsilonOptimalWith (fun e => (f e : ℝ))
      (stageEps L (costPrecisionExp I.m) j) y) (e : Fin I.m) :
    (freezeMargin I.m L (costPrecisionExp I.m) j ≤ I.reducedCost y e → f e = 0) ∧
    (freezeMargin I.m L (costPrecisionExp I.m) j ≤ -I.reducedCost y e →
      f e = (I.capacity e : ℤ)) := by
  have hgt := freezeMargin_gt_eps I.m L j hm
  have hlo : 0 ≤ f e := (Int.cast_nonneg_iff (R := ℝ)).mp (hopt.2.1.2 e).1
  have hhi : f e ≤ (I.capacity e : ℤ) := by
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [Int.cast_natCast] using (hopt.2.1.2 e).2
  constructor
  · intro hpos
    by_contra hne
    have hgt0 : (0 : ℝ) < (f e : ℝ) := Int.cast_pos.mpr (by omega)
    have hrev := (hopt.2.2 e).2 hgt0
    linarith only [hgt, hpos, hrev]
  · intro hneg
    by_contra hne
    have hlt : (f e : ℝ) < (I.capacity e : ℝ) := by
      have : f e < (I.capacity e : ℤ) := by omega
      exact_mod_cast this
    have hfwd := (hopt.2.2 e).1 hlt
    linarith only [hgt, hneg, hfwd]

end MinCostFlow.Narrow
