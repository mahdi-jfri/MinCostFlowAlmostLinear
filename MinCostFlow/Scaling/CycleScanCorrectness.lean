module

public import MinCostFlow.Scaling.WalkRepeatPeel
public import MinCostFlow.Scaling.CycleScanFacts
public import MinCostFlow.Scaling.CycleExtractionCost
public import MinCostFlow.Scaling.CycleEdgeMembership
public import MinCostFlow.Scaling.ReductionAlgorithm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Correctness of the outer negative-cycle scan

The unit-flow reduction in Lemma C.10 of Chen et al., arXiv:2203.00671v2,
Appendix C, follows unused arcs, peels closed suffixes, and discards only
nonnegative closed parts. This proof follows the actual finite run. The
unused-flow balance rules out an open dead end, candidate coverage rules out
unused edges at completion, and the cost ledger makes failure impossible
on a negative input circulation. Repeated-vertex phases use their exact
proved execution identity, including when the supplied fuel ends mid-phase.
-/

public section
namespace MinCostFlow.Scaling.Circulation
open CycleState
variable {I : Circulation}

mutual
private theorem scan_choose (fuel : ℕ) (bound : ℝ)
    (out : Fin I.n → List (Fin I.m)) (candidates : List (Fin I.m))
    (hout : ∀ v e, e ∈ out v → I.tail e = v ∧ 0 < I.capacity e)
    (hb : ∀ v, I.balance (I.adjacencyFlow out) v = 0)
    (hcover : ∀ v, out v ≠ [] → ∃ e ∈ candidates, I.tail e = v)
    (hbound : I.objective (I.adjacencyFlow out) ≤ bound)
    (hdone : (run fuel (chooseFrame out candidates)).1.mode = .done) :
    ((run fuel (chooseFrame out candidates)).1.result = none ∧ 0 ≤ bound) ∨
      ∃ es : List (Fin I.m), ∃ v : Fin I.n, ∃ p : I.DirectedWalk v v,
        (run fuel (chooseFrame out candidates)).1.result = some es ∧
          p.edges = es ∧ ∀ e, p.count e ≤ 1 := by
  cases fuel with
  | zero => cases hdone
  | succ fuel =>
    have hr : (run (fuel + 1) (chooseFrame out candidates)).1 =
        (run fuel (chooseFrame out candidates).step).1 := by
      simp only [run, chooseFrame, reduceCtorEq, ↓reduceIte]
    rw [hr] at hdone ⊢
    cases candidates with
    | nil =>
      have hempty : ∀ v, out v = [] := by
        intro v
        by_contra hn
        obtain ⟨e, he, _⟩ := hcover v hn
        cases he
      have hzero : I.objective (I.adjacencyFlow out) = 0 := by
        simp only [objective, adjacencyFlow, hempty, List.count_nil, Nat.cast_zero,
          mul_zero, Finset.sum_const_zero]
      rw [run_value_of_done _ _ (by rfl)]
      exact Or.inl ⟨rfl, hzero ▸ hbound⟩
    | cons e rest =>
      by_cases ho : out (I.tail e) = []
      · rw [chooseFrame_skip out e rest ho] at hdone ⊢
        apply scan_choose fuel bound out rest hout hb _ hbound hdone
        intro v hv
        obtain ⟨a, ha, ht⟩ := hcover v hv
        rcases List.mem_cons.mp ha with ha | ha
        · subst a
          rw [← ht, ho] at hv
          exact False.elim (hv rfl)
        · exact ⟨a, ha, ht⟩
      · rw [chooseFrame_start out e rest ho] at hdone ⊢
        apply scan_walk fuel bound out rest (ReverseWalk.nil (I := I) (I.tail e))
          (by simp [ReverseWalk.vertices]) hout _ _ _ hdone
        · intro v
          rw [hb]
          simp only [sub_self]
        · intro v hv
          obtain ⟨a, ha, ht⟩ := hcover v hv
          rcases List.mem_cons.mp ha with ha | ha
          · subst a
            exact Or.inl ht.symm
          · exact Or.inr ⟨a, ha, ht⟩
        · simpa only [ReverseWalk.cost, Int.cast_zero, add_zero] using hbound
termination_by fuel

private theorem scan_walk (fuel : ℕ) (bound : ℝ)
    (out : Fin I.n → List (Fin I.m)) (candidates : List (Fin I.m))
    {root current : Fin I.n} (path : I.ReverseWalk root current) (hp : path.vertices.Nodup)
    (hout : ∀ v e, e ∈ out v → I.tail e = v ∧ 0 < I.capacity e)
    (hb : ∀ v, I.balance (I.adjacencyFlow out) v =
      (if v = current then 1 else 0) - (if v = root then 1 else 0))
    (hcover : ∀ v, out v ≠ [] → v = root ∨ ∃ e ∈ candidates, I.tail e = v)
    (hbound : I.objective (I.adjacencyFlow out) + (path.cost : ℝ) ≤ bound)
    (hdone : (run fuel (walkFrame out candidates path)).1.mode = .done) :
    ((run fuel (walkFrame out candidates path)).1.result = none ∧ 0 ≤ bound) ∨
      ∃ es : List (Fin I.m), ∃ v : Fin I.n, ∃ p : I.DirectedWalk v v,
        (run fuel (walkFrame out candidates path)).1.result = some es ∧
          p.edges = es ∧ ∀ e, p.count e ≤ 1 := by
  cases fuel with
  | zero => cases hdone
  | succ fuel =>
    have hr : (run (fuel + 1) (walkFrame out candidates path)).1 =
        (run fuel (walkFrame out candidates path).step).1 := by
      simp only [run, walkFrame, reduceCtorEq, ↓reduceIte]
    cases ho : out current with
    | nil =>
      obtain ⟨heq, hedges⟩ := path.edges_nil_of_no_outgoing hp out ho hb
      have hvertices : path.vertices = [current] := by rw [path.vertices_of_edges_nil hedges, heq]
      rw [hr, walkFrame_end out candidates path ho hedges hvertices] at hdone ⊢
      apply scan_choose fuel bound out candidates hout _ _ _ hdone
      · intro v
        rw [hb, heq, sub_self]
      · intro v hv
        rcases hcover v hv with hvroot | he
        · have hvr : v = current := hvroot.trans heq.symm
          rw [hvr, ho] at hv
          exact False.elim (hv rfl)
        · exact he
      · have hc := path.cost_of_edges_nil hedges
        simpa only [hc, Int.cast_zero, add_zero] using hbound
    | cons e rest =>
      obtain ⟨ht, hactive⟩ := hout current e (by rw [ho]; exact List.mem_cons_self)
      subst current
      let nextOut := Function.update out (I.tail e) rest
      have hnout : ∀ v a, a ∈ nextOut v → I.tail a = v ∧ 0 < I.capacity a :=
        outgoing_pop_property out e rest ho _ hout
      have hnbalance := adjacencyFlow_pop_endpoint_balance out root e rest ho hb
      have hncover := outgoing_pop_coverage out e rest ho root candidates hcover
      have hcost := I.adjacencyFlow_pop_objective out (I.tail e) e rest ho rfl
      by_cases hseen : I.head e ∈ path.vertices
      · obtain ⟨p, q, hedge, hvertices, hpn, hqn, hdisj⟩ := path.split_simple_at_vertex hp (I.head e) hseen
        let phase := 2 + q.edges.length
        let es := q.toDirectedWalk.edges ++ [e]
        have hphase : (run phase (walkFrame out candidates path)).1 =
            finishPeelFrame nextOut candidates p es :=
          run_walk_repeat out candidates e rest ho path hseen p q hedge hvertices hqn hdisj
        obtain ⟨v, cycle, hcycle, hcount⟩ := q.closed_list_of_suffix e hactive hqn
        by_cases henough : phase ≤ fuel + 1
        · have heq : fuel + 1 = phase + (fuel + 1 - phase) := by omega
          rw [heq, run_value_add, hphase] at hdone ⊢
          by_cases hneg : (es.map I.cost).sum < 0
          · simp only [finishPeelFrame, hneg, ↓reduceIte] at hdone ⊢
            rw [run_value_of_done _ _ (by rfl)]
            exact Or.inr ⟨es, v, cycle, rfl, hcycle, hcount⟩
          · simp only [finishPeelFrame, hneg, ↓reduceIte] at hdone ⊢
            apply scan_walk (fuel + 1 - phase) bound nextOut candidates p hpn hnout hnbalance hncover _ hdone
            have hsplit := path.cost_eq_of_split p q hedge
            have hsplitreal : (path.cost : ℝ) = (q.cost : ℝ) + (p.cost : ℝ) := by exact_mod_cast hsplit
            have hescost : (es.map I.cost).sum = q.cost + I.cost e := by
              simp only [es, List.map_append, List.sum_append, List.map_cons, List.map_nil,
                List.sum_cons, List.sum_nil, add_zero, DirectedWalk.sum_cost_edges, ReverseWalk.cost_toDirectedWalk]
            have hnon : (0 : ℝ) ≤ (q.cost : ℝ) + (I.cost e : ℝ) := by
              have hh : 0 ≤ q.cost + I.cost e := by rw [← hescost]; exact le_of_not_gt hneg
              exact_mod_cast hh
            change I.objective (I.adjacencyFlow nextOut) = I.objective (I.adjacencyFlow out) - (I.cost e : ℝ) at hcost
            linarith only [hcost, hsplitreal, hbound, hnon]
        · have hle : fuel + 1 ≤ phase := by omega
          have heq : finishPeelFrame nextOut candidates p es =
              (run (fuel + 1) (walkFrame out candidates path)).1 :=
            hphase.symm.trans (run_value_eq_of_done_prefix _ _ _ hle hdone)
          rw [← heq] at hdone ⊢
          by_cases hneg : (es.map I.cost).sum < 0
          · simp only [finishPeelFrame, hneg, ↓reduceIte]
            exact Or.inr ⟨es, v, cycle, rfl, hcycle, hcount⟩
          · simp only [finishPeelFrame, hneg, ↓reduceIte, walkFrame, reduceCtorEq] at hdone
      · rw [hr, walkFrame_extend out candidates e rest path hactive ho hseen] at hdone ⊢
        apply scan_walk fuel bound nextOut candidates (ReverseWalk.snoc e hactive path)
          (List.nodup_cons.mpr ⟨hseen, hp⟩) hnout hnbalance hncover _ hdone
        change I.objective (I.adjacencyFlow nextOut) = I.objective (I.adjacencyFlow out) - (I.cost e : ℝ) at hcost
        simp only [ReverseWalk.cost, Int.cast_add]
        linarith only [hcost, hbound]
termination_by fuel
  decreasing_by all_goals omega
end

/-- The complete scan returns a closed edge-simple walk, or its input unit
circulation has nonnegative cost. This is the extraction step used by C.10. -/
theorem extractCycleModel_closed_or_nonnegative (I : Circulation) (flow : Fin I.m → ℤ)
    (hunit : ∀ e, 0 ≤ flow e ∧ flow e ≤ 1)
    (hfeas : I.Feasible (fun e => (flow e : ℝ))) :
    ((I.extractCycleModel flow).1.result = none ∧ 0 ≤ I.integerObjective flow) ∨
      ∃ es : List (Fin I.m), ∃ v : Fin I.n, ∃ p : I.DirectedWalk v v,
        (I.extractCycleModel flow).1.result = some es ∧ p.edges = es ∧ ∀ e, p.count e ≤ 1 := by
  have hout : ∀ v e, e ∈ I.buildAdjacency flow v → I.tail e = v ∧ 0 < I.capacity e := by
    intro v e he
    have hh := (I.buildAdjacency_mem flow e v).mp he
    have hp : (0 : ℝ) < flow e := Int.cast_pos.mpr hh.1
    have hc : (0 : ℝ) < I.capacity e := lt_of_lt_of_le hp (hfeas.2 e).2
    exact ⟨hh.2.symm, by exact_mod_cast hc⟩
  have hflow := I.adjacencyFlow_build flow hunit
  have hb : ∀ v, I.balance (I.adjacencyFlow (I.buildAdjacency flow)) v = 0 := by
    rw [hflow]
    exact hfeas.1
  have hcover : ∀ v, I.buildAdjacency flow v ≠ [] →
      ∃ e ∈ List.finRange I.m, I.tail e = v := by
    intro v hv
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hv
    exact ⟨e, List.mem_finRange _, ((I.buildAdjacency_mem flow e v).mp he).2.symm⟩
  have hbound : I.objective (I.adjacencyFlow (I.buildAdjacency flow)) ≤
      (I.integerObjective flow : ℝ) := by
    rw [hflow, I.integerObjective_cast]
  have hd := I.extractCycleModel_done flow
  have hh := scan_choose (6 * I.m + 1) (I.integerObjective flow : ℝ)
    (I.buildAdjacency flow) (List.finRange I.m) hout hb hcover hbound hd
  rcases hh with hh | hh
  · exact Or.inl ⟨hh.1, (Int.cast_nonneg_iff (R := ℝ)).mp hh.2⟩
  · exact Or.inr hh

end MinCostFlow.Scaling.Circulation
