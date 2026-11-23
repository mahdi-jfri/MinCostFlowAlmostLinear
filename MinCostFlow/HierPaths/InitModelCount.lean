module

public import MinCostFlow.HierPaths.IndexStatic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Counting the work of flattening

This file counts what the end of `Init` handles. `card_connRecs_le`: there are at most
`leafDepth · 2^b · 2^x` connectors, since a group of size `s` at depth `t` has fewer than `r²`
pairs of children (`r` children) with `s / r` connectors each, and the groups of one depth have
`2^x` members in total.

`flatSteps` is the step count of `flatWalk`: at each depth, one step per edge of the walk and one
per edge of its substitution (`substSteps`). `flatSteps_le`: when every local bound `d k` is at
least one, flattening a walk of `ℓ` edges from depth `t` takes at most
`t · 2 · ℓ · ∏_{k < t} d k` steps.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The steps of `flatWalk`: the substitution steps at each depth. -/
def flatSteps (H : HierData) (x b : ℕ) : ℕ → ℕ → ℕ → List ℕ → ℕ
  | 0, _, _, _ => 0
  | t + 1, g, s, es =>
    substSteps (H.emb t g) es +
      flatSteps H x b t (parentGroup x b t g) s (substWalk (H.host (t + 1) g).edges (H.emb t g) s es)

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp HierData

variable {x b : ℕ} {H : HierData}

private theorem length_conn_le (hH : H.IsValid x b) {t g c c' : ℕ} (hs : 1 < groupSize x b t)
    (hg : g < numGroups x b t) (hc : c ∈ childGroups x b t g) (hc' : c' ∈ childGroups x b t g)
    (hcc : c < c') : (H.conn t c c').length ≤ groupSize x b (t + 1) := by
  obtain ⟨h1, h2, _, _⟩ := hH.conn_perfect t g hs hg c hc c' hc' hcc
  rw [← List.length_map (f := Prod.fst), ← List.toFinset_card_of_nodup h1, h2, card_members]

/-- **The number of connectors** is at most `leafDepth · 2^b · 2^x`. -/
theorem card_connRecs_le (hb : 0 < b) (hH : H.IsValid x b) :
    (connRecs H x b).length ≤ leafDepth x b * (2 ^ b * 2 ^ x) := by
  unfold connRecs
  rw [List.length_flatMap]
  refine (sum_map_le_length_mul' fun t ht => ?_).trans (by rw [List.length_range])
  have hs := one_lt_groupSize_of_lt_leafDepth hb (List.mem_range.mp ht)
  rw [List.length_flatMap]
  have hgrp : ∀ g ∈ List.range (numGroups x b t),
      ((childList x b t g).flatMap fun c => (childList x b t g).flatMap fun c' =>
        pairRecs H x b t g c c').length ≤ branching x b t * groupSize x b t := by
    intro g hg
    have hg' := List.mem_range.mp hg
    rw [List.length_flatMap]
    refine (sum_map_le_length_mul' (K := branching x b t * groupSize x b (t + 1))
      fun c hc => ?_).trans ?_
    · rw [List.length_flatMap]
      refine (sum_map_le_length_mul' (K := groupSize x b (t + 1)) fun c' hc' => ?_).trans ?_
      · unfold pairRecs
        split_ifs with hcc
        · rw [List.length_map]
          exact length_conn_le hH hs hg' (mem_childList.mp hc) (mem_childList.mp hc') hcc
        · exact Nat.zero_le _
      · rw [length_childList]
    · rw [length_childList, groupSize_eq_mul_branching (j := t)]
  refine (sum_map_le_length_mul' hgrp).trans ?_
  rw [List.length_range, ← Nat.mul_assoc, Nat.mul_comm (numGroups x b t), Nat.mul_assoc,
    numGroups_mul_groupSize]
  exact Nat.mul_le_mul_right _ (branching_le hs)

/-- **The steps of flattening.** With local bounds `d k ≥ 1`, flattening a walk `es` of the host
of group `g` at depth `t` takes at most `t · (2 · |es| · ∏_{k < t} d k)` steps. -/
theorem flatSteps_le (hH : H.IsValid x b) {d ρ κ : ℕ → ℕ} (hB : H.Bounds x b d ρ κ)
    (hd : ∀ k, 1 ≤ d k) :
    ∀ {t g : ℕ}, 1 < groupSize x b t → g < numGroups x b t → ∀ {u v : ℕ} {es : List ℕ},
      IsEdgeWalk (H.host t g).edges u v es →
        flatSteps H x b t g u es ≤ t * (2 * (es.length * ∏ k ∈ Finset.range t, d k))
  | 0, g, _, _, u, v, es, _ => by simp [flatSteps]
  | t + 1, g, hs, hg, u, v, es, hW => by
    unfold flatSteps
    have hW' := substWalk_isEdgeWalk hW fun j hj => hH.emb_walk hs hg (hW.lt_length j hj)
    have hL : ∀ j ∈ es, (H.emb t g j).length ≤ d t :=
      fun j hj => hB.emb_length t g hs hg j (hW.lt_length j hj)
    have h1 := flatSteps_le hH hB hd (hs.trans_le (groupSize_succ_le t))
      (parentGroup_lt_numGroups hg) hW'
    have h2 : (substWalk (H.host (t + 1) g).edges (H.emb t g) u es).length ≤ es.length * d t :=
      length_substWalk_le hL
    have h3 := substSteps_le hL
    have hP : 0 < ∏ k ∈ Finset.range t, d k := Finset.prod_pos fun k _ => hd k
    have hdt := hd t
    set P := ∏ k ∈ Finset.range t, d k
    set ℓ := es.length
    set ℓ' := (substWalk (H.host (t + 1) g).edges (H.emb t g) u es).length
    rw [Finset.prod_range_succ]
    have e1 : ℓ * (1 + d t) ≤ 2 * (ℓ * (P * d t)) := by
      have : ℓ * (1 + d t) ≤ ℓ * (2 * d t) := Nat.mul_le_mul_left _ (by omega)
      calc ℓ * (1 + d t) ≤ ℓ * (2 * d t) := this
        _ = 2 * (ℓ * (1 * d t)) := by ring
        _ ≤ 2 * (ℓ * (P * d t)) := by gcongr; exact hP
    have e2 : t * (2 * (ℓ' * P)) ≤ t * (2 * (ℓ * (P * d t))) := by
      have : ℓ' * P ≤ ℓ * (P * d t) :=
        calc ℓ' * P ≤ ℓ * d t * P := Nat.mul_le_mul_right _ h2
          _ = ℓ * (P * d t) := by ring
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
    calc substSteps (H.emb t g) es + flatSteps H x b t (parentGroup x b t g) u
          (substWalk (H.host (t + 1) g).edges (H.emb t g) u es)
        ≤ 2 * (ℓ * (P * d t)) + t * (2 * (ℓ * (P * d t))) := Nat.add_le_add (h3.trans e1) (h1.trans e2)
      _ = (t + 1) * (2 * (ℓ * (P * d t))) := by ring

end MinCostFlow.HierPaths
