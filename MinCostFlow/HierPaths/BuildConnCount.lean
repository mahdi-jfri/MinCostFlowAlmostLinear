module

public import MinCostFlow.HierPaths.BuildConn
public import MinCostFlow.HierPaths.BuildProgEraseCost
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Each terminal lies in `k − 1` connectors

The last claim about sibling connectors: a terminal `t` of a child `ch c` is an end of exactly
`k − 1` connectors of the group. The connectors of a pair `(a, b)` form a perfect matching between
`ch a` and `ch b` (`siblingConns_perfect`). So `t` is an end of exactly one of them when `c` is `a` or
`b`, and of none otherwise, since the children are disjoint. Exactly `k − 1` of the pairs
`a < b < k` contain `c` (`countP_pairsBelow`).

Main result: `countP_connList`. The cost of the connector calls, `connCost` (router calls and
the shortcuts of their walks), is bounded by `connCost_le_of` in `BuildCost.lean`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- All connectors of the group, with their ends. -/
def connList (route : RouterFn) (G : Graph) (X : Finset ℕ) (Δ L : ℕ) (ch : ℕ → Finset ℕ)
    (k : ℕ) : List ((ℕ × ℕ) × List ℕ) :=
  (pairsBelow k).flatMap fun p => siblingConns route G X Δ L ch p.1 p.2

/-- The total cost of the connector calls of the group, with the shortcuts of their walks. -/
def connCost (route : RouterFn) (routeCost : RouterCostFn) (G : Graph) (X : Finset ℕ) (Δ L : ℕ)
    (ch : ℕ → Finset ℕ) (k : ℕ) : ℕ :=
  ((pairsBelow k).map fun p =>
    callCost route routeCost G X [(ch p.1, ch p.2)] Δ L).sum

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Exactly `k − 1` of the pairs `a < b < k` contain a given `c < k`, and none contains `c ≥ k`. -/
theorem countP_pairsBelow (k c : ℕ) :
    (pairsBelow k).countP (fun p => decide (p.1 = c ∨ p.2 = c)) = if c < k then k - 1 else 0 := by
  induction k with
  | zero => simp [pairsBelow]
  | succ k ih =>
    have hsplit : pairsBelow (k + 1) = pairsBelow k ++ (List.range k).map fun a => (a, k) := by
      simp [pairsBelow, List.range_succ, List.flatMap_append]
    rw [hsplit, List.countP_append, ih, List.countP_map]
    by_cases hck : c < k
    · have hnew : (List.range k).countP ((fun p : ℕ × ℕ => decide (p.1 = c ∨ p.2 = c)) ∘
          fun a => (a, k)) = 1 := by
        have : ((fun p : ℕ × ℕ => decide (p.1 = c ∨ p.2 = c)) ∘ fun a => (a, k)) =
            fun a => a == c := by
          funext a
          simp only [Function.comp_apply]
          by_cases h : a = c <;> simp [h, show k ≠ c by omega]
        rw [this, ← List.count]
        exact List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr hck)
      rw [hnew, ite_eq_left hck, ite_eq_left (by omega)]
      omega
    · by_cases hck' : c = k
      · subst hck'
        have hnew : (List.range c).countP ((fun p : ℕ × ℕ => decide (p.1 = c ∨ p.2 = c)) ∘
            fun a => (a, c)) = c := by
          rw [List.countP_eq_length.mpr (by intro a _; simp)]
          simp
        rw [hnew, ite_eq_right hck, ite_eq_left (by omega)]
        omega
      · have hnew : (List.range k).countP ((fun p : ℕ × ℕ => decide (p.1 = c ∨ p.2 = c)) ∘
            fun a => (a, k)) = 0 := by
          rw [List.countP_eq_zero]
          intro a ha
          have := List.mem_range.mp ha
          simp only [Function.comp_apply, decide_eq_true_eq, not_or]
          omega
        rw [hnew, ite_eq_right hck, ite_eq_right (by omega)]

/-- A sum of indicators is a count. -/
private theorem sum_ite_eq_countP {α : Type*} (l : List α) (Q : α → Bool) :
    (l.map fun x => if Q x = true then 1 else 0).sum = l.countP Q := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    split_ifs <;> simp_all [Nat.add_comm]

/-- **Connectors, incidences.** A terminal `t` of the child `ch c`, `c < k`, is an end of exactly
`k − 1` connectors of the group. -/
theorem countP_connList {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {ch : ℕ → Finset ℕ} {k s : ℕ} (hch : IsChildren X ch k s)
    {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ)) {c t : ℕ} (hc : c < k) (ht : t ∈ ch c) :
    (connList route G X Δ L ch k).countP (fun cn => decide (cn.1.1 = t ∨ cn.1.2 = t)) = k - 1 := by
  have hdisj := hch.2.2
  have hper : ∀ p ∈ pairsBelow k,
      (siblingConns route G X Δ L ch p.1 p.2).countP (fun cn => decide (cn.1.1 = t ∨ cn.1.2 = t)) =
        if decide (p.1 = c ∨ p.2 = c) = true then 1 else 0 := by
    intro p hp
    obtain ⟨ha, hb, hab⟩ := (pairsBelow_spec k).2 p hp
    obtain ⟨_, hnd1, hfs1, hnd2, hfs2⟩ :=
      siblingConns_perfect hrouter hH hch hβ hexp hbh ha hb (by omega)
    set cs := siblingConns route G X Δ L ch p.1 p.2
    have hmem1 : ∀ cn ∈ cs, cn.1.1 ∈ ch p.1 := fun cn hcn => by
      rw [← hfs1]; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨cn, hcn, rfl⟩)
    have hmem2 : ∀ cn ∈ cs, cn.1.2 ∈ ch p.2 := fun cn hcn => by
      rw [← hfs2]; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨cn, hcn, rfl⟩)
    have hnot : ∀ {c'}, c' < k → c' ≠ c → t ∉ ch c' := fun hc' hne htc =>
      Finset.disjoint_left.mp (hdisj c hc _ hc' (Ne.symm hne)) ht htc
    by_cases h1 : p.1 = c
    · have hnt2 : t ∉ ch p.2 := hnot hb (by omega)
      have hq : (cs.countP fun cn => decide (cn.1.1 = t ∨ cn.1.2 = t)) =
          (cs.map fun cn => cn.1.1).count t := by
        rw [List.count, List.countP_map]
        apply List.countP_congr
        intro cn hcn
        have : cn.1.2 ≠ t := fun h => hnt2 (h ▸ hmem2 cn hcn)
        simp [this]
      rw [hq, List.count_eq_one_of_mem hnd1 (List.mem_toFinset.mp (by rw [hfs1, h1]; exact ht))]
      simp [h1]
    · by_cases h2 : p.2 = c
      · have hnt1 : t ∉ ch p.1 := hnot ha h1
        have hq : (cs.countP fun cn => decide (cn.1.1 = t ∨ cn.1.2 = t)) =
            (cs.map fun cn => cn.1.2).count t := by
          rw [List.count, List.countP_map]
          apply List.countP_congr
          intro cn hcn
          have : cn.1.1 ≠ t := fun h => hnt1 (h ▸ hmem1 cn hcn)
          simp [this]
        rw [hq, List.count_eq_one_of_mem hnd2 (List.mem_toFinset.mp (by rw [hfs2, h2]; exact ht))]
        simp [h2]
      · have hnt1 : t ∉ ch p.1 := hnot ha h1
        have hnt2 : t ∉ ch p.2 := hnot hb h2
        rw [List.countP_eq_zero.mpr]
        · simp [h1, h2]
        · intro cn hcn
          have e1 : cn.1.1 ≠ t := fun h => hnt1 (h ▸ hmem1 cn hcn)
          have e2 : cn.1.2 ≠ t := fun h => hnt2 (h ▸ hmem2 cn hcn)
          simp [e1, e2]
  unfold connList
  rw [List.countP_flatMap]
  have : ((pairsBelow k).map ((List.countP fun cn : (ℕ × ℕ) × List ℕ =>
      decide (cn.1.1 = t ∨ cn.1.2 = t)) ∘ fun p => siblingConns route G X Δ L ch p.1 p.2)) =
      (pairsBelow k).map fun p => if decide (p.1 = c ∨ p.2 = c) = true then 1 else 0 := by
    apply List.map_congr_left
    intro p hp
    exact hper p hp
  rw [this, sum_ite_eq_countP, countP_pairsBelow, ite_eq_left hc]

end MinCostFlow.HierPaths
