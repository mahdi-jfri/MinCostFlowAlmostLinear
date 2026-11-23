module

public import MinCostFlow.HierPaths.Index
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The connectors of a terminal

For each terminal `u`, the data structure stores the numbers of the connectors that have `u` as
an endpoint (`termConns`). When `u` is lost, these connectors become ineligible. This file proves
that there are at most `leafDepth · (B − 1)` of them, with `B = 2 ^ b`
(`length_termConns_le`): at each depth, `u` lies in one child `c_u` of one group, and the
connectors with endpoint `u` at that depth come from the matchings between `c_u` and each of its
fewer than `B` siblings, where `u` is matched exactly once.

It also gives the fact that `vol_prunedSet_le` (`HierPaths/Live.lean`) needs for the initial pruned set:
every vertex owns a terminal (`connSystem_owner_surj`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-- The connectors with endpoint `u`. -/
def termConns (H : HierData) (x b : ℕ) (u : ℕ) : List ℕ :=
  (List.range (connRecs H x b).length).filter fun k =>
    ((connRecs H x b).getD k default).endA = u ∨ ((connRecs H x b).getD k default).endB = u

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner HierData

variable {x b : ℕ} {H : HierData}

/-- Every vertex of positive degree owns a terminal, when it owns at least its degree in
terminals. -/
theorem connSystem_owner_surj {G : Graph} {owner : ℕ → ℕ} {label : ℕ → Option ℕ}
    (hdeg : ∀ v, G.deg v ≤ ((Finset.range (2 ^ x)).filter fun p => owner p = v).card)
    (hpos : ∀ w < G.n, 1 ≤ G.deg w) :
    ∀ w < G.n, ∃ t < (connSystem H x b owner label).numTerm,
      (connSystem H x b owner label).owner t = w := by
  intro w hw
  have h := (hpos w hw).trans (hdeg w)
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  rw [Finset.mem_filter, Finset.mem_range] at hp
  exact ⟨p, hp.1, hp.2⟩

theorem mem_termConns {u k : ℕ} : k ∈ termConns H x b u ↔ k < (connRecs H x b).length ∧
    (((connRecs H x b).getD k default).endA = u ∨ ((connRecs H x b).getD k default).endB = u) := by
  simp [termConns]

private theorem length_filter_range_getD {α : Type*} [Inhabited α] (l : List α)
    (p : α → Prop) [DecidablePred p] :
    ((List.range l.length).filter fun k => p (l.getD k default)).length =
      (l.filter fun a => p a).length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append,
      List.filter_append, List.length_append, List.length_append]
    have h1 : ((List.range l.length).filter fun k => p ((l ++ [a]).getD k default)) =
        (List.range l.length).filter fun k => p (l.getD k default) := by
      apply List.filter_congr
      intro k hk
      rw [List.getD_append _ _ _ _ (List.mem_range.mp hk)]
    rw [h1, ih]
    congr 1
    have ha : (l ++ [a]).getD l.length default = a := by simp [List.getD_eq_getElem?_getD]
    simp only [List.filter_cons, List.filter_nil, ha]
    split_ifs <;> rfl

/-- The number of matched pairs of one list with first entry `u` is at most one, and zero when
`u` is not in the first group. -/
private theorem length_filter_fst_le {l : List (ℕ × ℕ × List ℕ)} {S : Finset ℕ}
    (hnd : (l.map Prod.fst).Nodup) (hS : (l.map Prod.fst).toFinset = S) (u : ℕ) :
    (l.filter fun q => q.1 = u).length ≤ if u ∈ S then 1 else 0 := by
  have hc : (l.filter fun q => q.1 = u).length = (l.map Prod.fst).count u := by
    rw [List.count, List.countP_map, List.countP_eq_length_filter]
    congr 1
  rw [hc]
  split_ifs with hu
  · exact List.nodup_iff_count_le_one.mp hnd u
  · rw [← hS, List.mem_toFinset] at hu
    rw [List.count_eq_zero.mpr hu]

private theorem length_filter_snd_le {l : List (ℕ × ℕ × List ℕ)} {S : Finset ℕ}
    (hnd : (l.map fun q => q.2.1).Nodup) (hS : (l.map fun q => q.2.1).toFinset = S) (u : ℕ) :
    (l.filter fun q => q.2.1 = u).length ≤ if u ∈ S then 1 else 0 := by
  have hc : (l.filter fun q => q.2.1 = u).length = (l.map fun q => q.2.1).count u := by
    rw [List.count, List.countP_map, List.countP_eq_length_filter]
    congr 1
  rw [hc]
  split_ifs with hu
  · exact List.nodup_iff_count_le_one.mp hnd u
  · rw [← hS, List.mem_toFinset] at hu
    rw [List.count_eq_zero.mpr hu]

private theorem length_filter_or_le {α : Type*} (l : List α) (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] :
    (l.filter fun a => p a ∨ q a).length ≤ (l.filter fun a => p a).length +
      (l.filter fun a => q a).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons]
    by_cases hp : p a <;> by_cases hq : q a <;>
      simp only [hp, hq, or_true, or_false, decide_true, decide_false, ↓reduceIte,
        List.length_cons, Bool.false_eq_true] <;> omega

private theorem length_filter_flatMap {α β : Type*} (l : List α) (f : α → List β) (p : β → Prop)
    [DecidablePred p] :
    ((l.flatMap f).filter fun r => p r).length =
      (l.map fun a => ((f a).filter fun r => p r).length).sum := by
  rw [List.filter_flatMap, List.length_flatMap]

private theorem toFinset_childList (t g : ℕ) :
    (childList x b t g).toFinset = childGroups x b t g := by
  ext c; rw [List.mem_toFinset, mem_childList]

private theorem nodup_childList (t g : ℕ) : (childList x b t g).Nodup := List.nodup_range'

private theorem sum_childList {f : ℕ → ℕ} (t g : ℕ) :
    ((childList x b t g).map f).sum = ∑ c ∈ childGroups x b t g, f c := by
  rw [← toFinset_childList, List.sum_toFinset _ (nodup_childList t g)]

/-- The connectors of one pair of children with endpoint `u`: at most one from each side. -/
private theorem length_pairRecs_filter_le (hH : H.IsValid x b) {t g c c' : ℕ}
    (hs : 1 < groupSize x b t) (hg : g < numGroups x b t) (hc : c ∈ childGroups x b t g)
    (hc' : c' ∈ childGroups x b t g) (u : ℕ) :
    ((pairRecs H x b t g c c').filter fun r => r.endA = u ∨ r.endB = u).length ≤
      if c < c' then (if groupOf x b (t + 1) u = c then 1 else 0) +
        (if groupOf x b (t + 1) u = c' then 1 else 0) else 0 := by
  unfold pairRecs
  by_cases hcc : c < c'
  · simp only [eq_true hcc, ↓reduceIte]
    obtain ⟨h1, h2, h3, h4⟩ := hH.conn_perfect t g hs hg c hc c' hc' hcc
    rw [List.filter_map, List.length_map]
    refine (length_filter_or_le _ (fun q : ℕ × ℕ × List ℕ => q.1 = u)
      (fun q : ℕ × ℕ × List ℕ => q.2.1 = u)).trans ?_
    have e1 := length_filter_fst_le h1 h2 u
    have e2 := length_filter_snd_le h3 h4 u
    simp only [mem_members_iff] at e1 e2
    exact Nat.add_le_add e1 e2
  · simp [hcc]

/-- At one group, the connectors with endpoint `u` number at most `branching − 1`, and none
unless the child of `u` is a child of the group. -/
private theorem sum_pairs_le (t g : ℕ) (cu : ℕ) :
    ∑ c ∈ childGroups x b t g, ∑ c' ∈ childGroups x b t g,
      (if c < c' then (if cu = c then 1 else 0) + (if cu = c' then 1 else 0) else 0) ≤
        if cu ∈ childGroups x b t g then branching x b t - 1 else 0 := by
  set S := childGroups x b t g
  have hsplit : ∀ c c', (if c < c' then (if cu = c then 1 else 0) + (if cu = c' then 1 else 0)
      else 0) = (if cu = c then (if c < c' then 1 else 0) else 0) +
        (if cu = c' then (if c < c' then 1 else 0) else 0) := by
    intro c c'
    split_ifs <;> omega
  have hpush : ∀ (f : ℕ → ℕ → ℕ) (c : ℕ), ∑ c' ∈ S, (if cu = c then f c c' else 0) =
      if cu = c then ∑ c' ∈ S, f c c' else 0 := by
    intro f c; split_ifs <;> simp
  simp only [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := S) (t := S)
    (f := fun c c' => if cu = c' then (if c < c' then 1 else 0) else 0)]
  simp only [hpush (fun c c' => if c < c' then 1 else 0),
    hpush (fun c' c => if c < c' then 1 else 0), Finset.sum_ite_eq]
  split_ifs with hcu
  · simp only [Finset.sum_boole]
    have hdisj : Disjoint (S.filter fun c' => cu < c') (S.filter fun c => c < cu) := by
      rw [Finset.disjoint_filter]; intro _ _ h1 h2; omega
    have hsub : (S.filter fun c' => cu < c') ∪ (S.filter fun c => c < cu) ⊆ S.erase cu := by
      intro c hc
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hc
      rw [Finset.mem_erase]
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by omega, h1⟩
      · exact ⟨by omega, h1⟩
    have h := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hcu, card_childGroups] at h
    exact h
  · simp

/-- **The connectors of a terminal.** A terminal is an endpoint of at most `leafDepth · (B − 1)`
connectors, with `B = 2 ^ b`. -/
theorem length_termConns_le (hb : 0 < b) (hH : H.IsValid x b) (u : ℕ) :
    (termConns H x b u).length ≤ leafDepth x b * (2 ^ b - 1) := by
  unfold termConns
  rw [length_filter_range_getD (connRecs H x b) (fun r => r.endA = u ∨ r.endB = u)]
  unfold connRecs
  rw [length_filter_flatMap]
  refine (sum_map_le_length_mul' fun t ht => ?_).trans (by rw [List.length_range])
  have ht' := List.mem_range.mp ht
  have hs := one_lt_groupSize_of_lt_leafDepth hb ht'
  rw [length_filter_flatMap]
  have hg_step : ∀ g ∈ List.range (numGroups x b t),
      (((childList x b t g).flatMap fun c => (childList x b t g).flatMap fun c' =>
        pairRecs H x b t g c c').filter fun r => r.endA = u ∨ r.endB = u).length ≤
        if parentGroup x b t (groupOf x b (t + 1) u) = g then branching x b t - 1 else 0 := by
    intro g hg
    have hg' := List.mem_range.mp hg
    rw [length_filter_flatMap, sum_childList]
    have hin : ∀ c ∈ childGroups x b t g,
        (((childList x b t g).flatMap (fun c' => pairRecs H x b t g c c')).filter
          (fun r => r.endA = u ∨ r.endB = u)).length =
        ∑ c' ∈ childGroups x b t g,
          ((pairRecs H x b t g c c').filter fun r => r.endA = u ∨ r.endB = u).length :=
      fun c _ => by rw [length_filter_flatMap, sum_childList]
    rw [Finset.sum_congr rfl hin]
    refine (Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun c' hc' =>
      length_pairRecs_filter_le hH hs hg' hc hc' u).trans ?_
    refine (sum_pairs_le t g _).trans (le_of_eq ?_)
    simp only [mem_childGroups_iff]
  refine (List.sum_le_sum fun g hg => hg_step g hg).trans ?_
  calc ((List.range (numGroups x b t)).map (fun g =>
          if parentGroup x b t (groupOf x b (t + 1) u) = g then branching x b t - 1
          else 0)).sum
      ≤ branching x b t - 1 := by
        rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.sum_ite_eq]
        split_ifs <;> omega
    _ ≤ 2 ^ b - 1 := Nat.sub_le_sub_right (branching_le hs) 1

end MinCostFlow.HierPaths
