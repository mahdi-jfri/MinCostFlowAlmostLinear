module

public import MinCostFlow.HierPaths.BuildChild
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD

/-!
# List facts for the batched game of `lemma_3`

* `witnessEdges_congr`, `witnessEdges_eq_flatten`: the game graph of a child is the list of the
  local edges of its rounds.
* `filter_flatten_single`: filtering a flattened list by a test that only the entries of one
  inner list pass gives that inner list.
* `validTerminalPairs_of_children`: the requests of distinct children form valid terminal pairs.
* `sum_occLoad_filter_le`: splitting a family by exclusive tests does not raise the total load.
* `occLoad_rawEntries_le`, `occLoad_callEntries_le`: the walks of one call use each host edge at
  most `d · R` times, and at most `R` times when they repeat no edge, as the shortcut walks of
  `callEntries` do.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The family of walks of a list of entries, with the first ends as starts. -/
@[expose] def walkFamily (l : List ((ℕ × ℕ) × List ℕ)) : List (ℕ × List ℕ) :=
  l.map fun en => (en.1.1, en.2)

/-- The witness graph after `j` rounds only depends on the first `j` matchings. -/
theorem witnessEdges_congr {M M' : ℕ → List (ℕ × ℕ)} {j : ℕ} (h : ∀ j' < j, M j' = M' j') :
    witnessEdges M j = witnessEdges M' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [witnessEdges]
    rw [ih fun j' hj' => h j' (by omega), h j (by omega)]

/-- The game graph of a list of rounds is the list of their local edges. -/
theorem witnessEdges_eq_flatten (l : List (List ((ℕ × ℕ) × List ℕ))) :
    witnessEdges (fun j => (l.getD j []).map Prod.fst) l.length = (l.flatten).map Prod.fst := by
  have key : ∀ j ≤ l.length, witnessEdges (fun j => (l.getD j []).map Prod.fst) j =
      ((l.take j).flatten).map Prod.fst := by
    intro j hj
    induction j with
    | zero => simp [witnessEdges]
    | succ j ih =>
      simp only [witnessEdges]
      rw [ih (by omega), List.take_add_one, List.flatten_append, List.map_append]
      congr 1
      rw [List.getElem?_eq_getElem (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < l.length by omega)]
  rw [key l.length le_rfl, List.take_length]

/-- If exactly the entries of the inner list number `i` pass the test, the filtered flattened list
is that inner list. -/
theorem filter_flatten_single {α : Type*} {Ms : List (List α)} {P : α → Bool} {i : ℕ}
    (hi : i < Ms.length) (hP : ∀ i' (hi' : i' < Ms.length), ∀ x ∈ Ms[i'], P x = true ↔ i' = i) :
    Ms.flatten.filter P = Ms[i] := by
  induction Ms generalizing i with
  | nil => simp at hi
  | cons m Ms ih =>
    rw [List.flatten_cons, List.filter_append]
    cases i with
    | zero =>
      have h1 : m.filter P = m := List.filter_eq_self.mpr fun x hx => (hP 0 (by simp) x hx).mpr rfl
      have h2 : Ms.flatten.filter P = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx hPx
        obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hx
        obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hl
        have := (hP (i' + 1) (by simp; omega) x (by simpa using hxl)).mp hPx
        omega
      rw [h1, h2, List.append_nil]
      rfl
    | succ i =>
      have h1 : m.filter P = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx hPx
        have := (hP 0 (by simp) x hx).mp hPx
        omega
      rw [h1, List.nil_append]
      simp only [List.getElem_cons_succ]
      apply ih (by simpa using hi)
      intro i' hi' x hx
      have := hP (i' + 1) (by simp; omega) x (by simpa using hx)
      simp only [Nat.add_right_cancel_iff] at this
      exact this

/-- **The requests of distinct children are valid terminal pairs.** Let `cs` be a list of distinct
children; child `c` owns the set `Y c ⊆ X`, the sets of distinct children are disjoint, and the
pair of `c` has two disjoint sets inside `Y c` with the first no larger. -/
theorem validTerminalPairs_of_children {X : Finset ℕ} {cs : List ℕ} (hnd : cs.Nodup)
    {Y : ℕ → Finset ℕ} {p : ℕ → Finset ℕ × Finset ℕ} (hY : ∀ c ∈ cs, Y c ⊆ X)
    (hdisj : ∀ c ∈ cs, ∀ c' ∈ cs, c ≠ c' → Disjoint (Y c) (Y c'))
    (hp : ∀ c ∈ cs, (p c).1 ⊆ Y c ∧ (p c).2 ⊆ Y c ∧ Disjoint (p c).1 (p c).2 ∧
      (p c).1.card ≤ (p c).2.card) :
    ValidTerminalPairs X (cs.map p) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
    obtain ⟨h1, h2, _, h4⟩ := hp c hc
    exact ⟨h1.trans (hY c hc), h2.trans (hY c hc), h4⟩
  · induction cs with
    | nil => simp
    | cons c cs ih =>
      have hnd' := List.nodup_cons.mp hnd
      have ih' := ih hnd'.2 (fun c' hc' => hY c' (List.mem_cons_of_mem _ hc'))
        (fun a ha b hb hab => hdisj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab)
        (fun c' hc' => hp c' (List.mem_cons_of_mem _ hc'))
      obtain ⟨h1, h2, h3, _⟩ := hp c List.mem_cons_self
      have hrest : ∀ T ∈ (cs.map p).flatMap (fun q => [q.1, q.2]), Disjoint (Y c) T := by
        intro T hT
        obtain ⟨q, hq, hTq⟩ := List.mem_flatMap.mp hT
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hq
        have hne : c ≠ c' := fun h => hnd'.1 (h ▸ hc')
        have hd := hdisj c List.mem_cons_self c' (List.mem_cons_of_mem _ hc') hne
        obtain ⟨h1', h2', _, _⟩ := hp c' (List.mem_cons_of_mem _ hc')
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hTq
        rcases hTq with rfl | rfl
        · exact hd.mono_right h1'
        · exact hd.mono_right h2'
      simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append,
        List.pairwise_cons, List.mem_cons]
      refine ⟨?_, ?_, ih'⟩
      · intro T hT
        rcases hT with rfl | hT
        · exact h3
        · exact (hrest T hT).mono_left h1
      · intro T hT
        exact (hrest T hT).mono_left h2

/-- **Splitting a family does not raise the load.** If at most one of the tests `P c`, `c < k`,
passes each entry, the loads of the filtered families add up to at most the load of the
family. -/
theorem sum_occLoad_filter_le {k : ℕ} {P : ℕ → ((ℕ × ℕ) × List ℕ) → Bool}
    (hP : ∀ x, ∀ c < k, ∀ c' < k, P c x = true → P c' x = true → c = c')
    (f : ((ℕ × ℕ) × List ℕ) → (ℕ × List ℕ)) (l : List ((ℕ × ℕ) × List ℕ)) (i : ℕ) :
    ∑ c ∈ Finset.range k, occLoad ((l.filter (P c)).map f) i ≤ occLoad (l.map f) i := by
  induction l with
  | nil => simp [occLoad]
  | cons x l ih =>
    have hsplit : ∀ c, occLoad (((x :: l).filter (P c)).map f) i =
        (if P c x = true then (f x).2.count i else 0) + occLoad ((l.filter (P c)).map f) i := by
      intro c
      rw [List.filter_cons]
      split_ifs <;> simp [occLoad]
    rw [Finset.sum_congr rfl fun c _ => hsplit c, Finset.sum_add_distrib]
    have hone : ∑ c ∈ Finset.range k, (if P c x = true then (f x).2.count i else 0) ≤
        (f x).2.count i := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_const, smul_eq_mul]
      have : ((Finset.range k).filter fun c => P c x = true).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [Finset.mem_filter, Finset.mem_range] at ha hb
        exact hP x a ha.1 b hb.1 ha.2 hb.2
      calc ((Finset.range k).filter fun c => P c x = true).card * (f x).2.count i
          ≤ 1 * (f x).2.count i := Nat.mul_le_mul_right _ this
        _ = (f x).2.count i := Nat.one_mul _
    have hx : occLoad ((x :: l).map f) i = (f x).2.count i + occLoad (l.map f) i := by
      simp [occLoad]
    rw [hx]
    omega

/-- **The load of one call.** If the walks of the call have at most `d` edges and every host edge
lies on at most `R` of them, each host edge occurs at most `d · R` times in all of them, and at
most `R` times when no walk repeats an edge. -/
theorem occLoad_rawEntries_le {n : ℕ} {F : List (ℕ × ℕ)} {emb : ℕ → List ℕ} {d R i : ℕ}
    (hlen : ∀ j < F.length, (emb j).length ≤ d)
    (hcong : congestion (Graph.mk n F) emb i ≤ R) :
    occLoad (walkFamily (rawEntries F emb)) i ≤ d * R ∧
      ((∀ j < F.length, (emb j).Nodup) →
        occLoad (walkFamily (rawEntries F emb)) i ≤ R) := by
  set N := F.length
  unfold congestion Graph.m at hcong
  simp only at hcong
  have hcard : ((List.range N).filter fun j => decide (i ∈ emb j)).length =
      ((Finset.range N).filter fun j => i ∈ emb j).card := by
    rw [length_filter_eq_card_range _ _ 0]
    simp only [List.length_range]
    congr 1
    apply Finset.filter_congr
    intro j hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  have hocc : occLoad (walkFamily (rawEntries F emb)) i =
      ((List.range N).map fun j => (emb j).count i).sum := by
    simp [occLoad, walkFamily, rawEntries, N, List.map_map, Function.comp_def]
  have hgen : ∀ (l : List ℕ) (b : ℕ), (∀ j ∈ l, (emb j).count i ≤ b) →
      (l.map fun j => (emb j).count i).sum ≤ (l.filter fun j => decide (i ∈ emb j)).length * b := by
    intro l b h
    induction l with
    | nil => simp
    | cons x l ih =>
      have hx := h x List.mem_cons_self
      have ih' := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
      simp only [List.map_cons, List.sum_cons, List.filter_cons]
      by_cases hxi : i ∈ emb x
      · simp only [hxi, decide_true, ite_true, List.length_cons, Nat.succ_mul]
        omega
      · simp only [hxi, decide_false, Bool.false_eq_true, ite_false]
        rw [List.count_eq_zero_of_not_mem hxi]
        omega
  have hfil : ((List.range N).filter fun j => decide (i ∈ emb j)).length ≤ R := by
    rw [hcard]; exact hcong
  constructor
  · rw [hocc]
    refine le_trans (hgen _ d fun j hj => le_trans List.count_le_length
      (hlen j (List.mem_range.mp hj))) ?_
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hfil
  · intro hnd
    rw [hocc]
    refine le_trans (hgen _ 1 fun j hj => ?_) (by rw [Nat.mul_one]; exact hfil)
    exact List.nodup_iff_count_le_one.mp (hnd j (List.mem_range.mp hj)) i

/-- **The load of one call, with shortcut walks.** If the walks `emb` are walks between the ends
of their edges and every host edge lies on at most `R` of them, then each host edge occurs at most
`R` times in the shortcut walks of the call: they repeat no edge, and each is a sublist of its
walk. -/
theorem occLoad_callEntries_le {n : ℕ} {E : List (ℕ × ℕ)} {Ms : List (List (ℕ × ℕ))}
    {emb : ℕ → List ℕ} {R i : ℕ}
    (hwalk : ∀ j < Ms.flatten.length,
      IsEdgeWalk E (edgeAt Ms.flatten j).1 (edgeAt Ms.flatten j).2 (emb j))
    (hcong : congestion (Graph.mk n Ms.flatten) emb i ≤ R) :
    occLoad (walkFamily (callEntries E (.matched Ms emb))) i ≤ R := by
  set emb' : ℕ → List ℕ := fun j => erase E (edgeAt Ms.flatten j).1 (emb j)
  have hspec : ∀ j < Ms.flatten.length, (emb' j).Sublist (emb j) ∧ (emb' j).Nodup := by
    intro j hj
    obtain ⟨_, h2, _, h4⟩ := erase_spec (emb j).length _ _ (emb j) le_rfl (hwalk j hj)
    exact ⟨h2, h4⟩
  have hcong' : congestion (Graph.mk n Ms.flatten) emb' i ≤ R := by
    refine le_trans ?_ hcong
    unfold congestion
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨hj.1, (hspec j hj.1).1.subset hj.2⟩
  have hlen : ∀ j < Ms.flatten.length,
      (emb' j).length ≤ ∑ j' ∈ Finset.range Ms.flatten.length, (emb' j').length :=
    fun j hj => Finset.single_le_sum (f := fun j' => (emb' j').length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
  exact (occLoad_rawEntries_le hlen hcong').2 (fun j hj => (hspec j hj).2)

end MinCostFlow.HierPaths
