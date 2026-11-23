module

public import MinCostFlow.HierPaths.Substitute

/-!
# Walks without repeated edges

The router's interface bounds the congestion by the number of walks through an edge, and its
walks may repeat edges. The loads `(T + 1) R_X` and `k² R_X` that we want need walks that repeat no
edge. This file shortcuts an edge walk to one that repeats no edge (`erase`).

The walk `erase u w` starts at `u`. It jumps to the last time `w` is at `u` (`lastFrom`), takes
the next edge `j` to a vertex `x`, and goes on from `x` with the rest. After the jump the walk
never comes back to `u`, so the rest of the shortcut walk does not meet `u`, and so it does not
use `j` again (both ends of `j` are `u` and `x`, and `x ≠ u`). The main result `erase_spec`: the
shortcut walk is a walk with the same ends, a sublist of `w` (so it is no longer and uses only
edges of `w`), and it repeats no edge.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The vertices of the walk `w` from `u`: `u`, then the vertex after each edge. -/
def walkVerts (E : List (ℕ × ℕ)) : ℕ → List ℕ → List ℕ
  | u, [] => [u]
  | u, j :: rest => u :: walkVerts E (otherEnd E j u) rest

/-- Walk along `w` from `cur`, and keep in `best` the rest of the walk from the last time the walk
is at `u`. -/
def lastFrom (E : List (ℕ × ℕ)) (u : ℕ) : ℕ → List ℕ → List ℕ → List ℕ
  | cur, [], best => if cur = u then [] else best
  | cur, j :: rest, best =>
    lastFrom E u (otherEnd E j cur) rest (if cur = u then j :: rest else best)

theorem lastFrom_cases (E : List (ℕ × ℕ)) (u : ℕ) :
    ∀ (cur : ℕ) (w best : List ℕ), lastFrom E u cur w best = best ∨ lastFrom E u cur w best <:+ w
  | cur, [], best => by
    simp only [lastFrom]
    split_ifs
    · right; exact List.nil_suffix
    · left; rfl
  | cur, j :: rest, best => by
    simp only [lastFrom]
    rcases lastFrom_cases E u (otherEnd E j cur) rest (if cur = u then j :: rest else best)
      with h | h
    · rw [h]
      split_ifs
      · right; exact List.suffix_refl _
      · left; rfl
    · right; exact h.trans (List.suffix_cons _ _)

theorem lastFrom_suffix (E : List (ℕ × ℕ)) (u : ℕ) (w : List ℕ) : lastFrom E u u w w <:+ w := by
  rcases lastFrom_cases E u u w w with h | h
  · rw [h]
  · exact h

-- The name `hl` is used in the termination proof, which the unused-variable linter does not see.
set_option linter.unusedVariables false in
/-- Shortcut the walk `w` from `u` to a walk that repeats no edge. -/
def erase (E : List (ℕ × ℕ)) (u : ℕ) (w : List ℕ) : List ℕ :=
  match hl : lastFrom E u u w w with
  | [] => []
  | j :: rest => j :: erase E (otherEnd E j u) rest
termination_by w.length
decreasing_by
  have := (lastFrom_suffix E u w).length_le
  rw [hl] at this
  simp only [List.length_cons] at this
  omega

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

variable {E : List (ℕ × ℕ)}

theorem otherEnd_eq {u x j : ℕ}
    (hend : ((edgeAt E j).1 = u ∧ (edgeAt E j).2 = x) ∨ ((edgeAt E j).1 = x ∧ (edgeAt E j).2 = u)) :
    otherEnd E j u = x := by
  unfold otherEnd
  rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [h1, h2, ite_true]
  · split_ifs with h3
    · rw [h2, ← h3, h1]
    · exact h1

theorem isEdgeWalk_head {u v j : ℕ} {es : List ℕ} (h : IsEdgeWalk E u v (j :: es)) :
    IsEdgeWalk E u (otherEnd E j u) [j] := by
  cases h with
  | cons hj hend _ =>
    rw [otherEnd_eq hend]
    exact IsEdgeWalk.cons hj hend (IsEdgeWalk.nil _)

theorem walkVerts_eq_cons (u : ℕ) (l : List ℕ) : walkVerts E u l = u :: (walkVerts E u l).tail := by
  cases l <;> rfl

theorem mem_walkVerts_self (u : ℕ) (l : List ℕ) : u ∈ walkVerts E u l := by
  rw [walkVerts_eq_cons]
  exact List.mem_cons_self

theorem walkVerts_append {x c : ℕ} {mid : List ℕ} (h : IsEdgeWalk E x c mid) (l : List ℕ) :
    walkVerts E x (mid ++ l) = walkVerts E x mid ++ (walkVerts E c l).tail := by
  induction h with
  | nil u =>
    simp only [List.nil_append, walkVerts]
    exact walkVerts_eq_cons u l
  | cons hj hend _ ih =>
    simp only [List.cons_append, walkVerts, otherEnd_eq hend, ih, List.cons_append]

/-- The ends of every edge of a walk are vertices of the walk. -/
theorem ends_mem_walkVerts {y v : ℕ} {w : List ℕ} (h : IsEdgeWalk E y v w) {j : ℕ} (hj : j ∈ w) :
    (edgeAt E j).1 ∈ walkVerts E y w ∧ (edgeAt E j).2 ∈ walkVerts E y w := by
  induction h with
  | nil u => simp at hj
  | cons hj' hend hrest ih =>
    rename_i u x v' j' es
    simp only [walkVerts, otherEnd_eq hend, List.mem_cons]
    rcases List.mem_cons.mp hj with rfl | hj
    · have hx := mem_walkVerts_self (E := E) x es
      rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact ⟨Or.inl rfl, Or.inr hx⟩
      · rw [h1, h2]; exact ⟨Or.inr hx, Or.inl rfl⟩
    · obtain ⟨a, b⟩ := ih hj
      exact ⟨Or.inr a, Or.inr b⟩

/-- **The jump of `lastFrom`.** -/
theorem lastFrom_spec {u v : ℕ} {S : List ℕ} (huS : u ∈ S) :
    ∀ (cur : ℕ) (w best : List ℕ), IsEdgeWalk E cur v w →
      (∀ y ∈ walkVerts E cur w, y ∈ S) → (∀ y ∈ walkVerts E u best, y ∈ S) →
      (cur = u ∨ ∃ j0 mid, best = j0 :: (mid ++ w) ∧ IsEdgeWalk E u cur (j0 :: mid) ∧
        u ∉ walkVerts E (otherEnd E j0 u) mid) →
      (∀ y ∈ walkVerts E u (lastFrom E u cur w best), y ∈ S) ∧
      ((lastFrom E u cur w best = [] ∧ v = u) ∨
        ∃ j rest, lastFrom E u cur w best = j :: rest ∧ IsEdgeWalk E u v (j :: rest) ∧
          u ∉ walkVerts E (otherEnd E j u) rest)
  | cur, [], best, hw, _, hbS, hinv => by
    cases hw
    simp only [lastFrom]
    split_ifs with hc
    · refine ⟨fun y hy => ?_, Or.inl ⟨rfl, hc⟩⟩
      simp only [walkVerts, List.mem_singleton] at hy
      rw [hy]; exact huS
    · refine ⟨hbS, Or.inr ?_⟩
      rcases hinv with h | ⟨j0, mid, hb, hwalk, hnot⟩
      · exact absurd h hc
      · rw [List.append_nil] at hb
        exact ⟨j0, mid, hb, hwalk, hnot⟩
  | cur, j :: rest, best, hw, hcS, hbS, hinv => by
    simp only [lastFrom]
    set cur' := otherEnd E j cur
    have hw' : IsEdgeWalk E cur' v rest := isEdgeWalk_tail_otherEnd hw
    have hcS' : ∀ y ∈ walkVerts E cur' rest, y ∈ S :=
      fun y hy => hcS y (by simp only [walkVerts]; exact List.mem_cons_of_mem _ hy)
    apply lastFrom_spec huS cur' rest _ hw' hcS'
    · split_ifs with hc
      · rw [← hc]; exact hcS
      · exact hbS
    · by_cases hc' : cur' = u
      · exact Or.inl hc'
      · right
        by_cases hc : cur = u
        · simp only [hc, ↓reduceIte]
          refine ⟨j, [], by simp, ?_, ?_⟩
          · rw [← hc]; exact isEdgeWalk_head hw
          · simp only [walkVerts, List.mem_singleton]
            rw [← hc]
            exact fun h => hc' (h.symm.trans hc)
        · simp only [hc, ↓reduceIte]
          rcases hinv with h | ⟨j0, mid, hb, hwalk, hnot⟩
          · exact absurd h hc
          · refine ⟨j0, mid ++ [j], by rw [hb]; simp, ?_, ?_⟩
            · have := isEdgeWalk_append hwalk (isEdgeWalk_head hw)
              simpa using this
            · have hmid := isEdgeWalk_tail_otherEnd hwalk
              rw [walkVerts_append hmid]
              simp only [walkVerts, List.tail_cons, List.mem_append, List.mem_singleton, not_or]
              exact ⟨hnot, fun h => hc' h.symm⟩

/-- **Shortcutting a walk.** The shortcut walk is a walk with the same ends, a sublist of `w`,
visits only vertices of `w`, and repeats no edge. -/
theorem erase_spec : ∀ (n : ℕ) (u v : ℕ) (w : List ℕ), w.length ≤ n → IsEdgeWalk E u v w →
    IsEdgeWalk E u v (erase E u w) ∧ (erase E u w).Sublist w ∧
      (∀ y ∈ walkVerts E u (erase E u w), y ∈ walkVerts E u w) ∧ (erase E u w).Nodup := by
  intro n
  induction n with
  | zero =>
    intro u v w hn hw
    have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hw0
    cases hw
    rw [erase]
    split
    · exact ⟨IsEdgeWalk.nil _, List.nil_sublist _, fun y hy => hy, List.nodup_nil⟩
    · rename_i h
      simp [lastFrom] at h
  | succ n ih =>
    intro u v w hn hw
    have hspec := lastFrom_spec (E := E) (v := v) (mem_walkVerts_self (E := E) u w) u w w hw
      (fun y hy => hy) (fun y hy => hy) (Or.inl rfl)
    have hsuf := lastFrom_suffix E u w
    obtain ⟨hS, hcase⟩ := hspec
    rcases hcase with ⟨h0, hvu⟩ | ⟨j, rest, hjr, hwalk, hnot⟩
    · rw [erase]
      split
      · subst hvu
        refine ⟨IsEdgeWalk.nil _, List.nil_sublist _, ?_, List.nodup_nil⟩
        intro y hy
        simp only [walkVerts, List.mem_singleton] at hy
        rw [hy]
        exact mem_walkVerts_self _ w
      · rename_i j' rest' h'
        rw [h0] at h'
        cases h'
    · have hlen : rest.length ≤ n := by
        have := hsuf.length_le
        rw [hjr] at this
        simp only [List.length_cons] at this
        omega
      set x := otherEnd E j u
      have hrest : IsEdgeWalk E x v rest := isEdgeWalk_tail_otherEnd hwalk
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih x v rest hlen hrest
      have hval : erase E u w = j :: erase E x rest := by
        rw [erase]
        split
        · rename_i h'
          rw [hjr] at h'
          cases h'
        · rename_i j' rest' h'
          rw [hjr] at h'
          cases h'
          rfl
      rw [hval]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact isEdgeWalk_append (isEdgeWalk_head hwalk) ih1
      · have hsuf' : (j :: rest) <:+ w := hjr ▸ hsuf
        exact (ih2.cons_cons j).trans hsuf'.sublist
      · intro y hy
        simp only [walkVerts, List.mem_cons] at hy
        apply hS
        rw [hjr]
        simp only [walkVerts, List.mem_cons]
        rcases hy with rfl | hy
        · exact Or.inl rfl
        · exact Or.inr (ih3 y hy)
      · refine List.nodup_cons.mpr ⟨fun hj => ?_, ih4⟩
        have hends := ends_mem_walkVerts ih1 hj
        have hu : (edgeAt E j).1 = u ∨ (edgeAt E j).2 = u := by
          cases hwalk with
          | cons _ hend _ =>
            rcases hend with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact Or.inl h1
            · exact Or.inr h2
        rcases hu with hu | hu
        · rw [hu] at hends
          exact hnot (ih3 u hends.1)
        · rw [hu] at hends
          exact hnot (ih3 u hends.2)

end MinCostFlow.HierPaths
