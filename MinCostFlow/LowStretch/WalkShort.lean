module

public import MinCostFlow.LowStretch.Walks
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.GetD

/-!
# Short walks

Every walk in a finite vertex set can be shortened to a walk with the same ends whose pairs form a
sublist of the original pairs and whose vertices are all different. Such a walk has fewer pairs
than the vertex set has elements. We use this to bound how much a distance changes when the
lengths of some pairs grow by a small amount.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PG

variable {G : PG}

/-- The other end of pair `p`, seen from `x`. -/
def other (G : PG) (p x : ℕ) : ℕ := if G.pu p = x then G.pv p else G.pu p

/-- The vertices of the walk that starts at `a` and uses the pairs `ps`. -/
def vtx (G : PG) : ℕ → List ℕ → List ℕ
  | a, [] => [a]
  | a, p :: ps => a :: G.vtx (G.other p a) ps

theorem Joins.other_eq {p a b : ℕ} (h : G.Joins p a b) : G.other p a = b := by
  rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [other, h1, h2]
  · by_cases hab : G.pu p = a
    · simp only [other, hab, ite_true]; rw [h2, ← hab, h1]
    · simp only [other, hab, ite_false]; exact h1

namespace IsWalk

variable {V P : Set ℕ}

/-- If `a` is a vertex of a walk from `b` to `c`, a tail of the walk goes from `a` to `c`. -/
theorem tail_of_mem {a b c : ℕ} {qs : List ℕ} (h : G.IsWalk V P b c qs) (ha : a ∈ G.vtx b qs) :
    ∃ qs', qs'.IsSuffix qs ∧ G.IsWalk V P a c qs' ∧ (G.vtx a qs').IsSuffix (G.vtx b qs) := by
  induction h with
  | nil hb =>
    simp only [vtx, List.mem_singleton] at ha
    subst ha
    exact ⟨[], List.suffix_refl _, .nil hb, List.suffix_refl _⟩
  | @cons x y z p ps hx hp hj rest ih =>
    rw [vtx, hj.other_eq] at ha ⊢
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨p :: ps, List.suffix_refl _, .cons hx hp hj rest, by rw [vtx, hj.other_eq]⟩
    · obtain ⟨qs', hs, hw, hv⟩ := ih ha
      exact ⟨qs', hs.trans (List.suffix_cons _ _), hw, hv.trans (List.suffix_cons _ _)⟩

/-- Every walk has a walk with the same ends, pairs forming a sublist, and distinct vertices. -/
theorem exists_nodup {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) :
    ∃ qs, qs.Sublist ps ∧ G.IsWalk V P a b qs ∧ (G.vtx a qs).Nodup := by
  induction h with
  | nil ha => exact ⟨[], List.Sublist.slnil, .nil ha, by simp [vtx]⟩
  | @cons x y z p ps hx hp hj rest ih =>
    obtain ⟨qs, hsub, hw, hnd⟩ := ih
    by_cases hmem : x ∈ G.vtx y qs
    · obtain ⟨qs', hs, hw', hv⟩ := hw.tail_of_mem hmem
      exact ⟨qs', (hs.sublist.trans hsub).cons p, hw', hv.sublist.nodup hnd⟩
    · refine ⟨p :: qs, hsub.cons_cons p, .cons hx hp hj hw, ?_⟩
      rw [vtx, hj.other_eq]
      exact List.nodup_cons.mpr ⟨hmem, hnd⟩

theorem vtx_subset {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) :
    ∀ x ∈ G.vtx a ps, x ∈ V := by
  induction h with
  | nil ha => intro x hx; simp only [vtx, List.mem_singleton] at hx; exact hx ▸ ha
  | cons hx _ hj _ ih =>
    intro x hmem
    rw [vtx, hj.other_eq] at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hx
    · exact ih x hmem

theorem length_vtx (a : ℕ) (ps : List ℕ) : (G.vtx a ps).length = ps.length + 1 := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih => simp [vtx, ih]

/-- A walk in a finite set `S` can be shortened to one with fewer pairs than `S` has elements. -/
theorem exists_short {S : Finset ℕ} {a b : ℕ} {ps : List ℕ} (h : G.IsWalk ↑S P a b ps) :
    ∃ qs, qs.Sublist ps ∧ G.IsWalk ↑S P a b qs ∧ qs.length + 1 ≤ S.card := by
  obtain ⟨qs, hsub, hw, hnd⟩ := h.exists_nodup
  refine ⟨qs, hsub, hw, ?_⟩
  rw [← length_vtx a qs, ← List.toFinset_card_of_nodup hnd]
  exact Finset.card_le_card fun x hx => by
    simpa using hw.vtx_subset x (List.mem_toFinset.mp hx)


/-- Step number `i` of a walk joins its vertices number `i` and `i + 1`. -/
theorem joins_getD {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) {i : ℕ}
    (hi : i < ps.length) :
    G.Joins (ps.getD i 0) ((G.vtx a ps).getD i 0) ((G.vtx a ps).getD (i + 1) 0) := by
  induction h generalizing i with
  | nil _ => simp at hi
  | @cons x y z p ps hx hp hj rest ih =>
    rw [vtx, hj.other_eq]
    cases i with
    | zero => cases rest <;> simpa [vtx] using hj
    | succ i => simpa using ih (by simpa using hi)

/-- Vertex number `i` of a walk lies in its vertex set. -/
theorem getD_mem {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) {i : ℕ}
    (hi : i ≤ ps.length) : (G.vtx a ps).getD i 0 ∈ V := by
  refine h.vtx_subset _ ?_
  rw [List.getD_eq_getElem _ _ (by rw [length_vtx]; omega)]
  exact List.getElem_mem _

/-- The last vertex of a walk is its end. -/
theorem getD_length {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) :
    (G.vtx a ps).getD ps.length 0 = b := by
  induction h with
  | nil _ => rfl
  | cons _ _ hj _ ih => simpa [vtx, hj.other_eq] using ih

end IsWalk

end PG

end MinCostFlow.LowStretch
