module

public import MinCostFlow.LowStretch.PetalFacts

/-!
# Parts of a walk

A walk that starts at `a` and uses the pairs `ps` has the vertex list `vtx a ps`. Its first `j`
pairs form a walk from `a` to vertex number `j`, and the other pairs form a walk from vertex
number `j` to the end. A walk whose vertices all lie in `S` is a walk in `S`. Along a highway,
the length of the part between vertices `j ≤ k` is the drop of the distance to the center.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PG

variable {G : PG} {V P : Set ℕ}

theorem vtx_drop (a : ℕ) (ps : List ℕ) (j : ℕ) (hj : j ≤ ps.length) :
    G.vtx ((G.vtx a ps).getD j 0) (ps.drop j) = (G.vtx a ps).drop j := by
  induction ps generalizing a j with
  | nil => simp at hj; subst hj; rfl
  | cons p ps ih =>
    cases j with
    | zero => rfl
    | succ j => simpa [vtx] using ih (G.other p a) j (by simpa using hj)

theorem vtx_take (a : ℕ) (ps : List ℕ) (j : ℕ) :
    G.vtx a (ps.take j) = (G.vtx a ps).take (j + 1) := by
  induction ps generalizing a j with
  | nil => simp [vtx]
  | cons p ps ih =>
    cases j with
    | zero => simp [vtx]
    | succ j => simp [vtx, ih]

namespace IsWalk

/-- A walk whose vertices all lie in `S` is a walk in `S`. -/
theorem restrict {S : Set ℕ} {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps)
    (hS : ∀ x ∈ G.vtx a ps, x ∈ S) : G.IsWalk S P a b ps := by
  induction h with
  | nil _ => exact .nil (hS _ (by simp [vtx]))
  | cons _ hp hj _ ih =>
    refine .cons (hS _ (by simp [vtx])) hp hj (ih fun x hx => hS x ?_)
    rw [vtx, hj.other_eq]; exact List.mem_cons_of_mem _ hx

theorem drop {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) (j : ℕ) (hj : j ≤ ps.length) :
    G.IsWalk V P ((G.vtx a ps).getD j 0) b (ps.drop j) := by
  induction h generalizing j with
  | nil ha => simp at hj; subst hj; exact .nil ha
  | @cons x y z p ps hx hp hj' rest ih =>
    cases j with
    | zero => exact .cons hx hp hj' rest
    | succ j =>
      simpa [vtx, hj'.other_eq] using ih j (by simpa using hj)

theorem take {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) (j : ℕ) (hj : j ≤ ps.length) :
    G.IsWalk V P a ((G.vtx a ps).getD j 0) (ps.take j) := by
  induction h generalizing j with
  | nil ha => simp at hj; subst hj; exact .nil ha
  | @cons x y z p ps hx hp hj' rest ih =>
    cases j with
    | zero => exact .nil hx
    | succ j =>
      simpa [vtx, hj'.other_eq] using IsWalk.cons hx hp hj' (ih j (by simpa using hj))

end IsWalk

theorem getD_vtx_mem_take {a : ℕ} {ps : List ℕ} {j k : ℕ} (hk : k ≤ j) (hj : j ≤ ps.length) :
    (G.vtx a ps).getD k 0 ∈ G.vtx a (ps.take j) := by
  rw [vtx_take, List.getD_eq_getElem _ _ (by rw [IsWalk.length_vtx]; omega)]
  have : k < ((G.vtx a ps).take (j + 1)).length := by
    rw [List.length_take, IsWalk.length_vtx]; omega
  have h := List.getElem_mem this
  rwa [List.getElem_take] at h

/-- Every vertex of a walk has a number. -/
theorem mem_vtx {a x : ℕ} {ps : List ℕ} (hx : x ∈ G.vtx a ps) :
    ∃ k ≤ ps.length, (G.vtx a ps).getD k 0 = x := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  rw [IsWalk.length_vtx] at hk
  exact ⟨k, by omega, by rw [List.getD_eq_getElem]⟩

/-- Every vertex of the first `j` pairs of a walk is one of its vertices number `0, …, j`. -/
theorem mem_vtx_take {a x : ℕ} {ps : List ℕ} {j : ℕ} (hx : x ∈ G.vtx a (ps.take j)) :
    ∃ k ≤ j, k ≤ ps.length ∧ (G.vtx a ps).getD k 0 = x := by
  rw [vtx_take] at hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  rw [List.length_take, IsWalk.length_vtx] at hk
  refine ⟨k, by omega, by omega, ?_⟩
  rw [List.getElem_take, List.getD_eq_getElem]

/-- Every vertex after the first `j` pairs of a walk is one of its vertices number `≥ j`. -/
theorem mem_vtx_drop {a x : ℕ} {ps : List ℕ} {j : ℕ} (hj : j ≤ ps.length)
    (hx : x ∈ G.vtx ((G.vtx a ps).getD j 0) (ps.drop j)) :
    ∃ k, j ≤ k ∧ k ≤ ps.length ∧ (G.vtx a ps).getD k 0 = x := by
  rw [vtx_drop a ps j hj] at hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  rw [List.length_drop, IsWalk.length_vtx] at hk
  refine ⟨j + k, by omega, by omega, ?_⟩
  rw [List.getElem_drop, List.getD_eq_getElem]

theorem getD_vtx_drop {a : ℕ} {ps : List ℕ} {j : ℕ} (hj : j ≤ ps.length) (k : ℕ) :
    (G.vtx ((G.vtx a ps).getD j 0) (ps.drop j)).getD k 0 = (G.vtx a ps).getD (j + k) 0 := by
  rw [vtx_drop a ps j hj]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_vtx_take {a : ℕ} {ps : List ℕ} {j k : ℕ} (hk : k ≤ j) :
    (G.vtx a (ps.take j)).getD k 0 = (G.vtx a ps).getD k 0 := by
  rw [vtx_take]
  simp [List.getD_eq_getElem?_getD, show k < j + 1 by omega]

/-- A pair of a walk has both ends among the vertices of the walk. -/
theorem ends_of_mem {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) {p : ℕ} (hp : p ∈ ps) :
    ∃ k < ps.length, ps.getD k 0 = p ∧
      G.Joins p ((G.vtx a ps).getD k 0) ((G.vtx a ps).getD (k + 1) 0) := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  refine ⟨k, hk, by rw [List.getD_eq_getElem], ?_⟩
  have := h.joins_getD hk
  rw [List.getD_eq_getElem _ _ hk] at this
  exact this

end PG

namespace Cl

variable {G : PG} {c : Cl} {t : ℕ} {hw : List ℕ}

/-- Along a highway, the part between vertices `j ≤ k` has length `d(x0, h_j) - d(x0, h_k)`. -/
theorem IsHighway.seg_len (hh : c.IsHighway G t hw) {j k : ℕ} (hjk : j ≤ k)
    (hk : k ≤ hw.length) :
    PG.wlen (c.len G) ((hw.drop j).take (k - j)) + c.d G c.x0 (hv G t hw k) =
      c.d G c.x0 (hv G t hw j) := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hjk ih =>
    have h1 := ih (by omega)
    have h2 := hh.2 k (by omega)
    have e : (hw.drop j).take (k + 1 - j) = (hw.drop j).take (k - j) ++ [hw.getD k 0] := by
      rw [show k + 1 - j = (k - j) + 1 by omega, List.take_add_one]
      congr 1
      rw [List.getElem?_drop, show j + (k - j) = k by omega]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < hw.length by omega)]
    rw [e, PG.wlen_append]
    simp only [PG.wlen_cons, PG.wlen_nil, Nat.add_zero]
    omega

/-- The part of a highway between vertices `j ≤ k` is a walk between them. -/
theorem IsHighway.seg_walk (hh : c.IsHighway G t hw) {j k : ℕ} (hjk : j ≤ k)
    (hk : k ≤ hw.length) :
    G.IsWalk ↑c.X Set.univ (hv G t hw j) (hv G t hw k) ((hw.drop j).take (k - j)) := by
  have h1 := hh.1.drop j (by omega)
  have h2 := h1.take (k - j) (by rw [List.length_drop]; omega)
  rw [PG.getD_vtx_drop (by omega), show j + (k - j) = k by omega] at h2
  exact h2

/-- The vertices of the part of a highway between vertices `j ≤ k` are its vertices number
`j, …, k`. -/
theorem seg_vtx {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ hw.length) {x : ℕ}
    (hx : x ∈ G.vtx (hv G t hw j) ((hw.drop j).take (k - j))) :
    ∃ m, j ≤ m ∧ m ≤ k ∧ hv G t hw m = x := by
  obtain ⟨m, hm, -, rfl⟩ := PG.mem_vtx_take hx
  refine ⟨j + m, by omega, by omega, ?_⟩
  unfold hv
  rw [PG.getD_vtx_drop (by omega)]

end Cl

end MinCostFlow.LowStretch
