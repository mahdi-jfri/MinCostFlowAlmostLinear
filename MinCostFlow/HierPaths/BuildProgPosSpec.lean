module

public import MinCostFlow.HierPaths.BuildProgPos
public import MinCostFlow.HierPaths.BuildProgErase

/-!
# Pass 1 in memory is `posFill`

`posFillProc` writes, for `j = 0, …, n − 1` in turn, the number `n − 1 − j` into the cell
`P + vs_j`, where `vs_0, …, vs_{n−1}` are the words at `vs` (`fillMem`). When these words are the
vertices `walkVerts E u w` of a walk `w` (so `n = |w| + 1`), the array it leaves at `P` is the
array `posFill E u w` of `BuildProgErase.lean` (`fillMem_eq_posFill`): both write, at each visit
of a vertex, the number of edges after the visit.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Write `|rest|` at each vertex `v` of the list `v :: rest`, from front to back. -/
@[expose] def listFill : List ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | [], Q => Q
  | v :: rest, Q => listFill rest (Function.update Q v rest.length)

/-- The first `i` writes of `listFill`, by index. -/
@[expose] def idxFill (L : List ℕ) (Q : ℕ → ℕ) : ℕ → (ℕ → ℕ)
  | 0 => Q
  | i + 1 => Function.update (idxFill L Q i) (L.getD i 0) (L.length - 1 - i)

theorem posFill_eq_listFill (E : List (ℕ × ℕ)) :
    ∀ (u : ℕ) (w : List ℕ) (Q : ℕ → ℕ), posFill E u w Q = listFill (walkVerts E u w) Q
  | u, [], Q => rfl
  | u, j :: rest, Q => by
    simp only [posFill, walkVerts, listFill]
    have hl : (walkVerts E (otherEnd E j u) rest).length = rest.length + 1 := by
      clear Q
      induction rest generalizing u j with
      | nil => rfl
      | cons i t ih => simp only [walkVerts, List.length_cons, ih]
    rw [hl]
    exact posFill_eq_listFill E _ rest _

theorem idxFill_cons (v : ℕ) (rest : List ℕ) (Q : ℕ → ℕ) :
    ∀ k ≤ rest.length,
      idxFill (v :: rest) Q (k + 1) = idxFill rest (Function.update Q v rest.length) k
  | 0, _ => by simp [idxFill]
  | k + 1, hk => by
    rw [idxFill, idxFill_cons v rest Q k (by omega), idxFill]
    simp only [List.getD_cons_succ, List.length_cons]
    congr 1
    omega

theorem listFill_eq_idxFill : ∀ (L : List ℕ) (Q : ℕ → ℕ), listFill L Q = idxFill L Q L.length
  | [], Q => rfl
  | v :: rest, Q => by
    rw [listFill, List.length_cons, idxFill_cons v rest Q rest.length le_rfl]
    exact listFill_eq_idxFill rest _

/-- The memory of pass 1 seen through `P + ·` is `idxFill` of the stored list. -/
theorem fillMem_eq_idxFill {mem₀ : ℕ → ℕ} {vs P : ℕ} {L : List ℕ}
    (hL : ∀ j < L.length, mem₀ (vs + j) = L.getD j 0) :
    ∀ i ≤ L.length, (fun v => fillMem mem₀ vs L.length P i (P + v)) =
      idxFill L (fun v => mem₀ (P + v)) i
  | 0, _ => rfl
  | i + 1, hi => by
    funext v
    rw [fillMem, idxFill, ← fillMem_eq_idxFill hL i (by omega), hL i (by omega)]
    by_cases hv : v = L.getD i 0
    · subst hv; simp
    · rw [Function.update_of_ne (by omega), Function.update_of_ne hv]

/-- **Pass 1 in memory is `posFill`.** If the words at `vs` are the vertices of the walk `w`
from `u`, then after `posFillProc` the cell `P + v` holds `posFill E u w P₀ v`, where `P₀` is the
array at `P` before the call. -/
theorem fillMem_eq_posFill (E : List (ℕ × ℕ)) (u : ℕ) (w : List ℕ) {mem₀ : ℕ → ℕ} {vs P : ℕ}
    (hL : ∀ j < (walkVerts E u w).length, mem₀ (vs + j) = (walkVerts E u w).getD j 0) (v : ℕ) :
    fillMem mem₀ vs (walkVerts E u w).length P (walkVerts E u w).length (P + v) =
      posFill E u w (fun y => mem₀ (P + y)) v := by
  rw [posFill_eq_listFill, listFill_eq_idxFill, ← fillMem_eq_idxFill hL _ le_rfl]

end MinCostFlow.HierPaths

/-! ### Pass 2 by index

Pass 2 in memory keeps the index `i` of the current vertex `vs_i` in the walk. From `vs_i`, the
next kept edge is edge `|w| − P(vs_i)` and the walk goes on from vertex `|w| − P(vs_i) + 1`;
it stops when `P(vs_i) = 0`. `jumpRun_index` says this is `jumpRun`. -/

namespace MinCostFlow.HierPaths

variable {E : List (ℕ × ℕ)}

theorem length_walkVerts (u : ℕ) (w : List ℕ) : (walkVerts E u w).length = w.length + 1 := by
  induction w generalizing u with
  | nil => rfl
  | cons i t ih => simp only [walkVerts, List.length_cons, ih]

/-- The vertex after edge `k` is the other end of edge `k` from the vertex before it. -/
theorem walkVerts_succ (u : ℕ) (w : List ℕ) :
    ∀ k < w.length, (walkVerts E u w).getD (k + 1) 0 =
      otherEnd E (w.getD k 0) ((walkVerts E u w).getD k 0) := by
  induction w generalizing u with
  | nil => intro k hk; simp at hk
  | cons j t ih =>
    intro k hk
    cases k with
    | zero =>
      simp only [walkVerts, List.getD_cons_succ, List.getD_cons_zero]
      rw [walkVerts_eq_cons]; rfl
    | succ k =>
      simp only [walkVerts, List.getD_cons_succ]
      exact ih _ k (by simp at hk; omega)

/-- **Pass 1 by index**: the value at the vertex at index `t` is at most `|w| − t`, and the
vertex at index `|w| − P v` is `v`, for `v` the vertex at index `t`. -/
theorem posFill_index : ∀ (u : ℕ) (w : List ℕ) (Q : ℕ → ℕ) (t : ℕ), t ≤ w.length →
    posFill E u w Q ((walkVerts E u w).getD t 0) ≤ w.length - t ∧
      (walkVerts E u w).getD (w.length - posFill E u w Q ((walkVerts E u w).getD t 0)) 0 =
        (walkVerts E u w).getD t 0
  | u, [], Q, t, ht => by
    have : t = 0 := by simpa using ht
    subst this
    simp [posFill, walkVerts]
  | u, j :: rest, Q, t, ht => by
    set u' := otherEnd E j u
    set Q' := Function.update Q u (rest.length + 1)
    have hlen := length_walkVerts (E := E) u' rest
    have hP : posFill E u (j :: rest) Q = posFill E u' rest Q' := rfl
    have hvs : walkVerts E u (j :: rest) = u :: walkVerts E u' rest := rfl
    rw [hP, hvs]
    simp only [List.length_cons]
    cases t with
    | succ s =>
      simp only [List.getD_cons_succ]
      obtain ⟨h1, h2⟩ := posFill_index u' rest Q' s (by simp at ht; omega)
      refine ⟨by omega, ?_⟩
      have e : rest.length + 1 - posFill E u' rest Q' ((walkVerts E u' rest).getD s 0) =
          (rest.length - posFill E u' rest Q' ((walkVerts E u' rest).getD s 0)) + 1 := by omega
      rw [e, List.getD_cons_succ, h2]
    | zero =>
      simp only [List.getD_cons_zero]
      by_cases hu : u ∈ walkVerts E u' rest
      · obtain ⟨s, hs, hsu⟩ := List.getElem_of_mem hu
        have hsd : (walkVerts E u' rest).getD s 0 = u := by
          rw [List.getD_eq_getElem _ _ hs, hsu]
        obtain ⟨h1, h2⟩ := posFill_index u' rest Q' s (by omega)
        rw [hsd] at h1 h2
        refine ⟨by omega, ?_⟩
        have e : rest.length + 1 - posFill E u' rest Q' u =
            (rest.length - posFill E u' rest Q' u) + 1 := by omega
        rw [e, List.getD_cons_succ, h2]
      · have h1 := (off_walk (E := E) u' rest Q' [] hu).1
        have hQ : Q' u = rest.length + 1 := by simp [Q']
        rw [h1, hQ]
        simp

/-- **Pass 2 by index.** With `P = posFill E u w Q` and the current vertex at index `i`, the
next step of `jumpRun` keeps edge `k = |w| − P cur` and goes on from the vertex at index
`k + 1`, or stops when `P cur = 0`. -/
theorem jumpRun_index (u : ℕ) (w : List ℕ) (Q : ℕ → ℕ) {i : ℕ} (hi : i ≤ w.length) :
    jumpRun E (posFill E u w Q) ((walkVerts E u w).getD i 0) (w.drop i) =
      if posFill E u w Q ((walkVerts E u w).getD i 0) = 0 then [] else
        w.getD (w.length - posFill E u w Q ((walkVerts E u w).getD i 0)) 0 ::
          jumpRun E (posFill E u w Q)
            ((walkVerts E u w).getD (w.length - posFill E u w Q ((walkVerts E u w).getD i 0) + 1) 0)
            (w.drop (w.length - posFill E u w Q ((walkVerts E u w).getD i 0) + 1)) := by
  set P := posFill E u w Q
  set cur := (walkVerts E u w).getD i 0
  obtain ⟨hle0, hcur0⟩ := posFill_index (E := E) u w Q i hi
  have hle : P cur ≤ w.length - i := hle0
  have hcur : (walkVerts E u w).getD (w.length - P cur) 0 = cur := hcur0
  have hd : (w.drop i).drop ((w.drop i).length - P cur) = w.drop (w.length - P cur) := by
    rw [List.drop_drop, List.length_drop]
    congr 1
    omega
  rw [jumpRun]
  split
  · rename_i h
    rw [hd] at h
    have : P cur = 0 := by
      by_contra h0
      have hk : w.length - P cur < w.length := by omega
      rw [List.drop_eq_getElem_cons hk] at h
      simp at h
      all_goals omega
    simp [this]
  · rename_i j r h
    rw [hd] at h
    have h0 : P cur ≠ 0 := by
      intro h0
      rw [h0, Nat.sub_zero, List.drop_length] at h
      simp at h
    have hk : w.length - P cur < w.length := by omega
    rw [List.drop_eq_getElem_cons hk] at h
    obtain ⟨hj, hr⟩ := List.cons.inj h
    simp only [h0, ↓reduceIte]
    have hjd : w.getD (w.length - P cur) 0 = j := by rw [List.getD_eq_getElem _ _ hk, hj]
    rw [hjd, ← hr]
    congr 2
    rw [walkVerts_succ u w _ hk, hjd, hcur]

end MinCostFlow.HierPaths
