module

public import MinCostFlow.HierPaths.LoopErase

/-!
# Loop erasure on arrays

A program cannot keep the stack of `eraseStep` (`HierPaths/LoopErase.lean`) as a list with its
top first. It keeps the stack from the bottom in an array, with a position array that gives for
each vertex its place on the stack plus one, or `0` when the vertex is not on the stack. Then a
step to a vertex `y` on the stack keeps the first `pos y` entries.

This file gives that array form, `arrStep`, and proves that it is the reverse of `eraseStep`
(`reverse_eraseFrom`), so the erased walk is `ofSteps s (arrFrom s [] (Walk.steps P))`
(`loopErase_eq_arrFrom`). It also gives the position function of a stack, `stackPos`, and how a
step changes it, which the program uses to keep the position array up to date.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- One step of loop erasure on the stack `r`, kept from the bottom. -/
def arrStep (s : ℕ) (r : List (ℕ × ℕ)) (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  if p.2 = s then []
  else if p.2 ∈ r.map Prod.snd then r.take ((r.map Prod.snd).idxOf p.2 + 1)
  else r ++ [p]

/-- Loop erasure of the steps `l` on arrays, from the stack `r`. -/
def arrFrom (s : ℕ) (r l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  l.foldl (arrStep s) r

/-- The position array of the stack `r`: the place of `y` on the stack plus one, or `0`. -/
def stackPos (r : List (ℕ × ℕ)) (y : ℕ) : ℕ :=
  if y ∈ r.map Prod.snd then (r.map Prod.snd).idxOf y + 1 else 0

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

public section

/-- The distinctness invariant of the stack, kept by each step. -/
theorem nodup_eraseStep {s : ℕ} {st : List (ℕ × ℕ)} (h : (s :: st.map Prod.snd).Nodup)
    (p : ℕ × ℕ) : (s :: (eraseStep s st p).map Prod.snd).Nodup := by
  unfold eraseStep
  split_ifs with h1 h2
  · simp
  · exact h.sublist (List.Sublist.cons_cons _ ((List.dropWhile_suffix _).sublist.map _))
  · refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨Ne.symm h1, (List.nodup_cons.mp h).1⟩
    · simp only [List.map_cons]
      exact List.nodup_cons.mpr ⟨h2, (List.nodup_cons.mp h).2⟩

private theorem dropWhile_reverse {st : List (ℕ × ℕ)} {y : ℕ} (hnd : (st.map Prod.snd).Nodup)
    (hy : y ∈ st.map Prod.snd) :
    (st.dropWhile (fun q => q.2 ≠ y)).reverse =
      st.reverse.take ((st.reverse.map Prod.snd).idxOf y + 1) := by
  induction st with
  | nil => simp at hy
  | cons q st ih =>
    rw [List.map_cons] at hnd hy
    have hnd2 := List.nodup_cons.mp hnd
    rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
    by_cases hq : q.2 = y
    · -- The top is `y`, so nothing is dropped, and `y` is last in the reverse.
      have hyst : y ∉ st.reverse.map Prod.snd := by
        rw [List.map_reverse, List.mem_reverse, ← hq]; exact hnd2.1
      rw [List.dropWhile_cons_of_neg (by simpa using hq), List.idxOf_append_of_notMem hyst]
      rw [List.take_of_length_le (by simp)]
      simp
    · have hy' : y ∈ st.map Prod.snd := by
        rcases List.mem_cons.mp hy with h | h
        · exact absurd h.symm hq
        · exact h
      rw [List.dropWhile_cons_of_pos (by simpa using hq), ih hnd2.2 hy']
      have hmem : y ∈ st.reverse.map Prod.snd := by
        rw [List.map_reverse, List.mem_reverse]; exact hy'
      rw [List.idxOf_append_of_mem hmem]
      have hlt := List.idxOf_lt_length_iff.mpr hmem
      rw [List.length_map] at hlt
      rw [List.take_append_of_le_length (by omega)]

/-- The array step is the reverse of the stack step. -/
theorem reverse_eraseStep {s : ℕ} {st : List (ℕ × ℕ)} (h : (s :: st.map Prod.snd).Nodup)
    (p : ℕ × ℕ) : (eraseStep s st p).reverse = arrStep s st.reverse p := by
  unfold eraseStep arrStep
  have hmem : p.2 ∈ st.reverse.map Prod.snd ↔ p.2 ∈ st.map Prod.snd := by simp
  by_cases h1 : p.2 = s
  · simp [h1]
  · by_cases h2 : p.2 ∈ st.map Prod.snd
    · simp only [h1, h2, hmem, ↓reduceIte]
      exact dropWhile_reverse (List.nodup_cons.mp h).2 h2
    · simp [h1, h2]

/-- Loop erasure on arrays is the reverse of loop erasure on the stack. -/
theorem reverse_eraseFrom (s : ℕ) :
    ∀ (st l : List (ℕ × ℕ)), (s :: st.map Prod.snd).Nodup →
      (eraseFrom s st l).reverse = arrFrom s st.reverse l
  | st, [], _ => rfl
  | st, p :: l, h => by
    have := reverse_eraseFrom s (eraseStep s st p) l (nodup_eraseStep h p)
    simp only [eraseFrom, List.foldl_cons] at this ⊢
    rw [this, reverse_eraseStep h p]
    rfl

/-- The erased walk from the array form. -/
theorem loopErase_eq_arrFrom (P : Walk) {s : ℕ} {t : List ℕ} (hv : P.verts = s :: t) :
    loopErase P = ofSteps s (arrFrom s [] (Walk.steps P)) := by
  simp only [loopErase, hv]
  rw [reverse_eraseFrom s [] _ (by simp)]
  rfl

/-- Reading the position of a vertex on the stack. -/
theorem stackPos_of_mem {r : List (ℕ × ℕ)} {y : ℕ} (hy : y ∈ r.map Prod.snd) :
    stackPos r y = (r.map Prod.snd).idxOf y + 1 := by
  simp [stackPos, hy]

theorem stackPos_of_not_mem {r : List (ℕ × ℕ)} {y : ℕ} (hy : y ∉ r.map Prod.snd) :
    stackPos r y = 0 := by
  simp [stackPos, hy]

/-- A vertex is on the stack exactly when its position is not `0`. -/
theorem stackPos_eq_zero_iff {r : List (ℕ × ℕ)} {y : ℕ} :
    stackPos r y = 0 ↔ y ∉ r.map Prod.snd := by
  by_cases hy : y ∈ r.map Prod.snd
  · simp [stackPos, hy]
  · simp [stackPos, hy]

/-- The position of a vertex on the stack is at most the length of the stack. -/
theorem stackPos_le (r : List (ℕ × ℕ)) (y : ℕ) : stackPos r y ≤ r.length := by
  by_cases hy : y ∈ r.map Prod.snd
  · rw [stackPos_of_mem hy]
    have := List.idxOf_lt_length_iff.mpr hy
    rw [List.length_map] at this
    omega
  · rw [stackPos_of_not_mem hy]; exact Nat.zero_le _

/-- Pushing a new vertex gives it the last place. -/
theorem stackPos_push {r : List (ℕ × ℕ)} {p : ℕ × ℕ} (hp : p.2 ∉ r.map Prod.snd) (y : ℕ) :
    stackPos (r ++ [p]) y = if y = p.2 then r.length + 1 else stackPos r y := by
  by_cases hy : y = p.2
  · subst hy
    have : (r.map Prod.snd ++ [p.2]).idxOf p.2 = r.length := by
      rw [List.idxOf_append_of_notMem hp]; simp
    simp [stackPos, this]
  · by_cases hyr : y ∈ r.map Prod.snd
    · have : (r.map Prod.snd ++ [p.2]).idxOf y = (r.map Prod.snd).idxOf y :=
        List.idxOf_append_of_mem hyr
      simp [stackPos, hy, hyr, this]
    · simp [stackPos, hy, hyr]

/-- The position on a stack with one more entry at the bottom. -/
theorem stackPos_cons (q : ℕ × ℕ) (r : List (ℕ × ℕ)) (y : ℕ) :
    stackPos (q :: r) y =
      if y = q.2 then 1 else if stackPos r y = 0 then 0 else stackPos r y + 1 := by
  by_cases hy : y = q.2
  · subst hy; simp [stackPos]
  · by_cases hm : y ∈ r.map Prod.snd
    · have hm' : y ∈ (q :: r).map Prod.snd := by
        rw [List.map_cons]; exact List.mem_cons_of_mem _ hm
      rw [stackPos_of_mem hm', stackPos_of_mem hm, List.map_cons,
        List.idxOf_cons_ne _ (Ne.symm hy)]
      simp only [hy, ↓reduceIte, Nat.add_one_ne_zero, Nat.succ_eq_add_one]
    · have hm' : y ∉ (q :: r).map Prod.snd := by
        simp only [List.map_cons, List.mem_cons, not_or]; exact ⟨hy, hm⟩
      rw [stackPos_of_not_mem hm', stackPos_of_not_mem hm]
      simp [hy]

/-- Cutting the stack to its first `k` entries: the
vertices of the first `k` entries keep their place, and the others leave. -/
theorem stackPos_take {r : List (ℕ × ℕ)} (k y : ℕ) :
    stackPos (r.take k) y = if stackPos r y ≤ k then stackPos r y else 0 := by
  induction r generalizing k with
  | nil => simp [stackPos]
  | cons q r ih =>
    cases k with
    | zero =>
      have h0 : stackPos ([] : List (ℕ × ℕ)) y = 0 := by simp [stackPos]
      rw [List.take_zero, h0, stackPos_cons]
      split_ifs <;> omega
    | succ k =>
      rw [List.take_succ_cons, stackPos_cons, stackPos_cons, ih k]
      split_ifs <;> omega

/-! ### Facts the program uses -/

/-- The distinctness invariant of the array stack, kept by each step. -/
theorem nodup_arrStep {s : ℕ} {r : List (ℕ × ℕ)} (h : (s :: r.map Prod.snd).Nodup)
    (p : ℕ × ℕ) : (s :: (arrStep s r p).map Prod.snd).Nodup := by
  unfold arrStep
  split_ifs with h1 h2
  · simp
  · exact h.sublist (List.Sublist.cons_cons _ ((List.take_sublist _ _).map _))
  · have hnd := List.nodup_cons.mp h
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton, not_or]
      exact ⟨hnd.1, Ne.symm h1⟩
    · rw [List.map_append, List.nodup_append]
      refine ⟨hnd.2, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      rw [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hab; subst hb; exact h2 ha

theorem nodup_arrFrom (s : ℕ) :
    ∀ (r l : List (ℕ × ℕ)), (s :: r.map Prod.snd).Nodup →
      (s :: (arrFrom s r l).map Prod.snd).Nodup
  | _, [], h => h
  | r, p :: l, h => nodup_arrFrom s (arrStep s r p) l (nodup_arrStep h p)

/-- Every entry of the array stack is an entry of the start stack or a step. -/
theorem mem_arrFrom (s : ℕ) :
    ∀ (r l : List (ℕ × ℕ)) (q : ℕ × ℕ), q ∈ arrFrom s r l → q ∈ r ∨ q ∈ l
  | r, [], q, h => Or.inl h
  | r, p :: l, q, h => by
    rcases mem_arrFrom s (arrStep s r p) l q h with h1 | h1
    · unfold arrStep at h1
      split_ifs at h1
      · simp at h1
      · exact Or.inl (List.mem_of_mem_take h1)
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact Or.inl h2
        · rw [List.mem_singleton] at h2; subst h2; exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem length_arrStep_le (s : ℕ) (r : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    (arrStep s r p).length ≤ r.length + 1 := by
  unfold arrStep
  split_ifs
  · simp
  · rw [List.length_take]; omega
  · simp

theorem length_arrFrom_le (s : ℕ) :
    ∀ (r l : List (ℕ × ℕ)), (arrFrom s r l).length ≤ r.length + l.length
  | r, [] => by simp [arrFrom]
  | r, p :: l => by
    have h1 := length_arrFrom_le s (arrStep s r p) l
    have h2 := length_arrStep_le s r p
    simp only [arrFrom, List.foldl_cons, List.length_cons] at h1 ⊢
    omega

/-- One more step of the input. -/
theorem arrFrom_take_succ (s : ℕ) (r l : List (ℕ × ℕ)) {i : ℕ} (hi : i < l.length) :
    arrFrom s r (l.take (i + 1)) = arrStep s (arrFrom s r (l.take i)) l[i] := by
  simp only [arrFrom]
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  rfl

/-- A step to the start or to a vertex on the stack cuts the stack. -/
theorem arrStep_of_pop {s : ℕ} {r : List (ℕ × ℕ)} {p : ℕ × ℕ}
    (hp : p.2 = s ∨ p.2 ∈ r.map Prod.snd) :
    arrStep s r p = r.take (if p.2 = s then 0 else stackPos r p.2) := by
  unfold arrStep
  by_cases h1 : p.2 = s
  · simp [h1]
  · have h2 : p.2 ∈ r.map Prod.snd := hp.resolve_left h1
    simp only [h1, h2, ↓reduceIte, stackPos_of_mem h2]

/-- Any other step is pushed. -/
theorem arrStep_of_push {s : ℕ} {r : List (ℕ × ℕ)} {p : ℕ × ℕ} (h1 : p.2 ≠ s)
    (h2 : p.2 ∉ r.map Prod.snd) : arrStep s r p = r ++ [p] := by
  simp [arrStep, h1, h2]

/-- The position of the vertex of entry `i` is `i + 1`. -/
theorem stackPos_getElem {r : List (ℕ × ℕ)} (hnd : (r.map Prod.snd).Nodup) {i : ℕ}
    (hi : i < r.length) : stackPos r r[i].2 = i + 1 := by
  have hm : r[i].2 ∈ r.map Prod.snd := List.mem_map_of_mem (List.getElem_mem hi)
  rw [stackPos_of_mem hm]
  have : (r.map Prod.snd)[i]'(by simpa using hi) = r[i].2 := by simp
  rw [← this, List.Nodup.idxOf_getElem hnd]

/-- Only the vertex of entry `i` has position `i + 1`. -/
theorem eq_of_stackPos_eq {r : List (ℕ × ℕ)} {i : ℕ} (hi : i < r.length) {v : ℕ}
    (hv : stackPos r v = i + 1) : v = r[i].2 := by
  have hm : v ∈ r.map Prod.snd := by
    by_contra h; rw [stackPos_of_not_mem h] at hv; omega
  rw [stackPos_of_mem hm] at hv
  have hidx : (r.map Prod.snd).idxOf v = i := by omega
  have := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hm)
  simp only [hidx, List.getElem_map] at this
  exact this.symm

end

end MinCostFlow.HierPaths
