module

public import MinCostFlow.HierPaths.BuildErase

/-!
# Shortcutting a walk in linear time

`erase u w` (`BuildErase.lean`) jumps, at each vertex `c` it reaches, to the last time the walk
`w` is at `c` (`lastFrom`). Found by a scan, each jump costs the length of the walk, so `erase`
as written takes time quadratic in the length. This file computes the same walk in linear time
with a position array `P`, indexed by vertices.

* Pass 1 (`posFill`): walk along `w` and, at each vertex `c`, write into `P c` the number of edges
  of `w` after this visit. Later visits overwrite earlier ones, so at the end `P c` says where
  the last visit to `c` is: the rest of the walk after it is the last `P c` edges.
* Pass 2 (`jumpRun`): from the current vertex `c` and the rest `rest` of the walk, jump to the
  last `P c` edges of `rest`, keep the first edge `j` of them, and go on from the other end of
  `j`. Each step keeps one edge and drops at least that edge, so there are at most `|w| + 1`
  steps (`jumpSteps_le`).
* Pass 3 (`posClear`): write `0` back into `P c` for each vertex `c` of the walk. If `P` was `0`
  on the walk before, it is the same array as before (`posClear_posFill`), so one array serves
  all calls.

`jumpRun_eq_erase` says that pass 2 gives `erase u w`. The reason: at a vertex `c` of the rest of
the walk, the last visit to `c` in the whole walk is also the last visit in the rest
(`posFill_append`), and the jump of pass 2 lands where `lastFrom` does (`lastFrom_eq_drop`).
The work of the three passes is at most `3 (|w| + 1)` (`eraseSteps_le`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The end of the walk `w` from `u`. -/
def walkEnd (E : List (ℕ × ℕ)) : ℕ → List ℕ → ℕ
  | u, [] => u
  | u, j :: rest => walkEnd E (otherEnd E j u) rest

/-- Pass 1: at each vertex `c` of the walk, write into `P c` the number of edges after this visit. -/
def posFill (E : List (ℕ × ℕ)) : ℕ → List ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | cur, [], P => Function.update P cur 0
  | cur, j :: rest, P => posFill E (otherEnd E j cur) rest (Function.update P cur (rest.length + 1))

/-- Pass 3: write `0` into `P c` for each vertex `c` of the walk. -/
def posClear (E : List (ℕ × ℕ)) : ℕ → List ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | cur, [], P => Function.update P cur 0
  | cur, j :: rest, P => posClear E (otherEnd E j cur) rest (Function.update P cur 0)

theorem length_drop_cons {rest r : List ℕ} {k j : ℕ} (h : rest.drop k = j :: r) :
    r.length < rest.length := by
  have := congrArg List.length h
  simp only [List.length_drop, List.length_cons] at this
  omega

-- The name `h` is used in the termination proof, which the unused-variable linter does not see.
set_option linter.unusedVariables false in
/-- Pass 2: jump to the last `P c` edges of the rest, keep the first one, go on. -/
def jumpRun (E : List (ℕ × ℕ)) (P : ℕ → ℕ) (cur : ℕ) (rest : List ℕ) : List ℕ :=
  match h : rest.drop (rest.length - P cur) with
  | [] => []
  | j :: r => j :: jumpRun E P (otherEnd E j cur) r
termination_by rest.length
decreasing_by exact length_drop_cons h

set_option linter.unusedVariables false in
/-- The number of steps of pass 2. -/
def jumpSteps (E : List (ℕ × ℕ)) (P : ℕ → ℕ) (cur : ℕ) (rest : List ℕ) : ℕ :=
  match h : rest.drop (rest.length - P cur) with
  | [] => 1
  | j :: r => 1 + jumpSteps E P (otherEnd E j cur) r
termination_by rest.length
decreasing_by exact length_drop_cons h

/-- The work of the shortcut: `|w| + 1` writes in pass 1, the steps of pass 2, and `|w| + 1`
writes in pass 3. -/
def eraseSteps (E : List (ℕ × ℕ)) (u : ℕ) (w : List ℕ) (P : ℕ → ℕ) : ℕ :=
  (w.length + 1) + jumpSteps E (posFill E u w P) u w + (w.length + 1)

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

variable {E : List (ℕ × ℕ)}

/-! ## Pass 2 is linear -/

theorem jumpSteps_le (P : ℕ → ℕ) : ∀ (n cur : ℕ) (rest : List ℕ), rest.length ≤ n →
    jumpSteps E P cur rest ≤ rest.length + 1
  | 0, cur, rest, hn => by
    have h0 : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h0
    rw [jumpSteps]
    split
    · simp
    · rename_i j r h; simp at h
  | n + 1, cur, rest, hn => by
    rw [jumpSteps]
    split
    · omega
    · rename_i j r h
      have hlt := length_drop_cons h
      have := jumpSteps_le P n (otherEnd E j cur) r (by omega)
      omega

/-! ## Pass 1 finds the last visits -/

/-- Pass 1 and pass 3 leave alone the vertices off the walk, and `lastFrom` keeps its default. -/
theorem off_walk {v : ℕ} : ∀ (cur : ℕ) (rest : List ℕ) (P : ℕ → ℕ) (best : List ℕ),
    v ∉ walkVerts E cur rest →
    posFill E cur rest P v = P v ∧ posClear E cur rest P v = P v ∧
      lastFrom E v cur rest best = best
  | cur, [], P, best, hv => by
    simp only [walkVerts, List.mem_singleton] at hv
    simp only [posFill, posClear, lastFrom, Function.update_of_ne hv, Ne.symm hv, ↓reduceIte,
      and_self]
  | cur, j :: rest, P, best, hv => by
    simp only [walkVerts, List.mem_cons, not_or] at hv
    obtain ⟨h1, h2, h3⟩ := off_walk (otherEnd E j cur) rest (Function.update P cur
      (rest.length + 1)) (if cur = v then j :: rest else best) hv.2
    obtain ⟨_, h2', _⟩ := off_walk (otherEnd E j cur) rest (Function.update P cur 0) best hv.2
    simp only [posFill, posClear, lastFrom]
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, Function.update_of_ne hv.1]
    · rw [h2', Function.update_of_ne hv.1]
    · rw [h3]; simp only [Ne.symm hv.1, ↓reduceIte]

/-- On the walk, pass 1 writes a number at most the length, the jump to the last `P v` edges is
where `lastFrom` lands, and the walk up to there ends at `v`. -/
theorem on_walk {v : ℕ} : ∀ (cur : ℕ) (rest : List ℕ) (P : ℕ → ℕ) (best : List ℕ),
    v ∈ walkVerts E cur rest →
    posFill E cur rest P v ≤ rest.length ∧
      lastFrom E v cur rest best = rest.drop (rest.length - posFill E cur rest P v) ∧
      walkEnd E cur (rest.take (rest.length - posFill E cur rest P v)) = v
  | cur, [], P, best, hv => by
    simp only [walkVerts, List.mem_singleton] at hv
    subst hv
    simp [posFill, lastFrom, walkEnd]
  | cur, j :: rest, P, best, hv => by
    simp only [posFill, lastFrom, List.length_cons]
    set P' := Function.update P cur (rest.length + 1)
    set best' := if cur = v then j :: rest else best
    by_cases hv' : v ∈ walkVerts E (otherEnd E j cur) rest
    · obtain ⟨h1, h2, h3⟩ := on_walk (otherEnd E j cur) rest P' best' hv'
      have hk : rest.length + 1 - posFill E (otherEnd E j cur) rest P' v =
          (rest.length - posFill E (otherEnd E j cur) rest P' v) + 1 := by omega
      refine ⟨by omega, ?_, ?_⟩
      · rw [h2, hk, List.drop_succ_cons]
      · rw [hk, List.take_succ_cons, walkEnd, h3]
    · simp only [walkVerts, List.mem_cons] at hv
      have hvc : v = cur := hv.resolve_right hv'
      obtain ⟨h1, _, h3⟩ := off_walk (otherEnd E j cur) rest P' best' hv'
      have hP : posFill E (otherEnd E j cur) rest P' v = rest.length + 1 := by
        rw [h1, hvc]; simp [P']
      refine ⟨by omega, ?_, ?_⟩
      · rw [h3, hP, Nat.sub_self, List.drop_zero]; simp [best', hvc]
      · rw [hP, Nat.sub_self, List.take_zero, walkEnd, hvc]

/-- Pass 1 over `pre ++ rest` ends as pass 1 over `rest`, from some array. -/
theorem posFill_append : ∀ (cur : ℕ) (pre rest : List ℕ) (P : ℕ → ℕ),
    ∃ Q, posFill E cur (pre ++ rest) P = posFill E (walkEnd E cur pre) rest Q
  | cur, [], rest, P => ⟨P, rfl⟩
  | cur, j :: pre, rest, P => by
    simp only [List.cons_append, posFill, walkEnd]
    exact posFill_append (otherEnd E j cur) pre rest _

theorem walkEnd_append (cur : ℕ) (a b : List ℕ) :
    walkEnd E cur (a ++ b) = walkEnd E (walkEnd E cur a) b := by
  induction a generalizing cur with
  | nil => rfl
  | cons i t ih => exact ih _

theorem mem_walkVerts_append {v : ℕ} (cur : ℕ) (pre r : List ℕ)
    (hv : v ∈ walkVerts E (walkEnd E cur pre) r) : v ∈ walkVerts E cur (pre ++ r) := by
  induction pre generalizing cur with
  | nil => exact hv
  | cons i t ih =>
    simp only [List.cons_append, walkVerts]
    exact List.mem_cons_of_mem _ (ih _ hv)

/-- Pass 3 writes `0` at each vertex of the walk. -/
theorem posClear_on_walk {v : ℕ} : ∀ (cur : ℕ) (rest : List ℕ) (P : ℕ → ℕ),
    v ∈ walkVerts E cur rest → posClear E cur rest P v = 0
  | cur, [], P, hv => by
    simp only [walkVerts, List.mem_singleton] at hv
    subst hv
    simp [posClear]
  | cur, j :: rest, P, hv => by
    simp only [posClear]
    by_cases hv' : v ∈ walkVerts E (otherEnd E j cur) rest
    · exact posClear_on_walk _ rest _ hv'
    · simp only [walkVerts, List.mem_cons] at hv
      have hvc : v = cur := hv.resolve_right hv'
      rw [(off_walk (otherEnd E j cur) rest _ [] hv').2.1, hvc, Function.update_self]

/-- On the walk, what pass 1 writes does not depend on the array it starts from. -/
theorem posFill_indep {v : ℕ} : ∀ (cur : ℕ) (rest : List ℕ) (P Q : ℕ → ℕ),
    v ∈ walkVerts E cur rest → posFill E cur rest P v = posFill E cur rest Q v
  | cur, [], P, Q, hv => by
    simp only [walkVerts, List.mem_singleton] at hv
    subst hv
    simp [posFill]
  | cur, j :: rest, P, Q, hv => by
    simp only [posFill]
    by_cases hv' : v ∈ walkVerts E (otherEnd E j cur) rest
    · exact posFill_indep _ rest _ _ hv'
    · simp only [walkVerts, List.mem_cons] at hv
      have hvc : v = cur := hv.resolve_right hv'
      rw [(off_walk (otherEnd E j cur) rest _ [] hv').1, (off_walk (otherEnd E j cur) rest _ [] hv').1,
        hvc, Function.update_self, Function.update_self]

/-- `lastFrom` from the start of the walk is the jump of pass 2. -/
theorem lastFrom_eq_drop (cur : ℕ) (rest : List ℕ) (P : ℕ → ℕ) :
    lastFrom E cur cur rest rest = rest.drop (rest.length - posFill E cur rest P cur) :=
  (on_walk cur rest P rest (mem_walkVerts_self cur rest)).2.1

/-! ## Pass 2 gives `erase` -/

/-- **Pass 2 computes `erase`**, whenever the array agrees on the walk with pass 1 over it. -/
theorem jumpRun_eq_erase_of (P : ℕ → ℕ) : ∀ (n cur : ℕ) (rest : List ℕ) (P0 : ℕ → ℕ),
    rest.length ≤ n → (∀ v ∈ walkVerts E cur rest, P v = posFill E cur rest P0 v) →
    jumpRun E P cur rest = erase E cur rest
  | 0, cur, rest, P0, hn, _ => by
    have h0 : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h0
    rw [jumpRun, erase]
    split
    · split
      · rfl
      · rename_i h; simp [lastFrom] at h
    · rename_i j r h; simp at h
  | n + 1, cur, rest, P0, hn, hP => by
    have hc := hP cur (mem_walkVerts_self cur rest)
    have hlast := lastFrom_eq_drop (E := E) cur rest P0
    rw [← hc] at hlast
    rw [jumpRun, erase]
    split
    · rename_i h
      split
      · rfl
      · rename_i j r h'; rw [hlast, h] at h'; simp at h'
    · rename_i j r h
      split
      · rename_i h'; rw [hlast, h] at h'; simp at h'
      · rename_i j' r' h'
        rw [hlast, h] at h'
        obtain ⟨rfl, rfl⟩ := List.cons.inj h'
        congr 1
        -- the rest after `j`: pass 1 over `rest` ends as pass 1 over `r`
        set k := rest.length - P cur
        have hsplit : rest = rest.take k ++ [j] ++ r := by
          rw [List.append_assoc, List.singleton_append, ← h, List.take_append_drop]
        have hend : walkEnd E cur (rest.take k) = cur := by
          have := (on_walk (E := E) cur rest P0 rest (mem_walkVerts_self cur rest)).2.2
          rw [← hc] at this; exact this
        have hendj : walkEnd E cur (rest.take k ++ [j]) = otherEnd E j cur := by
          rw [walkEnd_append, hend]; rfl
        obtain ⟨Q, hQ⟩ := posFill_append (E := E) cur (rest.take k ++ [j]) r P0
        rw [← hsplit, hendj] at hQ
        have hlt := length_drop_cons h
        apply jumpRun_eq_erase_of P n _ r Q (by omega)
        intro v hv
        have hv' : v ∈ walkVerts E cur rest := by
          rw [hsplit]
          exact mem_walkVerts_append cur _ r (by rw [hendj]; exact hv)
        rw [hP v hv', hQ]

/-- **Pass 2 computes `erase`.** -/
theorem jumpRun_eq_erase (u : ℕ) (w : List ℕ) (P : ℕ → ℕ) :
    jumpRun E (posFill E u w P) u w = erase E u w :=
  jumpRun_eq_erase_of _ w.length u w P le_rfl fun _ _ => rfl

/-- **The work of the shortcut is linear**: at most `3 (|w| + 1)`. -/
theorem eraseSteps_le (u : ℕ) (w : List ℕ) (P : ℕ → ℕ) : eraseSteps E u w P ≤ 3 * (w.length + 1) := by
  have := jumpSteps_le (E := E) (posFill E u w P) w.length u w le_rfl
  unfold eraseSteps
  omega

/-- **Pass 3 clears the array**: if it was `0` on the walk, it is the same array after the three
passes. -/
theorem posClear_posFill (u : ℕ) (w : List ℕ) (P : ℕ → ℕ) (hP : ∀ v ∈ walkVerts E u w, P v = 0) :
    posClear E u w (posFill E u w P) = P := by
  funext v
  by_cases hv : v ∈ walkVerts E u w
  · rw [hP v hv]
    exact posClear_on_walk u w _ hv
  · rw [(off_walk u w _ [] hv).2.1, (off_walk u w P [] hv).1]

end MinCostFlow.HierPaths
