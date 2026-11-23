module

public import MinCostFlow.HierPaths.Walks

import Mathlib.Data.List.TakeWhile

/-!
# Chronological loop erasure

The query of the path data structure first builds a walk, which may visit a vertex many times, and
then must return a path with no repeated vertex. It does so by *chronological loop erasure*:
walk along the steps and keep a stack holding a simple walk from the start to
the current vertex. When a step reaches a vertex that is already on the stack, pop back to it.
Otherwise push the step.

Here the stack is a list of steps `(e, y)` with the top first (`eraseStep`, `eraseStack`), and
`loopErase` turns the final stack back into a walk. The invariant of the stack is that, read from
the bottom, it is a step chain from the start, and that the start and the stack vertices are
distinct. The main results:

* `isWalk_loopErase`: the erased walk of a walk from `u` to `v` is a walk from `u` to `v` with no
  repeated vertex;
* `edges_loopErase_subset`, `verts_loopErase_subset`, `length_edges_loopErase_le`: its edges and
  vertices are among the original ones, and it has at most as many edges;
* `loopErase_of_closed`: a closed walk erases to the empty walk;
* `eraseOps_le`: the stack version takes at most `2 · (length + 1)` unit steps, counting one per
  step read, one per pop, and one per entry cleared at the end.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- The current vertex of a stack of steps from `s` (top first): the vertex of the top step, or
`s` for the empty stack. -/
def stackTop (s : ℕ) (st : List (ℕ × ℕ)) : ℕ :=
  (st.head?.map Prod.snd).getD s

/-- One step of loop erasure from the start `s`. A step to `s` empties the stack. A step to a
vertex on the stack pops back to that vertex. Any other step is pushed. -/
def eraseStep (s : ℕ) (st : List (ℕ × ℕ)) (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  if p.2 = s then []
  else if p.2 ∈ st.map Prod.snd then st.dropWhile (fun q => q.2 ≠ p.2)
  else p :: st

/-- The stack after loop erasure of the steps `l` from `s`, starting from the stack `st`. -/
def eraseFrom (s : ℕ) (st l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  l.foldl (eraseStep s) st

/-- The chronological loop erasure of a walk. -/
def loopErase (P : Walk) : Walk :=
  match P.verts with
  | [] => Walk.empty
  | s :: _ => ofSteps s (eraseFrom s [] (Walk.steps P)).reverse

/-- The number of unit steps of the stack version on the steps `l` from the stack `st`: one per
step read (a lookup in a position array), one per pop, and at the end one per entry cleared from
the position array, plus one for the start. -/
def eraseOps (s : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ) → ℕ
  | st, [] => st.length + 1
  | st, p :: l => 1 + (st.length - (eraseStep s st p).length) + eraseOps s (eraseStep s st p) l

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- The stack invariant: read from the bottom, the stack is a step chain from `s`, and `s` and the
stack vertices are distinct. -/
private def StackInv (G : Graph) (s : ℕ) (st : List (ℕ × ℕ)) : Prop :=
  StepChain G s st.reverse ∧ (s :: st.map Prod.snd).Nodup

private theorem stackTop_eq_stepsEnd (s : ℕ) (st : List (ℕ × ℕ)) :
    stackTop s st = stepsEnd s st.reverse := by
  cases st with
  | nil => rfl
  | cons p st =>
    rw [List.reverse_cons, stepsEnd_append]
    rfl

/-- A suffix of an invariant stack is invariant. -/
private theorem stackInv_of_suffix {G : Graph} {s : ℕ} {st st' : List (ℕ × ℕ)}
    (h : StackInv G s st) (hsuf : st' <:+ st) : StackInv G s st' := by
  obtain ⟨t, rfl⟩ := hsuf
  refine ⟨?_, ?_⟩
  · have := h.1
    rw [List.reverse_append, stepChain_append] at this
    exact this.1
  · refine List.Nodup.sublist ?_ h.2
    exact List.Sublist.cons_cons _ ((List.sublist_append_right t st').map _)

private theorem eraseStep_length_le_or (s : ℕ) (st : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    (eraseStep s st p = p :: st) ∨ (eraseStep s st p).length ≤ st.length := by
  unfold eraseStep
  split_ifs
  · right; simp
  · right; exact (List.dropWhile_suffix _).sublist.length_le
  · left; rfl

private theorem mem_eraseStep {s : ℕ} {st : List (ℕ × ℕ)} {p q : ℕ × ℕ}
    (hq : q ∈ eraseStep s st p) : q ∈ st ∨ q = p := by
  unfold eraseStep at hq
  split_ifs at hq
  · simp at hq
  · exact Or.inl ((List.dropWhile_suffix _).subset hq)
  · rcases List.mem_cons.mp hq with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- One step keeps the invariant and moves the top to the vertex reached. -/
private theorem eraseStep_inv {G : Graph} {s : ℕ} {st : List (ℕ × ℕ)} {p : ℕ × ℕ}
    (h : StackInv G s st) (hp : p.1 < G.m)
    (hm : Walk.EdgeMatches (G.edges.getD p.1 (0, 0)) (stackTop s st) p.2) :
    StackInv G s (eraseStep s st p) ∧ stackTop s (eraseStep s st p) = p.2 := by
  unfold eraseStep
  split_ifs with h1 h2
  · exact ⟨⟨trivial, by simp⟩, h1.symm⟩
  · refine ⟨stackInv_of_suffix h (List.dropWhile_suffix _), ?_⟩
    have hne : st.dropWhile (fun q => q.2 ≠ p.2) ≠ [] := by
      rw [Ne, List.dropWhile_eq_nil_iff]
      intro hall
      obtain ⟨q, hq, hq2⟩ := List.mem_map.mp h2
      have := hall q hq
      simp [hq2] at this
    have hhead := List.head_dropWhile_not (fun q : ℕ × ℕ => decide (q.2 ≠ p.2)) hne
    simp only [decide_eq_false_iff_not, not_not] at hhead
    rw [stackTop, List.head?_eq_some_head hne]
    simpa using hhead
  · refine ⟨⟨?_, ?_⟩, rfl⟩
    · rw [List.reverse_cons, stepChain_append, ← stackTop_eq_stepsEnd]
      exact ⟨h.1, hp, hm, trivial⟩
    · have hn := h.2
      rw [List.nodup_cons] at hn ⊢
      simp only [List.map_cons, List.mem_cons, List.nodup_cons, not_or] at hn ⊢
      exact ⟨⟨Ne.symm h1, hn.1⟩, h2, hn.2⟩

/-- The fold over a step chain from the current top keeps the invariant, ends at the end of the
chain, keeps only steps of the stack or of the chain, and adds at most one step per step. -/
private theorem eraseFrom_inv {G : Graph} {s : ℕ} :
    ∀ {st l : List (ℕ × ℕ)}, StackInv G s st → StepChain G (stackTop s st) l →
      StackInv G s (eraseFrom s st l) ∧
      stackTop s (eraseFrom s st l) = stepsEnd (stackTop s st) l ∧
      (∀ q ∈ eraseFrom s st l, q ∈ st ∨ q ∈ l) ∧
      (eraseFrom s st l).length ≤ st.length + l.length
  | st, [], h, _ => ⟨h, rfl, fun q hq => Or.inl hq, by simp [eraseFrom]⟩
  | st, p :: l, h, hc => by
    obtain ⟨hp, hm, hc'⟩ := hc
    obtain ⟨hinv, htop⟩ := eraseStep_inv h hp hm
    rw [← htop] at hc'
    obtain ⟨i1, i2, i3, i4⟩ := eraseFrom_inv hinv hc'
    have hfold : eraseFrom s st (p :: l) = eraseFrom s (eraseStep s st p) l := rfl
    rw [hfold]
    refine ⟨i1, by rw [i2, htop]; rfl, ?_, ?_⟩
    · intro q hq
      rcases i3 q hq with hq | hq
      · rcases mem_eraseStep hq with hq | rfl
        · exact Or.inl hq
        · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ hq)
    · have : (eraseStep s st p).length ≤ st.length + 1 := by
        rcases eraseStep_length_le_or s st p with he | he
        · rw [he]; rfl
        · omega
      simp only [List.length_cons]
      omega

/-- The final stack of a walk with at least one edge, with its properties. -/
private theorem eraseFrom_steps {G : Graph} {u v : ℕ} {P : Walk} (hP : P.IsWalk G u v)
    (he : P.edges ≠ []) :
    StackInv G u (eraseFrom u [] (Walk.steps P)) ∧
      stackTop u (eraseFrom u [] (Walk.steps P)) = v ∧
      (∀ q ∈ eraseFrom u [] (Walk.steps P), q ∈ Walk.steps P) ∧
      (eraseFrom u [] (Walk.steps P)).length ≤ (Walk.steps P).length := by
  obtain ⟨_, hc, hend⟩ := isWalk_steps hP he
  have h0 : StackInv G u [] := ⟨trivial, by simp⟩
  obtain ⟨i1, i2, i3, i4⟩ := eraseFrom_inv h0 hc
  refine ⟨i1, i2.trans hend, fun q hq => ?_, by simpa using i4⟩
  rcases i3 q hq with h | h
  · simp at h
  · exact h

/-- The first vertex of a walk with an edge is its start. -/
private theorem loopErase_eq {G : Graph} {u v : ℕ} {P : Walk} (hP : P.IsWalk G u v)
    (he : P.edges ≠ []) : loopErase P = ofSteps u (eraseFrom u [] (Walk.steps P)).reverse := by
  have hverts : P.verts = u :: (Walk.steps P).map Prod.snd := by
    conv_lhs => rw [eq_ofSteps hP he]
    exact verts_ofSteps (isWalk_steps hP he).1
  unfold loopErase
  rw [hverts]

private theorem eq_empty_of_edges_nil {G : Graph} {u v : ℕ} {P : Walk} (hP : P.IsWalk G u v)
    (he : P.edges = []) : P.verts = [] ∧ u = v := by
  rcases hP with ⟨_, _, ⟨hv, _, huv⟩ | ⟨hne, _⟩⟩
  · exact ⟨hv, huv⟩
  · exact (hne he).elim

public section

/-- The erased walk of a walk from `u` to `v` is again a walk from `u` to `v`, and it has no
repeated vertex. -/
theorem isWalk_loopErase {G : Graph} {u v : ℕ} {P : Walk} (hP : P.IsWalk G u v) :
    (loopErase P).IsWalk G u v ∧ (loopErase P).verts.Nodup := by
  by_cases he : P.edges = []
  · obtain ⟨hv, rfl⟩ := eq_empty_of_edges_nil hP he
    have hl : loopErase P = Walk.empty := by unfold loopErase; rw [hv]
    rw [hl]
    exact ⟨⟨hP.1, hP.1, Or.inl ⟨rfl, rfl, rfl⟩⟩, List.nodup_nil⟩
  · obtain ⟨⟨hc, hnd⟩, htop, _, _⟩ := eraseFrom_steps hP he
    rw [loopErase_eq hP he]
    set st := eraseFrom u [] (Walk.steps P)
    by_cases hst : st = []
    · have huv : u = v := by rw [← htop, hst]; rfl
      subst huv
      rw [hst]
      exact ⟨⟨hP.1, hP.1, Or.inl ⟨rfl, rfl, rfl⟩⟩, List.nodup_nil⟩
    · have hrev : st.reverse ≠ [] := by simpa using hst
      refine ⟨(isWalk_ofSteps_iff hrev).mpr ⟨hP.1, hP.2.1, hc, ?_⟩, ?_⟩
      · rw [← stackTop_eq_stepsEnd, htop]
      · rw [verts_ofSteps hrev, List.map_reverse]
        rw [List.nodup_cons] at hnd ⊢
        exact ⟨by simpa using hnd.1, List.nodup_reverse.mpr hnd.2⟩

/-- The edges of the erased walk are edges of the walk. -/
theorem edges_loopErase_subset {G : Graph} {u v : ℕ} {P : Walk} (hP : P.IsWalk G u v) :
    ∀ e ∈ (loopErase P).edges, e ∈ P.edges := by
  intro e hmem
  by_cases he : P.edges = []
  · obtain ⟨hv, _⟩ := eq_empty_of_edges_nil hP he
    have hl : loopErase P = Walk.empty := by unfold loopErase; rw [hv]
    rw [hl] at hmem
    simp [Walk.empty] at hmem
  · obtain ⟨_, _, hsub, _⟩ := eraseFrom_steps hP he
    rw [loopErase_eq hP he, edges_ofSteps] at hmem
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
    exact (List.of_mem_zip (hsub q (List.mem_reverse.mp hq))).1

/-- The vertices of the erased walk are vertices of the walk. -/
theorem verts_loopErase_subset {G : Graph} {u v : ℕ} {P : Walk} (hP : P.IsWalk G u v) :
    ∀ x ∈ (loopErase P).verts, x ∈ P.verts := by
  intro x hmem
  by_cases he : P.edges = []
  · obtain ⟨hv, _⟩ := eq_empty_of_edges_nil hP he
    have hl : loopErase P = Walk.empty := by unfold loopErase; rw [hv]
    rw [hl] at hmem
    simp [Walk.empty] at hmem
  · obtain ⟨_, _, hsub, _⟩ := eraseFrom_steps hP he
    have hverts : P.verts = u :: (Walk.steps P).map Prod.snd := by
      conv_lhs => rw [eq_ofSteps hP he]
      exact verts_ofSteps (isWalk_steps hP he).1
    rw [loopErase_eq hP he] at hmem
    unfold ofSteps at hmem
    split_ifs at hmem
    · simp [Walk.empty] at hmem
    · rw [hverts]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact List.mem_cons_self ..
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
        exact List.mem_cons_of_mem _ (List.mem_map_of_mem (hsub q (List.mem_reverse.mp hq)))

/-- The erased walk has at most as many edges as the walk. -/
theorem length_edges_loopErase_le {G : Graph} {u v : ℕ} {P : Walk} (hP : P.IsWalk G u v) :
    (loopErase P).edges.length ≤ P.edges.length := by
  by_cases he : P.edges = []
  · obtain ⟨hv, _⟩ := eq_empty_of_edges_nil hP he
    have hl : loopErase P = Walk.empty := by unfold loopErase; rw [hv]
    rw [hl]
    simp [Walk.empty]
  · obtain ⟨_, _, _, hlen⟩ := eraseFrom_steps hP he
    rw [loopErase_eq hP he, edges_ofSteps, List.length_map, List.length_reverse]
    refine hlen.trans ?_
    rw [Walk.steps, List.length_zip]
    exact min_le_left _ _

/-- A closed walk erases to the empty walk. -/
theorem loopErase_of_closed {G : Graph} {u : ℕ} {P : Walk} (hP : P.IsWalk G u u) :
    loopErase P = Walk.empty := by
  by_cases he : P.edges = []
  · obtain ⟨hv, _⟩ := eq_empty_of_edges_nil hP he
    unfold loopErase; rw [hv]
  · obtain ⟨⟨_, hnd⟩, htop, _, _⟩ := eraseFrom_steps hP he
    rw [loopErase_eq hP he]
    cases hst : eraseFrom u [] (Walk.steps P) with
    | nil => rfl
    | cons q st =>
      exfalso
      rw [hst] at hnd htop
      have hq : q.2 = u := htop
      simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hnd
      exact hnd.1.1 hq.symm

/-- The stack version of loop erasure on the steps `l` from the stack `st` takes at most
`2 · |l| + |st| + 1` unit steps. -/
theorem eraseOps_le_aux (s : ℕ) :
    ∀ st l : List (ℕ × ℕ), eraseOps s st l ≤ 2 * l.length + st.length + 1
  | st, [] => by simp [eraseOps]
  | st, p :: l => by
    have ih := eraseOps_le_aux s (eraseStep s st p) l
    simp only [eraseOps, List.length_cons]
    rcases eraseStep_length_le_or s st p with he | he
    · rw [he] at ih ⊢
      simp only [List.length_cons] at ih ⊢
      omega
    · omega

/-- The stack version of loop erasure of a walk with `L` edges takes at most `2 · (L + 1)` unit
steps: each step of the walk is read once and pushed at most once, each push is popped at most
once, and each entry left at the end is cleared once. -/
theorem eraseOps_le (P : Walk) (s : ℕ) :
    eraseOps s [] (Walk.steps P) ≤ 2 * (P.edges.length + 1) := by
  have h := eraseOps_le_aux s [] (Walk.steps P)
  have hl : (Walk.steps P).length ≤ P.edges.length := by
    rw [Walk.steps, List.length_zip]; exact min_le_left _ _
  simp only [List.length_nil] at h
  omega

end

end MinCostFlow.HierPaths
