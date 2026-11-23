module

public import MinCostFlow.LSF.Program.DecompGenRec

/-!
# The greedy batching, one child at a time

`greedyGroupAux` reads the whole child list and returns the closed batches and the rest. A
program sees the children one at a time instead. It keeps, for the parent, the number `nb` of
closed batches and the sum `cur` of the open batch, and gives each child the number of the batch
it joins (`bidx`). The open batch is closed when its sum reaches `θ`.

`OnlineRun` says that a list of children was handled this way, from state `(nb, cur)` to state
`(nbF, curF)`. `greedy_online` reads off the result of `greedyGroupAux` from the numbers: batch
`j` holds the children with number `nb + j`, and the rest holds those with number `nbF`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program.DecompGen

open MinCostFlow MinCostFlow.LSF

/-- The children `xs` were handled one at a time from state `(nb, cur)` to `(nbF, curF)`. -/
def OnlineRun {α : Type*} (θ : ℝ) (f : α → ℝ) (bidx : α → ℕ) :
    ℕ → ℝ → List α → ℕ → ℝ → Prop
  | nb, cur, [], nbF, curF => nbF = nb ∧ curF = cur
  | nb, cur, x :: xs, nbF, curF => bidx x = nb ∧
    (if θ ≤ cur + f x then OnlineRun θ f bidx (nb + 1) 0 xs nbF curF
      else OnlineRun θ f bidx nb (cur + f x) xs nbF curF)

/-- Handling one more child. -/
lemma onlineRun_append {α : Type*} (θ : ℝ) (f : α → ℝ) (bidx : α → ℕ) :
    ∀ (xs : List α) (nb : ℕ) (cur : ℝ) (nbM : ℕ) (curM : ℝ) (x : α) (nbF : ℕ) (curF : ℝ),
      OnlineRun θ f bidx nb cur xs nbM curM →
      (bidx x = nbM ∧ (if θ ≤ curM + f x then nbF = nbM + 1 ∧ curF = 0
        else nbF = nbM ∧ curF = curM + f x)) →
      OnlineRun θ f bidx nb cur (xs ++ [x]) nbF curF := by
  intro xs
  induction xs with
  | nil =>
    intro nb cur nbM curM x nbF curF h hx
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hx.1, ?_⟩
    split_ifs with hc
    · rw [ite_eq_left_iff.mpr (fun h => absurd hc h)] at hx; exact hx.2
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hc)] at hx; exact hx.2
  | cons y ys ih =>
    intro nb cur nbM curM x nbF curF h hx
    obtain ⟨hy, h⟩ := h
    refine ⟨hy, ?_⟩
    split_ifs with hc
    · rw [ite_eq_left_iff.mpr (fun h => absurd hc h)] at h; exact ih _ _ _ _ _ _ _ h hx
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hc)] at h; exact ih _ _ _ _ _ _ _ h hx

/-- The numbers stay between the start and the end count. -/
lemma onlineRun_bounds {α : Type*} (θ : ℝ) (f : α → ℝ) (bidx : α → ℕ) :
    ∀ (xs : List α) (nb : ℕ) (cur : ℝ) (nbF : ℕ) (curF : ℝ),
      OnlineRun θ f bidx nb cur xs nbF curF →
      nb ≤ nbF ∧ ∀ y ∈ xs, nb ≤ bidx y ∧ bidx y ≤ nbF := by
  intro xs
  induction xs with
  | nil =>
    intro nb cur nbF curF h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨le_rfl, fun y hy => by simp at hy⟩
  | cons x xs ih =>
    intro nb cur nbF curF h
    obtain ⟨hx, h⟩ := h
    split_ifs at h with hc
    · obtain ⟨h1, h2⟩ := ih _ _ _ _ h
      refine ⟨by omega, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · have := h2 y hy; omega
    · obtain ⟨h1, h2⟩ := ih _ _ _ _ h
      refine ⟨h1, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact h2 y hy

/-- The result of `greedyGroupAux` in terms of the batch numbers. -/
theorem greedy_online {α : Type*} (θ : ℝ) (f : α → ℝ) (bidx : α → ℕ) :
    ∀ (xs acc : List α) (nb : ℕ) (cur : ℝ) (nbF : ℕ) (curF : ℝ),
      OnlineRun θ f bidx nb cur xs nbF curF → (∀ y ∈ acc, bidx y = nb) →
      (acc.map f).sum = cur →
      nb + (greedyGroupAux θ f acc cur xs).1.length = nbF ∧
      (∀ j (hj : j < (greedyGroupAux θ f acc cur xs).1.length), ∀ y,
        y ∈ (greedyGroupAux θ f acc cur xs).1[j] ↔ (y ∈ acc ∨ y ∈ xs) ∧ bidx y = nb + j) ∧
      (∀ y, y ∈ (greedyGroupAux θ f acc cur xs).2 ↔ (y ∈ acc ∨ y ∈ xs) ∧ bidx y = nbF) ∧
      ((greedyGroupAux θ f acc cur xs).2.map f).sum = curF := by
  intro xs
  induction xs with
  | nil =>
    intro acc nb cur nbF curF h hacc hsum
    obtain ⟨rfl, rfl⟩ := h
    unfold greedyGroupAux
    refine ⟨rfl, fun j hj => by simp at hj, fun y => ?_, hsum⟩
    simp only [List.not_mem_nil, or_false]
    exact ⟨fun hy => ⟨hy, hacc y hy⟩, fun hy => hy.1⟩
  | cons x xs ih =>
    intro acc nb cur nbF curF h hacc hsum
    obtain ⟨hx, h⟩ := h
    have hxacc : ∀ y ∈ x :: acc, bidx y = nb := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hacc y hy
    by_cases hc : θ ≤ cur + f x
    · rw [ite_eq_left_iff.mpr (fun h => absurd hc h)] at h
      have hgr : greedyGroupAux θ f acc cur (x :: xs) =
          ((x :: acc) :: (greedyGroupAux θ f [] 0 xs).1, (greedyGroupAux θ f [] 0 xs).2) := by
        conv_lhs => unfold greedyGroupAux
        simp only [ite_eq_left_iff.mpr (fun h => absurd hc h)]
      rw [hgr]
      obtain ⟨hlen, hbat, hrest, hcur⟩ := ih [] (nb + 1) 0 nbF curF h (by simp) (by simp)
      have hbd := onlineRun_bounds θ f bidx xs _ _ _ _ h
      refine ⟨by simp only [List.length_cons]; omega, fun j hj y => ?_, fun y => ?_, hcur⟩
      · cases j with
        | zero =>
          simp only [List.getElem_cons_zero, Nat.add_zero]
          constructor
          · intro hy
            refine ⟨?_, hxacc y hy⟩
            rcases List.mem_cons.mp hy with rfl | hy
            · exact Or.inr List.mem_cons_self
            · exact Or.inl hy
          · rintro ⟨hy, hb⟩
            rcases hy with hy | hy
            · exact List.mem_cons_of_mem _ hy
            · rcases List.mem_cons.mp hy with rfl | hy
              · exact List.mem_cons_self
              · have := (hbd.2 y hy).1; omega
        | succ j =>
          simp only [List.getElem_cons_succ]
          have hj' : j < (greedyGroupAux θ f [] 0 xs).1.length := by
            simp only [List.length_cons] at hj; omega
          rw [hbat j hj' y]
          simp only [List.not_mem_nil, false_or]
          constructor
          · rintro ⟨hy, hb⟩
            exact ⟨Or.inr (List.mem_cons_of_mem _ hy), by omega⟩
          · rintro ⟨hy, hb⟩
            rcases hy with hy | hy
            · have := hacc y hy; omega
            · rcases List.mem_cons.mp hy with rfl | hy
              · omega
              · exact ⟨hy, by omega⟩
      · simp only
        rw [hrest y]
        simp only [List.not_mem_nil, false_or]
        constructor
        · rintro ⟨hy, hb⟩
          exact ⟨Or.inr (List.mem_cons_of_mem _ hy), hb⟩
        · rintro ⟨hy, hb⟩
          rcases hy with hy | hy
          · have := hacc y hy; omega
          · rcases List.mem_cons.mp hy with rfl | hy
            · omega
            · exact ⟨hy, hb⟩
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hc)] at h
      have hgr : greedyGroupAux θ f acc cur (x :: xs) =
          greedyGroupAux θ f (x :: acc) (cur + f x) xs := by
        conv_lhs => unfold greedyGroupAux
        simp only [ite_eq_right_iff.mpr (fun h => absurd h hc)]
      rw [hgr]
      have hsum' : ((x :: acc).map f).sum = cur + f x := by
        simp only [List.map_cons, List.sum_cons, hsum, add_comm]
      obtain ⟨hlen, hbat, hrest, hcur⟩ := ih (x :: acc) nb (cur + f x) nbF curF h hxacc hsum'
      have hmem : ∀ y, (y ∈ x :: acc ∨ y ∈ xs) ↔ (y ∈ acc ∨ y ∈ x :: xs) := by
        intro y
        simp only [List.mem_cons]
        tauto
      refine ⟨hlen, fun j hj y => ?_, fun y => ?_, hcur⟩
      · rw [hbat j hj y, hmem]
      · rw [hrest y, hmem]

end MinCostFlow.LSF.Program.DecompGen
