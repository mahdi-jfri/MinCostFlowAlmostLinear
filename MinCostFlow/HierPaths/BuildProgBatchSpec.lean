module

public import MinCostFlow.HierPaths.BuildProgBatch
import MinCostFlow.HierPaths.InitLayout

/-!
# Reading the assembled batch as a router input

Each selected child contributes two consecutive equal-size sections. Their
uniform offsets and payload agree with the router's compressed pair layout.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The batch has two sections per request. -/
theorem batch_sections_length (pairs : List (Finset ℕ × Finset ℕ)) :
    (pairs.flatMap fun p => [finsetWords p.1, finsetWords p.2]).length = 2 * pairs.length := by
  induction pairs with
  | nil => simp
  | cons p pairs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    omega

private theorem batch_get_sections (pairs : List (Finset ℕ × Finset ℕ)) (i : ℕ)
    (hi : i < pairs.length) :
    let bs := pairs.flatMap fun p => [finsetWords p.1, finsetWords p.2]
    let p := pairs.getD i (∅, ∅)
    bs.getD (2 * i) [] = finsetWords p.1 ∧ bs.getD (2 * i + 1) [] = finsetWords p.2 := by
  induction pairs generalizing i with
  | nil => simp at hi
  | cons p pairs ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hx : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
      simpa only [hx, List.flatMap_cons, List.cons_append, List.nil_append, List.getD_cons_succ]
        using ih i (by simp only [List.length_cons] at hi; omega)

private theorem batch_getD_mem {α : Type} {xs : List α} {i : ℕ} {b : α} (hi : i < xs.length) :
    xs.getD i b ∈ xs := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- The batch is in the layout expected by `RouterProcContract`. -/
theorem BatchWritten.pairsAt {mem : ℕ → ℕ} {out s : ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hAt : BatchWritten mem out s pairs) (hEven : 2 * (s / 2) = s)
    (hSides : ∀ p ∈ pairs, p.1.card = s / 2 ∧ p.2.card = s / 2) :
    ListAt mem out (pairsWords pairs) := by
  obtain ⟨hLast, hRows⟩ := hAt
  let bs := pairs.flatMap fun p => [finsetWords p.1, finsetWords p.2]
  have hLen : bs.length = 2 * pairs.length := batch_sections_length pairs
  let ℓ := s / 2
  have heven : 2 * ℓ = s := hEven
  have hMul (i : ℕ) : (2 * i) * ℓ = i * s := by
    rw [show 2 * i = i * 2 by omega, Nat.mul_assoc, heven]
  have hsplit (j : ℕ) : j = 2 * (j / 2) ∨ j = 2 * (j / 2) + 1 := by omega
  have hSection : ∀ i < pairs.length,
      (bs.getD (2 * i) []).length = ℓ ∧ (bs.getD (2 * i + 1) []).length = ℓ := by
    intro i hi
    obtain ⟨hL, hR⟩ := batch_get_sections pairs i hi
    change bs.getD (2 * i) [] = _ at hL
    change bs.getD (2 * i + 1) [] = _ at hR
    obtain ⟨hl, hr⟩ := hSides _ (batch_getD_mem hi)
    simp only [hL, hR, finsetWords, Finset.length_sort]
    exact ⟨hl, hr⟩
  change ListAt mem out (layoutList bs)
  refine listAt_layoutList_of_starts (e := fun j => j * ℓ) (by simp) ?_ ?_ ?_
  · intro j hj
    have hi : j / 2 < pairs.length := by omega
    obtain ⟨hl, hr⟩ := hSection _ hi
    have he : (bs.getD j []).length = ℓ :=
      (hsplit j).elim (fun h => h.symm ▸ hl) (fun h => h.symm ▸ hr)
    change (j + 1) * ℓ = j * ℓ + (bs.getD j []).length
    rw [Nat.succ_mul, he]
  · intro j hj
    by_cases he : j = bs.length
    · rw [he, hLen, hMul]
      exact hLast
    have hi : j / 2 < pairs.length := by omega
    obtain ⟨hl, hr, _⟩ := hRows _ hi
    rcases hsplit j with he | he
    · have hM : j * ℓ = (j / 2) * s :=
        (congrArg (· * ℓ) he).trans (hMul _)
      rw [hM]
      exact (congrArg (fun x => mem (out + x)) he).trans hl
    · have hM : j * ℓ = (j / 2) * s + ℓ := by
        calc j * ℓ = (2 * (j / 2) + 1) * ℓ := congrArg (· * ℓ) he
          _ = (j / 2) * s + ℓ := by rw [Nat.succ_mul, hMul]
      rw [hM]
      rw [show out + j = out + 2 * (j / 2) + 1 by omega]
      exact hr
  · intro j hj
    have hi : j / 2 < pairs.length := by omega
    obtain ⟨_, _, hRow⟩ := hRows _ hi
    obtain ⟨hBL, hBR⟩ := batch_get_sections pairs (j / 2) hi
    change bs.getD (2 * (j / 2)) [] = _ at hBL
    change bs.getD (2 * (j / 2) + 1) [] = _ at hBR
    obtain ⟨hl, _⟩ := hSection _ hi
    obtain ⟨ha, hb⟩ := listAt_append.mp hRow
    rcases hsplit j with he | he
    · have hj' : bs.getD j [] = _ := he.symm ▸ hBL
      have hM : j * ℓ = j / 2 * s := by calc
        j * ℓ = (2 * (j / 2)) * ℓ := congrArg (· * ℓ) he
        _ = j / 2 * s := hMul _
      rw [hLen, hM, hj']
      exact ha
    · have hj' : bs.getD j [] = _ := he.symm ▸ hBR
      have hM : j * ℓ = j / 2 * s + ℓ := by calc
        j * ℓ = (2 * (j / 2) + 1) * ℓ := congrArg (· * ℓ) he
        _ = j / 2 * s + ℓ := by rw [Nat.succ_mul, hMul]
      have hOld : (finsetWords (pairs.getD (j / 2) (∅, ∅)).1).length = ℓ := by
        rw [← hBL]; exact hl
      rw [hLen, hM, hj', ← Nat.add_assoc]
      simpa only [hOld, Nat.add_assoc] using hb

end MinCostFlow.HierPaths
