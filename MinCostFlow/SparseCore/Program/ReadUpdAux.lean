module

public import MinCostFlow.SparseCore.Program.ReadRepChange

/-!
# Facts on cells for the update of one entry of the batch

The update of one entry of the input batch (`ReadUpdOne.lean`) writes in the blocks of `T`, `F`,
`G`, the live and the frozen part, and in the cells of one edge in the stretch tables. This file
collects the facts on cells that its proof needs.

* `outBlocks`: a cell outside these blocks and tables. A cell outside the data (`readFoot`) is
  outside them (`outBlocks_of_notFoot`), and so is a fixed cell (`outBlocks_of_fixed`).
* `cell_kept`: the limbs of an edge `f ≠ e` are not the limbs of `e`.
* `UpdateWithinCaps.mono`: the caps of an update grow with the caps.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-- The cell `x` is outside the blocks of `T`, `F`, `G`, the live and the frozen part, and outside
the two stretch tables. -/
def outBlocks (vCap eCap tCap L_w : ℕ) (y : ReadConc) (x : ℕ) : Prop :=
  (x < y.q.t ∨ y.q.t + dynGraphSize vCap tCap ≤ x) ∧
  (x < y.q.f ∨ y.q.f + dynGraphSize vCap tCap ≤ x) ∧
  (x < y.q.g ∨ y.q.g + dynGraphSize vCap eCap ≤ x) ∧
  (x < y.q.num ∨ y.q.num + eCap * L_w ≤ x) ∧
  (x < y.q.den ∨ y.q.den + eCap * L_w ≤ x) ∧
  (x < y.live ∨ y.live + dynGraphSize vCap eCap ≤ x) ∧
  (x < y.frz ∨ y.frz + dynGraphSize vCap tCap ≤ x)

/-- A cell outside the data is outside the blocks. -/
theorem outBlocks_of_notFoot {vCap eCap tCap L_w r : ℕ} {y : ReadConc} {x : ℕ}
    (h : ¬ readFoot vCap eCap tCap L_w r y x) : outBlocks vCap eCap tCap L_w y x := by
  simp only [readFoot, ReadRecFoot, not_or, not_and, not_lt] at h
  obtain ⟨-, ⟨-, ht, hf, -, -, hg, hn, hd⟩, hl, hz⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hx : y.q.t ≤ x
    · exact Or.inr (ht hx)
    · exact Or.inl (by omega)
  · by_cases hx : y.q.f ≤ x
    · exact Or.inr (hf hx)
    · exact Or.inl (by omega)
  · by_cases hx : y.q.g ≤ x
    · exact Or.inr (hg hx)
    · exact Or.inl (by omega)
  · by_cases hx : y.q.num ≤ x
    · exact Or.inr (hn hx)
    · exact Or.inl (by omega)
  · by_cases hx : y.q.den ≤ x
    · exact Or.inr (hd hx)
    · exact Or.inl (by omega)
  · by_cases hx : y.live ≤ x
    · exact Or.inr (hl hx)
    · exact Or.inl (by omega)
  · by_cases hx : y.frz ≤ x
    · exact Or.inr (hz hx)
    · exact Or.inl (by omega)

/-- A fixed cell is a cell of the data and is outside the blocks. -/
theorem outBlocks_of_fixed {vCap eCap tCap L_w r : ℕ} {y : ReadConc} {x : ℕ}
    (hlay : ReadLayout r vCap eCap tCap L_w y) (h : readFixed vCap eCap r y x) :
    readFoot vCap eCap tCap L_w r y x ∧ outBlocks vCap eCap tCap L_w y x := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hlay
  simp only [readFullWords] at h1
  refine ⟨?_, ?_⟩
  · rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · simp only [readFixed, readFullWords] at h
    unfold outBlocks
    omega

/-- The limbs of an edge `f ≠ e` are not the limbs of `e`. -/
theorem cell_kept {e f L i : ℕ} (hne : f ≠ e) (hi : i < L) :
    f * L + i < e * L ∨ (e + 1) * L ≤ f * L + i := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    have : (f + 1) * L ≤ e * L := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, one_mul] at this
    omega
  · right
    have : (e + 1) * L ≤ f * L := Nat.mul_le_mul_right _ h
    omega

/-- The limbs of an edge below `cap` lie in a table of `cap` entries. -/
theorem cell_in_table {e L cap : ℕ} (he : e < cap) : e * L + L ≤ cap * L := by
  have : (e + 1) * L ≤ cap * L := Nat.mul_le_mul_right _ he
  rwa [Nat.add_mul, one_mul] at this

/-- The caps of an update grow with the caps. -/
theorem UpdateWithinCaps.mono {vCap eCap eCap' : ℕ} {u : Update}
    (h : UpdateWithinCaps vCap eCap u) (he : eCap ≤ eCap') : UpdateWithinCaps vCap eCap' u := by
  cases u with
  | insert e x z => exact lt_of_lt_of_le (show e < eCap from h) he
  | delete e => trivial
  | split v v' St Sh => exact (show v' < vCap from h)

end MinCostFlow.SparseCore.Program.Read
