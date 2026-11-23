module

public import MinCostFlow.Num.Representation
public import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.NormNum

/-!
# Exact stretch readouts using fixed-point blocks

The stretches in Section 5 (Definition 5.3, page 17) divide a tree-path
length by an edge length. Even dyadic lengths need not give a dyadic
stretch. For example, path length two and edge length three give `5/3`.
A stretch readout therefore stores numerator and denominator tables,
each in the shared fixed-point format. Reading their quotient recovers
the model's exact stretch, without requiring a single fixed-point block
to hold that quotient.

The descriptor has two pointers. Each table has `L` limbs per edge name.
The denominator is positive. This is a layout choice and adds no stretch
or forest-quality guarantee to the model.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

/-- A two-pointer descriptor for exact stretch quotients of fixed-point
numerator and denominator tables. Every stored scalar is a numeric-library
block at the same precision. -/
def StretchValuesAt (mem : ℕ → ℕ) (a h L P : ℕ) (E : Finset ℕ)
    (values : ℕ → ℝ) : Prop :=
  ∀ e ∈ E,
    Num.Valid mem (mem a + e * L) h L ∧
    Num.Valid mem (mem (a + 1) + e * L) h L ∧
    0 < Num.fixVal mem (mem (a + 1) + e * L) h L P ∧
    Num.fixVal mem (mem a + e * L) h L P /
      Num.fixVal mem (mem (a + 1) + e * L) h L P = values e

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

/-- No numeric cells are needed for an empty stretch domain. -/
theorem stretchValuesAt_empty (mem : ℕ → ℕ) (a h L P : ℕ) (values : ℕ → ℝ) :
    StretchValuesAt mem a h L P ∅ values := by
  intro e he
  cases he

/-- Values outside the active edge set do not affect a stretch readout. -/
theorem StretchValuesAt.of_eqOn {mem : ℕ → ℕ} {a h L P : ℕ}
    {E : Finset ℕ} {values values' : ℕ → ℝ}
    (hv : StretchValuesAt mem a h L P E values)
    (heq : ∀ e ∈ E, values e = values' e) : StretchValuesAt mem a h L P E values' := by
  intro e he
  exact ⟨(hv e he).1, (hv e he).2.1, (hv e he).2.2.1,
    (hv e he).2.2.2.trans (heq e he)⟩

/-- A non-dyadic stretch has an exact readout using two four-limb blocks.
The same blocks work at every common fixed-point precision. -/
theorem stretchValuesAt_five_thirds (P : ℕ) :
    ∃ mem, StretchValuesAt mem 0 1 4 P {0} (fun _ => (5 / 3 : ℝ)) := by
  let mem : ℕ → ℕ := fun a => [2, 6, 1, 0, 1, 0, 1, 1, 0, 0][a]?.getD 0
  have hn : Num.Valid mem 2 1 4 ∧ Num.intVal mem 2 1 4 = 5 := by unfold Num.Valid; decide
  have hd : Num.Valid mem 6 1 4 ∧ Num.intVal mem 6 1 4 = 3 := by unfold Num.Valid; decide
  refine ⟨mem, ?_⟩
  intro e he
  have he0 : e = 0 := Finset.mem_singleton.mp he
  subst e
  change Num.Valid mem 2 1 4 ∧ Num.Valid mem 6 1 4 ∧
    0 < Num.fixVal mem 6 1 4 P ∧ Num.fixVal mem 2 1 4 P / Num.fixVal mem 6 1 4 P = 5 / 3
  refine ⟨hn.1, hd.1, ?_, ?_⟩
  · rw [Num.fixVal, hd.2]
    exact div_pos (by norm_num) (pow_pos (zero_lt_two : (0 : ℝ) < 2) P)
  · rw [Num.fixVal, Num.fixVal, hn.2, hd.2]
    have hs : (2 : ℝ) ^ P ≠ 0 := ne_of_gt (pow_pos (zero_lt_two : (0 : ℝ) < 2) P)
    field_simp
    norm_num

end MinCostFlow.MinRatio
