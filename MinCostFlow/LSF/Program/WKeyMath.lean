module

public import MinCostFlow.Num.ShiftFacts

/-!
# Keys made of three numbers

The sort of the `W` block orders the kept indices by the triple `(labY x, labB x, rt x)`. The
sort compares one unsigned number per index, so the triple is written as one block of `3L`
limbs: `labY x` in the low `L` limbs, then `labB x`, then `rt x`. When the three numbers are
below the capacity `C` of `L` limbs, the block holds `labY x + C (labB x + C rt x)`, and two
blocks are equal exactly when the triples are equal (`key3_inj`).
-/

namespace MinCostFlow.LSF.Program

open MinCostFlow.Num

@[expose] public section

/-- The number of the triple `(a, b, c)` with digits below `C`. -/
def key3 (C a b c : ℕ) : ℕ := a + C * (b + C * c)

lemma key3_inj {C a b c a' b' c' : ℕ} (ha : a < C) (hb : b < C) (ha' : a' < C) (hb' : b' < C)
    (h : key3 C a b c = key3 C a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  unfold key3 at h
  have hC : 0 < C := by omega
  have h1 : a = a' := by
    have := congrArg (· % C) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at this
    exact this
  subst h1
  have h2 : b + C * c = b' + C * c' := by
    have := Nat.eq_of_mul_eq_mul_left hC (Nat.add_left_cancel h)
    exact this
  have h3 : b = b' := by
    have := congrArg (· % C) h2
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at this
    exact this
  subst h3
  exact ⟨rfl, rfl, Nat.eq_of_mul_eq_mul_left hC (Nat.add_left_cancel h2)⟩

lemma key3_iff {C a b c a' b' c' : ℕ} (ha : a < C) (hb : b < C) (ha' : a' < C) (hb' : b' < C) :
    key3 C a b c = key3 C a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · exact key3_inj ha hb ha' hb'
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-- Three valid `L`-limb blocks in a row form a valid `3L`-limb block, whose value is the
`key3` number of the three values. -/
lemma key3_block {mem : ℕ → ℕ} {a h L : ℕ} (h0 : Valid mem a h L) (h1 : Valid mem (a + L) h L)
    (h2 : Valid mem (a + 2 * L) h L) :
    Valid mem a h (3 * L) ∧ unsignedVal mem a h (3 * L) =
      key3 (capacity h L) (unsignedVal mem a h L) (unsignedVal mem (a + L) h L)
        (unsignedVal mem (a + 2 * L) h L) := by
  refine ⟨fun i hi => ?_, ?_⟩
  · by_cases hi1 : i < L
    · exact h0 i hi1
    · by_cases hi2 : i < 2 * L
      · have := h1 (i - L) (by omega)
        rwa [show a + L + (i - L) = a + i by omega] at this
      · have := h2 (i - 2 * L) (by omega)
        rwa [show a + 2 * L + (i - 2 * L) = a + i by omega] at this
  · rw [show 3 * L = L + (L + L) by omega, unsignedVal_split, unsignedVal_split,
      show a + L + L = a + 2 * L by omega]
    rfl

end

end MinCostFlow.LSF.Program
