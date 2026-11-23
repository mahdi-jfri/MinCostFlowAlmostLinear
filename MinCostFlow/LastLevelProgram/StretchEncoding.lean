module

public import MinCostFlow.LastLevelProgram.Rounding
public import MinCostFlow.Num.Encoding
public import MinCostFlow.MinRatio.Layouts
import Mathlib.Tactic

/-!
# Encoding rounded last-level stretches

The shared stretch layout divides two signed blocks with the same
fractional precision. Their scales cancel. The denominator can therefore
store the grid scale as an integer numerator, even when the length
tables have a different fractional precision from the stretch grid.
-/

public section

namespace MinCostFlow.LastLevelProgram

/-- A width bound suffices to store the rounded stretch in two signed
blocks, independently of the fractional precision of the memory layout. -/
theorem roundStretch_encoding (h L P F : ℕ) {s B : ℝ}
    (hs : 1 ≤ s) (hB : roundStretch P s ≤ B)
    (hwidth : 2 * (2 : ℝ)^P * B < Num.capacity h L) :
    ∃ a d : ℤ, Num.Fits h L a ∧ Num.Fits h L d ∧ 0 < d ∧
      ((a : ℝ) / (2 : ℝ)^F) / ((d : ℝ) / (2 : ℝ)^F) = roundStretch P s := by
  let a : ℤ := -⌊-s * (2 : ℝ)^P⌋
  let d : ℤ := (2 : ℤ)^P
  have hdp : (0 : ℝ) < (d : ℝ) := by dsimp [d]; positivity
  have hdval : (d : ℝ) = (2 : ℝ)^P := by simp [d]
  have hval : roundStretch P s = (a : ℝ) / (d : ℝ) := by
    rw [hdval]
    simp [roundStretch, Num.dyadicFloor, a, neg_div]
  have hda : (d : ℝ) ≤ (a : ℝ) :=
    (one_le_div hdp).mp (hval ▸ hs.trans (roundStretch_bounds P s).1)
  have haB : (a : ℝ) ≤ B * (d : ℝ) := (div_le_iff₀ hdp).mp (hval ▸ hB)
  have haHi : 2 * (a : ℝ) < Num.capacity h L := by
    rw [← hdval] at hwidth
    linarith
  have hnonneg : (0 : ℝ) ≤ Num.capacity h L := Nat.cast_nonneg _
  refine ⟨a, d, ⟨?_, ?_⟩, ⟨?_, ?_⟩, by exact_mod_cast hdp, ?_⟩
  · exact_mod_cast (show -(Num.capacity h L : ℝ) ≤ 2 * (a : ℝ) by linarith)
  · exact_mod_cast haHi
  · exact_mod_cast (show -(Num.capacity h L : ℝ) ≤ 2 * (d : ℝ) by linarith)
  · exact_mod_cast (show 2 * (d : ℝ) < Num.capacity h L by linarith)
  · rw [hval, div_div_div_cancel_right₀ (by positivity : (2 : ℝ)^F ≠ 0)]

/-- The branch stretch capacity bound also fits the two integers
written while preparing the shared grid denominator. -/
theorem stretchUnit_fits_of_capacity {h L P : ℕ} {B : ℝ}
    (hB : 1 ≤ B) (hwidth : 2 * (2 : ℝ)^P * B < Num.capacity h L) :
    Num.Fits h L 1 ∧ Num.Fits h L ((2 : ℤ)^P) := by
  have hp : (1 : ℝ) ≤ (2 : ℝ)^P := one_le_pow₀ (by norm_num)
  have hd : 2 * (2 : ℝ)^P < Num.capacity h L :=
    (le_mul_of_one_le_right (by positivity) hB).trans_lt hwidth
  have hu : (2 : ℝ) < Num.capacity h L := by linarith
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · have hc : (0 : ℤ) ≤ Num.capacity h L := Int.natCast_nonneg _
    omega
  · exact_mod_cast hu
  · have hc : (0 : ℤ) ≤ Num.capacity h L := Int.natCast_nonneg _
    have hpow : (0 : ℤ) ≤ (2 : ℤ)^P := by positivity
    omega
  · exact_mod_cast hd

/-- A materialized stretch quotient can be read at any fractional
precision. Both blocks are scaled by the same positive factor. -/
theorem stretchValuesAt_changePrecision {mem : ℕ → ℕ} {a h L P : ℕ}
    {E : Finset ℕ} {values : ℕ → ℝ}
    (hs : MinRatio.StretchValuesAt mem a h L P E values) (Q : ℕ) :
    MinRatio.StretchValuesAt mem a h L Q E values := by
  intro e he
  obtain ⟨hn,hd,hpos,hval⟩ := hs e he
  unfold Num.fixVal at hpos hval ⊢
  have hp : (0 : ℝ) < (2 : ℝ)^P := by positivity
  have hq : (0 : ℝ) < (2 : ℝ)^Q := by positivity
  refine ⟨hn,hd,div_pos ((div_pos_iff_of_pos_right hp).mp hpos) hq,?_⟩
  rw [div_div_div_cancel_right₀ hq.ne']
  rwa [div_div_div_cancel_right₀ hp.ne'] at hval

/-- The LSF header and graph payloads are unchanged when the same
stretch quotient is read at the caller's fractional precision. -/
theorem lsfAt_changePrecision {mem : ℕ → ℕ} {a vCap eCap h L P : ℕ}
    {E : Finset ℕ} {branch : LSF}
    (ha : MinRatio.LSFAt mem a vCap eCap h L P E branch) (Q : ℕ) :
    MinRatio.LSFAt mem a vCap eCap h L Q E branch :=
  ⟨ha.1,ha.2.1,ha.2.2.1,stretchValuesAt_changePrecision ha.2.2.2 Q⟩

/-- The collection can be published using the stretch grid precision
and read using the caller's precision without rewriting its blocks. -/
theorem lsfCollectionAt_changePrecision {mem : ℕ → ℕ} {a vCap eCap h L P : ℕ}
    {E : Finset ℕ} {branches : ℕ × (ℕ → LSF)}
    (ha : MinRatio.LSFCollectionAt mem a vCap eCap h L P E branches) (Q : ℕ) :
    MinRatio.LSFCollectionAt mem a vCap eCap h L Q E branches :=
  ⟨ha.1, fun j hj => lsfAt_changePrecision (ha.2 j hj) Q⟩

/-- With path and edge lengths in the same format, rounding the stretch
uses one integer division at the target scale. Here `a` and `d` are the
unscaled path and edge length numerators. -/
theorem roundStretch_of_integer_lengths (P : ℕ) (a d : ℤ) (hd : 0 < d) :
    roundStretch P (1 + (a : ℝ) / (d : ℝ)) =
      (-( -((d + a) * (2 : ℤ)^P) / d : ℤ) : ℝ) / (2 : ℝ)^P := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hargs : -(1 + (a : ℝ) / (d : ℝ)) * (2 : ℝ)^P =
      ((-((d + a) * (2 : ℤ)^P) : ℤ) : ℝ) / (d : ℝ) := by
    push_cast
    field_simp
  rw [roundStretch, Num.dyadicFloor, hargs, Int.floor_div_cast_of_nonneg hd.le, Int.floor_intCast]
  ring

end MinCostFlow.LastLevelProgram
