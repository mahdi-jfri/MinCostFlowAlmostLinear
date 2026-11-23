module

public import MinCostFlow.IPM.Machine.Layout
import MinCostFlow.Num.ShiftFacts
import Mathlib.Tactic.NormNum

/-!
# Narrowing a queried coordinate after its capacity guard

The candidate is first formed at twice the ordinary width. Once the
strict capacity guard accepts, the lower and upper stored values bound
its numerator inside the ordinary signed range. Its low L limbs then
decode to the same value. No feasibility premise is needed before the
guard, and no unrelated rounding of coordinates occurs afterward.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Any integer between two fitting signed capacity values also fits.
The strict interval used by the IPM is a sufficient condition. -/
theorem fits_of_strict_capacity_interval {h L : ℕ} {lower x upper : ℤ}
    (hlo : Num.Fits h L lower) (hup : Num.Fits h L upper)
    (hx : lower < x ∧ x < upper) : Num.Fits h L x := by
  obtain ⟨hll,_⟩ := hlo
  obtain ⟨_,huu⟩ := hup
  change -(Num.capacity h L:ℤ) ≤ 2*x ∧ 2*x < (Num.capacity h L:ℤ)
  constructor <;> omega

/-- A fitting wide value has exactly the same signed decoding in its
low L limbs. Copying those limbs therefore preserves the fixed-point value. -/
theorem scalarAt_narrow_of_fits {mem : ℕ → ℕ} {a h L P : ℕ} {x : ℝ}
    (hx : ScalarAt mem a h (2*L) P x)
    (hfit : Num.Fits h L (Num.intVal mem a h (2*L))) :
    ScalarAt mem a h L P x := by
  have he := Num.intVal_prefix_wrap hx.1 (show L ≤ 2*L by omega)
  rw [Num.wrap_of_fits hfit] at he
  refine ⟨fun i hi => hx.1 i (by omega),?_⟩
  change (Num.intVal mem a h L:ℝ)/(2:ℝ)^P=x
  rw [he]
  exact hx.2

/-- Acceptance between represented capacity bounds justifies narrowing
an actual wide candidate to the stored-flow format, exactly. -/
theorem scalarAt_narrow_of_capacity_guard {mem : ℕ → ℕ} {lo a up h L P : ℕ}
    {lower x upper : ℝ}
    (hlo : ScalarAt mem lo h L P lower) (hx : ScalarAt mem a h (2*L) P x)
    (hup : ScalarAt mem up h L P upper) (hinside : lower < x ∧ x < upper) :
    ScalarAt mem a h L P x := by
  apply scalarAt_narrow_of_fits hx
  apply fits_of_strict_capacity_interval (Num.intVal_fits hlo.1) (Num.intVal_fits hup.1)
  have hleft : (Num.intVal mem lo h L:ℝ)/(2:ℝ)^P <
      (Num.intVal mem a h (2*L):ℝ)/(2:ℝ)^P := by
    change Num.fixVal mem lo h L P < Num.fixVal mem a h (2*L) P
    rw [hlo.2,hx.2]
    exact hinside.1
  have hright : (Num.intVal mem a h (2*L):ℝ)/(2:ℝ)^P <
      (Num.intVal mem up h L:ℝ)/(2:ℝ)^P := by
    change Num.fixVal mem a h (2*L) P < Num.fixVal mem up h L P
    rw [hx.2,hup.2]
    exact hinside.2
  have hp : (0:ℝ) < 2^P := by positivity
  rw [div_lt_div_iff_of_pos_right hp] at hleft hright
  exact ⟨by exact_mod_cast hleft,by exact_mod_cast hright⟩

end MinCostFlow.IPM.Machine
