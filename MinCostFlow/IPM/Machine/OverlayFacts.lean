module

public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.ShiftFacts
import Mathlib.Tactic.Linarith

/-!
# A safe wide sum for queried flow coordinates

A rejected target need not preserve feasible flows. Adding its queried
increment in the ordinary output width could wrap before a range guard
runs. Two fitting signed blocks always have an exact sum in twice the
width. This permits checking the candidate before narrowing it to the
stored-flow format, without a feasibility hypothesis for rejected runs.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The sum of two signed L-limb values fits in 2L limbs, including the
empty-block case. This needs no bound on the represented flow. -/
theorem overlay_sum_fits_double {h L : ℕ} {x y : ℤ}
    (hx : Num.Fits h L x) (hy : Num.Fits h L y) : Num.Fits h (2*L) (x+y) := by
  have hc : 0 < Num.capacity h L := Num.capacity_pos h L
  have he : Num.capacity h (2*L)=Num.capacity h L*Num.capacity h L := by
    rw [show 2*L=L+L by omega,Num.capacity_add]
  obtain ⟨hxl,hxu⟩ := hx
  obtain ⟨hyl,hyu⟩ := hy
  change -(Num.capacity h (2*L):ℤ) ≤ 2*(x+y) ∧ 2*(x+y) < (Num.capacity h (2*L):ℤ)
  rw [he]
  push_cast
  by_cases hc1 : Num.capacity h L=1
  · rw [hc1] at hxl hxu hyl hyu ⊢
    omega
  · have hc2 : (2:ℤ) ≤ Num.capacity h L := by exact_mod_cast (show 2 ≤ Num.capacity h L by omega)
    have hwide : 2*(Num.capacity h L:ℤ) ≤ (Num.capacity h L:ℤ)*(Num.capacity h L:ℤ) := by
      nlinarith only [hc2]
    constructor <;> omega

end MinCostFlow.IPM.Machine
