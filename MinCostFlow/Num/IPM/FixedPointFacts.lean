module

public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.WordBounds
import Mathlib.Tactic

/-!
# Fixed-point framing and signed ranges for IPM arithmetic

Heap procedures preserve earlier numeric blocks. The real bound on a decoded
number also gives the integer signed-fit condition needed by exact arithmetic.
These lemmas connect the real IPM bounds to the existing arithmetic contracts.
-/

public section
namespace MinCostFlow.Num.IPM

/-- A block below a preserved heap prefix stays valid. -/
theorem valid_frozen {mem mem' : ℕ→ℕ} {a h L heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) (hv : Valid mem a h L) :
    Valid mem' a h L := by
  intro i hi
  rw [hf _ (by omega)]
  exact hv i hi

/-- Signed decoding of a block below a preserved prefix is unchanged. -/
theorem value_frozen {mem mem' : ℕ→ℕ} {a h L heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) :
    intVal mem' a h L=intVal mem a h L := intVal_congr (fun i hi => hf _ (by omega))

/-- Fixed-point decoding of a block below a preserved prefix is unchanged. -/
theorem fixVal_frozen {mem mem' : ℕ→ℕ} {a h L P heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) :
    fixVal mem' a h L P=fixVal mem a h L P := by
  simp only [fixVal,value_frozen hf ha]

/-- Two signed guard bits suffice for any numerator whose decoded absolute
value is at most `2^E`. -/
theorem fits_of_scaled_bound {h L P E : ℕ} {N : ℤ}
    (hwidth : P+E+2≤h*L) (hN : |(N:ℝ)/(2:ℝ)^P|≤(2:ℝ)^E) : Fits h L N := by
  have hp : (0:ℝ)<(2:ℝ)^P := by positivity
  rw [abs_div,abs_of_pos hp] at hN
  have hb := (div_le_iff₀ hp).mp hN
  have hb' : |N|≤(2:ℤ)^E*(2:ℤ)^P := by exact_mod_cast hb
  have hc : (2:ℤ)^(P+E+2)≤(capacity h L:ℤ) := by
    rw [capacity_eq_two_pow]
    push_cast
    exact pow_le_pow_right₀ (by decide) hwidth
  simp only [pow_add,show (2:ℤ)^2=4 by decide] at hc
  have hpos : (0:ℤ)<(2:ℤ)^P*(2:ℤ)^E := by positivity
  have hlo := neg_abs_le N
  have hhi := le_abs_self N
  constructor <;> nlinarith only [hb',hc,hpos,hlo,hhi]

/-- Exact integer subtraction decodes as subtraction of the real inputs. -/
theorem scaled_sub (N M : ℤ) (P : ℕ) :
    ((N-M:ℤ):ℝ)/(2:ℝ)^P=(N:ℝ)/(2:ℝ)^P-(M:ℝ)/(2:ℝ)^P := by
  rw [Int.cast_sub,sub_div]

end MinCostFlow.Num.IPM
