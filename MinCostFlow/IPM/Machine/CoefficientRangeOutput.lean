module

public import MinCostFlow.IPM.Machine.CoefficientRangeGuard
import Mathlib.Tactic.Positivity

/-!
# Decoding the coefficient guard at its fixed-point scale

All five blocks share a scale. The signed integer comparisons therefore
check the same real intervals. With exact signed endpoints and a
positive minimum length, acceptance supplies Update's bounded gradient
and positive bounded length without any approximation premise.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Decode both acceptance and rejection at the represented real scale.
The predicate uses strict intervals so the admissible run can retain a
margin from the machine range endpoints. -/
theorem coefficientRangeGuard_output {w h neg g mx mn l L P v : ℕ}
    {mem mem' : ℕ → ℕ} {gradient length maximum minimum : ℝ}
    (hout : (coefficientRangeGuardContract w h).post [neg,g,mx,mn,l,L] mem v mem')
    (hn : ScalarAt mem neg h L P (-maximum))
    (hg : ScalarAt mem g h L P gradient)
    (hx : ScalarAt mem mx h L P maximum)
    (hm : ScalarAt mem mn h L P minimum)
    (hl : ScalarAt mem l h L P length) :
    mem'=mem ∧ v≤1 ∧ (v=1 ↔ |gradient|<maximum ∧ minimum<length ∧ length<maximum) := by
  have hraw : v=if Num.intVal mem neg h L<Num.intVal mem g h L ∧
      Num.intVal mem g h L<Num.intVal mem mx h L ∧
      Num.intVal mem mn h L<Num.intVal mem l h L ∧
      Num.intVal mem l h L<Num.intVal mem mx h L then 1 else 0 := hout.2
  have hbit : v≤1 := by split_ifs at hraw <;> omega
  have hiff : v=1 ↔ Num.intVal mem neg h L<Num.intVal mem g h L ∧
      Num.intVal mem g h L<Num.intVal mem mx h L ∧
      Num.intVal mem mn h L<Num.intVal mem l h L ∧
      Num.intVal mem l h L<Num.intVal mem mx h L := by
    rw [hraw]
    split_ifs <;> simp_all
  refine ⟨hout.1,hbit,?_⟩
  rw [hiff,abs_lt,← hn.2,← hg.2,← hx.2,← hm.2,← hl.2]
  simp only [Num.fixVal,div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<2^P)]
  norm_cast
  tauto

/-- Accepted represented endpoints give the nonstrict bounds required
by the min-ratio machine Update operation. -/
theorem coefficientRangeGuard_accepted {w h neg g mx mn l L P v : ℕ}
    {mem mem' : ℕ → ℕ} {gradient length maximum minimum : ℝ}
    (hout : (coefficientRangeGuardContract w h).post [neg,g,mx,mn,l,L] mem v mem')
    (hn : ScalarAt mem neg h L P (-maximum))
    (hg : ScalarAt mem g h L P gradient)
    (hx : ScalarAt mem mx h L P maximum)
    (hm : ScalarAt mem mn h L P minimum)
    (hl : ScalarAt mem l h L P length) (haccept : v=1) (hmin : 0<minimum) :
    |gradient|≤maximum ∧ minimum≤length ∧ length≤maximum ∧ 0<length := by
  have hc := (coefficientRangeGuard_output hout hn hg hx hm hl).2.2.mp haccept
  exact ⟨hc.1.le,hc.2.1.le,hc.2.2.le,hmin.trans hc.2.1⟩

end MinCostFlow.IPM.Machine
