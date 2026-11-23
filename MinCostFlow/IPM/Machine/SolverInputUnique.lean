module

public import MinCostFlow.Scaling.SolverContract
import MinCostFlow.Scaling.SolverInputLayout
import Mathlib.Tactic

/-!
# Uniqueness of the bounded solver input

The shared solver contract quantifies over all circulations represented
by its input memory. The header and five-word rows determine that
circulation, including the signs of its integral costs.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- A signed integer is determined by its sign test and magnitude. -/
private theorem signedMagnitude_inj (x y : ℤ)
    (hSign : (if x<0 then (1:ℕ) else 0)=(if y<0 then 1 else 0))
    (hAbs : x.natAbs=y.natAbs) : x=y := by
  have hA : |x|=|y| := by rw [←Int.natCast_natAbs,←Int.natCast_natAbs,hAbs]
  by_cases hx : x<0 <;> by_cases hy : y<0
  · rw [abs_of_neg hx,abs_of_neg hy] at hA
    omega
  · simp [hx,hy] at hSign
  · simp [hx,hy] at hSign
  · rwa [abs_of_nonneg (by omega),abs_of_nonneg (by omega)] at hA

/-- Two graphs encoded at the same address are the same circulation. -/
theorem solverWordsAt_unique (J K : Circulation) (mem : ℕ → ℕ) (a : ℕ)
    (hJ : ListAt mem a J.solverWords) (hK : ListAt mem a K.solverWords) : J=K := by
  have hj := (Scaling.Machine.solverWords_at_iff J mem a).mp hJ
  have hk := (Scaling.Machine.solverWords_at_iff K mem a).mp hK
  have hN := hj.1.symm.trans hk.1
  have hM := hj.2.1.symm.trans hk.2.1
  cases J with
  | mk n m t h u c =>
    cases K with
    | mk n' m' t' h' u' c' =>
      change n=n' at hN
      change m=m' at hM
      subst n' m'
      have hr (e : Fin m) (j : Fin 5) := (hj.2.2 e j).symm.trans (hk.2.2 e j)
      have ht : t=t' := by
        funext e
        apply Fin.ext
        exact hr e 0
      have hh : h=h' := by
        funext e
        apply Fin.ext
        exact hr e 1
      have hu : u=u' := by
        funext e
        exact hr e 2
      have hc : c=c' := by
        funext e
        exact signedMagnitude_inj _ _ (hr e 3) (hr e 4)
      subst t' h' u' c'
      rfl

end MinCostFlow.IPM.Machine
