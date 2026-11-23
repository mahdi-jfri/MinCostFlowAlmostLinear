module

public import MinCostFlow.Num.IPM.LengthArray
public import MinCostFlow.Num.IPM.GradientArray
import Mathlib.Tactic.Ring

/-!
# Explicit workspace polynomials for coefficient refresh

The numerical modules expose bounds for their returned heap pointers.
Reserve their complete workspaces before the next call, so that output
arrays and scratch cells cannot overlap. Expanding the numerical bounds
into sums and products gives quantities the machine can compute with
word arithmetic. Each formula is equal to the imported bound.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- Workspace per edge for a numerical length refresh. -/
def lengthWorkspace (L P E : ℕ) : ℕ :=
  270*L*L+409*L+24+6*(P+4)*(5*L*L+24*L+3)+
    2*E*(3*L+1)+(4*E+12)*(11*L+1)

/-- Workspace per edge for a numerical gradient refresh. -/
def gradientWorkspace (L P E : ℕ) : ℕ :=
  lengthWorkspace L P E+45*L*L+65*L+3

/-- Expanding the numerical length workspace leaves only additions and
multiplications, including every logarithm and power workspace. -/
theorem lengthWorkspace_eq (L P E : ℕ) :
    lengthWorkspace L P E=Num.IPM.lengthSpace L P E := by
  simp only [lengthWorkspace,Num.IPM.lengthSpace,Num.IPM.lengthFromSlacksSpace,
    Num.IPM.slackPowerSpace,Num.negativePowerSpace,Num.logarithmSpace,
    Num.normalizedLogarithmSpace,Num.rangeLogarithmSpace,Num.logHornerSpace,
    Num.logHornerStepSpace,Num.fixedDivideSpace,Num.integerDivideSpace,
    Num.unsignedDivideSpace,Num.exponentialSpace,Num.positiveExponentialSpace,
    Num.expHornerSpace,Num.roundedSquaringSpace]
  ring

/-- The gradient's extra workspaces are also included exactly. -/
theorem gradientWorkspace_eq (L P E : ℕ) :
    gradientWorkspace L P E=Num.IPM.gradientSpace L P E := by
  simp only [gradientWorkspace,lengthWorkspace_eq,Num.IPM.gradientSpace,
    Num.IPM.gradientFromSlacksSpace,Num.IPM.costTermSpace,
    Num.IPM.barrierFromSlacksSpace,Num.IPM.lengthSpace,Num.IPM.lengthFromSlacksSpace,
    Num.fixedDivideSpace,Num.integerDivideSpace,Num.unsignedDivideSpace]
  ring

/-- Allocation of the whole length vector, including its guard block. -/
theorem lengthArrayWorkspace_eq (m L P E : ℕ) :
    (m+1)*L+m*lengthWorkspace L P E=Num.IPM.lengthArraySpace m L P E := by
  rw [lengthWorkspace_eq]
  rfl

/-- Allocation of the whole gradient vector, including its guard block. -/
theorem gradientArrayWorkspace_eq (m L P E : ℕ) :
    (m+1)*L+m*gradientWorkspace L P E=Num.IPM.gradientArraySpace m L P E := by
  rw [gradientWorkspace_eq]
  rfl

end MinCostFlow.IPM.Machine
