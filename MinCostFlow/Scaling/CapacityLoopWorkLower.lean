module

public import MinCostFlow.Scaling.CapacityLoopModel

/-!
# Work paying for round-count setup

Every finite model round includes one explicit control operation. Thus
the capacity loop's work is at least its prescribed round count, which
in turn pays for computing both ceiling logarithms and initializing the
machine state. The prescribed count is always positive.
-/

public section
namespace MinCostFlow.Scaling

private theorem rounds_le_work {α : Type} (step : α → CallResult α) (fuel : ℕ) (s : α) :
    fuel≤(CallResult.forRounds step fuel s).work := by
  induction fuel with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    simp only [CallResult.forRounds,CallResult.bind,CallResult.charge]
    omega

/-- The model's explicit control charge pays for at least one operation
per capacity round. -/
theorem capacityLoop_rounds_le_work (solve : (J : Circulation) → Fin J.m → ℤ) (J : Circulation) (U : ℕ) :
    capacityRounds J.m U≤(capacityLoop solve J U).work := rounds_le_work _ _ _

/-- Even an immediately stopped capacity loop has positive model work. -/
theorem capacityLoop_work_pos (solve : (J : Circulation) → Fin J.m → ℤ) (J : Circulation) (U : ℕ) :
    0<(capacityLoop solve J U).work := by
  have h := capacityLoop_rounds_le_work solve J U
  have hrounds : 0<capacityRounds J.m U := by
    change 0<1+11*Nat.clog 2 (J.m+1)+Nat.clog 2 (U+1)
    omega
  exact hrounds.trans_le h

end MinCostFlow.Scaling
