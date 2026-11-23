module

public import MinCostFlow.IPM.Machine.TargetSearch
import Mathlib.Tactic.NormNum

/-!
# Interval arithmetic for the machine bisection

The test's flag compares the midpoint to the integral optimum.
Both updates preserve the inclusive interval and reduce its span
to less than the next power of two.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- The number of bisection rounds is the binary length of its
initial span. One additional target call recovers the flow. -/
def targetSearchRounds (radius : ℕ) : ℕ := (2*radius).size

/-- The signed optimum has a unique offset within the search radius. -/
theorem offsetTarget_optimum (B : ℕ) (z : ℤ) (hlo : -(B:ℤ)≤z) (hhi : z≤(B:ℤ)) :
    ∃ tick≤2*B,offsetTarget B tick=z := by
  let tick := (z+(B:ℤ)).toNat
  have hTick : (tick:ℤ)=z+(B:ℤ) := Int.toNat_of_nonneg (by omega)
  exact ⟨tick,by omega,by unfold offsetTarget; omega⟩

/-- The target decision transfers to the unsigned interval positions. -/
theorem offsetTarget_le_offsetTarget (B i j : ℕ) :
    offsetTarget B i≤offsetTarget B j ↔ i≤j := by
  unfold offsetTarget
  omega

/-- The midpoint fits and is strictly below the right endpoint of a
nontrivial interval. -/
theorem targetSearch_midpoint (lo hi : ℕ) (h : lo<hi) :
    lo≤lo+(hi-lo)/2 ∧ lo+(hi-lo)/2<hi := by omega

/-- Either decision gives a valid next bracket with the next binary
span bound. The two endpoints and the midpoint are unsigned words. -/
theorem targetSearch_narrow (lo hi tick fuel : ℕ)
    (hlo : lo≤tick) (hhi : tick≤hi) (hSpan : hi-lo<2^(fuel+1))
    (h : lo<hi) (bit : ℕ) (hBit : bit=1 ↔ tick≤lo+(hi-lo)/2) :
    let mid := lo+(hi-lo)/2
    let l' := if bit=1 then lo else mid+1
    let u' := if bit=1 then mid else hi
    lo≤l' ∧ l'≤tick ∧ tick≤u' ∧ u'≤hi ∧ u'-l'<2^fuel := by
  dsimp only
  rw [pow_succ] at hSpan
  by_cases hb : bit=1
  · simp only [hb,ite_true]
    exact ⟨le_rfl,hlo,hBit.mp hb,by omega,by omega⟩
  · simp only [hb,ite_false]
    have hr : ¬tick≤lo+(hi-lo)/2 := fun ht => hb (hBit.mpr ht)
    exact ⟨by omega,by omega,hhi,le_rfl,by omega⟩

/-- The fixed round count is sufficient even for radius zero. -/
theorem targetSearch_rounds_fit_span (B : ℕ) : 2*B<2^targetSearchRounds B :=
  Nat.lt_size_self _

end MinCostFlow.IPM.Machine
