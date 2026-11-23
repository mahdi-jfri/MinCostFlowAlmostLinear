module

public import MinCostFlow.Scaling.CapacityStepContract
import MinCostFlow.Scaling.CapacityNumericFacts
import MinCostFlow.Scaling.BottleneckGuestSpace
import MinCostFlow.Scaling.BottleneckSearchSpace

/-!
# Uniform residual and approximation storage bounds

The sum of graph dimensions and input bounds controls every original and
residual word. The residual encoding base is at most its fourth power.
The proved search-space bound then controls the entire residual
approximation, independently of the current bounded flow.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A common numerical base for all capacity-step coordinates and arrays. -/
def capacityStepNumberBase (J : Circulation) (C U : ℕ) : ℕ := J.n+2*J.m+C+U+4

/-- Every bounded residual has word maximum at most the square of the
common base and encoding size base at most its fourth power. -/
theorem capacityResidual_encoding_bounds (J : Circulation) (s : CapacityState J) (C U : ℕ)
    (hf : ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) (hC : J.CostsBounded C)
    (hu : ∀ e,J.capacity e≤U) :
    let D := capacityStepNumberBase J C U
    (J.residual s.flow).solverWords.foldr max 0≤D^2 ∧
      (J.residual s.flow).solverWords.length+(J.residual s.flow).solverWords.foldr max 0+2≤D^4 := by
  let D := capacityStepNumberBase J C U
  let R := J.residual s.flow
  change R.solverWords.foldr max 0≤D^2 ∧ R.solverWords.length+R.solverWords.foldr max 0+2≤D^4
  have hD : J.n+2*J.m+C+U+4=D := rfl
  have hD4 : 4≤D := by omega
  have hfourD : 4*D≤D^2 := by simpa only [pow_two] using Nat.mul_le_mul_right D hD4
  have h16 : 16≤D^2 := Nat.pow_le_pow_left hD4 2
  have hRn : R.n=J.n := rfl
  have hRm : R.m=J.m+J.m := rfl
  have hcap := J.residual_capacities_le s.flow (integral_capacity_bounds_cast J s.flow hf) U hu
  have hcost := J.residual_costsBounded s.flow C hC
  have hmax : R.solverWords.foldr max 0≤D^2 := solverWords_max_le_of_bounds R (D^2)
    (by rw [hRn]; omega) (by rw [hRm]; omega)
    (fun e => (hcap e).trans (by omega)) (fun e => (hcost e).trans (by omega)) (by omega)
  have hlen : R.solverWords.length≤3*D^2 := by rw [R.solverWords_length,hRm]; omega
  have hpow : 16*D^2≤D^4 := by
    have h := Nat.mul_le_mul_right (D^2) h16
    simpa only [←pow_add] using h
  exact ⟨hmax,by omega⟩

/-- The residual approximation's full fresh-space reserve is bounded
uniformly over all starting flows satisfying the original capacities. -/
theorem capacityApproxSpace_le (J : Circulation) (s : CapacityState J) (C U : ℕ)
    (hf : ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) (hC : J.CostsBounded C)
    (hu : ∀ e,J.capacity e≤U) :
    capacityApproxSpace (J.residual s.flow)≤(capacityStepNumberBase J C U)^56 := by
  let D := capacityStepNumberBase J C U
  let R := J.residual s.flow
  change capacityApproxSpace R≤D^56
  have hD : J.n+2*J.m+C+U+4=D := rfl
  have hD4 : 4≤D := by omega
  have hDpos : 0<D := by omega
  have hfourD : 4*D≤D^2 := by simpa only [pow_two] using Nat.mul_le_mul_right D hD4
  have h256 : 256≤D^4 := Nat.pow_le_pow_left hD4 4
  have h2_52 : D^2≤D^52 := Nat.pow_le_pow_right hDpos (by decide)
  have hbase := (capacityResidual_encoding_bounds J s C U hf hC hu).2
  have hsearch := bottleneckSearchSpace_le R
  have hsearchD : bottleneckSearchSpace R≤D^52 := by
    have hp := Nat.pow_le_pow_left hbase 13
    rw [←pow_mul] at hp
    exact hsearch.trans hp
  have hlinear : 10+3*R.n+33*R.m+12≤20*D^2 := by
    change 10+3*J.n+33*(J.m+J.m)+12≤20*D^2
    omega
  have hpow : 256*D^52≤D^56 := by
    have h := Nat.mul_le_mul_right (D^52) h256
    simpa only [←pow_add] using h
  change bottleneckSearchSpace R+10+3*R.n+33*R.m+12≤D^56
  omega

end MinCostFlow.Scaling.Machine
