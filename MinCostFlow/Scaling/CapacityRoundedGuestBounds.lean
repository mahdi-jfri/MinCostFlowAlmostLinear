module

public import MinCostFlow.Scaling.CapacityRoundedSolveProgram
import MinCostFlow.Scaling.BottleneckGuestSpace

/-!
# Logarithmic word width of the clipped capacity solver

On compressed polynomial-cost graphs, clipping bounds all solver
capacities by `m^40`. Its encoding base is at most `(m+2)^44`. Thus the
multiplier-five canonical guest width is at most 225 times a padded
binary logarithm. This charges guest setup to the rounded model's
linear work counter.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem rounded_encoding_poly (m n : ℕ) (hn : n≤2*m) :
    n+6*m+m^40+m^10+6≤(m+2)^44 := by
  let P := m+2
  have hP : 0<P := by dsimp only [P]; omega
  have h40 : m^40≤P^40 := Nat.pow_le_pow_left (by dsimp only [P]; omega) 40
  have h10 : m^10≤P^40 :=
    (Nat.pow_le_pow_left (by dsimp only [P]; omega) 10).trans (Nat.pow_le_pow_right hP (by decide))
  have hlinear : P≤P^40 := by simpa only [pow_one] using Nat.pow_le_pow_right hP (by decide : 1≤40)
  have hsum : n+6*m+m^40+m^10+6≤10*P^40 := by change m+2≤P^40 at hlinear; omega
  have h4 : 16≤P^4 := Nat.pow_le_pow_left (by dsimp only [P]; omega : 2≤P) 4
  have hmul : 10*P^40≤P^44 := by
    have h := Nat.mul_le_mul_right (P^40) (show 10≤P^4 by omega)
    simpa only [←pow_add] using h
  exact hsum.trans hmul

/-- The positive-magnitude clipped solver guest uses logarithmically many
bits on the compressed polynomial-cost instances of capacity scaling. -/
theorem capacityRoundedGuest_width_le (J : Circulation) (B : ℕ) (hm : 0<J.m) (hB : 0<B)
    (hn : J.n≤2*J.m) (hc : J.CostsBounded (J.m^10)) :
    wordSize 5 (J.scaledRoundedInstance B).positiveInstance.solverWords≤
      225*(Nat.clog 2 (J.m+2)+1) := by
  let K := (J.scaledRoundedInstance B).positiveInstance
  let M := J.n+J.m+J.m^40+J.m^10+2
  have hcost : K.CostsBounded M := by
    have h := (J.scaledRoundedInstance B).positiveInstance_costsBounded (J.m^10) hc
    intro e
    exact (h e).trans (by dsimp only [M]; omega)
  have hcap : ∀ e,K.capacity e≤M := by
    intro e
    have h := (J.scaledRoundedInstance B).positiveInstance_capacitiesBounded (J.m^40)
      (Nat.pow_pos hm) (fun k => scaledCapacity_le J.m B (J.capacity k) hm hB) e
    exact h.2.trans (by dsimp only [M]; omega)
  have hmax := solverWords_max_le_of_bounds K M (by change J.n+1≤M; dsimp only [M]; omega)
    (by change J.m≤M; dsimp only [M]; omega) hcap hcost (by dsimp only [M]; omega)
  have hbase : K.solverWords.length+K.solverWords.foldr max 0+2≤(J.m+2)^44 := by
    rw [K.solverWords_length]
    have hp := rounded_encoding_poly J.m J.n hn
    change 2+5*J.m+K.solverWords.foldr max 0+2≤_
    dsimp only [M] at hmax
    omega
  have hpow : (J.m+2)^44≤2^(Nat.clog 2 (J.m+2)*44) := by
    have h := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1<2) (J.m+2)) 44
    simpa only [←pow_mul] using h
  have hlog : Nat.log 2 (K.solverWords.length+K.solverWords.foldr max 0+2)≤Nat.clog 2 (J.m+2)*44 :=
    (Nat.log_le_clog _ _).trans (Nat.clog_le_of_le_pow (hbase.trans hpow))
  change 5*(Nat.log 2 (K.solverWords.length+K.solverWords.foldr max 0+2)+1)≤_
  omega

end MinCostFlow.Scaling.Machine
