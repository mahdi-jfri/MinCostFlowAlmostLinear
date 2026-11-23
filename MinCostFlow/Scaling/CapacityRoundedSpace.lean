module

public import MinCostFlow.Scaling.CapacityStepContract
import MinCostFlow.Scaling.CanonicalGuestSpace
import MinCostFlow.Scaling.BottleneckGuestSpace

/-!
# Uniform workspace for the capacity-rounded solver

The clipped solver graph has capacities at most `m^40` and unchanged
costs. A bound on dimensions and costs therefore bounds its encoding
base, canonical guest region, and host reserve by fixed powers. These
bounds do not depend on the chosen positive rounding magnitude.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Polynomial clipping makes every positive-magnitude rounded guest's
addressable region polynomial in a dimensions-and-cost bound. -/
theorem capacityRoundedGuest_space_le (J : Circulation) (B N : ℕ) (hN : 4≤N)
    (hn : J.n≤N) (hm : J.m≤N) (hc : J.CostsBounded N) (hpos : 0<J.m) (hB : 0<B) :
    2^wordSize 5 (J.scaledRoundedInstance B).positiveInstance.solverWords≤N^215 := by
  let K := (J.scaledRoundedInstance B).positiveInstance
  have hNpos : 0<N := by omega
  have hN40 : N≤N^40 := by simpa only [pow_one] using Nat.pow_le_pow_right hNpos (by decide : 1≤40)
  have hN2_40 : N^2≤N^40 := Nat.pow_le_pow_right hNpos (by decide)
  have hN2 : 16≤N^2 := Nat.pow_le_pow_left hN 2
  have hfourN : 4*N≤N^2 := by simpa only [pow_two] using Nat.mul_le_mul_right N hN
  have hcap : ∀ e,K.capacity e≤N^40 := by
    intro e
    have h := (J.scaledRoundedInstance B).positiveInstance_capacitiesBounded (J.m^40)
      (Nat.pow_pos hpos) (fun k => scaledCapacity_le J.m B (J.capacity k) hpos hB) e
    exact h.2.trans (Nat.pow_le_pow_left hm 40)
  have hcost := (J.scaledRoundedInstance B).positiveInstance_costsBounded N hc
  have hmax : K.solverWords.foldr max 0≤N^40 := solverWords_max_le_of_bounds K (N^40)
    (by change J.n+1≤N^40; omega) (by change J.m≤N^40; omega) hcap
    (fun e => (hcost e).trans hN40) (by omega)
  have h42 : 16*N^40≤N^42 := by
    have h := Nat.mul_le_mul_right (N^40) hN2
    simpa only [←pow_add] using h
  have hbase : K.solverWords.length+K.solverWords.foldr max 0+2≤N^42 := by
    rw [K.solverWords_length]
    change 2+5*J.m+K.solverWords.foldr max 0+2≤N^42
    omega
  have h43 : 2*N^42≤N^43 :=
    (Nat.mul_le_mul_right (N^42) (show 2≤N by omega)).trans_eq (pow_succ' N 42).symm
  have hdouble : 2*(K.solverWords.length+K.solverWords.foldr max 0+2)≤N^43 :=
    (Nat.mul_le_mul_left 2 hbase).trans h43
  have hguest := canonicalGuest_space_le K.solverWords
  have hp := Nat.pow_le_pow_left hdouble 5
  rw [←pow_mul] at hp
  exact hguest.trans hp

/-- One extra guest bit and its two boundary cells fit the same fixed
polynomial reserve. -/
theorem capacityRoundedGuest_margin_le (J : Circulation) (B N : ℕ) (hN : 4≤N)
    (hn : J.n≤N) (hm : J.m≤N) (hc : J.CostsBounded N) (hpos : 0<J.m) (hB : 0<B) :
    2^(wordSize 5 (J.scaledRoundedInstance B).positiveInstance.solverWords+1)+2≤N^216 := by
  have hg := capacityRoundedGuest_space_le J B N hN hn hm hc hpos hB
  have hNpos : 0<N := by omega
  have hpow : 1≤N^215 := Nat.one_le_pow 215 _ (by omega)
  have h216 : 4*N^215≤N^216 :=
    (Nat.mul_le_mul_right (N^215) hN).trans_eq (pow_succ' N 215).symm
  rw [pow_succ]
  omega

/-- The complete rounded-solve fresh-space reserve is polynomial in the
same bound, including the zero-magnitude branch. -/
theorem capacityRoundedSpace_le (J : Circulation) (B N : ℕ) (hN : 4≤N)
    (hn : J.n≤N) (hm : J.m≤N) (hc : J.CostsBounded N) (hpos : 0<J.m) :
    capacityRoundedSpace J B≤N^218 := by
  have hNpos : 0<N := by omega
  have hN215 : N≤N^215 := by simpa only [pow_one] using Nat.pow_le_pow_right hNpos (by decide : 1≤215)
  have hN218 : N≤N^218 := by simpa only [pow_one] using Nat.pow_le_pow_right hNpos (by decide : 1≤218)
  by_cases hB : B=0
  · simpa only [capacityRoundedSpace,hB,↓reduceIte] using hm.trans hN218
  · have hg := capacityRoundedGuest_space_le J B N hN hn hm hc hpos (Nat.pos_of_ne_zero hB)
    have h64 : 64≤N^3 := Nat.pow_le_pow_left hN 3
    have h218 : 64*N^215≤N^218 := by
      have h := Nat.mul_le_mul_right (N^215) h64
      simpa only [←pow_add] using h
    simp only [capacityRoundedSpace,hB,↓reduceIte]
    omega

end MinCostFlow.Scaling.Machine
