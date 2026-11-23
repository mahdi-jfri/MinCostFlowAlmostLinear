module

public import MinCostFlow.Scaling.InputMagnitudeBounds
import MinCostFlow.Scaling.ScalingSourceWidth
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Original-input width for scaling phase reservations

The original encoding must hold the ten fresh phase regions used by
the scaling reduction on page 15. If a phase uses a word multiplier
q on its extended encoding, multiplier 8*q suffices on the original input.
-/

public section
namespace MinCostFlow.Final
open WordRAM Scaling.Machine

/-- The original-input multiplier covers ten complete phase
regions and two cells for entry metadata, for every valid instance. -/
theorem scratch_input_space_wordSize (q : ℕ) (hq : 1 ≤ q) (I : Instance) (hv : I.IsValid) :
    I.encode.length+2+10*2^wordSize q
      (I.encode++[max I.maxCost 1,(I.m+1)*I.maxCapacity])<2^wordSize (8*q) I.encode := by
  let M := I.encode.foldr max 0
  let b := I.encode.length+M+2
  let source := I.encode++[max I.maxCost 1,(I.m+1)*I.maxCapacity]
  let region := 2^wordSize q source
  have hlen := instance_encode_length I hv
  have hb4 : 4≤b := by omega
  have hbpos : 0<b := by omega
  have hc : I.maxCost≤M := maxCost_le_encode_max I
  have hu : I.maxCapacity≤M := maxCapacity_le_encode_max I
  have hm1 : I.m+1≤b := by omega
  have hK : max I.maxCost 1≤b := max_le (by omega) (by omega)
  have hU : (I.m+1)*I.maxCapacity≤b^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hm1 (show I.maxCapacity≤b by omega)
  have hb2 : 16≤b^2 := Nat.pow_le_pow_left hb4 2
  have h2b : 2*b≤b^2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right b (show 2≤b by omega)
  have hword : ∀ x∈source,x≤b^2 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hmax : x≤M := Link.elem_le_foldr_max hx
      omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl <;> omega
  have hsourceMax : source.foldr max 0≤b^2 := List.max_le_of_forall_le source _ hword
  have hsourceLen : source.length≤b := by
    simp only [source,List.length_append,List.length_cons,List.length_nil]
    omega
  have hsourceBase : source.length+source.foldr max 0+2≤b^3 := by
    have hnext : 2*b^2≤b^3 :=
      (Nat.mul_le_mul_right (b^2) (show 2≤b by omega)).trans_eq (pow_succ' b 2).symm
    omega
  have hpower : (source.length+source.foldr max 0+2)^(2*q)≤b^(6*q) := by
    simpa only [←pow_mul, show 3*(2*q) = 6*q by omega] using Nat.pow_le_pow_left hsourceBase (2*q)
  have hregion : region≤b^(6*q) := (wordCapacity_le_source_power q source).trans hpower
  have hbpow : b≤b^(6*q) := Nat.le_pow (by omega)
  have hreserve : I.encode.length+2+10*region≤11*b^(6*q) := by omega
  have hnext : 11*b^(6*q)≤b^(6*q+2) :=
    (Nat.mul_le_mul_right (b^(6*q)) (show 11≤b^2 by omega)).trans_eq (by rw [Nat.add_comm (6*q) 2, pow_add])
  have hfull : b^(6*q+2)≤b^(8*q) := Nat.pow_le_pow_right hbpos (by omega)
  have hp := pow_lt_two_pow_wordSize (by omega : 1≤8*q) I.encode
  change b^(8*q)<2^wordSize (8*q) I.encode at hp
  exact ((hreserve.trans hnext).trans hfull).trans_lt hp

end MinCostFlow.Final
