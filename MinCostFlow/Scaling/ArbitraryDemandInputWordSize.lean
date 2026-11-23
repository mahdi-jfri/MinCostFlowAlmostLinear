module

public import MinCostFlow.Scaling.ArbitraryDemandContract
import MinCostFlow.Scaling.ScalingSourceWidth
import MinCostFlow.Scaling.InputMagnitudeBounds
import WordRAM.Entry
import WordRAM.LinkDefs
import Mathlib.Data.List.MinMax

/-!
# One word-size multiplier on the original problem encoding

The statement's cost and capacity maxima are bounded by the largest
original input word. The internal `(m+1)*U` budget is bounded by the square
of the original source base. Adding the supplied bounds therefore raises
that base by at most a cube. The ten complete scaling regions fit power
98306 of the original base. Multiplier 131072 on `I.encode` covers the
entire arbitrary-demand program, including two extra entry cells reserved
for the computed input maxima.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

set_option exponentiation.threshold 262144 in
set_option maxRecDepth 524288 in
/-- Fixed original-input multiplier 131072 covers ten complete phase
regions and two cells for entry metadata, for every valid instance. -/
theorem arbitraryDemand_input_space_wordSize (I : Instance) (hv : I.IsValid) :
    I.encode.length+2+10*2^wordSize 16384
      (I.encode++[max I.maxCost 1,(I.m+1)*I.maxCapacity])<2^wordSize 131072 I.encode := by
  let M := I.encode.foldr max 0
  let b := I.encode.length+M+2
  let source := I.encode++[max I.maxCost 1,(I.m+1)*I.maxCapacity]
  let region := 2^wordSize 16384 source
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
  have hpower : (source.length+source.foldr max 0+2)^32768≤b^98304 := by
    simpa only [←pow_mul] using Nat.pow_le_pow_left hsourceBase 32768
  have hregion : region≤b^98304 := (wordCapacity_le_source_power 16384 source).trans hpower
  have hbpow : b≤b^98304 := Nat.le_pow (by decide)
  have hreserve : I.encode.length+2+10*region≤11*b^98304 := by omega
  have hnext : 11*b^98304≤b^98306 :=
    (Nat.mul_le_mul_right (b^98304) (show 11≤b^2 by omega)).trans_eq (pow_add b 2 98304).symm
  have hfull : b^98306≤b^131072 := Nat.pow_le_pow_right hbpos (by decide)
  have hp := pow_lt_two_pow_wordSize (by decide : 1≤131072) I.encode
  change b^131072<2^wordSize 131072 I.encode at hp
  exact ((hreserve.trans hnext).trans hfull).trans_lt hp

/-- At multiplier 131072 on exactly `I.encode`, the original maxima and
canonical memory satisfy every arbitrary-demand entry premise jointly. -/
theorem arbitraryDemand_pre_input_wordSize (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (I : Instance) (hv : I.IsValid) :
    (∀ x∈[0,I.maxCost,I.maxCapacity,I.encode.length],x<2^wordSize 131072 I.encode) ∧
      (arbitraryDemandContract (wordSize 131072 I.encode) solver entry T hproc I hv I.maxCost I.maxCapacity).pre
        [0,I.maxCost,I.maxCapacity,I.encode.length] (initMem I.encode) := by
  let region := 2^wordSize 16384 (I.encode++[max I.maxCost 1,(I.m+1)*I.maxCapacity])
  let w := wordSize 131072 I.encode
  have hs := arbitraryDemand_input_space_wordSize I hv
  change I.encode.length+2+10*region<2^w at hs
  have hC : max I.maxCost 1<region := lt_two_pow_wordSize_of_mem (by decide)
    (List.mem_append_right _ List.mem_cons_self)
  have hU : (I.m+1)*I.maxCapacity<region := lt_two_pow_wordSize_of_mem (by decide)
    (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hUle : I.maxCapacity≤(I.m+1)*I.maxCapacity := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right I.maxCapacity (show 1≤I.m+1 by omega)
  have hCraw : I.maxCost<region := (le_max_left _ _).trans_lt hC
  have hUraw : I.maxCapacity<region := hUle.trans_lt hU
  change (∀ x∈[0,I.maxCost,I.maxCapacity,I.encode.length],x<2^w) ∧
    (arbitraryDemandContract w solver entry T hproc I hv I.maxCost I.maxCapacity).pre
      [0,I.maxCost,I.maxCapacity,I.encode.length] (initMem I.encode)
  refine ⟨?_,0,I.encode.length,rfl,listAt_initMem _,by omega,?_,?_,?_,zeroFrom_initMem _,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · intro e
    exact Link.elem_le_foldr_max (List.mem_map.mpr ⟨I.edge e,List.getElem_mem e.isLt,rfl⟩)
  · intro e
    exact lower_natAbs_le_maxCapacity I _ (List.getElem_mem e.isLt)
  · intro e
    exact upper_natAbs_le_maxCapacity I _ (List.getElem_mem e.isLt)
  · change I.encode.length+10*region<2^w
    omega

end MinCostFlow.Scaling.Machine
