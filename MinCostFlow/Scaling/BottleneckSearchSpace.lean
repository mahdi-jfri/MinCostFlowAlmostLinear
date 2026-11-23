module

public import MinCostFlow.Scaling.PolyApproxContract
import MinCostFlow.Scaling.BottleneckGuestSpace
import WordRAM.LinkDefs

/-!
# Polynomial storage for the complete threshold search

The source encoding base bounds the edge count and logarithmic round
budget. Each query guest uses at most its tenth power in cells. Combining
sorting, headers, and the bounded loop gives a thirteenth-power reserve
for the full search, independent of its solver's time function.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The search's complete fresh-space reserve is polynomial in the source
encoding base, including every canonical solver guest. -/
theorem bottleneckSearchSpace_le (J : Circulation) :
    bottleneckSearchSpace J≤(J.solverWords.length+J.solverWords.foldr max 0+2)^13 := by
  let B := J.solverWords.length+J.solverWords.foldr max 0+2
  let L := Nat.clog 2 (J.m+1)
  let G := bottleneckGuestBound J (sortCapacities (List.ofFn J.capacity)).1
  let A := 12+15*J.m+2^G
  have hlen := J.solverWords_length
  have hB : 4+5*J.m≤B := by dsimp only [B]; omega
  have hB4 : 4≤B := by omega
  have hL : L≤J.m+1 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hLB : L+1≤B := by omega
  have hmB : J.m≤B := by omega
  have hBpos : 0<B := by omega
  have hB11 : B≤B^11 := by simpa only [pow_one] using Nat.pow_le_pow_right hBpos (by decide : 1≤11)
  have hB10 : B≤B^10 := by simpa only [pow_one] using Nat.pow_le_pow_right hBpos (by decide : 1≤10)
  have hB2 : 16≤B^2 := Nat.pow_le_pow_left hB4 2
  have hB2_11 : B^2≤B^11 := Nat.pow_le_pow_right hBpos (by decide)
  have hguest : 2^G≤B^10 := bottleneckGuestBound_space_le J _
  have hA : A≤4*B^10 := by dsimp only [A]; omega
  have hsort : (L+1)*J.m≤B^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hLB hmB
  have hquery : (L+1)*A≤4*B^11 := by
    calc
      _ ≤ B*(4*B^10) := Nat.mul_le_mul hLB hA
      _ = _ := by rw [Nat.mul_left_comm B 4,←pow_succ']
  have hspace : bottleneckSearchSpace J≤7*B^11 := by
    change J.m+(L+1)*J.m+5+(L+1)*A≤7*B^11
    omega
  have h13 : 16*B^11≤B^13 := by
    have h := Nat.mul_le_mul_right (B^11) hB2
    simpa only [←pow_add] using h
  change bottleneckSearchSpace J≤B^13
  exact hspace.trans (by omega)

end MinCostFlow.Scaling.Machine
