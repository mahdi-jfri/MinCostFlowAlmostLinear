module

public import MinCostFlow.Scaling.PotentialUpdateScanProgram
import MinCostFlow.Scaling.InputLayout
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Concrete source tables for the potential-update scan

Store both signed source vectors consecutively and start fresh output
immediately after them. A finite width covering their doubled magnitude
budgets and all array addresses satisfies every scan premise jointly.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Every finite list of old-potential/dual-label pairs has simultaneous
full scan premises in canonical source memory. -/
theorem exists_potentialUpdateScan_pre (xs : List (ℤ × ℤ)) :
    ∃ w,(∀ a∈[0,2*xs.length,xs.length,4*xs.length],a<2^w) ∧
      (potentialUpdateScanContract w xs).pre [0,2*xs.length,xs.length,4*xs.length]
        (initMem (((xs.map Prod.fst).flatMap encodeInt)++((xs.map Prod.snd).flatMap encodeInt))) := by
  let input := ((xs.map Prod.fst).flatMap encodeInt)++((xs.map Prod.snd).flatMap encodeInt)
  let budget := (xs.map (fun x => 2*(x.1.natAbs+x.2.natAbs))).foldr max 0
  let w := 6*xs.length+budget+10
  have hw : 6*xs.length+budget+10<2^w := Nat.lt_two_pow_self
  have hstored := listAt_append.mp (listAt_initMem input)
  have hright : ListAt (initMem input) (2*xs.length) ((xs.map Prod.snd).flatMap encodeInt) := by
    simpa only [Nat.zero_add,integers_encode_length,List.length_map] using hstored.2
  have hzero : ZeroFrom (initMem input) (4*xs.length) := by
    have hlen : input.length=4*xs.length := by
      dsimp only [input]
      rw [List.length_append,integers_encode_length,integers_encode_length,List.length_map,List.length_map]
      omega
    simpa only [hlen] using zeroFrom_initMem input
  refine ⟨w,?_,⟨0,2*xs.length,4*xs.length,rfl,hstored.1,hright,by omega,by omega,?_,by omega⟩,hzero,?_⟩
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  · intro x hx
    have h : 2*(x.1.natAbs+x.2.natAbs)≤budget :=
      Link.elem_le_foldr_max (List.mem_map_of_mem hx)
    omega
  · change 4*xs.length+2*xs.length<2^w
    omega

end MinCostFlow.Scaling.Machine
