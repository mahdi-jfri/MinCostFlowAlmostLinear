module

public import MinCostFlow.IPM.Machine.TargetSearch
public import MinCostFlow.IPM.Machine.TargetTestLayout
import Mathlib.Tactic.IntervalCases

/-!
# Forwarding the binary search packet

The caller saves the original half-slack flow, fixed parameters,
stage limit and radius. Only the heap and the tested offset change.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The repeated test has exactly twenty-five arguments. -/
theorem targetOffsetPacket_length {w : ℕ} (F : MinRatioFormat w) (I : Instance) (L : EpochLayout)
    (offset qp src heap limit radius : ℕ) :
    (targetOffsetPacket L F I offset qp src heap limit radius).length=25 := rfl

/-- The parent forwards the exact offset and current heap. -/
theorem targetSearch_args {w : ℕ} (F : MinRatioFormat w) (I : Instance) (L : EpochLayout)
    (offset qp src heap limit radius reg : ℕ) (st : State)
    (hreg : st.regs reg=offset)
    (hfixed : ∀ j<25,j≠6 → st.regs j=
      (targetOffsetPacket L F I offset qp src heap limit radius).getD j 0) :
    evalArgs w st (targetSearchArgs reg)=some (targetOffsetPacket L F I offset qp src heap limit radius) := by
  have hregs (j : ℕ) (hj : j<25) :
      st.regs (if j=6 then reg else j)=(targetOffsetPacket L F I offset qp src heap limit radius).getD j 0 := by
    by_cases h : j=6
    · subst j
      exact hreg
    · rw [ite_eq_right h]
      exact hfixed j hj h
  let replaced : State := {st with regs:=fun j => st.regs (if j=6 then reg else j)}
  have hh := evalArgs_range_regs (w:=w) replaced (targetOffsetPacket L F I offset qp src heap limit radius) 0
    (fun j hj => by simpa only [replaced,Nat.zero_add] using hregs j hj)
  change evalArgs w replaced ((List.range 25).map Expr.reg)=_ at hh
  unfold targetSearchArgs
  rw [← hh]
  generalize List.range 25 = indices
  induction indices with
  | nil => rfl
  | cons j js ih =>
    simp only [List.map_cons,evalArgs,ih]
    by_cases h : j=6 <;> simp only [h,ite_true,ite_false,Expr.eval,replaced]

/-- Replacing the search target and the heap keeps other packet words. -/
theorem targetOffsetPacket_fixed {w : ℕ} (F : MinRatioFormat w) (I : Instance) (L : EpochLayout)
    (offset next qp src heap newHeap limit radius j : ℕ) (hj : j<25) (h6 : j≠6) (h21 : j≠21) :
    (targetOffsetPacket L F I offset qp src heap limit radius).getD j 0=
      (targetOffsetPacket L F I next qp src newHeap limit radius).getD j 0 := by
  interval_cases j <;> simp_all [targetOffsetPacket,targetEpochPacket]

/-- The fixed words are reused for another offset at a fitting heap. -/
theorem targetOffsetPacket_words {w : ℕ} (F : MinRatioFormat w) (I : Instance) (L : EpochLayout)
    (offset next qp src heap newHeap limit radius : ℕ)
    (h : ∀ z∈targetOffsetPacket L F I offset qp src heap limit radius,z<2^w)
    (ht : next<2^w) (hh : newHeap<2^w) :
    ∀ z∈targetOffsetPacket L F I next qp src newHeap limit radius,z<2^w := by
  intro z hz
  simp only [targetOffsetPacket,targetEpochPacket,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ht | exact hh | exact h _ (by simp [targetOffsetPacket,targetEpochPacket])

end MinCostFlow.IPM.Machine
