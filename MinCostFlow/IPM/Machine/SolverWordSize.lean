module

public import MinCostFlow.IPM.Machine.SolverResources
import WordRAM.Entry
import MinCostFlow.Scaling.SolverContract
import Mathlib.Tactic

/-!
# Canonical word size for bounded solver calls

An allocation bound polynomial in the dimensions gives a constant
word-size multiplier. The solver is also correct at any width that
satisfies the caller-space inequality. This file constructs a canonical
call at the explicit multiplier derived from its space bound.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- If scratch is bounded by `(n+m+2)^s`, the canonical word
multiplier `s+4` suffices for the entire input, output and scratch. -/
theorem solverWorkspace_wordSize (r : SolverResources) (s : ℕ) (J : Circulation)
    (hSpace : solverWorkspace r J.n J.m≤(J.n+J.m+2)^s) :
    J.solverWords.length+J.m+solverWorkspace r J.n J.m <
      2^wordSize (s+4) J.solverWords := by
  let xs := J.solverWords
  let B := xs.length+xs.foldr max 0+2
  have hB : 2≤B := by unfold B; omega
  have hn : J.n≤xs.foldr max 0 := by
    change J.n≤max J.n _
    exact le_max_left _ _
  have hl : xs.length=2+5*J.m := J.solverWords_length
  have hj : J.n+J.m+2≤B := by unfold B; omega
  have hS : solverWorkspace r J.n J.m≤B^s := hSpace.trans (Nat.pow_le_pow_left hj s)
  have hBpow : B≤B^(s+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0<B by omega) (show 1≤s+1 by omega)
  have hBpow' : B^s≤B^(s+1) := Nat.pow_le_pow_right (show 0<B by omega) (by omega)
  have hh : 3*B^(s+1)≤B^(s+4) := by
    have he : B^(s+4)=B^(s+1)*B^3 := by
      rw [←pow_add]
    rw [he]
    have hcube : 3≤B^3 := by
      exact (by decide : 3≤2^3).trans (Nat.pow_le_pow_left hB 3)
    simpa only [Nat.mul_comm 3] using Nat.mul_le_mul_left (B^(s+1)) hcube
  have hb₁ : xs.length≤B := by unfold B; omega
  have hb₂ : J.m≤B := by omega
  have htotal : xs.length+J.m+solverWorkspace r J.n J.m≤3*B^(s+1) := by omega
  exact (htotal.trans hh).trans_lt (pow_lt_two_pow_wordSize (by omega) xs)

/-- The canonical precondition is inhabited at the stated word size on
every bounded input whose scratch has the stated polynomial bound. -/
theorem boundedIPM_pre_wordSize (r : SolverResources) (s : ℕ) (J : Circulation)
    (hS : solverWorkspace r J.n J.m≤(J.n+J.m+2)^s)
    (hc : J.CostsBounded (J.m^10))
    (hu : ∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) :
    let w := wordSize (s+4) J.solverWords
    (∀ a∈[0,J.solverWords.length],a<2^w) ∧
      (Scaling.Machine.solverContract w (solverTime r) (solverWorkspace r)).pre
        [0,J.solverWords.length] (initMem J.solverWords) := by
  dsimp only
  let w := wordSize (s+4) J.solverWords
  have hfit := solverWorkspace_wordSize r s J hS
  have hAt := listAt_initMem J.solverWords
  have hd := Scaling.Machine.solverDimensions_of_at J _ 0 J.solverWords.length hAt
  refine ⟨?_,⟨?_,zeroFrom_initMem J.solverWords,?_⟩⟩
  · intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl <;> omega
  · exact ⟨0,J.solverWords.length,rfl,J,hAt,by omega,
      fun _ hx => lt_two_pow_wordSize_of_mem (by omega) hx,hc,hfit,hu⟩
  · change J.solverWords.length+((Scaling.Machine.solverDimensions [0,J.solverWords.length]
      (initMem J.solverWords)).2+solverWorkspace r (Scaling.Machine.solverDimensions
      [0,J.solverWords.length] (initMem J.solverWords)).1 (Scaling.Machine.solverDimensions
      [0,J.solverWords.length] (initMem J.solverWords)).2)<2^w
    rw [hd]
    change J.solverWords.length+(J.m+solverWorkspace r J.n J.m)<2^w
    exact Nat.add_assoc _ _ _ ▸ hfit

end MinCostFlow.IPM.Machine
