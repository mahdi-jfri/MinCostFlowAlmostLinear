module

public import MinCostFlow.Statement.Problem
public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Removing one lower capacity

The general-flow reduction in the proof of Lemma C.1 of Chen et al.,
arXiv:2203.00671v2, subtracts each lower capacity from its upper capacity.
After checking their order, the difference is nonnegative. Equal signs
subtract magnitudes in the appropriate order. Opposite signs add them.
This procedure returns the unsigned capacity without allocating memory.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments are canonical signed lower and upper capacities. -/
def capacityDifferenceBody : Stmt :=
  .cond (.bin .eq (.reg 0) (.reg 2))
    (.cond (.bin .eq (.reg 0) (.const 0))
      (.ret (.bin .sub (.reg 3) (.reg 1)))
      (.ret (.bin .sub (.reg 1) (.reg 3))))
    (.ret (.bin .add (.reg 1) (.reg 3)))

/-- The capacity difference occupies one procedure slot. -/
def capacityDifferenceModule : List Stmt := [capacityDifferenceBody]

/-- Consistent signed capacities yield their nonnegative difference. -/
def capacityDifferenceContract (w : ℕ) (lower upper : ℤ) : Contract where
  pre args _ := args = [if lower < 0 then 1 else 0, lower.natAbs,
      if upper < 0 then 1 else 0, upper.natAbs] ∧ lower ≤ upper ∧
    lower.natAbs + upper.natAbs < 2 ^ w ∧ 1 < 2 ^ w
  post _ mem out mem' := mem' = mem ∧ out = (upper - lower).toNat
  cost _ _ := 30

/-- Removing a lower capacity reads no random bits. -/
theorem capacityDifferenceBody_noRand : capacityDifferenceBody.NoRand := by
  simp only [capacityDifferenceBody, Stmt.NoRand, and_self]

/-- Exact unsigned capacity subtraction, with no memory changes and at
most 30 steps for every canonical pair of consistent capacities. -/
theorem capacityDifference_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b capacityDifferenceModule) (lower upper : ℤ) :
    MeetsContract w p b (capacityDifferenceContract w lower upper) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl, horder, hsum, hone⟩ := hpre
  have hl : lower.natAbs < 2 ^ w := by omega
  have hu : upper.natAbs < 2 ^ w := by omega
  apply runs_start_le
  unfold capacityDifferenceBody
  wram_step
  · have hsign : (if lower < 0 then 1 else 0 : ℕ) = if upper < 0 then 1 else 0 := by
      simpa [startState] using hcond
    wram_step
    · have hz : (if lower < 0 then 1 else 0 : ℕ) = 0 := by
        simpa [startState] using hcond
      have hresult : upper.natAbs - lower.natAbs = (upper - lower).toNat := by
        by_cases hlower : lower < 0 <;> by_cases hupper : upper < 0 <;>
          simp only [hlower, hupper, ↓reduceIte] at hz hsign <;> omega
      refine runs_ret_le (by eval_expr) ⟨rfl, hresult⟩ ?_
      simp only [capacityDifferenceContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
    · have hz : (if lower < 0 then 1 else 0 : ℕ) ≠ 0 := by
        simpa [startState] using hcond
      have hresult : lower.natAbs - upper.natAbs = (upper - lower).toNat := by
        by_cases hlower : lower < 0 <;> by_cases hupper : upper < 0 <;>
          simp only [hlower, hupper, ↓reduceIte] at hz hsign <;> omega
      refine runs_ret_le (by eval_expr) ⟨rfl, hresult⟩ ?_
      simp only [capacityDifferenceContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hsign : (if lower < 0 then 1 else 0 : ℕ) ≠ if upper < 0 then 1 else 0 := by
      simpa [startState] using hcond
    have hresult : lower.natAbs + upper.natAbs = (upper - lower).toNat := by
      by_cases hlower : lower < 0 <;> by_cases hupper : upper < 0 <;>
        simp only [hlower, hupper, ↓reduceIte] at hsign <;> omega
    refine runs_ret_le (by eval_expr) ⟨rfl, hresult⟩ ?_
    simp only [capacityDifferenceContract, Expr.size_bin, Expr.size_reg]
    omega

/-- Every consistent capacity pair has a width at which its full machine
precondition and argument bounds hold together. -/
theorem exists_capacityDifference_pre (lower upper : ℤ) (horder : lower ≤ upper) :
    ∃ w, (∀ a ∈ [if lower < 0 then 1 else 0, lower.natAbs,
        if upper < 0 then 1 else 0, upper.natAbs], a < 2 ^ w) ∧
      (capacityDifferenceContract w lower upper).pre
        [if lower < 0 then 1 else 0, lower.natAbs,
          if upper < 0 then 1 else 0, upper.natAbs] (fun _ => 0) := by
  let w := wordSize 1 [lower.natAbs + upper.natAbs + 2]
  have hlarge : lower.natAbs + upper.natAbs + 2 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  refine ⟨w, ?_, rfl, horder, by omega, by omega⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · split <;> omega
  · omega
  · split <;> omega
  · omega

end MinCostFlow.Scaling.Machine
