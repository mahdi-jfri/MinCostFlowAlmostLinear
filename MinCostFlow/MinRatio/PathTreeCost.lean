module

public import Mathlib.Data.Nat.Log

/-!
# Combining the link-cut work bounds for Section 6

The proof of Theorem 5.1 (pages 29–30) charges logarithmic amortized
work per tree operation. The link-cut model accounts separately for half
the number of rotations and for iterations of the expose loop. This file
combines the two bounds with the cost of processing one payload. The
number of word operations per unit of model work is a separate premise.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

/-- A budget for a tree operation, with a quadratic allowance in the
number of limbs for each unit of link-cut work. -/
def pathTreeBudget (constant limbs n : ℕ) : ℕ :=
  25 * (constant * (limbs + 1) ^ 2) * (Nat.log 2 (2 * n + 1) + 1)

/-- The two link-cut potentials charged at the same word-operation rate. -/
def pathTreePotential (constant limbs rotationPotential splicePotential : ℕ) : ℕ :=
  constant * (limbs + 1) ^ 2 * (rotationPotential + splicePotential)

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

private theorem combine_charges {rotations splices oldRotation newRotation oldSplice newSplice
    log : ℕ}
    (hr : rotations + newRotation ≤ oldRotation + 18 * log)
    (hs : splices + newSplice ≤ oldSplice + 6 * log + 10) :
    rotations + splices + 1 + (newRotation + newSplice) ≤
      25 * (log + 1) + (oldRotation + oldSplice) := by
  omega

/-- The link-cut model's two potential bounds give a logarithmic amortized
word budget when a call costs at most the payload rate times the number of
half rotations, expose iterations, and one unit of call overhead.
The constants cover the bounds for connectedness, Link, Cut, and ordinary
path and expose operations of the shared model. Reporting needs its own
analysis to obtain these premises or a corresponding bound. -/
theorem pathTreeCost_amortized {constant limbs n cost rotations splices
    oldRotation newRotation oldSplice newSplice : ℕ}
    (hcost : cost ≤ constant * (limbs + 1) ^ 2 * (rotations + splices + 1))
    (hrotation : rotations + newRotation ≤
      oldRotation + 18 * Nat.log 2 (2 * n + 1))
    (hsplice : splices + newSplice ≤
      oldSplice + 6 * Nat.log 2 (2 * n + 1) + 10) :
    cost + pathTreePotential constant limbs newRotation newSplice ≤
      pathTreeBudget constant limbs n + pathTreePotential constant limbs oldRotation oldSplice := by
  calc
    cost + pathTreePotential constant limbs newRotation newSplice ≤
        constant * (limbs + 1) ^ 2 * (rotations + splices + 1) +
          pathTreePotential constant limbs newRotation newSplice :=
      Nat.add_le_add_right hcost _
    _ = constant * (limbs + 1) ^ 2 *
          (rotations + splices + 1 + (newRotation + newSplice)) := by
      rw [pathTreePotential, Nat.mul_add (constant * (limbs + 1) ^ 2)
        (rotations + splices + 1) (newRotation + newSplice)]
    _ ≤ constant * (limbs + 1) ^ 2 *
          (25 * (Nat.log 2 (2 * n + 1) + 1) + (oldRotation + oldSplice)) :=
      Nat.mul_le_mul_left _ (combine_charges hrotation hsplice)
    _ = pathTreeBudget constant limbs n + pathTreePotential constant limbs oldRotation oldSplice := by
      rw [Nat.mul_add, pathTreeBudget, pathTreePotential, ← Nat.mul_assoc, Nat.mul_comm
        (constant * (limbs + 1) ^ 2) 25]

end MinCostFlow.MinRatio
