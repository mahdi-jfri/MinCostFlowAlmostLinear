module

public import MinCostFlow.LastLevelProgram.AncestorTable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
# Aligning the depths in an LCA query

To climb a given number of edges, inspect its binary digits from low
to high. For each set digit, use the corresponding ancestor table row.
The resulting vertex is exactly the indicated iterate of the parent map.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

/-- One bit of a climb, given the vertex and the remaining bits. -/
def climbBit (parent : ℕ → ℕ) (k : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  (if s.2 % 2 = 0 then s.1 else ancestorJump parent k s.1, s.2 / 2)

/-- Process the indicated number of binary digits starting at level `k`. -/
def climbBits (parent : ℕ → ℕ) : ℕ → ℕ → (ℕ × ℕ) → ℕ × ℕ
  | 0, _, s => s
  | count + 1, k, s => climbBits parent count (k + 1) (climbBit parent k s)

/-- One binary digit contributes an exact parent iterate. -/
theorem climbBit_iterate (parent : ℕ → ℕ) (k : ℕ) (s : ℕ × ℕ) :
    (climbBit parent k s).1 = (parent^[2^k * (s.2 % 2)]) s.1 := by
  have hbit : s.2 % 2 < 2 := Nat.mod_lt _ (by decide)
  have hcases : s.2 % 2 = 0 ∨ s.2 % 2 = 1 := by omega
  rcases hcases with h | h <;> simp [climbBit, h, ancestorJump]

/-- The low bits specify exactly the number of parent steps taken. -/
theorem climbBits_iterate (parent : ℕ → ℕ) (count k : ℕ) (s : ℕ × ℕ) :
    (climbBits parent count k s).1 = (parent^[2^k * (s.2 % 2^count)]) s.1 := by
  induction count generalizing k s with
  | zero => simp [climbBits, Nat.mod_one]
  | succ count ih =>
    rw [climbBits, ih, climbBit_iterate, ← Function.iterate_add_apply]
    change (parent^[2^(k+1) * (s.2 / 2 % 2^count) + 2^k * (s.2 % 2)]) s.1 =
      (parent^[2^k * (s.2 % 2^(count+1))]) s.1
    have hmod : s.2 % 2^(count+1) = s.2 % 2 + 2 * (s.2 / 2 % 2^count) := by
      rw [pow_succ', Nat.mod_mul, Nat.add_comm]
    rw [hmod, pow_succ', Nat.mul_add]
    apply congrArg (fun j => (parent^[j]) s.1)
    ring

/-- With enough rows, climbing from row zero consumes the whole distance. -/
theorem climbBits_exact (parent : ℕ → ℕ) {count v d : ℕ} (hd : d < 2^count) :
    (climbBits parent count 0 (v,d)).1 = (parent^[d]) v := by
  rw [climbBits_iterate, Nat.mod_eq_of_lt hd, pow_zero, one_mul]

end MinCostFlow.LastLevelProgram
