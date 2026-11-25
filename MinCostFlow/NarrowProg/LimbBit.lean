module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layout
public import WordRAM.Module
public import WordRAM.Std.Limbs
import WordRAM.Std.LimbsBits
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Data.Nat.Bitwise

/-!
# Extracting a single bit of a long number

`limbBit (pa, n, i, k)` returns bit `i` of a long number stored at `pa` as `n` limbs of width `k`
(lowest limb first, each limb below `2 ^ k`), in `O(1)` steps.

It reads limb `q = i / k`, shifts it right by `r = i % k`, and takes the result modulo `2` when
`q < n`, returning `0` when `q ≥ n`. Its value is `(Nat.ofDigits (2 ^ k) xs / 2 ^ i) % 2`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std

namespace MinCostFlow.NarrowProg

/-! ### Bit extraction from limbs -/

/-- Bit `i` of a number in base `2 ^ k` is bit `i % k` of limb `i / k`. -/
theorem limbBit_val_of_lt {k : ℕ} (hk : 1 ≤ k) {xs : List ℕ} (hL : Limbs k xs) {i : ℕ}
    (hq : i / k < xs.length) :
    (xs[i / k] >>> (i % k)) % 2 = (Nat.ofDigits (2 ^ k) xs / 2 ^ i) % 2 := by
  have hk0 : 0 < k := by omega
  have hr : i % k < k := Nat.mod_lt i hk0
  have hlimb : xs[i / k] = Nat.ofDigits (2 ^ k) xs / 2 ^ (k * (i / k)) % 2 ^ k :=
    getElem_eq_limb hL hq
  rw [hlimb, Nat.shiftRight_eq_div_pow]
  set V := Nat.ofDigits (2 ^ k) xs
  set q := i / k
  set r := i % k
  have hi : k * q + r = i := Nat.div_add_mod i k
  have hdiv : V / 2 ^ i = V / 2 ^ (k * q) / 2 ^ r := by
    rw [← hi, pow_add, Nat.div_div_eq_div_mul]
  rw [hdiv]
  set A := V / 2 ^ (k * q)
  have htest : (A % 2 ^ k).testBit r = A.testBit r := by
    rw [Nat.testBit_mod_two_pow, decide_eq_true hr, Bool.true_and]
  have hbit1 : (A % 2 ^ k / 2 ^ r) % 2 = if (A % 2 ^ k).testBit r then 1 else 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (A % 2 ^ k / 2 ^ r) with h | h <;> simp [h]
  have hbit2 : (A / 2 ^ r) % 2 = if A.testBit r then 1 else 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (A / 2 ^ r) with h | h <;> simp [h]
  rw [hbit1, hbit2, htest]

/-- Past the last limb, every bit of the number is `0`. -/
theorem limbBit_val_of_ge {k : ℕ} {xs : List ℕ} (hL : Limbs k xs) {i : ℕ}
    (hq : xs.length ≤ i / k) :
    (Nat.ofDigits (2 ^ k) xs / 2 ^ i) % 2 = 0 := by
  have hV : Nat.ofDigits (2 ^ k) xs < 2 ^ (k * xs.length) := ofDigits_lt_pow hL
  have hle : k * xs.length ≤ i := by
    have h1 : k * xs.length ≤ k * (i / k) := Nat.mul_le_mul_left k hq
    have h2 : k * (i / k) ≤ i := Nat.mul_div_le i k
    omega
  have hlt : Nat.ofDigits (2 ^ k) xs < 2 ^ i :=
    lt_of_lt_of_le hV (Nat.pow_le_pow_right (by norm_num) hle)
  rw [Nat.div_eq_of_lt hlt, Nat.zero_mod]

/-! ### The procedure -/

/-- Return bit `i` of the `n`-limb number at `pa` in base `2 ^ k` (`0` when `i / k ≥ n`). -/
wram_def limbBit (pa, n, i, k) {
  q := i / k
  res := 0
  if q < n {
    r := i % k
    res := (mem[pa + q] >>> r) % 2
  }
  return res
}

/-- Specification of `limbBit`: returns `(Nat.ofDigits (2 ^ k) xs / 2 ^ i) % 2` without modifying
the limbs at `pa`. -/
def limbBitSpec (w : ℕ) : Spec (ℕ × List ℕ × ℕ) where
  pre := fun (k, xs, i) args => ⨆ pa : ℕ,
    ⌜args = [pa, xs.length, i, k] ∧ Limbs k xs ∧ 1 ≤ k ∧ 2 < 2 ^ w⌝ * Assn.list pa xs
  post := fun (k, xs, i) args v => ⨆ pa : ℕ,
    ⌜args = [pa, xs.length, i, k] ∧ v = (Nat.ofDigits (2 ^ k) xs / 2 ^ i) % 2⌝ *
      Assn.list pa xs

/-- `limbBit` computes bit `i` of a long number in at most `35` steps. -/
theorem limbBit_meets {w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some limbBit) :
    Meets w p f ((limbBitSpec w).withCost fun _ _ => 35) := by
  sep_enter ⟨k, xs, i⟩ with hL hk hw
  sep_run
  · rw [hres]; exact limbBit_val_of_lt hk hL hcond
  · exact (limbBit_val_of_ge hL (by omega)).symm

/-- `limbBit` runs in `O(1)` steps. -/
theorem limbBit_meetsO {w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some limbBit) :
    MeetsO w p f (limbBitSpec w) fun _ _ => 1 :=
  MeetsO.of_meets (limbBit_meets hp) ⟨35, fun _ => by dsimp only; omega⟩

/-! ### Module -/

/-- Single-procedure module for `limbBit`, polymorphic over the procedure-name type `ι`. -/
def limbBitMod {ι : Type} (name : ι) : Module ι :=
  ⟨[(name, fun _ => limbBit)]⟩

theorem limbBitMod_noRand {ι : Type} (name : ι) : (limbBitMod name).NoRand := by
  wram_no_rand

/-- In any program placing `limbBitMod name`, `limbBit` meets its `O(1)` specification. -/
theorem limbBitMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ} {name : ι}
    (hp : (limbBitMod name).Placed p idx) :
    MeetsO w p (idx name) (limbBitSpec w) (fun _ _ => 1) :=
  limbBit_meetsO (hp.get (n := name) (b := fun _ => limbBit) (by simp [limbBitMod]))

end MinCostFlow.NarrowProg
