module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layout
public import WordRAM.Module
public import WordRAM.Std.Limbs
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Reading encoded integers from the input

An integer `z : ℤ` in base `2 ^ k` is encoded as `[sign, n, limb 0, …, limb (n - 1)]`
(`intWords k z`), where `sign = if z < 0 then 1 else 0` and the limbs are `Nat.digits (2 ^ k) z.natAbs`
(lowest limb first, no leading zero limb; zero is `[0, 0]`). This matches `encodeInt` on the
narrow-word statement branch by unfolding.

`readInt (pos, out)` reads the header of the encoded integer at `pos`, writes
`[sign, n, pos + 2, pos + 2 + n]` into the 4-word output buffer `out`, and returns the next
position `pos + 2 + n`, in `O(1)` steps.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std

namespace MinCostFlow.NarrowProg

/-! ### Encoded integer words -/

/-- An integer written in base `2 ^ k`: `1` if negative and `0` otherwise, then the number of
base-`2 ^ k` limbs of `|z|`, then those limbs lowest first with no leading zero limb (`Nat.digits`).
Zero is `[0, 0]`. -/
def intWords (k : ℕ) (z : ℤ) : List ℕ :=
  (if z < 0 then 1 else 0) :: (Nat.digits (2 ^ k) z.natAbs).length :: Nat.digits (2 ^ k) z.natAbs

@[sep_len] theorem intWords_length (k : ℕ) (z : ℤ) :
    (intWords k z).length = 2 + (Nat.digits (2 ^ k) z.natAbs).length := by
  simp [intWords]; omega

/-- Splitting the owned list of an encoded integer into its sign, limb count, and limb array. -/
theorem list_intWords (pos k : ℕ) (z : ℤ) :
    Assn.list pos (intWords k z) =
      (pos ↦ (if z < 0 then 1 else 0)) *
      (pos + 1 ↦ (Nat.digits (2 ^ k) z.natAbs).length) *
      Assn.list (pos + 2) (Nat.digits (2 ^ k) z.natAbs) := by
  simp only [intWords, Assn.list_cons, mul_assoc, show pos + 1 + 1 = pos + 2 by omega]

theorem digits_limbs {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : Limbs k (Nat.digits (2 ^ k) n) := by
  intro x hx
  have hbase : 1 < 2 ^ k := by
    have := two_le_pow hk; omega
  exact Nat.digits_lt_base hbase hx

theorem digits_ofDigits_eq {k : ℕ} (n : ℕ) :
    Nat.ofDigits (2 ^ k) (Nat.digits (2 ^ k) n) = n :=
  Nat.ofDigits_digits (2 ^ k) n

theorem digits_getLast_ne_zero {k : ℕ} (n : ℕ)
    (h : Nat.digits (2 ^ k) n ≠ []) : (Nat.digits (2 ^ k) n).getLast h ≠ 0 :=
  Nat.getLast_digit_ne_zero (2 ^ k) (by
    intro h0; subst h0; simp at h)

/-- Signed reconstruction of `z` from its sign bit and `Nat.ofDigits (2 ^ k)` of its limbs. -/
theorem intWords_signed_val (k : ℕ) (z : ℤ) :
    (if (if z < 0 then (1 : ℕ) else 0) = 1 then
      -((Nat.ofDigits (2 ^ k) (Nat.digits (2 ^ k) z.natAbs) : ℕ) : ℤ)
    else
      ((Nat.ofDigits (2 ^ k) (Nat.digits (2 ^ k) z.natAbs) : ℕ) : ℤ)) = z := by
  rw [Nat.ofDigits_digits]
  by_cases h : z < 0
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte, Nat.zero_ne_one]; omega

private theorem set_four {buf : List ℕ} (hlen : buf.length = 4) (a b c d : ℕ) :
    (((buf.set 0 a).set 1 b).set 2 c).set 3 d = [a, b, c, d] := by
  rcases buf with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | xs⟩⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · rfl
  · simp at hlen

/-! ### The procedure -/

/-- Read the encoded integer at `pos`, write `[sign, n, pos + 2, pos + 2 + n]` into `out`,
and return the next position `pos + 2 + n`. -/
wram_def readInt (pos, out) {
  s := mem[pos]
  n := mem[pos + 1]
  p := pos + 2
  nxt := p + n
  mem[out] := s
  mem[out + 1] := n
  mem[out + 2] := p
  mem[out + 3] := nxt
  return nxt
}

/-- Specification of `readInt`: extracts sign, limb count, limb-0 address, and next position
for an encoded integer `intWords k z` in `O(1)` steps, relating them to `Nat.ofDigits (2 ^ k)`
and `Nat.digits`. -/
def readIntSpec (w : ℕ) : Spec (ℕ × ℤ × List ℕ) where
  pre := fun (k, z, buf) args => ⨆ (pos : ℕ) (out : ℕ),
    ⌜args = [pos, out] ∧ buf.length = 4 ∧ 1 ≤ k ∧
      pos + (intWords k z).length < 2 ^ w ∧ 3 < 2 ^ w⌝ *
    Assn.list pos (intWords k z) * Assn.list out buf
  post := fun (k, z, _) args v => ⨆ (pos : ℕ) (out : ℕ),
    let sign := if z < 0 then 1 else 0
    let ds := Nat.digits (2 ^ k) z.natAbs
    ⌜args = [pos, out] ∧ v = pos + 2 + ds.length ∧
      Limbs k ds ∧ Nat.ofDigits (2 ^ k) ds = z.natAbs ∧
      (z = 0 → sign = 0 ∧ ds = []) ∧
      (∀ h : ds ≠ [], ds.getLast h ≠ 0) ∧
      (if sign = 1 then -((Nat.ofDigits (2 ^ k) ds : ℕ) : ℤ)
        else ((Nat.ofDigits (2 ^ k) ds : ℕ) : ℤ)) = z⌝ *
    Assn.list pos (intWords k z) * Assn.list out [sign, ds.length, pos + 2, pos + 2 + ds.length]

/-- `readInt` decodes an input integer header in at most `65` steps. -/
theorem readInt_meets {w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some readInt) :
    Meets w p f ((readIntSpec w).withCost fun _ _ => 65) := by
  sep_enter ⟨k, z, buf⟩ with hbuf hk hfit hw
  have hlen : (intWords k z).length = 2 + (Nat.digits (2 ^ k) z.natAbs).length :=
    intWords_length k z
  have h0 : (intWords k z)[0]'(by omega) = if z < 0 then 1 else 0 := rfl
  have h1 : (intWords k z)[1]'(by omega) = (Nat.digits (2 ^ k) z.natAbs).length := rfl
  have hL : Limbs k (Nat.digits (2 ^ k) z.natAbs) := digits_limbs hk z.natAbs
  have hval : Nat.ofDigits (2 ^ k) (Nat.digits (2 ^ k) z.natAbs) = z.natAbs :=
    digits_ofDigits_eq z.natAbs
  have hlast : ∀ h : Nat.digits (2 ^ k) z.natAbs ≠ [],
      (Nat.digits (2 ^ k) z.natAbs).getLast h ≠ 0 :=
    digits_getLast_ne_zero z.natAbs
  have hsigned := intWords_signed_val k z
  have hzero : z = 0 → (if z < 0 then 1 else 0) = 0 ∧ Nat.digits (2 ^ k) z.natAbs = [] := by
    rintro rfl; simp
  sep_run
  rw [set_four hbuf, hnxt, hs, hn, h0, h1]

/-- `readInt` runs in `O(1)` steps. -/
theorem readInt_meetsO {w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some readInt) :
    MeetsO w p f (readIntSpec w) fun _ _ => 1 :=
  MeetsO.of_meets (readInt_meets hp) ⟨65, fun _ => by dsimp only; omega⟩

/-! ### Module -/

/-- Single-procedure module for `readInt`, polymorphic over the procedure-name type `ι`. -/
def readIntMod {ι : Type} (name : ι) : Module ι :=
  ⟨[(name, fun _ => readInt)]⟩

theorem readIntMod_noRand {ι : Type} (name : ι) : (readIntMod name).NoRand := by
  wram_no_rand

/-- In any program placing `readIntMod name`, `readInt` meets its `O(1)` specification. -/
theorem readIntMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ} {name : ι}
    (hp : (readIntMod name).Placed p idx) :
    MeetsO w p (idx name) (readIntSpec w) (fun _ _ => 1) :=
  readInt_meetsO (hp.get (n := name) (b := fun _ => readInt) (by simp [readIntMod]))

end MinCostFlow.NarrowProg
