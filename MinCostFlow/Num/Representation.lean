module

public import WordRAM.Layout
public import Mathlib.Basic.Real.Basic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Fixed-point numbers stored in limbs

The computational model on page 7 of arXiv:2309.16629v1 uses fixed-point numbers with
polylogarithmically many bits. Here a number occupies exactly `L` consecutive cells, each
holding a base-`2^h` digit, least significant first. We use two's complement: it needs no
extra sign cell, has one encoding of zero, and supports addition modulo the capacity.
The empty block represents zero. Nonempty blocks have the usual signed range.

`intVal` reads the signed integer. `fixVal` divides it by `2^P`. Callers use a precision
`P` divisible by `h`. `Format` records this condition and the word-size slack for limb
products and carries. Memory validity is stated separately by `Valid`, so values can be
read without carrying proofs as arguments.
-/

@[expose] public section

namespace MinCostFlow.Num

/-- The limb width and fixed-point precision, with room for products and carries.
These are representation choices for the computational model on page 7. -/
structure Format (w : ℕ) where
  limbBits : ℕ
  precision : ℕ
  limbBits_pos : 0 < limbBits
  product_fits : 2 * limbBits + 2 ≤ w
  precision_aligned : limbBits ∣ precision

/-- The base of a limb. -/
def base (h : ℕ) : ℕ := 2 ^ h

/-- The number of unsigned values of an `L`-limb block. -/
def capacity (h L : ℕ) : ℕ := base h ^ L

/-- Each of the `L` cells contains one limb. -/
def Valid (mem : ℕ → ℕ) (a h L : ℕ) : Prop :=
  ∀ i < L, mem (a + i) < base h

/-- Read the unsigned value, starting with the low limb. -/
def unsignedVal (mem : ℕ → ℕ) (a h : ℕ) : ℕ → ℕ
  | 0 => 0
  | L + 1 => mem a + base h * unsignedVal mem (a + 1) h L

/-- Interpret the upper half of an unsigned range as negative, in two's complement.
The test also handles the empty block, whose capacity is one. -/
def signedVal (h L u : ℕ) : ℤ :=
  (u : ℤ) - if capacity h L ≤ 2 * u then (capacity h L : ℤ) else 0

/-- The signed integer in the block beginning at `a`. -/
def intVal (mem : ℕ → ℕ) (a h L : ℕ) : ℤ :=
  signedVal h L (unsignedVal mem a h L)

/-- The real value at precision `P`, as in the computational model on page 7. -/
noncomputable def fixVal (mem : ℕ → ℕ) (a h L P : ℕ) : ℝ :=
  (intVal mem a h L : ℝ) / (2 : ℝ) ^ P

@[simp] theorem base_pos (h : ℕ) : 0 < base h := by
  exact pow_pos (by decide) h

@[simp] theorem capacity_pos (h L : ℕ) : 0 < capacity h L := by
  exact pow_pos (base_pos h) L

@[simp] theorem capacity_zero (h : ℕ) : capacity h 0 = 1 := by rfl

 theorem capacity_succ (h L : ℕ) : capacity h (L + 1) = base h * capacity h L := by
  exact pow_succ' _ _

/-- Validity splits into the low limb and the rest of the block. -/
theorem valid_succ {mem : ℕ → ℕ} {a h L : ℕ} :
    Valid mem a h (L + 1) ↔ mem a < base h ∧ Valid mem (a + 1) h L := by
  constructor
  · intro hv
    refine ⟨by simpa using hv 0 (by omega), ?_⟩
    intro i hi
    simpa [Nat.add_assoc, Nat.add_comm 1] using hv (i + 1) (by omega)
  · rintro ⟨hhead, htail⟩ i hi
    cases i with
    | zero => simpa using hhead
    | succ i => simpa [Nat.add_assoc, Nat.add_comm 1] using htail i (by omega)

/-- An unsigned block is strictly below its capacity. -/
theorem unsignedVal_lt {mem : ℕ → ℕ} {a h L : ℕ} (hv : Valid mem a h L) :
    unsignedVal mem a h L < capacity h L := by
  induction L generalizing a with
  | zero => simp [unsignedVal, capacity]
  | succ L ih =>
    obtain ⟨hh, ht⟩ := valid_succ.mp hv
    have hb := base_pos h
    have hr := ih ht
    rw [unsignedVal, capacity_succ]
    nlinarith

/-- Two memories that agree on the block have the same unsigned value. -/
theorem unsignedVal_congr {mem mem' : ℕ → ℕ} {a a' h L : ℕ}
    (heq : ∀ i < L, mem (a + i) = mem' (a' + i)) :
    unsignedVal mem a h L = unsignedVal mem' a' h L := by
  induction L generalizing a a' with
  | zero => rfl
  | succ L ih =>
    have hh : mem a = mem' a' := by simpa using heq 0 (by omega)
    rw [unsignedVal, unsignedVal, hh, ih]
    intro i hi
    simpa [Nat.add_assoc, Nat.add_comm 1] using heq (i + 1) (by omega)

/-- Reading depends only on the cells of the block, even when its address changes. -/
theorem intVal_congr {mem mem' : ℕ → ℕ} {a a' h L : ℕ}
    (heq : ∀ i < L, mem (a + i) = mem' (a' + i)) :
    intVal mem a h L = intVal mem' a' h L := by
  simp only [intVal, unsignedVal_congr heq]

/-- A block of fresh zero cells has unsigned value zero. -/
theorem unsignedVal_zero {mem : ℕ → ℕ} {a h L : ℕ}
    (hz : ∀ i < L, mem (a + i) = 0) : unsignedVal mem a h L = 0 := by
  induction L generalizing a with
  | zero => rfl
  | succ L ih =>
    have hh : mem a = 0 := by simpa using hz 0 (by omega)
    simp only [unsignedVal, hh, zero_add]
    rw [ih, mul_zero]
    intro i hi
    simpa [Nat.add_assoc, Nat.add_comm 1] using hz (i + 1) (by omega)

@[simp] theorem signedVal_zero (h L : ℕ) : signedVal h L 0 = 0 := by
  simp [signedVal, Nat.not_le_of_gt (capacity_pos h L)]

/-- Fresh zero memory represents the integer zero. -/
theorem intVal_zero {mem : ℕ → ℕ} {a h L : ℕ}
    (hz : ∀ i < L, mem (a + i) = 0) : intVal mem a h L = 0 := by
  rw [intVal, unsignedVal_zero hz, signedVal_zero]

/-- A block at or above the heap pointer is a valid encoding of zero. -/
theorem zeroFrom_valid {mem : ℕ → ℕ} {heap a h L : ℕ}
    (hz : WordRAM.ZeroFrom mem heap) (ha : heap ≤ a) : Valid mem a h L := by
  intro i _
  rw [hz (a + i) (by omega)]
  exact base_pos h

 theorem intVal_zeroFrom {mem : ℕ → ℕ} {heap a h L : ℕ}
    (hz : WordRAM.ZeroFrom mem heap) (ha : heap ≤ a) : intVal mem a h L = 0 := by
  exact intVal_zero fun i _ => hz (a + i) (by omega)

 theorem fixVal_zeroFrom {mem : ℕ → ℕ} {heap a h L P : ℕ}
    (hz : WordRAM.ZeroFrom mem heap) (ha : heap ≤ a) : fixVal mem a h L P = 0 := by
  simp [fixVal, intVal_zeroFrom hz ha]

/-- Signed decoding stays between minus the capacity and the capacity. -/
theorem intVal_bounds {mem : ℕ → ℕ} {a h L : ℕ} (hv : Valid mem a h L) :
    -(capacity h L : ℤ) ≤ intVal mem a h L ∧
      intVal mem a h L < (capacity h L : ℤ) := by
  have hu := unsignedVal_lt hv
  have hc := capacity_pos h L
  dsimp only [intVal, signedVal]
  split_ifs <;> omega

/-- Storing a list of limbs determines its unsigned value. -/
def listVal (h : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + base h * listVal h xs

 theorem unsignedVal_listAt {mem : ℕ → ℕ} {a h : ℕ} {xs : List ℕ}
    (hx : WordRAM.ListAt mem a xs) : unsignedVal mem a h xs.length = listVal h xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hh, ht⟩ := WordRAM.listAt_cons.mp hx
    simp only [List.length_cons, unsignedVal, listVal, hh, ih ht]

 theorem valid_listAt {mem : ℕ → ℕ} {a h : ℕ} {xs : List ℕ}
    (hx : WordRAM.ListAt mem a xs) (hb : ∀ x ∈ xs, x < base h) :
    Valid mem a h xs.length := by
  intro i hi
  rw [hx i hi]
  exact hb _ (List.getElem_mem hi)

 theorem intVal_listAt {mem : ℕ → ℕ} {a h : ℕ} {xs : List ℕ}
    (hx : WordRAM.ListAt mem a xs) :
    intVal mem a h xs.length = signedVal h xs.length (listVal h xs) := by
  rw [intVal, unsignedVal_listAt hx]

/-- A valid block is signed zero exactly when its unsigned value is zero. -/
theorem intVal_eq_zero_iff {mem : ℕ → ℕ} {a h L : ℕ} (hv : Valid mem a h L) :
    intVal mem a h L = 0 ↔ unsignedVal mem a h L = 0 := by
  have hu := unsignedVal_lt hv
  have hp := capacity_pos h L
  dsimp only [intVal, signedVal]
  split_ifs <;> omega

/-- An unsigned value is zero exactly when every stored limb is zero. -/
theorem unsignedVal_eq_zero_iff {mem : ℕ → ℕ} {a h L : ℕ} :
    unsignedVal mem a h L = 0 ↔ ∀ i < L, mem (a + i) = 0 := by
  constructor
  · intro hz
    induction L generalizing a with
    | zero => intro i hi; omega
    | succ L ih =>
      have hb := base_pos h
      have hhead : mem a = 0 := by unfold unsignedVal at hz; omega
      have htail : unsignedVal mem (a + 1) h L = 0 := by
        simp only [unsignedVal, hhead, zero_add, mul_eq_zero] at hz
        exact hz.resolve_left (ne_of_gt hb)
      intro i hi
      cases i with
      | zero => simpa using hhead
      | succ i => simpa [Nat.add_assoc, Nat.add_comm 1] using ih htail i (by omega)
  · exact unsignedVal_zero

end MinCostFlow.Num
