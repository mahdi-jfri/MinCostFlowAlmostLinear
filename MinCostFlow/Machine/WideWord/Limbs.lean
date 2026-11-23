module

public import Mathlib.Data.Nat.Bitwise
public import WordRAM.Memory

/-!
# Multiword limb representation and pure arithmetic lemmas

This file defines the base-`2 ^ h` little-endian limb representation of unsigned integers for
simulating wide-word (`w'`-bit) Word-RAM programs on narrower (`w`-bit) words.

* `toLimbs x L h`: the canonical `L`-element list of `h`-bit limbs of `x` (least significant first).
* `evalLimbs h ds`: the integer value of a limb list `ds`.
* `LimbsAt mem a L h x`: `x < 2 ^ (L * h)` and `toLimbs x L h` is stored at `mem[a .. a + L - 1]`.
* `activeLimbs x L h`, `bitLen x`, `bitsMSB k`: active limb count, bit length, and MSB-first bits
  for constructing large guest constants at run time from `{0, 1}`.
* Bitwise, shift, addition, subtraction, multiplication, and binary long-division step lemmas.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-- Canonical `L`-limb base-`2 ^ h` representation of `x`, least significant limb first. -/
def toLimbs (x L h : ℕ) : List ℕ :=
  match L with
  | 0 => []
  | L + 1 => (x % 2 ^ h) :: toLimbs (x / 2 ^ h) L h

/-- Value of a list of base-`2 ^ h` limbs, least significant limb first. -/
def evalLimbs (h : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + 2 ^ h * evalLimbs h ds

/-- Host memory `mem` holds the `L`-limb base-`2 ^ h` representation of `x < 2 ^ (L * h)` at
addresses `a, …, a + L - 1`. -/
def LimbsAt (mem : ℕ → ℕ) (a L h x : ℕ) : Prop :=
  x < 2 ^ (L * h) ∧ ListAt mem a (toLimbs x L h)

/-- Number of low limbs needed to cover all nonzero limbs of `x` within `L` limbs of `h` bits. -/
def activeLimbs (x : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | L + 1, h => if (x / 2 ^ (L * h)) % 2 ^ h = 0 then activeLimbs x L h else L + 1

/-- Bit length of `x` (`0` for `x = 0`, otherwise `Nat.log 2 x + 1`). -/
def bitLen (x : ℕ) : ℕ :=
  if x = 0 then 0 else Nat.log 2 x + 1

/-- MSB-first list of binary digits of `k`, of length `bitLen k`. -/
def bitsMSB : ℕ → List ℕ
  | 0 => []
  | k + 1 => bitsMSB ((k + 1) / 2) ++ [(k + 1) % 2]
termination_by k => k

/-! ### Basic properties of `toLimbs` and `evalLimbs` -/

@[simp] theorem toLimbs_zero_len (x h : ℕ) : toLimbs x 0 h = [] := rfl

@[simp] theorem toLimbs_length (x L h : ℕ) : (toLimbs x L h).length = L := by
  induction L generalizing x with
  | zero => rfl
  | succ L ih => simp [toLimbs, ih]

theorem toLimbs_lt_two_pow {x L h d : ℕ} (hd : d ∈ toLimbs x L h) : d < 2 ^ h := by
  induction L generalizing x with
  | zero => cases hd
  | succ L ih =>
    simp only [toLimbs, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt x (Nat.two_pow_pos h)
    · exact ih hd

theorem pow_two_pow_mul (L h : ℕ) : (2 ^ h) ^ L = 2 ^ (L * h) := by
  rw [← Nat.pow_mul, Nat.mul_comm]

theorem toLimbs_getElem {x L h i : ℕ} (hi : i < L) :
    (toLimbs x L h)[i]'(by simp [hi]) = (x / 2 ^ (i * h)) % 2 ^ h := by
  induction L generalizing x i with
  | zero => omega
  | succ L ih =>
    cases i with
    | zero => simp [toLimbs]
    | succ i =>
      simp only [toLimbs, List.getElem_cons_succ]
      rw [ih (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_mul, Nat.one_mul,
        Nat.add_comm h (i * h)]

theorem toLimbs_zero (L h : ℕ) : toLimbs 0 L h = List.replicate L 0 := by
  induction L with
  | zero => rfl
  | succ L ih => simp [toLimbs, ih, List.replicate_succ]

theorem toLimbs_mod (x L h : ℕ) : toLimbs (x % 2 ^ (L * h)) L h = toLimbs x L h := by
  refine List.ext_getElem (by simp) fun i hi₁ hi₂ => ?_
  simp only [toLimbs_length] at hi₁
  rw [toLimbs_getElem hi₁, toLimbs_getElem hi₁]
  have h1_lt : i + 1 ≤ L := hi₁
  have hexp : L * h = i * h + (h + (L - (i + 1)) * h) := by
    calc L * h = ((i + 1) + (L - (i + 1))) * h := by rw [Nat.add_sub_cancel' h1_lt]
      _ = i * h + (h + (L - (i + 1)) * h) := by ring
  have hdecomp : 2 ^ (L * h) = 2 ^ (i * h) * (2 ^ h * 2 ^ ((L - (i + 1)) * h)) := by
    rw [hexp, Nat.pow_add, Nat.pow_add]
  have h1 : x % 2 ^ (L * h) / 2 ^ (i * h) = (x / 2 ^ (i * h)) % (2 ^ h * 2 ^ ((L - (i + 1)) * h)) := by
    rw [hdecomp, Nat.mul_comm (2 ^ (i * h)), Nat.mod_mul_left_div_self]
  rw [h1, Nat.mod_mul_right_mod]

theorem evalLimbs_toLimbs (x L h : ℕ) : evalLimbs h (toLimbs x L h) = x % 2 ^ (L * h) := by
  induction L generalizing x with
  | zero => simp [toLimbs, evalLimbs, Nat.mod_one]
  | succ L ih =>
    simp only [toLimbs, evalLimbs]
    rw [ih (x / 2 ^ h)]
    have hpow : 2 ^ ((L + 1) * h) = 2 ^ h * 2 ^ (L * h) := by
      rw [← Nat.pow_add, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [hpow]
    have hmod_div : x % (2 ^ h * 2 ^ (L * h)) = x % 2 ^ h + 2 ^ h * ((x / 2 ^ h) % 2 ^ (L * h)) := by
      rw [Nat.mod_mul, Nat.add_comm]
    exact hmod_div.symm

theorem evalLimbs_toLimbs_of_lt {x L h : ℕ} (hx : x < 2 ^ (L * h)) :
    evalLimbs h (toLimbs x L h) = x := by
  rw [evalLimbs_toLimbs, Nat.mod_eq_of_lt hx]

theorem evalLimbs_lt {h : ℕ} {ds : List ℕ} (hd : ∀ d ∈ ds, d < 2 ^ h) :
    evalLimbs h ds < 2 ^ (ds.length * h) := by
  induction ds with
  | nil => simp [evalLimbs]
  | cons d ds ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hd
    have h1 := ih hd.2
    simp only [evalLimbs, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm _ h, Nat.pow_add]
    have := hd.1
    calc d + 2 ^ h * evalLimbs h ds
        < 2 ^ h + 2 ^ h * evalLimbs h ds := Nat.add_lt_add_right this _
      _ = 2 ^ h * (evalLimbs h ds + 1) := by ring
      _ ≤ 2 ^ h * 2 ^ (ds.length * h) := Nat.mul_le_mul_left _ h1

theorem toLimbs_evalLimbs {h : ℕ} {ds : List ℕ} (hd : ∀ d ∈ ds, d < 2 ^ h) :
    toLimbs (evalLimbs h ds) ds.length h = ds := by
  induction ds with
  | nil => simp [evalLimbs]
  | cons d ds ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hd
    simp only [evalLimbs, List.length_cons, toLimbs]
    have hd1 : d < 2 ^ h := hd.1
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd1,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos h), Nat.div_eq_of_lt hd1, Nat.zero_add,
      ih hd.2]

theorem evalLimbs_append (h : ℕ) (xs ys : List ℕ) :
    evalLimbs h (xs ++ ys) = evalLimbs h xs + 2 ^ (xs.length * h) * evalLimbs h ys := by
  induction xs with
  | nil => simp [evalLimbs]
  | cons x xs ih =>
    simp only [List.cons_append, evalLimbs, List.length_cons, ih, Nat.add_mul, Nat.one_mul,
      Nat.add_comm (xs.length * h) h, Nat.pow_add]
    ring

theorem toLimbs_take (x L h i : ℕ) (hi : i ≤ L) :
    (toLimbs x L h).take i = toLimbs (x % 2 ^ (i * h)) i h := by
  refine List.ext_getElem (by simp [Nat.min_eq_left hi]) fun j hj₁ hj₂ => ?_
  rw [List.length_take, toLimbs_length, Nat.min_eq_left hi] at hj₁
  rw [List.getElem_take, toLimbs_getElem (lt_of_lt_of_le hj₁ hi), toLimbs_getElem hj₁]
  have h1 := toLimbs_mod x i h
  have h2 := congrArg (fun l => l[j]?) h1
  simpa [List.getElem?_eq_getElem, hj₁, toLimbs_getElem hj₁] using h2.symm

/-! ### `LimbsAt` lemmas -/

theorem LimbsAt.lt_pow {mem : ℕ → ℕ} {a L h x : ℕ} (hx : LimbsAt mem a L h x) :
    x < 2 ^ (L * h) :=
  hx.1

theorem LimbsAt.listAt {mem : ℕ → ℕ} {a L h x : ℕ} (hx : LimbsAt mem a L h x) :
    ListAt mem a (toLimbs x L h) :=
  hx.2

theorem LimbsAt.getElem {mem : ℕ → ℕ} {a L h x i : ℕ} (hx : LimbsAt mem a L h x) (hi : i < L) :
    mem (a + i) = (x / 2 ^ (i * h)) % 2 ^ h := by
  have := hx.2 i (by simpa using hi)
  simpa [toLimbs_getElem hi] using this

theorem LimbsAt.limb_lt {mem : ℕ → ℕ} {a L h x i : ℕ} (hx : LimbsAt mem a L h x) (hi : i < L) :
    mem (a + i) < 2 ^ h := by
  rw [hx.getElem hi]
  exact Nat.mod_lt _ (Nat.two_pow_pos h)

theorem LimbsAt.ext {mem : ℕ → ℕ} {a L h x y : ℕ}
    (hx : LimbsAt mem a L h x) (hy : LimbsAt mem a L h y) : x = y := by
  have hl : toLimbs x L h = toLimbs y L h := ListAt.ext hx.2 hy.2 (by simp)
  have he := congrArg (evalLimbs h) hl
  rwa [evalLimbs_toLimbs_of_lt hx.1, evalLimbs_toLimbs_of_lt hy.1] at he

theorem limbsAt_iff_pointwise {mem : ℕ → ℕ} {a L h x : ℕ} :
    LimbsAt mem a L h x ↔
      x < 2 ^ (L * h) ∧ ∀ i < L, mem (a + i) = (x / 2 ^ (i * h)) % 2 ^ h := by
  constructor
  · intro hx
    exact ⟨hx.1, fun i hi => hx.getElem hi⟩
  · rintro ⟨hx, hpt⟩
    refine ⟨hx, fun i hi => ?_⟩
    simp only [toLimbs_length] at hi
    rw [toLimbs_getElem hi]
    exact hpt i hi

theorem limbsAt_of_list {mem : ℕ → ℕ} {a L h : ℕ} {ds : List ℕ}
    (hlist : ListAt mem a ds) (hlen : ds.length = L) (hd : ∀ d ∈ ds, d < 2 ^ h) :
    LimbsAt mem a L h (evalLimbs h ds) := by
  refine ⟨by simpa [hlen] using evalLimbs_lt hd, ?_⟩
  have h1 : toLimbs (evalLimbs h ds) L h = ds := by
    rw [← hlen]
    exact toLimbs_evalLimbs hd
  rwa [h1]

theorem limbsAt_zero_iff {mem : ℕ → ℕ} {a L h : ℕ} :
    LimbsAt mem a L h 0 ↔ ListAt mem a (List.replicate L 0) := by
  simp [LimbsAt, toLimbs_zero]

theorem limbsAt_of_zeroFrom {mem : ℕ → ℕ} {hp a L h : ℕ}
    (hz : ZeroFrom mem hp) (ha : hp ≤ a) : LimbsAt mem a L h 0 :=
  limbsAt_zero_iff.mpr (hz.listAt_replicate ha)

theorem LimbsAt.congr {mem mem' : ℕ → ℕ} {a L h x : ℕ}
    (hx : LimbsAt mem a L h x) (heq : ∀ k, a ≤ k → k < a + L → mem' k = mem k) :
    LimbsAt mem' a L h x :=
  ⟨hx.1, hx.2.congr (by simpa using heq)⟩

theorem LimbsAt.update_outside {mem : ℕ → ℕ} {a L h x p v : ℕ}
    (hx : LimbsAt mem a L h x) (hp : p < a ∨ a + L ≤ p) :
    LimbsAt (Function.update mem p v) a L h x :=
  ⟨hx.1, hx.2.update_outside (by simpa using hp)⟩

theorem LimbsAt.update_lt {mem : ℕ → ℕ} {a L h x p v : ℕ}
    (hx : LimbsAt mem a L h x) (hp : p < a) :
    LimbsAt (Function.update mem p v) a L h x :=
  hx.update_outside (Or.inl hp)

theorem LimbsAt.update_ge {mem : ℕ → ℕ} {a L h x p v : ℕ}
    (hx : LimbsAt mem a L h x) (hp : a + L ≤ p) :
    LimbsAt (Function.update mem p v) a L h x :=
  hx.update_outside (Or.inr hp)

/-! ### Prefix reconstruction for `add`, `sub`, `lt`, `eq`, `mul`, `shl1AddBit` -/

theorem split_prefix {x h i : ℕ} :
    x = x % 2 ^ (i * h) + 2 ^ (i * h) * (x / 2 ^ (i * h)) := by
  exact (Nat.mod_add_div x (2 ^ (i * h))).symm

theorem limb_step_prefix (x h i : ℕ) :
    x % 2 ^ ((i + 1) * h) = x % 2 ^ (i * h) + 2 ^ (i * h) * ((x / 2 ^ (i * h)) % 2 ^ h) := by
  have hpow : 2 ^ ((i + 1) * h) = 2 ^ (i * h) * 2 ^ h := by
    rw [← Nat.pow_add, Nat.add_mul, Nat.one_mul]
  rw [hpow, Nat.mod_mul, Nat.add_comm]

theorem prefix_lt_of_limb_eq_above {x y L h i : ℕ}
    (hx : x < 2 ^ (L * h)) (hy : y < 2 ^ (L * h)) (hi : i < L)
    (heq : ∀ j, i < j → j < L → (x / 2 ^ (j * h)) % 2 ^ h = (y / 2 ^ (j * h)) % 2 ^ h)
    (hlt : (x / 2 ^ (i * h)) % 2 ^ h < (y / 2 ^ (i * h)) % 2 ^ h) :
    x < y := by
  have hdiv_eq : x / 2 ^ ((i + 1) * h) = y / 2 ^ ((i + 1) * h) := by
    have hL : x / 2 ^ ((i + 1) * h) < 2 ^ ((L - (i + 1)) * h) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
      have : (L - (i + 1)) * h + (i + 1) * h = L * h := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hi]
      rwa [this]
    have hL' : y / 2 ^ ((i + 1) * h) < 2 ^ ((L - (i + 1)) * h) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
      have : (L - (i + 1)) * h + (i + 1) * h = L * h := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hi]
      rwa [this]
    have hlist : toLimbs (x / 2 ^ ((i + 1) * h)) (L - (i + 1)) h =
        toLimbs (y / 2 ^ ((i + 1) * h)) (L - (i + 1)) h := by
      refine List.ext_getElem (by simp) fun k hk₁ hk₂ => ?_
      simp only [toLimbs_length] at hk₁
      rw [toLimbs_getElem hk₁, toLimbs_getElem hk₁]
      simp only [Nat.div_div_eq_div_mul, ← Nat.pow_add]
      have hidx : (i + 1) * h + k * h = (i + 1 + k) * h := by ring
      rw [hidx]
      exact heq (i + 1 + k) (by omega) (by omega)
    have he := congrArg (evalLimbs h) hlist
    rwa [evalLimbs_toLimbs_of_lt hL, evalLimbs_toLimbs_of_lt hL'] at he
  have hx' : x = x % 2 ^ ((i + 1) * h) + 2 ^ ((i + 1) * h) * (x / 2 ^ ((i + 1) * h)) :=
    split_prefix
  have hy' : y = y % 2 ^ ((i + 1) * h) + 2 ^ ((i + 1) * h) * (y / 2 ^ ((i + 1) * h)) :=
    split_prefix
  have hlow : x % 2 ^ ((i + 1) * h) < y % 2 ^ ((i + 1) * h) := by
    rw [limb_step_prefix, limb_step_prefix]
    have hmod_x : x % 2 ^ (i * h) < 2 ^ (i * h) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h1 : x % 2 ^ (i * h) + 2 ^ (i * h) * ((x / 2 ^ (i * h)) % 2 ^ h) <
        2 ^ (i * h) * ((x / 2 ^ (i * h)) % 2 ^ h + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have h2 : 2 ^ (i * h) * ((x / 2 ^ (i * h)) % 2 ^ h + 1) ≤
        2 ^ (i * h) * ((y / 2 ^ (i * h)) % 2 ^ h) :=
      Nat.mul_le_mul_left _ hlt
    omega
  rw [hx', hy', hdiv_eq]
  omega

theorem limbs_eq_of_pointwise {x y L h : ℕ}
    (hx : x < 2 ^ (L * h)) (hy : y < 2 ^ (L * h))
    (heq : ∀ i < L, (x / 2 ^ (i * h)) % 2 ^ h = (y / 2 ^ (i * h)) % 2 ^ h) :
    x = y := by
  have hlist : toLimbs x L h = toLimbs y L h := by
    refine List.ext_getElem (by simp) fun i hi₁ hi₂ => ?_
    simp only [toLimbs_length] at hi₁
    rw [toLimbs_getElem hi₁, toLimbs_getElem hi₁]
    exact heq i hi₁
  have he := congrArg (evalLimbs h) hlist
  rwa [evalLimbs_toLimbs_of_lt hx, evalLimbs_toLimbs_of_lt hy] at he

/-! ### Bitwise operations on limbs -/

theorem bitwise_mod_two_pow {f : Bool → Bool → Bool} (hf : f false false = false)
    (x y h : ℕ) : Nat.bitwise f x y % 2 ^ h = Nat.bitwise f (x % 2 ^ h) (y % 2 ^ h) := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  by_cases hk : k < h
  · simp [Nat.testBit_mod_two_pow, hk, Nat.testBit_bitwise hf]
  · simp only [Nat.testBit_mod_two_pow, hk, decide_false, Bool.false_and,
      Nat.testBit_bitwise hf]
    have h1 : (x % 2 ^ h).testBit k = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.mp hk)))
    have h2 : (y % 2 ^ h).testBit k = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.mp hk)))
    simp [hf]

theorem bitwise_div_two_pow {f : Bool → Bool → Bool} (hf : f false false = false)
    (x y h : ℕ) : Nat.bitwise f x y / 2 ^ h = Nat.bitwise f (x / 2 ^ h) (y / 2 ^ h) := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  simp [Nat.testBit_div_two_pow, Nat.testBit_bitwise hf, Nat.add_comm]

theorem and_limb {x y h i : ℕ} :
    ((x &&& y) / 2 ^ (i * h)) % 2 ^ h =
      ((x / 2 ^ (i * h)) % 2 ^ h) &&& ((y / 2 ^ (i * h)) % 2 ^ h) := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  by_cases hk : k < h <;> simp [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_and, hk]

theorem or_limb {x y h i : ℕ} :
    ((x ||| y) / 2 ^ (i * h)) % 2 ^ h =
      ((x / 2 ^ (i * h)) % 2 ^ h) ||| ((y / 2 ^ (i * h)) % 2 ^ h) := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  by_cases hk : k < h <;> simp [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_or, hk]

theorem xor_limb {x y h i : ℕ} :
    ((x ^^^ y) / 2 ^ (i * h)) % 2 ^ h =
      ((x / 2 ^ (i * h)) % 2 ^ h) ^^^ ((y / 2 ^ (i * h)) % 2 ^ h) := by
  refine Nat.eq_of_testBit_eq fun k => ?_
  by_cases hk : k < h <;> simp [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_xor, hk]

theorem and_lt_two_pow_left {x y M : ℕ} (hx : x < 2 ^ M) : x &&& y < 2 ^ M :=
  Nat.lt_of_le_of_lt Nat.and_le_left hx

theorem or_lt_two_pow_both {x y M : ℕ} (hx : x < 2 ^ M) (hy : y < 2 ^ M) : x ||| y < 2 ^ M :=
  Nat.or_lt_two_pow hx hy

theorem xor_lt_two_pow_both {x y M : ℕ} (hx : x < 2 ^ M) (hy : y < 2 ^ M) : x ^^^ y < 2 ^ M :=
  Nat.xor_lt_two_pow hx hy

/-! ### `activeLimbs`, `bitLen`, and `bitsMSB` -/

theorem activeLimbs_le (x L h : ℕ) : activeLimbs x L h ≤ L := by
  induction L with
  | zero => simp [activeLimbs]
  | succ L ih =>
    simp only [activeLimbs]
    split_ifs
    · exact Nat.le_trans ih (Nat.le_succ _)
    · exact le_rfl

theorem limb_eq_zero_of_activeLimbs_le {x L h i : ℕ} (hle : activeLimbs x L h ≤ i) (hi : i < L) :
    (x / 2 ^ (i * h)) % 2 ^ h = 0 := by
  induction L with
  | zero => omega
  | succ L ih =>
    simp only [activeLimbs] at hle
    split_ifs at hle with htop
    · by_cases hil : i = L
      · subst hil; exact htop
      · exact ih hle (by omega)
    · omega

theorem activeLimbs_eq_zero_iff {x L h : ℕ} (hx : x < 2 ^ (L * h)) :
    activeLimbs x L h = 0 ↔ x = 0 := by
  constructor
  · intro hact
    refine limbs_eq_of_pointwise hx (Nat.two_pow_pos _) fun i hi => ?_
    rw [limb_eq_zero_of_activeLimbs_le (by omega) hi]
    simp
  · rintro rfl
    induction L with
    | zero => simp [activeLimbs]
    | succ L ih => simp [activeLimbs, ih]

theorem lt_two_pow_activeLimbs {x L h : ℕ} (hx : x < 2 ^ (L * h)) :
    x < 2 ^ (activeLimbs x L h * h) := by
  induction L with
  | zero => simpa [activeLimbs] using hx
  | succ L ih =>
    simp only [activeLimbs]
    split_ifs with htop
    · apply ih
      have hdiv : x / 2 ^ (L * h) < 2 ^ h := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← Nat.pow_add,
          show L * h + h = (L + 1) * h by ring]
        exact hx
      rw [Nat.mod_eq_of_lt hdiv] at htop
      exact (Nat.div_eq_zero_iff.mp htop).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos _))
    · exact hx

theorem top_limb_ne_zero_of_activeLimbs_pos {x L h : ℕ} (hpos : 0 < activeLimbs x L h) :
    (x / 2 ^ ((activeLimbs x L h - 1) * h)) % 2 ^ h ≠ 0 := by
  induction L with
  | zero => simp [activeLimbs] at hpos
  | succ L ih =>
    simp only [activeLimbs] at hpos ⊢
    by_cases htop : (x / 2 ^ (L * h)) % 2 ^ h = 0
    · simp only [htop, ↓reduceIte] at hpos ⊢
      exact ih hpos
    · simp only [htop, ↓reduceIte, Nat.add_sub_cancel]
      exact htop

theorem bitLen_zero : bitLen 0 = 0 := by simp [bitLen]

theorem bitLen_pos {x : ℕ} (hx : 0 < x) : bitLen x = Nat.log 2 x + 1 := by
  simp [bitLen, Nat.ne_of_gt hx]

theorem lt_two_pow_bitLen (x : ℕ) : x < 2 ^ bitLen x := by
  by_cases hx : x = 0
  · subst hx; simp [bitLen]
  · simp only [bitLen, hx, ↓reduceIte]
    exact Nat.lt_pow_succ_log_self (by norm_num) x

theorem two_pow_bitLen_sub_one_le {x : ℕ} (hx : 0 < x) : 2 ^ (bitLen x - 1) ≤ x := by
  simp only [bitLen, Nat.ne_of_gt hx, ↓reduceIte, Nat.add_sub_cancel]
  exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hx)

theorem bitLen_le_of_lt_two_pow {x k : ℕ} (hx : x < 2 ^ k) : bitLen x ≤ k := by
  by_cases hx0 : x = 0
  · subst hx0; simp [bitLen]
  · simp only [bitLen, hx0, ↓reduceIte]
    have := Nat.log_lt_of_lt_pow hx0 hx
    omega

theorem activeLimbs_le_bitLen {x L h : ℕ} (hh : 1 ≤ h) : activeLimbs x L h ≤ bitLen x := by
  by_cases ha : activeLimbs x L h = 0
  · omega
  · have hpos : 0 < activeLimbs x L h := Nat.pos_of_ne_zero ha
    have htop := top_limb_ne_zero_of_activeLimbs_pos hpos
    have hx_ge : 2 ^ ((activeLimbs x L h - 1) * h) ≤ x := by
      by_contra hlt
      have hlt' : x < 2 ^ ((activeLimbs x L h - 1) * h) := Nat.not_le.mp hlt
      rw [Nat.div_eq_of_lt hlt', Nat.zero_mod] at htop
      exact htop rfl
    have hx_pos : 0 < x := lt_of_lt_of_le (Nat.two_pow_pos _) hx_ge
    have hpow_lt : 2 ^ ((activeLimbs x L h - 1) * h) < 2 ^ bitLen x :=
      lt_of_le_of_lt hx_ge (lt_two_pow_bitLen x)
    have hexp_lt : (activeLimbs x L h - 1) * h < bitLen x :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow_lt
    have hmul : activeLimbs x L h - 1 ≤ (activeLimbs x L h - 1) * h :=
      Nat.le_mul_of_pos_right _ hh
    omega

theorem bitLen_eq_activeLimbs_mul_add {x L h : ℕ} (hx : x < 2 ^ (L * h))
    (hpos : 0 < activeLimbs x L h) :
    bitLen x = (activeLimbs x L h - 1) * h +
      bitLen ((x / 2 ^ ((activeLimbs x L h - 1) * h)) % 2 ^ h) := by
  set la := activeLimbs x L h
  set top := (x / 2 ^ ((la - 1) * h)) % 2 ^ h
  have htop_ne : top ≠ 0 := top_limb_ne_zero_of_activeLimbs_pos hpos
  have htop_pos : 0 < top := Nat.pos_of_ne_zero htop_ne
  have hx_lt_la : x < 2 ^ (la * h) := lt_two_pow_activeLimbs hx
  have hdiv_lt : x / 2 ^ ((la - 1) * h) < 2 ^ h := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← Nat.pow_add,
      show (la - 1) * h + h = la * h by rw [← Nat.add_one_mul, Nat.sub_add_cancel hpos]]
    exact hx_lt_la
  have hdiv_eq : x / 2 ^ ((la - 1) * h) = top := (Nat.mod_eq_of_lt hdiv_lt).symm
  have hge1 : 2 ^ (bitLen top - 1) ≤ top := two_pow_bitLen_sub_one_le htop_pos
  have hlt1 : top < 2 ^ bitLen top := lt_two_pow_bitLen top
  have hx_split : x = x % 2 ^ ((la - 1) * h) + 2 ^ ((la - 1) * h) * top := by
    rw [← hdiv_eq]
    exact split_prefix
  have hx_ge : 2 ^ ((la - 1) * h + (bitLen top - 1)) ≤ x := by
    rw [Nat.pow_add]
    calc 2 ^ ((la - 1) * h) * 2 ^ (bitLen top - 1)
        ≤ 2 ^ ((la - 1) * h) * top := Nat.mul_le_mul_left _ hge1
      _ ≤ x := by omega
  have hx_lt : x < 2 ^ ((la - 1) * h + bitLen top) := by
    rw [Nat.pow_add]
    have hmod_lt : x % 2 ^ ((la - 1) * h) < 2 ^ ((la - 1) * h) := Nat.mod_lt _ (Nat.two_pow_pos _)
    calc x = x % 2 ^ ((la - 1) * h) + 2 ^ ((la - 1) * h) * top := hx_split
      _ < 2 ^ ((la - 1) * h) + 2 ^ ((la - 1) * h) * top := Nat.add_lt_add_right hmod_lt _
      _ = 2 ^ ((la - 1) * h) * (top + 1) := by ring
      _ ≤ 2 ^ ((la - 1) * h) * 2 ^ bitLen top := Nat.mul_le_mul_left _ hlt1
  have hx_pos : 0 < x := lt_of_lt_of_le (Nat.two_pow_pos _) hx_ge
  have hbt_pos : 1 ≤ bitLen top := by
    by_contra hle
    have : bitLen top = 0 := by omega
    rw [this] at hlt1
    omega
  have hle_b := bitLen_le_of_lt_two_pow hx_lt
  have hpow_lt : 2 ^ ((la - 1) * h + bitLen top - 1) < 2 ^ bitLen x := by
    have : (la - 1) * h + bitLen top - 1 = (la - 1) * h + (bitLen top - 1) := by omega
    rw [this]
    exact lt_of_le_of_lt hx_ge (lt_two_pow_bitLen x)
  have hlt_b : (la - 1) * h + bitLen top - 1 < bitLen x :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow_lt
  omega

theorem bitsMSB_length (k : ℕ) : (bitsMSB k).length = bitLen k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [bitsMSB, bitLen]
    | succ k =>
      have hdiv_lt : (k + 1) / 2 < k + 1 := Nat.div_lt_self (Nat.succ_pos _) (by norm_num)
      have hsub := ih ((k + 1) / 2) hdiv_lt
      rw [bitsMSB.eq_2]
      simp only [List.length_append, List.length_singleton, hsub]
      by_cases hd : (k + 1) / 2 = 0
      · have hk0 : k = 0 := by omega
        subst hk0
        simp [bitLen]
      · have h2 : 2 ≤ k + 1 := by omega
        have hd_pos : 0 < (k + 1) / 2 := Nat.pos_of_ne_zero hd
        have hlog : Nat.log 2 (k + 1) = Nat.log 2 ((k + 1) / 2) + 1 := by
          have hp1 : 2 ^ Nat.log 2 ((k + 1) / 2) ≤ (k + 1) / 2 :=
            Nat.pow_log_le_self 2 (Nat.ne_of_gt hd_pos)
          have hp2 : (k + 1) / 2 < 2 ^ (Nat.log 2 ((k + 1) / 2) + 1) :=
            Nat.lt_pow_succ_log_self (by norm_num) _
          have hlo : 2 ^ (Nat.log 2 ((k + 1) / 2) + 1) ≤ k + 1 := by
            rw [Nat.pow_succ']
            omega
          have hhi : k + 1 < 2 ^ (Nat.log 2 ((k + 1) / 2) + 2) := by
            rw [Nat.pow_succ']
            omega
          have ha := Nat.le_log_of_pow_le (by norm_num) hlo
          have hb := Nat.log_lt_of_lt_pow (by omega) hhi
          omega
        simp only [bitLen, Nat.succ_ne_zero, ↓reduceIte, hd, hlog]

theorem bitsMSB_mem {k b : ℕ} (hb : b ∈ bitsMSB k) : b = 0 ∨ b = 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [bitsMSB] at hb
    | succ k =>
      rw [bitsMSB.eq_2, List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact ih ((k + 1) / 2) (Nat.div_lt_self (Nat.succ_pos _) (by norm_num)) hb
      · omega

theorem foldl_bitsMSB (k : ℕ) :
    (bitsMSB k).foldl (fun acc b => 2 * acc + b) 0 = k := by
  suffices h : ∀ k init, (bitsMSB k).foldl (fun acc b => 2 * acc + b) init =
      init * 2 ^ bitLen k + k by
    simpa using h k 0
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro init
    cases k with
    | zero => simp [bitsMSB, bitLen]
    | succ k =>
      rw [bitsMSB.eq_2, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hdiv_lt : (k + 1) / 2 < k + 1 := Nat.div_lt_self (Nat.succ_pos _) (by norm_num)
      rw [ih ((k + 1) / 2) hdiv_lt init]
      have hbl : bitLen (k + 1) = bitLen ((k + 1) / 2) + 1 := by
        have := bitsMSB_length (k + 1)
        have := bitsMSB_length ((k + 1) / 2)
        rw [bitsMSB.eq_2, List.length_append, List.length_singleton] at *
        omega
      rw [hbl, Nat.pow_succ]
      have hdm : 2 * ((k + 1) / 2) + (k + 1) % 2 = k + 1 := Nat.div_add_mod (k + 1) 2
      calc 2 * (init * 2 ^ bitLen ((k + 1) / 2) + (k + 1) / 2) + (k + 1) % 2
          = init * (2 ^ bitLen ((k + 1) / 2) * 2) + (2 * ((k + 1) / 2) + (k + 1) % 2) := by ring
        _ = init * (2 ^ bitLen ((k + 1) / 2) * 2) + (k + 1) := by rw [hdm]

/-! ### Shift lemmas -/

theorem shiftLeft_split {x q r h : ℕ} :
    x <<< (q * h + r) = (x <<< r) * 2 ^ (q * h) := by
  simp only [Nat.shiftLeft_eq]
  rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm (2 ^ r) (2 ^ (q * h)), ← Nat.mul_assoc]

theorem shiftLeft_limb_formula {x L h q r i : ℕ}
    (hr : r < h) (hq : q < L) (hi : i < L) :
    (((x <<< (q * h + r)) % 2 ^ (L * h)) / 2 ^ (i * h)) % 2 ^ h =
      if i < q then 0
      else if i = q then ((x % 2 ^ h) <<< r) % 2 ^ h
      else (((x / 2 ^ ((i - q) * h)) % 2 ^ h) <<< r) % 2 ^ h +
        ((x / 2 ^ ((i - q - 1) * h)) % 2 ^ h) >>> (h - r) := by
  have hsh : x <<< (q * h + r) = (x * 2 ^ r) * 2 ^ (q * h) := by
    simpa [Nat.shiftLeft_eq] using (shiftLeft_split (x := x) (q := q) (r := r) (h := h))
  by_cases hiq : i < q
  · simp only [hiq, ↓reduceIte]
    have hdvd : 2 ^ ((i + 1) * h) ∣ 2 ^ (q * h) :=
      Nat.pow_dvd_pow 2 (Nat.mul_le_mul_right h hiq)
    have hdvd2 : 2 ^ ((i + 1) * h) ∣ 2 ^ (L * h) :=
      Nat.pow_dvd_pow 2 (Nat.mul_le_mul_right h hi)
    have hdvd_lhs : 2 ^ ((i + 1) * h) ∣ (x <<< (q * h + r)) % 2 ^ (L * h) := by
      rw [Nat.dvd_mod_iff hdvd2, hsh]
      exact dvd_mul_of_dvd_right hdvd _
    rcases hdvd_lhs with ⟨m, hm⟩
    rw [hm, show 2 ^ ((i + 1) * h) = 2 ^ (i * h) * 2 ^ h by
      rw [← Nat.pow_add, Nat.add_mul, Nat.one_mul], Nat.mul_assoc,
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos _), Nat.mul_mod_right]
  · have hqi : q ≤ i := Nat.not_lt.mp hiq
    simp only [hiq, ↓reduceIte]
    have hmod_drop : (((x <<< (q * h + r)) % 2 ^ (L * h)) / 2 ^ (i * h)) % 2 ^ h =
        ((x <<< (q * h + r)) / 2 ^ (i * h)) % 2 ^ h := by
      have hexp : L * h = i * h + (h + (L - (i + 1)) * h) := by
        calc L * h = ((i + 1) + (L - (i + 1))) * h := by rw [Nat.add_sub_cancel' hi]
          _ = i * h + (h + (L - (i + 1)) * h) := by ring
      have hdecomp : 2 ^ (L * h) = 2 ^ (i * h) * (2 ^ h * 2 ^ ((L - (i + 1)) * h)) := by
        rw [hexp, Nat.pow_add, Nat.pow_add]
      rw [hdecomp, Nat.mul_comm (2 ^ (i * h)), Nat.mod_mul_left_div_self, Nat.mod_mul_right_mod]
    rw [hmod_drop, hsh]
    have hpow_q : 2 ^ (i * h) = 2 ^ (q * h) * 2 ^ ((i - q) * h) := by
      rw [← Nat.pow_add, ← Nat.add_mul, Nat.add_sub_cancel' hqi]
    rw [hpow_q, ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    by_cases hieq : i = q
    · subst hieq
      simp only [Nat.sub_self, Nat.zero_mul, pow_zero, Nat.div_one, ↓reduceIte, Nat.shiftLeft_eq]
      rw [Nat.mod_mul_mod]
    · have hqlt : q < i := lt_of_le_of_ne hqi (Ne.symm hieq)
      simp only [hieq, ↓reduceIte]
      set k := i - q
      have hk_pos : 1 ≤ k := by omega
      have hsplit : x * 2 ^ r =
          (x % 2 ^ (k * h)) * 2 ^ r + 2 ^ (k * h) * ((x / 2 ^ (k * h)) * 2 ^ r) := by
        have hx := (Nat.mod_add_div x (2 ^ (k * h))).symm
        conv_lhs => rw [hx]
        ring
      have hk_decomp : k * h = (k - 1) * h + h := by
        rw [← Nat.add_one_mul, Nat.sub_add_cancel hk_pos]
      have hlow_split : x % 2 ^ (k * h) =
          x % 2 ^ ((k - 1) * h) + 2 ^ ((k - 1) * h) * ((x / 2 ^ ((k - 1) * h)) % 2 ^ h) := by
        have hstep := limb_step_prefix x h (k - 1)
        rwa [Nat.sub_add_cancel hk_pos] at hstep
      set lo_rem := x % 2 ^ ((k - 1) * h)
      set prev_limb := (x / 2 ^ ((k - 1) * h)) % 2 ^ h
      have hlo_rem_lt : lo_rem < 2 ^ ((k - 1) * h) := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hprev_lt : prev_limb < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hprev_split : prev_limb * 2 ^ r =
          (prev_limb % 2 ^ (h - r)) * 2 ^ r + 2 ^ h * (prev_limb / 2 ^ (h - r)) := by
        have hs := (Nat.mod_add_div prev_limb (2 ^ (h - r))).symm
        have hpow_h : 2 ^ (h - r) * 2 ^ r = 2 ^ h := by
          rw [← Nat.pow_add, Nat.sub_add_cancel (le_of_lt hr)]
        calc prev_limb * 2 ^ r
            = (prev_limb % 2 ^ (h - r) + 2 ^ (h - r) * (prev_limb / 2 ^ (h - r))) * 2 ^ r := by
                conv_lhs => rw [hs]
          _ = (prev_limb % 2 ^ (h - r)) * 2 ^ r +
                (2 ^ (h - r) * 2 ^ r) * (prev_limb / 2 ^ (h - r)) := by ring
          _ = (prev_limb % 2 ^ (h - r)) * 2 ^ r + 2 ^ h * (prev_limb / 2 ^ (h - r)) := by
                rw [hpow_h]
      have htotal : x * 2 ^ r =
          (lo_rem * 2 ^ r + 2 ^ ((k - 1) * h) * ((prev_limb % 2 ^ (h - r)) * 2 ^ r)) +
          2 ^ (k * h) * ((x / 2 ^ (k * h)) * 2 ^ r + prev_limb / 2 ^ (h - r)) := by
        have hpow_kh : 2 ^ ((k - 1) * h) * 2 ^ h = 2 ^ (k * h) := by
          rw [← Nat.pow_add, ← hk_decomp]
        calc x * 2 ^ r
            = (lo_rem + 2 ^ ((k - 1) * h) * prev_limb) * 2 ^ r +
                2 ^ (k * h) * ((x / 2 ^ (k * h)) * 2 ^ r) := by
                rw [hsplit, hlow_split]
          _ = lo_rem * 2 ^ r + 2 ^ ((k - 1) * h) * (prev_limb * 2 ^ r) +
                2 ^ (k * h) * ((x / 2 ^ (k * h)) * 2 ^ r) := by ring
          _ = lo_rem * 2 ^ r + 2 ^ ((k - 1) * h) *
                ((prev_limb % 2 ^ (h - r)) * 2 ^ r + 2 ^ h * (prev_limb / 2 ^ (h - r))) +
                2 ^ (k * h) * ((x / 2 ^ (k * h)) * 2 ^ r) := by rw [hprev_split]
          _ = lo_rem * 2 ^ r + 2 ^ ((k - 1) * h) * ((prev_limb % 2 ^ (h - r)) * 2 ^ r) +
                (2 ^ ((k - 1) * h) * 2 ^ h) * (prev_limb / 2 ^ (h - r)) +
                2 ^ (k * h) * ((x / 2 ^ (k * h)) * 2 ^ r) := by ring
          _ = _ := by rw [hpow_kh]; ring
      have hsmall : lo_rem * 2 ^ r + 2 ^ ((k - 1) * h) * ((prev_limb % 2 ^ (h - r)) * 2 ^ r) <
          2 ^ (k * h) := by
        have hm1 : prev_limb % 2 ^ (h - r) < 2 ^ (h - r) := Nat.mod_lt _ (Nat.two_pow_pos _)
        have h1 : lo_rem * 2 ^ r < 2 ^ ((k - 1) * h) * 2 ^ r :=
          Nat.mul_lt_mul_of_pos_right hlo_rem_lt (Nat.two_pow_pos _)
        have h2 : 2 ^ ((k - 1) * h) * ((prev_limb % 2 ^ (h - r)) * 2 ^ r) + 2 ^ ((k - 1) * h) * 2 ^ r ≤
            2 ^ ((k - 1) * h) * (2 ^ (h - r) * 2 ^ r) := by
          calc 2 ^ ((k - 1) * h) * ((prev_limb % 2 ^ (h - r)) * 2 ^ r) + 2 ^ ((k - 1) * h) * 2 ^ r
              = 2 ^ ((k - 1) * h) * ((prev_limb % 2 ^ (h - r) + 1) * 2 ^ r) := by ring
            _ ≤ 2 ^ ((k - 1) * h) * (2 ^ (h - r) * 2 ^ r) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hm1)
        have h3 : 2 ^ ((k - 1) * h) * (2 ^ (h - r) * 2 ^ r) = 2 ^ (k * h) := by
          rw [← Nat.pow_add, ← Nat.pow_add, Nat.sub_add_cancel (le_of_lt hr), ← hk_decomp]
        omega
      rw [htotal, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hsmall,
        Nat.zero_add]
      have hcarry_lt : prev_limb / 2 ^ (h - r) < 2 ^ r := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
          Nat.add_sub_cancel' (le_of_lt hr)]
        exact hprev_lt
      have hdiv_mod : (x / 2 ^ (k * h)) * 2 ^ r =
          ((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r + 2 ^ h * ((x / 2 ^ (k * h)) / 2 ^ h * 2 ^ r) := by
        have hx := (Nat.mod_add_div (x / 2 ^ (k * h)) (2 ^ h)).symm
        calc (x / 2 ^ (k * h)) * 2 ^ r
            = ((x / 2 ^ (k * h)) % 2 ^ h + 2 ^ h * ((x / 2 ^ (k * h)) / 2 ^ h)) * 2 ^ r := by
                conv_lhs => rw [hx]
          _ = ((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r +
                2 ^ h * ((x / 2 ^ (k * h)) / 2 ^ h * 2 ^ r) := by ring
      have hsum_mod :
          (((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r + prev_limb / 2 ^ (h - r)) % 2 ^ h =
            (((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r) % 2 ^ h + prev_limb / 2 ^ (h - r) := by
        have hm := Nat.mod_add_div (((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r) (2 ^ h)
        have hdvd : 2 ^ r ∣ 2 ^ h := Nat.pow_dvd_pow 2 (le_of_lt hr)
        have hrem_mul : 2 ^ r ∣ (((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r) % 2 ^ h := by
          rw [Nat.dvd_mod_iff hdvd]
          exact dvd_mul_left _ _
        rcases hrem_mul with ⟨c, hc⟩
        have hc_lt : 2 ^ r * c < 2 ^ h := by
          rw [← hc]
          exact Nat.mod_lt _ (Nat.two_pow_pos _)
        have h2hr : 2 ^ h = 2 ^ r * 2 ^ (h - r) := by
          rw [← Nat.pow_add, Nat.add_sub_cancel' (le_of_lt hr)]
        have hc_lt2 : c < 2 ^ (h - r) := by
          rw [h2hr] at hc_lt
          exact Nat.lt_of_mul_lt_mul_left hc_lt
        have hlt_h : (((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r) % 2 ^ h + prev_limb / 2 ^ (h - r) < 2 ^ h := by
          have hmul : 2 ^ r * (c + 1) ≤ 2 ^ r * 2 ^ (h - r) := Nat.mul_le_mul_left _ hc_lt2
          rw [← h2hr] at hmul
          have hstep : 2 ^ r * c + 2 ^ r = 2 ^ r * (c + 1) := by ring
          rw [hc]
          omega
        calc (((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r + prev_limb / 2 ^ (h - r)) % 2 ^ h
            = ((((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r) % 2 ^ h +
                2 ^ h * ((((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r) / 2 ^ h) +
                prev_limb / 2 ^ (h - r)) % 2 ^ h := by rw [hm]
          _ = ((((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r) % 2 ^ h + prev_limb / 2 ^ (h - r) +
                2 ^ h * ((((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r) / 2 ^ h)) % 2 ^ h := by ring_nf
          _ = ((((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r) % 2 ^ h + prev_limb / 2 ^ (h - r)) % 2 ^ h := by
                rw [Nat.add_mul_mod_self_left]
          _ = (((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r) % 2 ^ h + prev_limb / 2 ^ (h - r) :=
                Nat.mod_eq_of_lt hlt_h
      calc ((x / 2 ^ (k * h)) * 2 ^ r + prev_limb / 2 ^ (h - r)) % 2 ^ h
          = (((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r + prev_limb / 2 ^ (h - r) +
              2 ^ h * ((x / 2 ^ (k * h)) / 2 ^ h * 2 ^ r)) % 2 ^ h := by
              rw [hdiv_mod]; ring_nf
        _ = (((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r + prev_limb / 2 ^ (h - r)) % 2 ^ h :=
              Nat.add_mul_mod_self_left _ _ _
        _ = (((x / 2 ^ (k * h)) % 2 ^ h) * 2 ^ r) % 2 ^ h + prev_limb / 2 ^ (h - r) := hsum_mod
        _ = (((x / 2 ^ ((i - q) * h)) % 2 ^ h) <<< r) % 2 ^ h +
              ((x / 2 ^ ((i - q - 1) * h)) % 2 ^ h) >>> (h - r) := by
              simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, k, prev_limb]

theorem shiftRight_limb_formula {x L h q r i : ℕ}
    (hx : x < 2 ^ (L * h)) (hr : r < h) (_hi : i < L) :
    ((x >>> (q * h + r)) / 2 ^ (i * h)) % 2 ^ h =
      (if i + q < L then (x / 2 ^ ((i + q) * h)) % 2 ^ h else 0) >>> r +
      ((if i + q + 1 < L then (x / 2 ^ ((i + q + 1) * h)) % 2 ^ h else 0) % 2 ^ r) <<< (h - r) := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_comm (q * h + r) (i * h)]
  have hexp : i * h + (q * h + r) = (i + q) * h + r := by ring
  rw [hexp, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  set y := x / 2 ^ ((i + q) * h)
  have hy_split : y = y % 2 ^ h + 2 ^ h * (y / 2 ^ h) := (Nat.mod_add_div y (2 ^ h)).symm
  have hnext : y / 2 ^ h = (x / 2 ^ ((i + q + 1) * h)) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show (i + q) * h + h = (i + q + 1) * h by ring]
  have hy0_zero : L ≤ i + q → y = 0 := by
    intro hle
    apply Nat.div_eq_of_lt
    refine lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right h hle))
  have hy1_zero : L ≤ i + q + 1 → y / 2 ^ h = 0 := by
    intro hle
    rw [hnext]
    apply Nat.div_eq_of_lt
    refine lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right h hle))
  have hy1_limb : i + q + 1 < L → y / 2 ^ h % 2 ^ r =
      ((x / 2 ^ ((i + q + 1) * h)) % 2 ^ h) % 2 ^ r := by
    intro _
    rw [hnext, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (le_of_lt hr))]
  have hpow_h : 2 ^ h = 2 ^ r * 2 ^ (h - r) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' (le_of_lt hr)]
  have hmain : (y / 2 ^ r) % 2 ^ h =
      (y % 2 ^ h) / 2 ^ r + ((y / 2 ^ h) % 2 ^ r) * 2 ^ (h - r) := by
    have hy1_split : y / 2 ^ h = (y / 2 ^ h) % 2 ^ r + 2 ^ r * ((y / 2 ^ h) / 2 ^ r) :=
      (Nat.mod_add_div (y / 2 ^ h) (2 ^ r)).symm
    have hrem_y : y % 2 ^ h < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hdiv_r : y / 2 ^ r =
        (y % 2 ^ h) / 2 ^ r + 2 ^ (h - r) * ((y / 2 ^ h) % 2 ^ r) +
        2 ^ h * ((y / 2 ^ h) / 2 ^ r) := by
      have hdecomp : y = y % 2 ^ h + 2 ^ r * (2 ^ (h - r) * ((y / 2 ^ h) % 2 ^ r) +
          2 ^ h * ((y / 2 ^ h) / 2 ^ r)) := by
        calc y = y % 2 ^ h + 2 ^ h * (y / 2 ^ h) := hy_split
          _ = y % 2 ^ h + (2 ^ r * 2 ^ (h - r)) *
                ((y / 2 ^ h) % 2 ^ r + 2 ^ r * ((y / 2 ^ h) / 2 ^ r)) := by
                rw [← hpow_h, ← hy1_split]
          _ = y % 2 ^ h + 2 ^ r * (2 ^ (h - r) * ((y / 2 ^ h) % 2 ^ r) +
                (2 ^ r * 2 ^ (h - r)) * ((y / 2 ^ h) / 2 ^ r)) := by ring
          _ = _ := by rw [← hpow_h]
      conv_lhs => rw [hdecomp]
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos r)]
      ring
    have hlt_h : (y % 2 ^ h) / 2 ^ r + ((y / 2 ^ h) % 2 ^ r) * 2 ^ (h - r) < 2 ^ h := by
      have h1 : (y % 2 ^ h) / 2 ^ r < 2 ^ (h - r) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
          Nat.sub_add_cancel (le_of_lt hr)]
        exact hrem_y
      have h2 : (y / 2 ^ h) % 2 ^ r < 2 ^ r := Nat.mod_lt _ (Nat.two_pow_pos _)
      have hmul : ((y / 2 ^ h) % 2 ^ r + 1) * 2 ^ (h - r) ≤ 2 ^ r * 2 ^ (h - r) :=
        Nat.mul_le_mul_right _ h2
      rw [← hpow_h] at hmul
      linarith
    rw [hdiv_r, show (y % 2 ^ h) / 2 ^ r + 2 ^ (h - r) * ((y / 2 ^ h) % 2 ^ r) +
        2 ^ h * ((y / 2 ^ h) / 2 ^ r) =
        ((y % 2 ^ h) / 2 ^ r + ((y / 2 ^ h) % 2 ^ r) * 2 ^ (h - r)) +
        2 ^ h * ((y / 2 ^ h) / 2 ^ r) by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_h]
  rw [hmain]
  by_cases hiq : i + q < L
  · by_cases hiq1 : i + q + 1 < L
    · simp only [hiq, hiq1, ↓reduceIte, y, hy1_limb hiq1]
    · simp only [hiq, hiq1, ↓reduceIte, y, hy1_zero (by omega)]
  · have hiq1 : ¬ i + q + 1 < L := by omega
    simp only [hiq, hiq1, ↓reduceIte, hy0_zero (by omega)]
    simp

end MinCostFlow.WideWord
