module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layout
public import WordRAM.Module
public import WordRAM.Std.Limbs
import WordRAM.Std.LimbsShift
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Data.Nat.Log

/-!
# Shifted accumulator addition in `O(1)` steps

Stage 2 builds each arc flow as a sum `Σ_t d_t · 2 ^ (T - t)` with `|d_t| ≤ M < 2 ^ k` using two
lazy base-`2 ^ k` accumulators (for positive and negative parts).

`accAdd (pa, x, s, k)` adds `x · 2 ^ s` (with `x < 2 ^ k`) into the lazy limb array at `pa`
without carry propagation in `O(1)` steps: writing `s = k · q + r`, it adds `(x · 2 ^ r) % 2 ^ k`
to limb `q` and `(x · 2 ^ r) / 2 ^ k` to limb `q + 1`.

`accAdd_ofDigits` proves that `Nat.ofDigits (2 ^ k)` increases by `x * 2 ^ s`.
`accAdd_round_bound` proves that `2 * k * 2 ^ k < 2 ^ w` whenever `w ≥ k + Nat.log 2 (2 * k) + 1`,
so each limb stays a machine word across up to `2 * k` additions per round.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std

namespace MinCostFlow.NarrowProg

/-! ### Lazy limb update and value lemma -/

/-- The updated lazy limb list after adding `x * 2 ^ s` into limbs `s / k` and `s / k + 1`
in base `2 ^ k` with no carry propagation. -/
def accAddResult (k : ℕ) (ls : List ℕ) (x s : ℕ) : List ℕ :=
  let q := s / k
  let v := x * 2 ^ (s % k)
  (ls.set q (ls.getD q 0 + v % 2 ^ k)).set (q + 1) (ls.getD (q + 1) 0 + v / 2 ^ k)

@[sep_len] theorem length_accAddResult (k : ℕ) (ls : List ℕ) (x s : ℕ) :
    (accAddResult k ls x s).length = ls.length := by
  simp [accAddResult]

/-- Adding `d` to limb `i` increases `Nat.ofDigits B` by `B ^ i * d` (no limb-bound needed). -/
theorem ofDigits_set_add (B : ℕ) (ls : List ℕ) {i : ℕ} (hi : i < ls.length) (d : ℕ) :
    Nat.ofDigits B (ls.set i (ls.getD i 0 + d)) = Nat.ofDigits B ls + B ^ i * d := by
  induction ls generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.getD_cons_zero, Nat.ofDigits_cons, pow_zero, one_mul]
      ring
    | succ j =>
      simp only [List.length_cons] at hi
      simp only [List.set_cons_succ, List.getD_cons_succ, Nat.ofDigits_cons]
      rw [ih (by omega), pow_succ']
      ring

/-- **Value lemma for `accAdd`.** Adding `(x * 2 ^ (s % k)) % 2 ^ k` to limb `s / k` and
`(x * 2 ^ (s % k)) / 2 ^ k` to limb `s / k + 1` increases `Nat.ofDigits (2 ^ k) ls` by
`x * 2 ^ s`. -/
theorem accAdd_ofDigits {k : ℕ} {ls : List ℕ} {x s : ℕ}
    (hfit : s / k + 1 < ls.length) :
    Nat.ofDigits (2 ^ k) (accAddResult k ls x s) = Nat.ofDigits (2 ^ k) ls + x * 2 ^ s := by
  unfold accAddResult
  dsimp only
  set q := s / k
  set r := s % k
  set v := x * 2 ^ r
  set ls1 := ls.set q (ls.getD q 0 + v % 2 ^ k)
  have hlen1 : ls1.length = ls.length := List.length_set
  have hget1 : ls1.getD (q + 1) 0 = ls.getD (q + 1) 0 := by
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hfit]
    exact List.getElem_set_ne (by omega : q ≠ q + 1) _
  have h1 : Nat.ofDigits (2 ^ k) ls1 = Nat.ofDigits (2 ^ k) ls + (2 ^ k) ^ q * (v % 2 ^ k) :=
    ofDigits_set_add (2 ^ k) ls (by omega) (v % 2 ^ k)
  have h2 : Nat.ofDigits (2 ^ k) (ls1.set (q + 1) (ls.getD (q + 1) 0 + v / 2 ^ k)) =
      Nat.ofDigits (2 ^ k) ls1 + (2 ^ k) ^ (q + 1) * (v / 2 ^ k) := by
    rw [← hget1]
    exact ofDigits_set_add (2 ^ k) ls1 (by omega) (v / 2 ^ k)
  rw [h2, h1]
  have hmod : v % 2 ^ k + 2 ^ k * (v / 2 ^ k) = v := Nat.mod_add_div v (2 ^ k)
  have hqr : k * q + r = s := Nat.div_add_mod s k
  calc Nat.ofDigits (2 ^ k) ls + (2 ^ k) ^ q * (v % 2 ^ k) + (2 ^ k) ^ (q + 1) * (v / 2 ^ k)
      = Nat.ofDigits (2 ^ k) ls + (2 ^ k) ^ q * (v % 2 ^ k + 2 ^ k * (v / 2 ^ k)) := by
        rw [pow_succ]; ring
    _ = Nat.ofDigits (2 ^ k) ls + (2 ^ k) ^ q * (x * 2 ^ r) := by rw [hmod]
    _ = Nat.ofDigits (2 ^ k) ls + x * (2 ^ (k * q) * 2 ^ r) := by rw [← pow_mul]; ring
    _ = Nat.ofDigits (2 ^ k) ls + x * 2 ^ s := by rw [← pow_add, hqr]

/-- Both split summands added by `accAdd` are strictly below `2 ^ k`. -/
theorem accAdd_parts_lt {k x s : ℕ} (hk : 1 ≤ k) (hx : x < 2 ^ k) :
    (x * 2 ^ (s % k)) % 2 ^ k < 2 ^ k ∧ (x * 2 ^ (s % k)) / 2 ^ k < 2 ^ k := by
  have hr : s % k < k := Nat.mod_lt s (by omega)
  refine ⟨Nat.mod_lt _ (Nat.two_pow_pos k), ?_⟩
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
  have hpow : 2 ^ (s % k) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (le_of_lt hr)
  exact Nat.mul_lt_mul_of_lt_of_le hx hpow (Nat.two_pow_pos _)

/-- **Round overflow bound.** When `w ≥ k + Nat.log 2 (2 * k) + 1`, `2 * k` additions of values
below `2 ^ k` stay below `2 ^ w`. -/
theorem accAdd_round_bound {k w : ℕ} (hw : k + Nat.log 2 (2 * k) + 1 ≤ w) :
    2 * k * 2 ^ k < 2 ^ w := by
  have h1 : 2 * k < 2 ^ (Nat.log 2 (2 * k) + 1) := Nat.lt_pow_succ_log_self (by norm_num) (2 * k)
  calc 2 * k * 2 ^ k
      < 2 ^ (Nat.log 2 (2 * k) + 1) * 2 ^ k := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos k)
    _ = 2 ^ (k + Nat.log 2 (2 * k) + 1) := by rw [← pow_add]; congr 1; omega
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw

/-- With one extra bit of headroom (`w ≥ k + Nat.log 2 (2 * k) + 2`), `2 * k * 2 ^ k < 2 ^ (w - 1)`,
matching the normalization precondition of `accNormalize`. -/
theorem accAdd_round_bound_half {k w : ℕ} (hw : k + Nat.log 2 (2 * k) + 2 ≤ w) :
    2 * k * 2 ^ k < 2 ^ (w - 1) :=
  accAdd_round_bound (by omega)

/-! ### The procedure -/

/-- Add `x * 2 ^ s` (with `x < 2 ^ k`) into the lazy base-`2 ^ k` limb array at `pa`, without
carry propagation, in `O(1)` steps. -/
wram_def accAdd (pa, x, s, k) {
  B := 1 <<< k
  q := s / k
  r := s % k
  v := x <<< r
  lo := v % B
  hi := v / B
  mem[pa + q] := mem[pa + q] + lo
  mem[pa + q + 1] := mem[pa + q + 1] + hi
  return 0
}

/-- Specification of `accAdd`: updates limbs `s / k` and `s / k + 1` in place without carry
propagation, increasing `Nat.ofDigits (2 ^ k)` by `x * 2 ^ s`. -/
def accAddSpec (w : ℕ) : Spec (ℕ × List ℕ × ℕ × ℕ) where
  pre := fun (k, ls, x, s) args => ⨆ pa : ℕ,
    ⌜args = [pa, x, s, k] ∧ 1 ≤ k ∧ 2 * k ≤ w ∧ x < 2 ^ k ∧ s / k + 1 < ls.length ∧
      ls.getD (s / k) 0 + (x * 2 ^ (s % k)) % 2 ^ k < 2 ^ w ∧
      ls.getD (s / k + 1) 0 + (x * 2 ^ (s % k)) / 2 ^ k < 2 ^ w⌝ *
    Assn.list pa ls
  post := fun (k, ls, x, s) args v => ⨆ pa : ℕ,
    ⌜args = [pa, x, s, k] ∧ v = 0 ∧
      Nat.ofDigits (2 ^ k) (accAddResult k ls x s) = Nat.ofDigits (2 ^ k) ls + x * 2 ^ s⌝ *
    Assn.list pa (accAddResult k ls x s)

/-- `accAdd` updates the two affected limbs in at most `70` steps. -/
theorem accAdd_meets {w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some accAdd) :
    Meets w p f ((accAddSpec w).withCost fun _ _ => 70) := by
  sep_enter ⟨k, ls, x, s⟩ with hk hkw hx hfit hlo_w hhi_w
  have h2k := two_le_pow hk
  have h2kw := pow_lt_pow_w hk hkw
  have hB_eq : 1 <<< k = 2 ^ k := by simp [Nat.shiftLeft_eq]
  have hr : s % k ≤ k := Nat.le_of_lt (Nat.mod_lt s (by omega))
  have hv_lt : x <<< (s % k) < 2 ^ w := shl_lt hx hr hkw
  have hv_eq : x <<< (s % k) = x * 2 ^ (s % k) := Nat.shiftLeft_eq x (s % k)
  have hq_elem : ls[s / k]'(by omega) = ls.getD (s / k) 0 :=
    (List.getD_eq_getElem ls 0 (by omega)).symm
  have hq1_elem : ls[s / k + 1]'hfit = ls.getD (s / k + 1) 0 :=
    (List.getD_eq_getElem ls 0 hfit).symm
  have hval := accAdd_ofDigits (k := k) hfit (x := x)
  sep_step
  sep_step
  sep_step
  sep_step
  sep_step
  sep_step
  have hlo_val : lo = (x * 2 ^ (s % k)) % 2 ^ k := by rw [hlo, hv, hv_eq, hB_eq]
  have hhi_val : hi = (x * 2 ^ (s % k)) / 2 ^ k := by rw [hhi, hv, hv_eq, hB_eq]
  have hlo_lt : ls[s / k]'(by omega) + lo < 2 ^ w := by rw [hq_elem, hlo_val]; exact hlo_w
  sep_step
  have hset1 : (ls.set (s / k) (ls[s / k]'(by omega) + lo))[s / k + 1]'(by simp; omega) =
      ls.getD (s / k + 1) 0 := by
    rw [List.getElem_set_ne (by omega : s / k ≠ s / k + 1), hq1_elem]
  have hhi_lt : (ls.set (s / k) (ls[s / k]'(by omega) + lo))[s / k + 1]'(by simp; omega) + hi <
      2 ^ w := by rw [hset1, hhi_val]; exact hhi_w
  sep_run
  unfold accAddResult
  dsimp only
  rw [hset1, hq_elem, hlo_val, hhi_val]

/-- `accAdd` runs in `O(1)` steps. -/
theorem accAdd_meetsO {w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some accAdd) :
    MeetsO w p f (accAddSpec w) fun _ _ => 1 :=
  MeetsO.of_meets (accAdd_meets hp) ⟨70, fun _ => by dsimp only; omega⟩

/-! ### Module -/

/-- Single-procedure module for `accAdd`, polymorphic over the procedure-name type `ι`. -/
def accAddMod {ι : Type} (name : ι) : Module ι :=
  ⟨[(name, fun _ => accAdd)]⟩

theorem accAddMod_noRand {ι : Type} (name : ι) : (accAddMod name).NoRand := by
  wram_no_rand

/-- In any program placing `accAddMod name`, `accAdd` meets its `O(1)` specification. -/
theorem accAddMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ} {name : ι}
    (hp : (accAddMod name).Placed p idx) :
    MeetsO w p (idx name) (accAddSpec w) (fun _ _ => 1) :=
  accAdd_meetsO (hp.get (n := name) (b := fun _ => accAdd) (by simp [accAddMod]))

end MinCostFlow.NarrowProg
