module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layout
public import WordRAM.Module
public import WordRAM.Std.Limbs
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Normalizing a lazy base-`2 ^ k` accumulator in `O(n + 1)` steps

`accNormalize (pa, n, k)` runs a single in-place carry pass over `n` lazy limbs stored at `pa`,
reducing every limb below `2 ^ k` while preserving the represented value
`Nat.ofDigits (2 ^ k) xs`, and returns the final carry out, in `O(n + 1)` steps.

When every initial limb satisfies `x < 2 ^ (w - 1)` and `1 ≤ k < w`, every intermediate carry
stays strictly below `2 ^ (w - 1)`, so `limb + carry < 2 ^ w` never overflows. If the true value
is below `(2 ^ k) ^ n`, the final carry is `0` (`normCarry_eq_zero_of_lt`), and the signed flow
is then obtained from the normalized positive and negative accumulators via `limbsCmp` and
`limbsSub` (`WordRAM/Std/Limbs.lean`).
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std

namespace MinCostFlow.NarrowProg

/-! ### Carry pass specification -/

/-- One step of the normalization carry pass at limb `i` with incoming carry `c`. -/
def normStep (k : ℕ) (xs : List ℕ) (i c : ℕ) : ℕ × ℕ :=
  ((xs.getD i 0 + c) % 2 ^ k, (xs.getD i 0 + c) / 2 ^ k)

/-- The normalized limbs produced by `accNormalize`. -/
def normLimbs (k : ℕ) (xs : List ℕ) : List ℕ :=
  (carryRun (normStep k xs) xs.length).1

/-- The final carry out of `accNormalize`. -/
def normCarry (k : ℕ) (xs : List ℕ) : ℕ :=
  (carryRun (normStep k xs) xs.length).2

@[sep_len] theorem length_normLimbs (k : ℕ) (xs : List ℕ) :
    (normLimbs k xs).length = xs.length :=
  length_carryRun (normStep k xs) xs.length

/-- **Partial normalization invariant.** After `i` limbs, the normalized prefix plus the carry
equals the original prefix in base `2 ^ k`, the carry stays below `2 ^ (w - 1)`, and every
output limb is below `2 ^ k`. -/
theorem normRun_spec {k w : ℕ} (hk : 1 ≤ k) {xs : List ℕ}
    (hxs : ∀ x ∈ xs, x < 2 ^ (w - 1)) :
    ∀ i ≤ xs.length,
      Nat.ofDigits (2 ^ k) (carryRun (normStep k xs) i).1 +
          (carryRun (normStep k xs) i).2 * (2 ^ k) ^ i =
        Nat.ofDigits (2 ^ k) (xs.take i) ∧
      (carryRun (normStep k xs) i).2 < 2 ^ (w - 1) ∧
      Limbs k (carryRun (normStep k xs) i).1 := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [carryRun, Limbs]
  | succ i ih =>
    intro hi
    obtain ⟨hv, hc, hL⟩ := ih (by omega)
    have hB := two_le_pow hk
    have hlen := length_carryRun (normStep k xs) i
    have hxi : xs.getD i 0 < 2 ^ (w - 1) := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hxs _ (List.getElem_mem (by omega))
    simp only [carryRun, normStep]
    set B := 2 ^ k
    set L := (carryRun (normStep k xs) i).1
    set c := (carryRun (normStep k xs) i).2
    set s := xs.getD i 0 + c with hs_def
    have hs := Nat.mod_add_div s B
    have hcarry : s / B < 2 ^ (w - 1) := by
      have hdiv2 : s / B ≤ s / 2 := Nat.div_le_div_left hB (by norm_num)
      have hs2 : s < 2 * 2 ^ (w - 1) := by omega
      have hlt2 : s / 2 < 2 ^ (w - 1) := (Nat.div_lt_iff_lt_mul (by norm_num)).2 (by omega)
      omega
    refine ⟨?_, hcarry, hL.append (Nat.mod_lt _ (by omega))⟩
    rw [Nat.ofDigits_append, Nat.ofDigits_singleton, hlen, ofDigits_take_succ B (by omega)]
    calc Nat.ofDigits B L + B ^ i * (s % B) + s / B * B ^ (i + 1)
        = Nat.ofDigits B L + B ^ i * (s % B + B * (s / B)) := by ring
      _ = (Nat.ofDigits B L + c * B ^ i) + B ^ i * xs.getD i 0 := by rw [hs, hs_def]; ring
      _ = _ := by rw [hv]

/-- When the represented value fits in `xs.length` base-`2 ^ k` limbs, the carry out is `0` and
the normalized limbs have the exact same value. -/
theorem normCarry_eq_zero_of_lt {k w : ℕ} (hk : 1 ≤ k) {xs : List ℕ}
    (hxs : ∀ x ∈ xs, x < 2 ^ (w - 1)) (hfit : Nat.ofDigits (2 ^ k) xs < (2 ^ k) ^ xs.length) :
    normCarry k xs = 0 ∧ Nat.ofDigits (2 ^ k) (normLimbs k xs) = Nat.ofDigits (2 ^ k) xs := by
  obtain ⟨hv, -, -⟩ := normRun_spec hk hxs xs.length le_rfl
  rw [List.take_length] at hv
  change Nat.ofDigits (2 ^ k) (normLimbs k xs) + normCarry k xs * (2 ^ k) ^ xs.length =
    Nat.ofDigits (2 ^ k) xs at hv
  have hc0 : normCarry k xs = 0 := by
    by_contra hne
    have h1 : 1 * (2 ^ k) ^ xs.length ≤ normCarry k xs * (2 ^ k) ^ xs.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  rw [hc0, Nat.zero_mul, Nat.add_zero] at hv
  exact ⟨hc0, hv⟩

/-- Subtracting two normalized zero-carry accumulators with `limbsSub` yields the exact difference
when `neg ≤ pos`. -/
theorem normLimbs_sub_eq {k w : ℕ} (hk : 1 ≤ k) {pos neg : List ℕ}
    (hlen : neg.length = pos.length)
    (hpos : ∀ x ∈ pos, x < 2 ^ (w - 1)) (hneg : ∀ x ∈ neg, x < 2 ^ (w - 1))
    (hfitP : Nat.ofDigits (2 ^ k) pos < (2 ^ k) ^ pos.length)
    (hfitN : Nat.ofDigits (2 ^ k) neg < (2 ^ k) ^ neg.length)
    (hle : Nat.ofDigits (2 ^ k) neg ≤ Nat.ofDigits (2 ^ k) pos) :
    subBorrow k (normLimbs k pos) (normLimbs k neg) = 0 ∧
    ((Nat.ofDigits (2 ^ k) (subLimbs k (normLimbs k pos) (normLimbs k neg)) : ℕ) : ℤ) =
      ((Nat.ofDigits (2 ^ k) pos : ℕ) : ℤ) - ((Nat.ofDigits (2 ^ k) neg : ℕ) : ℤ) := by
  obtain ⟨_, _, hLp⟩ := normRun_spec hk hpos pos.length le_rfl
  obtain ⟨_, _, hLn⟩ := normRun_spec hk hneg neg.length le_rfl
  change Limbs k (normLimbs k pos) at hLp
  change Limbs k (normLimbs k neg) at hLn
  have hvp := (normCarry_eq_zero_of_lt hk hpos hfitP).2
  have hvn := (normCarry_eq_zero_of_lt hk hneg hfitN).2
  have hlen' : (normLimbs k neg).length = (normLimbs k pos).length := by
    simp [length_normLimbs, hlen]
  obtain ⟨hsub, _, hLsub⟩ := subRun_spec hk hLp hLn hlen' (normLimbs k pos).length le_rfl
  rw [List.take_length, List.take_of_length_le (by omega)] at hsub
  change Nat.ofDigits (2 ^ k) (subLimbs k (normLimbs k pos) (normLimbs k neg)) +
      Nat.ofDigits (2 ^ k) (normLimbs k neg) =
    Nat.ofDigits (2 ^ k) (normLimbs k pos) +
      subBorrow k (normLimbs k pos) (normLimbs k neg) * (2 ^ k) ^ (normLimbs k pos).length at hsub
  rw [hvp, hvn, length_normLimbs] at hsub
  have hsub_lt : Nat.ofDigits (2 ^ k) (subLimbs k (normLimbs k pos) (normLimbs k neg)) <
      (2 ^ k) ^ pos.length := by
    change Limbs k (subLimbs k (normLimbs k pos) (normLimbs k neg)) at hLsub
    have hlt := Nat.ofDigits_lt_base_pow_length (b := 2 ^ k) (by have := two_le_pow hk; omega) hLsub
    have hls : (subLimbs k (normLimbs k pos) (normLimbs k neg)).length = pos.length := by
      simp [subLimbs, length_carryRun, length_normLimbs]
    rwa [hls] at hlt
  have hb0 : subBorrow k (normLimbs k pos) (normLimbs k neg) = 0 := by
    by_contra hne
    have h1 : 1 * (2 ^ k) ^ pos.length ≤
        subBorrow k (normLimbs k pos) (normLimbs k neg) * (2 ^ k) ^ pos.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  rw [hb0, Nat.zero_mul, Nat.add_zero] at hsub
  exact ⟨hb0, by omega⟩

private theorem getElem_append_drop {L xs : List ℕ} {i : ℕ} (hL : L.length = i)
    (hi : i < xs.length) (h : i < (L ++ xs.drop i).length) :
    (L ++ xs.drop i)[i] = xs.getD i 0 := by
  rw [List.getD_eq_getElem _ _ hi]
  simp [List.getElem_append_right (by omega : L.length ≤ i), hL]

/-! ### The procedure -/

/-- Normalize `n` lazy base-`2 ^ k` limbs at `pa` in place with a single carry pass, returning
the final carry out, in `O(n + 1)` steps. -/
wram_def accNormalize (pa, n, k) {
  B := 1 <<< k
  c := 0
  for i in 0 .. n {
    s := mem[pa + i] + c
    mem[pa + i] := s % B
    c := s / B
  }
  return c
}

/-- Specification of `accNormalize`: reduces the `n` lazy limbs at `pa` into base-`2 ^ k` limbs
below `2 ^ k` preserving `Nat.ofDigits (2 ^ k)` up to the returned carry out. -/
def accNormalizeSpec (w : ℕ) : Spec (ℕ × List ℕ) where
  pre := fun (k, xs) args => ⨆ pa : ℕ,
    ⌜args = [pa, xs.length, k] ∧ 1 ≤ k ∧ k < w ∧ (∀ x ∈ xs, x < 2 ^ (w - 1))⌝ *
    Assn.list pa xs
  post := fun (k, xs) args v => ⨆ pa : ℕ,
    ⌜args = [pa, xs.length, k] ∧ v = normCarry k xs ∧ v < 2 ^ (w - 1) ∧
      Limbs k (normLimbs k xs) ∧
      Nat.ofDigits (2 ^ k) (normLimbs k xs) + v * (2 ^ k) ^ xs.length =
        Nat.ofDigits (2 ^ k) xs⌝ *
    Assn.list pa (normLimbs k xs)

/-- `accNormalize` normalizes `n` lazy limbs in place in at most `45 * n + 25` steps. -/
theorem accNormalize_meets {w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some accNormalize) :
    Meets w p f ((accNormalizeSpec w).withCost fun x _ => 45 * x.2.length + 25) := by
  sep_enter ⟨k, xs⟩ with hk hkw hxs
  have h2k := two_le_pow hk
  have h2kw : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) hkw
  have hw2 : 2 * 2 ^ (w - 1) = 2 ^ w := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  have hrun := normRun_spec hk hxs
  sep_step
  sep_step
  sep_for (fun i (t : ℕ) => ⟨[pa, xs.length, k, 2 ^ k, (carryRun (normStep k xs) i).2, i, t],
      i ≤ xs.length, 35 * (xs.length - i) + 5,
      [Assn.list pa ((carryRun (normStep k xs) i).1 ++ xs.drop i)]⟩) with t
  · obtain ⟨_, hc, hL⟩ := hrun i (by omega)
    have hlen := length_append_drop (zs := xs) (length_carryRun (normStep k xs) i) (by omega)
    have hget := getElem_append_drop (length_carryRun (normStep k xs) i) hhi (by omega)
    have hxi : xs.getD i 0 < 2 ^ (w - 1) := by
      rw [List.getD_eq_getElem _ _ hhi]
      exact hxs _ (List.getElem_mem hhi)
    have hsum_lt : ((carryRun (normStep k xs) i).1 ++ xs.drop i)[i]'(by omega) +
        (carryRun (normStep k xs) i).2 < 2 ^ w := by
      rw [hget]; omega
    sep_run
    · rw [hs, hget, set_append_drop (length_carryRun _ i) hhi]; rfl
    · rw [hs, hget]; rfl
  · obtain ⟨hv, hc, hL⟩ := hrun xs.length le_rfl
    rw [List.take_length] at hv
    have hrun' : (carryRun (normStep k xs) xs.length).1 ++ xs.drop xs.length = normLimbs k xs := by
      rw [List.drop_of_length_le le_rfl, List.append_nil]; rfl
    rw [hrun']
    sep_run

/-- `accNormalize` runs in `O(n + 1)` steps. -/
theorem accNormalize_meetsO {w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some accNormalize) :
    MeetsO w p f (accNormalizeSpec w) fun x _ => x.2.length + 1 :=
  MeetsO.of_meets (accNormalize_meets hp) ⟨45, fun _ => by dsimp only; omega⟩

/-! ### Module -/

/-- Single-procedure module for `accNormalize`, polymorphic over the procedure-name type `ι`. -/
def accNormalizeMod {ι : Type} (name : ι) : Module ι :=
  ⟨[(name, fun _ => accNormalize)]⟩

theorem accNormalizeMod_noRand {ι : Type} (name : ι) : (accNormalizeMod name).NoRand := by
  wram_no_rand

/-- In any program placing `accNormalizeMod name`, `accNormalize` runs in `O(n + 1)` steps. -/
theorem accNormalizeMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ} {name : ι}
    (hp : (accNormalizeMod name).Placed p idx) :
    MeetsO w p (idx name) (accNormalizeSpec w) (fun x _ => x.2.length + 1) :=
  accNormalize_meetsO
    (hp.get (n := name) (b := fun _ => accNormalize) (by simp [accNormalizeMod]))

end MinCostFlow.NarrowProg
