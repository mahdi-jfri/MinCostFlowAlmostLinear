module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layout
public import WordRAM.Module
public import WordRAM.Std.Limbs
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Narrow.Stage1Trace
public import MinCostFlow.NarrowProg.LimbBit
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Reading one bit of a signed edge cost in `O(1)` steps (Part 2)

Given an edge cost `c : ℤ` whose sign bit (`1` iff `c < 0`) and adjusted limb array `xs`
(`Nat.ofDigits (2 ^ k) xs = if c < 0 then c.natAbs - 1 else c.natAbs`, precomputed once at
startup by `stage1PrepNegCosts`) are stored in memory, `stage1CostBit (sign, ptr, len, L, j, k)`
computes `(costBit c ((L : ℤ) - ((j + 1 : ℕ) : ℤ))).toNat` in `O(1)` steps via a single call to
`limbBit`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Narrow MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

/-- Compute `costBit c (L - (j + 1))` (`∈ {0, 1}`) from the sign bit and precomputed adjusted
limb array (`c.natAbs - 1` if `c < 0`, else `c.natAbs`), calling `limbBit` once. -/
wram_def stage1CostBit (lbIdx : ℕ) (sign, ptr, len, L, j, k) {
  res := 0
  if j < L {
    shift := L - j - 1
    b := lbIdx(ptr, len, shift, k)
    if sign == 1 {
      res := 1 - b
    } else {
      res := b
    }
  }
  return res
}

/-- Specification of `stage1CostBit`. -/
def stage1CostBitSpec (w : ℕ) : Spec (ℤ × ℕ × List ℕ × ℕ × ℕ) where
  pre := fun (c, k, xs, L, j) args => ⨆ ptr : ℕ,
    ⌜args = [if c < 0 then 1 else 0, ptr, xs.length, L, j, k] ∧
      Limbs k xs ∧
      Nat.ofDigits (2 ^ k) xs = (if c < 0 then c.natAbs - 1 else c.natAbs) ∧
      1 ≤ k ∧ 2 < 2 ^ w⌝ *
    Assn.list ptr xs
  post := fun (c, k, xs, L, j) args v => ⨆ ptr : ℕ,
    ⌜args = [if c < 0 then 1 else 0, ptr, xs.length, L, j, k] ∧
      (v : ℤ) = costBit c ((L : ℤ) - ((j + 1 : ℕ) : ℤ)) ∧ v ≤ 1⌝ *
    Assn.list ptr xs

theorem stage1CostBit_meets {w : ℕ} {p : Program} {f lbIdx : ℕ} {Tlb : ℕ}
    (hp : p.procs[f]? = some (stage1CostBit lbIdx))
    (hlb : Meets w p lbIdx ((limbBitSpec w).withCost fun _ _ => Tlb)) :
    Meets w p f ((stage1CostBitSpec w).withCost fun _ _ => Tlb + 40) := by
  sep_enter ⟨c, k, xs, L, j⟩ with hL hval hk hw
  sep_step
  sep_step
  · -- j < L
    have hshift_eq : ((L : ℤ) - ((j + 1 : ℕ) : ℤ)) = ((L - j - 1 : ℕ) : ℤ) := by omega
    sep_step; sep_step; sep_step
    sep_step from (k, xs, L - j - 1)
    sep_step
    · -- sign == 1, so c < 0
      have hneg : c < 0 := by split_ifs at hcond_1 with h; exact h
      have hbit_le : (Nat.ofDigits (2 ^ k) xs / 2 ^ (L - j - 1)) % 2 ≤ 1 := by omega
      sep_run
      rw [hb, hshift_eq, costBit_neg_eq_sub_one hneg (L - j - 1), hval]
      simp only [hneg, ↓reduceIte]
      have hle : ((c.natAbs - 1) / 2 ^ (L - j - 1)) % 2 ≤ 1 := by omega
      omega
    · -- sign ≠ 1, so 0 ≤ c
      have hnonneg : 0 ≤ c := by split_ifs at hcond_1 with h; omega; omega
      have hnot : ¬ c < 0 := by omega
      sep_run
      rw [hb, hshift_eq, costBit_nonneg_eq hnonneg (L - j - 1), hval]
      simp only [hnot, ↓reduceIte]
  · -- L ≤ j
    sep_run
    simp only [costBit, show ¬ (0 : ℤ) ≤ (L : ℤ) - ((j + 1 : ℕ) : ℤ) by omega, ↓reduceIte,
      Nat.cast_zero]

theorem stage1CostBit_meetsO {w : ℕ} {p : Program} {f lbIdx : ℕ}
    (hp : p.procs[f]? = some (stage1CostBit lbIdx))
    (hlb : MeetsO w p lbIdx (limbBitSpec w) fun _ _ => 1) :
    MeetsO w p f (stage1CostBitSpec w) fun _ _ => 1 :=
  MeetsO.of_callee hlb fun K hK =>
    ⟨_, stage1CostBit_meets hp hK, K + 40, fun _ => by dsimp only; omega⟩

/-- Single-procedure module for `stage1CostBit`, polymorphic over `ι`. -/
def stage1CostBitMod {ι : Type} (name lbName : ι) : Module ι :=
  ⟨[(name, fun idx => stage1CostBit (idx lbName))]⟩

theorem stage1CostBitMod_noRand {ι : Type} (name lbName : ι) :
    (stage1CostBitMod name lbName).NoRand := by
  wram_no_rand

theorem stage1CostBitMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ} {name lbName : ι}
    (hp : (stage1CostBitMod name lbName).Placed p idx)
    (hlb : MeetsO w p (idx lbName) (limbBitSpec w) fun _ _ => 1) :
    MeetsO w p (idx name) (stage1CostBitSpec w) fun _ _ => 1 :=
  stage1CostBit_meetsO
    (hp.get (n := name) (b := fun i => stage1CostBit (i lbName)) (by simp [stage1CostBitMod])) hlb

end MinCostFlow.NarrowProg.Stage1
