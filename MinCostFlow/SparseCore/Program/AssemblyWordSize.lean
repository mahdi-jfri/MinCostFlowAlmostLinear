module

public import MinCostFlow.SparseCore.Program.AssemblyContract
public import MinCostFlow.SparseCore.Program.OrdStoreContract
public import MinCostFlow.LSF.Program.Spec
import Mathlib.Tactic.Linarith

/-!
# Word size and log factors of the sparse-core program

The pieces of the sparse-core program cost one search-tree step, `ordStoreLog eCap =
⌊log₂ (eCap + 2)⌋ + 1`, per change of an order or a tour, and the LSF works on numbers of
`L_w` limbs. The model pays these through `bundleLogFactor M N = (⌊log₂ (M + N + 2)⌋ + 1) ^ 2`.
This file proves that the cap condition `SparseCoreCapHyp` makes these bounds hold with constants
free of the input.

* `ordStoreLog_le_of_cap`: if `eCap + 2 ≤ (M + N + 2) ^ c`, then `ordStoreLog eCap ≤
  c · (⌊log₂ (M + N + 2)⌋ + 1)`. The reason: `(M + N + 2) ^ c < 2 ^ (c (⌊log₂ (M + N + 2)⌋ + 1))`.
* `logStep_le_bundleLogFactor`: `⌊log₂ (M + N + 2)⌋ + 1 ≤ bundleLogFactor M N`.
* `ordStoreLog_le_capExp_mul_lg`, `limbs_le_capExp_mul_lg`: the two bounds of `SparseCoreCapHyp`
  in terms of `bundleLogFactor M N`.
* `capWord_of_wordExp`: if `2 capExp ≤ wordExp`, the word condition of the contract gives the word
  condition `(vCap + eCap + 2) ^ 2 < 2 ^ w` of the order store.
* `lsfBatchCost_le_of_limbs`: the LSF batch cost `10000 (words · L_w + 1)` is at most a constant
  times `(words + 1) · bundleLogFactor M N` when `L_w ≤ L + capExp (⌊log₂ (M + N + 2)⌋ + 1)`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.SparseCore

/-- A power is below the power of two of the exponent times the bit length of its base:
`x ^ c < 2 ^ (c (⌊log₂ x⌋ + 1))` for `c ≥ 1`. -/
theorem pow_lt_two_pow_mul_log {x c : ℕ} (hc : 1 ≤ c) :
    x ^ c < 2 ^ (c * (Nat.log 2 x + 1)) := by
  have hlt : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  rw [pow_mul']
  exact Nat.pow_lt_pow_left hlt (by omega)

/-- If `eCap + 2 ≤ (M + N + 2) ^ c`, a step of the order store costs at most
`c · (⌊log₂ (M + N + 2)⌋ + 1)`. -/
theorem ordStoreLog_le_of_cap {eCap M N c : ℕ} (h : eCap + 2 ≤ (M + N + 2) ^ c) :
    ordStoreLog eCap ≤ c * (Nat.log 2 (M + N + 2) + 1) := by
  have hc : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0
      simp at h
    · exact h0
  have hlt : eCap + 2 < 2 ^ (c * (Nat.log 2 (M + N + 2) + 1)) :=
    lt_of_le_of_lt h (pow_lt_two_pow_mul_log hc)
  have hlog : Nat.log 2 (eCap + 2) < c * (Nat.log 2 (M + N + 2) + 1) :=
    Nat.log_lt_of_lt_pow (by omega) hlt
  unfold ordStoreLog
  omega

/-- The bit length of `M + N + 2` is at most the log factor of the model. -/
theorem logStep_le_bundleLogFactor (M N : ℕ) :
    Nat.log 2 (M + N + 2) + 1 ≤ bundleLogFactor M N := by
  unfold bundleLogFactor
  have h1 : 1 ≤ Nat.log 2 (M + N + 2) + 1 := by omega
  calc Nat.log 2 (M + N + 2) + 1 = (Nat.log 2 (M + N + 2) + 1) ^ 1 := (pow_one _).symm
    _ ≤ (Nat.log 2 (M + N + 2) + 1) ^ 2 := Nat.pow_le_pow_right h1 (by norm_num)

/-- Under the cap condition, a step of the order store (or of the tours, whose log factor is the
same function of `eCap`) costs at most `capExp` times the log factor of the model. -/
theorem ordStoreLog_le_capExp_mul_lg {capExp limbMul L M N vCap eCap : ℕ}
    (h : SparseCoreCapHyp capExp limbMul L M N vCap eCap) :
    ordStoreLog eCap ≤ capExp * bundleLogFactor M N := by
  have hcap : eCap + 2 ≤ (M + N + 2) ^ capExp := le_trans (by omega) h.1
  exact le_trans (ordStoreLog_le_of_cap hcap)
    (Nat.mul_le_mul_left _ (logStep_le_bundleLogFactor M N))

/-- Under the cap condition, the limb count is at most `limbMul` times the log factor of the
model. -/
theorem limbs_le_capExp_mul_lg {capExp limbMul L M N vCap eCap : ℕ}
    (h : SparseCoreCapHyp capExp limbMul L M N vCap eCap) :
    L ≤ limbMul * bundleLogFactor M N :=
  h.2

/-- The word condition of the order store follows from the word condition of the contract when the
contract's exponent is at least twice the cap exponent: `(vCap + eCap + 2) ^ 2 ≤
(M + N + 2) ^ (2 capExp) ≤ (M + N + 2) ^ wordExp < 2 ^ w`. -/
theorem capWord_of_wordExp {capExp limbMul wordExp w L M N vCap eCap : ℕ}
    (h : SparseCoreCapHyp capExp limbMul L M N vCap eCap) (hexp : 2 * capExp ≤ wordExp)
    (hw : (M + N + 2) ^ wordExp < 2 ^ w) :
    (vCap + eCap + 2) ^ 2 < 2 ^ w := by
  have h1 : (vCap + eCap + 2) ^ 2 ≤ ((M + N + 2) ^ capExp) ^ 2 := Nat.pow_le_pow_left h.1 2
  have h2 : ((M + N + 2) ^ capExp) ^ 2 ≤ (M + N + 2) ^ wordExp := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- Under the cap condition, a working limb count
`L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (⌊log₂ (M + N + 2)⌋ + 1)` is at most
`limbMul + capExp + sparseCoreReadout2LimbConst` times the log factor of the model. -/
theorem workLimbs_le_of_cap {capExp limbMul L L_w M N vCap eCap : ℕ}
    (h : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hLw : L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)) :
    L_w ≤ (limbMul + capExp + sparseCoreReadout2LimbConst) * bundleLogFactor M N := by
  have h1 := limbs_le_capExp_mul_lg h
  have h2 : (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ≤
      (capExp + sparseCoreReadout2LimbConst) * bundleLogFactor M N :=
    Nat.mul_le_mul_left _ (logStep_le_bundleLogFactor M N)
  have h3 : (limbMul + capExp + sparseCoreReadout2LimbConst) * bundleLogFactor M N =
      limbMul * bundleLogFactor M N +
      (capExp + sparseCoreReadout2LimbConst) * bundleLogFactor M N := by ring
  omega

/-- The LSF batch cost `10000 (words · L_w + 1)` (`lsfBatchCost`) is at most
`10000 * (limbMul + capExp + sparseCoreReadout2LimbConst + 1)` times
`(words + 1) · bundleLogFactor M N` under the cap condition. -/
theorem lsfBatchCost_le_of_limbs {capExp limbMul L L_w M N vCap eCap words : ℕ}
    (h : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hLw : L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)) :
    LSF.Program.lsfBatchCostFactor * (words * L_w + 1) ≤
      10000 * (limbMul + capExp + sparseCoreReadout2LimbConst + 1) *
        ((words + 1) * bundleLogFactor M N) := by
  have hLw' := workLimbs_le_of_cap h hLw
  have hlg : 1 ≤ bundleLogFactor M N :=
    le_trans (by omega) (logStep_le_bundleLogFactor M N)
  set C := limbMul + capExp + sparseCoreReadout2LimbConst
  have h1 : words * L_w ≤ words * (C * bundleLogFactor M N) :=
    Nat.mul_le_mul_left _ hLw'
  have h2 : words * (C * bundleLogFactor M N) + 1 ≤
      (C + 1) * ((words + 1) * bundleLogFactor M N) := by
    have h1le : 1 ≤ (C + 1) * bundleLogFactor M N :=
      le_trans (by omega : 1 ≤ C + 1) (Nat.le_mul_of_pos_right _ hlg)
    have hmul : words * (C * bundleLogFactor M N) ≤ (C + 1) * (words * bundleLogFactor M N) := by
      have heq : words * (C * bundleLogFactor M N) = C * (words * bundleLogFactor M N) := by ring
      rw [heq]; exact Nat.mul_le_mul_right _ (by omega)
    have hdist : (C + 1) * ((words + 1) * bundleLogFactor M N) =
        (C + 1) * (words * bundleLogFactor M N) + (C + 1) * bundleLogFactor M N := by ring
    omega
  unfold LSF.Program.lsfBatchCostFactor
  calc 10000 * (words * L_w + 1) ≤ 10000 * (words * (C * bundleLogFactor M N) + 1) :=
        Nat.mul_le_mul_left _ (by omega)
    _ ≤ 10000 * ((C + 1) * ((words + 1) * bundleLogFactor M N)) :=
        Nat.mul_le_mul_left _ h2
    _ = 10000 * (C + 1) * ((words + 1) * bundleLogFactor M N) := by ring

/-- The cap condition can hold: with no limbs and capacities `vCap = eCap = 0`, it holds at
`capExp = 1`, `limbMul = 0` for every `M` and `N`. -/
theorem sparseCoreCapHyp_zero (M N : ℕ) : SparseCoreCapHyp 1 0 0 M N 0 0 :=
  ⟨by simp, Nat.zero_le _⟩

end MinCostFlow.SparseCore.Program
