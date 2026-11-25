module

public import WordRAM.Entry
public import MinCostFlow.NarrowProg.Stage0Defs
public import MinCostFlow.Final.Scratch
import MinCostFlow.Narrow.CostUnitsClip
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.Ring

/-!
# Word-size bounds for the narrow-word top theorem

For any valid instance `I` and any solver workspace bound `S n m ≤ a * (n + m + 2) ^ e`, proves
that `NarrowMainFits (wordSize c (narrowEncode I)) S I hv` and that the length and every word of
`narrowEncode I` fit below `2 ^ wordSize c (narrowEncode I)` for all `c ≥ narrowWordMultiplierPoly a e`.

In particular, for `a = 8` and `e = 42 * scratchWordMultiplier 1 d`, this yields the concrete
multiplier `narrowWordMultiplier d = 168 * scratchWordMultiplier 1 d + 17`.

The core elementary estimate is `narrowBitLength_le_base_sq`:
`narrowBitLength I ≤ ((narrowEncode I).length + (narrowEncode I).foldr max 0 + 2) ^ 2`,
which holds uniformly for every valid instance (including `n = 0`, `m = 0`, `U = 0`, `C = 0`).
-/

@[expose] public section

open WordRAM WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow MinCostFlow.NarrowProg
  MinCostFlow.Final

namespace MinCostFlow.NarrowTop

/-- Word-size multiplier for any solver workspace bounded by `a * (n + m + 2) ^ e`. -/
def narrowWordMultiplierPoly (a e : ℕ) : ℕ :=
  max 24 (4 * e + Nat.clog 8 a + 9)

/-- Concrete word-size multiplier for solver space bounded by
`8 * (n + m + 2) ^ (42 * scratchWordMultiplier 1 d)`. -/
def narrowWordMultiplier (d : ℕ) : ℕ :=
  168 * scratchWordMultiplier 1 d + 17

theorem narrowWordMultiplierPoly_le_narrowWordMultiplier (d : ℕ) :
    narrowWordMultiplierPoly 8 (42 * scratchWordMultiplier 1 d) ≤ narrowWordMultiplier d := by
  have hclog : Nat.clog 8 8 = 1 := by decide
  have hm : 3 ≤ scratchWordMultiplier 1 d := by
    unfold scratchWordMultiplier
    omega
  unfold narrowWordMultiplierPoly narrowWordMultiplier
  rw [hclog]
  omega

/-! ### Bit-length vs. encoded-word base -/

private lemma narrowIntBits_le_mul_intWords_length {k : ℕ} (hk : 1 ≤ k) (x : ℤ) :
    narrowIntBits x ≤ (k + 1) * (intWords k x).length := by
  rw [intWords_length]
  unfold narrowIntBits
  by_cases hx : x.natAbs = 0
  · rw [hx]; simp
  · have hb : 1 < 2 ^ k := by
      have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
      omega
    have hlt : x.natAbs < (2 ^ k) ^ (Nat.digits (2 ^ k) x.natAbs).length :=
      Nat.lt_base_pow_length_digits hb
    rw [← Nat.pow_mul] at hlt
    have hlog : Nat.log 2 x.natAbs < k * (Nat.digits (2 ^ k) x.natAbs).length :=
      (Nat.log_lt_iff_lt_pow (by decide) hx).mpr hlt
    have hmul : k * (Nat.digits (2 ^ k) x.natAbs).length + 2 ≤
        (k + 1) * (2 + (Nat.digits (2 ^ k) x.natAbs).length) := by
      have : (k + 1) * (2 + (Nat.digits (2 ^ k) x.natAbs).length) =
          k * (Nat.digits (2 ^ k) x.natAbs).length +
            (Nat.digits (2 ^ k) x.natAbs).length + 2 * k + 2 := by ring
      omega
    omega

private lemma narrowIntBits_nat_le_of_lt_pow {k n : ℕ} (hk : 1 ≤ k) (hn : n < 2 ^ k) :
    narrowIntBits n ≤ k + 1 := by
  unfold narrowIntBits
  simp only [Int.natAbs_natCast]
  by_cases h0 : n = 0
  · subst h0; simp; omega
  · have hlog : Nat.log 2 n < k := (Nat.log_lt_iff_lt_pow (by decide) h0).mpr hn
    omega

private lemma sum_map_le_mul_length_flatMap {α : Type} (c : ℕ) (l : List α)
    (f : α → ℕ) (g : α → List ℕ) (h : ∀ x ∈ l, f x ≤ c * (g x).length) :
    (l.map f).sum ≤ c * (l.flatMap g).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
    have ha := h a List.mem_cons_self
    have hl := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    rw [Nat.mul_add]
    omega

private lemma narrowBitLength_le_mul_encode_length (I : Instance) (hv : I.IsValid) :
    narrowBitLength I ≤ (narrowLimbWidth I + 1) * (narrowEncode I).length := by
  set k := narrowLimbWidth I
  have hk : 1 ≤ k := one_le_narrowLimbWidth I
  have hge : 10 * I.m + 2 * I.n + 4 ≤ narrowBitLength I := narrowBitLength_ge I hv
  have hpow : narrowBitLength I < 2 ^ k := narrowBitLength_lt_pow_limbWidth I
  have hn_bits : narrowIntBits I.n ≤ k + 1 := narrowIntBits_nat_le_of_lt_pow hk (by omega)
  have hm_bits : narrowIntBits I.m ≤ k + 1 := narrowIntBits_nat_le_of_lt_pow hk (by omega)
  have hedges : (I.edges.map narrowEdgeBits).sum ≤
      (k + 1) * (I.edges.flatMap (narrowEdgeWords k)).length := by
    apply sum_map_le_mul_length_flatMap
    intro e he
    have hvalid := hv.1 e he
    have ht : narrowIntBits e.tail ≤ k + 1 := narrowIntBits_nat_le_of_lt_pow hk (by omega)
    have hh : narrowIntBits e.head ≤ k + 1 := narrowIntBits_nat_le_of_lt_pow hk (by omega)
    have hlo := narrowIntBits_le_mul_intWords_length hk e.lower
    have hhi := narrowIntBits_le_mul_intWords_length hk e.upper
    have hco := narrowIntBits_le_mul_intWords_length hk e.cost
    unfold narrowEdgeBits narrowEdgeWords
    simp only [List.length_cons, List.length_append, Nat.mul_add]
    omega
  have hdem : (I.demand.map narrowIntBits).sum ≤
      (k + 1) * (I.demand.flatMap (intWords k)).length :=
    sum_map_le_mul_length_flatMap (k + 1) I.demand narrowIntBits (intWords k)
      (fun x _ => narrowIntBits_le_mul_intWords_length hk x)
  unfold narrowBitLength narrowEncode
  simp only [List.length_cons, List.length_append]
  change narrowIntBits I.n + narrowIntBits I.m + (I.edges.map narrowEdgeBits).sum +
      (I.demand.map narrowIntBits).sum ≤
    (k + 1) * (((I.edges.flatMap (narrowEdgeWords k)).length +
      (I.demand.flatMap (intWords k)).length) + 1 + 1 + 1)
  have heq : (k + 1) * (((I.edges.flatMap (narrowEdgeWords k)).length +
      (I.demand.flatMap (intWords k)).length) + 1 + 1 + 1) =
    (k + 1) * (I.edges.flatMap (narrowEdgeWords k)).length +
      (k + 1) * (I.demand.flatMap (intWords k)).length + 3 * (k + 1) := by ring
  omega

/-- Every valid instance has total bit length at most the square of the `wordSize` base
`B = (narrowEncode I).length + (narrowEncode I).foldr max 0 + 2`. -/
theorem narrowBitLength_le_base_sq (I : Instance) (hv : I.IsValid) :
    narrowBitLength I ≤
      ((narrowEncode I).length + (narrowEncode I).foldr max 0 + 2) ^ 2 := by
  set B := (narrowEncode I).length + (narrowEncode I).foldr max 0 + 2
  have hk_le : narrowLimbWidth I ≤ (narrowEncode I).foldr max 0 := by
    simp only [narrowEncode, List.foldr_cons]
    exact le_max_left _ _
  have h1 : narrowLimbWidth I + 1 ≤ B := by omega
  have h2 : (narrowEncode I).length ≤ B := by omega
  calc narrowBitLength I
      ≤ (narrowLimbWidth I + 1) * (narrowEncode I).length :=
        narrowBitLength_le_mul_encode_length I hv
    _ ≤ B * B := Nat.mul_le_mul h1 h2
    _ = B ^ 2 := (sq B).symm

/-! ### Bounds on `maxCapacity`, `maxCost`, and `narrowMainSpace` in terms of `z` -/

private lemma foldr_max_le_of_all {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x ≤ M) :
    l.foldr max 0 ≤ M := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem a hx))

private lemma le_sum_map_of_mem {α : Type} {l : List α} {f : α → ℕ} {a : α} (ha : a ∈ l) :
    f a ≤ (l.map f).sum := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ha with rfl | hmem
    · omega
    · have := ih hmem; omega

private lemma natAbs_lt_pow_pred_of_intBits_le {x : ℤ} {z : ℕ} (h : narrowIntBits x ≤ z) :
    x.natAbs < 2 ^ (z - 1) := by
  unfold narrowIntBits at h
  exact lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by decide) x.natAbs)
    (Nat.pow_le_pow_right (by decide) (by omega))

private lemma log_maxCapacity_add_two_le_bitLength (I : Instance) :
    Nat.log 2 I.maxCapacity + 2 ≤ narrowBitLength I := by
  have h4 := four_le_narrowBitLength I
  by_cases hU : I.maxCapacity = 0
  · rw [hU]; simp; omega
  · have hbound : I.maxCapacity ≤ 2 ^ (narrowBitLength I - 1) - 1 := by
      unfold Instance.maxCapacity
      apply foldr_max_le_of_all
      intro x hx
      rcases List.mem_append.mp hx with he | hd
      · rcases List.mem_map.mp he with ⟨e, he_mem, rfl⟩
        have hsum : narrowEdgeBits e ≤ narrowBitLength I :=
          le_trans (le_sum_map_of_mem he_mem) (by unfold narrowBitLength; omega)
        have hlo : e.lower.natAbs < 2 ^ (narrowBitLength I - 1) :=
          natAbs_lt_pow_pred_of_intBits_le (by unfold narrowEdgeBits at hsum; omega)
        have hhi : e.upper.natAbs < 2 ^ (narrowBitLength I - 1) :=
          natAbs_lt_pow_pred_of_intBits_le (by unfold narrowEdgeBits at hsum; omega)
        exact max_le (by omega) (by omega)
      · rcases List.mem_map.mp hd with ⟨d, hd_mem, rfl⟩
        have hsum : narrowIntBits d ≤ narrowBitLength I :=
          le_trans (le_sum_map_of_mem hd_mem) (by unfold narrowBitLength; omega)
        have hdlt := natAbs_lt_pow_pred_of_intBits_le hsum
        omega
    have hlt : I.maxCapacity < 2 ^ (narrowBitLength I - 1) := by
      have hp : 1 ≤ 2 ^ (narrowBitLength I - 1) := Nat.two_pow_pos _
      omega
    have hlog := (Nat.log_lt_iff_lt_pow (by decide) hU).mpr hlt
    omega

private lemma log_maxCost_add_two_le_bitLength (I : Instance) :
    Nat.log 2 I.maxCost + 2 ≤ narrowBitLength I := by
  have h4 := four_le_narrowBitLength I
  by_cases hC : I.maxCost = 0
  · rw [hC]; simp; omega
  · have hbound : I.maxCost ≤ 2 ^ (narrowBitLength I - 1) - 1 := by
      unfold Instance.maxCost
      apply foldr_max_le_of_all
      intro x hx
      rcases List.mem_map.mp hx with ⟨e, he_mem, rfl⟩
      have hsum : narrowEdgeBits e ≤ narrowBitLength I :=
        le_trans (le_sum_map_of_mem he_mem) (by unfold narrowBitLength; omega)
      have hco : e.cost.natAbs < 2 ^ (narrowBitLength I - 1) :=
        natAbs_lt_pow_pred_of_intBits_le (by unfold narrowEdgeBits at hsum; omega)
      omega
    have hlt : I.maxCost < 2 ^ (narrowBitLength I - 1) := by
      have hp : 1 ≤ 2 ^ (narrowBitLength I - 1) := Nat.two_pow_pos _
      omega
    have hlog := (Nat.log_lt_iff_lt_pow (by decide) hC).mpr hlt
    omega

private lemma size_scalingCapacityBudget_le_two_mul (I : Instance) (hv : I.IsValid) :
    Nat.size (FlowReduction.scalingCapacityBudget I I.maxCapacity) ≤ 2 * narrowBitLength I := by
  set z := narrowBitLength I
  have hge := narrowBitLength_ge I hv
  have hU := log_maxCapacity_add_two_le_bitLength I
  apply Nat.size_le.mpr
  have h2m : 2 * (I.m + 1) < 2 ^ z := by
    have hlt : z < 2 ^ z := Nat.lt_two_pow_self
    omega
  have hU_lt : I.maxCapacity < 2 ^ (z - 1) := by
    have h1 := Nat.lt_pow_succ_log_self (by decide : 1 < 2) I.maxCapacity
    have h2 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show Nat.log 2 I.maxCapacity + 1 ≤ z - 1 by omega)
    omega
  have hprod : 2 * (I.m + 1) * I.maxCapacity + 1 ≤ 2 ^ z * 2 ^ (z - 1) := by
    have h1 : 2 * (I.m + 1) ≤ 2 ^ z - 1 := by omega
    have h2 : I.maxCapacity ≤ 2 ^ (z - 1) - 1 := by omega
    have hmul := Nat.mul_le_mul h1 h2
    have hp1 : 1 ≤ 2 ^ z := Nat.two_pow_pos z
    have hp2 : 1 ≤ 2 ^ (z - 1) := Nat.two_pow_pos (z - 1)
    have hexp : (2 ^ z - 1) * (2 ^ (z - 1) - 1) + 1 ≤ 2 ^ z * 2 ^ (z - 1) := by
      zify [hp1, hp2]; nlinarith
    omega
  have hpow_lt : 2 ^ z * 2 ^ (z - 1) < 2 ^ (2 * z) := by
    rw [← Nat.pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  unfold FlowReduction.scalingCapacityBudget
  omega

private lemma narrowMainSpace_le_poly {S : ℕ → ℕ → ℕ} {a e : ℕ}
    (hS : ∀ n m, S n m ≤ a * (n + m + 2) ^ e)
    (I : Instance) (hv : I.IsValid) :
    let z := narrowBitLength I
    narrowMainSpace I S ≤ 3706 * z ^ 3 + 336 * a * z ^ (2 * e + 2) := by
  set z := narrowBitLength I
  set k := narrowLimbWidth I
  set U := I.maxCapacity
  set C := I.maxCost
  have hge : 10 * I.m + 2 * I.n + 4 ≤ z := narrowBitLength_ge I hv
  have h4 : 4 ≤ z := four_le_narrowBitLength I
  have hk3 : 3 ≤ k := three_le_narrowLimbWidth I
  have hk1 : 1 ≤ k := one_le_narrowLimbWidth I
  have hU_log : Nat.log 2 U + 2 ≤ z := log_maxCapacity_add_two_le_bitLength I
  have hC_log : Nat.log 2 C + 2 ≤ z := log_maxCost_add_two_le_bitLength I
  have hTU : Nat.size (FlowReduction.scalingCapacityBudget I U) ≤ 2 * z :=
    size_scalingCapacityBudget_le_two_mul I hv
  have hLU : narrowMaxCapLimbs I ≤ z := by
    have h1 : narrowMaxCapLimbs I ≤ Nat.clog 2 (U + 1) := digits_length_le_clog hk1
    have h2 : Nat.clog 2 (U + 1) ≤ z := by
      apply Nat.clog_le_of_le_pow
      have := Nat.lt_pow_succ_log_self (by decide : 1 < 2) U
      have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show Nat.log 2 U + 1 ≤ z by omega)
      omega
    omega
  have hLC : narrowMaxCostLimbs I ≤ z := by
    have h1 : narrowMaxCostLimbs I ≤ Nat.clog 2 (C + 1) := digits_length_le_clog hk1
    have h2 : Nat.clog 2 (C + 1) ≤ z := by
      apply Nat.clog_le_of_le_pow
      have := Nat.lt_pow_succ_log_self (by decide : 1 < 2) C
      have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show Nat.log 2 C + 1 ≤ z by omega)
      omega
    omega
  have hLc : Nat.size (max C 1) ≤ z := by
    apply Nat.size_le.mpr
    have h1 := Nat.lt_pow_succ_log_self (by decide : 1 < 2) C
    have h2 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show Nat.log 2 C + 1 ≤ z by omega)
    have h3 : 1 < 2 ^ z := by have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) h4; omega
    omega
  have hclogC : Nat.clog 2 (C + 2) ≤ z := by
    apply Nat.clog_le_of_le_pow
    have h1 : C < 2 ^ (Nat.log 2 C + 1) := Nat.lt_pow_succ_log_self (by decide) C
    have h2 : 2 ^ (Nat.log 2 C + 2) = 2 ^ (Nat.log 2 C + 1) * 2 := Nat.pow_succ 2 (Nat.log 2 C + 1)
    have h3 : 2 ^ (Nat.log 2 C + 2) ≤ 2 ^ z := Nat.pow_le_pow_right (by decide) hC_log
    have h4p : 2 ≤ 2 ^ (Nat.log 2 C + 1) := by
      have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.succ_pos (Nat.log 2 C)); omega
    omega
  have hclogm : Nat.clog 2 (I.m + 1) ≤ I.m := by
    apply Nat.clog_le_of_le_pow
    have := Nat.lt_two_pow_self (n := I.m)
    omega
  have hKcap : Nat.size (FlowReduction.scalingCapacityBudget I U) / k + 2 ≤ 2 * z := by
    have hdiv : Nat.size (FlowReduction.scalingCapacityBudget I U) / k ≤
        Nat.size (FlowReduction.scalingCapacityBudget I U) / 3 := Nat.div_le_div_left hk3 (by omega)
    omega
  have hLlimbs : Nat.size (max C 1) / k + 2 ≤ z := by
    have hdiv : Nat.size (max C 1) / k ≤ Nat.size (max C 1) / 3 := Nat.div_le_div_left hk3 (by omega)
    omega
  have hR : 28 * (Nat.clog 2 (C + 2) + Nat.clog 2 (I.m + 1) + 1) ≤ 56 * z := by omega
  have hz2 : 4 * z ≤ z ^ 2 := by
    have := Nat.mul_le_mul_right z h4; rw [sq]; exact this
  have hz3 : 4 * z ^ 2 ≤ z ^ 3 := by
    have := Nat.mul_le_mul_right (z ^ 2) h4
    rw [show z ^ 3 = z * z ^ 2 from by rw [pow_succ, Nat.mul_comm]]; exact this
  have hm_z : 10 * I.m ≤ z := by omega
  have hmz : 10 * I.m * z ≤ z ^ 2 := by
    have := Nat.mul_le_mul_right z hm_z; rw [sq]; exact this
  have h42m : 42 * I.m + 4 ≤ z ^ 2 := by
    by_cases hm0 : I.m = 0
    · rw [hm0]; omega
    · have hz14 : 14 ≤ z := by omega
      have h14z : 14 * z ≤ z ^ 2 := by
        have := Nat.mul_le_mul_right z hz14; rw [sq]; exact this
      omega
  have hS1 : S (6 * I.m + 1) (12 * I.m) ≤ a * z ^ (2 * e) := by
    calc S (6 * I.m + 1) (12 * I.m)
        ≤ a * (6 * I.m + 1 + 12 * I.m + 2) ^ e := hS _ _
      _ ≤ a * (z ^ 2) ^ e := Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) e)
      _ = a * z ^ (2 * e) := by rw [← Nat.pow_mul]
  have hS2 : S (6 * I.m + 2) (36 * I.m) ≤ a * z ^ (2 * e) := by
    calc S (6 * I.m + 2) (36 * I.m)
        ≤ a * (6 * I.m + 2 + 36 * I.m + 2) ^ e := hS _ _
      _ ≤ a * (z ^ 2) ^ e := Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) e)
      _ = a * z ^ (2 * e) := by rw [← Nat.pow_mul]
  have hstart : (I.n + 1) + 30 + 48 * I.m +
      15 * I.m * (Nat.size (FlowReduction.scalingCapacityBudget I U) / k + 2) +
      3 * I.m * (Nat.size (max C 1) / k + 2) ≤ 9 * z ^ 2 := by
    have h1 : 15 * I.m * (Nat.size (FlowReduction.scalingCapacityBudget I U) / k + 2) ≤
        3 * (10 * I.m * z) := by
      have := Nat.mul_le_mul_left (15 * I.m) hKcap
      have heq : 15 * I.m * (2 * z) = 3 * (10 * I.m * z) := by ring
      omega
    have h2 : 3 * I.m * (Nat.size (max C 1) / k + 2) ≤ 10 * I.m * z := by
      have := Nat.mul_le_mul_left (3 * I.m) hLlimbs
      have : 3 * I.m * z ≤ 10 * I.m * z := Nat.mul_le_mul_right z (by omega)
      omega
    omega
  have hbs : 5 + 12 * I.m +
      18 * I.m * (Nat.size (FlowReduction.scalingCapacityBudget I U) / k + 2) +
      Nat.size (FlowReduction.scalingCapacityBudget I U) *
        (2 + 72 * I.m + S (6 * I.m + 1) (12 * I.m)) ≤
      21 * z ^ 2 + 2 * z * (a * z ^ (2 * e)) := by
    have h1 : 18 * I.m * (Nat.size (FlowReduction.scalingCapacityBudget I U) / k + 2) ≤
        4 * (10 * I.m * z) := by
      have := Nat.mul_le_mul_left (18 * I.m) hKcap
      have heq : 18 * I.m * (2 * z) = 36 * I.m * z := by ring
      have : 36 * I.m * z ≤ 4 * (10 * I.m * z) := by
        have : 4 * (10 * I.m * z) = 40 * I.m * z := by ring
        have := Nat.mul_le_mul_right z (show 36 * I.m ≤ 40 * I.m by omega)
        omega
      omega
    have h2 := Nat.mul_le_mul hTU (Nat.add_le_add_left hS1 (2 + 72 * I.m))
    rw [Nat.mul_add (2 * z)] at h2
    have h3 : 2 * z * (2 + 72 * I.m) ≤ 16 * z ^ 2 := by
      have : 2 + 72 * I.m ≤ 8 * z := by omega
      have hmul := Nat.mul_le_mul_left (2 * z) this
      have heq : 2 * z * (8 * z) = 16 * z ^ 2 := by ring
      omega
    omega
  have hdual : 50 + 180 * I.m + 150 * I.m + S (6 * I.m + 2) (36 * I.m) ≤
      12 * z ^ 2 + a * z ^ (2 * e) := by omega
  have hR_prod : 28 * (Nat.clog 2 (C + 2) + Nat.clog 2 (I.m + 1) + 1) *
      ((5 + 12 * I.m + 18 * I.m * (Nat.size (FlowReduction.scalingCapacityBudget I U) / k + 2) +
          Nat.size (FlowReduction.scalingCapacityBudget I U) *
            (2 + 72 * I.m + S (6 * I.m + 1) (12 * I.m))) +
       (50 + 180 * I.m + 150 * I.m + S (6 * I.m + 2) (36 * I.m))) ≤
      1848 * z ^ 3 + 168 * a * z ^ (2 * e + 2) := by
    have hsum0 := Nat.add_le_add hbs hdual
    have hsum : (5 + 12 * I.m + 18 * I.m * (Nat.size (FlowReduction.scalingCapacityBudget I U) / k + 2) +
          Nat.size (FlowReduction.scalingCapacityBudget I U) *
            (2 + 72 * I.m + S (6 * I.m + 1) (12 * I.m))) +
       (50 + 180 * I.m + 150 * I.m + S (6 * I.m + 2) (36 * I.m)) ≤
        33 * z ^ 2 + (2 * z + 1) * (a * z ^ (2 * e)) := by
      have : 2 * z * (a * z ^ (2 * e)) + a * z ^ (2 * e) =
          (2 * z + 1) * (a * z ^ (2 * e)) := by ring
      omega
    have hmul := Nat.mul_le_mul hR hsum
    have hz1 : 2 * z + 1 ≤ 3 * z := by omega
    have hmul2 : 56 * z * (33 * z ^ 2 + (2 * z + 1) * (a * z ^ (2 * e))) ≤
        56 * z * (33 * z ^ 2 + 3 * z * (a * z ^ (2 * e))) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ hz1) _)
    have heq : 56 * z * (33 * z ^ 2 + 3 * z * (a * z ^ (2 * e))) =
        1848 * z ^ 3 + 168 * a * z ^ (2 * e + 2) := by
      rw [show z ^ (2 * e + 2) = z ^ (2 * e) * z ^ 2 from Nat.pow_add z (2 * e) 2]
      ring
    omega
  have houter : 4 * I.n + 65 * I.m + 13 * I.m * (narrowMaxCapLimbs I + 1) +
      2 * I.m * narrowMaxCostLimbs I + 7 * (narrowMaxCapLimbs I + 1) + 60 ≤ 4 * z ^ 3 := by
    have h1 : 13 * I.m * (narrowMaxCapLimbs I + 1) ≤ 13 * I.m * z + 13 * I.m := by
      have := Nat.mul_le_mul_left (13 * I.m) (show narrowMaxCapLimbs I + 1 ≤ z + 1 by omega)
      rw [Nat.mul_add, Nat.mul_one] at this; exact this
    have h1' : 13 * I.m * z ≤ 2 * (10 * I.m * z) := by
      have : 2 * (10 * I.m * z) = 20 * I.m * z := by ring
      have := Nat.mul_le_mul_right z (show 13 * I.m ≤ 20 * I.m by omega)
      omega
    have h2 : 2 * I.m * narrowMaxCostLimbs I ≤ 10 * I.m * z := by
      have := Nat.mul_le_mul_left (2 * I.m) hLC
      have := Nat.mul_le_mul_right z (show 2 * I.m ≤ 10 * I.m by omega)
      omega
    omega
  have h9z : 9 * z ^ 2 ≤ 3 * z ^ 3 := by omega
  have h336 : 2 * (168 * a * z ^ (2 * e + 2)) = 336 * a * z ^ (2 * e + 2) := by ring
  dsimp only [U, C, k] at hstart hR_prod
  unfold narrowMainSpace narrowStage1SpaceBound
  dsimp only
  omega

/-! ### Main word-size theorems -/

/-- For any solver space bounded by `a * (n + m + 2) ^ e` and any word-size multiplier
`c ≥ narrowWordMultiplierPoly a e`, every valid instance satisfies `NarrowMainFits` at
`wordSize c (narrowEncode I)`. -/
theorem narrowMainFits_wordSize_of_poly {S : ℕ → ℕ → ℕ} {a e c : ℕ}
    (hS : ∀ n m, S n m ≤ a * (n + m + 2) ^ e)
    (hc : narrowWordMultiplierPoly a e ≤ c)
    (I : Instance) (hv : I.IsValid) :
    NarrowMainFits (wordSize c (narrowEncode I)) S I hv := by
  set xs := narrowEncode I
  set B := xs.length + xs.foldr max 0 + 2
  set z := narrowBitLength I
  set k := narrowLimbWidth I
  have hc24 : 24 ≤ c := le_trans (le_max_left _ _) hc
  have hc_poly : 4 * e + Nat.clog 8 a + 9 ≤ c := le_trans (le_max_right _ _) hc
  have hz_le : z ≤ B ^ 2 := narrowBitLength_le_base_sq I hv
  have hk3 : 3 ≤ k := three_le_narrowLimbWidth I
  have hlen3 : 3 ≤ xs.length := narrowEncode_length_ge_three I
  have hk_max : k ≤ xs.foldr max 0 := by
    simp only [xs, narrowEncode, List.foldr_cons]; exact le_max_left _ _
  have hB8 : 8 ≤ B := by omega
  have h4z : 4 ≤ z := four_le_narrowBitLength I
  have hge := narrowBitLength_ge I hv
  refine ⟨?_, ?_, ?_⟩
  · -- Conjunct 1: `2 * k + 1 ≤ wordSize c xs`
    have hBlog : B < 2 ^ (Nat.log 2 B + 1) := Nat.lt_pow_succ_log_self (by decide) B
    have hz_lt : z < 2 ^ (2 * (Nat.log 2 B + 1)) := by
      calc z ≤ B ^ 2 := hz_le
        _ < (2 ^ (Nat.log 2 B + 1)) ^ 2 := Nat.pow_lt_pow_left hBlog (by decide)
        _ = 2 ^ (2 * (Nat.log 2 B + 1)) := by rw [← Nat.pow_mul, Nat.mul_comm]
    have hlogz : Nat.log 2 z < 2 * (Nat.log 2 B + 1) :=
      (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr hz_lt
    have hB1 : 1 ≤ Nat.log 2 B + 1 := Nat.succ_pos _
    have hw : wordSize c xs = c * (Nat.log 2 B + 1) := rfl
    have hk_eq : k = Nat.log 2 z + 1 := rfl
    have h5c : 5 * (Nat.log 2 B + 1) ≤ c * (Nat.log 2 B + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · -- Conjunct 2: `(18 * I.m + 21) * upperClip (3 * I.m) < 2 ^ wordSize c xs`
    have hB24 : (18 * I.m + 21) * upperClip (3 * I.m) ≤ B ^ c := by
      have h24 : (18 * I.m + 21) * upperClip (3 * I.m) ≤ B ^ 24 := by
        by_cases hm0 : I.m = 0
        · rw [hm0]
          have huc0 : upperClip 0 = 1 := by decide
          rw [huc0]
          have h8_24 : 8 ^ 2 ≤ B ^ 24 :=
            le_trans (Nat.pow_le_pow_left hB8 2) (Nat.pow_le_pow_right (by omega) (by decide))
          omega
        · have hup : upperClip (3 * I.m) ≤ (6 * I.m) ^ 10 := by
            have := upperClip_le_pow10 (3 * I.m) (by omega)
            simpa only [show 2 * (3 * I.m) = 6 * I.m by omega] using this
          have hup_z : upperClip (3 * I.m) ≤ z ^ 10 :=
            le_trans hup (Nat.pow_le_pow_left (by omega) 10)
          have hcoef : 18 * I.m + 21 ≤ z ^ 2 := by
            have hz14 : 14 ≤ z := by omega
            have h14z : 14 * z ≤ z ^ 2 := by
              have := Nat.mul_le_mul_right z hz14; rw [sq]; exact this
            omega
          calc (18 * I.m + 21) * upperClip (3 * I.m)
              ≤ z ^ 2 * z ^ 10 := Nat.mul_le_mul hcoef hup_z
            _ = z ^ 12 := (Nat.pow_add z 2 10).symm
            _ ≤ (B ^ 2) ^ 12 := Nat.pow_le_pow_left hz_le 12
            _ = B ^ 24 := by rw [← Nat.pow_mul]
      exact le_trans h24 (Nat.pow_le_pow_right (by omega) hc24)
    exact lt_of_le_of_lt hB24 (pow_lt_two_pow_wordSize (by omega) xs)
  · -- Conjunct 3: `xs.length + narrowMainSpace I S < 2 ^ wordSize c xs`
    have hspace : narrowMainSpace I S ≤ 3706 * z ^ 3 + 336 * a * z ^ (2 * e + 2) :=
      narrowMainSpace_le_poly hS I hv
    have ht1 : xs.length + 3706 * z ^ 3 < B ^ 11 := by
      have h3706 : 3706 < B ^ 4 := by
        have := Nat.pow_le_pow_left hB8 4
        omega
      have hz3 : z ^ 3 ≤ B ^ 6 := by
        calc z ^ 3 ≤ (B ^ 2) ^ 3 := Nat.pow_le_pow_left hz_le 3
          _ = B ^ 6 := by rw [← Nat.pow_mul]
      have hprod : 3706 * z ^ 3 < B ^ 10 := by
        have := Nat.mul_lt_mul_of_lt_of_le' h3706 hz3 (Nat.pow_pos (by omega))
        rw [← Nat.pow_add] at this
        exact this
      have hlen_le : xs.length ≤ B ^ 10 :=
        le_trans (by omega : xs.length ≤ B) (Nat.le_self_pow (by decide) B)
      have h2B10 : 2 * B ^ 10 < B ^ 11 := by
        rw [Nat.pow_succ B 10, Nat.mul_comm (B ^ 10) B]
        exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega))
      omega
    have ht2 : 336 * a * z ^ (2 * e + 2) ≤ B ^ (4 * e + Nat.clog 8 a + 7) := by
      have h336 : 336 ≤ B ^ 3 := by
        have := Nat.pow_le_pow_left hB8 3; omega
      have ha : a ≤ B ^ Nat.clog 8 a :=
        le_trans (Nat.le_pow_clog (by decide : 1 < 8) a) (Nat.pow_le_pow_left hB8 _)
      have hz_pow : z ^ (2 * e + 2) ≤ B ^ (4 * e + 4) := by
        calc z ^ (2 * e + 2) ≤ (B ^ 2) ^ (2 * e + 2) := Nat.pow_le_pow_left hz_le _
          _ = B ^ (4 * e + 4) := by rw [← Nat.pow_mul, show 2 * (2 * e + 2) = 4 * e + 4 by omega]
      calc 336 * a * z ^ (2 * e + 2)
          ≤ B ^ 3 * B ^ Nat.clog 8 a * B ^ (4 * e + 4) :=
            Nat.mul_le_mul (Nat.mul_le_mul h336 ha) hz_pow
        _ = B ^ (4 * e + Nat.clog 8 a + 7) := by
            rw [← Nat.pow_add, ← Nat.pow_add]
            congr 1; omega
    have ht1' : xs.length + 3706 * z ^ 3 ≤ B ^ (c - 1) :=
      le_trans (le_of_lt ht1) (Nat.pow_le_pow_right (by omega) (by omega))
    have ht2' : 336 * a * z ^ (2 * e + 2) ≤ B ^ (c - 1) :=
      le_trans ht2 (Nat.pow_le_pow_right (by omega) (by omega))
    have hsum_le : xs.length + narrowMainSpace I S ≤ B ^ c := by
      have h2B : 2 * B ^ (c - 1) ≤ B ^ c := by
        have hc1 : c - 1 + 1 = c := by omega
        rw [← hc1, Nat.pow_succ, Nat.mul_comm (B ^ (c - 1)) B]
        exact Nat.mul_le_mul_right _ (by omega)
      omega
    exact lt_of_le_of_lt hsum_le (pow_lt_two_pow_wordSize (by omega) xs)

/-- For any positive multiplier `c ≥ 1`, both the length and every word of `narrowEncode I`
fit in `wordSize c (narrowEncode I)` bits. -/
theorem narrowEncode_words_and_len_lt_of_pos {c : ℕ} (hc : 1 ≤ c) (I : Instance) :
    (narrowEncode I).length < 2 ^ wordSize c (narrowEncode I) ∧
    ∀ x ∈ narrowEncode I, x < 2 ^ wordSize c (narrowEncode I) :=
  ⟨length_lt_two_pow_wordSize hc (narrowEncode I),
   fun _ hx => lt_two_pow_wordSize_of_mem hc hx⟩

/-- Corollary at `narrowWordMultiplier d = 168 * scratchWordMultiplier 1 d + 17` for any solver
space satisfying `S n m ≤ 8 * (n + m + 2) ^ (42 * scratchWordMultiplier 1 d)`. -/
theorem narrowMainFits_wordSize {d : ℕ} {S : ℕ → ℕ → ℕ}
    (hS : ∀ n m, S n m ≤ 8 * (n + m + 2) ^ (42 * scratchWordMultiplier 1 d))
    (I : Instance) (hv : I.IsValid) :
    NarrowMainFits (wordSize (narrowWordMultiplier d) (narrowEncode I)) S I hv :=
  narrowMainFits_wordSize_of_poly hS (narrowWordMultiplierPoly_le_narrowWordMultiplier d) I hv

/-- Both the length and every word of `narrowEncode I` fit at `narrowWordMultiplier d`. -/
theorem narrowEncode_words_and_len_lt (d : ℕ) (I : Instance) :
    (narrowEncode I).length < 2 ^ wordSize (narrowWordMultiplier d) (narrowEncode I) ∧
    ∀ x ∈ narrowEncode I, x < 2 ^ wordSize (narrowWordMultiplier d) (narrowEncode I) :=
  narrowEncode_words_and_len_lt_of_pos (by unfold narrowWordMultiplier; omega) I

end MinCostFlow.NarrowTop
