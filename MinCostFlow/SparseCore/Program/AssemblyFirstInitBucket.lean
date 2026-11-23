module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBucketMath
public import MinCostFlow.Num.Absolute
public import MinCostFlow.Num.ExtendCopy
public import MinCostFlow.Num.Multiply
public import MinCostFlow.Num.EffectiveLength
public import MinCostFlow.Num.ShiftLeft
public import MinCostFlow.Num.UnsignedLess
public import MinCostFlow.Num.ModulePlacement
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitLengths
import MinCostFlow.Num.ExtendFacts
import MinCostFlow.Num.ShiftFacts
import MinCostFlow.Num.DivisionStepFacts
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# The bucket word of an edge (`AssemblyFirstInitBucket`)

At the init of a branch, each edge `e` of the graph gets the word
`bucketCode (bucketOf (wstr e · ℓ₀ e))` (`AsmSdMapsAt`, `AssemblyBranchSide.lean`). P4's export
gives `wstr e = num / den` as two signed integers of `L_w` limbs, and `ℓ₀ e = len / 2 ^ P` is a
fixed-point number of `L` limbs (`BranchLengthsAt`). All limbs have four bits. This file gives a
procedure `bucketWordBody` that returns this word, and its contract `bucketWord_meetsContract`.

The procedure follows `AssemblyFirstInitBucketMath.lean`. With `K = L_w + L + 1` and
`Z = 2 K + L_w + 1`, it
1. writes `|num|` (`absolute`), widens `|num|` and `len` to `K` limbs (`extendCopy`, fill `0`), and
   multiplies them (`multiply`). The product `X = |num| · len` has `2 K` limbs;
2. finds the top nonzero limb of `X` (`effectiveLength`), and so `a = ⌊log₂ X⌋`, and in the same
   way `c = ⌊log₂ den⌋`. The floor of `log₂` of a limb is three tests (`limbLog`);
3. widens `X` and `den` to `Z` limbs, shifts `X` left by `c` and `den` by `a` (`shiftLeft`), and
   compares the two (`unsignedLess`). This gives the test `lt`;
4. returns `0` when `X = 0`, and `bucketCode (a - (c + P + lt))` otherwise.

The cost is quadratic in `K` (the product), and the procedure uses `5 L_w + 16 K + 4` fresh words.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore

/-! ## Facts on blocks of limbs -/

theorem bucket_capacity_four (n : ℕ) : Num.capacity 4 n = 2 ^ (4 * n) := by
  simp only [Num.capacity, Num.base, ← pow_mul]

theorem bucket_valid_of_agree {m m' : ℕ → ℕ} {a h L : ℕ} (hv : Num.Valid m a h L)
    (hag : ∀ i < L, m' (a + i) = m (a + i)) : Num.Valid m' a h L := fun i hi => by
  rw [hag i hi]
  exact hv i hi

theorem bucket_unsignedVal_of_agree {m m' : ℕ → ℕ} {a h L : ℕ}
    (hag : ∀ i < L, m' (a + i) = m (a + i)) :
    Num.unsignedVal m' a h L = Num.unsignedVal m a h L :=
  Num.unsignedVal_congr hag

/-- A block widened with zero limbs: it is valid, with the same unsigned value. -/
theorem bucket_extZero {m m0 : ℕ → ℕ} {q a M K : ℕ}
    (hl : ListAt m q (Num.extendedLimbs m0 a 0 M K)) (hv : Num.Valid m0 a 4 M) (hMK : M ≤ K) :
    Num.Valid m q 4 K ∧ Num.unsignedVal m q 4 K = Num.unsignedVal m0 a 4 M := by
  have hval := Num.valid_listAt hl (Num.extendedLimbs_lt hv (Num.base_pos 4))
  have hu := Num.unsignedVal_listAt (h := 4) hl
  rw [Num.extendedLimbs_length] at hval hu
  exact ⟨hval, hu.trans (Num.listVal_extended_zero hMK)⟩

/-- A block whose unsigned value is below half its capacity reads as that value. -/
theorem bucket_intVal_of_small {m : ℕ → ℕ} {q h K : ℕ}
    (h2 : 2 * Num.unsignedVal m q h K < Num.capacity h K) :
    Num.intVal m q h K = Num.unsignedVal m q h K := by
  simp [Num.intVal, Num.signedVal, not_le.mpr h2]

/-- A positive block reads, unsigned, as the natural number of its value. -/
theorem bucket_unsignedVal_of_pos {m : ℕ → ℕ} {q h K : ℕ} (hv : Num.Valid m q h K)
    (hpos : 0 < Num.intVal m q h K) :
    Num.unsignedVal m q h K = (Num.intVal m q h K).toNat :=
  Num.unsignedVal_of_intVal_nonneg hv (Int.toNat_of_nonneg hpos.le).symm

theorem bucket_capacity_mono {M K : ℕ} (h : M ≤ K) : Num.capacity 4 M ≤ Num.capacity 4 K := by
  rw [bucket_capacity_four, bucket_capacity_four]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- A value below the capacity of `M` limbs is below half the capacity of `K > M` limbs. -/
theorem bucket_two_mul_lt {u M K : ℕ} (hu : u < Num.capacity 4 M) (hMK : M < K) :
    2 * u < Num.capacity 4 K := by
  rw [bucket_capacity_four] at hu ⊢
  have : 2 ^ (4 * M) * 2 ≤ 2 ^ (4 * K) := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- A shifted value that fits: `X < 2 ^ E` and `c < F` with `E + F ≤ 4 Z`. -/
theorem bucket_shift_lt {X c E F Z : ℕ} (hX : X < 2 ^ E) (hc : c < F) (hZ : E + F ≤ 4 * Z) :
    2 * (X * 2 ^ c) < Num.capacity 4 Z := by
  rw [bucket_capacity_four]
  have h1 : 2 * (X * 2 ^ c) < 2 * (2 ^ E * 2 ^ c) := by
    have := Nat.mul_lt_mul_of_pos_right hX (by positivity : 0 < 2 ^ c)
    omega
  have h2 : 2 * (2 ^ E * 2 ^ c) = 2 ^ (E + c + 1) := by rw [pow_add, pow_add]; ring
  have h3 : 2 ^ (E + c + 1) ≤ 2 ^ (4 * Z) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem bucket_fits_of_lt {n Z : ℕ} (h : 2 * n < Num.capacity 4 Z) : Num.Fits 4 Z (n : ℤ) := by
  unfold Num.Fits
  constructor <;> omega

theorem bucket_ite_le_one (a b : ℕ) : (if a < b then 1 else 0) ≤ 1 := by
  split_ifs <;> omega

/-- The machine's `⌊log₂⌋` of a block: `t` limbs up to the top nonzero limb, and `a` from the top
limb by `limbLog`. -/
theorem bucket_log_top {m : ℕ → ℕ} {p t K a : ℕ} (hv : Num.Valid m p 4 K) (ht : t ≤ K)
    (htop : 0 < t → 0 < m (p + (t - 1))) (ha : a = 4 * (t - 1) + limbLog (m (p + t - 1)))
    (h0 : 0 < t) : a = Nat.log 2 (Num.unsignedVal m p 4 t) := by
  have hv' : Num.Valid m p 4 ((t - 1) + 1) := fun i hi => hv i (by omega)
  have hl := natLog_unsignedVal_top hv' (htop h0)
  rw [show t - 1 + 1 = t by omega] at hl
  rw [hl, ha, show p + t - 1 = p + (t - 1) by omega]

/-- The block is zero exactly when its count `t` of limbs is zero. -/
theorem bucket_pos_iff {m : ℕ → ℕ} {p t : ℕ} (htop : 0 < t → 0 < m (p + (t - 1))) :
    0 < t ↔ 0 < Num.unsignedVal m p 4 t := by
  constructor
  · intro h0
    have htop' := htop h0
    by_contra hcon
    have hz' := (Num.unsignedVal_eq_zero_iff (mem := m) (a := p) (h := 4) (L := t)).mp
      (by omega)
    have := hz' (t - 1) (by omega)
    omega
  · intro h0
    by_contra hcon
    have h00 : t = 0 := by omega
    subst h00
    simp [Num.unsignedVal] at h0

/-! ## The procedure -/

/-- **The bucket word of an edge.** Arguments `[numA, denA, Lw, lenA, L, P, heap]`. Registers:
`7 = K`, `8 = Z`, `13` the product `X`, `14` its number `t` of limbs, `16 = a`, `17` the number
of limbs of `den`, `19 = c`, `24 = lt`, `25 = c + P + lt`, `26` the code. It returns the code
when `0 < t`, and `0` otherwise. -/
def bucketWordBody (fAbs fExt fMul fLen fShl fLess : ℕ) : Stmt :=
  .assign 7 (.bin .add (.bin .add (.reg 2) (.reg 4)) (.const 1)) ;;
  .assign 8 (.bin .add (.bin .add (.bin .mul (.const 2) (.reg 7)) (.reg 2)) (.const 1)) ;;
  .call 9 fAbs [.reg 0, .reg 2, .reg 6] ;;
  .call 10 fExt [.reg 6, .reg 2, .reg 7, .const 0, .reg 9] ;;
  .call 11 fExt [.reg 3, .reg 4, .reg 7, .const 0, .reg 10] ;;
  .call 12 fMul [.reg 9, .reg 10, .reg 7, .reg 11] ;;
  .assign 13 (.bin .add (.reg 11) (.bin .mul (.const 4) (.reg 7))) ;;
  .call 14 fLen [.reg 13, .bin .mul (.const 2) (.reg 7)] ;;
  .assign 15 (.load (.bin .sub (.bin .add (.reg 13) (.reg 14)) (.const 1))) ;;
  .assign 16 (.bin .add (.bin .mul (.const 4) (.bin .sub (.reg 14) (.const 1)))
    (.bin .add (.bin .add (.bin .lt (.const 1) (.reg 15)) (.bin .lt (.const 3) (.reg 15)))
      (.bin .lt (.const 7) (.reg 15)))) ;;
  .call 17 fLen [.reg 1, .reg 2] ;;
  .assign 18 (.load (.bin .sub (.bin .add (.reg 1) (.reg 17)) (.const 1))) ;;
  .assign 19 (.bin .add (.bin .mul (.const 4) (.bin .sub (.reg 17) (.const 1)))
    (.bin .add (.bin .add (.bin .lt (.const 1) (.reg 18)) (.bin .lt (.const 3) (.reg 18)))
      (.bin .lt (.const 7) (.reg 18)))) ;;
  .call 20 fExt [.reg 13, .bin .mul (.const 2) (.reg 7), .reg 8, .const 0, .reg 12] ;;
  .call 21 fExt [.reg 1, .reg 2, .reg 8, .const 0, .reg 20] ;;
  .call 22 fShl [.reg 12, .reg 8, .reg 19, .reg 21] ;;
  .call 23 fShl [.reg 20, .reg 8, .reg 16, .reg 22] ;;
  .call 24 fLess [.reg 21, .reg 22, .reg 8] ;;
  .assign 25 (.bin .add (.bin .add (.reg 19) (.reg 5)) (.reg 24)) ;;
  .assign 26 (.bin .sub (.bin .add (.bin .mul (.const 2) (.bin .sub (.reg 16) (.reg 25)))
      (.bin .mul (.const 2) (.bin .sub (.reg 25) (.reg 16)))) (.bin .lt (.reg 16) (.reg 25))) ;;
  .cond (.reg 14) (.ret (.reg 26)) (.ret (.const 0))

/-- The procedure and the arithmetic modules it calls, from `b` on (`16` bodies). -/
def bucketWordModule (b : ℕ) : List Stmt :=
  bucketWordBody (b + 1) (b + 6) (b + 7) (b + 12) (b + 13) (b + 15) ::
    (Num.absoluteModule (b + 1) 4 ++ (Num.extendCopyModule (b + 6) ++
      (Num.multiplyModule (b + 7) 4 ++ (Num.effectiveLengthModule (b + 12) ++
        (Num.shiftLeftModule (b + 13) 4 ++ Num.unsignedLessModule (b + 15))))))

theorem bucketWordModule_noRand (b : ℕ) : ∀ s ∈ bucketWordModule b, s.NoRand := by
  intro s hs
  simp only [bucketWordModule, List.mem_cons, List.mem_append] at hs
  rcases hs with rfl | hs | hs | hs | hs | hs | hs
  · simp [bucketWordBody, Stmt.NoRand]
  · exact Num.absoluteModule_noRand _ _ _ hs
  · simp only [Num.extendCopyModule, List.mem_singleton] at hs
    subst hs
    exact Num.extendCopyBody_noRand _
  · exact Num.multiplyModule_noRand _ _ _ hs
  · simp only [Num.effectiveLengthModule, List.mem_singleton] at hs
    subst hs
    exact Num.effectiveLengthBody_noRand _
  · exact Num.shiftLeftModule_noRand _ _ _ hs
  · simp only [Num.unsignedLessModule, List.mem_singleton] at hs
    subst hs
    exact Num.unsignedLessBody_noRand _

/-- The fresh words of the procedure. -/
def bucketWordSpace (Lw L : ℕ) : ℕ := 5 * Lw + 16 * (Lw + L + 1) + 4

/-- The cost of the procedure: quadratic in `K = Lw + L + 1`, from the product. -/
def bucketWordCost (Lw L : ℕ) : ℕ :=
  2 * (Lw + L + 1) * (38 * (2 * (Lw + L + 1)) + 35) + 1000 * (Lw + L + 1) + 1000

/-- **The contract of the bucket word.** The blocks `num`, `den` (`Lw` limbs) and `len` (`L`
limbs) lie below the heap pointer, with `0 < den` and `0 < len`. The procedure returns the code of
the bucket of `num / den · len / 2 ^ P`, keeps the memory below the heap pointer, and leaves zero
from `heap + bucketWordSpace Lw L` on. -/
def bucketWordContract (w : ℕ) : Contract where
  pre args mem := ∃ numA denA Lw lenA L P heap, args = [numA, denA, Lw, lenA, L, P, heap] ∧
    numA + Lw ≤ heap ∧ denA + Lw ≤ heap ∧ lenA + L ≤ heap ∧
    Num.Valid mem numA 4 Lw ∧ Num.Valid mem denA 4 Lw ∧ Num.Valid mem lenA 4 L ∧
    0 < Num.intVal mem denA 4 Lw ∧ 0 < Num.intVal mem lenA 4 L ∧
    ZeroFrom mem heap ∧ heap + bucketWordSpace Lw L < 2 ^ w ∧
    2 * (P + bucketWordSpace Lw L) < 2 ^ w
  post args mem v mem' :=
    (∀ x < args.getD 6 0, mem' x = mem x) ∧
    ZeroFrom mem' (args.getD 6 0 + bucketWordSpace (args.getD 2 0) (args.getD 4 0)) ∧
    v = bucketCode (bucketOf ((Num.intVal mem (args.getD 0 0) 4 (args.getD 2 0) : ℝ) /
      (Num.intVal mem (args.getD 1 0) 4 (args.getD 2 0) : ℝ) *
      Num.fixVal mem (args.getD 3 0) 4 (args.getD 4 0) (args.getD 5 0)))
  cost args _ := bucketWordCost (args.getD 2 0) (args.getD 4 0)

/-! ## The contract -/

set_option maxHeartbeats 1000000 in
/-- **The bucket word meets its contract**, at word size at least `10` (so that a product of two
limbs fits in a word). -/
theorem bucketWord_meetsContract {w b : ℕ} {p : Program} (hw : 10 ≤ w)
    (hp : p.HasAt b (bucketWordModule b)) : MeetsContract w p b (bucketWordContract w) := by
  have hR1 : p.HasAt (b + 1) (Num.absoluteModule (b + 1) 4 ++ (Num.extendCopyModule (b + 6) ++
      (Num.multiplyModule (b + 7) 4 ++ (Num.effectiveLengthModule (b + 12) ++
        (Num.shiftLeftModule (b + 13) 4 ++ Num.unsignedLessModule (b + 15)))))) :=
    Num.hasAt_append_right
      (xs := [bucketWordBody (b + 1) (b + 6) (b + 7) (b + 12) (b + 13) (b + 15)]) hp
  have hR2 : p.HasAt (b + 6) (Num.extendCopyModule (b + 6) ++
      (Num.multiplyModule (b + 7) 4 ++ (Num.effectiveLengthModule (b + 12) ++
        (Num.shiftLeftModule (b + 13) 4 ++ Num.unsignedLessModule (b + 15))))) :=
    Num.hasAt_append_right hR1
  have hR3 : p.HasAt (b + 7) (Num.multiplyModule (b + 7) 4 ++
      (Num.effectiveLengthModule (b + 12) ++
        (Num.shiftLeftModule (b + 13) 4 ++ Num.unsignedLessModule (b + 15)))) :=
    Num.hasAt_append_right hR2
  have hR4 : p.HasAt (b + 12) (Num.effectiveLengthModule (b + 12) ++
      (Num.shiftLeftModule (b + 13) 4 ++ Num.unsignedLessModule (b + 15))) :=
    Num.hasAt_append_right hR3
  have hR5 : p.HasAt (b + 13) (Num.shiftLeftModule (b + 13) 4 ++
      Num.unsignedLessModule (b + 15)) :=
    Num.hasAt_append_right hR4
  have hU : p.HasAt (b + 15) (Num.unsignedLessModule (b + 15)) := Num.hasAt_append_right hR5
  have hb16 : Num.base 4 < 2 ^ w := Num.base_lt_word (by omega)
  have hw16 : 16 < 2 ^ w := by simpa [Num.base] using hb16
  have hw1 : 1 < 2 ^ w := by omega
  have hAbsC := Num.absolute_meetsContract (by norm_num) hw1 hb16 (Num.hasAt_append_left hR1)
  have hExtC := Num.extendCopy_meetsContract (h := 4) hw1 (Num.hasAt_append_left hR2)
  have hMulC := Num.multiply_meetsContract (h := 4) (by norm_num) (by omega)
    (Num.hasAt_append_left hR3)
  have hLenC := Num.effectiveLength_meetsContract (h := 4) hw1 (Num.hasAt_append_left hR4)
  have hShlC := Num.shiftLeft_meetsContract (h := 4) (by norm_num) (by omega)
    (Num.hasAt_append_left hR5)
  have hLessC := Num.unsignedLess_meetsContract (h := 4) hw1 hU
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨numA, denA, Lw, lenA, L, P, heap, rfl, hnumA, hdenA, hlenA, hvn, hvd, hvl, hd0, hl0,
    hz, hsp, hPw⟩ := hpre
  have hheapw : heap < 2 ^ w := hwords heap (by simp)
  have hPw' : P < 2 ^ w := hwords P (by simp)
  unfold bucketWordSpace at hsp hPw
  obtain ⟨K, hK⟩ : ∃ K, K = Lw + L + 1 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 2 * K + Lw + 1 := ⟨_, rfl⟩
  apply runs_start_le
  unfold bucketWordBody
  refine runs_seq_assign_le (v := K) (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := Z) (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  -- 1. `|num|` at `heap`
  refine runs_seq_call_le hAbsC (vs := [numA, Lw, heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨numA, Lw, heap, rfl, hnumA, hvn⟩, hz, by change heap + Lw < 2 ^ w; omega⟩
  intro v1 m1 pos1 hp1
  obtain ⟨hv1, -, -, hf1, hz1, hval1, habs1⟩ := hp1
  change v1 = heap + Lw at hv1
  change ∀ x < heap, m1 x = mem x at hf1
  change Num.Valid m1 heap 4 Lw at hval1
  change Num.unsignedVal m1 heap 4 Lw = (Num.intVal mem numA 4 Lw).natAbs at habs1
  subst hv1
  -- 2. `|num|` widened to `K` limbs at `heap + Lw`
  refine runs_seq_call_le hExtC (vs := [heap, Lw, K, 0, heap + Lw]) (by eval_expr)
    (by wram_words) ?_ ?_
  · exact ⟨⟨heap, Lw, K, 0, heap + Lw, rfl, by omega, le_rfl, Num.base_pos 4, hval1⟩, hz1,
      by change heap + Lw + K < 2 ^ w; omega⟩
  intro v2 m2 pos2 hp2
  obtain ⟨hv2, -, -, hf2, hz2, hl2⟩ := hp2
  change v2 = heap + Lw + K at hv2
  change ∀ x < heap + Lw, m2 x = m1 x at hf2
  change ListAt m2 (heap + Lw) (Num.extendedLimbs m1 heap 0 Lw K) at hl2
  subst hv2
  have hag2 : ∀ x < heap, m2 x = mem x := fun x hx => by rw [hf2 x (by omega), hf1 x hx]
  have hvl2 : Num.Valid m2 lenA 4 L := bucket_valid_of_agree hvl (fun i hi => hag2 _ (by omega))
  -- 3. `len` widened to `K` limbs at `heap + Lw + K`
  refine runs_seq_call_le hExtC (vs := [lenA, L, K, 0, heap + Lw + K]) (by eval_expr)
    (by wram_words) ?_ ?_
  · exact ⟨⟨lenA, L, K, 0, heap + Lw + K, rfl, by omega, by omega, Num.base_pos 4, hvl2⟩, hz2,
      by change heap + Lw + K + K < 2 ^ w; omega⟩
  intro v3 m3 pos3 hp3
  obtain ⟨hv3, -, -, hf3, hz3, hl3⟩ := hp3
  change v3 = heap + Lw + K + K at hv3
  change ∀ x < heap + Lw + K, m3 x = m2 x at hf3
  change ListAt m3 (heap + Lw + K) (Num.extendedLimbs m2 lenA 0 L K) at hl3
  subst hv3
  -- the two factors
  have hA2 := bucket_extZero hl2 hval1 (by omega)
  have hagA : ∀ i < K, m3 (heap + Lw + i) = m2 (heap + Lw + i) := fun i hi => hf3 _ (by omega)
  have hA3v : Num.Valid m3 (heap + Lw) 4 K := bucket_valid_of_agree hA2.1 hagA
  have hA3u : Num.unsignedVal m3 (heap + Lw) 4 K = (Num.intVal mem numA 4 Lw).natAbs :=
    (bucket_unsignedVal_of_agree hagA).trans (hA2.2.trans habs1)
  have hB3 := bucket_extZero hl3 hvl2 (by omega)
  have hlenU : Num.unsignedVal m2 lenA 4 L = (Num.intVal mem lenA 4 L).toNat := by
    rw [bucket_unsignedVal_of_agree (m := mem) (fun i hi => hag2 _ (by omega))]
    exact bucket_unsignedVal_of_pos hvl hl0
  have hA3i : Num.intVal m3 (heap + Lw) 4 K = ((Num.intVal mem numA 4 Lw).natAbs : ℤ) := by
    rw [bucket_intVal_of_small, hA3u]
    rw [hA3u, ← habs1]
    exact bucket_two_mul_lt (Num.unsignedVal_lt hval1) (by omega)
  have hB3i : Num.intVal m3 (heap + Lw + K) 4 K = ((Num.intVal mem lenA 4 L).toNat : ℤ) := by
    rw [bucket_intVal_of_small, hB3.2, hlenU]
    rw [hB3.2, hlenU]
    have h1 := (Num.intVal_fits hvl).2
    have h2 : (((Num.intVal mem lenA 4 L).toNat : ℕ) : ℤ) = Num.intVal mem lenA 4 L :=
      Int.toNat_of_nonneg hl0.le
    have h3 : 2 * (Num.intVal mem lenA 4 L).toNat < Num.capacity 4 L := by omega
    exact lt_of_lt_of_le h3 (bucket_capacity_mono (by omega))
  -- 4. the product `X = |num| · len`, `2 K` limbs at `heap + Lw + 6 K`
  refine runs_seq_call_le hMulC (vs := [heap + Lw, heap + Lw + K, K, heap + Lw + K + K])
    (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨heap + Lw, heap + Lw + K, K, heap + Lw + K + K, rfl, by omega, by omega, hA3v,
      hB3.1⟩, hz3, by change heap + Lw + K + K + 6 * K < 2 ^ w; omega⟩
  intro v4 m4 pos4 hp4
  obtain ⟨hv4, -, -, hf4, hz4, hvalP, hprod⟩ := hp4
  change v4 = heap + Lw + K + K + 6 * K at hv4
  change ∀ x < heap + Lw + K + K, m4 x = m3 x at hf4
  change Num.Valid m4 (heap + Lw + K + K + 4 * K) 4 (2 * K) at hvalP
  change Num.intVal m4 (heap + Lw + K + K + 4 * K) 4 (2 * K) =
    Num.intVal m3 (heap + Lw) 4 K * Num.intVal m3 (heap + Lw + K) 4 K at hprod
  subst hv4
  obtain ⟨pX, hpX⟩ : ∃ pX, pX = heap + Lw + K + K + 4 * K := ⟨_, rfl⟩
  rw [← hpX] at hvalP hprod
  have hX : Num.unsignedVal m4 pX 4 (2 * K) =
      (Num.intVal mem numA 4 Lw).natAbs * (Num.intVal mem lenA 4 L).toNat := by
    apply Num.unsignedVal_of_intVal_nonneg hvalP
    rw [hprod, hA3i, hB3i]
    push_cast
    ring
  have hag4 : ∀ x < heap, m4 x = mem x := fun x hx => by
    rw [hf4 x (by omega), hf3 x (by omega), hag2 x hx]
  have hvd4 : Num.Valid m4 denA 4 Lw := bucket_valid_of_agree hvd (fun i hi => hag4 _ (by omega))
  have hYu : Num.unsignedVal m4 denA 4 Lw = (Num.intVal mem denA 4 Lw).toNat := by
    rw [bucket_unsignedVal_of_agree (m := mem) (fun i hi => hag4 _ (by omega))]
    exact bucket_unsignedVal_of_pos hvd hd0
  -- 5. the number `t` of limbs of `X`, and `a = ⌊log₂ X⌋`
  refine runs_seq_assign_le (v := pX) (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  refine runs_seq_call_le hLenC (vs := [pX, 2 * K]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨pX, 2 * K, rfl, by omega, hvalP⟩
  intro t m5 pos5 hp5
  obtain ⟨hm5, ht, htz, htop, hut⟩ := hp5
  change m5 = m4 at hm5
  change t ≤ 2 * K at ht
  change 0 < t → 0 < m4 (pX + (t - 1)) at htop
  change Num.unsignedVal m4 pX 4 t = Num.unsignedVal m4 pX 4 (2 * K) at hut
  subst m5
  clear htz
  have hb1 := bucket_ite_le_one 1 (m4 (pX + t - 1))
  have hb3 := bucket_ite_le_one 3 (m4 (pX + t - 1))
  have hb7 := bucket_ite_le_one 7 (m4 (pX + t - 1))
  refine runs_seq_assign_le (v := m4 (pX + t - 1))
    (Expr.eval_load_of_eq (x := pX + t - 1) (by eval_expr) rfl) ?_
  obtain ⟨a, ha⟩ : ∃ a, a = 4 * (t - 1) + limbLog (m4 (pX + t - 1)) := ⟨_, rfl⟩
  have ha3 : a ≤ 4 * (t - 1) + 3 := by
    have := limbLog_le_three (m4 (pX + t - 1))
    omega
  refine runs_seq_assign_le (v := a) (Expr.eval_eq_of_eq (by eval_expr) (by rw [ha]; rfl)) ?_
  -- 6. the number `tD` of limbs of `den`, and `c = ⌊log₂ den⌋`
  refine runs_seq_call_le hLenC (vs := [denA, Lw]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨denA, Lw, rfl, by omega, hvd4⟩
  intro tD m6 pos6 hp6
  obtain ⟨hm6, htD, htDz, htDtop, hutD⟩ := hp6
  change m6 = m4 at hm6
  change tD ≤ Lw at htD
  change 0 < tD → 0 < m4 (denA + (tD - 1)) at htDtop
  change Num.unsignedVal m4 denA 4 tD = Num.unsignedVal m4 denA 4 Lw at hutD
  subst m6
  clear htDz
  have hc1 := bucket_ite_le_one 1 (m4 (denA + tD - 1))
  have hc3 := bucket_ite_le_one 3 (m4 (denA + tD - 1))
  have hc7 := bucket_ite_le_one 7 (m4 (denA + tD - 1))
  refine runs_seq_assign_le (v := m4 (denA + tD - 1))
    (Expr.eval_load_of_eq (x := denA + tD - 1) (by eval_expr) rfl) ?_
  obtain ⟨c, hc⟩ : ∃ c, c = 4 * (tD - 1) + limbLog (m4 (denA + tD - 1)) := ⟨_, rfl⟩
  have hc3' : c ≤ 4 * (tD - 1) + 3 := by
    have := limbLog_le_three (m4 (denA + tD - 1))
    omega
  refine runs_seq_assign_le (v := c) (Expr.eval_eq_of_eq (by eval_expr) (by rw [hc]; rfl)) ?_
  -- 7. `X` widened to `Z` limbs at `q4 = heap + Lw + 8 K`
  obtain ⟨q4, hq4⟩ : ∃ q4, q4 = heap + Lw + K + K + 6 * K := ⟨_, rfl⟩
  rw [← hq4] at hz4
  refine runs_seq_call_le hExtC (vs := [pX, 2 * K, Z, 0, q4]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨pX, 2 * K, Z, 0, q4, rfl, by omega, by omega, Num.base_pos 4, hvalP⟩, hz4,
      by change q4 + Z < 2 ^ w; omega⟩
  intro v7 m7 pos7 hp7
  obtain ⟨hv7, -, -, hf7, hz7, hl7⟩ := hp7
  change v7 = q4 + Z at hv7
  change ∀ x < q4, m7 x = m4 x at hf7
  change ListAt m7 q4 (Num.extendedLimbs m4 pX 0 (2 * K) Z) at hl7
  subst hv7
  have hvd7 : Num.Valid m7 denA 4 Lw := bucket_valid_of_agree hvd4 (fun i hi => hf7 _ (by omega))
  -- 8. `den` widened to `Z` limbs at `q4 + Z`
  refine runs_seq_call_le hExtC (vs := [denA, Lw, Z, 0, q4 + Z]) (by eval_expr) (by wram_words)
    ?_ ?_
  · exact ⟨⟨denA, Lw, Z, 0, q4 + Z, rfl, by omega, by omega, Num.base_pos 4, hvd7⟩, hz7,
      by change q4 + Z + Z < 2 ^ w; omega⟩
  intro v8 m8 pos8 hp8
  obtain ⟨hv8, -, -, hf8, hz8, hl8⟩ := hp8
  change v8 = q4 + Z + Z at hv8
  change ∀ x < q4 + Z, m8 x = m7 x at hf8
  change ListAt m8 (q4 + Z) (Num.extendedLimbs m7 denA 0 Lw Z) at hl8
  subst hv8
  have hX7 := bucket_extZero hl7 hvalP (by omega)
  have hagX8 : ∀ i < Z, m8 (q4 + i) = m7 (q4 + i) := fun i hi => hf8 _ (by omega)
  have hX8v : Num.Valid m8 q4 4 Z := bucket_valid_of_agree hX7.1 hagX8
  have hX8u : Num.unsignedVal m8 q4 4 Z = Num.unsignedVal m4 pX 4 (2 * K) :=
    (bucket_unsignedVal_of_agree hagX8).trans hX7.2
  -- 9. `X · 2 ^ c` at `q4 + 2 Z`
  refine runs_seq_call_le hShlC (vs := [q4, Z, c, q4 + Z + Z]) (by eval_expr) (by wram_words)
    ?_ ?_
  · exact ⟨⟨q4, Z, c, q4 + Z + Z, rfl, by omega, hX8v⟩, hz8,
      by change q4 + Z + Z + Z < 2 ^ w; omega⟩
  intro v9 m9 pos9 hp9
  obtain ⟨hv9, -, -, hf9, hz9, hval9, hsh9⟩ := hp9
  change v9 = q4 + Z + Z + Z at hv9
  change ∀ x < q4 + Z + Z, m9 x = m8 x at hf9
  change Num.Valid m9 (q4 + Z + Z) 4 Z at hval9
  change Num.intVal m9 (q4 + Z + Z) 4 Z =
    Num.wrap 4 Z (Num.intVal m8 q4 4 Z * (2 : ℤ) ^ c) at hsh9
  subst hv9
  have hY8 := bucket_extZero hl8 hvd7 (by omega)
  have hagY9 : ∀ i < Z, m9 (q4 + Z + i) = m8 (q4 + Z + i) := fun i hi => hf9 _ (by omega)
  have hY9v : Num.Valid m9 (q4 + Z) 4 Z := bucket_valid_of_agree hY8.1 hagY9
  have hY9u : Num.unsignedVal m9 (q4 + Z) 4 Z = Num.unsignedVal m7 denA 4 Lw :=
    (bucket_unsignedVal_of_agree hagY9).trans hY8.2
  -- 10. `den · 2 ^ a` at `q4 + 3 Z`
  refine runs_seq_call_le hShlC (vs := [q4 + Z, Z, a, q4 + Z + Z + Z]) (by eval_expr)
    (by wram_words) ?_ ?_
  · exact ⟨⟨q4 + Z, Z, a, q4 + Z + Z + Z, rfl, by omega, hY9v⟩, hz9,
      by change q4 + Z + Z + Z + Z < 2 ^ w; omega⟩
  intro v10 m10 pos10 hp10
  obtain ⟨hv10, -, -, hf10, hz10, hval10, hsh10⟩ := hp10
  change v10 = q4 + Z + Z + Z + Z at hv10
  change ∀ x < q4 + Z + Z + Z, m10 x = m9 x at hf10
  change Num.Valid m10 (q4 + Z + Z + Z) 4 Z at hval10
  change Num.intVal m10 (q4 + Z + Z + Z) 4 Z =
    Num.wrap 4 Z (Num.intVal m9 (q4 + Z) 4 Z * (2 : ℤ) ^ a) at hsh10
  subst hv10
  have hag10 : ∀ i < Z, m10 (q4 + Z + Z + i) = m9 (q4 + Z + Z + i) := fun i hi =>
    hf10 _ (by omega)
  have hval10' : Num.Valid m10 (q4 + Z + Z) 4 Z := bucket_valid_of_agree hval9 hag10
  -- 11. the test `lt`
  refine runs_seq_call_le hLessC (vs := [q4 + Z + Z, q4 + Z + Z + Z, Z]) (by eval_expr)
    (by wram_words) ?_ ?_
  · exact ⟨q4 + Z + Z, q4 + Z + Z + Z, Z, rfl, by omega, by omega, hval10', hval10⟩
  intro lt m11 pos11 hp11
  obtain ⟨hm11, hlt⟩ := hp11
  change m11 = m10 at hm11
  change lt = if Num.unsignedVal m10 (q4 + Z + Z) 4 Z < Num.unsignedVal m10 (q4 + Z + Z + Z) 4 Z
    then 1 else 0 at hlt
  subst m11
  have hlt1 : lt ≤ 1 := by rw [hlt]; split_ifs <;> omega
  -- 12. the code
  refine runs_seq_assign_le (v := c + P + lt) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 2 * (a - (c + P + lt)) + 2 * ((c + P + lt) - a) -
    (if a < c + P + lt then 1 else 0)) (by eval_expr) ?_
  -- the facts on `X` and `t`
  obtain ⟨X, hXd⟩ : ∃ X, X = (Num.intVal mem numA 4 Lw).natAbs *
      (Num.intVal mem lenA 4 L).toNat := ⟨_, rfl⟩
  rw [← hXd] at hX
  have hXt : Num.unsignedVal m4 pX 4 t = X := hut.trans hX
  have hXlt : X < 2 ^ (8 * K) := by
    have h1 := Num.unsignedVal_lt hvalP
    rw [hX, bucket_capacity_four] at h1
    rw [show 8 * K = 4 * (2 * K) by ring]
    exact h1
  have ht_iff : 0 < t ↔ 0 < X := hXt ▸ bucket_pos_iff htop
  have ha_eq : 0 < t → a = Nat.log 2 X := fun h0 => hXt ▸ bucket_log_top hvalP ht htop ha h0
  -- the facts on `Y = den` and `tD`
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = (Num.intVal mem denA 4 Lw).toNat := ⟨_, rfl⟩
  rw [← hYd] at hYu
  have hYpos : 0 < Y := by
    have h1 : (((Num.intVal mem denA 4 Lw).toNat : ℕ) : ℤ) = Num.intVal mem denA 4 Lw :=
      Int.toNat_of_nonneg hd0.le
    omega
  have hYt : Num.unsignedVal m4 denA 4 tD = Y := hutD.trans hYu
  have hYlt : Y < 2 ^ (4 * Lw) := by
    have h1 := Num.unsignedVal_lt hvd4
    rwa [hYu, bucket_capacity_four] at h1
  have htD0 : 0 < tD := (bucket_pos_iff htDtop).mpr (hYt ▸ hYpos)
  have hc_eq : c = Nat.log 2 Y := hYt ▸ bucket_log_top hvd4 htD htDtop hc htD0
  have hc_lt : c < 4 * Lw := by
    rw [hc_eq]
    exact Nat.log_lt_of_lt_pow (by omega) hYlt
  -- the test, when `0 < t`
  have hlt_eq : 0 < t → lt = if X * 2 ^ c < Y * 2 ^ a then 1 else 0 := by
    intro h0
    have ha_lt : a < 8 * K := by omega
    have hX8i : Num.intVal m8 q4 4 Z = (X : ℤ) := by
      rw [bucket_intVal_of_small, hX8u, hX]
      rw [hX8u, hX]
      exact bucket_two_mul_lt
        (by rw [bucket_capacity_four, show 4 * (2 * K) = 8 * K by ring]; exact hXlt)
        (show 2 * K < Z by omega)
    have hsh9' : Num.intVal m9 (q4 + Z + Z) 4 Z = ((X * 2 ^ c : ℕ) : ℤ) := by
      rw [hsh9, hX8i]
      have hf := Num.wrap_of_fits (bucket_fits_of_lt (bucket_shift_lt hXlt hc_lt
        (show 8 * K + 4 * Lw ≤ 4 * Z by omega)))
      push_cast at hf ⊢
      exact hf
    have hU1 : Num.unsignedVal m10 (q4 + Z + Z) 4 Z = X * 2 ^ c := by
      apply Num.unsignedVal_of_intVal_nonneg hval10'
      rw [Num.intVal_congr (mem' := m9) (a' := q4 + Z + Z) hag10, hsh9']
    have hY9 : Num.unsignedVal m9 (q4 + Z) 4 Z = Y := by
      rw [hY9u, bucket_unsignedVal_of_agree (m := m4) (fun i hi => hf7 _ (by omega)), hYu]
    have hY9i : Num.intVal m9 (q4 + Z) 4 Z = (Y : ℤ) := by
      rw [bucket_intVal_of_small, hY9]
      rw [hY9]
      exact bucket_two_mul_lt (by rw [bucket_capacity_four]; omega) (show Lw < Z by omega)
    have hU2 : Num.unsignedVal m10 (q4 + Z + Z + Z) 4 Z = Y * 2 ^ a := by
      apply Num.unsignedVal_of_intVal_nonneg hval10
      rw [hsh10, hY9i]
      have hf := Num.wrap_of_fits (bucket_fits_of_lt (bucket_shift_lt hYlt ha_lt
        (show 4 * Lw + 8 * K ≤ 4 * Z by omega)))
      push_cast at hf ⊢
      exact hf
    rw [hlt, hU1, hU2]
  have hfix : Num.fixVal mem lenA 4 L P = (Num.intVal mem lenA 4 L : ℝ) / 2 ^ P := rfl
  have hmem : ∀ x < heap, m10 x = mem x := fun x hx => by
    rw [hf10 x (by omega), hf9 x (by omega), hf8 x (by omega), hf7 x (by omega), hag4 x hx]
  have hzero : ZeroFrom m10 (heap + bucketWordSpace Lw L) := by
    unfold bucketWordSpace
    rw [show heap + (5 * Lw + 16 * (Lw + L + 1) + 4) = q4 + Z + Z + Z + Z by omega]
    exact hz10
  -- 13. return the code when `0 < t`, and `0` otherwise
  refine runs_cond_le (v := t) (by eval_expr) ?_ ?_
  · intro ht0
    refine runs_ret_le (by eval_expr) ?_ ?_
    · refine ⟨hmem, hzero, ?_⟩
      change _ = bucketCode (bucketOf ((Num.intVal mem numA 4 Lw : ℝ) /
        (Num.intVal mem denA 4 Lw : ℝ) * Num.fixVal mem lenA 4 L P))
      subst hXd hYd
      rw [hfix, bucketCode_bucketOf_eq hd0 hl0 ht_iff ha_eq hc_eq (hlt_eq (by omega))]
      simp [Nat.pos_of_ne_zero ht0, Outcome.value]
    · simp only [bucketWordContract, bucketWordCost, Num.absoluteContract,
        Num.extendCopyContract, Num.multiplyContract, Num.effectiveLengthContract,
        Num.shiftLeftContract, Num.unsignedLessContract, heapContract, List.getD_cons_zero,
        List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
        argsSize_cons, argsSize_nil]
      subst hZ hK
      omega
  · intro ht0
    refine runs_ret_le (by eval_expr) ?_ ?_
    · refine ⟨hmem, hzero, ?_⟩
      change _ = bucketCode (bucketOf ((Num.intVal mem numA 4 Lw : ℝ) /
        (Num.intVal mem denA 4 Lw : ℝ) * Num.fixVal mem lenA 4 L P))
      subst hXd hYd
      rw [ht0] at ht_iff
      rw [hfix, bucketCode_bucketOf_eq (t := 0) (a := 0) hd0 hl0 ht_iff (by omega) hc_eq rfl]
      simp [Outcome.value]
    · simp only [bucketWordContract, bucketWordCost, Num.absoluteContract,
        Num.extendCopyContract, Num.multiplyContract, Num.effectiveLengthContract,
        Num.shiftLeftContract, Num.unsignedLessContract, heapContract, List.getD_cons_zero,
        List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
        argsSize_cons, argsSize_nil]
      subst hZ hK
      omega

/-! ## The word of an edge of the graph -/

/-- The length of an edge of the graph is a valid positive block (`BranchLengthsAt`). -/
theorem branchLengthsAt_intVal_pos {mem : ℕ → ℕ} {lengths eCap L P h e : ℕ} {G : MGraph}
    {ℓ₀ : ℕ → ℝ} (hlen : BranchLengthsAt mem lengths eCap L P h G ℓ₀) (he : e ∈ G.E) :
    Num.Valid mem (lengths + e * L) 4 L ∧ 0 < Num.intVal mem (lengths + e * L) 4 L := by
  obtain ⟨-, hAt, -⟩ := hlen
  obtain ⟨-, hv, hpos⟩ := hAt e he
  refine ⟨hv, ?_⟩
  simp only [MinRatio.readEdgeValues, he, ↓reduceIte, Num.fixVal] at hpos
  have h2 : (0 : ℝ) < 2 ^ P := by positivity
  have h3 : (0 : ℝ) < Num.intVal mem (lengths + e * L) 4 L := by
    rwa [div_pos_iff_of_pos_right h2] at hpos
  exact_mod_cast h3

/-- **The word of an edge of the graph.** On the blocks of P4's export (`num e`, `den e` with
`num e / den e = wstr e`) and of the lengths, the word of `bucketWordContract` is
`bucketCode (bucketOf (wstr e · ℓ₀ e))`, the word that `AsmSdMapsAt` asks. -/
theorem bucketWord_edge {mem : ℕ → ℕ} {numA denA Lw lengths eCap L P h e : ℕ} {G : MGraph}
    {ℓ₀ wstr : ℕ → ℝ} {num den : ℕ → ℤ}
    (hlen : BranchLengthsAt mem lengths eCap L P h G ℓ₀) (he : e ∈ G.E)
    (hnum : Num.intVal mem numA 4 Lw = num e) (hden : Num.intVal mem denA 4 Lw = den e)
    (hw : (num e : ℝ) / (den e : ℝ) = wstr e) :
    bucketCode (bucketOf ((Num.intVal mem numA 4 Lw : ℝ) / (Num.intVal mem denA 4 Lw : ℝ) *
      Num.fixVal mem (lengths + e * L) 4 L P)) = bucketCode (bucketOf (wstr e * ℓ₀ e)) := by
  rw [hnum, hden, hw, hlen.2.2]
  simp [MinRatio.readEdgeValues, he]

end MinCostFlow.SparseCore.Program
