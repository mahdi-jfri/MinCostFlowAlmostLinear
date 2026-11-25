module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layout
public import WordRAM.Module
public import WordRAM.Std.Limbs
public import MinCostFlow.NarrowProg.AccAdd
public import MinCostFlow.NarrowProg.AccNormalize
public import MinCostFlow.NarrowProg.Stage0Defs
public import MinCostFlow.NarrowProg.Stage0CheckHelpers
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Limb helpers for Stage 0 shift and Stage 3 answer assembly

Provides the reusable multi-limb primitives and straight-line per-item helpers:
- `padLimbs`, `free_to_prod_replicate`, `canonical_eq_digits`, `limbs_eq_padLimbs_digits`;
- `padCopy`: copies `len ≤ L` limbs and zero-pads to length `L` in `O(L + 1)` steps;
- `canonLen`: strips trailing zero limbs from an `L`-limb array in `O(L + 1)` steps;
- `accAddLimbs`: unshifted limb-by-limb addition into an `L`-limb lazy accumulator in `O(len + 1)`;
- `stage0ShiftOneCap`: computes `(upper - lower).toNat` for `lower ≤ upper` in `O(L + 1)` steps;
- `stage0ShiftOneDem`: normalizes a `(pos, neg)` lazy accumulator pair and writes the signed
  canonical difference `pos - neg` in `O(L + 1)` steps.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std

namespace MinCostFlow.NarrowProg

/-! ### Free-block splitting, padded limbs, and canonical trimming -/

/-- Split a free block of `cnt * L` zeroed cells into a product of `cnt` blocks of `L` zeros. -/
theorem free_to_prod_replicate (p cnt L : ℕ) :
    Assn.free p (cnt * L) =
      ∏ c ∈ Finset.range cnt, Assn.list (p + c * L) (List.replicate L 0) := by
  induction cnt with
  | zero =>
    simp only [Nat.zero_mul, Assn.free_zero, Finset.range_zero, Finset.prod_empty]
  | succ c ih =>
    have hsplit : (c + 1) * L = c * L + L := by ring
    rw [hsplit, Assn.free_add', Finset.prod_range_succ, ih]
    rfl

/-- Right-pad a list of limbs with zeros to length `L`. -/
def padLimbs (xs : List ℕ) (L : ℕ) : List ℕ :=
  xs ++ List.replicate (L - xs.length) 0

@[sep_len] theorem length_padLimbs {xs : List ℕ} {L : ℕ} (h : xs.length ≤ L) :
    (padLimbs xs L).length = L := by
  simp only [padLimbs, List.length_append, List.length_replicate]; omega

theorem ofDigits_replicate_zero (B n : ℕ) :
    Nat.ofDigits B (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, Nat.ofDigits_cons, ih]

theorem ofDigits_padLimbs (B : ℕ) (xs : List ℕ) (L : ℕ) :
    Nat.ofDigits B (padLimbs xs L) = Nat.ofDigits B xs := by
  simp [padLimbs]

theorem limbs_padLimbs {k : ℕ} {xs : List ℕ} (hx : Limbs k xs) (L : ℕ) :
    Limbs k (padLimbs xs L) := by
  intro x hm
  rcases List.mem_append.mp hm with h1 | h2
  · exact hx x h1
  · rw [List.eq_of_mem_replicate h2]; exact Nat.two_pow_pos k

/-- Every canonical base-`2 ^ k` limb list equals `Nat.digits (2 ^ k)` of its value. -/
theorem canonical_eq_digits {k : ℕ} (hk : 1 ≤ k) {ys : List ℕ} (hc : CanonicalLimbs k ys) :
    ys = Nat.digits (2 ^ k) (Nat.ofDigits (2 ^ k) ys) := by
  have hb : 1 < 2 ^ k := by have := two_le_pow hk; omega
  exact (Nat.digits_ofDigits (2 ^ k) hb ys (fun l hl => hc.1 l hl) hc.2).symm

/-- If `xs` has limbs `< 2 ^ k`, trailing zeros from `len` onward, and either `len = 0` or
`xs[len - 1] ≠ 0`, then `len` is the canonical digit length and `xs` is `padLimbs` of
`Nat.digits (2 ^ k) (Nat.ofDigits (2 ^ k) xs)`. -/
theorem limbs_eq_padLimbs_digits {k : ℕ} (hk : 1 ≤ k) {xs : List ℕ} (hL : Limbs k xs)
    {len : ℕ} (hlen : len ≤ xs.length)
    (hdrop : xs.drop len = List.replicate (xs.length - len) 0)
    (hlast : len = 0 ∨ ∃ h : len - 1 < xs.length, xs[len - 1]'h ≠ 0) :
    len = (Nat.digits (2 ^ k) (Nat.ofDigits (2 ^ k) xs)).length ∧
    xs = padLimbs (Nat.digits (2 ^ k) (Nat.ofDigits (2 ^ k) xs)) xs.length := by
  have hval : Nat.ofDigits (2 ^ k) (xs.take len) = Nat.ofDigits (2 ^ k) xs := by
    have hsp : xs = xs.take len ++ xs.drop len := (List.take_append_drop len xs).symm
    conv_rhs => rw [hsp, hdrop, Nat.ofDigits_append, ofDigits_replicate_zero,
      Nat.mul_zero, Nat.add_zero]
  have hcan : CanonicalLimbs k (xs.take len) := by
    refine ⟨fun x hx => hL x (List.mem_of_mem_take hx), fun hne => ?_⟩
    have hlen_pos : 0 < len := by
      rcases Nat.eq_zero_or_pos len with rfl | hp
      · simp at hne
      · exact hp
    rcases hlast with rfl | ⟨hidx, hnz⟩
    · omega
    · have htl : (xs.take len).length = len := by simp [hlen]
      rw [List.getLast_eq_getElem]
      have hget : (xs.take len)[(xs.take len).length - 1]'(by omega) = xs[len - 1]'hidx := by
        simp [List.getElem_take, htl]
      rw [hget]; exact hnz
  have hdig : xs.take len = Nat.digits (2 ^ k) (Nat.ofDigits (2 ^ k) xs) := by
    rw [← hval]
    exact canonical_eq_digits hk hcan
  have hlen_eq : len = (Nat.digits (2 ^ k) (Nat.ofDigits (2 ^ k) xs)).length := by
    rw [← hdig, List.length_take, Nat.min_eq_left hlen]
  refine ⟨hlen_eq, ?_⟩
  unfold padLimbs
  rw [← hlen_eq, ← hdig, ← hdrop, List.take_append_drop]

/-- Unshifted limb-by-limb addition of `ys` into `xs` (same length as `xs`). -/
def accAddList (xs ys : List ℕ) : List ℕ :=
  List.ofFn fun i : Fin xs.length => xs[i] + ys.getD i.val 0

@[sep_len] theorem length_accAddList (xs ys : List ℕ) :
    (accAddList xs ys).length = xs.length := by
  simp [accAddList]

theorem getElem_accAddList (xs ys : List ℕ) {i : ℕ} (hi : i < xs.length) :
    (accAddList xs ys)[i]'(by simp [accAddList, hi]) = xs[i]'hi + ys.getD i 0 := by
  simp [accAddList]

private theorem accAddList_step (xs ys : List ℕ) {i : ℕ} (hi : i < ys.length) (hxl : ys.length ≤ xs.length) :
    (List.ofFn fun j : Fin xs.length =>
      xs[j] + if j.val < i then ys.getD j.val 0 else 0).set i
        ((List.ofFn fun j : Fin xs.length =>
          xs[j] + if j.val < i then ys.getD j.val 0 else 0)[i]'(by simp; omega) + ys[i]'hi) =
      List.ofFn fun j : Fin xs.length =>
        xs[j] + if j.val < i + 1 then ys.getD j.val 0 else 0 := by
  apply List.ext_getElem
  · simp
  · intro j hj1 hj2
    have hjl : j < xs.length := by simpa using hj2
    by_cases hji : j = i
    · subst hji
      simp [List.getD_eq_getElem?_getD, hi]
    · simp only [List.getElem_set_ne (Ne.symm hji), List.getElem_ofFn]
      have hiff : (j < i + 1) ↔ (j < i) := by omega
      simp [hiff]

theorem ofDigits_accAddList (B : ℕ) {xs ys : List ℕ} (hlen : ys.length ≤ xs.length) :
    Nat.ofDigits B (accAddList xs ys) = Nat.ofDigits B xs + Nat.ofDigits B ys := by
  have haux : ∀ k ≤ ys.length,
      Nat.ofDigits B (List.ofFn fun j : Fin xs.length =>
        xs[j] + if j.val < k then ys.getD j.val 0 else 0) =
      Nat.ofDigits B xs + Nat.ofDigits B (ys.take k) := by
    intro k
    induction k with
    | zero =>
      intro _
      have heq : (List.ofFn fun j : Fin xs.length =>
          xs[j] + if j.val < 0 then ys.getD j.val 0 else 0) = xs := by
        apply List.ext_getElem <;> simp
      rw [heq]; simp
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      set cur := List.ofFn fun j : Fin xs.length =>
        xs[j] + if j.val < k then ys.getD j.val 0 else 0
      have hstep := accAddList_step xs ys (i := k) (by omega) hlen
      have hcur_get : cur.getD k 0 = cur[k]'(by simp [cur]; omega) :=
        List.getD_eq_getElem _ _ (by simp [cur]; omega)
      have hset : Nat.ofDigits B (cur.set k (cur[k]'(by simp [cur]; omega) + ys[k]'(by omega))) =
          Nat.ofDigits B cur + B ^ k * ys[k]'(by omega) := by
        rw [← hcur_get]
        exact ofDigits_set_add B cur (by simp [cur]; omega) (ys[k]'(by omega))
      rw [← hstep, hset, hprev, ofDigits_take_succ B (by omega), List.getD_eq_getElem _ _ (by omega)]
      ring
  have hfull := haux ys.length le_rfl
  rw [List.take_length] at hfull
  have heq : (List.ofFn fun j : Fin xs.length =>
      xs[j] + if j.val < ys.length then ys.getD j.val 0 else 0) = accAddList xs ys := by
    apply List.ext_getElem
    · simp [accAddList]
    · intro j hj1 hj2
      simp only [List.getElem_ofFn, accAddList]
      by_cases h : j < ys.length
      · simp [h]
      · simp [h]
  rwa [heq] at hfull

/-! ### `padCopy`: copy `len ≤ L` limbs and zero-pad to `L` -/

wram_def padCopy (pSrc, len, pDst, L) {
  for i in 0 .. len {
    mem[pDst + i] := mem[pSrc + i]
  }
  rem := L - len
  for j in 0 .. rem {
    mem[pDst + len + j] := 0
  }
  return 0
}

def padCopySpec : Spec (List ℕ × List ℕ) where
  pre := fun (xs, dst) args => ⨆ (pSrc : ℕ) (pDst : ℕ),
    ⌜args = [pSrc, xs.length, pDst, dst.length] ∧ xs.length ≤ dst.length⌝ *
    Assn.list pSrc xs * Assn.list pDst dst
  post := fun (xs, dst) args v => ⨆ (pSrc : ℕ) (pDst : ℕ),
    ⌜args = [pSrc, xs.length, pDst, dst.length] ∧ v = 0⌝ *
    Assn.list pSrc xs * Assn.list pDst (padLimbs xs dst.length)

theorem padCopy_meets {w : ℕ} {p : Program} {f : ℕ} (hw : 1 < 2 ^ w)
    (hp : p.procs[f]? = some padCopy) :
    Meets w p f (padCopySpec.withCost fun x _ => 55 * x.2.length + 35) := by
  sep_enter ⟨xs, dst⟩ with hle
  sep_for (fun i => ⟨[pSrc, xs.length, pDst, dst.length, i, 0, 0],
      i ≤ xs.length, 40 * (xs.length - i) + 45 * (dst.length - xs.length) + 25,
      [Assn.list pSrc xs, Assn.list pDst (xs.take i ++ dst.drop i)]⟩)
  · have hlen : (xs.take i ++ dst.drop i).length = dst.length := by
      simp [List.length_take, Nat.min_eq_left (by omega : i ≤ xs.length)]; omega
    sep_run
    rw [List.set_append_right _ _ (by simp)]
    have htl : (xs.take i).length = i := by simp; omega
    rw [htl, Nat.sub_self, List.drop_eq_getElem_cons (by omega : i < dst.length),
      List.set_cons_zero, List.take_add_one, List.getElem?_eq_getElem hhi, Option.toList_some]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · have htl : xs.take xs.length ++ dst.drop xs.length =
        xs ++ List.replicate 0 0 ++ dst.drop (xs.length + 0) := by simp
    sep_apply (show Assn.list pDst _ = Assn.list pDst _ from congrArg (Assn.list pDst) htl)
    sep_step
    sep_for (fun j => ⟨[pSrc, xs.length, pDst, dst.length, xs.length, dst.length - xs.length, j],
        j ≤ dst.length - xs.length, 35 * (dst.length - xs.length - j) + 10,
        [Assn.list pSrc xs,
          Assn.list pDst (xs ++ List.replicate j 0 ++ dst.drop (xs.length + j))]⟩)
    · have hlen : (xs ++ List.replicate j 0 ++ dst.drop (xs.length + j)).length = dst.length := by
        simp; omega
      sep_run
      rw [List.set_append_right _ _ (by simp)]
      have hpl : (xs ++ List.replicate j 0).length = xs.length + j := by simp
      rw [hpl, Nat.sub_self, List.drop_eq_getElem_cons (by omega : xs.length + j < dst.length),
        List.set_cons_zero, List.replicate_succ']
      simp only [List.append_assoc, List.cons_append, List.nil_append,
        show xs.length + j + 1 = xs.length + (j + 1) by omega]
    · have hfin : xs ++ List.replicate (dst.length - xs.length) 0 ++
          dst.drop (xs.length + (dst.length - xs.length)) = padLimbs xs dst.length := by
        rw [List.drop_of_length_le (by omega), List.append_nil]; rfl
      sep_apply (show Assn.list pDst _ = Assn.list pDst _ from congrArg (Assn.list pDst) hfin)
      sep_step

/-! ### `canonLen`: strip trailing zero limbs -/

wram_def canonLen (pa, L) {
  len := L
  while len {
    len := len - 1
    x := mem[pa + len]
    if 0 < x {
      return len + 1
    }
  }
  return 0
}

def canonLenSpec : Spec (ℕ × List ℕ) where
  pre := fun (k, xs) args => ⨆ pa : ℕ,
    ⌜args = [pa, xs.length] ∧ 1 ≤ k ∧ Limbs k xs⌝ *
    Assn.list pa xs
  post := fun (k, xs) args v => ⨆ pa : ℕ,
    ⌜args = [pa, xs.length] ∧
      v = (Nat.digits (2 ^ k) (Nat.ofDigits (2 ^ k) xs)).length ∧
      xs = padLimbs (Nat.digits (2 ^ k) (Nat.ofDigits (2 ^ k) xs)) xs.length⌝ *
    Assn.list pa xs

theorem canonLen_meets {w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some canonLen) :
    Meets w p f (canonLenSpec.withCost fun x _ => 45 * x.2.length + 25) := by
  sep_enter ⟨k, xs⟩ with hk hL
  sep_step
  sep_while (fun (t : ℕ × ℕ) => (⟨[pa, xs.length, t.1, t.2],
      t.1 ≤ xs.length ∧ xs.drop t.1 = List.replicate (xs.length - t.1) 0,
      40 * t.1 + 10, [Assn.list pa xs]⟩ : SInv))
    (fun t => t.1) from (xs.length, 0) with ⟨len, x⟩
  · have hpos : 0 < len := by omega
    have hidx : len - 1 < xs.length := by omega
    sep_step; sep_step; sep_step
    · have hres := limbs_eq_padLimbs_digits hk hL (by omega) hinv_1 (Or.inr ⟨hidx, by omega⟩)
      have hsub_add : len - 1 + 1 = len := by omega
      sep_step
      exact hres.2
    · have hzero : xs[len - 1]'hidx = 0 := by omega
      have hdrop_prev : xs.drop (len - 1) = List.replicate (xs.length - (len - 1)) 0 := by
        rw [List.drop_eq_getElem_cons hidx, hzero]
        have hsub : len - 1 + 1 = len := by omega
        have hsub2 : xs.length - (len - 1) = (xs.length - len) + 1 := by omega
        rw [hsub, hinv_1, hsub2, List.replicate_succ]
      sep_run
  · have hres := limbs_eq_padLimbs_digits hk hL (by omega) hinv_1 (Or.inl (by omega))
    sep_step
    exact hres.2

/-! ### `accAddLimbs`: unshifted limb-by-limb addition -/

wram_def accAddLimbs (pAcc, pSrc, len) {
  for j in 0 .. len {
    mem[pAcc + j] := mem[pAcc + j] + mem[pSrc + j]
  }
  return 0
}

def accAddLimbsSpec (w : ℕ) : Spec (List ℕ × List ℕ) where
  pre := fun (xs, ys) args => ⨆ (pAcc : ℕ) (pSrc : ℕ),
    ⌜args = [pAcc, pSrc, ys.length] ∧ ys.length ≤ xs.length ∧
      ∀ j, j < ys.length → xs.getD j 0 + ys.getD j 0 < 2 ^ w⌝ *
    Assn.list pAcc xs * Assn.list pSrc ys
  post := fun (xs, ys) args v => ⨆ (pAcc : ℕ) (pSrc : ℕ),
    ⌜args = [pAcc, pSrc, ys.length] ∧ v = 0⌝ *
    Assn.list pAcc (accAddList xs ys) * Assn.list pSrc ys

theorem accAddLimbs_meets {w : ℕ} {p : Program} {f : ℕ} (hw : 1 < 2 ^ w)
    (hp : p.procs[f]? = some accAddLimbs) :
    Meets w p f ((accAddLimbsSpec w).withCost fun x _ => 55 * x.2.length + 30) := by
  sep_enter ⟨xs, ys⟩ with hlen hfit
  sep_for (fun j => ⟨[pAcc, pSrc, ys.length, j], j ≤ ys.length, 40 * (ys.length - j) + 10,
      [Assn.list pAcc (List.ofFn fun t : Fin xs.length =>
          xs[t] + if t.val < j then ys.getD t.val 0 else 0),
        Assn.list pSrc ys]⟩)
  · have hfit_j := hfit j hhi
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hhi] at hfit_j
    have hlen_cur : (List.ofFn fun t : Fin xs.length =>
        xs[t] + if t.val < j then ys.getD t.val 0 else 0).length = xs.length := List.length_ofFn
    have hcur_j : (List.ofFn fun t : Fin xs.length =>
        xs[t] + if t.val < j then ys.getD t.val 0 else 0)[j]'(by omega) = xs[j]'(by omega) := by
      simp
    sep_run
    exact accAddList_step xs ys hhi hlen
  · have heq : (List.ofFn fun t : Fin xs.length =>
        xs[t] + if t.val < ys.length then ys.getD t.val 0 else 0) = accAddList xs ys := by
      apply List.ext_getElem
      · simp [accAddList]
      · intro j hj1 hj2
        simp only [List.getElem_ofFn, accAddList]
        by_cases h : j < ys.length
        · simp [h]
        · simp [h]
    sep_apply (show Assn.list pAcc _ = Assn.list pAcc _ from congrArg (Assn.list pAcc) heq)
    sep_step

/-! ### `stage0ShiftOneCap`: shifted capacity `(upper - lower).toNat` for one edge -/

wram_def stage0ShiftOneCap (padCopy limbsAdd limbsSub canonLen : ℕ)
    (pLoPtr, loSign, loLen, pHiPtr, hiSign, hiLen, pDst, pTmpA, pTmpB, L, k) {
  d := padCopy(pLoPtr, loLen, pTmpA, L)
  d := padCopy(pHiPtr, hiLen, pTmpB, L)
  if loSign == 0 {
    d := limbsSub(pTmpB, pTmpA, pDst, L, k)
  } else {
    if hiSign == 0 {
      d := limbsAdd(pTmpB, pTmpA, pDst, L, k)
    } else {
      d := limbsSub(pTmpA, pTmpB, pDst, L, k)
    }
  }
  len := canonLen(pDst, L)
  return len
}

structure ShiftOneCapData where
  k : ℕ
  L : ℕ
  lo : ℤ
  hi : ℤ
  dst0 : List ℕ
  tmpA0 : List ℕ
  tmpB0 : List ℕ

def stage0ShiftOneCapSpec (w : ℕ) : Spec ShiftOneCapData where
  pre := fun d args => ⨆ (pLoPtr : ℕ) (pHiPtr : ℕ) (pDst : ℕ) (pTmpA : ℕ) (pTmpB : ℕ),
    let loDig := Nat.digits (2 ^ d.k) d.lo.natAbs
    let hiDig := Nat.digits (2 ^ d.k) d.hi.natAbs
    ⌜args = [pLoPtr, (if d.lo < 0 then 1 else 0), loDig.length,
        pHiPtr, (if d.hi < 0 then 1 else 0), hiDig.length,
        pDst, pTmpA, pTmpB, d.L, d.k] ∧
      3 ≤ d.k ∧ 2 * d.k ≤ w ∧ d.lo ≤ d.hi ∧
      loDig.length < d.L ∧ hiDig.length < d.L ∧
      d.dst0.length = d.L ∧ d.tmpA0.length = d.L ∧ d.tmpB0.length = d.L⌝ *
    Assn.list pLoPtr loDig * Assn.list pHiPtr hiDig *
    Assn.list pDst d.dst0 * Assn.list pTmpA d.tmpA0 * Assn.list pTmpB d.tmpB0
  post := fun d args v => ⨆ (pLoPtr : ℕ) (pHiPtr : ℕ) (pDst : ℕ) (pTmpA : ℕ) (pTmpB : ℕ)
      (tmpA1 : List ℕ) (tmpB1 : List ℕ),
    let loDig := Nat.digits (2 ^ d.k) d.lo.natAbs
    let hiDig := Nat.digits (2 ^ d.k) d.hi.natAbs
    let capDig := Nat.digits (2 ^ d.k) (d.hi - d.lo).toNat
    ⌜args = [pLoPtr, (if d.lo < 0 then 1 else 0), loDig.length,
        pHiPtr, (if d.hi < 0 then 1 else 0), hiDig.length,
        pDst, pTmpA, pTmpB, d.L, d.k] ∧
      v = capDig.length ∧ tmpA1.length = d.L ∧ tmpB1.length = d.L⌝ *
    Assn.list pLoPtr loDig * Assn.list pHiPtr hiDig *
    Assn.list pDst (padLimbs capDig d.L) * Assn.list pTmpA tmpA1 * Assn.list pTmpB tmpB1

private theorem subBorrow_eq_zero_of_le {k : ℕ} (hk : 1 ≤ k) {xs ys : List ℕ}
    (hx : Limbs k xs) (hy : Limbs k ys) (hl : ys.length = xs.length)
    (hle : Nat.ofDigits (2 ^ k) ys ≤ Nat.ofDigits (2 ^ k) xs) :
    subBorrow k xs ys = 0 ∧
    Nat.ofDigits (2 ^ k) (subLimbs k xs ys) = Nat.ofDigits (2 ^ k) xs - Nat.ofDigits (2 ^ k) ys := by
  obtain ⟨hsub, _, hLsub⟩ := subRun_spec hk hx hy hl xs.length le_rfl
  rw [List.take_length, List.take_of_length_le (by omega)] at hsub
  change Nat.ofDigits (2 ^ k) (subLimbs k xs ys) + Nat.ofDigits (2 ^ k) ys =
    Nat.ofDigits (2 ^ k) xs + subBorrow k xs ys * (2 ^ k) ^ xs.length at hsub
  have hlt : Nat.ofDigits (2 ^ k) (subLimbs k xs ys) < (2 ^ k) ^ xs.length := by
    change Limbs k (subLimbs k xs ys) at hLsub
    have h2 := two_le_pow hk
    have h := Nat.ofDigits_lt_base_pow_length (b := 2 ^ k) (by omega) hLsub
    have hls : (subLimbs k xs ys).length = xs.length := by simp [subLimbs, length_carryRun]
    rwa [hls] at h
  have hb0 : subBorrow k xs ys = 0 := by
    by_contra hne
    have h1 : 1 * (2 ^ k) ^ xs.length ≤ subBorrow k xs ys * (2 ^ k) ^ xs.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  rw [hb0, Nat.zero_mul, Nat.add_zero] at hsub
  exact ⟨hb0, by omega⟩

private theorem addCarry_eq_zero_of_lt {k : ℕ} (hk : 1 ≤ k) {xs ys : List ℕ}
    (hx : Limbs k xs) (hy : Limbs k ys) (hl : ys.length = xs.length)
    (hfit : Nat.ofDigits (2 ^ k) xs + Nat.ofDigits (2 ^ k) ys < (2 ^ k) ^ xs.length) :
    addCarry k xs ys = 0 ∧
    Nat.ofDigits (2 ^ k) (addLimbs k xs ys) = Nat.ofDigits (2 ^ k) xs + Nat.ofDigits (2 ^ k) ys := by
  obtain ⟨hadd, _, _⟩ := addRun_spec hk hx hy hl xs.length le_rfl
  rw [List.take_length, List.take_of_length_le (by omega)] at hadd
  change Nat.ofDigits (2 ^ k) (addLimbs k xs ys) + addCarry k xs ys * (2 ^ k) ^ xs.length =
    Nat.ofDigits (2 ^ k) xs + Nat.ofDigits (2 ^ k) ys at hadd
  have hc0 : addCarry k xs ys = 0 := by
    by_contra hne
    have h1 : 1 * (2 ^ k) ^ xs.length ≤ addCarry k xs ys * (2 ^ k) ^ xs.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  rw [hc0, Nat.zero_mul, Nat.add_zero] at hadd
  exact ⟨hc0, hadd⟩

theorem stage0ShiftOneCap_meets {w : ℕ} {p : Program} {f pCopy lAdd lSub cLen : ℕ}
    {Tpad Tadd Tsub Tcan : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ShiftOneCap pCopy lAdd lSub cLen))
    (hpad : Meets w p pCopy (padCopySpec.withCost fun x _ => Tpad x.2.length))
    (hadd : Meets w p lAdd ((limbsAddSpec w).withCost fun x _ => Tadd x.2.1.length))
    (hsub : Meets w p lSub ((limbsSubSpec w).withCost fun x _ => Tsub x.2.1.length))
    (hcan : Meets w p cLen (canonLenSpec.withCost fun x _ => Tcan x.2.length)) :
    Meets w p f ((stage0ShiftOneCapSpec w).withCost fun d _ =>
      2 * Tpad d.L + Tadd d.L + Tsub d.L + Tcan d.L + 80) := by
  sep_enter d with hk3 h2k hle hloLt hhiLt hdstL htmpAL htmpBL
  have hk1 : 1 ≤ d.k := by omega
  have hloDigL : Limbs d.k (Nat.digits (2 ^ d.k) d.lo.natAbs) := digits_limbs hk1 _
  have hhiDigL : Limbs d.k (Nat.digits (2 ^ d.k) d.hi.natAbs) := digits_limbs hk1 _
  have hpadA_len : (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L).length = d.L :=
    length_padLimbs (by omega)
  have hpadB_len : (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L).length = d.L :=
    length_padLimbs (by omega)
  have hpadA_val : Nat.ofDigits (2 ^ d.k) (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L) =
      d.lo.natAbs := by rw [ofDigits_padLimbs, Nat.ofDigits_digits]
  have hpadB_val : Nat.ofDigits (2 ^ d.k) (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L) =
      d.hi.natAbs := by rw [ofDigits_padLimbs, Nat.ofDigits_digits]
  have hpadA_L : Limbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L) :=
    limbs_padLimbs hloDigL d.L
  have hpadB_L : Limbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L) :=
    limbs_padLimbs hhiDigL d.L
  have h2k_ge : 8 ≤ 2 ^ d.k := by
    calc 8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ d.k := Nat.pow_le_pow_right (by norm_num) hk3
  -- Call 1: padCopy lo -> tmpA
  generalize hF1 :
    (Assn.list pHiPtr (Nat.digits (2 ^ d.k) d.hi.natAbs) *
     Assn.list pDst d.dst0 * Assn.list pTmpB d.tmpB0) = F1
  sep_apply hF1
  sep_step from (Nat.digits (2 ^ d.k) d.lo.natAbs, d.tmpA0)
  subst F1; sep_norm
  -- Call 2: padCopy hi -> tmpB
  generalize hF2 :
    (Assn.list pLoPtr (Nat.digits (2 ^ d.k) d.lo.natAbs) *
     Assn.list pDst d.dst0 * Assn.list pTmpA (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L)) = F2
  sep_apply hF2
  sep_step from (Nat.digits (2 ^ d.k) d.hi.natAbs, d.tmpB0)
  subst F2; sep_norm
  -- Case split on loSign == 0
  sep_step
  · -- loSign = 0 => lo ≥ 0 => hi ≥ lo ≥ 0 => hi - lo = hi.natAbs - lo.natAbs
    have hlo_nn : 0 ≤ d.lo := by split_ifs at hcond with h; omega
    have hhi_nn : 0 ≤ d.hi := by omega
    have hle_abs : d.lo.natAbs ≤ d.hi.natAbs := by omega
    have hcap_eq : (d.hi - d.lo).toNat = d.hi.natAbs - d.lo.natAbs := by omega
    generalize hF3 :
      (Assn.list pLoPtr (Nat.digits (2 ^ d.k) d.lo.natAbs) *
       Assn.list pHiPtr (Nat.digits (2 ^ d.k) d.hi.natAbs)) = F3
    sep_apply hF3
    sep_step from (d.k, padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L,
        padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L, d.dst0) with _ _ hsubL _
    subst F3; sep_norm
    have hval := (subBorrow_eq_zero_of_le hk1 hpadB_L hpadA_L (by omega)
      (by rw [hpadA_val, hpadB_val]; exact hle_abs)).2
    rw [hpadA_val, hpadB_val, ← hcap_eq] at hval
    have hsub_len : (subLimbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L)
        (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L)).length = d.L := by
      simp [subLimbs, length_carryRun, hpadB_len]
    generalize hF4 :
      (Assn.list pLoPtr (Nat.digits (2 ^ d.k) d.lo.natAbs) *
       Assn.list pHiPtr (Nat.digits (2 ^ d.k) d.hi.natAbs) *
       Assn.list pTmpA (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L) *
       Assn.list pTmpB (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L)) = F4
    sep_apply hF4
    sep_step from (d.k, subLimbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L)
        (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L)) with _ hpad_eq
    subst F4; sep_norm
    rw [hval] at hlen hpad_eq
    rw [hsub_len] at hpad_eq
    sep_apply (show Assn.list pDst (subLimbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L)
        (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L)) =
      Assn.list pDst (padLimbs (Nat.digits (2 ^ d.k) (d.hi - d.lo).toNat) d.L) by rw [hpad_eq])
    sep_step
    · rw [htmpAL, htmpBL, hpadB_len, hsub_len]; omega
  · -- loSign ≠ 0 => lo < 0
    have hlo_neg : d.lo < 0 := by split_ifs at hcond with h <;> omega
    sep_step
    · -- hiSign = 0 => hi ≥ 0 => hi - lo = hi.natAbs + lo.natAbs
      have hhi_nn : 0 ≤ d.hi := by split_ifs at hcond_1 with h; omega
      have hcap_eq : (d.hi - d.lo).toNat = d.hi.natAbs + d.lo.natAbs := by omega
      have hlo_lt : d.lo.natAbs < (2 ^ d.k) ^ (d.L - 1) := by
        have h1 := ofDigits_lt_pow_length hk1 hloDigL
        rw [Nat.ofDigits_digits] at h1
        exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))
      have hhi_lt : d.hi.natAbs < (2 ^ d.k) ^ (d.L - 1) := by
        have h1 := ofDigits_lt_pow_length hk1 hhiDigL
        rw [Nat.ofDigits_digits] at h1
        exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))
      have hsum_lt : d.hi.natAbs + d.lo.natAbs < (2 ^ d.k) ^ d.L := by
        have hpow : (2 ^ d.k) ^ d.L = (2 ^ d.k) ^ (d.L - 1) * 2 ^ d.k := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        rw [hpow]; nlinarith
      generalize hF3 :
        (Assn.list pLoPtr (Nat.digits (2 ^ d.k) d.lo.natAbs) *
         Assn.list pHiPtr (Nat.digits (2 ^ d.k) d.hi.natAbs)) = F3
      sep_apply hF3
      sep_step from (d.k, padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L,
          padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L, d.dst0) with _ _ haddL _
      subst F3; sep_norm
      have hval := (addCarry_eq_zero_of_lt hk1 hpadB_L hpadA_L (by omega)
        (by rw [hpadA_val, hpadB_val, hpadB_len]; exact hsum_lt)).2
      rw [hpadA_val, hpadB_val, ← hcap_eq] at hval
      have hadd_len : (addLimbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L)
          (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L)).length = d.L := by
        simp [addLimbs, length_carryRun, hpadB_len]
      generalize hF4 :
        (Assn.list pLoPtr (Nat.digits (2 ^ d.k) d.lo.natAbs) *
         Assn.list pHiPtr (Nat.digits (2 ^ d.k) d.hi.natAbs) *
         Assn.list pTmpA (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L) *
         Assn.list pTmpB (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L)) = F4
      sep_apply hF4
      sep_step from (d.k, addLimbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L)
          (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L)) with _ hpad_eq
      subst F4; sep_norm
      rw [hval] at hlen hpad_eq
      rw [hadd_len] at hpad_eq
      sep_apply (show Assn.list pDst (addLimbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L)
          (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L)) =
        Assn.list pDst (padLimbs (Nat.digits (2 ^ d.k) (d.hi - d.lo).toNat) d.L) by rw [hpad_eq])
      sep_step
      · rw [htmpAL, htmpBL, hpadB_len, hadd_len]; omega
    · -- hiSign ≠ 0 => lo ≤ hi < 0 => hi - lo = lo.natAbs - hi.natAbs
      have hhi_neg : d.hi < 0 := by split_ifs at hcond_1 with h <;> omega
      have hle_abs : d.hi.natAbs ≤ d.lo.natAbs := by omega
      have hcap_eq : (d.hi - d.lo).toNat = d.lo.natAbs - d.hi.natAbs := by omega
      generalize hF3 :
        (Assn.list pLoPtr (Nat.digits (2 ^ d.k) d.lo.natAbs) *
         Assn.list pHiPtr (Nat.digits (2 ^ d.k) d.hi.natAbs)) = F3
      sep_apply hF3
      sep_step from (d.k, padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L,
          padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L, d.dst0) with _ _ hsubL _
      subst F3; sep_norm
      have hval := (subBorrow_eq_zero_of_le hk1 hpadA_L hpadB_L (by omega)
        (by rw [hpadA_val, hpadB_val]; exact hle_abs)).2
      rw [hpadA_val, hpadB_val, ← hcap_eq] at hval
      have hsub_len : (subLimbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L)
          (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L)).length = d.L := by
        simp [subLimbs, length_carryRun, hpadA_len]
      generalize hF4 :
        (Assn.list pLoPtr (Nat.digits (2 ^ d.k) d.lo.natAbs) *
         Assn.list pHiPtr (Nat.digits (2 ^ d.k) d.hi.natAbs) *
         Assn.list pTmpA (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L) *
         Assn.list pTmpB (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L)) = F4
      sep_apply hF4
      sep_step from (d.k, subLimbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L)
          (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L)) with _ hpad_eq
      subst F4; sep_norm
      rw [hval] at hlen hpad_eq
      rw [hsub_len] at hpad_eq
      sep_apply (show Assn.list pDst (subLimbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.L)
          (padLimbs (Nat.digits (2 ^ d.k) d.hi.natAbs) d.L)) =
        Assn.list pDst (padLimbs (Nat.digits (2 ^ d.k) (d.hi - d.lo).toNat) d.L) by rw [hpad_eq])
      sep_step
      · rw [htmpAL, htmpBL, hpadA_len, hsub_len]; omega

/-! ### `stage0ShiftOneDem`: normalize `(pos, neg)` accumulators and emit signed difference -/

wram_def stage0ShiftOneDem (accNorm lCmp lSub cLen : ℕ)
    (pPos, pNeg, pDst, pSignCell, L, k) {
  d := accNorm(pPos, L, k)
  d := accNorm(pNeg, L, k)
  cmp := lCmp(pPos, pNeg, L)
  if cmp < 1 {
    d := lSub(pNeg, pPos, pDst, L, k)
    mem[pSignCell] := 1
  } else {
    d := lSub(pPos, pNeg, pDst, L, k)
    mem[pSignCell] := 0
  }
  len := cLen(pDst, L)
  return len
}

structure ShiftOneDemData where
  k : ℕ
  pos : List ℕ
  neg : List ℕ
  dst0 : List ℕ
  sign0 : ℕ

def stage0ShiftOneDemSpec (w : ℕ) : Spec ShiftOneDemData where
  pre := fun d args => ⨆ (pPos : ℕ) (pNeg : ℕ) (pDst : ℕ) (pSignCell : ℕ),
    ⌜args = [pPos, pNeg, pDst, pSignCell, d.pos.length, d.k] ∧
      1 ≤ d.k ∧ 2 * d.k ≤ w ∧
      d.neg.length = d.pos.length ∧ d.dst0.length = d.pos.length ∧
      (∀ x ∈ d.pos, x < 2 ^ (w - 1)) ∧ (∀ x ∈ d.neg, x < 2 ^ (w - 1)) ∧
      Nat.ofDigits (2 ^ d.k) d.pos < (2 ^ d.k) ^ d.pos.length ∧
      Nat.ofDigits (2 ^ d.k) d.neg < (2 ^ d.k) ^ d.neg.length⌝ *
    Assn.list pPos d.pos * Assn.list pNeg d.neg * Assn.list pDst d.dst0 * (pSignCell ↦ d.sign0)
  post := fun d args v => ⨆ (pPos : ℕ) (pNeg : ℕ) (pDst : ℕ) (pSignCell : ℕ),
    let diff : ℤ := ((Nat.ofDigits (2 ^ d.k) d.pos : ℕ) : ℤ) - ((Nat.ofDigits (2 ^ d.k) d.neg : ℕ) : ℤ)
    let diffDig := Nat.digits (2 ^ d.k) diff.natAbs
    ⌜args = [pPos, pNeg, pDst, pSignCell, d.pos.length, d.k] ∧ v = diffDig.length⌝ *
    Assn.list pPos (normLimbs d.k d.pos) * Assn.list pNeg (normLimbs d.k d.neg) *
    Assn.list pDst (padLimbs diffDig d.pos.length) *
    (pSignCell ↦ (if diff < 0 then 1 else 0))

theorem stage0ShiftOneDem_meets {w : ℕ} {p : Program} {f accNorm lCmp lSub cLen : ℕ}
    {Tnorm Tcmp Tsub Tcan : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0ShiftOneDem accNorm lCmp lSub cLen))
    (hnorm : Meets w p accNorm ((accNormalizeSpec w).withCost fun x _ => Tnorm x.2.length))
    (hcmp : Meets w p lCmp (limbsCmpSpec.withCost fun x _ => Tcmp x.2.1.length))
    (hsub : Meets w p lSub ((limbsSubSpec w).withCost fun x _ => Tsub x.2.1.length))
    (hcan : Meets w p cLen (canonLenSpec.withCost fun x _ => Tcan x.2.length)) :
    Meets w p f ((stage0ShiftOneDemSpec w).withCost fun d _ =>
      2 * Tnorm d.pos.length + Tcmp d.pos.length + Tsub d.pos.length + Tcan d.pos.length + 80) := by
  sep_enter d with hk h2k hnegL hdstL hposW hnegW hposFit hnegFit
  have hkw : d.k < w := by omega
  have hw2 : 2 < 2 ^ w := by
    have : 2 ^ 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hvp := (normCarry_eq_zero_of_lt hk hposW hposFit).2
  have hvn := (normCarry_eq_zero_of_lt hk hnegW hnegFit).2
  have hLp : Limbs d.k (normLimbs d.k d.pos) := (normRun_spec hk hposW d.pos.length le_rfl).2.2
  have hLn : Limbs d.k (normLimbs d.k d.neg) := (normRun_spec hk hnegW d.neg.length le_rfl).2.2
  -- Normalize pos
  generalize hF1 : (Assn.list pNeg d.neg * Assn.list pDst d.dst0 * (pSignCell ↦ d.sign0)) = F1
  sep_apply hF1
  sep_step from (d.k, d.pos)
  subst F1; sep_norm
  -- Normalize neg
  generalize hF2 :
    (Assn.list pPos (normLimbs d.k d.pos) * Assn.list pDst d.dst0 * (pSignCell ↦ d.sign0)) = F2
  sep_apply hF2
  sep_step from (d.k, d.neg)
  subst F2; sep_norm
  -- Compare normPos vs normNeg
  generalize hF3 : (Assn.list pDst d.dst0 * (pSignCell ↦ d.sign0)) = F3
  sep_apply hF3
  sep_step from (d.k, normLimbs d.k d.pos, normLimbs d.k d.neg)
  subst F3; sep_norm
  have hlenP : (normLimbs d.k d.pos).length = d.pos.length := length_normLimbs d.k d.pos
  have hlenN : (normLimbs d.k d.neg).length = d.pos.length := by rw [length_normLimbs, hnegL]
  sep_step
  · -- cmp < 1 => pos < neg => diff < 0, diff.natAbs = neg - pos
    have hlt : Nat.ofDigits (2 ^ d.k) d.pos < Nat.ofDigits (2 ^ d.k) d.neg := by
      rw [hvp, hvn] at hcmp_1
      unfold cmpCode at hcmp_1
      split_ifs at hcmp_1 <;> omega
    have hdiff_neg : (((Nat.ofDigits (2 ^ d.k) d.pos : ℕ) : ℤ) - ((Nat.ofDigits (2 ^ d.k) d.neg : ℕ) : ℤ)) < 0 := by
      omega
    have hdiff_abs : (((Nat.ofDigits (2 ^ d.k) d.pos : ℕ) : ℤ) - ((Nat.ofDigits (2 ^ d.k) d.neg : ℕ) : ℤ)).natAbs =
        Nat.ofDigits (2 ^ d.k) d.neg - Nat.ofDigits (2 ^ d.k) d.pos := by
      omega
    sep_step
    sep_step from (d.k, normLimbs d.k d.neg, normLimbs d.k d.pos, d.dst0)
    sep_step
    have hval := (subBorrow_eq_zero_of_le hk hLn hLp (by omega)
      (by rw [hvp, hvn]; omega)).2
    rw [hvp, hvn, ← hdiff_abs] at hval
    have hsub_len : (subLimbs d.k (normLimbs d.k d.neg) (normLimbs d.k d.pos)).length =
        d.pos.length := by simp [subLimbs, length_carryRun, hlenN]
    have hsubL : Limbs d.k (subLimbs d.k (normLimbs d.k d.neg) (normLimbs d.k d.pos)) :=
      (subRun_spec hk hLn hLp (by omega) _ le_rfl).2.2
    generalize hF5 :
      (Assn.list pPos (normLimbs d.k d.pos) * Assn.list pNeg (normLimbs d.k d.neg) *
       (pSignCell ↦ 1)) = F5
    sep_apply hF5
    sep_step from (d.k, subLimbs d.k (normLimbs d.k d.neg) (normLimbs d.k d.pos)) with _ hpad_eq
    subst F5; sep_norm
    rw [hval] at hlen hpad_eq
    rw [hsub_len] at hpad_eq
    sep_apply (show Assn.list pDst (subLimbs d.k (normLimbs d.k d.neg) (normLimbs d.k d.pos)) =
      Assn.list pDst (padLimbs (Nat.digits (2 ^ d.k)
        (((Nat.ofDigits (2 ^ d.k) d.pos : ℕ) : ℤ) - ((Nat.ofDigits (2 ^ d.k) d.neg : ℕ) : ℤ)).natAbs) d.pos.length)
      by rw [hpad_eq])
    sep_apply (show (pSignCell ↦ 1) = (pSignCell ↦ if ((Nat.ofDigits (2 ^ d.k) d.pos : ℕ) : ℤ) -
        ((Nat.ofDigits (2 ^ d.k) d.neg : ℕ) : ℤ) < 0 then 1 else 0) by simp [hdiff_neg])
    sep_step
    · rw [hnegL, hlenP, hlenN, hsub_len]; omega
  · -- cmp ≥ 1 => neg ≤ pos => diff ≥ 0, diff.natAbs = pos - neg
    have hge : Nat.ofDigits (2 ^ d.k) d.neg ≤ Nat.ofDigits (2 ^ d.k) d.pos := by
      rw [hvp, hvn] at hcmp_1
      unfold cmpCode at hcmp_1
      split_ifs at hcmp_1 <;> omega
    have hdiff_nn : ¬ (((Nat.ofDigits (2 ^ d.k) d.pos : ℕ) : ℤ) - ((Nat.ofDigits (2 ^ d.k) d.neg : ℕ) : ℤ)) < 0 := by
      omega
    have hdiff_abs : (((Nat.ofDigits (2 ^ d.k) d.pos : ℕ) : ℤ) - ((Nat.ofDigits (2 ^ d.k) d.neg : ℕ) : ℤ)).natAbs =
        Nat.ofDigits (2 ^ d.k) d.pos - Nat.ofDigits (2 ^ d.k) d.neg := by
      omega
    sep_step
    sep_step from (d.k, normLimbs d.k d.pos, normLimbs d.k d.neg, d.dst0)
    sep_step
    have hval := (subBorrow_eq_zero_of_le hk hLp hLn (by omega)
      (by rw [hvp, hvn]; omega)).2
    rw [hvp, hvn, ← hdiff_abs] at hval
    have hsub_len : (subLimbs d.k (normLimbs d.k d.pos) (normLimbs d.k d.neg)).length =
        d.pos.length := by simp [subLimbs, length_carryRun, hlenP]
    have hsubL : Limbs d.k (subLimbs d.k (normLimbs d.k d.pos) (normLimbs d.k d.neg)) :=
      (subRun_spec hk hLp hLn (by omega) _ le_rfl).2.2
    generalize hF5 :
      (Assn.list pPos (normLimbs d.k d.pos) * Assn.list pNeg (normLimbs d.k d.neg) *
       (pSignCell ↦ 0)) = F5
    sep_apply hF5
    sep_step from (d.k, subLimbs d.k (normLimbs d.k d.pos) (normLimbs d.k d.neg)) with _ hpad_eq
    subst F5; sep_norm
    rw [hval] at hlen hpad_eq
    rw [hsub_len] at hpad_eq
    sep_apply (show Assn.list pDst (subLimbs d.k (normLimbs d.k d.pos) (normLimbs d.k d.neg)) =
      Assn.list pDst (padLimbs (Nat.digits (2 ^ d.k)
        (((Nat.ofDigits (2 ^ d.k) d.pos : ℕ) : ℤ) - ((Nat.ofDigits (2 ^ d.k) d.neg : ℕ) : ℤ)).natAbs) d.pos.length)
      by rw [hpad_eq])
    sep_apply (show (pSignCell ↦ 0) = (pSignCell ↦ if ((Nat.ofDigits (2 ^ d.k) d.pos : ℕ) : ℤ) -
        ((Nat.ofDigits (2 ^ d.k) d.neg : ℕ) : ℤ) < 0 then 1 else 0) by simp [hdiff_nn])
    sep_step
    · rw [hnegL, hlenP, hsub_len]; omega

end MinCostFlow.NarrowProg
