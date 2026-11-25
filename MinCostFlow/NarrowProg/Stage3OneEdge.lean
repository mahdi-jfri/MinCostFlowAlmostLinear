module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layout
public import WordRAM.Module
public import WordRAM.Std.Limbs
public import WordRAM.Std.Array
public import MinCostFlow.NarrowProg.Stage0ShiftHelpers
public import MinCostFlow.NarrowProg.Stage0Read
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Stage 3, item 6 helper: per-edge restored flow calculation and emission

Splits one-edge restoration into two straight-line procedures:
- `stage3Compute`: computes `ans = lower + f + hFwd - hRev` in `L` base-`2 ^ k` limbs into `pRes`
  (zero carry, zero borrow) and returns `sign = if ans < 0 then 1 else 0`.
- `stage3OneEdge`: calls `stage3Compute`, trims trailing zeros with `canonLen`, writes
  `[sign, len] ++ digits` to `pDst` via `WordRAM.Std.copy`, and returns `len + 2`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling

namespace MinCostFlow.NarrowProg

/-! ### Data and arithmetic helpers -/

structure Stage3OneEdgeData where
  k : ℕ
  L : ℕ
  lo : ℤ
  hi : ℤ
  fVal : ℕ
  hFwdVal : ℕ
  hRevVal : ℕ
  tmpA0 : List ℕ
  tmpB0 : List ℕ
  res0 : List ℕ
  dstBuf : List ℕ

/-- The restored integral flow value on one edge: `lo + fVal + hFwdVal - hRevVal`. -/
def stage3EdgeVal (d : Stage3OneEdgeData) : ℤ :=
  d.lo + (d.fVal : ℤ) + (d.hFwdVal : ℤ) - (d.hRevVal : ℤ)

private theorem subBorrow_zero_of_le' {k : ℕ} (hk : 1 ≤ k) {xs ys : List ℕ}
    (hx : Limbs k xs) (hy : Limbs k ys) (hl : ys.length = xs.length)
    (hle : Nat.ofDigits (2 ^ k) ys ≤ Nat.ofDigits (2 ^ k) xs) :
    Nat.ofDigits (2 ^ k) (subLimbs k xs ys) = Nat.ofDigits (2 ^ k) xs - Nat.ofDigits (2 ^ k) ys ∧
    Limbs k (subLimbs k xs ys) ∧ (subLimbs k xs ys).length = xs.length := by
  obtain ⟨hsub, _, hLsub⟩ := subRun_spec hk hx hy hl xs.length le_rfl
  rw [List.take_length, List.take_of_length_le (by omega)] at hsub
  change Nat.ofDigits (2 ^ k) (subLimbs k xs ys) + Nat.ofDigits (2 ^ k) ys =
    Nat.ofDigits (2 ^ k) xs + subBorrow k xs ys * (2 ^ k) ^ xs.length at hsub
  change Limbs k (subLimbs k xs ys) at hLsub
  have hlen : (subLimbs k xs ys).length = xs.length := by simp [subLimbs, length_carryRun]
  have hlt : Nat.ofDigits (2 ^ k) (subLimbs k xs ys) < (2 ^ k) ^ xs.length := by
    have h2 := two_le_pow hk
    have h := Nat.ofDigits_lt_base_pow_length (b := 2 ^ k) (by omega) hLsub
    rwa [hlen] at h
  have hb0 : subBorrow k xs ys = 0 := by
    by_contra hne
    have h1 : 1 * (2 ^ k) ^ xs.length ≤ subBorrow k xs ys * (2 ^ k) ^ xs.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  rw [hb0, Nat.zero_mul, Nat.add_zero] at hsub
  exact ⟨by omega, hLsub, hlen⟩

private theorem addCarry_zero_of_lt' {k : ℕ} (hk : 1 ≤ k) {xs ys : List ℕ}
    (hx : Limbs k xs) (hy : Limbs k ys) (hl : ys.length = xs.length)
    (hfit : Nat.ofDigits (2 ^ k) xs + Nat.ofDigits (2 ^ k) ys < (2 ^ k) ^ xs.length) :
    Nat.ofDigits (2 ^ k) (addLimbs k xs ys) = Nat.ofDigits (2 ^ k) xs + Nat.ofDigits (2 ^ k) ys ∧
    Limbs k (addLimbs k xs ys) ∧ (addLimbs k xs ys).length = xs.length := by
  obtain ⟨hadd, _, hLadd⟩ := addRun_spec hk hx hy hl xs.length le_rfl
  rw [List.take_length, List.take_of_length_le (by omega)] at hadd
  change Nat.ofDigits (2 ^ k) (addLimbs k xs ys) + addCarry k xs ys * (2 ^ k) ^ xs.length =
    Nat.ofDigits (2 ^ k) xs + Nat.ofDigits (2 ^ k) ys at hadd
  change Limbs k (addLimbs k xs ys) at hLadd
  have hlen : (addLimbs k xs ys).length = xs.length := by simp [addLimbs, length_carryRun]
  have hc0 : addCarry k xs ys = 0 := by
    by_contra hne
    have h1 : 1 * (2 ^ k) ^ xs.length ≤ addCarry k xs ys * (2 ^ k) ^ xs.length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  rw [hc0, Nat.zero_mul, Nat.add_zero] at hadd
  exact ⟨hadd, hLadd, hlen⟩

private theorem emit_intWords_split {pDst len : ℕ} {dstBuf : List ℕ}
    (hlen : 2 + len ≤ dstBuf.length) :
    Assn.list pDst dstBuf =
      (pDst ↦ dstBuf[0]'(by omega)) * (pDst + 1 ↦ dstBuf[1]'(by omega)) *
      Assn.list (pDst + 2) ((dstBuf.drop 2).take len) *
      Assn.list (pDst + 2 + len) (dstBuf.drop (2 + len)) := by
  have h0 : dstBuf = dstBuf[0]'(by omega) :: dstBuf[1]'(by omega) :: dstBuf.drop 2 := by
    rcases dstBuf with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp at hlen
    · simp at hlen; omega
    · rfl
  have hdrop : dstBuf.drop 2 = (dstBuf.drop 2).take len ++ dstBuf.drop (2 + len) := by
    have h1 := (List.take_append_drop len (dstBuf.drop 2)).symm
    rwa [List.drop_drop] at h1
  conv_lhs => rw [h0, Assn.list_cons, Assn.list_cons, hdrop, Assn.list_append]
  rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega : len ≤ dstBuf.length - 2)]
  simp only [mul_assoc, show pDst + 1 + 1 = pDst + 2 by omega]

private theorem emit_intWords_join {pDst k : ℕ} {z : ℤ} {dstBuf : List ℕ} :
    (pDst ↦ (if z < 0 then 1 else 0)) *
    (pDst + 1 ↦ (Nat.digits (2 ^ k) z.natAbs).length) *
    Assn.list (pDst + 2) (Nat.digits (2 ^ k) z.natAbs) *
    Assn.list (pDst + 2 + (Nat.digits (2 ^ k) z.natAbs).length)
      (dstBuf.drop (2 + (Nat.digits (2 ^ k) z.natAbs).length)) =
    Assn.list pDst (intWords k z ++ dstBuf.drop (intWords k z).length) := by
  rw [Assn.list_append, list_intWords, intWords_length]
  simp only [mul_assoc, add_assoc]

/-! ### `stage3NetFlow`: compute `g = f - hRev + hFwd` in `L` limbs into `pTmpB` -/

wram_def stage3NetFlow (lSub lAdd : ℕ) (pF, pHFwd, pHRev, pTmpA, pTmpB, L, k) {
  d := lSub(pF, pHRev, pTmpA, L, k)
  d := lAdd(pTmpA, pHFwd, pTmpB, L, k)
  return 0
}

def stage3NetFlowSpec (w : ℕ) : Spec Stage3OneEdgeData where
  pre := fun d args => ⨆ (pF : ℕ) (pHFwd : ℕ) (pHRev : ℕ) (pTmpA : ℕ) (pTmpB : ℕ),
    let fDig := Nat.digits (2 ^ d.k) d.fVal
    let fwdDig := Nat.digits (2 ^ d.k) d.hFwdVal
    let revDig := Nat.digits (2 ^ d.k) d.hRevVal
    ⌜args = [pF, pHFwd, pHRev, pTmpA, pTmpB, d.L, d.k] ∧
      3 ≤ d.k ∧ 2 * d.k ≤ w ∧ d.lo ≤ d.hi ∧
      (Nat.digits (2 ^ d.k) d.lo.natAbs).length < d.L ∧
      (Nat.digits (2 ^ d.k) d.hi.natAbs).length < d.L ∧
      d.hRevVal ≤ d.fVal ∧ d.fVal + d.hFwdVal ≤ (d.hi - d.lo).toNat ∧
      fDig.length ≤ d.L ∧ fwdDig.length ≤ d.L ∧ revDig.length ≤ d.L ∧
      d.tmpA0.length = d.L ∧ d.tmpB0.length = d.L⌝ *
    Assn.list pF (padLimbs fDig d.L) *
    Assn.list pHFwd (padLimbs fwdDig d.L) *
    Assn.list pHRev (padLimbs revDig d.L) *
    Assn.list pTmpA d.tmpA0 * Assn.list pTmpB d.tmpB0
  post := fun d args v => ⨆ (pF : ℕ) (pHFwd : ℕ) (pHRev : ℕ) (pTmpA : ℕ) (pTmpB : ℕ)
      (tmpA1 : List ℕ) (tmpB1 : List ℕ),
    let fDig := Nat.digits (2 ^ d.k) d.fVal
    let fwdDig := Nat.digits (2 ^ d.k) d.hFwdVal
    let revDig := Nat.digits (2 ^ d.k) d.hRevVal
    ⌜args = [pF, pHFwd, pHRev, pTmpA, pTmpB, d.L, d.k] ∧ v = 0 ∧
      tmpA1.length = d.L ∧ tmpB1.length = d.L ∧
      Limbs d.k tmpB1 ∧ Nat.ofDigits (2 ^ d.k) tmpB1 = d.fVal - d.hRevVal + d.hFwdVal⌝ *
    Assn.list pF (padLimbs fDig d.L) *
    Assn.list pHFwd (padLimbs fwdDig d.L) *
    Assn.list pHRev (padLimbs revDig d.L) *
    Assn.list pTmpA tmpA1 * Assn.list pTmpB tmpB1

theorem stage3NetFlow_meets {w : ℕ} {p : Program} {f lSub lAdd : ℕ} {Tsub Tadd : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage3NetFlow lSub lAdd))
    (hsub : Meets w p lSub ((limbsSubSpec w).withCost fun x _ => Tsub x.2.1.length))
    (hadd : Meets w p lAdd ((limbsAddSpec w).withCost fun x _ => Tadd x.2.1.length)) :
    Meets w p f ((stage3NetFlowSpec w).withCost fun d _ => Tsub d.L + Tadd d.L + 30) := by
  sep_enter d with hk3 h2k hle hloLt hhiLt hrevLe hsumLe hfL hfwdL hrevL htmpAL htmpBL
  have hk1 : 1 ≤ d.k := by omega
  have h2k_ge : 8 ≤ 2 ^ d.k := by
    calc 8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ d.k := Nat.pow_le_pow_right (by norm_num) hk3
  have hlo_lt : d.lo.natAbs < (2 ^ d.k) ^ (d.L - 1) := by
    have h1 := ofDigits_lt_pow_length hk1 (digits_limbs hk1 d.lo.natAbs)
    rw [Nat.ofDigits_digits] at h1
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))
  have hhi_lt : d.hi.natAbs < (2 ^ d.k) ^ (d.L - 1) := by
    have h1 := ofDigits_lt_pow_length hk1 (digits_limbs hk1 d.hi.natAbs)
    rw [Nat.ofDigits_digits] at h1
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))
  have hpowL : (2 ^ d.k) ^ d.L = (2 ^ d.k) ^ (d.L - 1) * 2 ^ d.k := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have htwo_pow : 2 * (2 ^ d.k) ^ (d.L - 1) ≤ (2 ^ d.k) ^ d.L := by
    rw [hpowL, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have hpFL : (padLimbs (Nat.digits (2 ^ d.k) d.fVal) d.L).length = d.L := length_padLimbs hfL
  have hpFwdL : (padLimbs (Nat.digits (2 ^ d.k) d.hFwdVal) d.L).length = d.L := length_padLimbs hfwdL
  have hpRevL : (padLimbs (Nat.digits (2 ^ d.k) d.hRevVal) d.L).length = d.L := length_padLimbs hrevL
  have hpFLimbs : Limbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.fVal) d.L) :=
    limbs_padLimbs (digits_limbs hk1 _) d.L
  have hpFwdLimbs : Limbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.hFwdVal) d.L) :=
    limbs_padLimbs (digits_limbs hk1 _) d.L
  have hpRevLimbs : Limbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.hRevVal) d.L) :=
    limbs_padLimbs (digits_limbs hk1 _) d.L
  have hpFVal : Nat.ofDigits (2 ^ d.k) (padLimbs (Nat.digits (2 ^ d.k) d.fVal) d.L) = d.fVal := by
    rw [ofDigits_padLimbs, Nat.ofDigits_digits]
  have hpFwdVal : Nat.ofDigits (2 ^ d.k) (padLimbs (Nat.digits (2 ^ d.k) d.hFwdVal) d.L) = d.hFwdVal := by
    rw [ofDigits_padLimbs, Nat.ofDigits_digits]
  have hpRevVal : Nat.ofDigits (2 ^ d.k) (padLimbs (Nat.digits (2 ^ d.k) d.hRevVal) d.L) = d.hRevVal := by
    rw [ofDigits_padLimbs, Nat.ofDigits_digits]
  generalize hFList : padLimbs (Nat.digits (2 ^ d.k) d.fVal) d.L = pFList at hpFL hpFLimbs hpFVal ⊢
  generalize hFwdList : padLimbs (Nat.digits (2 ^ d.k) d.hFwdVal) d.L = pFwdList at hpFwdL hpFwdLimbs hpFwdVal ⊢
  generalize hRevList : padLimbs (Nat.digits (2 ^ d.k) d.hRevVal) d.L = pRevList at hpRevL hpRevLimbs hpRevVal ⊢
  generalize hF1 : (Assn.list pHFwd pFwdList * Assn.list pTmpB d.tmpB0) = F1
  sep_apply hF1
  sep_step from (d.k, pFList, pRevList, d.tmpA0)
  subst F1; sep_norm
  obtain ⟨hdiff_val, hdiff_L, hdiff_len⟩ :=
    subBorrow_zero_of_le' hk1 hpFLimbs hpRevLimbs (by omega) (by rw [hpFVal, hpRevVal]; exact hrevLe)
  rw [hpFVal, hpRevVal] at hdiff_val; rw [hpFL] at hdiff_len
  generalize subLimbs d.k pFList pRevList = diffFR at hdiff_val hdiff_L hdiff_len ⊢
  generalize hF2 : (Assn.list pF pFList * Assn.list pHRev pRevList) = F2
  sep_apply hF2
  sep_step from (d.k, diffFR, pFwdList, d.tmpB0)
  subst F2; sep_norm
  have hg_lt : d.fVal - d.hRevVal + d.hFwdVal < (2 ^ d.k) ^ d.L := by
    have hcap_lt : (d.hi - d.lo).toNat ≤ d.hi.natAbs + d.lo.natAbs := by omega
    omega
  obtain ⟨hg_val, hg_L, hg_len⟩ :=
    addCarry_zero_of_lt' hk1 hdiff_L hpFwdLimbs (by omega)
      (by rw [hdiff_val, hpFwdVal, hdiff_len]; exact hg_lt)
  rw [hdiff_val, hpFwdVal] at hg_val; rw [hdiff_len] at hg_len
  generalize addLimbs d.k diffFR pFwdList = gList at hg_val hg_L hg_len ⊢
  simp only [stage3NetFlowSpec, Spec.withCost, hFList, hFwdList, hRevList]
  sep_step
  · rw [hpFL, hdiff_len]; omega

/-! ### `stage3AddLower`: compute `lo + g` into `pRes` and return `sign` -/

wram_def stage3AddLower (pCopy lAdd lSub lCmp : ℕ)
    (pLoPtr, loSign, loLen, pG, pTmpA, pRes, L, k) {
  d := pCopy(pLoPtr, loLen, pTmpA, L)
  if loSign == 0 {
    d := lAdd(pTmpA, pG, pRes, L, k)
    return 0
  } else {
    cmp := lCmp(pG, pTmpA, L)
    if cmp < 1 {
      d := lSub(pTmpA, pG, pRes, L, k)
      return 1
    } else {
      d := lSub(pG, pTmpA, pRes, L, k)
      return 0
    }
  }
}

structure Stage3AddLowerData where
  k : ℕ
  L : ℕ
  lo : ℤ
  hi : ℤ
  gList : List ℕ
  tmpA0 : List ℕ
  res0 : List ℕ

def stage3AddLowerSpec (w : ℕ) : Spec Stage3AddLowerData where
  pre := fun d args => ⨆ (pLoPtr : ℕ) (pG : ℕ) (pTmpA : ℕ) (pRes : ℕ),
    let loDig := Nat.digits (2 ^ d.k) d.lo.natAbs
    ⌜args = [pLoPtr, (if d.lo < 0 then 1 else 0), loDig.length, pG, pTmpA, pRes, d.L, d.k] ∧
      3 ≤ d.k ∧ 2 * d.k ≤ w ∧ d.lo ≤ d.hi ∧
      loDig.length < d.L ∧ (Nat.digits (2 ^ d.k) d.hi.natAbs).length < d.L ∧
      d.gList.length = d.L ∧ Limbs d.k d.gList ∧
      Nat.ofDigits (2 ^ d.k) d.gList ≤ (d.hi - d.lo).toNat ∧
      d.tmpA0.length = d.L ∧ d.res0.length = d.L⌝ *
    Assn.list pLoPtr loDig * Assn.list pG d.gList * Assn.list pTmpA d.tmpA0 * Assn.list pRes d.res0
  post := fun d args v => ⨆ (pLoPtr : ℕ) (pG : ℕ) (pTmpA : ℕ) (pRes : ℕ)
      (tmpA1 : List ℕ) (res1 : List ℕ),
    let loDig := Nat.digits (2 ^ d.k) d.lo.natAbs
    let ans : ℤ := d.lo + ((Nat.ofDigits (2 ^ d.k) d.gList : ℕ) : ℤ)
    ⌜args = [pLoPtr, (if d.lo < 0 then 1 else 0), loDig.length, pG, pTmpA, pRes, d.L, d.k] ∧
      v = (if ans < 0 then 1 else 0) ∧
      tmpA1.length = d.L ∧ res1.length = d.L ∧
      Limbs d.k res1 ∧ Nat.ofDigits (2 ^ d.k) res1 = ans.natAbs⌝ *
    Assn.list pLoPtr loDig * Assn.list pG d.gList * Assn.list pTmpA tmpA1 * Assn.list pRes res1

theorem stage3AddLower_meets {w : ℕ} {p : Program} {f pCopy lAdd lSub lCmp : ℕ}
    {Tpad Tadd Tsub Tcmp : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage3AddLower pCopy lAdd lSub lCmp))
    (hpad : Meets w p pCopy (padCopySpec.withCost fun x _ => Tpad x.2.length))
    (hadd : Meets w p lAdd ((limbsAddSpec w).withCost fun x _ => Tadd x.2.1.length))
    (hsub : Meets w p lSub ((limbsSubSpec w).withCost fun x _ => Tsub x.2.1.length))
    (hcmp : Meets w p lCmp (limbsCmpSpec.withCost fun x _ => Tcmp x.2.1.length)) :
    Meets w p f ((stage3AddLowerSpec w).withCost fun d _ =>
      Tpad d.L + Tadd d.L + Tsub d.L + Tcmp d.L + 60) := by
  sep_enter d with hk3 h2k hle hloLt hhiLt hgLen hgL hgLe htmpAL hresL
  have hk1 : 1 ≤ d.k := by omega
  have h2k_ge : 8 ≤ 2 ^ d.k := by
    calc 8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ d.k := Nat.pow_le_pow_right (by norm_num) hk3
  have hhi_lt : d.hi.natAbs < (2 ^ d.k) ^ (d.L - 1) := by
    have h1 := ofDigits_lt_pow_length hk1 (digits_limbs hk1 d.hi.natAbs)
    rw [Nat.ofDigits_digits] at h1
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))
  have hpowL : (2 ^ d.k) ^ d.L = (2 ^ d.k) ^ (d.L - 1) * 2 ^ d.k := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have htwo_pow : 2 * (2 ^ d.k) ^ (d.L - 1) ≤ (2 ^ d.k) ^ d.L := by
    rw [hpowL, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  generalize hF1 : (Assn.list pG d.gList * Assn.list pRes d.res0) = F1
  sep_apply hF1
  sep_step from (Nat.digits (2 ^ d.k) d.lo.natAbs, d.tmpA0)
  subst F1; sep_norm
  have hloPad_len : (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.tmpA0.length).length = d.L := by
    rw [length_padLimbs (by omega), htmpAL]
  have hloPad_L : Limbs d.k (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.tmpA0.length) :=
    limbs_padLimbs (digits_limbs hk1 _) _
  have hloPad_val : Nat.ofDigits (2 ^ d.k) (padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.tmpA0.length) =
      d.lo.natAbs := by rw [ofDigits_padLimbs, Nat.ofDigits_digits]
  generalize padLimbs (Nat.digits (2 ^ d.k) d.lo.natAbs) d.tmpA0.length = loPad at hloPad_len hloPad_L hloPad_val ⊢
  sep_step
  · have hlo_nn : 0 ≤ d.lo := by
      by_cases h : d.lo < 0
      · simp [h] at hcond
      · omega
    have hans_nn : ¬ (d.lo + ((Nat.ofDigits (2 ^ d.k) d.gList : ℕ) : ℤ) < 0) := by omega
    have hans_abs : (d.lo + ((Nat.ofDigits (2 ^ d.k) d.gList : ℕ) : ℤ)).natAbs =
        d.lo.natAbs + Nat.ofDigits (2 ^ d.k) d.gList := by omega
    have hsum_fit : d.lo.natAbs + Nat.ofDigits (2 ^ d.k) d.gList < (2 ^ d.k) ^ d.L := by omega
    sep_step from (d.k, loPad, d.gList, d.res0)
    obtain ⟨hres_val, hres_L, hres_len⟩ :=
      addCarry_zero_of_lt' hk1 hloPad_L hgL (by omega)
        (by rw [hloPad_val, hloPad_len]; exact hsum_fit)
    rw [hloPad_val, ← hans_abs] at hres_val; rw [hloPad_len] at hres_len
    generalize addLimbs d.k loPad d.gList = res1 at hres_val hres_L hres_len ⊢
    sep_step
    · rw [htmpAL, hloPad_len]; omega
  · have hlo_neg : d.lo < 0 := by
      by_cases h : d.lo < 0
      · exact h
      · simp [h] at hcond
    generalize hF2 : (Assn.list pLoPtr (Nat.digits (2 ^ d.k) d.lo.natAbs) * Assn.list pRes d.res0) = F2
    sep_apply hF2
    sep_step from (d.k, d.gList, loPad)
    subst F2; sep_norm
    sep_step
    · have hg_lt_lo : Nat.ofDigits (2 ^ d.k) d.gList < d.lo.natAbs := by
        rw [hloPad_val] at hcmp_1; unfold cmpCode at hcmp_1
        split_ifs at hcmp_1 with h1 h2
        · exact h1
        · omega
        · omega
      have hans_neg : d.lo + ((Nat.ofDigits (2 ^ d.k) d.gList : ℕ) : ℤ) < 0 := by omega
      have hans_abs : (d.lo + ((Nat.ofDigits (2 ^ d.k) d.gList : ℕ) : ℤ)).natAbs =
          d.lo.natAbs - Nat.ofDigits (2 ^ d.k) d.gList := by omega
      sep_step from (d.k, loPad, d.gList, d.res0)
      obtain ⟨hres_val, hres_L, hres_len⟩ :=
        subBorrow_zero_of_le' hk1 hloPad_L hgL (by omega) (by rw [hloPad_val]; omega)
      rw [hloPad_val, ← hans_abs] at hres_val; rw [hloPad_len] at hres_len
      generalize subLimbs d.k loPad d.gList = res1 at hres_val hres_L hres_len ⊢
      sep_step
      · rw [htmpAL, hgLen, hloPad_len]; omega
    · have hlo_le_g : d.lo.natAbs ≤ Nat.ofDigits (2 ^ d.k) d.gList := by
        rw [hloPad_val] at hcmp_1; unfold cmpCode at hcmp_1
        split_ifs at hcmp_1 with h1 h2
        · omega
        · omega
        · omega
      have hans_nn : ¬ (d.lo + ((Nat.ofDigits (2 ^ d.k) d.gList : ℕ) : ℤ) < 0) := by omega
      have hans_abs : (d.lo + ((Nat.ofDigits (2 ^ d.k) d.gList : ℕ) : ℤ)).natAbs =
          Nat.ofDigits (2 ^ d.k) d.gList - d.lo.natAbs := by omega
      sep_step from (d.k, d.gList, loPad, d.res0)
      obtain ⟨hres_val, hres_L, hres_len⟩ :=
        subBorrow_zero_of_le' hk1 hgL hloPad_L (by omega) (by rw [hloPad_val]; omega)
      rw [hloPad_val, ← hans_abs] at hres_val; rw [hgLen] at hres_len
      generalize subLimbs d.k d.gList loPad = res1 at hres_val hres_L hres_len ⊢
      sep_step
      · rw [htmpAL, hgLen]; omega

/-! ### `stage3OneEdge`: compute, trim, and emit `intWords k ans` at `pDst` -/

wram_def stage3OneEdge (netFlow addLower cLen arrCopy : ℕ)
    (pLoPtr, loSign, loLen, pF, pHFwd, pHRev, pTmpA, pTmpB, pRes, pDst, L, k) {
  d := netFlow(pF, pHFwd, pHRev, pTmpA, pTmpB, L, k)
  sign := addLower(pLoPtr, loSign, loLen, pTmpB, pTmpA, pRes, L, k)
  len := cLen(pRes, L)
  mem[pDst] := sign
  mem[pDst + 1] := len
  d := arrCopy(pRes, pDst + 2, len)
  return len + 2
}

def stage3OneEdgeSpec (w : ℕ) : Spec Stage3OneEdgeData where
  pre := fun d args => ⨆ (pLoPtr : ℕ) (pF : ℕ) (pHFwd : ℕ) (pHRev : ℕ)
      (pTmpA : ℕ) (pTmpB : ℕ) (pRes : ℕ) (pDst : ℕ),
    let loDig := Nat.digits (2 ^ d.k) d.lo.natAbs
    let fDig := Nat.digits (2 ^ d.k) d.fVal
    let fwdDig := Nat.digits (2 ^ d.k) d.hFwdVal
    let revDig := Nat.digits (2 ^ d.k) d.hRevVal
    ⌜args = [pLoPtr, (if d.lo < 0 then 1 else 0), loDig.length,
        pF, pHFwd, pHRev, pTmpA, pTmpB, pRes, pDst, d.L, d.k] ∧
      3 ≤ d.k ∧ 2 * d.k ≤ w ∧ d.lo ≤ d.hi ∧
      loDig.length < d.L ∧ (Nat.digits (2 ^ d.k) d.hi.natAbs).length < d.L ∧
      d.hRevVal ≤ d.fVal ∧ d.fVal + d.hFwdVal ≤ (d.hi - d.lo).toNat ∧
      fDig.length ≤ d.L ∧ fwdDig.length ≤ d.L ∧ revDig.length ≤ d.L ∧
      d.tmpA0.length = d.L ∧ d.tmpB0.length = d.L ∧ d.res0.length = d.L ∧
      d.L + 2 ≤ d.dstBuf.length ∧ pDst + d.dstBuf.length ≤ 2 ^ w ∧ d.L + 2 < 2 ^ w⌝ *
    Assn.list pLoPtr loDig *
    Assn.list pF (padLimbs fDig d.L) *
    Assn.list pHFwd (padLimbs fwdDig d.L) *
    Assn.list pHRev (padLimbs revDig d.L) *
    Assn.list pTmpA d.tmpA0 * Assn.list pTmpB d.tmpB0 * Assn.list pRes d.res0 *
    Assn.list pDst d.dstBuf
  post := fun d args v => ⨆ (pLoPtr : ℕ) (pF : ℕ) (pHFwd : ℕ) (pHRev : ℕ)
      (pTmpA : ℕ) (pTmpB : ℕ) (pRes : ℕ) (pDst : ℕ)
      (tmpA1 : List ℕ) (tmpB1 : List ℕ) (res1 : List ℕ),
    let loDig := Nat.digits (2 ^ d.k) d.lo.natAbs
    let fDig := Nat.digits (2 ^ d.k) d.fVal
    let fwdDig := Nat.digits (2 ^ d.k) d.hFwdVal
    let revDig := Nat.digits (2 ^ d.k) d.hRevVal
    let words := intWords d.k (stage3EdgeVal d)
    ⌜args = [pLoPtr, (if d.lo < 0 then 1 else 0), loDig.length,
        pF, pHFwd, pHRev, pTmpA, pTmpB, pRes, pDst, d.L, d.k] ∧
      v = words.length ∧ words.length ≤ d.L + 2 ∧
      tmpA1.length = d.L ∧ tmpB1.length = d.L ∧ res1.length = d.L⌝ *
    Assn.list pLoPtr loDig *
    Assn.list pF (padLimbs fDig d.L) *
    Assn.list pHFwd (padLimbs fwdDig d.L) *
    Assn.list pHRev (padLimbs revDig d.L) *
    Assn.list pTmpA tmpA1 * Assn.list pTmpB tmpB1 * Assn.list pRes res1 *
    Assn.list pDst (words ++ d.dstBuf.drop words.length)

theorem stage3OneEdge_meets {w : ℕ} {p : Program} {f netFlow addLower cLen arrCopy : ℕ}
    {Tnet TaddL Tcan Tcopy : ℕ → ℕ}
    (hmonoC : ∀ a b, a ≤ b → Tcopy a ≤ Tcopy b)
    (hp : p.procs[f]? = some (stage3OneEdge netFlow addLower cLen arrCopy))
    (hnet : Meets w p netFlow ((stage3NetFlowSpec w).withCost fun d _ => Tnet d.L))
    (haddL : Meets w p addLower ((stage3AddLowerSpec w).withCost fun d _ => TaddL d.L))
    (hcan : Meets w p cLen (canonLenSpec.withCost fun x _ => Tcan x.2.length))
    (hcopy : Meets w p arrCopy ((copySpec w).withCost fun x _ => Tcopy x.1.length)) :
    Meets w p f ((stage3OneEdgeSpec w).withCost fun d _ =>
      Tnet d.L + TaddL d.L + Tcan d.L + Tcopy d.L + 100) := by
  sep_enter d with hk3 h2k hle hloLt hhiLt hrevLe hsumLe hfL hfwdL hrevL htmpAL htmpBL hresL hdstL hpDstW hL2w
  have hk1 : 1 ≤ d.k := by omega
  have hL1 : 1 ≤ d.L := by omega
  have hw2 : 1 < 2 ^ w := by
    have : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  -- Call stage3NetFlow
  generalize hF0 :
    (Assn.list pLoPtr (Nat.digits (2 ^ d.k) d.lo.natAbs) *
     Assn.list pRes d.res0 * Assn.list pDst d.dstBuf) = F0
  sep_apply hF0
  sep_step from d with htmpA0 htmpB1 hgLimbs hgVal
  subst F0; sep_norm
  -- Call stage3AddLower
  have hans_eq : d.lo + ((Nat.ofDigits (2 ^ d.k) tmpB1 : ℕ) : ℤ) = stage3EdgeVal d := by
    rw [hgVal]; unfold stage3EdgeVal; omega
  generalize hF1 :
    (Assn.list pF (padLimbs (Nat.digits (2 ^ d.k) d.fVal) d.L) *
     Assn.list pHFwd (padLimbs (Nat.digits (2 ^ d.k) d.hFwdVal) d.L) *
     Assn.list pHRev (padLimbs (Nat.digits (2 ^ d.k) d.hRevVal) d.L) *
     Assn.list pDst d.dstBuf) = F1
  sep_apply hF1
  sep_step from (⟨d.k, d.L, d.lo, d.hi, tmpB1, tmpA1, d.res0⟩ : Stage3AddLowerData)
    with htmpA2 hres1L hres1Limbs hres1Val
  subst F1; sep_norm
  rw [hans_eq] at hsign hres1Val
  -- Call canonLen
  generalize hF2 :
    (Assn.list pLoPtr (Nat.digits (2 ^ d.k) d.lo.natAbs) *
     Assn.list pF (padLimbs (Nat.digits (2 ^ d.k) d.fVal) d.L) *
     Assn.list pHFwd (padLimbs (Nat.digits (2 ^ d.k) d.hFwdVal) d.L) *
     Assn.list pHRev (padLimbs (Nat.digits (2 ^ d.k) d.hRevVal) d.L) *
     Assn.list pTmpA tmpA1_1 * Assn.list pTmpB tmpB1 * Assn.list pDst d.dstBuf) = F2
  sep_apply hF2
  sep_step from (d.k, res1) with _ hpad_eq
  subst F2; sep_norm
  rw [hres1Val] at hlen hpad_eq
  rw [hres1L] at hpad_eq
  have hdig_le : (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length ≤ d.L := by
    have h1 : (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length ≤
        (padLimbs (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs) d.L).length := by
      simp [padLimbs]
    rw [← hpad_eq, hres1L] at h1; exact h1
  sep_apply (show Assn.list pRes res1 =
    Assn.list pRes (padLimbs (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs) d.L) by rw [hpad_eq])
  have hres_split :
      Assn.list pRes (padLimbs (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs) d.L) =
      Assn.list pRes (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs) *
      Assn.list (pRes + (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length)
        (List.replicate (d.L - (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length) 0) := by
    unfold padLimbs; rw [Assn.list_append]
  sep_apply hres_split
  sep_step; sep_step
  have hdst_upd :
      Assn.list pDst ((d.dstBuf.set 0 (if stage3EdgeVal d < 0 then 1 else 0)).set 1
        (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length) =
      (pDst ↦ if stage3EdgeVal d < 0 then 1 else 0) *
      (pDst + 1 ↦ (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length) *
      Assn.list (pDst + 2) ((d.dstBuf.drop 2).take (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length) *
      Assn.list (pDst + 2 + (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length)
        (d.dstBuf.drop (2 + (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length)) := by
    rw [emit_intWords_split (len := (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length)
      (by simp; omega)]
    have hdrop2 : ((d.dstBuf.set 0 (if stage3EdgeVal d < 0 then 1 else 0)).set 1
        (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length).drop 2 = d.dstBuf.drop 2 := by
      rcases d.dstBuf with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp at hdstL ⊢
    have hdropL : ((d.dstBuf.set 0 (if stage3EdgeVal d < 0 then 1 else 0)).set 1
        (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length).drop
        (2 + (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length) =
        d.dstBuf.drop (2 + (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length) := by
      rw [← List.drop_drop, hdrop2, List.drop_drop]
    simp [hdrop2, hdropL]
  sep_apply hdst_upd
  generalize hF3 :
    (Assn.list pLoPtr (Nat.digits (2 ^ d.k) d.lo.natAbs) *
     Assn.list pF (padLimbs (Nat.digits (2 ^ d.k) d.fVal) d.L) *
     Assn.list pHFwd (padLimbs (Nat.digits (2 ^ d.k) d.hFwdVal) d.L) *
     Assn.list pHRev (padLimbs (Nat.digits (2 ^ d.k) d.hRevVal) d.L) *
     Assn.list pTmpA tmpA1_1 * Assn.list pTmpB tmpB1 *
     Assn.list (pRes + (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length)
       (List.replicate (d.L - (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length) 0) *
     (pDst ↦ if stage3EdgeVal d < 0 then 1 else 0) *
     (pDst + 1 ↦ (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length) *
     Assn.list (pDst + 2 + (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length)
       (d.dstBuf.drop (2 + (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length))) = F3
  sep_apply hF3
  sep_step from (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs,
    (d.dstBuf.drop 2).take (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length)
  subst F3; sep_norm
  sep_apply hres_split.symm
  sep_apply emit_intWords_join (pDst := pDst) (k := d.k) (z := stage3EdgeVal d) (dstBuf := d.dstBuf)
  have hcopy_le : Tcopy (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length ≤ Tcopy d.L :=
    hmonoC _ _ hdig_le
  have hlen_ret : (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length + 2 =
      (intWords d.k (stage3EdgeVal d)).length := by rw [intWords_length]; omega
  have hlen_w : (Nat.digits (2 ^ d.k) (stage3EdgeVal d).natAbs).length + 2 < 2 ^ w := by omega
  sep_step
  · rw [hres1L]; omega

end MinCostFlow.NarrowProg
