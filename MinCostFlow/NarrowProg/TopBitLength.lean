module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import WordRAM.Std.Limbs
public import WordRAM.Std.Bits
import WordRAM.Std.LimbsBits
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Bit length of the largest of `m` long numbers

Given `m` canonical base-`2 ^ k` long numbers (each with no leading zero limb), stored at pointers
`ptrs[0], …, ptrs[m - 1]` with limb counts `lens[0], …, lens[m - 1]`, `topBitLength` computes
`Nat.size (maxLimbsVal k xs)`, the bit length of the largest number, in `O(m)` steps plus a single
call to `bitLength`.

It scans the `m` numbers once in `O(1)` time each, tracking the largest limb count `bestLen` and
the largest top limb `bestTop` among numbers of that length. If `bestLen = 0` all numbers are zero
and it returns `0`; otherwise it calls `bitLength (bestTop)` once and returns
`(bestLen - 1) * k + bitLength (bestTop)`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std

namespace MinCostFlow.NarrowProg

/-! ### Canonical limbs and maximum bit length -/

/-- A base-`2 ^ k` limb list with every limb below `2 ^ k` and no leading zero limb. -/
def CanonicalLimbs (k : ℕ) (l : List ℕ) : Prop :=
  Limbs k l ∧ ∀ h : l ≠ [], l.getLast h ≠ 0

/-- The largest natural number represented by a list of base-`2 ^ k` limb lists (`0` if empty). -/
def maxLimbsVal (k : ℕ) (xs : List (List ℕ)) : ℕ :=
  (xs.map (Nat.ofDigits (2 ^ k))).foldr max 0

/-- One step of the `(bestLen, bestTop)` scan over canonical limb lists. -/
def bestPairStep (p : ℕ × ℕ) (l : List ℕ) : ℕ × ℕ :=
  if l.length = 0 then p
  else if p.1 < l.length then (l.length, l.getD (l.length - 1) 0)
  else if l.length = p.1 then
    if p.2 < l.getD (l.length - 1) 0 then (p.1, l.getD (l.length - 1) 0) else p
  else p

/-- The `(bestLen, bestTop)` pair after scanning the first `i` limb lists of `xs`. -/
def bestPairPrefix (xs : List (List ℕ)) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | i + 1 => bestPairStep (bestPairPrefix xs i) (xs.getD i [])

/-- The top limb selected by the scan over `xs` (`0` if all numbers are zero). -/
def maxTopLimb (xs : List (List ℕ)) : ℕ :=
  (bestPairPrefix xs xs.length).2

/-- The bit length encoded by a `(bestLen, bestTop)` pair in base `2 ^ k`. -/
def pairBitLength (k : ℕ) (p : ℕ × ℕ) : ℕ :=
  if p.1 = 0 then 0 else (p.1 - 1) * k + Nat.size p.2

/-- The bit length of a canonical base-`2 ^ k` number with `n > 0` limbs is
`(n - 1) * k + Nat.size topLimb`. -/
theorem size_ofDigits_canonical {k : ℕ} {l : List ℕ} (hC : CanonicalLimbs k l)
    (hn : 0 < l.length) :
    Nat.size (Nat.ofDigits (2 ^ k) l) =
      (l.length - 1) * k + Nat.size (l.getD (l.length - 1) 0) := by
  have hne : l ≠ [] := List.ne_nil_of_length_pos hn
  have hidx : l.length - 1 < l.length := by omega
  have htop_eq : l.getD (l.length - 1) 0 = l.getLast hne := by
    rw [List.getD_eq_getElem _ _ hidx, List.getLast_eq_getElem]
  have htop_pos : 0 < l.getD (l.length - 1) 0 := by
    rw [htop_eq]; exact Nat.pos_of_ne_zero (hC.2 hne)
  have htop_size_pos : 0 < Nat.size (l.getD (l.length - 1) 0) := Nat.size_pos.mpr htop_pos
  set n := l.length
  set top := l.getD (n - 1) 0
  have hsplit : Nat.ofDigits (2 ^ k) l =
      Nat.ofDigits (2 ^ k) (l.take (n - 1)) + 2 ^ ((n - 1) * k) * top := by
    have hs := ofDigits_split (2 ^ k) (xs := l) (j := n - 1) hidx
    rw [show n - 1 + 1 = n by omega, List.drop_of_length_le le_rfl, Nat.ofDigits_nil,
      Nat.mul_zero, Nat.add_zero, ← pow_mul, Nat.mul_comm k (n - 1)] at hs
    exact hs
  have hA : Nat.ofDigits (2 ^ k) (l.take (n - 1)) < 2 ^ ((n - 1) * k) := by
    have hLtake : Limbs k (l.take (n - 1)) := fun x hx => hC.1 x (List.mem_of_mem_take hx)
    have h := ofDigits_lt_pow hLtake
    rw [List.length_take, Nat.min_eq_left (by omega), Nat.mul_comm] at h
    exact h
  rw [hsplit]
  refine le_antisymm ?_ ?_
  · refine Nat.size_le.mpr ?_
    have htop_lt : top < 2 ^ Nat.size top := Nat.lt_size_self top
    have h1 : 2 ^ ((n - 1) * k) * (top + 1) ≤ 2 ^ ((n - 1) * k) * 2 ^ Nat.size top :=
      Nat.mul_le_mul_left _ (by omega)
    rw [← pow_add] at h1
    have h2 : Nat.ofDigits (2 ^ k) (l.take (n - 1)) + 2 ^ ((n - 1) * k) * top <
        2 ^ ((n - 1) * k) * (top + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    exact lt_of_lt_of_le h2 h1
  · have htop_ge : 2 ^ (Nat.size top - 1) ≤ top := Nat.lt_size.mp (by omega)
    have h1 : 2 ^ ((n - 1) * k + Nat.size top - 1) ≤ 2 ^ ((n - 1) * k) * top := by
      rw [show (n - 1) * k + Nat.size top - 1 = (n - 1) * k + (Nat.size top - 1) by omega,
        pow_add]
      exact Nat.mul_le_mul_left _ htop_ge
    have hlt : (n - 1) * k + Nat.size top - 1 <
        Nat.size (Nat.ofDigits (2 ^ k) (l.take (n - 1)) + 2 ^ ((n - 1) * k) * top) :=
      Nat.lt_size.mpr (le_trans h1 (Nat.le_add_left _ _))
    omega

theorem size_max (a b : ℕ) : Nat.size (max a b) = max (Nat.size a) (Nat.size b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Nat.size_le_size h)]
  · rw [max_eq_left h, max_eq_left (Nat.size_le_size h)]

private theorem foldr_max_append_singleton (xs : List ℕ) (a : ℕ) :
    (xs ++ [a]).foldr max 0 = max (xs.foldr max 0) a := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.foldr_cons, ih]
    omega

theorem maxLimbsVal_take_succ (k : ℕ) {xs : List (List ℕ)} {i : ℕ} (hi : i < xs.length) :
    maxLimbsVal k (xs.take (i + 1)) =
      max (maxLimbsVal k (xs.take i)) (Nat.ofDigits (2 ^ k) (xs.getD i [])) := by
  unfold maxLimbsVal
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.map_append,
    List.map_singleton, foldr_max_append_singleton, List.getD_eq_getElem _ _ hi]

/-- Invariant of `bestPairPrefix`: tracks the exact bit length of the prefix maximum,
keeps the top limb positive and below `2 ^ k` when nonzero, and bounds `bestLen * k`. -/
theorem bestPairPrefix_spec {k w : ℕ} (hk : 1 ≤ k) {xs : List (List ℕ)}
    (hC : ∀ l ∈ xs, CanonicalLimbs k l ∧ l.length * k < 2 ^ w) :
    ∀ i ≤ xs.length,
      let p := bestPairPrefix xs i
      pairBitLength k p = Nat.size (maxLimbsVal k (xs.take i)) ∧
      (p.1 = 0 → p.2 = 0) ∧
      (0 < p.1 → 0 < p.2 ∧ p.2 < 2 ^ k ∧ p.1 * k < 2 ^ w) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [bestPairPrefix, pairBitLength, maxLimbsVal]
  | succ i ih =>
    intro hi
    obtain ⟨hsize, hz, hpos⟩ := ih (by omega)
    have hi' : i < xs.length := by omega
    have hl_mem : xs.getD i [] ∈ xs := by
      rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi'
    obtain ⟨hCl, hfitl⟩ := hC _ hl_mem
    simp only [bestPairPrefix, bestPairStep]
    rw [maxLimbsVal_take_succ k hi', size_max, ← hsize]
    set p := bestPairPrefix xs i
    set l := xs.getD i []
    by_cases hl0 : l.length = 0
    · simp only [hl0, ↓reduceIte]
      have hlnil : l = [] := List.eq_nil_of_length_eq_zero hl0
      rw [hlnil, Nat.ofDigits_nil, Nat.size_zero, max_eq_left (Nat.zero_le _)]
      exact ⟨rfl, hz, hpos⟩
    · have hlpos : 0 < l.length := by omega
      have hne : l ≠ [] := List.ne_nil_of_length_pos hlpos
      have hidx : l.length - 1 < l.length := by omega
      have htop_pos : 0 < l.getD (l.length - 1) 0 := by
        rw [List.getD_eq_getElem _ _ hidx, ← List.getLast_eq_getElem hne]
        exact Nat.pos_of_ne_zero (hCl.2 hne)
      have htop_lt : l.getD (l.length - 1) 0 < 2 ^ k := hCl.1.getD_lt (l.length - 1)
      have htop_spos : 0 < Nat.size (l.getD (l.length - 1) 0) := Nat.size_pos.mpr htop_pos
      have htop_sle : Nat.size (l.getD (l.length - 1) 0) ≤ k := Nat.size_le.mpr htop_lt
      have hls : Nat.size (Nat.ofDigits (2 ^ k) l) =
          (l.length - 1) * k + Nat.size (l.getD (l.length - 1) 0) :=
        size_ofDigits_canonical hCl hlpos
      rw [hls]
      simp only [hl0, ↓reduceIte]
      by_cases hlt : p.1 < l.length
      · simp only [hlt, ↓reduceIte]
        refine ⟨?_, fun h => absurd h hl0, fun _ => ⟨htop_pos, htop_lt, hfitl⟩⟩
        simp only [pairBitLength, hl0, ↓reduceIte]
        by_cases hp0 : p.1 = 0
        · simp [hp0]
        · obtain ⟨_, hp2lt, _⟩ := hpos (by omega)
          have hp2s : Nat.size p.2 ≤ k := Nat.size_le.mpr hp2lt
          have hmul : p.1 * k ≤ (l.length - 1) * k := Nat.mul_le_mul_right k (by omega)
          have hsub : (p.1 - 1) * k + k = p.1 * k := by
            cases h1 : p.1 with
            | zero => omega
            | succ m => simp [Nat.succ_mul]
          simp only [hp0, ↓reduceIte]
          omega
      · simp only [hlt, ↓reduceIte]
        by_cases heq : l.length = p.1
        · simp only [heq, ↓reduceIte]
          have hp0 : p.1 ≠ 0 := by omega
          obtain ⟨hp2pos, hp2lt, hpfit⟩ := hpos (by omega)
          by_cases htop : p.2 < l.getD (p.1 - 1) 0
          · simp only [htop, ↓reduceIte]
            have htop' : p.2 < l.getD (l.length - 1) 0 := by rwa [heq]
            have hsle : Nat.size p.2 ≤ Nat.size (l.getD (l.length - 1) 0) :=
              Nat.size_le_size (le_of_lt htop')
            refine ⟨?_, fun h => absurd h hp0, fun _ => ?_⟩
            · simp only [pairBitLength, hp0, ↓reduceIte]
              rw [heq] at hsle; omega
            · rw [← heq]; exact ⟨htop_pos, htop_lt, by omega⟩
          · simp only [htop, ↓reduceIte]
            have htop' : ¬ p.2 < l.getD (l.length - 1) 0 := by rwa [heq]
            have hsle : Nat.size (l.getD (l.length - 1) 0) ≤ Nat.size p.2 :=
              Nat.size_le_size (by omega)
            refine ⟨?_, fun h => absurd h hp0, fun _ => ⟨hp2pos, hp2lt, hpfit⟩⟩
            simp only [pairBitLength, hp0, ↓reduceIte]
            rw [heq] at hsle; omega
        · simp only [heq, ↓reduceIte]
          have hp0 : p.1 ≠ 0 := by omega
          obtain ⟨hp2pos, hp2lt, hpfit⟩ := hpos (by omega)
          have hp2spos : 0 < Nat.size p.2 := Nat.size_pos.mpr hp2pos
          have hmul : l.length * k ≤ (p.1 - 1) * k := Nat.mul_le_mul_right k (by omega)
          have hsub : (l.length - 1) * k + k = l.length * k := by
            cases h1 : l.length with
            | zero => omega
            | succ m => simp [Nat.succ_mul]
          refine ⟨?_, hz, hpos⟩
          simp only [pairBitLength, hp0, ↓reduceIte]
          omega

/-! ### The procedure -/

/-- Compute the bit length of the largest of `m` canonical base-`2 ^ k` long numbers, given their
base pointers at `pPtrs` and limb counts at `pLens`, using a single call to `bitLength` (`bl`). -/
wram_def topBitLength (bl : ℕ) (pPtrs, pLens, m, k) {
  bestLen := 0
  bestTop := 0
  for i in 0 .. m {
    len := mem[pLens + i]
    if 0 < len {
      if bestLen < len {
        ptr := mem[pPtrs + i]
        bestTop := mem[ptr + (len - 1)]
        bestLen := len
      } else {
        if len == bestLen {
          ptr := mem[pPtrs + i]
          ptr := mem[ptr + (len - 1)]
          if bestTop < ptr {
            bestTop := ptr
          }
        }
      }
    }
  }
  res := 0
  if 0 < bestLen {
    b := bl(bestTop)
    res := (bestLen - 1) * k + b
  }
  return res
}

/-- Specification of `topBitLength`: returns `Nat.size (maxLimbsVal k xs)` without modifying memory. -/
def topBitLengthSpec (w : ℕ) : Spec (ℕ × List ℕ × List (List ℕ)) where
  pre := fun (k, ptrs, xs) args => ⨆ (pPtrs : ℕ) (pLens : ℕ),
    ⌜args = [pPtrs, pLens, xs.length, k] ∧ ptrs.length = xs.length ∧ 1 ≤ k ∧ 2 < 2 ^ w ∧
      (∀ l ∈ xs, CanonicalLimbs k l ∧ l.length * k < 2 ^ w)⌝ *
    Assn.list pPtrs ptrs * Assn.list pLens (xs.map List.length) *
    ∏ j ∈ Finset.range xs.length, Assn.list (ptrs.getD j 0) (xs.getD j [])
  post := fun (k, ptrs, xs) args v => ⨆ (pPtrs : ℕ) (pLens : ℕ),
    ⌜args = [pPtrs, pLens, xs.length, k] ∧ v = Nat.size (maxLimbsVal k xs)⌝ *
    Assn.list pPtrs ptrs * Assn.list pLens (xs.map List.length) *
    ∏ j ∈ Finset.range xs.length, Assn.list (ptrs.getD j 0) (xs.getD j [])

/-- `topBitLength` scans `m` numbers in at most `75 * m + 35` steps plus one call of `bitLength`
on `maxTopLimb xs`. -/
theorem topBitLength_meets {w : ℕ} {p : Program} {f bl : ℕ} {T : ℕ → ℕ}
    (hp : p.procs[f]? = some (topBitLength bl))
    (hbl : Meets w p bl ((bitLengthSpec w).withCost fun x _ => T x)) :
    Meets w p f ((topBitLengthSpec w).withCost fun x _ =>
      75 * x.2.2.length + T (maxTopLimb x.2.2) + 50) := by
  sep_enter ⟨k, ptrs, xs⟩ with hptrs hk hw hC
  have hspec := bestPairPrefix_spec hk hC
  sep_step
  sep_step
  sep_for (fun i (t : ℕ × ℕ) => ⟨[pPtrs, pLens, xs.length, k,
      (bestPairPrefix xs i).1, (bestPairPrefix xs i).2, i, t.1, t.2, 0, 0],
      i ≤ xs.length, 65 * (xs.length - i) + T (maxTopLimb xs) + 30,
      [Assn.list pPtrs ptrs, Assn.list pLens (xs.map List.length),
        ∏ j ∈ Finset.range xs.length, Assn.list (ptrs.getD j 0) (xs.getD j [])]⟩)
    with ⟨t1, t2⟩
  · have hmem : i ∈ Finset.range xs.length := Finset.mem_range.mpr hhi
    have hxi : xs.getD i [] = xs[i]'hhi := List.getD_eq_getElem xs [] hhi
    have hpi : ptrs.getD i 0 = ptrs[i]'(by omega) := List.getD_eq_getElem ptrs 0 (by omega)
    have hlen_i : (xs.map List.length)[i]'(by simp; omega) = (xs.getD i []).length := by
      rw [List.getElem_map, hxi]
    sep_step
    have hlen_eq : len = (xs.getD i []).length := by rw [hlen, hlen_i]
    sep_step
    · -- 0 < len
      have hl0 : (xs.getD i []).length ≠ 0 := by omega
      have hidx_eq : ptrs[i]'(by omega) + (len - 1) - ptrs.getD i 0 = (xs.getD i []).length - 1 := by
        omega
      have htop_getD : (xs.getD i [])[ptrs[i]'(by omega) + (len - 1) - ptrs.getD i 0]'(by omega) =
          (xs.getD i []).getD ((xs.getD i []).length - 1) 0 := by
        rw [List.getD_eq_getElem _ _ (by omega : (xs.getD i []).length - 1 < (xs.getD i []).length)]
        congr 1
      sep_step
      · -- bestLen < len
        have hlt' : (bestPairPrefix xs i).1 < (xs.getD i []).length := by omega
        have hstep : bestPairPrefix xs (i + 1) =
            ((xs.getD i []).length, (xs.getD i []).getD ((xs.getD i []).length - 1) 0) := by
          simp only [bestPairPrefix, bestPairStep, hl0, hlt', ↓reduceIte]
        sep_step
        sep_apply Assn.prod_eq_mul_erase hmem
          (fun j => Assn.list (ptrs.getD j 0) (xs.getD j []))
        sep_step
        sep_apply (Assn.prod_eq_mul_erase hmem
          (fun j => Assn.list (ptrs.getD j 0) (xs.getD j []))).symm
        sep_run
        rw [hstep, hbestTop]; exact htop_getD
      · -- ¬ bestLen < len
        have hlt' : ¬ (bestPairPrefix xs i).1 < (xs.getD i []).length := by omega
        sep_step
        · -- len == bestLen
          have heq' : (xs.getD i []).length = (bestPairPrefix xs i).1 := by omega
          sep_step
          sep_apply Assn.prod_eq_mul_erase hmem
            (fun j => Assn.list (ptrs.getD j 0) (xs.getD j []))
          sep_step
          sep_apply (Assn.prod_eq_mul_erase hmem
            (fun j => Assn.list (ptrs.getD j 0) (xs.getD j []))).symm
          sep_step
          · -- bestTop < ptr
            have htop' : (bestPairPrefix xs i).2 <
                (xs.getD i []).getD ((xs.getD i []).length - 1) 0 := by
              rw [← htop_getD, ← hptr]; exact hcond_3
            have hstep : bestPairPrefix xs (i + 1) =
                ((bestPairPrefix xs i).1, (xs.getD i []).getD ((xs.getD i []).length - 1) 0) := by
              rw [show bestPairPrefix xs (i + 1) = bestPairStep (bestPairPrefix xs i) (xs.getD i []) from rfl]
              unfold bestPairStep
              rw [ite_eq_right_iff.mpr (fun h => absurd h hl0),
                ite_eq_right_iff.mpr (fun h => absurd h hlt'),
                ite_eq_left_iff.mpr (fun h => absurd heq' h),
                ite_eq_left_iff.mpr (fun h => absurd htop' h)]
            sep_run
            rw [hstep, hptr]; exact htop_getD
          · -- ¬ bestTop < ptr
            have htop' : ¬ (bestPairPrefix xs i).2 <
                (xs.getD i []).getD ((xs.getD i []).length - 1) 0 := by
              rw [← htop_getD, ← hptr]; omega
            have hstep : bestPairPrefix xs (i + 1) = bestPairPrefix xs i := by
              rw [show bestPairPrefix xs (i + 1) = bestPairStep (bestPairPrefix xs i) (xs.getD i []) from rfl]
              unfold bestPairStep
              rw [ite_eq_right_iff.mpr (fun h => absurd h hl0),
                ite_eq_right_iff.mpr (fun h => absurd h hlt'),
                ite_eq_left_iff.mpr (fun h => absurd heq' h),
                ite_eq_right_iff.mpr (fun h => absurd h htop')]
            sep_run
        · -- len ≠ bestLen
          have hne' : (xs.getD i []).length ≠ (bestPairPrefix xs i).1 := by omega
          have hstep : bestPairPrefix xs (i + 1) = bestPairPrefix xs i := by
            rw [show bestPairPrefix xs (i + 1) = bestPairStep (bestPairPrefix xs i) (xs.getD i []) from rfl]
            unfold bestPairStep
            rw [ite_eq_right_iff.mpr (fun h => absurd h hl0),
              ite_eq_right_iff.mpr (fun h => absurd h hlt'),
              ite_eq_right_iff.mpr (fun h => absurd h hne')]
          sep_run
    · -- len = 0
      have hl0 : (xs.getD i []).length = 0 := by omega
      have hstep : bestPairPrefix xs (i + 1) = bestPairPrefix xs i := by
        rw [show bestPairPrefix xs (i + 1) = bestPairStep (bestPairPrefix xs i) (xs.getD i []) from rfl]
        unfold bestPairStep
        rw [ite_eq_left_iff.mpr (fun h => absurd hl0 h)]
      sep_run
  · obtain ⟨hsize, _, hpos⟩ := hspec xs.length le_rfl
    rw [List.take_length] at hsize
    sep_step
    sep_step
    · -- 0 < bestLen
      obtain ⟨_, hp2lt, hpfit⟩ := hpos hcond
      have hbl_le : Nat.size (bestPairPrefix xs xs.length).2 ≤ k := Nat.size_le.mpr hp2lt
      have hsub : ((bestPairPrefix xs xs.length).1 - 1) * k + k =
          (bestPairPrefix xs xs.length).1 * k := by
        cases h1 : (bestPairPrefix xs xs.length).1 with
        | zero => omega
        | succ m => simp [Nat.succ_mul]
      have hmul_lt : ((bestPairPrefix xs xs.length).1 - 1) * k < 2 ^ w := by omega
      have hres_lt : ((bestPairPrefix xs xs.length).1 - 1) * k +
          Nat.size (bestPairPrefix xs xs.length).2 < 2 ^ w := by omega
      sep_run
      · unfold maxTopLimb; omega
      · rw [hres, hb, ← hsize]
        simp [pairBitLength, show (bestPairPrefix xs xs.length).1 ≠ 0 by omega]
    · -- bestLen = 0
      sep_run
      rw [← hsize]
      simp [pairBitLength, show (bestPairPrefix xs xs.length).1 = 0 by omega]

/-- `topBitLength` runs in `O(m + Nat.size (maxTopLimb xs) + 1)` steps when `bl` is `bitLength`. -/
theorem topBitLength_meetsO_size {w : ℕ} {p : Program} {f bl : ℕ}
    (hp : p.procs[f]? = some (topBitLength bl))
    (hbl : MeetsO w p bl (bitLengthSpec w) fun x _ => Nat.size x + 1) :
    MeetsO w p f (topBitLengthSpec w) fun x _ =>
      x.2.2.length + Nat.size (maxTopLimb x.2.2) + 1 := by
  refine MeetsO.of_callee hbl fun K hK => ⟨_, topBitLength_meets hp hK, K + 75, fun xa => ?_⟩
  dsimp only
  nlinarith

/-- `topBitLength` runs in `O(m + k + 1)` steps when `bl` is `bitLength`. -/
theorem topBitLength_meetsO {w : ℕ} {p : Program} {f bl : ℕ}
    (hp : p.procs[f]? = some (topBitLength bl))
    (hbl : MeetsO w p bl (bitLengthSpec w) fun x _ => Nat.size x + 1) :
    MeetsO w p f (topBitLengthSpec w) fun x _ => x.2.2.length + x.1 + 1 := by
  obtain ⟨K, hK⟩ := topBitLength_meetsO_size hp hbl
  refine MeetsO.of_meets_on hK
    (P := fun x _ => 1 ≤ x.1 ∧ ∀ l ∈ x.2.2, CanonicalLimbs x.1 l ∧ l.length * x.1 < 2 ^ w) ?_ ?_
  · rintro ⟨k, ptrs, xs⟩ args
    simp only [topBitLengthSpec]
    refine Assn.iSup_le_iff'.mpr fun pPtrs => Assn.iSup_le_iff'.mpr fun pLens => ?_
    rw [mul_assoc, mul_assoc]
    intro h c hx
    obtain ⟨h1, h2, c1, c2, -, rfl, rfl, ⟨hpure, -, -⟩, -⟩ := hx
    exact ⟨Heap.empty, h1.union h2, 0, c1 + c2, Heap.disjoint_empty_left _,
      (Heap.empty_union _).symm, (zero_add _).symm, ⟨⟨hpure.2.2.1, hpure.2.2.2.2⟩, rfl, rfl⟩,
      trivial⟩
  · refine ⟨K, fun xa hxa => ?_⟩
    obtain ⟨hk, hC⟩ := hxa
    obtain ⟨_, hz, hpos⟩ := bestPairPrefix_spec hk hC xa.1.2.2.length le_rfl
    have htop_le : Nat.size (maxTopLimb xa.1.2.2) ≤ xa.1.1 := by
      unfold maxTopLimb
      by_cases h0 : (bestPairPrefix xa.1.2.2 xa.1.2.2.length).1 = 0
      · rw [hz h0, Nat.size_zero]; omega
      · exact Nat.size_le.mpr (hpos (by omega)).2.1
    dsimp only
    exact Nat.mul_le_mul_left K (by omega)

/-! ### Module -/

/-- Module for `topBitLength`, parameterized by its own name and `bitLength`'s name. -/
def topBitLengthMod {ι : Type} (name blName : ι) : Module ι :=
  ⟨[(name, fun idx => topBitLength (idx blName))]⟩

theorem topBitLengthMod_noRand {ι : Type} (name blName : ι) :
    (topBitLengthMod name blName).NoRand := by
  wram_no_rand

/-- In any program placing `topBitLengthMod name blName` alongside `bitLength`,
`topBitLength` runs in `O(m + k + 1)` steps. -/
theorem topBitLengthMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ} {name blName : ι}
    (hp : (topBitLengthMod name blName).Placed p idx)
    (hbl : MeetsO w p (idx blName) (bitLengthSpec w) fun x _ => Nat.size x + 1) :
    MeetsO w p (idx name) (topBitLengthSpec w) (fun x _ => x.2.2.length + x.1 + 1) :=
  topBitLength_meetsO
    (hp.get (n := name) (b := fun idx => topBitLength (idx blName)) (by simp [topBitLengthMod]))
    hbl

end MinCostFlow.NarrowProg
