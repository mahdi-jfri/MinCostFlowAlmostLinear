module

public import Mathlib.Data.Nat.Log
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Pair arrays and max-heap invariants for in-place heapsort

This file defines `readPairs`, `swapPairs`, and the max-heap predicates (`HeapExcept`,
`HeapGrand`, `MaxHeapOn`) used by `OrdStoreSort.lean` to sort `(pos, node)` pairs in place.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

/-! ### Array of pairs in memory -/

/-- Read `n` pairs `(pos, node)` starting at address `arr`. -/
def readPairs (mem : ℕ → ℕ) (arr : ℕ) (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).map fun i => (mem (arr + 2 * i), mem (arr + 2 * i + 1))

theorem readPairs_length (mem : ℕ → ℕ) (arr n : ℕ) : (readPairs mem arr n).length = n := by
  simp [readPairs]

theorem readPairs_getElem (mem : ℕ → ℕ) (arr n i : ℕ) (hi : i < (readPairs mem arr n).length) :
    (readPairs mem arr n)[i]'hi = (mem (arr + 2 * i), mem (arr + 2 * i + 1)) := by
  simp [readPairs]

theorem readPairs_congr {m₁ m₂ : ℕ → ℕ} {arr n : ℕ}
    (h : ∀ a, arr ≤ a → a < arr + 2 * n → m₁ a = m₂ a) :
    readPairs m₁ arr n = readPairs m₂ arr n := by
  unfold readPairs
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [h (arr + 2 * i) (by omega) (by omega), h (arr + 2 * i + 1) (by omega) (by omega)]

/-- Swap the two pairs at indices `i` and `j` in a list of pairs. -/
def swapPairs (xs : List (ℕ × ℕ)) (i j : ℕ) : List (ℕ × ℕ) :=
  let a := xs.getD i (0, 0)
  let b := xs.getD j (0, 0)
  (xs.set i b).set j a

theorem swapPairs_length (xs : List (ℕ × ℕ)) (i j : ℕ) :
    (swapPairs xs i j).length = xs.length := by
  simp [swapPairs]

theorem swapPairs_getElem {xs : List (ℕ × ℕ)} {i j k : ℕ}
    (hi : i < xs.length) (hj : j < xs.length) (hk : k < xs.length) :
    (swapPairs xs i j)[k]'(by rw [swapPairs_length]; exact hk) =
      if k = j then xs[i]'hi else if k = i then xs[j]'hj else xs[k]'hk := by
  have hgi : xs.getD i (0, 0) = xs[i]'hi := List.getD_eq_getElem _ _ hi
  have hgj : xs.getD j (0, 0) = xs[j]'hj := List.getD_eq_getElem _ _ hj
  change ((xs.set i (xs.getD j (0, 0))).set j (xs.getD i (0, 0)))[k]'(by simp [hk]) = _
  by_cases hkj : k = j
  · subst hkj
    rw [List.getElem_set_self, hgi]
    simp
  · rw [List.getElem_set_ne (Ne.symm hkj)]
    by_cases hki : k = i
    · subst hki
      rw [List.getElem_set_self, hgj]
      simp [hkj]
    · rw [List.getElem_set_ne (Ne.symm hki)]
      simp [hkj, hki]

theorem swapPairs_perm {xs : List (ℕ × ℕ)} {i j : ℕ} (hi : i < xs.length) (hj : j < xs.length) :
    (swapPairs xs i j).Perm xs := by
  by_cases hij : i = j
  · subst hij
    have heq : swapPairs xs i i = xs := by
      apply List.ext_getElem (swapPairs_length xs i i)
      intro k hk _
      rw [swapPairs_getElem hi hi (by simpa [swapPairs_length] using hk)]
      split_ifs with h1 <;> simp_all
    rw [heq]
  · refine List.perm_iff_count.mpr fun z => ?_
    have hcount : ∀ (l : List (ℕ × ℕ)), l.count z =
        ((Finset.range l.length).filter fun k => l[k]?.getD (0, 0) = z).card := by
      intro l
      induction l with
      | nil => simp
      | cons a tl ih =>
        rw [List.count_cons, ih]
        have hshift : (Finset.range (tl.length + 1)).filter (fun k => (a :: tl)[k]?.getD (0, 0) = z) =
            (if a = z then {0} else ∅) ∪
              ((Finset.range tl.length).filter (fun k => tl[k]?.getD (0, 0) = z)).image (· + 1) := by
          ext k
          cases k with
          | zero =>
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image,
              Nat.add_eq_zero_iff, one_ne_zero, and_false, exists_false, or_false,
              List.getElem?_cons_zero, Option.getD_some]
            by_cases haz : a = z <;> simp [haz]
          | succ k =>
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image,
              Nat.succ_lt_succ_iff, List.getElem?_cons_succ, Nat.add_right_cancel_iff,
              exists_eq_right]
            by_cases haz : a = z <;> simp [haz]
        rw [List.length_cons, hshift]
        have hdisj : Disjoint (if a = z then ({0} : Finset ℕ) else ∅)
            (((Finset.range tl.length).filter (fun k => tl[k]?.getD (0, 0) = z)).image (· + 1)) := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          rcases Finset.mem_image.mp hx2 with ⟨k, -, rfl⟩
          split_ifs at hx1 <;> simp at hx1
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ Nat.succ_injective]
        by_cases haz : a = z
        · subst haz; simp; omega
        · simp [haz, beq_false_of_ne haz]
    rw [hcount, hcount, swapPairs_length]
    let f : ℕ → ℕ := fun k => if k = i then j else if k = j then i else k
    refine Finset.card_bij (fun k _ => f k) ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk ⊢
      refine ⟨by dsimp [f]; split_ifs <;> omega, ?_⟩
      have hget : ((swapPairs xs i j)[k]?).getD (0, 0) = (xs[f k]?).getD (0, 0) := by
        rw [List.getElem?_eq_getElem (by rw [swapPairs_length]; exact hk.1), Option.getD_some]
        rw [swapPairs_getElem hi hj hk.1]
        dsimp only [f]
        by_cases hki : k = i
        · subst hki; simp [hij, List.getElem?_eq_getElem hj]
        · by_cases hkj : k = j
          · subst hkj; simp [hki, List.getElem?_eq_getElem hi]
          · simp [hki, hkj, List.getElem?_eq_getElem hk.1]
      rw [← hget]; exact hk.2
    · intro a _ b _ hab
      dsimp only [f] at hab
      split_ifs at hab <;> omega
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      refine ⟨f k, ?_, by dsimp only [f]; split_ifs <;> omega⟩
      rw [Finset.mem_filter, Finset.mem_range]
      have hfk : f k < xs.length := by dsimp only [f]; split_ifs <;> omega
      refine ⟨hfk, ?_⟩
      rw [List.getElem?_eq_getElem (by rw [swapPairs_length]; exact hfk), Option.getD_some]
      rw [swapPairs_getElem hi hj hfk]
      have heq : (if f k = j then xs[i]'hi else if f k = i then xs[j]'hj else xs[f k]'hfk) =
          xs[k]'hk.1 := by
        dsimp only [f]
        by_cases hki : k = i
        · subst hki; simp
        · by_cases hkj : k = j
          · subst hkj; simp [hki, hij]
          · simp [hki, hkj]
      rw [heq]
      simpa [List.getElem?_eq_getElem hk.1] using hk.2

/-! ### Max-heap invariants -/

/-- Every node `j` with `lo ≤ j` and `j ≠ idx` satisfies the max-heap inequality with its
children in `[0, hi)`. -/
def HeapExcept (xs : List (ℕ × ℕ)) (lo hi idx : ℕ) : Prop :=
  ∀ j, lo ≤ j → j ≠ idx →
    (∀ h1 : 2 * j + 1 < hi, ∀ h1' : 2 * j + 1 < xs.length, ∀ hj : j < xs.length,
      (xs[2 * j + 1]'h1').1 ≤ (xs[j]'hj).1) ∧
    (∀ h2 : 2 * j + 2 < hi, ∀ h2' : 2 * j + 2 < xs.length, ∀ hj : j < xs.length,
      (xs[2 * j + 2]'h2').1 ≤ (xs[j]'hj).1)

/-- If `idx` has a parent `p ≥ lo`, then both children of `idx` (within `hi`) have key at most
`xs[p].1`. -/
def HeapGrand (xs : List (ℕ × ℕ)) (lo hi idx : ℕ) : Prop :=
  ∀ p, lo ≤ p → (idx = 2 * p + 1 ∨ idx = 2 * p + 2) → ∀ hp : p < xs.length,
    (∀ h1 : 2 * idx + 1 < hi, ∀ h1' : 2 * idx + 1 < xs.length,
      (xs[2 * idx + 1]'h1').1 ≤ (xs[p]'hp).1) ∧
    (∀ h2 : 2 * idx + 2 < hi, ∀ h2' : 2 * idx + 2 < xs.length,
      (xs[2 * idx + 2]'h2').1 ≤ (xs[p]'hp).1)

/-- Full max-heap property on `[lo, hi)`. -/
def MaxHeapOn (xs : List (ℕ × ℕ)) (lo hi : ℕ) : Prop :=
  ∀ j, lo ≤ j →
    (∀ h1 : 2 * j + 1 < hi, ∀ h1' : 2 * j + 1 < xs.length, ∀ hj : j < xs.length,
      (xs[2 * j + 1]'h1').1 ≤ (xs[j]'hj).1) ∧
    (∀ h2 : 2 * j + 2 < hi, ∀ h2' : 2 * j + 2 < xs.length, ∀ hj : j < xs.length,
      (xs[2 * j + 2]'h2').1 ≤ (xs[j]'hj).1)

theorem maxHeapOn_of_except {xs : List (ℕ × ℕ)} {lo hi idx : ℕ}
    (hex : HeapExcept xs lo hi idx)
    (hidx1 : ∀ h1 : 2 * idx + 1 < hi, ∀ h1' : 2 * idx + 1 < xs.length, ∀ hi' : idx < xs.length,
      (xs[2 * idx + 1]'h1').1 ≤ (xs[idx]'hi').1)
    (hidx2 : ∀ h2 : 2 * idx + 2 < hi, ∀ h2' : 2 * idx + 2 < xs.length, ∀ hi' : idx < xs.length,
      (xs[2 * idx + 2]'h2').1 ≤ (xs[idx]'hi').1) :
    MaxHeapOn xs lo hi := by
  intro j hj
  by_cases hji : j = idx
  · subst hji; exact ⟨hidx1, hidx2⟩
  · exact hex j hj hji

theorem maxHeapOn_top_max {xs : List (ℕ × ℕ)} {hi : ℕ} (hhi : hi ≤ xs.length)
    (hheap : MaxHeapOn xs 0 hi) :
    ∀ j (hj : j < hi), (xs[j]'(lt_of_lt_of_le hj hhi)).1 ≤ (xs[0]'(by omega)).1 := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact le_refl _
    · set p := (j - 1) / 2
      have hplt : p < j := by omega
      have hphi : p < hi := lt_trans hplt hj
      have hstep : (xs[j]'(lt_of_lt_of_le hj hhi)).1 ≤ (xs[p]'(lt_of_lt_of_le hphi hhi)).1 := by
        have hp := hheap p (Nat.zero_le _)
        by_cases hodd : j = 2 * p + 1
        · have h1 := hp.1 (by omega) (by omega) (lt_of_lt_of_le hphi hhi)
          have heq : xs[j]'(lt_of_lt_of_le hj hhi) = xs[2 * p + 1]'(by omega) := by
            congr 1
          rw [heq]; exact h1
        · have heven : j = 2 * p + 2 := by omega
          have h2 := hp.2 (by omega) (by omega) (lt_of_lt_of_le hphi hhi)
          have heq : xs[j]'(lt_of_lt_of_le hj hhi) = xs[2 * p + 2]'(by omega) := by
            congr 1
          rw [heq]; exact h2
      exact le_trans hstep (ih p hplt hphi)

theorem heap_swap_step {xs : List (ℕ × ℕ)} {lo hi idx best : ℕ}
    (hhi : hi ≤ xs.length) (hlo : lo ≤ idx) (hidx : idx < hi)
    (hbest_ch : best = 2 * idx + 1 ∨ best = 2 * idx + 2) (hbest_lt : best < hi)
    (hex : HeapExcept xs lo hi idx) (hgr : HeapGrand xs lo hi idx)
    (hgt : (xs[idx]'(lt_of_lt_of_le hidx hhi)).1 < (xs[best]'(lt_of_lt_of_le hbest_lt hhi)).1)
    (hbest_ge1 : ∀ h1 : 2 * idx + 1 < hi,
      (xs[2 * idx + 1]'(lt_of_lt_of_le h1 hhi)).1 ≤ (xs[best]'(lt_of_lt_of_le hbest_lt hhi)).1)
    (hbest_ge2 : ∀ h2 : 2 * idx + 2 < hi,
      (xs[2 * idx + 2]'(lt_of_lt_of_le h2 hhi)).1 ≤ (xs[best]'(lt_of_lt_of_le hbest_lt hhi)).1) :
    HeapExcept (swapPairs xs idx best) lo hi best ∧
      HeapGrand (swapPairs xs idx best) lo hi best := by
  have hi_len : idx < xs.length := lt_of_lt_of_le hidx hhi
  have hb_len : best < xs.length := lt_of_lt_of_le hbest_lt hhi
  have hne_ib : idx ≠ best := by omega
  have hget : ∀ k (hk : k < xs.length),
      (swapPairs xs idx best)[k]'(by rw [swapPairs_length]; exact hk) =
        if k = best then xs[idx]'hi_len else if k = idx then xs[best]'hb_len else xs[k]'hk :=
    fun k hk => swapPairs_getElem hi_len hb_len hk
  constructor
  · intro j hjlo hjne
    have hch : ∀ c (hc : c < hi) (hc' : c < (swapPairs xs idx best).length)
        (hj' : j < (swapPairs xs idx best).length),
        (c = 2 * j + 1 ∨ c = 2 * j + 2) →
        ((swapPairs xs idx best)[c]'hc').1 ≤ ((swapPairs xs idx best)[j]'hj').1 := by
      intro c hc hc' hj' hcj
      have hc_len : c < xs.length := lt_of_lt_of_le hc hhi
      have hj_len : j < xs.length := by rwa [swapPairs_length] at hj'
      rw [hget c hc_len, hget j hj_len]
      rw [ite_eq_right hjne]
      by_cases hji : j = idx
      · subst hji
        rw [ite_eq_left rfl]
        by_cases hcb : c = best
        · subst hcb; rw [ite_eq_left rfl]; exact le_of_lt hgt
        · rw [ite_eq_right hcb, ite_eq_right (by omega)]
          rcases hcj with rfl | rfl
          · exact hbest_ge1 hc
          · exact hbest_ge2 hc
      · rw [ite_eq_right hji]
        by_cases hcb : c = best
        · subst hcb
          exfalso; omega
        · rw [ite_eq_right hcb]
          by_cases hci : c = idx
          · subst hci
            rw [ite_eq_left rfl]
            have hgp := hgr j hjlo hcj hj_len
            rcases hbest_ch with rfl | rfl
            · exact hgp.1 hbest_lt hb_len
            · exact hgp.2 hbest_lt hb_len
          · rw [ite_eq_right hci]
            have hjp := hex j hjlo hji
            rcases hcj with rfl | rfl
            · exact hjp.1 hc hc_len hj_len
            · exact hjp.2 hc hc_len hj_len
    exact ⟨fun h1 h1' hj' => hch _ h1 h1' hj' (Or.inl rfl),
           fun h2 h2' hj' => hch _ h2 h2' hj' (Or.inr rfl)⟩
  · intro p hplo hbp hp'
    have hpi : p = idx := by omega
    subst hpi
    have hp_len : p < xs.length := by rwa [swapPairs_length] at hp'
    constructor
    · intro h1 h1'
      have h1_len : 2 * best + 1 < xs.length := lt_of_lt_of_le h1 hhi
      rw [hget _ h1_len, hget p hp_len]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hne_ib, ite_eq_left rfl]
      exact (hex best (by omega) (Ne.symm hne_ib)).1 h1 h1_len hb_len
    · intro h2 h2'
      have h2_len : 2 * best + 2 < xs.length := lt_of_lt_of_le h2 hhi
      rw [hget _ h2_len, hget p hp_len]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hne_ib, ite_eq_left rfl]
      exact (hex best (by omega) (Ne.symm hne_ib)).2 h2 h2_len hb_len

/-- Remaining height of index `idx` in a heap of size `hi`: at most `Nat.log 2 (hi + 1)`. -/
def siftMeasure (idx hi : ℕ) : ℕ := Nat.log 2 (hi + 1) - Nat.log 2 (idx + 1)

theorem siftMeasure_child_lt {idx ch hi : ℕ} (hch : ch = 2 * idx + 1 ∨ ch = 2 * idx + 2)
    (hlt : ch < hi) :
    siftMeasure ch hi < siftMeasure idx hi := by
  unfold siftMeasure
  have h1 : 2 * (idx + 1) ≤ ch + 1 := by omega
  have h2 : Nat.log 2 (idx + 1) + 1 ≤ Nat.log 2 (ch + 1) := by
    rw [← Nat.log_mul_base (by decide : 1 < 2) (by omega : idx + 1 ≠ 0)]
    exact Nat.log_mono_right (by omega)
  have h3 : Nat.log 2 (ch + 1) ≤ Nat.log 2 (hi + 1) := Nat.log_mono_right (by omega)
  omega

/-- Updating memory by swapping pairs `i` and `j` at `arr` produces `swapPairs` on `readPairs`. -/
theorem readPairs_swapMem {mem : ℕ → ℕ} {arr n i j : ℕ} (hi : i < n) (hj : j < n) (hne : i ≠ j) :
    let m1 := Function.update mem (arr + 2 * i) (mem (arr + 2 * j))
    let m2 := Function.update m1 (arr + 2 * i + 1) (mem (arr + 2 * j + 1))
    let m3 := Function.update m2 (arr + 2 * j) (mem (arr + 2 * i))
    let m4 := Function.update m3 (arr + 2 * j + 1) (mem (arr + 2 * i + 1))
    readPairs m4 arr n = swapPairs (readPairs mem arr n) i j ∧
      (∀ a, (a < arr ∨ arr + 2 * n ≤ a) → m4 a = mem a) := by
  dsimp only
  constructor
  · apply List.ext_getElem (by simp [readPairs_length, swapPairs_length])
    intro k hk _
    have hk' : k < n := by simpa [readPairs_length] using hk
    rw [readPairs_getElem, swapPairs_getElem (by simpa [readPairs_length] using hi)
        (by simpa [readPairs_length] using hj) (by simpa [readPairs_length] using hk')]
    simp only [readPairs_getElem]
    by_cases hkj : k = j
    · subst hkj
      have h1 : arr + 2 * k ≠ arr + 2 * k + 1 := by omega
      simp [hne, h1, Function.update_apply]
    · by_cases hki : k = i
      · subst hki
        have h1 : arr + 2 * k ≠ arr + 2 * j + 1 := by omega
        have h2 : arr + 2 * k ≠ arr + 2 * j := by omega
        have h3 : arr + 2 * k + 1 ≠ arr + 2 * j + 1 := by omega
        have h4 : arr + 2 * k + 1 ≠ arr + 2 * j := by omega
        have h5 : arr + 2 * k ≠ arr + 2 * k + 1 := by omega
        simp [h1, h2, h3, h4, h5, hkj, Function.update_apply]
      · have h1 : arr + 2 * k ≠ arr + 2 * j + 1 := by omega
        have h2 : arr + 2 * k ≠ arr + 2 * j := by omega
        have h3 : arr + 2 * k ≠ arr + 2 * i + 1 := by omega
        have h4 : arr + 2 * k ≠ arr + 2 * i := by omega
        have h5 : arr + 2 * k + 1 ≠ arr + 2 * j + 1 := by omega
        have h6 : arr + 2 * k + 1 ≠ arr + 2 * j := by omega
        have h7 : arr + 2 * k + 1 ≠ arr + 2 * i + 1 := by omega
        have h8 : arr + 2 * k + 1 ≠ arr + 2 * i := by omega
        simp [h1, h2, h3, h4, h5, h6, h7, h8, hki, hkj, Function.update_apply]
  · intro a ha
    have h1 : a ≠ arr + 2 * j + 1 := by omega
    have h2 : a ≠ arr + 2 * j := by omega
    have h3 : a ≠ arr + 2 * i + 1 := by omega
    have h4 : a ≠ arr + 2 * i := by omega
    simp [h1, h2, h3, h4, Function.update_apply]

theorem maxHeapOn_suffix_step {xs : List (ℕ × ℕ)} {i n : ℕ}
    (hheap : MaxHeapOn xs (i + 1) n) :
    HeapExcept xs i n i ∧ HeapGrand xs i n i := by
  refine ⟨fun j hj hne => hheap j (by omega), fun p hp hch _ => False.elim (by omega)⟩

theorem extract_step_inv {xs : List (ℕ × ℕ)} {e n : ℕ}
    (hlen : xs.length = n) (he : e + 1 ≤ n)
    (hheap : MaxHeapOn xs 0 (e + 1))
    (hsorted : (xs.drop (e + 1)).Pairwise fun a b => a.1 ≤ b.1)
    (hpart : ∀ a ∈ xs.take (e + 1), ∀ b ∈ xs.drop (e + 1), a.1 ≤ b.1) :
    let xs₁ := swapPairs xs 0 e
    (xs₁.drop e).Pairwise (fun a b => a.1 ≤ b.1) ∧
    (∀ a ∈ xs₁.take e, ∀ b ∈ xs₁.drop e, a.1 ≤ b.1) ∧
    (e > 0 → HeapExcept (xs₁.take e) 0 e 0 ∧ HeapGrand (xs₁.take e) 0 e 0) := by
  dsimp only
  have h0 : 0 < xs.length := by omega
  have he_len : e < xs.length := by omega
  have hxs1_len : (swapPairs xs 0 e).length = n := by rw [swapPairs_length, hlen]
  have hdrop_eq : (swapPairs xs 0 e).drop e = xs[0]'h0 :: xs.drop (e + 1) := by
    apply List.ext_getElem
    · simp [hxs1_len, hlen]; omega
    · intro k hk _
      simp only [List.length_drop, hxs1_len] at hk
      simp only [List.getElem_drop]
      rw [swapPairs_getElem h0 he_len (by omega)]
      cases k with
      | zero => simp
      | succ k =>
        have h1 : e + (k + 1) ≠ e := by omega
        have h2 : e + (k + 1) ≠ 0 := by omega
        simp only [h1, h2, ↓reduceIte, List.getElem_cons_succ, List.getElem_drop]
        congr 1; omega
  have htop_le_drop : ∀ b ∈ xs.drop (e + 1), (xs[0]'h0).1 ≤ b.1 := fun b hb =>
    hpart (xs[0]'h0) (by
      have h0t : 0 < (xs.take (e + 1)).length := by simp [hlen]; omega
      have := List.getElem_mem h0t
      simpa [List.getElem_take] using this) b hb
  have htake_le_top : ∀ a ∈ (swapPairs xs 0 e).take e, a.1 ≤ (xs[0]'h0).1 := by
    intro a ha
    rcases List.getElem_of_mem ha with ⟨k, hk, rfl⟩
    simp only [List.length_take, hxs1_len] at hk
    have hke : k < e := by omega
    simp only [List.getElem_take]
    rw [swapPairs_getElem h0 he_len (by omega)]
    rw [ite_eq_right (by omega)]
    by_cases hk0 : k = 0
    · subst hk0; rw [ite_eq_left rfl]; exact maxHeapOn_top_max (by omega) hheap e (by omega)
    · rw [ite_eq_right hk0]; exact maxHeapOn_top_max (by omega) hheap k (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [hdrop_eq, List.pairwise_cons]
    exact ⟨htop_le_drop, hsorted⟩
  · intro a ha b hb
    rw [hdrop_eq, List.mem_cons] at hb
    rcases hb with rfl | hb'
    · exact htake_le_top a ha
    · exact le_trans (htake_le_top a ha) (htop_le_drop b hb')
  · intro _
    refine ⟨fun j _ hj0 => ?_, fun p _ hch _ => False.elim (by omega)⟩
    have hjp := hheap j (Nat.zero_le _)
    constructor
    · intro h1 h1' hj'
      simp only [List.getElem_take]
      rw [swapPairs_getElem h0 he_len (by omega), swapPairs_getElem h0 he_len (by omega)]
      simp only [show 2 * j + 1 ≠ e by omega, show 2 * j + 1 ≠ 0 by omega,
        show j ≠ e by omega, hj0, ↓reduceIte]
      exact hjp.1 (by omega) (by omega) (by omega)
    · intro h2 h2' hj'
      simp only [List.getElem_take]
      rw [swapPairs_getElem h0 he_len (by omega), swapPairs_getElem h0 he_len (by omega)]
      simp only [show 2 * j + 2 ≠ e by omega, show 2 * j + 2 ≠ 0 by omega,
        show j ≠ e by omega, hj0, ↓reduceIte]
      exact hjp.2 (by omega) (by omega) (by omega)

end MinCostFlow.SparseCore.Program
