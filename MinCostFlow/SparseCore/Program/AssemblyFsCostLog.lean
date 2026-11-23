module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepBunPrepProg
public import MinCostFlow.SparseCore.Program.OrdStoreContract
public import MinCostFlow.SparseCore.BundleTreeCore
public import MinCostFlow.Chain.SparseCoreTool

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Pure logarithmic, threshold, and split-group size bounds (`AssemblyFsCostLog`)

Pure arithmetic helpers shared by the Phase 1–3 and Phase 4 cost proofs of the first step:

* `log_two_plus_one_ge_two`, `bundleLogFactor_ge_four`, `capExp_pos_of_caps`
* `ordStoreLog_le_capExp`, `log_four_mul_eCap_le`, `log_two_mul_le_capExp`, `log_succ_le_capExp`
* `updateThreshold_nat_le`, `log_del_le`
* `splitGroupsOf_length_le`, `groupsTotalLen_splitGroupsOf_le`
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.SparseCore MinCostFlow.Chain

public section

lemma log_two_plus_one_ge_two (M N : ℕ) : 2 ≤ Nat.log 2 (M + N + 2) + 1 := by
  have h1 : 1 ≤ Nat.log 2 (M + N + 2) := Nat.le_log_of_pow_le (by omega) (by omega)
  omega

lemma bundleLogFactor_ge_four (M N : ℕ) : 4 ≤ bundleLogFactor M N := by
  unfold bundleLogFactor
  have h := log_two_plus_one_ge_two M N
  nlinarith

lemma capExp_pos_of_caps {M N vCap eCap capExp : ℕ}
    (h : vCap + eCap + 2 ≤ (M + N + 2) ^ capExp) : 1 ≤ capExp := by
  by_contra hc
  have h0 : capExp = 0 := by omega
  subst h0
  simp at h

lemma ordStoreLog_le_capExp {M N vCap eCap capExp : ℕ}
    (h : vCap + eCap + 2 ≤ (M + N + 2) ^ capExp) :
    ordStoreLog eCap ≤ capExp * (Nat.log 2 (M + N + 2) + 1) := by
  have hpos : 0 < capExp := capExp_pos_of_caps h
  have hlt1 : M + N + 2 < 2 ^ (Nat.log 2 (M + N + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by omega) (M + N + 2)
  have hlt2 : (M + N + 2) ^ capExp < (2 ^ (Nat.log 2 (M + N + 2) + 1)) ^ capExp :=
    Nat.pow_lt_pow_left hlt1 (by omega)
  rw [← pow_mul, mul_comm (Nat.log 2 (M + N + 2) + 1) capExp] at hlt2
  have hlt3 : eCap + 2 < 2 ^ (capExp * (Nat.log 2 (M + N + 2) + 1)) := by omega
  have hlog : Nat.log 2 (eCap + 2) < capExp * (Nat.log 2 (M + N + 2) + 1) :=
    Nat.log_lt_of_lt_pow (by omega) hlt3
  unfold ordStoreLog
  omega

lemma log_four_mul_eCap_le {M N vCap eCap capExp : ℕ}
    (h : vCap + eCap + 2 ≤ (M + N + 2) ^ capExp) :
    Nat.log 2 (4 * eCap) + 2 ≤ (capExp + 2) * (Nat.log 2 (M + N + 2) + 1) := by
  have hlg : 2 ≤ Nat.log 2 (M + N + 2) + 1 := log_two_plus_one_ge_two M N
  by_cases he : eCap = 0
  · subst he; simp; nlinarith
  · have hpos : 0 < capExp := capExp_pos_of_caps h
    have hlt1 : M + N + 2 < 2 ^ (Nat.log 2 (M + N + 2) + 1) :=
      Nat.lt_pow_succ_log_self (by omega) (M + N + 2)
    have hlt2 : (M + N + 2) ^ capExp < 2 ^ (capExp * (Nat.log 2 (M + N + 2) + 1)) := by
      have := Nat.pow_lt_pow_left hlt1 (by omega : capExp ≠ 0)
      rwa [← pow_mul, mul_comm (Nat.log 2 (M + N + 2) + 1) capExp] at this
    have hlt3 : 4 * eCap < 2 ^ (capExp * (Nat.log 2 (M + N + 2) + 1) + 2) := by
      rw [pow_add]
      have : 2 ^ 2 = 4 := by norm_num
      rw [this]
      omega
    have hlog : Nat.log 2 (4 * eCap) < capExp * (Nat.log 2 (M + N + 2) + 1) + 2 :=
      Nat.log_lt_of_lt_pow (by omega) hlt3
    nlinarith

lemma log_two_mul_le_capExp {M N vCap eCap capExp s : ℕ} (hs : s ≤ eCap)
    (h : vCap + eCap + 2 ≤ (M + N + 2) ^ capExp) :
    Nat.log 2 (2 * s + 1) ≤ (capExp + 1) * (Nat.log 2 (M + N + 2) + 1) := by
  have hlg : 2 ≤ Nat.log 2 (M + N + 2) + 1 := log_two_plus_one_ge_two M N
  have hpos : 0 < capExp := capExp_pos_of_caps h
  have hlt1 : M + N + 2 < 2 ^ (Nat.log 2 (M + N + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by omega) (M + N + 2)
  have hlt2 : (M + N + 2) ^ capExp < 2 ^ (capExp * (Nat.log 2 (M + N + 2) + 1)) := by
    have := Nat.pow_lt_pow_left hlt1 (by omega : capExp ≠ 0)
    rwa [← pow_mul, mul_comm (Nat.log 2 (M + N + 2) + 1) capExp] at this
  have hlt3 : 2 * s + 1 < 2 ^ (capExp * (Nat.log 2 (M + N + 2) + 1) + 1) := by
    rw [pow_succ]; omega
  have hlog : Nat.log 2 (2 * s + 1) < capExp * (Nat.log 2 (M + N + 2) + 1) + 1 :=
    Nat.log_lt_of_lt_pow (by omega) hlt3
  nlinarith

lemma log_succ_le_capExp {M N vCap eCap capExp m : ℕ} (hm : m ≤ vCap + eCap)
    (h : vCap + eCap + 2 ≤ (M + N + 2) ^ capExp) :
    Nat.log 2 (m + 1) + 1 ≤ capExp * (Nat.log 2 (M + N + 2) + 1) := by
  have hpos : 0 < capExp := capExp_pos_of_caps h
  have hlt1 : M + N + 2 < 2 ^ (Nat.log 2 (M + N + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by omega) (M + N + 2)
  have hlt2 : (M + N + 2) ^ capExp < 2 ^ (capExp * (Nat.log 2 (M + N + 2) + 1)) := by
    have := Nat.pow_lt_pow_left hlt1 (by omega : capExp ≠ 0)
    rwa [← pow_mul, mul_comm (Nat.log 2 (M + N + 2) + 1) capExp] at this
  have hlt3 : m + 1 < 2 ^ (capExp * (Nat.log 2 (M + N + 2) + 1)) := by omega
  have hlog : Nat.log 2 (m + 1) < capExp * (Nat.log 2 (M + N + 2) + 1) :=
    Nat.log_lt_of_lt_pow (by omega) hlt3
  omega

/-- From `((n + u : ℕ) : ℝ) ≤ updateThreshold k M N`, always `u ≤ 4 * M` (even for `k = 0`). -/
lemma updateThreshold_nat_le {k M N n u : ℕ}
    (h : ((n + u : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold k M N) : u ≤ 4 * M := by
  unfold SparseCoreTool.updateThreshold at h
  by_cases hk : k = 0
  · subst hk
    simp only [Nat.cast_zero, zero_mul, div_zero] at h
    have h0 : ((n + u : ℕ) : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    have hnu : n + u = 0 := Nat.cast_eq_zero.mp h0
    omega
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hk)
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      have hexp : Real.exp (1 / 2 : ℝ) < 2 := by
        have hsq : Real.exp (1 / 2 : ℝ) ^ 2 < 2 ^ 2 := by
          rw [← Real.exp_nat_mul]
          have h1 : (2 : ℕ) * (1 / 2 : ℝ) = 1 := by norm_num
          rw [h1]
          have he := Real.exp_one_lt_d9
          linarith
        nlinarith [Real.exp_pos (1 / 2 : ℝ)]
      have h' := Real.log_lt_log (Real.exp_pos _) hexp
      rwa [Real.log_exp] at h'
    have hlogN : (1 / 2 : ℝ) < Real.log ((N : ℝ) + 2) := by
      refine lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) ?_)
      linarith [Nat.cast_nonneg (α := ℝ) N]
    have hden : (1 / 4 : ℝ) ≤ (k : ℝ) * (Real.log ((N : ℝ) + 2)) ^ 2 := by
      have hsq : (1 / 4 : ℝ) ≤ (Real.log ((N : ℝ) + 2)) ^ 2 := by nlinarith
      nlinarith
    have hdiv : (M : ℝ) / ((k : ℝ) * (Real.log ((N : ℝ) + 2)) ^ 2) ≤ 4 * (M : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [Nat.cast_nonneg (α := ℝ) M]
    have hle : ((u : ℕ) : ℝ) ≤ 4 * (M : ℝ) := by
      have hu : ((u : ℕ) : ℝ) ≤ ((n + u : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left u n)
      linarith
    exact_mod_cast hle

lemma log_del_le {M N d : ℕ} (hd : d ≤ 4 * M) :
    Nat.log 2 (d + 1) + 1 ≤ 2 * (Nat.log 2 (M + N + 2) + 1) := by
  have hlg : 2 ≤ Nat.log 2 (M + N + 2) + 1 := log_two_plus_one_ge_two M N
  have hlt1 : M + N + 2 < 2 ^ (Nat.log 2 (M + N + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by omega) (M + N + 2)
  have hlt2 : d + 1 < 2 ^ (Nat.log 2 (M + N + 2) + 1 + 2) := by
    rw [pow_add]
    have : 2 ^ 2 = 4 := by norm_num
    rw [this]
    omega
  have hlog : Nat.log 2 (d + 1) < Nat.log 2 (M + N + 2) + 1 + 2 :=
    Nat.log_lt_of_lt_pow (by omega) hlt2
  omega

/-- Pure list lemma: summing filter counts over a deduplicated key list never exceeds the input
list's length. -/
private lemma sum_filter_eq_le {α β : Type*} [DecidableEq β] (f : α → β) :
    ∀ (xs : List α) (ks : List β), ks.Nodup →
      (ks.map fun r => (xs.filter fun x => decide (f x = r)).length).sum ≤ xs.length
  | [], ks, _ => by
      simp only [List.filter_nil, List.length_nil]
      induction ks with
      | nil => simp
      | cons _ tl ih => simp
  | a :: xs, ks, hnd => by
      have hadd : ∀ l : List β,
          (l.map fun r => ((a :: xs).filter fun x => decide (f x = r)).length).sum =
          (l.map fun r => if f a = r then 1 else 0).sum +
            (l.map fun r => (xs.filter fun x => decide (f x = r)).length).sum := by
        intro l
        induction l with
        | nil => simp
        | cons r tl ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [ih]
          simp only [List.filter_cons]
          by_cases hfa : f a = r
          · simp [hfa]; omega
          · simp [hfa]; omega
      have h1 : ∀ l : List β, l.Nodup → (l.map fun r => if f a = r then 1 else 0).sum ≤ 1 := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons r tl ih =>
          intro hnd'
          rcases List.nodup_cons.mp hnd' with ⟨hr, htl⟩
          simp only [List.map_cons, List.sum_cons]
          by_cases hfa : f a = r
          · subst hfa
            have h0 : (tl.map fun r => if f a = r then 1 else 0).sum = 0 := by
              clear ih htl hnd'
              induction tl with
              | nil => simp
              | cons b bs ihb =>
                have hne : f a ≠ b := fun h => hr (h ▸ List.mem_cons_self)
                simp only [List.map_cons, List.sum_cons, hne, ↓reduceIte, Nat.zero_add]
                exact ihb fun h => hr (List.mem_cons_of_mem b h)
            simp [h0]
          · simp only [hfa, ↓reduceIte, Nat.zero_add]
            exact ih htl
      rw [hadd ks]
      have hih := sum_filter_eq_le f xs ks hnd
      have ha1 := h1 ks hnd
      simp only [List.length_cons]
      omega

lemma splitGroupsOf_length_le (pairs : List (ℕ × ℕ)) :
    (splitGroupsOf pairs).length ≤ pairs.length := by
  unfold splitGroupsOf splitOldRoots
  rw [List.length_map, Finset.length_sort]
  calc (splitOldList pairs (fun _ => 0)).toFinset.card
      ≤ (splitOldList pairs (fun _ => 0)).length := List.toFinset_card_le _
    _ = pairs.length := splitOldList_length pairs _

lemma groupsTotalLen_splitGroupsOf_le (pairs : List (ℕ × ℕ)) :
    groupsTotalLen (splitGroupsOf pairs) ≤ 2 * pairs.length := by
  unfold groupsTotalLen splitGroupsOf
  set anc := splitAncFold pairs (fun _ => 0)
  set ks := splitOldRoots pairs
  have hnd : ks.Nodup := Finset.sort_nodup _ _
  have hks : ks.length ≤ pairs.length := by
    have := splitGroupsOf_length_le pairs
    simpa [splitGroupsOf, ks] using this
  have hsplit : ∀ l : List ℕ,
      ((l.map fun r => r :: (pairs.filter fun p => ancDecode anc p.2 = r).map Prod.snd).map
        List.length).sum =
      l.length + (l.map fun r => (pairs.filter fun p => decide (ancDecode anc p.2 = r)).length).sum := by
    intro l
    induction l with
    | nil => simp
    | cons r tl ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_map]
      omega
  rw [hsplit ks]
  have hfilt := sum_filter_eq_le (fun p : ℕ × ℕ => ancDecode anc p.2) pairs ks hnd
  omega

end

end MinCostFlow.SparseCore.Program
