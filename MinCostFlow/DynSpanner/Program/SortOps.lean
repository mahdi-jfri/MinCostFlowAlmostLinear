module

public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Log

/-!
# Deterministic sorting primitives (`SortOps`)

Implements and verifies the deterministic Word-RAM primitives used by `MergeSort` and graph
translations:
* `natMerge` and `mergePairStmt`: two-pointer merge of adjacent sorted subarrays
  `[lo, mid)` and `[mid, hi)` via `[scratch, scratch + (hi - lo))` in `O(hi - lo + 1)` time.
* `dedupStmt`: deduplicates a sorted array in `O(n + 1)` time into a strictly increasing array.
* `binSearchStmt`: binary search returning `L.idxOf key` on a strictly increasing array in
  `O(Nat.log 2 (n + 1) + 1)` time.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

def sortIdxMergePair : ℕ := 0
def sortIdxMergeSort : ℕ := 1
def sortIdxDedup : ℕ := 2
def sortIdxBinSearch : ℕ := 3

/-- Pure two-way merge of two sorted lists of natural numbers. -/
def natMerge : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs', y :: ys' =>
    if y < x then y :: natMerge (x :: xs') ys' else x :: natMerge xs' (y :: ys')

/-- Pure deduplication of a sorted list (matching `dedupStmt`). -/
def sortedDedupAux : ℕ → List ℕ → List ℕ
  | _, [] => []
  | prev, x :: xs => if x = prev then sortedDedupAux prev xs else x :: sortedDedupAux x xs

def sortedDedup : List ℕ → List ℕ
  | [] => []
  | x :: xs => x :: sortedDedupAux x xs

/-- Merge `[lo, mid)` and `[mid, hi)` inside `a` using `scratch` (`[a, scratch, lo, mid, hi]`). -/
def mergePairStmt : Stmt :=
  .assign 5 (.reg 2) ;;
  .assign 6 (.reg 3) ;;
  .assign 7 (.const 0) ;;
  .assign 8 (.bin .sub (.reg 4) (.reg 2)) ;;
  .loop (.bin .lt (.reg 7) (.reg 8))
    (.cond (.bin .lt (.reg 5) (.reg 3))
      (.cond (.bin .lt (.reg 6) (.reg 4))
        (.assign 9 (.load (.bin .add (.reg 0) (.reg 5))) ;;
         .assign 10 (.load (.bin .add (.reg 0) (.reg 6))) ;;
         .cond (.bin .lt (.reg 10) (.reg 9))
           (.store (.bin .add (.reg 1) (.reg 7)) (.reg 10) ;;
            .assign 6 (.bin .add (.reg 6) (.const 1)))
           (.store (.bin .add (.reg 1) (.reg 7)) (.reg 9) ;;
            .assign 5 (.bin .add (.reg 5) (.const 1))))
        (.assign 9 (.load (.bin .add (.reg 0) (.reg 5))) ;;
         .store (.bin .add (.reg 1) (.reg 7)) (.reg 9) ;;
         .assign 5 (.bin .add (.reg 5) (.const 1))))
      (.assign 10 (.load (.bin .add (.reg 0) (.reg 6))) ;;
       .store (.bin .add (.reg 1) (.reg 7)) (.reg 10) ;;
       .assign 6 (.bin .add (.reg 6) (.const 1))) ;;
     .assign 7 (.bin .add (.reg 7) (.const 1))) ;;
  forRange 9 (.const 0) (.reg 8)
    (.assign 10 (.load (.bin .add (.reg 1) (.reg 9))) ;;
     .store (.bin .add (.bin .add (.reg 0) (.reg 2)) (.reg 9)) (.reg 10)) ;;
  .ret (.const 0)

/-- Deduplicate sorted array `[src, src + n)` into `[dst, dst + outLen)` (`[src, n, dst]`),
returning `outLen`. -/
def dedupStmt : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0))
    (.ret (.const 0))
    (.assign 3 (.load (.reg 0)) ;;
     .store (.reg 2) (.reg 3) ;;
     .assign 4 (.const 1) ;;
     forRange 5 (.const 1) (.reg 1)
       (.assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
        .cond (.bin .eq (.reg 6) (.reg 3))
          .nop
          (.store (.bin .add (.reg 2) (.reg 4)) (.reg 6) ;;
           .assign 3 (.reg 6) ;;
           .assign 4 (.bin .add (.reg 4) (.const 1)))) ;;
     .ret (.reg 4))

/-- Binary search for `key` in strictly increasing array `[a, a + n)` (`[a, n, key]`),
returning `L.idxOf key`. -/
def binSearchStmt : Stmt :=
  .assign 3 (.const 0) ;;
  .assign 4 (.reg 1) ;;
  .loop (.bin .lt (.bin .add (.reg 3) (.const 1)) (.reg 4))
    (.assign 5 (.bin .add (.reg 3) (.bin .div (.bin .sub (.reg 4) (.reg 3)) (.const 2))) ;;
     .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
     .cond (.bin .lt (.reg 2) (.reg 6))
       (.assign 4 (.reg 5))
       (.assign 3 (.reg 5))) ;;
  .ret (.reg 3)

/-- Merge sort (`[a, n, scratch]`) using `sortProcs bSort` at `bSort + sortIdxMergePair`. -/
def mergeSortStmt (bSort : ℕ) : Stmt :=
  .assign 3 (.const 1) ;;
  .loop (.bin .lt (.reg 3) (.reg 1))
    (.assign 4 (.const 0) ;;
     .loop (.bin .lt (.reg 4) (.reg 1))
       (.cond (.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 4)))
          (.assign 5 (.bin .add (.reg 4) (.reg 3)))
          (.assign 5 (.reg 1)) ;;
        .cond (.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 5)))
          (.assign 6 (.bin .add (.reg 5) (.reg 3)))
          (.assign 6 (.reg 1)) ;;
        .cond (.bin .lt (.reg 5) (.reg 6))
          (.call 7 (bSort + sortIdxMergePair) [.reg 0, .reg 2, .reg 4, .reg 5, .reg 6])
          .nop ;;
        .assign 4 (.reg 6)) ;;
     .cond (.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 3)))
       (.assign 3 (.bin .mul (.const 2) (.reg 3)))
       (.assign 3 (.reg 1))) ;;
  .ret (.const 0)

def sortProcs (bSort : ℕ) : List Stmt :=
  [mergePairStmt, mergeSortStmt bSort, dedupStmt, binSearchStmt]

lemma sortProcs_length (bSort : ℕ) : (sortProcs bSort).length = 4 := rfl

lemma sortProcs_noRand (bSort : ℕ) : ∀ s ∈ sortProcs bSort, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Contracts -/

def mergePairContract (w : ℕ) (L : List ℕ) (lo mid hi : ℕ) : Contract where
  pre args mem := ∃ a scratch,
    args = [a, scratch, lo, mid, hi] ∧ 16 ≤ 2 ^ w ∧
    a + L.length < 2 ^ w ∧ scratch + (hi - lo) < 2 ^ w ∧
    (a + L.length ≤ scratch ∨ scratch + (hi - lo) ≤ a) ∧
    lo ≤ mid ∧ mid ≤ hi ∧ hi ≤ L.length ∧
    ListAt mem a L ∧ (∀ x ∈ L, x < 2 ^ w) ∧
    ((L.drop lo).take (mid - lo)).Pairwise (· ≤ ·) ∧
    ((L.drop mid).take (hi - mid)).Pairwise (· ≤ ·)
  post args mem ret mem' := ∃ a scratch L',
    args = [a, scratch, lo, mid, hi] ∧ ret = 0 ∧
    L'.length = L.length ∧
    (∀ i < lo, L'[i]? = L[i]?) ∧
    (∀ i, hi ≤ i → L'[i]? = L[i]?) ∧
    (L'.drop lo).take (hi - lo) =
      natMerge ((L.drop lo).take (mid - lo)) ((L.drop mid).take (hi - mid)) ∧
    ListAt mem' a L' ∧
    ∀ addr, addr < a + lo ∨ a + hi ≤ addr →
      (addr < scratch ∨ scratch + (hi - lo) ≤ addr → mem' addr = mem addr)
  cost _ _ := 70 * (hi - lo) + 50

def mergeSortContract (w : ℕ) (L : List ℕ) : Contract where
  pre args mem := ∃ a scratch,
    args = [a, L.length, scratch] ∧ 16 ≤ 2 ^ w ∧
    a + L.length < 2 ^ w ∧ scratch + L.length < 2 ^ w ∧
    (a + L.length ≤ scratch ∨ scratch + L.length ≤ a) ∧
    ListAt mem a L ∧ (∀ x ∈ L, x < 2 ^ w)
  post args mem ret mem' := ∃ a scratch L',
    args = [a, L.length, scratch] ∧ ret = 0 ∧
    L'.Perm L ∧ L'.Pairwise (· ≤ ·) ∧ ListAt mem' a L' ∧
    ∀ addr, (addr < a ∨ a + L.length ≤ addr) →
      (addr < scratch ∨ scratch + L.length ≤ addr) → mem' addr = mem addr
  cost _ _ := 200 * L.length * (Nat.log 2 (L.length + 1) + 1) + 50

def dedupContract (w : ℕ) (L : List ℕ) : Contract where
  pre args mem := ∃ src dst,
    args = [src, L.length, dst] ∧ 16 ≤ 2 ^ w ∧
    src + L.length < 2 ^ w ∧ dst + L.length < 2 ^ w ∧
    (src + L.length ≤ dst ∨ dst + L.length ≤ src) ∧
    L.Pairwise (· ≤ ·) ∧ ListAt mem src L ∧ (∀ x ∈ L, x < 2 ^ w)
  post args mem ret mem' := ∃ src dst,
    args = [src, L.length, dst] ∧ ret = (sortedDedup L).length ∧
    (sortedDedup L).Pairwise (· < ·) ∧ (∀ x, x ∈ sortedDedup L ↔ x ∈ L) ∧
    ListAt mem' dst (sortedDedup L) ∧
    ∀ addr, addr < dst ∨ dst + (sortedDedup L).length ≤ addr → mem' addr = mem addr
  cost _ _ := 45 * L.length + 25

def binSearchContract (w : ℕ) (L : List ℕ) (key : ℕ) : Contract where
  pre args mem := ∃ a,
    args = [a, L.length, key] ∧ 16 ≤ 2 ^ w ∧
    a + L.length < 2 ^ w ∧
    L.Pairwise (· < ·) ∧ key ∈ L ∧
    ListAt mem a L ∧ (∀ x ∈ L, x < 2 ^ w)
  post args mem ret mem' := ∃ a,
    args = [a, L.length, key] ∧ mem' = mem ∧
    ret = L.idxOf key ∧ ret < L.length
  cost _ _ := 45 * (Nat.log 2 (L.length + 1) + 1) + 20

end

/-! ## Pure list lemmas for `natMerge` and `sortedDedup` -/

public section

lemma natMerge_length : ∀ (xs ys : List ℕ), (natMerge xs ys).length = xs.length + ys.length
  | [], ys => by simp [natMerge]
  | _ :: xs', [] => by simp [natMerge]
  | x :: xs', y :: ys' => by
    unfold natMerge
    split_ifs
    · have ih := natMerge_length (x :: xs') ys'
      simp only [List.length_cons] at ih ⊢; omega
    · have ih := natMerge_length xs' (y :: ys')
      simp only [List.length_cons] at ih ⊢; omega

lemma natMerge_perm : ∀ (xs ys : List ℕ), (natMerge xs ys).Perm (xs ++ ys)
  | [], ys => by simp [natMerge]
  | _ :: xs', [] => by simp [natMerge]
  | x :: xs', y :: ys' => by
    unfold natMerge
    split_ifs
    · have ih := natMerge_perm (x :: xs') ys'
      exact (List.Perm.cons y ih).trans (by
        rw [← List.cons_append]
        exact List.perm_middle.symm)
    · exact List.Perm.cons x (natMerge_perm xs' (y :: ys'))

lemma mem_natMerge_iff {xs ys : List ℕ} {z : ℕ} :
    z ∈ natMerge xs ys ↔ z ∈ xs ∨ z ∈ ys := by
  rw [(natMerge_perm xs ys).mem_iff, List.mem_append]

lemma natMerge_pairwise :
    ∀ {xs ys : List ℕ},
      xs.Pairwise (· ≤ ·) → ys.Pairwise (· ≤ ·) → (natMerge xs ys).Pairwise (· ≤ ·)
  | [], ys, _, hys => by simpa [natMerge] using hys
  | _ :: xs', [], hxs, _ => by simpa [natMerge] using hxs
  | x :: xs', y :: ys', hxs, hys => by
    simp only [List.pairwise_cons] at hxs hys
    unfold natMerge
    split_ifs with hyx
    · rw [List.pairwise_cons]
      refine ⟨fun z hz => ?_, natMerge_pairwise (List.pairwise_cons.mpr hxs) hys.2⟩
      rw [mem_natMerge_iff, List.mem_cons] at hz
      rcases hz with (hz_eq | hz') | hz'
      · rw [hz_eq]; exact Nat.le_of_lt hyx
      · exact Nat.le_trans (Nat.le_of_lt hyx) (hxs.1 z hz')
      · exact hys.1 z hz'
    · rw [List.pairwise_cons]
      refine ⟨fun z hz => ?_, natMerge_pairwise hxs.2 (List.pairwise_cons.mpr hys)⟩
      rw [mem_natMerge_iff, List.mem_cons] at hz
      rcases hz with hz' | (hz_eq | hz')
      · exact hxs.1 z hz'
      · rw [hz_eq]; omega
      · exact Nat.le_trans (by omega) (hys.1 z hz')

lemma sortedDedupAux_mem {prev : ℕ} :
    ∀ {L : List ℕ} {x : ℕ},
      L.Pairwise (· ≤ ·) → (∀ y ∈ L, prev ≤ y) →
      (x ∈ sortedDedupAux prev L ↔ x ∈ L ∧ x ≠ prev)
  | [], _, _, _ => by simp [sortedDedupAux]
  | y :: ys, x, hL, hprev => by
    simp only [List.pairwise_cons] at hL
    have hy_prev : prev ≤ y := hprev y List.mem_cons_self
    have hprev' : ∀ z ∈ ys, y ≤ z := hL.1
    have hprev_y : ∀ z ∈ ys, prev ≤ z := fun z hz => Nat.le_trans hy_prev (hL.1 z hz)
    unfold sortedDedupAux
    split_ifs with hyp
    · rw [sortedDedupAux_mem hL.2 (by simpa [hyp] using hprev'), List.mem_cons]
      constructor
      · rintro ⟨hx, hne⟩; exact ⟨Or.inr hx, hne⟩
      · rintro ⟨hx_eq | hx, hne⟩
        · exact absurd (hx_eq ▸ hyp) hne
        · exact ⟨hx, hne⟩
    · rw [List.mem_cons, sortedDedupAux_mem hL.2 hprev', List.mem_cons]
      constructor
      · rintro (rfl | ⟨hx, _⟩)
        · exact ⟨Or.inl rfl, hyp⟩
        · refine ⟨Or.inr hx, fun hc => ?_⟩
          have hzx := hL.1 x hx
          omega
      · rintro ⟨hx_eq | hx, _hne⟩
        · exact Or.inl hx_eq
        · by_cases hxy : x = y
          · exact Or.inl hxy
          · exact Or.inr ⟨hx, hxy⟩

lemma sortedDedupAux_pairwise {prev : ℕ} :
    ∀ {L : List ℕ},
      L.Pairwise (· ≤ ·) → (∀ y ∈ L, prev ≤ y) →
      (sortedDedupAux prev L).Pairwise (· < ·) ∧ (∀ y ∈ sortedDedupAux prev L, prev < y)
  | [], _, _ => by simp [sortedDedupAux]
  | y :: ys, hL, hprev => by
    simp only [List.pairwise_cons] at hL
    have hy_prev : prev ≤ y := hprev y List.mem_cons_self
    have hys_prev : ∀ z ∈ ys, y ≤ z := hL.1
    unfold sortedDedupAux
    split_ifs with hyp
    · simpa [hyp] using sortedDedupAux_pairwise hL.2 hys_prev
    · obtain ⟨ihP, ihGt⟩ := sortedDedupAux_pairwise hL.2 hys_prev
      refine ⟨List.pairwise_cons.mpr ⟨ihGt, ihP⟩, fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz'
      · omega
      · exact Nat.lt_trans (by omega) (ihGt z hz')

lemma sortedDedup_mem {L : List ℕ} (hL : L.Pairwise (· ≤ ·)) (x : ℕ) :
    x ∈ sortedDedup L ↔ x ∈ L := by
  cases L with
  | nil => simp [sortedDedup]
  | cons y ys =>
    simp only [List.pairwise_cons] at hL
    simp only [sortedDedup, List.mem_cons, sortedDedupAux_mem hL.2 hL.1]
    constructor
    · rintro (rfl | ⟨hx, _⟩)
      · exact Or.inl rfl
      · exact Or.inr hx
    · rintro (rfl | hx)
      · exact Or.inl rfl
      · by_cases hxy : x = y
        · exact Or.inl hxy
        · exact Or.inr ⟨hx, hxy⟩

lemma sortedDedup_pairwise {L : List ℕ} (hL : L.Pairwise (· ≤ ·)) :
    (sortedDedup L).Pairwise (· < ·) := by
  cases L with
  | nil => simp [sortedDedup]
  | cons y ys =>
    simp only [List.pairwise_cons] at hL
    obtain ⟨hP, hGt⟩ := sortedDedupAux_pairwise hL.2 hL.1
    exact List.pairwise_cons.mpr ⟨hGt, hP⟩

lemma sortedDedup_length_le : ∀ (L : List ℕ), (sortedDedup L).length ≤ L.length
  | [] => by simp [sortedDedup]
  | x :: xs => by
    have aux : ∀ p (M : List ℕ), (sortedDedupAux p M).length ≤ M.length := by
      intro p M
      induction M generalizing p with
      | nil => simp [sortedDedupAux]
      | cons y ys ih =>
        unfold sortedDedupAux
        split_ifs
        · exact (ih p).trans (Nat.le_succ _)
        · simp only [List.length_cons]
          exact Nat.succ_le_succ (ih y)
    simpa [sortedDedup] using Nat.succ_le_succ (aux x xs)

end

/-! ## Helper indexing lemmas for `mergePair` -/

private lemma drop_take_getElem {L : List ℕ} {lo hi i : ℕ}
    (hi_len : hi ≤ L.length) (hi_i : i < hi - lo) :
    ((L.drop lo).take (hi - lo))[i]'(by
      rw [List.length_take, List.length_drop]; omega) = L[lo + i]'(by omega) := by
  rw [List.getElem_take, List.getElem_drop]

private lemma drop_take_drop {L : List ℕ} {a b k : ℕ} (_hbk : k ≤ b - a) :
    ((L.drop a).take (b - a)).drop k = (L.drop (a + k)).take (b - (a + k)) := by
  rw [List.drop_take, List.drop_drop, show b - a - k = b - (a + k) by omega]

private lemma list_take_succ_eq_drop_take_zero {L : List ℕ} {a b : ℕ}
    (ha : a < b) (hb : b ≤ L.length) :
    (L.drop a).take (b - a) = L[a] :: (L.drop (a + 1)).take (b - (a + 1)) := by
  refine List.ext_getElem (by simp; omega) fun i hi₁ hi₂ => ?_
  cases i with
  | zero => simp [List.getElem_take, List.getElem_drop]
  | succ j =>
    simp only [List.getElem_cons_succ, List.getElem_take, List.getElem_drop]
    congr 1; omega

private def lastAux (p : ℕ) : List ℕ → ℕ
  | [] => p
  | y :: ys => lastAux y ys

private lemma lastAux_snoc_of_ne {p y : ℕ} :
    ∀ (ys : List ℕ), lastAux p (ys ++ [y]) = y
  | [] => rfl
  | z :: zs => by simpa [lastAux] using lastAux_snoc_of_ne zs

private lemma sortedDedupAux_snoc (p : ℕ) :
    ∀ (L : List ℕ) (x : ℕ),
      sortedDedupAux p (L ++ [x]) =
        sortedDedupAux p L ++ (if x = lastAux p (sortedDedupAux p L) then [] else [x])
  | [], x => by
    simp only [List.nil_append, sortedDedupAux, lastAux]
  | y :: ys, x => by
    by_cases hyp : y = p
    · subst hyp
      simp only [List.cons_append, sortedDedupAux, ↓reduceIte]
      exact sortedDedupAux_snoc y ys x
    · simp only [List.cons_append, sortedDedupAux, hyp, ↓reduceIte, lastAux]
      rw [sortedDedupAux_snoc y ys x]

private lemma logBound_halve {d d' : ℕ} (_hd : 2 ≤ d) (hdiv : d' - 1 ≤ (d - 1) / 2) :
    (if d' ≤ 1 then 0 else Nat.log 2 (d' - 1) + 1) + 1 ≤ Nat.log 2 (d - 1) + 1 := by
  split_ifs with h1
  · exact Nat.le_add_left _ _
  · have hd' : 1 ≤ d' - 1 := by omega
    have hpow : 2 ^ (Nat.log 2 (d' - 1) + 1) ≤ d - 1 := by
      have hp := Nat.pow_log_le_self 2 (by omega : d' - 1 ≠ 0)
      rw [Nat.pow_succ']
      omega
    exact Nat.succ_le_succ (Nat.le_log_of_pow_le (by omega) hpow)

private theorem runs_cond_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v)
    (hT : v ≠ 0 → ∃ o st' c, Runs w p ω s₁ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T)
    (hF : v = 0 → ∃ o st' c, Runs w p ω s₂ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  by_cases hv : v = 0
  · rcases hF hv with ⟨o, st', c₁, hr₁, hq, hc⟩
    exact ⟨o, st', e.size + c₁ + 1,
      runs_cond_iff.mpr ⟨0, c₁, hv ▸ he, by simpa using hr₁, rfl⟩, hq, by omega⟩
  · rcases hT hv with ⟨o, st', c₁, hr₁, hq, hc⟩
    exact ⟨o, st', e.size + c₁ + 1,
      runs_cond_iff.mpr ⟨v, c₁, he, by simpa [hv] using hr₁, rfl⟩, hq, by omega⟩

public section

theorem dedup_meetsContract {w : ℕ} {p : Program} {b bSort : ℕ} {L : List ℕ}
    (hp : p.HasAt b (sortProcs bSort)) :
    MeetsContract w p (b + sortIdxDedup) (dedupContract w L) := by
  refine meetsContract_of_runs (hp.get (i := sortIdxDedup) (by simp [sortProcs, sortIdxDedup]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨src, dst, rfl, hw16, hsrcB, hdstB, hdisj, hLpair, hLat, hLw⟩
  have hlt_src : src < 2 ^ w := hargs src (by simp)
  have hlt_len : L.length < 2 ^ w := hargs L.length (by simp)
  have hlt_dst : dst < 2 ^ w := hargs dst (by simp)
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [sortProcs, sortIdxDedup, List.getElem_cons_succ, List.getElem_cons_zero, dedupStmt]
  cases L with
  | nil =>
    refine runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, startState, h0_lt, h1_lt]) ?_ ?_
    · intro _
      refine runs_ret_le (by eval_expr) ⟨src, dst, rfl, rfl, by simp [sortedDedup], by simp [sortedDedup],
        fun _ hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ ?_
      dsimp only [dedupContract, Expr.size]; omega
    · intro hc; cases hc
  | cons x₀ xs =>
    have hx₀_lt : x₀ < 2 ^ w := hLw x₀ List.mem_cons_self
    have hx₀_mem : mem src = x₀ := by
      have h := hLat 0 (by simp)
      simpa using h
    refine runs_cond_le (v := 0)
      (by simp [Expr.eval, BinOp.eval, startState, h0_lt]) ?_ ?_
    · intro hc; exact absurd rfl hc
    · intro _
      refine runs_seq_assign_le (Expr.eval_load_of_eq (v := x₀) (by eval_expr) hx₀_mem) ?_
      refine runs_seq_store_le (v := x₀) (x := dst) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_assign_le (v := 1) (by eval_expr) ?_
      let Inv : ℕ → State → Prop := fun k st =>
        1 ≤ k ∧ k ≤ xs.length + 1 ∧
        st.regs 0 = src ∧ st.regs 1 = xs.length + 1 ∧ st.regs 2 = dst ∧ st.regs 5 = k ∧
        let aux := sortedDedupAux x₀ (xs.take (k - 1))
        st.regs 3 = lastAux x₀ aux ∧
        st.regs 4 = (x₀ :: aux).length ∧
        (x₀ :: aux).length ≤ k ∧
        ListAt st.mem dst (x₀ :: aux) ∧
        ∀ addr, addr < dst ∨ dst + (x₀ :: aux).length ≤ addr → st.mem addr = mem addr
      let body : Stmt :=
        .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
        .cond (.bin .eq (.reg 6) (.reg 3))
          .nop
          (.store (.bin .add (.reg 2) (.reg 4)) (.reg 6) ;;
           .assign 3 (.reg 6) ;;
           .assign 4 (.bin .add (.reg 4) (.const 1)))
      let P0 : State → Prop := fun st =>
        st.regs 0 = src ∧ st.regs 1 = xs.length + 1 ∧ st.regs 2 = dst ∧
        st.regs 3 = x₀ ∧ st.regs 4 = 1 ∧
        st.mem dst = x₀ ∧
        ∀ addr, addr < dst ∨ dst + 1 ≤ addr → st.mem addr = mem addr
      have hLoop : Triple w p P0 (forRange 5 (.const 1) (.reg 1) body)
          (normalPost (Inv (xs.length + 1)))
          (fun _ => (xs.length + 1 - 1) * (35 + Expr.size (.reg 1) + 8) +
            (Expr.size (.const 1) + Expr.size (.reg 1) + 5)) := by
        refine Triple.forRange_const 35 1 (xs.length + 1) (Nat.le_add_left _ _) h1_lt (fun _ => hlt_len)
          (fun st hst => by
            rcases hst with ⟨h0, h1, h2, h3, h4, hmd, hfr⟩
            refine ⟨by simp [Expr.eval, h1_lt], ⟨le_refl _, Nat.le_add_left _ _,
              ?_, ?_, ?_, ?_, ?_, ?_, le_refl _, ?_, ?_⟩⟩
            · simp [h0]
            · simp [h1]
            · simp [h2]
            · simp
            · simp [h3, List.take_zero, sortedDedupAux, lastAux]
            · simp [h4, List.take_zero, sortedDedupAux]
            · intro i hi
              simp only [show (1 : ℕ) - 1 = 0 by rfl, List.take_zero, sortedDedupAux,
                List.length_cons, List.length_nil] at hi
              have : i = 0 := by omega
              subst this
              simp [List.take_zero, sortedDedupAux, hmd]
            · intro addr hout
              simp only [show (1 : ℕ) - 1 = 0 by rfl, List.take_zero, sortedDedupAux,
                List.length_cons, List.length_nil] at hout
              exact hfr addr hout)
          (fun k st _ _ hk => hk.2.2.2.2.2.1)
          (fun k st _ _ hk => by
            rcases hk with ⟨_, _, _, hr1, _, _, _, _, _, _, _⟩
            simp [Expr.eval, hr1])
          (fun k hk_ge hk_lt st ω' hk => by
            rcases hk with ⟨_, _, hr0, hr1, hr2, hr5, hr3, hr4, hlen_le, hdat, hfr⟩
            let aux := sortedDedupAux x₀ (xs.take (k - 1))
            have hk1_xs : k - 1 < xs.length := by omega
            have haux_len_le : aux.length + 1 ≤ k := by
              simpa [aux, List.length_cons] using hlen_le
            have hsrc_k_disj : src + k < dst ∨ dst + (x₀ :: aux).length ≤ src + k := by
              simp only [List.length_cons]
              rcases hdisj with hd | hd
              · left; simp only [List.length_cons] at hd; omega
              · right; simp only [List.length_cons] at hd; omega
            have hsrc_k_lt : src + k < 2 ^ w := by simp only [List.length_cons] at hsrcB; omega
            have hx_mem : st.mem (src + k) = xs[k - 1] := by
              have hmem_k := hLat k (by simp; omega)
              have hget_k : (x₀ :: xs)[k]'(by simp; omega) = xs[k - 1] := by
                rw [List.getElem_cons (by omega)]
                split_ifs with hk0
                · omega
                · rfl
              rw [hfr _ hsrc_k_disj, hmem_k, hget_k]
            have hx_lt : xs[k - 1] < 2 ^ w := hLw xs[k - 1] (List.mem_cons_of_mem _ (List.getElem_mem hk1_xs))
            have haux_next : sortedDedupAux x₀ (xs.take k) =
                aux ++ (if xs[k - 1] = lastAux x₀ aux then [] else [xs[k - 1]]) := by
              have htake : xs.take k = xs.take (k - 1) ++ [xs[k - 1]] := by
                have h := List.take_succ_eq_append_getElem hk1_xs
                rwa [show k - 1 + 1 = k by omega] at h
              rw [htake]
              exact sortedDedupAux_snoc x₀ (xs.take (k - 1)) xs[k - 1]
            suffices h : ∃ o st₁ c, Runs w p ω' body st o st₁ c ∧
                (normalPost fun st₁ =>
                  Inv (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 5 (k + 1), pos := st₁.pos } ∧
                    st₁.regs 5 = k) o st₁ ∧
                0 + c ≤ 35 by
              rcases h with ⟨o, s', c, hr, hq, hc⟩
              exact ⟨o, s', c, hr, hq, by simpa using hc⟩
            dsimp only [body]
            refine runs_seq_assign_le (Expr.eval_load_of_eq (v := xs[k - 1])
              (by simp [Expr.eval, BinOp.eval, hr0, hr5, hsrc_k_lt]) hx_mem) ?_
            by_cases hsame : xs[k - 1] = lastAux x₀ aux
            · refine runs_cond_le (v := 1)
                (by dsimp only [aux] at hsame ⊢
                    simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr3, hsame, h1_lt]) ?_ ?_
              · intro _
                refine runs_nop_le ?_ (by dsimp only [Expr.size]; omega)
                refine ⟨⟨by omega, by omega, ?_, ?_, ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
                · simp [hr0]
                · simp [hr1]
                · simp [hr2]
                · simpa [aux, Nat.add_sub_cancel, haux_next, hsame] using hr3
                · simpa [aux, Nat.add_sub_cancel, haux_next, hsame] using hr4
                · dsimp only [aux] at hsame hlen_le haux_len_le ⊢
                  simp only [aux, Nat.add_sub_cancel, haux_next, hsame, ↓reduceIte, List.append_nil,
                    List.length_cons]
                  omega
                · simpa [aux, Nat.add_sub_cancel, haux_next, hsame] using hdat
                · simpa [aux, Nat.add_sub_cancel, haux_next, hsame] using hfr
                · simp [hr5]
              · intro hc; cases hc
            · have haux_lt : aux.length + 1 ≤ xs.length := by omega
              simp only [List.length_cons] at hdstB
              have hdst_out_lt : dst + (aux.length + 1) < 2 ^ w := by omega
              have hlen1_lt : aux.length + 2 < 2 ^ w := by omega
              refine runs_cond_le (v := 0)
                (by dsimp only [aux] at hsame ⊢
                    simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr3, hsame, h0_lt]) ?_ ?_
              · intro hc; exact absurd rfl hc
              · intro _
                refine runs_seq_store_le (v := xs[k - 1]) (x := dst + (aux.length + 1))
                  (by dsimp only [aux] at hdst_out_lt ⊢
                      simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr2, hr4, List.length_cons,
                        hdst_out_lt])
                  (by eval_expr) ?_
                refine runs_seq_assign_le (v := xs[k - 1]) (by eval_expr) ?_
                refine runs_assign_le (v := aux.length + 2)
                  (by dsimp only [aux] at hlen1_lt ⊢
                      have hlen1' : (sortedDedupAux x₀ (xs.take (k - 1))).length + 1 + 1 < 2 ^ w := by omega
                      simp [Expr.eval, BinOp.eval, Function.update_of_ne, h1_lt, hr4, List.length_cons,
                        hlen1']) ?_
                  (by dsimp only [Expr.size]; omega)
                refine ⟨⟨by omega, by omega, ?_, ?_, ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
                · simp [hr0]
                · simp [hr1]
                · simp [hr2]
                · simp only [aux, Nat.add_sub_cancel, haux_next, hsame, ↓reduceIte]
                  cases haux : sortedDedupAux x₀ (xs.take (k - 1)) with
                  | nil => simp [lastAux]
                  | cons y ys =>
                    have hcons : (y :: ys) ++ [xs[k - 1]] = y :: (ys ++ [xs[k - 1]]) := rfl
                    simp [lastAux, hcons, lastAux_snoc_of_ne]
                · simp only [aux, Nat.add_sub_cancel, haux_next, hsame, ↓reduceIte,
                    List.length_cons, List.length_append, List.length_nil,
                    Function.update_of_ne (by decide : (4 : ℕ) ≠ 5), Function.update_self]
                · dsimp only [aux] at hlen_le hsame haux_len_le ⊢
                  simp only [aux, Nat.add_sub_cancel, haux_next, hsame, ↓reduceIte,
                    List.length_cons, List.length_append, List.length_nil]
                  omega
                · intro i hi
                  dsimp only [aux] at hdat hsame hi hdst_out_lt ⊢
                  simp only [aux, Nat.add_sub_cancel, haux_next, hsame, ↓reduceIte,
                    ← List.cons_append] at hi ⊢
                  have hi_lt : i < (x₀ :: sortedDedupAux x₀ (xs.take (k - 1))).length + 1 := by
                    simpa [List.length_append, List.length_cons] using hi
                  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi_lt) with hi0 | heqi
                  · have hget := hdat i hi0
                    rw [List.getElem_append_left hi0]
                    simp only [List.length_cons] at hi0 ⊢
                    rw [Function.update_of_ne (by omega)]
                    exact hget
                  · simp only [heqi, List.length_cons]
                    simp
                · intro addr hout
                  dsimp only [aux] at hfr hsame hout ⊢
                  simp only [aux, Nat.add_sub_cancel, haux_next, hsame, ↓reduceIte,
                    List.length_cons, List.length_append, List.length_nil] at hout ⊢
                  rw [Function.update_of_ne (by omega)]
                  exact hfr addr (by
                    simp only [List.length_cons]
                    rcases hout with hlt | hge <;> [exact Or.inl hlt; exact Or.inr (by omega)])
                · simp [hr5])
      refine runs_seq_triple_le hLoop ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · intro addr hout
        dsimp only [startState]
        rw [Function.update_of_ne (by omega)]
      intro st₁ ⟨_, _, _, _, hr2₁, _, _, hr4₁, _, hdat₁, hfr₁⟩
      have hsub_eq : xs.take (xs.length + 1 - 1) = xs := by simp
      have hded_eq : x₀ :: sortedDedupAux x₀ (xs.take (xs.length + 1 - 1)) = sortedDedup (x₀ :: xs) := by
        rw [hsub_eq]; rfl
      rw [hded_eq] at hr4₁ hdat₁ hfr₁
      refine runs_ret_le (by eval_expr)
        ⟨src, dst, rfl, hr4₁, sortedDedup_pairwise hLpair, sortedDedup_mem hLpair, hdat₁, hfr₁⟩ ?_
      dsimp only [dedupContract, Expr.size]
      simp only [List.length_cons]
      omega

theorem binSearch_meetsContract {w : ℕ} {p : Program} {b bSort : ℕ} {L : List ℕ} {key : ℕ}
    (hp : p.HasAt b (sortProcs bSort)) :
    MeetsContract w p (b + sortIdxBinSearch) (binSearchContract w L key) := by
  refine meetsContract_of_runs (hp.get (i := sortIdxBinSearch) (by simp [sortProcs, sortIdxBinSearch]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨a, rfl, hw16, haB, hLpair, hkey_mem, hLat, hLw⟩
  have hlt_a : a < 2 ^ w := hargs a (by simp)
  have hlt_len : L.length < 2 ^ w := hargs L.length (by simp)
  have hlt_key : key < 2 ^ w := hargs key (by simp)
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  let idx := L.idxOf key
  have hidx_lt : idx < L.length := List.idxOf_lt_length_iff.mpr hkey_mem
  have hidx_val : L[idx] = key := List.getElem_idxOf hidx_lt
  refine runs_start_le ?_
  dsimp only [sortProcs, sortIdxBinSearch, List.getElem_cons_succ, List.getElem_cons_zero,
    binSearchStmt]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := L.length) (by eval_expr) ?_
  let logB : ℕ → ℕ := fun d => if d ≤ 1 then 0 else Nat.log 2 (d - 1) + 1
  let Inv : State → Prop := fun st =>
    st.regs 0 = a ∧ st.regs 2 = key ∧ st.mem = mem ∧
    st.regs 3 ≤ idx ∧ idx < st.regs 4 ∧ st.regs 4 ≤ L.length
  let condExpr : Expr := .bin .lt (.bin .add (.reg 3) (.const 1)) (.reg 4)
  let bodyStmt : Stmt :=
    .assign 5 (.bin .add (.reg 3) (.bin .div (.bin .sub (.reg 4) (.reg 3)) (.const 2))) ;;
    .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
    .cond (.bin .lt (.reg 2) (.reg 6))
      (.assign 4 (.reg 5))
      (.assign 3 (.reg 5))
  let mFn : State → ℕ := fun st => st.regs 4 - st.regs 3
  let remFn : State → ℕ := fun st => 45 * logB (st.regs 4 - st.regs 3) + 10
  let condFn : State → ℕ := fun st => if st.regs 3 + 1 < st.regs 4 then 1 else 0
  have hloop : Triple w p Inv (.loop condExpr bodyStmt)
      (normalPost fun st => st.regs 3 = idx ∧ st.mem = mem) remFn := by
    refine Triple.loop_measure (condVal := condFn) (m := mFn) (rem := remFn)
      (fun st hInv => by
        rcases hInv with ⟨_, _, _, hlo, _, hhi⟩
        have hlo1 : st.regs 3 + 1 < 2 ^ w := by omega
        dsimp only [condExpr, condFn]
        split_ifs with hlt <;> simp [Expr.eval, BinOp.eval, h1_lt, hlo1, h0_lt, hlt])
      (fun st hInv hv => by
        rcases hInv with ⟨_, _, hmem, hlo, hhi, _⟩
        dsimp only [condFn] at hv
        have hnot : ¬ (st.regs 3 + 1 < st.regs 4) := by
          by_contra hc; simp [hc] at hv
        have h3eq : st.regs 3 = idx := by omega
        refine ⟨⟨h3eq, hmem⟩, by dsimp only [condExpr, Expr.size, remFn]; omega⟩)
      (fun st hInv hv => by
        rcases hInv with ⟨hr0, hr2, hmem, hlo_idx, hidx_hi, hhi_len⟩
        dsimp only [condFn] at hv
        have hlo1_hi : st.regs 3 + 1 < st.regs 4 := by
          by_contra hc; simp [hc] at hv
        let lo := st.regs 3
        let hi := st.regs 4
        let mid := lo + (hi - lo) / 2
        have hmid_lo : lo < mid := by dsimp only [mid]; omega
        have hmid_hi : mid < hi := by dsimp only [mid]; omega
        have hmid_len : mid < L.length := lt_of_lt_of_le hmid_hi hhi_len
        have hamid_lt : a + mid < 2 ^ w := by omega
        have hval_lt : L[mid] < 2 ^ w := hLw L[mid] (List.getElem_mem hmid_len)
        have hval_mem : st.mem (a + mid) = L[mid] := by
          rw [hmem]; exact hLat mid hmid_len
        refine ⟨35, ?_⟩
        intro s ω' hs_eq
        subst s
        suffices h : ∃ o s' c, Runs w p ω' bodyStmt st o s' c ∧
            (match o with
              | .returned u => normalPost (fun st => st.regs 3 = idx ∧ st.mem = mem) (.returned u) s' ∧
                  condExpr.size + 35 + 1 ≤ remFn st
              | .normal => Inv s' ∧ mFn s' < mFn st ∧ condExpr.size + 35 + remFn s' + 1 ≤ remFn st) ∧
            0 + c ≤ 35 by
          rcases h with ⟨o, s', c, hr, hq, hc⟩
          exact ⟨o, s', c, hr, hq, by simpa using hc⟩
        dsimp only [bodyStmt]
        refine runs_seq_assign_le (v := mid)
          (by simp [Expr.eval, BinOp.eval, h2_lt,
            show hi - lo < 2 ^ w by omega, show (hi - lo) / 2 < 2 ^ w by omega,
            show mid < 2 ^ w by omega, lo, hi, mid]) ?_
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (v := L[mid]) (by simp [Expr.eval, BinOp.eval, hr0, hamid_lt]) hval_mem) ?_
        by_cases hlt_k : key < L[mid]
        · have hidx_mid : idx < mid := by
            by_contra hnot
            have hle : mid ≤ idx := Nat.le_of_not_lt hnot
            rcases lt_or_eq_of_le hle with hlt' | heq
            · exact absurd hlt_k (Nat.not_lt_of_le (Nat.le_of_lt (by
                have := (List.pairwise_iff_getElem.mp hLpair) mid idx hmid_len hidx_lt hlt'
                rwa [hidx_val] at this)))
            · simp [heq, hidx_val] at hlt_k
          refine runs_cond_le (v := 1)
            (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr2, hlt_k, h1_lt]) ?_ ?_
          · intro _
            refine runs_assign_le (v := mid) (by eval_expr) ?_ (by dsimp only [Expr.size]; omega)
            refine ⟨⟨by simp [hr0], by simp [hr2], hmem, by simpa using hlo_idx, hidx_mid,
              by simp; omega⟩, (by dsimp only [mFn]; simp; omega), ?_⟩
            have hnot1 : ¬ (st.regs 4 - st.regs 3 ≤ 1) := by dsimp only [lo, hi] at *; omega
            dsimp only [condExpr, Expr.size, remFn, logB, lo, hi]
            simp only [hnot1, ↓reduceIte, Function.update_self,
              Function.update_of_ne (by decide : (3 : ℕ) ≠ 4),
              Function.update_of_ne (by decide : (3 : ℕ) ≠ 5),
              Function.update_of_ne (by decide : (3 : ℕ) ≠ 6)]
            have hlog := logBound_halve (d := st.regs 4 - st.regs 3) (d' := mid - st.regs 3)
              (by dsimp only [lo, hi] at *; omega)
              (by dsimp only [mid, lo, hi] at *; omega)
            have h45 := Nat.mul_le_mul_left 45 hlog
            dsimp only [mid, lo, hi] at h45 ⊢
            omega
          · intro hc; cases hc
        · have hmid_idx : mid ≤ idx := by
            by_contra hnot
            have hlt' : idx < mid := Nat.lt_of_not_le hnot
            have := (List.pairwise_iff_getElem.mp hLpair) idx mid hidx_lt hmid_len hlt'
            rw [hidx_val] at this
            exact hlt_k this
          refine runs_cond_le (v := 0)
            (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr2, hlt_k, h0_lt]) ?_ ?_
          · intro hc; exact absurd rfl hc
          · intro _
            refine runs_assign_le (v := mid) (by eval_expr) ?_ (by dsimp only [Expr.size]; omega)
            refine ⟨⟨by simp [hr0], by simp [hr2], hmem, by simpa using hmid_idx,
              by simp; omega, hhi_len⟩, (by dsimp only [mFn]; simp; omega), ?_⟩
            have hnot1 : ¬ (st.regs 4 - st.regs 3 ≤ 1) := by dsimp only [lo, hi] at *; omega
            dsimp only [condExpr, Expr.size, remFn, logB, lo, hi]
            simp only [hnot1, ↓reduceIte, Function.update_self,
              Function.update_of_ne (by decide : (4 : ℕ) ≠ 3),
              Function.update_of_ne (by decide : (4 : ℕ) ≠ 5),
              Function.update_of_ne (by decide : (4 : ℕ) ≠ 6)]
            have hlog := logBound_halve (d := st.regs 4 - st.regs 3) (d' := st.regs 4 - mid)
              (by dsimp only [lo, hi] at *; omega)
              (by dsimp only [mid, lo, hi] at *; omega)
            have h45 := Nat.mul_le_mul_left 45 hlog
            dsimp only [mid, lo, hi] at h45 ⊢
            omega)
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState], rfl, Nat.zero_le _, hidx_lt, le_refl _⟩ ?_
  intro st₁ ⟨hr3₁, hmem₁⟩
  refine runs_ret_le (by eval_expr) ⟨a, rfl, hmem₁, hr3₁, hr3₁ ▸ hidx_lt⟩ ?_
  dsimp only [binSearchContract, remFn, logB, Expr.size]
  simp only [Function.update_self, Function.update_of_ne (by decide : (3 : ℕ) ≠ 4), Nat.sub_zero]
  split_ifs with hl
  · omega
  · have hmono : Nat.log 2 (L.length - 1) ≤ Nat.log 2 (L.length + 1) :=
      Nat.log_mono_right (by omega)
    omega

end

end MinCostFlow.DynSpanner.Program

