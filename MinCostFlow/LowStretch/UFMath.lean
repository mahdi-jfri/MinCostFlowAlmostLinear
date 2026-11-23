module

public import MinCostFlow.LowStretch.ProgFind
public import Mathlib.Data.Finset.Card

/-!
# Union by size

The union-find structure in memory: parents at `UF`, set sizes at `SZ` and a label per set at `TN`
(the current top of the set in the merge tree). `UFRep` says that the structure represents the
labels `top`: two elements have the same root exactly when they have the same label, the root of
`x` holds the label of `x`, a root holds the size of its set, and `2^(dep x)` is at most the size
of the set of `x`. `UFRep.union` hangs the root `r1` of the smaller set below the root `r2` of the
larger one and gives the merged set the label `N`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open Finset

variable {M : ℕ → ℕ} {UF SZ TN n : ℕ} {dep : ℕ → ℕ} {top : ℕ → ℕ}

/-- The set of `r`: the elements whose root is `r`. -/
noncomputable def ufSet (M : ℕ → ℕ) (UF n : ℕ) (dep : ℕ → ℕ) (r : ℕ) : Finset ℕ :=
  (range n).filter (fun x => rt M UF dep x = r)

/-- The roots. -/
noncomputable def ufRoots (M : ℕ → ℕ) (UF n : ℕ) : Finset ℕ :=
  (range n).filter (fun r => M (UF + r) = r)

/-- The union-find structure represents the labels `top`. -/
structure UFRep (M : ℕ → ℕ) (UF SZ TN n : ℕ) (dep : ℕ → ℕ) (top : ℕ → ℕ) : Prop where
  cons : UFCons M UF n dep
  lab : ∀ x < n, M (TN + rt M UF dep x) = top x
  size : ∀ x < n, 2 ^ dep x ≤ M (SZ + rt M UF dep x)
  same : ∀ x < n, ∀ y < n, rt M UF dep x = rt M UF dep y ↔ top x = top y
  card : ∀ r < n, M (UF + r) = r → M (SZ + r) = (ufSet M UF n dep r).card

theorem UFRep.size_le (h : UFRep M UF SZ TN n dep top) {r : ℕ} (hr : r < n)
    (hroot : M (UF + r) = r) : M (SZ + r) ≤ n := by
  rw [h.card r hr hroot]
  exact (card_filter_le _ _).trans (by simp)

theorem UFRep.dep_le (h : UFRep M UF SZ TN n dep top) {x : ℕ} (hx : x < n) : 2 ^ dep x ≤ n :=
  (h.size x hx).trans (h.size_le (h.cons.rt_lt hx) (h.cons.rt_is_root hx))

/-- The start: every element is its own root, with size `1` and label itself. -/
theorem ufRep_init (h : ∀ x < n, M (UF + x) = x ∧ M (SZ + x) = 1 ∧ M (TN + x) = x) :
    UFRep M UF SZ TN n (fun _ => 0) id := by
  have hrt : ∀ x, rt M UF (fun _ => 0) x = x := fun x => rfl
  refine ⟨fun x hx => ⟨by rw [(h x hx).1]; exact hx, by simp [(h x hx).1], fun hne =>
    absurd (h x hx).1 hne⟩, fun x hx => by rw [hrt, (h x hx).2.2]; rfl,
    fun x hx => by rw [hrt, (h x hx).2.1]; simp, fun x _ y _ => by simp [hrt], fun r hr _ => ?_⟩
  rw [(h r hr).2.1]
  unfold ufSet
  simp only [hrt]
  rw [show (range n).filter (fun x => x = r) = {r} by
    ext x; simp only [mem_filter, mem_range, mem_singleton]
    exact ⟨fun hx => hx.2, fun hx => ⟨by omega, hx⟩⟩]
  simp

/-- Along the path from `x` to its root, the depth goes down by one per step. -/
theorem UFCons.dep_iter (h : UFCons M UF n dep) {x : ℕ} (hx : x < n) {j : ℕ} (hj : j ≤ dep x) :
    dep ((fun y => M (UF + y))^[j] x) = dep x - j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ih' := ih (by omega)
    rw [Function.iterate_succ_apply']
    set y := (fun y => M (UF + y))^[j] x
    have hy : y < n := h.iter_lt hx j
    have hne : M (UF + y) ≠ y := fun e => by have := (h y hy).2.1.mp e; omega
    have := (h y hy).2.2 hne
    show dep (M (UF + y)) = dep x - (j + 1)
    omega

/-- Changing the parent of one root `r1` does not change the path below any root. -/
theorem UFCons.iter_eq (h : UFCons M UF n dep) {f' : ℕ → ℕ} {r1 : ℕ}
    (hr1 : M (UF + r1) = r1) (hf' : ∀ y < n, y ≠ r1 → f' y = M (UF + y)) {x : ℕ} (hx : x < n)
    {j : ℕ} (hj : j ≤ dep x) : f'^[j] x = (fun y => M (UF + y))^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
    set y := (fun y => M (UF + y))^[j] x
    have hy : y < n := h.iter_lt hx j
    have hdy : dep y = dep x - j := h.dep_iter hx (j := j) (by omega)
    have hne : y ≠ r1 := fun e => by
      have := (h y hy).2.1.mp (by rw [e]; exact hr1)
      omega
    exact hf' y hy hne

/-- Hanging the root `r1` below the root `r2`. -/
theorem UFRep.union (h : UFRep M UF SZ TN n dep top) {r1 r2 N : ℕ} (h1 : r1 < n) (h2 : r2 < n)
    (hr1 : M (UF + r1) = r1) (hr2 : M (UF + r2) = r2) (hne : r1 ≠ r2)
    (hsz : M (SZ + r1) ≤ M (SZ + r2)) (hl1 : UF + n ≤ SZ) (hl2 : SZ + n ≤ TN)
    (hN : ∀ x < n, top x ≠ N) :
    let M' := Function.update (Function.update (Function.update M (UF + r1) r2) (SZ + r2)
      (M (SZ + r1) + M (SZ + r2))) (TN + r2) N
    let dep' := fun x => if rt M UF dep x = r1 then dep x + 1 else dep x
    UFRep M' UF SZ TN n dep'
        (fun x => if rt M UF dep x = r1 ∨ rt M UF dep x = r2 then N else top x) ∧
      (∀ x < n, rt M' UF dep' x = if rt M UF dep x = r1 then r2 else rt M UF dep x) ∧
      ufRoots M' UF n = (ufRoots M UF n).erase r1 := by
  intro M' dep'
  have hc := h.cons
  -- the new parents
  have hpar : ∀ y < n, M' (UF + y) = if y = r1 then r2 else M (UF + y) := fun y hy => by
    simp only [M', Function.update_apply]
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases hy1 : y = r1
    · subst hy1; simp
    · rw [if_neg (by omega), if_neg hy1]
  have hroot1 : rt M UF dep r1 = r1 := hc.rt_root h1 hr1
  have hroot2 : rt M UF dep r2 = r2 := hc.rt_root h2 hr2
  have hdep1 : dep r1 = 0 := (hc r1 h1).2.1.mp hr1
  have hdep2 : dep r2 = 0 := (hc r2 h2).2.1.mp hr2
  -- the path to the old root is unchanged
  have hpath : ∀ x < n, (fun y => M' (UF + y))^[dep x] x = rt M UF dep x := fun x hx =>
    hc.iter_eq hr1 (fun y hy hy1 => by rw [hpar y hy, if_neg hy1]) hx le_rfl
  have hrt' : ∀ x < n, rt M' UF dep' x = if rt M UF dep x = r1 then r2 else rt M UF dep x := by
    intro x hx
    show (fun y => M' (UF + y))^[dep' x] x = _
    by_cases hx1 : rt M UF dep x = r1
    · simp only [dep', if_pos hx1]
      rw [Function.iterate_succ_apply', hpath x hx, hx1, hpar r1 h1, if_pos rfl]
    · simp only [dep', if_neg hx1]
      exact hpath x hx
  have hcons' : UFCons M' UF n dep' := by
    intro x hx
    rw [hpar x hx]
    have hcx := hc x hx
    by_cases hx1 : x = r1
    · subst hx1
      simp only [if_true, dep', hroot1]
      refine ⟨h2, ⟨fun e => absurd e.symm hne, fun e => by omega⟩, fun _ => ?_⟩
      simp only [hroot2, if_neg (Ne.symm hne), hdep1, hdep2]
    · rw [if_neg hx1]
      refine ⟨hcx.1, ?_, fun hnr => ?_⟩
      · by_cases hrx : rt M UF dep x = r1
        · simp only [dep', if_pos hrx]
          constructor
          · intro e; exfalso; rw [hc.rt_root hx e] at hrx; exact hx1 hrx
          · intro e; omega
        · simp only [dep', if_neg hrx]
          exact hcx.2.1
      · have hrp := hc.rt_par hx hnr
        have := hcx.2.2 hnr
        by_cases hrx : rt M UF dep x = r1
        · simp only [dep', if_pos hrx, hrp]; omega
        · simp only [dep', if_neg hrx, hrp]; omega
  refine ⟨⟨hcons', fun x hx => ?_, fun x hx => ?_, fun x hx y hy => ?_, fun r hr hroot => ?_⟩,
    hrt', ?_⟩
  · -- labels
    rw [hrt' x hx]
    have hrlt := hc.rt_lt hx
    by_cases hx1 : rt M UF dep x = r1
    · rw [if_pos hx1, if_pos (Or.inl hx1)]; simp [M']
    · rw [if_neg hx1]
      by_cases hx2 : rt M UF dep x = r2
      · rw [if_pos (Or.inr hx2), hx2]; simp [M']
      · rw [if_neg (by tauto)]
        simp only [M', Function.update_apply]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        exact h.lab x hx
  · -- sizes
    rw [hrt' x hx]
    have hrlt := hc.rt_lt hx
    have hs := h.size x hx
    by_cases hx1 : rt M UF dep x = r1
    · rw [if_pos hx1]
      simp only [dep', if_pos hx1, M', Function.update_apply, if_neg (show SZ + r2 ≠ TN + r2 by omega),
        if_true]
      rw [hx1] at hs
      rw [pow_succ]; omega
    · rw [if_neg hx1]
      simp only [dep', if_neg hx1]
      by_cases hx2 : rt M UF dep x = r2
      · rw [hx2] at hs ⊢
        simp only [M', Function.update_apply, if_neg (show SZ + r2 ≠ TN + r2 by omega), if_true]
        omega
      · simp only [M', Function.update_apply]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        exact hs
  · -- same roots, same labels
    rw [hrt' x hx, hrt' y hy]
    have hsame := h.same x hx y hy
    have hNx := hN x hx
    have hNy := hN y hy
    have hlx := hc.rt_lt hx
    have hly := hc.rt_lt hy
    by_cases ix : rt M UF dep x = r1 ∨ rt M UF dep x = r2 <;>
      by_cases iy : rt M UF dep y = r1 ∨ rt M UF dep y = r2
    · rw [if_pos iy, if_pos ix]
      have a1 : (if rt M UF dep x = r1 then r2 else rt M UF dep x) = r2 := by
        rcases ix with e | e <;> simp [e, hne]
      have a2 : (if rt M UF dep y = r1 then r2 else rt M UF dep y) = r2 := by
        rcases iy with e | e <;> simp [e, hne]
      rw [a1, a2]; simp
    · rw [if_pos ix, if_neg iy]
      have a1 : (if rt M UF dep x = r1 then r2 else rt M UF dep x) = r2 := by
        rcases ix with e | e <;> simp [e, hne]
      have a2 : (if rt M UF dep y = r1 then r2 else rt M UF dep y) = rt M UF dep y := by
        rw [if_neg (fun e => iy (Or.inl e))]
      rw [a1, a2]
      exact ⟨fun e => absurd e.symm (fun e' => iy (Or.inr e')), fun e => absurd e.symm hNy⟩
    · rw [if_neg ix, if_pos iy]
      have a1 : (if rt M UF dep y = r1 then r2 else rt M UF dep y) = r2 := by
        rcases iy with e | e <;> simp [e, hne]
      have a2 : (if rt M UF dep x = r1 then r2 else rt M UF dep x) = rt M UF dep x := by
        rw [if_neg (fun e => ix (Or.inl e))]
      rw [a1, a2]
      exact ⟨fun e => absurd e (fun e' => ix (Or.inr e')), fun e => absurd e hNx⟩
    · rw [if_neg ix, if_neg iy, if_neg (fun e => ix (Or.inl e)), if_neg (fun e => iy (Or.inl e))]
      exact hsame
  · -- sizes of roots
    have hr1' : r ≠ r1 := fun e => by
      subst e; rw [hpar r hr, if_pos rfl] at hroot; exact hne hroot.symm
    rw [hpar r hr, if_neg hr1'] at hroot
    have hset : ∀ x < n, (rt M' UF dep' x = r ↔ rt M UF dep x = r ∨ (r = r2 ∧ rt M UF dep x = r1)) :=
      fun x hx => by
        rw [hrt' x hx]
        split_ifs with hx1
        · constructor
          · intro e; exact Or.inr ⟨e.symm, hx1⟩
          · rintro (e | ⟨e1, -⟩)
            · exact absurd (e.symm.trans hx1) hr1'
            · exact e1.symm
        · constructor
          · exact Or.inl
          · rintro (e | ⟨-, e⟩)
            · exact e
            · exact absurd e hx1
    by_cases hr2' : r = r2
    · subst hr2'
      have : ufSet M' UF n dep' r = ufSet M UF n dep r ∪ ufSet M UF n dep r1 := by
        ext x
        simp only [ufSet, mem_union, mem_filter, mem_range]
        constructor
        · rintro ⟨hx, e⟩
          rcases (hset x hx).mp e with e | ⟨-, e⟩
          · exact Or.inl ⟨hx, e⟩
          · exact Or.inr ⟨hx, e⟩
        · rintro (⟨hx, e⟩ | ⟨hx, e⟩)
          · exact ⟨hx, (hset x hx).mpr (Or.inl e)⟩
          · exact ⟨hx, (hset x hx).mpr (Or.inr ⟨rfl, e⟩)⟩
      rw [this, card_union_of_disjoint]
      · simp only [M', Function.update_apply, if_neg (show SZ + r ≠ TN + r by omega), if_true]
        rw [h.card r1 h1 hr1, h.card r h2 hr2]
        omega
      · rw [disjoint_left]
        intro x hx hx'
        simp only [ufSet, mem_filter] at hx hx'
        exact hne (hx'.2.symm.trans hx.2)
    · have hm' : M' (SZ + r) = M (SZ + r) := by
        simp only [M', Function.update_apply]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [hm', h.card r hr hroot]
      congr 1
      ext x
      simp only [ufSet, mem_filter, mem_range]
      constructor
      · rintro ⟨hx, e⟩; exact ⟨hx, (hset x hx).mpr (Or.inl e)⟩
      · rintro ⟨hx, e⟩
        rcases (hset x hx).mp e with e | ⟨e, -⟩
        · exact ⟨hx, e⟩
        · exact absurd e hr2'
  · -- roots
    ext r
    simp only [ufRoots, mem_filter, mem_range, mem_erase]
    constructor
    · rintro ⟨hr, e⟩
      rw [hpar r hr] at e
      split_ifs at e with hr1'
      · subst hr1'; exact absurd e.symm hne
      · exact ⟨hr1', hr, e⟩
    · rintro ⟨hr1', hr, e⟩
      exact ⟨hr, by rw [hpar r hr, if_neg hr1', e]⟩

end MinCostFlow.LowStretch
