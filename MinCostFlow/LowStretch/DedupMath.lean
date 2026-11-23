module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.Basic

/-!
# Keeping one lightest pair per pair of ends: the bookkeeping

The pairs are scanned in groups, one group per smaller end `u`. Inside a group, a pair `p` is
known by its larger end `oth p`. The first pass keeps, for each larger end `v`, a mark
`MK v = u + 1` once a pair with larger end `v` has been seen, and the lightest such pair `BS v`
seen so far (`P1`, `P1.nil`, `P1.hit`, `P1.new`). The second pass keeps the pairs `q` with
`BS (oth q) = q`. This file proves the facts about the first pass, for any memory `M` with the
marks at `MARK + v` and the best pairs at `BEST + v`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable (oth wt : ℕ → ℕ) (n u MARK BEST : ℕ)

/-- The state after the first pass has seen the pairs of `l` (all with smaller end `u`). -/
def P1 (l : List ℕ) (M : ℕ → ℕ) : Prop :=
  ∀ v < n, M (MARK + v) ≤ u + 1 ∧ (M (MARK + v) = u + 1 ↔ ∃ p ∈ l, oth p = v) ∧
    (M (MARK + v) = u + 1 → M (BEST + v) ∈ l ∧ oth (M (BEST + v)) = v ∧
      ∀ p ∈ l, oth p = v → wt (M (BEST + v)) ≤ wt p)

variable {oth wt n u MARK BEST}

theorem P1.nil {M : ℕ → ℕ} (h : ∀ v < n, M (MARK + v) ≤ u) : P1 oth wt n u MARK BEST [] M := by
  intro v hv
  have := h v hv
  refine ⟨by omega, ⟨fun h' => by omega, fun ⟨p, hp, _⟩ => by simp at hp⟩, fun h' => by omega⟩

/-- A pair whose larger end is already marked: it replaces the best pair if it is lighter. -/
theorem P1.hit {l : List ℕ} {M : ℕ → ℕ} (h : P1 oth wt n u MARK BEST l M) {p : ℕ}
    (hv : oth p < n) (hm : M (MARK + oth p) = u + 1) (hMB : MARK + n ≤ BEST) :
    P1 oth wt n u MARK BEST (l ++ [p])
      (if wt p < wt (M (BEST + oth p)) then Function.update M (BEST + oth p) p else M) := by
  intro v hvn
  obtain ⟨h1, h2, h3⟩ := h v hvn
  obtain ⟨hb1, hb2, hb3⟩ := h (oth p) hv
  have hb := hb3 hm
  split_ifs with hlt
  · have hM : M (MARK + v) = (Function.update M (BEST + oth p) p) (MARK + v) := by
      rw [Function.update_apply, if_neg (by omega)]
    rw [← hM]
    refine ⟨h1, ⟨fun hmv => ?_, fun ⟨q, hq, hqv⟩ => ?_⟩, fun hmv => ?_⟩
    · obtain ⟨q, hq, hqv⟩ := h2.mp hmv
      exact ⟨q, by simp [hq], hqv⟩
    · rcases List.mem_append.mp hq with hq | hq
      · exact h2.mpr ⟨q, hq, hqv⟩
      · simp at hq; subst hq; subst hqv; exact hm
    · by_cases hvp : v = oth p
      · subst hvp
        simp only [Function.update_self]
        refine ⟨by simp, trivial, fun q hq hqv => ?_⟩
        rcases List.mem_append.mp hq with hq | hq
        · have := hb.2.2 q hq hqv; omega
        · simp at hq; subst hq; exact Nat.le_refl _
      · rw [Function.update_apply, if_neg (by omega)]
        obtain ⟨hc1, hc2, hc3⟩ := h3 hmv
        refine ⟨by simp [hc1], hc2, fun q hq hqv => ?_⟩
        rcases List.mem_append.mp hq with hq | hq
        · exact hc3 q hq hqv
        · simp at hq; subst hq; exact absurd hqv.symm hvp
  · refine ⟨h1, ⟨fun hmv => ?_, fun ⟨q, hq, hqv⟩ => ?_⟩, fun hmv => ?_⟩
    · obtain ⟨q, hq, hqv⟩ := h2.mp hmv
      exact ⟨q, by simp [hq], hqv⟩
    · rcases List.mem_append.mp hq with hq | hq
      · exact h2.mpr ⟨q, hq, hqv⟩
      · simp at hq; subst hq; subst hqv; exact hm
    · obtain ⟨hc1, hc2, hc3⟩ := h3 hmv
      refine ⟨by simp [hc1], hc2, fun q hq hqv => ?_⟩
      rcases List.mem_append.mp hq with hq | hq
      · exact hc3 q hq hqv
      · simp at hq; subst hq; subst hqv; omega

/-- A pair whose larger end is not marked yet: mark it and make the pair the best one. -/
theorem P1.new {l : List ℕ} {M : ℕ → ℕ} (h : P1 oth wt n u MARK BEST l M) {p : ℕ}
    (hv : oth p < n) (hm : M (MARK + oth p) ≠ u + 1) (hMB : MARK + n ≤ BEST) :
    P1 oth wt n u MARK BEST (l ++ [p])
      (Function.update (Function.update M (MARK + oth p) (u + 1)) (BEST + oth p) p) := by
  intro v hvn
  obtain ⟨h1, h2, h3⟩ := h v hvn
  have hnone : ∀ q ∈ l, oth q ≠ oth p := fun q hq hq' => hm ((h (oth p) hv).2.1.mpr ⟨q, hq, hq'⟩)
  by_cases hvp : v = oth p
  · subst hvp
    have e1 : (Function.update (Function.update M (MARK + oth p) (u + 1)) (BEST + oth p) p)
        (MARK + oth p) = u + 1 := by
      rw [Function.update_apply, if_neg (by omega)]; simp
    have e2 : (Function.update (Function.update M (MARK + oth p) (u + 1)) (BEST + oth p) p)
        (BEST + oth p) = p := by simp
    rw [e1, e2]
    refine ⟨Nat.le_refl _, ⟨fun _ => ⟨p, by simp, rfl⟩, fun _ => rfl⟩, fun _ => ⟨by simp, rfl, ?_⟩⟩
    intro q hq hqv
    rcases List.mem_append.mp hq with hq | hq
    · exact absurd hqv (hnone q hq)
    · simp at hq; subst hq; exact Nat.le_refl _
  · simp only [Function.update_apply, if_neg (show MARK + v ≠ BEST + oth p by omega),
      if_neg (show MARK + v ≠ MARK + oth p by omega), if_neg (show BEST + v ≠ BEST + oth p by omega),
      if_neg (show BEST + v ≠ MARK + oth p by omega)]
    refine ⟨h1, ⟨fun hmv => ?_, fun ⟨q, hq, hqv⟩ => ?_⟩, fun hmv => ?_⟩
    · obtain ⟨q, hq, hqv⟩ := h2.mp hmv
      exact ⟨q, by simp [hq], hqv⟩
    · rcases List.mem_append.mp hq with hq | hq
      · exact h2.mpr ⟨q, hq, hqv⟩
      · simp at hq; subst hq; exact absurd hqv.symm hvp
    · obtain ⟨hc1, hc2, hc3⟩ := h3 hmv
      refine ⟨by simp [hc1], hc2, fun q hq hqv => ?_⟩
      rcases List.mem_append.mp hq with hq | hq
      · exact hc3 q hq hqv
      · simp at hq; subst hq; exact absurd hqv.symm hvp

/-- Writes outside the marks and best pairs keep `P1`. -/
theorem P1.frame {l : List ℕ} {M M' : ℕ → ℕ} (h : P1 oth wt n u MARK BEST l M)
    (hM : ∀ v < n, M' (MARK + v) = M (MARK + v) ∧ M' (BEST + v) = M (BEST + v)) :
    P1 oth wt n u MARK BEST l M' := by
  intro v hv
  rw [(hM v hv).1, (hM v hv).2]
  exact h v hv

end MinCostFlow.LowStretch
