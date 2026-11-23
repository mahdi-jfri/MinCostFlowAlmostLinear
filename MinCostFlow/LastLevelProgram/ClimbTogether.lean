module

public import MinCostFlow.LastLevelProgram.AncestorRow
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
# Climbing two vertices after depth alignment

Starting with the largest row, take a jump only if the resulting
vertices differ. The pass finds the last distinct pair immediately
below their first common ancestor.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

/-- Take a jump if the two ancestors at this level remain distinct. -/
def climbTogetherStep (parent : ℕ → ℕ) (k : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  let u := ancestorJump parent k s.1
  let v := ancestorJump parent k s.2
  if u = v then s else (u,v)

/-- Process rows in decreasing order, from `count - 1` through zero. -/
def climbTogether (parent : ℕ → ℕ) : ℕ → (ℕ × ℕ) → ℕ × ℕ
  | 0, s => s
  | count+1, s => climbTogether parent count (climbTogetherStep parent count s)

/-- The two resulting vertices are exactly one step short of the
first meeting distance. -/
theorem climbTogether_exact (parent : ℕ → ℕ) (count : ℕ) (s : ℕ × ℕ) (d : ℕ)
    (hd : 0 < d) (hbound : d ≤ 2^count)
    (hmeet : ∀ k, (parent^[k]) s.1 = (parent^[k]) s.2 ↔ d ≤ k) :
    climbTogether parent count s = ((parent^[d-1]) s.1,(parent^[d-1]) s.2) := by
  induction count generalizing s d with
  | zero =>
    have hd1 : d = 1 := by simp at hbound; omega
    subst d
    simp [climbTogether]
  | succ count ih =>
    rw [climbTogether]
    have hmeet' : ancestorJump parent count s.1 = ancestorJump parent count s.2 ↔ d ≤ 2^count :=
      hmeet _
    by_cases hsmall : d ≤ 2^count
    · rw [climbTogetherStep, ite_eq_left (hmeet'.2 hsmall)]
      exact ih s d hd hsmall hmeet
    · let t := (ancestorJump parent count s.1,ancestorJump parent count s.2)
      have hd' : 0 < d-2^count := by omega
      have hbound' : d-2^count ≤ 2^count := by
        rw [pow_succ, Nat.mul_two] at hbound
        omega
      have hshift (k : ℕ) :
          (parent^[k]) t.1 = (parent^[k]) t.2 ↔ d-2^count ≤ k := by
        change (parent^[k]) ((parent^[2^count]) s.1) =
          (parent^[k]) ((parent^[2^count]) s.2) ↔ _
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, hmeet]
        omega
      rw [climbTogetherStep, ite_eq_right (fun h => hsmall (hmeet'.1 h))]
      change climbTogether parent count t = _
      rw [ih t (d-2^count) hd' hbound' hshift]
      dsimp only [t, ancestorJump]
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
        show d - 2^count - 1 + 2^count = d-1 by omega]

/-- Once two parent walks meet they agree at every later step. -/
theorem parent_iterates_meet_mono (parent : ℕ → ℕ) {u v a b : ℕ}
    (ha : (parent^[a]) u = (parent^[a]) v) (hab : a ≤ b) :
    (parent^[b]) u = (parent^[b]) v := by
  have he : b = b-a+a := by omega
  rw [he, Function.iterate_add_apply, Function.iterate_add_apply, ha]

/-- With an upper bound on the first meeting, the pass and one parent
lookup return that common ancestor for distinct vertices. -/
theorem climbTogether_parent (parent : ℕ → ℕ) (count u v : ℕ)
    (hne : u ≠ v) (hroot : (parent^[2^count]) u = (parent^[2^count]) v) :
    let d := Nat.find (show ∃ k, (parent^[k]) u = (parent^[k]) v from ⟨2^count,hroot⟩)
    parent (climbTogether parent count (u,v)).1 = (parent^[d]) u := by
  classical
  intro d
  let hExists : ∃ k, (parent^[k]) u = (parent^[k]) v := ⟨2^count,hroot⟩
  have hd : 0 < d := by
    by_contra h
    have he : d = 0 := by omega
    have ht : (parent^[d]) u = (parent^[d]) v := Nat.find_spec hExists
    rw [he] at ht
    exact hne ht
  have hbound : d ≤ 2^count := Nat.find_min' hExists hroot
  have hmeet (k : ℕ) : (parent^[k]) (u,v).1 = (parent^[k]) (u,v).2 ↔ d ≤ k :=
    ⟨Nat.find_min' hExists, parent_iterates_meet_mono parent (Nat.find_spec hExists)⟩
  rw [climbTogether_exact parent count (u,v) d hd hbound hmeet]
  change parent ((parent^[d-1]) u) = _
  have he : d = (d-1).succ := by omega
  conv_rhs => rw [he, Function.iterate_succ_apply']

end MinCostFlow.LastLevelProgram
