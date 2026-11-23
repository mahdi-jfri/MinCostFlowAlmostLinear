module

public import MinCostFlow.LSF.Program.SubtreeSumMath

/-!
# Passes from the root down

Several passes walk a top-down order `Q` forward and store, at each index `x` other than the
root, a value that depends only on the values already stored at `x` and at its parent. The rule
of such a pass is *local*: whether it holds at `y` depends only on the stored values at `y` and
`par y` (`TDLocal`). Writing the value at `x = Q[j]` then keeps the rule at the indices before
`x`, since `x` is neither one of them nor the parent of one of them (`td_step`).
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow

/-- The rule at `y` depends only on the values at `y` and at `par y`. -/
def TDLocal (par : ℕ → ℕ) (rule : (ℕ → ℕ) → ℕ → Prop) : Prop :=
  ∀ f f' y, f y = f' y → f (par y) = f' (par y) → rule f y → rule f' y

variable {n r : ℕ} {par : ℕ → ℕ} {Q : List ℕ}

lemma TopDownOrder.ne_root (hQ : TopDownOrder n r par Q) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j < Q.length) : Q[j] ≠ r := by
  intro h
  have hn : 0 < n := by rw [← hQ.len]; omega
  rw [← hQ.head_eq hn] at h
  have := (hQ.nodup.getElem_inj_iff).mp h
  omega

lemma list_take_succ_eq {j : ℕ} (hj : j < Q.length) :
    Q.take (j + 1) = Q.take j ++ [Q[j]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]

/-- Writing at `Q[j]` a value that meets the rule keeps the rule on `Q.take (j + 1)`. -/
lemma td_step (hQ : TopDownOrder n r par Q) {rule : (ℕ → ℕ) → ℕ → Prop}
    (hloc : TDLocal par rule) {f : ℕ → ℕ} {j : ℕ} (hj : j < Q.length)
    (h : ∀ y ∈ Q.take j, y ≠ r → rule f y) {v : ℕ}
    (hv : Q[j] ≠ r → rule (Function.update f Q[j] v) Q[j]) :
    ∀ y ∈ Q.take (j + 1), y ≠ r → rule (Function.update f Q[j] v) y := by
  have hxt : Q[j] ∉ Q.take j := hQ.not_mem_take hj
  intro y hy hyr
  rw [list_take_succ_eq hj, List.mem_append, List.mem_singleton] at hy
  rcases hy with hy | rfl
  · obtain ⟨k, hk, hky⟩ := List.mem_iff_getElem.mp hy
    rw [List.length_take] at hk
    rw [List.getElem_take] at hky
    have hpk : par y ∈ Q.take j := by
      rw [← hky] at hyr ⊢
      exact (List.take_prefix_take_left (by omega)).subset (hQ.after k (by omega) hyr)
    refine hloc f _ y ?_ ?_ (h y hy hyr)
    · exact (Function.update_of_ne (fun h => hxt (by rw [← h]; exact hy)) _ _).symm
    · exact (Function.update_of_ne (fun h => hxt (by rw [← h]; exact hpk)) _ _).symm
  · exact hv hyr

/-- The values `y ↦ mem (a + y)` after one store at `a + x`. -/
lemma update_shift (mem : ℕ → ℕ) (a x v : ℕ) :
    (fun y => Function.update mem (a + x) v (a + y)) =
      Function.update (fun y => mem (a + y)) x v := by
  funext y
  by_cases hyx : y = x
  · subst hyx; simp
  · rw [Function.update_of_ne (by omega), Function.update_of_ne hyx]

/-- Selection without a branch. -/
lemma sel_eq {c a a' : ℕ} (P : Prop) [Decidable P] (hc : c = if P then 1 else 0) :
    c * a + (1 - c) * a' = if P then a else a' := by
  subst hc; split_ifs <;> simp

lemma mul_le_self_of_le_one {c a : ℕ} (hc : c ≤ 1) : c * a ≤ a := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h <;> subst h <;> simp

lemma sel_le {c a a' B : ℕ} (hc : c ≤ 1) (ha : a ≤ B) (ha' : a' ≤ B) :
    c * a + (1 - c) * a' ≤ B := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h <;> subst h <;> simp <;> omega

/-- The end of block `y` lies within `n` blocks. -/
lemma blk_end {y n : ℕ} (K : ℕ) (hy : y < n) : y * K + K ≤ n * K := by
  have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hy)
  rwa [Nat.succ_mul] at this

/-- Two different blocks do not overlap. -/
lemma blk_disj {a b : ℕ} (K : ℕ) (hab : a ≠ b) :
    a * K + K ≤ b * K ∨ b * K + K ≤ a * K := by
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · left; exact blk_end K h
  · right; exact blk_end K h

end MinCostFlow.LSF.Program
