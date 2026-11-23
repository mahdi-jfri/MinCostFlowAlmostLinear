module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Charging the Detect outputs to flow movement

Chen et al., arXiv:2203.00671v2, Lemma 9.4 (pages 71--72), charges every
reported edge to the absolute flow movement since its last report.
This file proves that charging argument with explicit constants. A
per-edge accumulator resets only when that edge is reported. Thus no
unit of movement can pay for two reports. If the total movement per
iteration is at most five detection thresholds, there are at most five
reports per iteration on average.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- The uncharged movement remaining after each Detect stage. At a report,
that edge's accumulated movement is used once and its account resets. -/
@[expose] def detectAccount {m : ℕ} (x : ℕ → Fin m → ℝ)
    (S : ℕ → Finset (Fin m)) : ℕ → Fin m → ℝ
  | 0, _ => 0
  | t+1, e => if e ∈ S (t+1) then 0 else detectAccount x S t e+x (t+1) e

/-- Uncharged movement remains nonnegative when each movement is
nonnegative. -/
theorem detectAccount_nonneg {m : ℕ} (x : ℕ → Fin m → ℝ)
    (S : ℕ → Finset (Fin m)) (hx : ∀ t e, 0 ≤ x t e) (t : ℕ) (e : Fin m) :
    0 ≤ detectAccount x S t e := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    simp only [detectAccount]
    split_ifs
    · exact le_rfl
    · exact add_nonneg ih (hx _ _)

private theorem detect_step_charge {m : ℕ} (x : ℕ → Fin m → ℝ)
    (S : ℕ → Finset (Fin m)) (ε : ℝ) (t : ℕ)
    (hpaid : ∀ e ∈ S (t+1), ε ≤ detectAccount x S t e+x (t+1) e) :
    ε*((S (t+1)).card : ℝ)+(∑ e, detectAccount x S (t+1) e) ≤
      (∑ e, detectAccount x S t e)+(∑ e, x (t+1) e) := by
  classical
  have hh : ∀ e, (if e ∈ S (t+1) then ε else 0)+detectAccount x S (t+1) e ≤
      detectAccount x S t e+x (t+1) e := by
    intro e
    by_cases he : e ∈ S (t+1)
    · simpa only [detectAccount, he, ↓reduceIte, add_zero] using hpaid e he
    · simp only [detectAccount, he, ↓reduceIte, zero_add, le_refl]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hh e)
  simp only [Finset.sum_add_distrib] at hsum
  have hcost : (∑ e : Fin m, if e ∈ S (t+1) then ε else 0) = ε*((S (t+1)).card : ℝ) := by
    simp [Finset.sum_ite_mem, mul_comm]
  rw [hcost] at hsum
  exact hsum

/-- Total detection thresholds paid, plus the remaining movement account,
are bounded by the total movement inserted into the accounts. -/
theorem detect_total_charge {m : ℕ} (x : ℕ → Fin m → ℝ)
    (S : ℕ → Finset (Fin m)) (ε : ℝ) (n : ℕ)
    (hpaid : ∀ t < n, ∀ e ∈ S (t+1), ε ≤ detectAccount x S t e+x (t+1) e) :
    ε*(∑ t ∈ Finset.range n, ((S (t+1)).card : ℝ))+
      (∑ e, detectAccount x S n e) ≤
      ∑ t ∈ Finset.range n, ∑ e, x (t+1) e := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, mul_zero, detectAccount,
      Finset.sum_const_zero, add_zero, le_refl]
  | succ n ih =>
    have hp := ih (fun t ht => hpaid t (Nat.lt_succ_of_lt ht))
    have hs := detect_step_charge x S ε n (hpaid n (Nat.lt_succ_self n))
    simp only [Finset.sum_range_succ, mul_add]
    linarith only [hp, hs]

/-- Chen et al., arXiv:2203.00671v2, Lemma 9.4 (pages 71--72), adapted to
Definition 4.5 with explicit constants. Each detected edge spends one
threshold from its movement account. If an iteration deposits at most
`5ε` total, the total size of the Detect outputs is at most `5n`.
The scaled ratio bound supplies this deposit bound for the IPM. -/
theorem lemma_9_4 {m : ℕ} (x : ℕ → Fin m → ℝ)
    (S : ℕ → Finset (Fin m)) (ε : ℝ) (n : ℕ) (he : 0 < ε)
    (hx : ∀ t e, 0 ≤ x t e)
    (hpaid : ∀ t < n, ∀ e ∈ S (t+1), ε ≤ detectAccount x S t e+x (t+1) e)
    (hbudget : ∀ t < n, (∑ e, x (t+1) e) ≤ 5*ε) :
    (∑ t ∈ Finset.range n, (S (t+1)).card) ≤ 5*n := by
  have hcharge := detect_total_charge x S ε n hpaid
  have hleft : 0 ≤ ∑ e, detectAccount x S n e :=
    Finset.sum_nonneg (fun e _ => detectAccount_nonneg x S hx n e)
  have htotal : (∑ t ∈ Finset.range n, ∑ e, x (t+1) e) ≤ (n : ℝ)*(5*ε) := by
    calc
      _ ≤ ∑ _ ∈ Finset.range n, (5*ε) :=
        Finset.sum_le_sum (fun t ht => hbudget t (Finset.mem_range.mp ht))
      _ = _ := by simp
  have hh : (∑ t ∈ Finset.range n, ((S (t+1)).card : ℝ)) ≤ 5*n := by
    apply (mul_le_mul_iff_right₀ he).mp
    nlinarith only [hcharge, hleft, htotal]
  exact_mod_cast hh

/-- All the movement-account hypotheses can hold: with no movement and
no reported edges, every account remains zero at every horizon. -/
theorem detect_zero_example (m n : ℕ) :
    let x : ℕ → Fin m → ℝ := fun _ _ => 0
    let S : ℕ → Finset (Fin m) := fun _ => ∅
    (∀ t e, 0 ≤ x t e) ∧
      (∀ t < n, ∀ e ∈ S (t+1), (1 : ℝ) ≤ detectAccount x S t e+x (t+1) e) ∧
      (∀ t < n, (∑ e, x (t+1) e) ≤ (5 : ℝ)) := by
  simp

end MinCostFlow.IPM
