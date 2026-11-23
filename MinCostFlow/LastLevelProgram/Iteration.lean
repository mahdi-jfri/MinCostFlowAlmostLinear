module

public import MinCostFlow.LastLevelProgram.Potential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Fixed-point iteration for Lemma 5.5 (page 18)

A round can choose its stretch vector using the current rounded weights.
The weighted guarantee is imposed only on the queries made by the loop.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open scoped BigOperators

/-- The weights used to query round `j`. -/
noncomputable def weights (P : ℕ) (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ) :
    ℕ → ℕ → ℝ
  | 0 => fun _ => 1
  | j + 1 => fun e => updateWeight P ρ (weights P ρ query j e) (query (weights P ρ query j) e)

/-- Every weight queried by the iteration lies on its fixed-point grid. -/
theorem weights_onGrid (P : ℕ) (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ) (j e : ℕ) :
    ∃ a : ℤ, weights P ρ query j e = (a : ℝ) / (2 : ℝ)^P := by
  induction j with
  | zero =>
    refine ⟨(2 : ℤ)^P, ?_⟩
    simp [weights, ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) P)]
  | succ j ih =>
    obtain ⟨a, ha⟩ := ih
    have h := updateWeight_onGrid P ρ (query (weights P ρ query j) e) a
    rwa [← ha] at h

/-- Appendix A.2 bounds the final sum and each edge's accumulated stretch
for the rounded iteration. The second bound is on the actual queried
stretch estimates, including any rounding used to produce them. -/
theorem iteration_bounds (E : Finset ℕ) (P K : ℕ) {ρ W : ℝ}
    (query : (ℕ → ℝ) → ℕ → ℝ) (hρ : 0 < ρ) (hP : 2 * ρ ≤ (2 : ℝ)^P)
    (hK : (K : ℝ) * (W / ρ) ≤ Real.log 2)
    (hs : ∀ j < K, ∀ e ∈ E, 1 ≤ query (weights P ρ query j) e)
    (hmean : ∀ j < K, (∀ e ∈ E, 1 ≤ weights P ρ query j e) →
      (∑ e ∈ E, weights P ρ query j e) ≤ 2 * E.card →
      (∑ e ∈ E, weights P ρ query j e * query (weights P ρ query j) e) ≤
        W * ∑ e ∈ E, weights P ρ query j e)
    (hcap : W * (2 * E.card) ≤ ρ)
    (hW : 0 ≤ W) :
    (∀ j ≤ K, (∀ e ∈ E, 1 ≤ weights P ρ query j e) ∧
      (∑ e ∈ E, weights P ρ query j e) ≤ 2 * E.card) ∧
    (∀ j < K, ∀ e ∈ E, query (weights P ρ query j) e ≤ ρ) ∧
    ∀ e ∈ E, ∑ j ∈ Finset.range K, query (weights P ρ query j) e ≤
      (4 * ρ) * Real.log (2 * E.card) := by
  have hexp : ∀ j ≤ K, Real.exp (j * (W / ρ)) ≤ 2 := by
    intro j hj
    have hlog : (j : ℝ) * (W / ρ) ≤ Real.log 2 :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (div_nonneg hW hρ.le)).trans hK
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr hlog
  have hmass (j : ℕ) (hj : j ≤ K) :
      (E.card : ℝ) * Real.exp (j * (W / ρ)) ≤ 2 * E.card :=
    (mul_le_mul_of_nonneg_left (hexp j hj) (Nat.cast_nonneg _)).trans_eq (mul_comm _ _)
  have hist : ∀ j ≤ K, (∀ e ∈ E, 1 ≤ weights P ρ query j e) ∧
      (∑ e ∈ E, weights P ρ query j e) ≤ (E.card : ℝ) * Real.exp (j * (W / ρ)) := by
    intro j
    induction j with
    | zero => simp [weights]
    | succ j ih =>
      intro hj
      have hj' : j < K := hj
      obtain ⟨hv, hsum⟩ := ih hj'.le
      constructor
      · intro e he
        apply (hv e he).trans
        exact le_add_of_nonneg_right (Num.dyadicFloor_nonneg
          (mul_nonneg (zero_le_one.trans (hv e he))
            (div_nonneg (zero_le_one.trans (hs j hj' e he)) hρ.le)))
      · calc
          _ ≤ Real.exp (W / ρ) * ∑ e ∈ E, weights P ρ query j e :=
            sum_update_le E P hρ hP hv (hs j hj') (hmean j hj' hv (hsum.trans (hmass j hj'.le)))
          _ ≤ Real.exp (W / ρ) * (E.card * Real.exp (j * (W / ρ))) :=
            mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
          _ = _ := by
            rw [mul_left_comm, ← Real.exp_add, Nat.cast_succ]
            congr 2
            ring
  have htot : ∀ j ≤ K, (∀ e ∈ E, 1 ≤ weights P ρ query j e) ∧
      (∑ e ∈ E, weights P ρ query j e) ≤ 2 * E.card := by
    intro j hj
    obtain ⟨hv, hsum⟩ := hist j hj
    exact ⟨hv, hsum.trans (hmass j hj)⟩
  have hroundCap : ∀ j < K, ∀ e ∈ E, query (weights P ρ query j) e ≤ ρ := by
    intro j hj e he
    obtain ⟨hv, hsum⟩ := htot j hj.le
    calc
      _ ≤ weights P ρ query j e * query (weights P ρ query j) e :=
        le_mul_of_one_le_left (zero_le_one.trans (hs j hj e he)) (hv e he)
      _ ≤ ∑ f ∈ E, weights P ρ query j f * query (weights P ρ query j) f :=
        Finset.single_le_sum (fun f hf => mul_nonneg (zero_le_one.trans (hv f hf))
          (zero_le_one.trans (hs j hj f hf))) he
      _ ≤ W * ∑ f ∈ E, weights P ρ query j f := hmean j hj hv hsum
      _ ≤ W * (2 * E.card) := mul_le_mul_of_nonneg_left hsum hW
      _ ≤ ρ := hcap
  refine ⟨htot, hroundCap, fun e he => ?_⟩
  have hpot := exp_sum_le_weight P K hρ hP (v := fun j => weights P ρ query j e)
    (s := fun j => query (weights P ρ query j) e) rfl
    (fun j hj => (htot j hj.le).1 e he)
    (fun j hj => ⟨hs j hj e he, hroundCap j hj e he⟩) (fun _ _ => rfl)
  have hsingle : weights P ρ query K e ≤ ∑ f ∈ E, weights P ρ query K f :=
    Finset.single_le_sum (fun f hf => zero_le_one.trans ((htot K le_rfl).1 f hf)) he
  have hpos : (0 : ℝ) < 2 * E.card := by
    have hp : (0 : ℝ) < E.card := by exact_mod_cast Finset.card_pos.mpr ⟨e, he⟩
    positivity
  have hlog := (hpot.trans (hsingle.trans (htot K le_rfl).2))
  rw [← Real.exp_log hpos, Real.exp_le_exp] at hlog
  exact ((div_le_iff₀ (by positivity : 0 < 4 * ρ)).mp hlog).trans_eq (mul_comm _ _)

end MinCostFlow.LastLevelProgram
