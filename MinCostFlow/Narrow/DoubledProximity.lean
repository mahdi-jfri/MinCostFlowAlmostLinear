module

public import MinCostFlow.Narrow.Defs
import MinCostFlow.Scaling.CapacitySolverModel
import MinCostFlow.Scaling.IntegralOptimality
import MinCostFlow.Scaling.ResidualGap
import MinCostFlow.Scaling.CycleDecomposition
import MinCostFlow.Scaling.CycleSum
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Proximity after doubling capacities

This file proves the bit-scaling proximity theorem (Lemma 1): if `g` is an
integral optimal circulation of `I`, then the doubled instance `doubled I b`
with `b e ≤ 1` has a real optimal circulation `h` satisfying
`|h e - 2 * g e| ≤ I.m` for every edge `e`.

The proof decomposes the lifted residual difference `h₀ - 2g` of an optimum
`h₀` into simple cycles, drops cycles of nonnegative cost, and shows that each
negative-cost cycle uses a forward slot where `g e = I.capacity e` and
`b e = 1`. Since each such slot has residual capacity `1`, the total amount of
all negative-cost cycles is at most `I.m`, bounding every coordinate change.
-/

public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling

/-- Doubling an integral feasible flow of `I` yields a feasible flow of
`doubled I b` for any nonnegative bit vector `b`. -/
theorem doubled_feasible_two_mul (I : Circulation) (b : Fin I.m → ℕ)
    (g : Fin I.m → ℤ) (hg : I.Feasible (fun e => (g e : ℝ))) :
    (doubled I b).Feasible (fun e => ((2 * g e : ℤ) : ℝ)) := by
  constructor
  · intro v
    have hmul : (doubled I b).balance (fun e => ((2 * g e : ℤ) : ℝ)) v =
        2 * I.balance (fun e => (g e : ℝ)) v := by
      have hcast : (fun e => ((2 * g e : ℤ) : ℝ)) = fun e => 2 * (g e : ℝ) := by
        funext e; simp
      rw [hcast]
      exact I.balance_const_mul 2 (fun e => (g e : ℝ)) v
    rw [hmul, hg.1 v, mul_zero]
  · intro e
    have hge := hg.2 e
    have hcap : ((doubled I b).capacity e : ℝ) = 2 * (I.capacity e : ℝ) + (b e : ℝ) := by
      simp
    have hb0 : (0 : ℝ) ≤ (b e : ℝ) := Nat.cast_nonneg _
    simp only [Int.cast_mul, Int.cast_ofNat]
    rw [hcap]
    constructor <;> linarith only [hge.1, hge.2, hb0]

/-- Doubling an integral optimum of `I` yields an optimum of the purely
doubled instance `doubled I (fun _ => 0)`. -/
theorem doubled_zero_optimal_two_mul (I : Circulation) (g : Fin I.m → ℤ)
    (hg : I.Optimal (fun e => (g e : ℝ))) :
    (doubled I (fun _ => 0)).Optimal (fun e => ((2 * g e : ℤ) : ℝ)) := by
  refine ⟨doubled_feasible_two_mul I (fun _ => 0) g hg.1, ?_⟩
  intro f hf
  have hhalf : I.Feasible (fun e => (1 / 2 : ℝ) * f e) := by
    constructor
    · intro v
      rw [I.balance_const_mul]
      change (1 / 2 : ℝ) * (doubled I (fun _ => 0)).balance f v = 0
      rw [hf.1 v, mul_zero]
    · intro e
      have hfe := hf.2 e
      have hcap : ((doubled I (fun _ => 0)).capacity e : ℝ) = 2 * (I.capacity e : ℝ) := by
        simp
      rw [hcap] at hfe
      constructor <;> linarith only [hfe.1, hfe.2]
  have hcmp := hg.2 _ hhalf
  have hobj_half : I.objective (fun e => (1 / 2 : ℝ) * f e) =
      (1 / 2 : ℝ) * (doubled I (fun _ => 0)).objective f := by
    simp only [Circulation.objective, doubled, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hobj_two : (doubled I (fun _ => 0)).objective (fun e => ((2 * g e : ℤ) : ℝ)) =
      2 * I.objective (fun e => (g e : ℝ)) := by
    simp only [Circulation.objective, doubled, Int.cast_mul, Int.cast_ofNat, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hobj_half] at hcmp
  rw [hobj_two]
  linarith only [hcmp]

private lemma cycleSum_filter_le (R : Circulation)
    (terms : List (Circulation.CycleTerm R)) (p : Circulation.CycleTerm R → Bool)
    (ht : ∀ t ∈ terms, 0 ≤ t.amount) (a : Fin R.m) :
    R.cycleSum (terms.filter p) a ≤ R.cycleSum terms a := by
  induction terms with
  | nil => simp [Circulation.cycleSum]
  | cons t ts ih =>
    have hts : ∀ u ∈ ts, 0 ≤ u.amount := fun u hu => ht u (List.mem_cons_of_mem t hu)
    have hta : 0 ≤ t.amount * (t.walk.count a : ℝ) :=
      mul_nonneg (ht t List.mem_cons_self) (Nat.cast_nonneg _)
    have hrec := ih hts
    simp only [Circulation.cycleSum, List.filter_cons] at hrec ⊢
    cases hpt : p t with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
      linarith only [hta, hrec]
    | true =>
      simp only [↓reduceIte, List.map_cons, List.sum_cons]
      linarith only [hrec]

private lemma sum_filter_neg_cost_le (R : Circulation)
    (terms : List (Circulation.CycleTerm R))
    (ht : ∀ t ∈ terms, 0 ≤ t.amount) :
    ((terms.filter (fun t => decide (t.walk.cost < 0))).map
        (fun t => t.amount * (t.walk.cost : ℝ))).sum ≤
      (terms.map (fun t => t.amount * (t.walk.cost : ℝ))).sum := by
  induction terms with
  | nil => simp
  | cons t ts ih =>
    have hts : ∀ u ∈ ts, 0 ≤ u.amount := fun u hu => ht u (List.mem_cons_of_mem t hu)
    have hrec := ih hts
    by_cases hneg : t.walk.cost < 0
    · simp only [List.filter_cons, decide_eq_true_eq.mpr hneg, ↓reduceIte, List.map_cons,
        List.sum_cons]
      linarith only [hrec]
    · have hge : (0 : ℝ) ≤ (t.walk.cost : ℝ) := by
        exact_mod_cast (show (0 : ℤ) ≤ t.walk.cost by omega)
      have hterm : 0 ≤ t.amount * (t.walk.cost : ℝ) :=
        mul_nonneg (ht t List.mem_cons_self) hge
      simp only [List.filter_cons, decide_eq_false_iff_not.mpr hneg, Bool.false_eq_true,
        ↓reduceIte, List.map_cons, List.sum_cons]
      linarith only [hterm, hrec]

private lemma cycleSum_le_sum_amounts (R : Circulation)
    (terms : List (Circulation.CycleTerm R))
    (ht : ∀ t ∈ terms, 0 ≤ t.amount ∧ ∀ a, t.walk.count a ≤ 1) (a : Fin R.m) :
    R.cycleSum terms a ≤ (terms.map (fun t => t.amount)).sum := by
  induction terms with
  | nil => simp [Circulation.cycleSum]
  | cons t ts ih =>
    have hts : ∀ u ∈ ts, 0 ≤ u.amount ∧ ∀ k, u.walk.count k ≤ 1 :=
      fun u hu => ht u (List.mem_cons_of_mem t hu)
    have hrec := ih hts
    have hta := (ht t List.mem_cons_self).1
    have hca : (t.walk.count a : ℝ) ≤ 1 := by
      exact_mod_cast (ht t List.mem_cons_self).2 a
    have hterm : t.amount * (t.walk.count a : ℝ) ≤ t.amount := by
      nlinarith only [hta, hca]
    simp only [Circulation.cycleSum, List.map_cons, List.sum_cons] at hrec ⊢
    linarith only [hterm, hrec]

private lemma sum_amounts_le_sum_finset (R : Circulation) (S : Finset (Fin R.m))
    (terms : List (Circulation.CycleTerm R))
    (ht : ∀ t ∈ terms, 0 ≤ t.amount ∧ ∃ a ∈ S, 0 < t.walk.count a) :
    (terms.map (fun t => t.amount)).sum ≤ ∑ a ∈ S, R.cycleSum terms a := by
  induction terms with
  | nil => simp [Circulation.cycleSum]
  | cons t ts ih =>
    have hts : ∀ u ∈ ts, 0 ≤ u.amount ∧ ∃ a ∈ S, 0 < u.walk.count a :=
      fun u hu => ht u (List.mem_cons_of_mem t hu)
    have hrec := ih hts
    obtain ⟨hta, a₀, ha₀S, hca₀⟩ := ht t List.mem_cons_self
    have h1 : (1 : ℝ) ≤ (t.walk.count a₀ : ℝ) := by exact_mod_cast hca₀
    have hsingle : t.amount ≤ ∑ a ∈ S, t.amount * (t.walk.count a : ℝ) := by
      have hle1 : t.amount ≤ t.amount * (t.walk.count a₀ : ℝ) := by nlinarith only [hta, h1]
      have hle2 : t.amount * (t.walk.count a₀ : ℝ) ≤ ∑ a ∈ S, t.amount * (t.walk.count a : ℝ) :=
        Finset.single_le_sum (fun a _ => mul_nonneg hta (Nat.cast_nonneg _)) ha₀S
      exact le_trans hle1 hle2
    have hsplit : (∑ a ∈ S, R.cycleSum (t :: ts) a) =
        (∑ a ∈ S, t.amount * (t.walk.count a : ℝ)) + ∑ a ∈ S, R.cycleSum ts a := by
      simp only [Circulation.cycleSum, List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    rw [hsplit]
    simp only [List.map_cons, List.sum_cons]
    linarith only [hsingle, hrec]

private lemma neg_cycle_uses_saturated_slot (I : Circulation) (b : Fin I.m → ℕ)
    (hb : ∀ e, b e ≤ 1) (g : Fin I.m → ℤ) (hg : I.Optimal (fun e => (g e : ℝ)))
    (t : Circulation.CycleTerm ((doubled I b).residual (fun e => 2 * g e)))
    (hcost : t.walk.cost < 0) (hsimple : ∀ a, t.walk.count a ≤ 1) :
    ∃ e : Fin I.m, g e = (I.capacity e : ℤ) ∧ b e = 1 ∧ 0 < t.walk.count (Fin.castAdd I.m e) := by
  by_contra hno
  push Not at hno
  let I₂ := doubled I (fun _ => 0)
  let g2 : Fin I.m → ℤ := fun e => 2 * g e
  have hzero : (I₂.residual g2).Optimal (fun _ => 0) :=
    I₂.zero_residual_optimal g2 (doubled_zero_optimal_two_mul I g hg)
  let f : Fin (I.m + I.m) → ℝ := fun a => (t.walk.count a : ℝ)
  have hf : (I₂.residual g2).Feasible f := by
    constructor
    · intro v
      have hbal : (I₂.residual g2).balance f v =
          ((doubled I b).residual g2).balance f v := rfl
      rw [hbal, t.walk.balance_count, sub_self]
    · intro a
      refine ⟨Nat.cast_nonneg _, ?_⟩
      by_cases hz : t.walk.count a = 0
      · simp only [f, hz, Nat.cast_zero]
        exact Nat.cast_nonneg _
      · have hpos : 0 < t.walk.count a := Nat.pos_of_ne_zero hz
        have hact : 0 < ((doubled I b).residual g2).capacity a :=
          t.walk.active_of_count_pos a hpos
        have hcap_pos : 0 < (I₂.residual g2).capacity a := by
          revert hpos hact
          refine Fin.addCases (m := I.m) (n := I.m) (fun e hpos hact => ?_) (fun e _ hact => ?_) a
          · have hge : g e ≤ (I.capacity e : ℤ) := by
              apply (Int.cast_le (R := ℝ)).mp
              simpa only [Int.cast_natCast] using (hg.1.2 e).2
            have hbe : b e ≤ 1 := hb e
            have hact' : 0 < (((2 * I.capacity e + b e : ℕ) : ℤ) - 2 * g e).toNat := by
              simpa only [g2, Fin.addCases_left] using hact
            simp only [I₂, doubled, g2, Fin.addCases_left]
            by_cases heq : g e = (I.capacity e : ℤ)
            · have hb1 : b e = 1 := by omega
              have hcnt := hno e heq hb1
              omega
            · omega
          · simpa only [I₂, doubled, g2, Fin.addCases_right] using hact
        have hle1 : t.walk.count a ≤ 1 := hsimple a
        have hle : t.walk.count a ≤ (I₂.residual g2).capacity a := by omega
        dsimp only [f]
        exact_mod_cast hle
  have hcmp := hzero.2 f hf
  have hobj0 : (I₂.residual g2).objective (fun _ => 0) = 0 := by
    simp [Circulation.objective]
  have hobjf : (I₂.residual g2).objective f = (t.walk.cost : ℝ) := by
    have heq : (I₂.residual g2).objective f = ((doubled I b).residual g2).objective f := rfl
    rw [heq]
    exact t.walk.objective_count
  rw [hobj0, hobjf] at hcmp
  have hlt : (t.walk.cost : ℝ) < 0 := by exact_mod_cast hcost
  linarith only [hcmp, hlt]

/-- Bit-scaling proximity (Lemma 1): if `g` is an integral optimum of `I`,
then the doubled instance `doubled I b` (with `b e ≤ 1`) has a real optimum
`h` within `I.m` of `2 * g` on every edge. -/
theorem doubled_exists_proximal_optimal (I : Circulation) (b : Fin I.m → ℕ)
    (hb : ∀ e, b e ≤ 1) (g : Fin I.m → ℤ) (hg : I.Optimal (fun e => (g e : ℝ))) :
    ∃ h : Fin I.m → ℝ, (doubled I b).Optimal h ∧
      ∀ e, |h e - 2 * (g e : ℝ)| ≤ (I.m : ℝ) := by
  classical
  let I' := doubled I b
  let g2 : Fin I.m → ℤ := fun e => 2 * g e
  let R := I'.residual g2
  have hg2_feas : I'.Feasible (fun e => (g2 e : ℝ)) :=
    doubled_feasible_two_mul I b g hg.1
  obtain ⟨h₀, hh₀⟩ := I'.exists_integral_optimum
  let r := I'.differenceLift g2 (fun e => (h₀ e : ℝ))
  have hr_opt : R.Optimal r := I'.differenceLift_optimal g2 hg2_feas _ hh₀
  obtain ⟨terms, _, hterms, hsum⟩ := R.exists_cycle_decomposition r hr_opt.1
  let negTerms := terms.filter (fun t => decide (t.walk.cost < 0))
  have hneg_mem : ∀ t ∈ negTerms, t ∈ terms ∧ t.walk.cost < 0 := by
    intro t ht
    have hmem := List.mem_filter.mp ht
    exact ⟨hmem.1, decide_eq_true_eq.mp hmem.2⟩
  have hterms_nonneg : ∀ t ∈ terms, 0 ≤ t.amount := fun t ht => (hterms t ht).1.le
  have hneg_nonneg : ∀ t ∈ negTerms, 0 ≤ t.amount := fun t ht =>
    hterms_nonneg t (hneg_mem t ht).1
  have hneg_feas : R.Feasible (R.cycleSum negTerms) := by
    refine ⟨R.cycleSum_conserves negTerms, fun a => ⟨R.cycleSum_nonneg negTerms hneg_nonneg a, ?_⟩⟩
    have hle1 : R.cycleSum negTerms a ≤ R.cycleSum terms a :=
      cycleSum_filter_le R terms _ hterms_nonneg a
    rw [hsum] at hle1
    exact le_trans hle1 (hr_opt.1.2 a).2
  have hneg_opt : R.Optimal (R.cycleSum negTerms) := by
    refine ⟨hneg_feas, fun q hq => ?_⟩
    have hobj_le : R.objective (R.cycleSum negTerms) ≤ R.objective r := by
      rw [← hsum, R.cycleSum_objective, R.cycleSum_objective]
      exact sum_filter_neg_cost_le R terms hterms_nonneg
    exact le_trans hobj_le (hr_opt.2 q hq)
  let h' : Fin I.m → ℝ := I'.augment g2 (R.cycleSum negTerms)
  have hh'_opt : I'.Optimal h' := by
    have haug := I'.augment_optimal_with_demands g2 hg2_feas.2 (R.cycleSum negTerms) hneg_opt
    refine ⟨I'.augment_feasible g2 hg2_feas _ hneg_feas, fun q hq => ?_⟩
    exact haug.2.2 q (fun v => (hq.1 v).trans (hg2_feas.1 v).symm) hq.2
  -- Bound the sum of cycle amounts by the number of saturated edges with `b e = 1`.
  let satEdges : Finset (Fin I.m) :=
    Finset.univ.filter (fun e => g e = (I.capacity e : ℤ) ∧ b e = 1)
  let S : Finset (Fin R.m) := satEdges.image (Fin.castAdd I.m)
  have hS_hit : ∀ t ∈ negTerms, 0 ≤ t.amount ∧ ∃ a ∈ S, 0 < t.walk.count a := by
    intro t ht
    obtain ⟨hmem, hcost⟩ := hneg_mem t ht
    obtain ⟨e, hge, hbe, hcnt⟩ := neg_cycle_uses_saturated_slot I b hb g hg t hcost (hterms t hmem).2.2
    refine ⟨(hterms t hmem).1.le, Fin.castAdd I.m e, ?_, hcnt⟩
    exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, hge, hbe⟩, rfl⟩
  have hS_cap : ∀ a ∈ S, (R.capacity a : ℝ) = 1 := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hge, hbe⟩ := (Finset.mem_filter.mp he).2
    have hcap1 : R.capacity (Fin.castAdd I.m e) = 1 := by
      simp only [R, I', doubled, g2, Fin.addCases_left]
      omega
    rw [hcap1, Nat.cast_one]
  have hsum_amounts : (negTerms.map (fun t => t.amount)).sum ≤ (I.m : ℝ) := by
    calc
      (negTerms.map (fun t => t.amount)).sum
          ≤ ∑ a ∈ S, R.cycleSum negTerms a := sum_amounts_le_sum_finset R S negTerms hS_hit
      _ ≤ ∑ a ∈ S, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          have hle := (hneg_feas.2 a).2
          rw [hS_cap a ha] at hle
          exact hle
      _ = (S.card : ℝ) := by simp
      _ ≤ (I.m : ℝ) := by
          have hcard : S.card ≤ I.m := by
            calc
              S.card ≤ satEdges.card := Finset.card_image_le
              _ ≤ (Finset.univ : Finset (Fin I.m)).card := Finset.card_le_card (Finset.subset_univ _)
              _ = I.m := by simp
          exact_mod_cast hcard
  refine ⟨h', hh'_opt, fun e => ?_⟩
  have hneg_simple : ∀ t ∈ negTerms, 0 ≤ t.amount ∧ ∀ a, t.walk.count a ≤ 1 := fun t ht =>
    ⟨(hterms t (hneg_mem t ht).1).1.le, (hterms t (hneg_mem t ht).1).2.2⟩
  have hfwd_le : R.cycleSum negTerms (Fin.castAdd I.m e) ≤ (I.m : ℝ) :=
    le_trans (cycleSum_le_sum_amounts R negTerms hneg_simple (Fin.castAdd I.m e)) hsum_amounts
  have hrev_le : R.cycleSum negTerms (Fin.natAdd I.m e) ≤ (I.m : ℝ) :=
    le_trans (cycleSum_le_sum_amounts R negTerms hneg_simple (Fin.natAdd I.m e)) hsum_amounts
  have hfwd_nonneg : 0 ≤ R.cycleSum negTerms (Fin.castAdd I.m e) :=
    (hneg_feas.2 (Fin.castAdd I.m e)).1
  have hrev_nonneg : 0 ≤ R.cycleSum negTerms (Fin.natAdd I.m e) :=
    (hneg_feas.2 (Fin.natAdd I.m e)).1
  have hdiff : h' e - 2 * (g e : ℝ) =
      R.cycleSum negTerms (Fin.castAdd I.m e) - R.cycleSum negTerms (Fin.natAdd I.m e) := by
    simp only [h', Circulation.augment, Circulation.project, g2, Int.cast_mul, Int.cast_ofNat]
    ring
  rw [hdiff, abs_le]
  constructor <;> linarith only [hfwd_le, hrev_le, hfwd_nonneg, hrev_nonneg]

end MinCostFlow.Narrow
