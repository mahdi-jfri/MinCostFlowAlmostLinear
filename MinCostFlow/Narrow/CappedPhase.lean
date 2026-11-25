module

public import MinCostFlow.Narrow.Defs
import MinCostFlow.Narrow.DoubledProximity
import MinCostFlow.Scaling.ResidualGap
import Mathlib.Tactic.Linarith

/-!
# Capping phase capacities preserves optimality

This file proves Lemma 2 (capping): for any cap `M ≥ I.m`, if `g` is an
integral optimal circulation of `I` and `d` is an optimal circulation of the
capped residual phase instance `phaseInstance I b g M` (with `b e ≤ 1`), then
augmenting `2 * g` by `d` gives an optimal circulation of `doubled I b`.

By Lemma 1 (`doubled_exists_proximal_optimal`), `doubled I b` has a real
optimum `h` within `I.m ≤ M` of `2 * g` on every edge, so its lifted residual
difference is feasible in `phaseInstance I b g M`. Conversely, every feasible
flow of `phaseInstance I b g M` is feasible in the uncapped residual instance
and changes the objective by the same amount.
-/

public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling

/-- Any feasible flow of a capacity-capped instance is feasible in the original
instance. -/
theorem capCapacities_feasible_to_orig (J : Circulation) (M : ℕ) (f : Fin J.m → ℝ)
    (hf : (capCapacities J M).Feasible f) : J.Feasible f := by
  refine ⟨hf.1, fun e => ⟨(hf.2 e).1, ?_⟩⟩
  have hle : ((capCapacities J M).capacity e : ℝ) ≤ (J.capacity e : ℝ) := by
    exact_mod_cast Nat.min_le_left (J.capacity e) M
  exact le_trans (hf.2 e).2 hle

/-- Real cast of `intAugment` agrees with `Circulation.augment`. -/
theorem intAugment_cast (I : Circulation) (f : Fin I.m → ℤ) (d : Fin (I.m + I.m) → ℤ) :
    (fun e => (intAugment I.m f d e : ℝ)) = I.augment f (fun a => (d a : ℝ)) := by
  funext e
  simp only [intAugment, intProject, Circulation.augment, Circulation.project,
    Int.cast_add, Int.cast_sub]

/-- Capping is safe (Lemma 2, real residual flow): for `M ≥ I.m`, augmenting
`2 * g` by any real optimum `d` of `phaseInstance I b g M` yields an optimum of
`doubled I b`. -/
theorem augment_phaseInstance_optimal_real (I : Circulation) (b : Fin I.m → ℕ)
    (hb : ∀ e, b e ≤ 1) (g : Fin I.m → ℤ) (hg : I.Optimal (fun e => (g e : ℝ)))
    (M : ℕ) (hM : I.m ≤ M) (d : Fin (I.m + I.m) → ℝ)
    (hd : (phaseInstance I b g M).Optimal d) :
    (doubled I b).Optimal ((doubled I b).augment (fun e => 2 * g e) d) := by
  let I' := doubled I b
  let g2 : Fin I.m → ℤ := fun e => 2 * g e
  let R := I'.residual g2
  have hg2_feas : I'.Feasible (fun e => (g2 e : ℝ)) :=
    doubled_feasible_two_mul I b g hg.1
  have hd_R : R.Feasible d := capCapacities_feasible_to_orig R M d hd.1
  refine ⟨I'.augment_feasible g2 hg2_feas d hd_R, fun f hf => ?_⟩
  obtain ⟨h, hh_opt, hprox⟩ := doubled_exists_proximal_optimal I b hb g hg
  let q := I'.differenceLift g2 h
  have hq_R : R.Feasible q :=
    I'.differenceLift_feasible g2 h hg2_feas.2 hh_opt.1.2
      (fun v => (hh_opt.1.1 v).trans (hg2_feas.1 v).symm)
  have hM_real : (I.m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hq_P : (phaseInstance I b g M).Feasible q := by
    refine ⟨hq_R.1, fun a => ⟨(hq_R.2 a).1, ?_⟩⟩
    have hq_le_M : q a ≤ (M : ℝ) := by
      refine Fin.addCases (m := I.m) (n := I.m) (fun e => ?_) (fun e => ?_) a
      · have hpe := abs_le.mp (hprox e)
        have h0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        simp only [q, Circulation.differenceLift, I', doubled, g2, Fin.addCases_left, Int.cast_mul,
          Int.cast_ofNat]
        exact max_le (by linarith only [hpe.2, hM_real]) h0
      · have hpe := abs_le.mp (hprox e)
        have h0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        simp only [q, Circulation.differenceLift, I', doubled, g2, Fin.addCases_right, Int.cast_mul,
          Int.cast_ofNat]
        exact max_le (by linarith only [hpe.1, hM_real]) h0
    have hq_le_cap : q a ≤ (R.capacity a : ℝ) := (hq_R.2 a).2
    have hcap_min : ((phaseInstance I b g M).capacity a : ℝ) =
        min (R.capacity a : ℝ) (M : ℝ) := by
      change ((min (R.capacity a) M : ℕ) : ℝ) = min (R.capacity a : ℝ) (M : ℝ)
      exact Nat.cast_min (R.capacity a) M
    rw [hcap_min]
    exact le_min hq_le_cap hq_le_M
  have hd_le_q : R.objective d ≤ R.objective q := hd.2 q hq_P
  have hobj_aug : I'.objective (I'.augment g2 d) =
      I'.objective (fun e => (g2 e : ℝ)) + R.objective d :=
    I'.augment_objective g2 d
  have hobj_q : R.objective q = I'.objective h - I'.objective (fun e => (g2 e : ℝ)) :=
    I'.differenceLift_objective g2 h
  have hh_le_f : I'.objective h ≤ I'.objective f := hh_opt.2 f hf
  linarith only [hd_le_q, hobj_aug, hobj_q, hh_le_f]

/-- Capping is safe (Lemma 2, integral residual flow): for `M ≥ I.m`, if `d` is
an integral optimum of `phaseInstance I b g M`, then `intAugment` of `2 * g` by
`d` is an integral optimum of `doubled I b`. -/
theorem augment_phaseInstance_optimal (I : Circulation) (b : Fin I.m → ℕ)
    (hb : ∀ e, b e ≤ 1) (g : Fin I.m → ℤ) (hg : I.Optimal (fun e => (g e : ℝ)))
    (M : ℕ) (hM : I.m ≤ M) (d : Fin (I.m + I.m) → ℤ)
    (hd : (phaseInstance I b g M).Optimal (fun a => (d a : ℝ))) :
    (doubled I b).Optimal (fun e => (intAugment I.m (fun k => 2 * g k) d e : ℝ)) := by
  rw [intAugment_cast (doubled I b)]
  exact augment_phaseInstance_optimal_real I b hb g hg M hM (fun a => (d a : ℝ)) hd

end MinCostFlow.Narrow
