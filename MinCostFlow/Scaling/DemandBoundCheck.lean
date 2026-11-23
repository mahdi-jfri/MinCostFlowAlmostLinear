module

public import MinCostFlow.Scaling.GeneralScalingModel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Rejecting demands that capacities cannot route

Lemma C.1 of Chen et al., arXiv:2203.00671v2, allows arbitrary integral
demands while bounding the absolute lower and upper capacities by `U`.
A feasible flow has absolute value at most `U` on each edge. Its net flow at
any vertex therefore has absolute value at most `m*U`. This gives a single
initial demand scan before the bounded-demand reduction.
-/

@[expose] public section
namespace MinCostFlow.Scaling.FlowReduction

/-- Any feasible flow forces every demand to have absolute value at most `m*U`. -/
theorem demand_natAbs_le_of_feasible (I : Instance) (U : ℕ)
    (hl : ∀ e, (I.edge e).lower.natAbs ≤ U)
    (hu : ∀ e, (I.edge e).upper.natAbs ≤ U)
    (f : Fin I.m → ℝ) (hf : I.IsFeasible f) (v : Fin I.n) :
    (I.d v).natAbs ≤ I.m * U := by
  have hflow (e : Fin I.m) : -(U : ℝ) ≤ f e ∧ f e ≤ U := by
    have hlo : -(U : ℤ) ≤ (I.edge e).lower := by have h := hl e; omega
    have hup : (I.edge e).upper ≤ (U : ℤ) := by have h := hu e; omega
    have hlo' : -(U : ℝ) ≤ ((I.edge e).lower : ℝ) := by exact_mod_cast hlo
    have hup' : ((I.edge e).upper : ℝ) ≤ U := by exact_mod_cast hup
    exact ⟨le_trans hlo' (hf.2 e).1, le_trans (hf.2 e).2 hup'⟩
  have hterm (e : Fin I.m) :
      -(U : ℝ) ≤ (I.edge e).b v * f e ∧ (I.edge e).b v * f e ≤ U := by
    have hh := hflow e
    have hnon : (0 : ℝ) ≤ U := Nat.cast_nonneg _
    unfold Edge.b
    split <;> split <;> simp only [sub_self, zero_mul, sub_zero, one_mul,
      zero_sub, neg_mul] <;> constructor <;> linarith only [hh.1, hh.2, hnon]
  have hlo := Finset.sum_le_sum (s := Finset.univ) (fun e _ => (hterm e).1)
  have hup := Finset.sum_le_sum (s := Finset.univ) (fun e _ => (hterm e).2)
  have hr := hf.1 v
  rw [hr] at hlo hup
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_neg] at hlo hup
  have hli : -((I.m * U : ℕ) : ℤ) ≤ I.d v := by exact_mod_cast hlo
  have hui : I.d v ≤ ((I.m * U : ℕ) : ℤ) := by exact_mod_cast hup
  omega

/-- One Boolean scan of the input demand table. -/
def demandBoundCheck (I : Instance) (U : ℕ) : Bool :=
  (List.finRange I.n).all (fun v => (I.d v).natAbs ≤ I.m * U)

/-- The Boolean scan tests precisely the pointwise demand bound. -/
theorem demandBoundCheck_iff (I : Instance) (U : ℕ) :
    demandBoundCheck I U = true ↔ ∀ v : Fin I.n, (I.d v).natAbs ≤ I.m * U := by
  simp only [demandBoundCheck, List.all_eq_true, decide_eq_true_eq]
  simp only [List.mem_finRange, forall_const]

/-- Rejection certifies infeasibility under only the input capacity bounds. -/
theorem infeasible_of_demandBoundCheck (I : Instance) (U : ℕ)
    (hl : ∀ e, (I.edge e).lower.natAbs ≤ U)
    (hu : ∀ e, (I.edge e).upper.natAbs ≤ U)
    (hcheck : demandBoundCheck I U = false) : ∀ f, ¬ I.IsFeasible f := by
  intro f hf
  have ht := (demandBoundCheck_iff I U).mpr (demand_natAbs_le_of_feasible I U hl hu f hf)
  rw [hcheck] at ht
  cases ht

/-- The source's arbitrary-demand wrapper. The one initial scan costs `3*n`
integer/table operations; on success the internal bound is `(m+1)*U`. -/
def arbitraryDemandScalingModel (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C U : ℕ) : CallResult (Option (Fin I.m → ℤ)) :=
  if demandBoundCheck I U then
    let r := generalScalingModel solve I hv C ((I.m + 1) * U)
    ⟨r.value, r.calls, r.work + 3 * I.n⟩
  else ⟨none, [], 3 * I.n⟩

/-- The preliminary demand scan adds no primitive calls. -/
theorem arbitraryDemandScalingModel_edges (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Instance) (hv : I.IsValid) (C U : ℕ) :
    ∀ J ∈ (arbitraryDemandScalingModel solve I hv C U).calls, J.m ≤ 72 * I.m := by
  unfold arbitraryDemandScalingModel
  split
  · exact generalScalingModel_edges solve I hv C ((I.m + 1) * U)
  · simp

end MinCostFlow.Scaling.FlowReduction
