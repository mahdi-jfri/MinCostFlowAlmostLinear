module

public import MinCostFlow.IPM.EpochMemory
import MinCostFlow.IPM.GradientStability
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Feasibility checks for target tests without a hidden witness

A target test may use a guess below the optimum. Definition 4.5 still
promises exact Query and Detect operations and a circulation at each
Update on a valid input history, although it makes no ratio promise
without hidden stability. Checking only the reported coordinates keeps
the stored vector interior. Detect bounds all other coordinate errors,
so the represented flow is also interior. Routing is preserved by the
unconditional circulation guarantee. This supplies a sound acceptance
check even for a wrong target, without assuming a hidden witness.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- Check the newly reported stored coordinates. Only the reported edge
list is inspected. Previously unreported entries retain their values. -/
def epochStoredGuard (I : Instance) {A : MinRatioDataStructure} (s : IpmEpochState I A) : Prop :=
  ∀ e ∈ s.pending, ∃ he : e < I.m,
    ((I.edge ⟨e, he⟩).lower : ℝ) < s.stored ⟨e, he⟩ ∧
      s.stored ⟨e, he⟩ < (I.edge ⟨e, he⟩).upper

/-- Passing every reported-coordinate check keeps all stored coordinates
strictly interior, including when no hidden witness exists. -/
theorem epoch_guards_stored (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n : ℕ) (hbase : StrictlyInside I base)
    (hguard : ∀ j ≤ n, epochStoredGuard I (epochState I U κ r A base j)) :
    ∀ j ≤ n, StrictlyInside I (epochState I U κ r A base j).stored := by
  intro j
  induction j with
  | zero => intro _; exact hbase
  | succ j ih =>
    intro hj e
    by_cases he : (e : ℕ) ∈ (epochState I U κ r A base (j+1)).pending
    · obtain ⟨heI, hbounds⟩ := hguard (j+1) hj e he
      exact hbounds
    · rw [epoch_stored_unchanged I U κ r A base j e he]
      exact ih (by omega) e

/-- The actual Update increment is a circulation on every valid history.
Hidden stability is needed for its quality, not for this routing fact. -/
theorem epoch_increment_circulation (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (T t : ℕ) (hA : MinRatioSpec A κ α Ψ ε)
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (ht : 2*t+1 ≤ T) : IsCirculation I (fun e => epochIncrement I U κ r A base t e) := by
  have hop : epochIsUpdate (2*t+1) = true := by
    unfold epochIsUpdate
    apply decide_eq_true
    omega
  have hh := (hA _ (epochEta I U κ) epochIsUpdate T hvalid).2.1 (2*t) ht hop
  let d := minRatioDirection A (epochInstance I U κ r A base) (epochEta I U κ) epochIsUpdate (2*t)
  have hc : IsCirculation I (fun e => d e) := namedInstance_restrict_circulation I d hh.1
  let c := -(epochEta I U κ (2*t+1)/((epochInstance I U κ r A base).G (2*t+1)).inner
    ((epochInstance I U κ r A base).g (2*t+1)) d)
  have hinc : ∀ e : Fin I.m, epochIncrement I U κ r A base t e = c*d e := by
    intro e
    have he : (e : ℕ) ∈ ((epochInstance I U κ r A base).G (2*t+1)).E := Finset.mem_range.mpr e.2
    simp only [epochIncrement, minRatioIncrement, hop, true_and, he, ↓reduceIte]
    rfl
  intro v
  simp_rw [hinc]
  calc
    _ = c*(∑ e, (I.edge e).b v*d e) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = 0 := by rw [hc v, mul_zero]

/-- Valid operation histories preserve the base flow's routing equations,
even on guesses for which no min-ratio guarantee is available. -/
theorem epoch_routes (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (T n : ℕ) (hA : MinRatioSpec A κ α Ψ ε)
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (hn : 2*n ≤ T) (hroute : I.Routes base) : I.Routes (epochFlow I U κ r A base n) := by
  induction n with
  | zero =>
    intro v
    have hf : epochFlow I U κ r A base 0 = base := by
      funext e
      rw [epoch_query I U κ r α Ψ ε A base T 0 hA hvalid (by omega)]
      change base e+minRatioFlow A _ _ _ 0 e = base e
      rw [minRatioFlow_zero, add_zero]
    rw [hf]
    exact hroute v
  | succ n ih =>
    have hp := ih (by omega)
    have hc := epoch_increment_circulation I U κ r α Ψ ε A base T n hA hvalid (by omega)
    intro v
    simp_rw [epoch_flow_step I U κ r α Ψ ε A base T n hA hvalid hn]
    simp only [mul_add, Finset.sum_add_distrib, hc v, hp v, add_zero]

/-- A completed prefix that passed its reported-coordinate checks has a
feasible represented flow. This is a soundness theorem for arbitrary
guesses; it assumes no hidden stability or cycle-quality bound. -/
theorem epoch_guards_feasible (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n : ℕ) (hI : I.IsValid) (hm : 0 < I.m)
    (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U) (hnums : NumbersBounded I U)
    (he : 0 ≤ ε) (he' : ε ≤ 1/100) (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hA : MinRatioSpec A κ α Ψ ε)
    (hguard : ∀ j ≤ n, epochStoredGuard I (epochState I U κ r A base j)) :
    I.IsFeasible (epochFlow I U κ r A base n) := by
  have hstored := epoch_guards_stored I U κ r A base n hbase hguard
  have hv := epoch_history_valid_prefix I U κ r A base (2*n) hI
    (by intro j hj; exact hstored j (by omega))
  have herr := epoch_stored_error I U κ r α Ψ ε A base (2*n) n hA hv le_rfl he
  have hins := stability_inside I U ε (epochState I U κ r A base n).stored
    (epochFlow I U κ r A base n) hm hU hsize hnums (hstored n le_rfl) he he' herr
  exact feasible_of_inside I _ (epoch_routes I U κ r α Ψ ε A base (2*n) n hA hv le_rfl hroute) hins

/-- Passing the coordinate guards also gives strict interiority, which is
needed when the returned flow is used as the next epoch's base. -/
theorem epoch_guards_inside (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n : ℕ) (hI : I.IsValid) (hm : 0 < I.m)
    (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U) (hnums : NumbersBounded I U)
    (he : 0 ≤ ε) (he' : ε ≤ 1/100) (hbase : StrictlyInside I base)
    (hA : MinRatioSpec A κ α Ψ ε)
    (hguard : ∀ j ≤ n, epochStoredGuard I (epochState I U κ r A base j)) :
    StrictlyInside I (epochFlow I U κ r A base n) := by
  have hstored := epoch_guards_stored I U κ r A base n hbase hguard
  have hv := epoch_history_valid_prefix I U κ r A base (2*n) hI
    (by intro j hj; exact hstored j (by omega))
  exact stability_inside I U ε (epochState I U κ r A base n).stored
    (epochFlow I U κ r A base n) hm hU hsize hnums (hstored n le_rfl) he he'
    (epoch_stored_error I U κ r α Ψ ε A base (2*n) n hA hv le_rfl he)

end MinCostFlow.IPM
