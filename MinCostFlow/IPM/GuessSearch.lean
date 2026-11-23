module

public import MinCostFlow.IPM.GuessTest
public import Mathlib.Data.Nat.Log
import MinCostFlow.IPM.GuessInitial
import MinCostFlow.IPM.GuessBounds
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

/-!
# Binary search for the unknown target cost

Section 4 of Chen et al., arXiv:2203.00671v2 (page 24), proposes binary
search without a proof. The bounded IPM test supplies the comparison.
Search an inclusive integer interval, halving its span after each test.
An interval of span less than `2^q` is resolved with at most `q` tests.
One last IPM run at the resulting optimal integer target returns a flow
within `(mU)^(-10)` of optimal. Thus the number of IPM runs is at most
`clog 2 (2B+1) + 1`, for the integer cost bound `B = mU²`.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- The target returned by bisection, together with the list of tested
integer guesses. The span is the difference of the inclusive endpoints. -/
@[expose] def bisectCost (test : ℤ → Bool) (lo : ℤ) (span : ℕ) : ℕ → ℤ × List ℤ
  | 0 => (lo, [])
  | q+1 =>
    if span = 0 then (lo, []) else
      let mid := lo+(span/2 : ℕ)
      let result := if test mid then bisectCost test lo (span/2) q
        else bisectCost test (mid+1) (span-span/2-1) q
      (result.1, mid::result.2)

/-- Bisection returns the unique threshold in an inclusive integer interval
in at most `q` tests when its span is less than `2^q`. The comparison
hypothesis is local to this interval. -/
theorem bisectCost_correct (test : ℤ → Bool) (z lo : ℤ) (span q : ℕ)
    (hlo : lo ≤ z) (hhi : z ≤ lo+span) (hspan : span < 2^q)
    (htest : ∀ F, lo ≤ F → F ≤ lo+span → (test F = true ↔ z ≤ F)) :
    (bisectCost test lo span q).1 = z ∧ (bisectCost test lo span q).2.length ≤ q := by
  induction q generalizing lo span with
  | zero =>
    have hz : span = 0 := by simpa only [pow_zero] using Nat.eq_zero_of_le_zero (by omega : span ≤ 0)
    have heq : lo = z := by omega
    simp only [bisectCost, heq, List.length_nil, le_refl, and_self]
  | succ q ih =>
    by_cases hz : span = 0
    · have heq : lo = z := by omega
      simp only [bisectCost, hz, ↓reduceIte, heq, List.length_nil, Nat.zero_le, and_self]
    · have hhalf : span/2 < 2^q := by
        rw [pow_succ] at hspan
        omega
      have hrest : span-span/2-1 < 2^q := by omega
      have hmidlo : lo ≤ lo+(span/2 : ℕ) := by omega
      have hmidhi : lo+(span/2 : ℕ) ≤ lo+span := by omega
      cases hm : test (lo+(span/2 : ℕ)) with
      | true =>
        have hleft := (htest _ hmidlo hmidhi).mp hm
        have hh := ih lo (span/2) hlo hleft hhalf (by
          intro F hFl hFh
          exact htest F hFl (by omega))
        simp only [bisectCost, hz, ↓reduceIte, hm, List.length_cons]
        exact ⟨hh.1, Nat.succ_le_succ hh.2⟩
      | false =>
        have hright : lo+(span/2 : ℕ)+1 ≤ z := by
          have hn : ¬ z ≤ lo+(span/2 : ℕ) := by
            intro hh
            have ht := (htest _ hmidlo hmidhi).mpr hh
            rw [hm] at ht
            contradiction
          omega
        have hh := ih (lo+(span/2 : ℕ)+1) (span-span/2-1) hright (by omega)
          hrest (by
            intro F hFl hFh
            exact htest F (by omega) (by omega))
        simp only [bisectCost, hz, ↓reduceIte, hm, Bool.false_eq_true, List.length_cons]
        exact ⟨hh.1, Nat.succ_le_succ hh.2⟩

/-- The real residual tolerance is at most one half in the nondegenerate
IPM range. This turns the final target run into the required additive
half-unit solution. -/
theorem guess_tolerance_le_half (I : Instance) (U : ℝ) (hsize : 2 ≤ (I.m : ℝ)*U) :
    Real.rpow (I.m*U) (-10) ≤ (1/2 : ℝ) := by
  have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2) hsize
    (by norm_num : (-10 : ℝ) ≤ 0)
  have hh : Real.rpow (2 : ℝ) (-10) ≤ (1/2 : ℝ) := by norm_num
  exact h.trans hh

/-- Bisection uses at most `clog 2 (2B+1)` target tests. One final target
run is included in the reported upper bound on the number of IPM runs. -/
@[expose] def searchCost (I : Instance) (U κ : ℝ) (step : StepSelector I U κ)
    (f₀ : Fin I.m → ℝ) (B : ℕ) : Option (Fin I.m → ℝ) × ℕ :=
  let result := bisectCost (fun F => (guessTest I U F κ step f₀).isSome)
    (-(B : ℤ)) (2*B) (Nat.clog 2 (2*B+1))
  (guessTest I U result.1 κ step f₀, result.2.length+1)

/-- Binary search for the optimal integer cost, using the proved IPM
comparison test. All initial-potential hypotheses concern the actual
initial flow, and follow from half-unit slacks via `guess_initial_potential`.
The returned flow is feasible and has cost within one half of optimal. -/
theorem searchCost_correct (I : Instance) (U κ : ℝ) (step : StepSelector I U κ)
    (hstep : SelectsPermittedSteps step) (f₀ fstar : Fin I.m → ℝ) (z : ℤ) (B : ℕ)
    (hm : 0 < I.m) (hU : 0 < U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f₀) (hroute : I.Routes f₀)
    (hs : I.IsMinCostFlow fstar) (hz : I.cost fstar = z)
    (hzlo : -(B : ℤ) ≤ z) (hzhi : z ≤ B)
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hinit : ∀ F : ℤ, -(B : ℤ) ≤ F → F ≤ B → 0 < residual I F f₀ →
      potential I (alpha I U) F f₀ ≤ 200*I.m*Real.log (I.m*U)) :
    ∃ g, (searchCost I U κ step f₀ B).1 = some g ∧ I.IsFeasible g ∧
      I.cost g ≤ I.cost fstar+1/2 ∧
      (searchCost I U κ step f₀ B).2 ≤ Nat.clog 2 (2*B+1)+1 := by
  classical
  let test : ℤ → Bool := fun F => (guessTest I U F κ step f₀).isSome
  have htest : ∀ F : ℤ, -(B : ℤ) ≤ F → F ≤ B → (test F = true ↔ z ≤ F) := by
    intro F hFl hFh
    constructor
    · intro hh
      obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hh
      exact guessTest_integer_sound I U κ F z step f₀ fstar g hm hU.le hsize hnums
        hf hroute hs hz hκ hκa (hinit F hFl hFh) hg
    · intro hh
      apply guessTest_complete I U F κ step hstep f₀ fstar hm hU hsize hnums hf hroute
        hs.1 _ hκ hκa (hinit F hFl hFh)
      rw [hz]
      exact_mod_cast hh
  have hspan : 2*B < 2^(Nat.clog 2 (2*B+1)) := by
    have hh := Nat.le_pow_clog (by decide : 1 < 2) (2*B+1)
    omega
  have hb := bisectCost_correct test z (-(B : ℤ)) (2*B) (Nat.clog 2 (2*B+1))
    hzlo (by omega) hspan (by intro F hFl hFh; exact htest F hFl (by omega))
  have hsome := (htest z hzlo hzhi).mpr le_rfl
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hsome
  have hsound := guessTest_sound I U z κ step f₀ g hm hU.le hsize hnums hf hroute
    hκ hκa (hinit z hzlo hzhi) hg
  refine ⟨g, ?_, hsound.1, ?_, ?_⟩
  · change guessTest I U (bisectCost test (-(B : ℤ)) (2*B) (Nat.clog 2 (2*B+1))).1 κ step f₀ = _
    rw [hb.1]
    exact hg
  · rw [hz]
    exact hsound.2.trans (add_le_add_right (guess_tolerance_le_half I U hsize) (z : ℝ))
  · exact Nat.succ_le_succ hb.2

/-- The full target search from a half-unit-slack initial flow. Neither the
optimal flow nor its value is an input. The integer interval and every
initial potential bound are proved from the numeric bound. -/
theorem halfSlack_search_correct (I : Instance) (U : ℕ) (κ : ℝ)
    (step : StepSelector I (U : ℝ) κ) (hstep : SelectsPermittedSteps step)
    (f₀ : Fin I.m → ℝ) (hI : I.IsValid) (hm : 0 < I.m) (hU : 2 ≤ U)
    (hnums : NumbersBounded I (U : ℝ)) (hf : I.IsFeasible f₀)
    (hslack : ∀ e, (1/2 : ℝ) ≤ f₀ e-(I.edge e).lower ∧
      (1/2 : ℝ) ≤ (I.edge e).upper-f₀ e)
    (hκ : 0 < κ) (hκa : κ ≤ alpha I (U : ℝ)/4) :
    ∃ g, (searchCost I (U : ℝ) κ step f₀ (I.m*U^2)).1 = some g ∧
      I.IsFeasible g ∧ (∀ fstar, I.IsMinCostFlow fstar → I.cost g ≤ I.cost fstar+1/2) ∧
      (searchCost I (U : ℝ) κ step f₀ (I.m*U^2)).2 ≤
        Nat.clog 2 (2*(I.m*U^2)+1)+1 := by
  have hUR : (2 : ℝ) ≤ U := by exact_mod_cast hU
  have hmR : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hsize : (2 : ℝ) ≤ I.m*(U : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hmR (le_trans (by norm_num) hUR)
    nlinarith only [hh, hUR]
  have hstrict : StrictlyInside I f₀ := by
    intro e
    constructor <;> linarith only [(hslack e).1, (hslack e).2]
  obtain ⟨fstar, hs, hint⟩ := exists_integral_minCostFlow I hI ⟨f₀, hf⟩
  obtain ⟨z, hz⟩ := integral_cost I fstar hint
  have hbound := feasible_cost_abs_le I (U : ℝ) (Nat.cast_nonneg _) hnums fstar hs.1
  rw [hz] at hbound
  have hzlo : -((I.m*U^2 : ℕ) : ℤ) ≤ z := by
    exact_mod_cast (abs_le.mp hbound).1
  have hzhi : z ≤ ((I.m*U^2 : ℕ) : ℤ) := by
    exact_mod_cast (abs_le.mp hbound).2
  have hinit : ∀ F : ℤ, -((I.m*U^2 : ℕ) : ℤ) ≤ F → F ≤ ((I.m*U^2 : ℕ) : ℤ) →
      0 < residual I F f₀ →
      potential I (alpha I (U : ℝ)) F f₀ ≤ 200*I.m*Real.log (I.m*(U : ℝ)) := by
    intro F hFl _ hr
    apply guess_initial_potential I (U : ℝ) F f₀ hm
      (le_trans (by norm_num) hUR) hsize hnums hf hslack _ hr
    exact_mod_cast hFl
  obtain ⟨g, hg, hgfeas, hgcost, hcount⟩ := searchCost_correct I (U : ℝ) κ step hstep
    f₀ fstar z (I.m*U^2) hm (lt_of_lt_of_le (by norm_num) hUR) hsize hnums
    hstrict hf.1 hs hz hzlo hzhi hκ hκa hinit
  refine ⟨g, hg, hgfeas, ?_, hcount⟩
  intro f' hf'
  exact hgcost.trans (add_le_add_left (hs.2 f' hf'.1) (1/2 : ℝ))

end MinCostFlow.IPM
