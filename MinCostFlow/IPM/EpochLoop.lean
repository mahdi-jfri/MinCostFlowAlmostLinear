module

public import MinCostFlow.IPM.EpochCorrect
public import Mathlib.Algebra.Order.Floor.Semiring
import MinCostFlow.IPM.Potential
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Repeating full epochs until the target is reached

The single-flow adaptation of Algorithm 7 of Chen et al.,
arXiv:2203.00671v2 (Section 9, page 69), fully refreshes after each
`m` updates. At a full refresh it reads all flow coordinates, computes
the residual, and stops when that residual is at most one quarter.
The epoch invariant and potential decrease prove termination for every
upper target guess. The explicit epoch limit cancels the `m` factor
from the per-epoch decrease, leaving the expected number of updates.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- Full-refresh base flows. Each nonterminal epoch executes exactly `m`
Updates and Detects. Once successful, the flow remains fixed. -/
def ipmEpochBase (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure)
    (initial : Fin I.m → ℝ) : ℕ → Fin I.m → ℝ
  | 0 => initial
  | t+1 =>
    let base := ipmEpochBase I U F κ A initial t
    if residual I F base ≤ 1/4 then base
    else epochFlow I U κ (residual I F base) A base I.m

/-- Number of nonterminal epochs actually executed in a prefix. -/
def ipmEpochCount (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure)
    (initial : Fin I.m → ℝ) : ℕ → ℕ
  | 0 => 0
  | t+1 => ipmEpochCount I U F κ A initial t+
      if residual I F (ipmEpochBase I U F κ A initial t) ≤ 1/4 then 0 else 1

/-- Explicit number of full epochs sufficient for an upper target guess.
The effective least step parameter is `κ α/64`. -/
def ipmEpochLimit (I : Instance) (U κ : ℝ) : ℕ :=
  Nat.ceil (200000*Real.log (I.m*U)/(κ*alpha I U/64)^2)

/-- Once an epoch reaches its target, all later base flows remain there. -/
theorem ipmEpochBase_terminal_mono (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure)
    (initial : Fin I.m → ℝ) (s t : ℕ) (hst : s ≤ t)
    (hstop : residual I F (ipmEpochBase I U F κ A initial s) ≤ 1/4) :
    residual I F (ipmEpochBase I U F κ A initial t) ≤ 1/4 := by
  induction t, hst using Nat.le_induction with
  | base => exact hstop
  | succ t hst ih =>
    change residual I F (if residual I F (ipmEpochBase I U F κ A initial t) ≤ 1/4 then _ else _) ≤ _
    rw [ite_eq_left ih]
    exact ih

/-- Repeated causal epochs preserve feasibility, strict capacities,
positive residual, and the potential budget. Each executed epoch pays
its full `m(κ α/64)²/500` decrease. The theorem also holds when the target
is any upper guess, using a feasible comparison flow below that target. -/
theorem ipmEpochBase_invariants (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure)
    (initial fstar : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hi : StrictlyInside I initial) (hroute : I.Routes initial) (hr : 0 < residual I F initial)
    (hpot : potential I (alpha I U) F initial ≤ 200*I.m*Real.log (I.m*U))
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ)) (n : ℕ) :
    I.IsFeasible (ipmEpochBase I U F κ A initial n) ∧
      StrictlyInside I (ipmEpochBase I U F κ A initial n) ∧
      0 < residual I F (ipmEpochBase I U F κ A initial n) ∧
      potential I (alpha I U) F (ipmEpochBase I U F κ A initial n) ≤
        potential I (alpha I U) F initial-
          (ipmEpochCount I U F κ A initial n : ℝ)*I.m*((κ*alpha I U/64)^2/500) := by
  have hm0 : (0 : ℝ) ≤ I.m := Nat.cast_nonneg _
  have hdrop0 : 0 ≤ (I.m : ℝ)*((κ*alpha I U/64)^2/500) :=
    mul_nonneg hm0 (div_nonneg (sq_nonneg _) (by norm_num))
  induction n with
  | zero =>
    refine ⟨feasible_of_inside I initial hroute hi, hi, hr, ?_⟩
    simp only [ipmEpochBase, ipmEpochCount, Nat.cast_zero, zero_mul, sub_zero, le_refl]
  | succ n ih =>
    let base := ipmEpochBase I U F κ A initial n
    have hpast : potential I (alpha I U) F base ≤ 200*I.m*Real.log (I.m*U) := by
      have hpaid := mul_nonneg (Nat.cast_nonneg (ipmEpochCount I U F κ A initial n)) hdrop0
      linarith only [ih.2.2.2, hpot, hpaid]
    by_cases hstop : residual I F (ipmEpochBase I U F κ A initial n) ≤ 1/4
    · simpa only [ipmEpochBase, ipmEpochCount, hstop, ↓reduceIte, Nat.add_zero] using ih
    · have hepoch := epoch_correct I U F κ A base fstar hI hm hU hsize hnums hk hk' hs hF
        ih.2.1 ih.1.1 (lt_of_not_ge hstop) hpast hA
      dsimp only [base] at hepoch
      simp only [ipmEpochBase, ipmEpochCount, hstop, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      refine ⟨hepoch.1, hepoch.2.1, hepoch.2.2.1, ?_⟩
      linarith only [hepoch.2.2.2.1, ih.2.2.2]

/-- For every upper target guess, the full-refresh loop reaches cost at
most `F+1/4` by `ipmEpochLimit` epochs. This is the repeated-epoch form
of the potential-counting argument in Chen et al., Lemma 9.3 (page 71). -/
theorem ipmEpochBase_terminates (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure)
    (initial fstar : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hi : StrictlyInside I initial) (hroute : I.Routes initial) (hr : 0 < residual I F initial)
    (hpot : potential I (alpha I U) F initial ≤ 200*I.m*Real.log (I.m*U))
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ)) :
    I.IsFeasible (ipmEpochBase I U F κ A initial (ipmEpochLimit I U κ)) ∧
      I.cost (ipmEpochBase I U F κ A initial (ipmEpochLimit I U κ)) ≤ F+1/4 := by
  have hinv := ipmEpochBase_invariants I U F κ A initial fstar hI hm hU hsize hnums hk hk'
    hs hF hi hroute hr hpot hA
  let N := ipmEpochLimit I U κ
  have hfinal := hinv N
  refine ⟨hfinal.1, ?_⟩
  have hstop : residual I F (ipmEpochBase I U F κ A initial N) ≤ 1/4 := by
    by_contra hn
    have hbefore : ∀ t ≤ N, ¬ residual I F (ipmEpochBase I U F κ A initial t) ≤ 1/4 := by
      intro t ht hst
      exact hn (ipmEpochBase_terminal_mono I U F κ A initial t N ht hst)
    have hcount : ∀ n ≤ N, ipmEpochCount I U F κ A initial n = n := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hnn
        simp only [ipmEpochCount, hbefore n (by omega), ↓reduceIte, ih (by omega)]
    have hq : 0 < κ*alpha I U/64 := div_pos (mul_pos hk (alpha_pos I U hsize)) (by norm_num)
    have hceil : 200000*Real.log (I.m*U) ≤ (N : ℝ)*(κ*alpha I U/64)^2 :=
      (div_le_iff₀ (sq_pos_of_pos hq)).mp (Nat.le_ceil _)
    have hpaid := mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg I.m : (0 : ℝ) ≤ I.m)
    have hphi : potential I (alpha I U) F (ipmEpochBase I U F κ A initial N) ≤ -200*I.m*Real.log (I.m*U) := by
      have hh := hfinal.2.2.2
      rw [hcount N le_rfl] at hh
      linarith only [hh, hpot, hpaid]
    have hsmall := lemma_4_1_small I (alpha I U) F U _ hm (lt_of_lt_of_le (by norm_num) hU)
      hfinal.2.1 hfinal.2.2.1 hphi
    have hp := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2) hsize
      (by norm_num : (-10 : ℝ) ≤ 0)
    have hquarter : Real.rpow (I.m*U) (-10) ≤ (1/4 : ℝ) := hp.trans (by norm_num)
    exact hn (hsmall.trans hquarter)
  dsimp only [residual] at hstop
  linarith only [hstop]

end MinCostFlow.IPM
