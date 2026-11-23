module

public import MinCostFlow.IPM.Potential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Counting potential reductions

The proof of Theorem 4.3 (page 25) of Chen et al., arXiv:2203.00671v2, sums the
decrease from Lemma 4.4 (page 25). A drop of `κ²/500` per step crosses the gap from
`200m log(mU)` to `-200m log(mU)` after at least
`200000m log(mU)/κ²` steps. This file proves only this counting step:
it does not assert that the required flow updates have been constructed.
-/

public section
namespace MinCostFlow.IPM

/-- Summing a fixed potential drop over a finite prefix. -/
theorem potential_after_steps (p : ℕ → ℝ) (drop : ℝ) (n : ℕ)
    (hstep : ∀ t < n, p (t+1) ≤ p t - drop) :
    p n ≤ p 0 - n*drop := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := ih (fun t ht => hstep t (Nat.lt_succ_of_lt ht))
    have hs := hstep n (Nat.lt_succ_self n)
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only [hp, hs]

/-- The explicit counting step in the proof of Theorem 4.3 (page 25), with constant
`200000` and the corrected inverse-square dependence on `κ`. The
hypothesis recording each potential drop remains visible. -/
theorem iteration_count_bound (I : Instance) (a F U κ : ℝ)
    (f : ℕ → Fin I.m → ℝ) (n : ℕ)
    (hinit : potential I a F (f 0) ≤ 200*I.m*Real.log (I.m*U))
    (hstep : ∀ t < n, potential I a F (f (t+1)) ≤ potential I a F (f t) - κ^2/500)
    (hn : 200000*I.m*Real.log (I.m*U) ≤ n*κ^2) :
    potential I a F (f n) ≤ -200*I.m*Real.log (I.m*U) := by
  have h := potential_after_steps (fun t => potential I a F (f t)) (κ^2/500) n hstep
  linarith only [h, hinit, hn]

/-- Lemma 4.1 (page 24) applied after the explicit number of potential reductions.
The counting argument itself does not need the target to be optimal. -/
theorem residual_after_steps (I : Instance) (a F U κ : ℝ)
    (f : ℕ → Fin I.m → ℝ) (n : ℕ) (hm : 0 < I.m) (hU : 0 < U)
    (hf : StrictlyInside I (f n)) (hr : 0 < residual I F (f n))
    (hinit : potential I a F (f 0) ≤ 200*I.m*Real.log (I.m*U))
    (hstep : ∀ t < n, potential I a F (f (t+1)) ≤ potential I a F (f t) - κ^2/500)
    (hn : 200000*I.m*Real.log (I.m*U) ≤ n*κ^2) :
    residual I F (f n) ≤ Real.rpow (I.m*U) (-10) :=
  lemma_4_1_small I a F U (f n) hm hU hf hr
    (iteration_count_bound I a F U κ f n hinit hstep hn)

/-- The scalar step conditions used in the counting lemma can hold at once. -/
theorem affine_potential_steps (p₀ drop : ℝ) :
    ∃ p : ℕ → ℝ, p 0 = p₀ ∧ ∀ t, p (t+1) = p t - drop := by
  refine ⟨fun t => p₀-t*drop, by simp, ?_⟩
  intro t
  simp only [Nat.cast_add, Nat.cast_one]
  ring

end MinCostFlow.IPM
