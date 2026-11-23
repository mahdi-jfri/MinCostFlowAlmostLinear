module

public import MinCostFlow.Statement.Problem
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Potential, lengths, and gradients

These are the real-vector objects of Section 4 of Chen et al.,
arXiv:2203.00671v2, equations (8)--(11). The target value is a parameter:
this permits a lower guess as well as the optimal value. Approximation uses
Section 2 (page 5) of arXiv:2309.16629v1.
-/

@[expose] public section
noncomputable section

namespace MinCostFlow.IPM

/-- The source's `U` bounds every demand, capacity, and cost in absolute value
(Section 4, equation (8)). -/
def NumbersBounded (I : Instance) (U : ℝ) : Prop :=
  (∀ v : Fin I.n, |(I.d v : ℝ)| ≤ U) ∧
  ∀ e : Fin I.m, |((I.edge e).lower : ℝ)| ≤ U ∧
    |((I.edge e).upper : ℝ)| ≤ U ∧ |((I.edge e).cost : ℝ)| ≤ U

/-- The source chooses `α = 1/(1000 log mU)` immediately before its potential. -/
def alpha (I : Instance) (U : ℝ) : ℝ := 1 / (1000 * Real.log (I.m * U))

/-- The open capacity box, the domain of the barrier in Section 4. -/
def StrictlyInside (I : Instance) (f : Fin I.m → ℝ) : Prop :=
  ∀ e, ((I.edge e).lower : ℝ) < f e ∧ f e < (I.edge e).upper

/-- The residual cost `cᵀf - F`, with a supplied target value `F`. -/
def residual (I : Instance) (F : ℝ) (f : Fin I.m → ℝ) : ℝ := I.cost f - F

/-- The two power barriers on an edge in equation (9), labelled `eq:karmarkar`. -/
def edgeBarrier (I : Instance) (a : ℝ) (e : Fin I.m) (x : ℝ) : ℝ :=
  Real.rpow ((I.edge e).upper - x) (-a) + Real.rpow (x - (I.edge e).lower) (-a)

/-- Equation (9), labelled `eq:karmarkar`: `20m log(cᵀf-F)` plus the power barriers.
Its analytic domain is `StrictlyInside I f` and `0 < residual I F f`. -/
def potential (I : Instance) (a F : ℝ) (f : Fin I.m → ℝ) : ℝ :=
  20 * I.m * Real.log (residual I F f) + ∑ e, edgeBarrier I a e (f e)

/-- Definition 4.2 (page 24), equation (10): the sum of the two slack powers `-1-α`. -/
def lengths (I : Instance) (a : ℝ) (f : Fin I.m → ℝ) (e : Fin I.m) : ℝ :=
  Real.rpow ((I.edge e).upper - f e) (-1-a) +
    Real.rpow (f e - (I.edge e).lower) (-1-a)

/-- Definition 4.2 (page 24), equation (11): the stated coordinates of `∇Φ(f)`.
The derivative identity is a separate theorem. -/
def gradient (I : Instance) (a F : ℝ) (f : Fin I.m → ℝ) (e : Fin I.m) : ℝ :=
  20 * I.m * (residual I F f)⁻¹ * (I.edge e).cost +
    a * Real.rpow ((I.edge e).upper - f e) (-1-a) -
    a * Real.rpow (f e - (I.edge e).lower) (-1-a)

/-- Multiplication by `L = diag(ℓ)` from Section 4. -/
def diagonal {n : ℕ} (l x : Fin n → ℝ) : Fin n → ℝ := fun e => l e * x e

/-- Multiplication by `L⁻¹`, used to express the gradient tolerance coordinatewise. -/
def inverseDiagonal {n : ℕ} (l x : Fin n → ℝ) : Fin n → ℝ := fun e => x e / l e

/-- The dot product used for gradients and circulations. -/
def dot {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ e, x e * y e

/-- The `ℓ₁` length `‖Lx‖₁`. -/
def weightedLength {n : ℕ} (l x : Fin n → ℝ) : ℝ := ∑ e, |l e * x e|

/-- Section 2 (page 5) of arXiv:2309.16629v1: for positive scalars,
`x ≈_b y` means `b⁻¹ y ≤ x ≤ b y`. -/
def ScalarApprox (b x y : ℝ) : Prop :=
  0 < x ∧ 0 < y ∧ b⁻¹ * y ≤ x ∧ x ≤ b * y

/-- The coordinatewise version of `≈`, with the same factor on every edge. -/
def VectorApprox {n : ℕ} (b : ℝ) (x y : Fin n → ℝ) : Prop :=
  ∀ e, ScalarApprox b (x e) (y e)

/-- The usable coordinate form of `‖L⁻¹(g̃-g)‖∞ ≤ ε` in Lemma 4.4 (page 25). -/
def GradientTolerance {n : ℕ} (l gApprox g : Fin n → ℝ) (ε : ℝ) : Prop :=
  ∀ e, |(gApprox e - g e) / l e| ≤ ε

/-- A circulation satisfies the homogeneous routing equations of Section 4. -/
def IsCirculation (I : Instance) (x : Fin I.m → ℝ) : Prop :=
  ∀ v : Fin I.n, ∑ e, (I.edge e).b v * x e = 0

/-- Lengths in Definition 4.2 (page 24) are positive inside the capacity box. -/
theorem lengths_pos (I : Instance) (a : ℝ) (f : Fin I.m → ℝ)
    (hf : StrictlyInside I f) (e : Fin I.m) : 0 < lengths I a f e := by
  exact add_pos (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).2) _)
    (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).1) _)

/-- A strictly interior flow that routes the demands is feasible for equation (8). -/
theorem feasible_of_inside (I : Instance) (f : Fin I.m → ℝ)
    (hr : I.Routes f) (hf : StrictlyInside I f) : I.IsFeasible f :=
  ⟨hr, fun e => ⟨(hf e).1.le, (hf e).2.le⟩⟩

end MinCostFlow.IPM
