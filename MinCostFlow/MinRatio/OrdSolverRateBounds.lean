module

public import MinCostFlow.MinRatio.DetectTreePhaseBase
public import MinCostFlow.LinkCut.PathProg.Account
public import MinCostFlow.Chain.Theorem5_1Asymptotics
import MinCostFlow.Final.TimeFactorBounds
import Mathlib.Tactic

/-!
# Rate and space bounds of the min-ratio solver

The solver of Algorithms 1 and 2 must run at a rate `rate m` that is `m^{o(1)}`, and its four
operations must use space polynomial in the input size (the fields `cycleRate_subpoly` and
`cycleSpace_poly` of `Final.DyadicWithVConcretePrograms`). This file gives such a rate and such
an allocation, built from bounds on the inner budgets, and proves the bounds.

* `OrdSolverRateAllocFixed` collects the inequalities that the Init, Query and Detect clauses of
  `OrdSolverContractEnvelope` ask of `rate` and `alloc`, for the budgets of those operations.
* `OrdSolverInnerBounds` holds bounds, as functions of the edge count `m`, on the number of limbs,
  the number of vertices and the budgets of the inner procedures. Their concrete values come
  from the programs of the inner procedures.
* `OrdSolverInnerBounds.cycleRate` and `OrdSolverInnerBounds.cycleAllocation` are the rate and
  the allocation. `ordSolverRateAllocFixed_of_le` shows that they meet
  `OrdSolverRateAllocFixed` whenever the actual sizes are below the bounds.
* `OrdSolverInnerBounds.cycleRate_subpoly` shows that the rate is at most
  `C · alg2TimeFactor E (47 / 48) m` when each bound is, and
  `OrdSolverInnerBounds.cycleSpace_poly` shows that the space is polynomial when each space bound
  is.

The subpolynomial bounds are closed under sums and products (`SubpolyNat.add`, `SubpolyNat.mul`),
because `alg2TimeFactor e₁ a m * alg2TimeFactor e₂ a m = alg2TimeFactor (e₁ + e₂) a m`. This is
all the rate proof uses. The polynomial bounds are closed in the same way.
-/

public section

namespace MinCostFlow.MinRatio

open Chain

/-! ## The fixed part of the envelope -/

/-- The inequalities that the Init, Query and Detect clauses of `OrdSolverContractEnvelope` ask
of the rate and the allocation, for limb count `L`, vertex count `n`, edge count `m`, and the
space and budget of Init. The Detect clause follows from the last conjunct by
`detect_cost_of_step`. -/
@[expose] def OrdSolverRateAllocFixed (L n m initSpace initBudget : ℕ)
    (rate : ℕ → ℕ) (alloc : ℕ → List ℕ → ℕ) : Prop :=
  (∀ args, initSpace ≤ alloc 3 args) ∧ initBudget ≤ rate m * (m + 1) ∧
  (∀ args, max (L + 20 * LinkCut.PathProg.treeLimbs L + 100) (2 + 5 * L) + L ≤ alloc 1 args) ∧
  pathTreeBudget LinkCut.PathProg.pathC L n + 53 * L + 160 ≤ rate m ∧
  detectTreeStepBudget L n + 202 ≤ rate m

/-- The Detect cost clause of `OrdSolverContractEnvelope` for `c` reported edges follows from a
rate that covers one step of the tree phase. -/
theorem detect_cost_of_step {L n r : ℕ} (h : detectTreeStepBudget L n + 202 ≤ r) (c : ℕ) :
    (c + 1) * (detectTreeStepBudget L n + 2) + 200 ≤ r * (1 + c) := by
  have h1 : (c + 1) * (detectTreeStepBudget L n + 2) + 200 ≤
      (c + 1) * (detectTreeStepBudget L n + 202) := by nlinarith
  have h2 : (c + 1) * (detectTreeStepBudget L n + 202) ≤ (c + 1) * r :=
    Nat.mul_le_mul_left _ h
  calc (c + 1) * (detectTreeStepBudget L n + 2) + 200 ≤ (c + 1) * r := h1.trans h2
    _ = r * (1 + c) := by ring

/-- The Query space clause of `OrdSolverContractEnvelope` is the third conjunct of
`OrdSolverRateAllocFixed`, since the path-tree allocation of an operation other than Init is
`20 * treeLimbs L + 100`. -/
theorem query_space_of_fixed {L n m initSpace initBudget : ℕ} {rate : ℕ → ℕ}
    {alloc : ℕ → List ℕ → ℕ} (h : OrdSolverRateAllocFixed L n m initSpace initBudget rate alloc)
    (nTree : ℕ) (xs args : List ℕ) :
    max (L + LinkCut.PathProg.pathAlloc L 4 nTree xs) (2 + 5 * L) + L ≤ alloc 1 args := by
  have hA : LinkCut.PathProg.pathAlloc L 4 nTree xs = 20 * LinkCut.PathProg.treeLimbs L + 100 := by
    simp [LinkCut.PathProg.pathAlloc]
  rw [hA]
  have := h.2.2.1 args
  omega

/-! ## Subpolynomial and polynomial bounds -/

/-- A function of the edge count is at most `c · alg2TimeFactor e (47 / 48) M` for all `M`, the
form of `cycleRate_subpoly` in `Final.DyadicWithVConcretePrograms`. -/
@[expose] def SubpolyNat (f : ℕ → ℕ) : Prop :=
  ∃ c e : ℝ, 0 ≤ e ∧ ∀ M, (f M : ℝ) ≤ c * alg2TimeFactor e (47 / 48) M

/-- A function of the edge count is at most `a · (M + 2) ^ q` for all `M`. -/
@[expose] def PolyNat (f : ℕ → ℕ) : Prop :=
  ∃ a q : ℕ, ∀ M, f M ≤ a * (M + 2) ^ q

namespace SubpolyNat

private theorem coeff_nonneg {f : ℕ → ℕ} {c e : ℝ}
    (h : ∀ M, (f M : ℝ) ≤ c * alg2TimeFactor e (47 / 48) M) : 0 ≤ c := by
  by_contra hc
  have hneg : c * alg2TimeFactor e (47 / 48) 0 < 0 :=
    mul_neg_of_neg_of_pos (lt_of_not_ge hc) (alg2TimeFactor_pos _ _ _)
  linarith [h 0, (Nat.cast_nonneg (f 0) : (0 : ℝ) ≤ f 0)]

theorem const (a : ℕ) : SubpolyNat (fun _ => a) :=
  ⟨a, 0, le_rfl, fun M => by
    simpa using mul_le_mul_of_nonneg_left (Final.scalingTimeFactor_one_le le_rfl M)
      (Nat.cast_nonneg a)⟩

theorem mono {f g : ℕ → ℕ} (hfg : ∀ M, f M ≤ g M) (hg : SubpolyNat g) : SubpolyNat f := by
  obtain ⟨c, e, he, hc⟩ := hg
  exact ⟨c, e, he, fun M => (Nat.cast_le.mpr (hfg M)).trans (hc M)⟩

theorem add {f g : ℕ → ℕ} (hf : SubpolyNat f) (hg : SubpolyNat g) :
    SubpolyNat (fun M => f M + g M) := by
  obtain ⟨c₁, e₁, he₁, h₁⟩ := hf
  obtain ⟨c₂, e₂, he₂, h₂⟩ := hg
  have hc₁ := coeff_nonneg h₁
  have hc₂ := coeff_nonneg h₂
  refine ⟨c₁ + c₂, max e₁ e₂, le_max_of_le_left he₁, fun M => ?_⟩
  have t₁ := mul_le_mul_of_nonneg_left
    (Final.scalingTimeFactor_mono (le_max_left e₁ e₂) M) hc₁
  have t₂ := mul_le_mul_of_nonneg_left
    (Final.scalingTimeFactor_mono (le_max_right e₁ e₂) M) hc₂
  push_cast
  linarith [h₁ M, h₂ M]

theorem mul {f g : ℕ → ℕ} (hf : SubpolyNat f) (hg : SubpolyNat g) :
    SubpolyNat (fun M => f M * g M) := by
  obtain ⟨c₁, e₁, he₁, h₁⟩ := hf
  obtain ⟨c₂, e₂, he₂, h₂⟩ := hg
  have hc₂ := coeff_nonneg h₂
  refine ⟨c₁ * c₂, e₁ + e₂, add_nonneg he₁ he₂, fun M => ?_⟩
  have hprod : alg2TimeFactor e₁ (47 / 48) M * alg2TimeFactor e₂ (47 / 48) M =
      alg2TimeFactor (e₁ + e₂) (47 / 48) M := by
    rw [Final.scalingTimeFactor_eq, Final.scalingTimeFactor_eq, Final.scalingTimeFactor_eq,
      ← Real.exp_add, add_mul]
  have hmul := mul_le_mul (h₁ M) (h₂ M) (Nat.cast_nonneg _)
    (le_trans (Nat.cast_nonneg _) (h₁ M))
  push_cast
  calc (f M : ℝ) * g M ≤ c₁ * alg2TimeFactor e₁ (47 / 48) M * (c₂ * alg2TimeFactor e₂ (47 / 48) M) :=
        hmul
    _ = c₁ * c₂ * (alg2TimeFactor e₁ (47 / 48) M * alg2TimeFactor e₂ (47 / 48) M) := by ring
    _ = c₁ * c₂ * alg2TimeFactor (e₁ + e₂) (47 / 48) M := by rw [hprod]

theorem add_const {f : ℕ → ℕ} (hf : SubpolyNat f) (a : ℕ) : SubpolyNat (fun M => f M + a) :=
  hf.add (const a)

theorem const_mul {f : ℕ → ℕ} (hf : SubpolyNat f) (a : ℕ) : SubpolyNat (fun M => a * f M) :=
  (const a).mul hf

end SubpolyNat

namespace PolyNat

private theorem pow_le_pow_max_left (M q₁ q₂ : ℕ) : (M + 2) ^ q₁ ≤ (M + 2) ^ max q₁ q₂ :=
  Nat.pow_le_pow_right (by omega) (le_max_left _ _)

private theorem pow_le_pow_max_right (M q₁ q₂ : ℕ) : (M + 2) ^ q₂ ≤ (M + 2) ^ max q₁ q₂ :=
  Nat.pow_le_pow_right (by omega) (le_max_right _ _)

theorem const (a : ℕ) : PolyNat (fun _ => a) := ⟨a, 0, fun M => by simp⟩

theorem mono {f g : ℕ → ℕ} (hfg : ∀ M, f M ≤ g M) (hg : PolyNat g) : PolyNat f := by
  obtain ⟨a, q, h⟩ := hg
  exact ⟨a, q, fun M => (hfg M).trans (h M)⟩

theorem id : PolyNat (fun M => M) := ⟨1, 1, fun M => by simp⟩

theorem add {f g : ℕ → ℕ} (hf : PolyNat f) (hg : PolyNat g) : PolyNat (fun M => f M + g M) := by
  obtain ⟨a₁, q₁, h₁⟩ := hf
  obtain ⟨a₂, q₂, h₂⟩ := hg
  refine ⟨a₁ + a₂, max q₁ q₂, fun M => ?_⟩
  have t₁ := Nat.mul_le_mul_left a₁ (pow_le_pow_max_left M q₁ q₂)
  have t₂ := Nat.mul_le_mul_left a₂ (pow_le_pow_max_right M q₁ q₂)
  have := h₁ M
  have := h₂ M
  show f M + g M ≤ _
  rw [Nat.add_mul]
  omega

theorem mul {f g : ℕ → ℕ} (hf : PolyNat f) (hg : PolyNat g) : PolyNat (fun M => f M * g M) := by
  obtain ⟨a₁, q₁, h₁⟩ := hf
  obtain ⟨a₂, q₂, h₂⟩ := hg
  refine ⟨a₁ * a₂, q₁ + q₂, fun M => ?_⟩
  calc f M * g M ≤ (a₁ * (M + 2) ^ q₁) * (a₂ * (M + 2) ^ q₂) := Nat.mul_le_mul (h₁ M) (h₂ M)
    _ = a₁ * a₂ * (M + 2) ^ (q₁ + q₂) := by ring

/-- A polynomial bound in the edge count `m` is a polynomial bound in `n + m + 2`. -/
theorem le_total {f : ℕ → ℕ} (hf : PolyNat f) :
    ∃ a q : ℕ, ∀ n m, f m ≤ a * (n + m + 2) ^ q := by
  obtain ⟨a, q, h⟩ := hf
  exact ⟨a, q, fun n m => (h m).trans
    (Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) q))⟩

end PolyNat

/-! ## The bounds on the inner budgets, the rate and the allocation -/

/-- Bounds, as functions of the edge count `m`, on the sizes and the inner budgets of the
solver: the number of limbs, the number of vertices, the space and budget of Init, the number of
internal edge names (which bounds the pending off-tree list of Detect), and the space of one
Update. The concrete values come from the programs of the inner procedures. -/
structure OrdSolverInnerBounds where
  /-- Bound on the number of limbs of a fixed-point number. -/
  limbs : ℕ → ℕ
  /-- Bound on the number of vertices. -/
  verts : ℕ → ℕ
  /-- Bound on the heap space of Init. -/
  initSpace : ℕ → ℕ
  /-- Bound on the cost of Init. -/
  initBudget : ℕ → ℕ
  /-- Bound on the number of internal edge names. -/
  names : ℕ → ℕ
  /-- Bound on the heap space of one Update. -/
  updateSpace : ℕ → ℕ
  /-- Bound on the amortized cost of one Update per unit of `1 + |U|`, against the shift and
  forward potentials (`update_fwd_amortized`). -/
  updateRate : ℕ → ℕ

namespace OrdSolverInnerBounds

variable (B : OrdSolverInnerBounds)

/-- The rate of Query for `L` limbs and `n` vertices. -/
@[expose] def queryRate (L n : ℕ) : ℕ :=
  pathTreeBudget LinkCut.PathProg.pathC L n + 53 * L + 160

/-- The rate of one step of the tree phase of Detect for `L` limbs and `n` vertices. -/
@[expose] def detectRate (L n : ℕ) : ℕ :=
  detectTreeStepBudget L n + 202

/-- The rate of the solver at edge count `m`: Update is paid by its amortized rate, Init is
spread over its `m + 1` units, and Query and Detect are paid by their rates. -/
@[expose] def cycleRate (M : ℕ) : ℕ :=
  B.updateRate M + (B.initBudget M / (M + 1) + 1) + queryRate (B.limbs M) (B.verts M) +
    detectRate (B.limbs M) (B.verts M)

/-- The heap space of Query for `L` limbs. -/
@[expose] def querySpace (L : ℕ) : ℕ :=
  max (L + 20 * LinkCut.PathProg.treeLimbs L + 100) (2 + 5 * L) + L

/-- The heap space of Detect for `m` edges, `L` limbs and at most `names` pending entries. -/
@[expose] def detectSpace (m L names : ℕ) : ℕ :=
  1 + m + (m + 1) * detectTreeRoundSpace L + names * (2 + 4 * L)

/-- The allocation of operation `j` (`0` Update, `1` Query, `2` Detect, `3` Init). -/
@[expose] def cycleAllocation (_n m : ℕ) (j : ℕ) (_args : List ℕ) : ℕ :=
  match j with
  | 0 => B.updateSpace m
  | 1 => querySpace (B.limbs m)
  | 2 => detectSpace m (B.limbs m) (B.names m)
  | 3 => B.initSpace m
  | _ => 0

/-- The space of the solver: the sum of the allocations of its four operations. -/
@[expose] def cycleSpace (_n m : ℕ) : ℕ :=
  B.updateSpace m + querySpace (B.limbs m) + detectSpace m (B.limbs m) (B.names m) +
    B.initSpace m

theorem cycleAllocation_le_cycleSpace (n m j : ℕ) (hj : j < 4) (args : List ℕ) :
    B.cycleAllocation n m j args ≤ B.cycleSpace n m := by
  interval_cases j <;> simp only [cycleAllocation, cycleSpace] <;> omega

private theorem pathTreeBudget_mono {c L L' n n' : ℕ} (hL : L ≤ L') (hn : n ≤ n') :
    pathTreeBudget c L n ≤ pathTreeBudget c L' n' := by
  unfold pathTreeBudget
  have h1 : (L + 1) ^ 2 ≤ (L' + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : Nat.log 2 (2 * n + 1) ≤ Nat.log 2 (2 * n' + 1) := Nat.log_mono_right (by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)) (by omega)

private theorem detectTreeStepBudget_mono {L L' n n' : ℕ} (hL : L ≤ L') (hn : n ≤ n') :
    detectTreeStepBudget L n ≤ detectTreeStepBudget L' n' := by
  unfold detectTreeStepBudget
  have := pathTreeBudget_mono (c := LinkCut.PathProg.pathC) hL hn
  omega

/-- The rate and the allocation meet `OrdSolverRateAllocFixed` whenever the number of limbs,
the number of vertices and the space and budget of Init are below their bounds. -/
theorem ordSolverRateAllocFixed_of_le {L n nI m initSpace initBudget : ℕ}
    (hL : L ≤ B.limbs m) (hn : n ≤ B.verts m) (hS : initSpace ≤ B.initSpace m)
    (hI : initBudget ≤ B.initBudget m) :
    OrdSolverRateAllocFixed L n m initSpace initBudget B.cycleRate (B.cycleAllocation nI m) := by
  have hQ : queryRate L n ≤ queryRate (B.limbs m) (B.verts m) := by
    unfold queryRate
    have := pathTreeBudget_mono (c := LinkCut.PathProg.pathC) hL hn
    omega
  have hD : detectRate L n ≤ detectRate (B.limbs m) (B.verts m) := by
    unfold detectRate
    have := detectTreeStepBudget_mono hL hn
    omega
  refine ⟨fun _ => hS, ?_, fun _ => ?_, ?_, ?_⟩
  · have hdiv : B.initBudget m < (B.initBudget m / (m + 1) + 1) * (m + 1) := by
      have := Nat.lt_div_mul_add (a := B.initBudget m) (Nat.succ_pos m)
      rw [Nat.add_mul, one_mul]
      exact this
    have hmono : (B.initBudget m / (m + 1) + 1) * (m + 1) ≤ B.cycleRate m * (m + 1) := by
      apply Nat.mul_le_mul_right
      unfold cycleRate
      omega
    omega
  · show _ ≤ querySpace (B.limbs m)
    unfold querySpace LinkCut.PathProg.treeLimbs
    omega
  · exact hQ.trans ((Nat.le_add_left _ _).trans (Nat.le_add_right _ _))
  · exact hD.trans (Nat.le_add_left _ _)

/-- **The Update charge fits the rate.** `update_fwd_amortized` charges one call
`R + B + B · W · |U|`. If `R ≤ r₀ + r₁ |U|`, `B ≤ b` and `W ≤ w`, the charge is at most
`(r₀ + r₁ + b + b w) (1 + |U|)`, so `updateRate := r₀ + r₁ + b + b w` pays for it. -/
theorem update_charge_le_rate {R Bc W u r₀ r₁ b w : ℕ} (hR : R ≤ r₀ + r₁ * u) (hB : Bc ≤ b)
    (hW : W ≤ w) : R + Bc + Bc * W * u ≤ (r₀ + r₁ + b + b * w) * (1 + u) := by
  have h1 : Bc * W * u ≤ b * w * u := Nat.mul_le_mul_right u (Nat.mul_le_mul hB hW)
  have h2 : (r₀ + r₁ + b + b * w) * (1 + u) =
      r₀ + r₁ + b + b * w + (r₀ * u + r₁ * u + b * u + b * w * u) := by ring
  rw [h2]
  omega

/-- The rate `r₀ + r₁ + b + b w` of `update_charge_le_rate` is subpolynomial when its parts
are. -/
theorem updateRate_subpoly {r₀ r₁ b w : ℕ → ℕ} (h₀ : SubpolyNat r₀) (h₁ : SubpolyNat r₁)
    (hb : SubpolyNat b) (hw : SubpolyNat w) :
    SubpolyNat (fun M => r₀ M + r₁ M + b M + b M * w M) :=
  ((h₀.add h₁).add hb).add (hb.mul hw)

/-- The rate is subpolynomial when the bounds on the limbs, on the logarithm of the number of
vertices, on the Init budget per edge, and on the Update rate are. -/
theorem cycleRate_subpoly (hL : SubpolyNat B.limbs)
    (hn : SubpolyNat (fun M => Nat.log 2 (2 * B.verts M + 1)))
    (hI : SubpolyNat (fun M => B.initBudget M / (M + 1)))
    (hU : SubpolyNat B.updateRate) :
    ∃ C E : ℝ, 0 < C ∧ 0 ≤ E ∧
      ∀ M, (B.cycleRate M : ℝ) ≤ C * alg2TimeFactor E (47 / 48) M := by
  have hL1 : SubpolyNat (fun M => (B.limbs M + 1) ^ 2) := by
    have h := (hL.add_const 1).mul (hL.add_const 1)
    exact SubpolyNat.mono (fun M => by rw [sq]) h
  have hP : SubpolyNat (fun M => pathTreeBudget LinkCut.PathProg.pathC (B.limbs M) (B.verts M)) := by
    have h := ((hL1.const_mul LinkCut.PathProg.pathC).const_mul 25).mul (hn.add_const 1)
    exact SubpolyNat.mono (fun M => by unfold pathTreeBudget; exact le_rfl) h
  have hQ : SubpolyNat (fun M => queryRate (B.limbs M) (B.verts M)) :=
    SubpolyNat.mono (fun M => le_of_eq (by unfold queryRate; rfl))
      ((hP.add (hL.const_mul 53)).add_const 160)
  have hD : SubpolyNat (fun M => detectRate (B.limbs M) (B.verts M)) :=
    SubpolyNat.mono (fun M => le_of_eq (by unfold detectRate detectTreeStepBudget; rfl))
      ((((hP.const_mul 3).add (hL.const_mul 87)).add_const 220).add_const 202)
  obtain ⟨c, e, he, h⟩ := SubpolyNat.mono (f := B.cycleRate)
    (fun M => le_of_eq (by unfold cycleRate; rfl))
    (((hU.add (hI.add_const 1)).add hQ).add hD)
  refine ⟨max c 1, e, lt_of_lt_of_le one_pos (le_max_right _ _), he, fun M => ?_⟩
  exact (h M).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (alg2TimeFactor_pos _ _ _).le)

/-- The space is polynomial in `n + m + 2` when the bounds on the limbs, on the names, and on
the spaces of Init and Update are polynomial in `m`. -/
theorem cycleSpace_poly (hL : PolyNat B.limbs) (hN : PolyNat B.names)
    (hS : PolyNat B.initSpace) (hU : PolyNat B.updateSpace) :
    ∃ a q : ℕ, ∀ n m, B.cycleSpace n m ≤ a * (n + m + 2) ^ q := by
  have hQ : PolyNat (fun M => querySpace (B.limbs M)) :=
    PolyNat.mono (fun M => by
      unfold querySpace LinkCut.PathProg.treeLimbs
      show _ ≤ 82 * B.limbs M + 262
      omega) ((hL.mul (PolyNat.const 82)).add (PolyNat.const 262) |>.mono
        (fun M => by rw [Nat.mul_comm]))
  have hR : PolyNat (fun M => detectTreeRoundSpace (B.limbs M)) :=
    PolyNat.mono (fun M => by
      unfold detectTreeRoundSpace LinkCut.PathProg.treeLimbs
      show _ ≤ 244 * B.limbs M + 782
      omega) ((hL.mul (PolyNat.const 244)).add (PolyNat.const 782) |>.mono
        (fun M => by rw [Nat.mul_comm]))
  have hDet : PolyNat (fun M => detectSpace M (B.limbs M) (B.names M)) := by
    have h := (((PolyNat.const 1).add PolyNat.id).add
      ((PolyNat.id.add (PolyNat.const 1)).mul hR)).add
      (hN.mul ((PolyNat.const 2).add ((PolyNat.const 4).mul hL)))
    exact PolyNat.mono (fun M => le_of_eq (by unfold detectSpace; rfl)) h
  obtain ⟨a, q, h⟩ := PolyNat.le_total
    (PolyNat.mono (fun M => le_of_eq (by unfold cycleSpace; rfl))
      (((hU.add hQ).add hDet).add hS) : PolyNat (fun M => B.cycleSpace 0 M))
  exact ⟨a, q, fun n m => h n m⟩

end OrdSolverInnerBounds

end MinCostFlow.MinRatio
