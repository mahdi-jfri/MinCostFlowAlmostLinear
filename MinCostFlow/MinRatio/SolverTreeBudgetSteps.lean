module

public import MinCostFlow.MinRatio.SolverTreeBudgetInv
import Mathlib.Tactic

/-!
# The tree budget across the operations (`SolverTreeBudgetSteps`)

`SolverTreeBudgetInv` (`SolverTreeBudgetInv.lean`) holds the tree budget `B₀ + c X`, `c X`
between operations, where `c` is the number of `Update`s so far. This file gives one lemma for
each operation that takes the invariant from its input to its output.
* `Query` keeps the model and the record pointers, and keeps any tree budget.
* `Detect` keeps the counter and the vectors, sets some accumulators to `0`, and keeps the
  record blocks apart.
* `Update` adds one to the counter, and its good branch raises the budget by `X`.

It also gives the model facts these steps need. The accumulators stay nonnegative, and after a
`Detect` each live accumulator is below its threshold (`ordAlg2_detected_accum_lt`). Finally it
gives the fits of the budget at the start of `Update` and `Detect`, and the bound of the budget at
a power of two that the dry run uses (`treeBudget_le_pow`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore.Program

/-! ## 1. Model facts -/

/-- `Update` keeps the accumulators nonnegative: it keeps them, or adds `|inc e|`. -/
theorem ordAlg2_updateWith_detectAccum_nonneg (cfg : Alg2Config) (κ : ℝ) (st : Alg2State cfg)
    (U : List Update) (g l : ℕ → ℝ) (η : ℝ) (h : ∀ e, 0 ≤ st.detectAccum e) (e : ℕ) :
    0 ≤ (Chain.Ordered.algorithm2_updateWith cfg κ st U g l η).1.detectAccum e := by
  dsimp only [Chain.Ordered.algorithm2_updateWith]
  split
  · exact h e
  · exact add_nonneg (h e) (abs_nonneg _)

/-- `Detect` keeps the accumulators nonnegative: it keeps them, or sets them to `0`. -/
theorem algorithm2_detect_detectAccum_nonneg (cfg : Alg2Config) (st : Alg2State cfg)
    (h : ∀ e, 0 ≤ st.detectAccum e) (e : ℕ) :
    0 ≤ (algorithm2_detect cfg st).2.detectAccum e := by
  dsimp only [algorithm2_detect]
  split_ifs
  · exact le_rfl
  · exact h e

/-- After `Detect`, `extℓ e · detectAccum e < ε` on every live edge. A reported edge is reset to
`0`, and `0 < ε`. An edge that is not reported has `¬ (ε ≤ extℓ e · detectAccum e)`. -/
theorem algorithm2_detect_len_mul_accum_lt (cfg : Alg2Config) (st : Alg2State cfg)
    (hε : 0 < cfg.ε) (e : ℕ) (he : e ∈ st.extG.E) :
    (algorithm2_detect cfg st).2.extℓ e * (algorithm2_detect cfg st).2.detectAccum e < cfg.ε := by
  dsimp only [algorithm2_detect]
  split_ifs with hS
  · simpa using hε
  · exact lt_of_not_ge fun h => hS (Finset.mem_filter.mpr ⟨he, h⟩)

/-- The state passed to `Update` has `extℓ e · detectAccum e < ε` on every live edge, since it
is a `Detect` output (`MinRatioDetectedWith.detected`). -/
theorem ordAlg2_detected_accum_lt {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {s : Alg2State cfg} {changed : ℕ → Prop} {g l : ℕ → ℝ}
    (h : MinRatioDetectedWith (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G s changed g l)
    (hε : 0 < cfg.ε) (e : ℕ) (he : e ∈ s.extG.E) : s.extℓ e * s.detectAccum e < cfg.ε := by
  obtain ⟨s₀, hs⟩ := h.detected
  subst hs
  exact algorithm2_detect_len_mul_accum_lt cfg s₀ hε e he

/-! ## 2. The steps -/

/-- **`Query`.** The model is the same. The program keeps the record pointers and any tree
budget. -/
theorem SolverTreeBudgetInv.query_step {cfg : Alg2Config} {L P' m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {root : ℕ} {G : MGraph}
    {P E : ℕ} {X : ℤ} {model : Alg2State cfg} {tok tok' : SolverToken cfg L Rcore}
    {mem mem' : ℕ → ℕ}
    (h : SolverTreeBudgetInv G P E X model tok mem)
    (hrep : (solverStateRep cfg L P' m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hkeep : ∀ B R : ℤ, PathTreeNumericInv tok.tree tok.trees B R →
      PathTreeNumericInv tok'.tree tok'.trees B R)
    (hrec : tok'.edgeRecords = tok.edgeRecords)
    (hptr : ∀ j < tok.intCap, mem' (tok.edgeRecords + j) = mem (tok.edgeRecords + j)) :
    SolverTreeBudgetInv G P E X model tok' mem' := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, hkeep _ _ h.2.2.2.2⟩
  rw [hrec]
  exact h.2.2.2.1.of_agree fun e he => hptr _ (solverStateRep_extToInt_lt hrep he)

/-- **`Detect`.** The counter and the vectors are the same, the accumulators stay
nonnegative, the program keeps the record blocks apart, and it keeps the tree budget. -/
theorem SolverTreeBudgetInv.detect_step {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {G : MGraph}
    {P E : ℕ} {X : ℤ} {model : Alg2State cfg} {tok tok' : SolverToken cfg L Rcore}
    {mem mem' : ℕ → ℕ}
    (h : SolverTreeBudgetInv G P E X model tok mem)
    (hsep : OffTreeRecSep model L mem tok.edgeRecords →
      OffTreeRecSep (algorithm2_detect cfg model).2 L mem' tok'.edgeRecords)
    (hnum : PathTreeNumericInv tok'.tree tok'.trees
      (treeBudgetBase P E + (model.updateCount : ℤ) * X) ((model.updateCount : ℤ) * X)) :
    SolverTreeBudgetInv G P E X (algorithm2_detect cfg model).2 tok' mem' :=
  ⟨h.1, h.2.1, algorithm2_detect_detectAccum_nonneg cfg model h.2.2.1, hsep h.2.2.2.1, hnum⟩

/-- **`Update`.** The counter goes from `c ≤ 2 G.m` to `c + 1`, and the good branch raises the
budget `B₀ + c X`, `c X` by `X`. -/
theorem SolverTreeBudgetInv.update_step {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {G : MGraph}
    {P E : ℕ} {X : ℤ} {model model' : Alg2State cfg} {tok' : SolverToken cfg L Rcore}
    {mem' : ℕ → ℕ}
    (hc : model.updateCount ≤ 2 * G.m) (hc' : model'.updateCount = model.updateCount + 1)
    (hrange : ∀ e ∈ model'.extG.E, |model'.extg e| ≤ (2 : ℝ) ^ E ∧
      (2 : ℝ) ^ (-(E : ℤ)) ≤ model'.extℓ e ∧ model'.extℓ e ≤ (2 : ℝ) ^ E)
    (hacc : ∀ e, 0 ≤ model'.detectAccum e)
    (hsep : OffTreeRecSep model' L mem' tok'.edgeRecords)
    (hnum : PathTreeNumericInv tok'.tree tok'.trees
      ((treeBudgetBase P E + (model.updateCount : ℤ) * X) + X)
      ((model.updateCount : ℤ) * X + X)) :
    SolverTreeBudgetInv G P E X model' tok' mem' := by
  refine ⟨by omega, hrange, hacc, hsep, ?_⟩
  have h1 : treeBudgetBase P E + ((model.updateCount + 1 : ℕ) : ℤ) * X =
      (treeBudgetBase P E + (model.updateCount : ℤ) * X) + X := by push_cast; ring
  have h2 : ((model.updateCount + 1 : ℕ) : ℤ) * X = (model.updateCount : ℤ) * X + X := by
    push_cast; ring
  rw [hc', h1, h2]
  exact hnum

/-! ## 3. The fits -/

/-- The budget at the start of `Update` fits after one raise: `c ≤ 2 G.m` gives
`(c + 1) X ≤ 2 G.m X + X` (`treeBudget_fit`). -/
theorem treeBudget_fit_succ {c Gm n : ℕ} {B₀ X B_bound R_bound cap : ℤ} (hX : 0 ≤ X)
    (hc : c ≤ 2 * Gm) (hB : B₀ + 2 * (Gm : ℤ) * X ≤ B_bound) (hR : 2 * (Gm : ℤ) * X ≤ R_bound)
    (hcap : 2 * ((2 * n + 1 : ℕ) : ℤ) * ((B_bound + X) + (R_bound + X)) < cap) :
    2 * ((2 * n + 1 : ℕ) : ℤ) * (((B₀ + (c : ℤ) * X) + X) + ((c : ℤ) * X + X)) < cap := by
  have h := treeBudget_fit (c := c + 1) hX (by omega) hB hR hcap
  have h1 : (B₀ + ((c + 1 : ℕ) : ℤ) * X) + ((c + 1 : ℕ) : ℤ) * X =
      ((B₀ + (c : ℤ) * X) + X) + ((c : ℤ) * X + X) := by push_cast; ring
  rwa [h1] at h

/-- With `c ≤ 2 G.m`, the budget `B₀ + c X` is at most `B_bound`. -/
theorem treeBudget_le_bound {c Gm : ℕ} {B₀ X B_bound : ℤ} (hX : 0 ≤ X) (hc : c ≤ 2 * Gm)
    (hB : B₀ + 2 * (Gm : ℤ) * X ≤ B_bound) : B₀ + (c : ℤ) * X ≤ B_bound := by
  have hcZ : (c : ℤ) ≤ 2 * (Gm : ℤ) := by exact_mod_cast hc
  nlinarith

/-- With `c ≤ 2 G.m`, the budget `c X` is at most `R_bound`. -/
theorem treeBudget_le_rbound {c Gm : ℕ} {X R_bound : ℤ} (hX : 0 ≤ X) (hc : c ≤ 2 * Gm)
    (hR : 2 * (Gm : ℤ) * X ≤ R_bound) : (c : ℤ) * X ≤ R_bound := by
  have hcZ : (c : ℤ) ≤ 2 * (Gm : ℤ) := by exact_mod_cast hc
  nlinarith

/-- **The budget at a power of two.** The budget between operations is at most `B₀ + 2 m X`,
`2 m X` with `X = maxPaths · 2^(3E + 2 + P)`. With `m < 2^(E + 8)` and `maxPaths < 2^(3E + 20)`,
the raise `2 m X` is at most `2^(P + 7E + 31)`, and `B₀` is smaller. So both parts stay below
`2^(P + 80E)` once `E ≥ 1`. The dry run uses this. -/
theorem treeBudget_le_pow {P E m maxPaths : ℕ} (hE : 1 ≤ E) (hm : Nat.size m ≤ E + 8)
    (hmp : maxPaths < 2 ^ (3 * E + 20)) :
    treeBudgetBase P E + 2 * (m : ℤ) * ((maxPaths : ℤ) * 2 ^ (3 * E + 2 + P)) ≤
        (2 : ℤ) ^ (P + 80 * E) ∧
      2 * (m : ℤ) * ((maxPaths : ℤ) * 2 ^ (3 * E + 2 + P)) ≤ (2 : ℤ) ^ (P + 80 * E) := by
  have hmLt : m < 2 ^ (E + 8) :=
    lt_of_lt_of_le (Nat.lt_size_self m) (Nat.pow_le_pow_right (by norm_num) hm)
  have hprod : 2 * m * (maxPaths * 2 ^ (3 * E + 2 + P)) ≤ 2 ^ (P + 7 * E + 31) := by
    have h1 : 2 * m * (maxPaths * 2 ^ (3 * E + 2 + P)) ≤
        2 * 2 ^ (E + 8) * (2 ^ (3 * E + 20) * 2 ^ (3 * E + 2 + P)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hmLt.le) (Nat.mul_le_mul_right _ hmp.le)
    have h2 : 2 * 2 ^ (E + 8) * (2 ^ (3 * E + 20) * 2 ^ (3 * E + 2 + P)) =
        2 ^ (P + 7 * E + 31) := by
      rw [← pow_succ', ← pow_add, ← pow_add]
      congr 1
      omega
    exact h1.trans_eq h2
  have hB0 : 2 ^ (P + 2 * E + 2) ≤ 2 ^ (P + 7 * E + 31) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum : 2 ^ (P + 7 * E + 31) + 2 ^ (P + 7 * E + 31) ≤ 2 ^ (P + 80 * E) := by
    rw [← two_mul, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold treeBudgetBase
  constructor
  · exact_mod_cast le_trans (Nat.add_le_add hB0 hprod) hsum
  · exact_mod_cast hprod.trans ((Nat.le_add_left _ _).trans hsum)

end MinCostFlow.MinRatio
