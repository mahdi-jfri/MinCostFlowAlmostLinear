module

public import MinCostFlow.Scaling.IntegralOptimality
public import Mathlib.Data.List.Pi
import Mathlib.Tactic.NormNum

/-!
# A finite integer exact solver

The solver hypotheses in Appendix C of Chen et al., arXiv:2203.00671v2,
can hold simultaneously. This slow function enumerates every capacity-bounded
integer table with a product of finite lists. It scans them once, retaining
the least-cost table satisfying integer conservation. The scan starts at zero.
All decisions use integers. The integral-minimum theorem proves correctness
against real competitors, without assuming another solver.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Compute conservation using only integer incidence coefficients. -/
def integerConservationCheck (I : Circulation) (f : Fin I.m → ℤ) : Bool :=
  (List.finRange I.n).all (fun v =>
    (∑ e, ((if v = I.tail e then 1 else 0) - (if v = I.head e then 1 else 0) : ℤ) * f e) = 0)

/-- The integer check is exactly the real conservation constraint. -/
theorem integerConservationCheck_iff (I : Circulation) (f : Fin I.m → ℤ) :
    I.integerConservationCheck f = true ↔ I.Conserves (fun e => (f e : ℝ)) := by
  simp only [integerConservationCheck, List.all_eq_true, decide_eq_true_eq,
    List.mem_finRange, forall_const]
  constructor
  · intro h v
    have hh := congrArg (fun z : ℤ => (z : ℝ)) (h v)
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_ite,
      Int.cast_one, Int.cast_zero, balance, incidence] using hh
  · intro h v
    have hh := h v
    apply (Int.cast_inj (α := ℝ)).mp
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_ite,
      Int.cast_one, Int.cast_zero, balance, incidence] using hh

/-- Enumerate bounded integer tables by explicit finite product loops. -/
def boundedIntegerTables (I : Circulation) : List (Fin I.m → ℤ) :=
  (List.pi (List.finRange I.m) (fun e => List.range (I.capacity e + 1))).map
    (fun f e => (f e (List.mem_finRange e) : ℤ))

/-- Enumeration covers precisely all nonnegative capacity-bounded tables. -/
theorem mem_boundedIntegerTables (I : Circulation) (f : Fin I.m → ℤ) :
    f ∈ I.boundedIntegerTables ↔ ∀ e, 0 ≤ f e ∧ f e ≤ (I.capacity e : ℤ) := by
  constructor
  · intro h
    obtain ⟨g, hg, heq⟩ := List.mem_map.mp h
    have hh := (List.mem_pi _ _).mp hg
    intro e
    have hb := List.mem_range.mp (hh e (List.mem_finRange e))
    rw [← heq]
    dsimp only
    constructor <;> omega
  · intro hf
    let g : ∀ e ∈ List.finRange I.m, ℕ := fun e _ => (f e).toNat
    have hg : g ∈ List.pi (List.finRange I.m) (fun e => List.range (I.capacity e + 1)) := by
      apply (List.mem_pi _ _).mpr
      intro e _
      apply List.mem_range.mpr
      have hh := hf e
      dsimp only [g]
      omega
    apply List.mem_map.mpr
    refine ⟨g, hg, ?_⟩
    funext e
    exact Int.toNat_of_nonneg (hf e).1

/-- Scan candidates, keeping a feasible incumbent with the smallest objective
seen. Candidate bounds are supplied by the enumeration, not tested with reals. -/
def scanIntegerMinimum (I : Circulation) :
    List (Fin I.m → ℤ) → (Fin I.m → ℤ) → (Fin I.m → ℤ)
  | [], best => best
  | f :: rest, best =>
      let next := if I.integerConservationCheck f = true ∧
        I.integerObjective f < I.integerObjective best then f else best
      I.scanIntegerMinimum rest next

/-- The scan preserves feasibility and is no worse than any feasible table
in its input, or the initial incumbent. -/
theorem scanIntegerMinimum_spec (I : Circulation) (tables : List (Fin I.m → ℤ))
    (hb : ∀ f ∈ tables, ∀ e, 0 ≤ f e ∧ f e ≤ (I.capacity e : ℤ))
    (best : Fin I.m → ℤ) (hbest : I.Feasible (fun e => (best e : ℝ))) :
    I.Feasible (fun e => (I.scanIntegerMinimum tables best e : ℝ)) ∧
      I.integerObjective (I.scanIntegerMinimum tables best) ≤ I.integerObjective best ∧
      ∀ f ∈ tables, I.Feasible (fun e => (f e : ℝ)) →
        I.integerObjective (I.scanIntegerMinimum tables best) ≤ I.integerObjective f := by
  induction tables generalizing best with
  | nil => exact ⟨hbest, le_rfl, by intro f h; cases h⟩
  | cons f rest ih =>
    let next := if I.integerConservationCheck f = true ∧
      I.integerObjective f < I.integerObjective best then f else best
    have hn : I.Feasible (fun e => (next e : ℝ)) := by
      dsimp only [next]
      split
      · rename_i h
        refine ⟨(I.integerConservationCheck_iff f).mp h.1, ?_⟩
        intro e
        have hh := hb f (List.mem_cons_self) e
        exact ⟨Int.cast_nonneg_iff.mpr hh.1, by change (f e : ℝ) ≤ (I.capacity e : ℝ); exact_mod_cast hh.2⟩
      · exact hbest
    have hle : I.integerObjective next ≤ I.integerObjective best := by
      dsimp only [next]
      split
      · rename_i h; exact le_of_lt h.2
      · exact le_rfl
    have hhead : I.Feasible (fun e => (f e : ℝ)) → I.integerObjective next ≤ I.integerObjective f := by
      intro hf
      dsimp only [next]
      split
      · exact le_rfl
      · rename_i h
        have hh := (I.integerConservationCheck_iff f).mpr hf.1
        exact le_of_not_gt (fun hlt => h ⟨hh, hlt⟩)
    have hr := ih (fun g hg => hb g (List.mem_cons_of_mem f hg)) next hn
    refine ⟨hr.1, hr.2.1.trans hle, ?_⟩
    intro g hg hgf
    rcases List.mem_cons.mp hg with heq | hmem
    · subst g; exact hr.2.1.trans (hhead hgf)
    · exact hr.2.2 g hmem hgf

/-- A slow exact solver using finite integer loops, with no oracle calls. -/
def exactSolver (I : Circulation) : Fin I.m → ℤ :=
  I.scanIntegerMinimum I.boundedIntegerTables (fun _ => 0)

/-- The explicit solver is an integral exact minimum against all feasible
real circulations, without cost or capacity bounds beyond the input data. -/
theorem exactSolver_optimal (I : Circulation) :
    I.Optimal (fun e => (I.exactSolver e : ℝ)) := by
  have hs := I.scanIntegerMinimum_spec I.boundedIntegerTables
    (fun f hf => (I.mem_boundedIntegerTables f).mp hf) (fun _ => 0)
    (by simpa only [Int.cast_zero] using I.zero_feasible)
  apply I.optimal_of_integer_minimum I.exactSolver hs.1
  intro g hg
  apply hs.2.2 g
  · apply (I.mem_boundedIntegerTables g).mpr
    intro e
    have hh : (g e : ℝ) ≤ (I.capacity e : ℝ) := (hg.2 e).2
    exact ⟨Int.cast_nonneg_iff.mp (hg.2 e).1, by exact_mod_cast hh⟩
  · exact hg

/-- In particular, the bounded primitive hypotheses of C.1 and C.9 can all
hold at once, witnessed by the explicit finite solver. -/
theorem exists_bounded_exact_solver :
    ∃ solve : (I : Circulation) → Fin I.m → ℤ,
      ∀ I : Circulation, I.CostsBounded (I.m ^ 10) →
        (∀ e, 1 ≤ I.capacity e ∧ I.capacity e ≤ I.m ^ 40) →
        I.Optimal (fun e => (solve I e : ℝ)) :=
  ⟨exactSolver, fun I _ _ => I.exactSolver_optimal⟩

end MinCostFlow.Scaling.Circulation
