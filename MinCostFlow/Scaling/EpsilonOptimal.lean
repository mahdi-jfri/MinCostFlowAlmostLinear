module

public import MinCostFlow.Scaling.Circulation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Strict epsilon optimality

Definition C.4 of Chen et al., arXiv:2203.00671v2, asks that every active
residual arc have reduced cost strictly greater than minus epsilon. The two
implications below express this without building a real-capacity residual
instance. The source's claimed initialization at epsilon `C` fails because
its inequality is strict. Initialization at `C + 1` repairs that step.
-/

@[expose] public section

namespace MinCostFlow.Scaling.Circulation

/-- Definition C.4, with its witness potential supplied explicitly. Forward
arcs are active below capacity and reverse arcs are active above zero. -/
def EpsilonOptimalWith (I : Circulation) (f : Fin I.m → ℝ)
    (epsilon : ℝ) (y : Fin I.n → ℝ) : Prop :=
  0 < epsilon ∧ I.Feasible f ∧ ∀ e,
    (f e < I.capacity e → -epsilon < I.reducedCost y e) ∧
    (0 < f e → -epsilon < -I.reducedCost y e)

/-- Definition C.4 (Appendix C): a feasible circulation is epsilon optimal
when a potential makes every active residual reduced cost exceed `-epsilon`. -/
def EpsilonOptimal (I : Circulation) (f : Fin I.m → ℝ) (epsilon : ℝ) : Prop :=
  ∃ y, I.EpsilonOptimalWith f epsilon y

/-- The strict initialization needed for Algorithm CostScaling. Unlike the
source's initialization at `C`, this also covers an edge of cost exactly `-C`. -/
theorem zero_epsilonOptimal (I : Circulation) (C : ℕ)
    (hc : ∀ e, -(C : ℤ) ≤ I.cost e) :
    I.EpsilonOptimalWith (fun _ => 0) ((C : ℝ) + 1) (fun _ => 0) := by
  refine ⟨by positivity, I.zero_feasible, ?_⟩
  intro e
  constructor
  · intro _
    have h : -(C : ℝ) ≤ (I.cost e : ℝ) := by
      have := (Int.cast_le (R := ℝ)).mpr (hc e)
      simpa only [Int.cast_neg, Int.cast_natCast] using this
    simp only [reducedCost, potentialDifference, sub_self, sub_zero]
    linarith
  · intro h
    exact False.elim (lt_irrefl (0 : ℝ) h)

/-- A one-edge negative loop witnesses the strict-initialization error in
Appendix C immediately after Definition C.4. -/
def negativeLoop : Circulation where
  n := 1
  m := 1
  tail := fun _ => 0
  head := fun _ => 0
  capacity := fun _ => 1
  cost := fun _ => -1

/-- Zero flow need not be `C`-optimal under the strict Definition C.4. -/
theorem zero_not_one_epsilonOptimal :
    ¬ negativeLoop.EpsilonOptimal (fun _ => 0) 1 := by
  rintro ⟨y, _, _, h⟩
  have hbad := (h ⟨0, by decide⟩).1 (by dsimp [negativeLoop]; norm_num)
  dsimp [reducedCost, potentialDifference, negativeLoop] at hbad
  norm_num at hbad

end MinCostFlow.Scaling.Circulation
