module

public import MinCostFlow.Scaling.Circulation
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Directed walks in a capacitated graph

The strong-duality argument in Appendix C of Chen et al., arXiv:2203.00671v2,
uses the absence of negative cycles in an optimal flow's residual graph. Walks
below use only arcs of positive capacity. Their edge counts give a flow whose
net flow is one at the start and minus one at the end. Thus a nonempty closed
walk, divided by its length, is a feasible circulation. This supplies the
optimality argument for excluding negative closed walks.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- A directed walk using positive-capacity arcs. -/
inductive DirectedWalk (I : Circulation) : Fin I.n → Fin I.n → Type
  | nil (v : Fin I.n) : DirectedWalk I v v
  | cons (e : Fin I.m) (active : 0 < I.capacity e) {v : Fin I.n}
      (rest : DirectedWalk I (I.head e) v) : DirectedWalk I (I.tail e) v

namespace DirectedWalk
variable {I : Circulation} {a b c : Fin I.n}

/-- Number of arcs, counting repetitions. -/
def length {a b : Fin I.n} : DirectedWalk I a b → ℕ
  | .nil _ => 0
  | .cons _ _ p => p.length + 1

/-- The integral cost of a walk. -/
def cost {a b : Fin I.n} : DirectedWalk I a b → ℤ
  | .nil _ => 0
  | .cons e _ p => I.cost e + p.cost

/-- How many times a walk uses a given arc. -/
def count {a b : Fin I.n} : DirectedWalk I a b → Fin I.m → ℕ
  | .nil _, _ => 0
  | .cons e _ p, k => (if k = e then 1 else 0) + p.count k

/-- Visited vertices, including both endpoints. -/
def vertices {a b : Fin I.n} : DirectedWalk I a b → List (Fin I.n)
  | .nil v => [v]
  | .cons e _ p => I.tail e :: p.vertices

/-- Concatenate walks with matching endpoints. -/
def append {a b c : Fin I.n} : DirectedWalk I a b → DirectedWalk I b c → DirectedWalk I a c
  | .nil _, q => q
  | .cons e h p, q => .cons e h (p.append q)

/-- Walk length adds under concatenation. -/
theorem length_append (p : DirectedWalk I a b) (q : DirectedWalk I b c) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp [append, length]
  | cons e h p ih => simp only [append, length, ih]; omega

/-- Walk cost adds under concatenation. -/
theorem cost_append (p : DirectedWalk I a b) (q : DirectedWalk I b c) :
    (p.append q).cost = p.cost + q.cost := by
  induction p with
  | nil => simp [append, cost]
  | cons e h p ih => simp only [append, cost, ih, add_assoc]

/-- An arc cannot be used more times than the walk's length. -/
theorem count_le_length (p : DirectedWalk I a b) (e : Fin I.m) :
    p.count e ≤ p.length := by
  induction p with
  | nil => exact le_rfl
  | cons k h p ih =>
    simp only [count, length]
    split <;> omega

/-- Every used arc has positive capacity. -/
theorem active_of_count_pos (p : DirectedWalk I a b) (e : Fin I.m)
    (h : 0 < p.count e) : 0 < I.capacity e := by
  induction p with
  | nil => exact False.elim (Nat.lt_irrefl 0 h)
  | cons k hk p ih =>
    by_cases he : e = k
    · exact he.symm ▸ hk
    · simp only [count, he, ↓reduceIte, zero_add] at h
      exact ih h

/-- Edge counts telescope to the difference of endpoint indicators. -/
theorem balance_count (p : DirectedWalk I a b) (v : Fin I.n) :
    I.balance (fun e => (p.count e : ℝ)) v =
      (if v = a then 1 else 0) - (if v = b then 1 else 0) := by
  classical
  induction p with
  | nil w => simp [balance, count]
  | cons e h p ih =>
    have he : I.balance (fun k => ((if k = e then 1 else 0 : ℕ) : ℝ)) v =
        I.incidence e v := by
      simp [balance, Nat.cast_ite, mul_ite]
    simp only [count, Nat.cast_add, mul_add, balance, Finset.sum_add_distrib]
    change I.balance (fun k => ((if k = e then 1 else 0 : ℕ) : ℝ)) v +
      I.balance (fun k => (p.count k : ℝ)) v = _
    rw [he, ih]
    simp only [incidence]
    ring

/-- The circulation objective of edge counts equals the walk's cost. -/
theorem objective_count (p : DirectedWalk I a b) :
    I.objective (fun e => (p.count e : ℝ)) = (p.cost : ℝ) := by
  classical
  induction p with
  | nil => simp [objective, count, cost]
  | cons e h p ih =>
    simp only [objective, count, Nat.cast_add, mul_add, Finset.sum_add_distrib]
    change (∑ k, (I.cost k : ℝ) * ((if k = e then 1 else 0 : ℕ) : ℝ)) +
      I.objective (fun k => (p.count k : ℝ)) = _
    rw [ih]
    simp [cost, Nat.cast_ite, mul_ite]

/-- Dividing a nonempty closed walk's edge counts by its length yields a
feasible circulation, since every used edge has capacity at least one. -/
theorem normalized_feasible (p : DirectedWalk I a a) (hp : 0 < p.length) :
    I.Feasible (fun e => (p.count e : ℝ) / (p.length : ℝ)) := by
  have hl : (0 : ℝ) < p.length := Nat.cast_pos.mpr hp
  constructor
  · intro v
    simp only [balance, ← mul_div_assoc, ← Finset.sum_div]
    change I.balance (fun e => (p.count e : ℝ)) v / (p.length : ℝ) = 0
    rw [p.balance_count, sub_self, zero_div]
  · intro e
    refine ⟨div_nonneg (Nat.cast_nonneg _) hl.le, ?_⟩
    by_cases hz : p.count e = 0
    · simp only [hz, Nat.cast_zero, zero_div]
      exact Nat.cast_nonneg _
    · have hc : (1 : ℝ) ≤ I.capacity e := by
        exact_mod_cast p.active_of_count_pos e (Nat.pos_of_ne_zero hz)
      apply le_trans _ hc
      apply (div_le_one hl).mpr
      exact_mod_cast p.count_le_length e

/-- If zero is an optimum, every closed walk of positive-capacity arcs has
nonnegative cost. This is the no-negative-cycle step needed for strong duality. -/
theorem cost_nonneg_of_zero_optimal (p : DirectedWalk I a a)
    (hopt : I.Optimal (fun _ => 0)) : 0 ≤ p.cost := by
  by_cases hp : p.length = 0
  · cases p with
    | nil => exact le_rfl
    | cons e h q => simp only [length] at hp; omega
  · have hl : 0 < p.length := Nat.pos_of_ne_zero hp
    have h := hopt.2 _ (p.normalized_feasible hl)
    have hz : I.objective (fun _ => 0) = 0 := by simp [objective]
    rw [hz] at h
    have he : I.objective (fun e => (p.count e : ℝ) / (p.length : ℝ)) =
        (p.cost : ℝ) / (p.length : ℝ) := by
      simp only [objective, ← mul_div_assoc, ← Finset.sum_div]
      exact congrArg (fun x : ℝ => x / (p.length : ℝ)) p.objective_count
    rw [he] at h
    have hc : (0 : ℝ) ≤ p.cost := by
      simpa only [zero_mul] using (le_div_iff₀ (Nat.cast_pos.mpr hl)).mp h
    exact (Int.cast_nonneg_iff (R := ℝ)).mp hc

end DirectedWalk
end MinCostFlow.Scaling.Circulation
