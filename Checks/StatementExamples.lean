module

public import MinCostFlow.Statement.Main

/-!
# Checks of the statement on small examples

These examples test the definitions of the statement on small inputs: feasibility, costs and
minimum-cost flows, flows against the direction of an edge, edges from a vertex to itself,
infeasible instances, the bounds `U` and `C`, the encodings, and runs of small programs on the
machine.
-/

namespace MinCostFlow

open WordRAM

/-! ## Instances and answers -/

/-- A sum over the edges of an instance with one edge. -/
theorem sum_of_eq_one {n : ℕ} (h : n = 1) (F : Fin n → ℝ) : ∑ j, F j = F ⟨0, by omega⟩ := by
  subst h
  simp only [Fin.sum_univ_one]
  rfl

/-- A sum over the edges of an instance with two edges. -/
theorem sum_of_eq_two {n : ℕ} (h : n = 2) (F : Fin n → ℝ) :
    ∑ j, F j = F ⟨0, by omega⟩ + F ⟨1, by omega⟩ := by
  subst h
  simp only [Fin.sum_univ_two]
  rfl

/-- One edge from vertex 0 to vertex 1 with capacities `[0, 5]` and cost 1, and 3 units to send
from 0 to 1. -/
def oneEdge : Instance :=
  { n := 2, edges := [⟨0, 1, 0, 5, 1⟩], demand := [3, -3] }

example : oneEdge.IsValid := by
  unfold Instance.IsValid
  decide

/-- The feasible flows of `oneEdge` send exactly 3 units along the edge: at vertex 0 the row of
`Bᵀ f = d` reads `f_0 = 3`. -/
theorem oneEdge_isFeasible_iff (f : Fin oneEdge.m → ℝ) :
    oneEdge.IsFeasible f ↔ f ⟨0, by decide⟩ = 3 := by
  constructor
  · intro hf
    have h := hf.1 ⟨0, by decide⟩
    rw [sum_of_eq_one (n := oneEdge.m) rfl] at h
    simpa [Instance.edge, Instance.d, Edge.b, oneEdge] using h
  · intro hf
    refine ⟨fun ⟨v, hv⟩ => ?_, fun ⟨j, hj⟩ => ?_⟩
    · rw [sum_of_eq_one (n := oneEdge.m) rfl]
      have hv : v < 2 := hv
      interval_cases v <;> simp [Instance.edge, Instance.d, Edge.b, oneEdge] <;> exact hf
    · have hj : j = 0 := by have : j < 1 := hj; omega
      subst hj
      rw [show f ⟨0, hj⟩ = 3 from hf]
      simp only [Instance.edge, oneEdge]
      norm_num

/-- The answer `1, (0, 3)`: the flow that sends 3 units, written as the integer `3`. -/
example : oneEdge.IsCorrectAnswer [1, 0, 3] := by
  refine Or.inr ⟨fun _ => 3, ⟨(oneEdge_isFeasible_iff _).2 (by norm_num), fun g hg => ?_⟩, rfl⟩
  have hg0 := (oneEdge_isFeasible_iff g).1 hg
  simp only [Instance.cost]
  rw [sum_of_eq_one (n := oneEdge.m) rfl, sum_of_eq_one (n := oneEdge.m) rfl, hg0]
  norm_num

/-- The same edge with 6 units to send. -/
def oneEdgeSix : Instance :=
  { n := 2, edges := [⟨0, 1, 0, 5, 1⟩], demand := [6, -6] }

/-- With 6 units to send and capacity 5 there is no feasible flow, and `[0]` is the answer. -/
example : oneEdgeSix.IsCorrectAnswer [0] := by
  refine Or.inl ⟨rfl, fun f hf => ?_⟩
  have h := hf.1 ⟨0, by decide⟩
  have hc := (hf.2 ⟨0, by decide⟩).2
  rw [sum_of_eq_one (n := oneEdgeSix.m) rfl] at h
  simp [Instance.edge, Instance.d, Edge.b, oneEdgeSix] at h hc
  linarith

/-- Demands that do not add up to `0` cannot be routed. -/
example : ({ n := 1, edges := [], demand := [1] } : Instance).IsCorrectAnswer [0] := by
  refine Or.inl ⟨rfl, fun f hf => ?_⟩
  have h := hf.1 ⟨0, by decide⟩
  have hempty : IsEmpty (Fin ({ n := 1, edges := [], demand := [1] } : Instance).m) :=
    ⟨fun j => absurd j.2 (by simp [Instance.m])⟩
  simp [Instance.d] at h

/-- Two parallel edges from 0 to 1: the first has capacities `[0, 2]` and cost 1, the second
`[0, 5]` and cost 3. Three units go from 0 to 1. -/
def twoParallel : Instance :=
  { n := 2, edges := [⟨0, 1, 0, 2, 1⟩, ⟨0, 1, 0, 5, 3⟩], demand := [3, -3] }

/-- The cost of a feasible flow of `twoParallel` is at least 5: it sends `f_0 + f_1 = 3` units
with `f_0 ≤ 2`, at cost `f_0 + 3 f_1 = 9 - 2 f_0`. -/
theorem twoParallel_cost_ge (g : Fin twoParallel.m → ℝ) (hg : twoParallel.IsFeasible g) :
    5 ≤ twoParallel.cost g := by
  have h := hg.1 ⟨0, by decide⟩
  have hc := (hg.2 ⟨0, by decide⟩).2
  rw [sum_of_eq_two (n := twoParallel.m) rfl] at h
  simp [Instance.edge, Instance.d, Edge.b, twoParallel] at h hc
  simp only [Instance.cost]
  rw [sum_of_eq_two (n := twoParallel.m) rfl]
  simp [Instance.edge, twoParallel]
  linarith

/-- The flow `(2, 1)` of `twoParallel` is feasible. -/
theorem twoParallel_isFeasible : twoParallel.IsFeasible (fun j => if (j : ℕ) = 0 then 2 else 1) := by
  refine ⟨fun ⟨v, hv⟩ => ?_, fun ⟨j, hj⟩ => ?_⟩
  · rw [sum_of_eq_two (n := twoParallel.m) rfl]
    have hv : v < 2 := hv
    interval_cases v <;> simp [Instance.edge, Instance.d, Edge.b, twoParallel] <;> norm_num
  · have hj : j < 2 := hj
    interval_cases j <;> simp [Instance.edge, twoParallel]

/-- The cheapest flow uses the cheap edge to its capacity: `f = (2, 1)`, of cost 5. -/
example : twoParallel.IsCorrectAnswer [1, 0, 2, 0, 1] := by
  refine Or.inr ⟨fun j => if (j : ℕ) = 0 then 2 else 1, ⟨?_, fun g hg => ?_⟩, rfl⟩
  · simpa using twoParallel_isFeasible
  · have h5 : twoParallel.cost (fun j => if (j : ℕ) = 0 then 2 else 1) = 5 := by
      simp only [Instance.cost]
      rw [sum_of_eq_two (n := twoParallel.m) rfl]
      simp [Instance.edge, twoParallel]
      norm_num
    have := twoParallel_cost_ge g hg
    simp only [Int.cast_ite] at h5 ⊢
    push_cast
    linarith

/-- The flow `(0, 3)` is feasible but not of minimum cost: it costs 9, and `(2, 1)` costs 5. -/
example : ¬ twoParallel.IsMinCostFlow (fun j => if (j : ℕ) = 0 then 0 else 3) := by
  rintro ⟨-, h⟩
  have := h _ twoParallel_isFeasible
  simp only [Instance.cost] at this
  rw [sum_of_eq_two (n := twoParallel.m) rfl, sum_of_eq_two (n := twoParallel.m) rfl] at this
  simp [Instance.edge, twoParallel] at this
  norm_num at this

/-- One edge from 0 to 1 with capacities `[-4, 0]`, and two units to send from 1 to 0. -/
def backward : Instance :=
  { n := 2, edges := [⟨0, 1, -4, 0, 0⟩], demand := [-2, 2] }

/-- A flow may go against the direction of an edge: the two units go from 1 to 0 as the flow
`-2`, written as the integer `-2`, that is, the words `1, 2`. -/
example : backward.IsCorrectAnswer [1, 1, 2] := by
  refine Or.inr ⟨fun _ => -2, ⟨⟨fun ⟨v, hv⟩ => ?_, fun ⟨j, hj⟩ => ?_⟩, fun g _ => ?_⟩, rfl⟩
  · rw [sum_of_eq_one (n := backward.m) rfl]
    have hv : v < 2 := hv
    interval_cases v <;> simp [Instance.edge, Instance.d, Edge.b, backward]
  · have hj : j = 0 := by have : j < 1 := hj; omega
    subst hj
    simp [Instance.edge, backward]
    norm_num
  · simp only [Instance.cost]
    rw [sum_of_eq_one (n := backward.m) rfl, sum_of_eq_one (n := backward.m) rfl]
    simp [Instance.edge, backward]

/-- One edge from vertex 0 to itself, with capacities `[0, 3]` and cost `-1`. -/
def selfLoop : Instance :=
  { n := 1, edges := [⟨0, 0, 0, 3, -1⟩], demand := [0] }

/-- An edge from a vertex to itself has `b_e = 0`, so it only adds its cost: the cheapest flow
fills it. -/
example : selfLoop.IsCorrectAnswer [1, 0, 3] := by
  refine Or.inr ⟨fun _ => 3, ⟨⟨fun ⟨v, hv⟩ => ?_, fun ⟨j, hj⟩ => ?_⟩, fun g hg => ?_⟩, rfl⟩
  · rw [sum_of_eq_one (n := selfLoop.m) rfl]
    have hv : v = 0 := by have : v < 1 := hv; omega
    subst hv
    simp [Instance.edge, Instance.d, Edge.b, selfLoop]
  · have hj : j = 0 := by have : j < 1 := hj; omega
    subst hj
    simp [Instance.edge, selfLoop]
  · have hc := (hg.2 ⟨0, by decide⟩).2
    simp [Instance.edge, selfLoop] at hc
    simp only [Instance.cost]
    rw [sum_of_eq_one (n := selfLoop.m) rfl, sum_of_eq_one (n := selfLoop.m) rfl]
    simp [Instance.edge, selfLoop]
    exact hc

/-- The bounds `U` and `C` of `twoParallel`. -/
example : twoParallel.maxCapacity = 5 ∧ twoParallel.maxCost = 3 := by decide

/-- The encoding of `oneEdge`: `n = 2`, `m = 1`, the edge `0, 1, (0, 0), (0, 5), (0, 1)`, and the
demands `(0, 3), (1, 3)`. -/
example : oneEdge.encode = [2, 1, 0, 1, 0, 0, 0, 5, 0, 1, 0, 3, 1, 3] := rfl

/-! ## Deterministic programs -/

/-- A statement with no `rand` runs the same way for all random bits, in a program whose
procedures have no `rand`. The proof goes by induction on the fuel: only `rand` reads the bits,
and every other statement runs statements that also have no `rand`, including the procedure
bodies that a `call` runs. -/
theorem exec_eq_of_noRand {w : ℕ} {p : Program} (hp : p.IsDeterministic) (ω ω' : ℕ → Bool) :
    ∀ fuel s st, s.NoRand → exec w p ω fuel s st = exec w p ω' fuel s st := by
  intro fuel
  induction fuel with
  | zero => intro s st _; rfl
  | succ n ih =>
    intro s st hs
    cases s with
    | nop => rfl
    | assign r e => rfl
    | store a e => rfl
    | rand r => exact hs.elim
    | ret e => rfl
    | seq s t =>
      have ht : ∀ st', exec w p ω n t st' = exec w p ω' n t st' := fun st' => ih t st' hs.2
      simp only [exec, ih s st hs.1, ht]
    | cond e s t =>
      have hb : ∀ v, exec w p ω n (if v = 0 then t else s) st =
          exec w p ω' n (if v = 0 then t else s) st := by
        intro v
        split_ifs
        · exact ih t st hs.2
        · exact ih s st hs.1
      simp only [exec, hb]
    | loop e body =>
      have hb : ∀ st', exec w p ω n body st' = exec w p ω' n body st' :=
        fun st' => ih body st' hs
      have hl : ∀ st', exec w p ω n (.loop e body) st' = exec w p ω' n (.loop e body) st' :=
        fun st' => ih (.loop e body) st' hs
      simp only [exec, hb, hl]
    | call r f args =>
      rcases hv : evalArgs w st args with _ | vs <;> rcases hf : p.procs[f]? with _ | body
      · simp only [exec, hv, hf]
      · simp only [exec, hv, hf]
      · simp only [exec, hv, hf]
      · have hb : ∀ st', exec w p ω n body st' = exec w p ω' n body st' :=
          fun st' => ih body st' (hp body (List.mem_of_getElem? hf))
        simp only [exec, hv, hf, hb]

/-- A deterministic program has the same runs for all random bits. -/
theorem runsTo_iff_of_isDeterministic {w : ℕ} {p : Program} (hp : p.IsDeterministic)
    (input : List ℕ) (ω ω' : ℕ → Bool) (out : List ℕ) (cost : ℕ) :
    RunsTo w p input ω out cost ↔ RunsTo w p input ω' out cost := by
  have h : ∀ fuel, run w p ω input fuel = run w p ω' input fuel := by
    intro fuel
    unfold run
    rw [exec_eq_of_noRand hp ω ω' fuel (.call 0 0 [.const input.length]) _ trivial]
  simp only [RunsTo, h]

/-- A program that writes `0` at address 0 and returns 1 outputs `[0]`. At word size 4 the call
costs 2 (its argument and the call itself), the `store` 3, the `ret` 2, and the sequence 1. -/
example : run 4 ⟨[.seq (.store (.const 0) (.const 0)) (.ret (.const 1))]⟩ (fun _ => false) [5] 3 =
    some ([0], 8) := by
  decide

/-- A program with a `rand` statement is not deterministic. -/
example : ¬ (⟨[.seq (.rand 0) (.ret (.reg 0))]⟩ : Program).IsDeterministic := by
  simp [Program.IsDeterministic, Stmt.NoRand]

end MinCostFlow
