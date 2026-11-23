module

public import WordRAM.Model
public import MinCostFlow.Statement.Problem
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The main theorem: statement

This file states Theorem 1.1 of the paper (*A Deterministic Almost-Linear Time Algorithm for
Minimum-Cost Flow*, arXiv:2309.16629v1, page 2) over the machine of `WordRAM/Model.lean` and the
problem of `MinCostFlow/Statement/Problem.lean`.

> **Theorem 1.1 (Min-cost flow).** There is a deterministic algorithm that given a `m`-edge graph
> with integral vertex demands and edge capacities bounded by `U` in absolute value, and integral
> edge costs bounded by `C` in absolute value, computes an (exact) minimum-cost flow in time
> `m^{1+o(1)} log U log C`.

The paper's model of computation (Section 2, page 7):

> For problem instances encoded with `z` bits, all algorithms developed in this paper work in
> fixed-point arithmetic where words have `O(log^{O(1)} z)` bits, i.e., we prove that all numbers
> stored are in `[exp(-log^{O(1)} z), exp(log^{O(1)} z)]`.

How the statement reads the words of the paper:

* "There is a deterministic algorithm": a program `P` with no `rand` statement
  (`Program.IsDeterministic`). Its run is then the same for every sequence `ω` of random bits, and
  the statement asks for a correct answer within the time bound for every `ω`.
* The machine is the word RAM of `WordRAM/Model.lean`, with words of `wordSize c input` bits for
  a constant `c`: `c` times the number of bits of the largest number of the input or its length.
  The paper's fixed-point numbers of `log^{O(1)} z` bits take `log^{O(1)} z` such words, and an
  operation on them takes `log^{O(1)} z` steps.
* "Given a `m`-edge graph with integral vertex demands and edge capacities bounded by `U` in
  absolute value, and integral edge costs bounded by `C`": every well-formed instance
  (`Instance.IsValid`), with `U = Instance.maxCapacity` and `C = Instance.maxCost`, the least
  bounds. The time bound grows with `U` and `C`, so the statement then holds for every larger
  bound as well.
* "Computes an (exact) minimum-cost flow": the output is a correct answer
  (`Instance.IsCorrectAnswer`): an integral minimum-cost flow, or `[0]` when no flow is feasible.
* The time `m^{1+o(1)} log U log C` is `timeBound K ε I`, which is
  `K·n + (m+2)^{1+ε(m)}·log(U+2)·log(C+2)` with `ε(m) → 0`. Writing `m + 2`, `U + 2` and
  `C + 2` for `m`, `U` and `C` changes the bound by at most a constant factor when `m, U, C ≥ 2`,
  and keeps it positive for smaller values.
* The term `K·n` is not in the printed bound. A program must read the demands of all `n`
  vertices, since one vertex with no edges and a nonzero demand makes the instance infeasible. So
  no program meets the printed bound on instances with many more vertices than edges. When
  `n ≤ m + 1`, for example when the graph is connected, `K·n` is at most a constant times `m + 2`
  and is absorbed into `(m+2)^{1+ε(m)}`.
* The program `P`, the constants `c` and `K`, and the function `ε` do not depend on the instance.
-/

@[expose] public section

namespace MinCostFlow

open WordRAM Filter Topology

/-- The running time bound of Theorem 1.1, `K·n + (m+2)^{1+ε(m)}·log(U+2)·log(C+2)`. -/
noncomputable def timeBound (K : ℝ) (ε : ℕ → ℝ) (I : Instance) : ℝ :=
  K * I.n + ((I.m : ℝ) + 2) ^ (1 + ε I.m) * Real.log ((I.maxCapacity : ℝ) + 2) *
    Real.log ((I.maxCost : ℝ) + 2)

/-- **Theorem 1.1** (Min-cost flow, page 2). There are a deterministic program `P`, a word size
constant `c`, a constant `K` and a function `ε` tending to `0`, such that on every well-formed
instance, `P` halts with a correct answer (an integral minimum-cost flow, or the report that no
flow is feasible) within `K·n + (m+2)^{1+ε(m)}·log(U+2)·log(C+2)` steps. -/
def MinCostFlowStatement : Prop :=
  ∃ (P : Program) (c : ℕ) (K : ℝ) (ε : ℕ → ℝ),
    P.IsDeterministic ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ I : Instance, I.IsValid → ∀ ω, ∃ out cost,
      RunsTo (wordSize c I.encode) P I.encode ω out cost ∧ I.IsCorrectAnswer out ∧
        (cost : ℝ) ≤ timeBound K ε I

end MinCostFlow
