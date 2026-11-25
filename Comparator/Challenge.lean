module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.List.GetD
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Deterministic almost-linear-time minimum-cost flow: the statement to be proved

The theorem `MinCostFlow.theorem_1_1` is Theorem 1.1 (page 2) of J. van den Brand, L. Chen,
R. Kyng, Y. P. Liu, R. Peng, M. Probst Gutenberg, S. Sachdeva and A. Sidford, *A Deterministic
Almost-Linear Time Algorithm for Minimum-Cost Flow* (arXiv:2309.16629v1). Its conclusion,
`MinCostFlowStatement`, is defined below, over the problem and the machine model.

This file imports only Mathlib, so that it can be checked without the library. It repeats the
files `WordRAM/Model.lean` (of the pinned WordRAM package), `MinCostFlow/Statement/Problem.lean`
and `MinCostFlow/Statement/Main.lean` word for word, without their imports, and
`tools/gen_challenge.py` writes it from them. Comparator checks that every definition used by the
statement is identical here and in the library.

The file `Comparator/Solution.lean` proves the theorem.
-/

-- The file WordRAM/Model.lean, without its imports.
/-!
# The machine model

A statement that an algorithm exists and runs within a time bound needs a model of computation.
This file is the model. It is the part of the library a reader must check to know what such a
statement says; everything else in the library is proved from it.

The model is a randomized word RAM. Programs are data, every step is counted, and every value is
a word.

* **Words.** A run has a word size `w`. Every value that the program computes or stores must be
  less than `2 ^ w`; an operation whose result does not fit stops the run with no answer. So
  memory addresses are also less than `2 ^ w`. The word size of a run on an input is
  `wordSize c input`, which is `c` times the number of bits needed to write the length of the
  input or any of its numbers. Each statement about running times picks its own constant `c`.
* **Unit cost.** Each operation on words costs one, whatever the values are, as in the standard
  word RAM of algorithm design. A log-cost RAM would charge `log n` for each operation instead.
* **Memory.** One global memory `ℕ → ℕ`, which starts with the input at addresses
  `0, …, len - 1` and zero elsewhere. A program writes its output at the start of memory.
* **Procedures.** A program is a list of procedures, and procedure 0 is the entry point. Each
  running procedure has its own registers, which start with the arguments of the call and zero
  elsewhere. A register is named by a constant in the program text, so each procedure uses a
  fixed number of registers, and a call costs as much as a constant-size stack frame.
* **Randomness.** A run reads an infinite sequence `ω : ℕ → Bool` of random bits. The statement
  `rand r` puts a random word into register `r`, made of the next `w` bits, at unit cost.
  Probabilities are taken for `ω` drawn from `coins`, under which the bits are independent and
  uniform, so each random word is uniform on `0, …, 2 ^ w - 1` and independent of the others.
  A program with no `rand` statement is deterministic (`Program.IsDeterministic`).

The semantics `exec` is a function with fuel. Fuel only bounds the depth of the evaluation, so
that the definition terminates; it does not limit the running time, which is the cost.
-/

@[expose] public section

namespace WordRAM

/-- Binary operations on words. Comparisons give 1 for true and 0 for false. Subtraction stops at
0, and division or remainder by 0 gives 0, as for `ℕ` in Lean. The bitwise operations and shifts
are those of the standard word RAM. -/
inductive BinOp
  | add | sub | mul | div | mod | lt | eq | and | or | xor | shiftLeft | shiftRight
  deriving DecidableEq, Repr

/-- The value of a binary operation, before the check that it fits in a word. -/
def BinOp.eval : BinOp → ℕ → ℕ → ℕ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .lt, a, b => if a < b then 1 else 0
  | .eq, a, b => if a = b then 1 else 0
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shiftLeft, a, b => a <<< b
  | .shiftRight, a, b => a >>> b

/-- Expressions. `reg r` reads register `r` of the running procedure, and `load a` reads the
memory cell whose address is the value of `a`. -/
inductive Expr
  | const (k : ℕ)
  | reg (r : ℕ)
  | load (addr : Expr)
  | bin (op : BinOp) (a b : Expr)
  deriving Repr

/-- The number of operations in an expression. Evaluating it costs this much. -/
def Expr.size : Expr → ℕ
  | .const _ => 1
  | .reg _ => 1
  | .load a => a.size + 1
  | .bin _ a b => a.size + b.size + 1

/-- The memory and the registers of the running procedure, and the position of the next random
bit to be read. -/
structure State where
  mem : ℕ → ℕ
  regs : ℕ → ℕ
  pos : ℕ

/-- The value of an expression at word size `w`, or `none` if a constant or the result of an
operation is not less than `2 ^ w`. Registers and memory hold only words, since everything stored
there passed this check or came from the input. -/
def Expr.eval (w : ℕ) (st : State) : Expr → Option ℕ
  | .const k => if k < 2 ^ w then some k else none
  | .reg r => some (st.regs r)
  | .load a => (a.eval w st).map st.mem
  | .bin op a b =>
    match a.eval w st, b.eval w st with
    | some x, some y => if op.eval x y < 2 ^ w then some (op.eval x y) else none
    | _, _ => none

/-- The values of a list of expressions, or `none` if one of them has no value. -/
def evalArgs (w : ℕ) (st : State) : List Expr → Option (List ℕ)
  | [] => some []
  | e :: es =>
    match e.eval w st, evalArgs w st es with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- The total size of a list of expressions. -/
def argsSize : List Expr → ℕ
  | [] => 0
  | e :: es => e.size + argsSize es

/-- Statements.
* `assign r e` puts the value of `e` in register `r`.
* `store a e` puts the value of `e` in the memory cell at the value of `a`.
* `rand r` puts the next random word in register `r` (see `readWord`).
* `cond e s t` runs `s` if `e` is nonzero and `t` otherwise.
* `loop e s` runs `s` while `e` is nonzero.
* `call r f args` runs procedure `f`. Its registers start with the values of `args` in
  registers `0, 1, …` and 0 everywhere else. Its return value goes to register `r`.
* `ret e` ends the running procedure with the value of `e`. A procedure that ends without
  `ret` returns 0. -/
inductive Stmt
  | nop
  | assign (r : ℕ) (e : Expr)
  | store (addr val : Expr)
  | rand (r : ℕ)
  | seq (s t : Stmt)
  | cond (e : Expr) (s t : Stmt)
  | loop (e : Expr) (body : Stmt)
  | call (r : ℕ) (f : ℕ) (args : List Expr)
  | ret (e : Expr)
  deriving Repr

/-- A program: the bodies of its procedures. Procedure 0 is the entry point. -/
structure Program where
  procs : List Stmt
  deriving Repr

/-- `s` contains no `rand` statement. -/
def Stmt.NoRand : Stmt → Prop
  | .rand _ => False
  | .seq s t => s.NoRand ∧ t.NoRand
  | .cond _ s t => s.NoRand ∧ t.NoRand
  | .loop _ body => body.NoRand
  | _ => True

/-- `p` is deterministic: none of its procedures contains a `rand` statement, so it never reads
the random bits. `Checks/StatementExamples.lean` proves that its runs are then the same for every
sequence of random bits (`runsTo_iff_of_isDeterministic`). -/
def Program.IsDeterministic (p : Program) : Prop :=
  ∀ s ∈ p.procs, s.NoRand

/-- The word whose binary digits are the `w` bits `ω pos, …, ω (pos + w - 1)`, lowest digit
first. It is less than `2 ^ w`. -/
def readWord (ω : ℕ → Bool) (pos : ℕ) : ℕ → ℕ
  | 0 => 0
  | w + 1 => (if ω pos then 1 else 0) + 2 * readWord ω (pos + 1) w

/-- How a statement ended: normally, or by `ret` with a value. -/
inductive Outcome
  | normal
  | returned (v : ℕ)
  deriving DecidableEq, Repr

/-- Run statement `s` of program `p` from state `st`, at word size `w`, with random bits `ω`. The
result is how the statement ended, the new state, and the cost. Every statement costs one plus
the sizes of the expressions it evaluates, plus the costs of the statements it runs.

The result is `none` when a value does not fit in a word, when a call names a procedure that
does not exist, or when the run needs more than `fuel` levels of evaluation. Fuel bounds only the
depth of the evaluation, so that this function terminates: more fuel never changes a result
that is not `none`. -/
def exec (w : ℕ) (p : Program) (ω : ℕ → Bool) : ℕ → Stmt → State → Option (Outcome × State × ℕ)
  | 0, _, _ => none
  | fuel + 1, s, st =>
    match s with
    | .nop => some (.normal, st, 1)
    | .assign r e =>
      match e.eval w st with
      | none => none
      | some v => some (.normal, { st with regs := Function.update st.regs r v }, e.size + 1)
    | .store a e =>
      match a.eval w st, e.eval w st with
      | some x, some v =>
        some (.normal, { st with mem := Function.update st.mem x v }, a.size + e.size + 1)
      | _, _ => none
    | .rand r =>
      some (.normal,
        { st with regs := Function.update st.regs r (readWord ω st.pos w), pos := st.pos + w }, 1)
    | .seq s t =>
      match exec w p ω fuel s st with
      | none => none
      | some (.returned v, st', c) => some (.returned v, st', c + 1)
      | some (.normal, st', c) =>
        match exec w p ω fuel t st' with
        | none => none
        | some (o, st'', c') => some (o, st'', c + c' + 1)
    | .cond e s t =>
      match e.eval w st with
      | none => none
      | some v =>
        match exec w p ω fuel (if v = 0 then t else s) st with
        | none => none
        | some (o, st', c) => some (o, st', e.size + c + 1)
    | .loop e body =>
      match e.eval w st with
      | none => none
      | some v =>
        if v = 0 then some (.normal, st, e.size + 1) else
        match exec w p ω fuel body st with
        | none => none
        | some (.returned u, st', c) => some (.returned u, st', e.size + c + 1)
        | some (.normal, st', c) =>
          match exec w p ω fuel (.loop e body) st' with
          | none => none
          | some (o, st'', c') => some (o, st'', e.size + c + c' + 1)
    | .call r f args =>
      match evalArgs w st args, p.procs[f]? with
      | some vs, some body =>
        match exec w p ω fuel body { st with regs := fun i => vs.getD i 0 } with
        | none => none
        | some (o, st', c) =>
          let u := match o with
            | .returned u => u
            | .normal => 0
          some (.normal, { st' with regs := Function.update st.regs r u }, argsSize args + c + 1)
      | _, _ => none
    | .ret e =>
      match e.eval w st with
      | none => none
      | some v => some (.returned v, st, e.size + 1)

/-- The memory at the start of a run: the input at addresses `0, …, len - 1`, and zero
elsewhere. -/
def initMem (input : List ℕ) (a : ℕ) : ℕ :=
  input.getD a 0

/-- Run program `p` at word size `w` with random bits `ω` on `input`, by calling procedure 0 with
the length of the input as its argument. If procedure 0 returns `ℓ`, the output is the contents
of memory cells `0, …, ℓ - 1`. The result is the output and the total cost, or `none` as for
`exec`. -/
def run (w : ℕ) (p : Program) (ω : ℕ → Bool) (input : List ℕ) (fuel : ℕ) :
    Option (List ℕ × ℕ) :=
  match exec w p ω fuel (.call 0 0 [.const input.length])
      { mem := initMem input, regs := fun _ => 0, pos := 0 } with
  | none => none
  | some (_, st, c) => some ((List.range (st.regs 0)).map st.mem, c)

/-- `RunsTo w p input ω out cost`: at word size `w` and with random bits `ω`, program `p` halts
on `input` with output `out` after `cost` steps. -/
def RunsTo (w : ℕ) (p : Program) (input : List ℕ) (ω : ℕ → Bool) (out : List ℕ) (cost : ℕ) :
    Prop :=
  ∃ fuel, run w p ω input fuel = some (out, cost)

/-- The word size for `input` with constant `c`: `c` times the number of bits of
`len + max + 2`, where `len` is the length of the input and `max` is its largest number. Every
number of the input, and every address of the input, is less than `2 ^ wordSize c input` when
`c ≥ 1`. -/
def wordSize (c : ℕ) (input : List ℕ) : ℕ :=
  c * (Nat.log 2 (input.length + input.foldr max 0 + 2) + 1)

/-- The distribution of the random bits: independent bits, each 0 or 1 with probability `1/2`. -/
noncomputable def coins : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi fun _ => (PMF.uniformOfFintype Bool).toMeasure

end WordRAM
end

-- The file MinCostFlow/Statement/Problem.lean, without its imports.
/-!
# The minimum-cost flow problem

This file defines the problem of Theorem 1.1 of the paper (J. van den Brand, L. Chen, R. Kyng,
Y. P. Liu, R. Peng, M. Probst Gutenberg, S. Sachdeva, A. Sidford, *A Deterministic Almost-Linear
Time Algorithm for Minimum-Cost Flow*, arXiv:2309.16629v1, page 2):

> **Theorem 1.1 (Min-cost flow).** There is a deterministic algorithm that given a `m`-edge graph
> with integral vertex demands and edge capacities bounded by `U` in absolute value, and integral
> edge costs bounded by `C` in absolute value, computes an (exact) minimum-cost flow in time
> `m^{1+o(1)} log U log C`.

Its conventions are those of Section 2 (page 5):

> We consider multi-graphs `G` with edge set `E(G)` and vertex set `V(G)`. […] We assume that
> each edge `e ∈ E` has an implicit direction and overload the notation slightly by writing
> `e = (u, v)` where `u` and `v` are the tail and head of `e` respectively […].
>
> A *flow vector* is a vector `f ∈ ℝ^E`. If `f_e ≥ 0`, this means that `f_e` units flow in the
> implicit direction of the edge `e` chosen, and if `f_e ≤ 0`, then `|f_e|` units flow in the
> opposite direction. A *demand vector* is a vector `d ∈ ℝ^V` with `∑_{v ∈ V} d_v = 0`. For an
> edge `e = (u, v) ∈ G` we let `b_e ∈ ℝ^V` denote the demand vector of routing one unit from `u`
> to `v`, i.e., `b_e` has a `1` at `u`, `-1` at `v`, and `0` elsewhere. Define the edge-vertex
> incidence matrix `B ∈ ℝ^{E × V}` as the matrix whose rows are `b_e`. We say that a flow `f`
> routes a demand `d` if `Bᵀ f = d`.

The paper does not write out the minimum-cost flow problem. It takes it from the framework it
builds on, [chen2022maximum] (L. Chen, R. Kyng, Y. P. Liu, R. Peng, M. Probst Gutenberg,
S. Sachdeva, *Maximum Flow and Minimum-Cost Flow in Almost-Linear Time*, arXiv:2203.00671v2),
which it cites for Theorem 4.6 (page 15). There, Section 4, equation (8), an instance is a graph
with demands `d ∈ ℤ^V`, lower and upper capacities `u⁻, u⁺ ∈ ℤ^E` and costs `c ∈ ℤ^E`, and the
problem is to minimize `cᵀ f` over the flows with `Bᵀ f = d` and `u⁻_e ≤ f_e ≤ u⁺_e` for every
edge. This is why Theorem 1.1 bounds the capacities "in absolute value". The capacities
`0 ≤ f_e ≤ u_e` of the introduction (page 1) are the case `u⁻ = 0`. Lemma 4.12 of
[chen2022maximum] either computes an optimal flow or concludes that the instance admits no
feasible flow.

How the definitions read the paper:

* An instance has vertices `0, …, n - 1`, a list of edges, and a demand for each vertex. Edge
  number `j` is `edges[j]`. It has a tail, a head, a lower and an upper capacity and a cost, all
  integers. Several edges may join the same two vertices. An edge may also join a vertex to
  itself: then `b_e = 0`, and such an edge only adds its cost.
* A flow gives each edge number a real number. It is *feasible* if it routes the demands and lies
  between the capacities on every edge. A *minimum-cost flow* is a feasible flow whose cost is at
  most the cost of every feasible flow.
* The demands of a demand vector add up to `0`. The definitions do not ask this of an instance.
  When the demands do not add up to `0`, no flow routes them (summing `Bᵀ f = d` over all
  vertices gives `0 = ∑ d_v`), and the only correct answer is that there is no feasible flow.
* "Computes an (exact) minimum-cost flow": the answer is an integral minimum-cost flow, or, when
  there is no feasible flow, the statement that there is none. The flow is compared with every
  feasible real flow, as in the paper's Section 4 (page 13), where the rounding of Lemma 4.1
  turns a fractional flow into an integral one of no larger cost.

The file also fixes how instances and answers are written as lists of words for the machine of
`WordRAM/Model.lean`. Let `z` be the length of the instance in bits (`Instance.bitLength`), and
`k` the number of bits of `z` (`Instance.limbWidth`). Every integer of the instance is written in
base `2 ^ k`, so a well-formed instance is written with words less than `2 ^ k ≤ 2z`. An integer
with more than `k` bits takes several words.
-/

@[expose] public section

namespace MinCostFlow

/-- An edge of an instance: its tail, its head, its lower and upper capacities, and its cost per
unit of flow. -/
structure Edge where
  /-- The tail `u` of `e = (u, v)`. -/
  tail : ℕ
  /-- The head `v` of `e = (u, v)`. -/
  head : ℕ
  /-- The lower capacity `u⁻_e`. -/
  lower : ℤ
  /-- The upper capacity `u⁺_e`. -/
  upper : ℤ
  /-- The cost `c_e` of one unit of flow. -/
  cost : ℤ

namespace Edge

/-- The vector `b_e` at vertex `v`: `1` at the tail, `-1` at the head, and `0` elsewhere (Section
2, page 5). For an edge from a vertex to itself the two entries cancel, and `b_e = 0`. -/
def b (e : Edge) (v : ℕ) : ℝ :=
  (if v = e.tail then 1 else 0) - (if v = e.head then 1 else 0)

end Edge

/-- An instance of the minimum-cost flow problem: `n` vertices `0, …, n - 1`, the edges, and the
demand of each vertex. -/
structure Instance where
  /-- The number of vertices. -/
  n : ℕ
  /-- The edges. Edge number `j` is `edges[j]`. -/
  edges : List Edge
  /-- The demands: vertex `v` has demand `demand[v]`. -/
  demand : List ℤ

namespace Instance

/-- The number of edges. -/
def m (I : Instance) : ℕ :=
  I.edges.length

/-- Edge number `j`. -/
def edge (I : Instance) (j : Fin I.m) : Edge :=
  I.edges[j.1]'j.2

/-- The demand `d_v` of vertex `v`. -/
def d (I : Instance) (v : ℕ) : ℤ :=
  I.demand.getD v 0

/-- The instance is well formed: the ends of every edge are vertices, and every vertex has a
demand. -/
def IsValid (I : Instance) : Prop :=
  (∀ e ∈ I.edges, e.tail < I.n ∧ e.head < I.n) ∧ I.demand.length = I.n

/-- The flow `f` routes the demands: `Bᵀ f = d`, that is, `∑_e (b_e)_v f_e = d_v` at every
vertex `v` (Section 2, page 5). -/
def Routes (I : Instance) (f : Fin I.m → ℝ) : Prop :=
  ∀ v : Fin I.n, ∑ j, (I.edge j).b v * f j = I.d v

/-- The flow `f` is feasible: it routes the demands, and `u⁻_e ≤ f_e ≤ u⁺_e` on every edge. -/
def IsFeasible (I : Instance) (f : Fin I.m → ℝ) : Prop :=
  I.Routes f ∧ ∀ j, ((I.edge j).lower : ℝ) ≤ f j ∧ f j ≤ (I.edge j).upper

/-- The cost `cᵀ f = ∑_e c_e f_e` of the flow `f`. -/
def cost (I : Instance) (f : Fin I.m → ℝ) : ℝ :=
  ∑ j, ((I.edge j).cost : ℝ) * f j

/-- `f` is a minimum-cost flow: it is feasible, and its cost is at most the cost of every
feasible flow. -/
def IsMinCostFlow (I : Instance) (f : Fin I.m → ℝ) : Prop :=
  I.IsFeasible f ∧ ∀ g, I.IsFeasible g → I.cost f ≤ I.cost g

/-- The bound `U` of Theorem 1.1: the largest absolute value of a demand or a capacity (`0` if
there is none). -/
def maxCapacity (I : Instance) : ℕ :=
  ((I.edges.map fun e => max e.lower.natAbs e.upper.natAbs) ++ I.demand.map Int.natAbs).foldr
    max 0

/-- The bound `C` of Theorem 1.1: the largest absolute value of a cost (`0` if there is no
edge). -/
def maxCost (I : Instance) : ℕ :=
  (I.edges.map fun e => e.cost.natAbs).foldr max 0

end Instance

/-! ## Words -/

/-- The number of bits of the integer `x`: one for its sign, and the `Nat.log 2 |x| + 1` binary
digits of `|x|` (one digit for `0`). -/
def intBits (x : ℤ) : ℕ :=
  Nat.log 2 x.natAbs + 2

/-- The number of bits of an edge: those of its tail, its head, its capacities and its cost. -/
def Edge.bits (e : Edge) : ℕ :=
  intBits e.tail + intBits e.head + intBits e.lower + intBits e.upper + intBits e.cost

namespace Instance

/-- The length `z` of the instance in bits, the `z` of the paper's model of computation (Section
2, page 7): the bits of `n`, of `m`, of every edge and of every demand. -/
def bitLength (I : Instance) : ℕ :=
  intBits I.n + intBits I.m + (I.edges.map Edge.bits).sum + (I.demand.map intBits).sum

/-- The limb width `k = ⌊log₂ z⌋ + 1`, the number of bits of `z = I.bitLength`. It satisfies
`z < 2 ^ k ≤ 2z`. The integers of the instance and of the answer are written in base `2 ^ k`. -/
def limbWidth (I : Instance) : ℕ :=
  Nat.log 2 I.bitLength + 1

end Instance

/-- An integer written in base `2 ^ k`: `1` if it is negative and `0` otherwise, then the number
of digits of its absolute value, then those digits, least significant first and with no leading
zero digit (`Nat.digits`). Zero is written `[0, 0]`. -/
def encodeInt (k : ℕ) (z : ℤ) : List ℕ :=
  (if z < 0 then 1 else 0) :: (Nat.digits (2 ^ k) z.natAbs).length :: Nat.digits (2 ^ k) z.natAbs

/-- An edge written as words: its tail, its head, then its lower capacity, its upper capacity and
its cost as integers in base `2 ^ k`. -/
def Edge.encode (k : ℕ) (e : Edge) : List ℕ :=
  e.tail :: e.head :: (encodeInt k e.lower ++ encodeInt k e.upper ++ encodeInt k e.cost)

namespace Instance

/-- The instance written as a list of words: the limb width `k = I.limbWidth`, then `n`, `m`, the
edges in order, then the demands in order, with every integer in base `2 ^ k`. -/
def encode (I : Instance) : List ℕ :=
  I.limbWidth :: I.n :: I.m ::
    (I.edges.flatMap (Edge.encode I.limbWidth) ++ I.demand.flatMap (encodeInt I.limbWidth))

/-- `out` is a correct answer for `I`. Either `out = [0]` and no flow is feasible, or `out` is `1`
followed by the values `f_0, …, f_{m-1}` of an integral minimum-cost flow `f`, each written as an
integer in base `2 ^ I.limbWidth`. -/
def IsCorrectAnswer (I : Instance) (out : List ℕ) : Prop :=
  (out = [0] ∧ ∀ f, ¬ I.IsFeasible f) ∨
  ∃ f : Fin I.m → ℤ, I.IsMinCostFlow (fun j => (f j : ℝ)) ∧
    out = 1 :: (List.finRange I.m).flatMap fun j => encodeInt I.limbWidth (f j)

end Instance

end MinCostFlow
end

-- The file MinCostFlow/Statement/Main.lean, without its imports.
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
  The input `I.encode` starts with the number `k` of bits of `z` (`Instance.limbWidth`), and
  writes every integer of the instance in base `2 ^ k`. For a well-formed instance its words are
  less than `2z` and it has at most `2z` words, so the machine's words have `Θ(c·log z)` bits.
  This is within the paper's `O(log^{O(1)} z)`. An integer of the instance with more than `k`
  bits takes several words, and an operation on it takes a step for each word. The paper's
  fixed-point numbers of `log^{O(1)} z` bits likewise take `log^{O(1)} z` words.
* The answer writes its integers in base `2 ^ k` too, with the same `k`.
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
end

public section

namespace MinCostFlow

/-- **Theorem 1.1** (Min-cost flow, page 2). There is a deterministic algorithm that, given a
graph with `m` edges, integral demands and capacities bounded by `U` in absolute value and
integral costs bounded by `C` in absolute value, computes an exact minimum-cost flow, or reports
that no flow is feasible, in time `O(n) + m^{1+o(1)} log U log C`. -/
theorem theorem_1_1 : MinCostFlowStatement :=
  sorry

end MinCostFlow
