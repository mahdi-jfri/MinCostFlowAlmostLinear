# Deterministic almost-linear-time minimum-cost flow, in Lean

This repository contains a Lean 4 proof of Theorem 1.1 of J. van den Brand, L. Chen, R. Kyng,
Y. P. Liu, R. Peng, M. Probst Gutenberg, S. Sachdeva and A. Sidford, *A Deterministic
Almost-Linear Time Algorithm for Minimum-Cost Flow* ([arXiv:2309.16629v1](https://arxiv.org/abs/2309.16629v1)).

> **Theorem 1.1 (Min-cost flow).** There is a deterministic algorithm that given a `m`-edge graph
> with integral vertex demands and edge capacities bounded by `U` in absolute value, and integral
> edge costs bounded by `C` in absolute value, computes an (exact) minimum-cost flow in time
> `m^{1+o(1)} log U log C`.

The algorithm is one program for a word RAM, and the proof shows that it returns a correct answer
within the time bound on every instance.

```lean
theorem MinCostFlow.theorem_1_1 : MinCostFlowStatement
```

[`Comparator/Challenge.lean`](Comparator/Challenge.lean) states the theorem, and
[`Comparator/Solution.lean`](Comparator/Solution.lean) proves it. The challenge imports only
Mathlib: it repeats the three files of the statement word for word, so it can be checked without
the library.

- The theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
- The library has about 5,000 files and 1.7 million lines of Lean, excluding dependencies.

## The statement

`MinCostFlowStatement` ([`MinCostFlow/Statement/Main.lean`](MinCostFlow/Statement/Main.lean))
says: there are a program `P` with no `rand` statement, a word size constant `c`, a constant `K`
and a function `ε` tending to `0`, such that on every well-formed instance `P` halts with a
correct answer within `K·n + (m+2)^{1+ε(m)}·log(U+2)·log(C+2)` steps.

- An instance ([`MinCostFlow/Statement/Problem.lean`](MinCostFlow/Statement/Problem.lean)) has
  vertices `0, …, n - 1`, a list of edges, each with a tail, a head, a lower and an upper
  capacity and a cost, and a demand for each vertex, all integers. Parallel edges and edges from
  a vertex to itself are allowed. A flow routes the demands when `Bᵀ f = d`, with `B` the
  edge-vertex incidence matrix of the paper (page 5).
- A correct answer is an integral flow whose cost is at most that of every feasible real flow, or
  `[0]` when no flow is feasible.
- `U` and `C` are the largest absolute values of the capacities and costs. Writing `m + 2`,
  `U + 2` and `C + 2` for `m`, `U` and `C` changes the bound by at most a constant factor when
  `m, U, C ≥ 2`.
- The term `K·n` is not in the printed bound. A program must read the `n` demands, so the printed
  bound cannot hold on graphs with many more vertices than edges. When `n ≤ m + 1` the term is
  absorbed into `(m+2)^{1+ε(m)}`.

The docstrings of the two files give every reading of the paper's words.
[`Checks/StatementExamples.lean`](Checks/StatementExamples.lean) checks the definitions on small
instances.

## The machine model

The paper does not fix a machine model beyond fixed-point arithmetic on words of
`O(log^{O(1)} z)` bits (Section 2, page 7). The statement fixes one: the deterministic part of
the randomized word RAM of the package [WordRAM](https://github.com/mahdi-jfri/WordRam)
(`WordRAM/Model.lean`, pinned in [`lakefile.toml`](lakefile.toml)). The statement uses only that
file: `Program`, `RunsTo`, `wordSize` and `Program.IsDeterministic`. Words have `c·log(N)` bits,
where `N` is the input length plus its largest number, and every operation costs one step. The
input writes every integer of the instance in base `2^k`, where `k` is the number of bits of the
length `z` of the instance in bits, and the answer does the same. So the input has at most `2z`
words, each less than `2z`, and words have `Θ(c·log z)` bits. This is within the paper's
`O(log^{O(1)} z)`. An integer with more than `k` bits takes several words, and so does each of
the paper's fixed-point numbers. The library implements their arithmetic on words. The package also provides the program logic, contracts and linking that the proofs use.

## Cited results

The library proves every result of another paper that the paper cites, or the case of it that
the paper uses.

- Theorem 2.4 of Chuzhoy, Gao, Li, Nanongkai, Peng and Saranurak, arXiv:1910.08025v2 (the explicit
  expander, cited for Theorem 8.4): `MinCostFlow.ExplicitExpander.explicitExpander`.
- Theorem 1 of Abraham and Neiman, SIAM J. Comput. 2019 (the low-stretch spanning tree, cited for
  Theorem 2.2): `MinCostFlow.LowStretch.lowStretchSpanningTree_lsst`.
- Corollary 6.1 of Chuzhoy et al. (the expander decomposition, cited for Theorems 8.5 and B.1), in
  the case the paper uses: `MinCostFlow.ExpanderDecomp.expanderDecompositionUsed_holds`.
- Theorem 3.9 of Chuzhoy and Saranurak, arXiv:2009.08479v1 (decremental expander paths, cited for
  Theorem 8.6). The library does not prove this theorem. It proves the static sparsifier of
  Theorem 8.1 directly, from a deterministic hierarchy of embedded matchings
  (`MinCostFlow.HierPaths.hierPathDSExistsFrom`).
- The results of Chen, Kyng, Liu, Peng, Probst Gutenberg and Sachdeva, arXiv:2203.00671v2, that
  the paper uses: Lemmas 4.1, 4.4, 4.7 to 4.10, 4.12 and C.1, and the interior point method of
  its Section 4 in the form of Theorem 4.6 of the paper.

The statements of the cited results, as their sources state them, are in
[`MinCostFlow/Statement/Cited/`](MinCostFlow/Statement/Cited), and
[`Checks/CitedExamples.lean`](Checks/CitedExamples.lean) checks their notions on small graphs.

## Where the proof departs from the paper

The statement is the paper's, read as above. Some steps of the proof differ from the paper,
because the printed argument has a gap there. None of the changes affects Theorem 1.1.

- **Theorem 4.6** (page 15). The algorithm needs the optimal cost, which is found by binary
  search. A run with a guess below the optimum can produce instances without hidden stability,
  and on those the data structure of Theorem 5.1 has no time bound. Here an update may answer
  "fail", but only when the instance so far is not hidden stable. The binary search counts a
  failure as a guess below the optimum.
- **Theorem 5.1, the number of rebuilds** (page 30). The count uses item 1 of Lemma 5.17 for a
  branch that `Shift(i)` has just replaced, and the lemma does not give it there. Here `Shift(i)`
  also restarts the dynamic spanner of the new branch.
- **Lemma 5.17, the degrees of the spanner input** (pages 23 and 24). The proof applies Theorem 8.2
  to the core graphs, whose degrees nothing bounds. Here Theorem 8.2 runs on a graph of bundles
  of at most `k` consecutive ends, and its output is mapped back. The time of Lemma 5.17 becomes
  `Õ(m k² γ_r)`, with a recourse factor that does not depend on `k`, and Theorem 5.1 keeps its form.
- **Definition 5.8 and Algorithm 1, the order of the ends.** Without an order of the ends from the
  level below, one vertex split can cut every bundle. Here each graph of the chain carries a
  rotation system.
- **Theorems 8.6 and B.1.** Their parameters do not follow from the cited results as printed. The
  library proves the parameters that do follow, which change only the `m^{o(1)}` factors.
- **Chen et al., Appendix C.** The zero flow is not always strictly `C`-optimal, so the scaling
  starts at `C + 1`.

## Layout

| Path | Contents |
| --- | --- |
| `MinCostFlow/Statement` | the statement of Theorem 1.1, and the statements of the cited results |
| `MinCostFlow/Basic` | graphs, embeddings, flows, updates and encoding sizes |
| `MinCostFlow/IPM`, `Scaling`, `Rounding` | the interior point method, the scaling of costs and capacities, and the rounding of the final flow |
| `MinCostFlow/Num`, `Machine` | fixed-point numbers on words, and programs for the machine |
| `MinCostFlow/Chain`, `MinRatio`, `Game` | the data structure for min-ratio cycles (Sections 5 and 6) |
| `MinCostFlow/LSF`, `LowStretch`, `LinkCut` | dynamic low-stretch forests, low-stretch spanning trees and link-cut trees |
| `MinCostFlow/Bundle`, `SparseCore`, `LastLevelProgram` | the core graphs, their bundles and the last level of the chain |
| `MinCostFlow/Spanner`, `DynSpanner` | the static and dynamic spanners (Section 8) |
| `MinCostFlow/Expander`, `ExpanderDecomp`, `ExplicitExpander`, `HierPaths` | expanders, the expander decomposition, the explicit expander and the hierarchy of embedded matchings |
| `MinCostFlow/Narrow`, `NarrowProg` | the reduction of Theorem 1.1 to the inner solver on numbers of several words: reading the input, the checks, the scaling of capacities and costs, and the answer |
| `MinCostFlow/NarrowTop` | the program of Theorem 1.1 and the proof of its bounds |
| `MinCostFlow/Final` | the inner solver and the proof of its bounds |
| `Checks` | the axiom check, and checks of the definitions on small examples |
| `Comparator/Challenge.lean` | the statement, for comparator, with only Mathlib imports |
| `Comparator/Solution.lean` | the theorem |

## Build

The build uses Lean `v4.35.0-rc3` and Mathlib `b63f6e8`. To download Mathlib's prebuilt files
and build, run from the repository root:

```sh
ulimit -s 1048576
export RUST_MIN_STACK=1073741824
lake exe cache get
lake build
```

The build prints one expected `sorry` warning, from `Comparator/Challenge.lean`. `tools/check`
checks that the root file `MinCostFlow.lean` imports every file of the library and that no
forbidden word (`sorry`, `native_decide`, `axiom` and a few others) appears in it. Then it builds
the library, the checks, the challenge and the solution. `Checks/Axioms.lean` fails unless every
declaration of the library and of WordRAM uses only `propext`, `Classical.choice` and
`Quot.sound`. Last, it checks that `Comparator/Challenge.lean` is the file that
`tools/gen_challenge.py` writes from `WordRAM/Model.lean`, `MinCostFlow/Statement/Problem.lean`
and `MinCostFlow/Statement/Main.lean`.

[`comparator.json`](comparator.json) sets up [comparator](https://github.com/leanprover/comparator)
for `Comparator/Challenge.lean` and `Comparator/Solution.lean`. Comparator checks that every
definition the statement uses is the same in the challenge and in the library.

Licensed under [Apache-2.0](LICENSE).
