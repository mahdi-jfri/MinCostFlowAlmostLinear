module

public import MinCostFlow.Basic.Embedding
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Static sparsifier interface for the dynamic spanner (Theorem 8.1)

This file specifies the static sparsification procedure `Sparsify(H', J, Π_{J → H'})` of Theorem 8.1
(*A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow*, arXiv:2309.16629v1,
page 39) on `MGraph` and `Embedding`, taken as a parameter by the dynamic spanner algorithm of
Theorem 8.2.

> **Theorem 8.1 (page 39).** Given unweighted, undirected graphs `H'` and `J` with `V(J) ⊆ V(H')`
> and an embedding `Π_{J → H'}` from `J` into `H'`, `Sparsify(H', J, Π_{J → H'})` returns a
> sparsifier `J̃ ⊆ J` with an embedding `Π_{J → J̃}` from `J` to `J̃` such that:
> 1. `vcong(Π_{J → H'} ∘ Π_{J → J̃}) ≤ γ_c · length(Π_{J → H'}) · (vcong(Π_{J → H'}) + Δ_max(J))`,
> 2. `length(Π_{J → H'} ∘ Π_{J → J̃}) ≤ γ_ℓ · length(Π_{J → H'})`, and
> 3. `|E(J̃)| = Õ(|V(J)| γ_ℓ)`,
> running in time `Õ(|E(J)| γ_ℓ² length(Π_{J → H'}))`.

Faithful reading notes:
* The `Õ(·)` factors in item 3 and the running time are written explicitly as
  `K * (1 + log(|V(J)| + |E(J)| + 2)) ^ p`, which is at least `K ≥ 0` on all graphs.
* The running-time bound includes `|V(J)|` alongside `|E(J)| γ_ℓ² length(Π_{J → H'})` so that
  empty or sparse graphs with isolated vertices have a realistic operation budget.
* When `J` has edges, the precondition `1 ≤ length(Π_{J → H'})` excludes degenerate empty walks on
  self-loops, for which item 1's right-hand side `0` cannot bound positive vertex congestion.
-/

@[expose] public section

namespace MinCostFlow.DynSpanner

/-- Result returned by a static sparsification call `Sparsify(H', J, Π_{J → H'})`
(Theorem 8.1, page 39): the subgraph `Jtilde`, the embedding `emb : Π_{J → J̃}`, and the
operation count `cost`. -/
structure SparsifyOut where
  /-- The sparsified subgraph `J̃ ⊆ J`. -/
  Jtilde : MGraph
  /-- The embedding `Π_{J → J̃}`. -/
  emb : Embedding
  /-- The operation count of the call. -/
  cost : ℕ

/-- Parameters capturing the approximation and polylogarithmic factors of Theorem 8.1 (page 39):
congestion factor `γ_c ≥ 1`, length factor `γ_ℓ ≥ 1`, sparsity factor `K_s · (1 + log(·))^{p_s}`,
and time factor `K_t · (1 + log(·))^{p_t}`. -/
structure SparsifyParams where
  /-- Vertex-congestion factor `γ_c`. -/
  γ_c : ℝ
  /-- Embedding-length factor `γ_ℓ`. -/
  γ_ℓ : ℝ
  /-- Leading constant in the `Õ(|V(J)| γ_ℓ)` sparsity bound. -/
  K_s : ℝ
  /-- Polylogarithmic exponent in the sparsity bound. -/
  p_s : ℕ
  /-- Leading constant in the `Õ((|V(J)| + |E(J)| γ_ℓ² length(Π_{J → H'})) · γ_t)` runtime bound. -/
  K_t : ℝ
  /-- Polylogarithmic exponent in the runtime bound. -/
  p_t : ℕ
  /-- Query/fallback runtime overhead factor `γ_t ≥ 1` (defaults to `1` when Theorem 8.6 holds
  at `exp(O(log^{7/8} m))`; equals `γ_query` for concrete fallback `PathDS`). -/
  γ_t : ℝ := 1
  hγ_c : 1 ≤ γ_c
  hγ_ℓ : 1 ≤ γ_ℓ
  hK_s : 0 ≤ K_s
  hK_t : 0 ≤ K_t
  hγ_t : 1 ≤ γ_t := by norm_num

/-- Specification of `Sparsify(H', J, Π_{J → H'})` (Theorem 8.1, page 39) on `MGraph` for graphs
`J` with `J.m ≤ mMax` (`γ_t = 1` specialization for un-parametrized consumers). -/
def SparsifySpec (mMax : ℕ) (P : SparsifyParams)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) : Prop :=
  ∀ (H' J : MGraph) (embJH : Embedding),
    H'.IsValid → J.IsValid → J.m ≤ mMax →
    (J.E.Nonempty → 1 ≤ embJH.length J) →
    embJH.IsEmbedding J H' →
    let out := sparsify H' J embJH
    J.IsSubgraph out.Jtilde ∧
    out.emb.IsEmbedding J out.Jtilde ∧
    (Embedding.comp embJH out.emb).vcong J H' (fun _ => 1) ≤
      P.γ_c * (embJH.length J : ℝ) *
        (embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ)) ∧
    ((Embedding.comp embJH out.emb).length J : ℝ) ≤
      P.γ_ℓ * (embJH.length J : ℝ) ∧
    (out.Jtilde.m : ℝ) ≤
      P.K_s * (J.n : ℝ) * P.γ_ℓ * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s ∧
    (out.cost : ℝ) ≤
      P.K_t * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_t

/-- Runtime-parametrized specification of `Sparsify(H', J, Π_{J → H'})` carrying the explicit
multiplicative `γ_t ≥ 1` overhead factor in the runtime bound
`K_t · γ_t · (|V(J)| + |E(J)| · γ_ℓ² · length(Π_{J → H'})) · log^{p_t}`. -/
def SparsifySpecWithTime (mMax : ℕ) (P : SparsifyParams)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) : Prop :=
  ∀ (H' J : MGraph) (embJH : Embedding),
    H'.IsValid → J.IsValid → J.m ≤ mMax →
    (J.E.Nonempty → 1 ≤ embJH.length J) →
    embJH.IsEmbedding J H' →
    let out := sparsify H' J embJH
    J.IsSubgraph out.Jtilde ∧
    out.emb.IsEmbedding J out.Jtilde ∧
    (Embedding.comp embJH out.emb).vcong J H' (fun _ => 1) ≤
      P.γ_c * (embJH.length J : ℝ) *
        (embJH.vcong J H' (fun _ => 1) + (J.maxDeg : ℝ)) ∧
    ((Embedding.comp embJH out.emb).length J : ℝ) ≤
      P.γ_ℓ * (embJH.length J : ℝ) ∧
    (out.Jtilde.m : ℝ) ≤
      P.K_s * (J.n : ℝ) * P.γ_ℓ * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s ∧
    (out.cost : ℝ) ≤
      P.K_t * P.γ_t * ((J.n : ℝ) + (J.m : ℝ) * P.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_t

/-- Absorbing `γ_t` into `K_t` converts between `SparsifySpecWithTime` and `SparsifySpec`. -/
def SparsifyParams.absorbTime (P : SparsifyParams) : SparsifyParams where
  γ_c := P.γ_c
  γ_ℓ := P.γ_ℓ
  K_s := P.K_s
  p_s := P.p_s
  K_t := P.K_t * P.γ_t
  p_t := P.p_t
  γ_t := 1
  hγ_c := P.hγ_c
  hγ_ℓ := P.hγ_ℓ
  hK_s := P.hK_s
  hK_t := mul_nonneg P.hK_t (le_trans zero_le_one P.hγ_t)
  hγ_t := le_rfl

lemma sparsifySpecWithTime_iff_absorb {mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut} :
    SparsifySpecWithTime mMax P sparsify ↔ SparsifySpec mMax P.absorbTime sparsify := by
  simp only [SparsifySpecWithTime, SparsifySpec, SparsifyParams.absorbTime, mul_assoc]

lemma sparsifySpecWithTime_iff_of_one {mMax : ℕ} {P : SparsifyParams} (h1 : P.γ_t = 1)
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut} :
    SparsifySpecWithTime mMax P sparsify ↔ SparsifySpec mMax P sparsify := by
  simp only [SparsifySpecWithTime, SparsifySpec, h1, mul_one]

end MinCostFlow.DynSpanner
