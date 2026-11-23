module

public import MinCostFlow.ExpanderDecomp.Embedding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Interface for the static matching player (`RouteOrCut`)

This file fixes the output type and specification of the static matching player (the router
`RouteOrCut`), so that `OneShot` and `Core` are
proved against it, and the router implementation proves separately that it meets
`IsMatchingPlayer`.

The host is a `Graph` `G` restricted to a vertex set `X ⊆ Finset.range G.n` (loopless on
`G.inside X`, maximum degree at most `Δ ≥ 1`, `|X| < 2 ^ L`), with `k` pairwise disjoint terminal
pairs `(A_i, B_i)` inside `X` satisfying `|A_i| ≤ |B_i|`, sparsity denominator `b ≥ 2`, and total
deficit budget `z`.

With the exact router parameters:
* `routePathLen Δ b L = 32 * Δ * b * L` (`d`),
* `routeBatchH Δ b L = 16 * b * Δ * (d + 1)` (`H_batch`),
* `routeCong Δ b L = routeBatchH Δ b L * L` (`R`),

a call either returns:
* `RouteResult.matched matchings emb`: partial matchings `M_i ⊆ A_i × B_i` with total deficit
  `∑ (|A_i| - |M_i|) ≤ z` and an embedding `emb` of `⟨G.n, matchings.flatten⟩` into `G` on `X`
  using paths of length at most `d` and edge congestion at most `R`; or
* `RouteResult.cut U`: a subset `U ⊆ X` with `b * G.cutIn X U ≤ min |U| |X \ U|` and
  `z + 1 ≤ 2 * |U|`, `z + 1 ≤ 2 * |X \ U|`.

The cost function `routeCost` satisfies the step-count bound:
`routeCost ≤ C * (k * (|X| + e_X + 1) * (d + 1) * R + 1)`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- Step parameter `h = 16 Δ b` of the router. -/
def routeH (Δ b : ℕ) : ℕ :=
  16 * Δ * b

/-- Maximum path length `d = 32 Δ b L` of the router. -/
def routePathLen (Δ b L : ℕ) : ℕ :=
  32 * Δ * b * L

/-- Batch-halving factor `H_batch = 16 b Δ (d + 1)` of the router. -/
def routeBatchH (Δ b L : ℕ) : ℕ :=
  16 * b * Δ * (routePathLen Δ b L + 1)

/-- Maximum edge congestion `R = H_batch · L` of the router. -/
def routeCong (Δ b L : ℕ) : ℕ :=
  routeBatchH Δ b L * L

/-- Terminal pairs `(A_i, B_i)` inside `X` are valid when every `A_i, B_i ⊆ X`, `|A_i| ≤ |B_i|`,
and all `2k` terminal sets `A_1, B_1, …, A_k, B_k` are pairwise disjoint. -/
def ValidTerminalPairs (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) : Prop :=
  (∀ p ∈ pairs, p.1 ⊆ X ∧ p.2 ⊆ X ∧ p.1.card ≤ p.2.card) ∧
    (pairs.flatMap fun p => [p.1, p.2]).Pairwise Disjoint

/-- Output of a static matching player call (`RouteOrCut`). -/
inductive RouteResult where
  /-- Partial matchings `matchings[i] ⊆ A_i × B_i` and an embedding of their flattened witness
  graph `⟨G.n, matchings.flatten⟩` into the host `G` on `X`. -/
  | matched (matchings : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ)
  /-- A sparse cut `U ⊆ X` in the original host `G[X]`. -/
  | cut (U : Finset ℕ)

/-- Type of a static matching player function: takes `(G, X, pairs, Δ, L, b, z)`. -/
abbrev RouterFn :=
  Graph → Finset ℕ → List (Finset ℕ × Finset ℕ) → ℕ → ℕ → ℕ → ℕ → RouteResult

/-- Type of the operation-count function for a static matching player. -/
abbrev RouterCostFn :=
  Graph → Finset ℕ → List (Finset ℕ × Finset ℕ) → ℕ → ℕ → ℕ → ℕ → ℕ

/-- The matched outcome guarantee of Lemma 1. -/
def RouteMatchedSpec (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    (Δ L b z : ℕ) (matchings : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ) : Prop :=
  matchings.length = pairs.length ∧
    (∀ i (hi : i < pairs.length),
      let M := matchings.getD i []
      let p := pairs[i]'hi
      (∀ e ∈ M, e.1 ∈ p.1 ∧ e.2 ∈ p.2) ∧
        (M.map Prod.fst).Nodup ∧ (M.map Prod.snd).Nodup) ∧
    (List.zipWith (fun p M => p.1.card - M.length) pairs matchings).sum ≤ z ∧
    IsEmbeddingOn (Graph.mk G.n matchings.flatten) G X emb ∧
    (∀ j < matchings.flatten.length, (emb j).length ≤ routePathLen Δ b L) ∧
    (∀ i < G.m, congestion (Graph.mk G.n matchings.flatten) emb i ≤ routeCong Δ b L)

/-- The cut outcome guarantee of the router. -/
def RouteCutSpec (G : Graph) (X : Finset ℕ) (b z : ℕ) (U : Finset ℕ) : Prop :=
  U ⊆ X ∧
    b * G.cutIn X U ≤ min U.card (X \ U).card ∧
    z + 1 ≤ 2 * U.card ∧
    z + 1 ≤ 2 * (X \ U).card

/-- Full outcome specification of the router for a single call. -/
def RouteSpec (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    (Δ L b z : ℕ) : RouteResult → Prop
  | .matched matchings emb => RouteMatchedSpec G X pairs Δ L b z matchings emb
  | .cut U => RouteCutSpec G X b z U

/-- Specification of a static matching player (`route`, `routeCost`) matching the router
specification and its running-time bound. -/
structure IsMatchingPlayer (route : RouterFn) (routeCost : RouterCostFn) : Prop where
  /-- Correctness of every valid call. -/
  spec : ∀ (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (Δ L b z : ℕ),
    X ⊆ Finset.range G.n →
    (∀ e ∈ G.inside X, e.1 ≠ e.2) →
    1 ≤ Δ →
    (∀ v ∈ X, G.degIn X v ≤ Δ) →
    1 ≤ L →
    X.card < 2 ^ L →
    2 ≤ b →
    ValidTerminalPairs X pairs →
    RouteSpec G X pairs Δ L b z (route G X pairs Δ L b z)
  /-- Operation-count bound `C * (k * (|X| + e_X + 1) * (d + 1) * R + 1)`. -/
  cost_bound : ∃ C : ℕ,
    ∀ (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (Δ L b z : ℕ),
      X ⊆ Finset.range G.n →
      (∀ e ∈ G.inside X, e.1 ≠ e.2) →
      1 ≤ Δ →
      (∀ v ∈ X, G.degIn X v ≤ Δ) →
      1 ≤ L →
      X.card < 2 ^ L →
      2 ≤ b →
      ValidTerminalPairs X pairs →
      routeCost G X pairs Δ L b z ≤
        C * (pairs.length * (X.card + (G.inside X).length + 1) *
          (routePathLen Δ b L + 1) * routeCong Δ b L + 1)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- Congestion bound: `R ≤ 528 Δ² b² L²` whenever `Δ, b, L ≥ 1`. -/
theorem routeCong_le {Δ b L : ℕ} (hΔ : 1 ≤ Δ) (hb : 1 ≤ b) (hL : 1 ≤ L) :
    routeCong Δ b L ≤ 528 * Δ ^ 2 * b ^ 2 * L ^ 2 := by
  unfold routeCong routeBatchH routePathLen
  have h1 : 1 ≤ Δ * b * L := by
    calc 1 = 1 * 1 * 1 := by norm_num
      _ ≤ Δ * b * L := Nat.mul_le_mul (Nat.mul_le_mul hΔ hb) hL
  have h2 : 32 * Δ * b * L + 1 ≤ 33 * (Δ * b * L) := by
    have heq : 32 * Δ * b * L = 32 * (Δ * b * L) := by ring
    omega
  calc 16 * b * Δ * (32 * Δ * b * L + 1) * L
      ≤ 16 * b * Δ * (33 * (Δ * b * L)) * L :=
        Nat.mul_le_mul_right L (Nat.mul_le_mul_left _ h2)
    _ = 528 * Δ ^ 2 * b ^ 2 * L ^ 2 := by ring

/-- In a matched outcome, each partial matching `M_i` has at most `|A_i|` edges. -/
theorem RouteMatchedSpec.length_le_fst_card {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {Δ L b z : ℕ}
    {matchings : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (h : RouteMatchedSpec G X pairs Δ L b z matchings emb) {i : ℕ} (hi : i < pairs.length) :
    (matchings.getD i []).length ≤ (pairs[i]'hi).1.card := by
  have hi_spec := h.2.1 i hi
  dsimp only at hi_spec
  set M := matchings.getD i []
  calc M.length = (M.map Prod.fst).length := by simp
    _ = (M.map Prod.fst).toFinset.card := (List.toFinset_card_of_nodup hi_spec.2.1).symm
    _ ≤ (pairs[i]'hi).1.card := by
      apply Finset.card_le_card
      intro u hu
      rw [List.mem_toFinset, List.mem_map] at hu
      obtain ⟨e, he, rfl⟩ := hu
      exact (hi_spec.1 e he).1

/-- In `ValidTerminalPairs`, the two sets of each pair are disjoint. -/
theorem ValidTerminalPairs.disjoint_pair {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hp : ValidTerminalPairs X pairs) {p : Finset ℕ × Finset ℕ} (hmem : p ∈ pairs) :
    Disjoint p.1 p.2 := by
  have hpw := hp.2
  clear hp
  induction pairs with
  | nil => simp at hmem
  | cons q rest ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.pairwise_cons] at hpw
    rcases List.mem_cons.mp hmem with rfl | hrest
    · exact hpw.1 p.2 List.mem_cons_self
    · exact ih hrest hpw.2.2

end MinCostFlow.ExpanderDecomp
