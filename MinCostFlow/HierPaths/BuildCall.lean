module

public import MinCostFlow.HierPaths.FullRoute
import Mathlib.Tactic.Linarith

/-!
# One full-routing call, with bounds at a fixed denominator

The child construction and the sibling connectors call the full router (`lemma1Route`) many
times in one host `G[X]`. The denominator `b` at which a call stops depends on the call, but every
one is at most `max(2, 2/β)` (`lemma_1`). To state one length bound `d_X` and one congestion bound
`R_X` for all calls, fix a natural number `b̂ ≥ max(2, 2/β)` and use the router's bounds at `b̂`:
they are monotone in `b`.

Main result: `call_facts`, which collects for one call the matched outcome, the full matchings,
the embedding, and the length, congestion and cost bounds at `b̂`.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The router's path length bound is monotone in `b`. -/
theorem routePathLen_mono {Δ L b b' : ℕ} (h : b ≤ b') : routePathLen Δ b L ≤ routePathLen Δ b' L := by
  unfold routePathLen
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)

/-- The router's congestion bound is monotone in `b`. -/
theorem routeCong_mono {Δ L b b' : ℕ} (h : b ≤ b') : routeCong Δ b L ≤ routeCong Δ b' L := by
  unfold routeCong routeBatchH
  have h1 := routePathLen_mono (Δ := Δ) (L := L) h
  apply Nat.mul_le_mul_right
  exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)) (by omega)

/-- The cost bound of one call is monotone in `b`. -/
theorem routeBound_mono {C : ℕ} {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {Δ L b b' : ℕ} (h : b ≤ b') :
    routeBound C G X pairs Δ L b ≤ routeBound C G X pairs Δ L b' := by
  unfold routeBound
  have h1 := routePathLen_mono (Δ := Δ) (L := L) h
  have h2 := routeCong_mono (Δ := Δ) (L := L) h
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) h2

/-- **One full-routing call.** Under the hypotheses of `lemma_1` and for a natural number
`b̂ ≥ max(2, 2/β)`, the call `lemma1Route` returns matchings `M` and an embedding `emb` such that:
the router's specification holds at deficit `0`; every matching `M_i` has `|A_i|` edges; the
embedding of the flattened matchings into `G` on `X` uses walks of at most `routePathLen Δ b̂ L`
edges with congestion at most `routeCong Δ b̂ L`; and the total cost is at most twice the cost
bound at `b̂`. -/
theorem call_facts {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {C : ℕ}
    {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)} {Δ L : ℕ}
    (hC : ∀ b, 2 ≤ b → routeCost G X pairs Δ L b 0 ≤ routeBound C G X pairs Δ L b)
    (hpre : RouterPre G X pairs Δ L) (hk : 1 ≤ pairs.length) {β : ℝ} (hβ : 0 < β)
    (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ} (hbh : max 2 (2 / β) ≤ (bh : ℝ)) :
    ∃ M emb b', lemma1Route route G X pairs Δ L = (.matched M emb, b') ∧
      RouteMatchedSpec G X pairs Δ L b' 0 M emb ∧
      (∀ i (hi : i < pairs.length), (M.getD i []).length = (pairs[i]'hi).1.card) ∧
      b' ≤ bh ∧
      IsEmbeddingOn (Graph.mk G.n M.flatten) G X emb ∧
      (∀ j < M.flatten.length, (emb j).length ≤ routePathLen Δ bh L) ∧
      (∀ i < G.m, congestion (Graph.mk G.n M.flatten) emb i ≤ routeCong Δ bh L) ∧
      fullRouteCost route routeCost G X pairs Δ L X.card 2 ≤
        2 * routeBound C G X pairs Δ L bh := by
  obtain ⟨⟨M, emb, hr, hs⟩, _, h22, _, _, hcost⟩ := lemma_1 hrouter hC hpre hk hβ hexp
  have hb' : (lemma1Route route G X pairs Δ L).2 ≤ bh := by
    have : ((lemma1Route route G X pairs Δ L).2 : ℝ) ≤ bh := le_trans h22 hbh
    exact_mod_cast this
  refine ⟨M, emb, (lemma1Route route G X pairs Δ L).2, ?_, hs, fullRoute_full hs, hb', hs.2.2.2.1,
    fun j hj => le_trans (hs.2.2.2.2.1 j hj) (routePathLen_mono hb'),
    fun i hi => le_trans (hs.2.2.2.2.2 i hi) (routeCong_mono hb'),
    le_trans hcost (Nat.mul_le_mul_left _ (routeBound_mono hb'))⟩
  rw [← hr]

end MinCostFlow.HierPaths
