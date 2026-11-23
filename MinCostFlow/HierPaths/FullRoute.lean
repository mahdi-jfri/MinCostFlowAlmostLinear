module

public import MinCostFlow.ExpanderDecomp.MatchingPlayer
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Full routing in an expanding host

Full routing (`lemma_1`): in a host `G[X]` on `p` vertices with edge expansion `β > 0` (by
cardinality), call the static router (`ExpanderDecomp.IsMatchingPlayer`) with deficit `z = 0`,
starting at `b = 2` and doubling `b` after each cut. The loop returns a full matching for every
requested pair.

Why. With `z = 0`, a returned cut `U` has both sides nonempty and `b · cut(U) ≤ min(|U|, |X \ U|)`.
Expansion gives `β · min(|U|, |X \ U|) ≤ cut(U)`, so `b β ≤ 1`. The cut has an edge, since
`β > 0` and the cut is an integer, so also `2b ≤ p`. Hence a cut at `b` needs `b ≤ 1/β` and
`b ≤ p/2`: the last `b` is `2` or twice a `b` that was cut, so it is at most `max(2, 2/β)` and at
most `max(2, p)`. Once `2b > p` no cut is possible, so `p` doublings suffice. The cost bound of one
call (`ExpanderDecomp.IsMatchingPlayer.cost_bound`) at least doubles when `b` doubles, so the costs
of all calls sum to at most twice the bound of the last call.

We bound the last `b` by `max(2, 2/β)` and `max(2, p)`, and derive from these the weaker
bounds `max(2, 4/β)` and `4p`.

The cost claim needs at least one terminal pair: the bound of a call has an additive term `C` that
does not grow with `b`, so with no pairs `j` calls cost up to `j · C`.

Main results: `cut_forces` (a cut needs `b β ≤ 1` and `2b ≤ p`), `two_mul_routeBound_le` (the
bound of one call doubles with `b`), `fullRoute_invariant` (the loop, by induction on the fuel),
`lemma_1`, `fullRoute_full` (deficit `0` gives full matchings), and `exists_lemma_1`, which takes
the constant `C` from `IsMatchingPlayer.cost_bound`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The full-routing loop, with `fuel` further doublings allowed: call the router at `b` with
`z = 0`; return the matching and `b` if it matches, and otherwise go on at `2b`. The last call
(fuel `0`) returns whatever the router returns. -/
def fullRoute (route : RouterFn) (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    (Δ L : ℕ) : ℕ → ℕ → RouteResult × ℕ
  | 0, b => (route G X pairs Δ L b 0, b)
  | fuel + 1, b =>
    match route G X pairs Δ L b 0 with
    | .matched M emb => (.matched M emb, b)
    | .cut _ => fullRoute route G X pairs Δ L fuel (2 * b)

/-- The full-routing loop from `b = 2` with `|X|` doublings allowed. -/
def lemma1Route (route : RouterFn) (G : Graph) (X : Finset ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) (Δ L : ℕ) : RouteResult × ℕ :=
  fullRoute route G X pairs Δ L X.card 2

/-- The total cost of the calls made by `fullRoute`. -/
def fullRouteCost (route : RouterFn) (routeCost : RouterCostFn) (G : Graph) (X : Finset ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) (Δ L : ℕ) : ℕ → ℕ → ℕ
  | 0, b => routeCost G X pairs Δ L b 0
  | fuel + 1, b =>
    match route G X pairs Δ L b 0 with
    | .matched _ _ => routeCost G X pairs Δ L b 0
    | .cut _ => routeCost G X pairs Δ L b 0 + fullRouteCost route routeCost G X pairs Δ L fuel (2 * b)

/-- The preconditions of `IsMatchingPlayer.spec` other than `2 ≤ b`. -/
def RouterPre (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (Δ L : ℕ) : Prop :=
  X ⊆ Finset.range G.n ∧ (∀ e ∈ G.inside X, e.1 ≠ e.2) ∧ 1 ≤ Δ ∧
    (∀ v ∈ X, G.degIn X v ≤ Δ) ∧ 1 ≤ L ∧ X.card < 2 ^ L ∧ ValidTerminalPairs X pairs

/-- The cost bound of one router call at `b`, with the constant `C` of
`IsMatchingPlayer.cost_bound`. -/
def routeBound (C : ℕ) (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    (Δ L b : ℕ) : ℕ :=
  C * (pairs.length * (X.card + (G.inside X).length + 1) * (routePathLen Δ b L + 1) *
    routeCong Δ b L + 1)

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- **A cut needs a small `b`.** With `z = 0`, a cut returned at `b` in a host of expansion
`β > 0` forces `b β ≤ 1` and `2b ≤ |X|`. -/
theorem cut_forces {G : Graph} {X : Finset ℕ} {β : ℝ} (hβ : 0 < β)
    (hexp : G.IsExpansionExpanderOn X β) {b : ℕ} {U : Finset ℕ} (hU : RouteCutSpec G X b 0 U) :
    (b : ℝ) * β ≤ 1 ∧ 2 * b ≤ X.card := by
  obtain ⟨hUX, hsp, h1, h2⟩ := hU
  have hne : U.Nonempty := Finset.card_pos.mp (by omega)
  have hne' : (X \ U).Nonempty := Finset.card_pos.mp (by omega)
  have hneX : U ≠ X := by
    intro h
    rw [h, Finset.sdiff_self] at hne'
    exact Finset.not_nonempty_empty hne'
  have he := hexp U hUX hne hneX
  set mn := min U.card (X \ U).card
  have hmn : 1 ≤ mn := le_min (Finset.card_pos.mpr hne) (Finset.card_pos.mpr hne')
  have hmnr : (1 : ℝ) ≤ (mn : ℝ) := by exact_mod_cast hmn
  have hcast : min (U.card : ℝ) ((X \ U).card : ℝ) = (mn : ℝ) := by
    simp [mn, Nat.cast_min]
  rw [hcast] at he
  have hcut_pos : (0 : ℝ) < G.cutIn X U := lt_of_lt_of_le (by positivity) he
  have hcut1 : 1 ≤ G.cutIn X U := by exact_mod_cast hcut_pos
  have hsp' : (b : ℝ) * G.cutIn X U ≤ mn := by exact_mod_cast hsp
  have hcard : U.card + (X \ U).card = X.card := by
    rw [Finset.card_sdiff_of_subset hUX]
    have := Finset.card_le_card hUX
    omega
  refine ⟨?_, ?_⟩
  · have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    have : (b : ℝ) * β * mn ≤ 1 * mn := by
      calc (b : ℝ) * β * mn = b * (β * mn) := by ring
        _ ≤ b * G.cutIn X U := mul_le_mul_of_nonneg_left he hb0
        _ ≤ mn := hsp'
        _ = 1 * mn := by ring
    exact le_of_mul_le_mul_right this (by linarith)
  · have h3 : b ≤ mn := by
      calc b = b * 1 := by ring
        _ ≤ b * G.cutIn X U := Nat.mul_le_mul_left _ hcut1
        _ ≤ mn := hsp
    have h4 : mn ≤ U.card := min_le_left _ _
    have h5 : mn ≤ (X \ U).card := min_le_right _ _
    omega

/-- The bound of one call at least doubles when `b` doubles, when there is a terminal pair. -/
theorem two_mul_routeBound_le {C : ℕ} {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {Δ L b : ℕ} (hk : 1 ≤ pairs.length) (hΔ : 1 ≤ Δ)
    (hL : 1 ≤ L) (hb : 1 ≤ b) :
    2 * routeBound C G X pairs Δ L b ≤ routeBound C G X pairs Δ L (2 * b) := by
  unfold routeBound routeCong routeBatchH routePathLen
  set A := pairs.length * (X.card + (G.inside X).length + 1)
  have hA : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  set d := 32 * Δ * b * L
  have hd2 : 32 * Δ * (2 * b) * L = 2 * d := by simp only [d]; ring
  rw [hd2]
  have hd : 1 ≤ d := by
    simp only [d]
    have : 1 ≤ Δ * b * L := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega))
    nlinarith
  set Q := 16 * b * Δ * L
  have hQ : 1 ≤ Q := by
    simp only [Q]
    have : 1 ≤ b * Δ * L := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega))
    nlinarith
  have e1 : A * (d + 1) * (16 * b * Δ * (d + 1) * L) = A * Q * ((d + 1) * (d + 1)) := by
    simp only [Q]; ring
  have e2 : A * (2 * d + 1) * (16 * (2 * b) * Δ * (2 * d + 1) * L) =
      2 * (A * Q * ((2 * d + 1) * (2 * d + 1))) := by
    simp only [Q]; ring
  rw [e1, e2]
  have hsq : (d + 1) * (d + 1) + 1 ≤ (2 * d + 1) * (2 * d + 1) := by nlinarith
  have hAQ : 1 ≤ A * Q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hmain : 2 * (A * Q * ((d + 1) * (d + 1)) + 1) ≤
      2 * (A * Q * ((2 * d + 1) * (2 * d + 1))) + 1 := by
    have : A * Q * ((d + 1) * (d + 1) + 1) ≤ A * Q * ((2 * d + 1) * (2 * d + 1)) :=
      Nat.mul_le_mul_left _ hsq
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  calc 2 * (C * (A * Q * ((d + 1) * (d + 1)) + 1))
      = C * (2 * (A * Q * ((d + 1) * (d + 1)) + 1)) := by ring
    _ ≤ C * (2 * (A * Q * ((2 * d + 1) * (2 * d + 1))) + 1) := Nat.mul_le_mul_left _ hmain

/-- The invariant of the loop, by induction on the fuel. Start at `b ≥ 2` with `|X| < 2^{n+1} b`.
Then the result is a matched outcome that meets the router's specification at the returned `b'`;
`b ≤ b'`; either `b' = b`, or `b' ≤ |X|` and `b' β ≤ 2`; and the total cost plus the bound at `b`
is at most twice the bound at `b'`. -/
theorem fullRoute_invariant {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {C : ℕ}
    {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)} {Δ L : ℕ}
    (hC : ∀ b, 2 ≤ b → routeCost G X pairs Δ L b 0 ≤ routeBound C G X pairs Δ L b)
    (hpre : RouterPre G X pairs Δ L) (hk : 1 ≤ pairs.length) {β : ℝ} (hβ : 0 < β)
    (hexp : G.IsExpansionExpanderOn X β) :
    ∀ n b, 2 ≤ b → X.card < 2 ^ (n + 1) * b →
      let r := fullRoute route G X pairs Δ L n b
      (∃ M emb, r.1 = .matched M emb ∧ RouteMatchedSpec G X pairs Δ L r.2 0 M emb) ∧
        b ≤ r.2 ∧ (r.2 = b ∨ (r.2 ≤ X.card ∧ (r.2 : ℝ) * β ≤ 2)) ∧
        fullRouteCost route routeCost G X pairs Δ L n b + routeBound C G X pairs Δ L b ≤
          2 * routeBound C G X pairs Δ L r.2 := by
  obtain ⟨hX, hloop, hΔ, hdeg, hL, hXL, hvalid⟩ := hpre
  have hspec : ∀ b, 2 ≤ b → RouteSpec G X pairs Δ L b 0 (route G X pairs Δ L b 0) :=
    fun b hb => hrouter.spec G X pairs Δ L b 0 hX hloop hΔ hdeg hL hXL hb hvalid
  intro n
  induction n with
  | zero =>
    intro b hb hXb
    have hs := hspec b hb
    have hc := hC b hb
    simp only [fullRoute, fullRouteCost]
    cases hr : route G X pairs Δ L b 0 with
    | matched M emb =>
      rw [hr] at hs
      exact ⟨⟨M, emb, rfl, hs⟩, le_rfl, by simp, by omega⟩
    | cut U =>
      rw [hr] at hs
      have := (cut_forces hβ hexp hs).2
      simp at hXb
      omega
  | succ n ih =>
    intro b hb hXb
    have hs := hspec b hb
    have hc := hC b hb
    cases hr : route G X pairs Δ L b 0 with
    | matched M emb =>
      rw [hr] at hs
      simp only [fullRoute, fullRouteCost, hr]
      exact ⟨⟨M, emb, rfl, hs⟩, le_rfl, by simp, by omega⟩
    | cut U =>
      rw [hr] at hs
      simp only [fullRoute, fullRouteCost, hr]
      obtain ⟨hbβ, h2b⟩ := cut_forces hβ hexp hs
      have hXb' : X.card < 2 ^ (n + 1) * (2 * b) := by
        rw [show 2 ^ (n + 1) * (2 * b) = 2 ^ (n + 1 + 1) * b by ring]; exact hXb
      obtain ⟨hm, hle, hcase, hcost⟩ := ih (2 * b) (by omega) hXb'
      refine ⟨hm, by omega, Or.inr ?_, ?_⟩
      · rcases hcase with h | h
        · rw [h]
          refine ⟨h2b, ?_⟩
          push_cast
          linarith
        · exact h
      · have hdbl := two_mul_routeBound_le (C := C) (G := G) (X := X) (pairs := pairs) hk hΔ hL
          (b := b) (by omega)
        omega

private theorem card_lt_start (p : ℕ) : p < 2 ^ (p + 1) * 2 := by
  have h := Nat.lt_two_pow_self (n := p)
  have : 2 ^ (p + 1) * 2 = 2 ^ p * 4 := by ring
  omega

/-- **`lemma_1` (full routing).** Let the router meet `IsMatchingPlayer` with cost
constant `C` (as in `IsMatchingPlayer.cost_bound`), let the host `G[X]` meet the router's
preconditions and have edge expansion `β > 0`, and let there be at least one terminal pair. The
loop from `b = 2` that doubles `b` after a cut returns a matched outcome with deficit `0` at its
last `b`. This `b` is at least `2`, at most `max(2, 2/β) ≤ max(2, 4/β)` and at most
`max(2, |X|)`. The total cost of all calls is at most twice the cost bound of the last call. -/
theorem lemma_1 {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {C : ℕ}
    {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)} {Δ L : ℕ}
    (hC : ∀ b, 2 ≤ b → routeCost G X pairs Δ L b 0 ≤ routeBound C G X pairs Δ L b)
    (hpre : RouterPre G X pairs Δ L) (hk : 1 ≤ pairs.length) {β : ℝ} (hβ : 0 < β)
    (hexp : G.IsExpansionExpanderOn X β) :
    let r := lemma1Route route G X pairs Δ L
    (∃ M emb, r.1 = .matched M emb ∧ RouteMatchedSpec G X pairs Δ L r.2 0 M emb) ∧
      2 ≤ r.2 ∧ (r.2 : ℝ) ≤ max 2 (2 / β) ∧ (r.2 : ℝ) ≤ max 2 (4 / β) ∧ r.2 ≤ max 2 X.card ∧
      fullRouteCost route routeCost G X pairs Δ L X.card 2 ≤ 2 * routeBound C G X pairs Δ L r.2 := by
  obtain ⟨hm, hle, hcase, hcost⟩ := fullRoute_invariant hrouter hC hpre hk hβ hexp X.card 2
    le_rfl (card_lt_start X.card)
  simp only [lemma1Route]
  have h22 : ((fullRoute route G X pairs Δ L X.card 2).2 : ℝ) ≤ max 2 (2 / β) := by
    rcases hcase with h | ⟨_, h⟩
    · rw [h]; push_cast; exact le_max_left _ _
    · refine le_trans ?_ (le_max_right _ _)
      rw [le_div_iff₀ hβ]; exact h
  refine ⟨hm, hle, h22, le_trans h22 (max_le_max le_rfl ?_), ?_, by omega⟩
  · exact div_le_div_of_nonneg_right (by norm_num) hβ.le
  · rcases hcase with h | ⟨h, _⟩
    · rw [h]; exact le_max_left _ _
    · exact le_trans h (le_max_right _ _)

/-- With deficit `0`, the matched outcome is full: the `i`-th matching has `|A_i|` edges. -/
theorem fullRoute_full {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {Δ L b : ℕ} {M : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (h : RouteMatchedSpec G X pairs Δ L b 0 M emb) :
    ∀ i (hi : i < pairs.length), (M.getD i []).length = (pairs[i]'hi).1.card := by
  intro i hi
  have hlen := h.1
  have hsum := h.2.2.1
  have hle := h.length_le_fst_card hi
  have hz : (List.zipWith (fun p M => p.1.card - M.length) pairs M).sum = 0 := by omega
  rw [List.sum_eq_zero_iff] at hz
  have hiz : i < (List.zipWith (fun (p : Finset ℕ × Finset ℕ) (M : List (ℕ × ℕ)) =>
      p.1.card - M.length) pairs M).length := by
    rw [List.length_zipWith, hlen, min_self]; exact hi
  have h0 := hz _ (List.getElem_mem hiz)
  rw [List.getElem_zipWith] at h0
  have hMi : M.getD i [] = M[i]'(by rw [hlen]; exact hi) := by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)]
  rw [hMi]
  rw [hMi] at hle
  omega

/-- **Full routing, with the router's own constant.** For a router that meets `IsMatchingPlayer` there
is a constant `C` such that for every host `G[X]` that meets the router's preconditions and has
edge expansion `β > 0`, and every nonempty list of terminal pairs, the loop returns full matchings
(`fullRoute_full`) at a last `b` with `2 ≤ b ≤ max(2, 2/β)` and `b ≤ max(2, |X|)`, and its total
cost is at most twice the cost bound of the call at the last `b`. -/
theorem exists_lemma_1 {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) :
    ∃ C : ℕ, ∀ (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (Δ L : ℕ),
      RouterPre G X pairs Δ L → 1 ≤ pairs.length → ∀ β : ℝ, 0 < β →
      G.IsExpansionExpanderOn X β →
      let r := lemma1Route route G X pairs Δ L
      (∃ M emb, r.1 = .matched M emb ∧ RouteMatchedSpec G X pairs Δ L r.2 0 M emb ∧
        ∀ i (hi : i < pairs.length), (M.getD i []).length = (pairs[i]'hi).1.card) ∧
      2 ≤ r.2 ∧ (r.2 : ℝ) ≤ max 2 (2 / β) ∧ r.2 ≤ max 2 X.card ∧
      fullRouteCost route routeCost G X pairs Δ L X.card 2 ≤
        2 * routeBound C G X pairs Δ L r.2 := by
  obtain ⟨C, hC⟩ := hrouter.cost_bound
  refine ⟨C, fun G X pairs Δ L hpre hk β hβ hexp => ?_⟩
  obtain ⟨hX, hloop, hΔ, hdeg, hL, hXL, hvalid⟩ := hpre
  have hC' : ∀ b, 2 ≤ b → routeCost G X pairs Δ L b 0 ≤ routeBound C G X pairs Δ L b :=
    fun b hb => hC G X pairs Δ L b 0 hX hloop hΔ hdeg hL hXL hb hvalid
  obtain ⟨⟨M, emb, hr, hs⟩, h2, h22, _, hX2, hcost⟩ :=
    lemma_1 hrouter hC' ⟨hX, hloop, hΔ, hdeg, hL, hXL, hvalid⟩ hk hβ hexp
  exact ⟨⟨M, emb, hr, hs, fullRoute_full hs⟩, h2, h22, hX2, hcost⟩

end MinCostFlow.HierPaths
