module

public import MinCostFlow.HierPaths.BuildHierBounds
public import MinCostFlow.HierPaths.BuildConnCount

/-!
# The operation count of the construction at one group

The work at a group `X` (with host `G`, children of size `s` and `k` children) is:
- in each of the `T` rounds of the game, one core call per active child (`coreCost`) and, if some
  child requests a matching, one full-routing call for all requests, counted with the shortcuts of
  its walks (`callCost`) (`roundCost`);
- one injection call after the rounds (`gameCost`);
- one full-routing call per pair of children for the connectors (`connCost`).

The costs of the router and the core are parameters. `gameCost_le` bounds the game by
`T · (k · s · N² · W^{10 r² + 10} + 2 ρ_k) + 2 ρ_k`, where
`ρ_n = routeBoundN (C + 2) G X n Δ L b̂` bounds one call with `n` terminal pairs and its shortcuts
(`callCost_le`; `C` is the constant of `IsMatchingPlayer.cost_bound`), and `connCost_le_of`
bounds the connectors by `k² · 2 ρ_1`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The cost bound of the router with constant `C` (the body of `IsMatchingPlayer.cost_bound`). -/
def RouteCostLe (routeCost : RouterCostFn) (C : ℕ) : Prop :=
  ∀ (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (Δ L b z : ℕ),
    X ⊆ Finset.range G.n → (∀ e ∈ G.inside X, e.1 ≠ e.2) → 1 ≤ Δ →
    (∀ v ∈ X, G.degIn X v ≤ Δ) → 1 ≤ L → X.card < 2 ^ L → 2 ≤ b →
    ValidTerminalPairs X pairs →
    routeCost G X pairs Δ L b z ≤
      C * (pairs.length * (X.card + (G.inside X).length + 1) *
        (routePathLen Δ b L + 1) * routeCong Δ b L + 1)

/-- The cost bound of one router call with `n` terminal pairs. -/
def routeBoundN (C : ℕ) (G : Graph) (X : Finset ℕ) (n Δ L b : ℕ) : ℕ :=
  C * (n * (X.card + (G.inside X).length + 1) * (routePathLen Δ b L + 1) * routeCong Δ b L + 1)

/-- The cost of one round of the game. -/
def roundCost (route : RouterFn) (routeCost : RouterCostFn) (G : Graph) (X : Finset ℕ)
    (Δ L : ℕ) (core : ℕ → Graph → CoreResult) (coreCost : ℕ → Graph → ℕ) (M r s k : ℕ)
    (off : ℕ → ℕ) (sts : ℕ → ChildState) : ℕ :=
  ((List.range k).map fun c =>
    match (sts c).saved with
    | some _ => 0
    | none => coreCost (coreLevel M r s) (gameGraph s (sts c))).sum +
  (if requesting core M r s k off sts = [] then 0 else
    callCost route routeCost G X (roundPairs core M r s k off sts) Δ L)

/-- The cost of the game with `t` rounds and the injection call. -/
def gameCost (route : RouterFn) (routeCost : RouterCostFn) (G : Graph) (X : Finset ℕ)
    (Δ L : ℕ) (core : ℕ → Graph → CoreResult) (coreCost : ℕ → Graph → ℕ) (M r s k : ℕ)
    (off : ℕ → ℕ) (t : ℕ) : ℕ :=
  ∑ u ∈ Finset.range t,
      roundCost route routeCost G X Δ L core coreCost M r s k off
        (gameRun route G X Δ L core M r s k off u) +
    callCost route routeCost G X
      (injPairs s k off (gameRun route G X Δ L core M r s k off t)) Δ L

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

theorem routeBound_eq_routeBoundN (C : ℕ) (G : Graph) (X : Finset ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) (Δ L b : ℕ) :
    routeBound C G X pairs Δ L b = routeBoundN C G X pairs.length Δ L b := rfl

theorem routeBoundN_mono {C : ℕ} {G : Graph} {X : Finset ℕ} {n n' Δ L b : ℕ} (h : n ≤ n') :
    routeBoundN C G X n Δ L b ≤ routeBoundN C G X n' Δ L b := by
  unfold routeBoundN
  apply Nat.mul_le_mul_left
  have := Nat.mul_le_mul_right ((X.card + (G.inside X).length + 1)) h
  have := Nat.mul_le_mul_right (routePathLen Δ b L + 1) this
  have := Nat.mul_le_mul_right (routeCong Δ b L) this
  omega

/-- **The cost of one full-routing call for valid pairs.** -/
theorem fullRouteCost_le {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {C : ℕ} (hC : RouteCostLe routeCost C)
    {G : Graph} {X : Finset ℕ} {Δ L : ℕ} (hH : HostPre G X Δ L)
    {pairs : List (Finset ℕ × Finset ℕ)} (hv : ValidTerminalPairs X pairs)
    (hk : 1 ≤ pairs.length) {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ)) :
    fullRouteCost route routeCost G X pairs Δ L X.card 2 ≤
      2 * routeBoundN C G X pairs.length Δ L bh := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hcost⟩ :=
    call_facts hrouter (fun b hb => hC G X pairs Δ L b 0 a1 a2 a3 a4 a5 a6 hb hv)
      ⟨a1, a2, a3, a4, a5, a6, hv⟩ hk hβ hexp hbh
  exact hcost

/-- **The cost of one call with its shortcuts**: at most `2 ρ_n` with the constant `C + 2`. -/
theorem callCost_le {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {C : ℕ} (hC : RouteCostLe routeCost C)
    {G : Graph} {X : Finset ℕ} {Δ L : ℕ} (hH : HostPre G X Δ L)
    {pairs : List (Finset ℕ × Finset ℕ)} (hv : ValidTerminalPairs X pairs)
    (hk : 1 ≤ pairs.length) {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ)) :
    callCost route routeCost G X pairs Δ L ≤ 2 * routeBoundN (C + 2) G X pairs.length Δ L bh := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
  obtain ⟨Ms, emb, b', hr, hs, hcard, _, _, hlen, _, hcost⟩ :=
    call_facts hrouter (fun b hb => hC G X pairs Δ L b 0 a1 a2 a3 a4 a5 a6 hb hv)
      ⟨a1, a2, a3, a4, a5, a6, hv⟩ hk hβ hexp hbh
  have hbh2 : 2 ≤ bh := by
    have : (2 : ℝ) ≤ bh := le_trans (le_max_left _ _) hbh
    exact_mod_cast this
  have hfl := length_flatten_le hv hs.1 hcard
  have her := resEraseCost_le (E := G.edges) hlen
  unfold callCost
  rw [hr]
  simp only
  -- `n |X| (d + 1) ≤ Y`, where `ρ_n = C (Y + 1)`
  set n := pairs.length
  set d := routePathLen Δ bh L
  set R := routeCong Δ bh L
  have hR : 1 ≤ R := by
    show 1 ≤ 16 * bh * Δ * (routePathLen Δ bh L + 1) * L
    apply Nat.one_le_iff_ne_zero.mpr
    apply Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega))
    omega
  have hY : n * X.card * (d + 1) ≤ n * (X.card + (G.inside X).length + 1) * (d + 1) * R := by
    calc n * X.card * (d + 1) ≤ n * (X.card + (G.inside X).length + 1) * (d + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ ≤ _ := Nat.le_mul_of_pos_right _ hR
  have hcost' : fullRouteCost route routeCost G X pairs Δ L X.card 2 ≤
      2 * routeBoundN C G X n Δ L bh := hcost
  have her' : Ms.flatten.length * (3 * (d + 1)) ≤ 3 * (n * X.card * (d + 1)) := by
    have := Nat.mul_le_mul_right (3 * (d + 1)) hfl
    calc Ms.flatten.length * (3 * (d + 1)) ≤ n * X.card * (3 * (d + 1)) := this
      _ = 3 * (n * X.card * (d + 1)) := by ring
  unfold routeBoundN at hcost' ⊢
  set Y := n * (X.card + (G.inside X).length + 1) * (d + 1) * R
  have e : 2 * ((C + 2) * (Y + 1)) = 2 * (C * (Y + 1)) + 4 * (Y + 1) := by ring
  rw [e]
  omega

/-- **The connectors cost** at most `k² · 2 ρ_1`. -/
theorem connCost_le_of {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {C : ℕ} (hC : RouteCostLe routeCost C)
    {G : Graph} {X : Finset ℕ} {Δ L : ℕ} (hH : HostPre G X Δ L)
    {ch : ℕ → Finset ℕ} {k s : ℕ} (hch : IsChildren X ch k s)
    {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ)) :
    connCost route routeCost G X Δ L ch k ≤ k * k * (2 * routeBoundN (C + 2) G X 1 Δ L bh) := by
  obtain ⟨hlen, hp⟩ := pairsBelow_spec k
  unfold connCost
  calc ((pairsBelow k).map fun p =>
        callCost route routeCost G X [(ch p.1, ch p.2)] Δ L).sum
      ≤ ((pairsBelow k).map fun _ => 2 * routeBoundN (C + 2) G X 1 Δ L bh).sum := by
        apply List.sum_le_sum
        intro p hpm
        obtain ⟨h1, h2, h3⟩ := hp p hpm
        obtain ⟨a1, a2, a3, a4, a5, a6, hv⟩ := routerPre_pair hH hch h1 h2 (by omega)
        exact callCost_le hrouter hC ⟨a1, a2, a3, a4, a5, a6⟩ hv (by simp) hβ hexp hbh
    _ = (pairsBelow k).length * (2 * routeBoundN (C + 2) G X 1 Δ L bh) := by simp
    _ ≤ k * k * (2 * routeBoundN (C + 2) G X 1 Δ L bh) := Nat.mul_le_mul_right _ hlen

/-- **The cost of one round.** -/
theorem roundCost_le {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {C : ℕ} (hC : RouteCostLe routeCost C)
    {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ))
    {cfg : ParamConfig} {M r : ℕ} {core : ℕ → Graph → CoreResult}
    {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg M r core coreCost)
    {k s : ℕ} {off : ℕ → ℕ} (hch : IsChildren X (fun c => shiftSet (off c) (Finset.range s)) k s)
    {t L' d P : ℕ} (hs2 : 2 ≤ s) (heven : s % 2 = 0) (hsN : s ≤ (NOf M r) ^ r)
    (hΔ : 49 * L' ≤ deltaParam M) (ht : t ≤ 49 * L') {sts : ℕ → ChildState}
    (hinv : ∀ c < k, ChildInv G X s (off c) d P t (sts c)) :
    roundCost route routeCost G X Δ L core coreCost M r s k off sts ≤
      k * (s * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) +
        2 * routeBoundN (C + 2) G X k Δ L bh := by
  unfold roundCost
  apply Nat.add_le_add
  · have h : ∀ x ∈ (List.range k).map (fun c =>
        match (sts c).saved with
        | some _ => 0
        | none => coreCost (coreLevel M r s) (gameGraph s (sts c))),
        x ≤ s * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      have hck := List.mem_range.mp hc
      cases (sts c).saved with
      | some _ => exact Nat.zero_le _
      | none =>
        obtain ⟨hlen, _, hrounds, _, _⟩ := hinv c hck
        have hpm : ∀ j < (sts c).rounds.length, IsPerfectMatchingOn (Finset.range s) ((sts c).M j) :=
          fun j hj => (hrounds j hj).1
        have hdeg : ∀ v < (gameGraph s (sts c)).n, (gameGraph s (sts c)).deg v ≤ deltaParam M := by
          intro v _
          have := witness_deg_le hpm v
          unfold gameGraph at this ⊢
          omega
        exact hcore.cost_coreLevel (witness_valid hpm) (witness_loopless hpm) hs2 hsN hdeg
    have := List.sum_le_length_nsmul _ _ h
    simpa using this
  · split_ifs with hne
    · exact Nat.zero_le _
    · obtain ⟨hnd, hmem⟩ := requesting_spec core M r s k off sts
      set p : ℕ → Finset ℕ × Finset ℕ :=
        fun c' => (request core M r s (off c') (sts c')).getD (∅, ∅)
      have hp : ∀ c' ∈ requesting core M r s k off sts,
          (p c').1 ⊆ shiftSet (off c') (Finset.range s) ∧
          (p c').2 ⊆ shiftSet (off c') (Finset.range s) ∧ Disjoint (p c').1 (p c').2 ∧
          (p c').1.card ≤ (p c').2.card := by
        intro c' hc'
        obtain ⟨hc'k, hsome⟩ := (hmem c').mp hc'
        obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
        have hpq : p c' = q := by simp only [p, hq, Option.getD_some]
        rw [hpq]
        exact request_props hcore heven hsN hΔ ht (hinv c' hc'k) hq
      have hY : ∀ c ∈ requesting core M r s k off sts, shiftSet (off c) (Finset.range s) ⊆ X :=
        fun c hc => (hch.2.1 c ((hmem c).mp hc).1).1
      have hdisj : ∀ c ∈ requesting core M r s k off sts, ∀ c' ∈ requesting core M r s k off sts,
          c ≠ c' → Disjoint (shiftSet (off c) (Finset.range s)) (shiftSet (off c') (Finset.range s)) :=
        fun c hc c' hc' h => hch.2.2 c ((hmem c).mp hc).1 c' ((hmem c').mp hc').1 h
      have hv := validTerminalPairs_of_children hnd hY hdisj hp
      have hpairs : roundPairs core M r s k off sts = (requesting core M r s k off sts).map p := rfl
      have hk : 1 ≤ (roundPairs core M r s k off sts).length := by
        rw [hpairs, List.length_map]
        exact List.length_pos_iff.mpr hne
      rw [← hpairs] at hv
      refine le_trans (callCost_le hrouter hC hH hv hk hβ hexp hbh) ?_
      apply Nat.mul_le_mul_left
      apply routeBoundN_mono
      rw [hpairs, List.length_map]
      unfold requesting
      exact (List.length_filter_le _ _).trans (by simp)

/-- **The cost of the game.** -/
theorem gameCost_le {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {C : ℕ} (hC : RouteCostLe routeCost C)
    {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ))
    {cfg : ParamConfig} {M r : ℕ} {core : ℕ → Graph → CoreResult}
    {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg M r core coreCost)
    {k s : ℕ} {off : ℕ → ℕ} (hch : IsChildren X (fun c => shiftSet (off c) (Finset.range s)) k s)
    (hk : 1 ≤ k) {L' : ℕ} (hs2 : 2 ≤ s) (heven : s % 2 = 0) (hsN : s ≤ (NOf M r) ^ r)
    (hΔ : 49 * L' ≤ deltaParam M) (hsL : s < 2 ^ L') :
    gameCost route routeCost G X Δ L core coreCost M r s k off (49 * L' + 1) ≤
      (49 * L' + 1) * (k * (s * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) +
        2 * routeBoundN (C + 2) G X k Δ L bh) + 2 * routeBoundN (C + 2) G X k Δ L bh := by
  unfold gameCost
  apply Nat.add_le_add
  · calc _ ≤ ∑ u ∈ Finset.range (49 * L' + 1),
          (k * (s * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) +
            2 * routeBoundN (C + 2) G X k Δ L bh) := by
          apply Finset.sum_le_sum
          intro u hu
          have hu' := Finset.mem_range.mp hu
          obtain ⟨hinv, _⟩ := gameRun_inv hrouter hH hβ hexp hbh hcore hch heven hsN hΔ u
            (by omega)
          exact roundCost_le hrouter hC hH hβ hexp hbh hcore hch hs2 heven hsN hΔ (by omega) hinv
      _ = _ := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  · set sts := gameRun route G X Δ L core M r s k off (49 * L' + 1)
    obtain ⟨hinv, _⟩ := gameRun_inv hrouter hH hβ hexp hbh hcore hch heven hsN hΔ _ le_rfl
    have hsaved := gameRun_saved hrouter hH hβ hexp hbh hcore hch heven hsN hΔ hsL
    set p : ℕ → Finset ℕ × Finset ℕ := fun c =>
      (shiftSet (off c) (Finset.range s \ savedSet s (sts c)), shiftSet (off c) (savedSet s (sts c)))
    have hpairs : injPairs s k off sts = (List.range k).map p := rfl
    have hp : ∀ c ∈ List.range k, (p c).1 ⊆ shiftSet (off c) (Finset.range s) ∧
        (p c).2 ⊆ shiftSet (off c) (Finset.range s) ∧ Disjoint (p c).1 (p c).2 ∧
        (p c).1.card ≤ (p c).2.card := by
      intro c hc
      have hck := List.mem_range.mp hc
      obtain ⟨S, hS⟩ := hsaved c hck
      obtain ⟨h1, h2, _⟩ := (hinv c hck).2.2.2.1 S hS
      have hss : savedSet s (sts c) = S := by
        unfold savedSet
        rw [hS]
        rfl
      refine ⟨shiftSet_subset Finset.sdiff_subset, ?_, ?_, ?_⟩
      · simp only [p, hss]
        exact shiftSet_subset h1
      · simp only [p]
        rw [shiftSet_sdiff]
        exact Finset.sdiff_disjoint
      · simp only [p, hss]
        rw [card_shiftSet, card_shiftSet, Finset.card_sdiff_of_subset h1, Finset.card_range]
        omega
    have hv := validTerminalPairs_of_children List.nodup_range
      (fun c hc => (hch.2.1 c (List.mem_range.mp hc)).1)
      (fun a ha b hb hab => hch.2.2 a (List.mem_range.mp ha) b (List.mem_range.mp hb) hab) hp
    rw [← hpairs] at hv
    have hk' : 1 ≤ (injPairs s k off sts).length := by
      rw [hpairs, List.length_map, List.length_range]
      exact hk
    refine le_trans (callCost_le hrouter hC hH hv hk' hβ hexp hbh) ?_
    apply Nat.mul_le_mul_left
    apply routeBoundN_mono
    rw [hpairs, List.length_map, List.length_range]

end MinCostFlow.HierPaths
