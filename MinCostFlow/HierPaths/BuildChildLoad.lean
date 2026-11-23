module

public import MinCostFlow.HierPaths.BuildChildRound

/-!
# The batched game of `lemma_3`: the load and the whole run

Each round makes one router call. The children's terminal sets are disjoint, so each matched edge
goes to at most one child, and the walks all children take in one round add at most the load of
one call (`sum_occLoad_take_le`). One call has load at most `R`, the congestion bound of the router,
since its walks are shortcut to walks that repeat no edge (`occLoad_callEntries_le`). So `t`
rounds add load at most `t · R` (`gameRun_inv`).

After `49 L' + 1` rounds, where `s < 2^{L'}`, every child has saved its set (`gameRun_saved`): a
child still in the game would have played `49 L' + 1` rounds that meet the condition of the round
bound (`game_rounds_lt`).
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

theorem occLoad_append (F F' : List (ℕ × List ℕ)) (i : ℕ) :
    occLoad (F ++ F') i = occLoad F i + occLoad F' i := by
  simp [occLoad]

/-- The load only depends on the walks. -/
theorem occLoad_map_congr {α : Type*} {l : List α} {f g : α → ℕ × List ℕ}
    (h : ∀ x ∈ l, (f x).2 = (g x).2) (i : ℕ) : occLoad (l.map f) i = occLoad (l.map g) i := by
  unfold occLoad
  rw [List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun x hx => by simp [h x hx]

/-- **What all children take from one call has at most the load of the call.** -/
theorem sum_occLoad_take_le {k s : ℕ} {off : ℕ → ℕ}
    (hdisj : ∀ c < k, ∀ c' < k, c ≠ c' →
      Disjoint (shiftSet (off c) (Finset.range s)) (shiftSet (off c') (Finset.range s)))
    (es : List ((ℕ × ℕ) × List ℕ)) (i : ℕ) :
    ∑ c ∈ Finset.range k, occLoad (walkFamily (takeEntries s (off c) es)) i ≤
      occLoad (walkFamily es) i := by
  have h1 : ∀ c, occLoad (walkFamily (takeEntries s (off c) es)) i =
      occLoad ((es.filter fun en => decide (en.1.1 ∈ shiftSet (off c) (Finset.range s))).map
        fun en => (0, en.2)) i := by
    intro c
    unfold walkFamily takeEntries
    rw [List.map_map]
    exact occLoad_map_congr (fun _ _ => by rfl) i
  have h2 : occLoad (walkFamily es) i = occLoad (es.map fun en => (0, en.2)) i := by
    unfold walkFamily
    exact occLoad_map_congr (fun _ _ => by rfl) i
  rw [Finset.sum_congr rfl fun c _ => h1 c, h2]
  refine sum_occLoad_filter_le
    (P := fun c en => decide (en.1.1 ∈ shiftSet (off c) (Finset.range s))) ?_ _ es i
  intro x c hc c' hc' h h'
  by_contra hne
  simp only [decide_eq_true_eq] at h h'
  exact Finset.disjoint_left.mp (hdisj c hc c' hc' hne) h h'

/-- The call of a round in which some child requests returns matchings with walks of at most `d`
edges and congestion at most `R`. -/
theorem round_call {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ))
    {cfg : ParamConfig} {M r : ℕ} {core : ℕ → Graph → CoreResult}
    {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg M r core coreCost)
    {k s : ℕ} {off : ℕ → ℕ} (hch : IsChildren X (fun c => shiftSet (off c) (Finset.range s)) k s)
    {t L' d P : ℕ} (heven : s % 2 = 0) (hsN : s ≤ (NOf M r) ^ r) (hΔ : 49 * L' ≤ deltaParam M)
    (ht : t ≤ 49 * L') {sts : ℕ → ChildState}
    (hinv : ∀ c < k, ChildInv G X s (off c) d P t (sts c))
    (hne : requesting core M r s k off sts ≠ []) :
    ∃ Ms emb, (lemma1Route route G X (roundPairs core M r s k off sts) Δ L).1 = .matched Ms emb ∧
      (∀ j < Ms.flatten.length, (emb j).length ≤ routePathLen Δ bh L) ∧
      (∀ i < G.m, congestion (Graph.mk G.n Ms.flatten) emb i ≤ routeCong Δ bh L) ∧
      (∀ j < Ms.flatten.length,
        IsEdgeWalk G.edges (edgeAt Ms.flatten j).1 (edgeAt Ms.flatten j).2 (emb j)) := by
  obtain ⟨hnd, hmem⟩ := requesting_spec core M r s k off sts
  set p : ℕ → Finset ℕ × Finset ℕ := fun c' => (request core M r s (off c') (sts c')).getD (∅, ∅)
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
  obtain ⟨Ms, emb, hres, _, _, _, hlen, hcong, hwalk⟩ :=
    group_call hrouter hH hβ hexp hbh hch hnd (fun c' hc' => ((hmem c').mp hc').1) hne hp
  exact ⟨Ms, emb, hres, hlen, hcong, hwalk⟩

/-- **The load of one round.** -/
theorem gameRound_load {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ))
    {cfg : ParamConfig} {M r : ℕ} {core : ℕ → Graph → CoreResult}
    {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg M r core coreCost)
    {k s : ℕ} {off : ℕ → ℕ} (hch : IsChildren X (fun c => shiftSet (off c) (Finset.range s)) k s)
    {t L' d P : ℕ} (heven : s % 2 = 0) (hsN : s ≤ (NOf M r) ^ r) (hΔ : 49 * L' ≤ deltaParam M)
    (ht : t ≤ 49 * L') {sts : ℕ → ChildState}
    (hinv : ∀ c < k, ChildInv G X s (off c) d P t (sts c)) {i : ℕ} (hi : i < G.m) :
    ∑ c ∈ Finset.range k,
        occLoad (walkFamily (gameRound route G X Δ L core M r s k off sts c).rounds.flatten) i ≤
      ∑ c ∈ Finset.range k, occLoad (walkFamily (sts c).rounds.flatten) i +
        routeCong Δ bh L := by
  set es := callEntries G.edges (lemma1Route route G X (roundPairs core M r s k off sts) Δ L).1 with hes
  have hstep : ∀ c,
      occLoad (walkFamily (gameRound route G X Δ L core M r s k off sts c).rounds.flatten) i ≤
        occLoad (walkFamily (sts c).rounds.flatten) i +
          (if (request core M r s (off c) (sts c)).isSome then
            occLoad (walkFamily (takeEntries s (off c) es)) i else 0) := by
    intro c
    unfold gameRound request
    cases hsv : (sts c).saved with
    | some S => simp
    | none =>
      cases hca : coreAnswer core M r s (sts c) with
      | expander S => simp
      | cut U =>
        simp only [List.flatten_append, List.flatten_singleton, walkFamily, List.map_append,
          occLoad_append, Option.isSome_some, ite_true]
        rfl
  have hite : ∑ c ∈ Finset.range k,
      (if (request core M r s (off c) (sts c)).isSome then
        occLoad (walkFamily (takeEntries s (off c) es)) i else 0) ≤
      routeCong Δ bh L := by
    obtain ⟨_, hmem⟩ := requesting_spec core M r s k off sts
    by_cases hne : requesting core M r s k off sts = []
    · have h0 : ∀ c ∈ Finset.range k, (if (request core M r s (off c) (sts c)).isSome then
          occLoad (walkFamily (takeEntries s (off c) es)) i else 0) = 0 := by
        intro c hc
        cases hs : (request core M r s (off c) (sts c)).isSome with
        | false => simp
        | true =>
          have hmc := (hmem c).mpr ⟨Finset.mem_range.mp hc, hs⟩
          rw [hne] at hmc
          simp at hmc
      rw [Finset.sum_eq_zero h0]
      exact Nat.zero_le _
    · obtain ⟨Ms, emb, hres, _, hcong, hwalk⟩ :=
        round_call hrouter hH hβ hexp hbh hcore hch heven hsN hΔ ht hinv hne
      have hes' : es = callEntries G.edges (.matched Ms emb) := by rw [hes, hres]
      calc _ ≤ ∑ c ∈ Finset.range k, occLoad (walkFamily (takeEntries s (off c) es)) i := by
            apply Finset.sum_le_sum
            intro c _
            split_ifs <;> simp
        _ ≤ occLoad (walkFamily es) i :=
            sum_occLoad_take_le (fun c hc c' hc' h => hch.2.2 c hc c' hc' h) es i
        _ ≤ routeCong Δ bh L := by
            rw [hes']
            exact occLoad_callEntries_le hwalk (hcong i hi)
  calc _ ≤ ∑ c ∈ Finset.range k, (occLoad (walkFamily (sts c).rounds.flatten) i +
          (if (request core M r s (off c) (sts c)).isSome then
            occLoad (walkFamily (takeEntries s (off c) es)) i else 0)) :=
        Finset.sum_le_sum fun c _ => hstep c
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := Nat.add_le_add_left hite _

/-- **The run of the game.** For `t ≤ 49 L' + 1` rounds, every child satisfies the invariant,
and the walks of all children have load at most `t · R`. -/
theorem gameRun_inv {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ))
    {cfg : ParamConfig} {M r : ℕ} {core : ℕ → Graph → CoreResult}
    {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg M r core coreCost)
    {k s : ℕ} {off : ℕ → ℕ} (hch : IsChildren X (fun c => shiftSet (off c) (Finset.range s)) k s)
    {L' : ℕ} (heven : s % 2 = 0) (hsN : s ≤ (NOf M r) ^ r) (hΔ : 49 * L' ≤ deltaParam M) :
    ∀ t ≤ 49 * L' + 1,
      (∀ c < k, ChildInv G X s (off c) (routePathLen Δ bh L) (PParam cfg M r) t
        (gameRun route G X Δ L core M r s k off t c)) ∧
      ∀ i < G.m, ∑ c ∈ Finset.range k,
          occLoad (walkFamily (gameRun route G X Δ L core M r s k off t c).rounds.flatten) i ≤
        t * routeCong Δ bh L := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨fun c _ => childInv_init G X s (off c) _ _, fun i _ => ?_⟩
    simp [gameRun, ChildState.init, walkFamily, occLoad]
  | succ t ih =>
    intro ht
    obtain ⟨hinv, hload⟩ := ih (by omega)
    refine ⟨gameRound_inv hrouter hH hβ hexp hbh hcore hch heven hsN hΔ (by omega) hinv,
      fun i hi => ?_⟩
    have := gameRound_load hrouter hH hβ hexp hbh hcore hch heven hsN hΔ (by omega) hinv hi
    have h2 := hload i hi
    simp only [gameRun]
    rw [Nat.succ_mul]
    omega

/-- **Every child saves its set by round `49 L' + 1`.** -/
theorem gameRun_saved {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hH : HostPre G X Δ L) {β : ℝ} (hβ : 0 < β) (hexp : G.IsExpansionExpanderOn X β) {bh : ℕ}
    (hbh : max 2 (2 / β) ≤ (bh : ℝ))
    {cfg : ParamConfig} {M r : ℕ} {core : ℕ → Graph → CoreResult}
    {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg M r core coreCost)
    {k s : ℕ} {off : ℕ → ℕ} (hch : IsChildren X (fun c => shiftSet (off c) (Finset.range s)) k s)
    {L' : ℕ} (heven : s % 2 = 0) (hsN : s ≤ (NOf M r) ^ r) (hΔ : 49 * L' ≤ deltaParam M)
    (hsL : s < 2 ^ L') :
    ∀ c < k, ∃ S, (gameRun route G X Δ L core M r s k off (49 * L' + 1) c).saved = some S := by
  intro c hc
  obtain ⟨hinv, _⟩ := gameRun_inv hrouter hH hβ hexp hbh hcore hch heven hsN hΔ _ le_rfl
  obtain ⟨_, hact, hrounds, _, _⟩ := hinv c hc
  cases hsv : (gameRun route G X Δ L core M r s k off (49 * L' + 1) c).saved with
  | some S => exact ⟨S, rfl⟩
  | none =>
    exfalso
    have hlen := hact hsv
    rw [hlen] at hrounds
    have := game_rounds_lt (t := 49 * L' + 1) hch.1 hsL (fun j hj => (hrounds j hj).1)
      (fun j hj => (hrounds j hj).2)
    omega

end MinCostFlow.HierPaths
