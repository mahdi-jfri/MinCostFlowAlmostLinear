module

public import MinCostFlow.ExpanderDecomp.OneShotStepD
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Step B of `OneShot`: parallel block cut-matching games and complement injection

In Step B of `OneShot(q, G, X)` (with `q ≥ 2`), we have `k` equal-sized
full blocks `blockSet vs b i` (`i < k`) of even size `b = N ^ (q - 1) / 2`. We run a cut-matching
game on each block simultaneously for `49 * L + 1` rounds:
* In each round, every still-active block queries `subCore` (`Core(q - 1)`) on its current witness
  graph `witnessEdges (rounds i) (numRounds i)`.
* Blocks returning `.expander S` save `S` and become inactive.
* Blocks returning `.cut U` pad their smaller side to a bisection `(C', B \ C')`, and all active
  blocks are routed in one combined call to `route`.
* If `route` returns a cut, Step B aborts and returns that cut; otherwise missing pairs are
  completed with fake edges and appended to each active block's witness.

By the round bound `Rounds.round_bound_nat`, every block must deactivate within `49 * L + 1` rounds.
Finally, one combined routing call injects `blockSet vs b i \ savedS i` into `savedS i` for all
`i < k`, certifying by the injection lemma `isExpansionExpanderOn_of_injection` that every full block has
edge expansion at least `1 / (2 * P (q - 1))` in `callsWitnessEdges calls_B`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- State of the `k` parallel block cut-matching games in Step B. -/
structure BlockGameState where
  /-- Whether block `i` is still playing its cut-matching game. -/
  active : ℕ → Bool
  /-- Saved expanding subset of block `i` once deactivated. -/
  savedS : ℕ → Finset ℕ
  /-- `rounds i j` is the perfect matching appended to block `i` in round `j`. -/
  rounds : ℕ → ℕ → List (ℕ × ℕ)
  /-- Number of matching rounds played so far by block `i`. -/
  numRounds : ℕ → ℕ
  /-- All routing calls performed so far in Step B. -/
  calls : List RoutedCall

/-- Initial state of Step B before any rounds: all blocks active, no edges, no routing calls. -/
def BlockGameState.init : BlockGameState where
  active := fun _ => true
  savedS := fun _ => ∅
  rounds := fun _ _ => []
  numRounds := fun _ => 0
  calls := []

/-- Query `subCore` on every active block `i < k`, returning the list of `(i, (C', B \ C'))` pairs
for blocks that returned a cut. -/
def activeCutPairs (G : Graph) (vs : List ℕ) (b k : ℕ)
    (subCore : Graph → Finset ℕ → CoreResult) (st : BlockGameState) :
    List (ℕ × (Finset ℕ × Finset ℕ)) :=
  (List.range k).filterMap fun i =>
    if st.active i then
      match subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
          (blockSet vs b i) with
      | .expander _ => none
      | .cut U =>
          let B := blockSet vs b i
          let C := smallerSide B U
          let C' := padToHalf B C
          some (i, (C', B \ C'))
    else none

/-- One common round of Step B. Returns `Sum.inl U` if the router fails with cut `U`, or
`Sum.inr st'` with the updated game state. -/
def stepBRound (cfg : CoreParams) (route : RouterFn) (G : Graph) (X : Finset ℕ) (vs : List ℕ)
    (b k z : ℕ) (subCore : Graph → Finset ℕ → CoreResult) (st : BlockGameState) :
    Finset ℕ ⊕ BlockGameState :=
  let rpairs := activeCutPairs G vs b k subCore st
  let pairs := rpairs.map Prod.snd
  if rpairs.isEmpty then
    Sum.inr
      { active := fun i =>
          if i < k then false else st.active i
        savedS := fun i =>
          if i < k && st.active i then
            match subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
                (blockSet vs b i) with
            | .expander S => S
            | .cut _ => st.savedS i
          else st.savedS i
        rounds := st.rounds
        numRounds := st.numRounds
        calls := st.calls }
  else
    match route G X pairs cfg.Δ cfg.L 100 z with
    | .cut U => Sum.inl U
    | .matched matchings emb =>
        let fake := completeBatchFake pairs matchings
        let rc : RoutedCall := ⟨matchings.flatten, emb, fake⟩
        let ids := rpairs.map Prod.fst
        let newM : ℕ → List (ℕ × ℕ) := fun i =>
          let idx := ids.idxOf i
          let p := pairs.getD idx (∅, ∅)
          let m := matchings.getD idx []
          m ++ completeMatchingFake p.1 p.2 m
        Sum.inr
          { active := fun i =>
              if i < k && st.active i then
                match subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
                    (blockSet vs b i) with
                | .expander _ => false
                | .cut _ => true
              else st.active i
            savedS := fun i =>
              if i < k && st.active i then
                match subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
                    (blockSet vs b i) with
                | .expander S => S
                | .cut _ => st.savedS i
              else st.savedS i
            rounds := fun i j =>
              if i < k && st.active i && j = st.numRounds i then
                match subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
                    (blockSet vs b i) with
                | .expander _ => st.rounds i j
                | .cut _ => newM i
              else st.rounds i j
            numRounds := fun i =>
              if i < k && st.active i then
                match subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
                    (blockSet vs b i) with
                | .expander _ => st.numRounds i
                | .cut _ => st.numRounds i + 1
              else st.numRounds i
            calls := st.calls ++ [rc] }

/-- Run `t` common rounds of Step B starting from `BlockGameState.init`. -/
def stepBRunRounds (cfg : CoreParams) (route : RouterFn) (G : Graph) (X : Finset ℕ) (vs : List ℕ)
    (b k z : ℕ) (subCore : Graph → Finset ℕ → CoreResult) : ℕ → Finset ℕ ⊕ BlockGameState
  | 0 => Sum.inr BlockGameState.init
  | t + 1 =>
      match stepBRunRounds cfg route G X vs b k z subCore t with
      | Sum.inl U => Sum.inl U
      | Sum.inr st => stepBRound cfg route G X vs b k z subCore st

/-- Full Step B for `q ≥ 2`: run `49 * cfg.L + 1` game rounds, then one combined routing call
injecting each block complement into its saved expanding subset. Returns either a router cut `U`
or the list of valid `RoutedCall`s from Step B. -/
def stepB (cfg : CoreParams) (route : RouterFn) (G : Graph) (X : Finset ℕ) (vs : List ℕ)
    (b k z : ℕ) (subCore : Graph → Finset ℕ → CoreResult) : Finset ℕ ⊕ List RoutedCall :=
  match stepBRunRounds cfg route G X vs b k z subCore (49 * cfg.L + 1) with
  | Sum.inl U => Sum.inl U
  | Sum.inr st =>
      let injPairs := (List.range k).map fun i => (blockSet vs b i \ st.savedS i, st.savedS i)
      match route G X injPairs cfg.Δ cfg.L 100 z with
      | .cut U => Sum.inl U
      | .matched matchings emb =>
          let rc : RoutedCall := ⟨matchings.flatten, emb, completeBatchFake injPairs matchings⟩
          Sum.inr (st.calls ++ [rc])

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Helper lemmas for cuts, degrees, and disjoint blocks -/

/-- The cut of a single list `l ∈ ls` is at most the cut of `ls.flatten`. -/
theorem cutIn_le_flatten (n : ℕ) {ls : List (List (ℕ × ℕ))} {l : List (ℕ × ℕ)} (hl : l ∈ ls)
    (X S : Finset ℕ) : (Graph.mk n l).cutIn X S ≤ (Graph.mk n ls.flatten).cutIn X S := by
  induction ls with
  | nil => simp at hl
  | cons a rest ih =>
    rw [List.flatten_cons, cutIn_append]
    rcases List.mem_cons.mp hl with rfl | hrest
    · omega
    · have := ih hrest; omega

/-- A witness built from `t` perfect matchings on `B` is loopless and has degree at most `t` on
`B`. -/
private lemma witnessEdges_loopless_deg_le {n t : ℕ} {B : Finset ℕ} {M : ℕ → List (ℕ × ℕ)}
    (hM : ∀ j < t, IsPerfectMatchingOn B (M j)) :
    (∀ e ∈ (Graph.mk n (witnessEdges M t)).inside B, e.1 ≠ e.2) ∧
    (∀ v ∈ B, (Graph.mk n (witnessEdges M t)).degIn B v ≤ t) := by
  induction t with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro e he; simp [witnessEdges, Graph.inside] at he
    · intro v _; simp [witnessEdges, Graph.degIn, Graph.inside]
  | succ t ih =>
    have hprev := ih fun j hj => hM j (Nat.lt_succ_of_lt hj)
    have ht := hM t (Nat.lt_succ_self t)
    have hnd := ht.2.1
    have hloop_t : ∀ e ∈ M t, e.1 ≠ e.2 := by
      have hgen : ∀ (L : List (ℕ × ℕ)), (L.flatMap fun e => [e.1, e.2]).Nodup →
          ∀ e ∈ L, e.1 ≠ e.2 := by
        intro L
        induction L with
        | nil => intro _ e he; simp at he
        | cons p rest ihr =>
          rcases p with ⟨a, b⟩
          intro hnd' e he
          simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons] at hnd'
          rcases List.mem_cons.mp he with rfl | hrest
          · intro heq; dsimp only at heq; apply hnd'.1; rw [heq]; exact List.mem_cons_self
          · exact ihr hnd'.2.2 e hrest
      exact hgen (M t) hnd
    have hdeg_t : ∀ v ∈ B, (Graph.mk n (M t)).degIn B v ≤ 1 := by
      intro v _
      have h1 : ((Graph.mk n (M t)).inside B |>.filter fun e => e.1 = v).length ≤
          ((M t).filter fun e => e.1 = v).length := by
        unfold Graph.inside
        rw [List.filter_filter]
        exact length_filter_le_of_imp (M t) fun e _ h => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢; exact h.1
      have h2 : ((Graph.mk n (M t)).inside B |>.filter fun e => e.2 = v).length ≤
          ((M t).filter fun e => e.2 = v).length := by
        unfold Graph.inside
        rw [List.filter_filter]
        exact length_filter_le_of_imp (M t) fun e _ h => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢; exact h.1
      have hsum : ((M t).filter fun e => e.1 = v).length + ((M t).filter fun e => e.2 = v).length =
          ((M t).flatMap fun e => [e.1, e.2]).count v := by
        clear h1 h2 hnd hloop_t ht hprev ih hM
        induction M t with
        | nil => simp
        | cons p rest ihr =>
          rcases p with ⟨a, b⟩
          simp only [List.filter_cons, List.flatMap_cons, List.cons_append, List.nil_append,
            List.count_cons, beq_iff_eq]
          by_cases ha : a = v <;> by_cases hb : b = v <;> simp [ha, hb] <;> omega
      have hcnt : ((M t).flatMap fun e => [e.1, e.2]).count v ≤ 1 :=
        List.nodup_iff_count_le_one.mp hnd v
      unfold Graph.degIn
      omega
    refine ⟨?_, ?_⟩
    · intro e he
      rw [mem_inside_iff] at he
      rw [witnessEdges] at he
      rcases List.mem_append.mp he.1 with h1 | h2
      · exact hprev.1 e (mem_inside_iff.mpr ⟨h1, he.2.1, he.2.2⟩)
      · exact hloop_t e h2
    · intro v hv
      rw [witnessEdges, degIn_append]
      have h1 := hprev.2 v hv
      have h2 := hdeg_t v hv
      omega

/-- Modifying `M` at index `t` does not change `witnessEdges M j` for `j ≤ t`. -/
private lemma witnessEdges_congr_lt {M₁ M₂ : ℕ → List (ℕ × ℕ)} {k : ℕ}
    (h : ∀ j < k, M₁ j = M₂ j) : witnessEdges M₁ k = witnessEdges M₂ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [witnessEdges, witnessEdges, ih (fun j hj => h j (Nat.lt_succ_of_lt hj)),
      h k (Nat.lt_succ_self k)]

/-- Distinct full blocks are disjoint. -/
theorem disjoint_blockSet {vs : List ℕ} (hnd : vs.Nodup) {b i₁ i₂ : ℕ} (hb : 0 < b)
    (h1 : i₁ < numFullBlocks vs b) (h2 : i₂ < numFullBlocks vs b) (hne : i₁ ≠ i₂) :
    Disjoint (blockSet vs b i₁) (blockSet vs b i₂) := by
  rw [← filter_blockOf_eq_blockSet hnd hb h1, ← filter_blockOf_eq_blockSet hnd hb h2,
    Finset.disjoint_left]
  intro v hv1 hv2
  simp only [Finset.mem_filter] at hv1 hv2
  exact hne (hv1.2.symm.trans hv2.2)

/-- Every full block is a subset of `vs.toFinset`. -/
theorem blockSet_subset_toFinset (vs : List ℕ) (b i : ℕ) :
    blockSet vs b i ⊆ vs.toFinset := by
  intro v hv
  unfold blockSet blockList at hv
  rw [List.mem_toFinset] at hv ⊢
  exact List.mem_of_mem_drop (List.mem_of_mem_take hv)

/-- Helper: pairs built from disjoint subsets of distinct blocks form `ValidTerminalPairs`. -/
theorem validTerminalPairs_of_distinct_blocks {vs : List ℕ} (hnd : vs.Nodup) {b : ℕ} (hb : 0 < b)
    {rpairs : List (ℕ × (Finset ℕ × Finset ℕ))}
    (hids_nd : (rpairs.map Prod.fst).Nodup)
    (hspec : ∀ ip ∈ rpairs, ip.1 < numFullBlocks vs b ∧
      ip.2.1 ⊆ blockSet vs b ip.1 ∧ ip.2.2 ⊆ blockSet vs b ip.1 ∧
      Disjoint ip.2.1 ip.2.2 ∧ ip.2.1.card ≤ ip.2.2.card) :
    ValidTerminalPairs vs.toFinset (rpairs.map Prod.snd) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨ip, hip, rfl⟩ := List.mem_map.mp hp
    obtain ⟨_, h1, h2, _, hle⟩ := hspec ip hip
    exact ⟨h1.trans (blockSet_subset_toFinset vs b ip.1),
      h2.trans (blockSet_subset_toFinset vs b ip.1), hle⟩
  · induction rpairs with
    | nil => simp
    | cons ip rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hids_nd
      have hip := hspec ip List.mem_cons_self
      have hrest : ∀ q ∈ rest, q.1 < numFullBlocks vs b ∧
          q.2.1 ⊆ blockSet vs b q.1 ∧ q.2.2 ⊆ blockSet vs b q.1 ∧
          Disjoint q.2.1 q.2.2 ∧ q.2.1.card ≤ q.2.2.card :=
        fun q hq => hspec q (List.mem_cons_of_mem _ hq)
      simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append,
        List.pairwise_cons]
      refine ⟨?_, ?_, ih hids_nd.2 hrest⟩
      · intro S hS
        rcases List.mem_cons.mp hS with rfl | hfm
        · exact hip.2.2.2.1
        · obtain ⟨p, hp, hpS⟩ := List.mem_flatMap.mp hfm
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          have hqsp := hrest q hq
          have hne : ip.1 ≠ q.1 := fun h => hids_nd.1 (List.mem_map.mpr ⟨q, hq, h.symm⟩)
          have hdisj := disjoint_blockSet hnd hb hip.1 hqsp.1 hne
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpS
          rcases hpS with rfl | rfl
          · exact Disjoint.mono hip.2.1 hqsp.2.1 hdisj
          · exact Disjoint.mono hip.2.1 hqsp.2.2.1 hdisj
      · intro S hS
        obtain ⟨p, hp, hpS⟩ := List.mem_flatMap.mp hS
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have hqsp := hrest q hq
        have hne : ip.1 ≠ q.1 := fun h => hids_nd.1 (List.mem_map.mpr ⟨q, hq, h.symm⟩)
        have hdisj := disjoint_blockSet hnd hb hip.1 hqsp.1 hne
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpS
        rcases hpS with rfl | rfl
        · exact Disjoint.mono hip.2.2.1 hqsp.2.1 hdisj
        · exact Disjoint.mono hip.2.2.1 hqsp.2.2.1 hdisj

/-! ### Invariant for Step B's parallel game rounds -/

/-- Loop invariant after `t` rounds of Step B (`t ≤ 49 * cfg.L + 1`). -/
private structure StepBInv (cfg : CoreParams) (q : ℕ) (G : Graph) (X : Finset ℕ) (vs : List ℕ)
    (b k z t : ℕ) (st : BlockGameState) : Prop where
  calls_len : st.calls.length ≤ t
  calls_valid : ∀ c ∈ st.calls, c.Valid G X (routeCong cfg.Δ 100 cfg.L) z
  numRounds_le : ∀ i < k, st.numRounds i ≤ t
  active_numRounds : ∀ i < k, st.active i = true → st.numRounds i = t
  rounds_pm : ∀ i < k, ∀ j < st.numRounds i,
    IsPerfectMatchingOn (blockSet vs b i) (st.rounds i j)
  rounds_cut : ∀ i < k, ∀ j < st.numRounds i,
    ∃ C ⊆ blockSet vs b i,
      (blockSet vs b i).card ≤ 4 * C.card ∧
      (∀ e ∈ st.rounds i j, ¬ (e.1 ∈ C ∧ e.2 ∈ C)) ∧
      100 * (Graph.mk G.n (witnessEdges (st.rounds i) j)).cutIn (blockSet vs b i) C ≤
        (blockSet vs b i).card
  inactive_exp : ∀ i < k, st.active i = false →
    st.savedS i ⊆ blockSet vs b i ∧
    (blockSet vs b i).card ≤ 2 * (st.savedS i).card ∧
    (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))).IsExpansionExpanderOn
      (st.savedS i) (1 / (cfg.P (q - 1) : ℝ))
  sub_cut : ∀ i < k, ∀ Y S : Finset ℕ,
    (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))).cutIn Y S ≤
      (Graph.mk G.n (callsWitnessEdges st.calls)).cutIn Y S

private lemma stepBInv_init (cfg : CoreParams) (q : ℕ) (G : Graph) (X : Finset ℕ) (vs : List ℕ)
    (b k z : ℕ) : StepBInv cfg q G X vs b k z 0 BlockGameState.init where
  calls_len := by simp [BlockGameState.init]
  calls_valid := by simp [BlockGameState.init]
  numRounds_le := by simp [BlockGameState.init]
  active_numRounds := by simp [BlockGameState.init]
  rounds_pm := by simp [BlockGameState.init]
  rounds_cut := by simp [BlockGameState.init]
  inactive_exp := by simp [BlockGameState.init]
  sub_cut := by simp [BlockGameState.init, witnessEdges, Graph.cutIn, Graph.inside]

private lemma filterMap_range_fst_nodup {α : Type*} (k : ℕ) (f : ℕ → Option (ℕ × α))
    (hf : ∀ i p, f i = some p → p.1 = i) :
    (((List.range k).filterMap f).map Prod.fst).Nodup := by
  have hsub : List.Sublist (((List.range k).filterMap f).map Prod.fst) (List.range k) := by
    have hgen : ∀ (l : List ℕ), List.Sublist ((l.filterMap f).map Prod.fst) l := by
      intro l
      induction l with
      | nil => simp
      | cons a rest ih =>
        rw [List.filterMap_cons]
        cases hfa : f a with
        | none => exact List.Sublist.cons a ih
        | some p =>
          rw [List.map_cons, hf a p hfa]
          exact List.Sublist.cons_cons a ih
    exact hgen (List.range k)
  exact hsub.nodup List.nodup_range

private lemma mem_activeCutPairs_iff {G : Graph} {vs : List ℕ} {b k : ℕ}
    {subCore : Graph → Finset ℕ → CoreResult} {st : BlockGameState} {i : ℕ}
    {p : Finset ℕ × Finset ℕ} :
    (i, p) ∈ activeCutPairs G vs b k subCore st ↔
      i < k ∧ st.active i = true ∧
      ∃ U, subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
          (blockSet vs b i) = .cut U ∧
        p = (padToHalf (blockSet vs b i) (smallerSide (blockSet vs b i) U),
             blockSet vs b i \ padToHalf (blockSet vs b i) (smallerSide (blockSet vs b i) U)) := by
  unfold activeCutPairs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, hsome⟩
    have hjk : j < k := List.mem_range.mp hj
    by_cases hact : st.active j = true
    · simp only [hact, ↓reduceIte] at hsome
      cases hsc : subCore (Graph.mk G.n (witnessEdges (st.rounds j) (st.numRounds j)))
          (blockSet vs b j) with
      | expander S => simp [hsc] at hsome
      | cut U =>
        simp only [hsc, Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨rfl, rfl⟩ := hsome
        exact ⟨hjk, hact, U, hsc, rfl⟩
    · simp [hact] at hsome
  · rintro ⟨hik, hact, U, hsc, rfl⟩
    refine ⟨i, List.mem_range.mpr hik, ?_⟩
    simp [hact, hsc]

private lemma stepBRound_spec {cfg : CoreParams} {r q : ℕ} (hcfg : CoreParamsValid cfg r)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    {G : Graph} {X : Finset ℕ} {vs : List ℕ} {b z t : ℕ}
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ cfg.Δ) (hXL : X.card < 2 ^ cfg.L)
    (hnd : vs.Nodup) (hvs : vs.toFinset = X)
    (hb_pos : 0 < b) (hb_even : Even b) (hb_le : b ≤ cfg.N ^ (q - 1))
    (ht : t ≤ 49 * cfg.L)
    {subCore : Graph → Finset ℕ → CoreResult}
    (hsubCore : ∀ W Y, Y ⊆ Finset.range W.n → W.IsValid → (∀ e ∈ W.inside Y, e.1 ≠ e.2) →
      Y.card ≤ cfg.N ^ (q - 1) → (∀ v ∈ Y, W.degIn Y v ≤ cfg.Δ) →
      CoreSpec cfg (q - 1) W Y (subCore W Y))
    {st : BlockGameState} (hinv : StepBInv cfg q G X vs b (numFullBlocks vs b) z t st) :
    match stepBRound cfg route G X vs b (numFullBlocks vs b) z subCore st with
    | Sum.inl U => RouteCutSpec G X 100 z U
    | Sum.inr st' => StepBInv cfg q G X vs b (numFullBlocks vs b) z (t + 1) st' := by
  set k := numFullBlocks vs b
  set rpairs := activeCutPairs G vs b k subCore st
  set pairs := rpairs.map Prod.snd
  -- Every active block `i < k` meets the precondition of `subCore`.
  have hsc_spec : ∀ i < k,
      CoreSpec cfg (q - 1) (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
        (blockSet vs b i)
        (subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
          (blockSet vs b i)) := by
    intro i hi
    have hBsub : blockSet vs b i ⊆ Finset.range G.n :=
      (blockSet_subset_toFinset vs b i).trans (hvs.symm ▸ hX)
    have hBcard : (blockSet vs b i).card = b := card_blockSet hnd hi
    have hwd := witnessEdges_loopless_deg_le (n := G.n) (hinv.rounds_pm i hi)
    have hWvalid : (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))).IsValid := by
      have hgen : ∀ m, (∀ j < m, IsPerfectMatchingOn (blockSet vs b i) (st.rounds i j)) →
          ∀ e ∈ witnessEdges (st.rounds i) m, e.1 < G.n ∧ e.2 < G.n := by
        intro m hm e he
        induction m with
        | zero => simp [witnessEdges] at he
        | succ m ihm =>
          rw [witnessEdges] at he
          rcases List.mem_append.mp he with h1 | h2
          · exact ihm (fun j hj => hm j (Nat.lt_succ_of_lt hj)) h1
          · have hmem := (hm m (Nat.lt_succ_self m)).1 e h2
            exact ⟨Finset.mem_range.mp (hBsub hmem.1), Finset.mem_range.mp (hBsub hmem.2)⟩
      exact hgen (st.numRounds i) (hinv.rounds_pm i hi)
    have hnr := hinv.numRounds_le i hi
    have hΔ := hcfg.hΔ
    refine hsubCore _ _ hBsub hWvalid hwd.1 (by rw [hBcard]; exact hb_le)
      (fun v hv => le_trans (hwd.2 v hv) (by omega))
  unfold stepBRound
  dsimp only
  by_cases hemp : (activeCutPairs G vs b k subCore st).isEmpty = true
  · simp only [hemp, ↓reduceIte]
    have hnil : rpairs = [] := List.isEmpty_iff.mp hemp
    -- Every active block returned `.expander`.
    have hexp_all : ∀ i < k, st.active i = true →
        ∃ S, subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
            (blockSet vs b i) = .expander S := by
      intro i hi hact
      cases hsc : subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
          (blockSet vs b i) with
      | expander S => exact ⟨S, rfl⟩
      | cut U =>
        exfalso
        have hmem : (i, (padToHalf (blockSet vs b i) (smallerSide (blockSet vs b i) U),
            blockSet vs b i \ padToHalf (blockSet vs b i) (smallerSide (blockSet vs b i) U))) ∈
            rpairs := mem_activeCutPairs_iff.mpr ⟨hi, hact, U, hsc, rfl⟩
        rw [hnil] at hmem
        simp at hmem
    refine ⟨Nat.le_succ_of_le hinv.calls_len, hinv.calls_valid,
      fun i hi => Nat.le_succ_of_le (hinv.numRounds_le i hi), ?_, hinv.rounds_pm, hinv.rounds_cut,
      ?_, hinv.sub_cut⟩
    · intro i hi hact
      simp [hi] at hact
    · intro i hi _
      by_cases hact : st.active i = true
      · obtain ⟨S, hS⟩ := hexp_all i hi hact
        have hcs := hsc_spec i hi
        rw [hS] at hcs
        simp only [hi, decide_true, hact, Bool.and_self, ↓reduceIte, hS]
        exact hcs
      · have hactf : st.active i = false := Bool.eq_false_iff.mpr hact
        simp only [hi, hactf, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact hinv.inactive_exp i hi hactf
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
    -- Show `ValidTerminalPairs X pairs`.
    have hids_nd : (rpairs.map Prod.fst).Nodup := by
      refine filterMap_range_fst_nodup k _ fun i p hp => ?_
      by_cases hact : st.active i = true
      · simp only [hact, ↓reduceIte] at hp
        cases hsc : subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
            (blockSet vs b i) with
        | expander _ => simp [hsc] at hp
        | cut U => simp only [hsc, Option.some.injEq] at hp; rw [← hp]
      · simp [hact] at hp
    have hpairs_valid : ValidTerminalPairs X pairs := by
      rw [← hvs]
      refine validTerminalPairs_of_distinct_blocks hnd hb_pos hids_nd ?_
      intro ⟨i, p⟩ hip
      obtain ⟨hik, hact, U, hsc, rfl⟩ := mem_activeCutPairs_iff.mp hip
      have hcs := hsc_spec i hik
      rw [hsc] at hcs
      have hsm := smallerSide_spec hcs.1 hcs.2.1 hcs.2.2.1 hcs.2.2.2
      have hBcard : (blockSet vs b i).card = b := card_blockSet hnd hik
      have hpad := padToHalf_spec hsm.1 hsm.2.1 (by rw [hBcard]; exact hb_even)
      exact ⟨hik, hpad.2.1, Finset.sdiff_subset, disjoint_sdiff_self_right, le_of_eq hpad.2.2.2.symm⟩
    have hrspec := hroute.spec G X pairs cfg.Δ cfg.L 100 z hX hGloop hcfg.hΔ_pos hdegG hcfg.hL
      hXL (by decide) hpairs_valid
    cases hres : route G X pairs cfg.Δ cfg.L 100 z with
    | cut U =>
      rw [hres] at hrspec
      exact hrspec
    | matched matchings emb =>
      rw [hres] at hrspec
      dsimp only
      have hrc_valid : RoutedCall.Valid G X (routeCong cfg.Δ 100 cfg.L) z
          ⟨matchings.flatten, emb, completeBatchFake pairs matchings⟩ :=
        routedCall_valid_of_matched hpairs_valid hrspec
      set rc : RoutedCall := ⟨matchings.flatten, emb, completeBatchFake pairs matchings⟩
      set ids := rpairs.map Prod.fst
      let newM : ℕ → List (ℕ × ℕ) := fun i =>
        let idx := ids.idxOf i
        let p := pairs.getD idx (∅, ∅)
        let m := matchings.getD idx []
        m ++ completeMatchingFake p.1 p.2 m
      -- Properties of `newM i` whenever `i < k`, `st.active i = true`, and `subCore` returned `.cut U`.
      have hnewM_spec : ∀ i (hi : i < k) (hact : st.active i = true) (U : Finset ℕ)
          (hsc : subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
            (blockSet vs b i) = .cut U),
          IsPerfectMatchingOn (blockSet vs b i) (newM i) ∧
          (∀ e ∈ newM i, ¬ (e.1 ∈ smallerSide (blockSet vs b i) U ∧
            e.2 ∈ smallerSide (blockSet vs b i) U)) ∧
          (∀ Y S : Finset ℕ, (Graph.mk G.n (newM i)).cutIn Y S ≤
            (Graph.mk G.n (rc.routed ++ rc.fake)).cutIn Y S) := by
        intro i hi hact U hsc
        set B := blockSet vs b i
        set C := smallerSide B U
        set C' := padToHalf B C
        have hcs := hsc_spec i hi
        rw [hsc] at hcs
        have hsm := smallerSide_spec hcs.1 hcs.2.1 hcs.2.2.1 hcs.2.2.2
        have hBcard : B.card = b := card_blockSet hnd hi
        have hpad := padToHalf_spec hsm.1 hsm.2.1 (by rw [hBcard]; exact hb_even)
        have hmem_rp : (i, (C', B \ C')) ∈ rpairs :=
          mem_activeCutPairs_iff.mpr ⟨hi, hact, U, hsc, rfl⟩
        have hi_ids : i ∈ ids := List.mem_map.mpr ⟨(i, (C', B \ C')), hmem_rp, rfl⟩
        set idx := ids.idxOf i
        have hidx_lt : idx < ids.length := List.idxOf_lt_length_of_mem hi_ids
        have hidx_rp : idx < rpairs.length := by simpa [ids] using hidx_lt
        have hidx_pairs : idx < pairs.length := by simpa [pairs] using hidx_rp
        have hget_id : (rpairs[idx]'hidx_rp).1 = i := by
          have h1 : ids[idx]'hidx_lt = i := List.getElem_idxOf hidx_lt
          simpa [ids] using h1
        -- Because `ids` is `Nodup`, `rpairs[idx]` must be `(i, (C', B \ C'))`.
        have hget_pair : pairs.getD idx (∅, ∅) = (C', B \ C') := by
          rw [List.getD_eq_getElem _ _ hidx_pairs]
          have hmem_get : rpairs[idx]'hidx_rp ∈ rpairs := List.getElem_mem hidx_rp
          obtain ⟨_, _, U', hsc', hp_eq⟩ := mem_activeCutPairs_iff.mp
            (show (i, (rpairs[idx]'hidx_rp).2) ∈ rpairs by rw [← hget_id]; exact hmem_get)
          rw [hsc] at hsc'
          injection hsc' with hUeq
          subst hUeq
          simpa [pairs] using hp_eq
        have hmspec := hrspec.2.1 idx hidx_pairs
        dsimp only at hmspec
        have hp_eq' : pairs[idx]'hidx_pairs = (C', B \ C') := by
          rw [← List.getD_eq_getElem pairs (∅, ∅) hidx_pairs]; exact hget_pair
        rw [hp_eq'] at hmspec
        set m := matchings.getD idx []
        have hnewM_eq : newM i = m ++ completeMatchingFake C' (B \ C') m := by
          dsimp only [newM, idx, m]; rw [hget_pair]
        rw [hnewM_eq]
        have hunion : C' ∪ (B \ C') = B := Finset.union_sdiff_of_subset hpad.2.1
        have hpm := isPerfectMatchingOn_complete disjoint_sdiff_self_right hunion
          hpad.2.2.2.symm hmspec.1 hmspec.2.1 hmspec.2.2
        have hcf := completeMatchingFake_spec (le_of_eq hpad.2.2.2.symm)
          hmspec.1 hmspec.2.1 hmspec.2.2
        have hdisjC : ∀ e ∈ m ++ completeMatchingFake C' (B \ C') m, ¬ (e.1 ∈ C ∧ e.2 ∈ C) := by
          intro e he ⟨_, h2⟩
          have he2 : e.2 ∈ B \ C' := by
            rcases List.mem_append.mp he with h | h
            · exact (hmspec.1 e h).2
            · exact (hcf.2.1 e h).2
          exact (Finset.mem_sdiff.mp he2).2 (hpad.1 h2)
        have hcut_le : ∀ Y S : Finset ℕ,
            (Graph.mk G.n (m ++ completeMatchingFake C' (B \ C') m)).cutIn Y S ≤
              (Graph.mk G.n (rc.routed ++ rc.fake)).cutIn Y S := by
          intro Y S
          rw [cutIn_append, cutIn_append]
          have hidx_m : idx < matchings.length := hrspec.1.symm ▸ hidx_pairs
          have hm_mem : m ∈ matchings := by
            dsimp only [m]
            rw [List.getD_eq_getElem _ _ hidx_m]
            exact List.getElem_mem hidx_m
          have h1 : (Graph.mk G.n m).cutIn Y S ≤ (Graph.mk G.n rc.routed).cutIn Y S :=
            cutIn_le_flatten G.n hm_mem Y S
          have hfake_mem : completeMatchingFake C' (B \ C') m ∈
              List.zipWith (fun p M => completeMatchingFake p.1 p.2 M) pairs matchings := by
            have hzw_len : (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M)
                pairs matchings).length = pairs.length := by
              rw [List.length_zipWith, hrspec.1, min_self]
            have hidx_zw : idx < (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M)
                pairs matchings).length := hzw_len.symm ▸ hidx_pairs
            have hget_zw : (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M)
                pairs matchings)[idx]'hidx_zw = completeMatchingFake C' (B \ C') m := by
              rw [List.getElem_zipWith, hp_eq']
              dsimp only [m]
              rw [List.getD_eq_getElem _ _ hidx_m]
            rw [← hget_zw]
            exact List.getElem_mem hidx_zw
          have h2 : (Graph.mk G.n (completeMatchingFake C' (B \ C') m)).cutIn Y S ≤
              (Graph.mk G.n rc.fake).cutIn Y S := cutIn_le_flatten G.n hfake_mem Y S
          omega
        exact ⟨hpm, hdisjC, hcut_le⟩
      -- Now verify all 8 fields of `StepBInv` at `t + 1`.
      let rounds' : ℕ → ℕ → List (ℕ × ℕ) := fun i j =>
        if (decide (i < k) && st.active i && decide (j = st.numRounds i)) = true then
          match subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
              (blockSet vs b i) with
          | .expander _ => st.rounds i j
          | .cut _ => newM i
        else st.rounds i j
      have hrounds'_lt : ∀ i j, j < st.numRounds i → rounds' i j = st.rounds i j := fun i j hj => by
        dsimp only [rounds']
        have hne : j ≠ st.numRounds i := by omega
        simp [hne]
      have hw_eq : ∀ i j, j ≤ st.numRounds i →
          witnessEdges (rounds' i) j = witnessEdges (st.rounds i) j := fun i j hj =>
        witnessEdges_congr_lt fun j' hj' => hrounds'_lt i j' (lt_of_lt_of_le hj' hj)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.length_append, List.length_singleton]; exact Nat.add_le_add_right hinv.calls_len 1
      · intro c hc
        rcases List.mem_append.mp hc with h1 | h2
        · exact hinv.calls_valid c h1
        · rw [List.mem_singleton.mp h2]; exact hrc_valid
      · intro i hi
        by_cases hact : st.active i = true
        · simp only [hi, decide_true, hact, Bool.and_self, ↓reduceIte]
          cases subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
              (blockSet vs b i) with
          | expander _ => exact Nat.le_succ_of_le (hinv.numRounds_le i hi)
          | cut _ => exact Nat.add_le_add_right (hinv.numRounds_le i hi) 1
        · have hactf : st.active i = false := Bool.eq_false_iff.mpr hact
          simp only [hi, decide_true, hactf, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact Nat.le_succ_of_le (hinv.numRounds_le i hi)
      · intro i hi hact'
        by_cases hact : st.active i = true
        · simp only [hi, decide_true, hact, Bool.and_self, ↓reduceIte] at hact' ⊢
          cases hsc : subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
              (blockSet vs b i) with
          | expander _ => simp [hsc] at hact'
          | cut _ =>
            rw [hinv.active_numRounds i hi hact]
        · have hactf : st.active i = false := Bool.eq_false_iff.mpr hact
          simp [hi, hactf] at hact'
      · intro i hi j hj
        change IsPerfectMatchingOn (blockSet vs b i) (rounds' i j)
        by_cases hact : st.active i = true
        · simp only [hi, decide_true, hact, Bool.and_self, ↓reduceIte] at hj
          cases hsc : subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
              (blockSet vs b i) with
          | expander _ =>
            simp only [hsc] at hj
            rw [hrounds'_lt i j hj]
            exact hinv.rounds_pm i hi j hj
          | cut U =>
            simp only [hsc] at hj
            by_cases hjeq : j = st.numRounds i
            · subst hjeq
              have hr : rounds' i (st.numRounds i) = newM i := by
                dsimp only [rounds']; simp [hi, hact, hsc]
              rw [hr]
              exact (hnewM_spec i hi hact U hsc).1
            · rw [hrounds'_lt i j (by omega)]
              exact hinv.rounds_pm i hi j (by omega)
        · have hactf : st.active i = false := Bool.eq_false_iff.mpr hact
          simp only [hi, decide_true, hactf, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hj
          rw [hrounds'_lt i j hj]
          exact hinv.rounds_pm i hi j hj
      · intro i hi j hj
        change ∃ C ⊆ blockSet vs b i,
          (blockSet vs b i).card ≤ 4 * C.card ∧
          (∀ e ∈ rounds' i j, ¬ (e.1 ∈ C ∧ e.2 ∈ C)) ∧
          100 * (Graph.mk G.n (witnessEdges (rounds' i) j)).cutIn (blockSet vs b i) C ≤
            (blockSet vs b i).card
        by_cases hact : st.active i = true
        · simp only [hi, decide_true, hact, Bool.and_self, ↓reduceIte] at hj
          cases hsc : subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
              (blockSet vs b i) with
          | expander _ =>
            simp only [hsc] at hj
            rw [hw_eq i j (le_of_lt hj), hrounds'_lt i j hj]
            exact hinv.rounds_cut i hi j hj
          | cut U =>
            simp only [hsc] at hj
            rw [hw_eq i j (by omega)]
            by_cases hjeq : j = st.numRounds i
            · subst hjeq
              have hr : rounds' i (st.numRounds i) = newM i := by
                dsimp only [rounds']; simp [hi, hact, hsc]
              rw [hr]
              have hcs := hsc_spec i hi
              rw [hsc] at hcs
              have hsm := smallerSide_spec hcs.1 hcs.2.1 hcs.2.2.1 hcs.2.2.2
              exact ⟨smallerSide (blockSet vs b i) U, hsm.1, hsm.2.2.1,
                (hnewM_spec i hi hact U hsc).2.1, hsm.2.2.2⟩
            · rw [hrounds'_lt i j (by omega)]
              exact hinv.rounds_cut i hi j (by omega)
        · have hactf : st.active i = false := Bool.eq_false_iff.mpr hact
          simp only [hi, decide_true, hactf, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hj
          rw [hw_eq i j (le_of_lt hj), hrounds'_lt i j hj]
          exact hinv.rounds_cut i hi j hj
      · intro i hi hact'
        change _ ∧ _ ∧ (Graph.mk G.n (witnessEdges (rounds' i) _)).IsExpansionExpanderOn _ _
        by_cases hact : st.active i = true
        · simp only [hi, decide_true, hact, Bool.and_self, ↓reduceIte] at hact' ⊢
          cases hsc : subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
              (blockSet vs b i) with
          | cut _ => simp [hsc] at hact'
          | expander S =>
            rw [hw_eq i (st.numRounds i) (le_refl _)]
            have hcs := hsc_spec i hi
            rw [hsc] at hcs
            exact hcs
        · have hactf : st.active i = false := Bool.eq_false_iff.mpr hact
          simp only [hi, decide_true, hactf, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          rw [hw_eq i (st.numRounds i) (le_refl _)]
          exact hinv.inactive_exp i hi hactf
      · intro i hi Y S
        have hcw : callsWitnessEdges (st.calls ++ [rc]) =
            callsWitnessEdges st.calls ++ (rc.routed ++ rc.fake) := by
          simp [callsWitnessEdges]
        rw [hcw, cutIn_append]
        change (Graph.mk G.n (witnessEdges (rounds' i) _)).cutIn Y S ≤ _
        by_cases hact : st.active i = true
        · simp only [hi, decide_true, hact, Bool.and_self, ↓reduceIte]
          cases hsc : subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
              (blockSet vs b i) with
          | expander _ =>
            rw [hw_eq i (st.numRounds i) (le_refl _)]
            exact le_trans (hinv.sub_cut i hi Y S) (Nat.le_add_right _ _)
          | cut U =>
            rw [witnessEdges, hw_eq i (st.numRounds i) (le_refl _)]
            have hr : rounds' i (st.numRounds i) = newM i := by
              dsimp only [rounds']; simp [hi, hact, hsc]
            rw [hr, cutIn_append]
            exact Nat.add_le_add (hinv.sub_cut i hi Y S) ((hnewM_spec i hi hact U hsc).2.2 Y S)
        · have hactf : st.active i = false := Bool.eq_false_iff.mpr hact
          simp only [hi, decide_true, hactf, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          rw [hw_eq i (st.numRounds i) (le_refl _)]
          exact le_trans (hinv.sub_cut i hi Y S) (Nat.le_add_right _ _)

/-- **Step B specification**: either `stepB` returns a router cut `U`, or it returns a list of at
most `49 * cfg.L + 2` valid `RoutedCall`s whose combined witness graph `callsWitnessEdges calls`
gives every full block `blockSet vs b i` (`i < numFullBlocks vs b`) edge expansion at least
`1 / (2 * P (q - 1))`. -/
theorem stepB_spec {cfg : CoreParams} {r q : ℕ} (hcfg : CoreParamsValid cfg r)
    (hq2 : 2 ≤ q) (hqr : q ≤ r)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    {G : Graph} {X : Finset ℕ} {vs : List ℕ} {b z : ℕ}
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ cfg.Δ) (hXL : X.card < 2 ^ cfg.L)
    (hnd : vs.Nodup) (hvs : vs.toFinset = X)
    (hb_pos : 0 < b) (hb_even : Even b) (hb_le : b ≤ cfg.N ^ (q - 1))
    {subCore : Graph → Finset ℕ → CoreResult}
    (hsubCore : ∀ W Y, Y ⊆ Finset.range W.n → W.IsValid → (∀ e ∈ W.inside Y, e.1 ≠ e.2) →
      Y.card ≤ cfg.N ^ (q - 1) → (∀ v ∈ Y, W.degIn Y v ≤ cfg.Δ) →
      CoreSpec cfg (q - 1) W Y (subCore W Y)) :
    match stepB cfg route G X vs b (numFullBlocks vs b) z subCore with
    | Sum.inl U => RouteCutSpec G X 100 z U
    | Sum.inr calls =>
        calls.length ≤ 49 * cfg.L + 2 ∧
        (∀ c ∈ calls, c.Valid G X (routeCong cfg.Δ 100 cfg.L) z) ∧
        (∀ i < numFullBlocks vs b,
          (Graph.mk G.n (callsWitnessEdges calls)).IsExpansionExpanderOn (blockSet vs b i)
            (1 / (2 * (cfg.P (q - 1) : ℝ)))) := by
  set k := numFullBlocks vs b
  -- First prove the loop invariant up to `t = 49 * cfg.L + 1`.
  have hrun : ∀ t ≤ 49 * cfg.L + 1,
      match stepBRunRounds cfg route G X vs b k z subCore t with
      | Sum.inl U => RouteCutSpec G X 100 z U
      | Sum.inr st => StepBInv cfg q G X vs b k z t st := by
    intro t ht
    induction t with
    | zero => exact stepBInv_init cfg q G X vs b k z
    | succ t ih =>
      have hprev := ih (Nat.le_of_succ_le ht)
      unfold stepBRunRounds
      cases hstep : stepBRunRounds cfg route G X vs b k z subCore t with
      | inl U => rw [hstep] at hprev; exact hprev
      | inr st =>
        rw [hstep] at hprev
        exact stepBRound_spec hcfg hroute hX hGloop hdegG hXL hnd hvs
          hb_pos hb_even hb_le (by omega) hsubCore hprev
  have hfinal := hrun (49 * cfg.L + 1) (le_refl _)
  unfold stepB
  cases hst : stepBRunRounds cfg route G X vs b k z subCore (49 * cfg.L + 1) with
  | inl U =>
    rw [hst] at hfinal
    exact hfinal
  | inr st =>
    rw [hst] at hfinal
    dsimp only at hfinal ⊢
    -- By the round bound `round_bound_nat`, no block `i < k` can still be active!
    have hall_inactive : ∀ i < k, st.active i = false := by
      intro i hi
      by_contra hact
      have hactt : st.active i = true := Bool.eq_true_of_not_eq_false hact
      have hnr : st.numRounds i = 49 * cfg.L + 1 := hfinal.active_numRounds i hi hactt
      have hBcard : (blockSet vs b i).card = b := card_blockSet hnd hi
      have hBne : (blockSet vs b i).Nonempty := Finset.card_pos.mp (by rw [hBcard]; exact hb_pos)
      have hBL : (blockSet vs b i).card < 2 ^ cfg.L := by
        have hsub : blockSet vs b i ⊆ X := hvs ▸ blockSet_subset_toFinset vs b i
        exact lt_of_le_of_lt (Finset.card_le_card hsub) hXL
      have hpm : ∀ j < 49 * cfg.L + 1, IsPerfectMatchingOn (blockSet vs b i) (st.rounds i j) :=
        fun j hj => hfinal.rounds_pm i hi j (hnr.symm ▸ hj)
      have hcut : ∀ j < 49 * cfg.L + 1, ∃ C ⊆ blockSet vs b i,
          (blockSet vs b i).card ≤ 4 * C.card ∧
          (∀ e ∈ st.rounds i j, ¬ (e.1 ∈ C ∧ e.2 ∈ C)) ∧
          100 * (Graph.mk G.n (witnessEdges (st.rounds i) j)).cutIn (blockSet vs b i) C ≤
            (blockSet vs b i).card :=
        fun j hj => hfinal.rounds_cut i hi j (hnr.symm ▸ hj)
      have hlt := round_bound_nat hBne hBL hpm hcut
      omega
    -- Build the complement-to-expander injection pairs.
    set injPairs := (List.range k).map fun i => (blockSet vs b i \ st.savedS i, st.savedS i)
    have hinj_valid : ValidTerminalPairs X injPairs := by
      rw [← hvs]
      let rpairs := (List.range k).map fun i => (i, (blockSet vs b i \ st.savedS i, st.savedS i))
      have hmap : injPairs = rpairs.map Prod.snd := by
        simp [injPairs, rpairs]
      rw [hmap]
      refine validTerminalPairs_of_distinct_blocks hnd hb_pos ?_ ?_
      · have hfst : rpairs.map Prod.fst = List.range k := by simp [rpairs, Function.comp_def]
        rw [hfst]; exact List.nodup_range
      · intro ip hip
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hip
        have hik : i < k := List.mem_range.mp hi
        obtain ⟨hSsub, hS2, _⟩ := hfinal.inactive_exp i hik (hall_inactive i hik)
        have hsd : (blockSet vs b i \ st.savedS i).card + (st.savedS i).card =
            (blockSet vs b i).card := Finset.card_sdiff_add_card_eq_card hSsub
        exact ⟨hik, Finset.sdiff_subset, hSsub, disjoint_sdiff_self_left, by dsimp only; omega⟩
    have hrspec := hroute.spec G X injPairs cfg.Δ cfg.L 100 z hX hGloop hcfg.hΔ_pos hdegG hcfg.hL
      hXL (by decide) hinj_valid
    dsimp only [injPairs] at hrspec ⊢
    cases hres : route G X ((List.range k).map fun i =>
        (blockSet vs b i \ st.savedS i, st.savedS i)) cfg.Δ cfg.L 100 z with
    | cut U =>
      rw [hres] at hrspec
      exact hrspec
    | matched matchings emb =>
      rw [hres] at hrspec
      dsimp only
      set rc : RoutedCall := ⟨matchings.flatten, emb, completeBatchFake injPairs matchings⟩
      have hrc_valid : rc.Valid G X (routeCong cfg.Δ 100 cfg.L) z :=
        routedCall_valid_of_matched hinj_valid hrspec
      refine ⟨?_, ?_, ?_⟩
      · rw [List.length_append, List.length_singleton]
        have := hfinal.calls_len
        omega
      · intro c hc
        rcases List.mem_append.mp hc with h1 | h2
        · exact hfinal.calls_valid c h1
        · rw [List.mem_singleton.mp h2]; exact hrc_valid
      · intro i hi
        obtain ⟨hSsub, hS2, hSexp⟩ := hfinal.inactive_exp i hi (hall_inactive i hi)
        -- Transfer expansion of `savedS i` to `callsWitnessEdges st.calls`.
        have hSexp_st : (Graph.mk G.n (callsWitnessEdges st.calls)).IsExpansionExpanderOn
            (st.savedS i) (1 / (cfg.P (q - 1) : ℝ)) := by
          intro T hTS hne hneS
          have h1 := hSexp T hTS hne hneS
          have hcut1 : (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))).cutIn
              (st.savedS i) T ≤
              (Graph.mk G.n (callsWitnessEdges st.calls)).cutIn (st.savedS i) T :=
            hfinal.sub_cut i hi (st.savedS i) T
          have hcut1r : ((Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))).cutIn
              (st.savedS i) T : ℝ) ≤
              ((Graph.mk G.n (callsWitnessEdges st.calls)).cutIn (st.savedS i) T : ℝ) := by
            exact_mod_cast hcut1
          linarith
        -- Apply the injection lemma `isExpansionExpanderOn_of_injection` with `M_i`.
        have hi_inj : i < ((List.range k).map fun i =>
            (blockSet vs b i \ st.savedS i, st.savedS i)).length := by simp [hi]
        have hmspec := hrspec.2.1 i hi_inj
        dsimp only at hmspec
        have hp_eq : ((List.range k).map fun i =>
            (blockSet vs b i \ st.savedS i, st.savedS i))[i]'hi_inj =
            (blockSet vs b i \ st.savedS i, st.savedS i) := by simp
        rw [hp_eq] at hmspec
        dsimp only at hmspec
        set m := matchings.getD i []
        set f := completeMatchingFake (blockSet vs b i \ st.savedS i) (st.savedS i) m
        have hsd : (blockSet vs b i \ st.savedS i).card + (st.savedS i).card =
            (blockSet vs b i).card := Finset.card_sdiff_add_card_eq_card hSsub
        have hcf := completeMatchingFake_spec (by omega) hmspec.1 hmspec.2.1 hmspec.2.2
        have hPpos : (0 : ℝ) < cfg.P (q - 1) := Nat.cast_pos.mpr (hcfg.hP_pos (by omega))
        have hβ0 : 0 ≤ 1 / (cfg.P (q - 1) : ℝ) := by positivity
        have hβ1 : 1 / (cfg.P (q - 1) : ℝ) ≤ 1 := by
          rw [div_le_one hPpos]
          exact_mod_cast hcfg.hP_pos (by omega)
        have hinj_exp := isExpansionExpanderOn_of_injection (E := callsWitnessEdges st.calls)
          (M := m ++ f) hβ0 hβ1 hSsub hSexp_st
          (fun e he => by
            have h12 : e.1 ∈ blockSet vs b i \ st.savedS i ∧ e.2 ∈ st.savedS i := by
              rcases List.mem_append.mp he with h | h
              · exact hmspec.1 e h
              · exact hcf.2.1 e h
            exact ⟨(Finset.mem_sdiff.mp h12.1).1, (Finset.mem_sdiff.mp h12.1).2, h12.2⟩)
          hcf.2.2.2.2.2.1
          (fun v hvB hvS => hcf.2.2.2.2.2.2.2 v (Finset.mem_sdiff.mpr ⟨hvB, hvS⟩))
        -- Transfer from `callsWitnessEdges st.calls ++ (m ++ f)` to `callsWitnessEdges (st.calls ++ [rc])`.
        have hdiv : 1 / (cfg.P (q - 1) : ℝ) / 2 = 1 / (2 * (cfg.P (q - 1) : ℝ)) := by ring
        rw [hdiv] at hinj_exp
        intro T hTB hne hneB
        have h1 := hinj_exp T hTB hne hneB
        have hcw : callsWitnessEdges (st.calls ++ [rc]) =
            callsWitnessEdges st.calls ++ (rc.routed ++ rc.fake) := by
          simp [callsWitnessEdges]
        have hcut_le : (Graph.mk G.n (callsWitnessEdges st.calls ++ (m ++ f))).cutIn
            (blockSet vs b i) T ≤
            (Graph.mk G.n (callsWitnessEdges (st.calls ++ [rc]))).cutIn (blockSet vs b i) T := by
          rw [hcw, cutIn_append, cutIn_append, cutIn_append, cutIn_append]
          have hi_m : i < matchings.length := hrspec.1.symm ▸ hi_inj
          have hm_mem : m ∈ matchings := by
            dsimp only [m]; rw [List.getD_eq_getElem _ _ hi_m]; exact List.getElem_mem hi_m
          have h1' := cutIn_le_flatten G.n hm_mem (blockSet vs b i) T
          have hf_mem : f ∈ List.zipWith (fun p M => completeMatchingFake p.1 p.2 M)
              injPairs matchings := by
            have hzw_len : (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M)
                injPairs matchings).length = injPairs.length := by
              rw [List.length_zipWith, hrspec.1, min_self]
            have hi_zw : i < (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M)
                injPairs matchings).length := hzw_len.symm ▸ hi_inj
            have hget_zw : (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M)
                injPairs matchings)[i]'hi_zw = f := by
              rw [List.getElem_zipWith, hp_eq]
              dsimp only [f, m]
              rw [List.getD_eq_getElem _ _ hi_m]
            rw [← hget_zw]
            exact List.getElem_mem hi_zw
          have h2' := cutIn_le_flatten G.n hf_mem (blockSet vs b i) T
          change (Graph.mk G.n (callsWitnessEdges st.calls)).cutIn (blockSet vs b i) T +
              ((Graph.mk G.n m).cutIn (blockSet vs b i) T +
                (Graph.mk G.n f).cutIn (blockSet vs b i) T) ≤
            (Graph.mk G.n (callsWitnessEdges st.calls)).cutIn (blockSet vs b i) T +
              ((Graph.mk G.n matchings.flatten).cutIn (blockSet vs b i) T +
                (Graph.mk G.n (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M)
                  injPairs matchings).flatten).cutIn (blockSet vs b i) T)
          omega
        have hcut_ler : ((Graph.mk G.n (callsWitnessEdges st.calls ++ (m ++ f))).cutIn
            (blockSet vs b i) T : ℝ) ≤
            ((Graph.mk G.n (callsWitnessEdges (st.calls ++ [rc]))).cutIn
              (blockSet vs b i) T : ℝ) := by
          exact_mod_cast hcut_le
        linarith

/-- Valid-state summary for `stepBRunRounds` at every step `t ≤ 49 * cfg.L + 1`: every block's
current witness graph satisfies the preconditions of `Core(q - 1)`, the active cut pairs are valid
with length `≤ k`, and at `t = 49 * cfg.L + 1` the complement-injection pairs are valid. -/
theorem stepBRunRounds_state_valid {cfg : CoreParams} {r q : ℕ} (hcfg : CoreParamsValid cfg r)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    {G : Graph} {X : Finset ℕ} {vs : List ℕ} {b z : ℕ}
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ cfg.Δ) (hXL : X.card < 2 ^ cfg.L)
    (hnd : vs.Nodup) (hvs : vs.toFinset = X)
    (hb_pos : 0 < b) (hb_even : Even b) (hb_le : b ≤ cfg.N ^ (q - 1))
    {subCore : Graph → Finset ℕ → CoreResult}
    (hsubCore : ∀ W Y, Y ⊆ Finset.range W.n → W.IsValid → (∀ e ∈ W.inside Y, e.1 ≠ e.2) →
      Y.card ≤ cfg.N ^ (q - 1) → (∀ v ∈ Y, W.degIn Y v ≤ cfg.Δ) →
      CoreSpec cfg (q - 1) W Y (subCore W Y))
    {t : ℕ} (ht : t ≤ 49 * cfg.L + 1) {st : BlockGameState}
    (hst : stepBRunRounds cfg route G X vs b (numFullBlocks vs b) z subCore t = Sum.inr st) :
    (∀ i < numFullBlocks vs b,
      let W := Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))
      let B := blockSet vs b i
      B ⊆ Finset.range W.n ∧ W.IsValid ∧ (∀ e ∈ W.inside B, e.1 ≠ e.2) ∧
        B.card ≤ cfg.N ^ (q - 1) ∧ (∀ v ∈ B, W.degIn B v ≤ cfg.Δ)) ∧
    (t ≤ 49 * cfg.L →
      ValidTerminalPairs X ((activeCutPairs G vs b (numFullBlocks vs b) subCore st).map Prod.snd) ∧
      ((activeCutPairs G vs b (numFullBlocks vs b) subCore st).map Prod.snd).length ≤
        numFullBlocks vs b) ∧
    (t = 49 * cfg.L + 1 →
      ValidTerminalPairs X ((List.range (numFullBlocks vs b)).map fun i =>
        (blockSet vs b i \ st.savedS i, st.savedS i))) := by
  set k := numFullBlocks vs b
  have hrun : ∀ t' ≤ 49 * cfg.L + 1,
      match stepBRunRounds cfg route G X vs b k z subCore t' with
      | Sum.inl U => RouteCutSpec G X 100 z U
      | Sum.inr st' => StepBInv cfg q G X vs b k z t' st' := by
    intro t' ht'
    induction t' with
    | zero => exact stepBInv_init cfg q G X vs b k z
    | succ t' ih =>
      have hprev := ih (Nat.le_of_succ_le ht')
      unfold stepBRunRounds
      cases hstep : stepBRunRounds cfg route G X vs b k z subCore t' with
      | inl U => rw [hstep] at hprev; exact hprev
      | inr st' =>
        rw [hstep] at hprev
        exact stepBRound_spec hcfg hroute hX hGloop hdegG hXL hnd hvs
          hb_pos hb_even hb_le (by omega) hsubCore hprev
  have hinv := hrun t ht
  rw [hst] at hinv
  dsimp only at hinv
  have hblocks : ∀ i < k,
      let W := Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))
      let B := blockSet vs b i
      B ⊆ Finset.range W.n ∧ W.IsValid ∧ (∀ e ∈ W.inside B, e.1 ≠ e.2) ∧
        B.card ≤ cfg.N ^ (q - 1) ∧ (∀ v ∈ B, W.degIn B v ≤ cfg.Δ) := by
    intro i hi
    dsimp only
    have hBsub : blockSet vs b i ⊆ Finset.range G.n :=
      (blockSet_subset_toFinset vs b i).trans (hvs.symm ▸ hX)
    have hBcard : (blockSet vs b i).card = b := card_blockSet hnd hi
    have hwd := witnessEdges_loopless_deg_le (n := G.n) (hinv.rounds_pm i hi)
    have hWvalid : (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))).IsValid := by
      have hgen : ∀ m, (∀ j < m, IsPerfectMatchingOn (blockSet vs b i) (st.rounds i j)) →
          ∀ e ∈ witnessEdges (st.rounds i) m, e.1 < G.n ∧ e.2 < G.n := by
        intro m hm e he
        induction m with
        | zero => simp [witnessEdges] at he
        | succ m ihm =>
          rw [witnessEdges] at he
          rcases List.mem_append.mp he with h1 | h2
          · exact ihm (fun j hj => hm j (Nat.lt_succ_of_lt hj)) h1
          · have hmem := (hm m (Nat.lt_succ_self m)).1 e h2
            exact ⟨Finset.mem_range.mp (hBsub hmem.1), Finset.mem_range.mp (hBsub hmem.2)⟩
      exact hgen (st.numRounds i) (hinv.rounds_pm i hi)
    have hnr := hinv.numRounds_le i hi
    have hΔ := hcfg.hΔ
    exact ⟨hBsub, hWvalid, hwd.1, by rw [hBcard]; exact hb_le,
      fun v hv => le_trans (hwd.2 v hv) (by omega)⟩
  refine ⟨hblocks, ?_, ?_⟩
  · intro _
    set rpairs := activeCutPairs G vs b k subCore st
    have hids_nd : (rpairs.map Prod.fst).Nodup := by
      refine filterMap_range_fst_nodup k _ fun i p hp => ?_
      by_cases hact : st.active i = true
      · simp only [hact, ↓reduceIte] at hp
        cases hsc : subCore (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
            (blockSet vs b i) with
        | expander _ => simp [hsc] at hp
        | cut U => simp only [hsc, Option.some.injEq] at hp; rw [← hp]
      · simp [hact] at hp
    have hvp : ValidTerminalPairs X (rpairs.map Prod.snd) := by
      rw [← hvs]
      refine validTerminalPairs_of_distinct_blocks hnd hb_pos hids_nd ?_
      intro ⟨i, p⟩ hip
      obtain ⟨hik, _, U, hsc, rfl⟩ := mem_activeCutPairs_iff.mp hip
      obtain ⟨h1, h2, h3, h4, h5⟩ := hblocks i hik
      have hcs := hsubCore _ _ h1 h2 h3 h4 h5
      rw [hsc] at hcs
      have hsm := smallerSide_spec hcs.1 hcs.2.1 hcs.2.2.1 hcs.2.2.2
      have hBcard : (blockSet vs b i).card = b := card_blockSet hnd hik
      have hpad := padToHalf_spec hsm.1 hsm.2.1 (by rw [hBcard]; exact hb_even)
      exact ⟨hik, hpad.2.1, Finset.sdiff_subset, disjoint_sdiff_self_right,
        le_of_eq hpad.2.2.2.symm⟩
    have hlen : (rpairs.map Prod.snd).length ≤ k := by
      rw [List.length_map]
      unfold rpairs activeCutPairs
      exact le_trans (List.length_filterMap_le _ _) (by simp)
    exact ⟨hvp, hlen⟩
  · intro ht_eq
    subst ht_eq
    have hall_inactive : ∀ i < k, st.active i = false := by
      intro i hi
      by_contra hact
      have hactt : st.active i = true := Bool.eq_true_of_not_eq_false hact
      have hnr : st.numRounds i = 49 * cfg.L + 1 := hinv.active_numRounds i hi hactt
      have hBcard : (blockSet vs b i).card = b := card_blockSet hnd hi
      have hBne : (blockSet vs b i).Nonempty := Finset.card_pos.mp (by rw [hBcard]; exact hb_pos)
      have hBL : (blockSet vs b i).card < 2 ^ cfg.L := by
        have hsub : blockSet vs b i ⊆ X := hvs ▸ blockSet_subset_toFinset vs b i
        exact lt_of_le_of_lt (Finset.card_le_card hsub) hXL
      have hpm : ∀ j < 49 * cfg.L + 1, IsPerfectMatchingOn (blockSet vs b i) (st.rounds i j) :=
        fun j hj => hinv.rounds_pm i hi j (hnr.symm ▸ hj)
      have hcut : ∀ j < 49 * cfg.L + 1, ∃ C ⊆ blockSet vs b i,
          (blockSet vs b i).card ≤ 4 * C.card ∧
          (∀ e ∈ st.rounds i j, ¬ (e.1 ∈ C ∧ e.2 ∈ C)) ∧
          100 * (Graph.mk G.n (witnessEdges (st.rounds i) j)).cutIn (blockSet vs b i) C ≤
            (blockSet vs b i).card :=
        fun j hj => hinv.rounds_cut i hi j (hnr.symm ▸ hj)
      have hlt := round_bound_nat hBne hBL hpm hcut
      omega
    rw [← hvs]
    let rpairs := (List.range k).map fun i => (i, (blockSet vs b i \ st.savedS i, st.savedS i))
    have hmap : ((List.range k).map fun i => (blockSet vs b i \ st.savedS i, st.savedS i)) =
        rpairs.map Prod.snd := by simp [rpairs]
    rw [hmap]
    refine validTerminalPairs_of_distinct_blocks hnd hb_pos ?_ ?_
    · have hfst : rpairs.map Prod.fst = List.range k := by simp [rpairs, Function.comp_def]
      rw [hfst]; exact List.nodup_range
    · intro ip hip
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hip
      have hik : i < k := List.mem_range.mp hi
      obtain ⟨hSsub, hS2, _⟩ := hinv.inactive_exp i hik (hall_inactive i hik)
      have hsd : (blockSet vs b i \ st.savedS i).card + (st.savedS i).card =
          (blockSet vs b i).card := Finset.card_sdiff_add_card_eq_card hSsub
      exact ⟨hik, Finset.sdiff_subset, hSsub, disjoint_sdiff_self_left, by dsimp only; omega⟩

end MinCostFlow.ExpanderDecomp
