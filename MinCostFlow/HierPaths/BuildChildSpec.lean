module

public import MinCostFlow.HierPaths.BuildChildAux

/-!
# The batched game of `lemma_3`: one child's step

The invariant `ChildInv` of one child after `t` rounds of the game (`BuildChild.lean`):
- it has played at most `t` rounds, and exactly `t` while it is active;
- every round is a perfect matching of `range s` that crosses a balanced sparse cut of the game
  graph before it (`RoundCut`, the condition of the round bound);
- a saved set `S` has at least half of the child and expansion at least `1/P` in the game graph;
- every entry has a host walk of at most `d` edges between the shifted ends of its edge, inside
  `X` (`EntryOK`).

`childInv_step` proves that one round keeps it, given what the router call gives this child
(`TakeOK`). The core player's preconditions hold because the game graph is made of perfect
matchings (`witness_valid`, `witness_loopless`, `witness_deg_le`) and has at most `t ≤ 49 L`
rounds.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- An entry is good: its walk is an edge walk of `G` between the ends of its edge shifted by `o`,
inside `X`, with at most `d` edges. -/
@[expose] def EntryOK (G : Graph) (X : Finset ℕ) (o d : ℕ) (en : (ℕ × ℕ) × List ℕ) : Prop :=
  IsEdgeWalk G.edges (o + en.1.1) (o + en.1.2) en.2 ∧
    (∀ i ∈ en.2, insideB X (edgeAt G.edges i) = true) ∧ en.2.length ≤ d

/-- The invariant of one child after `t` rounds. -/
@[expose] def ChildInv (G : Graph) (X : Finset ℕ) (s o d P t : ℕ) (st : ChildState) : Prop :=
  st.rounds.length ≤ t ∧ (st.saved = none → st.rounds.length = t) ∧
    (∀ j < st.rounds.length, IsPerfectMatchingOn (Finset.range s) (st.M j) ∧ RoundCut s st.M j) ∧
    (∀ S, st.saved = some S → S ⊆ Finset.range s ∧ s ≤ 2 * S.card ∧
      (gameGraph s st).IsExpansionExpanderOn S (1 / (P : ℝ))) ∧
    ∀ en ∈ st.rounds.flatten, EntryOK G X o d en

/-- What a router call must give a requesting child whose core cut is `U`: its entries are a full
matching from the shifted bisection `C' = bisectOf s U` to the rest, shifted back, and every
entry is good. -/
@[expose] def TakeOK (G : Graph) (X : Finset ℕ) (s o d : ℕ) (U : Finset ℕ)
    (take : List ((ℕ × ℕ) × List ℕ)) : Prop :=
  (∃ Mh : List (ℕ × ℕ), take.map Prod.fst = unshiftEdges o Mh ∧
    (∀ e ∈ Mh, e.1 ∈ shiftSet o (bisectOf s U) ∧
      e.2 ∈ shiftSet o (Finset.range s \ bisectOf s U)) ∧
    (Mh.map Prod.fst).Nodup ∧ (Mh.map Prod.snd).Nodup ∧ Mh.length = (bisectOf s U).card) ∧
  ∀ en ∈ take, EntryOK G X o d en

/-- The start satisfies the invariant. -/
theorem childInv_init (G : Graph) (X : Finset ℕ) (s o d P : ℕ) :
    ChildInv G X s o d P 0 ChildState.init := by
  refine ⟨by simp [ChildState.init], fun _ => by simp [ChildState.init], ?_, ?_, ?_⟩
  · intro j hj; simp [ChildState.init] at hj
  · intro S hS; simp [ChildState.init] at hS
  · intro en hen; simp [ChildState.init] at hen

/-- The bisection of a core cut has `s / 2` vertices inside `range s`. -/
theorem bisectOf_spec {s : ℕ} {U : Finset ℕ} (hU : U ⊆ Finset.range s) :
    bisectOf s U ⊆ Finset.range s ∧ (bisectOf s U).card = s / 2 := by
  have hC := smallerSide_subset hU
  have hc := (card_smallerSide hU).1
  rw [Finset.card_range] at hc
  exact ⟨padHalf_subset hC, card_padHalf hC (by omega)⟩

/-- The matchings of a state with one more round agree with the old ones before it. -/
theorem M_append (st : ChildState) (x : List ((ℕ × ℕ) × List ℕ)) {j : ℕ}
    (hj : j < st.rounds.length) : (ChildState.M ⟨st.rounds ++ [x], none⟩) j = st.M j := by
  unfold ChildState.M
  simp only
  rw [List.getD_append _ _ _ _ hj]

/-- The new matching of a state with one more round. -/
theorem M_append_last (st : ChildState) (x : List ((ℕ × ℕ) × List ℕ)) :
    (ChildState.M ⟨st.rounds ++ [x], none⟩) st.rounds.length = x.map Prod.fst := by
  unfold ChildState.M
  simp only
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

/-- Update one child from its saved status, the actual core answer and the
stored matching entries. -/
@[expose] def childStepAnswer (st : ChildState) (answer : CoreResult)
    (take : List ((ℕ × ℕ) × List ℕ)) : ChildState :=
  match st.saved with
  | some _ => st
  | none => match answer with
    | .expander S => ⟨st.rounds, some S⟩
    | .cut _ => ⟨st.rounds ++ [take], none⟩

/-- A child may use any core answer certified for its current graph.
The router supplies the entries when that answer is a cut. -/
theorem childInv_step_of_answer {cfg : ParamConfig} {M r : ℕ} {answer : CoreResult}
    {G : Graph} {X : Finset ℕ} {s o d t : ℕ} (heven : s % 2 = 0)
    {st : ChildState} (hinv : ChildInv G X s o d (PParam cfg M r) t st)
    (hSpec : st.saved = none → CoreOutcomeSpec cfg M r (gameGraph s st) answer)
    {take : List ((ℕ × ℕ) × List ℕ)}
    (htake : ∀ U, st.saved = none → answer = .cut U → TakeOK G X s o d U take) :
    ChildInv G X s o d (PParam cfg M r) (t + 1) (childStepAnswer st answer take) := by
  unfold childStepAnswer
  obtain ⟨hlen, hact, hrounds, hsaved, hent⟩ := hinv
  cases hsv : st.saved with
  | some S₀ =>
    simp only
    exact ⟨by omega, fun h => (by rw [hsv] at h; cases h), hrounds, hsaved, hent⟩
  | none =>
    simp only
    have hlt : st.rounds.length = t := hact hsv
    have hspec := hSpec hsv
    cases hca : answer with
    | expander S =>
      rw [hca] at hspec
      obtain ⟨hS1, hS2, hS3⟩ := hspec
      simp only
      refine ⟨(by show st.rounds.length ≤ t + 1; omega), fun h => (by cases h), hrounds, ?_, hent⟩
      intro S' hS'
      simp only [Option.some.injEq] at hS'
      subst hS'
      refine ⟨hS1, ?_, hS3⟩
      have : (gameGraph s st).n = s := rfl
      omega
    | cut U =>
      rw [hca] at hspec
      obtain ⟨hU1, hU2, hU3, hU4⟩ := hspec
      have hUs : U ⊆ Finset.range s := hU1
      obtain ⟨⟨Mh, hmap, hends, hnd1, hnd2, hMlen⟩, hok⟩ := htake U hsv hca
      obtain ⟨hC's, hC'card⟩ := bisectOf_spec hUs
      obtain ⟨hperf, hcross, _⟩ :=
        perfect_of_route hC's (by omega) hends hnd1 hnd2 hMlen
      simp only
      set st' : ChildState := ⟨st.rounds ++ [take], none⟩
      have hlen' : st'.rounds.length = st.rounds.length + 1 := by simp [st']
      have hMold : ∀ j < st.rounds.length, st'.M j = st.M j := fun j hj => M_append st take hj
      have hMnew : st'.M st.rounds.length = unshiftEdges o Mh := by
        rw [M_append_last, hmap]
      have hwit : ∀ j ≤ st.rounds.length, witnessEdges st'.M j = witnessEdges st.M j :=
        fun j hj => witnessEdges_congr fun j' hj' => hMold j' (by omega)
      refine ⟨by omega, fun _ => by omega, ?_, fun S hS => by simp [st'] at hS, ?_⟩
      · intro j hj
        rw [hlen'] at hj
        by_cases hjt : j < st.rounds.length
        · obtain ⟨h1, hrc⟩ := hrounds j hjt
          unfold RoundCut at hrc
          obtain ⟨C, hC, h2, h3, h4⟩ := hrc
          rw [hMold j hjt]
          refine ⟨h1, ?_⟩
          unfold RoundCut
          refine ⟨C, hC, h2, ?_, ?_⟩
          · rw [hMold j hjt]; exact h3
          · rw [hwit j hjt.le]; exact h4
        · have hjeq : j = st.rounds.length := by omega
          subst hjeq
          rw [hMnew]
          refine ⟨hperf, roundCut_of_core hUs (by exact hU2) (by exact hU3) ?_ ?_⟩
          · rw [hwit _ le_rfl]
            exact hU4
          · intro e he
            rw [hMnew] at he
            exact hcross e he
      · intro en hen
        simp only [st', List.flatten_append, List.flatten_singleton, List.mem_append] at hen
        rcases hen with h | h
        · exact hent en h
        · exact hok en h

/-- **One child's step.** Let the child satisfy the invariant after `t ≤ 49 L'` rounds, with
`2 ≤ s ≤ N^r`, `s` even, and `49 L' ≤ deltaParam M`. If the router call gives the child what
`TakeOK` says whenever it requests, the child satisfies the invariant after round `t + 1`. -/
theorem childInv_step {cfg : ParamConfig} {M r : ℕ} {core : ℕ → Graph → CoreResult}
    {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg M r core coreCost)
    {G : Graph} {X : Finset ℕ} {s o d t L' : ℕ} (heven : s % 2 = 0)
    (hsN : s ≤ (NOf M r) ^ r) (hΔ : 49 * L' ≤ deltaParam M) (ht : t ≤ 49 * L')
    {st : ChildState} (hinv : ChildInv G X s o d (PParam cfg M r) t st)
    {take : List ((ℕ × ℕ) × List ℕ)}
    (htake : ∀ U, st.saved = none → coreAnswer core M r s st = .cut U → TakeOK G X s o d U take) :
    ChildInv G X s o d (PParam cfg M r) (t + 1)
      (match st.saved with
        | some _ => st
        | none =>
          match coreAnswer core M r s st with
          | .expander S => ⟨st.rounds, some S⟩
          | .cut _ => ⟨st.rounds ++ [take], none⟩) := by
  apply childInv_step_of_answer heven hinv ?_ htake
  intro _
  obtain ⟨hlen, _, hrounds, _, _⟩ := hinv
  have hpm : ∀ j < st.rounds.length, IsPerfectMatchingOn (Finset.range s) (st.M j) :=
    fun j hj => (hrounds j hj).1
  have hdeg : ∀ v < (gameGraph s st).n, (gameGraph s st).deg v ≤ deltaParam M := by
    intro v _
    exact (witness_deg_le hpm v).trans (hlen.trans (ht.trans hΔ))
  exact hcore.spec_coreLevel (witness_valid hpm) (witness_loopless hpm) hsN hdeg

end MinCostFlow.HierPaths
