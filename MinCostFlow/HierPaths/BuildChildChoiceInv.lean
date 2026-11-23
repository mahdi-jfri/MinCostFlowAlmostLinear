module

public import MinCostFlow.HierPaths.BuildChildChoice

/-!
# The invariant and stopping bound for the certified game

Any valid core answer yields the same matching and sparse-cut conditions
used in the round bound. The common routed batch contributes its
occurrence load only once, across all children.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Pass the certified requests through the common router, with one complete
matching and its paths for each requesting child. -/
theorem choiceRound_call {route : RouterFn} {routeCost : RouterCostFn}
    (hRouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hHost : HostPre G X Δ L) {β : ℝ} (hβ : 0 < β) (hExp : G.IsExpansionExpanderOn X β)
    {bh : ℕ} (hb : max 2 (2/β) ≤ (bh:ℝ)) {s k M r : ℕ} {off : ℕ → ℕ}
    (hChildren : IsChildren X (fun c => shiftSet (off c) (Finset.range s)) k s)
    (hEven : s%2=0) {sts : ℕ → ChildState} {answer : ℕ → CoreResult}
    (hCert : ∀ c < k, (sts c).saved = none →
      CoreOutcomeSpec ParamConfig.default M (coreLevel M r s) (gameGraph s (sts c)) (answer c))
    (hne : choiceRequesting s k off sts answer ≠ []) :
    let cs := choiceRequesting s k off sts answer
    let req := fun c => (choiceRequest s (off c) (sts c) (answer c)).getD (∅,∅)
    ∃ Ms emb, (lemma1Route route G X (choiceRoundPairs s k off sts answer) Δ L).1 = .matched Ms emb ∧
      Ms.length = cs.length ∧
      (∀ i (hi : i < cs.length), (∀ e ∈ Ms.getD i [], e.1 ∈ (req cs[i]).1 ∧ e.2 ∈ (req cs[i]).2) ∧
        ((Ms.getD i []).map Prod.fst).Nodup ∧ ((Ms.getD i []).map Prod.snd).Nodup ∧
        (Ms.getD i []).length = (req cs[i]).1.card) ∧
      IsEmbeddingOn (Graph.mk G.n Ms.flatten) G X emb ∧
      (∀ j < Ms.flatten.length, (emb j).length ≤ routePathLen Δ bh L) ∧
      (∀ i < G.m, congestion (Graph.mk G.n Ms.flatten) emb i ≤ routeCong Δ bh L) ∧
      (∀ j < Ms.flatten.length, IsEdgeWalk G.edges (edgeAt Ms.flatten j).1 (edgeAt Ms.flatten j).2 (emb j)) := by
  refine group_call hRouter hHost hβ hExp hb hChildren (List.nodup_range.filter _)
    (fun c hc => (mem_choiceRequesting.mp hc).1) hne ?_
  intro c hc
  obtain ⟨hc,ha,U,hU⟩ := mem_choiceRequesting.mp hc
  have hReq : choiceRequest s (off c) (sts c) (answer c) = some
      (shiftSet (off c) (bisectOf s U),shiftSet (off c) (Finset.range s \ bisectOf s U)) :=
    by simp [choiceRequest,ha,hU]
  have hh := choiceRequest_props hEven (hCert c hc ha) hReq
  change ((choiceRequest s (off c) (sts c) (answer c)).getD (∅,∅)).1 ⊆
    shiftSet (off c) (Finset.range s) ∧ _
  rw [hReq]
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.le⟩

/-- The actual answer batch preserves the child invariant and contributes
at most one router call's load. -/
theorem choiceRound_inv {route : RouterFn} {routeCost : RouterCostFn}
    (hRouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hHost : HostPre G X Δ L) {β : ℝ} (hβ : 0 < β) (hExp : G.IsExpansionExpanderOn X β)
    {bh : ℕ} (hb : max 2 (2/β) ≤ (bh:ℝ)) {s k M r t : ℕ} {off : ℕ → ℕ}
    (hChildren : IsChildren X (fun c => shiftSet (off c) (Finset.range s)) k s)
    (hEven : s%2=0) (hq : coreLevel M r s ≤ r)
    {sts : ℕ → ChildState} {answer : ℕ → CoreResult}
    (hCert : ∀ c < k, (sts c).saved = none →
      CoreOutcomeSpec ParamConfig.default M (coreLevel M r s) (gameGraph s (sts c)) (answer c))
    (hInv : ∀ c < k, ChildInv G X s (off c) (routePathLen Δ bh L)
      (PParam ParamConfig.default M r) t (sts c)) :
    let next := choiceGameRound route G X Δ L s k off sts answer
    (∀ c < k, ChildInv G X s (off c) (routePathLen Δ bh L)
      (PParam ParamConfig.default M r) (t+1) (next c)) ∧
    ∀ i < G.m, ∑ c ∈ Finset.range k, occLoad (walkFamily (next c).rounds.flatten) i ≤
      (∑ c ∈ Finset.range k, occLoad (walkFamily (sts c).rounds.flatten) i) + routeCong Δ bh L := by
  let cs := choiceRequesting s k off sts answer
  let es := if cs.isEmpty then [] else
    callEntries G.edges (lemma1Route route G X (choiceRoundPairs s k off sts answer) Δ L).1
  let next := choiceGameRound route G X Δ L s k off sts answer
  have hc (c : ℕ) (h : c ∈ cs) : c < k := (mem_choiceRequesting.mp h).1
  have hP (c : ℕ) (h : c ∈ cs) :
      let p := (choiceRequest s (off c) (sts c) (answer c)).getD (∅,∅)
      p.1 ⊆ shiftSet (off c) (Finset.range s) ∧ p.2 ⊆ shiftSet (off c) (Finset.range s) := by
    obtain ⟨hck,hAct,U,hU⟩ := mem_choiceRequesting.mp h
    have hSub : U ⊆ Finset.range s := by
      have hh := hCert c hck hAct
      rw [hU] at hh
      exact hh.1
    simp [choiceRequest,hAct,hU,shiftSet_subset (bisectOf_spec hSub).1,
      shiftSet_subset Finset.sdiff_subset]
  change (∀ c < k, ChildInv G X s (off c) (routePathLen Δ bh L)
      (PParam ParamConfig.default M r) (t+1) (next c)) ∧ _
  refine ⟨?_,?_⟩
  · intro c hck
    change ChildInv G X s (off c) (routePathLen Δ bh L) (PParam ParamConfig.default M r)
      (t+1) (if c < k then childStepAnswer (sts c) (answer c) (takeEntries s (off c) es) else sts c)
    rw [ite_eq_left hck]
    refine childInv_step_of_answer hEven (hInv c hck)
      (fun ha => coreOutcome_weaken hq (hCert c hck ha)) ?_
    intro U hAct hU
    have hmem : c ∈ cs := mem_choiceRequesting.mpr ⟨hck,hAct,U,hU⟩
    have hNon := List.ne_nil_of_mem hmem
    have hNe : cs.isEmpty = false := Bool.eq_false_iff.mpr (fun he => hNon (List.isEmpty_iff.mp he))
    obtain ⟨Ms,emb,hRes,hM,hBlock,hEmb,hLen,_,_⟩ :=
      choiceRound_call hRouter hHost hβ hExp hb hChildren hEven hCert hNon
    let i := cs.idxOf c
    have hi : i < cs.length := List.idxOf_lt_length_of_mem hmem
    have hIdx : cs[i] = c := List.getElem_idxOf hi
    have hY (c : ℕ) (hm : c ∈ cs) := (hChildren.2.1 c (hc c hm)).1
    have hDis (a : ℕ) (ha : a ∈ cs) (b : ℕ) (hb : b ∈ cs) (hne : a ≠ b) :=
      hChildren.2.2 a (hc a ha) b (hc b hb) hne
    have hE : es = callEntries G.edges (.matched Ms emb) := by
      have hh : (lemma1Route route G X (choiceRoundPairs s k off sts answer) Δ L).1 = .matched Ms emb := hRes
      simp [es,hNe,hh]
    rw [hE]
    have hN : cs.Nodup := List.nodup_range.filter _
    obtain ⟨hMap,hOK⟩ := take_call hN hY hDis hP hM
      (fun j hj => (hBlock j hj).1) hEmb hLen hi (show shiftSet (off cs[i]) _ = _ by rw [hIdx])
    have hB := hBlock i hi
    let req := fun c => (choiceRequest s (off c) (sts c) (answer c)).getD (∅,∅)
    change (∀ e ∈ Ms.getD i [], e.1 ∈ (req cs[i]).1 ∧ e.2 ∈ (req cs[i]).2) ∧
        ((Ms.getD i []).map Prod.fst).Nodup ∧ ((Ms.getD i []).map Prod.snd).Nodup ∧
        (Ms.getD i []).length = (req cs[i]).1.card at hB
    rw [hIdx] at hB
    simp only [req,choiceRequest,hAct,hU,Option.getD_some] at hB
    exact ⟨⟨Ms.getD i [],hMap,hB.1,hB.2.1,hB.2.2.1,
      hB.2.2.2.trans (card_shiftSet _ _)⟩,hOK⟩
  · intro i hi
    have hAdd : ∀ c < k, occLoad (walkFamily (next c).rounds.flatten) i ≤
        occLoad (walkFamily (sts c).rounds.flatten) i +
          occLoad (walkFamily (takeEntries s (off c) es)) i := by
      intro c hck
      change occLoad (walkFamily (if c < k then childStepAnswer (sts c) (answer c)
        (takeEntries s (off c) es) else sts c).rounds.flatten) i ≤ _
      rw [ite_eq_left hck]
      cases hS : (sts c).saved <;> cases hA : answer c <;>
        simp [childStepAnswer,hS,walkFamily,occLoad_append]
    have hLoad : occLoad (walkFamily es) i ≤ routeCong Δ bh L := by
      by_cases hEmpty : cs = []
      · have hh : cs.isEmpty = true := List.isEmpty_iff.mpr hEmpty
        simp [es,hh,walkFamily,occLoad]
      · obtain ⟨Ms,emb,hRes,_,_,_,_,hCong,hWalk⟩ :=
          choiceRound_call hRouter hHost hβ hExp hb hChildren hEven hCert hEmpty
        have hNe : cs.isEmpty = false := Bool.eq_false_iff.mpr
          (fun he => hEmpty (List.isEmpty_iff.mp he))
        have hE : es = callEntries G.edges (.matched Ms emb) := by
          have hh : (lemma1Route route G X (choiceRoundPairs s k off sts answer) Δ L).1 = .matched Ms emb := hRes
          simp [es,hNe,hh]
        rw [hE]
        exact occLoad_callEntries_le hWalk (hCong i hi)
    calc
      _ ≤ ∑ c ∈ Finset.range k, (occLoad (walkFamily (sts c).rounds.flatten) i +
          occLoad (walkFamily (takeEntries s (off c) es)) i) :=
        Finset.sum_le_sum fun c hc => hAdd c (Finset.mem_range.mp hc)
      _ ≤ _ := by
        rw [Finset.sum_add_distrib]
        exact Nat.add_le_add_left ((sum_occLoad_take_le hChildren.2.2 es i).trans hLoad) _

/-- Each certified game prefix satisfies the round invariant and total load bound. -/
theorem CertifiedGame.invariant {route : RouterFn} {routeCost : RouterCostFn}
    (hRouter : IsMatchingPlayer route routeCost) {G : Graph} {X : Finset ℕ} {Δ L : ℕ}
    (hHost : HostPre G X Δ L) {β : ℝ} (hβ : 0 < β) (hExp : G.IsExpansionExpanderOn X β)
    {bh : ℕ} (hb : max 2 (2/β) ≤ (bh:ℝ)) {s k M r : ℕ} {off : ℕ → ℕ}
    (hChildren : IsChildren X (fun c => shiftSet (off c) (Finset.range s)) k s)
    (hEven : s%2=0) (hq : coreLevel M r s ≤ r)
    {t : ℕ} {sts : ℕ → ChildState} (hRun : CertifiedGame route G X M r Δ L s k off t sts) :
    (∀ c < k, ChildInv G X s (off c) (routePathLen Δ bh L)
      (PParam ParamConfig.default M r) t (sts c)) ∧
    ∀ i < G.m, ∑ c ∈ Finset.range k, occLoad (walkFamily (sts c).rounds.flatten) i ≤
      t * routeCong Δ bh L := by
  induction hRun with
  | start =>
    refine ⟨fun c _ => childInv_init G X s (off c) _ _,fun i _ => ?_⟩
    simp [ChildState.init,walkFamily,occLoad]
  | step hRun answer cert ih =>
    obtain ⟨hInv,hLoad⟩ := ih
    obtain ⟨hStep,hStepLoad⟩ := choiceRound_inv hRouter hHost hβ hExp hb hChildren hEven hq cert hInv
    refine ⟨hStep, fun i hi => ?_⟩
    rw [Nat.succ_mul]
    exact (hStepLoad i hi).trans (Nat.add_le_add_right (hLoad i hi) _)

/-- After the round bound every child has saved an expander certificate,
regardless of which certified replies were returned. -/
theorem CertifiedGame.all_saved {G : Graph} {X : Finset ℕ}
    {M r Δ L L' s k bh : ℕ} {off : ℕ → ℕ} {sts : ℕ → ChildState}
    (hs : 1 ≤ s) (hLog : s < 2^L')
    (hInv : ∀ c < k, ChildInv G X s (off c) (routePathLen Δ bh L)
      (PParam ParamConfig.default M r) (49*L'+1) (sts c)) :
    ∀ c < k, ∃ S, (sts c).saved = some S := by
  intro c hc
  obtain ⟨_,hAct,hRound,_,_⟩ := hInv c hc
  cases he : (sts c).saved with
  | some S => exact ⟨S,rfl⟩
  | none =>
    have hLen := hAct he
    rw [hLen] at hRound
    have hh := game_rounds_lt (t := 49*L'+1) hs hLog
      (fun j hj => (hRound j hj).1) (fun j hj => (hRound j hj).2)
    omega

end MinCostFlow.HierPaths
