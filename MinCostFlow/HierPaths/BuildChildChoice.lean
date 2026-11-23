module

public import MinCostFlow.HierPaths.BuildChildLoad

/-!
# The batched child game with arbitrary certified core answers

The cut or expander decision belongs to its call. Each batch uses the
decisions of its active children and the exact result of the common
router call. The child invariant and occurrence bounds are the same
as in the child construction (`lemma_3`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- A certified cut becomes a padded pair when its child is active. -/
def choiceRequest (s o : ℕ) (st : ChildState) (res : CoreResult) :
    Option (Finset ℕ × Finset ℕ) :=
  match st.saved, res with
  | none, .cut U => some (shiftSet o (bisectOf s U), shiftSet o (Finset.range s \ bisectOf s U))
  | _, _ => none

/-- Original child indices in the batch, in increasing order. -/
def choiceRequesting (s k : ℕ) (off : ℕ → ℕ) (sts : ℕ → ChildState)
    (answer : ℕ → CoreResult) : List ℕ :=
  (List.range k).filter fun c => (choiceRequest s (off c) (sts c) (answer c)).isSome

/-- The pairs for the common router call of one certified round. -/
def choiceRoundPairs (s k : ℕ) (off : ℕ → ℕ) (sts : ℕ → ChildState)
    (answer : ℕ → CoreResult) : List (Finset ℕ × Finset ℕ) :=
  (choiceRequesting s k off sts answer).map fun c =>
    (choiceRequest s (off c) (sts c) (answer c)).getD (∅,∅)

/-- Apply the answer and the child's row of the common routed result. -/
def choiceGameRound (route : RouterFn) (G : Graph) (X : Finset ℕ) (Δ L s k : ℕ)
    (off : ℕ → ℕ) (sts : ℕ → ChildState) (answer : ℕ → CoreResult) : ℕ → ChildState :=
  let es := if (choiceRequesting s k off sts answer).isEmpty then [] else
    callEntries G.edges (lemma1Route route G X (choiceRoundPairs s k off sts answer) Δ L).1
  fun c => if c < k then childStepAnswer (sts c) (answer c) (takeEntries s (off c) es) else sts c

/-- A prefix of the game, with a fresh certified answer for each active
child at every round. Saved children make no further calls. -/
inductive CertifiedGame (route : RouterFn) (G : Graph) (X : Finset ℕ)
    (M r Δ L s k : ℕ) (off : ℕ → ℕ) : ℕ → (ℕ → ChildState) → Prop where
  | start : CertifiedGame route G X M r Δ L s k off 0 (fun _ => ChildState.init)
  | step {t sts} (run : CertifiedGame route G X M r Δ L s k off t sts)
      (answer : ℕ → CoreResult)
      (cert : ∀ c < k, (sts c).saved = none →
        CoreOutcomeSpec ParamConfig.default M (coreLevel M r s) (gameGraph s (sts c)) (answer c)) :
      CertifiedGame route G X M r Δ L s k off (t+1)
        (choiceGameRound route G X Δ L s k off sts answer)

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The level-q certificate implies the uniform level-r certificate. -/
theorem coreOutcome_weaken {M q r : ℕ} {cfg : ParamConfig} {G : Graph} {res : CoreResult}
    (hqr : q ≤ r) (h : CoreOutcomeSpec cfg M q G res) : CoreOutcomeSpec cfg M r G res := by
  cases res with
  | cut U => exact h
  | expander S =>
    exact ⟨h.1,h.2.1,isExpansionExpanderOn_mono (inv_PParam_le_of_le cfg M hqr) h.2.2⟩

/-- A requesting child is active and gave the cut used to construct its pair. -/
theorem mem_choiceRequesting {s k c : ℕ} {off : ℕ → ℕ} {sts : ℕ → ChildState}
    {answer : ℕ → CoreResult} :
    c ∈ choiceRequesting s k off sts answer ↔
      c < k ∧ (sts c).saved = none ∧ ∃ U, answer c = .cut U := by
  simp only [choiceRequesting,List.mem_filter,List.mem_range]
  cases h : (sts c).saved <;> cases hr : answer c <;> simp [choiceRequest,h]

/-- A certified request has disjoint sides contained in its child, of equal size. -/
theorem choiceRequest_props {s o : ℕ} {st : ChildState} {res : CoreResult}
    {cfg : ParamConfig} {M q : ℕ} {p : Finset ℕ × Finset ℕ}
    (heven : s % 2 = 0) (hs : CoreOutcomeSpec cfg M q (gameGraph s st) res)
    (h : choiceRequest s o st res = some p) :
    p.1 ⊆ shiftSet o (Finset.range s) ∧ p.2 ⊆ shiftSet o (Finset.range s) ∧
      Disjoint p.1 p.2 ∧ p.1.card = p.2.card := by
  cases hSt : st.saved <;> cases res <;> simp only [choiceRequest,hSt,Option.some.injEq,
    reduceCtorEq] at h
  rename_i U
  obtain rfl := h
  have hU : U ⊆ Finset.range s := hs.1
  obtain ⟨hC,hCard⟩ := bisectOf_spec hU
  refine ⟨shiftSet_subset hC,shiftSet_subset Finset.sdiff_subset,?_,?_⟩
  · rw [shiftSet_sdiff]
    exact Finset.disjoint_sdiff
  · rw [card_shiftSet,card_shiftSet,Finset.card_sdiff_of_subset hC,Finset.card_range,hCard]
    omega

end MinCostFlow.HierPaths
