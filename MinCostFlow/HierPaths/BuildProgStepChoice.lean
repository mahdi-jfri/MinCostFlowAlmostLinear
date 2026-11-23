module

public import MinCostFlow.HierPaths.BuildProgRoundChoice
public import MinCostFlow.HierPaths.BuildProgGameStep

/-!
# Saving and compacting a round with certified choices

The step saves the certificates returned in this round and keeps only
its cut requests on the active tables. The same postcondition retains
the updated graphs and stored shortened walks.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- A running step has room for its round record and the active tables, for
every answer and valid bump gaps that the certified scan and bump router could produce. -/
def buildStepChoiceContract (w tailBudget : ℕ) (B : BuildRoundData) (A : BuildRoundAddrs)
    (start saved : ℕ) (child : ℕ → ℕ) : Contract where
  pre args mem := args = B.stepArgs A start saved ∧
    (buildRoundChoiceContract w tailBudget B A).pre (B.args A) mem ∧
    GameStepLayout w B A start saved child ∧
    ∀ (ans : ℕ → CoreResult) (bump : ℕ → ℕ) (rBump : ℕ),
      (∀ i < B.jobs.count, CoreOutcomeSpec ParamConfig.default B.M B.q (B.jobs.graph i) (ans i)) →
      B.ValidBump ans bump →
      (B.withReplies ans bump).ValidRouteBump rBump →
      (B.withReplies ans bump rBump).record A + 2 + B.jobs.count < 2^w
  post _ mem v mem' := ∃ (ans : ℕ → CoreResult) (bump : ℕ → ℕ) (rBump : ℕ),
    (∀ i < B.jobs.count, CoreOutcomeSpec ParamConfig.default B.M B.q (B.jobs.graph i) (ans i)) ∧
    B.ValidBump ans bump ∧
    (B.withReplies ans bump).ValidRouteBump rBump ∧
    (buildGameStepContract w (B.withReplies ans bump rBump) A start saved child).post
      (B.stepArgs A start saved) mem v mem'
  cost args mem := (buildRoundChoiceContract w tailBudget B A).cost args mem +
    128*B.jobs.count + 226

/-- The step accepts a round that uses the actual core replies, and then
advances the active state using those replies. -/
theorem buildStepChoiceProc_meetsContract {w tailBudget f round endProc advance : ℕ} {p : Program}
    {B : BuildRoundData} {A : BuildRoundAddrs} {start saved : ℕ} {child : ℕ → ℕ}
    (hf : p.procs[f]? = some (buildGameStepProc round endProc advance))
    (hRound : MeetsContract w p round (buildRoundChoiceContract w tailBudget B A))
    (hEnd : ∀ ans bump rBump,
      MeetsContract w p endProc (buildPreparedEndContract w (B.withReplies ans bump rBump) A))
    (hAdvance : ∀ ans bump rBump,
      MeetsContract w p advance (buildGameAdvanceContract w (B.withReplies ans bump rBump) A child))
    (hPlayer : IsMatchingPlayer B.route B.routeCost) {β : ℝ}
    (hβ : 0 < β) (hExp : B.host.IsExpansionExpanderOn B.verts β) :
    MeetsContract w p f (buildStepChoiceContract w tailBudget B A start saved child) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨rfl,hRoundPre,hLayout,hRoom⟩ := hPre
  have hRoundW : ∀ a ∈ B.args A, a < 2^w := fun a ha =>
    hWords a (List.mem_append_left _ ha)
  refine runs_start_le ?_
  unfold buildGameStepProc
  refine runs_seq_call_le hRound (vs := B.args A) (by rfl) hRoundW hRoundPre ?_
  intro v mid pos' hPost
  obtain ⟨ans,bump,rBump,hCert,hBump,hRBump,hRoundPost⟩ := hPost
  let R := B.withReplies ans bump rBump
  have hLayout' : GameStepLayout w R A start saved child :=
    ⟨hLayout.active,hLayout.size,hLayout.childInj,hLayout.offsets,hLayout.offsetWord,hLayout.savedBelow,
      hLayout.graphsBelow,hLayout.offsetsBelow,hLayout.tableBelow⟩
  have hFit := (hRoundPre.2.2 ans bump hCert hBump).1 rBump hRBump
  have hCount : R.indices.length ≤ R.jobs.count := by
    simpa [BuildRoundData.indices,batchJobIndices,cutReplyIndices] using
      List.length_filter_le (fun i => decide (coreTag (R.jobs.answer R.core R.q i) = 0))
        (List.range R.jobs.count)
  have hRows : ∀ Ms emb, R.indices.isEmpty = false → R.result.1 = .matched Ms emb →
      Ms.length = R.indices.length := by
    intro Ms emb hne hMatch
    have hk : 1 ≤ R.pairs.length := by
      rw [show R.pairs.length = R.indices.length from length_batchJobPairs ..]
      exact List.length_pos_iff.mpr (fun h => (Bool.eq_false_iff.mp hne) (List.isEmpty_iff.mpr h))
    obtain ⟨_,hr⟩ := exists_lemma_1 hPlayer
    obtain ⟨⟨ms,em,he,hs,_⟩,_⟩ := hr R.host R.verts R.pairs R.Δ R.L hFit.router hk β hβ hExp
    change R.result.1 = _ at he
    rw [hMatch] at he
    cases he
    exact hs.1.trans (length_batchJobPairs ..)
  have hPack : ∀ a ∈ R.stepArgs A start saved, a < 2^w := hWords
  let prefixCost := (buildRoundChoiceContract w tailBudget B A).cost (B.args A) mem + 17
  let total := (buildStepChoiceContract w tailBudget B A start saved child).cost
    (B.stepArgs A start saved) mem
  obtain ⟨o,st,c,hRun,hResult,hBudget⟩ := buildGameStepTail_runs
    (pos := pos) (pos' := pos') (ω := ω) (prefixCost := prefixCost) (total := total)
    hPack hFit hLayout' (hRoom ans bump rBump hCert hBump hRBump) hRoundPost
    (hEnd ans bump rBump) (hAdvance ans bump rBump) hRows (by
      have hEq : R.jobs.count = B.jobs.count := rfl
      change R.indices.length ≤ B.jobs.count at hCount
      simp [prefixCost,total,buildStepChoiceContract,buildRoundChoiceContract]
      omega)
  refine ⟨o,st,c,hRun,⟨ans,bump,rBump,hCert,hBump,hRBump,hResult⟩,?_⟩
  simp [prefixCost,total,Expr.size,argsSize,buildRoundChoiceContract,Nat.add_assoc] at hBudget ⊢
  omega

end MinCostFlow.HierPaths
