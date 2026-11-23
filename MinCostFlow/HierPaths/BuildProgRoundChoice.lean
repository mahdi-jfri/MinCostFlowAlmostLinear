module

public import MinCostFlow.HierPaths.BuildProgChoiceReplies
public import MinCostFlow.HierPaths.BuildProgOneRoundSpec

/-!
# A common game round follows the actual certified choices

The scan returns an answer for each active index. The router and application
parts use those answers without any assumption that equal graphs receive
equal replies.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Fix the replies, core bump gaps, and router bump gap of the current round. -/
def BuildRoundData.withReplies (B : BuildRoundData) (answer : ℕ → CoreResult)
    (bump : ℕ → ℕ := fun _ => 0) (rBump : ℕ := 0) : BuildRoundData :=
  { B with jobs := { B.jobs with choice := some answer, bump := some bump }, routeBump := rBump }

/-- Bound on per-child prepared width + bump gap left by the core scan. -/
def BuildRoundData.ValidBump (B : BuildRoundData) (answer : ℕ → CoreResult) (bump : ℕ → ℕ) : Prop :=
  ∀ i < B.jobs.count,
    preparedChildEnd 0 (B.jobs.graph i).n (answer i) + bump i ≤
      B.coreSpace (B.jobs.graph i).encode.length + 3 * (B.jobs.graph i).n

/-- The output of a complete round records its actual certified replies, bump sizes,
and the verified matching application. -/
def buildRoundChoiceContract (w tailBudget : ℕ) (B : BuildRoundData) (A : BuildRoundAddrs) : Contract where
  pre args mem :=
    args = B.args A ∧
    (buildScanChoiceContract w B.K B.M B.r B.q B.childSize B.coreCost B.coreSpace B.jobs).pre
      (B.scanArgs A) mem ∧
    ∀ (answer : ℕ → CoreResult) (bump : ℕ → ℕ),
      (∀ i < B.jobs.count, CoreOutcomeSpec ParamConfig.default B.M B.q (B.jobs.graph i) (answer i)) →
      B.ValidBump answer bump →
      (∀ rBump, (B.withReplies answer bump).ValidRouteBump rBump →
        BuildRoundFit w (B.withReplies answer bump rBump) A mem) ∧
      buildOneRoundTailCost w (B.withReplies answer bump) ≤ tailBudget
  post _ mem v mem' := ∃ (answer : ℕ → CoreResult) (bump : ℕ → ℕ) (rBump : ℕ),
    (∀ i < B.jobs.count, CoreOutcomeSpec ParamConfig.default B.M B.q (B.jobs.graph i) (answer i)) ∧
    B.ValidBump answer bump ∧
    (B.withReplies answer bump).ValidRouteBump rBump ∧
    (buildOneRoundContract w (B.withReplies answer bump rBump)).post (B.args A) mem v mem'
  cost _ _ := rangeCost (prepGameStepCost B.jobs B.K B.q B.coreCost) 0 B.jobs.count +
    9*B.jobs.count+38+tailBudget

/-- The program of the common round works with the independent certified core
scan and the bump router. -/
theorem buildRoundChoiceProc_meetsContract {w tailBudget f scan route finish : ℕ} {p : Program}
    {B : BuildRoundData} {A : BuildRoundAddrs}
    (hf : p.procs[f]? = some (buildOneRoundProc scan route finish))
    (hScan : MeetsContract w p scan
      (buildScanChoiceContract w B.K B.M B.r B.q B.childSize B.coreCost B.coreSpace B.jobs))
    (hRoute : ∀ ans bump, MeetsContract w p route ((B.withReplies ans bump).routeContract w))
    (hFinish : ∀ ans bump Ms emb, MeetsContract w p finish
      (buildFinishBatchContract w ((B.withReplies ans bump).applyData Ms emb)))
    (hPlayer : IsMatchingPlayer B.route B.routeCost)
    {β : ℝ} (hβ : 0 < β) (hExp : B.host.IsExpansionExpanderOn B.verts β) :
    MeetsContract w p f (buildRoundChoiceContract w tailBudget B A) := by
  refine meetsContract_of_runs hf fun args mem pos ω hArgs hPre => ?_
  obtain ⟨rfl,hScanPre,hUniform⟩ := hPre
  have hSW : ∀ a ∈ B.scanArgs A, a < 2^w := fun a ha => hArgs a (List.mem_append_left _ ha)
  refine runs_start_le ?_
  unfold buildOneRoundProc
  refine runs_seq_call_le hScan (vs := B.scanArgs A) (by rfl) hSW hScanPre ?_
  intro v after pos' hSP
  obtain ⟨_,_,_,_,he,_,_,hZ,hFrame,hGap,hRepEnd,ans,bump,addr,hChoices⟩ := hSP
  simp only [BuildRoundData.scanArgs,List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  let R := B.withReplies ans bump
  have hCert : ∀ i < B.jobs.count, CoreOutcomeSpec ParamConfig.default B.M B.q (B.jobs.graph i) (ans i) :=
    fun i hi => (hChoices.rows i hi).2.1
  have hBump : B.ValidBump ans bump := fun i hi => (hChoices.rows i hi).2.2.2.2
  obtain ⟨hFitAll,hCost⟩ := hUniform ans bump hCert hBump
  have hv : v = R.prepared A := hChoices.last.symm.trans
    (hChoices.chosenPrefixes B.core B.jobs.count le_rfl)
  rw [hv] at hZ hRepEnd hChoices
  have hReplies : GameRepliesAt R.jobs R.core R.q A.heap A.replies after :=
    hChoices.gameRepliesAt hRepEnd B.core
  have hScanDone : (R.scanContract w).post (R.scanArgs A) mem (R.prepared A) after :=
    ⟨A.graphs,A.offsets,A.heap,A.replies,rfl,rfl,hZ,⟨hFrame,hGap⟩,hReplies.1,hReplies.2⟩
  have hWords : ∀ a ∈ R.args A, a < 2^w := hArgs
  obtain ⟨o,st,c,rBump,hRun,hRBump,hPost,hBound⟩ := buildOneRoundTail_runs
    (pos := pos) (pos₁ := pos') (ω := ω)
    (prefixCost := rangeCost (prepGameStepCost B.jobs B.K B.q B.coreCost) 0 B.jobs.count +
      9*B.jobs.count+38) (total := (buildRoundChoiceContract w tailBudget B A).cost (B.args A) mem)
    hWords hFitAll hScanDone (hRoute ans bump) (fun ms em _ => hFinish ans bump ms em)
    hPlayer hβ hExp (by simp [buildRoundChoiceContract]; omega)
  rw [← hv] at hRun
  refine ⟨o,st,c,hRun,⟨ans,bump,rBump,hCert,hBump,hRBump,hPost⟩,?_⟩
  simp [buildScanChoiceContract,argsSize,Expr.size]
  omega

end MinCostFlow.HierPaths
