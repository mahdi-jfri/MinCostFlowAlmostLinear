module

public import MinCostFlow.HierPaths.BuildProgStepChoice
public import MinCostFlow.HierPaths.BuildProgChoiceJobs
public import MinCostFlow.HierPaths.BuildProgGameLoop

/-!
# The batched loop with certified answers

The loop keeps the current game state and heap cursor in its invariant.
Each active iteration extends the certified history by the actual replies
at that iteration. The directory stores where to find its round record.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- The parts of the game that remain fixed while the calls choose replies. -/
structure ChoiceLoopData where
  base : BuildRoundData
  addrs : BuildRoundAddrs
  count : ℕ
  first : ℕ
  childAddr : ℕ → ℕ
  saved : ℕ
  directory : ℕ
  L' : ℕ

namespace ChoiceLoopData

/-- Global interval start of an original child. -/
def offset (D : ChoiceLoopData) (c : ℕ) : ℕ := D.first+c*D.base.childSize

/-- Original child number of a current active index. -/
def active (D : ChoiceLoopData) (sts : ℕ → ChildState) (i : ℕ) : ℕ :=
  (activeChildren D.count sts).getD i 0

/-- The graph inputs of the next core scan. -/
def round (D : ChoiceLoopData) (sts : ℕ → ChildState) : BuildRoundData :=
  { D.base with
    jobs := modelGameJobs D.base.childSize D.count D.offset D.childAddr sts
    q := coreLevel D.base.M D.base.r D.base.childSize }

/-- The arena end changes while all the other addresses are fixed. -/
def atHeap (D : ChoiceLoopData) (heap : ℕ) : BuildRoundAddrs :=
  { D.addrs with heap := heap }

/-- The certified round limit. -/
def limit (D : ChoiceLoopData) : ℕ := 49*D.L'+1

/-- Runtime arguments at the start of a loop iteration. -/
def args (D : ChoiceLoopData) (heap : ℕ) (sts : ℕ → ChildState) : List ℕ :=
  (D.round sts).stepArgs (D.atHeap heap) D.first D.saved ++ [D.directory,D.limit]

/-- The next model state with the replies recorded by this iteration. -/
def next (D : ChoiceLoopData) (sts : ℕ → ChildState) (ans : ℕ → CoreResult) : ℕ → ChildState :=
  choiceGameRound D.base.route D.base.host D.base.verts D.base.Δ D.base.L D.base.childSize
    D.count D.offset sts (answerByChild D.count sts ans)

end ChoiceLoopData

/-- The run's completed iteration records, including the model and memory
state of each step that actually called the players. -/
inductive ChoiceLoopTrace (w : ℕ) (D : ChoiceLoopData) (initial : ℕ → ℕ) :
    ℕ → ℕ → (ℕ → ChildState) → (ℕ → ℕ) → Prop where
  | start : ChoiceLoopTrace w D initial 0 D.addrs.heap (fun _ => ChildState.init) initial
  | skip {t heap sts mem} : ChoiceLoopTrace w D initial t heap sts mem →
      (D.round sts).jobs.count = 0 →
      ChoiceLoopTrace w D initial (t+1) heap sts mem
  | run {t heap sts mem v after} : ChoiceLoopTrace w D initial t heap sts mem →
      (D.round sts).jobs.count ≠ 0 →
      ∀ (ans : ℕ → CoreResult) (bump : ℕ → ℕ) (rBump : ℕ),
      (∀ i < (D.round sts).jobs.count, CoreOutcomeSpec ParamConfig.default D.base.M
        (D.round sts).q ((D.round sts).jobs.graph i) (ans i)) →
      (D.round sts).ValidBump ans bump →
      ((D.round sts).withReplies ans bump).ValidRouteBump rBump →
      (buildGameStepContract w ((D.round sts).withReplies ans bump rBump) (D.atHeap heap)
        D.first D.saved (D.active sts)).post
        ((D.round sts).stepArgs (D.atHeap heap) D.first D.saved) mem v after →
      ChoiceLoopTrace w D initial (t+1) (v+2+(D.round sts).jobs.count) (D.next sts ans)
        (Function.update after (D.directory+t) v)

/-- The step's uniform arena and time bounds. The bounds are needed only when
the current table has an active child. -/
structure ChoiceLoopFit (w tailBudget stepBudget : ℕ) (D : ChoiceLoopData)
    (initial : ℕ → ℕ) : Prop where
  bits : 3 < 2^w
  directoryWord : D.directory + D.limit < 2^w
  directoryBelow : D.directory + D.limit ≤ D.addrs.replies
  words : ∀ t heap sts mem, t < D.limit → ChoiceLoopTrace w D initial t heap sts mem →
    ∀ a ∈ D.args heap sts, a < 2^w
  stepPre : ∀ t heap sts mem, t < D.limit → ChoiceLoopTrace w D initial t heap sts mem →
    (D.round sts).jobs.count ≠ 0 →
    let B := D.round sts
    let A := D.atHeap heap
    (buildStepChoiceContract w tailBudget B A D.first D.saved (D.active sts)).pre
      (B.stepArgs A D.first D.saved) mem
  stepCost : ∀ t heap sts mem, t < D.limit → ChoiceLoopTrace w D initial t heap sts mem →
    (D.round sts).jobs.count ≠ 0 →
    let B := D.round sts
    let A := D.atHeap heap
    (buildStepChoiceContract w tailBudget B A D.first D.saved (D.active sts)).cost
      (B.stepArgs A D.first D.saved) mem + 60 ≤ stepBudget
  budget : 3 ≤ stepBudget
  done : ∀ heap sts mem, ChoiceLoopTrace w D initial D.limit heap sts mem → (D.round sts).jobs.count = 0

/-- The game loop with the same runtime code as the fixed-answer specialization.
Its output carries the chosen certified history. -/
def buildChoiceLoopContract (w tailBudget stepBudget : ℕ) (D : ChoiceLoopData) : Contract where
  pre args mem := args = D.args D.addrs.heap (fun _ => ChildState.init) ∧
    ChoiceLoopFit w tailBudget stepBudget D mem
  post _ mem v mem' := ∃ sts, ChoiceLoopTrace w D mem D.limit v sts mem' ∧
    (D.round sts).jobs.count = 0
  cost _ _ := D.limit * (stepBudget+9)+12

/-- The loop's next active count is the recorded number of requests. -/
theorem ChoiceLoopData.next_count (D : ChoiceLoopData) (sts : ℕ → ChildState)
    (ans : ℕ → CoreResult) (bump : ℕ → ℕ := fun _ => 0) (rBump : ℕ := 0) :
    (D.round (D.next sts ans)).jobs.count = ((D.round sts).withReplies ans bump rBump).indices.length := by
  change (activeChildren D.count (D.next sts ans)).length = _
  unfold ChoiceLoopData.next
  rw [activeChildren_choiceRound]
  have hh := choiceGameJobs_indices D.base.childSize D.count D.offset D.childAddr sts ans
    D.base.core (coreLevel D.base.M D.base.r D.base.childSize)
  have he := congrArg List.length hh
  rw [List.length_map] at he
  exact he.symm

private theorem readGameStepRecord {w : ℕ} {B : BuildRoundData} {A : BuildRoundAddrs}
    {start saved v : ℕ} {child : ℕ → ℕ} {mem after : ℕ → ℕ}
    (hFit : BuildRoundFit w B A mem) (hLay : GameStepLayout w B A start saved child)
    (hRows : ∀ Ms emb, B.indices.isEmpty = false → B.result.1 = .matched Ms emb →
      Ms.length = B.indices.length)
    (hPost : (buildGameStepContract w B A start saved child).post
      (B.stepArgs A start saved) mem v after) :
    after v = B.prepared A ∧ after (B.prepared A) = B.indices.length ∧
    B.prepared A + 1 + B.indices.length ≤ v := by
  obtain ⟨_,hRecord,mid,m,hRound,hAdv,hFrame,_⟩ := hPost
  have hKeep := oneRoundMemory_of_post hFit hRows hRound
  have hLow := hKeep.preparedEnd
  refine ⟨hRecord 0 (by simp),?_,hLow⟩
  rw [hFrame _ (by omega) (by omega)]
  obtain ⟨_,_,_,heq,_,_,_,_,_,hAF⟩ := hAdv
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  have hK : B.indices.length ≤ B.jobs.count := by
    simpa [BuildRoundData.indices,batchJobIndices,cutReplyIndices] using
      List.length_filter_le (fun i => decide (coreTag (B.jobs.answer B.core B.q i) = 0))
        (List.range B.jobs.count)
  have hp : A.heap ≤ B.prepared A :=
    B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
  have h₀ := hLay.graphsBelow
  have h₁ := hLay.offsetsBelow
  have h₂ := hLay.tableBelow
  exact (hAF _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
    (fun i hi _ => Nat.ne_of_gt (by have := hLay.savedBelow i hi; omega))).trans hKeep.count

private def choiceLoopInv (w : ℕ) (D : ChoiceLoopData) (initial : ℕ → ℕ) (t : ℕ) (st : State) : Prop :=
  ∃ heap sts, (∀ j < 19, st.regs j = (D.args heap sts).getD j 0) ∧
    st.regs 19 = t ∧ ChoiceLoopTrace w D initial t heap sts st.mem

private theorem choiceLoop_step {w tailBudget stepBudget t f : ℕ} {D : ChoiceLoopData}
    {initial : ℕ → ℕ} {p : Program} (hFit : ChoiceLoopFit w tailBudget stepBudget D initial)
    (ht : t < D.limit)
    (hStep : ∀ heap sts, MeetsContract w p f
      (buildStepChoiceContract w tailBudget (D.round sts) (D.atHeap heap) D.first D.saved (D.active sts)))
    (hPlayer : IsMatchingPlayer D.base.route D.base.routeCost) {β : ℝ} (hβ : 0 < β)
    (hExp : D.base.host.IsExpansionExpanderOn D.base.verts β) :
    Triple w p (choiceLoopInv w D initial t) (buildGameLoopStep f)
      (normalPost fun st => choiceLoopInv w D initial (t+1)
        {st with regs := Function.update st.regs 19 (t+1)} ∧ st.regs 19 = t) (fun _ => stepBudget) := by
  intro st ω ⟨heap,sts,hRegs,hCounter,hTrace⟩
  let B := D.round sts
  let A := D.atHeap heap
  let n := B.jobs.count
  have hn : st.regs 3 = n := hRegs 3 (by decide)
  have hdir : st.regs 17 = D.directory := hRegs 17 (by decide)
  have hOne : 1 < 2^w := by have := hFit.bits; omega
  have hTwo : 2 < 2^w := by have := hFit.bits; omega
  by_cases hZero : n = 0
  · refine ⟨.normal,st,3,?_,⟨⟨heap,sts,?_,by simp,.skip hTrace hZero⟩,hCounter⟩,hFit.budget⟩
    · unfold buildGameLoopStep
      exact runs_cond_iff.mpr ⟨0,1,Expr.eval_reg_of_eq (hn.trans hZero),
        runs_nop_iff.mpr ⟨rfl,rfl,rfl⟩,rfl⟩
    · intro j hj
      change Function.update st.regs 19 (t+1) j = _
      rw [Function.update_of_ne (by omega), hRegs j hj]
  · let P := fun o st' => normalPost (fun st => choiceLoopInv w D initial (t+1)
      {st with regs := Function.update st.regs 19 (t+1)} ∧ st.regs 19 = t) o st'
    have hpre := hFit.stepPre t heap sts st.mem ht hTrace hZero
    have hCost := hFit.stepCost t heap sts st.mem ht hTrace hZero
    have hWord := hFit.words t heap sts st.mem ht hTrace
    have hStepWords : ∀ a ∈ B.stepArgs A D.first D.saved, a < 2^w :=
      fun a ha => hWord a (List.mem_append_left _ ha)
    have hEval : evalArgs w st (List.range 17 |>.map Expr.reg) =
        some (B.stepArgs A D.first D.saved) := by
      have hR (j : ℕ) (hj : j < 17) : st.regs j = (D.args heap sts).getD j 0 := hRegs j (by omega)
      simp [List.range_succ,evalArgs,Expr.eval,hR,ChoiceLoopData.args,BuildRoundData.stepArgs,
        BuildRoundData.args,B,A]
    unfold buildGameLoopStep
    suffices ∃ o st' c, Runs w p ω
        (.seq (.call 20 f (List.range 17 |>.map Expr.reg))
          (.seq (.store (.bin .add (.reg 17) (.reg 19)) (.reg 20))
          (.seq (.assign 21 (.load (.reg 20)))
          (.seq (.assign 6 (.bin .add (.bin .add (.reg 20) (.const 2)) (.reg 3)))
            (.assign 3 (.load (.reg 21))))))) st o st' c ∧ P o st' ∧ 2+c ≤ stepBudget by
      obtain ⟨o,st',c,hr,hp,hc⟩ := this
      exact ⟨o,st',1+c+1,runs_cond_iff.mpr
        ⟨n,c,Expr.eval_reg_of_eq hn,by simpa [hZero,List.range_succ] using hr,by simp⟩,
        hp,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc⟩
    refine runs_seq_call_le (hStep heap sts) (vs := B.stepArgs A D.first D.saved) hEval hStepWords hpre ?_
    intro v after pos' hPost
    obtain ⟨ans,bump,rBump,hCert,hBump,hRBump,hPost⟩ := hPost
    let R := B.withReplies ans bump rBump
    have hBuild : BuildRoundFit w R A st.mem := (hpre.2.1.2.2 ans bump hCert hBump).1 rBump hRBump
    have hLayout := hpre.2.2.1
    have hLay : GameStepLayout w R A D.first D.saved (D.active sts) :=
      ⟨hLayout.active,hLayout.size,hLayout.childInj,hLayout.offsets,hLayout.offsetWord,
        hLayout.savedBelow,hLayout.graphsBelow,hLayout.offsetsBelow,hLayout.tableBelow⟩
    have hRows : ∀ Ms emb, R.indices.isEmpty = false → R.result.1 = .matched Ms emb →
        Ms.length = R.indices.length := by
      intro Ms emb hne hMatch
      have hp : 1 ≤ R.pairs.length := by
        rw [show R.pairs.length = R.indices.length from length_batchJobPairs ..]
        exact List.length_pos_iff.mpr (fun h => (Bool.eq_false_iff.mp hne) (List.isEmpty_iff.mpr h))
      obtain ⟨_,hr⟩ := exists_lemma_1 hPlayer
      obtain ⟨⟨ms,em,he,hs,_⟩,_⟩ := hr R.host R.verts R.pairs R.Δ R.L hBuild.router hp β hβ hExp
      change R.result.1 = _ at he
      rw [hMatch] at he
      cases he
      exact hs.1.trans (length_batchJobPairs ..)
    have hv : v = R.record A := hPost.1
    have hvWord : v+2+n < 2^w := hv ▸ hpre.2.2.2 ans bump rBump hCert hBump hRBump
    have hv2 : v+2 < 2^w := by omega
    have hDirW : D.directory+t < 2^w := by have := hFit.directoryWord; omega
    obtain ⟨hRecord,hCount,hLow⟩ := readGameStepRecord hBuild hLay hRows hPost
    have hBefore : D.directory+t < R.prepared A := by
      have hd := hFit.directoryBelow
      have hh := hLay.tableBelow
      have hHeap : A.heap ≤ R.prepared A :=
        R.jobs.prepPrefix_mono R.core R.q A.heap (Nat.zero_le _)
      change D.addrs.replies + R.jobs.count + 1 ≤ A.heap at hh
      omega
    let out := Function.update after (D.directory+t) v
    have he : v ≠ D.directory+t := by omega
    have hpne : R.prepared A ≠ D.directory+t := by omega
    have hRead : out v = R.prepared A := (Function.update_of_ne he ..).trans hRecord
    have hCountRead : out (R.prepared A) = R.indices.length :=
      (Function.update_of_ne hpne ..).trans hCount
    refine runs_seq_store_le (x := D.directory+t) (v := v) ?_ (by simp [Expr.eval,Function.update]) ?_
    · simp [Expr.eval,Function.update,hdir,hCounter,hDirW]
    refine runs_seq_assign_le (v := R.prepared A) ?_ ?_
    · change some (out v) = some (R.prepared A)
      rw [hRead]
    refine runs_seq_assign_le (v := v+2+n) ?_ ?_
    · simp [Expr.eval,Function.update,hn,hTwo,hv2,hvWord]
    refine runs_assign_le (v := R.indices.length) ?_ ?_ ?_
    · change some (out (R.prepared A)) = some R.indices.length
      rw [hCountRead]
    · refine ⟨⟨v+2+n,D.next sts ans,?_,by simp,.run hTrace hZero ans bump rBump hCert hBump hRBump hPost⟩,by simp [hCounter]⟩
      intro j hj
      by_cases h₃ : j = 3
      · subst j
        exact (D.next_count sts ans bump rBump).symm
      by_cases h₆ : j = 6
      · subst j
        rfl
      have h₁₉ : j ≠ 19 := by omega
      have h₂₀ : j ≠ 20 := by omega
      have h₂₁ : j ≠ 21 := by omega
      have hSame : (D.args (v+2+n) (D.next sts ans)).getD j 0 = (D.args heap sts).getD j 0 := by
        have hh : ∀ a ∈ List.range 19, a ≠ 3 → a ≠ 6 →
            (D.args (v+2+n) (D.next sts ans)).getD a 0 = (D.args heap sts).getD a 0 := by
          simp [List.range_succ,ChoiceLoopData.args,ChoiceLoopData.round,ChoiceLoopData.atHeap,
            BuildRoundData.stepArgs,BuildRoundData.args]
        exact hh j (List.mem_range.mpr hj) h₃ h₆
      simpa [Function.update,h₃,h₆,h₁₉,h₂₀,h₂₁,hRegs j hj] using hSame.symm
    · change (buildStepChoiceContract w tailBudget B A D.first D.saved (D.active sts)).cost
        (B.stepArgs A D.first D.saved) st.mem + 60 ≤ stepBudget at hCost
      simp [buildStepChoiceContract,buildRoundChoiceContract,Expr.size,argsSize,List.range_succ] at hCost ⊢
      dsimp only [B] at hCost ⊢
      omega

/-- Execute the bounded loop with its actual core replies, recording the
resulting certified history and returning the final arena end. -/
theorem buildChoiceLoopProc_meetsContract {w tailBudget stepBudget f step : ℕ}
    {p : Program} {D : ChoiceLoopData}
    (hf : p.procs[f]? = some (buildGameLoopProc step))
    (hStep : ∀ heap sts, MeetsContract w p step
      (buildStepChoiceContract w tailBudget (D.round sts) (D.atHeap heap) D.first D.saved (D.active sts)))
    (hPlayer : IsMatchingPlayer D.base.route D.base.routeCost) {β : ℝ} (hβ : 0 < β)
    (hExp : D.base.host.IsExpansionExpanderOn D.base.verts β) :
    MeetsContract w p f (buildChoiceLoopContract w tailBudget stepBudget D) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨rfl,hFit⟩ := hPre
  let sts₀ : ℕ → ChildState := fun _ => ChildState.init
  let st₀ := startState (D.args D.addrs.heap sts₀) mem pos
  have hw : 1 < 2^w := by have := hFit.bits; omega
  have hLim : D.limit < 2^w := by have := hFit.directoryWord; omega
  have hLoop := Triple.forRange_const (p := p) (r := 19) (lo := .const 0) (hi := .reg 18)
    (body := buildGameLoopStep step) (P := fun st => st = st₀)
    (Inv := choiceLoopInv w D mem) stepBudget 0 D.limit (Nat.zero_le _) hw (fun _ => hLim)
    (fun st he => by
      subst st
      refine ⟨Expr.eval_const (Nat.two_pow_pos _),D.addrs.heap,sts₀,?_,by simp,.start⟩
      intro j hj
      change Function.update st₀.regs 19 0 j = _
      rw [Function.update_of_ne (by omega)]
      rfl)
    (fun _ _ _ _ h => by obtain ⟨_,_,_,hc,_⟩ := h; exact hc)
    (fun _ _ _ _ h => by
      obtain ⟨_,_,hR,_,_⟩ := h
      exact Expr.eval_reg_of_eq (hR 18 (by decide)))
    (fun _ _ ht => choiceLoop_step hFit ht hStep hPlayer hβ hExp)
  refine runs_start_le ?_
  unfold buildGameLoopProc
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨heap,sts,hRegs,_,hTrace⟩
  refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (hRegs 6 (by decide)))
    ⟨sts,hTrace,hFit.done heap sts st.mem hTrace⟩ ?_
  simp [buildChoiceLoopContract,Expr.size]

end MinCostFlow.HierPaths
