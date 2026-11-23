module

public import MinCostFlow.HierPaths.BuildProgGameRows

/-!
# Repeating the child-game step

A round directory stores the records of the rounds that run. Each iteration
uses the current count and arena cursor. Once the active count is zero,
later iterations leave memory unchanged.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- Run one step when there are active children and advance the arena cursor. -/
def buildGameLoopStep (step : ℕ) : Stmt :=
  .cond (.reg 3)
    (.seq (.call 20 step
      [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,
        .reg 11,.reg 12,.reg 13,.reg 14,.reg 15,.reg 16])
    (.seq (.store (.bin .add (.reg 17) (.reg 19)) (.reg 20))
    (.seq (.assign 21 (.load (.reg 20)))
    (.seq (.assign 6 (.bin .add (.bin .add (.reg 20) (.const 2)) (.reg 3)))
      (.assign 3 (.load (.reg 21)))))))
    .nop

/-- The first seventeen words are those of a game step. The last two are the
round directory and the round limit. Return the first free address. -/
def buildGameLoopProc (step : ℕ) : Stmt :=
  .seq (forRange 19 (.const 0) (.reg 18) (buildGameLoopStep step)) (.ret (.reg 6))

theorem buildGameLoopProc_noRand (step : ℕ) : (buildGameLoopProc step).NoRand := by
  simp [buildGameLoopProc,buildGameLoopStep,forRange,forUp,Stmt.NoRand]

/-- The model rounds and addresses for the fixed parent group. -/
structure BuildGameLoopData where
  round : ℕ → BuildRoundData
  addrs : ℕ → BuildRoundAddrs
  child : ℕ → ℕ → ℕ
  start : ℕ
  saved : ℕ
  directory : ℕ
  limit : ℕ

/-- The current register packet consists of the game step's arguments and the
two fixed directory parameters. -/
def BuildGameLoopData.args (D : BuildGameLoopData) (t : ℕ) : List ℕ :=
  (D.round t).stepArgs (D.addrs t) D.start D.saved ++ [D.directory,D.limit]

/-- Successive memory states with every game step and directory write recorded.
An iteration after all children are saved skips the calls. -/
inductive GameLoopTrace (w : ℕ) (D : BuildGameLoopData) (mem : ℕ → ℕ) :
    ℕ → (ℕ → ℕ) → Prop where
  | init : GameLoopTrace w D mem 0 mem
  | skip {t mem'} : GameLoopTrace w D mem t mem' → (D.round t).jobs.count = 0 →
      GameLoopTrace w D mem (t+1) mem'
  | run {t before after v} : GameLoopTrace w D mem t before →
      (D.round t).jobs.count ≠ 0 →
      (buildGameStepContract w (D.round t) (D.addrs t) D.start D.saved (D.child t)).post
        ((D.round t).stepArgs (D.addrs t) D.start D.saved) before v after →
      GameLoopTrace w D mem (t+1) (Function.update after (D.directory+t) v)

/-- Only memory geometry and the progress of the model are needed to schedule
the checked step. The fixed packet fields keep their values between rounds. -/
structure GameLoopFit (w : ℕ) (D : BuildGameLoopData) (mem : ℕ → ℕ) : Prop where
  word : 3 < 2^w
  limitWord : D.limit < 2^w
  directoryWord : D.directory + D.limit < 2^w
  fixed : ∀ t < D.limit, ∀ j < 19, j ≠ 3 → j ≠ 6 →
    (D.args (t+1)).getD j 0 = (D.args t).getD j 0
  done : (D.round D.limit).jobs.count = 0
  skip : ∀ t < D.limit, (D.round t).jobs.count = 0 →
    (D.round (t+1)).jobs.count = 0 ∧ (D.addrs (t+1)).heap = (D.addrs t).heap
  advance : ∀ t < D.limit, (D.round t).jobs.count ≠ 0 →
    (D.round (t+1)).jobs.count = (D.round t).indices.length ∧
    (D.addrs (t+1)).heap = (D.round t).record (D.addrs t) + 2 + (D.round t).jobs.count
  directoryBelow : ∀ t < D.limit, D.directory + t < (D.addrs t).replies
  stepPre : ∀ t < D.limit, ∀ before, GameLoopTrace w D mem t before →
    (D.round t).jobs.count ≠ 0 →
    (buildGameStepContract w (D.round t) (D.addrs t) D.start D.saved (D.child t)).pre
      ((D.round t).stepArgs (D.addrs t) D.start D.saved) before

/-- The step bound counts the game calls and the records only while there is
an active child. -/
def gameLoopStepCost (w : ℕ) (D : BuildGameLoopData) (t : ℕ) : ℕ :=
  if (D.round t).jobs.count = 0 then 3 else
    (buildGameStepContract w (D.round t) (D.addrs t) D.start D.saved (D.child t)).cost [] (fun _ => 0) + 60

/-- Run the complete bounded loop, retaining its memory trace. -/
def buildGameLoopContract (w : ℕ) (D : BuildGameLoopData) : Contract where
  pre args mem := args = D.args 0 ∧ GameLoopFit w D mem
  post _ mem v mem' := v = (D.addrs D.limit).heap ∧
    (D.round D.limit).jobs.count = 0 ∧ GameLoopTrace w D mem D.limit mem'
  cost _ _ := rangeCost (gameLoopStepCost w D) 0 D.limit + 9 * D.limit + 12

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

private def gameLoopInv (w : ℕ) (D : BuildGameLoopData) (mem : ℕ → ℕ) (t : ℕ) (st : State) : Prop :=
  (∀ j < 19, st.regs j = (D.args t).getD j 0) ∧
    st.regs 19 = t ∧ GameLoopTrace w D mem t st.mem

private theorem gameLoopStep_triple {w t step : ℕ} {D : BuildGameLoopData} {mem : ℕ → ℕ}
    {p : Program} (hFit : GameLoopFit w D mem) (ht : t < D.limit)
    (hWord : ∀ a ∈ D.args t, a < 2 ^ w)
    (hFitRows : ∀ Ms emb, (D.round t).indices.isEmpty = false → (D.round t).result.1 = .matched Ms emb →
      Ms.length = (D.round t).indices.length)
    (hStep : MeetsContract w p step
      (buildGameStepContract w (D.round t) (D.addrs t) D.start D.saved (D.child t))) :
    Triple w p (gameLoopInv w D mem t) (buildGameLoopStep step)
      (normalPost fun st => gameLoopInv w D mem (t+1)
        {st with regs := Function.update st.regs 19 (t+1)} ∧ st.regs 19 = t)
      (fun _ => gameLoopStepCost w D t) := by
  intro st ω ⟨hRegs,hCounter,hTrace⟩
  let B := D.round t
  let A := D.addrs t
  let n := B.jobs.count
  have hn : st.regs 3 = n := hRegs 3 (by decide)
  have hh : st.regs 6 = A.heap := hRegs 6 (by decide)
  have hdir : st.regs 17 = D.directory := hRegs 17 (by decide)
  have hOne : 1 < 2^w := by have := hFit.word; omega
  have hTwo : 2 < 2^w := by have := hFit.word; omega
  by_cases hZero : n = 0
  · obtain ⟨hCount,hHeap⟩ := hFit.skip t ht hZero
    refine ⟨.normal,st,3,?_,⟨⟨?_,by simp,.skip hTrace hZero⟩,hCounter⟩,?_⟩
    · unfold buildGameLoopStep
      refine runs_cond_iff.mpr ⟨0,1,Expr.eval_reg_of_eq (hn.trans hZero),?_,rfl⟩
      exact runs_nop_iff.mpr ⟨rfl,rfl,rfl⟩
    · intro j hj
      change Function.update st.regs 19 (t+1) j = _
      rw [Function.update_of_ne (by omega), hRegs j hj]
      by_cases h₃ : j = 3
      · subst j
        change n = (D.round (t+1)).jobs.count
        rw [hZero,hCount]
      by_cases h₆ : j = 6
      · subst j
        exact hHeap.symm
      exact (hFit.fixed t ht j hj h₃ h₆).symm
    · simp [gameLoopStepCost,show (D.round t).jobs.count = 0 from hZero]
  · obtain ⟨hCount,hHeap⟩ := hFit.advance t ht hZero
    let P := fun o st' => normalPost (fun st => gameLoopInv w D mem (t+1)
      {st with regs := Function.update st.regs 19 (t+1)} ∧ st.regs 19 = t) o st'
    have hpre := hFit.stepPre t ht st.mem hTrace hZero
    have hSpace := hpre.2.2.2
    have hStepWords : ∀ a ∈ B.stepArgs A D.start D.saved, a < 2 ^ w :=
      fun a ha => hWord a (List.mem_append_left _ ha)
    have hEval : evalArgs w st (List.range 17 |>.map Expr.reg) =
        some (B.stepArgs A D.start D.saved) := by
      have hR (j : ℕ) (hj : j < 17) : st.regs j = (D.args t).getD j 0 := hRegs j (by omega)
      simp [List.range_succ,evalArgs,Expr.eval,hR,BuildGameLoopData.args,BuildRoundData.stepArgs,
        BuildRoundData.args,B,A]
    have habove : D.directory + t < B.prepared A := by
      have h₀ := hFit.directoryBelow t ht
      have h₁ := hpre.2.2.1.tableBelow
      have h₂ : A.heap ≤ B.prepared A :=
        B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
      change D.directory + t < A.replies at h₀
      change A.replies + n + 1 ≤ A.heap at h₁
      omega
    unfold buildGameLoopStep
    suffices ∃ o st' c, Runs w p ω
        (.seq (.call 20 step (List.range 17 |>.map Expr.reg))
          (.seq (.store (.bin .add (.reg 17) (.reg 19)) (.reg 20))
          (.seq (.assign 21 (.load (.reg 20)))
          (.seq (.assign 6 (.bin .add (.bin .add (.reg 20) (.const 2)) (.reg 3)))
            (.assign 3 (.load (.reg 21))))))) st o st' c ∧ P o st' ∧
        2 + c ≤ gameLoopStepCost w D t by
      obtain ⟨o,st',c,hr,hp,hc⟩ := this
      exact ⟨o,st',1+c+1,runs_cond_iff.mpr
        ⟨n,c,Expr.eval_reg_of_eq hn,by simpa [hZero,List.range_succ] using hr,by simp⟩,
        hp,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc⟩
    refine runs_seq_call_le hStep (vs := B.stepArgs A D.start D.saved) hEval hStepWords hpre ?_
    intro v after pos' hPost
    have hv : v = B.record A := hPost.1
    have hvWord : v + 2 + n < 2^w := hv ▸ hSpace
    have hv2 : v + 2 < 2^w := by omega
    have hDirW : D.directory + t < 2^w := by have := hFit.directoryWord; omega
    have hRecord : after v = B.prepared A := hPost.2.1 0 (by simp)
    have hLow : B.prepared A + 1 + B.indices.length ≤ v := by
      obtain ⟨mid,_,hRound,_,_,_⟩ := hPost.2.2
      have hScan : BuildRoundFit w B A st.mem := hpre.2.1
      have hRows : ∀ Ms emb, B.indices.isEmpty = false → B.result.1 = .matched Ms emb →
          Ms.length = B.indices.length := by
        exact hFitRows
      exact (oneRoundMemory_of_post hScan hRows hRound).preparedEnd
    let out := Function.update after (D.directory + t) v
    have he : D.directory + t ≠ v := by omega
    have hpne : B.prepared A ≠ D.directory + t := by omega
    have hRead : out v = B.prepared A :=
      (Function.update_of_ne (Ne.symm he) ..).trans hRecord
    have hCountRead : out (B.prepared A) = B.indices.length := by
      rw [show out (B.prepared A) = after (B.prepared A) from Function.update_of_ne hpne ..]
      obtain ⟨mid,m,hRound,hAdv,hFrame,_⟩ := hPost.2.2
      have hScan : BuildRoundFit w B A st.mem := hpre.2.1
      have hKeep := oneRoundMemory_of_post hScan hFitRows hRound
      rw [hFrame _ (by omega) (by omega)]
      obtain ⟨_,_,_,heq,_,_,_,_,_,hAF⟩ := hAdv
      simp only [List.cons.injEq,and_true,true_and] at heq
      obtain ⟨rfl,rfl,rfl⟩ := heq
      have hL := hpre.2.2.1
      have hK : B.indices.length ≤ n := by
        simpa [n,BuildRoundData.indices,batchJobIndices,cutReplyIndices] using
          List.length_filter_le (fun i => decide (coreTag (B.jobs.answer B.core B.q i) = 0))
            (List.range n)
      have hp : A.heap ≤ B.prepared A := B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
      have h₀ := hL.graphsBelow
      have h₁ := hL.offsetsBelow
      have h₂ := hL.tableBelow
      change (D.addrs t).heap ≤ B.prepared A at hp
      change (D.round t).indices.length ≤ (D.round t).jobs.count at hK
      exact (hAF _ (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
        (fun i hi _ => Nat.ne_of_gt (by have := hL.savedBelow i hi; omega))).trans hKeep.count
    refine runs_seq_store_le (x := D.directory+t) (v := v) ?_ (by simp [Expr.eval,Function.update]) ?_
    · simp [Expr.eval,Function.update,hdir,hCounter,hDirW]
    refine runs_seq_assign_le (v := B.prepared A) ?_ ?_
    · have hr : Function.update after (D.directory + t) v v = B.prepared A := hRead
      simp [Expr.eval,Function.update,he.symm,hRecord] at hr ⊢
    refine runs_seq_assign_le (v := v + 2 + n) ?_ ?_
    · simp [Expr.eval,Function.update,hn,hTwo,hv2,hvWord]
    refine runs_assign_le (v := B.indices.length) ?_ ?_ ?_
    · change some (out (B.prepared A)) = some B.indices.length
      rw [hCountRead]
    · refine ⟨⟨?_,by simp,.run hTrace hZero hPost⟩,by simp [hCounter]⟩
      intro j hj
      by_cases h₃ : j = 3
      · subst j
        exact hCount.symm
      by_cases h₆ : j = 6
      · subst j
        exact (hHeap.trans (congrArg (fun x => x+2+n) hv.symm)).symm
      have h₁₉ : j ≠ 19 := by omega
      have h₂₀ : j ≠ 20 := by omega
      have h₂₁ : j ≠ 21 := by omega
      simpa [Function.update,h₃,h₆,h₁₉,h₂₀,h₂₁,hRegs j hj] using
        (hFit.fixed t ht j hj h₃ h₆).symm
    · simp [gameLoopStepCost,show (D.round t).jobs.count ≠ 0 from hZero,
        buildGameStepContract,buildOneRoundContract,BuildRoundData.scanContract,
        BuildRoundData.routeContract,buildGameScanContract,buildRoundRouteContract,
        buildFinishBatchContract,Expr.size,argsSize,List.range_succ,B,A,Nat.add_assoc]
      split <;> omega

/-- The loop executes each scheduled game step and returns an empty active table
with the sequence of memory transitions certified. -/
theorem buildGameLoopProc_meetsContract {w f step : ℕ} {p : Program} {D : BuildGameLoopData}
    (hf : p.procs[f]? = some (buildGameLoopProc step))
    (hWord : ∀ t < D.limit, ∀ a ∈ D.args t, a < 2 ^ w)
    (hRows : ∀ t < D.limit, ∀ Ms emb, (D.round t).indices.isEmpty = false → (D.round t).result.1 = .matched Ms emb →
      Ms.length = (D.round t).indices.length)
    (hStep : ∀ t < D.limit, MeetsContract w p step
      (buildGameStepContract w (D.round t) (D.addrs t) D.start D.saved (D.child t))) :
    MeetsContract w p f (buildGameLoopContract w D) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨rfl,hFit⟩ := hPre
  let st₀ := startState (D.args 0) mem pos
  have hw : 1 < 2 ^ w := by have := hFit.word; omega
  have hLoop := Triple.forRange_le (p := p) (r := 19) (lo := .const 0) (hi := .reg 18)
    (body := buildGameLoopStep step) (P := fun st => st = st₀)
    (Inv := gameLoopInv w D mem) (gameLoopStepCost w D) 0 D.limit (Nat.zero_le _) hw
    (fun _ => hFit.limitWord) (fun st he => by
      subst st
      refine ⟨Expr.eval_const (Nat.two_pow_pos _),?_,by simp,.init⟩
      intro j hj
      change Function.update st₀.regs 19 0 j = _
      rw [Function.update_of_ne (by omega)]
      rfl)
    (fun _ _ _ _ h => h.2.1)
    (fun i st _ _ h => Expr.eval_reg_of_eq (h.1 18 (by decide)))
    (fun t _ ht => gameLoopStep_triple hFit ht (hWord t ht) (hRows t ht) (hStep t ht))
  refine runs_start_le ?_
  unfold buildGameLoopProc
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨hRegs,_,hTrace⟩
  refine runs_ret_le (v := (D.addrs D.limit).heap) (Expr.eval_reg_of_eq (hRegs 6 (by decide)))
    ⟨rfl,hFit.done,hTrace⟩ ?_
  simp [buildGameLoopContract,Expr.size]
  omega

end MinCostFlow.HierPaths
