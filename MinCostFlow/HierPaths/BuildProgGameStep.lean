module

public import MinCostFlow.HierPaths.BuildProgGameAdvance

/-!
# A game round followed by the update of its active state

The step runs the common round, finds its cut list, and advances the active
tables. Its caller can keep the returned arena address in a round directory.
At that address the step stores the address of the cut list, the old count,
and the old offsets.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- Finish a round whose arena record address is in register 17. -/
def buildGameStepTail (preparedEnd advance : ℕ) : Stmt :=
  .seq (.call 18 preparedEnd [.reg 7,.reg 3,.reg 8])
  (.seq (.assign 19 (.bin .add (.reg 17) (.const 2)))
  (.seq (.call 20 advance
    [.reg 4,.reg 5,.reg 3,.reg 7,.reg 18,.reg 8,.reg 15,.reg 16,.reg 19])
  (.seq (.store (.reg 17) (.reg 18))
  (.seq (.store (.bin .add (.reg 17) (.const 1)) (.reg 3))
    (.ret (.reg 17))))))

/-- The ordinary round arguments followed by the first child offset and the
certificate table. The procedure returns the start of the round record. -/
def buildGameStepProc (round preparedEnd advance : ℕ) : Stmt :=
  .seq (.call 17 round
    [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,
      .reg 11,.reg 12,.reg 13,.reg 14])
    (buildGameStepTail preparedEnd advance)

theorem buildGameStepProc_noRand (round preparedEnd advance : ℕ) :
    (buildGameStepProc round preparedEnd advance).NoRand := by
  simp [buildGameStepProc,buildGameStepTail, Stmt.NoRand]

/-- Memory separations and child numbering shared across the game steps. -/
structure GameStepLayout (w : ℕ) (B : BuildRoundData) (A : BuildRoundAddrs) (start saved : ℕ)
    (child : ℕ → ℕ) : Prop where
  active : 0 < B.jobs.count
  size : 0 < B.childSize
  childInj : ∀ i < B.jobs.count, ∀ j < B.jobs.count, child i = child j → i = j
  offsets : ∀ i < B.jobs.count, B.jobs.offset i = start + child i * B.childSize
  offsetWord : ∀ i < B.jobs.count, B.jobs.offset i < 2 ^ w
  savedBelow : ∀ i < B.jobs.count, saved + child i < A.graphs
  graphsBelow : A.graphs + B.jobs.count ≤ A.offsets
  offsetsBelow : A.offsets + B.jobs.count ≤ A.replies
  tableBelow : A.replies + B.jobs.count + 1 ≤ A.heap

/-- The record starts at the exact arena end returned after the common routing
pass. It has two header words followed by the snapshot. -/
def BuildRoundData.record (B : BuildRoundData) (A : BuildRoundAddrs) : ℕ :=
  if B.indices.isEmpty then B.prepared A + 1 + B.jobs.count else
    match B.result.1 with
    | .matched Ms emb =>
      (B.applyData Ms emb).cursor (B.routedEnd A + 4 + Ms.flatten.length + B.pathBound + 1 + B.host.n)
        Ms.length
    | .cut _ => 0

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- Runtime arguments for a child-game step. -/
def BuildRoundData.stepArgs (B : BuildRoundData) (A : BuildRoundAddrs) (start saved : ℕ) :
    List ℕ := B.args A ++ [start,saved]

/-- The round followed by the directory entry and the active-table update.
The arena above the entry and snapshot is available to the next round. -/
def buildGameStepContract (w : ℕ) (B : BuildRoundData) (A : BuildRoundAddrs)
    (start saved : ℕ) (child : ℕ → ℕ) : Contract where
  pre args mem := args = B.stepArgs A start saved ∧ BuildRoundFit w B A mem ∧
    GameStepLayout w B A start saved child ∧ B.record A + 2 + B.jobs.count < 2 ^ w
  post _ mem v mem' :=
    v = B.record A ∧ ListAt mem' v [B.prepared A,B.jobs.count] ∧
    ∃ mid after,
      (buildOneRoundContract w B).post (B.args A) mem v mid ∧
      (buildGameAdvanceContract w B A child).post
        [A.graphs,A.offsets,B.jobs.count,A.replies,B.prepared A,B.childSize,start,saved,v+2]
        mid B.indices.length after ∧
      (∀ a, a ≠ v → a ≠ v+1 → mem' a = after a) ∧
      ZeroFrom mem' (v+2+B.jobs.count)
  cost _ mem := (buildOneRoundContract w B).cost (B.args A) mem +
    80 * B.jobs.count + 48 * B.indices.length + 230

private theorem record_of_round {w : ℕ} {B : BuildRoundData} {A : BuildRoundAddrs}
    {mem mem' : ℕ → ℕ} {v : ℕ}
    (hPost : (buildOneRoundContract w B).post (B.args A) mem v mem') :
    v = B.record A := by
  obtain ⟨A',m₁,m₂,mid,he,_,hR,hF⟩ := hPost
  have ha : A = A' := by
    cases A
    cases A'
    simp only [BuildRoundData.args,List.cons.injEq,and_true,true_and] at he
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := he
    rfl
  subst A'
  obtain ⟨_,_,_,_,he,hRoute,_,_,_⟩ := hR
  simp only [BuildRoundData.routeArgs,List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  have hv := hRoute.2.2
  unfold BuildRoundData.record
  by_cases hempty : B.indices.isEmpty
  · simp [roundFinishPost,hempty] at hF
    change (if B.indices.isEmpty then mid = B.prepared A + 1 + B.jobs.count else _) at hv
    simp only [hempty,ite_true] at hv ⊢
    exact hF.1.trans hv
  · obtain ⟨hmid,Ms,emb,hRes,hApply⟩ := by
      simpa [roundFinishPost,hempty] using hF
    subst mid
    obtain ⟨rep,idx,graphs,offs,ends,cap,heap,eq,hPost⟩ := hApply
    simp only [BuildRoundData.finishArgs,List.cons.injEq,and_true] at eq
    obtain ⟨rfl,rfl,rfl,rfl,rfl,_,rfl,rfl,_⟩ := eq
    obtain ⟨mt,tb,idx,graphs,offs,tmp,ends,vs,P,dir,out,he,hEnd,_,_,_,_⟩ := hPost
    simp only [finishBatchApplyArgs,List.cons.injEq,and_true,true_and] at he
    obtain ⟨rfl,rfl,_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := he
    simp only [hempty, Bool.false_eq_true, ite_false, hRes]
    exact hEnd

private theorem advanceFit_of_round {w : ℕ} {B : BuildRoundData} {A : BuildRoundAddrs}
    {mem mem' : ℕ → ℕ} {v start saved : ℕ} {child : ℕ → ℕ}
    (hFit : BuildRoundFit w B A mem) (hLayout : GameStepLayout w B A start saved child)
    (hKeep : OneRoundMemory B A mem' v)
    (hSpace : v + 2 + B.jobs.count < 2 ^ w) :
    GameAdvanceFit w B A start saved (v + 2) mem' child := by
  have hp : A.heap ≤ B.prepared A :=
    B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
  have hr : A.replies + B.jobs.count ≤ B.prepared A := by
    have := hLayout.tableBelow; omega
  have hm : B.prepared A + 1 + B.indices.length ≤ v := hKeep.preparedEnd
  have hGraphs := hLayout.graphsBelow
  have hOffsets := hLayout.offsetsBelow
  have hTable := hLayout.tableBelow
  have hAt : ListAt mem' A.offsets (tabList B.jobs.count B.jobs.offset) := hKeep.offsets
  have hReply (i : ℕ) (hi : i < B.jobs.count) : A.heap ≤ mem' (A.replies + i) ∧
      mem' (A.replies + i) + 3 < B.prepared A ∧
      mem' (mem' (A.replies + i) + 3) = coreTag (B.jobs.answer B.core B.q i) := by
    obtain ⟨hPtr,hBlock⟩ := hKeep.replies.2 i hi
    have hL := coreTag_lt_length (B.jobs.answer B.core B.q i)
    have hN := B.jobs.prepPrefix_mono B.core B.q A.heap (show i + 1 ≤ B.jobs.count by omega)
    change _ ≤ B.prepared A at hN
    have hEnd := hBlock.core_end_le
    rw [hPtr]
    refine ⟨B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _),?_,coreTag_at hBlock.1⟩
    omega
  refine ⟨?_, ⟨hLayout.size,hFit.bits,?_,?_,hLayout.childInj,?_,?_⟩,
    hLayout.savedBelow,hGraphs,hOffsets,hr,hSpace⟩
  · exact ⟨hKeep.graphs,hKeep.offsets,hKeep.replies,hKeep.count,hKeep.indices,by omega,
      fun a ha => hKeep.zero a (by omega)⟩
  · omega
  · omega
  · intro i hi
    obtain ⟨_,hCeil,hTag⟩ := hReply i hi
    have he : mem' (A.offsets+i) = B.jobs.offset i := by
      simpa [tabList] using hAt i (by simpa using hi)
    have hb := hLayout.savedBelow i hi
    have hEq := hLayout.offsets i hi
    have hW := hLayout.offsetWord i hi
    exact ⟨he.trans hEq,hEq ▸ hW,by omega,by omega,by omega,hTag⟩
  · intro i hi j hj
    have hBelow : saved + child i < A.graphs := hLayout.savedBelow i hi
    have hRep := (hReply j hj).1
    omega

set_option maxHeartbeats 550000 in
/-- Save the actual replies and compact the tables using the already completed
round. The proof applies to both exact and certified-choice model answers. -/
theorem buildGameStepTail_runs {w preparedEnd advance v prefixCost total : ℕ}
    {p : Program} {B : BuildRoundData} {A : BuildRoundAddrs} {start saved : ℕ}
    {child : ℕ → ℕ} {mem mid : ℕ → ℕ} {pos pos' : ℕ} {ω : ℕ → Bool}
    (hWords : ∀ a ∈ B.stepArgs A start saved, a < 2^w)
    (hFit : BuildRoundFit w B A mem)
    (hLayout : GameStepLayout w B A start saved child)
    (hSpace : B.record A + 2 + B.jobs.count < 2^w)
    (hRoundPost : (buildOneRoundContract w B).post (B.args A) mem v mid)
    (hEnd : MeetsContract w p preparedEnd (buildPreparedEndContract w B A))
    (hAdvance : MeetsContract w p advance (buildGameAdvanceContract w B A child))
    (hRows : ∀ Ms emb, B.indices.isEmpty = false → B.result.1 = .matched Ms emb →
      Ms.length = B.indices.length)
    (hBudget : prefixCost + (80*B.jobs.count + 48*B.indices.length + 205) ≤ total) :
    ∃ o st' c, Runs w p ω (buildGameStepTail preparedEnd advance)
      { startState (B.stepArgs A start saved) mem pos with
        mem := mid
        regs := Function.update (startState (B.stepArgs A start saved) mem pos).regs 17 v
        pos := pos' }
      o st' c ∧ (buildGameStepContract w B A start saved child).post
        (B.stepArgs A start saved) mem o.value st'.mem ∧ prefixCost+c ≤ total := by
  unfold buildGameStepTail
  have hRoundW : ∀ a ∈ B.args A, a < 2 ^ w := fun a ha =>
    hWords a (List.mem_append_left _ ha)
  have hStart := hWords start (by simp [BuildRoundData.stepArgs])
  have hSaved := hWords saved (by simp [BuildRoundData.stepArgs])
  have hn := hRoundW B.jobs.count (by simp [BuildRoundData.args])
  have hS := hRoundW B.childSize (by simp [BuildRoundData.args])
  have hG := hRoundW A.graphs (by simp [BuildRoundData.args])
  have hO := hRoundW A.offsets (by simp [BuildRoundData.args])
  have hR := hRoundW A.replies (by simp [BuildRoundData.args])
  have hw := hFit.bits
  have hOne : 1 < 2 ^ w := by omega
  have hTwo : 2 < 2 ^ w := by omega
  have hRecord := record_of_round hRoundPost
  have hv : v + 2 + B.jobs.count < 2 ^ w := hRecord ▸ hSpace
  have hKeep := oneRoundMemory_of_post hFit hRows hRoundPost
  have hLow := hKeep.preparedEnd
  have hPrep : B.prepared A < 2 ^ w := by omega
  let endArgs := [A.replies,B.jobs.count,B.childSize]
  have hEndW : ∀ a ∈ endArgs, a < 2 ^ w := by dsimp [endArgs]; wram_words
  refine runs_seq_call_le hEnd (vs := endArgs) (by rfl) hEndW
    ⟨rfl,hLayout.active,hKeep.replies,hw,hLayout.tableBelow,hPrep,
      hFit.childSize _ (by have := hLayout.active; omega)⟩ ?_
  intro prep m pos'' hPrepared
  obtain ⟨hPrepEq,hMemEq⟩ := hPrepared
  change prep = B.prepared A at hPrepEq
  change m = mid at hMemEq
  subst prep m
  have hV2 : v + 2 < 2 ^ w := by omega
  have hV1 : v + 1 < 2 ^ w := by omega
  refine runs_seq_assign_le (v := v + 2) ?_ ?_
  · simp [Expr.eval,Function.update,hTwo,hV2]
  let advArgs := [A.graphs,A.offsets,B.jobs.count,A.replies,B.prepared A,B.childSize,start,saved,v+2]
  have hAdvW : ∀ a ∈ advArgs, a < 2 ^ w := by dsimp [advArgs]; wram_words
  have hAdvFit := advanceFit_of_round hFit hLayout hKeep hv
  refine runs_seq_call_le hAdvance (vs := advArgs) ?_ hAdvW
    ⟨start,saved,v+2,rfl,hAdvFit⟩ ?_
  · simp [evalArgs,Expr.eval,Function.update,startState,advArgs,BuildRoundData.stepArgs,
      BuildRoundData.args]
  intro k after pos₃ hAdvPost
  refine runs_seq_store_le (x := v) (v := B.prepared A) ?_ ?_ ?_
  · simp [Expr.eval,Function.update]
  · simp [Expr.eval,Function.update]
  refine runs_seq_store_le (x := v+1) (v := B.jobs.count) ?_ ?_ ?_
  · simp [Expr.eval,Function.update,hOne,hV1]
  · rfl
  refine runs_ret_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · let out := Function.update (Function.update after v (B.prepared A)) (v+1) B.jobs.count
    have he : k = B.indices.length := by
      obtain ⟨a,b,c,eq,hk,_⟩ := hAdvPost
      exact hk
    refine ⟨hRecord,?_,mid,after,hRoundPost,he ▸ hAdvPost,?_,?_⟩
    · change ListAt out v _
      intro j hj
      have hCases : j = 0 ∨ j = 1 := by simp at hj; omega
      rcases hCases with rfl | rfl <;> simp [out,Function.update]
    · intro a hv₀ hv₁
      change a ≠ v at hv₀
      change a ≠ v+1 at hv₁
      change out a = after a
      dsimp [out]
      rw [Function.update_of_ne hv₁, Function.update_of_ne hv₀]
    · intro a hal
      change out a = 0
      change v+2+B.jobs.count ≤ a at hal
      obtain ⟨a₁,b₁,c₁,eq,_,_,_,_,_,hFrame⟩ := hAdvPost
      simp only [advArgs,List.cons.injEq,and_true,true_and] at eq
      obtain ⟨rfl,rfl,rfl⟩ := eq
      have hK := List.length_filter_le (fun i => decide (coreTag (B.jobs.answer B.core B.q i) = 0))
        (List.range B.jobs.count)
      have hkn : B.indices.length ≤ B.jobs.count := by
        simpa [BuildRoundData.indices,batchJobIndices,cutReplyIndices] using hK
      have hG := hLayout.graphsBelow
      have hO := hLayout.offsetsBelow
      have hR := hLayout.tableBelow
      have hP : A.heap ≤ B.prepared A :=
        B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
      have ha : after a = mid a := hFrame a (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr hal) (fun i hi _ => Nat.ne_of_gt (by have := hLayout.savedBelow i hi; omega))
      have h₀ : a ≠ v := by omega
      have h₁ : a ≠ v+1 := by omega
      have hz : mid a = 0 := hKeep.zero a (by omega)
      dsimp [out]
      rw [Function.update_of_ne h₁,Function.update_of_ne h₀,ha,hz]
  · simp [buildPreparedEndContract,buildGameAdvanceContract,
      Expr.size,argsSize,Nat.add_assoc]
    omega

/-- One game step retains the round data, saves the certificates, and leaves the
active arrays compacted for the next step. -/
theorem buildGameStepProc_meetsContract {w f round preparedEnd advance : ℕ} {p : Program}
    {B : BuildRoundData} {A : BuildRoundAddrs} {start saved : ℕ} {child : ℕ → ℕ}
    (hf : p.procs[f]? = some (buildGameStepProc round preparedEnd advance))
    (hRound : MeetsContract w p round (buildOneRoundContract w B))
    (hEnd : MeetsContract w p preparedEnd (buildPreparedEndContract w B A))
    (hAdvance : MeetsContract w p advance (buildGameAdvanceContract w B A child))
    (hRows : ∀ Ms emb, B.indices.isEmpty = false → B.result.1 = .matched Ms emb → Ms.length = B.indices.length) :
    MeetsContract w p f (buildGameStepContract w B A start saved child) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨rfl,hFit,hLayout,hSpace⟩ := hPre
  have hRoundW : ∀ a ∈ B.args A, a < 2 ^ w := fun a ha =>
    hWords a (List.mem_append_left _ ha)
  refine runs_start_le ?_
  unfold buildGameStepProc
  refine runs_seq_call_le hRound (vs := B.args A) (by rfl) hRoundW ⟨A,rfl,hFit⟩ ?_
  intro v mid pos' hPost
  refine buildGameStepTail_runs hWords hFit hLayout hSpace hPost hEnd hAdvance hRows ?_
  simp [buildGameStepContract,Expr.size,argsSize,startState]
  omega

end MinCostFlow.HierPaths
