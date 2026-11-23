module

public import MinCostFlow.HierPaths.BuildProgChoiceFit
import MinCostFlow.HierPaths.BuildProgGameNext

/-!
# Saved core replies

Each original child has one pointer slot. Once a core reply saves the
child, the slot points to the certificate retained in the round arena.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The saved pointers refer to complete certificate blocks in the arena. -/
def ChoiceSavedMemory (D : ChoiceLoopData) (heap : ℕ) (sts : ℕ → ChildState)
    (mem : ℕ → ℕ) : Prop :=
  ∀ c < D.count, ∀ S, (sts c).saved = some S →
    let addr := mem (D.saved+c)
    D.addrs.replies+D.count+1 ≤ addr ∧
    addr+(coreResultWords (.expander S)).length ≤ heap ∧
    ListAt mem addr (coreResultWords (.expander S))

/-- A round preserves old saved replies and records each new certificate. -/
theorem choiceSavedMemory_next {w tailBudget t heap v : ℕ} {D : ChoiceLoopData} {β : ℝ}
    {bh : ℕ} {sts : ℕ → ChildState} {initial mem after : ℕ → ℕ}
    {ans : ℕ → CoreResult} {bump : ℕ → ℕ} {rBump : ℕ}
    (h : ChoiceGameHyp D β bh) (hL : GameFixedLayout w D.geometry)
    (hM : ChoiceGameMemory D heap sts mem) (ht : t < D.limit)
    (hTrace : ChoiceLoopTrace w D initial t heap sts mem)
    (hRoom : ChoiceRoundBudget w tailBudget D heap sts)
    (hn : (D.round sts).jobs.count ≠ 0)
    (hCert : ∀ i < (D.round sts).jobs.count, CoreOutcomeSpec ParamConfig.default D.base.M
      (D.round sts).q ((D.round sts).jobs.graph i) (ans i))
    (hBump : (D.round sts).ValidBump ans bump)
    (hRBump : ((D.round sts).withReplies ans bump).ValidRouteBump rBump)
    (hOld : ChoiceSavedMemory D heap sts mem)
    (hPost : (buildGameStepContract w ((D.round sts).withReplies ans bump rBump) (D.atHeap heap)
      D.first D.saved (D.active sts)).post
      ((D.round sts).stepArgs (D.atHeap heap) D.first D.saved) mem v after) :
    ChoiceSavedMemory D (v+2+(D.round sts).jobs.count) (D.next sts ans)
      (Function.update after (D.directory+t) v) := by
  let B := (D.round sts).withReplies ans bump rBump
  let A := D.atHeap heap
  let out := Function.update after (D.directory+t) v
  have hPre := choiceStep_pre_of_memory h hL hM ht hTrace hRoom (Nat.pos_of_ne_zero hn)
  have hFit : BuildRoundFit w B A mem := (hPre.2.1.2.2 ans bump hCert hBump).1 rBump hRBump
  have hLay₀ := hPre.2.2.1
  have hLay : GameStepLayout w B A D.first D.saved (D.active sts) :=
    ⟨hLay₀.active,hLay₀.size,hLay₀.childInj,hLay₀.offsets,hLay₀.offsetWord,
      hLay₀.savedBelow,hLay₀.graphsBelow,hLay₀.offsetsBelow,hLay₀.tableBelow⟩
  have hRows (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ)
      (hne : B.indices.isEmpty = false) (he : B.result.1 = .matched Ms emb) :
      Ms.length = B.indices.length :=
    (D.matchedRows hCert h.router h.host h.positive h.expansion h.denominator h.children h.even hne he).1
  have hPostCopy := hPost
  obtain ⟨_,_,mid,adv,hRound,hAdv,hAF,_⟩ := hPostCopy
  have hRoundMem := oneRoundMemory_of_post hFit hRows hRound
  have hLow := hRoundMem.preparedEnd
  have hHeap : heap ≤ B.prepared A :=
    B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
  have hR := hLay.tableBelow
  have hG := hLay.graphsBelow
  have hO := hLay.offsetsBelow
  have hDir : D.directory + t < D.saved := by
    have hh := hL.directory
    change D.directory+D.limit ≤ D.saved at hh
    omega
  have hSaved := hL.saved
  change D.saved+D.count ≤ A.graphs at hSaved
  have hDirG : D.directory + t < A.graphs := by omega
  have hDirO : D.directory + t < A.offsets := by omega
  have hOutFrame (a : ℕ) (ha : A.graphs ≤ a) : out a = after a :=
    Function.update_of_ne (Nat.ne_of_gt (hDirG.trans_le ha)) ..
  have hCount : B.jobs.count ≤ D.count := D.active_le sts
  have hIndices : B.indices.length ≤ B.jobs.count := by
    simpa [BuildRoundData.indices,batchJobIndices,cutReplyIndices] using
      List.length_filter_le (fun i => decide (coreTag (B.jobs.answer B.core B.q i) = 0))
        (List.range B.jobs.count)
  have hHeapOld : A.replies + D.count + 1 ≤ heap := hL.replies.trans hM.heap
  have hOutSaved (a : ℕ) (ha : D.saved ≤ a) : out a = after a :=
    Function.update_of_ne (Nat.ne_of_gt (hDir.trans_le ha)) ..
  intro c hc S hS
  cases hSavedC : (sts c).saved with
  | some C =>
    have hSC : (D.next sts ans c).saved = some C := by
      simp [ChoiceLoopData.next,choiceGameRound,hc,childStepAnswer,hSavedC]
    have e : C = S := Option.some.inj (hSC.symm.trans hS)
    subst S
    obtain ⟨hStart,hEnd,hBlock⟩ := hOld c hc C hSavedC
    have hPreserve (a : ℕ)
        (hReg : (a < A.replies ∧ B.unchangedBelow a) ∨ A.replies+B.jobs.count+1 ≤ a ∧ a < heap)
        (hAG : a < A.graphs ∨ A.graphs+B.indices.length ≤ a)
        (hAO : a < A.offsets ∨ A.offsets+B.indices.length ≤ a)
        (hAS : ∀ i < B.jobs.count, coreTag (B.jobs.answer B.core B.q i) ≠ 0 →
          a ≠ D.saved + D.active sts i) (ha : D.saved ≤ a) : out a = mem a :=
      (hOutSaved a ha).trans (gameStep_prefix_frame hFit hLay hRows hPost hReg hAG hAO hAS)
    have hCell : D.saved+c < A.graphs := by omega
    have hSafe : B.unchangedBelow (D.saved+c) := by
      by_cases hem : B.indices.isEmpty = true
      · exact Or.inl hem
      · refine Or.inr fun Ms emb hm i hi => Or.inl ?_
        have hIdx := (mem_batchJobIndices.mp (rowIndex_mem (emb := emb) hi
          (hRows Ms emb (Bool.eq_false_iff.mpr hem) hm))).1
        have hs := (hL.slots _ (D.active_mem hIdx).1).1
        change A.offsets+D.count ≤ D.childAddr (D.active sts ((B.applyData Ms emb).child i)) at hs
        change D.saved+c < D.childAddr (D.active sts ((B.applyData Ms emb).child i))
        omega
    have hp : out (D.saved+c) = mem (D.saved+c) :=
      hPreserve _ (Or.inl ⟨by omega,hSafe⟩) (Or.inl hCell) (Or.inl (by omega))
        (fun i hi _ he => by
          have hEq : c = D.active sts i := Nat.add_left_cancel he
          have hAct := (D.active_mem hi).2
          rw [← hEq,hSavedC] at hAct
          contradiction) (Nat.le_add_right _ _)
    change D.addrs.replies + D.count + 1 ≤ out (D.saved+c) ∧
      out (D.saved+c) + (coreResultWords (.expander C)).length ≤ v+2+(D.round sts).jobs.count ∧
      ListAt out (out (D.saved+c)) (coreResultWords (.expander C))
    rw [hp]
    refine ⟨hStart,by omega,WordRAM.ListAt.congr hBlock fun a ha hb => ?_⟩
    have hFrom : A.replies + D.count + 1 ≤ a := hStart.trans ha
    exact hPreserve a (Or.inr ⟨by omega,hb.trans_le hEnd⟩) (Or.inr (by omega))
      (Or.inr (by omega)) (fun i hi _ => Nat.ne_of_gt ((hLay.savedBelow i hi).trans_le (by omega)))
      (by omega)
  | none =>
    have hm : c ∈ activeChildren D.count sts := by simp [activeChildren,hc,hSavedC]
    let i := (activeChildren D.count sts).idxOf c
    have hi : i < (D.round sts).jobs.count := List.idxOf_lt_length_iff.mpr hm
    have hic : D.active sts i = c := by
      unfold ChoiceLoopData.active
      rw [List.getD_eq_getElem _ _ hi, List.getElem_idxOf hi]
    have hAns : ans i = .expander S := by
      have hEq : answerByChild D.count sts ans c = ans i := hic ▸ answerByChild_getD ans hi
      cases ha : ans i with
      | cut U =>
        simp [ChoiceLoopData.next,choiceGameRound,hc,childStepAnswer,hSavedC,hEq,ha] at hS
      | expander C =>
        have hh : (D.next sts ans c).saved = some C := by
          simp [ChoiceLoopData.next,choiceGameRound,hc,childStepAnswer,hSavedC,hEq,ha]
        exact congrArg CoreResult.expander (Option.some.inj (hh.symm.trans hS))
    change i < B.jobs.count at hi
    let ptr := B.jobs.prepPrefix B.core B.q heap i
    obtain ⟨hPtr,hPrep⟩ := hRoundMem.replies.2 i hi
    have hReply : B.jobs.answer B.core B.q i = .expander S := hAns
    rw [hReply] at hPrep
    have hStart : heap ≤ ptr := B.jobs.prepPrefix_mono B.core B.q heap (Nat.zero_le i)
    have hEnd : ptr+(coreResultWords (.expander S)).length ≤ B.prepared A := by
      have hnext := B.jobs.prepPrefix_mono B.core B.q heap (Nat.succ_le_of_lt hi)
      exact hPrep.core_end_le.trans hnext
    obtain ⟨_,_,_,he,_,_,_,_,hSet,hKeep⟩ := hAdv
    simp only [List.cons.injEq,and_true,true_and] at he
    obtain ⟨rfl,rfl,rfl⟩ := he
    have hpCell : out (D.saved+c) = ptr := by
      have hCell : D.saved+c < A.graphs := by omega
      rw [hOutSaved _ (Nat.le_add_right _ _),hAF _ (by omega) (by omega)]
      have hTag : coreTag (B.jobs.answer B.core B.q i) ≠ 0 := by simp [hReply,coreTag]
      rw [← hic,hSet i hi hTag]
      exact hPtr
    change D.addrs.replies + D.count + 1 ≤ out (D.saved+c) ∧
      out (D.saved+c)+(coreResultWords (.expander S)).length ≤ v+2+(D.round sts).jobs.count ∧
      ListAt out (out (D.saved+c)) (coreResultWords (.expander S))
    rw [hpCell]
    refine ⟨hHeapOld.trans hStart,by omega,WordRAM.ListAt.congr hPrep.1 fun a ha hb => ?_⟩
    have hFrom := hStart.trans ha
    have hUntil := hb.trans_le hEnd
    have hAfterG : A.graphs + B.indices.length ≤ a := by omega
    have hAfterO : A.offsets + B.indices.length ≤ a := by omega
    exact (hOutSaved a (by omega)).trans ((hAF a (by omega) (by omega)).trans
      (hKeep a (Or.inr hAfterG) (Or.inr hAfterO) (Or.inl (by omega))
        (fun j hj _ => Nat.ne_of_gt ((hLay.savedBelow j hj).trans_le (by omega)))))

/-- At the end of the game every saved model set has its reply in RAM. -/
theorem ChoiceLoopTrace.savedMemory {w tailBudget : ℕ} {D : ChoiceLoopData} {β : ℝ} {bh : ℕ}
    {initial mem : ℕ → ℕ} {t heap : ℕ} {sts : ℕ → ChildState}
    (hTrace : ChoiceLoopTrace w D initial t heap sts mem) (ht : t ≤ D.limit)
    (h : ChoiceGameHyp D β bh) (hL : GameFixedLayout w D.geometry)
    (hInit : ChoiceGameMemory D D.addrs.heap (fun _ => ChildState.init) initial)
    (hRoom : ∀ t heap sts mem, t < D.limit →
      ChoiceLoopTrace w D initial t heap sts mem → (D.round sts).jobs.count ≠ 0 →
      ChoiceRoundBudget w tailBudget D heap sts) :
    ChoiceSavedMemory D heap sts mem := by
  induction hTrace with
  | start =>
    intro c hc S hS
    cases hS
  | skip _ _ ih => exact ih (Nat.le_of_succ_le ht)
  | run hTrace hn ans bump rBump hCert hBump hRBump hPost ih =>
    exact choiceSavedMemory_next h hL
      (hTrace.memory (Nat.le_of_succ_le ht) h hL hInit hRoom) ht hTrace
      (hRoom _ _ _ _ ht hTrace hn) hn hCert hBump hRBump (ih (Nat.le_of_succ_le ht)) hPost

end MinCostFlow.HierPaths
