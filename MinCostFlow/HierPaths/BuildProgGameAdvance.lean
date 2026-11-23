module

public import MinCostFlow.HierPaths.BuildProgPreparedEnd
public import MinCostFlow.HierPaths.BuildProgSaveCore
public import MinCostFlow.HierPaths.BuildProgActiveCompact
public import MinCostFlow.HierPaths.BuildProgCopy

/-!
# Saving replies and compacting the active tables

Keep an unmodified copy of the active offsets for each round. Then save the
expander replies by original child number and compact both active arrays by the
router's cut indices. The next round can use the same array addresses.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- Arguments are active graph and offset tables, count, reply table, prepared
end, child size, first child offset, saved table, and offset snapshot address. -/
def buildGameAdvanceProc (copy save compact : ℕ) : Stmt :=
  .seq (.call 9 copy [.reg 1, .reg 2, .reg 8])
  (.seq (.call 9 save [.reg 1, .reg 3, .reg 2, .reg 5, .reg 6, .reg 7])
  (.seq (.assign 10 (.bin .add (.reg 4) (.const 1)))
  (.seq (.assign 11 (.load (.reg 4)))
  (.seq (.call 9 compact [.reg 0, .reg 10, .reg 11])
  (.seq (.call 9 compact [.reg 1, .reg 10, .reg 11])
    (.ret (.reg 11)))))))

theorem buildGameAdvanceProc_noRand (copy save compact : ℕ) :
    (buildGameAdvanceProc copy save compact).NoRand := by
  simp [buildGameAdvanceProc, Stmt.NoRand]

/-- The input tables are disjoint and the round's replies and cut indices
remain available from the end of the routing pass. -/
structure GameAdvanceFit (w : ℕ) (B : BuildRoundData) (A : BuildRoundAddrs)
    (start saved out : ℕ) (mem : ℕ → ℕ) (child : ℕ → ℕ) : Prop where
  memory : OneRoundMemory B A mem out
  save : SaveCoreInput w B.jobs.count B.childSize start A.offsets A.replies saved mem child
    (fun i => B.jobs.answer B.core B.q i)
  savedBelow : ∀ i < B.jobs.count, saved + child i < A.graphs
  graphsBelow : A.graphs + B.jobs.count ≤ A.offsets
  offsetsBelow : A.offsets + B.jobs.count ≤ A.replies
  repliesBelow : A.replies + B.jobs.count ≤ B.prepared A
  snapshotEnd : out + B.jobs.count < 2 ^ w

/-- The exact new active arrays, the saved-reply update, and the old offsets. -/
def buildGameAdvanceContract (w : ℕ) (B : BuildRoundData) (A : BuildRoundAddrs)
    (child : ℕ → ℕ) : Contract where
  pre args mem := ∃ start saved out,
    args = [A.graphs,A.offsets,B.jobs.count,A.replies,B.prepared A,B.childSize,start,saved,out] ∧
    GameAdvanceFit w B A start saved out mem child
  post args mem v mem' := ∃ start saved out,
    args = [A.graphs,A.offsets,B.jobs.count,A.replies,B.prepared A,B.childSize,start,saved,out] ∧
    v = B.indices.length ∧
    ListAt mem' A.graphs (activeCompactWords (tabList B.jobs.count B.jobs.addr) B.indices) ∧
    ListAt mem' A.offsets (activeCompactWords (tabList B.jobs.count B.jobs.offset) B.indices) ∧
    ListAt mem' out (tabList B.jobs.count B.jobs.offset) ∧
    (∀ i < B.jobs.count, coreTag (B.jobs.answer B.core B.q i) ≠ 0 →
      mem' (saved + child i) = mem (A.replies + i)) ∧
    ∀ a, (a < A.graphs ∨ A.graphs + v ≤ a) →
      (a < A.offsets ∨ A.offsets + v ≤ a) →
      (a < out ∨ out + B.jobs.count ≤ a) →
      (∀ i < B.jobs.count, coreTag (B.jobs.answer B.core B.q i) ≠ 0 →
        a ≠ saved + child i) → mem' a = mem a
  cost _ _ := 80 * B.jobs.count + 48 * B.indices.length + 120

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- Saving and compacting preserves the round snapshot and all cells outside
the two new active tables, the snapshot, and the newly saved pointers. -/
theorem buildGameAdvanceProc_meetsContract {w f copy save compact : ℕ} {p : Program}
    {B : BuildRoundData} {A : BuildRoundAddrs} {child : ℕ → ℕ}
    (hf : p.procs[f]? = some (buildGameAdvanceProc copy save compact))
    (hc : p.procs[copy]? = some buildCopyProc)
    (hs : p.procs[save]? = some buildSaveCoreProc)
    (ha : p.procs[compact]? = some buildActiveCompactProc) :
    MeetsContract w p f (buildGameAdvanceContract w B A child) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨start,saved,out,rfl,hFit⟩ := hPre
  let n := B.jobs.count
  let k := B.indices.length
  let prep := B.prepared A
  let cuts := prep + 1
  let answer := fun i => B.jobs.answer B.core B.q i
  let graphs := tabList n B.jobs.addr
  let offsets := tabList n B.jobs.offset
  have hg : A.graphs + n ≤ A.offsets := hFit.graphsBelow
  have ho : A.offsets + n ≤ A.replies := hFit.offsetsBelow
  have hp : A.replies + n ≤ prep := hFit.repliesBelow
  have hout : cuts + k ≤ out := hFit.memory.preparedEnd
  have hwOut : out + n < 2 ^ w := hFit.snapshotEnd
  have hOne : 1 < 2 ^ w := by have := hFit.save.word; omega
  have hk : k ≤ n := by
    simpa [k,n,BuildRoundData.indices,batchJobIndices,cutReplyIndices] using
      List.length_filter_le (fun i => decide (coreTag (answer i) = 0)) (List.range n)
  have hIndices : ∀ i (hi : i < B.indices.length), i ≤ B.indices[i] ∧ B.indices[i] < n := by
    intro i hi
    exact ⟨le_cutReplyIndex answer n i hi,
      (mem_batchJobIndices.mp (List.getElem_mem hi)).1⟩
  have hgW := hWords A.graphs (by simp)
  have hoW := hWords A.offsets (by simp)
  have hnW := hWords n (by simp [n])
  have hrW := hWords A.replies (by simp)
  have hsW := hWords B.childSize (by simp)
  have hstartW := hWords start (by simp)
  have hsavedW := hWords saved (by simp)
  have houtW := hWords out (by simp)
  have hCutsW : cuts < 2 ^ w := by omega
  have hKW : k < 2 ^ w := by omega
  have hWordsG : ∀ a ∈ [A.graphs,cuts,k], a < 2^w := by wram_words
  have hWordsO : ∀ a ∈ [A.offsets,cuts,k], a < 2^w := by wram_words
  refine runs_start_le ?_
  unfold buildGameAdvanceProc
  refine runs_seq_call_le (buildCopyProc_meetsContract hc) (vs := [A.offsets,n,out])
    (by rfl) (by wram_words) ⟨A.offsets,n,out,rfl,by omega,hwOut,hOne⟩ ?_
  intro _ m₁ _ hCopy
  obtain ⟨_,_,_,he,hCopied,hFrame₁⟩ := hCopy
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl⟩ := he
  have hMem₁ : ∀ a < out, m₁ a = mem a := fun a hh => hFrame₁ a (Or.inl hh)
  have hSave : SaveCoreInput w n B.childSize start A.offsets A.replies saved m₁ child answer := by
    have hh := hFit.save
    refine ⟨hh.size,hh.word,hh.offsetsEnd,hh.repliesEnd,hh.childInj,?_,?_⟩
    · intro i hi
      obtain ⟨hl,hw,hos,hrs,ht,hTag⟩ := hh.data i hi
      have hP := (hFit.memory.replies.2 i hi).1
      have hEndCore := (hFit.memory.replies.2 i hi).2.core_end_le
      have hNext := B.jobs.prepPrefix_mono B.core B.q A.heap (show i+1 ≤ n by omega)
      change _ ≤ prep at hNext
      have hTagLower : mem (A.replies + i) + 3 < out := by
        rw [hP]
        have hlen := coreTag_lt_length (answer i)
        dsimp only [answer] at hlen
        omega
      rw [hMem₁ _ (by omega),hMem₁ _ (by omega),hMem₁ _ hTagLower]
      exact ⟨hl,hw,hos,hrs,ht,hTag⟩
    · intro i hi j hj
      rw [hMem₁ _ (by omega)]
      exact hh.tagsAbove i hi j hj
  refine runs_seq_call_le (buildSaveCoreProc_meetsContract hs)
    (vs := [A.offsets,A.replies,n,B.childSize,start,saved])
    (by rfl) (by wram_words) ⟨_,_,_,_,_,rfl,hSave⟩ ?_
  intro _ m₂ _ hSaveOut
  obtain ⟨_,_,_,_,_,he,hSaveOut⟩ := hSaveOut
  simp only [List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := he
  have hSaveFrame : ∀ a, A.graphs ≤ a → m₂ a = m₁ a := by
    intro a hal
    exact hSaveOut.2 a fun i hi _ => Nat.ne_of_gt ((hFit.savedBelow i hi).trans_le hal)
  have hGraphs : ListAt m₂ A.graphs graphs := by
    intro i hi
    rw [hSaveFrame _ (by omega),hMem₁ _ (by simp [graphs] at hi; omega)]
    exact hFit.memory.graphs i hi
  have hOffsets : ListAt m₂ A.offsets offsets := by
    intro i hi
    rw [hSaveFrame _ (by omega),hMem₁ _ (by simp [offsets] at hi; omega)]
    exact hFit.memory.offsets i hi
  have hIdx : ListAt m₂ cuts B.indices := by
    intro i hi
    rw [hSaveFrame _ (by dsimp [cuts]; omega),hMem₁ _ (by change i < k at hi; omega)]
    exact hFit.memory.indices i hi
  have hCount : m₂ prep = k := by
    rw [hSaveFrame _ (by omega),hMem₁ _ (by dsimp [cuts] at hout; omega)]
    exact hFit.memory.count
  refine runs_seq_assign_le (v := cuts) ?_ ?_
  · have hw : B.prepared A + 1 < 2 ^ w := hCutsW
    simp [Expr.eval,Function.update,startState,hOne,cuts,prep,hw]
  refine runs_seq_assign_le (v := k) ?_ ?_
  · have hh : m₂ (B.prepared A) = k := hCount
    simp [Expr.eval,Function.update,startState,hh]
  refine runs_seq_call_le (buildActiveCompactProc_meetsContract ha)
    (vs := [A.graphs,cuts,k]) ?_ hWordsG
      ⟨A.graphs,cuts,rfl,hGraphs,hIdx,by simp [graphs]; omega,by omega,hOne,by simpa [graphs] using hIndices⟩ ?_
  · simp [evalArgs,Expr.eval,Function.update,startState]
  intro _ m₃ _ hCompG
  obtain ⟨_,_,he,hNewG,hFrame₃⟩ := hCompG
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,_⟩ := he
  have hRight : ∀ a, A.offsets ≤ a → m₃ a = m₂ a :=
    fun a h => hFrame₃ a (Or.inr (by omega))
  have hOffsets' : ListAt m₃ A.offsets offsets := by
    intro i hi
    rw [hRight _ (by omega)]
    exact hOffsets i hi
  have hIdx' : ListAt m₃ cuts B.indices := by
    intro i hi
    rw [hRight _ (by dsimp [cuts]; omega)]
    exact hIdx i hi
  refine runs_seq_call_le (buildActiveCompactProc_meetsContract ha)
    (vs := [A.offsets,cuts,k]) ?_ hWordsO
      ⟨A.offsets,cuts,rfl,hOffsets',hIdx',by simp [offsets]; omega,by omega,hOne,by simpa [offsets] using hIndices⟩ ?_
  · simp [evalArgs,Expr.eval,Function.update,startState]
  intro _ m₄ _ hCompO
  obtain ⟨_,_,he,hNewO,hFrame₄⟩ := hCompO
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,_⟩ := he
  refine runs_ret_le (v := k) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · refine ⟨start,saved,out,rfl,rfl,?_,hNewO,?_,?_,?_⟩
    · intro i hi
      have hil : i < k := by simpa [activeCompactWords,k] using hi
      change m₄ (A.graphs + i) = _
      exact (hFrame₄ _ (Or.inl (by omega))).trans (hNewG i hi)
    · intro i hi
      rw [length_tabList] at hi
      change m₄ (out + i) = _
      calc
        m₄ (out + i) = m₃ (out + i) := hFrame₄ _ (Or.inr (by omega))
        _ = m₂ (out + i) := hRight _ (by omega)
        _ = m₁ (out + i) := hSaveFrame _ (by omega)
        _ = mem (A.offsets + i) := hCopied i hi
        _ = _ := hFit.memory.offsets i (by simpa [offsets] using hi)
    · intro i hi hsTag
      have hh := hFit.savedBelow i hi
      change m₄ (saved + child i) = mem (A.replies + i)
      calc
        m₄ (saved + child i) = m₃ (saved + child i) := hFrame₄ _ (Or.inl (by omega))
        _ = m₂ (saved + child i) := hFrame₃ _ (Or.inl hh)
        _ = m₁ (A.replies + i) := hSaveOut.1 i hi hsTag
        _ = _ := hMem₁ _ (by omega)
    · intro addr hg' ho' hout' hSave'
      change m₄ addr = mem addr
      exact (hFrame₄ _ ho').trans ((hFrame₃ _ hg').trans
        ((hSaveOut.2 _ hSave').trans (hFrame₁ _ hout')))
  · simp [buildGameAdvanceContract,buildCopyContract,buildSaveCoreContract,
      buildActiveCompactContract,Expr.size,argsSize,n,k,Nat.add_assoc]
    omega

end MinCostFlow.HierPaths
