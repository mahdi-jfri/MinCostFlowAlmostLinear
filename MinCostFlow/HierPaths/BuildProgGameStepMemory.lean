module

public import MinCostFlow.HierPaths.BuildProgGameProcs
public import MinCostFlow.HierPaths.BuildProgGameTables

/-!
# Reading the memory of a completed game step

The postcondition retains the executions of the round and the active-table
update. Their frame lemmas show that the final memory keeps the data needed
by the loop and the injection pass.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The written certificate cells are the only writable cells below the
active tables. With the updated graph intervals excluded, the rest of
the old prefix and the old arena are kept. -/
theorem gameStep_prefix_frame {w : ℕ} {B : BuildRoundData} {A : BuildRoundAddrs}
    {start saved v : ℕ} {child : ℕ → ℕ} {mem after : ℕ → ℕ}
    (hFit : BuildRoundFit w B A mem) (hLayout : GameStepLayout w B A start saved child)
    (hRows : ∀ Ms emb, B.indices.isEmpty = false → B.result.1 = .matched Ms emb →
      Ms.length = B.indices.length)
    (hPost : (buildGameStepContract w B A start saved child).post (B.stepArgs A start saved)
      mem v after) {a : ℕ}
    (hRegion : (a < A.replies ∧ B.unchangedBelow a) ∨ A.replies + B.jobs.count + 1 ≤ a ∧ a < A.heap)
    (hG : a < A.graphs ∨ A.graphs + B.indices.length ≤ a)
    (hO : a < A.offsets ∨ A.offsets + B.indices.length ≤ a)
    (hS : ∀ i < B.jobs.count, coreTag (B.jobs.answer B.core B.q i) ≠ 0 → a ≠ saved + child i) :
    after a = mem a := by
  obtain ⟨_,_,mid,adv,hRound,hAdv,hFrame,_⟩ := hPost
  have hLower := (oneRoundMemory_of_post hFit hRows hRound).preparedEnd
  have hHeap : A.heap ≤ B.prepared A :=
    B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
  have hTable := hLayout.tableBelow
  have ha : a < A.heap := hRegion.elim (fun h => h.1.trans_le (by omega)) And.right
  have hA := advancePost_frame hAdv hG hO (Or.inl (by omega)) hS
  have hE := roundEffects_of_post hFit hRound
  rw [hFrame a (by omega) (by omega),hA]
  exact hRegion.elim (fun h => hE.1 a h.1 h.2) (fun h => hE.2.1 a h.1 h.2)
where
  advancePost_frame {w : ℕ} {B : BuildRoundData} {A : BuildRoundAddrs}
      {start saved out : ℕ} {child : ℕ → ℕ} {mid adv : ℕ → ℕ}
      (h : (buildGameAdvanceContract w B A child).post
        [A.graphs,A.offsets,B.jobs.count,A.replies,B.prepared A,B.childSize,start,saved,out]
        mid B.indices.length adv) {a : ℕ}
      (hG : a < A.graphs ∨ A.graphs + B.indices.length ≤ a)
      (hO : a < A.offsets ∨ A.offsets + B.indices.length ≤ a)
      (hOut : a < out ∨ out + B.jobs.count ≤ a)
      (hS : ∀ i < B.jobs.count, coreTag (B.jobs.answer B.core B.q i) ≠ 0 → a ≠ saved + child i) :
      adv a = mid a := by
    obtain ⟨_,_,_,he,_,_,_,_,_,hFrame⟩ := h
    simp only [List.cons.injEq,and_true,true_and] at he
    obtain ⟨rfl,rfl,rfl⟩ := he
    exact hFrame a hG hO hOut hS

/-- The current step's active arrays are the corresponding arrays of the
next model state. -/
theorem BuildGameSchedule.step_active_tables {w t v : ℕ} {S : BuildGameSchedule}
    {mem after : ℕ → ℕ} (hFit : BuildRoundFit w (S.round t) (S.data.addrs t) mem)
    (hLayout : GameStepLayout w (S.round t) (S.data.addrs t) S.start S.saved (S.child t))
    (hRows : ∀ Ms emb, (S.round t).indices.isEmpty = false →
      (S.round t).result.1 = .matched Ms emb → Ms.length = (S.round t).indices.length)
    (hPost : (buildGameStepContract w (S.round t) (S.data.addrs t) S.start S.saved (S.child t)).post
      ((S.round t).stepArgs (S.data.addrs t) S.start S.saved) mem v after) :
    ListAt after S.addrs.graphs (tabList (S.round (t+1)).jobs.count (S.round (t+1)).jobs.addr) ∧
    ListAt after S.addrs.offsets (tabList (S.round (t+1)).jobs.count (S.round (t+1)).jobs.offset) := by
  let B := S.round t
  let A := S.data.addrs t
  obtain ⟨_,_,mid,adv,hR,hAdv,hFrame,_⟩ := hPost
  have hLow := (oneRoundMemory_of_post hFit hRows hR).preparedEnd
  change B.prepared A + 1 + B.indices.length ≤ v at hLow
  have hHeap : A.heap ≤ B.prepared A :=
    B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
  have hG := hLayout.graphsBelow
  have hO := hLayout.offsetsBelow
  have hR := hLayout.tableBelow
  change A.graphs + B.jobs.count ≤ A.offsets at hG
  change A.offsets + B.jobs.count ≤ A.replies at hO
  change A.replies + B.jobs.count + 1 ≤ A.heap at hR
  have hK : B.indices.length ≤ B.jobs.count := by
    simpa [BuildRoundData.indices,batchJobIndices,cutReplyIndices] using
      List.length_filter_le (fun i => decide (coreTag (B.jobs.answer B.core B.q i) = 0))
        (List.range B.jobs.count)
  obtain ⟨_,_,_,he,_,hGraphs,hOffsets,_,_,_⟩ := hAdv
  have hGraphs' : ListAt after A.graphs
      (activeCompactWords (tabList B.jobs.count B.jobs.addr) B.indices) :=
    WordRAM.ListAt.congr hGraphs (fun a _ ha => by
      have ha' : a < A.graphs + B.indices.length := by simpa [activeCompactWords] using ha
      exact hFrame a (by omega) (by omega))
  have hOffsets' : ListAt after A.offsets
      (activeCompactWords (tabList B.jobs.count B.jobs.offset) B.indices) :=
    WordRAM.ListAt.congr hOffsets (fun a _ ha => by
      have ha' : a < A.offsets + B.indices.length := by simpa [activeCompactWords] using ha
      exact hFrame a (by omega) (by omega))
  exact ⟨S.compact_table t S.childAddr ▸ hGraphs', S.compact_table t S.offset ▸ hOffsets'⟩

end MinCostFlow.HierPaths
