module

public import MinCostFlow.HierPaths.BuildProgGamePre

/-!
# The loop memory invariant after a round

The active arrays have the next model order. The matching rows give the new
graphs of the requesting children. The other graphs and the parent input
stay in their original reservations.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

private theorem graph_eq_of_not_requesting (S : BuildGameSchedule) (t c : ℕ) (hc : c < S.count)
    (h : c ∉ requesting S.base.core S.base.M S.base.r S.base.childSize S.count S.offset (S.states t)) :
    gameGraph S.base.childSize (S.states (t+1) c) = gameGraph S.base.childSize (S.states t c) := by
  let st := S.states t c
  change gameGraph S.base.childSize (gameRound S.base.route S.base.host S.base.verts S.base.Δ S.base.L
    S.base.core S.base.M S.base.r S.base.childSize S.count S.offset (S.states t) c) = _
  have hReq := (requesting_spec S.base.core S.base.M S.base.r S.base.childSize S.count S.offset
    (S.states t)).2 c
  change c ∉ _ at h
  have hNo : ¬(request S.base.core S.base.M S.base.r S.base.childSize (S.offset c) st).isSome :=
    fun hyes => h (hReq.mpr ⟨hc,hyes⟩)
  change gameGraph S.base.childSize _ = gameGraph S.base.childSize st
  cases hs : st.saved with
  | some T =>
    change (S.states t c).saved = some T at hs
    simp [gameRound,hs,st]
  | none =>
    cases ha : coreAnswer S.base.core S.base.M S.base.r S.base.childSize st with
    | cut U => simp [request,hs,ha] at hNo
    | expander T =>
      change (S.states t c).saved = none at hs
      change coreAnswer S.base.core S.base.M S.base.r S.base.childSize (S.states t c) = .expander T at ha
      simp only [gameRound,hs,ha]
      rfl

private theorem graph_eq_when_empty {S : BuildGameSchedule} {t c : ℕ} (hc : c < S.count)
    (hEmpty : (S.round t).indices = []) :
    gameGraph S.base.childSize (S.states (t+1) c) = gameGraph S.base.childSize (S.states t c) := by
  apply graph_eq_of_not_requesting S t c hc
  have hMap := modelGameJobs_indices S.base.core S.base.M S.base.r S.base.childSize S.count
    S.offset S.childAddr (S.states t)
  change (S.round t).indices.map _ = _ at hMap
  rw [hEmpty,List.map_nil] at hMap
  rw [← hMap]
  simp

/-- During an iteration with an empty active table, the graph and memory data
already represent the next model round. -/
theorem GameMemory.skip_round {S : BuildGameSchedule} {t : ℕ} {mem : ℕ → ℕ}
    (hM : GameMemory S t mem) (hEmpty : (S.round t).jobs.count = 0) :
    GameMemory S (t+1) mem := by
  have hIdx := S.indices_empty hEmpty
  have hCount : (S.round (t+1)).jobs.count = 0 :=
    (S.count_succ t).trans (congrArg List.length hIdx)
  have hh : S.heap (t+1) = S.heap t := by
    simp only [BuildGameSchedule.heap,hEmpty,ite_true]
  refine ⟨hM.host,hM.verts,?_,?_,?_,hh ▸ hM.zero⟩
  · simp [hCount,tabList,ListAt]
  · simp [hCount,tabList,ListAt]
  · intro c hc
    rw [graph_eq_when_empty hc hIdx]
    exact hM.children c hc

/-- A row index and its original child number. -/
theorem BuildGameSchedule.rowChild {S : BuildGameSchedule} {t : ℕ}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ} {i : ℕ}
    (hi : i < Ms.length) (hRows : Ms.length = (S.round t).indices.length) :
    let D := (S.round t).applyData Ms emb
    D.child i < (S.round t).jobs.count ∧
      S.child t (D.child i) ∈ requesting S.base.core S.base.M S.base.r S.base.childSize S.count
        S.offset (S.states t) := by
  let B := S.round t
  let D := B.applyData Ms emb
  have hi' : i < B.indices.length := hRows ▸ hi
  have ha : D.child i ∈ B.indices := by
    change B.indices.getD i 0 ∈ B.indices
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  refine ⟨(mem_batchJobIndices.mp ha).1,?_⟩
  have hMap := modelGameJobs_indices S.base.core S.base.M S.base.r S.base.childSize S.count
    S.offset S.childAddr (S.states t)
  change B.indices.map (S.child t) = _ at hMap
  rw [← hMap]
  exact List.mem_map_of_mem ha

private theorem row_for_child {S : BuildGameSchedule} {t c : ℕ}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hRows : Ms.length = (S.round t).indices.length)
    (hreq : c ∈ requesting S.base.core S.base.M S.base.r S.base.childSize S.count S.offset
      (S.states t)) :
    ∃ i < Ms.length, S.child t (((S.round t).applyData Ms emb).child i) = c := by
  have hMap := modelGameJobs_indices S.base.core S.base.M S.base.r S.base.childSize S.count
    S.offset S.childAddr (S.states t)
  change (S.round t).indices.map (S.child t) = _ at hMap
  rw [← hMap] at hreq
  obtain ⟨j,hj,hc⟩ := List.mem_map.mp hreq
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hj
  refine ⟨i,hRows ▸ hi,?_⟩
  change S.child t ((S.round t).indices.getD i 0) = c
  rw [List.getD_eq_getElem _ _ hi]
  exact hc

/-- The table updates preserve the round data above both active tables. -/
theorem stepAboveTables {w : ℕ} {B : BuildRoundData} {A : BuildRoundAddrs}
    {start saved v : ℕ} {child : ℕ → ℕ} {mem after : ℕ → ℕ}
    (hLay : GameStepLayout w B A start saved child)
    (hPost : (buildGameStepContract w B A start saved child).post
      (B.stepArgs A start saved) mem v after) :
    ∃ mid, (buildOneRoundContract w B).post (B.args A) mem v mid ∧
      ∀ a, A.offsets + B.jobs.count ≤ a → a < v → after a = mid a := by
  obtain ⟨_,_,mid,adv,hR,hA,hFrame,_⟩ := hPost
  obtain ⟨_,_,_,eq,_,_,_,_,_,hAF⟩ := hA
  simp only [List.cons.injEq,and_true,true_and] at eq
  obtain ⟨rfl,rfl,rfl⟩ := eq
  refine ⟨mid,hR,?_⟩
  have hk : B.indices.length ≤ B.jobs.count := by
    simpa [BuildRoundData.indices,batchJobIndices,cutReplyIndices] using List.length_filter_le
      (fun i => decide (coreTag (B.jobs.answer B.core B.q i) = 0)) (List.range B.jobs.count)
  have hg := hLay.graphsBelow
  intro a hlo hhi
  exact (hFrame a (by omega) (by omega)).trans
    (hAF a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
      (fun i hi _ => Nat.ne_of_gt ((hLay.savedBelow i hi).trans_le (by omega))))

/-- A running iteration establishes the invariant with the next model graphs.
The directory write lies below the saved table and leaves the input and
graph blocks available. -/
theorem GameMemory.advance_round {w : ℕ} {S : BuildGameSchedule} {cfg : ParamConfig} {β : ℝ}
    {bh t v : ℕ} {mem after : ℕ → ℕ}
    (hM : GameMemory S t mem) (hL : GameFixedLayout w S) (hP : BuildGamePlayerBounds S cfg β bh)
    (ht : t < S.data.limit) (hn : (S.round t).jobs.count ≠ 0)
    (hFit : BuildRoundFit w (S.round t) (S.data.addrs t) mem)
    (hLay : GameStepLayout w (S.round t) (S.data.addrs t) S.start S.saved (S.child t))
    (hPost : (buildGameStepContract w (S.round t) (S.data.addrs t) S.start S.saved (S.child t)).post
      ((S.round t).stepArgs (S.data.addrs t) S.start S.saved) mem v after) :
    GameMemory S (t+1) (Function.update after (S.directory+t) v) := by
  let B := S.round t
  let A := S.data.addrs t
  let out := Function.update after (S.directory+t) v
  have hRows (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ) :
      B.indices.isEmpty = false → B.result.1 = .matched Ms emb → Ms.length = B.indices.length :=
    fun hne hm => hP.rows ht (fun h => (Bool.eq_false_iff.mp hne) (List.isEmpty_iff.mpr h)) hm
  obtain ⟨mid,hR,hMid⟩ := stepAboveTables hLay hPost
  have hRound := roundEffects_of_post hFit hR
  have hLow := (oneRoundMemory_of_post hFit hRows hR).preparedEnd
  change B.prepared A + 1 + B.indices.length ≤ v at hLow
  have hH : A.heap ≤ B.prepared A := B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
  have hTable := hLay.tableBelow
  have hG := hL.graphs
  have hO := hL.offsets
  have hD := hL.directory
  have hSaved := hL.saved
  have hDir : S.directory + t < S.saved := by omega
  have hnB : B.jobs.count ≤ S.count := S.count_le t
  have hk : B.indices.length ≤ B.jobs.count := by
    simpa [BuildRoundData.indices,batchJobIndices,cutReplyIndices] using List.length_filter_le
      (fun i => decide (coreTag (B.jobs.answer B.core B.q i) = 0)) (List.range B.jobs.count)
  have hGeo : S.addrs.replies < v := by
    change A.replies + B.jobs.count + 1 ≤ A.heap at hTable
    change A.replies < v
    omega
  have hDirG : S.directory + t < S.addrs.graphs := by omega
  have hDirO : S.directory + t < S.addrs.offsets := by omega
  have hHeapEq : S.heap (t+1) = v+2+B.jobs.count := by
    simp only [BuildGameSchedule.heap,hn,ite_false]
    exact congrArg (fun b => b+2+B.jobs.count) hPost.1.symm
  have noChangeBelow (a : ℕ) (ha : a < S.directory) : out a = mem a := by
    have hSafe : B.unchangedBelow a := by
      by_cases he : B.indices.isEmpty = true
      · exact Or.inl he
      · refine Or.inr ?_
        intro Ms emb hm i hi
        have hR := S.rowChild (emb := emb) hi (hRows Ms emb (Bool.eq_false_iff.mpr he) hm)
        have hc := (S.child_active hR.1).1
        have hSlot := (hL.slots _ hc).1
        left
        change a < S.childAddr (S.child t (((S.round t).applyData Ms emb).child i))
        omega
    have hFr : after a = mem a := gameStep_prefix_frame hFit hLay hRows hPost
      (Or.inl ⟨by change a < S.addrs.replies; omega,hSafe⟩) (Or.inl (by change a < S.addrs.graphs; omega))
      (Or.inl (by change a < S.addrs.offsets; omega)) (fun _ _ _ => Nat.ne_of_lt (by omega))
    exact (Function.update_of_ne (Nat.ne_of_lt (by omega)) ..).trans hFr
  obtain ⟨hGraphs,hOffsets⟩ := S.step_active_tables hFit hLay hRows hPost
  have updatePast (a : ℕ) (ha : S.addrs.graphs ≤ a) : out a = after a :=
    Function.update_of_ne (Nat.ne_of_gt (hDirG.trans_le ha)) ..
  refine ⟨WordRAM.ListAt.congr hM.host (fun a _ hu => noChangeBelow a (hu.trans_le hL.host)),
    WordRAM.ListAt.congr hM.verts (fun a _ hu => noChangeBelow a (hu.trans_le hL.verts)),
    WordRAM.ListAt.congr hGraphs (fun a hl _ => updatePast a hl),
    WordRAM.ListAt.congr hOffsets (fun a hl _ => updatePast a (by omega)),?_,?_⟩
  · intro c hc
    let req := requesting S.base.core S.base.M S.base.r S.base.childSize S.count S.offset (S.states t)
    have hSlot := hL.slots c hc
    by_cases hReq : c ∈ req
    · have hne : B.indices.isEmpty = false := by
        apply Bool.eq_false_iff.mpr
        intro he
        have hm := modelGameJobs_indices S.base.core S.base.M S.base.r S.base.childSize S.count
          S.offset S.childAddr (S.states t)
        change B.indices.map _ = req at hm
        rw [List.isEmpty_iff.mp he,List.map_nil] at hm
        exact List.not_mem_nil (hm ▸ hReq)
      obtain ⟨Ms,emb,hRes,hWrite⟩ := hRound.2.2 hne
      obtain ⟨i,hi,hc'⟩ := row_for_child (emb := emb) (hRows Ms emb hne hRes) hReq
      let D := B.applyData Ms emb
      have hg : GraphAt mid (D.addr i) (appendGameMatching (D.graph i) (D.offset i) (Ms.getD i [])) :=
        (hWrite i hi).1
      have hge : appendGameMatching (D.graph i) (D.offset i) (Ms.getD i []) =
          gameGraph B.childSize (S.states (t+1) (S.child t (D.child i))) :=
        hP.graph_succ ht hRes hne hi
      rw [hge] at hg
      change GraphAt mid (S.childAddr (S.child t (((S.round t).applyData Ms emb).child i)))
        (gameGraph S.base.childSize (S.states (t+1) (S.child t (((S.round t).applyData Ms emb).child i)))) at hg
      rw [hc'] at hg
      refine WordRAM.ListAt.congr hg fun a hlo hhi => ?_
      have hBound := (hP.gameGraph_bounds (Nat.succ_le_of_lt ht) hc).2.2.1
      have hLen : (gameGraph S.base.childSize (S.states (t+1) c)).encode.length ≤ S.slotWords :=
        hBound.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)
      have ha := hhi.trans_le ((Nat.add_le_add_left hLen _).trans hSlot.2)
      exact (updatePast a (by omega)).trans (hMid a (by
        change S.addrs.offsets + B.jobs.count ≤ a
        omega) (ha.trans hGeo))
    · rw [graph_eq_of_not_requesting S t c hc hReq]
      refine WordRAM.ListAt.congr (hM.children c hc) fun a hlo hhi => ?_
      have hBound := (hP.gameGraph_bounds ht.le hc).2.2.1
      have hLen : (gameGraph S.base.childSize (S.states t c)).encode.length ≤ S.slotWords :=
        hBound.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)
      have ha := hhi.trans_le ((Nat.add_le_add_left hLen _).trans hSlot.2)
      have hSafe : B.unchangedBelow a := by
        by_cases he : B.indices.isEmpty = true
        · exact Or.inl he
        · refine Or.inr ?_
          intro Ms emb hm i hi
          let D := B.applyData Ms emb
          have hne : B.indices.isEmpty = false := Bool.eq_false_iff.mpr he
          have hRow := S.rowChild (emb := emb) hi (hRows Ms emb hne hm)
          have hChild := (S.child_active hRow.1).1
          have hcNe : c ≠ S.child t (D.child i) := by
            intro heq
            exact hReq (heq ▸ hRow.2)
          obtain hd | hd := hL.slotsApart c hc _ hChild hcNe
          · exact Or.inl ((hhi.trans_le (Nat.add_le_add_left hLen _)).trans_le hd)
          · exact Or.inr ((hP.matchedCap ht hm hne hi).trans (hd.trans hlo))
      exact (updatePast a (by omega)).trans
        (gameStep_prefix_frame hFit hLay hRows hPost (Or.inl ⟨ha,hSafe⟩)
          (Or.inr (by change S.addrs.graphs + B.indices.length ≤ a; omega))
          (Or.inr (by change S.addrs.offsets + B.indices.length ≤ a; omega))
          (fun i hi _ => Nat.ne_of_gt ((hLay.savedBelow i hi).trans_le (by change S.addrs.graphs ≤ a; omega))))
  · intro a ha
    rw [hHeapEq] at ha
    obtain ⟨_,_,_,_,_,_,_,hZero⟩ := hPost
    exact (updatePast a (by omega)).trans (hZero a ha)

end MinCostFlow.HierPaths
