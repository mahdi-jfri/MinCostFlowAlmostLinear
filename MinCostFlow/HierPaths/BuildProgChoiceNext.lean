module

public import MinCostFlow.HierPaths.BuildProgChoicePre
import MinCostFlow.HierPaths.BuildProgGameNext

/-!
# The chosen round preserves the graph memory invariant

The router rows write the requesting children. The saved children and all
other graph slots are disjoint from those writes. The compacted lists
therefore describe the next certified model state.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

theorem rowIndex_mem {D : ChoiceLoopData} {sts : ℕ → ChildState} {ans : ℕ → CoreResult}
    {bump : ℕ → ℕ} {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ} {i : ℕ}
    (hi : i < Ms.length) (hRows : Ms.length = ((D.round sts).withReplies ans bump).indices.length) :
    let B := (D.round sts).withReplies ans bump
    (B.applyData Ms emb).child i ∈ B.indices := by
  let B := (D.round sts).withReplies ans bump
  change B.indices.getD i 0 ∈ B.indices
  have hi' : i < B.indices.length := hRows ▸ hi
  rw [List.getD_eq_getElem _ _ hi']
  exact List.getElem_mem hi'

private theorem rowOfChild {D : ChoiceLoopData} {sts : ℕ → ChildState} {ans : ℕ → CoreResult}
    {bump : ℕ → ℕ} {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ} {c : ℕ}
    (hRows : Ms.length = ((D.round sts).withReplies ans bump).indices.length)
    (hc : c ∈ choiceRequesting D.base.childSize D.count D.offset sts (answerByChild D.count sts ans)) :
    ∃ i < Ms.length, D.active sts ((((D.round sts).withReplies ans bump).applyData Ms emb).child i) = c := by
  rw [← D.selected_eq sts ans] at hc
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hc
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hj
  refine ⟨i,hRows ▸ hi,?_⟩
  change D.active sts (((D.round sts).withReplies ans bump).indices.getD i 0) = c
  rw [show ((D.round sts).withReplies ans bump).indices = ((D.round sts).withReplies ans).indices from rfl,
    List.getD_eq_getElem _ _ hi]
  exact he

/-- The actual certified step leaves the next model graphs and active tables
in their reserved slots. -/
theorem choiceGameMemory_next {w tailBudget t heap v : ℕ} {D : ChoiceLoopData} {β : ℝ}
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
    (hPost : (buildGameStepContract w ((D.round sts).withReplies ans bump rBump) (D.atHeap heap)
      D.first D.saved (D.active sts)).post
      ((D.round sts).stepArgs (D.atHeap heap) D.first D.saved) mem v after) :
    ChoiceGameMemory D (v+2+(D.round sts).jobs.count) (D.next sts ans)
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
  obtain ⟨mid,hRound,hAbove⟩ := stepAboveTables hLay hPost
  have hEffects := roundEffects_of_post hFit hRound
  have hLow := (oneRoundMemory_of_post hFit hRows hRound).preparedEnd
  have hHeap : heap ≤ B.prepared A :=
    B.jobs.prepPrefix_mono B.core B.q A.heap (Nat.zero_le _)
  have hR := hLay.tableBelow
  have hG := hLay.graphsBelow
  have hO := hLay.offsetsBelow
  have hK : B.indices.length ≤ B.jobs.count := by
    simpa [BuildRoundData.indices,batchJobIndices,cutReplyIndices] using
      List.length_filter_le (fun i => decide (coreTag (B.jobs.answer B.core B.q i) = 0))
        (List.range B.jobs.count)
  have hGeo : A.replies < v := by
    change A.replies + B.jobs.count + 1 ≤ heap at hR
    omega
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
  have hOldPrefix (a : ℕ) (ha : a < D.directory) : out a = mem a := by
    have hSafe : B.unchangedBelow a := by
      by_cases he : B.indices.isEmpty = true
      · exact Or.inl he
      · refine Or.inr ?_
        intro Ms emb hm i hi
        have hIdx := (mem_batchJobIndices.mp (rowIndex_mem (emb := emb) hi
          (hRows Ms emb (Bool.eq_false_iff.mpr he) hm))).1
        have hs := (hL.slots _ (D.active_mem hIdx).1).1
        change A.offsets + D.count ≤ D.childAddr (D.active sts ((B.applyData Ms emb).child i)) at hs
        left
        change a < D.childAddr (D.active sts ((B.applyData Ms emb).child i))
        omega
    have hf := gameStep_prefix_frame hFit hLay hRows hPost
      (Or.inl ⟨show a < A.replies by omega,hSafe⟩)
      (Or.inl (by omega)) (Or.inl (by omega))
      (fun i hi _ => by have := hLay.savedBelow i hi; omega)
    exact (Function.update_of_ne (Nat.ne_of_lt (by omega)) ..).trans hf
  have hPostCopy := hPost
  obtain ⟨_,_,_,adv,_,hAdv,hAF,hZero⟩ := hPostCopy
  obtain ⟨_,_,_,he,_,hGraphs,hOffsets,_,_,_⟩ := hAdv
  have hGraphOut : ListAt out A.graphs
      (activeCompactWords (tabList B.jobs.count B.jobs.addr) B.indices) := by
    refine WordRAM.ListAt.congr hGraphs fun a ha hb => ?_
    have hh : a < A.graphs+B.indices.length := by simpa [activeCompactWords] using hb
    exact (hOutFrame a ha).trans (hAF a (by omega) (by omega))
  have hOffOut : ListAt out A.offsets
      (activeCompactWords (tabList B.jobs.count B.jobs.offset) B.indices) := by
    refine WordRAM.ListAt.congr hOffsets fun a ha hb => ?_
    have hh : a < A.offsets+B.indices.length := by simpa [activeCompactWords] using hb
    exact (hOutFrame a (by omega)).trans (hAF a (by omega) (by omega))
  refine ⟨WordRAM.ListAt.congr hM.host (fun a _ ha => hOldPrefix a (ha.trans_le hL.host)),
    WordRAM.ListAt.congr hM.verts (fun a _ ha => hOldPrefix a (ha.trans_le hL.verts)),
    D.compact_words sts ans D.childAddr ▸ hGraphOut,D.compact_words sts ans D.offset ▸ hOffOut,
    ?_,?_,?_⟩
  · intro c hc
    let req := choiceRequesting D.base.childSize D.count D.offset sts (answerByChild D.count sts ans)
    have hSlot := hL.slots c hc
    change A.offsets+D.count ≤ D.childAddr c ∧ D.childAddr c+D.geometry.slotWords ≤ A.replies at hSlot
    by_cases hReq : c ∈ req
    · have hne : B.indices.isEmpty = false := by
        apply Bool.eq_false_iff.mpr
        intro hEmpty
        have heq : B.indices.map (D.active sts) = req := D.selected_eq sts ans
        rw [List.isEmpty_iff.mp hEmpty,List.map_nil] at heq
        exact List.not_mem_nil (heq ▸ hReq)
      obtain ⟨Ms,emb,hRes,hWrite⟩ := hEffects.2.2 hne
      obtain ⟨i,hi,hc'⟩ := rowOfChild (emb := emb) (hRows Ms emb hne hRes) hReq
      let Q := B.applyData Ms emb
      have hGraph : GraphAt mid (Q.addr i) (appendGameMatching (Q.graph i) (Q.offset i) (Ms.getD i [])) :=
        (hWrite i hi).1
      have hMRow := (D.matchedRows hCert h.router h.host h.positive h.expansion h.denominator
        h.children h.even hne hRes).2 i hi
      let wk := fun j => erase B.host.edges ((matchingWalkRow Ms emb i).u j) ((matchingWalkRow Ms emb i).raw j)
      have he : appendGameMatching (Q.graph i) (Q.offset i) (Ms.getD i []) =
          gameGraph D.base.childSize (D.next sts ans (D.active sts (Q.child i))) :=
        D.graph_of_row (emb := emb) wk hMRow.2.2
      rw [he] at hGraph
      have hr : Q.addr i = D.childAddr c := congrArg D.childAddr hc'
      rw [hr] at hGraph
      change D.active sts (Q.child i) = c at hc'
      rw [hc'] at hGraph
      have hCap := h.matchedCap hTrace ht hCert hne hRes hi
      have hCount : Q.cap i = D.childAddr c + (gameGraph D.base.childSize (D.next sts ans c)).encode.length := by
        have hh : Q.cap i = Q.addr i + (appendGameMatching (Q.graph i) (Q.offset i) (Ms.getD i [])).encode.length :=
          applyBatch_cap_eq i
        rw [hh,hr,he,hc']
      change Q.cap i ≤ Q.addr i + D.geometry.slotWords at hCap
      rw [hCount,hr] at hCap
      refine WordRAM.ListAt.congr hGraph fun a ha hb => ?_
      have hJobCount : B.jobs.count ≤ D.count := D.active_le sts
      have hStart : A.offsets+D.count ≤ a := hSlot.1.trans ha
      exact (hOutFrame a (by omega)).trans (hAbove a (by omega) (hb.trans_le hCap |>.trans_le hSlot.2 |>.trans hGeo))
    · rw [D.graph_eq_of_no_request sts ans hc hReq]
      refine WordRAM.ListAt.congr (hM.children c hc) fun a ha hb => ?_
      obtain ⟨hInv,_⟩ := hTrace.certified.invariant h.router h.host h.positive h.expansion
        h.denominator h.children h.even (coreLevel_le h.coreSize)
      have hEnc := (gameGraph_bounds_of_inv (hInv c hc)).2.2.1
      have hLen : (gameGraph D.base.childSize (sts c)).encode.length ≤ D.geometry.slotWords :=
        hEnc.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by
          change t ≤ D.limit+1; omega)) _)
      have hSafe : B.unchangedBelow a := by
        by_cases he : B.indices.isEmpty = true
        · exact Or.inl he
        · refine Or.inr ?_
          intro Ms emb hm i hi
          let Q := B.applyData Ms emb
          have he' : B.indices.isEmpty = false := Bool.eq_false_iff.mpr he
          have hRow := rowIndex_mem (emb := emb) hi (hRows Ms emb he' hm)
          have hA : D.active sts (Q.child i) ∈ req := by
            have hSelected : B.indices.map (D.active sts) = req := D.selected_eq sts ans
            rw [← hSelected]
            exact List.mem_map_of_mem hRow
          have hC := (mem_choiceRequesting.mp hA).1
          have hNot : c ≠ D.active sts (Q.child i) := fun heq => hReq (heq ▸ hA)
          obtain hSep | hSep := hL.slotsApart c hc _ hC hNot
          · exact Or.inl ((hb.trans_le (Nat.add_le_add_left hLen _)).trans_le hSep)
          · exact Or.inr ((h.matchedCap hTrace ht hCert he' hm hi).trans (hSep.trans ha))
      have hJobCount : B.jobs.count ≤ D.count := D.active_le sts
      have hStart : A.offsets+D.count ≤ a := hSlot.1.trans ha
      have hBelow := hb.trans_le ((Nat.add_le_add_left hLen _).trans hSlot.2)
      exact (hOutFrame a (by omega)).trans
        (gameStep_prefix_frame hFit hLay hRows hPost (Or.inl ⟨hBelow,hSafe⟩)
          (Or.inr (by omega)) (Or.inr (by omega))
          (fun i hi _ => Nat.ne_of_gt ((hLay.savedBelow i hi).trans_le (by omega))))
  · intro a ha
    change v+2+B.jobs.count ≤ a at ha
    exact (hOutFrame a (by omega)).trans (hZero a ha)
  · change D.addrs.heap ≤ v+2+B.jobs.count
    have hh := hM.heap
    omega

end MinCostFlow.HierPaths
