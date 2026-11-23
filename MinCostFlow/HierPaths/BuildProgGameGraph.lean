module

public import MinCostFlow.HierPaths.BuildProgGameStepMemory
public import MinCostFlow.HierPaths.BuildChildAux

/-!
# A game row appends the next model matching

The selected index determines which child owns the row. The core answer
is a cut there. The model and the writer both append the edges from
that row and shift both endpoints to the child's local numbering.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The requests in one scheduled round are exactly those of the model. -/
theorem BuildGameSchedule.pairs_eq (S : BuildGameSchedule) (t : ℕ) :
    (S.round t).pairs = roundPairs S.base.core S.base.M S.base.r S.base.childSize S.count
      S.offset (S.states t) :=
  modelGameJobs_pairs S.base.core S.base.M S.base.r S.base.childSize S.count
    S.offset S.childAddr (S.states t)

/-- A nonempty round gets a full matching with the router's bounds. -/
theorem BuildGamePlayerBounds.matched {S : BuildGameSchedule} {cfg : ParamConfig} {β : ℝ} {bh : ℕ}
    (h : BuildGamePlayerBounds S cfg β bh) {t : ℕ} (ht : t < S.data.limit)
    (hne : (S.round t).indices.isEmpty = false) :
    let B := S.round t
    ∃ Ms emb, B.result.1 = .matched Ms emb ∧
      RouteMatchedSpec B.host B.verts B.pairs B.Δ B.L B.result.2 0 Ms emb ∧
      (∀ i (hi : i < B.pairs.length), (Ms.getD i []).length = (B.pairs[i]'hi).1.card) ∧
      (B.result.2 : ℝ) ≤ (bh : ℝ) := by
  let B := S.round t
  have hl : B.pairs.length = B.indices.length := length_batchJobPairs ..
  have hp : 1 ≤ B.pairs.length := by
    rw [hl]
    exact List.length_pos_iff.mpr (fun he => (Bool.eq_false_iff.mp hne) (List.isEmpty_iff.mpr he))
  obtain ⟨_,hex⟩ := exists_lemma_1 h.router
  obtain ⟨⟨ms,em,he,hs,hFull⟩,_,hb,_,_⟩ := hex B.host B.verts B.pairs B.Δ B.L
    (h.routerPre ht) hp β h.positive h.expansion
  exact ⟨ms,em,he,hs,hFull,hb.trans h.bh⟩

/-- In a matched round, only the row for a child starts in that child. -/
theorem BuildGamePlayerBounds.row_starts {S : BuildGameSchedule} {cfg : ParamConfig} {β : ℝ} {bh : ℕ}
    (h : BuildGamePlayerBounds S cfg β bh) {t : ℕ} (ht : t < S.data.limit)
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ} {i : ℕ}
    (hRes : (S.round t).result.1 = .matched Ms emb) (hne : (S.round t).indices.isEmpty = false)
    (hi : i < Ms.length) :
    let B := S.round t
    let D := B.applyData Ms emb
    ∀ a (ha : a < Ms.length), ∀ e ∈ Ms[a],
      e.1 ∈ shiftSet (D.offset i) (Finset.range B.childSize) ↔ a = i := by
  let B := S.round t
  let D := B.applyData Ms emb
  change ∀ a (ha : a < Ms.length), ∀ e ∈ Ms[a],
    e.1 ∈ shiftSet (D.offset i) (Finset.range B.childSize) ↔ a = i
  intro a ha e he
  obtain ⟨xs,f,hMatch,hs,_,_⟩ := h.matched ht hne
  rw [hRes] at hMatch
  cases hMatch
  have hc : Ms.length = B.indices.length := hs.1.trans (length_batchJobPairs ..)
  have hIndex (j : ℕ) (hj : j < Ms.length) : D.child j ∈ B.indices := by
    change B.indices.getD j 0 ∈ B.indices
    have hj' : j < B.indices.length := hc ▸ hj
    rw [List.getD_eq_getElem _ _ hj']
    exact List.getElem_mem hj'
  have hActive (j : ℕ) (hj : j < Ms.length) : D.child j < B.jobs.count :=
    (mem_batchJobIndices.mp (hIndex j hj)).1
  let orig := fun j => S.child t (D.child j)
  have hOrig (j : ℕ) (hj : j < Ms.length) : orig j < S.count :=
    (S.child_active (hActive j hj)).1
  have ha' : a < B.pairs.length := hs.1 ▸ ha
  have hSide := ((hs.2.1 a ha').1 e (by rwa [List.getD_eq_getElem _ _ ha])).1
  have hRows : B.pairs[a] = batchJobPair B.jobs B.core B.q B.childSize (D.child a) := by
    have hb : a < B.indices.length := hc ▸ ha
    let f := batchJobPair B.jobs B.core B.q B.childSize
    have hw : a < (B.indices.map f).length := by simpa using hb
    exact (List.getElem_map f (h := hw)).trans (congrArg f (List.getD_eq_getElem _ _ hb).symm)
  change e.1 ∈ B.pairs[a].1 at hSide
  rw [hRows] at hSide
  obtain ⟨_,U,hCut⟩ := mem_batchJobIndices.mp (hIndex a ha)
  rw [batchJobPair,hCut] at hSide
  have hCutS := h.coreOutcome ht (hActive a ha)
  change CoreOutcomeSpec cfg B.M B.r (B.jobs.graph (D.child a))
    (B.jobs.answer B.core B.q (D.child a)) at hCutS
  rw [hCut] at hCutS
  have hU : U ⊆ Finset.range B.childSize := hCutS.1
  have hY := shiftSet_subset (bisectOf_spec hU).1 hSide
  change e.1 ∈ shiftSet (S.offset (orig a)) (Finset.range B.childSize) at hY
  change e.1 ∈ shiftSet (S.offset (orig i)) (Finset.range B.childSize) ↔ a = i
  refine ⟨?_,fun he => he ▸ hY⟩
  intro hYi
  by_contra hne'
  have hneq : orig a ≠ orig i := by
    intro heq
    have hChild := S.child_injective t (hActive a ha) (hActive i hi) heq
    have hnd : B.indices.Nodup := List.nodup_range.filter _
    have ha'' : a < B.indices.length := hc ▸ ha
    have hi'' : i < B.indices.length := hc ▸ hi
    change B.indices.getD a 0 = B.indices.getD i 0 at hChild
    rw [List.getD_eq_getElem _ _ ha'',List.getD_eq_getElem _ _ hi''] at hChild
    exact hne' ((hnd.getElem_inj_iff).mp hChild)
  exact Finset.disjoint_left.mp (h.children.2.2 _ (hOrig a ha) _ (hOrig i hi) hneq) hY hYi

/-- The graph appended by the writer is the next graph of its model child. -/
theorem BuildGamePlayerBounds.graph_succ {S : BuildGameSchedule} {cfg : ParamConfig} {β : ℝ} {bh : ℕ}
    (h : BuildGamePlayerBounds S cfg β bh) {t : ℕ} (ht : t < S.data.limit)
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ} {i : ℕ}
    (hRes : (S.round t).result.1 = .matched Ms emb) (hne : (S.round t).indices.isEmpty = false)
    (hi : i < Ms.length) :
    let B := S.round t
    let D := B.applyData Ms emb
    appendGameMatching (D.graph i) (D.offset i) (Ms.getD i []) =
      gameGraph B.childSize (S.states (t+1) (S.child t (D.child i))) := by
  let B := S.round t
  let D := B.applyData Ms emb
  let c := S.child t (D.child i)
  let sts := S.states t
  let s := B.childSize
  let o := D.offset i
  have hcnt := h.rows ht (fun he => (Bool.eq_false_iff.mp hne) (List.isEmpty_iff.mpr he)) hRes
  have hi' : i < B.indices.length := hcnt ▸ hi
  have hAt : D.child i ∈ B.indices := by
    change B.indices.getD i 0 ∈ B.indices
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  obtain ⟨hChild,U,hCut⟩ := mem_batchJobIndices.mp hAt
  have hSaved : (sts c).saved = none := (S.child_active hChild).2
  have hAnswer : coreAnswer B.core B.M B.r s (sts c) = .cut U := hCut
  have hEntry := takeEntries_eq_matchingRow (G := B.host) (emb := emb) hi
    (h.row_starts ht hRes hne hi)
  have hMap : (takeEntries s o (callEntries B.host.edges (.matched Ms emb))).map Prod.fst =
      (Ms.getD i []).map (fun e => (e.1-o,e.2-o)) := by
    rw [hEntry, List.map_map]
    apply List.ext_getElem
    · simp
    · intro j _ hj
      have hj' : j < (Ms.getD i []).length := by simpa using hj
      simp only [List.getElem_map, List.getElem_range, Function.comp_apply,matchingWalkRow,edgeAt]
      rw [List.getD_eq_getElem _ _ hj']
  have hModel : S.states (t+1) c =
      ⟨(sts c).rounds ++ [takeEntries s o (callEntries B.host.edges (.matched Ms emb))], none⟩ := by
    change gameRound S.base.route S.base.host S.base.verts S.base.Δ S.base.L S.base.core S.base.M
      S.base.r s S.count S.offset sts c = _
    have hEq : (lemma1Route S.base.route S.base.host S.base.verts
        (roundPairs S.base.core S.base.M S.base.r s S.count S.offset sts) S.base.Δ S.base.L).1 =
          .matched Ms emb := by
      have hh : B.pairs = roundPairs S.base.core S.base.M S.base.r s S.count S.offset sts :=
        S.pairs_eq t
      rw [← hh]
      exact hRes
    unfold gameRound
    change coreAnswer S.base.core S.base.M S.base.r s (sts c) = .cut U at hAnswer
    simp only [hSaved,hAnswer,hEq]
    rfl
  change appendGameMatching (gameGraph s (sts c)) o (Ms.getD i []) = _
  rw [hModel]
  have hg (st : ChildState) : (gameGraph s st).edges = st.rounds.flatten.map Prod.fst :=
    witnessEdges_eq_flatten st.rounds
  change (⟨s,(gameGraph s (sts c)).edges ++ _⟩ : Graph) = _
  rw [hg]
  congr 1
  change _ = (gameGraph s (⟨(sts c).rounds ++ [_],none⟩ : ChildState)).edges
  rw [hg]
  simp only [List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,List.map_append,hMap]

end MinCostFlow.HierPaths
