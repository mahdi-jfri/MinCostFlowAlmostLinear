module

public import MinCostFlow.HierPaths.BuildProgChoiceProcs
public import MinCostFlow.HierPaths.BuildProgChoiceHistory
public import MinCostFlow.HierPaths.BuildChildAux

/-!
# The rows of a certified matching batch

Reindexing the job list identifies each router row with its original
child. The canonical model walk for that row is the stored shortcut.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Each active index names an original child with no saved set. -/
theorem ChoiceLoopData.active_mem {D : ChoiceLoopData} {sts : ℕ → ChildState}
    {i : ℕ} (hi : i < (D.round sts).jobs.count) :
    D.active sts i < D.count ∧ (sts (D.active sts i)).saved = none := by
  let l := activeChildren D.count sts
  have hl : i < l.length := hi
  have hm : D.active sts i ∈ l := by
    change l.getD i 0 ∈ l
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem _
  simpa [l,activeChildren] using hm

/-- Reindexing the selected active indices yields exactly the requesters. -/
theorem ChoiceLoopData.selected_eq (D : ChoiceLoopData) (sts : ℕ → ChildState)
    (answer : ℕ → CoreResult) :
    ((D.round sts).withReplies answer).indices.map (D.active sts) =
      choiceRequesting D.base.childSize D.count D.offset sts (answerByChild D.count sts answer) :=
  choiceGameJobs_indices D.base.childSize D.count D.offset D.childAddr sts answer _
    (coreLevel D.base.M D.base.r D.base.childSize)

/-- The encoded request pairs use the choices of the current scan. -/
theorem ChoiceLoopData.pairs_eq (D : ChoiceLoopData) (sts : ℕ → ChildState)
    (answer : ℕ → CoreResult) :
    ((D.round sts).withReplies answer).pairs =
      choiceRoundPairs D.base.childSize D.count D.offset sts (answerByChild D.count sts answer) :=
  choiceGameJobs_pairs D.base.childSize D.count D.offset D.childAddr sts answer _
    (coreLevel D.base.M D.base.r D.base.childSize)

/-- The matchings and walks of an executed nonempty round, indexed by original
child number. -/
theorem ChoiceLoopData.matchedRows {D : ChoiceLoopData} {sts : ℕ → ChildState}
    {answer : ℕ → CoreResult}
    (hCert : ∀ i < (D.round sts).jobs.count, CoreOutcomeSpec ParamConfig.default D.base.M
      (D.round sts).q ((D.round sts).jobs.graph i) (answer i))
    (hRouter : IsMatchingPlayer D.base.route D.base.routeCost)
    (hHost : HostPre D.base.host D.base.verts D.base.Δ D.base.L) {β : ℝ}
    (hβ : 0 < β) (hExp : D.base.host.IsExpansionExpanderOn D.base.verts β) {bh : ℕ}
    (hBh : max 2 (2/β) ≤ (bh:ℝ))
    (hChildren : IsChildren D.base.verts (fun c => shiftSet (D.offset c) (Finset.range D.base.childSize))
      D.count D.base.childSize)
    (hEven : D.base.childSize%2=0) {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hne : ((D.round sts).withReplies answer).indices.isEmpty = false)
    (hRes : ((D.round sts).withReplies answer).result.1 = .matched Ms emb) :
    let B := (D.round sts).withReplies answer
    let A := B.applyData Ms emb
    Ms.length = B.indices.length ∧ ∀ i (hi : i < Ms.length),
      let c := D.active sts (A.child i)
      c < D.count ∧
      (∀ e ∈ Ms[i], e.1 ∈ shiftSet (D.offset c) (Finset.range B.childSize) ∧
        e.2 ∈ shiftSet (D.offset c) (Finset.range B.childSize)) ∧
      (D.next sts answer c).rounds = (sts c).rounds ++
        [(List.range (Ms.getD i []).length).map fun j =>
          let row := matchingWalkRow Ms emb i
          ((row.u j - D.offset c,row.v j - D.offset c),erase B.host.edges (row.u j) (row.raw j))] := by
  let B := (D.round sts).withReplies answer
  let A := B.applyData Ms emb
  let s := D.base.childSize
  let ans := answerByChild D.count sts answer
  let cs := choiceRequesting s D.count D.offset sts ans
  let req := fun c => (choiceRequest s (D.offset c) (sts c) (ans c)).getD (∅,∅)
  have hS : B.indices.map (D.active sts) = cs := D.selected_eq sts answer
  have hCL : cs.length = B.indices.length := by rw [← hS,List.length_map]
  have hNon : cs ≠ [] := by
    intro he
    have hh := List.isEmpty_iff.mpr (List.length_eq_zero_iff.mp (hCL.symm.trans (congrArg List.length he)))
    exact (Bool.eq_false_iff.mp hne) hh
  obtain ⟨ms,em,he,hr,hBlock,_,_,_,_⟩ :=
    choiceRound_call hRouter hHost hβ hExp hBh hChildren hEven (D.certify_children hCert) hNon
  change (lemma1Route D.base.route D.base.host D.base.verts
    (choiceRoundPairs s D.count D.offset sts ans) D.base.Δ D.base.L).1 = _ at he
  have hEq : B.pairs = choiceRoundPairs s D.count D.offset sts ans := D.pairs_eq sts answer
  rw [← hEq] at he
  change B.result.1 = _ at he
  rw [hRes] at he
  cases he
  change Ms.length = B.indices.length ∧ _
  have hRows := hr.trans hCL
  refine ⟨hRows,?_⟩
  have hC (i : ℕ) (hi : i < Ms.length) : cs[i]'(hr ▸ hi) = D.active sts (A.child i) := by
    have h' : i < B.indices.length := hRows ▸ hi
    have h'' : i < (B.indices.map (D.active sts)).length := by simpa using h'
    have he' : cs[i]'(hr ▸ hi) = (B.indices.map (D.active sts))[i] := by
      exact List.getElem_of_eq hS.symm (hr ▸ hi)
    rw [he',List.getElem_map]
    exact congrArg (D.active sts) (List.getD_eq_getElem _ _ h').symm
  have hReq (i : ℕ) (hi : i < Ms.length) : D.active sts (A.child i) ∈ cs :=
    hC i hi ▸ List.getElem_mem (hr ▸ hi)
  have hEnds (i : ℕ) (hi : i < Ms.length) : ∀ e ∈ Ms[i],
      e.1 ∈ shiftSet (D.offset (D.active sts (A.child i))) (Finset.range s) ∧
      e.2 ∈ shiftSet (D.offset (D.active sts (A.child i))) (Finset.range s) := by
    let c := D.active sts (A.child i)
    intro e he
    have hB := (hBlock i (hr ▸ hi)).1 e (by rwa [List.getD_eq_getElem _ _ hi])
    change e.1 ∈ (req (cs[i]'(hr ▸ hi))).1 ∧ e.2 ∈ (req (cs[i]'(hr ▸ hi))).2 at hB
    rw [hC i hi] at hB
    obtain ⟨hc,ha,U,hU⟩ := mem_choiceRequesting.mp (hReq i hi)
    have hCertHere := D.certify_children hCert _ hc ha
    change CoreOutcomeSpec ParamConfig.default D.base.M _ (gameGraph s (sts c)) (ans c) at hCertHere
    change ans c = .cut U at hU
    rw [hU] at hCertHere
    have hU' : U ⊆ Finset.range s := hCertHere.1
    change e.1 ∈ (req c).1 ∧ e.2 ∈ (req c).2 at hB
    change (sts c).saved = none at ha
    simp only [req,choiceRequest,ha,hU,Option.getD_some] at hB
    exact ⟨shiftSet_subset (bisectOf_spec hU').1 hB.1,shiftSet_subset Finset.sdiff_subset hB.2⟩
  intro i hi
  let c := D.active sts (A.child i)
  obtain ⟨hc,ha,U,hU⟩ := mem_choiceRequesting.mp (hReq i hi)
  refine ⟨hc,hEnds i hi,?_⟩
  have hStart : ∀ j (hj : j < Ms.length), ∀ e ∈ Ms[j],
      e.1 ∈ shiftSet (D.offset c) (Finset.range s) ↔ j=i := by
    intro j hj e he
    have hJ := (hEnds j hj e he).1
    refine ⟨?_,?_⟩
    swap
    · rintro rfl
      exact hJ
    intro hE
    by_contra hne'
    have hCH : D.active sts (A.child j) ≠ c := by
      intro heq
      have hN : cs.Nodup := List.nodup_range.filter _
      exact hne' ((hN.getElem_inj_iff).mp ((hC j hj).trans (heq.trans (hC i hi).symm)))
    exact Finset.disjoint_left.mp (hChildren.2.2 _ (mem_choiceRequesting.mp (hReq j hj)).1
      _ hc hCH) hJ hE
  have hEntry := takeEntries_eq_matchingRow (G := B.host) (emb := emb) hi hStart
  have hNot : cs.isEmpty = false := Bool.eq_false_iff.mpr (fun h => hNon (List.isEmpty_iff.mp h))
  have hR : (lemma1Route D.base.route D.base.host D.base.verts
      (choiceRoundPairs s D.count D.offset sts ans) D.base.Δ D.base.L).1 = .matched Ms emb := by
    rw [← hEq]
    exact hRes
  change (if c < D.count then childStepAnswer (sts c) (ans c)
      (takeEntries s (D.offset c) (if cs.isEmpty then [] else callEntries B.host.edges
        (lemma1Route D.base.route D.base.host D.base.verts
           (choiceRoundPairs s D.count D.offset sts ans) D.base.Δ D.base.L).1)) else sts c).rounds = _
  rw [ite_eq_left hc]
  change (sts c).saved = none at ha
  change ans c = .cut U at hU
  simp only [childStepAnswer,ha,hU,hNot,Bool.false_eq_true,ite_false,hR,hEntry]
  rfl

/-- A row's first two entries are its local graph endpoints, in input order. -/
theorem matchingWalkRow_map_ends {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (o i : ℕ) (wk : ℕ → List ℕ) :
    ((List.range (Ms.getD i []).length).map fun j =>
      let R := matchingWalkRow Ms emb i
      ((R.u j-o,R.v j-o),wk j)).map Prod.fst =
      (Ms.getD i []).map fun e => (e.1-o,e.2-o) := by
  rw [List.map_map]
  apply List.ext_getElem
  · simp
  · intro j _ hj
    have hj' : j < (Ms.getD i []).length := by simpa using hj
    simp only [List.getElem_map,List.getElem_range,Function.comp_apply,matchingWalkRow,edgeAt]
    rw [List.getD_eq_getElem _ _ hj']

/-- Appending a matching row to a child's graph writes the graph of its next
model state. -/
theorem ChoiceLoopData.graph_of_row {D : ChoiceLoopData} {sts : ℕ → ChildState}
    {answer : ℕ → CoreResult} {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    {i : ℕ} (wk : ℕ → List ℕ)
    (hr : let B := (D.round sts).withReplies answer
      let c := D.active sts ((B.applyData Ms emb).child i)
      (D.next sts answer c).rounds = (sts c).rounds ++
        [(List.range (Ms.getD i []).length).map fun j =>
          let R := matchingWalkRow Ms emb i
          ((R.u j-D.offset c,R.v j-D.offset c),wk j)]) :
    let B := (D.round sts).withReplies answer
    let A := B.applyData Ms emb
    let c := D.active sts (A.child i)
    appendGameMatching (A.graph i) (A.offset i) (Ms.getD i []) =
      gameGraph D.base.childSize (D.next sts answer c) := by
  let B := (D.round sts).withReplies answer
  let A := B.applyData Ms emb
  let c := D.active sts (A.child i)
  let s := D.base.childSize
  have hEdges (st : ChildState) : (gameGraph s st).edges = st.rounds.flatten.map Prod.fst :=
    witnessEdges_eq_flatten st.rounds
  change (⟨s,(gameGraph s (sts c)).edges ++
    (Ms.getD i []).map (fun e => (e.1-D.offset c,e.2-D.offset c))⟩ : Graph) =
      gameGraph s (D.next sts answer c)
  rw [hEdges]
  congr 1
  change _ = (gameGraph s (D.next sts answer c)).edges
  rw [hEdges]
  change (D.next sts answer c).rounds = _ at hr
  rw [hr]
  simp only [List.flatten_append,List.flatten_singleton,List.map_append,
    matchingWalkRow_map_ends (emb := emb)]
  rfl

/-- A child with no request in this round keeps its graph, even if the round
has just saved its certificate. -/
theorem ChoiceLoopData.graph_eq_of_no_request (D : ChoiceLoopData) (sts : ℕ → ChildState)
    (answer : ℕ → CoreResult) {c : ℕ} (hc : c < D.count)
    (hr : c ∉ choiceRequesting D.base.childSize D.count D.offset sts
      (answerByChild D.count sts answer)) :
    gameGraph D.base.childSize (D.next sts answer c) = gameGraph D.base.childSize (sts c) := by
  unfold ChoiceLoopData.next choiceGameRound
  simp only [hc,ite_true]
  cases hS : (sts c).saved with
  | some _ => simp [childStepAnswer,hS]
  | none =>
    cases hA : answerByChild D.count sts answer c with
    | expander C =>
      simp only [childStepAnswer,hS]
      rfl
    | cut U =>
      exact False.elim (hr (mem_choiceRequesting.mpr ⟨hc,hS,U,hA⟩))

/-- Compaction of either table keeps the original child index for the next
model state. -/
theorem ChoiceLoopData.compact_words (D : ChoiceLoopData) (sts : ℕ → ChildState)
    (ans : ℕ → CoreResult) (f : ℕ → ℕ) :
    activeCompactWords (tabList (D.round sts).jobs.count (fun i => f (D.active sts i)))
        ((D.round sts).withReplies ans).indices =
      tabList (D.round (D.next sts ans)).jobs.count (fun i => f (D.active (D.next sts ans) i)) := by
  let l := activeChildren D.count sts
  let l' := activeChildren D.count (D.next sts ans)
  let idx := ((D.round sts).withReplies ans).indices
  have hh (xs : List ℕ) : tabList xs.length (fun i => f (xs.getD i 0)) = xs.map f := by
    apply List.ext_getElem
    · simp
    · intro i _ hi
      have hw : i < xs.length := by simpa using hi
      simp [tabList,List.getElem?_eq_getElem hw]
  change activeCompactWords (tabList l.length (fun i => f (l.getD i 0))) idx =
    tabList l'.length (fun i => f (l'.getD i 0))
  rw [hh,hh]
  have hIdx : idx.map (D.active sts) = l' := by
    rw [D.selected_eq]
    exact (activeChildren_choiceRound D.base.route D.base.host D.base.verts
      D.base.Δ D.base.L D.base.childSize D.count D.offset sts (answerByChild D.count sts ans)).symm
  rw [← hIdx,List.map_map]
  unfold activeCompactWords
  apply List.map_congr_left
  intro i hi
  have hil : i < l.length := (mem_batchJobIndices.mp hi).1
  rw [List.getD_eq_getElem _ _ (by simpa using hil),List.getElem_map,Function.comp_apply]
  change f l[i] = f (l.getD i 0)
  rw [List.getD_eq_getElem _ _ hil]

end MinCostFlow.HierPaths
