module

public import MinCostFlow.HierPaths.BuildProgInjectInput
public import MinCostFlow.HierPaths.BuildProgFinishFits

/-!
# Matching rows of the final injection

The matchings come back in original child order. Each row has at most
half a child's worth of edges and remains in the reserved graph slot.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- The injection treats every original child as one job. -/
def ChoiceLoopData.injectionData (D : ChoiceLoopData) (sts : ℕ → ChildState)
    (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ) : ApplyBatchData :=
  ⟨⟨D.count,fun c => gameGraph D.base.childSize (sts c),D.childAddr,D.offset,none,none⟩,List.range D.count,
    Ms,emb,D.base.host⟩

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Application row i is for original child i. -/
theorem ChoiceLoopData.injection_child (D : ChoiceLoopData) (sts : ℕ → ChildState)
    (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ) {i : ℕ} (hi : i < D.count) :
    (D.injectionData sts Ms emb).child i = i := by
  change (List.range D.count).getD i 0 = i
  have hh : i < (List.range D.count).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ hh,List.getElem_range]

/-- The injection row lies in the child and uses at most half its vertices as sources. -/
theorem ChoiceLoopTrace.injectRow {w b : ℕ} {D : ChoiceLoopData} {β : ℝ} {bh : ℕ}
    {initial mem : ℕ → ℕ} {heap : ℕ} {sts : ℕ → ChildState}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hTrace : ChoiceLoopTrace w D initial D.limit heap sts mem) (h : ChoiceGameHyp D β bh)
    (hMatch : RouteMatchedSpec D.base.host D.base.verts (injPairs D.base.childSize D.count D.offset sts)
      D.base.Δ D.base.L b 0 Ms emb)
    (hFull : ∀ i (hi : i < (injPairs D.base.childSize D.count D.offset sts).length),
      (Ms.getD i []).length = ((injPairs D.base.childSize D.count D.offset sts)[i]'hi).1.card)
    {i : ℕ} (hi : i < Ms.length) :
    let A := D.injectionData sts Ms emb
    i < D.count ∧ A.cap i ≤ D.childAddr i + D.geometry.slotWords ∧
      ∀ e ∈ Ms.getD i [],
        e.1 ∈ shiftSet (D.offset i) (Finset.range D.base.childSize) ∧
        e.2 ∈ shiftSet (D.offset i) (Finset.range D.base.childSize) := by
  let A := D.injectionData sts Ms emb
  let pairs := injPairs D.base.childSize D.count D.offset sts
  have hLen : Ms.length = pairs.length := hMatch.1
  have hCount : pairs.length = D.count := by simp [pairs,injPairs]
  have hChild : i < D.count := by omega
  have hiP : i < pairs.length := by omega
  have hName := D.injection_child sts Ms emb hChild
  have hGraph : A.graph i = gameGraph D.base.childSize (sts i) := by
    change A.jobs.graph (A.child i) = _
    rw [hName]
    rfl
  have hAddr : A.addr i = D.childAddr i := by
    change D.childAddr (A.child i) = _
    rw [hName]
  obtain ⟨hInv,_⟩ := hTrace.certified.invariant h.router h.host h.positive h.expansion
    h.denominator h.children h.even (coreLevel_le h.coreSize)
  obtain ⟨S,hS⟩ := CertifiedGame.all_saved h.children.1 h.sizeLog hInv i hChild
  obtain ⟨hSub,hHalf,_⟩ := (hInv i hChild).2.2.2.1 S hS
  have hPair : pairs[i]'hiP =
      (shiftSet (D.offset i) (Finset.range D.base.childSize \ S),shiftSet (D.offset i) S) := by
    rw [← List.getD_eq_getElem _ _ hiP]
    exact injPairs_getD hChild hS
  refine ⟨hChild,?_,?_⟩
  · have hGame := (gameGraph_bounds_of_inv (hInv i hChild)).2.2.1
    rw [buildGraph_encode_length] at hGame
    have hSource := hFull i hiP
    change (Ms.getD i []).length = (pairs[i]'hiP).1.card at hSource
    rw [hPair,card_shiftSet,Finset.card_sdiff_of_subset hSub,Finset.card_range] at hSource
    have hSC : S.card ≤ D.base.childSize := by simpa using Finset.card_le_card hSub
    have hSourceHalf : 2*(Ms.getD i []).length ≤ D.base.childSize := by omega
    have hR : (A.row i).count = (Ms.getD i []).length := rfl
    have hCap : A.cap i = A.addr i + 2 + 2*((A.graph i).m+(A.row i).count) := rfl
    have hSpan : D.geometry.slotWords = 2+(D.limit+1)*D.base.childSize := rfl
    change A.cap i ≤ D.childAddr i + D.geometry.slotWords
    rw [hCap,hAddr,hGraph,hR,hSpan]
    have hMul : (D.limit+1)*D.base.childSize = D.limit*D.base.childSize+D.base.childSize :=
      Nat.succ_mul ..
    omega
  · intro e he
    have hEnds := (hMatch.2.1 i hiP).1 e he
    change e.1 ∈ (pairs[i]'hiP).1 ∧ e.2 ∈ (pairs[i]'hiP).2 at hEnds
    rw [hPair] at hEnds
    exact ⟨shiftSet_subset Finset.sdiff_subset hEnds.1,shiftSet_subset hSub hEnds.2⟩

/-- The dense child tables, slot bounds, and matched reply suffice to run
the shared application scan for the final injection. -/
theorem ChoiceLoopTrace.injectFinishPre {w b heap rep top : ℕ} {D : ChoiceLoopData} {β : ℝ} {bh : ℕ}
    {initial last mem : ℕ → ℕ} {sts : ℕ → ChildState}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hTrace : ChoiceLoopTrace w D initial D.limit heap sts last) (h : ChoiceGameHyp D β bh)
    (hL : GameFixedLayout w D.geometry) (hb : b ≤ bh)
    (hMatch : RouteMatchedSpec D.base.host D.base.verts (injPairs D.base.childSize D.count D.offset sts)
      D.base.Δ D.base.L b 0 Ms emb)
    (hFull : ∀ i (hi : i < (injPairs D.base.childSize D.count D.offset sts).length),
      (Ms.getD i []).length = ((injPairs D.base.childSize D.count D.offset sts)[i]'hi).1.card)
    (hReply : ListAt mem rep (routeResultWords (.matched Ms emb)))
    (hTop : rep + (routeResultWords (.matched Ms emb)).length ≤ top) (hZero : ZeroFrom mem top)
    (hIdx : ListAt mem D.addrs.replies (List.range D.count))
    (hGraphs : ListAt mem D.addrs.graphs (tabList D.count D.childAddr))
    (hOffs : ListAt mem D.addrs.offsets (tabList D.count D.offset))
    (hRep : D.addrs.replies+D.count ≤ rep)
    (hEnds : ListAt mem (D.addrs.host+2) (D.base.host.edges.flatMap fun e => [e.1,e.2]))
    (hChildren : ∀ c < D.count, GraphAt mem (D.childAddr c) (gameGraph D.base.childSize (sts c)))
    (hWord : (D.injectionData sts Ms emb).cursor
      (top+4+Ms.flatten.length+D.base.pathBound+1+D.base.host.n) Ms.length < 2^w) :
    let A := D.injectionData sts Ms emb
    (buildFinishBatchContract w A).pre
      [rep,D.addrs.replies,D.addrs.graphs,D.addrs.offsets,D.addrs.host+2,
        D.base.host.n,D.base.pathBound,top,Ms.length] mem := by
  let A := D.injectionData sts Ms emb
  let pairs := injPairs D.base.childSize D.count D.offset sts
  have hLen : Ms.length = D.count := by simpa [injPairs] using hMatch.1
  have hr := hTrace.injectRouterPre h
  have hRow (i : ℕ) (hi : i < Ms.length) :=
    hTrace.injectRow h hMatch hFull hi
  have hC (i : ℕ) (hi : i < Ms.length) : A.child i = i :=
    D.injection_child sts Ms emb (hRow i hi).1
  have hA (i : ℕ) (hi : i < Ms.length) : A.addr i = D.childAddr i := by
    change D.childAddr (A.child i) = _
    rw [hC i hi]
  have hO (i : ℕ) (hi : i < Ms.length) : A.offset i = D.offset i := by
    change D.offset (A.child i) = _
    rw [hC i hi]
  have hLay (i : ℕ) (hi : i < Ms.length) :
      D.addrs.offsets+D.count ≤ A.addr i ∧ A.cap i ≤ D.addrs.replies := by
    obtain ⟨hc,hCap,_⟩ := hRow i hi
    have hSlot := hL.slots i hc
    exact ⟨(hA i hi).symm ▸ hSlot.1,hCap.trans hSlot.2⟩
  have hGraphOff : D.addrs.graphs+D.count ≤ D.addrs.offsets := hL.graphs
  have hTables : ApplyBatchTables A mem D.addrs.replies D.addrs.graphs D.addrs.offsets := by
    refine ⟨hIdx,hGraphs,hOffs,?_,?_,fun i hi => Or.inr (hLay i hi).2,?_⟩
    · change (List.range D.count).length = Ms.length
      simp [hLen]
    · intro i hi
      rw [hC i hi]
      exact (hRow i hi).1
    · intro i hi
      exact ⟨(hGraphOff.trans (Nat.le_add_right ..)).trans (hLay i hi).1,(hLay i hi).1⟩
  have hHostEnd := hL.host
  rw [buildGraph_encode_length] at hHostEnd
  have hDir : D.directory+D.limit ≤ D.saved := hL.directory
  have hSaved : D.saved+D.count ≤ D.addrs.graphs := hL.saved
  have hRegions : FinishChildRegions w A (D.addrs.host+2) rep := by
    refine ⟨?_,fun i hi => (hLay i hi).2.trans (Nat.le_add_right .. |>.trans hRep),?_,?_⟩
    · intro i hi
      have hh := (hLay i hi).1
      change D.addrs.host+(2+2*D.base.host.m) ≤ D.directory at hHostEnd
      change D.addrs.host+2+2*D.base.host.m ≤ A.addr i
      omega
    · intro i hi j hj hij
      obtain hh | hh := hL.slotsApart i (hRow i hi).1 j (hRow j hj).1 hij
      · exact Or.inl ((hRow i hi).2.1.trans (hh.trans_eq (hA j hj).symm))
      · exact Or.inr ((hRow j hj).2.1.trans (hh.trans_eq (hA i hi).symm))
    · intro i hi
      rw [hO i hi]
      exact (Nat.le_add_right ..).trans_lt (hL.offsetWords i (hRow i hi).1)
  have hLength : routePathLen D.base.Δ b D.base.L ≤ D.base.pathBound := by
    apply Nat.le_trans _ h.path
    unfold routePathLen
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb)
  refine buildFinishBatch_pre_of_matched (D := A) hReply hTop hZero h.valid hMatch hr.1
    hr.2.2.2.2.2.2 hLength hTables ?_ hRegions hEnds ?_ ?_ hWord
  · simpa [A,ChoiceLoopData.injectionData] using hRep
  · intro i hi
    change GraphAt mem (A.addr i) (gameGraph D.base.childSize (sts (A.child i)))
    rw [hA i hi,hC i hi]
    exact hChildren i (hRow i hi).1
  · intro i hi e he
    rw [hO i hi]
    obtain ⟨h1,h2⟩ := (hRow i hi).2.2 e he
    obtain ⟨ha,hha⟩ := mem_shiftSet_iff.mp h1
    obtain ⟨hb,hhb⟩ := mem_shiftSet_iff.mp h2
    have hw := hL.offsetWords i (hRow i hi).1
    change D.offset i + D.base.childSize < 2^w at hw
    exact ⟨ha,hb,by have := Finset.mem_range.mp hha; omega,by have := Finset.mem_range.mp hhb; omega⟩

end MinCostFlow.HierPaths
