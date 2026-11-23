module

public import MinCostFlow.LastLevelProgram.StagedNumericLayout
public import MinCostFlow.LastLevelProgram.StagedGuestWeights
import MinCostFlow.LastLevelProgram.ConnectedLSST
import MinCostFlow.LSF.Components
import WordRAM.Link
import MinCostFlow.Num.ModulePlacement
import Mathlib.Tactic

/-!
# The staged numeric rebuild

For Definition 5.8 (pages 19–20), select the compact tree and retain it
while computing the stretches and next weights.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM LSF WideWord

/-- On the connected compact graph, the selected tree has (n-1)
edges with compact indices and the same vertex set as the input. -/
theorem stagedController_selectedTreeBounds (H T : MGraph)
    (ℓ v : ℕ → ℝ) (γ : ℝ) (hv : (indexedGraph H).Valid)
    (hc : ∀ a ∈ (indexedGraph H).toMGraph.V, ∀ b ∈ (indexedGraph H).toMGraph.V,
      (indexedGraph H).toMGraph.Connected a b)
    (ht : LSF.IsLSST (indexedGraph H).toMGraph ℓ v γ T) :
    T.E.card+1 = H.n ∧ T.V.card = H.n ∧ (∀ i ∈ T.E, i < H.m) ∧ H.n ≤ H.m+1 := by
  have hsub := connectedLSST_edges_subset (WideWord.IndexedGraph.toMGraph_isValid hv) hc ht
  have hcount := LSF.spanningTree_edge_card ht.1 (WideWord.IndexedGraph.toMGraph_V_nonempty hv)
  have hcard : (indexedGraph H).toMGraph.V.card = H.n := Finset.card_range _
  have hEdge : T.E.card+1 = H.n := hcount.trans hcard
  have hVertex : T.V.card = H.n := (congrArg Finset.card ht.1.2.1).trans hcard
  have hIndex (i : ℕ) (hi : i ∈ T.E) : i < H.m := Finset.mem_range.mp (hsub hi)
  have hm := Finset.card_le_card hsub
  change T.E.card ≤ (Finset.range H.m).card at hm
  rw [Finset.card_range] at hm
  exact ⟨hEdge,hVertex,hIndex,by omega⟩

/-- Cost of the staged numeric pass, including argument setup,
incidence records, and packing the host vectors. -/
def stagedRebuildNumericCost (G : MGraph) (N levels : ℕ) : ℕ :=
  argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
    (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
  argsSize stagedNumericArgs+112*G.n+stagedNumericFactor N levels*(G.m+1)+14+
  (17*N+75)*G.m+(35*N+60)*G.m+56*N+137+
  argsSize (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 19) ++
    [.reg 19])

/-- Link the installed tree traversal, stretch arithmetic, and weight
update at the width supplied by the round layout. -/
theorem stagedNumericProcedures_meetContract
    {w h Q numeric stretch update tables stretches narrow widen copy copyLimbs traverse distance
      ancestors edgeQuery distanceStep ancestorRow add ancestorLookup stretchEdge path stretchLength
      sub neg fixedDiv extend weightStep mul integerDiv : ℕ} {p : Program}
    (G T : MGraph) (len : ℕ → ℤ)
    (adj parents edges depths queue levels dist lengths N heap tails heads P old denom j : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    {ℓ v : ℕ → ℝ} {γ : ℝ}
    (hv : (indexedGraph G).Valid) (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (hbits : 0 < h) (hbasic : 2*h+2 ≤ w) (hwordBits : 3*h+2 ≤ w)
    (hw : 6 < 2^w) (hmPos : 0 < G.m) (hcopy : p.HasAt copy [copyWords]) (hdist : dist ≤ heap) :
    p.procs[numeric]? = some (stretchWeightRoundBody stretch update) →
    p.procs[stretch]? = some (treeStretchRoundBody tables stretches) →
    p.procs[tables]? = some (buildTreeTablesBody traverse distance ancestors) →
    p.procs[traverse]? = some traverseTreeQueueBody →
    p.procs[distance]? = some (rootedDistanceBody distanceStep) →
    p.procs[distanceStep]? = some (rootDistanceStepBody add copy) →
    p.HasAt add (Num.addCarryModule add h) →
    p.procs[ancestors]? = some (rootedAncestorTableBody ancestorRow) →
    p.procs[ancestorRow]? = some ancestorRowBody →
    p.procs[stretches]? = some (rootedStretchRoundBody edgeQuery) →
    p.procs[edgeQuery]? = some (edgeStretchQueryBody ancestorLookup stretchEdge) →
    p.procs[ancestorLookup]? = some rootedTreeAncestorBody →
    p.procs[stretchEdge]? = some (edgeStretchBody path stretchLength) →
    p.procs[path]? = some (pathLengthBody sub add) →
    p.procs[stretchLength]? = some (stretchFromLengthBody add neg fixedDiv) →
    p.HasAt sub (Num.subtractModule sub h) →
    p.HasAt neg (Num.negateCarryModule neg h) →
    p.HasAt fixedDiv (Num.fixedDivideModule fixedDiv h) →
    p.procs[update]? = some (weightRoundBody narrow) →
    p.procs[narrow]? = some (narrowWeightBody widen copyLimbs) →
    p.procs[widen]? = some (widenWeightBody extend weightStep) →
    p.HasAt extend (Num.signExtendModule extend h) →
    p.procs[weightStep]? = some (weightUpdateBody mul integerDiv add) →
    p.HasAt mul (Num.fixedMultiplyModule mul h) →
    p.HasAt integerDiv (Num.integerDivideModule integerDiv h) →
    p.HasAt copyLimbs (Num.copyModule copyLimbs) →
    0 < scale → 2*(2 : ℝ)^P*(2*(G.m : ℝ)) < Num.capacity h N →
    (∀ e ∈ G.E, 1 ≤ weights P (scale : ℝ) query (j+1) e) →
    (∑ e ∈ G.E, weights P (scale : ℝ) query (j+1) e) ≤ 2*G.m →
    (∀ i < G.m, roundStretch P (treeStretch (indexedGraph G).toMGraph T
        (fun e => (len e : ℝ)/(2 : ℝ)^Q) i) =
      query (weights P (scale : ℝ) query j) (edgeName G i)) →
    heap+(G.n-1)*N+G.m*edgeStretchSpace N+G.m*narrowWeightSpace N < 2^w →
    MeetsContract w p numeric (stretchWeightRoundContract w h Q (indexedGraph G).toMGraph
      T G 0 len adj parents edges depths queue G.n levels dist lengths N heap tails heads P
      old N denom j scale query) := by
  intro hNumeric hStretch hTables hTraverse hDistance hDistanceStep hAdd hAncestors hAncestorRow
    hStretches hEdgeQuery hAncestorLookup hStretchEdge hPath hStretchLength hSub hNeg hFixedDiv
    hUpdate hNarrow hWiden hExtend hWeightStep hMul hIntegerDiv hCopyLimbs hscale hwidth
    hone hsum hstretches hroom
  have hmIndex : (indexedGraph G).toMGraph.m = G.m := Finset.card_range _
  have hroomStretch : heap+(G.n-1)*N+G.m*edgeStretchSpace N < 2^w :=
    (Nat.le_add_right _ _).trans_lt hroom
  have hfirst : heap+(G.n-1)*N+edgeStretchSpace N < 2^w := by
    have hm := Nat.le_mul_of_pos_left (edgeStretchSpace N) hmPos
    exact (Nat.add_le_add_left hm _).trans_lt hroomStretch
  have hroot := indexedLSST_rooted_zero hv htree
  have hTreeCall := treeStretchRound_meetsContract (G := (indexedGraph G).toMGraph) (Q := Q) len hStretch
    (buildTreeTables_meetsContract (m := (indexedGraph G).toMGraph.m) hroot len hTables
      (traverseTreeQueue_meetsContract hroot hTraverse)
      (rootedDistance_meetsContract hroot len hDistance
        (rootDistanceStep_meetsContract hDistanceStep (Num.addCarry_meetsContract hbits hbasic hAdd) (copyWords_meetsContract hcopy)))
      (rootedAncestorTable_meetsContract hroot hAncestors hAncestorRow))
    (rootedStretchRound_meetsContract hroot len hStretches
      (edgeStretchQuery_meetsContract hroot hEdgeQuery (rootedTreeAncestor_meetsContract hroot hAncestorLookup)
        (edgeStretch_meetsContract hStretchEdge (pathLength_meetsContract hbits hbasic hPath hSub hAdd)
          (stretchFromLength_meetsContract hbits hwordBits hStretchLength hAdd hNeg hFixedDiv))))
  have hWeightCall := weightRound_meetsContract hUpdate
    (narrowWeight_meetsContract ((by decide : 1 < 6).trans hw) ((by decide : 2 < 6).trans hw)
      hNarrow
      (widenWeight_meetsContract hbits hwordBits hWiden hExtend
        (weightUpdate_meetsContract hbits hwordBits hWeightStep hMul hIntegerDiv hAdd)) hCopyLimbs)
  exact stretchWeightRound_meetsContract _ hNumeric hTreeCall hWeightCall
      adj parents edges depths queue G.n levels dist lengths N heap tails heads P
      old N denom j scale query hmIndex ((by decide : 1 < 6).trans hw)
      hscale hdist
      (by simpa only [hmIndex] using hroom) hfirst hwidth
      hone hsum hstretches

/-- One staged rebuild round preserves the source blocks through
selection and produces the numeric update using the selected guest tree. -/
theorem stagedRebuildVerified_runs {w h Q adjacency numeric insert push cap copy pack packWeights prepare select dedup shift store stretch update tables stretches narrow widen copyLimbs traverse distance ancestors edgeQuery distanceStep ancestorRow add ancestorLookup stretchEdge path stretchLength sub neg fixedDiv extend weightStep mul integerDiv : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G T : MGraph) (L staging sim levels : ℕ)
    (guest : Program) (D : ℕ) (vs : List ℕ)
    (guestCost guestWeightSrc guestWeightStride guestHostL guestHostP guestQ : ℕ)
    (guestLen guestWeight : ℕ → ℤ)
    (hq : MeetsContract w p select
      (convertedTreeSelectorContract w guest D G T L sim staging guestCost guestWeightSrc
        guestWeightStride guestHostL guestHostP guestQ guestLen guestWeight))
    (hargs : evalArgs w st convertedGuestCallArgs = some vs) (hwords : ∀ x ∈ vs, x < 2^w)
    (hready : convertedSelectorReady w G L sim staging guestWeightSrc guestWeightStride
      guestHostP guestQ guestHostL guestLen guestWeight vs st.mem) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (he : p.procs[adjacency]? = some (selectedAdjacencyBody insert))
    (hi : p.procs[insert]? = some (pushTreeEdgeBody push))
    (hpush : p.procs[push]? = some pushTreeIncidenceBody)
    (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (ha : st.regs 5 = staging)
    (hsim : st.regs 3 = sim) (hL : st.regs 2 = L) (hl : st.regs 14 = levels)
    (N P j B src names weightSrc weightStride scale : ℕ) (len : ℕ → ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hN : st.regs 19 = N) (hP : st.regs 23 = P)
    (hNPos : 0 < N) (hmPos : 0 < G.m)
    (hlevels : G.n ≤ 2^(levels+1)) (hRows : levels+1 < 2^w)
    (hprec : P < 2^w)
    (hcopy : p.HasAt copy [copyWords])
    (hpack : p.procs[pack]? = some (packValuesBody copy))
    (hpackWeights : p.procs[packWeights]? = some (packGuestWeightsBody shift))
    (hprepare : p.procs[prepare]? = some (denominatorBody store shift))
    (hstore : p.procs[store]? = some (storeWordBody h))
    (hshift : p.HasAt shift (Num.shiftLeftModule shift h)) (hbits : 0 < h) (hwordBits : 3*h+2 ≤ w)
    (hsrcReg : st.regs 27 = src) (hnamesReg : st.regs 28 = names)
    (hweightReg : st.regs 31 = weightSrc) (hstrideReg : st.regs 32 = weightStride)
    (hscaleReg : st.regs 35 = scale) (hscaleFit : scale < 2^w)
    (hstrideFit : weightStride < 2^w) (hstride : N ≤ weightStride)
    (hat : ∀ i < G.m, st.mem (names+i) = edgeName G i)
    (hcap : ∀ e ∈ G.E, e < cap)
    (hlen : ∀ e ∈ G.E, Num.Valid st.mem (src+e*N) h N ∧
      Num.intVal st.mem (src+e*N) h N = len e)
    (hvalid : ∀ i < G.m, Num.Valid st.mem (weightSrc+i*weightStride) h N)
    (hfit : Num.Fits h N (scale : ℤ)) (hscaled : Num.Fits h N ((scale : ℤ)*(2 : ℤ)^P))
    (hBounds : ∀ i < G.m, 0 < len (edgeName G i) ∧ len (edgeName G i) ≤ (B : ℤ))
    (hGraphCap : 2*((2*(G.n : ℤ)*B+B)*(2 : ℤ)^P) < (Num.capacity h N : ℤ)) :
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    let cursor := staging+queryOriginals G L+2^width
    let dest := cursor+1+G.m
    let parents := dest+G.n
    let edges := parents+(levels+1)*G.n
    let depths := edges+G.n
    let queue := depths+G.n
    let adj := parents+stagedTraversalReserve G.n levels
    let records := adj+G.n
    let tails := records+6*G.n
    let heads := tails+G.m
    let lengths := tails+2*G.m
    let old := lengths+G.m*N
    let denom := old+G.m*N+N
    let dist := old+G.m*N+2*N
    let heap := dist+G.n*N
    let _C := stretchWeightRoundContract w h Q (indexedGraph G).toMGraph T G 0 (len ∘ edgeName G)
      adj parents edges depths queue G.n levels dist lengths N heap tails heads P
      old N denom j scale query
    p.procs[numeric]? = some (stretchWeightRoundBody stretch update) →
    p.procs[stretch]? = some (treeStretchRoundBody tables stretches) →
    p.procs[tables]? = some (buildTreeTablesBody traverse distance ancestors) →
    p.procs[traverse]? = some traverseTreeQueueBody →
    p.procs[distance]? = some (rootedDistanceBody distanceStep) →
    p.procs[distanceStep]? = some (rootDistanceStepBody add copy) →
    p.HasAt add (Num.addCarryModule add h) →
    p.procs[ancestors]? = some (rootedAncestorTableBody ancestorRow) →
    p.procs[ancestorRow]? = some ancestorRowBody →
    p.procs[stretches]? = some (rootedStretchRoundBody edgeQuery) →
    p.procs[edgeQuery]? = some (edgeStretchQueryBody ancestorLookup stretchEdge) →
    p.procs[ancestorLookup]? = some rootedTreeAncestorBody →
    p.procs[stretchEdge]? = some (edgeStretchBody path stretchLength) →
    p.procs[path]? = some (pathLengthBody sub add) →
    p.procs[stretchLength]? = some (stretchFromLengthBody add neg fixedDiv) →
    p.HasAt sub (Num.subtractModule sub h) →
    p.HasAt neg (Num.negateCarryModule neg h) →
    p.HasAt fixedDiv (Num.fixedDivideModule fixedDiv h) →
    p.procs[update]? = some (weightRoundBody narrow) →
    p.procs[narrow]? = some (narrowWeightBody widen copyLimbs) →
    p.procs[widen]? = some (widenWeightBody extend weightStep) →
    p.HasAt extend (Num.signExtendModule extend h) →
    p.procs[weightStep]? = some (weightUpdateBody mul integerDiv add) →
    p.HasAt mul (Num.fixedMultiplyModule mul h) →
    p.HasAt integerDiv (Num.integerDivideModule integerDiv h) →
    p.HasAt copyLimbs (Num.copyModule copyLimbs) →
    0 < scale → 2*(2 : ℝ)^P*(2*(G.m : ℝ)) < Num.capacity h N →
    (∀ e ∈ G.E, 1 ≤ weights P (scale : ℝ) query (j+1) e) →
    (∑ e ∈ G.E, weights P (scale : ℝ) query (j+1) e) ≤ 2*G.m →
    (∀ i < G.m, roundStretch P (treeStretch (indexedGraph G).toMGraph T
        (fun e => (len (edgeName G e) : ℝ)/(2 : ℝ)^Q) i) =
      query (weights P (scale : ℝ) query j) (edgeName G i)) →
    p.procs[dedup]? = some dedupSelectedTreeBody → G.n+1 < 2^w →
    (src ≤ staging+queryWeights G L ∧ ∀ e ∈ G.E, src+e*N+N ≤ staging+queryWeights G L) →
    names+G.m ≤ staging+queryWeights G L →
    weightSrc+(G.m-1)*weightStride+N ≤ staging+queryWeights G L →
    (∀ i < G.m, Num.fixVal st.mem (weightSrc+i*weightStride) h N P =
      weights P (scale : ℝ) query j (edgeName G i)) →
    heap+(G.n-1)*N+G.m*edgeStretchSpace N+G.m*narrowWeightSpace N < 2^w →
    let numericBudget := stagedRebuildNumericCost G N levels
    ∃ out cost, Runs w p ω
      (stagedRebuildRoundBody select dedup copy pack packWeights prepare adjacency numeric
        convertedGuestCallArgs)
      st .normal out cost ∧
      ((∀ i < G.m,
        let stretch := roundStretchAddr (heap+(G.n-1)*N) N i
        let weight := roundWeightAddr (heap+(G.n-1)*N+G.m*edgeStretchSpace N) N i
        (Num.Valid out.mem stretch h N ∧ Num.fixVal out.mem stretch h N P =
          query (weights P (scale : ℝ) query j) (edgeName G i)) ∧
        (Num.Valid out.mem weight h N ∧ Num.fixVal out.mem weight h N P =
          weights P (scale : ℝ) query (j+1) (edgeName G i))) ∧
      retainedStagedTreeAt G T (staging+queryWeights G L) dest (out.regs 13) st.mem out.mem ∧
      out.regs 16 = heap+(G.n-1)*N+G.m*edgeStretchSpace N+G.m*narrowWeightSpace N ∧
      ZeroFrom out.mem (out.regs 16) ∧
      out.regs 12 = cursor ∧ out.regs 20 = heap ∧
      staging+queryWeights G L ≤ dest ∧ dest+G.n ≤ out.regs 16 ∧
      out.regs 13 ≤ G.n ∧ (∀ i ∈ T.E, i < G.m) ∧
      (∀ r, r < 12 ∨ 36 ≤ r ∨ r = 14 ∨ r = 19 ∨ r = 23 ∨ r = 28 →
        out.regs r = st.regs r)) ∧
      cost ≤ argsSize convertedGuestCallArgs+convertedTreeSelectorCost w guest D G L sim guestCost+
        argsSize (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 5) (.reg 12))+
        40*G.n+numericBudget+18 := by
  intro width cursor dest parents edges depths queue adj records tails heads
    lengths old denom dist heap C hNumeric hStretch hTables hTraverse hDistance hDistanceStep hAdd hAncestors hAncestorRow hStretches hEdgeQuery hAncestorLookup hStretchEdge hPath hStretchLength hSub hNeg hFixedDiv
    hUpdate hNarrow hWiden hExtend hWeightStep hMul hIntegerDiv hCopyLimbs hscale hwidth hone hsum hstretches hDedup hnWord hsrc hnames hweightSep hweights hroom budgetN
  obtain ⟨hEdges,hVertices,hIndex,hnm⟩ := stagedController_selectedTreeBounds G T ℓ v γ hv hconn htree
  have hE : T.E.card ≤ G.n := hEdges ▸ Nat.le_succ _
  have hV : T.V.card ≤ G.n := hVertices.le
  have hCap : 2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (Num.capacity h N : ℤ) := by
    simpa only [hVertices] using hGraphCap
  have hnPos : 0 < G.n := hv.1
  have hw : 6 < 2^w := by
    obtain ⟨_,_,_,_,_,_,_,_,_,hword,_⟩ := hready.2.1
    exact (show 6 < 16 by decide).trans_le hword
  have ht := hready.2.2.1
  have hh := hready.2.2.2.1
  let base := staging+queryOriginals G L+1
  let marks := base+2^width
  have hC : MeetsContract w p numeric C :=
    stagedNumericProcedures_meetContract G T (len ∘ edgeName G)
      adj parents edges depths queue levels dist lengths N heap tails heads P old denom j
      (scale : ℤ) query hv htree hbits (by omega) hwordBits hw hmPos hcopy (Nat.le_add_right _ _)
      hNumeric hStretch hTables hTraverse hDistance hDistanceStep hAdd hAncestors hAncestorRow
      hStretches hEdgeQuery hAncestorLookup hStretchEdge hPath hStretchLength hSub hNeg hFixedDiv
      hUpdate hNarrow hWiden hExtend hWeightStep hMul hIntegerDiv hCopyLimbs
      (by exact_mod_cast hscale) hwidth (by exact_mod_cast hone) (by exact_mod_cast hsum)
      (by exact_mod_cast hstretches) hroom
  have hbasic : 2*h+2 ≤ w := by omega
  have hmIndex : (indexedGraph G).toMGraph.m = G.m := Finset.card_range _
  have hroomStretch : heap+(G.n-1)*N+G.m*edgeStretchSpace N < 2^w :=
    (Nat.le_add_right _ _).trans_lt hroom
  have hDestEq : dest = marks+G.m := by dsimp [dest,cursor,marks,base]; omega
  have hbase : staging+queryWeights G L ≤ dest := by
    have h₁ : staging+queryWeights G L ≤ staging+queryOriginals G L :=
      Nat.add_le_add_left (Nat.le_add_right _ _) _
    exact h₁.trans (((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans
      (Nat.le_add_right _ _))
  have hsep : dest+G.n ≤ tails := by dsimp [tails,records,adj,parents]; omega
  have htDist : tails ≤ dist := by dsimp [dist,old,lengths]; omega
  have hDestHeap : dest+G.n ≤ heap :=
    hsep.trans (htDist.trans (show dist ≤ heap from Nat.le_add_right _ _))
  have hDestRoom : dest+G.n < 2^w := hDestHeap.trans_lt (by omega)
  refine stagedRebuildRound_runs (ω := ω) st guest D G T L sim staging ℓ v γ
    convertedGuestCallArgs vs _ _
    hq hargs hwords hready htree ht hh hn hm hL hsim ha ?_ ?_ hnWord
    (fun out => (∀ i < G.m,
        let stretch := roundStretchAddr (heap+(G.n-1)*N) N i
        let weight := roundWeightAddr (heap+(G.n-1)*N+G.m*edgeStretchSpace N) N i
        (Num.Valid out.mem stretch h N ∧ Num.fixVal out.mem stretch h N P =
          query (weights P (scale : ℝ) query j) (edgeName G i)) ∧
        (Num.Valid out.mem weight h N ∧ Num.fixVal out.mem weight h N P =
          weights P (scale : ℝ) query (j+1) (edgeName G i))) ∧
      retainedStagedTreeAt G T (staging+queryWeights G L) dest (out.regs 13) st.mem out.mem ∧
      out.regs 16 = heap+(G.n-1)*N+G.m*edgeStretchSpace N+G.m*narrowWeightSpace N ∧
      ZeroFrom out.mem (out.regs 16) ∧
      out.regs 12 = cursor ∧ out.regs 20 = heap ∧
      staging+queryWeights G L ≤ dest ∧ dest+G.n ≤ out.regs 16 ∧
      out.regs 13 ≤ G.n ∧ (∀ i ∈ T.E, i < G.m) ∧
      (∀ r, r < 12 ∨ 36 ≤ r ∨ r = 14 ∨ r = 19 ∨ r = 23 ∨ r = 28 →
        out.regs r = st.regs r)) budgetN ?_
  · exact dedupSelectedTree_meetsContract G ℓ v γ _ _ _ _ _ _ _ hDedup
      ((by decide : 1 < 6).trans hw) hv hconn
  · rwa [hDestEq] at hDestRoom
  · intro selected hTree hcursor hregs
    rw [← hDestEq] at hTree
    have hframe : ∀ a < staging+queryWeights G L, selected.mem a = st.mem a := by
      obtain ⟨_,_,_,_,_,_,hf,_⟩ := hTree
      exact hf
    have hcount : selected.regs 13 ≤ G.n := by
      obtain ⟨_,he,hs,_⟩ := hTree
      exact he ▸ hs
    have hnames' : ∀ i < G.m, selected.mem (names+i) = edgeName G i :=
      fun i hi => (hframe _ (by omega)).trans (hat i hi)
    have hlen' : ∀ e ∈ G.E, Num.Valid selected.mem (src+e*N) h N ∧
        Num.intVal selected.mem (src+e*N) h N = len e := by
      intro e he
      obtain ⟨hv,hval⟩ := hlen e he
      have hb := hsrc.2 e he
      have hf (k : ℕ) (hk : k < N) := hframe (src+e*N+k) (by omega)
      exact ⟨fun k hk => (hf k hk).trans_lt (hv k hk), (Num.intVal_congr hf).trans hval⟩
    have hfWeight (i : ℕ) (hi : i < G.m) (k : ℕ) (hk : k < N) :
        selected.mem (weightSrc+i*weightStride+k) = st.mem (weightSrc+i*weightStride+k) := by
      have hb := Nat.mul_le_mul_right weightStride (show i ≤ G.m-1 by omega)
      exact hframe _ (by omega)
    have hvalid' : ∀ i < G.m, Num.Valid selected.mem (weightSrc+i*weightStride) h N :=
      fun i hi k hk => (hfWeight i hi k hk).trans_lt (hvalid i hi k hk)
    have hweights' (i : ℕ) (hi : i < G.m) :
        Num.fixVal selected.mem (weightSrc+i*weightStride) h N P =
          weights P (scale : ℝ) query j (edgeName G i) := by
      unfold Num.fixVal
      rw [Num.intVal_congr (hfWeight i hi)]
      exact hweights i hi
    obtain ⟨_,out,c,hr,hpost,hprefix,hcursorOut,hcountOut,hheapOut,hframeOut,hcost⟩ :=
      prepareAndRunStagedNumeric_runs (ω := ω) selected G T G L staging cursor levels
        (selected.regs 13) st.mem ℓ v γ he (pushTreeEdge_meetsContract hi (pushTreeIncidence_meetsContract hpush))
        hw hv hconn htree ht hh
        ((hregs _ (by decide) (by decide)).trans hn)
        ((hregs _ (by decide) (by decide)).trans hm)
        ((hregs _ (by decide) (by decide)).trans ha) hcursor
        ((hregs _ (by decide) (by decide)).trans hl) rfl hnPos
        N P j B src names weightSrc weightStride scale len query
        ((hregs _ (by decide) (by decide)).trans hN)
        ((hregs _ (by decide) (by decide)).trans hP)
        hNPos hmPos hE hV hnm rfl hlevels hRows hprec (copyWords_meetsContract hcopy)
        (packValues_meetsContract G hpack hcopy)
        (packHostWeights_meetsContract hpackWeights hshift hbits hbasic)
        (denominator_meetsContract hbits hbasic hprepare
          (storeWord_meetsContract ((by decide : 1 < 6).trans hw)
            (show Num.base h < 2^w from Nat.pow_lt_pow_right (by decide) (by omega)) hstore) hshift)
        ((hregs _ (by decide) (by decide)).trans hsrcReg)
        ((hregs _ (by decide) (by decide)).trans hnamesReg)
        ((hregs _ (by decide) (by decide)).trans hweightReg)
        ((hregs _ (by decide) (by decide)).trans hstrideReg)
        ((hregs _ (by decide) (by decide)).trans hscaleReg)
        hscaleFit hstrideFit hstride hnames' hcap hlen' hvalid' hfit hscaled hBounds hCap
        hC hTree hbase
        (let hlimit := hbase.trans ((Nat.le_add_right _ _).trans hsep)
         ⟨hsrc.1.trans hlimit,fun e he => (hsrc.2 e he).trans hlimit⟩)
        (hnames.trans (hbase.trans ((Nat.le_add_right _ _).trans hsep)))
        (hweightSep.trans (hbase.trans ((Nat.le_add_right _ _).trans hsep))) hweights' hroomStretch
    have hRetained : retainedStagedTreeAt G T (staging+queryWeights G L) dest
        (out.regs 13) st.mem out.mem := by
      rw [hcountOut]
      exact retainedStagedTreeAt_of_frame hTree
        (hbase.trans (Nat.le_add_right _ _)) le_rfl hprefix
    have hEnd := hpost.1
    rw [hmIndex] at hEnd
    dsimp [heap,dist,old,lengths,tails,records,adj,parents,dest] at hEnd ⊢
    have hblocks i (hi : i < G.m) := hpost.2.2.2.1 i hi
    have hDestEnd : dest+G.n ≤ out.regs 16 :=
      hDestHeap.trans (hEnd.symm ▸ (Nat.le_add_right _ _ |>.trans
        (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _))))
    refine ⟨out,c,hr,⟨?_,hRetained,hEnd,hpost.2.1,hcursorOut,hheapOut,hbase,hDestEnd,
      hcountOut.trans_le hcount,hIndex,?_⟩,?_⟩
    · intro i hi
      obtain ⟨hWeight,hStretch⟩ := hblocks i hi
      rw [hmIndex] at hWeight
      exact ⟨hStretch,hWeight⟩
    · intro r hkeep
      exact (hframeOut r hkeep).trans (hregs r (by omega) (by omega))
    · dsimp only [budgetN,stagedRebuildNumericCost]
      omega

/-- The installed arithmetic procedures meet the contract at the
scratch addresses computed by the packed runtime round. -/
theorem packedNumericProcedures_meetContract
    {w Q numeric stretch update tables stretches narrow widen copy copyLimbs traverse distance
      ancestors edgeQuery distanceStep ancestorRow add ancestorLookup stretchEdge path stretchLength
      sub neg fixedDiv extend weightStep mul integerDiv : ℕ} {p : Program}
    (G T : MGraph) (len : ℕ → ℤ)
    (cursor levels L P j : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    {ℓ v : ℕ → ℝ} {γ : ℝ}
    (hv : (indexedGraph G).Valid) (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (hwordBits : 14 ≤ w)
    (hw : 6 < 2^w) (hmPos : 0 < G.m) (hcopy : p.HasAt copy [copyWords]) :
    let N := L+(P+levels+7)/4
    let parents := cursor+1+G.m+G.n
    let edges := parents+(levels+1)*G.n
    let depths := edges+G.n
    let queue := depths+G.n
    let adj := parents+stagedTraversalReserve G.n levels
    let records := adj+G.n
    let tails := records+6*G.n
    let heads := tails+G.m
    let lengths := tails+2*G.m
    let old := lengths+G.m*N
    let denom := old+G.m*N+N
    let dist := old+G.m*N+2*N
    let heap := dist+G.n*N
    p.procs[numeric]? = some (stretchWeightRoundBody stretch update) →
    p.procs[stretch]? = some (treeStretchRoundBody tables stretches) →
    p.procs[tables]? = some (buildTreeTablesBody traverse distance ancestors) →
    p.procs[traverse]? = some traverseTreeQueueBody →
    p.procs[distance]? = some (rootedDistanceBody distanceStep) →
    p.procs[distanceStep]? = some (rootDistanceStepBody add copy) →
    p.HasAt add (Num.addCarryModule add 4) →
    p.procs[ancestors]? = some (rootedAncestorTableBody ancestorRow) →
    p.procs[ancestorRow]? = some ancestorRowBody →
    p.procs[stretches]? = some (rootedStretchRoundBody edgeQuery) →
    p.procs[edgeQuery]? = some (edgeStretchQueryBody ancestorLookup stretchEdge) →
    p.procs[ancestorLookup]? = some rootedTreeAncestorBody →
    p.procs[stretchEdge]? = some (edgeStretchBody path stretchLength) →
    p.procs[path]? = some (pathLengthBody sub add) →
    p.procs[stretchLength]? = some (stretchFromLengthBody add neg fixedDiv) →
    p.HasAt sub (Num.subtractModule sub 4) →
    p.HasAt neg (Num.negateCarryModule neg 4) →
    p.HasAt fixedDiv (Num.fixedDivideModule fixedDiv 4) →
    p.procs[update]? = some (weightRoundBody narrow) →
    p.procs[narrow]? = some (narrowWeightBody widen copyLimbs) →
    p.procs[widen]? = some (widenWeightBody extend weightStep) →
    p.HasAt extend (Num.signExtendModule extend 4) →
    p.procs[weightStep]? = some (weightUpdateBody mul integerDiv add) →
    p.HasAt mul (Num.fixedMultiplyModule mul 4) →
    p.HasAt integerDiv (Num.integerDivideModule integerDiv 4) →
    p.HasAt copyLimbs (Num.copyModule copyLimbs) →
    0 < scale → 2*(2 : ℝ)^P*(2*(G.m : ℝ)) < Num.capacity 4 N →
    (∀ e ∈ G.E, 1 ≤ weights P (scale : ℝ) query (j+1) e) →
    (∑ e ∈ G.E, weights P (scale : ℝ) query (j+1) e) ≤ 2*G.m →
    (∀ i < G.m, roundStretch P (treeStretch (indexedGraph G).toMGraph T
        (fun e => (len e : ℝ)/(2 : ℝ)^Q) i) =
      query (weights P (scale : ℝ) query j) (edgeName G i)) →
    heap+(G.n-1)*N+G.m*edgeStretchSpace N+G.m*narrowWeightSpace N < 2^w →
    MeetsContract w p numeric (stretchWeightRoundContract w 4 Q (indexedGraph G).toMGraph
      T G 0 len adj parents edges depths queue G.n levels dist lengths N heap tails heads P
      old N denom j scale query) := by
  intro N parents edges depths queue adj records tails heads lengths old denom dist heap
  exact stagedNumericProcedures_meetContract G T len adj parents edges depths queue levels
    dist lengths N heap tails heads P old denom j scale query hv htree (by decide)
    (by omega) hwordBits hw hmPos hcopy (Nat.le_add_right _ _)

/-- Four-bit arithmetic for a packed round. The entry builds traversal
tables and updates the weight blocks. All limb counts and precisions
arrive in the call arguments. -/
def packedRoundArithmeticModule (b : ℕ) : List Stmt :=
  [stretchWeightRoundBody (b+1) (b+13),
   treeStretchRoundBody (b+2) (b+8),
   buildTreeTablesBody (b+3) (b+4) (b+6),
   traverseTreeQueueBody,
   rootedDistanceBody (b+5),
   rootDistanceStepBody (b+17) (b+16),
   rootedAncestorTableBody (b+7),
   ancestorRowBody,
   rootedStretchRoundBody (b+9),
   edgeStretchQueryBody (b+10) (b+11),
   rootedTreeAncestorBody,
   edgeStretchBody (b+12) (b+15),
   pathLengthBody (b+18) (b+17),
   weightRoundBody (b+30),
   widenWeightBody (b+32) (b+31),
   stretchFromLengthBody (b+17) (b+23) (b+35),
   copyWords] ++
  Num.addCarryModule (b+17) 4 ++
  Num.subtractModule (b+18) 4 ++
  Num.negateCarryModule (b+23) 4 ++
  List.replicate 6 .nop ++
  [narrowWeightBody (b+14) (b+103),weightUpdateBody (b+67) (b+78) (b+17)] ++
  Num.signExtendModule (b+32) 4 ++
  Num.fixedDivideModule (b+35) 4 ++
  Num.fixedMultiplyModule (b+67) 4 ++
  Num.integerDivideModule (b+78) 4 ++
  Num.copyModule (b+103)

/-- The fixed offsets of the arithmetic module cover the full procedure
list, including the nested division and multiplication modules. -/
theorem packedRoundArithmeticModule_length (b : ℕ) :
    (packedRoundArithmeticModule b).length = 104 := by
  rfl

/-- The installed arithmetic module exposes its helper procedures at
the offsets used by the traversal and weight update. -/
theorem packedRoundArithmeticModule_helpers {p : Program} {b : ℕ}
    (hp : p.HasAt b (packedRoundArithmeticModule b)) :
    p.HasAt (b+16) [copyWords] ∧
    p.HasAt (b+17) (Num.addCarryModule (b+17) 4) ∧
    p.HasAt (b+18) (Num.subtractModule (b+18) 4) ∧
    p.HasAt (b+23) (Num.negateCarryModule (b+23) 4) ∧
    p.HasAt (b+32) (Num.signExtendModule (b+32) 4) ∧
    p.HasAt (b+35) (Num.fixedDivideModule (b+35) 4) ∧
    p.HasAt (b+67) (Num.fixedMultiplyModule (b+67) 4) ∧
    p.HasAt (b+78) (Num.integerDivideModule (b+78) 4) ∧
    p.HasAt (b+103) (Num.copyModule (b+103)) := by
  have hcopy : p.HasAt (b+16) [copyWords] := by
    intro i hi
    have he : i = 0 := by simp at hi; omega
    subst i
    exact hp.get (i := 16) (by rw [packedRoundArithmeticModule_length]; decide)
  unfold packedRoundArithmeticModule at hp
  simp only [List.append_assoc] at hp
  have ht := Num.hasAt_append_right hp
  have hadd := Num.hasAt_append_left ht
  have ht := Num.hasAt_append_right ht
  have hsub := Num.hasAt_append_left ht
  have ht := Num.hasAt_append_right ht
  have hneg := Num.hasAt_append_left ht
  have ht := Num.hasAt_append_right (Num.hasAt_append_right (Num.hasAt_append_right ht))
  have hext := Num.hasAt_append_left ht
  have ht := Num.hasAt_append_right ht
  have hdiv := Num.hasAt_append_left ht
  have ht := Num.hasAt_append_right ht
  have hmul := Num.hasAt_append_left ht
  have ht := Num.hasAt_append_right ht
  exact ⟨hcopy,hadd,hsub,hneg,hext,hdiv,hmul,Num.hasAt_append_left ht,Num.hasAt_append_right ht⟩

end MinCostFlow.LastLevelProgram
