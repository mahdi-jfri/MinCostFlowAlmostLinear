module

public import MinCostFlow.LastLevelProgram.StagedRoundPreparation
import MinCostFlow.LastLevelProgram.ConnectedLSST
import MinCostFlow.LastLevelProgram.OutputCapacity
import MinCostFlow.Num.WordBounds
import MinCostFlow.LSF.Components

/-!
# Running the widened last-level round

The Definition 5.8 rebuild (pages 19–20) runs numeric arithmetic on the prepared blocks and compacts the output.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- Sign extension keeps the compact length numerators and the decoded
current weights required by the numeric round. -/
theorem widenedNumericArrays
    {G H : MGraph} {before after : ℕ → ℕ}
    {h L K P src lenBase weightSrc weightBase stride j : ℕ}
    (len : ℕ → ℤ) (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hm : H.m = G.m)
    (hblocks : ∀ i < G.m,
      (Valid after (lenBase+i*K) h K ∧ intVal after (lenBase+i*K) h K =
        intVal before (src+edgeName G i*L) h L) ∧
      (Valid after (weightBase+i*K) h K ∧ intVal after (weightBase+i*K) h K =
        intVal before (weightSrc+i*stride) h L))
    (hlen : ∀ i < G.m, intVal before (src+edgeName G i*L) h L = len i)
    (hweights : ∀ i < H.m, fixVal before (weightSrc+i*stride) h L P =
      weights P (scale : ℝ) query j (edgeName H i)) :
    (∀ i < G.m, Valid after (lenBase+i*K) h K ∧ intVal after (lenBase+i*K) h K = len i) ∧
    (∀ i < H.m, Valid after (weightBase+i*K) h K ∧ fixVal after (weightBase+i*K) h K P =
      weights P (scale : ℝ) query j (edgeName H i)) := by
  constructor
  · intro i hi
    obtain ⟨hv,he⟩ := (hblocks i hi).1
    exact ⟨hv,he.trans (hlen i hi)⟩
  · intro i hi
    obtain ⟨hv,he⟩ := (hblocks i (hm ▸ hi)).2
    refine ⟨hv,?_⟩
    calc
      _ = fixVal before (weightSrc+i*stride) h L P := by simp only [fixVal,he]
      _ = _ := hweights i hi

/-- Positive caller length numerators fit below the signed half-range.
That saved sign bit covers the extra traversal level in the scratch bound. -/
theorem widenedNumericLengthBounds
    {L P n levels m : ℕ} {len : ℕ → ℤ}
    (hL : 0 < L) (hn : n ≤ 2^(levels+1))
    (hlen : ∀ i < m, 0 < len i ∧ Fits 4 L (len i)) :
    let B := 2^(4*L-1)
    let K := L+(P+levels+7)/4
    (∀ i < m, 0 < len i ∧ len i ≤ (B : ℤ)) ∧
    2*((2*(n : ℤ)*B+B)*(2 : ℤ)^P) < (capacity 4 K : ℤ) := by
  intro B K
  have hb : 4*L-1+1 = 4*L := by omega
  constructor
  · intro i hi
    obtain ⟨hpos,_,hfit⟩ := hlen i hi
    rw [capacity_eq_two_pow,← hb,Nat.pow_succ,Nat.cast_mul] at hfit
    change 2 * len i < (B : ℤ) * (2 : ℤ) at hfit
    exact ⟨hpos,by omega⟩
  · apply numericTreeCapacity_of_bits hn (b := 4*L-1) le_rfl
    dsimp [K]
    omega

/-- Run the numeric pass at the runtime scratch width. The original
signed length range supplies the capacity for root-distance arithmetic. -/
theorem preparedWideNumericRound_runs {w Q adjacency numeric insert : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G T H : MGraph) (L staging cursor levels count callerL : ℕ)
    (mem : ℕ → ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (he : p.procs[adjacency]? = some (selectedAdjacencyBody insert))
    (hi : MeetsContract w p insert (pushTreeEdgeContract w))
    (hw : 6 < 2^w) (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : LSF.IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (ha : st.regs 5 = staging)
    (hc : st.regs 12 = cursor) (hl : st.regs 14 = levels) (hk : st.regs 13 = count)
    (hnPos : 0 < G.n)
    (P j : ℕ) (len : ℕ → ℤ) (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hP : st.regs 23 = P) (hCaller : 0 < callerL)
    (hmPos : 0 < G.m)
    (hE : T.E.card ≤ G.n) (hV : T.V.card ≤ G.n) (hnm : G.n ≤ G.m+1)
    (heq : H.m = G.m) (hlevels : G.n ≤ 2^(levels+1)) (hRows : levels+1 < 2^w)
    (hprec : P < 2^w)
    (hLenFit : ∀ i < G.m, 0 < len i ∧ Fits 4 callerL (len i)) :
    let N := callerL+(P+levels+7)/4
    st.regs 24 = N →
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
    let words := [adj,parents,edges,depths,queue,0,G.n,levels,dist,lengths,N,heap,
      tails,heads,P,G.m,old,N,denom,edgeStretchSpace N]
    let C := stretchWeightRoundContract w 4 Q (indexedGraph G).toMGraph T H 0 len
      adj parents edges depths queue G.n levels dist lengths N heap tails heads P
      old N denom j scale query
    MeetsContract w p numeric C →
    st.regs 17 = dist → st.regs 18 = lengths → st.regs 20 = heap →
    st.regs 21 = tails → st.regs 22 = heads → st.regs 26 = old → st.regs 25 = denom →
    retainedStagedTreeAt G T (staging+queryWeights G L) dest count mem st.mem →
    staging+queryWeights G L ≤ dest →
    (∀ a, dest+G.n ≤ a → a < records → st.mem a = 0) →
    ListAt st.mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) →
    ListAt st.mem heads (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) →
    (∀ i < G.m, Num.Valid st.mem (lengths+i*N) 4 N ∧ Num.intVal st.mem (lengths+i*N) 4 N = len i) →
    Num.Valid st.mem denom 4 N → Num.intVal st.mem denom 4 N = scale*(2 : ℤ)^P →
    (∀ i < H.m, Num.Valid st.mem (old+i*N) 4 N ∧
      Num.fixVal st.mem (old+i*N) 4 N P = weights P (scale : ℝ) query j (edgeName H i)) →
    ZeroFrom st.mem dist → heap+(G.n-1)*N+G.m*edgeStretchSpace N < 2^w →
    ∃ (mid out : State) (cost : ℕ),
      Runs w p ω (stagedNumericBodyFrom adjacency numeric 24) st .normal out cost ∧
      C.post words mid.mem (out.regs 16) out.mem ∧
      (∀ a < adj, mid.mem a = st.mem a) ∧
      (∀ a < parents, out.mem a = st.mem a) ∧
      (∀ r, r ≠ 15 → r ≠ 16 → out.regs r = st.regs r) ∧
      cost ≤ argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
        (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
        argsSize (stagedNumericArgsFrom 24)+112*count+stagedNumericFactor N levels*(G.m+1)+13 := by
  intro N hN
  let B := 2^(4*callerL-1)
  obtain ⟨hBounds,hCap⟩ := widenedNumericLengthBounds (P := P) hCaller hlevels hLenFit
  change 2*((2*(G.n : ℤ)*B+B)*(2 : ℤ)^P) < (capacity 4 N : ℤ) at hCap
  have hCapTree : 2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (capacity 4 N : ℤ) := by
    refine lt_of_le_of_lt ?_ hCap
    have hv' : (T.V.card : ℤ) ≤ G.n := by exact_mod_cast hV
    gcongr
  exact preparedStagedNumericRound_runs (ω := ω) st G T H L staging cursor levels count 24
    (by decide) mem ℓ v γ he hi hw hv hconn htree ht hh hn hm ha hc hl hk hnPos
    N P j B len scale query hN hP hN (by dsimp [N]; omega) hmPos hE hV hnm heq
    hlevels hRows hprec hBounds hCapTree

/-- Compact the numeric contract's output and preserve the part of the
prepared state below its traversal write boundary. -/
theorem wideNumeric_publicationFrame
    {w h Q pack shift limit : ℕ} {p : Program} {ω : ℕ → Bool}
    (ready st : State) (G T H : MGraph) (len : ℕ → ℤ)
    (adj parents edges depths queue n levels dist lengths K heap tails heads P old stride denom j L : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ) (args : List ℕ) (mem : ℕ → ℕ)
    (he : p.procs[pack]? = some (packGuestWeightsBody shift))
    (hp : p.HasAt shift (Num.shiftLeftModule shift h)) (hh : 0 < h) (hw : 2*h+2 ≤ w)
    (hr : ∀ r, r ≠ 15 → r ≠ 16 → st.regs r = ready.regs r)
    (hlimit : limit ≤ heap) (hframe : ∀ a < limit, st.mem a = ready.mem a)
    (hn : ready.regs 0 = n) (hm : ready.regs 1 = G.m) (hL : ready.regs 19 = L)
    (hK : ready.regs 24 = K) (hheap : ready.regs 20 = heap)
    (hnWord : n < 2^w) (hmWord : G.m < 2^w) (hLWord : L < 2^w)
    (hmPos : 0 < G.m) (hKPos : 0 < K) (hword : 1 < 2^w) (hLK : L ≤ K)
    (hmEq : H.m = G.m)
    (hpost : (stretchWeightRoundContract w h Q G T H 0 len adj parents edges depths queue n
      levels dist lengths K heap tails heads P old stride denom j scale query).post args mem
      (st.regs 16) st.mem)
    (sBound wBound : ℝ)
    (hs : ∀ i < H.m, let s := query (weights P (scale : ℝ) query j) (edgeName H i)
      0 ≤ s ∧ s ≤ sBound)
    (hwt : ∀ i < H.m, let v := weights P (scale : ℝ) query (j+1) (edgeName H i)
      0 ≤ v ∧ v ≤ wBound)
    (hsFit : 2*(2 : ℝ)^P*sBound < Num.capacity h L)
    (hwFit : 2*(2 : ℝ)^P*wBound < Num.capacity h L) :
    let stop := heap+(n-1)*K+G.m*edgeStretchSpace K+G.m*narrowWeightSpace K
    stop+G.m*L+G.m*L < 2^w →
    ∃ out cost, Runs w p ω (publishableWideOutputs pack) st .normal out cost ∧
      out.regs 16 = stop+G.m*L+G.m*L ∧ out.regs 36 = stop ∧ out.regs 37 = L ∧
      out.regs 38 = stop+G.m*L ∧ out.regs 39 = L ∧
      (∀ r, r ≠ 15 → r ≠ 16 → r ∉ ([36,37,38,39] : List ℕ) → out.regs r = ready.regs r) ∧
      ZeroFrom out.mem (stop+G.m*L+G.m*L) ∧ (∀ a < limit, out.mem a = ready.mem a) ∧
      (∀ i < H.m, Num.Valid out.mem (stop+i*L) h L ∧
        Num.fixVal out.mem (stop+i*L) h L P =
          query (weights P (scale : ℝ) query j) (edgeName H i)) ∧
      (∀ i < H.m, Num.Valid out.mem (stop+G.m*L+i*L) h L ∧
        Num.fixVal out.mem (stop+G.m*L+i*L) h L P =
          weights P (scale : ℝ) query (j+1) (edgeName H i)) ∧
      cost ≤ 2*((35*L+60)*G.m+17)+argsSize packedStagedOutputArgs+
        argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 24) (.reg 20))+21 := by
  intro stop hroom
  obtain ⟨out,cost,hrun,h16,h36,h37,h38,h39,hkeep,hz,hmem,hstretch,hweight,hcost⟩ :=
    publishableWideOutputs_of_numericPost (ω := ω) st G T H len adj parents edges depths queue n
      levels dist lengths K heap tails heads P old stride denom j L scale query args mem
      he hp hh hw ((hr 0 (by decide) (by decide)).trans hn) ((hr 1 (by decide) (by decide)).trans hm)
      ((hr 19 (by decide) (by decide)).trans hL) ((hr 24 (by decide) (by decide)).trans hK)
      ((hr 20 (by decide) (by decide)).trans hheap) hnWord hmWord hLWord hmPos hKPos hword hLK
      hmEq hpost sBound wBound hs hwt hsFit hwFit hroom
  have hle : limit ≤ stop := hlimit.trans (by dsimp [stop]; omega)
  exact ⟨out,cost,hrun,h16,h36,h37,h38,h39,fun r h15 h16 hrs =>
    (hkeep r h16 hrs).trans (hr r h15 h16),hz,
    fun a ha => (hmem a (ha.trans_le hle)).trans (hframe a ha),hstretch,hweight,hcost⟩

/-- Compute and pack the round outputs while retaining the memory
and registers used to append the branch. -/
theorem preparedWideNumeric_publish_runs {w Q adjacency numeric insert pack shift : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G T H : MGraph) (L staging cursor levels count callerL : ℕ)
    (mem : ℕ → ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (he : p.procs[adjacency]? = some (selectedAdjacencyBody insert))
    (hi : MeetsContract w p insert (pushTreeEdgeContract w))
    (hw : 6 < 2^w) (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : LSF.IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (ha : st.regs 5 = staging)
    (hc : st.regs 12 = cursor) (hl : st.regs 14 = levels) (hk : st.regs 13 = count)
    (hnPos : 0 < G.n)
    (P j : ℕ) (len : ℕ → ℤ) (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hP : st.regs 23 = P) (hCaller : 0 < callerL)
    (hmPos : 0 < G.m)
    (hE : T.E.card ≤ G.n) (hV : T.V.card ≤ G.n) (hnm : G.n ≤ G.m+1)
    (heq : H.m = G.m) (hlevels : G.n ≤ 2^(levels+1)) (hRows : levels+1 < 2^w)
    (hprec : P < 2^w)
    (hpack : p.procs[pack]? = some (packGuestWeightsBody shift))
    (hshift : p.HasAt shift (shiftLeftModule shift 4)) (hwidth : 10 ≤ w)
    (hcaller : st.regs 19 = callerL) (hcallerWord : callerL < 2^w)
    (hnWord : G.n < 2^w) (hmWord : G.m < 2^w)
    (sBound wBound : ℝ)
    (hs : ∀ i < H.m, let s := query (weights P (scale : ℝ) query j) (edgeName H i)
      0 ≤ s ∧ s ≤ sBound)
    (hwt : ∀ i < H.m, let v := weights P (scale : ℝ) query (j+1) (edgeName H i)
      0 ≤ v ∧ v ≤ wBound)
    (hsFit : 2*(2 : ℝ)^P*sBound < capacity 4 callerL)
    (hwFit : 2*(2 : ℝ)^P*wBound < capacity 4 callerL)
    (hLenFit : ∀ i < G.m, 0 < len i ∧ Fits 4 callerL (len i)) :
    let N := callerL+(P+levels+7)/4
    st.regs 24 = N →
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
    let C := stretchWeightRoundContract w 4 Q (indexedGraph G).toMGraph T H 0 len
      adj parents edges depths queue G.n levels dist lengths N heap tails heads P
      old N denom j scale query
    MeetsContract w p numeric C →
    st.regs 17 = dist → st.regs 18 = lengths → st.regs 20 = heap →
    st.regs 21 = tails → st.regs 22 = heads → st.regs 26 = old → st.regs 25 = denom →
    retainedStagedTreeAt G T (staging+queryWeights G L) dest count mem st.mem →
    staging+queryWeights G L ≤ dest →
    (∀ a, dest+G.n ≤ a → a < records → st.mem a = 0) →
    ListAt st.mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) →
    ListAt st.mem heads (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) →
    (∀ i < G.m, Num.Valid st.mem (lengths+i*N) 4 N ∧ Num.intVal st.mem (lengths+i*N) 4 N = len i) →
    Num.Valid st.mem denom 4 N → Num.intVal st.mem denom 4 N = scale*(2 : ℤ)^P →
    (∀ i < H.m, Num.Valid st.mem (old+i*N) 4 N ∧
      Num.fixVal st.mem (old+i*N) 4 N P = weights P (scale : ℝ) query j (edgeName H i)) →
    ZeroFrom st.mem dist →
    let stop := heap+(G.n-1)*N+G.m*edgeStretchSpace N+G.m*narrowWeightSpace N
    stop+G.m*callerL+G.m*callerL < 2^w →
    ∃ computed packed cn cp,
      Runs w p ω (stagedNumericBodyFrom adjacency numeric 24) st .normal computed cn ∧
      Runs w p ω (publishableWideOutputs pack) computed .normal packed cp ∧
      packed.regs 16 = stop+G.m*callerL+G.m*callerL ∧
      packed.regs 36 = stop ∧ packed.regs 37 = callerL ∧
      packed.regs 38 = stop+G.m*callerL ∧ packed.regs 39 = callerL ∧
      (∀ r, r ≠ 15 → r ≠ 16 → r ∉ ([36,37,38,39] : List ℕ) → packed.regs r = st.regs r) ∧
      ZeroFrom packed.mem (stop+G.m*callerL+G.m*callerL) ∧ (∀ a < parents, packed.mem a = st.mem a) ∧
      retainedStagedTreeAt G T (staging+queryWeights G L) dest count mem packed.mem ∧
      (∀ i < H.m, Valid packed.mem (stop+i*callerL) 4 callerL ∧
        fixVal packed.mem (stop+i*callerL) 4 callerL P =
          query (weights P (scale : ℝ) query j) (edgeName H i)) ∧
      (∀ i < H.m, Valid packed.mem (stop+G.m*callerL+i*callerL) 4 callerL ∧
        fixVal packed.mem (stop+G.m*callerL+i*callerL) 4 callerL P =
          weights P (scale : ℝ) query (j+1) (edgeName H i)) ∧
      cn ≤ argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
        (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
        argsSize (stagedNumericArgsFrom 24)+112*count+stagedNumericFactor N levels*(G.m+1)+13 ∧
      cp ≤ 2*((35*callerL+60)*G.m+17)+argsSize packedStagedOutputArgs+
        argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 24) (.reg 20))+21 := by
  intro N hN dest parents edges depths queue adj records tails heads lengths old denom dist heap C
    hC hd hLen hheap htReg hhReg ho hb hTree hsep hz htMem hhMem hlen hden hdenVal hweights
    hzero stop hroom
  have hroom' : heap+(G.n-1)*N+G.m*edgeStretchSpace N < 2^w :=
    (Nat.le_add_right _ _).trans_lt ((Nat.le_add_right _ _).trans_lt
      ((Nat.le_add_right _ _).trans_lt hroom))
  obtain ⟨mid,computed,cn,hnRun,hpost,_,hframe,hregs,hcn⟩ :=
    preparedWideNumericRound_runs (ω := ω) st G T H L staging cursor levels count callerL mem ℓ v γ
      he hi hw hv hconn htree ht hh hn hm ha hc hl hk hnPos P j len scale query hP hCaller
      hmPos hE hV hnm heq hlevels hRows hprec hLenFit hN hC hd hLen hheap htReg hhReg ho hb
      hTree hsep hz htMem hhMem hlen hden hdenVal hweights hzero hroom'
  have hlimit : parents ≤ heap := by
    dsimp [heap,dist,old,lengths,tails,records,adj]
    omega
  have hLK : callerL ≤ N := Nat.le_add_right _ _
  obtain ⟨packed,cp,hpRun,h16,h36,h37,h38,h39,hkeep,hfresh,hpres,hstretches,hweights',hcp⟩ :=
    wideNumeric_publicationFrame (ω := ω) st computed (indexedGraph G).toMGraph T H len adj parents edges
      depths queue G.n levels dist lengths N heap tails heads P old N denom j callerL scale query _ mid.mem
      hpack hshift (by decide) hwidth hregs hlimit hframe hn
      (by simpa only [WideWord.IndexedGraph.toMGraph_m, indexedGraph] using hm) hcaller hN hheap
      hnWord (by simpa only [WideWord.IndexedGraph.toMGraph_m, indexedGraph] using hmWord) hcallerWord
      (by simpa only [WideWord.IndexedGraph.toMGraph_m, indexedGraph] using hmPos)
      (hCaller.trans_le hLK) (by omega) hLK
      (by simpa only [WideWord.IndexedGraph.toMGraph_m, indexedGraph] using heq) hpost
      sBound wBound hs hwt hsFit hwFit
      (by simpa only [WideWord.IndexedGraph.toMGraph_m, indexedGraph] using hroom)
  simp only [WideWord.IndexedGraph.toMGraph_m, indexedGraph] at h16 h36 h38 hfresh hstretches hweights' hcp
  have hretained := retainedStagedTreeAt_congr hTree
    (hsep.trans (show dest ≤ parents from Nat.le_add_right _ _))
    (show dest+G.n ≤ parents from le_rfl) hpres
  exact ⟨computed,packed,cn,cp,hnRun,hpRun,h16,h36,h37,h38,h39,hkeep,hfresh,hpres,hretained,
    hstretches,hweights',hcn,hcp⟩

/-- The precision computed from the update scale leaves room for the
scaled denominator at scratch width. The caller need only fit the output grid. -/
theorem widenedScaleFits {L P levels scale : ℕ}
    (hpos : 0 < scale) (hP : P ≤ 4*L) (hscale : 2*scale < 2^P) :
    let K := L+(P+levels+7)/4
    Fits 4 K (scale : ℤ) ∧ Fits 4 K ((scale : ℤ)*(2 : ℤ)^P) := by
  intro K
  have hbits : P+P ≤ 4*K := by dsimp [K]; omega
  have hcap : 2*scale*2^P < capacity 4 K := by
    rw [capacity_eq_two_pow]
    calc
      _ < 2^P*2^P := Nat.mul_lt_mul_of_pos_right hscale (Nat.two_pow_pos _)
      _ = 2^(P+P) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hbits
  have hreal : 2*(scale : ℝ)*(2 : ℝ)^P < capacity 4 K := by exact_mod_cast hcap
  exact (stagedController_scaleFits hpos hreal).imp_right And.left

/-- A caller that can store the round stretches can also store one.
The model precision then bounds the widened denominator of its update. -/
theorem canonicalRound_scaleCapacity (G H : MGraph) (length : ℕ → ℝ)
    (C : ℝ) (L levels : ℕ) (hm : 0 < H.m)
    (hne : G.E.Nonempty) (hlen : ∀ e ∈ G.E, 0 < length e)
    (hwidth : ∀ e ∈ G.E, 2*(2 : ℝ)^weightPrecision C H*MinRatio.lastLevelStretchBound G length e <
      capacity 4 L) :
    let P := weightPrecision C H
    let scale := integerScale ⌈max 1 C⌉₊ H
    let K := L+(P+levels+7)/4
    0 < L ∧ P ≤ 4*L ∧ 2*(2 : ℝ)^P < capacity 4 L ∧
      Fits 4 K (scale : ℤ) ∧ Fits 4 K ((scale : ℤ)*(2 : ℤ)^P) := by
  intro P scale K
  obtain ⟨e,he⟩ := hne
  have hunit : 1 ≤ MinRatio.lastLevelStretchBound G length e := by
    unfold MinRatio.lastLevelStretchBound
    have hsum : 0 ≤ ∑ f ∈ G.E, length f := Finset.sum_nonneg (fun f hf => (hlen f hf).le)
    linarith only [div_nonneg hsum (hlen e he).le]
  have hcap : 2*(2 : ℝ)^P < capacity 4 L :=
    (le_mul_of_one_le_right (by positivity) hunit).trans_lt (hwidth e he)
  have hnat : 2*2^P < capacity 4 L := by exact_mod_cast hcap
  rw [capacity_eq_two_pow] at hnat
  have hprec : P < 4*L := by
    by_contra! hn
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    omega
  have hpow : 2*scale < 2^P := Nat.lt_size_self _
  have hposReal : 0 < roundedScale C H :=
    (mul_pos zero_lt_two (SparseCore.lastRho_pos hm)).trans_le (roundedScale_bounds C H).1
  have hpos : 0 < scale := by
    change (0 : ℝ) < (scale : ℝ) at hposReal
    exact_mod_cast hposReal
  exact ⟨by omega,hprec.le,hcap,widenedScaleFits (levels := levels) hpos hprec.le hpow⟩

/-- Every live representative round has a fitting canonical tree query
and outputs that fit the caller's packed tables. -/
theorem canonicalRound_modelInputs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (length : ℕ → ℝ) (L j : ℕ)
    (hOracle : LSF.HasLSSTSpec oracle C) (hG : G.IsValid)
    (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hlen : ∀ e ∈ G.E, 0 < length e)
    (hgrid : ∃ Q, ∀ e ∈ G.E, ∃ a : ℤ, length e = (a : ℝ)/(2 : ℝ)^Q) :
    let H := representativeGraph G length
    let P := weightPrecision C H
    let ρ := roundedScale C H
    let query := stretchQuery oracle H length P
    let v := weights P ρ query
    j < H.m →
    (∀ e ∈ G.E, 2*(2 : ℝ)^P*MinRatio.lastLevelStretchBound G length e < capacity 4 L) →
    GraphQueryReady C H (LSF.safeLen H length) (v j) ∧
    LSF.IsLSST H (LSF.safeLen H length) (v j) (C * (Real.log ((H.n : ℝ)+2))^2)
      (oracle H (LSF.safeLen H length) (v j)) ∧
    (∀ e ∈ H.E, 1 ≤ v (j+1) e) ∧
    (∑ e ∈ H.E, v (j+1) e) ≤ 2*H.m ∧
    ∃ B : ℝ, 2*(2 : ℝ)^P*B < capacity 4 L ∧
      (∀ e ∈ H.E, 0 ≤ query (v j) e ∧ query (v j) e ≤ B) ∧
      ∀ e ∈ H.E, 0 ≤ v (j+1) e ∧ v (j+1) e ≤ B := by
  intro H P ρ query v hj hwidth
  obtain ⟨e,he⟩ := hne
  have he' := (representativeGraph_shortest (ℓ := length) he).1
  have hH := representativeGraph_valid G length
  have hsub := (representativeGraph_subgraph hG length).2.1
  have hm : 1 ≤ H.m := Finset.card_pos.mpr ⟨_,he'⟩
  have hV : H.V.Nonempty := ⟨_,(hH _ he').1⟩
  have hlen' (f : ℕ) (hf : f ∈ H.E) : 0 < length f := hlen f (hsub hf)
  have horacle : ∀ k < SparseCore.lastMWUK H,
      (∀ f ∈ H.E, 1 ≤ v k f) → (∑ f ∈ H.E, v k f) ≤ 2*H.m →
      LSF.IsLSST H (LSF.safeLen H length) (v k) (C * (Real.log ((H.n : ℝ)+2))^2)
        (oracle H (LSF.safeLen H length) (v k)) := by
    intro k _ hw _
    apply hOracle H _ _ hH hV
    · intro f hf
      simpa [LSF.safeLen,hf] using hlen' f hf
    · exact fun f hf => zero_lt_one.trans_le (hw f hf)
  have hinv := (stretchQuery_bounds oracle C H length hm hlen' horacle).1
  have hk := hj.trans_le (lastMWUK_ge_edges H)
  obtain ⟨hA,hB⟩ := hinv j hk.le
  obtain ⟨hC,hD⟩ := hinv (j+1) hk
  exact ⟨representativeRound_graphQueryReady oracle C G length j hG hlen hgrid hk hA hB,
    horacle j hk hA hB,hC,hD,packedRoundOutputCapacity oracle G H length 4 P L j ρ _ hsub ⟨_,hsub he'⟩ hH hlen
      hwidth (horacle j hk hA hB) hC hD⟩

/-- Decode the runtime input lengths on their caller grid and discharge
the canonical round's model and output-capacity premises. -/
theorem canonicalRound_modelInputs_of_runtimePre
    {w L vCap eCap multiplier g src heap j : ℕ} (fmt : Format w)
    (allocation : ℕ → List ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G : MGraph) (mem : ℕ → ℕ)
    (hOracle : LSF.HasLSSTSpec oracle C)
    (hne : (SparseCore.nonLoopEdges G).Nonempty) :
    let length := MinRatio.readEdgeValues mem src 4 L fmt.precision G.E
    let H := representativeGraph G length
    let P := weightPrecision C H
    let ρ := roundedScale C H
    let query := stretchQuery oracle H length P
    let v := weights P ρ query
    (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C) G
      vCap eCap multiplier P allocation).initPre [g,src,L,fmt.precision,heap] mem →
    j < H.m →
    GraphQueryReady C H (LSF.safeLen H length) (v j) ∧
    LSF.IsLSST H (LSF.safeLen H length) (v j) (C * (Real.log ((H.n : ℝ)+2))^2)
      (oracle H (LSF.safeLen H length) (v j)) ∧
    (∀ e ∈ H.E, 1 ≤ v (j+1) e) ∧
    (∑ e ∈ H.E, v (j+1) e) ≤ 2*H.m ∧
    ∃ B : ℝ, 2*(2 : ℝ)^P*B < capacity 4 L ∧
      (∀ e ∈ H.E, 0 ≤ query (v j) e ∧ query (v j) e ≤ B) ∧
      ∀ e ∈ H.E, 0 ≤ v (j+1) e ∧ v (j+1) e ≤ B := by
  intro length H P ρ query v hpre hj
  obtain ⟨g',src',heap',heq,hbits,_,hbase,hcap⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  obtain ⟨g',src',heap',heq,hgraph,_,_,_,hpos⟩ := hbase
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  have hG := hgraph.1
  have hgrid : ∃ Q, ∀ e ∈ G.E, ∃ a : ℤ, length e = (a : ℝ)/(2 : ℝ)^Q := by
    refine ⟨fmt.precision,fun e he => ⟨intVal mem (src+e*L) 4 L,?_⟩⟩
    simp only [length,MinRatio.readEdgeValues,ite_eq_left he,fixVal]
  exact canonicalRound_modelInputs oracle C G length L j hOracle hG hne
    (by simpa only [hbits] using hpos) hgrid hj (by simpa only [hbits] using hcap)

end MinCostFlow.LastLevelProgram
