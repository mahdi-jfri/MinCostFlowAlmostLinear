module

public import MinCostFlow.LastLevelProgram.ConnectedLSST
public import MinCostFlow.LastLevelProgram.StretchWeightRound
import Mathlib.Data.List.Nodup
import WordRAM.Tactic
import MinCostFlow.LastLevelProgram.RepresentativeGraph

/-!
# Traversing the selected low-stretch tree

For Definition 5.8 (pages 19–20), the distinct selected indices enumerate
the edges of the compact LSST. The adjacency call builds their incidence
lists, which the queue traversal reads to assign parents and depths.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord LSF Num

private theorem adjacencyMemory_congr (mem : ℕ → ℕ) (adj records : ℕ)
    (u v u' v' edge : ℕ → ℕ) (k : ℕ)
    (hends : ∀ i < k, u i = u' i ∧ v i = v' i) :
    originalTreeAdjacencyMemory mem adj records u v edge k =
      originalTreeAdjacencyMemory mem adj records u' v' edge k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨hu,hv⟩ := hends k (Nat.lt_succ_self _)
    rw [originalTreeAdjacencyMemory, originalTreeAdjacencyMemory, hu, hv]
    rw [ih (fun i hi => hends i (hi.trans (Nat.lt_succ_self _)))]

/-- The adjacency result gives the traversal precondition if the queue
tables fit below the incidence lists and their starting cells are zero. -/
theorem traverseTreeQueue_pre_of_selected {w r : ℕ} {G : IndexedGraph} {T : MGraph}
    {mem out : ℕ → ℕ} {args : List ℕ} {ret : ℕ} (kept : List ℕ)
    (selected tails heads adj records parents edges depths queue floor : ℕ)
    (hnodup : kept.Nodup) (hT : T.IsForest) (hindex : ∀ e ∈ kept, e < G.m)
    (hdecode : decodedTree G.n G.m G.tail G.head kept [] = T)
    (hpost : (selectedAdjacencyContract w G kept selected tails heads adj records).post
      args mem ret out)
    (hw : 2 < 2^w) (hPE : parents + G.n ≤ edges) (hED : edges + G.n ≤ depths)
    (hDQ : depths + G.n ≤ queue) (hQF : queue + G.n < floor) (hFA : floor ≤ adj)
    (hAR : adj + G.n ≤ records) (hroom : records + 6 * kept.length < 2^w)
    (hdepth : mem (depths + r) = 0) (hheads : ∀ x < G.n, mem (adj + x) = 0) :
    (traverseTreeQueueContract w T r).pre [adj, parents, edges, depths, queue, r] out := by
  let edge := fun i => kept.getD i 0
  have hV : ∀ x, x ∈ T.V ↔ x < G.n := by
    intro x
    rw [← hdecode]
    exact Finset.mem_range
  have hE : ∀ e, e ∈ T.E ↔ e ∈ kept := by
    intro e
    rw [← hdecode]
    simp [decodedTree]
  have hget (i : ℕ) (hi : i < kept.length) : edge i = kept[i] := by
    simp [edge, hi]
  have hEnum : ∀ e, e ∈ T.E ↔ ∃ i < kept.length, edge i = e := by
    intro e
    rw [hE, List.mem_iff_getElem]
    constructor
    · rintro ⟨i, hi, he⟩
      exact ⟨i, hi, (hget i hi).trans he⟩
    · rintro ⟨i, hi, he⟩
      exact ⟨i, hi, (hget i hi).symm.trans he⟩
  refine ⟨adj, parents, edges, depths, queue, floor, records, G.n, kept.length, edge, mem,
    rfl, ?_, hw, hV, hPE, hED, hDQ, hQF, hFA, hAR, hroom, hdepth, hheads, ?_, hEnum, ?_⟩
  · refine hpost.2.trans (adjacencyMemory_congr _ _ _ _ _ _ _ edge _ ?_)
    intro i hi
    have hlt : edge i < G.m := by
      rw [hget i hi]
      exact hindex _ (List.getElem_mem hi)
    rw [← hdecode]
    simp only [decodedTree, Function.comp_apply, ite_eq_left hlt]
    exact ⟨rfl, rfl⟩
  · intro i hi
    have he := (hEnum _).2 ⟨i, hi, rfl⟩
    obtain ⟨ht, hh⟩ := hT.1 _ he
    exact ⟨(hV _).1 ht, (hV _).1 hh, isForest_no_selfLoop hT he⟩
  · intro i hi j hj he
    rw [hget i hi, hget j hj] at he
    exact (hnodup.getElem_inj_iff (hi := hi) (hj := hj)).1 he

/-- Adjacency construction keeps the earlier tables and the suffix
after the last incidence record, including the packed numeric arrays
when placed beyond the reserved record space. -/
theorem selectedAdjacency_frame {w : ℕ} {G : IndexedGraph}
    {mem out : ℕ → ℕ} {args : List ℕ} {ret : ℕ} (kept : List ℕ)
    (selected tails heads adj records : ℕ)
    (hv : G.Valid) (hindex : ∀ e ∈ kept, e < G.m)
    (halloc : adj + G.n ≤ records)
    (hpost : (selectedAdjacencyContract w G kept selected tails heads adj records).post
      args mem ret out) :
    ∀ a, a < adj ∨ records + 6 * kept.length ≤ a → out a = mem a := by
  intro a ha
  rw [hpost.2]
  rcases ha with ha | ha
  · exact originalTreeAdjacencyMemory_prefix _ _ _ _ _ _
      ((Nat.le_add_right adj G.n).trans halloc) _ _ ha
  · refine originalTreeAdjacencyMemory_suffix _ _ _ _ _ _ _ halloc _ ?_ _ ha
    intro i hi
    have he : kept.getD i 0 = kept[i] := by simp [hi]
    simp only [Function.comp_apply, he]
    exact hv.2 _ (hindex _ (List.getElem_mem hi))

/-- A compact LSST can be traversed from vertex zero whenever the
indexed input is valid. -/
theorem indexedLSST_rooted_zero {G : IndexedGraph} {T : MGraph} {ℓ v : ℕ → ℝ} {gamma : ℝ}
    (hG : G.Valid) (htree : IsLSST G.toMGraph ℓ v gamma T) : IsRootedTree T 0 := by
  have hV := htree.1.2.1
  refine ⟨?_, ?_⟩
  · rw [hV]
    exact htree.1
  · rw [hV]
    exact Finset.mem_range.mpr hG.1

/-- The compact representative graph of a connected input has the
connectivity and valid indices required by the tree traversal. Its
selected LSST can use compact vertex zero as the root. -/
theorem representativeLSST_traversalBounds {G T : MGraph} {ℓ v : ℕ → ℝ} {gamma : ℝ}
    (hG : G.IsValid) (hconn : ∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b) :
    let H := representativeGraph G ℓ
    let I := indexedGraph H
    H.V.Nonempty → IsLSST I.toMGraph (ℓ ∘ edgeName H) v gamma T →
    I.Valid ∧
      (∀ a ∈ I.toMGraph.V, ∀ b ∈ I.toMGraph.V, I.toMGraph.Connected a b) ∧
      IsRootedTree T 0 ∧ (∀ x, x ∈ T.V ↔ x < I.n) ∧ (∀ e ∈ T.E, e < I.m) := by
  intro H I hne htree
  have hv : I.Valid := indexedGraph_valid (representativeGraph_valid G ℓ) hne
  have hsub := representativeGraph_subgraph hG ℓ
  have hHConn : ∀ a ∈ H.V, ∀ b ∈ H.V, H.Connected a b :=
    fun a ha b hb => representativeGraph_connected ℓ (hconn a (hsub.1 ha) b (hsub.1 hb))
  have hIConn := indexedGraph_connected hHConn
  have he := connectedLSST_edges_subset (IndexedGraph.toMGraph_isValid hv) hIConn htree
  refine ⟨hv, hIConn, indexedLSST_rooted_zero hv htree, ?_, ?_⟩
  · intro x
    rw [htree.1.2.1]
    exact Finset.mem_range
  · intro e hem
    exact Finset.mem_range.mp (he hem)

/-- The capacity for rounded stretch also accommodates all root
distances. Every tree edge is a compact input edge. -/
theorem selectedRootDistances_fit {G : IndexedGraph} {T : MGraph} {r h L P : ℕ}
    (len : ℕ → ℤ) (B : ℕ) (htree : IsRootedTree T r)
    (hindex : ∀ e ∈ T.E, e < G.m)
    (hLen : ∀ i < G.m, 0 < len i ∧ len i ≤ (B : ℤ))
    (hCap : 2 * ((2 * (T.V.card : ℤ) * B + B) * (2 : ℤ)^P) < (capacity h L : ℤ)) :
    ∀ x ∈ T.V, Fits h L (rootDistanceNumerator T r len x) := by
  have hb : 0 ≤ (B : ℤ) := Int.natCast_nonneg _
  have hv : 0 ≤ (T.V.card : ℤ) := Int.natCast_nonneg _
  let bound : ℤ := 2 * (T.V.card : ℤ) * B
  have hn : 0 ≤ bound := by dsimp [bound]; positivity
  have hp : 1 ≤ (2 : ℤ)^P := one_le_pow₀ (by decide)
  have hmul : bound + B ≤ (bound + B) * (2 : ℤ)^P := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (add_nonneg hn hb)
  have hcap' : bound < (capacity h L : ℤ) := by
    change 2 * ((bound + B) * (2 : ℤ)^P) < (capacity h L : ℤ) at hCap
    omega
  have hnat : 2 * T.V.card * B < capacity h L := by
    dsimp [bound] at hcap'
    exact_mod_cast hcap'
  intro x hx
  exact rootDistanceNumerator_fits htree hx len B h L
    (fun e he => ⟨(hLen e (hindex e he)).1.le, (hLen e (hindex e he)).2⟩) hnat

/-- After adjacency construction, the tree-table builder can reuse the
packed lengths beyond the incidence records. The untouched zero suffix
initializes the root distance and supplies the distance workspace. -/
theorem buildTreeTables_pre_of_selected {w h Q r : ℕ} {G : IndexedGraph}
    {T : MGraph} {mem out : ℕ → ℕ} {args : List ℕ} {ret : ℕ}
    (kept : List ℕ) (len : ℕ → ℤ)
    (selected tails heads adj records parents edges depths queue levels dist lengths L heap : ℕ)
    (hv : G.Valid) (hindex : ∀ e ∈ kept, e < G.m)
    (hV : ∀ x, x ∈ T.V ↔ x < G.n) (hE : ∀ e ∈ T.E, e < G.m)
    (hpost : (selectedAdjacencyContract w G kept selected tails heads adj records).post
      args mem ret out)
    (htrav : (traverseTreeQueueContract w T r).pre [adj,parents,edges,depths,queue,r] out)
    (hw : 1 < 2^w) (hAR : adj + G.n ≤ records) (hrec : records + 6 * kept.length ≤ lengths)
    (hPE : parents + (levels + 1) * G.n ≤ edges) (hED : edges + G.n ≤ depths)
    (hDA : depths + G.n ≤ dist) (hQA : queue + G.n ≤ dist) (hEA : edges ≤ adj)
    (hLD : lengths + G.m * L ≤ dist) (hDH : dist + G.n * L ≤ heap)
    (hroom : heap + (G.n - 1) * L < 2^w)
    (hzero : ZeroFrom mem dist)
    (hLen : ∀ e ∈ T.E, Num.Valid mem (lengths + e * L) h L ∧
      Num.intVal mem (lengths + e * L) h L = len e)
    (hFit : ∀ x ∈ T.V, Num.Fits h L (rootDistanceNumerator T r len x)) :
    (buildTreeTablesContract w h Q G.m T r len).pre
      [adj,parents,edges,depths,queue,r,G.n,levels,dist,lengths,L,heap] out := by
  have hf := selectedAdjacency_frame kept selected tails heads adj records hv hindex hAR hpost
  have hlenBase : adj ≤ lengths := by omega
  have hdistBase : lengths ≤ dist := by omega
  have hz : ZeroFrom out dist := by
    intro a ha
    exact (hf a (Or.inr (hrec.trans (hdistBase.trans ha)))).trans (hzero a ha)
  refine ⟨adj,parents,edges,depths,queue,G.n,levels,dist,lengths,L,heap,rfl,hw,hV,hE,htrav,
    hPE,hDA,hED,hQA,hLD,hlenBase,hlenBase.trans hdistBase,hEA,hDH,hroom,
    (fun a ha => hz a (by omega)), ⟨Num.zeroFrom_valid hz (Nat.le_add_right _ _),
      Num.intVal_zeroFrom hz (Nat.le_add_right _ _)⟩, ?_, hFit⟩
  intro e he
  have ha (i : ℕ) : out (lengths + e * L + i) = mem (lengths + e * L + i) :=
    hf _ (Or.inr (by omega))
  obtain ⟨hvalid, hval⟩ := hLen e he
  exact ⟨fun i hi => (ha i).symm ▸ hvalid i hi,
    (Num.intVal_congr (fun i _ => ha i)).trans hval⟩

/-- After building incidence lists, packed endpoint copies and lengths
placed beyond the records still supply the stretch-query input arrays. -/
theorem stretchInputs_of_selectedAdjacency {w h L : ℕ} {G : IndexedGraph}
    {mem out : ℕ → ℕ} {args : List ℕ} {ret : ℕ}
    (kept : List ℕ) (len : ℕ → ℤ)
    (selected tails heads adj records queryTails queryHeads lengths : ℕ)
    (hv : G.Valid) (hindex : ∀ e ∈ kept, e < G.m) (hAR : adj + G.n ≤ records)
    (hpost : (selectedAdjacencyContract w G kept selected tails heads adj records).post
      args mem ret out)
    (ht : records + 6 * kept.length ≤ queryTails)
    (hh : records + 6 * kept.length ≤ queryHeads)
    (hl : records + 6 * kept.length ≤ lengths)
    (hTail : ListAt mem queryTails (List.ofFn fun i : Fin G.m => G.tail i))
    (hHead : ListAt mem queryHeads (List.ofFn fun i : Fin G.m => G.head i))
    (hLen : ∀ i < G.m, Num.Valid mem (lengths + i * L) h L ∧
      Num.intVal mem (lengths + i * L) h L = len i) :
    (∀ i < G.m, G.tail i < G.n ∧ G.head i < G.n ∧
      out (queryTails + i) = G.tail i ∧ out (queryHeads + i) = G.head i) ∧
    (∀ i < G.m, Num.Valid out (lengths + i * L) h L ∧
      Num.intVal out (lengths + i * L) h L = len i) := by
  have hf := selectedAdjacency_frame kept selected tails heads adj records hv hindex hAR hpost
  have suffix (a i : ℕ) (ha : records + 6 * kept.length ≤ a) : out (a + i) = mem (a + i) :=
    hf _ (Or.inr (ha.trans (Nat.le_add_right _ _)))
  constructor
  · intro i hi
    have hi' : i < (List.ofFn fun j : Fin G.m => G.tail j).length := by simpa using hi
    have hi'' : i < (List.ofFn fun j : Fin G.m => G.head j).length := by simpa using hi
    obtain ⟨hut, huh⟩ := hv.2 i hi
    refine ⟨hut, huh, (suffix _ _ ht).trans ?_, (suffix _ _ hh).trans ?_⟩
    · simpa using hTail i hi'
    · simpa using hHead i hi''
  · intro i hi
    have ha (j : ℕ) : out (lengths + i * L + j) = mem (lengths + i * L + j) :=
      suffix _ _ (hl.trans (Nat.le_add_right _ _))
    obtain ⟨hvalid, hval⟩ := hLen i hi
    exact ⟨fun j hj => (ha j).symm ▸ hvalid j hj,
      (Num.intVal_congr (fun j _ => ha j)).trans hval⟩

/-- Supply the rooted stretch call with the preserved compact arrays and
the bounds on edge length and stretch precision. -/
theorem treeStretchRound_pre_of_selectedInputs {w h Q r : ℕ} {G : IndexedGraph}
    {T : MGraph} {out : ℕ → ℕ} (len : ℕ → ℤ)
    (adj parents edges depths queue levels dist lengths L heap tails heads P B : ℕ)
    (hTables : (buildTreeTablesContract w h Q G.m T r len).pre
      [adj,parents,edges,depths,queue,r,G.n,levels,dist,lengths,L,heap] out)
    (hw : 2 < 2^w) (hV : ∀ x, x ∈ T.V ↔ x < G.n)
    (hE : ∀ e ∈ T.E, e < G.m)
    (hn : G.n ≤ 2^(levels+1)) (hRows : levels+1 < 2^w)
    (hParents : parents+(levels+1)*G.n ≤ heap) (hDepths : depths+G.n ≤ heap)
    (hDist : dist+G.n*L ≤ heap)
    (hTails : adj ≤ tails ∧ tails+G.m ≤ dist)
    (hHeads : adj ≤ heads ∧ heads+G.m ≤ dist)
    (hLengths : adj ≤ lengths ∧ lengths+G.m*L ≤ dist)
    (hRoom : heap+(G.n-1)*L+G.m*edgeStretchSpace L < 2^w)
    (hEnds : ∀ i < G.m, G.tail i < G.n ∧ G.head i < G.n ∧
      out (tails+i) = G.tail i ∧ out (heads+i) = G.head i)
    (hLen : ∀ i < G.m, Num.Valid out (lengths+i*L) h L ∧
      Num.intVal out (lengths+i*L) h L = len i)
    (hLenBounds : ∀ i < G.m, 0 < len i ∧ len i ≤ (B : ℤ))
    (hCap : 2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (Num.capacity h L : ℤ)) :
    (treeStretchRoundContract w h Q G.toMGraph T r len).pre
      [adj,parents,edges,depths,queue,r,G.n,levels,dist,lengths,L,heap,tails,heads,P,G.m] out := by
  simp only [treeStretchRoundContract, IndexedGraph.toMGraph_m]
  refine ⟨adj,parents,edges,depths,queue,G.n,levels,dist,lengths,L,heap,tails,heads,P,B,
    rfl,hTables,hw,hV,hn,hParents,hDepths,hDist,hTails,hHeads,hLengths,hRoom,hRows,
    hEnds,?_,?_,hCap⟩
  · intro i hi
    obtain ⟨hvalid, hval⟩ := hLen i hi
    exact ⟨hvalid, hval, hLenBounds i hi⟩
  · intro e he
    obtain ⟨hp, hb⟩ := hLenBounds e (hE e he)
    exact ⟨hp.le, hb⟩

/-- The adjacency pass preserves the denominator and old weight blocks
when they follow the incidence records and precede the distance table. -/
theorem stretchWeightRound_pre_of_selectedAdjacency {w h Q r : ℕ} {G : IndexedGraph}
    {T H : MGraph} {mem out : ℕ → ℕ} {args : List ℕ} {ret : ℕ}
    (kept : List ℕ) (len : ℕ → ℤ)
    (selected adjTails adjHeads adj records parents edges depths queue levels dist
      lengths L heap tails heads P old stride denom j : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hv : G.Valid) (hindex : ∀ e ∈ kept, e < G.m)
    (hAR : adj + G.n ≤ records)
    (hpost : (selectedAdjacencyContract w G kept selected adjTails adjHeads adj records).post
      args mem ret out)
    (hstretch : (treeStretchRoundContract w h Q G.toMGraph T r len).pre
      [adj,parents,edges,depths,queue,r,G.n,levels,dist,lengths,L,heap,tails,heads,P,G.m] out)
    (hOld : ∀ i < H.m, records + 6 * kept.length ≤ old + i * stride ∧
      old+i*stride+L ≤ dist)
    (hDen : records + 6 * kept.length ≤ denom ∧ denom+L ≤ dist)
    (hDenVal : Valid mem denom h L ∧ intVal mem denom h L = scale*(2 : ℤ)^P)
    (hWeights : ∀ i < H.m, Valid mem (old+i*stride) h L ∧
      fixVal mem (old+i*stride) h L P = weights P (scale : ℝ) query j (edgeName H i)) :
    (stretchWeightRoundContract w h Q G.toMGraph T H r len adj parents edges depths queue
      G.n levels dist lengths L heap tails heads P old stride denom j scale query).pre
      [adj,parents,edges,depths,queue,r,G.n,levels,dist,lengths,L,heap,tails,heads,P,G.m,
        old,stride,denom,edgeStretchSpace L] out := by
  have hf := selectedAdjacency_frame kept selected adjTails adjHeads adj records hv hindex hAR hpost
  have hbase : adj ≤ records + 6 * kept.length := by omega
  have block (a : ℕ) (ha : records + 6 * kept.length ≤ a) (i : ℕ) :
      out (a+i) = mem (a+i) := hf _ (Or.inr (ha.trans (Nat.le_add_right _ _)))
  simp only [stretchWeightRoundContract, IndexedGraph.toMGraph_m]
  refine ⟨True.intro, hstretch, fun i hi => ⟨hbase.trans (hOld i hi).1, (hOld i hi).2⟩,
    ⟨hbase.trans hDen.1, hDen.2⟩, ?_, ?_⟩
  · exact ⟨fun i hi => (block denom hDen.1 i).symm ▸ hDenVal.1 i hi,
      (intVal_congr (fun i _ => block denom hDen.1 i)).trans hDenVal.2⟩
  · intro i hi
    obtain ⟨hvalid, hvalue⟩ := hWeights i hi
    have he := block (old + i * stride) (hOld i hi).1
    refine ⟨fun k hk => (he k).symm ▸ hvalid k hk, ?_⟩
    change (intVal out (old+i*stride) h L : ℝ) / (2 : ℝ)^P = _
    rw [intVal_congr (fun k _ => he k)]
    exact hvalue

/-- The full numeric call precondition follows from the selected
incidences, preserved packed inputs, and the round's allocation bounds. -/
theorem selectedNumeric_pre {w h Q : ℕ} {G : IndexedGraph} {T H : MGraph}
    {mem out : ℕ → ℕ} {args : List ℕ} {ret : ℕ}
    (kept : List ℕ) (len : ℕ → ℤ)
    (selected adjTails adjHeads adj records parents edges depths queue floor levels dist
      lengths L heap tails heads P old stride denom j B : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hv : G.Valid) (hroot : IsRootedTree T 0)
    (hdecode : decodedTree G.n G.m G.tail G.head kept [] = T)
    (hV : ∀ x, x ∈ T.V ↔ x < G.n) (hE : ∀ e ∈ T.E, e < G.m)
    (hnodup : kept.Nodup)
    (hpost : (selectedAdjacencyContract w G kept selected adjTails adjHeads adj records).post
      args mem ret out)
    (hw : 2 < 2^w) (hAR : adj + G.n ≤ records)
    (hRecT : records + 6 * kept.length ≤ tails)
    (hRecH : records + 6 * kept.length ≤ heads)
    (hRecL : records + 6 * kept.length ≤ lengths)
    (hPE : parents + (levels+1)*G.n ≤ edges) (hED : edges+G.n ≤ depths)
    (hDQ : depths+G.n ≤ queue) (hQF : queue+G.n < floor) (hFA : floor ≤ adj)
    (hTL : tails+G.m ≤ dist) (hHL : heads+G.m ≤ dist)
    (hLD : lengths+G.m*L ≤ dist) (hDH : dist+G.n*L ≤ heap)
    (hRoom : heap+(G.n-1)*L+G.m*edgeStretchSpace L < 2^w)
    (hn : G.n ≤ 2^(levels+1)) (hRows : levels+1 < 2^w)
    (hzeroDepth : mem depths = 0) (hzeroAdj : ∀ x < G.n, mem (adj+x) = 0)
    (hzeroDist : ZeroFrom mem dist)
    (hTail : ListAt mem tails (List.ofFn fun i : Fin G.m => G.tail i))
    (hHead : ListAt mem heads (List.ofFn fun i : Fin G.m => G.head i))
    (hLen : ∀ i < G.m, Valid mem (lengths+i*L) h L ∧ intVal mem (lengths+i*L) h L = len i)
    (hBounds : ∀ i < G.m, 0 < len i ∧ len i ≤ (B : ℤ))
    (hCap : 2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (capacity h L : ℤ))
    (hOld : ∀ i < H.m, records + 6 * kept.length ≤ old+i*stride ∧ old+i*stride+L ≤ dist)
    (hDen : records + 6 * kept.length ≤ denom ∧ denom+L ≤ dist)
    (hDenVal : Valid mem denom h L ∧ intVal mem denom h L = scale*(2 : ℤ)^P)
    (hWeights : ∀ i < H.m, Valid mem (old+i*stride) h L ∧
      fixVal mem (old+i*stride) h L P = weights P (scale : ℝ) query j (edgeName H i)) :
    (stretchWeightRoundContract w h Q G.toMGraph T H 0 len adj parents edges depths queue
      G.n levels dist lengths L heap tails heads P old stride denom j scale query).pre
      [adj,parents,edges,depths,queue,0,G.n,levels,dist,lengths,L,heap,tails,heads,P,G.m,
        old,stride,denom,edgeStretchSpace L] out := by
  have hindex : ∀ e ∈ kept, e < G.m := by
    intro e he
    apply hE e
    rw [← hdecode]
    exact Finset.mem_union_left _ (List.mem_toFinset.mpr he)
  have hrow : G.n ≤ (levels + 1) * G.n := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have htrav := traverseTreeQueue_pre_of_selected (r := 0) kept selected adjTails adjHeads adj records
    parents edges depths queue floor hnodup hroot.isForest hindex hdecode hpost hw
    (by omega) hED hDQ hQF hFA hAR (by omega) (by simpa using hzeroDepth) hzeroAdj
  have hfit := selectedRootDistances_fit (G := G) len B hroot hE hBounds hCap
  have htable := buildTreeTables_pre_of_selected (Q := Q) kept len selected adjTails adjHeads
    adj records parents edges depths queue levels dist lengths L heap hv hindex hV hE
    hpost htrav (by omega) hAR hRecL hPE hED (by omega) (by omega) (by omega) hLD hDH
    (by omega) hzeroDist (fun e he => hLen e (hE e he)) hfit
  obtain ⟨hEnds, hLengths⟩ := stretchInputs_of_selectedAdjacency kept len selected adjTails
    adjHeads adj records tails heads lengths hv hindex hAR hpost hRecT hRecH hRecL hTail hHead hLen
  have hstretch := treeStretchRound_pre_of_selectedInputs len adj parents edges depths queue
    levels dist lengths L heap tails heads P B htable hw hV hE hn hRows (by omega) (by omega)
    hDH ⟨by omega,hTL⟩ ⟨by omega,hHL⟩ ⟨by omega,hLD⟩ hRoom hEnds hLengths hBounds hCap
  exact stretchWeightRound_pre_of_selectedAdjacency kept len selected adjTails adjHeads adj records
    parents edges depths queue levels dist lengths L heap tails heads P old stride denom j scale query
    hv hindex hAR hpost hstretch hOld hDen hDenVal hWeights

/-- Build the adjacency lists and then query the rounded stretches.
The first sixteen arguments match the stretch routine. The remaining
arguments give the selected array, incidence records, selected count,
and the endpoint arrays used to build adjacency. -/
@[expose] def adjacencyStretchBody (adjacency stretch : ℕ) : Stmt :=
  .seq (.call 21 adjacency [.reg 16, .reg 19, .reg 20, .reg 0, .reg 17, .reg 18])
    (.seq (.call 22 stretch ((List.range 16).map Expr.reg)) (.ret (.reg 22)))

/-- The adjacency and stretch calls return the stretch routine's result
and preserve its exact memory postcondition. -/
theorem adjacencyStretch_runs {w adjacency stretch : ℕ} {p : Program} {ω : ℕ → Bool}
    {C D : Contract} (mem : ℕ → ℕ)
    (pos adj parents edges depths queue r n levels dist lengths L heap tails heads P m
      selected records count adjTails adjHeads : ℕ)
    (hc : MeetsContract w p adjacency C) (hd : MeetsContract w p stretch D) :
    let first := [selected, adjTails, adjHeads, adj, records, count]
    let second := [adj,parents,edges,depths,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,m]
    (∀ a ∈ second ++ [selected, records, count, adjTails, adjHeads], a < 2^w) →
    C.pre first mem →
    (∀ v mid, C.post first mem v mid → D.pre second mid ∧ D.cost second mid ≤ D.cost second mem) →
    (∀ mid v out, D.post second mid v out → v < 2^w) →
    ∃ o out cost, Runs w p ω (adjacencyStretchBody adjacency stretch)
      (startState (second ++ [selected, records, count, adjTails, adjHeads]) mem pos) o out cost ∧
      (∃ v mid, C.post first mem v mid ∧ D.post second mid o.value out.mem) ∧
      cost ≤ C.cost first mem + D.cost second mem + 28 := by
  intro first second hwords hpre hnext hret
  apply runs_start_le
  unfold adjacencyStretchBody
  refine runs_seq_call_le hc (vs := first) (by rfl) ?_ hpre ?_
  · dsimp [first, second] at *
    intro a ha
    apply hwords a
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro v mid pos' hp
    obtain ⟨hpre', hcost⟩ := hnext v mid hp
    refine runs_seq_call_le hd (vs := second) (by rfl) ?_ hpre' ?_
    · intro a ha
      exact hwords a (List.mem_append_left _ ha)
    · intro value out _ hout
      have hval := hret mid value out hout
      refine runs_ret_le (v := value) (by eval_expr) ⟨v, mid, hp, hout⟩ ?_
      have hsize : argsSize ((List.range 16).map Expr.reg) = 16 := by decide
      simp only [hsize, argsSize, Expr.size, startState]
      omega

/-- Compose the selected adjacency and rooted stretch contracts.
The stretch budget is independent of the contents of the incidence lists. -/
theorem selectedAdjacencyStretch_runs {w h Q adjacency stretch : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : IndexedGraph} {T : MGraph}
    (kept : List ℕ) (len : ℕ → ℤ) (mem : ℕ → ℕ)
    (pos adj parents edges depths queue r levels dist lengths L heap tails heads P
      selected records adjTails adjHeads : ℕ) :
    let first := [selected, adjTails, adjHeads, adj, records, kept.length]
    let second := [adj,parents,edges,depths,queue,r,G.n,levels,dist,lengths,L,heap,tails,heads,P,G.m]
    let C := selectedAdjacencyContract w G kept selected adjTails adjHeads adj records
    let D := treeStretchRoundContract w h Q G.toMGraph T r len
    (∀ a ∈ second ++ [selected, records, kept.length, adjTails, adjHeads], a < 2^w) →
    MeetsContract w p adjacency C → MeetsContract w p stretch D → C.pre first mem →
    (∀ mid, C.post first mem 0 mid → D.pre second mid) →
    heap + (G.n - 1) * L + G.m * edgeStretchSpace L < 2^w →
    ∃ o out cost, Runs w p ω (adjacencyStretchBody adjacency stretch)
      (startState (second ++ [selected, records, kept.length, adjTails, adjHeads]) mem pos)
      o out cost ∧
      (∃ mid, C.post first mem 0 mid ∧ D.post second mid o.value out.mem) ∧
      cost ≤ 112 * kept.length + 38 + D.cost second mem := by
  intro first second C D hwords hc hd hpre hnext hroom
  obtain ⟨o, out, cost, hr, ⟨ret, mid, hp, hs⟩, hcost⟩ :=
    adjacencyStretch_runs (ω := ω) mem pos adj parents edges depths queue r G.n levels dist
      lengths L heap tails heads P G.m selected records kept.length adjTails adjHeads
      hc hd hwords hpre
      (fun ret mid hp => ⟨hnext mid (hp.1 ▸ hp), le_rfl⟩)
      (fun _ v _ hp => by
        have he : v = heap + (G.n - 1) * L + G.m * edgeStretchSpace L := by
          simpa [D, second, treeStretchRoundContract, IndexedGraph.toMGraph_m] using hp.1
        exact he ▸ hroom)
  exact ⟨o, out, cost, hr, ⟨mid, hp.1 ▸ hp, hs⟩,
    le_trans hcost (by change 112 * kept.length + 10 + D.cost second mem + 28 ≤ _; omega)⟩

/-- Build the adjacency lists and then compute the stretches and next weights.
The first twenty arguments match the stretch and update routine. The remaining
arguments give the selected array, incidence records, selected count,
and the endpoint arrays used to build adjacency. -/
@[expose] def adjacencyStretchWeightBody (adjacency stretch : ℕ) : Stmt :=
  .seq (.call 25 adjacency [.reg 20, .reg 23, .reg 24, .reg 0, .reg 21, .reg 22])
    (.seq (.call 26 stretch ((List.range 20).map Expr.reg)) (.ret (.reg 26)))

/-- The adjacency call followed by the stretch and update call returns
the latter's result and preserves its memory postcondition. -/
theorem adjacencyStretchWeight_runs {w adjacency stretch : ℕ} {p : Program} {ω : ℕ → Bool}
    {C D : Contract} (mem : ℕ → ℕ)
    (pos adj parents edges depths queue r n levels dist lengths L heap tails heads P m
      old stride denom stretchStride selected records count adjTails adjHeads : ℕ)
    (hc : MeetsContract w p adjacency C) (hd : MeetsContract w p stretch D) :
    let first := [selected, adjTails, adjHeads, adj, records, count]
    let second := [adj,parents,edges,depths,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,m,old,stride,denom,stretchStride]
    (∀ a ∈ second ++ [selected, records, count, adjTails, adjHeads], a < 2^w) →
    C.pre first mem →
    (∀ v mid, C.post first mem v mid → D.pre second mid ∧ D.cost second mid ≤ D.cost second mem) →
    (∀ mid v out, D.post second mid v out → v < 2^w) →
    ∃ o out cost, Runs w p ω (adjacencyStretchWeightBody adjacency stretch)
      (startState (second ++ [selected, records, count, adjTails, adjHeads]) mem pos) o out cost ∧
      (∃ v mid, C.post first mem v mid ∧ D.post second mid o.value out.mem) ∧
      cost ≤ C.cost first mem + D.cost second mem + 32 := by
  intro first second hwords hpre hnext hret
  apply runs_start_le
  unfold adjacencyStretchWeightBody
  refine runs_seq_call_le hc (vs := first) (by rfl) ?_ hpre ?_
  · dsimp [first, second] at *
    intro a ha
    apply hwords a
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro v mid pos' hp
    obtain ⟨hpre', hcost⟩ := hnext v mid hp
    refine runs_seq_call_le hd (vs := second) (by rfl) ?_ hpre' ?_
    · intro a ha
      exact hwords a (List.mem_append_left _ ha)
    · intro value out _ hout
      have hval := hret mid value out hout
      refine runs_ret_le (v := value) (by eval_expr) ⟨v, mid, hp, hout⟩ ?_
      have hsize : argsSize ((List.range 20).map Expr.reg) = 20 := by decide
      simp only [hsize, argsSize, Expr.size, startState]
      omega

/-- Compose the selected adjacency and stretch-and-update contracts.
The stretch budget is independent of the contents of the incidence lists. -/
theorem selectedAdjacencyStretchWeight_runs {w h Q adjacency stretch : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : IndexedGraph} {T H : MGraph}
    (kept : List ℕ) (len : ℕ → ℤ) (mem : ℕ → ℕ)
    (pos adj parents edges depths queue r levels dist lengths L heap tails heads P
      old stride denom j selected records adjTails adjHeads : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ) :
    let first := [selected, adjTails, adjHeads, adj, records, kept.length]
    let second := [adj,parents,edges,depths,queue,r,G.n,levels,dist,lengths,L,heap,tails,heads,P,G.m,
      old,stride,denom,edgeStretchSpace L]
    let C := selectedAdjacencyContract w G kept selected adjTails adjHeads adj records
    let D := stretchWeightRoundContract w h Q G.toMGraph T H r len adj parents edges depths queue
      G.n levels dist lengths L heap tails heads P old stride denom j scale query
    (∀ a ∈ second ++ [selected, records, kept.length, adjTails, adjHeads], a < 2^w) →
    MeetsContract w p adjacency C → MeetsContract w p stretch D → C.pre first mem →
    (∀ mid, C.post first mem 0 mid → D.pre second mid) →
    heap + (G.n - 1) * L + G.m * edgeStretchSpace L + H.m * narrowWeightSpace L < 2^w →
    ∃ o out cost, Runs w p ω (adjacencyStretchWeightBody adjacency stretch)
      (startState (second ++ [selected, records, kept.length, adjTails, adjHeads]) mem pos)
      o out cost ∧
      (∃ mid, C.post first mem 0 mid ∧ D.post second mid o.value out.mem) ∧
      cost ≤ 112 * kept.length + 42 + D.cost second mem := by
  intro first second C D hwords hc hd hpre hnext hroom
  obtain ⟨o, out, cost, hr, ⟨ret, mid, hp, hs⟩, hcost⟩ :=
    adjacencyStretchWeight_runs (ω := ω) mem pos adj parents edges depths queue r G.n levels dist
      lengths L heap tails heads P G.m old stride denom (edgeStretchSpace L) selected records kept.length adjTails adjHeads
      hc hd hwords hpre
      (fun ret mid hp => ⟨hnext mid (hp.1 ▸ hp), le_rfl⟩)
      (fun _ v _ hp => by
        have he : v = heap + (G.n - 1) * L + G.m * edgeStretchSpace L + H.m * narrowWeightSpace L := by
          simpa [D, second, stretchWeightRoundContract, IndexedGraph.toMGraph_m] using hp.1
        exact he ▸ hroom)
  exact ⟨o, out, cost, hr, ⟨mid, hp.1 ▸ hp, hs⟩,
    le_trans hcost (by change 112 * kept.length + 10 + D.cost second mem + 32 ≤ _; omega)⟩

/-- The adjacency and numeric wrapper uses only deterministic statements. -/
theorem adjacencyStretchWeightBody_noRand (adjacency stretch : ℕ) :
    (adjacencyStretchWeightBody adjacency stretch).NoRand := by
  simp [adjacencyStretchWeightBody, Stmt.NoRand]

/-- The caller supplies the numeric inputs followed by the selected
array and incidence layout. The postcondition includes both writes. -/
@[expose] def selectedNumericContract (C D : Contract) (adjArgs numericArgs suffix : List ℕ)
    (ready : (ℕ → ℕ) → Prop) :
    Contract where
  pre args mem := args = numericArgs ++ suffix ∧ C.pre adjArgs mem ∧ ready mem
  post _ mem ret out := ∃ mid, C.post adjArgs mem 0 mid ∧ D.post numericArgs mid ret out
  cost _ mem := C.cost adjArgs mem + D.cost numericArgs mem + 32

/-- Install the selected adjacency and numeric composition as a single
procedure for a last-level round. -/
theorem selectedNumeric_meetsContract {w h Q entry adjacency stretch : ℕ}
    {p : Program} {G : IndexedGraph} {T H : MGraph}
    (kept : List ℕ) (len : ℕ → ℤ)
    (adj parents edges depths queue r levels dist lengths L heap tails heads P
      old stride denom j selected records adjTails adjHeads : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (ready : (ℕ → ℕ) → Prop)
    (hp : p.procs[entry]? = some (adjacencyStretchWeightBody adjacency stretch)) :
    let first := [selected, adjTails, adjHeads, adj, records, kept.length]
    let second := [adj,parents,edges,depths,queue,r,G.n,levels,dist,lengths,L,heap,tails,heads,P,G.m,
      old,stride,denom,edgeStretchSpace L]
    let suffix := [selected, records, kept.length, adjTails, adjHeads]
    let C := selectedAdjacencyContract w G kept selected adjTails adjHeads adj records
    let D := stretchWeightRoundContract w h Q G.toMGraph T H r len adj parents edges depths queue
      G.n levels dist lengths L heap tails heads P old stride denom j scale query
    MeetsContract w p adjacency C → MeetsContract w p stretch D →
    (∀ mem mid, C.pre first mem → ready mem → C.post first mem 0 mid → D.pre second mid) →
    heap + (G.n - 1) * L + G.m * edgeStretchSpace L + H.m * narrowWeightSpace L < 2^w →
    MeetsContract w p entry (selectedNumericContract C D first second suffix ready) := by
  intro first second suffix C D hc hd hnext hroom
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨ha, hpre, hready⟩ := hpre
  subst args
  obtain ⟨o, out, cost, hr, hs, hcost⟩ :=
    selectedAdjacencyStretchWeight_runs (ω := ω) kept len mem pos adj parents edges depths queue
      r levels dist lengths L heap tails heads P old stride denom j selected records adjTails adjHeads
      scale query hwords hc hd hpre (fun mid hm => hnext mem mid hpre hready hm) hroom
  refine ⟨o, out, cost, hr, hs, hcost.trans ?_⟩
  change 112 * kept.length + 42 + D.cost second mem ≤
    112 * kept.length + 10 + D.cost second mem + 32
  omega

/-- Bound the selected numeric cost uniformly in the returned edge
list and tree. The graph-size bound pays for both adjacency scans and
all vertex-indexed tables. -/
theorem selectedNumeric_cost_le {w h Q : ℕ} {G : IndexedGraph} {T H : MGraph}
    (kept : List ℕ) (len : ℕ → ℤ) (mem : ℕ → ℕ)
    (adj parents edges depths queue r levels dist lengths L heap tails heads P
      old stride denom j selected records adjTails adjHeads : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ) (ready : (ℕ → ℕ) → Prop)
    (hcount : kept.length ≤ G.n) (hVertices : T.V.card = G.n)
    (hEdges : T.E.card ≤ G.m) (hm : H.m = G.m) (hn : G.n ≤ 2 * G.m) :
    let first := [selected, adjTails, adjHeads, adj, records, kept.length]
    let second := [adj,parents,edges,depths,queue,r,G.n,levels,dist,lengths,L,heap,tails,heads,P,G.m,
      old,stride,denom,edgeStretchSpace L]
    let extra := [selected, records, kept.length, adjTails, adjHeads]
    let C := selectedAdjacencyContract w G kept selected adjTails adjHeads adj records
    let D := stretchWeightRoundContract w h Q G.toMGraph T H r len adj parents edges depths queue
      G.n levels dist lengths L heap tails heads P old stride denom j scale query
    (selectedNumericContract C D first second extra ready).cost (second ++ extra) mem ≤
      (110 * L + 126 * levels + edgeStretchCost L + narrowWeightCost L + 988) * (G.m + 1) := by
  intro first second extra C D
  simp only [selectedNumericContract, C, D, selectedAdjacencyContract, stretchWeightRoundContract,
    treeStretchRoundContract, second, IndexedGraph.toMGraph_m, hVertices, hm]
  change 112 * kept.length + 10 +
    (114 * T.E.card + 35 * G.n + (55 * L + 75) * (G.n - 1) + (20 * G.n + 40) * levels +
      (86 * (levels + 1) + edgeStretchCost L + 126) * G.m + 126 +
      (narrowWeightCost L + 30) * G.m + 60) + 32 ≤ _
  have hcl : (55 * L + 75) * (G.n - 1) ≤ (55 * L + 75) * (2 * G.m) :=
    Nat.mul_le_mul_left _ (by omega)
  have hlev : (20 * G.n + 40) * levels ≤ (20 * (2 * G.m) + 40) * levels :=
    Nat.mul_le_mul_right _ (by omega)
  have hkeep : kept.length ≤ 2 * G.m := hcount.trans hn
  calc
    _ ≤ 112 * (2 * G.m) + 10 +
        (114 * G.m + 35 * (2 * G.m) + (55 * L + 75) * (2 * G.m) +
          (20 * (2 * G.m) + 40) * levels +
          (86 * (levels + 1) + edgeStretchCost L + 126) * G.m + 126 +
          (narrowWeightCost L + 30) * G.m + 60) + 32 := by omega
    _ = (110 * L + 126 * levels + edgeStretchCost L + narrowWeightCost L + 800) * G.m +
          (40 * levels + 228) := by ring
    _ ≤ _ := by
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (by omega)

end MinCostFlow.LastLevelProgram
