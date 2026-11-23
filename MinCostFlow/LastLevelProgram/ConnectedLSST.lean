module

public import MinCostFlow.LastLevelProgram.TreeCall
public import MinCostFlow.LastLevelProgram.TraversalAdjacency
public import MinCostFlow.LastLevelProgram.DedupTreeEdges
import WordRAM.Memory
import WordRAM.Tactic
import MinCostFlow.LSF.Walks

/-!
# Connected LSST inputs need no bridge records

Theorem 2.2 (page 7) keeps each input edge's tree path inside the
input edge set. For connected inputs these paths already connect all
vertices, which rules out a bridge in the output tree.
-/

public section

namespace MinCostFlow.LastLevelProgram

open LSF WideWord

private theorem restrictedWalk {G T : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hw : T.IsWalk u v P) (he : walkEdges P ⊆ G.E) :
    ({ T with E := T.E ∩ G.E } : MGraph).IsWalk u v P := by
  induction hw with
  | nil u => exact .nil u
  | @cons a b x Q hx hs _ ih =>
    rw [walkEdges_cons] at he
    exact .cons (Finset.mem_inter.mpr ⟨hx, he (Finset.mem_insert_self _ _)⟩) hs
      (ih fun f hf => he (Finset.mem_insert_of_mem hf))

/-- For a connected input, the edge set of any LSST lies in the input. -/
theorem connectedLSST_edges_subset {G T : MGraph} {ℓ v : ℕ → ℝ} {γ : ℝ}
    (hvalid : G.IsValid) (hG : ∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b)
    (ht : IsLSST G ℓ v γ T) :
    T.E ⊆ G.E := by
  let R : MGraph := { T with E := T.E ∩ G.E }
  have hsub : T.IsSubgraph R := ⟨Finset.Subset.rfl, Finset.inter_subset_left,
    fun _ _ => ⟨rfl,rfl⟩⟩
  have hconn {a b : ℕ} {P : List (ℕ × Bool)} (hw : G.IsWalk a b P) : R.Connected a b := by
    induction hw with
    | nil a => exact ⟨[],.nil a⟩
    | @cons a b x Q he hs _ ih =>
      obtain ⟨hu,hv⟩ := hvalid _ he
      have hend := ht.2.2.1 x.1 he
      have hends := forestPath_isPath ht.1.1
        (ht.1.2.2 _ hu _ hv)
      have hr : R.Connected (G.tail x.1) (G.head x.1) :=
        ⟨_, restrictedWalk hends.1 hend⟩
      have hx : R.Connected (G.src x) (G.dst x) := by
        rcases x with ⟨e, _ | _⟩
        · exact connected_symm hr
        · exact hr
      exact connected_trans (hs ▸ hx) ih
  intro f hf
  have hverts := ht.1.1.1 f hf
  rw [ht.1.2.1] at hverts
  obtain ⟨P,hP⟩ := hG _ hverts.1 _ hverts.2
  obtain ⟨Q,hQ⟩ := connected_isPath (hconn hP)
  have hfPath : T.IsPath (T.tail f) (T.head f) [(f,true)] := by
    refine ⟨.cons hf rfl (.nil _),?_⟩
    simp [MGraph.walkVertices,MGraph.dst,isForest_no_selfLoop ht.1.1 hf]
  have heq := (forestPath_eq_of_isPath ht.1.1 hfPath).symm.trans
    (forestPath_eq_of_isPath ht.1.1 (isPath_of_subgraph hsub hQ))
  have hfR : f ∈ R.E := by
    rw [← heq] at hQ
    exact IsWalk_edges_mem (a := (f,true)) hQ.1 (by simp)
  exact (Finset.mem_inter.mp hfR).2

/-- The decoded tree of a connected compact graph has an empty bridge
array and every selected original edge is in range. -/
theorem connectedDecodedTree_originals {G : IndexedGraph} {ℓ v : ℕ → ℝ} {γ : ℝ}
    {originals : List ℕ} {bridges : List (ℕ × ℕ)}
    (hvalid : G.Valid) (hconn : ∀ a ∈ G.toMGraph.V, ∀ b ∈ G.toMGraph.V, G.toMGraph.Connected a b)
    (ht : IsLSST G.toMGraph ℓ v γ (decodedTree G.n G.m G.tail G.head originals bridges)) :
    bridges = [] ∧ ∀ e ∈ originals, e < G.m := by
  have hsub := connectedLSST_edges_subset (IndexedGraph.toMGraph_isValid hvalid) hconn ht
  constructor
  · cases bridges with
    | nil => rfl
    | cons b bs =>
      have he : G.m ∈ (decodedTree G.n G.m G.tail G.head originals (b::bs)).E := by
        unfold decodedTree
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨0,by simp,by simp⟩)
      have hb := hsub he
      change G.m ∈ Finset.range G.m at hb
      exact False.elim (Nat.lt_irrefl _ (Finset.mem_range.mp hb))
  · intro e he
    have hb := hsub (Finset.mem_union_left _ (List.mem_toFinset.mpr he))
    exact Finset.mem_range.mp hb

open WordRAM in
/-- The adjacency pass accepts the selected-edge array from the connected
LSST call directly. Each record uses the compact input edge index. -/
theorem connectedDecodedTree_adjacency {w insert : ℕ} {p : WordRAM.Program}
    {G : IndexedGraph} {ℓ v : ℕ → ℝ} {gamma : ℝ}
    (hp : MeetsContract w p insert (pushTreeEdgeContract w))
    (mem : ℕ → ℕ) (pos selected tails heads adj records : ℕ)
    (originals : List ℕ) (bridges : List (ℕ × ℕ))
    (hvalid : G.Valid)
    (hconn : ∀ a ∈ G.toMGraph.V, ∀ b ∈ G.toMGraph.V, G.toMGraph.Connected a b)
    (htree : IsLSST G.toMGraph ℓ v gamma (decodedTree G.n G.m G.tail G.head originals bridges))
    (hw : 6 < 2^w) (hcount : originals.length < 2^w)
    (hs : selected+originals.length ≤ adj) (ht : tails+G.m ≤ adj) (hh : heads+G.m ≤ adj)
    (ha : adj+G.n ≤ records) (hr : records+6*originals.length < 2^w)
    (hS : ListAt mem selected originals)
    (hT : ListAt mem tails (List.ofFn fun i : Fin G.m => G.tail i))
    (hH : ListAt mem heads (List.ofFn fun i : Fin G.m => G.head i)) :
    Triple w p (fun st => st = startState [selected,tails,heads,adj,records,originals.length] mem pos)
      (originalTreeAdjacency insert) (normalPost fun st =>
        let edge := fun i => originals.getD i 0
        st.mem = originalTreeAdjacencyMemory mem adj records (G.tail ∘ edge) (G.head ∘ edge)
          edge originals.length) (fun _ => 112*originals.length+7) := by
  obtain ⟨_,hindex⟩ := connectedDecodedTree_originals hvalid hconn htree
  apply originalTreeAdjacency_triple hp mem pos selected tails heads adj records originals.length
    G.n G.m _ _ _ hw hcount hs ht hh ha hr
  intro i hi
  let e := originals.getD i 0
  have he : e = originals[i] := by simp [e,hi]
  have hem : e ∈ originals := he.symm ▸ List.getElem_mem hi
  have hlt := hindex _ hem
  obtain ⟨hu,hv⟩ := hvalid.2 _ hlt
  have hte : e ∈ (decodedTree G.n G.m G.tail G.head originals bridges).E :=
    Finset.mem_union_left _ (List.mem_toFinset.mpr hem)
  have hne := isForest_no_selfLoop htree.1.1 hte
  change (if e < G.m then G.tail e else _) ≠ (if e < G.m then G.head e else _) at hne
  rw [ite_eq_left hlt,ite_eq_left hlt] at hne
  refine ⟨hlt,hu,hv,hne,?_,?_,?_⟩
  · exact (hS.getElem hi).trans he.symm
  · have hi' : e < (List.ofFn fun i : Fin G.m => G.tail i).length := by simpa using hlt
    change mem (tails+e) = G.tail e
    simpa using hT.getElem hi'
  · have hi' : e < (List.ofFn fun i : Fin G.m => G.head i).length := by simpa using hlt
    change mem (heads+e) = G.head e
    simpa using hH.getElem hi'

/-- Deduplication does not change the decoded tree, which uses the
set of selected original edge indices. -/
theorem decodedTree_eq_of_same_originals (G : IndexedGraph) (a b : List ℕ)
    (bridges : List (ℕ × ℕ)) (h : ∀ e, e ∈ a ↔ e ∈ b) :
    decodedTree G.n G.m G.tail G.head a bridges =
      decodedTree G.n G.m G.tail G.head b bridges := by
  have he : a.toFinset = b.toFinset := by
    ext e
    simpa only [List.mem_toFinset] using h e
  simp only [decodedTree,he]

open WordRAM in
/-- On connected LSST output, deduplicate the original array while
preserving the decoded tree and the compact input endpoint arrays. -/
theorem connectedDecodedTree_dedup {w : ℕ} {p : WordRAM.Program}
    {G : IndexedGraph} {ℓ v : ℕ → ℝ} {gamma : ℝ}
    (mem : ℕ → ℕ) (pos selected tails heads marks dest : ℕ)
    (originals : List ℕ) (bridges : List (ℕ × ℕ))
    (hvalid : G.Valid)
    (hconn : ∀ a ∈ G.toMGraph.V, ∀ b ∈ G.toMGraph.V, G.toMGraph.Connected a b)
    (htree : IsLSST G.toMGraph ℓ v gamma (decodedTree G.n G.m G.tail G.head originals bridges))
    (hw : 1 < 2^w) (hcount : originals.length+1 < 2^w)
    (hs : selected+originals.length ≤ marks) (hm : marks+G.m ≤ dest)
    (hd : dest+originals.length < 2^w)
    (ht : tails+G.m ≤ marks) (hh : heads+G.m ≤ marks)
    (hS : ListAt mem selected originals)
    (hT : ListAt mem tails (List.ofFn fun i : Fin G.m => G.tail i))
    (hH : ListAt mem heads (List.ofFn fun i : Fin G.m => G.head i))
    (hz : ∀ e < G.m, mem (marks+e) = 0) :
    Triple w p (fun st => st = startState [selected,marks,dest,originals.length] mem pos)
      dedupTreeEdges (normalPost fun st =>
        (∀ a, a < marks ∨ dest + originals.length ≤ a → st.mem a = mem a) ∧
        ListAt st.mem tails (List.ofFn fun i : Fin G.m => G.tail i) ∧
        ListAt st.mem heads (List.ofFn fun i : Fin G.m => G.head i) ∧
        ∃ kept, st.regs 4 = kept.length ∧ kept.length ≤ originals.length ∧ kept.Nodup ∧ ListAt st.mem dest kept ∧
          decodedTree G.n G.m G.tail G.head kept [] =
            decodedTree G.n G.m G.tail G.head originals bridges)
      (fun _ => 40*originals.length+10) := by
  obtain ⟨hbridges,hindex⟩ := connectedDecodedTree_originals hvalid hconn htree
  have hreads (i : ℕ) (hi : i < originals.length) :
      mem (selected+i) = originals.getD i 0 ∧ originals.getD i 0 < G.m := by
    have he : originals.getD i 0 = originals[i] := by simp [hi]
    rw [he]
    exact ⟨hS.getElem hi,hindex _ (List.getElem_mem hi)⟩
  refine (dedupTreeEdges_triple (p := p) mem pos selected marks dest G.m originals.length
    (fun i => originals.getD i 0) hw hcount hs hm hd hreads hz).conseq
    (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st h
  cases o with
  | returned => exact h
  | normal =>
    obtain ⟨hf,kept,hnum,hsize,hnodup,hkept,hmem⟩ := h
    refine ⟨hf,?_,?_,kept,hnum,hsize,hnodup,hkept,?_⟩
    · intro i hi
      have hi' : i < G.m := by simpa using hi
      rw [hf _ (Or.inl (by omega))]
      exact hT i hi
    · intro i hi
      have hi' : i < G.m := by simpa using hi
      rw [hf _ (Or.inl (by omega))]
      exact hH i hi
    · rw [hbridges]
      apply decodedTree_eq_of_same_originals
      intro e
      rw [hmem, List.mem_iff_getElem]
      constructor
      · rintro ⟨j,hj,he⟩
        refine ⟨j,hj,?_⟩
        simpa [hj] using he
      · rintro ⟨j,hj,he⟩
        exact ⟨j,hj,by simpa [hj] using he⟩

open WordRAM in
/-- Deduplicate the selected array using the count in the LSST header.
For a connected input the resulting list represents the entire tree. -/
theorem treeFromOutput_dedup {w : ℕ} {p : Program}
    (G : MGraph) (mem : ℕ → ℕ)
    (pos selected bridges header marks dest tails heads : ℕ)
    {ℓ v : ℕ → ℝ} {gamma : ℝ}
    (hvalid : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v gamma
      (treeFromOutput G mem selected bridges header))
    (hw : 1 < 2^w) (hcount : mem header + 1 < 2^w)
    (hs : selected + mem header ≤ marks) (hm : marks + G.m ≤ dest)
    (hd : dest + mem header < 2^w)
    (ht : tails + G.m ≤ marks) (hh : heads + G.m ≤ marks)
    (hT : ListAt mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i))
    (hH : ListAt mem heads (List.ofFn fun i : Fin G.m => (indexedGraph G).head i))
    (hz : ∀ e < G.m, mem (marks+e) = 0) :
    Triple w p (fun st => st = startState [selected,marks,dest,mem header] mem pos)
      dedupTreeEdges (normalPost fun st =>
        (∀ a, a < marks ∨ dest + mem header ≤ a → st.mem a = mem a) ∧
        ListAt st.mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) ∧
        ListAt st.mem heads (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) ∧
        ∃ kept, st.regs 4 = kept.length ∧ kept.length ≤ mem header ∧ kept.Nodup ∧ ListAt st.mem dest kept ∧
          decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] =
            treeFromOutput G mem selected bridges header)
      (fun _ => 40 * mem header + 10) := by
  obtain ⟨edges, pairs, hlen, _, hlist, hdecode⟩ :=
    treeFromOutput_originals G mem selected bridges header
  rw [hdecode]
  rw [hdecode] at htree
  simpa only [hlen, indexedGraph] using
    connectedDecodedTree_dedup (p := p) (G := indexedGraph G) mem pos selected
      tails heads marks dest edges pairs hvalid hconn htree hw
      (by rwa [hlen]) (by rwa [hlen]) hm (by rwa [hlen]) ht hh hlist hT hH hz

open WordRAM in
/-- Return the number of selected edges after dropping repeated indices. -/
@[expose] def dedupSelectedTreeBody : Stmt := .seq dedupTreeEdges (.ret (.reg 4))

open WordRAM in
/-- The selected-edge procedure returns a duplicate-free array for the
same tree, keeps earlier memory intact, and costs linear time in the
original selection count. -/
theorem dedupSelectedTree_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (G : MGraph) (mem : ℕ → ℕ)
    (pos selected bridges header marks dest tails heads : ℕ)
    {ℓ v : ℕ → ℝ} {gamma : ℝ}
    (hvalid : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v gamma
      (treeFromOutput G mem selected bridges header))
    (hw : 1 < 2^w) (hcount : mem header + 1 < 2^w)
    (hs : selected + mem header ≤ marks) (hm : marks + G.m ≤ dest)
    (hd : dest + mem header < 2^w)
    (ht : tails + G.m ≤ marks) (hh : heads + G.m ≤ marks)
    (hT : ListAt mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i))
    (hH : ListAt mem heads (List.ofFn fun i : Fin G.m => (indexedGraph G).head i))
    (hz : ∀ e < G.m, mem (marks+e) = 0) :
    ∃ out cost kept,
      Runs w p ω dedupSelectedTreeBody (startState [selected,marks,dest,mem header] mem pos)
        (.returned kept.length) out cost ∧
      kept.length ≤ mem header ∧ kept.Nodup ∧ ListAt out.mem dest kept ∧
      decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] =
        treeFromOutput G mem selected bridges header ∧
      (∀ a, a < marks ∨ dest + mem header ≤ a → out.mem a = mem a) ∧ cost ≤ 40 * mem header + 14 := by
  have hscan := treeFromOutput_dedup (p := p) G mem pos selected bridges header marks dest
    tails heads hvalid hconn htree hw hcount hs hm hd ht hh hT hH hz
  obtain ⟨o, out, cost, hrun, hpost, hcost⟩ := hscan _ ω rfl
  cases o with
  | returned => exact False.elim hpost
  | normal =>
    obtain ⟨hframe, _, _, kept, hret, hlen, hnodup, hlist, htreeEq⟩ := hpost
    have hreturn : Runs w p ω (.ret (.reg 4)) out (.returned kept.length) out 2 := by
      apply runs_ret_iff.mpr
      have hword : kept.length < 2^w := by omega
      exact ⟨kept.length, by eval_expr, rfl, rfl, rfl⟩
    change cost ≤ 40 * mem header + 10 at hcost
    refine ⟨out, cost + 3, kept, ?_, hlen, hnodup, hlist, htreeEq, hframe, by omega⟩
    exact runs_seq_iff.mpr (Or.inr ⟨out, cost, 2, hrun, hreturn, by omega⟩)

open WordRAM in
/-- Contract for reading the selected array of a connected LSST and
writing its distinct indices to the caller's destination. -/
@[expose] def dedupSelectedTreeContract (w : ℕ) (G : MGraph)
    (ℓ v : ℕ → ℝ) (gamma : ℝ)
    (selected bridges header marks dest tails heads : ℕ) : Contract where
  pre args mem :=
    args = [selected, marks, dest, mem header] ∧
    IsLSST (indexedGraph G).toMGraph ℓ v gamma (treeFromOutput G mem selected bridges header) ∧
    mem header + 1 < 2^w ∧ selected + mem header ≤ marks ∧ marks + G.m ≤ dest ∧
    dest + mem header < 2^w ∧ tails + G.m ≤ marks ∧ heads + G.m ≤ marks ∧
    ListAt mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) ∧
    ListAt mem heads (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) ∧
    ∀ e < G.m, mem (marks + e) = 0
  post _ mem count out :=
    ∃ kept, count = kept.length ∧ count ≤ mem header ∧ kept.Nodup ∧ ListAt out dest kept ∧
      decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] =
        treeFromOutput G mem selected bridges header ∧
      ∀ a, a < marks ∨ dest + mem header ≤ a → out a = mem a
  cost _ mem := 40 * mem header + 14

open WordRAM in
/-- The installed selection procedure meets its contract on each
connected compact input. -/
theorem dedupSelectedTree_meetsContract {w b : ℕ} {p : Program}
    (G : MGraph) (ℓ v : ℕ → ℝ) (gamma : ℝ)
    (selected bridges header marks dest tails heads : ℕ)
    (hp : p.procs[b]? = some dedupSelectedTreeBody)
    (hw : 1 < 2^w) (hvalid : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b) :
    MeetsContract w p b (dedupSelectedTreeContract w G ℓ v gamma
      selected bridges header marks dest tails heads) := by
  intro args mem pos ω _ hpre
  obtain ⟨hargs, htree, hcount, hs, hm, hd, ht, hh, hT, hH, hz⟩ := hpre
  obtain ⟨out, cost, kept, hr, hlen, hnodup, hlist, htreeEq, hframe, hc⟩ :=
    dedupSelectedTree_runs (p := p) (ω := ω) G mem pos selected bridges header
      marks dest tails heads hvalid hconn htree hw hcount hs hm hd ht hh hT hH hz
  exact ⟨_, hp, .returned kept.length, out, cost, hargs.symm ▸ hr,
    ⟨kept, rfl, hlen, hnodup, hlist, htreeEq, hframe⟩, hc⟩

open WordRAM in
/-- Build incidence lists for the distinct selected edges. -/
@[expose] def selectedAdjacencyBody (insert : ℕ) : Stmt :=
  .seq (originalTreeAdjacency insert) (.ret (.const 0))

open WordRAM in
/-- Contract for the adjacency call following tree selection. -/
@[expose] def selectedAdjacencyContract (w : ℕ) (G : IndexedGraph)
    (originals : List ℕ) (selected tails heads adj records : ℕ) : Contract where
  pre args mem :=
    args = [selected, tails, heads, adj, records, originals.length] ∧
    selected + originals.length ≤ adj ∧ tails + G.m ≤ adj ∧ heads + G.m ≤ adj ∧
    adj + G.n ≤ records ∧ records + 6 * originals.length < 2^w ∧
    ListAt mem selected originals ∧
    ListAt mem tails (List.ofFn fun i : Fin G.m => G.tail i) ∧
    ListAt mem heads (List.ofFn fun i : Fin G.m => G.head i)
  post _ mem ret out :=
    let edge := fun i => originals.getD i 0
    ret = 0 ∧ out = originalTreeAdjacencyMemory mem adj records (G.tail ∘ edge)
      (G.head ∘ edge) edge originals.length
  cost _ _ := 112 * originals.length + 10

open WordRAM in
/-- The installed adjacency procedure builds both incidences of every
selected edge of the connected tree from Theorem 2.2 (page 7). -/
theorem selectedAdjacency_meetsContract {w b insert : ℕ} {p : Program}
    {G : IndexedGraph} {ℓ v : ℕ → ℝ} {gamma : ℝ}
    (originals : List ℕ) (selected tails heads adj records : ℕ)
    (hp : p.procs[b]? = some (selectedAdjacencyBody insert))
    (hi : MeetsContract w p insert (pushTreeEdgeContract w))
    (hw : 6 < 2^w) (hv : G.Valid)
    (hconn : ∀ a ∈ G.toMGraph.V, ∀ b ∈ G.toMGraph.V, G.toMGraph.Connected a b)
    (htree : IsLSST G.toMGraph ℓ v gamma (decodedTree G.n G.m G.tail G.head originals [])) :
    MeetsContract w p b (selectedAdjacencyContract w G originals selected tails heads adj records) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨rfl, hs, ht, hh, ha, hr, hS, hT, hH⟩ := hpre
  have hc := hwords originals.length (by simp)
  have hscan := connectedDecodedTree_adjacency hi mem pos selected tails heads adj records
    originals [] hv hconn htree hw hc hs ht hh ha hr hS hT hH
  apply runs_start_le
  unfold selectedAdjacencyBody
  refine runs_seq_triple_le hscan rfl ?_
  intro st hmem
  refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl, hmem⟩ ?_
  simp [selectedAdjacencyContract, Expr.size]

end MinCostFlow.LastLevelProgram
