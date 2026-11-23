module

public import MinCostFlow.LastLevelProgram.RepresentativeGraph
public import MinCostFlow.LastLevelProgram.NameTree
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
import Mathlib.Data.List.Nodup
import WordRAM.Tactic

/-!
# Naming the selected tree edges for the branch graph

Definition 5.8 (pages 19–20) retains the representative tree edges
and uses the original vertex set. The selected compact indices give
the edge records for constructing that graph.
-/

public section

namespace MinCostFlow.LastLevelProgram

open SparseCore WordRAM DynSpanner.Program

/-- The selected compact edges describe exactly the named branch edge
set. Each record uses the endpoints stored in the original graph. -/
theorem selectedBranch_edgeRecords {G T : MGraph} (ℓ : ℕ → ℝ) (kept : List ℕ)
    (hn : kept.Nodup) (hset : kept.toFinset = T.E)
    (hindex : ∀ i ∈ T.E, i < (representativeGraph G ℓ).m) :
    let H := representativeGraph G ℓ
    let E := (restoreTreeNames H T).E ∩ H.E
    let triples := kept.map fun i => (edgeName H i, G.tail (edgeName H i), G.head (edgeName H i))
    (triples.map Prod.fst).Nodup ∧
      (∀ t ∈ triples, t.1 ∈ E ∧ t.2.1 = G.tail t.1 ∧ t.2.2 = G.head t.1) ∧
      (∀ e ∈ E, ∃ t ∈ triples, t.1 = e) := by
  intro H E triples
  have hlt (i : ℕ) (hi : i ∈ kept) : i < H.m :=
    hindex i (hset ▸ List.mem_toFinset.mpr hi)
  refine ⟨?_, ?_, ?_⟩
  · change ((kept.map fun i => (edgeName H i, G.tail (edgeName H i),
      G.head (edgeName H i))).map Prod.fst).Nodup
    rw [List.map_map]
    apply hn.map_on
    intro i hi j hj he
    change edgeName H i = edgeName H j at he
    exact (edgeIndex_name (hlt i hi)).symm.trans
      ((congrArg (edgeIndex H) he).trans (edgeIndex_name (hlt j hj)))
  · intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    have htree : i ∈ T.E := hset ▸ List.mem_toFinset.mpr hi
    refine ⟨Finset.mem_inter.mpr ⟨?_, edgeName_mem (hlt i hi)⟩, rfl, rfl⟩
    change edgeName H i ∈ T.E.image (treeEdgeName H)
    exact Finset.mem_image.mpr ⟨i, htree, ite_eq_left (hlt i hi)⟩
  · intro e he
    have hm : e ∈ T.E.image (treeEdgeName H) := (Finset.mem_inter.mp he).1
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    have hk : i ∈ kept := List.mem_toFinset.mp (hset.symm ▸ hi)
    exact ⟨_, List.mem_map.mpr ⟨i, hk, rfl⟩, (ite_eq_left (hindex i hi)).symm⟩

/-- The original vertex list and restored selected edge records meet
the shared graph initialization contract. Both branch graphs can point
at the same allocation because the model gives them identical edges. -/
theorem selectedBranch_graphInit_pre {w : ℕ} {G T : MGraph} (ℓ : ℕ → ℝ)
    (kept vertices : List ℕ) (mem : ℕ → ℕ) (g vCap eCap vp ep : ℕ)
    (hG : G.IsValid) (hn : kept.Nodup) (hset : kept.toFinset = T.E)
    (hindex : ∀ i ∈ T.E, i < (representativeGraph G ℓ).m)
    (hV : ∀ v, v ∈ vertices ↔ v ∈ G.V)
    (hvc : ∀ v ∈ G.V, v < vCap) (hec : ∀ e ∈ G.E, e < eCap)
    (hw : 16 ≤ 2^w) (hroom : g + dynGraphSize vCap eCap < 2^w)
    (hzero : ZeroFrom mem g)
    (hvp : vp + vertices.length ≤ g) (hep : ep + 3 * kept.length ≤ g)
    (hvAt : ListAt mem vp vertices) :
    let H := representativeGraph G ℓ
    let F : MGraph :=
      { V := G.V, E := (restoreTreeNames H T).E ∩ H.E, tail := G.tail, head := G.head }
    let triples := kept.map fun i => (edgeName H i, G.tail (edgeName H i), G.head (edgeName H i))
    (∀ i (hi : i < triples.length),
      mem (ep+3*i) = triples[i].1 ∧ mem (ep+3*i+1) = triples[i].2.1 ∧
        mem (ep+3*i+2) = triples[i].2.2) →
    (dgInitFromListsContract w vCap eCap F vertices triples).pre
      [g,vCap,eCap,vertices.length,vp,kept.length,ep] mem := by
  intro H F triples heAt
  have hsub := representativeGraph_subgraph hG ℓ
  have hEdges : F.E ⊆ G.E := fun _ he => hsub.2.1 (Finset.mem_inter.mp he).2
  have hF : F.IsValid := fun e he => hG e (hEdges he)
  have ⟨hn', htriples, hcover⟩ := selectedBranch_edgeRecords ℓ kept hn hset hindex
  exact ⟨g,vertices.length,vp,kept.length,ep,rfl,hw,hroom,hzero,hF,hvc,
    fun e he => hec e (hEdges he),rfl,hvAt,hV,fun i hi => by omega,
    (List.length_map _),hn',heAt,htriples,hcover,fun i hi => by omega⟩

/-- Restore a compact edge index and its two compact endpoint indices
through the corresponding name arrays, then write a graph record. -/
@[expose] def writeBranchEdgeRecordBody : Stmt :=
  .seq (.assign 6 (.load (.bin .add (.reg 1) (.reg 5))))
  (.seq (.assign 7 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 2) (.reg 5))))))
  (.seq (.assign 8 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 3) (.reg 5))))))
  (.seq (.store (.reg 0) (.reg 6))
  (.seq (.store (.bin .add (.reg 0) (.const 1)) (.reg 7))
  (.seq (.store (.bin .add (.reg 0) (.const 2)) (.reg 8)) (.ret (.const 0)))))))

/-- Write one restored edge record and preserve all other cells. -/
theorem writeBranchEdgeRecord_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos dst names tails heads vertices i u v e a b : ℕ)
    (_hw : 2 < 2^w) (_hDst : dst+2 < 2^w)
    (_hn : names+i < dst) (_ht : tails+i < dst) (_hh : heads+i < dst)
    (_hu : vertices+u < dst) (_hv : vertices+v < dst)
    (_he : e < 2^w) (_ha : a < 2^w) (_hb : b < 2^w)
    (hname : mem (names+i) = e) (htail : mem (tails+i) = u) (hhead : mem (heads+i) = v)
    (huName : mem (vertices+u) = a) (hvName : mem (vertices+v) = b) :
    ∃ o out cost, Runs w p ω writeBranchEdgeRecordBody
      (startState [dst,names,tails,heads,vertices,i] mem pos) o out cost ∧
      (o.value = 0 ∧ out.mem = Function.update
        (Function.update (Function.update mem dst e) (dst+1) a) (dst+2) b) ∧ cost ≤ 48 := by
  apply runs_start_le
  unfold writeBranchEdgeRecordBody
  have htailAddr : vertices + (startState [dst,names,tails,heads,vertices,i] mem pos).mem
      (tails+i) < 2^w := by
    change vertices + mem (tails+i) < 2^w
    rw [htail]
    omega
  have hheadAddr : vertices + (startState [dst,names,tails,heads,vertices,i] mem pos).mem
      (heads+i) < 2^w := by
    change vertices + mem (heads+i) < 2^w
    rw [hhead]
    omega
  wram_run
  · simp [startState, hname, htail, hhead, huName, hvName, Outcome.value]
  · wram_cost

/-- Contract for restoring and writing one selected compact edge. -/
@[expose] def writeBranchEdgeRecordContract (w : ℕ) : Contract where
  pre args mem := ∃ dst names tails heads vertices i,
    args = [dst,names,tails,heads,vertices,i] ∧
    2 < 2^w ∧ dst+2 < 2^w ∧ names+i < dst ∧ tails+i < dst ∧ heads+i < dst ∧
    vertices+mem (tails+i) < dst ∧ vertices+mem (heads+i) < dst ∧
    mem (names+i) < 2^w ∧ mem (vertices+mem (tails+i)) < 2^w ∧
    mem (vertices+mem (heads+i)) < 2^w
  post args mem ret out := ∃ dst names tails heads vertices i,
    args = [dst,names,tails,heads,vertices,i] ∧ ret = 0 ∧
    out = Function.update
      (Function.update (Function.update mem dst (mem (names+i)))
        (dst+1) (mem (vertices+mem (tails+i))))
      (dst+2) (mem (vertices+mem (heads+i)))
  cost _ _ := 48

/-- The installed record writer meets its contract for every tape. -/
theorem writeBranchEdgeRecord_meetsContract {w entry : ℕ} {p : Program}
    (hp : p.procs[entry]? = some writeBranchEdgeRecordBody) :
    MeetsContract w p entry (writeBranchEdgeRecordContract w) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _ hpre
  obtain ⟨dst,names,tails,heads,vertices,i,rfl,hw,hd,hn,ht,hh,hu,hv,he,ha,hb⟩ := hpre
  obtain ⟨o,out,cost,hr,hpost,hcost⟩ :=
    writeBranchEdgeRecord_runs (p := p) (ω := ω) mem pos dst names tails heads vertices i
      _ _ _ _ _ hw hd hn ht hh hu hv he ha hb rfl rfl rfl rfl rfl
  exact ⟨o,out,cost,hr,⟨dst,names,tails,heads,vertices,i,rfl,hpost⟩,hcost⟩

/-- Each scan step reads a retained compact index and writes its three
restored words at the current record slot. -/
@[expose] def branchEdgeRecordsArgs : List Expr :=
  [.bin .add (.reg 0) (.bin .mul (.const 3) (.reg 7)), .reg 1, .reg 2, .reg 3, .reg 4,
    .load (.bin .add (.reg 5) (.reg 7))]

/-- Restore all selected edge records in their retained order. -/
@[expose] def branchEdgeRecordsLoop (entry : ℕ) : Stmt :=
  forRange 7 (.const 0) (.reg 6) (.call 8 entry branchEdgeRecordsArgs)

/-- The retained edge records are restored in a single pass. All
input words lie below the output array. -/
theorem branchEdgeRecords_triple {w entry : ℕ} {p : Program}
    (hp : MeetsContract w p entry (writeBranchEdgeRecordContract w))
    (mem : ℕ → ℕ) (pos dst names tails heads vertices selected count : ℕ)
    (edge : ℕ → ℕ) (hw : 3 < 2^w)
    (hwords : ∀ a ∈ [dst,names,tails,heads,vertices,selected,count], a < 2^w)
    (hroom : dst+3*count < 2^w)
    (hinput : ∀ j < count,
      mem (selected+j) = edge j ∧ selected+j < dst ∧ edge j < 2^w ∧
      names+edge j < dst ∧ tails+edge j < dst ∧ heads+edge j < dst ∧
      vertices+mem (tails+edge j) < dst ∧ vertices+mem (heads+edge j) < dst ∧
      mem (names+edge j) < 2^w ∧ mem (vertices+mem (tails+edge j)) < 2^w ∧
      mem (vertices+mem (heads+edge j)) < 2^w) :
    Triple w p (fun st => st = startState [dst,names,tails,heads,vertices,selected,count] mem pos)
      (branchEdgeRecordsLoop entry) (normalPost fun st =>
        (∀ j < count, st.mem (dst+3*j) = mem (names+edge j) ∧
          st.mem (dst+3*j+1) = mem (vertices+mem (tails+edge j)) ∧
          st.mem (dst+3*j+2) = mem (vertices+mem (heads+edge j))) ∧
        ∀ a, a < dst ∨ dst+3*count ≤ a → st.mem a = mem a)
      (fun _ => 73*count+7) := by
  let Inv := fun j (st : State) =>
    st.regs 0 = dst ∧ st.regs 1 = names ∧ st.regs 2 = tails ∧ st.regs 3 = heads ∧
    st.regs 4 = vertices ∧ st.regs 5 = selected ∧ st.regs 6 = count ∧ st.regs 7 = j ∧
    (∀ k < j, st.mem (dst+3*k) = mem (names+edge k) ∧
      st.mem (dst+3*k+1) = mem (vertices+mem (tails+edge k)) ∧
      st.mem (dst+3*k+2) = mem (vertices+mem (heads+edge k))) ∧
    ∀ a, a < dst ∨ dst+3*j ≤ a → st.mem a = mem a
  have hc := hwords count (by simp)
  have loop := Triple.forRange_const (p := p) (r := 7) (lo := .const 0) (hi := .reg 6)
    (body := .call 8 entry branchEdgeRecordsArgs) (Inv := Inv)
    (P := fun st => st = startState [dst,names,tails,heads,vertices,selected,count] mem pos)
    64 0 count (Nat.zero_le _) (by omega) (fun _ => hc)
    (fun st hst => by
      subst st
      exact ⟨by eval_expr, by simp [Inv,startState]⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.1)
    (fun i st _ _ h => by
      have hreg := h.2.2.2.2.2.2.1
      eval_expr)
    (fun j _ hj st ω ⟨h0,h1,h2,h3,h4,h5,h6,h7,hdone,hframe⟩ => by
      obtain ⟨hsel,hsa,hei,hni,hti,hhi,hu,hv,he,hU,hV⟩ := hinput j hj
      let base := dst+3*j
      have hbase : base+2 < 2^w := by dsimp [base]; omega
      have hmul : 3*j < 2^w := by omega
      have hread : st.mem (selected+j) = edge j := (hframe _ (Or.inl hsa)).trans hsel
      have hsaW : selected+j < 2^w := by omega
      have hn : st.mem (names+edge j) = mem (names+edge j) := hframe _ (Or.inl hni)
      have ht : st.mem (tails+edge j) = mem (tails+edge j) := hframe _ (Or.inl hti)
      have hh : st.mem (heads+edge j) = mem (heads+edge j) := hframe _ (Or.inl hhi)
      have htu : st.mem (vertices+st.mem (tails+edge j)) = mem (vertices+mem (tails+edge j)) := by
        rw [ht]
        exact hframe _ (Or.inl hu)
      have hhv : st.mem (vertices+st.mem (heads+edge j)) = mem (vertices+mem (heads+edge j)) := by
        rw [hh]
        exact hframe _ (Or.inl hv)
      have hargs : evalArgs w st branchEdgeRecordsArgs =
          some [base,names,tails,heads,vertices,edge j] := by
        unfold branchEdgeRecordsArgs
        dsimp [base]
        eval_expr
      have hwords' : ∀ a ∈ [base,names,tails,heads,vertices,edge j], a < 2^w := by
        intro a ha
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals omega
      have hpre : (writeBranchEdgeRecordContract w).pre [base,names,tails,heads,vertices,edge j] st.mem := by
        refine ⟨base,names,tails,heads,vertices,edge j,rfl,by omega,hbase,?_,?_,?_,?_,?_,?_,?_,?_⟩
        · dsimp [base]; omega
        · dsimp [base]; omega
        · dsimp [base]; omega
        · rw [ht]; dsimp [base]; omega
        · rw [hh]; dsimp [base]; omega
        · rwa [hn]
        · rwa [htu]
        · rwa [hhv]
      obtain ⟨out,cost,ret,hr,hpost,_,hregs,hcost⟩ :=
        runs_call_of_meetsContract (r := 8) hp hargs hwords' hpre ω
      obtain ⟨d,n,t,h,v,i,heq,_,hout⟩ := hpost
      simp only [List.cons.injEq,and_true] at heq
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
      rw [hn,htu,hhv] at hout
      refine ⟨.normal,out,cost,hr,⟨⟨(hregs 0 (by decide)).trans h0,
        (hregs 1 (by decide)).trans h1,(hregs 2 (by decide)).trans h2,
        (hregs 3 (by decide)).trans h3,(hregs 4 (by decide)).trans h4,
        (hregs 5 (by decide)).trans h5,(hregs 6 (by decide)).trans h6,by simp,?_,?_⟩,
        (hregs 7 (by decide)).trans h7⟩,?_⟩
      · intro k hk
        change out.mem (dst+3*k) = _ ∧ out.mem (dst+3*k+1) = _ ∧ out.mem (dst+3*k+2) = _
        rw [hout]
        by_cases he : k = j
        · subst k
          dsimp [base]
          refine ⟨?_,?_,Function.update_self ..⟩
          · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),Function.update_self]
          · rw [Function.update_of_ne (by omega),Function.update_self]
        · have hk' : k < j := by omega
          obtain ⟨hE,hA,hB⟩ := hdone k hk'
          dsimp [base]
          refine ⟨?_,?_,?_⟩
          all_goals rwa [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
      · intro a ha
        change out.mem a = mem a
        rw [hout]
        dsimp [base]
        rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
        exact hframe a (ha.imp_right (by omega))
      · change cost ≤ 64
        simp [writeBranchEdgeRecordContract,branchEdgeRecordsArgs,argsSize,Expr.size] at hcost
        omega)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned => exact h
    | normal => exact h.2.2.2.2.2.2.2.2
  · intro _ _
    simp [Expr.size_const,Expr.size_reg,Nat.mul_comm]

/-- The record scan on the packed representative graph produces the
exact triples required by the named branch graph initializer. -/
theorem branchEdgeRecords_model {w entry : ℕ} {p : Program} {G : MGraph}
    (ℓ : ℕ → ℝ) (kept : List ℕ)
    (hp : MeetsContract w p entry (writeBranchEdgeRecordContract w))
    (mem : ℕ → ℕ) (pos dst names tails heads vertices selected : ℕ)
    (hw : 3 < 2^w) (hG : G.IsValid)
    (hwords : ∀ a ∈ [dst,names,tails,heads,vertices,selected,kept.length], a < 2^w)
    (hroom : dst+3*kept.length < 2^w)
    (hs : selected+kept.length ≤ dst) (hselected : ListAt mem selected kept)
    (hE : ∀ i ∈ kept, i < (representativeGraph G ℓ).m)
    (hVwords : ∀ v ∈ G.V, v < 2^w) (hEwords : ∀ e ∈ G.E, e < 2^w) :
    let H := representativeGraph G ℓ
    let I := indexedGraph H
    let triples := kept.map fun i => (edgeName H i, G.tail (edgeName H i), G.head (edgeName H i))
    H.m < 2^w → names+H.m ≤ dst → tails+H.m ≤ dst → heads+H.m ≤ dst → vertices+H.n ≤ dst →
    (∀ i < H.m, mem (names+i) = edgeName H i ∧ mem (tails+i) = I.tail i ∧ mem (heads+i) = I.head i) →
    (∀ v < H.n, mem (vertices+v) = vertexName H v) →
    Triple w p (fun st => st = startState [dst,names,tails,heads,vertices,selected,kept.length] mem pos)
      (branchEdgeRecordsLoop entry) (normalPost fun st =>
        (∀ j (hj : j < triples.length),
          st.mem (dst+3*j) = triples[j].1 ∧ st.mem (dst+3*j+1) = triples[j].2.1 ∧
            st.mem (dst+3*j+2) = triples[j].2.2) ∧
        ∀ a, a < dst ∨ dst+3*kept.length ≤ a → st.mem a = mem a)
      (fun _ => 73*kept.length+7) := by
  intro H I triples hm hn ht hh hv hpack hverts
  let edge := fun j => kept.getD j 0
  have hfit (j : ℕ) (hj : j < kept.length) : edge j < H.m := by
    have he : edge j = kept[j] := by simp [edge,hj]
    rw [he]
    exact hE _ (List.getElem_mem hj)
  have hsub := representativeGraph_subgraph hG ℓ
  have hH := representativeGraph_valid G ℓ
  have packed (i : ℕ) (hi : i < H.m) :
      mem (names+i) = edgeName H i ∧ mem (vertices+mem (tails+i)) = G.tail (edgeName H i) ∧
        mem (vertices+mem (heads+i)) = G.head (edgeName H i) ∧
        mem (tails+i) < H.n ∧ mem (heads+i) < H.n := by
    obtain ⟨he,hu,hv'⟩ := hpack i hi
    obtain ⟨hU,hV⟩ := hH _ (edgeName_mem hi)
    have ht' : I.tail i < H.n := vertexIndex_lt hU
    have hh' : I.head i < H.n := vertexIndex_lt hV
    obtain ⟨hTail,hHead⟩ := indexedGraph_endpoints hH hi
    obtain ⟨heT,heH⟩ := hsub.2.2 _ (edgeName_mem hi)
    refine ⟨he, ?_, ?_, hu ▸ ht', hv' ▸ hh'⟩
    · rw [hu, hverts _ ht', hTail, ← heT]
    · rw [hv', hverts _ hh', hHead, ← heH]
  have hrun := branchEdgeRecords_triple hp mem pos dst names tails heads vertices selected kept.length
    edge hw hwords hroom (fun j hj => by
      have he := hfit j hj
      have hd : edge j = kept[j] := by simp [edge,hj]
      obtain ⟨hN,hT,hHd,hU,hV⟩ := packed _ he
      have hLive := hsub.2.1 (edgeName_mem he)
      obtain ⟨hUlive,hVlive⟩ := hG _ hLive
      refine ⟨(hselected j hj).trans hd.symm,by omega,he.trans hm,by omega,by omega,
        by omega,by omega,by omega,?_,?_,?_⟩
      · rw [hN]; exact hEwords _ hLive
      · rw [hT]; exact hVwords _ hUlive
      · rw [hHd]; exact hVwords _ hVlive)
  refine hrun.conseq (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st ho
  cases o with
  | returned => exact ho
  | normal =>
    refine ⟨?_,ho.2⟩
    intro j hj
    have hk : j < kept.length := by simpa [triples] using hj
    obtain ⟨h0,h1,h2⟩ := ho.1 j hk
    obtain ⟨hN,hT,hHd,_,_⟩ := packed _ (hfit j hk)
    simpa [triples, edge, hk] using And.intro (h0.trans hN)
      (And.intro (h1.trans hT) (h2.trans hHd))

/-- Callable form of the retained edge record scan. -/
@[expose] def branchEdgeRecordsBody (write : ℕ) : Stmt :=
  .seq (branchEdgeRecordsLoop write) (.ret (.const 0))

/-- The record scan can be invoked as a procedure before the graph
initializer. Its postcondition supplies the initializer's triples. -/
theorem branchEdgeRecords_meetsContract {w entry write : ℕ} {p : Program} {G : MGraph}
    (ℓ : ℕ → ℝ) (kept : List ℕ) (dst names tails heads vertices selected : ℕ)
    (hp : p.procs[entry]? = some (branchEdgeRecordsBody write))
    (hwrite : MeetsContract w p write (writeBranchEdgeRecordContract w))
    (hw : 3 < 2^w) (hG : G.IsValid)
    (hE : ∀ i ∈ kept, i < (representativeGraph G ℓ).m)
    (hVwords : ∀ v ∈ G.V, v < 2^w) (hEwords : ∀ e ∈ G.E, e < 2^w) :
    let H := representativeGraph G ℓ
    let I := indexedGraph H
    let triples := kept.map fun i => (edgeName H i, G.tail (edgeName H i), G.head (edgeName H i))
    H.m < 2^w → names+H.m ≤ dst → tails+H.m ≤ dst → heads+H.m ≤ dst → vertices+H.n ≤ dst →
    dst+3*kept.length < 2^w → selected+kept.length ≤ dst →
    MeetsContract w p entry {
      pre := fun args mem => args = [dst,names,tails,heads,vertices,selected,kept.length] ∧
        ListAt mem selected kept ∧
        (∀ i < H.m, mem (names+i) = edgeName H i ∧ mem (tails+i) = I.tail i ∧
          mem (heads+i) = I.head i) ∧ (∀ v < H.n, mem (vertices+v) = vertexName H v)
      post := fun _ mem ret out => ret = 0 ∧
        (∀ j (hj : j < triples.length),
          out (dst+3*j) = triples[j].1 ∧ out (dst+3*j+1) = triples[j].2.1 ∧
            out (dst+3*j+2) = triples[j].2.2) ∧
        ∀ a, a < dst ∨ dst+3*kept.length ≤ a → out a = mem a
      cost := fun _ _ => 73*kept.length+10 } := by
  intro H I triples hm hn ht hh hv hroom hs
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨rfl, hsel, hpack, hverts⟩ := hpre
  have hscan := branchEdgeRecords_model ℓ kept hwrite mem pos dst names tails heads vertices
    selected hw hG hwords hroom hs hsel hE hVwords hEwords hm hn ht hh hv hpack hverts
  apply runs_start_le
  unfold branchEdgeRecordsBody
  refine runs_seq_triple_le hscan rfl ?_
  intro st hpost
  refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl,hpost⟩ ?_
  simp [Expr.size]

/-- The output of the restored-record scan supplies the initializer
precondition. Its frame preserves both the vertex records and the
zero-initialized graph allocation. -/
theorem selectedBranch_graphInit_pre_of_scan {w : ℕ} {G T : MGraph} (ℓ : ℕ → ℝ)
    (kept vertices : List ℕ) (mem out : ℕ → ℕ) (g vCap eCap vp ep : ℕ)
    (hG : G.IsValid) (hn : kept.Nodup) (hset : kept.toFinset = T.E)
    (hindex : ∀ i ∈ T.E, i < (representativeGraph G ℓ).m)
    (hV : ∀ v, v ∈ vertices ↔ v ∈ G.V)
    (hvc : ∀ v ∈ G.V, v < vCap) (hec : ∀ e ∈ G.E, e < eCap)
    (hw : 16 ≤ 2^w) (hroom : g + dynGraphSize vCap eCap < 2^w)
    (hzero : ZeroFrom mem g)
    (hvp : vp + vertices.length ≤ ep) (hep : ep + 3 * kept.length ≤ g)
    (hvAt : ListAt mem vp vertices)
    (hframe : ∀ a, a < ep ∨ ep+3*kept.length ≤ a → out a = mem a) :
    let H := representativeGraph G ℓ
    let F : MGraph :=
      { V := G.V, E := (restoreTreeNames H T).E ∩ H.E, tail := G.tail, head := G.head }
    let triples := kept.map fun i => (edgeName H i, G.tail (edgeName H i), G.head (edgeName H i))
    (∀ i (hi : i < triples.length),
      out (ep+3*i) = triples[i].1 ∧ out (ep+3*i+1) = triples[i].2.1 ∧
        out (ep+3*i+2) = triples[i].2.2) →
    (dgInitFromListsContract w vCap eCap F vertices triples).pre
      [g,vCap,eCap,vertices.length,vp,kept.length,ep] out := by
  intro H F triples heAt
  have hzero' : ZeroFrom out g :=
    fun a ha => (hframe a (Or.inr (hep.trans ha))).trans (hzero a ha)
  have hvertices : ListAt out vp vertices := by
    intro i hi
    exact (hframe _ (Or.inl (by omega))).trans (hvAt i hi)
  exact selectedBranch_graphInit_pre ℓ kept vertices out g vCap eCap vp ep hG hn hset
    hindex hV hvc hec hw hroom hzero' (by omega) hep hvertices heAt

/-- Restore the edge records, initialize the branch graph, and return
the end of its allocated layout. -/
@[expose] def branchGraphBody (restore init : ℕ) : Stmt :=
  .seq (.call 12 restore ((List.range 7).map Expr.reg))
    (.seq (.call 13 init [.reg 7,.reg 8,.reg 9,.reg 10,.reg 11,.reg 6,.reg 0])
      (.ret (.reg 14)))

/-- The composed graph build returns its allocation end, and keeps
both the graph postcondition and the restored-record frame. -/
theorem branchGraph_runs {w restore init : ℕ} {p : Program} {ω : ℕ → Bool}
    {F : MGraph} {C : Contract} (verts : List ℕ) (triples : List (ℕ × ℕ × ℕ))
    (mem : ℕ → ℕ) (pos records names tails heads vertices selected count g vCap eCap vp : ℕ)
    (hr : MeetsContract w p restore C)
    (hg : MeetsContract w p init (dgInitFromListsContract w vCap eCap F verts triples)) :
    let ra := [records,names,tails,heads,vertices,selected,count]
    let ga := [g,vCap,eCap,verts.length,vp,count,records]
    let endPtr := g + dynGraphSize vCap eCap
    let args := ra ++ [g,vCap,eCap,verts.length,vp,0,0,endPtr]
    (∀ a ∈ args, a < 2^w) → C.pre ra mem →
    (∀ ret mid, C.post ra mem ret mid →
      (dgInitFromListsContract w vCap eCap F verts triples).pre ga mid) →
    ∃ o out cost, Runs w p ω (branchGraphBody restore init) (startState args mem pos) o out cost ∧
      (o.value = endPtr ∧ DynGraphAt out.mem g vCap eCap F ∧ ZeroFrom out.mem endPtr ∧
        ∃ mid ret, C.post ra mem ret mid ∧
          ∀ a, a < g ∨ endPtr ≤ a → out.mem a = mid a) ∧
      cost ≤ C.cost ra mem + 130*verts.length + 490*count + 120 := by
  intro ra ga endPtr args hwords hpre hnext
  have hend : endPtr < 2^w := hwords _ (by simp [args])
  apply runs_start_le
  unfold branchGraphBody
  refine runs_seq_call_le hr (vs := ra) (by rfl) ?_ hpre ?_
  · intro a ha
    exact hwords a (List.mem_append_left _ ha)
  · intro ret mid pos' hp
    refine runs_seq_call_le hg (vs := ga) (by rfl) ?_ (hnext ret mid hp) ?_
    · intro a ha
      apply hwords a
      simp only [ga,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [args,ra]
    · intro ret' out _ hout
      obtain ⟨g',vn,vp',en,ep,ha,_,hgraph,hframe,hzero⟩ := hout
      simp only [ga,List.cons.injEq,and_true,true_and] at ha
      obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := ha
      refine runs_ret_le (v := endPtr) (by eval_expr) ⟨rfl,hgraph,hzero,mid,ret,hp,hframe⟩ ?_
      have hsize : argsSize ((List.range 7).map Expr.reg) = 7 := by decide
      simp only [hsize, dgInitFromListsContract, ga, argsSize, Expr.size, startState]
      change 7 + C.cost ra mem + 2 + 7 + (130*verts.length + 490*count + 100) + 2 + 2 ≤
        C.cost ra mem + 130*verts.length + 490*count + 120
      omega

/-- Contract for restoring the named records and installing the shared
dynamic-graph layout for a retained edge list. -/
@[expose] def branchGraphContract (w vCap eCap : ℕ) (F : MGraph)
    (verts : List ℕ) (triples : List (ℕ × ℕ × ℕ)) (C : Contract) : Contract where
  pre args mem := ∃ records names tails heads vertices selected count g vp,
    let ra := [records,names,tails,heads,vertices,selected,count]
    let ga := [g,vCap,eCap,verts.length,vp,count,records]
    args = ra ++ [g,vCap,eCap,verts.length,vp,0,0,g+dynGraphSize vCap eCap] ∧
      C.pre ra mem ∧
      ∀ ret mid, C.post ra mem ret mid →
        (dgInitFromListsContract w vCap eCap F verts triples).pre ga mid
  post args mem ret out := ∃ records names tails heads vertices selected count g vp,
    let ra := [records,names,tails,heads,vertices,selected,count]
    let endPtr := g+dynGraphSize vCap eCap
    args = ra ++ [g,vCap,eCap,verts.length,vp,0,0,endPtr] ∧
      ret = endPtr ∧ DynGraphAt out g vCap eCap F ∧ ZeroFrom out endPtr ∧
      ∃ mid result, C.post ra mem result mid ∧
        ∀ a, a < g ∨ endPtr ≤ a → out a = mid a
  cost args mem := C.cost (args.take 7) mem + 130*verts.length + 490*args[6]! + 120

/-- The linked branch graph procedure returns the graph allocation end. -/
theorem branchGraph_meetsContract {w entry restore init vCap eCap : ℕ} {p : Program}
    {F : MGraph} {C : Contract} (verts : List ℕ) (triples : List (ℕ × ℕ × ℕ))
    (hp : p.procs[entry]? = some (branchGraphBody restore init))
    (hr : MeetsContract w p restore C)
    (hg : MeetsContract w p init (dgInitFromListsContract w vCap eCap F verts triples)) :
    MeetsContract w p entry (branchGraphContract w vCap eCap F verts triples C) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨records,names,tails,heads,vertices,selected,count,g,vp,rfl,hstart,hnext⟩ := hpre
  obtain ⟨o,out,cost,hrun,hpost,hcost⟩ := branchGraph_runs (p := p) (ω := ω)
    verts triples mem pos records names tails heads vertices selected count g vCap eCap vp
      hr hg hwords hstart hnext
  refine ⟨o,out,cost,hrun,⟨records,names,tails,heads,vertices,selected,count,g,vp,rfl,hpost⟩,?_⟩
  exact hcost

/-- Allocate the empty forest over the original vertices for the loop-only branch. -/
@[expose] def loopOnlyBranchGraph (entry : ℕ) : Stmt :=
  .call 46 entry [.reg 45,.reg 41,.reg 42,.reg 43,.reg 44,.const 0,.reg 45]

/-- The empty forest uses the original vertex list and no edge records. -/
theorem loopOnlyBranchGraph_runs {w entry vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (vertices : List ℕ) (dst src : ℕ)
    (h41 : st.regs 41 = vCap) (h42 : st.regs 42 = eCap)
    (h43 : st.regs 43 = vertices.length) (h44 : st.regs 44 = src) (h45 : st.regs 45 = dst)
    (hw : 16 ≤ 2^w) (hd : dst+dynGraphSize vCap eCap < 2^w)
    (hs : src+vertices.length ≤ dst) (hz : ZeroFrom st.mem dst)
    (hv : ∀ v ∈ G.V, v < vCap) (hlist : ListAt st.mem src vertices)
    (henum : ∀ v, v ∈ vertices ↔ v ∈ G.V) :
    let F : MGraph := { V := G.V, E := ∅, tail := G.tail, head := G.head }
    MeetsContract w p entry (dgInitFromListsContract w vCap eCap F vertices []) →
    ∃ out cost, Runs w p ω (loopOnlyBranchGraph entry) st .normal out cost ∧
      DynGraphAt out.mem dst vCap eCap F ∧ ZeroFrom out.mem (dst+dynGraphSize vCap eCap) ∧
      out.regs 46 = dst ∧
      (∀ a < dst, out.mem a = st.mem a) ∧
      (∀ r, r ≠ 46 → out.regs r = st.regs r) ∧ cost ≤ 130*vertices.length+108 := by
  intro F hc
  have hargs : evalArgs w st [.reg 45,.reg 41,.reg 42,.reg 43,.reg 44,.const 0,.reg 45] =
      some [dst,vCap,eCap,vertices.length,src,0,dst] := by
    simp [evalArgs,Expr.eval,h41,h42,h43,h44,h45,show 0 < 2^w by omega]
  have hwords : ∀ a ∈ [dst,vCap,eCap,vertices.length,src,0,dst], a < 2^w := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    unfold dynGraphSize at hd
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have hp : (dgInitFromListsContract w vCap eCap F vertices []).pre
      [dst,vCap,eCap,vertices.length,src,0,dst] st.mem := by
    refine ⟨dst,vertices.length,src,0,dst,rfl,hw,hd,hz,?_,hv,?_,rfl,hlist,henum,
      fun i hi => by omega,rfl,by simp,?_,?_,?_,?_⟩
    all_goals simp [F,MGraph.IsValid]
  obtain ⟨out,c,ret,hr,hpost,hret,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 46) hc hargs hwords hp ω
  obtain ⟨g,n,v,m,e,heq,hres,hgraph,hframe,hzero⟩ := hpost
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,_,_,_,rfl,rfl,rfl,rfl⟩ := heq
  change c ≤ 7+(130*vertices.length+100)+1 at hcost
  exact ⟨out,c,hr,hgraph,hzero,hret.trans hres,fun a ha => hframe a (Or.inl ha),hregs,by omega⟩

end MinCostFlow.LastLevelProgram
