module

public import MinCostFlow.LastLevelProgram.StretchQueryInputs
import WordRAM.Tactic

/-!
# Building and querying the stretch tables

Build the rooted tables once, then run the rounded stretch pass over
the compact edges using the resulting heap pointer.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num LSF

/-- Append the tail and head bases, stretch precision, and edge count
to the tree-table builder's arguments. -/
def treeStretchRoundBody (tables stretches : ℕ) : Stmt :=
  .call 16 tables [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,.reg 11] ;;
  .call 17 stretches [.reg 1,.reg 6,.bin .add (.reg 7) (.const 1),.reg 12,.reg 13,.reg 3,
    .reg 8,.reg 9,.reg 10,.reg 14,.reg 16,.reg 15] ;;
  .ret (.reg 17)

/-- The composed round computes rounded stretches and returns the heap
pointer after the results. The input edge lengths retain their scale. -/
theorem treeStretchRound_runs {w h Q tables stretches : ℕ} {p : Program} {G T : MGraph} {r : ℕ}
    (len : ℕ → ℤ) (ht : MeetsContract w p tables (buildTreeTablesContract w h Q G.m T r len))
    (hs : MeetsContract w p stretches (rootedStretchRoundContract w h Q G T r len))
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (pos adj base edges db queue n levels dist lengths L heap tails heads P B : ℕ)
    (hwords : ∀ a ∈ [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,G.m],
      a < 2^w)
    (hpre : (buildTreeTablesContract w h Q G.m T r len).pre
      [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap] mem)
    (hw : 2 < 2^w) (hV : ∀ x, x ∈ T.V ↔ x < n) (hn : n ≤ 2^(levels+1))
    (hat : base+(levels+1)*n ≤ heap) (hdb : db+n ≤ heap) (hDist : dist+n*L ≤ heap)
    (hTails : adj ≤ tails ∧ tails+G.m ≤ dist) (hHeads : adj ≤ heads ∧ heads+G.m ≤ dist)
    (hLen : adj ≤ lengths ∧ lengths+G.m*L ≤ dist)
    (hRoom : heap+(n-1)*L+G.m*edgeStretchSpace L < 2^w)
    (hRows : levels+1 < 2^w)
    (hEnds : ∀ i < G.m, G.tail i < n ∧ G.head i < n ∧ mem (tails+i) = G.tail i ∧ mem (heads+i) = G.head i)
    (hEdge : ∀ i < G.m, Valid mem (lengths+i*L) h L ∧ intVal mem (lengths+i*L) h L = len i ∧
      0 < len i ∧ len i ≤ (B : ℤ))
    (hTreeLen : ∀ e ∈ T.E, 0 ≤ len e ∧ len e ≤ (B : ℤ))
    (hcap : 2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (capacity h L : ℤ)) :
    let start := heap+(n-1)*L
    ∃ o out c, Runs w p ω (treeStretchRoundBody tables stretches)
      (startState [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,G.m] mem pos)
      o out c ∧
      (o.value = start+G.m*edgeStretchSpace L ∧ ZeroFrom out.mem o.value ∧
        (∀ a, adj ≤ a → a < dist → out.mem a = mem a) ∧
        (∀ i < G.m, Valid out.mem (roundStretchAddr start L i) h L ∧
          fixVal out.mem (roundStretchAddr start L i) h L P =
            roundStretch P (treeStretch G T (fun e => (len e : ℝ) / (2 : ℝ)^Q) i)) ∧
        ∀ a < base, out.mem a = mem a) ∧
      c ≤ 114*T.E.card+35*T.V.card+(55*L+75)*(n-1)+(20*n+40)*levels+
        (86*(levels+1)+edgeStretchCost L+126)*G.m+126 := by
  intro start
  have hadj := hwords adj (by simp)
  have hbase := hwords base (by simp)
  have hedges := hwords edges (by simp)
  have hdbW := hwords db (by simp)
  have hqueue := hwords queue (by simp)
  have hr := hwords r (by simp)
  have hnW := hwords n (by simp)
  have hlevels := hwords levels (by simp)
  have hdist := hwords dist (by simp)
  have hlengths := hwords lengths (by simp)
  have hL := hwords L (by simp)
  have hheap := hwords heap (by simp)
  have htails := hwords tails (by simp)
  have hheads := hwords heads (by simp)
  have hPW := hwords P (by simp)
  have hm := hwords G.m (by simp)
  apply runs_start_le
  unfold treeStretchRoundBody
  refine runs_seq_call_le ht (vs := [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap])
    (by eval_expr) ?_ hpre ?_
  · wram_words
  · intro ret middle pos' hpost
    have he : ret = start := hpost.1
    subst ret
    have hstart : start < 2^w := by dsimp [start]; omega
    have hroom : start+G.m*edgeStretchSpace L < 2^w := hRoom
    have hnext := rootedStretchRound_pre_of_treeTables len mem middle adj base edges db queue
      n levels dist lengths L heap G.m start tails heads P B hpost hw hV hn hat hdb hDist
      (Nat.le_add_right _ _) hTails hHeads hLen hroom hEnds hEdge hTreeLen hcap
    refine runs_seq_call_le hs (vs := [base,n,levels+1,tails,heads,db,dist,lengths,L,P,start,G.m])
      (by eval_expr) ?_ hnext ?_
    · wram_words
    · intro finish out _ hf
      have hfinish : finish = start+G.m*edgeStretchSpace L := hf.1
      have hfinishW : finish < 2^w := hfinish ▸ hroom
      refine runs_ret_le (v := finish) (by eval_expr) ?_ ?_
      · refine ⟨hf.1,hf.2.1,?_,hf.2.2.2,?_⟩
        · intro a ha hb
          have haStart : a < start := by dsimp [start]; omega
          exact (hf.2.2.1 a haStart).trans (hpost.2.2.2.2.1 a ha hb)
        · intro a ha
          have haStart : a < start := by dsimp [start]; omega
          exact (hf.2.2.1 a haStart).trans (hpost.2.2.2.2.2.2 a ha)
      · simp [buildTreeTablesContract,rootedStretchRoundContract,argsSize,Expr.size]
        omega


/-- Callable table construction and stretch computation for one round. -/
def treeStretchRoundContract (w h Q : ℕ) (G T : MGraph) (r : ℕ) (len : ℕ → ℤ) : Contract where
  pre args mem := ∃ (adj base edges db queue n levels dist lengths L heap tails heads P B : ℕ),
    args = [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap,tails,heads,P,G.m] ∧
    (buildTreeTablesContract w h Q G.m T r len).pre
      [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap] mem ∧
    2 < 2^w ∧ (∀ x, x ∈ T.V ↔ x < n) ∧ n ≤ 2^(levels+1) ∧
    base+(levels+1)*n ≤ heap ∧ db+n ≤ heap ∧ dist+n*L ≤ heap ∧
    (adj ≤ tails ∧ tails+G.m ≤ dist) ∧ (adj ≤ heads ∧ heads+G.m ≤ dist) ∧
    (adj ≤ lengths ∧ lengths+G.m*L ≤ dist) ∧
    heap+(n-1)*L+G.m*edgeStretchSpace L < 2^w ∧ levels+1 < 2^w ∧
    (∀ i < G.m, G.tail i < n ∧ G.head i < n ∧
      mem (tails+i) = G.tail i ∧ mem (heads+i) = G.head i) ∧
    (∀ i < G.m, Valid mem (lengths+i*L) h L ∧ intVal mem (lengths+i*L) h L = len i ∧
      0 < len i ∧ len i ≤ (B : ℤ)) ∧
    (∀ e ∈ T.E, 0 ≤ len e ∧ len e ≤ (B : ℤ)) ∧
    2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (capacity h L : ℤ)
  post args mem ret out :=
    let adj := args.getD 0 0
    let base := args.getD 1 0
    let n := args.getD 6 0
    let dist := args.getD 8 0
    let L := args.getD 10 0
    let start := args.getD 11 0+(n-1)*L
    let P := args.getD 14 0
    ret = start+G.m*edgeStretchSpace L ∧ ZeroFrom out ret ∧
    (∀ a, adj ≤ a → a < dist → out a = mem a) ∧
    (∀ i < G.m, Valid out (roundStretchAddr start L i) h L ∧
      fixVal out (roundStretchAddr start L i) h L P =
        roundStretch P (treeStretch G T (fun e => (len e : ℝ) / (2 : ℝ)^Q) i)) ∧
    ∀ a < base, out a = mem a
  cost args _ :=
    let n := args.getD 6 0
    let levels := args.getD 7 0
    let L := args.getD 10 0
    114*T.E.card+35*T.V.card+(55*L+75)*(n-1)+(20*n+40)*levels+
      (86*(levels+1)+edgeStretchCost L+126)*G.m+126

/-- The combined round satisfies the stretch output and memory frame. -/
theorem treeStretchRound_meetsContract {w h Q entry tables stretches : ℕ}
    {p : Program} {G T : MGraph} {r : ℕ} (len : ℕ → ℤ)
    (he : p.procs[entry]? = some (treeStretchRoundBody tables stretches))
    (ht : MeetsContract w p tables (buildTreeTablesContract w h Q G.m T r len))
    (hs : MeetsContract w p stretches (rootedStretchRoundContract w h Q G T r len)) :
    MeetsContract w p entry (treeStretchRoundContract w h Q G T r len) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨adj,base,edges,db,queue,n,levels,dist,lengths,L,heap,tails,heads,P,B,rfl,
    htpre,hw,hV,hn,hat,hdb,hDist,hTails,hHeads,hLen,hRoom,hRows,hEnds,hEdge,hTreeLen,hcap⟩ := hpre
  exact treeStretchRound_runs len ht hs mem ω pos adj base edges db queue n levels dist lengths L
    heap tails heads P B hwords htpre hw hV hn hat hdb hDist hTails hHeads hLen hRoom hRows
    hEnds hEdge hTreeLen hcap
end MinCostFlow.LastLevelProgram
