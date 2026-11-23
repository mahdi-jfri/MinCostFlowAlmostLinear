module

public import MinCostFlow.LastLevelProgram.EdgeStretchQuery
public import MinCostFlow.LastLevelProgram.StretchRound
public import MinCostFlow.LastLevelProgram.StretchFits
public import MinCostFlow.LastLevelProgram.TraversalDistances
public import MinCostFlow.LastLevelProgram.TreeTables
import Mathlib.Tactic
import WordRAM.Tactic

/-!
# Inputs to the stretch query

The rooted tables give the LCA and distance blocks. Bounds on the
encoded lengths give all signed arithmetic bounds required by the call.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num LSF

/-- Recover a distance numerator from the decoded root-distance table. -/
theorem intVal_eq_rootDistanceNumerator {T : MGraph} {r x : ℕ}
    (hT : IsRootedTree T r) (hx : x ∈ T.V) (len : ℕ → ℤ) (mem : ℕ → ℕ)
    (a h L P : ℕ)
    (hd : fixVal mem a h L P =
      walkLength (fun e => (len e : ℝ) / (2 : ℝ)^P) (T.forestPath x r)) :
    intVal mem a h L = rootDistanceNumerator T r len x := by
  rw [← rootDistanceNumerator_decode hT hx len P,fixVal] at hd
  have hscale : (2 : ℝ)^P ≠ 0 := by positivity
  have he := (div_left_inj' hscale).mp hd
  exact_mod_cast he

/-- A query with the constructed tables and bounded edge numerators
meets the complete tree-table stretch contract. -/
theorem edgeStretchQuery_pre_of_treeTables {w h : ℕ} {T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (mem : ℕ → ℕ)
    (base n rows u v db dist edge L P Q heap B : ℕ) (len : ℕ → ℤ)
    (hV : ∀ x, x ∈ T.V ↔ x < n) (hw : 2 < 2^w) (hrows : 0 < rows)
    (hu : u < n) (hv : v < n) (hn : n ≤ 2^rows)
    (hat : base+rows*n < 2^w) (hdb : db+n < 2^w)
    (hAncestor : ∀ i < rows, ∀ x < n, mem (base+i*n+x) = ancestorJump (parent T r) i x)
    (hDepth : ∀ x < n, mem (db+x) = depth T r x)
    (hdist : dist+n*L ≤ heap) (hedge : edge+L ≤ heap)
    (hzero : ZeroFrom mem heap) (hroom : heap+edgeStretchSpace L < 2^w)
    (hvalues : ∀ x ∈ T.V, Valid mem (dist+x*L) h L ∧
      fixVal mem (dist+x*L) h L Q =
        walkLength (fun e => (len e : ℝ) / (2 : ℝ)^Q) (T.forestPath x r))
    (hve : Valid mem edge h L) (hpos : 0 < intVal mem edge h L) (hEdge : intVal mem edge h L ≤ B)
    (hLen : ∀ e ∈ T.E, 0 ≤ len e ∧ len e ≤ (B : ℤ))
    (hcap : 2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (capacity h L : ℤ)) :
    (edgeStretchQueryContract w h T r).pre [base,n,rows,u,v,db,dist,edge,L,P,heap] mem := by
  let z := lca T r u v
  have hu' := (hV u).2 hu
  have hv' := (hV v).2 hv
  have hz' : z ∈ T.V := lca_mem hT hu' hv'
  have hz := (hV z).1 hz'
  have haddr (x : ℕ) (hx : x < n) : dist+x*L+L ≤ heap := by
    have hh := Nat.mul_le_mul_right L hx
    rw [Nat.succ_mul] at hh
    omega
  have hNum (x : ℕ) (hx : x ∈ T.V) :
      intVal mem (dist+x*L) h L = rootDistanceNumerator T r len x :=
    intVal_eq_rootDistanceNumerator hT hx len mem _ h L Q (hvalues x hx).2
  obtain ⟨ha,hb,hab,hstretch⟩ := treeStretchNumerator_fits hT hu' hv' len B h L P
    (intVal mem edge h L) hLen hpos hEdge hcap
  refine ⟨base,n,rows,u,v,db,dist,edge,L,P,heap,rfl,hV,hu,hv,by omega,?_,?_,hroom⟩
  · exact ⟨base,n,rows,u,v,db,rfl,hV,hw,hrows,hu,hv,
      fun x hx => compactTree_depth_bounds hT hV hx hn (by omega),hdb,hDepth,hat,hAncestor⟩
  · refine ⟨⟨_,_,_,_,L,P,heap,rfl,haddr u hu,haddr v hv,haddr z hz,hedge,
      (hvalues u hu').1,(hvalues v hv').1,(hvalues z hz').1,hve,?_,?_,?_,hpos,?_⟩,hzero,hroom⟩
    · rw [hNum u hu',hNum z hz']
      exact ha
    · rw [hNum v hv',hNum z hz']
      exact hb
    · rw [hNum u hu',hNum v hv',hNum z hz']
      exact hab
    · rw [hNum u hu',hNum v hv',hNum z hz']
      convert hstretch using 1
      dsimp [z]
      ring


/-- With the completed tree tables, one pass writes the rounded stretch
of every packed edge. Each output occupies the last block of its stride. -/
theorem rootedStretchRound_triple {w h query : ℕ} {p : Program} {G T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (hq : MeetsContract w p query (edgeStretchQueryContract w h T r))
    (mem : ℕ → ℕ) (pos base n rows tails heads db dist lengths L P Q heap m B : ℕ)
    (len : ℕ → ℤ)
    (hw : 2 < 2^w) (hV : ∀ x, x ∈ T.V ↔ x < n)
    (hwords : ∀ a ∈ [base,n,rows,tails,heads,db,dist,lengths,L,P,heap,m], a < 2^w)
    (hrows : 0 < rows) (hn : n ≤ 2^rows)
    (hat : base+rows*n ≤ heap) (hdb : db+n ≤ heap)
    (ht : tails+m ≤ heap) (hh : heads+m ≤ heap)
    (hDist : dist+n*L ≤ heap) (hLen : lengths+m*L ≤ heap)
    (hroom : heap+m*edgeStretchSpace L < 2^w) (hzero : ZeroFrom mem heap)
    (hAncestor : ∀ i < rows, ∀ x < n, mem (base+i*n+x) = ancestorJump (parent T r) i x)
    (hDepth : ∀ x < n, mem (db+x) = depth T r x)
    (hvalues : ∀ x ∈ T.V, Valid mem (dist+x*L) h L ∧
      fixVal mem (dist+x*L) h L Q =
        walkLength (fun e => (len e : ℝ) / (2 : ℝ)^Q) (T.forestPath x r))
    (hEnds : ∀ i < m, G.tail i < n ∧ G.head i < n ∧
      mem (tails+i) = G.tail i ∧ mem (heads+i) = G.head i)
    (hEdge : ∀ i < m, Valid mem (lengths+i*L) h L ∧ intVal mem (lengths+i*L) h L = len i ∧
      0 < len i ∧ len i ≤ B)
    (hTreeLen : ∀ e ∈ T.E, 0 ≤ len e ∧ len e ≤ (B : ℤ))
    (hcap : 2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (capacity h L : ℤ)) :
    Triple w p (fun st => st = startState [base,n,rows,tails,heads,db,dist,lengths,L,P,heap,m] mem pos)
      (stretchRoundLoop query)
      (normalPost fun st =>
        st.regs 10 = heap+m*edgeStretchSpace L ∧ ZeroFrom st.mem (st.regs 10) ∧
        (∀ a < heap, st.mem a = mem a) ∧
        ∀ i < m, Valid st.mem (roundStretchAddr heap L i) h L ∧
          fixVal st.mem (roundStretchAddr heap L i) h L P =
            roundStretch P (treeStretch G T (fun e => (len e : ℝ) / (2 : ℝ)^Q) i))
      (fun _ => (86*rows+edgeStretchCost L+126)*m+7) := by
  have hnW := hwords n (by simp)
  have hreadU (i : ℕ) (hi : i < m) : mem (tails+i) = G.tail i ∧ G.tail i < 2^w :=
    ⟨(hEnds i hi).2.2.1,(hEnds i hi).1.trans hnW⟩
  have hreadV (i : ℕ) (hi : i < m) : mem (heads+i) = G.head i ∧ G.head i < 2^w :=
    ⟨(hEnds i hi).2.2.2,(hEnds i hi).2.1.trans hnW⟩
  have hpre (i : ℕ) (hi : i < m) : (edgeStretchQueryContract w h T r).pre
      [base,n,rows,G.tail i,G.head i,db,dist,lengths+i*L,L,P,heap] mem := by
    obtain ⟨hu,hv,_,_⟩ := hEnds i hi
    obtain ⟨hve,hval,hpos,hB⟩ := hEdge i hi
    have he : lengths+i*L+L ≤ heap := by
      have hmul := Nat.mul_le_mul_right L hi
      rw [Nat.succ_mul] at hmul
      omega
    have hspace : heap+edgeStretchSpace L < 2^w := by
      have hh := Nat.le_mul_of_pos_left (edgeStretchSpace L) (by omega : 0 < m)
      omega
    exact edgeStretchQuery_pre_of_treeTables hT mem base n rows (G.tail i) (G.head i)
      db dist (lengths+i*L) L P Q heap B len hV hw hrows hu hv hn (by omega) (by omega)
      hAncestor hDepth hDist he hzero hspace hvalues hve (by simpa [hval] using hpos)
      (by simpa [hval] using hB) hTreeLen hcap
  refine (stretchRoundLoop_triple hq mem pos base n rows tails heads db dist lengths L P heap m
    G.tail G.head (by omega) hwords hat hdb ht hh hLen hroom hzero hreadU hreadV hpre).conseq
    (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st hs
  cases o with
  | returned => exact hs
  | normal =>
    obtain ⟨hret,hz,hf,hvalues'⟩ := hs
    refine ⟨hret,hz,hf,?_⟩
    exact stretchRound_outputs_eq_treeStretch hT (fun e => (len e : ℝ) / (2 : ℝ)^Q)
      mem st.mem h L P Q dist lengths heap m id (fun x hx => (hvalues x hx).2)
      (fun i hi => by simp only [fixVal,id]; rw [(hEdge i hi).2.1])
      (fun i hi => ⟨(hV _).2 (hEnds i hi).1,(hV _).2 (hEnds i hi).2.1⟩) hvalues'

/-- A stretch pass returns the heap pointer after the last edge result. -/
@[expose] def rootedStretchRoundBody (query : ℕ) : Stmt :=
  stretchRoundLoop query ;; .ret (.reg 10)

/-- Callable interface for the stretch pass, using the same ancestor,
depth, and distance tables as the individual queries. -/
@[expose] def rootedStretchRoundContract (w h Q : ℕ) (G T : MGraph) (r : ℕ)
    (len : ℕ → ℤ) : Contract where
  pre args mem := ∃ (base n rows tails heads db dist lengths L P heap m B : ℕ),
    args = [base,n,rows,tails,heads,db,dist,lengths,L,P,heap,m] ∧
    2 < 2^w ∧ (∀ x, x ∈ T.V ↔ x < n) ∧ 0 < rows ∧ n ≤ 2^rows ∧
    base+rows*n ≤ heap ∧ db+n ≤ heap ∧ tails+m ≤ heap ∧ heads+m ≤ heap ∧
    dist+n*L ≤ heap ∧ lengths+m*L ≤ heap ∧ heap+m*edgeStretchSpace L < 2^w ∧
    ZeroFrom mem heap ∧
    (∀ i < rows, ∀ x < n, mem (base+i*n+x) = ancestorJump (parent T r) i x) ∧
    (∀ x < n, mem (db+x) = depth T r x) ∧
    (∀ x ∈ T.V, Valid mem (dist+x*L) h L ∧
      fixVal mem (dist+x*L) h L Q =
        walkLength (fun e => (len e : ℝ) / (2 : ℝ)^Q) (T.forestPath x r)) ∧
    (∀ i < m, G.tail i < n ∧ G.head i < n ∧
      mem (tails+i) = G.tail i ∧ mem (heads+i) = G.head i) ∧
    (∀ i < m, Valid mem (lengths+i*L) h L ∧ intVal mem (lengths+i*L) h L = len i ∧
      0 < len i ∧ len i ≤ B) ∧
    (∀ e ∈ T.E, 0 ≤ len e ∧ len e ≤ (B : ℤ)) ∧
    2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (capacity h L : ℤ)
  post args mem ret out :=
    let L := args.getD 8 0
    let P := args.getD 9 0
    let heap := args.getD 10 0
    let m := args.getD 11 0
    ret = heap+m*edgeStretchSpace L ∧ ZeroFrom out ret ∧
    (∀ a < heap, out a = mem a) ∧
    ∀ i < m, Valid out (roundStretchAddr heap L i) h L ∧
      fixVal out (roundStretchAddr heap L i) h L P =
        roundStretch P (treeStretch G T (fun e => (len e : ℝ) / (2 : ℝ)^Q) i)
  cost args _ := (86*args.getD 2 0+edgeStretchCost (args.getD 8 0)+126)*args.getD 11 0+10

/-- The stretch pass writes the rounded tree stretch for every compact
edge and preserves the original tables. -/
theorem rootedStretchRound_meetsContract {w h Q entry query : ℕ} {p : Program} {G T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (len : ℕ → ℤ)
    (he : p.procs[entry]? = some (rootedStretchRoundBody query))
    (hq : MeetsContract w p query (edgeStretchQueryContract w h T r)) :
    MeetsContract w p entry (rootedStretchRoundContract w h Q G T r len) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨base,n,rows,tails,heads,db,dist,lengths,L,P,heap,m,B,rfl,
    hw,hV,hrows,hn,hat,hdb,ht,hh,hDist,hLen,hroom,hzero,hAnc,hDepth,hvalues,
    hEnds,hEdge,hTreeLen,hcap⟩ := hpre
  obtain ⟨o,mid,c,hr,hpost,hcost⟩ :=
    rootedStretchRound_triple hT hq mem pos base n rows tails heads db dist lengths L P Q heap m B
      len hw hV hwords hrows hn hat hdb ht hh hDist hLen hroom hzero hAnc hDepth hvalues
      hEnds hEdge hTreeLen hcap _ ω rfl
  cases o with
  | returned => exact False.elim hpost
  | normal =>
    have hrun : Runs w p ω (.ret (.reg 10)) mid (.returned (mid.regs 10)) mid 2 :=
      runs_ret_iff.mpr ⟨mid.regs 10,rfl,rfl,rfl,rfl⟩
    refine ⟨.returned (mid.regs 10),mid,c+3,
      runs_seq_iff.mpr (Or.inr ⟨mid,c,2,hr,hrun,by omega⟩),hpost,?_⟩
    change c ≤ (86*rows+edgeStretchCost L+126)*m+7 at hcost
    change c+3 ≤ (86*rows+edgeStretchCost L+126)*m+10
    omega

/-- The table builder preserves the compact input arrays and supplies
the complete precondition for the stretch round. -/
theorem rootedStretchRound_pre_of_treeTables {w h Q : ℕ} {G T : MGraph} {r : ℕ}
    (len : ℕ → ℤ) (mem out : ℕ → ℕ)
    (adj base edges db queue n levels dist lengths L heap m ret tails heads P B : ℕ)
    (hpost : (buildTreeTablesContract w h Q m T r len).post
      [adj,base,edges,db,queue,r,n,levels,dist,lengths,L,heap] mem ret out)
    (hw : 2 < 2^w) (hV : ∀ x, x ∈ T.V ↔ x < n) (hn : n ≤ 2^(levels+1))
    (hat : base+(levels+1)*n ≤ heap) (hdb : db+n ≤ heap)
    (hDist : dist+n*L ≤ heap) (hHeap : heap ≤ ret)
    (hTails : adj ≤ tails ∧ tails+m ≤ dist) (hHeads : adj ≤ heads ∧ heads+m ≤ dist)
    (hLen : adj ≤ lengths ∧ lengths+m*L ≤ dist)
    (hRoom : ret+m*edgeStretchSpace L < 2^w)
    (hEnds : ∀ i < m, G.tail i < n ∧ G.head i < n ∧
      mem (tails+i) = G.tail i ∧ mem (heads+i) = G.head i)
    (hEdge : ∀ i < m, Valid mem (lengths+i*L) h L ∧ intVal mem (lengths+i*L) h L = len i ∧
      0 < len i ∧ len i ≤ (B : ℤ))
    (hTreeLen : ∀ e ∈ T.E, 0 ≤ len e ∧ len e ≤ (B : ℤ))
    (hcap : 2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (capacity h L : ℤ)) :
    (rootedStretchRoundContract w h Q G T r len).pre
      [base,n,levels+1,tails,heads,db,dist,lengths,L,P,ret,m] out := by
  obtain ⟨_,hz,hAnc,hDepth,hframe,hvals,_⟩ := hpost
  change ∀ a, adj ≤ a → a < dist → out a = mem a at hframe
  have hdistHeap : dist ≤ heap := (Nat.le_add_right _ _).trans hDist
  refine ⟨base,n,levels+1,tails,heads,db,dist,lengths,L,P,ret,m,B,rfl,hw,hV,by omega,hn,
    hat.trans hHeap,hdb.trans hHeap,by omega,by omega,hDist.trans hHeap,by omega,hRoom,hz,
    hAnc,hDepth,hvals,?_,?_,hTreeLen,hcap⟩
  · intro i hi
    obtain ⟨hu,hv,hT,hH⟩ := hEnds i hi
    exact ⟨hu,hv,(hframe _ (by omega) (by omega)).trans hT,
      (hframe _ (by omega) (by omega)).trans hH⟩
  · intro i hi
    obtain ⟨hv,heq,hpos,hB⟩ := hEdge i hi
    have hmul := Nat.mul_le_mul_right L hi
    rw [Nat.succ_mul] at hmul
    have hsame (j : ℕ) (hj : j < L) :
        out (lengths+i*L+j) = mem (lengths+i*L+j) := hframe _ (by omega) (by omega)
    exact ⟨fun j hj => (hsame j hj).trans_lt (hv j hj),
      (intVal_congr hsame).trans heq,hpos,hB⟩
end MinCostFlow.LastLevelProgram
