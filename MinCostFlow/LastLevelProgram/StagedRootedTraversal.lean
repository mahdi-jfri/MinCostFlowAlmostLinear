module

public import MinCostFlow.LastLevelProgram.StagedGuestQuery
public import MinCostFlow.LastLevelProgram.TreeTables
public import WordRAM.CopyWords
public import MinCostFlow.LastLevelProgram.PackValues
public import MinCostFlow.LastLevelProgram.Denominator
import WordRAM.Tactic
import WordRAM.Link
import Mathlib.Tactic

/-!
# Rooted traversal after staged tree selection

A round of Definition 5.8 (pages 19–20) builds incidences for the
selected tree and traverses them from compact vertex zero.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM LSF WideWord

/-- Build the staged tree incidences, then write the rooted traversal tables. -/
def stagedRootedTraversalBody (adjacency traverse : ℕ) : Stmt :=
  .seq (.call 15 adjacency
    (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
      (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)))
    (.call 16 traverse (stagedTraversalArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12)))

/-- The two calls populate the rooted traversal tables and retain the
runtime layout registers for the following distance pass. -/
theorem stagedRootedTraversal_runs {w adjacency traverse insert : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G T : MGraph)
    (L staging cursor levels count : ℕ) (mem : ℕ → ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (he : p.procs[adjacency]? = some (selectedAdjacencyBody insert))
    (hi : MeetsContract w p insert (pushTreeEdgeContract w))
    (hq : p.procs[traverse]? = some traverseTreeQueueBody)
    (hw : 6 < 2^w) (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (ha : st.regs 5 = staging)
    (hc : st.regs 12 = cursor) (hl : st.regs 14 = levels) (hk : st.regs 13 = count)
    (hnPos : 0 < G.n) :
    let dest := cursor+1+G.m
    let parents := dest+G.n
    let edges := parents+(levels+1)*G.n
    let depths := edges+G.n
    let queue := depths+G.n
    let adj := parents+stagedTraversalReserve G.n levels
    let records := adj+G.n
    selectedTreeAt G T (staging+queryWeights G L) dest count mem st.mem →
    staging+queryWeights G L ≤ dest → records+6*G.n < 2^w →
    ∃ (mid out : State) (cost : ℕ), Runs w p ω (stagedRootedTraversalBody adjacency traverse)
      st .normal out cost ∧
      (traverseTreeQueueContract w T 0).post [adj,parents,edges,depths,queue,0]
        mid.mem (out.regs 16) out.mem ∧
      ZeroFrom out.mem (records+6*G.n) ∧
      (∀ r, r ≠ 15 → r ≠ 16 → out.regs r = st.regs r) ∧
      cost ≤ argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
          (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
        argsSize (stagedTraversalArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12)) +
        112*count+114*T.E.card+35*T.V.card+36 := by
  intro dest parents edges depths queue adj records hTree hsep hroom
  have hretain := retainedStagedTreeAt_of_frame hTree
    (limit := max (staging+queryWeights G L) (dest+G.n)) (le_max_left _ _) (le_max_right _ _)
    (fun _ _ => rfl)
  obtain ⟨mid,ca,kept,har,hcount,hnd,hdecode,hpost,_,hz,hregs,hca⟩ :=
    stagedAdjacency_runs (ω := ω) (result := 15) st G T L staging cursor levels count
      mem ℓ v γ he hi hw hv hconn htree ht hh hn hm ha hc hl hk hnPos hretain hsep hroom
  obtain ⟨xs,hxs,hsize,_,_,_,_,hzero⟩ := hTree
  have hkSize : kept.length ≤ G.n := hcount ▸ (hxs.symm ▸ hsize)
  rw [hcount] at hpost
  have hpre := traversal_pre_of_stagedAdjacency G T staging dest levels kept st.mem mid.mem
    ℓ v γ hv hconn htree hdecode hnd hkSize (by omega) hpost (fun a ha _ => hzero a ha) hroom
  have hAdj : adj < 2^w :=
    (Nat.le_add_right _ _).trans_lt ((Nat.le_add_right _ _).trans_lt hroom)
  obtain ⟨out,ct,htr,hresult,hpres,hct⟩ :=
    stagedTraversal_runs (ω := ω) (result := 16) mid T G.n G.m levels cursor hq
      (indexedLSST_rooted_zero hv htree)
      (by simp [hregs,hn]) (by simp [hregs,hm]) (by simp [hregs,hl])
      (by simp [hregs,hc]) hnPos hAdj hpre
  refine ⟨mid,out,ca+ct+1,runs_seq_iff.mpr (Or.inr ⟨mid,ca,ct,har,htr,rfl⟩),
    hresult,?_,?_,by omega⟩
  · obtain ⟨_,_,_,_,_,_,_,hf⟩ := hresult
    intro a ha
    exact (hf a (show adj ≤ a from
      (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans ha))).trans ((hz a ha).trans (hzero a (by
          change dest+G.n+stagedTraversalReserve G.n levels+G.n+6*G.n ≤ a at ha
          omega)))
  · intro r hr₁ hr₂
    rw [hpres r hr₂, hregs, Function.update_of_ne hr₁]

/-- The tree-table builder shares the traversal layout and appends
the runtime numerical pointers and limb count. -/
def stagedTreeTableBuildArgs (n m levels cursor dist lengths limbs heap : Expr) : List Expr :=
  stagedTraversalArgs n m levels cursor ++ [n,levels,dist,lengths,limbs,heap]

/-- The staged table builder receives the same addresses as the
adjacency and queue contracts, together with the fixed-point layout. -/
theorem stagedTreeTableBuildArgs_eval {w : ℕ} {st : State}
    {ne me ke ce de ae le he : Expr}
    (n m levels cursor dist lengths L heap : ℕ)
    (hn : ne.eval w st = some n) (hm : me.eval w st = some m)
    (hk : ke.eval w st = some levels) (hc : ce.eval w st = some cursor)
    (hd : de.eval w st = some dist) (ha : ae.eval w st = some lengths)
    (hL : le.eval w st = some L) (hh : he.eval w st = some heap)
    (hnPos : 0 < n) (hfit : cursor+1+m+n+stagedTraversalReserve n levels < 2^w) :
    let parents := cursor+1+m+n
    let edges := parents+(levels+1)*n
    let depths := edges+n
    let queue := depths+n
    let adj := parents+stagedTraversalReserve n levels
    evalArgs w st (stagedTreeTableBuildArgs ne me ke ce de ae le he) =
      some [adj,parents,edges,depths,queue,0,n,levels,dist,lengths,L,heap] := by
  intro parents edges depths queue adj
  have htrav := stagedTraversalArgs_eval n m levels cursor hn hm hk hc hnPos hfit
  have hnum : evalArgs w st [ne,ke,de,ae,le,he] = some [n,levels,dist,lengths,L,heap] := by
    simp only [evalArgs,hn,hk,hd,ha,hL,hh]
  exact Link.evalArgs_append htrav hnum

/-- Call the combined tree-table builder with the staged traversal
layout. The builder computes root distances and binary ancestor rows. -/
theorem stagedTreeTableBuild_runs {w h Q entry result : ℕ} {p : Program} {ω : ℕ → Bool}
    {ne me ke ce de ae le he : Expr} (st : State) (T : MGraph) (len : ℕ → ℤ)
    (n m levels cursor dist lengths L heap : ℕ)
    (hn : ne.eval w st = some n) (hm : me.eval w st = some m)
    (hk : ke.eval w st = some levels) (hc : ce.eval w st = some cursor)
    (hd : de.eval w st = some dist) (ha : ae.eval w st = some lengths)
    (hL : le.eval w st = some L) (hh : he.eval w st = some heap)
    (hnPos : 0 < n)
    (hcall : MeetsContract w p entry (buildTreeTablesContract w h Q m T 0 len)) :
    let parents := cursor+1+m+n
    let edges := parents+(levels+1)*n
    let depths := edges+n
    let queue := depths+n
    let adj := parents+stagedTraversalReserve n levels
    let words := [adj,parents,edges,depths,queue,0,n,levels,dist,lengths,L,heap]
    let args := stagedTreeTableBuildArgs ne me ke ce de ae le he
    (∀ a ∈ words, a < 2^w) →
    (buildTreeTablesContract w h Q m T 0 len).pre words st.mem →
    ∃ out cost, Runs w p ω (.call result entry args) st .normal out cost ∧
      (buildTreeTablesContract w h Q m T 0 len).post words st.mem (out.regs result) out.mem ∧
      (∀ r, r ≠ result → out.regs r = st.regs r) ∧
      cost ≤ argsSize args + 114*T.E.card+35*T.V.card+
        (55*L+75)*(n-1)+(20*n+40)*levels+81 := by
  intro parents edges depths queue adj words args hwords hpre
  have hfit : adj < 2^w := hwords _ (by simp [words])
  have hargs := stagedTreeTableBuildArgs_eval n m levels cursor dist lengths L heap
    hn hm hk hc hd ha hL hh hnPos hfit
  obtain ⟨out,cost,ret,hr,hpost,hret,hregs,hcost⟩ := runs_call_of_meetsContract
    (r := result) hcall hargs hwords hpre ω
  refine ⟨out,cost,hr,hret.symm ▸ hpost,hregs,?_⟩
  change cost ≤ argsSize args +
    (114*T.E.card+35*T.V.card+(55*L+75)*(n-1)+(20*n+40)*levels+80) + 1 at hcost
  omega

/-- The staged adjacency layout supplies the root-distance and ancestor
table precondition when the numeric blocks follow the incidence records. -/
theorem treeTables_pre_of_stagedAdjacency {w h Q : ℕ} (G T : MGraph)
    (staging dest levels dist lengths L heap : ℕ) (kept : List ℕ) (len : ℕ → ℤ)
    (mem out : ℕ → ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (hdecode : decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T)
    (hnd : kept.Nodup) (hsize : kept.length ≤ G.n)
    (hw : 2 < 2^w)
    (hLen : ∀ e ∈ T.E, Num.Valid mem (lengths+e*L) h L ∧
      Num.intVal mem (lengths+e*L) h L = len e)
    (hFit : ∀ x ∈ T.V, Num.Fits h L (rootDistanceNumerator T 0 len x)) :
    let parents := dest+G.n
    let edges := parents+(levels+1)*G.n
    let depths := edges+G.n
    let queue := depths+G.n
    let adj := parents+stagedTraversalReserve G.n levels
    let records := adj+G.n
    (selectedAdjacencyContract w (indexedGraph G) kept dest staging (staging+G.m)
      adj records).post [dest,staging,staging+G.m,adj,records,kept.length] mem 0 out →
    (∀ a, dest+G.n ≤ a → a < records → mem a = 0) →
    records+6*G.n < 2^w → records+6*G.n ≤ lengths →
    lengths+G.m*L ≤ dist → ZeroFrom mem dist → dist+G.n*L ≤ heap → heap+(G.n-1)*L < 2^w →
    (buildTreeTablesContract w h Q G.m T 0 len).pre
      [adj,parents,edges,depths,queue,0,G.n,levels,dist,lengths,L,heap] out := by
  intro parents edges depths queue adj records hpost hz hroom hrec hLD hZeroDist hDH hheap
  have hTrav := traversal_pre_of_stagedAdjacency G T staging dest levels kept mem out
    ℓ v γ hv hconn htree hdecode hnd hsize hw hpost hz hroom
  have hindex := (connectedDecodedTree_originals hv hconn (hdecode.symm ▸ htree)).2
  have hV : ∀ x, x ∈ T.V ↔ x < G.n := by
    intro x
    rw [← hdecode]
    exact Finset.mem_range
  have hE : ∀ e ∈ T.E, e < G.m := by
    intro e he
    apply hindex e
    rw [← hdecode] at he
    simpa [decodedTree] using he
  obtain ⟨hPE,hED,_,hQ⟩ := stagedTraversalReserve_layout parents G.n levels
  have hRec : records+6*kept.length ≤ lengths :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hsize) records).trans hrec
  have hadj : adj ≤ dist := by change adj+G.n+6*G.n ≤ lengths at hrec; omega
  have hqDist : queue+G.n ≤ dist := hQ.le.trans hadj
  have hdDist : depths+G.n ≤ dist := (Nat.le_add_right _ _).trans hqDist
  have heAdj : edges ≤ adj := by change edges+G.n+G.n+G.n < adj at hQ; omega
  exact buildTreeTables_pre_of_selected kept len dest staging (staging+G.m) adj records
    parents edges depths queue levels dist lengths L heap hv hindex hV hE hpost hTrav
    (by omega) le_rfl hRec hPE hED hdDist hqDist heAdj hLD hDH hheap
    hZeroDist hLen hFit

/-- One edge's stretch workspace has a quadratic limb allocation,
computed from the same division workspace as the stretch procedure. -/
def edgeStretchSpaceExpr (limbs : Expr) : Expr :=
  let add := Expr.bin .add
  let mul := Expr.bin .mul
  add (add (mul (.const 36) limbs) (.const 2))
    (mul (mul (.const 15) limbs) (add (mul (.const 3) limbs) (.const 1)))

/-- The runtime stride equals the stretch procedure's allocation formula. -/
theorem edgeStretchSpace_formula (L : ℕ) :
    edgeStretchSpace L = 36*L+2+15*L*(3*L+1) := by
  unfold edgeStretchSpace stretchFromLengthSpace Num.fixedDivideSpace
    Num.integerDivideSpace Num.unsignedDivideSpace
  ring

/-- Each calculation of the per-edge stretch stride fits if its
allocation does and the limb count is positive. -/
theorem edgeStretchSpaceExpr_eval {w : ℕ} {st : State} {e : Expr} (L : ℕ)
    (he : e.eval w st = some L) (hL : 0 < L) (hfit : edgeStretchSpace L < 2^w) :
    (edgeStretchSpaceExpr e).eval w st = some (edgeStretchSpace L) := by
  rw [edgeStretchSpace_formula] at hfit ⊢
  have h36 : 36*L < 2^w := (Nat.le_add_right _ _).trans_lt
    ((Nat.le_add_right _ _).trans_lt hfit)
  have hbase : 36*L+2 < 2^w := (Nat.le_add_right _ _).trans_lt hfit
  have hProd : 15*L*(3*L+1) < 2^w := (Nat.le_add_left _ _).trans_lt hfit
  have h15 : 15*L < 2^w := (Nat.le_mul_of_pos_right _ (by omega)).trans_lt hProd
  have h3p : 3*L+1 < 2^w :=
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) hL)).trans_lt hProd
  have h3 : 3*L < 2^w := by omega
  have hconst : 36 < 2^w := (Nat.le_mul_of_pos_right _ hL).trans_lt h36
  have h15c : 15 < 2^w := by omega
  have h3c : 3 < 2^w := by omega
  have h2c : 2 < 2^w := by omega
  have h1c : 1 < 2^w := by omega
  simp only [edgeStretchSpaceExpr,Expr.eval,BinOp.eval,he,h36,hbase,hProd,h15,h3p,h3,
    hconst,h15c,h3c,h2c,h1c,hfit,ite_eq_left]

/-- Extend the tree-table arguments with the compact edge arrays,
fixed-point precision, weight blocks, and runtime stretch stride. -/
def stagedStretchWeightArgs
    (n m levels cursor dist lengths limbs heap tails heads precision old stride denom : Expr) :
    List Expr :=
  stagedTreeTableBuildArgs n m levels cursor dist lengths limbs heap ++
    [tails,heads,precision,m,old,stride,denom,edgeStretchSpaceExpr limbs]

/-- The combined stretch and update receives the same rooted layout as
the selected tree and an edge workspace derived from its limb count. -/
theorem stagedStretchWeightArgs_eval {w : ℕ} {st : State}
    {ne me ke ce de ae le he te ye pe oe se be : Expr}
    (n m levels cursor dist lengths L heap tails heads P old stride denom : ℕ)
    (hn : ne.eval w st = some n) (hm : me.eval w st = some m)
    (hk : ke.eval w st = some levels) (hc : ce.eval w st = some cursor)
    (hd : de.eval w st = some dist) (ha : ae.eval w st = some lengths)
    (hL : le.eval w st = some L) (hh : he.eval w st = some heap)
    (ht : te.eval w st = some tails) (hy : ye.eval w st = some heads)
    (hP : pe.eval w st = some P) (ho : oe.eval w st = some old)
    (hs : se.eval w st = some stride) (hb : be.eval w st = some denom)
    (hnPos : 0 < n) (hLPos : 0 < L)
    (hfit : cursor+1+m+n+stagedTraversalReserve n levels < 2^w)
    (hstride : edgeStretchSpace L < 2^w) :
    let parents := cursor+1+m+n
    let edges := parents+(levels+1)*n
    let depths := edges+n
    let queue := depths+n
    let adj := parents+stagedTraversalReserve n levels
    evalArgs w st (stagedStretchWeightArgs ne me ke ce de ae le he te ye pe oe se be) =
      some [adj,parents,edges,depths,queue,0,n,levels,dist,lengths,L,heap,
        tails,heads,P,m,old,stride,denom,edgeStretchSpace L] := by
  intro parents edges depths queue adj
  have htable := stagedTreeTableBuildArgs_eval n m levels cursor dist lengths L heap
    hn hm hk hc hd ha hL hh hnPos hfit
  have hstrideEval := edgeStretchSpaceExpr_eval L hL hLPos hstride
  have hrest :
      evalArgs w st [te,ye,pe,me,oe,se,be,edgeStretchSpaceExpr le] =
        some [tails,heads,P,m,old,stride,denom,edgeStretchSpace L] := by
    simp only [evalArgs,ht,hy,hP,hm,ho,hs,hb,hstrideEval]
  exact Link.evalArgs_append htable hrest

/-- Invoke the combined numeric pass with the staged traversal layout.
Its return value and memory describe the rounded stretches and next weights. -/
theorem stagedStretchWeight_runs {w h Q entry result : ℕ} {p : Program} {ω : ℕ → Bool}
    {ne me ke ce de ae le he te ye pe oe se be : Expr}
    (st : State) (G T H : MGraph) (len : ℕ → ℤ)
    (j : ℕ) (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (n levels cursor dist lengths L heap tails heads P old stride denom : ℕ)
    (hn : ne.eval w st = some n) (hm : me.eval w st = some G.m)
    (hk : ke.eval w st = some levels) (hc : ce.eval w st = some cursor)
    (hd : de.eval w st = some dist) (ha : ae.eval w st = some lengths)
    (hL : le.eval w st = some L) (hh : he.eval w st = some heap)
    (ht : te.eval w st = some tails) (hy : ye.eval w st = some heads)
    (hP : pe.eval w st = some P) (ho : oe.eval w st = some old)
    (hs : se.eval w st = some stride) (hb : be.eval w st = some denom)
    (hnPos : 0 < n) (hLPos : 0 < L)
    (hfit : cursor+1+G.m+n+stagedTraversalReserve n levels < 2^w)
    (hstride : edgeStretchSpace L < 2^w) :
    let parents := cursor+1+G.m+n
    let edges := parents+(levels+1)*n
    let depths := edges+n
    let queue := depths+n
    let adj := parents+stagedTraversalReserve n levels
    let words := [adj,parents,edges,depths,queue,0,n,levels,dist,lengths,L,heap,
      tails,heads,P,G.m,old,stride,denom,edgeStretchSpace L]
    let args := stagedStretchWeightArgs ne me ke ce de ae le he te ye pe oe se be
    let C := stretchWeightRoundContract w h Q G T H 0 len adj parents edges
      depths queue n levels dist lengths L heap tails heads P old stride denom j scale query
    MeetsContract w p entry C → (∀ a ∈ words, a < 2^w) → C.pre words st.mem →
    ∃ out cost, Runs w p ω (.call result entry args) st .normal out cost ∧
      C.post words st.mem (out.regs result) out.mem ∧
      (∀ r, r ≠ result → out.regs r = st.regs r) ∧
      cost ≤ argsSize args+C.cost words st.mem+1 := by
  intro parents edges depths queue adj words args C hcall hwords hpre
  have hargs : evalArgs w st args = some words :=
    stagedStretchWeightArgs_eval n G.m levels cursor dist lengths L heap tails heads P old stride
      denom hn hm hk hc hd ha hL hh ht hy hP ho hs hb hnPos hLPos hfit hstride
  obtain ⟨out,cost,ret,hr,hpost,hret,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := result) hcall hargs hwords hpre ω
  exact ⟨out,cost,hr,hret.symm ▸ hpost,hregs,hcost⟩

/-- The numeric round uses the same staged traversal addresses as the
adjacency pass. Its numeric input blocks follow the incidence records. -/
theorem stretchWeight_pre_of_stagedAdjacency {w h Q : ℕ} (G T H : MGraph)
    (kept : List ℕ) (len : ℕ → ℤ)
    (staging dest levels dist lengths L heap tails heads P old stride denom j B : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (mem out : ℕ → ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (hdecode : decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T)
    (hnd : kept.Nodup) (hsize : kept.length ≤ G.n) (hw : 2 < 2^w)
    (hn : G.n ≤ 2^(levels+1)) (hRows : levels+1 < 2^w)
    (hTail : ListAt mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i))
    (hHead : ListAt mem heads (List.ofFn fun i : Fin G.m => (indexedGraph G).head i))
    (hLen : ∀ i < G.m, Num.Valid mem (lengths+i*L) h L ∧
      Num.intVal mem (lengths+i*L) h L = len i)
    (hBounds : ∀ i < G.m, 0 < len i ∧ len i ≤ (B : ℤ))
    (hCap : 2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (Num.capacity h L : ℤ))
    (hDenVal : Num.Valid mem denom h L ∧ Num.intVal mem denom h L = scale*(2 : ℤ)^P)
    (hWeights : ∀ i < H.m, Num.Valid mem (old+i*stride) h L ∧
      Num.fixVal mem (old+i*stride) h L P = weights P (scale : ℝ) query j (edgeName H i)) :
    let parents := dest+G.n
    let edges := parents+(levels+1)*G.n
    let depths := edges+G.n
    let queue := depths+G.n
    let adj := parents+stagedTraversalReserve G.n levels
    let records := adj+G.n
    let endRecords := records+6*G.n
    (selectedAdjacencyContract w (indexedGraph G) kept dest staging (staging+G.m)
      adj records).post [dest,staging,staging+G.m,adj,records,kept.length] mem 0 out →
    (∀ a, dest+G.n ≤ a → a < records → mem a = 0) →
    endRecords ≤ tails → endRecords ≤ heads → endRecords ≤ lengths →
    (∀ i < H.m, endRecords ≤ old+i*stride ∧ old+i*stride+L ≤ dist) →
    endRecords ≤ denom → denom+L ≤ dist →
    tails+G.m ≤ dist → heads+G.m ≤ dist → lengths+G.m*L ≤ dist →
    ZeroFrom mem dist → dist+G.n*L ≤ heap →
    heap+(G.n-1)*L+G.m*edgeStretchSpace L < 2^w →
    (stretchWeightRoundContract w h Q (indexedGraph G).toMGraph T H 0 len
      adj parents edges depths queue G.n levels dist lengths L heap tails heads P
      old stride denom j scale query).pre
      [adj,parents,edges,depths,queue,0,G.n,levels,dist,lengths,L,heap,tails,heads,P,G.m,
        old,stride,denom,edgeStretchSpace L] out := by
  intro parents edges depths queue adj records endRecords hpost hz ht hh hL hold
    hden hdenDist htDist hhDist hLD hzDist hDH hroom
  have hroot := indexedLSST_rooted_zero hv htree
  have hindex := (connectedDecodedTree_originals hv hconn (hdecode.symm ▸ htree)).2
  have hV : ∀ x, x ∈ T.V ↔ x < G.n := by
    intro x
    rw [← hdecode]
    exact Finset.mem_range
  have hE : ∀ e ∈ T.E, e < G.m := by
    intro e he
    apply hindex e
    rw [← hdecode] at he
    simpa [decodedTree] using he
  obtain ⟨hPE,hED,hDQ,hQ⟩ := stagedTraversalReserve_layout parents G.n levels
  have hrec : records+6*kept.length ≤ endRecords :=
    Nat.add_le_add_left (Nat.mul_le_mul_left 6 hsize) records
  have hd : mem depths = 0 := by
    apply hz
    · change parents ≤ edges+G.n
      exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    · change edges+G.n < adj+G.n
      change edges+G.n+G.n+G.n < adj at hQ
      omega
  have hheads : ∀ x < G.n, mem (adj+x) = 0 := by
    intro x hx
    exact hz _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
      (Nat.add_lt_add_left hx adj)
  exact selectedNumeric_pre kept len dest staging (staging+G.m) adj records parents edges
    depths queue adj levels dist lengths L heap tails heads P old stride denom j B scale query
    hv hroot hdecode hV hE hnd hpost hw le_rfl (hrec.trans ht) (hrec.trans hh) (hrec.trans hL)
    hPE hED hDQ hQ le_rfl htDist hhDist hLD hDH hroom hn hRows hd hheads hzDist
    hTail hHead hLen hBounds hCap
    (fun i hi => ⟨hrec.trans (hold i hi).1,(hold i hi).2⟩)
    ⟨hrec.trans hden,hdenDist⟩ hDenVal hWeights

/-- The fixed numeric argument list leaves the guest-format registers
available and takes the host numeric pointers from registers 17 through 26. -/
def stagedNumericArgsFrom (widthReg : ℕ) : List Expr :=
  stagedStretchWeightArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12)
    (.reg 17) (.reg 18) (.reg widthReg) (.reg 20) (.reg 21) (.reg 22)
    (.reg 23) (.reg 26) (.reg 24) (.reg 25)

/-- Numeric arguments for the caller-width pass. -/
def stagedNumericArgs : List Expr := stagedNumericArgsFrom 19

/-- The adjacency return register is disjoint from all runtime inputs
to the stretch and update call. -/
theorem stagedNumericArgsFrom_afterAdjacency {w : ℕ} (st mid : State) (widthReg : ℕ) (hwidthReg : widthReg ≠ 15)
    (hframe : mid.regs = Function.update st.regs 15 0)
    (n m levels cursor dist lengths L heap tails heads P old stride denom : ℕ)
    (hn : st.regs 0 = n) (hm : st.regs 1 = m) (hl : st.regs 14 = levels)
    (hc : st.regs 12 = cursor) (hd : st.regs 17 = dist) (ha : st.regs 18 = lengths)
    (hL : st.regs widthReg = L) (hh : st.regs 20 = heap) (ht : st.regs 21 = tails)
    (hy : st.regs 22 = heads) (hP : st.regs 23 = P) (ho : st.regs 26 = old)
    (hs : st.regs 24 = stride) (hb : st.regs 25 = denom)
    (hnPos : 0 < n) (hLPos : 0 < L)
    (hfit : cursor+1+m+n+stagedTraversalReserve n levels < 2^w)
    (hstride : edgeStretchSpace L < 2^w) :
    let parents := cursor+1+m+n
    let edges := parents+(levels+1)*n
    let depths := edges+n
    let queue := depths+n
    let adj := parents+stagedTraversalReserve n levels
    evalArgs w mid (stagedNumericArgsFrom widthReg) =
      some [adj,parents,edges,depths,queue,0,n,levels,dist,lengths,L,heap,
        tails,heads,P,m,old,stride,denom,edgeStretchSpace L] := by
  intro parents edges depths queue adj
  unfold stagedNumericArgsFrom
  refine stagedStretchWeightArgs_eval n m levels cursor dist lengths L heap tails heads P
    old stride denom ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hnPos hLPos hfit hstride
  all_goals simp [Expr.eval,hframe,hwidthReg,hn,hm,hl,hc,hd,ha,hL,hh,ht,hy,hP,ho,hs,hb]

/-- The adjacency return register is disjoint from all runtime inputs
to the stretch and update call. -/
theorem stagedNumericArgs_afterAdjacency {w : ℕ} (st mid : State)
    (hframe : mid.regs = Function.update st.regs 15 0)
    (n m levels cursor dist lengths L heap tails heads P old stride denom : ℕ)
    (hn : st.regs 0 = n) (hm : st.regs 1 = m) (hl : st.regs 14 = levels)
    (hc : st.regs 12 = cursor) (hd : st.regs 17 = dist) (ha : st.regs 18 = lengths)
    (hL : st.regs 19 = L) (hh : st.regs 20 = heap) (ht : st.regs 21 = tails)
    (hy : st.regs 22 = heads) (hP : st.regs 23 = P) (ho : st.regs 26 = old)
    (hs : st.regs 24 = stride) (hb : st.regs 25 = denom)
    (hnPos : 0 < n) (hLPos : 0 < L)
    (hfit : cursor+1+m+n+stagedTraversalReserve n levels < 2^w)
    (hstride : edgeStretchSpace L < 2^w) :
    let parents := cursor+1+m+n
    let edges := parents+(levels+1)*n
    let depths := edges+n
    let queue := depths+n
    let adj := parents+stagedTraversalReserve n levels
    evalArgs w mid stagedNumericArgs =
      some [adj,parents,edges,depths,queue,0,n,levels,dist,lengths,L,heap,
        tails,heads,P,m,old,stride,denom,edgeStretchSpace L] := by
  exact stagedNumericArgsFrom_afterAdjacency st mid 19 (by decide) hframe
    n m levels cursor dist lengths L heap tails heads P old stride denom
    hn hm hl hc hd ha hL hh ht hy hP ho hs hb hnPos hLPos hfit hstride

end MinCostFlow.LastLevelProgram
