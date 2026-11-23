module

public import MinCostFlow.LastLevelProgram.StagedRootedTraversal
import WordRAM.Tactic
import WordRAM.Link
import Mathlib.Tactic

/-!
# Running the staged numeric pass

The Definition 5.8 rebuild (pages 19–20) prepares its numeric inputs, computes stretches, and updates weights.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM LSF WideWord

/-- Build adjacency, then compute and store the rounded stretches and
the next multiplicative weights using the rooted tree tables. -/
def stagedNumericBodyFrom (adjacency numeric widthReg : ℕ) : Stmt :=
  .seq (.call 15 adjacency
    (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
      (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)))
    (.call 16 numeric (stagedNumericArgsFrom widthReg))

/-- Use the caller width for an unwidened numeric pass. -/
def stagedNumericBody (adjacency numeric : ℕ) : Stmt := stagedNumericBodyFrom adjacency numeric 19

/-- The staged numeric body charges one adjacency pass and one combined
stretch and update pass. The memory handoff is expressed by their contracts. -/
theorem stagedNumericFrom_runs {w adjacency numeric insert : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G T : MGraph) (L staging cursor levels count widthReg : ℕ)
    (mem : ℕ → ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (he : p.procs[adjacency]? = some (selectedAdjacencyBody insert))
    (hi : MeetsContract w p insert (pushTreeEdgeContract w))
    (hw : 6 < 2^w) (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (ha : st.regs 5 = staging)
    (hc : st.regs 12 = cursor) (hl : st.regs 14 = levels) (hk : st.regs 13 = count)
    (hnPos : 0 < G.n)
    (C : Contract) (words : List ℕ) (budget : ℕ)
    (hC : MeetsContract w p numeric C)
    (hwords : ∀ x ∈ words, x < 2^w)
    (hargs : ∀ mid, mid.regs = Function.update st.regs 15 0 →
      evalArgs w mid (stagedNumericArgsFrom widthReg) = some words) :
    let dest := cursor+1+G.m
    let adj := dest+G.n+stagedTraversalReserve G.n levels
    let records := adj+G.n
    retainedStagedTreeAt G T (staging+queryWeights G L) dest count mem st.mem →
    staging+queryWeights G L ≤ dest → records+6*G.n < 2^w →
    (∀ kept mid, count = kept.length → kept.Nodup →
      decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T →
      (selectedAdjacencyContract w (indexedGraph G) kept dest staging (staging+G.m)
        adj records).post [dest,staging,staging+G.m,adj,records,count] st.mem 0 mid →
      C.pre words mid ∧ C.cost words mid ≤ budget) →
    ∃ (mid out : State) (cost : ℕ),
      Runs w p ω (stagedNumericBodyFrom adjacency numeric widthReg) st .normal out cost ∧
      C.post words mid.mem (out.regs 16) out.mem ∧
      (∀ a < adj, mid.mem a = st.mem a) ∧
      (∀ r, r ≠ 15 → r ≠ 16 → out.regs r = st.regs r) ∧
      cost ≤ argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
        (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
        argsSize (stagedNumericArgsFrom widthReg)+112*count+budget+13 := by
  intro dest adj records hTree hsep hroom hnext
  obtain ⟨mid,ca,kept,har,hcount,hnd,hdecode,hpost,hframe,_,hregs,hca⟩ :=
    stagedAdjacency_runs (ω := ω) (result := 15) st G T L staging cursor levels count
      mem ℓ v γ he hi hw hv hconn htree ht hh hn hm ha hc hl hk hnPos hTree hsep hroom
  obtain ⟨hpre,hbudget⟩ := hnext kept mid.mem hcount hnd hdecode hpost
  obtain ⟨out,cn,ret,hnr,hpost',hret,hregs',hcn⟩ :=
    runs_call_of_meetsContract (r := 16) hC (hargs mid hregs) hwords hpre ω
  refine ⟨mid,out,ca+cn+1,runs_seq_iff.mpr (Or.inr ⟨mid,ca,cn,har,hnr,rfl⟩),
    hret.symm ▸ hpost',hframe,?_,by omega⟩
  intro r hr₁ hr₂
  rw [hregs' r hr₂,hregs,Function.update_of_ne hr₁]

/-- The staged numeric body charges one adjacency pass and one combined
stretch and update pass. The memory handoff is expressed by their contracts. -/
theorem stagedNumeric_runs {w adjacency numeric insert : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G T : MGraph) (L staging cursor levels count : ℕ)
    (mem : ℕ → ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (he : p.procs[adjacency]? = some (selectedAdjacencyBody insert))
    (hi : MeetsContract w p insert (pushTreeEdgeContract w))
    (hw : 6 < 2^w) (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (ha : st.regs 5 = staging)
    (hc : st.regs 12 = cursor) (hl : st.regs 14 = levels) (hk : st.regs 13 = count)
    (hnPos : 0 < G.n)
    (C : Contract) (words : List ℕ) (budget : ℕ)
    (hC : MeetsContract w p numeric C)
    (hwords : ∀ x ∈ words, x < 2^w)
    (hargs : ∀ mid, mid.regs = Function.update st.regs 15 0 →
      evalArgs w mid stagedNumericArgs = some words) :
    let dest := cursor+1+G.m
    let adj := dest+G.n+stagedTraversalReserve G.n levels
    let records := adj+G.n
    retainedStagedTreeAt G T (staging+queryWeights G L) dest count mem st.mem →
    staging+queryWeights G L ≤ dest → records+6*G.n < 2^w →
    (∀ kept mid, count = kept.length → kept.Nodup →
      decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T →
      (selectedAdjacencyContract w (indexedGraph G) kept dest staging (staging+G.m)
        adj records).post [dest,staging,staging+G.m,adj,records,count] st.mem 0 mid →
      C.pre words mid ∧ C.cost words mid ≤ budget) →
    ∃ (mid out : State) (cost : ℕ),
      Runs w p ω (stagedNumericBody adjacency numeric) st .normal out cost ∧
      C.post words mid.mem (out.regs 16) out.mem ∧
      (∀ a < adj, mid.mem a = st.mem a) ∧
      (∀ r, r ≠ 15 → r ≠ 16 → out.regs r = st.regs r) ∧
      cost ≤ argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
        (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
        argsSize stagedNumericArgs+112*count+budget+13 := by
  exact stagedNumericFrom_runs st G T L staging cursor levels count 19 mem ℓ v γ
    he hi hw hv hconn htree ht hh hn hm ha hc hl hk hnPos C words budget hC hwords hargs

/-- The cost of one numeric pass is linear in the edge count up to
the limb arithmetic and binary lifting factors. -/
def stagedNumericFactor (L levels : ℕ) : ℕ :=
  114+35+(55*L+75)+60*levels+
    (86*(levels+1)+edgeStretchCost L+126)+(narrowWeightCost L+30)+186

/-- The numeric contract has a memory-independent budget. On connected
inputs with equal compact and named edge counts it is bounded by the
same explicit factor times the edge count plus one. -/
theorem stagedNumeric_cost_le {w h Q : ℕ} (G T H : MGraph) (len : ℕ → ℤ)
    (adj parents edges depths queue n levels dist lengths L heap tails heads P old stride denom j : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ) (mem : ℕ → ℕ) (args : List ℕ)
    (hE : T.E.card ≤ n) (hV : T.V.card ≤ n) (hn : n ≤ G.m+1) (hm : H.m = G.m) :
    (stretchWeightRoundContract w h Q G T H 0 len adj parents edges depths queue n levels
      dist lengths L heap tails heads P old stride denom j scale query).cost args mem ≤
      stagedNumericFactor L levels*(G.m+1) := by
  let M := G.m+1
  have hm' : G.m ≤ M := Nat.le_succ _
  have hM : 1 ≤ M := Nat.succ_pos _
  have hl : 20*n+40 ≤ 60*M := by
    have h₁ := Nat.mul_le_mul_left 20 hn
    have h₂ := Nat.mul_le_mul_left 40 hM
    omega
  change 114*T.E.card+35*T.V.card+(55*L+75)*(n-1)+(20*n+40)*levels+
    (86*(levels+1)+edgeStretchCost L+126)*G.m+126+
    (narrowWeightCost L+30)*H.m+60 ≤ stagedNumericFactor L levels*M
  rw [hm]
  calc
    _ ≤ 114*M+35*M+(55*L+75)*M+60*levels*M+
        (86*(levels+1)+edgeStretchCost L+126)*M+126*M+
        (narrowWeightCost L+30)*M+60*M := by
      have hlevel : (20*n+40)*levels ≤ 60*levels*M := by
        simpa [Nat.mul_right_comm] using Nat.mul_le_mul_right levels hl
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.mul_le_mul_left 114 (hE.trans hn)) (Nat.mul_le_mul_left 35 (hV.trans hn)))
          (Nat.mul_le_mul_left _ ((Nat.sub_le n 1).trans hn))) hlevel)
        (Nat.mul_le_mul_left _ hm')) (by simpa using Nat.mul_le_mul_left 126 hM))
        (Nat.mul_le_mul_left _ hm')) (by simpa using Nat.mul_le_mul_left 60 hM)
    _ = stagedNumericFactor L levels*M := by unfold stagedNumericFactor; ring

/-- For the runtime numeric layout, adjacency changes neither the
call arguments nor the explicit linear budget for the numeric pass. -/
theorem stagedNumericRound_runs {w h Q adjacency numeric insert : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G T H : MGraph) (L staging cursor levels count widthReg : ℕ) (hwidthReg : widthReg ≠ 15)
    (mem : ℕ → ℕ) (ℓ v : ℕ → ℝ) (γ : ℝ)
    (he : p.procs[adjacency]? = some (selectedAdjacencyBody insert))
    (hi : MeetsContract w p insert (pushTreeEdgeContract w))
    (hw : 6 < 2^w) (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (ha : st.regs 5 = staging)
    (hc : st.regs 12 = cursor) (hl : st.regs 14 = levels) (hk : st.regs 13 = count)
    (hnPos : 0 < G.n)
    (dist lengths N heap tails heads P old stride denom j : ℕ)
    (len : ℕ → ℤ) (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hd : st.regs 17 = dist) (hLen : st.regs 18 = lengths) (hN : st.regs widthReg = N)
    (hheap : st.regs 20 = heap) (htail : st.regs 21 = tails) (hhead : st.regs 22 = heads)
    (hP : st.regs 23 = P) (ho : st.regs 26 = old) (hs : st.regs 24 = stride)
    (hb : st.regs 25 = denom) (hNPos : 0 < N)
    (hE : T.E.card ≤ G.n) (hV : T.V.card ≤ G.n) (hnm : G.n ≤ G.m+1)
    (heq : H.m = G.m) :
    let dest := cursor+1+G.m
    let parents := dest+G.n
    let edges := parents+(levels+1)*G.n
    let depths := edges+G.n
    let queue := depths+G.n
    let adj := parents+stagedTraversalReserve G.n levels
    let records := adj+G.n
    let words := [adj,parents,edges,depths,queue,0,G.n,levels,dist,lengths,N,heap,
      tails,heads,P,G.m,old,stride,denom,edgeStretchSpace N]
    let C := stretchWeightRoundContract w h Q (indexedGraph G).toMGraph T H 0 len
      adj parents edges depths queue G.n levels dist lengths N heap tails heads P
      old stride denom j scale query
    MeetsContract w p numeric C → (∀ x ∈ words, x < 2^w) →
    retainedStagedTreeAt G T (staging+queryWeights G L) dest count mem st.mem →
    staging+queryWeights G L ≤ dest → records+6*G.n < 2^w →
    (∀ kept mid, count = kept.length → kept.Nodup →
      decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T →
      (selectedAdjacencyContract w (indexedGraph G) kept dest staging (staging+G.m)
        adj records).post [dest,staging,staging+G.m,adj,records,count] st.mem 0 mid →
      C.pre words mid) →
    ∃ (mid out : State) (cost : ℕ),
      Runs w p ω (stagedNumericBodyFrom adjacency numeric widthReg) st .normal out cost ∧
      C.post words mid.mem (out.regs 16) out.mem ∧
      (∀ a < adj, mid.mem a = st.mem a) ∧
      (∀ r, r ≠ 15 → r ≠ 16 → out.regs r = st.regs r) ∧
      cost ≤ argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
        (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
        argsSize (stagedNumericArgsFrom widthReg)+112*count+stagedNumericFactor N levels*(G.m+1)+13 := by
  intro dest parents edges depths queue adj records words C hC hwords hTree hsep hroom hnext
  have hfit : adj < 2^w := hwords _ (by simp [words])
  have hstride : edgeStretchSpace N < 2^w := hwords _ (by simp [words])
  refine stagedNumericFrom_runs (ω := ω) st G T L staging cursor levels count widthReg mem ℓ v γ
    he hi hw hv hconn htree ht hh hn hm ha hc hl hk hnPos C words
    (stagedNumericFactor N levels*(G.m+1)) hC hwords ?_ hTree hsep hroom ?_
  · intro mid hregs
    exact stagedNumericArgsFrom_afterAdjacency st mid widthReg hwidthReg hregs G.n G.m levels cursor dist lengths N
      heap tails heads P old stride denom hn hm hl hc hd hLen hN hheap htail hhead hP
      ho hs hb hnPos hNPos hfit hstride
  · intro kept mid hcount hnd hdecode hpost
    refine ⟨hnext kept mid hcount hnd hdecode hpost,?_⟩
    have hmCompact : (indexedGraph G).toMGraph.m = G.m := IndexedGraph.toMGraph_m _
    have hbnd := stagedNumeric_cost_le (w := w) (h := h) (Q := Q)
      (indexedGraph G).toMGraph T H len adj parents edges depths queue G.n levels dist lengths N
      heap tails heads P old stride denom j scale query mid words hE hV
      (by rw [hmCompact]; exact hnm) (heq.trans hmCompact.symm)
    rw [hmCompact] at hbnd
    exact hbnd

/-- Both compact endpoint arrays are contiguous, so one copy places
them in the numeric input region after the incidence records. -/
def stagedNumericEndpointArgs : List Expr :=
  [.reg 5,.reg 21,.bin .add (.reg 1) (.reg 1)]

/-- A single copy supplies the numeric pass's compact endpoint arrays. -/
theorem stagedNumericEndpoints_runs {w copy result : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (staging dst : ℕ)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hs : st.regs 5 = staging) (hd : st.regs 21 = dst) (hm : st.regs 1 = G.m)
    (hw : 1 < 2^w) (hsep : staging+2*G.m ≤ dst) (hroom : dst+2*G.m < 2^w)
    (ht : ∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i) :
    ∃ out cost, Runs w p ω (.call result copy stagedNumericEndpointArgs) st .normal out cost ∧
      ListAt out.mem dst (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) ∧
      ListAt out.mem (dst+G.m) (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) ∧
      (∀ a, a < dst ∨ dst+2*G.m ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ result → out.regs r = st.regs r) ∧ cost ≤ 34*G.m+16 := by
  have hlength : G.m+G.m = 2*G.m := by omega
  have hdst : dst < 2^w := by omega
  have hst : staging < 2^w := by omega
  have hlen : 2*G.m < 2^w := by omega
  have hargs : evalArgs w st stagedNumericEndpointArgs = some [staging,dst,2*G.m] := by
    simp only [stagedNumericEndpointArgs,evalArgs,Expr.eval,BinOp.eval,hs,hd,hm,
      hlength,hlen,ite_eq_left]
  obtain ⟨out,cost,ret,hr,hpost,_,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := result) hcopy hargs (by wram_words)
      ⟨staging,dst,2*G.m,rfl,hw,by omega,hroom.le,Or.inr hsep⟩ ω
  obtain ⟨src,dest,count,he,_,hc,hframe⟩ := hpost
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl⟩ := he
  refine ⟨out,cost,hr,?_,?_,hframe,hregs,?_⟩
  · intro i hi
    have hi' : i < G.m := by simpa using hi
    simpa using (hc i (by omega)).trans (ht i hi')
  · intro i hi
    have hi' : i < G.m := by simpa using hi
    simpa [Nat.add_assoc] using (hc (G.m+i) (by omega)).trans (hh i hi')
  · change cost ≤ 5+(17*(2*G.m)+10)+1 at hcost
    omega

/-- Pack the caller's lengths into the numeric area using the staged
edge-name array. The guest conversion uses its own length array. -/
def stagedNumericLengthArgs : List Expr :=
  [.reg 27,.reg 18,.reg 28,.reg 19,.reg 1]

/-- The host-format packing call preserves endpoints and produces a
compact length table with the same numerator and limb count. -/
theorem stagedNumericLengths_runs {w h cap pack result : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (src dst names L : ℕ) (len : ℕ → ℤ)
    (hp : MeetsContract w p pack (packValuesContract w cap G))
    (hs : st.regs 27 = src) (hd : st.regs 18 = dst) (hn : st.regs 28 = names)
    (hL : st.regs 19 = L) (hm : st.regs 1 = G.m)
    (hwords : ∀ x ∈ [src,dst,names,L,G.m], x < 2^w)
    (hpre : (packValuesContract w cap G).pre [src,dst,names,L,G.m] st.mem)
    (hsrc : ∀ e ∈ G.E, Num.Valid st.mem (src+e*L) h L ∧
      Num.intVal st.mem (src+e*L) h L = len e)
    (hz : ZeroFrom st.mem dst) :
    ∃ out cost, Runs w p ω (.call result pack stagedNumericLengthArgs) st .normal out cost ∧
      (∀ i < G.m, Num.Valid out.mem (dst+i*L) h L ∧
        Num.intVal out.mem (dst+i*L) h L = len (edgeName G i)) ∧
      (∀ a < dst, out.mem a = st.mem a) ∧ ZeroFrom out.mem (dst+G.m*L) ∧
      (∀ r, r ≠ result → out.regs r = st.regs r) ∧ cost ≤ (17*L+41)*G.m+16 := by
  have hargs : evalArgs w st stagedNumericLengthArgs = some [src,dst,names,L,G.m] := by
    simp only [stagedNumericLengthArgs,evalArgs,Expr.eval,hs,hd,hn,hL,hm]
  obtain ⟨out,cost,ret,hr,hpost,_,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := result) hp hargs hwords hpre ω
  obtain ⟨hlens,hframe,hzero⟩ :=
    packedLengths_of_packValues src dst names L ret len st.mem out.mem hpost hsrc hz
  exact ⟨out,cost,hr,hlens,hframe,hzero,hregs,by
    change cost ≤ 5+((17*L+41)*G.m+10)+1 at hcost
    omega⟩

/-- Copy endpoints first and pack the lengths immediately after them. -/
def stagedNumericInputsBody (copy pack : ℕ) : Stmt :=
  .seq (.call 29 copy stagedNumericEndpointArgs) (.call 30 pack stagedNumericLengthArgs)

/-- The numeric input calls allocate adjacent endpoint and length arrays,
preserve the input prefix, and leave fresh memory for the next blocks. -/
theorem stagedNumericInputs_runs {w h cap copy pack : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (staging dst src names L : ℕ) (len : ℕ → ℤ)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hp : MeetsContract w p pack (packValuesContract w cap G))
    (hStage : st.regs 5 = staging) (hDst : st.regs 21 = dst)
    (hLength : st.regs 18 = dst+2*G.m) (hSrc : st.regs 27 = src)
    (hNames : st.regs 28 = names) (hL : st.regs 19 = L) (hm : st.regs 1 = G.m)
    (hw : 1 < 2^w) (hlimbs : L < 2^w)
    (hsep : staging+2*G.m ≤ dst) (hsrc : src ≤ dst ∧ ∀ e ∈ G.E, src+e*L+L ≤ dst) (hnames : names+G.m ≤ dst)
    (hroom : dst+2*G.m+G.m*L < 2^w)
    (ht : ∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hat : ∀ i < G.m, st.mem (names+i) = edgeName G i)
    (hcap : ∀ e ∈ G.E, e < cap)
    (hl : ∀ e ∈ G.E, Num.Valid st.mem (src+e*L) h L ∧
      Num.intVal st.mem (src+e*L) h L = len e)
    (hz : ZeroFrom st.mem dst) :
    let lengths := dst+2*G.m
    ∃ out cost, Runs w p ω (stagedNumericInputsBody copy pack) st .normal out cost ∧
      ListAt out.mem dst (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) ∧
      ListAt out.mem (dst+G.m) (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) ∧
      (∀ i < G.m, Num.Valid out.mem (lengths+i*L) h L ∧
        Num.intVal out.mem (lengths+i*L) h L = len (edgeName G i)) ∧
      (∀ a < dst, out.mem a = st.mem a) ∧ ZeroFrom out.mem (lengths+G.m*L) ∧
      (∀ r, r ≠ 29 → r ≠ 30 → out.regs r = st.regs r) ∧
      cost ≤ (17*L+75)*G.m+33 := by
  intro lengths
  have hptr : lengths < 2^w := (Nat.le_add_right _ _).trans_lt hroom
  obtain ⟨mid,ce,he,ht',hh',hf,hr,hce⟩ :=
    stagedNumericEndpoints_runs (ω := ω) (result := 29) st G staging dst
      hc hStage hDst hm hw hsep hptr ht hh
  have hsrc' : ∀ e ∈ G.E, Num.Valid mid.mem (src+e*L) h L ∧
      Num.intVal mid.mem (src+e*L) h L = len e := by
    intro e he
    obtain ⟨hv,hval⟩ := hl e he
    have hblock := hsrc.2 e he
    have hs (k : ℕ) (hk : k < L) :=
      hf (src+e*L+k) (Or.inl (by omega))
    exact ⟨fun k hk => (hs k hk).trans_lt (hv k hk),
      (Num.intVal_congr hs).trans hval⟩
  have hsrcBase := hsrc.1
  have hwords : ∀ a ∈ [src,lengths,names,L,G.m], a < 2^w := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> dsimp [lengths] at * <;> omega
  have hpre : (packValuesContract w cap G).pre [src,lengths,names,L,G.m] mid.mem :=
    ⟨src,lengths,names,L,rfl,hw,hlimbs,by dsimp [lengths] at hptr; omega,
      ⟨by dsimp [lengths]; omega,fun e he => (hsrc.2 e he).trans (Nat.le_add_right _ _)⟩,
      by dsimp [lengths]; omega,hroom,
      fun i hi => (hf _ (Or.inl (by omega))).trans (hat i hi),hcap⟩
  obtain ⟨out,cl,hrun,hl',hf',hz',hregs,hcl⟩ :=
    stagedNumericLengths_runs (ω := ω) (result := 30) mid G src lengths names L len hp
      ((hr _ (by decide)).trans hSrc) ((hr _ (by decide)).trans hLength)
      ((hr _ (by decide)).trans hNames) ((hr _ (by decide)).trans hL)
      ((hr _ (by decide)).trans hm) hwords hpre hsrc'
      (fun a ha => (hf a (Or.inr ha)).trans (hz a (by dsimp [lengths] at ha; omega)))
  refine ⟨out,ce+cl+1,runs_seq_iff.mpr (Or.inr ⟨mid,ce,cl,he,hrun,rfl⟩),
    ?_,?_,hl',?_,hz',?_,?_⟩
  · intro i hi
    have hi' : i < G.m := by simpa using hi
    exact (hf' _ (by dsimp [lengths]; omega)).trans (ht' i hi)
  · intro i hi
    have hi' : i < G.m := by simpa using hi
    exact (hf' _ (by dsimp [lengths]; omega)).trans (hh' i hi)
  · intro a ha
    exact (hf' a (by dsimp [lengths]; omega)).trans (hf a (Or.inl ha))
  · intro r h29 h30
    exact (hregs r h30).trans (hr r h29)
  · simp only [Nat.add_mul] at hcl ⊢
    omega

/-- Gather the old host weights after the compact length array. The
source stride and destination are independent of the guest input. -/
def stagedHostWeightArgs : List Expr :=
  [.reg 31,.reg 32,.reg 19,.reg 1,.const 0,.reg 26]

/-- Packing old weights preserves their fixed-point values for the
numeric round and leaves a fresh suffix for the denominator. -/
theorem stagedHostWeights_runs {w h P pack result : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (m L src stride dst : ℕ)
    (hpack : MeetsContract w p pack (packHostWeightsContract w h P))
    (hm : st.regs 1 = m) (hL : st.regs 19 = L) (hs : st.regs 31 = src)
    (hstride : st.regs 32 = stride) (hd : st.regs 26 = dst)
    (hwords : ∀ x ∈ [src,stride,L,m,0,dst], x < 2^w)
    (hpre : (packHostWeightsContract w h P).pre [src,stride,L,m,0,dst] st.mem) :
    ∃ out cost, Runs w p ω (.call result pack stagedHostWeightArgs) st .normal out cost ∧
      out.regs result = dst+m*L ∧ ZeroFrom out.mem (dst+m*L) ∧
      (∀ a < dst, out.mem a = st.mem a) ∧
      (∀ i < m, Num.Valid out.mem (dst+i*L) h L ∧
        Num.fixVal out.mem (dst+i*L) h L P = Num.fixVal st.mem (src+i*stride) h L P) ∧
      (∀ r, r ≠ result → out.regs r = st.regs r) ∧ cost ≤ (35*L+60)*m+17 := by
  have hargs : evalArgs w st stagedHostWeightArgs = some [src,stride,L,m,0,dst] := by
    simp [stagedHostWeightArgs,evalArgs,Expr.eval,hm,hL,hs,hstride,hd]
  obtain ⟨out,cost,ret,hr,hpost,hret,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := result) hpack hargs hwords hpre ω
  obtain ⟨a,S,N,k,b,he,hend,hzero,hframe,hblocks⟩ := hpost
  simp only [List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := he
  refine ⟨out,cost,hr,hret.trans hend,hend ▸ hzero,hframe,hblocks,hregs,?_⟩
  change cost ≤ 6+((35*L+60)*m+10)+1 at hcost
  omega

/-- Gather old weights and append the denominator using the returned
weight-allocation cursor. -/
def stagedWeightsDenominatorBody (pack prepare : ℕ) : Stmt :=
  .seq (.call 33 pack stagedHostWeightArgs)
    (.call 34 prepare [.reg 35,.reg 19,.reg 23,.reg 33])

/-- The combined preparation preserves the weight values and places the
scaled denominator in the next block, leaving the distance region fresh. -/
theorem stagedWeightsDenominator_runs {w h P pack prepare : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (m L src stride dst scale : ℕ)
    (hpack : MeetsContract w p pack (packHostWeightsContract w h P))
    (hprepare : MeetsContract w p prepare (denominatorContract w h))
    (hm : st.regs 1 = m) (hL : st.regs 19 = L) (hs : st.regs 31 = src)
    (hstride : st.regs 32 = stride) (hd : st.regs 26 = dst)
    (hP : st.regs 23 = P) (hscale : st.regs 35 = scale)
    (hwords : ∀ x ∈ [src,stride,L,m,0,dst], x < 2^w)
    (hpre : (packHostWeightsContract w h P).pre [src,stride,L,m,0,dst] st.mem)
    (hscaleFit : scale < 2^w) (hPFit : P < 2^w)
    (hfit : Num.Fits h L (scale : ℤ))
    (hscaled : Num.Fits h L ((scale : ℤ)*(2 : ℤ)^P))
    (hroom : dst+m*L+2*L < 2^w) :
    let base := dst+m*L
    ∃ out cost, Runs w p ω (stagedWeightsDenominatorBody pack prepare) st .normal out cost ∧
      out.regs 34 = base+2*L ∧ ZeroFrom out.mem (base+2*L) ∧
      Num.Valid out.mem (base+L) h L ∧
      Num.intVal out.mem (base+L) h L = (scale : ℤ)*(2 : ℤ)^P ∧
      (∀ a < dst, out.mem a = st.mem a) ∧
      (∀ i < m, Num.Valid out.mem (dst+i*L) h L ∧
        Num.fixVal out.mem (dst+i*L) h L P = Num.fixVal st.mem (src+i*stride) h L P) ∧
      (∀ r, r ≠ 33 → r ≠ 34 → out.regs r = st.regs r) ∧
      cost ≤ (35*L+60)*m+56*L+85 := by
  intro base
  obtain ⟨mid,cw,hr,hbase,hzero,hframe,hblocks,hregs,hcw⟩ :=
    stagedHostWeights_runs (ω := ω) (result := 33) st m L src stride dst hpack
      hm hL hs hstride hd hwords hpre
  have hArgs : evalArgs w mid [.reg 35,.reg 19,.reg 23,.reg 33] = some [scale,L,P,base] := by
    simp [evalArgs,Expr.eval,hregs 35 (by decide),hregs 19 (by decide),
      hregs 23 (by decide),hL,hP,hscale,hbase,base]
  have hLFit := hwords L (by simp)
  have hbaseFit : base < 2^w := (Nat.le_add_right _ _).trans_lt hroom
  obtain ⟨out,cd,ret,hdRun,hpost,hret,hregs',hcd⟩ :=
    runs_call_of_meetsContract (r := 34) hprepare hArgs (by wram_words)
      ⟨scale,L,P,base,rfl,hfit,hscaled,hzero,hroom⟩ ω
  obtain ⟨s,k,q,b,he,hcursor,hvalid,hval,hframe',hz⟩ := hpost
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  refine ⟨out,cw+cd+1,runs_seq_iff.mpr (Or.inr ⟨mid,cw,cd,hr,hdRun,rfl⟩),
    hret.trans hcursor,hcursor ▸ hz,hvalid,hval,?_,?_,?_,?_⟩
  · intro a ha
    exact (hframe' a (ha.trans_le (Nat.le_add_right _ _))).trans (hframe a ha)
  · intro i hi
    obtain ⟨hv,he⟩ := hblocks i hi
    have hblock : dst+i*L+L ≤ base := by
      have h := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at h
      dsimp [base]
      omega
    have hf (k : ℕ) (hk : k < L) := hframe' (dst+i*L+k) (by omega)
    refine ⟨fun k hk => (hf k hk).trans_lt (hv k hk),?_⟩
    unfold Num.fixVal at he ⊢
    rw [Num.intVal_congr hf]
    exact he
  · intro r hr₃ hr₄
    exact (hregs' r hr₄).trans (hregs r hr₃)
  · change cd ≤ 4+(56*L+62)+1 at hcd
    omega

/-- Prepare compact host inputs in consecutive allocations before the
distance and stretch workspace. -/
def stagedNumericPreparationBody (copy packLengths packWeights prepare : ℕ) : Stmt :=
  .seq (stagedNumericInputsBody copy packLengths)
    (stagedWeightsDenominatorBody packWeights prepare)

/-- Endpoint and length packing, weight packing, and denominator
preparation share an allocation without changing any source values. -/
theorem stagedNumericPreparation_runs {w h P cap copy pack packWeights prepare : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (staging dst src names L : ℕ) (len : ℕ → ℤ)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hp : MeetsContract w p pack (packValuesContract w cap G))
    (hStage : st.regs 5 = staging) (hDst : st.regs 21 = dst)
    (hLength : st.regs 18 = dst+2*G.m) (hSrc : st.regs 27 = src)
    (hNames : st.regs 28 = names) (hL : st.regs 19 = L) (hm : st.regs 1 = G.m)
    (hw : 1 < 2^w) (hlimbs : L < 2^w)
    (hsep : staging+2*G.m ≤ dst) (hsrc : src ≤ dst ∧ ∀ e ∈ G.E, src+e*L+L ≤ dst) (hnames : names+G.m ≤ dst)
    (hroom : dst+2*G.m+G.m*L < 2^w)
    (ht : ∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hat : ∀ i < G.m, st.mem (names+i) = edgeName G i)
    (hcap : ∀ e ∈ G.E, e < cap)
    (hl : ∀ e ∈ G.E, Num.Valid st.mem (src+e*L) h L ∧
      Num.intVal st.mem (src+e*L) h L = len e)
    (hz : ZeroFrom st.mem dst)
    (weightSrc weightStride scale : ℕ)
    (hpack : MeetsContract w p packWeights (packHostWeightsContract w h P))
    (hprep : MeetsContract w p prepare (denominatorContract w h))
    (hWeight : st.regs 31 = weightSrc) (hStride : st.regs 32 = weightStride)
    (hOld : st.regs 26 = dst+2*G.m+G.m*L) (hScale : st.regs 35 = scale)
    (hP : st.regs 23 = P) (hwordStride : weightStride < 2^w)
    (hsepWeight : weightSrc+(G.m-1)*weightStride+L ≤ dst) (hLS : L ≤ weightStride)
    (hvalid : ∀ i < G.m, Num.Valid st.mem (weightSrc+i*weightStride) h L)
    (hscaleFit : scale < 2^w) (hPFit : P < 2^w)
    (hfit : Num.Fits h L (scale : ℤ))
    (hscaled : Num.Fits h L ((scale : ℤ)*(2 : ℤ)^P))
    (hroomAll : dst+2*G.m+G.m*L+G.m*L+2*L < 2^w) :
    let lengths := dst+2*G.m
    let old := lengths+G.m*L
    let denom := old+G.m*L+L
    let dist := old+G.m*L+2*L
    ∃ out cost, Runs w p ω (stagedNumericPreparationBody copy pack packWeights prepare)
      st .normal out cost ∧
      ListAt out.mem dst (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) ∧
      ListAt out.mem (dst+G.m) (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) ∧
      (∀ i < G.m, Num.Valid out.mem (lengths+i*L) h L ∧
        Num.intVal out.mem (lengths+i*L) h L = len (edgeName G i)) ∧
      (∀ i < G.m, Num.Valid out.mem (old+i*L) h L ∧
        Num.fixVal out.mem (old+i*L) h L P =
          Num.fixVal st.mem (weightSrc+i*weightStride) h L P) ∧
      Num.Valid out.mem denom h L ∧
      Num.intVal out.mem denom h L = (scale : ℤ)*(2 : ℤ)^P ∧
      out.regs 34 = dist ∧ ZeroFrom out.mem dist ∧
      (∀ a < dst, out.mem a = st.mem a) ∧
      (∀ r, r ≠ 29 → r ≠ 30 → r ≠ 33 → r ≠ 34 → out.regs r = st.regs r) ∧
      cost ≤ (17*L+75)*G.m+(35*L+60)*G.m+56*L+119 := by
  intro lengths old denom dist
  obtain ⟨mid,ci,hi,ht',hh',hl',hf,hz',hr,hci⟩ :=
    stagedNumericInputs_runs (ω := ω) st G staging dst src names L len hc hp hStage hDst
      hLength hSrc hNames hL hm hw hlimbs hsep hsrc hnames hroom ht hh hat hcap hl hz
  have hblock (i : ℕ) (hi : i < G.m) : weightSrc+i*weightStride+L ≤ dst := by
    have h := Nat.mul_le_mul_right weightStride (show i ≤ G.m-1 by omega)
    omega
  have hmFit : G.m < 2^w := by omega
  have hOldFit : old < 2^w := hroom
  have hSrcFit : weightSrc < 2^w := by omega
  have hWords : ∀ a ∈ [weightSrc,weightStride,L,G.m,0,old], a < 2^w := by wram_words
  have hsep' (i : ℕ) (hi : i < G.m) : weightSrc+i*weightStride+L ≤ old :=
    (hblock i hi).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  have hPre : (packHostWeightsContract w h P).pre
      [weightSrc,weightStride,L,G.m,0,old] mid.mem := by
    refine ⟨weightSrc,weightStride,L,G.m,old,rfl,hw,hmFit,hLS,hsep',hz',?_,?_⟩
    · exact (Nat.le_add_right _ _).trans_lt hroomAll
    · intro i hi k hk
      exact (hf _ (by have hb := hblock i hi; omega)).trans_lt (hvalid i hi k hk)
  obtain ⟨out,cw,hwRun,hcursor,hzero,hDen,hDenVal,hframe,hweights,hregs,hcw⟩ :=
    stagedWeightsDenominator_runs (ω := ω) mid G.m L weightSrc weightStride old scale
      hpack hprep ((hr _ (by decide) (by decide)).trans hm)
      ((hr _ (by decide) (by decide)).trans hL)
      ((hr _ (by decide) (by decide)).trans hWeight)
      ((hr _ (by decide) (by decide)).trans hStride)
      ((hr _ (by decide) (by decide)).trans hOld)
      ((hr _ (by decide) (by decide)).trans hP)
      ((hr _ (by decide) (by decide)).trans hScale)
      hWords hPre hscaleFit hPFit hfit hscaled hroomAll
  refine ⟨out,ci+cw+1,runs_seq_iff.mpr (Or.inr ⟨mid,ci,cw,hi,hwRun,rfl⟩),
    ?_,?_,?_,?_,hDen,hDenVal,hcursor,hzero,?_,?_,by omega⟩
  · intro i hi
    have hi' : i < G.m := by simpa using hi
    exact (hframe _ (by dsimp [old,lengths]; omega)).trans (ht' i hi)
  · intro i hi
    have hi' : i < G.m := by simpa using hi
    exact (hframe _ (by dsimp [old,lengths]; omega)).trans (hh' i hi)
  · intro i hi
    have hend : lengths+i*L+L ≤ old := by
      have h := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at h
      dsimp [old]
      omega
    obtain ⟨hv,he⟩ := hl' i hi
    have hcell (k : ℕ) (hk : k < L) := hframe (lengths+i*L+k) (by omega)
    exact ⟨fun k hk => (hcell k hk).trans_lt (hv k hk),
      (Num.intVal_congr hcell).trans he⟩
  · intro i hi
    obtain ⟨hv,he⟩ := hweights i hi
    refine ⟨hv,he.trans ?_⟩
    unfold Num.fixVal
    rw [Num.intVal_congr (fun k hk => hf _ (by have hb := hblock i hi; omega))]
  · intro a ha
    exact (hframe a (by dsimp [old,lengths]; omega)).trans (hf a ha)
  · intro r h29 h30 h33 h34
    exact (hregs r h33 h34).trans (hr r h29 h30)

end MinCostFlow.LastLevelProgram
