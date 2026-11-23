module

public import MinCostFlow.LastLevelProgram.StagedNumericLayout
public import MinCostFlow.LastLevelProgram.BranchGraph
public import MinCostFlow.LastLevelProgram.BranchPublish
public import MinCostFlow.LastLevelProgram.BranchStretch
import Mathlib.Tactic

/-!
# Runtime addresses for the staged round outputs

The numeric pass of Definition 5.8 (pages 19–20) leaves one strided
array of rounded stretches and one of updated weights.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord DynSpanner.Program SparseCore LSF MinRatio Num

/-- The narrowed weight update reserves a quadratic number of words
in the host limb count. -/
def narrowWeightSpaceExpr (limbs : Expr) : Expr :=
  let add := Expr.bin .add
  let mul := Expr.bin .mul
  let wide := add (mul (.const 2) limbs) (.const 1)
  add (add (add (mul (.const 21) wide) (.const 3))
    (mul (mul (.const 5) wide) (add wide (.const 1)))) limbs

/-- The runtime expression uses the allocation formula of the signed
division and widened weight update. -/
theorem narrowWeightSpace_formula (L : ℕ) :
    narrowWeightSpace L = 21*(2*L+1)+3+5*(2*L+1)*(2*L+1+1)+L := by
  unfold narrowWeightSpace widenWeightSpace weightUpdateSpace Num.integerDivideSpace
    Num.unsignedDivideSpace
  dsimp only
  ring

/-- The weight stride expression fits if its final value fits. -/
theorem narrowWeightSpaceExpr_eval {w : ℕ} {st : State} {le : Expr}
    (L : ℕ) (hL : le.eval w st = some L) (hfit : narrowWeightSpace L < 2^w) :
    (narrowWeightSpaceExpr le).eval w st = some (narrowWeightSpace L) := by
  rw [narrowWeightSpace_formula] at hfit ⊢
  let k := 2*L+1
  change 21*k+3+5*k*(k+1)+L < 2^w at hfit
  have hkPos : 0 < k := by unfold k; omega
  have hsum : 21*k+3+5*k*(k+1) < 2^w := (Nat.le_add_right _ _).trans_lt hfit
  have hlinear : 21*k+3 < 2^w := (Nat.le_add_right _ _).trans_lt hsum
  have hprod : 5*k*(k+1) < 2^w := (Nat.le_add_left _ _).trans_lt hsum
  have h21 : 21*k < 2^w := by omega
  have hk : k < 2^w := by omega
  have h2L : 2*L < 2^w := by unfold k at hk; omega
  have hk1 : k+1 < 2^w := by omega
  have h5k : 5*k < 2^w := by omega
  have h21c : 21 < 2^w := (Nat.le_mul_of_pos_right _ hkPos).trans_lt h21
  have h5 : 5 < 2^w := by omega
  have h3 : 3 < 2^w := by omega
  have h2 : 2 < 2^w := by omega
  have h1 : 1 < 2^w := by omega
  simp only [narrowWeightSpaceExpr,Expr.eval,BinOp.eval,hL,h21c,h5,h3,h2,h1,h2L,
    show 2*L+1 = k from rfl,hk,hk1,h5k,h21,hlinear,hprod,hsum,hfit,ite_eq_left]

/-- Derive the first stretch and next-weight block addresses, together
with their strides, from the runtime edge count and host format. -/
def stagedOutputArgs (n m limbs heap : Expr) : List Expr :=
  let add := Expr.bin .add
  let mul := Expr.bin .mul
  let sub := Expr.bin .sub
  let start := add heap (mul (sub n (.const 1)) limbs)
  let stretchStride := edgeStretchSpaceExpr limbs
  let weightStride := narrowWeightSpaceExpr limbs
  let afterStretch := add start (mul m stretchStride)
  [sub (add start stretchStride) limbs, stretchStride,
    sub (add afterStretch weightStride) limbs, weightStride]

/-- A fitting full round allocation bounds the intermediate word
operations for both output addresses. -/
theorem stagedOutputArgs_eval {w : ℕ} {st : State} {ne me le he : Expr}
    (n m L heap : ℕ) (hn : ne.eval w st = some n) (hm : me.eval w st = some m)
    (hL : le.eval w st = some L) (hh : he.eval w st = some heap)
    (hnWord : n < 2^w) (hmPos : 0 < m) (hLPos : 0 < L) (hw : 1 < 2^w) :
    let start := heap+(n-1)*L
    let stretchStride := edgeStretchSpace L
    let weightStride := narrowWeightSpace L
    let afterStretch := start+m*stretchStride
    afterStretch+m*weightStride < 2^w →
    evalArgs w st (stagedOutputArgs ne me le he) =
      some [start+stretchStride-L,stretchStride,afterStretch+weightStride-L,weightStride] := by
  intro start stretchStride weightStride afterStretch hroom
  have hafter : afterStretch < 2^w := (Nat.le_add_right _ _).trans_lt hroom
  have hstart : start < 2^w := (Nat.le_add_right _ _).trans_lt hafter
  have hsMul : m*stretchStride < 2^w := (Nat.le_add_left _ _).trans_lt hafter
  have hwMul : m*weightStride < 2^w := (Nat.le_add_left _ _).trans_lt hroom
  have hsLe : stretchStride ≤ m*stretchStride := Nat.le_mul_of_pos_left _ hmPos
  have hwLe : weightStride ≤ m*weightStride := Nat.le_mul_of_pos_left _ hmPos
  have hsFit : start+stretchStride < 2^w := (Nat.add_le_add_left hsLe _).trans_lt hafter
  have hwFit : afterStretch+weightStride < 2^w := (Nat.add_le_add_left hwLe _).trans_lt hroom
  have hs' : start+stretchStride-L < 2^w := (Nat.sub_le _ _).trans_lt hsFit
  have hw' : afterStretch+weightStride-L < 2^w := (Nat.sub_le _ _).trans_lt hwFit
  have hsub : n-1 < 2^w := (Nat.sub_le _ _).trans_lt hnWord
  have hdist : (n-1)*L < 2^w := (Nat.le_add_left _ _).trans_lt hstart
  have hsEval : (edgeStretchSpaceExpr le).eval w st = some stretchStride :=
    edgeStretchSpaceExpr_eval L hL hLPos (hsLe.trans_lt hsMul)
  have hwEval : (narrowWeightSpaceExpr le).eval w st = some weightStride :=
    narrowWeightSpaceExpr_eval L hL (hwLe.trans_lt hwMul)
  simp only [stagedOutputArgs,evalArgs,Expr.eval,BinOp.eval,hn,hm,hL,hh,hw,hsub,hdist,
    hsEval,hwEval,show heap+(n-1)*L = start from rfl,hstart,hsFit,hwFit,hs',hw',hsMul,show start+m*stretchStride = afterStretch from rfl,hafter,ite_eq_left]

/-- Save the two output pointers and strides using the selected width register. -/
def installStagedOutputLayoutFrom (width : ℕ) : Stmt :=
  stagedAddressAssignments [36,37,38,39]
    (stagedOutputArgs (.reg 0) (.reg 1) (.reg width) (.reg 20))

/-- Save the addresses after a caller-width numeric pass. -/
def installStagedOutputLayout : Stmt := installStagedOutputLayoutFrom 19

/-- Save the addresses after a widened numeric pass. -/
def installWideStagedOutputLayout : Stmt := installStagedOutputLayoutFrom 24

/-- Compute the output addresses without touching the round's memory
or allocation cursor. -/
private theorem installStagedOutputLayoutFrom_runs {w width : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (n m L heap : ℕ)
    (hwidth : width ∉ ([36,37,38,39] : List ℕ))
    (hn : st.regs 0 = n) (hm : st.regs 1 = m) (hL : st.regs width = L)
    (hh : st.regs 20 = heap)
    (hnWord : n < 2^w) (hmPos : 0 < m) (hLPos : 0 < L) (hw : 1 < 2^w) :
    let start := heap+(n-1)*L
    let stretchStride := edgeStretchSpace L
    let weightStride := narrowWeightSpace L
    let afterStretch := start+m*stretchStride
    afterStretch+m*weightStride < 2^w →
    ∃ out cost, Runs w p ω (installStagedOutputLayoutFrom width) st .normal out cost ∧
      out.mem = st.mem ∧ out.regs 36 = start+stretchStride-L ∧
      out.regs 37 = stretchStride ∧ out.regs 38 = afterStretch+weightStride-L ∧
      out.regs 39 = weightStride ∧
      (∀ r, r ∉ ([36,37,38,39] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg width) (.reg 20))+9 := by
  intro start stretchStride weightStride afterStretch hroom
  let es := stagedOutputArgs (.reg 0) (.reg 1) (.reg width) (.reg 20)
  let rs := [36,37,38,39]
  have he (mid : State) (hf : ∀ r, r ∉ rs → mid.regs r = st.regs r) :
      evalArgs w mid es =
        some [start+stretchStride-L,stretchStride,afterStretch+weightStride-L,weightStride] :=
    stagedOutputArgs_eval (ne := .reg 0) (me := .reg 1) (le := .reg width) (he := .reg 20)
      n m L heap
      (congrArg some ((hf _ (by decide)).trans hn))
      (congrArg some ((hf _ (by decide)).trans hm))
      (congrArg some ((hf _ hwidth).trans hL))
      (congrArg some ((hf _ (by decide)).trans hh)) hnWord hmPos hLPos hw hroom
  obtain ⟨out,cost,hr,hmem,hregs,hcost⟩ :=
    addressAssignments_runs (p := p) (ω := ω) st rs es
      [start+stretchStride-L,stretchStride,afterStretch+weightStride-L,weightStride]
      (rfl) he
  refine ⟨out,cost,hr,hmem,?_,?_,?_,?_,?_,hcost⟩
  all_goals rw [hregs]
  all_goals simp [rs,Function.update]
  intro r h36 h37 h38 h39
  simp [h36,h37,h38,h39]

/-- Compute the output addresses without touching the round's memory
or allocation cursor. -/
theorem installStagedOutputLayout_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (n m L heap : ℕ)
    (hn : st.regs 0 = n) (hm : st.regs 1 = m) (hL : st.regs 19 = L)
    (hh : st.regs 20 = heap)
    (hnWord : n < 2^w) (hmPos : 0 < m) (hLPos : 0 < L) (hw : 1 < 2^w) :
    let start := heap+(n-1)*L
    let stretchStride := edgeStretchSpace L
    let weightStride := narrowWeightSpace L
    let afterStretch := start+m*stretchStride
    afterStretch+m*weightStride < 2^w →
    ∃ out cost, Runs w p ω installStagedOutputLayout st .normal out cost ∧
      out.mem = st.mem ∧ out.regs 36 = start+stretchStride-L ∧
      out.regs 37 = stretchStride ∧ out.regs 38 = afterStretch+weightStride-L ∧
      out.regs 39 = weightStride ∧
      (∀ r, r ∉ ([36,37,38,39] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 19) (.reg 20))+9 :=
  installStagedOutputLayoutFrom_runs st n m L heap (by decide) hn hm hL hh
    hnWord hmPos hLPos hw

/-- Locate the widened output blocks using the scratch width in register 24. -/
theorem installWideStagedOutputLayout_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (n m L heap : ℕ)
    (hn : st.regs 0 = n) (hm : st.regs 1 = m) (hL : st.regs 24 = L)
    (hh : st.regs 20 = heap)
    (hnWord : n < 2^w) (hmPos : 0 < m) (hLPos : 0 < L) (hw : 1 < 2^w) :
    let start := heap+(n-1)*L
    let stretchStride := edgeStretchSpace L
    let weightStride := narrowWeightSpace L
    let afterStretch := start+m*stretchStride
    afterStretch+m*weightStride < 2^w →
    ∃ out cost, Runs w p ω installWideStagedOutputLayout st .normal out cost ∧
      out.mem = st.mem ∧ out.regs 36 = start+stretchStride-L ∧
      out.regs 37 = stretchStride ∧ out.regs 38 = afterStretch+weightStride-L ∧
      out.regs 39 = weightStride ∧
      (∀ r, r ∉ ([36,37,38,39] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 24) (.reg 20))+9 :=
  installStagedOutputLayoutFrom_runs st n m L heap (by decide) hn hm hL hh
    hnWord hmPos hLPos hw

/-- The retained compact tree and the preserved staging tables supply
the named-edge scan used to publish the branch graph. -/
theorem stagedBranchRecords_ready (G T : MGraph) (ℓ : ℕ → ℝ)
    (L staging dest count names vertices records : ℕ) (mem out : ℕ → ℕ) :
    let H := representativeGraph G ℓ
    let I := indexedGraph H
    retainedStagedTreeAt H T (staging+queryWeights H L) dest count mem out →
    names+H.m ≤ staging+queryWeights H L → vertices+H.n ≤ staging+queryWeights H L →
    (∀ i < H.m, mem (names+i) = edgeName H i ∧
      mem (staging+i) = I.tail i ∧ mem (staging+(H.m+i)) = I.head i) →
    (∀ v < H.n, mem (vertices+v) = vertexName H v) →
    ∃ kept : List ℕ, count = kept.length ∧ kept.length ≤ H.n ∧ kept.Nodup ∧
      decodedTree H.n H.m I.tail I.head kept [] = T ∧
      [records,names,staging,staging+H.m,vertices,dest,count] =
        [records,names,staging,staging+H.m,vertices,dest,kept.length] ∧
      ListAt out dest kept ∧
      (∀ i < H.m, out (names+i) = edgeName H i ∧
        out (staging+i) = I.tail i ∧ out (staging+H.m+i) = I.head i) ∧
      ∀ v < H.n, out (vertices+v) = vertexName H v := by
  intro H I hTree hNameFit hVertexFit hEdges hVertices
  obtain ⟨kept,he,hSize,hNodup,hList,hDecode,hFrame⟩ := hTree
  have hprefix : 2*H.m ≤ queryWeights H L := by unfold queryWeights queryLengths; omega
  refine ⟨kept,he,hSize,hNodup,hDecode,by rw [he],hList,?_,?_⟩
  · intro i hi
    obtain ⟨hn,ht,hh⟩ := hEdges i hi
    refine ⟨(hFrame _ (by omega)).trans hn,(hFrame _ (by omega)).trans ht,?_⟩
    exact (hFrame _ (by omega)).trans (by simpa [Nat.add_assoc] using hh)
  · intro v hv
    exact (hFrame _ (by omega)).trans (hVertices v hv)

/-- Restore names from the staged endpoint tables into the fresh region
returned by the numeric pass. Register forty holds the vertex names. -/
def stagedBranchRecordArgs : List Expr :=
  [.reg 16,.reg 28,.reg 5,.bin .add (.reg 5) (.reg 1),.reg 40,
    .bin .add (.bin .add (.reg 12) (.const 1)) (.reg 1),.reg 13]

/-- The branch record scan receives the selected array and count that
survived the numeric pass. -/
theorem stagedBranchRecordArgs_eval {w : ℕ} (st : State)
    (records names staging m vertices cursor count : ℕ)
    (hRecords : st.regs 16 = records) (hNames : st.regs 28 = names)
    (hStaging : st.regs 5 = staging) (hm : st.regs 1 = m)
    (hVertices : st.regs 40 = vertices) (hCursor : st.regs 12 = cursor)
    (hCount : st.regs 13 = count)
    (hStageFit : staging+m < 2^w) (hDestFit : cursor+1+m < 2^w) :
    evalArgs w st stagedBranchRecordArgs =
      some [records,names,staging,staging+m,vertices,cursor+1+m,count] := by
  have hOne : 1 < 2^w := by omega
  have hMarks : cursor+1 < 2^w := by omega
  simp only [stagedBranchRecordArgs,evalArgs,Expr.eval,BinOp.eval,hRecords,hNames,
    hStaging,hm,hVertices,hCursor,hCount,hStageFit,hDestFit,hOne,hMarks,ite_eq_left]

/-- Restore the retained compact edges to their original names and
endpoints in fresh memory at the numeric allocation cursor. -/
theorem stagedBranchRecords_runs {w entry write result : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G T : MGraph) (ℓ : ℕ → ℝ)
    (L staging cursor count names vertices records : ℕ) (mem : ℕ → ℕ)
    (hp : p.procs[entry]? = some (branchEdgeRecordsBody write))
    (hwrite : MeetsContract w p write (writeBranchEdgeRecordContract w))
    (hw : 3 < 2^w) (hG : G.IsValid)
    (hV : ∀ v ∈ G.V, v < 2^w) (hE : ∀ e ∈ G.E, e < 2^w)
    (hRecords : st.regs 16 = records) (hNames : st.regs 28 = names)
    (hStaging : st.regs 5 = staging) (hVertices : st.regs 40 = vertices)
    (hCursor : st.regs 12 = cursor) (hCount : st.regs 13 = count) :
    let H := representativeGraph G ℓ
    let I := indexedGraph H
    let dest := cursor+1+H.m
    st.regs 1 = H.m →
    retainedStagedTreeAt H T (staging+queryWeights H L) dest count mem st.mem →
    (∀ i ∈ T.E, i < H.m) →
    names+H.m ≤ staging+queryWeights H L → vertices+H.n ≤ staging+queryWeights H L →
    (∀ i < H.m, mem (names+i) = edgeName H i ∧
      mem (staging+i) = I.tail i ∧ mem (staging+(H.m+i)) = I.head i) →
    (∀ v < H.n, mem (vertices+v) = vertexName H v) →
    staging+queryWeights H L ≤ dest → dest+H.n ≤ records →
    records+3*H.n < 2^w →
    ∃ out cost kept, Runs w p ω (.call result entry stagedBranchRecordArgs) st .normal out cost ∧
      count = kept.length ∧ kept.Nodup ∧ decodedTree H.n H.m I.tail I.head kept [] = T ∧
      (let triples := kept.map fun i => (edgeName H i, G.tail (edgeName H i), G.head (edgeName H i))
       ∀ j (hj : j < triples.length),
          out.mem (records+3*j) = triples[j].1 ∧
          out.mem (records+3*j+1) = triples[j].2.1 ∧
          out.mem (records+3*j+2) = triples[j].2.2) ∧
      (∀ a, a < records ∨ records+3*count ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ result → out.regs r = st.regs r) ∧ cost ≤ 73*count+24 := by
  intro H I dest hm hTree hIndex hNamesFit hVerticesFit hEdges hVerts hSep hDest hRoom
  obtain ⟨kept,hcount,hsize,hnd,hdecode,hargsEq,hlist,hpacked,hvertices⟩ :=
    stagedBranchRecords_ready G T ℓ L staging dest count names vertices records
      mem st.mem hTree hNamesFit hVerticesFit hEdges hVerts
  have hprefix : 2*H.m ≤ queryWeights H L := by unfold queryWeights queryLengths; omega
  have hdFit : dest < 2^w := by omega
  have hstageFit : staging+H.m < 2^w := by omega
  have hArgs := stagedBranchRecordArgs_eval st records names staging H.m vertices cursor count
    hRecords hNames hStaging hm hVertices hCursor hCount hstageFit hdFit
  change evalArgs w st stagedBranchRecordArgs =
    some [records,names,staging,staging+H.m,vertices,dest,count] at hArgs
  have hkept : ∀ i ∈ kept, i < H.m := by
    intro i hi
    apply hIndex i
    rw [← hdecode]
    exact Finset.mem_union_left _ (List.mem_toFinset.mpr hi)
  dsimp only [H] at hprefix hcount hsize hNamesFit hVerticesFit hSep hDest hRoom hdFit hstageFit
  have hcall := branchEdgeRecords_meetsContract (G := G) ℓ kept records names staging
    (staging+H.m) vertices dest hp hwrite hw hG hkept hV hE
    (by omega) (by omega) (by dsimp only [H] at *; omega)
    (by dsimp only [H] at *; omega) (by omega) (by omega) (by omega)
  have hwords : ∀ x ∈ [records,names,staging,staging+H.m,vertices,dest,count], x < 2^w := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [H] at * <;> omega
  obtain ⟨out,cost,ret,hr,hpost,_,hregs,hcost⟩ := runs_call_of_meetsContract (r := result)
    hcall hArgs hwords ⟨hargsEq,hlist,hpacked,hvertices⟩ ω
  obtain ⟨_,htriples,hframe⟩ := hpost
  refine ⟨out,cost,kept,hr,hcount,hnd,hdecode,htriples,?_,hregs,?_⟩
  · simpa only [hcount] using hframe
  · change cost ≤ 13+(73*kept.length+10)+1 at hcost
    omega

/-- Install the branch graph after the four-word header reserved there.
Registers forty-one through forty-four hold the caller's capacities,
vertex count, and original vertex array. -/
def stagedBranchGraphArgs : List Expr :=
  [.bin .add (.bin .add (.reg 16) (.bin .mul (.const 3) (.reg 13))) (.const 4),
    .reg 41,.reg 42,.reg 43,.reg 44,.reg 13,.reg 16]

/-- The branch initializer uses the restored record array directly. -/
theorem stagedBranchGraphArgs_eval {w : ℕ} (st : State)
    (records count vCap eCap n vertices : ℕ)
    (hRecords : st.regs 16 = records) (hCount : st.regs 13 = count)
    (hv : st.regs 41 = vCap) (he : st.regs 42 = eCap)
    (hn : st.regs 43 = n) (hvertices : st.regs 44 = vertices)
    (hw : 4 < 2^w) (hroom : records+3*count+4 < 2^w) :
    evalArgs w st stagedBranchGraphArgs =
      some [records+3*count+4,vCap,eCap,n,vertices,count,records] := by
  have hprefix : records+3*count < 2^w := (Nat.le_add_right _ _).trans_lt hroom
  have hcount : 3*count < 2^w := (Nat.le_add_left _ _).trans_lt hprefix
  have hThree : 3 < 2^w := by omega
  simp only [stagedBranchGraphArgs,evalArgs,Expr.eval,BinOp.eval,
    hRecords,hCount,hv,he,hn,hvertices,hw,hThree,hprefix,hroom,hcount,ite_eq_left]

/-- The retained indices enumerate exactly the tree edges. With the
restored triples this discharges the branch graph initializer's precondition. -/
theorem stagedBranchGraph_pre {w : ℕ} (G T : MGraph) (ℓ : ℕ → ℝ)
    (kept vertices : List ℕ) (mem out : ℕ → ℕ) (records vCap eCap vp : ℕ)
    (hG : G.IsValid) (hn : kept.Nodup)
    (hV : ∀ v, v ∈ vertices ↔ v ∈ G.V)
    (hvc : ∀ v ∈ G.V, v < vCap) (hec : ∀ e ∈ G.E, e < eCap)
    (hw : 16 ≤ 2^w) (hvp : vp+vertices.length ≤ records)
    (hvertices : ListAt mem vp vertices)
    (hframe : ∀ a, a < records ∨ records+3*kept.length ≤ a → out a = mem a) :
    let H := representativeGraph G ℓ
    let I := indexedGraph H
    let g := records+3*kept.length+4
    let F : MGraph :=
      { V := G.V, E := (restoreTreeNames H T).E ∩ H.E, tail := G.tail, head := G.head }
    let triples := kept.map fun i => (edgeName H i, G.tail (edgeName H i), G.head (edgeName H i))
    decodedTree H.n H.m I.tail I.head kept [] = T →
    (∀ i ∈ T.E, i < H.m) → ZeroFrom mem records →
    g+dynGraphSize vCap eCap < 2^w →
    (∀ i (hi : i < triples.length),
      out (records+3*i) = triples[i].1 ∧ out (records+3*i+1) = triples[i].2.1 ∧
        out (records+3*i+2) = triples[i].2.2) →
    (dgInitFromListsContract w vCap eCap F vertices triples).pre
      [g,vCap,eCap,vertices.length,vp,kept.length,records] out := by
  intro H I g F triples hdecode hindex hzero hroom htriples
  have hset : kept.toFinset = T.E := by rw [← hdecode]; simp [decodedTree]
  exact selectedBranch_graphInit_pre_of_scan ℓ kept vertices mem out g vCap eCap vp records
    hG hn hset hindex hV hvc hec hw hroom (fun a ha => hzero a (((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans ha))
    hvp (Nat.le_add_right _ _) hvertices hframe htriples

/-- Restore the branch records and initialize their graph in fresh memory. -/
def stagedBranchGraphBody (restore init : ℕ) : Stmt :=
  .seq (.call 45 restore stagedBranchRecordArgs) (.call 46 init stagedBranchGraphArgs)

/-- The two publication calls produce the branch graph with a fresh
suffix and preserve the weight and stretch blocks below the allocation. -/
theorem stagedBranchGraph_runs {w entry write init : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G T : MGraph) (ℓ : ℕ → ℝ)
    (L staging cursor count names vertices records : ℕ) (mem : ℕ → ℕ)
    (hp : p.procs[entry]? = some (branchEdgeRecordsBody write))
    (hwrite : MeetsContract w p write (writeBranchEdgeRecordContract w))
    (hw : 3 < 2^w) (hG : G.IsValid)
    (hV : ∀ v ∈ G.V, v < 2^w) (hE : ∀ e ∈ G.E, e < 2^w)
    (hRecords : st.regs 16 = records) (hNames : st.regs 28 = names)
    (hStaging : st.regs 5 = staging) (hVertices : st.regs 40 = vertices)
    (hCursor : st.regs 12 = cursor) (hCount : st.regs 13 = count) :
    let H := representativeGraph G ℓ
    let I := indexedGraph H
    let dest := cursor+1+H.m
    st.regs 1 = H.m →
    retainedStagedTreeAt H T (staging+queryWeights H L) dest count mem st.mem →
    (∀ i ∈ T.E, i < H.m) →
    names+H.m ≤ staging+queryWeights H L → vertices+H.n ≤ staging+queryWeights H L →
    (∀ i < H.m, mem (names+i) = edgeName H i ∧
      mem (staging+i) = I.tail i ∧ mem (staging+(H.m+i)) = I.head i) →
    (∀ v < H.n, mem (vertices+v) = vertexName H v) →
    staging+queryWeights H L ≤ dest → dest+H.n ≤ records →
    ∀ (verts : List ℕ) (vCap eCap vp : ℕ),
    st.regs 41 = vCap → st.regs 42 = eCap → st.regs 43 = verts.length → st.regs 44 = vp →
    (∀ v, v ∈ verts ↔ v ∈ G.V) →
    (∀ v ∈ G.V, v < vCap) → (∀ e ∈ G.E, e < eCap) →
    ListAt st.mem vp verts → vp+verts.length ≤ records → 16 ≤ 2^w →
    (∀ x ∈ [vCap,eCap,verts.length,vp], x < 2^w) → ZeroFrom st.mem records →
    records+3*H.n < 2^w → records+3*count+4+dynGraphSize vCap eCap < 2^w →
    let g := records+3*count+4
    let F : MGraph :=
      { V := G.V, E := (restoreTreeNames H T).E ∩ H.E, tail := G.tail, head := G.head }
    (∀ kept : List ℕ, MeetsContract w p init
      (dgInitFromListsContract w vCap eCap F verts
        (kept.map fun i => (edgeName H i, G.tail (edgeName H i), G.head (edgeName H i))))) →

    ∃ out cost, Runs w p ω (stagedBranchGraphBody entry init) st .normal out cost ∧
      DynGraphAt out.mem g vCap eCap F ∧ ZeroFrom out.mem (g+dynGraphSize vCap eCap) ∧
      (∀ a < records, out.mem a = st.mem a) ∧
      (∀ r, r ≠ 45 → r ≠ 46 → out.regs r = st.regs r) ∧
      cost ≤ 130*verts.length+563*count+139 := by
  intro H I dest hm hTree hIndex hNamesFit hVerticesFit hEdges hVerts hSep hDest
    verts vCap eCap vp hvCap heCap hn hVp hSet hvc hec hvAt hvp hw16 hwords hz hroom hfull g F hinit
  obtain ⟨mid,cr,kept,hr,hCountEq,hnd,hdecode,htriples,hframe,hregs,hcr⟩ :=
    stagedBranchRecords_runs (ω := ω) (result := 45) st G T ℓ L staging cursor count names
      vertices records mem hp hwrite hw hG hV hE hRecords hNames hStaging hVertices
      hCursor hCount hm hTree hIndex hNamesFit hVerticesFit hEdges hVerts hSep hDest hroom
  have hg : g < 2^w := (Nat.le_add_right _ _).trans_lt hfull
  have hargs := stagedBranchGraphArgs_eval mid records count vCap eCap verts.length vp
    ((hregs _ (by decide)).trans hRecords) ((hregs _ (by decide)).trans hCount)
    ((hregs _ (by decide)).trans hvCap) ((hregs _ (by decide)).trans heCap)
    ((hregs _ (by decide)).trans hn) ((hregs _ (by decide)).trans hVp) (by omega) hg
  have hgEq : records+3*kept.length+4 = g := by rw [← hCountEq]
  have hpre := stagedBranchGraph_pre G T ℓ kept verts st.mem mid.mem records vCap eCap vp
    hG hnd hSet hvc hec hw16 hvp hvAt (by simpa only [← hCountEq] using hframe)
    hdecode hIndex hz (by rwa [hgEq]) htriples
  rw [hgEq,← hCountEq] at hpre
  have hwords' : ∀ x ∈ [g,vCap,eCap,verts.length,vp,count,records], x < 2^w := by
    intro x hx
    have hrec : records < 2^w := by omega
    have hcount : count < 2^w := by dsimp [g] at hg; omega
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg
    · exact hwords _ (by simp)
    · exact hwords _ (by simp)
    · exact hwords _ (by simp)
    · exact hwords _ (by simp)
    · exact hcount
    · exact hrec
  obtain ⟨out,ci,ret,hrun,hpost,_,hregs',hci⟩ :=
    runs_call_of_meetsContract (r := 46) (hinit kept) hargs hwords' hpre ω
  obtain ⟨g',nv,pv,ne,pe,heq,_,hgraph,hkeep,hzero⟩ := hpost
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := heq
  refine ⟨out,cr+ci+1,runs_seq_iff.mpr (Or.inr ⟨mid,cr,ci,hr,hrun,rfl⟩),
    hgraph,hzero,?_,?_,?_⟩
  · intro a ha
    exact (hkeep a (Or.inl (ha.trans_le ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))))).trans (hframe a (Or.inl ha))
  · intro r hr₁ hr₂
    exact (hregs' r hr₂).trans (hregs r hr₁)
  · change ci ≤ 13+(130*verts.length+490*count+100)+1 at hci
    omega

/-- After the shared graph, reserve the root bits, the stretch header,
a source address table, and the two named fixed-point arrays. The
capacity and output limb count come from registers. -/
def stagedBranchPayloadArgs (outputLimbs : Expr) : List Expr :=
  let add := Expr.bin .add
  let mul := Expr.bin .mul
  let base := add (.reg 16) (mul (.const 3) (.reg 13))
  let graph := add base (.const 4)
  let graphSize := add (add (.const 4) (mul (.const 7) (.reg 41)))
    (mul (.const 9) (.reg 42))
  let roots := add graph graphSize
  let stretch := add roots (.reg 41)
  let addresses := add stretch (.const 2)
  let numerator := add addresses (.reg 42)
  let block := mul (.reg 42) outputLimbs
  let denominator := add numerator block
  [base,graph,roots,stretch,addresses,numerator,denominator,add denominator block]

/-- The end of the branch allocation bounds every address calculation
used to place its payloads. -/
theorem stagedBranchPayloadArgs_eval {w : ℕ} (st : State) (outputLimbs : Expr)
    (records count vCap eCap L : ℕ)
    (hRecords : st.regs 16 = records) (hCount : st.regs 13 = count)
    (hv : st.regs 41 = vCap) (he : st.regs 42 = eCap)
    (hL : outputLimbs.eval w st = some L) (hw : 9 < 2^w) :
    let base := records+3*count
    let graph := base+4
    let roots := graph+dynGraphSize vCap eCap
    let stretch := roots+vCap
    let addresses := stretch+2
    let numerator := addresses+eCap
    let denominator := numerator+eCap*L
    let stop := denominator+eCap*L
    stop < 2^w →
      evalArgs w st (stagedBranchPayloadArgs outputLimbs) =
        some [base,graph,roots,stretch,addresses,numerator,denominator,stop] := by
  intro base graph roots stretch addresses numerator denominator stop hroom
  have hden : denominator < 2^w := (Nat.le_add_right _ _).trans_lt hroom
  have hnum : numerator < 2^w := (Nat.le_add_right _ _).trans_lt hden
  have had : addresses < 2^w := (Nat.le_add_right _ _).trans_lt hnum
  have hstr : stretch < 2^w := (Nat.le_add_right _ _).trans_lt had
  have hr : roots < 2^w := (Nat.le_add_right _ _).trans_lt hstr
  have hg : graph < 2^w := (Nat.le_add_right _ _).trans_lt hr
  have hb : base < 2^w := (Nat.le_add_right _ _).trans_lt hg
  have hcount : 3*count < 2^w := (Nat.le_add_left _ _).trans_lt hb
  have hblock : eCap*L < 2^w := (Nat.le_add_left _ _).trans_lt hden
  have hsize : dynGraphSize vCap eCap < 2^w := (Nat.le_add_left _ _).trans_lt hr
  change 4+7*vCap+9*eCap < 2^w at hsize
  have hpartial : 4+7*vCap < 2^w := (Nat.le_add_right _ _).trans_lt hsize
  have hvertices : 7*vCap < 2^w := (Nat.le_add_left _ _).trans_lt hpartial
  have hedges : 9*eCap < 2^w := (Nat.le_add_left _ _).trans_lt hsize
  have h2 : 2 < 2^w := by omega
  have h3 : 3 < 2^w := by omega
  have h4 : 4 < 2^w := by omega
  have h7 : 7 < 2^w := by omega
  simp only [stagedBranchPayloadArgs,evalArgs,Expr.eval,BinOp.eval,hRecords,hCount,hv,he,hL,
    h2,h3,h4,h7,hw,hcount,hvertices,hedges,hpartial,hsize,hblock,
    show records+3*count = base from rfl,hb,show base+4 = graph from rfl,hg,
    show graph+(4+7*vCap+9*eCap) = roots from rfl,hr,
    show roots+vCap = stretch from rfl,hstr,show stretch+2 = addresses from rfl,had,
    show addresses+eCap = numerator from rfl,hnum,
    show numerator+eCap*L = denominator from rfl,hden,
    show denominator+eCap*L = stop from rfl,hroom,ite_eq_left]

/-- Save the branch addresses while keeping the runtime output format and
the compact round outputs in their existing registers. -/
def installStagedBranchPayloadLayout : Stmt :=
  stagedAddressAssignments [47,48,49,50,51,52,53,54]
    (stagedBranchPayloadArgs (.reg 55))

/-- Computing the branch layout preserves the graph and gives the
publisher pointers in registers forty-seven through fifty-four. -/
theorem installStagedBranchPayloadLayout_runs
    {w : ℕ} {p : Program} {ω : ℕ → Bool} (st : State)
    (records count vCap eCap L : ℕ)
    (hRecords : st.regs 16 = records) (hCount : st.regs 13 = count)
    (hv : st.regs 41 = vCap) (he : st.regs 42 = eCap)
    (hL : st.regs 55 = L) (hw : 9 < 2^w) :
    let base := records+3*count
    let graph := base+4
    let roots := graph+dynGraphSize vCap eCap
    let stretch := roots+vCap
    let addresses := stretch+2
    let numerator := addresses+eCap
    let denominator := numerator+eCap*L
    let stop := denominator+eCap*L
    stop < 2^w →
    ∃ out cost, Runs w p ω installStagedBranchPayloadLayout st .normal out cost ∧
      out.mem = st.mem ∧
      out.regs 47 = base ∧ out.regs 48 = graph ∧ out.regs 49 = roots ∧
      out.regs 50 = stretch ∧ out.regs 51 = addresses ∧ out.regs 52 = numerator ∧
      out.regs 53 = denominator ∧ out.regs 54 = stop ∧
      (∀ r, r < 47 ∨ 54 < r → out.regs r = st.regs r) ∧
      cost ≤ argsSize (stagedBranchPayloadArgs (.reg 55))+17 := by
  intro base graph roots stretch addresses numerator denominator stop hroom
  let rs := [47,48,49,50,51,52,53,54]
  have hargs (mid : State) (hf : ∀ r, r ∉ rs → mid.regs r = st.regs r) :
      evalArgs w mid (stagedBranchPayloadArgs (.reg 55)) =
        some [base,graph,roots,stretch,addresses,numerator,denominator,stop] :=
    stagedBranchPayloadArgs_eval mid (.reg 55) records count vCap eCap L
      ((hf _ (by decide)).trans hRecords) ((hf _ (by decide)).trans hCount)
      ((hf _ (by decide)).trans hv) ((hf _ (by decide)).trans he)
      (congrArg some ((hf _ (by decide)).trans hL)) hw hroom
  obtain ⟨out,cost,hr,hmem,hregs,hcost⟩ :=
    addressAssignments_runs (p := p) (ω := ω) st rs (stagedBranchPayloadArgs (.reg 55))
      [base,graph,roots,stretch,addresses,numerator,denominator,stop] (by decide) hargs
  refine ⟨out,cost,hr,hmem,?_,?_,?_,?_,?_,?_,?_,?_,?_,hcost⟩
  all_goals rw [hregs]
  all_goals simp [rs,Function.update]
  intro r hr
  have hne : ∀ k : ℕ, 47 ≤ k → k ≤ 54 → r ≠ k := by
    intro k hlo hhi heq
    omega
  simp [hne 47 (by decide) (by decide), hne 48 (by decide) (by decide),
    hne 49 (by decide) (by decide), hne 50 (by decide) (by decide),
    hne 51 (by decide) (by decide), hne 52 (by decide) (by decide),
    hne 53 (by decide) (by decide), hne 54 (by decide) (by decide)]

/-- The staged payload ranges supply the publisher's allocation bounds
when the original edge names fit the output capacity. -/
theorem stagedBranchPayload_publish_pre
    {w vCap eCap h L P floor oldEnd : ℕ} {E : Finset ℕ} {branch : LSF}
    {G : MGraph} {mem : ℕ → ℕ} (records count collection j vertices : ℕ)
    (hv : G.V.Nonempty) (hname : mem vertices = vertexName G 0)
    (hvertex : firstVertex G.V < vCap) (hmodel : componentRoots G = branch.F.R)
    (hw : 1 < 2^w) (hfloor : floor ≤ oldEnd) (hbase : oldEnd ≤ records)
    (hedges : ∀ e ∈ E, e < eCap) :
    let base := records+3*count
    let graph := base+4
    let roots := graph+dynGraphSize vCap eCap
    let stretch := roots+vCap
    let numerator := stretch+2+eCap
    let denominator := numerator+eCap*L
    let stop := denominator+eCap*L
    collection+1+j < base → stop < 2^w →
    (∀ v < vCap, mem (roots+v) = 0) →
    DynGraphAt mem graph vCap eCap branch.T →
    DynGraphAt mem graph vCap eCap branch.F.F →
    EdgeValuesAt mem numerator h L P E branch.wstr →
    EdgeValuesAt mem denominator h L P E (fun _ => 1) →
    (publishRootedBranchContract w vCap eCap h L P floor oldEnd stop E branch G).pre
      [base,graph,graph,roots,stretch,collection,j,numerator,denominator,vertices] mem := by
  intro base graph roots stretch numerator denominator stop hslot hfit hz ht hf hn hd
  have hblock (e : ℕ) (he : e ∈ E) : e*L+L ≤ eCap*L := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right L (hedges e he)
  have hrFit : roots+vCap < 2^w := by dsimp [stop,denominator,numerator,stretch] at hfit; omega
  apply publishRootedBranch_pre_of_payloads hv hname hvertex hrFit hz hmodel hw hslot hfit ht hf hn hd
    hfloor (hbase.trans (Nat.le_add_right _ _)) (le_refl _) (le_refl _)
    (le_refl _) (le_refl _) (Nat.le_add_right _ _) (le_refl _)
  · exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  · exact Nat.le_add_right _ _
  · exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  · intro e he
    rw [Nat.add_assoc]
    exact (Nat.add_le_add_left (hblock e he) _).trans (Nat.le_add_right _ _)
  · intro e he
    rw [Nat.add_assoc]
    exact Nat.add_le_add_left (hblock e he) _

end MinCostFlow.LastLevelProgram
