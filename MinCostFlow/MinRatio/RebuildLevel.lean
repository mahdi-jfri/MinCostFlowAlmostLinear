module

public import MinCostFlow.MinRatio.ShiftGraph
public import MinCostFlow.Chain.Algorithm1
public import MinCostFlow.MinRatio.ShiftModelPrefix
import MinCostFlow.MinRatio.TreeEditFold
import MinCostFlow.MinRatio.RebuildGuard

/-!
# Initializing a sparse-core level during Rebuild

Algorithm 1 (page 20) initializes all branches at the current level,
selects branch zero, and passes its sparsifier to the next level.
The initialization and the graph readout both use the shared
sparse-core contract from Lemma 5.17 (page 23).
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- Save the fresh handle, initialize the tool, and select branch zero.
The input graph, lengths, and gradients are in registers 6, 7, and 8. -/
@[expose] def rebuildLevelInit (init : ℕ) : Stmt :=
  .assign 3 (.reg 4) ;;
  .call 4 init [.reg 6, .reg 7, .reg 8, .reg 4] ;;
  .assign 2 (.const 0)

/-- Initialize one level with the exact model inputs and keep the
tool's returned heap for the branch-zero graph readout. -/
theorem rebuildLevelInit_runs {w L k M N vCap eCap init graph lengths gradient heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool G k M N vCap eCap costs allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient)
    (hh : st.regs 4 = heap)
    (hwords : ∀ a ∈ [graph, lengths, gradient, heap], a < 2 ^ w)
    (hpre : (sparseCoreMachineContract fmt L tool G k M N vCap eCap costs allocation).initPre
      [graph, lengths, gradient, heap] st.mem)
    (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 5 [graph, lengths, gradient, heap] < 2 ^ w) :
    let model := tool.init k M N G
      (readEdgeValues st.mem lengths fmt.limbBits L fmt.precision G.E)
      (readEdgeValues st.mem gradient fmt.limbBits L fmt.precision G.E)
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (rebuildLevelInit init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 4 = ret ∧
      R.rep heap model y out.mem ∧ SparseCoreInput tool.toSparseCoreTool tool.restart k model G ∧
      R.Respects (fun _ => False) heap (allocation 5 [graph, lengths, gradient, heap])
        st.mem ret heap y out.mem ∧
      cost + R.phi heap y out.mem ≤ costs.factor M N * (M + 1) * k + 11 := by
  dsimp only
  obtain ⟨body, hbody, o, after, c, hrun, next, y, hrep, hpost, hframe, hcost⟩ :=
    himpl.2.1 [graph, lengths, gradient, heap] st.mem st.pos ω hwords hpre hz hroom
  have hinput := sparseCoreMachineContract_init_input hpre hpost
  have hnext : next = tool.init k M N G
      (readEdgeValues st.mem lengths fmt.limbBits L fmt.precision G.E)
      (readEdgeValues st.mem gradient fmt.limbBits L fmt.precision G.E) := hpost
  subst next
  let first := { st with regs := Function.update st.regs 3 heap }
  let second := { after with regs := Function.update first.regs 4 o.value }
  let out := { second with regs := Function.update second.regs 2 0 }
  have hfirst : Runs w p ω (.assign 3 (.reg 4)) st .normal first 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have hargs : evalArgs w first [.reg 6, .reg 7, .reg 8, .reg 4] =
      some [graph, lengths, gradient, heap] := by
    simp [evalArgs, Expr.eval, first, Function.update_of_ne, hg, hl, hc, hh]
  have hcall : Runs w p ω (.call 4 init [.reg 6, .reg 7, .reg 8, .reg 4])
      first .normal second (4 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  have hzero : 0 < 2 ^ w := Nat.two_pow_pos _
  have hlast : Runs w p ω (.assign 2 (.const 0)) second .normal out 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hzero], rfl, rfl, rfl⟩
  refine ⟨out, o.value, 2 + ((4 + c + 1) + 2 + 1) + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨first, 2, _, hfirst,
      runs_seq_iff.mpr (Or.inr ⟨second, _, 2, hcall, hlast, rfl⟩), rfl⟩),
    by simp [out], by simp [out, second, first, Function.update_of_ne],
    by simp [out, second, Function.update_of_ne], hrep, hinput, hframe, ?_⟩
  change c + R.phi heap y after.mem ≤ costs.factor M N * (M + 1) * k at hcost
  change _ + R.phi heap y after.mem ≤ _
  omega

/-- Initialization changes only the branch, handle, and heap registers.
The caller keeps its suffix index and descriptor addresses across the call. -/
theorem rebuildLevelInit_preserves_regs {w init cost r : ℕ}
    {p : Program} {st out : State} {ω : ℕ → Bool}
    (hrun : Runs w p ω (rebuildLevelInit init) st .normal out cost)
    (h₂ : r ≠ 2) (h₃ : r ≠ 3) (h₄ : r ≠ 4) :
    out.regs r = st.regs r := by
  rcases runs_seq_iff.mp hrun with ⟨_, _, _, h, _⟩ | ⟨first, _, _, hs, ht, _⟩
  · cases h
  rcases runs_seq_iff.mp ht with ⟨_, _, _, h, _⟩ | ⟨second, _, _, hc, ha, _⟩
  · cases h
  obtain ⟨v₃, _, _, rfl, _⟩ := runs_assign_iff.mp hs
  obtain ⟨_, _, v₄, _, _, _, _, _, _, rfl, _⟩ := runs_call_iff.mp hc
  obtain ⟨v₂, _, _, rfl, _⟩ := runs_assign_iff.mp ha
  simp [Function.update_of_ne, h₂, h₃, h₄]

/-- Rebuild initializes a level and obtains exactly branch zero's
graph for the next level, charging only the two linked tool calls. -/
theorem rebuildLevelGraph_runs {w L k M N vCap eCap init graph lengths gradient heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool G k M N vCap eCap costs allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient)
    (hh : st.regs 4 = heap)
    (hwords : ∀ a ∈ [graph, lengths, gradient, heap], a < 2 ^ w)
    (hpre : (sparseCoreMachineContract fmt L tool G k M N vCap eCap costs allocation).initPre
      [graph, lengths, gradient, heap] st.mem)
    (hk : k < 2 ^ w)
    (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 5 [graph, lengths, gradient, heap] + 1 < 2 ^ w) :
    let model := tool.init k M N G
      (readEdgeValues st.mem lengths fmt.limbBits L fmt.precision G.E)
      (readEdgeValues st.mem gradient fmt.limbBits L fmt.precision G.E)
    ∃ (out : State) (ret ptr cost : ℕ) (y : R.τ),
      Runs w p ω (rebuildLevelInit init ;; shiftGraphRead (op 3)) st .normal out cost ∧
      out.regs 5 = ret ∧ R.rep heap model y out.mem ∧
      (∃ vc ec, DynGraphAt out.mem (out.mem ptr) vc ec (tool.S model 0)) ∧
      cost + R.phi heap y out.mem ≤ costs.factor M N * (M + 1) * k + 80 := by
  dsimp only
  have hpositive : 0 < k := by
    obtain ⟨_, _, _, _, _, hp, _⟩ := hpre
    exact hp
  have hheapWord := hwords heap (by simp)
  obtain ⟨mid, ptr, c, y, hi, hb, hh', hp, hrep, hinput, hframe, hc⟩ :=
    rebuildLevelInit_runs (ω := ω) himpl hg hl hc hh hwords hpre hz (by omega)
  have hptr := hframe.2.1
  have hfoot : ∀ a, R.foot heap y a → a < ptr := by
    intro a ha
    rcases hframe.2.2.2.2 a ha with ho | ⟨_, hn⟩
    · exact False.elim ho
    · exact hn
  obtain ⟨out, ret, d, z, hr, hret, hrep', hgraph, _, hd⟩ :=
    shiftGraphRead_runs (ω := ω) himpl hb hh' hp hpositive hk hheapWord hrep
      hinput hfoot hframe.2.2.1 (by omega)
  exact ⟨out, ret, ptr, c + d + 1, z,
    runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hi, hr, rfl⟩), hret, hrep', hgraph, by omega⟩

/-- Initialize a level from the prepared numerical tables. The tool receives
their exact live values, extended by zero outside the input graph. -/
theorem rebuildLevelInit_tables_runs {w L k M N vCap eCap init graph lengths gradient heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ)
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool G k M N vCap eCap costs allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient)
    (hh : st.regs 4 = heap)
    (hk : 0 < k) (hG : DynGraphAt st.mem graph vCap eCap G) (hm : G.m ≤ M) (hn : G.n ≤ N)
    (hgraph : graph + dynGraphSize vCap eCap ≤ heap)
    (hLenRoom : lengths + eCap * L ≤ heap) (hGradRoom : gradient + eCap * L ≤ heap)
    (hℓ : EdgeValuesAt st.mem lengths fmt.limbBits L fmt.precision G.E ℓ)
    (hgrad : EdgeValuesAt st.mem gradient fmt.limbBits L fmt.precision G.E g)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 5 [graph, lengths, gradient, heap] < 2 ^ w) :
    let model := tool.init k M N G (fun e => if e ∈ G.E then ℓ e else 0)
      (fun e => if e ∈ G.E then g e else 0)
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (rebuildLevelInit init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 4 = ret ∧
      R.rep heap model y out.mem ∧ SparseCoreInput tool.toSparseCoreTool tool.restart k model G ∧
      R.Respects (fun _ => False) heap (allocation 5 [graph, lengths, gradient, heap])
        st.mem ret heap y out.mem ∧
      cost + R.phi heap y out.mem ≤ costs.factor M N * (M + 1) * k + 11 := by
  dsimp only
  have hwords : ∀ a ∈ [graph, lengths, gradient, heap], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  have hpre := sparseCoreMachineContract_initPre_of_tables (tool := tool) (costs := costs)
    (allocation := allocation) hk hG hm hn hgraph hLenRoom hGradRoom hℓ hgrad hpos
  have hdecode (addr : ℕ) (values : ℕ → ℝ)
      (ht : EdgeValuesAt st.mem addr fmt.limbBits L fmt.precision G.E values) :
      readEdgeValues st.mem addr fmt.limbBits L fmt.precision G.E =
        fun e => if e ∈ G.E then values e else 0 := by
    apply readEdgeValues_eq_of_support
    · exact ht.of_eqOn (fun e he => by simp [he])
    · intro e he
      simp [he]
  rw [← hdecode lengths ℓ hℓ, ← hdecode gradient g hgrad]
  exact rebuildLevelInit_runs himpl hg hl hc hh hwords hpre hz hroom

/-- Record the handle of the new level and select its first branch
(Algorithm 1, page 20). Registers 51 and 52 address the two descriptor
cells, and register 3 holds the handle returned by initialization. -/
@[expose] def storeRebuiltLevel : Stmt :=
  .store (.reg 51) (.reg 3) ;; .store (.reg 52) (.const 0)

/-- Recording the level takes seven steps and changes only its two cells. -/
theorem storeRebuiltLevel_runs {w handleCell branchCell : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool} (hh : st.regs 51 = handleCell)
    (hb : st.regs 52 = branchCell) (hne : handleCell ≠ branchCell) :
    ∃ out, Runs w p ω storeRebuiltLevel st .normal out 7 ∧
      out.mem handleCell = st.regs 3 ∧ out.mem branchCell = 0 ∧
      (∀ a, a ≠ handleCell → a ≠ branchCell → out.mem a = st.mem a) ∧
      out.regs = st.regs ∧ out.pos = st.pos := by
  let mid := { st with mem := Function.update st.mem handleCell (st.regs 3) }
  let out := { mid with mem := Function.update mid.mem branchCell 0 }
  have hstore : Runs w p ω (.store (.reg 51) (.reg 3)) st .normal mid 3 :=
    runs_store_iff.mpr ⟨handleCell, st.regs 3, by simp [Expr.eval, hh],
      by simp [Expr.eval], rfl, rfl, rfl⟩
  have hreset : Runs w p ω (.store (.reg 52) (.const 0)) mid .normal out 3 :=
    runs_store_iff.mpr ⟨branchCell, 0, by simp [Expr.eval, mid, hb],
      by simp [Expr.eval], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 3, 3, hstore, hreset, rfl⟩),
    by simp [out, mid, Function.update_of_ne hne], by simp [out], ?_, rfl, rfl⟩
  intro a hah hab
  simp [out, mid, Function.update_of_ne hah, Function.update_of_ne hab]

/-- Installing the handle and branch zero in the chain descriptor preserves
the initialized tool and its potential when the descriptor lies below it. -/
theorem storeRebuiltLevel_preserves_tool_runs {w handleCell branchCell : ℕ}
    {σ : Type} {R : DSRep σ}
    {s : σ} {x : R.τ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hlocal : R.Local) (hh : st.regs 51 = handleCell) (hb : st.regs 52 = branchCell)
    (hne : handleCell ≠ branchCell)
    (hhBelow : handleCell < st.regs 3) (hbBelow : branchCell < st.regs 3)
    (hfoot : ∀ a, R.foot (st.regs 3) x a → st.regs 3 ≤ a)
    (hrep : R.rep (st.regs 3) s x st.mem) :
    ∃ out, Runs w p ω storeRebuiltLevel st .normal out 7 ∧
      out.mem handleCell = out.regs 3 ∧ out.mem branchCell = 0 ∧
      R.rep (out.regs 3) s x out.mem ∧
      R.phi (out.regs 3) x out.mem = R.phi (st.regs 3) x st.mem ∧
      (∀ a, a ≠ handleCell → a ≠ branchCell → out.mem a = st.mem a) ∧
      out.regs = st.regs ∧ out.pos = st.pos := by
  obtain ⟨out, hrun, hhandle, hbranch, hframe, hregs, hpos⟩ :=
    storeRebuiltLevel_runs (p := p) (ω := ω) hh hb hne
  have hp := hlocal (st.regs 3) s x st.mem out.mem fun a ha =>
    (hframe a (by have := hfoot a ha; omega) (by have := hfoot a ha; omega)).symm
  exact ⟨out, hrun, hregs.symm ▸ hhandle, hbranch, hregs.symm ▸ hp.1 hrep,
    by rw [hregs, hp.2], hframe, hregs, hpos⟩

/-- The first sparse core of Algorithm 1 Rebuild (page 20) is initialized
with the new graph and the numbers inherited from the earlier levels. -/
theorem rebuildFirstCore_eq (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i : ℕ) (hi : i < P.d)
    (Gnew : MGraph) (enc : ℕ) :
    (algorithm1_rebuild T L P st i Gnew enc).1.scState i =
      T.init P.k (st.lvlM i) st.N₀ Gnew (st.toTreeChain.chainLen st.ℓ i) (st.toTreeChain.chainGrad st.g i) := by
  let graphs := fun j => if j = i then Gnew else st.G j
  let partialChain : TreeChain :=
    { d := P.d, k := P.k, G := graphs, lsfs := fun j => T.lsfs (st.scState j), bran := st.bran,
      S := fun j => T.S (st.scState j), emb := fun j => T.emb (st.scState j), lastK := 1,
      lastLSFs := fun _ => ⟨graphs i, ⟨graphs i, ∅⟩, fun _ => 1⟩, lastBran := 0 }
  have hrem : P.d - i = (P.d - (i + 1)) + 1 := by omega
  have hbuild : (algorithm1_rebuild T L P st i Gnew enc).1.scState i =
      T.init P.k (st.lvlM i) st.N₀ Gnew (partialChain.chainLen st.ℓ i) (partialChain.chainGrad st.g i) := by
    unfold algorithm1_rebuild
    rw [dite_eq_left hi, hrem]
    simp only [rebuildSuffix]
    rw [rebuildSuffix_state_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Nat.lt_succ_self _)]
    simp only [partialChain, graphs, ite_true, ite_eq_left rfl]
  have hgraph (j : ℕ) (hj : j < i) : partialChain.G j = st.toTreeChain.G j := by
    simp [partialChain, graphs, Nat.ne_of_lt hj, ChainState.toTreeChain]
  have hforest (j : ℕ) (hj : j < i) : partialChain.activeLSF j = st.toTreeChain.activeLSF j := by
    simp [partialChain, ChainState.toTreeChain, TreeChain.activeLSF, hj.trans hi]
  rw [hbuild, chainLen_congr_lt st.ℓ i hgraph hforest, chainGrad_congr_lt st.g i hgraph hforest]

/-- Initialize a rebuilt level from exact model inputs. The machine
uses the active-edge tables and extends each input by zero. -/
theorem rebuildLevelInit_exact_runs {w L M N vCap eCap init graph lengths gradient heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : ChainParams} {model : tool.State}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ)
    (hmodel : model = tool.init P.k M N G
      (fun e => if e ∈ G.E then ℓ e else 0) (fun e => if e ∈ G.E then g e else 0))
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool G P.k M N vCap eCap costs allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient)
    (hh : st.regs 4 = heap)
    (hG : DynGraphAt st.mem graph vCap eCap G) (hm : G.m ≤ M) (hn : G.n ≤ N)
    (hgraph : graph + dynGraphSize vCap eCap ≤ heap)
    (hLenRoom : lengths + eCap * L ≤ heap) (hGradRoom : gradient + eCap * L ≤ heap)
    (hℓ : EdgeValuesAt st.mem lengths fmt.limbBits L fmt.precision G.E ℓ)
    (hgrad : EdgeValuesAt st.mem gradient fmt.limbBits L fmt.precision G.E g)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 5 [graph, lengths, gradient, heap] < 2 ^ w) :
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (rebuildLevelInit init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 4 = ret ∧
      R.rep heap model y out.mem ∧ SparseCoreInput tool.toSparseCoreTool tool.restart P.k model G ∧
      R.Respects (fun _ => False) heap (allocation 5 [graph, lengths, gradient, heap])
        st.mem ret heap y out.mem ∧
      cost + R.phi heap y out.mem ≤ costs.factor M N * (M + 1) * P.k + 11 := by
  have hrun := rebuildLevelInit_tables_runs (ω := ω) ℓ g himpl hg hl hc hh
    P.hk hG hm hn hgraph hLenRoom hGradRoom hℓ hgrad hpos hz hroom
  dsimp only at hrun
  rw [hmodel]
  exact hrun

/-- Initialize the first periodic Rebuild level and represent the model's
rebuilt core when the fixed-point tables give the full model inputs. -/
theorem rebuildFirstCore_exact_runs {w L M N vCap eCap init graph lengths gradient heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {last : LastLevelTool} {P : ChainParams}
    (chain : ChainState tool P) (i : Fin P.d) (enc : ℕ)
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ)
    (hℓModel : ℓ = chain.toTreeChain.chainLen chain.ℓ i.val)
    (hgModel : g = chain.toTreeChain.chainGrad chain.g i.val)
    (hM : chain.lvlM i.val = M) (hN : chain.N₀ = N)
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool G P.k M N vCap eCap costs allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient)
    (hh : st.regs 4 = heap)
    (hG : DynGraphAt st.mem graph vCap eCap G) (hm : G.m ≤ M) (hn : G.n ≤ N)
    (hgraph : graph + dynGraphSize vCap eCap ≤ heap)
    (hLenRoom : lengths + eCap * L ≤ heap) (hGradRoom : gradient + eCap * L ≤ heap)
    (hℓ : EdgeValuesAt st.mem lengths fmt.limbBits L fmt.precision G.E ℓ)
    (hgrad : EdgeValuesAt st.mem gradient fmt.limbBits L fmt.precision G.E g)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e) (hz : ZeroFrom st.mem heap)
    (hℓSupport : ∀ e ∉ G.E, ℓ e = 0) (hgSupport : ∀ e ∉ G.E, g e = 0)
    (hroom : heap + allocation 5 [graph, lengths, gradient, heap] < 2 ^ w) :
    let model := (algorithm1_rebuild tool last P chain i.val G enc).1.scState i.val
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (rebuildLevelInit init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 4 = ret ∧
      R.rep heap model y out.mem ∧ SparseCoreInput tool.toSparseCoreTool tool.restart P.k model G ∧
      R.Respects (fun _ => False) heap (allocation 5 [graph, lengths, gradient, heap])
        st.mem ret heap y out.mem ∧
      cost + R.phi heap y out.mem ≤ costs.factor M N * (M + 1) * P.k + 11 := by
  have hmodel := rebuildFirstCore_eq tool last P chain i.val i.isLt G enc
  rw [← hℓModel, ← hgModel, hM, hN] at hmodel
  have hmask (f : ℕ → ℝ) (hf : ∀ e ∉ G.E, f e = 0) :
      (fun e => if e ∈ G.E then f e else 0) = f := by
    funext e
    by_cases he : e ∈ G.E <;> simp [he, hf]
  apply rebuildLevelInit_exact_runs ℓ g _ himpl hg hl hc hh hG hm hn
    hgraph hLenRoom hGradRoom hℓ hgrad hpos hz hroom
  simpa only [hmask ℓ hℓSupport, hmask g hgSupport] using hmodel

/-- Install the new handle and branch after initializing a periodic rebuild level. -/
@[expose] def rebuildInstallLevel (init : ℕ) : Stmt :=
  rebuildLevelInit init ;; storeRebuiltLevel

/-- A periodic rebuild level records its initialized model core and
selects branch zero. The descriptor cells lie below the new allocation. -/
theorem rebuildInstallCore_runs {w L M N vCap eCap init graph lengths gradient heap handleCell branchCell : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : ChainParams} {model : tool.State}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ)
    (hmodel : model = tool.init P.k M N G
      (fun e => if e ∈ G.E then ℓ e else 0) (fun e => if e ∈ G.E then g e else 0))
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool G P.k M N vCap eCap costs allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient)
    (hh : st.regs 4 = heap)
    (hG : DynGraphAt st.mem graph vCap eCap G) (hm : G.m ≤ M) (hn : G.n ≤ N)
    (hgraph : graph + dynGraphSize vCap eCap ≤ heap)
    (hLenRoom : lengths + eCap * L ≤ heap) (hGradRoom : gradient + eCap * L ≤ heap)
    (hℓ : EdgeValuesAt st.mem lengths fmt.limbBits L fmt.precision G.E ℓ)
    (hgrad : EdgeValuesAt st.mem gradient fmt.limbBits L fmt.precision G.E g)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 5 [graph, lengths, gradient, heap] < 2 ^ w)
    (hhCell : st.regs 51 = handleCell) (hbCell : st.regs 52 = branchCell)
    (hne : handleCell ≠ branchCell) (hhBelow : handleCell < heap) (hbBelow : branchCell < heap) :
    ∃ out ret cost y,
      Runs w p ω (rebuildInstallLevel init) st .normal out cost ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧ out.regs 4 = ret ∧
      R.rep heap model y out.mem ∧ ZeroFrom out.mem ret ∧
      SparseCoreInput tool.toSparseCoreTool tool.restart P.k model G ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧
      heap ≤ ret ∧ ret ≤ heap + allocation 5 [graph, lengths, gradient, heap] ∧
      (∀ a, R.foot heap y a → heap ≤ a ∧ a < ret) ∧
      (∀ a < heap, a ≠ handleCell → a ≠ branchCell → out.mem a = st.mem a) ∧
      cost + R.phi heap y out.mem ≤ costs.factor M N * (M + 1) * P.k + 19 := by
  obtain ⟨mid, ret, c, y, hr, hzeroBranch, hhandle, hret, hrep, hinput, hframe, hc'⟩ :=
    rebuildLevelInit_exact_runs ℓ g hmodel himpl
      hg hl hc hh hG hm hn hgraph hLenRoom hGradRoom hℓ hgrad hpos hz hroom
  have hfoot (a : ℕ) (ha : R.foot heap y a) : heap ≤ a ∧ a < ret :=
    (hframe.2.2.2.2 a ha).resolve_left id
  have hh' := (rebuildLevelInit_preserves_regs (r := 51) hr (by decide) (by decide) (by decide)).trans hhCell
  have hb' := (rebuildLevelInit_preserves_regs (r := 52) hr (by decide) (by decide) (by decide)).trans hbCell
  obtain ⟨out, hs, hcell, hbranch, hrep', hphi, hmem, hregs, _⟩ :=
    storeRebuiltLevel_preserves_tool_runs himpl.1 hh' hb' hne
      (hhandle.symm ▸ hhBelow) (hhandle.symm ▸ hbBelow)
      (fun a ha => hhandle.symm ▸ (hfoot a (hhandle ▸ ha)).1) (hhandle.symm ▸ hrep)
  have houtHandle : out.regs 3 = heap := hregs ▸ hhandle
  refine ⟨out, ret, c + 8, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, c, 7, hr, hs, by omega⟩), hcell.trans houtHandle,
    hbranch, hregs ▸ hret, houtHandle ▸ hrep', ?_,
    hinput, hregs ▸ hzeroBranch, houtHandle, hframe.1, hframe.2.1, hfoot, ?_, ?_⟩
  · intro a ha
    have hlo := hframe.1
    exact (hmem a (by omega) (by omega)).trans (hframe.2.2.1 a ha)
  · intro a ha hhc hbc
    exact (hmem a hhc hbc).trans (hframe.2.2.2.1 a ha id)
  · rw [houtHandle, hhandle] at hphi
    omega

/-- Recording the descriptor preserves the caller registers outside the initializer outputs. -/
theorem rebuildInstallLevel_preserves_regs {w init cost r : ℕ}
    {p : Program} {st out : State} {ω : ℕ → Bool}
    (h : Runs w p ω (rebuildInstallLevel init) st .normal out cost)
    (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) : out.regs r = st.regs r := by
  rcases runs_seq_iff.mp h with ⟨_, _, _, hbad, _⟩ | ⟨mid, _, _, hi, hs, _⟩
  · cases hbad
  rcases runs_seq_iff.mp hs with ⟨_, _, _, hbad, _⟩ | ⟨first, _, _, h₁, h₂, _⟩
  · cases hbad
  obtain ⟨_, _, _, _, _, rfl, _⟩ := runs_store_iff.mp h₁
  obtain ⟨_, _, _, _, _, rfl, _⟩ := runs_store_iff.mp h₂
  exact rebuildLevelInit_preserves_regs (out := mid) hi h2 h3 h4

/-- Read branch zero's sparsifier after recording the rebuilt level
(Algorithm 1, page 20). -/
@[expose] def rebuildInstallReadGraph (init read : ℕ) : Stmt :=
  rebuildInstallLevel init ;; shiftGraphRead read ;; .assign 7 (.reg 6) ;; loadShiftGraph

/-- The readout preserves the installed descriptor and yields the
sparsifier and free heap for the next level. -/
theorem rebuildInstallReadGraph_runs
    {w L k M N vCap eCap init heap ret handleCell branchCell cost : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {initialGraph G : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep T.State} {model : T.State} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st mid : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L T initialGraph k M N vCap eCap costs allocation))
    (hinit : Runs w p ω (rebuildInstallLevel init) st .normal mid cost)
    (hh : mid.mem handleCell = heap) (hb : mid.mem branchCell = 0)
    (hhBelow : handleCell < heap) (hbBelow : branchCell < heap)
    (h2 : mid.regs 2 = 0) (h3 : mid.regs 3 = heap) (h4 : mid.regs 4 = ret)
    (hk : 0 < k) (hkw : k < 2 ^ w) (hhw : heap < 2 ^ w)
    (hrep : R.rep heap model x mid.mem)
    (hinput : SparseCoreInput T.toSparseCoreTool T.restart k model G)
    (hheap : heap ≤ ret) (hfoot : ∀ a, R.foot heap x a → heap ≤ a ∧ a < ret)
    (hz : ZeroFrom mid.mem ret) (hroom : ret + 1 < 2 ^ w) :
    ∃ out top time y,
      Runs w p ω (rebuildInstallReadGraph init (op 3)) st .normal out time ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧ out.regs 5 = top ∧
      R.rep heap model y out.mem ∧
      (∃ vc ec, DynGraphAt out.mem (out.regs 6) vc ec (T.S model 0)) ∧
      R.Respects (R.foot heap x) ret 1 mid.mem top heap y out.mem ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 4 = ret ∧ out.regs 7 = st.regs 6 ∧
      (∀ a < heap, out.mem a = mid.mem a) ∧
      (∀ r, r = 8 ∨ 13 ≤ r → out.regs r = st.regs r) ∧
      time + R.phi heap y out.mem ≤ cost + R.phi heap x mid.mem + 76 := by
  obtain ⟨out, top, c, y, hr, htop, hrp, ⟨vc, ec, hg⟩, hf, hc, hregs⟩ :=
    shiftGraphRead_runs himpl h2 h3 h4 hk hkw hhw hrep hinput
      (fun a ha => (hfoot a ha).2) hz hroom
  have hkeep (a : ℕ) (ha : a < heap) : out.mem a = mid.mem a :=
    hf.2.2.2.1 a (ha.trans_le hheap) (fun h => (Nat.not_le_of_lt ha) (hfoot a h).1)
  have hslot := (hregs 4 (by decide)).trans h4
  let saved := { out with regs := Function.update out.regs 7 (out.regs 6) }
  have hsave : Runs w p ω (.assign 7 (.reg 6)) out .normal saved 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  obtain ⟨ready, hload, _, hgraph, hmem, _, hkeepReg⟩ :=
    loadShiftGraph_runs (ω := ω) (st := saved) (by simpa [saved, Function.update_of_ne] using hslot) hg
  have hsaveReg (r : ℕ) (hr : r ≠ 7) : saved.regs r = out.regs r :=
    Function.update_of_ne hr _ _
  have hgraphReg : ready.regs 7 = st.regs 6 := by
    rw [hkeepReg 7 (by decide)]
    change Function.update out.regs 7 (out.regs 6) 7 = st.regs 6
    rw [Function.update_self, hregs 6 (by decide), rebuildInstallLevel_preserves_regs hinit (by decide) (by decide) (by decide)]
  refine ⟨ready, top, cost + c + 8, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, cost, c + 7, hinit,
      runs_seq_iff.mpr (Or.inr ⟨out, c, 6, hr,
        runs_seq_iff.mpr (Or.inr ⟨saved, 2, 3, hsave, hload, rfl⟩), by omega⟩), by omega⟩),
    hmem.symm ▸ (hkeep _ hhBelow).trans hh, hmem.symm ▸ (hkeep _ hbBelow).trans hb,
    ((hkeepReg 5 (by decide)).trans (hsaveReg 5 (by decide))).trans htop, hmem.symm ▸ hrp, ⟨vc, ec, hgraph⟩,
    hmem.symm ▸ hf,
    ((hkeepReg 2 (by decide)).trans (hsaveReg 2 (by decide))).trans ((hregs 2 (by decide)).trans h2),
    ((hkeepReg 3 (by decide)).trans (hsaveReg 3 (by decide))).trans ((hregs 3 (by decide)).trans h3), ((hkeepReg 4 (by decide)).trans (hsaveReg 4 (by decide))).trans hslot, hgraphReg, (by simpa only [hmem] using hkeep), ?_, ?_⟩
  · intro r hr
    exact (hkeepReg r (by omega)).trans ((hsaveReg r (by omega)).trans
      ((hregs r (by omega)).trans (rebuildInstallLevel_preserves_regs hinit
        (by omega) (by omega) (by omega))))
  · rw [hmem]
    change cost + c + 8 + R.phi heap y out.mem ≤ _
    omega

/-- The graph passed to the next rebuild level is branch zero's
sparsifier of the first rebuilt core (Algorithm 1, page 20). -/
theorem rebuildFirstCore_nextGraph_eq (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i : ℕ) (hi : i < P.d)
    (Gnew : MGraph) (enc : ℕ) :
    let result := (algorithm1_rebuild T L P st i Gnew enc).1
    result.G (i + 1) = T.S (result.scState i) 0 := by
  dsimp only
  have hrem : P.d - i = (P.d - (i + 1)) + 1 := by omega
  unfold algorithm1_rebuild
  rw [dite_eq_left hi, hrem]
  simp only [rebuildSuffix]
  rw [treeEdit_rebuildSuffix_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ le_rfl,
    rebuildSuffix_state_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Nat.lt_succ_self _)]
  simp only [ite_true]

/-- Install the first periodic rebuild core and read its branch-zero
sparsifier as the exact starting graph of the remaining rebuild levels. -/
theorem rebuildInstallCore_read_runs {w L M N vCap eCap init graph lengths gradient heap handleCell branchCell : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : ChainParams} {model : tool.State} {nextGraph : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ)
    (hmodel : model = tool.init P.k M N G
      (fun e => if e ∈ G.E then ℓ e else 0) (fun e => if e ∈ G.E then g e else 0))
    (hnextGraph : nextGraph = tool.S model 0)
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool G P.k M N vCap eCap costs allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient)
    (hh : st.regs 4 = heap)
    (hG : DynGraphAt st.mem graph vCap eCap G) (hm : G.m ≤ M) (hn : G.n ≤ N)
    (hgraph : graph + dynGraphSize vCap eCap ≤ heap)
    (hLenRoom : lengths + eCap * L ≤ heap) (hGradRoom : gradient + eCap * L ≤ heap)
    (hℓ : EdgeValuesAt st.mem lengths fmt.limbBits L fmt.precision G.E ℓ)
    (hgrad : EdgeValuesAt st.mem gradient fmt.limbBits L fmt.precision G.E g)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 5 [graph, lengths, gradient, heap] + 1 < 2 ^ w)
    (hkw : P.k < 2 ^ w)
    (hhCell : st.regs 51 = handleCell) (hbCell : st.regs 52 = branchCell)
    (hne : handleCell ≠ branchCell) (hhBelow : handleCell < heap) (hbBelow : branchCell < heap) :
    ∃ out top cost y,
      Runs w p ω (rebuildInstallReadGraph init (op 3)) st .normal out cost ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧ out.regs 5 = top ∧
      R.rep heap model y out.mem ∧
      (∃ vc ec, DynGraphAt out.mem (out.regs 6) vc ec nextGraph) ∧
      heap ≤ top ∧ ZeroFrom out.mem top ∧
      SparseCoreInput tool.toSparseCoreTool tool.restart P.k model G ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 7 = graph ∧
      (∀ addr, R.foot heap y addr → heap ≤ addr ∧ addr < top) ∧
      (∀ a < heap, a ≠ handleCell → a ≠ branchCell → out.mem a = st.mem a) ∧
      (∀ r, r = 8 ∨ 13 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi heap y out.mem ≤ costs.factor M N * (M + 1) * P.k + 95 := by
  obtain ⟨mid, slot, c, x, hrun, hh', hb', hret, hrep, hz', hinput, h2, h3,
    hlo, hhi, hfoot, hinitFrame, hcost⟩ :=
    rebuildInstallCore_runs ℓ g hmodel himpl
      hg hl hc hh hG hm hn hgraph hLenRoom hGradRoom hℓ hgrad hpos hz
      (by omega) hhCell hbCell hne hhBelow hbBelow
  obtain ⟨out, top, cost, y, hr, hhandle, hbranch, htop, hrep', hgraph', hframe, hbranchReg, hhandleReg, _, hgraphReg, hreadFrame, hreadRegs, hc'⟩ :=
    rebuildInstallReadGraph_runs himpl hrun hh' hb' hhBelow hbBelow h2 h3 hret
      P.hk hkw (by omega) hrep hinput hlo hfoot hz' (by omega)
  rw [← hnextGraph] at hgraph'
  refine ⟨out, top, cost, y, hr, hhandle, hbranch, htop, hrep', hgraph', hlo.trans hframe.1, hframe.2.2.1,
    hinput, hbranchReg, hhandleReg, hgraphReg.trans hg, ?_,
    (fun a ha hh hb => (hreadFrame a ha).trans (hinitFrame a ha hh hb)), hreadRegs, by omega⟩
  intro addr ha
  rcases hframe.2.2.2.2 addr ha with hold | ⟨hLower, hUpper⟩
  · exact ⟨(hfoot addr hold).1, (hfoot addr hold).2.trans_le hframe.1⟩
  · exact ⟨hlo.trans hLower, hUpper⟩

/-- Keep the next Rebuild graph in caller memory before asking the core
for its selected forest (Algorithm 1, page 20). -/
@[expose] def rebuildInstallCopyGraph (init read : ℕ) : Stmt :=
  rebuildInstallReadGraph init read ;; copyGraphFromHeader

/-- Copy the next graph while retaining the rebuilt tool, its descriptor,
and its potential. The output graph is separate from the tool footprint. -/
theorem rebuildInstallCopyGraph_runs {w init read cost top vc ec heap handleCell branchCell : ℕ}
    {σ : Type} {R : DSRep σ} {model : σ} {x : R.τ} {G : MGraph}
    {p : Program} {st mid : State} {ω : ℕ → Bool}
    (hinit : Runs w p ω (rebuildInstallReadGraph init read) st .normal mid cost)
    (hlocal : R.Local) (hrep : R.rep heap model x mid.mem)
    (hfoot : ∀ a, R.foot heap x a → a < top)
    (hhandle : mid.mem handleCell = heap) (hbranch : mid.mem branchCell = 0)
    (hhBelow : handleCell < top) (hbBelow : branchCell < top)
    (h2 : mid.regs 2 = 0) (h3 : mid.regs 3 = heap) (h5 : mid.regs 5 = top)
    (hgraph : DynGraphAt mid.mem (mid.regs 6) vc ec G)
    (hdisj : mid.regs 6 + dynGraphSize vc ec ≤ top)
    (hword : top + dynGraphSize vc ec < 2 ^ w) (hw : 9 < 2 ^ w) (hz : ZeroFrom mid.mem top) :
    ∃ out time, Runs w p ω (rebuildInstallCopyGraph init read) st .normal out time ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 6 = top ∧
      out.regs 5 = top + dynGraphSize vc ec ∧ ZeroFrom out.mem (out.regs 5) ∧
      DynGraphAt out.mem top vc ec G ∧ R.rep heap model x out.mem ∧
      out.regs 7 = mid.regs 7 ∧ (∀ a < top, out.mem a = mid.mem a) ∧
      (∀ r, r = 8 ∨ 13 ≤ r → out.regs r = mid.regs r) ∧
      time + R.phi heap x out.mem ≤ cost + R.phi heap x mid.mem + 17 * dynGraphSize vc ec + 44 := by
  obtain ⟨out, c, hr, hg, hout, hheap, hzero, hrep', hphi, _, hmem, _, hc, hregs⟩ :=
    copyShiftGraph_preserves_tool_runs hlocal hrep hfoot rfl h5 hgraph hdisj hword hw hz
  refine ⟨out, cost + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, cost, c, hinit, hr, rfl⟩),
    (hmem _ hhBelow).trans hhandle, (hmem _ hbBelow).trans hbranch,
    (hregs 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2,
    (hregs 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h3,
    hout, hheap, hzero, hout ▸ hg, hrep',
    hregs 7 (by decide) (by decide) (by decide) (by decide) (by decide), hmem,
    (fun r hr => hregs r (by omega) (by omega) (by omega) (by omega) (by omega)), ?_⟩
  rw [hphi]
  omega

/-- Read the rebuilt branch-zero forest after copying the next graph. -/
@[expose] def rebuildReadForest (init graphRead forestRead : ℕ) : Stmt :=
  rebuildInstallCopyGraph init graphRead ;; shiftForestRead forestRead

/-- The forest readout preserves the copied next graph and the rebuilt
descriptor. Its footprint can grow into the four readout words. -/
theorem rebuildReadForest_runs
    {w L k M N vCap eCap init handle graph heap copied vc ec hc bc prefixCost : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {initialGraph G H : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep T.State} {s : T.State} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st mid : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L T initialGraph k M N vCap eCap costs allocation))
    (hprefix : Runs w p ω (rebuildInstallCopyGraph init (op 3)) st .normal mid prefixCost)
    (hb : mid.regs 2 = 0) (hh : mid.regs 3 = handle) (hg : mid.regs 7 = graph)
    (hp : mid.regs 5 = heap) (hk : 0 < k) (hw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hrep : R.rep handle s x mid.mem)
    (hG : SparseCoreGraphAt T.toSparseCoreTool T.restart k s mid.mem graph vCap eCap G)
    (hgraphRoom : graph + dynGraphSize vCap eCap ≤ heap)
    (hfoot : ∀ a, R.foot handle x a → a < copied)
    (hsep : ∀ a, R.foot handle x a → handle ≤ a)
    (hz : ZeroFrom mid.mem heap) (hroom : heap + 4 < 2 ^ w)
    (hcopyReg : mid.regs 6 = copied) (hcopy : DynGraphAt mid.mem copied vc ec H)
    (hcopyEnd : copied + dynGraphSize vc ec ≤ heap)
    (hhc : mid.mem hc = handle) (hbc : mid.mem bc = 0)
    (hhBelow : hc < handle) (hbBelow : bc < handle) (halloc : handle ≤ heap) :
    ∃ out ret cost y,
      Runs w p ω (rebuildReadForest init (op 3) (op 2)) st .normal out cost ∧
      out.regs 5 = ret ∧ out.regs 9 = heap ∧ out.regs 6 = copied ∧
      DynGraphAt out.mem copied vc ec H ∧ out.mem hc = handle ∧ out.mem bc = 0 ∧
      R.rep handle s y out.mem ∧
      (∃ fv fe, LSFAt out.mem heap fv fe fmt.limbBits L fmt.precision G.E (T.lsfs s 0)) ∧
      heap ≤ ret ∧ ZeroFrom out.mem ret ∧
      (∀ addr < handle, out.mem addr = mid.mem addr) ∧
      (∀ addr, R.foot handle y addr → handle ≤ addr ∧ addr < ret) ∧
      (∀ r, r = 8 ∨ 13 ≤ r → out.regs r = mid.regs r) ∧
      cost + R.phi handle y out.mem ≤ prefixCost + R.phi handle x mid.mem + 73 := by
  have hfootHeap (a : ℕ) (ha : R.foot handle x a) : a < heap :=
    (hfoot a ha).trans_le ((Nat.le_add_right _ _).trans hcopyEnd)
  obtain ⟨out, ret, c, y, hr, hret, hhead, hrep', hlsf, hframe, hcost, hregs⟩ :=
    shiftForestRead_runs himpl hb hh hg hp hk hw hhw hrep hG hgraphRoom hfootHeap hz hroom
  have hg' := hcopy.of_agree (fun a hlo hhi =>
    hframe.2.2.2.1 a (hhi.trans_le hcopyEnd) (fun hf => (Nat.not_lt_of_ge hlo) (hfoot a hf)))
  have hkeep (a : ℕ) (ha : a < handle) : out.mem a = mid.mem a :=
    hframe.2.2.2.1 a (ha.trans_le halloc) (fun hf => (Nat.not_le_of_lt ha) (hsep a hf))
  refine ⟨out, ret, prefixCost + c + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, prefixCost, c, hprefix, hr, rfl⟩),
    hret, hhead, (hregs 6 (by decide) (by decide)).trans hcopyReg, hg',
    (hkeep _ hhBelow).trans hhc, (hkeep _ hbBelow).trans hbc,
    hrep', hlsf, hframe.1, hframe.2.2.1, hkeep, ?_, (fun r hr => hregs r (by omega) (by omega)), by omega⟩
  intro addr ha
  rcases hframe.2.2.2.2 addr ha with hold | ⟨hlo, hhi⟩
  · exact ⟨hsep addr hold, (hfootHeap addr hold).trans_le hframe.1⟩
  · exact ⟨halloc.trans hlo, hhi⟩

/-- The initialized periodic rebuild core supplies a caller-owned copy
of the exact graph at the next level. -/
theorem rebuildInstallCore_copy_runs {w L M N vCap eCap init graph lengths gradient heap handleCell branchCell reserve : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : ChainParams} {model : tool.State} {nextGraph : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ)
    (hmodel : model = tool.init P.k M N G
      (fun e => if e ∈ G.E then ℓ e else 0) (fun e => if e ∈ G.E then g e else 0))
    (hnextGraph : nextGraph = tool.S model 0)
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool G P.k M N vCap eCap costs allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient)
    (hh : st.regs 4 = heap)
    (hG : DynGraphAt st.mem graph vCap eCap G) (hm : G.m ≤ M) (hn : G.n ≤ N)
    (hgraph : graph + dynGraphSize vCap eCap ≤ heap)
    (hLenRoom : lengths + eCap * L ≤ heap) (hGradRoom : gradient + eCap * L ≤ heap)
    (hℓ : EdgeValuesAt st.mem lengths fmt.limbBits L fmt.precision G.E ℓ)
    (hgrad : EdgeValuesAt st.mem gradient fmt.limbBits L fmt.precision G.E g)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 5 [graph, lengths, gradient, heap] + 1 < 2 ^ w)
    (hkw : P.k < 2 ^ w)
    (hhCell : st.regs 51 = handleCell) (hbCell : st.regs 52 = branchCell)
    (hne : handleCell ≠ branchCell) (hhBelow : handleCell < heap) (hbBelow : branchCell < heap)
    (hw : 9 < 2 ^ w)
    (hcopyRoom : ∀ mid top vc ec cost,
      Runs w p ω (rebuildInstallReadGraph init (op 3)) st .normal mid cost →
      mid.regs 5 = top →
      DynGraphAt mid.mem (mid.regs 6) vc ec
        nextGraph →
      mid.regs 6 + dynGraphSize vc ec ≤ top ∧ top + dynGraphSize vc ec + reserve < 2 ^ w) :
    ∃ out copied vc ec cost y,
      Runs w p ω (rebuildInstallCopyGraph init (op 3)) st .normal out cost ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 6 = copied ∧ out.regs 7 = graph ∧
      out.regs 5 = copied + dynGraphSize vc ec ∧ ZeroFrom out.mem (out.regs 5) ∧ out.regs 5 + reserve < 2 ^ w ∧
      heap ≤ copied ∧ DynGraphAt out.mem copied vc ec nextGraph ∧
      R.rep heap model y out.mem ∧
      SparseCoreInput tool.toSparseCoreTool tool.restart P.k model G ∧
      (∀ addr, R.foot heap y addr → heap ≤ addr ∧ addr < copied) ∧
      (∀ addr < heap, addr ≠ handleCell → addr ≠ branchCell → out.mem addr = st.mem addr) ∧
      (∀ r, r = 8 ∨ 13 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi heap y out.mem ≤
        costs.factor M N * (M + 1) * P.k + 17 * dynGraphSize vc ec + 139 := by
  obtain ⟨mid, top, c, y, hr, hd, hb, htop, hrep, ⟨vc, ec, hnext⟩, hlo, hz', hin,
    h2, h3, h7, hfoot, hframe, hreadRegs, hcost⟩ :=
    rebuildInstallCore_read_runs ℓ g hmodel hnextGraph himpl
      hg hl hc hh hG hm hn hgraph hLenRoom hGradRoom hℓ hgrad hpos hz
      hroom hkw hhCell hbCell hne hhBelow hbBelow
  obtain ⟨hsrc, hdst⟩ := hcopyRoom mid top vc ec c hr htop hnext
  obtain ⟨out, cost, hr', hd', hb', h2', h3', h6', h5', hz'', hgraph', hrep', h7', hmem, hcopyRegs, hc'⟩ :=
    rebuildInstallCopyGraph_runs hr himpl.1 hrep (fun a ha => (hfoot a ha).2)
      hd hb (hhBelow.trans_le hlo) (hbBelow.trans_le hlo) h2 h3 htop hnext hsrc (by omega) hw hz'
  exact ⟨out, top, vc, ec, cost, y, hr', hd', hb', h2', h3', h6', h7'.trans h7,
    h5', hz'', by omega, hlo, hgraph', hrep', hin, hfoot,
    (fun a ha hd hb => (hmem a (ha.trans_le hlo)).trans (hframe a ha hd hb)),
    (fun r hr => (hcopyRegs r hr).trans (hreadRegs r hr)), by omega⟩

/-- Read the first rebuilt core's branch-zero forest while retaining the
caller-owned graph at the next model level (Algorithm 1, page 20). -/
theorem rebuildCore_forest_runs {w L M N vCap eCap init graph lengths gradient heap handleCell branchCell : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : ChainParams} {model : tool.State} {nextGraph : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ)
    (hmodel : model = tool.init P.k M N G
      (fun e => if e ∈ G.E then ℓ e else 0) (fun e => if e ∈ G.E then g e else 0))
    (hnextGraph : nextGraph = tool.S model 0)
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool G P.k M N vCap eCap costs allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient)
    (hh : st.regs 4 = heap)
    (hG : DynGraphAt st.mem graph vCap eCap G) (hm : G.m ≤ M) (hn : G.n ≤ N)
    (hgraph : graph + dynGraphSize vCap eCap ≤ heap)
    (hLenRoom : lengths + eCap * L ≤ heap) (hGradRoom : gradient + eCap * L ≤ heap)
    (hℓ : EdgeValuesAt st.mem lengths fmt.limbBits L fmt.precision G.E ℓ)
    (hgrad : EdgeValuesAt st.mem gradient fmt.limbBits L fmt.precision G.E g)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 5 [graph, lengths, gradient, heap] + 1 < 2 ^ w)
    (hkw : P.k < 2 ^ w)
    (hhCell : st.regs 51 = handleCell) (hbCell : st.regs 52 = branchCell)
    (hne : handleCell ≠ branchCell) (hhBelow : handleCell < heap) (hbBelow : branchCell < heap)
    (hw : 9 < 2 ^ w)
    (hcopyRoom : ∀ mid top vc ec cost,
      Runs w p ω (rebuildInstallReadGraph init (op 3)) st .normal mid cost →
      mid.regs 5 = top →
      DynGraphAt mid.mem (mid.regs 6) vc ec
        nextGraph →
      mid.regs 6 + dynGraphSize vc ec ≤ top ∧ top + dynGraphSize vc ec + 4 < 2 ^ w)
    (hgraphSep : ∀ addr, graph ≤ addr → addr < graph + dynGraphSize vCap eCap →
      addr ≠ handleCell ∧ addr ≠ branchCell) :
    ∃ out copied vc ec cost y,
      Runs w p ω (rebuildReadForest init (op 3) (op 2)) st .normal out cost ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧
      out.regs 6 = copied ∧ DynGraphAt out.mem copied vc ec nextGraph ∧
      R.rep heap model y out.mem ∧
      (∃ fv fe, LSFAt out.mem (out.regs 9) fv fe fmt.limbBits L fmt.precision G.E
        (tool.lsfs model 0)) ∧
      copied + dynGraphSize vc ec ≤ out.regs 5 ∧
      heap ≤ copied ∧ heap ≤ out.regs 5 ∧ out.regs 9 + 3 < 2 ^ w ∧ ZeroFrom out.mem (out.regs 5) ∧
      (∀ addr < heap, addr ≠ handleCell → addr ≠ branchCell → out.mem addr = st.mem addr) ∧
      (∀ addr, R.foot heap y addr → heap ≤ addr ∧ addr < out.regs 5) ∧
      (∀ r, r = 8 ∨ 13 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi heap y out.mem ≤
        costs.factor M N * (M + 1) * P.k + 17 * dynGraphSize vc ec + 212 := by
  obtain ⟨mid, copied, vc, ec, c, x, hr, hd, hb, h2, h3, h6, h7, h5, hz', hmidRoom, hlo, hnext,
    hrep, hin, hfoot, hframe, hcopyRegs, hc'⟩ :=
    rebuildInstallCore_copy_runs ℓ g hmodel hnextGraph himpl
      hg hl hc hh hG hm hn hgraph hLenRoom hGradRoom hℓ hgrad hpos hz
      hroom hkw hhCell hbCell hne hhBelow hbBelow hw
      hcopyRoom
  have hG' := hG.of_agree (fun addr hlo hhi => hframe addr (hhi.trans_le hgraph)
    (hgraphSep addr hlo hhi).1 (hgraphSep addr hlo hhi).2)
  obtain ⟨out, ret, cost, y, hrun, hret, hheader, hgraphReg, hgraph', hh', hb',
      hrep', hlsfs, hretLo, hz'', hkeep, hfootOut, hforestRegs, hcost⟩ :=
    rebuildReadForest_runs himpl hr h2 h3 h7 rfl P.hk hkw (by omega) hrep
      ⟨hin, hG'⟩ (by omega) (fun a ha => (hfoot a ha).2) (fun a ha => (hfoot a ha).1)
      hz' hmidRoom h6 hnext (by omega) hd hb hhBelow hbBelow (by omega)
  exact ⟨out, copied, vc, ec, cost, y, hrun, hh', hb', hgraphReg, hgraph', hrep',
    hheader.symm ▸ hlsfs, by omega, hlo, by omega, by omega, hret.symm ▸ hz'',
    (fun a ha hd hb => (hkeep a ha).trans (hframe a ha hd hb)), hret.symm ▸ hfootOut,
    (fun r hr => (hforestRegs r hr).trans (hcopyRegs r hr)), by omega⟩

/-- Load the next Rebuild level's length pointer from the forest readout
(Definitions 5.6 and 5.7, pages 18–19). -/
@[expose] def rebuildReadForestLengths (init graphRead forestRead : ℕ) : Stmt :=
  rebuildReadForest init graphRead forestRead ;; loadShiftForestLengths

/-- The numerator table represents the next lengths when the denominator
represents the current lengths. The read leaves the copied graph intact. -/
theorem rebuildReadForestLengths_runs
    {w init graphRead forestRead prefixCost header fv fe h L precision : ℕ}
    {p : Program} {st mid : State} {ω : ℕ → Bool} {G H : MGraph} {forest : LSF}
    {ℓ : ℕ → ℝ}
    (hprefix : Runs w p ω (rebuildReadForest init graphRead forestRead) st .normal mid prefixCost)
    (hheader : mid.regs 9 = header) (hbound : header + 3 < 2 ^ w)
    (hforest : LSFAt mid.mem header fv fe h L precision G.E forest)
    (hlen : EdgeValuesAt mid.mem (mid.mem (mid.mem (header + 3) + 1)) h L precision G.E ℓ)
    (hsub : H.E ⊆ G.E) :
    ∃ out, Runs w p ω (rebuildReadForestLengths init graphRead forestRead)
        st .normal out (prefixCost + 7) ∧
      EdgeValuesAt out.mem (out.regs 7) h L precision H.E (coreLen forest ℓ) ∧
      out.mem = mid.mem ∧ (∀ r ≠ 7, out.regs r = mid.regs r) := by
  obtain ⟨out, hr, hptr, hmem, _, hregs⟩ :=
    loadForestNumerator_runs (ω := ω) hheader hbound
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, prefixCost, 6, hprefix, hr, by omega⟩),
    ?_, hmem, hregs⟩
  rw [hmem, hptr]
  exact coreLengthAt_of_stretch_numerator hsub hforest.2.2.2 hlen

/-- The first Rebuild level uses branch zero to compute the next lengths
and gradients from the inherited numbers (Algorithm 1, page 20). -/
theorem rebuildNextLevelNumbers (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i : ℕ) (hi : i < P.d)
    (Gnew : MGraph) (enc : ℕ) :
    let next := (algorithm1_rebuild T L P st i Gnew enc).1
    let forest := T.lsfs (next.scState i) 0
    next.toTreeChain.chainLen st.ℓ (i + 1) =
      coreLen forest (st.toTreeChain.chainLen st.ℓ i) ∧
    next.toTreeChain.chainGrad st.g (i + 1) =
      coreGrad Gnew forest (st.toTreeChain.chainGrad st.g i) := by
  dsimp only
  let next := (algorithm1_rebuild T L P st i Gnew enc).1
  have hgraph (j : ℕ) (hj : j ≤ i) : next.G j = if j = i then Gnew else st.G j := by
    simp only [next, algorithm1_rebuild, hi, dite_true]
    exact treeEdit_rebuildSuffix_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj
  have hbranch (j : ℕ) :
      next.bran j = if i ≤ j ∧ j < P.d then 0 else st.bran j := by
    simp only [next, algorithm1_rebuild, hi, dite_true]
    rw [rebuildSuffix_branch, Nat.add_sub_of_le hi.le]
  have hcore (j : ℕ) (hj : j < i) : next.scState j = st.scState j := by
    simp only [next, algorithm1_rebuild, hi, dite_true]
    exact rebuildSuffix_state_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ hj
  have hforest (j : ℕ) (hj : j < i) :
      next.toTreeChain.activeLSF j = st.toTreeChain.activeLSF j := by
    simp only [ChainState.toTreeChain, TreeChain.activeLSF, hj.trans hi, ite_true,
      hcore j hj, hbranch, not_le_of_gt hj, false_and, ite_false]
  have hactive : next.toTreeChain.activeLSF i = T.lsfs (next.scState i) 0 := by
    simp only [ChainState.toTreeChain, TreeChain.activeLSF, hi, ite_true,
      hbranch, le_rfl, true_and]
  have hprefix (j : ℕ) (hj : j < i) : next.toTreeChain.G j = st.toTreeChain.G j := by
    simpa only [ChainState.toTreeChain, ite_eq_right (Nat.ne_of_lt hj)] using hgraph j hj.le
  have hlen := chainLen_congr_lt st.ℓ i hprefix hforest
  have hgrad := chainGrad_congr_lt st.g i hprefix hforest
  constructor
  · rw [TreeChain.chainLen, hactive, hlen]
  · rw [TreeChain.chainGrad, hactive, hgrad]
    exact congrArg (fun G => coreGrad G _ _) (by simpa only [ChainState.toTreeChain, ite_true, ite_eq_left rfl] using hgraph i le_rfl)

/-- The rebuilt core supplies the copied next graph and its exact
model lengths when the selected forest stores the inherited denominator. -/
theorem rebuildCore_lengths_runs {w L M N vCap eCap init graph lengths gradient heap handleCell branchCell : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : ChainParams} {model : tool.State} {nextGraph : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ)
    (hmodel : model = tool.init P.k M N G
      (fun e => if e ∈ G.E then ℓ e else 0) (fun e => if e ∈ G.E then g e else 0))
    (hnextGraph : nextGraph = tool.S model 0)
    (nextLengths : ℕ → ℝ) (hnextLengths : nextLengths = coreLen (tool.lsfs model 0) ℓ)
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool G P.k M N vCap eCap costs allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient)
    (hh : st.regs 4 = heap)
    (hG : DynGraphAt st.mem graph vCap eCap G) (hm : G.m ≤ M) (hn : G.n ≤ N)
    (hgraph : graph + dynGraphSize vCap eCap ≤ heap)
    (hLenRoom : lengths + eCap * L ≤ heap) (hGradRoom : gradient + eCap * L ≤ heap)
    (hℓ : EdgeValuesAt st.mem lengths fmt.limbBits L fmt.precision G.E ℓ)
    (hgrad : EdgeValuesAt st.mem gradient fmt.limbBits L fmt.precision G.E g)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 5 [graph, lengths, gradient, heap] + 1 < 2 ^ w)
    (hkw : P.k < 2 ^ w)
    (hhCell : st.regs 51 = handleCell) (hbCell : st.regs 52 = branchCell)
    (hne : handleCell ≠ branchCell) (hhBelow : handleCell < heap) (hbBelow : branchCell < heap)
    (hw : 9 < 2 ^ w)
    (hcopyRoom : ∀ mid top vc ec cost,
      Runs w p ω (rebuildInstallReadGraph init (op 3)) st .normal mid cost →
      mid.regs 5 = top →
      DynGraphAt mid.mem (mid.regs 6) vc ec
        nextGraph →
      mid.regs 6 + dynGraphSize vc ec ≤ top ∧ top + dynGraphSize vc ec + 4 < 2 ^ w)
    (hgraphSep : ∀ addr, graph ≤ addr → addr < graph + dynGraphSize vCap eCap →
      addr ≠ handleCell ∧ addr ≠ branchCell)
    (hsub : nextGraph.E ⊆ G.E)
    (hden : ∀ mid c fv fe,
      Runs w p ω (rebuildReadForest init (op 3) (op 2)) st .normal mid c →
      LSFAt mid.mem (mid.regs 9) fv fe fmt.limbBits L fmt.precision G.E
        (tool.lsfs model 0) →
      EdgeValuesAt mid.mem (mid.mem (mid.mem (mid.regs 9 + 3) + 1))
        fmt.limbBits L fmt.precision G.E ℓ) :
    ∃ out copied vc ec cost y,
      Runs w p ω (rebuildReadForestLengths init (op 3) (op 2)) st .normal out cost ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧
      out.regs 6 = copied ∧ DynGraphAt out.mem copied vc ec nextGraph ∧
      R.rep heap model y out.mem ∧
      EdgeValuesAt out.mem (out.regs 7) fmt.limbBits L fmt.precision
        nextGraph.E nextLengths ∧
      copied + dynGraphSize vc ec ≤ out.regs 5 ∧
      heap ≤ copied ∧ heap ≤ out.regs 5 ∧ ZeroFrom out.mem (out.regs 5) ∧
      (∃ fv fe, LSFAt out.mem (out.regs 9) fv fe fmt.limbBits L fmt.precision G.E
        (tool.lsfs model 0)) ∧
      (∀ addr < heap, addr ≠ handleCell → addr ≠ branchCell → out.mem addr = st.mem addr) ∧
      (∀ addr, R.foot heap y addr → heap ≤ addr ∧ addr < out.regs 5) ∧
      DynGraphAt out.mem graph vCap eCap G ∧
      ((∀ e ∈ G.E, ∀ j < L,
        let addr := gradient + e * L + j
        addr ≠ handleCell ∧ addr ≠ branchCell) →
        EdgeValuesAt out.mem gradient fmt.limbBits L fmt.precision G.E g) ∧
      (∀ r, r = 8 ∨ 13 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi heap y out.mem ≤
        costs.factor M N * (M + 1) * P.k + 17 * dynGraphSize vc ec + 219 := by
  obtain ⟨mid, copied, vc, ec, c, y, hr, hh', hb', h6, hgraph', hrep, ⟨fv, fe, hlsf⟩, hcopyEnd, hcopiedLo, hheapLo, hhead, hz', hframe, hfoot, hforestRegs, hc'⟩ :=
    rebuildCore_forest_runs ℓ g hmodel hnextGraph himpl
      hg hl hc hh hG hm hn hgraph hLenRoom hGradRoom hℓ hgrad hpos hz
      hroom hkw hhCell hbCell hne hhBelow hbBelow hw hcopyRoom hgraphSep
  obtain ⟨out, hrun, hlen, hmem, hregs⟩ :=
    rebuildReadForestLengths_runs hr rfl hhead hlsf (hden mid c fv fe hr hlsf) hsub
  rw [← hnextLengths] at hlen
  refine ⟨out, copied, vc, ec, c + 7, y, hrun, hmem.symm ▸ hh', hmem.symm ▸ hb',
    (hregs 6 (by decide)).trans h6, hmem.symm ▸ hgraph', hmem.symm ▸ hrep,
    hlen, (hregs 5 (by decide)).symm ▸ hcopyEnd, hcopiedLo, (hregs 5 (by decide)).symm ▸ hheapLo, (hregs 5 (by decide)).symm ▸ (hmem.symm ▸ hz'),
    ⟨fv, fe, (hregs 9 (by decide)).symm ▸ (hmem.symm ▸ hlsf)⟩,
    hmem.symm ▸ hframe, (hregs 5 (by decide)).symm ▸ hfoot, ?_, ?_,
    (fun r hr => (hregs r (by omega)).trans (hforestRegs r hr)), by rw [hmem]; omega⟩
  · rw [hmem]
    exact hG.of_agree (fun addr hlo hhi => hframe addr (hhi.trans_le hgraph)
      (hgraphSep addr hlo hhi).1 (hgraphSep addr hlo hhi).2)
  · intro hsep
    rw [hmem]
    apply hgrad.congr
    intro e he j hj
    have heCap := hG.2.2.1 e he
    have hmul := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heCap)
    rw [Nat.succ_mul] at hmul
    exact hframe _ (by omega) (hsep e he j hj).1 (hsep e he j hj).2

end MinCostFlow.MinRatio
