module

public import MinCostFlow.MinRatio.ShiftGraph
public import MinCostFlow.MinRatio.DetectorRefresh
public import WordRAM.CopyWords
import MinCostFlow.MinRatio.PathCycleCoefficients
import WordRAM.Tactic
public import MinCostFlow.Chain.Algorithm1
import MinCostFlow.MinRatio.TreeEditFold
import MinCostFlow.MinRatio.TreeEditEndpoints
import MinCostFlow.MinRatio.RebuildGuard

/-!
# Shift prefix and model state

The restart readout in Algorithm 1 (page 20) already represents the shifted
core and the input graph of the next level. The subsequent suffix rebuild
leaves these fields as they are.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- Match the machine restart and loaded graph to the fields of Algorithm 1 Shift. -/
theorem shiftRestartLoadGraph_chain_runs {w L M N vCap eCap init addr handle heap i : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {last : LastLevelTool} {P : ChainParams} (chain : ChainState tool P)
    (hi : i < P.d)
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool initialGraph P.k M N vCap eCap costs allocation))
    (ha : st.regs 0 = addr) (hk : st.regs 1 = P.k)
    (hh : st.regs 3 = handle) (hheap : st.regs 4 = heap)
    (hb : st.mem addr = chain.bran i) (hj : chain.bran i < P.k) (hw : P.k < 2 ^ w)
    (hhandle : handle < 2 ^ w) (haheap : addr < heap) (hsep : ¬ R.foot handle x addr)
    (hrep : R.rep handle (chain.scState i) x st.mem)
    (hG : SparseCoreInput tool.toSparseCoreTool tool.restart P.k (chain.scState i) (chain.G i))
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 1 [handle, (chain.bran i + 1) % P.k, heap] + 1 < 2 ^ w) :
    let selected := (chain.bran i + 1) % P.k
    let next := (algorithm1_shift tool last P chain i).1
    ∃ (out : State) (ret ptr cost : ℕ) (y : R.τ),
      Runs w p ω (shiftRestartLoadGraph (op 1) (op 3)) st .normal out cost ∧
      out.regs 5 = ret ∧ out.regs 6 = out.mem ptr ∧ out.mem addr = selected ∧
      R.rep handle (next.scState i) y out.mem ∧
      (∃ vc ec, DynGraphAt out.mem (out.regs 6) vc ec (next.G (i + 1))) ∧
      cost + R.phi handle y out.mem ≤ costs.restartCost M N + R.phi handle x st.mem + 92 ∧
      SparseCoreInput tool.toSparseCoreTool tool.restart P.k (next.scState i) (next.G i) ∧
      (∀ a < heap, ¬ R.foot handle x a → a ≠ addr → out.mem a = st.mem a) ∧
      heap ≤ ret ∧ ret ≤ heap + allocation 1 [handle, selected, heap] + 1 ∧
      ZeroFrom out.mem ret ∧ (∀ a, R.foot handle y a → a < ret) ∧
      out.regs 2 = selected ∧ out.regs 3 = handle ∧ out.regs 4 = ptr ∧
      (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 5 → r ≠ 6 → out.regs r = st.regs r) ∧
      (∀ a < heap, R.foot handle y a → R.foot handle x a) := by
  dsimp only
  have hcore := algorithm1_shift_core_prefix tool last P chain i i hi (Nat.le_refl _)
  have hgraph := algorithm1_shift_graph_prefix tool last P chain i (i + 1) hi (Nat.le_refl _)
  have hcurrent := algorithm1_shift_graph_prefix tool last P chain i i hi (Nat.le_succ _)
  simp only [ite_true] at hcore hgraph
  simp only [Nat.ne_of_lt (Nat.lt_succ_self i), ite_false] at hcurrent
  rw [hcore, hgraph, hcurrent]
  exact shiftRestartLoadGraph_runs himpl ha hk hh hheap hb hj hw hhandle haheap hsep
    hrep hG hfoot hz hroom

/-- The first rebuilt level after Shift (page 20) uses the old numerical
data through the shifted level and applies the newly selected forest to it. -/
theorem shiftNextLevelNumbers (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i : ℕ) (hi : i < P.d) :
    let next := (algorithm1_shift T L P st i).1
    let branch := (st.bran i + 1) % P.k
    let forest := T.lsfs (T.restart (st.scState i) branch) branch
    next.toTreeChain.chainLen st.ℓ (i + 1) =
      coreLen forest (st.toTreeChain.chainLen st.ℓ i) ∧
    next.toTreeChain.chainGrad st.g (i + 1) =
      coreGrad (st.G i) forest (st.toTreeChain.chainGrad st.g i) := by
  dsimp only
  let next := (algorithm1_shift T L P st i).1
  have hgraph (j : ℕ) (hj : j ≤ i) : next.G j = st.G j := by
    simpa [show j ≠ i + 1 by omega] using
      algorithm1_shift_graph_prefix T L P st i j hi (hj.trans (Nat.le_succ _))
  have hforest (j : ℕ) (hj : j < i) :
      next.toTreeChain.activeLSF j = st.toTreeChain.activeLSF j := by
    have hj' := hj.trans hi
    simp only [TreeChain.activeLSF, ChainState.toTreeChain, hj', ite_true]
    rw [algorithm1_shift_core_prefix T L P st i j hi hj.le,
      algorithm1_shift_branch_prefix T L P st i j hi hj.le]
    simp [Nat.ne_of_lt hj]
  have hactive : next.toTreeChain.activeLSF i =
      T.lsfs (T.restart (st.scState i) ((st.bran i + 1) % P.k)) ((st.bran i + 1) % P.k) := by
    simp only [TreeChain.activeLSF, ChainState.toTreeChain, hi, ite_true]
    rw [algorithm1_shift_core_prefix T L P st i i hi le_rfl,
      algorithm1_shift_branch_prefix T L P st i i hi le_rfl]
    simp
  have hlen := chainLen_congr_lt (C₁ := next.toTreeChain) (C₂ := st.toTreeChain) st.ℓ i
    (fun j hj => hgraph j hj.le) hforest
  have hgrad := chainGrad_congr_lt (C₁ := next.toTreeChain) (C₂ := st.toTreeChain) st.g i
    (fun j hj => hgraph j hj.le) hforest
  constructor
  · rw [TreeChain.chainLen, hactive, hlen]
  · rw [TreeChain.chainGrad, hactive, hgrad]
    exact congrArg (fun G => coreGrad G _ _) (hgraph i le_rfl)


/-- If Shift has a deeper sparse-core level, its first initializer uses
the shifted chain's graph, lengths, and gradients at that level. Subsequent
rebuilds preserve its initialized state (Algorithm 1, page 20). -/
theorem shiftNextCoreBuild_eq (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i : ℕ) (hi : i + 1 < P.d) :
    let next := (algorithm1_shift T L P st i).1
    next.scState (i + 1) = T.init P.k (st.lvlM (i + 1)) st.N₀ (next.G (i + 1))
      (next.toTreeChain.chainLen st.ℓ (i + 1))
      (next.toTreeChain.chainGrad st.g (i + 1)) := by
  have hlt : i < P.d := by omega
  have hrem : P.d - (i + 1) = (P.d - (i + 2)) + 1 := by omega
  dsimp only
  let branch := (st.bran i + 1) % P.k
  let core := T.restart (st.scState i) branch
  let graphs := fun j => if j = i + 1 then T.S core branch else st.G j
  let states := fun j => if j = i then core else st.scState j
  let branches := fun j => if j = i then branch else st.bran j
  let initialChain : TreeChain :=
    { d := P.d, k := P.k, G := graphs, lsfs := fun j => T.lsfs (states j), bran := branches,
      S := fun j => T.S (states j), emb := fun j => T.emb (states j), lastK := 1,
      lastLSFs := fun _ => ⟨graphs (i + 1), ⟨graphs (i + 1), ∅⟩, fun _ => 1⟩, lastBran := 0 }
  let next := (algorithm1_shift T L P st i).1
  change next.scState (i + 1) = T.init P.k (st.lvlM (i + 1)) st.N₀ (next.G (i + 1))
    (next.toTreeChain.chainLen st.ℓ (i + 1)) (next.toTreeChain.chainGrad st.g (i + 1))
  have hbuild : next.scState (i + 1) = T.init P.k (st.lvlM (i + 1)) st.N₀ (graphs (i + 1))
      (initialChain.chainLen st.ℓ (i + 1)) (initialChain.chainGrad st.g (i + 1)) := by
    unfold next algorithm1_shift
    rw [dite_eq_left hlt, hrem]
    simp only [rebuildSuffix]
    rw [rebuildSuffix_state_prefix T L P _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Nat.lt_succ_self _)]
    simp only [initialChain, graphs, states, branches, core, branch, ite_true, ite_eq_left rfl]
  have hG (j : ℕ) (hj : j ≤ i + 1) : next.G j = graphs j :=
    algorithm1_shift_graph_prefix T L P st i j hlt hj
  have hLSF (j : ℕ) (hj : j < i + 1) : next.toTreeChain.activeLSF j = initialChain.activeLSF j := by
    have hjd : j < P.d := by omega
    simp only [TreeChain.activeLSF, ChainState.toTreeChain, initialChain, hjd, ite_true]
    rw [algorithm1_shift_core_prefix T L P st i j hlt (by omega),
      algorithm1_shift_branch_prefix T L P st i j hlt (by omega)]
  rw [hbuild, hG _ le_rfl,
    chainLen_congr_lt st.ℓ (i + 1) (fun j hj => (hG j hj.le).symm)
      (fun j hj => (hLSF j hj).symm),
    chainGrad_congr_lt st.g (i + 1) (fun j hj => (hG j hj.le).symm)
      (fun j hj => (hLSF j hj).symm)]

/-- When the following level is terminal, Algorithm 1 Shift (page 20)
builds its forest collection immediately from the new graph and lengths. -/
theorem shiftTerminalBuild_eq (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i : ℕ) (hi : i + 1 = P.d) :
    let next := (algorithm1_shift T L P st i).1
    (next.lastK, next.lastLSFs) =
      L.build (next.G P.d) (next.toTreeChain.chainLen st.ℓ P.d) := by
  have hlt : i < P.d := by omega
  have hrem : P.d - (i + 1) = 0 := by omega
  dsimp only
  let branch := (st.bran i + 1) % P.k
  let core := T.restart (st.scState i) branch
  let graphs := fun j => if j = i + 1 then T.S core branch else st.G j
  let states := fun j => if j = i then core else st.scState j
  let branches := fun j => if j = i then branch else st.bran j
  let initialChain : TreeChain :=
    { d := P.d, k := P.k, G := graphs, lsfs := fun j => T.lsfs (states j), bran := branches,
      S := fun j => T.S (states j), emb := fun j => T.emb (states j), lastK := 1,
      lastLSFs := fun _ => ⟨graphs (i + 1), ⟨graphs (i + 1), ∅⟩, fun _ => 1⟩, lastBran := 0 }
  let next := (algorithm1_shift T L P st i).1
  change (next.lastK, next.lastLSFs) = L.build (next.G P.d) (next.toTreeChain.chainLen st.ℓ P.d)
  have hbuild : (next.lastK, next.lastLSFs) =
      L.build (graphs (i + 1)) (initialChain.chainLen st.ℓ (i + 1)) := by
    unfold next algorithm1_shift
    rw [dite_eq_left hlt, hrem]
    rfl
  rw [hbuild]
  have hG : ∀ j, next.G j = graphs j := by
    intro j
    simp only [next, algorithm1_shift, hlt, dite_true, hrem, rebuildSuffix]
    rfl
  have hLSF : ∀ j < P.d, next.toTreeChain.activeLSF j = initialChain.activeLSF j := by
    intro j hj
    simp only [next, algorithm1_shift, hlt, dite_true, hrem, rebuildSuffix,
      ChainState.toTreeChain, TreeChain.activeLSF, initialChain, hj, ite_true]
    rfl
  rw [hi, hG, chainLen_congr_lt st.ℓ P.d (fun j _ => (hG j).symm)
    (fun j hj => (hLSF j hj).symm)]

/-- The first deeper graph after a Shift uses the stretch numerator
as its length table when the denominator represents the current lengths
(Definitions 5.6 and 5.7, pages 18–19). -/
theorem shiftNextLevelLengthAt {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (st : ChainState T P) (i : ℕ) (hi : i < P.d)
    {mem : ℕ → ℕ} {ptr limbBits limbs precision : ℕ}
    {branch : ℕ}
    (hbranch : branch = (st.bran i + 1) % P.k)
    (hsub : (T.S (T.restart (st.scState i) branch) branch).E ⊆ (st.G i).E)
    (hst : StretchValuesAt mem ptr limbBits limbs precision (st.G i).E
      (T.lsfs (T.restart (st.scState i) branch) branch).wstr)
    (hlen : EdgeValuesAt mem (mem (ptr + 1)) limbBits limbs precision
      (st.G i).E (st.toTreeChain.chainLen st.ℓ i)) :
    let next := (algorithm1_shift T L P st i).1
    EdgeValuesAt mem (mem ptr) limbBits limbs precision (next.G (i + 1)).E
      (next.toTreeChain.chainLen st.ℓ (i + 1)) := by
  subst branch
  dsimp only
  rw [(shiftNextLevelNumbers T L P st i hi).1]
  have hgraph := algorithm1_shift_graph_prefix T L P st i (i + 1) hi (Nat.le_refl _)
  simp only [ite_true] at hgraph
  rw [hgraph]
  exact coreLengthAt_of_stretch_numerator hsub hst hlen

/-- Supply the length pointer to the next sparse-core initialization.
Register 9 holds the stretch descriptor and register 7 receives its numerator. -/
@[expose] def loadShiftLengths : Stmt :=
  .assign 7 (.load (.reg 9))

theorem loadShiftLengths_noRand : loadShiftLengths.NoRand := by
  simp [loadShiftLengths, Stmt.NoRand]

/-- The length handoff uses a single load, preserves the other inputs,
and represents the next graph's lengths in three machine steps. -/
theorem loadShiftLengths_runs {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : ℕ) (hi : i < P.d)
    {w ptr limbBits limbs precision branch : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hptr : st.regs 9 = ptr) (hbranch : branch = (chain.bran i + 1) % P.k)
    (hsub : (T.S (T.restart (chain.scState i) branch) branch).E ⊆ (chain.G i).E)
    (hst : StretchValuesAt st.mem ptr limbBits limbs precision (chain.G i).E
      (T.lsfs (T.restart (chain.scState i) branch) branch).wstr)
    (hlen : EdgeValuesAt st.mem (st.mem (ptr + 1)) limbBits limbs precision
      (chain.G i).E (chain.toTreeChain.chainLen chain.ℓ i)) :
    let next := (algorithm1_shift T L P chain i).1
    ∃ out, Runs w p ω loadShiftLengths st .normal out 3 ∧
      EdgeValuesAt out.mem (out.regs 7) limbBits limbs precision
        (next.G (i + 1)).E (next.toTreeChain.chainLen chain.ℓ (i + 1)) ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧ (∀ r ≠ 7, out.regs r = st.regs r) := by
  let out := { st with regs := Function.update st.regs 7 (st.mem ptr) }
  have hr : Runs w p ω loadShiftLengths st .normal out 3 :=
    runs_assign_iff.mpr ⟨st.mem ptr, by simp [Expr.eval, hptr], rfl, rfl, rfl⟩
  refine ⟨out, hr, ?_, rfl, rfl, ?_⟩
  · simpa only [out, Function.update_self] using
      shiftNextLevelLengthAt (L := L) chain i hi hbranch hsub hst hlen
  · intro r hr
    exact Function.update_of_ne hr _ _

/-- Load the numerator pointer directly from the four-word forest
header returned by the sparse-core tool. Register 9 holds that header. -/
@[expose] def loadShiftForestLengths : Stmt :=
  .assign 7 (.load (.load (.bin .add (.reg 9) (.const 3))))

theorem loadShiftForestLengths_noRand : loadShiftForestLengths.NoRand := by
  simp [loadShiftForestLengths, Stmt.NoRand]

/-- Read the numerator pointer of a selected forest's stretch descriptor.
The copy of the graph, the descriptor, and all other registers are unchanged. -/
theorem loadForestNumerator_runs {w header : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hheader : st.regs 9 = header) (hbound : header + 3 < 2 ^ w) :
    ∃ out, Runs w p ω loadShiftForestLengths st .normal out 6 ∧
      out.regs 7 = st.mem (st.mem (header + 3)) ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧ (∀ r ≠ 7, out.regs r = st.regs r) := by
  let ptr := st.mem (st.mem (header + 3))
  let out := { st with regs := Function.update st.regs 7 ptr }
  have hthree : 3 < 2 ^ w := by omega
  have hr : Runs w p ω loadShiftForestLengths st .normal out 6 :=
    runs_assign_iff.mpr ⟨ptr, by simp [Expr.eval, BinOp.eval, ptr, hheader, hthree, hbound],
      rfl, rfl, rfl⟩
  exact ⟨out, hr, by simp [out, ptr], rfl, rfl, fun r hr => Function.update_of_ne hr _ _⟩

/-- The restarted forest readout supplies the next level's length pointer
in six steps when its denominator represents the current lengths. -/
theorem loadShiftForestLengths_runs {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : ℕ) (hi : i < P.d)
    {w header vc ec limbBits limbs precision branch : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hheader : st.regs 9 = header) (hbound : header + 3 < 2 ^ w)
    (hbranch : branch = (chain.bran i + 1) % P.k)
    (hsub : (T.S (T.restart (chain.scState i) branch) branch).E ⊆ (chain.G i).E)
    (hforest : LSFAt st.mem header vc ec limbBits limbs precision (chain.G i).E
      (T.lsfs (T.restart (chain.scState i) branch) branch))
    (hlen : EdgeValuesAt st.mem (st.mem (st.mem (header + 3) + 1)) limbBits limbs precision
      (chain.G i).E (chain.toTreeChain.chainLen chain.ℓ i)) :
    let next := (algorithm1_shift T L P chain i).1
    ∃ out, Runs w p ω loadShiftForestLengths st .normal out 6 ∧
      EdgeValuesAt out.mem (out.regs 7) limbBits limbs precision
        (next.G (i + 1)).E (next.toTreeChain.chainLen chain.ℓ (i + 1)) ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧ (∀ r ≠ 7, out.regs r = st.regs r) := by
  obtain ⟨out, hr, hptr, hmem, hpos, hregs⟩ :=
    loadForestNumerator_runs (p := p) (ω := ω) hheader hbound
  refine ⟨out, hr, ?_, hmem, hpos, hregs⟩
  simpa only [hmem, hptr] using
    shiftNextLevelLengthAt (L := L) chain i hi hbranch hsub hforest.2.2.2 hlen

/-- Read the selected forest and load its numerator for the next level. -/
@[expose] def shiftForestLengths (entry : ℕ) : Stmt :=
  shiftForestRead entry ;; loadShiftForestLengths

/-- Connect the forest call to the next level's length input. The denominator
must encode the current lengths in the returned layout. -/
theorem shiftForestLengths_runs {w L M N vCap eCap init branch handle graph heap i : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {last : LastLevelTool} {P : ChainParams} (chain : ChainState tool P) (hi : i < P.d)
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool initialGraph P.k M N vCap eCap costs allocation))
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle) (hg : st.regs 7 = graph)
    (hp : st.regs 5 = heap) (hbranch : branch = (chain.bran i + 1) % P.k) (hw : P.k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hrep : R.rep handle (tool.restart (chain.scState i) branch) x st.mem)
    (hG : SparseCoreGraphAt tool.toSparseCoreTool tool.restart P.k
      (tool.restart (chain.scState i) branch) st.mem graph vCap eCap (chain.G i))
    (hgraphRoom : graph + dynGraphSize vCap eCap ≤ heap)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 4 < 2 ^ w)
    (hsub : (tool.S (tool.restart (chain.scState i) branch) branch).E ⊆ (chain.G i).E)
    (hden : ∀ (mid : State) readCost fv fe,
      Runs w p ω (shiftForestRead (op 2)) st .normal mid readCost →
      LSFAt mid.mem heap fv fe fmt.limbBits L fmt.precision (chain.G i).E
        (tool.lsfs (tool.restart (chain.scState i) branch) branch) →
      EdgeValuesAt mid.mem (mid.mem (mid.mem (heap + 3) + 1)) fmt.limbBits L fmt.precision
        (chain.G i).E (chain.toTreeChain.chainLen chain.ℓ i)) :
    let core := tool.restart (chain.scState i) branch
    let next := (algorithm1_shift tool last P chain i).1
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (shiftForestLengths (op 2)) st .normal out cost ∧ out.regs 5 = ret ∧
      R.rep handle core y out.mem ∧
      EdgeValuesAt out.mem (out.regs 7) fmt.limbBits L fmt.precision
        (next.G (i + 1)).E (next.toTreeChain.chainLen chain.ℓ (i + 1)) ∧
      R.Respects (R.foot handle x) heap 4 st.mem ret handle y out.mem ∧
      (∃ fv fe, LSFAt out.mem (out.regs 9) fv fe fmt.limbBits L fmt.precision
        (chain.G i).E (tool.lsfs (tool.restart (chain.scState i) branch) branch)) ∧
      cost + R.phi handle y out.mem ≤ 79 + R.phi handle x st.mem ∧
      (∀ r, r ≠ 5 → r ≠ 7 → r ≠ 9 → out.regs r = st.regs r) ∧
      (∀ vc ec, DynGraphAt st.mem (st.regs 6) vc ec (next.G (i + 1)) →
        st.regs 6 + dynGraphSize vc ec ≤ heap →
        (∀ addr, st.regs 6 ≤ addr → addr < st.regs 6 + dynGraphSize vc ec →
          ¬ R.foot handle x addr) →
        DynGraphAt out.mem (out.regs 6) vc ec (next.G (i + 1))) := by
  have hj : branch < P.k := by rw [hbranch]; exact Nat.mod_lt _ P.hk
  obtain ⟨mid, ret, c, y, hr, hret, hheader, hrep', ⟨fv, fe, hforest⟩, hframe, hc, hsaved⟩ :=
    shiftForestRead_runs (ω := ω) himpl hb hh hg hp hj hw hhw hrep hG hgraphRoom hfoot hz hroom
  obtain ⟨out, hl, hlen, hm, _, hregs⟩ :=
    loadShiftForestLengths_runs (L := last) (w := w) (ω := ω) chain i hi hheader
      (by omega) hbranch hsub hforest (hden mid c fv fe hr hforest)
  refine ⟨out, ret, c + 7, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, c, 6, hr, hl, by omega⟩),
    (hregs 5 (by decide)).trans hret, hm.symm ▸ hrep', hlen, hm.symm ▸ hframe, ?_, ?_, ?_, ?_⟩
  · exact ⟨fv, fe, ((hregs 9 (by decide)).trans hheader).symm ▸ (hm.symm ▸ hforest)⟩
  · rw [hm]
    omega
  · intro r hr₅ hr₇ hr₉
    exact (hregs r hr₇).trans (hsaved r hr₅ hr₉)

  · intro vc ec hgraph hroom hsep
    rw [(hregs 6 (by decide)).trans (hsaved 6 (by decide) (by decide)), hm]
    apply hgraph.of_agree
    intro addr hlo hhi
    exact hframe.2.2.2.1 addr (hhi.trans_le hroom) (hsep addr hlo hhi)

/-- After copying the sparsifier to caller memory, the forest call and
length load preserve that graph and prepare both inputs for the suffix. -/
theorem shiftCopiedGraphForestLengths_runs {w L M N vCap eCap init branch handle graph heap i : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {last : LastLevelTool} {P : ChainParams} (chain : ChainState tool P) (hi : i < P.d)
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool initialGraph P.k M N vCap eCap costs allocation))
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle) (hg : st.regs 7 = graph)
    (hp : st.regs 5 = heap) (hbranch : branch = (chain.bran i + 1) % P.k) (hw : P.k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hrep : R.rep handle (tool.restart (chain.scState i) branch) x st.mem)
    (hG : SparseCoreGraphAt tool.toSparseCoreTool tool.restart P.k
      (tool.restart (chain.scState i) branch) st.mem graph vCap eCap (chain.G i))
    (hgraphRoom : graph + dynGraphSize vCap eCap ≤ heap)
    (hz : ZeroFrom st.mem heap)
    (hroom : heap + 4 < 2 ^ w)
    (hsub : (tool.S (tool.restart (chain.scState i) branch) branch).E ⊆ (chain.G i).E)
    (hden : ∀ (mid : State) readCost fv fe,
      Runs w p ω (shiftForestRead (op 2)) st .normal mid readCost →
      LSFAt mid.mem heap fv fe fmt.limbBits L fmt.precision (chain.G i).E
        (tool.lsfs (tool.restart (chain.scState i) branch) branch) →
      EdgeValuesAt mid.mem (mid.mem (mid.mem (heap + 3) + 1)) fmt.limbBits L fmt.precision
        (chain.G i).E (chain.toTreeChain.chainLen chain.ℓ i))
    {copied vc ec : ℕ}
    (hptr : st.regs 6 = copied)
    (hcopy : DynGraphAt st.mem copied vc ec ((algorithm1_shift tool last P chain i).1.G (i + 1)))
    (hafter : copied + dynGraphSize vc ec ≤ heap)
    (hbefore : ∀ a, R.foot handle x a → a < copied) :
    let next := (algorithm1_shift tool last P chain i).1
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (shiftForestLengths (op 2)) st .normal out cost ∧
      out.regs 5 = ret ∧ out.regs 6 = copied ∧
      DynGraphAt out.mem copied vc ec (next.G (i + 1)) ∧
      EdgeValuesAt out.mem (out.regs 7) fmt.limbBits L fmt.precision
        (next.G (i + 1)).E (next.toTreeChain.chainLen chain.ℓ (i + 1)) ∧
      R.rep handle (tool.restart (chain.scState i) branch) y out.mem ∧
      ZeroFrom out.mem ret ∧ (∀ a, R.foot handle y a → a < ret) ∧
      (∃ fv fe, LSFAt out.mem (out.regs 9) fv fe fmt.limbBits L fmt.precision
        (chain.G i).E (tool.lsfs (tool.restart (chain.scState i) branch) branch)) ∧
      cost + R.phi handle y out.mem ≤ 79 + R.phi handle x st.mem ∧
      (∀ a, a < heap → ¬ R.foot handle x a → out.mem a = st.mem a) ∧
      heap ≤ ret ∧
      (∀ r, r ≠ 5 → r ≠ 7 → r ≠ 9 → out.regs r = st.regs r) := by
  have hfoot : ∀ a, R.foot handle x a → a < heap :=
    fun a ha => (hbefore a ha).trans_le ((Nat.le_add_right _ _).trans hafter)
  obtain ⟨out, ret, c, y, hr, hret, hs, hl, hframe, hforest, hc, hregs, hg'⟩ :=
    shiftForestLengths_runs (last := last) (ω := ω) chain hi himpl hb hh hg hp hbranch hw hhw
      hrep hG hgraphRoom hfoot hz hroom hsub hden
  have hgraphPtr := (hregs 6 (by decide) (by decide) (by decide)).trans hptr
  have hgraph := hg' vc ec (hptr.symm ▸ hcopy) (by simpa only [hptr] using hafter)
    (fun a ha _ hf => Nat.not_lt_of_ge (hptr ▸ ha) (hbefore a hf))
  refine ⟨out, ret, c, y, hr, hret, hgraphPtr, hgraphPtr ▸ hgraph, hl, hs,
    hframe.2.2.1, ?_, hforest, hc, hframe.2.2.2.1, hframe.1, hregs⟩
  intro a ha
  rcases hframe.2.2.2.2 a ha with ho | ⟨_, hn⟩
  · exact (hfoot a ho).trans_le hframe.1
  · exact hn

/-- Restart the chosen branch, copy the deeper graph, and load its lengths
before the suffix rebuild in Algorithm 1 (page 20). -/
@[expose] def shiftRestartGraphAndLengths (restart read forest : ℕ) : Stmt :=
  shiftRestartCopyGraph restart read ;; shiftForestLengths forest

/-- The next graph and its lengths are prepared for the suffix. The word
bounds and forest denominator condition are obligations of this composition. -/
theorem shiftRestartGraphAndLengths_runs {w L M N vCap eCap init addr handle heap graph i : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {last : LastLevelTool} {P : ChainParams} (chain : ChainState tool P) (hi : i < P.d)
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool initialGraph P.k M N vCap eCap costs allocation))
    (ha : st.regs 0 = addr) (hk : st.regs 1 = P.k)
    (hh : st.regs 3 = handle) (hheap : st.regs 4 = heap)
    (hb : st.mem addr = chain.bran i) (hj : chain.bran i < P.k) (hw : P.k < 2 ^ w)
    (hhandle : handle < 2 ^ w) (haheap : addr < heap) (hsep : ¬ R.foot handle x addr)
    (hrep : R.rep handle (chain.scState i) x st.mem)
    (hG : DynGraphAt st.mem graph vCap eCap (chain.G i))
    (hinput : SparseCoreInput tool.toSparseCoreTool tool.restart P.k (chain.scState i) (chain.G i))
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 1 [handle, (chain.bran i + 1) % P.k, heap] + 1 < 2 ^ w)
    (hword : 9 < 2 ^ w)
    (hgraph : st.regs 7 = graph) (hgHeap : graph + dynGraphSize vCap eCap ≤ heap)
    (hgSep : ∀ a, graph ≤ a → a < graph + dynGraphSize vCap eCap →
      ¬ R.foot handle x a ∧ a ≠ addr)
    (hcopyRoom : ∀ (mid : State) ret vc ec prefixCost,
      let branch := (chain.bran i + 1) % P.k
      Runs w p ω (shiftRestartLoadGraph (op 1) (op 3)) st .normal mid prefixCost →
      mid.regs 5 = ret →
      DynGraphAt mid.mem (mid.regs 6) vc ec (tool.S (tool.restart (chain.scState i) branch) branch) →
      ret ≤ heap + allocation 1 [handle, branch, heap] + 1 →
      mid.regs 6 + dynGraphSize vc ec ≤ ret ∧ ret + dynGraphSize vc ec + 4 < 2 ^ w)
    (hsub : let branch := (chain.bran i + 1) % P.k
      (tool.S (tool.restart (chain.scState i) branch) branch).E ⊆ (chain.G i).E)
    (hden : ∀ (mid after : State) prefixCost readCost fv fe,
      let branch := (chain.bran i + 1) % P.k
      Runs w p ω (shiftRestartCopyGraph (op 1) (op 3)) st .normal mid prefixCost →
      Runs w p ω (shiftForestRead (op 2)) mid .normal after readCost →
      LSFAt after.mem (mid.regs 5) fv fe fmt.limbBits L fmt.precision (chain.G i).E
        (tool.lsfs (tool.restart (chain.scState i) branch) branch) →
      EdgeValuesAt after.mem (after.mem (after.mem (mid.regs 5 + 3) + 1))
        fmt.limbBits L fmt.precision (chain.G i).E (chain.toTreeChain.chainLen chain.ℓ i)) :
    let next := (algorithm1_shift tool last P chain i).1
    ∃ (out : State) (vc ec cost : ℕ) (y : R.τ),
      Runs w p ω (shiftRestartGraphAndLengths (op 1) (op 3) (op 2)) st .normal out cost ∧
      DynGraphAt out.mem (out.regs 6) vc ec (next.G (i + 1)) ∧
      EdgeValuesAt out.mem (out.regs 7) fmt.limbBits L fmt.precision
        (next.G (i + 1)).E (next.toTreeChain.chainLen chain.ℓ (i + 1)) ∧
      R.rep handle (next.scState i) y out.mem ∧ ZeroFrom out.mem (out.regs 5) ∧
      (∀ a, R.foot handle y a → a < out.regs 5) ∧
      (∃ fv fe, let branch := (chain.bran i + 1) % P.k
        LSFAt out.mem (out.regs 9) fv fe fmt.limbBits L fmt.precision
        (chain.G i).E (tool.lsfs (tool.restart (chain.scState i) branch) branch)) ∧
      cost + R.phi handle y out.mem ≤ costs.restartCost M N + R.phi handle x st.mem +
        17 * dynGraphSize vc ec + 216 ∧
      (∀ a < heap, ¬ R.foot handle x a → a ≠ addr → out.mem a = st.mem a) ∧
      heap ≤ out.regs 5 ∧
      (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 9 →
        r ≠ 10 → r ≠ 11 → r ≠ 12 → out.regs r = st.regs r) ∧
      DynGraphAt out.mem graph vCap eCap (chain.G i) ∧
      (∀ gradients g,
        EdgeValuesAt st.mem gradients fmt.limbBits L fmt.precision (chain.G i).E g →
        (∀ e ∈ (chain.G i).E, ∀ j < L,
          let a := gradients + e * L + j
          a < heap ∧ ¬ R.foot handle x a ∧ a ≠ addr) →
        EdgeValuesAt out.mem gradients fmt.limbBits L fmt.precision (chain.G i).E g) := by
  dsimp only
  obtain ⟨mid, ret, vc, ec, c, y, hr, hptr, hheap', hretLo, hforestRoom, hb', hh', _, hre, hg, hin,
    hz', hfoot', hframe, hc, hregs, hfootBelow⟩ :=
    shiftRestartCopyGraph_runs (reserve := 4) (ω := ω) himpl ha hk hh hheap hb hj hw hhandle haheap hsep
      hrep hinput hfoot hz hroom hword
      hcopyRoom
  have hcore := algorithm1_shift_core_prefix tool last P chain i i hi (Nat.le_refl _)
  have hnext := algorithm1_shift_graph_prefix tool last P chain i (i + 1) hi (Nat.le_refl _)
  simp only [ite_true] at hcore hnext
  have hg' : DynGraphAt mid.mem graph vCap eCap (chain.G i) :=
    hG.of_agree (fun a hlo hhi => hframe a (hhi.trans_le hgHeap)
      (hgSep a hlo hhi).1 (hgSep a hlo hhi).2)
  obtain ⟨out, newHeap, d, z, hread, hout, hgraphOut, hgraphNext, hlen, hstate,
      hzero, hfootOut, hforest, hd, hframeOut, hheapOut, hregsOut⟩ :=
    shiftCopiedGraphForestLengths_runs (last := last) (ω := ω) chain hi himpl
      hb' hh' ((hregs 7 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hgraph) rfl rfl hw hhandle hre ⟨hin, hg'⟩
      (by omega) hz' hforestRoom hsub
      (fun after rc fv fe hrun hf => hden mid after c rc fv fe hr hrun hf)
      hptr (hnext ▸ hg) (by omega) hfoot'
  have hpreserved (a : ℕ) (ha : a < heap) (hsepOld : ¬ R.foot handle x a)
      (hne : a ≠ addr) : out.mem a = st.mem a :=
    (hframeOut a (by omega) (fun hf => hsepOld (hfootBelow a ha hf))).trans
      (hframe a ha hsepOld hne)
  refine ⟨out, vc, ec, c + d + 1, z, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hread, rfl⟩),
    hgraphOut.symm ▸ hgraphNext, hlen, hcore ▸ hstate, hout.symm ▸ hzero, ?_, hforest, by omega, hpreserved, by omega, ?_, ?_, ?_⟩
  · simpa only [hout] using hfootOut
  · intro r hr₂ hr₄ hr₅ hr₆ hr₇ hr₉ hr₁₀ hr₁₁ hr₁₂
    exact (hregsOut r hr₅ hr₇ hr₉).trans (hregs r hr₂ hr₄ hr₅ hr₆ hr₁₀ hr₁₁ hr₁₂)
  · exact hG.of_agree (fun a hlo hhi => hpreserved a (hhi.trans_le hgHeap)
      (hgSep a hlo hhi).1 (hgSep a hlo hhi).2)
  · intro gradients g hvalues hseparated e he
    obtain ⟨hvalid, hvalue⟩ := hvalues e he
    have hagree (j : ℕ) (hj : j < L) :=
      hpreserved _ (hseparated e he j hj).1 (hseparated e he j hj).2.1 (hseparated e he j hj).2.2
    exact ⟨fun j hj => (hagree j hj) ▸ hvalid j hj,
      by rw [Num.fixVal, Num.intVal_congr hagree]; exact hvalue⟩

end MinCostFlow.MinRatio
