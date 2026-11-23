module

public import MinCostFlow.MinRatio.RebuildCoreStep
public import MinCostFlow.MinRatio.ShiftDeeperLevel
public import MinCostFlow.MinRatio.InitCertifiedEntry
public import MinCostFlow.Chain.SparseCoreRestartInitAgree
import MinCostFlow.MinRatio.RebuildModelSuffix

/-!
# Exact core-state agreement for Init, Rebuild, and Shift

`Chain.SparseCoreRestartInitAgree` proves that `sparseCoreRestartTool.init` depends
only on live edge lengths and ignores gradients and off-edge values. This file uses
those equalities to remove off-edge support assumptions from the sparse-core machine
steps of Algorithm 1 (page 20), and composes one complete concrete sparse-core Init
iteration from the loop head to the next level.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- Graph and gradient input tables avoid the two level descriptor arrays
`[tableBase, tableBase + 2 * (d + 1))` during Init: at level zero both lie
below `tableBase`, and at every deeper level both are freshly allocated at or
above `tableBase + 2 * (d + 1)`. -/
@[expose] def InitLevelTablesSeparated
    (tableBase d graph vc ec gradient limbs : ℕ) : Prop :=
  (graph + dynGraphSize vc ec ≤ tableBase ∧ gradient + ec * limbs ≤ tableBase) ∨
    (tableBase + (d + 1) + (d + 1) ≤ graph ∧ tableBase + (d + 1) + (d + 1) ≤ gradient)

theorem InitLevelTablesSeparated.graphSep
    {tableBase d graph vc ec gradient limbs i : ℕ}
    (hsep : InitLevelTablesSeparated tableBase d graph vc ec gradient limbs) (hi : i ≤ d) :
    ∀ a, graph ≤ a → a < graph + dynGraphSize vc ec →
      a ≠ tableBase + i ∧ a ≠ tableBase + (d + 1) + i := by
  intro a hlo hhi
  rcases hsep with ⟨hg, _⟩ | ⟨hg, _⟩ <;> exact ⟨by omega, by omega⟩

theorem InitLevelTablesSeparated.gradSep
    {tableBase d graph vc ec gradient limbs i : ℕ}
    (hsep : InitLevelTablesSeparated tableBase d graph vc ec gradient limbs) (hi : i ≤ d) :
    ∀ e < ec, ∀ j < limbs,
      gradient + e * limbs + j ≠ tableBase + i ∧
        gradient + e * limbs + j ≠ tableBase + (d + 1) + i := by
  intro e he j hj
  have hmul : (e + 1) * limbs ≤ ec * limbs := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt he)
  rw [Nat.succ_mul] at hmul
  rcases hsep with ⟨_, hg⟩ | ⟨_, hg⟩ <;> exact ⟨by omega, by omega⟩

/-- Periodic Rebuild readout for `sparseCoreRestartTool`, discharging the
off-edge core-state agreement unconditionally via
`algorithm1_rebuild_coreAt_eq_zeroExtension`. -/
theorem RebuildSuffixAt.rebuildReadCoreLengths_concrete_runs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    {P : ChainParams} {tool : LastLevelTool}
    {R : DSRep (sparseCoreRestartTool oracle C depth sparsify).State}
    (chain : ChainState (sparseCoreRestartTool oracle C depth sparsify) P)
    (Gnew : MGraph) (enc : ℕ)
    {w init handleBase branchBase first level vc ec M N limbs : ℕ} {st : State}
    {fmt : Num.Format w} {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {p : Program} {ω : ℕ → Bool} {op : ℕ → ℕ}
    (hfirst : first ≤ level) (hlevel : level < P.d) :
    let T := sparseCoreRestartTool oracle C depth sparsify
    let next := (algorithm1_rebuild T tool P chain first Gnew enc).1
    let G := next.G level
    let H := next.G (level + 1)
    let len := next.toTreeChain.chainLen chain.ℓ level
    let grad := next.toTreeChain.chainGrad chain.g level
    let forest := T.lsfs (next.scState level) 0
    let hc := handleBase + level
    let bc := branchBase + level
    chain.lvlM level = M → chain.N₀ = N →
    RebuildSuffixAt R next chain.ℓ chain.g handleBase branchBase first level vc ec
      fmt.limbBits limbs fmt.precision st →
    R.Implements w p init op
      (sparseCoreMachineContract fmt limbs T G P.k M N vc ec costs allocation) →
    G.m ≤ M → G.n ≤ N →
    (∀ e ∈ G.E, 0 < len e) →
    st.regs 4 + allocation 5 [st.regs 6, st.regs 7, st.regs 8, st.regs 4] + 1 < 2 ^ w →
    P.k < 2 ^ w → 9 < 2 ^ w →
    hc ≠ bc → hc < st.regs 4 → bc < st.regs 4 →
    (∀ mid top v e cost,
      Runs w p ω (rebuildInstallReadGraph init (op 3)) st .normal mid cost →
      mid.regs 5 = top → DynGraphAt mid.mem (mid.regs 6) v e H →
      mid.regs 6 + dynGraphSize v e ≤ top ∧ top + dynGraphSize v e + 4 < 2 ^ w) →
    (∀ a, st.regs 6 ≤ a → a < st.regs 6 + dynGraphSize vc ec → a ≠ hc ∧ a ≠ bc) →
    (∀ e ∈ G.E, ∀ j < limbs, st.regs 8 + e * limbs + j ≠ hc ∧ st.regs 8 + e * limbs + j ≠ bc) →
    H.E ⊆ G.E →
    (∀ mid c fv fe,
      Runs w p ω (rebuildReadForest init (op 3) (op 2)) st .normal mid c →
      LSFAt mid.mem (mid.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
      EdgeValuesAt mid.mem (mid.mem (mid.mem (mid.regs 9 + 3) + 1))
        fmt.limbBits limbs fmt.precision G.E len) →
    ∃ out v e cost y,
      Runs w p ω (rebuildReadForestLengths init (op 3) (op 2)) st .normal out cost ∧
      out.mem hc = st.regs 4 ∧ out.mem bc = 0 ∧
      R.rep (st.regs 4) (next.scState level) y out.mem ∧
      DynGraphAt out.mem (out.regs 6) v e H ∧
      EdgeValuesAt out.mem (out.regs 7) fmt.limbBits limbs fmt.precision H.E
        (next.toTreeChain.chainLen chain.ℓ (level + 1)) ∧
      out.regs 6 + dynGraphSize v e ≤ out.regs 5 ∧
      st.regs 4 ≤ out.regs 6 ∧ st.regs 4 ≤ out.regs 5 ∧ ZeroFrom out.mem (out.regs 5) ∧
      (∃ fv fe, LSFAt out.mem (out.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest) ∧
      (∀ a < st.regs 4, a ≠ hc → a ≠ bc → out.mem a = st.mem a) ∧
      (∀ a, R.foot (st.regs 4) y a → st.regs 4 ≤ a ∧ a < out.regs 5) ∧
      DynGraphAt out.mem (st.regs 6) vc ec G ∧
      st.regs 6 + dynGraphSize vc ec ≤ out.regs 5 ∧
      st.regs 8 + ec * limbs ≤ out.regs 5 ∧
      EdgeValuesAt out.mem (st.regs 8) fmt.limbBits limbs fmt.precision G.E grad ∧
      (∀ r, r = 8 ∨ 13 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi (st.regs 4) y out.mem ≤
        costs.factor M N * (M + 1) * P.k + 17 * dynGraphSize v e + 219 := by
  dsimp only
  intro hM hN hin himpl hm hn hpos hroom hk hw hne hh hb hcopy hgraphSep hgradSep hsub hden
  have hmodel := algorithm1_rebuild_coreAt_eq_zeroExtension oracle C depth sparsify tool P chain first level
    hfirst hlevel Gnew enc
  exact RebuildSuffixAt.readCoreLengths_runs chain Gnew enc hfirst hlevel hin himpl hm hn hpos
    (by rw [← hM, ← hN]; exact hmodel)
    hroom hk hw hne hh hb hcopy hgraphSep hgradSep hsub hden

/-- Algorithm 1 Init readout for `sparseCoreRestartTool` at level `level < P.d`,
discharging the exact core-state agreement unconditionally via
`algorithm1_initialize_coreAt_eq_zeroExtension`. -/
theorem RebuildSuffixAt.initReadCoreLengths_concrete_runs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    {P : ChainParams} {tool : LastLevelTool}
    {R : DSRep (sparseCoreRestartTool oracle C depth sparsify).State}
    (lvlM : ℕ → ℕ) (N₀ : ℕ) (root : MGraph) (len₀ grad₀ : ℕ → ℝ)
    {w init tableBase level vc ec M N limbs : ℕ} {st : State}
    {fmt : Num.Format w} {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {p : Program} {ω : ℕ → Bool} {op : ℕ → ℕ}
    (hlevel : level < P.d) :
    let T := sparseCoreRestartTool oracle C depth sparsify
    let next := (algorithm1_initialize T tool P lvlM N₀ root len₀ grad₀).1
    let G := next.G level
    let H := next.G (level + 1)
    let len := next.toTreeChain.chainLen len₀ level
    let grad := next.toTreeChain.chainGrad grad₀ level
    let forest := T.lsfs (next.scState level) 0
    let hc := tableBase + level
    let bc := tableBase + (P.d + 1) + level
    lvlM level = M → N₀ = N →
    RebuildSuffixAt R next len₀ grad₀ tableBase (tableBase + (P.d + 1)) 0 level vc ec
      fmt.limbBits limbs fmt.precision st →
    InitLevelTablesSeparated tableBase P.d (st.regs 6) vc ec (st.regs 8) limbs →
    tableBase + (P.d + 1) + (P.d + 1) ≤ st.regs 4 →
    R.Implements w p init op
      (sparseCoreMachineContract fmt limbs T G P.k M N vc ec costs allocation) →
    G.m ≤ M → G.n ≤ N →
    (∀ e ∈ G.E, 0 < len e) →
    st.regs 4 + allocation 5 [st.regs 6, st.regs 7, st.regs 8, st.regs 4] + 1 < 2 ^ w →
    P.k < 2 ^ w → 9 < 2 ^ w →
    (∀ mid top v e cost,
      Runs w p ω (rebuildInstallReadGraph init (op 3)) st .normal mid cost →
      mid.regs 5 = top → DynGraphAt mid.mem (mid.regs 6) v e H →
      mid.regs 6 + dynGraphSize v e ≤ top ∧ top + dynGraphSize v e + 4 < 2 ^ w) →
    H.E ⊆ G.E →
    (∀ mid c fv fe,
      Runs w p ω (rebuildReadForest init (op 3) (op 2)) st .normal mid c →
      LSFAt mid.mem (mid.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
      EdgeValuesAt mid.mem (mid.mem (mid.mem (mid.regs 9 + 3) + 1))
        fmt.limbBits limbs fmt.precision G.E len) →
    ∃ out v e cost y,
      Runs w p ω (rebuildReadForestLengths init (op 3) (op 2)) st .normal out cost ∧
      out.mem hc = st.regs 4 ∧ out.mem bc = 0 ∧
      R.rep (st.regs 4) (next.scState level) y out.mem ∧
      DynGraphAt out.mem (out.regs 6) v e H ∧
      EdgeValuesAt out.mem (out.regs 7) fmt.limbBits limbs fmt.precision H.E
        (next.toTreeChain.chainLen len₀ (level + 1)) ∧
      out.regs 6 + dynGraphSize v e ≤ out.regs 5 ∧
      st.regs 4 ≤ out.regs 6 ∧ st.regs 4 ≤ out.regs 5 ∧ ZeroFrom out.mem (out.regs 5) ∧
      (∃ fv fe, LSFAt out.mem (out.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest) ∧
      (∀ a < st.regs 4, a ≠ hc → a ≠ bc → out.mem a = st.mem a) ∧
      (∀ a, R.foot (st.regs 4) y a → st.regs 4 ≤ a ∧ a < out.regs 5) ∧
      DynGraphAt out.mem (st.regs 6) vc ec G ∧
      st.regs 6 + dynGraphSize vc ec ≤ out.regs 5 ∧
      st.regs 8 + ec * limbs ≤ out.regs 5 ∧
      EdgeValuesAt out.mem (st.regs 8) fmt.limbBits limbs fmt.precision G.E grad ∧
      (∀ r, r = 8 ∨ 13 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi (st.regs 4) y out.mem ≤
        costs.factor M N * (M + 1) * P.k + 17 * dynGraphSize v e + 219 := by
  dsimp only
  intro hM hN hin hsep hend himpl hm hn hpos hroom hk hw hcopy hsub hden
  let T := sparseCoreRestartTool oracle C depth sparsify
  have hmodel_raw := algorithm1_initialize_coreAt_eq_zeroExtension oracle C depth sparsify tool P
    lvlM N₀ root len₀ grad₀ level hlevel
  have hmodel : (algorithm1_initialize T tool P lvlM N₀ root len₀ grad₀).1.scState level =
      T.init P.k M N ((algorithm1_initialize T tool P lvlM N₀ root len₀ grad₀).1.G level)
        (fun e => if e ∈ ((algorithm1_initialize T tool P lvlM N₀ root len₀ grad₀).1.G level).E
          then (algorithm1_initialize T tool P lvlM N₀ root len₀ grad₀).1.toTreeChain.chainLen len₀ level e else 0)
        (fun e => if e ∈ ((algorithm1_initialize T tool P lvlM N₀ root len₀ grad₀).1.G level).E
          then (algorithm1_initialize T tool P lvlM N₀ root len₀ grad₀).1.toTreeChain.chainGrad grad₀ level e else 0) := by
    rw [← hM, ← hN]
    exact hmodel_raw
  have hnext := (algorithm1_initialize_coreAt T tool P lvlM N₀ root len₀ grad₀ level hlevel).2.1
  have hnextLen := (algorithm1_initialize_nextLevelNumbers T tool P lvlM N₀ root len₀ grad₀ level hlevel).1
  have hgraphSep := hsep.graphSep hlevel.le
  have hgradSep : ∀ e ∈ ((algorithm1_initialize (sparseCoreRestartTool oracle C depth sparsify)
      tool P lvlM N₀ root len₀ grad₀).1.G level).E, ∀ j < limbs,
      st.regs 8 + e * limbs + j ≠ tableBase + level ∧
        st.regs 8 + e * limbs + j ≠ tableBase + (P.d + 1) + level :=
    fun e he => hsep.gradSep hlevel.le e (hin.graph.2.2.1 e he)
  obtain ⟨out, copied, v, e, cost, y, hrun, hhandle, hbranch, hptr, hG, hrep, hℓ, hcopyEnd,
      hcopiedLo, hheap, hfree, hforest, hframe, hfoot, hbase, hg, hregs, hcost⟩ :=
    rebuildCore_lengths_runs (ω := ω) _ _ hmodel hnext _ hnextLen himpl rfl rfl rfl rfl
      hin.graph hm hn hin.graphEnd hin.lengthsEnd hin.gradientsEnd hin.lengths hin.gradients
      hpos hin.free hroom hk hin.handleCursor hin.branchCursor (by omega) (by omega) (by omega)
      hw hcopy hgraphSep hsub hden
  exact ⟨out, v, e, cost, y, hrun, hhandle, hbranch, hrep, hptr.symm ▸ hG, hℓ, hptr.symm ▸ hcopyEnd,
    hptr.symm ▸ hcopiedLo, hheap, hfree, hforest, hframe, hfoot, hbase, hin.graphEnd.trans hheap,
    hin.gradientsEnd.trans hheap, hg hgradSep, hregs, hcost⟩

/-- Complete concrete sparse-core iteration of Algorithm 1 Init (page 20)
for `sparseCoreRestartTool`, advancing the suffix invariant and descriptor
separation from level `i` to `i + 1` with no off-edge support assumptions. -/
theorem solverInitCoreStep_concrete_runs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    {P : ChainParams} {tool : LastLevelTool}
    {R : DSRep (sparseCoreRestartTool oracle C depth sparsify).State}
    (lvlM : ℕ → ℕ) (N₀ : ℕ) (root : MGraph) (len₀ grad₀ : ℕ → ℝ) (i : Fin P.d)
    {w init copy sort entry tableBase vc ec M N limbs scanExponent nextGraphSizeCap : ℕ} {start : State}
    {fmt : Num.Format w} {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {p : Program} {ω : ℕ → Bool} {op : ℕ → ℕ} {gradientBound : ℝ} :
    let T := sparseCoreRestartTool oracle C depth sparsify
    let next := (algorithm1_initialize T tool P lvlM N₀ root len₀ grad₀).1
    let G := next.G i.val
    let H := next.G (i.val + 1)
    let len := next.toTreeChain.chainLen len₀ i.val
    let grad := next.toTreeChain.chainGrad grad₀ i.val
    let forest := T.lsfs (next.scState i.val) 0
    lvlM i.val = M → N₀ = N →
    RebuildSuffixAt R next len₀ grad₀ tableBase (tableBase + (P.d + 1)) 0 i.val vc ec
      fmt.limbBits limbs fmt.precision start →
    InitLevelTablesSeparated tableBase P.d (start.regs 6) vc ec (start.regs 8) limbs →
    tableBase + (P.d + 1) + (P.d + 1) ≤ start.regs 4 →
    start.regs 67 = limbs →
    R.Implements w p init op
      (sparseCoreMachineContract fmt limbs T G P.k M N vc ec costs allocation) →
    MeetsContract w p copy (copyWordsContract w) →
    MeetsContract w p sort (Expander.heapSortContract w) →
    (∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w fmt.limbBits x y z)) →
    G.m ≤ M → G.n ≤ N →
    (∀ e ∈ G.E, 0 < len e) →
    forest.T.IsForest → forest.T.E ⊆ G.E → G.V ⊆ forest.T.V → H.E ⊆ G.E →
    start.regs 4 + allocation 5 [start.regs 6, start.regs 7, start.regs 8, start.regs 4] + 1 < 2 ^ w →
    P.k < 2 ^ w → 9 < 2 ^ w → 2 * forest.T.n + 2 < 2 ^ w →
    fmt.precision + scanExponent + 2 ≤ fmt.limbBits * limbs →
    0 ≤ gradientBound →
    (∀ e ∈ G.E, |grad e| ≤ gradientBound) →
    (2 * (forest.T.m : ℝ) + 1) * gradientBound ≤ (2 : ℝ) ^ scanExponent →
    (∀ args,
      Runs w p ω prepareRebuildGraphArgs
        { start with regs := Function.update (Function.update start.regs 53 (start.regs 19)) 54 (start.regs 21) }
        .normal args 36 →
      (∀ mid top v e cost,
        Runs w p ω (rebuildInstallReadGraph init (op 3)) args .normal mid cost →
        mid.regs 5 = top → DynGraphAt mid.mem (mid.regs 6) v e H →
        mid.regs 6 + dynGraphSize v e ≤ top ∧ top + dynGraphSize v e + 4 < 2 ^ w) ∧
      (∀ mid c fv fe,
        Runs w p ω (rebuildReadForest init (op 3) (op 2)) args .normal mid c →
        LSFAt mid.mem (mid.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
        EdgeValuesAt mid.mem (mid.mem (mid.mem (mid.regs 9 + 3) + 1))
          fmt.limbBits limbs fmt.precision G.E len) ∧
      (∀ st v e fv fe c,
        Runs w p ω (rebuildReadForestLengths init (op 3) (op 2)) args .normal st c →
        DynGraphAt st.mem (st.regs 6) v e H →
        LSFAt st.mem (st.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
        dynGraphSize v e ≤ nextGraphSizeCap ∧
        st.mem (st.regs 9) + dynGraphSize fv fe ≤ st.regs 5 ∧
        st.regs 7 + e * limbs ≤ st.regs 5 ∧ e ≤ ec ∧
        st.regs 5 + forest.T.n + 2 < 2 ^ w ∧
        st.regs 5 + forest.T.n + fv * limbs + limbs + fv + fv +
          3 * limbs * forest.T.vol forest.T.V + ec * limbs + 3 * limbs * H.m < 2 ^ w)) →
    ∃ out nextVC nextEC cost,
      Runs w p ω (rebuildCoreStep init (op 3) (op 2) copy sort entry) start .normal out cost ∧
      (RebuildSuffixAt R next len₀ grad₀ tableBase (tableBase + (P.d + 1)) 0 (i.val + 1)
        nextVC nextEC fmt.limbBits limbs fmt.precision
        { out with regs := Function.update out.regs 19 (i.val + 1) } ∧
      out.regs 19 = i.val) ∧
      InitLevelTablesSeparated tableBase P.d (out.regs 6) nextVC nextEC (out.regs 8) limbs ∧
      start.regs 4 ≤ out.regs 4 ∧
      out.mem (tableBase + i.val) = start.regs 4 ∧
      (∀ a < start.regs 4, a ≠ start.regs 51 → a ≠ start.regs 52 → out.mem a = start.mem a) ∧
      cost ≤ 280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m +
        costs.factor M N * (M + 1) * P.k + 17 * nextGraphSizeCap + 484 := by
  dsimp only
  intro hM hN hin hsep hend hlimbs himpl hcopy hsort hentry hm hn hpos hforest hsub hverts hHE
    hroom hk hw hcount hscanWidth hboundNonneg hgradBound hsizeBound hreadout
  have hheapWord : start.regs 4 < 2 ^ w := by omega
  obtain ⟨args, hargs, h50, h17, h15, h16, hinArgs, hregsArgs, hmemArgs⟩ :=
    RebuildSuffixAt.prepareGraphArgs_runs (ω := ω) hin hheapWord (by omega)
  have hargs4 : args.regs 4 = start.regs 4 := hregsArgs 4 (by decide)
  have hargs6 : args.regs 6 = start.regs 6 := hregsArgs 6 (by decide)
  have hargs7 : args.regs 7 = start.regs 7 := hregsArgs 7 (by decide)
  have hargs8 : args.regs 8 = start.regs 8 := hregsArgs 8 (by decide)
  have hargs67 : args.regs 67 = limbs := (hregsArgs 67 (by decide)).trans hlimbs
  obtain ⟨hcopyRoom, hden, hpostReadout⟩ := hreadout args hargs
  obtain ⟨st, nextVC, nextEC, prefixCost, y, hprefix, hhc, hbc, hrep, hH, hnextLen, hHEnd,
      hcopiedLo, hheapLo, hz', ⟨fv, fe, hlsf⟩, hframe, hfoot, hG', hGEnd, hGradEnd, hGrad',
      hregsSt, hcostPre⟩ :=
    RebuildSuffixAt.initReadCoreLengths_concrete_runs oracle C depth sparsify lvlM N₀ root len₀ grad₀
      i.isLt hM hN hinArgs (by simpa only [hargs6, hargs8] using hsep) (hargs4.symm ▸ hend)
      himpl hm hn hpos (by simpa only [hargs4, hargs6, hargs7, hargs8] using hroom) hk hw
      hcopyRoom hHE hden
  obtain ⟨hnextCap, hforestEnd, hlenEnd, hcap, hsortRoom, hspace⟩ :=
    hpostReadout st nextVC nextEC fv fe prefixCost hprefix hH hlsf
  obtain ⟨out, cost, hstep, hs, ho6, ho8Lo, hheapOut, hmemCell, hframeOut, hcostStep⟩ :=
    solverInitCoreStep_fromReadout_runs (R := R) (last := tool) lvlM N₀ root len₀ grad₀ i hargs hmemArgs
      hprefix hcopy hsort hlsf rfl rfl ((hregsSt 67 (by decide)).trans hargs67) hz'
      hforestEnd hsortRoom hcount (by omega) hforest (by simpa only [hargs8] using hGrad') hsub
      (by simpa only [hargs8] using hGradEnd) hentry (by simpa only [hargs6] using hG')
      (by simpa only [hargs6] using hGEnd) hverts hH hHEnd hHE rfl
      ((hregsSt 8 (by decide)).trans hargs8) ((hregsSt 50 (by decide)).trans h50)
      ((hregsSt 15 (by decide)).trans h15) ((hregsSt 16 (by decide)).trans h16)
      ((hregsSt 17 (by decide)).trans h17) _ hnextLen hlenEnd hcap (by omega) hspace
      scanExponent hscanWidth gradientBound hboundNonneg hgradBound hsizeBound tableBase hin rfl
      hheapWord rfl rfl hend rfl rfl rfl rfl rfl himpl.1 (hargs4 ▸ hrep) (hargs4 ▸ hfoot)
      (hargs4 ▸ hhc) hbc (by omega) (by omega) (hargs4 ▸ hheapLo) (hargs4 ▸ hframe)
  have hsepNext : InitLevelTablesSeparated tableBase P.d (out.regs 6) nextVC nextEC (out.regs 8) limbs :=
    Or.inr ⟨by rw [ho6]; exact hend.trans (hargs4 ▸ hcopiedLo), hend.trans ho8Lo⟩
  refine ⟨out, nextVC, nextEC, cost, hstep, hs, hsepNext, hheapOut, hmemCell, hframeOut, ?_⟩
  rw [hargs4] at hcostPre
  omega

/-- Shift deeper-level initialization for `sparseCoreRestartTool`, removing
the two off-edge support hypotheses via `sparseCoreRestartTool_init_eq_zeroExtension`. -/
theorem shiftDeeperLevel_concrete_runs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    {w L k M N vc ec inputEC restart read forestOp copy sort cell init : ℕ}
    {fmt : Num.Format w} {G H : MGraph} {forest : LSF}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (sparseCoreRestartTool oracle C depth sparsify).State}
    {p : Program} {op : ℕ → ℕ} {st mid : State} {ω : ℕ → Bool}
    {prefixCost : ℕ} (ℓ g : ℕ → ℝ)
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L (sparseCoreRestartTool oracle C depth sparsify)
        H k M N vc ec costs allocation))
    (hprep : Runs w p ω (shiftRestartPrepareGradients restart read forestOp copy sort cell) st .normal mid prefixCost)
    (hgraph : DynGraphAt mid.mem (mid.regs 6) vc ec H)
    (hlen : EdgeValuesAt mid.mem (mid.regs 7) fmt.limbBits L fmt.precision H.E ℓ)
    (hgrad : EdgeValuesAt mid.mem (mid.regs 8) fmt.limbBits L fmt.precision H.E (coreGrad G forest g))
    (hk : 0 < k) (hm : H.m ≤ M) (hn : H.n ≤ N)
    (hgEnd : mid.regs 6 + dynGraphSize vc ec ≤ mid.regs 4)
    (hlenEnd : mid.regs 7 + ec * L ≤ mid.regs 4)
    (hgradEnd : mid.regs 8 + inputEC * L ≤ mid.regs 4) (hec : ec ≤ inputEC)
    (hpos : ∀ e ∈ H.E, 0 < ℓ e) (hz : ZeroFrom mid.mem (mid.regs 4))
    (hroom : mid.regs 4 + allocation 5 [mid.regs 6, mid.regs 7, mid.regs 8, mid.regs 4] < 2 ^ w) :
    let tool := sparseCoreRestartTool oracle C depth sparsify
    let model := tool.init k M N H ℓ (coreGrad G forest g)
    ∃ out ret cost y, Runs w p ω (shiftDeeperLevel restart read forestOp copy sort cell init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = mid.regs 4 ∧ out.regs 4 = ret ∧
      R.rep (mid.regs 4) model y out.mem ∧
      SparseCoreInput tool.toSparseCoreTool tool.restart k model H ∧
      R.Respects (fun _ => False) (mid.regs 4)
        (allocation 5 [mid.regs 6, mid.regs 7, mid.regs 8, mid.regs 4])
        mid.mem ret (mid.regs 4) y out.mem ∧
      cost + R.phi (mid.regs 4) y out.mem ≤ prefixCost + costs.factor M N * (M + 1) * k + 12 := by
  have hrun := shiftDeeperLevel_runs (ω := ω) ℓ g himpl hprep hgraph hlen hgrad
    hk hm hn hgEnd hlenEnd hgradEnd hec hpos hz hroom
  dsimp only at hrun ⊢
  rwa [← sparseCoreRestartTool_init_eq_zeroExtension oracle C depth sparsify k M N H ℓ (coreGrad G forest g)] at hrun

end MinCostFlow.MinRatio
