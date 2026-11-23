module

public import MinCostFlow.MinRatio.InitCoreStep
public import MinCostFlow.MinRatio.RebuildSuffixLoop
public import MinCostFlow.MinRatio.RebuildSuffix
import MinCostFlow.MinRatio.RebuildModelSuffix

/-!
# Exact core-state agreement for Rebuild and Shift suffixes

Uses `Chain.SparseCoreRestartInitAgree` and `fixedPointLastLevel_build_congr` to
assemble the complete periodic Rebuild suffix loop (`first .. P.d`) and the
terminal Shift handoff for `sparseCoreRestartTool` and `fixedPointLastLevelTool`
without off-edge support assumptions.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- At the terminal handoff with `fixedPointLastLevelTool`, Shift represents the
exact model terminal collection without any off-edge zero-extension hypothesis,
discharged via `fixedPointLastLevel_build_congr`. -/
theorem shiftInstallTerminal_fixedPoint_runs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    {w limbs restart read forestOp init vc ec multiplier stretchPrecision i prefixCost handleCell branchCell : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool}
    {P : ChainParams} (chain : ChainState T P) (hi : i + 1 = P.d)
    {allocation : ℕ → List ℕ → ℕ} {R : DSRep (ℕ × (ℕ → LSF))}
    {p : Program} {op : ℕ → ℕ} {initial mid : State} {ω : ℕ → Bool} :
    let tool := LastLevelProgram.fixedPointLastLevelTool oracle C
    let next := (algorithm1_shift T tool P chain i).1
    let G := next.G P.d
    let ℓ := next.toTreeChain.chainLen chain.ℓ P.d
    let graph := mid.regs 6
    let lengths := mid.regs 7
    let heap := mid.regs 5
    G.IsValid →
    Runs w p ω (shiftRestartGraphAndLengths restart read forestOp)
      initial .normal mid prefixCost →
    R.Implements w p init op (lastLevelRuntimeMachineContract fmt limbs tool G vc ec multiplier stretchPrecision allocation) →
    mid.regs 67 = limbs → mid.regs 68 = fmt.precision →
    limbs < 2 ^ w → fmt.precision < 2 ^ w → fmt.limbBits = 4 → fmt.precision ≤ 4 * limbs →
    DynGraphAt mid.mem graph vc ec G →
    graph + dynGraphSize vc ec ≤ heap → lengths + ec * limbs ≤ heap →
    EdgeValuesAt mid.mem lengths fmt.limbBits limbs fmt.precision G.E ℓ →
    (∀ e ∈ G.E, 2 * (2 : ℝ) ^ stretchPrecision * lastLevelStretchBound G ℓ e <
      Num.capacity fmt.limbBits limbs) →
    (∀ e ∈ G.E, 0 < ℓ e) →
    ZeroFrom mid.mem heap → heap + allocation 1 [graph, lengths, limbs, fmt.precision, heap] < 2 ^ w →
    initial.regs 51 = handleCell → initial.regs 52 = branchCell →
    handleCell ≠ branchCell → handleCell < heap → branchCell < heap →
    ∃ out ret cost y, Runs w p ω (shiftInstallTerminal restart read forestOp init)
        initial .normal out cost ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧
      out.regs 4 = ret ∧ R.rep heap (next.lastK, next.lastLSFs) y out.mem ∧
      ZeroFrom out.mem ret ∧
      (∀ a, R.foot heap y a → heap ≤ a ∧ a < ret) ∧
      cost + R.phi heap y out.mem ≤ prefixCost + multiplier * (tool.cost G + 1) + 24 := by
  dsimp only
  intro hValid hp himpl hL hP hLWord hPWord hFour hWidth hg hgb hlb hl hst hpos hz hroom hh hb hne hhBelow hbBelow
  let tool := LastLevelProgram.fixedPointLastLevelTool oracle C
  let next := (algorithm1_shift T tool P chain i).1
  let G := next.G P.d
  let ℓ := next.toTreeChain.chainLen chain.ℓ P.d
  let ready := { mid with regs := Function.update mid.regs 4 (mid.regs 5) }
  have hset : Runs w p ω (.assign 4 (.reg 5)) mid .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  obtain ⟨built, ret, c, y, hr, _, hhandle, hret, hrep0, _, hframe, hc⟩ :=
    rebuildLastLevelRuntime_tables_runs (st := ready) (ω := ω) himpl
      (by simp [ready, Function.update_of_ne]) (by simp [ready, Function.update_of_ne])
      (by simp [ready]) (by simpa [ready] using hL) (by simpa [ready] using hP)
      hLWord hPWord hFour hWidth ℓ hg hgb hlb hl hst hpos hz hroom
  have hagree : tool.build G (fun e => if e ∈ G.E then ℓ e else 0) = (next.lastK, next.lastLSFs) := by
    dsimp only [next, G, ℓ]
    rw [shiftTerminalBuild_eq T tool P chain i hi]
    exact fixedPointLastLevel_build_congr oracle C hValid (fun e he => by simp [he])
  have hrep : R.rep (mid.regs 5) (next.lastK, next.lastLSFs) y built.mem := hagree ▸ hrep0
  have hbuild : Runs w p ω (shiftRebuildTerminal restart read forestOp init)
      initial .normal built (prefixCost + (2 + c + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨mid, prefixCost, 2 + c + 1, hp,
      runs_seq_iff.mpr (Or.inr ⟨ready, 2, c, hset, hr, rfl⟩), rfl⟩)
  have hfoot (a : ℕ) (ha : R.foot (mid.regs 5) y a) : mid.regs 5 ≤ a ∧ a < ret :=
    (hframe.2.2.2.2 a ha).resolve_left id
  obtain ⟨out, ho, hh', hb', hrep', hphi, hmem, hregs⟩ :=
    shiftInstallTerminal_runs hbuild himpl.1 hh hb hne (hhandle.symm ▸ hhBelow)
      (hhandle.symm ▸ hbBelow) (fun a ha => hhandle.symm ▸ (hfoot a (hhandle ▸ ha)).1)
      (hhandle.symm ▸ hrep)
  have houtHandle : out.regs 3 = mid.regs 5 := hregs ▸ hhandle
  have houtPhi : R.phi (mid.regs 5) y out.mem = R.phi (mid.regs 5) y built.mem := by
    simpa only [houtHandle, hhandle] using hphi
  refine ⟨out, ret, (prefixCost + (2 + c + 1) + 1) + 8, y, ho,
    hh'.trans houtHandle, hb', hregs ▸ hret, houtHandle ▸ hrep', ?_, hfoot, ?_⟩
  · intro a ha
    have hlo := hframe.1
    exact (hmem a (by omega) (by omega)).trans (hframe.2.2.1 a ha)
  · rw [houtPhi]
    omega

/-- Graph and gradient tables avoid the suffix descriptor slots
`[handleBase + first, handleBase + d]` and `[branchBase + first, branchBase + d]`
during periodic Rebuild: either explicitly at entry or by lying at or above
`heapFloor` strictly beyond both descriptor arrays. -/
@[expose] def RebuildTablesSeparated
    (handleBase branchBase first d heapFloor graph vc ec gradient limbs : ℕ) : Prop :=
  (∀ i, first ≤ i → i ≤ d →
    (∀ a, graph ≤ a → a < graph + dynGraphSize vc ec →
      a ≠ handleBase + i ∧ a ≠ branchBase + i) ∧
    (∀ e < ec, ∀ j < limbs,
      gradient + e * limbs + j ≠ handleBase + i ∧ gradient + e * limbs + j ≠ branchBase + i)) ∨
  (heapFloor ≤ graph ∧ heapFloor ≤ gradient)

theorem RebuildTablesSeparated.graphSep
    {handleBase branchBase first d heapFloor graph vc ec gradient limbs i : ℕ}
    (hsep : RebuildTablesSeparated handleBase branchBase first d heapFloor graph vc ec gradient limbs)
    (hhFloor : handleBase + d < heapFloor) (hbFloor : branchBase + d < heapFloor)
    (hlo : first ≤ i) (hhi : i ≤ d) :
    ∀ a, graph ≤ a → a < graph + dynGraphSize vc ec →
      a ≠ handleBase + i ∧ a ≠ branchBase + i := by
  intro a h1 h2
  rcases hsep with h | ⟨hg, _⟩
  · exact (h i hlo hhi).1 a h1 h2
  · exact ⟨by omega, by omega⟩

theorem RebuildTablesSeparated.gradSep
    {handleBase branchBase first d heapFloor graph vc ec gradient limbs i : ℕ}
    (hsep : RebuildTablesSeparated handleBase branchBase first d heapFloor graph vc ec gradient limbs)
    (hhFloor : handleBase + d < heapFloor) (hbFloor : branchBase + d < heapFloor)
    (hlo : first ≤ i) (hhi : i ≤ d) :
    ∀ e < ec, ∀ j < limbs,
      gradient + e * limbs + j ≠ handleBase + i ∧ gradient + e * limbs + j ≠ branchBase + i := by
  intro e he j hj
  rcases hsep with h | ⟨_, hg⟩
  · exact (h i hlo hhi).2 e he j hj
  · exact ⟨by omega, by omega⟩

/-- One complete concrete periodic Rebuild step for `sparseCoreRestartTool` at
level `i` (`first ≤ i < P.d`), discharging off-edge agreement via
`algorithm1_rebuild_coreAt_eq_zeroExtension` and preserving `RebuildTablesSeparated`. -/
theorem rebuildCoreStep_concrete_runs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    {P : ChainParams} {L : LastLevelTool}
    {R : DSRep (sparseCoreRestartTool oracle C depth sparsify).State}
    (chain : ChainState (sparseCoreRestartTool oracle C depth sparsify) P)
    (Gnew : MGraph) (enc first : ℕ) (i : Fin P.d) (hfirst : first ≤ i.val)
    {w init copy sort entry handleBase branchBase heapFloor vc ec M N limbs scanExponent
      nextGraphSizeCap : ℕ}
    {fmt : Num.Format w} {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {gradientBound : ℝ} {p : Program} {op : ℕ → ℕ} {start : State} {ω : ℕ → Bool} :
    let T := sparseCoreRestartTool oracle C depth sparsify
    let next := (algorithm1_rebuild T L P chain first Gnew enc).1
    let G := next.G i.val
    let H := next.G (i.val + 1)
    let len := next.toTreeChain.chainLen chain.ℓ i.val
    let grad := next.toTreeChain.chainGrad chain.g i.val
    let forest := T.lsfs (next.scState i.val) 0
    RebuildSuffixAt R next chain.ℓ chain.g handleBase branchBase first i.val vc ec
      fmt.limbBits limbs fmt.precision start →
    RebuildTablesSeparated handleBase branchBase first P.d heapFloor
      (start.regs 6) vc ec (start.regs 8) limbs →
    heapFloor ≤ start.regs 4 →
    handleBase + P.d < heapFloor → branchBase + P.d < heapFloor →
    (handleBase + P.d < branchBase + first ∨ branchBase + P.d < handleBase + first) →
    start.regs 67 = limbs →
    R.Local →
    R.Implements w p init op
      (sparseCoreMachineContract fmt limbs T G P.k M N vc ec costs allocation) →
    MeetsContract w p copy (copyWordsContract w) →
    MeetsContract w p sort (Expander.heapSortContract w) →
    (∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w fmt.limbBits x y z)) →
    chain.lvlM i.val = M → chain.N₀ = N →
    G.m ≤ M → G.n ≤ N → (∀ e ∈ G.E, 0 < len e) →
    forest.T.IsForest → forest.T.E ⊆ G.E → G.V ⊆ forest.T.V → H.E ⊆ G.E →
    start.regs 4 + allocation 5 [start.regs 6, start.regs 7, start.regs 8, start.regs 4] + 1 < 2 ^ w →
    P.k < 2 ^ w → 9 < 2 ^ w → 2 * forest.T.n + 2 < 2 ^ w →
    fmt.precision + scanExponent + 2 ≤ fmt.limbBits * limbs →
    0 ≤ gradientBound → (∀ e ∈ G.E, |grad e| ≤ gradientBound) →
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
      (∀ s v e fv fe c,
        Runs w p ω (rebuildReadForestLengths init (op 3) (op 2)) args .normal s c →
        DynGraphAt s.mem (s.regs 6) v e H →
        LSFAt s.mem (s.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
        dynGraphSize v e ≤ nextGraphSizeCap ∧
        s.mem (s.regs 9) + dynGraphSize fv fe ≤ s.regs 5 ∧
        s.regs 7 + e * limbs ≤ s.regs 5 ∧ e ≤ ec ∧
        s.regs 5 + forest.T.n + 2 < 2 ^ w ∧
        s.regs 5 + forest.T.n + fv * limbs + limbs + fv + fv +
          3 * limbs * forest.T.vol forest.T.V + ec * limbs + 3 * limbs * H.m < 2 ^ w)) →
    ∃ out nextVC nextEC cost,
      Runs w p ω (rebuildCoreStep init (op 3) (op 2) copy sort entry) start .normal out cost ∧
      RebuildSuffixAt R next chain.ℓ chain.g handleBase branchBase first (i.val + 1)
        nextVC nextEC fmt.limbBits limbs fmt.precision
        { out with regs := Function.update out.regs 19 (i.val + 1) } ∧
      RebuildTablesSeparated handleBase branchBase first P.d heapFloor
        (out.regs 6) nextVC nextEC (out.regs 8) limbs ∧
      out.regs 19 = i.val ∧ start.regs 4 ≤ out.regs 4 ∧
      (∀ a < start.regs 4, a ≠ handleBase + i.val → a ≠ branchBase + i.val →
        out.mem a = start.mem a) ∧
      cost ≤ 280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m +
        costs.factor M N * (M + 1) * P.k + 17 * nextGraphSizeCap + 484 := by
  dsimp only
  intro hin hsep hfloor hhFloor hbFloor hdisj hlimbs hlocal himpl hcopy hsort hentry
    hM hN hm hn hpos hforest hFsub hVsub hHsub hroom hk hw9 hcount hscanWidth hboundNonneg
    hgradBound hsizeBound hreadout
  let T := sparseCoreRestartTool oracle C depth sparsify
  let next := (algorithm1_rebuild T L P chain first Gnew enc).1
  have hhandleW : start.regs 4 < 2 ^ w := by omega
  obtain ⟨args, hargs, h50, h17, h15, h16, hinArgs, hregsArgs, hargsMem⟩ :=
    RebuildSuffixAt.prepareGraphArgs_runs (ω := ω) hin hhandleW (by omega)
  have h4eq : args.regs 4 = start.regs 4 := hregsArgs 4 (by decide)
  have h6eq : args.regs 6 = start.regs 6 := hregsArgs 6 (by decide)
  have h7eq : args.regs 7 = start.regs 7 := hregsArgs 7 (by decide)
  have h8eq : args.regs 8 = start.regs 8 := hregsArgs 8 (by decide)
  have h67eq : args.regs 67 = limbs := (hregsArgs 67 (by decide)).trans hlimbs
  obtain ⟨hcopyRead, hdenRead, hspaceRead⟩ := hreadout args hargs
  have hgraphSep : ∀ a, args.regs 6 ≤ a → a < args.regs 6 + dynGraphSize vc ec →
      a ≠ handleBase + i.val ∧ a ≠ branchBase + i.val := by
    rw [h6eq]
    exact hsep.graphSep hhFloor hbFloor hfirst i.isLt.le
  have hgradSep : ∀ e ∈ (next.G i.val).E, ∀ j < limbs,
      args.regs 8 + e * limbs + j ≠ handleBase + i.val ∧
        args.regs 8 + e * limbs + j ≠ branchBase + i.val := by
    rw [h8eq]
    exact fun e he => hsep.gradSep hhFloor hbFloor hfirst i.isLt.le e (hin.graph.2.2.1 e he)
  obtain ⟨mid, v, e, prefixCost, y, hprefix, hhc, hbc, hrep, hH, hlen, hHEnd, h6Lo, hheapLo,
      hfree, ⟨fv, fe, hlsf⟩, hframePrefix, hfoot, hGmid, hGEndMid, hGradEndMid, hGradMid,
      hregsMid, hprefixCost⟩ :=
    RebuildSuffixAt.rebuildReadCoreLengths_concrete_runs oracle C depth sparsify chain Gnew enc
      hfirst i.isLt hM hN hinArgs himpl hm hn hpos
      (by rw [h4eq, h6eq, h7eq, h8eq]; exact hroom) hk hw9
      (by omega) (by omega) (by omega) hcopyRead hgraphSep hgradSep hHsub hdenRead
  obtain ⟨hcapNext, hlsfEnd, hlenEnd, heCap, hsortRoom, hscanSpace⟩ :=
    hspaceRead mid v e fv fe prefixCost hprefix hH hlsf
  have hnextGrad := (rebuildSuffix_nextLevelNumbers T L P chain first i.val hfirst i.isLt Gnew enc).2
  have hfirstLt : first < P.d := lt_of_le_of_lt hfirst i.isLt
  have hbran0 : next.bran i.val = 0 := by
    simp only [next, algorithm1_rebuild, hfirstLt, dite_true]
    rw [rebuildSuffix_branch]
    simp [hfirst, Nat.add_sub_of_le hfirstLt.le, i.isLt]
  obtain ⟨out, cost, hrun, hin', hi', ho6, ho8, _, ho4, hframeOut, hcost⟩ :=
    rebuildCoreStep_fromReadout_runs next chain.ℓ chain.g first i hfirst
      hargs hargsMem hprefix hcopy hsort hlsf rfl rfl
      ((hregsMid 67 (Or.inr (by decide))).trans h67eq) hfree hlsfEnd hsortRoom hcount
      (by omega) hforest (by simpa only [h8eq] using hGradMid) hFsub
      (by simpa only [h8eq] using hGradEndMid) hentry
      (by simpa only [h6eq] using hGmid) (by simpa only [h6eq] using hGEndMid) hVsub hH hHEnd hHsub
      rfl ((hregsMid 8 (Or.inl rfl)).trans h8eq) ((hregsMid 50 (Or.inr (by decide))).trans h50)
      ((hregsMid 15 (Or.inr (by decide))).trans h15)
      ((hregsMid 16 (Or.inr (by decide))).trans h16)
      ((hregsMid 17 (Or.inr (by decide))).trans h17)
      _ hlen hlenEnd heCap (by omega) hscanSpace scanExponent hscanWidth
      gradientBound hboundNonneg hgradBound hsizeBound handleBase branchBase
      hin rfl hhandleW rfl rfl (by omega) (by omega) hdisj
      rfl rfl rfl rfl rfl hnextGrad hbran0 hlocal (h4eq ▸ hrep)
      (by rw [← h4eq]; exact hfoot) (by rw [← h4eq]; exact hhc) hbc
      (by omega) (by omega) (by rw [← h4eq]; exact hheapLo)
      (by rw [← h4eq]; exact hframePrefix)
  have hphiZero : 0 ≤ R.phi (start.regs 4) y out.mem := Nat.zero_le _
  have hphiEq : R.phi (start.regs 4) y mid.mem = R.phi (args.regs 4) y mid.mem := by rw [h4eq]
  refine ⟨out, v, e, cost, hrun, hin', Or.inr ⟨hfloor.trans (ho6.symm ▸ (h4eq ▸ h6Lo)), hfloor.trans ho8⟩,
    hi', ho4, hframeOut, ?_⟩
  omega

/-- Full periodic Rebuild suffix (`first .. P.d`) for `sparseCoreRestartTool`
and `fixedPointLastLevelTool`, discharging every sparse-core and terminal
off-edge agreement unconditionally. -/
theorem rebuildSuffixProgram_fixedPoint_runs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    {P : ChainParams}
    {R : DSRep (sparseCoreRestartTool oracle C depth sparsify).State}
    {terminal : DSRep (ℕ × (ℕ → LSF))}
    (chain : ChainState (sparseCoreRestartTool oracle C depth sparsify) P)
    (Gnew : MGraph) (enc first : ℕ) (hfirstLt : first < P.d)
    {w handleBase branchBase heapFloor vc0 ec0 limbs init copy sort entry terminalInit : ℕ}
    {fmt : Num.Format w} {costs : SparseCoreMachineCosts}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {lastAllocation : ℕ → List ℕ → ℕ}
    {multiplier stretchPrecision : ℕ}
    {M N scanExponent nextGraphSizeCap : ℕ → ℕ} {gradientBound : ℕ → ℝ}
    {p : Program} {op lastOp : ℕ → ℕ} {st : State} {ω : ℕ → Bool} :
    let T := sparseCoreRestartTool oracle C depth sparsify
    let L := LastLevelProgram.fixedPointLastLevelTool oracle C
    let next := (algorithm1_rebuild T L P chain first Gnew enc).1
    let levelCost := fun i =>
      let forest := T.lsfs (next.scState i) 0
      let H := next.G (i + 1)
      280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m +
        costs.factor (M i) (N i) * (M i + 1) * P.k + 17 * nextGraphSizeCap (i + 1) + 484
    let terminalCost := multiplier * (L.cost (next.G P.d) + 1) + 20
    st.regs 20 = first →
    st.regs 67 = limbs → st.regs 68 = fmt.precision →
    RebuildSuffixAt R next chain.ℓ chain.g handleBase branchBase first first vc0 ec0
      fmt.limbBits limbs fmt.precision { st with regs := Function.update st.regs 19 first } →
    RebuildTablesSeparated handleBase branchBase first P.d heapFloor
      (st.regs 6) vc0 ec0 (st.regs 8) limbs →
    heapFloor ≤ st.regs 4 →
    handleBase + P.d < heapFloor → branchBase + P.d < heapFloor →
    (handleBase + P.d < branchBase + first ∨ branchBase + P.d < handleBase + first) →
    limbs < 2 ^ w → fmt.precision < 2 ^ w → fmt.limbBits = 4 → fmt.precision ≤ 4 * limbs →
    P.d < 2 ^ w → P.k < 2 ^ w → 9 < 2 ^ w →
    R.Local →
    MeetsContract w p copy (copyWordsContract w) →
    MeetsContract w p sort (Expander.heapSortContract w) →
    (∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w fmt.limbBits x y z)) →
    (next.G P.d).IsValid →
    (∀ i, first ≤ i → i < P.d → ∀ vc ec,
      R.Implements w p init op
        (sparseCoreMachineContract fmt limbs T (next.G i) P.k (M i) (N i) vc ec costs (allocation i))) →
    (∀ vc ec,
      terminal.Implements w p terminalInit lastOp
        (lastLevelRuntimeMachineContract fmt limbs L (next.G P.d) vc ec
          multiplier stretchPrecision lastAllocation)) →
    (∀ i, first ≤ i → i < P.d →
      let G := next.G i
      let H := next.G (i + 1)
      let len := next.toTreeChain.chainLen chain.ℓ i
      let grad := next.toTreeChain.chainGrad chain.g i
      let forest := T.lsfs (next.scState i) 0
      chain.lvlM i = M i ∧ chain.N₀ = N i ∧
      G.m ≤ M i ∧ G.n ≤ N i ∧ (∀ e ∈ G.E, 0 < len e) ∧
      forest.T.IsForest ∧ forest.T.E ⊆ G.E ∧ G.V ⊆ forest.T.V ∧ H.E ⊆ G.E ∧
      2 * forest.T.n + 2 < 2 ^ w ∧
      fmt.precision + scanExponent i + 2 ≤ fmt.limbBits * limbs ∧
      0 ≤ gradientBound i ∧ (∀ e ∈ G.E, |grad e| ≤ gradientBound i) ∧
      (2 * (forest.T.m : ℝ) + 1) * gradientBound i ≤ (2 : ℝ) ^ scanExponent i) →
    (∀ (ω' : ℕ → Bool) i, first ≤ i → i < P.d → ∀ vc ec before,
      let G := next.G i
      let H := next.G (i + 1)
      let len := next.toTreeChain.chainLen chain.ℓ i
      let forest := T.lsfs (next.scState i) 0
      RebuildSuffixAt R next chain.ℓ chain.g handleBase branchBase first i vc ec
        fmt.limbBits limbs fmt.precision before →
      RebuildTablesSeparated handleBase branchBase first P.d heapFloor
        (before.regs 6) vc ec (before.regs 8) limbs →
      heapFloor ≤ before.regs 4 →
      before.regs 4 + allocation i 5 [before.regs 6, before.regs 7, before.regs 8, before.regs 4] + 1 < 2 ^ w ∧
      ∀ args,
        Runs w p ω' prepareRebuildGraphArgs
          { before with regs := Function.update (Function.update before.regs 53 (before.regs 19)) 54 (before.regs 21) }
          .normal args 36 →
        (∀ mid top v e cost,
          Runs w p ω' (rebuildInstallReadGraph init (op 3)) args .normal mid cost →
          mid.regs 5 = top → DynGraphAt mid.mem (mid.regs 6) v e H →
          mid.regs 6 + dynGraphSize v e ≤ top ∧ top + dynGraphSize v e + 4 < 2 ^ w) ∧
        (∀ mid c fv fe,
          Runs w p ω' (rebuildReadForest init (op 3) (op 2)) args .normal mid c →
          LSFAt mid.mem (mid.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
          EdgeValuesAt mid.mem (mid.mem (mid.mem (mid.regs 9 + 3) + 1))
            fmt.limbBits limbs fmt.precision G.E len) ∧
        (∀ s v e fv fe c,
          Runs w p ω' (rebuildReadForestLengths init (op 3) (op 2)) args .normal s c →
          DynGraphAt s.mem (s.regs 6) v e H →
          LSFAt s.mem (s.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
          dynGraphSize v e ≤ nextGraphSizeCap (i + 1) ∧
          s.mem (s.regs 9) + dynGraphSize fv fe ≤ s.regs 5 ∧
          s.regs 7 + e * limbs ≤ s.regs 5 ∧ e ≤ ec ∧
          s.regs 5 + forest.T.n + 2 < 2 ^ w ∧
          s.regs 5 + forest.T.n + fv * limbs + limbs + fv + fv +
            3 * limbs * forest.T.vol forest.T.V + ec * limbs + 3 * limbs * H.m < 2 ^ w)) →
    (∀ e ∈ (next.G P.d).E, 2 * (2 : ℝ) ^ stretchPrecision *
      lastLevelStretchBound (next.G P.d) (next.toTreeChain.chainLen chain.ℓ P.d) e <
        Num.capacity fmt.limbBits limbs) →
    (∀ e ∈ (next.G P.d).E, 0 < next.toTreeChain.chainLen chain.ℓ P.d e) →
    (∀ vc ec before,
      RebuildSuffixAt R next chain.ℓ chain.g handleBase branchBase first P.d vc ec
        fmt.limbBits limbs fmt.precision before →
      before.regs 4 + lastAllocation 1 [before.regs 6, before.regs 7, limbs, fmt.precision, before.regs 4] < 2 ^ w) →
    ∃ out c, Runs w p ω
        (rebuildSuffixProgram (rebuildCoreStep init (op 3) (op 2) copy sort entry)
          (rebuildTerminalRuntimeStep terminalInit))
        st .normal out c ∧
      RebuiltCoresAt R next out.mem handleBase branchBase first P.d (out.regs 4) ∧
      out.mem (branchBase + P.d) = next.lastBran ∧ ZeroFrom out.mem (out.regs 4) ∧
      (∃ y : terminal.τ, terminal.rep (out.mem (handleBase + P.d)) (next.lastK, next.lastLSFs)
        y out.mem ∧ ∀ a, terminal.foot (out.mem (handleBase + P.d)) y a → a < out.regs 4) ∧
      (∀ a < heapFloor, (a < handleBase + first ∨ handleBase + P.d < a) →
        (a < branchBase + first ∨ branchBase + P.d < a) → out.mem a = st.mem a) ∧
      c ≤ rangeCost levelCost first P.d + (P.d - first) * 9 + terminalCost + 8 := by
  dsimp only
  intro h20 h67 h68 hin0 hsep0 hfloor0 hhFloor hbFloor hdisj hLWord hPWord hFour hWidth
    hPword hkWord hw9 hlocal hcopy hsort hentry hValidLast hcoreImpl htermImpl hmodel hreadout
    hstretch hposLast hspaceLast
  let T := sparseCoreRestartTool oracle C depth sparsify
  let L := LastLevelProgram.fixedPointLastLevelTool oracle C
  let next := (algorithm1_rebuild T L P chain first Gnew enc).1
  let Inv (i : ℕ) (s : State) : Prop :=
    (∃ vc ec,
      RebuildSuffixAt R next chain.ℓ chain.g handleBase branchBase first i vc ec
        fmt.limbBits limbs fmt.precision s ∧
      RebuildTablesSeparated handleBase branchBase first P.d heapFloor
        (s.regs 6) vc ec (s.regs 8) limbs) ∧
    heapFloor ≤ s.regs 4 ∧
    s.regs 67 = limbs ∧ s.regs 68 = fmt.precision ∧
    ∀ a < heapFloor, (a < handleBase + first ∨ handleBase + P.d < a) →
      (a < branchBase + first ∨ branchBase + P.d < a) → s.mem a = st.mem a
  let Done (out : State) : Prop :=
    RebuiltCoresAt R next out.mem handleBase branchBase first P.d (out.regs 4) ∧
    out.mem (branchBase + P.d) = next.lastBran ∧ ZeroFrom out.mem (out.regs 4) ∧
    (∃ y : terminal.τ, terminal.rep (out.mem (handleBase + P.d)) (next.lastK, next.lastLSFs)
      y out.mem ∧ ∀ a, terminal.foot (out.mem (handleBase + P.d)) y a → a < out.regs 4) ∧
    (∀ a < heapFloor, (a < handleBase + first ∨ handleBase + P.d < a) →
      (a < branchBase + first ∨ branchBase + P.d < a) → out.mem a = st.mem a)
  let levelCost := fun i =>
    let forest := T.lsfs (next.scState i) 0
    let H := next.G (i + 1)
    280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
      forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
      (129 * limbs + 172) * H.m +
      costs.factor (M i) (N i) * (M i + 1) * P.k + 17 * nextGraphSizeCap (i + 1) + 484
  let terminalCost := multiplier * (L.cost (next.G P.d) + 1) + 20
  obtain ⟨out, c, hrun, hdone, hcost⟩ :=
    rebuildSuffixProgram_runs (w := w) (p := p) (ω := ω) (st := st) (Inv := Inv) (Done := Done)
      levelCost terminalCost hfirstLt.le (by omega) hPword h20
      ⟨⟨vc0, ec0, hin0, by simpa [Function.update_of_ne] using hsep0⟩,
        by simpa [Function.update_of_ne] using hfloor0,
        by simpa [Function.update_of_ne] using h67,
        by simpa [Function.update_of_ne] using h68, fun _ _ _ _ => rfl⟩
      (fun _ _ _ _ hs => hs.1.choose_spec.choose_spec.1.index)
      (fun _ _ _ _ hs => hs.1.choose_spec.choose_spec.1.depth)
      (fun i hi hlt => by
        intro before ω' hs
        obtain ⟨⟨vc, ec, hin, hsep⟩, hfloor, h67b, h68b, hframeb⟩ := hs
        obtain ⟨hMi, hNi, hm, hn, hpos, hforest, hFsub, hVsub, hHsub, hcount, hscanWidth,
          hboundNonneg, hgradBound, hsizeBound⟩ := hmodel i hi hlt
        obtain ⟨hroom, hread⟩ := hreadout ω' i hi hlt vc ec before hin hsep hfloor
        obtain ⟨out, nextVC, nextEC, cost, hr, hin', hsep', hi', hheap, hframeOut, hcost⟩ :=
          rebuildCoreStep_concrete_runs oracle C depth sparsify chain Gnew enc first ⟨i, hlt⟩ hi
            hin hsep hfloor hhFloor hbFloor hdisj h67b hlocal (hcoreImpl i hi hlt vc ec)
            hcopy hsort hentry hMi hNi hm hn hpos hforest hFsub hVsub hHsub hroom hkWord hw9 hcount
            hscanWidth hboundNonneg hgradBound hsizeBound hread
        have h67n : out.regs 67 = limbs :=
          (runs_preserves_above (by decide : 55 ≤ 67) (rebuildCoreStep_writesBelow ..) hr).trans h67b
        have h68n : out.regs 68 = fmt.precision :=
          (runs_preserves_above (by decide : 55 ≤ 68) (rebuildCoreStep_writesBelow ..) hr).trans h68b
        refine ⟨.normal, out, cost, hr, ⟨⟨⟨nextVC, nextEC, hin', ?_⟩, ?_, ?_, ?_, ?_⟩, hi'⟩, hcost⟩
        · simpa [Function.update_of_ne] using hsep'
        · simpa [Function.update_of_ne] using hfloor.trans hheap
        · simpa [Function.update_of_ne] using h67n
        · simpa [Function.update_of_ne] using h68n
        · intro a ha hha hba
          have h1 : a ≠ handleBase + i := by omega
          have h2 : a ≠ branchBase + i := by omega
          exact (hframeOut a (ha.trans_le hfloor) h1 h2).trans (hframeb a ha hha hba))
      (by
        intro before ω' hs
        obtain ⟨⟨vc, ec, hin, _⟩, hfloor, h67b, h68b, hframeb⟩ := hs
        obtain ⟨hmodelLast, hbranchLast⟩ := algorithm1_rebuild_terminal T L P chain first hfirstLt Gnew enc
        have hagree : L.build (next.G P.d)
            (fun e => if e ∈ (next.G P.d).E then next.toTreeChain.chainLen chain.ℓ P.d e else 0) =
            L.build (next.G P.d) (next.toTreeChain.chainLen chain.ℓ P.d) :=
          fixedPointLastLevel_build_congr oracle C hValidLast (fun e he => by simp [he])
        obtain ⟨o, nextSt, c, hr, hp, hcost⟩ :=
          (rebuildTerminalRuntimeStep_suffixAt_triple next chain.ℓ chain.g hin (htermImpl vc ec)
            h67b h68b hLWord hPWord hFour hWidth hstretch hmodelLast hbranchLast hposLast hagree
            (hspaceLast vc ec before hin) (by omega) (by omega) hfirstLt.le hdisj hlocal).runs ω' rfl
        cases o with
        | returned value => exact False.elim hp
        | normal =>
          refine ⟨.normal, nextSt, c, hr, ⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2, ?_⟩, hcost⟩
          intro a ha hha hba
          have h1 : a ≠ before.regs 51 := by rw [hin.handleCursor]; omega
          have h2 : a ≠ before.regs 52 := by rw [hin.branchCursor]; omega
          exact (hp.2 a (ha.trans_le hfloor) h1 h2).trans (hframeb a ha hha hba))
  exact ⟨out, c, hrun, hdone.1, hdone.2.1, hdone.2.2.1, hdone.2.2.2.1, hdone.2.2.2.2, hcost⟩

end MinCostFlow.MinRatio
