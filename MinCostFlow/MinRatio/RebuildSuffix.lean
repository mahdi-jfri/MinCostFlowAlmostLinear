module

public import MinCostFlow.MinRatio.ShiftDeeperLevel
public import MinCostFlow.MinRatio.ShiftLastLevel
public import MinCostFlow.MinRatio.RebuildGuard
public import MinCostFlow.MinRatio.RebuildGradients
import MinCostFlow.MinRatio.RebuildModelSuffix

public import MinCostFlow.MinRatio.RebuildSuffixLoop

/-!
# Iterating the suffix rebuild

Algorithm 1 (page 20) rebuilds the sparse-core levels from the
first changed level to `d - 1`, then builds the terminal forest
collection at level `d`. The loop accounts for the different
initialization cost of each level.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- Load the periodic Rebuild counter arguments from the saved level,
depth, and table bases. Register 59 retains the returned heap. -/
@[expose] def loadRebuildCounterArgs : Stmt :=
  .assign 59 (.reg 4) ;;
  .assign 0 (.reg 55) ;;
  .assign 1 (.reg 57) ;;
  .assign 2 (.reg 58) ;;
  .assign 4 (.reg 56) ;;
  .assign 5 (.reg 60)

/-- The periodic Rebuild counter handoff takes seventeen steps. -/
theorem loadRebuildCounterArgs_runs {w updates restarts rebuilds i d : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hu : st.regs 55 = updates) (hr : st.regs 56 = restarts)
    (hi : st.regs 57 = i) (hd : st.regs 58 = d) (hc : st.regs 60 = rebuilds) :
    ∃ out, Runs w p ω loadRebuildCounterArgs st .normal out 17 ∧
      out.regs 0 = updates ∧ out.regs 1 = i ∧ out.regs 2 = d ∧
      out.regs 4 = restarts ∧ out.regs 5 = rebuilds ∧ out.regs 59 = st.regs 4 ∧
      out.mem = st.mem := by
  let s1 := { st with regs := Function.update st.regs 59 (st.regs 4) }
  let s2 := { s1 with regs := Function.update s1.regs 0 updates }
  let s3 := { s2 with regs := Function.update s2.regs 1 i }
  let s4 := { s3 with regs := Function.update s3.regs 2 d }
  let s5 := { s4 with regs := Function.update s4.regs 4 restarts }
  let s6 := { s5 with regs := Function.update s5.regs 5 rebuilds }
  have h1 : Runs w p ω (.assign 59 (.reg 4)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have h2 : Runs w p ω (.assign 0 (.reg 55)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hu, Function.update_of_ne, s1], rfl, rfl, rfl⟩
  have h3 : Runs w p ω (.assign 1 (.reg 57)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hi, Function.update_of_ne, s1, s2], rfl, rfl, rfl⟩
  have h4 : Runs w p ω (.assign 2 (.reg 58)) s3 .normal s4 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hd, Function.update_of_ne, s1, s2, s3], rfl, rfl, rfl⟩
  have h5 : Runs w p ω (.assign 4 (.reg 56)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hr, Function.update_of_ne, s1, s2, s3, s4], rfl, rfl, rfl⟩
  have h6 : Runs w p ω (.assign 5 (.reg 60)) s5 .normal s6 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hc, Function.update_of_ne, s1, s2, s3, s4, s5], rfl, rfl, rfl⟩
  refine ⟨s6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s1, 2, 14, h1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 2, 11, h2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 2, 8, h3,
          runs_seq_iff.mpr (Or.inr ⟨s4, 2, 5, h4,
            runs_seq_iff.mpr (Or.inr ⟨s5, 2, 2, h5, h6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  all_goals simp [s6, s5, s4, s3, s2, s1, Function.update_of_ne]

/-- Rebuild the suffix and record the periodic rebuild in the level
counters (Algorithm 1, page 20). -/
@[expose] def periodicRebuildWithCounters (level terminal : Stmt) : Stmt :=
  rebuildSuffixProgram level terminal ;; loadRebuildCounterArgs ;; recordPeriodicRebuild ;; .assign 4 (.reg 59)

/-- The three counter tables match the model after the suffix build, and
other memory retains the values written by that build. -/
theorem periodicRebuildWithCounters_runs {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : Fin P.d) (G : MGraph) (enc : ℕ)
    {w updates restarts rebuilds suffixCost : ℕ} {p : Program} {initial rebuilt : State} {level terminal : Stmt} {ω : ℕ → Bool}
    (hSuffix : Runs w p ω (rebuildSuffixProgram level terminal) initial .normal rebuilt suffixCost)
    (hLevelRegs : writesBelow 55 level = true) (hTerminalRegs : writesBelow 55 terminal = true)
    (hUpdates : initial.regs 55 = updates) (hRestarts : initial.regs 56 = restarts)
    (hLevel : initial.regs 57 = i.val) (hDepth : initial.regs 58 = P.d)
    (hRebuilds : initial.regs 60 = rebuilds)
    (hu : ∀ j : Fin P.d, rebuilt.mem (updates + j.val) = chain.updCount j.val)
    (hrr : ∀ j : Fin P.d, rebuilt.mem (restarts + j.val) = chain.curRestarts j.val)
    (hreb : ∀ j : Fin (P.d + 1), rebuilt.mem (rebuilds + j.val) = chain.rebuildCount j.val)
    (hur : updates + P.d ≤ restarts ∨ restarts + P.d ≤ updates)
    (huc : updates + P.d ≤ rebuilds ∨ rebuilds + P.d + 1 ≤ updates)
    (hrc : restarts + P.d ≤ rebuilds ∨ rebuilds + P.d + 1 ≤ restarts)
    (hub : updates + P.d < 2 ^ w) (hrb : restarts + P.d < 2 ^ w)
    (hcb : rebuilds + P.d < 2 ^ w) (hw : 1 < 2 ^ w)
    (hnext : chain.rebuildCount i.val + 1 < 2 ^ w) :
    let next := (algorithm1_rebuild T L P chain i.val G enc).1
    ∃ out cost, Runs w p ω (periodicRebuildWithCounters level terminal) initial .normal out cost ∧
      cost ≤ suffixCost + 28 * (P.d - i.val) + 54 ∧ out.regs 4 = rebuilt.regs 4 ∧
      (∀ j : Fin P.d, out.mem (updates + j.val) = next.updCount j.val) ∧
      (∀ j : Fin P.d, out.mem (restarts + j.val) = next.curRestarts j.val) ∧
      (∀ j : Fin (P.d + 1), out.mem (rebuilds + j.val) = next.rebuildCount j.val) ∧
      ∀ a, (a < updates + i.val ∨ updates + P.d ≤ a) →
        (a < restarts + i.val ∨ restarts + P.d ≤ a) →
        a ≠ rebuilds + i.val → out.mem a = rebuilt.mem a := by
  have hkeepArgs (r : ℕ) (hr : 55 ≤ r) : rebuilt.regs r = initial.regs r := by
    apply runs_preserves_above hr _ hSuffix
    simp [rebuildSuffixProgram, forRange, forUp, writesBelow, hLevelRegs, hTerminalRegs]
  obtain ⟨ready, hs, hb, hi, hend, hrbase, hcbase, hh, hmem⟩ :=
    loadRebuildCounterArgs_runs (p := p) (ω := ω)
      ((hkeepArgs 55 (by decide)).trans hUpdates) ((hkeepArgs 56 (by decide)).trans hRestarts)
      ((hkeepArgs 57 (by decide)).trans hLevel) ((hkeepArgs 58 (by decide)).trans hDepth)
      ((hkeepArgs 60 (by decide)).trans hRebuilds)
  obtain ⟨out, c, hr, hc, _, hu', hrs, hrc', hf⟩ :=
    recordPeriodicRebuild_runs (L := L) (ω := ω) chain i G enc hb hi hend hrbase hcbase
      (hmem.symm ▸ hu) (hmem.symm ▸ hrr) (hmem.symm ▸ hreb) hur huc hrc hub hrb hcb hw hnext
  have hkeep : out.regs 59 = ready.regs 59 :=
    runs_preserves_above (s := recordPeriodicRebuild) (by decide : 59 ≤ 59) rfl hr
  let final := { out with regs := Function.update out.regs 4 (rebuilt.regs 4) }
  have hrestore : Runs w p ω (.assign 4 (.reg 59)) out .normal final 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hkeep, hh], rfl, rfl, rfl⟩
  have htail : Runs w p ω (recordPeriodicRebuild ;; .assign 4 (.reg 59))
      ready .normal final (c + 3) :=
    runs_seq_iff.mpr (Or.inr ⟨out, c, 2, hr, hrestore, by omega⟩)
  exact ⟨final, suffixCost + c + 22,
    runs_seq_iff.mpr (Or.inr ⟨rebuilt, suffixCost, c + 21, hSuffix,
      runs_seq_iff.mpr (Or.inr ⟨ready, 17, c + 3, hs, htail, by omega⟩), by omega⟩),
    by omega, by simp [final], hu', hrs, hrc', by simpa only [hmem] using hf⟩

/-- Initialize and record the terminal level of the Rebuild suffix with runtime numeric arguments. -/
@[expose] def rebuildTerminalRuntimeStep (init : ℕ) : Stmt :=
  rebuildLastLevelRuntime init ;; storeRebuiltLevel


/-- Installing the terminal collection retains the model state and its
allocation, with a separate handle and branch descriptor below the heap. -/
theorem rebuildTerminalRuntimeStep_exact_runs {w L init graph lengths heap vCap eCap multiplier stretchPrecision handleCell branchCell : ℕ}
    {fmt : Num.Format w} {tool : LastLevelTool} {G : MGraph}
    {allocation : ℕ → List ℕ → ℕ} {R : DSRep (ℕ × (ℕ → LSF))}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier stretchPrecision allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hh : st.regs 4 = heap)
    (hL : st.regs 67 = L) (hP : st.regs 68 = fmt.precision)
    (hLWord : L < 2 ^ w) (hPWord : fmt.precision < 2 ^ w)
    (hFour : fmt.limbBits = 4) (hWidth : fmt.precision ≤ 4 * L)
    (ℓ : ℕ → ℝ) (hG : DynGraphAt st.mem graph vCap eCap G)
    (hgraph : graph + dynGraphSize vCap eCap ≤ heap)
    (hLenRoom : lengths + eCap * L ≤ heap)
    (hℓ : EdgeValuesAt st.mem lengths fmt.limbBits L fmt.precision G.E ℓ)
    (hst : ∀ e ∈ G.E, 2 * (2 : ℝ)^stretchPrecision * lastLevelStretchBound G ℓ e <
      Num.capacity fmt.limbBits L)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 1 [graph, lengths, L, fmt.precision, heap] < 2 ^ w)
    (hAgreement : tool.build G (fun e => if e ∈ G.E then ℓ e else 0) = tool.build G ℓ)
    (hhandleCell : st.regs 51 = handleCell) (hbranchCell : st.regs 52 = branchCell)
    (hne : handleCell ≠ branchCell) (hhBelow : handleCell < heap) (hbBelow : branchCell < heap) :
    ∃ out ret cost y,
      Runs w p ω (rebuildTerminalRuntimeStep init) st .normal out cost ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧ out.regs 4 = ret ∧
      R.rep heap (tool.build G ℓ) y out.mem ∧ ZeroFrom out.mem ret ∧
      (∀ a, R.foot heap y a → heap ≤ a ∧ a < ret) ∧
      (∀ a < heap, a ≠ handleCell → a ≠ branchCell → out.mem a = st.mem a) ∧
      heap ≤ ret ∧ cost + R.phi heap y out.mem ≤ multiplier * (tool.cost G + 1) + 20 := by
  have hbuild := rebuildLastLevelRuntime_tables_runs (ω := ω) himpl hg hl hh hL hP hLWord hPWord hFour hWidth ℓ hG hgraph hLenRoom hℓ hst hpos hz hroom
  dsimp only at hbuild
  rw [hAgreement] at hbuild
  obtain ⟨mid, ret, c, y, hr, _, hhandle, hret, hrep, _, hframe, hcost⟩ := hbuild
  have hregsKeep (r : ℕ) (hrBound : 51 ≤ r) : mid.regs r = st.regs r :=
    runs_preserves_above (s := rebuildLastLevelRuntime init) hrBound rfl hr
  have hfoot (a : ℕ) (ha : R.foot heap y a) : heap ≤ a ∧ a < ret :=
    (hframe.2.2.2.2 a ha).resolve_left id
  obtain ⟨out, hs, hcell, hbranch, hrep', hphi, hmem, hregs, _⟩ :=
    storeRebuiltLevel_preserves_tool_runs (ω := ω) himpl.1
      ((hregsKeep 51 (by decide)).trans hhandleCell) ((hregsKeep 52 (by decide)).trans hbranchCell)
      hne (hhandle.symm ▸ hhBelow) (hhandle.symm ▸ hbBelow)
      (fun a ha => hhandle.symm ▸ (hfoot a (hhandle ▸ ha)).1) (hhandle.symm ▸ hrep)
  have houtHandle : out.regs 3 = heap := hregs ▸ hhandle
  refine ⟨out, ret, c + 8, y, runs_seq_iff.mpr (Or.inr ⟨mid, c, 7, hr, hs, by omega⟩),
    hcell.trans houtHandle, hbranch, hregs ▸ hret, houtHandle ▸ hrep', ?_, hfoot, ?_, hframe.1, ?_⟩
  · intro a ha
    have hlo := hframe.1
    exact (hmem a (by omega) (by omega)).trans (hframe.2.2.1 a ha)
  · intro a ha hhc hbc
    exact (hmem a hhc hbc).trans (hframe.2.2.2.1 a ha (by simp))
  · rw [houtHandle, hhandle] at hphi
    omega


/-- Charge a terminal rebuild using the multiplier for its particular
graph and limb count, including the call and descriptor writes. -/
theorem rebuildTerminalRuntimeCost_le {tool : LastLevelTool} {params : LastLevelParams}
    (hTool : tool.IsSpec params) (G : MGraph) (lengths : ℕ → ℝ) (hG : G.IsValid)
    (hLengths : ∀ e ∈ G.E, 0 < lengths e) (multiplier cost potential : ℕ)
    (hcost : cost + potential ≤ multiplier * (tool.cost G + 1) + 20) :
    ((cost + potential : ℕ) : ℝ) ≤
      (multiplier : ℝ) * (params.c_last * ((G.m : ℝ) + 1) ^ 2 *
        (Real.log ((G.m : ℝ) + (G.n : ℝ) + 2)) ^ params.p_last + 1) + 20 := by
  have hmodel := (hTool G lengths hG hLengths).2.2.2.2
  calc
    ((cost + potential : ℕ) : ℝ) ≤ ((multiplier * (tool.cost G + 1) + 20 : ℕ) : ℝ) := by
      exact_mod_cast hcost
    _ ≤ _ := by
      push_cast
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left (add_le_add_left hmodel 1) (Nat.cast_nonneg multiplier)) 20

/-- Rebuilding at level `d` builds the terminal collection from the
new graph and the inherited lengths, and selects its first branch. -/
theorem rebuildTerminal_model (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (chain : ChainState T P) (G : MGraph) (enc : ℕ) :
    let next := (algorithm1_rebuild T L P chain P.d G enc).1
    (next.lastK, next.lastLSFs) = L.build G (chain.toTreeChain.chainLen chain.ℓ P.d) ∧
      next.lastBran = 0 := by
  simp [algorithm1_rebuild]

/-- The installed terminal descriptor and collection agree with the exact
model of the direct terminal Rebuild (Algorithm 1, page 20). -/
theorem rebuildTerminalRuntimeStep_model_runs {w L init graph lengths heap vCap eCap multiplier stretchPrecision handleCell branchCell : ℕ}
    {fmt : Num.Format w} {tool : LastLevelTool} {G : MGraph}
    {T : SparseCoreRestartTool} {P : ChainParams}
    (chain : ChainState T P) (enc : ℕ)
    {allocation : ℕ → List ℕ → ℕ} {R : DSRep (ℕ × (ℕ → LSF))}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier stretchPrecision allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hh : st.regs 4 = heap)
    (ℓ : ℕ → ℝ) (hLen : ℓ = chain.toTreeChain.chainLen chain.ℓ P.d)
    (hL : st.regs 67 = L) (hP : st.regs 68 = fmt.precision)
    (hLWord : L < 2 ^ w) (hPWord : fmt.precision < 2 ^ w)
    (hFour : fmt.limbBits = 4) (hWidth : fmt.precision ≤ 4 * L)
    (hG : DynGraphAt st.mem graph vCap eCap G)
    (hgraph : graph + dynGraphSize vCap eCap ≤ heap)
    (hLenRoom : lengths + eCap * L ≤ heap)
    (hℓ : EdgeValuesAt st.mem lengths fmt.limbBits L fmt.precision G.E ℓ)
    (hst : ∀ e ∈ G.E, 2 * (2 : ℝ)^stretchPrecision *
      lastLevelStretchBound G (chain.toTreeChain.chainLen chain.ℓ P.d) e <
        Num.capacity fmt.limbBits L)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 1 [graph, lengths, L, fmt.precision, heap] < 2 ^ w)
    (hSupport : ∀ e ∉ G.E, ℓ e = 0)
    (hhandleCell : st.regs 51 = handleCell) (hbranchCell : st.regs 52 = branchCell)
    (hne : handleCell ≠ branchCell) (hhBelow : handleCell < heap) (hbBelow : branchCell < heap) :
    let next := (algorithm1_rebuild T tool P chain P.d G enc).1
    ∃ out ret cost y,
      Runs w p ω (rebuildTerminalRuntimeStep init) st .normal out cost ∧
      out.mem handleCell = heap ∧ out.mem branchCell = next.lastBran ∧ out.regs 4 = ret ∧
      R.rep heap (next.lastK, next.lastLSFs) y out.mem ∧ ZeroFrom out.mem ret ∧
      (∀ a, R.foot heap y a → heap ≤ a ∧ a < ret) ∧
      cost + R.phi heap y out.mem ≤ multiplier * (tool.cost G + 1) + 20 := by
  have hmask : (fun e => if e ∈ G.E then ℓ e else 0) = ℓ := by
    funext e
    by_cases he : e ∈ G.E <;> simp [he, hSupport]
  have hr := rebuildTerminalRuntimeStep_exact_runs (ω := ω) himpl hg hl hh hL hP hLWord hPWord hFour hWidth ℓ hG hgraph hLenRoom hℓ (hLen.symm ▸ hst) hpos hz
    hroom (congrArg (tool.build G) hmask) hhandleCell hbranchCell hne hhBelow hbBelow
  dsimp only
  obtain ⟨he, hb⟩ := rebuildTerminal_model T tool P chain G enc
  rw [he, hb, ← hLen]
  obtain ⟨out, ret, cost, y, hrun, hhandle, hbranch, hheap, hrep, hfree, hfoot, _, _, hcost⟩ := hr
  exact ⟨out, ret, cost, y, hrun, hhandle, hbranch, hheap, hrep, hfree, hfoot, hcost⟩

/-- Finish the Rebuild suffix by installing its terminal collection
and retaining the completed interval of sparse cores. -/
theorem rebuildTerminalRuntimeStep_suffixAt_runs
    {w L init vCap eCap multiplier stretchPrecision first handleBase branchBase : ℕ}
    {fmt : Num.Format w} {tool : LastLevelTool}
    {T : SparseCoreRestartTool} {P : ChainParams}
    (chain : ChainState T P) (len grad : ℕ → ℝ)
    {allocation : ℕ → List ℕ → ℕ} {R : DSRep (ℕ × (ℕ → LSF))} {core : DSRep T.State}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (hin : RebuildSuffixAt core chain len grad handleBase branchBase first P.d
      vCap eCap fmt.limbBits L fmt.precision st)
    (himpl : R.Implements w p init op
      (lastLevelRuntimeMachineContract fmt L tool (chain.G P.d) vCap eCap multiplier stretchPrecision allocation))
    (hL : st.regs 67 = L) (hP : st.regs 68 = fmt.precision)
    (hLWord : L < 2 ^ w) (hPWord : fmt.precision < 2 ^ w)
    (hFour : fmt.limbBits = 4) (hWidth : fmt.precision ≤ 4 * L)
    (hst : ∀ e ∈ (chain.G P.d).E, 2 * (2 : ℝ)^stretchPrecision *
      lastLevelStretchBound (chain.G P.d) (chain.toTreeChain.chainLen len P.d) e <
        Num.capacity fmt.limbBits L)
    (hmodel : (chain.lastK, chain.lastLSFs) =
      tool.build (chain.G P.d) (chain.toTreeChain.chainLen len P.d))
    (hbranch : chain.lastBran = 0)
    (hpos : ∀ e ∈ (chain.G P.d).E, 0 < chain.toTreeChain.chainLen len P.d e)
    (hAgreement :
      tool.build (chain.G P.d) (fun e => if e ∈ (chain.G P.d).E
        then chain.toTreeChain.chainLen len P.d e else 0) =
      tool.build (chain.G P.d) (chain.toTreeChain.chainLen len P.d))
    (hroom : st.regs 4 + allocation 1 [st.regs 6, st.regs 7, L, fmt.precision, st.regs 4] < 2 ^ w)
    (hhBelow : handleBase + P.d < st.regs 4) (hbBelow : branchBase + P.d < st.regs 4)
    (hfirst : first ≤ P.d)
    (hsep : handleBase + P.d < branchBase + first ∨ branchBase + P.d < handleBase + first)
    (hlocal : core.Local) :
    ∃ out cost y, Runs w p ω (rebuildTerminalRuntimeStep init) st .normal out cost ∧
      out.mem (handleBase + P.d) = st.regs 4 ∧
      out.mem (branchBase + P.d) = chain.lastBran ∧
      R.rep (st.regs 4) (chain.lastK, chain.lastLSFs) y out.mem ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ a, R.foot (st.regs 4) y a → st.regs 4 ≤ a ∧ a < out.regs 4) ∧
      RebuiltCoresAt core chain out.mem handleBase branchBase first P.d (out.regs 4) ∧
      (∀ a < st.regs 4, a ≠ handleBase + P.d → a ≠ branchBase + P.d →
        out.mem a = st.mem a) ∧
      cost + R.phi (st.regs 4) y out.mem ≤ multiplier * (tool.cost (chain.G P.d) + 1) + 20 := by
  have hne : handleBase + P.d ≠ branchBase + P.d := by
    rcases hsep with h | h <;> omega
  obtain ⟨out, ret, cost, y, hr, hh, hb, hout, hrep, hfree, hfoot, hframe, hheap, hcost⟩ :=
    rebuildTerminalRuntimeStep_exact_runs (ω := ω) himpl rfl rfl rfl hL hP hLWord hPWord hFour hWidth _ hin.graph hin.graphEnd
      hin.lengthsEnd hin.lengths hst hpos hin.free hroom hAgreement hin.handleCursor hin.branchCursor
      hne hhBelow hbBelow
  rw [← hout] at hfree hfoot hheap
  have hkeep := hin.installed.preserve hlocal hheap hhBelow.le hbBelow.le
    (by
      intro j hj hd
      rcases hsep with h | h <;> exact ⟨by omega, by omega, by omega, by omega⟩)
    (Or.inl le_rfl) (Or.inr le_rfl) hframe
  exact ⟨out, cost, y, hr, hh, hb.trans hbranch.symm, hmodel.symm ▸ hrep, hfree, hfoot, hkeep, hframe, hcost⟩

/-- The terminal call supplies the represented collection and the local
memory frame required by the Init loop. -/
theorem rebuildTerminalRuntimeStep_suffixAt_triple
    {w L init vCap eCap multiplier stretchPrecision first handleBase branchBase : ℕ}
    {fmt : Num.Format w} {tool : LastLevelTool}
    {T : SparseCoreRestartTool} {P : ChainParams}
    (chain : ChainState T P) (len grad : ℕ → ℝ)
    {allocation : ℕ → List ℕ → ℕ} {R : DSRep (ℕ × (ℕ → LSF))} {core : DSRep T.State}
    {p : Program} {op : ℕ → ℕ} {st : State}
    (hin : RebuildSuffixAt core chain len grad handleBase branchBase first P.d
      vCap eCap fmt.limbBits L fmt.precision st)
    (himpl : R.Implements w p init op
      (lastLevelRuntimeMachineContract fmt L tool (chain.G P.d) vCap eCap multiplier stretchPrecision allocation))
    (hL : st.regs 67 = L) (hP : st.regs 68 = fmt.precision)
    (hLWord : L < 2 ^ w) (hPWord : fmt.precision < 2 ^ w)
    (hFour : fmt.limbBits = 4) (hWidth : fmt.precision ≤ 4 * L)
    (hst : ∀ e ∈ (chain.G P.d).E, 2 * (2 : ℝ)^stretchPrecision *
      lastLevelStretchBound (chain.G P.d) (chain.toTreeChain.chainLen len P.d) e <
        Num.capacity fmt.limbBits L)
    (hmodel : (chain.lastK, chain.lastLSFs) =
      tool.build (chain.G P.d) (chain.toTreeChain.chainLen len P.d))
    (hbranch : chain.lastBran = 0)
    (hpos : ∀ e ∈ (chain.G P.d).E, 0 < chain.toTreeChain.chainLen len P.d e)
    (hAgreement :
      tool.build (chain.G P.d) (fun e => if e ∈ (chain.G P.d).E
        then chain.toTreeChain.chainLen len P.d e else 0) =
      tool.build (chain.G P.d) (chain.toTreeChain.chainLen len P.d))
    (hroom : st.regs 4 + allocation 1 [st.regs 6, st.regs 7, L, fmt.precision, st.regs 4] < 2 ^ w)
    (hhBelow : handleBase + P.d < st.regs 4) (hbBelow : branchBase + P.d < st.regs 4)
    (hfirst : first ≤ P.d)
    (hsep : handleBase + P.d < branchBase + first ∨ branchBase + P.d < handleBase + first)
    (hlocal : core.Local) :
    Triple w p (fun current => current = st) (rebuildTerminalRuntimeStep init)
      (normalPost fun out =>
        (RebuiltCoresAt core chain out.mem handleBase branchBase first P.d (out.regs 4) ∧
          out.mem (branchBase + P.d) = chain.lastBran ∧ ZeroFrom out.mem (out.regs 4) ∧
          ∃ y : R.τ, R.rep (out.mem (handleBase + P.d)) (chain.lastK, chain.lastLSFs)
            y out.mem ∧ ∀ a, R.foot (out.mem (handleBase + P.d)) y a → a < out.regs 4) ∧
        ∀ a < st.regs 4, a ≠ st.regs 51 → a ≠ st.regs 52 → out.mem a = st.mem a)
      (fun _ => multiplier * (tool.cost (chain.G P.d) + 1) + 20) := by
  intro current ω heq
  subst current
  obtain ⟨out, cost, y, hr, hh, hb, hrep, hz, hfoot, hcores, hf, hcost⟩ :=
    rebuildTerminalRuntimeStep_suffixAt_runs (ω := ω) chain len grad hin himpl hL hP hLWord hPWord hFour hWidth
      hst hmodel hbranch hpos hAgreement hroom hhBelow hbBelow hfirst hsep hlocal
  refine ⟨.normal, out, cost, hr, ⟨⟨hcores, hb, hz, y, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [hh]
    exact hrep
  · rw [hh]
    exact fun a ha => (hfoot a ha).2
  · simpa only [hin.handleCursor, hin.branchCursor] using hf
  · exact (Nat.le_add_right _ _).trans hcost

/-- Iterate the core rebuild body, then install the terminal collection. -/
@[expose] def rebuildChainSuffix (init read forestOp copy sort cell terminalInit : ℕ) : Stmt :=
  rebuildSuffixProgram (rebuildCoreStep init read forestOp copy sort cell)
    (rebuildTerminalRuntimeStep terminalInit)

/-- The concrete suffix keeps the saved counter arguments. -/
theorem rebuildChainSuffix_writesBelow (init read forestOp copy sort cell terminalInit : ℕ) :
    writesBelow 55 (rebuildChainSuffix init read forestOp copy sort cell terminalInit) = true := rfl

/-- The Rebuild suffix (Algorithm 1, page 20) iterates the concrete core
body and installs the terminal tool, with the summed cost of its runs. -/
theorem rebuildChainSuffix_runs {w first last init read forestOp copy sort cell terminalInit : ℕ} {p : Program}
    {Inv : ℕ → State → Prop} {Done : State → Prop}
    {ω : ℕ → Bool} {st : State} (cost : ℕ → ℕ) (terminalCost : ℕ)
    (horder : first ≤ last) (hw : 1 < 2 ^ w) (hword : last < 2 ^ w)
    (hfirst : st.regs 20 = first)
    (hin : Inv first { st with regs := Function.update st.regs 19 first })
    (hindex : ∀ i current, first ≤ i → i ≤ last → Inv i current → current.regs 19 = i)
    (hstop : ∀ i current, first ≤ i → i ≤ last → Inv i current → current.regs 21 = last)
    (hlevel : ∀ i, first ≤ i → i < last → Triple w p (Inv i) (rebuildCoreStep init read forestOp copy sort cell)
      (normalPost fun next =>
        Inv (i + 1) { next with regs := Function.update next.regs 19 (i + 1) } ∧
          next.regs 19 = i) (fun _ => cost i))
    (hterminal : Triple w p (Inv last) (rebuildTerminalRuntimeStep terminalInit) (normalPost Done) (fun _ => terminalCost)) :
    ∃ out c, Runs w p ω (rebuildChainSuffix init read forestOp copy sort cell terminalInit) st .normal out c ∧ Done out ∧
      c ≤ rangeCost cost first last + (last - first) * 9 + terminalCost + 8 :=
  rebuildSuffixProgram_runs cost terminalCost horder hw hword hfirst hin hindex hstop hlevel hterminal

/-- At the start of the Rebuild loop the replacement graph and the
inherited number tables form the first suffix invariant. -/
theorem rebuildChainSuffix_entry
    {T : SparseCoreRestartTool} {P : ChainParams} {L : LastLevelTool}
    (chain : ChainState T P) (first : Fin P.d) (Gnew : MGraph) (enc : ℕ)
    {core : DSRep T.State} {handleBase branchBase vc ec h limbs precision : ℕ} {st : State}
    (hd : st.regs 21 = P.d)
    (hh : st.regs 51 = handleBase + first.val) (hb : st.regs 52 = branchBase + first.val)
    (hG : DynGraphAt st.mem (st.regs 6) vc ec Gnew)
    (hlen : EdgeValuesAt st.mem (st.regs 7) h limbs precision Gnew.E
      (chain.toTreeChain.chainLen chain.ℓ first.val))
    (hgrad : EdgeValuesAt st.mem (st.regs 8) h limbs precision Gnew.E
      (chain.toTreeChain.chainGrad chain.g first.val))
    (hgEnd : st.regs 6 + dynGraphSize vc ec ≤ st.regs 4)
    (hlEnd : st.regs 7 + ec * limbs ≤ st.regs 4)
    (hnEnd : st.regs 8 + ec * limbs ≤ st.regs 4) (hz : ZeroFrom st.mem (st.regs 4)) :
    let next := (algorithm1_rebuild T L P chain first.val Gnew enc).1
    RebuildSuffixAt core next chain.ℓ chain.g handleBase branchBase first.val first.val
      vc ec h limbs precision { st with regs := Function.update st.regs 19 first.val } := by
  dsimp only
  obtain ⟨hgraph, hl, hg⟩ := algorithm1_rebuild_entry T L P chain first Gnew enc
  have hcore := rebuiltCoresAt_empty core (algorithm1_rebuild T L P chain first.val Gnew enc).1
    st.mem handleBase branchBase first.val (st.regs 4)
  constructor <;> dsimp only <;> simp (config := { decide := true }) only
    [Function.update_self, Function.update_of_ne, ne_eq, hd, hh, hb, hgraph, hl, hg]
  all_goals assumption

/-- Iterate periodic Rebuild with the concrete suffix invariant and
install the model's terminal collection. The core step supplies its
successor invariant at each nonterminal level. -/
theorem rebuildChainSuffix_model_runs
    {T : SparseCoreRestartTool} {P : ChainParams} {L : LastLevelTool}
    (chain : ChainState T P) (first : Fin P.d) (Gnew : MGraph) (enc : ℕ)
    {w init read forestOp limbs copy sort cell terminalInit multiplier stretchPrecision handleBase branchBase : ℕ}
    {fmt : Num.Format w} {vc ec cost : ℕ → ℕ}
    {core : DSRep T.State} {terminal : DSRep (ℕ × (ℕ → LSF))}
    {allocation : ℕ → List ℕ → ℕ} {p : Program} {op : ℕ → ℕ}
    {st : State} {ω : ℕ → Bool}
    (hw : 1 < 2 ^ w) (hword : P.d < 2 ^ w) (hfirst : st.regs 20 = first.val)
    (hLWord : limbs < 2 ^ w) (hPWord : fmt.precision < 2 ^ w)
    (hFour : fmt.limbBits = 4) (hWidth : fmt.precision ≤ 4 * limbs)
    (hlocal : core.Local)
    (hsep : handleBase + P.d < branchBase + first.val ∨ branchBase + P.d < handleBase + first.val) :
    let next := (algorithm1_rebuild T L P chain first.val Gnew enc).1
    let Inv := fun i => RebuildSuffixAt core next chain.ℓ chain.g handleBase branchBase first.val i
      (vc i) (ec i) fmt.limbBits limbs fmt.precision
    let termCost := multiplier * (L.cost (next.G P.d) + 1) + 20
    Inv first.val { st with regs := Function.update st.regs 19 first.val } →
    (∀ i, first.val ≤ i → i < P.d →
      Triple w p (Inv i) (rebuildCoreStep init read forestOp copy sort cell)
        (normalPost fun out =>
          Inv (i + 1) { out with regs := Function.update out.regs 19 (i + 1) } ∧
            out.regs 19 = i) (fun _ => cost i)) →
    terminal.Implements w p terminalInit op
      (lastLevelRuntimeMachineContract fmt limbs L (next.G P.d) (vc P.d) (ec P.d) multiplier stretchPrecision allocation) →
    (∀ e ∈ (next.G P.d).E, 0 < next.toTreeChain.chainLen chain.ℓ P.d e) →
    L.build (next.G P.d) (fun e => if e ∈ (next.G P.d).E
      then next.toTreeChain.chainLen chain.ℓ P.d e else 0) =
      L.build (next.G P.d) (next.toTreeChain.chainLen chain.ℓ P.d) →
    (∀ e ∈ (next.G P.d).E, 2 * (2 : ℝ)^stretchPrecision *
      lastLevelStretchBound (next.G P.d) (next.toTreeChain.chainLen chain.ℓ P.d) e <
        Num.capacity fmt.limbBits limbs) →
    (∀ s, Inv P.d s →
      s.regs 67 = limbs ∧ s.regs 68 = fmt.precision ∧
      s.regs 4 + allocation 1 [s.regs 6, s.regs 7, limbs, fmt.precision, s.regs 4] < 2 ^ w ∧
      handleBase + P.d < s.regs 4 ∧ branchBase + P.d < s.regs 4) →
    ∃ out c, Runs w p ω (rebuildChainSuffix init read forestOp copy sort cell terminalInit)
        st .normal out c ∧
      RebuiltCoresAt core next out.mem handleBase branchBase first.val P.d (out.regs 4) ∧
      out.mem (branchBase + P.d) = next.lastBran ∧ ZeroFrom out.mem (out.regs 4) ∧
      (∃ y : terminal.τ, terminal.rep (out.mem (handleBase + P.d)) (next.lastK, next.lastLSFs)
        y out.mem ∧ ∀ a, terminal.foot (out.mem (handleBase + P.d)) y a → a < out.regs 4) ∧
      c ≤ rangeCost cost first.val P.d + (P.d - first.val) * 9 + termCost + 8 := by
  dsimp only
  intro hin hlevel himpl hpos hagreement hstretch hspace
  obtain ⟨hmodel, hbranch⟩ := algorithm1_rebuild_terminal T L P chain first.val first.isLt Gnew enc
  let next := (algorithm1_rebuild T L P chain first.val Gnew enc).1
  let Done (s : State) :=
    RebuiltCoresAt core next s.mem handleBase branchBase first.val P.d (s.regs 4) ∧
    s.mem (branchBase + P.d) = next.lastBran ∧ ZeroFrom s.mem (s.regs 4) ∧
    ∃ y : terminal.τ, terminal.rep (s.mem (handleBase + P.d)) (next.lastK, next.lastLSFs) y s.mem ∧
      ∀ a, terminal.foot (s.mem (handleBase + P.d)) y a → a < s.regs 4
  have hterminal := rebuildChainSuffix_runs (ω := ω) (terminalInit := terminalInit)
    (Done := Done) cost (multiplier * (L.cost (next.G P.d) + 1) + 20)
    first.isLt.le hw hword hfirst hin
    (fun _ _ _ _ h => h.index) (fun _ _ _ _ h => h.depth) hlevel
  obtain ⟨out, c, hr, ⟨hcores, hb, hz, hrep⟩, hc⟩ := hterminal (by
    intro s tape hs
    obtain ⟨hL, hP, hroom, hh, hb⟩ := hspace s hs
    obtain ⟨o, out, c, hr, hp, hc⟩ :=
      (rebuildTerminalRuntimeStep_suffixAt_triple _ chain.ℓ chain.g hs himpl hL hP hLWord
        hPWord hFour hWidth hstretch hmodel hbranch hpos hagreement hroom hh hb first.isLt.le hsep hlocal).runs
        tape rfl
    cases o with
    | returned value => exact False.elim hp
    | normal => exact ⟨.normal, out, c, hr, hp.1, hc⟩)
  exact ⟨out, c, hr, hcores, hb, hz, hrep, hc⟩

/-- Run the concrete Rebuild suffix and then record the periodic
counter changes at its starting level (Algorithm 1, page 20). -/
@[expose] def rebuildChainWithCounters (init read forestOp copy sort cell terminalInit : ℕ) : Stmt :=
  periodicRebuildWithCounters (rebuildCoreStep init read forestOp copy sort cell)
    (rebuildTerminalRuntimeStep terminalInit)

/-- Record the model counters after a run of the concrete Rebuild suffix.
The free heap and memory outside the counter writes are retained. -/
theorem rebuildChainWithCounters_runs
    {T : SparseCoreRestartTool} {L : LastLevelTool} {P : ChainParams}
    (chain : ChainState T P) (i : Fin P.d) (G : MGraph) (enc : ℕ)
    {w updates restarts rebuilds suffixCost init read forestOp copy sort cell terminalInit : ℕ}
    {p : Program} {initial rebuilt : State} {ω : ℕ → Bool}
    (hr : Runs w p ω (rebuildChainSuffix init read forestOp copy sort cell terminalInit)
      initial .normal rebuilt suffixCost)
    (hUpdates : initial.regs 55 = updates) (hRestarts : initial.regs 56 = restarts)
    (hLevel : initial.regs 57 = i.val) (hDepth : initial.regs 58 = P.d)
    (hRebuilds : initial.regs 60 = rebuilds)
    (hu : ∀ j : Fin P.d, rebuilt.mem (updates + j.val) = chain.updCount j.val)
    (hrr : ∀ j : Fin P.d, rebuilt.mem (restarts + j.val) = chain.curRestarts j.val)
    (hreb : ∀ j : Fin (P.d + 1), rebuilt.mem (rebuilds + j.val) = chain.rebuildCount j.val)
    (hur : updates + P.d ≤ restarts ∨ restarts + P.d ≤ updates)
    (huc : updates + P.d ≤ rebuilds ∨ rebuilds + P.d + 1 ≤ updates)
    (hrc : restarts + P.d ≤ rebuilds ∨ rebuilds + P.d + 1 ≤ restarts)
    (hub : updates + P.d < 2 ^ w) (hrb : restarts + P.d < 2 ^ w)
    (hcb : rebuilds + P.d < 2 ^ w) (hw : 1 < 2 ^ w)
    (hnext : chain.rebuildCount i.val + 1 < 2 ^ w) :
    let next := (algorithm1_rebuild T L P chain i.val G enc).1
    ∃ out cost,
      Runs w p ω (rebuildChainWithCounters init read forestOp copy sort cell terminalInit)
        initial .normal out cost ∧
      cost ≤ suffixCost + 28 * (P.d - i.val) + 54 ∧ out.regs 4 = rebuilt.regs 4 ∧
      (∀ j : Fin P.d, out.mem (updates + j.val) = next.updCount j.val) ∧
      (∀ j : Fin P.d, out.mem (restarts + j.val) = next.curRestarts j.val) ∧
      (∀ j : Fin (P.d + 1), out.mem (rebuilds + j.val) = next.rebuildCount j.val) ∧
      ∀ a, (a < updates + i.val ∨ updates + P.d ≤ a) →
        (a < restarts + i.val ∨ restarts + P.d ≤ a) →
        a ≠ rebuilds + i.val → out.mem a = rebuilt.mem a :=
  periodicRebuildWithCounters_runs chain i G enc
    (level := rebuildCoreStep init read forestOp copy sort cell)
    (terminal := rebuildTerminalRuntimeStep terminalInit) hr
    (rebuildCoreStep_writesBelow init read forestOp copy sort cell) rfl
    hUpdates hRestarts hLevel hDepth hRebuilds hu hrr hreb hur huc hrc hub hrb hcb hw hnext

end MinCostFlow.MinRatio
