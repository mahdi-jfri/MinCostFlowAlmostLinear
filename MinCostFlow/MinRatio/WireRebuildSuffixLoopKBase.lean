module

public import MinCostFlow.MinRatio.WireRebuildSuffixK
public import MinCostFlow.MinRatio.WireChainAlgebra
import WordRAM.Tactic

/-!
# K-contract ordered suffix rebuild loop: programs and invariant (`WireRebuildSuffixLoopKBase`)

Defines:
1. `ordRebuildLevelBodyKStore`: runs `ordRebuildLevelBodyK` and stores `nextLen` (`reg 7`) into
   `levelMeta[i + 1]` and `nextGraph` (`reg 6`) into `levelMeta[d + i + 1]` when `i + 1 < d`.
2. `ordRebuildSuffixProgramKStore`: `rebuildSuffixProgram` composing `ordRebuildLevelBodyKStore`
   on `[first, d)` with `rebuildTerminalRuntimeStep` at level `d`.
3. `SuffixLoopInv` and `wireCoreLenEdgeCost_mono` for `WireRebuildSuffixLoopK.lean`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- One K-contract sparse-core suffix level iteration (`first ≤ i < d`), additionally saving
`nextLen` (`reg 7`) into `levelMeta[i + 1]` and `nextGraph` (`reg 6`) into `levelMeta[d + i + 1]`
when `i + 1 < d`. -/
@[expose] def ordRebuildLevelBodyKStore (init readGraph readLSF coreLenProc readOrd : ℕ) : Stmt :=
  ordRebuildLevelBodyK init readGraph readLSF coreLenProc readOrd ;;
  .cond (.bin .lt (.bin .add (.reg 19) (.const 1)) (.reg 21))
    (.store (.bin .add (.reg 58) (.bin .add (.reg 19) (.const 1))) (.reg 7) ;;
     .store (.bin .add (.bin .add (.reg 58) (.reg 21)) (.bin .add (.reg 19) (.const 1))) (.reg 6))
    .nop

theorem ordRebuildLevelBodyKStore_noRand (init readGraph readLSF coreLenProc readOrd : ℕ) :
    (ordRebuildLevelBodyKStore init readGraph readLSF coreLenProc readOrd).NoRand := by
  simp [ordRebuildLevelBodyKStore, ordRebuildLevelBodyK_noRand, Stmt.NoRand]

/-- Full K-contract ordered suffix rebuild with `levelMeta` (`levelLens` and `levelGraphs`) updates. -/
@[expose] def ordRebuildSuffixProgramKStore
    (init readGraph readLSF coreLenProc readOrd lastInit : ℕ) : Stmt :=
  rebuildSuffixProgram
    (ordRebuildLevelBodyKStore init readGraph readLSF coreLenProc readOrd)
    (rebuildTerminalRuntimeStep lastInit)

theorem ordRebuildSuffixProgramKStore_noRand
    (init readGraph readLSF coreLenProc readOrd lastInit : ℕ) :
    (ordRebuildSuffixProgramKStore init readGraph readLSF coreLenProc readOrd lastInit).NoRand := by
  apply rebuildSuffixProgram_noRand (ordRebuildLevelBodyKStore_noRand _ _ _ _ _)
  simp [rebuildTerminalRuntimeStep, rebuildLastLevelRuntime, storeRebuiltLevel, Stmt.NoRand]

theorem wireCoreLenEdgeCost_mono {a b : ℕ} (h : a ≤ b) :
    wireCoreLenEdgeCost a ≤ wireCoreLenEdgeCost b := by
  unfold wireCoreLenEdgeCost
  have h1 : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left h 2
  have h2 : (2 * a) ^ 2 ≤ (2 * b) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem wireCoreLenEdgeSpace_mono {a b : ℕ} (h : a ≤ b) :
    wireCoreLenEdgeSpace a ≤ wireCoreLenEdgeSpace b := by
  unfold wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
  have h1 : 5 * (2 * a) * (2 * a + 1) ≤ 5 * (2 * b) * (2 * b + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 5 (by omega)) (by omega)
  omega

/-- Terminal rebuild step returning the explicit allocation upper bound `ret ≤ heap + allocation 1 [...]`. -/
theorem wireRebuildTerminalStep_runs {w L init graph lengths heap vCap eCap multiplier stretchPrecision
    handleCell branchCell : ℕ}
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
    (hst : ∀ e ∈ G.E, 2 * (2 : ℝ) ^ stretchPrecision * lastLevelStretchBound G ℓ e <
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
      heap ≤ ret ∧ ret ≤ heap + allocation 1 [graph, lengths, L, fmt.precision, heap] ∧
      cost + R.phi heap y out.mem ≤ multiplier * (tool.cost G + 1) + 20 := by
  have hbuild := rebuildLastLevelRuntime_tables_runs (ω := ω) himpl hg hl hh hL hP hLWord hPWord
    hFour hWidth ℓ hG hgraph hLenRoom hℓ hst hpos hz hroom
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
    hcell.trans houtHandle, hbranch, hregs ▸ hret, houtHandle ▸ hrep', ?_, hfoot, ?_, hframe.1,
    hframe.2.1, ?_⟩
  · intro a ha
    have hlo := hframe.1
    exact (hmem a (by omega) (by omega)).trans (hframe.2.2.1 a ha)
  · intro a ha hhc hbc
    exact (hmem a hhc hbc).trans (hframe.2.2.2.1 a ha (by simp))
  · rw [houtHandle, hhandle] at hphi
    omega

/-- Loop invariant for `ordRebuildSuffixProgramKStore_runs`. -/
structure SuffixLoopInv {w L first handleBase branchBase lvlMTable levelLens heapFloor
    ordWords0 : ℕ} {fmt : Num.Format w} {T : SparseCoreRestartTool} {CP : ChainParams}
    (Rcore : DSRep (SparseCoreOrdAbs T)) (next : ChainState T CP) (levelSpace : ℕ → ℕ)
    (st0 : State) (i : ℕ) (s : State) (pot : ℕ) : Prop where
  r19 : s.regs 19 = i
  r20 : s.regs 20 = first
  r21 : s.regs 21 = CP.d
  r1 : s.regs 1 = CP.k
  r56 : s.regs 56 = next.N₀
  r57 : s.regs 57 = lvlMTable
  r58 : s.regs 58 = levelLens
  r67 : s.regs 67 = L
  r68 : s.regs 68 = fmt.precision
  r51 : s.regs 51 = handleBase + i
  r52 : s.regs 52 = branchBase + i
  heapGe : st0.regs 4 ≤ s.regs 4
  heapLe : s.regs 4 ≤ st0.regs 4 + (Finset.Ico first i).sum levelSpace
  hz : ZeroFrom s.mem (s.regs 4)
  curTables : ∃ vc ec oWords,
    DynGraphAt s.mem (s.regs 6) vc ec (next.G i) ∧
    EdgeValuesAt s.mem (s.regs 7) 4 L fmt.precision (next.G i).E
      (next.toTreeChain.chainLen next.ℓ i) ∧
    s.regs 8 = s.regs 7 ∧
    (i < CP.d →
      OrdListAt s.mem (s.regs 9) (next.levelOrd i) oWords ∧
      (∀ j < oWords, s.mem (s.regs 9 + j) < 2 ^ w) ∧
      s.regs 9 + oWords ≤ s.regs 4 ∧
      (i = first → oWords = ordWords0) ∧
      (first < i → oWords ≤ ordRotWords (chainLevelOrdAbs next (i - 1)) 0)) ∧
    s.regs 6 + dynGraphSize vc ec ≤ s.regs 4 ∧
    s.regs 7 + ec * L ≤ s.regs 4 ∧
    (i = first →
      (∀ a, s.regs 6 ≤ a → a < s.regs 6 + dynGraphSize vc ec →
        (a < handleBase + first ∨ handleBase + CP.d < a) ∧
        (a < branchBase + first ∨ branchBase + CP.d < a) ∧
        (a < levelLens + (first + 1) ∨ levelLens + 2 * CP.d ≤ a)) ∧
      (∀ a, s.regs 7 ≤ a → a < s.regs 7 + ec * L →
        (a < handleBase + first ∨ handleBase + CP.d < a) ∧
        (a < branchBase + first ∨ branchBase + CP.d < a) ∧
        (a < levelLens + (first + 1) ∨ levelLens + 2 * CP.d ≤ a))) ∧
    (first < i → heapFloor ≤ s.regs 6 ∧ heapFloor ≤ s.regs 7)
  cores : ∃ tok : ℕ → Rcore.τ,
    (∀ j, first ≤ j → j < i →
      s.mem (branchBase + j) = next.bran j ∧
      heapFloor ≤ s.mem (handleBase + j) ∧ s.mem (handleBase + j) ≤ s.regs 4 ∧
      Rcore.rep (s.mem (handleBase + j)) (chainLevelOrdAbs next j) (tok j) s.mem ∧
      (∀ a, Rcore.foot (s.mem (handleBase + j)) (tok j) a → heapFloor ≤ a ∧ a < s.regs 4)) ∧
    (∀ j₁ j₂, first ≤ j₁ → j₁ < i → first ≤ j₂ → j₂ < i → j₁ ≠ j₂ →
      ∀ a, Rcore.foot (s.mem (handleBase + j₁)) (tok j₁) a →
        ¬ Rcore.foot (s.mem (handleBase + j₂)) (tok j₂) a) ∧
    (∀ j, first + 1 ≤ j → j ≤ i → j < CP.d →
      ∃ vc_j ec_j,
        DynGraphAt s.mem (s.mem (levelLens + CP.d + j)) vc_j ec_j (next.G j) ∧
        heapFloor ≤ s.mem (levelLens + CP.d + j) ∧
        s.mem (levelLens + CP.d + j) + dynGraphSize vc_j ec_j ≤ s.regs 4 ∧
        EdgeValuesAt s.mem (s.mem (levelLens + j)) 4 L fmt.precision (next.G j).E
          (next.toTreeChain.chainLen next.ℓ j) ∧
        heapFloor ≤ s.mem (levelLens + j) ∧
        s.mem (levelLens + j) + ec_j * L ≤ s.regs 4 ∧
        (∀ r, first ≤ r → r < i →
          (∀ a, s.mem (levelLens + j) ≤ a → a < s.mem (levelLens + j) + ec_j * L →
            ¬ Rcore.foot (s.mem (handleBase + r)) (tok r) a) ∧
          (∀ a, s.mem (levelLens + CP.d + j) ≤ a →
            a < s.mem (levelLens + CP.d + j) + dynGraphSize vc_j ec_j →
            ¬ Rcore.foot (s.mem (handleBase + r)) (tok r) a))) ∧
    pot = (Finset.Ico first i).sum (fun j => Rcore.phi (s.mem (handleBase + j)) (tok j) s.mem)
  frame : ∀ a < heapFloor,
    (a < handleBase + first ∨ handleBase + CP.d < a) →
    (a < branchBase + first ∨ branchBase + CP.d < a) →
    ((a < levelLens + (first + 1) ∨ levelLens + CP.d ≤ a) ∧
     (a < levelLens + CP.d + (first + 1) ∨ levelLens + 2 * CP.d ≤ a)) →
    s.mem a = st0.mem a

end MinCostFlow.MinRatio
