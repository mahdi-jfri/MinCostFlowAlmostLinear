module

public import MinCostFlow.MinRatio.WireRebuildLevelKFBL
public import MinCostFlow.MinRatio.WireRebuildSuffixLoopKBase

/-!
# The suffix rebuild loop under the layout contract: programs and invariant

The shift loop rebuilds the levels `first, …, d - 1` of the chain and then the last level `d`.
Each level step runs the level body under `sparseCoreOrdMachineContractKFBL`
(`ordRebuildLevelBodyKFBL`, `WireRebuildLevelKFBL.lean`) and then saves the lengths and the graph
it read for the next level in the table `levelMeta`, as `ordRebuildLevelBodyKStore` does.
* `ordRebuildLevelBodyKFBLStore`, `ordRebuildSuffixProgramKFBLStore`: the programs.
* `SuffixLoopInvKFBL`: the invariant of the loop. It is `SuffixLoopInv` with two changes: every
  level graph has the caps `(vCap, eCap)` of the module, and the order list of the current level
  has at most `2 N + 2 M + 1` words, where `M` is the edge bound of the level. Both are what the
  level body asks.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- One level of the suffix rebuild under `sparseCoreOrdMachineContractKFBL` (`first ≤ i < d`).
It runs `ordRebuildLevelBodyKFBL`, then, when `i + 1 < d`, saves the next lengths (`reg 7`) in
`levelMeta[i + 1]` and the next graph (`reg 6`) in `levelMeta[d + i + 1]`. -/
@[expose] def ordRebuildLevelBodyKFBLStore (init readGraph readLSF coreLenProc readOrd : ℕ) :
    Stmt :=
  ordRebuildLevelBodyKFBL init readGraph readLSF coreLenProc readOrd ;;
  .cond (.bin .lt (.bin .add (.reg 19) (.const 1)) (.reg 21))
    (.store (.bin .add (.reg 58) (.bin .add (.reg 19) (.const 1))) (.reg 7) ;;
     .store (.bin .add (.bin .add (.reg 58) (.reg 21)) (.bin .add (.reg 19) (.const 1))) (.reg 6))
    .nop

theorem ordRebuildLevelBodyKFBLStore_noRand (init readGraph readLSF coreLenProc readOrd : ℕ) :
    (ordRebuildLevelBodyKFBLStore init readGraph readLSF coreLenProc readOrd).NoRand := by
  simp [ordRebuildLevelBodyKFBLStore, ordRebuildLevelBodyKFBL_noRand, Stmt.NoRand]

/-- The suffix rebuild under `sparseCoreOrdMachineContractKFBL`: `ordRebuildLevelBodyKFBLStore` on
`first, …, d - 1`, then `rebuildTerminalRuntimeStep lastInit` at level `d`. -/
@[expose] def ordRebuildSuffixProgramKFBLStore
    (init readGraph readLSF coreLenProc readOrd lastInit : ℕ) : Stmt :=
  rebuildSuffixProgram
    (ordRebuildLevelBodyKFBLStore init readGraph readLSF coreLenProc readOrd)
    (rebuildTerminalRuntimeStep lastInit)

theorem ordRebuildSuffixProgramKFBLStore_noRand
    (init readGraph readLSF coreLenProc readOrd lastInit : ℕ) :
    (ordRebuildSuffixProgramKFBLStore init readGraph readLSF coreLenProc readOrd
      lastInit).NoRand := by
  apply rebuildSuffixProgram_noRand (ordRebuildLevelBodyKFBLStore_noRand _ _ _ _ _)
  simp [rebuildTerminalRuntimeStep, rebuildLastLevelRuntime, storeRebuiltLevel, Stmt.NoRand]

/-- The invariant of `ordRebuildSuffixProgramKFBLStore_runs` before level `i`. The levels
`first, …, i - 1` are built: their handles and branches are in the tables at `handleBase` and
`branchBase`, their footprints are disjoint and lie in `[heapFloor, reg 4)`, and the potential
`pot` is the sum of their potentials. The graph, lengths and order list of level `i` are at
registers `6`, `7` and `9`. The table `levelMeta` (at `levelLens`) holds the graphs and lengths
of the levels `first + 1, …, i`. -/
structure SuffixLoopInvKFBL {w L depth vCap eCap first handleBase branchBase lvlMTable levelLens
    heapFloor : ℕ} {fmt : Num.Format w} {T : SparseCoreRestartTool} {CP : ChainParams}
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
  r98 : s.regs 98 = depth
  r51 : s.regs 51 = handleBase + i
  r52 : s.regs 52 = branchBase + i
  heapGe : st0.regs 4 ≤ s.regs 4
  heapLe : s.regs 4 ≤ st0.regs 4 + (Finset.Ico first i).sum levelSpace
  hz : ZeroFrom s.mem (s.regs 4)
  curTables :
    DynGraphAt s.mem (s.regs 6) vCap eCap (next.G i) ∧
    EdgeValuesAt s.mem (s.regs 7) 4 L fmt.precision (next.G i).E
      (next.toTreeChain.chainLen next.ℓ i) ∧
    s.regs 8 = s.regs 7 ∧
    (i < CP.d → ∃ oWords,
      OrdListAt s.mem (s.regs 9) (next.levelOrd i) oWords ∧
      (∀ j < oWords, s.mem (s.regs 9 + j) < 2 ^ w) ∧
      s.regs 9 + oWords ≤ s.regs 4 ∧
      oWords ≤ 2 * (next.G i).n + 2 * (next.G i).m + 1) ∧
    s.regs 6 + dynGraphSize vCap eCap ≤ s.regs 4 ∧
    s.regs 7 + eCap * L ≤ s.regs 4 ∧
    (i = first →
      (∀ a, s.regs 6 ≤ a → a < s.regs 6 + dynGraphSize vCap eCap →
        (a < handleBase + first ∨ handleBase + CP.d < a) ∧
        (a < branchBase + first ∨ branchBase + CP.d < a) ∧
        (a < levelLens + (first + 1) ∨ levelLens + 2 * CP.d ≤ a)) ∧
      (∀ a, s.regs 7 ≤ a → a < s.regs 7 + eCap * L →
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
      DynGraphAt s.mem (s.mem (levelLens + CP.d + j)) vCap eCap (next.G j) ∧
      heapFloor ≤ s.mem (levelLens + CP.d + j) ∧
      s.mem (levelLens + CP.d + j) + dynGraphSize vCap eCap ≤ s.regs 4 ∧
      EdgeValuesAt s.mem (s.mem (levelLens + j)) 4 L fmt.precision (next.G j).E
        (next.toTreeChain.chainLen next.ℓ j) ∧
      heapFloor ≤ s.mem (levelLens + j) ∧
      s.mem (levelLens + j) + eCap * L ≤ s.regs 4 ∧
      (∀ r, first ≤ r → r < i →
        (∀ a, s.mem (levelLens + j) ≤ a → a < s.mem (levelLens + j) + eCap * L →
          ¬ Rcore.foot (s.mem (handleBase + r)) (tok r) a) ∧
        (∀ a, s.mem (levelLens + CP.d + j) ≤ a →
          a < s.mem (levelLens + CP.d + j) + dynGraphSize vCap eCap →
          ¬ Rcore.foot (s.mem (handleBase + r)) (tok r) a))) ∧
    pot = (Finset.Ico first i).sum (fun j => Rcore.phi (s.mem (handleBase + j)) (tok j) s.mem)
  metaOrd :
    (∀ j, first + 1 ≤ j → j ≤ i → j < CP.d →
      s.mem (levelLens + CP.d + j) + dynGraphSize vCap eCap ≤ s.mem (levelLens + j)) ∧
    (∀ j₁ j₂, first + 1 ≤ j₁ → j₁ < j₂ → j₂ ≤ i → j₂ < CP.d →
      s.mem (levelLens + j₁) + eCap * L ≤ s.mem (levelLens + CP.d + j₂))
  frame : ∀ a < heapFloor,
    (a < handleBase + first ∨ handleBase + CP.d < a) →
    (a < branchBase + first ∨ branchBase + CP.d < a) →
    ((a < levelLens + (first + 1) ∨ levelLens + CP.d ≤ a) ∧
     (a < levelLens + CP.d + (first + 1) ∨ levelLens + 2 * CP.d ≤ a)) →
    s.mem a = st0.mem a

/-- The sum over `[a, i)` plus the term at `i` is at most the sum over `[a, d)` when `i < d`. -/
theorem sum_Ico_add_le_sum_Ico {f : ℕ → ℕ} {a i d : ℕ} (hai : a ≤ i) (hid : i < d) :
    (Finset.Ico a i).sum f + f i ≤ (Finset.Ico a d).sum f := by
  rw [← Finset.sum_Ico_succ_top hai]
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right hid)

end MinCostFlow.MinRatio
