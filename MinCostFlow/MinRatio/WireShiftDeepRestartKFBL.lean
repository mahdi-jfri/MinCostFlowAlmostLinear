module

public import MinCostFlow.MinRatio.WireShiftDeepRestart
public import MinCostFlow.MinRatio.WireInitReadoutKFBL
public import MinCostFlow.MinRatio.WireCoreOpsKFBL
import WordRAM.Tactic

/-!
# Phase 2 of the deep shift under the layout contract (`WireShiftDeepRestartKFBL`)

Phase 2 of the deep shift (`shiftDeepRestartAndReadout`) restarts level `i` in place, reads the
graph, lengths and order of the next level `i + 1` from it, and stores the graph and lengths in
the table `levelMeta`. Then it loads the registers of the suffix rebuild.

`shiftDeepRestartAndReadoutKFBL_runs` is the `KFBL` copy of `shiftDeepRestartAndReadout_runs`
(`WireShiftDeepRestart.lean`). The restart is `ordCoreRestartKFBL_runs` and the readout is
`ordReadoutNextLevelKFBL_runs_bounded`. So the `K` hypotheses on where the readouts lie
(`hReadoutRoom`, `hOrd5Disj`) are gone. In their place the caller gives three facts about the
model: the edge bound `nextM` of the next graph, the bound of the order of the new branch, and
the room for `ordLevelSpace`. The level graph and the read graph have the caps `(vCap, eCap)` of
the module.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program Bundle

/-- Phase 2 under `sparseCoreOrdMachineContractKFBL`: identical to `shiftDeepRestartAndReadout`,
except that the readout uses `ordReadoutNextLevelKFBL` (with `copyGraphLiveFromHeader`). -/
@[expose] def shiftDeepRestartAndReadoutKFBL
    (restart readGraph readLSF coreLenProc readOrd : ℕ) : Stmt :=
  .assign 0 (.bin .add (.reg 78) (.reg 71)) ;;
  .assign 1 (.reg 76) ;;
  .assign 3 (.load (.bin .add (.reg 77) (.reg 71))) ;;
  ordCoreRestartStmt restart ;;
  .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 71))) ;;
  .assign 7 (.load (.bin .add (.reg 83) (.reg 71))) ;;
  .assign 67 (.load (.bin .add (.reg 73) (.const 5))) ;;
  ordReadoutNextLevelKFBL readGraph readLSF coreLenProc readOrd ;;
  .cond (.bin .lt (.bin .add (.reg 71) (.const 1)) (.reg 75))
    (.store (.bin .add (.reg 83) (.bin .add (.reg 71) (.const 1))) (.reg 7) ;;
     .store (.bin .add (.bin .add (.reg 83) (.reg 75)) (.bin .add (.reg 71) (.const 1))) (.reg 6))
    .nop ;;
  .assign 20 (.bin .add (.reg 71) (.const 1)) ;;
  .assign 21 (.reg 75) ;;
  .assign 51 (.bin .add (.reg 77) (.reg 20)) ;;
  .assign 52 (.bin .add (.reg 78) (.reg 20)) ;;
  .assign 56 (.load (.bin .sub (.reg 82) (.const 1))) ;;
  .assign 57 (.reg 82) ;;
  .assign 58 (.reg 83) ;;
  .assign 68 (.load (.bin .add (.reg 73) (.const 8)))

theorem shiftDeepRestartAndReadoutKFBL_noRand
    (restart readGraph readLSF coreLenProc readOrd : ℕ) :
    (shiftDeepRestartAndReadoutKFBL restart readGraph readLSF coreLenProc readOrd).NoRand := by
  simp [shiftDeepRestartAndReadoutKFBL, ordCoreRestartStmt_noRand, ordReadoutNextLevelKFBL_noRand,
    Stmt.NoRand]

/-- **Phase 2 of the deep shift under the layout contract.** It restarts level `i0` in place,
reads the next level `(G'_{i0+1}, ℓ'_{i0+1}, ord'_{i0+1})` at the caps `(vCap, eCap)`, stores
`levelMeta[i0 + 1]` and `levelMeta[d + i0 + 1]` when `i0 + 1 < d`, and loads the registers
`20, 21, 51, 52, 56, 57, 58, 68` of the suffix rebuild. Its space is
`ordLevelSpace L capExp capLimit (allocation 1 …) (lvlM i0) N₀ nextM`. -/
theorem shiftDeepRestartAndReadoutKFBL_runs
    {w L depth vCap eCap capExp capLimit init coreLenProc edgeProc signExt mul intDiv copy i0
      handle handleBase branchBase lvlMTable levelMeta N0 coreH nextM : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {LT : LastLevelTool} {CP : ChainParams}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {p : Program} {op : ℕ → ℕ}
    {st : State} {ω : ℕ → Bool}
    (chain : ChainState T CP) (y0 : Rcore.τ)
    (hCoreLocal : Rcore.Local)
    (hFour : fmt.limbBits = 4)
    (hCoreImpl : Rcore.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth T (chain.G i0) CP.k (chain.lvlM i0) chain.N₀
        vCap eCap capExp P allocation))
    (hFootAt : SparseCoreReadoutFootAt fmt L depth T (chain.G i0) CP.k (chain.lvlM i0) chain.N₀
      vCap eCap capExp P allocation Rcore p op)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hiLt : i0 < CP.d) (hkPos : 0 < CP.k) (hkW : CP.k < 2 ^ w) (hdW : CP.d < 2 ^ w)
    (hw10 : 10 < 2 ^ w)
    (h71 : st.regs 71 = i0) (h73 : st.regs 73 = handle) (h75 : st.regs 75 = CP.d)
    (h76 : st.regs 76 = CP.k) (h77 : st.regs 77 = handleBase) (h78 : st.regs 78 = branchBase)
    (h82 : st.regs 82 = lvlMTable) (h83 : st.regs 83 = levelMeta)
    (hHCell : st.mem (handleBase + i0) = coreH) (hCoreHW : coreH < 2 ^ w)
    (hBCell : st.mem (branchBase + i0) = chain.bran i0) (hBrLt : chain.bran i0 < CP.k)
    (hLCell : st.mem (handle + 5) = L) (hPCell : st.mem (handle + 8) = fmt.precision)
    (_hLvlMPos : 1 ≤ lvlMTable) (_hLvlMLt : lvlMTable < 2 ^ w)
    (hNCell : st.mem (lvlMTable - 1) = N0)
    (hCellsLt : handle + 8 < st.regs 4 ∧ lvlMTable - 1 < st.regs 4 ∧
      handleBase + CP.d < st.regs 4 ∧
      branchBase + CP.d < st.regs 4 ∧ levelMeta + 2 * CP.d ≤ st.regs 4)
    (hCellsNotFoot :
      ¬ Rcore.foot coreH y0 (branchBase + i0) ∧
      ¬ Rcore.foot coreH y0 (handle + 5) ∧ ¬ Rcore.foot coreH y0 (handle + 8) ∧
      ¬ Rcore.foot coreH y0 (lvlMTable - 1) ∧
      ¬ Rcore.foot coreH y0 (levelMeta + i0) ∧ ¬ Rcore.foot coreH y0 (levelMeta + CP.d + i0) ∧
      (i0 + 1 < CP.d → ¬ Rcore.foot coreH y0 (levelMeta + (i0 + 1)) ∧
        ¬ Rcore.foot coreH y0 (levelMeta + CP.d + (i0 + 1))))
    (hCellsDisjB :
      handle + 5 ≠ branchBase + i0 ∧ handle + 8 ≠ branchBase + i0 ∧ lvlMTable - 1 ≠ branchBase + i0 ∧
      levelMeta + i0 ≠ branchBase + i0 ∧ levelMeta + CP.d + i0 ≠ branchBase + i0 ∧
      (i0 + 1 < CP.d → levelMeta + (i0 + 1) ≠ branchBase + i0 ∧
        levelMeta + CP.d + (i0 + 1) ≠ branchBase + i0 ∧
        handle + 8 ≠ levelMeta + (i0 + 1) ∧ handle + 8 ≠ levelMeta + CP.d + (i0 + 1) ∧
        lvlMTable - 1 ≠ levelMeta + (i0 + 1) ∧ lvlMTable - 1 ≠ levelMeta + CP.d + (i0 + 1)))
    (hGI : DynGraphAt st.mem (st.mem (levelMeta + CP.d + i0)) vCap eCap (chain.G i0))
    (hGIEnd : st.mem (levelMeta + CP.d + i0) + dynGraphSize vCap eCap ≤ st.regs 4)
    (hGIDisj : ∀ a, st.mem (levelMeta + CP.d + i0) ≤ a →
      a < st.mem (levelMeta + CP.d + i0) + dynGraphSize vCap eCap →
      ¬ Rcore.foot coreH y0 a ∧ a ≠ branchBase + i0)
    (hLenI : EdgeValuesAt st.mem (st.mem (levelMeta + i0)) 4 L fmt.precision (chain.G i0).E
      (chain.toTreeChain.chainLen chain.ℓ i0))
    (hLenIEnd : st.mem (levelMeta + i0) + eCap * L ≤ st.regs 4)
    (hLenIDisj : ∀ a, st.mem (levelMeta + i0) ≤ a →
      a < st.mem (levelMeta + i0) + eCap * L →
      ¬ Rcore.foot coreH y0 a ∧ a ≠ branchBase + i0)
    (hRep0 : Rcore.rep coreH (chainLevelOrdAbs chain i0) y0 st.mem)
    (hIn0 : SparseCoreOrdInput T CP.k (chain.lvlM i0) chain.N₀ (chain.scState i0) (chain.G i0)
      (chain.levelOrd i0) (chain.updCount i0))
    (hFoot0 : ∀ a, Rcore.foot coreH y0 a → a < st.regs 4)
    (hz0 : ZeroFrom st.mem (st.regs 4))
    (hNextSub :
      let next := (Chain.Ordered.algorithm1_shift T LT CP chain i0).1
      (next.G (i0 + 1)).E ⊆ (chain.G i0).E ∧
      ∀ e ∈ (next.G (i0 + 1)).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
          next.toTreeChain.chainLen chain.ℓ (i0 + 1) e)
    (hNextM : ((Chain.Ordered.algorithm1_shift T LT CP chain i0).1.G (i0 + 1)).m ≤ nextM)
    (hRotWords :
      ordRotWords (chainLevelOrdAbs (Chain.Ordered.algorithm1_shift T LT CP chain i0).1 i0)
        ((chain.bran i0 + 1) % CP.k) ≤ 1 + 2 * chain.N₀ + 2 * nextM)
    (hRoom : st.regs 4 + ordLevelSpace L capExp capLimit
      (allocation 1 [coreH, (chain.bran i0 + 1) % CP.k, st.regs 4]) (chain.lvlM i0) chain.N₀
        nextM < 2 ^ w) :
    let next := (Chain.Ordered.algorithm1_shift T LT CP chain i0).1
    let newBran := (chain.bran i0 + 1) % CP.k
    let LwMax := ordLevelLwMax L capExp (chain.lvlM i0) chain.N₀
    ∃ (out : State) (nextOrdWords cost : ℕ) (yOut : Rcore.τ),
      Runs w p ω (shiftDeepRestartAndReadoutKFBL (op 1) (op 3) (op 2) coreLenProc (op 5)) st .normal
        out cost ∧
      out.mem (branchBase + i0) = newBran ∧
      Rcore.rep coreH (chainLevelOrdAbs next i0) yOut out.mem ∧
      DynGraphAt out.mem (out.regs 6) vCap eCap (next.G (i0 + 1)) ∧
      EdgeValuesAt out.mem (out.regs 7) 4 L fmt.precision (next.G (i0 + 1)).E
        (next.toTreeChain.chainLen chain.ℓ (i0 + 1)) ∧
      out.regs 8 = out.regs 7 ∧
      (i0 + 1 < CP.d →
        OrdListAt out.mem (out.regs 9) (next.levelOrd (i0 + 1)) nextOrdWords ∧
        (∀ t < nextOrdWords, out.mem (out.regs 9 + t) < 2 ^ w) ∧
        out.regs 9 + nextOrdWords ≤ out.regs 4) ∧
      nextOrdWords ≤ ordRotWords (chainLevelOrdAbs next i0) newBran ∧
      st.regs 4 ≤ out.regs 6 ∧ out.regs 6 + dynGraphSize vCap eCap ≤ out.regs 4 ∧
      (∀ a, out.regs 6 ≤ a → a < out.regs 6 + dynGraphSize vCap eCap →
        ¬ Rcore.foot coreH yOut a) ∧
      st.regs 4 ≤ out.regs 7 ∧ out.regs 7 + eCap * L ≤ out.regs 4 ∧
      (∀ a, out.regs 7 ≤ a → a < out.regs 7 + eCap * L → ¬ Rcore.foot coreH yOut a) ∧
      out.regs 6 + dynGraphSize vCap eCap ≤ out.regs 7 ∧
      (i0 + 1 < CP.d → out.mem (levelMeta + (i0 + 1)) = out.regs 7 ∧
        out.mem (levelMeta + CP.d + (i0 + 1)) = out.regs 6) ∧
      st.regs 4 ≤ out.regs 4 ∧
      out.regs 4 ≤ st.regs 4 + ordLevelSpace L capExp capLimit
        (allocation 1 [coreH, newBran, st.regs 4]) (chain.lvlM i0) chain.N₀ nextM ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ a, Rcore.foot coreH yOut a → Rcore.foot coreH y0 a ∨ (st.regs 4 ≤ a ∧ a < out.regs 4)) ∧
      (∀ a < st.regs 4, ¬ Rcore.foot coreH y0 a → a ≠ branchBase + i0 →
        (i0 + 1 < CP.d → a ≠ levelMeta + (i0 + 1) ∧ a ≠ levelMeta + CP.d + (i0 + 1)) →
        out.mem a = st.mem a) ∧
      out.regs 1 = CP.k ∧ out.regs 20 = i0 + 1 ∧ out.regs 21 = CP.d ∧
      out.regs 51 = handleBase + (i0 + 1) ∧ out.regs 52 = branchBase + (i0 + 1) ∧
      out.regs 56 = N0 ∧ out.regs 57 = lvlMTable ∧ out.regs 58 = levelMeta ∧
      out.regs 67 = L ∧ out.regs 68 = fmt.precision ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      cost + Rcore.phi coreH yOut out.mem ≤
        P.mul * (T.cost (next.scState i0) - T.cost (chain.scState i0) + 1) +
        P.mul * (ordRotWords (chainLevelOrdAbs next i0) newBran + 1) *
          SparseCore.bundleLogFactor (chain.lvlM i0) chain.N₀ +
        2 * P.readout + copyGraphLiveCost (next.G (i0 + 1)).n (next.G (i0 + 1)).m +
        (next.G (i0 + 1)).m * (wireCoreLenEdgeCost LwMax + 30) +
        Rcore.phi coreH y0 st.mem + 360 := by
  dsimp only
  set next := (Chain.Ordered.algorithm1_shift T LT CP chain i0).1
  set newBran := (chain.bran i0 + 1) % CP.k
  have hEx := ordAlgorithm1_shift_exact T LT CP chain hiLt
  have hAbsNext : ordRestartNext (chainLevelOrdAbs chain i0) newBran = chainLevelOrdAbs next i0 :=
    (ordAlgorithm1_shift_levelOrdAbs_le T LT CP chain hiLt).2.symm
  have hScNext : next.scState i0 = T.restart (chain.scState i0) newBran := hEx.2.2.1
  have hBrNext : next.bran i0 = newBran := hEx.2.2.2.1
  have hGNext : next.G (i0 + 1) = T.S (next.scState i0) newBran := by
    rw [hScNext]; exact hEx.2.2.2.2.2.2.2.1
  have hLenNext : coreLen (T.lsfs (next.scState i0) newBran) (chain.toTreeChain.chainLen chain.ℓ i0) =
      next.toTreeChain.chainLen chain.ℓ (i0 + 1) := by
    have hPre := hEx.2.1
    have hLenPre : ∀ m ≤ i0, chain.toTreeChain.chainLen chain.ℓ m =
        next.toTreeChain.chainLen chain.ℓ m := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        obtain ⟨hsc, hbr, _⟩ := hPre k (by omega)
        simp only [TreeChain.chainLen]
        rw [ih (by omega)]
        simp only [ChainState.toTreeChain, TreeChain.activeLSF, show k < CP.d by omega, ↓reduceIte]
        rw [hsc, hbr]
    rw [hLenPre i0 le_rfl]
    simp only [TreeChain.chainLen, ChainState.toTreeChain, TreeChain.activeLSF, hiLt, ↓reduceIte,
      hBrNext]
  have hOrdNext : T.rot (next.scState i0) newBran = next.levelOrd (i0 + 1) := by
    simp only [ChainState.levelOrd, Chain.Ordered.chainLevelOrd, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel, hBrNext]
  have hSpUnfold : ordLevelSpace L capExp capLimit (allocation 1 [coreH, newBran, st.regs 4])
      (chain.lvlM i0) chain.N₀ nextM =
      allocation 1 [coreH, newBran, st.regs 4] + 1 + dynGraphSize capLimit capLimit + 5 +
        capLimit * L + nextM * wireCoreLenEdgeSpace (ordLevelLwMax L capExp (chain.lvlM i0) chain.N₀) +
        (2 + 2 * chain.N₀ + 2 * nextM) := rfl
  rw [hSpUnfold] at hRoom
  -- Step 1: setup regs `0, 1, 3` and call `ordCoreRestartStmt`
  let s1 := { st with regs := Function.update st.regs 0 (branchBase + i0) }
  let s2 := { s1 with regs := Function.update s1.regs 1 CP.k }
  let s3 := { s2 with regs := Function.update s2.regs 3 coreH }
  have r1 : Runs w p ω (.assign 0 (.bin .add (.reg 78) (.reg 71))) st .normal s1 4 :=
    runs_assign_iff.mpr ⟨branchBase + i0, by simp [Expr.eval, BinOp.eval, h78, h71,
      show branchBase + i0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 1 (.reg 76)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨CP.k, by simp [Expr.eval, s1, h76], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 77) (.reg 71)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨coreH, by simp [Expr.eval, BinOp.eval, s2, s1, h77, h71,
      show handleBase + i0 < 2 ^ w by omega, hHCell], rfl, rfl, rfl⟩
  obtain ⟨s4, ret1, c4, y1, r4, hs4_2, hs4_3, hs4_4, hs4_b, hIn1, hrep1, hresp1, hc4, hs4_regs⟩ :=
    ordCoreRestartKFBL_runs (ω := ω) (st := s3) hCoreImpl
      (by simp [s3, s2, s1]) (by simp [s3, s2]) (by simp [s3]) (by simp [s3, s2, s1])
      hBCell hBrLt hkW hCoreHW (by omega) hCellsNotFoot.1 hRep0 hIn0 hFoot0 hz0
      (by dsimp only [newBran] at hRoom; omega)
  rw [hAbsNext] at hrep1
  have hs4_r (r : ℕ) (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) :
      s4.regs r = st.regs r := by
    rw [hs4_regs r h2 h4]
    simp [s3, s2, s1, Function.update_of_ne h3, Function.update_of_ne h1, Function.update_of_ne h0]
  have hs4_eq (a : ℕ) (ha : a < st.regs 4) (hnf : ¬ Rcore.foot coreH y0 a)
      (hneB : a ≠ branchBase + i0) : s4.mem a = st.mem a := by
    rw [hresp1.2.2.2.1 a ha hnf]; simp [s3, s2, s1, Function.update_of_ne hneB]
  -- Step 2: load `reg 6 = G_i`, `reg 7 = ℓ_i`, `reg 67 = L` and run `ordReadoutNextLevelK`
  have hs4_GPtr : s4.mem (levelMeta + CP.d + i0) = st.mem (levelMeta + CP.d + i0) :=
    hs4_eq _ (by omega) hCellsNotFoot.2.2.2.2.2.1 hCellsDisjB.2.2.2.2.1
  have hs4_LPtr : s4.mem (levelMeta + i0) = st.mem (levelMeta + i0) :=
    hs4_eq _ (by omega) hCellsNotFoot.2.2.2.2.1 hCellsDisjB.2.2.2.1
  have hs4_LVal : s4.mem (handle + 5) = L :=
    (hs4_eq _ (by omega) hCellsNotFoot.2.1 hCellsDisjB.1).trans hLCell
  let s5 := { s4 with regs := Function.update s4.regs 6 (st.mem (levelMeta + CP.d + i0)) }
  let s6 := { s5 with regs := Function.update s5.regs 7 (st.mem (levelMeta + i0)) }
  let s7 := { s6 with regs := Function.update s6.regs 67 L }
  have r5 : Runs w p ω (.assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 71))))
      s4 .normal s5 7 :=
    runs_assign_iff.mpr ⟨st.mem (levelMeta + CP.d + i0), by simp [Expr.eval, BinOp.eval,
      hs4_r 83 (by decide) (by decide) (by decide) (by decide) (by decide),
      hs4_r 75 (by decide) (by decide) (by decide) (by decide) (by decide),
      hs4_r 71 (by decide) (by decide) (by decide) (by decide) (by decide),
      h83, h75, h71, show levelMeta + CP.d < 2 ^ w by omega,
      show levelMeta + CP.d + i0 < 2 ^ w by omega, hs4_GPtr], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 83) (.reg 71)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨st.mem (levelMeta + i0), by simp [Expr.eval, BinOp.eval, s5,
      hs4_r 83 (by decide) (by decide) (by decide) (by decide) (by decide),
      hs4_r 71 (by decide) (by decide) (by decide) (by decide) (by decide),
      h83, h71, show levelMeta + i0 < 2 ^ w by omega, hs4_LPtr], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 67 (.load (.bin .add (.reg 73) (.const 5)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, BinOp.eval, s6, s5,
      hs4_r 73 (by decide) (by decide) (by decide) (by decide) (by decide), h73,
      show 5 < 2 ^ w by omega, show handle + 5 < 2 ^ w by omega, hs4_LVal], rfl, rfl, rfl⟩
  have hfoot1_lt : ∀ a, Rcore.foot coreH y1 a → a < ret1 := fun a ha => by
    rcases hresp1.2.2.2.2 a ha with h0 | ⟨_, hhi⟩
    · exact (hFoot0 a h0).trans_le hresp1.1
    · exact hhi
  have hGe : (chainLevelOrdAbs next i0).G = chain.G i0 := hEx.1 i0 le_rfl
  have hs7_GI : DynGraphAt s7.mem (st.mem (levelMeta + CP.d + i0)) vCap eCap
      (chainLevelOrdAbs next i0).G := by
    rw [hGe]
    exact dynGraphAt_of_agree hGI (fun a ha1 ha2 =>
      hs4_eq a (by omega) (hGIDisj a ha1 ha2).1 (hGIDisj a ha1 ha2).2)
  have hs7_LenI : EdgeValuesAt s7.mem (st.mem (levelMeta + i0)) 4 L fmt.precision
      (chainLevelOrdAbs next i0).G.E (chain.toTreeChain.chainLen chain.ℓ i0) := by
    rw [hGe]
    exact hLenI.congr (fun e he t ht => by
      have heLt := hGI.2.2.1 e he
      have hmul : e * L + L ≤ eCap * L := by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
      exact hs4_eq _ (by omega) (hLenIDisj _ (by omega) (by omega)).1
        (hLenIDisj _ (by omega) (by omega)).2)
  have hSm : (T.S (chainLevelOrdAbs next i0).st newBran).m ≤ nextM := by
    dsimp only [chainLevelOrdAbs]; rw [← hGNext]; exact hNextM
  obtain ⟨s8, vcH, ecH, nextOrdWords, Lw, c8, y2, r8, _, hvcEq, hecEq, _, hrep2, hH8, hLen8,
      hGrad8, hOrd8, hOrdLe8, hOrdEnd8, hOrdLo8, hOrdW8, h6Lo8, hHEnd8, h6Disj8, h7Lo8,
      hLenEnd8, h7Disj8, h6Le7_8, h4Lo8, h4Hi8, hz8, hs8_fr, _, hs8_footIn, hs8_regs, hc8⟩ :=
    ordReadoutNextLevelKFBL_runs_bounded_ord (branch := newBran) (nextM := nextM) (ω := ω) (st := s7)
      (chain.toTreeChain.chainLen chain.ℓ i0)
      hFour hCoreImpl hFootAt hcapLim hCoreLenProc hEdgeProc hSign hMul hDiv hCopy
      (by simp [s7, s6, s5, hs4_2, newBran]) (by simp [s7, s6, s5, hs4_3])
      (by simp [s7, s6, s5, hs4_4]) (by simp [s7, s6, s5]) (by simp [s7, s6]) (by simp [s7])
      (Nat.mod_lt _ hkPos) hkW hCoreHW (by omega) hs7_GI (hGIEnd.trans hresp1.1)
      (fun a ha1 ha2 hf => by
        rcases hresp1.2.2.2.2 a hf with h0 | ⟨hlo, _⟩
        · exact (hGIDisj a ha1 ha2).1 h0
        · omega)
      hs7_LenI (hLenIEnd.trans hresp1.1)
      (fun a ha1 ha2 hf => by
        rcases hresp1.2.2.2.2 a hf with h0 | ⟨hlo, _⟩
        · exact (hLenIDisj a ha1 ha2).1 h0
        · omega)
      hrep1 (by rwa [← hAbsNext]) hfoot1_lt hresp1.2.2.1
      (by dsimp [chainLevelOrdAbs]; rw [← hGNext, hEx.1 i0 le_rfl]; exact hNextSub.1)
      hSm hRotWords
      (by dsimp [chainLevelOrdAbs]; rw [← hGNext, hLenNext]; exact hNextSub.2)
      (by have h := hresp1.2.1; dsimp only [newBran] at hRoom h ⊢; unfold ordLevelLwMax at hRoom ⊢
          omega)
  subst hvcEq hecEq
  dsimp only [chainLevelOrdAbs] at hH8 hLen8 hOrd8
  rw [← hGNext] at hH8 hLen8
  rw [hLenNext] at hLen8
  rw [hOrdNext] at hOrd8
  -- Step 3: conditional store into `levelMeta` if `i0 + 1 < d`
  have hs8_high (r : ℕ) (hr : 70 ≤ r) : s8.regs r = st.regs r :=
    (hs8_regs r (by omega)).trans (by simp [s7, s6, s5, Function.update_of_ne (by omega : r ≠ 67),
      Function.update_of_ne (by omega : r ≠ 7), Function.update_of_ne (by omega : r ≠ 6),
      hs4_r r (by omega) (by omega) (by omega) (by omega) (by omega)])
  let condStmt : Stmt :=
    .cond (.bin .lt (.bin .add (.reg 71) (.const 1)) (.reg 75))
      (.store (.bin .add (.reg 83) (.bin .add (.reg 71) (.const 1))) (.reg 7) ;;
       .store (.bin .add (.bin .add (.reg 83) (.reg 75)) (.bin .add (.reg 71) (.const 1))) (.reg 6))
      .nop
  have hCond : ∃ s9 c9,
      Runs w p ω condStmt s8 .normal s9 c9 ∧ c9 ≤ 25 ∧ s9.regs = s8.regs ∧
      (i0 + 1 < CP.d → s9.mem (levelMeta + (i0 + 1)) = s8.regs 7 ∧
        s9.mem (levelMeta + CP.d + (i0 + 1)) = s8.regs 6) ∧
      (∀ a, (i0 + 1 < CP.d → a ≠ levelMeta + (i0 + 1) ∧ a ≠ levelMeta + CP.d + (i0 + 1)) →
        s9.mem a = s8.mem a) := by
    by_cases hNextLt : i0 + 1 < CP.d
    · let s9a := { s8 with mem := Function.update s8.mem (levelMeta + (i0 + 1)) (s8.regs 7) }
      let s9 := { s9a with mem := Function.update s9a.mem (levelMeta + CP.d + (i0 + 1)) (s8.regs 6) }
      have rS1 : Runs w p ω (.store (.bin .add (.reg 83) (.bin .add (.reg 71) (.const 1))) (.reg 7))
          s8 .normal s9a 7 :=
        runs_store_iff.mpr ⟨levelMeta + (i0 + 1), s8.regs 7,
          by simp [Expr.eval, BinOp.eval, hs8_high 83 (by decide), hs8_high 71 (by decide), h83, h71,
            show 1 < 2 ^ w by omega, show i0 + 1 < 2 ^ w by omega,
            show levelMeta + (i0 + 1) < 2 ^ w by omega],
          by simp [Expr.eval], rfl, rfl, rfl⟩
      have rS2 : Runs w p ω
          (.store (.bin .add (.bin .add (.reg 83) (.reg 75)) (.bin .add (.reg 71) (.const 1))) (.reg 6))
          s9a .normal s9 9 :=
        runs_store_iff.mpr ⟨levelMeta + CP.d + (i0 + 1), s8.regs 6,
          by simp [Expr.eval, BinOp.eval, s9a, hs8_high 83 (by decide), hs8_high 75 (by decide),
            hs8_high 71 (by decide), h83, h75, h71, show 1 < 2 ^ w by omega,
            show i0 + 1 < 2 ^ w by omega, show levelMeta + CP.d < 2 ^ w by omega,
            show levelMeta + CP.d + (i0 + 1) < 2 ^ w by omega],
          by simp [Expr.eval, s9a], rfl, rfl, rfl⟩
      have rC : Runs w p ω condStmt s8 .normal s9 23 :=
        runs_cond_iff.mpr ⟨1, 7 + 9 + 1,
          by simp [Expr.eval, BinOp.eval, hs8_high 71 (by decide), hs8_high 75 (by decide), h71, h75,
            show 1 < 2 ^ w by omega, show i0 + 1 < 2 ^ w by omega, hNextLt],
          by simpa using runs_seq_iff.mpr (Or.inr ⟨s9a, 7, 9, rS1, rS2, rfl⟩), by simp [Expr.size]⟩
      exact ⟨s9, 23, rC, by omega, rfl,
        fun _ => ⟨by simp [s9, s9a, Function.update_of_ne
            (by omega : levelMeta + (i0 + 1) ≠ levelMeta + CP.d + (i0 + 1))],
          by simp [s9]⟩,
        fun a hne => by
          obtain ⟨h1, h2⟩ := hne hNextLt
          simp [s9, s9a, Function.update_of_ne h1, Function.update_of_ne h2]⟩
    · have rC : Runs w p ω condStmt s8 .normal s8 7 :=
        runs_cond_iff.mpr ⟨0, 1,
          by simp [Expr.eval, BinOp.eval, hs8_high 71 (by decide), hs8_high 75 (by decide), h71, h75,
            show 1 < 2 ^ w by omega, show i0 + 1 < 2 ^ w by omega, hNextLt],
          by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩
      exact ⟨s8, 7, rC, by omega, rfl, fun h => absurd h hNextLt, fun _ _ => rfl⟩
  obtain ⟨s9, c9, r9, hc9, hs9_regs, hs9_meta, hs9_ne⟩ := hCond
  -- Step 4: setup suffix loop registers `20, 21, 51, 52, 56, 57, 58, 68`
  have hs9_eq_st (a : ℕ) (ha : a < st.regs 4) (hnf : ¬ Rcore.foot coreH y0 a)
      (hneB : a ≠ branchBase + i0)
      (hneM : i0 + 1 < CP.d → a ≠ levelMeta + (i0 + 1) ∧ a ≠ levelMeta + CP.d + (i0 + 1)) :
      s9.mem a = st.mem a := by
    have hnf1 : ¬ Rcore.foot coreH y1 a := fun hf => by
      rcases hresp1.2.2.2.2 a hf with h0 | ⟨hlo, _⟩
      · exact hnf h0
      · omega
    rw [hs9_ne a hneM, hs8_fr a (ha.trans_le hresp1.1) hnf1]
    exact hs4_eq a ha hnf hneB
  have hs9_N : s9.mem (lvlMTable - 1) = N0 :=
    (hs9_eq_st _ (by omega) hCellsNotFoot.2.2.2.1 hCellsDisjB.2.2.1
      (fun h => ⟨(hCellsDisjB.2.2.2.2.2 h).2.2.2.2.1,
        (hCellsDisjB.2.2.2.2.2 h).2.2.2.2.2⟩)).trans hNCell
  have hs9_P : s9.mem (handle + 8) = fmt.precision :=
    (hs9_eq_st _ (by omega) hCellsNotFoot.2.2.1 hCellsDisjB.2.1
      (fun h => ⟨(hCellsDisjB.2.2.2.2.2 h).2.2.1, (hCellsDisjB.2.2.2.2.2 h).2.2.2.1⟩)).trans hPCell
  let t1 := { s9 with regs := Function.update s9.regs 20 (i0 + 1) }
  let t2 := { t1 with regs := Function.update t1.regs 21 CP.d }
  let t3 := { t2 with regs := Function.update t2.regs 51 (handleBase + (i0 + 1)) }
  let t4 := { t3 with regs := Function.update t3.regs 52 (branchBase + (i0 + 1)) }
  let t5 := { t4 with regs := Function.update t4.regs 56 N0 }
  let t6 := { t5 with regs := Function.update t5.regs 57 lvlMTable }
  let t7 := { t6 with regs := Function.update t6.regs 58 levelMeta }
  let out := { t7 with regs := Function.update t7.regs 68 fmt.precision }
  have hs9_hi (r : ℕ) (hr : 70 ≤ r) : s9.regs r = st.regs r :=
    (congrFun hs9_regs r).trans (hs8_high r hr)
  have rt1 : Runs w p ω (.assign 20 (.bin .add (.reg 71) (.const 1))) s9 .normal t1 4 :=
    runs_assign_iff.mpr ⟨i0 + 1, by simp [Expr.eval, BinOp.eval, hs9_hi 71 (by decide), h71,
      show 1 < 2 ^ w by omega, show i0 + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have rt2 : Runs w p ω (.assign 21 (.reg 75)) t1 .normal t2 2 :=
    runs_assign_iff.mpr ⟨CP.d, by simp [Expr.eval, t1, hs9_hi 75 (by decide), h75], rfl, rfl, rfl⟩
  have rt3 : Runs w p ω (.assign 51 (.bin .add (.reg 77) (.reg 20))) t2 .normal t3 4 :=
    runs_assign_iff.mpr ⟨handleBase + (i0 + 1), by simp [Expr.eval, BinOp.eval, t2, t1,
      hs9_hi 77 (by decide), h77, show handleBase + (i0 + 1) < 2 ^ w by omega], rfl, rfl, rfl⟩
  have rt4 : Runs w p ω (.assign 52 (.bin .add (.reg 78) (.reg 20))) t3 .normal t4 4 :=
    runs_assign_iff.mpr ⟨branchBase + (i0 + 1), by simp [Expr.eval, BinOp.eval, t3, t2, t1,
      hs9_hi 78 (by decide), h78, show branchBase + (i0 + 1) < 2 ^ w by omega], rfl, rfl, rfl⟩
  have rt5 : Runs w p ω (.assign 56 (.load (.bin .sub (.reg 82) (.const 1)))) t4 .normal t5 5 :=
    runs_assign_iff.mpr ⟨N0, by simp [Expr.eval, BinOp.eval, t4, t3, t2, t1,
      hs9_hi 82 (by decide), h82, show 1 < 2 ^ w by omega, show lvlMTable - 1 < 2 ^ w by omega, hs9_N], rfl, rfl, rfl⟩
  have rt6 : Runs w p ω (.assign 57 (.reg 82)) t5 .normal t6 2 :=
    runs_assign_iff.mpr ⟨lvlMTable, by simp [Expr.eval, t5, t4, t3, t2, t1,
      hs9_hi 82 (by decide), h82], rfl, rfl, rfl⟩
  have rt7 : Runs w p ω (.assign 58 (.reg 83)) t6 .normal t7 2 :=
    runs_assign_iff.mpr ⟨levelMeta, by simp [Expr.eval, t6, t5, t4, t3, t2, t1,
      hs9_hi 83 (by decide), h83], rfl, rfl, rfl⟩
  have rt8 : Runs w p ω (.assign 68 (.load (.bin .add (.reg 73) (.const 8)))) t7 .normal out 5 :=
    runs_assign_iff.mpr ⟨fmt.precision, by simp [Expr.eval, BinOp.eval, t7, t6, t5, t4, t3, t2, t1,
      hs9_hi 73 (by decide), h73, show 8 < 2 ^ w by omega, show handle + 8 < 2 ^ w by omega, hs9_P],
      rfl, rfl, rfl⟩
  have hfoot2_in (a : ℕ) (ha : Rcore.foot coreH y2 a) :
      Rcore.foot coreH y0 a ∨ (st.regs 4 ≤ a ∧ a < s8.regs 4) := by
    rcases hs8_footIn a ha with hy1 | ⟨hlo, hhi⟩
    · rcases hresp1.2.2.2.2 a hy1 with hy0 | ⟨hlo1, hhi1⟩
      · exact Or.inl hy0
      · exact Or.inr ⟨hlo1, hhi1.trans_le h4Lo8⟩
    · exact Or.inr ⟨hresp1.1.trans hlo, hhi⟩
  have hlocY2 := hCoreLocal coreH (chainLevelOrdAbs next i0) y2 s8.mem out.mem
    (fun a ha => by
      change s8.mem a = s9.mem a
      symm
      apply hs9_ne a
      intro hlt
      rcases hfoot2_in a ha with hy0 | ⟨hlo, _⟩
      · exact ⟨fun h => (hCellsNotFoot.2.2.2.2.2.2 hlt).1 (h ▸ hy0),
          fun h => (hCellsNotFoot.2.2.2.2.2.2 hlt).2 (h ▸ hy0)⟩
      · exact ⟨by omega, by omega⟩)
  have hout_r (r : ℕ)
      (hr : r ≠ 20 ∧ r ≠ 21 ∧ r ≠ 51 ∧ r ≠ 52 ∧ r ≠ 56 ∧ r ≠ 57 ∧ r ≠ 58 ∧ r ≠ 68) :
      out.regs r = s8.regs r := by
    simp only [out, t7, t6, t5, t4, t3, t2, t1,
      Function.update_of_ne hr.2.2.2.2.2.2.2, Function.update_of_ne hr.2.2.2.2.2.2.1,
      Function.update_of_ne hr.2.2.2.2.2.1, Function.update_of_ne hr.2.2.2.2.1,
      Function.update_of_ne hr.2.2.2.1, Function.update_of_ne hr.2.2.1,
      Function.update_of_ne hr.2.1, Function.update_of_ne hr.1]
    exact congrFun hs9_regs r
  have hout4 : out.regs 4 = s8.regs 4 := hout_r 4 (by omega)
  have hout6 : out.regs 6 = s8.regs 6 := hout_r 6 (by omega)
  have hout7 : out.regs 7 = s8.regs 7 := hout_r 7 (by omega)
  have hout8 : out.regs 8 = s8.regs 8 := hout_r 8 (by omega)
  have hout9 : out.regs 9 = s8.regs 9 := hout_r 9 (by omega)
  have rAll : Runs w p ω (shiftDeepRestartAndReadoutKFBL (op 1) (op 3) (op 2) coreLenProc (op 5))
      st .normal out
      (4 + (2 + (5 + (c4 + (7 + (5 + (5 + (c8 + (c9 + (4 + (2 + (4 + (4 + (5 + (2 + (2 + 5 + 1) +
        1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 4, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, c4, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 7, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 5, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, c8, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, c9, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨t1, 4, _, rt1,
    runs_seq_iff.mpr (Or.inr ⟨t2, 2, _, rt2,
    runs_seq_iff.mpr (Or.inr ⟨t3, 4, _, rt3,
    runs_seq_iff.mpr (Or.inr ⟨t4, 4, _, rt4,
    runs_seq_iff.mpr (Or.inr ⟨t5, 5, _, rt5,
    runs_seq_iff.mpr (Or.inr ⟨t6, 2, _, rt6,
    runs_seq_iff.mpr (Or.inr ⟨t7, 2, 5, rt7, rt8, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨out, nextOrdWords, _, y2, rAll, ?_, hlocY2.1 hrep2, ?_, ?_,
    by rw [hout8, hout7, hGrad8], ?_, hOrdLe8,
    by rw [hout6]; exact hresp1.1.trans h6Lo8,
    by rw [hout6, hout4]; exact hHEnd8,
    fun a ha1 ha2 => h6Disj8 a (hout6 ▸ ha1) (hout6 ▸ ha2),
    by rw [hout7]; exact hresp1.1.trans h7Lo8,
    by rw [hout7, hout4]; exact hLenEnd8,
    fun a ha1 ha2 => h7Disj8 a (hout7 ▸ ha1) (hout7 ▸ ha2),
    by rw [hout6, hout7]; exact h6Le7_8,
    fun hlt => by rw [hout7, hout6]; exact hs9_meta hlt,
    by rw [hout4]; exact hresp1.1.trans h4Lo8,
    by rw [hSpUnfold, hout4]; have := hresp1.2.1; dsimp only [newBran] at h4Hi8 this ⊢; omega,
    fun a ha => by
      rw [hout4] at ha; have h4Ge : st.regs 4 ≤ s8.regs 4 := hresp1.1.trans h4Lo8
      change s9.mem a = 0; rw [hs9_ne a (fun _ => ⟨by omega, by omega⟩)]; exact hz8 a ha,
    fun a ha => hout4.symm ▸ hfoot2_in a ha, hs9_eq_st,
    (hout_r 1 (by omega)).trans ((hs8_regs 1 (by omega)).trans
      (by simp [s7, s6, s5, hs4_regs 1 (by decide) (by decide), s3, s2])),
    by simp [out, t7, t6, t5, t4, t3, t2, t1],
    by simp [out, t7, t6, t5, t4, t3, t2],
    by simp [out, t7, t6, t5, t4, t3],
    by simp [out, t7, t6, t5, t4],
    by simp [out, t7, t6, t5],
    by simp [out, t7, t6],
    by simp [out, t7],
    (hout_r 67 (by omega)).trans ((hs8_regs 67 (by omega)).trans (by simp [s7])),
    by simp [out],
    fun r hr => (hout_r r (by omega)).trans (hs8_high r hr),
    ?_⟩
  · change s9.mem (branchBase + i0) = newBran
    have hnf1 : ¬ Rcore.foot coreH y1 (branchBase + i0) := fun hf => by
      rcases hresp1.2.2.2.2 _ hf with h0 | ⟨hlo, _⟩
      · exact hCellsNotFoot.1 h0
      · omega
    rw [hs9_ne _ (fun hlt => ⟨(hCellsDisjB.2.2.2.2.2 hlt).1.symm,
        (hCellsDisjB.2.2.2.2.2 hlt).2.1.symm⟩),
      hs8_fr _ (by have := hresp1.1; omega) hnf1]
    exact hs4_b
  · rw [hout6]
    have h6Ge : st.regs 4 ≤ s8.regs 6 := hresp1.1.trans h6Lo8
    exact dynGraphAt_of_agree hH8 (fun a ha1 _ => hs9_ne a (fun _ => ⟨by omega, by omega⟩))
  · rw [hout7]
    have h7Ge : st.regs 4 ≤ s8.regs 7 := hresp1.1.trans h7Lo8
    exact hLen8.congr (fun e _ j _ => hs9_ne (s8.regs 7 + e * L + j) (fun _ => ⟨by omega, by omega⟩))
  · intro _
    have h9Ge : st.regs 4 < s8.regs 9 := lt_of_le_of_lt hresp1.1 hOrdLo8
    have hEqO (t : ℕ) (ht : t < nextOrdWords) : out.mem (s8.regs 9 + t) = s8.mem (s8.regs 9 + t) :=
      hs9_ne (s8.regs 9 + t) (fun _ => ⟨by omega, by omega⟩)
    refine ⟨by rw [hout9]; exact ordListAt_of_agree hOrd8 hEqO,
      fun t ht => by rw [hout9, hEqO t ht]; exact hOrdW8 t ht,
      by rw [hout9, hout4]; exact hOrdEnd8⟩
  · change _ + Rcore.phi coreH y2 s9.mem ≤ _
    rw [← hlocY2.2]
    have hs7m : s7.mem = s4.mem := rfl
    rw [hs7m] at hc8
    change c8 + Rcore.phi coreH y2 s8.mem ≤ _ at hc8
    dsimp only [chainLevelOrdAbs] at hc8 ⊢
    rw [← hGNext] at hc8
    change c4 + Rcore.phi coreH y1 s4.mem ≤ P.mul * (T.cost (T.restart (chain.scState i0) newBran) -
      T.cost (chain.scState i0) + 1) + Rcore.phi coreH y0 st.mem + 19 at hc4
    rw [← hScNext] at hc4
    omega

end MinCostFlow.MinRatio
