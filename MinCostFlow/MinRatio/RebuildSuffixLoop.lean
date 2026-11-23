module

public import MinCostFlow.MinRatio.ShiftDeeperLevel
public import MinCostFlow.MinRatio.ShiftLastLevel
public import MinCostFlow.MinRatio.RebuildGuard
public import MinCostFlow.MinRatio.RebuildGradients
import MinCostFlow.MinRatio.RebuildModelSuffix

/-!
# Rebuild suffix loop and Shift counters

Algorithm 1 (page 20) rebuilds the sparse-core levels from the
first changed level to `d - 1`, then builds the terminal forest
collection at level `d`. The loop accounts for the different
initialization cost of each level.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- Register 19 is the current level, register 20 the first level,
and register 21 the terminal level. The body must advance the
represented chain, leaving the loop counter for the loop itself. -/
@[expose] def rebuildSuffixProgram (level terminal : Stmt) : Stmt :=
  forRange 19 (.reg 20) (.reg 21) level ;; terminal

/-- The suffix code has no random instructions when its two
initialization bodies have none. -/
theorem rebuildSuffixProgram_noRand {level terminal : Stmt}
    (hl : level.NoRand) (ht : terminal.NoRand) :
    (rebuildSuffixProgram level terminal).NoRand := by
  simp [rebuildSuffixProgram, forRange, Stmt.NoRand, hl, ht, forUp]

/-- Iterate the sparse-core initialization body, then run the
terminal body. The cost is the sum of the applicable level bounds,
nine steps per loop iteration, the terminal cost, and eight fixed steps. -/
theorem rebuildSuffixProgram_runs {w first last : ℕ} {p : Program}
    {level terminal : Stmt} {Inv : ℕ → State → Prop} {Done : State → Prop}
    {ω : ℕ → Bool} {st : State} (cost : ℕ → ℕ) (terminalCost : ℕ)
    (horder : first ≤ last) (hw : 1 < 2 ^ w) (hword : last < 2 ^ w)
    (hfirst : st.regs 20 = first)
    (hin : Inv first { st with regs := Function.update st.regs 19 first })
    (hindex : ∀ i current, first ≤ i → i ≤ last → Inv i current → current.regs 19 = i)
    (hstop : ∀ i current, first ≤ i → i ≤ last → Inv i current → current.regs 21 = last)
    (hlevel : ∀ i, first ≤ i → i < last → Triple w p (Inv i) level
      (normalPost fun next =>
        Inv (i + 1) { next with regs := Function.update next.regs 19 (i + 1) } ∧
          next.regs 19 = i) (fun _ => cost i))
    (hterminal : Triple w p (Inv last) terminal (normalPost Done) (fun _ => terminalCost)) :
    ∃ out c, Runs w p ω (rebuildSuffixProgram level terminal) st .normal out c ∧ Done out ∧
      c ≤ rangeCost cost first last + (last - first) * 9 + terminalCost + 8 := by
  have hloop := Triple.forRange_le (p := p) (r := 19) (lo := .reg 20) (hi := .reg 21)
    (P := fun s => s = st) (Inv := Inv) cost first last horder hw (fun _ => hword)
    (fun s hs => by subst s; exact ⟨by simp [Expr.eval, hfirst], hin⟩)
    hindex (fun i s hi hj hs => by simp [Expr.eval, hstop i s hi hj hs]) hlevel
  obtain ⟨o, mid, c, hprefix, hnext, hc⟩ := hloop.runs ω rfl
  cases o with
  | returned ret => exact False.elim hnext
  | normal =>
    obtain ⟨o, out, d, hlast, hdone, hd⟩ := hterminal.runs ω hnext
    cases o with
    | returned ret => exact False.elim hdone
    | normal =>
      exact ⟨out, c + d + 1,
        runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hprefix, hlast, rfl⟩), hdone, by
          simp only [Expr.size] at hc
          omega⟩

/-- After restarting the selected spanner, Algorithm 1 Shift (page 20)
rebuilds the levels strictly below it and then the terminal level. -/
@[expose] def shiftWithSuffix (restart read : ℕ) (level terminal : Stmt) : Stmt :=
  shiftRestartLoadGraph restart read ;; rebuildSuffixProgram level terminal

/-- Compose the restart prefix and the suffix loop once the loaded graph
and prepared level inputs establish the first suffix invariant. -/
theorem shiftWithSuffix_runs {w shifted last restart read prefixCost : ℕ} {p : Program}
    {level terminal : Stmt} {Inv : ℕ → State → Prop} {Done : State → Prop}
    {ω : ℕ → Bool} {st mid : State} (cost : ℕ → ℕ) (terminalCost : ℕ)
    (hprefix : Runs w p ω (shiftRestartLoadGraph restart read) st .normal mid prefixCost)
    (hfirst : st.regs 20 = shifted + 1) (hframe : mid.regs 20 = st.regs 20)
    (horder : shifted < last) (hw : 1 < 2 ^ w) (hword : last < 2 ^ w)
    (hin : Inv (shifted + 1) { mid with regs := Function.update mid.regs 19 (shifted + 1) })
    (hindex : ∀ i current, shifted + 1 ≤ i → i ≤ last → Inv i current → current.regs 19 = i)
    (hstop : ∀ i current, shifted + 1 ≤ i → i ≤ last → Inv i current → current.regs 21 = last)
    (hlevel : ∀ i, shifted + 1 ≤ i → i < last → Triple w p (Inv i) level
      (normalPost fun next => Inv (i + 1) { next with regs := Function.update next.regs 19 (i + 1) } ∧
        next.regs 19 = i) (fun _ => cost i))
    (hterminal : Triple w p (Inv last) terminal (normalPost Done) (fun _ => terminalCost)) :
    ∃ out c, Runs w p ω (shiftWithSuffix restart read level terminal) st .normal out c ∧
      Done out ∧ c ≤ prefixCost + rangeCost cost (shifted + 1) last +
        (last - (shifted + 1)) * 9 + terminalCost + 9 := by
  obtain ⟨out, c, hr, hd, hc⟩ :=
    rebuildSuffixProgram_runs (ω := ω) cost terminalCost (Nat.succ_le_of_lt horder)
      hw hword (hframe.trans hfirst) hin hindex hstop hlevel hterminal
  refine ⟨out, prefixCost + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, prefixCost, c, hprefix, hr, rfl⟩),
    hd, ?_⟩
  change c ≤ rangeCost cost (shifted + 1) last + (last - (shifted + 1)) * 9 + terminalCost + 8 at hc
  omega

/-- Run the linked restart and pass its sparsifier and heap to the
deeper rebuild. The first suffix invariant is supplied by the caller
from the represented prefix and the prepared numerical inputs. -/
theorem shiftWithSuffix_linked_runs {w L k M N vCap eCap init addr branch handle heap shifted last : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph G : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {s : tool.State} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation))
    (ha : st.regs 0 = addr) (hk : st.regs 1 = k)
    (hh : st.regs 3 = handle) (hheap : st.regs 4 = heap)
    (hb : st.mem addr = branch) (hj : branch < k) (hw : k < 2 ^ w)
    (hhandle : handle < 2 ^ w) (haheap : addr < heap) (hsep : ¬ R.foot handle x addr)
    (hrep : R.rep handle s x st.mem)
    (hG : SparseCoreInput tool.toSparseCoreTool tool.restart k s G)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 1 [handle, (branch + 1) % k, heap] + 1 < 2 ^ w)
    {level terminal : Stmt} {Inv : ℕ → State → Prop} {Done : State → Prop}
    (cost : ℕ → ℕ) (terminalCost : ℕ)
    (hfirst : st.regs 20 = shifted + 1) (horder : shifted < last) (hword : last < 2 ^ w)
    (hin : ∀ (mid : State) (ret vc ec : ℕ) (y : R.τ),
      let selected := (branch + 1) % k
      let next := tool.restart s selected
      mid.regs 5 = ret → mid.mem addr = selected →
      R.rep handle next y mid.mem →
      DynGraphAt mid.mem (mid.regs 6) vc ec (tool.S next selected) →
      SparseCoreInput tool.toSparseCoreTool tool.restart k next G →
      (∀ a < heap, ¬ R.foot handle x a → a ≠ addr → mid.mem a = st.mem a) →
      heap ≤ ret → ret ≤ heap + allocation 1 [handle, selected, heap] + 1 →
      ZeroFrom mid.mem ret → (∀ a, R.foot handle y a → a < ret) →
      (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 5 → r ≠ 6 → mid.regs r = st.regs r) →
      Inv (shifted + 1) { mid with regs := Function.update mid.regs 19 (shifted + 1) })
    (hindex : ∀ i current, shifted + 1 ≤ i → i ≤ last → Inv i current → current.regs 19 = i)
    (hstop : ∀ i current, shifted + 1 ≤ i → i ≤ last → Inv i current → current.regs 21 = last)
    (hlevel : ∀ i, shifted + 1 ≤ i → i < last → Triple w p (Inv i) level
      (normalPost fun next => Inv (i + 1) { next with regs := Function.update next.regs 19 (i + 1) } ∧
        next.regs 19 = i) (fun _ => cost i))
    (hterminal : Triple w p (Inv last) terminal (normalPost Done) (fun _ => terminalCost)) :
    ∃ out c, Runs w p ω (shiftWithSuffix (op 1) (op 3) level terminal) st .normal out c ∧
      Done out ∧ c ≤ costs.restartCost M N + R.phi handle x st.mem +
        rangeCost cost (shifted + 1) last + (last - (shifted + 1)) * 9 + terminalCost + 101 := by
  obtain ⟨mid, ret, _, prefixCost, y, hp, hret, _, hcell, hrep', ⟨vc, ec, hg⟩, hc,
    hinput, hframe, hretLo, hretHi, hz', hf', _, _, _, hregs, _⟩ :=
    shiftRestartLoadGraph_runs (ω := ω) himpl ha hk hh hheap hb hj hw hhandle haheap hsep
      hrep hG hfoot hz hroom
  have hstart := hin mid ret vc ec y hret hcell hrep' hg hinput hframe hretLo hretHi hz' hf' hregs
  obtain ⟨out, c, hr, hdone, hcost⟩ :=
    shiftWithSuffix_runs cost terminalCost hp hfirst
      (hregs 20 (by decide) (by decide) (by decide) (by decide))
      horder (by omega) hword hstart hindex hstop hlevel hterminal
  exact ⟨out, c, hr, hdone, by omega⟩

/-- When Shift has a deeper sparse-core level, install it from the
restarted readouts and rebuild the remaining levels (Algorithm 1, page 20). -/
@[expose] def shiftInstalledSuffix
    (restart read forestOp copy sort cell init : ℕ) (level terminal : Stmt) : Stmt :=
  .assign 54 (.reg 21) ;; shiftInstallDeeperLevel restart read forestOp copy sort cell init ;;
    .assign 20 (.bin .add (.reg 53) (.const 1)) ;; .assign 21 (.reg 54) ;;
    rebuildSuffixProgram level terminal

/-- Once level `shifted + 1` is installed, the next loop iteration starts
at `shifted + 2`. An empty remaining sparse-core suffix still runs the
terminal initialization. -/
theorem shiftInstalledSuffix_runs
    {w shifted last restart read forestOp copy sort cell init prefixCost : ℕ}
    {p : Program} {initial mid : State} {ω : ℕ → Bool} {level terminal : Stmt}
    {Inv : ℕ → State → Prop} {Done : State → Prop} (cost : ℕ → ℕ) (terminalCost : ℕ)
    (hprefix : Runs w p ω (shiftInstallDeeperLevel restart read forestOp copy sort cell init)
      { initial with regs := Function.update initial.regs 54 last } .normal mid prefixCost)
    (horder : shifted + 2 ≤ last) (hw : 1 < 2 ^ w) (hword : last < 2 ^ w)
    (hnext : initial.regs 53 = shifted + 1) (hlast : initial.regs 21 = last)
    (hin : Inv (shifted + 2) { mid with regs := Function.update (Function.update (Function.update mid.regs 20 (shifted + 2)) 21 last) 19 (shifted + 2) })
    (hindex : ∀ i current, shifted + 2 ≤ i → i ≤ last → Inv i current → current.regs 19 = i)
    (hstop : ∀ i current, shifted + 2 ≤ i → i ≤ last → Inv i current → current.regs 21 = last)
    (hlevel : ∀ i, shifted + 2 ≤ i → i < last → Triple w p (Inv i) level
      (normalPost fun next =>
        Inv (i + 1) { next with regs := Function.update next.regs 19 (i + 1) } ∧
          next.regs 19 = i) (fun _ => cost i))
    (hterminal : Triple w p (Inv last) terminal (normalPost Done) (fun _ => terminalCost)) :
    ∃ out c, Runs w p ω
        (shiftInstalledSuffix restart read forestOp copy sort cell init level terminal)
        initial .normal out c ∧ Done out ∧
      c ≤ prefixCost + rangeCost cost (shifted + 2) last +
        (last - (shifted + 2)) * 9 + terminalCost + 20 := by
  let saved := { initial with regs := Function.update initial.regs 54 last }
  have hsave : Runs w p ω (.assign 54 (.reg 21)) initial .normal saved 2 :=
    runs_assign_iff.mpr ⟨last, by simp [Expr.eval, hlast], rfl, rfl, rfl⟩
  have hnextMid : mid.regs 53 = shifted + 1 :=
    (shiftInstallDeeperLevel_preserves_regs hprefix (by decide : 51 ≤ 53)).trans
      (by simpa [saved, Function.update_of_ne] using hnext)
  have hlastMid : mid.regs 54 = last :=
    (shiftInstallDeeperLevel_preserves_regs hprefix (by decide : 51 ≤ 54)).trans (by simp)
  let indexed := { mid with regs := Function.update mid.regs 20 (shifted + 2) }
  let ready := { indexed with regs := Function.update indexed.regs 21 last }
  have hfit : shifted + 2 < 2 ^ w := horder.trans_lt hword
  have hset : Runs w p ω (.assign 20 (.bin .add (.reg 53) (.const 1))) mid .normal indexed 4 :=
    runs_assign_iff.mpr ⟨shifted + 2, by simp [Expr.eval, BinOp.eval, hnextMid, hw, hfit],
      rfl, rfl, rfl⟩
  have hrestore : Runs w p ω (.assign 21 (.reg 54)) indexed .normal ready 2 :=
    runs_assign_iff.mpr ⟨last, by simp [Expr.eval, indexed, Function.update_of_ne, hlastMid],
      rfl, rfl, rfl⟩
  obtain ⟨out, c, hrun, hdone, hc⟩ := rebuildSuffixProgram_runs (ω := ω) (st := ready) cost terminalCost
    horder hw hword (by simp [ready, indexed, Function.update_of_ne]) hin hindex hstop hlevel hterminal
  have htail : Runs w p ω (.assign 21 (.reg 54) ;; rebuildSuffixProgram level terminal)
      indexed .normal out (c + 3) :=
    runs_seq_iff.mpr (Or.inr ⟨ready, 2, c, hrestore, hrun, by omega⟩)
  have hloop : Runs w p ω
      (.assign 20 (.bin .add (.reg 53) (.const 1)) ;;
        .assign 21 (.reg 54) ;; rebuildSuffixProgram level terminal)
      mid .normal out (c + 8) :=
    runs_seq_iff.mpr (Or.inr ⟨indexed, 4, c + 3, hset, htail, by omega⟩)
  have hbody : Runs w p ω
      (shiftInstallDeeperLevel restart read forestOp copy sort cell init ;;
        .assign 20 (.bin .add (.reg 53) (.const 1)) ;;
        .assign 21 (.reg 54) ;; rebuildSuffixProgram level terminal)
      saved .normal out (prefixCost + c + 9) :=
    runs_seq_iff.mpr (Or.inr ⟨mid, prefixCost, c + 8, hprefix, hloop, by omega⟩)
  exact ⟨out, prefixCost + c + 12,
    runs_seq_iff.mpr (Or.inr ⟨saved, 2, prefixCost + c + 9, hsave, hbody, by omega⟩),
    hdone, by omega⟩

/-- Shift at a sparse-core level (Algorithm 1, page 20). Register 53
holds the next level, and register 21 holds the terminal level. -/
@[expose] def shiftRebuildAfterRestart
    (restart read forestOp copy sort cell init lastInit : ℕ)
    (level terminal : Stmt) : Stmt :=
  .cond (.bin .lt (.reg 53) (.reg 21))
    (shiftInstalledSuffix restart read forestOp copy sort cell init level terminal)
    (shiftInstallTerminal restart read forestOp lastInit)

/-- Dispatch to the suffix beginning at a sparse-core level or directly
to the terminal rebuild. The comparison adds four steps. -/
theorem shiftRebuildAfterRestart_runs
    {w next last restart read forestOp copy sort cell init lastInit : ℕ}
    {p : Program} {initial out : State} {ω : ℕ → Bool} {c : ℕ} {level terminal : Stmt}
    (hn : initial.regs 53 = next) (hl : initial.regs 21 = last) (hw : 1 < 2 ^ w)
    (hr : Runs w p ω
      (if next < last then shiftInstalledSuffix restart read forestOp copy sort cell init level terminal
        else shiftInstallTerminal restart read forestOp lastInit) initial .normal out c) :
    Runs w p ω (shiftRebuildAfterRestart restart read forestOp copy sort cell init lastInit level terminal)
      initial .normal out (c + 4) := by
  by_cases h : next < last
  · exact runs_cond_iff.mpr ⟨1, c, by simp [Expr.eval, BinOp.eval, hn, hl, h, hw],
      by simpa [h] using hr, by simp [Expr.size]; omega⟩
  · exact runs_cond_iff.mpr ⟨0, c, by simp [Expr.eval, BinOp.eval, hn, hl, h],
      by simpa [h] using hr, by simp [Expr.size]; omega⟩

/-- Set the next level from the shifted level in register 19 before
dispatching its rebuild (Algorithm 1, page 20). -/
@[expose] def shiftRebuildBelow
    (restart read forestOp copy sort cell init lastInit : ℕ)
    (level terminal : Stmt) : Stmt :=
  .assign 53 (.bin .add (.reg 19) (.const 1)) ;;
    shiftRebuildAfterRestart restart read forestOp copy sort cell init lastInit level terminal

/-- The level setup and dispatch add nine steps. The selected body
runs with the original memory and only register 53 updated. -/
theorem shiftRebuildBelow_runs
    {w shifted last restart read forestOp copy sort cell init lastInit : ℕ}
    {p : Program} {initial out : State} {ω : ℕ → Bool} {c : ℕ} {level terminal : Stmt}
    (hi : initial.regs 19 = shifted) (hl : initial.regs 21 = last)
    (horder : shifted < last) (hword : last < 2 ^ w)
    (hr : Runs w p ω
      (if shifted + 1 < last then
        shiftInstalledSuffix restart read forestOp copy sort cell init level terminal
      else shiftInstallTerminal restart read forestOp lastInit)
      { initial with regs := Function.update initial.regs 53 (shifted + 1) } .normal out c) :
    Runs w p ω (shiftRebuildBelow restart read forestOp copy sort cell init lastInit level terminal)
      initial .normal out (c + 9) := by
  let ready := { initial with regs := Function.update initial.regs 53 (shifted + 1) }
  have hw : 1 < 2 ^ w := by omega
  have hnext : shifted + 1 < 2 ^ w := by omega
  have hset : Runs w p ω (.assign 53 (.bin .add (.reg 19) (.const 1))) initial .normal ready 4 :=
    runs_assign_iff.mpr ⟨shifted + 1,
      by simp [Expr.eval, BinOp.eval, hi, hw, hnext], rfl, rfl, rfl⟩
  have hrun := shiftRebuildAfterRestart_runs
    (initial := ready) (by simp [ready]) (by simp [ready, Function.update_of_ne, hl]) hw hr
  exact runs_seq_iff.mpr (Or.inr ⟨ready, 4, c + 4, hset, hrun, by omega⟩)

/-- The fixed dispatch code keeps the saved counter arguments if the
remaining level and terminal bodies write below their registers. -/
theorem shiftRebuildBelow_preserves_counters
    {w restart read forestOp copy sort cell init lastInit c r : ℕ}
    {p : Program} {initial out : State} {ω : ℕ → Bool} {level terminal : Stmt}
    (hLevelRegs : writesBelow 55 level = true) (hTerminalRegs : writesBelow 55 terminal = true)
    (hrun : Runs w p ω
      (shiftRebuildBelow restart read forestOp copy sort cell init lastInit level terminal)
      initial .normal out c)
    (hrBound : 55 ≤ r) : out.regs r = initial.regs r := by
  apply runs_preserves_above hrBound _ hrun
  have hinitRegs :
      writesBelow 55 (shiftInstallDeeperLevel restart read forestOp copy sort cell init) = true := rfl
  have hlastRegs : writesBelow 55 (shiftInstallTerminal restart read forestOp lastInit) = true := rfl
  simp [shiftRebuildBelow, shiftRebuildAfterRestart, shiftInstalledSuffix, rebuildSuffixProgram,
    forRange, forUp, writesBelow, hLevelRegs, hTerminalRegs, hinitRegs, hlastRegs]

/-- Shift dispatches directly to the terminal initializer when level
`i + 1` is terminal, then records the exact model collection. -/
theorem shiftRebuildBelow_terminal_runs
    {w limbs restart read forestOp init vc ec multiplier stretchPrecision i prefixCost handleCell branchCell copy sort cell sparseInit : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {tool : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (hi : i + 1 = P.d)
    {allocation : ℕ → List ℕ → ℕ} {R : DSRep (ℕ × (ℕ → LSF))}
    {p : Program} {op : ℕ → ℕ} {initial mid : State} {ω : ℕ → Bool} {level terminal : Stmt} :
    let next := (algorithm1_shift T tool P chain i).1
    let G := next.G P.d
    let ℓ := next.toTreeChain.chainLen chain.ℓ P.d
    let graph := mid.regs 6
    let lengths := mid.regs 7
    let heap := mid.regs 5
    initial.regs 19 = i → initial.regs 21 = P.d → P.d < 2 ^ w →
    Runs w p ω (shiftRestartGraphAndLengths restart read forestOp)
      { initial with regs := Function.update initial.regs 53 (i + 1) } .normal mid prefixCost →
    R.Implements w p init op (lastLevelRuntimeMachineContract fmt limbs tool G vc ec multiplier stretchPrecision allocation) →
    mid.regs 67 = limbs → mid.regs 68 = fmt.precision →
    limbs < 2 ^ w → fmt.precision < 2 ^ w → fmt.limbBits = 4 → fmt.precision ≤ 4 * limbs →
    DynSpanner.Program.DynGraphAt mid.mem graph vc ec G →
    graph + DynSpanner.Program.dynGraphSize vc ec ≤ heap → lengths + ec * limbs ≤ heap →
    EdgeValuesAt mid.mem lengths fmt.limbBits limbs fmt.precision G.E ℓ →
    (∀ e ∈ G.E, 2 * (2 : ℝ)^stretchPrecision * lastLevelStretchBound G ℓ e <
      Num.capacity fmt.limbBits limbs) →
    (∀ e ∈ G.E, 0 < ℓ e) → (∀ e ∉ G.E, ℓ e = 0) →
    ZeroFrom mid.mem heap → heap + allocation 1 [graph, lengths, limbs, fmt.precision, heap] < 2 ^ w →
    initial.regs 51 = handleCell → initial.regs 52 = branchCell →
    handleCell ≠ branchCell → handleCell < heap → branchCell < heap →
    ∃ out ret cost y, Runs w p ω (shiftRebuildBelow restart read forestOp copy sort cell sparseInit init level terminal)
        initial .normal out cost ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧
      out.regs 4 = ret ∧ R.rep heap (next.lastK, next.lastLSFs) y out.mem ∧
      ZeroFrom out.mem ret ∧
      (∀ a, R.foot heap y a → heap ≤ a ∧ a < ret) ∧
      (∀ r, 54 ≤ r → out.regs r = initial.regs r) ∧
      cost + R.phi heap y out.mem ≤ prefixCost + multiplier * (tool.cost G + 1) + 33 := by
  dsimp only
  intro hindex hlast hword hp himpl hL hP hLWord hPWord hFour hWidth hg hgb hlb hlen hst hpos hagreement hz hroom
    hh hb hne hhBelow hbBelow
  let ready := { initial with regs := Function.update initial.regs 53 (i + 1) }
  obtain ⟨out, ret, c, y, hr, hd, hb', hret, hrep, hz', hfoot, hc⟩ :=
    shiftInstallTerminal_exact_runs (initial := ready) chain hi hp himpl hL hP hLWord hPWord hFour hWidth hg hgb hlb
      hlen hst hpos hagreement hz hroom
      (by simpa [ready, Function.update_of_ne] using hh)
      (by simpa [ready, Function.update_of_ne] using hb) hne hhBelow hbBelow
  have hdispatch := shiftRebuildBelow_runs (level := level) (terminal := terminal)
    (copy := copy) (sort := sort) (cell := cell) (init := sparseInit)
    hindex hlast (by omega) hword (by simpa [ready, hi] using hr)
  refine ⟨out, ret, c + 9, y, hdispatch, hd, hb', hret, hrep, hz', hfoot, ?_, by omega⟩
  intro r hrBound
  exact (shiftInstallTerminal_preserves_regs hr (by omega)).trans
    (by simp [ready, Function.update_of_ne (show r ≠ 53 by omega)])

/-- Dispatch Shift to the sparse-core suffix when the next level is below
the terminal level. This adds nine steps to the suffix cost. -/
theorem shiftRebuildBelow_sparse_runs
    {w shifted last restart read forestOp copy sort cell init lastInit prefixCost : ℕ}
    {p : Program} {initial mid : State} {ω : ℕ → Bool} {level terminal : Stmt}
    {Inv : ℕ → State → Prop} {Done : State → Prop} (cost : ℕ → ℕ) (terminalCost : ℕ)
    (hprefix : Runs w p ω (shiftInstallDeeperLevel restart read forestOp copy sort cell init)
      { initial with regs := Function.update (Function.update initial.regs 53 (shifted + 1)) 54 last } .normal mid prefixCost)
    (horder : shifted + 1 < last) (hword : last < 2 ^ w)
    (hi : initial.regs 19 = shifted) (hlast : initial.regs 21 = last)
    (hin : Inv (shifted + 2) { mid with regs := Function.update (Function.update (Function.update mid.regs 20 (shifted + 2)) 21 last) 19 (shifted + 2) })
    (hindex : ∀ i current, shifted + 2 ≤ i → i ≤ last → Inv i current → current.regs 19 = i)
    (hstop : ∀ i current, shifted + 2 ≤ i → i ≤ last → Inv i current → current.regs 21 = last)
    (hlevel : ∀ i, shifted + 2 ≤ i → i < last → Triple w p (Inv i) level
      (normalPost fun next =>
        Inv (i + 1) { next with regs := Function.update next.regs 19 (i + 1) } ∧
          next.regs 19 = i) (fun _ => cost i))
    (hLevelRegs : writesBelow 55 level = true) (hTerminalRegs : writesBelow 55 terminal = true)
    (hterminal : Triple w p (Inv last) terminal (normalPost Done) (fun _ => terminalCost)) :
    ∃ out c, Runs w p ω
        (shiftRebuildBelow restart read forestOp copy sort cell init lastInit level terminal)
        initial .normal out c ∧ Done out ∧
      (∀ r, 55 ≤ r → out.regs r = initial.regs r) ∧
      c ≤ prefixCost + rangeCost cost (shifted + 2) last +
        (last - (shifted + 2)) * 9 + terminalCost + 29 := by
  let ready := { initial with regs := Function.update initial.regs 53 (shifted + 1) }
  obtain ⟨out, c, hr, hd, hc⟩ := shiftInstalledSuffix_runs (initial := ready) (ω := ω)
    cost terminalCost hprefix (by omega) (by omega) hword
    (by simp [ready]) (by simpa [ready, Function.update_of_ne] using hlast)
    hin hindex hstop hlevel hterminal
  have hdispatch := shiftRebuildBelow_runs (lastInit := lastInit) hi hlast (by omega) hword
    (by simpa [ready, horder] using hr)
  refine ⟨out, c + 9, hdispatch, hd, ?_, by omega⟩
  intro r hrBound
  exact shiftRebuildBelow_preserves_counters hLevelRegs hTerminalRegs hdispatch hrBound

/-- Load the counter arguments from the saved table bases and level indices
in registers 55 through 58. The setup leaves memory intact. -/
@[expose] def loadShiftCounterArgs : Stmt :=
  .assign 0 (.reg 55) ;;
  .assign 1 (.bin .add (.reg 57) (.const 1)) ;;
  .assign 2 (.reg 58) ;;
  .assign 3 (.const 1) ;;
  .assign 4 (.reg 56)

/-- Prepare the counter arguments in sixteen steps. -/
theorem loadShiftCounterArgs_runs {w updates restarts i d : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hu : st.regs 55 = updates) (hr : st.regs 56 = restarts)
    (hi : st.regs 57 = i) (hd : st.regs 58 = d)
    (hword : i + 1 < 2 ^ w) :
    ∃ out, Runs w p ω loadShiftCounterArgs st .normal out 16 ∧
      out.regs 0 = updates ∧ out.regs 1 = i + 1 ∧ out.regs 2 = d ∧
      out.regs 3 = 1 ∧ out.regs 4 = restarts ∧ out.mem = st.mem ∧ out.regs 59 = st.regs 59 := by
  have hw : 1 < 2 ^ w := by omega
  let s1 := { st with regs := Function.update st.regs 0 updates }
  let s2 := { s1 with regs := Function.update s1.regs 1 (i + 1) }
  let s3 := { s2 with regs := Function.update s2.regs 2 d }
  let s4 := { s3 with regs := Function.update s3.regs 3 1 }
  let s5 := { s4 with regs := Function.update s4.regs 4 restarts }
  have h1 : Runs w p ω (.assign 0 (.reg 55)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hu], rfl, rfl, rfl⟩
  have h2 : Runs w p ω (.assign 1 (.bin .add (.reg 57) (.const 1))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s1, Function.update_of_ne, BinOp.eval, hi, hw, hword], rfl, rfl, rfl⟩
  have h3 : Runs w p ω (.assign 2 (.reg 58)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s2, s1, Function.update_of_ne, hd], rfl, rfl, rfl⟩
  have h4 : Runs w p ω (.assign 3 (.const 1)) s3 .normal s4 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hw], rfl, rfl, rfl⟩
  have h5 : Runs w p ω (.assign 4 (.reg 56)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s4, s3, s2, s1, Function.update_of_ne, hr], rfl, rfl, rfl⟩
  refine ⟨s5, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s1, 2, 13, h1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 4, 8, h2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 2, 5, h3,
          runs_seq_iff.mpr (Or.inr ⟨s4, 2, 2, h4, h5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  all_goals simp [s5, s4, s3, s2, s1, Function.update_of_ne]

/-- Finish a nonterminal Shift by updating the received-update and
restart tables after rebuilding the lower levels (Algorithm 1, page 20).
The setup supplies the counter routine's arguments from the chain state. -/
@[expose] def shiftRebuildWithCounters
    (restart read forestOp copy sort cell init lastInit : ℕ)
    (level terminal : Stmt) : Stmt :=
  shiftRebuildBelow restart read forestOp copy sort cell init lastInit level terminal ;;
    .assign 59 (.reg 4) ;; loadShiftCounterArgs ;; shiftLevelCounters ;; .assign 4 (.reg 59)

/-- Sequence the Shift rebuild and counter writes. Cells outside the
counter intervals keep their values from the counter setup. -/
theorem shiftRebuildWithCounters_runs
    {T : SparseCoreRestartTool} {L : LastLevelTool} {P : ChainParams}
    (chain : ChainState T P) (i : Fin P.d)
    {w updates restarts restart read forestOp copy sort cell init lastInit
      rebuildCost : ℕ}
    {p : Program} {initial rebuilt : State} {ω : ℕ → Bool}
    {level terminal : Stmt}
    (hr : Runs w p ω
      (shiftRebuildBelow restart read forestOp copy sort cell init lastInit level terminal)
      initial .normal rebuilt rebuildCost)
    (hLevelRegs : writesBelow 55 level = true) (hTerminalRegs : writesBelow 55 terminal = true)
    (hUpdates : initial.regs 55 = updates) (hRestarts : initial.regs 56 = restarts)
    (hShifted : initial.regs 57 = i.val) (hDepth : initial.regs 58 = P.d)
    (hu : ∀ j : Fin P.d, rebuilt.mem (updates + j.val) = chain.updCount j.val)
    (hrr : ∀ j : Fin P.d, rebuilt.mem (restarts + j.val) = chain.curRestarts j.val)
    (hdisjoint : updates + P.d ≤ restarts ∨ restarts + P.d ≤ updates)
    (hub : updates + P.d < 2 ^ w) (hrb : restarts + P.d < 2 ^ w) (hw : 1 < 2 ^ w)
    (hnext : chain.curRestarts i.val + 1 < 2 ^ w) :
    let next := (algorithm1_shift T L P chain i.val).1
    ∃ out cost, Runs w p ω
        (shiftRebuildWithCounters restart read forestOp copy sort cell init lastInit
          level terminal) initial .normal out cost ∧
      cost ≤ rebuildCost + 28 * (P.d - (i.val + 1)) + 65 ∧ out.regs 4 = rebuilt.regs 4 ∧
      (∀ j : Fin P.d, out.mem (updates + j.val) = next.updCount j.val) ∧
      (∀ j : Fin P.d, out.mem (restarts + j.val) = next.curRestarts j.val) ∧
      (∀ a, (a < updates + (i.val + 1) ∨ updates + P.d ≤ a) →
        (a < restarts + i.val ∨ restarts + P.d ≤ a) → out.mem a = rebuilt.mem a) ∧
      (updates + P.d ≤ rebuilt.regs 4 → restarts + P.d ≤ rebuilt.regs 4 →
        ZeroFrom rebuilt.mem (rebuilt.regs 4) → ZeroFrom out.mem (out.regs 4)) ∧
      (∀ (σ : Type) (R : DSRep σ) (handle : ℕ) (state : σ) (x : R.τ),
        R.Local → R.rep handle state x rebuilt.mem →
        (∀ a, R.foot handle x a →
          (a < updates + (i.val + 1) ∨ updates + P.d ≤ a) ∧
          (a < restarts + i.val ∨ restarts + P.d ≤ a)) →
        R.rep handle state x out.mem ∧ R.phi handle x out.mem = R.phi handle x rebuilt.mem) := by
  have hregs {r : ℕ} (hb : 55 ≤ r) := shiftRebuildBelow_preserves_counters hLevelRegs hTerminalRegs hr hb
  have hword : i.val + 1 < 2 ^ w := by have := i.isLt; omega
  let saved := { rebuilt with regs := Function.update rebuilt.regs 59 (rebuilt.regs 4) }
  have hsave : Runs w p ω (.assign 59 (.reg 4)) rebuilt .normal saved 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  obtain ⟨ready, hs, hb, hi, hend, hflag, hrbase, hsetup, hsaved⟩ :=
    loadShiftCounterArgs_runs (p := p) (ω := ω) (st := saved)
      (by simpa [saved, Function.update_of_ne] using (hregs (r := 55) (by decide)).trans hUpdates)
      (by simpa [saved, Function.update_of_ne] using (hregs (r := 56) (by decide)).trans hRestarts)
      (by simpa [saved, Function.update_of_ne] using (hregs (r := 57) (by decide)).trans hShifted)
      (by simpa [saved, Function.update_of_ne] using (hregs (r := 58) (by decide)).trans hDepth) hword
  obtain ⟨out, c, hc, hcost, _, hupdate, hrestart, hframe⟩ :=
    shiftLevelCounters_runs (L := L) (ω := ω) chain i hb hi hend hflag hrbase
      (hsetup.symm ▸ hu) (hsetup.symm ▸ hrr) hdisjoint hub hrb hw hnext
  have hheap : out.regs 59 = rebuilt.regs 4 :=
    (shiftLevelCounters_preserves_heap_slot hc).trans (hsaved.trans (by simp [saved]))
  let final := { out with regs := Function.update out.regs 4 (rebuilt.regs 4) }
  have hrestore : Runs w p ω (.assign 4 (.reg 59)) out .normal final 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hheap], rfl, rfl, rfl⟩
  have htail : Runs w p ω (shiftLevelCounters ;; .assign 4 (.reg 59))
      ready .normal final (c + 3) :=
    runs_seq_iff.mpr (Or.inr ⟨out, c, 2, hc, hrestore, by omega⟩)
  have hargs : Runs w p ω (loadShiftCounterArgs ;; shiftLevelCounters ;; .assign 4 (.reg 59))
      saved .normal final (c + 20) :=
    runs_seq_iff.mpr (Or.inr ⟨ready, 16, c + 3, hs, htail, by omega⟩)
  refine ⟨final, rebuildCost + c + 24,
    runs_seq_iff.mpr (Or.inr ⟨rebuilt, rebuildCost, c + 23, hr,
      runs_seq_iff.mpr (Or.inr ⟨saved, 2, c + 20, hsave, hargs, by omega⟩), by omega⟩),
    by omega, by simp [final], hupdate, hrestart, ?_, ?_, ?_⟩
  · simpa only [hsetup] using hframe
  · intro huEnd hrEnd hz a ha
    have ha' : rebuilt.regs 4 ≤ a := by simpa [final] using ha
    exact (hframe a (Or.inr (huEnd.trans ha')) (Or.inr (hrEnd.trans ha'))).trans ((congrFun hsetup a).trans (hz a ha'))
  · intro σ R handle state x hlocal hrep hsep
    have hkeep := hlocal handle state x rebuilt.mem final.mem fun a ha =>
      (congrFun hsetup a).symm.trans (hframe a (hsep a ha).1 (hsep a ha).2).symm
    exact ⟨hkeep.1 hrep, hkeep.2.symm⟩

end MinCostFlow.MinRatio
