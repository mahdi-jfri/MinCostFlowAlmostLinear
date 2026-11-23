module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRefreshKFBL
public import MinCostFlow.MinRatio.WireChainCoreOps
import WordRAM.Tactic

/-!
# The last part of the interior rebuild step under `KFBL` (`WireChainCoreBranchBIntTailKFBL`)

After the suffix rebuild at level `idx`, the interior rebuild step of Branch B zeroes the update
counters of the rebuilt levels `idx, …, d - 1`, sets the flag `reg 97` that ends the loop, stores
the first rebuilt level `idx` at the select base `reg 72` (the word `mem heap = firstReb` of
`UpdateCoreSelectOutAt`), and reads the descriptor of level `idx - 1` again
(`wireBranchBRefreshDescStmt`), since op `5` ran on that core after its step. This file gives that
part, `wireBranchBIntTailKFBL`, and its run lemma `wireBranchBIntTailKFBL_runs`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- Zero the update counters from level `idx = reg 96` on, set `reg 97 := 1`, store `idx` at the
select base `reg 72`, and read the descriptor of level `idx - 1` again. -/
@[expose] def wireBranchBIntTailKFBL (readLSF : ℕ) : Stmt :=
  .assign 20 (.reg 96) ;;
  wireZeroUpdCountLoop ;;
  .assign 97 (.const 1) ;;
  .store (.reg 72) (.reg 96) ;;
  .assign 22 (.bin .sub (.reg 96) (.const 1)) ;;
  wireBranchBRefreshDescStmt readLSF

theorem wireBranchBIntTailKFBL_noRand (readLSF : ℕ) :
    (wireBranchBIntTailKFBL readLSF).NoRand := by
  simp [wireBranchBIntTailKFBL, wireZeroUpdCountLoop_noRand, wireBranchBRefreshDescStmt_noRand,
    Stmt.NoRand]

section Execution

variable {w L depth k M N vCap eCap capExp : ℕ} {fmt : Num.Format w}
  {tool : SparseCoreRestartTool} {initialGraph : MGraph} {Psc : SparseCoreOrdParams}
  {allocation : ℕ → List ℕ → ℕ} {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ}

set_option maxHeartbeats 800000 in
/-- One run of `wireBranchBIntTailKFBL` at level `idx ≤ d`, with the heap pointer
`cur = reg 4`. The refresh reads core `j = idx - 1`. Below `cur`, the part writes only the
counters of the levels `idx, …, d - 1`, the select base, the footprint of core `j` and the two
descriptor words of the slot of level `j`. -/
theorem wireBranchBIntTailKFBL_runs {d idx selBase ucBase cur handleBase branchBase levelMeta
      handle branch graph : ℕ}
    {a : SparseCoreOrdAbs tool} {x : R.τ} {st : State} {ω : ℕ → Bool}
    (hLocal : R.Local)
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp Psc
      allocation R p op)
    (hRegs : st.regs 4 = cur ∧ st.regs 72 = selBase ∧ st.regs 75 = d ∧ st.regs 77 = handleBase ∧
      st.regs 78 = branchBase ∧ st.regs 83 = levelMeta ∧ st.regs 85 = ucBase ∧ st.regs 96 = idx)
    (hIdxLe : idx ≤ d) (hUCW : ucBase + d < 2 ^ w)
    (hCells : st.mem (handleBase + (idx - 1)) = handle ∧
      st.mem (branchBase + (idx - 1)) = branch ∧ st.mem (levelMeta + d + (idx - 1)) = graph)
    (hAddrW : handleBase + (idx - 1) < 2 ^ w ∧ branchBase + (idx - 1) < 2 ^ w ∧
      levelMeta + d + (idx - 1) < 2 ^ w)
    (hb : branch < k) (hkw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hG : DynGraphAt st.mem graph vCap eCap a.G)
    (hgEnd : graph + dynGraphSize vCap eCap ≤ cur)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ z, R.foot handle x z → z < cur) (hz : ZeroFrom st.mem cur)
    (hroom : cur + 7 < 2 ^ w)
    (hSlotLt : selBase + 1 + 12 * (idx - 1) + 9 < cur)
    (hSlotOff : ¬ R.foot handle x (selBase + 1 + 12 * (idx - 1) + 8) ∧
      ¬ R.foot handle x (selBase + 1 + 12 * (idx - 1) + 9))
    (hWr : ∀ z, (ucBase + idx ≤ z ∧ z < ucBase + d) ∨ z = selBase →
      z < cur ∧ ¬ R.foot handle x z ∧ (z < graph ∨ graph + dynGraphSize vCap eCap ≤ z) ∧
      z ≠ handleBase + (idx - 1) ∧ z ≠ branchBase + (idx - 1) ∧
      z ≠ levelMeta + d + (idx - 1) ∧ z ≠ selBase + 1 + 12 * (idx - 1) + 8 ∧
      z ≠ selBase + 1 + 12 * (idx - 1) + 9)
    (hSelUC : selBase < ucBase + idx ∨ ucBase + d ≤ selBase) :
    ∃ (out : State) (cost ret : ℕ) (y : R.τ),
      Runs w p ω (wireBranchBIntTailKFBL (op 2)) st .normal out cost ∧
      cur ≤ ret ∧ ret ≤ cur + 5 ∧ out.regs 4 = cur + 7 ∧ out.regs 97 = 1 ∧
      (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 22 →
        r ≠ 30 → r ≠ 31 → r ≠ 32 → r ≠ 33 → r ≠ 97 → out.regs r = st.regs r) ∧
      R.rep handle a y out.mem ∧
      (∀ z, R.foot handle y z → R.foot handle x z ∨ (cur ≤ z ∧ z < ret)) ∧
      ZeroFrom out.mem (cur + 7) ∧
      out.mem selBase = idx ∧
      (∀ j, idx ≤ j → j < d → out.mem (ucBase + j) = 0) ∧
      (∀ z < cur, ¬ R.foot handle x z → (z < ucBase + idx ∨ ucBase + d ≤ z) → z ≠ selBase →
        z ≠ selBase + 1 + 12 * (idx - 1) + 8 → z ≠ selBase + 1 + 12 * (idx - 1) + 9 →
        out.mem z = st.mem z) ∧
      out.mem (selBase + 1 + 12 * (idx - 1) + 8) = cur + 5 ∧
      out.mem (selBase + 1 + 12 * (idx - 1) + 9) ≤ ordLevelLwMax L capExp M N ∧
      StretchValuesAt out.mem (cur + 5) fmt.limbBits (out.mem (selBase + 1 + 12 * (idx - 1) + 9))
        fmt.precision a.G.E (tool.lsfs a.st branch).wstr ∧
      SelOutTableAt w (R.foot handle y) cur (cur + 5) out.mem (cur + 5)
        (out.mem (selBase + 1 + 12 * (idx - 1) + 9)) a.G.E ∧
      SelOutTableAt w (R.foot handle y) cur (cur + 5) out.mem (cur + 5 + 1)
        (out.mem (selBase + 1 + 12 * (idx - 1) + 9)) a.G.E ∧
      cost + R.phi handle y out.mem ≤
        Psc.readout + 15 * (d - idx) + 160 + R.phi handle x st.mem := by
  obtain ⟨hr4, hr72, hr75, hr77, hr78, hr83, hr85, hr96⟩ := hRegs
  obtain ⟨hHC, hBC, hGC⟩ := hCells
  have hw1 : 1 < 2 ^ w := by omega
  -- Step 1: the counters
  let s1 := { st with regs := Function.update st.regs 20 idx }
  have r1 : Runs w p ω (.assign 20 (.reg 96)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨idx, by simp [Expr.eval, hr96], rfl, rfl, rfl⟩
  obtain ⟨s2, cZ, r2, hcZ, hZ2, hfr2, hregs2⟩ :=
    wireZeroUpdCountLoop_runs (w := w) (first := idx) (d := d) (updCountBase := ucBase) (p := p)
      (ω := ω) (st := s1) (by simp [s1]) (by simp [s1, hr75]) (by simp [s1, hr85]) hIdxLe hUCW hw1
  -- Step 2: the flag, the first rebuilt level and the level of the refresh
  let s3 := { s2 with regs := Function.update s2.regs 97 1 }
  have r3 : Runs w p ω (.assign 97 (.const 1)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
  have hs2r (r : ℕ) (h19 : r ≠ 19) (h20 : r ≠ 20) : s2.regs r = st.regs r := by
    rw [hregs2 r h19]; simp [s1, Function.update_of_ne h20]
  let s4 := { s3 with mem := Function.update s3.mem selBase idx }
  have r4 : Runs w p ω (.store (.reg 72) (.reg 96)) s3 .normal s4 3 :=
    runs_store_iff.mpr ⟨selBase, idx, by
      simp [Expr.eval, s3, hs2r 72 (by decide) (by decide), hr72], by
      simp [Expr.eval, s3, hs2r 96 (by decide) (by decide), hr96], rfl, rfl, rfl⟩
  let s5 := { s4 with regs := Function.update s4.regs 22 (idx - 1) }
  have r5 : Runs w p ω (.assign 22 (.bin .sub (.reg 96) (.const 1))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨idx - 1, by
      simp [Expr.eval, BinOp.eval, s4, s3, hs2r 96 (by decide) (by decide), hr96, hw1,
        show idx - 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hs5r (r : ℕ) (h19 : r ≠ 19) (h20 : r ≠ 20) (h22 : r ≠ 22) (h97 : r ≠ 97) :
      s5.regs r = st.regs r := by
    simp only [s5, s4, s3, Function.update_of_ne h22, Function.update_of_ne h97]
    exact hs2r r h19 h20
  -- the memory before the refresh
  have hm5 (z : ℕ) (h1 : z < ucBase + idx ∨ ucBase + d ≤ z) (h2 : z ≠ selBase) :
      s5.mem z = st.mem z := by
    show Function.update s2.mem selBase idx z = st.mem z
    rw [Function.update_of_ne h2]
    exact hfr2 z h1
  have hOk (z : ℕ) (hz1 : ¬ ((ucBase + idx ≤ z ∧ z < ucBase + d) ∨ z = selBase)) :
      s5.mem z = st.mem z := hm5 z (by omega) (fun h => hz1 (Or.inr h))
  have hneW (z : ℕ) (hf : ¬ (z < graph ∨ graph + dynGraphSize vCap eCap ≤ z) ∨ R.foot handle x z ∨
      z = handleBase + (idx - 1) ∨ z = branchBase + (idx - 1) ∨ z = levelMeta + d + (idx - 1) ∨
      cur ≤ z) : ¬ ((ucBase + idx ≤ z ∧ z < ucBase + d) ∨ z = selBase) := fun hw => by
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hWr z hw
    rcases hf with h | h | h | h | h | h
    · exact h h3
    · exact h2 h
    · exact h4 h
    · exact h5 h
    · exact h6 h
    · omega
  have hLoc5 := hLocal handle a x st.mem s5.mem fun z hf =>
    (hOk z (hneW z (Or.inr (Or.inl hf)))).symm
  -- Step 3: the refresh at `j = idx - 1`
  obtain ⟨s6, c6, ret, y, r6, hret1, hret2, h6_4, h6_regs, hrep6, hfoot6, hz6, hfr6, h68, h69,
      hSV6, hT06, hT16, hc6⟩ :=
    wireBranchBRefreshDescStmt_runs (d := d) (j := idx - 1) (selBase := selBase) (cur := cur)
      (handleBase := handleBase) (branchBase := branchBase) (levelMeta := levelMeta)
      (handle := handle) (branch := branch) (graph := graph) (st := s5) (ω := ω) hLocal hFootAt
      ⟨(hs5r 4 (by decide) (by decide) (by decide) (by decide)).trans hr4, by simp [s5],
        (hs5r 72 (by decide) (by decide) (by decide) (by decide)).trans hr72,
        (hs5r 75 (by decide) (by decide) (by decide) (by decide)).trans hr75,
        (hs5r 77 (by decide) (by decide) (by decide) (by decide)).trans hr77,
        (hs5r 78 (by decide) (by decide) (by decide) (by decide)).trans hr78,
        (hs5r 83 (by decide) (by decide) (by decide) (by decide)).trans hr83⟩
      ⟨(hOk _ (hneW _ (Or.inr (Or.inr (Or.inl rfl))))).trans hHC,
        (hOk _ (hneW _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).trans hBC,
        (hOk _ (hneW _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))).trans hGC⟩
      hAddrW hb hkw hhw
      (dynGraphAt_of_agree hG fun z h1 h2 => hOk z (hneW z (Or.inl (by omega))))
      hgEnd (hLoc5.1 hrep) hIn hfoot
      (fun z hz' => (hOk z (hneW z (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hz'))))))).trans
        (hz z hz'))
      hroom hSlotLt hSlotOff
  have hrun : Runs w p ω (wireBranchBIntTailKFBL (op 2)) st .normal s6 (cZ + c6 + 16) := by
    unfold wireBranchBIntTailKFBL
    exact runs_seq_iff.mpr (Or.inr ⟨s1, _, _, r1, runs_seq_iff.mpr (Or.inr ⟨s2, _, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, _, _, r3, runs_seq_iff.mpr (Or.inr ⟨s4, _, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, _, _, r5, r6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)
  -- the new words written before the refresh stay
  have hSelNe8 : selBase ≠ selBase + 1 + 12 * (idx - 1) + 8 := by omega
  have hSelNe9 : selBase ≠ selBase + 1 + 12 * (idx - 1) + 9 := by omega
  have hSelLt : selBase < cur := (hWr selBase (Or.inr rfl)).1
  refine ⟨s6, cZ + c6 + 16, ret, y, hrun, hret1, hret2, h6_4, ?_, ?_, hrep6, hfoot6, hz6, ?_,
    ?_, ?_, h68, h69, hSV6, hT06, hT16, ?_⟩
  · rw [h6_regs 97 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s5, s4, s3]
  · intro r h2 h3 h4 h5 h6 h18 h19 h20 h22 h30 h31 h32 h33 h97
    rw [h6_regs r h2 h3 h4 h5 h6 h18 h19 h30 h31 h32 h33]
    exact hs5r r h19 h20 h22 h97
  · rw [hfr6 selBase hSelLt (hWr selBase (Or.inr rfl)).2.1 hSelNe8 hSelNe9]
    simp [s5, s4]
  · intro j hj1 hj2
    have hw' := hWr (ucBase + j) (Or.inl ⟨by omega, by omega⟩)
    rw [hfr6 _ hw'.1 hw'.2.1 hw'.2.2.2.2.2.2.1 hw'.2.2.2.2.2.2.2]
    show Function.update s2.mem selBase idx (ucBase + j) = 0
    rw [Function.update_of_ne (by omega)]
    exact hZ2 j hj1 hj2
  · intro z hz' hn h1 h2 h8 h9
    rw [hfr6 z hz' hn h8 h9]
    exact hm5 z h1 h2
  · have hc6' : c6 + R.phi handle y s6.mem ≤ Psc.readout + 120 + R.phi handle x s5.mem := hc6
    rw [← hLoc5.2] at hc6'
    omega

end Execution

end MinCostFlow.MinRatio
