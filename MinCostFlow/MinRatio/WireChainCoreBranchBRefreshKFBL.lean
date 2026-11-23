module

public import MinCostFlow.MinRatio.WireChainCoreBranchBDescKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBDoneKFBL
import WordRAM.Tactic

/-!
# A new read of the descriptor of the last finished level (`WireChainCoreBranchBRefreshKFBL`)

The stretch tables of a finished level lie in the footprint of its core, and every op on that core
may rewrite its footprint. In Branch B, the cores of the finished levels see no op after their
step, but one: when level `idx` is rebuilt, the core of level `idx - 1` runs op `5` (the interior
rebuild) or ops `3`, `2`, `5` (the terminal step) after its step. Then the tables that the slot of
level `idx - 1` names may be gone.

So after the last op on that core, the chain-update core reads the descriptor again. The statement
`wireBranchBRefreshDescStmt` loads the handle, the branch and the graph of level `j = reg 22`, runs
`wireBranchBReadDescStmt` (op `2` and the copy of the two descriptor words to fresh heap), and
stores the new descriptor and its width into words `8` and `9` of the slot of level `j`.
`wireBranchBRefreshDescStmt_runs` gives its run, and `BranchBDoneSlots.refresh`
(`WireChainCoreBranchBDoneKFBL.lean`) turns its output into the finished-level clause of level `j`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- Read the descriptor of level `j = reg 22` again and store it into the slot of the level:
words `8`, `9` of `reg 72 + 1 + 12 j` get the new descriptor `cur + 5` and the width of its
tables. -/
@[expose] def wireBranchBRefreshDescStmt (readLSF : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 77) (.reg 22))) ;;
  .assign 2 (.load (.bin .add (.reg 78) (.reg 22))) ;;
  .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 22))) ;;
  wireBranchBReadDescStmt readLSF ;;
  .assign 33 (.bin .add (.bin .add (.reg 72) (.const 1)) (.bin .mul (.const 12) (.reg 22))) ;;
  .store (.bin .add (.reg 33) (.const 8)) (.reg 31) ;;
  .store (.bin .add (.reg 33) (.const 9)) (.reg 32)

theorem wireBranchBRefreshDescStmt_noRand (readLSF : ℕ) :
    (wireBranchBRefreshDescStmt readLSF).NoRand := by
  simp [wireBranchBRefreshDescStmt, wireBranchBReadDescStmt_noRand, Stmt.NoRand]

/-- `SelOutTableAt` reads the memory only at its base word. -/
theorem selOutTableAt_congr_base {w lo hi a Lw : ℕ} {F : ℕ → Prop} {mem mem' : ℕ → ℕ}
    {E : Finset ℕ} (h : SelOutTableAt w F lo hi mem a Lw E) (ha : mem' a = mem a) :
    SelOutTableAt w F lo hi mem' a Lw E := by
  unfold SelOutTableAt at h ⊢
  rw [ha]
  exact h

section Execution

variable {w L depth k M N vCap eCap capExp : ℕ} {fmt : Num.Format w}
  {tool : SparseCoreRestartTool} {initialGraph : MGraph} {Psc : SparseCoreOrdParams}
  {allocation : ℕ → List ℕ → ℕ} {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ}

set_option maxHeartbeats 800000 in
/-- One run of `wireBranchBRefreshDescStmt` at level `j`, with the heap pointer `cur = reg 4`.
Below `cur` it writes only the footprint of core `j` and the two descriptor words of the slot of
level `j`. Afterwards word `8` of the slot holds `cur + 5`, a descriptor off the footprint, word
`9` the width of its tables, and the rows of the two tables lie in the new footprint or in
`[cur, ret)`, with `ret ≤ cur + 5`. -/
theorem wireBranchBRefreshDescStmt_runs {d j selBase cur handleBase branchBase levelMeta handle
      branch graph : ℕ}
    {a : SparseCoreOrdAbs tool} {x : R.τ} {st : State} {ω : ℕ → Bool}
    (hLocal : R.Local)
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp Psc
      allocation R p op)
    (hRegs : st.regs 4 = cur ∧ st.regs 22 = j ∧ st.regs 72 = selBase ∧ st.regs 75 = d ∧
      st.regs 77 = handleBase ∧ st.regs 78 = branchBase ∧ st.regs 83 = levelMeta)
    (hCells : st.mem (handleBase + j) = handle ∧ st.mem (branchBase + j) = branch ∧
      st.mem (levelMeta + d + j) = graph)
    (hAddrW : handleBase + j < 2 ^ w ∧ branchBase + j < 2 ^ w ∧ levelMeta + d + j < 2 ^ w)
    (hb : branch < k) (hkw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hG : DynGraphAt st.mem graph vCap eCap a.G)
    (hgEnd : graph + dynGraphSize vCap eCap ≤ cur)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ z, R.foot handle x z → z < cur) (hz : ZeroFrom st.mem cur)
    (hroom : cur + 7 < 2 ^ w)
    (hSlotLt : selBase + 1 + 12 * j + 9 < cur)
    (hSlotOff : ¬ R.foot handle x (selBase + 1 + 12 * j + 8) ∧
      ¬ R.foot handle x (selBase + 1 + 12 * j + 9)) :
    ∃ (out : State) (cost ret : ℕ) (y : R.τ),
      Runs w p ω (wireBranchBRefreshDescStmt (op 2)) st .normal out cost ∧
      cur ≤ ret ∧ ret ≤ cur + 5 ∧ out.regs 4 = cur + 7 ∧
      (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 18 → r ≠ 19 → r ≠ 30 → r ≠ 31 →
        r ≠ 32 → r ≠ 33 → out.regs r = st.regs r) ∧
      R.rep handle a y out.mem ∧
      (∀ z, R.foot handle y z → R.foot handle x z ∨ (cur ≤ z ∧ z < ret)) ∧
      ZeroFrom out.mem (cur + 7) ∧
      (∀ z < cur, ¬ R.foot handle x z → z ≠ selBase + 1 + 12 * j + 8 →
        z ≠ selBase + 1 + 12 * j + 9 → out.mem z = st.mem z) ∧
      out.mem (selBase + 1 + 12 * j + 8) = cur + 5 ∧
      out.mem (selBase + 1 + 12 * j + 9) ≤ ordLevelLwMax L capExp M N ∧
      StretchValuesAt out.mem (cur + 5) fmt.limbBits (out.mem (selBase + 1 + 12 * j + 9))
        fmt.precision a.G.E (tool.lsfs a.st branch).wstr ∧
      SelOutTableAt w (R.foot handle y) cur (cur + 5) out.mem (cur + 5)
        (out.mem (selBase + 1 + 12 * j + 9)) a.G.E ∧
      SelOutTableAt w (R.foot handle y) cur (cur + 5) out.mem (cur + 5 + 1)
        (out.mem (selBase + 1 + 12 * j + 9)) a.G.E ∧
      cost + R.phi handle y out.mem ≤ Psc.readout + 120 + R.phi handle x st.mem := by
  obtain ⟨hr4, hr22, hr72, hr75, hr77, hr78, hr83⟩ := hRegs
  obtain ⟨hHC, hBC, hGC⟩ := hCells
  obtain ⟨hHW, hBW, hGW⟩ := hAddrW
  obtain ⟨hOff8, hOff9⟩ := hSlotOff
  -- the three loads
  let s1 := { st with regs := Function.update st.regs 3 handle }
  let s2 := { s1 with regs := Function.update s1.regs 2 branch }
  let s3 := { s2 with regs := Function.update s2.regs 6 graph }
  have r1 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 77) (.reg 22)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, BinOp.eval, hr77, hr22, hHW, hHC],
      rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 78) (.reg 22)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨branch, by simp [Expr.eval, BinOp.eval, s1, hr78, hr22, hBW, hBC],
      rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 22))))
      s2 .normal s3 7 :=
    runs_assign_iff.mpr ⟨graph, by simp [Expr.eval, BinOp.eval, s2, s1, hr83, hr75, hr22,
      show levelMeta + d < 2 ^ w by omega, hGW, hGC], rfl, rfl, rfl⟩
  have hs3 (r : ℕ) (h2 : r ≠ 2) (h3 : r ≠ 3) (h6 : r ≠ 6) : s3.regs r = st.regs r := by
    simp [s3, s2, s1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h6]
  -- op `2` and the copy of the descriptor
  obtain ⟨s4, ret, c4, y, r4, hret1, hret2, h44, -, h431, h432, hregs4, hrep4, hfoot4, hz4,
      hfr4, hLw4, hSV4, hT04, hT14, -, hc4⟩ :=
    wireBranchBReadDescStmt_runs (ω := ω) (st := s3) (branch := branch) (handle := handle)
      (graph := graph) (cur := cur) hLocal hFootAt (by simp [s3, s2]) (by simp [s3, s2, s1])
      (by simp [s3]) ((hs3 4 (by omega) (by omega) (by omega)).trans hr4) hb hkw hhw hG hgEnd
      hrep hIn hfoot hz hroom
  have h472 : s4.regs 72 = selBase :=
    (hregs4 72 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      ((hs3 72 (by omega) (by omega) (by omega)).trans hr72)
  have h422 : s4.regs 22 = j :=
    (hregs4 22 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      ((hs3 22 (by omega) (by omega) (by omega)).trans hr22)
  -- the slot address and the two stores
  set slot := selBase + 1 + 12 * j with hslot
  let s5 := { s4 with regs := Function.update s4.regs 33 slot }
  have r5 : Runs w p ω
      (.assign 33 (.bin .add (.bin .add (.reg 72) (.const 1)) (.bin .mul (.const 12) (.reg 22))))
      s4 .normal s5 8 :=
    runs_assign_iff.mpr ⟨slot, by
      simp [Expr.eval, BinOp.eval, h472, h422, show 1 < 2 ^ w by omega,
        show selBase + 1 < 2 ^ w by omega, show 12 < 2 ^ w by omega,
        show 12 * j < 2 ^ w by omega, show selBase + 1 + 12 * j < 2 ^ w by omega, hslot], rfl, rfl,
      rfl⟩
  let s6 := { s5 with mem := Function.update s5.mem (slot + 8) (cur + 5) }
  have r6 : Runs w p ω (.store (.bin .add (.reg 33) (.const 8)) (.reg 31)) s5 .normal s6 5 :=
    runs_store_iff.mpr ⟨slot + 8, cur + 5, by
      simp [Expr.eval, BinOp.eval, s5, show 8 < 2 ^ w by omega, show slot + 8 < 2 ^ w by omega],
      by simp [Expr.eval, s5, h431], rfl, rfl, rfl⟩
  let s7 := { s6 with mem := Function.update s6.mem (slot + 9) (s4.mem (cur + 4)) }
  have r7 : Runs w p ω (.store (.bin .add (.reg 33) (.const 9)) (.reg 32)) s6 .normal s7 5 :=
    runs_store_iff.mpr ⟨slot + 9, s4.mem (cur + 4), by
      simp [Expr.eval, BinOp.eval, s6, s5, show 9 < 2 ^ w by omega,
        show slot + 9 < 2 ^ w by omega],
      by simp [Expr.eval, s6, s5, h432], rfl, rfl, rfl⟩
  have hrun : Runs w p ω (wireBranchBRefreshDescStmt (op 2)) st .normal s7 (c4 + 41) := by
    unfold wireBranchBRefreshDescStmt
    exact runs_seq_iff.mpr (Or.inr ⟨s1, _, _, r1, runs_seq_iff.mpr (Or.inr ⟨s2, _, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, _, _, r3, runs_seq_iff.mpr (Or.inr ⟨s4, _, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, _, _, r5, runs_seq_iff.mpr (Or.inr ⟨s6, _, _, r6, r7,
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)
  -- the final memory
  have hm7 (z : ℕ) (h8 : z ≠ slot + 8) (h9 : z ≠ slot + 9) : s7.mem z = s4.mem z := by
    simp [s7, s6, s5, Function.update_of_ne h8, Function.update_of_ne h9]
  have hm78 : s7.mem (slot + 8) = cur + 5 := by
    simp [s7, s6, s5]
  have hm79 : s7.mem (slot + 9) = s4.mem (cur + 4) := by simp [s7]
  -- a word of the new footprint or of `[cur, ret)` is not one of the two slot words
  have hne (z : ℕ) (hz' : R.foot handle y z ∨ (cur ≤ z ∧ z < ret)) :
      z ≠ slot + 8 ∧ z ≠ slot + 9 := by
    have hz2 : R.foot handle x z ∨ cur ≤ z := by
      rcases hz' with hf | ⟨h1, _⟩
      · exact (hfoot4 z hf).imp id fun h => h.1
      · exact Or.inr h1
    constructor
    · rintro rfl
      rcases hz2 with hf | h
      · exact hOff8 hf
      · omega
    · rintro rfl
      rcases hz2 with hf | h
      · exact hOff9 hf
      · omega
  have hloc := hLocal handle a y s4.mem s7.mem fun z hf =>
    (hm7 z (hne z (Or.inl hf)).1 (hne z (Or.inl hf)).2).symm
  have hrow0 : ∀ e ∈ a.G.E, ∀ t < s4.mem (cur + 4),
      s7.mem (s4.mem (cur + 5) + e * s4.mem (cur + 4) + t) =
        s4.mem (s4.mem (cur + 5) + e * s4.mem (cur + 4) + t) := fun e he t ht =>
    hm7 _ (hne _ ((hT04.2 e he).2 t ht)).1 (hne _ ((hT04.2 e he).2 t ht)).2
  have hrow1 : ∀ e ∈ a.G.E, ∀ t < s4.mem (cur + 4),
      s7.mem (s4.mem (cur + 5 + 1) + e * s4.mem (cur + 4) + t) =
        s4.mem (s4.mem (cur + 5 + 1) + e * s4.mem (cur + 4) + t) := fun e he t ht =>
    hm7 _ (hne _ ((hT14.2 e he).2 t ht)).1 (hne _ ((hT14.2 e he).2 t ht)).2
  have hd0 : s7.mem (cur + 5) = s4.mem (cur + 5) := hm7 _ (by omega) (by omega)
  have hd1 : s7.mem (cur + 5 + 1) = s4.mem (cur + 5 + 1) := hm7 _ (by omega) (by omega)
  refine ⟨s7, c4 + 41, ret, y, hrun, hret1, hret2, ?_, ?_, hloc.1 hrep4, hfoot4, ?_, ?_, hm78,
    ?_, ?_, ?_, ?_, ?_⟩
  · show s5.regs 4 = cur + 7
    simp [s5, h44]
  · intro r h2 h3 h4 h5 h6 h18 h19 h30 h31 h32 h33
    show s5.regs r = st.regs r
    simp only [s5, Function.update_of_ne h33]
    exact (hregs4 r h4 h5 h18 h19 h30 h31 h32).trans (hs3 r h2 h3 h6)
  · intro z hz'
    rw [hm7 z (by omega) (by omega)]
    exact hz4 z hz'
  · intro z hz' hn h8 h9
    rw [hm7 z h8 h9]
    exact hfr4 z hz' hn
  · rw [hm79]; unfold ordLevelLwMax; exact hLw4
  · rw [hm79]
    exact stretchValuesAt_of_moved hSV4 (fun _ => ⟨hd0, hd1⟩) hrow0 hrow1
  · rw [hm79]
    exact selOutTableAt_congr_base (selOutTableAt_mono hT04 (fun _ h => h) le_rfl (by omega)) hd0
  · rw [hm79]
    exact selOutTableAt_congr_base (selOutTableAt_mono hT14 (fun _ h => h) le_rfl (by omega)) hd1
  · have hc4' : c4 + R.phi handle y s4.mem ≤ Psc.readout + 70 + R.phi handle x st.mem := hc4
    rw [← hloc.2]; omega

end Execution

end MinCostFlow.MinRatio
