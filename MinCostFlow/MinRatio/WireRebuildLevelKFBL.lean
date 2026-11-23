module

public import MinCostFlow.MinRatio.WireInitReadoutKFBL
public import MinCostFlow.MinRatio.WireCoreOpsKFBL
import WordRAM.Tactic

/-!
# One rebuild level under the layout contract (`WireRebuildLevelKFBL`)

A rebuild of the chain runs, at each sparse-core level, the init of the level and then the
readout of the next level's graph, lengths and order. Under `sparseCoreOrdMachineContractKFBL`
the init takes 11 arguments, so the level body has a new init statement
(`ordCoreInitStmtKFBL`, `WireCoreOpsKFBL.lean`); the readout is the same program
`ordReadoutNextLevelK`.
* `ordRebuildLevelBodyKFBL`, `ordRebuildSuffixProgramKFBL`: the programs. They are the `K`
  programs of `WireRebuildSuffixK.lean` with the new init. The init reads `L`, `P` and the depth
  from registers `67`, `68` and `98`.
* `ordRebuildLevelBodyKFBL_runs_bounded`: one level, with the result of
  `ordRebuildLevelBodyK_runs_bounded` (`WireInitReadoutK.lean`). The layout facts come from the
  contract and `SparseCoreReadoutFootAt`, so `OrdCoreReadoutLayout` is not needed. Only its init
  space bound stays, as the hypothesis `hInitSpaceLe`. It is asked only for the argument lists
  of this init call: any pointers, and the sizes `k, M, N, L, P` and the depth of this level.
  The graph read for the next level has the caps of this level.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

section Programs

/-- One sparse-core level iteration (`first ≤ i < d`) under `sparseCoreOrdMachineContractKFBL`:
loads `M_i := mem[reg 57 + reg 19]` into `reg 55`, initializes `tool.initOrd`, records
`(handle, 0)` in `(reg 51, reg 52)`, runs `ordReadoutNextLevelKFBL`, and advances descriptors. -/
@[expose] def ordRebuildLevelBodyKFBL (init readGraph readLSF coreLenProc readOrd : ℕ) : Stmt :=
  .assign 55 (.load (.bin .add (.reg 57) (.reg 19))) ;;
  ordCoreInitStmtKFBL init ;;
  storeRebuiltLevel ;;
  ordReadoutNextLevelKFBL readGraph readLSF coreLenProc readOrd ;;
  rebuildAdvanceDescriptors

theorem ordRebuildLevelBodyKFBL_noRand (init readGraph readLSF coreLenProc readOrd : ℕ) :
    (ordRebuildLevelBodyKFBL init readGraph readLSF coreLenProc readOrd).NoRand := by
  simp [ordRebuildLevelBodyKFBL, ordCoreInitStmtKFBL_noRand, storeRebuiltLevel,
    ordReadoutNextLevelKFBL_noRand, rebuildAdvanceDescriptors, Stmt.NoRand]

/-- The ordered suffix rebuild under `sparseCoreOrdMachineContractKFBL`: runs
`ordRebuildLevelBodyKFBL` on `first .. d - 1` and `rebuildTerminalRuntimeStep lastInit` at
level `d`. -/
@[expose] def ordRebuildSuffixProgramKFBL
    (init readGraph readLSF coreLenProc readOrd lastInit : ℕ) : Stmt :=
  rebuildSuffixProgram
    (ordRebuildLevelBodyKFBL init readGraph readLSF coreLenProc readOrd)
    (rebuildTerminalRuntimeStep lastInit)

theorem ordRebuildSuffixProgramKFBL_noRand
    (init readGraph readLSF coreLenProc readOrd lastInit : ℕ) :
    (ordRebuildSuffixProgramKFBL init readGraph readLSF coreLenProc readOrd lastInit).NoRand := by
  apply rebuildSuffixProgram_noRand (ordRebuildLevelBodyKFBL_noRand _ _ _ _ _)
  simp [rebuildTerminalRuntimeStep, rebuildLastLevelRuntime, storeRebuiltLevel, Stmt.NoRand]

end Programs

/-- Live-cost execution of one iteration of `ordRebuildLevelBodyKFBL` under
`sparseCoreOrdMachineContractKFBL` and `SparseCoreReadoutFootAt`. The non-tool cost is bounded by
`ordLevelLiveCost` using actual graph and rotation-order sizes with no global `N₀` or `capLimit`
terms. -/
theorem ordRebuildLevelBodyKFBL_runs_live
    {w L depth k M N vCap eCap capExp capLimit init coreLenProc edgeProc signExt mul intDiv copy
      graphBase lenBase gradBase ordBase ordWords heap handleCell branchCell lvlMTable idx
      nextM : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ} {coreInitSpace : ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ) (ordFn : ℕ → List End)
    (hFour : fmt.limbBits = 4)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth tool G k M N vCap eCap capExp P allocation))
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool G k M N vCap eCap capExp P allocation
      R p op)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hInitSpaceLe : ∀ g l gr o h,
      allocation 6 [g, l, gr, o, k, M, N, L, fmt.precision, depth, h] ≤ coreInitSpace idx)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hg : st.regs 6 = graphBase) (hl : st.regs 7 = lenBase)
    (hgr : st.regs 8 = gradBase) (ho : st.regs 9 = ordBase) (hh : st.regs 4 = heap)
    (hkR : st.regs 1 = k) (hNR : st.regs 56 = N) (hMTab : st.regs 57 = lvlMTable)
    (hIdx : st.regs 19 = idx)
    (h51 : st.regs 51 = handleCell) (h52 : st.regs 52 = branchCell) (h67 : st.regs 67 = L)
    (h68 : st.regs 68 = fmt.precision) (h98 : st.regs 98 = depth)
    (hMCell : st.mem (lvlMTable + idx) = M) (hMAddrW : lvlMTable + idx < 2 ^ w)
    (hk : 0 < k) (hwk : k < 2 ^ w) (hMw : M < 2 ^ w) (hNw : N < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hPw : fmt.precision < 2 ^ w) (hDw : depth < 2 ^ w)
    (hword : (M + N + 2) ^ P.wordExp * (L + 1) < 2 ^ w)
    (hne : handleCell ≠ branchCell) (hhBelow : handleCell < heap) (hbBelow : branchCell < heap)
    (hhNextW : handleCell + 1 < 2 ^ w) (hbNextW : branchCell + 1 < 2 ^ w)
    (hG : DynGraphAt st.mem graphBase vCap eCap G) (hm : G.m ≤ M) (hn : G.n ≤ N)
    (hgb : graphBase + dynGraphSize vCap eCap ≤ heap)
    (hDisjG : ∀ addr, graphBase ≤ addr → addr < graphBase + dynGraphSize vCap eCap →
      addr ≠ handleCell ∧ addr ≠ branchCell)
    (hlb : lenBase + eCap * L ≤ heap) (hgrb : gradBase + eCap * L ≤ heap)
    (hDisjLen : ∀ addr, lenBase ≤ addr → addr < lenBase + eCap * L →
      addr ≠ handleCell ∧ addr ≠ branchCell)
    (hord : OrdListAt st.mem ordBase ordFn ordWords)
    (hordb : ordBase + ordWords ≤ heap)
    (hordW : ∀ j < ordWords, st.mem (ordBase + j) < 2 ^ w)
    (hrot : IsRotationOrder G ordFn)
    (hℓ : EdgeValuesAt st.mem lenBase 4 L fmt.precision G.E ℓ)
    (hgv : EdgeValuesAt st.mem gradBase 4 L fmt.precision G.E g)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e)
    (hz : ZeroFrom st.mem heap)
    (hroom : heap + ordLevelSpace L capExp capLimit (coreInitSpace idx) M N nextM < 2 ^ w)
    (hHE :
      let a0 : SparseCoreOrdAbs tool :=
        ⟨tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
      (tool.S a0.st 0).E ⊆ G.E)
    (hHm :
      let a0 : SparseCoreOrdAbs tool :=
        ⟨tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
      (tool.S a0.st 0).m ≤ nextM)
    (hRotWords :
      let a0 : SparseCoreOrdAbs tool :=
        ⟨tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
      ordRotWords a0 0 ≤ 1 + 2 * N + 2 * nextM)
    (hCoreLenFits :
      let a0 : SparseCoreOrdAbs tool :=
        ⟨tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
      ∀ e ∈ (tool.S a0.st 0).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
          coreLen (tool.lsfs a0.st 0) ℓ e) :
    let a0 : SparseCoreOrdAbs tool :=
      ⟨tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
        (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
    let forest := tool.lsfs a0.st 0
    let H := tool.S a0.st 0
    ∃ (out : State) (vcH ecH nextOrdWords cost : ℕ) (y : R.τ),
      Runs w p ω (ordRebuildLevelBodyKFBL init (op 3) (op 2) coreLenProc (op 5)) st .normal out
        cost ∧
      vcH = vCap ∧ ecH = eCap ∧
      vcH + ecH + 2 ≤ capLimit ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧
      out.regs 19 = idx ∧
      out.regs 51 = handleCell + 1 ∧ out.regs 52 = branchCell + 1 ∧
      R.rep heap a0 y out.mem ∧
      DynGraphAt out.mem (out.regs 6) vcH ecH H ∧
      EdgeValuesAt out.mem (out.regs 7) 4 L fmt.precision H.E (coreLen forest ℓ) ∧
      out.regs 8 = out.regs 7 ∧
      OrdListAt out.mem (out.regs 9) (tool.rot a0.st 0) nextOrdWords ∧
      nextOrdWords ≤ ordRotWords a0 0 ∧
      out.regs 9 + nextOrdWords ≤ out.regs 4 ∧ heap < out.regs 9 ∧
      (∀ j < nextOrdWords, out.mem (out.regs 9 + j) < 2 ^ w) ∧
      heap ≤ out.regs 6 ∧ out.regs 6 + dynGraphSize vcH ecH ≤ out.regs 4 ∧
      (∀ addr, out.regs 6 ≤ addr → addr < out.regs 6 + dynGraphSize vcH ecH →
        ¬ R.foot heap y addr) ∧
      heap ≤ out.regs 7 ∧ out.regs 7 + ecH * L ≤ out.regs 4 ∧
      (∀ addr, out.regs 7 ≤ addr → addr < out.regs 7 + ecH * L → ¬ R.foot heap y addr) ∧
      out.regs 6 + dynGraphSize vcH ecH ≤ out.regs 7 ∧
      heap ≤ out.regs 4 ∧
      out.regs 4 ≤ heap + ordLevelSpace L capExp capLimit (coreInitSpace idx) M N nextM ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ addr < heap, addr ≠ handleCell → addr ≠ branchCell → out.mem addr = st.mem addr) ∧
      (∀ addr, R.foot heap y addr → heap ≤ addr ∧ addr < out.regs 4) ∧
      (∀ r, r = 0 ∨ r = 1 ∨ (13 ≤ r ∧ r ≤ 50) ∨ (53 ≤ r ∧ r ≤ 54) ∨ (56 ≤ r ∧ r ≤ 62) ∨
        r = 67 ∨ r = 68 ∨ 70 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi heap y out.mem ≤
        P.mul * tool.cost a0.st +
          ordLevelLiveCost L capExp P M N G.n G.m H.n H.m ordWords (ordRotWords a0 0) := by
  dsimp only
  have hInitAllocLe : allocation 6
      [graphBase, lenBase, gradBase, ordBase, k, M, N, L, fmt.precision, depth, heap] ≤
      coreInitSpace idx := hInitSpaceLe _ _ _ _ _
  have hRoomInit : heap + allocation 6
      [graphBase, lenBase, gradBase, ordBase, k, M, N, L, fmt.precision, depth, heap] < 2 ^ w := by
    dsimp only [ordLevelSpace] at hroom; omega
  -- Step 1: Load M from lvlMTable + idx
  let s1 := { st with regs := Function.update st.regs 55 M }
  have r1 : Runs w p ω (.assign 55 (.load (.bin .add (.reg 57) (.reg 19)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨M, by simp [Expr.eval, BinOp.eval, hMTab, hIdx, hMAddrW, hMCell],
      rfl, rfl, rfl⟩
  have hs1_r (r : ℕ) (h55 : r ≠ 55) : s1.regs r = st.regs r := Function.update_of_ne h55 _ _
  have hLw : L < 2 ^ w := by
    have h1 : 1 ≤ (M + N + 2) ^ P.wordExp := Nat.one_le_pow _ _ (by omega)
    have h2 : L + 1 ≤ (M + N + 2) ^ P.wordExp * (L + 1) := Nat.le_mul_of_pos_left _ h1
    omega
  -- Step 2: Init sparse-core level
  obtain ⟨s2, ret0, c2, y0, r2, hs2_2, hs2_3, hs2_4, hrep0, hIn0, hresp0, hc2⟩ :=
    ordCoreInitKFBL_tables_runs (ω := ω) (st := s1) ℓ g ordFn himpl
      ((hs1_r 6 (by decide)).trans hg) ((hs1_r 7 (by decide)).trans hl)
      ((hs1_r 8 (by decide)).trans hgr) ((hs1_r 9 (by decide)).trans ho)
      ((hs1_r 1 (by decide)).trans hkR) (by simp [s1])
      ((hs1_r 56 (by decide)).trans hNR) ((hs1_r 67 (by decide)).trans h67)
      ((hs1_r 68 (by decide)).trans h68) ((hs1_r 98 (by decide)).trans h98)
      ((hs1_r 4 (by decide)).trans hh)
      hk hwk hMw hNw hLw hPw hDw hword hG hm hn hgb hlb hgrb hord hordb hordW hrot
      (hFour ▸ hℓ) (hFour ▸ hgv) hpos hz hRoomInit
  have hs2_r (r : ℕ) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) : s2.regs r = s1.regs r :=
    ordCoreInitStmtKFBL_preserves_regs r2 h2 h3 h4
  have hfoot0 (addr : ℕ) (hf : R.foot heap y0 addr) : heap ≤ addr ∧ addr < ret0 :=
    (hresp0.2.2.2.2 addr hf).resolve_left id
  -- Step 3: Store handle and branch 0
  obtain ⟨s3, r3, hs3_h, hs3_b, hrep3, hphi3, hs3_frame, hs3_regs, _⟩ :=
    storeRebuiltLevel_preserves_tool_runs (ω := ω) (st := s2) himpl.1
      ((hs2_r 51 (by decide) (by decide) (by decide)).trans ((hs1_r 51 (by decide)).trans h51))
      ((hs2_r 52 (by decide) (by decide) (by decide)).trans ((hs1_r 52 (by decide)).trans h52))
      hne (hs2_3.symm ▸ hhBelow) (hs2_3.symm ▸ hbBelow)
      (fun addr hf => hs2_3.symm ▸ (hfoot0 addr (hs2_3 ▸ hf)).1) (hs2_3.symm ▸ hrep0)
  have hs3_lt (addr : ℕ) (hlt : addr < heap) (hh' : addr ≠ handleCell)
      (hb' : addr ≠ branchCell) : s3.mem addr = st.mem addr :=
    (hs3_frame addr hh' hb').trans (hresp0.2.2.2.1 addr hlt id)
  have hs3_G : DynGraphAt s3.mem graphBase vCap eCap G :=
    dynGraphAt_of_agree hG (fun addr hlo hhi =>
      hs3_lt addr (by omega) (hDisjG addr hlo hhi).1 (hDisjG addr hlo hhi).2)
  have hs3_Len : EdgeValuesAt s3.mem lenBase 4 L fmt.precision G.E ℓ :=
    hℓ.congr (fun e he j hj => by
      have heLt := hG.2.2.1 e he
      have hm' : e * L + L ≤ eCap * L := by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
      exact hs3_lt _ (by omega) (hDisjLen _ (by omega) (by omega)).1
        (hDisjLen _ (by omega) (by omega)).2)
  have hs3_hz : ZeroFrom s3.mem ret0 := fun addr ha => by
    have hlo := hresp0.1
    exact (hs3_frame addr (by omega) (by omega)).trans (hresp0.2.2.1 addr ha)
  have hret0Room :
      let LwMax := ordLevelLwMax L capExp M N
      ret0 + 1 + dynGraphSize capLimit capLimit + 5 +
        capLimit * L + nextM * wireCoreLenEdgeSpace LwMax + (2 + 2 * N + 2 * nextM) < 2 ^ w := by
    have hret0Hi := hresp0.2.1
    dsimp only [ordLevelSpace] at hroom
    dsimp only; omega
  -- Step 4: Bounded readout
  obtain ⟨s4, vcH, ecH, nextOrdWords, _Lw, c4, y4, r4, _, hvcH, hecH, hcapH, hrep4, hH4, hLen4,
      hGrad4, hOrd4, hOrdLe4, hOrdEnd4, hOrd9Lo4, hOrdW4, h6Lo4, hHEnd4, hHDisj4, h7Lo4,
      hLenEnd4, hLenDisj4, h6Le7_4, h4Lo4,
      h4Hi4, hz4, hs4_frame, _, hs4_footIn, hs4_regs, hc4⟩ :=
    ordReadoutNextLevelKFBL_runs_bounded_ord (ω := ω) (st := s3) ℓ hFour himpl hFootAt hcapLim
      hCoreLenProc hEdgeProc hSign hMul hDiv hCopy
      (hs3_regs.symm ▸ hs2_2) (hs3_regs.symm ▸ hs2_3) (hs3_regs.symm ▸ hs2_4)
      ((hs3_regs.symm ▸ hs2_r 6 (by decide) (by decide) (by decide)).trans
        ((hs1_r 6 (by decide)).trans hg))
      ((hs3_regs.symm ▸ hs2_r 7 (by decide) (by decide) (by decide)).trans
        ((hs1_r 7 (by decide)).trans hl))
      ((hs3_regs.symm ▸ hs2_r 67 (by decide) (by decide) (by decide)).trans
        ((hs1_r 67 (by decide)).trans h67))
      hk hwk (by omega) hw9 hs3_G (hgb.trans hresp0.1)
      (fun addr _ hhi hf => by have := (hfoot0 addr hf).1; omega)
      hs3_Len (hlb.trans hresp0.1)
      (fun addr _ hhi hf => by have := (hfoot0 addr hf).1; omega)
      (by simpa only [hs3_regs, hs2_3] using hrep3) hIn0
      (fun addr hf => (hfoot0 addr hf).2) hs3_hz hHE hHm hRotWords hCoreLenFits hret0Room
  -- Step 5: Advance descriptor cursors
  have hs4_51 : s4.regs 51 = handleCell :=
    (hs4_regs 51 (by omega)).trans (hs3_regs.symm ▸
      ((hs2_r 51 (by decide) (by decide) (by decide)).trans ((hs1_r 51 (by decide)).trans h51)))
  have hs4_52 : s4.regs 52 = branchCell :=
    (hs4_regs 52 (by omega)).trans (hs3_regs.symm ▸
      ((hs2_r 52 (by decide) (by decide) (by decide)).trans ((hs1_r 52 (by decide)).trans h52)))
  obtain ⟨out, r5, hout51, hout52, houtRegs, houtMem⟩ :=
    rebuildAdvanceDescriptors_runs (ω := ω) (st := s4) hs4_51 hs4_52 hhNextW hbNextW
  have rFull : Runs w p ω (ordRebuildLevelBodyKFBL init (op 3) (op 2) coreLenProc (op 5)) st
      .normal out (5 + (c2 + (7 + (c4 + 9 + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, c2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 7, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, c4, 9, r4, r5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hnf0 (addr : ℕ) (hlt : addr < heap) : ¬ R.foot heap y0 addr :=
    fun hf => by have := (hfoot0 addr hf).1; omega
  have h6Eq := houtRegs 6 (by decide) (by decide)
  have h7Eq := houtRegs 7 (by decide) (by decide)
  have h8Eq := houtRegs 8 (by decide) (by decide)
  have h9Eq := houtRegs 9 (by decide) (by decide)
  have h4Eq := houtRegs 4 (by decide) (by decide)
  refine ⟨out, vcH, ecH, nextOrdWords, _, y4, rFull, hvcH, hecH, hcapH, ?_, ?_,
    (houtRegs 19 (by decide) (by decide)).trans ((hs4_regs 19 (by omega)).trans
      (hs3_regs.symm ▸ ((hs2_r 19 (by decide) (by decide) (by decide)).trans
        ((hs1_r 19 (by decide)).trans hIdx)))),
    hout51, hout52, houtMem.symm ▸ hrep4,
    by rw [houtMem, h6Eq]; exact hH4,
    by rw [houtMem, h7Eq]; exact hLen4,
    by rw [h8Eq, h7Eq]; exact hGrad4,
    by rw [houtMem, h9Eq]; exact hOrd4,
    hOrdLe4,
    by rw [h9Eq, h4Eq]; exact hOrdEnd4,
    by rw [h9Eq]; exact lt_of_le_of_lt hresp0.1 hOrd9Lo4,
    by rw [houtMem, h9Eq]; exact hOrdW4,
    by rw [h6Eq]; exact hresp0.1.trans h6Lo4,
    by rw [h6Eq, h4Eq]; exact hHEnd4,
    fun addr hlo hhi => by rw [h6Eq] at hlo hhi; exact hHDisj4 addr hlo hhi,
    by rw [h7Eq]; exact hresp0.1.trans h7Lo4,
    by rw [h7Eq, h4Eq]; exact hLenEnd4,
    fun addr hlo hhi => by rw [h7Eq] at hlo hhi; exact hLenDisj4 addr hlo hhi,
    by rw [h6Eq, h7Eq]; exact h6Le7_4,
    by rw [h4Eq]; exact hresp0.1.trans h4Lo4,
    by rw [h4Eq]; have hret0Hi := hresp0.2.1; dsimp only [ordLevelSpace]; omega,
    by rw [houtMem, h4Eq]; exact hz4,
    fun addr hlt hneH hneB => by
      rw [houtMem, hs4_frame addr (hlt.trans_le hresp0.1) (hnf0 addr hlt)]
      exact hs3_lt addr hlt hneH hneB,
    fun addr hf => by
      rw [h4Eq]
      rcases hs4_footIn addr hf with hy0 | ⟨hlo, hhi⟩
      · exact ⟨(hfoot0 addr hy0).1, (hfoot0 addr hy0).2.trans_le h4Lo4⟩
      · exact ⟨hresp0.1.trans hlo, hhi⟩,
    fun r hr => by
      rw [houtRegs r (by omega) (by omega), hs4_regs r (by omega), hs3_regs,
        hs2_r r (by omega) (by omega) (by omega), hs1_r r (by omega)],
    ?_⟩
  · rw [houtMem, hs4_frame handleCell (hhBelow.trans_le hresp0.1) (hnf0 handleCell hhBelow),
      hs3_h, hs3_regs, hs2_3]
  · rw [houtMem, hs4_frame branchCell (hbBelow.trans_le hresp0.1) (hnf0 branchCell hbBelow),
      hs3_b]
  · rw [houtMem]
    rw [hs3_regs, hs2_3] at hphi3
    have hphiEq : R.phi heap y0 s3.mem = R.phi heap y0 s2.mem := hphi3
    rw [hphiEq] at hc4
    have hmulInit :
        P.mul * (tool.cost (tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn) + G.n + G.m + ordWords + 1) =
        P.mul * tool.cost (tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn) +
        P.mul * (G.n + G.m + ordWords + 1) := by
      rw [← Nat.mul_add]; congr 1; omega
    dsimp only [ordLevelLiveCost]
    dsimp only at hc2 hc4 ⊢
    omega

/-- Space- and word-bounded execution of one iteration of `ordRebuildLevelBodyKFBL` under
`sparseCoreOrdMachineContractKFBL` and `SparseCoreReadoutFootAt`, with the `ordLevelFixedCost`
bound for `WireInitLevelsK`. -/
theorem ordRebuildLevelBodyKFBL_runs_bounded
    {w L depth k M N vCap eCap capExp capLimit init coreLenProc edgeProc signExt mul intDiv copy
      graphBase lenBase gradBase ordBase ordWords heap handleCell branchCell lvlMTable idx
      nextM : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ} {coreInitSpace : ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ) (ordFn : ℕ → List End)
    (hFour : fmt.limbBits = 4)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth tool G k M N vCap eCap capExp P allocation))
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool G k M N vCap eCap capExp P allocation
      R p op)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hInitSpaceLe : ∀ g l gr o h,
      allocation 6 [g, l, gr, o, k, M, N, L, fmt.precision, depth, h] ≤ coreInitSpace idx)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hg : st.regs 6 = graphBase) (hl : st.regs 7 = lenBase)
    (hgr : st.regs 8 = gradBase) (ho : st.regs 9 = ordBase) (hh : st.regs 4 = heap)
    (hkR : st.regs 1 = k) (hNR : st.regs 56 = N) (hMTab : st.regs 57 = lvlMTable)
    (hIdx : st.regs 19 = idx)
    (h51 : st.regs 51 = handleCell) (h52 : st.regs 52 = branchCell) (h67 : st.regs 67 = L)
    (h68 : st.regs 68 = fmt.precision) (h98 : st.regs 98 = depth)
    (hMCell : st.mem (lvlMTable + idx) = M) (hMAddrW : lvlMTable + idx < 2 ^ w)
    (hk : 0 < k) (hwk : k < 2 ^ w) (hMw : M < 2 ^ w) (hNw : N < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hPw : fmt.precision < 2 ^ w) (hDw : depth < 2 ^ w)
    (hword : (M + N + 2) ^ P.wordExp * (L + 1) < 2 ^ w)
    (hne : handleCell ≠ branchCell) (hhBelow : handleCell < heap) (hbBelow : branchCell < heap)
    (hhNextW : handleCell + 1 < 2 ^ w) (hbNextW : branchCell + 1 < 2 ^ w)
    (hG : DynGraphAt st.mem graphBase vCap eCap G) (hm : G.m ≤ M) (hn : G.n ≤ N)
    (hgb : graphBase + dynGraphSize vCap eCap ≤ heap)
    (hDisjG : ∀ addr, graphBase ≤ addr → addr < graphBase + dynGraphSize vCap eCap →
      addr ≠ handleCell ∧ addr ≠ branchCell)
    (hlb : lenBase + eCap * L ≤ heap) (hgrb : gradBase + eCap * L ≤ heap)
    (hDisjLen : ∀ addr, lenBase ≤ addr → addr < lenBase + eCap * L →
      addr ≠ handleCell ∧ addr ≠ branchCell)
    (hord : OrdListAt st.mem ordBase ordFn ordWords)
    (hordWordsLe : ordWords ≤ 2 * N + 2 * M + 1)
    (hordb : ordBase + ordWords ≤ heap)
    (hordW : ∀ j < ordWords, st.mem (ordBase + j) < 2 ^ w)
    (hrot : IsRotationOrder G ordFn)
    (hℓ : EdgeValuesAt st.mem lenBase 4 L fmt.precision G.E ℓ)
    (hgv : EdgeValuesAt st.mem gradBase 4 L fmt.precision G.E g)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e)
    (hz : ZeroFrom st.mem heap)
    (hroom : heap + ordLevelSpace L capExp capLimit (coreInitSpace idx) M N nextM < 2 ^ w)
    (hHE :
      let a0 : SparseCoreOrdAbs tool :=
        ⟨tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
      (tool.S a0.st 0).E ⊆ G.E)
    (hHm :
      let a0 : SparseCoreOrdAbs tool :=
        ⟨tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
      (tool.S a0.st 0).m ≤ nextM)
    (hRotWords :
      let a0 : SparseCoreOrdAbs tool :=
        ⟨tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
      ordRotWords a0 0 ≤ 1 + 2 * N + 2 * nextM)
    (hCoreLenFits :
      let a0 : SparseCoreOrdAbs tool :=
        ⟨tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
      ∀ e ∈ (tool.S a0.st 0).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
          coreLen (tool.lsfs a0.st 0) ℓ e) :
    let a0 : SparseCoreOrdAbs tool :=
      ⟨tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
        (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
    let forest := tool.lsfs a0.st 0
    let H := tool.S a0.st 0
    ∃ (out : State) (vcH ecH nextOrdWords cost : ℕ) (y : R.τ),
      Runs w p ω (ordRebuildLevelBodyKFBL init (op 3) (op 2) coreLenProc (op 5)) st .normal out
        cost ∧
      vcH = vCap ∧ ecH = eCap ∧
      vcH + ecH + 2 ≤ capLimit ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧
      out.regs 19 = idx ∧
      out.regs 51 = handleCell + 1 ∧ out.regs 52 = branchCell + 1 ∧
      R.rep heap a0 y out.mem ∧
      DynGraphAt out.mem (out.regs 6) vcH ecH H ∧
      EdgeValuesAt out.mem (out.regs 7) 4 L fmt.precision H.E (coreLen forest ℓ) ∧
      out.regs 8 = out.regs 7 ∧
      OrdListAt out.mem (out.regs 9) (tool.rot a0.st 0) nextOrdWords ∧
      nextOrdWords ≤ ordRotWords a0 0 ∧
      out.regs 9 + nextOrdWords ≤ out.regs 4 ∧ heap < out.regs 9 ∧
      (∀ j < nextOrdWords, out.mem (out.regs 9 + j) < 2 ^ w) ∧
      heap ≤ out.regs 6 ∧ out.regs 6 + dynGraphSize vcH ecH ≤ out.regs 4 ∧
      (∀ addr, out.regs 6 ≤ addr → addr < out.regs 6 + dynGraphSize vcH ecH →
        ¬ R.foot heap y addr) ∧
      heap ≤ out.regs 7 ∧ out.regs 7 + ecH * L ≤ out.regs 4 ∧
      (∀ addr, out.regs 7 ≤ addr → addr < out.regs 7 + ecH * L → ¬ R.foot heap y addr) ∧
      out.regs 6 + dynGraphSize vcH ecH ≤ out.regs 7 ∧
      heap ≤ out.regs 4 ∧
      out.regs 4 ≤ heap + ordLevelSpace L capExp capLimit (coreInitSpace idx) M N nextM ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ addr < heap, addr ≠ handleCell → addr ≠ branchCell → out.mem addr = st.mem addr) ∧
      (∀ addr, R.foot heap y addr → heap ≤ addr ∧ addr < out.regs 4) ∧
      (∀ r, r = 0 ∨ r = 1 ∨ (13 ≤ r ∧ r ≤ 50) ∨ (53 ≤ r ∧ r ≤ 54) ∨ (56 ≤ r ∧ r ≤ 62) ∨
        r = 67 ∨ r = 68 ∨ 70 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi heap y out.mem ≤
        P.mul * tool.cost a0.st + ordLevelFixedCost L capExp capLimit P M N nextM := by
  dsimp only
  obtain ⟨out, vcH, ecH, nextOrdWords, cost, y, hrun, hvcH, hecH, hcapH, hH, hB, h19, h51', h52',
    hrep, hDG, hLen, h8, hOrd, hOrdLe, hOrdEnd, hOrdLo, hOrdW, h6Lo, h6End, h6Disj, h7Lo, h7End,
    h7Disj, h6Le7, h4Lo, h4Hi, hz', hfr, hfoot, hregs, hc⟩ :=
    ordRebuildLevelBodyKFBL_runs_live (ω := ω) ℓ g ordFn hFour himpl hFootAt hcapLim hInitSpaceLe
      hCoreLenProc hEdgeProc hSign hMul hDiv hCopy hg hl hgr ho hh hkR hNR hMTab hIdx h51 h52 h67
      h68 h98 hMCell hMAddrW hk hwk hMw hNw hw9 hPw hDw hword hne hhBelow hbBelow hhNextW hbNextW
      hG hm hn hgb hDisjG hlb hgrb hDisjLen hord hordb hordW hrot hℓ hgv hpos hz hroom hHE hHm
      hRotWords hCoreLenFits
  refine ⟨out, vcH, ecH, nextOrdWords, cost, y, hrun, hvcH, hecH, hcapH, hH, hB, h19, h51', h52',
    hrep, hDG, hLen, h8, hOrd, hOrdLe, hOrdEnd, hOrdLo, hOrdW, h6Lo, h6End, h6Disj, h7Lo, h7End,
    h7Disj, h6Le7, h4Lo, h4Hi, hz', hfr, hfoot, hregs, ?_⟩
  have hcopyLe := copyGraphLiveCost_le_17_dynGraphSize hDG hcapH
  have h1 : P.mul * (G.n + G.m + ordWords + 1) ≤ P.mul * (N + M + (2 * N + 2 * M + 1) + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : P.mul * (ordRotWords
      ⟨tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
        (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩ 0 + 1) *
      SparseCore.bundleLogFactor M N ≤
      P.mul * (2 * N + 2 * nextM + 2) * SparseCore.bundleLogFactor M N :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by dsimp only at hRotWords; omega))
  have h3 : (tool.S (tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
        (fun e => if e ∈ G.E then g e else 0) ordFn) 0).m *
      (wireCoreLenEdgeCost (ordLevelLwMax L capExp M N) + 30) ≤
      nextM * (wireCoreLenEdgeCost (ordLevelLwMax L capExp M N) + 30) :=
    Nat.mul_le_mul_right _ (by dsimp only at hHm; exact hHm)
  dsimp only at hcopyLe
  dsimp only [ordLevelLiveCost, ordLevelFixedCost] at hc ⊢
  omega

/-- Total heap space budget for `ordRebuildSuffixProgramKFBL` at Init across `d` sparse-core levels
plus the terminal last-level allocation `lastSpace`. -/
@[expose] def ordInitLevelsSpace (L capExp capLimit : ℕ) (coreInitSpace lvlM nextM : ℕ → ℕ)
    (N₀ lastSpace d : ℕ) : ℕ :=
  (∑ i ∈ Finset.range d,
    ordLevelSpace L capExp capLimit (coreInitSpace i) (lvlM i) N₀ (nextM i)) + lastSpace

/-- Total non-tool fixed step budget for `ordRebuildSuffixProgramKFBL` at Init (excluding
`max P.mul lastMult * chain.totalRuntime`). -/
@[expose] def ordInitLevelsFixed (L capExp capLimit : ℕ) (P : SparseCoreOrdParams)
    (lvlM nextM : ℕ → ℕ) (N₀ lastMult d : ℕ) : ℕ :=
  (∑ i ∈ Finset.range d,
    (ordLevelFixedCost L capExp capLimit P (lvlM i) N₀ (nextM i) + 9)) + lastMult + 30

end MinCostFlow.MinRatio
