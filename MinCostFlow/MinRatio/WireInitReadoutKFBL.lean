module

public import MinCostFlow.MinRatio.WireInitReadoutK
public import MinCostFlow.MinRatio.WireCoreReadKFBL
public import MinCostFlow.MinRatio.GraphLiveCopy
import WordRAM.Tactic

/-!
# The readout of one level under the layout contract (`WireInitReadoutKFBL`)

`ordReadoutNextLevelKFBL` runs the readout of one sparse-core level using `copyGraphLiveFromHeader`
(`GraphLiveCopy.lean`): op `3` gives the sparsifier graph, which is copied out in time
`copyGraphLiveCost H.n H.m = O(H.n + H.m + 1)` by walking only its live vertex and edge lists;
op `2` gives the forest and its stretch tables, from which `coreLenProc` computes the next lengths;
op `5` gives the order of the active branch.

* `ordReadoutNextLevelKFBL`: the readout statement using `copyGraphLiveFromHeader`.
* `ordLevelLiveCost`: per-level non-tool step cost in terms of actual graph and order sizes
  `(Gn, Gm, Hn, Hm, inOrdWords, outOrdWords)` with no global `N₀` or `capLimit` terms.
* `ordReadoutNextLevelKFBL_runs_bounded`: execution lemma under `sparseCoreOrdMachineContractKFBL`
  and `SparseCoreReadoutFootAt`, charging the live-list copy and actual output order size.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- Readout tail under `sparseCoreOrdMachineContractKFBL`: identical to `ordReadoutNextLevelK`
except that the sparsifier graph copy uses the live-list copy `copyGraphLiveFromHeader` in
`O(H.n + H.m + 1)` time instead of scanning the full capacity arrays. -/
@[expose] def ordReadoutNextLevelKFBL (readGraph readLSF coreLenProc readOrd : ℕ) : Stmt :=
  .assign 65 (.reg 2) ;;
  .assign 66 (.reg 3) ;;
  .assign 69 (.reg 6) ;;
  ordCoreReadGraphStmt readGraph ;;
  loadShiftGraph ;;
  copyGraphLiveFromHeader ;;
  .assign 64 (.load (.bin .add (.reg 6) (.const 1))) ;;
  .assign 4 (.reg 5) ;;
  .assign 63 (.reg 6) ;;
  .assign 6 (.reg 69) ;;
  ordCoreReadLSFStmt readLSF ;;
  .assign 10 (.load (.bin .add (.reg 4) (.const 3))) ;;
  .assign 11 (.load (.bin .add (.reg 4) (.const 4))) ;;
  .call 4 coreLenProc [.reg 63, .reg 10, .reg 7, .reg 67, .reg 11, .reg 5] ;;
  .assign 7 (.reg 5) ;;
  .assign 8 (.reg 5) ;;
  .assign 2 (.reg 65) ;;
  .assign 3 (.reg 66) ;;
  ordCoreReadOrdStmt readOrd ;;
  .assign 4 (.reg 5) ;;
  .assign 6 (.reg 63)

theorem ordReadoutNextLevelKFBL_noRand (readGraph readLSF coreLenProc readOrd : ℕ) :
    (ordReadoutNextLevelKFBL readGraph readLSF coreLenProc readOrd).NoRand := by
  simp [ordReadoutNextLevelKFBL, ordCoreReadGraphStmt, loadShiftGraph,
    copyGraphLiveFromHeader_noRand, ordCoreReadLSFStmt, ordCoreReadOrdStmt, Stmt.NoRand]

/-- Live per-level non-tool step cost of `ordRebuildLevelBodyKFBL` (excluding `P.mul * tool.cost`)
as a function of actual input/output graph sizes `(Gn, Gm, Hn, Hm)` and input/output rotation
order word counts `(inOrdWords, outOrdWords)`. -/
@[expose] def ordLevelLiveCost (L capExp : ℕ) (P : SparseCoreOrdParams)
    (M N Gn Gm Hn Hm inOrdWords outOrdWords : ℕ) : ℕ :=
  let LwMax := ordLevelLwMax L capExp M N
  P.mul * (Gn + Gm + inOrdWords + 1) +
    P.mul * (outOrdWords + 1) * SparseCore.bundleLogFactor M N +
    2 * P.readout + copyGraphLiveCost Hn Hm +
    Hm * (wireCoreLenEdgeCost LwMax + 30) + 200

private theorem dynGraphSize_mono {v₁ e₁ v₂ e₂ : ℕ} (hv : v₁ ≤ v₂) (he : e₁ ≤ e₂) :
    dynGraphSize v₁ e₁ ≤ dynGraphSize v₂ e₂ := by
  unfold dynGraphSize; omega

private theorem wireCoreLenEdgeSpace_mono {K₁ K₂ : ℕ} (h : K₁ ≤ K₂) :
    wireCoreLenEdgeSpace K₁ ≤ wireCoreLenEdgeSpace K₂ := by
  unfold wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
  have hmul : 5 * (2 * K₁) * (2 * K₁ + 1) ≤ 5 * (2 * K₂) * (2 * K₂ + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 5 (by omega)) (by omega)
  omega

private theorem wireCoreLenEdgeCost_mono {K₁ K₂ : ℕ} (h : K₁ ≤ K₂) :
    wireCoreLenEdgeCost K₁ ≤ wireCoreLenEdgeCost K₂ := by
  unfold wireCoreLenEdgeCost
  have hsq : K₁ ^ 2 ≤ K₂ ^ 2 := Nat.pow_le_pow_left h 2
  omega

/-- Space- and word-bounded execution of `ordReadoutNextLevelK` under the layout contract
`sparseCoreOrdMachineContractKFBL` and `SparseCoreReadoutFootAt`, with the same conclusion as
`ordReadoutNextLevelK_runs_bounded`. The cap bound `vCap + eCap + 2 ≤ capLimit` of the level
replaces `OrdCoreReadoutLayout`. -/
theorem ordReadoutNextLevelKFBL_runs_bounded_ord
    {w L depth k M N vCap eCap capExp capLimit init coreLenProc edgeProc signExt mul intDiv copy
      branch handle heap graphBase lenBase nextM : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ : ℕ → ℝ)
    (hFour : fmt.limbBits = 4)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P
        allocation))
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation R p op)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle) (hp : st.regs 4 = heap)
    (hg : st.regs 6 = graphBase) (hl : st.regs 7 = lenBase) (h67 : st.regs 67 = L)
    (hj : branch < k) (hwk : k < 2 ^ w) (hhw : handle < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hG : DynGraphAt st.mem graphBase vCap eCap a.G)
    (hgEnd : graphBase + dynGraphSize vCap eCap ≤ heap)
    (hFootG : ∀ addr, graphBase ≤ addr → addr < graphBase + dynGraphSize vCap eCap →
      ¬ R.foot handle x addr)
    (hLen : EdgeValuesAt st.mem lenBase 4 L fmt.precision a.G.E ℓ)
    (hLenEnd : lenBase + eCap * L ≤ heap)
    (hFootLen : ∀ addr, lenBase ≤ addr → addr < lenBase + eCap * L → ¬ R.foot handle x addr)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap)
    (hz : ZeroFrom st.mem heap)
    (hHE : (tool.S a.st branch).E ⊆ a.G.E)
    (hHm : (tool.S a.st branch).m ≤ nextM)
    (hRotWords : ordRotWords a branch ≤ 1 + 2 * N + 2 * nextM)
    (hCoreLenFits : ∀ e ∈ (tool.S a.st branch).E,
      ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
        coreLen (tool.lsfs a.st branch) ℓ e)
    (hroom :
      let LwMax := ordLevelLwMax L capExp M N
      heap + 1 + dynGraphSize capLimit capLimit + 5 +
        capLimit * L + nextM * wireCoreLenEdgeSpace LwMax + (2 + 2 * N + 2 * nextM) < 2 ^ w) :
    let forest := tool.lsfs a.st branch
    let H := tool.S a.st branch
    let LwMax := ordLevelLwMax L capExp M N
    ∃ (out : State) (vcH ecH nextOrdWords Lw cost : ℕ) (y : R.τ),
      Runs w p ω (ordReadoutNextLevelKFBL (op 3) (op 2) coreLenProc (op 5)) st .normal out cost ∧
      Lw ≤ LwMax ∧
      vcH = vCap ∧ ecH = eCap ∧
      vcH + ecH + 2 ≤ capLimit ∧
      R.rep handle a y out.mem ∧
      DynGraphAt out.mem (out.regs 6) vcH ecH H ∧
      EdgeValuesAt out.mem (out.regs 7) 4 L fmt.precision H.E (coreLen forest ℓ) ∧
      out.regs 8 = out.regs 7 ∧
      OrdListAt out.mem (out.regs 9) (tool.rot a.st branch) nextOrdWords ∧
      nextOrdWords ≤ ordRotWords a branch ∧
      out.regs 9 + nextOrdWords ≤ out.regs 4 ∧ heap < out.regs 9 ∧
      (∀ j < nextOrdWords, out.mem (out.regs 9 + j) < 2 ^ w) ∧
      heap ≤ out.regs 6 ∧ out.regs 6 + dynGraphSize vcH ecH ≤ out.regs 4 ∧
      (∀ addr, out.regs 6 ≤ addr → addr < out.regs 6 + dynGraphSize vcH ecH →
        ¬ R.foot handle y addr) ∧
      heap ≤ out.regs 7 ∧ out.regs 7 + ecH * L ≤ out.regs 4 ∧
      (∀ addr, out.regs 7 ≤ addr → addr < out.regs 7 + ecH * L → ¬ R.foot handle y addr) ∧
      out.regs 6 + dynGraphSize vcH ecH ≤ out.regs 7 ∧
      heap ≤ out.regs 4 ∧
      out.regs 4 ≤ heap + 1 + dynGraphSize capLimit capLimit + 5 +
        capLimit * L + nextM * wireCoreLenEdgeSpace LwMax + (2 + 2 * N + 2 * nextM) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ addr < heap, ¬ R.foot handle x addr → out.mem addr = st.mem addr) ∧
      (∀ addr, R.foot handle y addr → addr < out.regs 4) ∧
      (∀ addr, R.foot handle y addr → R.foot handle x addr ∨ (heap ≤ addr ∧ addr < out.regs 4)) ∧
      (∀ r, r = 0 ∨ r = 1 ∨ (13 ≤ r ∧ r ≤ 62) ∨ r = 67 ∨ r = 68 ∨ 70 ≤ r →
        out.regs r = st.regs r) ∧
      cost + R.phi handle y out.mem ≤
        2 * P.readout + copyGraphLiveCost H.n H.m +
          H.m * (wireCoreLenEdgeCost LwMax + 30) +
          P.mul * (ordRotWords a branch + 1) * SparseCore.bundleLogFactor M N +
          R.phi handle x st.mem + 150 := by
  dsimp only at hroom ⊢
  let forest := tool.lsfs a.st branch
  let H := tool.S a.st branch
  let LwMax := ordLevelLwMax L capExp M N
  -- Save branch, handle, curGraph
  let s1 := { st with regs := Function.update st.regs 65 branch }
  let s2 := { s1 with regs := Function.update s1.regs 66 handle }
  let s3 := { s2 with regs := Function.update s2.regs 69 graphBase }
  have r1 : Runs w p ω (.assign 65 (.reg 2)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨branch, by simp [Expr.eval, hb], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 66 (.reg 3)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, s1, Function.update_of_ne, hh], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 69 (.reg 6)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨graphBase, by simp [Expr.eval, s2, s1, Function.update_of_ne, hg], rfl, rfl, rfl⟩
  have hs3_r (r : ℕ) (h65 : r ≠ 65) (h66 : r ≠ 66) (h69 : r ≠ 69) : s3.regs r = st.regs r := by
    simp [s3, s2, s1, Function.update_of_ne h65, Function.update_of_ne h66, Function.update_of_ne h69]
  -- Op 3: read sparsifier graph
  obtain ⟨s4, h1, c4, y1, r4, hs4_5, hrep1, ⟨vcH, ecH, hH1, hvcH, hecH, hRawEnd0⟩, hresp1, hc4,
      hs4_regs⟩ :=
    ordCoreReadGraphKFBL_runs (ω := ω) (st := s3) hFootAt
      ((hs3_r 2 (by decide) (by decide) (by decide)).trans hb)
      ((hs3_r 3 (by decide) (by decide) (by decide)).trans hh)
      ((hs3_r 4 (by decide) (by decide) (by decide)).trans hp)
      hj hwk hhw hrep hIn hfoot hz (by omega)
  have hcapH : vcH + ecH + 2 ≤ capLimit := by omega
  have hRawEnd : s4.mem heap + dynGraphSize vcH ecH ≤ h1 := hRawEnd0.trans hresp1.1
  have hdgLe : dynGraphSize vcH ecH ≤ dynGraphSize capLimit capLimit :=
    dynGraphSize_mono (by omega) (by omega)
  obtain ⟨s5, r5, hs5_6, hH5, hs5_mem, _, hs5_regs⟩ :=
    loadShiftGraph_runs (ω := ω) (st := s4)
      ((hs4_regs 4 (by decide)).trans ((hs3_r 4 (by decide) (by decide) (by decide)).trans hp)) hH1
  have hfoot1 : ∀ addr, R.foot handle y1 addr → addr < h1 := fun addr ha => by
    rcases hresp1.2.2.2.2 addr ha with ho | ⟨_, hn⟩
    · exact (hfoot addr ho).trans_le hresp1.1
    · exact hn
  -- Copy graph to caller-owned memory [h1, h2) using live-list copy
  have hCopyFit : h1 + dynGraphSize vcH ecH < 2 ^ w := by
    have := hresp1.2.1; omega
  obtain ⟨s6, c6, r6, hH6, hs6_6, hs6_5, hz6, hrep6, hphi6, hfootDisj6, hmem6, _, hc6, hs6_regs⟩ :=
    copyGraphLive_preserves_tool_runs (ω := ω) (st := s5) himpl.1 (hs5_mem.symm ▸ hrep1) hfoot1
      hs5_6 ((hs5_regs 5 (by decide)).trans hs4_5) (hs5_6 ▸ hH5) hRawEnd hCopyFit hw9
      (hs5_mem.symm ▸ hresp1.2.2.1)
  let h2 := h1 + dynGraphSize vcH ecH
  have hH6_ec : s6.mem (h1 + 1) = ecH := (hs6_6 ▸ hH6).2.2.2.2.1
  let s7 := { s6 with regs := Function.update s6.regs 64 ecH }
  let s8 := { s7 with regs := Function.update s7.regs 4 h2 }
  let s9 := { s8 with regs := Function.update s8.regs 63 h1 }
  let s10 := { s9 with regs := Function.update s9.regs 6 graphBase }
  have r7 : Runs w p ω (.assign 64 (.load (.bin .add (.reg 6) (.const 1)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨ecH, by
      simp [Expr.eval, BinOp.eval, hs6_6, show 1 < 2 ^ w by omega,
        show h1 + 1 < 2 ^ w by unfold dynGraphSize at hCopyFit; omega, hH6_ec], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 4 (.reg 5)) s7 .normal s8 2 :=
    runs_assign_iff.mpr ⟨h2, by simp [Expr.eval, s7, Function.update_of_ne, hs6_5, h2], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 63 (.reg 6)) s8 .normal s9 2 :=
    runs_assign_iff.mpr ⟨h1, by simp [Expr.eval, s8, s7, Function.update_of_ne, hs6_6], rfl, rfl, rfl⟩
  have hs6_69 : s6.regs 69 = graphBase :=
    (hs6_regs 69 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans
      ((hs5_regs 69 (by decide)).trans ((hs4_regs 69 (by decide)).trans (by simp [s3])))
  have r10 : Runs w p ω (.assign 6 (.reg 69)) s9 .normal s10 2 :=
    runs_assign_iff.mpr ⟨graphBase, by simp [Expr.eval, s9, s8, s7, Function.update_of_ne, hs6_69], rfl, rfl, rfl⟩
  have hs6_frame (addr : ℕ) (hlt : addr < heap) (hnf : ¬ R.foot handle x addr) :
      s6.mem addr = st.mem addr :=
    (hmem6 addr (hlt.trans_le hresp1.1)).trans ((congrFun hs5_mem addr).trans
      (hresp1.2.2.2.1 addr hlt hnf))
  have hG10 : DynGraphAt s10.mem graphBase vCap eCap a.G :=
    dynGraphAt_of_agree hG (fun addr hlo hhi =>
      hs6_frame addr (by omega) (hFootG addr hlo hhi))
  have hfoot1_h2 : ∀ addr, R.foot handle y1 addr → addr < h2 := fun addr ha =>
    (hfoot1 addr ha).trans_le (Nat.le_add_right h1 _)
  have hs10_keep (r : ℕ) (h4 : r ≠ 4) (h5 : r ≠ 5) (h6 : r ≠ 6) (h8 : r ≠ 8) (h9 : r ≠ 9)
      (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) (h63 : r ≠ 63) (h64 : r ≠ 64)
      (h65 : r ≠ 65) (h66 : r ≠ 66) (h69 : r ≠ 69) : s10.regs r = st.regs r := by
    simp only [s10, s9, s8, s7, Function.update_of_ne h6, Function.update_of_ne h63,
      Function.update_of_ne h4, Function.update_of_ne h64]
    exact (hs6_regs r h5 h6 h8 h9 h10 h11 h12 h63 h64).trans ((hs5_regs r h6).trans
      ((hs4_regs r h5).trans (hs3_r r h65 h66 h69)))
  -- Op 2: read LSF with L_w at h2 + 4
  have hh2Room5 : h2 + 5 < 2 ^ w := by have := hresp1.2.1; omega
  obtain ⟨s11, h3, c11, y2, r11, hs11_5, hrep2, hLwLe, ⟨vcF, ecF, hLSF11, -, -⟩, hStDesc0, hNum0,
      hDen0, hresp2, hc11, hs11_regs⟩ :=
    ordCoreReadLSFKFBL_runs (ω := ω) (st := s10) hFootAt
      ((hs10_keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb)
      ((hs10_keep 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh)
      (by simp [s10]) (by simp [s10, s9, s8, Function.update_of_ne, h2])
      hj hwk hhw hG10 (hgEnd.trans (hresp1.1.trans (Nat.le_add_right h1 _)))
      hrep6 hIn hfoot1_h2 (by simpa [s10, s9, s8, s7, hs6_5, h2] using hz6) hh2Room5
  let Lw := s11.mem (h2 + 4)
  have hLSF11' : LSFAt s11.mem h2 vcF ecF 4 Lw fmt.precision a.G.E forest := by
    simpa only [hFour] using hLSF11
  have hStDescLe : s11.mem (h2 + 3) + 2 ≤ h3 := hStDesc0.trans hresp2.1
  have hNumLeCL : ∀ e ∈ H.E, s11.mem (s11.mem (h2 + 3)) + e * Lw + Lw ≤ h3 :=
    fun e he => (hNum0 e (hHE he)).trans hresp2.1
  have hDenLeCL : ∀ e ∈ H.E, s11.mem (s11.mem (h2 + 3) + 1) + e * Lw + Lw ≤ h3 :=
    fun e he => (hDen0 e (hHE he)).trans hresp2.1
  have h11_frame_h2 (addr : ℕ) (hlt : addr < h2) (hnf : ¬ R.foot handle y1 addr) :
      s11.mem addr = s6.mem addr := hresp2.2.2.2.1 addr hlt hnf
  have h11_frame_heap (addr : ℕ) (hlt : addr < heap) (hnf : ¬ R.foot handle x addr) :
      s11.mem addr = st.mem addr := by
    have hnf1 : ¬ R.foot handle y1 addr := fun hf => by
      rcases hresp1.2.2.2.2 addr hf with ho | ⟨hlo, _⟩
      · exact hnf ho
      · omega
    exact (h11_frame_h2 addr (hlt.trans_le (hresp1.1.trans (Nat.le_add_right h1 _))) hnf1).trans
      (hs6_frame addr hlt hnf)
  let stretchDesc := s11.mem (h2 + 3)
  let s12 := { s11 with regs := Function.update s11.regs 10 stretchDesc }
  let s13 := { s12 with regs := Function.update s12.regs 11 Lw }
  have r12 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 4) (.const 3)))) s11 .normal s12 5 :=
    runs_assign_iff.mpr ⟨stretchDesc, by
      simp [Expr.eval, BinOp.eval, hs11_regs 4 (by decide), s10, s9, s8, Function.update_of_ne,
        show 3 < 2 ^ w by omega, show h2 + 3 < 2 ^ w by omega, stretchDesc], rfl, rfl, rfl⟩
  have r13 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 4) (.const 4)))) s12 .normal s13 5 :=
    runs_assign_iff.mpr ⟨Lw, by
      simp [Expr.eval, BinOp.eval, s12, Function.update_of_ne, hs11_regs 4 (by decide),
        s10, s9, s8, show 4 < 2 ^ w by omega, show h2 + 4 < 2 ^ w by omega, Lw], rfl, rfl, rfl⟩
  -- Call `coreLenProc` at h3
  have hH13 : DynGraphAt s13.mem h1 vcH ecH H :=
    dynGraphAt_of_agree (hs6_6 ▸ hH6) (fun addr hlo hhi =>
      h11_frame_h2 addr (by dsimp [h2]; omega) (hfootDisj6 addr hlo))
  have hLen13 : EdgeValuesAt s13.mem lenBase 4 L fmt.precision a.G.E ℓ :=
    hLen.congr (fun e he j hj => by
      have heLt : e < eCap := hG.2.2.1 e he
      have hm : e * L + L ≤ eCap * L := by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
      exact h11_frame_heap _ (by omega) (hFootLen _ (by omega) (by omega)))
  have hLenLe13 : ∀ e ∈ H.E, lenBase + e * L + L ≤ h3 := fun e he => by
    have heLt : e < eCap := hG.2.2.1 e (hHE he)
    have hm : e * L + L ≤ eCap * L := by
      have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
    have h1le := hresp1.1; have h2le := hresp2.1
    omega
  let K := max L Lw
  have hKLe : K ≤ LwMax := max_le (by dsimp [LwMax, ordLevelLwMax]; omega) hLwLe
  have hEcLLe : ecH * L ≤ capLimit * L := Nat.mul_le_mul_right L (by omega)
  have hSpLe : H.m * wireCoreLenEdgeSpace K ≤ nextM * wireCoreLenEdgeSpace LwMax :=
    Nat.mul_le_mul hHm (wireCoreLenEdgeSpace_mono hKLe)
  have hCostEdgeLe : H.m * (wireCoreLenEdgeCost K + 30) ≤ H.m * (wireCoreLenEdgeCost LwMax + 30) :=
    Nat.mul_le_mul_left H.m (Nat.add_le_add_right (wireCoreLenEdgeCost_mono hKLe) 30)
  let h4 := h3 + ecH * L + H.m * wireCoreLenEdgeSpace K
  have h4Le : h4 + (1 + ordRotWords a branch) ≤
      heap + 1 + dynGraphSize capLimit capLimit + 5 +
        capLimit * L + nextM * wireCoreLenEdgeSpace (ordLevelLwMax L capExp M N) + (2 + 2 * N + 2 * nextM) := by
    have h1hi := hresp1.2.1; have h2hi := hresp2.2.1
    dsimp [h4, h2, LwMax] at hSpLe ⊢
    omega
  have hCLRoom' : h4 < 2 ^ w := by omega
  obtain ⟨outCL, cCL, rCLBody, hcCL, hNextLenCL, hzCL, hFrCL⟩ :=
    wireCoreLen_runs (w := w) (L := L) (Lw := Lw) (P := fmt.precision) (hBase := h1)
      (vcH := vcH) (ecH := ecH) (stretchDesc := stretchDesc) (lenPtr := lenBase) (heap := h3)
      (H := H) (G_E := a.G.E) (forest := forest) (ℓ := ℓ) (p := p) (ω := ω) (mem := s13.mem)
      (pos := s13.pos) hEdgeProc hSign hMul hDiv hCopy hH13 hHE hLSF11'.2.2.2 hLen13
      hCoreLenFits hresp2.1 hStDescLe hNumLeCL hDenLeCL hLenLe13 hresp2.2.2.1 hCLRoom' (by omega)
  let s14 : State := { regs := Function.update s13.regs 4 h4, mem := outCL.mem, pos := outCL.pos }
  have hs13_7 : s13.regs 7 = lenBase := by
    simp only [s13, s12, Function.update_of_ne (by decide : (7 : ℕ) ≠ 11),
      Function.update_of_ne (by decide : (7 : ℕ) ≠ 10)]
    rw [hs11_regs 7 (by decide)]
    exact (hs10_keep 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl
  have hs13_67 : s13.regs 67 = L := by
    simp only [s13, s12, Function.update_of_ne (by decide : (67 : ℕ) ≠ 11),
      Function.update_of_ne (by decide : (67 : ℕ) ≠ 10)]
    rw [hs11_regs 67 (by decide)]
    exact (hs10_keep 67 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h67
  have r14 : Runs w p ω
      (.call 4 coreLenProc [.reg 63, .reg 10, .reg 7, .reg 67, .reg 11, .reg 5])
      s13 .normal s14 (cCL + 7) :=
    runs_call_iff.mpr ⟨[h1, stretchDesc, lenBase, L, Lw, h3], wireCoreLenBody edgeProc,
      .returned h4, outCL, cCL, by
        simp only [evalArgs, Expr.eval, hs13_7, hs13_67]
        simp [s13, s12, hs11_regs 63 (by decide), hs11_5, s10, s9, Function.update_of_ne],
      hCoreLenProc, rCLBody, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  let s15 := { s14 with regs := Function.update s14.regs 7 h3 }
  let s16 := { s15 with regs := Function.update s15.regs 8 h3 }
  let s17 := { s16 with regs := Function.update s16.regs 2 branch }
  let s18 := { s17 with regs := Function.update s17.regs 3 handle }
  have hs14_5 : s14.regs 5 = h3 := by simp [s14, s13, s12, Function.update_of_ne, hs11_5]
  have hs14_65 : s14.regs 65 = branch := by
    simp only [s14, s13, s12, Function.update_of_ne (by decide : (65 : ℕ) ≠ 4),
      Function.update_of_ne (by decide : (65 : ℕ) ≠ 11),
      Function.update_of_ne (by decide : (65 : ℕ) ≠ 10)]
    rw [hs11_regs 65 (by decide)]
    simp only [s10, s9, s8, s7, Function.update_of_ne (by decide : (65 : ℕ) ≠ 6),
      Function.update_of_ne (by decide : (65 : ℕ) ≠ 63),
      Function.update_of_ne (by decide : (65 : ℕ) ≠ 4),
      Function.update_of_ne (by decide : (65 : ℕ) ≠ 64)]
    rw [hs6_regs 65 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
      hs5_regs 65 (by decide), hs4_regs 65 (by decide)]
    simp [s3, s2, s1, Function.update_of_ne]
  have hs14_66 : s14.regs 66 = handle := by
    simp only [s14, s13, s12, Function.update_of_ne (by decide : (66 : ℕ) ≠ 4),
      Function.update_of_ne (by decide : (66 : ℕ) ≠ 11),
      Function.update_of_ne (by decide : (66 : ℕ) ≠ 10)]
    rw [hs11_regs 66 (by decide)]
    simp only [s10, s9, s8, s7, Function.update_of_ne (by decide : (66 : ℕ) ≠ 6),
      Function.update_of_ne (by decide : (66 : ℕ) ≠ 63),
      Function.update_of_ne (by decide : (66 : ℕ) ≠ 4),
      Function.update_of_ne (by decide : (66 : ℕ) ≠ 64)]
    rw [hs6_regs 66 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
      hs5_regs 66 (by decide), hs4_regs 66 (by decide)]
    simp [s3, s2, Function.update_of_ne]
  have r15 : Runs w p ω (.assign 7 (.reg 5)) s14 .normal s15 2 :=
    runs_assign_iff.mpr ⟨h3, by simp [Expr.eval, hs14_5], rfl, rfl, rfl⟩
  have r16 : Runs w p ω (.assign 8 (.reg 5)) s15 .normal s16 2 :=
    runs_assign_iff.mpr ⟨h3, by simp [Expr.eval, s15, Function.update_of_ne, hs14_5], rfl, rfl, rfl⟩
  have r17 : Runs w p ω (.assign 2 (.reg 65)) s16 .normal s17 2 :=
    runs_assign_iff.mpr ⟨branch, by simp [Expr.eval, s16, s15, Function.update_of_ne, hs14_65], rfl, rfl, rfl⟩
  have r18 : Runs w p ω (.assign 3 (.reg 66)) s17 .normal s18 2 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, s17, s16, s15, Function.update_of_ne, hs14_66], rfl, rfl, rfl⟩
  have hfoot2 : ∀ addr, R.foot handle y2 addr → addr < h3 := fun addr ha => by
    rcases hresp2.2.2.2.2 addr ha with ho | ⟨_, hn⟩
    · exact (hfoot1_h2 addr ho).trans_le hresp2.1
    · exact hn
  have hloc18 := himpl.1 handle a y2 s11.mem s18.mem (fun addr ha => (hFrCL addr (hfoot2 addr ha)).symm)
  have hfoot2_h4 : ∀ addr, R.foot handle y2 addr → addr < h4 := fun addr ha =>
    (hfoot2 addr ha).trans_le (by dsimp [h4]; omega)
  -- Op 5: read output rotation order at h4 -> h5
  obtain ⟨s19, h5, nextOrdWords, c19, y3, r19, hs19_5, hs19_9, hrep3, hOrd19, hOrdLe19, hs19_9h,
      hOrdEnd19', hOrdW19', hresp3, hc19, hs19_regs⟩ :=
    ordCoreReadOrdKFBL_runs (ω := ω) (st := s18) hFootAt
      (by simp [s18, s17, Function.update_of_ne]) (by simp [s18])
      (by simp [s18, s17, s16, s15, s14, Function.update_of_ne])
      hj hwk hhw (hloc18.1 hrep2) hIn hfoot2_h4 hzCL (by omega)
  have hOrdEnd19 : s19.mem h4 + nextOrdWords ≤ h5 := hs19_9 ▸ hOrdEnd19'
  have hOrdW19 : ∀ j < nextOrdWords, s19.mem (s19.mem h4 + j) < 2 ^ w := hs19_9 ▸ hOrdW19'
  let s20 := { s19 with regs := Function.update s19.regs 4 h5 }
  let out := { s20 with regs := Function.update s20.regs 6 h1 }
  have hs19_63 : s19.regs 63 = h1 := by
    rw [hs19_regs 63 (by decide) (by decide)]
    simp only [s18, s17, s16, s15, s14, s13, s12, Function.update_of_ne (by decide : (63 : ℕ) ≠ 3),
      Function.update_of_ne (by decide : (63 : ℕ) ≠ 2), Function.update_of_ne (by decide : (63 : ℕ) ≠ 8),
      Function.update_of_ne (by decide : (63 : ℕ) ≠ 7), Function.update_of_ne (by decide : (63 : ℕ) ≠ 4),
      Function.update_of_ne (by decide : (63 : ℕ) ≠ 11), Function.update_of_ne (by decide : (63 : ℕ) ≠ 10)]
    rw [hs11_regs 63 (by decide)]
    simp [s10, s9, Function.update_of_ne]
  have r20 : Runs w p ω (.assign 4 (.reg 5)) s19 .normal s20 2 :=
    runs_assign_iff.mpr ⟨h5, by simp [Expr.eval, hs19_5], rfl, rfl, rfl⟩
  have r21 : Runs w p ω (.assign 6 (.reg 63)) s20 .normal out 2 :=
    runs_assign_iff.mpr ⟨h1, by simp [Expr.eval, s20, Function.update_of_ne, hs19_63], rfl, rfl, rfl⟩
  have rFull : Runs w p ω (ordReadoutNextLevelKFBL (op 3) (op 2) coreLenProc (op 5)) st .normal out
      (2 + (2 + (2 + (c4 + (3 + (c6 + (5 + (2 + (2 + (2 + (c11 + (5 + (5 + ((cCL + 7) +
        (2 + (2 + (2 + (2 + (c19 + (2 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
        1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 2, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, c4, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 3, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, c6, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 2, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 2, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 2, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, c11, _, r11,
    runs_seq_iff.mpr (Or.inr ⟨s12, 5, _, r12,
    runs_seq_iff.mpr (Or.inr ⟨s13, 5, _, r13,
    runs_seq_iff.mpr (Or.inr ⟨s14, cCL + 7, _, r14,
    runs_seq_iff.mpr (Or.inr ⟨s15, 2, _, r15,
    runs_seq_iff.mpr (Or.inr ⟨s16, 2, _, r16,
    runs_seq_iff.mpr (Or.inr ⟨s17, 2, _, r17,
    runs_seq_iff.mpr (Or.inr ⟨s18, 2, _, r18,
    runs_seq_iff.mpr (Or.inr ⟨s19, c19, _, r19,
    runs_seq_iff.mpr (Or.inr ⟨s20, 2, 2, r20, r21, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hnf2_H (addr : ℕ) (hlo : h1 ≤ addr) (hhi : addr < h2) : ¬ R.foot handle y2 addr := by
    intro hf
    rcases hresp2.2.2.2.2 addr hf with hy1 | ⟨hlo2, _⟩
    · exact hfootDisj6 addr hlo hy1
    · omega
  have hnf2_Len (addr : ℕ) (hlo : h3 ≤ addr) (hhi : addr < h3 + ecH * L) : ¬ R.foot handle y2 addr :=
    fun hf => by have := hfoot2 addr hf; omega
  have hHOut : DynGraphAt out.mem h1 vcH ecH H :=
    dynGraphAt_of_agree hH13 (fun addr hlo hhi =>
      (hresp3.2.2.2.1 addr (by dsimp [h4, h2] at *; have := hresp2.1; omega)
        (hnf2_H addr hlo hhi)).trans (hFrCL addr (by dsimp [h2] at *; have := hresp2.1; omega)))
  have hLenOut : EdgeValuesAt out.mem h3 4 L fmt.precision H.E (coreLen forest ℓ) :=
    hNextLenCL.congr (fun e he j hj => by
      have heLt := hH13.2.2.1 e he
      have hm : e * L + L ≤ ecH * L := by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
      exact hresp3.2.2.2.1 _ (by dsimp [h4]; omega) (hnf2_Len _ (by omega) (by omega)))
  have hout7 : out.regs 7 = h3 := by
    simp only [out, s20, Function.update_of_ne (by decide : (7 : ℕ) ≠ 6),
      Function.update_of_ne (by decide : (7 : ℕ) ≠ 4)]
    rw [hs19_regs 7 (by decide) (by decide)]
    simp [s18, s17, s16, s15, Function.update_of_ne]
  have hout8 : out.regs 8 = h3 := by
    simp only [out, s20, Function.update_of_ne (by decide : (8 : ℕ) ≠ 6),
      Function.update_of_ne (by decide : (8 : ℕ) ≠ 4)]
    rw [hs19_regs 8 (by decide) (by decide)]
    simp [s18, s17, s16, Function.update_of_ne]
  have hout9 : out.regs 9 = s19.mem h4 := by
    simp only [out, s20, Function.update_of_ne (by decide : (9 : ℕ) ≠ 6),
      Function.update_of_ne (by decide : (9 : ℕ) ≠ 4), hs19_9]
  have hfoot3_in (addr : ℕ) (hf : R.foot handle y3 addr) :
      R.foot handle x addr ∨ (heap ≤ addr ∧ addr < h5) := by
    rcases hresp3.2.2.2.2 addr hf with hy2 | ⟨hlo3, hhi3⟩
    · rcases hresp2.2.2.2.2 addr hy2 with hy1 | ⟨hlo2, hhi2⟩
      · rcases hresp1.2.2.2.2 addr hy1 with hx | ⟨hlo1, hhi1⟩
        · exact Or.inl hx
        · exact Or.inr ⟨hlo1, by have := hresp2.1; have := hresp3.1; dsimp [h4, h2] at *; omega⟩
      · exact Or.inr ⟨by have := hresp1.1; dsimp [h2] at *; omega,
          by have := hresp3.1; dsimp [h4] at *; omega⟩
    · exact Or.inr ⟨by have := hresp1.1; have := hresp2.1; dsimp [h4, h2] at *; omega, hhi3⟩
  have hfoot3_lt (addr : ℕ) (hf : R.foot handle y3 addr) : addr < h5 := by
    rcases hfoot3_in addr hf with hx | ⟨_, hhi⟩
    · have := hfoot addr hx; have := hresp1.1; have := hresp2.1; have := hresp3.1
      dsimp [h4, h2] at *; omega
    · exact hhi
  refine ⟨out, vcH, ecH, nextOrdWords, Lw, _, y3, rFull, hLwLe, hvcH, hecH, hcapH, hrep3,
    by simpa [out] using hHOut, by rw [hout7]; exact hLenOut, hout8.trans hout7.symm,
    by simpa [out, s20, Function.update_of_ne] using hOrd19, hOrdLe19,
    by rw [hout9]; simpa [out, s20] using hOrdEnd19,
    by rw [hout9, ← hs19_9, hs19_9h]; have := hresp1.1; have := hresp2.1; dsimp [h4, h2] at *; omega,
    by rw [hout9]; exact hOrdW19,
    by simpa [out] using hresp1.1,
    by simp only [out, s20, Function.update_self, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6)]
       have := hresp2.1; have := hresp3.1; dsimp [h4, h2] at *; omega,
    fun addr hlo hhi hf => by
      simp only [out, Function.update_self] at hlo hhi
      rcases hresp3.2.2.2.2 addr hf with hy2 | ⟨hlo3, _⟩
      · exact hnf2_H addr hlo hhi hy2
      · have := hresp2.1; dsimp [h4, h2] at *; omega,
    by rw [hout7]; have := hresp1.1; have := hresp2.1; dsimp [h2] at *; omega,
    by rw [hout7]; simp only [out, s20, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6), Function.update_self]
       have := hresp3.1; dsimp [h4] at *; omega,
    fun addr hlo hhi hf => by
      rw [hout7] at hlo hhi
      rcases hresp3.2.2.2.2 addr hf with hy2 | ⟨hlo3, _⟩
      · exact hnf2_Len addr hlo hhi hy2
      · dsimp [h4] at hlo3; omega,
    by rw [hout7]; simp only [out, Function.update_self]; exact hresp2.1,
    by simp only [out, s20, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6), Function.update_self]
       have := hresp1.1; have := hresp2.1; have := hresp3.1; dsimp [h4, h2] at *; omega,
    by simp only [out, s20, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6), Function.update_self]
       have := hresp3.2.1; omega,
    by simp only [out, s20, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6), Function.update_self]
       exact hresp3.2.2.1,
    fun addr hlt hnf => by
      have hnf2 : ¬ R.foot handle y2 addr := fun hf => by
        rcases hresp2.2.2.2.2 addr hf with hy1 | ⟨hlo2, _⟩
        · rcases hresp1.2.2.2.2 addr hy1 with hx | ⟨hlo1, _⟩
          · exact hnf hx
          · omega
        · have := hresp1.1; dsimp [h2] at *; omega
      have h1lt : addr < h4 := by have := hresp1.1; have := hresp2.1; dsimp [h4, h2] at *; omega
      have h2lt : addr < h3 := by have := hresp1.1; have := hresp2.1; dsimp [h2] at *; omega
      exact (hresp3.2.2.2.1 addr h1lt hnf2).trans ((hFrCL addr h2lt).trans (h11_frame_heap addr hlt hnf)),
    fun addr hf => by
      simp only [out, s20, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6), Function.update_self]
      exact hfoot3_lt addr hf,
    fun addr hf => by
      simp only [out, s20, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6), Function.update_self]
      exact hfoot3_in addr hf,
    fun r hr => by
      have hne : r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 6 ∧ r ≠ 7 ∧ r ≠ 8 ∧ r ≠ 9 ∧
          r ≠ 10 ∧ r ≠ 11 ∧ r ≠ 12 ∧ r ≠ 63 ∧ r ≠ 64 ∧ r ≠ 65 ∧ r ≠ 66 ∧ r ≠ 69 := by
        rcases hr with rfl | rfl | ⟨_, _⟩ | rfl | rfl | _ <;> omega
      simp only [out, s20, Function.update_of_ne hne.2.2.2.2.1, Function.update_of_ne hne.2.2.1]
      rw [hs19_regs r hne.2.2.2.1 hne.2.2.2.2.2.2.2.1]
      simp only [s18, s17, s16, s15, s14, s13, s12,
        Function.update_of_ne hne.2.1, Function.update_of_ne hne.1,
        Function.update_of_ne hne.2.2.2.2.2.2.1, Function.update_of_ne hne.2.2.2.2.2.1,
        Function.update_of_ne hne.2.2.1,
        Function.update_of_ne hne.2.2.2.2.2.2.2.2.2.1, Function.update_of_ne hne.2.2.2.2.2.2.2.2.1]
      rw [hs11_regs r hne.2.2.2.1]
      exact hs10_keep r hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2.2.1
        hne.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.1
        hne.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.2.1
        hne.2.2.2.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        hne.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    ?_⟩
  change _ + R.phi handle y3 s19.mem ≤ _
  have hphi18 : R.phi handle y2 s18.mem = R.phi handle y2 s11.mem := hloc18.2.symm
  have hphi6' : R.phi handle y1 s10.mem = R.phi handle y1 s4.mem := by
    change R.phi handle y1 s6.mem = R.phi handle y1 s4.mem; rw [hphi6, hs5_mem]
  have hc4' : c4 + R.phi handle y1 s4.mem ≤ P.readout + 4 + R.phi handle x st.mem := hc4
  rw [hphi18] at hc19; rw [hphi6'] at hc11
  change cCL ≤ H.m * (wireCoreLenEdgeCost K + 30) + 60 at hcCL
  dsimp only [H, LwMax] at hCostEdgeLe hcCL ⊢; omega

/-- Legacy wrapper around `ordReadoutNextLevelKFBL_runs_bounded_ord` preserving the exact
postcondition tuple expected by existing callers. -/
theorem ordReadoutNextLevelKFBL_runs_bounded
    {w L depth k M N vCap eCap capExp capLimit init coreLenProc edgeProc signExt mul intDiv copy
      branch handle heap graphBase lenBase nextM : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ : ℕ → ℝ)
    (hFour : fmt.limbBits = 4)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P
        allocation))
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation R p op)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle) (hp : st.regs 4 = heap)
    (hg : st.regs 6 = graphBase) (hl : st.regs 7 = lenBase) (h67 : st.regs 67 = L)
    (hj : branch < k) (hwk : k < 2 ^ w) (hhw : handle < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hG : DynGraphAt st.mem graphBase vCap eCap a.G)
    (hgEnd : graphBase + dynGraphSize vCap eCap ≤ heap)
    (hFootG : ∀ addr, graphBase ≤ addr → addr < graphBase + dynGraphSize vCap eCap →
      ¬ R.foot handle x addr)
    (hLen : EdgeValuesAt st.mem lenBase 4 L fmt.precision a.G.E ℓ)
    (hLenEnd : lenBase + eCap * L ≤ heap)
    (hFootLen : ∀ addr, lenBase ≤ addr → addr < lenBase + eCap * L → ¬ R.foot handle x addr)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap)
    (hz : ZeroFrom st.mem heap)
    (hHE : (tool.S a.st branch).E ⊆ a.G.E)
    (hHm : (tool.S a.st branch).m ≤ nextM)
    (hRotWords : ordRotWords a branch ≤ 1 + 2 * N + 2 * nextM)
    (hCoreLenFits : ∀ e ∈ (tool.S a.st branch).E,
      ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
        coreLen (tool.lsfs a.st branch) ℓ e)
    (hroom :
      let LwMax := ordLevelLwMax L capExp M N
      heap + 1 + dynGraphSize capLimit capLimit + 5 +
        capLimit * L + nextM * wireCoreLenEdgeSpace LwMax + (2 + 2 * N + 2 * nextM) < 2 ^ w) :
    let forest := tool.lsfs a.st branch
    let H := tool.S a.st branch
    let LwMax := ordLevelLwMax L capExp M N
    ∃ (out : State) (vcH ecH nextOrdWords Lw cost : ℕ) (y : R.τ),
      Runs w p ω (ordReadoutNextLevelKFBL (op 3) (op 2) coreLenProc (op 5)) st .normal out cost ∧
      Lw ≤ LwMax ∧
      vcH = vCap ∧ ecH = eCap ∧
      vcH + ecH + 2 ≤ capLimit ∧
      R.rep handle a y out.mem ∧
      DynGraphAt out.mem (out.regs 6) vcH ecH H ∧
      EdgeValuesAt out.mem (out.regs 7) 4 L fmt.precision H.E (coreLen forest ℓ) ∧
      out.regs 8 = out.regs 7 ∧
      OrdListAt out.mem (out.regs 9) (tool.rot a.st branch) nextOrdWords ∧
      nextOrdWords ≤ ordRotWords a branch ∧
      out.regs 9 + nextOrdWords ≤ out.regs 4 ∧ heap < out.regs 9 ∧
      (∀ j < nextOrdWords, out.mem (out.regs 9 + j) < 2 ^ w) ∧
      heap ≤ out.regs 6 ∧ out.regs 6 + dynGraphSize vcH ecH ≤ out.regs 4 ∧
      (∀ addr, out.regs 6 ≤ addr → addr < out.regs 6 + dynGraphSize vcH ecH →
        ¬ R.foot handle y addr) ∧
      heap ≤ out.regs 7 ∧ out.regs 7 + ecH * L ≤ out.regs 4 ∧
      (∀ addr, out.regs 7 ≤ addr → addr < out.regs 7 + ecH * L → ¬ R.foot handle y addr) ∧
      heap ≤ out.regs 4 ∧
      out.regs 4 ≤ heap + 1 + dynGraphSize capLimit capLimit + 5 +
        capLimit * L + nextM * wireCoreLenEdgeSpace LwMax + (2 + 2 * N + 2 * nextM) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ addr < heap, ¬ R.foot handle x addr → out.mem addr = st.mem addr) ∧
      (∀ addr, R.foot handle y addr → addr < out.regs 4) ∧
      (∀ addr, R.foot handle y addr → R.foot handle x addr ∨ (heap ≤ addr ∧ addr < out.regs 4)) ∧
      (∀ r, r = 0 ∨ r = 1 ∨ (13 ≤ r ∧ r ≤ 62) ∨ r = 67 ∨ r = 68 ∨ 70 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi handle y out.mem ≤
        2 * P.readout + copyGraphLiveCost H.n H.m +
          H.m * (wireCoreLenEdgeCost LwMax + 30) +
          P.mul * (ordRotWords a branch + 1) * SparseCore.bundleLogFactor M N +
          R.phi handle x st.mem + 150 := by
  obtain ⟨out, vcH, ecH, nextOrdWords, Lw, cost, y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, h16, h17, h18, h19, h20, _, h21, h22, h23, h24, h25, h26, h27, h28⟩ :=
    ordReadoutNextLevelKFBL_runs_bounded_ord ℓ hFour himpl hFootAt hcapLim hCoreLenProc hEdgeProc
      hSign hMul hDiv hCopy hb hh hp hg hl h67 hj hwk hhw hw9 hG hgEnd hFootG hLen hLenEnd
      hFootLen hrep hIn hfoot hz hHE hHm hRotWords hCoreLenFits hroom
  exact ⟨out, vcH, ecH, nextOrdWords, Lw, cost, y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩

end MinCostFlow.MinRatio
