module

public import MinCostFlow.MinRatio.WireRebuildSuffixK
public import MinCostFlow.MinRatio.WireInitBase
import WordRAM.Tactic

/-!
# Space-bounded K-contract readout and single-level rebuild (`WireInitReadoutK`)

Strengthens `ordReadoutNextLevelK_runs` and `ordRebuildLevelBodyK_runs` (`WireRebuildSuffixK.lean`)
with explicit upper bounds on the final heap cursor `out.regs 4`, output-graph capacity bounds
`vcH + ecH + 2 ≤ capLimit`, and output-order placement/word-fit bounds (`out.regs 9 + nextOrdWords ≤
out.regs 4` and `∀ j < nextOrdWords, out.mem (out.regs 9 + j) < 2 ^ w`) needed to chain levels
`0 .. d - 1` inside `ordRebuildSuffixProgramK` with a uniform `initSpace'` budget.

Bundles the sparse-core readout-layout invariants in `OrdCoreReadoutLayout`, shared between
`WireInitLevelsK` (level initialization) and `WireInitLinkK` (path-tree forest linking).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- Readout-layout and init-space bounds for an implementation of `sparseCoreOrdMachineContractK`
with capacity bound `capLimit` and per-level initialization space `coreInitSpace i`. -/
structure OrdCoreReadoutLayout (w L P_fp capExp capLimit : ℕ)
    (tool : SparseCoreRestartTool) (Rcore : DSRep (SparseCoreOrdAbs tool))
    (allocation : ℕ → List ℕ → ℕ) (coreInitSpace : ℕ → ℕ) (lvlM : ℕ → ℕ) (N₀ : ℕ) : Prop where
  initSpaceLe : ∀ i args, allocation 6 args ≤ coreInitSpace i
  readGraphLayout : ∀ (a : SparseCoreOrdAbs tool) (b handle cur ret vcH ecH : ℕ)
      (y : Rcore.τ) (mem' : ℕ → ℕ),
    cur ≤ ret →
    DynGraphAt mem' (mem' cur) vcH ecH (tool.S a.st b) →
    vcH + ecH + 2 ≤ capLimit ∧
    mem' cur + dynGraphSize vcH ecH ≤ ret ∧
    (∀ addr, mem' cur ≤ addr → addr < mem' cur + dynGraphSize vcH ecH →
      Rcore.foot handle y addr ∨ (cur ≤ addr ∧ addr < ret))
  readLSFLayout : ∀ (a : SparseCoreOrdAbs tool) (b handle cur ret vcF ecF Lw : ℕ)
      (y : Rcore.τ) (mem' : ℕ → ℕ),
    cur ≤ ret →
    LSFAt mem' cur vcF ecF 4 Lw P_fp a.G.E (tool.lsfs a.st b) →
    let fBase := mem' (cur + 1)
    let stDesc := mem' (cur + 3)
    fBase + dynGraphSize vcF ecF ≤ ret ∧
    (∀ addr, fBase ≤ addr → addr < fBase + dynGraphSize vcF ecF →
      Rcore.foot handle y addr ∨ (cur ≤ addr ∧ addr < ret)) ∧
    stDesc + 2 ≤ ret ∧
    (∀ e ∈ (tool.S a.st b).E, mem' stDesc + e * Lw + Lw ≤ ret) ∧
    (∀ e ∈ (tool.S a.st b).E, mem' (stDesc + 1) + e * Lw + Lw ≤ ret)
  readOrdLayout : ∀ (a : SparseCoreOrdAbs tool) (b cur ret words : ℕ) (mem' : ℕ → ℕ),
    cur ≤ ret →
    OrdListAt mem' (mem' cur) (tool.rot a.st b) words →
    mem' cur + words ≤ ret ∧ (∀ j < words, mem' (mem' cur + j) < 2 ^ w)

/-- Maximum stretch-table limb count `L_w` emitted by op `2` at level with bounds `(M, N)`. -/
@[expose] def ordLevelLwMax (L capExp M N : ℕ) : ℕ :=
  L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)

/-- Explicit upper bound on the heap words allocated by one iteration of `ordRebuildLevelBodyK`
at a level with size bounds `(M, N)`, output edge bound `nextM`, capacity limit `capLimit`, and
sparse-core init space `initSp`. -/
@[expose] def ordLevelSpace (L capExp capLimit initSp M N nextM : ℕ) : ℕ :=
  let LwMax := ordLevelLwMax L capExp M N
  initSp + 1 + dynGraphSize capLimit capLimit + 5 +
    capLimit * L + nextM * wireCoreLenEdgeSpace LwMax + (2 + 2 * N + 2 * nextM)

/-- Explicit upper bound on the non-tool step cost (plus readout/copy/coreLen/order overhead) of
one iteration of `ordRebuildLevelBodyK` (excluding `P.mul * tool.cost a0.st`). -/
@[expose] def ordLevelFixedCost (L capExp capLimit : ℕ) (P : SparseCoreOrdParams)
    (M N nextM : ℕ) : ℕ :=
  let LwMax := ordLevelLwMax L capExp M N
  P.mul * (N + M + (2 * N + 2 * M + 1) + 1) +
    P.mul * (2 * N + 2 * nextM + 2) * SparseCore.bundleLogFactor M N +
    2 * P.readout + 17 * dynGraphSize capLimit capLimit +
    nextM * (wireCoreLenEdgeCost LwMax + 30) + 235

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

/-- Space- and word-bounded execution of `ordReadoutNextLevelK` under `OrdCoreReadoutLayout`. -/
theorem ordReadoutNextLevelK_runs_bounded
    {w L k M N vCap eCap capExp capLimit init coreLenProc edgeProc signExt mul intDiv copy
      branch handle heap graphBase lenBase nextM : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ} {coreInitSpace lvlM : ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ : ℕ → ℝ)
    (hFour : fmt.limbBits = 4)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractK fmt L tool initialGraph k M N vCap eCap capExp P allocation))
    (hLayout : OrdCoreReadoutLayout w L fmt.precision capExp capLimit tool R allocation
      coreInitSpace lvlM N)
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
      Runs w p ω (ordReadoutNextLevelK (op 3) (op 2) coreLenProc (op 5)) st .normal out cost ∧
      Lw ≤ LwMax ∧
      vcH + ecH + 2 ≤ capLimit ∧
      R.rep handle a y out.mem ∧
      DynGraphAt out.mem (out.regs 6) vcH ecH H ∧
      EdgeValuesAt out.mem (out.regs 7) 4 L fmt.precision H.E (coreLen forest ℓ) ∧
      out.regs 8 = out.regs 7 ∧
      OrdListAt out.mem (out.regs 9) (tool.rot a.st branch) nextOrdWords ∧
      nextOrdWords ≤ ordRotWords a branch ∧
      out.regs 9 + nextOrdWords ≤ out.regs 4 ∧
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
      (∀ r, r = 0 ∨ r = 1 ∨ (13 ≤ r ∧ r ≤ 62) ∨ r = 67 ∨ r = 68 ∨ 70 ≤ r →
        out.regs r = st.regs r) ∧
      cost + R.phi handle y out.mem ≤
        2 * P.readout + 17 * dynGraphSize capLimit capLimit +
          nextM * (wireCoreLenEdgeCost LwMax + 30) +
          P.mul * (2 * N + 2 * nextM + 2) * SparseCore.bundleLogFactor M N +
          R.phi handle x st.mem + 190 := by
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
  obtain ⟨s4, h1, c4, y1, r4, hs4_5, hrep1, ⟨vcH, ecH, hH1⟩, hresp1, hc4, hs4_regs⟩ :=
    ordCoreReadGraphK_runs (ω := ω) (st := s3) himpl
      ((hs3_r 2 (by decide) (by decide) (by decide)).trans hb)
      ((hs3_r 3 (by decide) (by decide) (by decide)).trans hh)
      ((hs3_r 4 (by decide) (by decide) (by decide)).trans hp)
      hj hwk hhw hrep hIn hfoot hz (by omega)
  obtain ⟨hcapH, hRawEnd, _⟩ := hLayout.readGraphLayout a branch handle heap h1 vcH ecH y1 s4.mem
    hresp1.1 hH1
  have hdgLe : dynGraphSize vcH ecH ≤ dynGraphSize capLimit capLimit :=
    dynGraphSize_mono (by omega) (by omega)
  obtain ⟨s5, r5, hs5_6, hH5, hs5_mem, _, hs5_regs⟩ :=
    loadShiftGraph_runs (ω := ω) (st := s4)
      ((hs4_regs 4 (by decide)).trans ((hs3_r 4 (by decide) (by decide) (by decide)).trans hp)) hH1
  have hfoot1 : ∀ addr, R.foot handle y1 addr → addr < h1 := fun addr ha => by
    rcases hresp1.2.2.2.2 addr ha with ho | ⟨_, hn⟩
    · exact (hfoot addr ho).trans_le hresp1.1
    · exact hn
  -- Copy graph to caller-owned memory [h1, h2)
  have hCopyFit : h1 + dynGraphSize vcH ecH < 2 ^ w := by
    have := hresp1.2.1; omega
  obtain ⟨s6, c6, r6, hH6, hs6_6, hs6_5, hz6, hrep6, hphi6, hfootDisj6, hmem6, _, hc6, hs6_regs⟩ :=
    copyShiftGraph_preserves_tool_runs (ω := ω) (st := s5) himpl.1 (hs5_mem.symm ▸ hrep1) hfoot1
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
    (hs6_regs 69 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
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
  have hs10_keep (r : ℕ) (h4 : r ≠ 4) (h5 : r ≠ 5) (h6 : r ≠ 6) (h10 : r ≠ 10)
      (h11 : r ≠ 11) (h12 : r ≠ 12) (h63 : r ≠ 63) (h64 : r ≠ 64)
      (h65 : r ≠ 65) (h66 : r ≠ 66) (h69 : r ≠ 69) : s10.regs r = st.regs r := by
    simp only [s10, s9, s8, s7, Function.update_of_ne h6, Function.update_of_ne h63,
      Function.update_of_ne h4, Function.update_of_ne h64]
    exact (hs6_regs r h5 h6 h10 h11 h12).trans ((hs5_regs r h6).trans
      ((hs4_regs r h5).trans (hs3_r r h65 h66 h69)))
  -- Op 2: read LSF with L_w at h2 + 4
  have hh2Room5 : h2 + 5 < 2 ^ w := by have := hresp1.2.1; omega
  obtain ⟨s11, h3, c11, y2, r11, hs11_5, hrep2, hLwLe, ⟨vcF, ecF, hLSF11⟩, hresp2, hc11, hs11_regs⟩ :=
    ordCoreReadLSFK_runs (ω := ω) (st := s10) himpl
      ((hs10_keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb)
      ((hs10_keep 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh)
      (by simp [s10]) (by simp [s10, s9, s8, Function.update_of_ne, h2])
      hj hwk hhw hG10 (hgEnd.trans (hresp1.1.trans (Nat.le_add_right h1 _)))
      hrep6 hIn hfoot1_h2 (by simpa [s10, s9, s8, s7, hs6_5, h2] using hz6) hh2Room5
  let Lw := s11.mem (h2 + 4)
  have hLSF11' : LSFAt s11.mem h2 vcF ecF 4 Lw fmt.precision a.G.E forest := by
    simpa only [hFour] using hLSF11
  obtain ⟨_, _, hStDescLe, hNumLeCL, hDenLeCL⟩ :=
    hLayout.readLSFLayout a branch handle h2 h3 vcF ecF Lw y2 s11.mem hresp2.1 hLSF11'
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
  have hCostEdgeLe : H.m * (wireCoreLenEdgeCost K + 30) ≤ nextM * (wireCoreLenEdgeCost LwMax + 30) :=
    Nat.mul_le_mul hHm (Nat.add_le_add_right (wireCoreLenEdgeCost_mono hKLe) 30)
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
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl
  have hs13_67 : s13.regs 67 = L := by
    simp only [s13, s12, Function.update_of_ne (by decide : (67 : ℕ) ≠ 11),
      Function.update_of_ne (by decide : (67 : ℕ) ≠ 10)]
    rw [hs11_regs 67 (by decide)]
    exact (hs10_keep 67 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans h67
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
    rw [hs6_regs 65 (by decide) (by decide) (by decide) (by decide) (by decide),
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
    rw [hs6_regs 66 (by decide) (by decide) (by decide) (by decide) (by decide),
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
  obtain ⟨s19, h5, nextOrdWords, c19, y3, r19, hs19_5, hs19_9, hrep3, hOrd19, hOrdLe19,
      hresp3, hc19, hs19_regs⟩ :=
    ordCoreReadOrdK_runs (ω := ω) (st := s18) himpl
      (by simp [s18, s17, Function.update_of_ne]) (by simp [s18])
      (by simp [s18, s17, s16, s15, s14, Function.update_of_ne])
      hj hwk hhw (hloc18.1 hrep2) hIn hfoot2_h4 hzCL (by omega)
  obtain ⟨hOrdEnd19, hOrdW19⟩ :=
    hLayout.readOrdLayout a branch h4 h5 nextOrdWords s19.mem hresp3.1 (hs19_9 ▸ hOrd19)
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
  have rFull : Runs w p ω (ordReadoutNextLevelK (op 3) (op 2) coreLenProc (op 5)) st .normal out
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
  refine ⟨out, vcH, ecH, nextOrdWords, Lw, _, y3, rFull, hLwLe, hcapH, hrep3,
    by simpa [out] using hHOut, by rw [hout7]; exact hLenOut, hout8.trans hout7.symm,
    by simpa [out, s20, Function.update_of_ne] using hOrd19, hOrdLe19,
    by rw [hout9]; simpa [out, s20] using hOrdEnd19,
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
      exact hs10_keep r hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.1
        hne.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.2.1
        hne.2.2.2.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        hne.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    ?_⟩
  change _ + R.phi handle y3 s19.mem ≤ _
  have hphi18 : R.phi handle y2 s18.mem = R.phi handle y2 s11.mem := hloc18.2.symm
  have hphi6' : R.phi handle y1 s10.mem = R.phi handle y1 s4.mem := by
    change R.phi handle y1 s6.mem = R.phi handle y1 s4.mem; rw [hphi6, hs5_mem]
  have hc4' : c4 + R.phi handle y1 s4.mem ≤ P.readout + 4 + R.phi handle x st.mem := hc4
  have h17dg : 17 * dynGraphSize vcH ecH ≤ 17 * dynGraphSize capLimit capLimit :=
    Nat.mul_le_mul_left 17 hdgLe
  have hordCostLe :
      P.mul * (ordRotWords a branch + 1) * SparseCore.bundleLogFactor M N ≤
        P.mul * (2 * N + 2 * nextM + 2) * SparseCore.bundleLogFactor M N :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  rw [hphi18] at hc19; rw [hphi6'] at hc11
  change cCL ≤ H.m * (wireCoreLenEdgeCost K + 30) + 60 at hcCL
  dsimp only [LwMax] at hCostEdgeLe ⊢; omega

/-- Space- and word-bounded execution of one iteration of `ordRebuildLevelBodyK` under
`OrdCoreReadoutLayout`. -/
theorem ordRebuildLevelBodyK_runs_bounded
    {w L k M N vCap eCap capExp capLimit init coreLenProc edgeProc signExt mul intDiv copy
      graphBase lenBase gradBase ordBase ordWords heap handleCell branchCell lvlMTable idx
      nextM : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ} {coreInitSpace lvlM : ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ) (ordFn : ℕ → List End)
    (hFour : fmt.limbBits = 4)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractK fmt L tool G k M N vCap eCap capExp P allocation))
    (hLayout : OrdCoreReadoutLayout w L fmt.precision capExp capLimit tool R allocation
      coreInitSpace lvlM N)
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
    (hMCell : st.mem (lvlMTable + idx) = M) (hMAddrW : lvlMTable + idx < 2 ^ w)
    (hk : 0 < k) (hwk : k < 2 ^ w) (hMw : M < 2 ^ w) (hNw : N < 2 ^ w) (hw9 : 9 < 2 ^ w)
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
      Runs w p ω (ordRebuildLevelBodyK init (op 3) (op 2) coreLenProc (op 5)) st .normal out cost ∧
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
      out.regs 9 + nextOrdWords ≤ out.regs 4 ∧
      (∀ j < nextOrdWords, out.mem (out.regs 9 + j) < 2 ^ w) ∧
      heap ≤ out.regs 6 ∧ out.regs 6 + dynGraphSize vcH ecH ≤ out.regs 4 ∧
      heap ≤ out.regs 7 ∧ out.regs 7 + ecH * L ≤ out.regs 4 ∧
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
  have hInitAllocLe : allocation 6 [graphBase, lenBase, gradBase, ordBase, k, M, N, heap] ≤
      coreInitSpace idx := hLayout.initSpaceLe idx _
  have hRoomInit : heap + allocation 6 [graphBase, lenBase, gradBase, ordBase, k, M, N, heap] < 2 ^ w := by
    dsimp only [ordLevelSpace] at hroom; omega
  -- Step 1: Load M from lvlMTable + idx
  let s1 := { st with regs := Function.update st.regs 55 M }
  have r1 : Runs w p ω (.assign 55 (.load (.bin .add (.reg 57) (.reg 19)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨M, by simp [Expr.eval, BinOp.eval, hMTab, hIdx, hMAddrW, hMCell], rfl, rfl, rfl⟩
  have hs1_r (r : ℕ) (h55 : r ≠ 55) : s1.regs r = st.regs r := Function.update_of_ne h55 _ _
  -- Step 2: Init sparse-core level
  obtain ⟨s2, ret0, c2, y0, r2, hs2_2, hs2_3, hs2_4, hrep0, hIn0, hresp0, hc2⟩ :=
    ordCoreInitK_tables_runs (ω := ω) (st := s1) ℓ g ordFn himpl
      ((hs1_r 6 (by decide)).trans hg) ((hs1_r 7 (by decide)).trans hl)
      ((hs1_r 8 (by decide)).trans hgr) ((hs1_r 9 (by decide)).trans ho)
      ((hs1_r 1 (by decide)).trans hkR) (by simp [s1])
      ((hs1_r 56 (by decide)).trans hNR) ((hs1_r 4 (by decide)).trans hh)
      hk hwk hMw hNw hword hG hm hn hgb hlb hgrb hord hordb hordW hrot
      (hFour ▸ hℓ) (hFour ▸ hgv) hpos hz hRoomInit
  have hs2_r (r : ℕ) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) : s2.regs r = s1.regs r :=
    ordCoreInitStmtK_preserves_regs r2 h2 h3 h4
  have hfoot0 (addr : ℕ) (hf : R.foot heap y0 addr) : heap ≤ addr ∧ addr < ret0 :=
    (hresp0.2.2.2.2 addr hf).resolve_left id
  -- Step 3: Store handle and branch 0
  obtain ⟨s3, r3, hs3_h, hs3_b, hrep3, hphi3, hs3_frame, hs3_regs, _⟩ :=
    storeRebuiltLevel_preserves_tool_runs (ω := ω) (st := s2) himpl.1
      ((hs2_r 51 (by decide) (by decide) (by decide)).trans ((hs1_r 51 (by decide)).trans h51))
      ((hs2_r 52 (by decide) (by decide) (by decide)).trans ((hs1_r 52 (by decide)).trans h52))
      hne (hs2_3.symm ▸ hhBelow) (hs2_3.symm ▸ hbBelow)
      (fun addr hf => hs2_3.symm ▸ (hfoot0 addr (hs2_3 ▸ hf)).1) (hs2_3.symm ▸ hrep0)
  have hs3_lt (addr : ℕ) (hlt : addr < heap) (hh' : addr ≠ handleCell) (hb' : addr ≠ branchCell) :
      s3.mem addr = st.mem addr :=
    (hs3_frame addr hh' hb').trans (hresp0.2.2.2.1 addr hlt id)
  have hs3_G : DynGraphAt s3.mem graphBase vCap eCap G :=
    dynGraphAt_of_agree hG (fun addr hlo hhi =>
      hs3_lt addr (by omega) (hDisjG addr hlo hhi).1 (hDisjG addr hlo hhi).2)
  have hs3_Len : EdgeValuesAt s3.mem lenBase 4 L fmt.precision G.E ℓ :=
    hℓ.congr (fun e he j hj => by
      have heLt := hG.2.2.1 e he
      have hm' : e * L + L ≤ eCap * L := by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
      exact hs3_lt _ (by omega) (hDisjLen _ (by omega) (by omega)).1 (hDisjLen _ (by omega) (by omega)).2)
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
  obtain ⟨s4, vcH, ecH, nextOrdWords, _Lw, c4, y4, r4, _, hcapH, hrep4, hH4, hLen4, hGrad4,
      hOrd4, hOrdLe4, hOrdEnd4, hOrdW4, h6Lo4, hHEnd4, _, h7Lo4, hLenEnd4, _, h4Lo4, h4Hi4, hz4,
      hs4_frame, _, hs4_footIn, hs4_regs, hc4⟩ :=
    ordReadoutNextLevelK_runs_bounded (ω := ω) (st := s3) ℓ hFour himpl hLayout
      hCoreLenProc hEdgeProc hSign hMul hDiv hCopy
      (hs3_regs.symm ▸ hs2_2) (hs3_regs.symm ▸ hs2_3) (hs3_regs.symm ▸ hs2_4)
      ((hs3_regs.symm ▸ hs2_r 6 (by decide) (by decide) (by decide)).trans ((hs1_r 6 (by decide)).trans hg))
      ((hs3_regs.symm ▸ hs2_r 7 (by decide) (by decide) (by decide)).trans ((hs1_r 7 (by decide)).trans hl))
      ((hs3_regs.symm ▸ hs2_r 67 (by decide) (by decide) (by decide)).trans ((hs1_r 67 (by decide)).trans h67))
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
  have rFull : Runs w p ω (ordRebuildLevelBodyK init (op 3) (op 2) coreLenProc (op 5)) st .normal out
      (5 + (c2 + (7 + (c4 + 9 + 1) + 1) + 1) + 1) :=
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
  refine ⟨out, vcH, ecH, nextOrdWords, _, y4, rFull, hcapH, ?_, ?_,
    (houtRegs 19 (by decide) (by decide)).trans ((hs4_regs 19 (by omega)).trans
      (hs3_regs.symm ▸ ((hs2_r 19 (by decide) (by decide) (by decide)).trans ((hs1_r 19 (by decide)).trans hIdx)))),
    hout51, hout52, houtMem.symm ▸ hrep4,
    by rw [houtMem, h6Eq]; exact hH4,
    by rw [houtMem, h7Eq]; exact hLen4,
    by rw [h8Eq, h7Eq]; exact hGrad4,
    by rw [houtMem, h9Eq]; exact hOrd4,
    hOrdLe4,
    by rw [h9Eq, h4Eq]; exact hOrdEnd4,
    by rw [houtMem, h9Eq]; exact hOrdW4,
    by rw [h6Eq]; exact hresp0.1.trans h6Lo4,
    by rw [h6Eq, h4Eq]; exact hHEnd4,
    by rw [h7Eq]; exact hresp0.1.trans h7Lo4,
    by rw [h7Eq, h4Eq]; exact hLenEnd4,
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
  · rw [houtMem, hs4_frame branchCell (hbBelow.trans_le hresp0.1) (hnf0 branchCell hbBelow), hs3_b]
  · rw [houtMem]
    rw [hs3_regs, hs2_3] at hphi3
    have hphiEq : R.phi heap y0 s3.mem = R.phi heap y0 s2.mem := hphi3
    rw [hphiEq] at hc4
    have hmulInit :
        P.mul * (tool.cost (tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn) + G.n + G.m + ordWords + 1) ≤
        P.mul * tool.cost (tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn) +
        P.mul * (N + M + (2 * N + 2 * M + 1) + 1) := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left _ (by omega)
    dsimp only [ordLevelFixedCost]
    dsimp only at hc2 hc4 ⊢
    omega

end MinCostFlow.MinRatio
