module

public import MinCostFlow.MinRatio.OrdCoreOps
public import MinCostFlow.MinRatio.RebuildGradients
public import MinCostFlow.DynSpanner.Program.StateLayout
import WordRAM.Tactic

/-!
# Shared ordered readout and gradient-preparation tail (`ordReadoutsAndGradTail`)

Shared deterministic Word-RAM sequence run immediately after initializing a sparse-core level
(in `OrdRebuildSuffix`) or restarting a branch (in `OrdShiftCore`).

Order of operations (chosen so every output passed to the next level lies strictly outside the
current level's `R.foot`):
1. Read sparsifier graph (op `3`) and copy it to caller-owned memory (`copyGraphFromHeader`).
2. Read LSF (op `2`) at the new heap, load next-level lengths (`loadShiftForestLengths`), and
   compute next-level gradients (`prepareShiftReadoutGradients`), producing `nextGrad` in
   caller-owned memory.
3. Copy `nextLengths` (`ecH * L` words) to caller-owned memory via `copyWords` (`copyWordsContract`).
4. Read the active branch's output rotation order `OrdListAt` of `tool.rot a.st branch` (op `5`)
   LAST, into register `9`. Because `nextGraph`, `nextGrad`, and `nextLengths` are all disjoint
   from `R.foot`, op `5` leaves all three intact while delivering `nextOrd` directly in `reg 9`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- Gradient-scan cost expression matching `prepareShiftReadoutGradients_runs`. -/
@[expose] def ordGradScanCost (forest : LSF) (H : MGraph) (limbs : ℕ) : ℕ :=
  280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
  forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
  (129 * limbs + 172) * H.m + 202

/-- Scratch space required by `prepareShiftReadoutGradients_runs`. -/
@[expose] def ordGradScanSpace (forest : LSF) (H : MGraph) (vcF ecG limbs : ℕ) : ℕ :=
  forest.T.n + vcF * limbs + limbs + vcF + vcF +
  3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m

/-- Step 1–2 prefix: read sparsifier graph (op `3`), copy it to caller memory, read LSF (op `2`),
load next lengths, and run `prepareShiftReadoutGradients`. Leaves `branch` in `reg 65`, `handle`
in `reg 66`, `ecH` in `reg 64`, `nextGraph` in `reg 6`, `nextLengths` in `reg 7`, `nextGrad` in
`reg 8`, and free heap in `reg 4`. -/
@[expose] def ordReadoutsPrefix (readGraph readLSF copy sort entry : ℕ) : Stmt :=
  .assign 65 (.reg 2) ;;
  .assign 66 (.reg 3) ;;
  .assign 69 (.reg 6) ;;
  ordCoreReadGraphStmt readGraph ;;
  loadShiftGraph ;;
  copyGraphFromHeader ;;
  .assign 64 (.load (.bin .add (.reg 6) (.const 1))) ;;
  .assign 4 (.reg 5) ;;
  .assign 63 (.reg 6) ;;
  .assign 6 (.reg 69) ;;
  ordCoreReadLSFStmt readLSF ;;
  .assign 9 (.reg 4) ;;
  .assign 6 (.reg 63) ;;
  loadShiftForestLengths ;;
  passRebuildGradient ;;
  prepareShiftReadoutGradients copy sort entry

/-- Step 3–4 suffix: copy `nextLengths` (`ecH * L` words) into caller memory via `copyWords`,
then call op `5` (`ordCoreReadOrdStmt`) to place `OrdListAt` of `tool.rot` in `reg 9` and the
new free heap in `reg 4`. -/
@[expose] def ordCopyLengthsAndReadOrd (copy readOrd : ℕ) : Stmt :=
  .assign 10 (.bin .mul (.reg 64) (.reg 67)) ;;
  .call 11 copy [.reg 7, .reg 4, .reg 10] ;;
  .assign 7 (.reg 4) ;;
  .assign 4 (.bin .add (.reg 4) (.reg 10)) ;;
  .assign 2 (.reg 65) ;;
  .assign 3 (.reg 66) ;;
  ordCoreReadOrdStmt readOrd ;;
  .assign 4 (.reg 5)

/-- Full shared readout and gradient/order preparation tail after core Init or Restart. -/
@[expose] def ordReadoutsAndGradTail
    (readGraph readLSF readOrd copy sort entry : ℕ) : Stmt :=
  ordReadoutsPrefix readGraph readLSF copy sort entry ;;
  ordCopyLengthsAndReadOrd copy readOrd

theorem prepareShiftReadoutGradients_noRand (copy sort entry : ℕ) :
    (prepareShiftReadoutGradients copy sort entry).NoRand := by
  simp only [prepareShiftReadoutGradients, setShiftGradientWidth, loadShiftTreeTraversal,
    passShiftTraversalInputs, computeDeeperGradients, computeForestPotentials,
    setupForestTraversal, prepareOrderedForestNames, loadForestActiveNames,
    reserveForestActiveNames, orderForestActiveNames, copyForestActiveNames, sortForestActiveNames,
    reserveForestTraversal, reserveForestPotentials, reserveForestVisited, reserveForestQueue,
    propagateForestVertices, propagateOrderedForestVertex, loadOrderedForestVertex,
    propagateForestRootCandidate, visitFreshForestChild, propagateForestComponent,
    enqueueForestRoot, propagateForestQueue, scanForestQueueParent,
    propagateForestParent, loadForestIncidenceHead, propagateForestAdjacency,
    propagateForestIncidence, propagateAndEnqueueForestChild, propagateForestChild,
    scanForestIncidence, readForestChildAndAdvance, readForestChild, loadForestChild,
    decodeForestIncidence, loadForestIncidenceNext, advanceForestRead, loadForestChildVisited,
    addressForestGradient, writeAndMarkForestChild, writeNamedForestPotential,
    forestPotentialAddresses, writeForestPotential, selectForestPotentialOperands,
    forestPotentialOperandPair, markForestChildVisited, enqueueForestChild,
    reserveAndPrepareDeeperGradients, reserveDeeperGradients,
    prepareShiftGradientInputs, prepareShiftGradients,
    prepareShiftGradientTable, readShiftGradientEdges, shiftGradientStep, shiftGradientArgs,
    shiftGradientSlotArgs, shiftGradientPotentialArgs, shiftPotentialAddress,
    callShiftGradientCell, forRange, forUp, Stmt.NoRand]
  trivial

theorem ordReadoutsPrefix_noRand (readGraph readLSF copy sort entry : ℕ) :
    (ordReadoutsPrefix readGraph readLSF copy sort entry).NoRand := by
  simp only [ordReadoutsPrefix, ordCoreReadGraphStmt_noRand, loadShiftGraph, copyGraphFromHeader,
    readGraphCopySize, copyReadoutGraphAtHeap, copyReadoutGraph,
    ordCoreReadLSFStmt_noRand, loadShiftForestLengths_noRand, passRebuildGradient,
    prepareShiftReadoutGradients_noRand, Stmt.NoRand]
  trivial

theorem ordCopyLengthsAndReadOrd_noRand (copy readOrd : ℕ) :
    (ordCopyLengthsAndReadOrd copy readOrd).NoRand := by
  simp [ordCopyLengthsAndReadOrd, ordCoreReadOrdStmt_noRand, Stmt.NoRand]

theorem ordReadoutsAndGradTail_noRand (readGraph readLSF readOrd copy sort entry : ℕ) :
    (ordReadoutsAndGradTail readGraph readLSF readOrd copy sort entry).NoRand := by
  simp [ordReadoutsAndGradTail, ordReadoutsPrefix_noRand, ordCopyLengthsAndReadOrd_noRand,
    Stmt.NoRand]

/-- Helper: `EdgeValuesAt` is preserved when copying `ecH * L` words from `src` to `dst`. -/
private theorem edgeValuesAt_of_copyWords {mem mem' : ℕ → ℕ} {src dst ecH h L P : ℕ}
    {H : MGraph} {f : ℕ → ℝ}
    (hE : ∀ e ∈ H.E, e < ecH)
    (hval : EdgeValuesAt mem src h L P H.E f)
    (hcp : ∀ i < ecH * L, mem' (dst + i) = mem (src + i)) :
    EdgeValuesAt mem' dst h L P H.E f := by
  intro e he
  have heLt : e < ecH := hE e he
  have hbound : e * L + L ≤ ecH * L := by
    have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt)
    rwa [Nat.succ_mul] at this
  have hag : ∀ j < L, mem' (dst + e * L + j) = mem (src + e * L + j) := fun j hj => by
    have h1 := hcp (e * L + j) (by omega)
    simpa [Nat.add_assoc] using h1
  obtain ⟨hv, hf⟩ := hval e he
  refine ⟨fun j hj => by rw [hag j hj]; exact hv j hj, ?_⟩
  rw [← hf]
  unfold Num.fixVal
  rw [Num.intVal_congr hag]

/-- Execute `ordReadoutsPrefix` (Steps 1–2): reads graph (op `3`), copies it to caller memory,
reads LSF (op `2`), loads next lengths, and computes next gradients into caller memory. -/
theorem ordReadoutsPrefix_runs
    {w L k M N vCap eCap init copy sort entry branch handle heap graphBase gradBase : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hcell : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w fmt.limbBits x y z))
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle) (hp : st.regs 4 = heap)
    (hg : st.regs 6 = graphBase) (hgr : st.regs 8 = gradBase)
    (h50 : st.regs 50 = eCap)
    (h15 : st.regs 15 = dgETailSlotBase graphBase vCap eCap)
    (h16 : st.regs 16 = dgEHeadSlotBase graphBase vCap eCap)
    (h17 : st.regs 17 = dgIntToExtBase graphBase vCap)
    (h67 : st.regs 67 = L)
    (hj : branch < k) (hwk : k < 2 ^ w) (hhw : handle < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hG : DynGraphAt st.mem graphBase vCap eCap a.G)
    (hgEnd : graphBase + dynGraphSize vCap eCap ≤ heap)
    (hFootG : ∀ addr, graphBase ≤ addr → addr < graphBase + dynGraphSize vCap eCap →
      ¬ R.foot handle x addr)
    (hgradVal : EdgeValuesAt st.mem gradBase fmt.limbBits L fmt.precision a.G.E g)
    (hgradEnd : gradBase + eCap * L ≤ heap)
    (hFootGrad : ∀ addr, gradBase ≤ addr → addr < gradBase + eCap * L → ¬ R.foot handle x addr)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap)
    (hz : ZeroFrom st.mem heap)
    (hforest : (tool.lsfs a.st branch).T.IsForest)
    (hsub : (tool.lsfs a.st branch).T.E ⊆ a.G.E)
    (hverts : a.G.V ⊆ (tool.lsfs a.st branch).T.V)
    (hHE : (tool.S a.st branch).E ⊆ a.G.E)
    (hCopyRoom : ∀ (m1 : ℕ → ℕ) (h1 rawGraph vcH ecH : ℕ),
      DynGraphAt m1 rawGraph vcH ecH (tool.S a.st branch) →
      heap ≤ h1 → h1 ≤ heap + 1 →
      rawGraph + dynGraphSize vcH ecH ≤ h1 ∧ h1 + dynGraphSize vcH ecH + 4 < 2 ^ w)
    (hScanFits : ∀ (m2 : ℕ → ℕ) (_vcH ecH vcF ecF lsfHdr h3 : ℕ),
      let forest := tool.lsfs a.st branch
      let H := tool.S a.st branch
      LSFAt m2 lsfHdr vcF ecF fmt.limbBits L fmt.precision a.G.E forest →
      heap ≤ lsfHdr → lsfHdr ≤ h3 → h3 ≤ lsfHdr + 4 →
      lsfHdr + 3 < 2 ^ w ∧
      m2 lsfHdr + dynGraphSize vcF ecF ≤ h3 ∧
      dgVListBase (m2 lsfHdr) vcF + forest.T.n ≤ h3 ∧
      EdgeValuesAt m2 (m2 (m2 (lsfHdr + 3) + 1)) fmt.limbBits L fmt.precision a.G.E ℓ ∧
      (∀ e ∈ H.E, m2 (m2 (lsfHdr + 3)) + e * L + L ≤ h3) ∧
      ecH ≤ eCap ∧
      h3 + forest.T.n + 2 < 2 ^ w ∧
      2 * forest.T.n + 2 < 2 ^ w ∧
      h3 + ordGradScanSpace forest H vcF eCap L < 2 ^ w ∧
      (let base := h3 + forest.T.n
       let flags := base + vcF * L + L
       let queue := flags + vcF
       ∀ parent ∈ forest.T.V, ∀ e ∈ forest.T.E, ∀ direction : Bool, ∀ s seen r,
         ForestWorklistAt s forest.T g base flags queue vcF fmt.limbBits L fmt.precision r seen →
         EdgeValuesAt s.mem gradBase fmt.limbBits L fmt.precision a.G.E g →
         let value := Num.intVal s.mem (gradBase + e * L) fmt.limbBits L
         Num.Fits fmt.limbBits L (Num.intVal s.mem (base + parent * L) fmt.limbBits L +
           ((if direction then value else 0) - (if direction then 0 else value)))) ∧
      (∀ mem,
        ForestPotentialsAt mem (h3 + forest.T.n) fmt.limbBits L fmt.precision forest.T g forest.T.V →
        EdgeValuesAt mem gradBase fmt.limbBits L fmt.precision a.G.E g →
        ∀ e ∈ a.G.E, Num.Fits fmt.limbBits L
          (Num.intVal mem (gradBase + e * L) fmt.limbBits L +
            (Num.intVal mem (h3 + forest.T.n + a.G.head e * L) fmt.limbBits L -
              Num.intVal mem (h3 + forest.T.n + a.G.tail e * L) fmt.limbBits L))))
    (hroom1 : heap + 1 < 2 ^ w) :
    let forest := tool.lsfs a.st branch
    let H := tool.S a.st branch
    ∃ (out : State) (vcH ecH cost : ℕ) (y : R.τ),
      Runs w p ω (ordReadoutsPrefix (op 3) (op 2) copy sort entry) st .normal out cost ∧
      R.rep handle a y out.mem ∧
      DynGraphAt out.mem (out.regs 6) vcH ecH H ∧
      EdgeValuesAt out.mem (out.regs 7) fmt.limbBits L fmt.precision H.E (coreLen forest ℓ) ∧
      EdgeValuesAt out.mem (out.regs 8) fmt.limbBits L fmt.precision H.E (coreGrad a.G forest g) ∧
      out.regs 64 = ecH ∧ out.regs 65 = branch ∧ out.regs 66 = handle ∧ out.regs 67 = L ∧
      heap ≤ out.regs 6 ∧ out.regs 6 + dynGraphSize vcH ecH ≤ out.regs 4 ∧
      (∀ addr, out.regs 6 ≤ addr → addr < out.regs 6 + dynGraphSize vcH ecH →
        ¬ R.foot handle y addr) ∧
      heap ≤ out.regs 8 ∧ out.regs 8 + ecH * L ≤ out.regs 4 ∧
      (∀ addr, out.regs 8 ≤ addr → addr < out.regs 8 + ecH * L → ¬ R.foot handle y addr) ∧
      (∀ addr, R.foot handle y addr → addr < out.regs 4) ∧
      (∀ addr, R.foot handle y addr → R.foot handle x addr ∨ (heap ≤ addr ∧ addr < out.regs 4)) ∧
      heap ≤ out.regs 4 ∧ ZeroFrom out.mem (out.regs 4) ∧
      (∀ addr < heap, ¬ R.foot handle x addr → out.mem addr = st.mem addr) ∧
      (∀ r, (51 ≤ r ∧ r ≤ 62) ∨ r = 67 ∨ r = 68 ∨ 70 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi handle y out.mem ≤
        2 * P.readout + 17 * dynGraphSize vcH ecH + ordGradScanCost forest H L +
          R.phi handle x st.mem + 190 := by
  dsimp only
  let forest := tool.lsfs a.st branch
  let H := tool.S a.st branch
  -- Save branch, handle, currentGraph in regs 65, 66, 69
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
  -- Op 3 (read sparsifier graph)
  obtain ⟨s4, h1, c4, y1, r4, hs4_5, hrep1, ⟨vcH, ecH, hH1⟩, hresp1, hc4, hs4_regs⟩ :=
    ordCoreReadGraph_runs (ω := ω) (st := s3) himpl
      ((hs3_r 2 (by decide) (by decide) (by decide)).trans hb)
      ((hs3_r 3 (by decide) (by decide) (by decide)).trans hh)
      ((hs3_r 4 (by decide) (by decide) (by decide)).trans hp)
      hj hwk hhw hrep hIn hfoot hz hroom1
  obtain ⟨s5, r5, hs5_6, hH5, hs5_mem, _, hs5_regs⟩ :=
    loadShiftGraph_runs (ω := ω) (st := s4)
      ((hs4_regs 4 (by decide)).trans ((hs3_r 4 (by decide) (by decide) (by decide)).trans hp)) hH1
  have hfoot1 : ∀ addr, R.foot handle y1 addr → addr < h1 := fun addr ha => by
    rcases hresp1.2.2.2.2 addr ha with ho | ⟨_, hn⟩
    · exact (hfoot addr ho).trans_le hresp1.1
    · exact hn
  obtain ⟨hRawEnd, hCopyFit⟩ := hCopyRoom s4.mem h1 (s4.mem heap) vcH ecH hH1 hresp1.1 hresp1.2.1
  -- Copy graph to caller-owned memory at h1
  obtain ⟨s6, c6, r6, hH6, hs6_6, hs6_5, hz6, hrep6, hphi6, hfootDisj6, hmem6, _, hc6, hs6_regs⟩ :=
    copyShiftGraph_preserves_tool_runs (ω := ω) (st := s5) himpl.1 (hs5_mem.symm ▸ hrep1) hfoot1
      hs5_6 ((hs5_regs 5 (by decide)).trans hs4_5) (hs5_6 ▸ hH5) hRawEnd (by omega) hw9
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
  -- Helper: s6.mem agrees with st.mem on addresses < heap outside R.foot x
  have hs6_frame (addr : ℕ) (hlt : addr < heap) (hnf : ¬ R.foot handle x addr) :
      s6.mem addr = st.mem addr :=
    (hmem6 addr (hlt.trans_le hresp1.1)).trans ((congrFun hs5_mem addr).trans
      (hresp1.2.2.2.1 addr hlt hnf))
  have hG10 : DynGraphAt s10.mem graphBase vCap eCap a.G :=
    dynGraphAt_of_agree hG (fun addr hlo hhi =>
      hs6_frame addr (by omega) (hFootG addr hlo hhi))
  have hfoot1_h2 : ∀ addr, R.foot handle y1 addr → addr < h2 := fun addr ha =>
    (hfoot1 addr ha).trans_le (Nat.le_add_right h1 _)
  have hs6_keep (r : ℕ) (h4 : r ≠ 4) (h5 : r ≠ 5) (h6 : r ≠ 6) (h10 : r ≠ 10)
      (h11 : r ≠ 11) (h12 : r ≠ 12) (h63 : r ≠ 63) (h64 : r ≠ 64)
      (h65 : r ≠ 65) (h66 : r ≠ 66) (h69 : r ≠ 69) : s10.regs r = st.regs r := by
    simp only [s10, s9, s8, s7, Function.update_of_ne h6, Function.update_of_ne h63,
      Function.update_of_ne h4, Function.update_of_ne h64]
    exact (hs6_regs r h5 h6 h10 h11 h12).trans ((hs5_regs r h6).trans
      ((hs4_regs r h5).trans (hs3_r r h65 h66 h69)))
  -- Op 2 (read LSF) at h2
  obtain ⟨s11, h3, c11, y2, r11, hs11_5, hrep2, ⟨vcF, ecF, hLSF11⟩, hresp2, hc11, hs11_regs⟩ :=
    ordCoreReadLSF_runs (ω := ω) (st := s10) himpl
      ((hs6_keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb)
      ((hs6_keep 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh)
      (by simp [s10]) (by simp [s10, s9, s8, Function.update_of_ne, h2])
      hj hwk hhw hG10 (hgEnd.trans (hresp1.1.trans (Nat.le_add_right h1 _)))
      hrep6 hIn hfoot1_h2 (by simpa [s10, s9, s8, s7, hs6_5, h2] using hz6) (by omega)
  let s12 := { s11 with regs := Function.update s11.regs 9 h2 }
  let s13 := { s12 with regs := Function.update s12.regs 6 h1 }
  have r12 : Runs w p ω (.assign 9 (.reg 4)) s11 .normal s12 2 :=
    runs_assign_iff.mpr ⟨h2, by
      simp [Expr.eval, hs11_regs 4 (by decide), s10, s9, s8, Function.update_of_ne], rfl, rfl, rfl⟩
  have r13 : Runs w p ω (.assign 6 (.reg 63)) s12 .normal s13 2 :=
    runs_assign_iff.mpr ⟨h1, by
      simp [Expr.eval, s12, Function.update_of_ne, hs11_regs 63 (by decide), s10, s9, Function.update_of_ne],
      rfl, rfl, rfl⟩
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
  -- Unpack readout/scan fit hypotheses
  obtain ⟨hlsf3W, hFGraphEnd, hFListEnd, hLenDenom, hLenH, hecHLe, hSortR, hCntW, hScanRoom,
    hFitW, hFitS⟩ := hScanFits s11.mem vcH ecH vcF ecF h2 h3 hLSF11
      (hresp1.1.trans (Nat.le_add_right h1 _)) hresp2.1 hresp2.2.1
  -- Load next lengths
  obtain ⟨s14, r14, hs14_7, hs14_mem, _, hs14_regs⟩ :=
    loadForestNumerator_runs (ω := ω) (st := s13) (by simp [s13, s12, Function.update_of_ne]) hlsf3W
  have hLen14 : EdgeValuesAt s14.mem (s14.regs 7) fmt.limbBits L fmt.precision H.E
      (coreLen forest ℓ) := by
    rw [hs14_mem, hs14_7]
    exact coreLengthAt_of_stretch_numerator hHE hLSF11.2.2.2 hLenDenom
  obtain ⟨s15, r15, hs15_13, hs15_regs, hs15_mem⟩ :=
    passRebuildGradient_runs (ω := ω) (st := s14)
  have hH15 : DynGraphAt s15.mem h1 vcH ecH H := by
    rw [hs15_mem, hs14_mem]
    exact dynGraphAt_of_agree (hs6_6 ▸ hH6) (fun addr hlo hhi =>
      h11_frame_h2 addr (by dsimp [h2]; omega) (hfootDisj6 addr hlo))
  have hG15 : DynGraphAt s15.mem graphBase vCap eCap a.G := by
    rw [hs15_mem, hs14_mem]
    exact dynGraphAt_of_agree hG (fun addr hlo hhi => h11_frame_heap addr (by omega) (hFootG addr hlo hhi))
  have hGrad15 : EdgeValuesAt s15.mem gradBase fmt.limbBits L fmt.precision a.G.E g := by
    rw [hs15_mem, hs14_mem]
    exact hgradVal.congr (fun e he j hj => by
      have heLt : e < eCap := hG.2.2.1 e he
      have hmul : e * L + L ≤ eCap * L := by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
      exact h11_frame_heap _ (by omega) (hFootGrad _ (by omega) (by omega)))
  have hs15_keep (r : ℕ) (h4 : r ≠ 4) (h5 : r ≠ 5) (h6 : r ≠ 6) (h7 : r ≠ 7) (h9 : r ≠ 9)
      (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) (h13 : r ≠ 13) (h63 : r ≠ 63) (h64 : r ≠ 64)
      (h65 : r ≠ 65) (h66 : r ≠ 66) (h69 : r ≠ 69) : s15.regs r = st.regs r :=
    (hs15_regs r h13).trans ((hs14_regs r h7).trans (by
      simp only [s13, s12, Function.update_of_ne h6, Function.update_of_ne h9]
      exact (hs11_regs r h5).trans (hs6_keep r h4 h5 h6 h10 h11 h12 h63 h64 h65 h66 h69)))
  have hs15_5 : s15.regs 5 = h3 :=
    (hs15_regs 5 (by decide)).trans ((hs14_regs 5 (by decide)).trans
      (by simp [s13, s12, Function.update_of_ne, hs11_5]))
  have hs15_6 : s15.regs 6 = h1 :=
    (hs15_regs 6 (by decide)).trans ((hs14_regs 6 (by decide)).trans (by simp [s13]))
  have hs15_9 : s15.regs 9 = h2 :=
    (hs15_regs 9 (by decide)).trans ((hs14_regs 9 (by decide)).trans (by simp [s13, s12, Function.update_of_ne]))
  have hs15_13_eq : s15.regs 13 = gradBase :=
    hs15_13.trans ((hs14_regs 8 (by decide)).trans (by
      simp only [s13, s12, Function.update_of_ne (by decide : 8 ≠ 6), Function.update_of_ne (by decide : 8 ≠ 9)]
      exact (hs11_regs 8 (by decide)).trans ((hs6_keep 8 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hgr)))
  -- Gradient scan
  obtain ⟨out, cScan, rScan, ho6, ho7, ho8Lo, ho8Hi, hHout, hLenOut, hGradOut, hzOut,
    h4Lo, _, hmemScan, hcScan⟩ :=
    prepareShiftReadoutGradients_runs (ω := ω) (st := s15) hcopy hsort
      (by simpa [hs15_9, hs15_mem, hs14_mem] using hLSF11)
      (by simp [hs15_9, hs15_mem, hs14_mem, s13, s12])
      hs15_5 ((hs15_keep 67 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h67)
      (by simpa [hs15_mem, hs14_mem, s13, s12] using hresp2.2.2.1)
      hFGraphEnd hFListEnd hSortR hCntW (by omega) hforest hGrad15 hsub
      (fun e he => by
        have hlt := hG.2.2.1 e he
        have hm := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt)
        rw [Nat.succ_mul] at hm
        have := hresp1.1; have := hresp2.1; omega)
      hcell hG15 (hgEnd.trans (hresp1.1.trans ((Nat.le_add_right h1 _).trans hresp2.1)))
      hverts hH15 hresp2.1 hHE hs15_6 hs15_13_eq
      ((hs15_keep 50 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h50)
      ((hs15_keep 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h15)
      ((hs15_keep 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16)
      ((hs15_keep 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h17)
      (coreLen forest ℓ)
      (by simpa [hs15_regs 7 (by decide), hs15_mem] using hLen14)
      (fun e he => by rw [hs15_regs 7 (by decide), hs14_7]; exact hLenH e he)
      (by omega) (by unfold ordGradScanSpace at hScanRoom; dsimp [H]; omega) hFitW hFitS
  have hfoot2_h3 : ∀ addr, R.foot handle y2 addr → addr < h3 := fun addr ha => by
    rcases hresp2.2.2.2.2 addr ha with ho | ⟨_, hn⟩
    · exact (hfoot1_h2 addr ho).trans_le hresp2.1
    · exact hn
  have hrepOut := himpl.1 handle a y2 s11.mem out.mem (fun addr ha =>
    ((hmemScan addr (hfoot2_h3 addr ha)).trans (by rw [hs15_mem, hs14_mem])).symm)
  have hScanRegs (r : ℕ) (hr : 51 ≤ r) : out.regs r = s15.regs r :=
    runs_preserves_above (s := prepareShiftReadoutGradients copy sort entry) hr rfl rScan
  have hFull : Runs w p ω (ordReadoutsPrefix (op 3) (op 2) copy sort entry) st .normal out
      (2 + (2 + (2 + (c4 + (3 + (c6 + (5 + (2 + (2 + (2 + (c11 + (2 + (2 + (6 + (2 + cScan + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
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
    runs_seq_iff.mpr (Or.inr ⟨s12, 2, _, r12,
    runs_seq_iff.mpr (Or.inr ⟨s13, 2, _, r13,
    runs_seq_iff.mpr (Or.inr ⟨s14, 6, _, r14,
    runs_seq_iff.mpr (Or.inr ⟨s15, 2, cScan, r15, rScan, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨out, vcH, ecH, _, y2, hFull, hrepOut.1 hrep2, hHout, hLenOut, hGradOut,
    ?_, ?_, ?_, ?_,
    ho6.symm ▸ hresp1.1, by rw [ho6]; have := hresp2.1; omega,
    fun addr hlo hhi hf => by
      rw [ho6] at hlo hhi
      rcases hresp2.2.2.2.2 addr hf with hy1 | ⟨hlo2, _⟩
      · exact hfootDisj6 addr hlo hy1
      · omega,
    (hresp1.1.trans ((Nat.le_add_right h1 _).trans (hresp2.1.trans ho8Lo))),
    (Nat.add_le_add_left (Nat.mul_le_mul_right L hecHLe) _).trans ho8Hi,
    fun addr hlo _ hf => by have := hfoot2_h3 addr hf; omega,
    fun addr hf => (hfoot2_h3 addr hf).trans_le h4Lo,
    fun addr hf => by
      rcases hresp2.2.2.2.2 addr hf with hy1 | ⟨hlo2, hhi2⟩
      · rcases hresp1.2.2.2.2 addr hy1 with hx | ⟨hlo1, hhi1⟩
        · exact Or.inl hx
        · exact Or.inr ⟨hlo1, hhi1.trans_le ((Nat.le_add_right h1 _).trans (hresp2.1.trans h4Lo))⟩
      · exact Or.inr ⟨hresp1.1.trans ((Nat.le_add_right h1 _).trans hlo2), hhi2.trans_le h4Lo⟩,
    hresp1.1.trans ((Nat.le_add_right h1 _).trans (hresp2.1.trans h4Lo)), hzOut,
    fun addr hlt hnf => by
      have hlt3 : addr < h3 := hlt.trans_le (hresp1.1.trans ((Nat.le_add_right h1 _).trans hresp2.1))
      exact ((hmemScan addr hlt3).trans (by rw [hs15_mem, hs14_mem])).trans (h11_frame_heap addr hlt hnf),
    fun r hr => by
      have h51 : 51 ≤ r := by omega
      rw [hScanRegs r h51]
      exact hs15_keep r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    ?_⟩
  · rw [hScanRegs 64 (by decide), hs15_regs 64 (by decide), hs14_regs 64 (by decide)]
    simp [s13, s12, Function.update_of_ne, hs11_regs 64 (by decide), s10, s9, s8, s7]
  · rw [hScanRegs 65 (by decide), hs15_regs 65 (by decide), hs14_regs 65 (by decide)]
    simp [s13, s12, Function.update_of_ne, hs11_regs 65 (by decide), s10, s9, s8, s7,
      hs6_regs 65 (by decide) (by decide) (by decide) (by decide) (by decide),
      hs5_regs 65 (by decide), hs4_regs 65 (by decide), s3, s2, s1]
  · rw [hScanRegs 66 (by decide), hs15_regs 66 (by decide), hs14_regs 66 (by decide)]
    simp [s13, s12, Function.update_of_ne, hs11_regs 66 (by decide), s10, s9, s8, s7,
      hs6_regs 66 (by decide) (by decide) (by decide) (by decide) (by decide),
      hs5_regs 66 (by decide), hs4_regs 66 (by decide), s3, s2]
  · rw [hScanRegs 67 (by decide)]
    exact (hs15_keep 67 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h67
  · have hphi1 : R.phi handle y1 s10.mem = R.phi handle y1 s4.mem := by
      change R.phi handle y1 s6.mem = R.phi handle y1 s4.mem
      rw [hphi6, hs5_mem]
    have hphi0 : R.phi handle x s3.mem = R.phi handle x st.mem := rfl
    rw [hphi1] at hc11
    rw [hphi0] at hc4
    rw [← hrepOut.2]
    dsimp only [ordGradScanCost, H, forest] at hcScan ⊢
    omega

/-- Execute `ordCopyLengthsAndReadOrd` (Steps 3–4): copies `ecH * L` length words into caller
memory and calls op `5` to obtain `OrdListAt` of `tool.rot a.st branch` in `reg 9`. -/
theorem ordCopyLengthsAndReadOrd_runs
    {w L k M N vCap eCap init copy branch handle heap nextGraph nextLen nextGrad vcH ecH : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (nextLenFn nextGradFn : ℕ → ℝ)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h4 : st.regs 4 = heap) (h6 : st.regs 6 = nextGraph)
    (h7 : st.regs 7 = nextLen) (h8 : st.regs 8 = nextGrad)
    (h64 : st.regs 64 = ecH) (h65 : st.regs 65 = branch)
    (h66 : st.regs 66 = handle) (h67 : st.regs 67 = L)
    (hj : branch < k) (hwk : k < 2 ^ w) (hhw : handle < 2 ^ w) (hw4 : 4 < 2 ^ w)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap)
    (hz : ZeroFrom st.mem heap)
    (hH : DynGraphAt st.mem nextGraph vcH ecH (tool.S a.st branch))
    (hHEnd : nextGraph + dynGraphSize vcH ecH ≤ heap)
    (hFootH : ∀ addr, nextGraph ≤ addr → addr < nextGraph + dynGraphSize vcH ecH →
      ¬ R.foot handle x addr)
    (hLen : EdgeValuesAt st.mem nextLen fmt.limbBits L fmt.precision (tool.S a.st branch).E nextLenFn)
    (hLenEnd : nextLen + ecH * L ≤ heap)
    (hGrad : EdgeValuesAt st.mem nextGrad fmt.limbBits L fmt.precision (tool.S a.st branch).E nextGradFn)
    (hGradEnd : nextGrad + ecH * L ≤ heap)
    (hFootGrad : ∀ addr, nextGrad ≤ addr → addr < nextGrad + ecH * L → ¬ R.foot handle x addr)
    (hroom : heap + ecH * L + (1 + ordRotWords a branch) < 2 ^ w) :
    let H := tool.S a.st branch
    ∃ (out : State) (ordWords cost : ℕ) (y : R.τ),
      Runs w p ω (ordCopyLengthsAndReadOrd copy (op 5)) st .normal out cost ∧
      R.rep handle a y out.mem ∧
      out.regs 6 = nextGraph ∧ out.regs 7 = heap ∧ out.regs 8 = nextGrad ∧
      DynGraphAt out.mem nextGraph vcH ecH H ∧
      EdgeValuesAt out.mem heap fmt.limbBits L fmt.precision H.E nextLenFn ∧
      EdgeValuesAt out.mem nextGrad fmt.limbBits L fmt.precision H.E nextGradFn ∧
      OrdListAt out.mem (out.regs 9) (tool.rot a.st branch) ordWords ∧
      ordWords ≤ ordRotWords a branch ∧
      heap + ecH * L ≤ out.regs 4 ∧
      out.regs 4 ≤ heap + ecH * L + (1 + ordRotWords a branch) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ addr < heap, ¬ R.foot handle x addr → out.mem addr = st.mem addr) ∧
      (∀ addr, R.foot handle y addr → R.foot handle x addr ∨ (heap + ecH * L ≤ addr ∧ addr < out.regs 4)) ∧
      (∀ r, (51 ≤ r ∧ r ≤ 62) ∨ r = 67 ∨ r = 68 ∨ 70 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi handle y out.mem ≤
        17 * (ecH * L) + P.mul * (ordRotWords a branch + 1) +
          R.phi handle x st.mem + 50 := by
  dsimp only
  let lenWords := ecH * L
  let s1 := { st with regs := Function.update st.regs 10 lenWords }
  have r1 : Runs w p ω (.assign 10 (.bin .mul (.reg 64) (.reg 67))) st .normal s1 4 :=
    runs_assign_iff.mpr ⟨lenWords, by
      simp [Expr.eval, BinOp.eval, h64, h67, lenWords, show lenWords < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hcpPre : (copyWordsContract w).pre [nextLen, heap, lenWords] s1.mem :=
    ⟨nextLen, heap, lenWords, rfl, by omega, by omega, by omega, Or.inr hLenEnd⟩
  obtain ⟨s2, c2, v2, r2, hcpPost, _, hs2_regs, hc2⟩ :=
    runs_call_of_meetsContract (w := w) (p := p) (r := 11) (f := copy)
      (args := [.reg 7, .reg 4, .reg 10]) hcopy
      (by simp [evalArgs, Expr.eval, s1, Function.update_of_ne, h7, h4])
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl <;> omega)
      hcpPre ω
  obtain ⟨src', dst', len', heqArgs, _, hcpEq, hcpFrame⟩ := hcpPost
  cases heqArgs
  have hs2_lt : ∀ addr < heap, s2.mem addr = st.mem addr := fun addr ha => hcpFrame addr (Or.inl ha)
  have hrep2 := himpl.1 handle a x st.mem s2.mem (fun addr hf => (hs2_lt addr (hfoot addr hf)).symm)
  have hz2 : ZeroFrom s2.mem (heap + lenWords) := fun addr ha =>
    (hcpFrame addr (Or.inr ha)).trans (hz addr (by omega))
  let s3 := { s2 with regs := Function.update s2.regs 7 heap }
  let s4 := { s3 with regs := Function.update s3.regs 4 (heap + lenWords) }
  let s5 := { s4 with regs := Function.update s4.regs 2 branch }
  let s6 := { s5 with regs := Function.update s5.regs 3 handle }
  have r3 : Runs w p ω (.assign 7 (.reg 4)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hs2_regs 4 (by decide), s1, Function.update_of_ne, h4], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.reg 10))) s3 .normal s4 4 :=
    runs_assign_iff.mpr ⟨heap + lenWords, by
      simp [Expr.eval, BinOp.eval, s3, Function.update_of_ne, hs2_regs 4 (by decide),
        hs2_regs 10 (by decide), s1, h4, show heap + lenWords < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 2 (.reg 65)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨branch, by
      simp [Expr.eval, s4, s3, Function.update_of_ne, hs2_regs 65 (by decide), s1, h65], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 3 (.reg 66)) s5 .normal s6 2 :=
    runs_assign_iff.mpr ⟨handle, by
      simp [Expr.eval, s5, s4, s3, Function.update_of_ne, hs2_regs 66 (by decide), s1, h66], rfl, rfl, rfl⟩
  -- Op 5 (read output rotation order) at heap + lenWords
  obtain ⟨s7, h5, ordWords, c7, y, r7, hs7_5, _, hrep7, hord7, hwordsLe, hresp7, hc7, hs7_regs⟩ :=
    ordCoreReadOrd_runs (ω := ω) (st := s6) himpl
      (by simp [s6, s5, Function.update_of_ne]) (by simp [s6])
      (by simp [s6, s5, s4, Function.update_of_ne])
      hj hwk hhw (hrep2.1 hrep) hIn (fun addr hf => (hfoot addr hf).trans_le (Nat.le_add_right heap _))
      hz2 hroom
  let out := { s7 with regs := Function.update s7.regs 4 h5 }
  have r8 : Runs w p ω (.assign 4 (.reg 5)) s7 .normal out 2 :=
    runs_assign_iff.mpr ⟨h5, by simp [Expr.eval, hs7_5], rfl, rfl, rfl⟩
  have hout_frame_lt (addr : ℕ) (hlt : addr < heap) (hnf : ¬ R.foot handle x addr) :
      out.mem addr = st.mem addr :=
    (hresp7.2.2.2.1 addr (hlt.trans_le (Nat.le_add_right heap _)) hnf).trans (hs2_lt addr hlt)
  have hout_H : DynGraphAt out.mem nextGraph vcH ecH (tool.S a.st branch) :=
    dynGraphAt_of_agree hH (fun addr hlo hhi => hout_frame_lt addr (by omega) (hFootH addr hlo hhi))
  have hout_Len : EdgeValuesAt out.mem heap fmt.limbBits L fmt.precision (tool.S a.st branch).E nextLenFn :=
    edgeValuesAt_of_copyWords hH.2.2.1 hLen (fun i hi => by
      have hnf : ¬ R.foot handle x (heap + i) := fun hf => by have := hfoot _ hf; omega
      exact (hresp7.2.2.2.1 (heap + i) (by omega) hnf).trans (hcpEq i hi))
  have hout_Grad : EdgeValuesAt out.mem nextGrad fmt.limbBits L fmt.precision (tool.S a.st branch).E nextGradFn :=
    hGrad.congr (fun e he j hj => by
      have heLt := hH.2.2.1 e he
      have hm : e * L + L ≤ ecH * L := by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
      exact hout_frame_lt _ (by omega) (hFootGrad _ (by omega) (by omega)))
  have rFull : Runs w p ω (ordCopyLengthsAndReadOrd copy (op 5)) st .normal out
      (4 + (c2 + (2 + (4 + (2 + (2 + (c7 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 4, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, c2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 2, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 4, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 2, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 2, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, c7, 2, r7, r8, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hout_keep (r : ℕ) (hr : (51 ≤ r ∧ r ≤ 62) ∨ r = 67 ∨ r = 68 ∨ 70 ≤ r) : out.regs r = st.regs r := by
    simp only [out, Function.update_of_ne (show r ≠ 4 by omega)]
    rw [hs7_regs r (by omega) (by omega)]
    simp only [s6, s5, s4, s3, Function.update_of_ne (show r ≠ 3 by omega),
      Function.update_of_ne (show r ≠ 2 by omega), Function.update_of_ne (show r ≠ 4 by omega),
      Function.update_of_ne (show r ≠ 7 by omega)]
    rw [hs2_regs r (by omega)]
    simp [s1, Function.update_of_ne (show r ≠ 10 by omega)]
  refine ⟨out, ordWords, _, y, rFull, hrep7, ?_, ?_, ?_, hout_H, hout_Len, hout_Grad,
    by simpa [out] using hord7, hwordsLe, by simp [out, hresp7.1, lenWords],
    by simp only [out]; exact hresp7.2.1, by simpa [out] using hresp7.2.2.1,
    hout_frame_lt, by simpa [out, lenWords] using hresp7.2.2.2.2, hout_keep, ?_⟩
  · simp only [out, Function.update_of_ne (by decide : 6 ≠ 4)]
    rw [hs7_regs 6 (by decide) (by decide)]
    simp [s6, s5, s4, s3, Function.update_of_ne, hs2_regs 6 (by decide), s1, h6]
  · simp only [out, Function.update_of_ne (by decide : 7 ≠ 4)]
    rw [hs7_regs 7 (by decide) (by decide)]
    simp [s6, s5, s4, s3, Function.update_of_ne]
  · simp only [out, Function.update_of_ne (by decide : 8 ≠ 4)]
    rw [hs7_regs 8 (by decide) (by decide)]
    simp [s6, s5, s4, s3, Function.update_of_ne, hs2_regs 8 (by decide), s1, h8]
  · rw [← hrep2.2] at hc7
    simp only [copyWordsContract, argsSize, Expr.size] at hc2
    change _ + R.phi handle y s7.mem ≤ _
    omega

/-- Composite execution of `ordReadoutsAndGradTail`: reads graph (op `3`), copies it, reads LSF
(op `2`), scans gradients, copies next lengths, and reads the active branch's output rotation
order `OrdListAt` of `tool.rot a.st branch` (op `5`) into `reg 9`. -/
theorem ordReadoutsAndGradTail_runs
    {w L k M N vCap eCap init copy sort entry branch handle heap graphBase gradBase : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hcell : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w fmt.limbBits x y z))
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle) (hp : st.regs 4 = heap)
    (hg : st.regs 6 = graphBase) (hgr : st.regs 8 = gradBase)
    (h50 : st.regs 50 = eCap)
    (h15 : st.regs 15 = dgETailSlotBase graphBase vCap eCap)
    (h16 : st.regs 16 = dgEHeadSlotBase graphBase vCap eCap)
    (h17 : st.regs 17 = dgIntToExtBase graphBase vCap)
    (h67 : st.regs 67 = L)
    (hj : branch < k) (hwk : k < 2 ^ w) (hhw : handle < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hG : DynGraphAt st.mem graphBase vCap eCap a.G)
    (hgEnd : graphBase + dynGraphSize vCap eCap ≤ heap)
    (hFootG : ∀ addr, graphBase ≤ addr → addr < graphBase + dynGraphSize vCap eCap →
      ¬ R.foot handle x addr)
    (hgradVal : EdgeValuesAt st.mem gradBase fmt.limbBits L fmt.precision a.G.E g)
    (hgradEnd : gradBase + eCap * L ≤ heap)
    (hFootGrad : ∀ addr, gradBase ≤ addr → addr < gradBase + eCap * L → ¬ R.foot handle x addr)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap)
    (hz : ZeroFrom st.mem heap)
    (hforest : (tool.lsfs a.st branch).T.IsForest)
    (hsub : (tool.lsfs a.st branch).T.E ⊆ a.G.E)
    (hverts : a.G.V ⊆ (tool.lsfs a.st branch).T.V)
    (hHE : (tool.S a.st branch).E ⊆ a.G.E)
    (hCopyRoom : ∀ (m1 : ℕ → ℕ) (h1 rawGraph vcH ecH : ℕ),
      DynGraphAt m1 rawGraph vcH ecH (tool.S a.st branch) →
      heap ≤ h1 → h1 ≤ heap + 1 →
      rawGraph + dynGraphSize vcH ecH ≤ h1 ∧ h1 + dynGraphSize vcH ecH + 4 < 2 ^ w)
    (hScanFits : ∀ (m2 : ℕ → ℕ) (_vcH ecH vcF ecF lsfHdr h3 : ℕ),
      let forest := tool.lsfs a.st branch
      let H := tool.S a.st branch
      LSFAt m2 lsfHdr vcF ecF fmt.limbBits L fmt.precision a.G.E forest →
      heap ≤ lsfHdr → lsfHdr ≤ h3 → h3 ≤ lsfHdr + 4 →
      lsfHdr + 3 < 2 ^ w ∧
      m2 lsfHdr + dynGraphSize vcF ecF ≤ h3 ∧
      dgVListBase (m2 lsfHdr) vcF + forest.T.n ≤ h3 ∧
      EdgeValuesAt m2 (m2 (m2 (lsfHdr + 3) + 1)) fmt.limbBits L fmt.precision a.G.E ℓ ∧
      (∀ e ∈ H.E, m2 (m2 (lsfHdr + 3)) + e * L + L ≤ h3) ∧
      ecH ≤ eCap ∧
      h3 + forest.T.n + 2 < 2 ^ w ∧
      2 * forest.T.n + 2 < 2 ^ w ∧
      h3 + ordGradScanSpace forest H vcF eCap L < 2 ^ w ∧
      (let base := h3 + forest.T.n
       let flags := base + vcF * L + L
       let queue := flags + vcF
       ∀ parent ∈ forest.T.V, ∀ e ∈ forest.T.E, ∀ direction : Bool, ∀ s seen r,
         ForestWorklistAt s forest.T g base flags queue vcF fmt.limbBits L fmt.precision r seen →
         EdgeValuesAt s.mem gradBase fmt.limbBits L fmt.precision a.G.E g →
         let value := Num.intVal s.mem (gradBase + e * L) fmt.limbBits L
         Num.Fits fmt.limbBits L (Num.intVal s.mem (base + parent * L) fmt.limbBits L +
           ((if direction then value else 0) - (if direction then 0 else value)))) ∧
      (∀ mem,
        ForestPotentialsAt mem (h3 + forest.T.n) fmt.limbBits L fmt.precision forest.T g forest.T.V →
        EdgeValuesAt mem gradBase fmt.limbBits L fmt.precision a.G.E g →
        ∀ e ∈ a.G.E, Num.Fits fmt.limbBits L
          (Num.intVal mem (gradBase + e * L) fmt.limbBits L +
            (Num.intVal mem (h3 + forest.T.n + a.G.head e * L) fmt.limbBits L -
              Num.intVal mem (h3 + forest.T.n + a.G.tail e * L) fmt.limbBits L))))
    (hLenTailFits : ∀ (mid : State) (ecH : ℕ),
      mid.regs 64 = ecH → heap ≤ mid.regs 4 →
      mid.regs 7 + ecH * L ≤ mid.regs 4 ∧
      mid.regs 4 + ecH * L + (1 + ordRotWords a branch) < 2 ^ w)
    (hroom1 : heap + 1 < 2 ^ w) :
    let forest := tool.lsfs a.st branch
    let H := tool.S a.st branch
    ∃ (out : State) (vcH ecH ordWords cost : ℕ) (y : R.τ),
      Runs w p ω (ordReadoutsAndGradTail (op 3) (op 2) (op 5) copy sort entry) st .normal out cost ∧
      R.rep handle a y out.mem ∧
      DynGraphAt out.mem (out.regs 6) vcH ecH H ∧
      EdgeValuesAt out.mem (out.regs 7) fmt.limbBits L fmt.precision H.E (coreLen forest ℓ) ∧
      EdgeValuesAt out.mem (out.regs 8) fmt.limbBits L fmt.precision H.E (coreGrad a.G forest g) ∧
      OrdListAt out.mem (out.regs 9) (tool.rot a.st branch) ordWords ∧
      ordWords ≤ ordRotWords a branch ∧
      out.regs 6 + dynGraphSize vcH ecH ≤ out.regs 4 ∧
      out.regs 7 + ecH * L ≤ out.regs 4 ∧
      out.regs 8 + ecH * L ≤ out.regs 4 ∧
      heap ≤ out.regs 4 ∧ ZeroFrom out.mem (out.regs 4) ∧
      (∀ addr < heap, ¬ R.foot handle x addr → out.mem addr = st.mem addr) ∧
      (∀ addr, R.foot handle y addr → R.foot handle x addr ∨ (heap ≤ addr ∧ addr < out.regs 4)) ∧
      (∀ r, (51 ≤ r ∧ r ≤ 62) ∨ r = 67 ∨ r = 68 ∨ 70 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi handle y out.mem ≤
        2 * P.readout + P.mul * (ordRotWords a branch + 1) +
          17 * dynGraphSize vcH ecH + 17 * (ecH * L) + ordGradScanCost forest H L +
          R.phi handle x st.mem + 241 := by
  dsimp only
  obtain ⟨mid, vcH, ecH, c1, y1, r1, hrep1, hH1, hLen1, hGrad1, h64, h65, h66, h67',
    _, hHEnd1, hFootH1, _, hGradEnd1, hFootGrad1, hfoot1, hfootIn1, h4Lo1, hz1,
    hframe1, hregs1, hc1⟩ :=
    ordReadoutsPrefix_runs (ω := ω) ℓ g himpl hcopy hsort hcell hb hh hp hg hgr h50
      h15 h16 h17 h67 hj hwk hhw hw9 hG hgEnd hFootG hgradVal hgradEnd hFootGrad
      hrep hIn hfoot hz hforest hsub hverts hHE hCopyRoom hScanFits hroom1
  obtain ⟨hLenEnd1, hRoom2⟩ := hLenTailFits mid ecH h64 h4Lo1
  obtain ⟨out, ordWords, c2, y2, r2, hrep2, ho6, ho7, ho8, hH2, hLen2, hGrad2, hOrd2,
    hOrdLe, h4Lo2, _, hz2, hframe2, hfootIn2, hregs2, hc2⟩ :=
    ordCopyLengthsAndReadOrd_runs (ω := ω) (st := mid) (coreLen (tool.lsfs a.st branch) ℓ)
      (coreGrad a.G (tool.lsfs a.st branch) g) himpl hcopy rfl rfl rfl rfl h64 h65 h66 h67'
      hj hwk hhw (by omega) hrep1 hIn hfoot1 hz1 hH1 hHEnd1 hFootH1 hLen1 hLenEnd1
      hGrad1 hGradEnd1 hFootGrad1 hRoom2
  refine ⟨out, vcH, ecH, ordWords, c1 + c2 + 1, y2,
    runs_seq_iff.mpr (Or.inr ⟨mid, c1, c2, r1, r2, rfl⟩), hrep2,
    ho6.symm ▸ hH2, ho7.symm ▸ hLen2, ho8.symm ▸ hGrad2, hOrd2, hOrdLe,
    ho6.symm ▸ (hHEnd1.trans ((Nat.le_add_right _ _).trans h4Lo2)),
    ho7.symm ▸ h4Lo2, ho8.symm ▸ (hGradEnd1.trans ((Nat.le_add_right _ _).trans h4Lo2)),
    h4Lo1.trans ((Nat.le_add_right _ _).trans h4Lo2), hz2,
    fun addr hlt hnf => by
      have hnf1 : ¬ R.foot handle y1 addr := fun hf => by
        rcases hfootIn1 addr hf with hx | ⟨hlo, _⟩
        · exact hnf hx
        · omega
      exact (hframe2 addr (hlt.trans_le h4Lo1) hnf1).trans (hframe1 addr hlt hnf),
    fun addr hf => by
      rcases hfootIn2 addr hf with hy1 | ⟨hlo, hhi⟩
      · rcases hfootIn1 addr hy1 with hx | ⟨hlo1, hhi1⟩
        · exact Or.inl hx
        · exact Or.inr ⟨hlo1, hhi1.trans_le ((Nat.le_add_right _ _).trans h4Lo2)⟩
      · exact Or.inr ⟨h4Lo1.trans ((Nat.le_add_right _ _).trans hlo), hhi⟩,
    fun r hr => (hregs2 r hr).trans (hregs1 r hr), by omega⟩

end MinCostFlow.MinRatio
