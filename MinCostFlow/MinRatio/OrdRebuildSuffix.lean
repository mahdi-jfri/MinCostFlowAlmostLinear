module

public import MinCostFlow.MinRatio.OrdReadoutTail
public import MinCostFlow.MinRatio.RebuildSuffix
import WordRAM.Tactic

/-!
# Ordered suffix rebuild (`Chain.Ordered.rebuildSuffix`)

Implements the deterministic Word-RAM suffix rebuild for Algorithm 1 with orders
(`MinCostFlow.Chain.Ordered.rebuildSuffix`):
1. `ordRebuildLevelBody`: one sparse-core iteration (`first ≤ i < d`), consuming `(G_i, ℓ_i, g_i, ord_i)`
   in registers `6, 7, 8, 9`, initializing `tool.initOrd` via `ordCoreInitStmt`, storing `(handle, 0)`
   into descriptor cells `(reg 51, reg 52)`, running `ordReadoutsAndGradTail` to produce
   `(G_{i+1}, ℓ_{i+1}, g_{i+1}, ord_{i+1})` in registers `6, 7, 8, 9`, and advancing cursors.
2. `ordRebuildSuffixProgram`: `rebuildSuffixProgram (ordRebuildLevelBody ...) (rebuildTerminalRuntimeStep lastInit)`.
3. `OrdRebuiltCoresAt`: tracks represented `SparseCoreOrdAbs` cores (`chainLevelOrdAbs`) on
   `[first, upto)` with pairwise disjoint footprints below the free heap.
4. `ordRebuildLevelBody_runs` and `ordRebuildSuffixProgram_runs`: execute one level and the full
   suffix, charging the telescoping sum of `P.mul * (tool.cost ...)` plus readout/scan/terminal costs.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

section Programs

/-- One sparse-core level iteration of the ordered Rebuild suffix (`first ≤ i < d`). -/
@[expose] def ordRebuildLevelBody
    (init readGraph readLSF readOrd copy sort entry : ℕ) : Stmt :=
  .assign 53 (.reg 19) ;;
  .assign 54 (.reg 21) ;;
  prepareRebuildGraphArgs ;;
  ordCoreInitStmt init ;;
  storeRebuiltLevel ;;
  ordReadoutsAndGradTail readGraph readLSF readOrd copy sort entry ;;
  .assign 19 (.reg 53) ;;
  .assign 21 (.reg 54) ;;
  rebuildAdvanceDescriptors

theorem ordRebuildLevelBody_noRand (init readGraph readLSF readOrd copy sort entry : ℕ) :
    (ordRebuildLevelBody init readGraph readLSF readOrd copy sort entry).NoRand := by
  simp [ordRebuildLevelBody, prepareRebuildGraphArgs, ordCoreInitStmt_noRand,
    storeRebuiltLevel, ordReadoutsAndGradTail_noRand, rebuildAdvanceDescriptors, Stmt.NoRand]

/-- Complete ordered suffix rebuild program: runs `ordRebuildLevelBody` for `i = first .. d - 1`
and `rebuildTerminalRuntimeStep lastInit` at level `d`. -/
@[expose] def ordRebuildSuffixProgram
    (init readGraph readLSF readOrd copy sort entry lastInit : ℕ) : Stmt :=
  rebuildSuffixProgram
    (ordRebuildLevelBody init readGraph readLSF readOrd copy sort entry)
    (rebuildTerminalRuntimeStep lastInit)

theorem ordRebuildSuffixProgram_noRand
    (init readGraph readLSF readOrd copy sort entry lastInit : ℕ) :
    (ordRebuildSuffixProgram init readGraph readLSF readOrd copy sort entry lastInit).NoRand := by
  apply rebuildSuffixProgram_noRand (ordRebuildLevelBody_noRand _ _ _ _ _ _ _)
  simp [rebuildTerminalRuntimeStep, rebuildLastLevelRuntime, storeRebuiltLevel, Stmt.NoRand]

end Programs

section OrderedCoresRep

/-- Interval of initialized ordered sparse-core levels `[first, upto)` installed in `handleBase`
and `branchBase`, each representing `chainLevelOrdAbs chain j` with pairwise-disjoint footprints
below `heap`. -/
@[expose] def OrdRebuiltCoresAt {T : SparseCoreRestartTool} {P : ChainParams}
    (Rcore : DSRep (SparseCoreOrdAbs T)) (chain : ChainState T P) (mem : ℕ → ℕ)
    (handleBase branchBase first upto heap : ℕ) : Prop :=
  ∃ tok : ℕ → Rcore.τ,
    (∀ j, first ≤ j → j < upto →
      mem (branchBase + j) = chain.bran j ∧
      Rcore.rep (mem (handleBase + j)) (chainLevelOrdAbs chain j) (tok j) mem ∧
      (∀ a, Rcore.foot (mem (handleBase + j)) (tok j) a → a < heap)) ∧
    (∀ j₁ j₂, first ≤ j₁ → j₁ < upto → first ≤ j₂ → j₂ < upto → j₁ ≠ j₂ →
      ∀ a, Rcore.foot (mem (handleBase + j₁)) (tok j₁) a →
        ¬ Rcore.foot (mem (handleBase + j₂)) (tok j₂) a)

theorem OrdRebuiltCoresAt.empty {T : SparseCoreRestartTool} {P : ChainParams}
    (Rcore : DSRep (SparseCoreOrdAbs T)) (chain : ChainState T P) (mem : ℕ → ℕ)
    (handleBase branchBase first heap : ℕ) (tok0 : Rcore.τ) :
    OrdRebuiltCoresAt Rcore chain mem handleBase branchBase first first heap :=
  ⟨fun _ => tok0, fun _ h1 h2 => by omega, fun _ _ h1 h2 => by omega⟩

theorem OrdRebuiltCoresAt.preserve {T : SparseCoreRestartTool} {P : ChainParams}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {chain : ChainState T P} {mem mem' : ℕ → ℕ}
    {handleBase branchBase first upto heap heap' : ℕ}
    (hcores : OrdRebuiltCoresAt Rcore chain mem handleBase branchBase first upto heap)
    (hlocal : Rcore.Local) (hle : heap ≤ heap')
    (hmem : ∀ a < heap, mem' a = mem a)
    (hcells : ∀ j, first ≤ j → j < upto →
      mem' (handleBase + j) = mem (handleBase + j) ∧
      mem' (branchBase + j) = mem (branchBase + j)) :
    OrdRebuiltCoresAt Rcore chain mem' handleBase branchBase first upto heap' := by
  obtain ⟨tok, hrep, hdisj⟩ := hcores
  refine ⟨tok, fun j hj1 hj2 => ?_, fun j₁ j₂ h1 h2 h3 h4 hne a ha => ?_⟩
  · obtain ⟨hbr, hr, hf⟩ := hrep j hj1 hj2
    obtain ⟨hh', hb'⟩ := hcells j hj1 hj2
    have hloc := hlocal (mem (handleBase + j)) (chainLevelOrdAbs chain j) (tok j) mem mem'
      (fun a ha => (hmem a (hf a ha)).symm)
    exact ⟨hb'.trans hbr, hh'.symm ▸ hloc.1 hr, fun a ha => (hf a (hh' ▸ ha)).trans_le hle⟩
  · obtain ⟨hh1, _⟩ := hcells j₁ h1 h2
    obtain ⟨hh2, _⟩ := hcells j₂ h3 h4
    exact fun ha2 => hdisj j₁ j₂ h1 h2 h3 h4 hne a (hh1 ▸ ha) (hh2 ▸ ha2)

theorem OrdRebuiltCoresAt.extend {T : SparseCoreRestartTool} {P : ChainParams}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {chain : ChainState T P} {mem : ℕ → ℕ}
    {handleBase branchBase first upto heap heap' : ℕ} {y : Rcore.τ}
    (hprev : OrdRebuiltCoresAt Rcore chain mem handleBase branchBase first upto heap)
    (hle : heap ≤ heap')
    (hbr : mem (branchBase + upto) = chain.bran upto)
    (hrep : Rcore.rep (mem (handleBase + upto)) (chainLevelOrdAbs chain upto) y mem)
    (hfoot : ∀ a, Rcore.foot (mem (handleBase + upto)) y a → heap ≤ a ∧ a < heap') :
    OrdRebuiltCoresAt Rcore chain mem handleBase branchBase first (upto + 1) heap' := by
  obtain ⟨tok, hreps, hdisj⟩ := hprev
  refine ⟨fun j => if j = upto then y else tok j, ?_, ?_⟩
  · intro j hj1 hj2
    by_cases hjeq : j = upto
    · subst hjeq
      simpa using ⟨hbr, hrep, fun a ha => (hfoot a ha).2⟩
    · have hjlt : j < upto := by omega
      obtain ⟨hb, hr, hf⟩ := hreps j hj1 hjlt
      simp only [hjeq, ↓reduceIte]
      exact ⟨hb, hr, fun a ha => (hf a ha).trans_le hle⟩
  · intro j₁ j₂ h1 h2 h3 h4 hne a ha1 ha2
    by_cases heq1 : j₁ = upto <;> by_cases heq2 : j₂ = upto
    · exact hne (heq1.trans heq2.symm)
    · subst heq1
      simp only [↓reduceIte, heq2] at ha1 ha2
      have hlo := (hfoot a ha1).1
      have hhi := (hreps j₂ h3 (by omega)).2.2 a ha2
      omega
    · subst heq2
      simp only [↓reduceIte, heq1] at ha1 ha2
      have hlo := (hfoot a ha2).1
      have hhi := (hreps j₁ h1 (by omega)).2.2 a ha1
      omega
    · simp only [heq1, heq2, ↓reduceIte] at ha1 ha2
      exact hdisj j₁ j₂ h1 (by omega) h3 (by omega) hne a ha1 ha2

end OrderedCoresRep

section LevelExecution

/-- Execute one iteration of `ordRebuildLevelBody`: initializes an ordered sparse-core level
from `(graph, lengths, grad, ord)` in registers `6, 7, 8, 9`, installs `(heap, 0)` into
`(handleCell, branchCell)`, reads out the branch-0 sparsifier graph, lengths, gradients, and
output rotation order `OrdListAt` of `tool.rot a0.st 0`, and advances the descriptor cursors.
Charges the exact `P.mul * (tool.cost a0.st + ...)` budget of `sparseCoreOrdMachineContract`. -/
theorem ordRebuildLevelBody_runs
    {w L k M N vCap eCap init copy sort entry graphBase lenBase gradBase ordBase ordWords heap
      handleCell branchCell : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ) (ordFn : ℕ → List End)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContract fmt L tool G k M N vCap eCap P allocation))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hcell : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w fmt.limbBits x y z))
    (hg : st.regs 6 = graphBase) (hl : st.regs 7 = lenBase)
    (hgr : st.regs 8 = gradBase) (ho : st.regs 9 = ordBase) (hh : st.regs 4 = heap)
    (h51 : st.regs 51 = handleCell) (h52 : st.regs 52 = branchCell) (h67 : st.regs 67 = L)
    (hk : 0 < k) (hwk : k < 2 ^ w) (hw9 : 9 < 2 ^ w) (hword : (M + N + 2) ^ P.wordExp < 2 ^ w)
    (hne : handleCell ≠ branchCell) (hhBelow : handleCell < heap) (hbBelow : branchCell < heap)
    (hhNextW : handleCell + 1 < 2 ^ w) (hbNextW : branchCell + 1 < 2 ^ w)
    (hG : DynGraphAt st.mem graphBase vCap eCap G) (hm : G.m ≤ M) (hn : G.n ≤ N)
    (hgb : graphBase + dynGraphSize vCap eCap ≤ heap)
    (hDisjG : ∀ addr, graphBase ≤ addr → addr < graphBase + dynGraphSize vCap eCap →
      addr ≠ handleCell ∧ addr ≠ branchCell)
    (hlb : lenBase + eCap * L ≤ heap) (hgrb : gradBase + eCap * L ≤ heap)
    (hDisjGrad : ∀ addr, gradBase ≤ addr → addr < gradBase + eCap * L →
      addr ≠ handleCell ∧ addr ≠ branchCell)
    (hord : OrdListAt st.mem ordBase ordFn ordWords)
    (hordb : ordBase + ordWords ≤ heap)
    (hordW : ∀ j < ordWords, st.mem (ordBase + j) < 2 ^ w)
    (hrot : IsRotationOrder G ordFn)
    (hℓ : EdgeValuesAt st.mem lenBase fmt.limbBits L fmt.precision G.E ℓ)
    (hgv : EdgeValuesAt st.mem gradBase fmt.limbBits L fmt.precision G.E g)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e)
    (hz : ZeroFrom st.mem heap)
    (hroomInit : heap + allocation 6 [graphBase, lenBase, gradBase, ordBase, heap] + 1 < 2 ^ w)
    (hGraphProps :
      let a0 : SparseCoreOrdAbs tool :=
        ⟨tool.initOrd k M N G
          (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
      (tool.lsfs a0.st 0).T.IsForest ∧
      (tool.lsfs a0.st 0).T.E ⊆ G.E ∧
      G.V ⊆ (tool.lsfs a0.st 0).T.V ∧
      (tool.S a0.st 0).E ⊆ G.E)
    -- Readout/scan room after init (for the returned heap `ret0`):
    (hTailFits : ∀ (ret0 : ℕ),
      let a0 : SparseCoreOrdAbs tool :=
        ⟨tool.initOrd k M N G
          (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
      let forest := tool.lsfs a0.st 0
      let H := tool.S a0.st 0
      heap ≤ ret0 → ret0 ≤ heap + allocation 6 [graphBase, lenBase, gradBase, ordBase, heap] →
      (∀ (m1 : ℕ → ℕ) (h1 rawGraph vcH ecH : ℕ),
        DynGraphAt m1 rawGraph vcH ecH H → ret0 ≤ h1 → h1 ≤ ret0 + 1 →
        rawGraph + dynGraphSize vcH ecH ≤ h1 ∧ h1 + dynGraphSize vcH ecH + 4 < 2 ^ w) ∧
      (∀ (m2 : ℕ → ℕ) (_vcH ecH vcF ecF lsfHdr h3 : ℕ),
        LSFAt m2 lsfHdr vcF ecF fmt.limbBits L fmt.precision G.E forest →
        ret0 ≤ lsfHdr → lsfHdr ≤ h3 → h3 ≤ lsfHdr + 4 →
        lsfHdr + 3 < 2 ^ w ∧
        m2 lsfHdr + dynGraphSize vcF ecF ≤ h3 ∧
        dgVListBase (m2 lsfHdr) vcF + forest.T.n ≤ h3 ∧
        EdgeValuesAt m2 (m2 (m2 (lsfHdr + 3) + 1)) fmt.limbBits L fmt.precision G.E ℓ ∧
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
           EdgeValuesAt s.mem gradBase fmt.limbBits L fmt.precision G.E g →
           let value := Num.intVal s.mem (gradBase + e * L) fmt.limbBits L
           Num.Fits fmt.limbBits L (Num.intVal s.mem (base + parent * L) fmt.limbBits L +
             ((if direction then value else 0) - (if direction then 0 else value)))) ∧
        (∀ mem,
          ForestPotentialsAt mem (h3 + forest.T.n) fmt.limbBits L fmt.precision forest.T g forest.T.V →
          EdgeValuesAt mem gradBase fmt.limbBits L fmt.precision G.E g →
          ∀ e ∈ G.E, Num.Fits fmt.limbBits L
            (Num.intVal mem (gradBase + e * L) fmt.limbBits L +
              (Num.intVal mem (h3 + forest.T.n + G.head e * L) fmt.limbBits L -
                Num.intVal mem (h3 + forest.T.n + G.tail e * L) fmt.limbBits L)))) ∧
      (∀ (mid : State) (ecH : ℕ),
        mid.regs 64 = ecH → ret0 ≤ mid.regs 4 →
        mid.regs 7 + ecH * L ≤ mid.regs 4 ∧
        mid.regs 4 + ecH * L + (1 + ordRotWords a0 0) < 2 ^ w)) :
    let a0 : SparseCoreOrdAbs tool :=
      ⟨tool.initOrd k M N G
        (fun e => if e ∈ G.E then ℓ e else 0)
        (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
    let forest := tool.lsfs a0.st 0
    let H := tool.S a0.st 0
    ∃ (out : State) (vcH ecH nextOrdWords cost : ℕ) (y : R.τ),
      Runs w p ω (ordRebuildLevelBody init (op 3) (op 2) (op 5) copy sort entry) st .normal out cost ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧
      out.regs 19 = st.regs 19 ∧ out.regs 21 = st.regs 21 ∧
      out.regs 51 = handleCell + 1 ∧ out.regs 52 = branchCell + 1 ∧
      R.rep heap a0 y out.mem ∧
      DynGraphAt out.mem (out.regs 6) vcH ecH H ∧
      EdgeValuesAt out.mem (out.regs 7) fmt.limbBits L fmt.precision H.E (coreLen forest ℓ) ∧
      EdgeValuesAt out.mem (out.regs 8) fmt.limbBits L fmt.precision H.E (coreGrad G forest g) ∧
      OrdListAt out.mem (out.regs 9) (tool.rot a0.st 0) nextOrdWords ∧
      nextOrdWords ≤ ordRotWords a0 0 ∧
      out.regs 6 + dynGraphSize vcH ecH ≤ out.regs 4 ∧
      out.regs 7 + ecH * L ≤ out.regs 4 ∧
      out.regs 8 + ecH * L ≤ out.regs 4 ∧
      heap ≤ out.regs 4 ∧ ZeroFrom out.mem (out.regs 4) ∧
      (∀ addr < heap, addr ≠ handleCell → addr ≠ branchCell → out.mem addr = st.mem addr) ∧
      (∀ addr, R.foot heap y addr → heap ≤ addr ∧ addr < out.regs 4) ∧
      (∀ r, (55 ≤ r ∧ r ≤ 62) ∨ r = 67 ∨ r = 68 ∨ 70 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi heap y out.mem ≤
        P.mul * (tool.cost a0.st + G.n + G.m + ordWords + ordRotWords a0 0 + 2) +
          2 * P.readout + 17 * dynGraphSize vcH ecH + 17 * (ecH * L) +
          ordGradScanCost forest H L + 330 := by
  dsimp only
  obtain ⟨hforest, hsub, hverts, hHE⟩ := hGraphProps
  -- Save loop registers (19, 21) -> (53, 54) and prepare graph args
  let s1 := { st with regs := Function.update st.regs 53 (st.regs 19) }
  let s2 := { s1 with regs := Function.update s1.regs 54 (st.regs 21) }
  have r1 : Runs w p ω (.assign 53 (.reg 19)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 54 (.reg 21)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s1, Function.update_of_ne], rfl, rfl, rfl⟩
  have hs2_r (r : ℕ) (h53 : r ≠ 53) (h54 : r ≠ 54) : s2.regs r = st.regs r := by
    simp [s2, s1, Function.update_of_ne h53, Function.update_of_ne h54]
  obtain ⟨s3, r3, hs3_50, hs3_17, hs3_15, hs3_16, hs3_regs, hs3_mem⟩ :=
    prepareRebuildGraphArgs_runs (w := w) (p := p) (ω := ω) (st := s2)
      ((hs2_r 6 (by decide) (by decide)).trans hg) hG (by omega) (by omega)
  have hs3_k (r : ℕ) (h15 : r ≠ 15) (h16 : r ≠ 16) (h17 : r ≠ 17) (h18 : r ≠ 18)
      (h50 : r ≠ 50) (h53 : r ≠ 53) (h54 : r ≠ 54) : s3.regs r = st.regs r :=
    (hs3_regs r h18 h50 h17 h15 h16).trans (hs2_r r h53 h54)
  -- Init ordered sparse-core level
  obtain ⟨s4, ret0, c4, y0, r4, hs4_2, hs4_3, hs4_4, hrep0, hIn0, hresp0, hc4⟩ :=
    ordCoreInit_tables_runs (ω := ω) (st := s3) ℓ g ordFn himpl
      ((hs3_k 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hg)
      ((hs3_k 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl)
      ((hs3_k 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hgr)
      ((hs3_k 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ho)
      ((hs3_k 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh)
      hk hword (hs3_mem.symm ▸ hG) hm hn hgb hlb hgrb (hs3_mem.symm ▸ hord) hordb
      (hs3_mem.symm ▸ hordW) hrot (hs3_mem.symm ▸ hℓ) (hs3_mem.symm ▸ hgv) hpos
      (hs3_mem.symm ▸ hz) (by omega)
  have hs4_r (r : ℕ) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) : s4.regs r = s3.regs r :=
    ordCoreInitStmt_preserves_regs r4 h2 h3 h4
  have hfoot0 (addr : ℕ) (hf : R.foot heap y0 addr) : heap ≤ addr ∧ addr < ret0 :=
    (hresp0.2.2.2.2 addr hf).resolve_left id
  -- Store handle and branch 0 into descriptor cells
  obtain ⟨s5, r5, hs5_h, hs5_b, hrep5, hphi5, hs5_frame, hs5_regs, _⟩ :=
    storeRebuiltLevel_preserves_tool_runs (ω := ω) (st := s4) himpl.1
      ((hs4_r 51 (by decide) (by decide) (by decide)).trans
        ((hs3_k 51 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h51))
      ((hs4_r 52 (by decide) (by decide) (by decide)).trans
        ((hs3_k 52 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h52))
      hne (hs4_3.symm ▸ hhBelow) (hs4_3.symm ▸ hbBelow)
      (fun addr hf => hs4_3.symm ▸ (hfoot0 addr (hs4_3 ▸ hf)).1) (hs4_3.symm ▸ hrep0)
  have hs5_lt (addr : ℕ) (hlt : addr < heap) (hh' : addr ≠ handleCell) (hb' : addr ≠ branchCell) :
      s5.mem addr = st.mem addr :=
    (hs5_frame addr hh' hb').trans ((hresp0.2.2.2.1 addr hlt id).trans (congrFun hs3_mem addr))
  have hs5_G : DynGraphAt s5.mem graphBase vCap eCap G :=
    dynGraphAt_of_agree hG (fun addr hlo hhi =>
      hs5_lt addr (by omega) (hDisjG addr hlo hhi).1 (hDisjG addr hlo hhi).2)
  have hs5_grad : EdgeValuesAt s5.mem gradBase fmt.limbBits L fmt.precision G.E g :=
    hgv.congr (fun e he j hj => by
      have heLt := hG.2.2.1 e he
      have hm : e * L + L ≤ eCap * L := by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
      exact hs5_lt _ (by omega) (hDisjGrad _ (by omega) (by omega)).1 (hDisjGrad _ (by omega) (by omega)).2)
  have hs5_hz : ZeroFrom s5.mem ret0 := fun addr ha => by
    have hlo := hresp0.1
    exact (hs5_frame addr (by omega) (by omega)).trans (hresp0.2.2.1 addr ha)
  obtain ⟨hCopyR, hScanF, hLenTailF⟩ := hTailFits ret0 hresp0.1 hresp0.2.1
  -- Run shared readout + gradient + copyLengths + op 5 tail
  obtain ⟨s6, vcH, ecH, nextOrdWords, c6, y6, r6, hrep6, hH6, hLen6, hGrad6, hOrd6,
    hOrdLe6, hHEnd6, hLenEnd6, hGradEnd6, h4Lo6, hz6, hs6_frame, hs6_footIn, hs6_regs, hc6⟩ :=
    ordReadoutsAndGradTail_runs (ω := ω) (st := s5) ℓ g himpl hcopy hsort hcell
      (hs5_regs.symm ▸ hs4_2) (hs5_regs.symm ▸ hs4_3) (hs5_regs.symm ▸ hs4_4)
      ((hs5_regs.symm ▸ hs4_r 6 (by decide) (by decide) (by decide)).trans
        ((hs3_k 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hg))
      ((hs5_regs.symm ▸ hs4_r 8 (by decide) (by decide) (by decide)).trans
        ((hs3_k 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hgr))
      ((hs5_regs.symm ▸ hs4_r 50 (by decide) (by decide) (by decide)).trans hs3_50)
      ((hs5_regs.symm ▸ hs4_r 15 (by decide) (by decide) (by decide)).trans hs3_15)
      ((hs5_regs.symm ▸ hs4_r 16 (by decide) (by decide) (by decide)).trans hs3_16)
      ((hs5_regs.symm ▸ hs4_r 17 (by decide) (by decide) (by decide)).trans hs3_17)
      ((hs5_regs.symm ▸ hs4_r 67 (by decide) (by decide) (by decide)).trans
        ((hs3_k 67 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h67))
      hk hwk (by omega) hw9 hs5_G (hgb.trans hresp0.1)
      (fun addr _ hhi hf => by have := (hfoot0 addr hf).1; omega)
      hs5_grad (hgrb.trans hresp0.1)
      (fun addr _ hhi hf => by have := (hfoot0 addr hf).1; omega)
      (by simpa only [hs5_regs, hs4_3] using hrep5) hIn0
      (fun addr hf => (hfoot0 addr hf).2) hs5_hz hforest hsub hverts hHE
      hCopyR hScanF hLenTailF (by have := hresp0.2.1; omega)
  -- Restore loop registers (19, 21) and advance descriptor cursors (51, 52)
  have hs6_53 : s6.regs 53 = st.regs 19 :=
    (hs6_regs 53 (by omega)).trans ((hs5_regs.symm ▸ hs4_r 53 (by decide) (by decide) (by decide)).trans
      ((hs3_regs 53 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (by simp [s2, s1, Function.update_of_ne])))
  have hs6_54 : s6.regs 54 = st.regs 21 :=
    (hs6_regs 54 (by omega)).trans ((hs5_regs.symm ▸ hs4_r 54 (by decide) (by decide) (by decide)).trans
      ((hs3_regs 54 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [s2])))
  have hs6_51 : s6.regs 51 = handleCell :=
    (hs6_regs 51 (by omega)).trans ((hs5_regs.symm ▸ hs4_r 51 (by decide) (by decide) (by decide)).trans
      ((hs3_k 51 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h51))
  have hs6_52 : s6.regs 52 = branchCell :=
    (hs6_regs 52 (by omega)).trans ((hs5_regs.symm ▸ hs4_r 52 (by decide) (by decide) (by decide)).trans
      ((hs3_k 52 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h52))
  let s7 := { s6 with regs := Function.update s6.regs 19 (st.regs 19) }
  let s8 := { s7 with regs := Function.update s7.regs 21 (st.regs 21) }
  have r7 : Runs w p ω (.assign 19 (.reg 53)) s6 .normal s7 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hs6_53], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 21 (.reg 54)) s7 .normal s8 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s7, Function.update_of_ne, hs6_54], rfl, rfl, rfl⟩
  obtain ⟨out, r9, hout51, hout52, houtRegs, houtMem⟩ :=
    rebuildAdvanceDescriptors_runs (ω := ω) (st := s8)
      (by simp [s8, s7, Function.update_of_ne, hs6_51])
      (by simp [s8, s7, Function.update_of_ne, hs6_52]) hhNextW hbNextW
  have hmemEq : out.mem = s6.mem := houtMem
  have hregKeep (r : ℕ) (h19 : r ≠ 19) (h21 : r ≠ 21) (h51' : r ≠ 51) (h52' : r ≠ 52) :
      out.regs r = s6.regs r := by
    rw [houtRegs r h51' h52']
    simp [s8, s7, Function.update_of_ne h19, Function.update_of_ne h21]
  have rFull : Runs w p ω (ordRebuildLevelBody init (op 3) (op 2) (op 5) copy sort entry) st .normal out
      (2 + (2 + (36 + (c4 + (7 + (c6 + (2 + (2 + 9 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 36, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, c4, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 7, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, c6, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 2, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 2, 9, r8, r9, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have h6Eq := hregKeep 6 (by decide) (by decide) (by decide) (by decide)
  have h7Eq := hregKeep 7 (by decide) (by decide) (by decide) (by decide)
  have h8Eq := hregKeep 8 (by decide) (by decide) (by decide) (by decide)
  have h9Eq := hregKeep 9 (by decide) (by decide) (by decide) (by decide)
  have h4Eq := hregKeep 4 (by decide) (by decide) (by decide) (by decide)
  have hnf0 (addr : ℕ) (hlt : addr < heap) : ¬ R.foot heap y0 addr :=
    fun hf => by have := (hfoot0 addr hf).1; omega
  refine ⟨out, vcH, ecH, nextOrdWords, _, y6, rFull, ?_, ?_,
    (houtRegs 19 (by decide) (by decide)).trans (by simp [s8, s7, Function.update_of_ne]),
    (houtRegs 21 (by decide) (by decide)).trans (by simp [s8]),
    hout51, hout52, hmemEq.symm ▸ hrep6,
    by rw [hmemEq, h6Eq]; exact hH6,
    by rw [hmemEq, h7Eq]; exact hLen6,
    by rw [hmemEq, h8Eq]; exact hGrad6,
    by rw [hmemEq, h9Eq]; exact hOrd6,
    hOrdLe6,
    by rw [h6Eq, h4Eq]; exact hHEnd6,
    by rw [h7Eq, h4Eq]; exact hLenEnd6,
    by rw [h8Eq, h4Eq]; exact hGradEnd6,
    by rw [h4Eq]; exact hresp0.1.trans h4Lo6,
    by rw [hmemEq, h4Eq]; exact hz6,
    fun addr hlt hneH hneB => by
      rw [hmemEq, hs6_frame addr (hlt.trans_le hresp0.1) (hnf0 addr hlt)]
      exact hs5_lt addr hlt hneH hneB,
    fun addr hf => by
      rw [h4Eq]
      rcases hs6_footIn addr hf with hy0 | ⟨hlo, hhi⟩
      · exact ⟨(hfoot0 addr hy0).1, (hfoot0 addr hy0).2.trans_le h4Lo6⟩
      · exact ⟨hresp0.1.trans hlo, hhi⟩,
    fun r hr => by
      rw [hregKeep r (by omega) (by omega) (by omega) (by omega), hs6_regs r (by omega), hs5_regs,
        hs4_r r (by omega) (by omega) (by omega)]
      exact hs3_k r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    ?_⟩
  · rw [hmemEq, hs6_frame handleCell (hhBelow.trans_le hresp0.1) (hnf0 handleCell hhBelow),
      hs5_h, hs5_regs, hs4_3]
  · rw [hmemEq, hs6_frame branchCell (hbBelow.trans_le hresp0.1) (hnf0 branchCell hbBelow), hs5_b]
  · rw [hmemEq]
    rw [hs5_regs, hs4_3] at hphi5
    have hphiEq : R.phi heap y0 s5.mem = R.phi heap y0 s4.mem := hphi5
    rw [hphiEq] at hc6
    have hmulDist :
        P.mul * (tool.cost (tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
            (fun e => if e ∈ G.E then g e else 0) ordFn) + G.n + G.m + ordWords +
            ordRotWords ⟨tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
              (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩ 0 + 2) =
        P.mul * (tool.cost (tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
            (fun e => if e ∈ G.E then g e else 0) ordFn) + G.n + G.m + ordWords + 1) +
        P.mul * (ordRotWords ⟨tool.initOrd k M N G (fun e => if e ∈ G.E then ℓ e else 0)
            (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩ 0 + 1) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [hmulDist]
    dsimp only at hc4 hc6 ⊢
    omega

end LevelExecution

end MinCostFlow.MinRatio
