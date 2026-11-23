module

public import MinCostFlow.SparseCore.Program.BundleInitPost

import WordRAM.Tactic

/-!
# End-to-end verification of `bundleInitSlotsStmt` (`BundleInitMain`)

Chains header loads, Loop 1 (`bundleInitLoop1_triple`), Loop 2 (`bundleInitLoop2_triple`),
temporary array allocation, Loop 3 (`bundleInitLoop3_runs`), Loop 4 (`bundleInitLoop4_triple`),
and `.ret (.reg 10)` into:

1. `bundleInitSlots_runs`: full correctness, `BundleTableRepAt`, `BundleTableCordMatch`,
   `ZeroFrom`, footprint containment, and amortized cost bound `bundleInitSlotsCost`.
2. `bundleInitSlots_eq_initBundleState` and `bundleInitSlots_eq_initBundleFor`: exact agreement
   of every initialized slot with `initBundleState ρ E_s k` and `initBundleFor cs ord E_s k`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.DynSpanner.Program

public section

private lemma bundleInitSlots_hdr_runs {w slotCap eCap tbl tourH k nSlots
    slotSpecPtr nEdges edgeAssignPtr nR rPtr h pos₀ : ℕ}
    {pProg : Program} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (htbl_h' : tbl + (14 + 7 * slotCap + 8 * eCap) ≤ h)
    (hh_w : h < 2 ^ w)
    (hr0 : mem₀ (tbl + btOffSlotCap) = slotCap)
    (hr3 : mem₀ (tbl + btOffSlotPtr) = btSlotPtrBase tbl)
    (hr4 : mem₀ (tbl + btOffEdgeSlot) = btEdgeSlotBase tbl slotCap)
    (hr5 : mem₀ (tbl + btOffEndBundle) = btEndBundleBase tbl slotCap eCap)
    (hr6 : mem₀ (tbl + btOffEndPrev) = btEndPrevBase tbl slotCap eCap)
    (hr7 : mem₀ (tbl + btOffEndNext) = btEndNextBase tbl slotCap eCap)
    (hr8 : mem₀ (tbl + btOffSlotTouched) = btSlotTouchedBase tbl slotCap eCap)
    (hr11 : mem₀ (tbl + btOffSlotCandHead) = btSlotCandHeadBase tbl slotCap eCap)
    (hk_mem : mem₀ (btBunCapAddr tbl slotCap eCap) = k) :
    let args := [tbl, tourH, nSlots, slotSpecPtr, nEdges, edgeAssignPtr, nR, rPtr, h]
    ∃ st_hdr : State,
      st_hdr.mem = mem₀ ∧ st_hdr.pos = pos₀ ∧ st_hdr.regs 10 = h ∧
      BundleInitConstRegs st_hdr tbl tourH k nSlots slotSpecPtr nEdges
        edgeAssignPtr nR rPtr h slotCap eCap ∧
      ∀ {sTail : Stmt} {o : Outcome} {stF : State} {cTail : ℕ},
        Runs w pProg ω sTail st_hdr o stF cTail →
        ∃ c, Runs w pProg ω
          (.assign 9 (.reg 8) ;;
           .assign 8 (.reg 7) ;;
           .assign 7 (.reg 6) ;;
           .assign 6 (.reg 5) ;;
           .assign 5 (.reg 4) ;;
           .assign 4 (.reg 3) ;;
           .assign 3 (.reg 2) ;;
           .assign 35 (.load (.reg 0)) ;;
           .assign 2 (.load (.bin .add (.bin .add (.load (.bin .add (.reg 0) (.const 11)))
             (.bin .mul (.const 4) (.reg 35))) (.const 1))) ;;
           .assign 11 (.load (.bin .add (.reg 0) (.const 3))) ;;
           .assign 12 (.load (.bin .add (.reg 0) (.const 4))) ;;
           .assign 13 (.load (.bin .add (.reg 0) (.const 5))) ;;
           .assign 14 (.load (.bin .add (.reg 0) (.const 6))) ;;
           .assign 15 (.load (.bin .add (.reg 0) (.const 7))) ;;
           .assign 16 (.load (.bin .add (.reg 0) (.const 8))) ;;
           .assign 10 (.reg 9) ;; sTail) (startState args mem₀ pos₀) o stF c ∧ c ≤ 85 + cTail := by
  intro args
  have hhdr_w : ∀ off < 12, tbl + off < 2 ^ w := fun off hoff => by omega
  let st0 : State := startState args mem₀ pos₀
  let rs9 := Function.update st0.regs 9 h
  let rs8 := Function.update rs9 8 rPtr
  let rs7 := Function.update rs8 7 nR
  let rs6 := Function.update rs7 6 edgeAssignPtr
  let rs5 := Function.update rs6 5 nEdges
  let rs4 := Function.update rs5 4 slotSpecPtr
  let rs3 := Function.update rs4 3 nSlots
  let r0 := Function.update rs3 35 slotCap
  let rk := Function.update r0 2 k
  let r1 := Function.update rk 11 (tbl + 12)
  let r2 := Function.update r1 12 (tbl + 12 + slotCap)
  let r3 := Function.update r2 13 (tbl + 12 + slotCap + eCap)
  let r4 := Function.update r3 14 (tbl + 12 + slotCap + 3 * eCap)
  let r5 := Function.update r4 15 (tbl + 12 + slotCap + 5 * eCap)
  let r6 := Function.update r5 16 (tbl + 12 + slotCap + 7 * eCap)
  let st_hdr : State := { mem := mem₀, regs := Function.update r6 10 h, pos := pos₀ }
  have hs9 : Runs w pProg ω (.assign 9 (.reg 8)) st0 .normal { st0 with regs := rs9 } 2 :=
    runs_assign_iff.mpr ⟨h, by simp [Expr.eval, st0, startState, args], rfl, rfl, rfl⟩
  have hs8 : Runs w pProg ω (.assign 8 (.reg 7)) { st0 with regs := rs9 } .normal { st0 with regs := rs8 } 2 :=
    runs_assign_iff.mpr ⟨rPtr, by simp [Expr.eval, rs9, st0, startState, args], rfl, rfl, rfl⟩
  have hs7 : Runs w pProg ω (.assign 7 (.reg 6)) { st0 with regs := rs8 } .normal { st0 with regs := rs7 } 2 :=
    runs_assign_iff.mpr ⟨nR, by simp [Expr.eval, rs8, rs9, st0, startState, args], rfl, rfl, rfl⟩
  have hs6 : Runs w pProg ω (.assign 6 (.reg 5)) { st0 with regs := rs7 } .normal { st0 with regs := rs6 } 2 :=
    runs_assign_iff.mpr ⟨edgeAssignPtr, by simp [Expr.eval, rs7, rs8, rs9, st0, startState, args], rfl, rfl, rfl⟩
  have hs5 : Runs w pProg ω (.assign 5 (.reg 4)) { st0 with regs := rs6 } .normal { st0 with regs := rs5 } 2 :=
    runs_assign_iff.mpr ⟨nEdges, by simp [Expr.eval, rs6, rs7, rs8, rs9, st0, startState, args], rfl, rfl, rfl⟩
  have hs4 : Runs w pProg ω (.assign 4 (.reg 3)) { st0 with regs := rs5 } .normal { st0 with regs := rs4 } 2 :=
    runs_assign_iff.mpr ⟨slotSpecPtr, by simp [Expr.eval, rs5, rs6, rs7, rs8, rs9, st0, startState, args], rfl, rfl, rfl⟩
  have hs3 : Runs w pProg ω (.assign 3 (.reg 2)) { st0 with regs := rs4 } .normal { st0 with regs := rs3 } 2 :=
    runs_assign_iff.mpr ⟨nSlots, by simp [Expr.eval, rs4, rs5, rs6, rs7, rs8, rs9, st0, startState, args], rfl, rfl, rfl⟩
  have ha35 : Runs w pProg ω (.assign 35 (.load (.reg 0))) { st0 with regs := rs3 } .normal { st0 with regs := r0 } 3 :=
    runs_assign_iff.mpr ⟨slotCap, by
      simpa [Expr.eval, rs3, rs4, rs5, rs6, rs7, rs8, rs9, st0, startState, args, btOffSlotCap] using hr0, rfl, rfl, rfl⟩
  have hr0_0 : r0 0 = tbl := by simp [r0, rs3, rs4, rs5, rs6, rs7, rs8, rs9, st0, startState, args]
  have hr0_35 : r0 35 = slotCap := by simp [r0]
  have ha2 : Runs w pProg ω
      (.assign 2 (.load (.bin .add (.bin .add (.load (.bin .add (.reg 0) (.const 11)))
        (.bin .mul (.const 4) (.reg 35))) (.const 1))))
      { st0 with regs := r0 } .normal { st0 with regs := rk } 12 :=
    runs_assign_iff.mpr ⟨k, by
      have h11 : mem₀ (tbl + 11) = btSlotCandHeadBase tbl slotCap eCap := by
        simpa [btOffSlotCandHead] using hr11
      have hka : btSlotCandHeadBase tbl slotCap eCap + 4 * slotCap + 1 = btBunCapAddr tbl slotCap eCap := by
        unfold btSlotCandHeadBase btBunCapAddr; omega
      simp [Expr.eval, BinOp.eval, hr0_0, hr0_35, st0, startState,
        show 11 < 2 ^ w by omega, show 4 < 2 ^ w by omega, show 1 < 2 ^ w by omega,
        hhdr_w 11 (by decide), h11, show 4 * slotCap < 2 ^ w by omega,
        show btSlotCandHeadBase tbl slotCap eCap + 4 * slotCap < 2 ^ w by unfold btSlotCandHeadBase; omega,
        hka, show btBunCapAddr tbl slotCap eCap < 2 ^ w by unfold btBunCapAddr; omega, hk_mem],
      rfl, rfl, by simp [Expr.size]⟩
  have hrk_0 : rk 0 = tbl := by simp [rk, hr0_0]
  have ha11 : Runs w pProg ω (.assign 11 (.load (.bin .add (.reg 0) (.const 3))))
      { st0 with regs := rk } .normal { st0 with regs := r1 } 5 :=
    runs_assign_iff.mpr ⟨tbl + 12, by
      simp [Expr.eval, BinOp.eval, hrk_0, st0, startState, show 3 < 2 ^ w by omega, hhdr_w 3 (by decide)]
      simpa [btOffSlotPtr, btSlotPtrBase] using hr3, rfl, rfl, rfl⟩
  have hr1_0 : r1 0 = tbl := by simp [r1, hrk_0]
  have ha12 : Runs w pProg ω (.assign 12 (.load (.bin .add (.reg 0) (.const 4))))
      { st0 with regs := r1 } .normal { st0 with regs := r2 } 5 :=
    runs_assign_iff.mpr ⟨tbl + 12 + slotCap, by
      simp [Expr.eval, BinOp.eval, hr1_0, st0, startState, show 4 < 2 ^ w by omega, hhdr_w 4 (by decide)]
      simpa [btOffEdgeSlot, btEdgeSlotBase] using hr4, rfl, rfl, rfl⟩
  have hr2_0 : r2 0 = tbl := by simp [r2, hr1_0]
  have ha13 : Runs w pProg ω (.assign 13 (.load (.bin .add (.reg 0) (.const 5))))
      { st0 with regs := r2 } .normal { st0 with regs := r3 } 5 :=
    runs_assign_iff.mpr ⟨tbl + 12 + slotCap + eCap, by
      simp [Expr.eval, BinOp.eval, hr2_0, st0, startState, show 5 < 2 ^ w by omega, hhdr_w 5 (by decide)]
      simpa [btOffEndBundle, btEndBundleBase] using hr5, rfl, rfl, rfl⟩
  have hr3_0 : r3 0 = tbl := by simp [r3, hr2_0]
  have ha14 : Runs w pProg ω (.assign 14 (.load (.bin .add (.reg 0) (.const 6))))
      { st0 with regs := r3 } .normal { st0 with regs := r4 } 5 :=
    runs_assign_iff.mpr ⟨tbl + 12 + slotCap + 3 * eCap, by
      simp [Expr.eval, BinOp.eval, hr3_0, st0, startState, show 6 < 2 ^ w by omega, hhdr_w 6 (by decide)]
      simpa [btOffEndPrev, btEndPrevBase] using hr6, rfl, rfl, rfl⟩
  have hr4_0 : r4 0 = tbl := by simp [r4, hr3_0]
  have ha15 : Runs w pProg ω (.assign 15 (.load (.bin .add (.reg 0) (.const 7))))
      { st0 with regs := r4 } .normal { st0 with regs := r5 } 5 :=
    runs_assign_iff.mpr ⟨tbl + 12 + slotCap + 5 * eCap, by
      simp [Expr.eval, BinOp.eval, hr4_0, st0, startState, show 7 < 2 ^ w by omega, hhdr_w 7 (by decide)]
      simpa [btOffEndNext, btEndNextBase] using hr7, rfl, rfl, rfl⟩
  have hr5_0 : r5 0 = tbl := by simp [r5, hr4_0]
  have ha16 : Runs w pProg ω (.assign 16 (.load (.bin .add (.reg 0) (.const 8))))
      { st0 with regs := r5 } .normal { st0 with regs := r6 } 5 :=
    runs_assign_iff.mpr ⟨tbl + 12 + slotCap + 7 * eCap, by
      simp [Expr.eval, BinOp.eval, hr5_0, st0, startState, show 8 < 2 ^ w by omega, hhdr_w 8 (by decide)]
      simpa [btOffSlotTouched, btSlotTouchedBase] using hr8, rfl, rfl, rfl⟩
  have hr6_9 : r6 9 = h := by simp [r6, r5, r4, r3, r2, r1, rk, r0, rs3, rs4, rs5, rs6, rs7, rs8, rs9]
  have ha10 : Runs w pProg ω (.assign 10 (.reg 9)) { st0 with regs := r6 } .normal st_hdr 2 :=
    runs_assign_iff.mpr ⟨h, by simp [Expr.eval, hr6_9], rfl, rfl, rfl⟩
  refine ⟨st_hdr, rfl, rfl, by simp [st_hdr], ?_, fun {sTail o stF cTail} hTail =>
    ⟨_, bundle_runs_seq_normal hs9 (bundle_runs_seq_normal hs8
      (bundle_runs_seq_normal hs7 (bundle_runs_seq_normal hs6
        (bundle_runs_seq_normal hs5 (bundle_runs_seq_normal hs4
          (bundle_runs_seq_normal hs3 (bundle_runs_seq_normal ha35
            (bundle_runs_seq_normal ha2 (bundle_runs_seq_normal ha11
              (bundle_runs_seq_normal ha12 (bundle_runs_seq_normal ha13
                (bundle_runs_seq_normal ha14 (bundle_runs_seq_normal ha15
                  (bundle_runs_seq_normal ha16 (bundle_runs_seq_normal ha10 hTail))))))))))))))), by omega⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [st_hdr, r6, r5, r4, r3, r2, r1, rk, r0, rs3, rs4, rs5, rs6, rs7, rs8, rs9, st0, startState, args]

/-- Full end-to-end verification of `bundleInitSlotsStmt bDllPush bTourList`. -/
theorem bundleInitSlots_runs {TS : BundleTourSpec} {w slotCap vCap eCap tbl tourH k nSlots
    slotSpecPtr nEdges edgeAssignPtr nR rPtr h : ℕ}
    {pProg : Program} {bDllPush bTourList bTourLen bTourOwner : ℕ}
    {htour : BundleTourAt TS w vCap eCap pProg bTourList bTourLen bTourOwner}
    {S₀ : BundleTableState slotCap} {m₀ : BundleTableMeta slotCap}
    {mem₀ : ℕ → ℕ} {pos₀ : ℕ} {tx₀ : htour.rep.τ} {ω : ℕ → Bool}
    {specs assigns : List (ℕ × ℕ)} {cord : ℕ → List End} {rList : List ℕ}
    (hbPush : ∀ prevBase nextBase headAddr key L,
      MeetsContract w pProg bDllPush
        (bundleDllPushContract w prevBase nextBase headAddr (2 * eCap) key L))
    (hw16 : 16 ≤ 2 ^ w) (hk1 : 1 ≤ k)
    (hk_mem : mem₀ (btBunCapAddr tbl slotCap eCap) = k)
    (htourH_w : tourH < 2 ^ w)
    (htbl_h : tbl + bundleTableFixedSize slotCap eCap ≤ h)
    (hfoot0_lt : ∀ a, bundleTableFoot eCap tbl m₀ a → a < h)
    (hspec_h : slotSpecPtr + 2 * nSlots ≤ h)
    (hspec_disj_tbl : slotSpecPtr + 2 * nSlots ≤ tbl ∨
      tbl + bundleTableFixedSize slotCap eCap ≤ slotSpecPtr)
    (hassign_h : edgeAssignPtr + 2 * nEdges ≤ h)
    (hassign_disj_tbl : edgeAssignPtr + 2 * nEdges ≤ tbl ∨
      tbl + bundleTableFixedSize slotCap eCap ≤ edgeAssignPtr)
    (hrPtr_h : rPtr + nR ≤ h)
    (hrPtr_disj_tbl : rPtr + nR ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ rPtr)
    (hspace_w : h + bundleInitSlotsSpace TS specs cord rList < 2 ^ w)
    (hrep0 : BundleTableRepAt slotCap vCap eCap tbl S₀ m₀ mem₀)
    (hcm0 : BundleTableCordMatch vCap S₀ cord)
    (hzero0 : ZeroFrom mem₀ h)
    (htour_rep : htour.rep.rep tourH cord tx₀ mem₀)
    (htour_foot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h)
    (htour_foot_disj_tbl : ∀ a, htour.rep.foot tourH tx₀ a →
      a < tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ a)
    (htour_foot_disj_blocks : ∀ a, htour.rep.foot tourH tx₀ a →
      ∀ j : Fin slotCap, ∀ p c, m₀.slotBlocks j = some (p, c) →
        a < p ∨ p + bundleSlotBlockSize c ≤ a)
    (htour_foot_disj_spec : ∀ a, htour.rep.foot tourH tx₀ a →
      a < slotSpecPtr ∨ slotSpecPtr + 2 * nSlots ≤ a)
    (htour_foot_disj_r : ∀ a, htour.rep.foot tourH tx₀ a → a < rPtr ∨ rPtr + nR ≤ a)
    (hnSlots : specs.length = nSlots)
    (hspecs_mem : bundleReadPairs mem₀ slotSpecPtr nSlots = specs)
    (hspecs_lt : ∀ sb ∈ specs, sb.1 < slotCap)
    (hspecs_nd : (specs.map Prod.fst).Nodup)
    (hspecs_empty : ∀ sb ∈ specs, ∀ hlt : sb.1 < slotCap, S₀ ⟨sb.1, hlt⟩ = none)
    (hspecs_cap : ∀ sb ∈ specs,
      (initPrefixSlots cord rList (slotEdgesOf assigns sb.1) k).length ≤ sb.2)
    (hnEdges : assigns.length = nEdges)
    (hassigns_mem : bundleReadPairs mem₀ edgeAssignPtr nEdges = assigns)
    (hassigns_in : ∀ es ∈ assigns, es.1 < eCap ∧ es.2 ∈ specs.map Prod.fst)
    (hassigns_nd : (assigns.map Prod.fst).Nodup)
    (hassigns_fresh : ∀ es ∈ assigns, ∀ j : Fin slotCap, ∀ B, S₀ j = some B → es.1 ∉ B.edges)
    (hnEdges_w : nEdges < 2 ^ w)
    (hnR : rList.length = nR)
    (hrList_mem : ListAt mem₀ rPtr rList)
    (hrList_lt : ∀ v ∈ rList, v < vCap ∧ v < 2 ^ w)
    (hrList_nd : rList.Nodup)
    (hcord_nd : ∀ v ∈ rList, (cord v).Nodup)
    (hcord_lt : ∀ v ∈ rList, ∀ x ∈ cord v, x.1 < eCap)
    (hcov : ∀ es ∈ assigns, ∀ side : Bool, ∃ v ∈ rList, (es.1, side) ∈ cord v) :
    let S' := tableAfterInitSlots S₀ specs assigns cord rList k
    let m' := allocSlotBlocksMeta m₀ specs h
    let args := [tbl, tourH, nSlots, slotSpecPtr, nEdges, edgeAssignPtr, nR, rPtr, h]
    ∃ st' c hEnd tx',
      Runs w pProg ω (bundleInitSlotsStmt bDllPush bTourList)
        (startState args mem₀ pos₀) (.returned hEnd) st' c ∧
      h + slotBlocksSpace specs ≤ hEnd ∧
      hEnd ≤ h + bundleInitSlotsSpace TS specs cord rList ∧
      ZeroFrom st'.mem hEnd ∧
      BundleTableRepAt slotCap vCap eCap tbl S' m' st'.mem ∧
      st'.mem (btBunCapAddr tbl slotCap eCap) = k ∧
      BundleTableCordMatch vCap S' cord ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      (∀ a, bundleTableFoot eCap tbl m' a →
        bundleTableFoot eCap tbl m₀ a ∨ (h ≤ a ∧ a < h + slotBlocksSpace specs)) ∧
      (∀ a, htour.rep.foot tourH tx' a →
        htour.rep.foot tourH tx₀ a ∨ (h + slotBlocksSpace specs ≤ a ∧ a < hEnd)) ∧
      (∀ a, a < h → ¬ bundleTableFoot eCap tbl m₀ a → ¬ htour.rep.foot tourH tx₀ a →
        st'.mem a = mem₀ a) ∧
      c + htour.rep.phi tourH tx' st'.mem ≤
        bundleInitSlotsCost TS eCap nSlots nEdges cord rList + htour.rep.phi tourH tx₀ mem₀ := by
  intro S' m' args
  have htbl_h' : tbl + (14 + 7 * slotCap + 8 * eCap) ≤ h := htbl_h
  have hh_w : h < 2 ^ w := by unfold bundleInitSlotsSpace at hspace_w; omega
  have hsp_w : h + slotBlocksSpace specs < 2 ^ w := by unfold bundleInitSlotsSpace at hspace_w; omega
  have hrep0_copy := hrep0
  rcases hrep0 with ⟨hr0, _, _, hr3, hr4, hr5, hr6, hr7, hr8, _, _, hr11,
    _, hedgeSlot0, _, _, _, hscrS0, _, hcur0⟩
  -- Phase 0: shift args [2..8] to [3..9], load slotCap & k & header bases + hCur := h
  obtain ⟨st_hdr, hmem_hdr, _, hr10_hdr, hc_hdr_regs, hrun_hdr⟩ :=
    bundleInitSlots_hdr_runs (pProg := pProg) (ω := ω) (tourH := tourH) (nSlots := nSlots)
      (slotSpecPtr := slotSpecPtr) (nEdges := nEdges) (edgeAssignPtr := edgeAssignPtr)
      (nR := nR) (rPtr := rPtr) (pos₀ := pos₀) hw16 htbl_h' hh_w hr0 hr3 hr4 hr5 hr6 hr7 hr8 hr11 hk_mem
  -- Phase 1: Loop 1
  obtain ⟨o1, st1, c1, hrun1, hpost1, hc1⟩ :=
    bundleInitLoop1_triple (w := w) (p := pProg) (mem := mem₀) (specs := specs)
      hw16 htbl_h' hspec_h hspec_disj_tbl hsp_w hnSlots hspecs_mem hspecs_lt hspecs_nd
      st_hdr ω ⟨hmem_hdr, hc_hdr_regs, hr10_hdr⟩
  cases o1 with
  | returned _ => exact False.elim hpost1
  | normal =>
  rcases hpost1 with ⟨hc1_regs, hr10_1, _, hdone1, hfr1⟩
  have htake_all : specs.take nSlots = specs := by rw [← hnSlots, List.take_length]
  rw [htake_all] at hr10_1
  let slotPtrOf : ℕ → ℕ := fun s =>
    match specs.findIdx? (fun sb => sb.1 == s) with
    | some q => h + slotBlocksSpace (specs.take q)
    | none => 0
  have hslotPtrOf_eq : ∀ q (hq : q < specs.length),
      slotPtrOf specs[q].1 = h + slotBlocksSpace (specs.take q) := by
    intro q hq
    have hf : specs.findIdx? (fun sb => sb.1 == specs[q].1) = some q := by
      rw [List.findIdx?_eq_some_iff_getElem]
      refine ⟨hq, by simp, fun j hj => ?_⟩
      simp only [beq_iff_eq]; intro heq
      have := hspecs_nd.getElem_inj_iff.mp
        (show (specs.map Prod.fst)[j]'(by simp; omega) = (specs.map Prod.fst)[q]'(by simp [hq]) by simpa using heq)
      omega
    simp [slotPtrOf, hf]
  have htake_le : ∀ q ≤ specs.length, slotBlocksSpace (specs.take q) ≤ slotBlocksSpace specs := by
    intro q _
    have : slotBlocksSpace specs = slotBlocksSpace (specs.take q) + slotBlocksSpace (specs.drop q) := by
      calc slotBlocksSpace specs = slotBlocksSpace (specs.take q ++ specs.drop q) := by
            rw [List.take_append_drop]
        _ = slotBlocksSpace (specs.take q) + slotBlocksSpace (specs.drop q) := by
            simp only [slotBlocksSpace, List.map_append, List.sum_append]
    omega
  have hblk_end : ∀ q (hq : q < specs.length),
      slotBlocksSpace (specs.take q) + bundleSlotBlockSize specs[q].2 ≤ slotBlocksSpace specs := by
    intro q hq
    have h1 : slotBlocksSpace (specs.take (q + 1)) =
        slotBlocksSpace (specs.take q) + bundleSlotBlockSize specs[q].2 := by
      simp only [slotBlocksSpace]
      rw [List.take_succ_eq_append_getElem hq, List.map_append, List.map_singleton,
        List.sum_append, List.sum_singleton]
    rw [← h1]; exact htake_le (q + 1) (by omega)
  have hblk_disj : ∀ q₁ q₂ (hq₁ : q₁ < specs.length) (hq₂ : q₂ < specs.length), q₁ ≠ q₂ →
      (h + slotBlocksSpace (specs.take q₁)) + bundleSlotBlockSize specs[q₁].2 ≤
        h + slotBlocksSpace (specs.take q₂) ∨
      (h + slotBlocksSpace (specs.take q₂)) + bundleSlotBlockSize specs[q₂].2 ≤
        h + slotBlocksSpace (specs.take q₁) := by
    have hstep : ∀ a b (hab : a < b) (hb : b ≤ specs.length),
        slotBlocksSpace (specs.take a) + bundleSlotBlockSize (specs[a]'(by omega)).2 ≤
          slotBlocksSpace (specs.take b) := by
      intro a b hab hb
      have h1 : slotBlocksSpace (specs.take (a + 1)) =
          slotBlocksSpace (specs.take a) + bundleSlotBlockSize (specs[a]'(by omega)).2 := by
        simp only [slotBlocksSpace]
        rw [List.take_succ_eq_append_getElem (by omega), List.map_append, List.map_singleton,
          List.sum_append, List.sum_singleton]
      rw [← h1]
      have h2 : specs.take (a + 1) = (specs.take b).take (a + 1) := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      have : slotBlocksSpace (specs.take b) =
          slotBlocksSpace ((specs.take b).take (a + 1)) +
          slotBlocksSpace ((specs.take b).drop (a + 1)) := by
        calc slotBlocksSpace (specs.take b) =
              slotBlocksSpace ((specs.take b).take (a + 1) ++ (specs.take b).drop (a + 1)) := by
              rw [List.take_append_drop]
          _ = slotBlocksSpace ((specs.take b).take (a + 1)) +
              slotBlocksSpace ((specs.take b).drop (a + 1)) := by
              simp only [slotBlocksSpace, List.map_append, List.sum_append]
      rw [← h2] at this; omega
    intro q₁ q₂ hq₁ hq₂ hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (by have := hstep q₁ q₂ hlt (by omega); omega)
    · exact Or.inr (by have := hstep q₂ q₁ hgt (by omega); omega)
  have hassigns_mem1 : bundleReadPairs st1.mem edgeAssignPtr nEdges = assigns := by
    rw [← hassigns_mem]; unfold bundleReadPairs; apply List.map_congr_left; intro i hi
    have hi_lt : i < nEdges := List.mem_range.mp hi
    have hne : ∀ a, edgeAssignPtr ≤ a → a < edgeAssignPtr + 2 * nEdges → st1.mem a = mem₀ a :=
      fun a ha1 ha2 => hfr1 a fun q _ hql =>
        ⟨by omega, by have := hspecs_lt _ (List.getElem_mem hql); unfold bundleTableFixedSize at hassign_disj_tbl; omega,
         by have := hspecs_lt _ (List.getElem_mem hql); unfold bundleTableFixedSize at hassign_disj_tbl; omega⟩
    rw [hne _ (by omega) (by omega), hne _ (by omega) (by omega)]
  have hassigns_lt : ∀ es ∈ assigns, es.1 < eCap ∧ es.2 < slotCap := fun es hes => by
    obtain ⟨h1, h2⟩ := hassigns_in es hes
    obtain ⟨sb, hsb, hsbeq⟩ := List.mem_map.mp h2
    exact ⟨h1, hsbeq ▸ hspecs_lt sb hsb⟩
  have hslotPtr_ge : ∀ s < slotCap, (∃ e, (e, s) ∈ assigns) →
      h ≤ slotPtrOf s ∧ slotPtrOf s + 3 < 2 ^ w ∧ st1.mem (tbl + 12 + s) = slotPtrOf s ∧
      st1.mem (slotPtrOf s + 2) = 0 := by
    rintro s _ ⟨e, hes⟩
    obtain ⟨sb, hsb, hsbeq⟩ := List.mem_map.mp (hassigns_in (e, s) hes).2
    obtain ⟨q, hq, hqeq⟩ := List.getElem_of_mem hsb
    have hsq : specs[q].1 = s := by rw [hqeq]; exact hsbeq
    rw [← hsq, hslotPtrOf_eq q hq]
    have hbe := hblk_end q hq
    refine ⟨by omega, by unfold bundleSlotBlockSize at hbe; omega, (hdone1 q (by omega) hq).2.1, ?_⟩
    rw [hfr1 _ fun q' _ hq' => by
      have hne_ptr : h + slotBlocksSpace (specs.take q) + 2 ≠ h + slotBlocksSpace (specs.take q') := by
        by_cases hqq : q' = q
        · subst hqq; omega
        · have := hblk_disj q q' hq hq' (Ne.symm hqq); unfold bundleSlotBlockSize at this; omega
      have := hspecs_lt _ (List.getElem_mem hq')
      exact ⟨hne_ptr, by omega, by omega⟩]
    exact hzero0 _ (by omega)
  have hslotPtr_inj : ∀ s₁ s₂, s₁ < slotCap → s₂ < slotCap →
      (∃ e, (e, s₁) ∈ assigns) → (∃ e, (e, s₂) ∈ assigns) →
      s₁ ≠ s₂ → slotPtrOf s₁ + 2 ≠ slotPtrOf s₂ + 2 := by
    rintro s₁ s₂ _ _ ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ hne
    obtain ⟨sb₁, hsb₁, heq₁⟩ := List.mem_map.mp (hassigns_in _ he₁).2
    obtain ⟨sb₂, hsb₂, heq₂⟩ := List.mem_map.mp (hassigns_in _ he₂).2
    obtain ⟨q₁, hq₁, hqeq₁⟩ := List.getElem_of_mem hsb₁
    obtain ⟨q₂, hq₂, hqeq₂⟩ := List.getElem_of_mem hsb₂
    have hsq₁ : specs[q₁].1 = s₁ := by rw [hqeq₁]; exact heq₁
    have hsq₂ : specs[q₂].1 = s₂ := by rw [hqeq₂]; exact heq₂
    have hqq : q₁ ≠ q₂ := fun h => hne (by subst h; rw [← hsq₁, ← hsq₂])
    rw [← hsq₁, ← hsq₂, hslotPtrOf_eq q₁ hq₁, hslotPtrOf_eq q₂ hq₂]
    have := hblk_disj q₁ q₂ hq₁ hq₂ hqq; unfold bundleSlotBlockSize at this; omega
  -- Phase 2: Loop 2
  obtain ⟨o2, st2, c2, hrun2, hpost2, hc2⟩ :=
    bundleInitLoop2_triple (w := w) (p := pProg) (mem := st1.mem) (assigns := assigns)
      (slotPtrOf := slotPtrOf) (hCur := h + slotBlocksSpace specs) hw16 htbl_h' hassign_h
      hassign_disj_tbl hnEdges hassigns_mem1 hassigns_lt hassigns_nd hslotPtr_ge hslotPtr_inj
      hnEdges_w st1 ω ⟨rfl, hc1_regs, hr10_1⟩
  cases o2 with
  | returned _ => exact False.elim hpost2
  | normal =>
  rcases hpost2 with ⟨hc2_regs, hr10_2, _, hed2, hcnt2, hfr2⟩
  -- Phase 2.5: table-resident temp array bases in registers 17 and 18
  set st2a : State := { st2 with regs := Function.update st2.regs 17 (btCurBunBase tbl slotCap eCap) }
  set st2b : State := { st2a with regs := Function.update st2a.regs 18 (btCurTagBase tbl slotCap eCap) }
  have hst2_eq_mem0 : ∀ a,
      (∀ q (hq : q < specs.length), a ≠ h + slotBlocksSpace (specs.take q) ∧
        a ≠ h + slotBlocksSpace (specs.take q) + 2 ∧
        a ≠ tbl + 12 + specs[q].1 ∧ a ≠ tbl + 12 + slotCap + 7 * eCap + specs[q].1) →
      (∀ q (hq : q < assigns.length), a ≠ tbl + 12 + slotCap + assigns[q].1) →
      st2.mem a = mem₀ a := fun a ha1 ha2 => by
    rw [hfr2 a (fun q _ hql => ha2 q hql) (fun s _ ⟨e, hes⟩ => by
      obtain ⟨sb, hsb, hsbeq⟩ := List.mem_map.mp (hassigns_in _ hes).2
      obtain ⟨q, hq, hqeq⟩ := List.getElem_of_mem hsb
      have hsq : specs[q].1 = s := by rw [hqeq]; exact hsbeq
      rw [← hsq, hslotPtrOf_eq q hq]; exact (ha1 q hq).2.1)]
    exact hfr1 a fun q _ hql => ⟨(ha1 q hql).1, (ha1 q hql).2.2.1, (ha1 q hql).2.2.2⟩
  have hhdr11_2 : st2.mem (tbl + btOffSlotCandHead) = btSlotCandHeadBase tbl slotCap eCap := by
    rw [hst2_eq_mem0 _ (fun q hq => by
      have := hspecs_lt _ (List.getElem_mem hq); unfold btOffSlotCandHead
      exact ⟨by omega, by omega, by omega, by omega⟩)
      (fun q hq => by unfold btOffSlotCandHead; omega)]
    exact hr11
  have ha17 : Runs w pProg ω
      (.assign 17 (.bin .add (.load (.bin .add (.reg 0) (.const btOffSlotCandHead))) (.reg 35)))
      st2 .normal st2a 7 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, hc2_regs.1, hc2_regs.2.2.2.2.2.2.2.2.2.2.1,
        show btOffSlotCandHead < 2 ^ w by unfold btOffSlotCandHead; omega,
        show tbl + btOffSlotCandHead < 2 ^ w by unfold btOffSlotCandHead; omega,
        hhdr11_2, show btSlotCandHeadBase tbl slotCap eCap + slotCap = btCurBunBase tbl slotCap eCap by
          unfold btSlotCandHeadBase btCurBunBase; omega,
        show btCurBunBase tbl slotCap eCap < 2 ^ w by unfold btCurBunBase; omega], rfl, rfl, rfl⟩
  have ha18 : Runs w pProg ω (.assign 18 (.bin .add (.reg 17) (.reg 35))) st2a .normal st2b 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, st2a, hc2_regs.2.2.2.2.2.2.2.2.2.2.1,
        show btCurBunBase tbl slotCap eCap + slotCap = btCurTagBase tbl slotCap eCap by
          unfold btCurBunBase btCurTagBase; omega,
        show btCurTagBase tbl slotCap eCap < 2 ^ w by unfold btCurTagBase; omega], rfl, rfl, rfl⟩
  have hst2_out_tbl : ∀ a, a < h → (a < tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ a) →
      st2.mem a = mem₀ a := fun a ha hdisj =>
    hst2_eq_mem0 a (fun q hq => by
      have := hspecs_lt _ (List.getElem_mem hq)
      unfold bundleTableFixedSize at hdisj; exact ⟨by omega, by omega, by omega, by omega⟩)
      (fun q hq => by
        have := (hassigns_in _ (List.getElem_mem hq)).1
        unfold bundleTableFixedSize at hdisj; omega)
  have hrList_mem2 : ListAt st2.mem rPtr rList := fun i hi => by
    rw [hst2_out_tbl (rPtr + i) (by omega) (by omega)]; exact hrList_mem i hi
  have htour_rep2 : htour.rep.rep tourH cord tx₀ st2.mem :=
    (htour.rep_local tourH cord tx₀ mem₀ st2.mem fun a ha =>
      (hst2_out_tbl a (htour_foot_lt a ha) (htour_foot_disj_tbl a ha)).symm).1 htour_rep
  have hphi2 : htour.rep.phi tourH tx₀ st2.mem = htour.rep.phi tourH tx₀ mem₀ :=
    ((htour.rep_local tourH cord tx₀ mem₀ st2.mem fun a ha =>
      (hst2_out_tbl a (htour_foot_lt a ha) (htour_foot_disj_tbl a ha)).symm).2).symm
  have hzero2 : ZeroFrom st2.mem (h + slotBlocksSpace specs) := fun a ha => by
    rw [hst2_eq_mem0 a (fun q hq => by
      have hbe := hblk_end q hq; have hsq := hspecs_lt _ (List.getElem_mem hq)
      unfold bundleSlotBlockSize at hbe
      exact ⟨by clear * - ha hbe; omega, by clear * - ha hbe; omega,
        by clear * - ha hsq htbl_h'; omega, by clear * - ha hsq htbl_h'; omega⟩)
      (fun q hq => by
        have := (hassigns_in _ (List.getElem_mem hq)).1
        clear * - ha this htbl_h'; omega)]
    exact hzero0 a (by omega)
  have hslotPtr2 : ∀ q (hq : q < specs.length),
      st2.mem (btSlotPtrBase tbl + specs[q].1) = h + slotBlocksSpace (specs.take q) := fun q hq => by
    have hsq_lt := hspecs_lt _ (List.getElem_mem hq)
    rw [hfr2 _ (fun j _ hjl => by unfold btSlotPtrBase; omega)
      (fun s _ ⟨e, hes⟩ => by
        have := (hslotPtr_ge s (hassigns_lt _ hes).2 ⟨e, hes⟩).1; unfold btSlotPtrBase; omega)]
    exact (hdone1 q (by omega) hq).2.1
  have htouched_in2 : ∀ s ∈ specs.map Prod.fst, st2.mem (btSlotTouchedBase tbl slotCap eCap + s) = 1 := by
    intro s hs
    obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs
    obtain ⟨q, hq, hqeq⟩ := List.getElem_of_mem hsb
    have hsq_lt := hspecs_lt sb hsb
    rw [hfr2 _ (fun j _ hjl => by
        have := (hassigns_in _ (List.getElem_mem hjl)).1; unfold btSlotTouchedBase; omega)
      (fun s' _ ⟨e, hes⟩ => by
        have := (hslotPtr_ge s' (hassigns_lt _ hes).2 ⟨e, hes⟩).1; unfold btSlotTouchedBase; omega)]
    simpa [btSlotTouchedBase, hqeq] using (hdone1 q (by omega) hq).2.2
  have htouched_out2 : ∀ s < slotCap, s ∉ specs.map Prod.fst →
      st2.mem (btSlotTouchedBase tbl slotCap eCap + s) = 0 := fun s hs hnot => by
    rw [hst2_eq_mem0 _ (fun q hq => by
      have hne : s ≠ specs[q].1 := fun heq => hnot (heq ▸ List.mem_map.mpr ⟨specs[q], List.getElem_mem hq, rfl⟩)
      have := hspecs_lt _ (List.getElem_mem hq); unfold btSlotTouchedBase
      exact ⟨by omega, by omega, by omega, by omega⟩)
      (fun q hq => by have := (hassigns_in _ (List.getElem_mem hq)).1; unfold btSlotTouchedBase; omega)]
    exact (hscrS0 s hs).1
  have hedgeSlot_in2 : ∀ e < eCap, ∀ s ∈ specs.map Prod.fst, e ∈ slotEdgesOf assigns s →
      st2.mem (btEdgeSlotBase tbl slotCap + e) = s + 1 := fun e _ s _ he => by
    simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq] at he
    rcases he with ⟨p, ⟨hp, hps⟩, rfl⟩
    obtain ⟨q, hq, hqeq⟩ := List.getElem_of_mem hp
    simpa [btEdgeSlotBase, hqeq, hps] using hed2 q (by omega) hq
  have hedgeSlot_out2 : ∀ e < eCap, (∀ s ∈ specs.map Prod.fst, e ∉ slotEdgesOf assigns s) →
      st2.mem (btEdgeSlotBase tbl slotCap + e) = 0 ∨
      ∃ s < slotCap, s ∉ specs.map Prod.fst ∧ st2.mem (btEdgeSlotBase tbl slotCap + e) = s + 1 := by
    intro e he hnot
    have hnot_as : ∀ q (hq : q < assigns.length), assigns[q].1 ≠ e := fun q hq heq => by
      have hmem := List.getElem_mem hq
      exact hnot assigns[q].2 (hassigns_in _ hmem).2 (by
        simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
        exact ⟨assigns[q], ⟨hmem, rfl⟩, heq⟩)
    have heq_m0 : st2.mem (btEdgeSlotBase tbl slotCap + e) = mem₀ (btEdgeSlotBase tbl slotCap + e) :=
      hst2_eq_mem0 _ (fun q hq => by
        have := hspecs_lt _ (List.getElem_mem hq); unfold btEdgeSlotBase
        exact ⟨by omega, by omega, by omega, by omega⟩)
        (fun q hq => by unfold btEdgeSlotBase; have := hnot_as q hq; omega)
    rw [heq_m0]
    by_cases hex : ∃ (j : Fin slotCap) (B : BundleState), S₀ j = some B ∧ e ∈ B.edges
    · obtain ⟨j, B, hSj, heB⟩ := hex
      refine Or.inr ⟨j.1, j.2, ?_, (hedgeSlot0 e he).1 j B hSj heB⟩
      intro hin; obtain ⟨sb, hsb, hsbeq⟩ := List.mem_map.mp hin
      have := hspecs_empty sb hsb (hsbeq ▸ j.2)
      rw [show (⟨sb.1, hsbeq ▸ j.2⟩ : Fin slotCap) = j from Fin.ext hsbeq, hSj] at this; cases this
    · push Not at hex; exact Or.inl ((hedgeSlot0 e he).2 hex)
  have hinit0 : ∀ q (hq : q < specs.length),
      InitScanSlotInv eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
        (btEndBundleBase tbl slotCap eCap) (btCurBunBase tbl slotCap eCap)
        (btCurTagBase tbl slotCap eCap) cord rList 0 0 specs[q].1
        (h + slotBlocksSpace (specs.take q)) specs[q].2 k (slotEdgesOf assigns specs[q].1) st2.mem := by
    intro q hq
    set p := h + slotBlocksSpace (specs.take q); set cap := specs[q].2
    have hbe := hblk_end q hq; have hsq_lt := hspecs_lt _ (List.getElem_mem hq)
    have hmid0 : initMidSlots cord (rList.take 0) (rList.getD 0 0) 0 (slotEdgesOf assigns specs[q].1) k = [] := by
      simp [initMidSlots, initPrefixSlots, initialChunks]
    have hzero_p : ∀ off, 0 < off → off ≠ 2 → off < bundleSlotBlockSize cap → st2.mem (p + off) = 0 := by
      intro off hpos hne2 hoff
      rw [hst2_eq_mem0 (p + off) (fun q' hq' => by
        have hne_p0 : p + off ≠ h + slotBlocksSpace (specs.take q') := by
          by_cases hqq : q' = q
          · subst hqq; omega
          · have hdj := hblk_disj q q' hq hq' (Ne.symm hqq)
            unfold bundleSlotBlockSize at hoff hdj; clear * - hpos hoff hdj; omega
        have hne_p2 : p + off ≠ h + slotBlocksSpace (specs.take q') + 2 := by
          by_cases hqq : q' = q
          · subst hqq; omega
          · have hdj := hblk_disj q q' hq hq' (Ne.symm hqq)
            unfold bundleSlotBlockSize at hoff hdj; clear * - hpos hoff hdj; omega
        have hsq' := hspecs_lt _ (List.getElem_mem hq')
        exact ⟨hne_p0, hne_p2, by clear * - hsq' htbl_h'; omega, by clear * - hsq' htbl_h'; omega⟩)
        (fun q' hq' => by have := (hassigns_in _ (List.getElem_mem hq')).1; clear * - this htbl_h'; omega)]
      exact hzero0 _ (by omega)
    refine ⟨by simp [initMidSlots, initPrefixSlots, initialChunks], ?_, ?_, ?_,
      fun b hb => by simp [initMidSlots, initPrefixSlots, initialChunks] at hb, ?_, ?_,
      fun b hb => by simp [initMidSlots, initPrefixSlots, initialChunks] at hb, ?_, fun hne => by simp at hne⟩
    · rw [bsOffBunCap, add_zero]
      rw [hfr2 p (fun j _ hjl => by have := (hassigns_in _ (List.getElem_mem hjl)).1; clear * - this htbl_h'; omega)
        (fun s' _ ⟨e, hes⟩ => by
          obtain ⟨sb', hsb', heq'⟩ := List.mem_map.mp (hassigns_in _ hes).2
          obtain ⟨q', hq', hqeq'⟩ := List.getElem_of_mem hsb'
          have hsq' : specs[q'].1 = s' := by rw [hqeq']; exact heq'
          rw [← hsq', hslotPtrOf_eq q' hq']
          by_cases hqq : q' = q
          · subst hqq; omega
          · have := hblk_disj q q' hq hq' (Ne.symm hqq); unfold bundleSlotBlockSize at this; omega)]
      exact (hdone1 q (by omega) hq).1
    · simp only [initMidSlots, initPrefixSlots, initialChunks, List.take_zero, List.filter_nil,
        List.flatMap_nil, List.nil_append, List.length_nil]
      simpa [bsOffNB] using hzero_p 1 (by omega) (by omega) (by unfold bundleSlotBlockSize; omega)
    · rw [bsOffNE, slotEdgesOf_card_eq hassigns_nd]
      by_cases hex : ∃ e, (e, specs[q].1) ∈ assigns
      · have hcnt := hcnt2 specs[q].1 hsq_lt hex
        dsimp only at hcnt
        rw [← hnEdges, List.take_length] at hcnt
        simpa [hslotPtrOf_eq q hq, p] using hcnt
      · push Not at hex
        have hflt : (assigns.filter fun p => p.2 == specs[q].1) = [] := by
          rw [List.filter_eq_nil_iff]; rintro ⟨e, s'⟩ hmem; simp only [beq_iff_eq]
          intro hs'; subst hs'; exact hex e hmem
        rw [hflt, List.length_nil]
        rw [hfr2 (p + 2) (fun j _ hjl => by have := (hassigns_in _ (List.getElem_mem hjl)).1; clear * - this htbl_h'; omega)
          (fun s' _ ⟨e, hes⟩ => by
            obtain ⟨sb', hsb', heq'⟩ := List.mem_map.mp (hassigns_in _ hes).2
            obtain ⟨q', hq', hqeq'⟩ := List.getElem_of_mem hsb'
            have hsq' : specs[q'].1 = s' := by rw [hqeq']; exact heq'
            have hne_s : s' ≠ specs[q].1 := fun heq => hex e (heq ▸ hes)
            have hqq : q' ≠ q := fun heq => hne_s (by subst heq; rw [← hsq'])
            rw [← hsq', hslotPtrOf_eq q' hq']
            have := hblk_disj q q' hq hq' (Ne.symm hqq); unfold bundleSlotBlockSize at this; omega),
          hfr1 (p + 2) fun q' _ hq' => by
            have hne_p : p + 2 ≠ h + slotBlocksSpace (specs.take q') := by
              by_cases hqq : q' = q
              · subst hqq; omega
              · have := hblk_disj q q' hq hq' (Ne.symm hqq); unfold bundleSlotBlockSize at this; omega
            have hsq' := hspecs_lt _ (List.getElem_mem hq')
            exact ⟨hne_p, by clear * - hsq' htbl_h'; omega, by clear * - hsq' htbl_h'; omega⟩]
        exact hzero0 _ (by omega)
    · intro b _ hb_cap
      refine ⟨?_, ?_, ?_⟩
      · simpa [bsHeadBase, Nat.add_assoc] using hzero_p (3 + b) (by omega) (by omega)
          (by unfold bundleSlotBlockSize; omega)
      · simpa [bsSizeBase, Nat.add_assoc] using hzero_p (3 + cap + b) (by omega) (by omega)
          (by unfold bundleSlotBlockSize; omega)
      · simpa [bsParentBase, Nat.add_assoc] using hzero_p (3 + 2 * cap + b) (by omega) (by omega)
          (by unfold bundleSlotBlockSize; omega)
    · intro b hb_cap
      refine ⟨?_, ?_, ?_⟩
      · simpa [bsSeenBase, Nat.add_assoc] using hzero_p (3 + 3 * cap + b) (by omega) (by omega)
          (by unfold bundleSlotBlockSize; omega)
      · simpa [bsInCandBase, Nat.add_assoc] using hzero_p (3 + 4 * cap + b) (by omega) (by omega)
          (by unfold bundleSlotBlockSize; omega)
      · simpa [bsCandNextBase, Nat.add_assoc] using hzero_p (3 + 5 * cap + b) (by omega) (by omega)
          (by unfold bundleSlotBlockSize; omega)
    · intro _
      have hz := (hcur0 specs[q].1 hsq_lt).2
      rw [hst2_eq_mem0 _ (fun q' hq' => by
        have hbe' := hblk_end q' hq'; have hsq' := hspecs_lt _ (List.getElem_mem hq')
        unfold btCurTagBase
        exact ⟨by clear * - htbl_h' hsq_lt; omega, by clear * - htbl_h' hsq_lt; omega,
          by clear * - hsq' hsq_lt; omega, by clear * - hsq' hsq_lt; omega⟩)
        (fun q' hq' => by have := (hassigns_in _ (List.getElem_mem hq')).1; unfold btCurTagBase; omega)]
      omega
  -- Phase 3: Loop 3
  obtain ⟨st3, c3, hEnd, tx', hrun3, hc3_regs, hr10_3, hr17_3, hr18_3, hh2_le, hEnd_le, hzero3, htrep3,
    htfoot3, hslots3, hfr3, hc3⟩ :=
    bundleInitLoop3_runs (TS := TS) (w := w) (slotCap := slotCap) (vCap := vCap) (eCap := eCap)
      (tbl := tbl) (tourH := tourH) (k := k) (nSlots := nSlots) (slotSpecPtr := slotSpecPtr)
      (nEdges := nEdges) (edgeAssignPtr := edgeAssignPtr) (nR := nR) (rPtr := rPtr) (h := h)
      (pProg := pProg) (bDllPush := bDllPush) (bTourList := bTourList) (bTourLen := bTourLen)
      (bTourOwner := bTourOwner) (htour := htour) (mem₀ := st2.mem) (st₀ := st2b) (tx₀ := tx₀)
      (ω := ω) (specs := specs) (assigns := assigns) (cord := cord) (rList := rList)
      hbPush hw16 hk1 htourH_w htbl_h hrPtr_h hrPtr_disj_tbl hspace_w hnR hrList_mem2
      hrList_lt hrList_nd hspecs_lt hspecs_nd hspecs_cap hcord_nd hcm0.1 hcord_lt hassigns_in
      hassigns_nd htour_rep2 htour_foot_lt htour_foot_disj_tbl htour_foot_disj_r hzero2
      hslotPtr2 htouched_in2 htouched_out2 hedgeSlot_in2 hedgeSlot_out2 hinit0
      ⟨rfl, (hc2_regs.upd (by decide)).upd (by decide),
        by simp [st2b, st2a, hr10_2], by simp [st2b, st2a], by simp [st2b]⟩
  -- Phase 4: Loop 4
  have hspecs_mem3 : bundleReadPairs st3.mem slotSpecPtr nSlots = specs := by
    rw [← hspecs_mem]; unfold bundleReadPairs; apply List.map_congr_left; intro i hi
    have hi_lt : i < nSlots := List.mem_range.mp hi
    have hne3 : ∀ a, slotSpecPtr ≤ a → a < slotSpecPtr + 2 * nSlots → st3.mem a = mem₀ a := by
      intro a ha1 ha2
      rw [hfr3 a (by omega) (fun hf => by have := htour_foot_disj_spec a hf; omega)
        (fun x ⟨_, _, he⟩ => by
          have he_lt : x.1 < eCap := by
            simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq] at he
            rcases he with ⟨p, ⟨hp, _⟩, hpeq⟩; exact hpeq ▸ (hassigns_in p hp).1
          have hkx : endKey x < 2 * eCap := by rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
          unfold bundleTableFixedSize at hspec_disj_tbl
          unfold btEndBundleBase btEndPrevBase btEndNextBase
          exact ⟨by omega, by omega, by omega⟩)
        (fun s hs => by
          obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs; have := hspecs_lt sb hsb
          unfold bundleTableFixedSize at hspec_disj_tbl
          unfold btCurBunBase btCurTagBase; exact ⟨by omega, by omega⟩)]
      exact hst2_out_tbl a (by omega) (by omega)
    rw [hne3 _ (by omega) (by omega), hne3 _ (by omega) (by omega)]
  obtain ⟨o4, st4, c4, hrun4, hpost4, hc4⟩ :=
    bundleInitLoop4_triple (w := w) (p := pProg) (mem := st3.mem) (specs := specs) (hCur := hEnd)
      hw16 htbl_h' hspec_h hspec_disj_tbl hh_w hnSlots hspecs_mem3 hspecs_lt
      st3 ω ⟨rfl, hc3_regs, hr10_3, hr17_3, hr18_3⟩
  cases o4 with
  | returned _ => exact False.elim hpost4
  | normal =>
  rcases hpost4 with ⟨_, _, hr10_4, _, _, _, _, hdone4, hfr4⟩
  have hret : Runs w pProg ω (.ret (.reg 10)) st4 (.returned hEnd) st4 2 :=
    runs_ret_iff.mpr ⟨hEnd, by simp [Expr.eval, hr10_4], rfl, rfl, rfl⟩
  obtain ⟨c_all, hrun_all, hc_all⟩ := hrun_hdr
    (bundle_runs_seq_normal hrun1
      (bundle_runs_seq_normal hrun2
        (bundle_runs_seq_normal ha17
          (bundle_runs_seq_normal ha18
            (bundle_runs_seq_normal hrun3
              (bundle_runs_seq_normal hrun4 hret))))))
  have hagree_tour4 : ∀ a, htour.rep.foot tourH tx' a → st4.mem a = st3.mem a := fun a ha =>
    hfr4 a fun q _ hql => by
      have hs_lt := hspecs_lt _ (List.getElem_mem hql)
      rcases htfoot3 a ha with h0 | ⟨hge, _⟩
      · have := htour_foot_disj_tbl a h0
        unfold bundleTableFixedSize at *
        exact ⟨by omega, by omega, by omega⟩
      · exact ⟨by omega, by omega, by omega⟩
  have hloc4 := htour.rep_local tourH cord tx' st3.mem st4.mem fun a ha => (hagree_tour4 a ha).symm
  obtain ⟨hzero4, hrep4, hcm4, hfoot4, hfr_all⟩ :=
    bundleInitSlots_post hk1 htbl_h hfoot0_lt hh2_le hrep0_copy hcm0 htour_foot_disj_tbl
      htour_foot_disj_blocks hnSlots hnR hspecs_lt hspecs_nd hspecs_empty hassigns_in hassigns_nd
      hassigns_fresh (fun v hv => (hrList_lt v hv).1) hrList_nd hcord_nd hcov hblk_end hblk_disj hst2_eq_mem0 hst2_out_tbl
      hslotPtr2 hedgeSlot_in2 hzero3 hslots3 hfr3 hdone4 hfr4
  have hka4 : st4.mem (btBunCapAddr tbl slotCap eCap) = k := by
    rw [hfr4 _ (fun q _ hql => by
      have hs_lt := hspecs_lt _ (List.getElem_mem hql)
      unfold btBunCapAddr
      exact ⟨by omega, by omega, by omega⟩),
      hfr3 _ (by unfold btBunCapAddr; omega)
        (fun hf => by have := htour_foot_disj_tbl _ hf; unfold btBunCapAddr bundleTableFixedSize at *; omega)
        (fun x ⟨_, _, he⟩ => by
          have he_lt : x.1 < eCap := by
            simp only [slotEdgesOf, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq] at he
            rcases he with ⟨p, ⟨hp, _⟩, hpeq⟩; exact hpeq ▸ (hassigns_in p hp).1
          have hkx : endKey x < 2 * eCap := by rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
          unfold btBunCapAddr btEndBundleBase btEndPrevBase btEndNextBase
          exact ⟨by omega, by omega, by omega⟩)
        (fun s hs => by
          obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hs; have := hspecs_lt sb hsb
          unfold btBunCapAddr btCurBunBase btCurTagBase; exact ⟨by omega, by omega⟩),
      hst2_eq_mem0 _ (fun q hq => by
        have hs_lt := hspecs_lt _ (List.getElem_mem hq); unfold btBunCapAddr
        exact ⟨by omega, by omega, by omega, by omega⟩)
        (fun q hq => by have := (hassigns_in _ (List.getElem_mem hq)).1; unfold btBunCapAddr; omega)]
    exact hk_mem
  refine ⟨st4, c_all, hEnd, tx', hrun_all, hh2_le, hEnd_le, hzero4, hrep4, hka4, hcm4, hloc4.1 htrep3,
    hfoot4, htfoot3, hfr_all, ?_⟩
  dsimp only at hc1 hc2 hc4
  rw [hloc4.2.symm]; rw [hphi2] at hc3; unfold bundleInitSlotsCost; rw [hnR]; omega

/-- Agreement with `initBundleState`: every slot initialized by `bundleInitSlotsStmt` agrees with
`initBundleState ρ (slotEdgesOf assigns s) k` when `rList = C.V.sort (· ≤ ·)` and `cord = ρ.order`. -/
theorem bundleInitSlots_eq_initBundleState {slotCap : ℕ} {C : MGraph} (ρ : Rotation C)
    (hC : C.IsValid) {S₀ : BundleTableState slotCap} {specs assigns : List (ℕ × ℕ)} {k : ℕ}
    (hk : 1 ≤ k) {j : Fin slotCap} (hj : j.1 ∈ specs.map Prod.fst)
    (hE : slotEdgesOf assigns j.1 ⊆ C.E) :
    ∃ B, tableAfterInitSlots S₀ specs assigns ρ.order (C.V.sort (· ≤ ·)) k j = some B ∧
      B.vertices = (initBundleState ρ (slotEdgesOf assigns j.1) k).vertices ∧
      B.edges = (initBundleState ρ (slotEdgesOf assigns j.1) k).edges ∧
      B.parent = (initBundleState ρ (slotEdgesOf assigns j.1) k).parent ∧
      (∀ x, x.1 ∈ slotEdgesOf assigns j.1 →
        B.bundleOf x = (initBundleState ρ (slotEdgesOf assigns j.1) k).bundleOf x) ∧
      GraphEq B.graph (initBundleState ρ (slotEdgesOf assigns j.1) k).graph := by
  set E := slotEdgesOf assigns j.1
  set B := bundleStateOfSlots (initPrefixSlots ρ.order (C.V.sort (· ≤ ·)) E k) E
  refine ⟨B, by simp [tableAfterInitSlots, hj, B, E], ?_⟩
  have hslots_eq : initPrefixSlots ρ.order (C.V.sort (· ≤ ·)) E k = initialSlots ρ E k :=
    initPrefixSlots_eq_initialSlots ρ E k
  have hcord_nd : ∀ v ∈ C.V.sort (· ≤ ·), (ρ.order v).Nodup := fun v _ => ρ.nodup v
  have hcord_disj : ∀ w₁ w₂ x, x ∈ ρ.order w₁ → x ∈ ρ.order w₂ → w₁ = w₂ := fun w₁ w₂ x h1 h2 =>
    ((ρ.mem_order w₁ x).mp h1).2.symm.trans ((ρ.mem_order w₂ x).mp h2).2
  have hcov : ∀ x : End, x.1 ∈ E → ∃ v ∈ C.V.sort (· ≤ ·), x ∈ ρ.order v := by
    intro x hx
    have hxE : x.1 ∈ C.E := hE hx
    have hv : C.src x ∈ C.V := by
      rcases x with ⟨e, side⟩
      cases side with
      | true => exact (hC e hxE).1
      | false => exact (hC e hxE).2
    exact ⟨C.src x, (Finset.mem_sort _).mpr hv, (ρ.mem_order (C.src x) x).mpr ⟨hxE, rfl⟩⟩
  obtain ⟨_, _, hbun, _, _⟩ :=
    bundleStateOfSlots_props hk (Finset.sort_nodup _ _) hcord_nd hcord_disj hcov
  exact bundleState_eq_initBundleState_of_slots ρ hC hE (by omega) B
    (by simp [B, bundleStateOfSlots, hslots_eq]) rfl
    (fun b => by simp [B, bundleStateOfSlots, hslots_eq])
    (fun b hb x hx => hbun b hb x hx)

/-- Agreement with `initBundleFor` (from `MinCostFlow/SparseCore/BundleTreeCore.lean`). -/
theorem bundleInitSlots_eq_initBundleFor {slotCap : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {cs : CompLSFState} (hI : CompLSFInv C_lsst ℓ₀ cs)
    (ord : ℕ → List End) (ρG : Rotation cs.G) (hρ : ρG.order = ord)
    {S₀ : BundleTableState slotCap} {specs assigns : List (ℕ × ℕ)} {k : ℕ}
    (hk : 1 ≤ k) {j : Fin slotCap} (hj : j.1 ∈ specs.map Prod.fst)
    (hE : slotEdgesOf assigns j.1 ⊆ (coreGraph cs.G cs.lsf).E) :
    let ρ := coreRotation (L := cs.lsf) ρG hI.hG_val (compLSF_RF_isRSF hI)
    ∃ B, tableAfterInitSlots S₀ specs assigns ρ.order
        ((coreGraph cs.G cs.lsf).V.sort (· ≤ ·)) k j = some B ∧
      B.vertices = (initBundleFor cs ord (slotEdgesOf assigns j.1) k).vertices ∧
      B.edges = (initBundleFor cs ord (slotEdgesOf assigns j.1) k).edges ∧
      B.parent = (initBundleFor cs ord (slotEdgesOf assigns j.1) k).parent ∧
      (∀ x, x.1 ∈ slotEdgesOf assigns j.1 →
        B.bundleOf x = (initBundleFor cs ord (slotEdgesOf assigns j.1) k).bundleOf x) ∧
      GraphEq B.graph (initBundleFor cs ord (slotEdgesOf assigns j.1) k).graph := by
  intro ρ
  have heq := initBundleFor_eq_initBundleState hI ρG hρ (slotEdgesOf assigns j.1) k
  simpa only [heq] using bundleInitSlots_eq_initBundleState ρ
    (coreGraph_isValid hI.hG_val (compLSF_RF_isRSF hI)) hk hj hE

end

end MinCostFlow.SparseCore.Program
