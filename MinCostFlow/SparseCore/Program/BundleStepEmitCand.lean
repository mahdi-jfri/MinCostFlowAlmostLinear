module

public import MinCostFlow.SparseCore.Program.BundleStepEmitCandBranch2
public import MinCostFlow.SparseCore.Program.BundleStepEmitCSR

/-!
# Phase 3 single-candidate splitting verification (`BundleStepEmitCand`)

Verifies the two-branch `bundleStepEmitOneCandStmt` against `runsFoldStep` in time and space
proportional to the candidate's scanned end count `m_b = (scan_j.filter (·.1 == b)).length`:
* `degB = 0` or `m_b = 0`: `.nop` (`byRootVRuns` has `drop 1 = []`).
* Branch 1 (`winLen < degB - m_b`): keeps the unscanned largest run in `b` untouched and runs
  `bundleStepEmitCand_runsLoop` on the sorted scanned runs `scanVRuns`.
* Branch 2 (`degB - m_b ≤ winLen`, hence `degB ≤ 2 * m_b`): delegates to
  `bundleStepEmitOneCandBranch2_runs`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

set_option maxHeartbeats 600000 in
/-- Full verification of the two-branch `bundleStepEmitOneCandStmt` on candidate `b = candArr[candIdx]`. -/
theorem bundleStepEmitOneCand_runs {TS : BundleTourSpec} {w vCap eCap p bunCap b nB tourH
    candArr candIdx offPtr bufPtr lo batchPtr writeOff updCnt prevBase nextBase endBundleBase hCur : ℕ}
    {pProg : Program} {bDllPush bDllErase bMergeSort bTourList bTourLen bTourOwner : ℕ} {ω : ℕ → Bool}
    {htour : BundleTourAt TS w vCap eCap pProg bTourList bTourLen bTourOwner}
    {cord' : ℕ → List End} {src' : End → ℕ} {G₀ : MGraph} {ops : List Update}
    {B B_init : BundleState} {candSet_j : Finset ℕ} {scan_j : List (ℕ × ℕ × ℕ)} {L_perm : List ℕ}
    {tx₀ : htour.rep.τ} {st₀ : State}
    (hpPush : pProg.HasAt bDllPush [bundleDllPushStmt])
    (hpErase : pProg.HasAt bDllErase [bundleDllEraseStmt])
    (hMergeSort : ∀ L : List ℕ, MeetsContract w pProg bMergeSort (mergeSortContract w L))
    (hw16 : 16 ≤ 2 ^ w) (htourH_w : tourH < 2 ^ w) (heCap_w : 2 * eCap < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (hprev_w : prevBase + 2 * eCap < 2 ^ w) (hnext_w : nextBase + 2 * eCap < 2 ^ w)
    (heb_w : endBundleBase + 2 * eCap < 2 ^ w)
    (hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w)
    (hcand_w : candArr + candIdx < 2 ^ w)
    (hoff_w : offPtr + candIdx + 1 < 2 ^ w)
    (hbuf_w : bufPtr + lo + (scan_j.filter fun t => t.1 == b).length < 2 ^ w)
    (hbuf_le_h : bufPtr + lo + (scan_j.filter fun t => t.1 == b).length ≤ hCur)
    (hbat_w : batchPtr + writeOff + 6 * (scan_j.filter fun t => t.1 == b).length < 2 ^ w)
    (hupd_w : updCnt + (scan_j.filter fun t => t.1 == b).length < 2 ^ w)
    (hh_w : hCur + (8 + 2 * TS.querySpace) * (scan_j.filter fun t => t.1 == b).length < 2 ^ w)
    (hV : B.vertices = Finset.range nB) (hb_lt : b < nB)
    (hnb_cap : nB + (scan_j.filter fun t => t.1 == b).length ≤ bunCap)
    (hB_edges : B.edges = B_init.edges) (hB_ends_b : B.ends b = B_init.ends b)
    (hval : ScanValidForSlot B_init src' candSet_j scan_j)
    (hb_cand : b ∈ candSet_j)
    (hsrc_lt : ∀ x ∈ B.ends b, src' x < vCap)
    (hsrc_mem : ∀ x ∈ B.ends b, x ∈ cord' (src' x))
    (hsrc_uniq : ∀ x ∈ B.ends b, ∀ v', x ∈ cord' v' → v' = src' x)
    (hprev_next : prevBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ prevBase)
    (hblk_prev : p + bundleSlotBlockSize bunCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ p)
    (hblk_next : p + bundleSlotBlockSize bunCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ p)
    (heb_prev : endBundleBase + 2 * eCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ endBundleBase)
    (heb_next : endBundleBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ endBundleBase)
    (heb_blk : endBundleBase + 2 * eCap ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ endBundleBase)
    (hbat_blk : batchPtr + writeOff + 6 * (scan_j.filter fun t => t.1 == b).length ≤ p ∨
      p + bundleSlotBlockSize bunCap ≤ batchPtr)
    (hbat_prev : batchPtr + writeOff + 6 * (scan_j.filter fun t => t.1 == b).length ≤ prevBase ∨
      prevBase + 2 * eCap ≤ batchPtr)
    (hbat_next : batchPtr + writeOff + 6 * (scan_j.filter fun t => t.1 == b).length ≤ nextBase ∨
      nextBase + 2 * eCap ≤ batchPtr)
    (hbat_eb : batchPtr + writeOff + 6 * (scan_j.filter fun t => t.1 == b).length ≤ endBundleBase ∨
      endBundleBase + 2 * eCap ≤ batchPtr)
    (hbat_h : batchPtr + writeOff + 6 * (scan_j.filter fun t => t.1 == b).length ≤ hCur)
    (hh_blk : p + bundleSlotBlockSize bunCap ≤ hCur)
    (hh_prev : prevBase + 2 * eCap ≤ hCur)
    (hh_next : nextBase + 2 * eCap ≤ hCur)
    (hh_eb : endBundleBase + 2 * eCap ≤ hCur)
    (htrep : htour.rep.rep tourH cord' tx₀ st₀.mem)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < hCur)
    (htfoot_disj_blk : ∀ a, htour.rep.foot tourH tx₀ a → a < p ∨ p + bundleSlotBlockSize bunCap ≤ a)
    (htfoot_disj_prev : ∀ a, htour.rep.foot tourH tx₀ a → a < prevBase ∨ prevBase + 2 * eCap ≤ a)
    (htfoot_disj_next : ∀ a, htour.rep.foot tourH tx₀ a → a < nextBase ∨ nextBase + 2 * eCap ≤ a)
    (htfoot_disj_eb : ∀ a, htour.rep.foot tourH tx₀ a → a < endBundleBase ∨ endBundleBase + 2 * eCap ≤ a)
    (htfoot_disj_bat : ∀ a, htour.rep.foot tourH tx₀ a →
      a < batchPtr ∨ batchPtr + writeOff + 6 * (scan_j.filter fun t => t.1 == b).length ≤ a)
    (hzero : ZeroFrom st₀.mem hCur)
    (hrep : BundleSlotRepAt eCap prevBase nextBase p bunCap B st₀.mem)
    (hG₀ : G₀.applyBatch ops = B.graph)
    (hbat : SmallBatchBodyAt st₀.mem (batchPtr + 1) G₀ ops (writeOff - 1)) (hw1 : 1 ≤ writeOff)
    (hm_cand : st₀.mem (candArr + candIdx) = b)
    (hlo_mem : st₀.mem (offPtr + candIdx) = lo)
    (hhi_mem : st₀.mem (offPtr + (candIdx + 1)) = lo + (scan_j.filter fun t => t.1 == b).length)
    (hperm : L_perm.Perm ((scan_j.filter fun t => t.1 == b).map fun t => packEndKey eCap t.2.1 t.2.2))
    (hbuf_at : ListAt st₀.mem (bufPtr + lo) L_perm)
    (hr1 : st₀.regs 1 = tourH) (hr4 : st₀.regs 4 = hCur) (hr6 : st₀.regs 6 = 2 * eCap)
    (hr7 : st₀.regs 7 = p) (hr8 : st₀.regs 8 = bunCap) (hr9 : st₀.regs 9 = endBundleBase)
    (hr10 : st₀.regs 10 = prevBase) (hr11 : st₀.regs 11 = nextBase)
    (hr13 : st₀.regs 13 = offPtr) (hr14 : st₀.regs 14 = bufPtr)
    (hr18 : st₀.regs 18 = candArr) (hr20 : st₀.regs 20 = batchPtr)
    (hr21 : st₀.regs 21 = writeOff) (hr22 : st₀.regs 22 = updCnt) (hr24 : st₀.regs 24 = candIdx) :
    let m_b := (scan_j.filter fun t => t.1 == b).length
    let vruns := byRootVRuns B B.edges src' b
    let res := runsFoldStep (ops, B) (b, vruns)
    let addedUpds := (vruns.drop 1).length
    ∃ stEnd cEnd txEnd hEnd addedWords,
      Runs w pProg ω (bundleStepEmitOneCandStmt bDllPush bDllErase bMergeSort bTourOwner)
        st₀ .normal stEnd cEnd ∧
      (∀ r ≤ 24, r ≠ 4 → r ≠ 21 → r ≠ 22 → r ≠ 23 → stEnd.regs r = st₀.regs r) ∧
      stEnd.regs 4 = hEnd ∧ hCur ≤ hEnd ∧ hEnd ≤ hCur + (8 + 2 * TS.querySpace) * m_b ∧
      stEnd.regs 21 = writeOff + addedWords ∧
      stEnd.regs 22 = updCnt + addedUpds ∧
      addedWords ≤ 6 * m_b ∧ addedUpds ≤ m_b ∧
      res.2.vertices = Finset.range (nB + addedUpds) ∧
      BundleSlotRepAt eCap prevBase nextBase p bunCap res.2 stEnd.mem ∧
      G₀.applyBatch res.1 = res.2.graph ∧
      SmallBatchBodyAt stEnd.mem (batchPtr + 1) G₀ res.1 (writeOff + addedWords - 1) ∧
      (∀ x ∈ B.ends b, stEnd.mem (endBundleBase + endKey x) = res.2.bundleOf x ∨
        (res.2.bundleOf x = b ∧ stEnd.mem (endBundleBase + endKey x) = st₀.mem (endBundleBase + endKey x))) ∧
      htour.rep.rep tourH cord' txEnd stEnd.mem ∧
      (∀ a, htour.rep.foot tourH txEnd a → htour.rep.foot tourH tx₀ a ∨ (hCur ≤ a ∧ a < hEnd)) ∧
      ZeroFrom stEnd.mem hEnd ∧
      (∀ a, ¬ htour.rep.foot tourH tx₀ a →
        (a < p ∨ p + bundleSlotBlockSize bunCap ≤ a) →
        (∀ x ∈ B.ends b, a ≠ prevBase + endKey x ∧ a ≠ nextBase + endKey x ∧ a ≠ endBundleBase + endKey x) →
        (a < batchPtr + writeOff ∨ batchPtr + writeOff + 6 * m_b ≤ a) →
        (a < hCur ∨ hEnd ≤ a) → stEnd.mem a = st₀.mem a) ∧
      cEnd + htour.rep.phi tourH txEnd stEnd.mem ≤
        (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * m_b + 1) + 1) + 920) * m_b + 420 +
        htour.rep.phi tourH tx₀ st₀.mem := by
  intro m_b vruns res addedUpds
  rw [show (scan_j.filter fun t => t.1 == b).length = m_b from rfl] at hbuf_w hbuf_le_h hbat_w hupd_w hh_w hnb_cap hbat_blk hbat_prev hbat_next hbat_eb hbat_h htfoot_disj_bat hhi_mem
  set degB := (B.ends b).card
  set L_b := scan_j.filter fun t => t.1 == b
  have hm_b_eq : L_b.length = m_b := rfl
  have hrep_copy := hrep
  obtain ⟨nB', hV', hnB', hE_lt, hbo_lt', _, _, _, _, hdll_all, _, _, _⟩ := hrep
  have hnB_eq : nB' = nB := by
    have := congrArg Finset.card (hV'.symm.trans hV); simpa [Finset.card_range] using this
  rw [hnB_eq] at hV' hnB' hbo_lt' hdll_all
  obtain ⟨L_dll, hdll_b, hsz_b, hmem_b⟩ := hdll_all b hb_lt
  have hL_dll_len : L_dll.length = degB := by
    have himg : (B.ends b).image endKey = L_dll.toFinset := by
      ext k; simp only [Finset.mem_image, List.mem_toFinset, hmem_b]
      exact ⟨fun ⟨x, hx, heq⟩ => by subst heq; rwa [bundle_endOfKey_endKey],
        fun hk => ⟨endOfKey k, hk, bundle_endKey_endOfKey k⟩⟩
    rw [← List.toFinset_card_of_nodup hdll_b.1, ← himg, Finset.card_image_of_injective _ endKey_injective]
  have hE_init_lt : ∀ e ∈ B_init.edges, e < eCap := fun e he => hE_lt e (hB_edges ▸ he)
  have hsurv_eq : survivingEnds B B.edges b = B.ends b := by
    ext x; simp only [survivingEnds, Finset.mem_filter, BundleState.mem_ends]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
  have hsurv_init : survivingEnds B B.edges b = survivingEnds B_init B_init.edges b := by
    ext x; simp only [survivingEnds, Finset.mem_filter, hB_ends_b, hB_edges]
  have hraw_eq_init : rawByRootVRuns B B.edges src' b = rawByRootVRuns B_init B_init.edges src' b := by
    simp only [rawByRootVRuns, finalRootsOf, hsurv_init]
  have hvruns_eq_init : byRootVRuns B B.edges src' b = byRootVRuns B_init B_init.edges src' b := by
    simp only [byRootVRuns, hraw_eq_init]
  have h3_w : 3 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  -- Load `b = candArr[candIdx]` and `degB = size[b]`
  let r25 := Function.update st₀.regs 25 b
  let r26 := Function.update r25 26 degB
  let stA : State := { st₀ with regs := r26 }
  have ha25 : Runs w pProg ω (.assign 25 (.load (.bin .add (.reg 18) (.reg 24))))
      st₀ .normal { st₀ with regs := r25 } 5 :=
    runs_assign_iff.mpr ⟨b, by simp [Expr.eval, BinOp.eval, hr18, hr24, hcand_w, hm_cand], rfl, rfl, rfl⟩
  have ha26 : Runs w pProg ω (.assign 26 (.load (.bin .add (.bin .add (.bin .add (.reg 7) (.const 3)) (.reg 8)) (.reg 25))))
      { st₀ with regs := r25 } .normal stA 9 :=
    runs_assign_iff.mpr ⟨degB, by
      simp [Expr.eval, BinOp.eval, r25, hr7, hr8, h3_w,
        show p + 3 < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
        show p + 3 + bunCap < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
        show p + 3 + bunCap + b < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
        show st₀.mem (p + 3 + bunCap + b) = degB from by simpa [bsSizeBase, hL_dll_len] using hsz_b],
      rfl, rfl, by simp [Expr.size]⟩
  by_cases hdeg0 : degB = 0
  · -- Case 1: `degB = 0` → `.nop`
    have hempty : B.ends b = ∅ := Finset.card_eq_zero.mp hdeg0
    have hvruns_nil : vruns = [] := by
      simp only [vruns, byRootVRuns, rawByRootVRuns, finalRootsOf, hsurv_eq, hempty, Finset.image_empty,
        Finset.sort_empty, List.map_nil, promoteLargestRun]
    have hres_eq : res = (ops, B) := by
      simp only [res, hvruns_nil, runsFoldStep, bundleSplitFoldStep, List.map_nil, bundleRunUpdates,
        List.drop_nil, List.zipIdx_nil, MGraph.applyBatch, List.foldl_nil, List.append_nil]
      refine Prod.ext rfl ?_
      rcases B with ⟨vB, eB, pB, boB⟩
      simp only [BundleState.graph, BundleState.mk.injEq, true_and]
      exact ⟨funext fun _ => by simp [runParent], funext fun x : End => by rcases x with ⟨e, side⟩; cases side <;> rfl⟩
    have hnop : ∀ sThen : Stmt, Runs w pProg ω (.cond (.reg 26) sThen .nop) stA .normal stA 3 := fun _ =>
      runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, stA, r26, hdeg0],
        by simpa using (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩ : Runs w pProg ω .nop stA .normal stA 1), by simp [Expr.size]⟩
    refine ⟨stA, 5 + (9 + 3 + 1) + 1, tx₀, hCur, 0,
      bundle_runs_seq_normal ha25 (bundle_runs_seq_normal ha26 (hnop _)),
      fun r hr _ _ _ _ => by simp [stA, r26, r25, show r ≠ 26 by omega, show r ≠ 25 by omega],
      by simp [stA, r26, r25, hr4], le_refl _, by omega,
      by simp [stA, r26, r25, hr21],
      by simp [stA, r26, r25, hr22, addedUpds, hvruns_nil],
      by omega, by simp [addedUpds, hvruns_nil],
      by rw [hres_eq]; simp [addedUpds, hvruns_nil, hV],
      by rw [hres_eq]; exact hrep_copy,
      by rw [hres_eq]; exact hG₀,
      by rw [hres_eq]; simpa using hbat,
      (fun x (hx : x ∈ B.ends b) => by rw [hempty] at hx; cases hx),
      htrep, fun _ ha => Or.inl ha, hzero, fun _ _ _ _ _ _ => rfl, by dsimp only [stA]; omega⟩
  · -- `degB > 0`: load `lo`, `hi`, `m_b = hi - lo`
    have hdeg_pos : 0 < degB := Nat.pos_of_ne_zero hdeg0
    have hmb_le_deg : m_b ≤ degB := by
      have h := scanValidForSlot_filter_len_le hval b; rwa [← hB_ends_b] at h
    have hdeg_lt_w : degB < 2 ^ w := by
      have hcard_le : degB ≤ 2 * eCap := by
        have hsub : (B.ends b).image endKey ⊆ Finset.range (2 * eCap) := fun k hk => by
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
          rw [Finset.mem_range]
          have := hE_lt x.1 ((BundleState.mem_ends B b x).mp hx).1
          rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
        calc degB = ((B.ends b).image endKey).card := (Finset.card_image_of_injective _ endKey_injective).symm
          _ ≤ (Finset.range (2 * eCap)).card := Finset.card_le_card hsub
          _ = 2 * eCap := Finset.card_range _
      omega
    obtain ⟨w_rem, hrem_ne, hrem_eq⟩ := hval.2.2 b hb_cand
    let r28 := Function.update stA.regs 28 lo
    let r29 := Function.update r28 29 (lo + m_b)
    let r30 := Function.update r29 30 m_b
    let stB : State := { stA with regs := r30 }
    have ha28 : Runs w pProg ω (.assign 28 (.load (.bin .add (.reg 13) (.reg 24))))
        stA .normal { stA with regs := r28 } 5 :=
      runs_assign_iff.mpr ⟨lo, by
        simp [Expr.eval, BinOp.eval, stA, r26, r25, hr13, hr24, show offPtr + candIdx < 2 ^ w by omega, hlo_mem],
        rfl, rfl, rfl⟩
    have ha29 : Runs w pProg ω (.assign 29 (.load (.bin .add (.reg 13) (.bin .add (.reg 24) (.const 1)))))
        { stA with regs := r28 } .normal { stA with regs := r29 } 7 :=
      runs_assign_iff.mpr ⟨lo + m_b, by
        simp [Expr.eval, BinOp.eval, r28, stA, r26, r25, hr13, hr24, h1_w,
          show candIdx + 1 < 2 ^ w by omega, show offPtr + (candIdx + 1) < 2 ^ w by omega, hhi_mem],
        rfl, rfl, by simp [Expr.size]⟩
    have ha30 : Runs w pProg ω (.assign 30 (.bin .sub (.reg 29) (.reg 28)))
        { stA with regs := r29 } .normal stB 4 :=
      runs_assign_iff.mpr ⟨m_b, by
        simp [Expr.eval, BinOp.eval, r29, r28, show lo + m_b - lo = m_b by omega, show m_b < 2 ^ w by omega],
        rfl, rfl, rfl⟩
    by_cases hmb0 : m_b = 0
    · -- Case 2: `degB > 0`, `m_b = 0` → all ends of `b` stay at `w_rem`, `.nop`!
      have hsr_nil : scanVRuns B_init src' b w_rem = [] := by
        have hlen := (scanVRuns_pack_eq_sort hE_init_lt hval hrem_ne hrem_eq).2
        have h0 : vRunsEndsLen (scanVRuns B_init src' b w_rem) = 0 := by rwa [show (scan_j.filter fun t => t.1 == b).length = 0 from hmb0] at hlen
        cases hsr : scanVRuns B_init src' b w_rem with
        | nil => rfl
        | cons vr tl =>
          have hpos := (rawByRootVRuns_info vr (List.mem_filter.mp (hsr ▸ List.mem_cons_self)).1).1
          rw [hsr] at h0; simp only [vRunsEndsLen, List.map_cons, List.sum_cons] at h0; omega
      obtain ⟨keptXs, hkept_pos, _, hby_eq⟩ := byRootVRuns_branch1_eq hE_init_lt hval hrem_ne hrem_eq
        (fun vr hvr => by rw [hsr_nil] at hvr; cases hvr)
        (by rw [← hB_ends_b]; change 0 < degB - m_b; omega)
      rw [hsr_nil, ← hvruns_eq_init] at hby_eq
      obtain ⟨hfold_eq, _⟩ := runsFoldStep_eq_fold_oneRun (ops := ops) (B := B) (nB := nB) (b := b)
        (v0 := w_rem) (xs0 := keptXs) (rest := []) hV hb_lt
      let B0 : BundleState := { B with parent := Function.update B.parent b w_rem }
      have hres_eq : res = (ops, B0) := by
        have : runsFoldStep (ops, B) (b, (w_rem, keptXs) :: []) = (ops, B0) := by
          simpa [foldOneSplitRuns] using hfold_eq.symm
        simpa [res, vruns, hby_eq] using this
      have hrep_B0 : BundleSlotRepAt eCap prevBase nextBase p bunCap B0 stB.mem := by
        obtain ⟨nB'', hV'', hnB'', hE'', hbo'', hpar0'', hc0, hc1, hc2, hdll'', hpar'', htail'', hscr''⟩ := hrep_copy
        have hnB''_eq : nB'' = nB := by
          have := congrArg Finset.card (hV''.symm.trans hV); simpa [Finset.card_range] using this
        refine ⟨nB'', hV'', hnB'', hE'', hbo'', fun c hc => by
          dsimp only [B0]; rw [Function.update_of_ne (by omega)]; exact hpar0'' c hc,
          hc0, hc1, hc2, hdll'', fun c hc hem => by
          have hcb : c ≠ b := fun heq => (Finset.card_pos.mp hdeg_pos).ne_empty (heq ▸ hem)
          dsimp only [B0]; rw [Function.update_of_ne hcb]; exact hpar'' c hc hem, htail'', hscr''⟩
      have hnop30 : ∀ sThen : Stmt, Runs w pProg ω (.cond (.reg 30) sThen .nop) stB .normal stB 3 := fun _ =>
        runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, stB, r30, hmb0],
          by simpa using (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩ : Runs w pProg ω .nop stB .normal stB 1), by simp [Expr.size]⟩
      have hcond26 : ∀ sThen : Stmt, Runs w pProg ω
          (.cond (.reg 26)
            (.assign 28 (.load (.bin .add (.reg 13) (.reg 24))) ;;
             .assign 29 (.load (.bin .add (.reg 13) (.bin .add (.reg 24) (.const 1)))) ;;
             .assign 30 (.bin .sub (.reg 29) (.reg 28)) ;;
             .cond (.reg 30) sThen .nop) .nop)
          stA .normal stB (1 + (5 + (7 + (4 + 3 + 1) + 1) + 1) + 1) := fun sThen =>
        runs_cond_iff.mpr ⟨degB, _, by simp [Expr.eval, stA, r26],
          by simpa [hdeg0] using bundle_runs_seq_normal ha28 (bundle_runs_seq_normal ha29 (bundle_runs_seq_normal ha30 (hnop30 sThen))),
          by simp [Expr.size]⟩
      refine ⟨stB, _, tx₀, hCur, 0,
        bundle_runs_seq_normal ha25 (bundle_runs_seq_normal ha26 (hcond26 _)),
        fun r hr _ _ _ _ => by
          simp [stB, r30, r29, r28, stA, r26, r25, show r ≠ 30 by omega, show r ≠ 29 by omega,
            show r ≠ 28 by omega, show r ≠ 26 by omega, show r ≠ 25 by omega],
        by simp [stB, r30, r29, r28, stA, r26, r25, hr4], le_refl _, by omega,
        by simp [stB, r30, r29, r28, stA, r26, r25, hr21],
        by simp [stB, r30, r29, r28, stA, r26, r25, hr22, addedUpds, vruns, hby_eq],
        by omega, by simp [addedUpds, vruns, hby_eq],
        by rw [hres_eq]; simp [addedUpds, vruns, hby_eq, B0, hV],
        by rw [hres_eq]; exact hrep_B0,
        by rw [hres_eq]; exact hG₀,
        by rw [hres_eq]; simpa using hbat,
        fun x hx => Or.inr ⟨by rw [hres_eq]; exact ((BundleState.mem_ends B b x).mp hx).2, rfl⟩,
        htrep, fun _ ha => Or.inl ha, hzero, fun _ _ _ _ _ _ => rfl, by dsimp only [stB, stA]; omega⟩
    · -- `degB > 0`, `m_b > 0`: copy CSR slice, sort, run `MaxRun`, branch on `winLen < degB - m_b`
      have hmb_pos : 0 < m_b := Nat.pos_of_ne_zero hmb0
      have h2mb_le_sp : 2 * m_b ≤ (8 + 2 * TS.querySpace) * m_b := by
        have h : 2 ≤ 8 + 2 * TS.querySpace := by omega
        exact Nat.mul_le_mul_right m_b h
      -- Allocate `[hCur, hCur + m_b)` and copy CSR slice
      let r27c := Function.update stB.regs 27 hCur
      let r4c := Function.update r27c 4 (hCur + m_b)
      let stC0 : State := { stB with regs := r4c }
      have ha27c : Runs w pProg ω (.assign 27 (.reg 4)) stB .normal { stB with regs := r27c } 2 :=
        runs_assign_iff.mpr ⟨hCur, by simp [Expr.eval, stB, r30, r29, r28, stA, r26, r25, hr4], rfl, rfl, rfl⟩
      have ha4c : Runs w pProg ω (.assign 4 (.bin .add (.reg 27) (.reg 30)))
          { stB with regs := r27c } .normal stC0 4 :=
        runs_assign_iff.mpr ⟨hCur + m_b, by
          simp [Expr.eval, BinOp.eval, r27c, stB, r30, show hCur + m_b < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hLperm_len : L_perm.length = m_b := by rw [hperm.length_eq, List.length_map]
      obtain ⟨stC, cCopy, hrunCopy, hregsC, hLatC, hfrC, hcCopy⟩ :=
        copy_slice_runs (bufPtr := bufPtr) (lo := lo) (dstPtr := hCur) (L := L_perm) (st₀ := stC0)
          hw16 (by rw [hLperm_len]; exact hbuf_w) (by rw [hLperm_len]; omega)
          (by rw [hLperm_len]; exact hbuf_le_h) hbuf_at
          (by simp [stC0, r4c, r27c, stB, r30, r29, r28, stA, r26, r25, hr14])
          (by simp [stC0, r4c, r27c])
          (by simp [stC0, r4c, r27c, stB, r30, r29, r28])
          (by simp [stC0, r4c, r27c, stB, r30, hLperm_len])
      rw [hLperm_len] at hfrC hcCopy
      -- Sort `mem[hCur .. hCur + m_b)` with scratch `[hCur + m_b .. hCur + 2 * m_b)`
      let r28s := Function.update stC.regs 28 (hCur + m_b)
      let r4s := Function.update r28s 4 (hCur + 2 * m_b)
      have ha28s : Runs w pProg ω (.assign 28 (.reg 4)) stC .normal { stC with regs := r28s } 2 :=
        runs_assign_iff.mpr ⟨hCur + m_b, by
          simp [Expr.eval, hregsC 4 (by decide), stC0, r4c], rfl, rfl, rfl⟩
      have ha4s : Runs w pProg ω (.assign 4 (.bin .add (.reg 28) (.reg 30)))
          { stC with regs := r28s } .normal { stC with regs := r4s } 4 :=
        runs_assign_iff.mpr ⟨hCur + 2 * m_b, by
          simp [Expr.eval, BinOp.eval, r28s, hregsC 30 (le_refl _), stC0, r4c, r27c, stB, r30,
            show hCur + m_b + m_b = hCur + 2 * m_b by omega, show hCur + 2 * m_b < 2 ^ w by omega],
          rfl, rfl, rfl⟩
      have hLperm_w : ∀ z ∈ L_perm, z < 2 ^ w := fun z hz => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (hperm.subset hz)
        obtain ⟨ht_in, htb⟩ := List.mem_filter.mp ht
        have htb' : t.1 = b := by simpa using htb
        have htB : endOfKey t.2.2 ∈ B.ends b := by rw [hB_ends_b, ← htb']; exact (hval.2.1 t ht_in).2.1
        have htsrc : t.2.1 < vCap := by rw [← (hval.2.1 t ht_in).2.2]; exact hsrc_lt _ htB
        have htk : t.2.2 < 2 * eCap := by
          have := hE_lt (endOfKey t.2.2).1 ((BundleState.mem_ends B b _).mp htB).1
          have hkeq := bundle_endKey_endOfKey t.2.2
          rcases hxk : endOfKey t.2.2 with ⟨ee, side⟩
          rw [hxk] at this hkeq; cases side <;> simp [endKey] at hkeq <;> omega
        have hmul := Nat.mul_le_mul_right (2 * eCap) (show t.2.1 + 1 ≤ vCap by omega)
        unfold packEndKey; rw [Nat.add_mul, Nat.one_mul] at hmul; omega
      obtain ⟨bodyS, hbodyS, oS, stS, cS, hrunS, hpostS, hcS⟩ :=
        hMergeSort L_perm [hCur, L_perm.length, hCur + m_b] stC.mem stC.pos ω
          (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
          ⟨hCur, hCur + m_b, rfl, hw16, by omega, by omega, Or.inl (by omega), hLatC, hLperm_w⟩
      rcases hpostS with ⟨aS, scS, L', hargsS, _, hpermS, hsortS, hLatS, hfrS⟩
      rcases List.cons.inj hargsS with ⟨haS_eq, hargsS1⟩
      rcases List.cons.inj hargsS1 with ⟨_, hargsS2⟩
      rcases List.cons.inj hargsS2 with ⟨hscS_eq, _⟩
      rw [← haS_eq] at hLatS hfrS; rw [← hscS_eq] at hfrS
      set sr := scanVRuns B_init src' b w_rem
      obtain ⟨hsr_pack, hsr_len⟩ := scanVRuns_pack_eq_sort hE_init_lt hval hrem_ne hrem_eq
      change vRunsPacked eCap sr = _ at hsr_pack
      change vRunsEndsLen sr = m_b at hsr_len
      have hLb_pk_nd : (L_b.map fun t => packEndKey eCap t.2.1 t.2.2).Nodup := by
        have hLb_k_nd : (L_b.map fun t => t.2.2).Nodup := hval.1.sublist (List.filter_sublist.map _)
        have hLb_lt : ∀ t ∈ L_b, t.2.2 < 2 * eCap := fun t ht => by
          obtain ⟨ht_in, htb⟩ := List.mem_filter.mp ht
          have htb' : t.1 = b := by simpa using htb
          have htB : endOfKey t.2.2 ∈ B.ends b := by rw [hB_ends_b, ← htb']; exact (hval.2.1 t ht_in).2.1
          have := hE_lt (endOfKey t.2.2).1 ((BundleState.mem_ends B b _).mp htB).1
          have hkeq := bundle_endKey_endOfKey t.2.2
          rcases hxk : endOfKey t.2.2 with ⟨ee, side⟩
          rw [hxk] at this hkeq; cases side <;> simp [endKey] at hkeq <;> omega
        have hgo : ∀ l : List (ℕ × ℕ × ℕ), (l.map fun t => t.2.2).Nodup →
            (∀ t ∈ l, t.2.2 < 2 * eCap) → (l.map fun t => packEndKey eCap t.2.1 t.2.2).Nodup := by
          intro l; induction l with
          | nil => intro _ _; exact List.nodup_nil
          | cons a tl ih =>
            intro hnd hlt; obtain ⟨ha_not, htl_nd⟩ := List.nodup_cons.mp hnd
            rw [List.map_cons, List.nodup_cons]
            refine ⟨fun hm => ?_, ih htl_nd fun t ht => hlt t (List.mem_cons_of_mem _ ht)⟩
            obtain ⟨t, ht, heq⟩ := List.mem_map.mp hm
            exact ha_not (List.mem_map.mpr ⟨t, ht, (packEndKey_inj (hlt t (List.mem_cons_of_mem _ ht)) (hlt a List.mem_cons_self) heq).2⟩)
        exact hgo L_b hLb_k_nd hLb_lt
      have hL'_eq : L' = vRunsPacked eCap sr := by
        have hnd_perm : L_perm.Nodup := hperm.nodup_iff.mpr hLb_pk_nd
        rw [sorted_perm_eq_toFinset_sort hnd_perm hpermS hsortS, hsr_pack]
        congr 1; ext z; simp [List.mem_toFinset, hperm.mem_iff, L_b]
      rw [hL'_eq] at hLatS
      let stM : State := { mem := stS.mem, regs := Function.update r4s 29 oS.value, pos := stS.pos }
      have hcallS : Runs w pProg ω (.call 29 bMergeSort [.reg 27, .reg 30, .reg 28])
          { stC with regs := r4s } .normal stM (cS + 4) :=
        runs_call_iff.mpr ⟨[hCur, L_perm.length, hCur + m_b], bodyS, oS, stS, cS,
          by simp [evalArgs, Expr.eval, r4s, r28s, hregsC 27 (by decide), hregsC 30 (le_refl _),
            stC0, r4c, r27c, stB, r30, hLperm_len],
          hbodyS, hrunS, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      -- Run `bundleStepEmitMaxRunStmt` on `sr`
      have hsr_sub : ∀ vr ∈ sr, vr ∈ rawByRootVRuns B_init B_init.edges src' b :=
        fun vr hvr => (List.mem_filter.mp hvr).1
      have hsr_pos : ∀ vr ∈ sr, vr.1 < vCap ∧ 0 < vr.2.length := fun vr hvr => by
        have hi := rawByRootVRuns_info vr (hsr_sub vr hvr)
        obtain ⟨x₀, hx₀⟩ := List.length_pos_iff_exists_mem.mp hi.1
        have hxi := hi.2.2 x₀ hx₀
        exact ⟨hxi.2 ▸ hsrc_lt x₀ (hB_ends_b.symm ▸ hxi.1), hi.1⟩
      have hsr_pw : (sr.map Prod.fst).Pairwise (· < ·) := scanVRuns_pairwise
      have hsr_keys : ∀ vr ∈ sr, ∀ x ∈ vr.2, endKey x < 2 * eCap := fun vr hvr x hx => by
        have hxB : x ∈ B.ends b := hB_ends_b.symm ▸ ((rawByRootVRuns_info vr (hsr_sub vr hvr)).2.2 x hx).1
        have := hE_lt x.1 ((BundleState.mem_ends B b x).mp hxB).1
        rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
      obtain ⟨stMR, cMR, hrunMR, hmemMR, hregsMR, _, _, hr33MR, hcMR⟩ :=
        bundleStepEmitMaxRun_runs (vCap := vCap) (arr := hCur) (vruns := sr) (st₀ := stM)
          hw16 hpk_w (by rw [hsr_len]; omega) hsr_pos hsr_pw hsr_keys hLatS
          (by simp [stM, r4s, r28s, hregsC 6 (by decide), stC0, r4c, r27c, stB, r30, r29, r28, stA, r26, r25, hr6])
          (by simp [stM, r4s, r28s, hregsC 27 (by decide), stC0, r4c, r27c])
          (by simp [stM, r4s, r28s, hregsC 30 (le_refl _), stC0, r4c, r27c, stB, r30, hsr_len])
      rw [hsr_len] at hcMR
      -- Memory frame from `st₀` to `stMR`: only `[hCur, hCur + 2 * m_b)` was touched!
      have hfr_toMR : ∀ a, (a < hCur ∨ hCur + 2 * m_b ≤ a) → stMR.mem a = st₀.mem a := fun a ha => by
        rw [hmemMR]; dsimp only [stM]
        rw [hfrS a (by rw [hLperm_len]; omega) (by rw [hLperm_len]; omega), hfrC a (by omega)]
      have hMR_regs : ∀ r ≤ 26, r ≠ 4 → stMR.regs r = stA.regs r := fun r hr h4 => by
        rw [hregsMR r (by omega)]
        simp only [stM, r4s, r28s, Function.update_of_ne (show r ≠ 29 by omega),
          Function.update_of_ne h4, Function.update_of_ne (show r ≠ 28 by omega)]
        rw [hregsC r (by omega)]
        simp [stC0, r4c, r27c, stB, r30, r29, r28, h4, show r ≠ 27 by omega, show r ≠ 30 by omega,
          show r ≠ 29 by omega, show r ≠ 28 by omega]
      have hMR_orig : ∀ r ≤ 24, r ≠ 4 → stMR.regs r = st₀.regs r := fun r hr h4 => by
        rw [hMR_regs r (by omega) h4]
        simp [stA, r26, r25, show r ≠ 26 by omega, show r ≠ 25 by omega]
      have hr4MR : stMR.regs 4 = hCur + 2 * m_b := by
        rw [hregsMR 4 (by decide)]; simp [stM, r4s]
      have hr25MR : stMR.regs 25 = b := by rw [hMR_regs 25 (by decide) (by decide)]; simp [stA, r26, r25]
      have hr26MR : stMR.regs 26 = degB := by rw [hMR_regs 26 (le_refl _) (by decide)]; simp [stA, r26]
      have hr30MR : stMR.regs 30 = m_b := by
        rw [hregsMR 30 (le_refl _)]; simp [stM, r4s, r28s, hregsC 30 (le_refl _), stC0, r4c, r27c, stB, r30]
      set winLen := (sr.getD (maxRunIdx sr) (0, [])).2.length
      have hrep_MR : BundleSlotRepAt eCap prevBase nextBase p bunCap B stMR.mem :=
        hrep_copy.of_agree (fun a _ h2 => (hfr_toMR a (Or.inl (by omega))).symm)
          (fun k hk => (hfr_toMR _ (Or.inl (by omega))).symm)
          (fun k hk => (hfr_toMR _ (Or.inl (by omega))).symm)
      have hbat_MR : SmallBatchBodyAt stMR.mem (batchPtr + 1) G₀ ops (writeOff - 1) :=
        smallBatchBodyAt_agree hbat fun a _ ha2 => hfr_toMR a (Or.inl (by omega))
      have htour_MR := htour.rep_local tourH cord' tx₀ st₀.mem stMR.mem fun a ha =>
        (hfr_toMR a (Or.inl (htfoot_lt a ha))).symm
      have hzero_MR : ZeroFrom stMR.mem (hCur + 2 * m_b) := fun a ha =>
        (hfr_toMR a (Or.inr ha)).trans (hzero a (by omega))
      let sBranch : Stmt :=
        .cond (.bin .lt (.reg 33) (.bin .sub (.reg 26) (.reg 30)))
          (.assign 26 (.reg 30) ;;
           .assign 29 (.const 0) ;;
           .loop (.bin .lt (.reg 29) (.reg 26))
             (bundleStepEmitOneRunStmt bDllPush bDllErase))
          (.assign 27 (.reg 4) ;;
           .assign 4 (.bin .add (.reg 27) (.reg 26)) ;;
           .assign 28 (.load (.bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25))) ;;
           .assign 29 (.const 0) ;;
           .loop (.reg 28)
             (.assign 30 (.bin .sub (.reg 28) (.const 1)) ;;
              .assign 31 (.reg 4) ;;
              .call 4 bTourOwner [.reg 1, .reg 30, .reg 4] ;;
              .assign 32 (.load (.reg 31)) ;;
              .store (.bin .add (.reg 27) (.reg 29))
                (.bin .add (.bin .mul (.reg 32) (.reg 6)) (.reg 30)) ;;
              .assign 29 (.bin .add (.reg 29) (.const 1)) ;;
              .assign 28 (.load (.bin .add (.reg 11) (.reg 30)))) ;;
           .assign 28 (.reg 4) ;;
           .assign 4 (.bin .add (.reg 28) (.reg 26)) ;;
           .call 29 bMergeSort [.reg 27, .reg 26, .reg 28] ;;
           .assign 30 (.reg 26) ;;
           bundleStepEmitMaxRunStmt ;;
           .assign 23 (.reg 26) ;;
           .assign 28 (.reg 32) ;;
           .assign 26 (.reg 31) ;;
           .assign 29 (.const 0) ;;
           .loop (.bin .lt (.reg 29) (.reg 26))
             (bundleStepEmitOneRunStmt bDllPush bDllErase) ;;
           .assign 26 (.reg 23) ;;
           .assign 29 (.reg 28) ;;
           .loop (.bin .lt (.reg 29) (.reg 26))
             (bundleStepEmitOneRunStmt bDllPush bDllErase))
      have hpref_run : ∀ {stEnd cTail},
          Runs w pProg ω sBranch stMR .normal stEnd cTail →
          Runs w pProg ω
            (bundleStepEmitOneCandStmt bDllPush bDllErase bMergeSort bTourOwner)
            st₀ .normal stEnd
            (5 + (9 + (1 + (5 + (7 + (4 + (1 + (2 + (4 + (cCopy + (2 + (4 + (cS + 4 + (cMR + cTail + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
        intro stEnd cTail hTail
        have h1 := bundle_runs_seq_normal ha27c (bundle_runs_seq_normal ha4c (bundle_runs_seq_normal hrunCopy
          (bundle_runs_seq_normal ha28s (bundle_runs_seq_normal ha4s (bundle_runs_seq_normal hcallS
            (bundle_runs_seq_normal hrunMR hTail))))))
        have hc30 : Runs w pProg ω (.cond (.reg 30) _ .nop) stB .normal stEnd
            (1 + (2 + (4 + (cCopy + (2 + (4 + (cS + 4 + (cMR + cTail + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨m_b, _, by simp [Expr.eval, stB, r30], by simpa [hmb0] using h1, by simp [Expr.size]⟩
        have h2 := bundle_runs_seq_normal ha28 (bundle_runs_seq_normal ha29 (bundle_runs_seq_normal ha30 hc30))
        have hc26 : Runs w pProg ω (.cond (.reg 26) _ .nop) stA .normal stEnd
            (1 + (5 + (7 + (4 + (1 + (2 + (4 + (cCopy + (2 + (4 + (cS + 4 + (cMR + cTail + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨degB, _, by simp [Expr.eval, stA, r26], by simpa [hdeg0] using h2, by simp [Expr.size]⟩
        exact bundle_runs_seq_normal ha25 (bundle_runs_seq_normal ha26 hc26)
      by_cases hbr1 : winLen < degB - m_b
      · -- Branch 1 (`winLen < degB - m_b`): keep unscanned `w_rem` run, emit `sr`
        have hsr_ne : sr ≠ [] := fun hnil => by rw [hnil] at hsr_len; simp [vRunsEndsLen] at hsr_len; omega
        have hwin_lt_all : ∀ vr ∈ sr, vr.2.length < (B_init.ends b).card - L_b.length := fun vr hvr => by
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hvr
          have hspec := (maxRunIdx_spec hsr_ne).1 i hi
          have hlt_b := maxRunIdx_lt hsr_ne
          have hwl : winLen = (sr[maxRunIdx sr]'hlt_b).2.length := by
            simp only [winLen, List.getD_eq_getElem _ _ hlt_b]
          rw [← hB_ends_b]; change (sr[i]'hi).2.length < degB - m_b; omega
        obtain ⟨keptXs, hkept_pos, hkept_info, hby_eq⟩ := byRootVRuns_branch1_eq hE_init_lt hval hrem_ne hrem_eq
          hwin_lt_all (by rw [← hB_ends_b]; change 0 < degB - m_b; omega)
        rw [← hvruns_eq_init] at hby_eq
        let B0 : BundleState := { B with parent := Function.update B.parent b w_rem }
        have hrep_B0 : BundleSlotRepAt eCap prevBase nextBase p bunCap B0 stMR.mem := by
          obtain ⟨nB'', hV'', hnB'', hE'', hbo'', hpar0'', hc0, hc1, hc2, hdll'', hpar'', htail'', hscr''⟩ := hrep_MR
          have hnB''_eq : nB'' = nB := by
            have := congrArg Finset.card (hV''.symm.trans hV); simpa [Finset.card_range] using this
          refine ⟨nB'', hV'', hnB'', hE'', hbo'', fun c hc => by
            dsimp only [B0]; rw [Function.update_of_ne (by omega)]; exact hpar0'' c hc,
            hc0, hc1, hc2, hdll'', fun c hc hem => by
            have hcb : c ≠ b := fun heq => (Finset.card_pos.mp hdeg_pos).ne_empty (heq ▸ hem)
            dsimp only [B0]; rw [Function.update_of_ne hcb]; exact hpar'' c hc hem, htail'', hscr''⟩
        let r26b1 := Function.update stMR.regs 26 m_b
        let r29b1 := Function.update r26b1 29 0
        let stB1 : State := { stMR with regs := r29b1 }
        have ha26b1 : Runs w pProg ω (.assign 26 (.reg 30)) stMR .normal { stMR with regs := r26b1 } 2 :=
          runs_assign_iff.mpr ⟨m_b, by simp [Expr.eval, hr30MR], rfl, rfl, rfl⟩
        have ha29b1 : Runs w pProg ω (.assign 29 (.const 0)) { stMR with regs := r26b1 } .normal stB1 2 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
        have hsr_len_le : sr.length ≤ m_b := by
          rw [← hsr_len]; exact vRuns_len_le_ends sr fun vr hvr => (hsr_pos vr hvr).2
        have hsr_bw_le : vRunsBatchWords sr ≤ 6 * m_b := by
          rw [← hsr_len]; exact vRunsBatchWords_le sr fun vr hvr => (hsr_pos vr hvr).2
        have hdisj_sr : ∀ i j (hi : i < sr.length) (hj : j < sr.length), i ≠ j → ∀ x ∈ sr[i].2, x ∉ sr[j].2 := by
          intro i j hi hj hne x hxi hxj
          have h1 := ((rawByRootVRuns_info _ (hsr_sub _ (List.getElem_mem hi))).2.2 x hxi).2
          have h2 := ((rawByRootVRuns_info _ (hsr_sub _ (List.getElem_mem hj))).2.2 x hxj).2
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have := List.pairwise_iff_getElem.mp hsr_pw i j (by simp; omega) (by simp; omega) hlt
            simp only [List.getElem_map] at this; omega
          · have := List.pairwise_iff_getElem.mp hsr_pw j i (by simp; omega) (by simp; omega) hgt
            simp only [List.getElem_map] at this; omega
        have h4mb_le : 4 * m_b ≤ (8 + 2 * TS.querySpace) * m_b := Nat.mul_le_mul_right _ (by omega)
        obtain ⟨stEnd, cR, hEnd, addedWords, hrunR, hregsR, hr4End, hhEnd_lo, hhEnd_hi, haddW_le_vr,
          hr21End, hr22End, _, hrepEnd, hbatEnd, hebEnd, hfrR, hcR⟩ :=
          bundleStepEmitCand_runsLoop (ω := ω) (degB := m_b) (packArr := hCur)
            hpPush hpErase hw16 heCap_w hpk_w hprev_w hnext_w heb_w hp_w
            (by omega) hprev_next hblk_prev hblk_next heb_prev heb_next heb_blk
            (by omega) (by omega) (by omega) (by omega)
            sr ops B0 nB 0 writeOff updCnt (hCur + 2 * m_b) G₀ stB1
            hV hb_lt (by omega) (by omega) (by omega) (by omega) (by omega)
            (fun vr hvr =>
              have hi := rawByRootVRuns_info vr (hsr_sub vr hvr)
              ⟨(hsr_pos vr hvr).1, hi.1, hi.2.1, fun x hx => hB_ends_b.symm ▸ (hi.2.2 x hx).1⟩)
            hsr_pw hdisj_sr
            ⟨keptXs[0]'hkept_pos, hB_ends_b.symm ▸ (hkept_info _ (List.getElem_mem hkept_pos)).1,
              fun vr hvr hmem => by
                have h1 := (hkept_info _ (List.getElem_mem hkept_pos)).2
                have h2 := ((rawByRootVRuns_info vr (hsr_sub vr hvr)).2.2 _ hmem).2
                have hne : vr.1 ≠ w_rem := by simpa using (List.mem_filter.mp hvr).2
                omega⟩
            (by clear * - hbat_h hsr_bw_le; omega) (Or.inl (by omega))
            (by clear * - hbat_blk hsr_bw_le; omega) (by clear * - hbat_prev hsr_bw_le; omega)
            (by clear * - hbat_next hsr_bw_le; omega) (by clear * - hbat_eb hsr_bw_le; omega)
            (by clear * - hbat_h hsr_bw_le; omega)
            (by omega) (by omega) (by omega) (by omega)
            hrep_B0 hG₀ hbat_MR hw1 (by simpa [stB1, hmemMR] using hLatS)
            (by simp [stB1, r29b1, r26b1, hr4MR])
            (by simp [stB1, r29b1, r26b1, hMR_orig 6 (by decide) (by decide), hr6])
            (by simp [stB1, r29b1, r26b1, hMR_orig 7 (by decide) (by decide), hr7])
            (by simp [stB1, r29b1, r26b1, hMR_orig 8 (by decide) (by decide), hr8])
            (by simp [stB1, r29b1, r26b1, hMR_orig 9 (by decide) (by decide), hr9])
            (by simp [stB1, r29b1, r26b1, hMR_orig 10 (by decide) (by decide), hr10])
            (by simp [stB1, r29b1, r26b1, hMR_orig 11 (by decide) (by decide), hr11])
            (by simp [stB1, r29b1, r26b1, hMR_orig 20 (by decide) (by decide), hr20])
            (by simp [stB1, r29b1, r26b1, hMR_orig 21 (by decide) (by decide), hr21])
            (by simp [stB1, r29b1, r26b1, hMR_orig 22 (by decide) (by decide), hr22])
            (by simp [stB1, r29b1, r26b1, hr25MR])
            (by simp [stB1, r29b1, r26b1])
            (by simp [stB1, r29b1, r26b1, hregsMR 27 (by decide), stM, r4s, r28s, hregsC 27 (by decide), stC0, r4c, r27c])
            (by simp [stB1, r29b1])
        obtain ⟨hfold_eq, _⟩ := runsFoldStep_eq_fold_oneRun (ops := ops) (B := B) (nB := nB) (b := b)
          (v0 := w_rem) (xs0 := keptXs) (rest := sr) hV hb_lt
        have hres_eq1 : (foldOneSplitRuns b sr (ops, B0, nB)).1 = res.1 := by
          have := congrArg Prod.fst hfold_eq; simpa [res, vruns, hby_eq] using this
        have hres_eq2 : (foldOneSplitRuns b sr (ops, B0, nB)).2.1 = res.2 := by
          have := congrArg Prod.snd hfold_eq; simpa [res, vruns, hby_eq] using this
        rw [hres_eq2] at hrepEnd hebEnd; rw [hres_eq1] at hbatEnd
        obtain ⟨hV_f, hE_f, hG_f, hstay_f⟩ := foldOneSplitRuns_props sr G₀ ops B0 nB hV hb_lt hG₀
          (fun vr hvr x hx => hB_ends_b.symm ▸ ((rawByRootVRuns_info vr (hsr_sub vr hvr)).2.2 x hx).1)
          hdisj_sr hbo_lt'
        have hcondB : Runs w pProg ω sBranch
            stMR .normal stEnd (5 + (2 + (2 + cR + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨1, _, by
            simp [Expr.eval, BinOp.eval, hr33MR, hr26MR, hr30MR, show degB - m_b < 2 ^ w by omega, hbr1, h1_w],
            by simpa using bundle_runs_seq_normal ha26b1 (bundle_runs_seq_normal ha29b1 hrunR),
            by simp [Expr.size]⟩
        have hfr_all : ∀ a,
            (a < p ∨ p + bundleSlotBlockSize bunCap ≤ a) →
            (∀ x ∈ B.ends b, a ≠ prevBase + endKey x ∧ a ≠ nextBase + endKey x ∧ a ≠ endBundleBase + endKey x) →
            (a < batchPtr + writeOff ∨ batchPtr + writeOff + 6 * m_b ≤ a) →
            (a < hCur ∨ hEnd ≤ a) → stEnd.mem a = st₀.mem a := fun a haBlk haE haBat haH => by
          rw [hfrR a haBlk (fun x hx => ⟨(haE x hx).1, (haE x hx).2.1⟩)
                (fun vr hvr x hx => (haE x (hB_ends_b.symm ▸ ((rawByRootVRuns_info vr (hsr_sub vr hvr)).2.2 x hx).1)).2.2)
                (by clear * - haBat hsr_bw_le; omega) (by omega)]
          exact hfr_toMR a (by omega)
        have htour_end := htour.rep_local tourH cord' tx₀ st₀.mem stEnd.mem fun a ha =>
          (hfr_all a (htfoot_disj_blk a ha)
            (fun x hx => by
              have hxk : endKey x < 2 * eCap := by
                have := hE_lt x.1 ((BundleState.mem_ends B b x).mp hx).1
                rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
              exact ⟨by have := htfoot_disj_prev a ha; omega,
                     by have := htfoot_disj_next a ha; omega,
                     by have := htfoot_disj_eb a ha; omega⟩)
            (by have := htfoot_disj_bat a ha; omega) (Or.inl (htfoot_lt a ha))).symm
        refine ⟨stEnd, _, tx₀, hEnd, addedWords, hpref_run hcondB,
          fun r hr h4 h21 h22 _ => by
            rw [hregsR r (by omega) h4 h21 h22 (by omega)]
            simp only [stB1, r29b1, r26b1, Function.update_of_ne (show r ≠ 29 by omega),
              Function.update_of_ne (show r ≠ 26 by omega)]
            rw [hMR_regs r (by omega) h4]
            simp [stA, r26, r25, show r ≠ 26 by omega, show r ≠ 25 by omega],
          hr4End, by omega, by omega, hr21End,
          by simpa [addedUpds, vruns, hby_eq] using hr22End,
          le_trans haddW_le_vr hsr_bw_le,
          by simpa [addedUpds, vruns, hby_eq] using hsr_len_le,
          by rw [← hres_eq2]; simpa [addedUpds, vruns, hby_eq] using hV_f,
          hrepEnd, by rw [← hres_eq1, ← hres_eq2]; exact hG_f, hbatEnd, ?_,
          htour_end.1 htrep, fun _ ha => Or.inl ha,
          fun a ha => (hfr_all a
            (by omega)
            (fun x hx => by
              have hxk : endKey x < 2 * eCap := by
                have := hE_lt x.1 ((BundleState.mem_ends B b x).mp hx).1
                rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
              exact ⟨by omega, by omega, by omega⟩)
            (by omega) (Or.inr ha)).trans (hzero a (by omega)),
          fun a _ => hfr_all a, ?_⟩
        · intro x hx
          by_cases hxr : ∃ vr ∈ sr, x ∈ vr.2
          · left; exact hebEnd x (by rw [← hres_eq2, hE_f]; exact (mem_edgeEnds _ _).mpr ((BundleState.mem_ends B b x).mp hx).1) hxr
          · right; push Not at hxr
            have hxk : endKey x < 2 * eCap := by
              have := hE_lt x.1 ((BundleState.mem_ends B b x).mp hx).1
              rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
            have hmem_unch : stEnd.mem (endBundleBase + endKey x) = st₀.mem (endBundleBase + endKey x) := by
              rw [hfrR (endBundleBase + endKey x) (by unfold bundleSlotBlockSize at heb_blk ⊢; clear * - heb_blk hxk; omega)
                (fun y hy => by
                  have hyk : endKey y < 2 * eCap := by
                    have := hE_lt y.1 ((BundleState.mem_ends B b y).mp hy).1
                    rcases y with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
                  exact ⟨by clear * - heb_prev hxk hyk; omega, by clear * - heb_next hxk hyk; omega⟩)
                (fun vr hvr y hy heq => hxr vr hvr ((endKey_injective (by omega : endKey x = endKey y)) ▸ hy))
                (by clear * - hbat_eb hsr_bw_le hxk; omega) (Or.inl (by omega))]
              exact hfr_toMR (endBundleBase + endKey x) (Or.inl (by omega))
            refine ⟨?_, hmem_unch⟩
            rw [← hres_eq2, hstay_f x ((mem_edgeEnds _ _).mpr ((BundleState.mem_ends B b x).mp hx).1) hxr]
            exact ((BundleState.mem_ends B b x).mp hx).2
        · dsimp only [mergeSortContract] at hcS
          rw [hLperm_len] at hcS
          rw [htour_end.2.symm]
          have hlog_le : Nat.log 2 (m_b + 1) ≤ Nat.log 2 (2 * m_b + 1) := Nat.log_mono_right (by omega)
          have hsort_le : 200 * m_b * (Nat.log 2 (m_b + 1) + 1) ≤
              600 * m_b * (Nat.log 2 (2 * m_b + 1) + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
          have hmul_tot : (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * m_b + 1) + 1) + 920) * m_b =
              (2 * TS.mul * ordStoreLog eCap) * m_b + 600 * m_b * (Nat.log 2 (2 * m_b + 1) + 1) + 920 * m_b := by ring
          clear * - hcCopy hcS hcMR hcR hsr_len hsort_le hmul_tot
          omega
      · -- Branch 2 (`degB - m_b ≤ winLen`): delegate to `bundleStepEmitOneCandBranch2_runs`
        have hkept_le : (B_init.ends b).card - L_b.length ≤ winLen := by
          rw [← hB_ends_b]; change degB - m_b ≤ winLen; omega
        have hbr2 : ∀ (raw' by' : List (ℕ × List End)) (deg' : ℕ),
            raw' = rawByRootVRuns B_init B_init.edges src' b →
            by' = byRootVRuns B_init B_init.edges src' b →
            deg' = (B_init.ends b).card →
            ∃ hlt : maxRunIdx raw' < raw'.length,
              by' = (raw'[maxRunIdx raw']'hlt) ::
                (raw'.take (maxRunIdx raw') ++ raw'.drop (maxRunIdx raw' + 1)) ∧
              vRunsEndsLen (raw'.take (maxRunIdx raw')) + (raw'[maxRunIdx raw']'hlt).2.length +
                vRunsEndsLen (raw'.drop (maxRunIdx raw' + 1)) = deg' ∧
              deg' ≤ 2 * m_b ∧
              vRunsEndsLen (raw'.take (maxRunIdx raw')) + vRunsEndsLen (raw'.drop (maxRunIdx raw' + 1)) ≤ m_b := by
          rintro _ _ _ rfl rfl rfl
          exact byRootVRuns_branch2_eq hE_init_lt hval hrem_ne hrem_eq (by rw [← hB_ends_b]; exact hdeg_pos) hkept_le
        obtain ⟨hlt_best, hby_eq, hsplit_len, hdeg_le, hmoved_le⟩ :=
          hbr2 _ _ _ hraw_eq_init hvruns_eq_init (congrArg Finset.card hB_ends_b)
        have hsp_br2 : (hCur + 2 * m_b) + (6 + 2 * TS.querySpace) * m_b < 2 ^ w := by
          have hmul : (8 + 2 * TS.querySpace) * m_b = 2 * m_b + (6 + 2 * TS.querySpace) * m_b := by ring
          omega
        obtain ⟨stEnd, cBr2, txEnd, hEnd, addedWords, hrunBr2, hregsBr2, hr4End, hhEnd_lo, hhEnd_hi,
          hr21End, hr22End, haddW_le, haddU_le, hV_end, hrepEnd, hG_end, hbatEnd, hebEnd,
          htrEnd, htfEnd, hzfEnd, hfrBr2, hcBr2⟩ :=
          bundleStepEmitOneCandBranch2_runs (htour := htour) (ω := ω) (st₀ := stMR)
            (b := b) (nB := nB) (hCur := hCur + 2 * m_b) (m_b := m_b)
            hpPush hpErase hMergeSort hw16 htourH_w heCap_w hpk_w
            hprev_w hnext_w heb_w hp_w hbat_w hupd_w hsp_br2
            hV hb_lt hnb_cap hdeg_pos hdeg_le hlt_best hby_eq hsplit_len hmoved_le
            hsrc_lt hsrc_mem hsrc_uniq
            hprev_next hblk_prev hblk_next heb_prev heb_next heb_blk
            hbat_blk hbat_prev hbat_next hbat_eb (by omega)
            (by omega) (by omega) (by omega) (by omega)
            (htour_MR.1 htrep) (fun a ha => lt_of_lt_of_le (htfoot_lt a ha) (by omega))
            htfoot_disj_blk htfoot_disj_prev htfoot_disj_next htfoot_disj_eb htfoot_disj_bat
            hzero_MR hrep_MR hG₀ hbat_MR hw1
            ((hMR_orig 1 (by decide) (by decide)).trans hr1) hr4MR
            ((hMR_orig 6 (by decide) (by decide)).trans hr6)
            ((hMR_orig 7 (by decide) (by decide)).trans hr7)
            ((hMR_orig 8 (by decide) (by decide)).trans hr8)
            ((hMR_orig 9 (by decide) (by decide)).trans hr9)
            ((hMR_orig 10 (by decide) (by decide)).trans hr10)
            ((hMR_orig 11 (by decide) (by decide)).trans hr11)
            ((hMR_orig 20 (by decide) (by decide)).trans hr20)
            ((hMR_orig 21 (by decide) (by decide)).trans hr21)
            ((hMR_orig 22 (by decide) (by decide)).trans hr22)
            hr25MR hr26MR
        have hcondB : Runs w pProg ω sBranch
            stMR .normal stEnd (5 + cBr2 + 1) :=
          runs_cond_iff.mpr ⟨0, cBr2, by
            simp [Expr.eval, BinOp.eval, hr33MR, hr26MR, hr30MR, show degB - m_b < 2 ^ w by omega, hbr1, h0_w],
            by simpa using hrunBr2, by simp [Expr.size]⟩
        refine ⟨stEnd, _, txEnd, hEnd, addedWords, hpref_run hcondB,
          fun r hr h4 h21 h22 h23 => by
            rw [hregsBr2 r hr h4 h21 h22 h23, hMR_regs r (by omega) h4]
            simp [stA, r26, r25, show r ≠ 26 by omega, show r ≠ 25 by omega],
          hr4End, by omega,
          by have hmul : (8 + 2 * TS.querySpace) * m_b = 2 * m_b + (6 + 2 * TS.querySpace) * m_b := by ring
             omega,
          hr21End, hr22End, haddW_le, haddU_le, hV_end, hrepEnd, hG_end, hbatEnd,
          fun x hx => by
            rcases hebEnd x hx with h1 | ⟨h1, h2⟩
            · exact Or.inl h1
            · refine Or.inr ⟨h1, h2.trans (hfr_toMR (endBundleBase + endKey x) (Or.inl ?_))⟩
              have hxk : endKey x < 2 * eCap := by
                have := hE_lt x.1 ((BundleState.mem_ends B b x).mp hx).1
                rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
              omega,
          htrEnd,
          fun a ha => by rcases htfEnd a ha with h0 | ⟨h1, h2⟩; exact Or.inl h0; exact Or.inr ⟨by omega, h2⟩,
          hzfEnd,
          fun a hnf haBlk haE haBat haH =>
            (hfrBr2 a hnf haBlk haE haBat (by omega)).trans (hfr_toMR a (by omega)),
          ?_⟩
        dsimp only [mergeSortContract] at hcS
        rw [hLperm_len] at hcS
        rw [htour_MR.2.symm] at hcBr2
        have hlog_le : Nat.log 2 (m_b + 1) ≤ Nat.log 2 (2 * m_b + 1) := Nat.log_mono_right (by omega)
        have hsort_le : 200 * m_b * (Nat.log 2 (m_b + 1) + 1) ≤
            200 * m_b * (Nat.log 2 (2 * m_b + 1) + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have hmul_tot : (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * m_b + 1) + 1) + 920) * m_b =
            (2 * TS.mul * ordStoreLog eCap + 400 * (Nat.log 2 (2 * m_b + 1) + 1) + 820) * m_b +
            200 * m_b * (Nat.log 2 (2 * m_b + 1) + 1) + 100 * m_b := by ring
        clear * - hcCopy hcS hcMR hcBr2 hsort_le hmul_tot
        omega

end

end MinCostFlow.SparseCore.Program
