module

public import MinCostFlow.SparseCore.Program.CompSplitListBranchPhase2
import MinCostFlow.SparseCore.Program.CompExportBase
import WordRAM.Tactic

/-!
# Per-Branch Canonical Split-List Emitter (`CompSplitListBranch`)

Top-level verification of `compEmitBranchSplitProc` (`compEmitBranchSplit_runs`), combining the
fast no-op path (`cuts1 = []` and `tag ≤ 1`), Phase 1 (`compEmitPhase1_runs`), and Phase 2
(`compEmitPhase2_runs`), with total cost `≤ 1500 * t * (Nat.log 2 (x1.m0Total + 2) + 1) + 1300`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section
/-! ## 2. Top-level verification (`compEmitBranchSplit_runs`) -/

set_option maxHeartbeats 800000 in
/-- Verification of `compEmitBranchSplitProc`: appends `canonStepSplits (S j) u` at
`spBufJ + 4 * spCnt`, increments `spCntAddr` by `(canonStepSplits (S j) u).length`, zeroes the
entire `ufEmitScratchSize x1.vCap` scratch region, preserves all other memory, and costs
`≤ 1500 * t * (Nat.log 2 (x1.m0Total + 2) + 1) + 1300`. -/
theorem compEmitBranchSplit_runs {W : LSFWindowImpl}
    {w k b bZero bSort bRootVal bEndRoots bUFInitFind bUFPairUnion bUFClean
      rootsPtr fDelPtr oldC tag delE x0 y0 spBufJ spCntAddr ufBase spCnt : ℕ}
    {S : CompLSFFamily k} {x1 : CompLSFMeta k} {touched1 : List ℕ} {u : Update}
    {cuts1 : List (ℕ × ℕ)} {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool} (j : Fin k)
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hpRootVal : p.procs[bRootVal]? = some compRootValProc)
    (hpEndRoots : p.procs[bEndRoots]? = some compEdgeEndRootsProc)
    (hpInitFind : p.procs[bUFInitFind]? = some compUFInitFindProc)
    (hpPairUnion : p.procs[bUFPairUnion]? = some compUFPairUnionProc)
    (hpClean : p.procs[bUFClean]? = some compUFCleanProc)
    (hw16 : 16 ≤ 2 ^ w)
    (hrep0 : ∃ ℓ₀, CompLSFInv W.C_lsst ℓ₀ (S j))
    (hu_val : (S j).G.UpdateIsValid u)
    (hrep1 : CompLSFRepDirty W k b (fun i => compLSFStepSingle (S i) u) x1 touched1 mem)
    (hend_le_rts : x1.endAddr ≤ rootsPtr)
    (hrts_le_fdel : rootsPtr + oldC + cuts1.length ≤ fDelPtr)
    (hfdel_le_sp : fDelPtr + oldC + cuts1.length ≤ spBufJ)
    (hsp_le_cnt : spBufJ + 4 * x1.vCap ≤ spCntAddr)
    (hcnt_lt_uf : spCntAddr + 1 ≤ ufBase)
    (huf_w : ufBase + ufEmitScratchSize x1.vCap < 2 ^ w)
    (hargs_w : tag < 2 ^ w ∧ delE < 2 ^ w ∧ x0 < 2 ^ w ∧ y0 < 2 ^ w)
    (hcut_ndE : (cuts1.map Prod.fst).Nodup)
    (hcut_setE : (cuts1.map Prod.fst).toFinset = (S j).RF.F.E \ (compLSFStepSingle (S j) u).RF.F.E)
    (hcut_setR : (cuts1.map Prod.snd).toFinset ∪
        (match u with | .split _ v' _ _ => {v'} | _ => ∅) =
      (compLSFStepSingle (S j) u).RF.R \ (S j).RF.R)
    (hcut_r_lt : ∀ q ∈ cuts1, q.2 < x1.vCap)
    (hcut_m : ∀ i (hi : i < cuts1.length),
      mem (rootsPtr + (oldC + i)) = cuts1[i].2 ∧ mem (fDelPtr + (oldC + i)) = cuts1[i].1)
    (htag_spec : match u with
      | .insert _ _ _ => tag = 0
      | .delete e => tag = 1 ∧ delE = e ∧
          (e ∈ (S j).RF.F.E → x0 = (S j).G.tail e ∧ y0 = (S j).G.head e)
      | .split v v' _ _ => 2 ≤ tag ∧ x0 = v ∧ y0 = v')
    (hspCnt_m : mem spCntAddr = spCnt)
    (hspCnt_bd : spCnt + (canonStepSplits (S j) u).length ≤ x1.vCap)
    (huf_zero : ∀ a, ufBase ≤ a → a < ufBase + ufEmitScratchSize x1.vCap → mem a = 0) :
    let step := canonStepSplits (S j) u
    let t := ((forestAfterInput (S j).RF.F u).E \ (compLSFStepSingle (S j) u).RF.F.E).card
    ∃ st' c,
      Runs w p ω
        (compEmitBranchSplitProc bZero (bSort + sortIdxMergeSort) bRootVal bEndRoots
          bUFInitFind bUFPairUnion bUFClean)
        (startState [b, j.1, rootsPtr, fDelPtr, oldC, oldC + cuts1.length, tag, delE,
          x0, y0, spBufJ, spCntAddr, ufBase] mem pos)
        (.returned 0) st' c ∧
      st'.mem spCntAddr = spCnt + step.length ∧
      (∀ idx (hidx : idx < step.length),
        let e := step[idx]
        st'.mem (spBufJ + 4 * (spCnt + idx)) = (if e.isRelease then 1 else 0) ∧
        st'.mem (spBufJ + 4 * (spCnt + idx) + 1) = e.edge ∧
        st'.mem (spBufJ + 4 * (spCnt + idx) + 2) = e.kept ∧
        st'.mem (spBufJ + 4 * (spCnt + idx) + 3) = e.fresh) ∧
      (∀ a, ufBase ≤ a → a < ufBase + ufEmitScratchSize x1.vCap → st'.mem a = 0) ∧
      (∀ a, a ≠ spCntAddr →
        (a < spBufJ + 4 * spCnt ∨ spBufJ + 4 * (spCnt + step.length) ≤ a) →
        (a < ufBase ∨ ufBase + ufEmitScratchSize x1.vCap ≤ a) →
        st'.mem a = mem a) ∧
      c ≤ 1500 * t * (Nat.log 2 (x1.m0Total + 2) + 1) + 1300 := by
  classical
  intro step t
  obtain ⟨ℓ₀, hIj⟩ := hrep0
  let cs1 := compLSFStepSingle (S j) u
  let RF0 := (S j).RF
  let RF' := cs1.RF
  let F_mid := forestAfterInput RF0.F u
  let hasInp := (inputSplitEntries (S j) u).length
  have hI1 : CompLSFInv W.C_lsst ℓ₀ cs1 := compLSFBatch_inv (U := [u]) hIj ⟨hu_val, trivial⟩
  have hrep1_orig := hrep1
  obtain ⟨hk, _, _, _, _, _, _, _, _, hTE1, hhdr1, ⟨ℓ₁, hBr1⟩, hm0_eq, _, _⟩ := hrep1
  have hG0_j := (hBr1 j).2.1
  have hvCap_m : mem (b + compOffVCap) = x1.vCap := hhdr1.1
  have hstep_len : step.length = hasInp + t := by
    simp only [step, canonStepSplits, List.length_append, releasesSplitEntries_length, Finset.length_sort, hasInp, t]
  have ht_le_m0 : t ≤ x1.m0Total := by
    have hF0_le : RF0.F.m ≤ (S j).G₀.m := (compLSF_F_eq_edgeful hIj).2.2.2
    have hsub : F_mid.E \ RF'.F.E ⊆ RF0.F.E := fun e he => by
      have hm := (Finset.mem_sdiff.mp he).1
      cases u with
      | insert _ _ _ => exact hm
      | delete _ => exact (Finset.mem_erase.mp hm).2
      | split _ _ _ _ => exact hm
    have hG0_same : (S j).G₀ = cs1.G₀ := by cases u <;> rfl
    rw [hG0_same, hG0_j, hm0_eq] at hF0_le
    exact le_trans (Finset.card_le_card hsub) hF0_le
  have hcuts1_le : cuts1.length ≤ t + 1 := by
    cases u with
    | insert _ _ _ =>
      have hsub : (cuts1.map Prod.fst).toFinset = F_mid.E \ RF'.F.E := hcut_setE
      have := congrArg Finset.card hsub
      rw [List.toFinset_card_of_nodup hcut_ndE, List.length_map] at this
      change cuts1.length = t at this; omega
    | delete e0 =>
      have hsub : (cuts1.map Prod.fst).toFinset ⊆ insert e0 (F_mid.E \ RF'.F.E) := by
        intro e he; rw [hcut_setE, Finset.mem_sdiff] at he
        by_cases heq : e = e0
        · exact Finset.mem_insert.mpr (Or.inl heq)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr
            ⟨Finset.mem_erase.mpr ⟨heq, he.1⟩, he.2⟩))
      have hc := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup hcut_ndE, List.length_map] at hc
      exact le_trans hc (Finset.card_insert_le _ _)
    | split _ _ _ _ =>
      have hsub : (cuts1.map Prod.fst).toFinset = F_mid.E \ RF'.F.E := hcut_setE
      have := congrArg Finset.card hsub
      rw [List.toFinset_card_of_nodup hcut_ndE, List.length_map] at this
      change cuts1.length = t at this; omega
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have huf_sz : ufEmitScratchSize x1.vCap = 8 * x1.vCap + 3 := rfl
  have hb_hdr_lt : b + compHdrSize ≤ x1.endAddr := by
    have : b + compHdrSize ≤ compTablesEnd b x1.vCap x1.eCap x1.L_w x1.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
    omega
  set st0 := startState [b, j.1, rootsPtr, fDelPtr, oldC, oldC + cuts1.length, tag, delE,
    x0, y0, spBufJ, spCntAddr, ufBase] mem pos
  let st1 : State := { st0 with regs := Function.update st0.regs 13 x1.vCap }
  let st2 : State := { st1 with regs := Function.update st1.regs 14 cuts1.length }
  have hp1 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 0) (.const compOffVCap)))) st0 .normal st1 5 :=
    runs_assign_iff.mpr ⟨x1.vCap, Expr.eval_load_of_eq (by
      have h1 : compOffVCap < 2 ^ w ∧ b + compOffVCap < 2 ^ w := by
        dsimp only [compOffVCap, compHdrSize] at hb_hdr_lt ⊢; omega
      simp [st0, startState, Expr.eval, BinOp.eval, h1.1, h1.2]) hvCap_m, rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 14 (.bin .sub (.reg 5) (.reg 4))) st1 .normal st2 4 :=
    runs_assign_iff.mpr ⟨cuts1.length, by
      simp [st1, st0, startState, Expr.eval, BinOp.eval, show cuts1.length < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  set fastCond := cuts1.length + (if 1 < tag then 1 else 0)
  have hfc_w : fastCond < 2 ^ w := by dsimp [fastCond]; split_ifs <;> omega
  have hfc_eval : Expr.eval w st2 (.bin .add (.reg 14) (.bin .lt (.const 1) (.reg 6))) = some fastCond := by
    by_cases ht : 1 < tag
    · simp [st2, st1, st0, startState, Expr.eval, BinOp.eval, hw1, ht, fastCond,
        show cuts1.length + 1 < 2 ^ w by dsimp [fastCond] at hfc_w; simp [ht] at hfc_w; exact hfc_w]
    · simp [st2, st1, st0, startState, Expr.eval, BinOp.eval, hw1, ht, fastCond,
        show cuts1.length < 2 ^ w by omega]
  by_cases hfast : fastCond = 0
  · have hcuts0 : cuts1.length = 0 := by dsimp [fastCond] at hfast; omega
    have htag_le1 : ¬ 1 < tag := by dsimp [fastCond] at hfast; split_ifs at hfast <;> omega
    have hc_nil : cuts1 = [] := List.eq_nil_of_length_eq_zero hcuts0
    have hF_diff0 : RF0.F.E \ RF'.F.E = ∅ := by rw [← hcut_setE, hc_nil]; simp
    have ht0 : t = 0 := by
      have hsub : F_mid.E \ RF'.F.E ⊆ RF0.F.E \ RF'.F.E := fun e he => by
        have ⟨h1, h2⟩ := Finset.mem_sdiff.mp he
        refine Finset.mem_sdiff.mpr ⟨?_, h2⟩
        cases u with
        | insert _ _ _ => exact h1
        | delete _ => exact (Finset.mem_erase.mp h1).2
        | split _ _ _ _ => exact h1
      rw [hF_diff0, Finset.subset_empty] at hsub
      exact Finset.card_eq_zero.mpr hsub
    have hhi0 : hasInp = 0 := by
      dsimp only [hasInp]
      cases u with
      | insert _ _ _ => simp [inputSplitEntries]
      | delete e0 =>
        have hnotF : e0 ∉ RF0.F.E := fun he => by
          have he' : e0 ∉ RF'.F.E := fun h => by
            have := (compLSF_F_edge_orig hI1 h).1
            simp [cs1, compLSFStepSingle, MGraph.applyUpdate] at this
          have : e0 ∈ RF0.F.E \ RF'.F.E := Finset.mem_sdiff.mpr ⟨he, he'⟩
          rw [hF_diff0] at this; exact Finset.notMem_empty _ this
        simp [inputSplitEntries, show e0 ∉ (S j).RF.F.E from hnotF]
      | split _ _ _ _ => have := htag_spec.1; omega
    have hstep0 : step.length = 0 := by omega
    have hret : Runs w p ω (.ret (.const 0)) st2 (.returned 0) st2 2 :=
      runs_ret_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
    have hcond : Runs w p ω
        (.cond (.bin .add (.reg 14) (.bin .lt (.const 1) (.reg 6)))
          (compEmitPhase1Stmt (bSort + sortIdxMergeSort) bEndRoots bUFInitFind bUFPairUnion ;;
           compEmitPhase2Stmt bZero bRootVal bUFInitFind bUFPairUnion bUFClean)
          (.ret (.const 0))) st2 (.returned 0) st2 8 :=
      runs_cond_iff.mpr ⟨0, 2, by rw [hfc_eval, hfast], by simp only [↓reduceIte]; exact hret, by simp [Expr.size]⟩
    have hfull : Runs w p ω
        (compEmitBranchSplitProc bZero (bSort + sortIdxMergeSort) bRootVal bEndRoots
          bUFInitFind bUFPairUnion bUFClean) st0 (.returned 0) st2 (5 + (4 + 8 + 1) + 1) := by
      have q1 := runs_seq_iff.mpr (Or.inr ⟨st2, 4, 8, hp2, hcond, rfl⟩)
      exact runs_seq_iff.mpr (Or.inr ⟨st1, 5, _, hp1, q1, rfl⟩)
    exact ⟨st2, _, hfull, by simpa [st2, st1, st0, startState, hstep0] using hspCnt_m,
      fun _ h => by omega, huf_zero, fun _ _ _ _ => rfl, by omega⟩
  · -- Slow path: Phase 1 + Phase 2
    obtain ⟨s14, c1, U_end, act_end, hrun1, hr14_lt14, hr14_15, hr14_16, hr14_17, hr14_18, hr14_19, hr14_24,
      hU_end, hMem_end, hact_end, hrels14, hfr14, hz_dBuf, hz_sort, hc1⟩ :=
      compEmitPhase1_runs (bSort := bSort) (bEndRoots := bEndRoots) (bUFInitFind := bUFInitFind)
        (bUFPairUnion := bUFPairUnion) (st := st2) (ω := ω) j hpSort hpEndRoots hpInitFind hpPairUnion
        hw16 ⟨ℓ₀, hIj⟩ hu_val hrep1_orig hend_le_rts hrts_le_fdel hfdel_le_sp hsp_le_cnt hcnt_lt_uf
        huf_w hargs_w hcut_ndE hcut_setE (by cases u <;> exact hcut_setR) hcut_r_lt hcut_m htag_spec hspCnt_m hspCnt_bd huf_zero
        ⟨by simp [st2, st1, st0, startState], by simp [st2, st1, st0, startState],
         by simp [st2, st1, st0, startState], by simp [st2, st1, st0, startState],
         by simp [st2, st1, st0, startState], by simp [st2, st1, st0, startState],
         by simp [st2, st1, st0, startState], by simp [st2, st1, st0, startState],
         by simp [st2, st1, st0, startState], by simp [st2, st1, st0, startState],
         by simp [st2, st1, st0, startState], by simp [st2, st1, st0, startState],
         by simp [st2, st1, st0, startState], by simp [st2, st1]⟩
    have ht_eq : ((F_mid.E \ RF'.F.E).sort (· ≤ ·)).length = t := Finset.length_sort _
    rw [ht_eq] at hr14_18 hact_end hfr14 hz_dBuf hz_sort hc1
    have hrep1_s14 : CompLSFRepDirty W k b (fun i => compLSFStepSingle (S i) u) x1 touched1 s14.mem :=
      compLSFRepDirty_of_agree hrep1_orig fun a _ ha2 =>
        hfr14 a (Or.inl (by omega)) (Or.inl (by omega))
    obtain ⟨s24, c2, hrun2, hcnt24, hstep24, hufZ24, hfr24, hc2⟩ :=
      compEmitPhase2_runs (bZero := bZero) (bRootVal := bRootVal) (bUFInitFind := bUFInitFind)
        (bUFPairUnion := bUFPairUnion) (bUFClean := bUFClean) (s14 := s14) (ω := ω) j
        hpZero hpRootVal hpInitFind hpPairUnion hpClean hw16 ⟨ℓ₀, hIj⟩ hu_val hrep1_s14
        hend_le_rts hrts_le_fdel hfdel_le_sp hsp_le_cnt hcnt_lt_uf huf_w hargs_w
        (by cases u <;> exact hcut_setR) hcut_r_lt
        (fun i hi => (hfr14 _ (Or.inl (by omega)) (Or.inl (by omega))).trans (hcut_m i hi).1)
        htag_spec hspCnt_bd hU_end hMem_end hact_end hrels14 hz_dBuf hz_sort
        ⟨(hr14_lt14 0 (by omega)).trans (by simp [st2, st1, st0, startState]),
         (hr14_lt14 1 (by omega)).trans (by simp [st2, st1, st0, startState]),
         (hr14_lt14 2 (by omega)).trans (by simp [st2, st1, st0, startState]),
         (hr14_lt14 4 (by omega)).trans (by simp [st2, st1, st0, startState]),
         (hr14_lt14 5 (by omega)).trans (by simp [st2, st1, st0, startState]),
         (hr14_lt14 6 (by omega)).trans (by simp [st2, st1, st0, startState]),
         (hr14_lt14 8 (by omega)).trans (by simp [st2, st1, st0, startState]),
         (hr14_lt14 9 (by omega)).trans (by simp [st2, st1, st0, startState]),
         (hr14_lt14 10 (by omega)).trans (by simp [st2, st1, st0, startState]),
         (hr14_lt14 11 (by omega)).trans (by simp [st2, st1, st0, startState]),
         (hr14_lt14 12 (by omega)).trans (by simp [st2, st1, st0, startState]),
         (hr14_lt14 13 (by omega)).trans (by simp [st2, st1]),
         hr14_15, hr14_16, hr14_17, hr14_18, hr14_19, hr14_24⟩
    have hbody := runs_seq_iff.mpr (Or.inr ⟨s14, c1, c2, hrun1, hrun2, rfl⟩)
    have hcond_s : Runs w p ω
        (.cond (.bin .add (.reg 14) (.bin .lt (.const 1) (.reg 6)))
          (compEmitPhase1Stmt (bSort + sortIdxMergeSort) bEndRoots bUFInitFind bUFPairUnion ;;
           compEmitPhase2Stmt bZero bRootVal bUFInitFind bUFPairUnion bUFClean)
          (.ret (.const 0))) st2 (.returned 0) s24 (c1 + c2 + 1 + 6) :=
      runs_cond_iff.mpr ⟨fastCond, c1 + c2 + 1, hfc_eval,
        by simp only [hfast, ↓reduceIte]; exact hbody, by simp [Expr.size]; omega⟩
    have hfull : Runs w p ω
        (compEmitBranchSplitProc bZero (bSort + sortIdxMergeSort) bRootVal bEndRoots
          bUFInitFind bUFPairUnion bUFClean) st0 (.returned 0) s24
        (5 + (4 + (c1 + c2 + 1 + 6) + 1) + 1) := by
      have q2 := runs_seq_iff.mpr (Or.inr ⟨st2, 4, _, hp2, hcond_s, rfl⟩)
      exact runs_seq_iff.mpr (Or.inr ⟨st1, 5, _, hp1, q2, rfl⟩)
    -- Cost arithmetic
    have hlog_bd : Nat.log 2 (2 * t + 2) ≤ Nat.log 2 (x1.m0Total + 2) + 1 := log_2t_add2_le ht_le_m0
    have hlog1_bd : Nat.log 2 (t + 1) + 1 ≤ Nat.log 2 (x1.m0Total + 2) + 1 :=
      Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
    have hc1_bd : c1 ≤ 55 * (t + 1) + 200 * t * (Nat.log 2 (x1.m0Total + 2) + 1) + 65 +
        t * (40 * (Nat.log 2 (x1.m0Total + 2) + 1) + 820) + 120 := by
      have hA : (if t = 0 then 10 else 200 * t * (Nat.log 2 (t + 1) + 1) + 65) ≤
          200 * t * (Nat.log 2 (x1.m0Total + 2) + 1) + 65 := by
        split_ifs with ht0
        · omega
        · have := Nat.mul_le_mul_left (200 * t) hlog1_bd; omega
      have hB : t * (40 * Nat.log 2 (2 * t + 2) + 820) ≤
          t * (40 * (Nat.log 2 (x1.m0Total + 2) + 1) + 820) :=
        Nat.mul_le_mul_left t (by omega)
      omega
    have hc2_bd : c2 ≤ 40 * t * (Nat.log 2 (x1.m0Total + 2) + 1) + 760 +
        25 * (t + 1) + 140 * t + 240 := by
      have hc2' : c2 ≤ (if hasInp = 0 then 5 else 40 * Nat.log 2 (2 * t + 2) + 720) +
          25 * cuts1.length + 140 * t + 240 := hc2
      have hA : (if hasInp = 0 then 5 else 40 * Nat.log 2 (2 * t + 2) + 720) ≤
          40 * t * (Nat.log 2 (x1.m0Total + 2) + 1) + 760 := by
        split_ifs with hhi
        · omega
        · by_cases ht0 : t = 0
          · rw [ht0, show Nat.log 2 (2 * 0 + 2) = 1 by decide]; simp
          · have ht1 : 1 ≤ t := Nat.pos_of_ne_zero ht0
            have h1 : 40 * Nat.log 2 (2 * t + 2) ≤ 40 * (Nat.log 2 (x1.m0Total + 2) + 1) := by omega
            have h2 : 40 * (Nat.log 2 (x1.m0Total + 2) + 1) ≤ 40 * t * (Nat.log 2 (x1.m0Total + 2) + 1) :=
              Nat.mul_le_mul_right (Nat.log 2 (x1.m0Total + 2) + 1) (by omega)
            omega
      omega
    have hcost_final : 1100 * t + 280 * t * (Nat.log 2 (x1.m0Total + 2) + 1) ≤
        1500 * t * (Nat.log 2 (x1.m0Total + 2) + 1) := by
      have h1 : 1100 * t ≤ 1220 * t * (Nat.log 2 (x1.m0Total + 2) + 1) := by
        have := Nat.mul_le_mul_left (1220 * t) (show 1 ≤ Nat.log 2 (x1.m0Total + 2) + 1 by omega)
        omega
      have h2 : 1220 * t * (Nat.log 2 (x1.m0Total + 2) + 1) + 280 * t * (Nat.log 2 (x1.m0Total + 2) + 1) =
          1500 * t * (Nat.log 2 (x1.m0Total + 2) + 1) := by ring
      omega
    have hring : t * (40 * (Nat.log 2 (x1.m0Total + 2) + 1) + 820) =
        40 * t * (Nat.log 2 (x1.m0Total + 2) + 1) + 820 * t := by ring
    have hsum_L : 200 * t * (Nat.log 2 (x1.m0Total + 2) + 1) +
        40 * t * (Nat.log 2 (x1.m0Total + 2) + 1) +
        40 * t * (Nat.log 2 (x1.m0Total + 2) + 1) =
        280 * t * (Nat.log 2 (x1.m0Total + 2) + 1) := by ring
    exact ⟨s24, _, hfull, hcnt24, hstep24, hufZ24,
      fun a h1 h2 h3 => (hfr24 a h1 (by omega) h3).trans (hfr14 a (by omega) h3),
      by omega⟩

end

end MinCostFlow.SparseCore.Program
