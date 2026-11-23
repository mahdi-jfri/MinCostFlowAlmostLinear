module

public import MinCostFlow.SparseCore.Program.CompSplitListBranchPrep
import WordRAM.Tactic

/-!
# Per-Branch Canonical Split-List Emitter: Phase 2 (`CompSplitListBranchPhase2`)

Verifies `compEmitPhase2Stmt` (`compEmitPhase2_runs`): optional input-split pair union,
storing `spCnt + step.length`, clearing `isNew`, cleaning the Reverse Union-Find, and zeroing
`dBuf`, `sortScr`, `tmp2`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Phase 2 verification (`compEmitPhase2_runs`) -/

set_option maxHeartbeats 1200000 in
/-- Verifies `compEmitPhase2Stmt`: conditionally emits the input delete/split entry at
`spBufJ + 4 * spCnt`, updates `spCntAddr`, clears all `ufEmitScratchSize x1.vCap` scratch cells
back to zero, and returns `0`. -/
theorem compEmitPhase2_runs {W : LSFWindowImpl}
    {w k b bZero bRootVal bUFInitFind bUFPairUnion bUFClean
      rootsPtr fDelPtr oldC tag delE x0 y0 spBufJ spCntAddr ufBase spCnt : ℕ}
    {S : CompLSFFamily k} {x1 : CompLSFMeta k} {touched1 : List ℕ} {u : Update}
    {cuts1 : List (ℕ × ℕ)} {U_end : RevUFState} {act_end : List ℕ}
    {p : Program} {ω : ℕ → Bool} {s14 : State} (j : Fin k)
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpRootVal : p.procs[bRootVal]? = some compRootValProc)
    (hpInitFind : p.procs[bUFInitFind]? = some compUFInitFindProc)
    (hpPairUnion : p.procs[bUFPairUnion]? = some compUFPairUnionProc)
    (hpClean : p.procs[bUFClean]? = some compUFCleanProc)
    (hw16 : 16 ≤ 2 ^ w)
    (hrep0 : ∃ ℓ₀, CompLSFInv W.C_lsst ℓ₀ (S j))
    (hu_val : (S j).G.UpdateIsValid u)
    (hrep1 : CompLSFRepDirty W k b (fun i => compLSFStepSingle (S i) u) x1 touched1 s14.mem)
    (hend_le_rts : x1.endAddr ≤ rootsPtr)
    (hrts_le_fdel : rootsPtr + oldC + cuts1.length ≤ fDelPtr)
    (hfdel_le_sp : fDelPtr + oldC + cuts1.length ≤ spBufJ)
    (hsp_le_cnt : spBufJ + 4 * x1.vCap ≤ spCntAddr)
    (hcnt_lt_uf : spCntAddr + 1 ≤ ufBase)
    (huf_w : ufBase + ufEmitScratchSize x1.vCap < 2 ^ w)
    (hargs_w : tag < 2 ^ w ∧ delE < 2 ^ w ∧ x0 < 2 ^ w ∧ y0 < 2 ^ w)
    (hcut_setR : (cuts1.map Prod.snd).toFinset ∪
        (match u with | .split _ v' _ _ => {v'} | _ => ∅) =
      (compLSFStepSingle (S j) u).RF.R \ (S j).RF.R)
    (hcut_r_lt : ∀ q ∈ cuts1, q.2 < x1.vCap)
    (hcut_m : ∀ i (hi : i < cuts1.length),
      s14.mem (rootsPtr + (oldC + i)) = cuts1[i].2)
    (htag_spec : match u with
      | .insert _ _ _ => tag = 0
      | .delete e => tag = 1 ∧ delE = e ∧
          (e ∈ (S j).RF.F.E → x0 = (S j).G.tail e ∧ y0 = (S j).G.head e)
      | .split v v' _ _ => 2 ≤ tag ∧ x0 = v ∧ y0 = v')
    (hspCnt_bd : spCnt + (canonStepSplits (S j) u).length ≤ x1.vCap)
    (hU_end : RevUFInv (forestAfterInput (S j).RF.F u) (compLSFStepSingle (S j) u).RF (S j).RF.R U_end)
    (hMem_end : RevUFMemAt s14.mem ufBase x1.vCap
      (fun v => decide (v ∈ (compLSFStepSingle (S j) u).RF.R \ (S j).RF.R)) U_end act_end)
    (hact_end : act_end.length ≤ 2 * ((forestAfterInput (S j).RF.F u).E \ (compLSFStepSingle (S j) u).RF.F.E).card)
    (hrels14 : ∀ idx (hidx : idx < (((forestAfterInput (S j).RF.F u).E \ (compLSFStepSingle (S j) u).RF.F.E).sort (· ≤ ·)).length),
      let D_s := ((forestAfterInput (S j).RF.F u).E \ (compLSFStepSingle (S j) u).RF.F.E).sort (· ≤ ·)
      let e := (releasesSplitEntries (compLSFStepSingle (S j) u).RF.R (inputMid (S j) u) D_s)[idx]'(by rw [releasesSplitEntries_length]; exact hidx)
      let hasInp := (inputSplitEntries (S j) u).length
      s14.mem (spBufJ + 4 * (spCnt + hasInp + idx)) = (if e.isRelease then 1 else 0) ∧
      s14.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 1) = e.edge ∧
      s14.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 2) = e.kept ∧
      s14.mem (spBufJ + 4 * (spCnt + hasInp + idx) + 3) = e.fresh)
    (hz_dBuf_tail : ∀ a, ufBase + 6 * x1.vCap + 1 +
      ((forestAfterInput (S j).RF.F u).E \ (compLSFStepSingle (S j) u).RF.F.E).card ≤ a →
      a < ufBase + 7 * x1.vCap + 1 → s14.mem a = 0)
    (hz_sort_tail : ∀ a, ufBase + 7 * x1.vCap + 1 +
      ((forestAfterInput (S j).RF.F u).E \ (compLSFStepSingle (S j) u).RF.F.E).card ≤ a →
      a < ufBase + 8 * x1.vCap + 1 → s14.mem a = 0)
    (hregs : s14.regs 0 = b ∧ s14.regs 1 = j.1 ∧ s14.regs 2 = rootsPtr ∧ s14.regs 4 = oldC ∧
      s14.regs 5 = oldC + cuts1.length ∧ s14.regs 6 = tag ∧ s14.regs 8 = x0 ∧ s14.regs 9 = y0 ∧
      s14.regs 10 = spBufJ ∧ s14.regs 11 = spCntAddr ∧ s14.regs 12 = ufBase ∧ s14.regs 13 = x1.vCap ∧
      s14.regs 15 = ufBase + 6 * x1.vCap + 1 ∧ s14.regs 16 = ufBase + 7 * x1.vCap + 1 ∧
      s14.regs 17 = ufBase + 8 * x1.vCap + 1 ∧
      s14.regs 18 = ((forestAfterInput (S j).RF.F u).E \ (compLSFStepSingle (S j) u).RF.F.E).card ∧
      s14.regs 19 = (inputSplitEntries (S j) u).length ∧ s14.regs 24 = spCnt) :
    let step := canonStepSplits (S j) u
    let t := ((forestAfterInput (S j).RF.F u).E \ (compLSFStepSingle (S j) u).RF.F.E).card
    let hasInp := (inputSplitEntries (S j) u).length
    ∃ s24 c2,
      Runs w p ω (compEmitPhase2Stmt bZero bRootVal bUFInitFind bUFPairUnion bUFClean)
        s14 (.returned 0) s24 c2 ∧
      s24.mem spCntAddr = spCnt + step.length ∧
      (∀ idx (hidx : idx < step.length),
        let e := step[idx]
        s24.mem (spBufJ + 4 * (spCnt + idx)) = (if e.isRelease then 1 else 0) ∧
        s24.mem (spBufJ + 4 * (spCnt + idx) + 1) = e.edge ∧
        s24.mem (spBufJ + 4 * (spCnt + idx) + 2) = e.kept ∧
        s24.mem (spBufJ + 4 * (spCnt + idx) + 3) = e.fresh) ∧
      (∀ a, ufBase ≤ a → a < ufBase + ufEmitScratchSize x1.vCap → s24.mem a = 0) ∧
      (∀ a, a ≠ spCntAddr →
        (a < spBufJ + 4 * spCnt ∨ spBufJ + 4 * (spCnt + hasInp) ≤ a) →
        (a < ufBase ∨ ufBase + ufEmitScratchSize x1.vCap ≤ a) → s24.mem a = s14.mem a) ∧
      c2 ≤ (if hasInp = 0 then 5 else 40 * Nat.log 2 (2 * t + 2) + 720) +
        25 * cuts1.length + 140 * t + 240 := by
  classical
  intro step t hasInp
  obtain ⟨ℓ₀, hIj⟩ := hrep0
  let cs1 := compLSFStepSingle (S j) u
  let RF0 := (S j).RF
  let RF' := cs1.RF
  let F_mid := forestAfterInput RF0.F u
  let D_sorted := (F_mid.E \ RF'.F.E).sort (· ≤ ·)
  let isNew : ℕ → Bool := fun v => decide (v ∈ RF'.R \ RF0.R)
  have hI1 : CompLSFInv W.C_lsst ℓ₀ cs1 := compLSFBatch_inv (U := [u]) hIj ⟨hu_val, trivial⟩
  have hRF0 : RF0.IsRootedSpanningForestOf (S j).G := compLSF_RF_isRSF hIj
  have hRF' : RF'.IsRootedSpanningForestOf cs1.G := compLSF_RF_isRSF hI1
  have hdec := compLSFBatch_decremental (U := [u]) hIj ⟨hu_val, trivial⟩
  have hR_old_sub : RF0.R ⊆ RF'.R := hdec.2
  have hD_sorted_len : D_sorted.length = t := Finset.length_sort _
  have hstep_len : step.length = hasInp + t := by
    simp only [step, canonStepSplits, List.length_append, releasesSplitEntries_length, Finset.length_sort, hasInp, t]
  have hrep1_orig := hrep1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨ℓ₁, hBr1⟩, _, hT1, _⟩ := hrep1
  have hG_j := (hBr1 j).2.2.1
  have hR_lt : ∀ r ∈ RF'.R, r < x1.vCap := fun r hr => hT1.hVlt r (hG_j ▸ hRF'.2.2.1 hr)
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have huf_sz : ufEmitScratchSize x1.vCap = 8 * x1.vCap + 3 := rfl
  have huf_scr : ufScratchSize x1.vCap = 6 * x1.vCap + 1 := rfl
  set dBuf := ufBase + 6 * x1.vCap + 1
  set sortScr := ufBase + 7 * x1.vCap + 1
  set tmp2 := ufBase + 8 * x1.vCap + 1
  have ⟨hr0, hr1, hr2, hr4, hr5, hr6, hr8, hr9, hr10, hr11, hr12, hr13, hr15, hr16, hr17, hr18, hr19, hr24⟩ := hregs
  have hr18' : s14.regs 18 = t := hr18
  have hr19' : s14.regs 19 = hasInp := hr19
  have hspCnt_bd' : spCnt + step.length ≤ x1.vCap := hspCnt_bd
  have hact_end' : act_end.length ≤ 2 * t := hact_end
  have hhasInp_le1 : hasInp ≤ 1 := by
    dsimp only [hasInp]
    cases u with
    | insert _ _ _ => simp [inputSplitEntries]
    | delete e => by_cases he : e ∈ (S j).RF.F.E <;> simp [inputSplitEntries, he]
    | split _ _ _ _ => simp [inputSplitEntries]
  -- Step 1: Conditional input-split emission (`cond r19`)
  have hinp_branch : ∃ s15 cInp U_inp act_inp,
      Runs w p ω
        (.cond (.reg 19)
          (.call 22 bRootVal [.reg 0, .reg 1, .reg 8] ;;
           .call 23 bRootVal [.reg 0, .reg 1, .reg 9] ;;
           .call 25 bUFInitFind [.reg 12, .reg 13, .reg 22] ;;
           .call 26 bUFInitFind [.reg 12, .reg 13, .reg 23] ;;
           .assign 27 (.bin .add (.reg 10) (.bin .mul (.const 4) (.reg 24))) ;;
           .call 23 bUFPairUnion [.reg 12, .reg 13, .reg 25, .reg 26, .reg 27, .const 0, .const 0, .const 0])
          .nop)
        s14 .normal s15 cInp ∧
      (∀ r < 20, s15.regs r = s14.regs r) ∧ s15.regs 24 = spCnt ∧
      RevUFMemAt s15.mem ufBase x1.vCap isNew U_inp act_inp ∧
      act_inp.length ≤ 2 * t + 2 ∧
      (∀ idx (hidx : idx < step.length),
        let e := step[idx]
        s15.mem (spBufJ + 4 * (spCnt + idx)) = (if e.isRelease then 1 else 0) ∧
        s15.mem (spBufJ + 4 * (spCnt + idx) + 1) = e.edge ∧
        s15.mem (spBufJ + 4 * (spCnt + idx) + 2) = e.kept ∧
        s15.mem (spBufJ + 4 * (spCnt + idx) + 3) = e.fresh) ∧
      (∀ a, (a < spBufJ + 4 * spCnt ∨ spBufJ + 4 * (spCnt + hasInp) ≤ a) →
        (a < ufBase + x1.vCap ∨ ufBase + ufScratchSize x1.vCap ≤ a) → s15.mem a = s14.mem a) ∧
      cInp ≤ (if hasInp = 0 then 5 else 40 * Nat.log 2 (2 * t + 2) + 720) := by
    by_cases hhi0 : hasInp = 0
    · have hinp_nil : inputSplitEntries (S j) u = [] := List.eq_nil_of_length_eq_zero hhi0
      refine ⟨s14, 3, U_end, act_end, runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, hr19', hhi0],
        by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
        fun _ _ => rfl, hr24, hMem_end, by omega, fun idx hidx => ?_, fun _ _ _ => rfl, by simp [hhi0]⟩
      have hstep_eq : step = releasesSplitEntries RF'.R (inputMid (S j) u) D_sorted := by
        dsimp only [step, canonStepSplits, RF', D_sorted, F_mid, RF0]
        rw [hinp_nil, List.nil_append]
      have hidx_D : idx < D_sorted.length := by omega
      have hrel := hrels14 idx hidx_D
      have hhi0' : (inputSplitEntries (S j) u).length = 0 := hhi0
      simp only [hhi0', Nat.add_zero] at hrel
      simpa only [hstep_eq] using hrel
    · have hhi1 : hasInp = 1 := by omega
      have hxy_in_G1 : x0 ∈ cs1.G.V ∧ y0 ∈ cs1.G.V := by
        dsimp only [hasInp] at hhi0
        cases u with
        | insert _ _ _ => simp [inputSplitEntries] at hhi0
        | delete e0 =>
          have heF : e0 ∈ (S j).RF.F.E := by
            by_contra hn; simp [inputSplitEntries, hn] at hhi0
          have ⟨hx, hy⟩ := htag_spec.2.2 heF
          have heG0 := (compLSF_F_edge_orig hIj heF).1
          exact ⟨by rw [hx]; exact (hIj.hG_val e0 heG0).1, by rw [hy]; exact (hIj.hG_val e0 heG0).2⟩
        | split v v' At Ah =>
          have ⟨_, hx, hy⟩ := htag_spec
          exact ⟨by rw [hx]; exact Finset.mem_insert_of_mem hu_val.1,
                 by rw [hy]; exact Finset.mem_insert_self _ _⟩
      obtain ⟨sR1, cR1, hrunR1, hmR1, hcR1⟩ :=
        compRootVal_runs (p := p) (pos := s14.pos) (ω := ω) j hw16 hrep1_orig (by omega) hxy_in_G1.1
      let q1 : State := { s14 with regs := Function.update s14.regs 22 (RF'.root x0), mem := sR1.mem, pos := sR1.pos }
      have hq1 : Runs w p ω (.call 22 bRootVal [.reg 0, .reg 1, .reg 8]) s14 .normal q1 (cR1 + 4) :=
        runs_call_iff.mpr ⟨[b, j.1, x0], _, .returned (RF'.root x0), sR1, cR1,
          by simp [evalArgs, Expr.eval, hr0, hr1, hr8], hpRootVal, hrunR1, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      have hrep1_q1 : CompLSFRepDirty W k b (fun i => compLSFStepSingle (S i) u) x1 touched1 q1.mem := by
        dsimp only [q1]; rwa [hmR1]
      obtain ⟨sR2, cR2, hrunR2, hmR2, hcR2⟩ :=
        compRootVal_runs (p := p) (pos := q1.pos) (ω := ω) j hw16 hrep1_q1 (by omega) hxy_in_G1.2
      let q2 : State := { q1 with regs := Function.update q1.regs 23 (RF'.root y0), mem := sR2.mem, pos := sR2.pos }
      have hq2 : Runs w p ω (.call 23 bRootVal [.reg 0, .reg 1, .reg 9]) q1 .normal q2 (cR2 + 4) :=
        runs_call_iff.mpr ⟨[b, j.1, y0], _, .returned (RF'.root y0), sR2, cR2,
          by simp [evalArgs, Expr.eval, q1, hr0, hr1, hr9], hpRootVal, hrunR2, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      have hMem_q2 : RevUFMemAt q2.mem ufBase x1.vCap isNew U_end act_end := by
        dsimp only [q2]; rw [hmR2, hmR1]; exact hMem_end
      have hRF'V_mid : ∀ r ∈ RF'.R, r ∈ F_mid.V := fun r hr => by
        have hV0 := hRF0.2.1
        have hVm : F_mid.V = cs1.G.V := by
          cases u <;> simp [F_mid, forestAfterInput, eraseForestEdge, cs1, compLSFStepSingle, MGraph.applyUpdate, hV0]
        rw [hVm]; exact hRF'.2.2.1 hr
      have hrx_R : RF'.root x0 ∈ RF'.R := (rootedForest_root_spec hRF' hxy_in_G1.1).1
      have hry_R : RF'.root y0 ∈ RF'.R := (rootedForest_root_spec hRF' hxy_in_G1.2).1
      have hisNew_iff : ∀ r ∈ RF'.R, isNew r = false ↔ r ∈ RF0.R := fun r hr => by simp [isNew, hr]
      obtain ⟨ra, sIF1, cIF1, hrunIF1, hU_i1, hMem_i1, hraR, hraAct, hraPar, hraConn, hfrIF1, hcIF1⟩ :=
        compUFInitFind_runs (p := p) (pos := q2.pos) (ω := ω) hw16 (by omega) hR_lt hR_old_sub
          hRF'V_mid hisNew_iff hU_end hMem_q2 hrx_R
      set U_i1 := ufInitOne (fun z => !isNew z) U_end (RF'.root x0)
      set act_i1 := if U_end.sz (RF'.root x0) = 0 then act_end ++ [RF'.root x0] else act_end
      let q3 : State := { q2 with regs := Function.update q2.regs 25 ra, mem := sIF1.mem, pos := sIF1.pos }
      have hq3 : Runs w p ω (.call 25 bUFInitFind [.reg 12, .reg 13, .reg 22]) q2 .normal q3 (cIF1 + 4) :=
        runs_call_iff.mpr ⟨[ufBase, x1.vCap, RF'.root x0], _, .returned ra, sIF1, cIF1,
          by simp [evalArgs, Expr.eval, q2, q1, hr12, hr13], hpInitFind, hrunIF1, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      obtain ⟨rb, sIF2, cIF2, hrunIF2, hU_i2, hMem_i2, hrbR, hrbAct, hrbPar, hrbConn, hfrIF2, hcIF2⟩ :=
        compUFInitFind_runs (p := p) (pos := q3.pos) (ω := ω) hw16 (by omega) hR_lt hR_old_sub
          hRF'V_mid hisNew_iff hU_i1 hMem_i1 hry_R
      set U_i2 := ufInitOne (fun z => !isNew z) U_i1 (RF'.root y0)
      set act_i2 := if U_i1.sz (RF'.root y0) = 0 then act_i1 ++ [RF'.root y0] else act_i1
      let q4 : State := { q3 with regs := Function.update q3.regs 26 rb, mem := sIF2.mem, pos := sIF2.pos }
      have hq4 : Runs w p ω (.call 26 bUFInitFind [.reg 12, .reg 13, .reg 23]) q3 .normal q4 (cIF2 + 4) :=
        runs_call_iff.mpr ⟨[ufBase, x1.vCap, RF'.root y0], _, .returned rb, sIF2, cIF2,
          by simp [evalArgs, Expr.eval, q3, q2, q1, hr12, hr13], hpInitFind, hrunIF2, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      have ⟨hraAct2, hraPar2⟩ := ufInitOne_preserves_active (isOld := fun z => !isNew z) (r := RF'.root y0) hraAct
      set outSlot0 := spBufJ + 4 * spCnt
      let q5 : State := { q4 with regs := Function.update q4.regs 27 outSlot0 }
      have hq5 : Runs w p ω (.assign 27 (.bin .add (.reg 10) (.bin .mul (.const 4) (.reg 24)))) q4 .normal q5 6 :=
        runs_assign_iff.mpr ⟨outSlot0, by
          simp [q4, q3, q2, q1, Expr.eval, BinOp.eval, hr10, hr24, hw4, outSlot0,
            show 4 * spCnt < 2 ^ w by omega, show outSlot0 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hoA_w : U_i2.oldR ra < 2 ^ w := by
        have hmo := (hU_i2.hRootMeta ra hraR (hraAct2.symm ▸ hraAct) (hraPar2.symm ▸ hraPar)).2.2
        rw [hmo]; split_ifs with hne
        · have := hR_lt _ (hR_old_sub (Finset.mem_inter.mp (Finset.min'_mem _ hne)).2); omega
        · omega
      have hoB_w : U_i2.oldR rb < 2 ^ w := by
        have hmo := (hU_i2.hRootMeta rb hrbR hrbAct hrbPar).2.2
        rw [hmo]; split_ifs with hne
        · have := hR_lt _ (hR_old_sub (Finset.mem_inter.mp (Finset.min'_mem _ hne)).2); omega
        · omega
      obtain ⟨sPU0, cPU0, hrunPU0, hPU0_0, hPU0_1, hPU0_2, hPU0_3, hMem_i3, hfrPU0, hcPU0⟩ :=
        compUFPairUnion_runs (outSlot := outSlot0) (p := p) (pos := q5.pos) (ω := ω) hw16 (by omega)
          (by omega) (Or.inl (by omega)) hw0' hw0' hw0' (hR_lt ra hraR) (hR_lt rb hrbR) hoA_w hoB_w
          hMem_i2 (fun h => absurd rfl h)
      simp only [↓reduceIte] at hMem_i3
      let q6 : State := { q5 with regs := Function.update q5.regs 23 0, mem := sPU0.mem, pos := sPU0.pos }
      have hq6 : Runs w p ω (.call 23 bUFPairUnion
          [.reg 12, .reg 13, .reg 25, .reg 26, .reg 27, .const 0, .const 0, .const 0]) q5 .normal q6 (cPU0 + 9) :=
        runs_call_iff.mpr ⟨[ufBase, x1.vCap, ra, rb, outSlot0, 0, 0, 0], _, .returned 0, sPU0, cPU0,
          by simp [evalArgs, Expr.eval, q5, q4, q3, q2, q1, hr12, hr13, hw0'],
          hpPairUnion, hrunPU0, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      have hinp_eq : inputSplitEntries (S j) u = [⟨false, 0, (ufPair U_i2 ra rb).1, (ufPair U_i2 ra rb).2⟩] := by
        have hF_mid_subRF' := compEmit_F_mid_subRF' hIj hu_val
        dsimp only [hasInp] at hhi0
        cases u with
        | insert _ _ _ => simp [inputSplitEntries] at hhi0
        | delete e0 =>
          have heF : e0 ∈ (S j).RF.F.E := by
            by_contra hn; simp [inputSplitEntries, hn] at hhi0
          have ⟨hx, hy⟩ := htag_spec.2.2 heF
          have ho := compLSF_F_edge_orig hIj heF
          have hx' : x0 = (S j).RF.F.tail e0 := hx.trans ho.2.2.2.1.symm
          have hy' : y0 = (S j).RF.F.head e0 := hy.trans ho.2.2.2.2.symm
          rw [hx'] at hraConn; rw [hy'] at hrbConn
          have hp := revUFInv_input_delete hRF0 hRF' heF hF_mid_subRF' hR_old_sub hU_i2
            hraR (hraAct2.symm ▸ hraAct) (hraPar2.symm ▸ hraPar) hraConn hrbR hrbAct hrbPar hrbConn
          simp only [inputSplitEntries, inputMid, forestAfterInput, heF, ↓reduceIte]
          exact congrArg (fun p : ℕ × ℕ => ([⟨false, 0, p.1, p.2⟩] : List CompSplitEntry)) hp.symm
        | split v v' At Ah =>
          have ⟨_, hx, hy⟩ := htag_spec
          rw [hx] at hraConn; rw [hy] at hrbConn
          have hp := revUFInv_input_split hRF0 hu_val.1 hu_val.2.1 hRF' hF_mid_subRF' hR_old_sub hU_i2
            hraR (hraAct2.symm ▸ hraAct) (hraPar2.symm ▸ hraPar) hraConn hrbR hrbAct hrbPar hrbConn
          simp only [inputSplitEntries, inputMid, forestAfterInput]
          exact congrArg (fun p : ℕ × ℕ => ([⟨false, 0, p.1, p.2⟩] : List CompSplitEntry)) hp.symm
      have hq_fr : ∀ a, (a < outSlot0 ∨ outSlot0 + 4 ≤ a) →
          (a < ufBase + x1.vCap ∨ ufBase + ufScratchSize x1.vCap ≤ a) → q6.mem a = s14.mem a := fun a ha1 ha2 => by
        exact (hfrPU0 a ha1 (Or.inl rfl)).trans ((hfrIF2 a ha2).trans ((hfrIF1 a ha2).trans (by rw [hmR2, hmR1])))
      have hact_i1_le : act_i1.length ≤ act_end.length + 1 := by dsimp [act_i1]; split_ifs <;> simp
      have hact_i2_le : act_i2.length ≤ 2 * t + 2 := by
        have h2 : act_i2.length ≤ act_i1.length + 1 := by dsimp [act_i2]; split_ifs <;> simp
        omega
      have p5 := runs_seq_iff.mpr (Or.inr ⟨q5, 6, cPU0 + 9, hq5, hq6, rfl⟩)
      have p4 := runs_seq_iff.mpr (Or.inr ⟨q4, cIF2 + 4, _, hq4, p5, rfl⟩)
      have p3 := runs_seq_iff.mpr (Or.inr ⟨q3, cIF1 + 4, _, hq3, p4, rfl⟩)
      have p2 := runs_seq_iff.mpr (Or.inr ⟨q2, cR2 + 4, _, hq2, p3, rfl⟩)
      have hbodyI := runs_seq_iff.mpr (Or.inr ⟨q1, cR1 + 4, _, hq1, p2, rfl⟩)
      have hcondI : Runs w p ω
          (.cond (.reg 19)
            (.call 22 bRootVal [.reg 0, .reg 1, .reg 8] ;;
             .call 23 bRootVal [.reg 0, .reg 1, .reg 9] ;;
             .call 25 bUFInitFind [.reg 12, .reg 13, .reg 22] ;;
             .call 26 bUFInitFind [.reg 12, .reg 13, .reg 23] ;;
             .assign 27 (.bin .add (.reg 10) (.bin .mul (.const 4) (.reg 24))) ;;
             .call 23 bUFPairUnion [.reg 12, .reg 13, .reg 25, .reg 26, .reg 27, .const 0, .const 0, .const 0])
            .nop) s14 .normal q6
          ((cR1 + 4 + (cR2 + 4 + (cIF1 + 4 + (cIF2 + 4 + (6 + (cPU0 + 9) + 1) + 1) + 1) + 1) + 1) + 2) :=
        runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, hr19', hhi1],
          by simp only [one_ne_zero, ↓reduceIte]; exact hbodyI, by simp [Expr.size]; omega⟩
      have hlog_i1 : Nat.log 2 act_i1.length ≤ Nat.log 2 (2 * t + 2) := Nat.log_mono_right (by omega)
      have hlog_i2 : Nat.log 2 act_i2.length ≤ Nat.log 2 (2 * t + 2) := Nat.log_mono_right (by omega)
      refine ⟨q6, _, U_i2, act_i2, hcondI,
        fun r hr => by simp [q6, q5, q4, q3, q2, q1, show r ≠ 22 by omega, show r ≠ 23 by omega,
          show r ≠ 25 by omega, show r ≠ 26 by omega, show r ≠ 27 by omega],
        by simp [q6, q5, q4, q3, q2, q1, hr24], hMem_i3, hact_i2_le, fun idx hidx => ?_,
        fun a ha1 ha2 => hq_fr a (by dsimp [outSlot0]; omega) ha2, by simp [hhi0]; omega⟩
      have hstep_cons : step = ⟨false, 0, (ufPair U_i2 ra rb).1, (ufPair U_i2 ra rb).2⟩ ::
          releasesSplitEntries RF'.R (inputMid (S j) u) D_sorted := by
        dsimp only [step, canonStepSplits, RF', D_sorted, F_mid, RF0]
        rw [hinp_eq, List.cons_append, List.nil_append]
      cases idx with
      | zero =>
        simp only [hstep_cons, List.getElem_cons_zero, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact ⟨hPU0_0, hPU0_1, hPU0_2, hPU0_3⟩
      | succ idx' =>
        have hidx'_lt : idx' < D_sorted.length := by omega
        have hrel := hrels14 idx' hidx'_lt
        simp only [hstep_cons, List.getElem_cons_succ]
        have hhi1' : (inputSplitEntries (S j) u).length = 1 := hhi1
        have haddr_eq : spBufJ + 4 * (spCnt + (idx' + 1)) =
            spBufJ + 4 * (spCnt + (inputSplitEntries (S j) u).length + idx') := by rw [hhi1']; omega
        rw [haddr_eq]
        exact ⟨(hq_fr _ (Or.inr (by dsimp [outSlot0]; omega)) (Or.inl (by omega))).trans hrel.1,
          (hq_fr _ (Or.inr (by dsimp [outSlot0]; omega)) (Or.inl (by omega))).trans hrel.2.1,
          (hq_fr _ (Or.inr (by dsimp [outSlot0]; omega)) (Or.inl (by omega))).trans hrel.2.2.1,
          (hq_fr _ (Or.inr (by dsimp [outSlot0]; omega)) (Or.inl (by omega))).trans hrel.2.2.2⟩
  obtain ⟨s15, cInp, U_inp, act_inp, hs15, hr15_o, hr15_24, hMem_inp, hact_inp, hstep15, hfr15, hcInp⟩ := hinp_branch
  -- Step 2: Store `spCnt + step.length`, unmark `isNew`, clean UF, zero `dBuf`/`sortScr`/`tmp2`, return `0`
  let s16 : State := { s15 with mem := Function.update s15.mem spCntAddr (spCnt + step.length) }
  let s17 : State := { s16 with regs := Function.update s16.regs 20 oldC }
  have hs16 : Runs w p ω (.store (.reg 11) (.bin .add (.bin .add (.reg 24) (.reg 19)) (.reg 18))) s15 .normal s16 7 :=
    runs_store_iff.mpr ⟨spCntAddr, spCnt + step.length,
      by simp [Expr.eval, hr15_o 11 (by omega), hr11],
      by simp [Expr.eval, BinOp.eval, hr15_24, hr15_o 19 (by omega), hr15_o 18 (by omega),
        hr19', hr18', hstep_len, show spCnt + hasInp < 2 ^ w by omega, show spCnt + hasInp + t < 2 ^ w by omega]; omega,
      rfl, rfl, by simp [Expr.size]⟩
  have hs17 : Runs w p ω (.assign 20 (.reg 4)) s16 .normal s17 2 :=
    runs_assign_iff.mpr ⟨oldC, by simp [s16, Expr.eval, hr15_o 4 (by omega), hr4], rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨s18, cUnm, hs18, hr18_o, hUnmZ, hfr18, hcUnm⟩ :=
    compUnmarkIsNew_runs (rootsPtr := rootsPtr) (oldC := oldC) (ufBase := ufBase)
      (p := p) (ω := ω) (st := s17) (cuts1 := cuts1) (vCap := x1.vCap)
      hw16 (by omega) (by omega) (Or.inl (by omega)) hcut_r_lt
      (fun i hi => by
        dsimp only [s17, s16]; rw [Function.update_of_ne (by omega)]
        exact (hfr15 _ (Or.inl (by omega)) (Or.inl (by omega))).trans (hcut_m i hi))
      (by simp [s17, s16, hr15_o 2 (by omega), hr2]) (by simp [s17, s16, hr15_o 5 (by omega), hr5])
      (by simp [s17, s16, hr15_o 12 (by omega), hr12]) (by simp [s17])
  -- Optional unmark of `y0` when `1 < tag`
  have hunm_y0 : ∃ s19 cUY,
      Runs w p ω (.cond (.bin .lt (.const 1) (.reg 6)) (.store (.bin .add (.reg 12) (.reg 9)) (.const 0)) .nop)
        s18 .normal s19 cUY ∧
      (∀ r < 20, s19.regs r = s18.regs r) ∧
      (∀ v < x1.vCap, s19.mem (ufBase + v) = 0) ∧
      (∀ a, a < ufBase ∨ ufBase + x1.vCap ≤ a → s19.mem a = s17.mem a) ∧ cUY ≤ 12 := by
    have hs17_is : ∀ v < x1.vCap, s17.mem (ufBase + v) = if isNew v then 1 else 0 := fun v hv => by
      dsimp only [s17, s16]; rw [Function.update_of_ne (by omega)]; exact hMem_inp.hIsNew v hv
    by_cases ht1 : 1 < tag
    · have hy0_lt : y0 < x1.vCap := by
        cases u with
        | insert _ _ _ => have := htag_spec; omega
        | delete _ => have := htag_spec.1; omega
        | split _ v' _ _ =>
          rw [htag_spec.2.2]; exact hT1.hVlt v' (hG_j ▸ by simp [compLSFStepSingle, MGraph.applyUpdate])
      let s19 : State := { s18 with mem := Function.update s18.mem (ufBase + y0) 0 }
      have hst : Runs w p ω (.store (.bin .add (.reg 12) (.reg 9)) (.const 0)) s18 .normal s19 5 :=
        runs_store_iff.mpr ⟨ufBase + y0, 0,
          by simp [Expr.eval, BinOp.eval, hr18_o 12 (by omega), hr18_o 9 (by omega), s17, s16,
            hr15_o 12 (by omega), hr15_o 9 (by omega), hr12, hr9, show ufBase + y0 < 2 ^ w by omega],
          by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
      refine ⟨s19, 9, runs_cond_iff.mpr ⟨1, 5,
        by simp [Expr.eval, BinOp.eval, hr18_o 6 (by omega), s17, s16, hr15_o 6 (by omega), hr6, hw1, ht1],
        by simp only [one_ne_zero, ↓reduceIte]; exact hst, by simp [Expr.size]⟩,
        fun _ _ => rfl, fun v hv => ?_, fun a ha => by
          dsimp only [s19]; rw [Function.update_of_ne (by omega)]
          exact hfr18 a fun r hr => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr; have := hcut_r_lt q hq; omega, by omega⟩
      dsimp only [s19]
      by_cases hvy : v = y0
      · subst hvy; simp
      · rw [Function.update_of_ne (by omega)]
        by_cases hc : v ∈ cuts1.map Prod.snd
        · exact hUnmZ v hc
        · rw [hfr18 (ufBase + v) (fun r hr heq => hc ((Nat.add_left_cancel heq).symm ▸ hr)), hs17_is v hv]
          have hnm : v ∉ RF'.R \ RF0.R := by
            rw [← hcut_setR, Finset.mem_union, List.mem_toFinset]
            cases u with
            | insert _ _ _ => have := htag_spec; omega
            | delete _ => have := htag_spec.1; omega
            | split _ v' _ _ => have hy := htag_spec.2.2; simp [hc, hy ▸ hvy]
          simp only [isNew, decide_eq_true_eq, hnm, ↓reduceIte]
    · refine ⟨s18, 5, runs_cond_iff.mpr ⟨0, 1,
        by simp [Expr.eval, BinOp.eval, hr18_o 6 (by omega), s17, s16, hr15_o 6 (by omega), hr6, hw1, ht1],
        by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
        fun _ _ => rfl, fun v hv => ?_,
        fun a ha => hfr18 a fun r hr => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr; have := hcut_r_lt q hq; omega, by omega⟩
      by_cases hc : v ∈ cuts1.map Prod.snd
      · exact hUnmZ v hc
      · rw [hfr18 (ufBase + v) (fun r hr heq => hc ((Nat.add_left_cancel heq).symm ▸ hr)), hs17_is v hv]
        have hnm : v ∉ RF'.R \ RF0.R := by
          rw [← hcut_setR, Finset.mem_union, List.mem_toFinset]
          cases u with
          | insert _ _ _ => simp [hc]
          | delete _ => simp [hc]
          | split _ _ _ _ => have := htag_spec.1; omega
        simp only [isNew, decide_eq_true_eq, hnm, ↓reduceIte]
  obtain ⟨s19, cUY, hs19, hr19_o, hIsZ19, hfr19, hcUY⟩ := hunm_y0
  have hact_inp_le_v : act_inp.length ≤ x1.vCap := by
    rw [← List.toFinset_card_of_nodup hMem_inp.hActNd]
    exact (Finset.card_le_card fun z hz => Finset.mem_range.mpr (hMem_inp.hActLt z (List.mem_toFinset.mp hz))).trans (by simp)
  have hMem_s19 : RevUFMemAt s19.mem ufBase x1.vCap (fun _ => false) U_inp act_inp := by
    have hfrA : ∀ a, ufBase + x1.vCap ≤ a → a < ufBase + ufScratchSize x1.vCap → s19.mem a = s15.mem a :=
      fun a ha1 _ => (hfr19 a (Or.inr ha1)).trans (by dsimp [s17, s16]; rw [Function.update_of_ne (by omega)])
    refine ⟨fun v hv => by simp [ufIsNewBase, hIsZ19 v hv], fun v hv => ?_, hMem_inp.hActNd, hMem_inp.hActLt,
      hMem_inp.hActIff, hMem_inp.hZeroRest,
      (hfrA _ (by dsimp [ufActLenAddr]; omega) (by dsimp [ufActLenAddr]; omega)).trans hMem_inp.hActLen,
      fun i hi => (hfrA _ (by dsimp [ufActBase]; omega) (by dsimp [ufActBase]; omega)).trans (hMem_inp.hActAt i hi),
      fun i hi1 hi2 => (hfrA _ (by dsimp [ufActBase]; omega) (by dsimp [ufActBase]; omega)).trans (hMem_inp.hActZero i hi1 hi2),
      hMem_inp.hRootSum⟩
    have ha := hMem_inp.hArrs v hv
    exact ⟨(hfrA _ (by dsimp [ufParBase]; omega) (by dsimp [ufParBase]; omega)).trans ha.1,
      (hfrA _ (by dsimp [ufSzBase]; omega) (by dsimp [ufSzBase]; omega)).trans ha.2.1,
      (hfrA _ (by dsimp [ufMinFBase]; omega) (by dsimp [ufMinFBase]; omega)).trans ha.2.2.1,
      (hfrA _ (by dsimp [ufOldRBase]; omega) (by dsimp [ufOldRBase]; omega)).trans ha.2.2.2⟩
  obtain ⟨sCl, cCl, hrunCl, hClZ, hClFr, hcCl⟩ :=
    compUFClean_runs (p := p) (pos := s19.pos) (ω := ω) hw16 (by omega) hMem_s19
  let s20 : State := { s19 with regs := Function.update s19.regs 23 0, mem := sCl.mem, pos := sCl.pos }
  have hs20 : Runs w p ω (.call 23 bUFClean [.reg 12, .reg 13]) s19 .normal s20 (cCl + 3) :=
    runs_call_iff.mpr ⟨[ufBase, x1.vCap], _, .returned 0, sCl, cCl,
      by simp [evalArgs, Expr.eval, hr19_o 12 (by omega), hr19_o 13 (by omega), hr18_o 12 (by omega),
        hr18_o 13 (by omega), s17, s16, hr15_o 12 (by omega), hr15_o 13 (by omega), hr12, hr13],
      hpClean, hrunCl, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  obtain ⟨oZ1, sZ1, cZ1, hrZ1, hoZ1, hZ1_post, hZ1_out, hcZ1⟩ :=
    compEmitZeroRange_call hpZero hw16 (ptr := dBuf) (len := t) (mem := s20.mem) (pos := s20.pos) (ω := ω) (by dsimp [dBuf]; omega)
  let s21 : State := { s20 with regs := Function.update s20.regs 23 0, mem := sZ1.mem, pos := sZ1.pos }
  have hs21 : Runs w p ω (.call 23 bZero [.reg 15, .reg 18]) s20 .normal s21 (2 + cZ1 + 1) :=
    runs_call_iff.mpr ⟨[dBuf, t], compZeroRangeProc, oZ1, sZ1, cZ1,
      by simp [evalArgs, Expr.eval, s20, hr19_o 15 (by omega), hr19_o 18 (by omega), hr18_o 15 (by omega),
        hr18_o 18 (by omega), s17, s16, hr15_o 15 (by omega), hr15_o 18 (by omega), hr15, hr18', dBuf],
      hpZero, hrZ1, rfl, by simp [s21, hoZ1], by simp [argsSize, Expr.size]⟩
  obtain ⟨oZ2, sZ2, cZ2, hrZ2, hoZ2, hZ2_post, hZ2_out, hcZ2⟩ :=
    compEmitZeroRange_call hpZero hw16 (ptr := sortScr) (len := t) (mem := s21.mem) (pos := s21.pos) (ω := ω) (by dsimp [sortScr]; omega)
  let s22 : State := { s21 with regs := Function.update s21.regs 23 0, mem := sZ2.mem, pos := sZ2.pos }
  have hs22 : Runs w p ω (.call 23 bZero [.reg 16, .reg 18]) s21 .normal s22 (2 + cZ2 + 1) :=
    runs_call_iff.mpr ⟨[sortScr, t], compZeroRangeProc, oZ2, sZ2, cZ2,
      by simp [evalArgs, Expr.eval, s21, s20, hr19_o 16 (by omega), hr19_o 18 (by omega), hr18_o 16 (by omega),
        hr18_o 18 (by omega), s17, s16, hr15_o 16 (by omega), hr15_o 18 (by omega), hr16, hr18', sortScr],
      hpZero, hrZ2, rfl, by simp [s22, hoZ2], by simp [argsSize, Expr.size]⟩
  let s23 : State := { s22 with mem := Function.update s22.mem tmp2 0 }
  let s24 : State := { s23 with mem := Function.update s23.mem (tmp2 + 1) 0 }
  have hr22_17 : s22.regs 17 = tmp2 := by
    simp [s22, s21, s20, hr19_o 17 (by omega), hr18_o 17 (by omega), s17, s16, hr15_o 17 (by omega), hr17, tmp2]
  have hs23 : Runs w p ω (.store (.reg 17) (.const 0)) s22 .normal s23 3 :=
    runs_store_iff.mpr ⟨tmp2, 0, by simp [Expr.eval, hr22_17], by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hs24 : Runs w p ω (.store (.bin .add (.reg 17) (.const 1)) (.const 0)) s23 .normal s24 5 :=
    runs_store_iff.mpr ⟨tmp2 + 1, 0, by simp [s23, Expr.eval, BinOp.eval, hr22_17, hw1, show tmp2 + 1 < 2 ^ w by omega],
      by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hret : Runs w p ω (.ret (.const 0)) s24 (.returned 0) s24 2 :=
    runs_ret_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hchain2 : Runs w p ω (compEmitPhase2Stmt bZero bRootVal bUFInitFind bUFPairUnion bUFClean)
      s14 (.returned 0) s24
      (cInp + (7 + (2 + (cUnm + (cUY + ((cCl + 3) + ((2 + cZ1 + 1) + ((2 + cZ2 + 1) + (3 + (5 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
    have k24 := runs_seq_iff.mpr (Or.inr ⟨s24, 5, 2, hs24, hret, rfl⟩)
    have k23 := runs_seq_iff.mpr (Or.inr ⟨s23, 3, _, hs23, k24, rfl⟩)
    have k22 := runs_seq_iff.mpr (Or.inr ⟨s22, 2 + cZ2 + 1, _, hs22, k23, rfl⟩)
    have k21 := runs_seq_iff.mpr (Or.inr ⟨s21, 2 + cZ1 + 1, _, hs21, k22, rfl⟩)
    have k20 := runs_seq_iff.mpr (Or.inr ⟨s20, cCl + 3, _, hs20, k21, rfl⟩)
    have k19 := runs_seq_iff.mpr (Or.inr ⟨s19, cUY, _, hs19, k20, rfl⟩)
    have k18 := runs_seq_iff.mpr (Or.inr ⟨s18, cUnm, _, hs18, k19, rfl⟩)
    have k17 := runs_seq_iff.mpr (Or.inr ⟨s17, 2, _, hs17, k18, rfl⟩)
    have k16 := runs_seq_iff.mpr (Or.inr ⟨s16, 7, _, hs16, k17, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s15, cInp, _, hs15, k16, rfl⟩)
  have hcl_out : ∀ a, a < ufBase ∨ ufBase + ufEmitScratchSize x1.vCap ≤ a → s24.mem a = s17.mem a := fun a ha => by
    dsimp only [s24, s23, s22, s21, s20]
    rw [Function.update_of_ne (by dsimp [tmp2]; omega), Function.update_of_ne (by dsimp [tmp2]; omega),
        hZ2_out a (by dsimp [sortScr]; omega), hZ1_out a (by dsimp [dBuf]; omega),
        hClFr a (by omega), hfr19 a (by omega)]
  refine ⟨s24, _, hchain2,
    (hcl_out spCntAddr (Or.inl (by omega))).trans (by simp [s17, s16]),
    fun idx hidx => by
      have hs15_i := hstep15 idx hidx
      have hcl_buf : ∀ off < 4, s24.mem (spBufJ + 4 * (spCnt + idx) + off) =
          s15.mem (spBufJ + 4 * (spCnt + idx) + off) := fun off hoff =>
        (hcl_out (spBufJ + 4 * (spCnt + idx) + off) (Or.inl (by omega))).trans
          (by dsimp [s17, s16]; rw [Function.update_of_ne (by omega)])
      have h0 := hcl_buf 0 (by omega); simp only [Nat.add_zero] at h0
      exact ⟨h0.trans hs15_i.1, (hcl_buf 1 (by omega)).trans hs15_i.2.1,
        (hcl_buf 2 (by omega)).trans hs15_i.2.2.1, (hcl_buf 3 (by omega)).trans hs15_i.2.2.2⟩,
    fun a ha1 ha2 => ?_,
    fun a h1 h2 h3 => (hcl_out a h3).trans (by dsimp [s17, s16]; rw [Function.update_of_ne h1]; exact hfr15 a h2 (by omega)),
    by omega⟩
  by_cases h1 : a < ufBase + x1.vCap
  · dsimp only [s24, s23, s22, s21, s20]
    rw [Function.update_of_ne (by dsimp [tmp2]; omega), Function.update_of_ne (by dsimp [tmp2]; omega),
        hZ2_out a (Or.inl (by dsimp [sortScr]; omega)), hZ1_out a (Or.inl (by dsimp [dBuf]; omega)),
        hClFr a (Or.inl (by omega))]
    have := hIsZ19 (a - ufBase) (by omega)
    rwa [show ufBase + (a - ufBase) = a by omega] at this
  · by_cases h2 : a < dBuf
    · dsimp only [s24, s23, s22, s21, s20]
      rw [Function.update_of_ne (by dsimp [tmp2, dBuf] at h2 ⊢; omega),
          Function.update_of_ne (by dsimp [tmp2, dBuf] at h2 ⊢; omega),
          hZ2_out a (Or.inl (by dsimp [sortScr, dBuf] at h2 ⊢; omega)),
          hZ1_out a (Or.inl h2)]
      exact hClZ a (by omega) (by dsimp [dBuf] at h2; omega)
    · by_cases h3 : a < sortScr
      · dsimp only [s24, s23, s22, s21]
        rw [Function.update_of_ne (by dsimp [tmp2, sortScr] at h3 ⊢; omega),
            Function.update_of_ne (by dsimp [tmp2, sortScr] at h3 ⊢; omega),
            hZ2_out a (Or.inl h3)]
        by_cases hlt : a < dBuf + t
        · have := hZ1_post (a - dBuf) (by omega)
          rwa [show dBuf + (a - dBuf) = a by omega] at this
        · rw [hZ1_out a (Or.inr (by omega))]
          dsimp only [s20]; rw [hClFr a (Or.inr (by dsimp [dBuf] at h2; omega)),
            hfr19 a (Or.inr (by dsimp [dBuf] at h2; omega))]
          dsimp only [s17, s16]; rw [Function.update_of_ne (by omega),
            hfr15 a (Or.inr (by omega)) (Or.inr (by dsimp [dBuf] at h2; omega))]
          exact hz_dBuf_tail a (by dsimp [dBuf] at hlt; omega) (by dsimp [sortScr] at h3; omega)
      · by_cases h4 : a < tmp2
        · dsimp only [s24, s23, s22]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          by_cases hlt : a < sortScr + t
          · have := hZ2_post (a - sortScr) (by omega)
            rwa [show sortScr + (a - sortScr) = a by omega] at this
          · rw [hZ2_out a (Or.inr (by omega))]
            dsimp only [s21]; rw [hZ1_out a (Or.inr (by dsimp [sortScr, dBuf] at h3 ⊢; omega))]
            dsimp only [s20]; rw [hClFr a (Or.inr (by dsimp [sortScr] at h3; omega)),
              hfr19 a (Or.inr (by dsimp [sortScr] at h3; omega))]
            dsimp only [s17, s16]; rw [Function.update_of_ne (by omega),
              hfr15 a (Or.inr (by omega)) (Or.inr (by dsimp [sortScr] at h3; omega))]
            exact hz_sort_tail a (by dsimp [sortScr] at hlt; omega) (by dsimp [tmp2] at h4; omega)
        · dsimp only [s24, s23]
          by_cases heq1 : a = tmp2 + 1
          · subst heq1; simp
          · rw [Function.update_of_ne heq1]
            have heq0 : a = tmp2 := by dsimp [tmp2] at ha2 h4 ⊢; omega
            subst heq0; simp


end

end MinCostFlow.SparseCore.Program
