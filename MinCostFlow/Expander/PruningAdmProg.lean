module

public import MinCostFlow.Expander.PruningFreezeProg

/-!
# Top-Level Prune Step Statement and Admissibility Check
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

/-! ### Section 8: Top-Level Single Step `pruneStepStmt` -/

def pruneStepStmt : Stmt :=
  .cond (.bin .lt (.const 0) (.reg prPeelTop))
    peelStepStmt
    (seqStmts
      [ .assign prU (.load (.bin .add (.reg prActStk) (.bin .sub (.reg prActTop) (.const 1))))
      , .assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prU)))
      , .assign prTmp2 (.load (.bin .add (.reg prEx) (.reg prU)))
      , .cond (.bin .eq (.bin .mul (.reg prTmp1) (.reg prTmp2)) (.const 0))
          popInactiveStepStmt
          (seqStmts
            [ .assign prTmp1 (.load (.bin .add (.reg prAbs) (.reg prU)))
            , .assign prTmp2 (.load (.bin .add (.reg prDegX) (.reg prU)))
            , .cond (.bin .lt (.reg prTmp1) (.reg prTmp2))
                absorbStepStmt
                (seqStmts
                  [ .assign prTmp1 (.load (.bin .add (.reg prCur) (.reg prU)))
                  , .assign prStart (.load (.bin .add (.reg prCsr) (.reg prU)))
                  , .assign prEnd (.load (.bin .add (.reg prCsr) (.bin .add (.reg prU) (.const 1))))
                  , .assign prTmp2 (.bin .sub (.reg prEnd) (.reg prStart))
                  , .cond (.bin .lt (.reg prTmp1) (.reg prTmp2))
                      (seqStmts
                        [ .assign prJ (.bin .add (.reg prStart) (.reg prTmp1))
                        , .assign prW (.load (.bin .add (.reg prCsrAdjV) (.reg prJ)))
                        , .assign prTmp3 (.load (.bin .add (.reg prCsrAdjH) (.reg prJ)))
                        , .assign prIdx (.bin .div (.reg prTmp3) (.const 2))
                        , .assign prDir (.bin .mod (.reg prTmp3) (.const 2))
                        , .assign prTmp3 (.load (.bin .add (.reg prFlowEnc) (.reg prIdx)))
                        , .cond (.bin .eq (.reg prDir) (.const 1))
                            (.assign prRc (.reg prTmp3))
                            (.assign prRc (.bin .sub (.bin .mul (.const 2) (.reg prCcap)) (.reg prTmp3)))
                        , .assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prW)))
                        , .assign prTmp2 (.load (.bin .add (.reg prHArr) (.reg prU)))
                        , .assign prTmp3 (.load (.bin .add (.reg prHArr) (.reg prW)))
                        , .cond (.bin .lt (.const 0) (.reg prRc))
                            (.assign prDelta (.const 1))
                            (.assign prDelta (.const 0))
                        , .assign prTmp1 (.bin .mul (.reg prTmp1) (.reg prDelta))
                        , .cond (.bin .lt (.const 0) (.reg prTmp2))
                            (.assign prDelta (.const 1))
                            (.assign prDelta (.const 0))
                        , .assign prTmp1 (.bin .mul (.reg prTmp1) (.reg prDelta))
                        , .cond (.bin .eq (.bin .sub (.reg prTmp2) (.const 1)) (.reg prTmp3))
                            (.assign prDelta (.const 1))
                            (.assign prDelta (.const 0))
                        , .assign prTmp1 (.bin .mul (.reg prTmp1) (.reg prDelta))
                        , .cond (.bin .eq (.reg prTmp1) (.const 1))
                            pushFlowStepStmt
                            advanceCurStepStmt ])
                      (seqStmts
                        [ .assign prTmp1 (.load (.bin .add (.reg prHArr) (.reg prU)))
                        , .cond (.bin .lt (.bin .add (.reg prTmp1) (.const 1)) (.reg prH))
                            relabelStepStmt
                            freezeStepStmt ]) ]) ]) ])

lemma pruneStepStmt_noRand : pruneStepStmt.NoRand := by
  dsimp [pruneStepStmt, seqStmts]
  repeat'
    first
    | exact peelStepStmt_noRand
    | exact popInactiveStepStmt_noRand
    | exact absorbStepStmt_noRand
    | exact pushFlowStepStmt_noRand
    | exact advanceCurStepStmt_noRand
    | exact relabelStepStmt_noRand
    | exact freezeStepStmt_noRand
    | constructor

lemma pruneMemInv_of_regs_agree {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} {st₀ st₁ : State}
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hreg : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st₁.regs r = st₀.regs r)
    (hat : st₁.regs prActTop = st₀.regs prActTop)
    (hpt : st₁.regs prPeelTop = st₀.regs prPeelTop)
    (hmem : st₁.mem = st₀.mem) :
    PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₁ :=
  mkPruneMemInv hinv hdisj hreg
    (by rw [hmem]; exact preservedOutside2_refl _ _ _ _ _)
    (hat.trans hinv.reg_actTop) (hpt.trans hinv.reg_peelTop)
    (by rw [hmem]; exact hinv.outR_eq) (by rw [hmem]; exact hinv.h_eq)
    (by rw [hmem]; exact hinv.cur_eq) (by rw [hmem]; exact hinv.abs_eq)
    (by rw [hmem]; exact hinv.ex_eq) (by rw [hmem]; exact hinv.degR_eq)
    (by rw [hmem]; exact hinv.inAct_eq) (by rw [hmem]; exact hinv.actStk_eq)
    (by rw [hmem]; exact hinv.peelStk_eq) (by rw [hmem]; exact hinv.flowEnc_eq)
    (by rw [hmem]; exact hinv.lvlVol_H) (by rw [hmem]; exact hinv.lvlVol_eq)
    hinv.buckets_nodup hinv.buckets_mem
    (fun ℓ h1 hH => by rw [hmem]; exact hinv.buckets_dl ℓ h1 hH)
    hinv.ex_bound hinv.prune_inv hinv.peelQ_inv

lemma pruneStep_adm_check {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr u : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} {st₀ st9 : State}
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (huN : u < cfg.G.n) (huR : s.inR u = true)
    (hcur_lt : s.cur u < (cfg.incEdges u).length)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w)
    (hm9 : st9.mem = st₀.mem) (hp9 : st9.pos = st₀.pos)
    (hr9_le : ∀ r ≤ prCsrAdjH, st9.regs r = st₀.regs r)
    (hr9_u : st9.regs prU = u)
    (hr9_t1 : st9.regs prTmp1 = s.cur u)
    (hr9_st : st9.regs prStart = csrOff cfg.G u) :
    let q := (cfg.incEdges u).getD (s.cur u) (0, false, 0)
    let adm := s.inR q.2.2 && decide (flowDir s.flow q.1 q.2.1 < ↑cfg.C_cap) &&
      decide (s.h u = s.h q.2.2 + 1)
    ∃ st25 c_adm, c_adm ≤ 102 ∧
      st25.mem = st₀.mem ∧ st25.pos = st₀.pos ∧
      (∀ r ≤ prCsrAdjH, st25.regs r = st₀.regs r) ∧
      st25.regs prU = u ∧
      st25.regs prTmp1 = (if adm = true then 1 else 0) ∧
      ∀ ω, Runs w p ω (seqStmts
        [ .assign prJ (.bin .add (.reg prStart) (.reg prTmp1))
        , .assign prW (.load (.bin .add (.reg prCsrAdjV) (.reg prJ)))
        , .assign prTmp3 (.load (.bin .add (.reg prCsrAdjH) (.reg prJ)))
        , .assign prIdx (.bin .div (.reg prTmp3) (.const 2))
        , .assign prDir (.bin .mod (.reg prTmp3) (.const 2))
        , .assign prTmp3 (.load (.bin .add (.reg prFlowEnc) (.reg prIdx)))
        , .cond (.bin .eq (.reg prDir) (.const 1))
            (.assign prRc (.reg prTmp3))
            (.assign prRc (.bin .sub (.bin .mul (.const 2) (.reg prCcap)) (.reg prTmp3)))
        , .assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prW)))
        , .assign prTmp2 (.load (.bin .add (.reg prHArr) (.reg prU)))
        , .assign prTmp3 (.load (.bin .add (.reg prHArr) (.reg prW)))
        , .cond (.bin .lt (.const 0) (.reg prRc))
            (.assign prDelta (.const 1))
            (.assign prDelta (.const 0))
        , .assign prTmp1 (.bin .mul (.reg prTmp1) (.reg prDelta))
        , .cond (.bin .lt (.const 0) (.reg prTmp2))
            (.assign prDelta (.const 1))
            (.assign prDelta (.const 0))
        , .assign prTmp1 (.bin .mul (.reg prTmp1) (.reg prDelta))
        , .cond (.bin .eq (.bin .sub (.reg prTmp2) (.const 1)) (.reg prTmp3))
            (.assign prDelta (.const 1))
            (.assign prDelta (.const 0))
        , .assign prTmp1 (.bin .mul (.reg prTmp1) (.reg prDelta)) ]) st9 .normal st25 c_adm := by
  have hwb := pruneWordBound_pos hw
  have hlt2w : ∀ k, k < workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H → k < 2 ^ w := fun k hk => by
    unfold PruneWordBound at hw; omega
  have hk_csr : s.cur u < (csrIncAux u 0 cfg.G.edges).length := by
    rwa [← hinv.cfg_incEdges u]
  let q := (cfg.incEdges u).getD (s.cur u) (0, false, 0)
  let idx := q.1; let dir := q.2.1; let nbr := q.2.2
  have hq_eq : q = (csrIncAux u 0 cfg.G.edges)[s.cur u]'hk_csr := by
    dsimp [q]; rw [hinv.cfg_incEdges u, List.getD_eq_getElem _ _ hk_csr]
  rcases csrIncAux_getElem_lt hinv.cfg_valid.1 hk_csr with ⟨hidx_gm, hnbr_lt, _, _⟩
  rw [← hq_eq] at hidx_gm hnbr_lt
  have hidx_lt : idx < cfg.G.m := hidx_gm
  have hnbr_lt' : nbr < cfg.G.n := hnbr_lt
  let enc := (↑cfg.C_cap + s.flow idx).toNat
  have hc_cap := hinv.prune_inv.flow_cap idx (by rw [hinv.cfg_edges]; exact hidx_lt)
  have henc_le : enc ≤ 2 * cfg.C_cap := by dsimp [enc]; omega
  let rc := (↑cfg.C_cap - flowDir s.flow idx dir).toNat
  have hrc_val : rc = if dir = true then enc else 2 * cfg.C_cap - enc := by
    dsimp [rc, enc, flowDir]; cases dir <;> (simp; try omega)
  have hrc_pos_iff : 0 < rc ↔ flowDir s.flow idx dir < ↑cfg.C_cap := by
    dsimp [rc, flowDir]; cases dir <;> (simp; try omega)
  have hcsr_off_lt : csrOff cfg.G u + s.cur u < 2 * cfg.G.m := by
    have hsub := csrOff_le_two_mul_m cfg.G (u + 1); rw [csrOff_succ] at hsub; omega
  have hadjH_lt2w : 2 * idx + (if dir = true then 1 else 0) < 2 ^ w := by
    unfold PruneWordBound at hw; cases dir <;> (simp; try omega)
  have hdir_val : (2 * idx + (if dir = true then 1 else 0)) % 2 = if dir = true then 1 else 0 := by
    cases dir <;> simp
  have hidx_val : (2 * idx + (if dir = true then 1 else 0)) / 2 = idx := by
    cases dir <;> (simp; try omega)
  let b1 := if s.inR nbr = true then 1 else 0
  let b2 := if 0 < rc then 1 else 0
  let b3a := if 0 < s.h u then 1 else 0
  let b3b := if s.h u - 1 = s.h nbr then 1 else 0
  let admFlag := b1 * b2 * b3a * b3b
  have hadm_iff : admFlag = 1 ↔
      (s.inR nbr && decide (flowDir s.flow idx dir < ↑cfg.C_cap) &&
        decide (s.h u = s.h nbr + 1)) = true := by
    dsimp [admFlag, b1, b2, b3a, b3b]
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, ← hrc_pos_iff]
    by_cases hrn : s.inR nbr = true <;> by_cases hfl : 0 < rc <;>
      by_cases hhu : 0 < s.h u <;> by_cases hsub : s.h u - 1 = s.h nbr <;>
      simp [hrn, hfl, hhu, hsub] <;> omega
  let st10 : State := { mem := st₀.mem, regs := Function.update st9.regs prJ (csrOff cfg.G u + s.cur u), pos := st₀.pos }
  let st11 : State := { mem := st₀.mem, regs := Function.update st10.regs prW nbr, pos := st₀.pos }
  let st12 : State := { mem := st₀.mem, regs := Function.update st11.regs prTmp3 (2 * idx + if dir = true then 1 else 0), pos := st₀.pos }
  let st13 : State := { mem := st₀.mem, regs := Function.update st12.regs prIdx idx, pos := st₀.pos }
  let st14 : State := { mem := st₀.mem, regs := Function.update st13.regs prDir (if dir = true then 1 else 0), pos := st₀.pos }
  let st15 : State := { mem := st₀.mem, regs := Function.update st14.regs prTmp3 enc, pos := st₀.pos }
  let st16 : State := { mem := st₀.mem, regs := Function.update st15.regs prRc rc, pos := st₀.pos }
  let st17 : State := { mem := st₀.mem, regs := Function.update st16.regs prTmp1 b1, pos := st₀.pos }
  let st18 : State := { mem := st₀.mem, regs := Function.update st17.regs prTmp2 (s.h u), pos := st₀.pos }
  let st19 : State := { mem := st₀.mem, regs := Function.update st18.regs prTmp3 (s.h nbr), pos := st₀.pos }
  let st20 : State := { mem := st₀.mem, regs := Function.update st19.regs prDelta b2, pos := st₀.pos }
  let st21 : State := { mem := st₀.mem, regs := Function.update st20.regs prTmp1 (b1 * b2), pos := st₀.pos }
  let st22 : State := { mem := st₀.mem, regs := Function.update st21.regs prDelta b3a, pos := st₀.pos }
  let st23 : State := { mem := st₀.mem, regs := Function.update st22.regs prTmp1 (b1 * b2 * b3a), pos := st₀.pos }
  let st24 : State := { mem := st₀.mem, regs := Function.update st23.regs prDelta b3b, pos := st₀.pos }
  let st25 : State := { mem := st₀.mem, regs := Function.update st24.regs prTmp1 admFlag, pos := st₀.pos }
  have hr16_le : ∀ r ≤ prCsrAdjH, st16.regs r = st₀.regs r := fun r hr => by
    dsimp [st16, st15, st14, st13, st12, st11, st10, prCsrAdjH, prRc, prTmp3, prDir, prIdx, prW, prJ] at hr ⊢
    simp only [Function.update_apply]
    repeat (rw [ite_eq_right (by omega)])
    exact hr9_le r hr
  have hr16_w : st16.regs prW = nbr := by
    dsimp [st16, st15, st14, st13, st12, st11]
    simp only [Function.update_apply, prRc, prTmp3, prDir, prIdx, prW]; simp
  have hr16_u : st16.regs prU = u := by
    dsimp [st16, st15, st14, st13, st12, st11, st10]
    simp only [Function.update_apply, prRc, prTmp3, prDir, prIdx, prW, prJ, prU]
    simp [hr9_u]
  have hr25_le : ∀ r ≤ prCsrAdjH, st25.regs r = st₀.regs r := fun r hr => by
    dsimp [st25, st24, st23, st22, st21, st20, st19, st18, st17,
      prCsrAdjH, prTmp1, prDelta, prTmp3, prTmp2] at hr ⊢
    simp only [Function.update_apply]
    repeat (rw [ite_eq_right (by omega)])
    exact hr16_le r hr
  have hr25_u : st25.regs prU = u := by
    dsimp [st25, st24, st23, st22, st21, st20, st19, st18, st17]
    simp only [Function.update_apply, prTmp1, prDelta, prTmp3, prTmp2, prU]
    simp [hr16_u]
  have hr25_t1 : st25.regs prTmp1 = if
      (s.inR q.2.2 && decide (flowDir s.flow q.1 q.2.1 < ↑cfg.C_cap) &&
        decide (s.h u = s.h q.2.2 + 1)) = true then 1 else 0 := by
    have hself : st25.regs prTmp1 = admFlag := by dsimp [st25]; rw [Function.update_self]
    rw [hself]
    by_cases hadm : (s.inR nbr && decide (flowDir s.flow idx dir < ↑cfg.C_cap) &&
        decide (s.h u = s.h nbr + 1)) = true
    · simp only [idx, dir, nbr] at hadm; simp [hadm]; exact hadm_iff.mpr hadm
    · have hadm' : (s.inR nbr && decide (flowDir s.flow idx dir < ↑cfg.C_cap) &&
          decide (s.h u = s.h nbr + 1)) = false := Bool.eq_false_iff.mpr hadm
      have h01 : admFlag = 0 ∨ admFlag = 1 := by
        dsimp [admFlag, b1, b2, b3a, b3b]; split_ifs <;> omega
      have hne1 : admFlag ≠ 1 := fun h1 => hadm (hadm_iff.mp h1)
      simp only [idx, dir, nbr] at hadm'; simp only [hadm', Bool.false_eq_true, ↓reduceIte]; omega
  let c16 := if dir = true then 6 else 10
  refine ⟨st25, 89 + c16, by dsimp [c16]; split_ifs <;> omega, rfl, rfl, hr25_le, hr25_u, hr25_t1, ?_⟩
  intro ω
  have hs10 : Runs w p ω (.assign prJ (.bin .add (.reg prStart) (.reg prTmp1))) st9 .normal st10 4 := by
    have hev : Expr.eval w st9 (.bin .add (.reg prStart) (.reg prTmp1)) = some (csrOff cfg.G u + s.cur u) :=
      Expr.eval_bin (op := .add) (eval_reg_eq w st9 prStart hr9_st) (eval_reg_eq w st9 prTmp1 hr9_t1)
        (by dsimp only [BinOp.eval]; unfold PruneWordBound at hw; omega)
    exact runs_assign_iff.mpr ⟨csrOff cfg.G u + s.cur u, hev, rfl,
      by cases st9; simp_all [st10], by simp [Expr.size]⟩
  have hadjV_mem : st₀.mem (csrAddr + 2 * cfg.G.n + 1 + (csrOff cfg.G u + s.cur u)) = nbr := by
    have h1 := (hinv.csr_at.2 u huN (s.cur u) hk_csr).1
    rw [Nat.add_assoc (csrAddr + 2 * cfg.G.n + 1)] at h1; dsimp [nbr]; rw [hq_eq]; exact h1
  have hadjH_mem : st₀.mem (csrAddr + 2 * cfg.G.n + 1 + 2 * cfg.G.m + (csrOff cfg.G u + s.cur u)) =
      2 * idx + (if dir = true then 1 else 0) := by
    have h2 := (hinv.csr_at.2 u huN (s.cur u) hk_csr).2
    rw [Nat.add_assoc (csrAddr + 2 * cfg.G.n + 1 + 2 * cfg.G.m)] at h2
    dsimp [idx, dir]; simp only [hq_eq]; exact h2
  have hs11 : Runs w p ω (.assign prW (.load (.bin .add (.reg prCsrAdjV) (.reg prJ)))) st10 .normal st11 5 :=
    runs_assign_iff.mpr ⟨nbr,
      eval_load_add_eq w st10 prCsrAdjV prJ
        (by dsimp [st10]; rw [Function.update_of_ne (by decide), hr9_le prCsrAdjV (by decide)]; exact hinv.reg_adjV)
        (by dsimp [st10]; rw [Function.update_self]) (by omega) hadjV_mem,
      rfl, rfl, by simp [Expr.size]⟩
  have hs12 : Runs w p ω (.assign prTmp3 (.load (.bin .add (.reg prCsrAdjH) (.reg prJ)))) st11 .normal st12 5 :=
    runs_assign_iff.mpr ⟨2 * idx + if dir = true then 1 else 0,
      eval_load_add_eq w st11 prCsrAdjH prJ
        (by dsimp [st11, st10]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            hr9_le prCsrAdjH (by decide)]; exact hinv.reg_adjH)
        (by dsimp [st11, st10]; rw [Function.update_of_ne (by decide), Function.update_self])
        (by omega) hadjH_mem,
      rfl, rfl, by simp [Expr.size]⟩
  have hs13 : Runs w p ω (.assign prIdx (.bin .div (.reg prTmp3) (.const 2))) st12 .normal st13 4 :=
    runs_assign_iff.mpr ⟨idx, by
      have hdiv_lt : (2 * idx + if dir = true then 1 else 0) / 2 < 2 ^ w := by
        rw [hidx_val]; unfold PruneWordBound at hw; omega
      have hev : Expr.eval w st12 (.bin .div (.reg prTmp3) (.const 2)) =
          some ((2 * idx + if dir = true then 1 else 0) / 2) :=
        Expr.eval_bin (op := .div)
          (eval_reg_eq w st12 prTmp3 (by dsimp [st12]; rw [Function.update_self]))
          (Expr.eval_const (k := 2) (by omega)) (by dsimp only [BinOp.eval]; exact hdiv_lt)
      simpa only [hidx_val] using hev, rfl, rfl, by simp [Expr.size]⟩
  have hs14 : Runs w p ω (.assign prDir (.bin .mod (.reg prTmp3) (.const 2))) st13 .normal st14 4 :=
    runs_assign_iff.mpr ⟨if dir = true then 1 else 0, by
      have hr13_t3 : st13.regs prTmp3 = 2 * idx + if dir = true then 1 else 0 := by
        dsimp [st13, st12]; rw [Function.update_of_ne (by decide), Function.update_self]
      have hev : Expr.eval w st13 (.bin .mod (.reg prTmp3) (.const 2)) =
          some ((2 * idx + if dir = true then 1 else 0) % 2) :=
        Expr.eval_bin (op := .mod) (eval_reg_eq w st13 prTmp3 hr13_t3) (Expr.eval_const (k := 2) (by omega))
          (lt_trans (Nat.mod_lt _ (by omega)) (by omega))
      simpa only [hdir_val] using hev, rfl, rfl, by simp [Expr.size]⟩
  have hs15 : Runs w p ω (.assign prTmp3 (.load (.bin .add (.reg prFlowEnc) (.reg prIdx)))) st14 .normal st15 5 :=
    runs_assign_iff.mpr ⟨enc,
      eval_load_add_eq w st14 prFlowEnc prIdx
        (by dsimp [st14, st13, st12, st11, st10]
            simp only [Function.update_apply, prDir, prIdx, prTmp3, prW, prJ, prFlowEnc]
            simp [hr9_le prFlowEnc (by decide), hinv.reg_flowEnc])
        (by dsimp [st14, st13]; rw [Function.update_of_ne (by decide), Function.update_self])
        (hlt2w _ (by unfold pruneWorkSpace; dsimp [wFlowEnc]; omega)) (hinv.flowEnc_eq idx hidx_lt),
      rfl, rfl, by simp [Expr.size]⟩
  have hs16 : Runs w p ω
      (.cond (.bin .eq (.reg prDir) (.const 1))
        (.assign prRc (.reg prTmp3))
        (.assign prRc (.bin .sub (.bin .mul (.const 2) (.reg prCcap)) (.reg prTmp3))))
      st15 .normal st16 c16 := by
    have hr15_dir : st15.regs prDir = if dir = true then 1 else 0 := by
      dsimp [st15, st14]; rw [Function.update_of_ne (by decide), Function.update_self]
    have hr15_t3 : st15.regs prTmp3 = enc := by dsimp [st15]; rw [Function.update_self]
    have hr15_cc : st15.regs prCcap = cfg.C_cap := by
      dsimp [st15, st14, st13, st12, st11, st10]
      simp only [Function.update_apply, prTmp3, prDir, prIdx, prW, prJ, prCcap]
      simp [hr9_le prCcap (by decide), hinv.reg_ccap]
    have hcond : Expr.eval w st15 (.bin .eq (.reg prDir) (.const 1)) =
        some (if dir = true then 1 else 0) := by
      have hev : Expr.eval w st15 (.bin .eq (.reg prDir) (.const 1)) =
          some (if (if dir = true then 1 else 0) = 1 then 1 else 0) :=
        Expr.eval_bin (op := .eq) (eval_reg_eq w st15 prDir hr15_dir) (Expr.eval_const (k := 1) (by omega))
          (by dsimp only [BinOp.eval]; split_ifs <;> omega)
      simpa only [show (if (if dir = true then 1 else 0) = 1 then 1 else 0) =
        if dir = true then 1 else 0 by cases dir <;> rfl] using hev
    cases hdb : dir
    · have hrc_b : rc = 2 * cfg.C_cap - enc := by simp [hrc_val, hdb]
      simp only [c16, hdb, Bool.false_eq_true, ↓reduceIte]
      refine runs_cond_iff.mpr ⟨0, 6, by simpa [hdb] using hcond, ?_, by simp [Expr.size]⟩
      simp only [↓reduceIte]
      refine runs_assign_iff.mpr ⟨rc, ?_, rfl, rfl, by simp [Expr.size]⟩
      rw [hrc_b]
      exact Expr.eval_bin (op := .sub)
        (Expr.eval_bin (op := .mul) (Expr.eval_const (k := 2) (by omega)) (eval_reg_eq w st15 prCcap hr15_cc)
          (by dsimp only [BinOp.eval]; unfold PruneWordBound at hw; omega))
        (eval_reg_eq w st15 prTmp3 hr15_t3) (by dsimp only [BinOp.eval]; unfold PruneWordBound at hw; omega)
    · have hrc_b : rc = enc := by simp [hrc_val, hdb]
      simp only [c16, hdb, ↓reduceIte]
      refine runs_cond_iff.mpr ⟨1, 2, by simpa [hdb] using hcond, ?_, by simp [Expr.size]⟩
      simp only [Nat.one_ne_zero, ↓reduceIte]
      exact runs_assign_iff.mpr ⟨rc, by rw [hrc_b]; exact eval_reg_eq w st15 prTmp3 hr15_t3,
        rfl, rfl, by simp [Expr.size]⟩
  have hs17 : Runs w p ω (.assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prW)))) st16 .normal st17 5 :=
    runs_assign_iff.mpr ⟨b1,
      eval_load_add_eq w st16 prOutR prW
        (by rw [hr16_le prOutR (by decide)]; exact hinv.reg_outR)
        hr16_w (by omega) (hinv.outR_eq nbr hnbr_lt'),
      rfl, rfl, by simp [Expr.size]⟩
  have hs18 : Runs w p ω (.assign prTmp2 (.load (.bin .add (.reg prHArr) (.reg prU)))) st17 .normal st18 5 :=
    runs_assign_iff.mpr ⟨s.h u,
      eval_load_add_eq w st17 prHArr prU
        (by dsimp [st17]; rw [Function.update_of_ne (by decide), hr16_le prHArr (by decide)]; exact hinv.reg_hArr)
        (by dsimp [st17]; rw [Function.update_of_ne (by decide)]; exact hr16_u)
        (hlt2w _ (by unfold pruneWorkSpace; dsimp [wHArr]; omega)) (hinv.h_eq u huN),
      rfl, rfl, by simp [Expr.size]⟩
  have hs19 : Runs w p ω (.assign prTmp3 (.load (.bin .add (.reg prHArr) (.reg prW)))) st18 .normal st19 5 :=
    runs_assign_iff.mpr ⟨s.h nbr,
      eval_load_add_eq w st18 prHArr prW
        (by dsimp [st18, st17]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            hr16_le prHArr (by decide)]; exact hinv.reg_hArr)
        (by dsimp [st18, st17]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr16_w)
        (hlt2w _ (by unfold pruneWorkSpace; dsimp [wHArr]; omega)) (hinv.h_eq nbr hnbr_lt'),
      rfl, rfl, by simp [Expr.size]⟩
  have hs20 : Runs w p ω
      (.cond (.bin .lt (.const 0) (.reg prRc)) (.assign prDelta (.const 1)) (.assign prDelta (.const 0)))
      st19 .normal st20 6 := by
    have hr19_rc : st19.regs prRc = rc := by
      dsimp [st19, st18, st17, st16]; simp only [Function.update_apply, prTmp3, prTmp2, prTmp1, prRc]; simp
    have hc20 : Expr.eval w st19 (.bin .lt (.const 0) (.reg prRc)) = some b2 :=
      Expr.eval_bin (op := .lt) (Expr.eval_const (k := 0) (by omega)) (eval_reg_eq w st19 prRc hr19_rc)
        (by dsimp only [BinOp.eval]; split_ifs <;> omega)
    by_cases hrc_pos : 0 < rc
    · exact runs_cond_iff.mpr ⟨1, 2, by simpa [b2, hrc_pos] using hc20,
        by simp only [Nat.one_ne_zero, ↓reduceIte, st20, b2, hrc_pos]
           exact runs_assign_iff.mpr ⟨1, Expr.eval_const (k := 1) (by omega), rfl, rfl, by simp [Expr.size]⟩,
        by simp [Expr.size]⟩
    · exact runs_cond_iff.mpr ⟨0, 2, by simpa [b2, hrc_pos] using hc20,
        by simp only [↓reduceIte, st20, b2, hrc_pos]
           exact runs_assign_iff.mpr ⟨0, Expr.eval_const (k := 0) (by omega), rfl, rfl, by simp [Expr.size]⟩,
        by simp [Expr.size]⟩
  have hr20_t1 : st20.regs prTmp1 = b1 := by
    dsimp [st20, st19, st18, st17]; simp only [Function.update_apply, prDelta, prTmp3, prTmp2, prTmp1]; simp
  have hr20_dl : st20.regs prDelta = b2 := by dsimp [st20]; rw [Function.update_self]
  have hs21 : Runs w p ω (.assign prTmp1 (.bin .mul (.reg prTmp1) (.reg prDelta))) st20 .normal st21 4 :=
    runs_assign_iff.mpr ⟨b1 * b2,
      Expr.eval_bin (op := .mul) (eval_reg_eq w st20 prTmp1 hr20_t1) (eval_reg_eq w st20 prDelta hr20_dl)
        (by dsimp only [BinOp.eval, b1, b2]; split_ifs <;> omega),
      rfl, rfl, by simp [Expr.size]⟩
  have hs22a : Runs w p ω
      (.cond (.bin .lt (.const 0) (.reg prTmp2))
        (.assign prDelta (.const 1)) (.assign prDelta (.const 0)))
      st21 .normal st22 6 := by
    have hr21_t2 : st21.regs prTmp2 = s.h u := by
      dsimp [st21, st20, st19, st18]; simp only [Function.update_apply, prTmp1, prDelta, prTmp3, prTmp2]; simp
    have hc22a : Expr.eval w st21 (.bin .lt (.const 0) (.reg prTmp2)) = some b3a :=
      Expr.eval_bin (op := .lt) (Expr.eval_const (k := 0) (by omega)) (eval_reg_eq w st21 prTmp2 hr21_t2)
        (by dsimp only [BinOp.eval]; split_ifs <;> omega)
    by_cases hpos_u : 0 < s.h u
    · exact runs_cond_iff.mpr ⟨1, 2, by simpa [b3a, hpos_u] using hc22a,
        by simp only [Nat.one_ne_zero, ↓reduceIte, st22, b3a, hpos_u]
           exact runs_assign_iff.mpr ⟨1, Expr.eval_const (k := 1) (by omega), rfl, rfl, by simp [Expr.size]⟩,
        by simp [Expr.size]⟩
    · exact runs_cond_iff.mpr ⟨0, 2, by simpa [b3a, hpos_u] using hc22a,
        by simp only [↓reduceIte, st22, b3a, hpos_u]
           exact runs_assign_iff.mpr ⟨0, Expr.eval_const (k := 0) (by omega), rfl, rfl, by simp [Expr.size]⟩,
        by simp [Expr.size]⟩
  have hr22_t1 : st22.regs prTmp1 = b1 * b2 := by
    dsimp [st22, st21]; rw [Function.update_of_ne (by decide), Function.update_self]
  have hr22_dl : st22.regs prDelta = b3a := by dsimp [st22]; rw [Function.update_self]
  have hs22b : Runs w p ω (.assign prTmp1 (.bin .mul (.reg prTmp1) (.reg prDelta))) st22 .normal st23 4 :=
    runs_assign_iff.mpr ⟨b1 * b2 * b3a,
      Expr.eval_bin (op := .mul) (eval_reg_eq w st22 prTmp1 hr22_t1) (eval_reg_eq w st22 prDelta hr22_dl)
        (by dsimp only [BinOp.eval, b1, b2, b3a]; split_ifs <;> omega),
      rfl, rfl, by simp [Expr.size]⟩
  have hs22c : Runs w p ω
      (.cond (.bin .eq (.bin .sub (.reg prTmp2) (.const 1)) (.reg prTmp3))
        (.assign prDelta (.const 1)) (.assign prDelta (.const 0)))
      st23 .normal st24 8 := by
    have hr23_t2 : st23.regs prTmp2 = s.h u := by
      dsimp [st23, st22, st21, st20, st19, st18]
      simp only [Function.update_apply, prTmp1, prDelta, prTmp3, prTmp2]; simp
    have hr23_t3 : st23.regs prTmp3 = s.h nbr := by
      dsimp [st23, st22, st21, st20, st19]
      simp only [Function.update_apply, prTmp1, prDelta, prTmp3]; simp
    have hhu_lt : s.h u < cfg.H := hinv.prune_inv.h_lt_H u huR
    have hc22c : Expr.eval w st23 (.bin .eq (.bin .sub (.reg prTmp2) (.const 1)) (.reg prTmp3)) = some b3b :=
      Expr.eval_bin (op := .eq)
        (Expr.eval_bin (op := .sub) (eval_reg_eq w st23 prTmp2 hr23_t2) (Expr.eval_const (k := 1) (by omega))
          (by dsimp only [BinOp.eval]; unfold PruneWordBound at hw; omega))
        (eval_reg_eq w st23 prTmp3 hr23_t3)
        (by dsimp only [BinOp.eval]; split_ifs <;> omega)
    by_cases hhh : s.h u - 1 = s.h nbr
    · exact runs_cond_iff.mpr ⟨1, 2, by simpa [b3b, hhh] using hc22c,
        by simp only [Nat.one_ne_zero, ↓reduceIte, st24, b3b, hhh]
           exact runs_assign_iff.mpr ⟨1, Expr.eval_const (k := 1) (by omega), rfl, rfl, by simp [Expr.size]⟩,
        by simp [Expr.size]⟩
    · exact runs_cond_iff.mpr ⟨0, 2, by simpa [b3b, hhh] using hc22c,
        by simp only [↓reduceIte, st24, b3b, hhh]
           exact runs_assign_iff.mpr ⟨0, Expr.eval_const (k := 0) (by omega), rfl, rfl, by simp [Expr.size]⟩,
        by simp [Expr.size]⟩
  have hr24_t1 : st24.regs prTmp1 = b1 * b2 * b3a := by
    dsimp [st24, st23]; rw [Function.update_of_ne (by decide), Function.update_self]
  have hr24_dl : st24.regs prDelta = b3b := by dsimp [st24]; rw [Function.update_self]
  have hs23 : Runs w p ω (.assign prTmp1 (.bin .mul (.reg prTmp1) (.reg prDelta))) st24 .normal st25 4 :=
    runs_assign_iff.mpr ⟨admFlag,
      Expr.eval_bin (op := .mul) (eval_reg_eq w st24 prTmp1 hr24_t1) (eval_reg_eq w st24 prDelta hr24_dl)
        (by dsimp only [BinOp.eval, admFlag, b1, b2, b3a, b3b]; split_ifs <;> omega),
      rfl, rfl, by simp [Expr.size]⟩
  convert runs_seq hs10 (runs_seq hs11 (runs_seq hs12 (runs_seq hs13
    (runs_seq hs14 (runs_seq hs15 (runs_seq hs16 (runs_seq hs17 (runs_seq hs18
      (runs_seq hs19 (runs_seq hs20 (runs_seq hs21
        (runs_seq hs22a (runs_seq hs22b (runs_seq hs22c hs23)))))))))))))) using 1
  omega

lemma runs_seqStmts_append {w : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ {s : Stmt} {ss : List Stmt} {t : Stmt} {st₀ st₁ st₂ : State} {c₁ c₂ : ℕ},
      Runs w p ω (seqStmts (s :: ss)) st₀ .normal st₁ c₁ →
      Runs w p ω t st₁ .normal st₂ c₂ →
      Runs w p ω (seqStmts (s :: ss ++ [t])) st₀ .normal st₂ (c₁ + c₂ + 1)
  | _, [], _, _, _, _, _, _, h1, h2 => runs_seq h1 h2
  | s, s' :: rest, t, st₀, st₁, st₂, c₁, c₂, h1, h2 => by
    rcases runs_seq_iff.mp h1 with ⟨v, c_s, _, hret, _⟩ | ⟨st_m, c_s, c_r, hs, hr, rfl⟩
    · exact absurd hret (by simp)
    · have ih := runs_seqStmts_append (s := s') (ss := rest) hr h2
      simpa only [List.cons_append, seqStmts, Nat.add_assoc] using
        runs_seq_iff.mpr (Or.inr ⟨st_m, c_s, c_r + c₂ + 1, hs, ih, by omega⟩)

lemma runs_seq2 {w : ℕ} {p : Program} {ω : ℕ → Bool} {a b t : Stmt}
    {st₀ st₁ st₂ : State} {c₁ c₂ : ℕ}
    (h1 : Runs w p ω (seqStmts [a, b]) st₀ .normal st₁ c₁)
    (h2 : Runs w p ω t st₁ .normal st₂ c₂) :
    Runs w p ω (.seq a (.seq b t)) st₀ .normal st₂ (c₁ + c₂ + 1) :=
  runs_seqStmts_append (s := a) (ss := [b]) h1 h2

lemma runs_seq3 {w : ℕ} {p : Program} {ω : ℕ → Bool} {a b c t : Stmt}
    {st₀ st₁ st₂ : State} {c₁ c₂ : ℕ}
    (h1 : Runs w p ω (seqStmts [a, b, c]) st₀ .normal st₁ c₁)
    (h2 : Runs w p ω t st₁ .normal st₂ c₂) :
    Runs w p ω (.seq a (.seq b (.seq c t))) st₀ .normal st₂ (c₁ + c₂ + 1) :=
  runs_seqStmts_append (s := a) (ss := [b, c]) h1 h2

lemma runs_seq4 {w : ℕ} {p : Program} {ω : ℕ → Bool} {a b c d t : Stmt}
    {st₀ st₁ st₂ : State} {c₁ c₂ : ℕ}
    (h1 : Runs w p ω (seqStmts [a, b, c, d]) st₀ .normal st₁ c₁)
    (h2 : Runs w p ω t st₁ .normal st₂ c₂) :
    Runs w p ω (.seq a (.seq b (.seq c (.seq d t)))) st₀ .normal st₂ (c₁ + c₂ + 1) :=
  runs_seqStmts_append (s := a) (ss := [b, c, d]) h1 h2


end MinCostFlow.Expander
