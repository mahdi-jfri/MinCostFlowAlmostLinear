module

public import MinCostFlow.Expander.PruningPeelPopProg

import Mathlib.Tactic.Linarith

/-!
# Absorb Step and Advance-Cursor Step Triples
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

/-- Word-RAM statement implementing `absorbStep cfg u s` (expects `prU = u`):
computes `give := min ex[u] (degX[u] - abs[u])`, decrements `ex[u]`, increments `abs[u]`. -/
def absorbStepStmt : Stmt :=
  seqStmts [
    .assign prTmp1 (.load (.bin .add (.reg prDegX) (.reg prU))),
    .assign prTmp2 (.load (.bin .add (.reg prAbs) (.reg prU))),
    .assign prTmp1 (.bin .sub (.reg prTmp1) (.reg prTmp2)),
    .assign prTmp2 (.load (.bin .add (.reg prEx) (.reg prU))),
    .cond (.bin .lt (.reg prTmp2) (.reg prTmp1))
      (.assign prTmp1 (.reg prTmp2))
      .nop,
    .store (.bin .add (.reg prEx) (.reg prU)) (.bin .sub (.reg prTmp2) (.reg prTmp1)),
    .assign prTmp2 (.load (.bin .add (.reg prAbs) (.reg prU))),
    .store (.bin .add (.reg prAbs) (.reg prU)) (.bin .add (.reg prTmp2) (.reg prTmp1))
  ]

lemma absorbStepStmt_noRand : absorbStepStmt.NoRand := by
  apply seqStmts_noRand
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Stmt.NoRand]

theorem absorbStep_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr u : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} (st₀ : State)
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (huR : s.inR u = true) (hexPos : 0 < s.ex u) (habsLt : s.abs u < cfg.degX u)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length) :
    let n := cfg.G.n
    let s' := absorbStep cfg u s
    Triple w p
      (fun st => st = st₀ ∧ st.regs prU = u)
      absorbStepStmt
      (normalPost fun st' =>
        (∀ r, r ≤ prCsrAdjH → r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + n)
          (wHArr workAddr n cfg.G.m cfg.H) (workAddr + pruneWorkSpace n cfg.G.m cfg.H) ∧
        PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s' buckets st')
      (fun _ => 55) := by
  intro n s' st ω ⟨hst, hru⟩
  subst st
  set m := cfg.G.m; set H := cfg.H
  have hw_pos := pruneWordBound_pos hw
  have hwb : workAddr + pruneWorkSpace n m H < 2 ^ w := by
    unfold PruneWordBound at hw; dsimp only [n, m, H] at *; omega
  have huX := hinv.prune_inv.inR_sub u huR
  have hun : u < n := by rw [hinv.cfg_X] at huX; exact Finset.mem_range.mp huX
  have hdeg_le : cfg.degX u ≤ 2 * m := hinv.degX_le_two_mul_m hun
  have hdeg_w : cfg.degX u < 2 ^ w := by
    unfold PruneWordBound at hw; dsimp only [m] at *; omega
  have habs_w : s.abs u < 2 ^ w := by dsimp only [m] at *; omega
  have hex_w : s.ex u < 2 ^ w := by
    have hex_le := hinv.ex_bound u hun
    have hlt8 : 4 * cfg.C_cap * cfg.G.m ≤ 8 * cfg.C_cap * cfg.G.m := by
      have : 0 ≤ cfg.C_cap * cfg.G.m := Nat.zero_le _
      linarith
    unfold PruneWordBound at hw; dsimp only [n, m, H] at *; omega
  set remCap := cfg.degX u - s.abs u
  set give := min (s.ex u) remCap
  have hgive_w : give < 2 ^ w := by dsimp [give, remCap]; omega
  apply runs_start_le
  apply runs_seq_assign_le (v := cfg.degX u)
  · exact eval_load_add_regs hinv.reg_degX hru
      (by dsimp [wDegX]; unfold pruneWorkSpace at hwb; omega)
      (hinv.degX_eq u hun) hdeg_w
  set st1 : State := { st₀ with regs := Function.update st₀.regs prTmp1 (cfg.degX u) }
  apply runs_seq_assign_le (v := s.abs u)
  · exact eval_load_add_regs
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide)]; exact hinv.reg_abs)
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide)]; exact hru)
      (by dsimp [wAbs]; unfold pruneWorkSpace at hwb; omega)
      (hinv.abs_eq u hun) habs_w
  set st2 : State := { st1 with regs := Function.update st1.regs prTmp2 (s.abs u) }
  apply runs_seq_assign_le (v := remCap)
  · exact eval_sub_regs
      (by dsimp only [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_self])
      (by dsimp only [st2]; exact Function.update_self ..) hdeg_w habs_w
  set st3 : State := { st2 with regs := Function.update st2.regs prTmp1 remCap }
  apply runs_seq_assign_le (v := s.ex u)
  · exact eval_load_add_regs
      (by dsimp only [st3, st2, st1]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide)]
          exact hinv.reg_ex)
      (by dsimp only [st3, st2, st1]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide)]
          exact hru)
      (by dsimp [wEx]; unfold pruneWorkSpace at hwb; omega)
      (hinv.ex_eq u hun) hex_w
  set st4 : State := { st3 with regs := Function.update st3.regs prTmp2 (s.ex u) }
  have hcond : Triple w p (fun sx => sx = st4)
      (.cond (.bin .lt (.reg prTmp2) (.reg prTmp1)) (.assign prTmp1 (.reg prTmp2)) .nop)
      (normalPost fun st5 =>
        (∀ r, r ≤ prCsrAdjH → st5.regs r = st₀.regs r) ∧
        st5.regs prU = u ∧ st5.regs prTmp1 = give ∧ st5.regs prTmp2 = s.ex u ∧
        st5.pos = st₀.pos ∧ st5.mem = st₀.mem)
      (fun _ => 8) := by
    intro sx ω hsx; subst sx
    have h4_t1 : st4.regs prTmp1 = remCap := by
      dsimp only [st4, st3]; rw [Function.update_of_ne (by decide), Function.update_self]
    have h4_t2 : st4.regs prTmp2 = s.ex u := by dsimp only [st4]; rw [Function.update_self]
    have h4_u : st4.regs prU = u := by
      dsimp only [st4, st3, st2, st1]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      exact hru
    have h4_regs : ∀ r, r ≤ prCsrAdjH → st4.regs r = st₀.regs r := by
      intro r hr
      dsimp only [st4, st3, st2, st1]
      rw [Function.update_of_ne (by dsimp only [prCsrAdjH, prTmp2] at *; omega),
        Function.update_of_ne (by dsimp only [prCsrAdjH, prTmp1] at *; omega),
        Function.update_of_ne (by dsimp only [prCsrAdjH, prTmp2] at *; omega),
        Function.update_of_ne (by dsimp only [prCsrAdjH, prTmp1] at *; omega)]
    have hev : Expr.eval w st4 (.bin .lt (.reg prTmp2) (.reg prTmp1)) =
        some (if s.ex u < remCap then 1 else 0) := by
      have h0lt : 0 < 2 ^ w := by omega
      have h1lt : 1 < 2 ^ w := by omega
      have hif : (if s.ex u < remCap then 1 else 0) < 2 ^ w := by split_ifs <;> omega
      simp [Expr.eval, h4_t1, h4_t2, WordRAM.BinOp.eval, hif]
    by_cases hlt : s.ex u < remCap
    · have hgive_eq : give = s.ex u := min_eq_left (le_of_lt hlt)
      refine ⟨.normal, { st4 with regs := Function.update st4.regs prTmp1 (s.ex u) }, _,
        runs_cond_iff.mpr ⟨1, _, by simpa [hlt] using hev,
          by simpa using runs_assign_iff.mpr ⟨s.ex u, eval_reg h4_t2 hex_w, rfl, rfl, rfl⟩, rfl⟩,
        ?_, by simp only [Expr.size]; omega⟩
      refine ⟨fun r hr => by dsimp only; rw [Function.update_of_ne (by dsimp only [prCsrAdjH, prTmp1] at *; omega)]; exact h4_regs r hr,
        by dsimp only; rw [Function.update_of_ne (by decide)]; exact h4_u,
        by dsimp only; rw [Function.update_self, hgive_eq],
        by dsimp only; rw [Function.update_of_ne (by decide)]; exact h4_t2,
        rfl, rfl⟩
    · have hgive_eq : give = remCap := min_eq_right (not_lt.mp hlt)
      refine ⟨.normal, st4, _,
        runs_cond_iff.mpr ⟨0, 1, by simpa [hlt] using hev,
          by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
        ⟨h4_regs, h4_u, h4_t1.trans hgive_eq.symm, h4_t2, rfl, rfl⟩,
        by simp only [Expr.size]; omega⟩
  apply runs_seq_triple_le hcond rfl
  intro st5 ⟨h5_regs, h5_u, h5_t1, h5_t2, h5_pos, h5_mem⟩
  apply runs_seq_store_le (x := wEx workAddr n m H + u) (v := s.ex u - give)
  · exact eval_add_regs ((h5_regs prEx (by decide)).trans hinv.reg_ex) h5_u
      (by dsimp [wEx]; unfold pruneWorkSpace at hwb; omega)
  · exact eval_sub_regs h5_t2 h5_t1 hex_w hgive_w
  set st6 : State := { st5 with mem := Function.update st5.mem (wEx workAddr n m H + u) (s.ex u - give) }
  apply runs_seq_assign_le (v := s.abs u)
  · refine eval_load_add_regs ((h5_regs prAbs (by decide)).trans hinv.reg_abs) h5_u
      (by dsimp [wAbs]; unfold pruneWorkSpace at hwb; omega) ?_ habs_w
    dsimp only [st6]; rw [Function.update_of_ne (by dsimp [wAbs, wEx]; omega), h5_mem]
    exact hinv.abs_eq u hun
  set st7 : State := { st6 with regs := Function.update st6.regs prTmp2 (s.abs u) }
  have habs_give_w : s.abs u + give < 2 ^ w := by
    have : s.abs u + give ≤ cfg.degX u := by dsimp [give, remCap]; omega
    omega
  apply runs_store_le (x := wAbs workAddr n m H + u) (v := s.abs u + give)
  · exact eval_add_regs
      (by dsimp only [st7, st6]; rw [Function.update_of_ne (by decide)]; exact (h5_regs prAbs (by decide)).trans hinv.reg_abs)
      (by dsimp only [st7, st6]; rw [Function.update_of_ne (by decide)]; exact h5_u)
      (by dsimp [wAbs]; unfold pruneWorkSpace at hwb; omega)
  · exact eval_add_regs (by dsimp only [st7]; exact Function.update_self ..)
      (by dsimp only [st7, st6]; rw [Function.update_of_ne (by decide)]; exact h5_t1)
      habs_give_w
  · set stF : State := { st7 with mem := Function.update st6.mem (wAbs workAddr n m H + u) (s.abs u + give) }
    have hF_regs_all : ∀ r, r ≤ prCsrAdjH → stF.regs r = st₀.regs r := by
      intro r hr
      dsimp only [stF, st7, st6]
      rw [Function.update_of_ne (by dsimp only [prCsrAdjH, prTmp2] at *; omega)]
      exact h5_regs r hr
    have hF_regs : ∀ r, r ≤ prCsrAdjH → r ≠ prActTop → r ≠ prPeelTop → stF.regs r = st₀.regs r :=
      fun r hr _ _ => hF_regs_all r hr
    have hmf1 : MemFrame st₀.mem st6.mem (wAbs workAddr n m H) (wDegR workAddr n m H) := by
      dsimp only [st6]; rw [h5_mem]
      exact memFrame_update_in (by dsimp [wAbs, wEx]; omega) (by dsimp [wEx, wDegR]; omega)
    have hmf2 : MemFrame st6.mem stF.mem (wAbs workAddr n m H) (wDegR workAddr n m H) :=
      memFrame_update_in (by dsimp [wAbs]; omega) (by dsimp [wAbs, wDegR]; omega)
    have hmf : MemFrame st₀.mem stF.mem (wAbs workAddr n m H) (wDegR workAddr n m H) :=
      memFrame_trans hmf1 hmf2
    have hpr : PreservedOutside2 st₀.mem stF.mem outRAddr (outRAddr + n)
        (wHArr workAddr n m H) (workAddr + pruneWorkSpace n m H) :=
      memFrame_to_preserved2_right hmf (by dsimp [wHArr, wAbs]; omega)
        (by unfold pruneWorkSpace; dsimp [wDegR]; omega)
    obtain ⟨hG_F, hCsr_F, hinB_F, hdegX_F⟩ := static_of_preserved2 hinv hdisj hpr
    obtain ⟨hlvlH, hlvlEq, hbnd, hbmem, hbdl⟩ := buckets_preserved_of_mem_agree s' stF hinv rfl rfl (fun k hk1 hk2 => by
      dsimp only [n, m, H] at *
      exact hmf k (Or.inr (by dsimp [wDegR, wLvlNext] at hk1 ⊢; omega)))
    have hstep_inv := (absorbStep_inv_pot_pub hinv.prune_inv huR hexPos habsLt).1
    have hstep_pq := peelQInv_of_fields hinv.peelQ_inv rfl rfl
    have hex'_bound : ∀ x < n, s'.ex x ≤ 4 * cfg.C_cap * m := by
      intro x hx
      dsimp only [s', absorbStep, m] at *
      by_cases hxu : x = u
      · subst hxu
        simp only [↓reduceIte]
        exact Nat.le_trans (Nat.sub_le _ _) (hinv.ex_bound x hx)
      · simp [hxu, hinv.ex_bound x hx]
    refine ⟨hF_regs, h5_pos, hpr,
      { cfg_X := hinv.cfg_X
        cfg_valid := hinv.cfg_valid
        reg_g := (hF_regs_all prG (by decide)).trans hinv.reg_g
        reg_csr := (hF_regs_all prCsr (by decide)).trans hinv.reg_csr
        reg_inB := (hF_regs_all prInB (by decide)).trans hinv.reg_inB
        reg_outR := (hF_regs_all prOutR (by decide)).trans hinv.reg_outR
        reg_work := (hF_regs_all prWork (by decide)).trans hinv.reg_work
        reg_ccap := (hF_regs_all prCcap (by decide)).trans hinv.reg_ccap
        reg_H := (hF_regs_all prH (by decide)).trans hinv.reg_H
        reg_theta := (hF_regs_all prTheta (by decide)).trans hinv.reg_theta
        reg_n := (hF_regs_all prN (by decide)).trans hinv.reg_n
        reg_m := (hF_regs_all prM (by decide)).trans hinv.reg_m
        reg_actTop := (hF_regs_all prActTop (by decide)).trans hinv.reg_actTop
        reg_peelTop := (hF_regs_all prPeelTop (by decide)).trans hinv.reg_peelTop
        reg_degX := (hF_regs_all prDegX (by decide)).trans hinv.reg_degX
        reg_hArr := (hF_regs_all prHArr (by decide)).trans hinv.reg_hArr
        reg_cur := (hF_regs_all prCur (by decide)).trans hinv.reg_cur
        reg_abs := (hF_regs_all prAbs (by decide)).trans hinv.reg_abs
        reg_ex := (hF_regs_all prEx (by decide)).trans hinv.reg_ex
        reg_degR := (hF_regs_all prDegR (by decide)).trans hinv.reg_degR
        reg_inAct := (hF_regs_all prInAct (by decide)).trans hinv.reg_inAct
        reg_actStk := (hF_regs_all prActStk (by decide)).trans hinv.reg_actStk
        reg_peelStk := (hF_regs_all prPeelStk (by decide)).trans hinv.reg_peelStk
        reg_lvlNext := (hF_regs_all prLvlNext (by decide)).trans hinv.reg_lvlNext
        reg_lvlPrev := (hF_regs_all prLvlPrev (by decide)).trans hinv.reg_lvlPrev
        reg_remArr := (hF_regs_all prRemArr (by decide)).trans hinv.reg_remArr
        reg_flowEnc := (hF_regs_all prFlowEnc (by decide)).trans hinv.reg_flowEnc
        reg_lvlVol := (hF_regs_all prLvlVol (by decide)).trans hinv.reg_lvlVol
        reg_lvlHead := (hF_regs_all prLvlHead (by decide)).trans hinv.reg_lvlHead
        reg_adjV := (hF_regs_all prCsrAdjV (by decide)).trans hinv.reg_adjV
        reg_adjH := (hF_regs_all prCsrAdjH (by decide)).trans hinv.reg_adjH
        graph_at := hG_F
        csr_at := hCsr_F
        inB_eq := hinB_F
        outR_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (outRAddr + x) (by
            have hdw := hdisj.2.2.2.2.2.2
            unfold pruneWorkSpace at hdw
            rcases hdw with h | h <;> dsimp [wAbs, wDegR]
            · left; omega
            · right; omega)]
          exact hinv.outR_eq x hx
        degX_eq := hdegX_F
        h_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (wHArr workAddr n m H + x) (Or.inl (by dsimp [wHArr, wAbs]; omega))]
          exact hinv.h_eq x hx
        cur_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (wCur workAddr n m H + x) (Or.inl (by dsimp [wCur, wAbs]; omega))]
          exact hinv.cur_eq x hx
        abs_eq := fun x hx => by
          dsimp only [stF, s', absorbStep, give, remCap, n, m, H] at *
          by_cases hxu : x = u
          · subst hxu; simp [Function.update_self]
          · rw [Function.update_of_ne (by omega)]
            dsimp only [st6]
            rw [Function.update_of_ne (by dsimp [wAbs, wEx]; omega), h5_mem, hinv.abs_eq x hx]
            simp [hxu]
        ex_eq := fun x hx => by
          dsimp only [stF, st6, s', absorbStep, give, remCap, n, m, H] at *
          rw [Function.update_of_ne (by dsimp [wEx, wAbs]; omega)]
          by_cases hxu : x = u
          · subst hxu; simp [Function.update_self]
          · rw [Function.update_of_ne (by omega), h5_mem, hinv.ex_eq x hx]
            simp [hxu]
        degR_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (wDegR workAddr n m H + x) (Or.inr (by dsimp [wEx, wDegR]; omega))]
          exact hinv.degR_eq x hx
        inAct_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (wInAct workAddr n m H + x) (Or.inr (by dsimp [wInAct, wDegR]; omega))]
          exact hinv.inAct_eq x hx
        actStk_eq := fun i hi => by
          dsimp only [n, m, H] at *
          rw [hmf (wActStk workAddr n m H + i) (Or.inr (by dsimp [wActStk, wDegR]; omega))]
          exact hinv.actStk_eq i hi
        peelStk_eq := fun i hi => by
          dsimp only [n, m, H] at *
          rw [hmf (wPeelStk workAddr n m H + i) (Or.inr (by dsimp [wPeelStk, wDegR]; omega))]
          exact hinv.peelStk_eq i hi
        flowEnc_eq := fun idx hidx => by
          dsimp only [n, m, H] at *
          rw [hmf (wFlowEnc workAddr n m H + idx) (Or.inr (by dsimp [wFlowEnc, wDegR]; omega))]
          exact hinv.flowEnc_eq idx hidx
        lvlVol_H := hlvlH
        lvlVol_eq := hlvlEq
        buckets_nodup := hbnd
        buckets_mem := hbmem
        buckets_dl := hbdl
        ex_bound := hex'_bound
        prune_inv := hstep_inv
        peelQ_inv := hstep_pq }⟩
  · simp only [Expr.size]; omega

/-- Word-RAM statement implementing `advanceCurStep u s` (expects `prU = u`):
increments `cur[u] := cur[u] + 1`. -/
def advanceCurStepStmt : Stmt :=
  seqStmts [
    .assign prTmp1 (.load (.bin .add (.reg prCur) (.reg prU))),
    .store (.bin .add (.reg prCur) (.reg prU)) (.bin .add (.reg prTmp1) (.const 1))
  ]

lemma advanceCurStepStmt_noRand : advanceCurStepStmt.NoRand := by
  apply seqStmts_noRand
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> simp [Stmt.NoRand]

theorem advanceCurStep_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr u : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} (st₀ : State)
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (huR : s.inR u = true) (habs : s.abs u = cfg.degX u)
    (hcurLt : s.cur u < (cfg.incEdges u).length)
    (hnotAdm : let q := (cfg.incEdges u).getD (s.cur u) (0, false, 0)
      !(s.inR q.2.2 && decide (flowDir s.flow q.1 q.2.1 < (cfg.C_cap : ℤ)) &&
        decide (s.h u = s.h q.2.2 + 1)))
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length) :
    let n := cfg.G.n
    let s' := advanceCurStep u s
    Triple w p
      (fun st => st = st₀ ∧ st.regs prU = u)
      advanceCurStepStmt
      (normalPost fun st' =>
        (∀ r, r ≤ prCsrAdjH → r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + n)
          (wHArr workAddr n cfg.G.m cfg.H) (workAddr + pruneWorkSpace n cfg.G.m cfg.H) ∧
        PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s' buckets st')
      (fun _ => 20) := by
  intro n s' st ω ⟨hst, hru⟩
  subst st
  set m := cfg.G.m; set H := cfg.H
  have hw_pos := pruneWordBound_pos hw
  have hwb : workAddr + pruneWorkSpace n m H < 2 ^ w := by
    unfold PruneWordBound at hw; dsimp only [n, m, H] at *; omega
  have h1lt : 1 < 2 ^ w := by unfold PruneWordBound at hw; omega
  have huX := hinv.prune_inv.inR_sub u huR
  have hun : u < n := by rw [hinv.cfg_X] at huX; exact Finset.mem_range.mp huX
  have hdeg_le : cfg.degX u ≤ 2 * m := hinv.degX_le_two_mul_m hun
  have hinc_le : (cfg.incEdges u).length ≤ 2 * m :=
    le_trans (incEdges_length_le_degX cfg u) hdeg_le
  have hcur_w : s.cur u + 1 < 2 ^ w := by
    unfold PruneWordBound at hw; dsimp only [m] at *; omega
  apply runs_start_le
  apply runs_seq_assign_le (v := s.cur u)
  · exact eval_load_add_regs hinv.reg_cur hru
      (by dsimp [wCur]; unfold pruneWorkSpace at hwb; omega)
      (hinv.cur_eq u hun) (by omega)
  set st1 : State := { st₀ with regs := Function.update st₀.regs prTmp1 (s.cur u) }
  apply runs_store_le (x := wCur workAddr n m H + u) (v := s.cur u + 1)
  · exact eval_add_regs
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide)]; exact hinv.reg_cur)
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide)]; exact hru)
      (by dsimp [wCur]; unfold pruneWorkSpace at hwb; omega)
  · exact eval_add_reg_const (by dsimp only [st1]; exact Function.update_self ..) h1lt hcur_w
  · set stF : State := { st1 with mem := Function.update st₀.mem (wCur workAddr n m H + u) (s.cur u + 1) }
    have hF_regs_all : ∀ r, r ≤ prCsrAdjH → stF.regs r = st₀.regs r := by
      intro r hr
      dsimp only [stF, st1]
      rw [Function.update_of_ne (by dsimp only [prCsrAdjH, prTmp1] at *; omega)]
    have hF_regs : ∀ r, r ≤ prCsrAdjH → r ≠ prActTop → r ≠ prPeelTop → stF.regs r = st₀.regs r :=
      fun r hr _ _ => hF_regs_all r hr
    have hmf : MemFrame st₀.mem stF.mem (wCur workAddr n m H) (wAbs workAddr n m H) :=
      memFrame_update_in (by dsimp [wCur]; omega) (by dsimp [wCur, wAbs]; omega)
    have hpr : PreservedOutside2 st₀.mem stF.mem outRAddr (outRAddr + n)
        (wHArr workAddr n m H) (workAddr + pruneWorkSpace n m H) :=
      memFrame_to_preserved2_right hmf (by dsimp [wHArr, wCur]; omega)
        (by unfold pruneWorkSpace; dsimp [wAbs]; omega)
    obtain ⟨hG_F, hCsr_F, hinB_F, hdegX_F⟩ := static_of_preserved2 hinv hdisj hpr
    obtain ⟨hlvlH, hlvlEq, hbnd, hbmem, hbdl⟩ := buckets_preserved_of_mem_agree s' stF hinv rfl rfl (fun k hk1 hk2 => by
      dsimp only [n, m, H] at *
      exact hmf k (Or.inr (by dsimp [wAbs, wLvlNext] at hk1 ⊢; omega)))
    have hstep_inv := (advanceCurStep_inv_pot_pub hinv.cfg_valid hinv.prune_inv huR habs hcurLt hnotAdm).1
    have hstep_pq := peelQInv_of_fields hinv.peelQ_inv rfl rfl
    refine ⟨hF_regs, rfl, hpr,
      { cfg_X := hinv.cfg_X
        cfg_valid := hinv.cfg_valid
        reg_g := (hF_regs_all prG (by decide)).trans hinv.reg_g
        reg_csr := (hF_regs_all prCsr (by decide)).trans hinv.reg_csr
        reg_inB := (hF_regs_all prInB (by decide)).trans hinv.reg_inB
        reg_outR := (hF_regs_all prOutR (by decide)).trans hinv.reg_outR
        reg_work := (hF_regs_all prWork (by decide)).trans hinv.reg_work
        reg_ccap := (hF_regs_all prCcap (by decide)).trans hinv.reg_ccap
        reg_H := (hF_regs_all prH (by decide)).trans hinv.reg_H
        reg_theta := (hF_regs_all prTheta (by decide)).trans hinv.reg_theta
        reg_n := (hF_regs_all prN (by decide)).trans hinv.reg_n
        reg_m := (hF_regs_all prM (by decide)).trans hinv.reg_m
        reg_actTop := (hF_regs_all prActTop (by decide)).trans hinv.reg_actTop
        reg_peelTop := (hF_regs_all prPeelTop (by decide)).trans hinv.reg_peelTop
        reg_degX := (hF_regs_all prDegX (by decide)).trans hinv.reg_degX
        reg_hArr := (hF_regs_all prHArr (by decide)).trans hinv.reg_hArr
        reg_cur := (hF_regs_all prCur (by decide)).trans hinv.reg_cur
        reg_abs := (hF_regs_all prAbs (by decide)).trans hinv.reg_abs
        reg_ex := (hF_regs_all prEx (by decide)).trans hinv.reg_ex
        reg_degR := (hF_regs_all prDegR (by decide)).trans hinv.reg_degR
        reg_inAct := (hF_regs_all prInAct (by decide)).trans hinv.reg_inAct
        reg_actStk := (hF_regs_all prActStk (by decide)).trans hinv.reg_actStk
        reg_peelStk := (hF_regs_all prPeelStk (by decide)).trans hinv.reg_peelStk
        reg_lvlNext := (hF_regs_all prLvlNext (by decide)).trans hinv.reg_lvlNext
        reg_lvlPrev := (hF_regs_all prLvlPrev (by decide)).trans hinv.reg_lvlPrev
        reg_remArr := (hF_regs_all prRemArr (by decide)).trans hinv.reg_remArr
        reg_flowEnc := (hF_regs_all prFlowEnc (by decide)).trans hinv.reg_flowEnc
        reg_lvlVol := (hF_regs_all prLvlVol (by decide)).trans hinv.reg_lvlVol
        reg_lvlHead := (hF_regs_all prLvlHead (by decide)).trans hinv.reg_lvlHead
        reg_adjV := (hF_regs_all prCsrAdjV (by decide)).trans hinv.reg_adjV
        reg_adjH := (hF_regs_all prCsrAdjH (by decide)).trans hinv.reg_adjH
        graph_at := hG_F
        csr_at := hCsr_F
        inB_eq := hinB_F
        outR_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (outRAddr + x) (by
            have hdw := hdisj.2.2.2.2.2.2
            unfold pruneWorkSpace at hdw
            rcases hdw with h | h <;> dsimp [wCur, wAbs]
            · left; omega
            · right; omega)]
          exact hinv.outR_eq x hx
        degX_eq := hdegX_F
        h_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (wHArr workAddr n m H + x) (Or.inl (by dsimp [wHArr, wCur]; omega))]
          exact hinv.h_eq x hx
        cur_eq := fun x hx => by
          dsimp only [stF, s', advanceCurStep, n, m, H] at *
          by_cases hxu : x = u
          · subst hxu; simp [Function.update_self]
          · rw [Function.update_of_ne (by omega), hinv.cur_eq x hx]; simp [hxu]
        abs_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (wAbs workAddr n m H + x) (Or.inr (by dsimp [wAbs]; omega))]
          exact hinv.abs_eq x hx
        ex_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (wEx workAddr n m H + x) (Or.inr (by dsimp [wEx, wAbs]; omega))]
          exact hinv.ex_eq x hx
        degR_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (wDegR workAddr n m H + x) (Or.inr (by dsimp [wDegR, wAbs]; omega))]
          exact hinv.degR_eq x hx
        inAct_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (wInAct workAddr n m H + x) (Or.inr (by dsimp [wInAct, wAbs]; omega))]
          exact hinv.inAct_eq x hx
        actStk_eq := fun i hi => by
          dsimp only [n, m, H] at *
          rw [hmf (wActStk workAddr n m H + i) (Or.inr (by dsimp [wActStk, wAbs]; omega))]
          exact hinv.actStk_eq i hi
        peelStk_eq := fun i hi => by
          dsimp only [n, m, H] at *
          rw [hmf (wPeelStk workAddr n m H + i) (Or.inr (by dsimp [wPeelStk, wAbs]; omega))]
          exact hinv.peelStk_eq i hi
        flowEnc_eq := fun idx hidx => by
          dsimp only [n, m, H] at *
          rw [hmf (wFlowEnc workAddr n m H + idx) (Or.inr (by dsimp [wFlowEnc, wAbs]; omega))]
          exact hinv.flowEnc_eq idx hidx
        lvlVol_H := hlvlH
        lvlVol_eq := hlvlEq
        buckets_nodup := hbnd
        buckets_mem := hbmem
        buckets_dl := hbdl
        ex_bound := hinv.ex_bound
        prune_inv := hstep_inv
        peelQ_inv := hstep_pq }⟩
  · simp only [Expr.size]; omega


end MinCostFlow.Expander
