module

public import MinCostFlow.Expander.PruningInitBase

/-!
# WordRAM Pruning Init: Setup Registers and Zero Vertices
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

lemma initSetupRegs_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ} (st₀ : State)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hg_w : gAddr + cfg.G.encode.length < 2 ^ w)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (hG : GraphAt st₀.mem gAddr cfg.G) :
    Triple w p
      (fun st => st = st₀ ∧ InitRegPre cfg gAddr csrAddr inBAddr outRAddr workAddr st)
      initSetupRegsStmt
      (normalPost fun st' =>
        st'.mem = st₀.mem ∧ st'.pos = st₀.pos ∧
        InitPtrRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st')
      (fun _ => 130) := by
  intro st ω ⟨hst, hpre⟩
  subst st
  set n := cfg.G.n
  set m := cfg.G.m
  set H := cfg.H
  have hwb := hw
  unfold PruneWordBound pruneWorkSpace at hwb
  have hlen_enc : cfg.G.encode.length = 2 + 2 * m := graph_encode_length cfg.G
  have h0lt : 0 < 2 ^ w := by omega
  have h1lt : 1 < 2 ^ w := by omega
  have h2lt : 2 < 2 ^ w := by omega
  have hg1_lt : gAddr + 1 < 2 ^ w := by omega
  have hlt_pow : ∀ x, x ≤ workAddr + (12 * n + m + 2 * H + 2) → x < 2 ^ w := fun x hx => by omega
  have hmn : st₀.mem gAddr = n := graphAt_n hG
  have hmm : st₀.mem (gAddr + 1) = m := graphAt_m hG
  have h2n : 2 * n < 2 ^ w := by omega
  have h2m : 2 * m < 2 ^ w := by omega
  have hcsrv1 : csrAddr + 2 * n < 2 ^ w := by omega
  have hcsrv : csrAddr + 2 * n + 1 < 2 ^ w := by omega
  have hcsrh : csrAddr + 2 * n + 1 + 2 * m < 2 ^ w := by omega
  have hH1 : H + 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [initSetupRegsStmt, seqStmts]
  apply runs_seq_assign_le (v := n)
  · simp only [Expr.eval, hpre.reg_g, Option.map_some, hmn]
  apply runs_seq_assign_le (v := m)
  · simp only [Expr.eval, Function.update_of_ne (by decide : prG ≠ prN), hpre.reg_g, h1lt,
      WordRAM.BinOp.eval, hg1_lt, ↓reduceIte, Option.map_some, hmm]
  apply runs_seq_assign_le (v := 0)
  · simp only [Expr.eval, h0lt, ↓reduceIte]
  apply runs_seq_assign_le (v := 0)
  · simp only [Expr.eval, h0lt, ↓reduceIte]
  apply runs_seq_assign_le (v := wDegX workAddr n m H)
  · simp only [Expr.eval, Function.update_of_ne (by decide : prWork ≠ prPeelTop),
      Function.update_of_ne (by decide : prWork ≠ prActTop),
      Function.update_of_ne (by decide : prWork ≠ prM),
      Function.update_of_ne (by decide : prWork ≠ prN), hpre.reg_work]
  apply runs_seq_assign_le (v := wHArr workAddr n m H)
  · exact eval_add_regs_eq (by simp [wDegX, wHArr])
      (hlt_pow _ (by dsimp [wHArr]; omega))
  apply runs_seq_assign_le (v := wCur workAddr n m H)
  · exact eval_add_regs_eq (by simp [wHArr, wCur]; omega)
      (hlt_pow _ (by dsimp [wCur]; omega))
  apply runs_seq_assign_le (v := wAbs workAddr n m H)
  · exact eval_add_regs_eq (by simp [wCur, wAbs]; omega)
      (hlt_pow _ (by dsimp [wAbs]; omega))
  apply runs_seq_assign_le (v := wEx workAddr n m H)
  · exact eval_add_regs_eq (by simp [wAbs, wEx]; omega)
      (hlt_pow _ (by dsimp [wEx]; omega))
  apply runs_seq_assign_le (v := wDegR workAddr n m H)
  · exact eval_add_regs_eq (by simp [wEx, wDegR]; omega)
      (hlt_pow _ (by dsimp [wDegR]; omega))
  apply runs_seq_assign_le (v := wInAct workAddr n m H)
  · exact eval_add_regs_eq (by simp [wDegR, wInAct]; omega)
      (hlt_pow _ (by dsimp [wInAct]; omega))
  apply runs_seq_assign_le (v := wActStk workAddr n m H)
  · exact eval_add_regs_eq (by simp [wInAct, wActStk]; omega)
      (hlt_pow _ (by dsimp [wActStk]; omega))
  apply runs_seq_assign_le (v := wPeelStk workAddr n m H)
  · exact eval_add_regs_eq (by simp [wActStk, wPeelStk]; omega)
      (hlt_pow _ (by dsimp [wPeelStk]; omega))
  apply runs_seq_assign_le (v := wLvlNext workAddr n m H)
  · exact eval_add_regs_eq (by simp [wPeelStk, wLvlNext]; omega)
      (hlt_pow _ (by dsimp [wLvlNext]; omega))
  apply runs_seq_assign_le (v := wLvlPrev workAddr n m H)
  · exact eval_add_regs_eq (by simp [wLvlNext, wLvlPrev]; omega)
      (hlt_pow _ (by dsimp [wLvlPrev]; omega))
  apply runs_seq_assign_le (v := wRemArr workAddr n m H)
  · exact eval_add_regs_eq (by simp [wLvlPrev, wRemArr]; omega)
      (hlt_pow _ (by dsimp [wRemArr]; omega))
  apply runs_seq_assign_le (v := wFlowEnc workAddr n m H)
  · exact eval_add_regs_eq (by simp [wRemArr, wFlowEnc]; omega)
      (hlt_pow _ (by dsimp [wFlowEnc]; omega))
  apply runs_seq_assign_le (v := wLvlVol workAddr n m H)
  · exact eval_add_regs_eq (by simp [wFlowEnc, wLvlVol])
      (hlt_pow _ (by dsimp [wLvlVol]; omega))
  apply runs_seq_assign_le (v := wLvlHead workAddr n m H)
  · have hsum : wLvlVol workAddr n m H + (H + 1) = wLvlHead workAddr n m H := by
      dsimp [wLvlVol, wLvlHead]; omega
    have hhead_lt : wLvlHead workAddr n m H < 2 ^ w := hlt_pow _ (by dsimp [wLvlHead]; omega)
    simp only [Expr.eval, Function.update_self, Function.update_of_ne (by decide : prH ≠ prLvlVol),
      Function.update_of_ne (by decide : prH ≠ prFlowEnc),
      Function.update_of_ne (by decide : prH ≠ prRemArr),
      Function.update_of_ne (by decide : prH ≠ prLvlPrev),
      Function.update_of_ne (by decide : prH ≠ prLvlNext),
      Function.update_of_ne (by decide : prH ≠ prPeelStk),
      Function.update_of_ne (by decide : prH ≠ prActStk),
      Function.update_of_ne (by decide : prH ≠ prInAct),
      Function.update_of_ne (by decide : prH ≠ prDegR),
      Function.update_of_ne (by decide : prH ≠ prEx),
      Function.update_of_ne (by decide : prH ≠ prAbs),
      Function.update_of_ne (by decide : prH ≠ prCur),
      Function.update_of_ne (by decide : prH ≠ prHArr),
      Function.update_of_ne (by decide : prH ≠ prDegX),
      Function.update_of_ne (by decide : prH ≠ prPeelTop),
      Function.update_of_ne (by decide : prH ≠ prActTop),
      Function.update_of_ne (by decide : prH ≠ prM),
      Function.update_of_ne (by decide : prH ≠ prN),
      (show st₀.regs prH = H from hpre.reg_H), h1lt, WordRAM.BinOp.eval,
      hH1, ↓reduceIte, hsum, hhead_lt]
  apply runs_seq_assign_le (v := csrAddr + 2 * n + 1)
  · simp only [Expr.eval, WordRAM.BinOp.eval, h2lt, h1lt, h2n, hcsrv1, hcsrv, ↓reduceIte,
      Function.update_of_ne (by decide : prCsr ≠ prLvlHead),
      Function.update_of_ne (by decide : prCsr ≠ prLvlVol),
      Function.update_of_ne (by decide : prCsr ≠ prFlowEnc),
      Function.update_of_ne (by decide : prCsr ≠ prRemArr),
      Function.update_of_ne (by decide : prCsr ≠ prLvlPrev),
      Function.update_of_ne (by decide : prCsr ≠ prLvlNext),
      Function.update_of_ne (by decide : prCsr ≠ prPeelStk),
      Function.update_of_ne (by decide : prCsr ≠ prActStk),
      Function.update_of_ne (by decide : prCsr ≠ prInAct),
      Function.update_of_ne (by decide : prCsr ≠ prDegR),
      Function.update_of_ne (by decide : prCsr ≠ prEx),
      Function.update_of_ne (by decide : prCsr ≠ prAbs),
      Function.update_of_ne (by decide : prCsr ≠ prCur),
      Function.update_of_ne (by decide : prCsr ≠ prHArr),
      Function.update_of_ne (by decide : prCsr ≠ prDegX),
      Function.update_of_ne (by decide : prCsr ≠ prPeelTop),
      Function.update_of_ne (by decide : prCsr ≠ prActTop),
      Function.update_of_ne (by decide : prCsr ≠ prM),
      Function.update_of_ne (by decide : prCsr ≠ prN),
      Function.update_of_ne (by decide : prN ≠ prLvlHead),
      Function.update_of_ne (by decide : prN ≠ prLvlVol),
      Function.update_of_ne (by decide : prN ≠ prFlowEnc),
      Function.update_of_ne (by decide : prN ≠ prRemArr),
      Function.update_of_ne (by decide : prN ≠ prLvlPrev),
      Function.update_of_ne (by decide : prN ≠ prLvlNext),
      Function.update_of_ne (by decide : prN ≠ prPeelStk),
      Function.update_of_ne (by decide : prN ≠ prActStk),
      Function.update_of_ne (by decide : prN ≠ prInAct),
      Function.update_of_ne (by decide : prN ≠ prDegR),
      Function.update_of_ne (by decide : prN ≠ prEx),
      Function.update_of_ne (by decide : prN ≠ prAbs),
      Function.update_of_ne (by decide : prN ≠ prCur),
      Function.update_of_ne (by decide : prN ≠ prHArr),
      Function.update_of_ne (by decide : prN ≠ prDegX),
      Function.update_of_ne (by decide : prN ≠ prPeelTop),
      Function.update_of_ne (by decide : prN ≠ prActTop),
      Function.update_of_ne (by decide : prN ≠ prM),
      Function.update_self, hpre.reg_csr]
  apply runs_assign_le (v := csrAddr + 2 * n + 1 + 2 * m)
  · simp only [Expr.eval, WordRAM.BinOp.eval, Function.update_self, h2lt, h2m, hcsrh, ↓reduceIte,
      Function.update_of_ne (by decide : prM ≠ prCsrAdjV),
      Function.update_of_ne (by decide : prM ≠ prLvlHead),
      Function.update_of_ne (by decide : prM ≠ prLvlVol),
      Function.update_of_ne (by decide : prM ≠ prFlowEnc),
      Function.update_of_ne (by decide : prM ≠ prRemArr),
      Function.update_of_ne (by decide : prM ≠ prLvlPrev),
      Function.update_of_ne (by decide : prM ≠ prLvlNext),
      Function.update_of_ne (by decide : prM ≠ prPeelStk),
      Function.update_of_ne (by decide : prM ≠ prActStk),
      Function.update_of_ne (by decide : prM ≠ prInAct),
      Function.update_of_ne (by decide : prM ≠ prDegR),
      Function.update_of_ne (by decide : prM ≠ prEx),
      Function.update_of_ne (by decide : prM ≠ prAbs),
      Function.update_of_ne (by decide : prM ≠ prCur),
      Function.update_of_ne (by decide : prM ≠ prHArr),
      Function.update_of_ne (by decide : prM ≠ prDegX),
      Function.update_of_ne (by decide : prM ≠ prPeelTop),
      Function.update_of_ne (by decide : prM ≠ prActTop)]
  · refine ⟨rfl, rfl, {
      reg_g := by simp; exact hpre.reg_g
      reg_csr := by simp; exact hpre.reg_csr
      reg_inB := by simp; exact hpre.reg_inB
      reg_outR := by simp; exact hpre.reg_outR
      reg_work := by simp; exact hpre.reg_work
      reg_ccap := by simp; exact hpre.reg_ccap
      reg_H := by simp; exact hpre.reg_H
      reg_theta := by simp; exact hpre.reg_theta
      reg_n := by simp; rfl
      reg_m := by simp; rfl
      reg_actTop := by simp
      reg_peelTop := by simp
      reg_degX := by simp
      reg_hArr := by simp; rfl
      reg_cur := by simp; rfl
      reg_abs := by simp; rfl
      reg_ex := by simp; rfl
      reg_degR := by simp; rfl
      reg_inAct := by simp; rfl
      reg_actStk := by simp; rfl
      reg_peelStk := by simp; rfl
      reg_lvlNext := by simp; rfl
      reg_lvlPrev := by simp; rfl
      reg_remArr := by simp; rfl
      reg_flowEnc := by simp; rfl
      reg_lvlVol := by simp; rfl
      reg_lvlHead := by simp; rfl
      reg_adjV := by simp; rfl
      reg_adjH := by simp; rfl }⟩
  · simp only [Expr.size]; omega

lemma initZeroVerts_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ} (st₀ : State)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hinB_w : inBAddr + cfg.G.n < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w)
    (hinB : ∀ b, b ∈ cfg.B ↔ b < cfg.G.n ∧ st₀.mem (inBAddr + b) ≠ 0) :
    Triple w p
      (fun st => st = st₀ ∧ InitPtrRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st)
      initZeroVertsStmt
      (normalPost fun st' =>
        InitPtrRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st' ∧
        st'.pos = st₀.pos ∧
        PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
          workAddr (workAddr + 11 * cfg.G.n) ∧
        (∀ u < cfg.G.n,
          st'.mem (outRAddr + u) = (if u ∈ cfg.B then 0 else 1) ∧
          st'.mem (wDegX workAddr cfg.G.n cfg.G.m cfg.H + u) = 0 ∧
          st'.mem (wHArr workAddr cfg.G.n cfg.G.m cfg.H + u) = 0 ∧
          st'.mem (wCur workAddr cfg.G.n cfg.G.m cfg.H + u) = 0 ∧
          st'.mem (wAbs workAddr cfg.G.n cfg.G.m cfg.H + u) = 0 ∧
          st'.mem (wEx workAddr cfg.G.n cfg.G.m cfg.H + u) = 0 ∧
          st'.mem (wDegR workAddr cfg.G.n cfg.G.m cfg.H + u) = 0 ∧
          st'.mem (wInAct workAddr cfg.G.n cfg.G.m cfg.H + u) = 0 ∧
          st'.mem (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H + u) = cfg.G.n ∧
          st'.mem (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H + u) = cfg.G.n))
      (fun _ => 85 * cfg.G.n + 10) := by
  intro st ω ⟨hst, hptrs⟩
  subst st
  set n := cfg.G.n
  set m := cfg.G.m
  set H := cfg.H
  have hwb := hw
  unfold PruneWordBound pruneWorkSpace at hwb
  have h0lt : 0 < 2 ^ w := by omega
  have h1lt : 1 < 2 ^ w := by omega
  have hlt_pow : ∀ x, x ≤ workAddr + (12 * n + m + 2 * H + 2) → x < 2 ^ w := fun x hx => by omega
  have hn_lt : n < 2 ^ w := by omega
  have hdisj_inB_outR := hdisj.2.2.1
  have hdisj_inB_work := hdisj.2.2.2.2.2.1
  have hdisj_outR_work := hdisj.2.2.2.2.2.2
  let eCond : Expr := .bin .lt (.reg prU) (.reg prN)
  have heSize : eCond.size = 3 := rfl
  let Inv : ℕ → State → Prop := fun k st =>
    k ≤ n ∧ st.regs prU = k ∧
    (∀ r, r ≠ prU → r ≠ prTmp1 → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    PreservedOutside2 st₀.mem st.mem outRAddr (outRAddr + n) workAddr (workAddr + 11 * n) ∧
    (∀ u < k,
      st.mem (outRAddr + u) = (if u ∈ cfg.B then 0 else 1) ∧
      st.mem (wDegX workAddr n m H + u) = 0 ∧
      st.mem (wHArr workAddr n m H + u) = 0 ∧
      st.mem (wCur workAddr n m H + u) = 0 ∧
      st.mem (wAbs workAddr n m H + u) = 0 ∧
      st.mem (wEx workAddr n m H + u) = 0 ∧
      st.mem (wDegR workAddr n m H + u) = 0 ∧
      st.mem (wInAct workAddr n m H + u) = 0 ∧
      st.mem (wLvlNext workAddr n m H + u) = n ∧
      st.mem (wLvlPrev workAddr n m H + u) = n)
  have hloop : Triple w p (Inv 0)
      (.loop eCond
        (seqStmts [
          .assign prTmp1 (.load (.bin .add (.reg prInB) (.reg prU))),
          .cond (.bin .lt (.const 0) (.reg prTmp1))
            (.store (.bin .add (.reg prOutR) (.reg prU)) (.const 0))
            (.store (.bin .add (.reg prOutR) (.reg prU)) (.const 1)),
          .store (.bin .add (.reg prDegX) (.reg prU)) (.const 0),
          .store (.bin .add (.reg prHArr) (.reg prU)) (.const 0),
          .store (.bin .add (.reg prCur) (.reg prU)) (.const 0),
          .store (.bin .add (.reg prAbs) (.reg prU)) (.const 0),
          .store (.bin .add (.reg prEx) (.reg prU)) (.const 0),
          .store (.bin .add (.reg prDegR) (.reg prU)) (.const 0),
          .store (.bin .add (.reg prInAct) (.reg prU)) (.const 0),
          .store (.bin .add (.reg prLvlNext) (.reg prU)) (.reg prN),
          .store (.bin .add (.reg prLvlPrev) (.reg prU)) (.reg prN),
          .assign prU (.bin .add (.reg prU) (.const 1))
        ]))
      (normalPost fun st => Inv n st)
      (fun _ => 85 * n + 4) := by
    apply (Triple.loop_inv (α := ℕ)
      (m := fun k => n - k) (rem := fun k => 85 * (n - k) + 4)
      (condVal := fun st => if st.regs prU < st.regs prN then 1 else 0)
      (Inv := Inv) ?_ ?_ ?_ 0).mono_cost (fun _ _ => le_rfl)
    · rintro k st ⟨_, _, hr, _, _, _⟩
      have hrn : st.regs prN = n := (hr prN (by decide) (by decide)).trans hptrs.reg_n
      simp only [eCond, Expr.eval, hrn, WordRAM.BinOp.eval]
      by_cases hcmp : st.regs prU < n <;> simp [hcmp, h1lt, h0lt]
    · rintro k st hInv heq
      rcases hInv with ⟨hk, hru, hr, hp, hpr, hall⟩
      have hrn : st.regs prN = n := (hr prN (by decide) (by decide)).trans hptrs.reg_n
      have hkn : k = n := by
        by_contra hne
        have hlt : k < n := by omega
        rw [hru, hrn] at heq; simp [hlt] at heq
      subst hkn
      exact ⟨⟨le_rfl, hru, hr, hp, hpr, hall⟩, by simp [eCond, Expr.size]⟩
    · rintro k st ⟨hk, hru, hr, hp, hpr, hall⟩ hne
      have hrn : st.regs prN = n := (hr prN (by decide) (by decide)).trans hptrs.reg_n
      have hk_lt : k < n := by
        by_contra hge
        rw [hru, hrn] at hne; simp [hge] at hne
      have hrInB : st.regs prInB = inBAddr := (hr prInB (by decide) (by decide)).trans hptrs.reg_inB
      have hrOutR : st.regs prOutR = outRAddr := (hr prOutR (by decide) (by decide)).trans hptrs.reg_outR
      have hrDX : st.regs prDegX = wDegX workAddr n m H := (hr prDegX (by decide) (by decide)).trans hptrs.reg_degX
      have hrH : st.regs prHArr = wHArr workAddr n m H := (hr prHArr (by decide) (by decide)).trans hptrs.reg_hArr
      have hrCur : st.regs prCur = wCur workAddr n m H := (hr prCur (by decide) (by decide)).trans hptrs.reg_cur
      have hrAbs : st.regs prAbs = wAbs workAddr n m H := (hr prAbs (by decide) (by decide)).trans hptrs.reg_abs
      have hrEx : st.regs prEx = wEx workAddr n m H := (hr prEx (by decide) (by decide)).trans hptrs.reg_ex
      have hrDR : st.regs prDegR = wDegR workAddr n m H := (hr prDegR (by decide) (by decide)).trans hptrs.reg_degR
      have hrIA : st.regs prInAct = wInAct workAddr n m H := (hr prInAct (by decide) (by decide)).trans hptrs.reg_inAct
      have hrLN : st.regs prLvlNext = wLvlNext workAddr n m H :=
        (hr prLvlNext (by decide) (by decide)).trans hptrs.reg_lvlNext
      have hrLP : st.regs prLvlPrev = wLvlPrev workAddr n m H :=
        (hr prLvlPrev (by decide) (by decide)).trans hptrs.reg_lvlPrev
      have hinBk : inBAddr + k < 2 ^ w := by omega
      have houtRk : outRAddr + k < 2 ^ w := by omega
      have hk1 : k + 1 < 2 ^ w := by omega
      have hdxk : wDegX workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wDegX]; omega)
      have hhk : wHArr workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wHArr]; omega)
      have hck : wCur workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wCur]; omega)
      have habk : wAbs workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wAbs]; omega)
      have hexk : wEx workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wEx]; omega)
      have hdrk : wDegR workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wDegR]; omega)
      have hiak : wInAct workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wInAct]; omega)
      have hlnk : wLvlNext workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wLvlNext]; omega)
      have hlpk : wLvlPrev workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wLvlPrev]; omega)
      have hinB_orig : st.mem (inBAddr + k) = st₀.mem (inBAddr + k) :=
        hpr (inBAddr + k) (by rcases hdisj_inB_outR with h | h <;> omega)
          (by unfold pruneWorkSpace at hdisj_inB_work; rcases hdisj_inB_work with h | h <;> omega)
      have hcond_out : Triple w p
          (fun st1 => st1 = { st with regs := Function.update st.regs prTmp1 (st₀.mem (inBAddr + k)) })
          (.cond (.bin .lt (.const 0) (.reg prTmp1))
            (.store (.bin .add (.reg prOutR) (.reg prU)) (.const 0))
            (.store (.bin .add (.reg prOutR) (.reg prU)) (.const 1)))
          (normalPost fun st' =>
            (∀ r, r ≠ prU → r ≠ prTmp1 → st'.regs r = st₀.regs r) ∧
            st'.regs prU = k ∧ st'.pos = st₀.pos ∧
            st'.mem = Function.update st.mem (outRAddr + k) (if k ∈ cfg.B then 0 else 1))
          (fun _ => 15) := by
        apply (Triple.cond_const
          (val := fun s => if 0 < s.regs prTmp1 then 1 else 0) (c_t := 5) (c_f := 5)
          (fun s hs => by
            subst s; simp only [Expr.eval, Function.update_self, h0lt, WordRAM.BinOp.eval]
            by_cases hcmp : 0 < st₀.mem (inBAddr + k) <;> simp [hcmp, h1lt, h0lt])
          ?_ ?_).mono_cost (fun _ _ => by simp [Expr.size])
        · apply Triple.store (addr := fun _ => outRAddr + k) (val := fun _ => 0)
            (fun s ⟨hs, _⟩ => by
              subst s
              exact eval_add_regs (by simp [hrOutR]) (by simp [hru]) houtRk)
            (fun _ _ => by simp [Expr.eval, h0lt])
            (fun s ⟨hs, hne⟩ => by
              subst s
              have hlt0 : 0 < st₀.mem (inBAddr + k) := by
                by_contra h'
                simp only [Function.update_self] at hne
                simp [h'] at hne
              have hkB : k ∈ cfg.B := (hinB k).mpr ⟨hk_lt, Nat.ne_of_gt hlt0⟩
              exact ⟨fun r h1 h2 => by simp [Function.update_of_ne h2, hr r h1 h2],
                by simp [hru], hp, by simp [hkB]⟩)
        · apply Triple.store (addr := fun _ => outRAddr + k) (val := fun _ => 1)
            (fun s ⟨hs, _⟩ => by
              subst s
              exact eval_add_regs (by simp [hrOutR]) (by simp [hru]) houtRk)
            (fun _ _ => by simp [Expr.eval, h1lt])
            (fun s ⟨hs, heq⟩ => by
              subst s
              have hnz0 : st₀.mem (inBAddr + k) = 0 := by
                by_contra h'
                have hpos : 0 < st₀.mem (inBAddr + k) := Nat.pos_of_ne_zero h'
                simp only [Function.update_self, hpos, ↓reduceIte] at heq
                exact Nat.one_ne_zero heq
              have hkNB : k ∉ cfg.B := fun hkB => absurd hnz0 ((hinB k).mp hkB).2
              exact ⟨fun r h1 h2 => by simp [Function.update_of_ne h2, hr r h1 h2],
                by simp [hru], hp, by simp [hkNB]⟩)
      refine ⟨80, ?_⟩
      intro st1 ω2 hst1
      subst st1
      have hbody : ∃ o st' c1,
          Runs w p ω2
            (seqStmts [
              .assign prTmp1 (.load (.bin .add (.reg prInB) (.reg prU))),
              .cond (.bin .lt (.const 0) (.reg prTmp1))
                (.store (.bin .add (.reg prOutR) (.reg prU)) (.const 0))
                (.store (.bin .add (.reg prOutR) (.reg prU)) (.const 1)),
              .store (.bin .add (.reg prDegX) (.reg prU)) (.const 0),
              .store (.bin .add (.reg prHArr) (.reg prU)) (.const 0),
              .store (.bin .add (.reg prCur) (.reg prU)) (.const 0),
              .store (.bin .add (.reg prAbs) (.reg prU)) (.const 0),
              .store (.bin .add (.reg prEx) (.reg prU)) (.const 0),
              .store (.bin .add (.reg prDegR) (.reg prU)) (.const 0),
              .store (.bin .add (.reg prInAct) (.reg prU)) (.const 0),
              .store (.bin .add (.reg prLvlNext) (.reg prU)) (.reg prN),
              .store (.bin .add (.reg prLvlPrev) (.reg prU)) (.reg prN),
              .assign prU (.bin .add (.reg prU) (.const 1))
            ])
            st o st' c1 ∧
          normalPost (fun st' => Inv (k + 1) st') o st' ∧ c1 ≤ 80 := by
        dsimp only [seqStmts]
        refine runs_start_le (T := 80) ?_
        apply runs_seq_assign_le (v := st₀.mem (inBAddr + k))
        · simp only [Expr.eval, hrInB, hru, WordRAM.BinOp.eval, hinBk, ↓reduceIte,
            Option.map_some, hinB_orig]
        apply runs_seq_triple_le hcond_out
        · rfl
        intro st2 ⟨hr2, hru2, hp2, hm2⟩
        have hr2_DX : st2.regs prDegX = wDegX workAddr n m H := (hr2 prDegX (by decide) (by decide)).trans hptrs.reg_degX
        have hr2_H : st2.regs prHArr = wHArr workAddr n m H := (hr2 prHArr (by decide) (by decide)).trans hptrs.reg_hArr
        have hr2_Cur : st2.regs prCur = wCur workAddr n m H := (hr2 prCur (by decide) (by decide)).trans hptrs.reg_cur
        have hr2_Abs : st2.regs prAbs = wAbs workAddr n m H := (hr2 prAbs (by decide) (by decide)).trans hptrs.reg_abs
        have hr2_Ex : st2.regs prEx = wEx workAddr n m H := (hr2 prEx (by decide) (by decide)).trans hptrs.reg_ex
        have hr2_DR : st2.regs prDegR = wDegR workAddr n m H := (hr2 prDegR (by decide) (by decide)).trans hptrs.reg_degR
        have hr2_IA : st2.regs prInAct = wInAct workAddr n m H := (hr2 prInAct (by decide) (by decide)).trans hptrs.reg_inAct
        have hr2_LN : st2.regs prLvlNext = wLvlNext workAddr n m H :=
          (hr2 prLvlNext (by decide) (by decide)).trans hptrs.reg_lvlNext
        have hr2_LP : st2.regs prLvlPrev = wLvlPrev workAddr n m H :=
          (hr2 prLvlPrev (by decide) (by decide)).trans hptrs.reg_lvlPrev
        have hr2_N : st2.regs prN = n := (hr2 prN (by decide) (by decide)).trans hptrs.reg_n
        apply runs_seq_store_le (x := wDegX workAddr n m H + k) (v := 0)
        · exact eval_add_regs hr2_DX hru2 hdxk
        · simp [Expr.eval, h0lt]
        apply runs_seq_store_le (x := wHArr workAddr n m H + k) (v := 0)
        · exact eval_add_regs hr2_H hru2 hhk
        · simp [Expr.eval, h0lt]
        apply runs_seq_store_le (x := wCur workAddr n m H + k) (v := 0)
        · exact eval_add_regs hr2_Cur hru2 hck
        · simp [Expr.eval, h0lt]
        apply runs_seq_store_le (x := wAbs workAddr n m H + k) (v := 0)
        · exact eval_add_regs hr2_Abs hru2 habk
        · simp [Expr.eval, h0lt]
        apply runs_seq_store_le (x := wEx workAddr n m H + k) (v := 0)
        · exact eval_add_regs hr2_Ex hru2 hexk
        · simp [Expr.eval, h0lt]
        apply runs_seq_store_le (x := wDegR workAddr n m H + k) (v := 0)
        · exact eval_add_regs hr2_DR hru2 hdrk
        · simp [Expr.eval, h0lt]
        apply runs_seq_store_le (x := wInAct workAddr n m H + k) (v := 0)
        · exact eval_add_regs hr2_IA hru2 hiak
        · simp [Expr.eval, h0lt]
        apply runs_seq_store_le (x := wLvlNext workAddr n m H + k) (v := n)
        · exact eval_add_regs hr2_LN hru2 hlnk
        · exact eval_reg hr2_N hn_lt
        apply runs_seq_store_le (x := wLvlPrev workAddr n m H + k) (v := n)
        · exact eval_add_regs hr2_LP hru2 hlpk
        · exact eval_reg hr2_N hn_lt
        apply runs_assign_le (v := k + 1)
        · simp only [Expr.eval, hru2, h1lt, WordRAM.BinOp.eval, hk1, ↓reduceIte]
        · simp only [normalPost]
          refine ⟨hk_lt, by simp, fun r h1 h2 => ?_, hp2, ?_, ?_⟩
          · dsimp only
            rw [Function.update_of_ne h1]
            exact hr2 r h1 h2
          · apply init_preservedOutside2_trans hpr
            rw [hm2]
            refine init_preservedOutside2_trans (init_preservedOutside2_update_left (by omega) (by omega))
              (init_preservedOutside2_trans (init_preservedOutside2_update_right (by dsimp [wDegX]; omega) (by dsimp [wDegX]; omega))
              (init_preservedOutside2_trans (init_preservedOutside2_update_right (by dsimp [wHArr]; omega) (by dsimp [wHArr]; omega))
              (init_preservedOutside2_trans (init_preservedOutside2_update_right (by dsimp [wCur]; omega) (by dsimp [wCur]; omega))
              (init_preservedOutside2_trans (init_preservedOutside2_update_right (by dsimp [wAbs]; omega) (by dsimp [wAbs]; omega))
              (init_preservedOutside2_trans (init_preservedOutside2_update_right (by dsimp [wEx]; omega) (by dsimp [wEx]; omega))
              (init_preservedOutside2_trans (init_preservedOutside2_update_right (by dsimp [wDegR]; omega) (by dsimp [wDegR]; omega))
              (init_preservedOutside2_trans (init_preservedOutside2_update_right (by dsimp [wInAct]; omega) (by dsimp [wInAct]; omega))
              (init_preservedOutside2_trans (init_preservedOutside2_update_right (by dsimp [wLvlNext]; omega) (by dsimp [wLvlNext]; omega))
                (init_preservedOutside2_update_right (by dsimp [wLvlPrev]; omega) (by dsimp [wLvlPrev]; omega))))))))))
          · intro u hu
            dsimp only
            have hdisj_out : ∀ base, wDegX workAddr n m H ≤ base → base ≤ wLvlPrev workAddr n m H →
                ∀ x < n, ∀ y < n, base + x ≠ outRAddr + y := by
              intro base hb1 hb2 x hx y hy heq
              dsimp [wDegX, wLvlPrev] at hb1 hb2
              unfold pruneWorkSpace at hdisj_outR_work
              rcases hdisj_outR_work with h | h <;> omega
            have hne_work_diff : ∀ s t : ℕ, s ≠ t → ∀ x < n, ∀ y < n,
                workAddr + s * n + x ≠ workAddr + t * n + y := by
              intro s t hst x hx y hy heq
              have heq' : s * n + x = t * n + y := by omega
              rcases lt_or_gt_of_ne hst with hlt | hgt
              · have hm : (s + 1) * n ≤ t * n := Nat.mul_le_mul_right n hlt
                rw [Nat.add_mul, Nat.one_mul] at hm; omega
              · have hm : (t + 1) * n ≤ s * n := Nat.mul_le_mul_right n hgt
                rw [Nat.add_mul, Nat.one_mul] at hm; omega
            have hne_k : ∀ s t : ℕ, s ≠ t →
                workAddr + s * n + k ≠ workAddr + t * n + k :=
              fun s t hst => hne_work_diff s t hst k hk_lt k hk_lt
            by_cases huk : u = k
            · subst u
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · have hno : ∀ t ≤ 10, outRAddr + k ≠ workAddr + t * n + k := fun t ht =>
                  (hdisj_out (workAddr + t * n) (by dsimp [wDegX]; omega)
                    (by dsimp [wLvlPrev]; have := Nat.mul_le_mul_right n ht; omega) k hk_lt k hk_lt).symm
                rw [Function.update_of_ne (by dsimp [wLvlPrev]; simpa [Nat.add_assoc] using hno 10 (by omega)),
                    Function.update_of_ne (by dsimp [wLvlNext]; simpa [Nat.add_assoc] using hno 9 (by omega)),
                    Function.update_of_ne (by dsimp [wInAct]; simpa [Nat.add_assoc] using hno 6 (by omega)),
                    Function.update_of_ne (by dsimp [wDegR]; simpa [Nat.add_assoc] using hno 5 (by omega)),
                    Function.update_of_ne (by dsimp [wEx]; simpa [Nat.add_assoc] using hno 4 (by omega)),
                    Function.update_of_ne (by dsimp [wAbs]; simpa [Nat.add_assoc] using hno 3 (by omega)),
                    Function.update_of_ne (by dsimp [wCur]; simpa [Nat.add_assoc] using hno 2 (by omega)),
                    Function.update_of_ne (by dsimp [wHArr]; simpa [Nat.add_assoc] using hno 1 (by omega)),
                    Function.update_of_ne (by dsimp [wDegX]; simpa [Nat.add_assoc] using hno 0 (by omega)),
                    hm2, Function.update_self]
              · rw [Function.update_of_ne (by dsimp [wDegX, wLvlPrev]; simpa [Nat.add_assoc] using hne_k 0 10 (by decide)),
                    Function.update_of_ne (by dsimp [wDegX, wLvlNext]; simpa [Nat.add_assoc] using hne_k 0 9 (by decide)),
                    Function.update_of_ne (by dsimp [wDegX, wInAct]; simpa [Nat.add_assoc] using hne_k 0 6 (by decide)),
                    Function.update_of_ne (by dsimp [wDegX, wDegR]; simpa [Nat.add_assoc] using hne_k 0 5 (by decide)),
                    Function.update_of_ne (by dsimp [wDegX, wEx]; simpa [Nat.add_assoc] using hne_k 0 4 (by decide)),
                    Function.update_of_ne (by dsimp [wDegX, wAbs]; simpa [Nat.add_assoc] using hne_k 0 3 (by decide)),
                    Function.update_of_ne (by dsimp [wDegX, wCur]; simpa [Nat.add_assoc] using hne_k 0 2 (by decide)),
                    Function.update_of_ne (by dsimp [wDegX, wHArr]; simpa [Nat.add_assoc] using hne_k 0 1 (by decide))]
                exact Function.update_self ..
              · rw [Function.update_of_ne (by dsimp [wHArr, wLvlPrev]; simpa [Nat.add_assoc] using hne_k 1 10 (by decide)),
                    Function.update_of_ne (by dsimp [wHArr, wLvlNext]; simpa [Nat.add_assoc] using hne_k 1 9 (by decide)),
                    Function.update_of_ne (by dsimp [wHArr, wInAct]; simpa [Nat.add_assoc] using hne_k 1 6 (by decide)),
                    Function.update_of_ne (by dsimp [wHArr, wDegR]; simpa [Nat.add_assoc] using hne_k 1 5 (by decide)),
                    Function.update_of_ne (by dsimp [wHArr, wEx]; simpa [Nat.add_assoc] using hne_k 1 4 (by decide)),
                    Function.update_of_ne (by dsimp [wHArr, wAbs]; simpa [Nat.add_assoc] using hne_k 1 3 (by decide)),
                    Function.update_of_ne (by dsimp [wHArr, wCur]; simpa [Nat.add_assoc] using hne_k 1 2 (by decide))]
                exact Function.update_self ..
              · rw [Function.update_of_ne (by dsimp [wCur, wLvlPrev]; simpa [Nat.add_assoc] using hne_k 2 10 (by decide)),
                    Function.update_of_ne (by dsimp [wCur, wLvlNext]; simpa [Nat.add_assoc] using hne_k 2 9 (by decide)),
                    Function.update_of_ne (by dsimp [wCur, wInAct]; simpa [Nat.add_assoc] using hne_k 2 6 (by decide)),
                    Function.update_of_ne (by dsimp [wCur, wDegR]; simpa [Nat.add_assoc] using hne_k 2 5 (by decide)),
                    Function.update_of_ne (by dsimp [wCur, wEx]; simpa [Nat.add_assoc] using hne_k 2 4 (by decide)),
                    Function.update_of_ne (by dsimp [wCur, wAbs]; simpa [Nat.add_assoc] using hne_k 2 3 (by decide))]
                exact Function.update_self ..
              · rw [Function.update_of_ne (by dsimp [wAbs, wLvlPrev]; simpa [Nat.add_assoc] using hne_k 3 10 (by decide)),
                    Function.update_of_ne (by dsimp [wAbs, wLvlNext]; simpa [Nat.add_assoc] using hne_k 3 9 (by decide)),
                    Function.update_of_ne (by dsimp [wAbs, wInAct]; simpa [Nat.add_assoc] using hne_k 3 6 (by decide)),
                    Function.update_of_ne (by dsimp [wAbs, wDegR]; simpa [Nat.add_assoc] using hne_k 3 5 (by decide)),
                    Function.update_of_ne (by dsimp [wAbs, wEx]; simpa [Nat.add_assoc] using hne_k 3 4 (by decide))]
                exact Function.update_self ..
              · rw [Function.update_of_ne (by dsimp [wEx, wLvlPrev]; simpa [Nat.add_assoc] using hne_k 4 10 (by decide)),
                    Function.update_of_ne (by dsimp [wEx, wLvlNext]; simpa [Nat.add_assoc] using hne_k 4 9 (by decide)),
                    Function.update_of_ne (by dsimp [wEx, wInAct]; simpa [Nat.add_assoc] using hne_k 4 6 (by decide)),
                    Function.update_of_ne (by dsimp [wEx, wDegR]; simpa [Nat.add_assoc] using hne_k 4 5 (by decide))]
                exact Function.update_self ..
              · rw [Function.update_of_ne (by dsimp [wDegR, wLvlPrev]; simpa [Nat.add_assoc] using hne_k 5 10 (by decide)),
                    Function.update_of_ne (by dsimp [wDegR, wLvlNext]; simpa [Nat.add_assoc] using hne_k 5 9 (by decide)),
                    Function.update_of_ne (by dsimp [wDegR, wInAct]; simpa [Nat.add_assoc] using hne_k 5 6 (by decide))]
                exact Function.update_self ..
              · rw [Function.update_of_ne (by dsimp [wInAct, wLvlPrev]; simpa [Nat.add_assoc] using hne_k 6 10 (by decide)),
                    Function.update_of_ne (by dsimp [wInAct, wLvlNext]; simpa [Nat.add_assoc] using hne_k 6 9 (by decide))]
                exact Function.update_self ..
              · rw [Function.update_of_ne (by dsimp [wLvlNext, wLvlPrev]; simpa [Nat.add_assoc] using hne_k 9 10 (by decide))]
                exact Function.update_self ..
              · exact Function.update_self ..
            · have hukt : u < k := by omega
              have hu_lt : u < n := by omega
              have hprev := hall u hukt
              have hmem_work : ∀ t ≤ 10,
                  Function.update (Function.update (Function.update (Function.update (Function.update
                    (Function.update (Function.update (Function.update (Function.update st2.mem
                      (wDegX workAddr n m H + k) 0) (wHArr workAddr n m H + k) 0)
                      (wCur workAddr n m H + k) 0) (wAbs workAddr n m H + k) 0)
                      (wEx workAddr n m H + k) 0) (wDegR workAddr n m H + k) 0)
                      (wInAct workAddr n m H + k) 0) (wLvlNext workAddr n m H + k) n)
                      (wLvlPrev workAddr n m H + k) n (workAddr + t * n + u) = st.mem (workAddr + t * n + u) := by
                intro t ht
                have hne_st : ∀ s : ℕ, workAddr + t * n + u ≠ workAddr + s * n + k := by
                  intro s
                  by_cases hts : t = s
                  · subst hts; omega
                  · exact hne_work_diff t s hts u hu_lt k hk_lt
                have hne_out : workAddr + t * n + u ≠ outRAddr + k :=
                  hdisj_out (workAddr + t * n) (by dsimp [wDegX]; omega)
                    (by dsimp [wLvlPrev]; have := Nat.mul_le_mul_right n ht; omega) u hu_lt k hk_lt
                rw [Function.update_of_ne (by dsimp [wLvlPrev]; simpa [Nat.add_assoc] using hne_st 10),
                    Function.update_of_ne (by dsimp [wLvlNext]; simpa [Nat.add_assoc] using hne_st 9),
                    Function.update_of_ne (by dsimp [wInAct]; simpa [Nat.add_assoc] using hne_st 6),
                    Function.update_of_ne (by dsimp [wDegR]; simpa [Nat.add_assoc] using hne_st 5),
                    Function.update_of_ne (by dsimp [wEx]; simpa [Nat.add_assoc] using hne_st 4),
                    Function.update_of_ne (by dsimp [wAbs]; simpa [Nat.add_assoc] using hne_st 3),
                    Function.update_of_ne (by dsimp [wCur]; simpa [Nat.add_assoc] using hne_st 2),
                    Function.update_of_ne (by dsimp [wHArr]; simpa [Nat.add_assoc] using hne_st 1),
                    Function.update_of_ne (by dsimp [wDegX]; simpa [Nat.add_assoc] using hne_st 0),
                    hm2, Function.update_of_ne hne_out]
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · have hno : ∀ t ≤ 10, outRAddr + u ≠ workAddr + t * n + k := fun t ht =>
                  (hdisj_out (workAddr + t * n) (by dsimp [wDegX]; omega)
                    (by dsimp [wLvlPrev]; have := Nat.mul_le_mul_right n ht; omega) k hk_lt u hu_lt).symm
                rw [Function.update_of_ne (by dsimp [wLvlPrev]; simpa [Nat.add_assoc] using hno 10 (by omega)),
                    Function.update_of_ne (by dsimp [wLvlNext]; simpa [Nat.add_assoc] using hno 9 (by omega)),
                    Function.update_of_ne (by dsimp [wInAct]; simpa [Nat.add_assoc] using hno 6 (by omega)),
                    Function.update_of_ne (by dsimp [wDegR]; simpa [Nat.add_assoc] using hno 5 (by omega)),
                    Function.update_of_ne (by dsimp [wEx]; simpa [Nat.add_assoc] using hno 4 (by omega)),
                    Function.update_of_ne (by dsimp [wAbs]; simpa [Nat.add_assoc] using hno 3 (by omega)),
                    Function.update_of_ne (by dsimp [wCur]; simpa [Nat.add_assoc] using hno 2 (by omega)),
                    Function.update_of_ne (by dsimp [wHArr]; simpa [Nat.add_assoc] using hno 1 (by omega)),
                    Function.update_of_ne (by dsimp [wDegX]; simpa [Nat.add_assoc] using hno 0 (by omega)),
                    hm2, Function.update_of_ne (by omega)]
                exact hprev.1
              · trans st.mem (wDegX workAddr n m H + u)
                · simpa [wDegX] using hmem_work 0 (by omega)
                · exact hprev.2.1
              · trans st.mem (wHArr workAddr n m H + u)
                · simpa [wHArr] using hmem_work 1 (by omega)
                · exact hprev.2.2.1
              · trans st.mem (wCur workAddr n m H + u)
                · simpa [wCur] using hmem_work 2 (by omega)
                · exact hprev.2.2.2.1
              · trans st.mem (wAbs workAddr n m H + u)
                · simpa [wAbs] using hmem_work 3 (by omega)
                · exact hprev.2.2.2.2.1
              · trans st.mem (wEx workAddr n m H + u)
                · simpa [wEx] using hmem_work 4 (by omega)
                · exact hprev.2.2.2.2.2.1
              · trans st.mem (wDegR workAddr n m H + u)
                · simpa [wDegR] using hmem_work 5 (by omega)
                · exact hprev.2.2.2.2.2.2.1
              · trans st.mem (wInAct workAddr n m H + u)
                · simpa [wInAct] using hmem_work 6 (by omega)
                · exact hprev.2.2.2.2.2.2.2.1
              · trans st.mem (wLvlNext workAddr n m H + u)
                · simpa [wLvlNext] using hmem_work 9 (by omega)
                · exact hprev.2.2.2.2.2.2.2.2.1
              · trans st.mem (wLvlPrev workAddr n m H + u)
                · simpa [wLvlPrev] using hmem_work 10 (by omega)
                · exact hprev.2.2.2.2.2.2.2.2.2
        · simp only [Expr.size]; omega
      obtain ⟨o, st_next, c_b, hrun_b, hpost_b, hc_b⟩ := hbody
      cases o with
      | returned _ => exact absurd hpost_b (by simp [normalPost])
      | normal =>
          exact ⟨.normal, st_next, c_b, hrun_b, ⟨k + 1, hpost_b, by omega, by omega⟩, hc_b⟩
  refine runs_start_le ?_
  dsimp only [initZeroVertsStmt, seqStmts]
  apply runs_seq_assign_le (v := 0)
  · simp [Expr.eval, h0lt]
  apply runs_triple_le hloop
  · refine ⟨Nat.zero_le _, by simp, fun r h1 _ => by simp [Function.update_of_ne h1],
      rfl, fun _ _ _ => rfl, fun u hu => (Nat.not_lt_zero u hu).elim⟩
  · intro o st1 h1
    cases o with
    | returned _ => exact absurd h1 (by simp [normalPost])
    | normal =>
        rcases h1 with ⟨_, _, hr1, hp1, hpr1, hall1⟩
        exact ⟨{
    reg_g := (hr1 prG (by decide) (by decide)).trans hptrs.reg_g
    reg_csr := (hr1 prCsr (by decide) (by decide)).trans hptrs.reg_csr
    reg_inB := (hr1 prInB (by decide) (by decide)).trans hptrs.reg_inB
    reg_outR := (hr1 prOutR (by decide) (by decide)).trans hptrs.reg_outR
    reg_work := (hr1 prWork (by decide) (by decide)).trans hptrs.reg_work
    reg_ccap := (hr1 prCcap (by decide) (by decide)).trans hptrs.reg_ccap
    reg_H := (hr1 prH (by decide) (by decide)).trans hptrs.reg_H
    reg_theta := (hr1 prTheta (by decide) (by decide)).trans hptrs.reg_theta
    reg_n := (hr1 prN (by decide) (by decide)).trans hptrs.reg_n
    reg_m := (hr1 prM (by decide) (by decide)).trans hptrs.reg_m
    reg_actTop := (hr1 prActTop (by decide) (by decide)).trans hptrs.reg_actTop
    reg_peelTop := (hr1 prPeelTop (by decide) (by decide)).trans hptrs.reg_peelTop
    reg_degX := (hr1 prDegX (by decide) (by decide)).trans hptrs.reg_degX
    reg_hArr := (hr1 prHArr (by decide) (by decide)).trans hptrs.reg_hArr
    reg_cur := (hr1 prCur (by decide) (by decide)).trans hptrs.reg_cur
    reg_abs := (hr1 prAbs (by decide) (by decide)).trans hptrs.reg_abs
    reg_ex := (hr1 prEx (by decide) (by decide)).trans hptrs.reg_ex
    reg_degR := (hr1 prDegR (by decide) (by decide)).trans hptrs.reg_degR
    reg_inAct := (hr1 prInAct (by decide) (by decide)).trans hptrs.reg_inAct
    reg_actStk := (hr1 prActStk (by decide) (by decide)).trans hptrs.reg_actStk
    reg_peelStk := (hr1 prPeelStk (by decide) (by decide)).trans hptrs.reg_peelStk
    reg_lvlNext := (hr1 prLvlNext (by decide) (by decide)).trans hptrs.reg_lvlNext
    reg_lvlPrev := (hr1 prLvlPrev (by decide) (by decide)).trans hptrs.reg_lvlPrev
    reg_remArr := (hr1 prRemArr (by decide) (by decide)).trans hptrs.reg_remArr
    reg_flowEnc := (hr1 prFlowEnc (by decide) (by decide)).trans hptrs.reg_flowEnc
    reg_lvlVol := (hr1 prLvlVol (by decide) (by decide)).trans hptrs.reg_lvlVol
    reg_lvlHead := (hr1 prLvlHead (by decide) (by decide)).trans hptrs.reg_lvlHead
    reg_adjV := (hr1 prCsrAdjV (by decide) (by decide)).trans hptrs.reg_adjV
    reg_adjH := (hr1 prCsrAdjH (by decide) (by decide)).trans hptrs.reg_adjH },
    hp1, hpr1, hall1⟩
  · simp only [Expr.size]; omega


end MinCostFlow.Expander
