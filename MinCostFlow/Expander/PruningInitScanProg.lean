module

public import MinCostFlow.Expander.PruningInitVertsProg

/-!
# WordRAM Pruning Init: Zero Levels, Zero Flows, and Scan-Edge Step
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

lemma initZeroLevels_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ} (st₀ : State)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr) :
    Triple w p
      (fun st => st = st₀ ∧ InitPtrRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st)
      initZeroLevelsStmt
      (normalPost fun st' =>
        InitPtrRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st' ∧
        st'.pos = st₀.pos ∧
        MemFrame st₀.mem st'.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H)
          (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
        (∀ ℓ < cfg.H + 1,
          st'.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) = 0 ∧
          st'.mem (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ) = cfg.G.n))
      (fun _ => 25 * (cfg.H + 1) + 12) := by
  intro st ω ⟨hst, hptrs⟩
  subst st
  set n := cfg.G.n
  set m := cfg.G.m
  set H := cfg.H
  have hwb := hw
  unfold PruneWordBound pruneWorkSpace at hwb
  have h0lt : 0 < 2 ^ w := by omega
  have h1lt : 1 < 2 ^ w := by omega
  have hn_lt : n < 2 ^ w := by omega
  have hH1_lt : H + 1 < 2 ^ w := by omega
  have hlt_pow : ∀ x, x ≤ workAddr + (12 * n + m + 2 * H + 2) → x < 2 ^ w := fun x hx => by omega
  let eCond : Expr := .bin .lt (.reg prI) (.reg prTmp1)
  have heSize : eCond.size = 3 := rfl
  let Inv : ℕ → State → Prop := fun k st =>
    k ≤ H + 1 ∧ st.regs prI = k ∧ st.regs prTmp1 = H + 1 ∧
    (∀ r, r ≠ prI → r ≠ prTmp1 → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame st₀.mem st.mem (wLvlVol workAddr n m H) (workAddr + (12 * n + m + 2 * H + 2)) ∧
    (∀ ℓ < k,
      st.mem (wLvlVol workAddr n m H + ℓ) = 0 ∧
      st.mem (wLvlHead workAddr n m H + ℓ) = n)
  have hloop : Triple w p (Inv 0)
      (.loop eCond
        (seqStmts [
          .store (.bin .add (.reg prLvlVol) (.reg prI)) (.const 0),
          .store (.bin .add (.reg prLvlHead) (.reg prI)) (.reg prN),
          .assign prI (.bin .add (.reg prI) (.const 1))
        ]))
      (normalPost fun st => Inv (H + 1) st)
      (fun _ => 25 * (H + 1) + 4) := by
    apply (Triple.loop_inv (α := ℕ)
      (m := fun k => H + 1 - k) (rem := fun k => 25 * (H + 1 - k) + 4)
      (condVal := fun st => if st.regs prI < st.regs prTmp1 then 1 else 0)
      (Inv := Inv) ?_ ?_ ?_ 0).mono_cost (fun _ _ => le_rfl)
    · rintro k st ⟨_, _, hrt, _, _, _, _⟩
      simp only [eCond, Expr.eval, hrt, WordRAM.BinOp.eval]
      by_cases hcmp : st.regs prI < H + 1 <;> simp [hcmp, h1lt, h0lt]
    · rintro k st hInv heq
      rcases hInv with ⟨hk, hri, hrt, hr, hp, hmf, hall⟩
      have hkEq : k = H + 1 := by
        by_contra hne
        have hlt : k < H + 1 := by omega
        rw [hri, hrt] at heq; simp [hlt] at heq
      subst hkEq
      exact ⟨⟨le_rfl, hri, hrt, hr, hp, hmf, hall⟩, by simp [eCond, Expr.size]⟩
    · rintro k st ⟨hk, hri, hrt, hr, hp, hmf, hall⟩ hne
      have hk_lt : k < H + 1 := by
        by_contra hge
        rw [hri, hrt] at hne; simp [hge] at hne
      have hrN : st.regs prN = n := (hr prN (by decide) (by decide)).trans hptrs.reg_n
      have hrLV : st.regs prLvlVol = wLvlVol workAddr n m H :=
        (hr prLvlVol (by decide) (by decide)).trans hptrs.reg_lvlVol
      have hrLH : st.regs prLvlHead = wLvlHead workAddr n m H :=
        (hr prLvlHead (by decide) (by decide)).trans hptrs.reg_lvlHead
      have hvk : wLvlVol workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wLvlVol]; omega)
      have hhk : wLvlHead workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wLvlHead]; omega)
      have hk1 : k + 1 < 2 ^ w := by omega
      have hne_vh : wLvlHead workAddr n m H + k ≠ wLvlVol workAddr n m H + k := by
        dsimp [wLvlHead, wLvlVol]; omega
      refine ⟨21, ?_⟩
      intro st1 ω2 hst1
      subst st1
      have hbody : ∃ o st' c1,
          Runs w p ω2
            (seqStmts [
              .store (.bin .add (.reg prLvlVol) (.reg prI)) (.const 0),
              .store (.bin .add (.reg prLvlHead) (.reg prI)) (.reg prN),
              .assign prI (.bin .add (.reg prI) (.const 1))
            ]) st o st' c1 ∧
          normalPost (fun st' => Inv (k + 1) st') o st' ∧ c1 ≤ 21 := by
        dsimp only [seqStmts]
        refine runs_start_le (T := 21) ?_
        apply runs_seq_store_le (x := wLvlVol workAddr n m H + k) (v := 0)
        · exact eval_add_regs hrLV hri hvk
        · simp [Expr.eval, h0lt]
        apply runs_seq_store_le (x := wLvlHead workAddr n m H + k) (v := n)
        · exact eval_add_regs hrLH hri hhk
        · exact eval_reg hrN hn_lt
        apply runs_assign_le (v := k + 1)
        · simp only [Expr.eval, hri, h1lt, WordRAM.BinOp.eval, hk1, ↓reduceIte]
        · refine ⟨hk_lt, by simp,
            by simp [hrt],
            fun r h1 h2 => by simp [Function.update_of_ne h1, hr r h1 h2], hp, ?_, ?_⟩
          · exact memFrame_trans hmf
              (memFrame_trans
                (memFrame_update_in (by dsimp [wLvlVol]; omega) (by dsimp [wLvlVol]; omega))
                (memFrame_update_in (by dsimp [wLvlHead, wLvlVol]; omega) (by dsimp [wLvlHead]; omega)))
          · intro ℓ hℓ
            dsimp only
            by_cases hℓk : ℓ = k
            · subst hℓk
              refine ⟨?_, by simp⟩
              rw [Function.update_of_ne (by dsimp [wLvlVol, wLvlHead]; omega), Function.update_self]
            · have hℓ' : ℓ < k := by omega
              refine ⟨?_, ?_⟩
              · rw [Function.update_of_ne (by dsimp [wLvlVol, wLvlHead]; omega),
                    Function.update_of_ne (by omega)]
                exact (hall ℓ hℓ').1
              · rw [Function.update_of_ne (by omega),
                    Function.update_of_ne (by dsimp [wLvlHead, wLvlVol]; omega)]
                exact (hall ℓ hℓ').2
        · simp only [Expr.size]; omega
      obtain ⟨o, st_next, c_b, hrun_b, hpost_b, hc_b⟩ := hbody
      cases o with
      | returned _ => exact absurd hpost_b (by simp [normalPost])
      | normal =>
          exact ⟨.normal, st_next, c_b, hrun_b, ⟨k + 1, hpost_b, by omega, by omega⟩, hc_b⟩
  refine runs_start_le ?_
  dsimp only [initZeroLevelsStmt, seqStmts]
  apply runs_seq_assign_le (v := 0)
  · simp [Expr.eval, h0lt]
  apply runs_seq_assign_le (v := H + 1)
  · simp only [Expr.eval, Function.update_of_ne (by decide : prH ≠ prI),
      (show st₀.regs prH = H from hptrs.reg_H), h1lt, WordRAM.BinOp.eval, hH1_lt, ↓reduceIte]
  apply runs_triple_le hloop
  · refine ⟨Nat.zero_le _, by simp,
      by simp, fun r h1 h2 => by simp [Function.update_of_ne h2, Function.update_of_ne h1],
      rfl, fun _ _ => rfl, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  · intro o st1 h1
    cases o with
    | returned _ => exact absurd h1 (by simp [normalPost])
    | normal =>
        rcases h1 with ⟨_, _, _, hr1, hp1, hmf1, hall1⟩
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
    hp1, hmf1, hall1⟩
  · simp only [Expr.size]; omega

lemma initZeroFlows_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ} (st₀ : State)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr) :
    Triple w p
      (fun st => st = st₀ ∧ InitPtrRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st)
      initZeroFlowsStmt
      (normalPost fun st' =>
        InitPtrRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st' ∧
        st'.pos = st₀.pos ∧
        MemFrame st₀.mem st'.mem (wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H)
          (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H) ∧
        (∀ idx < cfg.G.m,
          st'.mem (wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx) = cfg.C_cap))
      (fun _ => 20 * cfg.G.m + 10) := by
  intro st ω ⟨hst, hptrs⟩
  subst st
  set n := cfg.G.n
  set m := cfg.G.m
  set H := cfg.H
  have hwb := hw
  unfold PruneWordBound pruneWorkSpace at hwb
  have h0lt : 0 < 2 ^ w := by omega
  have h1lt : 1 < 2 ^ w := by omega
  have hC_lt : cfg.C_cap < 2 ^ w := by omega
  have hlt_pow : ∀ x, x ≤ workAddr + (12 * n + m + 2 * H + 2) → x < 2 ^ w := fun x hx => by omega
  let eCond : Expr := .bin .lt (.reg prI) (.reg prM)
  have heSize : eCond.size = 3 := rfl
  let Inv : ℕ → State → Prop := fun k st =>
    k ≤ m ∧ st.regs prI = k ∧
    (∀ r, r ≠ prI → st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame st₀.mem st.mem (wFlowEnc workAddr n m H) (wLvlVol workAddr n m H) ∧
    (∀ idx < k, st.mem (wFlowEnc workAddr n m H + idx) = cfg.C_cap)
  have hloop : Triple w p (Inv 0)
      (.loop eCond
        (seqStmts [
          .store (.bin .add (.reg prFlowEnc) (.reg prI)) (.reg prCcap),
          .assign prI (.bin .add (.reg prI) (.const 1))
        ]))
      (normalPost fun st => Inv m st)
      (fun _ => 20 * m + 4) := by
    apply (Triple.loop_inv (α := ℕ)
      (m := fun k => m - k) (rem := fun k => 20 * (m - k) + 4)
      (condVal := fun st => if st.regs prI < st.regs prM then 1 else 0)
      (Inv := Inv) ?_ ?_ ?_ 0).mono_cost (fun _ _ => le_rfl)
    · rintro k st ⟨_, _, hr, _, _, _⟩
      have hrm : st.regs prM = m := (hr prM (by decide)).trans hptrs.reg_m
      simp only [eCond, Expr.eval, hrm, WordRAM.BinOp.eval]
      by_cases hcmp : st.regs prI < m <;> simp [hcmp, h1lt, h0lt]
    · rintro k st hInv heq
      rcases hInv with ⟨hk, hri, hr, hp, hmf, hall⟩
      have hrm : st.regs prM = m := (hr prM (by decide)).trans hptrs.reg_m
      have hkEq : k = m := by
        by_contra hne
        have hlt : k < m := by omega
        rw [hri, hrm] at heq; simp [hlt] at heq
      subst hkEq
      exact ⟨⟨le_rfl, hri, hr, hp, hmf, hall⟩, by simp [eCond, Expr.size]⟩
    · rintro k st ⟨hk, hri, hr, hp, hmf, hall⟩ hne
      have hrm : st.regs prM = m := (hr prM (by decide)).trans hptrs.reg_m
      have hk_lt : k < m := by
        by_contra hge
        rw [hri, hrm] at hne; simp [hge] at hne
      have hrFE : st.regs prFlowEnc = wFlowEnc workAddr n m H :=
        (hr prFlowEnc (by decide)).trans hptrs.reg_flowEnc
      have hrCC : st.regs prCcap = cfg.C_cap := (hr prCcap (by decide)).trans hptrs.reg_ccap
      have hfk : wFlowEnc workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wFlowEnc]; omega)
      have hk1 : k + 1 < 2 ^ w := by omega
      refine ⟨16, ?_⟩
      intro st1 ω2 hst1
      subst st1
      have hbody : ∃ o st' c1,
          Runs w p ω2
            (seqStmts [
              .store (.bin .add (.reg prFlowEnc) (.reg prI)) (.reg prCcap),
              .assign prI (.bin .add (.reg prI) (.const 1))
            ]) st o st' c1 ∧
          normalPost (fun st' => Inv (k + 1) st') o st' ∧ c1 ≤ 16 := by
        dsimp only [seqStmts]
        refine runs_start_le (T := 16) ?_
        apply runs_seq_store_le (x := wFlowEnc workAddr n m H + k) (v := cfg.C_cap)
        · exact eval_add_regs hrFE hri hfk
        · exact eval_reg hrCC hC_lt
        apply runs_assign_le (v := k + 1)
        · simp only [Expr.eval, hri, h1lt, WordRAM.BinOp.eval, hk1, ↓reduceIte]
        · refine ⟨hk_lt, by simp, fun r h1 => by simp [Function.update_of_ne h1, hr r h1],
            hp, memFrame_trans hmf (memFrame_update_in (by dsimp [wFlowEnc]; omega) (by dsimp [wFlowEnc, wLvlVol]; omega)),
            fun idx hidx => ?_⟩
          by_cases hix : idx = k
          · subst hix; simp
          · simp [Function.update_of_ne (by omega : wFlowEnc workAddr n m H + idx ≠ wFlowEnc workAddr n m H + k), hall idx (by omega)]
        · simp only [Expr.size]; omega
      obtain ⟨o, st_next, c_b, hrun_b, hpost_b, hc_b⟩ := hbody
      cases o with
      | returned _ => exact absurd hpost_b (by simp [normalPost])
      | normal =>
          exact ⟨.normal, st_next, c_b, hrun_b, ⟨k + 1, hpost_b, by omega, by omega⟩, hc_b⟩
  refine runs_start_le ?_
  dsimp only [initZeroFlowsStmt, seqStmts]
  apply runs_seq_assign_le (v := 0)
  · simp [Expr.eval, h0lt]
  apply runs_triple_le hloop
  · refine ⟨Nat.zero_le _, by simp, fun r h1 => by simp [Function.update_of_ne h1],
      rfl, fun _ _ => rfl, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  · intro o st1 h1
    cases o with
    | returned _ => exact absurd h1 (by simp [normalPost])
    | normal =>
        rcases h1 with ⟨_, _, hr1, hp1, hmf1, hall1⟩
        exact ⟨{
    reg_g := (hr1 prG (by decide)).trans hptrs.reg_g
    reg_csr := (hr1 prCsr (by decide)).trans hptrs.reg_csr
    reg_inB := (hr1 prInB (by decide)).trans hptrs.reg_inB
    reg_outR := (hr1 prOutR (by decide)).trans hptrs.reg_outR
    reg_work := (hr1 prWork (by decide)).trans hptrs.reg_work
    reg_ccap := (hr1 prCcap (by decide)).trans hptrs.reg_ccap
    reg_H := (hr1 prH (by decide)).trans hptrs.reg_H
    reg_theta := (hr1 prTheta (by decide)).trans hptrs.reg_theta
    reg_n := (hr1 prN (by decide)).trans hptrs.reg_n
    reg_m := (hr1 prM (by decide)).trans hptrs.reg_m
    reg_actTop := (hr1 prActTop (by decide)).trans hptrs.reg_actTop
    reg_peelTop := (hr1 prPeelTop (by decide)).trans hptrs.reg_peelTop
    reg_degX := (hr1 prDegX (by decide)).trans hptrs.reg_degX
    reg_hArr := (hr1 prHArr (by decide)).trans hptrs.reg_hArr
    reg_cur := (hr1 prCur (by decide)).trans hptrs.reg_cur
    reg_abs := (hr1 prAbs (by decide)).trans hptrs.reg_abs
    reg_ex := (hr1 prEx (by decide)).trans hptrs.reg_ex
    reg_degR := (hr1 prDegR (by decide)).trans hptrs.reg_degR
    reg_inAct := (hr1 prInAct (by decide)).trans hptrs.reg_inAct
    reg_actStk := (hr1 prActStk (by decide)).trans hptrs.reg_actStk
    reg_peelStk := (hr1 prPeelStk (by decide)).trans hptrs.reg_peelStk
    reg_lvlNext := (hr1 prLvlNext (by decide)).trans hptrs.reg_lvlNext
    reg_lvlPrev := (hr1 prLvlPrev (by decide)).trans hptrs.reg_lvlPrev
    reg_remArr := (hr1 prRemArr (by decide)).trans hptrs.reg_remArr
    reg_flowEnc := (hr1 prFlowEnc (by decide)).trans hptrs.reg_flowEnc
    reg_lvlVol := (hr1 prLvlVol (by decide)).trans hptrs.reg_lvlVol
    reg_lvlHead := (hr1 prLvlHead (by decide)).trans hptrs.reg_lvlHead
    reg_adjV := (hr1 prCsrAdjV (by decide)).trans hptrs.reg_adjV
    reg_adjH := (hr1 prCsrAdjH (by decide)).trans hptrs.reg_adjH },
    hp1, hmf1, hall1⟩
  · simp only [Expr.size]; omega

lemma initScanOneEdgeCond_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {workAddr k a b : ℕ}
    (st₀ : State) (inR : ℕ → Bool)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hk : k < cfg.G.edges.length)
    (heq_e : cfg.G.edges[k]'hk = (a, b))
    (haN : a < cfg.G.n) (hbN : b < cfg.G.n) :
    let n := cfg.G.n
    let m := cfg.G.m
    let H := cfg.H
    Triple w p
      (fun st => st = st₀ ∧
        st.regs prDegR = wDegR workAddr n m H ∧
        st.regs prEx = wEx workAddr n m H ∧
        st.regs prCcap = cfg.C_cap ∧
        st.regs prU = a ∧ st.regs prW = b ∧
        st.regs prTmp1 = (if inR a then 1 else 0) ∧
        st.regs prTmp2 = (if inR b then 1 else 0) ∧
        (∀ u < n, st.mem (wDegR workAddr n m H + u) = degRPrefix cfg.G inR k u) ∧
        (∀ u < n, st.mem (wEx workAddr n m H + u) = exPrefix cfg.G inR cfg.C_cap k u))
      initScanOneEdgeCondStmt
      (normalPost fun st' =>
        (∀ r, r ≠ prTmp3 → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame st₀.mem st'.mem (wEx workAddr n m H) (wInAct workAddr n m H) ∧
        (∀ u < n, st'.mem (wDegR workAddr n m H + u) = degRPrefix cfg.G inR (k + 1) u) ∧
        (∀ u < n, st'.mem (wEx workAddr n m H + u) = exPrefix cfg.G inR cfg.C_cap (k + 1) u))
      (fun _ => 50) := by
  intro n m H st ω ⟨hst, hrDR, hrEX, hrCC, hru, hrw, hr1, hr2, hdr, hex⟩
  subst st
  have hwb := hw
  unfold PruneWordBound pruneWorkSpace at hwb
  have h0lt : 0 < 2 ^ w := by omega
  have h1lt : 1 < 2 ^ w := by omega
  have hlt_pow : ∀ x, x ≤ workAddr + (12 * n + m + 2 * H + 2) → x < 2 ^ w := fun x hx => by omega
  have ha_dr_lt : wDegR workAddr n m H + a < 2 ^ w := hlt_pow _ (by dsimp [wDegR]; omega)
  have hb_dr_lt : wDegR workAddr n m H + b < 2 ^ w := hlt_pow _ (by dsimp [wDegR]; omega)
  have ha_ex_lt : wEx workAddr n m H + a < 2 ^ w := hlt_pow _ (by dsimp [wEx]; omega)
  have hb_ex_lt : wEx workAddr n m H + b < 2 ^ w := hlt_pow _ (by dsimp [wEx]; omega)
  have ha_dr_val_lt : degRPrefix cfg.G inR k a + 1 < 2 ^ w := by
    have := degRPrefix_le_two_mul_m (G := cfg.G) inR k a; dsimp [m] at *; omega
  have ha_dr_self_lt : degRPrefix cfg.G inR k a + 1 + 1 < 2 ^ w := by
    have := degRPrefix_le_two_mul_m (G := cfg.G) inR k a; dsimp [m] at *; omega
  have hb_dr_val_lt : degRPrefix cfg.G inR k b + 1 < 2 ^ w := by
    have := degRPrefix_le_two_mul_m (G := cfg.G) inR k b; dsimp [m] at *; omega
  have ha_ex_val_lt : exPrefix cfg.G inR cfg.C_cap k a + cfg.C_cap < 2 ^ w := by
    have h1 := exPrefix_le_bound (G := cfg.G) inR cfg.C_cap k a haN
    have h8 : 2 * cfg.C_cap * cfg.G.m ≤ 8 * cfg.C_cap * cfg.G.m :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hb_ex_val_lt : exPrefix cfg.G inR cfg.C_cap k b + cfg.C_cap < 2 ^ w := by
    have h1 := exPrefix_le_bound (G := cfg.G) inR cfg.C_cap k b hbN
    have h8 : 2 * cfg.C_cap * cfg.G.m ≤ 8 * cfg.C_cap * cfg.G.m :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have h_then_true : Triple w p
      (fun st => st = st₀ ∧ inR a = true ∧ inR b = true)
      (seqStmts [
        .assign prTmp3 (.bin .add (.reg prDegR) (.reg prU)),
        .store (.reg prTmp3) (.bin .add (.load (.reg prTmp3)) (.const 1)),
        .assign prTmp3 (.bin .add (.reg prDegR) (.reg prW)),
        .store (.reg prTmp3) (.bin .add (.load (.reg prTmp3)) (.const 1))
      ])
      (normalPost fun st' =>
        (∀ r, r ≠ prTmp3 → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame st₀.mem st'.mem (wEx workAddr n m H) (wInAct workAddr n m H) ∧
        (∀ u < n, st'.mem (wDegR workAddr n m H + u) = degRPrefix cfg.G inR (k + 1) u) ∧
        (∀ u < n, st'.mem (wEx workAddr n m H + u) = exPrefix cfg.G inR cfg.C_cap (k + 1) u))
      (fun _ => 30) := by
    intro st ω' ⟨hst', ha_t, hb_t⟩
    subst st
    refine runs_start_le ?_
    dsimp only [seqStmts]
    apply runs_seq_assign_le (v := wDegR workAddr n m H + a)
    · exact eval_add_regs hrDR hru ha_dr_lt
    apply runs_seq_store_le (x := wDegR workAddr n m H + a) (v := degRPrefix cfg.G inR k a + 1)
    · simp [Expr.eval]
    · simp only [Expr.eval, Function.update_self, Option.map_some, hdr a haN, h1lt,
        WordRAM.BinOp.eval, ha_dr_val_lt, ↓reduceIte]
    apply runs_seq_assign_le (v := wDegR workAddr n m H + b)
    · exact eval_add_regs (by simp [hrDR]) (by simp [hrw]) hb_dr_lt
    apply runs_store_le (x := wDegR workAddr n m H + b)
        (v := (if b = a then degRPrefix cfg.G inR k a + 1 else degRPrefix cfg.G inR k b) + 1)
    · simp [Expr.eval]
    · by_cases hba : b = a
      · subst hba
        simp only [Expr.eval, Function.update_self, Option.map_some, h1lt,
          WordRAM.BinOp.eval, ha_dr_self_lt, ↓reduceIte]
      · simp only [Expr.eval, Function.update_self, Option.map_some,
          Function.update_of_ne (by omega : wDegR workAddr n m H + b ≠ wDegR workAddr n m H + a),
          hdr b hbN, h1lt, WordRAM.BinOp.eval, hb_dr_val_lt, ↓reduceIte, hba]
    · refine ⟨fun r hne => by simp [hne], rfl, ?_, ?_, ?_⟩
      · exact memFrame_trans
          (memFrame_update_in (by dsimp [wEx, wDegR]; omega) (by dsimp [wDegR, wInAct]; omega))
          (memFrame_update_in (by dsimp [wEx, wDegR]; omega) (by dsimp [wDegR, wInAct]; omega))
      · intro u hu
        have hstep := degRPrefix_succ cfg.G inR hk u
        rw [heq_e] at hstep
        simp only [ha_t, hb_t, Bool.and_self, ↓reduceIte] at hstep
        rw [hstep]
        dsimp only
        by_cases hub : u = b <;> by_cases hua : u = a
        · have hab : b = a := hub.symm.trans hua
          rw [hub, hab]; simp [Function.update_self]
        · rw [hub]
          have hne_ba : b ≠ a := by omega
          simp [Function.update_self, hne_ba, Ne.symm hne_ba]
        · rw [hua]
          have hne_ab : a ≠ b := by omega
          rw [Function.update_of_ne (by omega), Function.update_self]
          simp [Ne.symm hne_ab]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hdr u hu]
          simp [Ne.symm hua, Ne.symm hub]
      · intro u hu
        have hstep := exPrefix_succ cfg.G inR cfg.C_cap hk u
        rw [heq_e] at hstep
        simp only [ha_t, hb_t, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hstep
        dsimp only
        rw [hstep, Function.update_of_ne (by dsimp [wEx, wDegR]; omega),
          Function.update_of_ne (by dsimp [wEx, wDegR]; omega)]
        exact hex u hu
    · simp only [Expr.size]; omega
  have h_then_false : Triple w p
      (fun st => st = st₀ ∧ inR a = true ∧ inR b = false)
      (seqStmts [
        .assign prTmp3 (.bin .add (.reg prEx) (.reg prU)),
        .store (.reg prTmp3) (.bin .add (.load (.reg prTmp3)) (.reg prCcap))
      ])
      (normalPost fun st' =>
        (∀ r, r ≠ prTmp3 → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame st₀.mem st'.mem (wEx workAddr n m H) (wInAct workAddr n m H) ∧
        (∀ u < n, st'.mem (wDegR workAddr n m H + u) = degRPrefix cfg.G inR (k + 1) u) ∧
        (∀ u < n, st'.mem (wEx workAddr n m H + u) = exPrefix cfg.G inR cfg.C_cap (k + 1) u))
      (fun _ => 20) := by
    intro st ω' ⟨hst', ha_t, hb_f⟩
    subst st
    refine runs_start_le ?_
    dsimp only [seqStmts]
    apply runs_seq_assign_le (v := wEx workAddr n m H + a)
    · exact eval_add_regs hrEX hru ha_ex_lt
    apply runs_store_le (x := wEx workAddr n m H + a) (v := exPrefix cfg.G inR cfg.C_cap k a + cfg.C_cap)
    · simp [Expr.eval]
    · simp only [Expr.eval, Function.update_self, Function.update_of_ne (by decide : prCcap ≠ prTmp3),
        hrCC, Option.map_some, hex a haN, WordRAM.BinOp.eval, ha_ex_val_lt, ↓reduceIte]
    · refine ⟨fun r hne => by simp [hne], rfl,
        memFrame_update_in (by dsimp [wEx]; omega) (by dsimp [wEx, wInAct]; omega), ?_, ?_⟩
      · intro u hu
        have hstep := degRPrefix_succ cfg.G inR hk u
        rw [heq_e] at hstep
        simp only [ha_t, hb_f, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hstep
        dsimp only
        rw [hstep, Function.update_of_ne (by dsimp [wDegR, wEx]; omega)]
        exact hdr u hu
      · intro u hu
        have hstep := exPrefix_succ cfg.G inR cfg.C_cap hk u
        rw [heq_e] at hstep
        simp only [ha_t, hb_f, Bool.not_false, Bool.and_self, ↓reduceIte] at hstep
        rw [hstep]
        dsimp only
        by_cases hua : u = a
        · rw [hua]; simp
        · rw [Function.update_of_ne (by omega : wEx workAddr n m H + u ≠ wEx workAddr n m H + a), hex u hu]
          simp [Ne.symm hua]
    · simp only [Expr.size]; omega
  have h_else_true : Triple w p
      (fun st => st = st₀ ∧ inR a = false ∧ inR b = true)
      (seqStmts [
        .assign prTmp3 (.bin .add (.reg prEx) (.reg prW)),
        .store (.reg prTmp3) (.bin .add (.load (.reg prTmp3)) (.reg prCcap))
      ])
      (normalPost fun st' =>
        (∀ r, r ≠ prTmp3 → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame st₀.mem st'.mem (wEx workAddr n m H) (wInAct workAddr n m H) ∧
        (∀ u < n, st'.mem (wDegR workAddr n m H + u) = degRPrefix cfg.G inR (k + 1) u) ∧
        (∀ u < n, st'.mem (wEx workAddr n m H + u) = exPrefix cfg.G inR cfg.C_cap (k + 1) u))
      (fun _ => 20) := by
    intro st ω' ⟨hst', ha_f, hb_t⟩
    subst st
    refine runs_start_le ?_
    dsimp only [seqStmts]
    apply runs_seq_assign_le (v := wEx workAddr n m H + b)
    · exact eval_add_regs hrEX hrw hb_ex_lt
    apply runs_store_le (x := wEx workAddr n m H + b) (v := exPrefix cfg.G inR cfg.C_cap k b + cfg.C_cap)
    · simp [Expr.eval]
    · simp only [Expr.eval, Function.update_self, Function.update_of_ne (by decide : prCcap ≠ prTmp3),
        hrCC, Option.map_some, hex b hbN, WordRAM.BinOp.eval, hb_ex_val_lt, ↓reduceIte]
    · refine ⟨fun r hne => by simp [hne], rfl,
        memFrame_update_in (by dsimp [wEx]; omega) (by dsimp [wEx, wInAct]; omega), ?_, ?_⟩
      · intro u hu
        have hstep := degRPrefix_succ cfg.G inR hk u
        rw [heq_e] at hstep
        simp only [ha_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hstep
        dsimp only
        rw [hstep, Function.update_of_ne (by dsimp [wDegR, wEx]; omega)]
        exact hdr u hu
      · intro u hu
        have hstep := exPrefix_succ cfg.G inR cfg.C_cap hk u
        rw [heq_e] at hstep
        simp only [ha_f, hb_t, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          Bool.not_false, Bool.and_self] at hstep
        rw [hstep]
        dsimp only
        by_cases hub : u = b
        · rw [hub]; simp
        · rw [Function.update_of_ne (by omega : wEx workAddr n m H + u ≠ wEx workAddr n m H + b), hex u hu]
          simp [Ne.symm hub]
    · simp only [Expr.size]; omega
  have h_else_false : Triple w p
      (fun st => st = st₀ ∧ inR a = false ∧ inR b = false)
      .nop
      (normalPost fun st' =>
        (∀ r, r ≠ prTmp3 → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        MemFrame st₀.mem st'.mem (wEx workAddr n m H) (wInAct workAddr n m H) ∧
        (∀ u < n, st'.mem (wDegR workAddr n m H + u) = degRPrefix cfg.G inR (k + 1) u) ∧
        (∀ u < n, st'.mem (wEx workAddr n m H + u) = exPrefix cfg.G inR cfg.C_cap (k + 1) u))
      (fun _ => 1) := by
    apply Triple.nop
    intro st ⟨hst', ha_f, hb_f⟩
    subst st
    refine ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, ?_, ?_⟩
    · intro u hu
      have hstep := degRPrefix_succ cfg.G inR hk u
      rw [heq_e] at hstep
      simp only [ha_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hstep
      rw [hstep]; exact hdr u hu
    · intro u hu
      have hstep := exPrefix_succ cfg.G inR cfg.C_cap hk u
      rw [heq_e] at hstep
      simp only [ha_f, hb_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hstep
      rw [hstep]; exact hex u hu
  have hcond_then := (Triple.cond_const
    (P := fun st => st = st₀ ∧ inR a = true)
    (e := .bin .lt (.const 0) (.reg prTmp2))
    (val := fun st => if 0 < st.regs prTmp2 then 1 else 0) (c_t := 30) (c_f := 20)
    (fun st ⟨hst', _⟩ => by
      subst st
      simp only [Expr.eval, hr2, h0lt, WordRAM.BinOp.eval]
      by_cases hcmp : 0 < (if inR b then 1 else 0) <;> simp [hcmp, h1lt, h0lt])
    (h_then_true.weaken_pre fun st ⟨⟨hst', ha_t⟩, hne⟩ => by
      have hb_t : inR b = true := by
        subst st; cases hb : inR b <;> simp [hr2, hb] at hne; rfl
      exact ⟨hst', ha_t, hb_t⟩)
    (h_then_false.weaken_pre fun st ⟨⟨hst', ha_t⟩, heq⟩ => by
      have hb_f : inR b = false := by
        subst st; cases hb : inR b
        · rfl
        · simp [hr2, hb] at heq
      exact ⟨hst', ha_t, hb_f⟩)).mono_cost (T' := fun _ => 40)
        (fun _ _ => by simp only [Expr.size]; omega)
  have hcond_else := (Triple.cond_const
    (P := fun st => st = st₀ ∧ inR a = false)
    (e := .bin .lt (.const 0) (.reg prTmp2))
    (val := fun st => if 0 < st.regs prTmp2 then 1 else 0) (c_t := 20) (c_f := 1)
    (fun st ⟨hst', _⟩ => by
      subst st
      simp only [Expr.eval, hr2, h0lt, WordRAM.BinOp.eval]
      by_cases hcmp : 0 < (if inR b then 1 else 0) <;> simp [hcmp, h1lt, h0lt])
    (h_else_true.weaken_pre fun st ⟨⟨hst', ha_f⟩, hne⟩ => by
      have hb_t : inR b = true := by
        subst st; cases hb : inR b <;> simp [hr2, hb] at hne; rfl
      exact ⟨hst', ha_f, hb_t⟩)
    (h_else_false.weaken_pre fun st ⟨⟨hst', ha_f⟩, heq⟩ => by
      have hb_f : inR b = false := by
        subst st; cases hb : inR b
        · rfl
        · simp [hr2, hb] at heq
      exact ⟨hst', ha_f, hb_f⟩)).mono_cost (T' := fun _ => 30)
        (fun _ _ => by simp only [Expr.size]; omega)
  dsimp only [initScanOneEdgeCondStmt]
  exact ((Triple.cond_const
    (P := fun st => st = st₀)
    (e := .bin .lt (.const 0) (.reg prTmp1))
    (val := fun st => if 0 < st.regs prTmp1 then 1 else 0) (c_t := 40) (c_f := 30)
    (fun st hst' => by
      subst st
      simp only [Expr.eval, hr1, h0lt, WordRAM.BinOp.eval]
      by_cases hcmp : 0 < (if inR a then 1 else 0) <;> simp [hcmp, h1lt, h0lt])
    (hcond_then.weaken_pre fun st ⟨hst', hne⟩ => by
      have ha_t : inR a = true := by
        subst st; cases ha : inR a <;> simp [hr1, ha] at hne; rfl
      exact ⟨hst', ha_t⟩)
    (hcond_else.weaken_pre fun st ⟨hst', heq⟩ => by
      have ha_f : inR a = false := by
        subst st; cases ha : inR a
        · rfl
        · simp [hr1, ha] at heq
      exact ⟨hst', ha_f⟩)).mono_cost (T' := fun _ => 50)
        (fun _ _ => by simp only [Expr.size]; omega)).runs ω rfl


end MinCostFlow.Expander
