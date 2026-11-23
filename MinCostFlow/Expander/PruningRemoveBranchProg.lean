module

public import MinCostFlow.Expander.PruningRemoveSubProg

/-!
# Branch Triple for Removing a Vertex from R
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

lemma removeOneBranch_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {A : Finset ℕ} {s sk : PruneState} (inR' : ℕ → Bool)
    (q : ℕ × Bool × ℕ) (baseIdx k : ℕ) (st1 : State)
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hval : cfg.Valid) (hsw : SweepInv cfg A s)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (hptrs : PruneStepRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st1)
    (hq_idx : q.1 < cfg.G.edges.length) (hq_w : q.2.2 < cfg.G.n)
    (hqR_imp : inR' q.2.2 = true → s.inR q.2.2 = true)
    (hk_addr : baseIdx + k < 2 * cfg.G.m)
    (hst1_J : st1.regs prJ = baseIdx + k)
    (hst1_W : st1.regs prW = q.2.2)
    (hst1_1 : st1.regs prTmp1 = if inR' q.2.2 then 1 else 0)
    (hst1_AT : st1.regs prActTop = sk.active.length)
    (hst1_PT : st1.regs prPeelTop = sk.peelQ.length)
    (hadjH_mem : st1.mem (csrAddr + 2 * cfg.G.n + 1 + 2 * cfg.G.m + (baseIdx + k)) =
      2 * q.1 + (if q.2.1 then 1 else 0))
    (hfe : st1.mem (wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + q.1) =
      (↑cfg.C_cap + s.flow q.1).toNat)
    (hex_bd : inR' q.2.2 = true → (removeEdgeStep cfg s.flow inR' sk q).ex q.2.2 < 2 ^ w)
    (hdr_old_lt : inR' q.2.2 = true → sk.degR q.2.2 < 2 ^ w)
    (hnext_act_len : (removeEdgeStep cfg s.flow inR' sk q).active.length ≤ cfg.G.n)
    (hnext_peel_len : (removeEdgeStep cfg s.flow inR' sk q).peelQ.length ≤ cfg.G.n)
    (hEx : ∀ u < cfg.G.n, st1.mem (wEx workAddr cfg.G.n cfg.G.m cfg.H + u) = sk.ex u)
    (hDr : ∀ u < cfg.G.n, st1.mem (wDegR workAddr cfg.G.n cfg.G.m cfg.H + u) = sk.degR u)
    (hIA : ∀ u < cfg.G.n, st1.mem (wInAct workAddr cfg.G.n cfg.G.m cfg.H + u) = if sk.inActive u then 1 else 0)
    (hAS : ∀ i < sk.active.length,
      st1.mem (wActStk workAddr cfg.G.n cfg.G.m cfg.H + i) = sk.active.getD (sk.active.length - 1 - i) 0)
    (hPS : ∀ i < sk.peelQ.length,
      st1.mem (wPeelStk workAddr cfg.G.n cfg.G.m cfg.H + i) = sk.peelQ.getD (sk.peelQ.length - 1 - i) 0) :
    let n := cfg.G.n
    let m := cfg.G.m
    let H := cfg.H
    let sNext := removeEdgeStep cfg s.flow inR' sk q
    Triple w p (fun sx => sx = st1) removeOneBranchStmt
      (normalPost fun st' =>
        (∀ r, r ≠ prIdx → r ≠ prDir → r ≠ prRc → r ≠ prTmp1 → r ≠ prTmp2 →
          r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st1.regs r) ∧
        st'.regs prActTop = sNext.active.length ∧
        st'.regs prPeelTop = sNext.peelQ.length ∧
        st'.pos = st1.pos ∧
        MemFrame st1.mem st'.mem (wEx workAddr n m H) (wLvlNext workAddr n m H) ∧
        (∀ u < n, st'.mem (wEx workAddr n m H + u) = sNext.ex u) ∧
        (∀ u < n, st'.mem (wDegR workAddr n m H + u) = sNext.degR u) ∧
        (∀ u < n, st'.mem (wInAct workAddr n m H + u) = if sNext.inActive u then 1 else 0) ∧
        (∀ i < sNext.active.length,
          st'.mem (wActStk workAddr n m H + i) = sNext.active.getD (sNext.active.length - 1 - i) 0) ∧
        (∀ i < sNext.peelQ.length,
          st'.mem (wPeelStk workAddr n m H + i) = sNext.peelQ.getD (sNext.peelQ.length - 1 - i) 0))
      (fun _ => 125) := by
  intro n m H sNext
  have hGv : cfg.G.IsValid := hval.1
  have h0lt : 0 < 2 ^ w := by unfold PruneWordBound at hw; omega
  have h1lt : 1 < 2 ^ w := by unfold PruneWordBound at hw; omega
  have h2lt : 2 < 2 ^ w := by unfold PruneWordBound at hw; omega
  have h2C_lt : 2 * cfg.C_cap < 2 ^ w := by unfold PruneWordBound at hw; omega
  have hwb_w : workAddr + pruneWorkSpace n m H < 2 ^ w := by
    unfold PruneWordBound at hw; dsimp only [pruneWorkSpace, n, m, H] at *; omega
  have hlt_pow : ∀ x, x ≤ workAddr + (12 * n + m + 2 * H + 2) → x < 2 ^ w := fun x hx => by
    have := hwb_w; dsimp only [pruneWorkSpace] at this; omega
  have hq_w_lt : q.2.2 < n := hq_w
  have hqw_lt_w : q.2.2 < 2 ^ w := by unfold PruneWordBound at hw; dsimp only [n] at hq_w_lt; omega
  have hadjH_addr_lt : csrAddr + 2 * n + 1 + 2 * m + (baseIdx + k) < 2 ^ w := by
    dsimp only [n, m] at hcsr_w hk_addr ⊢; omega
  apply (Triple.cond_const
    (P := fun sx => sx = st1)
    (e := .bin .lt (.const 0) (.reg prTmp1))
    (val := fun sx => if 0 < sx.regs prTmp1 then 1 else 0)
    (c_t := 120) (c_f := 1)
    (fun sx hsx => by
      subst sx; simp only [Expr.eval, hst1_1, h0lt, WordRAM.BinOp.eval]
      by_cases hcmp : 0 < (if inR' q.2.2 then 1 else 0) <;> simp [hcmp, h1lt, h0lt])
    ?_ ?_).mono_cost (T' := fun _ => 125) (fun _ _ => by simp only [Expr.size]; omega)
  · intro sx ω2 ⟨hsx, hne⟩
    subst sx
    have hqR : inR' q.2.2 = true := by
      by_contra hf
      have hf' : inR' q.2.2 = false := Bool.eq_false_iff.mpr hf
      simp [hst1_1, hf'] at hne
    have hqR_s : s.inR q.2.2 = true := hqR_imp hqR
    have hflow_cap := hsw.flow_cap q.1 (by
      unfold PruneCfg.edges
      have hx : cfg.X = cfg.G.verts := hcfgX
      rw [hx, inside_verts_of_isValid hGv]
      exact hq_idx)
    have hq1_lt_m : q.1 < m := by simpa [m, Cited.Graph.m] using hq_idx
    have hflowEnc_le : (↑cfg.C_cap + s.flow q.1).toNat ≤ 2 * cfg.C_cap := by omega
    have hflowEnc_lt_w : (↑cfg.C_cap + s.flow q.1).toNat < 2 ^ w := by omega
    let rcVal := ((cfg.C_cap : ℤ) - flowDir s.flow q.1 q.2.1).toNat
    have hrc_eq : rcVal =
        if q.2.1 then (↑cfg.C_cap + s.flow q.1).toNat
        else 2 * cfg.C_cap - (↑cfg.C_cap + s.flow q.1).toNat := by
      dsimp only [rcVal, flowDir]
      cases q.2.1
      · simp; omega
      · simp
    have hrc_le : rcVal ≤ 2 * cfg.C_cap := by rw [hrc_eq]; split_ifs <;> omega
    have hrc_lt_w : rcVal < 2 ^ w := by omega
    have hadjH_val_lt : 2 * q.1 + (if q.2.1 then 1 else 0) < 2 ^ w := by
      by_cases qb : q.2.1 <;> simp [qb] <;> omega
    have hflowEnc_addr_lt : wFlowEnc workAddr n m H + q.1 < 2 ^ w :=
      hlt_pow _ (by dsimp [wFlowEnc]; omega)
    have hex_w_addr_lt : wEx workAddr n m H + q.2.2 < 2 ^ w :=
      hlt_pow _ (by dsimp [wEx]; omega)
    have hia_w_addr_lt : wInAct workAddr n m H + q.2.2 < 2 ^ w :=
      hlt_pow _ (by dsimp [wInAct]; omega)
    have hdr_w_addr_lt : wDegR workAddr n m H + q.2.2 < 2 ^ w :=
      hlt_pow _ (by dsimp [wEx, wDegR]; omega)
    have hstep_ex_q : sNext.ex q.2.2 = sk.ex q.2.2 + rcVal := by
      dsimp only [sNext, removeEdgeStep]; simp [hqR, rcVal]
    have hex_new_lt_w : sk.ex q.2.2 + rcVal < 2 ^ w := by
      rw [← hstep_ex_q]; exact hex_bd hqR
    have hex_old_lt_w : sk.ex q.2.2 < 2 ^ w := by omega
    have hdr_old_lt_w : sk.degR q.2.2 < 2 ^ w := hdr_old_lt hqR
    have hdivmod := eval_bin_two_mul_div_two q.1 (if q.2.1 then 1 else 0) (by split_ifs <;> omega)
    let rInit : ℕ → ℕ :=
      Function.update (Function.update (Function.update (Function.update st1.regs
        prTmp2 (2 * q.1 + (if q.2.1 then 1 else 0))) prIdx q.1) prDir (if q.2.1 then 1 else 0))
        prTmp1 (↑cfg.C_cap + s.flow q.1).toNat
    have hrc_triple : Triple w p (fun sz => sz = { st1 with regs := rInit })
        (.cond (.bin .eq (.reg prDir) (.const 0))
          (.assign prRc (.bin .sub (.bin .mul (.const 2) (.reg prCcap)) (.reg prTmp1)))
          (.assign prRc (.reg prTmp1)))
        (normalPost fun st' =>
          (∀ r, r ≠ prRc → st'.regs r = rInit r) ∧
          st'.regs prRc = rcVal ∧ st'.pos = st1.pos ∧ st'.mem = st1.mem)
        (fun _ => 10) := by
      apply (Triple.cond_const
        (P := fun sz => sz = { st1 with regs := rInit })
        (e := .bin .eq (.reg prDir) (.const 0))
        (val := fun sz => if sz.regs prDir = 0 then 1 else 0)
        (c_t := 6) (c_f := 2)
        (fun sz hsz => by
          subst sz
          have hrDir : rInit prDir = if q.2.1 then 1 else 0 := by simp [rInit]
          simp only [Expr.eval, hrDir, h0lt, WordRAM.BinOp.eval]
          cases q.2.1 <;> simp [h1lt, h0lt])
        ?_ ?_).mono_cost (T' := fun _ => 10) (fun _ _ => by simp only [Expr.size]; omega)
      · intro sz ω3 ⟨hsz, hne'⟩
        subst sz
        have hqf : q.2.1 = false := by
          by_contra hqt
          have hqt' : q.2.1 = true := Bool.eq_true_of_not_eq_false hqt
          simp [rInit, hqt'] at hne'
        have hrCC : rInit prCcap = cfg.C_cap := by simp [rInit, hptrs.reg_ccap]
        have hr1' : rInit prTmp1 = (↑cfg.C_cap + s.flow q.1).toNat := by simp [rInit]
        have hsub_lt : 2 * cfg.C_cap - (↑cfg.C_cap + s.flow q.1).toNat < 2 ^ w := by omega
        have hsub_eq : rcVal = 2 * cfg.C_cap - (↑cfg.C_cap + s.flow q.1).toNat := by
          simp [hrc_eq, hqf]
        refine runs_start_le (T := 6) ?_
        apply runs_assign_le (v := rcVal)
        · simp [Expr.eval, hrCC, hr1', h2lt, WordRAM.BinOp.eval, h2C_lt, hsub_lt, hsub_eq]
        · exact ⟨fun r hne'' => by simp [Function.update_of_ne hne''], by simp, rfl, rfl⟩
        · simp only [Expr.size]; omega
      · intro sz ω3 ⟨hsz, heq'⟩
        subst sz
        have hqt : q.2.1 = true := by
          by_contra hqf
          have hqf' : q.2.1 = false := Bool.eq_false_iff.mpr hqf
          simp [rInit, hqf'] at heq'
        have hr1' : rInit prTmp1 = (↑cfg.C_cap + s.flow q.1).toNat := by simp [rInit]
        have hsub_eq : rcVal = (↑cfg.C_cap + s.flow q.1).toNat := by simp [hrc_eq, hqt]
        refine runs_start_le (T := 2) ?_
        apply runs_assign_le (v := rcVal)
        · simp [Expr.eval, hr1', hsub_eq]
        · exact ⟨fun r hne'' => by simp [Function.update_of_ne hne''], by simp, rfl, rfl⟩
        · simp only [Expr.size]; omega
    refine runs_start_le (T := 120) ?_
    dsimp only [seqStmts]
    apply runs_seq_assign_le (v := 2 * q.1 + (if q.2.1 then 1 else 0))
    · exact eval_load_add_regs hptrs.reg_adjH hst1_J hadjH_addr_lt hadjH_mem hadjH_val_lt
    apply runs_seq_assign_le (v := q.1)
    · have hlt_q1 : q.1 < 2 ^ w := by omega
      simp only [Expr.eval, Function.update_self, h2lt, WordRAM.BinOp.eval, hdivmod.1, hlt_q1, ↓reduceIte]
    apply runs_seq_assign_le (v := if q.2.1 then 1 else 0)
    · have hr2' : Function.update (Function.update st1.regs prTmp2 (2 * q.1 + (if q.2.1 then 1 else 0))) prIdx q.1 prTmp2 =
          2 * q.1 + (if q.2.1 then 1 else 0) := by
        rw [Function.update_of_ne (by decide), Function.update_self]
      have hlt_dir : (if q.2.1 then 1 else 0) < 2 ^ w := by split_ifs <;> omega
      simp only [Expr.eval, hr2', h2lt, WordRAM.BinOp.eval, hdivmod.2, hlt_dir, ↓reduceIte]
    apply runs_seq_assign_le (v := (↑cfg.C_cap + s.flow q.1).toNat)
    · have hrFE : Function.update (Function.update (Function.update st1.regs
          prTmp2 (2 * q.1 + (if q.2.1 then 1 else 0))) prIdx q.1) prDir (if q.2.1 then 1 else 0) prFlowEnc =
          wFlowEnc workAddr n m H := by
        simp only [Function.update_of_ne (by decide : prFlowEnc ≠ prDir),
          Function.update_of_ne (by decide : prFlowEnc ≠ prIdx),
          Function.update_of_ne (by decide : prFlowEnc ≠ prTmp2), hptrs.reg_flowEnc, n, m, H]
      have hrIdx : Function.update (Function.update (Function.update st1.regs
          prTmp2 (2 * q.1 + (if q.2.1 then 1 else 0))) prIdx q.1) prDir (if q.2.1 then 1 else 0) prIdx =
          q.1 := by
        simp only [Function.update_of_ne (by decide : prIdx ≠ prDir), Function.update_self]
      exact eval_load_add_regs hrFE hrIdx hflowEnc_addr_lt hfe hflowEnc_lt_w
    apply runs_seq_triple_le hrc_triple
    · rfl
    intro st2 ⟨hr_2, hrc_2, hp_2, hm_2⟩
    have hr2_ptrs := pruneStepRegs_of_agree hptrs fun r hle _ _ => by
      rw [hr_2 r (by dsimp [prCsrAdjH, prRc] at hle ⊢; omega)]
      dsimp only [rInit]
      simp only [Function.update_of_ne (by dsimp [prCsrAdjH, prTmp1] at hle ⊢; omega : r ≠ prTmp1),
        Function.update_of_ne (by dsimp [prCsrAdjH, prDir] at hle ⊢; omega : r ≠ prDir),
        Function.update_of_ne (by dsimp [prCsrAdjH, prIdx] at hle ⊢; omega : r ≠ prIdx),
        Function.update_of_ne (by dsimp [prCsrAdjH, prTmp2] at hle ⊢; omega : r ≠ prTmp2)]
    have hr2_other : ∀ r, r ≠ prRc → r ≠ prTmp1 → r ≠ prDir → r ≠ prIdx → r ≠ prTmp2 →
        st2.regs r = st1.regs r := by
      intro r h1 h2 h3 h4 h5
      rw [hr_2 r h1]; dsimp only [rInit]
      simp only [Function.update_of_ne h2, Function.update_of_ne h3,
        Function.update_of_ne h4, Function.update_of_ne h5]
    have hr2_W : st2.regs prW = q.2.2 :=
      (hr2_other prW (by decide) (by decide) (by decide) (by decide) (by decide)).trans hst1_W
    have hr2_AT : st2.regs prActTop = sk.active.length :=
      (hr2_other prActTop (by decide) (by decide) (by decide) (by decide) (by decide)).trans hst1_AT
    have hr2_PT : st2.regs prPeelTop = sk.peelQ.length :=
      (hr2_other prPeelTop (by decide) (by decide) (by decide) (by decide) (by decide)).trans hst1_PT
    have hex_old_mem : st2.mem (wEx workAddr n m H + q.2.2) = sk.ex q.2.2 := by
      rw [hm_2]; exact hEx q.2.2 hq_w_lt
    apply runs_seq_assign_le (v := wEx workAddr n m H + q.2.2)
    · exact eval_add_regs hr2_ptrs.reg_ex hr2_W hex_w_addr_lt
    apply runs_seq_assign_le (v := sk.ex q.2.2)
    · exact eval_load_reg (by simp) hex_w_addr_lt (by simpa using hex_old_mem) hex_old_lt_w
    apply runs_seq_store_le (x := wEx workAddr n m H + q.2.2) (v := sk.ex q.2.2 + rcVal)
    · exact eval_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]) hex_w_addr_lt
    · have hrTmp2' : Function.update (Function.update st2.regs prTmp1 (wEx workAddr n m H + q.2.2))
          prTmp2 (sk.ex q.2.2) prTmp2 = sk.ex q.2.2 := by simp
      have hrRc' : Function.update (Function.update st2.regs prTmp1 (wEx workAddr n m H + q.2.2))
          prTmp2 (sk.ex q.2.2) prRc = rcVal := by
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hrc_2]
      exact eval_add_regs hrTmp2' hrRc' hex_new_lt_w
    let mem3 := Function.update st2.mem (wEx workAddr n m H + q.2.2) (sk.ex q.2.2 + rcVal)
    have hmem3_ia : mem3 (wInAct workAddr n m H + q.2.2) = if sk.inActive q.2.2 then 1 else 0 := by
      dsimp only [mem3]
      rw [Function.update_of_ne (by dsimp [wEx, wInAct]; omega), hm_2]
      exact hIA q.2.2 hq_w_lt
    have hia_val_lt : (if sk.inActive q.2.2 then 1 else 0) < 2 ^ w := by split_ifs <;> omega
    apply runs_seq_assign_le (v := if sk.inActive q.2.2 then 1 else 0)
    · have hr3_IA : Function.update (Function.update st2.regs prTmp1 (wEx workAddr n m H + q.2.2))
          prTmp2 (sk.ex q.2.2) prInAct = wInAct workAddr n m H := by
        simpa [n, m, H, Function.update_of_ne (by decide : prInAct ≠ prTmp2),
          Function.update_of_ne (by decide : prInAct ≠ prTmp1)] using hr2_ptrs.reg_inAct
      have hr3_W : Function.update (Function.update st2.regs prTmp1 (wEx workAddr n m H + q.2.2))
          prTmp2 (sk.ex q.2.2) prW = q.2.2 := by
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr2_W]
      exact eval_load_add_regs hr3_IA hr3_W hia_w_addr_lt hmem3_ia hia_val_lt
    let regs3 := Function.update (Function.update (Function.update st2.regs prTmp1 (wEx workAddr n m H + q.2.2))
      prTmp2 (sk.ex q.2.2)) prTmp1 (if sk.inActive q.2.2 then 1 else 0)
    let st3 : State := { mem := mem3, regs := regs3, pos := st2.pos }
    have hst3_rc : st3.regs prRc = rcVal := by
      dsimp only [st3, regs3]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hrc_2]
    have hst3_tmp1 : st3.regs prTmp1 = if sk.inActive q.2.2 then 1 else 0 := by simp [st3, regs3]
    have hst3_ptrs : PruneStepRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st3 :=
      pruneStepRegs_of_agree hr2_ptrs fun r hle _ _ => by
        simp [st3, regs3, Function.update_of_ne (by dsimp [prCsrAdjH, prTmp1] at hle ⊢; omega : r ≠ prTmp1),
          Function.update_of_ne (by dsimp [prCsrAdjH, prTmp2] at hle ⊢; omega : r ≠ prTmp2)]
    have hst3_W : st3.regs prW = q.2.2 := by
      dsimp only [st3, regs3]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hr2_W]
    have hst3_AT : st3.regs prActTop = sk.active.length := by
      dsimp only [st3, regs3]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), hr2_AT]
    have hact_push_eq : sNext.active =
        (if 0 < rcVal ∧ sk.inActive q.2.2 = false then q.2.2 :: sk.active else sk.active) ∧
        (∀ u < n, sNext.inActive u =
          if 0 < rcVal ∧ sk.inActive q.2.2 = false then
            (if u = q.2.2 then true else sk.inActive u)
          else sk.inActive u) := by
      dsimp only [sNext, removeEdgeStep]; simp only [hqR, ↓reduceIte, rcVal]
      by_cases h1c : 0 < rcVal <;> by_cases h2c : sk.inActive q.2.2 = true <;>
        simp [rcVal, h1c, h2c]
    have hst3_IA_mem : ∀ x < n, st3.mem (wInAct workAddr n m H + x) = if sk.inActive x then 1 else 0 := by
      intro x hx
      dsimp only [st3, mem3]
      rw [Function.update_of_ne (by dsimp [wEx, wInAct]; omega), hm_2]
      exact hIA x hx
    have hst3_AS_mem : ∀ i < sk.active.length,
        st3.mem (wActStk workAddr n m H + i) = sk.active.getD (sk.active.length - 1 - i) 0 := by
      intro i hi
      dsimp only [st3, mem3]
      rw [Function.update_of_ne (by dsimp [wEx, wActStk]; omega), hm_2]
      exact hAS i hi
    have hact_len_le : (if 0 < rcVal ∧ sk.inActive q.2.2 = false then q.2.2 :: sk.active else sk.active).length ≤ n := by
      rw [← hact_push_eq.1]; exact hnext_act_len
    apply runs_seq_triple_le (pushActIfNew_triple prRc workAddr n m H q.2.2 rcVal sk.active sk.inActive st3
      hwb_w hq_w_lt (by simpa [n, m, H] using hst3_ptrs.reg_inAct)
      (by simpa [n, m, H] using hst3_ptrs.reg_actStk)
      hst3_W hst3_tmp1 hst3_rc hst3_AT hact_len_le hst3_IA_mem hst3_AS_mem)
    · rfl
    intro st4 ⟨hr_4, hAT_4, hp_4, hmf_4, hIA_4, hAS_4⟩
    have hr4_ptrs := pruneStepRegs_of_agree hst3_ptrs fun _ _ hAT _ => hr_4 _ hAT
    have hr4_W : st4.regs prW = q.2.2 := (hr_4 prW (by decide)).trans hst3_W
    have hr4_PT : st4.regs prPeelTop = sk.peelQ.length := by
      rw [hr_4 prPeelTop (by decide)]
      dsimp only [st3, regs3]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      exact hr2_PT
    have hst4_dr_mem : st4.mem (wDegR workAddr n m H + q.2.2) = sk.degR q.2.2 := by
      rw [hmf_4 _ (Or.inl (by dsimp [wDegR, wInAct]; omega))]
      dsimp only [st3, mem3]; rw [Function.update_of_ne (by dsimp [wEx, wDegR]; omega), hm_2]
      exact hDr q.2.2 hq_w_lt
    let regs5 := Function.update (Function.update st4.regs prTmp1 (wDegR workAddr n m H + q.2.2))
      prTmp2 (sk.degR q.2.2)
    let st5 : State := { mem := st4.mem, regs := regs5, pos := st4.pos }
    have hst5_ptrs : PruneStepRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st5 :=
      pruneStepRegs_of_agree hr4_ptrs fun r hle _ _ => by
        simp [st5, regs5, Function.update_of_ne (by dsimp [prCsrAdjH, prTmp1] at hle ⊢; omega : r ≠ prTmp1),
          Function.update_of_ne (by dsimp [prCsrAdjH, prTmp2] at hle ⊢; omega : r ≠ prTmp2)]
    have hst5_W : st5.regs prW = q.2.2 := by
      dsimp only [st5, regs5]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr4_W]
    have hst5_PT : st5.regs prPeelTop = sk.peelQ.length := by
      dsimp only [st5, regs5]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr4_PT]
    have hst5_tmp1 : st5.regs prTmp1 = wDegR workAddr n m H + q.2.2 := by
      dsimp only [st5, regs5]; rw [Function.update_of_ne (by decide), Function.update_self]
    have hst5_tmp2 : st5.regs prTmp2 = sk.degR q.2.2 := by simp [st5, regs5]
    have hpeel_push_eq : sNext.peelQ =
        (if sk.degR q.2.2 = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat then
          q.2.2 :: sk.peelQ else sk.peelQ) ∧
        (∀ u < n, sNext.degR u =
          if u = q.2.2 then sk.degR q.2.2 - 1 else sk.degR u) := by
      dsimp only [sNext, removeEdgeStep]; simp only [hqR, ↓reduceIte]
      by_cases hpc : sk.degR q.2.2 = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat <;> simp [hpc]
    have hst5_PS_mem : ∀ i < sk.peelQ.length,
        st5.mem (wPeelStk workAddr n m H + i) = sk.peelQ.getD (sk.peelQ.length - 1 - i) 0 := by
      intro i hi
      dsimp only [st5]
      rw [hmf_4 _ (Or.inr (Nat.le_add_right _ _))]
      dsimp only [st3, mem3]; rw [Function.update_of_ne (by dsimp [wEx, wPeelStk]; omega), hm_2]
      exact hPS i hi
    have hpeel_len_le : (if sk.degR q.2.2 = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat then q.2.2 :: sk.peelQ else sk.peelQ).length ≤ n := by
      rw [← hpeel_push_eq.1]; exact hnext_peel_len
    apply runs_seq_assign_le (v := wDegR workAddr n m H + q.2.2)
    · exact eval_add_regs hr4_ptrs.reg_degR hr4_W hdr_w_addr_lt
    apply runs_seq_assign_le (v := sk.degR q.2.2)
    · exact eval_load_reg (by simp) hdr_w_addr_lt (by simpa using hst4_dr_mem) hdr_old_lt_w
    apply runs_seq_triple_le (pushPeelIfTheta_triple workAddr n m H q.2.2 (sk.degR q.2.2) cfg.θ_out_nat sk.peelQ st5
      hwb_w (by simpa [n, m, H] using hst5_ptrs.reg_peelStk)
      hst5_W hst5_tmp2 hst5_ptrs.reg_theta hst5_PT hpeel_len_le hqw_lt_w hst5_PS_mem)
    · rfl
    intro st6 ⟨hr_6, hPT_6, hp_6, hmf_6, hPS_6⟩
    have hr6_tmp1 : st6.regs prTmp1 = wDegR workAddr n m H + q.2.2 :=
      (hr_6 prTmp1 (by decide)).trans hst5_tmp1
    have hr6_tmp2 : st6.regs prTmp2 = sk.degR q.2.2 :=
      (hr_6 prTmp2 (by decide)).trans hst5_tmp2
    apply runs_store_le (x := wDegR workAddr n m H + q.2.2) (v := sk.degR q.2.2 - 1)
    · exact eval_reg hr6_tmp1 hdr_w_addr_lt
    · exact eval_sub_reg_const hr6_tmp2 hdr_old_lt_w h1lt
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro r hIdx hDir hRc h1 h2 hAT hPT
        dsimp only
        rw [hr_6 r hPT]
        dsimp only [st5, regs5]
        rw [Function.update_of_ne h2, Function.update_of_ne h1]
        rw [hr_4 r hAT]
        dsimp only [st3, regs3]
        rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h1]
        exact hr2_other r hRc h1 hDir hIdx h2
      · dsimp only
        rw [hr_6 prActTop (by decide)]; dsimp only [st5, regs5]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        rw [hAT_4, hact_push_eq.1]
      · dsimp only
        rw [hPT_6, hpeel_push_eq.1]
      · dsimp only
        rw [hp_6, hp_4]; exact hp_2
      · intro x hx
        dsimp only
        rw [Function.update_of_ne (by dsimp [wEx, wDegR, wLvlNext] at hx ⊢; omega)]
        rw [hmf_6 x (by rcases hx with h | h <;> [left; right] <;> dsimp [wEx, wPeelStk, wLvlNext] at h ⊢ <;> omega)]
        dsimp only [st5]
        rw [hmf_4 x (by rcases hx with h | h <;> [left; right] <;> dsimp [wEx, wInAct, wPeelStk, wLvlNext] at h ⊢ <;> omega)]
        dsimp only [st3, mem3]
        rw [Function.update_of_ne (by dsimp [wEx, wLvlNext] at hx ⊢; omega), hm_2]
      · intro u hu
        dsimp only
        rw [Function.update_of_ne (by dsimp [wEx, wDegR]; omega)]
        rw [hmf_6 _ (Or.inl (by dsimp [wEx, wPeelStk]; omega))]
        dsimp only [st5]
        rw [hmf_4 _ (Or.inl (by dsimp [wEx, wInAct]; omega))]
        dsimp only [st3, mem3]
        have hstep_ex : sNext.ex u = if u = q.2.2 then sk.ex q.2.2 + rcVal else sk.ex u := by
          dsimp only [sNext, removeEdgeStep]; simp [hqR, rcVal]
        rw [hstep_ex]
        by_cases huq : u = q.2.2
        · subst huq; simp
        · rw [Function.update_of_ne (by omega), hm_2, hEx u hu]; simp [huq]
      · intro u hu
        dsimp only
        rw [hpeel_push_eq.2 u hu]
        by_cases huq : u = q.2.2
        · subst huq; simp
        · rw [Function.update_of_ne (by omega)]
          rw [hmf_6 _ (Or.inl (by dsimp [wDegR, wPeelStk]; omega))]
          dsimp only [st5]
          rw [hmf_4 _ (Or.inl (by dsimp [wDegR, wInAct]; omega))]
          dsimp only [st3, mem3]
          rw [Function.update_of_ne (by dsimp [wEx, wDegR]; omega), hm_2, hDr u hu]
          simp [huq]
      · intro u hu
        dsimp only
        rw [Function.update_of_ne (by dsimp [wInAct, wDegR]; omega)]
        rw [hmf_6 _ (Or.inl (by dsimp [n, m, H, wInAct, wActStk, wPeelStk]; omega))]
        rw [hact_push_eq.2 u hu]
        exact hIA_4 u hu
      · intro i hi
        dsimp only
        rw [Function.update_of_ne (by dsimp [wActStk, wDegR]; omega)]
        rw [hmf_6 _ (Or.inl (by
          rw [hact_push_eq.1] at hi
          have : i < n := lt_of_lt_of_le hi hact_len_le
          dsimp [wActStk, wPeelStk]; omega))]
        rw [hact_push_eq.1] at hi ⊢
        exact hAS_4 i hi
      · intro i hi
        dsimp only
        rw [Function.update_of_ne (by
          have : i < n := lt_of_lt_of_le hi hnext_peel_len
          dsimp [wDegR, wPeelStk]; omega)]
        rw [hpeel_push_eq.1] at hi ⊢
        exact hPS_6 i hi
    · simp only [Expr.size]; omega
  · apply Triple.nop
    intro sx ⟨hsx, heq⟩
    subst sx
    have hqRf : inR' q.2.2 = false := by
      by_contra hqt
      have hqt' : inR' q.2.2 = true := Bool.eq_true_of_not_eq_false hqt
      simp [hst1_1, hqt'] at heq
    have hs_same : sNext = sk := by
      dsimp only [sNext, removeEdgeStep]; simp [hqRf]
    rw [hs_same]
    refine ⟨fun _ _ _ _ _ _ _ _ => rfl, hst1_AT, hst1_PT, rfl, memFrame_refl _ _ _, hEx, hDr, hIA, hAS, hPS⟩


end MinCostFlow.Expander
