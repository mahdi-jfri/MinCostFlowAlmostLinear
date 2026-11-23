module

public import MinCostFlow.Expander.PruningInitQueueProg

/-!
# WordRAM Pruning Init: Queue Loop and Top-Level initPrune_triple
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

lemma initQueues_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    (st₀ : State) (inR : ℕ → Bool) (ex degR : ℕ → ℕ)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w)
    (houtR : ∀ u < cfg.G.n, st₀.mem (outRAddr + u) = if inR u then 1 else 0)
    (hex : ∀ u < cfg.G.n, st₀.mem (wEx workAddr cfg.G.n cfg.G.m cfg.H + u) = ex u)
    (hdr : ∀ u < cfg.G.n, st₀.mem (wDegR workAddr cfg.G.n cfg.G.m cfg.H + u) = degR u)
    (hia0 : ∀ u < cfg.G.n, st₀.mem (wInAct workAddr cfg.G.n cfg.G.m cfg.H + u) = 0)
    (hex_bd : ∀ u < cfg.G.n, ex u ≤ 2 * cfg.C_cap * cfg.G.m)
    (hdr_bd : ∀ u < cfg.G.n, degR u ≤ 2 * cfg.G.m) :
    Triple w p
      (fun st => st = st₀ ∧ InitPtrRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st)
      initQueuesStmt
      (normalPost fun st' =>
        InitPtrRegs cfg gAddr csrAddr inBAddr outRAddr workAddr
          { st' with regs := Function.update (Function.update st'.regs prActTop 0) prPeelTop 0 } ∧
        st'.pos = st₀.pos ∧
        MemFrame st₀.mem st'.mem (wInAct workAddr cfg.G.n cfg.G.m cfg.H)
          (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H) ∧
        (let actL := (List.range cfg.G.n).filter fun u => inR u && decide (0 < ex u)
         let peelL := (List.range cfg.G.n).filter fun u => inR u && decide (degR u < cfg.θ_out_nat)
         st'.regs prActTop = actL.length ∧
         st'.regs prPeelTop = peelL.length ∧
         (∀ u < cfg.G.n, st'.mem (wInAct workAddr cfg.G.n cfg.G.m cfg.H + u) =
           if (inR u && decide (0 < ex u)) then 1 else 0) ∧
         (∀ i < actL.length, st'.mem (wActStk workAddr cfg.G.n cfg.G.m cfg.H + i) = actL.getD i 0) ∧
         (∀ i < peelL.length, st'.mem (wPeelStk workAddr cfg.G.n cfg.G.m cfg.H + i) = peelL.getD i 0)))
      (fun _ => 75 * cfg.G.n + 10) := by
  intro st ω ⟨hst, hptrs⟩
  subst st
  set n := cfg.G.n
  set m := cfg.G.m
  set H := cfg.H
  set actP : ℕ → Bool := fun u => inR u && decide (0 < ex u)
  set peelP : ℕ → Bool := fun u => inR u && decide (degR u < cfg.θ_out_nat)
  have hwb := hw
  unfold PruneWordBound pruneWorkSpace at hwb
  have h0lt : 0 < 2 ^ w := by omega
  have h1lt : 1 < 2 ^ w := by omega
  have hdisj_outR_work := hdisj.2.2.2.2.2.2
  let eCond : Expr := .bin .lt (.reg prU) (.reg prN)
  have heSize : eCond.size = 3 := rfl
  let Inv : ℕ → State → Prop := fun k st =>
    k ≤ n ∧ st.regs prU = k ∧
    (∀ r, r ≠ prU → r ≠ prTmp1 → r ≠ prTmp2 → r ≠ prActTop → r ≠ prPeelTop → st.regs r = st₀.regs r) ∧
    st.regs prActTop = ((List.range k).filter actP).length ∧
    st.regs prPeelTop = ((List.range k).filter peelP).length ∧
    st.pos = st₀.pos ∧
    MemFrame st₀.mem st.mem (wInAct workAddr n m H) (wLvlNext workAddr n m H) ∧
    (∀ u < n, st.mem (wInAct workAddr n m H + u) =
      if decide (u < k) && actP u then 1 else 0) ∧
    (∀ i < ((List.range k).filter actP).length,
      st.mem (wActStk workAddr n m H + i) = ((List.range k).filter actP).getD i 0) ∧
    (∀ i < ((List.range k).filter peelP).length,
      st.mem (wPeelStk workAddr n m H + i) = ((List.range k).filter peelP).getD i 0)
  have hloop : Triple w p (Inv 0)
      (.loop eCond
        (seqStmts [
          .assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prU))),
          initQueueOneVertStmt,
          .assign prU (.bin .add (.reg prU) (.const 1))
        ]))
      (normalPost fun st => Inv n st)
      (fun _ => 75 * n + 4) := by
    apply (Triple.loop_inv (α := ℕ)
      (m := fun k => n - k) (rem := fun k => 75 * (n - k) + 4)
      (condVal := fun st => if st.regs prU < st.regs prN then 1 else 0)
      (Inv := Inv) ?_ ?_ ?_ 0).mono_cost (fun _ _ => le_rfl)
    · rintro k st ⟨_, _, hr, _, _, _, _, _, _, _⟩
      have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_n
      simp only [eCond, Expr.eval, hrn, WordRAM.BinOp.eval]
      by_cases hcmp : st.regs prU < n <;> simp [hcmp, h1lt, h0lt]
    · rintro k st hInv heq
      rcases hInv with ⟨hk, hru, hr, hAT, hPT, hp, hmf, hmIA, hmAS, hmPS⟩
      have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_n
      have hkEq : k = n := by
        by_contra hne
        have hlt : k < n := by omega
        rw [hru, hrn] at heq; simp [hlt] at heq
      subst hkEq
      exact ⟨⟨le_rfl, hru, hr, hAT, hPT, hp, hmf, hmIA, hmAS, hmPS⟩, by simp [eCond, Expr.size]⟩
    · rintro k st ⟨hk, hru, hr, hAT, hPT, hp, hmf, hmIA, hmAS, hmPS⟩ hne
      have hrn : st.regs prN = n := (hr prN (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_n
      have hk_lt : k < n := by
        by_contra hge
        rw [hru, hrn] at hne; simp [hge] at hne
      have hrOutR : st.regs prOutR = outRAddr := (hr prOutR (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_outR
      have hrEX : st.regs prEx = wEx workAddr n m H := (hr prEx (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_ex
      have hrDR : st.regs prDegR = wDegR workAddr n m H := (hr prDegR (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_degR
      have hrIA : st.regs prInAct = wInAct workAddr n m H := (hr prInAct (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_inAct
      have hrAS : st.regs prActStk = wActStk workAddr n m H := (hr prActStk (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_actStk
      have hrPS : st.regs prPeelStk = wPeelStk workAddr n m H := (hr prPeelStk (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_peelStk
      have hrTh : st.regs prTheta = cfg.θ_out_nat := (hr prTheta (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_theta
      have houtRk : outRAddr + k < 2 ^ w := by omega
      have hk1 : k + 1 < 2 ^ w := by omega
      have hm_outR : st.mem (outRAddr + k) = if inR k then 1 else 0 := by
        rw [hmf (outRAddr + k) (by
          dsimp [wInAct, wLvlNext]
          unfold pruneWorkSpace at hdisj_outR_work
          rcases hdisj_outR_work with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
        exact houtR k hk_lt
      have hm_ex : st.mem (wEx workAddr n m H + k) = ex k := by
        rw [hmf (wEx workAddr n m H + k) (Or.inl (by dsimp [wEx, wInAct]; omega))]
        exact hex k hk_lt
      have hm_dr : st.mem (wDegR workAddr n m H + k) = degR k := by
        rw [hmf (wDegR workAddr n m H + k) (Or.inl (by dsimp [wDegR, wInAct]; omega))]
        exact hdr k hk_lt
      have hex_lt : ex k < 2 ^ w := by
        have h1 : ex k ≤ 2 * cfg.C_cap * m := hex_bd k hk_lt
        have h2 : 2 * (cfg.C_cap * m) ≤ 8 * (cfg.C_cap * m) := Nat.mul_le_mul_right _ (by omega)
        have h3 : 2 * cfg.C_cap * m = 2 * (cfg.C_cap * m) := Nat.mul_assoc _ _ _
        have h4 : 8 * cfg.C_cap * m = 8 * (cfg.C_cap * m) := Nat.mul_assoc _ _ _
        omega
      have hdr_lt : degR k < 2 ^ w := by have := hdr_bd k hk_lt; omega
      have hactLen : ((List.range k).filter actP).length ≤ k := by
        calc
          ((List.range k).filter actP).length ≤ (List.range k).length := List.length_filter_le _ _
          _ = k := List.length_range
      have hpeelLen : ((List.range k).filter peelP).length ≤ k := by
        calc
          ((List.range k).filter peelP).length ≤ (List.range k).length := List.length_filter_le _ _
          _ = k := List.length_range
      refine ⟨70, ?_⟩
      intro st1 ω2 hst1
      subst st1
      have hbody : ∃ o st' c1,
          Runs w p ω2
            (seqStmts [
              .assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prU))),
              initQueueOneVertStmt,
              .assign prU (.bin .add (.reg prU) (.const 1))
            ]) st o st' c1 ∧
          normalPost (fun st' => Inv (k + 1) st') o st' ∧ c1 ≤ 70 := by
        dsimp only [seqStmts]
        refine runs_start_le (T := 70) ?_
        apply runs_seq_assign_le (v := if inR k then 1 else 0)
        · exact eval_load_add_regs hrOutR hru houtRk hm_outR (by split_ifs <;> omega)
        apply runs_seq_triple_le (initQueueOneVert_triple _ inR ex degR hw hk_lt)
        · refine ⟨rfl, by simp [hru], by simp, by simpa using hrEX, by simpa using hrDR,
            by simpa using hrIA, by simpa using hrAS, by simpa using hrPS,
            by simpa using hAT, by simpa using hPT, by simpa using hrTh,
            hactLen, hpeelLen, hm_ex, hm_dr, hex_lt, hdr_lt, hmIA, hmAS, hmPS⟩
        intro st2 ⟨hr2, hAT2, hPT2, hp2, hmf2, hmIA2, hmAS2, hmPS2⟩
        apply runs_assign_le (v := k + 1)
        · simp only [Expr.eval, hr2 prU (by decide) (by decide) (by decide),
            Function.update_of_ne (by decide : prU ≠ prTmp1), hru, h1lt,
            WordRAM.BinOp.eval, hk1, ↓reduceIte]
        · refine ⟨hk_lt, by simp, fun r h1 h2 h3 h4 h5 => ?_,
            by simpa [Function.update_of_ne (by decide : prActTop ≠ prU)] using hAT2,
            by simpa [Function.update_of_ne (by decide : prPeelTop ≠ prU)] using hPT2,
            by simpa using hp2.trans hp, memFrame_trans hmf hmf2, hmIA2, hmAS2, hmPS2⟩
          dsimp only
          rw [Function.update_of_ne h1, hr2 r h3 h4 h5]
          dsimp only
          rw [Function.update_of_ne h2]
          exact hr r h1 h2 h3 h4 h5
        · simp only [Expr.size]; omega
      obtain ⟨o, st_next, c_b, hrun_b, hpost_b, hc_b⟩ := hbody
      cases o with
      | returned _ => exact absurd hpost_b (by simp [normalPost])
      | normal =>
          exact ⟨.normal, st_next, c_b, hrun_b, ⟨k + 1, hpost_b, by omega, by omega⟩, hc_b⟩
  refine runs_start_le ?_
  dsimp only [initQueuesStmt, seqStmts]
  apply runs_seq_assign_le (v := 0)
  · simp [Expr.eval, h0lt]
  apply runs_triple_le hloop
  · refine ⟨Nat.zero_le _, by simp,
      fun r h1 _ _ _ _ => by simp [Function.update_of_ne h1],
      by simp [hptrs.reg_actTop], by simp [hptrs.reg_peelTop],
      rfl, fun _ _ => rfl, fun u hu => by simp [hia0 u hu],
      fun _ h => by simp at h, fun _ h => by simp at h⟩
  · intro o st1 h1
    cases o with
    | returned _ => exact absurd h1 (by simp [normalPost])
    | normal =>
        rcases h1 with ⟨_, _, hr1, hAT1, hPT1, hp1, hmf1, hmIA1, hmAS1, hmPS1⟩
        have hptr_upd : InitPtrRegs cfg gAddr csrAddr inBAddr outRAddr workAddr
            { st1 with regs := Function.update (Function.update st1.regs prActTop 0) prPeelTop 0 } :=
          { reg_g := by simp [hr1 prG (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_g]
            reg_csr := by simp [hr1 prCsr (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_csr]
            reg_inB := by simp [hr1 prInB (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_inB]
            reg_outR := by simp [hr1 prOutR (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_outR]
            reg_work := by simp [hr1 prWork (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_work]
            reg_ccap := by simp [hr1 prCcap (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_ccap]
            reg_H := by simp [hr1 prH (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_H]
            reg_theta := by simp [hr1 prTheta (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_theta]
            reg_n := by simp [hr1 prN (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_n]
            reg_m := by simp [hr1 prM (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_m]
            reg_actTop := by simp
            reg_peelTop := by simp
            reg_degX := by simp [hr1 prDegX (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_degX]
            reg_hArr := by simp [hr1 prHArr (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_hArr]
            reg_cur := by simp [hr1 prCur (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_cur]
            reg_abs := by simp [hr1 prAbs (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_abs]
            reg_ex := by simp [hr1 prEx (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_ex]
            reg_degR := by simp [hr1 prDegR (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_degR]
            reg_inAct := by simp [hr1 prInAct (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_inAct]
            reg_actStk := by simp [hr1 prActStk (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_actStk]
            reg_peelStk := by simp [hr1 prPeelStk (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_peelStk]
            reg_lvlNext := by simp [hr1 prLvlNext (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_lvlNext]
            reg_lvlPrev := by simp [hr1 prLvlPrev (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_lvlPrev]
            reg_remArr := by simp [hr1 prRemArr (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_remArr]
            reg_flowEnc := by simp [hr1 prFlowEnc (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_flowEnc]
            reg_lvlVol := by simp [hr1 prLvlVol (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_lvlVol]
            reg_lvlHead := by simp [hr1 prLvlHead (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_lvlHead]
            reg_adjV := by simp [hr1 prCsrAdjV (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_adjV]
            reg_adjH := by simp [hr1 prCsrAdjH (by decide) (by decide) (by decide) (by decide) (by decide), hptrs.reg_adjH] }
        refine ⟨hptr_upd, hp1, hmf1, hAT1, hPT1, ?_, hmAS1, hmPS1⟩
        intro u hu
        simpa [actP, hu] using hmIA1 u hu
  · simp only [Expr.size]; omega

/-! ## 5. Top-Level `initPrune_triple` -/

theorem initPrune_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ} (st₀ : State)
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hval : cfg.Valid)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hg_w : gAddr + cfg.G.encode.length < 2 ^ w)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (hinB_w : inBAddr + cfg.G.n < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w)
    (hG : GraphAt st₀.mem gAddr cfg.G)
    (hCsr : HasCsrAt st₀.mem csrAddr cfg.G)
    (hinB : ∀ b, b ∈ cfg.B ↔ b < cfg.G.n ∧ st₀.mem (inBAddr + b) ≠ 0) :
    Triple w p
      (fun st => st = st₀ ∧ InitRegPre cfg gAddr csrAddr inBAddr outRAddr workAddr st)
      initPruneStmt
      (normalPost fun st' =>
        st'.pos = st₀.pos ∧
        PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
          workAddr (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
        PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr
          (initStateList cfg (List.range cfg.G.n).reverse) (fun _ => []) st')
      (fun _ => 170 * cfg.G.n + 140 * cfg.G.m + 30 * (cfg.H + 1) + 210) := by
  intro st ω ⟨hst, hreg0⟩
  subst st
  set n := cfg.G.n
  set m := cfg.G.m
  set H := cfg.H
  set s₀ := initStateList cfg (List.range n).reverse
  have hXList : (List.range n).reverse.Nodup ∧ ∀ x, x ∈ (List.range n).reverse ↔ x ∈ cfg.X := by
    refine ⟨List.nodup_reverse.mpr List.nodup_range, fun x => by simp [hcfgX]⟩
  have hinR_eq : ∀ u, s₀.inR u = decide (u ∈ cfg.X ∧ u ∉ cfg.B) := fun _ => rfl
  have hex_eq_prefix : ∀ u < n, s₀.ex u = exPrefix cfg.G s₀.inR cfg.C_cap m u := by
    intro u _
    have hc : cfg.incEdges u = csrIncAux u 0 cfg.G.edges := by
      unfold PruneCfg.incEdges PruneCfg.edges
      rw [hcfgX]
      change incEdgesAux u 0 (cfg.G.inside cfg.G.verts) = _
      rw [inside_verts_of_isValid hval.1]
      clear hinR_eq
      suffices h : ∀ k L, incEdgesAux u k L = csrIncAux u k L from h 0 cfg.G.edges
      intro k L
      induction L generalizing k with
      | nil => rfl
      | cons e rest ih =>
        rcases e with ⟨a, b⟩
        dsimp only [incEdgesAux, csrIncAux]
        by_cases hab : a = b <;> by_cases hau : a = u <;> by_cases hbu : b = u <;>
          simp [hab, hau, hbu, ih]
    dsimp only [s₀, initStateList, exPrefix, m, Cited.Graph.m]
    rw [List.take_length, hc]
  have hdegR_eq_prefix : ∀ u < n, s₀.degR u = degRPrefix cfg.G s₀.inR m u := by
    intro u _
    have h := degRPrefix_full hcfgX hval.1 s₀.inR u
    simpa only [s₀, initStateList] using h.symm
  have hdegX_eq_prefix : ∀ u < n, cfg.degX u = degXPrefix cfg.G m u := fun u _ =>
    (degXPrefix_full hcfgX hval.1 u).symm
  have hdisj_g_outR := hdisj.1
  have hdisj_csr_outR := hdisj.2.1
  have hdisj_inB_outR := hdisj.2.2.1
  have hdisj_g_work := hdisj.2.2.2.1
  have hdisj_csr_work := hdisj.2.2.2.2.1
  have hdisj_inB_work := hdisj.2.2.2.2.2.1
  have hdisj_outR_work := hdisj.2.2.2.2.2.2
  refine runs_start_le ?_
  dsimp only [initPruneStmt, seqStmts]
  apply runs_seq_triple_le (initSetupRegs_triple st₀ hw hg_w hcsr_w hG)
  · exact ⟨rfl, hreg0⟩
  intro st1 ⟨hm1, hp1, hptrs1⟩
  have hinB1 : ∀ b, b ∈ cfg.B ↔ b < n ∧ st1.mem (inBAddr + b) ≠ 0 := by rw [hm1]; exact hinB
  apply runs_seq_triple_le (initZeroVerts_triple st1 hw hdisj hinB_w houtR_w hinB1)
  · exact ⟨rfl, hptrs1⟩
  intro st2 ⟨hptrs2, hp2, hpr2, hall2⟩
  have hpr02 : PreservedOutside2 st₀.mem st2.mem outRAddr (outRAddr + n)
      workAddr (workAddr + pruneWorkSpace n m H) := by
    intro a ha1 ha2
    rw [← hm1]
    exact hpr2 a ha1 (by rcases ha2 with h | h <;> [exact Or.inl h; exact Or.inr (by unfold pruneWorkSpace at h; omega)])
  apply runs_seq_triple_le (initZeroLevels_triple st2 hw)
  · exact ⟨rfl, hptrs2⟩
  intro st3 ⟨hptrs3, hp3, hmf3, hlvl3⟩
  have hpr03 : PreservedOutside2 st₀.mem st3.mem outRAddr (outRAddr + n)
      workAddr (workAddr + pruneWorkSpace n m H) :=
    init_preservedOutside2_trans hpr02
      (memFrame_to_preserved2_snd (init_memFrame_weaken hmf3 (by dsimp [wLvlVol]; omega) le_rfl))
  apply runs_seq_triple_le (initZeroFlows_triple st3 hw)
  · exact ⟨rfl, hptrs3⟩
  intro st4 ⟨hptrs4, hp4, hmf4, hfl4⟩
  have hpr04 : PreservedOutside2 st₀.mem st4.mem outRAddr (outRAddr + n)
      workAddr (workAddr + pruneWorkSpace n m H) :=
    init_preservedOutside2_trans hpr03
      (memFrame_to_preserved2_snd (init_memFrame_weaken hmf4 (by dsimp [wFlowEnc]; omega)
        (by dsimp [wLvlVol]; unfold pruneWorkSpace; omega)))
  have hG4 : GraphAt st4.mem gAddr cfg.G := fun i hi => by
    rw [hpr04 (gAddr + i) (by rcases hdisj_g_outR with h | h <;> omega)
      (by rcases hdisj_g_work with h | h <;> omega)]
    exact hG i hi
  have houtR4 : ∀ u < n, st4.mem (outRAddr + u) = if s₀.inR u then 1 else 0 := by
    intro u hu
    have hdisj_out : outRAddr + u < wFlowEnc workAddr n m H ∨
        wLvlVol workAddr n m H ≤ outRAddr + u := by
      dsimp [wFlowEnc, wLvlVol]; unfold pruneWorkSpace at hdisj_outR_work
      rcases hdisj_outR_work with h | h <;> omega
    have hdisj_out3 : outRAddr + u < wLvlVol workAddr n m H ∨
        workAddr + pruneWorkSpace n m H ≤ outRAddr + u := by
      dsimp [wLvlVol]; unfold pruneWorkSpace at hdisj_outR_work ⊢
      rcases hdisj_outR_work with h | h <;> omega
    rw [hmf4 _ hdisj_out, hmf3 _ hdisj_out3, (hall2 u hu).1]
    have hu_inR : s₀.inR u = true ↔ u ∉ cfg.B := by
      simp [s₀, initStateList, hcfgX, hu]
    by_cases huB : u ∈ cfg.B
    · have : ¬(s₀.inR u = true) := fun h => absurd (hu_inR.mp h) (by simp [huB])
      have hf : s₀.inR u = false := Bool.eq_false_iff.mpr this
      simp [huB, hf]
    · have ht : s₀.inR u = true := hu_inR.mpr huB
      simp [huB, ht]
  have hdx4 : ∀ u < n, st4.mem (wDegX workAddr n m H + u) = 0 := fun u hu => by
    rw [hmf4 _ (Or.inl (by dsimp [wDegX, wFlowEnc]; omega)),
        hmf3 _ (Or.inl (by dsimp [wDegX, wLvlVol]; omega))]
    exact (hall2 u hu).2.1
  have hdr4 : ∀ u < n, st4.mem (wDegR workAddr n m H + u) = 0 := fun u hu => by
    rw [hmf4 _ (Or.inl (by dsimp [wDegR, wFlowEnc]; omega)),
        hmf3 _ (Or.inl (by dsimp [wDegR, wLvlVol]; omega))]
    exact (hall2 u hu).2.2.2.2.2.2.1
  have hex4 : ∀ u < n, st4.mem (wEx workAddr n m H + u) = 0 := fun u hu => by
    rw [hmf4 _ (Or.inl (by dsimp [wEx, wFlowEnc]; omega)),
        hmf3 _ (Or.inl (by dsimp [wEx, wLvlVol]; omega))]
    exact (hall2 u hu).2.2.2.2.2.1
  have hia4 : ∀ u < n, st4.mem (wInAct workAddr n m H + u) = 0 := fun u hu => by
    rw [hmf4 _ (Or.inl (by dsimp [wInAct, wFlowEnc]; omega)),
        hmf3 _ (Or.inl (by dsimp [wInAct, wLvlVol]; omega))]
    exact (hall2 u hu).2.2.2.2.2.2.2.1
  apply runs_seq_triple_le
    (initScanEdges_triple st4 s₀.inR hw hdisj hg_w houtR_w hval.1 hG4 houtR4 hdx4 hdr4 hex4)
  · exact ⟨rfl, hptrs4⟩
  intro st5 ⟨hptrs5, hp5, hmf5, hmid5, hdx5, hdr5, hex5⟩
  have hpr05 : PreservedOutside2 st₀.mem st5.mem outRAddr (outRAddr + n)
      workAddr (workAddr + pruneWorkSpace n m H) :=
    init_preservedOutside2_trans hpr04
      (memFrame_to_preserved2_snd (init_memFrame_weaken hmf5 le_rfl (by dsimp [wInAct]; unfold pruneWorkSpace; omega)))
  have houtR5 : ∀ u < n, st5.mem (outRAddr + u) = if s₀.inR u then 1 else 0 := fun u hu => by
    rw [hmf5 _ (by
      dsimp [wInAct]; unfold pruneWorkSpace at hdisj_outR_work
      rcases hdisj_outR_work with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
    exact houtR4 u hu
  have hex5' : ∀ u < n, st5.mem (wEx workAddr n m H + u) = s₀.ex u := fun u hu => by
    rw [hex5 u hu, hex_eq_prefix u hu]
  have hdr5' : ∀ u < n, st5.mem (wDegR workAddr n m H + u) = s₀.degR u := fun u hu => by
    rw [hdr5 u hu, hdegR_eq_prefix u hu]
  have hia5 : ∀ u < n, st5.mem (wInAct workAddr n m H + u) = 0 := fun u hu => by
    rw [hmf5 _ (Or.inr (by dsimp [wInAct]; omega))]
    exact hia4 u hu
  have hex_bd : ∀ u < n, s₀.ex u ≤ 2 * cfg.C_cap * m := fun u hu => by
    rw [hex_eq_prefix u hu]; exact exPrefix_le_bound s₀.inR cfg.C_cap m u hu
  have hdr_bd : ∀ u < n, s₀.degR u ≤ 2 * m := fun u hu => by
    rw [hdegR_eq_prefix u hu]; exact degRPrefix_le_two_mul_m s₀.inR m u
  obtain ⟨o, st6, c6, hrun6, hpost6, hc6⟩ :=
    (initQueues_triple st5 s₀.inR s₀.ex s₀.degR hw hdisj houtR_w houtR5 hex5' hdr5' hia5 hex_bd hdr_bd).runs
      ω ⟨rfl, hptrs5⟩
  cases o with
  | returned _ => exact absurd hpost6 (by simp [normalPost])
  | normal =>
      rcases hpost6 with ⟨hptrs6, hp6, hmf6, hAT6, hPT6, hIA6, hAS6, hPS6⟩
      refine ⟨.normal, st6, c6, hrun6, ?_, by omega⟩
      have hpr06 : PreservedOutside2 st₀.mem st6.mem outRAddr (outRAddr + n)
          workAddr (workAddr + pruneWorkSpace n m H) :=
        init_preservedOutside2_trans hpr05
          (memFrame_to_preserved2_snd (init_memFrame_weaken hmf6 (by dsimp [wInAct]; omega)
            (by dsimp [wLvlNext]; unfold pruneWorkSpace; omega)))
      have hG6 : GraphAt st6.mem gAddr cfg.G := fun i hi => by
        rw [hpr06 (gAddr + i) (by rcases hdisj_g_outR with h | h <;> omega)
          (by rcases hdisj_g_work with h | h <;> omega)]
        exact hG i hi
      have hCsr6 : HasCsrAt st6.mem csrAddr cfg.G := by
        refine ⟨fun u hu => ?_, fun u hu j hj => ?_⟩
        · rw [hpr06 (csrAddr + u) (by rcases hdisj_csr_outR with h | h <;> omega)
            (by rcases hdisj_csr_work with h | h <;> omega)]
          exact hCsr.1 u hu
        · have hj_lt : csrOff cfg.G u + j < 2 * m := by
            have hs := csrOff_succ cfg.G u
            have hle := csrOff_le_two_mul_m cfg.G (u + 1)
            dsimp [m, Cited.Graph.m] at *
            omega
          refine ⟨?_, ?_⟩
          · rw [hpr06 (csrAddr + 2 * n + 1 + csrOff cfg.G u + j)
              (by rcases hdisj_csr_outR with h | h <;> omega)
              (by rcases hdisj_csr_work with h | h <;> omega)]
            exact (hCsr.2 u hu j hj).1
          · rw [hpr06 (csrAddr + 2 * n + 1 + 2 * m + csrOff cfg.G u + j)
              (by rcases hdisj_csr_outR with h | h <;> omega)
              (by rcases hdisj_csr_work with h | h <;> omega)]
            exact (hCsr.2 u hu j hj).2
      have hinB6 : ∀ b, b ∈ cfg.B ↔ b < n ∧ st6.mem (inBAddr + b) ≠ 0 := by
        intro b
        constructor
        · intro hbB
          have hb0 := (hinB b).mp hbB
          refine ⟨hb0.1, ?_⟩
          rw [hpr06 (inBAddr + b) (by rcases hdisj_inB_outR with h | h <;> omega)
            (by rcases hdisj_inB_work with h | h <;> omega)]
          exact hb0.2
        · intro ⟨hbn, hnz⟩
          rw [hpr06 (inBAddr + b) (by rcases hdisj_inB_outR with h | h <;> omega)
            (by rcases hdisj_inB_work with h | h <;> omega)] at hnz
          exact (hinB b).mpr ⟨hbn, hnz⟩
      have hact_eq : s₀.active = (List.range n).reverse.filter (fun u => s₀.inR u && decide (0 < s₀.ex u)) := rfl
      have hpeel_eq : s₀.peelQ = (List.range n).reverse.filter (fun u => s₀.inR u && decide (s₀.degR u < cfg.θ_out_nat)) := rfl
      have hact_len : s₀.active.length = ((List.range n).filter (fun u => s₀.inR u && decide (0 < s₀.ex u))).length := by
        rw [hact_eq, List.filter_reverse, List.length_reverse]
      have hpeel_len : s₀.peelQ.length = ((List.range n).filter (fun u => s₀.inR u && decide (s₀.degR u < cfg.θ_out_nat))).length := by
        rw [hpeel_eq, List.filter_reverse, List.length_reverse]
      have hframe56_pre : ∀ addr < wInAct workAddr n m H, st6.mem addr = st5.mem addr := fun addr ha =>
        hmf6 addr (Or.inl ha)
      have hframe56_post : ∀ addr, wLvlNext workAddr n m H ≤ addr → st6.mem addr = st5.mem addr := fun addr ha =>
        hmf6 addr (Or.inr ha)
      have hframe45_post : ∀ addr, wInAct workAddr n m H ≤ addr → st5.mem addr = st4.mem addr := fun addr ha =>
        hmf5 addr (Or.inr ha)
      have hframe34_post : ∀ addr, wLvlVol workAddr n m H ≤ addr → st4.mem addr = st3.mem addr := fun addr ha =>
        hmf4 addr (Or.inr ha)
      have hframe23_pre : ∀ addr < wLvlVol workAddr n m H, st3.mem addr = st2.mem addr := fun addr ha =>
        hmf3 addr (Or.inl ha)
      have hframe34_pre : ∀ addr < wFlowEnc workAddr n m H, st4.mem addr = st3.mem addr := fun addr ha =>
        hmf4 addr (Or.inl ha)
      have hmid_zero : ∀ addr, wHArr workAddr n m H ≤ addr → addr < wEx workAddr n m H → st6.mem addr = st4.mem addr := by
        intro addr ha1 ha2
        rw [hframe56_pre addr (by dsimp [wInAct, wEx] at *; omega), hmid5 addr ha1 ha2]
      refine ⟨hp6.trans (hp5.trans (hp4.trans (hp3.trans (hp2.trans hp1)))), hpr06, {
        cfg_X := hcfgX
        cfg_valid := hval
        reg_g := by simpa using hptrs6.reg_g
        reg_csr := by simpa using hptrs6.reg_csr
        reg_inB := by simpa using hptrs6.reg_inB
        reg_outR := by simpa using hptrs6.reg_outR
        reg_work := by simpa using hptrs6.reg_work
        reg_ccap := by simpa using hptrs6.reg_ccap
        reg_H := by simpa using hptrs6.reg_H
        reg_theta := by simpa using hptrs6.reg_theta
        reg_n := by simpa using hptrs6.reg_n
        reg_m := by simpa using hptrs6.reg_m
        reg_actTop := by rw [hAT6, hact_len]
        reg_peelTop := by rw [hPT6, hpeel_len]
        reg_degX := by simpa using hptrs6.reg_degX
        reg_hArr := by simpa using hptrs6.reg_hArr
        reg_cur := by simpa using hptrs6.reg_cur
        reg_abs := by simpa using hptrs6.reg_abs
        reg_ex := by simpa using hptrs6.reg_ex
        reg_degR := by simpa using hptrs6.reg_degR
        reg_inAct := by simpa using hptrs6.reg_inAct
        reg_actStk := by simpa using hptrs6.reg_actStk
        reg_peelStk := by simpa using hptrs6.reg_peelStk
        reg_lvlNext := by simpa using hptrs6.reg_lvlNext
        reg_lvlPrev := by simpa using hptrs6.reg_lvlPrev
        reg_remArr := by simpa using hptrs6.reg_remArr
        reg_flowEnc := by simpa using hptrs6.reg_flowEnc
        reg_lvlVol := by simpa using hptrs6.reg_lvlVol
        reg_lvlHead := by simpa using hptrs6.reg_lvlHead
        reg_adjV := by simpa using hptrs6.reg_adjV
        reg_adjH := by simpa using hptrs6.reg_adjH
        graph_at := hG6
        csr_at := hCsr6
        inB_eq := hinB6
        outR_eq := fun u hu => by
          rw [hmf6 _ (by dsimp [wInAct, wLvlNext]; unfold pruneWorkSpace at hdisj_outR_work; rcases hdisj_outR_work with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
          exact houtR5 u hu
        degX_eq := fun u hu => by
          rw [hframe56_pre _ (by dsimp [wDegX, wInAct]; omega), hdx5 u hu, hdegX_eq_prefix u hu]
        h_eq := fun u hu => by
          rw [hmid_zero _ (by dsimp [wHArr]; omega) (by dsimp [wHArr, wEx]; omega),
              hframe34_pre _ (by dsimp [wHArr, wFlowEnc]; omega),
              hframe23_pre _ (by dsimp [wHArr, wLvlVol]; omega)]
          exact (hall2 u hu).2.2.1
        cur_eq := fun u hu => by
          rw [hmid_zero _ (by dsimp [wCur, wHArr]; omega) (by dsimp [wCur, wEx]; omega),
              hframe34_pre _ (by dsimp [wCur, wFlowEnc]; omega),
              hframe23_pre _ (by dsimp [wCur, wLvlVol]; omega)]
          exact (hall2 u hu).2.2.2.1
        abs_eq := fun u hu => by
          rw [hmid_zero _ (by dsimp [wAbs, wHArr]; omega) (by dsimp [wAbs, wEx]; omega),
              hframe34_pre _ (by dsimp [wAbs, wFlowEnc]; omega),
              hframe23_pre _ (by dsimp [wAbs, wLvlVol]; omega)]
          exact (hall2 u hu).2.2.2.2.1
        ex_eq := fun u hu => by
          rw [hframe56_pre _ (by dsimp [wEx, wInAct]; omega)]
          exact hex5' u hu
        degR_eq := fun u hu => by
          rw [hframe56_pre _ (by dsimp [wDegR, wInAct]; omega)]
          exact hdr5' u hu
        inAct_eq := fun u hu => by
          rw [hIA6 u hu]
          have hia : s₀.inActive u = (s₀.inR u && decide (0 < s₀.ex u)) := by
            simp [s₀, initStateList, hcfgX]
          simp [hia]
        actStk_eq := fun i hi => by
          rw [hAS6 i (hact_len ▸ hi)]
          simpa [hact_eq] using (filter_range_reverse_getD n (fun u => s₀.inR u && decide (0 < s₀.ex u)) i (hact_len ▸ hi)).symm
        peelStk_eq := fun i hi => by
          rw [hPS6 i (hpeel_len ▸ hi)]
          simpa [hpeel_eq] using (filter_range_reverse_getD n (fun u => s₀.inR u && decide (s₀.degR u < cfg.θ_out_nat)) i (hpeel_len ▸ hi)).symm
        flowEnc_eq := fun idx hidx => by
          rw [hframe56_post _ (by dsimp [wFlowEnc, wLvlNext]; omega),
              hframe45_post _ (by dsimp [wFlowEnc, wInAct]; omega),
              hfl4 idx hidx]
          simp [s₀, initStateList]
        lvlVol_H := by
          rw [hframe56_post _ (by dsimp [wLvlVol, wLvlNext]; omega),
              hframe45_post _ (by dsimp [wLvlVol, wInAct]; omega),
              hframe34_post _ (by dsimp [wLvlVol]; omega)]
          exact (hlvl3 H (by omega)).1
        lvlVol_eq := fun ℓ h1 h2 => by
          rw [hframe56_post _ (by dsimp [wLvlVol, wLvlNext]; omega),
              hframe45_post _ (by dsimp [wLvlVol, wInAct]; omega),
              hframe34_post _ (by dsimp [wLvlVol]; omega),
              (hlvl3 ℓ (by omega)).1]
          unfold volAtLevel
          symm
          apply Finset.sum_eq_zero
          intro x _
          simp only [s₀, initStateList]
          split_ifs with hs
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at hs; omega
          · rfl
        buckets_nodup := fun _ _ _ => List.nodup_nil
        buckets_mem := fun ℓ h1 _ x => by
          simp only [List.not_mem_nil, false_iff]
          rintro ⟨_, _, heq⟩
          have : (0 : ℕ) = ℓ := heq
          omega
        buckets_dl := fun ℓ h1 h2 => by
          change st6.mem (wLvlHead workAddr n m H + ℓ) = n
          rw [hframe56_post _ (by dsimp [wLvlHead, wLvlNext]; omega),
              hframe45_post _ (by dsimp [wLvlHead, wInAct]; omega),
              hframe34_post _ (by dsimp [wLvlHead, wLvlVol]; omega)]
          exact (hlvl3 ℓ (by omega)).2
        ex_bound := fun u hu => by
          have h1 := hex_bd u hu
          have h2 : 2 * cfg.C_cap * cfg.G.m ≤ 4 * cfg.C_cap * cfg.G.m :=
            Nat.mul_le_mul_right _ (by omega)
          exact le_trans h1 h2
        prune_inv := initStateList_inv hval hXList
        peelQ_inv := initStateList_peelQ_spec hXList }⟩


end MinCostFlow.Expander
