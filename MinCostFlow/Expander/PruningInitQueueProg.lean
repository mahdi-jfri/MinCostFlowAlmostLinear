module

public import MinCostFlow.Expander.PruningInitScanProg

/-!
# WordRAM Pruning Init: Scan Edges and Queue Single Vertex
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

lemma initScanEdges_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    (st₀ : State) (inR : ℕ → Bool)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hg_w : gAddr + cfg.G.encode.length < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w)
    (hval : cfg.G.IsValid)
    (hG : GraphAt st₀.mem gAddr cfg.G)
    (houtR : ∀ u < cfg.G.n, st₀.mem (outRAddr + u) = if inR u then 1 else 0)
    (hdx0 : ∀ u < cfg.G.n, st₀.mem (wDegX workAddr cfg.G.n cfg.G.m cfg.H + u) = 0)
    (hdr0 : ∀ u < cfg.G.n, st₀.mem (wDegR workAddr cfg.G.n cfg.G.m cfg.H + u) = 0)
    (hex0 : ∀ u < cfg.G.n, st₀.mem (wEx workAddr cfg.G.n cfg.G.m cfg.H + u) = 0) :
    Triple w p
      (fun st => st = st₀ ∧ InitPtrRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st)
      initScanEdgesStmt
      (normalPost fun st' =>
        InitPtrRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st' ∧
        st'.pos = st₀.pos ∧
        MemFrame st₀.mem st'.mem workAddr (wInAct workAddr cfg.G.n cfg.G.m cfg.H) ∧
        (∀ a, wHArr workAddr cfg.G.n cfg.G.m cfg.H ≤ a →
          a < wEx workAddr cfg.G.n cfg.G.m cfg.H → st'.mem a = st₀.mem a) ∧
        (∀ u < cfg.G.n, st'.mem (wDegX workAddr cfg.G.n cfg.G.m cfg.H + u) = degXPrefix cfg.G cfg.G.m u) ∧
        (∀ u < cfg.G.n, st'.mem (wDegR workAddr cfg.G.n cfg.G.m cfg.H + u) = degRPrefix cfg.G inR cfg.G.m u) ∧
        (∀ u < cfg.G.n, st'.mem (wEx workAddr cfg.G.n cfg.G.m cfg.H + u) = exPrefix cfg.G inR cfg.C_cap cfg.G.m u))
      (fun _ => 115 * cfg.G.m + 10) := by
  intro st ω ⟨hst, hptrs⟩
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
  have hlt_pow : ∀ x, x ≤ workAddr + (12 * n + m + 2 * H + 2) → x < 2 ^ w := fun x hx => by omega
  have hdisj_g_work := hdisj.2.2.2.1
  have hdisj_outR_work := hdisj.2.2.2.2.2.2
  let eCond : Expr := .bin .lt (.reg prI) (.reg prM)
  have heSize : eCond.size = 3 := rfl
  let Inv : ℕ → State → Prop := fun k st =>
    k ≤ m ∧ st.regs prI = k ∧
    (∀ r, r ≠ prI → r ≠ prIdx → r ≠ prU → r ≠ prW → r ≠ prTmp1 → r ≠ prTmp2 → r ≠ prTmp3 →
      st.regs r = st₀.regs r) ∧
    st.pos = st₀.pos ∧
    MemFrame st₀.mem st.mem workAddr (wInAct workAddr n m H) ∧
    (∀ addr, wHArr workAddr n m H ≤ addr → addr < wEx workAddr n m H → st.mem addr = st₀.mem addr) ∧
    (∀ u < n, st.mem (wDegX workAddr n m H + u) = degXPrefix cfg.G k u) ∧
    (∀ u < n, st.mem (wDegR workAddr n m H + u) = degRPrefix cfg.G inR k u) ∧
    (∀ u < n, st.mem (wEx workAddr n m H + u) = exPrefix cfg.G inR cfg.C_cap k u)
  have hloop : Triple w p (Inv 0)
      (.loop eCond
        (seqStmts [
          .assign prIdx (.bin .add (.bin .add (.reg prG) (.const 2)) (.bin .mul (.const 2) (.reg prI))),
          .assign prU (.load (.reg prIdx)),
          .assign prW (.load (.bin .add (.reg prIdx) (.const 1))),
          .assign prTmp3 (.bin .add (.reg prDegX) (.reg prU)),
          .store (.reg prTmp3) (.bin .add (.load (.reg prTmp3)) (.const 1)),
          .assign prTmp3 (.bin .add (.reg prDegX) (.reg prW)),
          .store (.reg prTmp3) (.bin .add (.load (.reg prTmp3)) (.const 1)),
          .assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prU))),
          .assign prTmp2 (.load (.bin .add (.reg prOutR) (.reg prW))),
          initScanOneEdgeCondStmt,
          .assign prI (.bin .add (.reg prI) (.const 1))
        ]))
      (normalPost fun st => Inv m st)
      (fun _ => 115 * m + 4) := by
    apply (Triple.loop_inv (α := ℕ)
      (m := fun k => m - k) (rem := fun k => 115 * (m - k) + 4)
      (condVal := fun st => if st.regs prI < st.regs prM then 1 else 0)
      (Inv := Inv) ?_ ?_ ?_ 0).mono_cost (fun _ _ => le_rfl)
    · rintro k st ⟨_, _, hr, _, _, _, _, _, _⟩
      have hrm : st.regs prM = m := (hr prM (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_m
      simp only [eCond, Expr.eval, hrm, WordRAM.BinOp.eval]
      by_cases hcmp : st.regs prI < m <;> simp [hcmp, h1lt, h0lt]
    · rintro k st hInv heq
      rcases hInv with ⟨hk, hri, hr, hp, hmf, hmid, hdx, hdr, hex⟩
      have hrm : st.regs prM = m := (hr prM (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_m
      have hkEq : k = m := by
        by_contra hne
        have hlt : k < m := by omega
        rw [hri, hrm] at heq; simp [hlt] at heq
      subst hkEq
      exact ⟨⟨le_rfl, hri, hr, hp, hmf, hmid, hdx, hdr, hex⟩, by simp [eCond, Expr.size]⟩
    · rintro k st ⟨hk, hri, hr, hp, hmf, hmid, hdx, hdr, hex⟩ hne
      have hrm : st.regs prM = m := (hr prM (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_m
      have hk_lt : k < m := by
        by_contra hge
        rw [hri, hrm] at hne; simp [hge] at hne
      have hk_len : k < cfg.G.edges.length := hk_lt
      set e := cfg.G.edges[k]'hk_len
      set a := e.1
      set b := e.2
      have h12 : a < n ∧ b < n := hval e (List.getElem_mem hk_len)
      have haN : a < n := h12.1
      have hbN : b < n := h12.2
      have ha_lt : a < 2 ^ w := by omega
      have hb_lt : b < 2 ^ w := by omega
      have hrG : st.regs prG = gAddr := (hr prG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_g
      have hrOutR : st.regs prOutR = outRAddr := (hr prOutR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_outR
      have hrDX : st.regs prDegX = wDegX workAddr n m H := (hr prDegX (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_degX
      have hg2 : gAddr + 2 < 2 ^ w := by omega
      have h2k : 2 * k < 2 ^ w := by omega
      have hidx : gAddr + 2 + 2 * k < 2 ^ w := by omega
      have hidx1 : gAddr + 2 + 2 * k + 1 < 2 ^ w := by omega
      have houtRa : outRAddr + a < 2 ^ w := by omega
      have houtRb : outRAddr + b < 2 ^ w := by omega
      have hdx_a_lt : wDegX workAddr n m H + a < 2 ^ w := hlt_pow _ (by dsimp [wDegX]; omega)
      have hdx_b_lt : wDegX workAddr n m H + b < 2 ^ w := hlt_pow _ (by dsimp [wDegX]; omega)
      have hk1 : k + 1 < 2 ^ w := by omega
      have hdx_a_val : degXPrefix cfg.G k a + 1 < 2 ^ w := by
        have := degXPrefix_le_two_mul_m (G := cfg.G) k a; dsimp [m] at *; omega
      have hdx_a_self : degXPrefix cfg.G k a + 1 + 1 < 2 ^ w := by
        have := degXPrefix_le_two_mul_m (G := cfg.G) k a; dsimp [m] at *; omega
      have hdx_b_val : degXPrefix cfg.G k b + 1 < 2 ^ w := by
        have := degXPrefix_le_two_mul_m (G := cfg.G) k b; dsimp [m] at *; omega
      have hfst_orig : st₀.mem (gAddr + 2 + 2 * k) = a := graphAt_edge_fst hG hk_lt
      have hsnd_orig : st₀.mem (gAddr + 2 + 2 * k + 1) = b := by
        rw [show gAddr + 2 + 2 * k + 1 = gAddr + 3 + 2 * k by omega]
        exact graphAt_edge_snd hG hk_lt
      have hfst : st.mem (gAddr + 2 + 2 * k) = a := by
        rw [hmf (gAddr + 2 + 2 * k) (by
          dsimp [wInAct]
          unfold pruneWorkSpace at hdisj_g_work
          rcases hdisj_g_work with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])]
        exact hfst_orig
      have hsnd : st.mem (gAddr + 2 + 2 * k + 1) = b := by
        rw [hmf (gAddr + 2 + 2 * k + 1) (by
          dsimp [wInAct]
          unfold pruneWorkSpace at hdisj_g_work
          rcases hdisj_g_work with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])]
        exact hsnd_orig
      have hout_disj : ∀ x, workAddr ≤ x → x < wInAct workAddr n m H → ∀ y < n, x ≠ outRAddr + y := by
        intro x hx1 hx2 y hy heq
        dsimp [wInAct] at hx2
        unfold pruneWorkSpace at hdisj_outR_work
        rcases hdisj_outR_work with h | h <;> omega
      refine ⟨110, ?_⟩
      intro st1 ω2 hst1
      subst st1
      have hbody : ∃ o st' c1,
          Runs w p ω2
            (seqStmts [
              .assign prIdx (.bin .add (.bin .add (.reg prG) (.const 2)) (.bin .mul (.const 2) (.reg prI))),
              .assign prU (.load (.reg prIdx)),
              .assign prW (.load (.bin .add (.reg prIdx) (.const 1))),
              .assign prTmp3 (.bin .add (.reg prDegX) (.reg prU)),
              .store (.reg prTmp3) (.bin .add (.load (.reg prTmp3)) (.const 1)),
              .assign prTmp3 (.bin .add (.reg prDegX) (.reg prW)),
              .store (.reg prTmp3) (.bin .add (.load (.reg prTmp3)) (.const 1)),
              .assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prU))),
              .assign prTmp2 (.load (.bin .add (.reg prOutR) (.reg prW))),
              initScanOneEdgeCondStmt,
              .assign prI (.bin .add (.reg prI) (.const 1))
            ]) st o st' c1 ∧
          normalPost (fun st' => Inv (k + 1) st') o st' ∧ c1 ≤ 110 := by
        dsimp only [seqStmts]
        refine runs_start_le (T := 110) ?_
        apply runs_seq_assign_le (v := gAddr + 2 + 2 * k)
        · simp only [Expr.eval, hrG, hri, h2lt, WordRAM.BinOp.eval, hg2, h2k, hidx, ↓reduceIte]
        apply runs_seq_assign_le (v := a)
        · simp only [Expr.eval, Function.update_self, Option.map_some, hfst]
        apply runs_seq_assign_le (v := b)
        · simp only [Expr.eval, Function.update_of_ne (by decide : prIdx ≠ prU),
            Function.update_self, h1lt, WordRAM.BinOp.eval, hidx1, ↓reduceIte, Option.map_some, hsnd]
        apply runs_seq_assign_le (v := wDegX workAddr n m H + a)
        · exact eval_add_regs (by simp; exact hrDX) (by simp) hdx_a_lt
        apply runs_seq_store_le (x := wDegX workAddr n m H + a) (v := degXPrefix cfg.G k a + 1)
        · simp [Expr.eval]
        · simp only [Expr.eval, Function.update_self, Option.map_some, hdx a haN, h1lt,
            WordRAM.BinOp.eval, hdx_a_val, ↓reduceIte]
        apply runs_seq_assign_le (v := wDegX workAddr n m H + b)
        · exact eval_add_regs (by simp; exact hrDX) (by simp) hdx_b_lt
        apply runs_seq_store_le (x := wDegX workAddr n m H + b)
            (v := (if b = a then degXPrefix cfg.G k a + 1 else degXPrefix cfg.G k b) + 1)
        · simp [Expr.eval]
        · by_cases hba : b = a
          · rw [hba]
            simp only [Expr.eval, Function.update_self, Option.map_some, h1lt,
              WordRAM.BinOp.eval, hdx_a_self, ↓reduceIte]
          · simp only [Expr.eval, Function.update_self, Option.map_some,
              Function.update_of_ne (by omega : wDegX workAddr n m H + b ≠ wDegX workAddr n m H + a),
              hdx b hbN, h1lt, WordRAM.BinOp.eval, hdx_b_val, ↓reduceIte, hba]
        -- mem after degX updates
        set mem1 := Function.update
          (Function.update st.mem (wDegX workAddr n m H + a) (degXPrefix cfg.G k a + 1))
          (wDegX workAddr n m H + b)
          ((if b = a then degXPrefix cfg.G k a + 1 else degXPrefix cfg.G k b) + 1)
        have hm1_outR : ∀ y < n, mem1 (outRAddr + y) = if inR y then 1 else 0 := by
          intro y hy
          dsimp only [mem1]
          rw [Function.update_of_ne (hout_disj _ (by dsimp [wDegX]; omega) (by dsimp [wDegX, wInAct]; omega) y hy).symm,
              Function.update_of_ne (hout_disj _ (by dsimp [wDegX]; omega) (by dsimp [wDegX, wInAct]; omega) y hy).symm,
              hmf (outRAddr + y) (by
                unfold pruneWorkSpace at hdisj_outR_work
                dsimp [wInAct]; rcases hdisj_outR_work with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]),
              houtR y hy]
        have hm1_dr : ∀ u < n, mem1 (wDegR workAddr n m H + u) = degRPrefix cfg.G inR k u := by
          intro u hu
          dsimp only [mem1]
          rw [Function.update_of_ne (by dsimp [wDegR, wDegX]; omega),
              Function.update_of_ne (by dsimp [wDegR, wDegX]; omega)]
          exact hdr u hu
        have hm1_ex : ∀ u < n, mem1 (wEx workAddr n m H + u) = exPrefix cfg.G inR cfg.C_cap k u := by
          intro u hu
          dsimp only [mem1]
          rw [Function.update_of_ne (by dsimp [wEx, wDegX]; omega),
              Function.update_of_ne (by dsimp [wEx, wDegX]; omega)]
          exact hex u hu
        apply runs_seq_assign_le (v := if inR a then 1 else 0)
        · exact eval_load_add_regs (by simp; exact hrOutR) (by simp) houtRa (hm1_outR a haN) (by split_ifs <;> omega)
        apply runs_seq_assign_le (v := if inR b then 1 else 0)
        · exact eval_load_add_regs (by simp; exact hrOutR) (by simp) houtRb (hm1_outR b hbN) (by split_ifs <;> omega)
        -- Now run initScanOneEdgeCondStmt via initScanOneEdgeCond_triple
        have hk_e : cfg.G.edges[k]'hk_len = (a, b) := rfl
        have hr_dr_c : st.regs prDegR = wDegR workAddr n m H :=
          (hr prDegR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_degR
        have hr_ex_c : st.regs prEx = wEx workAddr n m H :=
          (hr prEx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_ex
        have hr_cc_c : st.regs prCcap = cfg.C_cap :=
          (hr prCcap (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_ccap
        apply runs_seq_triple_le (initScanOneEdgeCond_triple _ inR hw hk_len hk_e haN hbN)
        · refine ⟨rfl, by simpa using hr_dr_c, by simpa using hr_ex_c, by simpa using hr_cc_c,
            by simp, by simp, by simp, by simp, hm1_dr, hm1_ex⟩
        intro st2 ⟨hr2, hp2, hmf2, hdr2, hex2⟩
        apply runs_assign_le (v := k + 1)
        · simp only [Expr.eval, hr2 prI (by decide), Function.update_of_ne (by decide : prI ≠ prTmp2),
            Function.update_of_ne (by decide : prI ≠ prTmp1),
            Function.update_of_ne (by decide : prI ≠ prTmp3),
            Function.update_of_ne (by decide : prI ≠ prW),
            Function.update_of_ne (by decide : prI ≠ prU),
            Function.update_of_ne (by decide : prI ≠ prIdx), hri, h1lt,
            WordRAM.BinOp.eval, hk1, ↓reduceIte]
        · refine ⟨hk_lt, by simp, fun r h1 h2 h3 h4 h5 h6 h7 => ?_, by simpa using hp2.trans hp, ?_, ?_, ?_, hdr2, hex2⟩
          · dsimp only
            rw [Function.update_of_ne h1, hr2 r h7]
            simp only [Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h4,
              Function.update_of_ne h5, Function.update_of_ne h6, Function.update_of_ne h7]
            exact hr r h1 h2 h3 h4 h5 h6 h7
          · refine memFrame_trans hmf (memFrame_trans ?_ (init_memFrame_weaken hmf2 (by dsimp [wEx]; omega) le_rfl))
            exact memFrame_trans
              (memFrame_update_in (by dsimp [wDegX]; omega) (by dsimp [wDegX, wInAct]; omega))
              (memFrame_update_in (by dsimp [wDegX]; omega) (by dsimp [wDegX, wInAct]; omega))
          · intro addr ha1 ha2
            rw [hmf2 addr (Or.inl ha2)]
            dsimp only [mem1]
            rw [Function.update_of_ne (by dsimp [wDegX, wHArr] at ha1 ⊢; omega),
                Function.update_of_ne (by dsimp [wDegX, wHArr] at ha1 ⊢; omega)]
            exact hmid addr ha1 ha2
          · intro u hu
            rw [hmf2 (wDegX workAddr n m H + u) (Or.inl (by dsimp [wDegX, wEx]; omega))]
            have hstep := degXPrefix_succ cfg.G hk_len u
            change degXPrefix cfg.G (k + 1) u = degXPrefix cfg.G k u + (if a = u then 1 else 0) + (if b = u then 1 else 0) at hstep
            rw [hstep]
            dsimp only [mem1]
            by_cases hub : u = b <;> by_cases hua : u = a
            · have hab : b = a := hub.symm.trans hua
              rw [hub, hab]; simp [Function.update_self]
            · rw [hub]
              have hne : b ≠ a := by omega
              simp [Function.update_self, hne, Ne.symm hne]
            · rw [hua]
              have hne : a ≠ b := by omega
              rw [Function.update_of_ne (by omega), Function.update_self]
              simp [Ne.symm hne]
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hdx u hu]
              simp [Ne.symm hua, Ne.symm hub]
        · simp only [Expr.size]; omega
      obtain ⟨o, st_next, c_b, hrun_b, hpost_b, hc_b⟩ := hbody
      cases o with
      | returned _ => exact absurd hpost_b (by simp [normalPost])
      | normal =>
          exact ⟨.normal, st_next, c_b, hrun_b, ⟨k + 1, hpost_b, by omega, by omega⟩, hc_b⟩
  refine runs_start_le ?_
  dsimp only [initScanEdgesStmt, seqStmts]
  apply runs_seq_assign_le (v := 0)
  · simp [Expr.eval, h0lt]
  apply runs_triple_le hloop
  · refine ⟨Nat.zero_le _, by simp,
      fun r h1 _ _ _ _ _ _ => by simp [Function.update_of_ne h1],
      rfl, fun _ _ => rfl, fun _ _ _ => rfl,
      fun u hu => by rw [degXPrefix_zero, hdx0 u hu],
      fun u hu => by rw [degRPrefix_zero, hdr0 u hu],
      fun u hu => by rw [exPrefix_zero, hex0 u hu]⟩
  · intro o st1 h1
    cases o with
    | returned _ => exact absurd h1 (by simp [normalPost])
    | normal =>
        rcases h1 with ⟨_, _, hr1, hp1, hmf1, hmid1, hdx1, hdr1, hex1⟩
        exact ⟨{
    reg_g := (hr1 prG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_g
    reg_csr := (hr1 prCsr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_csr
    reg_inB := (hr1 prInB (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_inB
    reg_outR := (hr1 prOutR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_outR
    reg_work := (hr1 prWork (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_work
    reg_ccap := (hr1 prCcap (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_ccap
    reg_H := (hr1 prH (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_H
    reg_theta := (hr1 prTheta (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_theta
    reg_n := (hr1 prN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_n
    reg_m := (hr1 prM (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_m
    reg_actTop := (hr1 prActTop (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_actTop
    reg_peelTop := (hr1 prPeelTop (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_peelTop
    reg_degX := (hr1 prDegX (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_degX
    reg_hArr := (hr1 prHArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_hArr
    reg_cur := (hr1 prCur (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_cur
    reg_abs := (hr1 prAbs (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_abs
    reg_ex := (hr1 prEx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_ex
    reg_degR := (hr1 prDegR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_degR
    reg_inAct := (hr1 prInAct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_inAct
    reg_actStk := (hr1 prActStk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_actStk
    reg_peelStk := (hr1 prPeelStk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_peelStk
    reg_lvlNext := (hr1 prLvlNext (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_lvlNext
    reg_lvlPrev := (hr1 prLvlPrev (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_lvlPrev
    reg_remArr := (hr1 prRemArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_remArr
    reg_flowEnc := (hr1 prFlowEnc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_flowEnc
    reg_lvlVol := (hr1 prLvlVol (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_lvlVol
    reg_lvlHead := (hr1 prLvlHead (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_lvlHead
    reg_adjV := (hr1 prCsrAdjV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_adjV
    reg_adjH := (hr1 prCsrAdjH (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hptrs.reg_adjH },
    hp1, hmf1, hmid1, hdx1, hdr1, hex1⟩
  · simp only [Expr.size]; omega

lemma initQueueOneVert_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {workAddr k : ℕ}
    (st₀ : State) (inR : ℕ → Bool) (ex degR : ℕ → ℕ)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hk : k < cfg.G.n) :
    let n := cfg.G.n
    let m := cfg.G.m
    let H := cfg.H
    let actP : ℕ → Bool := fun u => inR u && decide (0 < ex u)
    let peelP : ℕ → Bool := fun u => inR u && decide (degR u < cfg.θ_out_nat)
    let actL := (List.range k).filter actP
    let peelL := (List.range k).filter peelP
    Triple w p
      (fun st => st = st₀ ∧
        st.regs prU = k ∧
        st.regs prTmp1 = (if inR k then 1 else 0) ∧
        st.regs prEx = wEx workAddr n m H ∧
        st.regs prDegR = wDegR workAddr n m H ∧
        st.regs prInAct = wInAct workAddr n m H ∧
        st.regs prActStk = wActStk workAddr n m H ∧
        st.regs prPeelStk = wPeelStk workAddr n m H ∧
        st.regs prActTop = actL.length ∧
        st.regs prPeelTop = peelL.length ∧
        st.regs prTheta = cfg.θ_out_nat ∧
        actL.length ≤ k ∧ peelL.length ≤ k ∧
        st.mem (wEx workAddr n m H + k) = ex k ∧
        st.mem (wDegR workAddr n m H + k) = degR k ∧
        ex k < 2 ^ w ∧ degR k < 2 ^ w ∧
        (∀ u < n, st.mem (wInAct workAddr n m H + u) =
          if decide (u < k) && actP u then 1 else 0) ∧
        (∀ i < actL.length, st.mem (wActStk workAddr n m H + i) = actL.getD i 0) ∧
        (∀ i < peelL.length, st.mem (wPeelStk workAddr n m H + i) = peelL.getD i 0))
      initQueueOneVertStmt
      (normalPost fun st' =>
        (∀ r, r ≠ prTmp2 → r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
        st'.regs prActTop = ((List.range (k + 1)).filter actP).length ∧
        st'.regs prPeelTop = ((List.range (k + 1)).filter peelP).length ∧
        st'.pos = st₀.pos ∧
        MemFrame st₀.mem st'.mem (wInAct workAddr n m H) (wLvlNext workAddr n m H) ∧
        (∀ u < n, st'.mem (wInAct workAddr n m H + u) =
          if decide (u < k + 1) && actP u then 1 else 0) ∧
        (∀ i < ((List.range (k + 1)).filter actP).length,
          st'.mem (wActStk workAddr n m H + i) = ((List.range (k + 1)).filter actP).getD i 0) ∧
        (∀ i < ((List.range (k + 1)).filter peelP).length,
          st'.mem (wPeelStk workAddr n m H + i) = ((List.range (k + 1)).filter peelP).getD i 0))
      (fun _ => 58) := by
  intro n m H actP peelP actL peelL st ω
    ⟨hst, hru, hr1, hrEX, hrDR, hrIA, hrAS, hrPS, hrAT, hrPT, hrTh,
      hactLen, hpeelLen, hmEX, hmDR, hex_lt, hdr_lt, hmIA, hmAS, hmPS⟩
  subst st
  have hwb := hw
  unfold PruneWordBound pruneWorkSpace at hwb
  have h0lt : 0 < 2 ^ w := by omega
  have h1lt : 1 < 2 ^ w := by omega
  have hlt_pow : ∀ x, x ≤ workAddr + (12 * n + m + 2 * H + 2) → x < 2 ^ w := fun x hx => by omega
  have hk_lt : k < 2 ^ w := by omega
  have hex_addr_lt : wEx workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wEx]; omega)
  have hdr_addr_lt : wDegR workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wDegR]; omega)
  have hia_addr_lt : wInAct workAddr n m H + k < 2 ^ w := hlt_pow _ (by dsimp [wInAct]; omega)
  have has_addr_lt : wActStk workAddr n m H + actL.length < 2 ^ w :=
    hlt_pow _ (by dsimp [wActStk]; omega)
  have hps_addr_lt : wPeelStk workAddr n m H + peelL.length < 2 ^ w :=
    hlt_pow _ (by dsimp [wPeelStk]; omega)
  have hat1_lt : actL.length + 1 < 2 ^ w := by omega
  have hpt1_lt : peelL.length + 1 < 2 ^ w := by omega
  have hthen_body : Triple w p (fun st => st = st₀ ∧ inR k = true)
      (seqStmts [
        .assign prTmp2 (.load (.bin .add (.reg prEx) (.reg prU))),
        .cond (.bin .lt (.const 0) (.reg prTmp2))
          (seqStmts [
            .store (.bin .add (.reg prInAct) (.reg prU)) (.const 1),
            .store (.bin .add (.reg prActStk) (.reg prActTop)) (.reg prU),
            .assign prActTop (.bin .add (.reg prActTop) (.const 1))
          ])
          .nop,
        .assign prTmp2 (.load (.bin .add (.reg prDegR) (.reg prU))),
        .cond (.bin .lt (.reg prTmp2) (.reg prTheta))
          (seqStmts [
            .store (.bin .add (.reg prPeelStk) (.reg prPeelTop)) (.reg prU),
            .assign prPeelTop (.bin .add (.reg prPeelTop) (.const 1))
          ])
          .nop
      ])
      (normalPost fun st' =>
        (∀ r, r ≠ prTmp2 → r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
        st'.regs prActTop = ((List.range (k + 1)).filter actP).length ∧
        st'.regs prPeelTop = ((List.range (k + 1)).filter peelP).length ∧
        st'.pos = st₀.pos ∧
        MemFrame st₀.mem st'.mem (wInAct workAddr n m H) (wLvlNext workAddr n m H) ∧
        (∀ u < n, st'.mem (wInAct workAddr n m H + u) =
          if decide (u < k + 1) && actP u then 1 else 0) ∧
        (∀ i < ((List.range (k + 1)).filter actP).length,
          st'.mem (wActStk workAddr n m H + i) = ((List.range (k + 1)).filter actP).getD i 0) ∧
        (∀ i < ((List.range (k + 1)).filter peelP).length,
          st'.mem (wPeelStk workAddr n m H + i) = ((List.range (k + 1)).filter peelP).getD i 0))
      (fun _ => 50) := by
    intro st ω' ⟨hst', hink⟩
    subst st
    have hact_cond : Triple w p
        (fun st => st = { st₀ with regs := Function.update st₀.regs prTmp2 (ex k) })
        (.cond (.bin .lt (.const 0) (.reg prTmp2))
          (seqStmts [
            .store (.bin .add (.reg prInAct) (.reg prU)) (.const 1),
            .store (.bin .add (.reg prActStk) (.reg prActTop)) (.reg prU),
            .assign prActTop (.bin .add (.reg prActTop) (.const 1))
          ])
          .nop)
        (normalPost fun st' =>
          (∀ r, r ≠ prTmp2 → r ≠ prActTop → st'.regs r = st₀.regs r) ∧
          st'.regs prActTop = ((List.range (k + 1)).filter actP).length ∧
          st'.pos = st₀.pos ∧
          MemFrame st₀.mem st'.mem (wInAct workAddr n m H) (wPeelStk workAddr n m H) ∧
          (∀ u < n, st'.mem (wInAct workAddr n m H + u) =
            if decide (u < k + 1) && actP u then 1 else 0) ∧
          (∀ i < ((List.range (k + 1)).filter actP).length,
            st'.mem (wActStk workAddr n m H + i) = ((List.range (k + 1)).filter actP).getD i 0))
        (fun _ => 20) := by
      apply (Triple.cond_const
        (val := fun st => if 0 < st.regs prTmp2 then 1 else 0) (c_t := 16) (c_f := 1)
        (fun st hs => by
          subst st; simp only [Expr.eval, Function.update_self, h0lt, WordRAM.BinOp.eval]
          by_cases hcmp : 0 < ex k <;> simp [hcmp, h1lt, h0lt])
        ?_ ?_).mono_cost (fun _ _ => by simp [Expr.size])
      · intro st ω2 ⟨hs, hne⟩
        subst st
        have hexk : 0 < ex k := by
          by_contra h'
          simp only [Function.update_self] at hne; simp [h'] at hne
        have hactk : actP k = true := by simp [actP, hink, hexk]
        have hsucc : (List.range (k + 1)).filter actP = actL ++ [k] := by
          rw [filter_range_succ]; simp [hactk, actL]
        refine runs_start_le (T := 16) ?_
        dsimp only [seqStmts]
        apply runs_seq_store_le (x := wInAct workAddr n m H + k) (v := 1)
        · exact eval_add_regs (by simp [hrIA]) (by simp [hru]) hia_addr_lt
        · simp [Expr.eval, h1lt]
        apply runs_seq_store_le (x := wActStk workAddr n m H + actL.length) (v := k)
        · exact eval_add_regs (by simp [hrAS]) (by simp [hrAT]) has_addr_lt
        · exact eval_reg (by simp [hru]) hk_lt
        apply runs_assign_le (v := actL.length + 1)
        · simp only [Expr.eval, Function.update_of_ne (by decide : prActTop ≠ prTmp2), hrAT,
            h1lt, WordRAM.BinOp.eval, hat1_lt, ↓reduceIte]
        · refine ⟨fun r h1 h2 => by simp [Function.update_of_ne h1, Function.update_of_ne h2],
            by rw [hsucc, List.length_append, List.length_singleton]; simp,
            rfl, ?_, ?_, ?_⟩
          · exact memFrame_trans
              (memFrame_update_in (by dsimp [wInAct]; omega) (by dsimp [wInAct, wPeelStk]; omega))
              (memFrame_update_in (by dsimp [wInAct, wActStk]; omega) (by dsimp [wActStk, wPeelStk]; omega))
          · intro u hu
            dsimp only
            rw [Function.update_of_ne (by dsimp [wActStk, wInAct]; omega)]
            by_cases huk : u = k
            · subst huk; simp [Function.update_self, hactk]
            · rw [Function.update_of_ne (by omega), hmIA u hu]
              by_cases hu_lt : u < k
              · have hu1 : u < k + 1 := by omega
                simp [hu_lt, hu1]
              · have hnot1 : ¬(u < k + 1) := by omega
                simp [hu_lt, hnot1]
          · intro i hi
            rw [hsucc, List.length_append, List.length_singleton] at hi
            rw [hsucc]
            dsimp only
            by_cases hil : i = actL.length
            · subst hil; simp [Function.update_self, List.getD_eq_getElem?_getD]
            · have hiLt : i < actL.length := by omega
              rw [Function.update_of_ne (by omega),
                  Function.update_of_ne (by dsimp [wActStk, wInAct]; omega), hmAS i hiLt]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hiLt]
        · simp only [Expr.size]; omega
      · apply Triple.nop
        intro st ⟨hs, heq⟩
        subst st
        have hnz : ex k = 0 := by
          by_contra h'
          have hpos : 0 < ex k := Nat.pos_of_ne_zero h'
          simp only [Function.update_self, hpos, ↓reduceIte] at heq
          exact Nat.one_ne_zero heq
        have hactk : actP k = false := by simp [actP, hnz]
        have hsucc : (List.range (k + 1)).filter actP = actL := by
          rw [filter_range_succ]; simp [hactk, actL]
        refine ⟨fun r h1 _ => Function.update_of_ne h1 _ _,
          by simp [hsucc, hrAT],
          rfl, fun _ _ => rfl, ?_, ?_⟩
        · intro u hu
          rw [hmIA u hu]
          by_cases huk : u = k
          · subst huk; simp [hactk]
          · have hlt_eq : u < k + 1 ↔ u < k := by omega
            simp [hlt_eq]
        · intro i hi
          rw [hsucc] at hi ⊢; exact hmAS i hi
    refine runs_start_le ?_
    dsimp only [seqStmts]
    apply runs_seq_assign_le (v := ex k)
    · exact eval_load_add_regs hrEX hru hex_addr_lt hmEX hex_lt
    apply runs_seq_triple_le hact_cond
    · rfl
    intro st1 ⟨hr_1, hAT1, hp1, hmf1, hmIA1, hmAS1⟩
    have hr1_DR : st1.regs prDegR = wDegR workAddr n m H := (hr_1 prDegR (by decide) (by decide)).trans hrDR
    have hr1_U : st1.regs prU = k := (hr_1 prU (by decide) (by decide)).trans hru
    have hm1_DR : st1.mem (wDegR workAddr n m H + k) = degR k := by
      rw [hmf1 (wDegR workAddr n m H + k) (Or.inl (by dsimp [wDegR, wInAct]; omega))]
      exact hmDR
    have hpeel_cond : Triple w p
        (fun st => st = { st1 with regs := Function.update st1.regs prTmp2 (degR k) })
        (.cond (.bin .lt (.reg prTmp2) (.reg prTheta))
          (seqStmts [
            .store (.bin .add (.reg prPeelStk) (.reg prPeelTop)) (.reg prU),
            .assign prPeelTop (.bin .add (.reg prPeelTop) (.const 1))
          ])
          .nop)
        (normalPost fun st' =>
          (∀ r, r ≠ prTmp2 → r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
          st'.regs prActTop = ((List.range (k + 1)).filter actP).length ∧
          st'.regs prPeelTop = ((List.range (k + 1)).filter peelP).length ∧
          st'.pos = st₀.pos ∧
          MemFrame st₀.mem st'.mem (wInAct workAddr n m H) (wLvlNext workAddr n m H) ∧
          (∀ u < n, st'.mem (wInAct workAddr n m H + u) =
            if decide (u < k + 1) && actP u then 1 else 0) ∧
          (∀ i < ((List.range (k + 1)).filter actP).length,
            st'.mem (wActStk workAddr n m H + i) = ((List.range (k + 1)).filter actP).getD i 0) ∧
          (∀ i < ((List.range (k + 1)).filter peelP).length,
            st'.mem (wPeelStk workAddr n m H + i) = ((List.range (k + 1)).filter peelP).getD i 0))
        (fun _ => 16) := by
      apply (Triple.cond_const
        (val := fun st => if st.regs prTmp2 < cfg.θ_out_nat then 1 else 0) (c_t := 12) (c_f := 1)
        (fun st hs => by
          subst st
          have hrTh1 : st1.regs prTheta = cfg.θ_out_nat := (hr_1 prTheta (by decide) (by decide)).trans hrTh
          simp only [Expr.eval, Function.update_self, Function.update_of_ne (by decide : prTheta ≠ prTmp2),
            hrTh1, WordRAM.BinOp.eval]
          by_cases hcmp : degR k < cfg.θ_out_nat <;> simp [hcmp, h1lt, h0lt])
        ?_ ?_).mono_cost (fun _ _ => by simp [Expr.size])
      · intro st ω2 ⟨hs, hne⟩
        subst st
        have hlt_th : degR k < cfg.θ_out_nat := by
          by_contra h'
          simp only [Function.update_self] at hne; simp [h'] at hne
        have hpeelk : peelP k = true := by simp [peelP, hink, hlt_th]
        have hsucc : (List.range (k + 1)).filter peelP = peelL ++ [k] := by
          rw [filter_range_succ]; simp [hpeelk, peelL]
        have hr1_PS : st1.regs prPeelStk = wPeelStk workAddr n m H :=
          (hr_1 prPeelStk (by decide) (by decide)).trans hrPS
        have hr1_PT : st1.regs prPeelTop = peelL.length :=
          (hr_1 prPeelTop (by decide) (by decide)).trans hrPT
        refine runs_start_le (T := 12) ?_
        dsimp only [seqStmts]
        apply runs_seq_store_le (x := wPeelStk workAddr n m H + peelL.length) (v := k)
        · exact eval_add_regs (by simp [hr1_PS]) (by simp [hr1_PT]) hps_addr_lt
        · exact eval_reg (by simp [hr1_U]) hk_lt
        apply runs_assign_le (v := peelL.length + 1)
        · simp only [Expr.eval, Function.update_of_ne (by decide : prPeelTop ≠ prTmp2), hr1_PT,
            h1lt, WordRAM.BinOp.eval, hpt1_lt, ↓reduceIte]
        · refine ⟨fun r h1 h2 h3 => by simp [Function.update_of_ne h3, Function.update_of_ne h1, hr_1 r h1 h2],
            by simp [hAT1],
            by rw [hsucc, List.length_append, List.length_singleton]; simp,
            hp1, ?_, ?_, ?_, ?_⟩
          · dsimp only
            exact init_memFrame_weaken hmf1 le_rfl (by dsimp [wPeelStk, wLvlNext]; omega)
              |> fun h => memFrame_trans h
                (memFrame_update_in (by dsimp [wInAct, wPeelStk]; omega) (by dsimp [wPeelStk, wLvlNext]; omega))
          · intro u hu
            dsimp only
            rw [Function.update_of_ne (by dsimp [wInAct, wPeelStk]; omega)]
            exact hmIA1 u hu
          · intro i hi
            dsimp only
            have hi_n : i < n := by
              have hlen := List.length_filter_le actP (List.range (k + 1))
              rw [List.length_range] at hlen; omega
            rw [Function.update_of_ne (by dsimp [wActStk, wPeelStk]; omega)]
            exact hmAS1 i hi
          · intro i hi
            rw [hsucc, List.length_append, List.length_singleton] at hi
            rw [hsucc]
            dsimp only
            by_cases hil : i = peelL.length
            · subst hil; simp [Function.update_self, List.getD_eq_getElem?_getD]
            · have hiLt : i < peelL.length := by omega
              rw [Function.update_of_ne (by omega),
                  hmf1 (wPeelStk workAddr n m H + i) (Or.inr (by dsimp [wPeelStk]; omega)),
                  hmPS i hiLt]
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hiLt]
        · simp only [Expr.size]; omega
      · apply Triple.nop
        intro st ⟨hs, heq⟩
        subst st
        have hge : ¬(degR k < cfg.θ_out_nat) := by
          intro hlt
          simp only [Function.update_self, hlt, ↓reduceIte] at heq
          exact Nat.one_ne_zero heq
        have hpeelk : peelP k = false := by simp [peelP, hge]
        have hsucc : (List.range (k + 1)).filter peelP = peelL := by
          rw [filter_range_succ]; simp [hpeelk, peelL]
        have hr1_PT : st1.regs prPeelTop = peelL.length :=
          (hr_1 prPeelTop (by decide) (by decide)).trans hrPT
        refine ⟨fun r h1 h2 _ => by simp [Function.update_of_ne h1, hr_1 r h1 h2],
          by simp [hAT1],
          by simp [hsucc, hr1_PT],
          hp1, init_memFrame_weaken hmf1 le_rfl (by dsimp [wPeelStk, wLvlNext]; omega), hmIA1, hmAS1,
          fun i hi => by
            rw [hsucc] at hi ⊢
            rw [hmf1 (wPeelStk workAddr n m H + i) (Or.inr (by dsimp [wPeelStk]; omega))]
            exact hmPS i hi⟩
    apply runs_seq_assign_le (v := degR k)
    · exact eval_load_add_regs hr1_DR hr1_U hdr_addr_lt hm1_DR hdr_lt
    apply runs_triple_le hpeel_cond
    · rfl
    · exact fun _ _ h => h
    · simp only [Expr.size]; omega
  have helse_body : Triple w p (fun st => st = st₀ ∧ inR k = false)
      .nop
      (normalPost fun st' =>
        (∀ r, r ≠ prTmp2 → r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
        st'.regs prActTop = ((List.range (k + 1)).filter actP).length ∧
        st'.regs prPeelTop = ((List.range (k + 1)).filter peelP).length ∧
        st'.pos = st₀.pos ∧
        MemFrame st₀.mem st'.mem (wInAct workAddr n m H) (wLvlNext workAddr n m H) ∧
        (∀ u < n, st'.mem (wInAct workAddr n m H + u) =
          if decide (u < k + 1) && actP u then 1 else 0) ∧
        (∀ i < ((List.range (k + 1)).filter actP).length,
          st'.mem (wActStk workAddr n m H + i) = ((List.range (k + 1)).filter actP).getD i 0) ∧
        (∀ i < ((List.range (k + 1)).filter peelP).length,
          st'.mem (wPeelStk workAddr n m H + i) = ((List.range (k + 1)).filter peelP).getD i 0))
      (fun _ => 1) := by
    apply Triple.nop
    intro st ⟨hst', hnk⟩
    subst st
    have hactk : actP k = false := by simp [actP, hnk]
    have hpeelk : peelP k = false := by simp [peelP, hnk]
    have hs1 : (List.range (k + 1)).filter actP = actL := by rw [filter_range_succ]; simp [hactk, actL]
    have hs2 : (List.range (k + 1)).filter peelP = peelL := by rw [filter_range_succ]; simp [hpeelk, peelL]
    refine ⟨fun _ _ _ _ => rfl, by rw [hs1, hrAT], by rw [hs2, hrPT], rfl, fun _ _ => rfl, ?_, ?_, ?_⟩
    · intro u hu
      rw [hmIA u hu]
      by_cases huk : u = k
      · subst huk; simp [hactk]
      · have hlt_eq : u < k + 1 ↔ u < k := by omega
        simp [hlt_eq]
    · intro i hi; rw [hs1] at hi ⊢; exact hmAS i hi
    · intro i hi; rw [hs2] at hi ⊢; exact hmPS i hi
  dsimp only [initQueueOneVertStmt]
  exact ((Triple.cond_const
    (P := fun st => st = st₀)
    (e := .bin .lt (.const 0) (.reg prTmp1))
    (val := fun st => if 0 < st.regs prTmp1 then 1 else 0) (c_t := 50) (c_f := 1)
    (fun st hst' => by
      subst st; simp only [Expr.eval, hr1, h0lt, WordRAM.BinOp.eval]
      by_cases hcmp : 0 < (if inR k then 1 else 0) <;> simp [hcmp, h1lt, h0lt])
    (hthen_body.weaken_pre fun st ⟨hst', hne⟩ => by
      have hink : inR k = true := by
        subst st; cases ha : inR k <;> simp [hr1, ha] at hne; rfl
      exact ⟨hst', hink⟩)
    (helse_body.weaken_pre fun st ⟨hst', heq⟩ => by
      have hnk : inR k = false := by
        subst st; cases ha : inR k
        · rfl
        · simp [hr1, ha] at heq
      exact ⟨hst', hnk⟩)).mono_cost (T' := fun _ => 58)
        (fun _ _ => by simp only [Expr.size]; omega)).runs ω rfl


end MinCostFlow.Expander
