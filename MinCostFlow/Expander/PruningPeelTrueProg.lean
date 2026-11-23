module

public import MinCostFlow.Expander.PruningStepCommon

/-!
# Peel Step True-Branch Triple
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

/-! ## 3. `peelStepStmt` (`peelStep`) -/

/-- Word-RAM statement implementing `peelStep cfg v rest s` when `s.peelQ = v :: rest`.
Peeks `v := peelStk[peelTop - 1]`; if `outR[v] = 1` and `degR[v] < θ_out_nat`, conditionally
unlinks `v` (if `0 < h[v]`), decrements `peelTop`, and calls `removeOneFromRStmt`; otherwise
decrements `peelTop` only. -/
def peelStepStmt : Stmt :=
  seqStmts [
    .assign prTmp3 (.bin .sub (.reg prPeelTop) (.const 1)),
    .assign prU (.load (.bin .add (.reg prPeelStk) (.reg prTmp3))),
    .assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prU))),
    .assign prTmp2 (.load (.bin .add (.reg prDegR) (.reg prU))),
    .cond (.bin .eq (.bin .mul (.reg prTmp1) (.bin .lt (.reg prTmp2) (.reg prTheta))) (.const 1))
      (seqStmts [
        .assign prTmp1 (.load (.bin .add (.reg prHArr) (.reg prU))),
        .cond (.bin .lt (.const 0) (.reg prTmp1)) unlinkLvlStmt .nop,
        .assign prPeelTop (.bin .sub (.reg prPeelTop) (.const 1)),
        removeOneFromRStmt
      ])
      (.assign prPeelTop (.bin .sub (.reg prPeelTop) (.const 1)))
  ]

lemma peelStepStmt_noRand : peelStepStmt.NoRand := by
  apply seqStmts_noRand
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · refine ⟨?_, by simp [Stmt.NoRand]⟩
    apply seqStmts_noRand
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · simp [Stmt.NoRand]
    · exact ⟨unlinkLvlStmt_noRand, by simp [Stmt.NoRand]⟩
    · simp [Stmt.NoRand]
    · exact removeOneFromRStmt_noRand

lemma peelStep_true_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr v : ℕ}
    {rest : List ℕ} {s : PruneState} {buckets : ℕ → List ℕ} (st₀ : State)
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (hq : s.peelQ = v :: rest)
    (hvR : s.inR v = true) (hvDeg : s.degR v < cfg.θ_out_nat)
    (hθ : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d, d < cfg.θ_out_nat → 3 * d ≤ cfg.degX x)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w) :
    let n := cfg.G.n
    let s' := peelStep cfg v rest s
    let buckets' : ℕ → List ℕ :=
      if 1 ≤ s.h v then fun ℓ => if ℓ = s.h v then (buckets ℓ).erase v else buckets ℓ
      else buckets
    Triple w p
      (fun st =>
        (∀ r, r ≤ prCsrAdjH → st.regs r = st₀.regs r) ∧
        st.regs prU = v ∧
        st.pos = st₀.pos ∧
        st.mem = st₀.mem)
      (seqStmts [
        .assign prTmp1 (.load (.bin .add (.reg prHArr) (.reg prU))),
        .cond (.bin .lt (.const 0) (.reg prTmp1)) unlinkLvlStmt .nop,
        .assign prPeelTop (.bin .sub (.reg prPeelTop) (.const 1)),
        removeOneFromRStmt
      ])
      (normalPost fun st' =>
        (∀ r, r ≤ prCsrAdjH → r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + n)
          (wHArr workAddr n cfg.G.m cfg.H) (workAddr + pruneWorkSpace n cfg.G.m cfg.H) ∧
        PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s' buckets' st')
      (fun _ => 150 * (cfg.incEdges v).length + 140) := by
  intro n s' buckets' st ω ⟨hregs, hrU, hpos, hmem⟩
  set m := cfg.G.m
  set H := cfg.H
  have hGv := hinv.cfg_valid.1
  have hw_pos := pruneWordBound_pos hw
  have hwb : workAddr + pruneWorkSpace n m H < 2 ^ w := by
    unfold PruneWordBound at hw; dsimp only [n, m, H] at *; omega
  have h0lt : 0 < 2 ^ w := by omega
  have h1lt : 1 < 2 ^ w := by omega
  have hpq_info := peelQInv_to_nodup_lt hinv.cfg_X hinv.peelQ_inv
  have hvn : v < n := (hpq_info.2 v (hq ▸ List.mem_cons_self)).1
  have hvX : v ∈ cfg.X := hinv.prune_inv.inR_sub v hvR
  have hhv_lt_H : s.h v < H := hinv.prune_inv.h_lt_H v hvR
  have hpeel_len := hinv.peelQ_len_le
  have hrest_n : rest.length < n := by rw [hq, List.length_cons] at hpeel_len; omega
  have hrest_w : rest.length < 2 ^ w := by
    unfold PruneWordBound at hw; dsimp only [n] at *; omega
  have hhv_val : st.mem (wHArr workAddr n m H + v) = s.h v := by
    rw [hmem]; exact hinv.h_eq v hvn
  have hrHArr : st.regs prHArr = wHArr workAddr n m H :=
    (hregs prHArr (by decide)).trans hinv.reg_hArr
  have hha_sum : wHArr workAddr n m H + v < 2 ^ w := by
    dsimp [wHArr]; unfold pruneWorkSpace at hwb; omega
  -- Step 1: load prTmp1 := h[v]
  apply runs_start_le
  apply runs_seq_assign_le (v := s.h v)
  · exact eval_load_add_regs hrHArr hrU hha_sum hhv_val (by
      have := hhv_lt_H; unfold PruneWordBound at hw; dsimp only [H] at *; omega)
  set st1 : State := { st with regs := Function.update st.regs prTmp1 (s.h v) }
  -- Construct PruneMemInv at st1 (st1.mem = st₀.mem; registers <= prCsrAdjH equal to st₀.regs)
  have h1regs : ∀ r, r ≤ prCsrAdjH → st1.regs r = st₀.regs r := by
    intro r hr
    dsimp only [st1]
    rw [Function.update_of_ne (show r ≠ prTmp1 by dsimp only [prCsrAdjH, prTmp1] at *; omega)]
    exact hregs r hr
  have hinv1 : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st1 :=
    { cfg_X := hinv.cfg_X
      cfg_valid := hinv.cfg_valid
      reg_g := (h1regs prG (by decide)).trans hinv.reg_g
      reg_csr := (h1regs prCsr (by decide)).trans hinv.reg_csr
      reg_inB := (h1regs prInB (by decide)).trans hinv.reg_inB
      reg_outR := (h1regs prOutR (by decide)).trans hinv.reg_outR
      reg_work := (h1regs prWork (by decide)).trans hinv.reg_work
      reg_ccap := (h1regs prCcap (by decide)).trans hinv.reg_ccap
      reg_H := (h1regs prH (by decide)).trans hinv.reg_H
      reg_theta := (h1regs prTheta (by decide)).trans hinv.reg_theta
      reg_n := (h1regs prN (by decide)).trans hinv.reg_n
      reg_m := (h1regs prM (by decide)).trans hinv.reg_m
      reg_actTop := (h1regs prActTop (by decide)).trans hinv.reg_actTop
      reg_peelTop := (h1regs prPeelTop (by decide)).trans hinv.reg_peelTop
      reg_degX := (h1regs prDegX (by decide)).trans hinv.reg_degX
      reg_hArr := (h1regs prHArr (by decide)).trans hinv.reg_hArr
      reg_cur := (h1regs prCur (by decide)).trans hinv.reg_cur
      reg_abs := (h1regs prAbs (by decide)).trans hinv.reg_abs
      reg_ex := (h1regs prEx (by decide)).trans hinv.reg_ex
      reg_degR := (h1regs prDegR (by decide)).trans hinv.reg_degR
      reg_inAct := (h1regs prInAct (by decide)).trans hinv.reg_inAct
      reg_actStk := (h1regs prActStk (by decide)).trans hinv.reg_actStk
      reg_peelStk := (h1regs prPeelStk (by decide)).trans hinv.reg_peelStk
      reg_lvlNext := (h1regs prLvlNext (by decide)).trans hinv.reg_lvlNext
      reg_lvlPrev := (h1regs prLvlPrev (by decide)).trans hinv.reg_lvlPrev
      reg_remArr := (h1regs prRemArr (by decide)).trans hinv.reg_remArr
      reg_flowEnc := (h1regs prFlowEnc (by decide)).trans hinv.reg_flowEnc
      reg_lvlVol := (h1regs prLvlVol (by decide)).trans hinv.reg_lvlVol
      reg_lvlHead := (h1regs prLvlHead (by decide)).trans hinv.reg_lvlHead
      reg_adjV := (h1regs prCsrAdjV (by decide)).trans hinv.reg_adjV
      reg_adjH := (h1regs prCsrAdjH (by decide)).trans hinv.reg_adjH
      graph_at := hmem.symm ▸ hinv.graph_at
      csr_at := hmem.symm ▸ hinv.csr_at
      inB_eq := hmem.symm ▸ hinv.inB_eq
      outR_eq := hmem.symm ▸ hinv.outR_eq
      degX_eq := hmem.symm ▸ hinv.degX_eq
      h_eq := hmem.symm ▸ hinv.h_eq
      cur_eq := hmem.symm ▸ hinv.cur_eq
      abs_eq := hmem.symm ▸ hinv.abs_eq
      ex_eq := hmem.symm ▸ hinv.ex_eq
      degR_eq := hmem.symm ▸ hinv.degR_eq
      inAct_eq := hmem.symm ▸ hinv.inAct_eq
      actStk_eq := hmem.symm ▸ hinv.actStk_eq
      peelStk_eq := hmem.symm ▸ hinv.peelStk_eq
      flowEnc_eq := hmem.symm ▸ hinv.flowEnc_eq
      lvlVol_H := hmem.symm ▸ hinv.lvlVol_H
      lvlVol_eq := hmem.symm ▸ hinv.lvlVol_eq
      buckets_nodup := hinv.buckets_nodup
      buckets_mem := hinv.buckets_mem
      buckets_dl := hmem.symm ▸ hinv.buckets_dl
      ex_bound := hinv.ex_bound
      prune_inv := hinv.prune_inv
      peelQ_inv := hinv.peelQ_inv }
  -- Step 2: conditional unlinkLvlStmt; unify both branches via Triple on cond
  set PostUnlink : State → Prop := fun st2 =>
    (∀ r, r ≤ prCsrAdjH → st2.regs r = st₀.regs r) ∧
    st2.regs prU = v ∧
    st2.pos = st₀.pos ∧
    BucketMemPreserved st₀.mem st2.mem workAddr n m H (s.h v) ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ < H →
      st2.mem (wLvlVol workAddr n m H + ℓ) =
        if ℓ = s.h v then volAtLevel cfg s.inR s.h ℓ - cfg.degX v
        else volAtLevel cfg s.inR s.h ℓ) ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ < H → ℓ ≠ s.h v →
      DoublyLinked st2.mem (wLvlNext workAddr n m H) (wLvlPrev workAddr n m H) n
        (buckets' ℓ) n (st2.mem (wLvlHead workAddr n m H + ℓ))) ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ < H →
      DoublyLinked st2.mem (wLvlNext workAddr n m H) (wLvlPrev workAddr n m H) n
        (buckets' ℓ) n (st2.mem (wLvlHead workAddr n m H + ℓ)))
  have hcond_unlink : Triple w p (fun sx => sx = st1)
      (.cond (.bin .lt (.const 0) (.reg prTmp1)) unlinkLvlStmt .nop)
      (normalPost PostUnlink) (fun _ => 86) := by
    intro sx ω hsx
    subst sx
    have h1_u : st1.regs prU = v := by
      dsimp only [st1]; rw [Function.update_of_ne (by decide)]; exact hrU
    have h1_t1 : st1.regs prTmp1 = s.h v := by dsimp only [st1]; rw [Function.update_self]
    have hcond_eval : Expr.eval w st1 (.bin .lt (.const 0) (.reg prTmp1)) =
        some (if 0 < s.h v then 1 else 0) := by
      have hif_lt : (if 0 < s.h v then 1 else 0) < 2 ^ w := by split_ifs <;> omega
      simp [Expr.eval, h1_t1, WordRAM.BinOp.eval, h0lt, hif_lt]
    by_cases hhv : 0 < s.h v
    · have hunlink := unlinkLvl_triple (p := p) (gAddr := gAddr) (csrAddr := csrAddr)
        (inBAddr := inBAddr) (outRAddr := outRAddr) (buckets := buckets) st1 hw hvn hvR hhv
      obtain ⟨o2, st2, c2, hrun2, hpost2, hc2⟩ := hunlink.runs ω ⟨rfl, hinv1, h1_u⟩
      cases o2 with
      | returned _ => exact absurd hrun2 (by cases hpost2)
      | normal =>
          rcases hpost2 with ⟨hr2, hp2, hbmp2, hvol2, hdl_other2, hdl_erase2⟩
          refine ⟨.normal, st2, 3 + c2 + 1,
            runs_cond_iff.mpr ⟨1, c2, by simpa [hhv] using hcond_eval, by simpa using hrun2, rfl⟩,
            ?_, by dsimp only; omega⟩
          have hb_eq : buckets' = fun ℓ => if ℓ = s.h v then (buckets ℓ).erase v else buckets ℓ := by
            simp [buckets', show 1 ≤ s.h v by omega]
          have hbmp02 : BucketMemPreserved st₀.mem st2.mem workAddr n m H (s.h v) := by
            simpa [st1, hmem] using hbmp2
          refine ⟨fun r hr => (hr2 r
              (by dsimp only [prCsrAdjH, prTmp1] at *; omega)
              (by dsimp only [prCsrAdjH, prTmp2] at *; omega)
              (by dsimp only [prCsrAdjH, prTmp3] at *; omega)
              (by dsimp only [prCsrAdjH, prSuf] at *; omega)).trans (h1regs r hr),
            (hr2 prU (by decide) (by decide) (by decide) (by decide)).trans h1_u,
            hp2.trans hpos, hbmp02, ?_, ?_, ?_⟩
          · intro ℓ hℓ1 hℓH
            dsimp only [n, m, H] at *
            by_cases heq : ℓ = s.h v
            · subst heq
              have hm1 : st1.mem (wLvlVol workAddr n m H + s.h v) = volAtLevel cfg s.inR s.h (s.h v) :=
                hinv1.lvlVol_eq (s.h v) hℓ1 hhv_lt_H
              rw [hvol2, hm1]; simp
            · rw [(hbmp02.2.2 ℓ (le_of_lt hℓH) heq).1, hinv.lvlVol_eq ℓ hℓ1 hℓH]
              simp [heq]
          · intro ℓ hℓ1 hℓH hne
            rw [hb_eq]; simp only [hne, ↓reduceIte]
            exact hdl_other2 ℓ hℓ1 hℓH hne
          · intro ℓ hℓ1 hℓH
            rw [hb_eq]
            by_cases heq : ℓ = s.h v
            · subst heq; simp only [↓reduceIte]; exact hdl_erase2
            · simp only [heq, ↓reduceIte]; exact hdl_other2 ℓ hℓ1 hℓH heq
    · have hhv0 : s.h v = 0 := by omega
      refine ⟨.normal, st1, 3 + 1 + 1,
        runs_cond_iff.mpr ⟨0, 1, by simpa [hhv] using hcond_eval,
          by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
        ?_, by dsimp only; omega⟩
      have hb_eq : buckets' = buckets := by simp [buckets', hhv0]
      have hmem1 : st1.mem = st₀.mem := hmem
      have hbmp_refl : BucketMemPreserved st₀.mem st1.mem workAddr n m H (s.h v) := by
        rw [hmem1]; exact ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
      refine ⟨h1regs, h1_u, hpos, hbmp_refl, ?_, ?_, ?_⟩
      · intro ℓ hℓ1 hℓH
        dsimp only [n, m, H] at *
        have hne : ℓ ≠ s.h v := by omega
        simp [hne, hmem1]
        exact hinv.lvlVol_eq ℓ hℓ1 hℓH
      · intro ℓ hℓ1 hℓH _
        rw [hb_eq, hmem1]; exact hinv.buckets_dl ℓ hℓ1 hℓH
      · intro ℓ hℓ1 hℓH
        rw [hb_eq, hmem1]; exact hinv.buckets_dl ℓ hℓ1 hℓH
  apply runs_seq_triple_le hcond_unlink rfl
  intro st2 ⟨hr2_regs, hr2_u, hr2_pos, hbmp02, hvol2, _, hdl2⟩
  -- Step 3: decrement prPeelTop
  apply runs_seq_assign_le (v := rest.length)
  · exact eval_sub_reg_const ((hr2_regs prPeelTop (by decide)).trans hinv.reg_peelTop |>.trans (by rw [hq, List.length_cons]))
      (by unfold PruneWordBound at hw; dsimp only [n] at *; omega) h1lt
  set st3 : State := { st2 with regs := Function.update st2.regs prPeelTop rest.length }
  -- Step 4: removeOneFromRStmt
  have hcond_bool : (s.inR v && decide (s.degR v < cfg.θ_out_nat)) = true := by
    simp [hvR, hvDeg]
  have hs'_eq : s' = { removeOneFromR cfg v { s with peelQ := rest } with
      steps := s.steps + 1 + (cfg.incEdges v).length } :=
    peelStep_eq_pop_first hq hcond_bool
  have hinR_eq : (removeOneFromR cfg v s).inR = fun x => if x = v then false else s.inR x := by
    ext x; exact removeOneFromR_inR cfg v s x
  have h3_regs : ∀ r, r ≤ prCsrAdjH → r ≠ prPeelTop → st3.regs r = st₀.regs r := by
    intro r hr hne
    dsimp only [st3]
    rw [Function.update_of_ne hne]
    exact hr2_regs r hr
  have h3_ptrs : PruneStepRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st3 :=
    pruneStepRegs_of_agree hinv.stepRegs (fun r hr _ hpt => h3_regs r hr hpt)
  have h3_u : st3.regs prU = v := by
    dsimp only [st3]; rw [Function.update_of_ne (by decide)]; exact hr2_u
  have h3_AT : st3.regs prActTop = s.active.length :=
    (h3_regs prActTop (by decide) (by decide)).trans hinv.reg_actTop
  have h3_PT : st3.regs prPeelTop = rest.length := by
    dsimp only [st3]; rw [Function.update_self]
  have hbmp03 : BucketMemPreserved st₀.mem st3.mem workAddr n m H (s.h v) := hbmp02
  have h3_mem_below_lvlNext : ∀ k < wLvlNext workAddr n m H, st3.mem k = st₀.mem k := fun k hk =>
    hbmp03.1 k (Or.inl hk)
  have h3_mem_outside_work : ∀ k, k < workAddr ∨ workAddr + pruneWorkSpace n m H ≤ k →
      st3.mem k = st₀.mem k := by
    intro k hk
    apply hbmp03.1 k
    rcases hk with hlt | hge
    · exact Or.inl (by dsimp [wHArr, wLvlNext]; omega)
    · exact Or.inr (by unfold pruneWorkSpace at hge; dsimp [wLvlHead]; omega)
  have h3_csr : HasCsrAt st3.mem csrAddr cfg.G := by
    have hdisj_cw := hdisj.2.2.2.2.1
    refine ⟨fun u hu => ?_, fun u hu j hj => ?_⟩
    · rw [h3_mem_outside_work (csrAddr + u) (by dsimp only [n, m, H] at *; rcases hdisj_cw with h | h <;> omega)]
      exact hinv.csr_at.1 u hu
    · have hj_lt : csrOff cfg.G u + j < 2 * m := by
        have hs := csrOff_succ cfg.G u
        have hle := csrOff_le_two_mul_m cfg.G (u + 1)
        dsimp [m, Cited.Graph.m] at *; omega
      refine ⟨?_, ?_⟩
      · rw [h3_mem_outside_work (csrAddr + 2 * n + 1 + csrOff cfg.G u + j)
          (by dsimp only [n, m, H] at *; rcases hdisj_cw with h | h <;> omega)]
        exact (hinv.csr_at.2 u hu j hj).1
      · rw [h3_mem_outside_work (csrAddr + 2 * n + 1 + 2 * m + csrOff cfg.G u + j)
          (by dsimp only [n, m, H] at *; rcases hdisj_cw with h | h <;> omega)]
        exact (hinv.csr_at.2 u hu j hj).2
  have hsw0 : SweepInv cfg ∅ s := (pruningInv_iff_sweepInv_empty cfg s).mp hinv.prune_inv
  have hrest_nd : rest.Nodup := (List.nodup_cons.mp (hq ▸ hpq_info.1)).2
  have hrest_lt : ∀ x ∈ rest, x < n ∧ ((if x = v then false else s.inR x) = true → s.degR x < cfg.θ_out_nat) := by
    intro x hx
    refine ⟨(hpq_info.2 x (hq ▸ List.mem_cons_of_mem _ hx)).1, fun _ =>
      (hpq_info.2 x (hq ▸ List.mem_cons_of_mem _ hx)).2 (by simp_all)⟩
  have hrest_iso : ∀ x, (cfg.incEdges x).length = 0 → x ∉ rest := fun x hx hmem_r =>
    (hinv.prune_inv.no_ex_isolated x hx).2.2.2 (hq ▸ List.mem_cons_of_mem _ hmem_r)
  have hrm := removeOneFromR_triple (p := p) rest st3 hinv.cfg_X hinv.cfg_valid hsw0 hvR
    hrest_nd hrest_lt hrest_iso hw hdisj hcsr_w houtR_w h3_csr
  apply runs_triple_le hrm
  · refine ⟨rfl, h3_ptrs, h3_u, h3_AT, h3_PT, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      rw [h3_mem_outside_work (outRAddr + u) (by
        dsimp only [n, m, H] at *; rcases hdisj.2.2.2.2.2.2 with h | h <;> omega)]
      exact hinv.outR_eq u hu
    · intro u hu
      rw [h3_mem_below_lvlNext (wEx workAddr n m H + u) (by dsimp [wEx, wLvlNext]; omega)]
      exact hinv.ex_eq u hu
    · intro u hu
      rw [h3_mem_below_lvlNext (wDegR workAddr n m H + u) (by dsimp [wDegR, wLvlNext]; omega)]
      exact hinv.degR_eq u hu
    · intro u hu
      rw [h3_mem_below_lvlNext (wInAct workAddr n m H + u) (by dsimp [wInAct, wLvlNext]; omega)]
      exact hinv.inAct_eq u hu
    · intro i hi
      rw [h3_mem_below_lvlNext (wActStk workAddr n m H + i) (by
        have := hinv.active_len_le; dsimp [wActStk, wLvlNext]; omega)]
      exact hinv.actStk_eq i hi
    · intro i hi
      rw [h3_mem_below_lvlNext (wPeelStk workAddr n m H + i) (by
        dsimp [wPeelStk, wLvlNext]; omega)]
      have hi1 : i < s.peelQ.length := by rw [hq, List.length_cons]; omega
      rw [hinv.peelStk_eq i hi1, hq]
      have hidx : (v :: rest).length - 1 - i = (rest.length - 1 - i) + 1 := by simp; omega
      rw [hidx]; rfl
    · intro idx hidx
      rw [hbmp03.2.1 (wFlowEnc workAddr n m H + idx)
        (by dsimp [wLvlPrev, wFlowEnc]; omega)
        (by dsimp [wFlowEnc, wLvlVol]; omega)]
      exact hinv.flowEnc_eq idx hidx
  · intro o stFin hFin
    cases o with
    | returned _ => exact absurd hFin (by simp [normalPost])
    | normal =>
        rcases hFin with ⟨hregsF, hptrsF, _, hrAT_F, hrPT_F, hposF, hpr3F,
          houtR_F, hex_F, hdr_F, hia_F, has_F, hps_F⟩
        set inR' : ℕ → Bool := fun x => if x = v then false else s.inR x
        set sInit : PruneState := { s with inR := inR', peelQ := rest }
        set sRes : PruneState := (cfg.incEdges v).foldl (removeEdgeStep cfg s.flow inR') sInit
        set sRm : PruneState := removeOneFromR cfg v s
        obtain ⟨_, _, hshift⟩ :=
          foldl_removeEdgeStep_peelShift cfg s.flow inR' (cfg.incEdges v)
            { s with inR := inR' }
        obtain ⟨_, hs_inR, hs_h, hs_cur, hs_abs, hs_ex, hs_degR, hs_act, hs_inAct, hs_flow, _⟩ :=
          hshift rest
        have hs2_eq_sRes : removeOneFromR cfg v { s with peelQ := rest } = sRes := rfl
        have hs'_peel : s'.peelQ = sRes.peelQ := by rw [hs'_eq, hs2_eq_sRes]
        have hs'_inR : s'.inR = sRm.inR := by rw [hs'_eq, hs2_eq_sRes]; exact hs_inR
        have hs'_h : s'.h = sRm.h := by rw [hs'_eq, hs2_eq_sRes]; exact hs_h
        have hs'_cur : s'.cur = sRm.cur := by rw [hs'_eq, hs2_eq_sRes]; exact hs_cur
        have hs'_abs : s'.abs = sRm.abs := by rw [hs'_eq, hs2_eq_sRes]; exact hs_abs
        have hs'_ex : s'.ex = sRm.ex := by rw [hs'_eq, hs2_eq_sRes]; exact hs_ex
        have hs'_degR : s'.degR = sRm.degR := by rw [hs'_eq, hs2_eq_sRes]; exact hs_degR
        have hs'_act : s'.active = sRm.active := by rw [hs'_eq, hs2_eq_sRes]; exact hs_act
        have hs'_inAct : s'.inActive = sRm.inActive := by rw [hs'_eq, hs2_eq_sRes]; exact hs_inAct
        have hs'_flow : s'.flow = sRm.flow := by rw [hs'_eq, hs2_eq_sRes]; exact hs_flow
        have hsRm_const := foldl_removeEdgeStep_const cfg s.flow inR' (cfg.incEdges v)
          { s with inR := inR' }
        have hs'_h_eq : s'.h = s.h := hs'_h.trans hsRm_const.2.1
        have hs'_cur_eq : s'.cur = s.cur := hs'_cur.trans hsRm_const.2.2.1
        have hs'_abs_eq : s'.abs = s.abs := hs'_abs.trans hsRm_const.2.2.2.1
        have hs'_flow_eq : s'.flow = s.flow := hs'_flow.trans hsRm_const.2.2.2.2.1
        have hs'_inR_eq : s'.inR = inR' := hs'_inR.trans hsRm_const.1
        have hregs_fin : ∀ r, r ≤ prCsrAdjH → r ≠ prActTop → r ≠ prPeelTop →
            stFin.regs r = st₀.regs r := by
          intro r hr hat hpt
          refine (hregsF r (by dsimp only [prCsrAdjH, prStart] at *; omega)
            (by dsimp only [prCsrAdjH, prEnd] at *; omega)
            (by dsimp only [prCsrAdjH, prJ] at *; omega)
            (by dsimp only [prCsrAdjH, prW] at *; omega)
            (by dsimp only [prCsrAdjH, prIdx] at *; omega)
            (by dsimp only [prCsrAdjH, prDir] at *; omega)
            (by dsimp only [prCsrAdjH, prRc] at *; omega)
            (by dsimp only [prCsrAdjH, prTmp1] at *; omega)
            (by dsimp only [prCsrAdjH, prTmp2] at *; omega)
            (by dsimp only [prCsrAdjH, prTmp3] at *; omega)
            hat hpt).trans (h3_regs r hr hpt)
        have hpr02_work : PreservedOutside2 st₀.mem st3.mem outRAddr (outRAddr + n)
            (wHArr workAddr n m H) (workAddr + pruneWorkSpace n m H) := by
          intro k _ hk
          apply hbmp03.1 k
          rcases hk with hlt | hge
          · exact Or.inl (by dsimp [wHArr, wLvlNext] at hlt ⊢; omega)
          · exact Or.inr (by unfold pruneWorkSpace at hge; dsimp [wLvlHead]; omega)
        have hpr3F_widen : PreservedOutside2 st3.mem stFin.mem outRAddr (outRAddr + n)
            (wHArr workAddr n m H) (workAddr + pruneWorkSpace n m H) :=
          preservedOutside2_sub_right hpr3F (by dsimp [wHArr, wEx]; omega)
            (by unfold pruneWorkSpace; dsimp [wLvlNext]; omega)
        have hpr0F : PreservedOutside2 st₀.mem stFin.mem outRAddr (outRAddr + n)
            (wHArr workAddr n m H) (workAddr + pruneWorkSpace n m H) :=
          preservedOutside2_trans hpr02_work hpr3F_widen
        obtain ⟨hG_F, hCsr_F, hinB_F, hdegX_F⟩ := static_of_preserved2 hinv hdisj hpr0F
        have hstFin_below_ex : ∀ k, workAddr ≤ k → k < wEx workAddr n m H → stFin.mem k = st₀.mem k := by
          intro k hk0 hk
          have hk_outR : k < outRAddr ∨ outRAddr + n ≤ k := by
            have hdw := hdisj.2.2.2.2.2.2
            unfold pruneWorkSpace at hdw
            dsimp only [wEx] at hk
            dsimp only [n, m, H] at *
            rcases hdw with h | h <;> omega
          have h1 := hpr3F k hk_outR (Or.inl hk)
          have h2 := h3_mem_below_lvlNext k (by dsimp [wEx, wLvlNext] at hk ⊢; omega)
          exact h1.trans h2
        have hstFin_lvlNext_work : ∀ k, wLvlNext workAddr n m H ≤ k →
            k < workAddr + pruneWorkSpace n m H → stFin.mem k = st3.mem k := by
          intro k hk1 hk2
          have hk_outR : k < outRAddr ∨ outRAddr + n ≤ k := by
            have hdw := hdisj.2.2.2.2.2.2
            unfold pruneWorkSpace at hdw hk2
            dsimp only [wLvlNext] at hk1
            dsimp only [n, m, H] at *
            rcases hdw with h | h <;> omega
          exact hpr3F k hk_outR (Or.inr hk1)
        have hstep_inv := (peelStep_inv_pot_pub hinv.cfg_valid hinv.prune_inv hq hθ).1
        have hstep_pq := peelStep_peelQInv hinv.prune_inv.inR_sub hinv.peelQ_inv hq
        have hsw'_rm := (removeOneFromR_inv hinv.cfg_valid hsw0 hvR).1
        have hex'_bound : ∀ u < n, s'.ex u ≤ 4 * cfg.C_cap * m := by
          intro u hu
          rw [hs'_ex]
          exact ex_bound_of_sweep_after_removeOne hinv.cfg_X hGv hinv.ex_bound hsw'_rm u hu
        have hlvlVol_H_F : stFin.mem (wLvlVol workAddr n m H + H) = 0 := by
          rw [hstFin_lvlNext_work (wLvlVol workAddr n m H + H)
            (by dsimp [wLvlNext, wLvlVol]; omega)
            (by unfold pruneWorkSpace; dsimp [wLvlVol]; omega)]
          rw [(hbmp03.2.2 H (le_refl H) (by omega)).1]
          exact hinv.lvlVol_H
        have hlvlVol_eq_F : ∀ ℓ, 1 ≤ ℓ → ℓ < H →
            stFin.mem (wLvlVol workAddr n m H + ℓ) = volAtLevel cfg s'.inR s'.h ℓ := by
          intro ℓ hℓ1 hℓH
          rw [hstFin_lvlNext_work (wLvlVol workAddr n m H + ℓ)
            (by dsimp [wLvlNext, wLvlVol]; omega)
            (by unfold pruneWorkSpace; dsimp [wLvlVol]; omega)]
          rw [hvol2 ℓ hℓ1 hℓH, hs'_inR_eq, hs'_h_eq, volAtLevel_erase hvX hvR]
          by_cases heq : ℓ = s.h v <;> simp [heq, Eq.comm]
        have hbuckets_nd_F : ∀ ℓ, 1 ≤ ℓ → ℓ < H → (buckets' ℓ).Nodup := by
          intro ℓ hℓ1 hℓH
          dsimp only [buckets', n, m, H] at *
          by_cases h1 : 1 ≤ s.h v
          · by_cases h2 : ℓ = s.h v
            · rw [← h2]
              simp only [hℓ1, ↓reduceIte]
              exact (hinv.buckets_nodup ℓ hℓ1 hℓH).erase v
            · simp [h1, h2, hinv.buckets_nodup ℓ hℓ1 hℓH]
          · simp [h1, hinv.buckets_nodup ℓ hℓ1 hℓH]
        have hbuckets_mem_F : ∀ ℓ, 1 ≤ ℓ → ℓ < H →
            ∀ x, x ∈ buckets' ℓ ↔ x < n ∧ s'.inR x = true ∧ s'.h x = ℓ := by
          intro ℓ hℓ1 hℓH x
          dsimp only [buckets', n, m, H] at *
          rw [hs'_inR_eq, hs'_h_eq]
          by_cases hh1 : 1 ≤ s.h v
          · by_cases heq : ℓ = s.h v
            · subst heq
              simp only [hh1, ↓reduceIte]
              constructor
              · intro hx
                have hne : x ≠ v := fun hv => by
                  subst hv; exact List.Nodup.not_mem_erase (hinv.buckets_nodup _ hℓ1 hℓH) hx
                have hx0 := (hinv.buckets_mem (s.h v) hℓ1 hℓH x).mp (List.mem_of_mem_erase hx)
                refine ⟨hx0.1, ?_, hx0.2.2⟩
                dsimp only [inR']; simp [hne, hx0.2.1]
              · rintro ⟨hxn, hxR, hxh⟩
                have hne : x ≠ v := fun hv => by subst hv; simp [inR'] at hxR
                have hxR0 : s.inR x = true := by simpa [inR', hne] using hxR
                exact (List.mem_erase_of_ne hne).mpr ((hinv.buckets_mem (s.h v) hℓ1 hℓH x).mpr ⟨hxn, hxR0, hxh⟩)
            · simp only [hh1, heq, ↓reduceIte]
              constructor
              · intro hx
                obtain ⟨hxn, hxR0, hxh⟩ := (hinv.buckets_mem ℓ hℓ1 hℓH x).mp hx
                have hne : x ≠ v := fun hv => heq (hv ▸ hxh.symm)
                exact ⟨hxn, by simp [inR', hne, hxR0], hxh⟩
              · rintro ⟨hxn, hxR, hxh⟩
                have hne : x ≠ v := fun hv => heq (hv ▸ hxh.symm)
                have hxR0 : s.inR x = true := by simpa [inR', hne] using hxR
                exact (hinv.buckets_mem ℓ hℓ1 hℓH x).mpr ⟨hxn, hxR0, hxh⟩
          · simp only [hh1, ↓reduceIte]
            constructor
            · intro hx
              obtain ⟨hxn, hxR0, hxh⟩ := (hinv.buckets_mem ℓ hℓ1 hℓH x).mp hx
              have hne : x ≠ v := fun hv => hh1 (by rw [← hv, hxh]; exact hℓ1)
              exact ⟨hxn, by simp [inR', hne, hxR0], hxh⟩
            · rintro ⟨hxn, hxR, hxh⟩
              have hne : x ≠ v := fun hv => hh1 (by rw [← hv, hxh]; exact hℓ1)
              have hxR0 : s.inR x = true := by simpa [inR', hne] using hxR
              exact (hinv.buckets_mem ℓ hℓ1 hℓH x).mpr ⟨hxn, hxR0, hxh⟩
        have hbuckets_dl_F : ∀ ℓ, 1 ≤ ℓ → ℓ < H →
            DoublyLinked stFin.mem (wLvlNext workAddr n m H) (wLvlPrev workAddr n m H) n
              (buckets' ℓ) n (stFin.mem (wLvlHead workAddr n m H + ℓ)) := by
          intro ℓ hℓ1 hℓH
          rw [hstFin_lvlNext_work (wLvlHead workAddr n m H + ℓ)
            (by dsimp [wLvlNext, wLvlHead]; omega)
            (by unfold pruneWorkSpace; dsimp [wLvlHead]; omega)]
          refine doublyLinked_congr_disjoint ?_ ?_ (hdl2 ℓ hℓ1 hℓH)
          · intro y hy
            have hyn : y < n := doublyLinked_mem_lt (hdl2 ℓ hℓ1 hℓH) hy
            exact hstFin_lvlNext_work (wLvlNext workAddr n m H + y)
              (by dsimp [wHArr, wLvlNext]; omega)
              (by unfold pruneWorkSpace; dsimp [wLvlNext]; omega)
          · intro y hy
            have hyn : y < n := doublyLinked_mem_lt (hdl2 ℓ hℓ1 hℓH) hy
            exact hstFin_lvlNext_work (wLvlPrev workAddr n m H + y)
              (by dsimp [wLvlNext, wLvlPrev]; omega)
              (by unfold pruneWorkSpace; dsimp [wLvlPrev]; omega)
        refine ⟨hregs_fin, hposF.trans hr2_pos, hpr0F,
          { cfg_X := hinv.cfg_X
            cfg_valid := hinv.cfg_valid
            reg_g := hptrsF.reg_g
            reg_csr := hptrsF.reg_csr
            reg_inB := hptrsF.reg_inB
            reg_outR := hptrsF.reg_outR
            reg_work := hptrsF.reg_work
            reg_ccap := hptrsF.reg_ccap
            reg_H := hptrsF.reg_H
            reg_theta := hptrsF.reg_theta
            reg_n := hptrsF.reg_n
            reg_m := hptrsF.reg_m
            reg_actTop := hrAT_F.trans (by rw [hs'_act])
            reg_peelTop := hrPT_F.trans (by rw [hs'_peel])
            reg_degX := hptrsF.reg_degX
            reg_hArr := hptrsF.reg_hArr
            reg_cur := hptrsF.reg_cur
            reg_abs := hptrsF.reg_abs
            reg_ex := hptrsF.reg_ex
            reg_degR := hptrsF.reg_degR
            reg_inAct := hptrsF.reg_inAct
            reg_actStk := hptrsF.reg_actStk
            reg_peelStk := hptrsF.reg_peelStk
            reg_lvlNext := hptrsF.reg_lvlNext
            reg_lvlPrev := hptrsF.reg_lvlPrev
            reg_remArr := hptrsF.reg_remArr
            reg_flowEnc := hptrsF.reg_flowEnc
            reg_lvlVol := hptrsF.reg_lvlVol
            reg_lvlHead := hptrsF.reg_lvlHead
            reg_adjV := hptrsF.reg_adjV
            reg_adjH := hptrsF.reg_adjH
            graph_at := hG_F
            csr_at := hCsr_F
            inB_eq := hinB_F
            outR_eq := fun u hu => by rw [houtR_F u hu, ← hs'_inR]
            degX_eq := hdegX_F
            h_eq := fun u hu => by
              rw [hstFin_below_ex (wHArr workAddr n m H + u) (by dsimp [wHArr]; omega)
                  (by dsimp [wHArr, wEx]; omega),
                hs'_h_eq]
              exact hinv.h_eq u hu
            cur_eq := fun u hu => by
              rw [hstFin_below_ex (wCur workAddr n m H + u) (by dsimp [wCur]; omega)
                  (by dsimp [wCur, wEx]; omega),
                hs'_cur_eq]
              exact hinv.cur_eq u hu
            abs_eq := fun u hu => by
              rw [hstFin_below_ex (wAbs workAddr n m H + u) (by dsimp [wAbs]; omega)
                  (by dsimp [wAbs, wEx]; omega),
                hs'_abs_eq]
              exact hinv.abs_eq u hu
            ex_eq := fun u hu => by rw [hex_F u hu, hs'_ex]
            degR_eq := fun u hu => by rw [hdr_F u hu, hs'_degR]
            inAct_eq := fun u hu => by rw [hia_F u hu, hs'_inAct]
            actStk_eq := fun i hi => by
              rw [hs'_act] at hi ⊢; exact has_F i hi
            peelStk_eq := fun i hi => by
              rw [hs'_peel] at hi ⊢; exact hps_F i hi
            flowEnc_eq := fun idx hidx => by
              rw [hstFin_lvlNext_work (wFlowEnc workAddr n m H + idx)
                (by dsimp [wLvlNext, wFlowEnc]; omega)
                (by unfold pruneWorkSpace; dsimp [wFlowEnc]; omega),
                hbmp03.2.1 (wFlowEnc workAddr n m H + idx)
                (by dsimp [wLvlPrev, wFlowEnc]; omega)
                (by dsimp [wFlowEnc, wLvlVol]; omega),
                hs'_flow_eq]
              exact hinv.flowEnc_eq idx hidx
            lvlVol_H := hlvlVol_H_F
            lvlVol_eq := hlvlVol_eq_F
            buckets_nodup := hbuckets_nd_F
            buckets_mem := hbuckets_mem_F
            buckets_dl := hbuckets_dl_F
            ex_bound := hex'_bound
            prune_inv := hstep_inv
            peelQ_inv := hstep_pq }⟩
  · simp only [Expr.size]; omega


end MinCostFlow.Expander
