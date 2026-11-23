module

public import MinCostFlow.Expander.PruningPeelTrueProg

/-!
# Peel Step and Pop-Inactive Step Triples
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

theorem peelStep_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr v : ℕ}
    {rest : List ℕ} {s : PruneState} {buckets : ℕ → List ℕ} (st₀ : State)
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (hq : s.peelQ = v :: rest)
    (hθ : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d, d < cfg.θ_out_nat → 3 * d ≤ cfg.degX x)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w) :
    let n := cfg.G.n
    let cond := s.inR v && decide (s.degR v < cfg.θ_out_nat)
    let s' := peelStep cfg v rest s
    let buckets' : ℕ → List ℕ :=
      if cond = true ∧ 1 ≤ s.h v then
        fun ℓ => if ℓ = s.h v then (buckets ℓ).erase v else buckets ℓ
      else buckets
    Triple w p
      (fun st => st = st₀)
      peelStepStmt
      (normalPost fun st' =>
        (∀ r, r ≤ prCsrAdjH → r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + n)
          (wHArr workAddr n cfg.G.m cfg.H) (workAddr + pruneWorkSpace n cfg.G.m cfg.H) ∧
        PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s' buckets' st')
      (fun _ => 180 * (s'.steps - s.steps)) := by
  intro n cond s' buckets' st ω hst
  subst st
  set m := cfg.G.m
  set H := cfg.H
  have hw_pos := pruneWordBound_pos hw
  have hwb : workAddr + pruneWorkSpace n m H < 2 ^ w := by
    unfold PruneWordBound at hw; dsimp only [n, m, H] at *; omega
  have h0lt : 0 < 2 ^ w := by omega
  have h1lt : 1 < 2 ^ w := by omega
  have hpq_info := peelQInv_to_nodup_lt hinv.cfg_X hinv.peelQ_inv
  have hvn : v < n := (hpq_info.2 v (hq ▸ List.mem_cons_self)).1
  have hv_w : v < 2 ^ w := by unfold PruneWordBound at hw; dsimp only [n] at *; omega
  have hpeel_len := hinv.peelQ_len_le
  have hrest_n : rest.length < n := by rw [hq, List.length_cons] at hpeel_len; omega
  have hrest_w : rest.length < 2 ^ w := by
    unfold PruneWordBound at hw; dsimp only [n] at *; omega
  have hps_v : st₀.mem (wPeelStk workAddr n m H + rest.length) = v := by
    have hi : rest.length < s.peelQ.length := by rw [hq, List.length_cons]; omega
    rw [hinv.peelStk_eq rest.length hi, hq]
    have hidx : (v :: rest).length - 1 - rest.length = 0 := by simp
    rw [hidx]; simp
  apply runs_start_le
  apply runs_seq_assign_le (v := rest.length)
  · exact eval_sub_reg_const (hinv.reg_peelTop.trans (by rw [hq, List.length_cons]))
      (by unfold PruneWordBound at hw; dsimp only [n] at *; omega) h1lt
  set st1 : State := { st₀ with regs := Function.update st₀.regs prTmp3 rest.length }
  apply runs_seq_assign_le (v := v)
  · exact eval_load_add_regs
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide)]; exact hinv.reg_peelStk)
      (by dsimp only [st1]; exact Function.update_self ..)
      (by dsimp [wPeelStk]; unfold pruneWorkSpace at hwb; omega)
      hps_v hv_w
  set st2 : State := { st1 with regs := Function.update st1.regs prU v }
  apply runs_seq_assign_le (v := if s.inR v then 1 else 0)
  · exact eval_load_add_regs
      (by dsimp only [st2, st1]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
          exact hinv.reg_outR)
      (by dsimp only [st2]; exact Function.update_self ..)
      (by dsimp only [n] at *; omega)
      (hinv.outR_eq v hvn)
      (by split_ifs <;> omega)
  set st3 : State := { st2 with regs := Function.update st2.regs prTmp1 (if s.inR v then 1 else 0) }
  apply runs_seq_assign_le (v := s.degR v)
  · refine eval_load_add_regs_any
      (by dsimp only [st3, st2, st1]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide)]
          exact hinv.reg_degR)
      (by dsimp only [st3, st2]
          rw [Function.update_of_ne (by decide), Function.update_self])
      (by dsimp [wDegR]; unfold pruneWorkSpace at hwb; omega)
      (hinv.degR_eq v hvn)
  set st4 : State := { st3 with regs := Function.update st3.regs prTmp2 (s.degR v) }
  -- Evaluate cond: (tmp1 * (tmp2 < theta)) == 1
  set inRvNum : ℕ := if s.inR v then 1 else 0
  set degLtNum : ℕ := if s.degR v < cfg.θ_out_nat then 1 else 0
  have h4_t1 : st4.regs prTmp1 = inRvNum := by
    dsimp only [st4, st3]; rw [Function.update_of_ne (by decide), Function.update_self]
  have h4_t2 : st4.regs prTmp2 = s.degR v := by
    dsimp only [st4]; rw [Function.update_self]
  have h4_theta : st4.regs prTheta = cfg.θ_out_nat := by
    dsimp only [st4, st3, st2, st1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact hinv.reg_theta
  have heval_cond : Expr.eval w st4
      (.bin .eq (.bin .mul (.reg prTmp1) (.bin .lt (.reg prTmp2) (.reg prTheta))) (.const 1)) =
      some (if cond = true then 1 else 0) := by
    by_cases h1 : s.inR v = true <;> by_cases h2 : s.degR v < cfg.θ_out_nat <;>
      simp [Expr.eval, h4_t1, h4_t2, h4_theta, inRvNum, WordRAM.BinOp.eval, cond, h1, h2, h0lt, h1lt]
  have h4_regs : ∀ r, r ≤ prCsrAdjH → st4.regs r = st₀.regs r := by
    intro r hr
    dsimp only [st4, st3, st2, st1]
    rw [Function.update_of_ne (by dsimp only [prCsrAdjH, prTmp2] at *; omega),
      Function.update_of_ne (by dsimp only [prCsrAdjH, prTmp1] at *; omega),
      Function.update_of_ne (by dsimp only [prCsrAdjH, prU] at *; omega),
      Function.update_of_ne (by dsimp only [prCsrAdjH, prTmp3] at *; omega)]
  have h4_u : st4.regs prU = v := by
    dsimp only [st4, st3, st2]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  by_cases hc : cond = true
  · have hc' : (s.inR v && decide (s.degR v < cfg.θ_out_nat)) = true := hc
    have hc_and : s.inR v = true ∧ s.degR v < cfg.θ_out_nat := by simpa using hc'
    have hstep_diff : s'.steps - s.steps = 1 + (cfg.incEdges v).length := by
      dsimp only [s', peelStep]
      simp only [hc', ↓reduceIte]
      omega
    have htr := peelStep_true_triple (p := p) st₀ hinv hq hc_and.1 hc_and.2 hθ hw hdisj hcsr_w houtR_w
    obtain ⟨oF, stF, cF, hrunF, hpostF, hcF⟩ := htr.runs ω ⟨h4_regs, h4_u, rfl, rfl⟩
    cases oF with
    | returned _ => exact absurd hrunF (by cases hpostF)
    | normal =>
        refine ⟨.normal, stF, _,
          runs_cond_iff.mpr ⟨1, cF, by simpa [hc] using heval_cond, by simpa using hrunF, rfl⟩,
          ?_, ?_⟩
        · have hbe : (if cond = true ∧ 1 ≤ s.h v then
              fun ℓ => if ℓ = s.h v then (buckets ℓ).erase v else buckets ℓ else buckets) =
              (if 1 ≤ s.h v then fun ℓ => if ℓ = s.h v then (buckets ℓ).erase v else buckets ℓ else buckets) := by
            simp [hc]
          simpa [hbe, buckets'] using hpostF
        · simp only [Expr.size] at *; rw [hstep_diff]; omega
  · have hcF : cond = false := Bool.eq_false_of_not_eq_true hc
    have hcF' : (s.inR v && decide (s.degR v < cfg.θ_out_nat)) = false := hcF
    have hstep_diff : s'.steps - s.steps = 1 := by
      dsimp only [s', peelStep]
      simp only [hcF', Bool.false_eq_true, ↓reduceIte]
      omega
    have hs'_eq : s' = { s with peelQ := rest, steps := s.steps + 1 } := by
      dsimp only [s', peelStep]
      simp [hcF']
    have hb_eq : buckets' = buckets := by simp [buckets', hcF]
    have hstep_inv := (peelStep_inv_pot_pub hinv.cfg_valid hinv.prune_inv hq hθ).1
    have hstep_pq := peelStep_peelQInv hinv.prune_inv.inR_sub hinv.peelQ_inv hq
    refine ⟨.normal, { st4 with regs := Function.update st4.regs prPeelTop rest.length }, _,
      runs_cond_iff.mpr ⟨0, _, by simpa [hcF] using heval_cond,
        (by
          have he := eval_sub_reg_const
            ((h4_regs prPeelTop (by decide)).trans hinv.reg_peelTop |>.trans (by rw [hq, List.length_cons]))
            (by unfold PruneWordBound at hw; dsimp only [n] at *; omega) h1lt
          simpa using runs_assign_iff.mpr ⟨rest.length, he, rfl, rfl, rfl⟩),
        rfl⟩,
      ?_, ?_⟩
    · dsimp only [normalPost]
      set stF : State := { st4 with regs := Function.update st4.regs prPeelTop rest.length }
      have hF_regs : ∀ r, r ≤ prCsrAdjH → r ≠ prActTop → r ≠ prPeelTop → stF.regs r = st₀.regs r := by
        intro r hr _ hpt
        dsimp only [stF]
        rw [Function.update_of_ne hpt]
        exact h4_regs r hr
      refine ⟨hF_regs, rfl, preservedOutside2_refl _ _ _ _ _, ?_⟩
      have hmem_F : stF.mem = st₀.mem := rfl
      rw [hb_eq]
      exact
        { cfg_X := hinv.cfg_X
          cfg_valid := hinv.cfg_valid
          reg_g := (hF_regs prG (by decide) (by decide) (by decide)).trans hinv.reg_g
          reg_csr := (hF_regs prCsr (by decide) (by decide) (by decide)).trans hinv.reg_csr
          reg_inB := (hF_regs prInB (by decide) (by decide) (by decide)).trans hinv.reg_inB
          reg_outR := (hF_regs prOutR (by decide) (by decide) (by decide)).trans hinv.reg_outR
          reg_work := (hF_regs prWork (by decide) (by decide) (by decide)).trans hinv.reg_work
          reg_ccap := (hF_regs prCcap (by decide) (by decide) (by decide)).trans hinv.reg_ccap
          reg_H := (hF_regs prH (by decide) (by decide) (by decide)).trans hinv.reg_H
          reg_theta := (hF_regs prTheta (by decide) (by decide) (by decide)).trans hinv.reg_theta
          reg_n := (hF_regs prN (by decide) (by decide) (by decide)).trans hinv.reg_n
          reg_m := (hF_regs prM (by decide) (by decide) (by decide)).trans hinv.reg_m
          reg_actTop := by
            dsimp only [stF]
            rw [Function.update_of_ne (by decide), hs'_eq]
            exact (h4_regs prActTop (by decide)).trans hinv.reg_actTop
          reg_peelTop := by dsimp only [stF]; rw [Function.update_self, hs'_eq]
          reg_degX := (hF_regs prDegX (by decide) (by decide) (by decide)).trans hinv.reg_degX
          reg_hArr := (hF_regs prHArr (by decide) (by decide) (by decide)).trans hinv.reg_hArr
          reg_cur := (hF_regs prCur (by decide) (by decide) (by decide)).trans hinv.reg_cur
          reg_abs := (hF_regs prAbs (by decide) (by decide) (by decide)).trans hinv.reg_abs
          reg_ex := (hF_regs prEx (by decide) (by decide) (by decide)).trans hinv.reg_ex
          reg_degR := (hF_regs prDegR (by decide) (by decide) (by decide)).trans hinv.reg_degR
          reg_inAct := (hF_regs prInAct (by decide) (by decide) (by decide)).trans hinv.reg_inAct
          reg_actStk := (hF_regs prActStk (by decide) (by decide) (by decide)).trans hinv.reg_actStk
          reg_peelStk := (hF_regs prPeelStk (by decide) (by decide) (by decide)).trans hinv.reg_peelStk
          reg_lvlNext := (hF_regs prLvlNext (by decide) (by decide) (by decide)).trans hinv.reg_lvlNext
          reg_lvlPrev := (hF_regs prLvlPrev (by decide) (by decide) (by decide)).trans hinv.reg_lvlPrev
          reg_remArr := (hF_regs prRemArr (by decide) (by decide) (by decide)).trans hinv.reg_remArr
          reg_flowEnc := (hF_regs prFlowEnc (by decide) (by decide) (by decide)).trans hinv.reg_flowEnc
          reg_lvlVol := (hF_regs prLvlVol (by decide) (by decide) (by decide)).trans hinv.reg_lvlVol
          reg_lvlHead := (hF_regs prLvlHead (by decide) (by decide) (by decide)).trans hinv.reg_lvlHead
          reg_adjV := (hF_regs prCsrAdjV (by decide) (by decide) (by decide)).trans hinv.reg_adjV
          reg_adjH := (hF_regs prCsrAdjH (by decide) (by decide) (by decide)).trans hinv.reg_adjH
          graph_at := hinv.graph_at
          csr_at := hinv.csr_at
          inB_eq := hinv.inB_eq
          outR_eq := fun u hu => by rw [hs'_eq]; exact hinv.outR_eq u hu
          degX_eq := hinv.degX_eq
          h_eq := fun u hu => by rw [hs'_eq]; exact hinv.h_eq u hu
          cur_eq := fun u hu => by rw [hs'_eq]; exact hinv.cur_eq u hu
          abs_eq := fun u hu => by rw [hs'_eq]; exact hinv.abs_eq u hu
          ex_eq := fun u hu => by rw [hs'_eq]; exact hinv.ex_eq u hu
          degR_eq := fun u hu => by rw [hs'_eq]; exact hinv.degR_eq u hu
          inAct_eq := fun u hu => by rw [hs'_eq]; exact hinv.inAct_eq u hu
          actStk_eq := fun i hi => by rw [hs'_eq] at hi ⊢; exact hinv.actStk_eq i hi
          peelStk_eq := fun i hi => by
            rw [hs'_eq] at hi ⊢
            dsimp only at hi ⊢
            have hi1 : i < s.peelQ.length := by rw [hq, List.length_cons]; omega
            change st₀.mem (wPeelStk workAddr n m H + i) = rest.getD (rest.length - 1 - i) 0
            rw [hinv.peelStk_eq i hi1, hq]
            have hidx : (v :: rest).length - 1 - i = (rest.length - 1 - i) + 1 := by simp; omega
            rw [hidx]; rfl
          flowEnc_eq := fun idx hidx => by rw [hs'_eq]; exact hinv.flowEnc_eq idx hidx
          lvlVol_H := hinv.lvlVol_H
          lvlVol_eq := fun ℓ hℓ1 hℓH => by rw [hs'_eq]; exact hinv.lvlVol_eq ℓ hℓ1 hℓH
          buckets_nodup := hinv.buckets_nodup
          buckets_mem := fun ℓ hℓ1 hℓH x => by rw [hs'_eq]; exact hinv.buckets_mem ℓ hℓ1 hℓH x
          buckets_dl := hinv.buckets_dl
          ex_bound := fun u hu => by rw [hs'_eq]; exact hinv.ex_bound u hu
          prune_inv := hstep_inv
          peelQ_inv := hstep_pq }
    · simp only [Expr.size] at *; rw [hstep_diff]; omega

/-! ## 4. `popInactiveStepStmt`, `absorbStepStmt`, `advanceCurStepStmt` -/

/-- Word-RAM statement implementing `popInactiveStep u restAct s`:
pops `u` from `actStk` and sets `inAct[u] := 0`. -/
def popInactiveStepStmt : Stmt :=
  seqStmts [
    .assign prActTop (.bin .sub (.reg prActTop) (.const 1)),
    .assign prU (.load (.bin .add (.reg prActStk) (.reg prActTop))),
    .store (.bin .add (.reg prInAct) (.reg prU)) (.const 0)
  ]

lemma popInactiveStepStmt_noRand : popInactiveStepStmt.NoRand := by
  apply seqStmts_noRand
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> simp [Stmt.NoRand]

theorem popInactiveStep_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr u : ℕ}
    {restAct : List ℕ} {s : PruneState} {buckets : ℕ → List ℕ} (st₀ : State)
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (hact : s.active = u :: restAct)
    (hdead : s.inR u = false ∨ s.ex u = 0)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length) :
    let n := cfg.G.n
    let s' := popInactiveStep u restAct s
    Triple w p
      (fun st => st = st₀)
      popInactiveStepStmt
      (normalPost fun st' =>
        (∀ r, r ≤ prCsrAdjH → r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + n)
          (wHArr workAddr n cfg.G.m cfg.H) (workAddr + pruneWorkSpace n cfg.G.m cfg.H) ∧
        PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s' buckets st')
      (fun _ => 30) := by
  intro n s' st ω hst
  subst st
  set m := cfg.G.m; set H := cfg.H
  have hw_pos := pruneWordBound_pos hw
  have hwb : workAddr + pruneWorkSpace n m H < 2 ^ w := by
    unfold PruneWordBound at hw; dsimp only [n, m, H] at *; omega
  have h0lt : 0 < 2 ^ w := by omega
  have h1lt : 1 < 2 ^ w := by omega
  have huX := hinv.prune_inv.active_sub u (hact ▸ List.mem_cons_self)
  have hun : u < n := by rw [hinv.cfg_X] at huX; exact Finset.mem_range.mp huX
  have hu_w : u < 2 ^ w := by unfold PruneWordBound at hw; dsimp only [n] at *; omega
  have hact_len := hinv.active_len_le
  have hrest_n : restAct.length < n := by rw [hact, List.length_cons] at hact_len; omega
  have has_u : st₀.mem (wActStk workAddr n m H + restAct.length) = u := by
    have hi : restAct.length < s.active.length := by rw [hact, List.length_cons]; omega
    rw [hinv.actStk_eq restAct.length hi, hact]
    have hidx : (u :: restAct).length - 1 - restAct.length = 0 := by simp
    rw [hidx]; simp
  apply runs_start_le
  apply runs_seq_assign_le (v := restAct.length)
  · exact eval_sub_reg_const (hinv.reg_actTop.trans (by rw [hact, List.length_cons]))
      (by unfold PruneWordBound at hw; dsimp only [n] at *; omega) h1lt
  set st1 : State := { st₀ with regs := Function.update st₀.regs prActTop restAct.length }
  apply runs_seq_assign_le (v := u)
  · exact eval_load_add_regs
      (by dsimp only [st1]; rw [Function.update_of_ne (by decide)]; exact hinv.reg_actStk)
      (by dsimp only [st1]; exact Function.update_self ..)
      (by dsimp [wActStk]; unfold pruneWorkSpace at hwb; omega)
      has_u hu_w
  set st2 : State := { st1 with regs := Function.update st1.regs prU u }
  apply runs_store_le (x := wInAct workAddr n m H + u) (v := 0)
  · exact eval_add_regs
      (by dsimp only [st2, st1]
          rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
          exact hinv.reg_inAct)
      (by dsimp only [st2]; exact Function.update_self ..)
      (by dsimp [wInAct]; unfold pruneWorkSpace at hwb; omega)
  · exact by simp [Expr.eval, h0lt]
  · set stF : State := { st2 with mem := Function.update st₀.mem (wInAct workAddr n m H + u) 0 }
    have hF_regs_notAT : ∀ r, r ≤ prCsrAdjH → r ≠ prActTop → stF.regs r = st₀.regs r := by
      intro r hr hat
      dsimp only [stF, st2, st1]
      rw [Function.update_of_ne (by dsimp only [prCsrAdjH, prU] at *; omega),
        Function.update_of_ne hat]
    have hF_regs : ∀ r, r ≤ prCsrAdjH → r ≠ prActTop → r ≠ prPeelTop → stF.regs r = st₀.regs r :=
      fun r hr hat _ => hF_regs_notAT r hr hat
    have hmf : MemFrame st₀.mem stF.mem (wInAct workAddr n m H) (wActStk workAddr n m H) :=
      memFrame_update_in (by dsimp [wInAct]; omega) (by dsimp [wInAct, wActStk]; omega)
    have hpr : PreservedOutside2 st₀.mem stF.mem outRAddr (outRAddr + n)
        (wHArr workAddr n m H) (workAddr + pruneWorkSpace n m H) :=
      memFrame_to_preserved2_right hmf (by dsimp [wHArr, wInAct]; omega)
        (by unfold pruneWorkSpace; dsimp [wActStk]; omega)
    obtain ⟨hG_F, hCsr_F, hinB_F, hdegX_F⟩ := static_of_preserved2 hinv hdisj hpr
    obtain ⟨hlvlH, hlvlEq, hbnd, hbmem, hbdl⟩ := buckets_preserved_of_mem_agree s' stF hinv rfl rfl (fun k hk1 hk2 => by
      dsimp only [n, m, H] at *
      exact hmf k (Or.inr (by dsimp [wActStk, wLvlNext] at hk1 ⊢; omega)))
    have hstep_inv := (popInactiveStep_inv_pot_pub hinv.prune_inv hact hdead).1
    have hstep_pq := peelQInv_of_fields hinv.peelQ_inv rfl rfl
    refine ⟨hF_regs, rfl, hpr,
      { cfg_X := hinv.cfg_X
        cfg_valid := hinv.cfg_valid
        reg_g := (hF_regs prG (by decide) (by decide) (by decide)).trans hinv.reg_g
        reg_csr := (hF_regs prCsr (by decide) (by decide) (by decide)).trans hinv.reg_csr
        reg_inB := (hF_regs prInB (by decide) (by decide) (by decide)).trans hinv.reg_inB
        reg_outR := (hF_regs prOutR (by decide) (by decide) (by decide)).trans hinv.reg_outR
        reg_work := (hF_regs prWork (by decide) (by decide) (by decide)).trans hinv.reg_work
        reg_ccap := (hF_regs prCcap (by decide) (by decide) (by decide)).trans hinv.reg_ccap
        reg_H := (hF_regs prH (by decide) (by decide) (by decide)).trans hinv.reg_H
        reg_theta := (hF_regs prTheta (by decide) (by decide) (by decide)).trans hinv.reg_theta
        reg_n := (hF_regs prN (by decide) (by decide) (by decide)).trans hinv.reg_n
        reg_m := (hF_regs prM (by decide) (by decide) (by decide)).trans hinv.reg_m
        reg_actTop := by
          dsimp only [stF, st2, st1, s', popInactiveStep]
          rw [Function.update_of_ne (by decide), Function.update_self]
        reg_peelTop := (hF_regs_notAT prPeelTop (by decide) (by decide)).trans hinv.reg_peelTop
        reg_degX := (hF_regs prDegX (by decide) (by decide) (by decide)).trans hinv.reg_degX
        reg_hArr := (hF_regs prHArr (by decide) (by decide) (by decide)).trans hinv.reg_hArr
        reg_cur := (hF_regs prCur (by decide) (by decide) (by decide)).trans hinv.reg_cur
        reg_abs := (hF_regs prAbs (by decide) (by decide) (by decide)).trans hinv.reg_abs
        reg_ex := (hF_regs prEx (by decide) (by decide) (by decide)).trans hinv.reg_ex
        reg_degR := (hF_regs prDegR (by decide) (by decide) (by decide)).trans hinv.reg_degR
        reg_inAct := (hF_regs prInAct (by decide) (by decide) (by decide)).trans hinv.reg_inAct
        reg_actStk := (hF_regs prActStk (by decide) (by decide) (by decide)).trans hinv.reg_actStk
        reg_peelStk := (hF_regs prPeelStk (by decide) (by decide) (by decide)).trans hinv.reg_peelStk
        reg_lvlNext := (hF_regs prLvlNext (by decide) (by decide) (by decide)).trans hinv.reg_lvlNext
        reg_lvlPrev := (hF_regs prLvlPrev (by decide) (by decide) (by decide)).trans hinv.reg_lvlPrev
        reg_remArr := (hF_regs prRemArr (by decide) (by decide) (by decide)).trans hinv.reg_remArr
        reg_flowEnc := (hF_regs prFlowEnc (by decide) (by decide) (by decide)).trans hinv.reg_flowEnc
        reg_lvlVol := (hF_regs prLvlVol (by decide) (by decide) (by decide)).trans hinv.reg_lvlVol
        reg_lvlHead := (hF_regs prLvlHead (by decide) (by decide) (by decide)).trans hinv.reg_lvlHead
        reg_adjV := (hF_regs prCsrAdjV (by decide) (by decide) (by decide)).trans hinv.reg_adjV
        reg_adjH := (hF_regs prCsrAdjH (by decide) (by decide) (by decide)).trans hinv.reg_adjH
        graph_at := hG_F
        csr_at := hCsr_F
        inB_eq := hinB_F
        outR_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (outRAddr + x) (by
            have hdw := hdisj.2.2.2.2.2.2
            unfold pruneWorkSpace at hdw
            rcases hdw with h | h <;> dsimp [wInAct, wActStk]
            · left; omega
            · right; omega)]
          exact hinv.outR_eq x hx
        degX_eq := hdegX_F
        h_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (wHArr workAddr n m H + x) (Or.inl (by dsimp [wHArr, wInAct]; omega))]
          exact hinv.h_eq x hx
        cur_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (wCur workAddr n m H + x) (Or.inl (by dsimp [wCur, wInAct]; omega))]
          exact hinv.cur_eq x hx
        abs_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (wAbs workAddr n m H + x) (Or.inl (by dsimp [wAbs, wInAct]; omega))]
          exact hinv.abs_eq x hx
        ex_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (wEx workAddr n m H + x) (Or.inl (by dsimp [wEx, wInAct]; omega))]
          exact hinv.ex_eq x hx
        degR_eq := fun x hx => by
          dsimp only [n, m, H] at *
          rw [hmf (wDegR workAddr n m H + x) (Or.inl (by dsimp [wDegR, wInAct]; omega))]
          exact hinv.degR_eq x hx
        inAct_eq := fun x hx => by
          dsimp only [stF, s', popInactiveStep, n, m, H] at *
          by_cases hxu : x = u
          · subst hxu; simp [Function.update_self]
          · rw [Function.update_of_ne (by omega), hinv.inAct_eq x hx]; simp [hxu]
        actStk_eq := fun i hi => by
          dsimp only [s', popInactiveStep, n, m, H] at hi ⊢
          rw [hmf (wActStk workAddr n m H + i) (Or.inr (by dsimp [wActStk]; omega))]
          have hi1 : i < s.active.length := by rw [hact, List.length_cons]; omega
          rw [hinv.actStk_eq i hi1, hact]
          have hidx : (u :: restAct).length - 1 - i = (restAct.length - 1 - i) + 1 := by simp; omega
          rw [hidx]; rfl
        peelStk_eq := fun i hi => by
          dsimp only [n, m, H] at *
          rw [hmf (wPeelStk workAddr n m H + i) (Or.inr (by dsimp [wActStk, wPeelStk]; omega))]
          exact hinv.peelStk_eq i hi
        flowEnc_eq := fun idx hidx => by
          dsimp only [n, m, H] at *
          rw [hmf (wFlowEnc workAddr n m H + idx) (Or.inr (by dsimp [wActStk, wFlowEnc]; omega))]
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
