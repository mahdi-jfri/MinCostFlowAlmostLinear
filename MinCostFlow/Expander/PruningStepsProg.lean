module

public import MinCostFlow.Expander.PruningAdmProg

/-!
# Top-Level Single Prune Step Triple (pruneStep_triple)
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

theorem pruneStep_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} (st₀ : State)
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (hne : s.peelQ ≠ [] ∨ s.active ≠ [])
    (hθ : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d < cfg.θ_out_nat, 3 * d ≤ cfg.degX x)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w) :
    ∃ (T_step : ℕ),
      Triple w p (fun st => st = st₀) pruneStepStmt
        (normalPost fun st' =>
          ∃ s' buckets',
            (∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
            st'.pos = st₀.pos ∧
            PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
              (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
            PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s' buckets' st' ∧
            s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
            pot cfg s' < pot cfg s ∧
            volPminusB cfg s' + 2 * cfg.C_cap * cutPR cfg s' ≤
              volPminusB cfg s + 2 * cfg.C_cap * cutPR cfg s ∧
            T_step ≤ 350 * (pot cfg s - pot cfg s'))
        (fun _ => T_step) := by
  have hwb := pruneWordBound_pos hw
  have hlt2w : ∀ k, k < workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H → k < 2 ^ w := fun k hk => by
    unfold PruneWordBound at hw; omega
  have htop_cond : Expr.eval w st₀ (.bin .lt (.const 0) (.reg prPeelTop)) =
      some (if 0 < s.peelQ.length then 1 else 0) :=
    Expr.eval_bin (op := .lt) (Expr.eval_const (by omega)) (eval_reg_eq w st₀ prPeelTop hinv.reg_peelTop)
      (by dsimp only [BinOp.eval]; split_ifs <;> omega)
  cases hpq : s.peelQ with
  | cons v rest =>
    let s' := peelStep cfg v rest s
    let cond := s.inR v && decide (s.degR v < cfg.θ_out_nat)
    let buckets' : ℕ → List ℕ :=
      if cond = true ∧ 1 ≤ s.h v then
        fun ℓ => if ℓ = s.h v then (buckets ℓ).erase v else buckets ℓ
      else buckets
    have hpot := peelStep_inv_pot_pub hinv.cfg_valid hinv.prune_inv hpq hθ
    have hpeel := peelStep_triple (p := p) st₀ hinv hpq hθ hw hdisj hcsr_w houtR_w
    have hsteps_ge : 1 ≤ s'.steps - s.steps := by
      dsimp [s', peelStep]; split_ifs <;> dsimp only <;> omega
    refine ⟨3 + 180 * (s'.steps - s.steps) + 1, ?_⟩
    intro st ω hst
    subst st
    rcases hpeel st₀ ω rfl with ⟨o', st', c', hr', hq', hc'⟩
    cases o' with
    | returned => exact False.elim hq'
    | normal =>
      rcases hq' with ⟨hreg', hpos', hpr', hinv'⟩
      refine ⟨.normal, st', 3 + c' + 1, runs_cond_iff.mpr ⟨1, c', ?_, ?_, by simp [Expr.size]⟩,
        ⟨s', buckets', hreg', hpos', hpr', hinv', hpot.2.1, hpot.2.2.1, hpot.2.2.2, ?_⟩,
        by dsimp only [s'] at *; omega⟩
      · simpa [hpq] using htop_cond
      · simpa [hpq] using hr'
      · dsimp only [s'] at *; omega
  | nil =>
    have hact_ne : s.active ≠ [] := by rcases hne with h | h <;> [simp [hpq] at h; exact h]
    cases hact : s.active with
    | nil => exact absurd hact hact_ne
    | cons u restAct =>
      have huN : u < cfg.G.n := by
        have := hinv.prune_inv.active_sub u (hact ▸ List.mem_cons_self)
        rw [hinv.cfg_X] at this; exact Finset.mem_range.mp this
      have hact_len_pos : 0 < s.active.length := by rw [hact]; simp
      have hact_m1 : s.active.length - 1 = restAct.length := by rw [hact]; simp
      have hstk_u : st₀.mem (wActStk workAddr cfg.G.n cfg.G.m cfg.H + (s.active.length - 1)) = u := by
        rw [hinv.actStk_eq _ (by omega), hact_m1, hact]; simp
      have hat_lt2w : s.active.length < 2 ^ w := by
        have := hinv.active_len_le; unfold PruneWordBound at hw; omega
      have hstk_addr : wActStk workAddr cfg.G.n cfg.G.m cfg.H + (s.active.length - 1) < 2 ^ w := by
        have := hinv.active_len_le
        exact hlt2w _ (by unfold pruneWorkSpace; dsimp [wActStk]; omega)
      let r1 := Function.update st₀.regs prU u
      let st1 : State := { mem := st₀.mem, regs := r1, pos := st₀.pos }
      let v1 := if s.inR u = true then 1 else 0
      let r2 := Function.update r1 prTmp1 v1
      let st2 : State := { mem := st₀.mem, regs := r2, pos := st₀.pos }
      let v2 := s.ex u
      let r3 := Function.update r2 prTmp2 v2
      let st3 : State := { mem := st₀.mem, regs := r3, pos := st₀.pos }
      have hex_u_le : v2 ≤ 4 * cfg.C_cap * cfg.G.m := hinv.ex_bound u huN
      have hex_u_lt2w : v2 < 2 ^ w := by
        have hle8 : 4 * cfg.C_cap * cfg.G.m ≤ 8 * cfg.C_cap * cfg.G.m :=
          Nat.mul_le_mul_right cfg.G.m (by omega)
        unfold PruneWordBound at hw; omega
      have hmul_v12_lt2w : v1 * v2 < 2 ^ w := by
        have hle_v2 : v1 * v2 ≤ v2 := by dsimp [v1]; split_ifs <;> simp
        exact lt_of_le_of_lt hle_v2 hex_u_lt2w
      have mk_dispatch_pre : ∀ (stx : State),
          stx.mem = st₀.mem → stx.pos = st₀.pos →
          (∀ r ≤ prCsrAdjH, stx.regs r = st₀.regs r) →
          PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets stx :=
        fun stx hm _ hr =>
          pruneMemInv_of_regs_agree hinv hdisj (fun r hr0 _ _ => hr r hr0)
            (hr prActTop (by decide)) (hr prPeelTop (by decide)) hm
      have build_prefix : ∀ ω,
          Runs w p ω (seqStmts
            [ .assign prU (.load (.bin .add (.reg prActStk) (.bin .sub (.reg prActTop) (.const 1))))
            , .assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prU)))
            , .assign prTmp2 (.load (.bin .add (.reg prEx) (.reg prU))) ]) st₀ .normal st3 19 := by
        intro ω
        have hs1 : Runs w p ω
            (.assign prU (.load (.bin .add (.reg prActStk) (.bin .sub (.reg prActTop) (.const 1)))))
            st₀ .normal st1 7 := by
          refine runs_assign_iff.mpr ⟨u, ?_, rfl, rfl, by simp [Expr.size]⟩
          have hev1 := Expr.eval_load (st := st₀)
            (Expr.eval_bin (op := .add) (eval_reg_eq w st₀ prActStk hinv.reg_actStk)
              (Expr.eval_bin (op := .sub) (eval_reg_eq w st₀ prActTop hinv.reg_actTop)
                (Expr.eval_const (k := 1) (by omega)) (by dsimp only [BinOp.eval]; omega))
              (by dsimp only [BinOp.eval]; exact hstk_addr))
          dsimp only [BinOp.eval] at hev1; rw [hstk_u] at hev1; exact hev1
        have hr1_or : st1.regs prOutR = outRAddr := by
          dsimp [st1, r1]; rw [Function.update_of_ne (by decide)]; exact hinv.reg_outR
        have hr1_u : st1.regs prU = u := by dsimp [st1, r1]; rw [Function.update_self]
        have hs2 : Runs w p ω (.assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prU))))
            st1 .normal st2 5 :=
          runs_assign_iff.mpr ⟨v1,
            eval_load_add_eq w st1 prOutR prU hr1_or hr1_u (by omega) (hinv.outR_eq u huN),
            rfl, rfl, by simp [Expr.size]⟩
        have hr2_ex : st2.regs prEx = wEx workAddr cfg.G.n cfg.G.m cfg.H := by
          dsimp [st2, r2, r1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
          exact hinv.reg_ex
        have hr2_u : st2.regs prU = u := by
          dsimp [st2, r2, r1]; rw [Function.update_of_ne (by decide), Function.update_self]
        have hs3 : Runs w p ω (.assign prTmp2 (.load (.bin .add (.reg prEx) (.reg prU))))
            st2 .normal st3 5 :=
          runs_assign_iff.mpr ⟨v2,
            eval_load_add_eq w st2 prEx prU hr2_ex hr2_u
              (hlt2w _ (by unfold pruneWorkSpace; dsimp [wEx]; omega)) (hinv.ex_eq u huN),
            rfl, rfl, by simp [Expr.size]⟩
        exact runs_seq hs1 (runs_seq hs2 hs3)
      have hcond_dead : Expr.eval w st3 (.bin .eq (.bin .mul (.reg prTmp1) (.reg prTmp2)) (.const 0)) =
          some (if s.inR u = false ∨ s.ex u = 0 then 1 else 0) := by
        have hr3_t1 : st3.regs prTmp1 = v1 := by
          dsimp [st3, r3, r2]; rw [Function.update_of_ne (by decide), Function.update_self]
        have hr3_t2 : st3.regs prTmp2 = v2 := by dsimp [st3, r3]; rw [Function.update_self]
        have hev : Expr.eval w st3 (.bin .eq (.bin .mul (.reg prTmp1) (.reg prTmp2)) (.const 0)) =
            some (if v1 * v2 = 0 then 1 else 0) :=
          Expr.eval_bin (op := .eq)
            (Expr.eval_bin (op := .mul) (eval_reg_eq w st3 prTmp1 hr3_t1)
              (eval_reg_eq w st3 prTmp2 hr3_t2) (by dsimp only [BinOp.eval]; exact hmul_v12_lt2w))
            (Expr.eval_const (k := 0) (by omega)) (by dsimp only [BinOp.eval]; split_ifs <;> omega)
        convert hev using 2
        dsimp only [v1, v2]
        by_cases huR : s.inR u = true <;> by_cases hex0 : s.ex u = 0 <;> simp [huR, hex0]
      have hr3_le : ∀ r ≤ prCsrAdjH, st3.regs r = st₀.regs r := fun r hr => by
        dsimp [st3, r3, r2, r1, prCsrAdjH, prU, prTmp1, prTmp2] at hr ⊢
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      by_cases hdead : s.inR u = false ∨ s.ex u = 0
      · let s' := popInactiveStep u restAct s
        have hpot := popInactiveStep_inv_pot_pub hinv.prune_inv hact hdead
        have hs'_st : s'.steps + pot cfg s' ≤ s.steps + pot cfg s := hpot.2.1
        have hs'_lt : pot cfg s' < pot cfg s := hpot.2.2.1
        have hinv3 := mk_dispatch_pre st3 rfl rfl hr3_le
        have hpop := popInactiveStep_triple (p := p) st3 hinv3 hact hdead hw hdisj
        refine ⟨60, ?_⟩
        intro st ω hst; subst st
        rcases hpop st3 ω rfl with ⟨o', st', c', hr', hq', hc'⟩
        cases o' with
        | returned => exact False.elim hq'
        | normal =>
          rcases hq' with ⟨hreg', hpos', hpr', hinv'⟩
          have hreg_fin : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r :=
            fun r hr h1 h2 => (hreg' r hr h1 h2).trans (hr3_le r hr)
          have hrun : Runs w p ω pruneStepStmt st₀ .normal st' (3 + (19 + (5 + c' + 1) + 1) + 1) := by
            refine runs_cond_iff.mpr ⟨0, (19 + (5 + c' + 1) + 1),
              by simpa [hpq] using htop_cond, ?_, by simp [Expr.size]⟩
            simp only [↓reduceIte]
            refine runs_seq3 (build_prefix ω)
              (runs_cond_iff.mpr ⟨1, c', by simpa [hdead] using hcond_dead, ?_, by simp [Expr.size]⟩)
            simp only [Nat.one_ne_zero, ↓reduceIte]; exact hr'
          refine ⟨.normal, st', _, hrun,
            ⟨s', buckets, hreg_fin, hpos', hpr', hinv', hs'_st, hs'_lt,
              by rw [hpot.2.2.2.1, hpot.2.2.2.2], by omega⟩, by dsimp only at hc' ⊢; omega⟩
      · have huR : s.inR u = true := Bool.eq_true_of_not_eq_false (fun h => hdead (Or.inl h))
        have hexPos : 0 < s.ex u := Nat.pos_of_ne_zero (fun h => hdead (Or.inr h))
        have habs_le : s.abs u ≤ cfg.degX u := hinv.prune_inv.abs_le u huR
        have hdegX_lt2w : cfg.degX u < 2 ^ w := by
          have := hinv.degX_le_two_mul_m huN; unfold PruneWordBound at hw; omega
        have habs_lt2w : s.abs u < 2 ^ w := by omega
        let r4 := Function.update r3 prTmp1 (s.abs u)
        let st4 : State := { mem := st₀.mem, regs := r4, pos := st₀.pos }
        let r5 := Function.update r4 prTmp2 (cfg.degX u)
        let st5 : State := { mem := st₀.mem, regs := r5, pos := st₀.pos }
        have hr3_abs : st3.regs prAbs = wAbs workAddr cfg.G.n cfg.G.m cfg.H := by
          rw [hr3_le prAbs (by decide)]; exact hinv.reg_abs
        have hr3_u : st3.regs prU = u := by
          dsimp [st3, r3, r2, r1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
        have hr4_dx : st4.regs prDegX = wDegX workAddr cfg.G.n cfg.G.m cfg.H := by
          dsimp [st4, r4]; rw [Function.update_of_ne (by decide)]; exact (hr3_le prDegX (by decide)).trans hinv.reg_degX
        have hr4_u : st4.regs prU = u := by
          dsimp [st4, r4]; rw [Function.update_of_ne (by decide)]; exact hr3_u
        have hmid_abs : ∀ ω, Runs w p ω (seqStmts
            [ .assign prTmp1 (.load (.bin .add (.reg prAbs) (.reg prU)))
            , .assign prTmp2 (.load (.bin .add (.reg prDegX) (.reg prU))) ]) st3 .normal st5 11 := fun ω => by
          have ha1 : Runs w p ω (.assign prTmp1 (.load (.bin .add (.reg prAbs) (.reg prU)))) st3 .normal st4 5 :=
            runs_assign_iff.mpr ⟨s.abs u,
              eval_load_add_eq w st3 prAbs prU hr3_abs hr3_u
                (hlt2w _ (by unfold pruneWorkSpace; dsimp [wAbs]; omega)) (hinv.abs_eq u huN),
              rfl, rfl, by simp [Expr.size]⟩
          have ha2 : Runs w p ω (.assign prTmp2 (.load (.bin .add (.reg prDegX) (.reg prU)))) st4 .normal st5 5 :=
            runs_assign_iff.mpr ⟨cfg.degX u,
              eval_load_add_eq w st4 prDegX prU hr4_dx hr4_u
                (hlt2w _ (by unfold pruneWorkSpace; dsimp [wDegX]; omega)) (hinv.degX_eq u huN),
              rfl, rfl, by simp [Expr.size]⟩
          exact runs_seq ha1 ha2
        have hcond_abs : Expr.eval w st5 (.bin .lt (.reg prTmp1) (.reg prTmp2)) =
            some (if s.abs u < cfg.degX u then 1 else 0) :=
          Expr.eval_bin (op := .lt)
            (eval_reg_eq w st5 prTmp1 (by dsimp [st5, r5, r4]; rw [Function.update_of_ne (by decide), Function.update_self]))
            (eval_reg_eq w st5 prTmp2 (by dsimp [st5, r5]; rw [Function.update_self]))
            (by dsimp only [BinOp.eval]; split_ifs <;> omega)
        have hr5_le : ∀ r ≤ prCsrAdjH, st5.regs r = st₀.regs r := fun r hr => by
          dsimp [st5, r5, r4, prCsrAdjH, prTmp1, prTmp2] at hr ⊢
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hr3_le r hr
        have hr5_u : st5.regs prU = u := by
          dsimp [st5, r5, r4]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr3_u
        by_cases habs_lt : s.abs u < cfg.degX u
        · let s' := absorbStep cfg u s
          have hpot := absorbStep_inv_pot_pub hinv.prune_inv huR hexPos habs_lt
          have hs'_st : s'.steps + pot cfg s' ≤ s.steps + pot cfg s := hpot.2.1
          have hs'_lt : pot cfg s' < pot cfg s := hpot.2.2.1
          have hinv5 := mk_dispatch_pre st5 rfl rfl hr5_le
          have hab := absorbStep_triple (p := p) st5 hinv5 huR hexPos habs_lt hw hdisj
          refine ⟨101, ?_⟩
          intro st ω hst; subst st
          rcases hab st5 ω ⟨rfl, hr5_u⟩ with ⟨o', st', c', hr', hq', hc'⟩
          cases o' with
          | returned => exact False.elim hq'
          | normal =>
            rcases hq' with ⟨hreg', hpos', hpr', hinv'⟩
            have hreg_fin : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r :=
              fun r hr h1 h2 => (hreg' r hr h1 h2).trans (hr5_le r hr)
            have hrun : Runs w p ω pruneStepStmt st₀ .normal st'
                (3 + (19 + (5 + (11 + (3 + c' + 1) + 1) + 1) + 1) + 1) := by
              refine runs_cond_iff.mpr ⟨0, (19 + (5 + (11 + (3 + c' + 1) + 1) + 1) + 1),
                by simpa [hpq] using htop_cond, ?_, by simp [Expr.size]⟩
              simp only [↓reduceIte]
              refine runs_seq3 (build_prefix ω)
                (runs_cond_iff.mpr ⟨0, (11 + (3 + c' + 1) + 1),
                  by simpa [hdead] using hcond_dead, ?_, by simp [Expr.size]⟩)
              simp only [↓reduceIte]
              refine runs_seq2 (hmid_abs ω)
                (runs_cond_iff.mpr ⟨1, c', by simpa [habs_lt] using hcond_abs, ?_, by simp [Expr.size]⟩)
              simp only [Nat.one_ne_zero, ↓reduceIte]; exact hr'
            refine ⟨.normal, st', _, hrun,
              ⟨s', buckets, hreg_fin, hpos', hpr', hinv', hs'_st, hs'_lt,
                by rw [hpot.2.2.2.1, hpot.2.2.2.2], by omega⟩, by dsimp only at hc' ⊢; omega⟩
        · have habs_eq : s.abs u = cfg.degX u := by omega
          have hinc_eq : (cfg.incEdges u).length = csrOff cfg.G (u + 1) - csrOff cfg.G u := by
            have := csrOff_succ cfg.G u; rw [← hinv.cfg_incEdges u] at this; omega
          have hcur_le : s.cur u ≤ (cfg.incEdges u).length := hinv.prune_inv.cur_le u huR
          have hcur_lt2w : s.cur u < 2 ^ w := by
            have := csrOff_le_two_mul_m cfg.G (u + 1); rw [csrOff_succ, ← hinv.cfg_incEdges u] at this
            unfold PruneWordBound at hw; omega
          have hoff_lt2w : csrOff cfg.G u ≤ csrOff cfg.G (u + 1) ∧ csrOff cfg.G (u + 1) ≤ 2 * cfg.G.m :=
            ⟨by rw [csrOff_succ]; omega, csrOff_le_two_mul_m cfg.G (u + 1)⟩
          have hoff_w : csrOff cfg.G u < 2 ^ w ∧ csrOff cfg.G (u + 1) < 2 ^ w := by
            unfold PruneWordBound at hw; omega
          let r6 := Function.update r5 prTmp1 (s.cur u)
          let st6 : State := { mem := st₀.mem, regs := r6, pos := st₀.pos }
          let r7 := Function.update r6 prStart (csrOff cfg.G u)
          let st7 : State := { mem := st₀.mem, regs := r7, pos := st₀.pos }
          let r8 := Function.update r7 prEnd (csrOff cfg.G (u + 1))
          let st8 : State := { mem := st₀.mem, regs := r8, pos := st₀.pos }
          let r9 := Function.update r8 prTmp2 (cfg.incEdges u).length
          let st9 : State := { mem := st₀.mem, regs := r9, pos := st₀.pos }
          have hcur_prefix : ∀ ω, Runs w p ω (seqStmts
              [ .assign prTmp1 (.load (.bin .add (.reg prCur) (.reg prU)))
              , .assign prStart (.load (.bin .add (.reg prCsr) (.reg prU)))
              , .assign prEnd (.load (.bin .add (.reg prCsr) (.bin .add (.reg prU) (.const 1))))
              , .assign prTmp2 (.bin .sub (.reg prEnd) (.reg prStart)) ]) st5 .normal st9 24 := by
            intro ω
            have hs6 : Runs w p ω (.assign prTmp1 (.load (.bin .add (.reg prCur) (.reg prU)))) st5 .normal st6 5 :=
              runs_assign_iff.mpr ⟨s.cur u,
                eval_load_add_eq w st5 prCur prU (by rw [hr5_le prCur (by decide)]; exact hinv.reg_cur)
                  hr5_u (hlt2w _ (by unfold pruneWorkSpace; dsimp [wCur]; omega)) (hinv.cur_eq u huN),
                rfl, rfl, by simp [Expr.size]⟩
            have hr6_csr : st6.regs prCsr = csrAddr := by
              dsimp [st6, r6]; rw [Function.update_of_ne (by decide)]; exact (hr5_le prCsr (by decide)).trans hinv.reg_csr
            have hr6_u : st6.regs prU = u := by dsimp [st6, r6]; rw [Function.update_of_ne (by decide)]; exact hr5_u
            have hs7 : Runs w p ω (.assign prStart (.load (.bin .add (.reg prCsr) (.reg prU)))) st6 .normal st7 5 :=
              runs_assign_iff.mpr ⟨csrOff cfg.G u,
                eval_load_add_eq w st6 prCsr prU hr6_csr hr6_u (by omega) (hinv.csr_at.1 u (by omega)),
                rfl, rfl, by simp [Expr.size]⟩
            have hr7_csr : st7.regs prCsr = csrAddr := by
              dsimp [st7, r7]; rw [Function.update_of_ne (by decide)]; exact hr6_csr
            have hr7_u : st7.regs prU = u := by dsimp [st7, r7]; rw [Function.update_of_ne (by decide)]; exact hr6_u
            have hs8 : Runs w p ω (.assign prEnd (.load (.bin .add (.reg prCsr) (.bin .add (.reg prU) (.const 1)))))
                st7 .normal st8 7 := by
              refine runs_assign_iff.mpr ⟨csrOff cfg.G (u + 1), ?_, rfl, rfl, by simp [Expr.size]⟩
              have hev8 := Expr.eval_load (st := st7)
                (Expr.eval_bin (op := .add) (eval_reg_eq w st7 prCsr hr7_csr)
                  (Expr.eval_bin (op := .add) (eval_reg_eq w st7 prU hr7_u) (Expr.eval_const (k := 1) (by omega))
                    (by dsimp only [BinOp.eval]; unfold PruneWordBound at hw; omega))
                  (by dsimp only [BinOp.eval]; omega))
              dsimp only [BinOp.eval, st7] at hev8
              rw [hinv.csr_at.1 (u + 1) (by omega)] at hev8
              exact hev8
            have hr8_end : st8.regs prEnd = csrOff cfg.G (u + 1) := by dsimp [st8, r8]; rw [Function.update_self]
            have hr8_st : st8.regs prStart = csrOff cfg.G u := by
              dsimp [st8, r8, r7]; rw [Function.update_of_ne (by decide), Function.update_self]
            have hs9 : Runs w p ω (.assign prTmp2 (.bin .sub (.reg prEnd) (.reg prStart))) st8 .normal st9 4 := by
              refine runs_assign_iff.mpr ⟨(cfg.incEdges u).length, ?_, rfl, rfl, by simp [Expr.size]⟩
              have hev9 := Expr.eval_bin (op := .sub) (eval_reg_eq w st8 prEnd hr8_end) (eval_reg_eq w st8 prStart hr8_st)
                (by dsimp only [BinOp.eval]; rw [← hinc_eq]; unfold PruneWordBound at hw; omega)
              dsimp only [BinOp.eval] at hev9
              rw [← hinc_eq] at hev9
              exact hev9
            exact runs_seq hs6 (runs_seq hs7 (runs_seq hs8 hs9))
          have hr9_t1 : st9.regs prTmp1 = s.cur u := by
            dsimp [st9, r9, r8, r7, r6]
            rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
              Function.update_of_ne (by decide), Function.update_self]
          have hr9_t2 : st9.regs prTmp2 = (cfg.incEdges u).length := by dsimp [st9, r9]; rw [Function.update_self]
          have hcond_cur : Expr.eval w st9 (.bin .lt (.reg prTmp1) (.reg prTmp2)) =
              some (if s.cur u < (cfg.incEdges u).length then 1 else 0) :=
            Expr.eval_bin (op := .lt) (eval_reg_eq w st9 prTmp1 hr9_t1) (eval_reg_eq w st9 prTmp2 hr9_t2)
              (by dsimp only [BinOp.eval]; split_ifs <;> omega)
          have hr9_le : ∀ r ≤ prCsrAdjH, st9.regs r = st₀.regs r := fun r hr => by
            dsimp [st9, r9, r8, r7, r6, prCsrAdjH, prTmp1, prTmp2, prStart, prEnd] at hr ⊢
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hr5_le r hr
          have hr9_u : st9.regs prU = u := by
            dsimp [st9, r9, r8, r7, r6]
            rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
              Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr5_u
          by_cases hcur_lt : s.cur u < (cfg.incEdges u).length
          · have hr9_st : st9.regs prStart = csrOff cfg.G u := by
              dsimp [st9, r9, r8, r7]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
            obtain ⟨st25, c_adm, hc_adm, hm25, hp25, hr25_le, hr25_u, hr25_t1, hrun_adm⟩ :=
              pruneStep_adm_check (p := p) (st9 := st9) hinv huN huR hcur_lt hw hcsr_w houtR_w
                rfl rfl hr9_le hr9_u hr9_t1 hr9_st
            let q := (cfg.incEdges u).getD (s.cur u) (0, false, 0)
            have hcond_adm : Expr.eval w st25 (.bin .eq (.reg prTmp1) (.const 1)) =
                some (if (s.inR q.2.2 && decide (flowDir s.flow q.1 q.2.1 < ↑cfg.C_cap) &&
                    decide (s.h u = s.h q.2.2 + 1)) = true then 1 else 0) := by
              have hev := Expr.eval_bin (op := .eq) (eval_reg_eq w st25 prTmp1 hr25_t1)
                (Expr.eval_const (k := 1) (by omega)) (by dsimp only [BinOp.eval]; split_ifs <;> omega)
              convert hev using 2
              split_ifs <;> simp [BinOp.eval]
            have hinv25 := mk_dispatch_pre st25 hm25 hp25 hr25_le
            by_cases hadm_b : (s.inR q.2.2 && decide (flowDir s.flow q.1 q.2.1 < ↑cfg.C_cap) &&
                decide (s.h u = s.h q.2.2 + 1)) = true
            · have hadm' : have p := (cfg.incEdges u).getD (s.cur u) (0, false, 0);
                  s.inR p.2.2 = true ∧ flowDir s.flow p.1 p.2.1 < ↑cfg.C_cap ∧ s.h u = s.h p.2.2 + 1 := by
                simpa only [q, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hadm_b
              let s' := pushFlowStep cfg u restAct s
              have hpot := pushFlowStep_inv_pot_pub hinv.cfg_valid hinv.prune_inv hact huR hexPos habs_eq hcur_lt hadm'
              have hs'_st : s'.steps + pot cfg s' ≤ s.steps + pot cfg s := hpot.2.1
              have hs'_lt : pot cfg s' < pot cfg s := hpot.2.2.1
              have hpf := pushFlowStep_triple (p := p) st25 hinv25 hact huR hexPos habs_eq hcur_lt hadm' hw hdisj hcsr_w
              refine ⟨345, ?_⟩
              intro st ω hst; subst st
              rcases hpf st25 ω ⟨rfl, hr25_u⟩ with ⟨o', st', c', hr', hq', hc'⟩
              cases o' with
              | returned => exact False.elim hq'
              | normal =>
                rcases hq' with ⟨hreg', hpos', hpr', hinv'⟩
                have hreg_fin : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r :=
                  fun r hr h1 h2 => (hreg' r hr h1 h2).trans (hr25_le r hr)
                have hpos'_0 : st'.pos = st₀.pos := hpos'.trans hp25
                have hpr'_0 : PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
                    (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) := by
                  intro x hx1 hx2; rw [hpr' x hx1 hx2, hm25]
                have hrun : Runs w p ω pruneStepStmt st₀ .normal st'
                    (3 + (19 + (5 + (11 + (3 + (24 + (3 + (c_adm + (3 + c' + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
                  refine runs_cond_iff.mpr
                    ⟨0, (19 + (5 + (11 + (3 + (24 + (3 + (c_adm + (3 + c' + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                      by simpa [hpq] using htop_cond, ?_, by simp [Expr.size]⟩
                  simp only [↓reduceIte]
                  refine runs_seq3 (build_prefix ω)
                    (runs_cond_iff.mpr
                      ⟨0, (11 + (3 + (24 + (3 + (c_adm + (3 + c' + 1) + 1) + 1) + 1) + 1) + 1),
                        by simpa [hdead] using hcond_dead, ?_, by simp [Expr.size]⟩)
                  simp only [↓reduceIte]
                  refine runs_seq2 (hmid_abs ω)
                    (runs_cond_iff.mpr
                      ⟨0, (24 + (3 + (c_adm + (3 + c' + 1) + 1) + 1) + 1),
                        by simpa [habs_lt] using hcond_abs, ?_, by simp [Expr.size]⟩)
                  simp only [↓reduceIte]
                  refine runs_seq4 (hcur_prefix ω)
                    (runs_cond_iff.mpr
                      ⟨1, (c_adm + (3 + c' + 1) + 1),
                        by simpa [hcur_lt] using hcond_cur, ?_, by simp [Expr.size]⟩)
                  simp only [Nat.one_ne_zero, ↓reduceIte]
                  have htail : Runs w p ω (.cond (.bin .eq (.reg prTmp1) (.const 1)) pushFlowStepStmt advanceCurStepStmt)
                      st25 .normal st' (3 + c' + 1) := by
                    refine runs_cond_iff.mpr ⟨1, c', by simpa [hadm_b] using hcond_adm, ?_, by simp [Expr.size]⟩
                    simp only [Nat.one_ne_zero, ↓reduceIte]; exact hr'
                  exact runs_seqStmts_append (hrun_adm ω) htail
                refine ⟨.normal, st', _, hrun,
                  ⟨s', buckets, hreg_fin, hpos'_0, hpr'_0, hinv', hs'_st, hs'_lt,
                    by rw [hpot.2.2.2.1, hpot.2.2.2.2], by omega⟩, by dsimp only at hc' ⊢; omega⟩
            · have hnotAdm_b : let q := (cfg.incEdges u).getD (s.cur u) (0, false, 0)
                  !(s.inR q.2.2 && decide (flowDir s.flow q.1 q.2.1 < ↑cfg.C_cap) &&
                    decide (s.h u = s.h q.2.2 + 1)) := by
                dsimp only; rw [Bool.eq_false_iff.mpr hadm_b]; rfl
              let s' := advanceCurStep u s
              have hpot := advanceCurStep_inv_pot_pub hinv.cfg_valid hinv.prune_inv huR habs_eq hcur_lt hnotAdm_b
              have hs'_st : s'.steps + pot cfg s' ≤ s.steps + pot cfg s := hpot.2.1
              have hs'_lt : pot cfg s' < pot cfg s := hpot.2.2.1
              have hadv := advanceCurStep_triple (p := p) st25 hinv25 huR habs_eq hcur_lt hnotAdm_b hw hdisj
              refine ⟨205, ?_⟩
              intro st ω hst; subst st
              rcases hadv st25 ω ⟨rfl, hr25_u⟩ with ⟨o', st', c', hr', hq', hc'⟩
              cases o' with
              | returned => exact False.elim hq'
              | normal =>
                rcases hq' with ⟨hreg', hpos', hpr', hinv'⟩
                have hreg_fin : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r :=
                  fun r hr h1 h2 => (hreg' r hr h1 h2).trans (hr25_le r hr)
                have hpos'_0 : st'.pos = st₀.pos := hpos'.trans hp25
                have hpr'_0 : PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
                    (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) := by
                  intro x hx1 hx2; rw [hpr' x hx1 hx2, hm25]
                have hrun : Runs w p ω pruneStepStmt st₀ .normal st'
                    (3 + (19 + (5 + (11 + (3 + (24 + (3 + (c_adm + (3 + c' + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
                  refine runs_cond_iff.mpr
                    ⟨0, (19 + (5 + (11 + (3 + (24 + (3 + (c_adm + (3 + c' + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                      by simpa [hpq] using htop_cond, ?_, by simp [Expr.size]⟩
                  simp only [↓reduceIte]
                  refine runs_seq3 (build_prefix ω)
                    (runs_cond_iff.mpr
                      ⟨0, (11 + (3 + (24 + (3 + (c_adm + (3 + c' + 1) + 1) + 1) + 1) + 1) + 1),
                        by simpa [hdead] using hcond_dead, ?_, by simp [Expr.size]⟩)
                  simp only [↓reduceIte]
                  refine runs_seq2 (hmid_abs ω)
                    (runs_cond_iff.mpr
                      ⟨0, (24 + (3 + (c_adm + (3 + c' + 1) + 1) + 1) + 1),
                        by simpa [habs_lt] using hcond_abs, ?_, by simp [Expr.size]⟩)
                  simp only [↓reduceIte]
                  refine runs_seq4 (hcur_prefix ω)
                    (runs_cond_iff.mpr
                      ⟨1, (c_adm + (3 + c' + 1) + 1),
                        by simpa [hcur_lt] using hcond_cur, ?_, by simp [Expr.size]⟩)
                  simp only [Nat.one_ne_zero, ↓reduceIte]
                  have htail : Runs w p ω (.cond (.bin .eq (.reg prTmp1) (.const 1)) pushFlowStepStmt advanceCurStepStmt)
                      st25 .normal st' (3 + c' + 1) := by
                    refine runs_cond_iff.mpr ⟨0, c', by simpa [hadm_b] using hcond_adm, ?_, by simp [Expr.size]⟩
                    simp only [↓reduceIte]; exact hr'
                  exact runs_seqStmts_append (hrun_adm ω) htail
                refine ⟨.normal, st', _, hrun,
                  ⟨s', buckets, hreg_fin, hpos'_0, hpr'_0, hinv', hs'_st, hs'_lt,
                    by rw [hpot.2.2.2.1, hpot.2.2.2.2], by omega⟩, by dsimp only at hc' ⊢; omega⟩
          · have hcur_end : s.cur u = (cfg.incEdges u).length := by omega
            let st10 : State := { mem := st₀.mem, regs := Function.update st9.regs prTmp1 (s.h u), pos := st₀.pos }
            have hr10_le : ∀ r ≤ prCsrAdjH, st10.regs r = st₀.regs r := fun r hr => by
              dsimp [st10, prCsrAdjH, prTmp1] at hr ⊢
              rw [Function.update_of_ne (by omega)]; exact hr9_le r hr
            have hr10_u : st10.regs prU = u := by dsimp [st10]; rw [Function.update_of_ne (by decide)]; exact hr9_u
            have hcond_h : Expr.eval w st10 (.bin .lt (.bin .add (.reg prTmp1) (.const 1)) (.reg prH)) =
                some (if s.h u + 1 < cfg.H then 1 else 0) :=
              Expr.eval_bin (op := .lt)
                (Expr.eval_bin (op := .add) (eval_reg_eq w st10 prTmp1 (by dsimp [st10]; rw [Function.update_self]))
                  (Expr.eval_const (by omega))
                  (by dsimp only [BinOp.eval]; have := hinv.prune_inv.h_lt_H u huR; unfold PruneWordBound at hw; omega))
                (eval_reg_eq w st10 prH (by rw [hr10_le prH (by decide)]; exact hinv.reg_H))
                (by dsimp only [BinOp.eval]; split_ifs <;> omega)
            have hinv10 := mk_dispatch_pre st10 rfl rfl hr10_le
            have hs10 : ∀ ω, Runs w p ω (.assign prTmp1 (.load (.bin .add (.reg prHArr) (.reg prU))))
                st9 .normal st10 5 := fun ω =>
              runs_assign_iff.mpr ⟨s.h u,
                eval_load_add_eq w st9 prHArr prU (by rw [hr9_le prHArr (by decide)]; exact hinv.reg_hArr)
                  hr9_u (hlt2w _ (by unfold pruneWorkSpace; dsimp [wHArr]; omega)) (hinv.h_eq u huN),
                rfl, rfl, by simp [Expr.size]⟩
            by_cases hh_lt : s.h u + 1 < cfg.H
            · let s' := relabelStep u s
              let buckets1 := if 1 ≤ s.h u then fun ℓ => if ℓ = s.h u then (buckets ℓ).erase u else buckets ℓ else buckets
              let buckets' := fun ℓ => if ℓ = s.h u + 1 then u :: buckets1 ℓ else buckets1 ℓ
              have hpot := relabelStep_inv_pot_pub hinv.cfg_valid hinv.prune_inv huR hexPos habs_eq hcur_end hh_lt
              have hs'_st : s'.steps + pot cfg s' ≤ s.steps + pot cfg s := hpot.2.1
              have hs'_lt : pot cfg s' < pot cfg s := hpot.2.2.1
              have hrel := relabelStep_triple (p := p) st10 hinv10 huR hexPos habs_eq hcur_end hh_lt hw hdisj
              refine ⟨320, ?_⟩
              intro st ω hst; subst st
              rcases hrel st10 ω ⟨rfl, hr10_u⟩ with ⟨o', st', c', hr', hq', hc'⟩
              cases o' with
              | returned => exact False.elim hq'
              | normal =>
                rcases hq' with ⟨hreg', hpos', hpr', hinv'⟩
                have hreg_fin : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r :=
                  fun r hr h1 h2 => (hreg' r hr h1 h2).trans (hr10_le r hr)
                have hrun : Runs w p ω pruneStepStmt st₀ .normal st'
                    (3 + (19 + (5 + (11 + (3 + (24 + (3 + (5 + (5 + c' + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
                  refine runs_cond_iff.mpr
                    ⟨0, (19 + (5 + (11 + (3 + (24 + (3 + (5 + (5 + c' + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                      by simpa [hpq] using htop_cond, ?_, by simp [Expr.size]⟩
                  simp only [↓reduceIte]
                  refine runs_seq3 (build_prefix ω)
                    (runs_cond_iff.mpr
                      ⟨0, (11 + (3 + (24 + (3 + (5 + (5 + c' + 1) + 1) + 1) + 1) + 1) + 1),
                        by simpa [hdead] using hcond_dead, ?_, by simp [Expr.size]⟩)
                  simp only [↓reduceIte]
                  refine runs_seq2 (hmid_abs ω)
                    (runs_cond_iff.mpr
                      ⟨0, (24 + (3 + (5 + (5 + c' + 1) + 1) + 1) + 1),
                        by simpa [habs_lt] using hcond_abs, ?_, by simp [Expr.size]⟩)
                  simp only [↓reduceIte]
                  refine runs_seq4 (hcur_prefix ω)
                    (runs_cond_iff.mpr
                      ⟨0, (5 + (5 + c' + 1) + 1),
                        by simpa [hcur_lt] using hcond_cur, ?_, by simp [Expr.size]⟩)
                  simp only [↓reduceIte]
                  refine runs_seq (hs10 ω)
                    (runs_cond_iff.mpr ⟨1, c', by simpa [hh_lt] using hcond_h, ?_, by simp [Expr.size]⟩)
                  simp only [Nat.one_ne_zero, ↓reduceIte]; exact hr'
                refine ⟨.normal, st', _, hrun,
                  ⟨s', buckets', hreg_fin, hpos', hpr', hinv', hs'_st, hs'_lt,
                    by rw [hpot.2.2.2.1, hpot.2.2.2.2], by omega⟩, by dsimp only at hc' ⊢; omega⟩
            · have huH : s.h u + 1 = cfg.H := by have := hinv.prune_inv.h_lt_H u huR; omega
              let hTmp := fun z => if z = u then cfg.H else s.h z
              let lvl := pickLevel cfg s.inR hTmp
              let buckets1 := if 1 ≤ s.h u then fun ℓ => if ℓ = s.h u then (buckets ℓ).erase u else buckets ℓ else buckets
              let remList := freezeRemList cfg u s buckets
              let s' := freezeStepWith cfg u remList s
              let buckets' := fun ℓ => if ℓ ≤ lvl then buckets1 ℓ else []
              have hfrz := freezeStep_triple (p := p) st10 hinv10 huR hexPos habs_eq hcur_end huH hw hdisj hcsr_w houtR_w
              refine ⟨90 + 260 * (s'.steps - s.steps), ?_⟩
              intro st ω hst; subst st
              rcases hfrz st10 ω ⟨rfl, hr10_u⟩ with ⟨o', st', c', hr', hq', hc'⟩
              cases o' with
              | returned => exact False.elim hq'
              | normal =>
                rcases hq' with ⟨hreg', hpos', hpr', hinv', hrem_h, hrem_n, hrem_m⟩
                have hpot := freezeStepWith_inv_pot hinv.cfg_valid hinv.prune_inv huR hexPos habs_eq hcur_end huH
                  hrem_h hrem_n hrem_m
                have hs'_st : s'.steps + pot cfg s' ≤ s.steps + pot cfg s := hpot.2.1
                have hs'_lt : pot cfg s' < pot cfg s := hpot.2.2.1
                have hs'_vc : volPminusB cfg s' + 2 * cfg.C_cap * cutPR cfg s' ≤
                    volPminusB cfg s + 2 * cfg.C_cap * cutPR cfg s := hpot.2.2.2
                have hsteps_ge4 : 4 ≤ s'.steps - s.steps := by
                  have hH3 : 3 ≤ cfg.H := PruneCfg.valid_three_le_H hinv.cfg_valid
                  have hinc_pos : 1 ≤ (cfg.incEdges u).length := by
                    by_contra h0
                    have h0' : (cfg.incEdges u).length = 0 := by omega
                    have hno := (hinv.prune_inv.no_ex_isolated u h0').1; omega
                  have hlvl_lt : lvl < cfg.H :=
                    (pickLevel_spec hinv.cfg_valid s.inR hTmp
                      ⟨u, hinv.prune_inv.inR_sub u huR, huR, by simp [hTmp],
                        le_trans hinc_pos (incEdges_length_le_degX cfg u)⟩).2.1
                  have hum : u ∈ remList := (hrem_m u).mpr (by
                    simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
                    exact ⟨hinv.prune_inv.inR_sub u huR, huR, by simp only [↓reduceIte]; exact hlvl_lt⟩)
                  have hv_ge : 1 ≤ (remList.map fun a => (cfg.incEdges a).length).sum :=
                    le_trans hinc_pos (List.le_sum_of_mem (List.mem_map_of_mem hum))
                  dsimp [s', freezeStepWith] at *
                  omega
                have hreg_fin : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r :=
                  fun r hr h1 h2 => (hreg' r hr h1 h2).trans (hr10_le r hr)
                have hrun : Runs w p ω pruneStepStmt st₀ .normal st'
                    (3 + (19 + (5 + (11 + (3 + (24 + (3 + (5 + (5 + c' + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
                  refine runs_cond_iff.mpr
                    ⟨0, (19 + (5 + (11 + (3 + (24 + (3 + (5 + (5 + c' + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                      by simpa [hpq] using htop_cond, ?_, by simp [Expr.size]⟩
                  simp only [↓reduceIte]
                  refine runs_seq3 (build_prefix ω)
                    (runs_cond_iff.mpr
                      ⟨0, (11 + (3 + (24 + (3 + (5 + (5 + c' + 1) + 1) + 1) + 1) + 1) + 1),
                        by simpa [hdead] using hcond_dead, ?_, by simp [Expr.size]⟩)
                  simp only [↓reduceIte]
                  refine runs_seq2 (hmid_abs ω)
                    (runs_cond_iff.mpr
                      ⟨0, (24 + (3 + (5 + (5 + c' + 1) + 1) + 1) + 1),
                        by simpa [habs_lt] using hcond_abs, ?_, by simp [Expr.size]⟩)
                  simp only [↓reduceIte]
                  refine runs_seq4 (hcur_prefix ω)
                    (runs_cond_iff.mpr
                      ⟨0, (5 + (5 + c' + 1) + 1),
                        by simpa [hcur_lt] using hcond_cur, ?_, by simp [Expr.size]⟩)
                  simp only [↓reduceIte]
                  refine runs_seq (hs10 ω)
                    (runs_cond_iff.mpr ⟨0, c', by simpa [hh_lt] using hcond_h, ?_, by simp [Expr.size]⟩)
                  simp only [↓reduceIte]; exact hr'
                refine ⟨.normal, st', _, hrun,
                  ⟨s', buckets', hreg_fin, hpos', hpr', hinv', hs'_st, hs'_lt, hs'_vc,
                    by omega⟩, by have hbd : c' ≤ 260 * (s'.steps - s.steps) := hc'; dsimp only; omega⟩

end MinCostFlow.Expander
