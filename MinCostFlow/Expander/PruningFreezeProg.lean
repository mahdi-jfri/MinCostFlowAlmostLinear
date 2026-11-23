module

public import MinCostFlow.Expander.PruningFreezeWalkProg

/-!
# Freeze Step Triple
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

theorem freezeStep_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr u : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} (st₀ : State)
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (huR : s.inR u = true) (hexPos : 0 < s.ex u)
    (habs : s.abs u = cfg.degX u) (hcur : s.cur u = (cfg.incEdges u).length)
    (huH : s.h u + 1 = cfg.H)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w) :
    let hTmp := fun z => if z = u then cfg.H else s.h z
    let lvl := pickLevel cfg s.inR hTmp
    let buckets1 := if 1 ≤ s.h u then fun ℓ => if ℓ = s.h u then (buckets ℓ).erase u else buckets ℓ else buckets
    let remList := freezeRemList cfg u s buckets
    let s' := freezeStepWith cfg u remList s
    let buckets' := fun ℓ => if ℓ ≤ lvl then buckets1 ℓ else []
    Triple w p (fun st => st = st₀ ∧ st.regs prU = u) freezeStepStmt
      (normalPost fun st' =>
        (∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos ∧
        PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
          (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
        PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s' buckets' st' ∧
        remList.head? = some u ∧
        remList.Nodup ∧
        (∀ x, x ∈ remList ↔ x ∈ cfg.X.filter fun y => s.inR y && decide (lvl + 1 ≤ hTmp y)))
      (fun _ => 260 * (s'.steps - s.steps)) := by
  intro hTmp lvl buckets1 remList s' buckets' st ω ⟨hst, hru⟩
  subst st
  have hH3 : 3 ≤ cfg.H := PruneCfg.valid_three_le_H hinv.cfg_valid
  have hwb := pruneWordBound_pos hw
  have hlt2w : ∀ k, k < workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H → k < 2 ^ w := fun k hk => by
    unfold PruneWordBound at hw; omega
  have huN : u < cfg.G.n := by
    have := hinv.prune_inv.inR_sub u huR; rw [hinv.cfg_X] at this; exact Finset.mem_range.mp this
  have huX : u ∈ cfg.X := hinv.prune_inv.inR_sub u huR
  rcases freezeStep_walk_stage (p := p) st₀ hinv huR hexPos habs hcur huH hw hdisj st₀ ω ⟨rfl, hru⟩ with
    ⟨owk, st6, c_walk, hr_walk, hq_walk, hc_walk⟩
  cases owk with
  | returned => exact False.elim hq_walk
  | normal =>
    have hlvl1 : 1 ≤ lvl := hq_walk.lvl1
    have hlvlH : lvl < cfg.H := hq_walk.lvlH
    have hinc_pos : 1 ≤ (cfg.incEdges u).length := hq_walk.inc_pos
    have hb1_nd : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H → (buckets1 ℓ).Nodup := hq_walk.b1_nd
    have hb1_mem : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H → ∀ x,
        x ∈ buckets1 ℓ ↔ x < cfg.G.n ∧ s.inR x = true ∧ hTmp x = ℓ := hq_walk.b1_mem
    have hrem_head : remList.head? = some u := hq_walk.rem_head
    have hrem_nd : remList.Nodup := hq_walk.rem_nd
    have hrem_mem : ∀ x, x ∈ remList ↔
        x ∈ cfg.X.filter fun y => s.inR y && decide (lvl + 1 ≤ hTmp y) := hq_walk.rem_mem
    have hlv_le : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ lvl →
        st6.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) = volAtLevel cfg s.inR hTmp ℓ :=
      hq_walk.lvlVol_le
    have hlv_gt : ∀ ℓ, lvl + 1 ≤ ℓ → ℓ < cfg.H →
        st6.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) = 0 :=
      hq_walk.lvlVol_gt
    let r7a := Function.update st6.regs prSuf remList.length
    let st7a : State := { mem := st6.mem, regs := r7a, pos := st6.pos }
    have hr7a : Runs w p ω (.assign prSuf (.reg prEnd)) st6 .normal st7a 2 :=
      runs_assign_iff.mpr ⟨remList.length, eval_reg_eq w st6 prEnd hq_walk.reg_end, rfl, rfl, by simp [Expr.size]⟩
    let r7 := Function.update r7a prI 0
    let st7 : State := { mem := st6.mem, regs := r7, pos := st6.pos }
    have hr7b : Runs w p ω (.assign prI (.const 0)) st7a .normal st7 2 :=
      runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, by simp [Expr.size]⟩
    let A : Finset ℕ := cfg.X.filter fun x => s.inR x && decide (lvl + 1 ≤ hTmp x)
    let sMid : PruneState := { s with h := hTmp, cur := fun x => if x = u then 0 else s.cur x }
    have hMid_sw : SweepInv cfg A sMid :=
      freeze_sweep_inv hinv.prune_inv huR hexPos habs hcur huH hlvlH
    have hMid_pq : PeelQInv cfg sMid := hinv.peelQ_inv
    have hMid_ex : ∀ x < cfg.G.n, sMid.ex x ≤ 4 * cfg.C_cap * cfg.G.m := hinv.ex_bound
    let stateOf := freezeStateOf cfg sMid remList
    let remVol := freezeRemVol cfg remList
    have hlen_le_volEA : remList.length ≤ remVol 0 := by
      dsimp [remVol, freezeRemVol]; simp only [List.drop_zero]
      apply list_length_le_map_sum
      intro a ha
      by_cases hau : a = u
      · subst hau; exact hinc_pos
      · have haA := (hrem_mem a).mp ha
        simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at haA
        have haH : 0 < s.h a := by simp only [hTmp, hau, ↓reduceIte] at haA; omega
        by_contra h0
        have h0' : (cfg.incEdges a).length = 0 := by omega
        have := (hinv.prune_inv.no_ex_isolated a h0').2.1
        omega
    let remCond := Expr.bin .lt (.reg prI) (.reg prSuf)
    let remBody := seqStmts
      [ .assign prU (.load (.bin .add (.reg prRemArr) (.reg prI)))
      , removeOneFromRStmt
      , .assign prI (.bin .add (.reg prI) (.const 1)) ]
    let remInv := FreezeRemInv cfg gAddr csrAddr inBAddr outRAddr workAddr A sMid remList st₀ st6
    have hrem_init : remInv 0 st7 := by
      have hr7_le : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st7.regs r = st₀.regs r := by
        intro r hr h1 h2
        dsimp [st7, r7, r7a, prCsrAdjH, prI, prSuf] at hr ⊢
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hq_walk.regs_agree r hr h1 h2
      refine
        { i_le := Nat.zero_le _
          reg_i := by dsimp [st7, r7]; rw [Function.update_self]
          reg_suf := by dsimp [st7, r7, r7a]; rw [Function.update_of_ne (by decide), Function.update_self]
          reg_actTop := by
            dsimp [st7, r7, r7a]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
              hq_walk.reg_actTop, hinv.reg_actTop]; rfl
          reg_peelTop := by
            dsimp [st7, r7, r7a]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
              hq_walk.reg_peelTop, hinv.reg_peelTop]; rfl
          regs_agree := hr7_le
          stepRegs := pruneStepRegs_of_agree hinv.stepRegs hr7_le
          pos_eq := hq_walk.pos_eq
          pres_out := hq_walk.pres_out
          below_ex := fun _ _ _ => rfl
          above_ln := fun _ _ _ => rfl
          outR_eq := hq_walk.outR_eq
          ex_eq := fun x hx => by
            dsimp only [st7, st7a, freezeStateOf, sMid, List.take_zero, List.foldl_nil]
            rw [hq_walk.mid_eq _ (Nat.le_add_right _ _) (by dsimp [wEx, wLvlNext]; omega), hinv.ex_eq x hx]
          degR_eq := fun x hx => by
            dsimp only [st7, st7a, freezeStateOf, sMid, List.take_zero, List.foldl_nil]
            rw [hq_walk.mid_eq _ (by dsimp [wEx, wDegR]; omega) (by dsimp [wDegR, wLvlNext]; omega), hinv.degR_eq x hx]
          inAct_eq := fun x hx => by
            dsimp only [st7, st7a, freezeStateOf, sMid, List.take_zero, List.foldl_nil]
            rw [hq_walk.mid_eq _ (by dsimp [wEx, wInAct]; omega) (by dsimp [wInAct, wLvlNext]; omega), hinv.inAct_eq x hx]
            rfl
          actStk_eq := fun q hq => by
            have hqn : q < cfg.G.n := lt_of_lt_of_le hq hinv.active_len_le
            dsimp only [st7, st7a, freezeStateOf, sMid, List.take_zero, List.foldl_nil]
            rw [hq_walk.mid_eq _ (by dsimp [wEx, wActStk]; omega) (by dsimp [wActStk, wLvlNext]; omega), hinv.actStk_eq q hq]
          peelStk_eq := fun q hq => by
            have hpq_len : s.peelQ.length ≤ cfg.G.n := by
              have hsub : ∀ x ∈ s.peelQ, x ∈ Finset.range cfg.G.n := fun x hx => by
                rw [← hinv.cfg_X]; exact hinv.peelQ_inv.2.1 x hx
              calc s.peelQ.length = s.peelQ.toFinset.card := (List.toFinset_card_of_nodup hinv.peelQ_inv.1).symm
                _ ≤ (Finset.range cfg.G.n).card := Finset.card_le_card (fun x hx => hsub x (List.mem_toFinset.mp hx))
                _ = cfg.G.n := Finset.card_range cfg.G.n
            have hqn : q < cfg.G.n := lt_of_lt_of_le hq hpq_len
            dsimp only [st7, st7a, freezeStateOf, sMid, List.take_zero, List.foldl_nil]
            rw [hq_walk.mid_eq _ (by dsimp [wEx, wPeelStk]; omega) (by dsimp [wPeelStk, wLvlNext]; omega), hinv.peelStk_eq q hq]
          sw := by simp [freezeStateOf]; exact hMid_sw
          pq := hMid_pq
          ex_bd := hMid_ex }
    have hrem_sub : ∀ x ∈ remList, x < cfg.G.n ∧ sMid.inR x = true := fun x hx => by
      have haA := (hrem_mem x).mp hx
      simp only [Finset.mem_filter, Bool.and_eq_true] at haA
      exact ⟨Finset.mem_range.mp (by rw [← hinv.cfg_X]; exact haA.1), haA.2.1⟩
    have hflow6 : ∀ idx < cfg.G.m, st6.mem (wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx) =
        (↑cfg.C_cap + sMid.flow idx).toNat := hq_walk.flowEnc_eq
    have hrem_loop : Triple w p (remInv 0) (.loop remCond remBody)
        (normalPost (remInv remList.length))
        (fun _ => 50 * remList.length + 152 * remVol 0 + 10) := by
      apply Triple.loop_inv (Inv := remInv)
        (condVal := fun st => if st.regs prI < st.regs prSuf then 1 else 0)
        (fun i => remList.length - i)
        (fun i => 50 * (remList.length - i) + 152 * remVol i + 10)
        ?_ ?_ ?_ 0
      · intro i st hrm
        exact Expr.eval_bin (op := .lt) (eval_reg_eq w st prI rfl) (eval_reg_eq w st prSuf rfl)
          (by dsimp only [BinOp.eval]; split_ifs <;> omega)
      · intro i st hrm h0
        have hi_eq : i = remList.length := by
          by_contra hne
          have hlt : st.regs prI < st.regs prSuf := by
            rw [hrm.reg_i, hrm.reg_suf]; exact Nat.lt_of_le_of_ne hrm.i_le hne
          simp [hlt] at h0
        subst hi_eq; exact ⟨hrm, by simp [remCond, Expr.size]⟩
      · exact freezeStep_rem_step (p := p) hinv.cfg_X hinv.cfg_valid hinv.csr_at hw hdisj
          hcsr_w houtR_w hrem_nd hrem_sub hq_walk.remArr_eq hflow6
    rcases hrem_loop st7 ω hrem_init with ⟨orm, st8, c_rem, hr_rem, hq_rem, hc_rem⟩
    cases orm with
    | returned => exact False.elim hq_rem
    | normal =>
      have hfin_eq : stateOf remList.length =
          remList.foldl (fun st a => removeOneFromR cfg a st) sMid := by
        dsimp [stateOf, freezeStateOf]; simp [List.take_length]
      have hs'_st_eq : s' = { stateOf remList.length with steps := s.steps + cfg.H + remVol 0 } := by
        rw [hfin_eq]; rfl
      have hs'_inR : s'.inR = (stateOf remList.length).inR := by rw [hs'_st_eq]
      have hs'_ex : s'.ex = (stateOf remList.length).ex := by rw [hs'_st_eq]
      have hs'_degR : s'.degR = (stateOf remList.length).degR := by rw [hs'_st_eq]
      have hs'_inAct : s'.inActive = (stateOf remList.length).inActive := by rw [hs'_st_eq]
      have hs'_act : s'.active = (stateOf remList.length).active := by rw [hs'_st_eq]
      have hs'_peel : s'.peelQ = (stateOf remList.length).peelQ := by rw [hs'_st_eq]
      have hst_static : s'.h = hTmp ∧ s'.cur = (fun x => if x = u then 0 else s.cur x) ∧
          s'.abs = s.abs ∧ s'.flow = s.flow := by
        have hf := foldl_removeOneFromR_static cfg remList sMid
        rw [← hfin_eq] at hf
        rw [hs'_st_eq]; exact hf
      have hfin_inR_spec : ∀ x, s'.inR x = (s.inR x && !(x ∈ remList)) := by
        intro x; rw [hs'_inR, hfin_eq, foldl_removeOneFromR_inR]
      have hfw := freezeStepWith_inv_pot hinv.cfg_valid hinv.prune_inv huR hexPos habs hcur huH
        hrem_head hrem_nd hrem_mem
      have hs'_inv : PruningInv cfg s' := hfw.1
      have hs'_pq : PeelQInv cfg s' := by
        rw [hs'_st_eq]; exact hq_rem.pq
      have hst8_below_ex : ∀ q, wHArr workAddr cfg.G.n cfg.G.m cfg.H ≤ q →
          q < wEx workAddr cfg.G.n cfg.G.m cfg.H → st8.mem q = st6.mem q :=
        hq_rem.below_ex
      have hst8_above_ln : ∀ q, wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤ q →
          q < outRAddr ∨ outRAddr + cfg.G.n ≤ q → st8.mem q = st6.mem q :=
        hq_rem.above_ln
      have hst8_reg := hq_rem.regs_agree
      have hst8_pr := hq_rem.pres_out
      have hst8_vol : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
          st8.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) = volAtLevel cfg s'.inR s'.h ℓ := by
        intro ℓ h1 hH
        have hge : wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤
            wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ := by dsimp [wLvlNext, wLvlVol]; omega
        have hout : wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ < outRAddr ∨
            outRAddr + cfg.G.n ≤ wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ := by
          have hws : wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ <
              workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H := by
            unfold pruneWorkSpace; dsimp [wLvlVol]; omega
          dsimp [wLvlVol] at *; rcases hdisj.2.2.2.2.2.2 with h | h <;> omega
        rw [hst8_above_ln _ hge hout]
        by_cases hle : ℓ ≤ lvl
        · rw [hlv_le ℓ h1 hle, hst_static.1]
          unfold volAtLevel
          apply Finset.sum_congr rfl
          intro x _
          by_cases hxr : s.inR x = true
          · by_cases hxℓ : hTmp x = ℓ
            · have hnot_rem : x ∉ remList := by
                intro hm
                have ha := (hrem_mem x).mp hm
                simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at ha
                omega
              simp [hxr, hxℓ, hfin_inR_spec x, hnot_rem]
            · simp [hxr, hxℓ, hfin_inR_spec x]
          · simp [hxr, hfin_inR_spec x]
        · have hgt : lvl + 1 ≤ ℓ := by omega
          rw [hlv_gt ℓ hgt hH]
          symm; unfold volAtLevel; rw [hst_static.1]
          apply Finset.sum_eq_zero
          intro x hxX
          by_cases hxℓ : hTmp x = ℓ
          · by_cases hxr : s.inR x = true
            · have hin_rem : x ∈ remList := (hrem_mem x).mpr (by
                simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
                exact ⟨hxX, hxr, by omega⟩)
              simp [hfin_inR_spec x, hin_rem]
            · simp [hfin_inR_spec x, hxr]
          · simp [hxℓ]
      have hst8_dl_eq : ∀ q, wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤ q →
          q < wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + cfg.H →
          st8.mem q = st6.mem q := fun q hq1 hq2 => by
        apply hst8_above_ln q hq1
        have hws : q < workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H := by
          unfold pruneWorkSpace at *; dsimp [wLvlHead] at *; omega
        dsimp [wLvlNext] at *; rcases hdisj.2.2.2.2.2.2 with h | h <;> omega
      have hpost_run : Runs w p ω (seqStmts
          [ .assign prSuf (.reg prEnd)
          , .assign prI (.const 0)
          , .loop remCond remBody ]) st6 .normal st8 (2 + (2 + c_rem + 1) + 1) :=
        runs_seq hr7a (runs_seq hr7b hr_rem)
      have hrun : Runs w p ω freezeStepStmt st₀ .normal st8
          (c_walk + (2 + (2 + c_rem + 1) + 1) + 1) := by
        simpa only [freezeStepStmt, freezeWalkList, List.cons_append, List.nil_append] using
          runs_seqStmts_split (l1 := freezeWalkList)
            (l2 := [.assign prSuf (.reg prEnd), .assign prI (.const 0), .loop remCond remBody])
            (by simp) (by simp) hr_walk hpost_run
      have hsteps_eq : s'.steps - s.steps = cfg.H + remVol 0 := by
        rw [hs'_st_eq]; dsimp; omega
      change c_walk ≤ 85 * cfg.H + 26 * remList.length + 140 at hc_walk
      dsimp only at hc_walk hc_rem
      refine ⟨.normal, st8, _, hrun, ⟨hst8_reg, hq_rem.pos_eq, hst8_pr, ?_,
        hrem_head, hrem_nd, hrem_mem⟩, by dsimp only; rw [hsteps_eq]; omega⟩
      refine mkPruneMemInv hinv hdisj hst8_reg hst8_pr
        (hq_rem.reg_actTop.trans (by rw [hs'_act]))
        (hq_rem.reg_peelTop.trans (by rw [hs'_peel]))
        (fun x hx => by rw [hs'_inR]; exact hq_rem.outR_eq x hx)
        (fun x hx => by
          rw [hst8_below_ex _ (by dsimp [wHArr]; omega) (by dsimp [wHArr, wEx]; omega),
            hq_walk.hArr_eq x hx, hst_static.1])
        (fun x hx => by
          rw [hst8_below_ex _ (by dsimp [wHArr, wCur]; omega) (by dsimp [wCur, wEx]; omega),
            hq_walk.cur_eq x hx, hst_static.2.1])
        (fun x hx => by
          rw [hst8_below_ex _ (by dsimp [wHArr, wAbs]; omega) (by dsimp [wAbs, wEx]; omega),
            hq_walk.abs_eq x hx, hst_static.2.2.1])
        (fun x hx => by rw [hs'_ex]; exact hq_rem.ex_eq x hx)
        (fun x hx => by rw [hs'_degR]; exact hq_rem.degR_eq x hx)
        (fun x hx => by rw [hs'_inAct]; exact hq_rem.inAct_eq x hx)
        (fun q hq => by rw [hs'_act] at hq ⊢; exact hq_rem.actStk_eq q hq)
        (fun q hq => by rw [hs'_peel] at hq ⊢; exact hq_rem.peelStk_eq q hq)
        (fun idx hidx => by
          rw [hst_static.2.2.2]
          have hge : wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤
              wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx := by dsimp [wLvlNext, wFlowEnc]; omega
          have hout : wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx < outRAddr ∨
              outRAddr + cfg.G.n ≤ wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx := by
            have : wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx <
                workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H := by
              unfold pruneWorkSpace; dsimp [wFlowEnc]; omega
            dsimp [wFlowEnc] at *; rcases hdisj.2.2.2.2.2.2 with h | h <;> omega
          rw [hst8_above_ln _ hge hout, hflow6 idx hidx])
        (by
          have hge : wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤
              wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + cfg.H := by dsimp [wLvlNext, wLvlVol]; omega
          have hout : wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + cfg.H < outRAddr ∨
              outRAddr + cfg.G.n ≤ wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + cfg.H := by
            have : wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + cfg.H <
                workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H := by
              unfold pruneWorkSpace; dsimp [wLvlVol]; omega
            dsimp [wLvlVol] at *; rcases hdisj.2.2.2.2.2.2 with h | h <;> omega
          rw [hst8_above_ln _ hge hout, hq_walk.lvlVol_H])
        hst8_vol
        (fun ℓ h1 hH => by
          dsimp only [buckets']; by_cases hle : ℓ ≤ lvl
          · simp only [hle, ↓reduceIte]; exact hb1_nd ℓ h1 hH
          · simp [hle])
        (fun ℓ h1 hH x => by
          dsimp only [buckets']; by_cases hle : ℓ ≤ lvl
          · simp only [hle, ↓reduceIte, hb1_mem ℓ h1 hH x, hst_static.1, hfin_inR_spec x]
            constructor
            · rintro ⟨hxN, hxR, hxH⟩
              refine ⟨hxN, ?_, hxH⟩
              have hnr : x ∉ remList := by
                intro hm; have ha := (hrem_mem x).mp hm
                simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at ha; omega
              simp [hxR, hnr]
            · rintro ⟨hxN, hxR, hxH⟩
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxR
              exact ⟨hxN, hxR.1, hxH⟩
          · simp only [hle, ↓reduceIte, List.not_mem_nil, false_iff, not_and]
            intro _ hxR hxH
            have hin_rem : x ∈ remList := (hrem_mem x).mpr (by
              simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
              refine ⟨by rw [hinv.cfg_X]; exact Finset.mem_range.mpr ‹_›, ?_, ?_⟩
              · have := hxR; rw [hfin_inR_spec] at this
                exact (Bool.and_eq_true _ _ |>.mp this).1
              · rw [← hst_static.1]; omega)
            have := hfin_inR_spec x
            rw [hxR] at this
            simp [hin_rem] at this)
        (fun ℓ h1 hH => by
          dsimp only [buckets']
          have hge_h : wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤
              wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ := by dsimp [wLvlNext, wLvlHead]; omega
          have hlt_h : wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ <
              wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + cfg.H := by omega
          have hdl6 := hq_walk.buckets_dl ℓ h1 hH
          rw [hst8_dl_eq _ hge_h hlt_h]
          refine doublyLinked_congr_disjoint
            (fun y hy => by
              have hyN := doublyLinked_mem_lt hdl6 hy
              exact hst8_dl_eq _ (by dsimp [wLvlNext]; omega) (by dsimp [wLvlNext, wLvlHead]; omega))
            (fun y hy => by
              have hyN := doublyLinked_mem_lt hdl6 hy
              exact hst8_dl_eq _ (by dsimp [wLvlNext, wLvlPrev]; omega) (by dsimp [wLvlPrev, wLvlHead]; omega))
            hdl6)
        (fun x hx => by rw [hs'_ex]; exact hq_rem.ex_bd x hx)
        hs'_inv hs'_pq

end MinCostFlow.Expander
