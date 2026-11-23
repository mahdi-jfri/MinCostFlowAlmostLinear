module

public import MinCostFlow.Expander.PruningPushActProg

/-!
# Push-Flow Step Triple
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

theorem pushFlowStep_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr u : ℕ}
    {restAct : List ℕ} {s : PruneState} {buckets : ℕ → List ℕ} (st₀ : State)
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (hact : s.active = u :: restAct)
    (huR : s.inR u = true)
    (hex_pos : 0 < s.ex u)
    (habs : s.abs u = cfg.degX u)
    (hcur : s.cur u < (cfg.incEdges u).length)
    (hadm : have p := (cfg.incEdges u).getD (s.cur u) (0, false, 0);
      s.inR p.2.2 = true ∧ flowDir s.flow p.1 p.2.1 < ↑cfg.C_cap ∧ s.h u = s.h p.2.2 + 1)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hcsrB : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w) :
    let s' := pushFlowStep cfg u restAct s
    Triple w p (fun st => st = st₀ ∧ st.regs prU = u) pushFlowStepStmt
      (normalPost fun st' =>
        (∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
          st'.pos = st₀.pos ∧
            PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
                (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
              PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s' buckets st')
      (fun _ => 160) := by
  intro s'
  have hwb := pruneWordBound_pos hw
  have hlt2w : ∀ k, k < workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H → k < 2 ^ w := fun k hk => by
    unfold PruneWordBound at hw; omega
  have hstep_inv := pushFlowStep_inv_pot_pub hinv.cfg_valid hinv.prune_inv hact huR hex_pos habs hcur hadm
  have hs'_inv : PruningInv cfg s' := hstep_inv.1
  have hs'_peel : s'.peelQ = s.peelQ := by dsimp [s', pushFlowStep]; split_ifs <;> rfl
  have hs'_degR : s'.degR = s.degR := by dsimp [s', pushFlowStep]; split_ifs <;> rfl
  have hs'_inR : s'.inR = s.inR := by dsimp [s', pushFlowStep]; split_ifs <;> rfl
  have hs'_h : s'.h = s.h := by dsimp [s', pushFlowStep]; split_ifs <;> rfl
  have hs'_abs : s'.abs = s.abs := by dsimp [s', pushFlowStep]; split_ifs <;> rfl
  have hs'_pq : PeelQInv cfg s' :=
    ⟨by rw [hs'_peel]; exact hinv.peelQ_inv.1, by rw [hs'_peel]; exact hinv.peelQ_inv.2.1,
      fun x hx => by rw [hs'_peel] at hx; rw [hs'_degR]; exact hinv.peelQ_inv.2.2 x hx⟩
  have hact'_len : s'.active.length ≤ cfg.G.n := by
    have hsub : ∀ x ∈ s'.active, x ∈ Finset.range cfg.G.n := fun x hx => by
      rw [← hinv.cfg_X]; exact hs'_inv.active_sub x hx
    calc s'.active.length = s'.active.toFinset.card := (List.toFinset_card_of_nodup hs'_inv.active_nodup).symm
      _ ≤ (Finset.range cfg.G.n).card := Finset.card_le_card (fun x hx => hsub x (List.mem_toFinset.mp hx))
      _ = cfg.G.n := Finset.card_range cfg.G.n
  have hpq_len : s.peelQ.length ≤ cfg.G.n := by
    have hsub : ∀ x ∈ s.peelQ, x ∈ Finset.range cfg.G.n := fun x hx => by
      rw [← hinv.cfg_X]; exact hinv.peelQ_inv.2.1 x hx
    calc s.peelQ.length = s.peelQ.toFinset.card := (List.toFinset_card_of_nodup hinv.peelQ_inv.1).symm
      _ ≤ (Finset.range cfg.G.n).card := Finset.card_le_card (fun x hx => hsub x (List.mem_toFinset.mp hx))
      _ = cfg.G.n := Finset.card_range cfg.G.n
  have huN : u < cfg.G.n := by
    have := hinv.prune_inv.inR_sub u huR
    rw [hinv.cfg_X] at this; exact Finset.mem_range.mp this
  let q := (cfg.incEdges u).getD (s.cur u) (0, false, 0)
  let idx := q.1
  let dir := q.2.1
  let nbr := q.2.2
  let rc := (↑cfg.C_cap - flowDir s.flow idx dir).toNat
  let δ := min (s.ex u) rc
  let flow' := fun k => if k = idx then if dir = true then s.flow idx - ↑δ else s.flow idx + ↑δ else s.flow k
  let ex' := fun x => if x = u then s.ex u - δ else if x = nbr then s.ex nbr + δ else s.ex x
  have hs'_ex : s'.ex = ex' := by
    dsimp only [s', pushFlowStep, ex', δ, rc, nbr, dir, idx, q]
    by_cases hcond : (↑cfg.C_cap - flowDir s.flow ((cfg.incEdges u).getD (s.cur u) (0, false, 0)).1
        ((cfg.incEdges u).getD (s.cur u) (0, false, 0)).2.1).toNat ≤ s.ex u <;>
      simp only [hcond, ↓reduceIte]
  have hs'_flow : s'.flow = flow' := by
    dsimp only [s', pushFlowStep, flow', δ, rc, dir, idx, q]
    by_cases hcond : (↑cfg.C_cap - flowDir s.flow ((cfg.incEdges u).getD (s.cur u) (0, false, 0)).1
        ((cfg.incEdges u).getD (s.cur u) (0, false, 0)).2.1).toNat ≤ s.ex u <;>
      simp only [hcond, ↓reduceIte]
  have hpre := pushFlowPrefix_triple (p := p) st₀ hinv huR hcur hw hcsrB
  have htail : Triple w p
      (fun st1 =>
        (∀ r ≤ prCsrAdjH, st1.regs r = st₀.regs r) ∧
          st1.regs prU = u ∧ st1.regs prW = nbr ∧ st1.regs prTmp1 = s.ex u ∧ st1.regs prRc = rc ∧
          st1.pos = st₀.pos ∧ nbr < cfg.G.n ∧ nbr ≠ u ∧ idx < cfg.G.m ∧
          MemFrame st₀.mem st1.mem (wEx workAddr cfg.G.n cfg.G.m cfg.H) (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H) ∧
          (∀ x, x < wEx workAddr cfg.G.n cfg.G.m cfg.H ∨ wDegR workAddr cfg.G.n cfg.G.m cfg.H ≤ x →
            x ≠ wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx → st1.mem x = st₀.mem x) ∧
          (∀ x < cfg.G.n, st1.mem (wEx workAddr cfg.G.n cfg.G.m cfg.H + x) = ex' x) ∧
          (∀ k < cfg.G.m, st1.mem (wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + k) = (↑cfg.C_cap + flow' k).toNat))
      (.cond (.bin .lt (.reg prTmp1) (.reg prRc))
        (seqStmts
          [ .assign prActTop (.bin .sub (.reg prActTop) (.const 1))
          , .store (.bin .add (.reg prInAct) (.reg prU)) (.const 0)
          , pushActWStmt ])
        (seqStmts
          [ .assign prTmp3 (.load (.bin .add (.reg prCur) (.reg prU)))
          , .store (.bin .add (.reg prCur) (.reg prU)) (.bin .add (.reg prTmp3) (.const 1))
          , pushActWStmt ]))
      (normalPost fun st' =>
        (∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
          st'.pos = st₀.pos ∧
            PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
                (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
              PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s' buckets st')
      (fun _ => 47) := by
    intro st1 ω ⟨hr_le, hr_u, hr_w, hr_t1, hr_rc, hpos1, hnbr_lt, hnbr_ne, hidx_lt,
      hmf1, hother1, hex1, hflow1⟩
    have hregs1 : PruneStepRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st1 :=
      pruneStepRegs_of_agree hinv.stepRegs (fun r hr _ _ => hr_le r hr)
    have hcond_ev : Expr.eval w st1 (.bin .lt (.reg prTmp1) (.reg prRc)) =
        some (if s.ex u < rc then 1 else 0) :=
      Expr.eval_bin (eval_reg_eq w st1 prTmp1 hr_t1) (eval_reg_eq w st1 prRc hr_rc)
        (by simp [BinOp.eval]; split_ifs <;> omega)
    have mk_post : ∀ (st' : State),
        (∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) →
        st'.pos = st₀.pos →
        st'.regs prActTop = s'.active.length →
        st'.regs prPeelTop = s'.peelQ.length →
        PreservedOutside2 st1.mem st'.mem (wCur workAddr cfg.G.n cfg.G.m cfg.H) (wAbs workAddr cfg.G.n cfg.G.m cfg.H)
          (wInAct workAddr cfg.G.n cfg.G.m cfg.H) (wPeelStk workAddr cfg.G.n cfg.G.m cfg.H) →
        (∀ x < cfg.G.n, st'.mem (wCur workAddr cfg.G.n cfg.G.m cfg.H + x) = s'.cur x) →
        (∀ x < cfg.G.n, st'.mem (wInAct workAddr cfg.G.n cfg.G.m cfg.H + x) = if s'.inActive x = true then 1 else 0) →
        (∀ i < s'.active.length, st'.mem (wActStk workAddr cfg.G.n cfg.G.m cfg.H + i) = s'.active.getD (s'.active.length - 1 - i) 0) →
        (∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
          st'.pos = st₀.pos ∧
            PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
                (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
              PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s' buckets st' := by
      intro st' hreg' hpos' hat' hpt' hpr1' hcur' hinAct' hactStk'
      have hpr_all : PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
          (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) := by
        intro a _ ha2
        unfold pruneWorkSpace at ha2
        rw [hpr1' a (by dsimp [wHArr, wCur, wAbs] at *; omega) (by dsimp [wHArr, wInAct, wPeelStk] at *; omega),
          hmf1 a (by dsimp [wHArr, wEx, wLvlVol] at *; omega)]
      have hagree_low : ∀ a, a < workAddr + cfg.G.n ∨ workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H ≤ a →
          st'.mem a = st₀.mem a := fun a ha => by
        unfold pruneWorkSpace at ha
        rw [hpr1' a (by dsimp [wCur, wAbs] at *; omega) (by dsimp [wInAct, wPeelStk] at *; omega),
          hmf1 a (by dsimp [wEx, wLvlVol] at *; omega)]
      have hagree_mid_peel : ∀ a, wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤ a →
          a < wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H + cfg.G.n → st'.mem a = st₀.mem a := fun a ha1 ha2 => by
        rw [hpr1' a (by dsimp [wCur, wAbs, wLvlNext] at *; omega) (by dsimp [wInAct, wPeelStk, wLvlNext] at *; omega),
          hother1 a (Or.inr (by dsimp [wDegR, wLvlNext] at *; omega)) (by dsimp [wLvlNext, wLvlPrev, wFlowEnc] at *; omega)]
      refine ⟨hreg', hpos', hpr_all, ?_⟩
      refine mkPruneMemInv hinv hdisj hreg' hpr_all hat' hpt'
        (fun x hx => by
          have hdisj_or : outRAddr + x < workAddr ∨ workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H ≤ outRAddr + x := by
            rcases hdisj.2.2.2.2.2.2 with hdw | hdw <;> omega
          rw [hagree_low (outRAddr + x) (by rcases hdisj_or with h | h <;> [exact Or.inl (by omega); exact Or.inr h]),
            hinv.outR_eq x hx, hs'_inR])
        (fun x hx => by
          rw [hpr1' (wHArr workAddr cfg.G.n cfg.G.m cfg.H + x) (by dsimp [wHArr, wCur, wAbs]; omega)
            (by dsimp [wHArr, wInAct, wPeelStk]; omega),
            hmf1 (wHArr workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inl (by dsimp [wHArr, wEx]; omega)),
            hinv.h_eq x hx, hs'_h])
        hcur'
        (fun x hx => by
          rw [hpr1' (wAbs workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inr (by omega))
            (by dsimp [wAbs, wInAct, wPeelStk]; omega),
            hmf1 (wAbs workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inl (by dsimp [wAbs, wEx]; omega)),
            hinv.abs_eq x hx, hs'_abs])
        (fun x hx => by
          rw [hpr1' (wEx workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inr (by dsimp [wAbs, wEx]; omega))
            (by dsimp [wEx, wInAct, wPeelStk]; omega), hex1 x hx, hs'_ex])
        (fun x hx => by
          rw [hpr1' (wDegR workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inr (by dsimp [wAbs, wDegR]; omega))
            (by dsimp [wDegR, wInAct, wPeelStk]; omega),
            hother1 (wDegR workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inr (by omega)) (by dsimp [wDegR, wFlowEnc]; omega),
            hinv.degR_eq x hx, hs'_degR])
        hinAct' hactStk'
        (fun i hi => by
          rw [hs'_peel] at hi ⊢
          have hi_n : i < cfg.G.n := lt_of_lt_of_le hi hpq_len
          rw [hpr1' (wPeelStk workAddr cfg.G.n cfg.G.m cfg.H + i) (Or.inr (by dsimp [wAbs, wPeelStk]; omega))
            (Or.inr (by omega)),
            hother1 (wPeelStk workAddr cfg.G.n cfg.G.m cfg.H + i) (Or.inr (by dsimp [wDegR, wPeelStk]; omega))
              (by dsimp [wPeelStk, wFlowEnc]; omega),
            hinv.peelStk_eq i hi])
        (fun k hk => by
          rw [hpr1' (wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + k) (Or.inr (by dsimp [wAbs, wFlowEnc]; omega))
            (Or.inr (by dsimp [wPeelStk, wFlowEnc]; omega)), hflow1 k hk, hs'_flow])
        (by
          rw [hpr1' (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + cfg.H) (Or.inr (by dsimp [wAbs, wLvlVol]; omega))
            (Or.inr (by dsimp [wPeelStk, wLvlVol]; omega)),
            hmf1 (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + cfg.H) (Or.inr (by omega)), hinv.lvlVol_H])
        (fun ℓ h1 hH => by
          rw [hpr1' (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) (Or.inr (by dsimp [wAbs, wLvlVol]; omega))
            (Or.inr (by dsimp [wPeelStk, wLvlVol]; omega)),
            hmf1 (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) (Or.inr (by omega)),
            hinv.lvlVol_eq ℓ h1 hH, hs'_inR, hs'_h])
        hinv.buckets_nodup
        (fun ℓ h1 hH x => by rw [hs'_inR, hs'_h]; exact hinv.buckets_mem ℓ h1 hH x)
        (fun ℓ h1 hH => by
          rw [hpr1' (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ) (Or.inr (by dsimp [wAbs, wLvlHead]; omega))
            (Or.inr (by dsimp [wPeelStk, wLvlHead]; omega)),
            hmf1 (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ) (Or.inr (by dsimp [wLvlVol, wLvlHead]; omega))]
          refine doublyLinked_congr_disjoint
            (fun y hy => by
              have hyn := doublyLinked_mem_lt (hinv.buckets_dl ℓ h1 hH) hy
              exact hagree_mid_peel (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H + y)
                (by dsimp [wLvlNext]; omega) (by dsimp [wLvlNext, wLvlPrev]; omega))
            (fun y hy => by
              have hyn := doublyLinked_mem_lt (hinv.buckets_dl ℓ h1 hH) hy
              exact hagree_mid_peel (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H + y)
                (by dsimp [wLvlNext, wLvlPrev]; omega) (by dsimp [wLvlPrev]; omega))
            (hinv.buckets_dl ℓ h1 hH))
        (fun x hx => by
          by_cases hxr : s'.inR x = true
          · exact ex_le_bound_of_inR hinv.cfg_X hinv.cfg_valid hs'_inv hxr
          · have hxs : s'.ex x = s.ex x := by
              have hsR : s.inR x = false := by rw [← hs'_inR]; exact Bool.eq_false_iff.mpr hxr
              have hne1 : x ≠ u := fun h => by rw [h, huR] at hsR; simp at hsR
              have hne2 : x ≠ nbr := fun h => by rw [h, hadm.1] at hsR; simp at hsR
              rw [hs'_ex]; dsimp [ex']; simp [hne1, hne2]
            rw [hxs]; exact hinv.ex_bound x hx)
        hs'_inv hs'_pq
    by_cases hlt : s.ex u < rc
    · have hrc_nle : ¬ (rc ≤ s.ex u) := by omega
      have hs'_eq : s' =
          { inR := s.inR, h := s.h, cur := s.cur, abs := s.abs, ex := ex', degR := s.degR,
            flow := flow',
            active := if s.inActive nbr = true then restAct else nbr :: restAct,
            inActive := fun x => if x = u then false else if x = nbr then true else s.inActive x,
            peelQ := s.peelQ, steps := s.steps + 1 } := by
        dsimp only [s', pushFlowStep, ex', flow', δ, rc, nbr, dir, idx, q]
        simp only [show ¬ (↑cfg.C_cap - flowDir s.flow ((cfg.incEdges u).getD (s.cur u) (0, false, 0)).1
            ((cfg.incEdges u).getD (s.cur u) (0, false, 0)).2.1).toNat ≤ s.ex u from hrc_nle, ↓reduceIte]
      have hat1 : st1.regs prActTop = restAct.length + 1 := by
        rw [hr_le prActTop (by decide), hinv.reg_actTop, hact]; simp
      have hrest_lt2w : restAct.length < 2 ^ w := by
        have := hinv.active_len_le; rw [hact] at this
        unfold PruneWordBound at hw; simp at this; omega
      let regs2 := Function.update st1.regs prActTop restAct.length
      let st2 : State := { mem := st1.mem, regs := regs2, pos := st1.pos }
      have hsa1 : Runs w p ω (.assign prActTop (.bin .sub (.reg prActTop) (.const 1))) st1
          .normal st2 4 :=
        runs_assign_iff.mpr ⟨restAct.length,
          Expr.eval_bin (eval_reg_eq w st1 prActTop hat1) (Expr.eval_const (by omega))
            (by simp [BinOp.eval]; exact hrest_lt2w),
          rfl, by simp [st2, regs2], by simp [Expr.size]⟩
      let m3 := Function.update st1.mem (wInAct workAddr cfg.G.n cfg.G.m cfg.H + u) 0
      let st3 : State := { mem := m3, regs := regs2, pos := st1.pos }
      have hia_addr : wInAct workAddr cfg.G.n cfg.G.m cfg.H + u < 2 ^ w :=
        hlt2w _ (by unfold pruneWorkSpace; dsimp [wInAct]; omega)
      obtain ⟨o_a2, stx_a2, c_a2, hsa2, ⟨ho_a2, hstx_a2⟩, hc_a2⟩ := runs_store_le
        (w := w) (p := p) (ω := ω) (st := st2) (x := wInAct workAddr cfg.G.n cfg.G.m cfg.H + u) (v := 0)
        (k := 0) (T := 5) (Q := fun o s => o = .normal ∧ s = st3)
        (eval_add_eq w st2 prInAct prU
          (by dsimp [st2, regs2]; rw [Function.update_of_ne (by decide)]; exact hregs1.reg_inAct)
          (by dsimp [st2, regs2]; rw [Function.update_of_ne (by decide)]; exact hr_u) hia_addr)
        (Expr.eval_const (by omega)) ⟨rfl, rfl⟩ (by simp [Expr.size])
      rcases ho_a2 with rfl; rcases hstx_a2 with rfl
      let inAct2 := fun x => if x = u then false else s.inActive x
      have hlen_sub : (if inAct2 nbr = true then restAct else nbr :: restAct).length ≤ cfg.G.n := by
        have hia2 : inAct2 nbr = s.inActive nbr := by simp [inAct2, hnbr_ne]
        simpa [hs'_eq, hia2] using hact'_len
      have hpush := pushActW_triple (p := p) restAct inAct2 st3 hw hnbr_lt
        (by dsimp [st3, regs2]; rw [Function.update_of_ne (by decide)]; exact hr_w)
        (by dsimp [st3, regs2]; rw [Function.update_of_ne (by decide)]; exact hregs1.reg_inAct)
        (by dsimp [st3, regs2]; rw [Function.update_of_ne (by decide)]; exact hregs1.reg_actStk)
        (by dsimp [st3, regs2]; rw [Function.update_self])
        (fun x hx => by
          dsimp [st3, m3]
          by_cases hxu : x = u
          · subst hxu; simp [inAct2]
          · rw [Function.update_of_ne (by omega),
              hother1 (wInAct workAddr cfg.G.n cfg.G.m cfg.H + x)
                (Or.inr (by dsimp [wDegR, wInAct]; omega))
                (by dsimp [wFlowEnc, wInAct]; omega),
              hinv.inAct_eq x hx]
            simp [inAct2, hxu])
        (fun i hi => by
          dsimp [st3, m3]
          have hi_n : i < cfg.G.n := by
            have := hinv.active_len_le; rw [hact] at this; simp at this; omega
          rw [Function.update_of_ne (by dsimp [wInAct, wActStk]; omega),
            hother1 (wActStk workAddr cfg.G.n cfg.G.m cfg.H + i)
              (Or.inr (by dsimp [wDegR, wActStk]; omega))
              (by dsimp [wFlowEnc, wActStk]; omega),
            hinv.actStk_eq i (by rw [hact]; simp; omega), hact]
          have hget_rhs : (u :: restAct).getD ((u :: restAct).length - 1 - i) 0 =
              restAct.getD (restAct.length - 1 - i) 0 := by
            have hk : (u :: restAct).length - 1 - i = (restAct.length - 1 - i) + 1 := by simp; omega
            rw [hk]; rfl
          rw [hget_rhs])
        hlen_sub
      rcases hpush st3 ω rfl with ⟨o4, st4, c4, hr4, hq4, hc4⟩
      cases o4 with
      | returned => exact False.elim hq4
      | normal =>
        rcases hq4 with ⟨hreg4, hat4, hpos4, hmf4, hia4, has4⟩
        have hr_4 : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st4.regs r = st₀.regs r := by
          intro r hr hAT hPT
          rw [hreg4 r (le_adjH_ne_work hr).2.1 hAT]
          dsimp [st3, regs2]; rw [Function.update_of_ne hAT]; exact hr_le r hr
        have hpt_4 : st4.regs prPeelTop = st₀.regs prPeelTop := by
          rw [hreg4 prPeelTop (by decide) (by decide)]
          dsimp [st3, regs2]; rw [Function.update_of_ne (by decide)]
          exact hr_le prPeelTop (by decide)
        have hpr14 : PreservedOutside2 st1.mem st4.mem (wCur workAddr cfg.G.n cfg.G.m cfg.H)
            (wAbs workAddr cfg.G.n cfg.G.m cfg.H) (wInAct workAddr cfg.G.n cfg.G.m cfg.H)
            (wPeelStk workAddr cfg.G.n cfg.G.m cfg.H) := by
          intro a _ ha2
          rw [hmf4 a ha2]
          dsimp [st3, m3]; rw [Function.update_of_ne (by dsimp [wInAct, wPeelStk] at *; omega)]
        have hs'_act_eq : s'.active = if inAct2 nbr = true then restAct else nbr :: restAct := by
          rw [hs'_eq]; simp [inAct2, hnbr_ne]
        have hs'_inAct_eq : s'.inActive = fun x => if x = nbr then true else inAct2 x := by
          funext x; rw [hs'_eq]
          by_cases hxn : x = nbr
          · subst hxn; simp [inAct2, hnbr_ne]
          · simp [inAct2, hxn]
        have hpost := mk_post st4 hr_4 (hpos4.trans hpos1) (hat4.trans (by rw [hs'_act_eq]))
          (by rw [hpt_4, hinv.reg_peelTop, hs'_peel]) hpr14
          (fun x hx => by
            rw [hmf4 (wCur workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inl (by dsimp [wCur, wInAct]; omega))]
            dsimp [st3, m3]
            rw [Function.update_of_ne (by dsimp [wCur, wInAct]; omega),
              hother1 (wCur workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inl (by dsimp [wCur, wEx]; omega))
                (by dsimp [wCur, wFlowEnc]; omega), hinv.cur_eq x hx, show s'.cur = s.cur by rw [hs'_eq]])
          (fun x hx => by rw [hs'_inAct_eq]; exact hia4 x hx)
          (fun i hi => by rw [hs'_act_eq] at hi ⊢; exact has4 i hi)
        dsimp only at hc4 ⊢
        refine ⟨.normal, st4, 3 + (4 + (c_a2 + c4 + 1) + 1) + 1,
          runs_cond_iff.mpr ⟨1, _, ?_, ?_, rfl⟩, hpost, by omega⟩
        · simpa [hlt] using hcond_ev
        · simpa [seqStmts] using runs_seq hsa1 (runs_seq hsa2 hr4)
    · have hrc_le : rc ≤ s.ex u := by omega
      have hs'_eq : s' =
          { inR := s.inR, h := s.h, cur := fun x => if x = u then s.cur u + 1 else s.cur x,
            abs := s.abs, ex := ex', degR := s.degR, flow := flow',
            active := if s.inActive nbr = true then s.active else nbr :: s.active,
            inActive := fun x => if x = nbr then true else s.inActive x,
            peelQ := s.peelQ, steps := s.steps + 1 } := by
        dsimp only [s', pushFlowStep, ex', flow', δ, rc, nbr, dir, idx, q]
        simp only [show (↑cfg.C_cap - flowDir s.flow ((cfg.incEdges u).getD (s.cur u) (0, false, 0)).1
            ((cfg.incEdges u).getD (s.cur u) (0, false, 0)).2.1).toNat ≤ s.ex u from hrc_le, ↓reduceIte]
      have hcur1 : st1.mem (wCur workAddr cfg.G.n cfg.G.m cfg.H + u) = s.cur u := by
        rw [hother1 (wCur workAddr cfg.G.n cfg.G.m cfg.H + u) (Or.inl (by dsimp [wCur, wEx]; omega))
          (by dsimp [wCur, wFlowEnc]; omega), hinv.cur_eq u huN]
      have hcur_le2m : s.cur u + 1 ≤ 2 * cfg.G.m := by
        have hsub := csrOff_le_two_mul_m cfg.G (u + 1)
        rw [csrOff_succ, ← hinv.cfg_incEdges u] at hsub; omega
      have hcur1_lt2w : s.cur u + 1 < 2 ^ w := by unfold PruneWordBound at hw; omega
      have hcur_addr : wCur workAddr cfg.G.n cfg.G.m cfg.H + u < 2 ^ w :=
        hlt2w _ (by unfold pruneWorkSpace; dsimp [wCur]; omega)
      let regs2 := Function.update st1.regs prTmp3 (s.cur u)
      let st2 : State := { mem := st1.mem, regs := regs2, pos := st1.pos }
      have hsb1 : Runs w p ω (.assign prTmp3 (.load (.bin .add (.reg prCur) (.reg prU)))) st1
          .normal st2 5 :=
        runs_assign_iff.mpr ⟨s.cur u,
          eval_load_add_eq w st1 prCur prU hregs1.reg_cur hr_u hcur_addr hcur1,
          rfl, rfl, by simp [Expr.size]⟩
      let m3 := Function.update st1.mem (wCur workAddr cfg.G.n cfg.G.m cfg.H + u) (s.cur u + 1)
      let st3 : State := { mem := m3, regs := regs2, pos := st1.pos }
      obtain ⟨o_b2, stx_b2, c_b2, hsb2, ⟨ho_b2, hstx_b2⟩, hc_b2⟩ := runs_store_le
        (w := w) (p := p) (ω := ω) (st := st2) (x := wCur workAddr cfg.G.n cfg.G.m cfg.H + u) (v := s.cur u + 1)
        (k := 0) (T := 7) (Q := fun o s => o = .normal ∧ s = st3)
        (eval_add_eq w st2 prCur prU
          (by dsimp [st2, regs2]; rw [Function.update_of_ne (by decide)]; exact hregs1.reg_cur)
          (by dsimp [st2, regs2]; rw [Function.update_of_ne (by decide)]; exact hr_u) hcur_addr)
        (Expr.eval_bin (op := .add) (eval_reg_eq w st2 prTmp3 (by dsimp [st2, regs2]; simp))
          (Expr.eval_const (by omega)) (by simp [BinOp.eval]; exact hcur1_lt2w))
        ⟨rfl, rfl⟩ (by simp [Expr.size])
      rcases ho_b2 with rfl; rcases hstx_b2 with rfl
      have hlen_sub : (if s.inActive nbr = true then s.active else nbr :: s.active).length ≤ cfg.G.n := by
        simpa [hs'_eq] using hact'_len
      have hpush := pushActW_triple (p := p) s.active s.inActive st3 hw hnbr_lt
        (by dsimp [st3, regs2]; rw [Function.update_of_ne (by decide)]; exact hr_w)
        (by dsimp [st3, regs2]; rw [Function.update_of_ne (by decide)]; exact hregs1.reg_inAct)
        (by dsimp [st3, regs2]; rw [Function.update_of_ne (by decide)]; exact hregs1.reg_actStk)
        (by dsimp [st3, regs2]; rw [Function.update_of_ne (by decide)]; exact (hr_le prActTop (by decide)).trans hinv.reg_actTop)
        (fun x hx => by
          dsimp [st3, m3]
          rw [Function.update_of_ne (by dsimp [wCur, wInAct]; omega),
            hother1 (wInAct workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inr (by dsimp [wDegR, wInAct]; omega))
              (by dsimp [wFlowEnc, wInAct]; omega), hinv.inAct_eq x hx])
        (fun i hi => by
          dsimp [st3, m3]
          have hi_n : i < cfg.G.n := lt_of_lt_of_le hi hinv.active_len_le
          rw [Function.update_of_ne (by dsimp [wCur, wActStk]; omega),
            hother1 (wActStk workAddr cfg.G.n cfg.G.m cfg.H + i) (Or.inr (by dsimp [wDegR, wActStk]; omega))
              (by dsimp [wFlowEnc, wActStk]; omega), hinv.actStk_eq i hi])
        hlen_sub
      rcases hpush st3 ω rfl with ⟨o4, st4, c4, hr4, hq4, hc4⟩
      cases o4 with
      | returned => exact False.elim hq4
      | normal =>
        rcases hq4 with ⟨hreg4, hat4, hpos4, hmf4, hia4, has4⟩
        have hr_4 : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st4.regs r = st₀.regs r := by
          intro r hr hAT hPT
          rw [hreg4 r (le_adjH_ne_work hr).2.1 hAT]
          dsimp [st3, regs2]; rw [Function.update_of_ne (le_adjH_ne_work hr).2.2.1]; exact hr_le r hr
        have hpt_4 : st4.regs prPeelTop = st₀.regs prPeelTop := by
          rw [hreg4 prPeelTop (by decide) (by decide)]
          dsimp [st3, regs2]; rw [Function.update_of_ne (by decide)]
          exact hr_le prPeelTop (by decide)
        have hpr14 : PreservedOutside2 st1.mem st4.mem (wCur workAddr cfg.G.n cfg.G.m cfg.H)
            (wAbs workAddr cfg.G.n cfg.G.m cfg.H) (wInAct workAddr cfg.G.n cfg.G.m cfg.H)
            (wPeelStk workAddr cfg.G.n cfg.G.m cfg.H) := by
          intro a ha1 ha2
          rw [hmf4 a ha2]
          dsimp [st3, m3]; rw [Function.update_of_ne (by dsimp [wCur, wAbs] at *; omega)]
        have hs'_act_eq : s'.active = if s.inActive nbr = true then s.active else nbr :: s.active := by
          rw [hs'_eq]
        have hs'_inAct_eq : s'.inActive = fun x => if x = nbr then true else s.inActive x := by
          rw [hs'_eq]
        have hpost := mk_post st4 hr_4 (hpos4.trans hpos1) (hat4.trans (by rw [hs'_act_eq]))
          (by rw [hpt_4, hinv.reg_peelTop, hs'_peel]) hpr14
          (fun x hx => by
            rw [hmf4 (wCur workAddr cfg.G.n cfg.G.m cfg.H + x)
              (Or.inl (by dsimp [wCur, wInAct]; omega))]
            dsimp [st3, m3]; rw [hs'_eq]
            by_cases hxu : x = u
            · subst hxu; rw [Function.update_self]; simp
            · rw [Function.update_of_ne (by omega),
                hother1 (wCur workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inl (by dsimp [wCur, wEx]; omega))
                  (by dsimp [wCur, wFlowEnc]; omega), hinv.cur_eq x hx]
              simp [hxu])
          (fun x hx => by rw [hs'_inAct_eq]; exact hia4 x hx)
          (fun i hi => by rw [hs'_act_eq] at hi ⊢; exact has4 i hi)
        dsimp only at hc4 ⊢
        refine ⟨.normal, st4, 3 + (5 + (c_b2 + c4 + 1) + 1) + 1,
          runs_cond_iff.mpr ⟨0, _, ?_, ?_, rfl⟩, hpost, by omega⟩
        · simpa [hlt] using hcond_ev
        · simpa [seqStmts] using runs_seq hsb1 (runs_seq hsb2 hr4)
  exact Triple.seq hpre htail (fun _ _ h => False.elim h) (fun _ _ _ _ h => False.elim h)
    (fun _ _ _ _ => by omega)


end MinCostFlow.Expander
