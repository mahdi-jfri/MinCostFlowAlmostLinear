module

public import MinCostFlow.Expander.PruningPushFlowProg

/-!
# Relabel Step Triple
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

/-! ### Section 6: `relabelStep` -/

lemma volAtLevel_relabel_single {cfg : PruneCfg} {inR : ℕ → Bool} {h : ℕ → ℕ}
    {u ℓ : ℕ} (hX : cfg.X = Finset.range cfg.G.n) (hu : u < cfg.G.n) (huR : inR u = true) :
    let h' := fun x => if x = u then h u + 1 else h x
    volAtLevel cfg inR h' ℓ =
      if ℓ = h u + 1 then volAtLevel cfg inR h ℓ + cfg.degX u
      else if ℓ = h u then volAtLevel cfg inR h ℓ - cfg.degX u
      else volAtLevel cfg inR h ℓ := by
  intro h'
  have huX : u ∈ cfg.X := by rw [hX]; exact Finset.mem_range.mpr hu
  have hsum_old := Finset.add_sum_erase cfg.X
    (fun x => if (inR x && decide (h x = ℓ)) = true then cfg.degX x else 0) huX
  have hsum_new := Finset.add_sum_erase cfg.X
    (fun x => if (inR x && decide (h' x = ℓ)) = true then cfg.degX x else 0) huX
  have herase :
      (∑ x ∈ cfg.X.erase u, if (inR x && decide (h' x = ℓ)) = true then cfg.degX x else 0) =
      (∑ x ∈ cfg.X.erase u, if (inR x && decide (h x = ℓ)) = true then cfg.degX x else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hne : x ≠ u := (Finset.mem_erase.mp hx).1
    simp [h', hne]
  dsimp [volAtLevel]
  rw [← hsum_new, ← hsum_old, herase]
  by_cases h1 : ℓ = h u + 1
  · subst h1
    simp only [h', ↓reduceIte, huR, Bool.true_and, decide_eq_true_eq,
      show (h u = h u + 1) ↔ False by simp]
    omega
  · by_cases h2 : ℓ = h u
    · subst h2
      simp only [h', h1, ↓reduceIte, huR, Bool.true_and, decide_eq_true_eq,
        show (h u + 1 = h u) ↔ False by simp]
      omega
    · simp only [h', h1, h2, ↓reduceIte, huR, Bool.true_and, decide_eq_true_eq,
        show (h u + 1 = ℓ) ↔ False by simp [Ne.symm h1],
        show (h u = ℓ) ↔ False by simp [Ne.symm h2]]

def relabelStepStmt : Stmt :=
  seqStmts
    [ .assign prTmp2 (.load (.bin .add (.reg prHArr) (.reg prU)))
    , .cond (.bin .lt (.const 0) (.reg prTmp2)) unlinkLvlStmt .nop
    , .assign prTmp2 (.bin .add (.load (.bin .add (.reg prHArr) (.reg prU))) (.const 1))
    , .store (.bin .add (.reg prHArr) (.reg prU)) (.reg prTmp2)
    , .store (.bin .add (.reg prCur) (.reg prU)) (.const 0)
    , linkLvlStmt ]

lemma relabelStepStmt_noRand : relabelStepStmt.NoRand := by
  dsimp [relabelStepStmt, seqStmts, Stmt.NoRand]
  simp [unlinkLvlStmt_noRand, linkLvlStmt_noRand]

theorem relabelStep_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr u : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} (st₀ : State)
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (huR : s.inR u = true)
    (hex_pos : 0 < s.ex u)
    (habs : s.abs u = cfg.degX u)
    (hcur : s.cur u = (cfg.incEdges u).length)
    (hhH : s.h u + 1 < cfg.H)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr cfg.G.n cfg.G.m cfg.H cfg.G.encode.length) :
    let s' := relabelStep u s
    let buckets1 := if 1 ≤ s.h u then fun ℓ => if ℓ = s.h u then (buckets ℓ).erase u else buckets ℓ else buckets
    let buckets' := fun ℓ => if ℓ = s.h u + 1 then u :: buckets1 ℓ else buckets1 ℓ
    Triple w p (fun st => st = st₀ ∧ st.regs prU = u) relabelStepStmt
      (normalPost fun st' =>
        (∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
          st'.pos = st₀.pos ∧
            PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + cfg.G.n)
                (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
              PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s' buckets' st')
      (fun _ => 230) := by
  intro s' buckets1 buckets'
  have hwb := pruneWordBound_pos hw
  have hlt2w : ∀ k, k < workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H → k < 2 ^ w := fun k hk => by
    unfold PruneWordBound at hw; omega
  have huN : u < cfg.G.n := by
    have := hinv.prune_inv.inR_sub u huR
    rw [hinv.cfg_X] at this; exact Finset.mem_range.mp this
  have hstep_inv := relabelStep_inv_pot_pub hinv.cfg_valid hinv.prune_inv huR hex_pos habs hcur hhH
  have hs'_inv : PruningInv cfg s' := hstep_inv.1
  have hs'_pq : PeelQInv cfg s' := hinv.peelQ_inv
  intro st ω ⟨hst, hru⟩
  subst st
  let r1 := Function.update st₀.regs prTmp2 (s.h u)
  let st1 : State := { mem := st₀.mem, regs := r1, pos := st₀.pos }
  have hh1_lt2w : s.h u + 1 < 2 ^ w := by unfold PruneWordBound at hw; omega
  have hha_addr : wHArr workAddr cfg.G.n cfg.G.m cfg.H + u < 2 ^ w :=
    hlt2w _ (by unfold pruneWorkSpace; dsimp [wHArr]; omega)
  have hs1 : Runs w p ω (.assign prTmp2 (.load (.bin .add (.reg prHArr) (.reg prU)))) st₀
      .normal st1 5 :=
    runs_assign_iff.mpr ⟨s.h u, eval_load_add_eq w st₀ prHArr prU hinv.reg_hArr hru hha_addr (hinv.h_eq u huN),
      rfl, rfl, by simp [Expr.size]⟩
  have hst1_inv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st1 :=
    mkPruneMemInv hinv hdisj (fun r hr _ _ => by dsimp [st1, r1]; rw [Function.update_of_ne (le_adjH_ne_work hr).2.1])
      (preservedOutside2_refl _ _ _ _ _)
      (by dsimp [st1, r1]; rw [Function.update_of_ne (by decide)]; exact hinv.reg_actTop)
      (by dsimp [st1, r1]; rw [Function.update_of_ne (by decide)]; exact hinv.reg_peelTop)
      hinv.outR_eq hinv.h_eq hinv.cur_eq hinv.abs_eq hinv.ex_eq hinv.degR_eq hinv.inAct_eq
      hinv.actStk_eq hinv.peelStk_eq hinv.flowEnc_eq hinv.lvlVol_H hinv.lvlVol_eq
      hinv.buckets_nodup hinv.buckets_mem hinv.buckets_dl hinv.ex_bound hinv.prune_inv hinv.peelQ_inv
  have hs2 : ∃ st2 c2, c2 ≤ 84 ∧
      Runs w p ω (.cond (.bin .lt (.const 0) (.reg prTmp2)) unlinkLvlStmt .nop) st1 .normal st2 c2 ∧
      (∀ r, r ≠ prTmp1 → r ≠ prTmp2 → r ≠ prTmp3 → r ≠ prSuf → st2.regs r = st₀.regs r) ∧
      st2.pos = st₀.pos ∧
      MemFrame st₀.mem st2.mem (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H) (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + cfg.H + 1) ∧
      (∀ k, wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H + cfg.G.n ≤ k → k < wLvlVol workAddr cfg.G.n cfg.G.m cfg.H → st2.mem k = st₀.mem k) ∧
      st2.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + cfg.H) = 0 ∧
      (∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
        st2.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) =
          (if 1 ≤ s.h u ∧ ℓ = s.h u then st₀.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) - cfg.degX u
           else st₀.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ))) ∧
      (∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
        DoublyLinked st2.mem (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H) (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H) cfg.G.n
          (buckets1 ℓ) cfg.G.n (st2.mem (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ))) := by
    have hcond : Expr.eval w st1 (.bin .lt (.const 0) (.reg prTmp2)) =
        some (if 0 < s.h u then 1 else 0) :=
      Expr.eval_bin (Expr.eval_const (by omega)) (eval_reg_eq w st1 prTmp2 (by dsimp [st1, r1]; rw [Function.update_self]))
        (by simp [BinOp.eval]; split_ifs <;> omega)
    by_cases hhpos : 1 ≤ s.h u
    · have hunlink := unlinkLvl_triple (p := p) (gAddr := gAddr) (csrAddr := csrAddr)
        (inBAddr := inBAddr) (outRAddr := outRAddr) (buckets := buckets) st1 hw huN huR hhpos
      rcases hunlink st1 ω ⟨rfl, hst1_inv, by dsimp [st1, r1]; rw [Function.update_of_ne (by decide)]; exact hru⟩ with
        ⟨o2, st2, c2, hr2, hq2, hc2⟩
      cases o2 with
      | returned => exact False.elim hq2
      | normal =>
        rcases hq2 with ⟨hreg2, hpos2, hbmp2, hvol2, hdl_other, hdl_er⟩
        dsimp only at hc2
        refine ⟨st2, 3 + c2 + 1, by omega, runs_cond_iff.mpr ⟨1, c2, ?_, ?_, by simp [Expr.size]⟩,
          ?_, hpos2, hbmp2.1, hbmp2.2.1, ?_, ?_, ?_⟩
        · simpa [show 0 < s.h u by omega] using hcond
        · simpa [show 0 < s.h u by omega] using hr2
        · intro r h1 h2 h3 h4; rw [hreg2 r h1 h2 h3 h4]; dsimp [st1, r1]; rw [Function.update_of_ne h2]
        · have hneH : cfg.H ≠ s.h u := by omega
          rw [(hbmp2.2.2 cfg.H le_rfl hneH).1]; exact hinv.lvlVol_H
        · intro ℓ h1 hH
          by_cases heq : ℓ = s.h u
          · subst heq; simp only [hhpos, ↓reduceIte, true_and]; exact hvol2
          · simp only [hhpos, heq, and_false, ↓reduceIte]; exact (hbmp2.2.2 ℓ (by omega) heq).1
        · intro ℓ h1 hH
          by_cases heq : ℓ = s.h u
          · subst heq; simp only [buckets1, hhpos, ↓reduceIte]; exact hdl_er
          · simp only [buckets1, hhpos, heq, ↓reduceIte]; exact hdl_other ℓ h1 hH heq
    · have hh0 : s.h u = 0 := by omega
      refine ⟨st1, 5, by omega, runs_cond_iff.mpr ⟨0, 1, ?_, ?_, by simp [Expr.size]⟩,
        ?_, rfl, fun _ _ => rfl, fun _ _ _ => rfl, hinv.lvlVol_H, ?_, ?_⟩
      · simpa [hh0] using hcond
      · simpa [hh0] using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
      · intro r _ h2 _ _; dsimp [st1, r1]; rw [Function.update_of_ne h2]
      · intro ℓ h1 hH; dsimp [st1]; simp [hh0]
      · intro ℓ h1 hH; simp only [buckets1, hhpos, ↓reduceIte]; exact hinv.buckets_dl ℓ h1 hH
  rcases hs2 with ⟨st2, c2, hc2, hrs2, hreg2, hpos2, hmf2, hmid2, hlvlH2, hlvl2, hdl2⟩
  let r3 := Function.update st2.regs prTmp2 (s.h u + 1)
  let st3 : State := { mem := st2.mem, regs := r3, pos := st2.pos }
  have hst2_h : st2.mem (wHArr workAddr cfg.G.n cfg.G.m cfg.H + u) = s.h u := by
    rw [hmf2 (wHArr workAddr cfg.G.n cfg.G.m cfg.H + u) (Or.inl (by dsimp [wHArr, wLvlNext]; omega)), hinv.h_eq u huN]
  have hs3 : Runs w p ω (.assign prTmp2 (.bin .add (.load (.bin .add (.reg prHArr) (.reg prU))) (.const 1)))
      st2 .normal st3 7 :=
    runs_assign_iff.mpr ⟨s.h u + 1,
      Expr.eval_bin
        (eval_load_add_eq w st2 prHArr prU
          (by rw [hreg2 prHArr (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_hArr)
          (by rw [hreg2 prU (by decide) (by decide) (by decide) (by decide)]; exact hru) hha_addr hst2_h)
        (Expr.eval_const (by omega)) (by simp [BinOp.eval]; exact hh1_lt2w),
      rfl, rfl, by simp [Expr.size]⟩
  let m4 := Function.update st2.mem (wHArr workAddr cfg.G.n cfg.G.m cfg.H + u) (s.h u + 1)
  let st4 : State := { mem := m4, regs := r3, pos := st2.pos }
  obtain ⟨o4, stx4, c4, hs4, ⟨ho4, hstx4⟩, hc4⟩ := runs_store_le
    (w := w) (p := p) (ω := ω) (st := st3) (x := wHArr workAddr cfg.G.n cfg.G.m cfg.H + u) (v := s.h u + 1)
    (k := 0) (T := 6) (Q := fun o s => o = .normal ∧ s = st4)
    (eval_add_eq w st3 prHArr prU
      (by dsimp [st3, r3]; rw [Function.update_of_ne (by decide), hreg2 prHArr (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_hArr)
      (by dsimp [st3, r3]; rw [Function.update_of_ne (by decide), hreg2 prU (by decide) (by decide) (by decide) (by decide)]; exact hru)
      hha_addr)
    (eval_reg_eq w st3 prTmp2 (by dsimp [st3, r3]; rw [Function.update_self])) ⟨rfl, rfl⟩ (by simp [Expr.size])
  rcases ho4 with rfl; rcases hstx4 with rfl
  let m5 := Function.update m4 (wCur workAddr cfg.G.n cfg.G.m cfg.H + u) 0
  let st5 : State := { mem := m5, regs := r3, pos := st2.pos }
  have hcur_addr : wCur workAddr cfg.G.n cfg.G.m cfg.H + u < 2 ^ w :=
    hlt2w _ (by unfold pruneWorkSpace; dsimp [wCur]; omega)
  obtain ⟨o5, stx5, c5, hs5, ⟨ho5, hstx5⟩, hc5⟩ := runs_store_le
    (w := w) (p := p) (ω := ω) (st := st4) (x := wCur workAddr cfg.G.n cfg.G.m cfg.H + u) (v := 0)
    (k := 0) (T := 6) (Q := fun o s => o = .normal ∧ s = st5)
    (eval_add_eq w st4 prCur prU
      (by dsimp [st4, r3]; rw [Function.update_of_ne (by decide), hreg2 prCur (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_cur)
      (by dsimp [st4, r3]; rw [Function.update_of_ne (by decide), hreg2 prU (by decide) (by decide) (by decide) (by decide)]; exact hru)
      hcur_addr)
    (Expr.eval_const (by omega)) ⟨rfl, rfl⟩ (by simp [Expr.size])
  rcases ho5 with rfl; rcases hstx5 with rfl
  have hℓ1 : 1 ≤ s.h u + 1 := by omega
  have hL_eq : buckets1 (s.h u + 1) = buckets (s.h u + 1) := by
    dsimp [buckets1]
    by_cases h1 : 1 ≤ s.h u
    · simp [h1]
    · simp [h1]
  have hL_nd : (buckets1 (s.h u + 1)).Nodup := by
    rw [hL_eq]; exact hinv.buckets_nodup _ hℓ1 hhH
  have huNotL : u ∉ buckets1 (s.h u + 1) := by
    rw [hL_eq]; intro hmem
    have := (hinv.buckets_mem _ hℓ1 hhH u).mp hmem
    omega
  have hst5_agree : ∀ k, wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤ k →
      k < wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + cfg.H + 1 →
      st5.mem k = st2.mem k := fun k hk1 _ => by
    dsimp [st5, m5, m4]
    rw [Function.update_of_ne (by dsimp [wCur, wLvlNext] at *; omega),
      Function.update_of_ne (by dsimp [wHArr, wLvlNext] at *; omega)]
  have hother_pre : ∀ ℓ', 1 ≤ ℓ' → ℓ' < cfg.H → ℓ' ≠ s.h u + 1 →
      u ∉ buckets1 ℓ' ∧ (∀ x ∈ buckets1 (s.h u + 1), x ∉ buckets1 ℓ') ∧
        DoublyLinked st5.mem (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H) (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H) cfg.G.n
          (buckets1 ℓ') cfg.G.n (st5.mem (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ')) := by
    intro ℓ' hℓ'1 hℓ'H hne'
    have hin_b1 : ∀ x, x ∈ buckets1 ℓ' → x ∈ buckets ℓ' ∧ (1 ≤ s.h u → ℓ' = s.h u → x ≠ u) := by
      intro x hx
      dsimp [buckets1] at hx
      by_cases h1 : 1 ≤ s.h u
      · by_cases heq : ℓ' = s.h u
        · subst heq; simp only [h1, ↓reduceIte] at hx
          have hx' := (List.Nodup.mem_erase_iff (hinv.buckets_nodup _ hℓ'1 hℓ'H)).mp hx
          exact ⟨hx'.2, fun _ _ => hx'.1⟩
        · simp only [h1, heq, ↓reduceIte] at hx; exact ⟨hx, fun _ h => absurd h heq⟩
      · simp only [h1, ↓reduceIte] at hx; exact ⟨hx, fun h _ => absurd h h1⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hu_mem
      obtain ⟨hu_b, hne_u⟩ := hin_b1 u hu_mem
      have hh_eq := ((hinv.buckets_mem ℓ' hℓ'1 hℓ'H u).mp hu_b).2.2
      exact hne_u (by omega) hh_eq.symm rfl
    · intro x hxL hx_mem
      rw [hL_eq] at hxL
      have hx1 := ((hinv.buckets_mem _ hℓ1 hhH x).mp hxL).2.2
      obtain ⟨hx_b, _⟩ := hin_b1 x hx_mem
      have hx2 := ((hinv.buckets_mem _ hℓ'1 hℓ'H x).mp hx_b).2.2
      omega
    · rw [hst5_agree (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ') (by dsimp [wLvlNext, wLvlHead]; omega)
        (by dsimp [wHArr, wLvlHead]; omega)]
      refine doublyLinked_congr_disjoint
        (fun y hy => by
          have hyn : y < cfg.G.n := doublyLinked_mem_lt (hdl2 ℓ' hℓ'1 hℓ'H) hy
          exact hst5_agree (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H + y)
            (by dsimp [wHArr, wLvlNext]; omega) (by dsimp [wLvlNext, wLvlHead]; omega))
        (fun y hy => by
          have hyn : y < cfg.G.n := doublyLinked_mem_lt (hdl2 ℓ' hℓ'1 hℓ'H) hy
          exact hst5_agree (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H + y)
            (by dsimp [wLvlNext, wLvlPrev]; omega) (by dsimp [wLvlPrev, wLvlHead]; omega))
        (hdl2 ℓ' hℓ'1 hℓ'H)
  have hdl_L5 : DoublyLinked st5.mem (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H) (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H) cfg.G.n
      (buckets1 (s.h u + 1)) cfg.G.n (st5.mem (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + (s.h u + 1))) := by
    rw [hst5_agree (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + (s.h u + 1)) (by dsimp [wLvlNext, wLvlHead]; omega)
      (by dsimp [wHArr, wLvlHead]; omega)]
    refine doublyLinked_congr_disjoint
      (fun y hy => by
        have hyn : y < cfg.G.n := doublyLinked_mem_lt (hdl2 (s.h u + 1) hℓ1 hhH) hy
        exact hst5_agree (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H + y)
          (by dsimp [wHArr, wLvlNext]; omega) (by dsimp [wLvlNext, wLvlHead]; omega))
      (fun y hy => by
        have hyn : y < cfg.G.n := doublyLinked_mem_lt (hdl2 (s.h u + 1) hℓ1 hhH) hy
        exact hst5_agree (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H + y)
          (by dsimp [wLvlNext, wLvlPrev]; omega) (by dsimp [wLvlPrev, wLvlHead]; omega))
      (hdl2 (s.h u + 1) hℓ1 hhH)
  have hst5_vol : st5.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + (s.h u + 1)) = volAtLevel cfg s.inR s.h (s.h u + 1) := by
    rw [hst5_agree (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + (s.h u + 1)) (by dsimp [wLvlNext, wLvlVol]; omega)
      (by dsimp [wLvlVol, wLvlHead]; omega), hlvl2 (s.h u + 1) hℓ1 hhH]
    by_cases h1 : 1 ≤ s.h u
    · simp only [h1, show s.h u + 1 ≠ s.h u by omega, and_false, ↓reduceIte]
      exact hinv.lvlVol_eq (s.h u + 1) hℓ1 hhH
    · simp only [h1, false_and, ↓reduceIte]; exact hinv.lvlVol_eq (s.h u + 1) hℓ1 hhH
  have hst5_degX : st5.mem (wDegX workAddr cfg.G.n cfg.G.m cfg.H + u) = cfg.degX u := by
    dsimp [st5, m5, m4]
    rw [Function.update_of_ne (by dsimp [wDegX, wCur]; omega),
      Function.update_of_ne (by dsimp [wDegX, wHArr]; omega),
      hmf2 (wDegX workAddr cfg.G.n cfg.G.m cfg.H + u) (Or.inl (by dsimp [wDegX, wLvlNext]; omega)),
      hinv.degX_eq u huN]
  have hlink := linkLvl_triple_raw (p := p) (cfg.degX u) (buckets1 (s.h u + 1)) buckets1 st5
    hw hinv.cfg_valid.2.2.1 huN hℓ1 hhH hL_nd huNotL hother_pre
    (hinv.degX_le_two_mul_m huN) (hst5_vol ▸ hinv.volAtLevel_le_two_mul_m (s.h u + 1)) hst5_degX
    (by dsimp [st5, r3]; rw [Function.update_of_ne (by decide), hreg2 prN (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_n)
    (by dsimp [st5, r3]; rw [Function.update_of_ne (by decide), hreg2 prDegX (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_degX)
    (by dsimp [st5, r3]; rw [Function.update_of_ne (by decide), hreg2 prLvlNext (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_lvlNext)
    (by dsimp [st5, r3]; rw [Function.update_of_ne (by decide), hreg2 prLvlPrev (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_lvlPrev)
    (by dsimp [st5, r3]; rw [Function.update_of_ne (by decide), hreg2 prLvlVol (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_lvlVol)
    (by dsimp [st5, r3]; rw [Function.update_of_ne (by decide), hreg2 prLvlHead (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_lvlHead)
    hdl_L5
  rcases hlink st5 ω ⟨rfl, by dsimp [st5, r3]; rw [Function.update_of_ne (by decide), hreg2 prU (by decide) (by decide) (by decide) (by decide)]; exact hru,
    by dsimp [st5, r3]; rw [Function.update_self]⟩ with ⟨o6, st6, c6, hr6, hq6, hc6⟩
  cases o6 with
  | returned => exact False.elim hq6
  | normal =>
    rcases hq6 with ⟨hreg6, hpos6, hbmp6, hvol6, hdl6_o, hdl6_n⟩
    have hreg_fin : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st6.regs r = st₀.regs r := by
      intro r hr _ _
      have hne := le_adjH_ne_work hr
      rw [hreg6 r hne.1 hne.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.2.2.1]
      dsimp [st5, r3]; rw [Function.update_of_ne hne.2.1]
      exact hreg2 r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hat_6 : st6.regs prActTop = st₀.regs prActTop := by
      rw [hreg6 prActTop (by decide) (by decide) (by decide)]
      dsimp [st5, r3]; rw [Function.update_of_ne (by decide)]
      exact hreg2 prActTop (by decide) (by decide) (by decide) (by decide)
    have hpt_6 : st6.regs prPeelTop = st₀.regs prPeelTop := by
      rw [hreg6 prPeelTop (by decide) (by decide) (by decide)]
      dsimp [st5, r3]; rw [Function.update_of_ne (by decide)]
      exact hreg2 prPeelTop (by decide) (by decide) (by decide) (by decide)
    have hbelow_lvlNext : ∀ k, k < wLvlNext workAddr cfg.G.n cfg.G.m cfg.H → st6.mem k = st5.mem k := fun k hk =>
      hbmp6.1 k (Or.inl hk)
    have hpr_fin : PreservedOutside2 st₀.mem st6.mem outRAddr (outRAddr + cfg.G.n)
        (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) := by
      intro a _ ha2
      unfold pruneWorkSpace at ha2
      rw [hbmp6.1 a (by dsimp [wHArr, wLvlNext, wLvlHead] at *; omega)]
      dsimp [st5, m5, m4]
      rw [Function.update_of_ne (by dsimp [wCur, wHArr] at *; omega),
        Function.update_of_ne (by dsimp [wHArr] at *; omega),
        hmf2 a (by dsimp [wHArr, wLvlNext, wLvlHead] at *; omega)]
    have houtR_6 : ∀ x < cfg.G.n, st6.mem (outRAddr + x) = if s'.inR x = true then 1 else 0 := fun x hx => by
      have hdisj_or : outRAddr + x < workAddr ∨
          workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H ≤ outRAddr + x := by
        rcases hdisj.2.2.2.2.2.2 with hdw | hdw <;> omega
      unfold pruneWorkSpace at hdisj_or
      rw [hbmp6.1 (outRAddr + x) (by dsimp [wLvlNext, wLvlHead] at *; omega)]
      dsimp [st5, m5, m4]
      rw [Function.update_of_ne (by dsimp [wCur] at *; omega),
        Function.update_of_ne (by dsimp [wHArr] at *; omega),
        hmf2 (outRAddr + x) (by dsimp [wLvlNext, wLvlHead] at *; omega),
        hinv.outR_eq x hx]
      rfl
    have hmid_mem : ∀ k, wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H + cfg.G.n ≤ k →
        k < wLvlVol workAddr cfg.G.n cfg.G.m cfg.H → st6.mem k = st₀.mem k := fun k hk1 hk2 => by
      rw [hbmp6.2.1 k hk1 hk2]
      dsimp [st5, m5, m4]
      rw [Function.update_of_ne (by dsimp [wCur, wLvlPrev] at *; omega),
        Function.update_of_ne (by dsimp [wHArr, wLvlPrev] at *; omega)]
      exact hmid2 k hk1 hk2
    have hrun := runs_seq hs1 (runs_seq hrs2 (runs_seq hs3 (runs_seq hs4 (runs_seq hs5 hr6))))
    dsimp only at hc6 ⊢
    refine ⟨.normal, st6, _, hrun, ?_, by omega⟩
    refine ⟨hreg_fin, hpos6.trans hpos2, hpr_fin, ?_⟩
    refine mkPruneMemInv hinv hdisj hreg_fin hpr_fin
      (hat_6.trans hinv.reg_actTop) (hpt_6.trans hinv.reg_peelTop)
      houtR_6 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hs'_inv hs'_pq
    · intro x hx
      rw [hbelow_lvlNext (wHArr workAddr cfg.G.n cfg.G.m cfg.H + x) (by dsimp [wHArr, wLvlNext]; omega)]
      dsimp [st5, m5, m4]; rw [Function.update_of_ne (by dsimp [wHArr, wCur]; omega)]
      by_cases hxu : x = u
      · subst hxu; rw [Function.update_self]; simp [s', relabelStep]
      · rw [Function.update_of_ne (by omega),
          hmf2 (wHArr workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inl (by dsimp [wHArr, wLvlNext]; omega)),
          hinv.h_eq x hx]
        simp [s', relabelStep, hxu]
    · intro x hx
      rw [hbelow_lvlNext (wCur workAddr cfg.G.n cfg.G.m cfg.H + x) (by dsimp [wCur, wLvlNext]; omega)]
      dsimp [st5, m5, m4]
      by_cases hxu : x = u
      · subst hxu; rw [Function.update_self]; simp [s', relabelStep]
      · rw [Function.update_of_ne (by omega),
          Function.update_of_ne (by dsimp [wCur, wHArr]; omega),
          hmf2 (wCur workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inl (by dsimp [wCur, wLvlNext]; omega)),
          hinv.cur_eq x hx]
        simp [s', relabelStep, hxu]
    · intro x hx
      rw [hbelow_lvlNext (wAbs workAddr cfg.G.n cfg.G.m cfg.H + x) (by dsimp [wAbs, wLvlNext]; omega)]
      dsimp [st5, m5, m4]; rw [Function.update_of_ne (by dsimp [wAbs, wCur]; omega),
        Function.update_of_ne (by dsimp [wAbs, wHArr]; omega),
        hmf2 (wAbs workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inl (by dsimp [wAbs, wLvlNext]; omega)),
        hinv.abs_eq x hx]
      rfl
    · intro x hx
      rw [hbelow_lvlNext (wEx workAddr cfg.G.n cfg.G.m cfg.H + x) (by dsimp [wEx, wLvlNext]; omega)]
      dsimp [st5, m5, m4]; rw [Function.update_of_ne (by dsimp [wEx, wCur]; omega),
        Function.update_of_ne (by dsimp [wEx, wHArr]; omega),
        hmf2 (wEx workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inl (by dsimp [wEx, wLvlNext]; omega)),
        hinv.ex_eq x hx]
      rfl
    · intro x hx
      rw [hbelow_lvlNext (wDegR workAddr cfg.G.n cfg.G.m cfg.H + x) (by dsimp [wDegR, wLvlNext]; omega)]
      dsimp [st5, m5, m4]; rw [Function.update_of_ne (by dsimp [wDegR, wCur]; omega),
        Function.update_of_ne (by dsimp [wDegR, wHArr]; omega),
        hmf2 (wDegR workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inl (by dsimp [wDegR, wLvlNext]; omega)),
        hinv.degR_eq x hx]
      rfl
    · intro x hx
      rw [hbelow_lvlNext (wInAct workAddr cfg.G.n cfg.G.m cfg.H + x) (by dsimp [wInAct, wLvlNext]; omega)]
      dsimp [st5, m5, m4]; rw [Function.update_of_ne (by dsimp [wInAct, wCur]; omega),
        Function.update_of_ne (by dsimp [wInAct, wHArr]; omega),
        hmf2 (wInAct workAddr cfg.G.n cfg.G.m cfg.H + x) (Or.inl (by dsimp [wInAct, wLvlNext]; omega)),
        hinv.inAct_eq x hx]
      rfl
    · intro i hi
      have hi_n : i < cfg.G.n := lt_of_lt_of_le hi hinv.active_len_le
      rw [hbelow_lvlNext (wActStk workAddr cfg.G.n cfg.G.m cfg.H + i) (by dsimp [wActStk, wLvlNext]; omega)]
      dsimp [st5, m5, m4]; rw [Function.update_of_ne (by dsimp [wActStk, wCur]; omega),
        Function.update_of_ne (by dsimp [wActStk, wHArr]; omega),
        hmf2 (wActStk workAddr cfg.G.n cfg.G.m cfg.H + i) (Or.inl (by dsimp [wActStk, wLvlNext]; omega)),
        hinv.actStk_eq i hi]
      rfl
    · intro i hi
      dsimp only [s', relabelStep] at hi ⊢
      have hi_n : i < cfg.G.n := by
        have hsub : ∀ x ∈ s.peelQ, x ∈ Finset.range cfg.G.n := fun x hx => by
          rw [← hinv.cfg_X]; exact hinv.peelQ_inv.2.1 x hx
        have hpq_len : s.peelQ.length ≤ cfg.G.n := by
          calc s.peelQ.length = s.peelQ.toFinset.card := (List.toFinset_card_of_nodup hinv.peelQ_inv.1).symm
            _ ≤ (Finset.range cfg.G.n).card := Finset.card_le_card (fun x hx => hsub x (List.mem_toFinset.mp hx))
            _ = cfg.G.n := Finset.card_range cfg.G.n
        omega
      rw [hbelow_lvlNext (wPeelStk workAddr cfg.G.n cfg.G.m cfg.H + i) (by dsimp [wPeelStk, wLvlNext]; omega)]
      dsimp [st5, m5, m4]; rw [Function.update_of_ne (by dsimp [wPeelStk, wCur]; omega),
        Function.update_of_ne (by dsimp [wPeelStk, wHArr]; omega),
        hmf2 (wPeelStk workAddr cfg.G.n cfg.G.m cfg.H + i) (Or.inl (by dsimp [wPeelStk, wLvlNext]; omega)),
        hinv.peelStk_eq i hi]
    · intro k hk
      rw [hmid_mem (wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + k) (by dsimp [wLvlPrev, wFlowEnc]; omega)
        (by dsimp [wFlowEnc, wLvlVol]; omega), hinv.flowEnc_eq k hk]
      rfl
    · rw [(hbmp6.2.2 cfg.H le_rfl (by omega)).1,
        hst5_agree (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + cfg.H) (by dsimp [wLvlNext, wLvlVol]; omega)
          (by dsimp [wLvlVol, wLvlHead]; omega), hlvlH2]
    · intro ℓ h1 hH
      have hrelabel := volAtLevel_relabel_single (cfg := cfg) (inR := s.inR) (h := s.h) (u := u) (ℓ := ℓ)
        hinv.cfg_X huN huR
      dsimp only [s', relabelStep] at *
      rw [hrelabel]
      by_cases h_new : ℓ = s.h u + 1
      · subst h_new; simp only [↓reduceIte]
        rw [hvol6, hst5_vol]
      · simp only [h_new, ↓reduceIte]
        rw [(hbmp6.2.2 ℓ (by omega) h_new).1,
          hst5_agree (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) (by dsimp [wLvlNext, wLvlVol]; omega)
            (by dsimp [wLvlVol, wLvlHead]; omega),
          hlvl2 ℓ h1 hH]
        by_cases h_old : ℓ = s.h u
        · subst h_old; simp [h1, hinv.lvlVol_eq _ h1 hH]
        · simp [h_old, hinv.lvlVol_eq _ h1 hH]
    · intro ℓ h1 hH
      dsimp only [buckets']
      by_cases h_new : ℓ = s.h u + 1
      · subst h_new; simp only [↓reduceIte]; exact List.nodup_cons.mpr ⟨huNotL, hL_nd⟩
      · simp only [h_new, ↓reduceIte]; dsimp only [buckets1]
        by_cases hh1 : 1 ≤ s.h u
        · by_cases heq : ℓ = s.h u
          · subst heq; simp only [hh1, ↓reduceIte]; exact (hinv.buckets_nodup _ h1 hH).erase u
          · simp [hh1, heq, hinv.buckets_nodup _ h1 hH]
        · simp [hh1, hinv.buckets_nodup _ h1 hH]
    · intro ℓ h1 hH x
      dsimp only [buckets', s']
      by_cases h_new : ℓ = s.h u + 1
      · subst h_new; simp only [↓reduceIte, List.mem_cons]
        by_cases hxu : x = u
        · subst hxu; simp [huN, huR, relabelStep]
        · simp only [hxu, false_or]
          by_cases h1s : 1 ≤ s.h u
          · simp [buckets1, h1s, hinv.buckets_mem _ h1 hH x, hxu, relabelStep]
          · simp [buckets1, h1s, hinv.buckets_mem _ h1 hH x, hxu, relabelStep]
      · simp only [h_new, ↓reduceIte]
        by_cases hh1 : 1 ≤ s.h u
        · by_cases heq : ℓ = s.h u
          · subst heq; simp only [buckets1, hh1, ↓reduceIte]
            rw [(hinv.buckets_nodup _ h1 hH).mem_erase_iff, hinv.buckets_mem _ h1 hH x]
            constructor
            · rintro ⟨hne, hx1, hx2, hx3⟩; exact ⟨hx1, hx2, by simp [hne, hx3, relabelStep]⟩
            · rintro ⟨hx1, hx2, hx3⟩
              by_cases hxu : x = u
              · subst hxu; simp [relabelStep] at hx3
              · exact ⟨hxu, hx1, hx2, by simpa [hxu, relabelStep] using hx3⟩
          · simp only [buckets1, hh1, heq, ↓reduceIte, hinv.buckets_mem _ h1 hH x]
            by_cases hxu : x = u
            · subst hxu; simp [relabelStep, Ne.symm h_new, Ne.symm heq]
            · simp [hxu, relabelStep]
        · simp only [buckets1, hh1, ↓reduceIte, hinv.buckets_mem _ h1 hH x]
          by_cases hxu : x = u
          · subst hxu; simp only [relabelStep, ↓reduceIte]; exact ⟨fun ⟨_, _, h2⟩ => by omega, fun ⟨_, _, h2⟩ => by omega⟩
          · simp [hxu, relabelStep]
    · intro ℓ h1 hH
      dsimp only [buckets']
      by_cases h_new : ℓ = s.h u + 1
      · subst h_new; simp only [↓reduceIte]; exact hdl6_n
      · simp only [h_new, ↓reduceIte]; exact hdl6_o ℓ h1 hH h_new
    · exact hinv.ex_bound



end MinCostFlow.Expander
