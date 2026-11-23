module

public import MinCostFlow.Expander.PruningFreezeRemProg

/-!
# Freeze Step Bucket-Walk Stage Triple
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

abbrev freezeWalkList : List Stmt :=
  [ unlinkLvlStmt
  , .store (.bin .add (.reg prHArr) (.reg prU)) (.reg prH)
  , .store (.bin .add (.reg prCur) (.reg prU)) (.const 0)
  , pickLevelStmt
  , .store (.reg prRemArr) (.reg prU)
  , .assign prEnd (.const 1)
  , .assign prStart (.bin .add (.reg prPicked) (.const 1))
  , .loop (.bin .lt (.reg prStart) (.reg prH))
      (walkBucketStmt ;; .assign prStart (.bin .add (.reg prStart) (.const 1))) ]

structure FreezeWalkPost (cfg : PruneCfg) (gAddr csrAddr inBAddr outRAddr workAddr u : ℕ)
    (s : PruneState) (buckets : ℕ → List ℕ) (st₀ st6 : State) : Prop where
  lvl1 : 1 ≤ pickLevel cfg s.inR (fun z => if z = u then cfg.H else s.h z)
  lvlH : pickLevel cfg s.inR (fun z => if z = u then cfg.H else s.h z) < cfg.H
  inc_pos : 1 ≤ (cfg.incEdges u).length
  b1_nd : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
    ((if 1 ≤ s.h u then fun ℓ' => if ℓ' = s.h u then (buckets ℓ').erase u else buckets ℓ' else buckets) ℓ).Nodup
  b1_mem : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H → ∀ x,
    x ∈ (if 1 ≤ s.h u then fun ℓ' => if ℓ' = s.h u then (buckets ℓ').erase u else buckets ℓ' else buckets) ℓ ↔
      x < cfg.G.n ∧ s.inR x = true ∧ (fun z => if z = u then cfg.H else s.h z) x = ℓ
  rem_head : (freezeRemList cfg u s buckets).head? = some u
  rem_nd : (freezeRemList cfg u s buckets).Nodup
  rem_mem : ∀ x, x ∈ freezeRemList cfg u s buckets ↔
    x ∈ cfg.X.filter fun y =>
      s.inR y && decide (pickLevel cfg s.inR (fun z => if z = u then cfg.H else s.h z) + 1 ≤
        (fun z => if z = u then cfg.H else s.h z) y)
  reg_end : st6.regs prEnd = (freezeRemList cfg u s buckets).length
  regs_agree : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st6.regs r = st₀.regs r
  reg_actTop : st6.regs prActTop = st₀.regs prActTop
  reg_peelTop : st6.regs prPeelTop = st₀.regs prPeelTop
  pos_eq : st6.pos = st₀.pos
  pres_out : PreservedOutside2 st₀.mem st6.mem outRAddr (outRAddr + cfg.G.n)
    (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H)
  outR_eq : ∀ x < cfg.G.n, st6.mem (outRAddr + x) = if s.inR x = true then 1 else 0
  mid_eq : ∀ a, wEx workAddr cfg.G.n cfg.G.m cfg.H ≤ a →
    a < wLvlNext workAddr cfg.G.n cfg.G.m cfg.H → st6.mem a = st₀.mem a
  hArr_eq : ∀ x < cfg.G.n,
    st6.mem (wHArr workAddr cfg.G.n cfg.G.m cfg.H + x) = (fun z => if z = u then cfg.H else s.h z) x
  cur_eq : ∀ x < cfg.G.n,
    st6.mem (wCur workAddr cfg.G.n cfg.G.m cfg.H + x) = (if x = u then 0 else s.cur x)
  abs_eq : ∀ x < cfg.G.n, st6.mem (wAbs workAddr cfg.G.n cfg.G.m cfg.H + x) = s.abs x
  flowEnc_eq : ∀ idx < cfg.G.m,
    st6.mem (wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx) = (↑cfg.C_cap + s.flow idx).toNat
  remArr_eq : ∀ q < (freezeRemList cfg u s buckets).length,
    st6.mem (wRemArr workAddr cfg.G.n cfg.G.m cfg.H + q) = (freezeRemList cfg u s buckets).getD q 0
  lvlVol_H : st6.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + cfg.H) = 0
  lvlVol_le : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ pickLevel cfg s.inR (fun z => if z = u then cfg.H else s.h z) →
    st6.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) =
      volAtLevel cfg s.inR (fun z => if z = u then cfg.H else s.h z) ℓ
  lvlVol_gt : ∀ ℓ, pickLevel cfg s.inR (fun z => if z = u then cfg.H else s.h z) + 1 ≤ ℓ →
    ℓ < cfg.H → st6.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) = 0
  buckets_dl : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
    DoublyLinked st6.mem (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H) (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H)
      cfg.G.n (if ℓ ≤ pickLevel cfg s.inR (fun z => if z = u then cfg.H else s.h z) then
        (if 1 ≤ s.h u then fun ℓ' => if ℓ' = s.h u then (buckets ℓ').erase u else buckets ℓ' else buckets) ℓ else [])
      cfg.G.n (st6.mem (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ))

lemma freezeStep_walk_stage {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr u : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} (st₀ : State)
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (huR : s.inR u = true) (hexPos : 0 < s.ex u)
    (habs : s.abs u = cfg.degX u) (hcur : s.cur u = (cfg.incEdges u).length)
    (huH : s.h u + 1 = cfg.H)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length) :
    Triple w p (fun st => st = st₀ ∧ st.regs prU = u) (seqStmts freezeWalkList)
      (normalPost (FreezeWalkPost cfg gAddr csrAddr inBAddr outRAddr workAddr u s buckets st₀))
      (fun _ => 85 * cfg.H + 26 * (freezeRemList cfg u s buckets).length + 140) := by
  intro st ω ⟨hst, hru⟩
  subst st
  let hTmp := fun z => if z = u then cfg.H else s.h z
  let lvl := pickLevel cfg s.inR hTmp
  let buckets1 := if 1 ≤ s.h u then fun ℓ => if ℓ = s.h u then (buckets ℓ).erase u else buckets ℓ else buckets
  let remList := freezeRemList cfg u s buckets
  have hH3 : 3 ≤ cfg.H := PruneCfg.valid_three_le_H hinv.cfg_valid
  have hwb := pruneWordBound_pos hw
  have hlt2w : ∀ k, k < workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H → k < 2 ^ w := fun k hk => by
    unfold PruneWordBound at hw; omega
  have huN : u < cfg.G.n := by
    have := hinv.prune_inv.inR_sub u huR; rw [hinv.cfg_X] at this; exact Finset.mem_range.mp this
  have huX : u ∈ cfg.X := hinv.prune_inv.inR_sub u huR
  have hinc_pos : 1 ≤ (cfg.incEdges u).length := by
    by_contra h0
    have h0' : (cfg.incEdges u).length = 0 := by omega
    have hno := (hinv.prune_inv.no_ex_isolated u h0').1
    omega
  have hdeg_pos : 1 ≤ cfg.degX u := le_trans hinc_pos (incEdges_length_le_degX cfg u)
  have hlvl := pickLevel_spec hinv.cfg_valid s.inR hTmp ⟨u, huX, huR, by simp [hTmp], hdeg_pos⟩
  have hlvl1 : 1 ≤ lvl := hlvl.1
  have hlvlH : lvl < cfg.H := hlvl.2.1
  have hshu1 : 1 ≤ s.h u := by omega
  have hbuckets1_eq : buckets1 = fun ℓ => if ℓ = s.h u then (buckets ℓ).erase u else buckets ℓ := by
    dsimp [buckets1]; simp [hshu1]
  have hb1_nd : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H → (buckets1 ℓ).Nodup := fun ℓ h1 hH => by
    rw [hbuckets1_eq]; by_cases hsu : ℓ = s.h u
    · subst hsu; simp only [↓reduceIte]; exact (hinv.buckets_nodup _ h1 hH).erase u
    · simp only [hsu, ↓reduceIte]; exact hinv.buckets_nodup _ h1 hH
  have hb1_mem : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H → ∀ x,
      x ∈ buckets1 ℓ ↔ x < cfg.G.n ∧ s.inR x = true ∧ hTmp x = ℓ := fun ℓ h1 hH x => by
    rw [hbuckets1_eq]; by_cases hsu : ℓ = s.h u
    · subst hsu; simp only [↓reduceIte]
      rw [(hinv.buckets_nodup _ h1 hH).mem_erase_iff, hinv.buckets_mem _ h1 hH x]
      by_cases hxu : x = u
      · subst x; simp [hTmp, show cfg.H ≠ s.h u by omega]
      · simp [hTmp, hxu]
    · simp only [hsu, ↓reduceIte, hinv.buckets_mem _ h1 hH x]
      by_cases hxu : x = u
      · subst x; simp [hTmp, Ne.symm hsu, show cfg.H ≠ ℓ by omega]
      · simp [hTmp, hxu]
  have hb1_disj : ∀ ℓ₁ ℓ₂ x, 1 ≤ ℓ₁ → ℓ₁ < cfg.H → 1 ≤ ℓ₂ → ℓ₂ < cfg.H → ℓ₁ ≠ ℓ₂ →
      x ∈ buckets1 ℓ₁ → x ∉ buckets1 ℓ₂ := fun ℓ₁ ℓ₂ x h1₁ hH₁ h1₂ hH₂ hne hx1 hx2 => by
    have ha := ((hb1_mem ℓ₁ h1₁ hH₁ x).mp hx1).2.2
    have hb := ((hb1_mem ℓ₂ h1₂ hH₂ x).mp hx2).2.2
    omega
  have hu_not_b1 : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H → u ∉ buckets1 ℓ := fun ℓ h1 hH hmem => by
    have hh := ((hb1_mem ℓ h1 hH u).mp hmem).2.2
    simp only [hTmp, ↓reduceIte] at hh; omega
  have hrem_props := walkPref_props (u := u) (lvl := lvl) (H := cfg.H) hb1_nd hb1_disj hu_not_b1
    (by omega) (cfg.H - (lvl + 1)) (by omega)
  have hrem_eq : remList = walkPref u buckets1 lvl (cfg.H - (lvl + 1)) := rfl
  have hrem_head : remList.head? = some u := hrem_props.1
  have hrem_nd : remList.Nodup := hrem_props.2.1
  have hrem_mem : ∀ x, x ∈ remList ↔
      x ∈ cfg.X.filter fun y => s.inR y && decide (lvl + 1 ≤ hTmp y) := fun x => by
    rw [hrem_eq, hrem_props.2.2 x]
    simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (rfl | ⟨j, hj, hxj⟩)
      · exact ⟨huX, huR, by simp [hTmp]; omega⟩
      · have hm := (hb1_mem (lvl + 1 + j) (by omega) (by omega) x).mp hxj
        exact ⟨by rw [hinv.cfg_X]; exact Finset.mem_range.mpr hm.1, hm.2.1, by rw [hm.2.2]; omega⟩
    · rintro ⟨hxX, hxR, hle⟩
      by_cases hxu : x = u
      · exact Or.inl hxu
      · right
        have hxH : s.h x < cfg.H := hinv.prune_inv.h_lt_H x hxR
        have hx_htmp : hTmp x = s.h x := by simp [hTmp, hxu]
        rw [hx_htmp] at hle
        refine ⟨s.h x - (lvl + 1), by omega, (hb1_mem (lvl + 1 + (s.h x - (lvl + 1))) (by omega) (by omega) x).mpr ?_⟩
        refine ⟨Finset.mem_range.mp (hinv.cfg_X ▸ hxX), hxR, ?_⟩
        simp [hx_htmp]; omega
  -- Stage 1: `unlinkLvlStmt ;; h[u] := H ;; cur[u] := 0`
  have hunlink := unlinkLvl_triple (p := p) (gAddr := gAddr) (csrAddr := csrAddr)
    (inBAddr := inBAddr) (outRAddr := outRAddr) (buckets := buckets) st₀ hw huN huR hshu1
  rcases hunlink st₀ ω ⟨rfl, hinv, hru⟩ with ⟨o1, st1, c1, hr1, hq1, hc1⟩
  cases o1 with
  | returned => exact False.elim hq1
  | normal =>
    rcases hq1 with ⟨hreg1, hpos1, hbmp1, hvol1, hdl1_o, hdl1_e⟩
    have hha_addr : wHArr workAddr cfg.G.n cfg.G.m cfg.H + u < 2 ^ w :=
      hlt2w _ (by unfold pruneWorkSpace; dsimp [wHArr]; omega)
    have hH_lt2w : cfg.H < 2 ^ w := by unfold PruneWordBound at hw; omega
    have hr1_hArr : st1.regs prHArr = wHArr workAddr cfg.G.n cfg.G.m cfg.H := by
      rw [hreg1 prHArr (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_hArr
    have hr1_u : st1.regs prU = u := by
      rw [hreg1 prU (by decide) (by decide) (by decide) (by decide)]; exact hru
    have hr1_H : st1.regs prH = cfg.H := by
      rw [hreg1 prH (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_H
    let m2 := Function.update st1.mem (wHArr workAddr cfg.G.n cfg.G.m cfg.H + u) cfg.H
    let st2 : State := { mem := m2, regs := st1.regs, pos := st1.pos }
    obtain ⟨o2, stx2, c2, hr2, ⟨ho2, hstx2⟩, hc2⟩ := runs_store_le
      (w := w) (p := p) (ω := ω) (st := st1) (x := wHArr workAddr cfg.G.n cfg.G.m cfg.H + u) (v := cfg.H)
      (k := 0) (T := 6) (Q := fun o s => o = .normal ∧ s = st2)
      (eval_add_eq w st1 prHArr prU hr1_hArr hr1_u hha_addr)
      (eval_reg_eq w st1 prH hr1_H) ⟨rfl, rfl⟩ (by simp [Expr.size])
    rcases ho2 with rfl; rcases hstx2 with rfl
    have hcur_addr : wCur workAddr cfg.G.n cfg.G.m cfg.H + u < 2 ^ w :=
      hlt2w _ (by unfold pruneWorkSpace; dsimp [wCur]; omega)
    have hr2_cur : st2.regs prCur = wCur workAddr cfg.G.n cfg.G.m cfg.H := by
      rw [hreg1 prCur (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_cur
    let m3 := Function.update m2 (wCur workAddr cfg.G.n cfg.G.m cfg.H + u) 0
    let st3 : State := { mem := m3, regs := st1.regs, pos := st1.pos }
    obtain ⟨o3, stx3, c3, hr3, ⟨ho3, hstx3⟩, hc3⟩ := runs_store_le
      (w := w) (p := p) (ω := ω) (st := st2) (x := wCur workAddr cfg.G.n cfg.G.m cfg.H + u) (v := 0)
      (k := 0) (T := 6) (Q := fun o s => o = .normal ∧ s = st3)
      (eval_add_eq w st2 prCur prU hr2_cur hr1_u hcur_addr)
      (Expr.eval_const (by omega)) ⟨rfl, rfl⟩ (by simp [Expr.size])
    rcases ho3 with rfl; rcases hstx3 with rfl
    have hst3_below : ∀ k, k < wLvlNext workAddr cfg.G.n cfg.G.m cfg.H →
        k ≠ wHArr workAddr cfg.G.n cfg.G.m cfg.H + u →
        k ≠ wCur workAddr cfg.G.n cfg.G.m cfg.H + u →
        st3.mem k = st₀.mem k := fun k hk hne1 hne2 => by
      dsimp [st3, m3, m2]
      rw [Function.update_of_ne hne2, Function.update_of_ne hne1, hbmp1.1 k (Or.inl hk)]
    have hst3_above : ∀ k, wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + cfg.H + 1 ≤ k →
        st3.mem k = st₀.mem k := fun k hk => by
      dsimp [st3, m3, m2]
      rw [Function.update_of_ne (by dsimp [wCur, wLvlHead] at *; omega),
        Function.update_of_ne (by dsimp [wHArr, wLvlHead] at *; omega),
        hbmp1.1 k (Or.inr hk)]
    have hst3_lvl_agree : ∀ k, wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤ k →
        st3.mem k = st1.mem k := fun k hk => by
      dsimp [st3, m3, m2]
      rw [Function.update_of_ne (by dsimp [wCur, wLvlNext] at *; omega),
        Function.update_of_ne (by dsimp [wHArr, wLvlNext] at *; omega)]
    have hst3_degX_u : st3.mem (wDegX workAddr cfg.G.n cfg.G.m cfg.H + u) = cfg.degX u := by
      rw [hst3_below (wDegX workAddr cfg.G.n cfg.G.m cfg.H + u) (by dsimp [wDegX, wLvlNext]; omega)
        (by dsimp [wDegX, wHArr]; omega) (by dsimp [wDegX, wCur]; omega),
        hinv.degX_eq u huN]
    have hst3_lvlVol : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
        st3.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) = volAtLevel cfg s.inR hTmp ℓ := fun ℓ h1 hH => by
      rw [hst3_lvl_agree (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) (by dsimp [wLvlNext, wLvlVol]; omega),
        volAtLevel_erase_u hinv.cfg_X huN huR hH]
      by_cases hsu : ℓ = s.h u
      · subst hsu; simp only [↓reduceIte]; rw [hvol1, hinv.lvlVol_eq _ h1 hH]
      · simp only [hsu, ↓reduceIte]
        rw [(hbmp1.2.2 ℓ (by omega) hsu).1, hinv.lvlVol_eq _ h1 hH]
    have hst3_dl : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
        DoublyLinked st3.mem (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H) (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H) cfg.G.n
          (buckets1 ℓ) cfg.G.n (st3.mem (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ)) := fun ℓ h1 hH => by
      rw [hst3_lvl_agree (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ) (by dsimp [wLvlNext, wLvlHead]; omega)]
      refine doublyLinked_congr_disjoint
        (fun y hy => hst3_lvl_agree (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H + y) (by omega))
        (fun y hy => hst3_lvl_agree (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H + y) (by dsimp [wLvlNext, wLvlPrev]; omega))
        ?_
      rw [hbuckets1_eq]; by_cases hsu : ℓ = s.h u
      · subst hsu; simp only [↓reduceIte]; exact hdl1_e
      · simp only [hsu, ↓reduceIte]; exact hdl1_o ℓ h1 hH hsu
    -- Stage 2: `pickLevelStmt`
    have hpick := pickLevel_triple (p := p) st3 hw hinv.cfg_valid hinv.cfg_X (by rw [hinv.cfg_edges]; rfl)
      huN huR hinv.prune_inv.h_lt_H hr1_u hr1_H
      (by rw [hreg1 prCcap (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_ccap)
      (by rw [hreg1 prDegX (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_degX)
      (by rw [hreg1 prLvlVol (by decide) (by decide) (by decide) (by decide)]; exact hinv.reg_lvlVol)
      hst3_degX_u hst3_lvlVol
    rcases hpick st3 ω rfl with ⟨o4, st4, c4, hr4, hq4, hc4⟩
    cases o4 with
    | returned => exact False.elim hq4
    | normal =>
      rcases hq4 with ⟨hreg4, hr4_pk, hmem4, hpos4⟩
      -- Stage 3: `remArr[0] := u ;; end := 1 ;; start := picked + 1`
      have hreg_34_to_0 : ∀ r, r ≤ prCsrAdjH → r ≠ prActTop → r ≠ prPeelTop → st4.regs r = st₀.regs r := by
        intro r hr _ _
        obtain ⟨ht1, ht2, ht3, _, hdl, _, _, _, hj_ne, _, _, _, hsuf_ne, hpk_ne⟩ := le_adjH_ne_work hr
        rw [hreg4 r hj_ne ht1 ht2 hdl hpk_ne, hreg1 r ht1 ht2 ht3 hsuf_ne]
      have hat_4 : st4.regs prActTop = st₀.regs prActTop := by
        rw [hreg4 prActTop (by decide) (by decide) (by decide) (by decide) (by decide),
          hreg1 prActTop (by decide) (by decide) (by decide) (by decide)]
      have hpt_4 : st4.regs prPeelTop = st₀.regs prPeelTop := by
        rw [hreg4 prPeelTop (by decide) (by decide) (by decide) (by decide) (by decide),
          hreg1 prPeelTop (by decide) (by decide) (by decide) (by decide)]
      have hr4_u : st4.regs prU = u := by
        rw [hreg4 prU (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr1_u
      have hr4_ra : st4.regs prRemArr = wRemArr workAddr cfg.G.n cfg.G.m cfg.H := by
        rw [hreg_34_to_0 prRemArr (by decide) (by decide) (by decide)]; exact hinv.reg_remArr
      have hrem0_addr : wRemArr workAddr cfg.G.n cfg.G.m cfg.H < 2 ^ w :=
        hlt2w _ (by unfold pruneWorkSpace; dsimp [wRemArr]; omega)
      let m5a := Function.update st3.mem (wRemArr workAddr cfg.G.n cfg.G.m cfg.H) u
      let st5a : State := { mem := m5a, regs := st4.regs, pos := st4.pos }
      obtain ⟨o5a, stx5a, c5a, hr5a, ⟨ho5a, hstx5a⟩, hc5a⟩ := runs_store_le
        (w := w) (p := p) (ω := ω) (st := st4) (x := wRemArr workAddr cfg.G.n cfg.G.m cfg.H) (v := u)
        (k := 0) (T := 5) (Q := fun o s => o = .normal ∧ s = st5a)
        (eval_reg_eq w st4 prRemArr hr4_ra)
        (eval_reg_eq w st4 prU hr4_u)
        ⟨rfl, by simp [st5a, m5a, hmem4]⟩ (by simp [Expr.size])
      rcases ho5a with rfl; rcases hstx5a with rfl
      let r5b := Function.update st4.regs prEnd 1
      let st5b : State := { mem := m5a, regs := r5b, pos := st4.pos }
      have hr5b : Runs w p ω (.assign prEnd (.const 1)) st5a .normal st5b 2 :=
        runs_assign_iff.mpr ⟨1, Expr.eval_const (by omega), rfl, rfl, by simp [Expr.size]⟩
      let r5 := Function.update r5b prStart (lvl + 1)
      let st5 : State := { mem := m5a, regs := r5, pos := st4.pos }
      have hr5b_pk : st5b.regs prPicked = lvl := by
        dsimp [st5b, r5b]; rw [Function.update_of_ne (by decide)]; exact hr4_pk
      have hr5c : Runs w p ω (.assign prStart (.bin .add (.reg prPicked) (.const 1))) st5b .normal st5 4 :=
        runs_assign_iff.mpr ⟨lvl + 1,
          Expr.eval_bin (op := .add) (eval_reg_eq w st5b prPicked hr5b_pk) (Expr.eval_const (by omega))
            (by dsimp only [BinOp.eval]; omega),
          rfl, rfl, by simp [Expr.size]⟩
      -- Stage 4: `walkBucket` loop
      let K := cfg.H - (lvl + 1)
      let walkCond := Expr.bin .lt (.reg prStart) (.reg prH)
      let walkBody := walkBucketStmt ;; .assign prStart (.bin .add (.reg prStart) (.const 1))
      let walkInv : ℕ → State → Prop := fun k st =>
        k ≤ K ∧ st.regs prStart = lvl + 1 + k ∧
        st.regs prEnd = (walkPref u buckets1 lvl k).length ∧
        st.regs prH = cfg.H ∧ st.regs prN = cfg.G.n ∧
        st.regs prRemArr = wRemArr workAddr cfg.G.n cfg.G.m cfg.H ∧
        st.regs prLvlNext = wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ∧
        st.regs prLvlVol = wLvlVol workAddr cfg.G.n cfg.G.m cfg.H ∧
        st.regs prLvlHead = wLvlHead workAddr cfg.G.n cfg.G.m cfg.H ∧
        (∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st.regs r = st₀.regs r) ∧
        st.regs prActTop = st₀.regs prActTop ∧ st.regs prPeelTop = st₀.regs prPeelTop ∧
        st.pos = st₀.pos ∧
        MemFrame st3.mem st.mem (wRemArr workAddr cfg.G.n cfg.G.m cfg.H)
          (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + cfg.H + 1) ∧
        (∀ q, wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H ≤ q →
          q < wLvlVol workAddr cfg.G.n cfg.G.m cfg.H → st.mem q = st3.mem q) ∧
        (∀ q < (walkPref u buckets1 lvl k).length,
          st.mem (wRemArr workAddr cfg.G.n cfg.G.m cfg.H + q) = (walkPref u buckets1 lvl k).getD q 0) ∧
        st.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + cfg.H) = 0 ∧
        (∀ ℓ, 1 ≤ ℓ → ℓ ≤ lvl →
          st.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) = st3.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ)) ∧
        (∀ ℓ, lvl + 1 ≤ ℓ → ℓ < lvl + 1 + k →
          st.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) = 0 ∧
          st.mem (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ) = cfg.G.n) ∧
        (∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
          DoublyLinked st.mem (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H) (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H)
            cfg.G.n (if lvl + 1 ≤ ℓ ∧ ℓ < lvl + 1 + k then [] else buckets1 ℓ) cfg.G.n
            (st.mem (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ)))
      have hwalk_init : walkInv 0 st5 := by
        have hst5_reg : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st5.regs r = st₀.regs r := by
          intro r hr h1 h2
          obtain ⟨_, _, _, _, _, _, _, _, _, hst_ne, hend_ne, _, _, _⟩ := le_adjH_ne_work hr
          dsimp [st5, r5, r5b]
          rw [Function.update_of_ne hst_ne, Function.update_of_ne hend_ne]
          exact hreg_34_to_0 r hr h1 h2
        refine ⟨Nat.zero_le K, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hst5_reg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · dsimp [st5, r5]; rw [Function.update_self]
        · dsimp [st5, r5, r5b]; rw [Function.update_of_ne (by decide), Function.update_self]; rfl
        · exact hst5_reg prH (by decide) (by decide) (by decide) |>.trans hinv.reg_H
        · exact hst5_reg prN (by decide) (by decide) (by decide) |>.trans hinv.reg_n
        · exact hst5_reg prRemArr (by decide) (by decide) (by decide) |>.trans hinv.reg_remArr
        · exact hst5_reg prLvlNext (by decide) (by decide) (by decide) |>.trans hinv.reg_lvlNext
        · exact hst5_reg prLvlVol (by decide) (by decide) (by decide) |>.trans hinv.reg_lvlVol
        · exact hst5_reg prLvlHead (by decide) (by decide) (by decide) |>.trans hinv.reg_lvlHead
        · dsimp [st5, r5, r5b]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hat_4
        · dsimp [st5, r5, r5b]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hpt_4
        · exact hpos4.trans (hpos1.trans rfl)
        · intro q hq; dsimp [st5, m5a]
          rw [Function.update_of_ne (by dsimp [wRemArr, wLvlHead] at hq ⊢; rcases hq with hq | hq <;> omega)]
        · intro q hq1 _; dsimp [st5, m5a]; rw [Function.update_of_ne (by dsimp [wRemArr, wFlowEnc] at *; omega)]
        · intro q hq
          have hq0 : q = 0 := by simp [walkPref] at hq; omega
          subst hq0; dsimp [st5, m5a, walkPref]; simp
        · dsimp [st5, m5a]
          rw [Function.update_of_ne (by dsimp [wRemArr, wLvlVol]; omega),
            hst3_lvl_agree (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + cfg.H) (by dsimp [wLvlNext, wLvlVol]; omega),
            (hbmp1.2.2 cfg.H le_rfl (by omega)).1, hinv.lvlVol_H]
        · intro ℓ _ _
          dsimp [st5, m5a]; rw [Function.update_of_ne (by dsimp [wRemArr, wLvlVol]; omega)]
        · intro ℓ h1 h2; omega
        · intro ℓ h1 hH
          have hn : ¬ (lvl + 1 ≤ ℓ ∧ ℓ < lvl + 1 + 0) := by omega
          simp only [hn, ↓reduceIte]
          have heq_m5a : ∀ a, a ≠ wRemArr workAddr cfg.G.n cfg.G.m cfg.H →
              st5.mem a = st3.mem a := fun a ha => by
            dsimp [st5, m5a]; rw [Function.update_of_ne ha]
          rw [heq_m5a _ (by dsimp [wRemArr, wLvlHead]; omega)]
          exact doublyLinked_congr_disjoint
            (fun y hy => heq_m5a _ (by
              have hyN := ((hb1_mem ℓ h1 hH y).mp hy).1
              dsimp [wLvlNext, wRemArr]; omega))
            (fun y hy => heq_m5a _ (by
              have hyN := ((hb1_mem ℓ h1 hH y).mp hy).1
              dsimp [wLvlPrev, wRemArr]; omega))
            (hst3_dl ℓ h1 hH)
      have hwalk : Triple w p (walkInv 0) (.loop walkCond walkBody)
          (normalPost (walkInv K))
          (fun _ => 40 * K + 26 * remList.length + 10) := by
        apply (Triple.loop_inv (Inv := walkInv)
          (condVal := fun st => if st.regs prStart < st.regs prH then 1 else 0)
          (fun k => K - k)
          (fun k => 40 * (K - k) + 26 * (remList.length - (walkPref u buckets1 lvl k).length) + 10)
          ?_ ?_ ?_ 0).mono_cost (fun _ _ => by dsimp [walkPref]; omega)
        · intro k st hwk
          exact Expr.eval_bin (op := .lt) (eval_reg_eq w st prStart rfl) (eval_reg_eq w st prH rfl)
            (by dsimp only [BinOp.eval]; split_ifs <;> omega)
        · intro k st hwk h0
          have hk_ge : cfg.H ≤ st.regs prStart := by
            by_contra hlt
            have hlt' : st.regs prStart < st.regs prH := by rw [hwk.2.2.2.1]; omega
            simp [hlt'] at h0
          have hk_eq : k = K := by
            have hst_start := hwk.2.1; have hk_le := hwk.1; dsimp [K] at *; omega
          subst hk_eq
          exact ⟨hwk, by simp [walkCond, Expr.size]⟩
        ·
          · intro k st hwk hne
            have hk_lt : st.regs prStart < st.regs prH := by
              by_contra hge; simp [hge] at hne
            have hkK : k < K := by rw [hwk.2.1, hwk.2.2.2.1] at hk_lt; omega
            let ℓ := lvl + 1 + k
            have hℓ1 : 1 ≤ ℓ := by omega
            have hℓH : ℓ < cfg.H := by omega
            let prefk := walkPref u buckets1 lvl k
            let L := buckets1 ℓ
            have hnext_props := walkPref_props (u := u) (lvl := lvl) (H := cfg.H) hb1_nd hb1_disj hu_not_b1
              (by omega) (k + 1) (by omega)
            have hfit : prefk.length + L.length ≤ cfg.G.n := by
              have hsub_n : ∀ x ∈ walkPref u buckets1 lvl (k + 1), x ∈ Finset.range cfg.G.n := fun x hx => by
                rcases (hnext_props.2.2 x).mp hx with rfl | ⟨j, _, hxj⟩
                · exact Finset.mem_range.mpr huN
                · exact Finset.mem_range.mpr ((hb1_mem (lvl + 1 + j) (by omega) (by omega) x).mp hxj).1
              have hcard := calc (walkPref u buckets1 lvl (k + 1)).length
                  = (walkPref u buckets1 lvl (k + 1)).toFinset.card :=
                    (List.toFinset_card_of_nodup hnext_props.2.1).symm
                _ ≤ (Finset.range cfg.G.n).card :=
                    Finset.card_le_card (fun x hx => hsub_n x (List.mem_toFinset.mp hx))
                _ = cfg.G.n := Finset.card_range cfg.G.n
              simpa only [walkPref, List.length_append] using hcard
            let bucketsCur : ℕ → List ℕ := fun ℓ' =>
              if lvl + 1 ≤ ℓ' ∧ ℓ' < ℓ then [] else buckets1 ℓ'
            have hdl_ℓ : DoublyLinked st.mem (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H)
                (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H) cfg.G.n L cfg.G.n
                (st.mem (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ)) := by
              have hdl0 := hwk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ℓ hℓ1 hℓH
              simpa [ℓ] using hdl0
            have hdl_other : ∀ ℓ', 1 ≤ ℓ' → ℓ' < cfg.H → ℓ' ≠ ℓ →
                DoublyLinked st.mem (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H)
                  (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H) cfg.G.n (bucketsCur ℓ') cfg.G.n
                  (st.mem (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ')) := by
              intro ℓ' h1' hH' hne'
              have hdl0 := hwk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ℓ' h1' hH'
              simpa [bucketsCur, ℓ] using hdl0
            have hwbk := walkBucket_triple_raw (p := p) L bucketsCur (pref := prefk) st hw hℓ1 hℓH hfit
              hwk.2.2.2.2.1 hwk.2.2.2.2.2.1 hwk.2.2.2.2.2.2.1 hwk.2.2.2.2.2.2.2.1 hwk.2.2.2.2.2.2.2.2.1
              hdl_ℓ hdl_other
            refine ⟨25 * L.length + 35, ?_⟩
            intro st_in ω hsi
            subst st_in
            rcases hwbk st ω ⟨rfl, hwk.2.1, hwk.2.2.1, hwk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩ with
              ⟨ow, stw, cw, hrw, hqw, hcw⟩
            cases ow with
            | returned => exact False.elim hqw
            | normal =>
              rcases hqw with ⟨hregw, hrw_end, hposw, hmfw, hfew, hlvlw, hvol_ℓ, hhead_ℓ, hdl_w, hrem_w⟩
              let r_next := Function.update stw.regs prStart (ℓ + 1)
              let st_next : State := { mem := stw.mem, regs := r_next, pos := stw.pos }
              have hrw_start : stw.regs prStart = ℓ := by
                rw [hregw prStart (by decide) (by decide)]; exact hwk.2.1
              have hs_inc : Runs w p ω (.assign prStart (.bin .add (.reg prStart) (.const 1))) stw .normal st_next 4 :=
                runs_assign_iff.mpr ⟨ℓ + 1,
                  Expr.eval_bin (op := .add) (eval_reg_eq w stw prStart hrw_start) (Expr.eval_const (by omega))
                    (by dsimp only [BinOp.eval]; omega),
                  rfl, rfl, by simp [Expr.size]⟩
              have hreg_next : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop →
                  st_next.regs r = st₀.regs r := by
                intro r hr h1 h2
                dsimp [st_next, r_next, prCsrAdjH, prStart] at hr ⊢
                rw [Function.update_of_ne (by omega), hregw r (by dsimp [prU]; omega) (by dsimp [prEnd]; omega)]
                exact hwk.2.2.2.2.2.2.2.2.2.1 r hr h1 h2
              have hlen_sub_eq : (walkPref u buckets1 lvl (k + 1)).length = prefk.length + L.length := by
                simp [walkPref, prefk, L, ℓ]
              have hpref_sub_rem : (walkPref u buckets1 lvl (k + 1)).length ≤ remList.length := by
                have hsub_rem : ∀ x ∈ walkPref u buckets1 lvl (k + 1), x ∈ remList := fun x hx => by
                  rw [hrem_eq, hrem_props.2.2 x]
                  rcases (hnext_props.2.2 x).mp hx with rfl | ⟨j, hj, hxj⟩
                  · exact Or.inl rfl
                  · exact Or.inr ⟨j, by omega, hxj⟩
                calc (walkPref u buckets1 lvl (k + 1)).length
                    = (walkPref u buckets1 lvl (k + 1)).toFinset.card :=
                      (List.toFinset_card_of_nodup hnext_props.2.1).symm
                  _ ≤ remList.toFinset.card :=
                      Finset.card_le_card (fun x hx => List.mem_toFinset.mpr (hsub_rem x (List.mem_toFinset.mp hx)))
                  _ = remList.length := List.toFinset_card_of_nodup hrem_nd
              refine ⟨.normal, st_next, cw + 4 + 1, runs_seq hrw hs_inc, ?_, by dsimp only at hcw ⊢; omega⟩
              refine ⟨k + 1, ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hreg_next, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
                by omega, ?_⟩
              · dsimp [st_next, r_next]; rw [Function.update_self]; omega
              · dsimp [st_next, r_next]; rw [Function.update_of_ne (by decide), hrw_end, hlen_sub_eq]
              · exact hreg_next prH (by decide) (by decide) (by decide) |>.trans hinv.reg_H
              · exact hreg_next prN (by decide) (by decide) (by decide) |>.trans hinv.reg_n
              · exact hreg_next prRemArr (by decide) (by decide) (by decide) |>.trans hinv.reg_remArr
              · exact hreg_next prLvlNext (by decide) (by decide) (by decide) |>.trans hinv.reg_lvlNext
              · exact hreg_next prLvlVol (by decide) (by decide) (by decide) |>.trans hinv.reg_lvlVol
              · exact hreg_next prLvlHead (by decide) (by decide) (by decide) |>.trans hinv.reg_lvlHead
              · dsimp [st_next, r_next]; rw [Function.update_of_ne (by decide), hregw prActTop (by decide) (by decide)]
                exact hwk.2.2.2.2.2.2.2.2.2.2.1
              · dsimp [st_next, r_next]; rw [Function.update_of_ne (by decide), hregw prPeelTop (by decide) (by decide)]
                exact hwk.2.2.2.2.2.2.2.2.2.2.2.1
              · exact hposw.trans hwk.2.2.2.2.2.2.2.2.2.2.2.2.1
              · intro q hq; rw [hmfw q hq, hwk.2.2.2.2.2.2.2.2.2.2.2.2.2.1 q hq]
              · intro q hq1 hq2; rw [hfew q hq1 hq2, hwk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 q hq1 hq2]
              · intro q hq
                rw [hlen_sub_eq] at hq
                simpa only [walkPref] using hrem_w q hq
              · rw [hlvlw _ (by dsimp [wLvlVol]; omega) (by dsimp [wLvlVol, wLvlHead]; omega)
                  (by omega) (by dsimp [wLvlVol, wLvlHead]; omega)]
                exact hwk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              · intro ℓ' h1' hle'
                rw [hlvlw _ (by dsimp [wLvlVol]; omega) (by dsimp [wLvlVol, wLvlHead]; omega)
                  (by omega) (by dsimp [wLvlVol, wLvlHead]; omega)]
                exact hwk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ℓ' h1' hle'
              · intro ℓ' hlo hhi
                by_cases heq : ℓ' = ℓ
                · subst heq; exact ⟨hvol_ℓ, hhead_ℓ⟩
                · have hlt_prev : ℓ' < ℓ := by omega
                  have hpre := hwk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ℓ' hlo hlt_prev
                  refine ⟨?_, ?_⟩
                  · rw [hlvlw _ (by dsimp [wLvlVol]; omega) (by dsimp [wLvlVol, wLvlHead]; omega)
                      (by omega) (by dsimp [wLvlVol, wLvlHead]; omega)]; exact hpre.1
                  · rw [hlvlw _ (by dsimp [wLvlHead, wLvlVol]; omega) (by dsimp [wLvlHead]; omega)
                      (by dsimp [wLvlHead, wLvlVol]; omega) (by omega)]; exact hpre.2
              · intro ℓ' h1' hH'
                by_cases heq : ℓ' = ℓ
                · subst heq
                  simp only [show lvl + 1 ≤ ℓ ∧ ℓ < lvl + 1 + (k + 1) by omega]
                  rw [hhead_ℓ]; rfl
                · have hcond_eq : (if lvl + 1 ≤ ℓ' ∧ ℓ' < lvl + 1 + (k + 1) then [] else buckets1 ℓ') =
                      bucketsCur ℓ' := by
                    dsimp [bucketsCur]
                    split_ifs <;> first | rfl | omega
                  rw [hcond_eq]
                  exact hdl_w ℓ' h1' hH' heq
              · simp only [walkCond, Expr.size]
                have hle_rem : (walkPref u buckets1 lvl (k + 1)).length ≤ remList.length := by
                  have hsub_rem : ∀ x ∈ walkPref u buckets1 lvl (k + 1), x ∈ remList := fun x hx => by
                    rw [hrem_eq, hrem_props.2.2 x]
                    rcases (hnext_props.2.2 x).mp hx with rfl | ⟨j, _, hxj⟩
                    · exact Or.inl rfl
                    · exact Or.inr ⟨j, by omega, hxj⟩
                  calc (walkPref u buckets1 lvl (k + 1)).length
                      = (walkPref u buckets1 lvl (k + 1)).toFinset.card :=
                        (List.toFinset_card_of_nodup hnext_props.2.1).symm
                    _ ≤ remList.toFinset.card :=
                        Finset.card_le_card (fun x hx => List.mem_toFinset.mpr (hsub_rem x (List.mem_toFinset.mp hx)))
                    _ = remList.length := List.toFinset_card_of_nodup hrem_nd
                have hlen_sub_eq : (walkPref u buckets1 lvl (k + 1)).length = prefk.length + L.length := by
                  simp [walkPref, prefk, L, ℓ]
                dsimp [prefk] at hlen_sub_eq
                have hpref_k_le : (walkPref u buckets1 lvl k).length ≤ remList.length := by omega
                omega
      rcases hwalk st5 ω hwalk_init with ⟨owk, st6, c_walk, hr_walk, hq_walk, hc_walk⟩
      cases owk with
      | returned => exact False.elim hq_walk
      | normal =>
        have hrun_walk := runs_seq hr1 (runs_seq hr2 (runs_seq hr3 (runs_seq hr4 (runs_seq hr5a
          (runs_seq hr5b (runs_seq hr5c hr_walk))))))
        have hst6_pres' : PreservedOutside2 st₀.mem st6.mem outRAddr (outRAddr + cfg.G.n)
            (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) := by
          intro a _ ha2
          unfold pruneWorkSpace at ha2
          rw [hq_walk.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a (by dsimp [wRemArr, wHArr, wLvlHead] at *; omega)]
          rcases ha2 with hlo | hhi
          · exact hst3_below a (by dsimp [wHArr, wLvlNext] at *; omega)
              (by dsimp [wHArr] at *; omega) (by dsimp [wHArr, wCur] at *; omega)
          · exact hst3_above a (by dsimp [wLvlHead] at *; omega)
        have hst6_outR : ∀ x < cfg.G.n, st6.mem (outRAddr + x) = if s.inR x = true then 1 else 0 := fun x hx => by
          have hdo : outRAddr + x < wHArr workAddr cfg.G.n cfg.G.m cfg.H ∨
              workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H ≤ outRAddr + x := by
            dsimp [wHArr]; rcases hdisj.2.2.2.2.2.2 with h | h <;> omega
          unfold pruneWorkSpace at hdo
          rw [hq_walk.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (outRAddr + x) (by dsimp [wRemArr, wHArr, wLvlHead] at *; omega)]
          rcases hdo with hlo | hhi
          · rw [hst3_below (outRAddr + x) (by dsimp [wHArr, wLvlNext] at *; omega)
              (by omega) (by dsimp [wHArr, wCur] at *; omega), hinv.outR_eq x hx]
          · rw [hst3_above (outRAddr + x) (by dsimp [wLvlHead] at *; omega), hinv.outR_eq x hx]
        have hst6_mid : ∀ a, wEx workAddr cfg.G.n cfg.G.m cfg.H ≤ a →
            a < wLvlNext workAddr cfg.G.n cfg.G.m cfg.H → st6.mem a = st₀.mem a := fun a ha1 ha2 => by
          have ha_rem : a < wRemArr workAddr cfg.G.n cfg.G.m cfg.H := by
            dsimp [wLvlNext, wRemArr] at *; omega
          rw [hq_walk.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a (Or.inl ha_rem),
            hst3_below a ha2 (by dsimp [wEx, wHArr] at *; omega) (by dsimp [wEx, wCur] at *; omega)]
        refine ⟨.normal, st6, _, hrun_walk, ?_, by
          dsimp only at hc1 hc2 hc3 hc4 hc5a hc_walk ⊢
          have hK : K ≤ cfg.H := by dsimp [K]; omega
          have hcw_bd : c_walk ≤ 40 * cfg.H + 26 * (freezeRemList cfg u s buckets).length + 10 := by
            change c_walk ≤ 40 * K + 26 * remList.length + 10 at hc_walk
            dsimp only [remList] at hc_walk
            omega
          omega⟩
        exact
          { lvl1 := hlvl1
            lvlH := hlvlH
            inc_pos := hinc_pos
            b1_nd := hb1_nd
            b1_mem := hb1_mem
            rem_head := hrem_head
            rem_nd := hrem_nd
            rem_mem := hrem_mem
            reg_end := by rw [hq_walk.2.2.1]; rfl
            regs_agree := hq_walk.2.2.2.2.2.2.2.2.2.1
            reg_actTop := hq_walk.2.2.2.2.2.2.2.2.2.2.1
            reg_peelTop := hq_walk.2.2.2.2.2.2.2.2.2.2.2.1
            pos_eq := hq_walk.2.2.2.2.2.2.2.2.2.2.2.2.1
            pres_out := hst6_pres'
            outR_eq := hst6_outR
            mid_eq := hst6_mid
            hArr_eq := fun x hx => by
              rw [hq_walk.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (Or.inl (by dsimp [wHArr, wRemArr]; omega))]
              dsimp [st3, m3, m2]; rw [Function.update_of_ne (by dsimp [wHArr, wCur]; omega)]
              by_cases hxu : x = u
              · subst hxu; rw [Function.update_self]; simp
              · rw [Function.update_of_ne (by omega), hbmp1.1 _ (Or.inl (by dsimp [wHArr, wLvlNext]; omega)),
                  hinv.h_eq x hx]; simp [hxu]
            cur_eq := fun x hx => by
              rw [hq_walk.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (Or.inl (by dsimp [wCur, wRemArr]; omega))]
              dsimp [st3, m3, m2]
              by_cases hxu : x = u
              · subst hxu; rw [Function.update_self]; simp
              · rw [Function.update_of_ne (by omega), Function.update_of_ne (by dsimp [wCur, wHArr]; omega),
                  hbmp1.1 _ (Or.inl (by dsimp [wCur, wLvlNext]; omega)), hinv.cur_eq x hx]; simp [hxu]
            abs_eq := fun x hx => by
              rw [hq_walk.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (Or.inl (by dsimp [wAbs, wRemArr]; omega)),
                hst3_below _ (by dsimp [wAbs, wLvlNext]; omega) (by dsimp [wAbs, wHArr]; omega)
                  (by dsimp [wAbs, wCur]; omega),
                hinv.abs_eq x hx]
            flowEnc_eq := fun idx hidx => by
              rw [hq_walk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by dsimp [wFlowEnc]; omega) (by dsimp [wFlowEnc, wLvlVol]; omega),
                hst3_lvl_agree _ (by dsimp [wLvlNext, wFlowEnc]; omega),
                hbmp1.2.1 _ (by dsimp [wLvlPrev, wFlowEnc]; omega) (by dsimp [wFlowEnc, wLvlVol]; omega),
                hinv.flowEnc_eq idx hidx]
            remArr_eq := fun q hq => by
              change q < remList.length at hq
              change st6.mem (wRemArr workAddr cfg.G.n cfg.G.m cfg.H + q) = remList.getD q 0
              have hrem_k : walkPref u buckets1 lvl K = remList := by simp only [hrem_eq, K]
              have h0 := hq_walk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 q (hrem_k.symm ▸ hq)
              rwa [hrem_k] at h0
            lvlVol_H := hq_walk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            lvlVol_le := fun ℓ h1 hle => by
              rw [hq_walk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ℓ h1 hle,
                hst3_lvlVol ℓ h1 (lt_of_le_of_lt hle hlvlH)]
            lvlVol_gt := fun ℓ hge hlt =>
              (hq_walk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ℓ hge (by dsimp [K]; omega)).1
            buckets_dl := fun ℓ h1 hH => by
              change DoublyLinked st6.mem (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H)
                (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H) cfg.G.n (if ℓ ≤ lvl then buckets1 ℓ else [])
                cfg.G.n (st6.mem (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ))
              have hdl6 := hq_walk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ℓ h1 hH
              have heq_ℓ : (if lvl + 1 ≤ ℓ ∧ ℓ < lvl + 1 + K then [] else buckets1 ℓ) =
                  if ℓ ≤ lvl then buckets1 ℓ else [] := by
                by_cases hle : ℓ ≤ lvl
                · simp [hle]
                · simp [hle, show lvl + 1 ≤ ℓ ∧ ℓ < lvl + 1 + K by dsimp [K]; omega]
              rwa [heq_ℓ] at hdl6 }

end MinCostFlow.Expander
