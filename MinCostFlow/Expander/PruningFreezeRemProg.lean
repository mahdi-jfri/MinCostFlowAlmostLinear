module

public import MinCostFlow.Expander.PruningPickLevelProg

/-!
# Freeze Sweep Invariant and Removal-Loop Step
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

lemma freeze_sweep_inv {cfg : PruneCfg} {s : PruneState}
    (hinv : PruningInv cfg s) {u lvl : ℕ} (huR : s.inR u = true) (hexPos : 0 < s.ex u)
    (habs : s.abs u = cfg.degX u) (hcurEnd : s.cur u = (cfg.incEdges u).length)
    (huH : s.h u + 1 = cfg.H) (hlvlH : lvl < cfg.H) :
    let hTmp : ℕ → ℕ := fun x => if x = u then cfg.H else s.h x
    let A : Finset ℕ := cfg.X.filter fun x => s.inR x && decide (lvl + 1 ≤ hTmp x)
    let sMid : PruneState := { s with h := hTmp, cur := fun x => if x = u then 0 else s.cur x }
    SweepInv cfg A sMid := by
  intro hTmp A sMid
  have hle_hTmp : ∀ x, s.h x ≤ hTmp x := fun x => by
    by_cases hxu : x = u
    · subst hxu; simp only [hTmp, ↓reduceIte]; omega
    · simp only [hTmp, hxu, ↓reduceIte, le_refl]
  refine
    { inR_sub := hinv.inR_sub
      not_inR_B := hinv.not_inR_B
      h_le_H := fun x hxR => by
        by_cases hxu : x = u
        · simp [sMid, hTmp, hxu]
        · simp [sMid, hTmp, hxu]; exact (hinv.h_lt_H x hxR).le
      h_lt_H_notA := fun x hxR hxA => by
        by_cases hxu : x = u
        · exfalso; apply hxA
          simp only [A, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq, hTmp, hxu, ↓reduceIte]
          exact ⟨hinv.inR_sub u huR, huR, by omega⟩
        · simp only [sMid, hTmp, hxu, ↓reduceIte]; exact hinv.h_lt_H x hxR
      cur_le := fun x hxR => by
        by_cases hxu : x = u
        · simp [sMid, hxu]
        · simp only [sMid, hxu, ↓reduceIte]; exact hinv.cur_le x hxR
      abs_le := hinv.abs_le
      h_pos_abs := fun x hxR hxPos => by
        by_cases hxu : x = u
        · rw [hxu]; exact habs
        · exact hinv.h_pos_abs x hxR (by simpa [sMid, hTmp, hxu] using hxPos)
      flow_cap := hinv.flow_cap
      h_edge := fun x hxR p hp hpR hfl => by
        by_cases hxu : x = u
        · subst x
          obtain ⟨j, hj, hp_eq⟩ := List.mem_iff_getElem.mp hp
          have hj_cur : j < s.cur u := by rw [hcurEnd]; exact hj
          have hadm := hinv.cur_no_adm u huR habs j hj_cur
          have hget : (cfg.incEdges u).getD j (0, false, 0) = p := by
            simpa [List.getD_eq_getElem?_getD, hj] using hp_eq
          rw [hget] at hadm
          rcases hadm with h1 | h2 | h3
          · exact absurd hpR (by simp [sMid] at *; simp [h1])
          · exact absurd hfl (by simp [sMid] at *; omega)
          · have hle_nbr : s.h p.2.2 ≤ hTmp p.2.2 := hle_hTmp p.2.2
            dsimp only [sMid, hTmp] at hle_nbr ⊢
            simp only [↓reduceIte]; omega
        · have he := hinv.h_edge x hxR p hp hpR hfl
          have hle_nbr : s.h p.2.2 ≤ hTmp p.2.2 := hle_hTmp p.2.2
          dsimp only [sMid, hTmp] at hle_nbr ⊢
          simp only [hxu, ↓reduceIte]; omega
      cur_no_adm := fun x hxR hxAbs j hj => by
        by_cases hxu : x = u
        · exfalso; simp [sMid, hxu] at hj
        · simp only [sMid, hxu, ↓reduceIte] at hj
          have hadm := hinv.cur_no_adm x hxR hxAbs j hj
          rcases hadm with h1 | h2 | h3
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
          · right; right
            simp only [sMid, hTmp, hxu, ↓reduceIte]
            exact le_trans h3 (hle_hTmp _)
      cur_zero_of_abs_lt := fun x hxR hxLt => by
        by_cases hxu : x = u
        · exfalso; simp only [sMid] at hxLt; rw [hxu] at hxLt; omega
        · simp only [sMid, hxu, ↓reduceIte]; exact hinv.cur_zero_of_abs_lt x hxR hxLt
      flow_balance := hinv.flow_balance
      degR_eq := hinv.degR_eq
      degR_peel := hinv.degR_peel
      active_cov := hinv.active_cov
      active_mem_inActive := hinv.active_mem_inActive
      active_nodup := hinv.active_nodup
      active_sub := hinv.active_sub
      no_ex_isolated := fun x hx0 => by
        have hx := hinv.no_ex_isolated x hx0
        have hxu : x ≠ u := fun h => by rw [h] at hx; rw [hx.1] at hexPos; omega
        refine ⟨hx.1, ?_, hx.2.2.1, hx.2.2.2⟩
        simp only [sMid, hTmp, hxu, ↓reduceIte]; exact hx.2.1 }

lemma volAtLevel_erase_u {cfg : PruneCfg} {inR : ℕ → Bool} {h : ℕ → ℕ}
    {u ℓ : ℕ} (hcfgX : cfg.X = Finset.range cfg.G.n) (huN : u < cfg.G.n) (huR : inR u = true)
    (hℓH : ℓ < cfg.H) :
    let hTmp := fun x => if x = u then cfg.H else h x
    volAtLevel cfg inR hTmp ℓ =
      if ℓ = h u then volAtLevel cfg inR h ℓ - cfg.degX u else volAtLevel cfg inR h ℓ := by
  intro hTmp
  have huX : u ∈ cfg.X := by rw [hcfgX]; exact Finset.mem_range.mpr huN
  have hsum_old := Finset.add_sum_erase cfg.X
    (fun x => if (inR x && decide (h x = ℓ)) = true then cfg.degX x else 0) huX
  have hsum_new := Finset.add_sum_erase cfg.X
    (fun x => if (inR x && decide (hTmp x = ℓ)) = true then cfg.degX x else 0) huX
  have herase :
      (∑ x ∈ cfg.X.erase u, if (inR x && decide (hTmp x = ℓ)) = true then cfg.degX x else 0) =
      (∑ x ∈ cfg.X.erase u, if (inR x && decide (h x = ℓ)) = true then cfg.degX x else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hne : x ≠ u := (Finset.mem_erase.mp hx).1
    simp [hTmp, hne]
  have htu : (if (inR u && decide (hTmp u = ℓ)) = true then cfg.degX u else 0) = 0 := by
    simp [hTmp, show cfg.H ≠ ℓ by omega]
  unfold volAtLevel
  rw [← hsum_new, ← hsum_old, herase, htu, zero_add]
  by_cases hhu : ℓ = h u
  · simp [huR, hhu]
  · simp [huR, show h u ≠ ℓ by omega, hhu]

lemma hasCsrAt_of_preservedOutside2 {mem₁ mem₂ : ℕ → ℕ}
    {gAddr inBAddr outRAddr workAddr n m H lenG csrAddr : ℕ} {G : Cited.Graph}
    (hpr : PreservedOutside2 mem₁ mem₂ outRAddr (outRAddr + n)
      (wHArr workAddr n m H) (workAddr + pruneWorkSpace n m H))
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr n m H lenG)
    (hn : G.n = n) (hm : G.m = m)
    (hcsr : HasCsrAt mem₁ csrAddr G) :
    HasCsrAt mem₂ csrAddr G := by
  refine ⟨fun u hu => ?_, fun u hu j hj => ?_⟩
  · rw [hpr (csrAddr + u)
      (by rcases hdisj.2.1 with h | h <;> omega)
      (by dsimp [wHArr]; rcases hdisj.2.2.2.2.1 with h | h <;> omega)]
    exact hcsr.1 u hu
  · have hj_lt : csrOff G u + j < 2 * m := by
      have hs := csrOff_succ G u
      have hle := csrOff_le_two_mul_m G (u + 1)
      rw [← hm]; omega
    refine ⟨?_, ?_⟩
    · rw [hpr (csrAddr + 2 * G.n + 1 + csrOff G u + j)
        (by rcases hdisj.2.1 with h | h <;> omega)
        (by dsimp [wHArr]; rcases hdisj.2.2.2.2.1 with h | h <;> omega)]
      exact (hcsr.2 u hu j hj).1
    · rw [hpr (csrAddr + 2 * G.n + 1 + 2 * G.m + csrOff G u + j)
        (by rcases hdisj.2.1 with h | h <;> omega)
        (by dsimp [wHArr]; rcases hdisj.2.2.2.2.1 with h | h <;> omega)]
      exact (hcsr.2 u hu j hj).2

lemma list_length_le_map_sum {L : List ℕ} {f : ℕ → ℕ}
    (hf : ∀ a ∈ L, 1 ≤ f a) :
    L.length ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have ha := hf a List.mem_cons_self
    have ht := ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

lemma walkPref_props {u lvl H : ℕ} {buckets1 : ℕ → List ℕ}
    (hb_nd : ∀ ℓ, 1 ≤ ℓ → ℓ < H → (buckets1 ℓ).Nodup)
    (hb_disj : ∀ ℓ₁ ℓ₂ x, 1 ≤ ℓ₁ → ℓ₁ < H → 1 ≤ ℓ₂ → ℓ₂ < H → ℓ₁ ≠ ℓ₂ →
      x ∈ buckets1 ℓ₁ → x ∉ buckets1 ℓ₂)
    (hu_not : ∀ ℓ, 1 ≤ ℓ → ℓ < H → u ∉ buckets1 ℓ)
    (h1 : 1 ≤ lvl + 1) :
    ∀ k, lvl + 1 + k ≤ H →
      (walkPref u buckets1 lvl k).head? = some u ∧
      (walkPref u buckets1 lvl k).Nodup ∧
      ∀ x, x ∈ walkPref u buckets1 lvl k ↔ x = u ∨ ∃ j < k, x ∈ buckets1 (lvl + 1 + j)
  | 0, _ => ⟨rfl, List.nodup_singleton u, fun x => by simp [walkPref]⟩
  | k + 1, hkH => by
    have hk_le : lvl + 1 + k ≤ H := by omega
    obtain ⟨hh, hnd, hmem⟩ := walkPref_props hb_nd hb_disj hu_not h1 k hk_le
    have hℓ1 : 1 ≤ lvl + 1 + k := by omega
    have hℓH : lvl + 1 + k < H := by omega
    refine ⟨?_, ?_, ?_⟩
    · simp only [walkPref]
      cases hwp : walkPref u buckets1 lvl k with
      | nil => simp [hwp] at hh
      | cons hd tl => simp only [hwp, List.head?_cons] at hh; simp [hh]
    · simp only [walkPref, List.nodup_append]
      refine ⟨hnd, hb_nd _ hℓ1 hℓH, fun x hx1 y hy2 hxy => ?_⟩
      subst hxy
      rcases (hmem x).mp hx1 with rfl | ⟨j, hj, hxj⟩
      · exact hu_not _ hℓ1 hℓH hy2
      · exact hb_disj _ _ x (by omega) (by omega) hℓ1 hℓH (by omega) hxj hy2
    · intro x
      simp only [walkPref, List.mem_append, hmem x]
      constructor
      · rintro ((rfl | ⟨j, hj, hxj⟩) | hxk)
        · exact Or.inl rfl
        · exact Or.inr ⟨j, by omega, hxj⟩
        · exact Or.inr ⟨k, Nat.lt_succ_self k, hxk⟩
      · rintro (rfl | ⟨j, hj, hxj⟩)
        · exact Or.inl (Or.inl rfl)
        · by_cases hjk : j = k
          · subst hjk; exact Or.inr hxj
          · exact Or.inl (Or.inr ⟨j, by omega, hxj⟩)

lemma foldl_removeOneFromR_static (cfg : PruneCfg) :
    ∀ (L : List ℕ) (ps : PruneState),
      (L.foldl (fun st y => removeOneFromR cfg y st) ps).h = ps.h ∧
      (L.foldl (fun st y => removeOneFromR cfg y st) ps).cur = ps.cur ∧
      (L.foldl (fun st y => removeOneFromR cfg y st) ps).abs = ps.abs ∧
      (L.foldl (fun st y => removeOneFromR cfg y st) ps).flow = ps.flow := by
  have hstep : ∀ (y : ℕ) (ps : PruneState),
      (removeOneFromR cfg y ps).h = ps.h ∧
      (removeOneFromR cfg y ps).cur = ps.cur ∧
      (removeOneFromR cfg y ps).abs = ps.abs ∧
      (removeOneFromR cfg y ps).flow = ps.flow := by
    intro y ps
    have he : ∀ (E : List (ℕ × Bool × ℕ)) (qs : PruneState),
        (E.foldl (removeEdgeStep cfg ps.flow (fun z => if z = y then false else ps.inR z)) qs).h = qs.h ∧
        (E.foldl (removeEdgeStep cfg ps.flow (fun z => if z = y then false else ps.inR z)) qs).cur = qs.cur ∧
        (E.foldl (removeEdgeStep cfg ps.flow (fun z => if z = y then false else ps.inR z)) qs).abs = qs.abs ∧
        (E.foldl (removeEdgeStep cfg ps.flow (fun z => if z = y then false else ps.inR z)) qs).flow = qs.flow := by
      intro E
      induction E with
      | nil => intro qs; exact ⟨rfl, rfl, rfl, rfl⟩
      | cons e es ihe =>
        intro qs; simp only [List.foldl_cons]
        rcases ihe (removeEdgeStep cfg ps.flow (fun z => if z = y then false else ps.inR z) qs e) with ⟨h1, h2, h3, h4⟩
        have hbase : ∀ r : PruneState,
            (removeEdgeStep cfg ps.flow (fun z => if z = y then false else ps.inR z) r e).h = r.h ∧
            (removeEdgeStep cfg ps.flow (fun z => if z = y then false else ps.inR z) r e).cur = r.cur ∧
            (removeEdgeStep cfg ps.flow (fun z => if z = y then false else ps.inR z) r e).abs = r.abs ∧
            (removeEdgeStep cfg ps.flow (fun z => if z = y then false else ps.inR z) r e).flow = r.flow := fun r => by
          dsimp [removeEdgeStep]; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩
        rcases hbase qs with ⟨b1, b2, b3, b4⟩
        exact ⟨h1.trans b1, h2.trans b2, h3.trans b3, h4.trans b4⟩
    exact he (cfg.incEdges y) _
  intro L
  induction L with
  | nil => intro ps; exact ⟨rfl, rfl, rfl, rfl⟩
  | cons y ys ih =>
    intro ps; simp only [List.foldl_cons]
    rcases ih (removeOneFromR cfg y ps) with ⟨h1, h2, h3, h4⟩
    rcases hstep y ps with ⟨g1, g2, g3, g4⟩
    exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4⟩

lemma foldl_removeOneFromR_inR (cfg : PruneCfg) :
    ∀ (L : List ℕ) (ps : PruneState) (x : ℕ),
      (L.foldl (fun st y => removeOneFromR cfg y st) ps).inR x =
        (ps.inR x && !(x ∈ L)) := by
  intro L
  induction L with
  | nil => intro ps x; simp
  | cons y ys ih =>
    intro ps x
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih _ x, removeOneFromR_inR]
    by_cases hxy : x = y <;> simp [hxy]

lemma reg_ne_removeOne_scratch {r : ℕ} (hr : r ≤ prCsrAdjH) :
    r ≠ prStart ∧ r ≠ prEnd ∧ r ≠ prJ ∧ r ≠ prW ∧ r ≠ prIdx ∧ r ≠ prDir ∧
      r ≠ prRc ∧ r ≠ prTmp1 ∧ r ≠ prTmp2 ∧ r ≠ prTmp3 ∧ r ≠ prI ∧ r ≠ prU := by
  dsimp [prCsrAdjH, prStart, prEnd, prJ, prW, prIdx, prDir, prRc, prTmp1, prTmp2, prTmp3, prI, prU] at hr ⊢
  omega

abbrev freezeStateOf (cfg : PruneCfg) (sMid : PruneState) (remList : List ℕ) (i : ℕ) :
    PruneState :=
  (remList.take i).foldl (fun st a => removeOneFromR cfg a st) sMid

abbrev freezeRemVol (cfg : PruneCfg) (remList : List ℕ) (i : ℕ) : ℕ :=
  ((remList.drop i).map fun a => (cfg.incEdges a).length).sum

structure FreezeRemInv (cfg : PruneCfg) (gAddr csrAddr inBAddr outRAddr workAddr : ℕ)
    (A : Finset ℕ) (sMid : PruneState) (remList : List ℕ) (st₀ st6 : State)
    (i : ℕ) (st : State) : Prop where
  i_le : i ≤ remList.length
  reg_i : st.regs prI = i
  reg_suf : st.regs prSuf = remList.length
  reg_actTop : st.regs prActTop = (freezeStateOf cfg sMid remList i).active.length
  reg_peelTop : st.regs prPeelTop = (freezeStateOf cfg sMid remList i).peelQ.length
  regs_agree : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop → st.regs r = st₀.regs r
  stepRegs : PruneStepRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st
  pos_eq : st.pos = st₀.pos
  pres_out : PreservedOutside2 st₀.mem st.mem outRAddr (outRAddr + cfg.G.n)
    (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H)
  below_ex : ∀ q, wHArr workAddr cfg.G.n cfg.G.m cfg.H ≤ q →
    q < wEx workAddr cfg.G.n cfg.G.m cfg.H → st.mem q = st6.mem q
  above_ln : ∀ q, wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤ q →
    q < outRAddr ∨ outRAddr + cfg.G.n ≤ q → st.mem q = st6.mem q
  outR_eq : ∀ x < cfg.G.n,
    st.mem (outRAddr + x) = if (freezeStateOf cfg sMid remList i).inR x = true then 1 else 0
  ex_eq : ∀ x < cfg.G.n,
    st.mem (wEx workAddr cfg.G.n cfg.G.m cfg.H + x) = (freezeStateOf cfg sMid remList i).ex x
  degR_eq : ∀ x < cfg.G.n,
    st.mem (wDegR workAddr cfg.G.n cfg.G.m cfg.H + x) = (freezeStateOf cfg sMid remList i).degR x
  inAct_eq : ∀ x < cfg.G.n,
    st.mem (wInAct workAddr cfg.G.n cfg.G.m cfg.H + x) =
      if (freezeStateOf cfg sMid remList i).inActive x = true then 1 else 0
  actStk_eq : ∀ q < (freezeStateOf cfg sMid remList i).active.length,
    st.mem (wActStk workAddr cfg.G.n cfg.G.m cfg.H + q) =
      (freezeStateOf cfg sMid remList i).active.getD
        ((freezeStateOf cfg sMid remList i).active.length - 1 - q) 0
  peelStk_eq : ∀ q < (freezeStateOf cfg sMid remList i).peelQ.length,
    st.mem (wPeelStk workAddr cfg.G.n cfg.G.m cfg.H + q) =
      (freezeStateOf cfg sMid remList i).peelQ.getD
        ((freezeStateOf cfg sMid remList i).peelQ.length - 1 - q) 0
  sw : SweepInv cfg (A \ (remList.take i).toFinset) (freezeStateOf cfg sMid remList i)
  pq : PeelQInv cfg (freezeStateOf cfg sMid remList i)
  ex_bd : ∀ x < cfg.G.n, (freezeStateOf cfg sMid remList i).ex x ≤ 4 * cfg.C_cap * cfg.G.m

lemma freezeStep_rem_step {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {A : Finset ℕ} {sMid : PruneState} {remList : List ℕ} {st₀ st6 : State}
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hval : cfg.Valid)
    (hcsr : HasCsrAt st₀.mem csrAddr cfg.G)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w)
    (hrem_nd : remList.Nodup)
    (hrem_sub : ∀ x ∈ remList, x < cfg.G.n ∧ sMid.inR x = true)
    (hrem_arr : ∀ k < remList.length,
      st6.mem (wRemArr workAddr cfg.G.n cfg.G.m cfg.H + k) = remList.getD k 0)
    (hflow6 : ∀ idx < cfg.G.m,
      st6.mem (wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx) = (↑cfg.C_cap + sMid.flow idx).toNat) :
    ∀ i st,
      FreezeRemInv cfg gAddr csrAddr inBAddr outRAddr workAddr A sMid remList st₀ st6 i st →
      (if st.regs prI < st.regs prSuf then 1 else 0) ≠ 0 →
      ∃ stepCost, Triple w p (fun st' => st' = st)
        (seqStmts
          [ .assign prU (.load (.bin .add (.reg prRemArr) (.reg prI)))
          , removeOneFromRStmt
          , .assign prI (.bin .add (.reg prI) (.const 1)) ])
        (fun o st' => match o with
          | .returned u =>
            normalPost (FreezeRemInv cfg gAddr csrAddr inBAddr outRAddr workAddr
              A sMid remList st₀ st6 remList.length) (.returned u) st' ∧
              Expr.size (.bin .lt (.reg prI) (.reg prSuf)) + stepCost + 1 ≤
                50 * (remList.length - i) + 152 * freezeRemVol cfg remList i + 10
          | .normal =>
            ∃ j, FreezeRemInv cfg gAddr csrAddr inBAddr outRAddr workAddr A sMid remList st₀ st6 j st' ∧
              remList.length - j < remList.length - i ∧
              Expr.size (.bin .lt (.reg prI) (.reg prSuf)) + stepCost +
                (50 * (remList.length - j) + 152 * freezeRemVol cfg remList j + 10) + 1 ≤
                50 * (remList.length - i) + 152 * freezeRemVol cfg remList i + 10)
        (fun _ => stepCost) := by
  intro i st hrm hne
  have hlt2w : ∀ k, k < workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H → k < 2 ^ w := fun k hk => by
    unfold PruneWordBound at hw; omega
  have hi_lt : i < remList.length := by
    by_contra hge
    have hge' : ¬ st.regs prI < st.regs prSuf := by
      rw [hrm.reg_i, hrm.reg_suf]; omega
    simp [hge'] at hne
  let a := remList[i]
  let d := (cfg.incEdges a).length
  have ha_mem : a ∈ remList := List.getElem_mem hi_lt
  have ha_notin_take : a ∉ remList.take i := by
    intro hm
    obtain ⟨j, hj_len, hj_eq⟩ := List.mem_iff_getElem.mp hm
    rw [List.length_take_of_le (le_of_lt hi_lt)] at hj_len
    rw [List.getElem_take] at hj_eq
    have hno := (List.Nodup.getElem_inj_iff hrem_nd).mp hj_eq
    omega
  have haR_i : (freezeStateOf cfg sMid remList i).inR a = true := by
    dsimp [freezeStateOf]; rw [foldl_removeOneFromR_inR]
    simp [(hrem_sub a ha_mem).2, ha_notin_take]
  have hsw_i := hrm.sw
  have hpq_i := hrm.pq
  have hex_i := hrm.ex_bd
  have hfit_all : remList.length ≤ cfg.G.n := by
    have hsub_n : ∀ x ∈ remList, x ∈ Finset.range cfg.G.n := fun x hx =>
      Finset.mem_range.mpr (hrem_sub x hx).1
    calc remList.length = remList.toFinset.card := (List.toFinset_card_of_nodup hrem_nd).symm
      _ ≤ (Finset.range cfg.G.n).card := Finset.card_le_card (fun x hx => hsub_n x (List.mem_toFinset.mp hx))
      _ = cfg.G.n := Finset.card_range cfg.G.n
  have hrem_i_eq : st.mem (wRemArr workAddr cfg.G.n cfg.G.m cfg.H + i) = a := by
    have hge : wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤
        wRemArr workAddr cfg.G.n cfg.G.m cfg.H + i := by
      dsimp [wLvlNext, wRemArr]; omega
    have hout : wRemArr workAddr cfg.G.n cfg.G.m cfg.H + i < outRAddr ∨
        outRAddr + cfg.G.n ≤ wRemArr workAddr cfg.G.n cfg.G.m cfg.H + i := by
      have hlt_ws : wRemArr workAddr cfg.G.n cfg.G.m cfg.H + i <
          workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H := by
        unfold pruneWorkSpace; dsimp [wRemArr]; omega
      dsimp [wRemArr] at *; rcases hdisj.2.2.2.2.2.2 with h | h <;> omega
    rw [hrm.above_ln _ hge hout, hrem_arr i hi_lt]
    exact List.getD_eq_getElem _ _ hi_lt
  have htake_succ : freezeStateOf cfg sMid remList (i + 1) =
      removeOneFromR cfg a (freezeStateOf cfg sMid remList i) := by
    dsimp [freezeStateOf]
    rw [List.take_succ_eq_append_getElem hi_lt, List.foldl_append]; rfl
  have hs_step_inv := removeOneFromR_inv hval hsw_i haR_i
  have hsw_next : SweepInv cfg (A \ (remList.take (i + 1)).toFinset)
      (freezeStateOf cfg sMid remList (i + 1)) := by
    rw [htake_succ]
    have hA_eq : A \ (remList.take (i + 1)).toFinset = (A \ (remList.take i).toFinset) \ {a} := by
      ext x
      simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_singleton,
        List.take_succ_eq_append_getElem hi_lt, List.mem_append, List.mem_singleton, a]
      tauto
    rw [hA_eq]; exact hs_step_inv.1
  have hpq_next : PeelQInv cfg (freezeStateOf cfg sMid remList (i + 1)) := by
    rw [htake_succ]; exact removeOneFromR_peelQInv (fun x hxR => hsw_i.inR_sub x hxR) hpq_i
  have hex_next : ∀ x < cfg.G.n, (freezeStateOf cfg sMid remList (i + 1)).ex x ≤ 4 * cfg.C_cap * cfg.G.m := by
    rw [htake_succ]
    have hsw_succ : SweepInv cfg (A \ (remList.take (i + 1)).toFinset)
        (removeOneFromR cfg a (freezeStateOf cfg sMid remList i)) := by
      rw [← htake_succ]; exact hsw_next
    exact ex_bound_of_sweep_after_removeOne hcfgX hval.1 hex_i hsw_succ
  have hrem_drop : freezeRemVol cfg remList i = d + freezeRemVol cfg remList (i + 1) := by
    dsimp [freezeRemVol, d, a]
    rw [List.drop_eq_getElem_cons hi_lt]
    simp only [List.map_cons, List.sum_cons]
  have hcsr_i : HasCsrAt st.mem csrAddr cfg.G :=
    hasCsrAt_of_preservedOutside2 hrm.pres_out hdisj rfl rfl hcsr
  have hflow_i : ∀ idx < cfg.G.m,
      st.mem (wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx) =
        (↑cfg.C_cap + (freezeStateOf cfg sMid remList i).flow idx).toNat := by
    intro idx hidx
    have hge : wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤
        wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx := by dsimp [wLvlNext, wFlowEnc]; omega
    have hout : wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx < outRAddr ∨
        outRAddr + cfg.G.n ≤ wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx := by
      have : wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx <
          workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H := by
        unfold pruneWorkSpace; dsimp [wFlowEnc]; omega
      dsimp [wFlowEnc] at *; rcases hdisj.2.2.2.2.2.2 with h | h <;> omega
    rw [hrm.above_ln _ hge hout, hflow6 idx hidx,
      (foldl_removeOneFromR_static cfg (remList.take i) sMid).2.2.2]
  have hrem_addr : wRemArr workAddr cfg.G.n cfg.G.m cfg.H + i < 2 ^ w :=
    hlt2w _ (by unfold pruneWorkSpace; dsimp [wRemArr]; omega)
  have hpeel_lt_i : ∀ x ∈ (freezeStateOf cfg sMid remList i).peelQ, x < cfg.G.n ∧
      ((if x = a then false else (freezeStateOf cfg sMid remList i).inR x) = true →
        (freezeStateOf cfg sMid remList i).degR x < cfg.θ_out_nat) := fun x hx =>
    ⟨Finset.mem_range.mp (by rw [← hcfgX]; exact hpq_i.2.1 x hx),
      fun _ => hpq_i.2.2 x hx⟩
  have hpeel_iso_i : ∀ x, (cfg.incEdges x).length = 0 →
      x ∉ (freezeStateOf cfg sMid remList i).peelQ :=
    fun x hx0 => (hsw_i.no_ex_isolated x hx0).2.2.2
  let r_u := Function.update st.regs prU a
  let st_u : State := { mem := st.mem, regs := r_u, pos := st.pos }
  have hrm_tri := removeOneFromR_triple (p := p) (cfg := cfg)
    (gAddr := gAddr) (csrAddr := csrAddr) (inBAddr := inBAddr) (outRAddr := outRAddr)
    (workAddr := workAddr) (a := a) (A := A \ (remList.take i).toFinset)
    (s := freezeStateOf cfg sMid remList i) ((freezeStateOf cfg sMid remList i).peelQ)
    st_u hcfgX hval hsw_i haR_i hpq_i.1 hpeel_lt_i hpeel_iso_i hw hdisj hcsr_w houtR_w hcsr_i
  refine ⟨150 * d + 41, ?_⟩
  intro st_in ω hsi
  subst st_in
  have hs_u : Runs w p ω (.assign prU (.load (.bin .add (.reg prRemArr) (.reg prI))))
      st .normal st_u 5 :=
    runs_assign_iff.mpr ⟨a,
      eval_load_add_eq w st prRemArr prI hrm.stepRegs.reg_remArr hrm.reg_i hrem_addr hrem_i_eq,
      rfl, rfl, by simp [Expr.size]⟩
  have hst_u_pre : st_u = st_u ∧ PruneStepRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st_u ∧
      st_u.regs prU = a ∧
      st_u.regs prActTop = (freezeStateOf cfg sMid remList i).active.length ∧
      st_u.regs prPeelTop = (freezeStateOf cfg sMid remList i).peelQ.length ∧
      (∀ u < cfg.G.n, st_u.mem (outRAddr + u) =
        if (freezeStateOf cfg sMid remList i).inR u = true then 1 else 0) ∧
      (∀ u < cfg.G.n, st_u.mem (wEx workAddr cfg.G.n cfg.G.m cfg.H + u) =
        (freezeStateOf cfg sMid remList i).ex u) ∧
      (∀ u < cfg.G.n, st_u.mem (wDegR workAddr cfg.G.n cfg.G.m cfg.H + u) =
        (freezeStateOf cfg sMid remList i).degR u) ∧
      (∀ u < cfg.G.n, st_u.mem (wInAct workAddr cfg.G.n cfg.G.m cfg.H + u) =
        if (freezeStateOf cfg sMid remList i).inActive u = true then 1 else 0) ∧
      (∀ q < (freezeStateOf cfg sMid remList i).active.length,
        st_u.mem (wActStk workAddr cfg.G.n cfg.G.m cfg.H + q) =
          (freezeStateOf cfg sMid remList i).active.getD
            ((freezeStateOf cfg sMid remList i).active.length - 1 - q) 0) ∧
      (∀ q < (freezeStateOf cfg sMid remList i).peelQ.length,
        st_u.mem (wPeelStk workAddr cfg.G.n cfg.G.m cfg.H + q) =
          (freezeStateOf cfg sMid remList i).peelQ.getD
            ((freezeStateOf cfg sMid remList i).peelQ.length - 1 - q) 0) ∧
      (∀ idx < cfg.G.m, st_u.mem (wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx) =
        (↑cfg.C_cap + (freezeStateOf cfg sMid remList i).flow idx).toNat) :=
    ⟨rfl, pruneStepRegs_of_agree hrm.stepRegs
        (fun r hr _ _ => by
          dsimp [st_u, r_u]
          rw [Function.update_of_ne (reg_ne_removeOne_scratch hr).2.2.2.2.2.2.2.2.2.2.2]),
      by dsimp [st_u, r_u]; rw [Function.update_self],
      by dsimp [st_u, r_u]; rw [Function.update_of_ne (by decide)]; exact hrm.reg_actTop,
      by dsimp [st_u, r_u]; rw [Function.update_of_ne (by decide)]; exact hrm.reg_peelTop,
      hrm.outR_eq, hrm.ex_eq, hrm.degR_eq, hrm.inAct_eq, hrm.actStk_eq, hrm.peelStk_eq, hflow_i⟩
  rcases hrm_tri st_u ω hst_u_pre with ⟨or', st_r, c_r, hr_r, hq_r, hc_r⟩
  cases or' with
  | returned => exact False.elim hq_r
  | normal =>
    rcases hq_r with ⟨hreg_r, hptrs_r, _, hrAT_r, hrPT_r, hpos_r, hpr_r,
      houtR_r, hex_r, hdegR_r, hinAct_r, hactStk_r, hpeelStk_r⟩
    have hr_r_i : st_r.regs prI = i := by
      rw [hreg_r prI (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      dsimp [st_u, r_u]; rw [Function.update_of_ne (by decide)]; exact hrm.reg_i
    have hi1_lt2w : i + 1 < 2 ^ w := by unfold PruneWordBound at hw; omega
    let r_next := Function.update st_r.regs prI (i + 1)
    let st_next : State := { mem := st_r.mem, regs := r_next, pos := st_r.pos }
    have hs_inc : Runs w p ω (.assign prI (.bin .add (.reg prI) (.const 1))) st_r .normal st_next 4 :=
      runs_assign_iff.mpr ⟨i + 1,
        Expr.eval_bin (op := .add) (eval_reg_eq w st_r prI hr_r_i) (Expr.eval_const (by omega))
          (by dsimp only [BinOp.eval]; exact hi1_lt2w),
        rfl, rfl, by simp [Expr.size]⟩
    have hreg_next : ∀ r ≤ prCsrAdjH, r ≠ prActTop → r ≠ prPeelTop →
        st_next.regs r = st₀.regs r := by
      intro r hr hAT hPT
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hI, hU⟩ := reg_ne_removeOne_scratch hr
      dsimp [st_next, r_next]
      rw [Function.update_of_ne hI, hreg_r r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hAT hPT]
      dsimp [st_u, r_u]; rw [Function.update_of_ne hU]
      exact hrm.regs_agree r hr hAT hPT
    have hr_suf_next : st_next.regs prSuf = remList.length := by
      dsimp [st_next, r_next]; rw [Function.update_of_ne (by decide)]
      rw [hreg_r prSuf (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      dsimp [st_u, r_u]; rw [Function.update_of_ne (by decide)]; exact hrm.reg_suf
    have hr_sRes_peel :
        ((cfg.incEdges a).foldl
          (removeEdgeStep cfg (freezeStateOf cfg sMid remList i).flow
            (fun x => if x = a then false else (freezeStateOf cfg sMid remList i).inR x))
          ⟨fun x => if x = a then false else (freezeStateOf cfg sMid remList i).inR x,
            (freezeStateOf cfg sMid remList i).h, (freezeStateOf cfg sMid remList i).cur,
            (freezeStateOf cfg sMid remList i).abs, (freezeStateOf cfg sMid remList i).ex,
            (freezeStateOf cfg sMid remList i).degR, (freezeStateOf cfg sMid remList i).flow,
            (freezeStateOf cfg sMid remList i).active, (freezeStateOf cfg sMid remList i).inActive,
            (freezeStateOf cfg sMid remList i).peelQ,
            (freezeStateOf cfg sMid remList i).steps⟩).peelQ =
          (freezeStateOf cfg sMid remList (i + 1)).peelQ := by
      rw [htake_succ]; rfl
    have hpres_next : PreservedOutside2 st₀.mem st_next.mem outRAddr (outRAddr + cfg.G.n)
        (wHArr workAddr cfg.G.n cfg.G.m cfg.H) (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) := by
      intro q hq1 hq2
      have hq2' : q < wEx workAddr cfg.G.n cfg.G.m cfg.H ∨
          wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤ q := by
        rcases hq2 with h | h
        · exact Or.inl (by dsimp [wHArr, wEx] at h ⊢; omega)
        · unfold pruneWorkSpace at h
          exact Or.inr (by dsimp [wLvlNext, wLvlHead] at h ⊢; omega)
      rw [hpr_r q hq1 hq2', hrm.pres_out q hq1 hq2]
    have hbelow_next : ∀ q, wHArr workAddr cfg.G.n cfg.G.m cfg.H ≤ q →
        q < wEx workAddr cfg.G.n cfg.G.m cfg.H → st_next.mem q = st6.mem q := by
      intro q hq1 hq2
      have hout : q < outRAddr ∨ outRAddr + cfg.G.n ≤ q := by
        have hq_lo : workAddr ≤ q := by dsimp [wHArr] at hq1; omega
        have hq_ws : q < workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H := by
          unfold pruneWorkSpace; dsimp [wEx] at hq2; omega
        rcases hdisj.2.2.2.2.2.2 with h | h <;> omega
      rw [hpr_r q hout (Or.inl hq2), hrm.below_ex q hq1 hq2]
    have habove_next : ∀ q, wLvlNext workAddr cfg.G.n cfg.G.m cfg.H ≤ q →
        q < outRAddr ∨ outRAddr + cfg.G.n ≤ q → st_next.mem q = st6.mem q := by
      intro q hq1 hq2
      rw [hpr_r q hq2 (Or.inr hq1), hrm.above_ln q hq1 hq2]
    have hinv_next : FreezeRemInv cfg gAddr csrAddr inBAddr outRAddr workAddr
        A sMid remList st₀ st6 (i + 1) st_next :=
      { i_le := by omega
        reg_i := by dsimp [st_next, r_next]; rw [Function.update_self]
        reg_suf := hr_suf_next
        reg_actTop := by dsimp [st_next, r_next]; rw [Function.update_of_ne (by decide), hrAT_r, htake_succ]
        reg_peelTop := by dsimp [st_next, r_next]; rw [Function.update_of_ne (by decide), hrPT_r, hr_sRes_peel]
        regs_agree := hreg_next
        stepRegs := pruneStepRegs_of_agree hptrs_r (fun r hr _ _ => by
          dsimp [st_next, r_next]
          rw [Function.update_of_ne (reg_ne_removeOne_scratch hr).2.2.2.2.2.2.2.2.2.2.1])
        pos_eq := hpos_r.trans hrm.pos_eq
        pres_out := hpres_next
        below_ex := hbelow_next
        above_ln := habove_next
        outR_eq := by simpa only [htake_succ] using houtR_r
        ex_eq := by simpa only [htake_succ] using hex_r
        degR_eq := by simpa only [htake_succ] using hdegR_r
        inAct_eq := by simpa only [htake_succ] using hinAct_r
        actStk_eq := by simpa only [htake_succ] using hactStk_r
        peelStk_eq := by simpa only [hr_sRes_peel] using hpeelStk_r
        sw := hsw_next
        pq := hpq_next
        ex_bd := hex_next }
    refine ⟨.normal, st_next, 5 + (c_r + 4 + 1) + 1, runs_seq hs_u (runs_seq hr_r hs_inc),
      ⟨i + 1, hinv_next, by omega, by simp [Expr.size, hrem_drop]; omega⟩,
      by dsimp only at hc_r ⊢; dsimp [d]; omega⟩


end MinCostFlow.Expander
