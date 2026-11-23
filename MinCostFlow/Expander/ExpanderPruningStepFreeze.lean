module

public import MinCostFlow.Expander.ExpanderPruningStepRelabel

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Expander Pruning Step Helpers (Freeze Step Invariant & Potential)
-/

namespace MinCostFlow.Expander

open Classical

public section

lemma freezeStep_sweep_inv {cfg : PruneCfg} {s : PruneState}
    (hinv : PruningInv cfg s) {u lvl : ℕ} (huR : s.inR u = true) (hexPos : 0 < s.ex u)
    (habs : s.abs u = cfg.degX u) (hcurEnd : s.cur u = (cfg.incEdges u).length)
    (huH : s.h u + 1 = cfg.H) (hlvlH : lvl < cfg.H) :
    let hTmp : ℕ → ℕ := fun x => if x = u then cfg.H else s.h x
    let A : Finset ℕ := cfg.X.filter fun x => s.inR x && decide (lvl + 1 ≤ hTmp x)
    let sMid : PruneState := { s with h := hTmp, cur := fun x => if x = u then 0 else s.cur x }
    SweepInv cfg A sMid := by
  dsimp only
  set hTmp : ℕ → ℕ := fun x => if x = u then cfg.H else s.h x
  set A : Finset ℕ := cfg.X.filter fun x => s.inR x && decide (lvl + 1 ≤ hTmp x)
  set sMid : PruneState := { s with h := hTmp, cur := fun x => if x = u then 0 else s.cur x }
  exact
    { inR_sub := hinv.inR_sub
      not_inR_B := hinv.not_inR_B
      h_le_H := by
        intro x hxR
        by_cases hxu : x = u
        · simp [sMid, hTmp, hxu]
        · have := le_of_lt (hinv.h_lt_H x hxR)
          simpa [sMid, hTmp, hxu] using this
      h_lt_H_notA := by
        intro x hxR hxNotA
        have hxX := hinv.inR_sub x hxR
        have hlt_lvl : hTmp x < lvl + 1 := by
          by_contra hge
          apply hxNotA
          simp only [A, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hxX, hxR, by omega⟩
        change hTmp x < cfg.H
        omega
      cur_le := by
        intro x hxR
        by_cases hxu : x = u
        · simp [sMid, hxu]
        · simpa [sMid, hxu] using hinv.cur_le x hxR
      abs_le := hinv.abs_le
      h_pos_abs := by
        intro x hxR hxpos
        by_cases hxu : x = u
        · subst hxu; exact habs
        · exact hinv.h_pos_abs x hxR (by simpa [sMid, hTmp, hxu] using hxpos)
      flow_cap := hinv.flow_cap
      h_edge := by
        intro x hxR p hp hpR hflt
        have hsh_le : ∀ y, s.h y ≤ if y = u then cfg.H else s.h y := fun y => by
          split_ifs with hyu
          · rw [hyu]; exact le_of_lt (hinv.h_lt_H u huR)
          · exact le_rfl
        by_cases hxu : x = u
        · subst hxu
          rcases list_mem_exists_getD (0, false, 0) (cfg.incEdges x) hp with ⟨j, hj, rfl⟩
          have hjc : j < s.cur x := by rw [hcurEnd]; exact hj
          have hadm := hinv.cur_no_adm x hxR habs j hjc
          dsimp only at hadm
          rcases hadm with hf | hsat | hle
          · exact False.elim (Bool.false_ne_true (hpR.symm.trans hf).symm)
          · exact False.elim (lt_irrefl _ (hsat ▸ hflt))
          · have h2 := hsh_le ((cfg.incEdges x).getD j (0, false, 0)).2.2
            change (if x = x then cfg.H else s.h x) ≤
              (if ((cfg.incEdges x).getD j (0, false, 0)).2.2 = x then cfg.H else
                s.h ((cfg.incEdges x).getD j (0, false, 0)).2.2) + 1
            simp only [↓reduceIte]
            omega
        · have hold := hinv.h_edge x hxR p hp hpR hflt
          have h2 := hsh_le p.2.2
          change (if x = u then cfg.H else s.h x) ≤ (if p.2.2 = u then cfg.H else s.h p.2.2) + 1
          rw [ite_eq_right hxu]
          omega
      cur_no_adm := by
        intro x hxR hxdeg j hj
        have hsh_le : ∀ y, s.h y ≤ if y = u then cfg.H else s.h y := fun y => by
          split_ifs with hyu
          · rw [hyu]; exact le_of_lt (hinv.h_lt_H u huR)
          · exact le_rfl
        by_cases hxu : x = u
        · subst hxu; simp [sMid] at hj
        · have hold := hinv.cur_no_adm x hxR hxdeg j (by simpa [sMid, hxu] using hj)
          dsimp only at hold ⊢
          set p := (cfg.incEdges x).getD j (0, false, 0)
          rcases hold with hf | hsat | hle
          · exact Or.inl hf
          · exact Or.inr (Or.inl hsat)
          · right; right
            have h2 := hsh_le p.2.2
            change (if x = u then cfg.H else s.h x) ≤ (if p.2.2 = u then cfg.H else s.h p.2.2)
            rw [ite_eq_right hxu]
            omega
      cur_zero_of_abs_lt := by
        intro x hxR hxlt
        by_cases hxu : x = u
        · subst hxu; simp [sMid]
        · simpa [sMid, hxu] using hinv.cur_zero_of_abs_lt x hxR hxlt
      flow_balance := hinv.flow_balance
      degR_eq := hinv.degR_eq
      degR_peel := hinv.degR_peel
      active_cov := hinv.active_cov
      active_mem_inActive := hinv.active_mem_inActive
      active_nodup := hinv.active_nodup
      active_sub := hinv.active_sub
      no_ex_isolated := by
        intro x hx0
        have hne := hinv.no_ex_isolated x hx0
        have hxu : x ≠ u := by
          rintro rfl
          omega
        simpa [sMid, hTmp, hxu] using hne }

lemma freezeStep_pot_le (cfg : PruneCfg) (s s' : PruneState) (volEA : ℕ)
    (hH3 : 3 ≤ cfg.H) (hvolEA : 1 ≤ volEA)
    (hsteps : s'.steps = s.steps + cfg.H + volEA)
    (hvol : volR cfg s' + volEA = volR cfg s)
    (hrel : relabelCurRem cfg s' ≤ relabelCurRem cfg s)
    (habs : sumAbsRem cfg s' ≤ sumAbsRem cfg s)
    (hplen : s'.peelQ.length ≤ s.peelQ.length + volEA)
    (hphi : phiActive s' ≤ phiActive s + 1 + volEA * (cfg.H + 1)) :
    s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧ pot cfg s' < pot cfg s := by
  have h1 : 2 * s'.peelQ.length ≤ 2 * s.peelQ.length + 2 * volEA := by omega
  have h2 : (3 * cfg.H + 8) * volR cfg s' + (3 * cfg.H + 8) * volEA =
      (3 * cfg.H + 8) * volR cfg s := by
    rw [← hvol]; ring
  have h3 : (cfg.H + 4) * relabelCurRem cfg s' ≤ (cfg.H + 4) * relabelCurRem cfg s :=
    Nat.mul_le_mul_left _ hrel
  have h4 : 2 * sumAbsRem cfg s' ≤ 2 * sumAbsRem cfg s := by omega
  have h5 : 2 * phiActive s' ≤ 2 * phiActive s + 2 + (2 * cfg.H + 2) * volEA := by
    have hmul : 2 * (volEA * (cfg.H + 1)) = (2 * cfg.H + 2) * volEA := by ring
    omega
  have hcoef : (2 * volEA) + (2 * cfg.H + 2) * volEA + (cfg.H + 4) * volEA =
      (3 * cfg.H + 8) * volEA := by ring
  have hpot_drop : pot cfg s' + (cfg.H + 4) * volEA ≤ pot cfg s + 2 := by
    unfold pot
    omega
  have hstep_gap : cfg.H + volEA + 2 ≤ (cfg.H + 4) * volEA := by nlinarith
  exact ⟨by omega, by omega⟩

lemma freezeStep_inv_pot {cfg : PruneCfg} (hcfg : cfg.Valid) {s : PruneState}
    (hinv : PruningInv cfg s) {u : ℕ} (huR : s.inR u = true) (hexPos : 0 < s.ex u)
    (habs : s.abs u = cfg.degX u) (hcurEnd : s.cur u = (cfg.incEdges u).length)
    (huH : s.h u + 1 = cfg.H) :
    let s' := freezeStep cfg u s
    PruningInv cfg s' ∧
    s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
    pot cfg s' < pot cfg s ∧
    volPminusB cfg s' + 2 * cfg.C_cap * cutPR cfg s' ≤
      volPminusB cfg s + 2 * cfg.C_cap * cutPR cfg s := by
  have hH3 := cfg.valid_three_le_H hcfg
  dsimp only [freezeStep]
  set hTmp : ℕ → ℕ := fun x => if x = u then cfg.H else s.h x
  have huX : u ∈ cfg.X := hinv.inR_sub u huR
  have hlen_u_pos : 1 ≤ (cfg.incEdges u).length := by
    by_contra h0
    have := (hinv.no_ex_isolated u (by omega)).1
    omega
  have hdegX_u_pos : 1 ≤ cfg.degX u := le_trans hlen_u_pos (incEdges_length_le_degX cfg u)
  have hpick := pickLevel_spec hcfg s.inR hTmp ⟨u, huX, huR, by simp [hTmp], hdegX_u_pos⟩
  dsimp only at hpick
  set lvl := pickLevel cfg s.inR hTmp
  have hlvl1 : 1 ≤ lvl := hpick.1
  have hlvlH : lvl < cfg.H := hpick.2.1
  have hvol_pick : 4 * cfg.C_cap * volAtLevel cfg s.inR hTmp lvl ≤
      volGeLevel cfg s.inR hTmp (lvl + 1) := hpick.2.2
  set AList := cfg.X.toList.filter fun x => s.inR x && decide (lvl + 1 ≤ hTmp x)
  set remList := u :: AList.erase u
  have hAList_nd : AList.Nodup := (Finset.nodup_toList cfg.X).filter _
  have hu_AList : u ∈ AList := by
    simp only [AList, List.mem_filter, Finset.mem_toList, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨huX, huR, ?_⟩
    simp [hTmp]; omega
  have hperm : remList.Perm AList := (List.perm_cons_erase hu_AList).symm
  have hrem_nd : remList.Nodup := hperm.nodup_iff.mpr hAList_nd
  set A : Finset ℕ := cfg.X.filter fun x => s.inR x && decide (lvl + 1 ≤ hTmp x)
  have hA_toFinset : remList.toFinset = A := by
    ext x
    simp only [List.mem_toFinset, hperm.mem_iff, AList, A, List.mem_filter, Finset.mem_toList,
      Finset.mem_filter]
  have hALinR : ∀ a ∈ remList, s.inR a = true := by
    intro a ha
    have ha' := hperm.mem_iff.mp ha
    simp only [AList, List.mem_filter, Bool.and_eq_true] at ha'
    exact ha'.2.1
  set sMid : PruneState :=
    { s with h := hTmp, cur := fun x => if x = u then 0 else s.cur x }
  have hMid_sw : SweepInv cfg A sMid :=
    freezeStep_sweep_inv hinv huR hexPos habs hcurEnd huH hlvlH
  have hMid_headH : ∀ x, sMid.inR x = true → sMid.h x < cfg.H ∨ remList.head? = some x := by
    intro x hxR
    by_cases hxu : x = u
    · subst hxu; right; rfl
    · left; change hTmp x < cfg.H; simp only [hTmp, hxu, ↓reduceIte]; exact hinv.h_lt_H x hxR
  have hfold := foldl_removeOneFromR_inv hcfg remList A sMid hrem_nd hALinR hMid_sw hMid_headH
  dsimp only at hfold
  set s1 := remList.foldl (fun st a => removeOneFromR cfg a st) sMid
  set volEA := (remList.map fun a => (cfg.incEdges a).length).sum
  set s' : PruneState := { s1 with steps := s.steps + cfg.H + volEA }
  have hs1_sw : SweepInv cfg ∅ s1 := by
    have := hfold.1
    rwa [hA_toFinset, Finset.sdiff_self] at this
  have hs1_inv : PruningInv cfg s1 := (pruningInv_iff_sweepInv_empty cfg s1).mpr hs1_sw
  have hs'_inv : PruningInv cfg s' :=
    { inR_sub := hs1_inv.inR_sub
      not_inR_B := hs1_inv.not_inR_B
      h_lt_H := hs1_inv.h_lt_H
      cur_le := hs1_inv.cur_le
      abs_le := hs1_inv.abs_le
      h_pos_abs := hs1_inv.h_pos_abs
      flow_cap := hs1_inv.flow_cap
      h_edge := hs1_inv.h_edge
      cur_no_adm := hs1_inv.cur_no_adm
      cur_zero_of_abs_lt := hs1_inv.cur_zero_of_abs_lt
      flow_balance := hs1_inv.flow_balance
      degR_eq := hs1_inv.degR_eq
      degR_peel := hs1_inv.degR_peel
      active_cov := hs1_inv.active_cov
      active_mem_inActive := hs1_inv.active_mem_inActive
      active_nodup := hs1_inv.active_nodup
      active_sub := hs1_inv.active_sub
      no_ex_isolated := hs1_inv.no_ex_isolated }
  have hvolEA_ge1 : 1 ≤ volEA := by
    dsimp only [volEA, remList]
    rw [List.map_cons, List.sum_cons]
    omega
  have hs'_inR : ∀ x, s'.inR x = (s.inR x && !(x ∈ A)) := by
    intro x
    change s1.inR x = _
    rw [hfold.2.1 x]
    have hxmem : x ∈ remList ↔ x ∈ A := by
      rw [← List.mem_toFinset, hA_toFinset]
    simp [sMid, hxmem]
  have hvol_eq : volR cfg s' + volEA = volR cfg s := by
    have hv1 : volR cfg s' = volR cfg s1 := rfl
    have hvMid : volR cfg sMid = volR cfg s := rfl
    rw [hv1, ← hvMid]
    exact hfold.2.2.1
  have hrel_le : relabelCurRem cfg s' ≤ relabelCurRem cfg s := by
    have h1 : relabelCurRem cfg s' = relabelCurRem cfg s1 := rfl
    have h2 : relabelCurRem cfg s1 ≤ relabelCurRem cfg sMid := hfold.2.2.2.1
    have h3 : relabelCurRem cfg sMid + 2 = relabelCurRem cfg s := by
      unfold relabelCurRem
      rw [← Finset.add_sum_erase _ _ huX, ← Finset.add_sum_erase cfg.X _ huX]
      have hrest : ∑ x ∈ cfg.X.erase u,
            (if sMid.inR x && decide (0 < (cfg.incEdges x).length) then
              (cfg.H - sMid.h x) * (2 * (cfg.incEdges x).length + 2) +
              (2 * (cfg.incEdges x).length + 1 - 2 * sMid.cur x)
            else 0) =
          ∑ x ∈ cfg.X.erase u,
            (if s.inR x && decide (0 < (cfg.incEdges x).length) then
              (cfg.H - s.h x) * (2 * (cfg.incEdges x).length + 2) +
              (2 * (cfg.incEdges x).length + 1 - 2 * s.cur x)
            else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hne : x ≠ u := (Finset.mem_erase.mp hx).1
        simp [sMid, hTmp, hne]
      set len := (cfg.incEdges u).length
      have h0len : decide (0 < len) = true := decide_eq_true hlen_u_pos
      have h1_u : (if sMid.inR u && decide (0 < len) then
            (cfg.H - sMid.h u) * (2 * len + 2) + (2 * len + 1 - 2 * sMid.cur u)
          else 0) = 2 * len + 1 := by
        dsimp only [sMid, hTmp]
        rw [huR, h0len, Bool.and_self]
        simp only [↓reduceIte, Nat.sub_self, Nat.zero_mul, Nat.mul_zero, Nat.sub_zero, zero_add]
      have h2_u : (if s.inR u && decide (0 < len) then
            (cfg.H - s.h u) * (2 * len + 2) + (2 * len + 1 - 2 * s.cur u)
          else 0) = (cfg.H - s.h u) * (2 * len + 2) + 1 := by
        rw [huR, h0len, Bool.and_self]
        simp only [↓reduceIte, hcurEnd]
        omega
      have hHu : cfg.H - s.h u = 1 := by omega
      rw [h1_u, h2_u, hHu, hrest]
      omega
    omega
  have habs_le : sumAbsRem cfg s' ≤ sumAbsRem cfg s := by
    have h1 : sumAbsRem cfg s' = sumAbsRem cfg s1 := rfl
    have h2 : sumAbsRem cfg sMid = sumAbsRem cfg s := rfl
    rw [h1, ← h2]
    exact hfold.2.2.2.2.1
  have hplen_le : s'.peelQ.length ≤ s.peelQ.length + volEA := by
    have h1 : s'.peelQ = s1.peelQ := rfl
    have h2 : sMid.peelQ = s.peelQ := rfl
    rw [h1, ← h2]
    exact hfold.2.2.2.2.2.2.2.1
  have hphi_Mid : phiActive sMid ≤ phiActive s + 1 := by
    unfold phiActive
    have hu_act : u ∈ s.active := hinv.active_cov u huR hexPos
    suffices h : ∀ (M : List ℕ), M.Nodup → u ∈ M →
        (M.map fun x => if sMid.inR x then sMid.h x + 2 else 2).sum =
          (M.map fun x => if s.inR x then s.h x + 2 else 2).sum + 1 by
      rw [h s.active hinv.active_nodup hu_act]
    intro M hnd hm
    induction M with
    | nil => simp at hm
    | cons x xs ih =>
      simp only [List.nodup_cons] at hnd
      rcases List.mem_cons.mp hm with rfl | hmem
      · have hrest : xs.map (fun y => if sMid.inR y then sMid.h y + 2 else 2) =
            xs.map (fun y => if s.inR y then s.h y + 2 else 2) := by
          apply List.map_congr_left
          intro y hy
          have hne : y ≠ u := fun heq => hnd.1 (heq ▸ hy)
          simp only [sMid, hTmp, hne, ↓reduceIte]
        simp only [List.map_cons, List.sum_cons, hrest]
        simp [sMid, hTmp, huR, ← huH]
        omega
      · have hne : x ≠ u := fun heq => hnd.1 (heq ▸ hmem)
        have ih' := ih hnd.2 hmem
        simp only [List.map_cons, List.sum_cons]
        have hx_eq : (if sMid.inR x then sMid.h x + 2 else 2) =
            (if s.inR x then s.h x + 2 else 2) := by simp [sMid, hTmp, hne]
        omega
  have hphi_le : phiActive s' ≤ phiActive s + 1 + volEA * (cfg.H + 1) := by
    have h1 : phiActive s' = phiActive s1 := rfl
    rw [h1]
    linarith [hfold.2.2.2.2.2.2.2.2.1]
  have hpot_pair := freezeStep_pot_le cfg s s' volEA hH3 hvolEA_ge1 rfl
    hvol_eq hrel_le habs_le hplen_le hphi_le
  have hsteps_pot : s'.steps + pot cfg s' ≤ s.steps + pot cfg s := hpot_pair.1
  have hpot_lt : pot cfg s' < pot cfg s := hpot_pair.2
  have hAinR : ∀ x ∈ A, s.inR x = true := by
    intro x hx
    simp only [A, Finset.mem_filter, Bool.and_eq_true] at hx
    exact hx.2.1
  have hvolGe_eq : volGeLevel cfg s.inR hTmp (lvl + 1) = ∑ x ∈ A, cfg.degX x := by
    unfold volGeLevel
    rw [Finset.sum_filter]
  have hvolP_eq : volPminusB cfg s' = volPminusB cfg s + volGeLevel cfg s.inR hTmp (lvl + 1) := by
    rw [hvolGe_eq]
    unfold volPminusB
    have hsplit : (∑ x ∈ cfg.X, if !s'.inR x && decide (x ∉ cfg.B) then cfg.degX x else 0) =
        (∑ x ∈ cfg.X, if !s.inR x && decide (x ∉ cfg.B) then cfg.degX x else 0) +
        (∑ x ∈ A, cfg.degX x) := by
      have hsumA : ∑ x ∈ A, cfg.degX x =
          ∑ x ∈ cfg.X, if x ∈ A then cfg.degX x else 0 := by
        rw [← Finset.sum_filter]
        congr 1
        ext x
        simp only [Finset.mem_filter, A]
        tauto
      rw [hsumA, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hxX
      rw [hs'_inR x]
      by_cases hxA : x ∈ A
      · have hxR := hAinR x hxA
        have hxB : x ∉ cfg.B := fun hb => by have := hinv.not_inR_B x hb; simp [hxR] at this
        simp [hxA, hxR, hxB]
      · simp [hxA]
    exact hsplit
  have hcut_diff : (cutPR cfg s' : ℤ) - (cutPR cfg s : ℤ) =
      (crossRtoA s.inR A cfg.edges : ℤ) - (crossCutList s.inR A cfg.edges : ℤ) := by
    simpa [cutPR] using cut_change_removeSet s.inR s'.inR A hAinR hs'_inR cfg.edges
  have hcontrib := sum_edgeContrib_eq s.inR A hAinR s.flow cfg.C_cap 0 cfg.edges
  have hsum_A_ge : (volGeLevel cfg s.inR hTmp (lvl + 1) : ℤ) ≤
      (cfg.C_cap : ℤ) * (crossCutList s.inR A cfg.edges : ℤ) -
        flowOutAux s.inR A s.flow 0 cfg.edges := by
    rw [← hcontrib, hvolGe_eq]
    push_cast
    apply Finset.sum_le_sum
    intro x hxA
    have hxR := hAinR x hxA
    have hfb := hinv.flow_balance x hxR
    simp only [PruneCfg.incEdges] at hfb
    rw [← hfb]
    have hx_abs : s.abs x = cfg.degX x := by
      by_cases hxu : x = u
      · subst hxu; exact habs
      · have hxge : lvl + 1 ≤ hTmp x := by
          simp only [A, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hxA
          exact hxA.2.2
        have hxp : 0 < s.h x := by
          have : hTmp x = s.h x := by simp [hTmp, hxu]
          omega
        exact hinv.h_pos_abs x hxR hxp
    omega
  have huA : u ∈ A := by
    simp only [A, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨huX, huR, ?_⟩
    simp [hTmp]; omega
  have hflowOut_bd := flowOut_freeze_bound cfg s u lvl hTmp rfl A rfl ⟨hlvl1, hlvlH⟩
    huA huH hcurEnd habs hinv.flow_cap hinv.h_edge hinv.cur_no_adm 0 cfg.edges
    (fun j a b hj hab => by simpa using edges_getElem?_mem_incEdges cfg hj hab)
  have hvolAt_ge : (∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
      (cfg.incEdges y).length else 0) ≤ volAtLevel cfg s.inR hTmp lvl := by
    unfold volAtLevel
    apply Finset.sum_le_sum
    intro y _
    split_ifs
    · exact incEdges_length_le_degX cfg y
    · exact le_rfl
  have hvolAt_z : ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
        (cfg.incEdges y).length else 0 : ℕ) : ℤ) ≤ (volAtLevel cfg s.inR hTmp lvl : ℤ) := by
    exact_mod_cast hvolAt_ge
  have hpick_z : 4 * (cfg.C_cap : ℤ) * (volAtLevel cfg s.inR hTmp lvl : ℤ) ≤
      (volGeLevel cfg s.inR hTmp (lvl + 1) : ℤ) := by
    have h0 : ((4 * cfg.C_cap * volAtLevel cfg s.inR hTmp lvl : ℕ) : ℤ) ≤
        (volGeLevel cfg s.inR hTmp (lvl + 1) : ℤ) := by exact_mod_cast hvol_pick
    push_cast at h0
    simpa [mul_assoc] using h0
  have hbd1 : (cfg.C_cap : ℤ) * (crossRtoA s.inR A cfg.edges : ℤ) -
      flowOutAux s.inR A s.flow 0 cfg.edges ≤
      2 * (cfg.C_cap : ℤ) * (volAtLevel cfg s.inR hTmp lvl : ℤ) := by
    have h0 := hflowOut_bd
    change _ ≤ 2 * (cfg.C_cap : ℤ) *
      ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
        (cfg.incEdges y).length else 0 : ℕ) : ℤ) at h0
    have hmul : 2 * (cfg.C_cap : ℤ) *
        ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
          (cfg.incEdges y).length else 0 : ℕ) : ℤ) ≤
        2 * (cfg.C_cap : ℤ) * (volAtLevel cfg s.inR hTmp lvl : ℤ) :=
      mul_le_mul_of_nonneg_left hvolAt_z (by omega)
    omega
  have hC_cut : (cfg.C_cap : ℤ) * (cutPR cfg s' : ℤ) - (cfg.C_cap : ℤ) * (cutPR cfg s : ℤ) =
      ((cfg.C_cap : ℤ) * (crossRtoA s.inR A cfg.edges : ℤ) - flowOutAux s.inR A s.flow 0 cfg.edges) -
      ((cfg.C_cap : ℤ) * (crossCutList s.inR A cfg.edges : ℤ) - flowOutAux s.inR A s.flow 0 cfg.edges) := by
    calc (cfg.C_cap : ℤ) * (cutPR cfg s' : ℤ) - (cfg.C_cap : ℤ) * (cutPR cfg s : ℤ)
        = (cfg.C_cap : ℤ) * ((cutPR cfg s' : ℤ) - (cutPR cfg s : ℤ)) := by ring
      _ = (cfg.C_cap : ℤ) * ((crossRtoA s.inR A cfg.edges : ℤ) -
            (crossCutList s.inR A cfg.edges : ℤ)) := by rw [hcut_diff]
      _ = _ := by ring
  have hvolP_z : (volPminusB cfg s' : ℤ) =
      (volPminusB cfg s : ℤ) + (volGeLevel cfg s.inR hTmp (lvl + 1) : ℤ) := by
    exact_mod_cast hvolP_eq
  have h2v : 4 * (cfg.C_cap : ℤ) * (volAtLevel cfg s.inR hTmp lvl : ℤ) =
      2 * (2 * (cfg.C_cap : ℤ) * (volAtLevel cfg s.inR hTmp lvl : ℤ)) := by ring
  have h2a : 2 * (cfg.C_cap : ℤ) * (cutPR cfg s' : ℤ) =
      2 * ((cfg.C_cap : ℤ) * (cutPR cfg s' : ℤ)) := by ring
  have h2b : 2 * (cfg.C_cap : ℤ) * (cutPR cfg s : ℤ) =
      2 * ((cfg.C_cap : ℤ) * (cutPR cfg s : ℤ)) := by ring
  have hcut_le_Z : (volPminusB cfg s' : ℤ) + 2 * (cfg.C_cap : ℤ) * (cutPR cfg s' : ℤ) ≤
      (volPminusB cfg s : ℤ) + 2 * (cfg.C_cap : ℤ) * (cutPR cfg s : ℤ) := by
    omega
  have hvc : volPminusB cfg s' + 2 * cfg.C_cap * cutPR cfg s' ≤
      volPminusB cfg s + 2 * cfg.C_cap * cutPR cfg s := by exact_mod_cast hcut_le_Z
  exact ⟨hs'_inv, hsteps_pot, hpot_lt, hvc⟩


end

end MinCostFlow.Expander
