module

public import MinCostFlow.Expander.ExpanderPruningStepFlow

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Expander Pruning Step Helpers (Relabel & Freeze Cut/Flow Helpers)
-/

namespace MinCostFlow.Expander

open Classical

public section

/-! ### Micro-step 6: Relabel (`relabelStep`) -/

/-- Increases `s.h u` by `1` and resets `s.cur u` to `0` when `s.h u + 1 < cfg.H`. -/
@[expose] def relabelStep (u : ℕ) (s : PruneState) : PruneState :=
  { s with
    h := fun x => if x = u then s.h u + 1 else s.h x
    cur := fun x => if x = u then 0 else s.cur x
    steps := s.steps + 1 }

lemma relabelStep_inv_pot {cfg : PruneCfg} (hcfg : cfg.Valid) {s : PruneState}
    (hinv : PruningInv cfg s) {u : ℕ} (huR : s.inR u = true) (hexPos : 0 < s.ex u)
    (habs : s.abs u = cfg.degX u) (hcurEnd : s.cur u = (cfg.incEdges u).length)
    (hhLt : s.h u + 1 < cfg.H) :
    let s' := relabelStep u s
    PruningInv cfg s' ∧
    s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
    pot cfg s' < pot cfg s ∧
    volPminusB cfg s' = volPminusB cfg s ∧
    cutPR cfg s' = cutPR cfg s := by
  have hH3 := cfg.valid_three_le_H hcfg
  dsimp only [relabelStep]
  set s' : PruneState :=
    { s with
      h := fun x => if x = u then s.h u + 1 else s.h x
      cur := fun x => if x = u then 0 else s.cur x
      steps := s.steps + 1 }
  have hs'_inv : PruningInv cfg s' :=
    { inR_sub := hinv.inR_sub
      not_inR_B := hinv.not_inR_B
      h_lt_H := by
        intro x hxR
        by_cases hxu : x = u
        · subst hxu; simpa [s'] using hhLt
        · simpa [s', hxu] using hinv.h_lt_H x hxR
      cur_le := by
        intro x hxR
        by_cases hxu : x = u
        · subst hxu; simp [s']
        · simpa [s', hxu] using hinv.cur_le x hxR
      abs_le := hinv.abs_le
      h_pos_abs := by
        intro x hxR hxpos
        by_cases hxu : x = u
        · subst hxu; exact habs
        · exact hinv.h_pos_abs x hxR (by simpa [s', hxu] using hxpos)
      flow_cap := hinv.flow_cap
      h_edge := by
        intro x hxR p hp hpR hflt
        by_cases hxu : x = u
        · subst hxu
          have hpne : p.2.2 ≠ x := incEdgesAux_ne_self hp
          rcases list_mem_exists_getD (0, false, 0) (cfg.incEdges x) hp with ⟨j, hj, rfl⟩
          have hjc : j < s.cur x := by rw [hcurEnd]; exact hj
          have hadm := hinv.cur_no_adm x hxR habs j hjc
          dsimp only at hadm
          rcases hadm with hf | hsat | hle
          · rw [hpR] at hf; exact False.elim (Bool.false_ne_true hf.symm)
          · exact False.elim (lt_irrefl _ (hsat ▸ hflt))
          · dsimp only [s']
            simp only [↓reduceIte, hpne]
            exact Nat.succ_le_succ hle
        · have hold := hinv.h_edge x hxR p hp hpR hflt
          dsimp only [s']
          by_cases hpu : p.2.2 = u
          · simp only [hxu, hpu, ↓reduceIte]; rw [hpu] at hold; omega
          · simp only [hxu, hpu, ↓reduceIte]; exact hold
      cur_no_adm := by
        intro x hxR hxdeg j hj
        by_cases hxu : x = u
        · subst hxu; simp [s'] at hj
        · have hold := hinv.cur_no_adm x hxR hxdeg j (by simpa [s', hxu] using hj)
          dsimp only at hold ⊢
          dsimp only [s']
          by_cases hpu : ((cfg.incEdges x).getD j (0, false, 0)).2.2 = u
          · rcases hold with h1 | h2 | h3
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
            · rw [hpu] at h3; right; right; simp only [hxu, hpu, ↓reduceIte]; omega
          · rcases hold with h1 | h2 | h3
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
            · right; right; simp only [hxu, hpu, ↓reduceIte]; exact h3
      cur_zero_of_abs_lt := by
        intro x hxR hxlt
        by_cases hxu : x = u
        · subst hxu; simp [s']
        · simpa [s', hxu] using hinv.cur_zero_of_abs_lt x hxR hxlt
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
        have hxu : x ≠ u := by rintro rfl; omega
        simpa [s', hxu] using hne }
  have huX : u ∈ cfg.X := hinv.inR_sub u huR
  have hlenPos : 0 < (cfg.incEdges u).length := by
    by_contra h0
    have := (hinv.no_ex_isolated u (by omega)).1
    omega
  have hu_act : u ∈ s.active := hinv.active_cov u huR hexPos
  have hrel_drop : relabelCurRem cfg s' + 2 = relabelCurRem cfg s := by
    unfold relabelCurRem
    rw [← Finset.add_sum_erase _ _ huX, ← Finset.add_sum_erase cfg.X _ huX]
    have hrest : ∑ x ∈ cfg.X.erase u,
          (if s'.inR x && decide (0 < (cfg.incEdges x).length) then
            (cfg.H - s'.h x) * (2 * (cfg.incEdges x).length + 2) +
            (2 * (cfg.incEdges x).length + 1 - 2 * s'.cur x)
          else 0) =
        ∑ x ∈ cfg.X.erase u,
          (if s.inR x && decide (0 < (cfg.incEdges x).length) then
            (cfg.H - s.h x) * (2 * (cfg.incEdges x).length + 2) +
            (2 * (cfg.incEdges x).length + 1 - 2 * s.cur x)
          else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hne : x ≠ u := (Finset.mem_erase.mp hx).1
      simp [s', hne]
    set len := (cfg.incEdges u).length
    have hh_le1 : s.h u + 1 ≤ cfg.H := le_of_lt hhLt
    have hmul : (cfg.H - (s.h u + 1)) * (2 * len + 2) + (2 * len + 2) =
        (cfg.H - s.h u) * (2 * len + 2) := by
      have : cfg.H - s.h u = (cfg.H - (s.h u + 1)) + 1 := by omega
      rw [this]; ring
    have ht1 : (if s'.inR u && decide (0 < len) then
          (cfg.H - s'.h u) * (2 * len + 2) + (2 * len + 1 - 2 * s'.cur u)
        else 0) = (cfg.H - (s.h u + 1)) * (2 * len + 2) + (2 * len + 1) := by
      simp [s', huR, hlenPos]
    have ht2 : (if s.inR u && decide (0 < len) then
          (cfg.H - s.h u) * (2 * len + 2) + (2 * len + 1 - 2 * s.cur u)
        else 0) = (cfg.H - s.h u) * (2 * len + 2) + 1 := by
      simp only [huR, hlenPos, decide_true, Bool.and_self, ↓reduceIte, hcurEnd]
      omega
    rw [ht1, ht2, hrest]
    omega
  have hphi_eq : phiActive s' = phiActive s + 1 := by
    unfold phiActive
    suffices h : ∀ (M : List ℕ), M.Nodup → u ∈ M →
        (M.map fun x => if s'.inR x then s'.h x + 2 else 2).sum =
          (M.map fun x => if s.inR x then s.h x + 2 else 2).sum + 1 by
      exact h s.active hinv.active_nodup hu_act
    intro M hnd hm
    induction M with
    | nil => simp at hm
    | cons x xs ih =>
      simp only [List.nodup_cons] at hnd
      rcases List.mem_cons.mp hm with rfl | hmem
      · have hrest : xs.map (fun y => if s'.inR y then s'.h y + 2 else 2) =
            xs.map (fun y => if s.inR y then s.h y + 2 else 2) := by
          apply List.map_congr_left
          intro y hy
          have hne : y ≠ u := fun heq => hnd.1 (heq ▸ hy)
          dsimp only [s']
          simp only [hne, ↓reduceIte]
        simp only [List.map_cons, List.sum_cons, hrest]
        dsimp only [s']
        simp only [huR, ↓reduceIte]
        omega
      · have hne : x ≠ u := fun heq => hnd.1 (heq ▸ hmem)
        have ih' := ih hnd.2 hmem
        simp only [List.map_cons, List.sum_cons]
        have hx_eq : (if s'.inR x then s'.h x + 2 else 2) =
            (if s.inR x then s.h x + 2 else 2) := by simp [s', hne]
        omega
  have hpot_drop : pot cfg s' + (2 * cfg.H + 6) = pot cfg s := by
    unfold pot
    have hv : volR cfg s' = volR cfg s := rfl
    have ha : sumAbsRem cfg s' = sumAbsRem cfg s := rfl
    have hq : s'.peelQ = s.peelQ := rfl
    rw [hv, ha, hq, ← hrel_drop, hphi_eq]
    ring
  exact ⟨hs'_inv, by omega, by omega, rfl, rfl⟩

/-! ### Micro-step 7: Level-sweep freeze (`freezeStep`) -/

/-- Level-sweep freeze at `u` when `s.h u = cfg.H - 1` and `s.cur u = (cfg.incEdges u).length`:
raises `h u` to `H`, picks `lvl ∈ {1, ..., H - 1}` with `4 * C_cap * volAtLevel lvl ≤ volGeLevel (lvl + 1)`,
and removes `A = {x ∈ R | hTmp x ≥ lvl + 1}` (starting with `u`) via `removeOneFromR`. -/
@[expose] noncomputable def freezeStep (cfg : PruneCfg) (u : ℕ) (s : PruneState) : PruneState :=
  let hTmp : ℕ → ℕ := fun x => if x = u then cfg.H else s.h x
  let lvl := pickLevel cfg s.inR hTmp
  let AList := cfg.X.toList.filter fun x => s.inR x && decide (lvl + 1 ≤ hTmp x)
  let remList := u :: AList.erase u
  let sMid : PruneState := { s with h := hTmp, cur := fun x => if x = u then 0 else s.cur x }
  let s1 := remList.foldl (fun st a => removeOneFromR cfg a st) sMid
  let volEA := (remList.map fun a => (cfg.incEdges a).length).sum
  { s1 with steps := s.steps + cfg.H + volEA }

@[expose] def crossRtoA (inR : ℕ → Bool) (A : Finset ℕ) (L : List (ℕ × ℕ)) : ℕ :=
  (L.filter fun e =>
    decide ((e.1 ∈ A ∧ inR e.2 ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ inR e.1 ∧ e.1 ∉ A))).length

lemma cut_change_removeSet (inR inR' : ℕ → Bool) (A : Finset ℕ)
    (hAinR : ∀ x ∈ A, inR x = true) (hinR' : ∀ x, inR' x = (inR x && !(x ∈ A))) :
    ∀ (L : List (ℕ × ℕ)),
      ((L.filter fun e => decide (inR' e.1 ≠ inR' e.2)).length : ℤ) -
        ((L.filter fun e => decide (inR e.1 ≠ inR e.2)).length : ℤ) =
        (crossRtoA inR A L : ℤ) - (crossCutList inR A L : ℤ)
  | [] => by simp [crossRtoA, crossCutList]
  | (a, b) :: rest => by
    have ih := cut_change_removeSet inR inR' A hAinR hinR' rest
    simp only [crossRtoA, crossCutList] at ih ⊢
    rw [filter_cons_length, filter_cons_length, filter_cons_length, filter_cons_length]
    push_cast
    by_cases haA : a ∈ A <;> by_cases hbA : b ∈ A
    · have haR := hAinR a haA; have hbR := hAinR b hbA
      have ha' : inR' a = false := by simp [hinR' a, haA]
      have hb' : inR' b = false := by simp [hinR' b, hbA]
      conv_lhs => arg 1; arg 1; simp [ha', hb']
      conv_lhs => arg 2; arg 1; simp [haR, hbR]
      conv_rhs => arg 1; arg 1; simp [haA, hbA]
      conv_rhs => arg 2; arg 1; simp [haR, hbR]
      linarith
    · have haR := hAinR a haA
      have ha' : inR' a = false := by simp [hinR' a, haA]
      have hb' : inR' b = inR b := by simp [hinR' b, hbA]
      by_cases hbR : inR b = true
      · conv_lhs => arg 1; arg 1; simp [ha', hb', hbR]
        conv_lhs => arg 2; arg 1; simp [haR, hbR]
        conv_rhs => arg 1; arg 1; simp [haA, hbR, hbA]
        conv_rhs => arg 2; arg 1; simp [hbR, hbA]
        linarith
      · have hbF : inR b = false := Bool.eq_false_iff.mpr hbR
        conv_lhs => arg 1; arg 1; simp [ha', hb', hbF]
        conv_lhs => arg 2; arg 1; simp [haR, hbF]
        conv_rhs => arg 1; arg 1; simp [hbF, hbA]
        conv_rhs => arg 2; arg 1; simp [haA, hbF]
        linarith
    · have hbR := hAinR b hbA
      have hb' : inR' b = false := by simp [hinR' b, hbA]
      have ha' : inR' a = inR a := by simp [hinR' a, haA]
      by_cases haR : inR a = true
      · conv_lhs => arg 1; arg 1; simp [ha', hb', haR]
        conv_lhs => arg 2; arg 1; simp [haR, hbR]
        conv_rhs => arg 1; arg 1; simp [hbA, haR, haA]
        conv_rhs => arg 2; arg 1; simp [haA, haR]
        linarith
      · have haF : inR a = false := Bool.eq_false_iff.mpr haR
        conv_lhs => arg 1; arg 1; simp [ha', hb', haF]
        conv_lhs => arg 2; arg 1; simp [haF, hbR]
        conv_rhs => arg 1; arg 1; simp [haF, haA]
        conv_rhs => arg 2; arg 1; simp [hbA, haF]
        linarith
    · have ha' : inR' a = inR a := by simp [hinR' a, haA]
      have hb' : inR' b = inR b := by simp [hinR' b, hbA]
      have h1 : decide (inR' a ≠ inR' b) = decide (inR a ≠ inR b) := by simp [ha', hb']
      rw [h1]
      conv_rhs => arg 1; arg 1; simp [haA, hbA]
      conv_rhs => arg 2; arg 1; simp [haA, hbA]
      linarith

lemma flowOut_freeze_bound (cfg : PruneCfg) (s : PruneState) (u lvl : ℕ)
    (hTmp : ℕ → ℕ) (hhTmp : hTmp = fun x => if x = u then cfg.H else s.h x)
    (A : Finset ℕ) (hAeq : A = cfg.X.filter fun x => s.inR x && decide (lvl + 1 ≤ hTmp x))
    (hlvl : 1 ≤ lvl ∧ lvl < cfg.H)
    (huA : u ∈ A) (huH : s.h u + 1 = cfg.H) (huCur : s.cur u = (cfg.incEdges u).length)
    (huAbs : s.abs u = cfg.degX u)
    (hflow_cap : ∀ idx < cfg.edges.length, -(cfg.C_cap : ℤ) ≤ s.flow idx ∧ s.flow idx ≤ (cfg.C_cap : ℤ))
    (hh_edge : ∀ x, s.inR x = true → ∀ p ∈ cfg.incEdges x, s.inR p.2.2 = true →
      flowDir s.flow p.1 p.2.1 < (cfg.C_cap : ℤ) → s.h x ≤ s.h p.2.2 + 1)
    (hcur_no_adm : ∀ x, s.inR x = true → s.abs x = cfg.degX x →
      ∀ j < s.cur x,
        let p := (cfg.incEdges x).getD j (0, false, 0)
        s.inR p.2.2 = false ∨ flowDir s.flow p.1 p.2.1 = (cfg.C_cap : ℤ) ∨ s.h x ≤ s.h p.2.2) :
    ∀ (k : ℕ) (L : List (ℕ × ℕ)),
      (∀ j a b, L[j]? = some (a, b) → a ≠ b →
        (k + j, false, b) ∈ cfg.incEdges a ∧
        (k + j, true, a) ∈ cfg.incEdges b ∧
        k + j < cfg.edges.length) →
      (cfg.C_cap : ℤ) * (crossRtoA s.inR A L : ℤ) - flowOutAux s.inR A s.flow k L ≤
        2 * (cfg.C_cap : ℤ) *
          ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then (incEdgesAux y k L).length else 0 : ℕ) : ℤ)
  | _, [], _ => by simp [crossRtoA, flowOutAux, incEdgesAux]
  | k, (a, b) :: rest, hL => by
    have hrest : ∀ j x y, rest[j]? = some (x, y) → x ≠ y →
        (k + 1 + j, false, y) ∈ cfg.incEdges x ∧
        (k + 1 + j, true, x) ∈ cfg.incEdges y ∧
        k + 1 + j < cfg.edges.length := by
      intro j x y hj hxy
      have hk : k + 1 + j = k + (j + 1) := by omega
      rw [hk]
      exact hL (j + 1) x y (by simpa using hj) hxy
    have ih := flowOut_freeze_bound cfg s u lvl hTmp hhTmp A hAeq hlvl huA huH huCur huAbs
      hflow_cap hh_edge hcur_no_adm (k + 1) rest hrest
    have hsat_helper : ∀ (x y : ℕ) (dir : Bool),
        x ∈ A → s.inR y = true → y ∉ A →
        (k, dir, y) ∈ cfg.incEdges x → k < cfg.edges.length →
        hTmp y < lvl →
        flowDir s.flow k dir = (cfg.C_cap : ℤ) := by
      intro x y dir hxA hyR hyNotA hpMem hklt hyLt
      have hyu : y ≠ u := fun heq => hyNotA (heq ▸ huA)
      have hy_h : s.h y = hTmp y := by simp [hhTmp, hyu]
      rw [hAeq, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hxA
      obtain ⟨hxX, hxR, hxH⟩ := hxA
      have hcap := hflow_cap k hklt
      have hleC : flowDir s.flow k dir ≤ (cfg.C_cap : ℤ) := by
        cases dir <;> simp [flowDir] <;> omega
      by_cases hxu : x = u
      · subst hxu
        rcases list_mem_exists_getD (0, false, 0) (cfg.incEdges x) hpMem with ⟨j, hj, hget⟩
        have hjc : j < s.cur x := by rw [huCur]; exact hj
        have hadm := hcur_no_adm x hxR huAbs j hjc
        rw [hget] at hadm
        dsimp only at hadm
        rcases hadm with hf | hsat | hle
        · simp [hyR] at hf
        · exact hsat
        · exfalso; omega
      · have hx_h : s.h x = hTmp x := by simp [hhTmp, hxu]
        by_contra hneC
        have hflt : flowDir s.flow k dir < (cfg.C_cap : ℤ) := by omega
        have hle := hh_edge x hxR (k, dir, y) hpMem hyR hflt
        dsimp only at hle
        omega
    have hpt : ∀ y, (incEdgesAux y k ((a, b) :: rest)).length =
        (incEdgesAux y (k + 1) rest).length +
        (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) := by
      intro y
      conv_lhs => rw [incEdgesAux]
      by_cases h1 : a = b
      · simp [h1]
      · by_cases h2 : a = y
        · subst h2; simp [h1]
        · by_cases h3 : b = y
          · subst h3; simp [h1]
          · simp [h1, h2, h3]
    have hsum_step : (∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
          (incEdgesAux y k ((a, b) :: rest)).length else 0) =
        (∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
          (incEdgesAux y (k + 1) rest).length else 0) +
        (∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
          (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : (s.inR y && decide (hTmp y = lvl)) = true
      · simp only [hy, ↓reduceIte]; exact hpt y
      · simp only [hy, Bool.false_eq_true, ↓reduceIte, add_zero]
    have hsum_z : ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
          (incEdgesAux y k ((a, b) :: rest)).length else 0 : ℕ) : ℤ) =
        ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
          (incEdgesAux y (k + 1) rest).length else 0 : ℕ) : ℤ) +
        ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
          (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) else 0 : ℕ) : ℤ) := by
      exact_mod_cast hsum_step
    rw [hsum_z, mul_add]
    by_cases hab : a = b
    · subst hab
      have hcross_eq : crossRtoA s.inR A ((a, a) :: rest) = crossRtoA s.inR A rest := by
        unfold crossRtoA
        rw [filter_cons_length]
        have hfalse : ¬ ((a ∈ A ∧ s.inR a = true ∧ a ∉ A) ∨ (a ∈ A ∧ s.inR a = true ∧ a ∉ A)) := by
          tauto
        rw [ite_eq_right (by simpa using hfalse), zero_add]
      have hflow_eq : flowOutAux s.inR A s.flow k ((a, a) :: rest) =
          flowOutAux s.inR A s.flow (k + 1) rest := by
        conv_lhs => rw [flowOutAux]
        simp
      have hsum_zero : ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
            (if a = a then 0 else if a = y then 1 else if a = y then 1 else 0) else 0 : ℕ) : ℤ) = 0 := by
        simp
      rw [hcross_eq, hflow_eq, hsum_zero, mul_zero, add_zero]
      exact ih
    · obtain ⟨hinc_a, hinc_b, hklt⟩ := hL 0 a b (by simp) hab
      have hcap := hflow_cap k hklt
      have hadd_nonneg : (0 : ℤ) ≤
          ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
            (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) else 0 : ℕ) : ℤ) := by
        exact_mod_cast Nat.zero_le _
      by_cases h1 : a ∈ A ∧ s.inR b ∧ b ∉ A
      · have haA := h1.1; have hbR := h1.2.1; have hbNotA := h1.2.2
        have hbX : b ∈ cfg.X := (incEdges_mem_sub hinc_a).2
        have hcross_eq : crossRtoA s.inR A ((a, b) :: rest) = 1 + crossRtoA s.inR A rest := by
          unfold crossRtoA; rw [filter_cons_length, ite_eq_left (decide_eq_true (Or.inl h1))]
        have hflow_eq : flowOutAux s.inR A s.flow k ((a, b) :: rest) =
            s.flow k + flowOutAux s.inR A s.flow (k + 1) rest := by
          conv_lhs => rw [flowOutAux]
          rw [ite_eq_right hab, ite_eq_left h1]
        rw [hcross_eq, hflow_eq, Nat.cast_add, Nat.cast_one]
        have hble : hTmp b ≤ lvl := by
          by_contra hgt
          apply hbNotA
          rw [hAeq, Finset.mem_filter]
          refine ⟨hbX, ?_⟩
          simp only [hbR, Bool.true_and, decide_eq_true_eq]
          omega
        rcases lt_or_eq_of_le hble with hbLt | hbEq
        · have hfl : s.flow k = (cfg.C_cap : ℤ) :=
            hsat_helper a b false haA hbR hbNotA hinc_a hklt hbLt
          have hnonneg : (0 : ℤ) ≤ 2 * (cfg.C_cap : ℤ) *
              ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
                (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) else 0 : ℕ) : ℤ) :=
            mul_nonneg (by omega) hadd_nonneg
          linarith
        · have hb_ge1 : (1 : ℕ) ≤ ∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
              (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) else 0 := by
            calc 1 = if s.inR b && decide (hTmp b = lvl) then
                    (if a = b then 0 else if a = b then 1 else if b = b then 1 else 0) else 0 := by
                    simp [hbR, hbEq, hab]
              _ ≤ _ := Finset.single_le_sum
                  (f := fun y => if s.inR y && decide (hTmp y = lvl) then
                    (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) else 0)
                  (fun _ _ => Nat.zero_le _) hbX
          have hb_ge1_z : (1 : ℤ) ≤
              ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
                (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) else 0 : ℕ) : ℤ) := by
            exact_mod_cast hb_ge1
          have hhead_ge : 2 * (cfg.C_cap : ℤ) ≤ 2 * (cfg.C_cap : ℤ) *
              ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
                (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) else 0 : ℕ) : ℤ) := by
            nlinarith
          linarith
      · by_cases h2 : b ∈ A ∧ s.inR a ∧ a ∉ A
        · have hbA := h2.1; have haR := h2.2.1; have haNotA := h2.2.2
          have haX : a ∈ cfg.X := (incEdges_mem_sub hinc_b).2
          have hcross_eq : crossRtoA s.inR A ((a, b) :: rest) = 1 + crossRtoA s.inR A rest := by
            unfold crossRtoA; rw [filter_cons_length, ite_eq_left (decide_eq_true (Or.inr h2))]
          have hflow_eq : flowOutAux s.inR A s.flow k ((a, b) :: rest) =
              -(s.flow k) + flowOutAux s.inR A s.flow (k + 1) rest := by
            conv_lhs => rw [flowOutAux]
            rw [ite_eq_right hab, ite_eq_right h1, ite_eq_left h2]
          rw [hcross_eq, hflow_eq, Nat.cast_add, Nat.cast_one]
          have hale : hTmp a ≤ lvl := by
            by_contra hgt
            apply haNotA
            rw [hAeq, Finset.mem_filter]
            refine ⟨haX, ?_⟩
            simp only [haR, Bool.true_and, decide_eq_true_eq]
            omega
          rcases lt_or_eq_of_le hale with haLt | haEq
          · have hfl : flowDir s.flow k true = (cfg.C_cap : ℤ) :=
              hsat_helper b a true hbA haR haNotA hinc_b hklt haLt
            simp only [flowDir, ↓reduceIte] at hfl
            have hnonneg : (0 : ℤ) ≤ 2 * (cfg.C_cap : ℤ) *
                ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
                  (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) else 0 : ℕ) : ℤ) :=
              mul_nonneg (by omega) hadd_nonneg
            linarith
          · have ha_ge1 : (1 : ℕ) ≤ ∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
                (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) else 0 := by
              calc 1 = if s.inR a && decide (hTmp a = lvl) then
                      (if a = b then 0 else if a = a then 1 else if b = a then 1 else 0) else 0 := by
                      simp [haR, haEq, hab]
                _ ≤ _ := Finset.single_le_sum
                    (f := fun y => if s.inR y && decide (hTmp y = lvl) then
                      (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) else 0)
                    (fun _ _ => Nat.zero_le _) haX
            have ha_ge1_z : (1 : ℤ) ≤
                ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
                  (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) else 0 : ℕ) : ℤ) := by
              exact_mod_cast ha_ge1
            have hhead_ge : 2 * (cfg.C_cap : ℤ) ≤ 2 * (cfg.C_cap : ℤ) *
                ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
                  (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) else 0 : ℕ) : ℤ) := by
              nlinarith
            linarith
        · have hcross_eq : crossRtoA s.inR A ((a, b) :: rest) = crossRtoA s.inR A rest := by
            unfold crossRtoA
            have hfalse : ¬ ((a ∈ A ∧ s.inR b = true ∧ b ∉ A) ∨ (b ∈ A ∧ s.inR a = true ∧ a ∉ A)) := by tauto
            rw [filter_cons_length, ite_eq_right (by simpa using hfalse), zero_add]
          have hflow_eq : flowOutAux s.inR A s.flow k ((a, b) :: rest) =
              flowOutAux s.inR A s.flow (k + 1) rest := by
            conv_lhs => rw [flowOutAux]
            rw [ite_eq_right hab, ite_eq_right h1, ite_eq_right h2]
          rw [hcross_eq, hflow_eq]
          have hnonneg : (0 : ℤ) ≤ 2 * (cfg.C_cap : ℤ) *
              ((∑ y ∈ cfg.X, if s.inR y && decide (hTmp y = lvl) then
                (if a = b then 0 else if a = y then 1 else if b = y then 1 else 0) else 0 : ℕ) : ℤ) :=
            mul_nonneg (by omega) hadd_nonneg
          linarith


end

end MinCostFlow.Expander
