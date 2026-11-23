module

public import MinCostFlow.Expander.ExpanderPruningStepBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Expander Pruning Step Helpers (Absorb, AdvanceCur, PushFlow)
-/

namespace MinCostFlow.Expander

open Classical

public section

/-! ### Micro-step 3: Sink absorption (`absorbStep`) -/

/-- Absorbs `min (s.ex u) (cfg.degX u - s.abs u)` units of excess at `u`. -/
@[expose] def absorbStep (cfg : PruneCfg) (u : ℕ) (s : PruneState) : PruneState :=
  let give := min (s.ex u) (cfg.degX u - s.abs u)
  { s with
    ex := fun x => if x = u then s.ex u - give else s.ex x
    abs := fun x => if x = u then s.abs u + give else s.abs x
    steps := s.steps + 1 }

lemma absorbStep_inv_pot {cfg : PruneCfg} {s : PruneState} {u : ℕ}
    (hinv : PruningInv cfg s) (huR : s.inR u = true) (hexPos : 0 < s.ex u)
    (habsLt : s.abs u < cfg.degX u) :
    let s' := absorbStep cfg u s
    PruningInv cfg s' ∧
    s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
    pot cfg s' < pot cfg s ∧
    volPminusB cfg s' = volPminusB cfg s ∧
    cutPR cfg s' = cutPR cfg s := by
  dsimp only [absorbStep]
  set give := min (s.ex u) (cfg.degX u - s.abs u)
  have hgive_pos : 1 ≤ give := by omega
  have hgive_ex : give ≤ s.ex u := min_le_left _ _
  have hgive_abs : give ≤ cfg.degX u - s.abs u := min_le_right _ _
  have hsu_h0 : s.h u = 0 := by
    by_contra hne
    exact absurd (hinv.h_pos_abs u huR (by omega)) (by omega)
  have hsu_cur0 : s.cur u = 0 := hinv.cur_zero_of_abs_lt u huR habsLt
  set s' : PruneState :=
    { s with
      ex := fun x => if x = u then s.ex u - give else s.ex x
      abs := fun x => if x = u then s.abs u + give else s.abs x
      steps := s.steps + 1 }
  have hs'_inv : PruningInv cfg s' :=
    { inR_sub := hinv.inR_sub
      not_inR_B := hinv.not_inR_B
      h_lt_H := hinv.h_lt_H
      cur_le := hinv.cur_le
      abs_le := by
        intro x hxR
        by_cases hxu : x = u
        · subst hxu; simp [s']; omega
        · simp [s', hxu, hinv.abs_le x hxR]
      h_pos_abs := by
        intro x hxR hxpos
        by_cases hxu : x = u
        · subst hxu; change 0 < s.h x at hxpos; omega
        · simp [s', hxu, hinv.h_pos_abs x hxR hxpos]
      flow_cap := hinv.flow_cap
      h_edge := hinv.h_edge
      cur_no_adm := by
        intro x hxR hxdeg j hj
        by_cases hxu : x = u
        · subst hxu; change j < s.cur x at hj; omega
        · exact hinv.cur_no_adm x hxR (by simpa [s', hxu] using hxdeg) j hj
      cur_zero_of_abs_lt := by
        intro x hxR hxlt
        by_cases hxu : x = u
        · subst hxu; exact hsu_cur0
        · exact hinv.cur_zero_of_abs_lt x hxR (by simpa [s', hxu] using hxlt)
      flow_balance := by
        intro x hxR
        by_cases hxu : x = u
        · subst hxu
          have hfb := hinv.flow_balance x hxR
          have hcast : ((s.ex x - give : ℕ) : ℤ) + ((s.abs x + give : ℕ) : ℤ) =
              (s.ex x : ℤ) + (s.abs x : ℤ) := by omega
          dsimp only [s']
          simp only [↓reduceIte]
          rw [hcast]
          exact hfb
        · simpa [s', hxu] using hinv.flow_balance x hxR
      degR_eq := hinv.degR_eq
      degR_peel := hinv.degR_peel
      active_cov := by
        intro x hxR hxpos
        by_cases hxu : x = u
        · subst hxu; exact hinv.active_cov x huR hexPos
        · exact hinv.active_cov x hxR (by simpa [s', hxu] using hxpos)
      active_mem_inActive := hinv.active_mem_inActive
      active_nodup := hinv.active_nodup
      active_sub := hinv.active_sub
      no_ex_isolated := by
        intro x hx0
        have hne := hinv.no_ex_isolated x hx0
        have hxu : x ≠ u := by rintro rfl; omega
        simpa [s', hxu] using hne }
  have huX : u ∈ cfg.X := hinv.inR_sub u huR
  have habs_drop : sumAbsRem cfg s' + give = sumAbsRem cfg s := by
    unfold sumAbsRem
    rw [← Finset.add_sum_erase _ _ huX, ← Finset.add_sum_erase cfg.X _ huX]
    have hterm1 : (if s'.inR u then cfg.degX u - s'.abs u else 0) = cfg.degX u - (s.abs u + give) := by
      simp [s', huR]
    have hterm2 : (if s.inR u then cfg.degX u - s.abs u else 0) = cfg.degX u - s.abs u := by
      simp [huR]
    have hrest : ∑ x ∈ cfg.X.erase u, (if s'.inR x then cfg.degX x - s'.abs x else 0) =
        ∑ x ∈ cfg.X.erase u, (if s.inR x then cfg.degX x - s.abs x else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hne : x ≠ u := (Finset.mem_erase.mp hx).1
      simp [s', hne]
    rw [hterm1, hterm2, hrest]
    omega
  have hpot_drop : pot cfg s' + 2 ≤ pot cfg s := by
    unfold pot
    have hv : volR cfg s' = volR cfg s := rfl
    have hr : relabelCurRem cfg s' = relabelCurRem cfg s := rfl
    have hp : phiActive s' = phiActive s := rfl
    have hq : s'.peelQ = s.peelQ := rfl
    rw [hv, hr, hp, hq]
    omega
  exact ⟨hs'_inv, by omega, by omega, rfl, rfl⟩

/-! ### Micro-step 4: Advancing non-admissible current edge (`advanceCurStep`) -/

/-- Advances `cur u` past a non-admissible incident edge of `u`. -/
@[expose] def advanceCurStep (u : ℕ) (s : PruneState) : PruneState :=
  { s with cur := fun x => if x = u then s.cur u + 1 else s.cur x, steps := s.steps + 1 }

lemma advanceCurStep_inv_pot {cfg : PruneCfg} (hcfg : cfg.Valid) {s : PruneState}
    (hinv : PruningInv cfg s) {u : ℕ} (huR : s.inR u = true)
    (habs : s.abs u = cfg.degX u) (hcurLt : s.cur u < (cfg.incEdges u).length)
    (hnotAdm : let p := (cfg.incEdges u).getD (s.cur u) (0, false, 0)
      !(s.inR p.2.2 && decide (flowDir s.flow p.1 p.2.1 < (cfg.C_cap : ℤ)) &&
        decide (s.h u = s.h p.2.2 + 1))) :
    let s' := advanceCurStep u s
    PruningInv cfg s' ∧
    s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
    pot cfg s' < pot cfg s ∧
    volPminusB cfg s' = volPminusB cfg s ∧
    cutPR cfg s' = cutPR cfg s := by
  have hH3 := cfg.valid_three_le_H hcfg
  dsimp only [advanceCurStep]
  set p := (cfg.incEdges u).getD (s.cur u) (0, false, 0)
  have hpMem : p ∈ cfg.incEdges u := list_getD_mem (0, false, 0) (cfg.incEdges u) hcurLt
  have hp_cond : s.inR p.2.2 = false ∨ flowDir s.flow p.1 p.2.1 = (cfg.C_cap : ℤ) ∨
      s.h u ≤ s.h p.2.2 := by
    by_cases hwR : s.inR p.2.2 = true
    · by_cases hfl : flowDir s.flow p.1 p.2.1 < (cfg.C_cap : ℤ)
      · have hhle := hinv.h_edge u huR p hpMem hwR hfl
        have hne : s.h u ≠ s.h p.2.2 + 1 := by
          intro heq
          dsimp only at hnotAdm
          change !(s.inR p.2.2 && decide (flowDir s.flow p.1 p.2.1 < (cfg.C_cap : ℤ)) &&
            decide (s.h u = s.h p.2.2 + 1)) = true at hnotAdm
          simp [hwR, hfl, heq] at hnotAdm
        right; right; omega
      · have hidx_lt : p.1 < cfg.edges.length := by
          have := incEdgesAux_idx_ge hpMem
          omega
        have hcap := hinv.flow_cap p.1 hidx_lt
        have hleC : flowDir s.flow p.1 p.2.1 ≤ (cfg.C_cap : ℤ) := by
          cases p.2.1 <;> simp [flowDir] <;> omega
        right; left; omega
    · left; exact Bool.eq_false_iff.mpr hwR
  set s' : PruneState :=
    { s with cur := fun x => if x = u then s.cur u + 1 else s.cur x, steps := s.steps + 1 }
  have hs'_inv : PruningInv cfg s' :=
    { inR_sub := hinv.inR_sub
      not_inR_B := hinv.not_inR_B
      h_lt_H := hinv.h_lt_H
      cur_le := by
        intro x hxR
        by_cases hxu : x = u
        · subst hxu; simp [s']; omega
        · simpa [s', hxu] using hinv.cur_le x hxR
      abs_le := hinv.abs_le
      h_pos_abs := hinv.h_pos_abs
      flow_cap := hinv.flow_cap
      h_edge := hinv.h_edge
      cur_no_adm := by
        intro x hxR hxdeg j hj
        by_cases hxu : x = u
        · subst hxu
          simp only [s', ↓reduceIte] at hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
          · exact hinv.cur_no_adm x hxR hxdeg j hj'
          · exact hp_cond
        · dsimp only [s'] at hj ⊢
          simp only [hxu, ↓reduceIte] at hj
          simpa [hxu] using hinv.cur_no_adm x hxR hxdeg j hj
      cur_zero_of_abs_lt := by
        intro x hxR hxlt
        change s.abs x < cfg.degX x at hxlt
        have hxu : x ≠ u := by rintro rfl; omega
        dsimp only [s']
        simpa [hxu] using hinv.cur_zero_of_abs_lt x hxR hxlt
      flow_balance := hinv.flow_balance
      degR_eq := hinv.degR_eq
      degR_peel := hinv.degR_peel
      active_cov := hinv.active_cov
      active_mem_inActive := hinv.active_mem_inActive
      active_nodup := hinv.active_nodup
      active_sub := hinv.active_sub
      no_ex_isolated := hinv.no_ex_isolated }
  have huX : u ∈ cfg.X := hinv.inR_sub u huR
  have hlenPos : 0 < (cfg.incEdges u).length := by omega
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
    have ht1 : (if s'.inR u && decide (0 < (cfg.incEdges u).length) then
          (cfg.H - s'.h u) * (2 * (cfg.incEdges u).length + 2) +
          (2 * (cfg.incEdges u).length + 1 - 2 * s'.cur u)
        else 0) =
        (cfg.H - s.h u) * (2 * (cfg.incEdges u).length + 2) +
        (2 * (cfg.incEdges u).length + 1 - 2 * (s.cur u + 1)) := by
      simp [s', huR, hlenPos]
    have ht2 : (if s.inR u && decide (0 < (cfg.incEdges u).length) then
          (cfg.H - s.h u) * (2 * (cfg.incEdges u).length + 2) +
          (2 * (cfg.incEdges u).length + 1 - 2 * s.cur u)
        else 0) =
        (cfg.H - s.h u) * (2 * (cfg.incEdges u).length + 2) +
        (2 * (cfg.incEdges u).length + 1 - 2 * s.cur u) := by
      simp [huR, hlenPos]
    rw [ht1, ht2, hrest]
    omega
  have hpot_drop : pot cfg s' + 2 * (cfg.H + 4) = pot cfg s := by
    unfold pot
    have hv : volR cfg s' = volR cfg s := rfl
    have ha : sumAbsRem cfg s' = sumAbsRem cfg s := rfl
    have hp : phiActive s' = phiActive s := rfl
    have hq : s'.peelQ = s.peelQ := rfl
    rw [hv, ha, hp, hq, ← hrel_drop]
    ring
  exact ⟨hs'_inv, by omega, by omega, rfl, rfl⟩

/-! ### Micro-step 5: Pushing flow along an admissible edge (`pushFlowStep`) -/

/-- Pushes `δ = min (s.ex u) (C_cap - flowDir)` along the admissible edge `p = (idx, dir, w)`
incident to `u = s.active.head`. Advances `cur u` if saturating; removes `u` from `active` if
non-saturating (`s.ex u < rc`). -/
@[expose] def pushFlowStep (cfg : PruneCfg) (u : ℕ) (restAct : List ℕ) (s : PruneState) :
    PruneState :=
  let p := (cfg.incEdges u).getD (s.cur u) (0, false, 0)
  let idx := p.1
  let dir := p.2.1
  let w := p.2.2
  let rc := ((cfg.C_cap : ℤ) - flowDir s.flow idx dir).toNat
  let δ := min (s.ex u) rc
  let flow' : ℕ → ℤ := fun k =>
    if k = idx then (if dir then s.flow idx - (δ : ℤ) else s.flow idx + (δ : ℤ))
    else s.flow k
  let ex' : ℕ → ℕ := fun x =>
    if x = u then s.ex u - δ else if x = w then s.ex w + δ else s.ex x
  if rc ≤ s.ex u then
    { s with
      cur := fun x => if x = u then s.cur u + 1 else s.cur x
      ex := ex'
      flow := flow'
      active := if s.inActive w then s.active else w :: s.active
      inActive := fun x => if x = w then true else s.inActive x
      steps := s.steps + 1 }
  else
    { s with
      ex := ex'
      flow := flow'
      active := if s.inActive w then restAct else w :: restAct
      inActive := fun x => if x = u then false else if x = w then true else s.inActive x
      steps := s.steps + 1 }

private lemma flowContrib_sum_update {cfg : PruneCfg} (inR : ℕ → Bool) (flow flow' : ℕ → ℤ)
    (idx : ℕ) (x : ℕ) (q0 : ℕ × Bool × ℕ) (hq0_mem : q0 ∈ cfg.incEdges x) (hq0_idx : q0.1 = idx)
    (hother : ∀ k, k ≠ idx → flow' k = flow k) :
    ((cfg.incEdges x).map (edgeContrib inR flow' cfg.C_cap)).sum +
      edgeContrib inR flow cfg.C_cap q0 =
    ((cfg.incEdges x).map (edgeContrib inR flow cfg.C_cap)).sum +
      edgeContrib inR flow' cfg.C_cap q0 := by
  have hnodup : ((cfg.incEdges x).map Prod.fst).Nodup := incEdgesAux_nodup_idx x 0 cfg.edges
  suffices h : ∀ (M : List (ℕ × Bool × ℕ)),
      q0 ∈ M → (M.map Prod.fst).Nodup →
      (M.map (edgeContrib inR flow' cfg.C_cap)).sum + edgeContrib inR flow cfg.C_cap q0 =
        (M.map (edgeContrib inR flow cfg.C_cap)).sum + edgeContrib inR flow' cfg.C_cap q0 by
    exact h (cfg.incEdges x) hq0_mem hnodup
  intro M hqM hMnd
  induction M with
  | nil => simp at hqM
  | cons q qs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hMnd
    rcases hMnd with ⟨hnot, hqs_nd⟩
    rcases List.mem_cons.mp hqM with rfl | hmem
    · have hrest : qs.map (edgeContrib inR flow' cfg.C_cap) =
          qs.map (edgeContrib inR flow cfg.C_cap) := by
        apply List.map_congr_left
        intro q' hq'
        have hne : q'.1 ≠ idx := by
          intro heq
          apply hnot
          refine ⟨q', hq', heq.trans hq0_idx.symm⟩
        by_cases hwR : inR q'.2.2 = true
        · cases q'.2.1 <;> simp [edgeContrib, hwR, flowDir, hother q'.1 hne]
        · simp [edgeContrib, hwR]
      simp only [List.map_cons, List.sum_cons, hrest]
      ring
    · have hne : q.1 ≠ idx := by
        intro heq
        apply hnot
        refine ⟨q0, hmem, hq0_idx.trans heq.symm⟩
      have hqeq : edgeContrib inR flow' cfg.C_cap q = edgeContrib inR flow cfg.C_cap q := by
        by_cases hwR : inR q.2.2 = true
        · cases q.2.1 <;> simp [edgeContrib, hwR, flowDir, hother q.1 hne]
        · simp [edgeContrib, hwR]
      have ih' := ih hmem hqs_nd
      simp only [List.map_cons, List.sum_cons, hqeq]
      omega

private lemma flowContrib_sum_unchanged (cfg : PruneCfg) (inR : ℕ → Bool) (flow flow' : ℕ → ℤ)
    (idx : ℕ) (x : ℕ) (hno : ∀ q ∈ cfg.incEdges x, q.1 ≠ idx)
    (hother : ∀ k, k ≠ idx → flow' k = flow k) :
    ((cfg.incEdges x).map (edgeContrib inR flow' cfg.C_cap)).sum =
      ((cfg.incEdges x).map (edgeContrib inR flow cfg.C_cap)).sum := by
  congr 1
  apply List.map_congr_left
  intro q hq
  have hne := hno q hq
  by_cases hwR : inR q.2.2 = true
  · cases q.2.1 <;> simp [edgeContrib, hwR, flowDir, hother q.1 hne]
  · simp [edgeContrib, hwR]

lemma pushFlowStep_inv_pot {cfg : PruneCfg} (hcfg : cfg.Valid) {s : PruneState}
    (hinv : PruningInv cfg s) {u : ℕ} {restAct : List ℕ} (hact : s.active = u :: restAct)
    (huR : s.inR u = true) (hexPos : 0 < s.ex u) (habs : s.abs u = cfg.degX u)
    (hcurLt : s.cur u < (cfg.incEdges u).length)
    (hadm : let p := (cfg.incEdges u).getD (s.cur u) (0, false, 0)
      s.inR p.2.2 = true ∧ flowDir s.flow p.1 p.2.1 < (cfg.C_cap : ℤ) ∧ s.h u = s.h p.2.2 + 1) :
    let s' := pushFlowStep cfg u restAct s
    PruningInv cfg s' ∧
    s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
    pot cfg s' < pot cfg s ∧
    volPminusB cfg s' = volPminusB cfg s ∧
    cutPR cfg s' = cutPR cfg s := by
  have hH3 := cfg.valid_three_le_H hcfg
  set p := (cfg.incEdges u).getD (s.cur u) (0, false, 0)
  set idx := p.1
  set dir := p.2.1
  set w := p.2.2
  have hpMem : p ∈ cfg.incEdges u := list_getD_mem (0, false, 0) (cfg.incEdges u) hcurLt
  have hwu : w ≠ u := incEdgesAux_ne_self hpMem
  have hw_symm : (idx, !dir, u) ∈ cfg.incEdges w := incEdges_symm hpMem
  have hwX : w ∈ cfg.X := (incEdges_mem_sub hpMem).2
  have huX : u ∈ cfg.X := hinv.inR_sub u huR
  have hwLenPos : 0 < (cfg.incEdges w).length := List.length_pos_of_mem hw_symm
  have hidx_lt : idx < cfg.edges.length := by
    have := incEdgesAux_idx_ge hpMem
    omega
  have hcap_idx := hinv.flow_cap idx hidx_lt
  have hwR : s.inR w = true := hadm.1
  have hfd_lt : flowDir s.flow idx dir < (cfg.C_cap : ℤ) := hadm.2.1
  have hh_eq : s.h u = s.h w + 1 := hadm.2.2
  set rc := ((cfg.C_cap : ℤ) - flowDir s.flow idx dir).toNat
  have hrc_pos : 1 ≤ rc := by omega
  have hrc_cast : (rc : ℤ) = (cfg.C_cap : ℤ) - flowDir s.flow idx dir := by omega
  set δ := min (s.ex u) rc
  have hδ_pos : 1 ≤ δ := by omega
  have hδ_ex : δ ≤ s.ex u := min_le_left _ _
  have hδ_rc : δ ≤ rc := min_le_right _ _
  set flow' : ℕ → ℤ := fun k =>
    if k = idx then (if dir then s.flow idx - (δ : ℤ) else s.flow idx + (δ : ℤ))
    else s.flow k
  set ex' : ℕ → ℕ := fun x =>
    if x = u then s.ex u - δ else if x = w then s.ex w + δ else s.ex x
  have hother : ∀ k, k ≠ idx → flow' k = s.flow k := fun k hk => by simp [flow', hk]
  have hflow'_cap : ∀ k, k < cfg.edges.length →
      -(cfg.C_cap : ℤ) ≤ flow' k ∧ flow' k ≤ (cfg.C_cap : ℤ) := by
    intro k hk
    by_cases hki : k = idx
    · subst hki
      cases hdir : dir <;> simp only [flow', ↓reduceIte, hdir, Bool.false_eq_true] <;>
        simp [flowDir, hdir] at hrc_cast hcap_idx <;> omega
    · simp only [flow', hki, ↓reduceIte]; exact hinv.flow_cap k hk
  have hflowDir'_fwd : flowDir flow' idx dir = flowDir s.flow idx dir + (δ : ℤ) := by
    (cases hdir : dir <;> simp [flowDir, flow', hdir]); omega
  have hflowDir'_back : flowDir flow' idx (!dir) = flowDir s.flow idx (!dir) - (δ : ℤ) := by
    (cases hdir : dir <;> simp [flowDir, flow', hdir]); omega
  have h_edge_comm : ∀ x, s.inR x = true → ∀ q ∈ cfg.incEdges x, s.inR q.2.2 = true →
      flowDir flow' q.1 q.2.1 < (cfg.C_cap : ℤ) → s.h x ≤ s.h q.2.2 + 1 := by
    intro x hxR q hq hqR hflt
    by_cases hqi : q.1 = idx
    · rcases incEdges_unique_idx hq hpMem hqi with ⟨rfl, rfl⟩ | ⟨rfl, hq2, _⟩
      · have hpw : p.2.2 = w := rfl
        rw [hpw]; omega
      · rw [← hq2]; omega
    · rw [show flowDir flow' q.1 q.2.1 = flowDir s.flow q.1 q.2.1 by
        cases q.2.1 <;> simp [flowDir, hother q.1 hqi]] at hflt
      exact hinv.h_edge x hxR q hq hqR hflt
  have hflow_bal_comm : ∀ x, s.inR x = true →
      (ex' x : ℤ) + (s.abs x : ℤ) =
        ((cfg.incEdges x).map (edgeContrib s.inR flow' cfg.C_cap)).sum := by
    intro x hxR
    have hfb := hinv.flow_balance x hxR
    by_cases hxu : x = u
    · subst hxu
      have hupd := flowContrib_sum_update s.inR s.flow flow' idx x p hpMem rfl hother
      have hex_z : (ex' x : ℤ) = (s.ex x : ℤ) - (δ : ℤ) := by simp [ex']; omega
      have he1 : edgeContrib s.inR s.flow cfg.C_cap p = -(flowDir s.flow idx dir) := by
        simp [edgeContrib, hwR, w, idx, dir]
      have he2 : edgeContrib s.inR flow' cfg.C_cap p = -(flowDir s.flow idx dir + (δ : ℤ)) := by
        simp [edgeContrib, hwR, w, idx, dir, hflowDir'_fwd]
      omega
    · by_cases hxw : x = w
      · subst hxw
        have hupd := flowContrib_sum_update s.inR s.flow flow' idx w (idx, !dir, u) hw_symm rfl hother
        have hex_z : (ex' w : ℤ) = (s.ex w : ℤ) + (δ : ℤ) := by simp [ex', hxu]
        have he1 : edgeContrib s.inR s.flow cfg.C_cap (idx, !dir, u) =
            -(flowDir s.flow idx (!dir)) := by
          simp [edgeContrib, huR]
        have he2 : edgeContrib s.inR flow' cfg.C_cap (idx, !dir, u) =
            -(flowDir s.flow idx (!dir) - (δ : ℤ)) := by
          simp [edgeContrib, huR, hflowDir'_back]
        omega
      · have hno : ∀ q ∈ cfg.incEdges x, q.1 ≠ idx := by
          intro q hq hqi
          rcases incEdges_unique_idx hq hpMem hqi with ⟨rfl, _⟩ | ⟨hxw', _, _⟩
          · exact hxu rfl
          · exact hxw hxw'
        have hunc := flowContrib_sum_unchanged cfg s.inR s.flow flow' idx x hno hother
        have hex_eq : ex' x = s.ex x := by simp [ex', hxu, hxw]
        rw [hex_eq, hunc]
        exact hfb
  have hcur_no_adm_old : ∀ x, s.inR x = true → s.abs x = cfg.degX x →
      ∀ j < s.cur x,
        let q := (cfg.incEdges x).getD j (0, false, 0)
        s.inR q.2.2 = false ∨ flowDir flow' q.1 q.2.1 = (cfg.C_cap : ℤ) ∨ s.h x ≤ s.h q.2.2 := by
    intro x hxR hxdeg j hj
    have hold := hinv.cur_no_adm x hxR hxdeg j hj
    dsimp only at hold ⊢
    set q := (cfg.incEdges x).getD j (0, false, 0)
    by_cases hqi : q.1 = idx
    · have hqMem : q ∈ cfg.incEdges x := list_getD_mem (0, false, 0) (cfg.incEdges x)
        (lt_of_lt_of_le hj (hinv.cur_le x hxR))
      rcases incEdges_unique_idx hqMem hpMem hqi with ⟨rfl, hqp⟩ | ⟨hxw, hq2, _⟩
      · have hnd : ((cfg.incEdges x).map Prod.fst).Nodup := incEdgesAux_nodup_idx x 0 cfg.edges
        have : j = s.cur x := by
          clear hflow_bal_comm h_edge_comm hflow'_cap hold
          suffices hc : ∀ (M : List (ℕ × Bool × ℕ)) (a b : ℕ),
              a < M.length → b < M.length →
              ((M.getD a (0, false, 0)).1 = (M.getD b (0, false, 0)).1) →
              (M.map Prod.fst).Nodup → a = b by
            exact hc (cfg.incEdges x) j (s.cur x) (lt_trans hj hcurLt) hcurLt hqi hnd
          intro M a b ha hb heq hndM
          induction M generalizing a b with
          | nil => simp at ha
          | cons m ms ihm =>
            simp only [List.map_cons, List.nodup_cons, List.mem_map] at hndM
            cases a <;> cases b
            · rfl
            · simp only [List.getD_cons_zero, List.getD_cons_succ] at heq
              have hm := list_getD_mem (0, false, 0) ms (by simp at hb; omega)
              exact False.elim (hndM.1 ⟨ms.getD _ (0, false, 0), hm, heq.symm⟩)
            · simp only [List.getD_cons_zero, List.getD_cons_succ] at heq
              have hm := list_getD_mem (0, false, 0) ms (by simp at ha; omega)
              exact False.elim (hndM.1 ⟨ms.getD _ (0, false, 0), hm, heq⟩)
            · simp only [List.getD_cons_succ] at heq
              exact congrArg Nat.succ (ihm _ _ (by simp at ha; omega) (by simp at hb; omega) heq hndM.2)
        omega
      · right; right
        have hpw : p.2.2 = w := rfl
        rw [hxw, hpw, ← hq2]; omega
    · rcases hold with h1 | h2 | h3
      · exact Or.inl h1
      · right; left
        rw [show flowDir flow' q.1 q.2.1 = flowDir s.flow q.1 q.2.1 by
          cases q.2.1 <;> simp [flowDir, hother q.1 hqi]]
        exact h2
      · exact Or.inr (Or.inr h3)
  by_cases hsat : rc ≤ s.ex u
  · rw [show pushFlowStep cfg u restAct s =
        { s with
          cur := fun x => if x = u then s.cur u + 1 else s.cur x
          ex := ex'
          flow := flow'
          active := if s.inActive w then s.active else w :: s.active
          inActive := fun x => if x = w then true else s.inActive x
          steps := s.steps + 1 } by
      dsimp only [pushFlowStep]
      exact ite_eq_left_iff.mpr fun hn => False.elim (hn hsat)]
    have hδ_eq : δ = rc := min_eq_right hsat
    set s' : PruneState :=
      { s with
        cur := fun x => if x = u then s.cur u + 1 else s.cur x
        ex := ex'
        flow := flow'
        active := if s.inActive w then s.active else w :: s.active
        inActive := fun x => if x = w then true else s.inActive x
        steps := s.steps + 1 }
    have hs'_inv : PruningInv cfg s' :=
      { inR_sub := hinv.inR_sub
        not_inR_B := hinv.not_inR_B
        h_lt_H := hinv.h_lt_H
        cur_le := by
          intro x hxR
          by_cases hxu : x = u
          · subst hxu; simp [s']; omega
          · dsimp only [s']; simpa [hxu] using hinv.cur_le x hxR
        abs_le := hinv.abs_le
        h_pos_abs := hinv.h_pos_abs
        flow_cap := hflow'_cap
        h_edge := h_edge_comm
        cur_no_adm := by
          intro x hxR hxdeg j hj
          by_cases hxu : x = u
          · subst hxu
            simp only [s', ↓reduceIte] at hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
            · exact hcur_no_adm_old x hxR hxdeg j hj'
            · right; left
              change flowDir flow' idx dir = (cfg.C_cap : ℤ)
              rw [hflowDir'_fwd, hδ_eq, hrc_cast]
              ring
          · dsimp only [s'] at hj ⊢
            simp only [hxu, ↓reduceIte] at hj ⊢
            exact hcur_no_adm_old x hxR hxdeg j hj
        cur_zero_of_abs_lt := by
          intro x hxR hxlt
          change s.abs x < cfg.degX x at hxlt
          have hxu : x ≠ u := by rintro rfl; omega
          dsimp only [s']; simpa [hxu] using hinv.cur_zero_of_abs_lt x hxR hxlt
        flow_balance := hflow_bal_comm
        degR_eq := hinv.degR_eq
        degR_peel := hinv.degR_peel
        active_cov := by
          intro x hxR hxpos
          by_cases hxw : x = w
          · dsimp only [s']; rw [hxw]
            by_cases hin : s.inActive w = true
            · simp [hin, (hinv.active_mem_inActive w).mp hin]
            · simp [hin]
          · have hxu : x ≠ u → ex' x = s.ex x := fun hne => by simp [ex', hne, hxw]
            have hmem : x ∈ s.active := by
              by_cases hxueq : x = u
              · subst hxueq; rw [hact]; simp
              · change 0 < ex' x at hxpos
                rw [hxu hxueq] at hxpos
                exact hinv.active_cov x hxR hxpos
            dsimp only [s']
            by_cases hin : s.inActive w = true <;> simp [hin, hmem]
        active_mem_inActive := by
          intro x
          by_cases hxw : x = w
          · dsimp only [s']; rw [hxw]
            by_cases hin : s.inActive w = true
            · simp [hin, (hinv.active_mem_inActive w).mp hin]
            · simp [hin]
          · dsimp only [s']
            by_cases hin : s.inActive w = true <;> simp [hxw, hin, hinv.active_mem_inActive x]
        active_nodup := by
          by_cases hin : s.inActive w = true
          · simpa [s', hin] using hinv.active_nodup
          · have hnot : w ∉ s.active := fun hm => hin ((hinv.active_mem_inActive w).mpr hm)
            simpa [s', hin] using List.nodup_cons.mpr ⟨hnot, hinv.active_nodup⟩
        active_sub := by
          intro x hx
          by_cases hin : s.inActive w = true
          · simp only [s', hin, ↓reduceIte] at hx; exact hinv.active_sub x hx
          · simp only [s', hin, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact hwX
            · exact hinv.active_sub x hx
        no_ex_isolated := by
          intro x hx0
          have hne := hinv.no_ex_isolated x hx0
          have hxu : x ≠ u := by rintro rfl; omega
          have hxw : x ≠ w := by rintro rfl; omega
          have hmem : x ∉ s'.active := by
            by_cases hin : s.inActive w = true <;> simp [s', hin, hxw, hne.2.2.1]
          exact ⟨by simpa [s', ex', hxu, hxw] using hne.1, hne.2.1, hmem, hne.2.2.2⟩ }
    have hlenPos : 0 < (cfg.incEdges u).length := by omega
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
      have ht1 : (if s'.inR u && decide (0 < (cfg.incEdges u).length) then
            (cfg.H - s'.h u) * (2 * (cfg.incEdges u).length + 2) +
            (2 * (cfg.incEdges u).length + 1 - 2 * s'.cur u)
          else 0) =
          (cfg.H - s.h u) * (2 * (cfg.incEdges u).length + 2) +
          (2 * (cfg.incEdges u).length + 1 - 2 * (s.cur u + 1)) := by
        simp [s', huR, hlenPos]
      have ht2 : (if s.inR u && decide (0 < (cfg.incEdges u).length) then
            (cfg.H - s.h u) * (2 * (cfg.incEdges u).length + 2) +
            (2 * (cfg.incEdges u).length + 1 - 2 * s.cur u)
          else 0) =
          (cfg.H - s.h u) * (2 * (cfg.incEdges u).length + 2) +
          (2 * (cfg.incEdges u).length + 1 - 2 * s.cur u) := by
        simp [huR, hlenPos]
      rw [ht1, ht2, hrest]
      omega
    have hw_lt : s.h w < cfg.H := hinv.h_lt_H w hwR
    have hphi_le : phiActive s' ≤ phiActive s + (cfg.H + 1) := by
      have hinR' : s'.inR = s.inR := rfl
      have hh' : s'.h = s.h := rfl
      unfold phiActive
      rw [hinR', hh']
      by_cases hin : s.inActive w = true
      · have hact' : s'.active = s.active := by dsimp only [s']; simp [hin]
        rw [hact']; omega
      · have hact' : s'.active = w :: s.active := by dsimp only [s']; simp [hin]
        rw [hact', List.map_cons, List.sum_cons, hwR]
        simp only [↓reduceIte]
        omega
    have hpot_drop : pot cfg s' + 6 ≤ pot cfg s := by
      unfold pot
      have hv : volR cfg s' = volR cfg s := rfl
      have ha : sumAbsRem cfg s' = sumAbsRem cfg s := rfl
      have hq : s'.peelQ = s.peelQ := rfl
      rw [hv, ha, hq]
      nlinarith
    exact ⟨hs'_inv, by have hst : s'.steps = s.steps + 1 := rfl; rw [hst]; omega, by omega, rfl, rfl⟩
  · rw [show pushFlowStep cfg u restAct s =
        { s with
          ex := ex'
          flow := flow'
          active := if s.inActive w then restAct else w :: restAct
          inActive := fun x => if x = u then false else if x = w then true else s.inActive x
          steps := s.steps + 1 } by
      dsimp only [pushFlowStep]
      exact ite_eq_right_iff.mpr fun hp => False.elim (hsat hp)]
    have hδ_eq : δ = s.ex u := min_eq_left (le_of_not_ge hsat)
    set s' : PruneState :=
      { s with
        ex := ex'
        flow := flow'
        active := if s.inActive w then restAct else w :: restAct
        inActive := fun x => if x = u then false else if x = w then true else s.inActive x
        steps := s.steps + 1 }
    have huNotRest : u ∉ restAct := by
      have hn := hinv.active_nodup; rw [hact] at hn; exact (List.nodup_cons.mp hn).1
    have hrestNodup : restAct.Nodup := by
      have hn := hinv.active_nodup; rw [hact] at hn; exact (List.nodup_cons.mp hn).2
    have hwin_iff : s.inActive w = true ↔ w ∈ restAct := by
      rw [hinv.active_mem_inActive w, hact, List.mem_cons]
      exact ⟨fun h => h.resolve_left hwu, fun h => Or.inr h⟩
    have hs'_inv : PruningInv cfg s' :=
      { inR_sub := hinv.inR_sub
        not_inR_B := hinv.not_inR_B
        h_lt_H := hinv.h_lt_H
        cur_le := hinv.cur_le
        abs_le := hinv.abs_le
        h_pos_abs := hinv.h_pos_abs
        flow_cap := hflow'_cap
        h_edge := h_edge_comm
        cur_no_adm := hcur_no_adm_old
        cur_zero_of_abs_lt := hinv.cur_zero_of_abs_lt
        flow_balance := hflow_bal_comm
        degR_eq := hinv.degR_eq
        degR_peel := hinv.degR_peel
        active_cov := by
          intro x hxR hxpos
          have hxu : x ≠ u := by
            rintro rfl
            change 0 < ex' x at hxpos
            simp [ex', hδ_eq] at hxpos
          by_cases hxw : x = w
          · dsimp only [s']; rw [hxw]
            by_cases hin : s.inActive w = true
            · simp [hin, hwin_iff.mp hin]
            · simp [hin]
          · have hmem := hinv.active_cov x hxR (by simpa [s', ex', hxu, hxw] using hxpos)
            rw [hact, List.mem_cons] at hmem
            have hxrest : x ∈ restAct := hmem.resolve_left hxu
            dsimp only [s']
            by_cases hin : s.inActive w = true <;> simp [hin, hxrest]
        active_mem_inActive := by
          intro x
          by_cases hxu : x = u
          · subst hxu
            dsimp only [s']
            by_cases hin : s.inActive w = true <;> simp [hin, huNotRest, hwu.symm]
          · by_cases hxw : x = w
            · dsimp only [s']; rw [hxw] at hxu ⊢
              by_cases hin : s.inActive w = true
              · simp [hxu, hin, hwin_iff.mp hin]
              · simp [hxu, hin]
            · have hm := hinv.active_mem_inActive x
              rw [hact, List.mem_cons] at hm
              dsimp only [s']
              by_cases hin : s.inActive w = true <;> simp [hxu, hxw, hin, hm]
        active_nodup := by
          by_cases hin : s.inActive w = true
          · simpa [s', hin] using hrestNodup
          · have hwNotRest : w ∉ restAct := fun hm => hin (hwin_iff.mpr hm)
            simpa [s', hin] using List.nodup_cons.mpr ⟨hwNotRest, hrestNodup⟩
        active_sub := by
          intro x hx
          have hrestSub : ∀ y ∈ restAct, y ∈ cfg.X :=
            fun y hy => hinv.active_sub y (by rw [hact]; exact List.mem_cons_of_mem _ hy)
          by_cases hin : s.inActive w = true
          · simp only [s', hin, ↓reduceIte] at hx; exact hrestSub x hx
          · simp only [s', hin, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact hwX
            · exact hrestSub x hx
        no_ex_isolated := by
          intro x hx0
          have hne := hinv.no_ex_isolated x hx0
          have hxu : x ≠ u := by rintro rfl; omega
          have hxw : x ≠ w := by rintro rfl; omega
          have hmem : x ∉ s'.active := by
            have hnrest : x ∉ restAct := fun hm => hne.2.2.1 (by rw [hact]; exact List.mem_cons_of_mem _ hm)
            by_cases hin : s.inActive w = true <;> simp [s', hin, hxw, hnrest]
          exact ⟨by simpa [s', ex', hxu, hxw] using hne.1, hne.2.1, hmem, hne.2.2.2⟩ }
    have hphi_drop : phiActive s' + 1 ≤ phiActive s := by
      have hinR' : s'.inR = s.inR := rfl
      have hh' : s'.h = s.h := rfl
      unfold phiActive
      rw [hinR', hh']
      have hs_eq : (s.active.map fun x => if s.inR x then s.h x + 2 else 2).sum =
          (s.h u + 2) + (restAct.map fun x => if s.inR x then s.h x + 2 else 2).sum := by
        rw [hact, List.map_cons, List.sum_cons, huR]; simp
      by_cases hin : s.inActive w = true
      · have hact' : s'.active = restAct := by dsimp only [s']; simp [hin]
        rw [hact', hs_eq]
        omega
      · have hact' : s'.active = w :: restAct := by dsimp only [s']; simp [hin]
        rw [hact', List.map_cons, List.sum_cons, hwR, hs_eq]
        simp only [↓reduceIte]
        omega
    have hpot_drop : pot cfg s' + 2 ≤ pot cfg s := by
      unfold pot
      have hv : volR cfg s' = volR cfg s := rfl
      have hr : relabelCurRem cfg s' = relabelCurRem cfg s := rfl
      have ha : sumAbsRem cfg s' = sumAbsRem cfg s := rfl
      have hq : s'.peelQ = s.peelQ := rfl
      rw [hv, hr, ha, hq]
      omega
    exact ⟨hs'_inv, by have hst : s'.steps = s.steps + 1 := rfl; rw [hst]; omega, by omega, rfl, rfl⟩


end

end MinCostFlow.Expander
