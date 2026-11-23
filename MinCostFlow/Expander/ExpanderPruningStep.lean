module

public import MinCostFlow.Expander.ExpanderPruningStepFreeze

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Expander Pruning Step Helpers (Combined pruneStep, Wrappers & PeelQInv)
-/

namespace MinCostFlow.Expander

open Classical

public section

/-! ### Combined pruning step (`pruneStep`) -/

/-- One deterministic step of push-relabel + low-degree peeling expander pruning. -/
@[expose] noncomputable def pruneStep (cfg : PruneCfg) (s : PruneState) : PruneState :=
  match s.peelQ with
  | v :: rest => peelStep cfg v rest s
  | [] =>
      match s.active with
      | [] => s
      | u :: restAct =>
          if !(s.inR u) || (s.ex u == 0) then
            popInactiveStep u restAct s
          else if s.abs u < cfg.degX u then
            absorbStep cfg u s
          else if s.cur u < (cfg.incEdges u).length then
            let p := (cfg.incEdges u).getD (s.cur u) (0, false, 0)
            if s.inR p.2.2 && decide (flowDir s.flow p.1 p.2.1 < (cfg.C_cap : ℤ)) &&
                decide (s.h u = s.h p.2.2 + 1) then
              pushFlowStep cfg u restAct s
            else
              advanceCurStep u s
          else if s.h u + 1 < cfg.H then
            relabelStep u s
          else
            freezeStep cfg u s

/-- Every non-terminal step of `pruneStep` preserves `PruningInv`, strictly decreases `pot`,
keeps `steps + pot` non-increasing, and keeps `volPminusB + 2 * C_cap * cutPR` non-increasing. -/
theorem pruneStep_inv_pot {cfg : PruneCfg} (hcfg : cfg.Valid) {s : PruneState}
    (hinv : PruningInv cfg s) (hne : s.peelQ ≠ [] ∨ s.active ≠ [])
    (hθ : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d, d < cfg.θ_out_nat → 3 * d ≤ cfg.degX x) :
    let s' := pruneStep cfg s
    PruningInv cfg s' ∧
    s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
    pot cfg s' < pot cfg s ∧
    volPminusB cfg s' + 2 * cfg.C_cap * cutPR cfg s' ≤
      volPminusB cfg s + 2 * cfg.C_cap * cutPR cfg s := by
  dsimp only [pruneStep]
  cases hq : s.peelQ with
  | cons v rest =>
    exact peelStep_inv_pot hcfg hinv hq hθ
  | nil =>
    cases ha : s.active with
    | nil =>
      exact False.elim (hne.elim (fun h => h hq) (fun h => h ha))
    | cons u restAct =>
      by_cases hdead : s.inR u = false ∨ s.ex u = 0
      · have hb : (!(s.inR u) || (s.ex u == 0)) = true := by
          rcases hdead with h1 | h2
          · simp [h1]
          · simp [h2]
        simp only [hb, ↓reduceIte]
        rcases popInactiveStep_inv_pot hinv ha hdead with ⟨h1, h2, h3, h4, h5⟩
        exact ⟨h1, h2, h3, by rw [h4, h5]⟩
      · have halive : s.inR u = true ∧ 0 < s.ex u := by
          by_cases h1 : s.inR u = true
          · exact ⟨h1, Nat.pos_of_ne_zero fun hz => hdead (Or.inr hz)⟩
          · exact False.elim (hdead (Or.inl (Bool.eq_false_iff.mpr h1)))
        have hb : (!(s.inR u) || (s.ex u == 0)) = false := by
          have hnz : s.ex u ≠ 0 := Nat.ne_of_gt halive.2
          simp [halive.1, hnz]
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        by_cases habsLt : s.abs u < cfg.degX u
        · simp only [habsLt, ↓reduceIte]
          rcases absorbStep_inv_pot hinv halive.1 halive.2 habsLt with ⟨h1, h2, h3, h4, h5⟩
          exact ⟨h1, h2, h3, by rw [h4, h5]⟩
        · simp only [habsLt, ↓reduceIte]
          have habsEq : s.abs u = cfg.degX u := le_antisymm (hinv.abs_le u halive.1) (le_of_not_gt habsLt)
          by_cases hcurLt : s.cur u < (cfg.incEdges u).length
          · rw [ite_eq_left hcurLt]
            set p := (cfg.incEdges u).getD (s.cur u) (0, false, 0)
            by_cases hadm : s.inR p.2.2 = true ∧ flowDir s.flow p.1 p.2.1 < (cfg.C_cap : ℤ) ∧
                  s.h u = s.h p.2.2 + 1
            · have hb2 : (s.inR p.2.2 && decide (flowDir s.flow p.1 p.2.1 < (cfg.C_cap : ℤ)) &&
                  decide (s.h u = s.h p.2.2 + 1)) = true := by
                rw [hadm.1, decide_eq_true hadm.2.1, decide_eq_true hadm.2.2]; rfl
              rw [ite_eq_left hb2]
              rcases pushFlowStep_inv_pot hcfg hinv ha halive.1 halive.2 habsEq hcurLt hadm with
                ⟨h1, h2, h3, h4, h5⟩
              exact ⟨h1, h2, h3, by rw [h4, h5]⟩
            · have hb2 : (s.inR p.2.2 && decide (flowDir s.flow p.1 p.2.1 < (cfg.C_cap : ℤ)) &&
                  decide (s.h u = s.h p.2.2 + 1)) = false := by
                by_cases h1 : s.inR p.2.2 = true
                · by_cases h2 : flowDir s.flow p.1 p.2.1 < (cfg.C_cap : ℤ)
                  · have h3 : s.h u ≠ s.h p.2.2 + 1 := fun heq => hadm ⟨h1, h2, heq⟩
                    rw [h1, decide_eq_true h2, decide_eq_false h3]; rfl
                  · rw [h1, decide_eq_false h2]; rfl
                · rw [Bool.eq_false_iff.mpr h1]; rfl
              rw [ite_eq_right (Bool.eq_false_iff.mp hb2)]
              rcases advanceCurStep_inv_pot hcfg hinv halive.1 habsEq hcurLt
                  (by
                    by_contra hcontra
                    have hbad : s.inR p.2.2 = true ∧ flowDir s.flow p.1 p.2.1 < (cfg.C_cap : ℤ) ∧
                        s.h u = s.h p.2.2 + 1 := by
                      simp only [p] at *; simp_all
                    exact hadm hbad) with
                ⟨h1, h2, h3, h4, h5⟩
              exact ⟨h1, h2, h3, by rw [h4, h5]⟩
          · simp only [hcurLt, ↓reduceIte]
            have hcurEnd : s.cur u = (cfg.incEdges u).length :=
              le_antisymm (hinv.cur_le u halive.1) (le_of_not_gt hcurLt)
            by_cases hhLt : s.h u + 1 < cfg.H
            · simp only [hhLt, ↓reduceIte]
              rcases relabelStep_inv_pot hcfg hinv halive.1 halive.2 habsEq hcurEnd hhLt with
                ⟨h1, h2, h3, h4, h5⟩
              exact ⟨h1, h2, h3, by rw [h4, h5]⟩
            · simp only [hhLt, ↓reduceIte]
              have huH : s.h u + 1 = cfg.H := by
                have := hinv.h_lt_H u halive.1; omega
              exact freezeStep_inv_pot hcfg hinv halive.1 halive.2 habsEq hcurEnd huH



/-- Public wrapper for `peelStep_inv_pot`. -/
lemma peelStep_inv_pot_pub {cfg : PruneCfg} (hcfg : cfg.Valid) {s : PruneState}
    (hinv : PruningInv cfg s) {v : ℕ} {rest : List ℕ} (hq : s.peelQ = v :: rest)
    (hθ : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d, d < cfg.θ_out_nat → 3 * d ≤ cfg.degX x) :
    let s' := peelStep cfg v rest s
    PruningInv cfg s' ∧
    s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
    pot cfg s' < pot cfg s ∧
    volPminusB cfg s' + 2 * cfg.C_cap * cutPR cfg s' ≤
      volPminusB cfg s + 2 * cfg.C_cap * cutPR cfg s :=
  peelStep_inv_pot hcfg hinv hq hθ

/-- Public wrapper for `popInactiveStep_inv_pot`. -/
lemma popInactiveStep_inv_pot_pub {cfg : PruneCfg} {s : PruneState}
    (hinv : PruningInv cfg s) {u : ℕ} {restAct : List ℕ} (hact : s.active = u :: restAct)
    (hdead : s.inR u = false ∨ s.ex u = 0) :
    let s' := popInactiveStep u restAct s
    PruningInv cfg s' ∧
    s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
    pot cfg s' < pot cfg s ∧
    volPminusB cfg s' = volPminusB cfg s ∧
    cutPR cfg s' = cutPR cfg s :=
  popInactiveStep_inv_pot hinv hact hdead

/-- Public wrapper for `absorbStep_inv_pot`. -/
lemma absorbStep_inv_pot_pub {cfg : PruneCfg} {s : PruneState} {u : ℕ}
    (hinv : PruningInv cfg s) (huR : s.inR u = true) (hexPos : 0 < s.ex u)
    (habsLt : s.abs u < cfg.degX u) :
    let s' := absorbStep cfg u s
    PruningInv cfg s' ∧
    s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
    pot cfg s' < pot cfg s ∧
    volPminusB cfg s' = volPminusB cfg s ∧
    cutPR cfg s' = cutPR cfg s :=
  absorbStep_inv_pot hinv huR hexPos habsLt

/-- Public wrapper for `advanceCurStep_inv_pot`. -/
lemma advanceCurStep_inv_pot_pub {cfg : PruneCfg} (hcfg : cfg.Valid) {s : PruneState}
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
    cutPR cfg s' = cutPR cfg s :=
  advanceCurStep_inv_pot hcfg hinv huR habs hcurLt hnotAdm

/-- Public wrapper for `pushFlowStep_inv_pot`. -/
lemma pushFlowStep_inv_pot_pub {cfg : PruneCfg} (hcfg : cfg.Valid) {s : PruneState}
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
    cutPR cfg s' = cutPR cfg s :=
  pushFlowStep_inv_pot hcfg hinv hact huR hexPos habs hcurLt hadm

/-- Public wrapper for `relabelStep_inv_pot`. -/
lemma relabelStep_inv_pot_pub {cfg : PruneCfg} (hcfg : cfg.Valid) {s : PruneState}
    (hinv : PruningInv cfg s) {u : ℕ} (huR : s.inR u = true) (hexPos : 0 < s.ex u)
    (habs : s.abs u = cfg.degX u) (hcurEnd : s.cur u = (cfg.incEdges u).length)
    (hhLt : s.h u + 1 < cfg.H) :
    let s' := relabelStep u s
    PruningInv cfg s' ∧
    s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
    pot cfg s' < pot cfg s ∧
    volPminusB cfg s' = volPminusB cfg s ∧
    cutPR cfg s' = cutPR cfg s :=
  relabelStep_inv_pot hcfg hinv huR hexPos habs hcurEnd hhLt

/-- Parameterized freeze sweep step taking any explicit removal list `remList`
(representing `u` followed by vertices in `A \ {u}` collected in bucket order). -/
@[expose] noncomputable def freezeStepWith (cfg : PruneCfg) (u : ℕ) (remList : List ℕ)
    (s : PruneState) : PruneState :=
  let hTmp := fun x => if x = u then cfg.H else s.h x
  let sMid : PruneState := { s with h := hTmp, cur := fun x => if x = u then 0 else s.cur x }
  let s1 := remList.foldl (fun st a => removeOneFromR cfg a st) sMid
  let volEA := (remList.map fun a => (cfg.incEdges a).length).sum
  { s1 with steps := s.steps + cfg.H + volEA }

private lemma phiActive_update_h_le (u : ℕ) (inR : ℕ → Bool) (h : ℕ → ℕ) (H : ℕ)
    (hHu : H = h u + 1) :
    ∀ L : List ℕ, L.Nodup →
      (L.map fun x => if inR x then (if x = u then H else h x) + 2 else 2).sum ≤
        (L.map fun x => if inR x then h x + 2 else 2).sum + 1
  | [], _ => by simp
  | a :: as, hnd => by
    rw [List.nodup_cons] at hnd
    have ih := phiActive_update_h_le u inR h H hHu as hnd.2
    simp only [List.map_cons, List.sum_cons]
    by_cases ha : a = u
    · subst ha
      have heq : (as.map fun x => if inR x then (if x = a then H else h x) + 2 else 2) =
          (as.map fun x => if inR x then h x + 2 else 2) := by
        apply List.map_congr_left
        intro x hx
        have hxa : x ≠ a := fun hEq => hnd.1 (hEq ▸ hx)
        simp [hxa]
      rw [heq]
      cases hin : inR a
      · simp
      · simp; omega
    · simp only [ha, ↓reduceIte]
      omega

private lemma pruningInv_with_steps {cfg : PruneCfg} {s : PruneState} (h : PruningInv cfg s)
    (steps' : ℕ) : PruningInv cfg { s with steps := steps' } :=
  { inR_sub := h.inR_sub
    not_inR_B := h.not_inR_B
    h_lt_H := h.h_lt_H
    cur_le := h.cur_le
    abs_le := h.abs_le
    h_pos_abs := h.h_pos_abs
    flow_cap := h.flow_cap
    h_edge := h.h_edge
    cur_no_adm := h.cur_no_adm
    cur_zero_of_abs_lt := h.cur_zero_of_abs_lt
    flow_balance := h.flow_balance
    degR_eq := h.degR_eq
    degR_peel := h.degR_peel
    active_cov := h.active_cov
    active_mem_inActive := h.active_mem_inActive
    active_nodup := h.active_nodup
    active_sub := h.active_sub
    no_ex_isolated := h.no_ex_isolated }

private lemma pot_with_steps (cfg : PruneCfg) (s : PruneState) (steps' : ℕ) :
    pot cfg { s with steps := steps' } = pot cfg s := rfl

lemma freezeStepWith_inv_pot {cfg : PruneCfg} (hcfg : cfg.Valid) {s : PruneState}
    (hinv : PruningInv cfg s) {u : ℕ} (huR : s.inR u = true) (hexPos : 0 < s.ex u)
    (habs : s.abs u = cfg.degX u) (hcurEnd : s.cur u = (cfg.incEdges u).length)
    (huH : s.h u + 1 = cfg.H) {remList : List ℕ}
    (hrem_head : remList.head? = some u)
    (hrem_nodup : remList.Nodup)
    (hrem_mem : ∀ x, x ∈ remList ↔
      x ∈ cfg.X.filter fun y => s.inR y && decide (pickLevel cfg s.inR (fun z => if z = u then cfg.H else s.h z) + 1 ≤ (if y = u then cfg.H else s.h y))) :
    let s' := freezeStepWith cfg u remList s
    PruningInv cfg s' ∧
    s'.steps + pot cfg s' ≤ s.steps + pot cfg s ∧
    pot cfg s' < pot cfg s ∧
    volPminusB cfg s' + 2 * cfg.C_cap * cutPR cfg s' ≤
      volPminusB cfg s + 2 * cfg.C_cap * cutPR cfg s := by
  have huX : u ∈ cfg.X := hinv.inR_sub u huR
  have hinc_pos : 1 ≤ (cfg.incEdges u).length := by
    by_contra h0
    have hlen0 : (cfg.incEdges u).length = 0 := by omega
    have hno := (hinv.no_ex_isolated u hlen0).1
    omega
  have hdeg_pos : 1 ≤ cfg.degX u := le_trans hinc_pos (incEdges_length_le_degX cfg u)
  set hTmp : ℕ → ℕ := fun x => if x = u then cfg.H else s.h x
  set lvl : ℕ := pickLevel cfg s.inR hTmp
  have hlvl := pickLevel_spec hcfg s.inR hTmp ⟨u, huX, huR, by simp [hTmp], hdeg_pos⟩
  set A : Finset ℕ := cfg.X.filter fun y => s.inR y && decide (lvl + 1 ≤ hTmp y)
  have huA : u ∈ A := by
    simp only [A, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq, hTmp, ↓reduceIte]
    exact ⟨huX, huR, by omega⟩
  set sMid : PruneState := { s with h := hTmp, cur := fun x => if x = u then 0 else s.cur x }
  have hMid_sw : SweepInv cfg A sMid :=
    freezeStep_sweep_inv hinv huR hexPos habs hcurEnd huH hlvl.2.1
  have hrem_inR : ∀ a ∈ remList, sMid.inR a = true := by
    intro a ha
    have haA : a ∈ A := (hrem_mem a).mp ha
    exact (Bool.and_eq_true _ _ |>.mp (Finset.mem_filter.mp haA).2).1
  have hrem_hLt : ∀ x, sMid.inR x = true → sMid.h x < cfg.H ∨ remList.head? = some x := by
    intro x hxR
    by_cases hxu : x = u
    · subst hxu; exact Or.inr hrem_head
    · exact Or.inl (by simp only [sMid, hTmp, hxu, ↓reduceIte]; exact hinv.h_lt_H x hxR)
  have hf := foldl_removeOneFromR_inv hcfg remList A sMid hrem_nodup hrem_inR hMid_sw hrem_hLt
  set s1 := remList.foldl (fun st a => removeOneFromR cfg a st) sMid
  set volEA := (remList.map fun a => (cfg.incEdges a).length).sum
  set s' : PruneState := freezeStepWith cfg u remList s
  have hA_diff : A \ remList.toFinset = ∅ := by
    ext x
    simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.notMem_empty, iff_false, not_and, not_not]
    exact (hrem_mem x).mpr
  have hs1_inv : PruningInv cfg s1 := by
    rw [pruningInv_iff_sweepInv_empty]
    simpa only [hA_diff] using hf.1
  have hs'_inv : PruningInv cfg s' := pruningInv_with_steps hs1_inv _
  have hu_mem_rem : u ∈ remList := (hrem_mem u).mpr huA
  have hvolEA_pos : 1 ≤ volEA := by
    have hmem_map : (cfg.incEdges u).length ∈ remList.map fun a => (cfg.incEdges a).length :=
      List.mem_map_of_mem hu_mem_rem
    have hle : (cfg.incEdges u).length ≤ volEA := List.le_sum_of_mem hmem_map
    omega
  have hrel_Mid : relabelCurRem cfg sMid ≤ relabelCurRem cfg s := by
    unfold relabelCurRem
    apply Finset.sum_le_sum
    intro x _
    by_cases hxu : x = u
    · subst hxu
      simp only [sMid, hTmp, ↓reduceIte, huR, Bool.true_and]
      by_cases hd0 : 0 < (cfg.incEdges x).length
      · simp only [decide_eq_true hd0, ↓reduceIte, hcurEnd, Nat.sub_self, Nat.zero_mul,
          Nat.zero_add]
        have hHu : cfg.H - s.h x = 1 := by omega
        rw [hHu]
        omega
      · simp [hd0]
    · simp [sMid, hTmp, hxu]
  have hphi_Mid : phiActive sMid ≤ phiActive s + 1 := by
    unfold phiActive
    exact phiActive_update_h_le u s.inR s.h cfg.H (by omega) s.active hinv.active_nodup
  have hsteps' : s'.steps = s.steps + cfg.H + volEA := rfl
  have hvol' : volR cfg s' + volEA = volR cfg s := by
    change volR cfg s1 + volEA = volR cfg sMid
    exact hf.2.2.1
  have hrel' : relabelCurRem cfg s' ≤ relabelCurRem cfg s :=
    le_trans hf.2.2.2.1 hrel_Mid
  have habs' : sumAbsRem cfg s' ≤ sumAbsRem cfg s := hf.2.2.2.2.1
  have hplen' : s'.peelQ.length ≤ s.peelQ.length + volEA := hf.2.2.2.2.2.2.2.1
  have hphi' : phiActive s' ≤ phiActive s + 1 + volEA * (cfg.H + 1) := by
    have h1 := hf.2.2.2.2.2.2.2.2.1
    change phiActive s1 ≤ phiActive sMid + volEA * (cfg.H + 1) at h1
    change phiActive s1 ≤ phiActive s + 1 + volEA * (cfg.H + 1)
    omega
  have hpot := freezeStep_pot_le cfg s s' volEA (PruneCfg.valid_three_le_H hcfg) hvolEA_pos
    hsteps' hvol' hrel' habs' hplen' (by omega)
  have hpot1 : s'.steps + pot cfg s' ≤ s.steps + pot cfg s := by
    simpa only [pot_with_steps] using hpot.1
  have hpot2 : pot cfg s' < pot cfg s := by
    simpa only [pot_with_steps] using hpot.2
  have horig := freezeStep_inv_pot hcfg hinv huR hexPos habs hcurEnd huH
  set sOrig := freezeStep cfg u s
  set AListOrig := cfg.X.toList.filter fun x => s.inR x && decide (lvl + 1 ≤ hTmp x)
  set remOrig := u :: AListOrig.erase u
  have hremO_mem : ∀ x, x ∈ remOrig ↔ x ∈ A := by
    intro x
    simp only [remOrig, AListOrig, A, List.mem_cons, Finset.mem_filter, Bool.and_eq_true,
      decide_eq_true_eq]
    constructor
    · rintro (rfl | hx)
      · exact ⟨huX, huR, by simp [hTmp]; omega⟩
      · have hxF := (List.mem_filter.mp (List.mem_of_mem_erase hx)).2
        have hxX := Finset.mem_toList.mp (List.mem_filter.mp (List.mem_of_mem_erase hx)).1
        exact ⟨hxX, Bool.and_eq_true _ _ |>.mp hxF |>.1,
          decide_eq_true_eq.mp (Bool.and_eq_true _ _ |>.mp hxF |>.2)⟩
    · intro hxA
      by_cases hxu : x = u
      · exact Or.inl hxu
      · right
        apply (List.mem_erase_of_ne hxu).mpr
        rw [List.mem_filter]
        exact ⟨Finset.mem_toList.mpr hxA.1, by simp [hxA.2.1, hxA.2.2]⟩
  have hremO_nodup : remOrig.Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, (Finset.nodup_toList cfg.X |>.filter _).erase _⟩
    exact List.Nodup.not_mem_erase ((Finset.nodup_toList cfg.X).filter _)
  have hremO_inR : ∀ a ∈ remOrig, sMid.inR a = true := fun a ha => by
    have haA := (hremO_mem a).mp ha
    exact (Bool.and_eq_true _ _ |>.mp (Finset.mem_filter.mp haA).2).1
  have hremO_hLt : ∀ x, sMid.inR x = true → sMid.h x < cfg.H ∨ remOrig.head? = some x := by
    intro x hxR
    by_cases hxu : x = u
    · subst hxu; exact Or.inr rfl
    · exact Or.inl (by simp only [sMid, hTmp, hxu, ↓reduceIte]; exact hinv.h_lt_H x hxR)
  have hfO := foldl_removeOneFromR_inv hcfg remOrig A sMid hremO_nodup hremO_inR hMid_sw hremO_hLt
  have hinR_eq : ∀ x, s'.inR x = sOrig.inR x := fun x => by
    have h1 := hf.2.1 x
    have h2 := hfO.2.1 x
    change s1.inR x = (sMid.inR x && !(x ∈ remList)) at h1
    change sOrig.inR x = (sMid.inR x && !(x ∈ remOrig)) at h2
    have hmemEq : decide (x ∈ remList) = decide (x ∈ remOrig) := by
      simp only [decide_eq_decide]
      exact (hrem_mem x).trans (hremO_mem x).symm
    change s1.inR x = sOrig.inR x
    rw [h1, h2]
    by_cases hm : x ∈ remList
    · have hmO : x ∈ remOrig := (hremO_mem x).mpr ((hrem_mem x).mp hm)
      simp [hm, hmO]
    · have hmO : x ∉ remOrig := fun h => hm ((hrem_mem x).mpr ((hremO_mem x).mp h))
      simp [hm, hmO]
  have hvolP_eq : volPminusB cfg s' = volPminusB cfg sOrig := by
    unfold volPminusB
    apply Finset.sum_congr rfl
    intro x _
    rw [hinR_eq x]
  have hcut_eq : cutPR cfg s' = cutPR cfg sOrig := by
    unfold cutPR
    congr 1
    apply List.filter_congr
    intro e _
    rw [hinR_eq e.1, hinR_eq e.2]
  refine ⟨hs'_inv, hpot1, hpot2, ?_⟩
  rw [hvolP_eq, hcut_eq]
  exact horig.2.2.2

/-- Invariant preserving `peelQ.Nodup`, `peelQ ⊆ cfg.X`, and `degR < θ_out_nat` on `peelQ`. -/
@[expose] def PeelQInv (cfg : PruneCfg) (s : PruneState) : Prop :=
  s.peelQ.Nodup ∧ (∀ x ∈ s.peelQ, x ∈ cfg.X) ∧ (∀ x ∈ s.peelQ, s.degR x < cfg.θ_out_nat)

private lemma list_erase_append_right {α : Type*} [BEq α] [LawfulBEq α]
    {x : α} : ∀ {l1 l2 : List α}, x ∉ l1 → (l1 ++ x :: l2).erase x = l1 ++ l2
  | [], l2, _ => by simp [List.erase_cons_head]
  | a :: as, l2, hnot => by
    have hne : a ≠ x := fun h => hnot (h ▸ List.mem_cons_self)
    have hbeq : (a == x) = false := beq_false_of_ne hne
    change (a :: (as ++ x :: l2)).erase x = a :: (as ++ l2)
    rw [List.erase_cons, hbeq]
    simp only [Bool.false_eq_true, ↓reduceIte, List.cons.injEq, true_and]
    exact list_erase_append_right (fun h => hnot (List.mem_cons_of_mem _ h))

private lemma foldl_removeEdgeStep_peelQ_pop (cfg : PruneCfg) (flow : ℕ → ℤ)
    (inR' : ℕ → Bool) {v : ℕ} (hv : inR' v = false) :
    ∀ (L : List (ℕ × Bool × ℕ)) (st : PruneState) (pref rest : List ℕ),
      v ∉ pref → st.peelQ = pref ++ v :: rest →
      let st2 : PruneState := { st with peelQ := pref ++ rest }
      let r1 := L.foldl (removeEdgeStep cfg flow inR') st
      let r2 := L.foldl (removeEdgeStep cfg flow inR') st2
      r1.inR = r2.inR ∧ r1.h = r2.h ∧ r1.cur = r2.cur ∧ r1.abs = r2.abs ∧
      r1.ex = r2.ex ∧ r1.degR = r2.degR ∧ r1.flow = r2.flow ∧ r1.active = r2.active ∧
      r1.inActive = r2.inActive ∧ r1.steps = r2.steps ∧
      ∃ pref', v ∉ pref' ∧ r1.peelQ = pref' ++ v :: rest ∧ r2.peelQ = pref' ++ rest
  | [], st, pref, rest, hnot, hq => by
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, pref, hnot, hq, rfl⟩
  | p :: ps, st, pref, rest, hnot, hq => by
    dsimp only [List.foldl_cons]
    set st2 : PruneState := { st with peelQ := pref ++ rest }
    have hstep :
        let s1' := removeEdgeStep cfg flow inR' st p
        let s2' := removeEdgeStep cfg flow inR' st2 p
        s1'.inR = s2'.inR ∧ s1'.h = s2'.h ∧ s1'.cur = s2'.cur ∧ s1'.abs = s2'.abs ∧
        s1'.ex = s2'.ex ∧ s1'.degR = s2'.degR ∧ s1'.flow = s2'.flow ∧ s1'.active = s2'.active ∧
        s1'.inActive = s2'.inActive ∧ s1'.steps = s2'.steps ∧
        ∃ pref1, v ∉ pref1 ∧ s1'.peelQ = pref1 ++ v :: rest ∧ s2'.peelQ = pref1 ++ rest := by
      unfold removeEdgeStep
      by_cases hw : inR' p.2.2 = true
      · simp only [hw, ↓reduceIte]
        have hwne : p.2.2 ≠ v := fun h => by rw [h, hv] at hw; exact Bool.false_ne_true hw
        by_cases hpq : (decide (st.degR p.2.2 = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat)) = true
        · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, p.2.2 :: pref, ?_, ?_, ?_⟩
          · intro hmem
            rcases List.mem_cons.mp hmem with hEq | hmem
            · exact hwne hEq.symm
            · exact hnot hmem
          · simp only [hpq, ↓reduceIte]; rw [hq, List.cons_append]
          · simp only [hpq, ↓reduceIte, st2, List.cons_append]
        · have hpq' : decide (st.degR p.2.2 = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat) = false :=
            Bool.eq_false_iff.mpr hpq
          refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, pref, hnot, ?_, ?_⟩
          · simp only [hpq', Bool.false_eq_true, ↓reduceIte, hq]
          · simp only [hpq', Bool.false_eq_true, ↓reduceIte, st2]
      · simp only [hw]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, pref, hnot, hq, rfl⟩
    rcases hstep with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, pref1, hnot1, hq1, hq2⟩
    have hs2_eq : removeEdgeStep cfg flow inR' st2 p =
        { removeEdgeStep cfg flow inR' st p with peelQ := pref1 ++ rest } := by
      cases hs1 : removeEdgeStep cfg flow inR' st p
      cases hs2 : removeEdgeStep cfg flow inR' st2 p
      simp only [hs1, hs2] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hq2
      subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7; subst h8; subst h9; subst h10; subst hq2
      rfl
    rw [hs2_eq]
    exact foldl_removeEdgeStep_peelQ_pop cfg flow inR' hv ps _ pref1 rest hnot1 hq1

/-- When `s.peelQ = v :: rest` and `peelStep` removes `v`, it agrees with popping `v` first
and then calling `removeOneFromR cfg v { s with peelQ := rest }`. -/
lemma peelStep_eq_pop_first {cfg : PruneCfg} {s : PruneState} {v : ℕ} {rest : List ℕ}
    (hq : s.peelQ = v :: rest)
    (hcond : (s.inR v && decide (s.degR v < cfg.θ_out_nat)) = true) :
    let s2 := removeOneFromR cfg v { s with peelQ := rest }
    peelStep cfg v rest s =
      { s2 with steps := s.steps + 1 + (cfg.incEdges v).length } := by
  simp only [peelStep, hcond, ↓reduceIte, removeOneFromR]
  set inR' : ℕ → Bool := fun x => if x = v then false else s.inR x
  set s0 : PruneState :=
    { inR := inR', h := s.h, cur := s.cur, abs := s.abs, ex := s.ex,
      degR := s.degR, flow := s.flow, active := s.active, inActive := s.inActive,
      peelQ := s.peelQ, steps := s.steps }
  have hv_inR : inR' v = false := by simp [inR']
  have hpop := @foldl_removeEdgeStep_peelQ_pop cfg s.flow inR' v hv_inR
    (cfg.incEdges v) s0 [] rest (by simp) (by simp only [s0, hq, List.nil_append])
  dsimp only at hpop
  rcases hpop with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _, pref', hnot', hp1, hp2⟩
  set r1 := (cfg.incEdges v).foldl (removeEdgeStep cfg s.flow inR') s0
  set r2 := (cfg.incEdges v).foldl (removeEdgeStep cfg s.flow inR')
    { s0 with peelQ := [] ++ rest }
  have hp_erase : r1.peelQ.erase v = r2.peelQ := by
    rw [hp1, hp2]
    exact list_erase_append_right hnot'
  change { r1 with peelQ := r1.peelQ.erase v, steps := s.steps + 1 + (cfg.incEdges v).length } =
    { r2 with steps := s.steps + 1 + (cfg.incEdges v).length }
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, hp_erase]

private lemma foldl_removeEdgeStep_peelQInv (cfg : PruneCfg) (flow : ℕ → ℤ) (inR' : ℕ → Bool)
    (hinX : ∀ x, inR' x = true → x ∈ cfg.X) :
    ∀ (L : List (ℕ × Bool × ℕ)) (st : PruneState),
      PeelQInv cfg st → PeelQInv cfg (L.foldl (removeEdgeStep cfg flow inR') st)
  | [], st, hinv => hinv
  | p :: ps, st, hinv => by
    apply foldl_removeEdgeStep_peelQInv cfg flow inR' hinX ps
    unfold removeEdgeStep
    by_cases hw : inR' p.2.2 = true
    · simp only [hw, ↓reduceIte]
      have hdeg_le : ∀ x, (if x = p.2.2 then st.degR p.2.2 - 1 else st.degR x) ≤ st.degR x := by
        intro x; by_cases hx : x = p.2.2 <;> simp [hx]
      by_cases hpq : decide (st.degR p.2.2 = cfg.θ_out_nat ∧ 0 < cfg.θ_out_nat) = true
      · simp only [hpq, ↓reduceIte]
        have hspec := decide_eq_true_eq.mp hpq
        have hnot_mem : p.2.2 ∉ st.peelQ := fun hmem => by
          have hlt := hinv.2.2 p.2.2 hmem
          omega
        refine ⟨List.nodup_cons.mpr ⟨hnot_mem, hinv.1⟩, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hinX _ hw
          · exact hinv.2.1 x hx
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · simp only [↓reduceIte]; omega
          · exact lt_of_le_of_lt (hdeg_le x) (hinv.2.2 x hx)
      · simp only [hpq]
        refine ⟨hinv.1, hinv.2.1, fun x hx => lt_of_le_of_lt (hdeg_le x) (hinv.2.2 x hx)⟩
    · simp only [hw]
      exact hinv

private lemma foldl_removeEdgeStep_inR' (cfg : PruneCfg) (flow : ℕ → ℤ) (inR' : ℕ → Bool) :
    ∀ (L : List (ℕ × Bool × ℕ)) (st : PruneState) (x : ℕ),
      (L.foldl (removeEdgeStep cfg flow inR') st).inR x = st.inR x
  | [], _, _ => rfl
  | p :: ps, st, x => by
    dsimp only [List.foldl_cons]
    rw [foldl_removeEdgeStep_inR']
    unfold removeEdgeStep
    by_cases hw : inR' p.2.2 = true <;> simp [hw]

lemma removeOneFromR_peelQInv {cfg : PruneCfg} {a : ℕ} {st : PruneState}
    (hinX : ∀ x, st.inR x = true → x ∈ cfg.X) (hpq : PeelQInv cfg st) :
    PeelQInv cfg (removeOneFromR cfg a st) := by
  apply foldl_removeEdgeStep_peelQInv cfg st.flow (fun x => if x = a then false else st.inR x)
  · intro x hx
    by_cases hxa : x = a
    · simp [hxa] at hx
    · simp only [hxa, ↓reduceIte] at hx
      exact hinX x hx
  · exact hpq

lemma foldl_removeOneFromR_peelQInv {cfg : PruneCfg} :
    ∀ (L : List ℕ) (st : PruneState),
      (∀ x, st.inR x = true → x ∈ cfg.X) → PeelQInv cfg st →
      PeelQInv cfg (L.foldl (fun s a => removeOneFromR cfg a s) st)
  | [], _, _, hpq => hpq
  | a :: as, st, hinX, hpq => by
    apply foldl_removeOneFromR_peelQInv as
    · intro x hx
      have hinR' : (removeOneFromR cfg a st).inR x = (if x = a then false else st.inR x) := by
        unfold removeOneFromR
        exact foldl_removeEdgeStep_inR' _ _ _ _ _ x
      rw [hinR'] at hx
      by_cases hxa : x = a
      · simp [hxa] at hx
      · simp only [hxa, ↓reduceIte] at hx; exact hinX x hx
    · exact removeOneFromR_peelQInv hinX hpq

lemma peelStep_peelQInv {cfg : PruneCfg} {s : PruneState} {v : ℕ} {rest : List ℕ}
    (hinX : ∀ x, s.inR x = true → x ∈ cfg.X) (hpq : PeelQInv cfg s) (hq : s.peelQ = v :: rest) :
    PeelQInv cfg (peelStep cfg v rest s) := by
  have hrest_inv : PeelQInv cfg { s with peelQ := rest } := by
    have hnd : (v :: rest).Nodup := hq ▸ hpq.1
    exact ⟨(List.nodup_cons.mp hnd).2,
      fun x hx => hpq.2.1 x (hq ▸ List.mem_cons_of_mem _ hx),
      fun x hx => hpq.2.2 x (hq ▸ List.mem_cons_of_mem _ hx)⟩
  by_cases hcond : (s.inR v && decide (s.degR v < cfg.θ_out_nat)) = true
  · rw [peelStep_eq_pop_first hq hcond]
    exact removeOneFromR_peelQInv hinX hrest_inv
  · simp only [peelStep, hcond]
    exact hrest_inv

lemma freezeStepWith_peelQInv {cfg : PruneCfg} {s : PruneState} {u : ℕ} {remList : List ℕ}
    (hinX : ∀ x, s.inR x = true → x ∈ cfg.X) (hpq : PeelQInv cfg s) :
    PeelQInv cfg (freezeStepWith cfg u remList s) :=
  foldl_removeOneFromR_peelQInv remList _ hinX hpq



end

end MinCostFlow.Expander
