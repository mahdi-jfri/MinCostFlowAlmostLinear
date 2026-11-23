module

public import MinCostFlow.SparseCore.Program.TourOpsEditInsertCore
import Mathlib.Tactic

/-!
# Single-edit handler for `insertBefore` (Op 0)

Verifies `tourEditInsertBody_runs`, combining `tourEditInsertBody_runs_empty` (when `s.ord v = []`)
with the nonempty-vertex splice, optional head/root update, and `tourEditInsert_nonempty_core`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

private theorem runs_call_regs7 {w : ℕ} {p : Program} {ω : ℕ → Bool} (r : ℕ) {f : ℕ}
    (r0 r1 r2 r3 r4 r5 r6 : ℕ) {st st₁ : State} {v0 v1 v2 v3 v4 v5 v6 : ℕ} {body : Stmt}
    {o₁ : Outcome} {c₁ : ℕ} (hget : p.procs[f]? = some body)
    (h0 : st.regs r0 = v0) (h1 : st.regs r1 = v1) (h2 : st.regs r2 = v2) (h3 : st.regs r3 = v3)
    (h4 : st.regs r4 = v4) (h5 : st.regs r5 = v5) (h6 : st.regs r6 = v6)
    (hrun : Runs w p ω body (startState [v0, v1, v2, v3, v4, v5, v6] st.mem st.pos) o₁ st₁ c₁) :
    Runs w p ω (.call r f [.reg r0, .reg r1, .reg r2, .reg r3, .reg r4, .reg r5, .reg r6]) st .normal
      { st₁ with regs := Function.update st.regs r o₁.value } (8 + c₁) := by
  have h := tour_runs_call_of (r := r) (args := [.reg r0, .reg r1, .reg r2, .reg r3, .reg r4, .reg r5, .reg r6]) hget
    (by simp [evalArgs, Expr.eval, h0, h1, h2, h3, h4, h5, h6]) hrun
  convert h using 1; simp [argsSize, Expr.size]; omega

/-- Verified amortized run theorem for `tourEditInsertBody [b, v, keyX, yWord, heap]`. -/
theorem tourEditInsertBody_runs {τ_ord : Type}
    {w vCap eCap b v keyX yWord heap pos : ℕ} {p : Program}
    (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem)
    (hkeyLt : keyX < 2 * eCap)
    (hedit : TourEditValid vCap eCap s
      (.insertBefore v (endOfKey keyX) (if yWord = 0 then none else some (endOfKey (yWord - 1)))))
    (hord_le : ordHandleOf b vCap eCap ≤ heap) (hroom : heap + 2 < 2 ^ w)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 18 ≤ 2 ^ w) (hzero : ZeroFrom mem heap) :
    let yOpt : Option End := if yWord = 0 then none else some (endOfKey (yWord - 1))
    let s' := tourApplyEdit s (.insertBefore v (endOfKey keyX) yOpt)
    ∃ (st' : State) (c : ℕ) (x' : TourConcrete τ_ord),
      Runs w p ω (tourEditInsertBody C.initNode C.insertBefore C.setValNode C.rotateFront)
        (startState [b, v, keyX, yWord, heap] mem pos) (.returned heap) st' c ∧
      x'.ordX = x.ordX ∧
      ZeroFrom st'.mem heap ∧
      (∀ a, (a < b ∨ ordHandleOf b vCap eCap ≤ a) → a < heap → st'.mem a = mem a) ∧
      TourCoreAt vCap eCap b s' x' st'.mem ∧
      c + TOUR_PHI_MULT * forestPhi x'.trees ≤
        TOUR_PHI_MULT * forestPhi x.trees + TOUR_EDIT_SIMPLE_MUL * tourLog eCap := by
  intro yOpt s'
  have hvLt : v < vCap := hedit.1
  have hvF : v ∈ s.rf.F.V := hedit.2.1
  have hxOpen : (endOfKey keyX).1 ∉ s.rf.F.E := hedit.2.2.2.1
  have hxFresh : ∀ w', endOfKey keyX ∉ s.ord w' := hedit.2.2.2.2.1
  have hyWord_le : yWord ≤ 2 * eCap := by
    by_cases hy0 : yWord = 0
    · omega
    · have hylt := hedit.2.2.2.2.2 (endOfKey (yWord - 1)) (by simp [hy0])
      have := key_lt_two_mul_of_endOfKey hylt; omega
  have hvalid' : TourValid vCap eCap s' := tourValid_applyEdit_insertBefore h.valid hedit
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hlog : Nat.log 2 (2 * eCap + 2) + 1 ≤ 2 * tourLog eCap := tourLog_double_le eCap
  have hord'_mem : ∀ w' z, z ∈ s'.ord w' ↔ (w' = v ∧ z = endOfKey keyX) ∨ z ∈ s.ord w' := by
    intro w' z; by_cases hwv : w' = v
    · subst hwv; simp only [s', tourApplyEdit, applyOrdEdit, Function.update_self, insertBeforeList, true_and]
      cases yOpt with
      | none => simp [or_comm]
      | some y' =>
        have htd := List.take_append_drop ((s.ord w').idxOf y') (s.ord w')
        simp only [List.mem_append, List.mem_cons]
        constructor
        · rintro (h1 | rfl | h2)
          · exact Or.inr (List.mem_of_mem_take h1)
          · exact Or.inl rfl
          · exact Or.inr (List.mem_of_mem_drop h2)
        · rintro (rfl | hz)
          · exact Or.inr (Or.inl rfl)
          · rw [← htd, List.mem_append] at hz; rcases hz with h1 | h2; exact Or.inl h1; exact Or.inr (Or.inr h2)
    · simp [s', tourApplyEdit, applyOrdEdit, hwv]
  have hxNotMarked : endOfKey keyX ∉ s.marked := fun hm => by
    obtain ⟨⟨w', hw'⟩, _⟩ := h.valid.marked_open _ hm; exact hxFresh w' hw'
  -- Step 1: allocate/reuse `u` and initialize singleton
  by_cases hnil : s.ord v = []
  · exact tourEditInsertBody_runs_empty C ω h hkeyLt hedit hord_le hroom hw hwide hzero hnil
  -- Nonempty vertex (`s.ord v ≠ []`): allocate/reuse `u` and initialize singleton
  obtain ⟨u, nn1, nodeOf1, keyOf1, s1, trees1, mem1, r1, pos1, c1,
    hu1, hunn, hnn_le, hn1k, hk1u, hn1_ne, hk1_old, hn1_mem, hn1_ko, hk1_mem, hhdr1, hn1, hinv1, hphi1,
    hexact1, ht1_sub, ht1_mem, hs1u, hs1ne, hfr1_in, hfr1_out,
    hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hr19, hr110, hr111, hr112, hr113,
    hc1, hrun1⟩ :=
    tourEditInsert_alloc_exec (yWord := yWord) (pos := pos) C ω h hvLt hkeyLt (by omega) hxFresh hord_le hroom hw hwide
  have hmem1_fixed_eq : ∀ a, a < nodesBase b vCap eCap →
      a ≠ b + HDR_NUM_NODES → a ≠ nodeOfEndBase b vCap + keyX → a ≠ keyOfNodeBase b vCap eCap + u →
      mem1 a = mem a := fun a hlt h1 h2 h3 => by
    by_cases hba : b ≤ a
    · exact hfr1_in a hba (by simp [nodesBase, ordHandleOf, tourFixedSize] at hlt ⊢; omega) h1 h2 h3
        (fun i _ => by omega)
    · exact hfr1_out a (Or.inl (by omega))
  have hzero1 : ZeroFrom mem1 heap := fun a ha => by
    rw [hfr1_out a (Or.inr (by omega))]; exact hzero a ha
  have hgeo_eo : endOwnerBase b vCap eCap + keyX < 2 ^ w ∧ x.slotOf v + 1 < 2 ^ w ∧
      firstEndBase b + v < 2 ^ w ∧ isRootBase b vCap + v < 2 ^ w ∧ b + 16 < 2 ^ w := by
    have := (h.slot_bij v hvLt).1
    simp [endOwnerBase, firstEndBase, isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
  have hsv_lt : x.slotOf v < vCap := (h.slot_bij v hvLt).1
  -- Case split on `s.ord v = []` vs `s.ord v ≠ []`
  obtain ⟨aOld, haOld⟩ : ∃ aOld, (s.ord v).head? = some aOld :=
    Option.isSome_iff_exists.mp (by cases ho : s.ord v <;> simp_all)
  have haOld_mem : aOld ∈ s.ord v := List.mem_of_head? haOld
  have haOld_lt : endKey aOld < 2 * eCap := by
    have := h.valid.ordWithin.2.2 v aOld haOld_mem; simp only [endKey]; cases aOld.2 <;> simp <;> omega
  set feOld := mem (firstEndBase b + v)
  have hfeOld_eq : feOld = x.nodeOf (endKey aOld) := by simp [feOld, h.firstEnd_mem v hvLt, haOld]
  have haOld_ne_keyX : endKey aOld ≠ keyX := fun heq => hxFresh v (by rw [← heq, endOfKey_endKey]; exact haOld_mem)
  have hfeOld_eq1 : feOld = nodeOf1 (endKey aOld) := by rw [hfeOld_eq, hn1_ne _ haOld_ne_keyX]
  have hfeOld_nz : feOld ≠ 0 := hfeOld_eq ▸ (h.active_end v hvLt aOld haOld_mem).1
  have hcond_fe : (Expr.bin .eq (.reg 9) (.const 0)).eval w ⟨mem1, r1, pos1⟩ = some 0 := by
    simp [Expr.eval, hr19, hfeOld_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]
  have heo_iff1 : ∀ k < 2 * eCap, mem1 (endOwnerBase b vCap eCap + k) = x.slotOf v + 1 ↔ endOfKey k ∈ s.ord v := by
    intro k hk
    rw [hmem1_fixed_eq _ (by simp [endOwnerBase, nodesBase]; omega) (by simp [endOwnerBase, HDR_NUM_NODES]; omega)
      (by simp [endOwnerBase, nodeOfEndBase]; omega) (by simp [endOwnerBase, keyOfNodeBase]; omega)]
    constructor
    · intro hmem_eo
      by_contra hnot
      by_cases hex : ∃ w', endOfKey k ∈ s.ord w'
      · obtain ⟨w', hw'⟩ := hex
        have hw'Lt : w' < vCap := by
          by_contra hge; have := h.valid.ordWithin.2.1 w' (Nat.le_of_not_lt hge); rw [this] at hw'; simp at hw'
        have h1 := (h.active_end w' hw'Lt (endOfKey k) hw').2
        rw [endKey_endOfKey', hmem_eo] at h1
        have hseq : x.slotOf v = x.slotOf w' := by omega
        have hvw : v = w' := by rw [← (h.slot_bij v hvLt).2.1, hseq, (h.slot_bij w' hw'Lt).2.1]
        exact hnot (hvw ▸ hw')
      · push Not at hex; rw [h.inactive_owner k hk hex] at hmem_eo; omega
    · intro hm; simpa [endKey_endOfKey'] using (h.active_end v hvLt (endOfKey k) hm).2
  have hn1_inj : ∀ k1 k2, k1 < 2 * eCap → k2 < 2 * eCap → nodeOf1 k1 ≠ 0 → nodeOf1 k1 = nodeOf1 k2 → k1 = k2 := by
    intro k1 k2 hk1 hk2 hnz heq
    have h2nz : nodeOf1 k2 ≠ 0 := heq ▸ hnz
    rw [← hn1_ko k1 hk1 hnz, heq, hn1_ko k2 hk2 h2nz]
  -- Target selection: compute `(yEnd, yNode, headCh)`
  obtain ⟨yEnd, yNode, headCh, rT, cT, hyEnd_mem, hyNode_eq, hy_target, hch_iff, hch_01,
    hrT0, hrT1, hrT2, hrT3, hrT4, hrT5, hrT6, hrT7, hrT8, hrT9, hrT10, hrT11, hrT12, hrT13,
    hcT, hrunT⟩ :=
    tourEditInsert_target_exec (p := p) (pos := pos1) ω hord_le hroom hvLt hyWord_le hsv_lt hw haOld haOld_lt hfeOld_eq1
      hhdr1.2.2.2.2.2.2.1 (fun k hk => (hn1_mem k hk).1) hn1_inj hfeOld_nz heo_iff1
      hr10 hr11 hr12 hr13 hr14 hr15 hr16 hr17 hr18 hr19 hr110 hr111
  -- Component tree `t` containing `yNode` and `feOld`
  have ⟨_, hrR, hrLt, hyLt, hy1, hy_le_old, hy_ko_old, t, rest0, hct_r, hperm_r, ht_map, hy_t⟩ :=
    h.mem_compTree_of_active hyEnd_mem
  set r := s.rf.root v
  have hyEnd_ne_keyX : endKey yEnd ≠ keyX := fun heq => hxFresh v (by rw [← heq, endOfKey_endKey]; exact hyEnd_mem)
  have hyNode_old : yNode = x.nodeOf (endKey yEnd) := by rw [hyNode_eq, hn1_ne _ hyEnd_ne_keyX]
  have hyNode_t : yNode ∈ t.toList := hyNode_old ▸ hy_t
  have ht_ne_u : t ≠ AuxTree.node u .leaf .leaf := fun heq => by
    have hu_t : u ∈ t.toList := by rw [heq]; simp [AuxTree.toList]
    -- `yNode ∈ t.toList = [u]`, so `yNode = u`, contradiction with `yEnd ∈ s.ord v` vs `x` fresh
    rw [heq] at hyNode_t; simp [AuxTree.toList] at hyNode_t
    have hkeq : keyOf1 yNode = endKey yEnd := by
      rw [hyNode_eq]; exact hn1_ko _ hyLt (by rw [← hyNode_eq, hyNode_old]; omega)
    rw [hyNode_t, hk1u] at hkeq; exact hyEnd_ne_keyX hkeq.symm
  have ht_in_t1 : t ∈ trees1 := ht1_mem t (hperm_r.mem_iff.mpr (by simp)) ht_ne_u
  set rest1 := trees1.erase t
  have hperm_t1 : trees1.Perm (t :: rest1) := List.perm_cons_erase ht_in_t1
  have hperm_u : (AuxTree.node u .leaf .leaf :: trees1).Perm (AuxTree.node u .leaf .leaf :: t :: rest1) :=
    hperm_t1.cons _
  have hinv1_p : TourForestInv nn1 s1 (AuxTree.node u .leaf .leaf :: t :: rest1) :=
    (hinv1.perm hperm_u).1
  have hvals1 : TourValsOk w nn1 s1 := by
    have hv0 := h.valsOk hw
    refine ⟨by omega, fun id hid => ?_⟩
    by_cases hiu : id = u
    · subst hiu; simp [hs1u, tourSingletonNode]
    · rw [hs1ne id hiu]
      by_cases hle : id ≤ x.numNodes
      · exact hv0.2 id hle
      · exfalso
        have hmem_nn : id ∈ (AuxTree.node u .leaf .leaf :: trees1).flatMap AuxTree.toList :=
          (hexact1 id).mpr ⟨by omega, hid⟩
        simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.cons_append, List.mem_cons] at hmem_nn
        rcases hmem_nn with rfl | hrest
        · exact hiu rfl
        · obtain ⟨tr, htr, htrm⟩ := List.mem_flatMap.mp hrest
          have := (h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨tr, (ht1_sub tr htr).1, htrm⟩)
          omega
  have hheap1 : HeapOk tourLayout w (nodesBase b vCap eCap) nn1 heap 2 mem1 :=
    ⟨by simp [NodeLayout.nodeAddr, tourLayout_stride, nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega, hroom, hzero1, by omega⟩
  -- Call `tourInsertBeforeBody [nb, u, yNode, fuel, heap]`
  obtain ⟨t₂, s₂, o₂, st₂, c₂, P, Q, hrun₂, _, hn₂, hfr₂, hinv₂, hvals₂, hne₂, _, ht_PQ, ht₂_PQ,
    hval₂, hout₂, hcost₂⟩ :=
    tourInsertBeforeBody_runs (fuel := 2 * eCap + 2) (pos := pos1) C.toTourSplayOpsProcs ω hn1 hinv1_p hvals1 hyNode_t
      (by omega) (by omega) hheap1
  have hcall_ib := runs_call_regs5 14 10 6 12 11 4 (st := ⟨mem1, rT, pos1⟩) C.insertBefore_body
    hrT10 hrT6 hrT12 hrT11 hrT4 hrun₂
  set rIB := Function.update rT 14 o₂.value
  -- Read `isRoot[v]`
  have hm2_pre : ∀ a < nodesBase b vCap eCap, st₂.mem a = mem1 a := fun a ha =>
    hfr₂.2 a (by simp [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega)
      (fun hrec => by have := (inRecords_lt_ordHandle_of_le hnn_le hrec).1; omega)
  have hm2_irb : st₂.mem (b + HDR_IS_ROOT) = isRootBase b vCap := by
    rw [hm2_pre _ (by simp [HDR_IS_ROOT, nodesBase]; omega)]; exact hhdr1.2.2.2.2.2.1
  set irV := if v ∈ s.rf.R then 1 else 0
  have hm2_irv : st₂.mem (isRootBase b vCap + v) = irV := by
    rw [hm2_pre _ (by simp [isRootBase, nodesBase]; omega),
      hmem1_fixed_eq _ (by simp [isRootBase, nodesBase]; omega) (by simp [isRootBase, HDR_NUM_NODES]; omega)
        (by simp [isRootBase, nodeOfEndBase]; omega) (by simp [isRootBase, keyOfNodeBase]; omega)]
    exact h.isRoot_mem v hvLt
  set rIR1 := Function.update rIB 14 (isRootBase b vCap)
  set rIR2 := Function.update rIR1 14 irV
  have hIR1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 0) (off := HDR_IS_ROOT)
    (b := b) (val := isRootBase b vCap) (st := { st₂ with regs := rIB })
    (by simp [rIB, hrT0]) (by simp [HDR_IS_ROOT]; omega) (by simp [HDR_IS_ROOT]; omega) hm2_irb
  have hIR2 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 14) (rIdx := 1)
    (base := isRootBase b vCap) (idx := v) (val := irV) (st := { st₂ with regs := rIR1 })
    (by simp [rIR1]) (by simp [rIR1, rIB, hrT1]) hgeo_eo.2.2.2.1 hm2_irv
  -- Key Euler-tour rotation fact from `fullTour_insertOpen`:
  have ht₂_isRot : (t₂.toList.map fun id => endOfKey (keyOf1 id)).IsRotated
      (fullTour s'.ord s'.rf.F hvalid'.compat.forest r) := by
    have hf_eq_old : ∀ id ∈ t.toList, keyOf1 id = x.keyOf id := fun id hid => by
      have h1 := (h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨t, hperm_r.mem_iff.mpr (by simp), hid⟩)
      exact hk1_old id h1.1 h1.2
    have hPQ_map : (P.map fun id => endOfKey (keyOf1 id)) ++ yEnd :: (Q.map fun id => endOfKey (keyOf1 id)) =
        fullTour s.ord s.rf.F h.valid.compat.forest r := by
      rw [← ht_map, ht_PQ]
      have h1 : (P ++ yNode :: Q).map (fun id => endOfKey (keyOf1 id)) =
          (P ++ yNode :: Q).map (fun id => endOfKey (x.keyOf id)) :=
        List.map_congr_left fun id hid => by rw [hf_eq_old id (ht_PQ ▸ hid)]
      rw [← h1]; simp [List.map_append, hyNode_eq, hn1_ko _ hyLt (by rw [← hyNode_eq, hyNode_old]; omega), endOfKey_endKey]
    have hrot_v : ((P.map fun id => endOfKey (keyOf1 id)) ++ yEnd :: (Q.map fun id => endOfKey (keyOf1 id))).IsRotated
        (fullTour s.ord s.rf.F h.valid.compat.forest v) := by
      rw [hPQ_map]
      exact fullTour_isRotated_of_connected h.valid.compat (connected_symm (h.valid.root_spec hvF).2)
    have hins := fullTour_insertOpen h.valid.compat hvF hxFresh hxOpen hyEnd_mem hy_target hrot_v
    have hrot_r : (fullTour s'.ord s'.rf.F hvalid'.compat.forest v).IsRotated
        (fullTour s'.ord s'.rf.F hvalid'.compat.forest r) :=
      fullTour_isRotated_of_connected hvalid'.compat (h.valid.root_spec hvF).2
    have ht₂_m : t₂.toList.map (fun id => endOfKey (keyOf1 id)) =
        (P.map fun id => endOfKey (keyOf1 id)) ++ endOfKey keyX :: yEnd :: (Q.map fun id => endOfKey (keyOf1 id)) := by
      rw [ht₂_PQ]; simp [List.map_append, hk1u, hyNode_eq, hn1_ko _ hyLt (by rw [← hyNode_eq, hyNode_old]; omega), endOfKey_endKey]
    rw [ht₂_m]; exact hins.trans hrot_r
  have hft_other : ∀ r' ∈ s.rf.R, r' ≠ r →
      fullTour s'.ord s'.rf.F hvalid'.compat.forest r' = fullTour s.ord s.rf.F h.valid.compat.forest r' := by
    intro r' hr' hne
    exact fullTour_insertOpen_other h.valid hedit fun hconn => by
      have h1 := h.valid.unique_root v hvF
      have hrr' : r' = r := (h1.unique ⟨hr', connected_symm hconn⟩ (h.valid.root_spec hvF))
      exact hne hrr'
  have hcomp_inj : ∀ r' ∈ s.rf.R, r' ≠ r → x.compTree r' ≠ some t := by
    intro r' hr' hne heq
    have hr'ne : fullTour s.ord s.rf.F h.valid.compat.forest r' ≠ [] := by
      intro h0; rw [h.comp_none r' hr' h0] at heq; cases heq
    obtain ⟨t', ht'eq, _, ht'map⟩ := h.comp_some r' hr' hr'ne
    rw [heq] at ht'eq; cases Option.some.inj ht'eq
    have hy_ft' : yEnd ∈ fullTour s.ord s.rf.F h.valid.compat.forest r' := by
      rw [← ht'map]; exact List.mem_map.mpr ⟨yNode, hyNode_t, by rw [hyNode_old, hy_ko_old, endOfKey_endKey]⟩
    obtain ⟨w', hw', hcr'⟩ := ((fullTour_spec h.valid.compat r').2 _).mp hy_ft'
    have hw'v : w' = v := h.valid.compat.unique w' v yEnd hw' hyEnd_mem
    subst hw'v
    exact hne ((h.valid.unique_root w' hvF).unique ⟨hr', connected_symm hcr'⟩ (h.valid.root_spec hvF))
  -- Unified helper: given final `(tF, sF, memF, rF, posF, cTail)` after the `headCh`/`irV` block,
  -- close the final `endOwner[keyX] := sv + 1 ;; ret heap` and `TourCoreAt`!
  have hFinish : ∀ (tF : AuxTree) (sF : SplayState TourVal TourSum Unit) (memF : ℕ → ℕ)
      (rF : ℕ → ℕ) (posF cTail : ℕ),
      Runs w p ω
        (.cond (.reg 13)
          (.store (.bin .add (.reg 8) (.reg 1)) (.reg 6) ;;
           .cond (.reg 14)
             (.assign 15 (.bin .add (.reg 10) (.bin .mul (.const 17) (.reg 9))) ;;
              .assign 16 (.load (.bin .add (.reg 15) (.const 9))) ;;
              .assign 17 (.load (.bin .add (.reg 15) (.const 10))) ;;
              .assign 18 (.const 0) ;;
              .call 19 C.setValNode [.reg 10, .reg 9, .reg 16, .reg 17, .reg 18, .reg 11, .reg 4] ;;
              .assign 16 (.const 1) ;;
              .assign 17 (.const 0) ;;
              .assign 18 (.bin .add (.reg 1) (.const 1)) ;;
              .call 19 C.setValNode [.reg 10, .reg 6, .reg 16, .reg 17, .reg 18, .reg 11, .reg 4] ;;
              .call 19 C.rotateFront [.reg 10, .reg 6, .reg 11, .reg 4])
             .nop)
          (.cond (.reg 14) (.call 19 C.rotateFront [.reg 10, .reg 9, .reg 11, .reg 4]) .nop))
        { st₂ with regs := rIR2 } .normal ⟨memF, rF, posF⟩ cTail →
      rF 2 = keyX → rF 4 = heap → rF 5 = x.slotOf v → rF 7 = endOwnerBase b vCap eCap →
      tourLayout.NodesAt memF (nodesBase b vCap eCap) nn1 sF →
      TourForestInv nn1 sF (tF :: rest1) →
      tF.toList.Perm t₂.toList →
      tF.toList.map (fun id => endOfKey (keyOf1 id)) = fullTour s'.ord s'.rf.F hvalid'.compat.forest r →
      (∀ a, a < nodesBase b vCap eCap → a ≠ firstEndBase b + v → memF a = st₂.mem a) →
      memF (firstEndBase b + v) = (if headCh = 1 then u else feOld) →
      ZeroFrom memF heap →
      (∀ a, (a < b ∨ ordHandleOf b vCap eCap ≤ a) → a < heap → memF a = st₂.mem a) →
      (∀ id, 1 ≤ id → id ≤ nn1 → (sF.nodes id).val =
        if id = u then ⟨true, false, tourRootTagVal s' (endOfKey keyX)⟩
        else if id = feOld then { (x.st.nodes feOld).val with rootTag := tourRootTagVal s' aOld }
        else (x.st.nodes id).val) →
      (∀ id ≤ nn1, id = 0 ∨ nn1 < id → (sF.nodes id).val.rootTag = 0) →
      cTail + TOUR_PHI_MULT * forestPhi (tF :: rest1) ≤
        TOUR_PHI_MULT * forestPhi (t₂ :: rest1) +
          (2 * TOUR_FIND_AMORT + TOUR_SEQ_AMORT) * (Nat.log 2 (nn1 + 2) + 1) + 200 →
      ∃ (st' : State) (c : ℕ) (x' : TourConcrete τ_ord),
        Runs w p ω (tourEditInsertBody C.initNode C.insertBefore C.setValNode C.rotateFront)
          (startState [b, v, keyX, yWord, heap] mem pos) (.returned heap) st' c ∧
        x'.ordX = x.ordX ∧ ZeroFrom st'.mem heap ∧
        (∀ a, (a < b ∨ ordHandleOf b vCap eCap ≤ a) → a < heap → st'.mem a = mem a) ∧
        TourCoreAt vCap eCap b s' x' st'.mem ∧
        c + TOUR_PHI_MULT * forestPhi x'.trees ≤
          TOUR_PHI_MULT * forestPhi x.trees + TOUR_EDIT_SIMPLE_MUL * tourLog eCap := by
    intro tF sF memF rF posF cTail hrunTail hrF2 hrF4 hrF5 hrF7 hnF hinvF htF_perm htF_map
      hmF_pre hmF_fev hzF hmF_out hvalF hvalF_un hcTail
    set memEnd := Function.update memF (endOwnerBase b vCap eCap + keyX) (x.slotOf v + 1)
    have hst_eo : Runs w p ω (.store (.bin .add (.reg 7) (.reg 2)) (.bin .add (.reg 5) (.const 1)))
        ⟨memF, rF, posF⟩ .normal ⟨memEnd, rF, posF⟩ 7 :=
      runs_store_iff.mpr ⟨endOwnerBase b vCap eCap + keyX, x.slotOf v + 1,
        by simp [Expr.eval, hrF7, hrF2, BinOp.eval, hgeo_eo.1],
        by simp [Expr.eval, hrF5, BinOp.eval, (by omega : 1 < 2 ^ w), hgeo_eo.2.1], rfl, rfl, rfl⟩
    have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := ⟨memEnd, rF, posF⟩) (r := 4) (v := heap) hrF4
    have hfull : Runs w p ω (tourEditInsertBody C.initNode C.insertBefore C.setValNode C.rotateFront)
        (startState [b, v, keyX, yWord, heap] mem pos) (.returned heap) ⟨memEnd, rF, posF⟩ _ :=
      runs_seqAppend hrun1 (tour_runs_seq_normal
        (tour_runs_cond_false hcond_fe
          (runs_seqAppend hrunT (tour_runs_seq_normal hcall_ib (tour_runs_seq_normal hIR1 (tour_runs_seq_normal hIR2 hrunTail)))))
        (tour_runs_seq_normal hst_eo hret))
    have hmEnd_pre : ∀ a < nodesBase b vCap eCap, a ≠ endOwnerBase b vCap eCap + keyX →
        a ≠ firstEndBase b + v → memEnd a = mem1 a := fun a hlt h1 h2 => by
      dsimp only [memEnd]; rw [Function.update_of_ne h1, hmF_pre a hlt h2, hm2_pre a hlt]
    have hmEnd_out : ∀ a, (a < b ∨ ordHandleOf b vCap eCap ≤ a) → a < heap → memEnd a = mem a := fun a ha hlt => by
      dsimp only [memEnd]
      rw [Function.update_of_ne (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | h2 <;> omega),
        hmF_out a ha hlt,
        hfr₂.2 a hlt (fun hrec => by have := inRecords_lt_ordHandle_of_le hnn_le hrec; simp [nodesBase] at this; rcases ha with h1 | h2 <;> omega)]
      exact hfr1_out a ha
    set x' : TourConcrete τ_ord :=
      { ordX := x.ordX, numNodes := nn1, st := sF, trees := tF :: rest1,
        nodeOf := nodeOf1, keyOf := keyOf1,
        compTree := Function.update x.compTree r (some tF),
        slotOf := x.slotOf, vertOf := x.vertOf }
    have hcore' : TourCoreAt vCap eCap b s' x' memEnd :=
      tourEditInsert_nonempty_core h hkeyLt hedit hu1 hunn hnn_le hn1k hk1u hn1_ne hk1_old
        hn1_mem hn1_ko hk1_mem hhdr1 hexact1 ht1_sub ht1_mem hmem1_fixed_eq
        haOld haOld_lt hfeOld_eq hfeOld_eq1 hfeOld_nz hyEnd_mem hyNode_old hy_ko_old hch_iff
        hct_r hperm_u rfl hyNode_t ht_PQ ht₂_PQ htF_perm hinv1_p.nodupAll hcomp_inj
        (NodesAt.congr tourLayout hnF fun a ha => by
          dsimp only [memEnd]; rw [Function.update_of_ne fun heq => by
            have := (inRecords_lt_ordHandle_of_le hnn_le ha).1; simp [endOwnerBase, nodesBase] at heq this; omega])
        hinvF htF_map hmEnd_pre
        (by dsimp only [memEnd]; rw [Function.update_of_ne (by simp [firstEndBase, endOwnerBase]; omega)]; exact hmF_fev)
        (by simp [memEnd]) hvalF hvalF_un
    refine ⟨⟨memEnd, rF, posF⟩, _, x', hfull, rfl,
      fun a ha => by
        dsimp only [memEnd]; rw [Function.update_of_ne (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
        exact hzF a ha,
      hmEnd_out, hcore', ?_⟩
    have hphi_u : forestPhi (AuxTree.node u .leaf .leaf :: t :: rest1) = forestPhi x.trees := by
      rw [← forestPhi_perm hperm_u, hphi1]
    have hmul : (TOUR_SEQ_AMORT + (2 * TOUR_FIND_AMORT + TOUR_SEQ_AMORT)) * (Nat.log 2 (nn1 + 2) + 1) ≤
        (TOUR_SEQ_AMORT + (2 * TOUR_FIND_AMORT + TOUR_SEQ_AMORT)) * (2 * tourLog eCap) :=
      Nat.mul_le_mul_left _ (tourLog_of_le hnn_le)
    dsimp only [x']; rw [hphi_u] at hcost₂
    clear * - hc1 hcT hcost₂ hcTail hmul htl
    simp only [Expr.size, TOUR_SPLICE_COST, TOUR_PHI_MULT, TOUR_FIND_AMORT, TOUR_SEQ_AMORT, TOUR_EDIT_SIMPLE_MUL] at *
    omega
  have hinj_t2 : ∀ a1 ∈ t₂.toList, ∀ a2 ∈ t₂.toList, endOfKey (keyOf1 a1) = endOfKey (keyOf1 a2) → a1 = a2 := by
    intro a1 ha1 a2 ha2 hab
    have ha' := hinv₂.mem_inCap (t := t₂) (by simp) ha1
    have hb' := hinv₂.mem_inCap (t := t₂) (by simp) ha2
    have hka : keyOf1 a1 = keyOf1 a2 := by rw [← endKey_endOfKey' (keyOf1 a1), hab, endKey_endOfKey']
    have hmem_nn : ∀ z ∈ t₂.toList, z ≤ nn1 := fun z hz => ((hexact1 z).mp (by
      have hmem_p : z ∈ (AuxTree.node u .leaf .leaf :: t :: rest1).flatMap AuxTree.toList := by
        simp only [List.flatMap_cons, AuxTree.toList, List.nil_append, List.cons_append, List.mem_cons, List.mem_append]
        rw [ht₂_PQ] at hz; rw [ht_PQ]; simp only [List.mem_append, List.mem_cons] at hz ⊢
        rcases hz with h1 | rfl | rfl | h2
        · exact Or.inr (Or.inl (Or.inl h1))
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inl (Or.inr (Or.inr h2)))
      obtain ⟨tr, htr, hzt⟩ := List.mem_flatMap.mp hmem_p
      exact List.mem_flatMap.mpr ⟨tr, hperm_u.mem_iff.mpr htr, hzt⟩)).2
    rw [← (hk1_mem a1 ha'.1 (hmem_nn a1 ha1)).2.2, hka, (hk1_mem a2 hb'.1 (hmem_nn a2 ha2)).2.2]
  have ht₂_map_not_root : v ∉ s.rf.R →
      t₂.toList.map (fun id => endOfKey (keyOf1 id)) = fullTour s'.ord s'.rf.F hvalid'.compat.forest r := by
    intro hvR
    have hrv_ne : r ≠ v := fun heq => hvR (heq ▸ hrR)
    have hord_r_ne : s.ord r ≠ [] := fun h0 => by
      have := (fullTour_eq_nil_iff h.valid.compat r).mpr h0
      rw [← ht_map] at this; have hnil := List.map_eq_nil_iff.mp this
      have hne := h.forestInv.nonEmpty t (hperm_r.mem_iff.mpr (by simp))
      cases t <;> simp [AuxTree.toList] at hne hnil
    obtain ⟨aR, haR⟩ : ∃ aR, (s.ord r).head? = some aR := by
      cases ho : s.ord r with | nil => exact absurd ho hord_r_ne | cons aR _ => exact ⟨aR, rfl⟩
    have hhd_t : (t.toList.map fun id => endOfKey (x.keyOf id)).head? = some aR := by
      rw [ht_map]; exact fullTour_head? h.valid.compat r haR
    have haR_ne_y : aR ≠ yEnd := fun heq =>
      hrv_ne (h.valid.compat.unique r v aR (List.mem_of_head? haR) (heq ▸ hyEnd_mem))
    have hP_ne : P ≠ [] := fun hP0 => by
      subst hP0; rw [ht_PQ] at hhd_t
      simp only [List.nil_append, List.map_cons, List.head?_cons, Option.some.injEq] at hhd_t
      rw [hyNode_old, hy_ko_old, endOfKey_endKey] at hhd_t; exact haR_ne_y hhd_t.symm
    obtain ⟨p0, ps, hPc⟩ := List.exists_cons_of_ne_nil hP_ne
    have hp0_eq : endOfKey (keyOf1 p0) = aR := by
      have hp0_t : p0 ∈ t.toList := by rw [ht_PQ, hPc]; simp
      have hp0_old := (h.nodes_exact p0).mp (List.mem_flatMap.mpr ⟨t, hperm_r.mem_iff.mpr (by simp), hp0_t⟩)
      rw [hk1_old p0 hp0_old.1 hp0_old.2]; rw [ht_PQ, hPc] at hhd_t; simpa using hhd_t
    have hhd_t2 : (t₂.toList.map fun id => endOfKey (keyOf1 id)).head? = some aR := by
      rw [ht₂_PQ, hPc]; simp [hp0_eq]
    have hhd_s' : (s'.ord r).head? = some aR := by
      simpa [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hrv_ne] using haR
    have h1 := tour_rotateToList_eq_of_isRotated (ht₂_isRot.perm.nodup_iff.mpr (fullTour_spec hvalid'.compat r).1)
      (List.IsRotated.refl _) hhd_t2
    have h2 := tour_rotateToList_eq_of_isRotated (fullTour_spec hvalid'.compat r).1 ht₂_isRot
      (fullTour_head? hvalid'.compat r hhd_s')
    exact h1.symm.trans h2
  have hle_old : x.numNodes ≤ nn1 := by
    by_contra hlt; push Not at hlt
    have := (hexact1 x.numNodes).mp (by
      have hxnn := (h.nodes_exact x.numNodes).mpr ⟨by omega, le_refl _⟩
      obtain ⟨t0, ht0, hmem0⟩ := List.mem_flatMap.mp hxnn
      by_cases htu : t0 = AuxTree.node u .leaf .leaf
      · subst htu; simp [AuxTree.toList] at hmem0; omega
      · exact List.mem_flatMap.mpr ⟨t0, List.mem_cons_of_mem _ (ht1_mem t0 ht0 htu), hmem0⟩)
    omega
  -- Now handle the 4 subcases of `(headCh, irV)`!
  have hvals_t2 : ∀ id, 1 ≤ id → id ≤ nn1 → (s₂.nodes id).val =
      if id = u then ⟨true, false, 0⟩ else (x.st.nodes id).val := fun id h1 h2 => by
    rw [hval₂ id (by omega)]
    by_cases hiu : id = u
    · subst hiu; simp [hs1u, tourSingletonNode]
    · simp [hiu, hs1ne id hiu]
  have hval_un_t2 : ∀ id ≤ nn1, id = 0 ∨ nn1 < id → (s₂.nodes id).val.rootTag = 0 := fun id hid hc => by
    have hiu : id ≠ u := by omega
    rw [hval₂ id hid, hs1ne id hiu]
    rcases hc with rfl | hgt
    · exact h.val_unused_rt 0 (Nat.zero_le _) (Or.inl rfl)
    · omega
  rcases hch_01 with hch0 | hch1
  · -- `headCh = 0`: `firstEnd[v]` unchanged (`feOld`), `yOpt ≠ some aOld`.
    have hcond_ch : (Expr.reg 13).eval w { st₂ with regs := rIR2 } = some 0 := by
      simp [Expr.eval, rIR2, rIR1, rIB, hrT13, hch0]
    have hyo_ne : yOpt ≠ some aOld := mt hch_iff.mpr (by omega)
    have hrt_u0 : tourRootTagVal s' (endOfKey keyX) = 0 := by
      apply tourRootTagVal_eq_zero; intro r' hr' hh
      by_cases hrv : r' = v
      · subst hrv; simp only [s', tourApplyEdit, applyOrdEdit, Function.update_self, insertBeforeList_head?, haOld, hyo_ne, ↓reduceIte] at hh
        exact hxFresh r' (Option.some.inj hh ▸ haOld_mem)
      · exact hxFresh r' (List.mem_of_head? (by simpa [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hrv] using hh))
    have hrt_old_eq : tourRootTagVal s' aOld = tourRootTagVal s aOld := by
      by_cases hvR : v ∈ s.rf.R
      · rw [tourRootTagVal_eq_succ h.valid hvR haOld,
          tourRootTagVal_eq_succ hvalid' hvR (by simp [s', tourApplyEdit, applyOrdEdit, insertBeforeList_head?, haOld, hyo_ne])]
      · rw [tourRootTagVal_eq_zero (fun r' hr' hh => by
            have hrv : r' = v := hvalid'.compat.unique r' v aOld (List.mem_of_head? hh) ((hord'_mem v aOld).mpr (Or.inr haOld_mem))
            exact hvR (hrv ▸ hr')),
          tourRootTagVal_eq_zero (fun r' hr' hh => by
            have hrv : r' = v := h.valid.compat.unique r' v aOld (List.mem_of_head? hh) haOld_mem
            exact hvR (hrv ▸ hr'))]
    have hfe_old_in : 1 ≤ feOld ∧ feOld ≤ x.numNodes := ⟨by omega, hfeOld_eq ▸ (h.nodeOf_mem _ haOld_lt).2⟩
    have hfe_val_eq : (x.st.nodes feOld).val = { (x.st.nodes feOld).val with rootTag := tourRootTagVal s' aOld } := by
      have hact_fe := h.val_active feOld hfe_old_in.1 hfe_old_in.2 ⟨v, by
        rw [hfeOld_eq, h.nodeOf_keyOf _ haOld_lt (hfeOld_eq ▸ hfeOld_nz), endOfKey_endKey]; exact haOld_mem⟩
      have hkfe : endOfKey (x.keyOf feOld) = aOld := by
        rw [hfeOld_eq, h.nodeOf_keyOf _ haOld_lt (hfeOld_eq ▸ hfeOld_nz), endOfKey_endKey]
      rw [hkfe] at hact_fe; rw [hact_fe, hrt_old_eq]
    have hm2_fev : st₂.mem (firstEndBase b + v) = feOld := by
      rw [hm2_pre _ (by simp [firstEndBase, nodesBase]; omega),
        hmem1_fixed_eq _ (by simp [firstEndBase, nodesBase]; omega) (by simp [firstEndBase, HDR_NUM_NODES]; omega)
          (by simp [firstEndBase, nodeOfEndBase]; omega) (by simp [firstEndBase, keyOfNodeBase]; omega)]
    by_cases hvR : v ∈ s.rf.R
    · -- `headCh = 0`, `v ∈ s.rf.R`: rotate `t₂` so `feOld` is at front!
      have hr_eq_v : r = v := ((h.valid.unique_root v hvF).unique (h.valid.root_spec hvF) ⟨hvR, connected_refl _ v⟩)
      have hir1 : irV = 1 := by simp [irV, hvR]
      have hcond_ir : (Expr.reg 14).eval w { st₂ with regs := rIR2 } = some 1 := by simp [Expr.eval, rIR2, hir1]
      have hfe_t2 : feOld ∈ t₂.toList := by
        have hfe_t : feOld ∈ t.toList := by
          have ha_ft : aOld ∈ fullTour s.ord s.rf.F h.valid.compat.forest r :=
            ((fullTour_spec h.valid.compat r).2 aOld).mpr ⟨v, haOld_mem, connected_symm (h.valid.root_spec hvF).2⟩
          rw [← ht_map] at ha_ft; obtain ⟨id, hid, hida⟩ := List.mem_map.mp ha_ft
          have hid_in := (h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨t, hperm_r.mem_iff.mpr (by simp), hid⟩)
          have hkeq : x.keyOf id = endKey aOld := by rw [← hida, endKey_endOfKey']
          have : id = feOld := by rw [hfeOld_eq, ← hkeq, (h.keyOf_mem id hid_in.1 hid_in.2).2.2]
          exact this ▸ hid
        rw [ht_PQ] at hfe_t; rw [ht₂_PQ]
        simp only [List.mem_append, List.mem_cons] at hfe_t ⊢
        rcases hfe_t with h1 | rfl | h2
        · exact Or.inl h1
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr h2))
      obtain ⟨t₃, s₃, o₃, st₃, c₃, hrun₃, _, hn₃, hfr₃, hinv₃, _, _, hrot₃, hval₃, _, hcost₃⟩ :=
        tourRotateFrontBody_runs (fuel := 2 * eCap + 2) (pos := st₂.pos) C.toTourSplayOpsProcs ω hn₂ hinv₂ hvals₂ hfe_t2
          (by omega) (by omega) ⟨hheap1.rec_le, hheap1.room, hfr₂.1, hheap1.wide⟩
      have hcall_rot := runs_call_regs4 19 10 9 11 4 (st := { st₂ with regs := rIR2 }) C.rotateFront_body
        (by simp [rIR2, rIR1, rIB, hrT10]) (by simp [rIR2, rIR1, rIB, hrT9])
        (by simp [rIR2, rIR1, rIB, hrT11]) (by simp [rIR2, rIR1, rIB, hrT4]) hrun₃
      have ht₃_map : t₃.toList.map (fun id => endOfKey (keyOf1 id)) = fullTour s'.ord s'.rf.F hvalid'.compat.forest r := by
        have hnd2 : (t₂.toList.map fun id => endOfKey (keyOf1 id)).Nodup :=
          ht₂_isRot.perm.nodup_iff.mpr (fullTour_spec hvalid'.compat r).1
        have hrot_m : (rotateNatList feOld t₂.toList).map (fun id => endOfKey (keyOf1 id)) =
            rotateToList aOld (t₂.toList.map fun id => endOfKey (keyOf1 id)) := by
          have hkfe : endOfKey (keyOf1 feOld) = aOld := by
            rw [hfeOld_eq1, hn1_ko _ haOld_lt (hfeOld_eq1 ▸ hfeOld_nz), endOfKey_endKey]
          have hidx : (t₂.toList.map fun id => endOfKey (keyOf1 id)).idxOf aOld = t₂.toList.idxOf feOld := by
            rw [← hkfe]; clear * - hinj_t2 hfe_t2
            generalize t₂.toList = ls at hinj_t2 hfe_t2 ⊢
            induction ls with
            | nil => simp at hfe_t2
            | cons z zs ih =>
              by_cases hzf : z = feOld
              · subst hzf; simp
              · have hne : endOfKey (keyOf1 z) ≠ endOfKey (keyOf1 feOld) := fun heq =>
                  hzf (hinj_t2 z (by simp) feOld hfe_t2 heq)
                have hfzs : feOld ∈ zs := (List.mem_cons.mp hfe_t2).resolve_left (Ne.symm hzf)
                simp [List.idxOf_cons_ne _ hzf, List.idxOf_cons_ne _ hne,
                  ih (fun a ha b hb => hinj_t2 a (by simp [ha]) b (by simp [hb])) hfzs]
          have ham : aOld ∈ t₂.toList.map (fun id => endOfKey (keyOf1 id)) :=
            List.mem_map.mpr ⟨feOld, hfe_t2, hkfe⟩
          simp [rotateNatList, rotateToList, hfe_t2, ham, hidx, List.map_append, List.map_drop, List.map_take]
        rw [hrot₃, hrot_m]
        have hhd' : (s'.ord r).head? = some aOld := by
          rw [hr_eq_v]; simp [s', tourApplyEdit, applyOrdEdit, insertBeforeList_head?, haOld, hyo_ne]
        exact tour_rotateToList_eq_of_isRotated (fullTour_spec hvalid'.compat r).1 ht₂_isRot (fullTour_head? hvalid'.compat r hhd')
      exact hFinish t₃ s₃ st₃.mem (Function.update rIR2 19 o₃.value) st₃.pos _
        (tour_runs_cond_false hcond_ch (tour_runs_cond_true hcond_ir (by omega) hcall_rot))
        (by simp [rIR2, rIR1, rIB, hrT2]) (by simp [rIR2, rIR1, rIB, hrT4])
        (by simp [rIR2, rIR1, rIB, hrT5]) (by simp [rIR2, rIR1, rIB, hrT7])
        hn₃ hinv₃ (by rw [hrot₃]; exact rotateNatList_perm hfe_t2) ht₃_map
        (fun a ha _ => hfr₃.2 a (by simp [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega)
          (fun hrec => by have := (inRecords_lt_ordHandle_of_le hnn_le hrec).1; omega))
        (by rw [hfr₃.2 _ (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
              (fun hrec => by have := (inRecords_lt_ordHandle_of_le hnn_le hrec).1; simp [firstEndBase, nodesBase] at this; omega),
            hm2_fev]; simp [hch0])
        hfr₃.1
        (fun a ha hlt => hfr₃.2 a hlt (fun hrec => by have := inRecords_lt_ordHandle_of_le hnn_le hrec; simp [nodesBase] at this; rcases ha with h1 | h2 <;> omega))
        (fun id h1 h2 => by
          rw [hval₃ id (by omega), hvals_t2 id h1 h2]
          by_cases hiu : id = u
          · subst hiu; simp [hrt_u0]
          · by_cases hife : id = feOld
            · subst hife; simp only [hiu, ↓reduceIte]; exact hfe_val_eq
            · simp [hiu, hife])
        (fun id hid hc => by rw [hval₃ id hid]; exact hval_un_t2 id hid hc)
        (by
          have hmul : TOUR_SEQ_AMORT * (Nat.log 2 (nn1 + 2) + 1) ≤
              (2 * TOUR_FIND_AMORT + TOUR_SEQ_AMORT) * (Nat.log 2 (nn1 + 2) + 1) :=
            Nat.mul_le_mul_right _ (by unfold TOUR_FIND_AMORT TOUR_SEQ_AMORT; omega)
          clear * - hcost₃ hmul; simp only [Expr.size] at *; omega)
    · -- `headCh = 0`, `v ∉ s.rf.R`: no rotation needed! `r ≠ v`, so `t₂` already starts at `firstEnd[r]`.
      have hir0 : irV = 0 := by simp [irV, hvR]
      have hcond_ir : (Expr.reg 14).eval w { st₂ with regs := rIR2 } = some 0 := by simp [Expr.eval, rIR2, hir0]
      exact hFinish t₂ s₂ st₂.mem rIR2 st₂.pos _
        (tour_runs_cond_false hcond_ch (tour_runs_cond_false hcond_ir (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)))
        (by simp [rIR2, rIR1, rIB, hrT2]) (by simp [rIR2, rIR1, rIB, hrT4])
        (by simp [rIR2, rIR1, rIB, hrT5]) (by simp [rIR2, rIR1, rIB, hrT7])
        hn₂ hinv₂ (List.Perm.refl _) (ht₂_map_not_root hvR) (fun _ _ _ => rfl) (by simp [hm2_fev, hch0])
        hfr₂.1 (fun _ _ _ => rfl)
        (fun id h1 h2 => by
          rw [hvals_t2 id h1 h2]
          by_cases hiu : id = u
          · subst hiu; simp [hrt_u0]
          · by_cases hife : id = feOld
            · subst hife; simp only [hiu, ↓reduceIte]; exact hfe_val_eq
            · simp [hiu, hife])
        hval_un_t2 (by clear * -; simp only [Expr.size]; omega)
  · -- `headCh = 1`: `yOpt = some aOld`, store `firstEnd[v] := u`!
    have hcond_ch : (Expr.reg 13).eval w { st₂ with regs := rIR2 } = some 1 := by
      simp [Expr.eval, rIR2, rIR1, rIB, hrT13, hch1]
    have hyo_eq : yOpt = some aOld := hch_iff.mp hch1
    set memF1 := Function.update st₂.mem (firstEndBase b + v) u
    have hst_fe : Runs w p ω (.store (.bin .add (.reg 8) (.reg 1)) (.reg 6))
        { st₂ with regs := rIR2 } .normal { st₂ with mem := memF1, regs := rIR2 } 5 :=
      runs_store_iff.mpr ⟨firstEndBase b + v, u,
        by simp [Expr.eval, rIR2, rIR1, rIB, hrT8, hrT1, BinOp.eval, hgeo_eo.2.2.1],
        by simp [Expr.eval, rIR2, rIR1, rIB, hrT6], rfl, rfl, rfl⟩
    have hnF1 : tourLayout.NodesAt memF1 (nodesBase b vCap eCap) nn1 s₂ :=
      NodesAt.congr tourLayout hn₂ fun a ha => by
        dsimp only [memF1]; rw [Function.update_of_ne fun heq => by
          have := (inRecords_lt_ordHandle_of_le hnn_le ha).1; simp [firstEndBase, nodesBase] at heq this; omega]
    have hzF1 : ZeroFrom memF1 heap := fun a ha => by
      dsimp only [memF1]; rw [Function.update_of_ne (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]
      exact hfr₂.1 a ha
    by_cases hvR : v ∈ s.rf.R
    · -- `headCh = 1`, `v ∈ s.rf.R`: clear `rootTag` on `feOld`, set `v + 1` on `u`, `rotateFront u`!
      have hr_eq_v : r = v := ((h.valid.unique_root v hvF).unique (h.valid.root_spec hvF) ⟨hvR, connected_refl _ v⟩)
      have hir1 : irV = 1 := by simp [irV, hvR]
      have hcond_ir : (Expr.reg 14).eval w { st₂ with mem := memF1, regs := rIR2 } = some 1 := by simp [Expr.eval, rIR2, hir1]
      have hfe_cap : feOld ≤ nn1 := le_trans (hfeOld_eq ▸ (h.nodeOf_mem _ haOld_lt).2) hle_old
      have hfe_t2 : feOld ∈ t₂.toList := by
        have ha_ft : aOld ∈ fullTour s.ord s.rf.F h.valid.compat.forest r :=
          ((fullTour_spec h.valid.compat r).2 aOld).mpr ⟨v, haOld_mem, connected_symm (h.valid.root_spec hvF).2⟩
        rw [← ht_map] at ha_ft; obtain ⟨id, hid, hida⟩ := List.mem_map.mp ha_ft
        have hid_in := (h.nodes_exact id).mp (List.mem_flatMap.mpr ⟨t, hperm_r.mem_iff.mpr (by simp), hid⟩)
        have hkeq : x.keyOf id = endKey aOld := by rw [← hida, endKey_endOfKey']
        have : id = feOld := by rw [hfeOld_eq, ← hkeq, (h.keyOf_mem id hid_in.1 hid_in.2).2.2]
        rw [ht_PQ] at hid; rw [ht₂_PQ]; rw [← this]; simp only [List.mem_append, List.mem_cons] at hid ⊢
        rcases hid with h1 | rfl | h2
        · exact Or.inl h1
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr h2))
      have hu_t2 : u ∈ t₂.toList := by rw [ht₂_PQ]; simp
      have hheapF1 : HeapOk tourLayout w (nodesBase b vCap eCap) nn1 heap 2 memF1 :=
        ⟨hheap1.rec_le, hheap1.room, hzF1, hheap1.wide⟩
      set opO := if (s₂.nodes feOld).val.isOpen then 1 else 0
      set mkO := if (s₂.nodes feOld).val.isMarked then 1 else 0
      have hmF1_opO : memF1 (nodesBase b vCap eCap + 17 * feOld + 9) = opO := by
        have hnd := hnF1 feOld hfe_cap; simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_VAL, opO, Nat.add_assoc] using hnd.2.2.2.2.2.2.1.2.2.2.1
      have hmF1_mkO : memF1 (nodesBase b vCap eCap + 17 * feOld + 10) = mkO := by
        have hnd := hnF1 feOld hfe_cap; simpa [NodeLayout.nodeAddr, tourLayout_stride, OFF_VAL, mkO, Nat.add_assoc] using hnd.2.2.2.2.2.2.1.2.2.2.2.1
      obtain ⟨t₃, s₃, o₃, st₃, c₃, hrun₃, hn₃, hfr₃, hinv₃, hvals₃, _, _, hlist₃, hvalO₃, hvalne₃, _, hcost₃⟩ :=
        tourSetValNodeBody_runs (fuel := 2 * eCap + 2) (pos := st₂.pos) C ω hnF1 hinv₂ hvals₂ hfe_t2 (by omega) (by omega)
          (isOpen := opO) (isMarked := mkO) (rootTag := 0) (by omega) hheapF1
      have hu_t3 : u ∈ t₃.toList := by rw [hlist₃]; exact hu_t2
      obtain ⟨t₄, s₄, o₄, st₄, c₄, hrun₄, hn₄, hfr₄, hinv₄, hvals₄, _, _, hlist₄, hvalU₄, hvalne₄, _, hcost₄⟩ :=
        tourSetValNodeBody_runs (fuel := 2 * eCap + 2) (pos := st₃.pos) C ω hn₃ hinv₃ hvals₃ hu_t3 (by omega) (by omega)
          (isOpen := 1) (isMarked := 0) (rootTag := v + 1) (by omega)
          ⟨hheapF1.rec_le, hheapF1.room, hfr₃.1, hheapF1.wide⟩
      have hu_t4 : u ∈ t₄.toList := by rw [hlist₄]; exact hu_t3
      obtain ⟨t₅, s₅, o₅, st₅, c₅, hrun₅, _, hn₅, hfr₅, hinv₅, _, _, hrot₅, hval₅, _, hcost₅⟩ :=
        tourRotateFrontBody_runs (fuel := 2 * eCap + 2) (pos := st₄.pos) C.toTourSplayOpsProcs ω hn₄ hinv₄ hvals₄ hu_t4
          (by omega) (by omega) ⟨hheapF1.rec_le, hheapF1.room, (hfr₃.trans hfr₄).1, hheapF1.wide⟩
      -- Execute the inner 11-step root-update block
      have hAfe : nodesBase b vCap eCap + 17 * feOld + 17 < 2 ^ w := by
        have := hheapF1.addr_lt hfe_cap; simp [NodeLayout.nodeAddr, tourLayout_stride] at this; omega
      set rR1 := Function.update rIR2 15 (nodesBase b vCap eCap + 17 * feOld)
      set rR2 := Function.update rR1 16 opO
      set rR3 := Function.update rR2 17 mkO
      set rR4 := Function.update rR3 18 0
      have hR1 : Runs w p ω (.assign 15 (.bin .add (.reg 10) (.bin .mul (.const 17) (.reg 9))))
          { st₂ with mem := memF1, regs := rIR2 } .normal { st₂ with mem := memF1, regs := rR1 } 6 :=
        runs_assign_iff.mpr ⟨nodesBase b vCap eCap + 17 * feOld, by
          simp [Expr.eval, rIR2, rIR1, rIB, hrT10, hrT9, BinOp.eval, (by omega : 17 < 2 ^ w),
            (by omega : 17 * feOld < 2 ^ w), (by omega : nodesBase b vCap eCap + 17 * feOld < 2 ^ w)], rfl, rfl, rfl⟩
      have hR2 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 16) (rBase := 15) (off := 9)
        (b := nodesBase b vCap eCap + 17 * feOld) (val := opO) (st := { st₂ with mem := memF1, regs := rR1 })
        (by simp [rR1]) (by omega) (by omega) hmF1_opO
      have hR3 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 17) (rBase := 15) (off := 10)
        (b := nodesBase b vCap eCap + 17 * feOld) (val := mkO) (st := { st₂ with mem := memF1, regs := rR2 })
        (by simp [rR2, rR1]) (by omega) (by omega) hmF1_mkO
      have hR4 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 18) (val := 0)
        (st := { st₂ with mem := memF1, regs := rR3 }) (by omega)
      have hR5 := runs_call_regs7 19 10 9 16 17 18 11 4 (st := { st₂ with mem := memF1, regs := rR4 }) C.setValNode_body
        (by simp [rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT10]) (by simp [rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT9])
        (by simp [rR4, rR3, rR2]) (by simp [rR4, rR3]) (by simp [rR4])
        (by simp [rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT11]) (by simp [rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT4]) hrun₃
      set rR5 := Function.update rR4 19 o₃.value
      set rR6 := Function.update rR5 16 1
      set rR7 := Function.update rR6 17 0
      set rR8 := Function.update rR7 18 (v + 1)
      have hR6 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 16) (val := 1) (st := { st₃ with regs := rR5 }) (by omega)
      have hR7 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 17) (val := 0) (st := { st₃ with regs := rR6 }) (by omega)
      have hR8 : Runs w p ω (.assign 18 (.bin .add (.reg 1) (.const 1)))
          { st₃ with regs := rR7 } .normal { st₃ with regs := rR8 } 4 :=
        runs_assign_iff.mpr ⟨v + 1, by
          simp [Expr.eval, rR7, rR6, rR5, rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT1,
            BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : v + 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hR9 := runs_call_regs7 19 10 6 16 17 18 11 4 (st := { st₃ with regs := rR8 }) C.setValNode_body
        (by simp [rR8, rR7, rR6, rR5, rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT10])
        (by simp [rR8, rR7, rR6, rR5, rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT6])
        (by simp [rR8, rR7, rR6]) (by simp [rR8, rR7]) (by simp [rR8])
        (by simp [rR8, rR7, rR6, rR5, rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT11])
        (by simp [rR8, rR7, rR6, rR5, rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT4]) hrun₄
      set rR9 := Function.update rR8 19 o₄.value
      have hR10 := runs_call_regs4 19 10 6 11 4 (st := { st₄ with regs := rR9 }) C.rotateFront_body
        (by simp [rR9, rR8, rR7, rR6, rR5, rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT10])
        (by simp [rR9, rR8, rR7, rR6, rR5, rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT6])
        (by simp [rR9, rR8, rR7, rR6, rR5, rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT11])
        (by simp [rR9, rR8, rR7, rR6, rR5, rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT4]) hrun₅
      have hrun_root := tour_runs_seq_normal hR1 (tour_runs_seq_normal hR2 (tour_runs_seq_normal hR3
        (tour_runs_seq_normal hR4 (tour_runs_seq_normal hR5 (tour_runs_seq_normal hR6 (tour_runs_seq_normal hR7
          (tour_runs_seq_normal hR8 (tour_runs_seq_normal hR9 hR10))))))))
      have hfr35 : TreeFrame tourLayout (nodesBase b vCap eCap) nn1 heap memF1 st₅.mem :=
        hfr₃.trans (hfr₄.trans hfr₅)
      have ht₅_map : t₅.toList.map (fun id => endOfKey (keyOf1 id)) = fullTour s'.ord s'.rf.F hvalid'.compat.forest r := by
        have ht4_eq : t₄.toList = t₂.toList := hlist₄.trans hlist₃
        have hrot_m : (rotateNatList u t₄.toList).map (fun id => endOfKey (keyOf1 id)) =
            rotateToList (endOfKey keyX) (t₂.toList.map fun id => endOfKey (keyOf1 id)) := by
          rw [ht4_eq]
          have hidx : (t₂.toList.map fun id => endOfKey (keyOf1 id)).idxOf (endOfKey keyX) = t₂.toList.idxOf u := by
            rw [← hk1u]; clear * - hinj_t2 hu_t2
            generalize t₂.toList = ls at hinj_t2 hu_t2 ⊢
            induction ls with
            | nil => simp at hu_t2
            | cons z zs ih =>
              by_cases hzu : z = u
              · subst hzu; simp
              · have hne : endOfKey (keyOf1 z) ≠ endOfKey (keyOf1 u) := fun heq => hzu (hinj_t2 z (by simp) u hu_t2 heq)
                have huzs : u ∈ zs := (List.mem_cons.mp hu_t2).resolve_left (Ne.symm hzu)
                simp [List.idxOf_cons_ne _ hzu, List.idxOf_cons_ne _ hne,
                  ih (fun a ha b hb => hinj_t2 a (by simp [ha]) b (by simp [hb])) huzs]
          have hxm : endOfKey keyX ∈ t₂.toList.map (fun id => endOfKey (keyOf1 id)) :=
            List.mem_map.mpr ⟨u, hu_t2, by rw [hk1u]⟩
          simp [rotateNatList, rotateToList, hu_t2, hxm, hidx, List.map_append, List.map_drop, List.map_take]
        rw [hrot₅, hrot_m]
        have hhd' : (s'.ord r).head? = some (endOfKey keyX) := by
          rw [hr_eq_v]; simp [s', tourApplyEdit, applyOrdEdit, insertBeforeList_head?, haOld, hyo_eq]
        exact tour_rotateToList_eq_of_isRotated (fullTour_spec hvalid'.compat r).1 ht₂_isRot (fullTour_head? hvalid'.compat r hhd')
      have hrt_u : tourRootTagVal s' (endOfKey keyX) = v + 1 :=
        tourRootTagVal_eq_succ hvalid' hvR (by simp [s', tourApplyEdit, applyOrdEdit, insertBeforeList_head?, haOld, hyo_eq])
      have hrt_old0 : tourRootTagVal s' aOld = 0 := by
        apply tourRootTagVal_eq_zero; intro r' hr' hh
        have hr'v : r' = v := hvalid'.compat.unique r' v aOld (List.mem_of_head? hh) ((hord'_mem v aOld).mpr (Or.inr haOld_mem))
        subst hr'v; simp [s', tourApplyEdit, applyOrdEdit, insertBeforeList_head?, haOld, hyo_eq] at hh
        exact hxFresh r' (hh ▸ haOld_mem)
      have hu_ne_fe : u ≠ feOld := fun heq => by
        have h1 : keyOf1 feOld = endKey aOld := by rw [hfeOld_eq1]; exact hn1_ko _ haOld_lt (hfeOld_eq1 ▸ hfeOld_nz)
        rw [← heq, hk1u] at h1; exact haOld_ne_keyX h1.symm
      exact hFinish t₅ s₅ st₅.mem (Function.update rR9 19 o₅.value) st₅.pos _
        (tour_runs_cond_true hcond_ch (by omega) (tour_runs_seq_normal hst_fe (tour_runs_cond_true hcond_ir (by omega) hrun_root)))
        (by simp [rR9, rR8, rR7, rR6, rR5, rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT2])
        (by simp [rR9, rR8, rR7, rR6, rR5, rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT4])
        (by simp [rR9, rR8, rR7, rR6, rR5, rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT5])
        (by simp [rR9, rR8, rR7, rR6, rR5, rR4, rR3, rR2, rR1, rIR2, rIR1, rIB, hrT7])
        hn₅ hinv₅ (by rw [hrot₅]; exact (rotateNatList_perm hu_t4).trans (by rw [hlist₄, hlist₃])) ht₅_map
        (fun a ha hne => by
          rw [hfr35.2 a (by simp [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega)
            (fun hrec => by have := (inRecords_lt_ordHandle_of_le hnn_le hrec).1; omega)]
          dsimp only [memF1]; exact Function.update_of_ne hne _ _)
        (by rw [hfr35.2 _ (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
              (fun hrec => by have := (inRecords_lt_ordHandle_of_le hnn_le hrec).1; simp [firstEndBase, nodesBase] at this; omega)]
            simp [memF1, hch1])
        hfr35.1
        (fun a ha hlt => by
          rw [hfr35.2 a hlt (fun hrec => by have := inRecords_lt_ordHandle_of_le hnn_le hrec; simp [nodesBase] at this; rcases ha with h1 | h2 <;> omega)]
          dsimp only [memF1]
          exact Function.update_of_ne (by simp [firstEndBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | h2 <;> omega) _ _)
        (fun id h1 h2 => by
          rw [hval₅ id (by omega)]
          by_cases hiu : id = u
          · subst hiu; simp [hvalU₄, hrt_u]
          · rw [hvalne₄ id (by omega) hiu]
            by_cases hife : id = feOld
            · subst hife
              have hop : decide (0 < opO) = (x.st.nodes feOld).val.isOpen := by
                have hfe_v := hvals_t2 feOld h1 h2; simp [hiu] at hfe_v
                simp only [opO, hfe_v]; cases (x.st.nodes feOld).val.isOpen <;> simp
              have hmk : decide (0 < mkO) = (x.st.nodes feOld).val.isMarked := by
                have hfe_v := hvals_t2 feOld h1 h2; simp [hiu] at hfe_v
                simp only [mkO, hfe_v]; cases (x.st.nodes feOld).val.isMarked <;> simp
              simp [hiu, hvalO₃, hop, hmk, hrt_old0]
            · rw [hvalne₃ id (by omega) hife, hvals_t2 id h1 h2]; simp [hiu, hife])
        (fun id hid hc => by
          have hiu : id ≠ u := by omega
          have hife : id ≠ feOld := by
            have hle_fe : feOld ≤ x.numNodes := hfeOld_eq ▸ (h.nodeOf_mem _ haOld_lt).2
            omega
          rw [hval₅ id hid, hvalne₄ id hid hiu, hvalne₃ id hid hife]; exact hval_un_t2 id hid hc)
        (by
          have hsum : TOUR_FIND_AMORT * (Nat.log 2 (nn1 + 2) + 1) +
              TOUR_FIND_AMORT * (Nat.log 2 (nn1 + 2) + 1) +
              TOUR_SEQ_AMORT * (Nat.log 2 (nn1 + 2) + 1) =
              (2 * TOUR_FIND_AMORT + TOUR_SEQ_AMORT) * (Nat.log 2 (nn1 + 2) + 1) := by ring
          clear * - hcost₃ hcost₄ hcost₅ hsum; simp only [Expr.size, TOUR_PHI_MULT] at *; omega)
    · -- `headCh = 1`, `v ∉ s.rf.R`: only `firstEnd[v] := u` changed; `t₂` already starts at `firstEnd[r]`!
      have hir0 : irV = 0 := by simp [irV, hvR]
      have hcond_ir : (Expr.reg 14).eval w { st₂ with mem := memF1, regs := rIR2 } = some 0 := by simp [Expr.eval, rIR2, hir0]
      have hrt_u0 : tourRootTagVal s' (endOfKey keyX) = 0 := by
        apply tourRootTagVal_eq_zero; intro r' hr' hh
        have hr'v : r' ≠ v := fun heq => hvR (heq ▸ hr')
        exact hxFresh r' (List.mem_of_head? (by simpa [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hr'v] using hh))
      have hrt_old0 : tourRootTagVal s' aOld = 0 := by
        apply tourRootTagVal_eq_zero; intro r' hr' hh
        have hr'v : r' = v := hvalid'.compat.unique r' v aOld (List.mem_of_head? hh) ((hord'_mem v aOld).mpr (Or.inr haOld_mem))
        exact hvR (hr'v ▸ hr')
      have hfe_old_in : 1 ≤ feOld ∧ feOld ≤ x.numNodes := ⟨by omega, hfeOld_eq ▸ (h.nodeOf_mem _ haOld_lt).2⟩
      have hfe_val_eq : (x.st.nodes feOld).val = { (x.st.nodes feOld).val with rootTag := tourRootTagVal s' aOld } := by
        have hkfe : endOfKey (x.keyOf feOld) = aOld := by
          rw [hfeOld_eq, h.nodeOf_keyOf _ haOld_lt (hfeOld_eq ▸ hfeOld_nz), endOfKey_endKey]
        have hact_fe := h.val_active feOld hfe_old_in.1 hfe_old_in.2 ⟨v, hkfe.symm ▸ haOld_mem⟩
        rw [hkfe] at hact_fe
        have hrt_s0 : tourRootTagVal s aOld = 0 := by
          apply tourRootTagVal_eq_zero; intro r' hr' hh
          exact hvR ((h.valid.compat.unique r' v aOld (List.mem_of_head? hh) haOld_mem) ▸ hr')
        rw [hact_fe, hrt_s0, hrt_old0]
      exact hFinish t₂ s₂ memF1 rIR2 st₂.pos _
        (tour_runs_cond_true hcond_ch (by omega) (tour_runs_seq_normal hst_fe (tour_runs_cond_false hcond_ir (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩))))
        (by simp [rIR2, rIR1, rIB, hrT2]) (by simp [rIR2, rIR1, rIB, hrT4])
        (by simp [rIR2, rIR1, rIB, hrT5]) (by simp [rIR2, rIR1, rIB, hrT7])
        hnF1 hinv₂ (List.Perm.refl _) (ht₂_map_not_root hvR)
        (fun a _ hne => Function.update_of_ne hne _ _) (by simp [memF1, hch1])
        hzF1 (fun a ha _ => Function.update_of_ne (by simp [firstEndBase, ordHandleOf, tourFixedSize] at ha ⊢; rcases ha with h1 | h2 <;> omega) _ _)
        (fun id h1 h2 => by
          rw [hvals_t2 id h1 h2]
          by_cases hiu : id = u
          · subst hiu; simp [hrt_u0]
          · by_cases hife : id = feOld
            · subst hife; simp only [hiu, ↓reduceIte]; exact hfe_val_eq
            · simp [hiu, hife])
        hval_un_t2 (by clear * -; simp only [Expr.size]; omega)


end MinCostFlow.SparseCore.Program
