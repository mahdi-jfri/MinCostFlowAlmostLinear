module

public import MinCostFlow.SparseCore.Program.TourOpsEditCommon
import Mathlib.Tactic

/-!
# Single-edit handler for `rotateTo` (Op 0)

Implements and verifies `tourEditRotateBody [b, v, keyY, heap]`, updating the tour concrete
representation (`TourCoreAt`) for `OrdEdit.rotateTo v (endOfKey keyY)` in `O(tourLog eCap)`
amortized time with `2` words of heap headroom and without touching memory outside
`[b, ordHandleOf b vCap eCap)`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-- Amortized per-`tourLog` multiplier covering single simple edits (`rotateTo`, `insertBefore`,
`dropEdge`). -/
def TOUR_EDIT_SIMPLE_MUL : ℕ := 2500000

/-- Tour update for `rotateTo v (endOfKey keyY)`: args `[b, v, keyY, heap]`. -/
def tourEditRotateBody (setValNodeProc rotateFrontProc : ℕ) : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const HDR_NEXT_ARR))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const HDR_ECAP))) ;;
  .assign 4 (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 5))) ;;
  .assign 5 (.load (.bin .add (.reg 4) (.reg 1))) ;;
  .cond (.reg 5) (.assign 5 (.bin .sub (.reg 5) (.const 1))) (.assign 5 (.reg 1)) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const HDR_END_OWNER))) ;;
  .assign 6 (.load (.bin .add (.reg 6) (.reg 2))) ;;
  .cond (.bin .eq (.reg 6) (.bin .add (.reg 5) (.const 1)))
    (.assign 7 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
     .assign 7 (.load (.bin .add (.reg 7) (.reg 2))) ;;
     .assign 8 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
     .assign 9 (.load (.bin .add (.reg 8) (.reg 1))) ;;
     .cond (.bin .eq (.reg 7) (.reg 9))
       .nop
       (.store (.bin .add (.reg 8) (.reg 1)) (.reg 7) ;;
        .assign 10 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
        .assign 10 (.load (.bin .add (.reg 10) (.reg 1))) ;;
        .cond (.reg 10)
          (.assign 11 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
           .assign 12 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
           .assign 13 (.bin .add (.reg 11) (.bin .mul (.const 17) (.reg 9))) ;;
           .assign 14 (.load (.bin .add (.reg 13) (.const 9))) ;;
           .assign 15 (.load (.bin .add (.reg 13) (.const 10))) ;;
           .assign 16 (.const 0) ;;
           .call 17 setValNodeProc [.reg 11, .reg 9, .reg 14, .reg 15, .reg 16, .reg 12, .reg 3] ;;
           .assign 13 (.bin .add (.reg 11) (.bin .mul (.const 17) (.reg 7))) ;;
           .assign 14 (.load (.bin .add (.reg 13) (.const 9))) ;;
           .assign 15 (.load (.bin .add (.reg 13) (.const 10))) ;;
           .assign 16 (.bin .add (.reg 1) (.const 1)) ;;
           .call 17 setValNodeProc [.reg 11, .reg 7, .reg 14, .reg 15, .reg 16, .reg 12, .reg 3] ;;
           .call 17 rotateFrontProc [.reg 11, .reg 7, .reg 12, .reg 3])
          .nop))
    .nop ;;
  .ret (.reg 3)

theorem tourEditRotateBody_noRand (svP rfP : ℕ) :
    (tourEditRotateBody svP rfP).NoRand := by
  simp [tourEditRotateBody, Stmt.NoRand]

/-! ## Execution helper for the prefix + root-update inner block -/

private theorem tourEditRotate_prefix_exec {w vCap eCap b v keyY heap pos : ℕ} {p : Program}
    (ω : ℕ → Bool) {mem : ℕ → ℕ} {rawSlot eo : ℕ}
    (hord_le : ordHandleOf b vCap eCap ≤ heap) (hroom : heap + 2 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hvLt : v < vCap) (hkeyLt : keyY < 2 * eCap) (hrawW : rawSlot < 2 ^ w)
    (hm_na : mem (b + HDR_NEXT_ARR) = nextArrBase b vCap eCap)
    (hm_ec : mem (b + HDR_ECAP) = eCap)
    (hm_rs : mem (slotOfVertBase b vCap eCap + v) = rawSlot)
    (hm_eob : mem (b + HDR_END_OWNER) = endOwnerBase b vCap eCap)
    (hm_eo : mem (endOwnerBase b vCap eCap + keyY) = eo) :
    ∃ rP cP, rP 0 = b ∧ rP 1 = v ∧ rP 2 = keyY ∧ rP 3 = heap ∧
      rP 5 = decodeSlot rawSlot v ∧ rP 6 = eo ∧ cP ≤ 60 ∧
      Runs w p ω
        (.assign 4 (.load (.bin .add (.reg 0) (.const HDR_NEXT_ARR))) ;;
         .assign 5 (.load (.bin .add (.reg 0) (.const HDR_ECAP))) ;;
         .assign 4 (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 5))) ;;
         .assign 5 (.load (.bin .add (.reg 4) (.reg 1))) ;;
         .cond (.reg 5) (.assign 5 (.bin .sub (.reg 5) (.const 1))) (.assign 5 (.reg 1)) ;;
         .assign 6 (.load (.bin .add (.reg 0) (.const HDR_END_OWNER))) ;;
         .assign 6 (.load (.bin .add (.reg 6) (.reg 2))))
        (startState [b, v, keyY, heap] mem pos) .normal ⟨mem, rP, pos⟩ cP := by
  have hgeo : b + 16 < 2 ^ w ∧ 2 * eCap < 2 ^ w ∧ slotOfVertBase b vCap eCap + v < 2 ^ w ∧
      endOwnerBase b vCap eCap + keyY < 2 ^ w := by
    simp only [ordHandleOf, tourFixedSize, slotOfVertBase, endOwnerBase] at hord_le ⊢; omega
  set s0 : State := startState [b, v, keyY, heap] mem pos
  set r1 := Function.update s0.regs 4 (nextArrBase b vCap eCap)
  set r2 := Function.update r1 5 eCap
  set r3 := Function.update r2 4 (slotOfVertBase b vCap eCap)
  set r4 := Function.update r3 5 rawSlot
  set r5 := Function.update r4 5 (decodeSlot rawSlot v)
  set r6 := Function.update r5 6 (endOwnerBase b vCap eCap)
  set r7 := Function.update r6 6 eo
  have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 0) (off := HDR_NEXT_ARR)
    (b := b) (val := nextArrBase b vCap eCap) (st := s0) (by simp [s0, startState])
    (by simp [HDR_NEXT_ARR]; omega) (by simp [HDR_NEXT_ARR]; omega) hm_na
  have ha2 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 0) (off := HDR_ECAP)
    (b := b) (val := eCap) (st := ⟨mem, r1, pos⟩) (by simp [r1, s0, startState])
    (by rw [HDR_ECAP]; omega) (by rw [HDR_ECAP]; omega) hm_ec
  have ha3 : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 5))))
      ⟨mem, r2, pos⟩ .normal ⟨mem, r3, pos⟩ 6 :=
    runs_assign_iff.mpr ⟨slotOfVertBase b vCap eCap, by
      have h4 : r2 4 = nextArrBase b vCap eCap := by simp [r2, r1]
      have h5 : r2 5 = eCap := by simp [r2]
      simp only [Expr.eval, h4, h5, (by omega : 2 < 2 ^ w), BinOp.eval, (by omega : 2 * eCap < 2 ^ w),
        ← slotOfVertBase_eq, (by omega : slotOfVertBase b vCap eCap < 2 ^ w), ↓reduceIte], rfl, rfl, rfl⟩
  have ha4 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 4) (rIdx := 1)
    (base := slotOfVertBase b vCap eCap) (idx := v) (val := rawSlot) (st := ⟨mem, r3, pos⟩)
    (by simp [r3]) (by simp [r3, r2, r1, s0, startState]) hgeo.2.2.1 hm_rs
  have hc5 := runs_decodeSlot_stmt (w := w) (p := p) (ω := ω) (dst := 5) (rRaw := 5) (rIdx := 1)
    (raw := rawSlot) (idx := v) (st := ⟨mem, r4, pos⟩) (by simp [r4])
    (by simp [r4, r3, r2, r1, s0, startState]) (by omega) hrawW
  have ha6 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_END_OWNER)
    (b := b) (val := endOwnerBase b vCap eCap) (st := ⟨mem, r5, pos⟩)
    (by simp [r5, r4, r3, r2, r1, s0, startState])
    (by simp [HDR_END_OWNER]; omega) (by simp [HDR_END_OWNER]; omega) hm_eob
  have ha7 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 6) (rIdx := 2)
    (base := endOwnerBase b vCap eCap) (idx := keyY) (val := eo) (st := ⟨mem, r6, pos⟩)
    (by simp [r6]) (by simp [r6, r5, r4, r3, r2, r1, s0, startState]) hgeo.2.2.2 hm_eo
  have hseq := tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3
    (tour_runs_seq_normal ha4 (tour_runs_seq_normal hc5 (tour_runs_seq_normal ha6 ha7)))))
  refine ⟨r7, _, by simp [r7, r6, r5, r4, r3, r2, r1, s0, startState],
    by simp [r7, r6, r5, r4, r3, r2, r1, s0, startState],
    by simp [r7, r6, r5, r4, r3, r2, r1, s0, startState],
    by simp [r7, r6, r5, r4, r3, r2, r1, s0, startState],
    by simp [r7, r6, r5], by simp [r7], ?_, hseq⟩
  clear * -; split_ifs <;> omega

private theorem tourEditRotate_rootBlock_exec {w vCap eCap b v heap pos : ℕ} {p : Program}
    (C : TourSplayQueryProcs w p) (ω : ℕ → Bool) {mem1 : ℕ → ℕ} {rIn : ℕ → ℕ}
    {uOld uNew opO mkO opN mkN : ℕ}
    {o₁ o₂ o₃ : Outcome} {st₁ st₂ st₃ : State} {c₁ c₂ c₃ : ℕ}
    (hord_le : ordHandleOf b vCap eCap ≤ heap) (hroom : heap + 2 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hvLt : v < vCap)
    (hAxO : nodesBase b vCap eCap + 17 * uOld + 17 ≤ heap)
    (hAxN : nodesBase b vCap eCap + 17 * uNew + 17 ≤ heap)
    (hr0 : rIn 0 = b) (hr1 : rIn 1 = v) (hr3 : rIn 3 = heap) (hr7 : rIn 7 = uNew) (hr9 : rIn 9 = uOld)
    (hm_nb : mem1 (b + HDR_NODES_BASE) = nodesBase b vCap eCap)
    (hm_fuel : mem1 (b + HDR_FUEL) = 2 * eCap + 2)
    (hm_opO : mem1 (nodesBase b vCap eCap + 17 * uOld + 9) = opO)
    (hm_mkO : mem1 (nodesBase b vCap eCap + 17 * uOld + 10) = mkO)
    (hrun₁ : Runs w p ω (tourSetValNodeBody C.splay.splay C.setVal)
      (startState [nodesBase b vCap eCap, uOld, opO, mkO, 0, 2 * eCap + 2, heap] mem1 pos) o₁ st₁ c₁)
    (hm1_opN : st₁.mem (nodesBase b vCap eCap + 17 * uNew + 9) = opN)
    (hm1_mkN : st₁.mem (nodesBase b vCap eCap + 17 * uNew + 10) = mkN)
    (hrun₂ : Runs w p ω (tourSetValNodeBody C.splay.splay C.setVal)
      (startState [nodesBase b vCap eCap, uNew, opN, mkN, v + 1, 2 * eCap + 2, heap] st₁.mem st₁.pos) o₂ st₂ c₂)
    (hrun₃ : Runs w p ω (tourRotateFrontBody C.splay.splay C.detachLeft C.join)
      (startState [nodesBase b vCap eCap, uNew, 2 * eCap + 2, heap] st₂.mem st₂.pos) o₃ st₃ c₃) :
    ∃ rOut cOut, rOut 3 = heap ∧ cOut ≤ c₁ + c₂ + c₃ + 140 ∧
      Runs w p ω
        (.assign 11 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
         .assign 12 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
         .assign 13 (.bin .add (.reg 11) (.bin .mul (.const 17) (.reg 9))) ;;
         .assign 14 (.load (.bin .add (.reg 13) (.const 9))) ;;
         .assign 15 (.load (.bin .add (.reg 13) (.const 10))) ;;
         .assign 16 (.const 0) ;;
         .call 17 C.setValNode [.reg 11, .reg 9, .reg 14, .reg 15, .reg 16, .reg 12, .reg 3] ;;
         .assign 13 (.bin .add (.reg 11) (.bin .mul (.const 17) (.reg 7))) ;;
         .assign 14 (.load (.bin .add (.reg 13) (.const 9))) ;;
         .assign 15 (.load (.bin .add (.reg 13) (.const 10))) ;;
         .assign 16 (.bin .add (.reg 1) (.const 1)) ;;
         .call 17 C.setValNode [.reg 11, .reg 7, .reg 14, .reg 15, .reg 16, .reg 12, .reg 3] ;;
         .call 17 C.rotateFront [.reg 11, .reg 7, .reg 12, .reg 3])
        ⟨mem1, rIn, pos⟩ .normal ⟨st₃.mem, rOut, st₃.pos⟩ cOut := by
  have hb_lt : b + 16 < 2 ^ w ∧ v + 1 < 2 ^ w := by
    simp only [ordHandleOf, tourFixedSize] at hord_le; omega
  set r1 := Function.update rIn 11 (nodesBase b vCap eCap)
  set r2 := Function.update r1 12 (2 * eCap + 2)
  set r3 := Function.update r2 13 (nodesBase b vCap eCap + 17 * uOld)
  set r4 := Function.update r3 14 opO
  set r5 := Function.update r4 15 mkO
  set r6 := Function.update r5 16 0
  set s_1 : State := { st₁ with regs := Function.update r6 17 o₁.value }
  set r7 := Function.update s_1.regs 13 (nodesBase b vCap eCap + 17 * uNew)
  set r8 := Function.update r7 14 opN
  set r9 := Function.update r8 15 mkN
  set r10 := Function.update r9 16 (v + 1)
  set s_2 : State := { st₂ with regs := Function.update r10 17 o₂.value }
  set s_3 : State := { st₃ with regs := Function.update s_2.regs 17 o₃.value }
  have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 11) (rBase := 0) (off := HDR_NODES_BASE)
    (b := b) (val := nodesBase b vCap eCap) (st := ⟨mem1, rIn, pos⟩) hr0
    (by simp [HDR_NODES_BASE]; omega) (by simp [HDR_NODES_BASE]; omega) hm_nb
  have ha2 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 12) (rBase := 0) (off := HDR_FUEL)
    (b := b) (val := 2 * eCap + 2) (st := ⟨mem1, r1, pos⟩) (by simp [r1, hr0])
    (by simp [HDR_FUEL]; omega) (by simp [HDR_FUEL]; omega) hm_fuel
  have ha3 := runs_assign_node_addr (w := w) (p := p) (ω := ω) (dst := 13) (rNb := 11) (rNode := 9)
    (nb := nodesBase b vCap eCap) (node := uOld) (st := ⟨mem1, r2, pos⟩)
    (by simp [r2, r1]) (by simp [r2, r1, hr9]) (by omega) (by omega) (by omega)
  have ha4 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 13) (off := 9)
    (b := nodesBase b vCap eCap + 17 * uOld) (val := opO) (st := ⟨mem1, r3, pos⟩) (by simp [r3])
    (by omega) (by omega) hm_opO
  have ha5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 15) (rBase := 13) (off := 10)
    (b := nodesBase b vCap eCap + 17 * uOld) (val := mkO) (st := ⟨mem1, r4, pos⟩) (by simp [r4, r3])
    (by omega) (by omega) hm_mkO
  have ha6 := runs_assign_const (w := w) (p := p) (ω := ω) (dst := 16) (val := 0) (st := ⟨mem1, r5, pos⟩) (by omega)
  have hc1 := tour_runs_call_of (r := 17) (args := [.reg 11, .reg 9, .reg 14, .reg 15, .reg 16, .reg 12, .reg 3])
    (st := ⟨mem1, r6, pos⟩) C.setValNode_body
    (by simp [evalArgs, Expr.eval, r6, r5, r4, r3, r2, r1, hr9, hr3]) hrun₁
  have ha7 := runs_assign_node_addr (w := w) (p := p) (ω := ω) (dst := 13) (rNb := 11) (rNode := 7)
    (nb := nodesBase b vCap eCap) (node := uNew) (st := s_1)
    (by simp [s_1, r6, r5, r4, r3, r2, r1]) (by simp [s_1, r6, r5, r4, r3, r2, r1, hr7])
    (by omega) (by omega) (by omega)
  have ha8 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 14) (rBase := 13) (off := 9)
    (b := nodesBase b vCap eCap + 17 * uNew) (val := opN) (st := ⟨st₁.mem, r7, st₁.pos⟩) (by simp [r7])
    (by omega) (by omega) hm1_opN
  have ha9 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 15) (rBase := 13) (off := 10)
    (b := nodesBase b vCap eCap + 17 * uNew) (val := mkN) (st := ⟨st₁.mem, r8, st₁.pos⟩) (by simp [r8, r7])
    (by omega) (by omega) hm1_mkN
  have ha10 := runs_assign_reg_add1 (w := w) (p := p) (ω := ω) (dst := 16) (rSrc := 1) (v := v)
    (st := ⟨st₁.mem, r9, st₁.pos⟩) (by simp [r9, r8, r7, s_1, r6, r5, r4, r3, r2, r1, hr1]) (by omega) (by omega)
  have hc2 := tour_runs_call_of (r := 17) (args := [.reg 11, .reg 7, .reg 14, .reg 15, .reg 16, .reg 12, .reg 3])
    (st := ⟨st₁.mem, r10, st₁.pos⟩) C.setValNode_body
    (by simp [evalArgs, Expr.eval, r10, r9, r8, r7, s_1, r6, r5, r4, r3, r2, r1, hr7, hr3]) hrun₂
  have hc3 := runs_call_regs4 17 11 7 12 3 (st := s_2) C.rotateFront_body
    (by simp [s_2, r10, r9, r8, r7, s_1, r6, r5, r4, r3, r2, r1])
    (by simp [s_2, r10, r9, r8, r7, s_1, r6, r5, r4, r3, r2, r1, hr7])
    (by simp [s_2, r10, r9, r8, r7, s_1, r6, r5, r4, r3, r2])
    (by simp [s_2, r10, r9, r8, r7, s_1, r6, r5, r4, r3, r2, r1, hr3]) hrun₃
  have hseq := tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
    (tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal hc1 (tour_runs_seq_normal ha7
      (tour_runs_seq_normal ha8 (tour_runs_seq_normal ha9 (tour_runs_seq_normal ha10 (tour_runs_seq_normal hc2 hc3)))))))))))
  refine ⟨s_3.regs, _, by simp [s_3, s_2, r10, r9, r8, r7, s_1, r6, r5, r4, r3, r2, r1, hr3], ?_, hseq⟩
  clear * -; simp only [argsSize, Expr.size]; omega

/-! ## Amortized verification for `tourEditRotateBody` -/

/-- Verified amortized tour-side run theorem for `rotateTo v (endOfKey keyY)`. -/
theorem tourEditRotateBody_runs {τ_ord : Type}
    {w vCap eCap b v keyY heap pos : ℕ} {p : Program}
    (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete τ_ord} {mem : ℕ → ℕ}
    (h : TourCoreAt vCap eCap b s x mem)
    (hvLt : v < vCap) (hkeyLt : keyY < 2 * eCap)
    (hord_le : ordHandleOf b vCap eCap ≤ heap)
    (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hzero : ZeroFrom mem heap) (hroom : heap + 2 < 2 ^ w) :
    ∃ st' c x',
      Runs w p ω (tourEditRotateBody C.setValNode C.rotateFront)
        (startState [b, v, keyY, heap] mem pos) (.returned heap) st' c ∧
      x'.ordX = x.ordX ∧
      ZeroFrom st'.mem heap ∧
      (∀ a, (a < b ∨ ordHandleOf b vCap eCap ≤ a) → a < heap → st'.mem a = mem a) ∧
      TourCoreAt vCap eCap b (tourApplyEdit s (.rotateTo v (endOfKey keyY))) x' st'.mem ∧
      c + TOUR_PHI_MULT * forestPhi x'.trees ≤
        TOUR_EDIT_SIMPLE_MUL * tourLog eCap + TOUR_PHI_MULT * forestPhi x.trees := by
  classical
  set y := endOfKey keyY
  set s' := tourApplyEdit s (.rotateTo v y)
  have hvalid' : TourValid vCap eCap s' := tourValid_applyEdit_rotateTo h.valid hvLt
  have hhdr := h.header
  set rawSlot := mem (slotOfVertBase b vCap eCap + v)
  have hdec : decodeSlot rawSlot v = x.slotOf v := h.slotOf_mem v hvLt
  have hsv_lt : x.slotOf v < vCap := (h.slot_bij v hvLt).1
  have hraw_le : rawSlot ≤ vCap := by unfold decodeSlot at hdec; split_ifs at hdec <;> omega
  set eo := mem (endOwnerBase b vCap eCap + keyY)
  have hgeo : b + 16 < 2 ^ w ∧ nodeOfEndBase b vCap + keyY < 2 ^ w ∧
      firstEndBase b + v < 2 ^ w ∧ isRootBase b vCap + v < 2 ^ w ∧ x.slotOf v + 1 < 2 ^ w := by
    simp only [ordHandleOf, tourFixedSize, nodeOfEndBase, firstEndBase, isRootBase] at hord_le ⊢; omega
  obtain ⟨rP, cP, hrP0, hrP1, hrP2, hrP3, hrP5, hrP6, hcP, hrunP⟩ :=
    tourEditRotate_prefix_exec (p := p) (pos := pos) ω hord_le hroom hwide hvLt hkeyLt (by omega)
      hhdr.2.2.2.2.2.2.2.2.2.2.2.1 hhdr.2.1 rfl hhdr.2.2.2.2.2.2.2.1 rfl
  rw [hdec] at hrP5
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hlog := tourLog_of_le h.numNodes_le
  have heo_iff : eo = x.slotOf v + 1 ↔ y ∈ s.ord v := by
    constructor
    · intro heq
      by_contra hnot
      by_cases hex : ∃ w', y ∈ s.ord w'
      · obtain ⟨w', hw'⟩ := hex
        have hw'Lt : w' < vCap := by
          by_contra hge; have := h.valid.ordWithin.2.1 w' (Nat.le_of_not_lt hge); rw [this] at hw'; simp at hw'
        have hact := (h.active_end w' hw'Lt y hw').2
        rw [endKey_endOfKey'] at hact
        have heq_sl : x.slotOf w' = x.slotOf v := by change eo = x.slotOf w' + 1 at hact; omega
        have hvw' : w' = v := by
          have h1 := (h.slot_bij w' hw'Lt).2.1; have h2 := (h.slot_bij v hvLt).2.1
          rw [← h1, heq_sl, h2]
        exact hnot (hvw' ▸ hw')
      · push Not at hex
        have h0 := h.inactive_owner keyY hkeyLt hex
        change eo = 0 at h0; omega
    · intro hy_mem
      have hact := (h.active_end v hvLt y hy_mem).2
      rw [endKey_endOfKey'] at hact; exact hact
  by_cases hy_mem : y ∈ s.ord v
  · have heo_eq : eo = x.slotOf v + 1 := heo_iff.mpr hy_mem
    have hcond_eo : (Expr.bin .eq (.reg 6) (.bin .add (.reg 5) (.const 1))).eval w ⟨mem, rP, pos⟩ = some 1 := by
      dsimp only [eo] at heo_eq
      simp [Expr.eval, hrP5, hrP6, heo_eq, BinOp.eval, (by omega : 1 < 2 ^ w), hgeo.2.2.2.2]
    obtain ⟨_, hrR, _, _, huN_pos, huN_le, huN_key, t, rest, hct, hperm, ht_map, huN_t⟩ :=
      h.mem_compTree_of_active hy_mem
    rw [endKey_endOfKey'] at huN_pos huN_le huN_key huN_t
    set uNew := x.nodeOf keyY
    have hord_ne : s.ord v ≠ [] := List.ne_nil_of_mem hy_mem
    obtain ⟨aOld, haOld⟩ : ∃ aOld, (s.ord v).head? = some aOld :=
      Option.isSome_iff_exists.mp (by cases ho : s.ord v <;> simp_all)
    have haOld_mem : aOld ∈ s.ord v := List.mem_of_head? haOld
    obtain ⟨_, _, _, _, huO_pos, huO_le, huO_key, tO, _, hctO, _, _, huO_tO⟩ :=
      h.mem_compTree_of_active haOld_mem
    set uOld := x.nodeOf (endKey aOld)
    have htO_eq : tO = t := Option.some.inj (hctO.symm.trans hct)
    subst tO
    have hm_fev : mem (firstEndBase b + v) = uOld := by rw [h.firstEnd_mem v hvLt, haOld]
    set rA1 := Function.update rP 7 (nodeOfEndBase b vCap)
    set rA2 := Function.update rA1 7 uNew
    set rA3 := Function.update rA2 8 (firstEndBase b)
    set rA4 := Function.update rA3 9 uOld
    have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 0) (off := HDR_NODE_OF_END)
      (b := b) (val := nodeOfEndBase b vCap) (st := ⟨mem, rP, pos⟩) hrP0
      (by simp [HDR_NODE_OF_END]; omega) (by simp [HDR_NODE_OF_END]; omega) hhdr.2.2.2.2.2.2.1
    have ha2 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 7) (rIdx := 2)
      (base := nodeOfEndBase b vCap) (idx := keyY) (val := uNew) (st := ⟨mem, rA1, pos⟩)
      (by simp [rA1]) (by simp [rA1, hrP2]) hgeo.2.1 (h.nodeOf_mem keyY hkeyLt).1
    have ha3 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 8) (rBase := 0) (off := HDR_FIRST_END)
      (b := b) (val := firstEndBase b) (st := ⟨mem, rA2, pos⟩) (by simp [rA2, rA1, hrP0])
      (by simp [HDR_FIRST_END]; omega) (by simp [HDR_FIRST_END]; omega) hhdr.2.2.2.2.1
    have ha4 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 9) (rBase := 8) (rIdx := 1)
      (base := firstEndBase b) (idx := v) (val := uOld) (st := ⟨mem, rA3, pos⟩)
      (by simp [rA3]) (by simp [rA3, rA2, rA1, hrP1]) hgeo.2.2.1 hm_fev
    by_cases heq_u : uNew = uOld
    · -- Already at head: rotateTo is a no-op!
      have hy_eq_old : y = aOld := by
        have hk : keyY = endKey aOld := by rw [← huN_key, heq_u, huO_key]
        rw [← endOfKey_endKey' aOld, ← hk]
      have hs'_eq : s' = s := by
        have hord_eq : applyOrdEdit s.ord (.rotateTo v y) = s.ord := by
          funext w'
          by_cases hwv : w' = v
          · subst hwv
            simp only [applyOrdEdit, Function.update_self]
            rw [hy_eq_old]; cases hl : s.ord w' with
            | nil => simp [hl] at haOld
            | cons a as =>
              rw [hl] at haOld; cases Option.some.inj haOld
              simp [rotateToList, List.idxOf_cons_self]
          · simp [applyOrdEdit, Function.update_of_ne hwv]
        cases s; simpa [s', tourApplyEdit] using hord_eq
      have hcond_eq : (Expr.bin .eq (.reg 7) (.reg 9)).eval w ⟨mem, rA4, pos⟩ = some 1 := by
        simp [Expr.eval, rA4, rA3, rA2, heq_u, BinOp.eval, (by omega : 1 < 2 ^ w)]
      have hfull : Runs w p ω (tourEditRotateBody C.setValNode C.rotateFront)
          (startState [b, v, keyY, heap] mem pos) (.returned heap) ⟨mem, rA4, pos⟩ _ :=
        runs_seqAppend hrunP (tour_runs_seq_normal
          (tour_runs_cond_true hcond_eo (by omega)
            (tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3
              (tour_runs_seq_normal ha4 (tour_runs_cond_true hcond_eq (by omega)
                (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)))))))
          (runs_ret_reg (w := w) (p := p) (ω := ω) (st := ⟨mem, rA4, pos⟩) (r := 3) (v := heap)
            (by simp [rA4, rA3, rA2, rA1, hrP3])))
      refine ⟨⟨mem, rA4, pos⟩, _, x, hfull, rfl, hzero, fun _ _ _ => rfl, hs'_eq ▸ h, ?_⟩
      clear * - hcP htl; simp only [Expr.size, TOUR_EDIT_SIMPLE_MUL] at hcP htl ⊢; omega
    · -- `uNew ≠ uOld`: store `firstEnd[v] := uNew`, then check `isRoot[v]`.
      have hy_ne_old : y ≠ aOld := fun hEq => heq_u (by dsimp only [uNew, uOld]; rw [← hEq, endKey_endOfKey'])
      have hcond_eq : (Expr.bin .eq (.reg 7) (.reg 9)).eval w ⟨mem, rA4, pos⟩ = some 0 := by
        simp [Expr.eval, rA4, rA3, rA2, heq_u, BinOp.eval, (by omega : 0 < 2 ^ w)]
      set mem1 := Function.update mem (firstEndBase b + v) uNew
      have hst1 : Runs w p ω (.store (.bin .add (.reg 8) (.reg 1)) (.reg 7))
          ⟨mem, rA4, pos⟩ .normal ⟨mem1, rA4, pos⟩ 5 :=
        runs_store_iff.mpr ⟨firstEndBase b + v, uNew,
          by simp [Expr.eval, rA4, rA3, rA2, rA1, hrP1, BinOp.eval, hgeo.2.2.1],
          by simp [Expr.eval, rA4, rA3, rA2], rfl, rfl, rfl⟩
      set rB1 := Function.update rA4 10 (isRootBase b vCap)
      set irV := if v ∈ s.rf.R then 1 else 0
      set rB2 := Function.update rB1 10 irV
      have hm1_irB : mem1 (b + HDR_IS_ROOT) = isRootBase b vCap := by
        dsimp only [mem1]; rw [Function.update_of_ne (by simp [HDR_IS_ROOT, firstEndBase]; omega)]; exact hhdr.2.2.2.2.2.1
      have hm1_irV : mem1 (isRootBase b vCap + v) = irV := by
        dsimp only [mem1]; rw [Function.update_of_ne (by simp [isRootBase, firstEndBase]; omega)]; exact h.isRoot_mem v hvLt
      have hb1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 10) (rBase := 0) (off := HDR_IS_ROOT)
        (b := b) (val := isRootBase b vCap) (st := ⟨mem1, rA4, pos⟩) (by simp [rA4, rA3, rA2, rA1, hrP0])
        (by simp [HDR_IS_ROOT]; omega) (by simp [HDR_IS_ROOT]; omega) hm1_irB
      have hb2 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 10) (rBase := 10) (rIdx := 1)
        (base := isRootBase b vCap) (idx := v) (val := irV) (st := ⟨mem1, rB1, pos⟩)
        (by simp [rB1]) (by simp [rB1, rA4, rA3, rA2, rA1, hrP1]) hgeo.2.2.2.1 hm1_irV
      have hord'_mem : ∀ w' z, z ∈ s'.ord w' ↔ z ∈ s.ord w' := fun w' z => by
        by_cases hwv : w' = v
        · subst hwv; simp only [s', tourApplyEdit, applyOrdEdit, Function.update_self]
          exact rotateToList_isRotated.perm.mem_iff.symm
        · simp [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hwv]
      have hft_other : ∀ r' ∈ s.rf.R, r' ≠ v →
          fullTour s'.ord s'.rf.F hvalid'.compat.forest r' = fullTour s.ord s.rf.F h.valid.compat.forest r' := by
        intro r' hr' hr'v
        have hrot := fullTour_rotateTo h.valid.compat v y r'
        have hord_r' : s'.ord r' = s.ord r' := by simp [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hr'v]
        by_cases hnil : s.ord r' = []
        · rw [(fullTour_eq_nil_iff hvalid'.compat r').mpr (by rw [hord_r', hnil]),
              (fullTour_eq_nil_iff h.valid.compat r').mpr hnil]
        · obtain ⟨ar, har⟩ : ∃ ar, (s.ord r').head? = some ar :=
            Option.isSome_iff_exists.mp (by cases ho : s.ord r' <;> simp_all)
          have har' : (s'.ord r').head? = some ar := by rw [hord_r']; exact har
          have h1 := tour_rotateToList_eq_of_isRotated (fullTour_spec hvalid'.compat r').1 hrot (fullTour_head? hvalid'.compat r' har')
          have h2 := tour_rotateToList_eq_of_isRotated (fullTour_spec h.valid.compat r').1 (List.IsRotated.refl _) (fullTour_head? h.valid.compat r' har)
          exact h1.symm.trans h2
      by_cases hvR : v ∈ s.rf.R
      · -- `v ∈ s.rf.R`: update rootTag on `uOld` and `uNew`, then `rotateFront(uNew)`
        have hir1 : irV = 1 := by simp [irV, hvR]
        have hrv_eq : s.rf.root v = v := h.valid.root_eq_of_mem (h.valid.roots_sub hvR) hvR (connected_refl _ _)
        rw [hrv_eq] at hct ht_map
        have huO_cap : uOld ≤ x.numNodes := huO_le
        have huN_cap : uNew ≤ x.numNodes := huN_le
        have hnodes1 : tourLayout.NodesAt mem1 (nodesBase b vCap eCap) x.numNodes x.st :=
          NodesAt.congr tourLayout h.nodesAt fun a ha => by
            dsimp only [mem1]; rw [Function.update_of_ne (fun heq => by
              have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [firstEndBase, nodesBase] at heq this; omega)]
        have hheap1 : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes heap 2 mem1 :=
          ⟨by have hnn := h.numNodes_le; rw [← nodesBase_end_eq b vCap eCap] at hord_le; simp only [nodeAddr, tourLayout_stride]; omega,
           hroom, fun a ha => by dsimp only [mem1]; rw [Function.update_of_ne (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]; exact hzero a ha,
           hwide⟩
        set opO := if (x.st.nodes uOld).val.isOpen then 1 else 0
        set mkO := if (x.st.nodes uOld).val.isMarked then 1 else 0
        have hm1_opO : mem1 (nodesBase b vCap eCap + 17 * uOld + 9) = opO := nodesAt_isOpen hnodes1 huO_cap
        have hm1_mkO : mem1 (nodesBase b vCap eCap + 17 * uOld + 10) = mkO := nodesAt_isMarked hnodes1 huO_cap
        have hf_perm := (h.forestInv.perm hperm).1
        obtain ⟨t₁, s₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, _, _, hlist₁, hvalO₁, hvalne₁, _, hcost₁⟩ :=
          tourSetValNodeBody_runs (isOpen := opO) (isMarked := mkO) (rootTag := 0)
            (fuel := 2 * eCap + 2) (pos := pos) C ω hnodes1 hf_perm (h.valsOk hw)
            huO_tO (by omega) (by have := h.numNodes_le; omega) (by omega) hheap1
        set opN := if (s₁.nodes uNew).val.isOpen then 1 else 0
        set mkN := if (s₁.nodes uNew).val.isMarked then 1 else 0
        have hm2_opN : st₁.mem (nodesBase b vCap eCap + 17 * uNew + 9) = opN := nodesAt_isOpen hn₁ huN_cap
        have hm2_mkN : st₁.mem (nodesBase b vCap eCap + 17 * uNew + 10) = mkN := nodesAt_isMarked hn₁ huN_cap
        have huN_t1 : uNew ∈ t₁.toList := by rw [hlist₁]; exact huN_t
        obtain ⟨t₂, s₂, o₂, st₂, c₂, hrun₂, hn₂, hfr₂, hinv₂, hvals₂, _, _, hlist₂, hvalN₂, hvalne₂, _, hcost₂⟩ :=
          tourSetValNodeBody_runs (isOpen := opN) (isMarked := mkN) (rootTag := v + 1)
            (fuel := 2 * eCap + 2) (pos := st₁.pos) C ω hn₁ hinv₁ hvals₁
            huN_t1 (by omega) (by have := h.numNodes_le; omega) (by omega) ⟨hheap1.rec_le, hroom, hfr₁.1, hwide⟩
        have huN_t2 : uNew ∈ t₂.toList := by rw [hlist₂]; exact huN_t1
        obtain ⟨t₃, s₃, o₃, st₃, c₃, hrun₃, _, hn₃, hfr₃, hinv₃, _, _, hrot₃, hval₃, _, hcost₃⟩ :=
          tourRotateFrontBody_runs (fuel := 2 * eCap + 2) (pos := st₂.pos) C.toTourSplayOpsProcs ω
            hn₂ hinv₂ hvals₂ huN_t2 (by have := h.numNodes_le; omega) (by omega) ⟨hheap1.rec_le, hroom, hfr₂.1, hwide⟩
        have ht₃_map : t₃.toList.map (fun id => endOfKey (x.keyOf id)) =
            fullTour s'.ord s'.rf.F hvalid'.compat.forest v := by
          rw [hrot₃, hlist₂, hlist₁]
          have hnd : (t.toList.map fun id => endOfKey (x.keyOf id)).Nodup := by
            rw [ht_map]; exact (fullTour_spec h.valid.compat v).1
          rw [rotateNatList_map_of_nodup' hnd huN_t, huN_key, ht_map]
          have hrot_ft := fullTour_rotateTo h.valid.compat v y v
          have hy_hd : (s'.ord v).head? = some y := by
            simp only [s', tourApplyEdit, applyOrdEdit, Function.update_self]
            exact rotateToList_head?_of_mem hy_mem
          exact rotateToList_fullTour_of_isRotated hvalid'.compat hy_hd hrot_ft
        have hfr13 : TreeFrame tourLayout (nodesBase b vCap eCap) x.numNodes heap mem1 st₃.mem :=
          hfr₁.trans (hfr₂.trans hfr₃)
        have hpre_eq : ∀ a < nodesBase b vCap eCap, st₃.mem a = mem1 a := fun a ha =>
          hfr13.2 a (by simp only [nodesBase, ordHandleOf, tourFixedSize] at ha hord_le ⊢; omega)
            (not_inRecords_of_lt_nodesBase ha)
        have hpre_eq_mem : ∀ a < nodesBase b vCap eCap, a ≠ firstEndBase b + v → st₃.mem a = mem a := fun a ha hne => by
          rw [hpre_eq a ha]; exact Function.update_of_ne hne _ _
        have hhdr' : TourHeaderAt vCap eCap b x.numNodes st₃.mem := by
          rcases hhdr with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
          have hf : ∀ k < 16, st₃.mem (b + k) = mem (b + k) := fun k hk =>
            hpre_eq_mem (b + k) (by simp [nodesBase]; omega) (by simp [firstEndBase]; omega)
          exact ⟨by rw [hf _ (by decide)]; exact h0, by rw [hf _ (by decide)]; exact h1,
            by rw [hf _ (by decide)]; exact h2, by rw [hf _ (by decide)]; exact h3,
            by rw [hf _ (by decide)]; exact h4, by rw [hf _ (by decide)]; exact h5,
            by rw [hf _ (by decide)]; exact h6, by rw [hf _ (by decide)]; exact h7,
            by rw [hf _ (by decide)]; exact h8, by rw [hf _ (by decide)]; exact h9,
            by rw [hf _ (by decide)]; exact h10, by rw [hf _ (by decide)]; exact h11,
            by rw [hf _ (by decide)]; exact h12, by rw [hf _ (by decide)]; exact h13,
            by rw [hf _ (by decide)]; exact h14⟩
        have ht_not_rest : t ∉ rest := by
          intro hm
          have hnd := hf_perm.nodupAll
          rw [List.flatMap_cons, List.nodup_append] at hnd
          exact hnd.2.2 uNew huN_t uNew (List.mem_flatMap.mpr ⟨t, hm, huN_t⟩) rfl
        have hcomp_inj : ∀ r' ∈ s.rf.R, r' ≠ v → x.compTree r' ≠ some t := by
          intro r' hr' hne hcr'
          have hft' : fullTour s.ord s.rf.F h.valid.compat.forest r' ≠ [] := fun hnil => by
            have := h.comp_none r' hr' hnil; rw [hcr'] at this; simp at this
          obtain ⟨t', hct', _, ht'_map⟩ := h.comp_some r' hr' hft'
          have ht'eq : t' = t := Option.some.inj (hct'.symm.trans hcr'); subst ht'eq
          have he1 : endOfKey (x.keyOf uNew) ∈ fullTour s.ord s.rf.F h.valid.compat.forest v := by
            rw [← ht_map]; exact List.mem_map_of_mem huN_t
          have he2 : endOfKey (x.keyOf uNew) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r' := by
            rw [← ht'_map]; exact List.mem_map_of_mem huN_t
          obtain ⟨w1, hw1, hc1⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he1
          obtain ⟨w2, hw2, hc2⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he2
          have hw12 : w1 = w2 := h.valid.compat.unique w1 w2 _ hw1 hw2; subst hw12
          have hvF := h.valid.compat.vert w1 (List.ne_nil_of_mem hw1)
          exact hne ((h.valid.root_eq_of_mem hvF hr' (connected_symm hc2)).symm.trans
            (h.valid.root_eq_of_mem hvF hvR (connected_symm hc1)))
        set x' : TourConcrete τ_ord := { x with st := s₃, trees := t₃ :: rest, compTree := Function.update x.compTree v (some t₃) }
        have hcore' : TourCoreAt vCap eCap b s' x' st₃.mem :=
          { valid := hvalid'
            header := hhdr'
            numNodes_le := h.numNodes_le
            nodeOf_mem := fun k hk => by
              rw [hpre_eq_mem _ (by simp [nodeOfEndBase, nodesBase]; omega) (by simp [nodeOfEndBase, firstEndBase]; omega)]
              exact h.nodeOf_mem k hk
            nodeOf_keyOf := h.nodeOf_keyOf
            keyOf_mem := fun u h1 h2 => by
              dsimp only [x'] at h2; have := h.numNodes_le
              rw [hpre_eq_mem _ (by simp [keyOfNodeBase, nodesBase]; omega) (by simp [keyOfNodeBase, firstEndBase]; omega)]
              exact h.keyOf_mem u h1 h2
            firstEnd_mem := fun w' hw' => by
              rw [hpre_eq _ (by simp [firstEndBase, nodesBase]; omega)]
              by_cases hwv : w' = v
              · subst hwv; simp only [mem1, Function.update_self, s', tourApplyEdit, applyOrdEdit,
                  rotateToList_head?_of_mem hy_mem, uNew, x', y, endKey_endOfKey']
              · rw [show mem1 (firstEndBase b + w') = mem (firstEndBase b + w') from Function.update_of_ne (by omega) _ _,
                  h.firstEnd_mem w' hw']
                simp [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hwv, x']
            isRoot_mem := fun w' hw' => by
              rw [hpre_eq_mem _ (by simp [isRootBase, nodesBase]; omega) (by simp [isRootBase, firstEndBase]; omega)]
              exact h.isRoot_mem w' hw'
            slot_bij := h.slot_bij
            slotOf_mem := fun w' hw' => by
              rw [hpre_eq_mem _ (by simp [slotOfVertBase, nodesBase]; omega) (by simp [slotOfVertBase, firstEndBase]; omega)]
              exact h.slotOf_mem w' hw'
            vertOf_mem := fun sl hsl => by
              rw [hpre_eq_mem _ (by simp [vertOfSlotBase, nodesBase]; omega) (by simp [vertOfSlotBase, firstEndBase]; omega)]
              exact h.vertOf_mem sl hsl
            active_end := fun w' hw' z hz => by
              have hz0 := (hord'_mem w' z).mp hz
              have hzLt : endKey z < 2 * eCap := by
                have := h.valid.ordWithin.2.2 w' z hz0; simp only [endKey]; cases z.2 <;> simp <;> omega
              rw [hpre_eq_mem _ (by simp [endOwnerBase, nodesBase]; omega) (by simp [endOwnerBase, firstEndBase]; omega)]
              exact h.active_end w' hw' z hz0
            inactive_owner := fun k hk hno => by
              rw [hpre_eq_mem _ (by simp [endOwnerBase, nodesBase]; omega) (by simp [endOwnerBase, firstEndBase]; omega)]
              exact h.inactive_owner k hk fun w' hw' => hno w' ((hord'_mem w' _).mpr hw')
            markArr_zero := fun k hk => by
              rw [hpre_eq_mem _ (by simp [markArrBase, nodesBase]; omega) (by simp [markArrBase, firstEndBase]; omega)]
              exact h.markArr_zero k hk
            nodesAt := hn₃
            forestInv := hinv₃
            nodes_exact := fun id => by
              have h1 : id ∈ t₃.toList ↔ id ∈ t.toList := by
                rw [hrot₃, hlist₂, hlist₁]; exact (rotateNatList_perm huN_t).mem_iff
              have h2 : id ∈ (t₃ :: rest).flatMap AuxTree.toList ↔ id ∈ (t :: rest).flatMap AuxTree.toList := by
                simp only [List.flatMap_cons, List.mem_append, h1]
              have h3 : id ∈ (t :: rest).flatMap AuxTree.toList ↔ id ∈ x.trees.flatMap AuxTree.toList := by
                simp only [List.mem_flatMap]
                exact ⟨fun ⟨a, ha, hi⟩ => ⟨a, hperm.mem_iff.mpr ha, hi⟩, fun ⟨a, ha, hi⟩ => ⟨a, hperm.mem_iff.mp ha, hi⟩⟩
              exact h2.trans (h3.trans (h.nodes_exact id))
            comp_none := fun r' hr' hnil => by
              have hne : r' ≠ v := fun heq => by
                subst heq; rw [← ht₃_map] at hnil
                exact List.ne_nil_of_mem ((rotateNatList_perm huN_t).mem_iff.mpr huN_t)
                  (by rw [← hlist₁, ← hlist₂, ← hrot₃]; exact List.map_eq_nil_iff.mp hnil)
              rw [hft_other r' hr' hne] at hnil
              simp only [x', Function.update_of_ne hne]; exact h.comp_none r' hr' hnil
            comp_some := fun r' hr' hne_ft => by
              by_cases hr'v : r' = v
              · subst hr'v; exact ⟨t₃, by simp [x'], by simp [x'], ht₃_map⟩
              · rw [hft_other r' hr' hr'v] at hne_ft ⊢
                obtain ⟨tr', hctr', htr'_mem, htr'_map⟩ := h.comp_some r' hr' hne_ft
                have htr'_rest : tr' ∈ rest :=
                  (List.mem_cons.mp (hperm.mem_iff.mp htr'_mem)).resolve_left fun heq => hcomp_inj r' hr' hr'v (heq ▸ hctr')
                exact ⟨tr', by simp [x', Function.update_of_ne hr'v, hctr'], by simp [x', htr'_rest], htr'_map⟩
            tree_class := fun tr htr => by
              simp only [x', List.mem_cons] at htr
              rcases htr with rfl | hrest
              · exact Or.inl ⟨v, hvR, by simp [x']⟩
              · have htr_mem : tr ∈ x.trees := hperm.mem_iff.mpr (by simp [hrest])
                rcases h.tree_class tr htr_mem with ⟨r', hr', hcr'⟩ | ⟨u, huEq, hno⟩
                · have hne : r' ≠ v := fun heq => by subst heq; exact ht_not_rest ((Option.some.inj (hcr'.symm.trans hct)) ▸ hrest)
                  exact Or.inl ⟨r', hr', by simp [x', Function.update_of_ne hne, hcr']⟩
                · exact Or.inr ⟨u, huEq, fun w' hw' => hno w' ((hord'_mem w' _).mp hw')⟩
            inactive_single := fun id h1 h2 hno => by
              have hno0 : ∀ w', endOfKey (x.keyOf id) ∉ s.ord w' := fun w' hw' => hno w' ((hord'_mem w' _).mpr hw')
              have hmem := h.inactive_single id h1 h2 hno0
              have hne : AuxTree.node id .leaf .leaf ≠ t := fun heq => by
                have he' : endOfKey (x.keyOf id) ∈ fullTour s.ord s.rf.F h.valid.compat.forest v := by
                  rw [← ht_map, ← heq]; simp [AuxTree.toList]
                obtain ⟨w', hw', _⟩ := ((fullTour_spec h.valid.compat _).2 _).mp he'
                exact hno0 w' hw'
              have hrest : AuxTree.node id .leaf .leaf ∈ rest := (List.mem_cons.mp (hperm.mem_iff.mp hmem)).resolve_left hne
              simp [x', hrest]
            val_active := fun id h1 h2 hact => by
              dsimp only [x'] at h2 ⊢
              have hid_cap : id ≤ x.numNodes := h2
              have hact0 : ∃ w', endOfKey (x.keyOf id) ∈ s.ord w' := by
                obtain ⟨w', hw'⟩ := hact; exact ⟨w', (hord'_mem w' _).mp hw'⟩
              rw [hval₃ id hid_cap]
              by_cases hiN : id = uNew
              · subst id
                rw [hvalN₂]
                have hop : decide (0 < opN) = (s₁.nodes uNew).val.isOpen :=
                  (by intro b; cases b <;> rfl : ∀ b : Bool, decide (0 < if b then 1 else 0) = b) _
                have hmk : decide (0 < mkN) = (s₁.nodes uNew).val.isMarked :=
                  (by intro b; cases b <;> rfl : ∀ b : Bool, decide (0 < if b then 1 else 0) = b) _
                rw [hvalne₁ uNew huN_cap heq_u, h.val_active uNew h1 h2 hact0] at hop hmk
                have hy_hd : (s'.ord v).head? = some (endOfKey (x.keyOf uNew)) := by
                  rw [huN_key]; simp only [s', tourApplyEdit, applyOrdEdit, Function.update_self]
                  exact rotateToList_head?_of_mem hy_mem
                rw [hop, hmk, tourRootTagVal_eq_succ hvalid' hvR hy_hd]; rfl
              · rw [hvalne₂ id hid_cap hiN]
                by_cases hiO : id = uOld
                · subst id
                  rw [hvalO₁]
                  have hop : decide (0 < opO) = (x.st.nodes uOld).val.isOpen :=
                    (by intro b; cases b <;> rfl : ∀ b : Bool, decide (0 < if b then 1 else 0) = b) _
                  have hmk : decide (0 < mkO) = (x.st.nodes uOld).val.isMarked :=
                    (by intro b; cases b <;> rfl : ∀ b : Bool, decide (0 < if b then 1 else 0) = b) _
                  rw [h.val_active uOld h1 h2 hact0] at hop hmk
                  have hrt0 : tourRootTagVal s' (endOfKey (x.keyOf uOld)) = 0 := by
                    rw [huO_key, endOfKey_endKey']
                    refine tourRootTagVal_eq_zero fun r' hr' hh => ?_
                    by_cases hr'v : r' = v
                    · subst hr'v
                      have hy_hd : (s'.ord r').head? = some y := by
                        simp only [s', tourApplyEdit, applyOrdEdit, Function.update_self]
                        exact rotateToList_head?_of_mem hy_mem
                      exact hy_ne_old (Option.some.inj (hy_hd.symm.trans hh))
                    · have hm : aOld ∈ s.ord r' := (hord'_mem r' aOld).mp (List.mem_of_head? hh)
                      exact hr'v (h.valid.compat.unique r' v aOld hm haOld_mem)
                  rw [hop, hmk, hrt0]; rfl
                · rw [hvalne₁ id hid_cap hiO, h.val_active id h1 h2 hact0]
                  have hne_y : endOfKey (x.keyOf id) ≠ y := fun heq => hiN (by
                    have hk : x.keyOf id = keyY := by rw [← endKey_endOfKey' (x.keyOf id), heq, endKey_endOfKey']
                    exact (h.keyOf_mem id h1 h2).2.2.symm.trans (by rw [hk]))
                  have hne_aO : endOfKey (x.keyOf id) ≠ aOld := fun heq => hiO (by
                    have hk : x.keyOf id = endKey aOld := by rw [← endKey_endOfKey' (x.keyOf id), heq]
                    exact (h.keyOf_mem id h1 h2).2.2.symm.trans (by rw [hk]))
                  have hrt_eq : tourRootTagVal s' (endOfKey (x.keyOf id)) = tourRootTagVal s (endOfKey (x.keyOf id)) := by
                    by_cases hex : ∃ r' ∈ s.rf.R, (s.ord r').head? = some (endOfKey (x.keyOf id))
                    · obtain ⟨r', hr'R, hr'h⟩ := hex
                      have hr'v : r' ≠ v := fun heq => hne_aO (Option.some.inj (hr'h.symm.trans (heq ▸ haOld)))
                      have hr'h' : (s'.ord r').head? = some (endOfKey (x.keyOf id)) := by
                        simpa [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hr'v] using hr'h
                      rw [tourRootTagVal_eq_succ h.valid hr'R hr'h, tourRootTagVal_eq_succ hvalid' hr'R hr'h']
                    · push Not at hex
                      rw [tourRootTagVal_eq_zero hex, tourRootTagVal_eq_zero]
                      intro r' hr' hh
                      by_cases hr'v : r' = v
                      · subst hr'v
                        have hy_hd : (s'.ord r').head? = some y := by
                          simp only [s', tourApplyEdit, applyOrdEdit, Function.update_self]
                          exact rotateToList_head?_of_mem hy_mem
                        exact hne_y (Option.some.inj (hh.symm.trans hy_hd))
                      · exact hex r' hr' (by simpa [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hr'v] using hh)
                  rw [hrt_eq]; rfl
            val_inactive_rt := fun id h1 h2 hno => by
              dsimp only [x'] at h2 ⊢
              have hid_cap : id ≤ x.numNodes := h2
              have hno0 : ∀ w', endOfKey (x.keyOf id) ∉ s.ord w' := fun w' hw' => hno w' ((hord'_mem w' _).mpr hw')
              have hiN : id ≠ uNew := fun heq => by subst id; rw [huN_key] at hno0; exact hno0 v hy_mem
              have hiO : id ≠ uOld := fun heq => by subst id; rw [huO_key, endOfKey_endKey'] at hno0; exact hno0 v haOld_mem
              rw [hval₃ id hid_cap, hvalne₂ id hid_cap hiN, hvalne₁ id hid_cap hiO]
              exact h.val_inactive_rt id h1 h2 hno0
            val_unused_rt := fun id hid hcond => by
              dsimp only [x'] at hcond
              have hiN : id ≠ uNew := by omega
              have hiO : id ≠ uOld := by omega
              rw [hval₃ id hid, hvalne₂ id hid hiN, hvalne₁ id hid hiO]
              exact h.val_unused_rt id hid hcond }
        have hm1_nb : mem1 (b + HDR_NODES_BASE) = nodesBase b vCap eCap := by
          dsimp only [mem1]; rw [Function.update_of_ne (by simp [HDR_NODES_BASE, firstEndBase]; omega)]; exact hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hm1_fuel : mem1 (b + HDR_FUEL) = 2 * eCap + 2 := by
          dsimp only [mem1]; rw [Function.update_of_ne (by simp [HDR_FUEL, firstEndBase]; omega)]; exact hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        obtain ⟨rOut, cOut, hrOut3, hcOut, hrunRoot⟩ := tourEditRotate_rootBlock_exec (rIn := rB2) C ω hord_le hroom hwide hvLt
          (by simpa [nodeAddr, tourLayout_stride] using hheap1.addr_lt huO_cap)
          (by simpa [nodeAddr, tourLayout_stride] using hheap1.addr_lt huN_cap)
          (by simp [rB2, rB1, rA4, rA3, rA2, rA1, hrP0])
          (by simp [rB2, rB1, rA4, rA3, rA2, rA1, hrP1])
          (by simp [rB2, rB1, rA4, rA3, rA2, rA1, hrP3])
          (by simp [rB2, rB1, rA4, rA3, rA2])
          (by simp [rB2, rB1, rA4])
          hm1_nb hm1_fuel hm1_opO hm1_mkO hrun₁ hm2_opN hm2_mkN hrun₂ hrun₃
        have hcond_ir : (Expr.reg 10).eval w ⟨mem1, rB2, pos⟩ = some 1 := by simp [Expr.eval, rB2, hir1]
        have hfull : Runs w p ω (tourEditRotateBody C.setValNode C.rotateFront)
            (startState [b, v, keyY, heap] mem pos) (.returned heap) ⟨st₃.mem, rOut, st₃.pos⟩ _ :=
          runs_seqAppend hrunP (tour_runs_seq_normal
            (tour_runs_cond_true hcond_eo (by omega)
              (tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
                (tour_runs_cond_false hcond_eq
                  (tour_runs_seq_normal hst1 (tour_runs_seq_normal hb1 (tour_runs_seq_normal hb2
                    (tour_runs_cond_true hcond_ir (by omega) hrunRoot))))))))))
            (runs_ret_reg (w := w) (p := p) (ω := ω) (st := ⟨st₃.mem, rOut, st₃.pos⟩) (r := 3) (v := heap) hrOut3))
        refine ⟨⟨st₃.mem, rOut, st₃.pos⟩, _, x', hfull, rfl, hfr13.1, fun a ha hlt => ?_, hcore', ?_⟩
        · have hnr : ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a := fun hrec => by
            have := inRecords_lt_ordHandle_of_le h.numNodes_le hrec; simp [nodesBase] at this; rcases ha with h1 | h2 <;> omega
          rw [hfr13.2 a hlt hnr]; dsimp only [mem1]
          rw [Function.update_of_ne (fun heq => by simp [firstEndBase, ordHandleOf, tourFixedSize] at ha heq; rcases ha with h1 | h2 <;> omega)]
        · have hmul : (2 * TOUR_FIND_AMORT + TOUR_SEQ_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) ≤
              (2 * TOUR_FIND_AMORT + TOUR_SEQ_AMORT) * (2 * tourLog eCap) := Nat.mul_le_mul_left _ hlog
          dsimp only [x']; rw [forestPhi_perm hperm]
          clear * - hcost₁ hcost₂ hcost₃ hcP hcOut hmul htl
          simp only [Expr.size, TOUR_PHI_MULT, TOUR_FIND_AMORT, TOUR_SEQ_AMORT, TOUR_EDIT_SIMPLE_MUL] at *
          omega
      · -- `v ∉ s.rf.R`: only `firstEnd[v] := uNew` changed; all `fullTour`s and `rootTag`s unchanged!
        have hir0 : irV = 0 := by simp [irV, hvR]
        have hcond_ir : (Expr.reg 10).eval w ⟨mem1, rB2, pos⟩ = some 0 := by simp [Expr.eval, rB2, hir0]
        have hfull : Runs w p ω (tourEditRotateBody C.setValNode C.rotateFront)
            (startState [b, v, keyY, heap] mem pos) (.returned heap) ⟨mem1, rB2, pos⟩ _ :=
          runs_seqAppend hrunP (tour_runs_seq_normal
            (tour_runs_cond_true hcond_eo (by omega)
              (tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
                (tour_runs_cond_false hcond_eq
                  (tour_runs_seq_normal hst1 (tour_runs_seq_normal hb1 (tour_runs_seq_normal hb2
                    (tour_runs_cond_false hcond_ir (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)))))))))))
            (runs_ret_reg (w := w) (p := p) (ω := ω) (st := ⟨mem1, rB2, pos⟩) (r := 3) (v := heap)
              (by simp [rB2, rB1, rA4, rA3, rA2, rA1, hrP3])))
        have hpre_ne : ∀ a, a ≠ firstEndBase b + v → mem1 a = mem a := fun a hne => Function.update_of_ne hne _ _
        have hhdr' : TourHeaderAt vCap eCap b x.numNodes mem1 := by
          rcases hhdr with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
          have hf : ∀ k < 16, mem1 (b + k) = mem (b + k) := fun k hk => hpre_ne _ (by simp [firstEndBase]; omega)
          exact ⟨by rw [hf _ (by decide)]; exact h0, by rw [hf _ (by decide)]; exact h1,
            by rw [hf _ (by decide)]; exact h2, by rw [hf _ (by decide)]; exact h3,
            by rw [hf _ (by decide)]; exact h4, by rw [hf _ (by decide)]; exact h5,
            by rw [hf _ (by decide)]; exact h6, by rw [hf _ (by decide)]; exact h7,
            by rw [hf _ (by decide)]; exact h8, by rw [hf _ (by decide)]; exact h9,
            by rw [hf _ (by decide)]; exact h10, by rw [hf _ (by decide)]; exact h11,
            by rw [hf _ (by decide)]; exact h12, by rw [hf _ (by decide)]; exact h13,
            by rw [hf _ (by decide)]; exact h14⟩
        have hcore' : TourCoreAt vCap eCap b s' x mem1 :=
          { valid := hvalid'
            header := hhdr'
            numNodes_le := h.numNodes_le
            nodeOf_mem := fun k hk => by rw [hpre_ne _ (by simp [nodeOfEndBase, firstEndBase]; omega)]; exact h.nodeOf_mem k hk
            nodeOf_keyOf := h.nodeOf_keyOf
            keyOf_mem := fun u h1 h2 => by rw [hpre_ne _ (by simp [keyOfNodeBase, firstEndBase]; omega)]; exact h.keyOf_mem u h1 h2
            firstEnd_mem := fun w' hw' => by
              by_cases hwv : w' = v
              · subst hwv; simp only [mem1, Function.update_self, s', tourApplyEdit, applyOrdEdit,
                  rotateToList_head?_of_mem hy_mem, uNew, y, endKey_endOfKey']
              · rw [hpre_ne _ (by omega), h.firstEnd_mem w' hw']; simp [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hwv]
            isRoot_mem := fun w' hw' => by rw [hpre_ne _ (by simp [isRootBase, firstEndBase]; omega)]; exact h.isRoot_mem w' hw'
            slot_bij := h.slot_bij
            slotOf_mem := fun w' hw' => by rw [hpre_ne _ (by simp [slotOfVertBase, firstEndBase]; omega)]; exact h.slotOf_mem w' hw'
            vertOf_mem := fun sl hsl => by rw [hpre_ne _ (by simp [vertOfSlotBase, firstEndBase]; omega)]; exact h.vertOf_mem sl hsl
            active_end := fun w' hw' z hz => by
              rw [hpre_ne _ (by simp [endOwnerBase, firstEndBase]; omega)]
              exact h.active_end w' hw' z ((hord'_mem w' z).mp hz)
            inactive_owner := fun k hk hno => by
              rw [hpre_ne _ (by simp [endOwnerBase, firstEndBase]; omega)]
              exact h.inactive_owner k hk fun w' hw' => hno w' ((hord'_mem w' _).mpr hw')
            markArr_zero := fun k hk => by rw [hpre_ne _ (by simp [markArrBase, firstEndBase]; omega)]; exact h.markArr_zero k hk
            nodesAt := NodesAt.congr tourLayout h.nodesAt fun a ha =>
              hpre_ne a (fun heq => by have := (inRecords_lt_ordHandle_of_le h.numNodes_le ha).1; simp [firstEndBase, nodesBase] at heq this; omega)
            forestInv := h.forestInv
            nodes_exact := h.nodes_exact
            comp_none := fun r' hr' hnil => by
              have hne : r' ≠ v := fun heq => hvR (heq ▸ hr')
              rw [hft_other r' hr' hne] at hnil; exact h.comp_none r' hr' hnil
            comp_some := fun r' hr' hne_ft => by
              have hne : r' ≠ v := fun heq => hvR (heq ▸ hr')
              rw [hft_other r' hr' hne] at hne_ft ⊢; exact h.comp_some r' hr' hne_ft
            tree_class := fun tr htr => by
              rcases h.tree_class tr htr with h1 | ⟨u, huEq, hno⟩
              · exact Or.inl h1
              · exact Or.inr ⟨u, huEq, fun w' hw' => hno w' ((hord'_mem w' _).mp hw')⟩
            inactive_single := fun id h1 h2 hno =>
              h.inactive_single id h1 h2 fun w' hw' => hno w' ((hord'_mem w' _).mpr hw')
            val_active := fun id h1 h2 hact => by
              obtain ⟨w', hw'⟩ := hact
              rw [h.val_active id h1 h2 ⟨w', (hord'_mem w' _).mp hw'⟩]
              have hrt_eq : tourRootTagVal s' (endOfKey (x.keyOf id)) = tourRootTagVal s (endOfKey (x.keyOf id)) := by
                by_cases hex : ∃ r' ∈ s.rf.R, (s.ord r').head? = some (endOfKey (x.keyOf id))
                · obtain ⟨r', hr'R, hr'h⟩ := hex
                  have hr'v : r' ≠ v := fun heq => hvR (heq ▸ hr'R)
                  rw [tourRootTagVal_eq_succ h.valid hr'R hr'h,
                    tourRootTagVal_eq_succ hvalid' hr'R (by simpa [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hr'v] using hr'h)]
                · push Not at hex
                  rw [tourRootTagVal_eq_zero hex, tourRootTagVal_eq_zero]
                  intro r' hr' hh
                  have hr'v : r' ≠ v := fun heq => hvR (heq ▸ hr')
                  exact hex r' hr' (by simpa [s', tourApplyEdit, applyOrdEdit, Function.update_of_ne hr'v] using hh)
              rw [hrt_eq]; rfl
            val_inactive_rt := fun id h1 h2 hno => h.val_inactive_rt id h1 h2 fun w' hw' => hno w' ((hord'_mem w' _).mpr hw')
            val_unused_rt := h.val_unused_rt }
        refine ⟨⟨mem1, rB2, pos⟩, _, x, hfull, rfl,
          fun a ha => by dsimp only; rw [hpre_ne a (by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)]; exact hzero a ha,
          fun a ha _ => hpre_ne a (fun heq => by simp [firstEndBase, ordHandleOf, tourFixedSize] at ha heq; rcases ha with h1 | h2 <;> omega),
          hcore', ?_⟩
        clear * - hcP htl; simp only [Expr.size, TOUR_EDIT_SIMPLE_MUL] at hcP htl ⊢; omega
  · -- `y ∉ s.ord v`: `eo ≠ x.slotOf v + 1`, no-op!
    have heo_ne : eo ≠ x.slotOf v + 1 := mt heo_iff.mp hy_mem
    have hcond_eo : (Expr.bin .eq (.reg 6) (.bin .add (.reg 5) (.const 1))).eval w ⟨mem, rP, pos⟩ = some 0 := by
      dsimp only [eo] at heo_ne
      simp [Expr.eval, hrP5, hrP6, heo_ne, BinOp.eval, (by omega : 1 < 2 ^ w), hgeo.2.2.2.2, (by omega : 0 < 2 ^ w)]
    have hs'_eq : s' = s := by
      have hord_eq : applyOrdEdit s.ord (.rotateTo v y) = s.ord := by
        funext w'
        by_cases hwv : w' = v
        · subst hwv; simp [applyOrdEdit, rotateToList, hy_mem]
        · simp [applyOrdEdit, Function.update_of_ne hwv]
      cases s; simpa [s', tourApplyEdit] using hord_eq
    have hfull : Runs w p ω (tourEditRotateBody C.setValNode C.rotateFront)
        (startState [b, v, keyY, heap] mem pos) (.returned heap) ⟨mem, rP, pos⟩ _ :=
      runs_seqAppend hrunP (tour_runs_seq_normal
        (tour_runs_cond_false hcond_eo (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩))
        (runs_ret_reg (w := w) (p := p) (ω := ω) (st := ⟨mem, rP, pos⟩) (r := 3) (v := heap) hrP3))
    refine ⟨⟨mem, rP, pos⟩, _, x, hfull, rfl, hzero, fun _ _ _ => rfl, hs'_eq ▸ h, ?_⟩
    clear * - hcP htl; simp only [Expr.size, TOUR_EDIT_SIMPLE_MUL] at hcP htl ⊢; omega

end MinCostFlow.SparseCore.Program
