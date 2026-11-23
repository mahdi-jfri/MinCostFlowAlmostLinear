module

public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepLoopHelpers

import Mathlib.Tactic

/-!
# Single-iteration verification for `.delete e` (`AssemblyFirstTourStepIter`)

Provides `batchBodyAt_congr` and verifies the `.delete e` iteration of `asmFirstTourLoopBody`:
1. `tourBlock_iter_delete_prefix_runs`: loads `tag = 1`, `e`, and `isOpen(e)` into `r16..r21`.
2. `tourBlock_iter_forestDel_runs`: wraps `tourBlock_case_forestDel_runs` into a full iteration
   of `asmFirstTourLoopBody`.
3. `tourBlock_iter_nonForestDel_runs`: wraps `tourBlock_case_nonForestDel_runs` into a full
   iteration of `asmFirstTourLoopBody`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

public section

theorem batchBodyAt_congr {mem mem' : ℕ → ℕ} {G : MGraph} :
    ∀ {U : List Update} {a tot : ℕ},
      BatchBodyAt mem a G U tot → (∀ x, a ≤ x → x < a + tot → mem' x = mem x) →
      BatchBodyAt mem' a G U tot
  | [], _, _, h, _ => h
  | u :: U, a, tot, ⟨len, hle, hu, hrest⟩, hag => by
    refine ⟨len, hle, ?_, batchBodyAt_congr hrest (fun x h1 h2 => hag x (by omega) (by omega))⟩
    cases u with
    | insert e x y =>
      obtain ⟨rfl, hl⟩ := hu
      exact ⟨rfl, fun i hi => (hag (a + i) (by omega) (by simp at hi; omega)).trans (hl i hi)⟩
    | delete e =>
      obtain ⟨rfl, hl⟩ := hu
      exact ⟨rfl, fun i hi => (hag (a + i) (by omega) (by simp at hi; omega)).trans (hl i hi)⟩
    | split v v' St Sh =>
      rcases hu with ⟨Lt, Lh, h1, h2, h3, h4, hlen, hl⟩ | ⟨Lt, Lh, h1, h2, h3, h4, hlen, hl⟩
      · exact Or.inl ⟨Lt, Lh, h1, h2, h3, h4, hlen, fun i hi =>
          (hag (a + i) (by omega) (by simp at hi; omega)).trans (hl i hi)⟩
      · exact Or.inr ⟨Lt, Lh, h1, h2, h3, h4, hlen, fun i hi =>
          (hag (a + i) (by omega) (by simp at hi; omega)).trans (hl i hi)⟩

/-- Shared register-wrapping helper for the `.delete e` branch of `asmFirstTourLoopBody`:
given runs of `tag = 1` prefix (`r16..r21`) and the inner `isOpen = 0` conditional body,
produces a complete `Runs` of `asmFirstTourLoopBody` with `r12 += 2, r13 += 2, r14 += 1, r15 += 1`. -/
theorem tourBlock_iter_delete_wrap {w vCap eCap bSelf bTour bOut bCopy tourH uPtr ePtr eIdx i e hCur : ℕ}
    {p : Program} {ω : ℕ → Bool}
    {s : TourAbs} {tx : (tourAsmRep vCap eCap).τ} {st st1 : State} {cBody : ℕ}
    (hwide : 18 ≤ 2 ^ w) (hu_w : uPtr + 2 < 2 ^ w) (he_w : ePtr + 2 < 2 ^ w)
    (heIdx_w : eIdx + 1 < 2 ^ w) (hi_w : i + 1 < 2 ^ w) (hCur_w : hCur + 1 < 2 ^ w)
    (hr0 : st.regs 0 = tourH) (hr12 : st.regs 12 = uPtr) (hr13 : st.regs 13 = ePtr)
    (hr14 : st.regs 14 = eIdx) (hr15 : st.regs 15 = i)
    (htag1 : st.mem uPtr = 1) (heVal : st.mem (uPtr + 1) = e)
    (hRep : (tourAsmRep vCap eCap).rep tourH (tourToAsmTour s) tx st.mem)
    (hFoot : ∀ x, (tourAsmRep vCap eCap).foot tourH tx x → x < hCur)
    {v : ℕ} (hvLt : v < vCap) (heOrd : (e, true) ∈ s.ord v)
    (hBody :
      let uNode := tx.nodeOf (2 * e)
      let isOp := if e ∉ s.rf.F.E then 1 else 0
      let rTag := Function.update st.regs 16 1
      let r17 := Function.update rTag 17 e
      let r18 := Function.update r17 18 (nodeOfEndBase tourH vCap)
      let r19 := Function.update r18 19 uNode
      let r20 := Function.update r19 20 (nodesBase tourH vCap eCap)
      let r21 := Function.update r20 21 isOp
      Runs w p ω
        (if isOp = 0 then
           .assign 22 (.load (.reg 7)) ;;
           .assign 23 (.bin .add (.bin .add (.reg 5) (.const 1)) (.bin .mul (.const 4) (.reg 22))) ;;
           .assign 24 (.load (.bin .add (.reg 23) (.const 2))) ;;
           .assign 25 (.load (.bin .add (.reg 23) (.const 3))) ;;
           .store (.reg 7) (.bin .add (.reg 22) (.const 1)) ;;
           .call 9 (tourOp bTour 1) [.reg 0, .reg 17, .reg 25, .reg 9] ;;
           .store (.reg 9) (.const 1) ;;
           .store (.bin .add (.reg 9) (.const 1)) (.const 0) ;;
           .store (.bin .add (.reg 9) (.const 2)) (.reg 17) ;;
           .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .const 3, .bin .add (.reg 9) (.const 3)] ;;
           .assign 26 (.reg 9) ;;
           .assign 27 (.load (.bin .add (.reg 7) (.const 2))) ;;
           .call 9 (outIdxSmallSide bOut) [.reg 0, .reg 24, .reg 25, .reg 24, .reg 25, .reg 27, .reg 26] ;;
           .cond (.bin .eq (.load (.bin .add (.reg 7) (.const 1))) (.const 0))
             (.store (.bin .add (.reg 7) (.const 1)) (.reg 26)) .nop ;;
           .store (.bin .add (.reg 7) (.const 2)) (.reg 26) ;;
           .call 9 (bSelf + 0) [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9]
         else
           .store (.reg 9) (.const 1) ;;
           .store (.bin .add (.reg 9) (.const 1)) (.const 0) ;;
           .store (.bin .add (.reg 9) (.const 2)) (.reg 17) ;;
           .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .const 3, .bin .add (.reg 9) (.const 3)])
        { st with regs := r21 } .normal st1 cBody)
    (hregs1 : ∀ r, r ≤ 15 → r ≠ 9 → st1.regs r = st.regs r) :
    let r12 := Function.update st1.regs 12 (uPtr + 2)
    let r13 := Function.update r12 13 (ePtr + 2)
    let r14 := Function.update r13 14 (eIdx + 1)
    let r15 := Function.update r14 15 (i + 1)
    ∃ cIter,
      Runs w p ω (asmFirstTourLoopBody bSelf bTour bOut bCopy) st .normal { st1 with regs := r15 } cIter ∧
      cIter ≤ cBody + 80 := by
  have heLt : e < eCap := hRep.valid.ordWithin.2.2 v (e, true) heOrd
  obtain ⟨hNOE, hUval, _, huLe, hNB, hOpenVal⟩ := tourAsmRep_isOpen_read (vCap := vCap) (eCap := eCap) hRep hvLt heOrd
  change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH s tx st.mem at hRep
  have hord_le : ordHandleOf tourH vCap eCap ≤ hCur := hRep.fixed_le_heap hFoot
  set uNode := tx.nodeOf (2 * e)
  set isOp := if e ∉ s.rf.F.E then 1 else 0
  set rTag := Function.update st.regs 16 1
  set r17 := Function.update rTag 17 e
  set r18 := Function.update r17 18 (nodeOfEndBase tourH vCap)
  set r19 := Function.update r18 19 uNode
  set r20 := Function.update r19 20 (nodesBase tourH vCap eCap)
  set r21 := Function.update r20 21 isOp
  have haTag : Runs w p ω (.assign 16 (.load (.reg 12))) st .normal { st with regs := rTag } 3 :=
    runs_assign_iff.mpr ⟨1, Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr12) htag1, rfl, rfl, rfl⟩
  have ha17 : Runs w p ω (.assign 17 (.load (.bin .add (.reg 12) (.const 1))))
      { st with regs := rTag } .normal { st with regs := r17 } 5 :=
    runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rTag, hr12])) (Expr.eval_const (by omega)) (by omega))
      heVal, rfl, rfl, rfl⟩
  have ha18 : Runs w p ω (.assign 18 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))))
      { st with regs := r17 } .normal { st with regs := r18 } 5 :=
    runs_assign_iff.mpr ⟨nodeOfEndBase tourH vCap, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r17, rTag, hr0]))
        (Expr.eval_const (by simp [HDR_NODE_OF_END]; omega))
        (by simp [HDR_NODE_OF_END, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))
      hNOE, rfl, rfl, rfl⟩
  have ha19 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 18) (.bin .mul (.const 2) (.reg 17)))))
      { st with regs := r18 } .normal { st with regs := r19 } 7 :=
    runs_assign_iff.mpr ⟨uNode, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r18]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r18, r17]))
          (by simp [ordHandleOf, tourFixedSize] at hord_le; omega))
        (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))
      hUval, rfl, rfl, rfl⟩
  have ha20 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))))
      { st with regs := r19 } .normal { st with regs := r20 } 5 :=
    runs_assign_iff.mpr ⟨nodesBase tourH vCap eCap, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r19, r18, r17, rTag, hr0]))
        (Expr.eval_const (by simp [HDR_NODES_BASE]; omega))
        (by simp [HDR_NODES_BASE, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))
      hNB, rfl, rfl, rfl⟩
  have ha21 : Runs w p ω (.assign 21 (.load (.bin .add (.bin .add (.reg 20) (.bin .mul (.const 17) (.reg 19))) (.const 9))))
      { st with regs := r20 } .normal { st with regs := r21 } 9 :=
    runs_assign_iff.mpr ⟨isOp, Expr.eval_load_of_eq
      (Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r20]))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r20, r19]))
            (by have := hRep.numNodes_le; simp [ordHandleOf, tourFixedSize] at hord_le; omega))
          (by have := hRep.numNodes_le; simp [nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))
        (Expr.eval_const (by omega))
        (by have := hRep.numNodes_le; simp [nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))
      hOpenVal, rfl, rfl, rfl⟩
  set r12 := Function.update st1.regs 12 (uPtr + 2)
  set r13 := Function.update r12 13 (ePtr + 2)
  set r14 := Function.update r13 14 (eIdx + 1)
  set r15 := Function.update r14 15 (i + 1)
  have ha12 : Runs w p ω (.assign 12 (.bin .add (.reg 12) (.const 2))) st1 .normal { st1 with regs := r12 } 4 :=
    runs_assign_iff.mpr ⟨uPtr + 2, Expr.eval_add
      (Expr.eval_reg_of_eq ((hregs1 12 (by decide) (by decide)).trans hr12))
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  have ha13 : Runs w p ω (.assign 13 (.bin .add (.reg 13) (.const 2))) { st1 with regs := r12 } .normal { st1 with regs := r13 } 4 :=
    runs_assign_iff.mpr ⟨ePtr + 2, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [r12, hregs1 13 (by decide) (by decide), hr13]))
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  have ha14 : Runs w p ω (.assign 14 (.bin .add (.reg 14) (.const 1))) { st1 with regs := r13 } .normal { st1 with regs := r14 } 4 :=
    runs_assign_iff.mpr ⟨eIdx + 1, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [r13, r12, hregs1 14 (by decide) (by decide), hr14]))
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  have ha15 : Runs w p ω (.assign 15 (.bin .add (.reg 15) (.const 1))) { st1 with regs := r14 } .normal { st1 with regs := r15 } 4 :=
    runs_assign_iff.mpr ⟨i + 1, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [r14, r13, r12, hregs1 15 (by decide) (by decide), hr15]))
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  have hrcOp : Runs w p ω
      (.cond (.bin .eq (.reg 21) (.const 0))
        (.assign 22 (.load (.reg 7)) ;;
         .assign 23 (.bin .add (.bin .add (.reg 5) (.const 1)) (.bin .mul (.const 4) (.reg 22))) ;;
         .assign 24 (.load (.bin .add (.reg 23) (.const 2))) ;;
         .assign 25 (.load (.bin .add (.reg 23) (.const 3))) ;;
         .store (.reg 7) (.bin .add (.reg 22) (.const 1)) ;;
         .call 9 (tourOp bTour 1) [.reg 0, .reg 17, .reg 25, .reg 9] ;;
         .store (.reg 9) (.const 1) ;;
         .store (.bin .add (.reg 9) (.const 1)) (.const 0) ;;
         .store (.bin .add (.reg 9) (.const 2)) (.reg 17) ;;
         .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .const 3, .bin .add (.reg 9) (.const 3)] ;;
         .assign 26 (.reg 9) ;;
         .assign 27 (.load (.bin .add (.reg 7) (.const 2))) ;;
         .call 9 (outIdxSmallSide bOut) [.reg 0, .reg 24, .reg 25, .reg 24, .reg 25, .reg 27, .reg 26] ;;
         .cond (.bin .eq (.load (.bin .add (.reg 7) (.const 1))) (.const 0))
           (.store (.bin .add (.reg 7) (.const 1)) (.reg 26)) .nop ;;
         .store (.bin .add (.reg 7) (.const 2)) (.reg 26) ;;
         .call 9 (bSelf + 0) [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9])
        (.store (.reg 9) (.const 1) ;;
         .store (.bin .add (.reg 9) (.const 1)) (.const 0) ;;
         .store (.bin .add (.reg 9) (.const 2)) (.reg 17) ;;
         .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .const 3, .bin .add (.reg 9) (.const 3)]))
      { st with regs := r21 } .normal st1 ((Expr.bin .eq (.reg 21) (.const 0)).size + cBody + 1) := by
    by_cases hop : isOp = 0
    · have hcond : (Expr.bin .eq (.reg 21) (.const 0)).eval w { st with regs := r21 } = some 1 := by
        simp [Expr.eval, r21, hop, BinOp.eval, (by omega : 1 < 2 ^ w)]
      refine runs_cond_iff.mpr ⟨1, cBody, hcond, ?_, rfl⟩
      simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
      have hB : Runs w p ω _ { st with regs := r21 } .normal st1 cBody := hBody
      simpa only [hop, ↓reduceIte] using hB
    · have hcond : (Expr.bin .eq (.reg 21) (.const 0)).eval w { st with regs := r21 } = some 0 := by
        simp [Expr.eval, r21, hop, BinOp.eval, (by omega : 0 < 2 ^ w)]
      refine runs_cond_iff.mpr ⟨0, cBody, hcond, ?_, rfl⟩
      simp only [↓reduceIte]
      have hB : Runs w p ω _ { st with regs := r21 } .normal st1 cBody := hBody
      simpa only [hop, ↓reduceIte] using hB
  have hcondT0 : (Expr.bin .eq (.reg 16) (.const 0)).eval w { st with regs := rTag } = some 0 := by
    simp [Expr.eval, rTag, BinOp.eval, (by omega : 0 < 2 ^ w)]
  have hcondT1 : (Expr.bin .eq (.reg 16) (.const 1)).eval w { st with regs := rTag } = some 1 := by
    simp [Expr.eval, rTag, BinOp.eval, (by omega : 1 < 2 ^ w)]
  have hdelBody := runs_seq_normal ha17 (runs_seq_normal ha18 (runs_seq_normal ha19
    (runs_seq_normal ha20 (runs_seq_normal ha21 (runs_seq_normal hrcOp
      (runs_seq_normal ha12 (runs_seq_normal ha13 ha14)))))))
  refine ⟨_, runs_seq_normal haTag (runs_seq_normal
    (runs_cond_iff.mpr ⟨0, _, hcondT0, by
      simpa using (runs_cond_iff.mpr ⟨1, _, hcondT1, by simpa using hdelBody, rfl⟩ :
        Runs w p ω (.cond (.bin .eq (.reg 16) (.const 1)) _ _) _ _ _ _), rfl⟩)
    ha15), by simp [Expr.size]; omega⟩

/-- Shared register-wrapping helper for the `.insert e a b` branch of `asmFirstTourLoopBody`. -/
theorem tourBlock_iter_insert_wrap {w bSelf bTour bOut bCopy uPtr ePtr eIdx i : ℕ}
    {p : Program} {ω : ℕ → Bool} {st st1 : State} {cBody : ℕ}
    (hwide : 18 ≤ 2 ^ w) (hu_w : uPtr + 4 < 2 ^ w) (he_w : ePtr + 8 < 2 ^ w)
    (heIdx_w : eIdx + 2 < 2 ^ w) (hi_w : i + 1 < 2 ^ w)
    (hr12 : st.regs 12 = uPtr) (hr13 : st.regs 13 = ePtr)
    (hr14 : st.regs 14 = eIdx) (hr15 : st.regs 15 = i) (htag0 : st.mem uPtr = 0)
    (hBody :
      let rTag := Function.update st.regs 16 0
      Runs w p ω
        (.store (.reg 9) (.const 2) ;;
         .call 17 bCopy [.reg 13, .bin .add (.reg 9) (.const 1), .const 8] ;;
         .call 9 (tourOp bTour 0) [.reg 0, .reg 9, .const 9, .bin .add (.reg 9) (.const 9)])
        { st with regs := rTag } .normal st1 cBody)
    (hregs1 : ∀ r, r ≤ 15 → r ≠ 9 → st1.regs r = st.regs r) :
    let r12 := Function.update st1.regs 12 (uPtr + 4)
    let r13 := Function.update r12 13 (ePtr + 8)
    let r14 := Function.update r13 14 (eIdx + 2)
    let r15 := Function.update r14 15 (i + 1)
    ∃ cIter,
      Runs w p ω (asmFirstTourLoopBody bSelf bTour bOut bCopy) st .normal { st1 with regs := r15 } cIter ∧
      cIter ≤ cBody + 40 := by
  set rTag := Function.update st.regs 16 0
  have haTag : Runs w p ω (.assign 16 (.load (.reg 12))) st .normal { st with regs := rTag } 3 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr12) htag0, rfl, rfl, rfl⟩
  set r12 := Function.update st1.regs 12 (uPtr + 4)
  set r13 := Function.update r12 13 (ePtr + 8)
  set r14 := Function.update r13 14 (eIdx + 2)
  set r15 := Function.update r14 15 (i + 1)
  have ha12 : Runs w p ω (.assign 12 (.bin .add (.reg 12) (.const 4))) st1 .normal { st1 with regs := r12 } 4 :=
    runs_assign_iff.mpr ⟨uPtr + 4, Expr.eval_add
      (Expr.eval_reg_of_eq ((hregs1 12 (by decide) (by decide)).trans hr12))
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  have ha13 : Runs w p ω (.assign 13 (.bin .add (.reg 13) (.const 8))) { st1 with regs := r12 } .normal { st1 with regs := r13 } 4 :=
    runs_assign_iff.mpr ⟨ePtr + 8, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [r12, hregs1 13 (by decide) (by decide), hr13]))
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  have ha14 : Runs w p ω (.assign 14 (.bin .add (.reg 14) (.const 2))) { st1 with regs := r13 } .normal { st1 with regs := r14 } 4 :=
    runs_assign_iff.mpr ⟨eIdx + 2, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [r13, r12, hregs1 14 (by decide) (by decide), hr14]))
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  have ha15 : Runs w p ω (.assign 15 (.bin .add (.reg 15) (.const 1))) { st1 with regs := r14 } .normal { st1 with regs := r15 } 4 :=
    runs_assign_iff.mpr ⟨i + 1, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [r14, r13, r12, hregs1 15 (by decide) (by decide), hr15]))
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  have hcondT0 : (Expr.bin .eq (.reg 16) (.const 0)).eval w { st with regs := rTag } = some 1 := by
    simp [Expr.eval, rTag, BinOp.eval, (by omega : 1 < 2 ^ w)]
  have hbodyThen := runs_seq_r3 (runs_seq_normal hBody (runs_seq_normal ha12 (runs_seq_normal ha13 ha14)))
  refine ⟨_, runs_seq_normal haTag (runs_seq_normal
    (runs_cond_iff.mpr ⟨1, _, hcondT0, by simpa using hbodyThen, rfl⟩) ha15),
    by simp [Expr.size]; omega⟩

/-- Shared register-wrapping helper for the `.split v v' St Sh` branch of `asmFirstTourLoopBody`. -/
theorem tourBlock_iter_split_wrap {w bSelf bTour bOut bCopy uPtr ePtr eIdx i tagU v v' kt kh m : ℕ}
    {p : Program} {ω : ℕ → Bool} {st st1 : State} {cBody : ℕ}
    (hwide : 18 ≤ 2 ^ w) (hu_w : uPtr + 5 + (kt + kh) < 2 ^ w) (he_w : ePtr + 4 + m < 2 ^ w)
    (heIdx_w : eIdx + 1 < 2 ^ w) (hi_w : i + 1 < 2 ^ w)
    (htagU : tagU = 2 ∨ tagU = 3)
    (hr12 : st.regs 12 = uPtr) (hr13 : st.regs 13 = ePtr)
    (hr14 : st.regs 14 = eIdx) (hr15 : st.regs 15 = i)
    (hmemTag : st.mem uPtr = tagU) (hmemV : st.mem (uPtr + 1) = v) (hmemV' : st.mem (uPtr + 2) = v')
    (hmemKt : st.mem (uPtr + 3) = kt) (hmemKh : st.mem (uPtr + 4) = kh) (hmemM : st.mem (ePtr + 3) = m)
    (hBody :
      let rTag := Function.update st.regs 16 tagU
      let r17 := Function.update rTag 17 v
      let r18 := Function.update r17 18 v'
      let r19 := Function.update r18 19 kt
      let r20 := Function.update r19 20 kh
      let r21 := Function.update r20 21 m
      Runs w p ω
        (.call 9 (bSelf + 1) [.reg 0, .reg 13, .reg 9] ;;
         .assign 22 (.load (.reg 7)) ;;
         .assign 23 (.bin .add (.bin .add (.reg 5) (.const 1)) (.bin .mul (.const 4) (.reg 22))) ;;
         .assign 24 (.load (.bin .add (.reg 23) (.const 2))) ;;
         .assign 25 (.load (.bin .add (.reg 23) (.const 3))) ;;
         .store (.reg 7) (.bin .add (.reg 22) (.const 1)) ;;
         .assign 26 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
         .assign 27 (.load (.bin .add (.reg 26) (.reg 18))) ;;
         .assign 28 (.reg 17) ;;
         .cond (.bin .eq (.reg 27) (.const 1)) (.assign 28 (.reg 18)) .nop ;;
         .call 9 (tourOp bTour 3) [.reg 0, .reg 28, .reg 25, .reg 9] ;;
         .assign 26 (.reg 9) ;;
         .assign 27 (.load (.bin .add (.reg 7) (.const 2))) ;;
         .call 9 (outIdxSmallSide bOut) [.reg 0, .reg 24, .reg 25, .reg 24, .reg 25, .reg 27, .reg 26] ;;
         .cond (.bin .eq (.load (.bin .add (.reg 7) (.const 1))) (.const 0))
           (.store (.bin .add (.reg 7) (.const 1)) (.reg 26)) .nop ;;
         .store (.bin .add (.reg 7) (.const 2)) (.reg 26) ;;
         .call 9 (bSelf + 0) [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9])
        { st with regs := r21 } .normal st1 cBody)
    (hregs1 : ∀ r, r ≤ 21 → r ≠ 9 → st1.regs r =
      (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update st.regs 16 tagU) 17 v) 18 v') 19 kt) 20 kh) 21 m) r) :
    let r12 := Function.update st1.regs 12 (uPtr + 5 + (kt + kh))
    let r13 := Function.update r12 13 (ePtr + 4 + m)
    let r14 := Function.update r13 14 (eIdx + 1)
    let r15 := Function.update r14 15 (i + 1)
    ∃ cIter,
      Runs w p ω (asmFirstTourLoopBody bSelf bTour bOut bCopy) st .normal { st1 with regs := r15 } cIter ∧
      cIter ≤ cBody + 80 := by
  set rTag := Function.update st.regs 16 tagU
  set r17 := Function.update rTag 17 v
  set r18 := Function.update r17 18 v'
  set r19 := Function.update r18 19 kt
  set r20 := Function.update r19 20 kh
  set r21 := Function.update r20 21 m
  have haTag : Runs w p ω (.assign 16 (.load (.reg 12))) st .normal { st with regs := rTag } 3 :=
    runs_assign_iff.mpr ⟨tagU, Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr12) hmemTag, rfl, rfl, rfl⟩
  have ha17 : Runs w p ω (.assign 17 (.load (.bin .add (.reg 12) (.const 1)))) { st with regs := rTag } .normal { st with regs := r17 } 5 :=
    runs_assign_iff.mpr ⟨v, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rTag, hr12])) (Expr.eval_const (by omega)) (by omega)) hmemV, rfl, rfl, rfl⟩
  have ha18 : Runs w p ω (.assign 18 (.load (.bin .add (.reg 12) (.const 2)))) { st with regs := r17 } .normal { st with regs := r18 } 5 :=
    runs_assign_iff.mpr ⟨v', Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r17, rTag, hr12])) (Expr.eval_const (by omega)) (by omega)) hmemV', rfl, rfl, rfl⟩
  have ha19 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 12) (.const 3)))) { st with regs := r18 } .normal { st with regs := r19 } 5 :=
    runs_assign_iff.mpr ⟨kt, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r18, r17, rTag, hr12])) (Expr.eval_const (by omega)) (by omega)) hmemKt, rfl, rfl, rfl⟩
  have ha20 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 12) (.const 4)))) { st with regs := r19 } .normal { st with regs := r20 } 5 :=
    runs_assign_iff.mpr ⟨kh, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r19, r18, r17, rTag, hr12])) (Expr.eval_const (by omega)) (by omega)) hmemKh, rfl, rfl, rfl⟩
  have ha21 : Runs w p ω (.assign 21 (.load (.bin .add (.reg 13) (.const 3)))) { st with regs := r20 } .normal { st with regs := r21 } 5 :=
    runs_assign_iff.mpr ⟨m, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r20, r19, r18, r17, rTag, hr13])) (Expr.eval_const (by omega)) (by omega)) hmemM, rfl, rfl, rfl⟩
  set r12 := Function.update st1.regs 12 (uPtr + 5 + (kt + kh))
  set r13 := Function.update r12 13 (ePtr + 4 + m)
  set r14 := Function.update r13 14 (eIdx + 1)
  set r15 := Function.update r14 15 (i + 1)
  have hr12_1 : st1.regs 12 = uPtr := by simpa [r21, r20, r19, r18, r17, rTag, hr12] using hregs1 12 (by decide) (by decide)
  have hr13_1 : st1.regs 13 = ePtr := by simpa [r21, r20, r19, r18, r17, rTag, hr13] using hregs1 13 (by decide) (by decide)
  have hr14_1 : st1.regs 14 = eIdx := by simpa [r21, r20, r19, r18, r17, rTag, hr14] using hregs1 14 (by decide) (by decide)
  have hr15_1 : st1.regs 15 = i := by simpa [r21, r20, r19, r18, r17, rTag, hr15] using hregs1 15 (by decide) (by decide)
  have hr19_1 : st1.regs 19 = kt := by simpa [r21, r20, r19] using hregs1 19 (by decide) (by decide)
  have hr20_1 : st1.regs 20 = kh := by simpa [r21, r20] using hregs1 20 (by decide) (by decide)
  have hr21_1 : st1.regs 21 = m := by simpa [r21] using hregs1 21 (by decide) (by decide)
  have ha12 : Runs w p ω (.assign 12 (.bin .add (.bin .add (.reg 12) (.const 5)) (.bin .add (.reg 19) (.reg 20))))
      st1 .normal { st1 with regs := r12 } 8 :=
    runs_assign_iff.mpr ⟨uPtr + 5 + (kt + kh), Expr.eval_add
      (Expr.eval_add (Expr.eval_reg_of_eq hr12_1) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_add (Expr.eval_reg_of_eq hr19_1) (Expr.eval_reg_of_eq hr20_1) (by omega))
      (by omega), rfl, rfl, rfl⟩
  have ha13 : Runs w p ω (.assign 13 (.bin .add (.bin .add (.reg 13) (.const 4)) (.reg 21)))
      { st1 with regs := r12 } .normal { st1 with regs := r13 } 6 :=
    runs_assign_iff.mpr ⟨ePtr + 4 + m, Expr.eval_add
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r12, hr13_1])) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp [r12, hr21_1])) (by omega), rfl, rfl, rfl⟩
  have ha14 : Runs w p ω (.assign 14 (.bin .add (.reg 14) (.const 1))) { st1 with regs := r13 } .normal { st1 with regs := r14 } 4 :=
    runs_assign_iff.mpr ⟨eIdx + 1, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [r13, r12, hr14_1])) (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  have ha15 : Runs w p ω (.assign 15 (.bin .add (.reg 15) (.const 1))) { st1 with regs := r14 } .normal { st1 with regs := r15 } 4 :=
    runs_assign_iff.mpr ⟨i + 1, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [r14, r13, r12, hr15_1])) (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  have hcondT0 : (Expr.bin .eq (.reg 16) (.const 0)).eval w { st with regs := rTag } = some 0 := by
    rcases htagU with rfl | rfl <;> simp [Expr.eval, rTag, BinOp.eval, (by omega : 0 < 2 ^ w)]
  have hcondT1 : (Expr.bin .eq (.reg 16) (.const 1)).eval w { st with regs := rTag } = some 0 := by
    have hw0 : w ≠ 0 := by intro h; subst h; simp at hwide
    rcases htagU with rfl | rfl <;> simp [Expr.eval, rTag, BinOp.eval, hw0, (by omega : 0 < 2 ^ w)]
  have hspBody := runs_seq_normal ha17 (runs_seq_normal ha18 (runs_seq_normal ha19
    (runs_seq_normal ha20 (runs_seq_normal ha21
      (runs_seq_r17 (runs_seq_normal hBody (runs_seq_normal ha12 (runs_seq_normal ha13 ha14))))))))
  refine ⟨_, runs_seq_normal haTag (runs_seq_normal
    (runs_cond_iff.mpr ⟨0, _, hcondT0, by
      simpa using (runs_cond_iff.mpr ⟨0, _, hcondT1, by simpa using hspBody, rfl⟩ :
        Runs w p ω (.cond (.bin .eq (.reg 16) (.const 1)) _ _) _ _ _ _), rfl⟩)
    ha15), by simp [Expr.size]; omega⟩

/-- Shared footprint-transport helper across one iteration of `asmFirstTourLoopBody`. -/
theorem tourLoop_foot_transport {vCap eCap tourH batch words edCopy editWords spPtr statePtr nSp hCur hNext : ℕ}
    {tx tx1 : (tourAsmRep vCap eCap).τ}
    (hhLo : hCur ≤ hNext) (hbatch : batch + words ≤ hCur) (hed : edCopy + editWords ≤ hCur)
    (hsp : spPtr + 1 + 4 * nSp ≤ hCur) (hst : statePtr + 3 ≤ hCur)
    (hFoot : ∀ x, (tourAsmRep vCap eCap).foot tourH tx x → x < hCur)
    (hBF : ∀ x, batch ≤ x → x < batch + words → ¬ (tourAsmRep vCap eCap).foot tourH tx x)
    (hEF : ∀ x, edCopy ≤ x → x < edCopy + editWords → ¬ (tourAsmRep vCap eCap).foot tourH tx x)
    (hSF : ∀ x, spPtr ≤ x → x < spPtr + 1 + 4 * nSp → ¬ (tourAsmRep vCap eCap).foot tourH tx x)
    (hStF : ∀ j < 3, ¬ (tourAsmRep vCap eCap).foot tourH tx (statePtr + j))
    (hFt : ∀ x, (tourAsmRep vCap eCap).foot tourH tx1 x →
      (tourAsmRep vCap eCap).foot tourH tx x ∨ (hCur ≤ x ∧ x < hNext)) :
    (∀ x, (tourAsmRep vCap eCap).foot tourH tx1 x → x < hNext) ∧
    (∀ x, batch ≤ x → x < batch + words → ¬ (tourAsmRep vCap eCap).foot tourH tx1 x) ∧
    (∀ x, edCopy ≤ x → x < edCopy + editWords → ¬ (tourAsmRep vCap eCap).foot tourH tx1 x) ∧
    (∀ x, spPtr ≤ x → x < spPtr + 1 + 4 * nSp → ¬ (tourAsmRep vCap eCap).foot tourH tx1 x) ∧
    (∀ j < 3, ¬ (tourAsmRep vCap eCap).foot tourH tx1 (statePtr + j)) :=
  ⟨fun x hx => by rcases hFt x hx with h0 | ⟨_, hlt⟩; exact lt_of_lt_of_le (hFoot x h0) hhLo; exact hlt,
   fun x h1 h2 hf => by rcases hFt x hf with h0 | ⟨hge, _⟩; exact hBF x h1 h2 h0; omega,
   fun x h1 h2 hf => by rcases hFt x hf with h0 | ⟨hge, _⟩; exact hEF x h1 h2 h0; omega,
   fun x h1 h2 hf => by rcases hFt x hf with h0 | ⟨hge, _⟩; exact hSF x h1 h2 h0; omega,
   fun j hj hf => by rcases hFt _ hf with h0 | ⟨hge, _⟩; exact hStF j hj h0; omega⟩

end

end MinCostFlow.SparseCore.Program
