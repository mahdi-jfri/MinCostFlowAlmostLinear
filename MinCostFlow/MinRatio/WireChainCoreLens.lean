module

public import MinCostFlow.MinRatio.WireChainCoreLen0
import WordRAM.Tactic

/-!
# Core-level batch length updates (`WireChainCoreLens`)

Provides `wireUpdateCoreLenFromBatchBody` (`NoRand`) and `wireUpdateCoreLenFromBatchBody_runs`,
updating `levelLens[idx + 1]` in place for every edge inserted by a batch `U`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
  MinCostFlow.IPM.Machine

@[expose] def wireUpdateCoreLenFromBatchBody (edgeProc : ℕ) : Stmt :=
  .assign 7 (.load (.reg 0)) ;;
  .assign 8 (.bin .add (.reg 0) (.const 1)) ;;
  .assign 9 (.load (.reg 1)) ;;
  .assign 10 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .assign 11 (.reg 6) ;;
  forRange 12 (.const 0) (.reg 7)
    (.assign 13 (.load (.reg 8)) ;;
     .cond (.bin .eq (.reg 13) (.const 0))
       (.assign 14 (.load (.bin .add (.reg 8) (.const 1))) ;;
        .call 11 edgeProc [.reg 9, .reg 10, .reg 2, .reg 3, .reg 14, .reg 4, .reg 5, .reg 11] ;;
        .assign 8 (.bin .add (.reg 8) (.const 4)))
       (.cond (.bin .eq (.reg 13) (.const 1))
         (.assign 8 (.bin .add (.reg 8) (.const 2)))
         (.assign 14 (.load (.bin .add (.reg 8) (.const 3))) ;;
          .assign 15 (.load (.bin .add (.reg 8) (.const 4))) ;;
          .assign 8 (.bin .add (.bin .add (.bin .add (.reg 8) (.const 5)) (.reg 14)) (.reg 15))))) ;;
  .ret (.reg 11)

theorem wireUpdateCoreLenFromBatchBody_noRand (edgeProc : ℕ) :
    (wireUpdateCoreLenFromBatchBody edgeProc).NoRand := by
  simp [wireUpdateCoreLenFromBatchBody, forRange, forUp, Stmt.NoRand]

/-- Execute `wireUpdateCoreLenFromBatchBody`: updates `curLenPtr` in-place at every inserted edge of
a `SmallBatchAt` batch `U` using `wireCoreLenEdgeBody`, returning `nextHeap ≤ heap + U.length *
wireCoreLenEdgeSpace (max L Lw)` in `O(U.length * wireCoreLenEdgeCost (max L Lw))` steps. -/
theorem wireUpdateCoreLenFromBatchBody_runs
    {w edgeProc signExt mul intDiv copy batchPtr stretchDesc prevLenPtr curLenPtr
      L Lw P ecPrev ecCur totalWords pos heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {G : MGraph} {U : List Update}
    {forest : LSF} {prevℓ oldCurℓ : ℕ → ℝ} {prevE : Finset ℕ}
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hSmall : DynSpanner.Program.SmallBatchAt mem batchPtr G U totalWords)
    (hBatchW : ∀ j < totalWords, mem (batchPtr + j) < 2 ^ w)
    (hStretch : StretchValuesAt mem stretchDesc 4 Lw P prevE forest.wstr)
    (hPrevLen : EdgeValuesAt mem prevLenPtr 4 L P prevE prevℓ)
    (hCurLen : EdgeValuesAt mem curLenPtr 4 L P G.E oldCurℓ)
    (hGE : ∀ e ∈ G.E, e < ecCur)
    (hInsInfo : ∀ u ∈ U, match u with
      | .insert e _ _ => e ∈ prevE ∧ e < ecPrev ∧ e < ecCur ∧
          (∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P = coreLen forest prevℓ e)
      | _ => True)
    (hAgreeOld : ∀ e ∈ (G.applyBatch U).E, (¬ ∃ u ∈ U, u.Inserts e) →
      e ∈ G.E ∧ oldCurℓ e = coreLen forest prevℓ e)
    (hMemIns : ∀ e ∈ (G.applyBatch U).E, (∃ u ∈ U, u.Inserts e) →
      ∃ k, ∃ hk : k < U.length, U[k].Inserts e)
    (hBatchLe : batchPtr + totalWords ≤ heap)
    (hStretchLe : stretchDesc + 2 ≤ heap)
    (hNumDenLe : ∀ e ∈ prevE, mem stretchDesc + e * Lw + Lw ≤ heap ∧
      mem (stretchDesc + 1) + e * Lw + Lw ≤ heap)
    (hPrevLe : prevLenPtr + ecPrev * L ≤ heap)
    (hCurLe : curLenPtr + ecCur * L ≤ heap)
    (hDisjBatch : batchPtr + totalWords ≤ curLenPtr ∨ curLenPtr + ecCur * L ≤ batchPtr)
    (hDisjPrev : prevLenPtr + ecPrev * L ≤ curLenPtr ∨ curLenPtr + ecCur * L ≤ prevLenPtr)
    (hDisjNum : ∀ e ∈ prevE, ∀ k < Lw, mem stretchDesc + e * Lw + k < curLenPtr ∨
      curLenPtr + ecCur * L ≤ mem stretchDesc + e * Lw + k)
    (hDisjDen : ∀ e ∈ prevE, ∀ k < Lw, mem (stretchDesc + 1) + e * Lw + k < curLenPtr ∨
      curLenPtr + ecCur * L ≤ mem (stretchDesc + 1) + e * Lw + k)
    (hz : ZeroFrom mem heap)
    (hRoom : heap + U.length * wireCoreLenEdgeSpace (max L Lw) < 2 ^ w)
    (hw5 : 5 < 2 ^ w) :
    let K := max L Lw
    ∃ nextHeap out cost,
      Runs w p ω (wireUpdateCoreLenFromBatchBody edgeProc)
        (startState [batchPtr, stretchDesc, prevLenPtr, curLenPtr, L, Lw, heap] mem pos)
        (.returned nextHeap) out cost ∧
      heap ≤ nextHeap ∧ nextHeap ≤ heap + U.length * wireCoreLenEdgeSpace K ∧
      cost ≤ U.length * (wireCoreLenEdgeCost K + 60) + 55 ∧
      EdgeValuesAt out.mem curLenPtr 4 L P (G.applyBatch U).E (coreLen forest prevℓ) ∧
      ZeroFrom out.mem nextHeap ∧
      ∀ a < heap, (a < curLenPtr ∨ curLenPtr + ecCur * L ≤ a) → out.mem a = mem a := by
  dsimp only
  set K := max L Lw
  set sp := wireCoreLenEdgeSpace K
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  obtain ⟨⟨hTotPos, hLenB0, hBody0⟩, _⟩ := hSmall
  have hULenW : U.length < 2 ^ w := by simpa [hLenB0] using hBatchW 0 (by omega)
  let numPtr := mem stretchDesc
  let denPtr := mem (stretchDesc + 1)
  let s0 := startState [batchPtr, stretchDesc, prevLenPtr, curLenPtr, L, Lw, heap] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 7 U.length }
  let s2 := { s1 with regs := Function.update s1.regs 8 (batchPtr + 1) }
  let s3 := { s2 with regs := Function.update s2.regs 9 numPtr }
  let s4 := { s3 with regs := Function.update s3.regs 10 denPtr }
  let s5 := { s4 with regs := Function.update s4.regs 11 heap }
  have r1 : Runs w p ω (.assign 7 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨U.length, by simp [Expr.eval, s0, startState, hLenB0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 8 (.bin .add (.reg 0) (.const 1))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨batchPtr + 1, by
      simp [Expr.eval, BinOp.eval, s1, s0, startState, hw1, show batchPtr + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 9 (.load (.reg 1))) s2 .normal s3 3 :=
    runs_assign_iff.mpr ⟨numPtr, by simp [Expr.eval, s2, s1, s0, startState, numPtr], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 1) (.const 1)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨denPtr, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, hw1,
        show stretchDesc + 1 < 2 ^ w by omega, denPtr], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 11 (.reg 6)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s4, s3, s2, s1, s0, startState], rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) : Prop :=
    ∃ ptr remW curH,
      s.regs 0 = batchPtr ∧ s.regs 1 = stretchDesc ∧ s.regs 2 = prevLenPtr ∧ s.regs 3 = curLenPtr ∧
      s.regs 4 = L ∧ s.regs 5 = Lw ∧ s.regs 6 = heap ∧
      s.regs 7 = U.length ∧ s.regs 8 = ptr ∧ s.regs 9 = numPtr ∧ s.regs 10 = denPtr ∧
      s.regs 11 = curH ∧ s.regs 12 = i ∧
      batchPtr + 1 ≤ ptr ∧ ptr + remW = batchPtr + totalWords ∧
      BatchBodyAt mem ptr (G.applyBatch (U.take i)) (U.drop i) remW ∧
      heap ≤ curH ∧ curH ≤ heap + i * sp ∧
      ZeroFrom s.mem curH ∧
      (∀ a < heap, (a < curLenPtr ∨ curLenPtr + ecCur * L ≤ a) → s.mem a = mem a) ∧
      (∀ e, e < ecCur → (¬ ∃ j, ∃ hj : j < U.length, j < i ∧ U[j].Inserts e) →
        ∀ t < L, s.mem (curLenPtr + e * L + t) = mem (curLenPtr + e * L + t)) ∧
      (∀ j, j < i → ∀ hj : j < U.length, match U[j] with
        | .insert e _ _ => Num.Valid s.mem (curLenPtr + e * L) 4 L ∧
            Num.fixVal s.mem (curLenPtr + e * L) 4 L P = coreLen forest prevℓ e
        | _ => True)
  let stepCost := wireCoreLenEdgeCost K + 51
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 12) (lo := .const 0) (hi := .reg 7)
    (P := fun s => s = s5) (Inv := Inv) (fun _ => stepCost) 0 U.length (Nat.zero_le _) hw1
    (fun _ => hULenW)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega],
        batchPtr + 1, totalWords - 1, heap,
        by simp [s5, s4, s3, s2, s1, s0, startState], by simp [s5, s4, s3, s2, s1, s0, startState],
        by simp [s5, s4, s3, s2, s1, s0, startState], by simp [s5, s4, s3, s2, s1, s0, startState],
        by simp [s5, s4, s3, s2, s1, s0, startState], by simp [s5, s4, s3, s2, s1, s0, startState],
        by simp [s5, s4, s3, s2, s1, s0, startState], by simp [s5, s4, s3, s2, s1],
        by simp [s5, s4, s3, s2], by simp [s5, s4, s3], by simp [s5, s4], by simp [s5], by simp,
        le_rfl, by omega, by simpa [MGraph.applyBatch] using hBody0,
        le_rfl, by simp, hz, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl,
        fun j hj _ => absurd hj (Nat.not_lt_zero _)⟩)
    (fun _ _ _ _ ⟨_, _, _, h⟩ => h.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ s _ _ ⟨_, _, _, h⟩ => by simp [Expr.eval, h.2.2.2.2.2.2.2.1])
    (fun i _ hi => by
      intro s ω' ⟨ptr, remW, curH, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
        hPtrLo, hPtrSum, hBodyI, hHLo, hHHi, hzS, hFr, hKeep, hDone⟩
      rw [List.drop_eq_getElem_cons hi] at hBodyI
      obtain ⟨uLen, huLenLe, huAt, hBodyRest⟩ := hBodyI
      have hTakeNext : G.applyBatch (U.take (i + 1)) = (G.applyBatch (U.take i)).applyUpdate U[i] := by
        simp only [MGraph.applyBatch, List.take_succ_eq_append_getElem hi, List.foldl_append,
          List.foldl_cons, List.foldl_nil]
      have hPtrIn (k : ℕ) (hk : k < uLen) : ptr + k < heap ∧ (ptr + k < curLenPtr ∨ curLenPtr + ecCur * L ≤ ptr + k) := by
        have hkT : ptr - batchPtr + k < totalWords := by omega
        exact ⟨by omega, by rcases hDisjBatch with h | h <;> omega⟩
      have hMemPtr (k : ℕ) (hk : k < uLen) : s.mem (ptr + k) = mem (ptr + k) :=
        hFr (ptr + k) (hPtrIn k hk).1 (hPtrIn k hk).2
      have hPtrNextW : ptr + uLen < 2 ^ w := by omega
      cases hUi : U[i] with
      | insert e u v =>
        simp only [hUi, UpdateAt] at huAt
        obtain ⟨huLenEq, hList⟩ := huAt
        subst huLenEq
        have hTag0 : mem ptr = 0 := by simpa using hList 0 (by simp)
        have hEi1 : mem (ptr + 1) = e := by simpa using hList 1 (by simp)
        obtain ⟨hePrev, hePrevCap, heCurCap, q, hqFits, hqVal⟩ := hInsInfo (.insert e u v) (hUi ▸ List.getElem_mem hi)
        have hTagS : s.mem ptr = 0 := by simpa using (hMemPtr 0 (by omega)).trans hTag0
        have hEiS : s.mem (ptr + 1) = e := (hMemPtr 1 (by omega)).trans hEi1
        let t1 := { s with regs := Function.update s.regs 13 0 }
        let t2 := { t1 with regs := Function.update t1.regs 14 e }
        have rt1 : Runs w p ω' (.assign 13 (.load (.reg 8))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h8, hTagS], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 14 (.load (.bin .add (.reg 8) (.const 1)))) t1 .normal t2 5 :=
          runs_assign_iff.mpr ⟨e, by simp [Expr.eval, BinOp.eval, t1, h8, hw1,
            show ptr + 1 < 2 ^ w by omega, hEiS], rfl, rfl, rfl⟩
        have hRoomI : curH + sp < 2 ^ w := by
          have hm : (i + 1) * sp ≤ U.length * sp := Nat.mul_le_mul_right sp (Nat.succ_le_of_lt hi)
          rw [Nat.succ_mul] at hm; omega
        have hNumV : Num.Valid t2.mem (numPtr + e * Lw) 4 Lw := fun k hk => by
          rw [hFr _ (by have := (hNumDenLe e hePrev).1; omega) (hDisjNum e hePrev k hk)]
          exact (hStretch e hePrev).1 k hk
        have hDenV : Num.Valid t2.mem (denPtr + e * Lw) 4 Lw := fun k hk => by
          rw [hFr _ (by have := (hNumDenLe e hePrev).2; omega) (hDisjDen e hePrev k hk)]
          exact (hStretch e hePrev).2.1 k hk
        have hPrevV : Num.Valid t2.mem (prevLenPtr + e * L) 4 L := fun k hk => by
          have hePL : e * L + L ≤ ecPrev * L := by
            simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt hePrevCap)
          rw [hFr _ (by omega) (by rcases hDisjPrev with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
          exact (hPrevLen e hePrev).1 k hk
        have hNumEq : Num.fixVal t2.mem (numPtr + e * Lw) 4 Lw P = Num.fixVal mem (numPtr + e * Lw) 4 Lw P := by
          unfold Num.fixVal; congr 2; exact Num.intVal_congr (fun k hk =>
            hFr _ (by have := (hNumDenLe e hePrev).1; omega) (hDisjNum e hePrev k hk))
        have hDenEq : Num.fixVal t2.mem (denPtr + e * Lw) 4 Lw P = Num.fixVal mem (denPtr + e * Lw) 4 Lw P := by
          unfold Num.fixVal; congr 2; exact Num.intVal_congr (fun k hk =>
            hFr _ (by have := (hNumDenLe e hePrev).2; omega) (hDisjDen e hePrev k hk))
        have hPrevEq : Num.fixVal t2.mem (prevLenPtr + e * L) 4 L P = prevℓ e := by
          rw [← (hPrevLen e hePrev).2]; unfold Num.fixVal; congr 2; exact Num.intVal_congr (fun k hk => by
            have hePL : e * L + L ≤ ecPrev * L := by
              simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt hePrevCap)
            exact hFr _ (by omega) (by rcases hDisjPrev with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]))
        have heCurL : e * L + L ≤ ecCur * L := by
          simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt heCurCap)
        have hePrevL : e * L + L ≤ ecPrev * L := by
          simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt hePrevCap)
        obtain ⟨outE, cE, rE, hcE, hOutV, hOutFix, hzE, hFrE⟩ :=
          wireCoreLenEdge_runs (w := w) (L := L) (Lw := Lw) (P := P)
            (numPtr := numPtr) (denPtr := denPtr) (lenPtr := prevLenPtr) (outPtr := curLenPtr)
            (e := e) (heap := curH) (p := p) (ω := ω') (mem := t2.mem) (pos := t2.pos)
            (forest := forest) (ℓ := prevℓ) (q := q)
            hSign hMul hDiv hCopy hNumV hDenV hPrevV
            (by rw [hDenEq]; exact (hStretch e hePrev).2.2.1)
            (by rw [hNumEq, hDenEq]; exact (hStretch e hePrev).2.2.2)
            hPrevEq hqFits hqVal
            (by have := (hNumDenLe e hePrev).1; omega)
            (by have := (hNumDenLe e hePrev).2; omega)
            (by omega) (by omega) hzS hRoomI hw4
        let t3 : State := { regs := Function.update t2.regs 11 (curH + sp), mem := outE.mem, pos := outE.pos }
        have rt3 : Runs w p ω'
            (.call 11 edgeProc [.reg 9, .reg 10, .reg 2, .reg 3, .reg 14, .reg 4, .reg 5, .reg 11])
            t2 .normal t3 (8 + cE + 1) :=
          runs_call_iff.mpr ⟨[numPtr, denPtr, prevLenPtr, curLenPtr, e, L, Lw, curH],
            wireCoreLenEdgeBody signExt mul intDiv copy, .returned (curH + sp), outE, cE,
            by simp [evalArgs, Expr.eval, t2, t1, h9, h10, h2, h3, h4, h5, h11],
            hEdgeProc, rE, rfl, rfl, by simp [argsSize, Expr.size]⟩
        let t4 : State := { t3 with regs := Function.update t3.regs 8 (ptr + 4) }
        have rt4 : Runs w p ω' (.assign 8 (.bin .add (.reg 8) (.const 4))) t3 .normal t4 4 :=
          runs_assign_iff.mpr ⟨ptr + 4, by simp [Expr.eval, BinOp.eval, t3, t2, t1, h8, hw4, hPtrNextW],
            rfl, rfl, rfl⟩
        have rBranch : Runs w p ω' _ t1 .normal t4 (5 + ((8 + cE + 1) + 4 + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, rt2,
            runs_seq_iff.mpr (Or.inr ⟨t3, 8 + cE + 1, 4, rt3, rt4, rfl⟩), rfl⟩)
        have rCond : Runs w p ω'
            (.cond (.bin .eq (.reg 13) (.const 0)) _
              (.cond (.bin .eq (.reg 13) (.const 1))
                (.assign 8 (.bin .add (.reg 8) (.const 2)))
                (.assign 14 (.load (.bin .add (.reg 8) (.const 3))) ;;
                 .assign 15 (.load (.bin .add (.reg 8) (.const 4))) ;;
                 .assign 8 (.bin .add (.bin .add (.bin .add (.reg 8) (.const 5)) (.reg 14)) (.reg 15)))))
            t1 .normal t4 (3 + (5 + ((8 + cE + 1) + 4 + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, t1, hw1], by simpa using rBranch,
            by simp [Expr.size]⟩
        have hInvN : Inv (i + 1) { t4 with regs := Function.update t4.regs 12 (i + 1) } := by
          refine ⟨ptr + 4, remW - 4, curH + sp,
            by simp [t4, t3, t2, t1, h0], by simp [t4, t3, t2, t1, h1],
            by simp [t4, t3, t2, t1, h2], by simp [t4, t3, t2, t1, h3],
            by simp [t4, t3, t2, t1, h4], by simp [t4, t3, t2, t1, h5],
            by simp [t4, t3, t2, t1, h6], by simp [t4, t3, t2, t1, h7],
            by simp [t4], by simp [t4, t3, t2, t1, h9], by simp [t4, t3, t2, t1, h10],
            by simp [t4, t3], by simp, by omega, by omega, by simpa [hTakeNext, hUi] using hBodyRest,
            by omega, by rw [Nat.succ_mul]; omega, hzE,
            fun a ha hOut => (hFrE a (lt_of_lt_of_le ha hHLo)
              (by rcases hOut with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])).trans (hFr a ha hOut),
            fun x hx hni t ht => by
              have hne : x ≠ e := fun h => hni ⟨i, hi, Nat.lt_succ_self i, by simp [hUi, h, Update.Inserts]⟩
              have hxL : x * L + L ≤ ecCur * L := by
                simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt hx)
              have hout : curLenPtr + x * L + t < curLenPtr + e * L ∨ curLenPtr + e * L + L ≤ curLenPtr + x * L + t := by
                rcases lt_or_gt_of_ne hne with hlt | hgt
                · left; have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt); rw [Nat.succ_mul] at this; omega
                · right; have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hgt); rw [Nat.succ_mul] at this; omega
              exact (hFrE _ (by omega) hout).trans (hKeep x hx (fun ⟨j, hjLt, hj, hjI⟩ => hni ⟨j, hjLt, by omega, hjI⟩) t ht),
            fun j hj hjLt => by
              by_cases hji : j = i
              · subst hji; simp only [hUi]; exact ⟨hOutV, hOutFix⟩
              · have hd := hDone j (by omega) hjLt
                cases hUj : U[j] with
                | delete _ => trivial
                | split _ _ _ _ => trivial
                | insert ej _ _ =>
                  simp only [hUj] at hd
                  by_cases heq : ej = e
                  · subst heq; exact ⟨hOutV, hOutFix⟩
                  · have ⟨_, _, hejCap, _⟩ := hInsInfo (.insert ej _ _) (hUj ▸ List.getElem_mem hjLt)
                    have hejL : ej * L + L ≤ ecCur * L := by
                      simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt hejCap)
                    have hout (t : ℕ) (ht : t < L) :
                        curLenPtr + ej * L + t < curLenPtr + e * L ∨ curLenPtr + e * L + L ≤ curLenPtr + ej * L + t := by
                      rcases lt_or_gt_of_ne heq with hlt | hgt
                      · left; have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt); rw [Nat.succ_mul] at this; omega
                      · right; have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hgt); rw [Nat.succ_mul] at this; omega
                    refine ⟨fun t ht => by rw [hFrE _ (by omega) (hout t ht)]; exact hd.1 t ht, ?_⟩
                    rw [← hd.2]; unfold Num.fixVal; congr 2
                    exact Num.intVal_congr (fun t ht => hFrE _ (by omega) (hout t ht))⟩
        refine ⟨.normal, t4, _, runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rCond, rfl⟩),
          ⟨hInvN, by simp [t4, t3, t2, t1, h12]⟩, by dsimp [stepCost, K]; omega⟩
      | delete e =>
        simp only [hUi, UpdateAt] at huAt
        obtain ⟨huLenEq, hList⟩ := huAt
        subst huLenEq
        have hTag1 : mem ptr = 1 := by simpa using hList 0 (by simp)
        have hTagS : s.mem ptr = 1 := by simpa using (hMemPtr 0 (by omega)).trans hTag1
        let t1 := { s with regs := Function.update s.regs 13 1 }
        let t2 := { t1 with regs := Function.update t1.regs 8 (ptr + 2) }
        have rt1 : Runs w p ω' (.assign 13 (.load (.reg 8))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h8, hTagS], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 8 (.bin .add (.reg 8) (.const 2))) t1 .normal t2 4 :=
          runs_assign_iff.mpr ⟨ptr + 2, by simp [Expr.eval, BinOp.eval, t1, h8, show 2 < 2 ^ w by omega, hPtrNextW],
            rfl, rfl, rfl⟩
        have rInner : Runs w p ω'
            (.cond (.bin .eq (.reg 13) (.const 1)) (.assign 8 (.bin .add (.reg 8) (.const 2)))
              (.assign 14 (.load (.bin .add (.reg 8) (.const 3))) ;;
               .assign 15 (.load (.bin .add (.reg 8) (.const 4))) ;;
               .assign 8 (.bin .add (.bin .add (.bin .add (.reg 8) (.const 5)) (.reg 14)) (.reg 15))))
            t1 .normal t2 8 :=
          runs_cond_iff.mpr ⟨1, 4, by simp [Expr.eval, BinOp.eval, t1, hw1], by simpa using rt2, by simp [Expr.size]⟩
        have rCond : Runs w p ω'
            (.cond (.bin .eq (.reg 13) (.const 0))
              (.assign 14 (.load (.bin .add (.reg 8) (.const 1))) ;;
               .call 11 edgeProc [.reg 9, .reg 10, .reg 2, .reg 3, .reg 14, .reg 4, .reg 5, .reg 11] ;;
               .assign 8 (.bin .add (.reg 8) (.const 4)))
              (.cond (.bin .eq (.reg 13) (.const 1)) (.assign 8 (.bin .add (.reg 8) (.const 2)))
                (.assign 14 (.load (.bin .add (.reg 8) (.const 3))) ;;
                 .assign 15 (.load (.bin .add (.reg 8) (.const 4))) ;;
                 .assign 8 (.bin .add (.bin .add (.bin .add (.reg 8) (.const 5)) (.reg 14)) (.reg 15)))))
            t1 .normal t2 12 :=
          runs_cond_iff.mpr ⟨0, 8, by simp [Expr.eval, BinOp.eval, t1, show (0 : ℕ) < 2 ^ w by omega],
            by simpa using rInner, by simp [Expr.size]⟩
        have hInvN : Inv (i + 1) { t2 with regs := Function.update t2.regs 12 (i + 1) } :=
          ⟨ptr + 2, remW - 2, curH,
            by simp [t2, t1, h0], by simp [t2, t1, h1], by simp [t2, t1, h2], by simp [t2, t1, h3],
            by simp [t2, t1, h4], by simp [t2, t1, h5], by simp [t2, t1, h6], by simp [t2, t1, h7],
            by simp [t2], by simp [t2, t1, h9], by simp [t2, t1, h10], by simp [t2, t1, h11], by simp,
            by omega, by omega, by simpa [hTakeNext, hUi] using hBodyRest, hHLo,
            hHHi.trans (Nat.add_le_add_left (Nat.mul_le_mul_right sp (Nat.le_succ i)) _),
            hzS, hFr, fun x hx hni t ht => hKeep x hx (fun ⟨j, hjLt, hj, hjI⟩ => hni ⟨j, hjLt, by omega, hjI⟩) t ht,
            fun j hj hjLt => by
              by_cases hji : j = i
              · subst hji; simp [hUi]
              · exact hDone j (by omega) hjLt⟩
        refine ⟨.normal, t2, _, runs_seq_iff.mpr (Or.inr ⟨t1, 3, 12, rt1, rCond, rfl⟩),
          ⟨hInvN, by simp [t2, t1, h12]⟩, by dsimp [stepCost]; omega⟩
      | split v v' St Sh =>
        simp only [hUi, UpdateAt] at huAt
        have ⟨tag, k1, k2, hTagGe2, huLenEq, hList⟩ :
            ∃ (tag : ℕ) (k1 k2 : List ℕ), 2 ≤ tag ∧ uLen = 5 + k1.length + k2.length ∧
              ListAt mem ptr ([tag, v, v', k1.length, k2.length] ++ k1 ++ k2) := by
          rcases huAt with ⟨k1, k2, _, _, _, _, hl, hli⟩ | ⟨k1, k2, _, _, _, _, hl, hli⟩
          · exact ⟨2, k1, k2, by omega, hl, hli⟩
          · exact ⟨3, k1, k2, by omega, hl, hli⟩
        subst huLenEq
        have hTagEq : mem ptr = tag := by simpa using hList 0 (by simp)
        have hk1Eq : mem (ptr + 3) = k1.length := by simpa using hList 3 (by simp)
        have hk2Eq : mem (ptr + 4) = k2.length := by simpa using hList 4 (by simp)
        have hTagVal : 2 ≤ s.mem ptr := by rw [show s.mem ptr = mem ptr by simpa using hMemPtr 0 (by omega), hTagEq]; exact hTagGe2
        have hk1S : s.mem (ptr + 3) = k1.length := (hMemPtr 3 (by omega)).trans hk1Eq
        have hk2S : s.mem (ptr + 4) = k2.length := (hMemPtr 4 (by omega)).trans hk2Eq
        let t1 := { s with regs := Function.update s.regs 13 (s.mem ptr) }
        let t2 := { t1 with regs := Function.update t1.regs 14 k1.length }
        let t3 := { t2 with regs := Function.update t2.regs 15 k2.length }
        let t4 := { t3 with regs := Function.update t3.regs 8 (ptr + 5 + k1.length + k2.length) }
        have rt1 : Runs w p ω' (.assign 13 (.load (.reg 8))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨s.mem ptr, by simp [Expr.eval, h8], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 14 (.load (.bin .add (.reg 8) (.const 3)))) t1 .normal t2 5 :=
          runs_assign_iff.mpr ⟨k1.length, by simp [Expr.eval, BinOp.eval, t1, h8, show 3 < 2 ^ w by omega,
            show ptr + 3 < 2 ^ w by omega, hk1S], rfl, rfl, rfl⟩
        have rt3 : Runs w p ω' (.assign 15 (.load (.bin .add (.reg 8) (.const 4)))) t2 .normal t3 5 :=
          runs_assign_iff.mpr ⟨k2.length, by simp [Expr.eval, BinOp.eval, t2, t1, h8, hw4,
            show ptr + 4 < 2 ^ w by omega, hk2S], rfl, rfl, rfl⟩
        have rt4 : Runs w p ω' (.assign 8 (.bin .add (.bin .add (.bin .add (.reg 8) (.const 5)) (.reg 14)) (.reg 15)))
            t3 .normal t4 8 :=
          runs_assign_iff.mpr ⟨ptr + 5 + k1.length + k2.length, by
            simp [Expr.eval, BinOp.eval, t3, t2, t1, h8, hw5, show ptr + 5 < 2 ^ w by omega,
              show ptr + 5 + k1.length < 2 ^ w by omega, show ptr + 5 + k1.length + k2.length < 2 ^ w by omega], rfl, rfl, rfl⟩
        have rSp : Runs w p ω' _ t1 .normal t4 20 :=
          runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, rt2, runs_seq_iff.mpr (Or.inr ⟨t3, 5, 8, rt3, rt4, rfl⟩), rfl⟩)
        have rInner : Runs w p ω'
            (.cond (.bin .eq (.reg 13) (.const 1)) (.assign 8 (.bin .add (.reg 8) (.const 2)))
              (.assign 14 (.load (.bin .add (.reg 8) (.const 3))) ;;
               .assign 15 (.load (.bin .add (.reg 8) (.const 4))) ;;
               .assign 8 (.bin .add (.bin .add (.bin .add (.reg 8) (.const 5)) (.reg 14)) (.reg 15))))
            t1 .normal t4 24 :=
          runs_cond_iff.mpr ⟨0, 20, by simp [Expr.eval, BinOp.eval, t1, hw1, show s.mem ptr ≠ 1 by omega],
            by simpa using rSp, by simp [Expr.size]⟩
        have rCond : Runs w p ω'
            (.cond (.bin .eq (.reg 13) (.const 0))
              (.assign 14 (.load (.bin .add (.reg 8) (.const 1))) ;;
               .call 11 edgeProc [.reg 9, .reg 10, .reg 2, .reg 3, .reg 14, .reg 4, .reg 5, .reg 11] ;;
               .assign 8 (.bin .add (.reg 8) (.const 4)))
              (.cond (.bin .eq (.reg 13) (.const 1)) (.assign 8 (.bin .add (.reg 8) (.const 2)))
                (.assign 14 (.load (.bin .add (.reg 8) (.const 3))) ;;
                 .assign 15 (.load (.bin .add (.reg 8) (.const 4))) ;;
                 .assign 8 (.bin .add (.bin .add (.bin .add (.reg 8) (.const 5)) (.reg 14)) (.reg 15)))))
            t1 .normal t4 28 :=
          runs_cond_iff.mpr ⟨0, 24, by simp [Expr.eval, BinOp.eval, t1, show (0 : ℕ) < 2 ^ w by omega,
            show s.mem ptr ≠ 0 by omega], by simpa using rInner, by simp [Expr.size]⟩
        have hInvN : Inv (i + 1) { t4 with regs := Function.update t4.regs 12 (i + 1) } :=
          ⟨ptr + (5 + k1.length + k2.length), remW - (5 + k1.length + k2.length), curH,
            by simp [t4, t3, t2, t1, h0], by simp [t4, t3, t2, t1, h1], by simp [t4, t3, t2, t1, h2],
            by simp [t4, t3, t2, t1, h3], by simp [t4, t3, t2, t1, h4], by simp [t4, t3, t2, t1, h5],
            by simp [t4, t3, t2, t1, h6], by simp [t4, t3, t2, t1, h7],
            by simp [t4, Nat.add_assoc], by simp [t4, t3, t2, t1, h9], by simp [t4, t3, t2, t1, h10],
            by simp [t4, t3, t2, t1, h11], by simp, by omega, by omega, by simpa [hTakeNext, hUi] using hBodyRest,
            hHLo, hHHi.trans (Nat.add_le_add_left (Nat.mul_le_mul_right sp (Nat.le_succ i)) _),
            hzS, hFr, fun x hx hni t ht => hKeep x hx (fun ⟨j, hjLt, hj, hjI⟩ => hni ⟨j, hjLt, by omega, hjI⟩) t ht,
            fun j hj hjLt => by
              by_cases hji : j = i
              · subst hji; simp [hUi]
              · exact hDone j (by omega) hjLt⟩
        refine ⟨.normal, t4, _, runs_seq_iff.mpr (Or.inr ⟨t1, 3, 28, rt1, rCond, rfl⟩),
          ⟨hInvN, by simp [t4, t3, t2, t1, h12]⟩, by dsimp [stepCost]; omega⟩)
  obtain ⟨o, out, cLoop, rLoop, hout, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hout
  | normal =>
    obtain ⟨_, _, nextH, _, _, _, _, _, _, _, _, _, _, _, h11End, _, _, _, _, hHLoEnd, hHHiEnd,
      hzEnd, hFrEnd, hKeepEnd, hDoneEnd⟩ := hout
    have rRet : Runs w p ω (.ret (.reg 11)) out (.returned nextH) out 2 :=
      runs_ret_iff.mpr ⟨nextH, by simp [Expr.eval, h11End], rfl, rfl, rfl⟩
    have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, r2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 3, _, r3,
          runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
            runs_seq_iff.mpr (Or.inr ⟨s5, 2, _, r5,
              runs_seq_iff.mpr (Or.inr ⟨out, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    refine ⟨nextH, out, _, rAll, hHLoEnd, hHHiEnd, ?_, ?_, hzEnd, hFrEnd⟩
    · have hrc : rangeCost (fun _ => stepCost) 0 U.length = U.length * stepCost := by simp [rangeCost]
      simp only [Expr.size, hrc] at hcLoop
      have hm : U.length * stepCost + U.length * 9 = U.length * (wireCoreLenEdgeCost K + 60) := by
        dsimp [stepCost]; ring
      omega
    · intro e he
      by_cases hIns : ∃ u ∈ U, u.Inserts e
      · obtain ⟨k, hk, hkIns⟩ := hMemIns e he hIns
        have hd := hDoneEnd k hk hk
        cases hUk : U[k] with
        | delete _ => simp [hUk, Update.Inserts] at hkIns
        | split _ _ _ _ => simp [hUk, Update.Inserts] at hkIns
        | insert ej _ _ =>
          simp only [hUk, Update.Inserts] at hkIns hd
          subst hkIns; exact hd
      · obtain ⟨heG, hEqL⟩ := hAgreeOld e he hIns
        have hNoJ : ¬ ∃ j, ∃ hj : j < U.length, j < U.length ∧ U[j].Inserts e :=
          fun ⟨j, hj, _, hji⟩ => hIns ⟨U[j], List.getElem_mem hj, hji⟩
        have hag (t : ℕ) (ht : t < L) : out.mem (curLenPtr + e * L + t) = mem (curLenPtr + e * L + t) :=
          hKeepEnd e (hGE e heG) hNoJ t ht
        refine ⟨fun t ht => by rw [hag t ht]; exact (hCurLen e heG).1 t ht, ?_⟩
        rw [← hEqL, ← (hCurLen e heG).2]; unfold Num.fixVal; congr 2
        exact Num.intVal_congr hag

end MinCostFlow.MinRatio
