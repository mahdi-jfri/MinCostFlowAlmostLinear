module

public import MinCostFlow.MinRatio.WireChainCoreRefreshSetup
public import MinCostFlow.Num.IsNegative
import WordRAM.Tactic

/-!
# Post-sync off-tree ready queue updates (`WireChainCoreReady`)

After `wireTreeSyncLoop` has synchronized the path tree with `newF`, off-tree edges (`slots[ei] = 0`)
whose detector residual is non-negative (`isNeg = 0`) must be present in `offReadyList`.
Provides two lightweight deterministic procedures:
1. `wireRebuildOffReadyBody` (`[root, mNew]`, Branch A): scans `j = 0 .. mNew - 1` (assuming
   `inOffReady[0..intCap)` was already zeroed and `offReadyCount = 0`), pushing every `j` with
   `slots[j] = 0` and `0 ≤ det j` onto `offReadyList`.
2. `wirePushReadyBatchBody` (`[root, uIntBuf]`, Branch B): scans edge-only `U_int`, pushing every
   `.insert ei _ _` with `slots[ei] = 0`, `inOffReady[ei] = 0`, and `0 ≤ det ei` onto `offReadyList`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.IPM.Machine

/-- Procedure `[root, mNew]` (`regs 0..1`): rebuilds `offReadyList` from scratch for `j < mNew`
with `slots[j] = 0` and `isNeg(edgeRecords[j].detector) = 0`, storing `offReadyCount` at `root + 11`. -/
@[expose] def wireRebuildOffReadyBody (isNeg : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 2) (.const 5))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 6))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 10))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 12))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const 13))) ;;
  .assign 8 (.const 0) ;;
  forRange 9 (.const 0) (.reg 1)
    (.cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 9))) (.const 0))
      (.assign 10 (.load (.bin .add (.reg 5) (.reg 9))) ;;
       .call 11 isNeg [.bin .add (.bin .add (.reg 10) (.const 2)) (.bin .mul (.const 3) (.reg 3)), .reg 3] ;;
       .cond (.bin .eq (.reg 11) (.const 0))
         (.store (.bin .add (.reg 6) (.reg 8)) (.reg 9) ;;
          .store (.bin .add (.reg 7) (.reg 9)) (.const 1) ;;
          .assign 8 (.bin .add (.reg 8) (.const 1)))
         .nop)
      .nop) ;;
  .store (.bin .add (.reg 0) (.const 11)) (.reg 8) ;;
  .ret (.reg 8)

theorem wireRebuildOffReadyBody_noRand (isNeg : ℕ) : (wireRebuildOffReadyBody isNeg).NoRand := by
  simp [wireRebuildOffReadyBody, forRange, forUp, Stmt.NoRand]

/-- Procedure `[root, uIntBuf]` (`regs 0..1`): scans edge-only `U_int`, pushing every `.insert ei _ _`
with `slots[ei] = 0`, `inOffReady[ei] = 0`, and `isNeg(edgeRecords[ei].detector) = 0` onto
`offReadyList`, updating `mem[root + 11]`. -/
@[expose] def wirePushReadyBatchBody (isNeg : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 2) (.const 5))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 6))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 10))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 11))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const 12))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const 13))) ;;
  .assign 9 (.load (.reg 1)) ;;
  .assign 10 (.bin .add (.reg 1) (.const 1)) ;;
  forRange 11 (.const 0) (.reg 9)
    (.assign 12 (.load (.reg 10)) ;;
     .cond (.bin .eq (.reg 12) (.const 0))
       (.assign 13 (.load (.bin .add (.reg 10) (.const 1))) ;;
        .assign 10 (.bin .add (.reg 10) (.const 4)) ;;
        .cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 13))) (.const 0))
          (.cond (.bin .eq (.load (.bin .add (.reg 8) (.reg 13))) (.const 0))
            (.assign 14 (.load (.bin .add (.reg 5) (.reg 13))) ;;
             .call 15 isNeg [.bin .add (.bin .add (.reg 14) (.const 2)) (.bin .mul (.const 3) (.reg 3)), .reg 3] ;;
             .cond (.bin .eq (.reg 15) (.const 0))
               (.store (.bin .add (.reg 7) (.reg 6)) (.reg 13) ;;
                .store (.bin .add (.reg 8) (.reg 13)) (.const 1) ;;
                .assign 6 (.bin .add (.reg 6) (.const 1)))
               .nop)
            .nop)
          .nop)
       (.assign 10 (.bin .add (.reg 10) (.const 2)))) ;;
  .store (.bin .add (.reg 0) (.const 11)) (.reg 6) ;;
  .ret (.reg 6)

theorem wirePushReadyBatchBody_noRand (isNeg : ℕ) : (wirePushReadyBatchBody isNeg).NoRand := by
  simp [wirePushReadyBatchBody, forRange, forUp, Stmt.NoRand]

/-- Execute `wireRebuildOffReadyBody`: given `inOffReady[0..intCap) = 0`, populates `offReadyList`
with all off-tree edges `j < mNew` (`slots[j] = 0`) satisfying `0 ≤ det j`, leaving all tree edges
(`slots[j] ≠ 0`) with `inOffReady[j] = 0`. -/
theorem wireRebuildOffReadyBody_runs
    {w isNeg root mNew handle table levelsEnd forward inverse freshCounter slots names
      slotThresholds edgeThresholds edgeRecords offReadyCount offReadyList inOffReady rootGraph
      intCap L pos : ℕ}
    {det : ℕ → ℤ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hisNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hRoot : SolverRootDirAt mem root handle table levelsEnd forward inverse freshCounter slots
      names slotThresholds edgeThresholds edgeRecords offReadyCount offReadyList inOffReady
      rootGraph intCap)
    (hLmem : mem (handle + 5) = L)
    (hmLe : mNew ≤ intCap) (hLpos : 0 < L)
    (hZeroIn : ∀ e < intCap, mem (inOffReady + e) = 0)
    (hDet : ∀ j < mNew, mem (slots + j) = 0 →
      PathIntAt mem (mem (edgeRecords + j) + 2 + 3 * L) 4 L (det j) ∧
      mem (edgeRecords + j) + 2 + 4 * L < 2 ^ w ∧
      (∀ t < L, (mem (edgeRecords + j) + 2 + 3 * L + t < inOffReady ∨ inOffReady + intCap ≤ mem (edgeRecords + j) + 2 + 3 * L + t) ∧
        (mem (edgeRecords + j) + 2 + 3 * L + t < offReadyList ∨ offReadyList + intCap ≤ mem (edgeRecords + j) + 2 + 3 * L + t)))
    (hDisj1 : offReadyList + intCap ≤ inOffReady ∨ inOffReady + intCap ≤ offReadyList)
    (hDisj2 : edgeRecords + intCap ≤ offReadyList ∨ offReadyList + intCap ≤ edgeRecords)
    (hDisj3 : edgeRecords + intCap ≤ inOffReady ∨ inOffReady + intCap ≤ edgeRecords)
    (hDisj4 : slots + intCap ≤ offReadyList ∨ offReadyList + intCap ≤ slots)
    (hDisj5 : slots + intCap ≤ inOffReady ∨ inOffReady + intCap ≤ slots)
    (hDisjR1 : root + 11 < offReadyList ∨ offReadyList + intCap ≤ root + 11)
    (hDisjR2 : root + 11 < inOffReady ∨ inOffReady + intCap ≤ root + 11)
    (hW1 : root + 16 < 2 ^ w) (hW2 : handle + 6 < 2 ^ w)
    (hW3 : slots + intCap < 2 ^ w) (hW4 : edgeRecords + intCap < 2 ^ w)
    (hW5 : offReadyList + intCap < 2 ^ w) (hW6 : inOffReady + intCap < 2 ^ w)
    (h3LW : 3 * L < 2 ^ w) (hw13 : 13 < 2 ^ w) :
    ∃ newCnt out cost,
      Runs w p ω (wireRebuildOffReadyBody isNeg)
        (startState [root, mNew] mem pos) (.returned newCnt) out cost ∧
      cost ≤ 80 * mNew + 80 ∧
      newCnt ≤ mNew ∧
      out.mem (root + 11) = newCnt ∧
      OffReadyInv out.mem newCnt offReadyList inOffReady intCap ∧
      (∀ j < mNew, out.mem (inOffReady + j) = if mem (slots + j) = 0 ∧ 0 ≤ det j then 1 else 0) ∧
      (∀ j, mNew ≤ j → j < intCap → out.mem (inOffReady + j) = 0) ∧
      ∀ a, a ≠ root + 11 → (a < offReadyList ∨ offReadyList + intCap ≤ a) →
        (a < inOffReady ∨ inOffReady + intCap ≤ a) → out.mem a = mem a := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  let s0 := startState [root, mNew] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 2 handle }
  let s2 := { s1 with regs := Function.update s1.regs 3 L }
  let s3 := { s2 with regs := Function.update s2.regs 4 slots }
  let s4 := { s3 with regs := Function.update s3.regs 5 edgeRecords }
  let s5 := { s4 with regs := Function.update s4.regs 6 offReadyList }
  let s6 := { s5 with regs := Function.update s5.regs 7 inOffReady }
  let s7 := { s6 with regs := Function.update s6.regs 8 0 }
  have r1 : Runs w p ω (.assign 2 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, s0, startState, show mem root = handle by simpa using hRoot 0 (by simp)], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 2) (.const 5)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, BinOp.eval, s1, s0, startState, show 5 < 2 ^ w by omega, show handle + 5 < 2 ^ w by omega, hLmem], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const 6)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨slots, by simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, show 6 < 2 ^ w by omega,
      show root + 6 < 2 ^ w by omega, show mem (root + 6) = slots by simpa using hRoot 6 (by simp)], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const 10)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨edgeRecords, by simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, show 10 < 2 ^ w by omega,
      show root + 10 < 2 ^ w by omega, show mem (root + 10) = edgeRecords by simpa using hRoot 10 (by simp)], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const 12)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨offReadyList, by simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState, show 12 < 2 ^ w by omega,
      show root + 12 < 2 ^ w by omega, show mem (root + 12) = offReadyList by simpa using hRoot 12 (by simp)], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const 13)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨inOffReady, by simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, startState, hw13,
      show root + 13 < 2 ^ w by omega, show mem (root + 13) = inOffReady by simpa using hRoot 13 (by simp)], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 8 (.const 0)) s6 .normal s7 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  let Inv (j : ℕ) (s : State) : Prop :=
    ∃ cnt, j ≤ mNew ∧ cnt ≤ j ∧ s.regs 0 = root ∧ s.regs 1 = mNew ∧ s.regs 3 = L ∧
    s.regs 4 = slots ∧ s.regs 5 = edgeRecords ∧ s.regs 6 = offReadyList ∧ s.regs 7 = inOffReady ∧
    s.regs 8 = cnt ∧ s.regs 9 = j ∧
    OffReadyInv s.mem cnt offReadyList inOffReady intCap ∧
    (∀ k < j, s.mem (inOffReady + k) = if mem (slots + k) = 0 ∧ 0 ≤ det k then 1 else 0) ∧
    (∀ k, j ≤ k → k < intCap → s.mem (inOffReady + k) = 0) ∧
    ∀ a, (a < offReadyList ∨ offReadyList + intCap ≤ a) →
      (a < inOffReady ∨ inOffReady + intCap ≤ a) → s.mem a = mem a
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 9) (lo := .const 0) (hi := .reg 1)
    (P := fun s => s = s7) (Inv := Inv) 70 0 mNew (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], 0, Nat.zero_le _, le_rfl,
        by simp [s7, s6, s5, s4, s3, s2, s1, s0, startState], by simp [s7, s6, s5, s4, s3, s2, s1, s0, startState],
        by simp [s7, s6, s5, s4, s3, s2], by simp [s7, s6, s5, s4, s3], by simp [s7, s6, s5, s4],
        by simp [s7, s6, s5], by simp [s7, s6], by simp [s7], by simp,
        ⟨Nat.zero_le _, fun _ h => by omega, fun _ h => by omega,
          fun e he => Or.inl (hZeroIn e he), fun e he h1 => by
            change mem (inOffReady + e) = 1 at h1; rw [hZeroIn e he] at h1; omega⟩,
        fun _ hk => by omega, fun k _ hk => hZeroIn k hk, fun _ _ _ => rfl⟩)
    (fun _ _ _ _ h => by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h9, _⟩ := h; exact h9)
    (fun _ _ _ _ h => by obtain ⟨_, _, _, _, h1, _⟩ := h; simp [Expr.eval, h1])
    (fun j _ hj s ω' hI => by
      obtain ⟨cnt, _, hcntLe, h0, h1, h3, h4, h5, h6, h7, h8, h9, hOffS, hDoneS, hZeroS, hFrS⟩ := hI
      let pushBody1 : Stmt :=
        .store (.bin .add (.reg 6) (.reg 8)) (.reg 9) ;;
        .store (.bin .add (.reg 7) (.reg 9)) (.const 1) ;;
        .assign 8 (.bin .add (.reg 8) (.const 1))
      let thenSlot : Stmt :=
        .assign 10 (.load (.bin .add (.reg 5) (.reg 9))) ;;
        .call 11 isNeg [.bin .add (.bin .add (.reg 10) (.const 2)) (.bin .mul (.const 3) (.reg 3)), .reg 3] ;;
        .cond (.bin .eq (.reg 11) (.const 0)) pushBody1 .nop
      have hSlotEq : s.mem (slots + j) = mem (slots + j) :=
        hFrS _ (by rcases hDisj4 with h | h <;> omega) (by rcases hDisj5 with h | h <;> omega)
      by_cases hSlot0 : mem (slots + j) = 0
      · let recPtr := mem (edgeRecords + j)
        have hRecEq : s.mem (edgeRecords + j) = recPtr :=
          hFrS _ (by rcases hDisj2 with h | h <;> omega) (by rcases hDisj3 with h | h <;> omega)
        let t1 := { s with regs := Function.update s.regs 10 recPtr }
        have rt1 : Runs w p ω' (.assign 10 (.load (.bin .add (.reg 5) (.reg 9)))) s .normal t1 5 :=
          runs_assign_iff.mpr ⟨recPtr, by simp [Expr.eval, BinOp.eval, h5, h9, show edgeRecords + j < 2 ^ w by omega, hRecEq],
            rfl, rfl, rfl⟩
        obtain ⟨hDetJ, hRecW, hDetDisj⟩ := hDet j hj hSlot0
        have hDetT1 : PathIntAt t1.mem (recPtr + 2 + 3 * L) 4 L (det j) :=
          hDetJ.congr (fun t ht => hFrS _ (hDetDisj t ht).2 (hDetDisj t ht).1)
        obtain ⟨t2, cN, negBit, rt2, hpN, hr2_11, ht2Regs, hcN⟩ :=
          runs_call_of_meetsContract (r := 11)
            (args := [.bin .add (.bin .add (.reg 10) (.const 2)) (.bin .mul (.const 3) (.reg 3)), .reg 3])
            hisNeg (st := t1) (vs := [recPtr + 2 + 3 * L, L])
            (by simp [evalArgs, Expr.eval, BinOp.eval, t1, h3, hw2, hw3, h3LW,
              show recPtr + 2 < 2 ^ w by omega, show recPtr + 2 + 3 * L < 2 ^ w by omega])
            (by simp [show recPtr + 2 + 3 * L < 2 ^ w by omega, show L < 2 ^ w by omega])
            ⟨recPtr + 2 + 3 * L, L, rfl, by omega, hDetT1.1⟩ ω'
        obtain ⟨ht2Mem, hNegEq⟩ := hpN
        have hNegVal : negBit = if det j < 0 then 1 else 0 := by simpa [hDetT1.2] using hNegEq
        have hcNLe : cN ≤ 24 := by simp only [Num.isNegativeContract, argsSize, Expr.size] at hcN; omega
        by_cases hlt : det j < 0
        · have hnb : negBit = 1 := by simp [hNegVal, hlt]
          have rIn : Runs w p ω' (.cond (.bin .eq (.reg 11) (.const 0)) pushBody1 .nop) t2 .normal t2 5 :=
            runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, hr2_11, hnb, show 0 < 2 ^ w by omega],
              by simp [runs_nop_iff], by simp [Expr.size]⟩
          have rOut : Runs w p ω' (.cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 9))) (.const 0)) thenSlot .nop)
              s .normal t2 (6 + (5 + (cN + 5 + 1) + 1) + 1) :=
            runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, h4, h9, show slots + j < 2 ^ w by omega,
              hSlotEq, hSlot0, show 0 < 2 ^ w by omega, hw1],
              by simpa [thenSlot] using runs_seq_iff.mpr (Or.inr ⟨t1, 5, _, rt1,
                runs_seq_iff.mpr (Or.inr ⟨t2, cN, 5, rt2, rIn, rfl⟩), rfl⟩), by simp [Expr.size]⟩
          refine ⟨.normal, t2, _, rOut, ⟨⟨cnt, by omega, by omega,
            by simp only [Function.update_of_ne (by decide : (0 : ℕ) ≠ 9)]; rw [ht2Regs 0 (by decide)]; simp [t1, h0],
            by simp only [Function.update_of_ne (by decide : (1 : ℕ) ≠ 9)]; rw [ht2Regs 1 (by decide)]; simp [t1, h1],
            by simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 9)]; rw [ht2Regs 3 (by decide)]; simp [t1, h3],
            by simp only [Function.update_of_ne (by decide : (4 : ℕ) ≠ 9)]; rw [ht2Regs 4 (by decide)]; simp [t1, h4],
            by simp only [Function.update_of_ne (by decide : (5 : ℕ) ≠ 9)]; rw [ht2Regs 5 (by decide)]; simp [t1, h5],
            by simp only [Function.update_of_ne (by decide : (6 : ℕ) ≠ 9)]; rw [ht2Regs 6 (by decide)]; simp [t1, h6],
            by simp only [Function.update_of_ne (by decide : (7 : ℕ) ≠ 9)]; rw [ht2Regs 7 (by decide)]; simp [t1, h7],
            by simp only [Function.update_of_ne (by decide : (8 : ℕ) ≠ 9)]; rw [ht2Regs 8 (by decide)]; simp [t1, h8], by simp,
            ht2Mem.symm ▸ hOffS,
            fun k hk => by
              rw [ht2Mem]
              by_cases hkj : k = j
              · subst hkj; simp [show ¬ (mem (slots + k) = 0 ∧ 0 ≤ det k) by omega]; exact hZeroS k le_rfl (by omega)
              · exact hDoneS k (by omega),
            fun k hk1 hk2 => by rw [ht2Mem]; exact hZeroS k (by omega) hk2,
            fun a ha1 ha2 => by rw [ht2Mem]; exact hFrS a ha1 ha2⟩,
            by rw [ht2Regs 9 (by decide)]; simp [t1, h9]⟩, by dsimp only; omega⟩
        · have hnb : negBit = 0 := by simp [hNegVal, hlt]
          have hZeroJ : t2.mem (inOffReady + j) = 0 := by rw [ht2Mem]; exact hZeroS j le_rfl (by omega)
          obtain ⟨hCntLt, hOffNew⟩ := wireCore_offReadyInv_push (ht2Mem.symm ▸ hOffS) (by omega) hZeroJ hDisj1
          let t3 := { t2 with mem := Function.update t2.mem (offReadyList + cnt) j }
          let t4 := { t3 with mem := Function.update t3.mem (inOffReady + j) 1 }
          let t5 := { t4 with regs := Function.update t4.regs 8 (cnt + 1) }
          have rt3 : Runs w p ω' (.store (.bin .add (.reg 6) (.reg 8)) (.reg 9)) t2 .normal t3 5 :=
            runs_store_iff.mpr ⟨offReadyList + cnt, j, by
              simp [Expr.eval, BinOp.eval, ht2Regs 6 (by decide), ht2Regs 8 (by decide), t1, h6, h8,
                show offReadyList + cnt < 2 ^ w by omega],
              by simp [Expr.eval, ht2Regs 9 (by decide), t1, h9], rfl, rfl, rfl⟩
          have rt4 : Runs w p ω' (.store (.bin .add (.reg 7) (.reg 9)) (.const 1)) t3 .normal t4 5 :=
            runs_store_iff.mpr ⟨inOffReady + j, 1, by
              simp [Expr.eval, BinOp.eval, t3, ht2Regs 7 (by decide), ht2Regs 9 (by decide), t1, h7, h9,
                show inOffReady + j < 2 ^ w by omega],
              by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
          have rt5 : Runs w p ω' (.assign 8 (.bin .add (.reg 8) (.const 1))) t4 .normal t5 4 :=
            runs_assign_iff.mpr ⟨cnt + 1, by
              simp [Expr.eval, BinOp.eval, t4, t3, ht2Regs 8 (by decide), t1, h8, hw1,
                show cnt + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
          have rIn : Runs w p ω' (.cond (.bin .eq (.reg 11) (.const 0)) pushBody1 .nop) t2 .normal t5 20 :=
            runs_cond_iff.mpr ⟨1, 16, by simp [Expr.eval, BinOp.eval, hr2_11, hnb, show 0 < 2 ^ w by omega, hw1],
              by simpa [pushBody1] using runs_seq_iff.mpr (Or.inr ⟨t3, 5, _, rt3, runs_seq_iff.mpr (Or.inr ⟨t4, 5, 4, rt4, rt5, rfl⟩), rfl⟩),
              by simp [Expr.size]⟩
          have rOut : Runs w p ω' (.cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 9))) (.const 0)) thenSlot .nop)
              s .normal t5 (6 + (5 + (cN + 20 + 1) + 1) + 1) :=
            runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, h4, h9, show slots + j < 2 ^ w by omega,
              hSlotEq, hSlot0, show 0 < 2 ^ w by omega, hw1],
              by simpa [thenSlot] using runs_seq_iff.mpr (Or.inr ⟨t1, 5, _, rt1,
                runs_seq_iff.mpr (Or.inr ⟨t2, cN, 20, rt2, rIn, rfl⟩), rfl⟩), by simp [Expr.size]⟩
          refine ⟨.normal, t5, _, rOut, ⟨⟨cnt + 1, by omega, by omega,
            by simp only [t5, t4, t3, Function.update_of_ne (by decide : (0 : ℕ) ≠ 9), Function.update_of_ne (by decide : (0 : ℕ) ≠ 8)]; rw [ht2Regs 0 (by decide)]; simp [t1, h0],
            by simp only [t5, t4, t3, Function.update_of_ne (by decide : (1 : ℕ) ≠ 9), Function.update_of_ne (by decide : (1 : ℕ) ≠ 8)]; rw [ht2Regs 1 (by decide)]; simp [t1, h1],
            by simp only [t5, t4, t3, Function.update_of_ne (by decide : (3 : ℕ) ≠ 9), Function.update_of_ne (by decide : (3 : ℕ) ≠ 8)]; rw [ht2Regs 3 (by decide)]; simp [t1, h3],
            by simp only [t5, t4, t3, Function.update_of_ne (by decide : (4 : ℕ) ≠ 9), Function.update_of_ne (by decide : (4 : ℕ) ≠ 8)]; rw [ht2Regs 4 (by decide)]; simp [t1, h4],
            by simp only [t5, t4, t3, Function.update_of_ne (by decide : (5 : ℕ) ≠ 9), Function.update_of_ne (by decide : (5 : ℕ) ≠ 8)]; rw [ht2Regs 5 (by decide)]; simp [t1, h5],
            by simp only [t5, t4, t3, Function.update_of_ne (by decide : (6 : ℕ) ≠ 9), Function.update_of_ne (by decide : (6 : ℕ) ≠ 8)]; rw [ht2Regs 6 (by decide)]; simp [t1, h6],
            by simp only [t5, t4, t3, Function.update_of_ne (by decide : (7 : ℕ) ≠ 9), Function.update_of_ne (by decide : (7 : ℕ) ≠ 8)]; rw [ht2Regs 7 (by decide)]; simp [t1, h7],
            by simp [t5], by simp, hOffNew,
            fun k hk => by
              by_cases hkj : k = j
              · subst hkj; simp [hSlot0, not_lt.mp hlt, t5, t4]
              · simp only [t5, t4, t3, Function.update_of_ne (by omega : inOffReady + k ≠ inOffReady + j),
                  Function.update_of_ne (by rcases hDisj1 with h | h <;> omega : inOffReady + k ≠ offReadyList + cnt), ht2Mem]
                exact hDoneS k (by omega),
            fun k hk1 hk2 => by
              simp only [t5, t4, t3, Function.update_of_ne (by omega : inOffReady + k ≠ inOffReady + j),
                Function.update_of_ne (by rcases hDisj1 with h | h <;> omega : inOffReady + k ≠ offReadyList + cnt), ht2Mem]
              exact hZeroS k (by omega) hk2,
            fun a ha1 ha2 => by
              simp only [t5, t4, t3, Function.update_of_ne (by rcases ha2 with h | h <;> omega : a ≠ inOffReady + j),
                Function.update_of_ne (by rcases ha1 with h | h <;> omega : a ≠ offReadyList + cnt), ht2Mem]
              exact hFrS a ha1 ha2⟩,
            by simp only [t5, t4, t3, Function.update_of_ne (by decide : (9 : ℕ) ≠ 8)]; rw [ht2Regs 9 (by decide)]; simp [t1, h9]⟩,
            by dsimp only; omega⟩
      · have rOut : Runs w p ω' (.cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 9))) (.const 0)) thenSlot .nop)
            s .normal s 8 :=
          runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, h4, h9, show slots + j < 2 ^ w by omega,
            hSlotEq, hSlot0, show 0 < 2 ^ w by omega], by simp [runs_nop_iff], by simp [Expr.size]⟩
        refine ⟨.normal, s, 8, rOut, ⟨⟨cnt, by omega, by omega,
          by simp [h0], by simp [h1], by simp [h3], by simp [h4], by simp [h5], by simp [h6], by simp [h7],
          by simp [h8], by simp, hOffS,
          fun k hk => by
            by_cases hkj : k = j
            · subst hkj; simp [hSlot0]; exact hZeroS k le_rfl (by omega)
            · exact hDoneS k (by omega),
          fun k hk1 hk2 => hZeroS k (by omega) hk2, hFrS⟩, h9⟩, by dsimp only; omega⟩)
  obtain ⟨o, s8, cL, rL, hL, hcL⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hL
  | normal =>
    obtain ⟨newCnt, _, hncLe, h8_0, _, _, _, _, _, _, h8_8, _, hOff8, hDone8, hZero8, hFr8⟩ := hL
    let out := { s8 with mem := Function.update s8.mem (root + 11) newCnt }
    have rStore : Runs w p ω (.store (.bin .add (.reg 0) (.const 11)) (.reg 8)) s8 .normal out 5 :=
      runs_store_iff.mpr ⟨root + 11, newCnt, by simp [Expr.eval, BinOp.eval, h8_0, show 11 < 2 ^ w by omega,
        show root + 11 < 2 ^ w by omega], by simp [Expr.eval, h8_8], rfl, rfl, rfl⟩
    have rRet : Runs w p ω (.ret (.reg 8)) out (.returned newCnt) out 2 :=
      runs_ret_iff.mpr ⟨newCnt, by simp [Expr.eval, out, h8_8], rfl, rfl, rfl⟩
    have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, r5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 5, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨s7, 2, _, r7,
      runs_seq_iff.mpr (Or.inr ⟨s8, cL, _, rL,
      runs_seq_iff.mpr (Or.inr ⟨out, 5, 2, rStore, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have hOutNe (a : ℕ) (hne : a ≠ root + 11) : out.mem a = s8.mem a := Function.update_of_ne hne _ _
    simp only [Expr.size] at hcL
    refine ⟨newCnt, out, _, rAll, by omega, hncLe, by simp [out], ?_,
      fun j hj => (hOutNe _ (by rcases hDisjR2 with h | h <;> omega)).trans (hDone8 j hj),
      fun j h1 h2 => (hOutNe _ (by rcases hDisjR2 with h | h <;> omega)).trans (hZero8 j h1 h2),
      fun a h1 h2 h3 => (hOutNe a h1).trans (hFr8 a h2 h3)⟩
    obtain ⟨hcnt, hmemL, hdist, hbits, hrev⟩ := hOff8
    refine ⟨hcnt, fun j hj => by
        rw [hOutNe _ (by rcases hDisjR1 with h | h <;> omega),
            hOutNe _ (by have := (hmemL j hj).1; rcases hDisjR2 with h | h <;> omega)]
        exact hmemL j hj,
      fun j₁ hj₁ j₂ hj₂ hne => by
        rw [hOutNe _ (by rcases hDisjR1 with h | h <;> omega),
            hOutNe _ (by rcases hDisjR1 with h | h <;> omega)]
        exact hdist j₁ hj₁ j₂ hj₂ hne,
      fun e he => by rw [hOutNe _ (by rcases hDisjR2 with h | h <;> omega)]; exact hbits e he,
      fun e he h1 => by
        rw [hOutNe _ (by rcases hDisjR2 with h | h <;> omega)] at h1
        obtain ⟨j, hj, hje⟩ := hrev e he h1
        exact ⟨j, hj, (hOutNe _ (by rcases hDisjR1 with h | h <;> omega)).trans hje⟩⟩

/-- Execute `wirePushReadyBatchBody`: pushes every inserted off-tree edge `ei` in `U_int` with
`slots[ei] = 0`, `inOffReady[ei] = 0`, and `0 ≤ det ei` onto `offReadyList`, updating
`mem[root + 11]`. -/
theorem wirePushReadyBatchBody_runs
    {w isNeg root uIntBuf handle table levelsEnd forward inverse freshCounter slots names
      slotThresholds edgeThresholds edgeRecords offReadyCount offReadyList inOffReady rootGraph
      intCap L pos : ℕ}
    {U_int : List Update} {det : ℕ → ℤ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hisNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hRoot : SolverRootDirAt mem root handle table levelsEnd forward inverse freshCounter slots
      names slotThresholds edgeThresholds edgeRecords offReadyCount offReadyList inOffReady
      rootGraph intCap)
    (hLmem : mem (handle + 5) = L)
    (hBatch : IPM.Machine.BatchAt mem uIntBuf U_int)
    (hEdgeOnly : ∀ u ∈ U_int, IsEdgeUpdate u)
    (hOffInv : OffReadyInv mem offReadyCount offReadyList inOffReady intCap)
    (hLpos : 0 < L)
    (hInsInfo : ∀ u ∈ U_int, match u with
      | .insert ei _ _ =>
        ei < intCap ∧
        (mem (slots + ei) = 0 →
          PathIntAt mem (mem (edgeRecords + ei) + 2 + 3 * L) 4 L (det ei) ∧
          mem (edgeRecords + ei) + 2 + 4 * L < 2 ^ w ∧
          (∀ t < L, (mem (edgeRecords + ei) + 2 + 3 * L + t < inOffReady ∨ inOffReady + intCap ≤ mem (edgeRecords + ei) + 2 + 3 * L + t) ∧
            (mem (edgeRecords + ei) + 2 + 3 * L + t < offReadyList ∨ offReadyList + intCap ≤ mem (edgeRecords + ei) + 2 + 3 * L + t)))
      | _ => True)
    (hDisj1 : offReadyList + intCap ≤ inOffReady ∨ inOffReady + intCap ≤ offReadyList)
    (hDisj2 : edgeRecords + intCap ≤ offReadyList ∨ offReadyList + intCap ≤ edgeRecords)
    (hDisj3 : edgeRecords + intCap ≤ inOffReady ∨ inOffReady + intCap ≤ edgeRecords)
    (hDisj4 : slots + intCap ≤ offReadyList ∨ offReadyList + intCap ≤ slots)
    (hDisj5 : slots + intCap ≤ inOffReady ∨ inOffReady + intCap ≤ slots)
    (hDisjB1 : uIntBuf + (batchWords U_int).length ≤ offReadyList ∨ offReadyList + intCap ≤ uIntBuf)
    (hDisjB2 : uIntBuf + (batchWords U_int).length ≤ inOffReady ∨ inOffReady + intCap ≤ uIntBuf)
    (hDisjR1 : root + 11 < offReadyList ∨ offReadyList + intCap ≤ root + 11)
    (hDisjR2 : root + 11 < inOffReady ∨ inOffReady + intCap ≤ root + 11)
    (hW1 : root + 16 < 2 ^ w) (hW2 : handle + 6 < 2 ^ w)
    (hW3 : slots + intCap < 2 ^ w) (hW4 : edgeRecords + intCap < 2 ^ w)
    (hW5 : offReadyList + intCap < 2 ^ w) (hW6 : inOffReady + intCap < 2 ^ w)
    (hW7 : uIntBuf + (batchWords U_int).length < 2 ^ w)
    (h3LW : 3 * L < 2 ^ w) (hw13 : 13 < 2 ^ w) :
    ∃ newCnt out cost,
      Runs w p ω (wirePushReadyBatchBody isNeg)
        (startState [root, uIntBuf] mem pos) (.returned newCnt) out cost ∧
      cost ≤ 100 * U_int.length + 100 ∧
      offReadyCount ≤ newCnt ∧ newCnt ≤ offReadyCount + U_int.length ∧
      out.mem (root + 11) = newCnt ∧
      OffReadyInv out.mem newCnt offReadyList inOffReady intCap ∧
      (∀ ei < intCap, mem (slots + ei) ≠ 0 → out.mem (inOffReady + ei) = mem (inOffReady + ei)) ∧
      (∀ ei < intCap, mem (inOffReady + ei) = 1 → out.mem (inOffReady + ei) = 1) ∧
      (∀ ei u v, .insert ei u v ∈ U_int → mem (slots + ei) = 0 → 0 ≤ det ei →
        out.mem (inOffReady + ei) = 1) ∧
      ∀ a, a ≠ root + 11 → (a < offReadyList ∨ offReadyList + intCap ≤ a) →
        (a < inOffReady ∨ inOffReady + intCap ≤ a) → out.mem a = mem a := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hLenB0 : mem uIntBuf = U_int.length := by simpa [batchWords] using hBatch 0 (by simp [batchWords])
  have hULenW : U_int.length < 2 ^ w := by
    have h2 : ∀ Lst : List Update, (∀ u ∈ Lst, IsEdgeUpdate u) →
        2 * Lst.length ≤ (Lst.flatMap updateWords).length := by
      intro Lst hL; induction Lst with
      | nil => simp
      | cons u rest ih =>
        have hu := hL u List.mem_cons_self
        have hr := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
        cases u with
        | insert _ _ _ => simp only [List.flatMap_cons, List.length_append, updateWords, List.length_cons, List.length_nil]; omega
        | delete _ => simp only [List.flatMap_cons, List.length_append, updateWords, List.length_cons, List.length_nil]; omega
        | split _ _ _ _ => exact hu.elim
    have := h2 U_int hEdgeOnly; simp only [batchWords, List.length_cons] at hW7; omega
  let s0 := startState [root, uIntBuf] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 2 handle }
  let s2 := { s1 with regs := Function.update s1.regs 3 L }
  let s3 := { s2 with regs := Function.update s2.regs 4 slots }
  let s4 := { s3 with regs := Function.update s3.regs 5 edgeRecords }
  let s5 := { s4 with regs := Function.update s4.regs 6 offReadyCount }
  let s6 := { s5 with regs := Function.update s5.regs 7 offReadyList }
  let s7 := { s6 with regs := Function.update s6.regs 8 inOffReady }
  let s8 := { s7 with regs := Function.update s7.regs 9 U_int.length }
  let s9 := { s8 with regs := Function.update s8.regs 10 (uIntBuf + 1) }
  have r1 : Runs w p ω (.assign 2 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, s0, startState, show mem root = handle by simpa using hRoot 0 (by simp)], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 2) (.const 5)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, BinOp.eval, s1, s0, startState, show 5 < 2 ^ w by omega, show handle + 5 < 2 ^ w by omega, hLmem], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const 6)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨slots, by simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, show 6 < 2 ^ w by omega,
      show root + 6 < 2 ^ w by omega, show mem (root + 6) = slots by simpa using hRoot 6 (by simp)], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const 10)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨edgeRecords, by simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, show 10 < 2 ^ w by omega,
      show root + 10 < 2 ^ w by omega, show mem (root + 10) = edgeRecords by simpa using hRoot 10 (by simp)], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const 11)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨offReadyCount, by simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState, show 11 < 2 ^ w by omega,
      show root + 11 < 2 ^ w by omega, show mem (root + 11) = offReadyCount by simpa using hRoot 11 (by simp)], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const 12)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨offReadyList, by simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, startState, show 12 < 2 ^ w by omega,
      show root + 12 < 2 ^ w by omega, show mem (root + 12) = offReadyList by simpa using hRoot 12 (by simp)], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 0) (.const 13)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨inOffReady, by simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, s0, startState, hw13,
      show root + 13 < 2 ^ w by omega, show mem (root + 13) = inOffReady by simpa using hRoot 13 (by simp)], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 9 (.load (.reg 1))) s7 .normal s8 3 :=
    runs_assign_iff.mpr ⟨U_int.length, by simp [Expr.eval, s7, s6, s5, s4, s3, s2, s1, s0, startState, hLenB0], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 10 (.bin .add (.reg 1) (.const 1))) s8 .normal s9 4 :=
    runs_assign_iff.mpr ⟨uIntBuf + 1, by simp [Expr.eval, BinOp.eval, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState,
      hw1, show uIntBuf + 1 < 2 ^ w by simp [batchWords] at hW7; omega], rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) : Prop :=
    ∃ cnt, offReadyCount ≤ cnt ∧ cnt ≤ offReadyCount + i ∧
    s.regs 0 = root ∧ s.regs 3 = L ∧ s.regs 4 = slots ∧ s.regs 5 = edgeRecords ∧
    s.regs 6 = cnt ∧ s.regs 7 = offReadyList ∧ s.regs 8 = inOffReady ∧ s.regs 9 = U_int.length ∧
    s.regs 10 = uIntBuf + 1 + edgeRecOff U_int i ∧ s.regs 11 = i ∧
    OffReadyInv s.mem cnt offReadyList inOffReady intCap ∧
    (∀ ei < intCap, mem (slots + ei) ≠ 0 → s.mem (inOffReady + ei) = mem (inOffReady + ei)) ∧
    (∀ ei < intCap, mem (inOffReady + ei) = 1 → s.mem (inOffReady + ei) = 1) ∧
    (∀ j < i, ∀ hj : j < U_int.length, ∀ ei u v, U_int[j] = .insert ei u v →
      mem (slots + ei) = 0 → 0 ≤ det ei → s.mem (inOffReady + ei) = 1) ∧
    ∀ a, (a < offReadyList ∨ offReadyList + intCap ≤ a) →
      (a < inOffReady ∨ inOffReady + intCap ≤ a) → s.mem a = mem a
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 11) (lo := .const 0) (hi := .reg 9)
    (P := fun s => s = s9) (Inv := Inv) 90 0 U_int.length (Nat.zero_le _) hw1 (fun _ => hULenW)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], offReadyCount, le_rfl, by simp,
        by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState], by simp [s9, s8, s7, s6, s5, s4, s3, s2],
        by simp [s9, s8, s7, s6, s5, s4, s3], by simp [s9, s8, s7, s6, s5, s4], by simp [s9, s8, s7, s6, s5],
        by simp [s9, s8, s7, s6], by simp [s9, s8, s7], by simp [s9, s8], by simp [s9, edgeRecOff], by simp,
        hOffInv, fun _ _ _ => rfl, fun _ _ h => h, fun j hj _ => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl⟩)
    (fun _ _ _ _ h => by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h11, _⟩ := h; exact h11)
    (fun _ _ _ _ h => by obtain ⟨_, _, _, _, _, _, _, _, _, _, h9, _⟩ := h; simp [Expr.eval, h9])
    (fun i _ hi s ω' hI => by
      obtain ⟨cnt, hCLo, hCHi, h0, h3, h4, h5, h6, h7, h8, h9, h10, h11, hOffS, hKeepT, hKeep1, hDoneS, hFrS⟩ := hI
      have huE := hEdgeOnly U_int[i] (List.getElem_mem hi)
      have hRec0 := edgeBatch_rec_word hBatch hi (j := 0) (by
        cases h : U_int[i] with
        | insert _ _ _ => simp [updateWords]
        | delete _ => simp [updateWords]
        | split _ _ _ _ => rw [h] at huE; exact huE.elim)
      have hTagMem : s.mem (uIntBuf + 1 + edgeRecOff U_int i) = (updateWords U_int[i])[0]'(by
          cases h : U_int[i] with
          | insert _ _ _ => simp [updateWords]
          | delete _ => simp [updateWords]
          | split _ _ _ _ => rw [h] at huE; exact huE.elim) := by
        have hlt := hRec0.2
        rw [hFrS _ (by rcases hDisjB1 with h | h <;> omega) (by rcases hDisjB2 with h | h <;> omega)]
        simpa using hRec0.1
      let pushBody2 : Stmt :=
        .store (.bin .add (.reg 7) (.reg 6)) (.reg 13) ;;
        .store (.bin .add (.reg 8) (.reg 13)) (.const 1) ;;
        .assign 6 (.bin .add (.reg 6) (.const 1))
      let pushInner : Stmt :=
        .assign 14 (.load (.bin .add (.reg 5) (.reg 13))) ;;
        .call 15 isNeg [.bin .add (.bin .add (.reg 14) (.const 2)) (.bin .mul (.const 3) (.reg 3)), .reg 3] ;;
        .cond (.bin .eq (.reg 15) (.const 0)) pushBody2 .nop
      let checkStmt : Stmt :=
        .cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 13))) (.const 0))
          (.cond (.bin .eq (.load (.bin .add (.reg 8) (.reg 13))) (.const 0)) pushInner .nop)
          .nop
      let insThen : Stmt :=
        .assign 13 (.load (.bin .add (.reg 10) (.const 1))) ;;
        .assign 10 (.bin .add (.reg 10) (.const 4)) ;;
        checkStmt
      cases hUi : U_int[i] with
      | split _ _ _ _ => rw [hUi] at huE; exact huE.elim
      | delete ei =>
        have hTagVal : s.mem (uIntBuf + 1 + edgeRecOff U_int i) = 1 := by rw [hTagMem]; simp [hUi, updateWords]
        have hOffNext : edgeRecOff U_int (i + 1) = edgeRecOff U_int i + 2 := by rw [edgeRecOff_succ hi, hUi]; simp [updateWords]
        have hNextW : uIntBuf + 1 + edgeRecOff U_int i + 2 < 2 ^ w := by
          have := (edgeBatch_rec_word hBatch hi (j := 1) (by simp [hUi, updateWords])).2; omega
        let t1 := { s with regs := Function.update s.regs 12 1 }
        let t2 := { t1 with regs := Function.update t1.regs 10 (uIntBuf + 1 + edgeRecOff U_int (i + 1)) }
        have rt1 : Runs w p ω' (.assign 12 (.load (.reg 10))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h10, hTagVal], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 10 (.bin .add (.reg 10) (.const 2))) t1 .normal t2 4 :=
          runs_assign_iff.mpr ⟨uIntBuf + 1 + edgeRecOff U_int (i + 1), by
            simp only [Expr.eval, BinOp.eval, t1, h10, hw2, hNextW, ↓reduceIte, Option.some.injEq,
              Function.update_of_ne (by decide : (10 : ℕ) ≠ 12)]; omega, rfl, rfl, rfl⟩
        have rCond : Runs w p ω' (.cond (.bin .eq (.reg 12) (.const 0)) insThen (.assign 10 (.bin .add (.reg 10) (.const 2))))
            t1 .normal t2 8 :=
          runs_cond_iff.mpr ⟨0, 4, by simp [Expr.eval, BinOp.eval, t1, show 0 < 2 ^ w by omega],
            by simpa using rt2, by simp [Expr.size]⟩
        refine ⟨.normal, t2, 3 + 8 + 1, runs_seq_iff.mpr (Or.inr ⟨t1, 3, 8, rt1, rCond, rfl⟩),
          ⟨⟨cnt, hCLo, by omega, by simp [t2, t1, h0], by simp [t2, t1, h3], by simp [t2, t1, h4],
            by simp [t2, t1, h5], by simp [t2, t1, h6], by simp [t2, t1, h7], by simp [t2, t1, h8],
            by simp [t2, t1, h9], by simp [t2], by simp, hOffS, hKeepT, hKeep1,
            fun j hj hjLt e' u' v' hUj => by
              by_cases hji : j = i
              · subst hji; rw [hUi] at hUj; cases hUj
              · exact hDoneS j (by omega) hjLt e' u' v' hUj, hFrS⟩,
          by simp [t2, t1, h11]⟩, by dsimp only; omega⟩
      | insert ei u v =>
        obtain ⟨heiCap, hDetInfo⟩ := hInsInfo (.insert ei u v) (hUi ▸ List.getElem_mem hi)
        have hTagVal : s.mem (uIntBuf + 1 + edgeRecOff U_int i) = 0 := by rw [hTagMem]; simp [hUi, updateWords]
        have hOffNext : edgeRecOff U_int (i + 1) = edgeRecOff U_int i + 4 := by rw [edgeRecOff_succ hi, hUi]; simp [updateWords]
        have hRec1 := edgeBatch_rec_word hBatch hi (j := 1) (by simp [hUi, updateWords])
        have hEiMem : s.mem (uIntBuf + 1 + edgeRecOff U_int i + 1) = ei := by
          rw [hFrS _ (by have := hRec1.2; rcases hDisjB1 with h | h <;> omega)
            (by have := hRec1.2; rcases hDisjB2 with h | h <;> omega)]
          simpa [hUi, updateWords, Nat.add_assoc] using hRec1.1
        have hNextW : uIntBuf + 1 + edgeRecOff U_int i + 4 < 2 ^ w := by
          have := (edgeBatch_rec_word hBatch hi (j := 3) (by simp [hUi, updateWords])).2; omega
        let t1 := { s with regs := Function.update s.regs 12 0 }
        let t2 := { t1 with regs := Function.update t1.regs 13 ei }
        let t3 := { t2 with regs := Function.update t2.regs 10 (uIntBuf + 1 + edgeRecOff U_int (i + 1)) }
        have rt1 : Runs w p ω' (.assign 12 (.load (.reg 10))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h10, hTagVal], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 13 (.load (.bin .add (.reg 10) (.const 1)))) t1 .normal t2 5 :=
          runs_assign_iff.mpr ⟨ei, by simp [Expr.eval, BinOp.eval, t1, h10, hw1,
            show uIntBuf + 1 + edgeRecOff U_int i + 1 < 2 ^ w by have := hRec1.2; omega, hEiMem], rfl, rfl, rfl⟩
        have rt3 : Runs w p ω' (.assign 10 (.bin .add (.reg 10) (.const 4))) t2 .normal t3 4 :=
          runs_assign_iff.mpr ⟨uIntBuf + 1 + edgeRecOff U_int (i + 1), by
            simp only [Expr.eval, BinOp.eval, t2, t1, h10, hw4, hNextW, ↓reduceIte, Option.some.injEq,
              Function.update_of_ne (by decide : (10 : ℕ) ≠ 13),
              Function.update_of_ne (by decide : (10 : ℕ) ≠ 12)]; omega, rfl, rfl, rfl⟩
        have hSlotEq : s.mem (slots + ei) = mem (slots + ei) :=
          hFrS _ (by rcases hDisj4 with h | h <;> omega) (by rcases hDisj5 with h | h <;> omega)
        have hCheckStep : ∃ tEnd cCheck newCnt,
            Runs w p ω' checkStmt t3 .normal tEnd cCheck ∧
            cCheck ≤ 68 ∧ cnt ≤ newCnt ∧ newCnt ≤ cnt + 1 ∧
            tEnd.regs 6 = newCnt ∧ (∀ r, r ≠ 6 → r ≠ 14 → r ≠ 15 → tEnd.regs r = t3.regs r) ∧
            OffReadyInv tEnd.mem newCnt offReadyList inOffReady intCap ∧
            (∀ x < intCap, mem (slots + x) ≠ 0 → tEnd.mem (inOffReady + x) = mem (inOffReady + x)) ∧
            (∀ x < intCap, s.mem (inOffReady + x) = 1 → tEnd.mem (inOffReady + x) = 1) ∧
            (mem (slots + ei) = 0 → 0 ≤ det ei → tEnd.mem (inOffReady + ei) = 1) ∧
            ∀ a, (a < offReadyList ∨ offReadyList + intCap ≤ a) →
              (a < inOffReady ∨ inOffReady + intCap ≤ a) → tEnd.mem a = mem a := by
          by_cases hSlot0 : mem (slots + ei) = 0
          · rcases hOffS.2.2.2.1 ei heiCap with hBit0 | hBit1
            · let recPtr := mem (edgeRecords + ei)
              have hRecEq : s.mem (edgeRecords + ei) = recPtr :=
                hFrS _ (by rcases hDisj2 with h | h <;> omega) (by rcases hDisj3 with h | h <;> omega)
              let t4 := { t3 with regs := Function.update t3.regs 14 recPtr }
              have rt4 : Runs w p ω' (.assign 14 (.load (.bin .add (.reg 5) (.reg 13)))) t3 .normal t4 5 :=
                runs_assign_iff.mpr ⟨recPtr, by simp [Expr.eval, BinOp.eval, t3, t2, t1, h5,
                  show edgeRecords + ei < 2 ^ w by omega, hRecEq], rfl, rfl, rfl⟩
              obtain ⟨hDetE, hRecW, hDetDisj⟩ := hDetInfo hSlot0
              have hDetT4 : PathIntAt t4.mem (recPtr + 2 + 3 * L) 4 L (det ei) :=
                hDetE.congr (fun t ht => hFrS _ (hDetDisj t ht).2 (hDetDisj t ht).1)
              obtain ⟨t5, cN, negBit, rt5, hpN, hr5_15, ht5Regs, hcN⟩ :=
                runs_call_of_meetsContract (r := 15)
                  (args := [.bin .add (.bin .add (.reg 14) (.const 2)) (.bin .mul (.const 3) (.reg 3)), .reg 3])
                  hisNeg (st := t4) (vs := [recPtr + 2 + 3 * L, L])
                  (by simp [evalArgs, Expr.eval, BinOp.eval, t4, t3, t2, t1, h3, hw2, hw3, h3LW,
                    show recPtr + 2 < 2 ^ w by omega, show recPtr + 2 + 3 * L < 2 ^ w by omega])
                  (by simp [show recPtr + 2 + 3 * L < 2 ^ w by omega, show L < 2 ^ w by omega])
                  ⟨recPtr + 2 + 3 * L, L, rfl, by omega, hDetT4.1⟩ ω'
              obtain ⟨ht5Mem, hNegEq⟩ := hpN
              have hNegVal : negBit = if det ei < 0 then 1 else 0 := by simpa [hDetT4.2] using hNegEq
              have hcNLe : cN ≤ 24 := by simp only [Num.isNegativeContract, argsSize, Expr.size] at hcN; omega
              by_cases hlt : det ei < 0
              · have hnb : negBit = 1 := by simp [hNegVal, hlt]
                have rP : Runs w p ω' (.cond (.bin .eq (.reg 15) (.const 0)) pushBody2 .nop) t5 .normal t5 5 :=
                  runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, hr5_15, hnb, show 0 < 2 ^ w by omega],
                    by simp [runs_nop_iff], by simp [Expr.size]⟩
                have rC2 : Runs w p ω' (.cond (.bin .eq (.load (.bin .add (.reg 8) (.reg 13))) (.const 0)) pushInner .nop)
                    t3 .normal t5 (6 + (5 + (cN + 5 + 1) + 1) + 1) :=
                  runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, t3, t2, t1, h8,
                    show inOffReady + ei < 2 ^ w by omega, hBit0, show 0 < 2 ^ w by omega, hw1],
                    by simpa [pushInner] using runs_seq_iff.mpr (Or.inr ⟨t4, 5, _, rt4,
                      runs_seq_iff.mpr (Or.inr ⟨t5, cN, 5, rt5, rP, rfl⟩), rfl⟩), by simp [Expr.size]⟩
                have rC1 : Runs w p ω' checkStmt t3 .normal t5 (6 + (6 + (5 + (cN + 5 + 1) + 1) + 1) + 1) :=
                  runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, t3, t2, t1, h4,
                    show slots + ei < 2 ^ w by omega, hSlotEq, hSlot0, show 0 < 2 ^ w by omega, hw1],
                    by simpa using rC2, by simp [Expr.size]⟩
                refine ⟨t5, _, cnt, rC1, by omega, le_rfl, Nat.le_succ _,
                  by rw [ht5Regs 6 (by decide)]; simp [t4, t3, t2, t1, h6],
                  fun r _ h14 h15 => by rw [ht5Regs r h15]; simp [t4, Function.update_of_ne h14],
                  ht5Mem.symm ▸ hOffS, fun x hx hnz => by rw [ht5Mem]; exact hKeepT x hx hnz,
                  fun x _ h1 => by rw [ht5Mem]; exact h1, fun _ h0 => by omega,
                  fun a ha1 ha2 => by rw [ht5Mem]; exact hFrS a ha1 ha2⟩
              · have hnb : negBit = 0 := by simp [hNegVal, hlt]
                obtain ⟨hCntLt, hOffNew⟩ := wireCore_offReadyInv_push (ht5Mem.symm ▸ hOffS) heiCap (ht5Mem.symm ▸ hBit0) hDisj1
                let t6 := { t5 with mem := Function.update t5.mem (offReadyList + cnt) ei }
                let t7 := { t6 with mem := Function.update t6.mem (inOffReady + ei) 1 }
                let t8 := { t7 with regs := Function.update t7.regs 6 (cnt + 1) }
                have rt6 : Runs w p ω' (.store (.bin .add (.reg 7) (.reg 6)) (.reg 13)) t5 .normal t6 5 :=
                  runs_store_iff.mpr ⟨offReadyList + cnt, ei, by
                    simp [Expr.eval, BinOp.eval, ht5Regs 7 (by decide), ht5Regs 6 (by decide), t4, t3, t2, t1,
                      h7, h6, show offReadyList + cnt < 2 ^ w by omega],
                    by simp [Expr.eval, ht5Regs 13 (by decide), t4, t3, t2], rfl, rfl, rfl⟩
                have rt7 : Runs w p ω' (.store (.bin .add (.reg 8) (.reg 13)) (.const 1)) t6 .normal t7 5 :=
                  runs_store_iff.mpr ⟨inOffReady + ei, 1, by
                    simp [Expr.eval, BinOp.eval, t6, ht5Regs 8 (by decide), ht5Regs 13 (by decide), t4, t3, t2, t1,
                      h8, show inOffReady + ei < 2 ^ w by omega],
                    by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
                have rt8 : Runs w p ω' (.assign 6 (.bin .add (.reg 6) (.const 1))) t7 .normal t8 4 :=
                  runs_assign_iff.mpr ⟨cnt + 1, by
                    simp [Expr.eval, BinOp.eval, t7, t6, ht5Regs 6 (by decide), t4, t3, t2, t1, h6, hw1,
                      show cnt + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
                have rP : Runs w p ω' (.cond (.bin .eq (.reg 15) (.const 0)) pushBody2 .nop) t5 .normal t8 20 :=
                  runs_cond_iff.mpr ⟨1, 16, by simp [Expr.eval, BinOp.eval, hr5_15, hnb, show 0 < 2 ^ w by omega, hw1],
                    by simpa [pushBody2] using runs_seq_iff.mpr (Or.inr ⟨t6, 5, _, rt6, runs_seq_iff.mpr (Or.inr ⟨t7, 5, 4, rt7, rt8, rfl⟩), rfl⟩),
                    by simp [Expr.size]⟩
                have rC2 : Runs w p ω' (.cond (.bin .eq (.load (.bin .add (.reg 8) (.reg 13))) (.const 0)) pushInner .nop)
                    t3 .normal t8 (6 + (5 + (cN + 20 + 1) + 1) + 1) :=
                  runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, t3, t2, t1, h8,
                    show inOffReady + ei < 2 ^ w by omega, hBit0, show 0 < 2 ^ w by omega, hw1],
                    by simpa [pushInner] using runs_seq_iff.mpr (Or.inr ⟨t4, 5, _, rt4,
                      runs_seq_iff.mpr (Or.inr ⟨t5, cN, 20, rt5, rP, rfl⟩), rfl⟩), by simp [Expr.size]⟩
                have rC1 : Runs w p ω' checkStmt t3 .normal t8 (6 + (6 + (5 + (cN + 20 + 1) + 1) + 1) + 1) :=
                  runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, t3, t2, t1, h4,
                    show slots + ei < 2 ^ w by omega, hSlotEq, hSlot0, show 0 < 2 ^ w by omega, hw1],
                    by simpa using rC2, by simp [Expr.size]⟩
                refine ⟨t8, _, cnt + 1, rC1, by omega, Nat.le_succ _, le_rfl, by simp [t8],
                  fun r h6' h14 h15 => by simp only [t8, t7, t6, Function.update_of_ne h6']; rw [ht5Regs r h15]; simp [t4, Function.update_of_ne h14],
                  hOffNew,
                  fun x hx hnz => by
                    have hne : x ≠ ei := fun h => hnz (h ▸ hSlot0)
                    simp only [t8, t7, t6, Function.update_of_ne (by omega : inOffReady + x ≠ inOffReady + ei),
                      Function.update_of_ne (by rcases hDisj1 with h | h <;> omega : inOffReady + x ≠ offReadyList + cnt), ht5Mem]
                    exact hKeepT x hx hnz,
                  fun x hx h1 => by
                    by_cases hxe : x = ei
                    · subst hxe; simp [t8, t7]
                    · simp only [t8, t7, t6, Function.update_of_ne (by omega : inOffReady + x ≠ inOffReady + ei),
                        Function.update_of_ne (by rcases hDisj1 with h | h <;> omega : inOffReady + x ≠ offReadyList + cnt), ht5Mem]
                      exact h1,
                  fun _ _ => by simp [t8, t7],
                  fun a ha1 ha2 => by
                    simp only [t8, t7, t6, Function.update_of_ne (by rcases ha2 with h | h <;> omega : a ≠ inOffReady + ei),
                      Function.update_of_ne (by rcases ha1 with h | h <;> omega : a ≠ offReadyList + cnt), ht5Mem]
                    exact hFrS a ha1 ha2⟩
            · have rC2 : Runs w p ω' (.cond (.bin .eq (.load (.bin .add (.reg 8) (.reg 13))) (.const 0)) pushInner .nop)
                  t3 .normal t3 8 :=
                runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, t3, t2, t1, h8,
                  show inOffReady + ei < 2 ^ w by omega, hBit1, show 0 < 2 ^ w by omega],
                  by simp [runs_nop_iff], by simp [Expr.size]⟩
              have rC1 : Runs w p ω' checkStmt t3 .normal t3 15 :=
                runs_cond_iff.mpr ⟨1, 8, by simp [Expr.eval, BinOp.eval, t3, t2, t1, h4,
                  show slots + ei < 2 ^ w by omega, hSlotEq, hSlot0, show 0 < 2 ^ w by omega, hw1],
                  by simpa using rC2, by simp [Expr.size]⟩
              refine ⟨t3, 15, cnt, rC1, by omega, le_rfl, Nat.le_succ _, by simp [t3, t2, t1, h6],
                fun _ _ _ _ => rfl, hOffS, hKeepT, fun _ _ h => h, fun _ _ => hBit1, hFrS⟩
          · have rC1 : Runs w p ω' checkStmt t3 .normal t3 8 :=
              runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, t3, t2, t1, h4,
                show slots + ei < 2 ^ w by omega, hSlotEq, hSlot0, show 0 < 2 ^ w by omega],
                by simp [runs_nop_iff], by simp [Expr.size]⟩
            refine ⟨t3, 8, cnt, rC1, by omega, le_rfl, Nat.le_succ _, by simp [t3, t2, t1, h6],
              fun _ _ _ _ => rfl, hOffS, hKeepT, fun _ _ h => h, fun h => absurd h hSlot0, hFrS⟩
        obtain ⟨tEnd, cCheck, newCnt, rCheck, hcCheck, hNC1, hNC2, hEnd6, hEndRegs, hOffEnd,
          hKeepTEnd, hKeep1End, hDetEnd, hFrEnd⟩ := hCheckStep
        have rThen : Runs w p ω' insThen t1 .normal tEnd (5 + (4 + cCheck + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, rt2, runs_seq_iff.mpr (Or.inr ⟨t3, 4, cCheck, rt3, rCheck, rfl⟩), rfl⟩)
        have rCond : Runs w p ω' (.cond (.bin .eq (.reg 12) (.const 0)) insThen (.assign 10 (.bin .add (.reg 10) (.const 2))))
            t1 .normal tEnd (3 + (5 + (4 + cCheck + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, t1, hw1], by simpa using rThen, by simp [Expr.size]⟩
        refine ⟨.normal, tEnd, _, runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rCond, rfl⟩),
          ⟨⟨newCnt, by omega, by omega,
            by simp only [Function.update_of_ne (by decide : (0 : ℕ) ≠ 11)]; rw [hEndRegs 0 (by decide) (by decide) (by decide)]; simp [t3, t2, t1, h0],
            by simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 11)]; rw [hEndRegs 3 (by decide) (by decide) (by decide)]; simp [t3, t2, t1, h3],
            by simp only [Function.update_of_ne (by decide : (4 : ℕ) ≠ 11)]; rw [hEndRegs 4 (by decide) (by decide) (by decide)]; simp [t3, t2, t1, h4],
            by simp only [Function.update_of_ne (by decide : (5 : ℕ) ≠ 11)]; rw [hEndRegs 5 (by decide) (by decide) (by decide)]; simp [t3, t2, t1, h5],
            by simp only [Function.update_of_ne (by decide : (6 : ℕ) ≠ 11)]; exact hEnd6,
            by simp only [Function.update_of_ne (by decide : (7 : ℕ) ≠ 11)]; rw [hEndRegs 7 (by decide) (by decide) (by decide)]; simp [t3, t2, t1, h7],
            by simp only [Function.update_of_ne (by decide : (8 : ℕ) ≠ 11)]; rw [hEndRegs 8 (by decide) (by decide) (by decide)]; simp [t3, t2, t1, h8],
            by simp only [Function.update_of_ne (by decide : (9 : ℕ) ≠ 11)]; rw [hEndRegs 9 (by decide) (by decide) (by decide)]; simp [t3, t2, t1, h9],
            by simp only [Function.update_of_ne (by decide : (10 : ℕ) ≠ 11)]; rw [hEndRegs 10 (by decide) (by decide) (by decide)]; simp [t3],
            by simp, hOffEnd, hKeepTEnd, fun x hx h1 => hKeep1End x hx (hKeep1 x hx h1),
            fun j hj hjLt e' u' v' hUj hS0 hD0 => by
              by_cases hji : j = i
              · subst hji; rw [hUi] at hUj; injection hUj with heq _ _; subst heq; exact hDetEnd hS0 hD0
              · exact hKeep1End e' (hInsInfo (.insert e' u' v') (hUj ▸ List.getElem_mem hjLt)).1
                  (hDoneS j (by omega) hjLt e' u' v' hUj hS0 hD0),
            hFrEnd⟩,
          by rw [hEndRegs 11 (by decide) (by decide) (by decide)]; simp [t3, t2, t1, h11]⟩, by dsimp only; omega⟩)
  obtain ⟨o, s10, cL, rL, hL, hcL⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hL
  | normal =>
    obtain ⟨newCnt, hCLo, hCHi, h10_0, _, _, _, h10_6, _, _, _, _, _, hOff10, hKeepT10, hKeep1_10, hDone10, hFr10⟩ := hL
    let out := { s10 with mem := Function.update s10.mem (root + 11) newCnt }
    have rStore : Runs w p ω (.store (.bin .add (.reg 0) (.const 11)) (.reg 6)) s10 .normal out 5 :=
      runs_store_iff.mpr ⟨root + 11, newCnt, by simp [Expr.eval, BinOp.eval, h10_0, show 11 < 2 ^ w by omega,
        show root + 11 < 2 ^ w by omega], by simp [Expr.eval, h10_6], rfl, rfl, rfl⟩
    have rRet : Runs w p ω (.ret (.reg 6)) out (.returned newCnt) out 2 :=
      runs_ret_iff.mpr ⟨newCnt, by simp [Expr.eval, out, h10_6], rfl, rfl, rfl⟩
    have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, r5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 5, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨s7, 5, _, r7,
      runs_seq_iff.mpr (Or.inr ⟨s8, 3, _, r8,
      runs_seq_iff.mpr (Or.inr ⟨s9, 4, _, r9,
      runs_seq_iff.mpr (Or.inr ⟨s10, cL, _, rL,
      runs_seq_iff.mpr (Or.inr ⟨out, 5, 2, rStore, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have hOutNe (a : ℕ) (hne : a ≠ root + 11) : out.mem a = s10.mem a := Function.update_of_ne hne _ _
    simp only [Expr.size] at hcL
    refine ⟨newCnt, out, _, rAll, by omega, hCLo, hCHi, by simp [out], ?_,
      fun ei hei hnz => (hOutNe _ (by rcases hDisjR2 with h | h <;> omega)).trans (hKeepT10 ei hei hnz),
      fun ei hei h1 => (hOutNe _ (by rcases hDisjR2 with h | h <;> omega)).trans (hKeep1_10 ei hei h1),
      fun ei u v hMem hS0 hD0 => by
        obtain ⟨j, hjLt, hUj⟩ := List.getElem_of_mem hMem
        have heiCap := (hInsInfo (.insert ei u v) hMem).1
        exact (hOutNe _ (by rcases hDisjR2 with h | h <;> omega)).trans (hDone10 j hjLt hjLt ei u v hUj hS0 hD0),
      fun a h1 h2 h3 => (hOutNe a h1).trans (hFr10 a h2 h3)⟩
    obtain ⟨hcnt, hmemL, hdist, hbits, hrev⟩ := hOff10
    refine ⟨hcnt, fun j hj => by
        rw [hOutNe _ (by rcases hDisjR1 with h | h <;> omega),
            hOutNe _ (by have := (hmemL j hj).1; rcases hDisjR2 with h | h <;> omega)]
        exact hmemL j hj,
      fun j₁ hj₁ j₂ hj₂ hne => by
        rw [hOutNe _ (by rcases hDisjR1 with h | h <;> omega),
            hOutNe _ (by rcases hDisjR1 with h | h <;> omega)]
        exact hdist j₁ hj₁ j₂ hj₂ hne,
      fun e he => by rw [hOutNe _ (by rcases hDisjR2 with h | h <;> omega)]; exact hbits e he,
      fun e he h1 => by
        rw [hOutNe _ (by rcases hDisjR2 with h | h <;> omega)] at h1
        obtain ⟨j, hj, hje⟩ := hrev e he h1
        exact ⟨j, hj, (hOutNe _ (by rcases hDisjR1 with h | h <;> omega)).trans hje⟩⟩

end MinCostFlow.MinRatio
