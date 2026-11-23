module

public import MinCostFlow.MinRatio.DetectOffTreeDrainBase
import WordRAM.Tactic

/-!
# Off-tree pending list drain execution for `Detect`

Proves `detectOffTreeDrainStep_triple` and `detectOffTreeDrainBody_runs`, showing that
`detectOffTreeDrainBody` scans `offReadyList[0 .. tok.offReadyCount)`, emits every live
off-tree ready edge without duplicates, resets its detector via `detectResetContract` in
a freshly allocated `PathEdgeAt` block, clears `inOffReady[0 .. intCap)` and `offReadyCount`,
and costs at most `tok.offReadyCount * detectOffTreeDrainUnit L + 70` (absorbed by the
potential drop `tok.offReadyCount * drainUnit` in `solverStateRep.phi`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- One-step execution of `detectOffTreeDrainStep` inside `forRange 14`:
maintains `DrainInv` and costs at most `detectOffTreeStepBudget L`. -/
theorem detectOffTreeDrainStep_triple {w L P m V psi k epsExp drainUnit isNeg reset : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {p : Program}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {mem₀ : ℕ → ℕ}
    {root base heap₀ : ℕ} {treeRep : List ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem₀)
    (hbelow : ∀ a, tok.tag a ≠ 0 → tok.tag a ≠ 16 → a < base)
    (hExtRange : ∀ e < m, e ∈ model.extG.E)
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hfitThr : ∀ e ∈ model.extG.E, Num.Fits 4 L (-detectorThreshold P cfg.ε (model.extℓ e)))
    (hIsNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hReset : ∀ edge th, MeetsContract w p reset (detectResetContract w 4 edge th))
    (hbaseHeap : base + 1 + m ≤ heap₀)
    (hTreeSub : ∀ e ∈ treeRep, e ∈ model.extG.E ∧ model.extToInt e ∈ model.chain.toTreeChain.chainTree.E)
    (hroom : heap₀ + tok.offReadyCount * (2 + 4 * L) < 2 ^ w)
    (hw13 : 13 < 2 ^ w) (hLpos : 0 < L)
    {j : ℕ} (hj : j < tok.offReadyCount) :
    Triple w p (DrainInv (P := P) (m := m) model tok mem₀ root base heap₀ treeRep j)
      (detectOffTreeDrainStep isNeg reset)
      (normalPost fun s' =>
        DrainInv (P := P) (m := m) model tok mem₀ root base heap₀ treeRep (j + 1)
          { s' with regs := Function.update s'.regs 14 (j + 1) } ∧ s'.regs 14 = j)
      (fun _ => detectOffTreeStepBudget L) := by
  intro s ω hInv
  have hInv0 := hInv
  obtain ⟨offRep, curHeap, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13,
    hr14, hoffLen, htotLen, hnd, hlist, hcurLo, hcurHi, hzCur, hclr, hkeep1, hzero0,
    hoffIff, hrecInv, hframe0, hsepR⟩ := hInv
  have hrep0 := hrep
  obtain ⟨_, _, _, _, hfreshInv, hfreshTab, hextLt, _, _, hoffInv, _, _, _, hedgeAcc, _, _, _, _, hwire, htags⟩ := hrep
  obtain ⟨_, _, _, _, _, _, _, t7, t8, t9, _, _, t12, t13, t14, t15, _, t1718, _, _, _⟩ := htags
  have hltB {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) (hv16 : v ≠ 16 := by decide) : a < base :=
    hbelow a (ht ▸ hv) (ht ▸ hv16)
  have hbaseW : base < 2 ^ w := by omega
  have hheap0W : heap₀ < 2 ^ w := by omega
  have hcurW : curHeap < 2 ^ w := by
    have : j * (2 + 4 * L) ≤ tok.offReadyCount * (2 + 4 * L) := Nat.mul_le_mul_right _ hj.le
    omega
  have hcurStepW : curHeap + (2 + 4 * L) < 2 ^ w := by
    have hmul : (j + 1) * (2 + 4 * L) ≤ tok.offReadyCount * (2 + 4 * L) :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at hmul; omega
  have hLW : L < 2 ^ w := by omega
  have hmW : m < 2 ^ w := by omega
  have hmemT {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) (hv13 : v ≠ 13) (hv15 : v ≠ 15)
      (hv16 : v ≠ 16 := by decide) :
      s.mem a = mem₀ a := by
    have haB : a < base := hltB ht hv hv16
    refine hframe0 a (by omega) (Or.inl (by omega)) ?_ ?_
    · by_contra hnot; push Not at hnot
      have h15 : tok.tag a = 15 := by
        have h1 := t15 (a - tok.inOffReady) (by omega)
        rwa [Nat.add_sub_of_le hnot.1] at h1
      exact hv15 (ht.symm.trans h15)
    · by_contra hnot; push Not at hnot
      have h13 : tok.tag a = 13 := by
        have h1 := t13 (a - tok.edgeRecords) (by omega)
        rwa [Nat.add_sub_of_le hnot.1] at h1
      exact hv13 (ht.symm.trans h13)
  have hjCap : j < tok.intCap := lt_of_lt_of_le hj hoffInv.1
  let ei := mem₀ (tok.offReadyList + j)
  have heiCap : ei < tok.intCap := (hoffInv.2.1 j hj).1
  have hListAddrW : tok.offReadyList + j < 2 ^ w := lt_trans (hltB (t14 j hjCap) (by decide)) hbaseW
  have hListEq : s.mem (tok.offReadyList + j) = ei := hmemT (t14 j hjCap) (by decide) (by decide) (by decide)
  have hInOffW : tok.inOffReady + ei < 2 ^ w := lt_trans (hltB (t15 ei heiCap) (by decide)) hbaseW
  have hInvW : tok.inverse + ei < 2 ^ w := lt_trans (hltB (t8 ei heiCap) (by decide)) hbaseW
  let e := mem₀ (tok.inverse + ei)
  have hInvEq : s.mem (tok.inverse + ei) = e := hmemT (t8 ei heiCap) (by decide) (by decide) (by decide)
  have hInvNeInOff : tok.inverse + ei ≠ tok.inOffReady + ei := fun h => by
    have h1 := t8 ei heiCap; have h2 := t15 ei heiCap; rw [h] at h1; omega
  let s1 := { s with regs := Function.update s.regs 15 ei }
  let s2 := { s1 with mem := Function.update s1.mem (tok.inOffReady + ei) 0 }
  let s3 := { s2 with regs := Function.update s2.regs 16 e }
  have r1 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 12) (.reg 14)))) s .normal s1 5 :=
    runs_assign_iff.mpr ⟨ei, by simp [Expr.eval, BinOp.eval, hr12, hr14, hListAddrW, hListEq, ei], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.store (.bin .add (.reg 13) (.reg 15)) (.const 0)) s1 .normal s2 5 :=
    runs_store_iff.mpr ⟨tok.inOffReady + ei, 0, by simp [Expr.eval, BinOp.eval, s1, hr13, hInOffW],
      by simp [Expr.eval], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 7) (.reg 15)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨e, by
      simp [Expr.eval, BinOp.eval, s2, s1, hr7, hInvW, Function.update_of_ne hInvNeInOff, hInvEq, e],
      rfl, rfl, rfl⟩
  have hSkipClose {st : State} (hmemSt : st.mem = s3.mem) (hregsSt : ∀ r ≤ 14, st.regs r = s3.regs r)
      (hnotReady : ¬ IsOffTreeReady model ei) :
      DrainInv (P := P) (m := m) model tok mem₀ root base heap₀ treeRep (j + 1)
        { st with regs := Function.update st.regs 14 (j + 1) } ∧ st.regs 14 = j :=
    drainStep_skip_inv hrep0 hbelow hbaseHeap hj hInv0 hmemSt (fun r hr => by
      rw [hregsSt r hr]; simp [s3, s2, s1,
        Function.update_of_ne (show r ≠ 16 by omega),
        Function.update_of_ne (show r ≠ 15 by omega)]) hnotReady
  have hs3_r2 : s3.regs 2 = m := by simp [s3, s2, s1, hr2]
  have hs3_r6 : s3.regs 6 = tok.forward := by simp [s3, s2, s1, hr6]
  have hs3_r8 : s3.regs 8 = tok.slots := by simp [s3, s2, s1, hr8]
  have hs3_r10 : s3.regs 10 = tok.edgeRecords := by simp [s3, s2, s1, hr10]
  have hs3_r15 : s3.regs 15 = ei := by simp [s3, s2, s1]
  have hs3_r16 : s3.regs 16 = e := rfl
  let emitBody : Stmt :=
    .store (.reg 3) (.reg 16) ;;
    .assign 3 (.bin .add (.reg 3) (.const 1)) ;;
    .assign 20 (.load (.bin .add (.reg 9) (.reg 15))) ;;
    .call 21 reset [.reg 17, .reg 20, .reg 5, .reg 4] ;;
    .store (.bin .add (.reg 10) (.reg 15)) (.reg 4) ;;
    .assign 4 (.reg 21)
  let cond4 : Stmt := .cond (.reg 19) .nop emitBody
  let innerBody : Stmt :=
    .assign 17 (.load (.bin .add (.reg 10) (.reg 15))) ;;
    .assign 18 (.bin .add (.bin .add (.reg 17) (.const 2))
      (.bin .mul (.const 3) (.reg 5))) ;;
    .call 19 isNeg [.reg 18, .reg 5] ;;
    cond4
  let cond3 : Stmt := .cond (.load (.bin .add (.reg 8) (.reg 15))) .nop innerBody
  let cond2 : Stmt := .cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 16))) (.reg 15)) cond3 .nop
  let cond1 : Stmt := .cond (.bin .lt (.reg 16) (.reg 2)) cond2 .nop
  have hwnz : ¬ w = 0 := fun h => by subst h; simp at hw13
  by_cases hem : e < m
  · have hfwdW : tok.forward + e < 2 ^ w := lt_trans (hltB (t7 e hem) (by decide)) hbaseW
    have hfwdNeInOff : tok.forward + e ≠ tok.inOffReady + ei := fun h => by
      have h1 := t7 e hem; have h2 := t15 ei heiCap; rw [h] at h1; omega
    have hfwdEq : s3.mem (tok.forward + e) = mem₀ (tok.forward + e) := by
      simp only [s3, s2, s1, Function.update_of_ne hfwdNeInOff]
      exact hmemT (t7 e hem) (by decide) (by decide) (by decide)
    by_cases hlive : mem₀ (tok.forward + e) = ei
    · have hlivePair : model.intToExt ei ∈ model.extG.E ∧ model.extToInt (model.intToExt ei) = ei :=
        (live_offtree_iff hfreshTab hExtRange hextLt heiCap).mp ⟨hem, hlive⟩
      have heEq : e = model.intToExt ei := hfreshTab.2.2 ei heiCap
      have heE : e ∈ model.extG.E := heEq ▸ hlivePair.1
      have he2i : model.extToInt e = ei := heEq ▸ hlivePair.2
      have hslW : tok.slots + ei < 2 ^ w := lt_trans (hltB (t9 ei heiCap) (by decide)) hbaseW
      have hslNeInOff : tok.slots + ei ≠ tok.inOffReady + ei := fun h => by
        have h1 := t9 ei heiCap; have h2 := t15 ei heiCap; rw [h] at h1; omega
      have hslEq : s3.mem (tok.slots + ei) = mem₀ (tok.slots + ei) := by
        simp only [s3, s2, s1, Function.update_of_ne hslNeInOff]
        exact hmemT (t9 ei heiCap) (by decide) (by decide) (by decide)
      by_cases hslot0 : mem₀ (tok.slots + ei) = 0
      · have hnotTree : ei ∉ model.chain.toTreeChain.chainTree.E := by
          intro hin
          have hbr := (hedgeAcc.1 e heE).2.2
          rw [he2i, ite_eq_left hin] at hbr
          exact hbr.1 hslot0
        have heNotOff : e ∉ offRep := by
          intro hin
          obtain ⟨k, hk, hR, hkEq⟩ := (hoffIff e).mp hin
          have heiEq : mem₀ (tok.offReadyList + k) = ei := by
            rw [← he2i, hkEq]; exact hR.2.1.symm
          exact hoffInv.2.2.1 k (lt_trans hk hj) j hj (by omega) heiEq
        have heNotTreeRep : e ∉ treeRep := fun hin => hnotTree (he2i ▸ (hTreeSub e hin).2)
        have hrecNot := hrecInv e heE (by rwa [he2i])
        rw [ite_eq_right heNotOff] at hrecNot
        let recPtr := mem₀ (tok.edgeRecords + ei)
        have herW : tok.edgeRecords + ei < 2 ^ w := lt_trans (hltB (t13 ei heiCap) (by decide)) hbaseW
        have herNeInOff : tok.edgeRecords + ei ≠ tok.inOffReady + ei := fun h => by
          have h1 := t13 ei heiCap; have h2 := t15 ei heiCap; rw [h] at h1; omega
        have herEq : s3.mem (tok.edgeRecords + ei) = recPtr := by
          simp only [s3, s2, s1, Function.update_of_ne herNeInOff]
          simpa [he2i, recPtr] using hrecNot.1
        have hdi := solverStateRep_detect_iff hrep0 heE heps (hlen e heE)
        dsimp only at hdi
        rw [he2i, ite_eq_right hnotTree] at hdi
        obtain ⟨val, hvalRec0, hdetIff, _⟩ := hdi
        have hvalRec3 : PathEdgeAt s3.mem recPtr 4 L (some val) := by
          refine hvalRec0.congr (fun a halo hahi => ?_)
          have haIdx : a = recPtr + (a - recPtr) := by omega
          have hidxLt : a - recPtr < 2 + 4 * L := by omega
          have hne : a ≠ tok.inOffReady + ei := fun h => by
            have h1 := (t1718 e heE).2 (by rwa [he2i]) (a - recPtr) hidxLt
            have h2 := t15 ei heiCap
            rw [he2i, ← haIdx, h] at h1; omega
          have h1 : s3.mem a = s.mem a := by simp [s3, s2, s1, Function.update_of_ne hne]
          rw [h1, haIdx]
          simpa [he2i, recPtr] using hrecNot.2 (a - recPtr) hidxLt
        have hrecEndB : recPtr + (2 + 4 * L) ≤ base := by
          have hlast : recPtr + (2 + 4 * L - 1) < base := by
            have h1 := (t1718 e heE).2 (by rwa [he2i]) (2 + 4 * L - 1) (by omega)
            rw [he2i] at h1; exact hltB h1 (by decide)
          omega
        let detPtr := recPtr + 2 + 3 * L
        have hdetPtrW : detPtr < 2 ^ w := by omega
        have hdetEndW : detPtr + L < 2 ^ w := by omega
        let s4 := { s3 with regs := Function.update s3.regs 17 recPtr }
        let s5 := { s4 with regs := Function.update s4.regs 18 detPtr }
        have r17 : Runs w p ω (.assign 17 (.load (.bin .add (.reg 10) (.reg 15)))) s3 .normal s4 5 :=
          runs_assign_iff.mpr ⟨recPtr, by simp [Expr.eval, BinOp.eval, hs3_r10, hs3_r15, herW, herEq], rfl, rfl, rfl⟩
        have r18 : Runs w p ω (.assign 18 (.bin .add (.bin .add (.reg 17) (.const 2))
            (.bin .mul (.const 3) (.reg 5)))) s4 .normal s5 8 :=
          runs_assign_iff.mpr ⟨detPtr, by
            simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, hr5,
              show 2 < 2 ^ w by omega, show 3 < 2 ^ w by omega,
              show recPtr + 2 < 2 ^ w by omega, show 3 * L < 2 ^ w by omega, detPtr, hdetPtrW],
            rfl, rfl, rfl⟩
        have hdetValid : Num.Valid s5.mem detPtr 4 L := hvalRec3.2.2.2.2.2.1
        have hdetVal : Num.intVal s5.mem detPtr 4 L = val.detector := hvalRec3.2.2.2.2.2.2
        have hNegPre : (Num.isNegativeContract w 4).pre [detPtr, L] s5.mem :=
          ⟨detPtr, L, rfl, hdetEndW, hdetValid⟩
        have hNegEval : evalArgs w s5 [.reg 18, .reg 5] = some [detPtr, L] := by
          simp [evalArgs, Expr.eval, s5, s4, s3, s2, s1, hr5]
        obtain ⟨bodyN, hbodyN, oN, stN, cN, hrN, ⟨hmemN, hnegVal⟩, hcN⟩ :=
          hIsNeg [detPtr, L] s5.mem s5.pos ω (by wram_words) hNegPre
        change stN.mem = s5.mem at hmemN
        let negBit := oN.value
        change negBit = (if Num.intVal s5.mem detPtr 4 L < 0 then 1 else 0) at hnegVal
        rw [hdetVal] at hnegVal
        change cN ≤ 13 at hcN
        let s6 : State := { mem := stN.mem, regs := Function.update s5.regs 19 negBit, pos := stN.pos }
        have r19 : Runs w p ω (.call 19 isNeg [.reg 18, .reg 5]) s5 .normal s6 (cN + 3) :=
          runs_call_iff.mpr ⟨[detPtr, L], bodyN, oN, stN, cN, hNegEval, hbodyN, hrN, rfl, rfl, by
            simp [argsSize, Expr.size]; omega⟩
        by_cases hneg : val.detector < 0
        · have hnb1 : negBit = 1 := by rw [hnegVal, ite_eq_left hneg]
          have hnotR : ¬ IsOffTreeReady model ei := fun hR => by
            have := hdetIff.mpr (heEq.symm ▸ hR.2.2.2); omega
          have rCond4 : Runs w p ω cond4 s6 .normal s6 3 :=
            runs_cond_iff.mpr ⟨1, 1, by simp [Expr.eval, s6, hnb1],
              by simp only [Nat.one_ne_zero, ite_false]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
          have rInner : Runs w p ω innerBody s3 .normal s6 (5 + (8 + ((cN + 3) + 3 + 1) + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r17,
              runs_seq_iff.mpr (Or.inr ⟨s5, 8, _, r18,
                runs_seq_iff.mpr (Or.inr ⟨s6, cN + 3, 3, r19, rCond4, rfl⟩), rfl⟩), rfl⟩)
          have rCond3 : Runs w p ω cond3 s3 .normal s6
              (4 + (5 + (8 + ((cN + 3) + 3 + 1) + 1) + 1) + 1) :=
            runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, BinOp.eval, hs3_r8, hs3_r15, hslW, hslEq, hslot0],
              by simpa using rInner, rfl⟩
          have rCond2 : Runs w p ω cond2
              s3 .normal s6 (6 + (4 + (5 + (8 + ((cN + 3) + 3 + 1) + 1) + 1) + 1) + 1) :=
            runs_cond_iff.mpr ⟨1, _, by
              simp [Expr.eval, BinOp.eval, hs3_r6, hs3_r16, hs3_r15, hfwdW, hfwdEq, hlive, hwnz],
              by simp only [Nat.one_ne_zero, ite_false]; exact rCond3, rfl⟩
          have rCond1 : Runs w p ω cond1
              s3 .normal s6 (3 + (6 + (4 + (5 + (8 + ((cN + 3) + 3 + 1) + 1) + 1) + 1) + 1) + 1) :=
            runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, hs3_r16, hs3_r2, hem, hwnz],
              by simp only [Nat.one_ne_zero, ite_false]; exact rCond2, rfl⟩
          have rFull : Runs w p ω (detectOffTreeDrainStep isNeg reset) s .normal s6 _ :=
            runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
              runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
                runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3, rCond1, rfl⟩), rfl⟩), rfl⟩)
          have hs6R : ∀ r ≤ 14, s6.regs r = s3.regs r := fun r hr => by
            simp [s6, s5, s4, Function.update_of_ne (show r ≠ 19 by omega),
              Function.update_of_ne (show r ≠ 18 by omega),
              Function.update_of_ne (show r ≠ 17 by omega)]
          exact ⟨.normal, s6, _, rFull, hSkipClose hmemN hs6R hnotR,
            by dsimp only [detectOffTreeStepBudget]; omega⟩
        · have hnn : 0 ≤ val.detector := not_lt.mp hneg
          have hnb0 : negBit = 0 := by rw [hnegVal, ite_eq_right hneg]
          have hReadyEi : IsOffTreeReady model ei :=
            ⟨hlivePair.1, hlivePair.2, hnotTree, heEq ▸ hdetIff.mp hnn⟩
          have heNotBoth : e ∉ treeRep ++ offRep := by
            rw [List.mem_append]; rintro (h | h); exact heNotTreeRep h; exact heNotOff h
          have hsubE : ∀ x ∈ treeRep ++ offRep, x ∈ model.extG.E := by
            intro x hx; rw [List.mem_append] at hx
            rcases hx with h1 | h2
            · exact (hTreeSub x h1).1
            · obtain ⟨_, _, hR, rfl⟩ := (hoffIff x).mp h2; exact hR.1
          have hlenNext : (treeRep ++ offRep ++ [e]).length ≤ m :=
            nodup_snoc_length_le hextLt hsubE hnd heE heNotBoth
          have hcurPosW : base + 1 + (treeRep ++ offRep).length < 2 ^ w := by omega
          have hcurNextW : base + 1 + (treeRep ++ offRep).length + 1 < 2 ^ w := by omega
          have heW : e < 2 ^ w := by omega
          let thrPtr := mem₀ (tok.edgeThresholds + ei)
          have hthrAddrW : tok.edgeThresholds + ei < 2 ^ w := lt_trans (hltB (t12 ei heiCap) (by decide)) hbaseW
          have hthrEndB : thrPtr + L ≤ base := by
            have hlast : thrPtr + (L - 1) < base := by
              have h1 := (t1718 e heE).1 (L - 1) (by omega)
              rw [he2i] at h1; exact hltB h1 (by decide)
            omega
          have hthrPtrW : thrPtr < 2 ^ w := by omega
          have hthrEq : s6.mem (tok.edgeThresholds + ei) = thrPtr := by
            dsimp only [s6]; rw [hmemN]
            have hne : tok.edgeThresholds + ei ≠ tok.inOffReady + ei := fun h => by
              have h1 := t12 ei heiCap; have h2 := t15 ei heiCap; rw [h] at h1; omega
            simpa [s5, s4, s3, s2, s1, Function.update_of_ne hne, thrPtr] using
              hmemT (t12 ei heiCap) (by decide) (by decide) (by decide)
          let cursor := base + 1 + (treeRep ++ offRep).length
          have hlenLt : (treeRep ++ offRep).length < m := by
            simp only [List.length_append, List.length_singleton] at hlenNext ⊢; omega
          have hcurLtHeap0 : cursor < heap₀ := by change base + 1 + (treeRep ++ offRep).length < heap₀; omega
          let s7 := { s6 with mem := Function.update s6.mem cursor e }
          let s8 := { s7 with regs := Function.update s7.regs 3 (cursor + 1) }
          let s9 := { s8 with regs := Function.update s8.regs 20 thrPtr }
          have hthrNeCur : tok.edgeThresholds + ei ≠ cursor := by
            have := hltB (t12 ei heiCap) (by decide); omega
          have rStCur : Runs w p ω (.store (.reg 3) (.reg 16)) s6 .normal s7 3 :=
            runs_store_iff.mpr ⟨cursor, e, by simp [Expr.eval, s6, s5, s4, s3, s2, s1, hr3, cursor],
              by simp [Expr.eval, s6, s5, s4, s3], rfl, rfl, rfl⟩
          have rIncCur : Runs w p ω (.assign 3 (.bin .add (.reg 3) (.const 1))) s7 .normal s8 4 :=
            runs_assign_iff.mpr ⟨cursor + 1, by
              have hr3s : s7.regs 3 = cursor := by simp [s7, s6, s5, s4, s3, s2, s1, hr3, cursor]
              simp [Expr.eval, BinOp.eval, hr3s, hwnz, show cursor + 1 < 2 ^ w from hcurNextW],
              rfl, rfl, rfl⟩
          have rLoadThr : Runs w p ω (.assign 20 (.load (.bin .add (.reg 9) (.reg 15)))) s8 .normal s9 5 :=
            runs_assign_iff.mpr ⟨thrPtr, by
              have hr9s : s8.regs 9 = tok.edgeThresholds := by simp [s8, s7, s6, s5, s4, s3, s2, s1, hr9]
              have hr15s : s8.regs 15 = ei := by simp [s8, s7, s6, s5, s4, s3, s2, s1]
              have hms : s8.mem (tok.edgeThresholds + ei) = thrPtr := by
                simp only [s8, s7, Function.update_of_ne hthrNeCur]; exact hthrEq
              simp [Expr.eval, BinOp.eval, hr9s, hr15s, hthrAddrW, hms], rfl, rfl, rfl⟩
          have hvalRec9 : PathEdgeAt s9.mem recPtr 4 L (some val) := by
            refine hvalRec3.congr (fun a halo hahi => ?_)
            have hne : a ≠ cursor := by change a ≠ base + 1 + (treeRep ++ offRep).length; omega
            simp [s9, s8, s7, Function.update_of_ne hne, s6, hmemN, s5, s4]
          have hthrInt9 : PathIntAt s9.mem thrPtr 4 L (detectorThreshold P cfg.ε (model.extℓ e)) := by
            have hthr0 := (hedgeAcc.1 e heE).2.1
            rw [he2i] at hthr0
            refine hthr0.congr (fun idx hidx => ?_)
            have htag : tok.tag (thrPtr + idx) = 17 := by
              have h1 := (t1718 e heE).1 idx hidx; rwa [he2i] at h1
            have hneCur : thrPtr + idx ≠ cursor := by have := hltB htag (by decide); omega
            have hneIO : thrPtr + idx ≠ tok.inOffReady + ei := fun h => by
              have h2 := t15 ei heiCap; rw [h] at htag; omega
            simp only [s9, s8, s7, Function.update_of_ne hneCur, s6, hmemN, s5, s4, s3, s2, s1,
              Function.update_of_ne hneIO]
            exact hmemT htag (by decide) (by decide) (by decide)
          have hzCur9 : ZeroFrom s9.mem curHeap := fun a ha => by
            have hneCur : a ≠ cursor := by change a ≠ base + 1 + (treeRep ++ offRep).length; omega
            have hneIO : a ≠ tok.inOffReady + ei := by have := hltB (t15 ei heiCap) (by decide); omega
            simpa [s9, s8, s7, Function.update_of_ne hneCur, s6, hmemN, s5, s4, s3, s2, s1,
              Function.update_of_ne hneIO] using hzCur a ha
          have hResetPre : (detectResetContract w 4 val (detectorThreshold P cfg.ε (model.extℓ e))).pre
              [recPtr, thrPtr, L, curHeap] s9.mem :=
            ⟨recPtr, thrPtr, L, curHeap, rfl, by omega, by omega, by omega, hcurStepW,
              hvalRec9, hthrInt9, hfitThr e heE, hzCur9⟩
          have hResetEval : evalArgs w s9 [.reg 17, .reg 20, .reg 5, .reg 4] =
              some [recPtr, thrPtr, L, curHeap] := by
            simp [evalArgs, Expr.eval, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr5, hr4]
          have hrecPtrW : recPtr < 2 ^ w := by omega
          obtain ⟨bodyR, hbodyR, oR, stR, cR, hrR, hpostR, hcR⟩ :=
            hReset val (detectorThreshold P cfg.ε (model.extℓ e))
              [recPtr, thrPtr, L, curHeap] s9.mem s9.pos ω (by wram_words) hResetPre
          let retR := oR.value
          let memR := stR.mem
          obtain ⟨_, _, _, _, heqR, hretR, hnewEdgeR, hframeR, hzR⟩ := hpostR
          simp only [List.cons.injEq, and_true] at heqR
          obtain ⟨rfl, rfl, rfl, rfl⟩ := heqR
          change cR ≤ 87 * L + 96 at hcR
          let s10 : State := { mem := memR, regs := Function.update s9.regs 21 retR, pos := stR.pos }
          let s11 := { s10 with mem := Function.update s10.mem (tok.edgeRecords + ei) curHeap }
          let s12 := { s11 with regs := Function.update s11.regs 4 retR }
          have rResetCall : Runs w p ω (.call 21 reset [.reg 17, .reg 20, .reg 5, .reg 4])
              s9 .normal s10 (cR + 5) :=
            runs_call_iff.mpr ⟨[recPtr, thrPtr, L, curHeap], bodyR, oR, stR, cR,
              hResetEval, hbodyR, hrR, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
          have rStRec : Runs w p ω (.store (.bin .add (.reg 10) (.reg 15)) (.reg 4)) s10 .normal s11 5 :=
            runs_store_iff.mpr ⟨tok.edgeRecords + ei, curHeap,
              by simp [Expr.eval, BinOp.eval, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr10, herW],
              by simp [Expr.eval, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr4], rfl, rfl, rfl⟩
          have rUpdHeap : Runs w p ω (.assign 4 (.reg 21)) s11 .normal s12 2 :=
            runs_assign_iff.mpr ⟨retR, by simp [Expr.eval, s11, s10], rfl, rfl, rfl⟩
          have rEmit : Runs w p ω emitBody s6 .normal s12 (3 + (4 + (5 + ((cR + 5) + (5 + 2 + 1) + 1) + 1) + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨s7, 3, _, rStCur,
              runs_seq_iff.mpr (Or.inr ⟨s8, 4, _, rIncCur,
                runs_seq_iff.mpr (Or.inr ⟨s9, 5, _, rLoadThr,
                  runs_seq_iff.mpr (Or.inr ⟨s10, cR + 5, _, rResetCall,
                    runs_seq_iff.mpr (Or.inr ⟨s11, 5, 2, rStRec, rUpdHeap, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
          have rCond4 : Runs w p ω cond4 s6 .normal s12
              (1 + (3 + (4 + (5 + ((cR + 5) + (5 + 2 + 1) + 1) + 1) + 1) + 1) + 1) :=
            runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, s6, hnb0], by simpa using rEmit, rfl⟩
          have rInner : Runs w p ω innerBody s3 .normal s12 _ :=
            runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r17,
              runs_seq_iff.mpr (Or.inr ⟨s5, 8, _, r18,
                runs_seq_iff.mpr (Or.inr ⟨s6, cN + 3, _, r19, rCond4, rfl⟩), rfl⟩), rfl⟩)
          have rCond3 : Runs w p ω cond3 s3 .normal s12 _ :=
            runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, BinOp.eval, hs3_r8, hs3_r15, hslW, hslEq, hslot0],
              by simpa using rInner, rfl⟩
          have rCond2 : Runs w p ω cond2 s3 .normal s12 _ :=
            runs_cond_iff.mpr ⟨1, _, by
              simp [Expr.eval, BinOp.eval, hs3_r6, hs3_r16, hs3_r15, hfwdW, hfwdEq, hlive, hwnz],
              by simp only [Nat.one_ne_zero, ite_false]; exact rCond3, rfl⟩
          have rCond1 : Runs w p ω cond1 s3 .normal s12 _ :=
            runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, hs3_r16, hs3_r2, hem, hwnz],
              by simp only [Nat.one_ne_zero, ite_false]; exact rCond2, rfl⟩
          have rFull : Runs w p ω (detectOffTreeDrainStep isNeg reset) s .normal s12 _ :=
            runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
              runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
                runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3, rCond1, rfl⟩), rfl⟩), rfl⟩)
          have hmem12_lt (a : ℕ) (ha : a < curHeap) (hneEr : a ≠ tok.edgeRecords + ei)
              (hneCur : a ≠ cursor) (hneIO : a ≠ tok.inOffReady + ei) : s12.mem a = s.mem a := by
            have h1 : s12.mem a = memR a := by simp [s12, s11, s10, Function.update_of_ne hneEr]
            have h2 : memR a = s9.mem a := hframeR a ha
            have h3 : s9.mem a = s.mem a := by
              simp [s9, s8, s7, Function.update_of_ne hneCur, s6, hmemN, s5, s4, s3, s2, s1,
                Function.update_of_ne hneIO]
            exact h1.trans (h2.trans h3)
          have hvalFlow : (val.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e := by
            have hbr := (hedgeAcc.1 e heE).2.2
            rw [he2i, ite_eq_right hnotTree] at hbr
            obtain ⟨_, v0, _, hrec0, hfl0, _, _, _⟩ := hbr
            rw [pathEdgeAt_originalFlow_eq hvalRec0 hrec0]; exact hfl0
          refine ⟨.normal, s12, _, rFull, ⟨⟨offRep ++ [e], retR,
            by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr0],
            by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr1],
            by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr2],
            by simp [s12, s11, s10, s9, s8, s7, cursor]; omega,
            by simp [s12],
            by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr5],
            by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr6],
            by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr7],
            by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr8],
            by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr9],
            by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr10],
            by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr11],
            by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr12],
            by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr13],
            by simp, by simp; omega,
            by simpa [List.append_assoc] using hlenNext,
            by
              rw [← List.append_assoc, List.nodup_append]
              exact ⟨hnd, List.nodup_singleton e, fun a ha b hb => by
                simp only [List.mem_singleton] at hb; subst hb; intro h; exact heNotBoth (h ▸ ha)⟩,
            ?_, by omega, by rw [Nat.succ_mul]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
            by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hr14]⟩,
            by simp only [Expr.size, detectOffTreeStepBudget]; omega⟩
          · rw [← List.append_assoc]
            intro idx hidx
            by_cases hlast : idx = (treeRep ++ offRep).length
            · subst hlast
              have hneEr : cursor ≠ tok.edgeRecords + ei := by
                have := hltB (t13 ei heiCap) (by decide)
                change base + 1 + (treeRep ++ offRep).length ≠ _; omega
              have h1 : s12.mem cursor = memR cursor := by
                simp [s12, s11, s10, Function.update_of_ne hneEr]
              have h2 : memR cursor = s9.mem cursor := hframeR cursor (by omega)
              have h3 : s9.mem cursor = e := by simp [s9, s8, s7]
              simpa [cursor, List.getElem_append_right] using h1.trans (h2.trans h3)
            · have hltIdx : idx < (treeRep ++ offRep).length := by
                simp only [List.length_append, List.length_singleton] at hidx hlast ⊢; omega
              have hneEr : base + 1 + idx ≠ tok.edgeRecords + ei := by
                have := hltB (t13 ei heiCap) (by decide); omega
              have hneIO : base + 1 + idx ≠ tok.inOffReady + ei := by
                have := hltB (t15 ei heiCap) (by decide); omega
              rw [hmem12_lt _ (by omega) hneEr (by omega) hneIO, List.getElem_append_left hltIdx]
              exact hlist idx hltIdx
          · intro a ha
            have hneEr : a ≠ tok.edgeRecords + ei := by have := hltB (t13 ei heiCap) (by decide); omega
            simpa [s12, s11, s10, Function.update_of_ne hneEr] using hzR a ha
          · intro k hk
            by_cases hkj : k = j
            · subst hkj
              have hneEr : tok.inOffReady + ei ≠ tok.edgeRecords + ei := fun h => by
                have h1 := t15 ei heiCap; have h2 := t13 ei heiCap; rw [h] at h1; omega
              have hneCur : tok.inOffReady + ei ≠ cursor := by
                have := hltB (t15 ei heiCap) (by decide); omega
              have h1 : s12.mem (tok.inOffReady + ei) = memR (tok.inOffReady + ei) := by
                simp [s12, s11, s10, Function.update_of_ne hneEr]
              have h2 : memR (tok.inOffReady + ei) = s9.mem (tok.inOffReady + ei) :=
                hframeR _ (by have := hltB (t15 ei heiCap) (by decide); omega)
              have h3 : s9.mem (tok.inOffReady + ei) = 0 := by
                simp [s9, s8, s7, Function.update_of_ne hneCur, s6, hmemN, s5, s4, s3, s2, s1]
              exact h1.trans (h2.trans h3)
            · have hklt : k < j := by omega
              have hkCap : mem₀ (tok.offReadyList + k) < tok.intCap := (hoffInv.2.1 k (lt_trans hklt hj)).1
              have hneEr : tok.inOffReady + mem₀ (tok.offReadyList + k) ≠ tok.edgeRecords + ei := fun h => by
                have h1 := t15 _ hkCap; have h2 := t13 ei heiCap; rw [h] at h1; omega
              have hneCur : tok.inOffReady + mem₀ (tok.offReadyList + k) ≠ cursor := by
                have := hltB (t15 _ hkCap) (by decide); omega
              have hneIO : tok.inOffReady + mem₀ (tok.offReadyList + k) ≠ tok.inOffReady + ei := by
                intro heq; exact hoffInv.2.2.1 k (lt_trans hklt hj) j hj hkj (by omega)
              rw [hmem12_lt _ (by have := hltB (t15 _ hkCap) (by decide); omega) hneEr hneCur hneIO]
              exact hclr k hklt
          · intro k hklo hkhi
            have hkCap : mem₀ (tok.offReadyList + k) < tok.intCap := (hoffInv.2.1 k hkhi).1
            have hneEr : tok.inOffReady + mem₀ (tok.offReadyList + k) ≠ tok.edgeRecords + ei := fun h => by
              have h1 := t15 _ hkCap; have h2 := t13 ei heiCap; rw [h] at h1; omega
            have hneCur : tok.inOffReady + mem₀ (tok.offReadyList + k) ≠ cursor := by
              have := hltB (t15 _ hkCap) (by decide); omega
            have hneIO : tok.inOffReady + mem₀ (tok.offReadyList + k) ≠ tok.inOffReady + ei := by
              intro heq; exact hoffInv.2.2.1 k hkhi j hj (by omega) (by omega)
            rw [hmem12_lt _ (by have := hltB (t15 _ hkCap) (by decide); omega) hneEr hneCur hneIO]
            exact hkeep1 k (by omega) hkhi
          · intro x hx h0x
            by_cases hxei : x = ei
            · subst hxei
              have hneEr : tok.inOffReady + ei ≠ tok.edgeRecords + ei := fun h => by
                have h1 := t15 ei heiCap; have h2 := t13 ei heiCap; rw [h] at h1; omega
              have hneCur : tok.inOffReady + ei ≠ cursor := by have := hltB (t15 ei heiCap) (by decide); omega
              have h1 : s12.mem (tok.inOffReady + ei) = memR (tok.inOffReady + ei) := by
                simp [s12, s11, s10, Function.update_of_ne hneEr]
              have h2 : memR (tok.inOffReady + ei) = s9.mem (tok.inOffReady + ei) :=
                hframeR _ (by have := hltB (t15 ei heiCap) (by decide); omega)
              have h3 : s9.mem (tok.inOffReady + ei) = 0 := by
                simp [s9, s8, s7, Function.update_of_ne hneCur, s6, hmemN, s5, s4, s3, s2, s1]
              exact h1.trans (h2.trans h3)
            · have hneEr : tok.inOffReady + x ≠ tok.edgeRecords + ei := fun h => by
                have h1 := t15 x hx; have h2 := t13 ei heiCap; rw [h] at h1; omega
              have hneCur : tok.inOffReady + x ≠ cursor := by have := hltB (t15 x hx) (by decide); omega
              rw [hmem12_lt _ (by have := hltB (t15 x hx) (by decide); omega) hneEr hneCur (by omega)]
              exact hzero0 x hx h0x
          · intro x
            rw [List.mem_append, List.mem_singleton, hoffIff x]
            constructor
            · rintro (⟨k, hk, h1, h2⟩ | rfl)
              · exact ⟨k, by omega, h1, h2⟩
              · exact ⟨j, by omega, hReadyEi, heEq⟩
            · rintro ⟨k, hk, h1, h2⟩
              by_cases hkj : k = j
              · subst hkj; exact Or.inr (h2.trans heEq.symm)
              · exact Or.inl ⟨k, by omega, h1, h2⟩
          · intro x hx; dsimp only; intro hnotT
            by_cases hxe : x = e
            · simp only [hxe, List.mem_append, List.mem_singleton, or_true, ↓reduceIte, he2i]
              have hptr : s12.mem (tok.edgeRecords + ei) = curHeap := by simp [s12, s11]
              rw [hptr]
              have hglE := hwire.2.2.2.2 e heE; dsimp only at hglE
              rw [he2i, ite_eq_right hnotTree] at hglE
              obtain ⟨hfwdE, hgradE, hlenE⟩ := hglE val hvalRec0
              refine ⟨hcurLo, by omega, { val with detector := -detectorThreshold P cfg.ε (model.extℓ e) },
                ?_, hfwdE, hvalFlow, rfl, hgradE, hlenE⟩
              refine hnewEdgeR.congr (fun a halo hahi => ?_)
              have hneEr : a ≠ tok.edgeRecords + ei := by have := hltB (t13 ei heiCap) (by decide); omega
              simp [s12, s11, s10, Function.update_of_ne hneEr, memR]
            · have hneEi : model.extToInt x ≠ ei := fun h => hxe (by
                have := hfreshInv.hLeft x hx; rw [h] at this; exact this.symm.trans heEq.symm)
              have hxCap := (hedgeAcc.1 x hx).1
              have hneEr : tok.edgeRecords + model.extToInt x ≠ tok.edgeRecords + ei := by omega
              have hneCur : tok.edgeRecords + model.extToInt x ≠ cursor := by
                have := hltB (t13 _ hxCap) (by decide); omega
              have hneIO : tok.edgeRecords + model.extToInt x ≠ tok.inOffReady + ei := fun h => by
                have h1 := t13 _ hxCap; have h2 := t15 ei heiCap; rw [h] at h1; omega
              have hptrEq : s12.mem (tok.edgeRecords + model.extToInt x) =
                  s.mem (tok.edgeRecords + model.extToInt x) :=
                hmem12_lt _ (by have := hltB (t13 _ hxCap) (by decide); omega) hneEr hneCur hneIO
              have hrec := hrecInv x hx hnotT
              have hxMem : (x ∈ offRep ++ [e]) ↔ x ∈ offRep := by simp [hxe]
              simp only [hxMem]
              split_ifs at hrec ⊢ with hxIn
              · obtain ⟨hlo, hhi, vx, hpa, hfwdx, hfl, hdet, hgradx, hlenx⟩ := hrec
                rw [hptrEq]
                refine ⟨hlo, by omega, vx, ?_, hfwdx, hfl, hdet, hgradx, hlenx⟩
                refine hpa.congr (fun a halo hahi => ?_)
                have hne1 : a ≠ tok.edgeRecords + ei := by have := hltB (t13 ei heiCap) (by decide); omega
                have hne2 : a ≠ cursor := by omega
                have hne3 : a ≠ tok.inOffReady + ei := by have := hltB (t15 ei heiCap) (by decide); omega
                exact hmem12_lt a (by omega) hne1 hne2 hne3
              · obtain ⟨heqP, hcell⟩ := hrec
                refine ⟨hptrEq.trans heqP, fun idx hidx => ?_⟩
                have htag : tok.tag (mem₀ (tok.edgeRecords + model.extToInt x) + idx) = 18 :=
                  (t1718 x hx).2 hnotT idx hidx
                have hne1 : mem₀ (tok.edgeRecords + model.extToInt x) + idx ≠ tok.edgeRecords + ei := fun h => by
                  have h2 := t13 ei heiCap; rw [h] at htag; omega
                have hne2 : mem₀ (tok.edgeRecords + model.extToInt x) + idx ≠ cursor := by
                  have := hltB htag (by decide); omega
                have hne3 : mem₀ (tok.edgeRecords + model.extToInt x) + idx ≠ tok.inOffReady + ei := fun h => by
                  have h2 := t15 ei heiCap; rw [h] at htag; omega
                rw [hmem12_lt _ (by have := hltB htag (by decide); omega) hne1 hne2 hne3]
                exact hcell idx hidx
          · intro a ha h1 h2 h3
            have hneC : a ≠ cursor := by change a ≠ base + 1 + (treeRep ++ offRep).length; omega
            rw [hmem12_lt a (by omega) (by omega) hneC (by omega)]
            exact hframe0 a ha h1 h2 h3
          · -- The new block starts at `curHeap`, above every block allocated before.
            have hoffE (z : ℕ) (hz : z ∈ offRep) : z ∈ model.extG.E := by
              obtain ⟨_, _, hR, rfl⟩ := (hoffIff z).mp hz; exact hR.1
            have hptrE : s12.mem (tok.edgeRecords + model.extToInt e) = curHeap := by
              rw [he2i]; simp [s12, s11]
            have hptrOld (z : ℕ) (hz : z ∈ offRep) : s12.mem (tok.edgeRecords + model.extToInt z) =
                s.mem (tok.edgeRecords + model.extToInt z) := by
              have hzE := hoffE z hz
              have hze : z ≠ e := fun h => heNotBoth (h ▸ List.mem_append_right _ hz)
              have hneEi : model.extToInt z ≠ ei := fun h => hze (by
                have := hfreshInv.hLeft z hzE; rw [h] at this; exact this.symm.trans heEq.symm)
              have hzCap := (hedgeAcc.1 z hzE).1
              exact hmem12_lt _ (by have := hltB (t13 _ hzCap) (by decide); omega) (by omega)
                (by have := hltB (t13 _ hzCap) (by decide); omega)
                (fun h => by have h1 := t13 _ hzCap; have h2 := t15 ei heiCap; rw [h] at h1; omega)
            have hbelowCur (z : ℕ) (hz : z ∈ offRep) :
                s.mem (tok.edgeRecords + model.extToInt z) + (2 + 4 * L) ≤ curHeap := by
              obtain ⟨_, _, hR, hzEq⟩ := (hoffIff z).mp hz
              have hnotT : model.extToInt z ∉ model.chain.toTreeChain.chainTree.E := by
                rw [hzEq, hR.2.1]; exact hR.2.2.1
              have hrec := hrecInv z (hoffE z hz) hnotT
              rw [if_pos hz] at hrec
              exact hrec.2.1
            intro x hx y hy hxy
            simp only [List.mem_append, List.mem_singleton] at hx hy
            rcases hx with hx | rfl <;> rcases hy with hy | rfl
            · rw [hptrOld x hx, hptrOld y hy]; exact hsepR x hx y hy hxy
            · rw [hptrOld x hx, hptrE]; exact Or.inl (hbelowCur x hx)
            · rw [hptrOld y hy, hptrE]; exact Or.inr (hbelowCur y hy)
            · exact absurd rfl hxy
      · have hnotR : ¬ IsOffTreeReady model ei := fun hR => by
          have hbr := (hedgeAcc.1 e heE).2.2
          rw [he2i, ite_eq_right hR.2.2.1] at hbr
          exact hslot0 hbr.1
        have rCond3 : Runs w p ω cond3 s3 .normal s3 6 :=
          runs_cond_iff.mpr ⟨mem₀ (tok.slots + ei), 1,
            by simp [Expr.eval, BinOp.eval, hs3_r8, hs3_r15, hslW, hslEq],
            by rw [ite_eq_right hslot0]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
        have rCond2 : Runs w p ω cond2 s3 .normal s3 13 :=
          runs_cond_iff.mpr ⟨1, 6, by
            simp [Expr.eval, BinOp.eval, hs3_r6, hs3_r16, hs3_r15, hfwdW, hfwdEq, hlive, hwnz],
            by simp only [Nat.one_ne_zero, ite_false]; exact rCond3, rfl⟩
        have rCond1 : Runs w p ω cond1 s3 .normal s3 17 :=
          runs_cond_iff.mpr ⟨1, 13, by simp [Expr.eval, BinOp.eval, hs3_r16, hs3_r2, hem, hwnz],
            by simp only [Nat.one_ne_zero, ite_false]; exact rCond2, rfl⟩
        exact ⟨.normal, s3, 35,
          runs_seq_iff.mpr (Or.inr ⟨s1, 5, 29, r1,
            runs_seq_iff.mpr (Or.inr ⟨s2, 5, 23, r2,
              runs_seq_iff.mpr (Or.inr ⟨s3, 5, 17, r3, rCond1, rfl⟩), rfl⟩), rfl⟩),
          hSkipClose rfl (fun _ _ => rfl) hnotR, by dsimp only [detectOffTreeStepBudget]; omega⟩
    · have hnotR : ¬ IsOffTreeReady model ei := fun hR => by
        have hpair := (live_offtree_iff hfreshTab hExtRange hextLt heiCap).mpr ⟨hR.1, hR.2.1⟩
        exact hlive hpair.2
      have rCond2 : Runs w p ω cond2 s3 .normal s3 8 :=
        runs_cond_iff.mpr ⟨0, 1, by
          simp [Expr.eval, BinOp.eval, hs3_r6, hs3_r16, hs3_r15, hfwdW, hfwdEq, hlive],
          by simp only [ite_true]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
      have rCond1 : Runs w p ω cond1 s3 .normal s3 12 :=
        runs_cond_iff.mpr ⟨1, 8, by simp [Expr.eval, BinOp.eval, hs3_r16, hs3_r2, hem, hwnz],
          by simp only [Nat.one_ne_zero, ite_false]; exact rCond2, rfl⟩
      exact ⟨.normal, s3, 30,
        runs_seq_iff.mpr (Or.inr ⟨s1, 5, 24, r1,
          runs_seq_iff.mpr (Or.inr ⟨s2, 5, 18, r2,
            runs_seq_iff.mpr (Or.inr ⟨s3, 5, 12, r3, rCond1, rfl⟩), rfl⟩), rfl⟩),
        hSkipClose rfl (fun _ _ => rfl) hnotR, by dsimp only [detectOffTreeStepBudget]; omega⟩
  · have hnotR : ¬ IsOffTreeReady model ei := fun hR => by
      have hpair := (live_offtree_iff hfreshTab hExtRange hextLt heiCap).mpr ⟨hR.1, hR.2.1⟩
      exact hem hpair.1
    have rCond1 : Runs w p ω cond1 s3 .normal s3 5 :=
      runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, hs3_r16, hs3_r2, hem],
        by simp only [ite_true]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    exact ⟨.normal, s3, 23,
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, 17, r1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 5, 11, r2,
          runs_seq_iff.mpr (Or.inr ⟨s3, 5, 5, r3, rCond1, rfl⟩), rfl⟩), rfl⟩),
      hSkipClose rfl (fun _ _ => rfl) hnotR, by dsimp only [detectOffTreeStepBudget]; omega⟩

end MinCostFlow.MinRatio
