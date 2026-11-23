module

public import MinCostFlow.MinRatio.WireEvalBase
import WordRAM.Tactic

/-!
# Off-tree edge loop and representation preservation for `evalCycleBody`

Proves:
1. `evalEdgesLoop_runs`: Loop 2 of `evalCycleBody` scans the explicit off-tree edge list,
   adding or subtracting each record's gradient and adding its length.
2. `solverStateRep_after_eval`: re-establishes `solverStateRep` after `evalCycleBody`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut LinkCut.PathTree LinkCut.PathProg Chain

/-! ### Helper: Loop 2 (off-tree edge records) -/

theorem evalEdgesLoop_runs
    {w L P edgesBase edgeRecords workHeap heapAfterPaths maxEdges maxPaths : ℕ}
    {cfg : Alg2Config} {numAdd numSub : ℕ} {p : Program} {ω : ℕ → Bool}
    {model : Alg2State cfg} {edges : List (ℕ × Bool)} {B : ℤ}
    (hAdd : MeetsContract w p numAdd (Num.addContract w 4))
    (hSub : MeetsContract w p numSub (Num.subtractContract w 4))
    (hw10 : 10 ≤ w) (hB : 0 ≤ B)
    (hedgesMax : edges.length ≤ maxEdges)
    (hedgesEnd : edgesBase + 2 * edges.length ≤ workHeap)
    (hheapLo : workHeap + 2 * L ≤ heapAfterPaths)
    (hheapHi : heapAfterPaths ≤ workHeap + 2 * L + maxPaths * (pathApplySpace L + 4 * L))
    (hcapE : 2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ))
    (hroom : workHeap + evalCycleSpace L maxEdges maxPaths < 2 ^ w) :
    ∀ (rem : ℕ) (st : State) (curInner curNorm : ℤ) (innerPtr normPtr curHeap : ℕ),
      let j := edges.length - rem
      rem ≤ edges.length →
      st.regs 1 = edgesBase → st.regs 2 = edges.length → st.regs 5 = workHeap →
      st.regs 8 = L → st.regs 9 = edgeRecords →
      st.regs 10 = innerPtr → st.regs 11 = normPtr → st.regs 12 = curHeap → st.regs 13 = j →
      ExplicitEdgesAt st.mem edgesBase edges →
      (∀ x ∈ edges,
        edgeRecords + x.1 < workHeap ∧
        st.mem (edgeRecords + x.1) + 2 + 4 * L ≤ workHeap ∧
        ∃ val : PathEdgeValue,
          PathEdgeAt st.mem (st.mem (edgeRecords + x.1)) 4 L (some val) ∧
          val.forward = true ∧
          (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg (model.intToExt x.1) ∧
          (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ (model.intToExt x.1) ∧
          |val.gradient| ≤ B ∧ |val.length| ≤ B) →
      (innerPtr = workHeap ∨ workHeap + 2 * L ≤ innerPtr) →
      (normPtr = workHeap + L ∨ workHeap + 2 * L ≤ normPtr) →
      innerPtr + L ≤ curHeap → normPtr + L ≤ curHeap →
      heapAfterPaths ≤ curHeap →
      curHeap ≤ heapAfterPaths + j * (3 * L) →
      PathIntAt st.mem innerPtr 4 L curInner →
      PathIntAt st.mem normPtr 4 L curNorm →
      |curInner| ≤ ((maxPaths * model.extG.n + j : ℕ) : ℤ) * B →
      |curNorm| ≤ ((maxPaths * model.extG.n + j : ℕ) : ℤ) * B →
      ZeroFrom st.mem curHeap →
      ∃ out cost addGrad addLen innerPtr' normPtr' curHeap',
        Runs w p ω
          (.loop (.bin .lt (.reg 13) (.reg 2))
            ((.assign 14 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 13)))) ;;
              .assign 15 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 13))) (.const 1))) ;;
              .assign 16 (.load (.bin .add (.reg 9) (.reg 14))) ;;
              .assign 17 (.bin .add (.reg 16) (.const 2)) ;;
              .cond (.reg 15)
                (.assign 18 (.reg 12) ;;
                 .call 12 numAdd [.reg 10, .reg 17, .reg 8, .reg 12] ;;
                 .assign 10 (.reg 18))
                (.assign 18 (.bin .add (.reg 12) (.reg 8)) ;;
                 .call 12 numSub [.reg 10, .reg 17, .reg 8, .reg 12] ;;
                 .assign 10 (.reg 18)) ;;
              .assign 17 (.bin .add (.reg 17) (.reg 8)) ;;
              .assign 18 (.reg 12) ;;
              .call 12 numAdd [.reg 11, .reg 17, .reg 8, .reg 12] ;;
              .assign 11 (.reg 18)) ;;
             .assign 13 (.bin .add (.reg 13) (.const 1))))
          st .normal out cost ∧
        out.regs 5 = workHeap ∧ out.regs 8 = L ∧
        out.regs 10 = innerPtr' ∧ out.regs 11 = normPtr' ∧ out.regs 12 = curHeap' ∧
        (innerPtr' = workHeap ∨ workHeap + 2 * L ≤ innerPtr') ∧
        (normPtr' = workHeap + L ∨ workHeap + 2 * L ≤ normPtr') ∧
        innerPtr' + L ≤ curHeap' ∧ normPtr' + L ≤ curHeap' ∧
        curHeap ≤ curHeap' ∧ curHeap' ≤ heapAfterPaths + edges.length * (3 * L) ∧
        PathIntAt out.mem innerPtr' 4 L (curInner + addGrad) ∧
        PathIntAt out.mem normPtr' 4 L (curNorm + addLen) ∧
        (addGrad : ℝ) / (2 : ℝ) ^ P =
          ((edges.drop j).map fun x => (if x.2 then (1 : ℝ) else -1) * model.extg (model.intToExt x.1)).sum ∧
        (addLen : ℝ) / (2 : ℝ) ^ P =
          ((edges.drop j).map fun x => model.extℓ (model.intToExt x.1)).sum ∧
        ZeroFrom out.mem curHeap' ∧
        (∀ a < curHeap, out.mem a = st.mem a) ∧
        cost ≤ rem * (112 * L + 180) + 4 := by
  intro rem
  have hw1024 : 1024 ≤ 2 ^ w := by
    calc (1024 : ℕ) = 2 ^ 10 := by decide
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw10
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hLW : L < 2 ^ w := by dsimp only [evalCycleSpace] at hroom; omega
  induction rem with
  | zero =>
    intro st curInner curNorm innerPtr normPtr curHeap j hrem _ hr2 hr5 hr8 _ hr10 hr11 hr12 hr13
      _ _ hInPos hNoPos hInLe hNoLe _ hCurHi hInAt hNoAt _ _ hz
    have hjEq : j = edges.length := by dsimp only [j]; omega
    have hdrop : edges.drop j = [] := List.drop_eq_nil_of_le (by omega)
    have hcond0 : (Expr.bin .lt (.reg 13) (.reg 2)).eval w st = some 0 := by
      simp [Expr.eval, BinOp.eval, hr13, hr2, hjEq, show 0 < 2 ^ w by omega]
    refine ⟨st, 4, 0, 0, innerPtr, normPtr, curHeap,
      runs_loop_iff.mpr (Or.inl ⟨hcond0, rfl, rfl, by simp [Expr.size]⟩),
      hr5, hr8, hr10, hr11, hr12, hInPos, hNoPos, hInLe, hNoLe, le_rfl,
      by rw [hjEq] at hCurHi; exact hCurHi,
      by simpa using hInAt, by simpa using hNoAt,
      by simp [hdrop], by simp [hdrop], hz, fun _ _ => rfl, by omega⟩
  | succ rem ih =>
    intro st curInner curNorm innerPtr normPtr curHeap j hrem hr1 hr2 hr5 hr8 hr9 hr10 hr11 hr12 hr13
      hEdAt hEdOk hInPos hNoPos hInLe hNoLe hCurLo hCurHi hInAt hNoAt hInBd hNoBd hz
    have hjLt : j < edges.length := by dsimp only [j]; omega
    have hremNext : edges.length - rem = j + 1 := by dsimp only [j]; omega
    have hstepW : heapAfterPaths + (j + 1) * (3 * L) < 2 ^ w := by
      have hm : (j + 1) * (3 * L) ≤ maxEdges * (3 * L) := Nat.mul_le_mul_right _ (by omega)
      dsimp only [evalCycleSpace] at hroom; omega
    have hcurW : curHeap < 2 ^ w := by
      have hm : j * (3 * L) ≤ (j + 1) * (3 * L) := Nat.mul_le_mul_right _ (by omega)
      omega
    obtain ⟨hmEi, hmDir⟩ := hEdAt.read hjLt
    let x := edges[j]'hjLt
    let ei := x.1
    let dir := x.2
    obtain ⟨herW, hrecEnd, val, hrecAt, hfwd, hgrEq, hlenEq, hgrBd, hlenBd⟩ :=
      hEdOk x (List.getElem_mem hjLt)
    let recPtr := st.mem (edgeRecords + ei)
    have hworkW : workHeap < 2 ^ w := by dsimp only [evalCycleSpace] at hroom; omega
    have herW' : edgeRecords + ei < workHeap := herW
    have hrecEnd' : recPtr + 2 + 4 * L ≤ workHeap := hrecEnd
    have hrecPtrW : recPtr + 2 + 2 * L < 2 ^ w := by omega
    have h2jW : 2 * j < 2 ^ w := by omega
    have he2jW : edgesBase + 2 * j < 2 ^ w := by omega
    have he2j1W : edgesBase + 2 * j + 1 < 2 ^ w := by omega
    -- Preamble: load `ei`, `dir`, `recPtr`, `gradPtr := recPtr + 2`
    let s1 : State := { st with regs := Function.update st.regs 14 ei }
    let s2 : State := { s1 with regs := Function.update s1.regs 15 (if dir then 1 else 0) }
    let s3 : State := { s2 with regs := Function.update s2.regs 16 recPtr }
    let s4 : State := { s3 with regs := Function.update s3.regs 17 (recPtr + 2) }
    have r1 : Runs w p ω (.assign 14 (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 13)))))
        st .normal s1 7 :=
      runs_assign_iff.mpr ⟨ei, by
        simp [Expr.eval, BinOp.eval, hr1, hr13, hw2, h2jW, he2jW, hmEi, ei, x], rfl, rfl, rfl⟩
    have r2 : Runs w p ω (.assign 15 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 13))) (.const 1))))
        s1 .normal s2 9 :=
      runs_assign_iff.mpr ⟨if dir then 1 else 0, by
        simp [Expr.eval, BinOp.eval, s1, hr1, hr13, hw2, hw1, h2jW, he2jW, he2j1W, hmDir, dir, x],
        rfl, rfl, rfl⟩
    have r3 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 9) (.reg 14)))) s2 .normal s3 5 :=
      runs_assign_iff.mpr ⟨recPtr, by
        simp [Expr.eval, BinOp.eval, s2, s1, hr9, show edgeRecords + ei < 2 ^ w by omega, recPtr],
        rfl, rfl, rfl⟩
    have r4 : Runs w p ω (.assign 17 (.bin .add (.reg 16) (.const 2))) s3 .normal s4 4 :=
      runs_assign_iff.mpr ⟨recPtr + 2, by
        simp [Expr.eval, BinOp.eval, s3, hw2, show recPtr + 2 < 2 ^ w by omega], rfl, rfl, rfl⟩
    -- Conditional: add or subtract `val.gradient` into `inner`
    let deltaG : ℤ := if dir then val.gradient else -val.gradient
    have hInNextBd : |curInner + deltaG| ≤ ((maxPaths * model.extG.n + (j + 1) : ℕ) : ℤ) * B := by
      have h1 : |curInner + deltaG| ≤ |curInner| + |deltaG| := abs_add_le _ _
      have h2 : |deltaG| ≤ B := by dsimp [deltaG]; split_ifs <;> simp [hgrBd]
      have h3 : ((maxPaths * model.extG.n + j : ℕ) : ℤ) * B + B =
          ((maxPaths * model.extG.n + (j + 1) : ℕ) : ℤ) * B := by push_cast; ring
      omega
    have hInNextFits : Num.Fits 4 L (curInner + deltaG) := by
      refine fits_of_abs_le hInNextBd ?_
      have hle : ((maxPaths * model.extG.n + (j + 1) : ℕ) : ℤ) ≤
          ((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) := by exact_mod_cast (show maxPaths * model.extG.n + (j + 1) ≤ maxEdges + maxPaths * model.extG.n by omega)
      have hmul := mul_le_mul_of_nonneg_right hle hB
      omega
    have hcondStep : ∃ (s5 : State) (cCond newInnerPtr heap1 : ℕ),
        Runs w p ω
          (.cond (.reg 15)
            (.assign 18 (.reg 12) ;;
             .call 12 numAdd [.reg 10, .reg 17, .reg 8, .reg 12] ;;
             .assign 10 (.reg 18))
            (.assign 18 (.bin .add (.reg 12) (.reg 8)) ;;
             .call 12 numSub [.reg 10, .reg 17, .reg 8, .reg 12] ;;
             .assign 10 (.reg 18))) s4 .normal s5 cCond ∧
        (∀ r, r ≠ 10 → r ≠ 12 → r ≠ 18 → s5.regs r = s4.regs r) ∧
        s5.regs 10 = newInnerPtr ∧ s5.regs 12 = heap1 ∧
        workHeap + 2 * L ≤ newInnerPtr ∧ newInnerPtr + L ≤ heap1 ∧
        curHeap ≤ heap1 ∧ heap1 ≤ curHeap + 2 * L ∧
        PathIntAt s5.mem newInnerPtr 4 L (curInner + deltaG) ∧
        ZeroFrom s5.mem heap1 ∧
        (∀ a < curHeap, s5.mem a = st.mem a) ∧
        cCond ≤ 74 * L + 60 := by
      cases hdir : dir with
      | true =>
        let s4a : State := { s4 with regs := Function.update s4.regs 18 curHeap }
        have r4a : Runs w p ω (.assign 18 (.reg 12)) s4 .normal s4a 2 :=
          runs_assign_iff.mpr ⟨curHeap, by simp [Expr.eval, s4, s3, s2, s1, hr12], rfl, rfl, rfl⟩
        obtain ⟨bA, hbA, oA, stA, cA, hrA, hpostA, hcA⟩ :=
          hAdd [innerPtr, recPtr + 2, L, curHeap] s4a.mem s4a.pos ω
            (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
                rcases hy with rfl | rfl | rfl | rfl <;> omega)
            ⟨innerPtr, recPtr + 2, L, curHeap, rfl,
              ⟨innerPtr, recPtr + 2, L, 0, curHeap, rfl, by omega, by omega, by decide,
                hInAt.1, hrecAt.2.2.1.1⟩,
              hz, by change curHeap + L < 2 ^ w; rw [Nat.add_mul, one_mul] at hstepW; omega⟩
        obtain ⟨hretA, _, _, hfrA, hzA, hlistA⟩ := hpostA
        change oA.value = curHeap + L at hretA
        change ∀ y < curHeap, stA.mem y = st.mem y at hfrA
        change ZeroFrom stA.mem oA.value at hzA
        change ListAt stA.mem curHeap (Num.digits 4 L (Num.unsignedVal st.mem innerPtr 4 L +
          Num.unsignedVal st.mem (recPtr + 2) 4 L + 0)) at hlistA
        have hvA := Num.addCarry_value hlistA
        have hInA : PathIntAt stA.mem curHeap 4 L (curInner + deltaG) := by
          refine ⟨hvA.1, ?_⟩
          rw [hvA.2, hInAt.2, hrecAt.2.2.1.2, Int.natCast_zero, add_zero]
          have hdg : curInner + val.gradient = curInner + deltaG := by simp [deltaG, hdir]
          rw [hdg, Num.wrap_of_fits hInNextFits]
        have hcA' : cA ≤ 38 * L + 15 := hcA
        let s4b : State := { stA with regs := Function.update s4a.regs 12 (curHeap + L) }
        let s5 : State := { s4b with regs := Function.update s4b.regs 10 curHeap }
        have r4b : Runs w p ω (.call 12 numAdd [.reg 10, .reg 17, .reg 8, .reg 12]) s4a .normal s4b (4 + cA + 1) :=
          runs_call_iff.mpr ⟨[innerPtr, recPtr + 2, L, curHeap], bA, oA, stA, cA,
            by simp [evalArgs, Expr.eval, s4a, s4, s3, s2, s1, hr10, hr8, hr12],
            hbA, hrA, rfl, by simp [s4b, hretA], by simp [argsSize, Expr.size]⟩
        have r4c : Runs w p ω (.assign 10 (.reg 18)) s4b .normal s5 2 :=
          runs_assign_iff.mpr ⟨curHeap, by simp [Expr.eval, s4b, s4a], rfl, rfl, rfl⟩
        have rThen : Runs w p ω _ s4 .normal s5 (2 + ((4 + cA + 1) + 2 + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨s4a, 2, _, r4a,
            runs_seq_iff.mpr (Or.inr ⟨s4b, 4 + cA + 1, 2, r4b, r4c, rfl⟩), rfl⟩)
        refine ⟨s5, 1 + (2 + ((4 + cA + 1) + 2 + 1) + 1) + 1, curHeap, curHeap + L,
          runs_cond_iff.mpr ⟨1, 2 + ((4 + cA + 1) + 2 + 1) + 1, by simp [Expr.eval, s4, s3, s2, hdir],
            by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact rThen, by simp [Expr.size]⟩,
          fun r h10 h12 h18 => by simp [s5, s4b, s4a, h10, h12, h18],
          by simp [s5], by simp [s5, s4b], by omega, by omega, by omega, by omega,
          hInA, hretA ▸ hzA, hfrA, by omega⟩
      | false =>
        have hcurLW : curHeap + L < 2 ^ w := by rw [Nat.add_mul, one_mul] at hstepW; omega
        let s4a : State := { s4 with regs := Function.update s4.regs 18 (curHeap + L) }
        have r4a : Runs w p ω (.assign 18 (.bin .add (.reg 12) (.reg 8))) s4 .normal s4a 4 :=
          runs_assign_iff.mpr ⟨curHeap + L, by
            simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, hr12, hr8, hcurLW], rfl, rfl, rfl⟩
        obtain ⟨bS, hbS, oS, stS, cS, hrS, hpostS, hcS⟩ :=
          hSub [innerPtr, recPtr + 2, L, curHeap] s4a.mem s4a.pos ω
            (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
                rcases hy with rfl | rfl | rfl | rfl <;> omega)
            ⟨⟨innerPtr, recPtr + 2, L, curHeap, rfl, by omega, by omega, hInAt.1, hrecAt.2.2.1.1⟩,
              hz, by change curHeap + 2 * L < 2 ^ w; rw [Nat.add_mul, one_mul] at hstepW; omega⟩
        obtain ⟨hretS, _, _, hfrS, hzS, hvS, hintS⟩ := hpostS
        change oS.value = curHeap + 2 * L at hretS
        change ∀ y < curHeap, stS.mem y = st.mem y at hfrS
        change ZeroFrom stS.mem oS.value at hzS
        change Num.Valid stS.mem (curHeap + L) 4 L at hvS
        change Num.intVal stS.mem (curHeap + L) 4 L =
          Num.wrap 4 L (Num.intVal st.mem innerPtr 4 L - Num.intVal st.mem (recPtr + 2) 4 L) at hintS
        have hInS : PathIntAt stS.mem (curHeap + L) 4 L (curInner + deltaG) := by
          refine ⟨hvS, ?_⟩
          rw [hintS, hInAt.2, hrecAt.2.2.1.2]
          have hdg : curInner - val.gradient = curInner + deltaG := by simp [deltaG, hdir, sub_eq_add_neg]
          rw [hdg, Num.wrap_of_fits hInNextFits]
        have hcS' : cS ≤ 74 * L + 42 := hcS
        let s4b : State := { stS with regs := Function.update s4a.regs 12 (curHeap + 2 * L) }
        let s5 : State := { s4b with regs := Function.update s4b.regs 10 (curHeap + L) }
        have r4b : Runs w p ω (.call 12 numSub [.reg 10, .reg 17, .reg 8, .reg 12]) s4a .normal s4b (4 + cS + 1) :=
          runs_call_iff.mpr ⟨[innerPtr, recPtr + 2, L, curHeap], bS, oS, stS, cS,
            by simp [evalArgs, Expr.eval, s4a, s4, s3, s2, s1, hr10, hr8, hr12],
            hbS, hrS, rfl, by simp [s4b, hretS], by simp [argsSize, Expr.size]⟩
        have r4c : Runs w p ω (.assign 10 (.reg 18)) s4b .normal s5 2 :=
          runs_assign_iff.mpr ⟨curHeap + L, by simp [Expr.eval, s4b, s4a], rfl, rfl, rfl⟩
        have rElse : Runs w p ω _ s4 .normal s5 (4 + ((4 + cS + 1) + 2 + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨s4a, 4, _, r4a,
            runs_seq_iff.mpr (Or.inr ⟨s4b, 4 + cS + 1, 2, r4b, r4c, rfl⟩), rfl⟩)
        refine ⟨s5, 1 + (4 + ((4 + cS + 1) + 2 + 1) + 1) + 1, curHeap + L, curHeap + 2 * L,
          runs_cond_iff.mpr ⟨0, 4 + ((4 + cS + 1) + 2 + 1) + 1, by simp [Expr.eval, s4, s3, s2, hdir],
            by simp only [↓reduceIte]; exact rElse, by simp [Expr.size]⟩,
          fun r h10 h12 h18 => by simp [s5, s4b, s4a, h10, h12, h18],
          by simp [s5], by simp [s5, s4b], by omega, by omega, by omega, by omega,
          hInS, hretS ▸ hzS, hfrS, by omega⟩
    obtain ⟨s5, cCond, newInnerPtr, heap1, rCond, hs5_regs, hs5_10, hs5_12, hnewInLo, hnewInLe,
      hh1Lo, hh1Hi, hInAt5, hz5, hfr5, hcCond⟩ := hcondStep
    -- Add `val.length` into `norm`
    have hh1W : heap1 < 2 ^ w := by rw [Nat.add_mul, one_mul] at hstepW; omega
    have hlenPtrW : recPtr + 2 + L < 2 ^ w := by omega
    let s6 : State := { s5 with regs := Function.update s5.regs 17 (recPtr + 2 + L) }
    let s7 : State := { s6 with regs := Function.update s6.regs 18 heap1 }
    have r6 : Runs w p ω (.assign 17 (.bin .add (.reg 17) (.reg 8))) s5 .normal s6 4 :=
      runs_assign_iff.mpr ⟨recPtr + 2 + L, by
        have h17 := (hs5_regs 17 (by decide) (by decide) (by decide))
        have h8 := (hs5_regs 8 (by decide) (by decide) (by decide))
        simp [Expr.eval, BinOp.eval, h17, h8, s4, s3, s2, s1, hr8, hlenPtrW], rfl, rfl, rfl⟩
    have r7 : Runs w p ω (.assign 18 (.reg 12)) s6 .normal s7 2 :=
      runs_assign_iff.mpr ⟨heap1, by simp [Expr.eval, s6, hs5_12], rfl, rfl, rfl⟩
    have hNoAt5 : PathIntAt s5.mem normPtr 4 L curNorm :=
      hNoAt.congr fun i hi => hfr5 (normPtr + i) (by omega)
    have hLenAt5 : PathIntAt s5.mem (recPtr + 2 + L) 4 L val.length :=
      hrecAt.2.2.2.1.congr fun i hi => hfr5 (recPtr + 2 + L + i) (by omega)
    have hNoNextBd : |curNorm + val.length| ≤ ((maxPaths * model.extG.n + (j + 1) : ℕ) : ℤ) * B := by
      have h1 : |curNorm + val.length| ≤ |curNorm| + |val.length| := abs_add_le _ _
      have h2 : ((maxPaths * model.extG.n + j : ℕ) : ℤ) * B + B =
          ((maxPaths * model.extG.n + (j + 1) : ℕ) : ℤ) * B := by push_cast; ring
      omega
    have hNoNextFits : Num.Fits 4 L (curNorm + val.length) := by
      refine fits_of_abs_le hNoNextBd ?_
      have hle : ((maxPaths * model.extG.n + (j + 1) : ℕ) : ℤ) ≤
          ((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) := by
        exact_mod_cast (show maxPaths * model.extG.n + (j + 1) ≤ maxEdges + maxPaths * model.extG.n by omega)
      have hmul := mul_le_mul_of_nonneg_right hle hB
      omega
    obtain ⟨bN, hbN, oN, stN, cN, hrN, hpostN, hcN⟩ :=
      hAdd [normPtr, recPtr + 2 + L, L, heap1] s7.mem s7.pos ω
        (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
            rcases hy with rfl | rfl | rfl | rfl <;> omega)
        ⟨normPtr, recPtr + 2 + L, L, heap1, rfl,
          ⟨normPtr, recPtr + 2 + L, L, 0, heap1, rfl, by omega, by omega, by decide, hNoAt5.1, hLenAt5.1⟩,
          hz5, by change heap1 + L < 2 ^ w; rw [Nat.add_mul, one_mul] at hstepW; omega⟩
    obtain ⟨hretN, _, _, hfrN, hzN, hlistN⟩ := hpostN
    change oN.value = heap1 + L at hretN
    change ∀ y < heap1, stN.mem y = s5.mem y at hfrN
    change ZeroFrom stN.mem oN.value at hzN
    change ListAt stN.mem heap1 (Num.digits 4 L (Num.unsignedVal s5.mem normPtr 4 L +
      Num.unsignedVal s5.mem (recPtr + 2 + L) 4 L + 0)) at hlistN
    have hvN := Num.addCarry_value hlistN
    have hNoAtN : PathIntAt stN.mem heap1 4 L (curNorm + val.length) := by
      refine ⟨hvN.1, ?_⟩
      rw [hvN.2, hNoAt5.2, hLenAt5.2, Int.natCast_zero, add_zero, Num.wrap_of_fits hNoNextFits]
    have hInAtN : PathIntAt stN.mem newInnerPtr 4 L (curInner + deltaG) :=
      hInAt5.congr fun i hi => hfrN (newInnerPtr + i) (by omega)
    have hcN' : cN ≤ 38 * L + 15 := hcN
    let heap2 := heap1 + L
    let s8 : State := { stN with regs := Function.update s7.regs 12 heap2 }
    let s9 : State := { s8 with regs := Function.update s8.regs 11 heap1 }
    let s10 : State := { s9 with regs := Function.update s9.regs 13 (j + 1) }
    have r8 : Runs w p ω (.call 12 numAdd [.reg 11, .reg 17, .reg 8, .reg 12]) s7 .normal s8 (4 + cN + 1) :=
      runs_call_iff.mpr ⟨[normPtr, recPtr + 2 + L, L, heap1], bN, oN, stN, cN,
        by
          have h11 := hs5_regs 11 (by decide) (by decide) (by decide)
          have h8 := hs5_regs 8 (by decide) (by decide) (by decide)
          simp [evalArgs, Expr.eval, s7, s6, h11, h8, hs5_12, s4, s3, s2, s1, hr11, hr8],
        hbN, hrN, rfl, by simp [s8, hretN, heap2], by simp [argsSize, Expr.size]⟩
    have r9 : Runs w p ω (.assign 11 (.reg 18)) s8 .normal s9 2 :=
      runs_assign_iff.mpr ⟨heap1, by simp [Expr.eval, s8, s7], rfl, rfl, rfl⟩
    have r10 : Runs w p ω (.assign 13 (.bin .add (.reg 13) (.const 1))) s9 .normal s10 4 :=
      runs_assign_iff.mpr ⟨j + 1, by
        have h13 := hs5_regs 13 (by decide) (by decide) (by decide)
        simp [Expr.eval, BinOp.eval, s9, s8, s7, s6, h13, s4, s3, s2, s1, hr13, hw1,
          show j + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    let cBody := (7 + (9 + (5 + (4 + (cCond + (4 + (2 + ((4 + cN + 1) + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 4 + 1
    have rBody : Runs w p ω _ st .normal s10 cBody :=
      runs_seq_iff.mpr (Or.inr ⟨s9, _, 4,
        runs_seq_iff.mpr (Or.inr ⟨s1, 7, _, r1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 9, _, r2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
        runs_seq_iff.mpr (Or.inr ⟨s4, 4, _, r4,
        runs_seq_iff.mpr (Or.inr ⟨s5, cCond, _, rCond,
        runs_seq_iff.mpr (Or.inr ⟨s6, 4, _, r6,
        runs_seq_iff.mpr (Or.inr ⟨s7, 2, _, r7,
        runs_seq_iff.mpr (Or.inr ⟨s8, 4 + cN + 1, 2, r8, r9, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
          rfl⟩), rfl⟩), rfl⟩), rfl⟩), r10, rfl⟩)
    -- Frame below `curHeap`
    have hfr10 : ∀ a < curHeap, s10.mem a = st.mem a := fun a ha =>
      (hfrN a (by omega)).trans (hfr5 a ha)
    have hEdAt10 : ExplicitEdgesAt s10.mem edgesBase edges :=
      hEdAt.congr fun y hlo hhi => hfr10 y (by omega)
    have hEdOk10 : ∀ y ∈ edges,
        edgeRecords + y.1 < workHeap ∧
        s10.mem (edgeRecords + y.1) + 2 + 4 * L ≤ workHeap ∧
        ∃ val : PathEdgeValue,
          PathEdgeAt s10.mem (s10.mem (edgeRecords + y.1)) 4 L (some val) ∧
          val.forward = true ∧
          (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg (model.intToExt y.1) ∧
          (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ (model.intToExt y.1) ∧
          |val.gradient| ≤ B ∧ |val.length| ≤ B := by
      intro y hy
      obtain ⟨h1, h2, v0, hpa, hfw, hg, hl, hgb, hlb⟩ := hEdOk y hy
      have hptr : s10.mem (edgeRecords + y.1) = st.mem (edgeRecords + y.1) := hfr10 _ (by omega)
      rw [hptr]
      exact ⟨h1, h2, v0, hpa.congr (fun z zlo zhi => hfr10 z (by omega)), hfw, hg, hl, hgb, hlb⟩
    -- Recurse on `rem`
    obtain ⟨out, cRest, addGR, addLR, innerPtr', normPtr', curHeap', hrRest,
        hr5', hr8', hr10', hr11', hr12', hInPos', hNoPos', hInLe', hNoLe', hHeapLo', hHeapHi',
        hInAt', hNoAt', haddGR, haddLR, hz', hfrRest, hcRest⟩ :=
      ih s10 (curInner + deltaG) (curNorm + val.length) newInnerPtr heap1 heap2 (by omega)
        (by have := hs5_regs 1 (by decide) (by decide) (by decide); simp [s10, s9, s8, s7, s6, this, s4, s3, s2, s1, hr1])
        (by have := hs5_regs 2 (by decide) (by decide) (by decide); simp [s10, s9, s8, s7, s6, this, s4, s3, s2, s1, hr2])
        (by have := hs5_regs 5 (by decide) (by decide) (by decide); simp [s10, s9, s8, s7, s6, this, s4, s3, s2, s1, hr5])
        (by have := hs5_regs 8 (by decide) (by decide) (by decide); simp [s10, s9, s8, s7, s6, this, s4, s3, s2, s1, hr8])
        (by have := hs5_regs 9 (by decide) (by decide) (by decide); simp [s10, s9, s8, s7, s6, this, s4, s3, s2, s1, hr9])
        (by simp [s10, s9, s8, s7, s6, hs5_10]) (by simp [s10, s9]) (by simp [s10, s9, s8])
        (by simp [s10, hremNext])
        hEdAt10 hEdOk10 (Or.inr hnewInLo) (Or.inr (by omega))
        (by dsimp only [heap2]; omega) (by dsimp only [heap2]; omega)
        (by dsimp only [heap2]; omega)
        (by rw [hremNext, Nat.add_mul, one_mul]; dsimp only [heap2]; omega)
        hInAtN hNoAtN (by rw [hremNext]; exact hInNextBd) (by rw [hremNext]; exact hNoNextBd)
        (by dsimp only [s10, s9, s8, heap2]; rw [← hretN]; exact hzN)
    have hcond1 : (Expr.bin .lt (.reg 13) (.reg 2)).eval w st = some 1 := by
      simp [Expr.eval, BinOp.eval, hr13, hr2, hjLt, hw1]
    have hrLoop : Runs w p ω _ st .normal out (3 + cBody + cRest + 1) :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s10, cBody, cRest, hcond1, by decide, rBody, hrRest,
        by simp [Expr.size]⟩))
    have hdropSplit : edges.drop j = x :: edges.drop (j + 1) := List.drop_eq_getElem_cons hjLt
    have hdgDiv : (deltaG : ℝ) / (2 : ℝ) ^ P =
        (if dir then (1 : ℝ) else -1) * model.extg (model.intToExt ei) := by
      have hvg : (val.gradient : ℝ) / (2 : ℝ) ^ P = model.extg (model.intToExt ei) := by
        unfold PathEdgeValue.originalGradient at hgrEq
        simpa [hfwd] using hgrEq
      dsimp only [deltaG]
      cases dir <;> simp [hvg, neg_div]
    have htotG : ((deltaG + addGR : ℤ) : ℝ) / (2 : ℝ) ^ P =
        ((edges.drop j).map fun y => (if y.2 then (1 : ℝ) else -1) * model.extg (model.intToExt y.1)).sum := by
      rw [hdropSplit, List.map_cons, List.sum_cons, Int.cast_add, add_div, hdgDiv, ← hremNext, haddGR]
    have htotL : ((val.length + addLR : ℤ) : ℝ) / (2 : ℝ) ^ P =
        ((edges.drop j).map fun y => model.extℓ (model.intToExt y.1)).sum := by
      rw [hdropSplit, List.map_cons, List.sum_cons, Int.cast_add, add_div, hlenEq, ← hremNext, haddLR]
    refine ⟨out, _, deltaG + addGR, val.length + addLR, innerPtr', normPtr', curHeap', hrLoop,
      hr5', hr8', hr10', hr11', hr12', hInPos', hNoPos', hInLe', hNoLe',
      le_trans (by dsimp only [heap2]; omega) hHeapLo', hHeapHi',
      by rw [← add_assoc]; exact hInAt', by rw [← add_assoc]; exact hNoAt',
      htotG, htotL, hz',
      fun a ha => (hfrRest a (by dsimp only [heap2]; omega)).trans (hfr10 a ha), ?_⟩
    rw [Nat.add_mul, one_mul]
    omega

/-! ### Re-establishing `solverStateRep` after `evalCycleBody` -/

theorem solverStateRep_after_eval {cfg : Alg2Config}
    {L P m V psi k epsExp drainUnit : ℕ} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    (hlocalCore : Rcore.Local)
    {root workHeap : ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {mem mem' : ℕ → ℕ} {s' : PathTreeState} {trees' : List AuxTree} {depth' : ℕ → ℕ}
    {treeTok' : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < workHeap)
    (hsn : s'.n = model.extG.n)
    (hlct' : LctInvWith pathPayload s' trees' tok.free depth')
    (htrep' : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).rep tok.treeHeap s' treeTok' mem')
    (hfr : ∀ a < workHeap, ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a →
      mem' a = mem a)
    (hns' : TreeEditNamedSlots s' trees' model.chain.toTreeChain.chainTree
      (fun ei => mem (tok.slots + ei)) (fun sl => mem (tok.names + sl)))
    (hpreSome' : ∀ sl val, (sl, some val) ∈ forestPairs pathPayload s'.splay trees' →
      ∃ val0, (sl, some val0) ∈ forestPairs pathPayload tok.tree.splay tok.trees)
    (hor' : ∀ e ∈ model.chain.toTreeChain.chainTree.E ∩ (model.chain.G 0).E, ∀ val : PathEdgeValue,
      (mem (tok.slots + e), some val) ∈ forestPairs pathPayload tok.tree.splay tok.trees →
      ∃ val' : PathEdgeValue,
        (mem (tok.slots + e), some val') ∈ forestPairs pathPayload s'.splay trees' ∧
        val'.originalFlow = val.originalFlow ∧
        val'.originalGradient = val.originalGradient ∧
        val'.length = val.length ∧
        val'.detector = val.detector ∧
        (val'.forward = true →
          inducedSubPar pathPayload s'.splay trees' (vid (model.chain.toTreeChain.chainTree.head e)) = mem (tok.slots + e) ∧
          inducedSubPar pathPayload s'.splay trees' (mem (tok.slots + e)) = vid (model.chain.toTreeChain.chainTree.tail e)) ∧
        (val'.forward = false →
          inducedSubPar pathPayload s'.splay trees' (vid (model.chain.toTreeChain.chainTree.tail e)) = mem (tok.slots + e) ∧
          inducedSubPar pathPayload s'.splay trees' (mem (tok.slots + e)) = vid (model.chain.toTreeChain.chainTree.head e))) :
    let tok' : SolverToken cfg L Rcore :=
      { tok with tree := s', trees := trees', depth := depth', treeTok := treeTok' }
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok' mem' ∧
    (∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a ↔
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a) ∧
    (∀ i < cfg.P.d, Rcore.phi (tok'.coreHandle i) (tok'.coreTok i) mem' =
      Rcore.phi (tok.coreHandle i) (tok.coreTok i) mem) := by
  dsimp only
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  obtain ⟨hrootDir, hdetect, hnum, hchainP, hfreshInv, hfreshTab, hextM, hintCapE,
    hsched, hoffReady, htn, hlct, htrep, hedgeAcc, hcores, htermH, htermBr,
    htermRep, hwire, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15,
    t16, t1718, t19, t20, t21⟩ := htags
  have hfoot_eq : ∀ a, Rtree.foot tok.treeHeap treeTok' a ↔ Rtree.foot tok.treeHeap tok.treeTok a := by
    intro a
    change (tok.treeHeap ≤ a ∧ a < arenaEnd tok.treeHeap treeTok'.1.n L) ↔
      (tok.treeHeap ≤ a ∧ a < arenaEnd tok.treeHeap tok.treeTok.1.n L)
    rw [htrep'.1, htrep.1, hsn, htn]
  have hagT {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv16 : v ≠ 16) : mem' a = mem a :=
    hfr a (hbelow a (Or.inl (hOwn a (ht ▸ hv0)))) (fun hf => hv16 (ht.symm.trans (t16 a hf)))
  have hcore_ag (i : ℕ) (hi : i < cfg.P.d) (a : ℕ)
      (ha : Rcore.foot (tok.coreHandle i) (tok.coreTok i) a) : mem a = mem' a :=
    (hagT (t21 i hi a ha) (by omega) (by omega)).symm
  have htermLocal := LastLevelProgram.lastLevelRepresentation_local tok.vcLast tok.ecLast
    4 L P (model.chain.G cfg.P.d).E
  have hterm_ag (a : ℕ)
      (ha : (LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
        (model.chain.G cfg.P.d).E).foot tok.termHandle tok.termTok a) : mem a = mem' a :=
    (hagT (t19 a ((lastLevelRepresentation_foot_indep_P _ _ _ _ P 0 _ _ _ _).mp ha))
      (by decide) (by decide)).symm
  have hmem_et (e : ℕ) (he : e ∈ model.extG.E) :
      mem' (tok.edgeThresholds + model.extToInt e) = mem (tok.edgeThresholds + model.extToInt e) :=
    hagT (t12 _ (hedgeAcc.1 e he).1) (by decide) (by decide)
  have hmem_er (e : ℕ) (he : e ∈ model.extG.E) :
      mem' (tok.edgeRecords + model.extToInt e) = mem (tok.edgeRecords + model.extToInt e) :=
    hagT (t13 _ (hedgeAcc.1 e he).1) (by decide) (by decide)
  have hmem_sl (ei : ℕ) (hei : ei < tok.intCap) : mem' (tok.slots + ei) = mem (tok.slots + ei) :=
    hagT (t9 ei hei) (by decide) (by decide)
  have hmem_nm (sl : ℕ) (hsl : sl < 2 * model.extG.n) : mem' (tok.names + sl) = mem (tok.names + sl) :=
    hagT (t10 sl (htn.symm ▸ hsl)) (by decide) (by decide)
  have hlistC {base : ℕ} {xs : List ℕ} (h : ListAt mem base xs)
      (hag : ∀ j < xs.length, mem' (base + j) = mem (base + j)) : ListAt mem' base xs :=
    fun j hj => (hag j hj).trans (h j hj)
  refine ⟨⟨hlistC hrootDir (fun j hj => hagT (t1 j (by simpa [List.length] using hj)) (by decide) (by decide)),
    hlistC hdetect (fun j hj => hagT (t2 j (by simp [List.length] at hj; omega)) (by decide) (by decide)),
    hlistC hnum (fun j hj => by
      have h1 : tok.handle + 5 + j = tok.handle + (5 + j) := by omega
      rw [h1]; exact hagT (t2 (5 + j) (by simp [List.length] at hj; omega)) (by decide) (by decide)),
    hlistC hchainP (fun j hj => by
      have h1 : tok.handle + 9 + j = tok.handle + (9 + j) := by omega
      rw [h1]; exact hagT (t2 (9 + j) (by simp [List.length] at hj; omega)) (by decide) (by decide)),
    hfreshInv,
    ⟨(hagT t6 (by decide) (by decide)).trans hfreshTab.1,
      fun e he => (hagT (t7 e he) (by decide) (by decide)).trans (hfreshTab.2.1 e he),
      fun e he => (hagT (t8 e he) (by decide) (by decide)).trans (hfreshTab.2.2 e he)⟩,
    hextM, hintCapE,
    ⟨fun i => (hagT (t5 i.val (by omega)) (by decide) (by decide)).trans (hsched.1 i),
      fun i hi => by
        have h1 : tok.levelsEnd + (cfg.P.d + 1) + i = tok.levelsEnd + (cfg.P.d + 1 + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.1 i hi),
      fun i hi => by
        have h1 : tok.levelsEnd + 2 * (cfg.P.d + 1) + i = tok.levelsEnd + (2 * (cfg.P.d + 1) + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.2.1 i hi),
      fun i hi => by
        have h1 : tok.levelsEnd + 3 * (cfg.P.d + 1) + i = tok.levelsEnd + (3 * (cfg.P.d + 1) + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.2.2.1 i hi),
      (hagT (t5 (4 * (cfg.P.d + 1)) (by omega)) (by decide) (by decide)).trans hsched.2.2.2.2⟩,
    ?_, hsn, hlct', htrep', ?_,
    fun i hi => by
      obtain ⟨hh, hbr, hcr⟩ := hcores i hi
      exact ⟨(hagT (t4 i (by omega)) (by decide) (by decide)).trans hh,
        by
          have h1 : tok.handle + 18 + (cfg.P.d + 1) + i = tok.handle + 18 + (cfg.P.d + 1 + i) := by omega
          rw [h1] at hbr ⊢; exact (hagT (t4 _ (by omega)) (by decide) (by decide)).trans hbr,
        (hlocalCore (tok.coreHandle i) _ (tok.coreTok i) mem mem' (hcore_ag i hi)).1 hcr⟩,
    (hagT (t4 cfg.P.d (by omega)) (by decide) (by decide)).trans htermH,
    by
      have h1 : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by omega
      rw [h1] at htermBr ⊢; exact (hagT (t4 _ (by omega)) (by decide) (by decide)).trans htermBr,
    (htermLocal tok.termHandle _ tok.termTok mem mem' hterm_ag).1 htermRep,
    ?_,
    ⟨hOwn, t1, t2, t3, t4, t5, t6, t7, t8, t9,
      fun j hj => t10 j (by rw [htn]; exact hsn ▸ hj),
      fun j hj => t11 j (by rw [htn]; exact hsn ▸ hj),
      t12, t13, t14, t15,
      fun a ha => t16 a ((hfoot_eq a).mp ha),
      fun e he => by dsimp only; rw [hmem_et e he, hmem_er e he]; exact t1718 e he,
      t19, t20, t21⟩⟩,
    fun a => by
      dsimp only [solverStateRep]
      constructor
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl ((hfoot_eq a).mp h))
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl ((hfoot_eq a).mpr h))
        · exact Or.inr (Or.inr h),
    fun i hi => (hlocalCore (tok.coreHandle i) (chainLevelOrdAbs model.chain i) (tok.coreTok i) mem mem'
      (hcore_ag i hi)).2.symm⟩
  · obtain ⟨hcnt, hmemL, hdist, hbits, hrev⟩ := hoffReady
    refine ⟨hcnt, fun j hj => ?_, fun j₁ hj₁ j₂ hj₂ hne => ?_, fun e he => ?_, fun e he h1 => ?_⟩
    · rw [hagT (t14 j (lt_of_lt_of_le hj hcnt)) (by decide) (by decide)]
      exact ⟨(hmemL j hj).1, (hagT (t15 _ (hmemL j hj).1) (by decide) (by decide)).trans (hmemL j hj).2⟩
    · rw [hagT (t14 j₁ (lt_of_lt_of_le hj₁ hcnt)) (by decide) (by decide),
          hagT (t14 j₂ (lt_of_lt_of_le hj₂ hcnt)) (by decide) (by decide)]
      exact hdist j₁ hj₁ j₂ hj₂ hne
    · rw [hagT (t15 e he) (by decide) (by decide)]; exact hbits e he
    · rw [hagT (t15 e he) (by decide) (by decide)] at h1
      obtain ⟨j, hj, hje⟩ := hrev e he h1
      exact ⟨j, hj, (hagT (t14 j (lt_of_lt_of_le hj hcnt)) (by decide) (by decide)).trans hje⟩
  · refine ⟨fun e he => ?_, fun sl val hsl hpair => ?_⟩
    · obtain ⟨heiCap, hthr, hbranch⟩ := hedgeAcc.1 e he
      refine ⟨heiCap, ?_, ?_⟩
      · rw [hmem_et e he]
        exact hthr.congr fun j hj => hagT ((t1718 e he).1 j hj) (by decide) (by decide)
      · split_ifs at hbranch ⊢ with hin
        · obtain ⟨hsnz, his, hnm, hst, val, acc, hpair, hfl, hac, hdet⟩ := hbranch
          have hslLt : mem (tok.slots + model.extToInt e) < 2 * model.extG.n := by
            unfold isEdgeSlot at his; omega
          dsimp only
          rw [hmem_sl _ heiCap, hmem_et e he, hmem_nm _ hslLt,
            hagT (t11 _ (htn.symm ▸ hslLt)) (by decide) (by decide)]
          obtain ⟨val', hp', hfl', _, _, hdet', _⟩ :=
            hor' _ (Finset.mem_inter.mpr ⟨hin, hfreshInv.hE ▸ Finset.mem_image_of_mem _ he⟩) val hpair
          exact ⟨hsnz, by unfold isEdgeSlot at his ⊢; omega, hnm, hst, val', acc, hp',
            by rw [hfl']; exact hfl, hac, by rw [hdet']; exact hdet⟩
        · obtain ⟨hs0, val, acc, hrec, hfl, hac, hdet, hpush⟩ := hbranch
          dsimp only
          rw [hmem_sl _ heiCap, hmem_er e he]
          refine ⟨hs0, val, acc, hrec.congr (fun x hx1 hx2 => by
            have hx : x = mem (tok.edgeRecords + model.extToInt e) +
                (x - mem (tok.edgeRecords + model.extToInt e)) := by omega
            rw [hx]; exact hagT ((t1718 e he).2 hin _ (by omega)) (by decide) (by decide)),
            hfl, hac, hdet, fun hnn => (hagT (t15 _ heiCap) (by decide) (by decide)).trans (hpush hnn)⟩
    · dsimp only at hsl ⊢
      have hslLt : sl < 2 * model.extG.n := by unfold isEdgeSlot at hsl; omega
      obtain ⟨val0, hp0⟩ := hpreSome' sl val hpair
      have hsl0 : isEdgeSlot tok.tree.n sl := by unfold isEdgeSlot at hsl ⊢; omega
      obtain ⟨heiCap, hin, hse, heE, he2i⟩ := hedgeAcc.2 sl val0 hsl0 hp0
      rw [hmem_nm sl hslLt, hmem_sl _ heiCap]
      exact ⟨heiCap, hin, hse, heE, he2i⟩
  · obtain ⟨htabW, hrgW, hsubCap, _, hglW⟩ := hwire
    refine ⟨fun j hj => (hagT (t3 j hj) (by decide) (by decide)).trans (htabW j hj),
      hrgW.of_agree (fun a h1 h2 => hagT (t20 a h1 h2) (by decide) (by decide)),
      hsubCap,
      ⟨fun ei hei => by
          dsimp only
          rw [hmem_sl ei (hsubCap.2 ei hei).1]
          obtain ⟨h1, h2, h3⟩ := hns'.forward ei hei
          have hslLt : mem (tok.slots + ei) < 2 * model.extG.n := by unfold isEdgeSlot at h2; omega
          rw [hmem_nm _ hslLt]; exact ⟨h1, h2, h3⟩,
        fun sl hsl hs => by
          dsimp only at hs ⊢
          have hslLt : sl < 2 * model.extG.n := by unfold isEdgeSlot at hs; omega
          rw [hmem_nm sl hslLt]
          obtain ⟨heE, hse⟩ := hns'.inverse sl hsl hs
          rw [hmem_sl _ (hsubCap.2 _ heE).1]; exact ⟨heE, hse⟩,
        fun ei hei => by dsimp only; rw [hmem_sl ei (hsubCap.2 ei hei).1]; exact hns'.endpoints ei hei⟩,
      fun e he => by
        dsimp only
        have hgl := hglW e he; dsimp only at hgl
        have heiCap := (hedgeAcc.1 e he).1
        split_ifs at hgl ⊢ with hin
        · rw [hmem_sl _ heiCap]
          intro val hp
          have hbranch := (hedgeAcc.1 e he).2.2
          rw [ite_eq_left hin] at hbranch
          obtain ⟨_, _, _, _, val0, _, hp0, _⟩ := hbranch
          obtain ⟨val1, hp1, _, hgr1, hlen1, _, hft1, hff1⟩ :=
            hor' _ (Finset.mem_inter.mpr ⟨hin, hfreshInv.hE ▸ Finset.mem_image_of_mem _ he⟩) val0 hp0
          have heq := forestPairs_val_unique hlct' hp hp1
          subst heq
          obtain ⟨hg0, hl0, _⟩ := hgl val0 hp0
          exact ⟨by rw [hgr1]; exact hg0, by rw [hlen1]; exact hl0, hft1, hff1⟩
        · intro val hpa
          rw [hmem_er e he] at hpa
          exact hgl val (hpa.congr fun x hx1 hx2 => by
            have hx : x = mem (tok.edgeRecords + model.extToInt e) +
                (x - mem (tok.edgeRecords + model.extToInt e)) := by omega
            rw [hx]; exact (hagT ((t1718 e he).2 hin _ (by omega)) (by decide) (by decide)).symm)⟩


end MinCostFlow.MinRatio
