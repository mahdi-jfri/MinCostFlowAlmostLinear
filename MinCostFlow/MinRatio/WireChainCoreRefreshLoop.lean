module

public import MinCostFlow.MinRatio.WireChainCoreRefreshSetup
import WordRAM.Tactic

/-!
# Batch edge-account refresh loop execution (`WireChainCoreRefreshLoop`)

Proves `wireRefreshAccountsBody_runs`: refreshes `edgeThresholds[ei_new]` and `edgeRecords[ei_new]`
for every live deleted edge `ei_old ∈ G₀.E` in `U_int` in `O(|U_int| · L^2)` steps, leaving
`offReadyList` and `inOffReady` untouched so `wireTreeSyncLoop` can link newly-inserted edges
before off-tree ready edges are pushed.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
  MinCostFlow.IPM.Machine

set_option maxHeartbeats 600000 in
/-- Execute `wireRefreshAccountsBody`: refreshes thresholds and canonical `PathEdgeAt` records
for every live deleted edge in `U_int` in `O(|U_int| · L^2)` steps. -/
theorem wireRefreshAccountsBody_runs
    {w shift negate refreshOneProc divide add sub copy isNeg
      root uIntBuf g l heap handle table levelsEnd forward inverse freshCounter
      slots names slotThresholds edgeThresholds edgeRecords offReadyCount offReadyList inOffReady
      rootGraph intCap n rootECap m L P epsExp nf' pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {G0 : MGraph} {U_int : List Update} {e2i' i2e' : ℕ → ℕ}
    {oldVal : ℕ → PathEdgeValue} {oldThr acc gNew : ℕ → ℤ} {lNew : ℕ → ℕ}
    (hRefProc : p.procs[refreshOneProc]? = some (wireRefreshOneAccountBody divide add sub negate copy isNeg))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w 4))
    (hdiv : MeetsContract w p divide (Num.fixedDivideContract w 4))
    (hadd : MeetsContract w p add (Num.addContract w 4))
    (hsub : MeetsContract w p sub (Num.subtractContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hisNeg : MeetsContract w p isNeg (Num.isNegativeContract w 4))
    (hRoot : SolverRootDirAt mem root handle table levelsEnd forward inverse freshCounter slots
      names slotThresholds edgeThresholds edgeRecords offReadyCount offReadyList inOffReady
      rootGraph intCap)
    (hLmem : mem (handle + 5) = L) (hPmem : mem (handle + 8) = P)
    (hEpsMem : mem (handle + 16) = epsExp)
    (hDG0 : DynGraphAt mem rootGraph n rootECap G0)
    (hBatch : BatchAt mem uIntBuf U_int)
    (hEdgeOnly : ∀ u ∈ U_int, IsEdgeUpdate u)
    (hFresh : FreshTablesAt mem forward inverse freshCounter m intCap e2i' i2e' nf')
    (hLpos : 0 < L) (hPdiv : 4 ∣ P) (hPword : P < 2 ^ w) (hle : epsExp ≤ P)
    (hfitPos : P - epsExp + 1 < 4 * L)
    (hDelInfo : ∀ ei_old ∈ G0.E, .delete ei_old ∈ U_int →
      let e := i2e' ei_old
      let ei_new := e2i' e
      let ε := (((2 : ℤ) ^ (P - epsExp) : ℤ) : ℝ) / (2 : ℝ) ^ P
      let thrNew := detectorThreshold P ε ((lNew e : ℝ) / (2 : ℝ) ^ P)
      ei_old < intCap ∧ ei_old < rootECap ∧ e < m ∧ ei_new < intCap ∧
      0 < lNew e ∧
      (∀ ei2 ∈ G0.E, .delete ei2 ∈ U_int → ei_new ≠ ei2) ∧
      (∀ ei2 ∈ G0.E, .delete ei2 ∈ U_int → ei2 ≠ ei_old → e2i' (i2e' ei2) ≠ ei_new) ∧
      (oldVal ei_old).forward = true ∧
      PathEdgeAt mem (mem (edgeRecords + ei_old)) 4 L (some (oldVal ei_old)) ∧
      PathIntAt mem (mem (edgeThresholds + ei_old)) 4 L (oldThr ei_old) ∧
      (oldVal ei_old).detector = acc ei_old - oldThr ei_old ∧
      PathIntAt mem (g + e * L) 4 L (gNew e) ∧
      PathIntAt mem (l + e * L) 4 L (lNew e : ℤ) ∧
      Num.Fits 4 L (-thrNew) ∧ Num.Fits 4 L thrNew ∧
      Num.Fits 4 L (acc ei_old) ∧ Num.Fits 4 L (acc ei_old - thrNew) ∧
      mem (edgeRecords + ei_old) + (2 + 4 * L) ≤ heap ∧
      mem (edgeThresholds + ei_old) + L ≤ heap ∧
      (∀ j < 2 + 4 * L, ¬ InRefreshMutable edgeThresholds edgeRecords intCap (mem (edgeRecords + ei_old) + j)) ∧
      (∀ j < L, ¬ InRefreshMutable edgeThresholds edgeRecords intCap (mem (edgeThresholds + ei_old) + j)))
    (hRootLe : root + 16 ≤ heap) (hHandleLe : handle + 18 ≤ heap)
    (hRGLe : rootGraph + dynGraphSize n rootECap ≤ heap)
    (hBatchLe : uIntBuf + (batchWords U_int).length ≤ heap)
    (hFwdLe : forward + m ≤ heap) (hInvLe : inverse + intCap ≤ heap)
    (hGLe : g + m * L ≤ heap) (hLLe : l + m * L ≤ heap)
    (hETLe : edgeThresholds + intCap ≤ heap) (hERLe : edgeRecords + intCap ≤ heap)
    (hMutDisj : edgeThresholds + intCap ≤ edgeRecords ∨ edgeRecords + intCap ≤ edgeThresholds)
    (hRODisj :
      (∀ j < (batchWords U_int).length, ¬ InRefreshMutable edgeThresholds edgeRecords intCap (uIntBuf + j)) ∧
      (∀ j < dynGraphSize n rootECap, ¬ InRefreshMutable edgeThresholds edgeRecords intCap (rootGraph + j)) ∧
      (∀ j < m, ¬ InRefreshMutable edgeThresholds edgeRecords intCap (forward + j)) ∧
      (∀ j < intCap, ¬ InRefreshMutable edgeThresholds edgeRecords intCap (inverse + j)) ∧
      (∀ j < m * L, ¬ InRefreshMutable edgeThresholds edgeRecords intCap (g + j)) ∧
      (∀ j < m * L, ¬ InRefreshMutable edgeThresholds edgeRecords intCap (l + j)))
    (hDelCap : ∀ u ∈ U_int, match u with | .delete ei => ei < rootECap | _ => True)
    (hz : ZeroFrom mem heap)
    (hRoom : heap + 3 * L + U_int.length * wireRefreshOneSpace L < 2 ^ w)
    (hw16 : 16 < 2 ^ w) :
    let ε := (((2 : ℤ) ^ (P - epsExp) : ℤ) : ℝ) / (2 : ℝ) ^ P
    ∃ nextHeap out cost,
      Runs w p ω (wireRefreshAccountsBody shift negate refreshOneProc)
        (startState [root, uIntBuf, g, l, heap] mem pos) (.returned nextHeap) out cost ∧
      heap + 3 * L ≤ nextHeap ∧
      nextHeap ≤ heap + 3 * L + U_int.length * wireRefreshOneSpace L ∧
      cost ≤ U_int.length * (wireRefreshOneCost L + 120) + 71 * L + 210 ∧
      ZeroFrom out.mem nextHeap ∧
      (∀ a < heap, ¬ InRefreshMutable edgeThresholds edgeRecords intCap a → out.mem a = mem a) ∧
      (∀ ei < intCap, (¬ ∃ ei_old ∈ G0.E, .delete ei_old ∈ U_int ∧ e2i' (i2e' ei_old) = ei) →
        out.mem (edgeThresholds + ei) = mem (edgeThresholds + ei) ∧
        out.mem (edgeRecords + ei) = mem (edgeRecords + ei)) ∧
      (∀ ei_old ∈ G0.E, .delete ei_old ∈ U_int →
        let e := i2e' ei_old
        let ei_new := e2i' e
        let thrNew := detectorThreshold P ε ((lNew e : ℝ) / (2 : ℝ) ^ P)
        let newVal : PathEdgeValue :=
          { forward := true, gradient := gNew e, length := (lNew e : ℤ),
            flow := (oldVal ei_old).flow, detector := acc ei_old - thrNew }
        heap + 3 * L ≤ out.mem (edgeThresholds + ei_new) ∧
        out.mem (edgeThresholds + ei_new) + L ≤ nextHeap ∧
        heap + 3 * L ≤ out.mem (edgeRecords + ei_new) ∧
        out.mem (edgeRecords + ei_new) + (2 + 4 * L) ≤ nextHeap ∧
        PathIntAt out.mem (out.mem (edgeThresholds + ei_new)) 4 L thrNew ∧
        PathEdgeAt out.mem (out.mem (edgeRecords + ei_new)) 4 L (some newVal)) ∧
      (∀ ei₁ ∈ G0.E, ∀ ei₂ ∈ G0.E, .delete ei₁ ∈ U_int → .delete ei₂ ∈ U_int →
        let n1 := e2i' (i2e' ei₁)
        let n2 := e2i' (i2e' ei₂)
        (ei₁ ≠ ei₂ →
          out.mem (edgeRecords + n1) + (2 + 4 * L) ≤ out.mem (edgeRecords + n2) ∨
          out.mem (edgeRecords + n2) + (2 + 4 * L) ≤ out.mem (edgeRecords + n1)) ∧
        (out.mem (edgeThresholds + n1) + L ≤ out.mem (edgeRecords + n2) ∨
          out.mem (edgeRecords + n2) + (2 + 4 * L) ≤ out.mem (edgeThresholds + n1))) := by
  classical
  dsimp only
  set ε : ℝ := (((2 : ℤ) ^ (P - epsExp) : ℤ) : ℝ) / (2 : ℝ) ^ P
  set sp : ℕ := wireRefreshOneSpace L
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hEpsPos : (0 : ℝ) < ε := by dsimp only [ε]; positivity
  have hLenB0 : mem uIntBuf = U_int.length := by
    simpa [batchWords] using hBatch 0 (by simp [batchWords])
  have hULenW : U_int.length < 2 ^ w := by
    have h2 : ∀ Lst : List Update, (∀ u ∈ Lst, IsEdgeUpdate u) →
        2 * Lst.length ≤ (Lst.flatMap updateWords).length := by
      intro Lst hL
      induction Lst with
      | nil => simp
      | cons u rest ih =>
        have hu := hL u List.mem_cons_self
        have hr := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
        cases u with
        | insert _ _ _ => simp only [List.flatMap_cons, List.length_append, updateWords, List.length_cons, List.length_nil]; omega
        | delete _ => simp only [List.flatMap_cons, List.length_append, updateWords, List.length_cons, List.length_nil]; omega
        | split _ _ _ _ => exact hu.elim
    have h2' := h2 U_int hEdgeOnly
    simp only [batchWords, List.length_cons] at hBatchLe; omega
  obtain ⟨sA, cA, rA, hcA, hA60, hA61, hA62, hA63, _, hA65, hA66, hA67, hA68, hA69, hA70,
    _, _, _, hA77, hA95, hA99, hANegEps, hzA, hAFr⟩ :=
    wireRefreshAccountsSetup_runs (w := w) (root := root) (uIntBuf := uIntBuf) (g := g) (l := l)
      (heap := heap) (pos := pos) (p := p) (ω := ω)
      hshift hneg hRoot hLmem hPmem hEpsMem hDG0 hLpos hPword hle
      hfitPos hRootLe hHandleLe hRGLe hz (by omega) hw16
  let sB := { sA with regs := Function.update sA.regs 78 U_int.length }
  let sC := { sB with regs := Function.update sB.regs 79 (uIntBuf + 1) }
  have rB : Runs w p ω (.assign 78 (.load (.reg 61))) sA .normal sB 3 :=
    runs_assign_iff.mpr ⟨U_int.length, by
      simp [Expr.eval, hA61, hAFr uIntBuf (by simp [batchWords] at hBatchLe; omega), hLenB0], rfl, rfl, rfl⟩
  have rC : Runs w p ω (.assign 79 (.bin .add (.reg 61) (.const 1))) sB .normal sC 4 :=
    runs_assign_iff.mpr ⟨uIntBuf + 1, by
      simp [Expr.eval, BinOp.eval, sB, hA61, hw1, show uIntBuf + 1 < 2 ^ w by simp [batchWords] at hBatchLe; omega],
      rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) : Prop :=
    ∃ curH,
      s.regs 60 = root ∧ s.regs 61 = uIntBuf ∧ s.regs 62 = g ∧ s.regs 63 = l ∧
      s.regs 65 = forward ∧ s.regs 66 = inverse ∧ s.regs 67 = L ∧ s.regs 68 = P ∧
      s.regs 69 = edgeThresholds ∧ s.regs 70 = edgeRecords ∧ s.regs 77 = rootGraph + 4 + 7 * n ∧
      s.regs 78 = U_int.length ∧ s.regs 79 = uIntBuf + 1 + edgeRecOff U_int i ∧
      s.regs 80 = i ∧ s.regs 95 = heap + 2 * L ∧ s.regs 99 = curH ∧
      heap + 3 * L ≤ curH ∧ curH ≤ heap + 3 * L + i * sp ∧
      ZeroFrom s.mem curH ∧
      PathIntAt s.mem (heap + 2 * L) 4 L (-((2 : ℤ) ^ (P - epsExp))) ∧
      (∀ a < heap, ¬ InRefreshMutable edgeThresholds edgeRecords intCap a → s.mem a = mem a) ∧
      (∀ ei < intCap, (¬ ∃ j, ∃ hj : j < U_int.length, j < i ∧ ∃ ei_old ∈ G0.E,
          U_int[j] = .delete ei_old ∧ e2i' (i2e' ei_old) = ei) →
        s.mem (edgeThresholds + ei) = mem (edgeThresholds + ei) ∧
        s.mem (edgeRecords + ei) = mem (edgeRecords + ei)) ∧
      (∀ j < i, ∀ hj : j < U_int.length, ∀ ei_old ∈ G0.E, U_int[j] = .delete ei_old →
        let e := i2e' ei_old
        let ei_new := e2i' e
        let thrNew := detectorThreshold P ε ((lNew e : ℝ) / (2 : ℝ) ^ P)
        let newVal : PathEdgeValue :=
          { forward := true, gradient := gNew e, length := (lNew e : ℤ),
            flow := (oldVal ei_old).flow, detector := acc ei_old - thrNew }
        heap + 3 * L ≤ s.mem (edgeThresholds + ei_new) ∧
        s.mem (edgeThresholds + ei_new) + L ≤ curH ∧
        heap + 3 * L ≤ s.mem (edgeRecords + ei_new) ∧
        s.mem (edgeRecords + ei_new) + (2 + 4 * L) ≤ curH ∧
        PathIntAt s.mem (s.mem (edgeThresholds + ei_new)) 4 L thrNew ∧
        PathEdgeAt s.mem (s.mem (edgeRecords + ei_new)) 4 L (some newVal)) ∧
      (∀ j₁ < i, ∀ hj₁ : j₁ < U_int.length, ∀ e₁ ∈ G0.E, U_int[j₁] = .delete e₁ →
       ∀ j₂ < i, ∀ hj₂ : j₂ < U_int.length, ∀ e₂ ∈ G0.E, U_int[j₂] = .delete e₂ →
        let n1 := e2i' (i2e' e₁)
        let n2 := e2i' (i2e' e₂)
        (e₁ ≠ e₂ →
          s.mem (edgeRecords + n1) + (2 + 4 * L) ≤ s.mem (edgeRecords + n2) ∨
          s.mem (edgeRecords + n2) + (2 + 4 * L) ≤ s.mem (edgeRecords + n1)) ∧
        (s.mem (edgeThresholds + n1) + L ≤ s.mem (edgeRecords + n2) ∨
          s.mem (edgeRecords + n2) + (2 + 4 * L) ≤ s.mem (edgeThresholds + n1)))
  let stepCost := wireRefreshOneCost L + 110
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 80) (lo := .const 0) (hi := .reg 78)
    (P := fun s => s = sC) (Inv := Inv) (fun _ => stepCost) 0 U_int.length (Nat.zero_le _) hw1
    (fun _ => hULenW)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], heap + 3 * L,
        by simp [sC, sB, hA60], by simp [sC, sB, hA61], by simp [sC, sB, hA62], by simp [sC, sB, hA63],
        by simp [sC, sB, hA65], by simp [sC, sB, hA66], by simp [sC, sB, hA67], by simp [sC, sB, hA68],
        by simp [sC, sB, hA69], by simp [sC, sB, hA70], by simp [sC, sB, hA77], by simp [sC, sB],
        by simp [sC, edgeRecOff], by simp, by simp [sC, sB, hA95], by simp [sC, sB, hA99],
        le_rfl, by simp, hzA, hANegEps, fun a ha _ => hAFr a ha,
        fun ei hei _ => ⟨hAFr _ (by omega), hAFr _ (by omega)⟩,
        fun j hj _ => absurd hj (Nat.not_lt_zero _),
        fun j hj _ => absurd hj (Nat.not_lt_zero _)⟩)
    (fun _ _ _ _ h => by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h80, _⟩ := h; exact h80)
    (fun _ _ _ _ h => by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h78, _⟩ := h; simp [Expr.eval, h78])
    (fun i _ hi => by
      intro s ω' hI
      obtain ⟨curH, h60, h61, h62, h63, h65, h66, h67, h68, h69, h70, h77,
        h78, h79, h80, h95, h99, hHLo, hHHi, hzS, hNegEpsS, hFrS, hUnchS, hDoneS, hDisjS⟩ := hI
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
        rw [show uIntBuf + 1 + edgeRecOff U_int i = uIntBuf + (1 + edgeRecOff U_int i) by omega,
            hFrS _ (by omega) (hRODisj.1 (1 + edgeRecOff U_int i) (by omega))]
        simpa [Nat.add_assoc] using hRec0.1
      let liveThen : Stmt :=
        .assign 83 (.load (.bin .add (.reg 66) (.reg 82))) ;;
        .assign 84 (.load (.bin .add (.reg 65) (.reg 83))) ;;
        .assign 85 (.load (.bin .add (.reg 70) (.reg 82))) ;;
        .assign 86 (.load (.bin .add (.reg 69) (.reg 82))) ;;
        .call 99 refreshOneProc
          [.reg 85, .reg 86,
           .bin .add (.reg 62) (.bin .mul (.reg 83) (.reg 67)),
           .bin .add (.reg 63) (.bin .mul (.reg 83) (.reg 67)),
           .reg 95, .reg 67, .reg 68, .reg 99] ;;
        .assign 87 (.load (.bin .sub (.reg 99) (.const 3))) ;;
        .assign 88 (.load (.bin .sub (.reg 99) (.const 2))) ;;
        .store (.bin .add (.reg 69) (.reg 84)) (.reg 87) ;;
        .store (.bin .add (.reg 70) (.reg 84)) (.reg 88)
      let delElse : Stmt :=
        .assign 82 (.load (.bin .add (.reg 79) (.const 1))) ;;
        .assign 79 (.bin .add (.reg 79) (.const 2)) ;;
        .cond (.load (.bin .add (.reg 77) (.reg 82))) liveThen .nop
      cases hUi : U_int[i] with
      | split _ _ _ _ => rw [hUi] at huE; exact huE.elim
      | insert ei u v =>
        have hTagVal : s.mem (uIntBuf + 1 + edgeRecOff U_int i) = 0 := by rw [hTagMem]; simp [hUi, updateWords]
        have hOffNext : edgeRecOff U_int (i + 1) = edgeRecOff U_int i + 4 := by
          rw [edgeRecOff_succ hi, hUi]; simp [updateWords]
        have hNextW : uIntBuf + 1 + edgeRecOff U_int i + 4 < 2 ^ w := by
          have := (edgeBatch_rec_word hBatch hi (j := 3) (by simp [hUi, updateWords])).2; omega
        let t1 := { s with regs := Function.update s.regs 81 0 }
        let t2 := { t1 with regs := Function.update t1.regs 79 (uIntBuf + 1 + edgeRecOff U_int (i + 1)) }
        have rt1 : Runs w p ω' (.assign 81 (.load (.reg 79))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h79, hTagVal], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 79 (.bin .add (.reg 79) (.const 4))) t1 .normal t2 4 :=
          runs_assign_iff.mpr ⟨uIntBuf + 1 + edgeRecOff U_int (i + 1), by
            simp only [Expr.eval, BinOp.eval, t1, h79, hw4, hNextW, ↓reduceIte, Option.some.injEq,
              Function.update_of_ne (by decide : (79 : ℕ) ≠ 81)]; omega, rfl, rfl, rfl⟩
        have rCond : Runs w p ω' (.cond (.bin .eq (.reg 81) (.const 0)) (.assign 79 (.bin .add (.reg 79) (.const 4))) delElse)
            t1 .normal t2 8 :=
          runs_cond_iff.mpr ⟨1, 4, by simp [Expr.eval, BinOp.eval, t1, hw1], by simpa using rt2, by simp [Expr.size]⟩
        have hInvN : Inv (i + 1) { t2 with regs := Function.update t2.regs 80 (i + 1) } :=
          ⟨curH, by simp [t2, t1, h60], by simp [t2, t1, h61], by simp [t2, t1, h62],
            by simp [t2, t1, h63], by simp [t2, t1, h65], by simp [t2, t1, h66], by simp [t2, t1, h67],
            by simp [t2, t1, h68], by simp [t2, t1, h69], by simp [t2, t1, h70], by simp [t2, t1, h77],
            by simp [t2, t1, h78], by simp [t2], by simp, by simp [t2, t1, h95], by simp [t2, t1, h99],
            hHLo, hHHi.trans (Nat.add_le_add_left (Nat.mul_le_mul_right sp (Nat.le_succ i)) _),
            hzS, hNegEpsS, hFrS,
            fun ei hei hni => hUnchS ei hei (fun ⟨j, hjLt, hj, eio, heio, hUj, hEq⟩ =>
              hni ⟨j, hjLt, Nat.lt_succ_of_lt hj, eio, heio, hUj, hEq⟩),
            fun j hj hjLt eio heio hUj => by
              by_cases hji : j = i
              · subst hji; rw [hUi] at hUj; cases hUj
              · exact hDoneS j (by omega) hjLt eio heio hUj,
            fun j₁ hj₁ hj₁Lt e₁ he₁ hU₁ j₂ hj₂ hj₂Lt e₂ he₂ hU₂ => by
              have h1 : j₁ < i := by
                by_contra h; have heq : j₁ = i := by omega
                subst heq; rw [hUi] at hU₁; cases hU₁
              have h2 : j₂ < i := by
                by_contra h; have heq : j₂ = i := by omega
                subst heq; rw [hUi] at hU₂; cases hU₂
              exact hDisjS j₁ h1 hj₁Lt e₁ he₁ hU₁ j₂ h2 hj₂Lt e₂ he₂ hU₂⟩
        refine ⟨.normal, t2, 3 + 8 + 1, runs_seq_iff.mpr (Or.inr ⟨t1, 3, 8, rt1, rCond, rfl⟩),
          ⟨hInvN, by simp [t2, t1, h80]⟩, by dsimp [stepCost]; omega⟩
      | delete ei_old =>
        have hTagVal : s.mem (uIntBuf + 1 + edgeRecOff U_int i) = 1 := by rw [hTagMem]; simp [hUi, updateWords]
        have hOffNext : edgeRecOff U_int (i + 1) = edgeRecOff U_int i + 2 := by
          rw [edgeRecOff_succ hi, hUi]; simp [updateWords]
        have hRec1 := edgeBatch_rec_word hBatch hi (j := 1) (by simp [hUi, updateWords])
        have hEiOldMem : s.mem (uIntBuf + 1 + edgeRecOff U_int i + 1) = ei_old := by
          rw [show uIntBuf + 1 + edgeRecOff U_int i + 1 = uIntBuf + (1 + edgeRecOff U_int i + 1) by omega,
              hFrS _ (by have := hRec1.2; omega) (hRODisj.1 (1 + edgeRecOff U_int i + 1) (by have := hRec1.2; omega))]
          simpa [hUi, updateWords, Nat.add_assoc] using hRec1.1
        have hEiOldECap : ei_old < rootECap := by
          have := hDelCap (.delete ei_old) (hUi ▸ List.getElem_mem hi); simpa using this
        have hEPresOff : 4 + 7 * n + ei_old < dynGraphSize n rootECap := by unfold dynGraphSize; omega
        have hEPresAt : s.mem (rootGraph + 4 + 7 * n + ei_old) = if ei_old ∈ G0.E then 1 else 0 := by
          rw [show rootGraph + 4 + 7 * n + ei_old = rootGraph + (4 + 7 * n + ei_old) by omega,
              hFrS _ (by omega) (hRODisj.2.1 _ hEPresOff)]
          have hP := hDG0.2.2.2.2.2.2.2.2.2.2.2.1 ei_old hEiOldECap
          simpa [dgEPresBase, Nat.add_assoc] using hP
        let t1 := { s with regs := Function.update s.regs 81 1 }
        let t2 := { t1 with regs := Function.update t1.regs 82 ei_old }
        let t3 := { t2 with regs := Function.update t2.regs 79 (uIntBuf + 1 + edgeRecOff U_int (i + 1)) }
        have rt1 : Runs w p ω' (.assign 81 (.load (.reg 79))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h79, hTagVal], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 82 (.load (.bin .add (.reg 79) (.const 1)))) t1 .normal t2 5 :=
          runs_assign_iff.mpr ⟨ei_old, by
            simp [Expr.eval, BinOp.eval, t1, h79, hw1, show uIntBuf + 1 + edgeRecOff U_int i + 1 < 2 ^ w by
              have := hRec1.2; omega, hEiOldMem], rfl, rfl, rfl⟩
        have rt3 : Runs w p ω' (.assign 79 (.bin .add (.reg 79) (.const 2))) t2 .normal t3 4 :=
          runs_assign_iff.mpr ⟨uIntBuf + 1 + edgeRecOff U_int (i + 1), by
            simp only [Expr.eval, BinOp.eval, t2, t1, h79, show 2 < 2 ^ w by omega,
              show uIntBuf + 1 + edgeRecOff U_int i + 2 < 2 ^ w by have := hRec1.2; omega, ↓reduceIte,
              Option.some.injEq, Function.update_of_ne (by decide : (79 : ℕ) ≠ 82),
              Function.update_of_ne (by decide : (79 : ℕ) ≠ 81)]; omega, rfl, rfl, rfl⟩
        by_cases hLive : ei_old ∈ G0.E
        · obtain ⟨hOldInt, _, heLtM, hNewInt, hlPos, hNewNeOld, hNewInj, hOldFwd, hOldRec, hOldThr,
            hOldDet, hGAt, hLAt, hFitNegThr, hFitPosThr, hFitAcc, hFitDetNew, hRecLe, hThrLe,
            hRecDisj, hThrDisj⟩ := hDelInfo ei_old hLive (hUi ▸ List.getElem_mem hi)
          set e := i2e' ei_old
          set ei_new := e2i' e
          set thrNew := detectorThreshold P ε ((lNew e : ℝ) / (2 : ℝ) ^ P)
          set newVal : PathEdgeValue :=
            { forward := true, gradient := gNew e, length := (lNew e : ℤ),
              flow := (oldVal ei_old).flow, detector := acc ei_old - thrNew }
          have hOldNotWritten : ¬ ∃ j, ∃ hj : j < U_int.length, j < i ∧ ∃ ei2 ∈ G0.E,
              U_int[j] = .delete ei2 ∧ e2i' (i2e' ei2) = ei_old := by
            rintro ⟨j, hjLt, _, ei2, hei2, hUj, hEq⟩
            exact (hDelInfo ei2 hei2 (hUj ▸ List.getElem_mem hjLt)).2.2.2.2.2.1 ei_old hLive
              (hUi ▸ List.getElem_mem hi) hEq
          have hOldETEq : s.mem (edgeThresholds + ei_old) = mem (edgeThresholds + ei_old) :=
            (hUnchS ei_old hOldInt hOldNotWritten).1
          have hOldEREq : s.mem (edgeRecords + ei_old) = mem (edgeRecords + ei_old) :=
            (hUnchS ei_old hOldInt hOldNotWritten).2
          have hInvEq : s.mem (inverse + ei_old) = e := by
            rw [hFrS _ (by omega) (hRODisj.2.2.2.1 ei_old hOldInt)]; exact hFresh.2.2 ei_old hOldInt
          have hFwdEq : s.mem (forward + e) = ei_new := by
            rw [hFrS _ (by omega) (hRODisj.2.2.1 e heLtM)]; exact hFresh.2.1 e heLtM
          let oldRecPtr := mem (edgeRecords + ei_old)
          let oldThrPtr := mem (edgeThresholds + ei_old)
          let t4 := { t3 with regs := Function.update t3.regs 83 e }
          let t5 := { t4 with regs := Function.update t4.regs 84 ei_new }
          let t6 := { t5 with regs := Function.update t5.regs 85 oldRecPtr }
          let t7 := { t6 with regs := Function.update t6.regs 86 oldThrPtr }
          have rt4 : Runs w p ω' (.assign 83 (.load (.bin .add (.reg 66) (.reg 82)))) t3 .normal t4 5 :=
            runs_assign_iff.mpr ⟨e, by simp [Expr.eval, BinOp.eval, t3, t2, t1, h66,
              show inverse + ei_old < 2 ^ w by omega, hInvEq], rfl, rfl, rfl⟩
          have rt5 : Runs w p ω' (.assign 84 (.load (.bin .add (.reg 65) (.reg 83)))) t4 .normal t5 5 :=
            runs_assign_iff.mpr ⟨ei_new, by simp [Expr.eval, BinOp.eval, t4, t3, t2, t1, h65,
              show forward + e < 2 ^ w by omega, hFwdEq], rfl, rfl, rfl⟩
          have rt6 : Runs w p ω' (.assign 85 (.load (.bin .add (.reg 70) (.reg 82)))) t5 .normal t6 5 :=
            runs_assign_iff.mpr ⟨oldRecPtr, by simp [Expr.eval, BinOp.eval, t5, t4, t3, t2, t1, h70,
              show edgeRecords + ei_old < 2 ^ w by omega, hOldEREq, oldRecPtr], rfl, rfl, rfl⟩
          have rt7 : Runs w p ω' (.assign 86 (.load (.bin .add (.reg 69) (.reg 82)))) t6 .normal t7 5 :=
            runs_assign_iff.mpr ⟨oldThrPtr, by simp [Expr.eval, BinOp.eval, t6, t5, t4, t3, t2, t1, h69,
              show edgeThresholds + ei_old < 2 ^ w by omega, hOldETEq, oldThrPtr], rfl, rfl, rfl⟩
          have hRoomI : curH + sp < 2 ^ w := by
            have hm : (i + 1) * sp ≤ U_int.length * sp := Nat.mul_le_mul_right sp (Nat.succ_le_of_lt hi)
            rw [Nat.succ_mul] at hm; omega
          have heL : e * L + L ≤ m * L := by
            simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLtM)
          have hOldRecS : PathEdgeAt t7.mem oldRecPtr 4 L (some (oldVal ei_old)) :=
            hOldRec.congr (fun x hxlo hxhi => by
              have hEq : x = oldRecPtr + (x - oldRecPtr) := by omega
              rw [hEq]; exact hFrS _ (by omega) (hRecDisj _ (by omega)))
          have hOldThrS : PathIntAt t7.mem oldThrPtr 4 L (oldThr ei_old) :=
            hOldThr.congr (fun j hj => hFrS _ (by omega) (hThrDisj j hj))
          have hGAtS : PathIntAt t7.mem (g + e * L) 4 L (gNew e) :=
            hGAt.congr (fun j hj => by
              rw [show g + e * L + j = g + (e * L + j) by omega]
              exact hFrS _ (by omega) (hRODisj.2.2.2.2.1 _ (by omega)))
          have hLAtS : PathIntAt t7.mem (l + e * L) 4 L (lNew e : ℤ) :=
            hLAt.congr (fun j hj => by
              rw [show l + e * L + j = l + (e * L + j) by omega]
              exact hFrS _ (by omega) (hRODisj.2.2.2.2.2 _ (by omega)))
          obtain ⟨outRef, cRef, rRef, hcRef, hThrP, hRecP, _, hThrNewAt, hRecNewAt, hzRef, hFrRef⟩ :=
            wireRefreshOneAccountBody_runs (w := w) (divide := divide) (add := add) (sub := sub)
              (negate := negate) (copy := copy) (isNeg := isNeg) (oldRecPtr := oldRecPtr)
              (oldThrPtr := oldThrPtr) (gPtr := g + e * L) (lPtr := l + e * L)
              (negEpsPtr := heap + 2 * L) (L := L) (P := P) (heap := curH) (pos := t7.pos)
              (p := p) (ω := ω') (mem := t7.mem) (oldVal := oldVal ei_old)
              (epsInt := (2 : ℤ) ^ (P - epsExp)) (gNewInt := gNew e) (oldThr := oldThr ei_old)
              (acc := acc ei_old) (lNewInt := lNew e)
              hdiv hadd hsub hneg hcopy hisNeg hPdiv hPword hLpos hlPos
              (by omega) (by omega) (by omega) (by omega) (by omega)
              hOldRecS hOldFwd hOldThrS hOldDet hNegEpsS hGAtS hLAtS hEpsPos
              hFitNegThr hFitPosThr hFitAcc hFitDetNew hzS hRoomI hw4
          let nextH := curH + sp
          let thrNewPtr := curH + Num.fixedDivideSpace L
          let recNewPtr := thrNewPtr + 4 * L
          let t8 : State := { regs := Function.update t7.regs 99 nextH, mem := outRef.mem, pos := outRef.pos }
          have rt8 : Runs w p ω'
              (.call 99 refreshOneProc
                [.reg 85, .reg 86,
                 .bin .add (.reg 62) (.bin .mul (.reg 83) (.reg 67)),
                 .bin .add (.reg 63) (.bin .mul (.reg 83) (.reg 67)),
                 .reg 95, .reg 67, .reg 68, .reg 99])
              t7 .normal t8 (16 + cRef + 1) :=
            runs_call_iff.mpr ⟨[oldRecPtr, oldThrPtr, g + e * L, l + e * L, heap + 2 * L, L, P, curH],
              wireRefreshOneAccountBody divide add sub negate copy isNeg, .returned nextH, outRef, cRef,
              by simp [evalArgs, Expr.eval, BinOp.eval, t7, t6, t5, t4, t3, t2, t1, h62, h63, h67,
                h68, h95, h99, show e * L < 2 ^ w by omega, show g + e * L < 2 ^ w by omega,
                show l + e * L < 2 ^ w by omega],
              hRefProc, rRef, rfl, rfl, by simp [argsSize, Expr.size]⟩
          let t9 := { t8 with regs := Function.update t8.regs 87 thrNewPtr }
          let t10 := { t9 with regs := Function.update t9.regs 88 recNewPtr }
          let t11 := { t10 with mem := Function.update t10.mem (edgeThresholds + ei_new) thrNewPtr }
          let t12 := { t11 with mem := Function.update t11.mem (edgeRecords + ei_new) recNewPtr }
          have hSpGe3 : 3 ≤ sp := by unfold sp wireRefreshOneSpace; omega
          have rt9 : Runs w p ω' (.assign 87 (.load (.bin .sub (.reg 99) (.const 3)))) t8 .normal t9 5 :=
            runs_assign_iff.mpr ⟨thrNewPtr, by simp [Expr.eval, BinOp.eval, t8, show 3 < 2 ^ w by omega,
              show nextH - 3 < 2 ^ w by omega, nextH, sp, thrNewPtr, hThrP], rfl, rfl, rfl⟩
          have rt10 : Runs w p ω' (.assign 88 (.load (.bin .sub (.reg 99) (.const 2)))) t9 .normal t10 5 :=
            runs_assign_iff.mpr ⟨recNewPtr, by simp [Expr.eval, BinOp.eval, t9, t8, show 2 < 2 ^ w by omega,
              show nextH - 2 < 2 ^ w by omega, nextH, sp, recNewPtr, thrNewPtr, hRecP], rfl, rfl, rfl⟩
          have rt11 : Runs w p ω' (.store (.bin .add (.reg 69) (.reg 84)) (.reg 87)) t10 .normal t11 5 :=
            runs_store_iff.mpr ⟨edgeThresholds + ei_new, thrNewPtr, by
              simp [Expr.eval, BinOp.eval, t10, t9, t8, t7, t6, t5, t4, t3, t2, t1, h69,
                show edgeThresholds + ei_new < 2 ^ w by omega],
              by simp [Expr.eval, t10, t9], rfl, rfl, rfl⟩
          have rt12 : Runs w p ω' (.store (.bin .add (.reg 70) (.reg 84)) (.reg 88)) t11 .normal t12 5 :=
            runs_store_iff.mpr ⟨edgeRecords + ei_new, recNewPtr, by
              simp [Expr.eval, BinOp.eval, t11, t10, t9, t8, t7, t6, t5, t4, t3, t2, t1, h70,
                show edgeRecords + ei_new < 2 ^ w by omega],
              by simp [Expr.eval, t11, t10], rfl, rfl, rfl⟩
          have h12_above (a : ℕ) (ha : heap ≤ a) : t12.mem a = outRef.mem a := by
            simp only [t12, t11, t10, t9, t8,
              Function.update_of_ne (by omega : a ≠ edgeRecords + ei_new),
              Function.update_of_ne (by omega : a ≠ edgeThresholds + ei_new)]
          have h12_eq_s (a : ℕ) (ha : a < heap) (hne1 : a ≠ edgeThresholds + ei_new)
              (hne2 : a ≠ edgeRecords + ei_new) : t12.mem a = s.mem a := by
            simp only [t12, t11, t10, t9, t8, Function.update_of_ne hne2, Function.update_of_ne hne1]
            exact hFrRef a (lt_of_lt_of_le ha (by omega))
          let cLive := 5 + (5 + (5 + (5 + ((16 + cRef + 1) + (5 + (5 + (5 + 5 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1
          have rLiveBody : Runs w p ω' liveThen t3 .normal t12 cLive :=
            runs_seq_iff.mpr (Or.inr ⟨t4, 5, _, rt4,
            runs_seq_iff.mpr (Or.inr ⟨t5, 5, _, rt5,
            runs_seq_iff.mpr (Or.inr ⟨t6, 5, _, rt6,
            runs_seq_iff.mpr (Or.inr ⟨t7, 5, _, rt7,
            runs_seq_iff.mpr (Or.inr ⟨t8, 16 + cRef + 1, _, rt8,
            runs_seq_iff.mpr (Or.inr ⟨t9, 5, _, rt9,
            runs_seq_iff.mpr (Or.inr ⟨t10, 5, _, rt10,
            runs_seq_iff.mpr (Or.inr ⟨t11, 5, 5, rt11, rt12, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
            rfl⟩), rfl⟩), rfl⟩), rfl⟩)
          have rCondLive : Runs w p ω' (.cond (.load (.bin .add (.reg 77) (.reg 82))) liveThen .nop)
              t3 .normal t12 (4 + cLive + 1) :=
            runs_cond_iff.mpr ⟨1, cLive, by
              simp [Expr.eval, BinOp.eval, t3, t2, t1, h77, show rootGraph + 4 + 7 * n + ei_old < 2 ^ w by omega,
                hEPresAt, hLive], by simpa using rLiveBody, by simp [Expr.size]⟩
          have rElse : Runs w p ω' delElse t1 .normal t12 (5 + (4 + (4 + cLive + 1) + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, rt2, runs_seq_iff.mpr (Or.inr ⟨t3, 4, 4 + cLive + 1, rt3, rCondLive, rfl⟩), rfl⟩)
          have rOuter : Runs w p ω' (.cond (.bin .eq (.reg 81) (.const 0)) (.assign 79 (.bin .add (.reg 79) (.const 4))) delElse)
              t1 .normal t12 (3 + (5 + (4 + (4 + cLive + 1) + 1) + 1) + 1) :=
            runs_cond_iff.mpr ⟨0, 5 + (4 + (4 + cLive + 1) + 1) + 1, by simp [Expr.eval, BinOp.eval, t1, show (0 : ℕ) < 2 ^ w by omega],
              by simpa using rElse, by simp [Expr.size]⟩
          have h12_r (r : ℕ) (hr : r ≠ 79 ∧ r ≠ 81 ∧ r ≠ 82 ∧ r ≠ 83 ∧ r ≠ 84 ∧ r ≠ 85 ∧
              r ≠ 86 ∧ r ≠ 87 ∧ r ≠ 88 ∧ r ≠ 99) : t12.regs r = s.regs r := by
            simp [t12, t11, t10, t9, t8, t7, t6, t5, t4, t3, t2, t1,
              Function.update_of_ne hr.2.2.2.2.2.2.2.2.1, Function.update_of_ne hr.2.2.2.2.2.2.2.1,
              Function.update_of_ne hr.2.2.2.2.2.2.2.2.2, Function.update_of_ne hr.2.2.2.2.2.2.1,
              Function.update_of_ne hr.2.2.2.2.2.1, Function.update_of_ne hr.2.2.2.2.1,
              Function.update_of_ne hr.2.2.2.1, Function.update_of_ne hr.1,
              Function.update_of_ne hr.2.2.1, Function.update_of_ne hr.2.1]
          have hET12 : t12.mem (edgeThresholds + ei_new) = thrNewPtr := by
            simp [t12, t11, Function.update_of_ne (by rcases hMutDisj with h | h <;> omega :
              edgeThresholds + ei_new ≠ edgeRecords + ei_new)]
          have hER12 : t12.mem (edgeRecords + ei_new) = recNewPtr := by simp [t12]
          have hThrSp : thrNewPtr + L ≤ nextH := by dsimp [thrNewPtr, nextH, sp, wireRefreshOneSpace]; omega
          have hRecSp : recNewPtr + (2 + 4 * L) ≤ nextH := by dsimp [recNewPtr, thrNewPtr, nextH, sp, wireRefreshOneSpace]; omega
          have hInvN : Inv (i + 1) { t12 with regs := Function.update t12.regs 80 (i + 1) } := by
            refine ⟨nextH,
              by simp [h12_r 60 (by omega), h60], by simp [h12_r 61 (by omega), h61],
              by simp [h12_r 62 (by omega), h62], by simp [h12_r 63 (by omega), h63],
              by simp [h12_r 65 (by omega), h65], by simp [h12_r 66 (by omega), h66],
              by simp [h12_r 67 (by omega), h67], by simp [h12_r 68 (by omega), h68],
              by simp [h12_r 69 (by omega), h69], by simp [h12_r 70 (by omega), h70],
              by simp [h12_r 77 (by omega), h77], by simp [h12_r 78 (by omega), h78],
              by simp [t12, t11, t10, t9, t8, t7, t6, t5, t4, t3], by simp,
              by simp [h12_r 95 (by omega), h95], by simp [t12, t11, t10, t9, t8],
              by dsimp only [nextH]; omega,
              by dsimp only [nextH]; exact (Nat.add_le_add_right hHHi sp).trans_eq (by ring),
              fun a ha => by rw [h12_above a (by omega)]; exact hzRef a ha,
              hNegEpsS.congr (fun j hj => by rw [h12_above _ (by omega)]; exact hFrRef _ (by omega)),
              fun a ha hNotM => (h12_eq_s a ha
                (fun h => hNotM (Or.inl (by omega))) (fun h => hNotM (Or.inr (by omega)))).trans (hFrS a ha hNotM),
              ?_, ?_, ?_⟩
            · intro ei hei hni
              have hne : ei ≠ ei_new := fun h => hni ⟨i, hi, Nat.lt_succ_self i, ei_old, hLive, hUi, h.symm⟩
              have hPrev := hUnchS ei hei (fun ⟨j, hjLt, hj, eio, heio, hUj, hEq⟩ =>
                hni ⟨j, hjLt, Nat.lt_succ_of_lt hj, eio, heio, hUj, hEq⟩)
              exact ⟨(h12_eq_s _ (by omega) (by omega) (by rcases hMutDisj with h | h <;> omega)).trans hPrev.1,
                (h12_eq_s _ (by omega) (by rcases hMutDisj with h | h <;> omega) (by omega)).trans hPrev.2⟩
            · intro j hj hjLt eio heio hUj
              by_cases hji : j = i
              · subst hji; rw [hUi] at hUj; injection hUj with hEq; subst hEq
                refine ⟨by rw [hET12]; dsimp [thrNewPtr]; omega, by rw [hET12]; exact hThrSp,
                  by rw [hER12]; dsimp [recNewPtr, thrNewPtr]; omega, by rw [hER12]; exact hRecSp,
                  by rw [hET12]; exact hThrNewAt.congr (fun k hk => h12_above _ (by dsimp [thrNewPtr]; omega)),
                  by rw [hER12]; exact hRecNewAt.congr (fun x hxlo hxhi => h12_above x (by omega))⟩
              · have hd := hDoneS j (by omega) hjLt eio heio hUj
                by_cases hSame : eio = ei_old
                · subst hSame
                  refine ⟨by rw [hET12]; dsimp [thrNewPtr]; omega, by rw [hET12]; exact hThrSp,
                    by rw [hER12]; dsimp [recNewPtr, thrNewPtr]; omega, by rw [hER12]; exact hRecSp,
                    by rw [hET12]; exact hThrNewAt.congr (fun k hk => h12_above _ (by dsimp [thrNewPtr]; omega)),
                    by rw [hER12]; exact hRecNewAt.congr (fun x hxlo hxhi => h12_above x (by omega))⟩
                · have hneNew : e2i' (i2e' eio) ≠ ei_new := hNewInj eio heio (hUj ▸ List.getElem_mem hjLt) hSame
                  have hCapO := (hDelInfo eio heio (hUj ▸ List.getElem_mem hjLt)).2.2.2.1
                  have hETEq : t12.mem (edgeThresholds + e2i' (i2e' eio)) = s.mem (edgeThresholds + e2i' (i2e' eio)) :=
                    h12_eq_s _ (by omega) (by omega) (by rcases hMutDisj with h | h <;> omega)
                  have hEREq : t12.mem (edgeRecords + e2i' (i2e' eio)) = s.mem (edgeRecords + e2i' (i2e' eio)) :=
                    h12_eq_s _ (by omega) (by rcases hMutDisj with h | h <;> omega) (by omega)
                  refine ⟨by rw [hETEq]; exact hd.1, by rw [hETEq]; omega,
                    by rw [hEREq]; exact hd.2.2.1, by rw [hEREq]; omega,
                    by rw [hETEq]; exact hd.2.2.2.2.1.congr (fun k hk =>
                        (h12_above _ (by omega)).trans (hFrRef _ (by omega))),
                    by rw [hEREq]; exact hd.2.2.2.2.2.congr (fun x hxlo hxhi =>
                        (h12_above x (by omega)).trans (hFrRef x (by omega)))⟩
            · intro j₁ hj₁ hj₁Lt e₁ he₁ hU₁ j₂ hj₂ hj₂Lt e₂ he₂ hU₂
              dsimp only
              have hEqOfNe : ∀ eio ∈ G0.E, ∀ hMem : .delete eio ∈ U_int, eio ≠ ei_old →
                  t12.mem (edgeThresholds + e2i' (i2e' eio)) = s.mem (edgeThresholds + e2i' (i2e' eio)) ∧
                  t12.mem (edgeRecords + e2i' (i2e' eio)) = s.mem (edgeRecords + e2i' (i2e' eio)) := by
                intro eio heio hMem hne
                have hneNew := hNewInj eio heio hMem hne
                have hCapO := (hDelInfo eio heio hMem).2.2.2.1
                exact ⟨h12_eq_s _ (by omega) (by omega) (by rcases hMutDisj with h | h <;> omega),
                  h12_eq_s _ (by omega) (by rcases hMutDisj with h | h <;> omega) (by omega)⟩
              have hCur12 : curH ≤ thrNewPtr ∧ thrNewPtr + L ≤ recNewPtr := by
                dsimp [thrNewPtr, recNewPtr]; omega
              by_cases h1 : e₁ = ei_old
              · subst h1
                by_cases h2 : e₂ = e₁
                · subst h2
                  exact ⟨fun hne => absurd rfl hne, by rw [hET12, hER12]; exact Or.inl hCur12.2⟩
                · have h2Lt : j₂ < i := by
                    by_contra h; have heq : j₂ = i := by omega
                    subst heq; rw [hUi] at hU₂; injection hU₂ with hE; exact h2 hE.symm
                  have hd2 := hDoneS j₂ h2Lt hj₂Lt e₂ he₂ hU₂
                  have hE2 := hEqOfNe e₂ he₂ (hU₂ ▸ List.getElem_mem hj₂Lt) h2
                  rw [hET12, hER12, hE2.2]
                  exact ⟨fun _ => Or.inr (by omega), Or.inr (by omega)⟩
              · have h1Lt : j₁ < i := by
                  by_contra h; have heq : j₁ = i := by omega
                  subst heq; rw [hUi] at hU₁; injection hU₁ with hE; exact h1 hE.symm
                have hd1 := hDoneS j₁ h1Lt hj₁Lt e₁ he₁ hU₁
                have hE1 := hEqOfNe e₁ he₁ (hU₁ ▸ List.getElem_mem hj₁Lt) h1
                by_cases h2 : e₂ = ei_old
                · subst h2
                  rw [hE1.1, hE1.2, hER12]
                  exact ⟨fun _ => Or.inl (by omega), Or.inl (by omega)⟩
                · have h2Lt : j₂ < i := by
                    by_contra h; have heq : j₂ = i := by omega
                    subst heq; rw [hUi] at hU₂; injection hU₂ with hE; exact h2 hE.symm
                  have hE2 := hEqOfNe e₂ he₂ (hU₂ ▸ List.getElem_mem hj₂Lt) h2
                  rw [hE1.1, hE1.2, hE2.2]
                  exact hDisjS j₁ h1Lt hj₁Lt e₁ he₁ hU₁ j₂ h2Lt hj₂Lt e₂ he₂ hU₂
          refine ⟨.normal, t12, _, runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rOuter, rfl⟩),
            ⟨hInvN, by simp [h12_r 80 (by omega), h80]⟩, by dsimp [stepCost]; omega⟩
        · have rCondDead : Runs w p ω' (.cond (.load (.bin .add (.reg 77) (.reg 82))) liveThen .nop) t3 .normal t3 6 :=
            runs_cond_iff.mpr ⟨0, 1, by
              simp [Expr.eval, BinOp.eval, t3, t2, t1, h77, show rootGraph + 4 + 7 * n + ei_old < 2 ^ w by omega,
                hEPresAt, hLive], by simp [runs_nop_iff], by simp [Expr.size]⟩
          have rElse : Runs w p ω' delElse t1 .normal t3 17 :=
            runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, rt2, runs_seq_iff.mpr (Or.inr ⟨t3, 4, 6, rt3, rCondDead, rfl⟩), rfl⟩)
          have rOuter : Runs w p ω' (.cond (.bin .eq (.reg 81) (.const 0)) (.assign 79 (.bin .add (.reg 79) (.const 4))) delElse)
              t1 .normal t3 21 :=
            runs_cond_iff.mpr ⟨0, 17, by simp [Expr.eval, BinOp.eval, t1, show (0 : ℕ) < 2 ^ w by omega],
              by simpa using rElse, by simp [Expr.size]⟩
          have hInvN : Inv (i + 1) { t3 with regs := Function.update t3.regs 80 (i + 1) } :=
            ⟨curH, by simp [t3, t2, t1, h60], by simp [t3, t2, t1, h61], by simp [t3, t2, t1, h62],
              by simp [t3, t2, t1, h63], by simp [t3, t2, t1, h65], by simp [t3, t2, t1, h66],
              by simp [t3, t2, t1, h67], by simp [t3, t2, t1, h68], by simp [t3, t2, t1, h69],
              by simp [t3, t2, t1, h70], by simp [t3, t2, t1, h77], by simp [t3, t2, t1, h78],
              by simp [t3], by simp, by simp [t3, t2, t1, h95], by simp [t3, t2, t1, h99],
              hHLo, hHHi.trans (Nat.add_le_add_left (Nat.mul_le_mul_right sp (Nat.le_succ i)) _),
              hzS, hNegEpsS, hFrS,
              fun ei hei hni => hUnchS ei hei (fun ⟨j, hjLt, hj, eio, heio, hUj, hEq⟩ =>
                hni ⟨j, hjLt, Nat.lt_succ_of_lt hj, eio, heio, hUj, hEq⟩),
              fun j hj hjLt eio heio hUj => by
                by_cases hji : j = i
                · subst hji; rw [hUi] at hUj; injection hUj with hEq; subst hEq; exact absurd heio hLive
                · exact hDoneS j (by omega) hjLt eio heio hUj,
              fun j₁ hj₁ hj₁Lt e₁ he₁ hU₁ j₂ hj₂ hj₂Lt e₂ he₂ hU₂ => by
                have h1 : j₁ < i := by
                  by_contra h; have heq : j₁ = i := by omega
                  subst heq; rw [hUi] at hU₁; injection hU₁ with hEq; subst hEq; exact absurd he₁ hLive
                have h2 : j₂ < i := by
                  by_contra h; have heq : j₂ = i := by omega
                  subst heq; rw [hUi] at hU₂; injection hU₂ with hEq; subst hEq; exact absurd he₂ hLive
                exact hDisjS j₁ h1 hj₁Lt e₁ he₁ hU₁ j₂ h2 hj₂Lt e₂ he₂ hU₂⟩
          refine ⟨.normal, t3, 3 + 21 + 1, runs_seq_iff.mpr (Or.inr ⟨t1, 3, 21, rt1, rOuter, rfl⟩),
            ⟨hInvN, by simp [t3, t2, t1, h80]⟩, by dsimp [stepCost]; omega⟩)
  obtain ⟨o, out, cLoop, rLoop, hD, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hD
  | normal =>
    obtain ⟨nextH, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hD99,
      hHLoE, hHHiE, hzE, _, hFrE, hUnchE, hDoneE, hDisjE⟩ := hD
    have rRet : Runs w p ω (.ret (.reg 99)) out (.returned nextH) out 2 :=
      runs_ret_iff.mpr ⟨nextH, by simp [Expr.eval, hD99], rfl, rfl, rfl⟩
    have rAll := runs_seq_iff.mpr (Or.inr ⟨sA, cA, _, rA,
      runs_seq_iff.mpr (Or.inr ⟨sB, 3, _, rB,
      runs_seq_iff.mpr (Or.inr ⟨sC, 4, _, rC,
      runs_seq_iff.mpr (Or.inr ⟨out, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    refine ⟨nextH, out, _, rAll, hHLoE, hHHiE, ?_, hzE, hFrE, ?_, ?_, ?_⟩
    · have hrc : rangeCost (fun _ => stepCost) 0 U_int.length = U_int.length * stepCost := by simp [rangeCost]
      simp only [Expr.size, hrc] at hcLoop
      have hm : U_int.length * stepCost + U_int.length * 9 = U_int.length * (wireRefreshOneCost L + 119) := by
        dsimp [stepCost]; ring
      have hle120 : U_int.length * (wireRefreshOneCost L + 119) ≤ U_int.length * (wireRefreshOneCost L + 120) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    · intro ei hei hni
      exact hUnchE ei hei (fun ⟨j, hjLt, _, eio, heio, hUj, hEq⟩ =>
        hni ⟨eio, heio, hUj ▸ List.getElem_mem hjLt, hEq⟩)
    · intro ei_old hLive hMem
      obtain ⟨j, hjLt, hUj⟩ := List.getElem_of_mem hMem
      exact hDoneE j hjLt hjLt ei_old hLive hUj
    · intro ei₁ he₁ ei₂ he₂ hM₁ hM₂
      obtain ⟨j₁, hj₁, hU₁⟩ := List.getElem_of_mem hM₁
      obtain ⟨j₂, hj₂, hU₂⟩ := List.getElem_of_mem hM₂
      exact hDisjE j₁ hj₁ hj₁ ei₁ he₁ hU₁ j₂ hj₂ hj₂ ei₂ he₂ hU₂

end MinCostFlow.MinRatio
