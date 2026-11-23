module

public import MinCostFlow.MinRatio.UpdateCycleLoopBase
public import MinCostFlow.MinRatio.OrdSolverToolMono
public import MinCostFlow.MinRatio.WireFindCycleSpec
public import MinCostFlow.MinRatio.OrdShiftStepSpecW
public import MinCostFlow.Chain.Ordered.ShiftLoopOdometer
import WordRAM.Tactic

/-!
# The inner candidate-cycle and shift loop of `Update`, by induction on the shift quota

Proves `updateCycleLoop_ind`: the `.loop` inside `updateCycleLoopBody` implements
`Chain.Ordered.algorithm2_loopWith cfg (1 / 2^k)` while preserving `solverStateRep` and
`PathTreeNumericInv`. The proof is by strong induction on an upper bound of the unused shift
quota `shiftRemainingBudget` and of the shift-loop counter `loopOdometer`, each of which every
shift lowers by at least one (`loopStepBound`). The loop keeps
`Chain.Ordered.ShiftLoopChainInv` of the chain (`ShiftLoopChainInv.shift`), which the shift
step `ShiftLevelStepSpecW` assumes.

The cost is charged by the actual number of iterations: the bound has the quota left at the
end on its left side, `cost + φ' + N' · B ≤ (N + 1) · B + 10 + φ`, where `N` and `N'` are the
quotas before and after the loop and `B` is `cycleLoopIterBudget`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- A bound on the number of steps that the shift loop runs from `model`: the smaller of the
unused shift quota and the shift-loop counter. Each shift lowers both
(`loopStepBound_shift_lt`). The counter is below `(⌈2 Ψ_g⌉ k + 1)^{d+1}`
(`Chain.Ordered.loopOdometer_lt_pow`), so the space of the loop is bounded by a polynomial; the
quota alone has no such bound. -/
@[expose] noncomputable def loopStepBound (cfg : Alg2Config) (model : Alg2State cfg) : ℕ :=
  min (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain)
    (Chain.Ordered.loopOdometer cfg model.chain model.branD model.passes)

/-- A shift of the loop at the eligible level lowers `loopStepBound`. -/
theorem loopStepBound_shift_lt (cfg : Alg2Config) (model : Alg2State cfg) (i : Fin (cfg.P.d + 1))
    (hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) model.passes = some i)
    (hCap : (model.chain.shiftCount i.val : ℝ) + 1 ≤
      gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val) :
    loopStepBound cfg (alg2LoopShiftStep cfg model i) < loopStepBound cfg model := by
  have h1 : shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
      (alg2LoopShiftStep cfg model i).chain <
      shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain :=
    Chain.Ordered.shiftRemainingBudget_lt_of_step model.chain i hCap
  have h2 : Chain.Ordered.loopOdometer cfg (alg2LoopShiftStep cfg model i).chain
      (alg2LoopShiftStep cfg model i).branD (alg2LoopShiftStep cfg model i).passes <
      Chain.Ordered.loopOdometer cfg model.chain model.branD model.passes :=
    Chain.Ordered.loopOdometer_shift_lt cfg model.chain model.branD model.passes i hElig
  unfold loopStepBound
  omega

/-- A shift step of the loop preserves the chain's level size bounds `lvlM` and `N₀`. -/
theorem alg2LoopShiftStep_lvlM_N0 (cfg : Alg2Config) (model : Alg2State cfg)
    (i : Fin (cfg.P.d + 1)) :
    (alg2LoopShiftStep cfg model i).chain.lvlM = model.chain.lvlM ∧
    (alg2LoopShiftStep cfg model i).chain.N₀ = model.chain.N₀ := by
  dsimp only [alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- Generic credit-bearing strong induction on `loopStepBound` for the `.loop (.reg 16)` inside
`updateCycleLoopBody`, parameterized by a loop-carried invariant `Inv` preserved across `FindCycle`,
memory agreement on the solver's foot, and the shift step. -/
theorem updateCycleLoop_ind_credit_gen
    {w L P m U V psi k qHdr epsExp drainUnit capExp limbMul capLimit findCycleProc updateQualityProc
      shiftCheckProc shiftLevelProc findSpace findBudget maxEdges maxPaths shiftSpace shiftBudget
      toolMul treeMul root quotaBase : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {ω : ℕ → Bool}
    (Inv : Alg2State cfg → SolverToken cfg L Rcore → (ℕ → ℕ) → Prop)
    (hInvFind : ∀ model tok tok' mem mem',
      (solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).rep root model tok mem →
      Inv model tok mem →
      PreservesLevelMeta tok tok' mem mem' →
      tok'.intCap = tok.intCap →
      Inv model tok' mem')
    (hInvMem : ∀ model tok mem mem',
      (solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).rep root model tok mem →
      Inv model tok mem →
      (∀ a, (solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).foot root tok a →
        mem' a = mem a) →
      Inv model tok mem')
    (hMono : toolMul = 0 ∨ ToolCostMono cfg.T) (hV : cfg.ValidOrdNoHidden)
    (hα : cfg.α = Num.IPM.alphaPrime m U / 8)
    (hFind : FindCycleStepSpecW w L P m V psi qHdr epsExp drainUnit capExp limbMul capLimit cfg Rcore p
      findCycleProc findSpace findBudget maxEdges maxPaths)
    (hQual : ∀ inner norm, MeetsContract w p updateQualityProc
      (updateQualityFromNormContract w 4 m U k P inner norm))
    (hCheck : p.procs[shiftCheckProc]? = some shiftCheckBody)
    (hShift :
      let Rrep := solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore
      ∃ body, p.procs[shiftLevelProc]? = some body ∧
        ∀ (root heap pos : ℕ) (i : Fin (cfg.P.d + 1)) (ω : ℕ → Bool) (mem : ℕ → ℕ)
          (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
          let model' := alg2LoopShiftStep cfg model i
          (model.chain.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val →
          (if i.val < cfg.P.d then model.chain.bran i.val else model.branD) < cfg.P.k →
          (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
          shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val < 2 ^ w →
          model.passes i + 1 < 2 ^ w →
          Rrep.rep root model tok mem →
          Inv model tok mem →
          Chain.Ordered.ShiftLoopChainInv cfg model.chain →
          Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
          2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
          PathTreeNumericInv tok.tree tok.trees B R →
          OffTreeRecInv model L mem tok.edgeRecords B →
          OffTreeRecBound model L mem tok.edgeRecords B →
          WireCapFacts capExp limbMul L capLimit model →
          (∀ a, Rrep.foot root tok a → a < heap) →
          ZeroFrom mem heap →
          heap + shiftSpace < 2 ^ w →
          ∃ nextHeap cost out tok',
            Runs w p ω body (startState [root, i.val, heap] mem pos) (.returned nextHeap) out cost ∧
            heap ≤ nextHeap ∧ nextHeap ≤ heap + shiftSpace ∧
            tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
            Rrep.rep root model' tok' out.mem ∧
            Inv model' tok' out.mem ∧
            PathTreeNumericInv tok'.tree tok'.trees B R ∧
            OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
            OffTreeRecBound model' L out.mem tok'.edgeRecords B ∧
            ZeroFrom out.mem nextHeap ∧
            (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
            (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
            cost + Rrep.phi root tok' out.mem ≤
              shiftBudget +
                toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
                treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
                Rrep.phi root tok mem)
    (hw5 : 5 < 2 ^ w) (h5L1W : 5 * L + 1 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) (hqW : k + Num.IPM.alphaExponent m U + 3 < 2 ^ w)
    (_hpsiLimW : ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore
    ∀ (N : ℕ) (st : State) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ)
      (lctOps : ℕ),
      loopStepBound cfg model ≤ N →
      let curHeap := st.regs 18
      st.regs 0 = root → st.regs 1 = quotaBase →
      st.regs 2 = ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ →
      st.regs 3 = k + Num.IPM.alphaExponent m U + 3 →
      st.regs 11 = tok.levelsEnd → st.regs 12 = L →
      st.regs 14 = cfg.P.d + 1 → st.regs 15 = tok.levelsEnd + (cfg.P.d + 1) →
      st.regs 16 = 1 →
      Rrep.rep root model tok st.mem →
      Inv model tok st.mem →
      Chain.Ordered.ShiftLoopChainInv cfg model.chain →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L st.mem tok.edgeRecords B →
      OffTreeRecBound model L st.mem tok.edgeRecords B →
      WireCapFacts capExp limbMul L capLimit model →
      2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ) →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      (∀ e ∈ model.extG.E, 0 ≤ model.extℓ e) →
      (∀ a, Rrep.foot root tok a → a < curHeap) →
      quotaBase + cfg.P.d < curHeap →
      (∀ i ≤ cfg.P.d, st.mem (quotaBase + i) =
        shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i) →
      (∀ i ≤ cfg.P.d,
        shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i < 2 ^ w) →
      BranchesLtK cfg model →
      (∀ i ≤ cfg.P.d, ¬ Rrep.foot root tok (quotaBase + i)) →
      ZeroFrom st.mem curHeap →
      curHeap + (N + 1) * cycleLoopIterSpace L findSpace shiftSpace < 2 ^ w →
      let loopRes := Chain.Ordered.algorithm2_loopWith cfg (1 / (2 : ℝ) ^ k) model.extG model.extToInt
        model.extg model.extℓ model.chain model.branD model.passes lctOps
      let modelEnd : Alg2State cfg :=
        { model with
          chain := loopRes.1
          branD := loopRes.2.1
          passes := loopRes.2.2.1 }
      ∃ out cost ret curDesc tokEnd,
        Runs w p ω
          (.loop (.reg 16)
            (.assign 20 (.reg 18) ;;
             .call 18 findCycleProc [.reg 0, .reg 18] ;;
             .assign 22 (.load (.reg 20)) ;;
             .assign 23 (.load (.bin .add (.reg 20) (.const 1))) ;;
             .call 24 updateQualityProc [.reg 23, .reg 22, .reg 12, .reg 3, .reg 18] ;;
             .assign 18 (.bin .add (.reg 18) (.bin .add (.bin .mul (.const 5) (.reg 12)) (.const 1))) ;;
             .cond (.reg 24)
               (.assign 17 (.const 1) ;; .assign 16 (.const 0))
               (.call 25 shiftCheckProc [.reg 11, .reg 2, .reg 14, .reg 15, .reg 1] ;;
                .cond (.reg 25)
                  (.assign 26 (.bin .sub (.reg 25) (.const 1)) ;;
                   .call 18 shiftLevelProc [.reg 0, .reg 26, .reg 18])
                  (.assign 17 (.const 0) ;; .assign 16 (.const 0)))))
          st .normal out cost ∧
        out.regs 4 = st.regs 4 ∧
        out.regs 17 = (if loopRes.2.2.2.2.isSome then 1 else 0) ∧
        out.regs 18 = ret ∧ out.regs 20 = curDesc ∧
        curHeap ≤ ret ∧ ret ≤ curHeap + (N + 1) * cycleLoopIterSpace L findSpace shiftSpace ∧
        Rrep.rep root modelEnd tokEnd out.mem ∧
        Inv modelEnd tokEnd out.mem ∧
        tokEnd.intCap = tok.intCap ∧
        PathTreeNumericInv tokEnd.tree tokEnd.trees B R ∧
        OffTreeRecInv modelEnd L out.mem tokEnd.edgeRecords B ∧
        (loopRes.2.2.2.2.isSome →
          ∃ inner norm edges paths,
            CycleDescriptorAt modelEnd L P out.mem curDesc ret inner norm edges paths ∧
            edges.length ≤ maxEdges ∧ paths.length ≤ maxPaths ∧
            (∀ x < 2 * edges.length, tokEnd.tag (out.mem (curDesc + 2) + x) = 0) ∧
            (∀ x < 2 * paths.length, tokEnd.tag (out.mem (curDesc + 4) + x) = 0) ∧
            (∀ a, tokEnd.tag a = 18 → a < curDesc) ∧
            curHeap ≤ curDesc ∧ curDesc + 6 ≤ ret) ∧
        ZeroFrom out.mem ret ∧
        (∀ a < curHeap, ¬ Rrep.foot root tok a → out.mem a = st.mem a) ∧
        (∀ a, Rrep.foot root tokEnd a → Rrep.foot root tok a ∨ (curHeap ≤ a ∧ a < ret)) ∧
        cost + Rrep.phi root tokEnd out.mem +
            shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) loopRes.1 *
              cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
            toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
          (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain + 1) *
            cycleLoopIterBudget L cfg.P.d findBudget shiftBudget + 10 +
          Rrep.phi root tok st.mem +
          toolMul * loopRes.1.totalRuntime + treeMul * loopRes.1.totalTreeUpdates := by
  intro Rrep N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro st model tok B R lctOps hN curHeap hr0 hr1 hr2 hr3 hr11 hr12 hr14 hr15 hr16
      hrep hInv hLoopInv hnum hoff hBd hCapFacts hcapEval hcapTree hlogW hlenNN hbelow hqBelow hquotas hquotasW hBr hqOut hz hroom
    obtain ⟨bFind, hbFind, hFindSpec⟩ := hFind
    obtain ⟨bShift, hbShift, hShiftSpec⟩ := hShift
    have hlocR := solverStateRep_local cfg L P m V psi qHdr epsExp drainUnit hlocalCore
    have hcurW : curHeap < 2 ^ w := by
      have : 1 * cycleLoopIterSpace L findSpace shiftSpace ≤ (N + 1) * cycleLoopIterSpace L findSpace shiftSpace :=
        Nat.mul_le_mul_right _ (by omega)
      dsimp only [cycleLoopIterSpace] at hroom this; omega
    have h1Iter : curHeap + cycleLoopIterSpace L findSpace shiftSpace < 2 ^ w := by
      have : 1 * cycleLoopIterSpace L findSpace shiftSpace ≤ (N + 1) * cycleLoopIterSpace L findSpace shiftSpace :=
        Nat.mul_le_mul_right _ (by omega)
      rw [one_mul] at this; omega
    have hrootW : root < 2 ^ w := by
      have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags⟩ := hrep
      exact lt_trans (hbelow root (Or.inl (htags.1 root (by rw [show root = root + 0 by omega, htags.2.1 0 (by omega)]; decide)))) hcurW
    have hlevEndW : tok.levelsEnd + (cfg.P.d + 1) + cfg.P.d < 2 ^ w := by
      have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags⟩ := hrep
      obtain ⟨hOwn, _, _, _, _, t5, _⟩ := htags
      have hlt := hbelow (tok.levelsEnd + (cfg.P.d + 1 + cfg.P.d))
        (Or.inl (hOwn _ (by rw [t5 (cfg.P.d + 1 + cfg.P.d) (by omega)]; decide)))
      omega
    -- Step 1: evaluate candidate cycle via `findCycleProc`
    let s1 : State := { st with regs := Function.update st.regs 20 curHeap }
    have r1 : Runs w p ω (.assign 20 (.reg 18)) st .normal s1 2 :=
      runs_assign_iff.mpr ⟨curHeap, by simp [Expr.eval, curHeap], rfl, rfl, rfl⟩
    obtain ⟨hF, cF, stF, tokF, inner, norm, edges, paths, hrF, hhFLo, hhFHi, hlevF, hintCapF,
        hedMaxF, hptMaxF, htagEdF, htagPtF, htag18F, hdescF,
        hrepF, hmetaF, hnumF, hoffF, hBdF, hzF, hfrF, hftF, hcF⟩ :=
      hFindSpec root curHeap s1.pos ω st.mem model tok B R hrep hnum hoff hBd hCapFacts
        (shiftLoopLevelFacts_of_inv hV hLoopInv)
        hcapEval hcapTree hlogW hlenNN hbelow hz
        (by dsimp only [cycleLoopIterSpace] at h1Iter; omega)
    have hInvF : Inv model tokF stF.mem := hInvFind model tok tokF st.mem stF.mem hrep hInv hmetaF hintCapF
    let s2 : State := { regs := Function.update s1.regs 18 hF, mem := stF.mem, pos := stF.pos }
    have r2 : Runs w p ω (.call 18 findCycleProc [.reg 0, .reg 18]) s1 .normal s2 (cF + 3) :=
      runs_call_iff.mpr ⟨[root, curHeap], bFind, .returned hF, stF, cF,
        by simp [evalArgs, Expr.eval, s1, hr0, curHeap], hbFind, hrF, rfl, rfl,
        by simp [argsSize, Expr.size]; omega⟩
    let innerPtr := stF.mem curHeap
    let normPtr := stF.mem (curHeap + 1)
    let s3 : State := { s2 with regs := Function.update s2.regs 22 innerPtr }
    let s4 : State := { s3 with regs := Function.update s3.regs 23 normPtr }
    have r3 : Runs w p ω (.assign 22 (.load (.reg 20))) s2 .normal s3 3 :=
      runs_assign_iff.mpr ⟨innerPtr, by simp [Expr.eval, s2, s1, innerPtr], rfl, rfl, rfl⟩
    have r4 : Runs w p ω (.assign 23 (.load (.bin .add (.reg 20) (.const 1)))) s3 .normal s4 5 :=
      runs_assign_iff.mpr ⟨normPtr, by
        have hcur1W : curHeap + 1 < 2 ^ w := by dsimp only [cycleLoopIterSpace] at h1Iter; omega
        simp [Expr.eval, BinOp.eval, s3, s2, s1, show 1 < 2 ^ w by omega, hcur1W, normPtr],
        rfl, rfl, rfl⟩
    -- Step 2: test quality via `updateQualityProc`
    have hhFW : hF < 2 ^ w := by dsimp only [cycleLoopIterSpace] at h1Iter; omega
    have ⟨_, _, _, _, _, _, _, hinnerEnd, hnormEnd, _, _, hnormNN, hinnerAt, hnormAt, hinnerEq, hnormEq, _, _, _⟩ := hdescF
    obtain ⟨bQ, hbQ, oQ, stQ, cQ, hrQ, ⟨hbitQ, hfrQ, hzQ⟩, hcQ⟩ :=
      hQual inner norm [normPtr, innerPtr, L, k + Num.IPM.alphaExponent m U + 3, hF] s4.mem s4.pos ω
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega)
        ⟨normPtr, innerPtr, L, hF, rfl, by omega, hnormNN, hnormEnd, hinnerEnd, hnormAt, hinnerAt,
          hzF, by dsimp only [cycleLoopIterSpace] at h1Iter; omega⟩
    change cQ ≤ 181 * L + 285 at hcQ
    change ∀ x < hF, stQ.mem x = stF.mem x at hfrQ
    let hQ := hF + (5 * L + 1)
    have hhQW : hQ < 2 ^ w := by dsimp only [hQ, cycleLoopIterSpace] at h1Iter ⊢; omega
    let s5 : State := { regs := Function.update s4.regs 24 oQ.value, mem := stQ.mem, pos := stQ.pos }
    have r5 : Runs w p ω (.call 24 updateQualityProc [.reg 23, .reg 22, .reg 12, .reg 3, .reg 18])
        s4 .normal s5 (cQ + 6) :=
      runs_call_iff.mpr ⟨[normPtr, innerPtr, L, k + Num.IPM.alphaExponent m U + 3, hF], bQ, oQ, stQ, cQ,
        by simp [evalArgs, Expr.eval, s4, s3, s2, s1, hr12, hr3], hbQ, hrQ, rfl, rfl,
        by simp [argsSize, Expr.size]; omega⟩
    let s6 : State := { s5 with regs := Function.update s5.regs 18 hQ }
    have r6 : Runs w p ω (.assign 18 (.bin .add (.reg 18) (.bin .add (.bin .mul (.const 5) (.reg 12)) (.const 1))))
        s5 .normal s6 8 :=
      runs_assign_iff.mpr ⟨hQ, by
        simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, hr12, hw5, show 1 < 2 ^ w by omega,
          show 5 * L < 2 ^ w by omega, h5L1W, hhQW, hQ], rfl, rfl, rfl⟩
    have hbitLoop : oQ.value =
        if model.extG.inner model.extg (liftEdgeFn model.extG model.extToInt (algorithm1_findCycle model.chain).1) /
            model.extG.lnorm model.extℓ (liftEdgeFn model.extG model.extToInt (algorithm1_findCycle model.chain).1) ≤
            -((1 / (2 : ℝ) ^ k) * cfg.α) then 1 else 0 :=
      updateQualityFromNorm_bit_eq_loopGuard (w := w) (h := 4) hα hinnerEq hnormEq ⟨hbitQ, hfrQ, hzQ⟩
    have hfootF (a : ℕ) (ha : Rrep.foot root tokF a) : a < hF := by
      rcases hftF a ha with h0 | ⟨_, hhi⟩
      · exact lt_of_lt_of_le (hbelow a h0) (by omega)
      · exact hhi
    have hagFQ (a : ℕ) (ha : Rrep.foot root tokF a) : stF.mem a = stQ.mem a :=
      (hfrQ a (hfootF a ha)).symm
    have hrepQ : Rrep.rep root model tokF stQ.mem := (hlocR root model tokF stF.mem stQ.mem hagFQ).1 hrepF
    have hInvQ : Inv model tokF stQ.mem :=
      hInvMem model tokF stF.mem stQ.mem hrepF hInvF (fun a ha => (hagFQ a ha).symm)
    have hoffQ : OffTreeRecInv model L stQ.mem tokF.edgeRecords B :=
      offTreeRecInv_of_agree hrepF hoffF fun a ha => by
        have hnz : tokF.tag a ≠ 0 := by rcases ha with h | h <;> omega
        have hownF : tokF.owned a := hrepF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a hnz
        exact hfrQ a (hfootF a (Or.inl hownF))
    have hBdQ : OffTreeRecBound model L stQ.mem tokF.edgeRecords B :=
      offTreeRecBound_of_agree hrepF hBdF fun a ha => by
        have hnz : tokF.tag a ≠ 0 := by rcases ha with h | h <;> omega
        have hownF : tokF.owned a := hrepF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a hnz
        exact hfrQ a (hfootF a (Or.inl hownF))
    have hphiQ : Rrep.phi root tokF stQ.mem = Rrep.phi root tokF stF.mem :=
      ((hlocR root model tokF stF.mem stQ.mem hagFQ).2).symm
    have hfrQ_st (a : ℕ) (ha : a < curHeap) (hnf : ¬ Rrep.foot root tok a) : stQ.mem a = st.mem a :=
      (hfrQ a (by omega)).trans (hfrF a ha hnf)
    let condIn : Stmt :=
      .cond (.reg 25)
        (.assign 26 (.bin .sub (.reg 25) (.const 1)) ;;
         .call 18 shiftLevelProc [.reg 0, .reg 26, .reg 18])
        (.assign 17 (.const 0) ;; .assign 16 (.const 0))
    let elseBranch : Stmt :=
      .call 25 shiftCheckProc [.reg 11, .reg 2, .reg 14, .reg 15, .reg 1] ;; condIn
    let condOut : Stmt :=
      .cond (.reg 24) (.assign 17 (.const 1) ;; .assign 16 (.const 0)) elseBranch
    let loopBody : Stmt :=
      .assign 20 (.reg 18) ;;
      .call 18 findCycleProc [.reg 0, .reg 18] ;;
      .assign 22 (.load (.reg 20)) ;;
      .assign 23 (.load (.bin .add (.reg 20) (.const 1))) ;;
      .call 24 updateQualityProc [.reg 23, .reg 22, .reg 12, .reg 3, .reg 18] ;;
      .assign 18 (.bin .add (.reg 18) (.bin .add (.bin .mul (.const 5) (.reg 12)) (.const 1))) ;;
      condOut
    -- Helper to chain the 6-statement prefix with `condOut`
    have hchainBody {sEnd : State} {cTail : ℕ}
        (hTail : Runs w p ω condOut s6 .normal sEnd cTail) :
        Runs w p ω loopBody st .normal sEnd
          (2 + ((cF + 3) + (3 + (5 + ((cQ + 6) + (8 + cTail + 1) + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
        runs_seq_iff.mpr (Or.inr ⟨s2, cF + 3, _, r2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 3, _, r3,
        runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
        runs_seq_iff.mpr (Or.inr ⟨s5, cQ + 6, _, r5,
        runs_seq_iff.mpr (Or.inr ⟨s6, 8, cTail, r6, hTail, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    -- Branch on the exact `Chain.Ordered.algorithm2_loopWith` guard
    by_cases hGood : model.extG.inner model.extg
        (liftEdgeFn model.extG model.extToInt (algorithm1_findCycle model.chain).1) /
        model.extG.lnorm model.extℓ
        (liftEdgeFn model.extG model.extToInt (algorithm1_findCycle model.chain).1) ≤
        -((1 / (2 : ℝ) ^ k) * cfg.α)
    · -- GOOD CYCLE FOUND: set `reg 17 := 1`, `reg 16 := 0`, and exit loop
      have hq1 : oQ.value = 1 := by rw [hbitLoop, ite_eq_left hGood]
      let s7 : State := { s6 with regs := Function.update s6.regs 17 1 }
      let s8 : State := { s7 with regs := Function.update s7.regs 16 0 }
      have r7 : Runs w p ω (.assign 17 (.const 1)) s6 .normal s7 2 :=
        runs_assign_iff.mpr ⟨1, by simp [Expr.eval, show 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have r8 : Runs w p ω (.assign 16 (.const 0)) s7 .normal s8 2 :=
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have rCond : Runs w p ω condOut s6 .normal s8 7 :=
        runs_cond_iff.mpr ⟨1, 5, by simp [Expr.eval, s6, s5, hq1],
          by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
             exact runs_seq_iff.mpr (Or.inr ⟨s7, 2, 2, r7, r8, rfl⟩), by simp [Expr.size]⟩
      have rExit : Runs w p ω (.loop (.reg 16) loopBody) s8 .normal s8 2 :=
        runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, s8], rfl, rfl, by simp [Expr.size]⟩)
      have rLoop : Runs w p ω (.loop (.reg 16) loopBody) st .normal s8
          (1 + (2 + ((cF + 3) + (3 + (5 + ((cQ + 6) + (8 + 7 + 1) + 1) + 1) + 1) + 1) + 1) + 2 + 1) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s8, _, 2, by simp [Expr.eval, hr16], by decide,
          hchainBody rCond, rExit, by simp [Expr.size]⟩))
      have hloopEq : Chain.Ordered.algorithm2_loopWith cfg (1 / (2 : ℝ) ^ k) model.extG model.extToInt
          model.extg model.extℓ model.chain model.branD model.passes lctOps =
          (model.chain, model.branD, model.passes,
            lctOps + 2 * ((walkEdges (algorithm1_findCycle model.chain).2.1 \
              model.chain.toTreeChain.chainTree.E).card + 1),
            some (liftEdgeFn model.extG model.extToInt (algorithm1_findCycle model.chain).1)) := by
        rw [Chain.Ordered.algorithm2_loopWith]; dsimp only; rw [dite_eq_left hGood]
      have hdescQ : CycleDescriptorAt model L P stQ.mem curHeap hQ inner norm edges paths := by
        obtain ⟨h3d, h5d, h6d, hiLo, hnLo, heLo, hpLo, hiE, hnE, heE, hpE, hnn, hiA, hnA, hiEq, hnEq, heA, hpA, hrt⟩ := hdescF
        have h0q : stQ.mem curHeap = stF.mem curHeap := hfrQ curHeap (by omega)
        have h1q : stQ.mem (curHeap + 1) = stF.mem (curHeap + 1) := hfrQ (curHeap + 1) (by omega)
        have h2q : stQ.mem (curHeap + 2) = stF.mem (curHeap + 2) := hfrQ (curHeap + 2) (by omega)
        have h3q : stQ.mem (curHeap + 3) = stF.mem (curHeap + 3) := hfrQ (curHeap + 3) (by omega)
        have h4q : stQ.mem (curHeap + 4) = stF.mem (curHeap + 4) := hfrQ (curHeap + 4) (by omega)
        have h5q : stQ.mem (curHeap + 5) = stF.mem (curHeap + 5) := hfrQ (curHeap + 5) (by omega)
        refine ⟨h3q.trans h3d, h5q.trans h5d, by dsimp only [hQ]; omega,
          by rw [h0q]; exact hiLo, by rw [h1q]; exact hnLo,
          by rw [h2q]; exact heLo, by rw [h4q]; exact hpLo,
          by rw [h0q]; dsimp only [hQ]; omega, by rw [h1q]; dsimp only [hQ]; omega,
          by rw [h2q]; dsimp only [hQ]; omega, by rw [h4q]; dsimp only [hQ]; omega,
          hnn, by rw [h0q]; exact hiA.congr (fun j hj => hfrQ _ (by omega)),
          by rw [h1q]; exact hnA.congr (fun j hj => hfrQ _ (by omega)),
          hiEq, hnEq,
          by rw [h2q]; exact heA.congr (fun x hx1 hx2 => hfrQ x (by omega)),
          fun j hj => by
            rw [h4q, hfrQ _ (by omega), hfrQ _ (by omega)]; exact hpA j hj, hrt⟩
      have hzQ' : ZeroFrom stQ.mem hQ := by simpa [hQ, heapArg, Nat.add_assoc] using hzQ
      refine ⟨s8, _, hQ, curHeap, tokF, rLoop, by simp [s8, s7, s6, s5, s4, s3, s2, s1],
        by rw [hloopEq]; simp [s8, s7], by simp [s8, s7, s6], by simp [s8, s7, s6, s5, s4, s3, s2, s1],
        by dsimp only [hQ]; omega, ?_, by rw [hloopEq]; exact hrepQ, by rw [hloopEq]; exact hInvQ,
        hintCapF, hnumF, by rw [hloopEq]; exact hoffQ,
        fun _ => ⟨inner, norm, edges, paths, by rw [hloopEq]; exact hdescQ,
          hedMaxF, hptMaxF,
          fun x hx => by rw [show s8.mem (curHeap + 2) = stF.mem (curHeap + 2) from hfrQ (curHeap + 2) (by omega)]; exact htagEdF x hx,
          fun x hx => by rw [show s8.mem (curHeap + 4) = stF.mem (curHeap + 4) from hfrQ (curHeap + 4) (by omega)]; exact htagPtF x hx,
          htag18F, le_rfl, by dsimp only [hQ]; omega⟩,
        hzQ', hfrQ_st,
        fun a ha => (hftF a ha).imp_right (fun ⟨h1, h2⟩ => ⟨h1, by dsimp only [hQ]; omega⟩), ?_⟩
      · have hle : cycleLoopIterSpace L findSpace shiftSpace ≤
            (N + 1) * cycleLoopIterSpace L findSpace shiftSpace :=
          le_mul_of_one_le_left (Nat.zero_le _) (by omega)
        dsimp only [hQ, cycleLoopIterSpace] at hle ⊢; omega
      · rw [hloopEq]
        have hmul : (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain + 1) *
              cycleLoopIterBudget L cfg.P.d findBudget shiftBudget =
            shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain *
              cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
            cycleLoopIterBudget L cfg.P.d findBudget shiftBudget := add_one_mul _ _
        dsimp only [cycleLoopIterBudget] at hmul ⊢
        change _ + Rrep.phi root tokF stQ.mem + _ + _ + _ ≤ _
        change cF + Rrep.phi root tokF stF.mem ≤ findBudget + Rrep.phi root tok st.mem at hcF
        rw [hphiQ]; omega
    · -- CYCLE REJECTED: run `shiftCheckProc`
      have hq0 : oQ.value = 0 := by rw [hbitLoop, ite_eq_right hGood]
      have hzQ' : ZeroFrom stQ.mem hQ := by simpa [hQ, heapArg, Nat.add_assoc] using hzQ
      have ⟨_, _, _, _, _, _, _, _, hschedQ, _, _, _, _, _, _, _, _, _, _, _⟩ := hrepQ
      have htablesQ : shiftCheckTablesAt stQ.mem tok.levelsEnd (tok.levelsEnd + (cfg.P.d + 1)) quotaBase model :=
        ⟨by simpa [hlevF] using hschedQ.1, by simpa [hlevF] using hschedQ.2.1,
          fun i hi => (hfrQ_st (quotaBase + i) (by omega) (hqOut i hi)).trans (hquotas i hi)⟩
      obtain ⟨cChk, stChk, hrChk, hcChk, hmemChk⟩ :=
        shiftCheckBody_runs (w := w) (passBase := tok.levelsEnd)
          (countBase := tok.levelsEnd + (cfg.P.d + 1)) (quotaBase := quotaBase) (pos := s6.pos)
          (p := p) (ω := ω) (mem := stQ.mem) model htablesQ
          (by omega) hlevEndW (by omega) hdW (by omega)
      let retChk := (findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) model.passes).elim 0
        (fun i => if (model.chain.shiftCount i.val : ℝ) + 1 ≤
          gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val
          then i.val + 1 else 0)
      let s7Chk : State := { regs := Function.update s6.regs 25 retChk, mem := stChk.mem, pos := stChk.pos }
      have rCallChk : Runs w p ω (.call 25 shiftCheckProc [.reg 11, .reg 2, .reg 14, .reg 15, .reg 1])
          s6 .normal s7Chk (cChk + 6) :=
        runs_call_iff.mpr ⟨[tok.levelsEnd, ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊, cfg.P.d + 1,
          tok.levelsEnd + (cfg.P.d + 1), quotaBase], shiftCheckBody, .returned retChk, stChk, cChk,
          by simp [evalArgs, Expr.eval, s6, s5, s4, s3, s2, s1, hr11, hr2, hr14, hr15, hr1],
          hCheck, hrChk, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      let loopRes := Chain.Ordered.algorithm2_loopWith cfg (1 / (2 : ℝ) ^ k) model.extG model.extToInt
        model.extg model.extℓ model.chain model.branD model.passes lctOps
      let modelEnd : Alg2State cfg :=
        { model with chain := loopRes.1, branD := loopRes.2.1, passes := loopRes.2.2.1 }
      have hFailExit : retChk = 0 →
          loopRes =
            (model.chain, model.branD, model.passes,
              lctOps + 2 * ((walkEdges (algorithm1_findCycle model.chain).2.1 \
                model.chain.toTreeChain.chainTree.E).card + 1), none) →
          ∃ out cost ret curDesc tokEnd,
            Runs w p ω (.loop (.reg 16) loopBody) st .normal out cost ∧
            out.regs 4 = st.regs 4 ∧
            out.regs 17 = (if loopRes.2.2.2.2.isSome then 1 else 0) ∧
            out.regs 18 = ret ∧ out.regs 20 = curDesc ∧
            curHeap ≤ ret ∧ ret ≤ curHeap + (N + 1) * cycleLoopIterSpace L findSpace shiftSpace ∧
            Rrep.rep root modelEnd tokEnd out.mem ∧
            Inv modelEnd tokEnd out.mem ∧
            tokEnd.intCap = tok.intCap ∧
            PathTreeNumericInv tokEnd.tree tokEnd.trees B R ∧
            OffTreeRecInv modelEnd L out.mem tokEnd.edgeRecords B ∧
            (loopRes.2.2.2.2.isSome →
              ∃ inner norm edges paths,
                CycleDescriptorAt modelEnd L P out.mem curDesc ret inner norm edges paths ∧
                edges.length ≤ maxEdges ∧ paths.length ≤ maxPaths ∧
                (∀ x < 2 * edges.length, tokEnd.tag (out.mem (curDesc + 2) + x) = 0) ∧
                (∀ x < 2 * paths.length, tokEnd.tag (out.mem (curDesc + 4) + x) = 0) ∧
                (∀ a, tokEnd.tag a = 18 → a < curDesc) ∧
                curHeap ≤ curDesc ∧ curDesc + 6 ≤ ret) ∧
            ZeroFrom out.mem ret ∧
            (∀ a < curHeap, ¬ Rrep.foot root tok a → out.mem a = st.mem a) ∧
            (∀ a, Rrep.foot root tokEnd a → Rrep.foot root tok a ∨ (curHeap ≤ a ∧ a < ret)) ∧
            cost + Rrep.phi root tokEnd out.mem +
                shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) loopRes.1 *
                  cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
                toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
              (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain + 1) *
                cycleLoopIterBudget L cfg.P.d findBudget shiftBudget + 10 +
              Rrep.phi root tok st.mem +
              toolMul * loopRes.1.totalRuntime + treeMul * loopRes.1.totalTreeUpdates := by
        intro hret0 hloopEq
        let s8 : State := { s7Chk with regs := Function.update s7Chk.regs 17 0 }
        let s9 : State := { s8 with regs := Function.update s8.regs 16 0 }
        have r8 : Runs w p ω (.assign 17 (.const 0)) s7Chk .normal s8 2 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
        have r9 : Runs w p ω (.assign 16 (.const 0)) s8 .normal s9 2 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
        have rCondIn : Runs w p ω condIn s7Chk .normal s9 7 :=
          runs_cond_iff.mpr ⟨0, 5, by simp [Expr.eval, s7Chk, hret0],
            by simp only [↓reduceIte]; exact runs_seq_iff.mpr (Or.inr ⟨s8, 2, 2, r8, r9, rfl⟩),
            by simp [Expr.size]⟩
        have rSeqElse : Runs w p ω elseBranch s6 .normal s9 ((cChk + 6) + 7 + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨s7Chk, cChk + 6, 7, rCallChk, rCondIn, rfl⟩)
        have rCondOut : Runs w p ω condOut s6 .normal s9 (1 + ((cChk + 6) + 7 + 1) + 1) :=
          runs_cond_iff.mpr ⟨0, (cChk + 6) + 7 + 1, by simp [Expr.eval, s6, s5, hq0],
            by simp only [↓reduceIte]; exact rSeqElse, by simp [Expr.size]⟩
        have rExit : Runs w p ω (.loop (.reg 16) loopBody) s9 .normal s9 2 :=
          runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, s9], rfl, rfl, by simp [Expr.size]⟩)
        have rLoop : Runs w p ω (.loop (.reg 16) loopBody) st .normal s9
            (1 + (2 + ((cF + 3) + (3 + (5 + ((cQ + 6) + (8 + (1 + ((cChk + 6) + 7 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 2 + 1) :=
          runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s9, _, 2, by simp [Expr.eval, hr16], by decide,
            hchainBody rCondOut, rExit, by simp [Expr.size]⟩))
        have hs9mem : s9.mem = stQ.mem := hmemChk
        have hmEnd : modelEnd = model := by
          dsimp only [modelEnd]; rw [hloopEq]
        refine ⟨s9, _, hQ, curHeap, tokF, rLoop, by simp [s9, s8, s7Chk, s6, s5, s4, s3, s2, s1],
          by rw [hloopEq]; simp [s9, s8], by simp [s9, s8, s7Chk, s6],
          by simp [s9, s8, s7Chk, s6, s5, s4, s3, s2, s1],
          by dsimp only [hQ]; omega, ?_, by rw [hs9mem, hmEnd]; exact hrepQ,
          by rw [hs9mem, hmEnd]; exact hInvQ, hintCapF, hnumF,
          by rw [hs9mem, hmEnd]; exact hoffQ,
          by rw [hloopEq]; simp, by rw [hs9mem]; exact hzQ',
          by rw [hs9mem]; exact hfrQ_st,
          fun a ha => (hftF a ha).imp_right (fun ⟨h1, h2⟩ => ⟨h1, by dsimp only [hQ]; omega⟩), ?_⟩
        · have hle : cycleLoopIterSpace L findSpace shiftSpace ≤
              (N + 1) * cycleLoopIterSpace L findSpace shiftSpace :=
            le_mul_of_one_le_left (Nat.zero_le _) (by omega)
          dsimp only [hQ, cycleLoopIterSpace] at hle ⊢; omega
        · rw [hloopEq]
          have hmul : (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain + 1) *
                cycleLoopIterBudget L cfg.P.d findBudget shiftBudget =
              shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain *
                cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
              cycleLoopIterBudget L cfg.P.d findBudget shiftBudget := add_one_mul _ _
          dsimp only [cycleLoopIterBudget] at hmul ⊢
          change _ + Rrep.phi root tokF s9.mem + _ + _ + _ ≤ _
          change cF + Rrep.phi root tokF stF.mem ≤ findBudget + Rrep.phi root tok st.mem at hcF
          rw [hs9mem, hphiQ]; omega
      cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) model.passes with
      | none =>
        refine hFailExit (by simp [retChk, hElig]) ?_
        dsimp only [loopRes]; rw [Chain.Ordered.algorithm2_loopWith]; dsimp only; rw [dite_eq_right hGood, hElig]
      | some i =>
        by_cases hCap : (model.chain.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val
        · -- SHIFT AT LEVEL `i` AND RECURSE
          have hretPos : retChk = i.val + 1 := by simp [retChk, hElig, hCap]
          have hLt : shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
              (alg2LoopShiftStep cfg model i).chain <
              shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain :=
            Chain.Ordered.shiftRemainingBudget_lt_of_step model.chain i hCap
          have hLtS := loopStepBound_shift_lt cfg model i hElig hCap
          have hNpos : 1 ≤ N := by omega
          let s8 : State := { s7Chk with regs := Function.update s7Chk.regs 26 i.val }
          have r8 : Runs w p ω (.assign 26 (.bin .sub (.reg 25) (.const 1))) s7Chk .normal s8 4 :=
            runs_assign_iff.mpr ⟨i.val, by
              have hiW : i.val < 2 ^ w := lt_trans i.isLt hdW
              simp [Expr.eval, BinOp.eval, s7Chk, hretPos, show 1 < 2 ^ w by omega, hiW],
              rfl, rfl, rfl⟩
          have hbelowQ (a : ℕ) (ha : Rrep.foot root tokF a) : a < hQ :=
            lt_of_lt_of_le (hfootF a ha) (by dsimp only [hQ]; omega)
          have hBrI : (if i.val < cfg.P.d then model.chain.bran i.val else model.branD) < cfg.P.k := by
            split_ifs with hiD
            · exact hBr.1 i.val hiD
            · exact hBr.2
          have hPassW : model.passes i + 1 < 2 ^ w := by
            have hlt : model.passes i < ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ :=
              Nat.lt_ceil.mpr (findEligibleLevel_spec hElig).1
            omega
          obtain ⟨hS, cS, stS, tokS, hrS, hhSLo, hhSHi, hlevS, hintCapS, hrepS, hInvS, hnumS, hoffS, hBdS,
              hzS, hfrS, hftS, hcS⟩ :=
            hShiftSpec root hQ s8.pos i ω stQ.mem model tokF B R hCap hBrI hBr.1
              (hquotasW i.val (Nat.lt_succ_iff.mp i.isLt)) hPassW
              hrepQ hInvQ hLoopInv hlogW hcapTree hnumF hoffQ hBdQ hCapFacts hbelowQ
              hzQ' (by dsimp only [hQ, cycleLoopIterSpace] at h1Iter ⊢; omega)
          let s9 : State := { regs := Function.update s8.regs 18 hS, mem := stS.mem, pos := stS.pos }
          have r9 : Runs w p ω (.call 18 shiftLevelProc [.reg 0, .reg 26, .reg 18]) s8 .normal s9 (cS + 4) :=
            runs_call_iff.mpr ⟨[root, i.val, hQ], bShift, .returned hS, stS, cS,
              by simp [evalArgs, Expr.eval, s8, s7Chk, s6, s5, s4, s3, s2, s1, hr0],
              hbShift, by simpa [s8, s7Chk, hmemChk] using hrS, rfl, rfl,
              by simp [argsSize, Expr.size]; omega⟩
          have rCondIn : Runs w p ω condIn s7Chk .normal s9 (1 + (4 + (cS + 4) + 1) + 1) :=
            runs_cond_iff.mpr ⟨i.val + 1, 4 + (cS + 4) + 1, by simp [Expr.eval, s7Chk, hretPos],
              by simp only [Nat.succ_ne_zero, ↓reduceIte]
                 exact runs_seq_iff.mpr (Or.inr ⟨s8, 4, cS + 4, r8, r9, rfl⟩),
              by simp [Expr.size]⟩
          have rSeqElse : Runs w p ω elseBranch s6 .normal s9 ((cChk + 6) + (1 + (4 + (cS + 4) + 1) + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨s7Chk, cChk + 6, _, rCallChk, rCondIn, rfl⟩)
          have rCondOut : Runs w p ω condOut s6 .normal s9 (1 + ((cChk + 6) + (1 + (4 + (cS + 4) + 1) + 1) + 1) + 1) :=
            runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, s6, s5, hq0],
              by simp only [↓reduceIte]; exact rSeqElse, by simp [Expr.size]⟩
          have hfootS (a : ℕ) (ha : Rrep.foot root tokS a) : a < hS := by
            rcases hftS a ha with h0 | ⟨_, hhi⟩
            · exact lt_of_lt_of_le (hbelowQ a h0) hhSLo
            · exact hhi
          have hqOutF (j : ℕ) (hj : j ≤ cfg.P.d) : ¬ Rrep.foot root tokF (quotaBase + j) := by
            intro hf
            rcases hftF _ hf with h0 | ⟨hlo, _⟩
            · exact hqOut j hj h0
            · omega
          have hqOutS (j : ℕ) (hj : j ≤ cfg.P.d) : ¬ Rrep.foot root tokS (quotaBase + j) := by
            intro hf
            rcases hftS _ hf with h0 | ⟨hlo, _⟩
            · exact hqOutF j hj h0
            · dsimp only [hQ] at hlo; omega
          have hquotasS (j : ℕ) (hj : j ≤ cfg.P.d) :
              stS.mem (quotaBase + j) =
                shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
                  (alg2LoopShiftStep cfg model i).chain.rebuildCount j := by
            have h1 := hfrS (quotaBase + j) (by dsimp only [hQ]; omega) (hqOutF j hj)
            have h2 := hfrQ_st (quotaBase + j) (by omega) (hqOut j hj)
            rw [h1, h2, hquotas j hj, alg2LoopShiftStep]
            dsimp only
            rw [show (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1.rebuildCount =
                model.chain.rebuildCount from funext (ordAlgorithm1_shift_rebuildCount model.chain i.val)]
          have hroomS : hS + ((N - 1) + 1) * cycleLoopIterSpace L findSpace shiftSpace < 2 ^ w := by
            have hN1 : (N - 1) + 1 = N := by omega
            rw [hN1]
            have : hS ≤ curHeap + cycleLoopIterSpace L findSpace shiftSpace := by
              dsimp only [hQ, cycleLoopIterSpace] at hhSHi ⊢; omega
            have hmul : (N + 1) * cycleLoopIterSpace L findSpace shiftSpace =
                cycleLoopIterSpace L findSpace shiftSpace + N * cycleLoopIterSpace L findSpace shiftSpace := by
              ring
            omega
          let lctOps' := lctOps + 2 * ((walkEdges (algorithm1_findCycle model.chain).2.1 \
            model.chain.toTreeChain.chainTree.E).card + 1)
          obtain ⟨out, cRest, ret, curDesc, tokEnd, hrRest, hr4End, hr17End, hr18End, hr20End,
              hretLo, hretHi, hrepEnd, hInvEnd, hintCapEnd, hnumEnd, hoffEnd, hdescEnd, hzEnd, hfrEnd, hftEnd,
              hcEnd⟩ :=
            ih (N - 1) (by omega) s9 (alg2LoopShiftStep cfg model i) tokS B R lctOps'
              (by omega)
              (by simp [s9, s8, s7Chk, s6, s5, s4, s3, s2, s1, hr0])
              (by simp [s9, s8, s7Chk, s6, s5, s4, s3, s2, s1, hr1])
              (by simp [s9, s8, s7Chk, s6, s5, s4, s3, s2, s1, hr2])
              (by simp [s9, s8, s7Chk, s6, s5, s4, s3, s2, s1, hr3])
              (by simp [s9, s8, s7Chk, s6, s5, s4, s3, s2, s1, hr11, hlevS, hlevF])
              (by simp [s9, s8, s7Chk, s6, s5, s4, s3, s2, s1, hr12])
              (by simp [s9, s8, s7Chk, s6, s5, s4, s3, s2, s1, hr14])
              (by simp [s9, s8, s7Chk, s6, s5, s4, s3, s2, s1, hr15, hlevS, hlevF])
              (by simp [s9, s8, s7Chk, s6, s5, s4, s3, s2, s1, hr16])
              hrepS hInvS (hLoopInv.shift hV i.val (Nat.lt_succ_iff.mp i.isLt)) hnumS hoffS hBdS
              (hCapFacts.congr (fun j _ => congrFun (alg2LoopShiftStep_lvlM_N0 cfg model i).1 j)
                (alg2LoopShiftStep_lvlM_N0 cfg model i).2)
              hcapEval hcapTree hlogW hlenNN
              hfootS (by simp only [s9, Function.update_self]; dsimp only [hQ] at hhSLo; omega) hquotasS
              (fun j hj => by
                rw [alg2LoopShiftStep]; dsimp only
                rw [show (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1.rebuildCount =
                    model.chain.rebuildCount from funext (ordAlgorithm1_shift_rebuildCount model.chain i.val)]
                exact hquotasW j hj)
              (branchesLtK_shiftStep hBr i) hqOutS hzS hroomS
          have hs9r18 : s9.regs 18 = hS := by simp [s9]
          rw [hs9r18] at hretLo hretHi hdescEnd hfrEnd hftEnd
          have hloopEq : Chain.Ordered.algorithm2_loopWith cfg (1 / (2 : ℝ) ^ k) model.extG model.extToInt
              model.extg model.extℓ model.chain model.branD model.passes lctOps =
              Chain.Ordered.algorithm2_loopWith cfg (1 / (2 : ℝ) ^ k) (alg2LoopShiftStep cfg model i).extG
                (alg2LoopShiftStep cfg model i).extToInt (alg2LoopShiftStep cfg model i).extg
                (alg2LoopShiftStep cfg model i).extℓ (alg2LoopShiftStep cfg model i).chain
                (alg2LoopShiftStep cfg model i).branD (alg2LoopShiftStep cfg model i).passes lctOps' := by
            conv_lhs => rw [Chain.Ordered.algorithm2_loopWith]
            dsimp only [alg2LoopShiftStep, lctOps']
            rw [dite_eq_right hGood, hElig]; dsimp only; rw [dite_eq_left hCap]
          have rLoop : Runs w p ω (.loop (.reg 16) loopBody) st .normal out
              (1 + (2 + ((cF + 3) + (3 + (5 + ((cQ + 6) + (8 + (1 + ((cChk + 6) + (1 + (4 + (cS + 4) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + cRest + 1) :=
            runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s9, _, cRest, by simp [Expr.eval, hr16], by decide,
              hchainBody rCondOut, hrRest, by simp [Expr.size]⟩))
          refine ⟨out, _, ret, curDesc, tokEnd, rLoop,
            hr4End.trans (by simp [s9, s8, s7Chk, s6, s5, s4, s3, s2, s1]),
            by rw [hloopEq]; exact hr17End, hr18End, hr20End,
            le_trans (by dsimp only [hQ] at hhSLo ⊢; omega) hretLo, ?_,
            by rw [hloopEq]; exact hrepEnd, by rw [hloopEq]; exact hInvEnd,
            hintCapEnd.trans (hintCapS.trans hintCapF), hnumEnd,
            by rw [hloopEq]; exact hoffEnd,
            fun hSome => by
              rw [hloopEq] at hSome
              obtain ⟨in', nm', ed', pt', hd', hmE', hmP', htE', htP', ht18', hcLo', hcHi'⟩ := hdescEnd hSome
              exact ⟨in', nm', ed', pt', by rw [hloopEq]; exact hd', hmE', hmP', htE', htP', ht18',
                le_trans (by dsimp only [hQ] at hhSLo ⊢; omega) hcLo', hcHi'⟩,
            hzEnd, ?_, ?_, ?_⟩
          · have hN1 : (N - 1) + 1 = N := by omega
            rw [hN1] at hretHi
            have : hS ≤ curHeap + cycleLoopIterSpace L findSpace shiftSpace := by
              dsimp only [hQ, cycleLoopIterSpace] at hhSHi ⊢; omega
            have hmul : (N + 1) * cycleLoopIterSpace L findSpace shiftSpace =
                cycleLoopIterSpace L findSpace shiftSpace + N * cycleLoopIterSpace L findSpace shiftSpace := by
              ring
            omega
          · intro a ha hnf
            have hnfF : ¬ Rrep.foot root tokF a := by
              intro hf; rcases hftF a hf with h0 | ⟨hlo, _⟩
              · exact hnf h0
              · omega
            have hnfS : ¬ Rrep.foot root tokS a := by
              intro hf; rcases hftS a hf with h0 | ⟨hlo, _⟩
              · exact hnfF h0
              · dsimp only [hQ] at hlo; omega
            have h1 := hfrEnd a (lt_of_lt_of_le ha (by dsimp only [hQ] at hhSLo ⊢; omega)) hnfS
            have h2 := hfrS a (lt_of_lt_of_le ha (by dsimp only [hQ]; omega)) hnfF
            exact h1.trans (h2.trans (hfrQ_st a ha hnf))
          · intro a ha
            rcases hftEnd a ha with h0 | ⟨hlo, hhi⟩
            · rcases hftS a h0 with h1 | ⟨hlo1, hhi1⟩
              · rcases hftF a h1 with h2 | ⟨hlo2, hhi2⟩
                · exact Or.inl h2
                · exact Or.inr ⟨hlo2, lt_of_lt_of_le hhi2 (by dsimp only [hQ] at hhSLo ⊢; omega)⟩
              · exact Or.inr ⟨le_trans (by dsimp only [hQ]; omega) hlo1, lt_of_lt_of_le hhi1 hretLo⟩
            · exact Or.inr ⟨le_trans (by dsimp only [hQ] at hhSLo ⊢; omega) hlo, hhi⟩
          · rw [hloopEq]
            have hmono : (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
                  (alg2LoopShiftStep cfg model i).chain + 1) *
                  cycleLoopIterBudget L cfg.P.d findBudget shiftBudget ≤
                shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain *
                  cycleLoopIterBudget L cfg.P.d findBudget shiftBudget :=
              Nat.mul_le_mul_right _ hLt
            have hmul : (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain + 1) *
                  cycleLoopIterBudget L cfg.P.d findBudget shiftBudget =
                shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain *
                  cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
                cycleLoopIterBudget L cfg.P.d findBudget shiftBudget := add_one_mul _ _
            have hRtStep : toolMul * ((alg2LoopShiftStep cfg model i).chain.totalRuntime -
                  model.chain.totalRuntime) + toolMul * model.chain.totalRuntime =
                toolMul * (alg2LoopShiftStep cfg model i).chain.totalRuntime := by
              rcases hMono with rfl | hM
              · simp
              · rw [← Nat.mul_add]; congr 1
                exact Nat.sub_add_cancel
                  (algorithm1_shift_totalRuntime_mono hM cfg.L cfg.P model.chain i.val)
            have hTuStep : treeMul * ((alg2LoopShiftStep cfg model i).chain.totalTreeUpdates -
                  model.chain.totalTreeUpdates) + treeMul * model.chain.totalTreeUpdates =
                treeMul * (alg2LoopShiftStep cfg model i).chain.totalTreeUpdates := by
              rw [← Nat.mul_add]; congr 1
              exact Nat.sub_add_cancel
                (algorithm1_shift_totalTreeUpdates_mono cfg.T cfg.L cfg.P model.chain i.val)
            dsimp only [cycleLoopIterBudget] at hmul hmono hcEnd ⊢
            change _ + Rrep.phi root tokEnd out.mem + _ + _ + _ ≤ _
            change cRest + Rrep.phi root tokEnd out.mem + _ + _ + _ ≤ _ + Rrep.phi root tokS stS.mem + _ + _ at hcEnd
            change cS + Rrep.phi root tokS stS.mem ≤
              shiftBudget +
                toolMul * ((alg2LoopShiftStep cfg model i).chain.totalRuntime - model.chain.totalRuntime) +
                treeMul * ((alg2LoopShiftStep cfg model i).chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
                Rrep.phi root tokF stQ.mem at hcS
            change cF + Rrep.phi root tokF stF.mem ≤ findBudget + Rrep.phi root tok st.mem at hcF
            rw [hphiQ] at hcS
            omega
        · refine hFailExit (by simp [retChk, hElig, hCap]) ?_
          dsimp only [loopRes]; rw [Chain.Ordered.algorithm2_loopWith]; dsimp only; rw [dite_eq_right hGood, hElig]; dsimp only; rw [dite_eq_right hCap]

end MinCostFlow.MinRatio
