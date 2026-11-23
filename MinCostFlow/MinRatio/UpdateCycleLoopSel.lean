module

public import MinCostFlow.MinRatio.UpdateCycleLoopSelInd
import WordRAM.Tactic

/-!
# Select-aware execution proof for the inner candidate-cycle and shift loop (`UpdateCycleLoopSel`)

Wraps `updateCycleLoop_ind_sel` (`UpdateCycleLoopSelInd.lean`) into `updateCycleLoopBody_runs_sel`,
proving that `updateCycleLoopBody` implements `Chain.Ordered.algorithm2_loopWith cfg (1 / 2^k)`
while maintaining `SolverLevelCapsInv`, `SolverSelectInv`,
`sg.reembPot = chainReembPot pot model.chain`, `SolverSelectRegionInv`, and `DeepInv`, with heap-backed `FindCycleStepSpecHeap`
and select-aware `ShiftLevelStepSpecWKFBLSel`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program

/-- Select-aware credit-bearing execution of `updateCycleLoopBody`: implements
`Chain.Ordered.algorithm2_loopWith cfg (1 / 2^k)`, preserving `SolverLevelCapsInv`,
`SolverSelectInv`, `sg.reembPot = chainReembPot pot model.chain`, `SolverSelectRegionInv`, and
`DeepInv`, and threading
`Rrep.phi + K * sg.reembPot` along with `toolMul * Δ totalRuntime + treeMul * Δ totalTreeUpdates`. -/
theorem updateCycleLoopBody_runs_sel
    {w L P m U V psi k qHdr epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec
      intCapMax forestEdgeCap vCap eCap dMul kOff K E pLast slot
      findCycleProc updateQualityProc shiftCheckProc shiftLevelProc
      findSpace findBudget maxEdges maxPaths shiftSpace shiftBudget
      toolMul treeMul root quotaBase descOut heap pos : ℕ}
    {cfg : Alg2Config} {G : MGraph} {pot : cfg.T.State → ℕ}
    {DeepInv : ChainState cfg.T cfg.P → Prop}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {sg : SelectGhost}
    {B R : ℤ} {lctOps : ℕ}
    (hMono : toolMul = 0 ∨ ToolCostMono cfg.T) (hV : cfg.ValidOrdNoHidden)
    (hα : cfg.α = Num.IPM.alphaPrime m U / 8)
    (hFind : FindCycleStepSpecHeap w L P m V psi qHdr epsExp drainUnit dMul kOff cfg Rcore p
      findCycleProc findSpace findBudget maxEdges maxPaths)
    (hQual : ∀ inner norm, MeetsContract w p updateQualityProc
      (updateQualityFromNormContract w 4 m U k P inner norm))
    (hCheck : p.procs[shiftCheckProc]? = some shiftCheckBody)
    (hShift : ShiftLevelStepSpecWKFBLSel w L P m V psi qHdr epsExp drainUnit capExp limbMul
      capLimit wordExp stretchPrec intCapMax forestEdgeCap vCap eCap dMul kOff K E pLast slot cfg G pot
      DeepInv Rcore p shiftLevelProc shiftSpace shiftBudget toolMul treeMul)
    (hMaxEdges1 : 1 ≤ maxEdges) (hMaxEP2 : 2 * maxEdges ≤ maxPaths)
    (hEmbBd : ∀ ch, Chain.Ordered.ShiftLoopChainInv cfg ch →
      ∀ i < cfg.P.d, ∀ e ∈ (ch.toTreeChain.activeCore i).E \ (ch.toTreeChain.activeS i).E,
        (ch.toTreeChain.activeEmb i e).length + 1 ≤ maxEdges)
    (hFEdgeCap : 2 * G.n ≤ forestEdgeCap)
    (hDeepShift : ∀ ch, Chain.Ordered.ShiftLoopChainInv cfg ch → DeepInv ch →
      ∀ i ≤ cfg.P.d, DeepInv (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i).1)
    (hDeepToModel : ∀ (stM : Alg2State cfg) (i : Fin (cfg.P.d + 1)), i.val < cfg.P.d →
      Chain.Ordered.ShiftLoopChainInv cfg stM.chain → DeepInv stM.chain →
      ShiftDeepModelInv w L P wordExp stretchPrec stM i)
    (hw11 : 11 < 2 ^ w) (h5L1W : 5 * L + 1 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) (hqW : k + Num.IPM.alphaExponent m U + 3 < 2 ^ w)
    (hpsiLimW : ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ < 2 ^ w)
    (hrep : (solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).rep root model tok mem)
    (hCaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hLay : SolverLevelLayoutAt vCap eCap tok mem)
    (hSel : SolverSelectInv G L P m dMul kOff tok.table model
      ((solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).foot root tok)
      (LevelMetaFoot tok) sg mem)
    (hReemb : sg.reembPot = chainReembPot pot model.chain)
    (hReg : SolverSelectRegionInv G L P m E pLast slot vCap eCap model
      ((solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).foot root tok) tok sg mem)
    (hDeep : DeepInv model.chain)
    (hIntCap : tok.intCap ≤ intCapMax)
    (hGn : (model.chain.G 0).n ≤ G.n)
    (hLoopInv : Chain.Ordered.ShiftLoopChainInv cfg model.chain)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hoff : OffTreeRecInv model L mem tok.edgeRecords B)
    (hBd : OffTreeRecBound model L mem tok.edgeRecords B)
    (hCapFacts : WireCapFacts capExp limbMul L capLimit model)
    (hcapEval : 2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ))
    (hcapTree : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hlogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hlenNN : ∀ e ∈ model.extG.E, 0 ≤ model.extℓ e)
    (hbelow : ∀ a,
      (solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).foot root tok a ∨ sg.owned a →
      a < heap)
    (hqBelow : quotaBase + cfg.P.d < heap)
    (hquotas : ∀ i ≤ cfg.P.d, mem (quotaBase + i) =
      shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i)
    (hquotasW : ∀ i ≤ cfg.P.d,
      shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i < 2 ^ w)
    (hBr : BranchesLtK cfg model)
    (hqOut : ∀ i ≤ cfg.P.d,
      ¬ ((solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).foot root tok (quotaBase + i) ∨
        sg.owned (quotaBase + i)))
    (hdescBelow : descOut + 1 < heap)
    (hdescOut0 :
      ¬ ((solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).foot root tok descOut ∨
        sg.owned descOut))
    (hdescOut1 :
      ¬ ((solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore).foot root tok (descOut + 1) ∨
        sg.owned (descOut + 1)))
    (hz : ZeroFrom mem heap)
    (hroom : heap + (loopStepBound cfg model + 1) *
      cycleLoopIterSpace L findSpace shiftSpace < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore
    let N := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain
    let loopRes := Chain.Ordered.algorithm2_loopWith cfg (1 / (2 : ℝ) ^ k) model.extG model.extToInt
      model.extg model.extℓ model.chain model.branD model.passes lctOps
    let modelEnd : Alg2State cfg :=
      { model with
        chain := loopRes.1
        branD := loopRes.2.1
        passes := loopRes.2.2.1 }
    ∃ ret cost out tokEnd sgEnd,
      Runs w p ω (updateCycleLoopBody findCycleProc updateQualityProc shiftCheckProc shiftLevelProc)
        (startState [root, quotaBase, ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊,
          k + Num.IPM.alphaExponent m U + 3, descOut, heap] mem pos)
        (.returned ret) out cost ∧
      heap ≤ ret ∧ ret ≤ heap + (loopStepBound cfg model + 1) * cycleLoopIterSpace L findSpace shiftSpace ∧
      out.mem descOut = (if loopRes.2.2.2.2.isSome then 1 else 0) ∧
      Rrep.rep root modelEnd tokEnd out.mem ∧
      SolverLevelCapsInv P V vCap eCap modelEnd tokEnd out.mem ∧
      SolverLevelLayoutAt vCap eCap tokEnd out.mem ∧
      SolverSelectInv G L P m dMul kOff tokEnd.table modelEnd (Rrep.foot root tokEnd)
        (LevelMetaFoot tokEnd) sgEnd out.mem ∧
      sgEnd.reembPot = chainReembPot pot modelEnd.chain ∧
      SolverSelectRegionInv G L P m E pLast slot vCap eCap modelEnd (Rrep.foot root tokEnd) tokEnd
        sgEnd out.mem ∧
      DeepInv modelEnd.chain ∧
      tokEnd.intCap = tok.intCap ∧
      PathTreeNumericInv tokEnd.tree tokEnd.trees B R ∧
      OffTreeRecInv modelEnd L out.mem tokEnd.edgeRecords B ∧
      (loopRes.2.2.2.2.isSome →
        ∃ inner norm edges paths,
          CycleDescriptorAt modelEnd L P out.mem (out.mem (descOut + 1)) ret inner norm edges paths ∧
          edges.length ≤ maxEdges ∧ paths.length ≤ maxPaths ∧
          (∀ x < 2 * edges.length, tokEnd.tag (out.mem (out.mem (descOut + 1) + 2) + x) = 0) ∧
          (∀ x < 2 * paths.length, tokEnd.tag (out.mem (out.mem (descOut + 1) + 4) + x) = 0) ∧
          (∀ a, tokEnd.tag a = 18 → a < out.mem (descOut + 1)) ∧
          heap ≤ out.mem (descOut + 1) ∧ out.mem (descOut + 1) + 6 ≤ ret) ∧
      ZeroFrom out.mem ret ∧
      (∀ a < heap, ¬ (Rrep.foot root tok a ∨ sg.owned a) → a ≠ descOut → a ≠ descOut + 1 →
        out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tokEnd a ∨ sgEnd.owned a →
        (Rrep.foot root tok a ∨ sg.owned a) ∨ (heap ≤ a ∧ a < ret)) ∧
      cost + (Rrep.phi root tokEnd out.mem + K * sgEnd.reembPot) +
          shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) loopRes.1 *
            cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
          toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
        (N + 1) * cycleLoopIterBudget L cfg.P.d findBudget shiftBudget + 80 +
        (Rrep.phi root tok mem + K * sg.reembPot) +
        toolMul * loopRes.1.totalRuntime + treeMul * loopRes.1.totalTreeUpdates := by
  dsimp only
  let Rrep := solverStateRep cfg L P m V psi qHdr epsExp drainUnit Rcore
  let N := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain
  have hlocR := solverStateRep_local cfg L P m V psi qHdr epsExp drainUnit hlocalCore
  have hheapW : heap < 2 ^ w := by
    have : 1 * cycleLoopIterSpace L findSpace shiftSpace ≤
        (loopStepBound cfg model + 1) * cycleLoopIterSpace L findSpace shiftSpace :=
      Nat.mul_le_mul_right _ (by omega)
    dsimp only [cycleLoopIterSpace] at hroom this; omega
  have ⟨hrootDir, _, hnumH, hchainP, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, _, _, t5, _⟩ := htags
  have hltFoot {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < heap :=
    hbelow a (Or.inl (Or.inl (hOwn a (ht ▸ hv))))
  have hmR0 : mem root = tok.handle := by simpa using hrootDir 0 (by simp [List.length])
  have hmR2 : mem (root + 2) = tok.levelsEnd := by simpa using hrootDir 2 (by simp [List.length])
  have hmH5 : mem (tok.handle + 5) = L := by simpa using hnumH 0 (by simp [List.length])
  have hmH11 : mem (tok.handle + 11) = cfg.P.d := by
    simpa [show tok.handle + 9 + 2 = tok.handle + 11 by omega] using hchainP 2 (by simp [List.length])
  have hR2W : root + 2 < 2 ^ w := lt_trans (hltFoot (t1 2 (by omega)) (by decide)) hheapW
  have hH5W : tok.handle + 5 < 2 ^ w := lt_trans (hltFoot (t2 5 (by omega)) (by decide)) hheapW
  have hH11W : tok.handle + 11 < 2 ^ w := lt_trans (hltFoot (t2 11 (by omega)) (by decide)) hheapW
  have hLevD1W : tok.levelsEnd + (cfg.P.d + 1) < 2 ^ w :=
    lt_trans (hltFoot (t5 (cfg.P.d + 1) (by omega)) (by decide)) hheapW
  let s0 := startState [root, quotaBase, ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊,
    k + Num.IPM.alphaExponent m U + 3, descOut, heap] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 10 tok.handle }
  let s2 : State := { s1 with regs := Function.update s1.regs 11 tok.levelsEnd }
  let s3 : State := { s2 with regs := Function.update s2.regs 12 L }
  let s4 : State := { s3 with regs := Function.update s3.regs 13 cfg.P.d }
  let s5 : State := { s4 with regs := Function.update s4.regs 14 (cfg.P.d + 1) }
  let s6 : State := { s5 with regs := Function.update s5.regs 15 (tok.levelsEnd + (cfg.P.d + 1)) }
  let s7 : State := { s6 with regs := Function.update s6.regs 16 1 }
  let s8 : State := { s7 with regs := Function.update s7.regs 17 0 }
  let s9 : State := { s8 with regs := Function.update s8.regs 18 heap }
  let s10 : State := { s9 with regs := Function.update s9.regs 20 heap }
  have r1 : Runs w p ω (.assign 10 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s0, startState, hmR0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 0) (.const 2)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨tok.levelsEnd, by
      simp [Expr.eval, BinOp.eval, s1, s0, startState, show 2 < 2 ^ w by omega, hR2W, hmR2],
      rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 10) (.const 5)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨L, by
      simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, show 5 < 2 ^ w by omega, hH5W, hmH5],
      rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 10) (.const 11)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨cfg.P.d, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, hw11, hH11W, hmH11],
      rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 14 (.bin .add (.reg 13) (.const 1))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨cfg.P.d + 1, by
      simp [Expr.eval, BinOp.eval, s4, show 1 < 2 ^ w by omega, hdW], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 15 (.bin .add (.reg 11) (.reg 14))) s5 .normal s6 4 :=
    runs_assign_iff.mpr ⟨tok.levelsEnd + (cfg.P.d + 1), by
      simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, hLevD1W], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 16 (.const 1)) s6 .normal s7 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, show 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 17 (.const 0)) s7 .normal s8 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 18 (.reg 5)) s8 .normal s9 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState],
      rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 20 (.reg 5)) s9 .normal s10 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState],
      rfl, rfl, rfl⟩
  have hs10r18 : s10.regs 18 = heap := by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState]
  obtain ⟨outL, cL, ret, curDesc, tokEnd, sgEnd, hrL, hr4L, hr17L, hr18L, hr20L,
      hretLo, hretHi, hrepEnd, hCapsEnd, hLayEnd, hSelEnd, hReembEnd, hRegEnd, hDeepEnd, hintCapEnd,
      hnumEnd, hoffEnd, hdescEnd, hzEnd, hfrEnd, hftEnd, hcEnd⟩ :=
    updateCycleLoop_ind_sel hlocalCore hMono hV hα hFind hQual hCheck hShift
      hMaxEdges1 hMaxEP2 hEmbBd hFEdgeCap hDeepShift hDeepToModel
      (by omega) h5L1W hdW hqW hpsiLimW
      (loopStepBound cfg model) s10 model tok sg B R lctOps le_rfl
      (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
      (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2])
      (by simp [s10, s9, s8, s7, s6, s5, s4, s3])
      (by simp [s10, s9, s8, s7, s6, s5])
      (by simp [s10, s9, s8, s7, s6])
      (by simp [s10, s9, s8, s7])
      hrep hCaps hLay hSel hReemb hReg hDeep hIntCap hGn hLoopInv hnum hoff hBd hCapFacts
      hcapEval hcapTree hlogW hlenNN
      (by simpa [hs10r18] using hbelow) (by simpa [hs10r18] using hqBelow)
      hquotas hquotasW hBr hqOut (by rw [hs10r18]; exact hz) (by simpa [hs10r18] using hroom)
  rw [hs10r18] at hretLo hretHi hdescEnd hfrEnd hftEnd
  have hr4Eq : outL.regs 4 = descOut :=
    hr4L.trans (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
  let loopRes := Chain.Ordered.algorithm2_loopWith cfg (1 / (2 : ℝ) ^ k) model.extG model.extToInt
    model.extg model.extℓ model.chain model.branD model.passes lctOps
  let foundBit := if loopRes.2.2.2.2.isSome then 1 else 0
  let out1 : State := { outL with mem := Function.update outL.mem descOut foundBit }
  let out2 : State := { out1 with mem := Function.update out1.mem (descOut + 1) curDesc }
  have rSt1 : Runs w p ω (.store (.reg 4) (.reg 17)) outL .normal out1 3 :=
    runs_store_iff.mpr ⟨descOut, foundBit, by simp [Expr.eval, hr4Eq],
      by simp [Expr.eval, hr17L, foundBit, loopRes], rfl, rfl, rfl⟩
  have rSt2 : Runs w p ω (.store (.bin .add (.reg 4) (.const 1)) (.reg 20)) out1 .normal out2 5 :=
    runs_store_iff.mpr ⟨descOut + 1, curDesc, by
      simp [Expr.eval, BinOp.eval, out1, hr4Eq, show 1 < 2 ^ w by omega, show descOut + 1 < 2 ^ w by omega],
      by simp [Expr.eval, out1, hr20L], rfl, rfl, rfl⟩
  have rRet : Runs w p ω (.ret (.reg 18)) out2 (.returned ret) out2 2 :=
    runs_ret_iff.mpr ⟨ret, by simp [Expr.eval, out2, out1, hr18L], rfl, rfl, rfl⟩
  have rFull : Runs w p ω (updateCycleLoopBody findCycleProc updateQualityProc shiftCheckProc shiftLevelProc)
      s0 (.returned ret) out2
      (3 + (5 + (5 + (5 + (4 + (4 + (2 + (2 + (2 + (2 + (cL + (3 + (5 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 4, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 4, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 2, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 2, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 2, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 2, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨outL, cL, _, hrL,
    runs_seq_iff.mpr (Or.inr ⟨out1, 3, _, rSt1,
    runs_seq_iff.mpr (Or.inr ⟨out2, 5, 2, rSt2, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hmemOut2 (a : ℕ) (h0 : a ≠ descOut) (h1 : a ≠ descOut + 1) : out2.mem a = outL.mem a := by
    dsimp only [out2, out1]
    rw [Function.update_of_ne h1, Function.update_of_ne h0]
  have hagAll (a : ℕ) (ha : Rrep.foot root tokEnd a ∨ sgEnd.owned a) : outL.mem a = out2.mem a := by
    have h0 : a ≠ descOut := by
      intro h; subst h; rcases hftEnd _ ha with h' | ⟨hlo, _⟩
      · exact hdescOut0 h'
      · omega
    have h1 : a ≠ descOut + 1 := by
      intro h; subst h; rcases hftEnd _ ha with h' | ⟨hlo, _⟩
      · exact hdescOut1 h'
      · omega
    exact (hmemOut2 a h0 h1).symm
  have hagFoot (a : ℕ) (ha : Rrep.foot root tokEnd a) : outL.mem a = out2.mem a :=
    hagAll a (Or.inl ha)
  have hrep2 : Rrep.rep root { model with chain := loopRes.1, branD := loopRes.2.1, passes := loopRes.2.2.1 } tokEnd out2.mem :=
    (hlocR root _ tokEnd outL.mem out2.mem hagFoot).1 hrepEnd
  have hmeta2 : PreservesLevelMeta tokEnd tokEnd outL.mem out2.mem :=
    (PreservesLevelMeta.refl tokEnd outL.mem).congr_mem_right fun a ht =>
      (hagFoot a (LevelMetaFoot.mem_foot hrepEnd ht)).symm
  have hCaps2 : SolverLevelCapsInv P V vCap eCap
      { model with chain := loopRes.1, branD := loopRes.2.1, passes := loopRes.2.2.1 } tokEnd out2.mem :=
    hmeta2.to_capsInv hCapsEnd rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) rfl
  have hSel2 : SolverSelectInv G L P m dMul kOff tokEnd.table
      { model with chain := loopRes.1, branD := loopRes.2.1, passes := loopRes.2.2.1 }
      (Rrep.foot root tokEnd) (LevelMetaFoot tokEnd) sgEnd out2.mem := by
    obtain ⟨hSt, hDisj, hMod⟩ := hSelEnd
    refine ⟨fun mem' hmem' => hSt mem' fun a ha => ?_, hDisj, hMod⟩
    rw [hmem' a ha]
    exact (hagAll a (ha.imp (fun hm => LevelMetaFoot.mem_foot hrepEnd hm) id)).symm
  have hReg2 : SolverSelectRegionInv G L P m E pLast slot vCap eCap
      { model with chain := loopRes.1, branD := loopRes.2.1, passes := loopRes.2.2.1 }
      (Rrep.foot root tokEnd) tokEnd sgEnd out2.mem :=
    hRegEnd.congr hCapsEnd.1 hmeta2 hRegEnd.owned_not_foot
      (fun a ho => (hagAll a (Or.inr ho)).symm) rfl rfl rfl
  have hphi2 : Rrep.phi root tokEnd out2.mem = Rrep.phi root tokEnd outL.mem :=
    ((hlocR root { model with chain := loopRes.1, branD := loopRes.2.1, passes := loopRes.2.2.1 }
      tokEnd outL.mem out2.mem hagFoot).2).symm
  have hoff2 : OffTreeRecInv { model with chain := loopRes.1, branD := loopRes.2.1, passes := loopRes.2.2.1 }
      L out2.mem tokEnd.edgeRecords B :=
    offTreeRecInv_of_agree hrepEnd hoffEnd fun a ha => by
      have hnz : tokEnd.tag a ≠ 0 := by rcases ha with h | h <;> omega
      have hown : tokEnd.owned a := hrepEnd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a hnz
      exact (hagFoot a (Or.inl hown)).symm
  refine ⟨ret, _, out2, tokEnd, sgEnd, rFull, hretLo, hretHi,
    by dsimp only [out2, out1]; rw [Function.update_of_ne (by omega), Function.update_self],
    hrep2, hCaps2, hmeta2.to_levelLayout hCapsEnd.1 hLayEnd, hSel2, hReembEnd, hReg2, hDeepEnd, hintCapEnd, hnumEnd, hoff2, ?_, ?_, ?_, hftEnd, ?_⟩
  · intro hSome
    obtain ⟨inner, norm, edges, paths, hdesc, hmE, hmP, htE, htP, ht18, hcLo, hcHi⟩ := hdescEnd hSome
    have hptr : out2.mem (descOut + 1) = curDesc := by dsimp only [out2]; exact Function.update_self _ _ _
    rw [hptr]
    obtain ⟨h3d, h5d, h6d, hiLo, hnLo, heLo, hpLo, hiE, hnE, heE, hpE, hnn, hiA, hnA, hiEq, hnEq, heA, hpA, hrt⟩ := hdesc
    have hge (x : ℕ) (hx : curDesc ≤ x) : out2.mem x = outL.mem x := hmemOut2 x (by omega) (by omega)
    refine ⟨inner, norm, edges, paths, ⟨(hge _ (by omega)).trans h3d, (hge _ (by omega)).trans h5d, h6d,
      by rw [hge curDesc le_rfl]; exact hiLo, by rw [hge _ (by omega)]; exact hnLo,
      by rw [hge _ (by omega)]; exact heLo, by rw [hge _ (by omega)]; exact hpLo,
      by rw [hge curDesc le_rfl]; exact hiE, by rw [hge _ (by omega)]; exact hnE,
      by rw [hge _ (by omega)]; exact heE, by rw [hge _ (by omega)]; exact hpE,
      hnn, by rw [hge curDesc le_rfl]; exact hiA.congr (fun j _ => hge _ (by omega)),
      by rw [hge _ (by omega)]; exact hnA.congr (fun j _ => hge _ (by omega)),
      hiEq, hnEq,
      by rw [hge _ (by omega)]; exact heA.congr (fun x hx1 _ => hge x (by omega)),
      fun j hj => by
        rw [hge (curDesc + 4) (by omega), hge _ (by omega), hge _ (by omega)]; exact hpA j hj, hrt⟩,
      hmE, hmP,
      fun x hx => by rw [hge (curDesc + 2) (by omega)]; exact htE x hx,
      fun x hx => by rw [hge (curDesc + 4) (by omega)]; exact htP x hx,
      ht18, hcLo, hcHi⟩
  · intro a ha
    rw [hmemOut2 a (by omega) (by omega)]
    exact hzEnd a ha
  · intro a ha hnf h0 h1
    rw [hmemOut2 a h0 h1]
    exact hfrEnd a ha hnf
  · change _ + (Rrep.phi root tokEnd out2.mem + K * sgEnd.reembPot) + _ + _ + _ ≤
      (N + 1) * cycleLoopIterBudget L cfg.P.d findBudget shiftBudget + 80 +
      (Rrep.phi root tok mem + K * sg.reembPot) + _ + _
    rw [hphi2]
    change cL + (Rrep.phi root tokEnd outL.mem + K * sgEnd.reembPot) + _ + _ + _ ≤
      (N + 1) * cycleLoopIterBudget L cfg.P.d findBudget shiftBudget + 10 +
      (Rrep.phi root tok mem + K * sg.reembPot) + _ + _ at hcEnd
    omega

end MinCostFlow.MinRatio
