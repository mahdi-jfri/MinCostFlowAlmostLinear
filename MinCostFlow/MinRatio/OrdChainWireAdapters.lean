module

public import MinCostFlow.MinRatio.OrdChainRefreshWired
public import MinCostFlow.MinRatio.ShiftLevelWired
public import MinCostFlow.MinRatio.WireChainSpecs
public import MinCostFlow.MinRatio.OrdShiftStepSpecW
public import MinCostFlow.MinRatio.ShiftTermFacts

/-!
# Wired adapters for `WireChainSpecs` (`ChainRefreshStepSpecW`, `ShiftLevelStepSpecW`)

Wires the credit-bearing chain sub-specs (`OrdChainUpdateCoreSpecW`,
`ShiftTermChainSyncSpecW`, `ShiftDeepChainSyncSpecW` in `MinRatio/WireChainSpecs.lean`) into the
outer `ordChainRefreshWiredBody` and `shiftLevelWiredBody` procedures:
* `ChainRefreshStepSpecW` / `chainRefreshStepSpecW_wired`: discharges the credit-bearing
  chain-refresh contract (including `WireCapFacts` premise and `tok'.levelsEnd`, `tok'.intCap`,
  `OffTreeRecBound` conclusions) from `OrdChainUpdateCoreSpecW` and `ShiftQuotaWriterSpec`.
* `ShiftLevelStepSpecW` / `shiftLevelStepSpecW_wired`: discharges the credit-bearing level-shift
  contract (including `OffTreeRecBound`, `WireCapFacts`, `bran j < k` premises and `tok'.intCap`,
  `OffTreeRecBound` conclusions) from `ShiftTermChainSyncSpecW` and `ShiftDeepChainSyncSpecW`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program MinCostFlow.Bundle

private theorem alg2PreLoopState_chain_eq (cfg : Alg2Config) (model : Alg2State cfg)
    (U : List Update) (gVec lVec : ℕ → ℝ) :
    (alg2PreLoopState cfg model U gVec lVec).chain =
      (alg2PreResetState cfg model U gVec lVec).chain := by
  dsimp only [alg2PreLoopState, alg2PreResetState]

private theorem alg2PreLoopState_extG_eq (cfg : Alg2Config) (model : Alg2State cfg)
    (U : List Update) (gVec lVec : ℕ → ℝ) :
    (alg2PreLoopState cfg model U gVec lVec).extG =
      (alg2PreResetState cfg model U gVec lVec).extG := by
  dsimp only [alg2PreLoopState, alg2PreResetState]

private theorem alg2PreLoopState_extToInt_eq (cfg : Alg2Config) (model : Alg2State cfg)
    (U : List Update) (gVec lVec : ℕ → ℝ) :
    (alg2PreLoopState cfg model U gVec lVec).extToInt =
      (alg2PreResetState cfg model U gVec lVec).extToInt := by
  dsimp only [alg2PreLoopState, alg2PreResetState]

private theorem offTreeRecBound_preReset_to_preLoop {cfg : Alg2Config} {model : Alg2State cfg}
    {U : List Update} {gVec lVec : ℕ → ℝ} {L : ℕ} {mem : ℕ → ℕ} {edgeRecords : ℕ} {B : ℤ}
    (h : OffTreeRecBound (alg2PreResetState cfg model U gVec lVec) L mem edgeRecords B) :
    OffTreeRecBound (alg2PreLoopState cfg model U gVec lVec) L mem edgeRecords B := by
  intro e he hnot val hpa
  rw [alg2PreLoopState_extG_eq] at he
  rw [alg2PreLoopState_extToInt_eq, alg2PreLoopState_chain_eq] at hnot
  rw [alg2PreLoopState_extToInt_eq] at hpa
  exact h e he hnot val hpa

/-- Discharges `ChainRefreshStepSpecW` for `ordChainRefreshWiredBody` from
`OrdChainUpdateCoreSpecW` and `ShiftQuotaWriterSpec`. -/
theorem chainRefreshStepSpecW_wired
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit chainRefreshProc ordEditsProc
      ordChainCoreProc shiftQuotaWriterProc quotaBudget toolMul treeMul : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {B_bound R_bound : ℤ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    (hlocal : Rcore.Local)
    (hAt : p.procs[chainRefreshProc]? =
      some (ordChainRefreshWiredBody ordEditsProc ordChainCoreProc shiftQuotaWriterProc))
    (hEditsAt : p.procs[ordEditsProc]? = some level0BatchToOrdEditsBody)
    (hCore : OrdChainUpdateCoreSpecW w L P m V psi k epsExp drainUnit capExp limbMul capLimit cfg Rcore p
      ordChainCoreProc coreSpace coreFixed toolMul treeMul B_bound R_bound)
    (hQuota : ShiftQuotaWriterSpec w L P m V psi k epsExp drainUnit cfg Rcore p
      shiftQuotaWriterProc quotaBudget)
    (hw11 : 11 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) :
    ChainRefreshStepSpecW w L P m V psi k epsExp drainUnit capExp limbMul capLimit cfg Rcore p
      chainRefreshProc
      (fun uLen => cfg.P.d + (8 * uLen + 1) + coreSpace uLen)
      (fun uLen => coreFixed uLen + quotaBudget + 120 * uLen + 62 * (cfg.P.d + 1) + 240)
      toolMul treeMul B_bound R_bound := by
  obtain ⟨bCore, hbCore, hCoreRun⟩ := hCore
  refine ⟨ordChainRefreshWiredBody ordEditsProc ordChainCoreProc shiftQuotaWriterProc, hAt, ?_⟩
  intro root uIntBuf g l quotaBase heap pos ω mem0 mem model tok U
  dsimp only
  intro hrep0 hCap htags0 hfreshTab hnfCap hbatchInt hsmallInt hRefreshU hwordsU hKeyW hQuotaW
    hfootLt hgEnd hlEnd hqEnd hqOut huLeH hz hroom
  let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
  let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
  let modelPre := alg2PreResetState cfg model U gVec lVec
  let model1 := alg2PreLoopState cfg model U gVec lVec
  let coreBud := coreFixed U.length +
    toolMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) +
    treeMul * (modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates)
  obtain ⟨nextHeap, cost, out, tok', B', R', memCore, hr, hlo, hhi, hB, hR, hrep, hnum, hoff,
      hq, hpsi, hz', hfr, hft, hc, hrepCore, ⟨hlev, hintCap, hbdCore⟩, hag, _⟩ :=
    ordChainRefreshWiredBody_runs_gen (coreSpace := coreSpace U.length) (coreBudget := coreBud)
      (Q := fun tok' memC B' _ =>
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        OffTreeRecBound modelPre L memC tok'.edgeRecords B')
      (extraFoot := fun _ => False)
      hlocal hEditsAt hbCore
      (fun memIn posIn _ htagI hfrI hbaI hsmI hordI hedW hzI hrmI => by
        obtain ⟨nh, c, o, t', B', R', r, lo, hi, lv, ic, hB, hR, rep, num, off, bd, z', fr, ft, hc⟩ :=
          hCoreRun root uIntBuf (heap + cfg.P.d)
            (1 + batchOrdPayloadWords (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2)
            g l _ posIn ω mem0 memIn model tok U
            hrep0 hCap htagI hfrI hnfCap hbaI hsmI hordI hedW rfl hRefreshU hfootLt hgEnd hlEnd
            (by omega) hzI hrmI
        exact ⟨nh, c, o, t', B', R', r, lo, hi, hB, hR, rep, num, off, z', fun a ha hnf _ => fr a ha hnf, ft, hc, lv, ic, bd⟩)
      hQuota hw11 hdW hrep0 htags0 hfreshTab hbatchInt hsmallInt hRefreshU hwordsU hKeyW
      hQuotaW hfootLt (fun _ h => False.elim h) hqEnd hqOut huLeH hz hroom
  have hbdOut : OffTreeRecBound model1 L out.mem tok'.edgeRecords B' :=
    offTreeRecBound_preReset_to_preLoop (offTreeRecBound_of_agree hrepCore hbdCore fun a ha =>
      hag a (by rcases ha with h | h <;> omega) (by rcases ha with h | h <;> omega))
  have hchEq : model1.chain = modelPre.chain := alg2PreLoopState_chain_eq cfg model U gVec lVec
  refine ⟨nextHeap, cost, out, tok', B', R', hr, hlo, hhi, hlev, hintCap, hB, hR, hrep, hnum,
    hoff, hbdOut, hq, hpsi, hz', fun a ha hnf hnotQ => hfr a ha hnf (by decide) hnotQ, hft, ?_⟩
  dsimp only [coreBud] at hc
  rw [hchEq]
  omega

/-- Discharges `ShiftLevelStepSpecW` for `shiftLevelWiredBody` from the term step with its
reached-state facts (`ShiftTermChainSyncSpecWExt` at `lastTreeCap = 2 * levelM cfg.TP cfg.P cfg.P.d`)
and `ShiftDeepChainSyncSpecW`. Facts 1 to 9 of the term step come from `ShiftLoopChainInv`
(`shiftTerm_reached_facts_1_to_9`). -/
theorem shiftLevelStepSpecW_wired
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit shiftLevelProc shiftTermChainProc
      shiftDeepChainProc termSpace termFixed deepSpace deepFixed toolMul treeMul : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    (hAt : p.procs[shiftLevelProc]? =
      some (shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc))
    (hV : cfg.ValidOrdNoHidden)
    (hTerm : ShiftTermChainSyncSpecWExt w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      (2 * levelM cfg.TP cfg.P cfg.P.d) cfg Rcore p shiftTermChainProc termSpace termFixed toolMul treeMul)
    (hDeep : ShiftDeepChainSyncSpecW w L P m V psi k epsExp drainUnit capExp limbMul capLimit cfg Rcore p
      shiftDeepChainProc deepSpace deepFixed toolMul treeMul)
    (hw17 : 17 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w)
    (hkW : cfg.P.k < 2 ^ w) :
    ShiftLevelStepSpecW w L P m V psi k epsExp drainUnit capExp limbMul capLimit cfg Rcore p
      shiftLevelProc (max termSpace deepSpace)
      (max termFixed deepFixed + 28 * (cfg.P.d + 1) + 220) toolMul treeMul := by
  obtain ⟨bTerm, hbTerm, hTermRun⟩ := hTerm
  obtain ⟨bDeep, hbDeep, hDeepRun⟩ := hDeep
  refine ⟨shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc, hAt, ?_⟩
  intro root heap pos i ω mem model tok B R
  dsimp only
  intro hAcc hBranchLt hBrAll hQuotaW hPassW hrep hLoopInv hlogW hcapTree hnum hoff hbd hCap hbelow
    hz hroom
  let model' := alg2LoopShiftStep cfg model i
  let Δ := toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
    treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates)
  obtain ⟨nh, c, out, tok', hr, hlo, hhi, hlev, hrep', hnum', hoff', hz', hfr, hft, hc,
      ⟨hintCap, hbd'⟩⟩ :=
    shiftLevelWiredBody_runs_gen (termSpace := termSpace) (termBudget := termFixed + Δ)
      (deepSpace := deepSpace) (deepBudget := deepFixed + Δ)
      (Q := fun tok' mem' =>
        tok'.intCap = tok.intCap ∧ OffTreeRecBound model' L mem' tok'.edgeRecords B)
      hbTerm hbDeep
      (fun hiEq posIn memIn htag hsched hzIn hrmIn => by
        obtain ⟨f1, f2, f5, f6, f7, f8, f9⟩ := shiftTerm_reached_facts_1_to_9 hV hLoopInv hrep hbelow
          (lt_of_le_of_lt (Nat.le_add_right heap _) hroom)
        obtain ⟨nh, c, o, t', r, lo, hi, lv, ic, rep, _hmeta, num, off, bd, z', fr, ft, hc⟩ :=
          hTermRun root heap posIn ω mem memIn model tok B R hrep htag hsched hnum hoff hbd
            hCap hBrAll f1 f2 hlogW hcapTree f5 f6 f7 f8 f9
            hbelow hzIn hrmIn
        have hΔeq : Δ = toolMul * ((alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain.totalRuntime -
              model.chain.totalRuntime) +
            treeMul * ((alg2LoopShiftStep cfg model (Fin.last cfg.P.d)).chain.totalTreeUpdates -
              model.chain.totalTreeUpdates) := by
          dsimp only [Δ, model']; rw [hiEq]
        refine ⟨nh, c, o, t', r, lo, hi, lv, rep, num, off, z', fr, ft, ?_, ic, ?_⟩
        · rw [hΔeq]; omega
        · dsimp only [model']; rw [hiEq]; exact bd)
      (fun hiD posIn memIn htag hsched hzIn hrmIn => by
        obtain ⟨nh, c, o, t', r, lo, hi, lv, ic, rep, num, off, bd, z', fr, ft, hc⟩ :=
          hDeepRun root heap posIn i ω mem memIn model tok B R hiD hrep htag hsched hnum hoff hbd
            hCap hBrAll hbelow hzIn hrmIn
        refine ⟨nh, c, o, t', r, lo, hi, lv, rep, num, off, z', fr, ft, ?_, ic, bd⟩
        dsimp only [Δ, model']; omega)
      hw17 hdW hkW hAcc hBranchLt hQuotaW hPassW hrep hbelow hz hroom
  refine ⟨nh, c, out, tok', hr, hlo, hhi, hlev, hintCap, hrep', hnum', hoff', hbd', hz', hfr, hft, ?_⟩
  dsimp only [Δ, model'] at hc ⊢
  omega

end MinCostFlow.MinRatio
