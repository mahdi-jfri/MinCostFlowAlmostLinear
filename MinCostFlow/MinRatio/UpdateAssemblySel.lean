module

public import MinCostFlow.MinRatio.UpdateCycleLoopSel
public import MinCostFlow.MinRatio.UpdateAssemblyGood
public import MinCostFlow.MinRatio.MinRatioMachineAssembly
public import MinCostFlow.MinRatio.OrdSolverHistory
public import MinCostFlow.MinRatio.SolverTreeBudgetInv
import MinCostFlow.MinRatio.UpdateCopyOffFoot
import MinCostFlow.MinRatio.UpdateOverlayRead
import WordRAM.Tactic

/-!
# Select-aware end-to-end Word-RAM `Update` assembly (`UpdateAssemblySel`)

Proves `solverOps_update_runs_credit_sel`, the select-aware counterpart of
`solverOps_update_runs_credit_kfbl` (`MinRatioMachineAssembly.lean`): executes
`solverUpdateBody` through `solverOpsProcs` dispatch at `solverOpsDispatch base 0`,
maintaining `SolverLevelCapsInv`, `SolverSelectInv`, `sg.reembPot = chainReembPot pot model.chain`,
`SolverSelectRegionInv`, and `DeepInv`, with heap-backed `FindCycleStepSpecHeap`, select-aware
`ChainRefreshStepSpecWKFBLSel`, and select-aware `ShiftLevelStepSpecWKFBLSel`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program

set_option maxHeartbeats 1200000 in
/-- Select-aware credit-bearing execution of `minRatioMachineContractWithV` op 0 (`Update`)
through `solverOpsProcs` dispatch at `solverOpsDispatch base 0`: threads `SolverLevelCapsInv`,
`SolverSelectInv`, `sg.reembPot = chainReembPot pot model.chain`, `SolverSelectRegionInv`,
`DeepInv`, and the combined
potential `Rrep.phi + K * sg.reembPot` along with `toolMul * Δ totalRuntime + treeMul * Δ totalTreeUpdates`. -/
theorem solverOps_update_runs_credit_sel
    {w base chainRefreshProc findCycleProc shiftLevelProc m U_cap V psi k epsExp capExp limbMul
      capLimit wordExp stretchPrec intCapMax forestEdgeCap vCap eCap dMul kOff K pLast slot
      findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths toolMul treeMul
      root batch g l eta heap pos : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph} {pot : cfg.T.State → ℕ}
    {DeepInv : ChainState cfg.T cfg.P → Prop}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg F.limbs Rcore} {sg : SelectGhost}
    {B_bound R_bound : ℤ}
    {refreshSpace refreshBudget : ℕ → ℕ} {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ}
    (hMono : toolMul = 0 ∨ ToolCostMono cfg.T)
    (hw : 14 ≤ w) (hfmt4 : F.fmt.limbBits = 4) (hV : cfg.ValidOrdNoHidden)
    (hPL : F.fmt.precision ≤ 4 * F.limbs)
    (hα : cfg.α = Num.IPM.alphaPrime m U_cap / 8)
    (hepsExp : epsExp = k + Num.IPM.alphaExponent m U_cap + 10)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc))
    (hRefresh : ChainRefreshStepSpecWKFBLSel w F.limbs F.fmt.precision F.rangeExponent m V psi k
      epsExp (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit intCapMax forestEdgeCap
      vCap eCap dMul kOff K pLast slot cfg G pot DeepInv Rcore p chainRefreshProc refreshSpace
      refreshBudget toolMul treeMul)
    (hFind : FindCycleStepSpecHeap w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) dMul kOff cfg Rcore p findCycleProc findSpace findBudget
      maxEdges maxPaths)
    (hShift : ShiftLevelStepSpecWKFBLSel w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap dMul kOff K F.rangeExponent pLast slot cfg G pot DeepInv Rcore p
      shiftLevelProc shiftSpace shiftBudget toolMul treeMul)
    (hBridge : GoodCycleNumericBridge F cfg G m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore maxEdges maxPaths B_bound R_bound)
    (hMaxEdges1 : 1 ≤ maxEdges) (hMaxEP2 : 2 * maxEdges ≤ maxPaths)
    (hEmbBd : ∀ ch, Chain.Ordered.ShiftLoopChainInv cfg ch →
      ∀ i < cfg.P.d, ∀ e ∈ (ch.toTreeChain.activeCore i).E \ (ch.toTreeChain.activeS i).E,
        (ch.toTreeChain.activeEmb i e).length + 1 ≤ maxEdges)
    (hFEdgeCap : 2 * G.n ≤ forestEdgeCap)
    (hDeepPreLoop : ∀ U gVec lVec, RefreshBatch G U →
      (∀ e ∈ G.E, (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ lVec e ∧ lVec e ≤ (2 : ℝ) ^ F.rangeExponent) →
      (∀ e ∈ G.E, ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ F.fmt.precision = lVec e) →
      (∀ e ∈ G.E, (∀ u ∈ U, ¬ u.Inserts e) → gVec e = model.extg e ∧ lVec e = model.extℓ e) →
      DeepInv model.chain → DeepInv (alg2PreLoopState cfg model U gVec lVec).chain)
    (hDeepShift : ∀ ch, Chain.Ordered.ShiftLoopChainInv cfg ch → DeepInv ch →
      ∀ i ≤ cfg.P.d, DeepInv (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i).1)
    (hDeepToModel : ∀ (stM : Alg2State cfg) (i : Fin (cfg.P.d + 1)), i.val < cfg.P.d →
      Chain.Ordered.ShiftLoopChainInv cfg stM.chain → DeepInv stM.chain →
      ShiftDeepModelInv w F.limbs F.fmt.precision wordExp stretchPrec stM i)
    (hrep : (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).rep root model tok mem)
    (hCaps : SolverLevelCapsInv F.fmt.precision V vCap eCap model tok mem)
    (hLay : SolverLevelLayoutAt vCap eCap tok mem)
    (hSel : SolverSelectInv G F.limbs F.fmt.precision m dMul kOff tok.table model
      ((solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) Rcore).foot root tok)
      (LevelMetaFoot tok) sg mem)
    (hReemb : sg.reembPot = chainReembPot pot model.chain)
    (hReg : SolverSelectRegionInv G F.limbs F.fmt.precision m F.rangeExponent pLast slot vCap eCap
      model ((solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) Rcore).foot root tok) tok sg mem)
    (hReach : OrdSolverReached cfg (1 / (2 : ℝ) ^ k) G model)
    (hDeep : DeepInv model.chain)
    (hNumInv : SolverTreeNumericInv F.fmt.precision model tok)
    (hnum0 : PathTreeNumericInv tok.tree tok.trees B_bound R_bound)
    (hsep0 : OffTreeRecSep model F.limbs mem tok.edgeRecords)
    (hB0 : treeBudgetBase F.fmt.precision F.rangeExponent ≤ B_bound)
    (hεPos : 0 < cfg.ε) (hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent)
    (hrange0 : ∀ e ∈ model.extG.E, |model.extg e| ≤ (2 : ℝ) ^ F.rangeExponent ∧
      (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ model.extℓ e ∧ model.extℓ e ≤ (2 : ℝ) ^ F.rangeExponent)
    (hacc0 : ∀ e ∈ model.extG.E, 0 ≤ model.detectAccum e ∧
      model.extℓ e * model.detectAccum e < cfg.ε)
    (hIntCapEq : tok.intCap = initTargetCap cfg G)
    (hIntCap : tok.intCap ≤ intCapMax)
    (hNoGrow : ∀ U, BatchAt mem batch U → model.nextFresh + U.length ≤ tok.intCap)
    (hLoopInv0 : Chain.Ordered.ShiftLoopChainInv cfg model.chain)
    (hCapFacts : WireCapFacts capExp limbMul F.limbs capLimit model)
    (hpre : (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
      G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc).pre 0 model [root, batch, g, l, eta, heap] mem)
    (hextEq : model.extG = G)
    (hBr : BranchesLtK cfg model)
    (hbelow : ∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).foot root tok a ∨ sg.owned a → a < heap)
    (hGE : ∀ e < m, e ∈ G.E)
    (hz : ZeroFrom mem heap)
    (hmPos : 0 < m) (hcapPos : 0 < tok.intCap)
    (hnfLe : model.nextFresh ≤ tok.intCap)
    (h5L1W : 5 * F.limbs + 1 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) (hepsW : epsExp < 2 ^ w)
    (hpsiLimW : ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ < 2 ^ w)
    (h2nW : 2 * G.n + 1 < 2 ^ w) (hlogW : Nat.log 2 (2 * G.n + 1) ≤ 4 * F.limbs)
    (hsizeM : Nat.size m ≤ F.rangeExponent + 8)
    (hmaxEP : maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20))
    (hcapEvalB : 2 * (((maxEdges + maxPaths * G.n : ℕ) : ℤ) * B_bound) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapTreeB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) *
      ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
        (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapOffB : B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
      (Num.capacity 4 F.limbs : ℤ))
    (hroom : ∀ U, BatchAt mem batch U →
      let model1 := alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m) (readVector mem l 4 F.limbs F.fmt.precision m)
      heap + updateSpaceBound F.limbs m cfg.P.d model.nextFresh U.length (loopStepBound cfg model1)
        findSpace shiftSpace maxEdges maxPaths (refreshSpace U.length) + 2 < 2 ^ w)
    (hquotasW : ∀ U, BatchAt mem batch U →
      let model1 := alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m) (readVector mem l 4 F.limbs F.fmt.precision m)
      ∀ i ≤ cfg.P.d,
        shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i < 2 ^ w)
    (hLoopInv : ∀ U, BatchAt mem batch U →
      Chain.Ordered.ShiftLoopChainInv cfg (alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m)
        (readVector mem l 4 F.limbs F.fmt.precision m)).chain) :
    let L := F.limbs
    let P := F.fmt.precision
    let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
    ∃ body, p.procs[solverOpsDispatch base 0]? = some body ∧
      ∃ ret cost out model' tok' sg',
        Runs w p ω body (startState [root, batch, g, l, eta, heap] mem pos) (.returned ret) out cost ∧
        (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
          G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc).post 0 model [root, batch, g, l, eta, heap] mem model' out.mem ∧
        Rrep.rep root model' tok' out.mem ∧
        SolverLevelCapsInv P V vCap eCap model' tok' out.mem ∧
        SolverLevelLayoutAt vCap eCap tok' out.mem ∧
        SolverSelectInv G L P m dMul kOff tok'.table model' (Rrep.foot root tok')
          (LevelMetaFoot tok') sg' out.mem ∧
        sg'.reembPot = chainReembPot pot model'.chain ∧
        SolverSelectRegionInv G L P m F.rangeExponent pLast slot vCap eCap model' (Rrep.foot root tok')
          tok' sg' out.mem ∧
        DeepInv model'.chain ∧
        (∀ U, BatchAt mem batch U →
          tok'.intCap =
            (if tok.intCap < model.nextFresh + U.length then 2 * (model.nextFresh + U.length) else tok.intCap)) ∧
        ZeroFrom out.mem ret ∧ heap ≤ ret ∧
        (∀ U, BatchAt mem batch U →
          let model1 := alg2PreLoopState cfg model U (readVector mem g 4 L P m) (readVector mem l 4 L P m)
          let N := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain
          ret ≤ heap + updateSpaceBound L m cfg.P.d model.nextFresh U.length (loopStepBound cfg model1)
            findSpace shiftSpace maxEdges maxPaths (refreshSpace U.length) ∧
          cost + (Rrep.phi root tok' out.mem + K * sg'.reembPot) +
              shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model'.chain *
                cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
              toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
            updateBudgetBound L cfg.P.d G.n tok.intCap model.nextFresh U.length N findBudget shiftBudget
              maxEdges maxPaths (detectOffTreeDrainUnit L) (refreshBudget U.length) +
            (Rrep.phi root tok mem + K * sg.reembPot) +
            toolMul * model'.chain.totalRuntime + treeMul * model'.chain.totalTreeUpdates) ∧
        (∀ a < heap, ¬ (Rrep.foot root tok a ∨ sg.owned a) → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a ∨ sg'.owned a →
          (Rrep.foot root tok a ∨ sg.owned a) ∨ (heap ≤ a ∧ a < ret)) ∧
        PathTreeNumericInv tok'.tree tok'.trees
          (B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))
          (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) ∧
        OffTreeRecSep model' L out.mem tok'.edgeRecords := by
  dsimp only
  have hall := solverOpsProcs_meetsAll hw hp
  have hw16 : 16 < 2 ^ w := lt_of_lt_of_le (by decide : 16 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw)
  have hPW : F.fmt.precision < 2 ^ w := F.parameters_fit.2.1
  let L := F.limbs
  let P := F.fmt.precision
  let drainUnit := detectOffTreeDrainUnit L
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  have hlocR := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
  have hP4 : 4 ∣ P := hfmt4 ▸ F.fmt.precision_aligned
  have hqExpEq : epsExp - 7 = k + Num.IPM.alphaExponent m U_cap + 3 := by omega
  have hqW : k + Num.IPM.alphaExponent m U_cap + 3 < 2 ^ w := by omega
  obtain ⟨hFits0, handle_, batch_, g_, l_, eta_, heap_, U, hargsEq, hκα, hprec, hflow0,
    hbatch0, hwordsU, hRefreshU, hbatchEnd, hgEnd, hlEnd, hetaEnd, hetaValid,
    hetaLo, hetaHi, hglValid, hglIn, _, hdet⟩ := hpre
  injection hargsEq with hrEq hrest1; injection hrest1 with hbEq hrest2
  injection hrest2 with hgEq hrest3; injection hrest3 with hlEq hrest4
  injection hrest4 with heEq hrest5; injection hrest5 with hhEq _
  subst hrEq; subst hbEq; subst hgEq; subst hlEq; subst heEq; subst hhEq
  rw [hfmt4] at hFits0 hetaValid hetaLo hetaHi hglValid hglIn hdet
  have hagree := ordAlg2_detectedWith_agree hdet
  let gVec := readVector mem g 4 L P m
  let lVec := readVector mem l 4 L P m
  let model1 := alg2PreLoopState cfg model U gVec lVec
  let N := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain
  let NS := loopStepBound cfg model1
  have hroomU : heap + updateSpaceBound L m cfg.P.d model.nextFresh U.length NS findSpace shiftSpace
      maxEdges maxPaths (refreshSpace U.length) + 2 < 2 ^ w := hroom U hbatch0
  let descOut := heap + 1 + 2 * L
  let quotaBase := descOut + 2
  let zeroBlock := quotaBase + (cfg.P.d + 2)
  let etaCopy := zeroBlock + L
  let copyLen := 4 * U.length + 1
  let gCopy := etaCopy + L + 2 * copyLen
  let h0 := gCopy + 2 * (m * L)
  have hh0_ge : heap + 1 + 2 * L + 2 + (cfg.P.d + 2) + L + L + 2 * copyLen + 2 * (m * L) = h0 := rfl
  have hh0W : h0 < 2 ^ w := by
    dsimp only [copyLen, updateSpaceBound] at hroomU hh0_ge ⊢; omega
  -- Steps 0–3: run `solverUpdatePrepBody`
  let lay := solverOpsLayout base
  obtain ⟨s9, cPrep, memC2, tokG, h2, h3, hrPrep, hs9r0, hs9r2, hs9r3, hs9r5, hs9r7, hs9r8,
      hs9r9, hs9r11, hs9r13, hs9r14, hs9r15, hs9r16, hs9r18, hs9r31, hs9r41, hs9r42,
      hh2Lo, hh3GeH2, hh3Hi, hrepC2, hpresPrep, hphiC2, hglCopy, hfrF_tags, hfreshTabF,
      hbatchInt, hsmallF, hzF, hftG, hetaCopyF, hfrF_ltEta, hcPrep, hnfCapG,
      ⟨hcapGLe, htreeG, htreesG, hptrC2, hglWordsC2⟩⟩ :=
    solverUpdatePrepBody_runs (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit)
      (growTables := lay.growTables) (copyWords := lay.copyWords) (freshBatch := lay.freshBatch)
      (root := root) (batch := batch) (g := g) (l := l) (eta := eta)
      (heap := heap) (pos := pos) hlocalCore
      hall.2.2.2.2.2.2.2.2.2.2.2.2.1 hall.1 hall.2.2.2.2.2.2.2.1
      hrep hextEq hbatch0 hwordsU hRefreshU hbatchEnd hgEnd hlEnd hetaEnd
      (fun a ha => hbelow a (Or.inl ha)) hz hmPos hcapPos hnfLe hw16
      (by omega) hepsW (by dsimp only [updateSpaceBound] at hroomU; omega)
  have htokGIntCap : tokG.intCap = tok.intCap := by
    have hng := hNoGrow U hbatch0
    rw [hcapGLe, ite_eq_right (by omega)]
  have hNumInvG : SolverTreeNumericInv P model tokG := by
    obtain ⟨B0, R0, h1, h2', h3', h4'⟩ := hNumInv
    exact ⟨B0, R0, htreeG ▸ htreesG ▸ h1, htreeG ▸ h2', h3', h4'⟩
  have hh2GeH0 : h0 + copyLen ≤ h2 := hh2Lo
  have hh3LeBound : h3 ≤ h0 + 12 * (model.nextFresh + U.length) + 2 * copyLen := hh3Hi
  replace hftG : ∀ a, Rrep.foot root tokG a → Rrep.foot root tok a ∨ (h0 ≤ a ∧ a < h2 - copyLen) :=
    hftG
  have hfrC2_sel (a : ℕ) (ha : a < heap) (hnf : ¬ Rrep.foot root tok a) : memC2 a = mem a := by
    have hnfG : ¬ Rrep.foot root tokG a := fun hf => by
      rcases hftG a hf with h0' | ⟨hlo, _⟩
      · exact hnf h0'
      · dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hlo; omega
    have hOwnG := hrepC2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have htag0 : tokG.tag a = 0 := Decidable.byContradiction fun hnz => hnfG (Or.inl (hOwnG a hnz))
    have h1 := hfrF_tags a (by
      have hhe : heap ≤ h0 := by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut]; omega
      omega) (by omega) (by omega) (by omega)
    have h2 := hfrF_ltEta a (by omega) hnf
    exact h1.symm.trans h2
  obtain ⟨hCapsC2, hSelC2⟩ := hpresPrep.preserve_both hCaps hSel hfrC2_sel hftG
    (fun a ha => hbelow a (Or.inr ha))
    (by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut]; omega) rfl rfl rfl
  have hLayC2 := hpresPrep.to_levelLayout hCaps.1 hLay
  have hRegC2 := hReg.preserve_of_levelMeta hCaps.1 hpresPrep hfrC2_sel hftG
    (fun a ha => hbelow a (Or.inr ha))
    (by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut]; omega) rfl rfl rfl
  have hgCopyLe : gCopy + m * L + m * L ≤ h2 :=
    le_trans (by dsimp only [h0]; omega) (le_trans (Nat.le_add_right _ _) hh2GeH0)
  have hGE' : ∀ e < m, e ∈ model.extG.E := fun e he => hextEq ▸ hGE e he
  have hgVecEq : updateOverlay model.extG.E U (readVector memC2 gCopy 4 L P m) model.extg =
      readVector mem g 4 L P m :=
    updateOverlay_readVector_eq hGE' (fun e he hn => (hagree e (hextEq ▸ he) hn).1)
      (fun e he => by unfold readVector; rw [ite_eq_right (by omega)]) (fun e he => (hglCopy e he).1)
  have hlVecEq : updateOverlay model.extG.E U (readVector memC2 (gCopy + m * L) 4 L P m) model.extℓ =
      readVector mem l 4 L P m :=
    updateOverlay_readVector_eq hGE' (fun e he hn => (hagree e (hextEq ▸ he) hn).2)
      (fun e he => by unfold readVector; rw [ite_eq_right (by omega)]) (fun e he => (hglCopy e he).2)
  -- Step 4: call `chainRefreshProc`
  obtain ⟨bRef, hbRef, hRefSpec⟩ := hRefresh
  have hfootG_ltH2 (a : ℕ) (ha : Rrep.foot root tokG a ∨ sg.owned a) : a < h2 := by
    rcases ha with hf | ho
    · rcases hftG a hf with h0' | ⟨_, hhi⟩
      · have := hbelow a (Or.inl h0'); dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hh2GeH0 ⊢; omega
      · omega
    · have := hbelow a (Or.inr ho); dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hh2GeH0 ⊢; omega
  have hqOutG (i : ℕ) (hi : i ≤ cfg.P.d + 1) :
      ¬ (Rrep.foot root tokG (quotaBase + i) ∨ sg.owned (quotaBase + i)) := by
    rintro (hf | ho)
    · rcases hftG _ hf with h0' | ⟨hlo, _⟩
      · have := hbelow _ (Or.inl h0'); dsimp only [quotaBase, descOut] at this; omega
      · dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hlo; omega
    · have := hbelow _ (Or.inr ho); dsimp only [quotaBase, descOut] at this; omega
  have hFEdge0 : 2 * (model.chain.G 0).n ≤ forestEdgeCap := by
    rw [hrep.2.2.2.2.1.n_eq, hextEq]; exact hFEdgeCap
  -- The records at the start of the refresh: bounded by the model at the budget `B_bound`
  have hXnn : (0 : ℤ) ≤ (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) :=
    mul_nonneg (Int.natCast_nonneg _) (pow_nonneg (by norm_num) _)
  obtain ⟨hoffC2, hbdC2⟩ := offTreeRec_of_model hrepC2 hεPos hεLe hB0 hrange0
    (fun e he => hflow0 e (hextEq ▸ he)) hacc0 (hsep0.of_copy hptrC2)
  have hfitC2 : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B_bound + R_bound) <
      (Num.capacity 4 L : ℤ) := by
    rw [hextEq]
    have hsum : B_bound + R_bound ≤
        (B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
        (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) := by
      linarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsum (by omega)) hcapTreeB
  obtain ⟨h4, cR, stR, tokR, sgR, hrR, hh4Lo, hh4Hi, _hlevR, hintCapR, _hrcapR, _htabR,
      hrepR, hMetaR, hCapsAtR, hLayR, hSelR, hReembR, hRegR, hnumR, hoffR, hBdR, hquotasR, hpsiLimR,
      hzR, hfrR, hftR, hcR⟩ :=
    hRefSpec root h2 gCopy (gCopy + m * L) quotaBase h3 s9.pos ω memC2 s9.mem model tokG sg U
      B_bound R_bound hrepC2 hCapsC2.1 hCapsC2.2 hSelC2 hReemb hRegC2 hReach hDeep hFits0 hNumInvG
      (htreeG ▸ htreesG ▸ hnum0) hoffC2 hbdC2 hB0 hfitC2 hrange0
      (fun e he => hflow0 e (hextEq ▸ he)) hacc0
      (htokGIntCap.trans hIntCapEq) (htokGIntCap.symm ▸ hIntCap) hFEdge0 (hextEq ▸ hlogW)
      hLoopInv0 (by rw [hgVecEq, hlVecEq]; exact hLoopInv U hbatch0) hCapFacts hBr.1
      (fun e he => by rw [hgVecEq, hlVecEq]; exact hglIn e (hextEq ▸ he))
      (fun e he hNo => by rw [hgVecEq, hlVecEq]; exact hagree e (hextEq ▸ he) fun ⟨u, hu, hi⟩ => hNo u hu hi)
      hfrF_tags hfreshTabF hnfCapG hbatchInt hsmallF (hextEq ▸ hRefreshU) hwordsU
      (by dsimp only [updateSpaceBound] at hroomU; omega)
      (by rw [hgVecEq, hlVecEq]; exact hquotasW U hbatch0)
      hfootG_ltH2 (le_trans (Nat.le_add_right _ _) hgCopyLe) hgCopyLe (copies_off_foot hbelow hftG
        (by dsimp only [gCopy, etaCopy, zeroBlock, quotaBase, descOut]; omega) le_rfl)
      (by dsimp only [quotaBase, descOut, gCopy, etaCopy, zeroBlock] at hgCopyLe ⊢; omega)
      hqOutG hh3GeH2 hzF
      (by dsimp only [copyLen, updateSpaceBound] at hh3LeBound hroomU hh0_ge ⊢; omega)
      (fun u hu e heIns => by
        have heG : e ∈ G.E := by
          have hm := hRefreshU.2.2 u hu; cases u with
          | insert e' _ _ => have : e' = e := heIns; subst this; exact hm.1
          | delete _ => exact False.elim heIns | split _ _ _ _ => exact False.elim hm
        have hem : e < m := hrep.2.2.2.2.2.2.1 e (hextEq.symm ▸ heG)
        have hcp := hglWordsC2 e hem ⟨u, hu, heIns⟩
        exact ⟨fun j hj => by rw [(hcp j hj).1]; exact (hglValid e hem).1 j hj,
          fun j hj => by rw [(hcp j hj).2]; exact (hglValid e hem).2 j hj⟩) hLayC2
  rw [hgVecEq, hlVecEq] at hrepR hMetaR hCapsAtR hSelR hReembR hRegR hoffR hBdR hquotasR hcR
  have hCapsR : SolverLevelCapsInv P V vCap eCap model1 tokR stR.mem := ⟨hMetaR, hCapsAtR⟩
  have hDeep1 : DeepInv model1.chain := by
    refine hDeepPreLoop U gVec lVec hRefreshU (fun e he => (hglIn e he).2) (fun e _ => ?_)
      (fun e he hNo => hagree e he fun ⟨u, hu, hi⟩ => hNo u hu hi) hDeep
    dsimp only [lVec]; unfold readVector; split_ifs
    · exact ⟨Num.intVal mem (l + e * L) 4 L, rfl⟩
    · exact ⟨0, by simp⟩
  let s10 : State := { regs := Function.update s9.regs 16 h4, mem := stR.mem, pos := stR.pos }
  have rCallR : Runs w p ω (.call 16 chainRefreshProc [.reg 0, .reg 18, .reg 41, .reg 42, .reg 14, .reg 16]) s9 .normal s10 (cR + 7) :=
    runs_call_iff.mpr ⟨[root, h2, gCopy, gCopy + m * L, quotaBase, h3], bRef, .returned h4, stR, cR,
      by simp [evalArgs, Expr.eval, hs9r0, hs9r18, hs9r41, hs9r42, hs9r14, hs9r16, quotaBase, descOut,
        gCopy, etaCopy, zeroBlock, copyLen],
      hbRef, hrR, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  let s10p : State := { s10 with regs := Function.update s10.regs 10 ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ }
  have rLoadPsi : Runs w p ω (.assign 10 (.load (.bin .add (.reg 14) (.bin .add (.reg 9) (.const 1))))) s10 .normal s10p 7 :=
    runs_assign_iff.mpr ⟨⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊, by
      simp [Expr.eval, BinOp.eval, s10, hs9r14, hs9r9, show 1 < 2 ^ w by omega, hdW,
        show quotaBase + (cfg.P.d + 1) < 2 ^ w by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hh0W ⊢; omega,
        quotaBase, descOut, hpsiLimR],
      rfl, rfl, rfl⟩
  -- Step 5: call `updateCycleLoopBody`
  have hfootR_lt (a : ℕ) (ha : Rrep.foot root tokR a ∨ sgR.owned a) : a < h4 := by
    rcases hftR a ha with h0' | ⟨_, hhi⟩
    · exact lt_of_lt_of_le (hfootG_ltH2 a h0') (by omega)
    · exact hhi
  have hqOutR (i : ℕ) (hi : i ≤ cfg.P.d) :
      ¬ (Rrep.foot root tokR (quotaBase + i) ∨ sgR.owned (quotaBase + i)) := by
    intro hf; rcases hftR _ hf with h0' | ⟨hlo, _⟩
    · exact hqOutG i (by omega) h0'
    · dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hh2GeH0 hlo; omega
  have hdescOutR (j : ℕ) (hj : j ≤ 1) :
      ¬ (Rrep.foot root tokR (descOut + j) ∨ sgR.owned (descOut + j)) := by
    intro hf; rcases hftR _ hf with h0' | ⟨hlo, _⟩
    · rcases h0' with hf' | ho'
      · rcases hftG _ hf' with h0'' | ⟨hlo', _⟩
        · have := hbelow _ (Or.inl h0''); dsimp only [descOut] at this; omega
        · dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hlo'; omega
      · have := hbelow _ (Or.inr ho'); dsimp only [descOut] at this; omega
    · dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hh2GeH0 hlo; omega
  have hmodel1ExtG : model1.extG = G := by
    dsimp only [model1, alg2PreLoopState]
    rw [(translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt model.intToExt
      model.nextFresh hrep.2.2.2.2.1 (hextEq ▸ hRefreshU.1)).1, hextEq, hRefreshU.2.1]
  have hGn1 : (model1.chain.G 0).n ≤ G.n := by
    rw [hrepR.2.2.2.2.1.n_eq, hmodel1ExtG]
  have hCapFacts1 : WireCapFacts capExp limbMul L capLimit model1 :=
    hCapFacts.congr (fun j _ => congrFun (alg2PreLoopState_lvlM_N0 cfg model U _ _).1 j)
      (alg2PreLoopState_lvlM_N0 cfg model U _ _).2
  have hlogW1 : Nat.log 2 (2 * model1.extG.n + 1) ≤ 4 * L := by
    rw [hmodel1ExtG]; exact hlogW
  have hlenNN1 : ∀ e ∈ model1.extG.E, 0 ≤ model1.extℓ e := fun e he => by
    rw [hmodel1ExtG] at he
    exact le_of_lt (lt_of_lt_of_le (by positivity) (hglIn e he).2.1)
  have hcapEval1 : 2 * (((maxEdges + maxPaths * model1.extG.n : ℕ) : ℤ) * B_bound) <
      (Num.capacity 4 L : ℤ) := by
    rw [hmodel1ExtG]; exact hcapEvalB
  have hcapTree1 : 2 * ((2 * model1.extG.n + 1 : ℕ) : ℤ) * (B_bound + R_bound) <
      (Num.capacity 4 L : ℤ) := by
    rw [hmodel1ExtG, ← hextEq]; exact hfitC2
  obtain ⟨h5, cL, stL, tokL, sgL, hrL, hh5Lo, hh5Hi, hfoundL, hrepL, hCapsL, hLayL, hSelL, hReembL, hRegL, hDeepL,
      hintCapL, hnumL, hoffL, hdescL, hzL, hfrL, hftL, hcL⟩ :=
    updateCycleLoopBody_runs_sel (w := w) (L := L) (P := P) (m := m) (U := U_cap) (V := V) (psi := psi)
      (k := k) (qHdr := k) (epsExp := epsExp) (drainUnit := drainUnit)
      (capExp := capExp) (limbMul := limbMul) (capLimit := capLimit)
      (wordExp := wordExp) (stretchPrec := stretchPrec) (intCapMax := intCapMax)
      (forestEdgeCap := forestEdgeCap) (vCap := vCap) (eCap := eCap) (dMul := dMul) (kOff := kOff)
      (K := K) (findCycleProc := findCycleProc) (updateQualityProc := lay.updateQuality)
      (shiftCheckProc := lay.shiftCheck) (shiftLevelProc := shiftLevelProc)
      (findSpace := findSpace) (findBudget := findBudget)
      (shiftSpace := shiftSpace) (shiftBudget := shiftBudget) (maxEdges := maxEdges) (maxPaths := maxPaths)
      (toolMul := toolMul) (treeMul := treeMul)
      (root := root) (quotaBase := quotaBase) (descOut := descOut) (heap := h4) (pos := s10p.pos)
      (lctOps := model1.lctUpdateOps)
      hlocalCore hMono hV hα hFind
      (hall.2.2.2.2.2.2.2.2.1 m U_cap k F.fmt.precision) hall.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hShift hMaxEdges1 hMaxEP2 hEmbBd hFEdgeCap hDeepShift hDeepToModel
      (by omega) h5L1W hdW hqW hpsiLimW
      hrepR hCapsR hLayR hSelR hReembR hRegR hDeep1 (hintCapR.symm ▸ htokGIntCap.symm ▸ hIntCap) hGn1
      (hLoopInv U hbatch0) hnumR hoffR hBdR hCapFacts1 hcapEval1 hcapTree1 hlogW1 hlenNN1
      hfootR_lt (by dsimp only [quotaBase, descOut]; omega) hquotasR
      (hquotasW U hbatch0) (branchesLtK_preLoop hBr) hqOutR
      (by dsimp only [descOut]; omega) (by simpa using hdescOutR 0 (by decide)) (hdescOutR 1 (by decide)) hzR
      (by
        have hN_eq : loopStepBound cfg
            (alg2PreLoopState cfg model U (readVector mem g 4 L P m) (readVector mem l 4 L P m)) = NS := rfl
        rw [hN_eq]; dsimp only [copyLen, updateSpaceBound] at hh4Hi hh3LeBound hroomU hh0_ge ⊢; omega)
  have hcapL : ∀ U', BatchAt mem batch U' →
      tokL.intCap =
        (if tok.intCap < model.nextFresh + U'.length then 2 * (model.nextFresh + U'.length) else tok.intCap) := by
    intro U' hB'
    obtain rfl := batchAt_unique_of_refresh hRefreshU hbatch0 hB'
    rw [hintCapL, hintCapR]
    exact hcapGLe
  let s11 : State := { regs := Function.update s10p.regs 16 h5, mem := stL.mem, pos := stL.pos }
  have rCallL : Runs w p ω (.call 16 lay.cycleLoop [.reg 0, .reg 14, .reg 10, .reg 11, .reg 13, .reg 16]) s10p .normal s11 (cL + 7) :=
    runs_call_iff.mpr ⟨[root, quotaBase, ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊, k + Num.IPM.alphaExponent m U_cap + 3, descOut, h4],
      updateCycleLoopBody findCycleProc lay.updateQuality lay.shiftCheck shiftLevelProc, .returned h5, stL, cL,
      by simp [evalArgs, Expr.eval, s10p, s10, hs9r0, hs9r14, hs9r11, hs9r13, quotaBase, descOut, hqExpEq],
      hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hrL, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  -- Shared frame & footprint helpers up to `s11`
  let loopRes := Chain.Ordered.algorithm2_loopWith cfg (1 / (2 : ℝ) ^ k) model1.extG model1.extToInt
    model1.extg model1.extℓ model1.chain model1.branD model1.passes model1.lctUpdateOps
  let modelLoop : Alg2State cfg :=
    { model1 with
      chain := loopRes.1
      branD := loopRes.2.1
      passes := loopRes.2.2.1
      lctUpdateOps := loopRes.2.2.2.1 }
  have hrepL' : Rrep.rep root modelLoop tokL stL.mem := hrepL
  have hCapsL' : SolverLevelCapsInv P V vCap eCap modelLoop tokL stL.mem :=
    (PreservesLevelMeta.refl tokL stL.mem).to_capsInv hCapsL rfl (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hSelL' : SolverSelectInv G L P m dMul kOff tokL.table modelLoop (Rrep.foot root tokL)
      (LevelMetaFoot tokL) sgL stL.mem := by
    obtain ⟨hSt, hDisj, G₀, σ, σ_mwu, γ_ℓ, γ_c, hMod⟩ := hSelL
    exact ⟨fun mem' hmem' => (hSt mem' hmem').mono_foot (fun _ hm => hm) rfl, hDisj,
      G₀, σ, σ_mwu, γ_ℓ, γ_c, hMod.of_chain_ext rfl rfl rfl⟩
  have hRegL' : SolverSelectRegionInv G L P m F.rangeExponent pLast slot vCap eCap modelLoop
      (Rrep.foot root tokL) tokL sgL stL.mem :=
    hRegL.congr hCapsL.1 (PreservesLevelMeta.refl tokL stL.mem) hRegL.owned_not_foot
      (fun _ _ => rfl) rfl rfl rfl
  have hfootL_range (a : ℕ) (ha : Rrep.foot root tokL a ∨ sgL.owned a) :
      (Rrep.foot root tok a ∨ sg.owned a) ∨ (h0 ≤ a ∧ a < h5) := by
    rcases hftL a ha with h1' | ⟨hlo, hhi⟩
    · rcases hftR a h1' with h2' | ⟨hlo, hhi⟩
      · rcases h2' with hf2 | ho2
        · exact (hftG a hf2).imp Or.inl (fun ⟨hlo', hhi'⟩ => ⟨hlo', by omega⟩)
        · exact Or.inl (Or.inr ho2)
      · exact Or.inr ⟨by omega, lt_of_lt_of_le hhi hh5Lo⟩
    · exact Or.inr ⟨by omega, hhi⟩
  have hfrL_toS9 (a : ℕ) (ha : a < h0) (hnf : ¬ (Rrep.foot root tok a ∨ sg.owned a))
      (hnDesc0 : a ≠ descOut) (hnDesc1 : a ≠ descOut + 1)
      (hnQuota : a < quotaBase ∨ quotaBase + cfg.P.d + 1 < a) : stL.mem a = s9.mem a := by
    have hnfG : ¬ (Rrep.foot root tokG a ∨ sg.owned a) := fun hf => by
      rcases hf with hf | ho
      · rcases hftG a hf with h' | ⟨hlo, _⟩
        · exact hnf (Or.inl h')
        · omega
      · exact hnf (Or.inr ho)
    have hah3 : a < h3 := lt_of_lt_of_le ha (le_trans (le_trans (Nat.le_add_right _ _) hh2GeH0) hh3GeH2)
    have hnfR : ¬ (Rrep.foot root tokR a ∨ sgR.owned a) := fun hf => by
      rcases hftR a hf with h' | ⟨hlo, _⟩
      · exact hnfG h'
      · exact absurd hah3 (not_lt.mpr hlo)
    exact (hfrL a (lt_of_lt_of_le hah3 hh4Lo) hnfR hnDesc0 hnDesc1).trans
      (hfrR a hah3 hnfG hnQuota)
  have hnotFoot_geHeap (a : ℕ) (ha : heap ≤ a) : ¬ (Rrep.foot root tok a ∨ sg.owned a) :=
    fun hf => absurd (hbelow a hf) (by omega)
  have hetaCopyL (j : ℕ) (hj : j < L) : stL.mem (etaCopy + j) = mem (eta + j) := by
    rw [hfrL_toS9 (etaCopy + j) (by dsimp only [h0, gCopy]; omega)
      (hnotFoot_geHeap _ (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega))
      (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega)
      (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega)
      (Or.inr (by dsimp only [etaCopy, zeroBlock, quotaBase]; omega))]
    exact hetaCopyF j hj
  have hzeroBlockL : PathIntAt stL.mem zeroBlock 4 L 0 :=
    pathIntAt_zero_of_zeroFrom fun j hj => by
      rw [hfrL_toS9 (zeroBlock + j) (by dsimp only [h0, gCopy, etaCopy]; omega)
        (hnotFoot_geHeap _ (by dsimp only [zeroBlock, quotaBase, descOut]; omega))
        (by dsimp only [zeroBlock, quotaBase, descOut]; omega)
        (by dsimp only [zeroBlock, quotaBase, descOut]; omega)
        (Or.inr (by dsimp only [zeroBlock, quotaBase]; omega)),
        hfrF_ltEta (zeroBlock + j) (by dsimp only [zeroBlock, quotaBase, descOut]; omega)
          (fun hf => hnotFoot_geHeap _ (by dsimp only [zeroBlock, quotaBase, descOut]; omega) (Or.inl hf))]
      exact hz (zeroBlock + j) (by dsimp only [zeroBlock, quotaBase, descOut]; omega)
  have hfrL_ltHeap (a : ℕ) (ha : a < heap) (hnf : ¬ (Rrep.foot root tok a ∨ sg.owned a)) :
      stL.mem a = mem a := by
    have hlt_h0 : a < h0 := lt_of_lt_of_le ha (by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut]; omega)
    have hlt_eta : a < etaCopy := lt_of_lt_of_le ha (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega)
    have hlt_desc : a < descOut := lt_of_lt_of_le ha (by dsimp only [descOut]; omega)
    exact (hfrL_toS9 a hlt_h0 hnf (Nat.ne_of_lt hlt_desc) (by omega)
      (Or.inl (lt_of_lt_of_le hlt_desc (by dsimp only [quotaBase]; omega)))).trans
      (hfrF_ltEta a hlt_eta (fun hf => hnf (Or.inl hf)))
  -- Step 6: load `foundBit := stL.mem descOut` and branch
  let foundBit := if loopRes.2.2.2.2.isSome then 1 else 0
  have hfoundEq : stL.mem descOut = foundBit := hfoundL
  let s12 : State := { s11 with regs := Function.update s11.regs 22 foundBit }
  have rLoadFound : Runs w p ω (.assign 22 (.load (.reg 13))) s11 .normal s12 3 :=
    runs_assign_iff.mpr ⟨foundBit, by simp [Expr.eval, s11, s10p, s10, hs9r13, descOut, hfoundEq], rfl, rfl, rfl⟩
  let goodBranch : Stmt :=
    .assign 23 (.load (.bin .add (.reg 13) (.const 1))) ;;
    .assign 24 (.load (.reg 23)) ;;
    .assign 25 (.load (.bin .add (.reg 23) (.const 2))) ;;
    .assign 26 (.load (.bin .add (.reg 23) (.const 3))) ;;
    .assign 27 (.load (.bin .add (.reg 23) (.const 4))) ;;
    .assign 28 (.load (.bin .add (.reg 23) (.const 5))) ;;
    .assign 29 (.bin .add (.reg 16) (.reg 7)) ;;
    .call 16 lay.subtract [.reg 15, .reg 24, .reg 7, .reg 16] ;;
    .call 16 lay.goodApply [.reg 0, .reg 31, .reg 29, .reg 25, .reg 26, .reg 27, .reg 28, .reg 5, .reg 16] ;;
    .ret (.reg 16)
  let failBranch : Stmt :=
    .call 30 lay.failOut [.reg 31, .reg 7, .reg 8, .reg 5] ;;
    .ret (.reg 16)
  have hchainAll {retEnd cTail : ℕ} {outEnd : State}
      (hTail : Runs w p ω (.cond (.reg 22) goodBranch failBranch) s12 (.returned retEnd) outEnd cTail) :
      Runs w p ω
        (solverUpdateBody lay.growTables lay.copyWords lay.freshBatch chainRefreshProc lay.cycleLoop lay.subtract
          lay.goodApply lay.failOut)
        (startState [root, batch, g, l, eta, heap] mem pos) (.returned retEnd) outEnd
        (cPrep + ((cR + 7) + (7 + ((cL + 7) + (3 + cTail + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s9, cPrep, _, hrPrep,
    runs_seq_iff.mpr (Or.inr ⟨s10, cR + 7, _, rCallR,
    runs_seq_iff.mpr (Or.inr ⟨s10p, 7, _, rLoadPsi,
    runs_seq_iff.mpr (Or.inr ⟨s11, cL + 7, _, rCallL,
    runs_seq_iff.mpr (Or.inr ⟨s12, 3, cTail, rLoadFound, hTail, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hcR0 : cR + (Rrep.phi root tokR stR.mem + K * sgR.reembPot) ≤
      refreshBudget U.length +
        toolMul * (model1.chain.totalRuntime - model.chain.totalRuntime) +
        treeMul * (model1.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
        (Rrep.phi root tok mem + K * sg.reembPot) := by
    have hphiC2' : Rrep.phi root tokG memC2 = Rrep.phi root tok mem := hphiC2
    change cR + Rrep.phi root tokR stR.mem + K * sgR.reembPot ≤
      refreshBudget U.length +
        toolMul * (model1.chain.totalRuntime - model.chain.totalRuntime) +
        treeMul * (model1.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
        Rrep.phi root tokG memC2 + K * sg.reembPot at hcR
    rw [hphiC2'] at hcR; omega
  refine ⟨_, hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  cases hOpt : loopRes.2.2.2.2 with
  | none =>
    have hfb0 : foundBit = 0 := by simp [foundBit, hOpt]
    have hetaCopyValid : Num.Valid stL.mem etaCopy 4 L := numValid_congr hetaValid hetaCopyL
    have hetaCopyVal : Num.fixVal stL.mem etaCopy 4 L P = Num.fixVal mem eta 4 L P := by
      unfold Num.fixVal; rw [numIntVal_congr hetaCopyL]
    have hposReq : 0 < Num.fixVal stL.mem etaCopy 4 L P := by rw [hetaCopyVal]; exact lt_of_lt_of_le (by positivity) hetaLo
    have hzeroOut : ∀ j < 2 * L, stL.mem (heap + 1 + j) = 0 := fun j hj => by
      rw [hfrL_toS9 (heap + 1 + j) (by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut]; omega)
        (hnotFoot_geHeap _ (by omega)) (by dsimp only [descOut]; omega) (by dsimp only [descOut]; omega)
        (Or.inl (by dsimp only [quotaBase, descOut]; omega)),
        hfrF_ltEta (heap + 1 + j) (by omega) (fun hf => hnotFoot_geHeap _ (by omega) (Or.inl hf))]
      exact hz (heap + 1 + j) (by omega)
    obtain ⟨cFail, stFail, hrFail, hcFail, hAnsF, hScalF, hNormF, hfrFail⟩ :=
      updateFailOutputBody_runs (w := w) (copyWords := lay.copyWords) (eta := etaCopy) (L := L) (P := P)
        (heap := heap) (pos := s12.pos) (p := p) (ω := ω) (mem := stL.mem) hall.1 hP4 hPL
        (Or.inr (by dsimp only [etaCopy, zeroBlock, quotaBase, descOut]; omega))
        (by dsimp only [h0, gCopy] at hh0W; omega) hetaCopyValid hposReq hzeroOut
        (by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hh0W; omega) (by omega)
    let s13 : State := { regs := Function.update s12.regs 30 (heap + 1 + 2 * L), mem := stFail.mem, pos := stFail.pos }
    have rCallFail : Runs w p ω (.call 30 lay.failOut [.reg 31, .reg 7, .reg 8, .reg 5]) s12 .normal s13 (cFail + 5) :=
      runs_call_iff.mpr ⟨[etaCopy, L, P, heap], updateFailOutputBody lay.copyWords, .returned (heap + 1 + 2 * L), stFail, cFail,
        by simp [evalArgs, Expr.eval, s12, s11, s10p, s10, hs9r31, hs9r7, hs9r8, hs9r5, etaCopy, zeroBlock, quotaBase, descOut],
        hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hrFail, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    have rRetFail : Runs w p ω (.ret (.reg 16)) s13 (.returned h5) s13 2 :=
      runs_ret_iff.mpr ⟨h5, by simp [Expr.eval, s13, s12, s11], rfl, rfl, rfl⟩
    have rCondFail : Runs w p ω (.cond (.reg 22) goodBranch failBranch) s12 (.returned h5) s13 (1 + ((cFail + 5) + 2 + 1) + 1) :=
      runs_cond_iff.mpr ⟨0, (cFail + 5) + 2 + 1, by simp [Expr.eval, s12, hfb0],
        by simp only [↓reduceIte]; exact runs_seq_iff.mpr (Or.inr ⟨s13, cFail + 5, 2, rCallFail, rRetFail, rfl⟩),
        by simp [Expr.size]⟩
    have hagFailAll (a : ℕ) (ha : Rrep.foot root tokL a ∨ sgL.owned a) : stL.mem a = stFail.mem a :=
      (hfootL_range a ha).elim (fun h0' => (hfrFail a (Or.inl (hbelow a h0'))).symm)
        (fun ⟨hlo, _⟩ => (hfrFail a (Or.inr (by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hlo; omega))).symm)
    have hagFail (a : ℕ) (ha : Rrep.foot root tokL a) : stL.mem a = stFail.mem a := hagFailAll a (Or.inl ha)
    have hrepFail : Rrep.rep root modelLoop tokL stFail.mem := (hlocR root modelLoop tokL stL.mem stFail.mem hagFail).1 hrepL'
    have hmetaFail : PreservesLevelMeta tokL tokL stL.mem stFail.mem :=
      (PreservesLevelMeta.refl tokL stL.mem).congr_mem_right fun a ht => (hagFail a (LevelMetaFoot.mem_foot hrepL' ht)).symm
    have hCapsFail : SolverLevelCapsInv P V vCap eCap modelLoop tokL stFail.mem :=
      hmetaFail.to_capsInv hCapsL' rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
    have hSelFail : SolverSelectInv G L P m dMul kOff tokL.table modelLoop (Rrep.foot root tokL)
        (LevelMetaFoot tokL) sgL stFail.mem := by
      obtain ⟨hSt, hDisj, hMod⟩ := hSelL'
      exact ⟨fun mem' hmem' => hSt mem' fun a ha => by
        rw [hmem' a ha]; exact (hagFailAll a (ha.imp (fun hm => LevelMetaFoot.mem_foot hrepL' hm) id)).symm,
        hDisj, hMod⟩
    have hRegFail := hRegL'.congr hCapsL'.1 hmetaFail hRegL'.owned_not_foot
      (fun a ho => (hagFailAll a (Or.inr ho)).symm) rfl rfl rfl
    have hphiFail : Rrep.phi root tokL stFail.mem = Rrep.phi root tokL stL.mem :=
      ((hlocR root modelLoop tokL stL.mem stFail.mem hagFail).2).symm
    refine ⟨h5, _, s13, modelLoop, tokL, sgL, hchainAll rCondFail, ?_, hrepFail, hCapsFail,
      hmetaFail.to_levelLayout hCapsL'.1 hLayL, hSelFail, hReembL, hRegFail, hDeepL, hcapL,
      fun a ha => by rw [hfrFail a (Or.inr (by omega))]; exact hzL a ha, by omega,
      fun U' hB' => ?_, ?_,
      fun a ha => (hfootL_range a ha).imp_right (fun ⟨h1', h2'⟩ =>
        ⟨by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at h1'; omega, h2'⟩),
      hnumL.mono (le_add_of_nonneg_right hXnn) (le_add_of_nonneg_right hXnn),
      hoffL.sep.of_agree fun e he => (hagFail _ (solverStateRep_recPtr_foot hrepL' he)).symm⟩
    · refine ⟨Num.fixVal mem eta 4 L P, by rw [hfmt4]; exact hetaCopyVal ▸ hScalF,
        by rw [hfmt4]; exact hetaCopyVal ▸ hNormF,
        by rw [hfmt4]; exact fun e he => hFits0 e he,
        fun U' hB' => ?_⟩
      have hUeq : U' = U := batchAt_unique_of_refresh hRefreshU hbatch0 hB'
      rw [hUeq]
      dsimp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [hfmt4, algorithm2_dsWithFailureWith_update_none cfg (1 / (2 : ℝ) ^ k) model U gVec lVec _ hOpt]
      exact ⟨rfl, by simpa [heapArg] using hAnsF⟩
    · have hUeq : U' = U := batchAt_unique_of_refresh hRefreshU hbatch0 hB'
      rw [hUeq]
      have hh5Hi' : h5 ≤ h4 + (NS + 1) * cycleLoopIterSpace L findSpace shiftSpace := hh5Hi
      obtain ⟨hcR', hcL', hsubAC'⟩ :=
        update_credit_telescope (L := L) (B0 := cycleLoopIterBudget L cfg.P.d findBudget shiftBudget)
          (N0 := N) (N1 := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) loopRes.1)
          (refBud := refreshBudget U.length)
          (phi0 := Rrep.phi root tok mem + K * sg.reembPot)
          (phiR := Rrep.phi root tokR stR.mem + K * sgR.reembPot)
          (phiL := Rrep.phi root tokL stFail.mem + K * sgL.reembPot)
          (k := k) (gVec := gVec) (lVec := lVec) hMono hcR0 (by rw [hphiFail]; exact hcL)
      have htot := updateBudgetBound_fail_le (n := G.n) (maxEdges := maxEdges)
        (maxPaths := maxPaths) (drainUnit := drainUnit) hcPrep hcR' hcL' hcFail
      refine ⟨updateSpaceBound_good_le hh0_ge hh3LeBound hh4Hi hh5Hi' (by omega), ?_⟩
      change _ + (Rrep.phi root tokL stFail.mem + K * sgL.reembPot) +
          shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) loopRes.1 *
            cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
          toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
        updateBudgetBound L cfg.P.d G.n tok.intCap model.nextFresh U.length N findBudget shiftBudget
          maxEdges maxPaths drainUnit (refreshBudget U.length) +
          (Rrep.phi root tok mem + K * sg.reembPot) +
          toolMul * loopRes.1.totalRuntime + treeMul * loopRes.1.totalTreeUpdates
      dsimp only [loopRes, model1] at htot hsubAC' ⊢
      omega
    · intro a ha hnf
      exact (hfrFail a (Or.inl ha)).trans (hfrL_ltHeap a ha hnf)
  | some Δ =>
    have hfb1 : foundBit = 1 := by simp [foundBit, hOpt]
    obtain ⟨inner, norm, edges, paths, hdescL', hedMax, hptMax, htagEd, htagPt, htag18, hcurDescLo, hcurDescHi⟩ :=
      hdescL (by rw [hOpt]; rfl)
    have ⟨hΔEq, hΔGood⟩ := algorithm2_loopWith_some_spec cfg (1 / (2 : ℝ) ^ k)
      model1.extG model1.extToInt model1.extg model1.extℓ model1.chain model1.branD model1.passes
      model1.lctUpdateOps Δ hOpt
    have htrFst : (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).1 = G := by
      rw [translateBatch_fst, hextEq, hRefreshU.2.1]
    have hExtEqL : modelLoop.extG = G := htrFst
    let request := Num.intVal mem eta 4 L
    have hetaCopyAt : PathIntAt s12.mem etaCopy 4 L request :=
      ⟨numValid_congr hetaValid hetaCopyL, numIntVal_congr hetaCopyL⟩
    have hh5Hi' : h5 ≤ h4 + (NS + 1) * cycleLoopIterSpace L findSpace shiftSpace := hh5Hi
    obtain ⟨hEnd, cGood, stGA, tokEnd, rGoodSeq, hout1, houtScal, hnormWithin, hFitsEnd, hrepEnd,
        hpresGood, hintCapGood, hzEnd, hhEndLo, hhEndHi, hfrGA, hftGA, hcGood, hnumGood⟩ :=
      solverUpdateGoodBranch_runs (psi := psi) (k := k) (epsExp := epsExp) (drainUnit := drainUnit)
        (copyWords := lay.copyWords) (subtract := lay.subtract) (goodApply := lay.goodApply) (initTree := lay.pathTree)
        (goodNormOut := lay.goodNormOut) (applyPaths := lay.applyPaths) (applyOffTree := lay.applyOffTree)
        (pathNorm := lay.pathNorm) (pathFlowTag := lay.pathFlowTag) (explicitRouteUpdate := lay.expRouteUpd)
        (offTreePush := lay.offTreePush) (isNeg := lay.isNeg) (maxEdges := maxEdges) (maxPaths := maxPaths)
        (root := root) (heap := heap) (descOut := descOut) (zeroBlock := zeroBlock)
        (etaCopy := etaCopy) (h0 := h0) (h5 := h5) (F := F) (G := G) (s12 := s12)
        hlocalCore hfmt4 hall.1 hall.2.1
        hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hall.2.2.2.2.2.2.2.2.2.1
        hall.2.2.2.2.2.2.2.2.2.2.1 (hall.2.2.2.1 F.fmt F.limbs hfmt4)
        (hall.2.2.2.2.2.2.2.2.2.2.2.1 F.limbs) hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hall.2.2.1 hBridge
        hExtEqL hFits0 hflow0 hκα hprec hglIn
        hrepL' hnumL hoffL le_rfl le_rfl hdescL' hedMax hptMax htagEd htagPt htag18
        hΔEq hΔGood hetaCopyAt hetaLo hetaHi hzeroBlockL hzL
        (fun a ha => (hfootL_range a (Or.inl ha)).imp_left (hbelow a))
        ⟨by simp [s12, s11, s10p, s10, hs9r0], by simp [s12, s11, s10p, s10, hs9r5], by simp [s12, s11, s10p, s10, hs9r7, L],
         by simp [s12, s11, s10p, s10, hs9r13, descOut], by simp [s12, s11, s10p, s10, hs9r15, zeroBlock, quotaBase, descOut],
         by simp [s12, s11], by simp [s12, s11, s10p, s10, hs9r31, etaCopy, zeroBlock, quotaBase, descOut]⟩
        ⟨rfl, by dsimp only [zeroBlock, quotaBase, descOut]; omega, rfl, by dsimp only [h0, gCopy]; omega, by omega,
         by change h0 ≤ stL.mem (descOut + 1); omega, hcurDescHi⟩
        (by omega) hPW h2nW hlogW hsizeM hmaxEP hcapTreeB hcapOffB (by
          change h5 + 2 * L + goodApplySpace L maxPaths maxEdges + 2 < 2 ^ w
          dsimp only [copyLen, updateSpaceBound] at hh5Hi' hh4Hi hh3LeBound hroomU hh0_ge ⊢; omega)
    have rCondGood : Runs w p ω (.cond (.reg 22) goodBranch failBranch) s12 (.returned hEnd) stGA (1 + cGood + 1) :=
      runs_cond_iff.mpr ⟨1, cGood, by simp [Expr.eval, s12, hfb1],
        by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact rGoodSeq, by simp [Expr.size]⟩
    let mult := pathMultiplier P request (-inner)
    let actual := -(((mult : ℝ) / (2 : ℝ) ^ P) * ((inner : ℝ) / (2 : ℝ) ^ P))
    let inc : ℕ → ℝ := fun e =>
      if e ∈ modelLoop.extG.E then -(actual / modelLoop.extG.inner modelLoop.extg Δ) * Δ e else 0
    let modelEnd : Alg2State cfg :=
      { modelLoop with
        flow := fun e => modelLoop.flow e + inc e
        detectAccum := fun e => modelLoop.detectAccum e + |inc e| }
    have hCapsEnd : SolverLevelCapsInv P V vCap eCap modelEnd tokEnd stGA.mem :=
      hpresGood.to_capsInv hCapsL' rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) rfl
    have hagOwnGA (a : ℕ) (ho : sgL.owned a) : stGA.mem a = stL.mem a := by
      have hdisjA : a < h5 ∧ (a < heap ∨ heap + 1 + 2 * L ≤ a) := by
        rcases hfootL_range a (Or.inr ho) with h0' | ⟨hlo, hhi⟩
        · have := hbelow a h0'
          exact ⟨by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hh2GeH0 hh3GeH2 hh4Lo hh5Lo ⊢; omega, Or.inl this⟩
        · exact ⟨hhi, Or.inr (by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hlo; omega)⟩
      exact hfrGA a hdisjA.1 hdisjA.2 (hSelL'.2.1 a ho)
    have hoffGA (a : ℕ) (ho : sgL.owned a) : ¬ Rrep.foot root tokEnd a := fun hf' => by
      rcases hftGA a hf' with hf | ⟨hlo, _⟩
      · exact hSelL'.2.1 a ho hf
      · rcases hfootL_range a (Or.inr ho) with h0' | ⟨_, hhi⟩
        · have := hbelow a h0'
          dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hh2GeH0 hh3GeH2 hh4Lo hh5Lo ⊢; omega
        · omega
    have hSelEnd : SolverSelectInv G L P m dMul kOff tokEnd.table modelEnd (Rrep.foot root tokEnd)
        (LevelMetaFoot tokEnd) sgL stGA.mem := by
      rw [hpresGood.1]
      obtain ⟨hSt, _, G₀, σ, σ_mwu, γ_ℓ, γ_c, hMod⟩ := hSelL'
      refine ⟨fun mem₁ hag₁ => (hSt mem₁ fun a ha => ha.elim
          (fun hm => (hag₁ a (Or.inl (hpresGood.levelMetaFoot_mono hm))).trans (hpresGood.metaEq a hm).2)
          (fun ho => (hag₁ a (Or.inr ho)).trans (hagOwnGA a ho))).mono_foot
          (fun _ hm => hpresGood.levelMetaFoot_mono hm) rfl,
        hoffGA, G₀, σ, σ_mwu, γ_ℓ, γ_c, hMod.of_chain_ext rfl rfl rfl⟩
    have hRegEnd : SolverSelectRegionInv G L P m F.rangeExponent pLast slot vCap eCap modelEnd
        (Rrep.foot root tokEnd) tokEnd sgL stGA.mem :=
      hRegL'.congr hCapsL'.1 hpresGood hoffGA hagOwnGA rfl rfl rfl
    refine ⟨hEnd, _, stGA, modelEnd, tokEnd, sgL, hchainAll rCondGood, ?_, hrepEnd, hCapsEnd,
      hpresGood.to_levelLayout hCapsL'.1 hLayL, hSelEnd, hReembL, hRegEnd, hDeepL,
      fun U' hB' => hintCapGood.trans (hcapL U' hB'), hzEnd, by omega,
      fun U' hB' => ?_, ?_, ?_, ?_⟩
    rotate_right
    · obtain ⟨Bg, Rg, hnumG, hBg, hRg, hrecG, hptrG⟩ := hnumGood
      refine ⟨hnumG.mono hBg hRg, ?_⟩
      show OffTreeRecSep modelLoop L stGA.mem tokEnd.edgeRecords
      rw [hrecG]
      exact hoffL.sep.of_copy fun e he => hptrG _ (solverStateRep_extToInt_lt hrepL' he)
    · refine ⟨actual, by rw [hfmt4]; exact houtScal, by rw [hfmt4]; exact hnormWithin,
        by rw [hfmt4]; exact hFitsEnd, fun U' hB' => ?_⟩
      have hUeq : U' = U := batchAt_unique_of_refresh hRefreshU hbatch0 hB'
      rw [hUeq]
      dsimp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [hfmt4, algorithm2_dsWithFailureWith_update_some cfg (1 / (2 : ℝ) ^ k) model U gVec lVec actual Δ hOpt]
      exact ⟨rfl, by simp [AnswerAt, heapArg, hout1]⟩
    · have hUeq : U' = U := batchAt_unique_of_refresh hRefreshU hbatch0 hB'
      rw [hUeq]
      obtain ⟨hcR', hcL', hsubAC'⟩ :=
        update_credit_telescope (L := L) (B0 := cycleLoopIterBudget L cfg.P.d findBudget shiftBudget)
          (N0 := N) (N1 := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) loopRes.1)
          (refBud := refreshBudget U.length)
          (phi0 := Rrep.phi root tok mem + K * sg.reembPot)
          (phiR := Rrep.phi root tokR stR.mem + K * sgR.reembPot)
          (phiL := Rrep.phi root tokL stL.mem + K * sgL.reembPot)
          (k := k) (gVec := gVec) (lVec := lVec) hMono hcR0 hcL
      have hcGood' : cGood + (Rrep.phi root tokEnd stGA.mem + K * sgL.reembPot) ≤
          updateGoodBranchBudget L G.n maxEdges maxPaths drainUnit +
            (Rrep.phi root tokL stL.mem + K * sgL.reembPot) := by
        change cGood + Rrep.phi root tokEnd stGA.mem ≤
          updateGoodBranchBudget L G.n maxEdges maxPaths drainUnit + Rrep.phi root tokL stL.mem at hcGood
        omega
      have htot := updateBudgetBound_good_le (n := G.n) (maxEdges := maxEdges)
        (maxPaths := maxPaths) (drainUnit := drainUnit) hcPrep hcR' hcL' hcGood'
      refine ⟨updateSpaceBound_good_le hh0_ge hh3LeBound hh4Hi hh5Hi' hhEndHi, ?_⟩
      change _ + (Rrep.phi root tokEnd stGA.mem + K * sgL.reembPot) +
          shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) loopRes.1 *
            cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
          toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
        updateBudgetBound L cfg.P.d G.n tok.intCap model.nextFresh U.length N findBudget shiftBudget
          maxEdges maxPaths drainUnit (refreshBudget U.length) +
          (Rrep.phi root tok mem + K * sg.reembPot) +
          toolMul * loopRes.1.totalRuntime + treeMul * loopRes.1.totalTreeUpdates
      dsimp only [loopRes, model1] at htot hsubAC' ⊢
      omega
    · intro a ha hnf
      have hnfL : ¬ Rrep.foot root tokL a := fun hf => by
        rcases hfootL_range a (Or.inl hf) with h0' | ⟨hlo, _⟩
        · exact hnf h0'
        · have : heap ≤ h0 := by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut]; omega
          exact absurd (lt_of_lt_of_le ha this) (not_lt_of_ge hlo)
      exact (hfrGA a (by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut] at hh2GeH0 hh3GeH2 hh4Lo hh5Lo ⊢; omega) (Or.inl ha) hnfL).trans
        (hfrL_ltHeap a ha hnf)
    · intro a ha
      have hheap_h0 : heap ≤ h0 := by dsimp only [h0, gCopy, etaCopy, zeroBlock, quotaBase, descOut]; omega
      have hheap_h5 : heap ≤ h5 := le_trans hheap_h0 (le_trans (le_trans (Nat.le_add_right _ _) hh2GeH0)
        (le_trans hh3GeH2 (le_trans hh4Lo hh5Lo)))
      rcases ha with hf | ho
      · rcases hftGA a hf with h0' | ⟨hlo, hhi⟩
        · exact (hfootL_range a (Or.inl h0')).imp_right fun ⟨h1', h2'⟩ =>
            ⟨le_trans hheap_h0 h1', lt_of_lt_of_le h2' (le_trans (Nat.le_add_right _ _) hhEndLo)⟩
        · exact Or.inr ⟨le_trans hheap_h5 (le_trans (Nat.le_add_right _ _) hlo), hhi⟩
      · exact (hfootL_range a (Or.inr ho)).imp_right fun ⟨h1', h2'⟩ =>
          ⟨le_trans hheap_h0 h1', lt_of_lt_of_le h2' (le_trans (Nat.le_add_right _ _) hhEndLo)⟩

end MinCostFlow.MinRatio
