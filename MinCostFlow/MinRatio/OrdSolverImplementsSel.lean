module

public import MinCostFlow.MinRatio.OrdSolverImplementsFull
public import MinCostFlow.MinRatio.OrdSolverRepSelKFBL
public import MinCostFlow.MinRatio.UpdateAssemblySel
public import MinCostFlow.MinRatio.SolverSelectPreserve
public import MinCostFlow.MinRatio.SolverTreeBudgetSteps
import Mathlib.Tactic

/-!
# `DSRep.Implements` for the select-aware solver representation `solverStateRepSelKFBL`

Proves `ordSolver_implements_sel_credit`: the solver implements `minRatioMachineContractWithV`
under `solverStateRepSelKFBL` (`OrdSolverRepSelKFBL.lean`, which carries `solverStateRepSel`,
`SolverLevelCapsInv`, `DeepInv` and `SolverSelectRegionInv`) from:
* `SolverInitStepSpecSel` (`OrdSelSpecs.lean`, discharged by `solverInitWiredSel_runs`),
* `ChainRefreshStepSpecWKFBLSel` (`OrdSelSpecs.lean`),
* `FindCycleStepSpecHeap` (`WireSelectSpec.lean`),
* `ShiftLevelStepSpecWKFBLSel` (`OrdSelSpecs.lean`),
* `OrdSolverContractEnvelopeFullCredit` (`OrdSolverImplementsFull.lean`).

`Query` and `Detect` are discharged directly by `solverOps_query_preserves_sel` and
`solverOps_detect_preserves_sel` (`SolverSelectPreserve.lean`), and `Update` is discharged by
`solverOps_update_runs_credit_sel` (`UpdateAssemblySel.lean`) with `update_fwd_amortized` and
`wire_dual_credit_update_step` over the combined potential `Rrep.phi + K * sg.reembPot`.

The rep also carries the tree budget `SolverTreeBudgetInv` at `B₀ + c X`, `c X`, where `c` counts
the `Update`s (`SolverTreeBudgetSteps.lean`). Init gives it at `c = 0`. `Query` and `Detect` keep
it. `Update` runs at that budget, which is at most `B_bound`, `R_bound` since `c ≤ 2 G.m`, and
gives it at `c + 1`. This uses one new hypothesis, `B₀ + 2 G.m X ≤ B_bound ∧ 2 G.m X ≤ R_bound`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore.Program Scaling Scaling.Machine Final

/-- Every state reached by Algorithm 2 on a connected graph satisfies `ShiftLoopChainInv`. -/
theorem OrdSolverReached.shiftLoopChainInv {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {model : Alg2State cfg} (h : OrdSolverReached cfg κ G model) (hV : cfg.ValidOrdNoHidden)
    (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) :
    Ordered.ShiftLoopChainInv cfg model.chain := by
  obtain ⟨D, η, op, T, hHist, hE, hL, hG, hm⟩ := h
  have hI := (Ordered.algorithm2_uncond_preserves_with (η := η) κ hV hHist hE hL
    (fun t ht => by rw [hG t ht]; exact hmG) (fun t ht => by rw [hG t ht]; exact hnG)).1 T le_rfl
  rcases hI with ⟨hInv, hBud, _, _, hFresh, hExtG, hExtℓ, hChℓ, _, _, _, _, _, _, _⟩
  rw [← hm] at hInv hBud hFresh hExtG hExtℓ hChℓ
  have hℓPos := (hHist.2.1 T le_rfl).2
  refine ⟨hInv, ⟨_, hBud⟩, fun e' he' => ?_,
    hFresh.connected (by rw [hExtG, hG T le_rfl]; exact hConn)⟩
  rw [hChℓ]
  dsimp only
  rw [(hExtℓ _ (hExtG ▸ (hFresh.hRight e' he').2)).1]
  exact hL.lenInRange le_rfl hℓPos _ (hExtG ▸ (hFresh.hRight e' he').2)

set_option maxHeartbeats 800000 in
/-- **Select-aware `DSRep.Implements` theorem for `solverStateRepSelKFBL`.**
Discharges `DSRep.Implements` against `minRatioMachineContractWithV` from `SolverInitStepSpecSel`,
`ChainRefreshStepSpecWKFBLSel`, `FindCycleStepSpecHeap`, `ShiftLevelStepSpecWKFBLSel`,
`GoodCycleNumericBridge`, and `OrdSolverContractEnvelopeFullCredit`. -/
theorem ordSolver_implements_sel_credit
    {w base initProc chainRefreshProc findCycleProc shiftLevelProc m U_cap V psi k epsExp
      capExp limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap dMul kOff K pLast slot
      initSpace initBudget findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths
      toolMul treeMul : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph} {pot : cfg.T.State → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {DeepInv : ChainState cfg.T cfg.P → Prop}
    {p : Program} {B_bound R_bound : ℤ}
    {refreshSpace refreshBudget : ℕ → ℕ} {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ}
    (hMono : toolMul = 0 ∨ ToolCostMono cfg.T)
    (hV : cfg.ValidOrdNoHidden) (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ)
    (hw : 14 ≤ w) (hfmt4 : F.fmt.limbBits = 4) (hLpos : 0 < F.limbs)
    (hPL : F.fmt.precision ≤ 4 * F.limbs)
    (hmPos : 0 < m) (hεPos : 0 < cfg.ε) (hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent)
    (hthrB : (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_bound)
    (hα : cfg.α = Num.IPM.alphaPrime m U_cap / 8)
    (hepsExp : epsExp = k + Num.IPM.alphaExponent m U_cap + 10)
    (hGE : ∀ e < m, e ∈ G.E)
    (h5L1W : 5 * F.limbs + 1 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) (hepsW : epsExp < 2 ^ w)
    (hQuotaBoundW : (2 * G.m + 2) *
      shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) < 2 ^ w)
    (h2nW : 2 * G.n + 1 < 2 ^ w) (hlogW : Nat.log 2 (2 * G.n + 1) ≤ 4 * F.limbs)
    (hsizeM : Nat.size m ≤ F.rangeExponent + 8)
    (hmaxEP : maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20))
    (hMaxEdges1 : 1 ≤ maxEdges) (hMaxEP2 : 2 * maxEdges ≤ maxPaths)
    (hEmbBd : ∀ ch, Chain.Ordered.ShiftLoopChainInv cfg ch →
      ∀ i < cfg.P.d, ∀ e ∈ (ch.toTreeChain.activeCore i).E \ (ch.toTreeChain.activeS i).E,
        (ch.toTreeChain.activeEmb i e).length + 1 ≤ maxEdges)
    (hcapEvalB : 2 * (((maxEdges + maxPaths * G.n : ℕ) : ℤ) * B_bound) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapTreeB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) *
      ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
        (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapOffB : B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
      (Num.capacity 4 F.limbs : ℤ))
    (hBudgetB : treeBudgetBase F.fmt.precision F.rangeExponent +
        2 * (G.m : ℤ) * ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) ≤
        B_bound ∧
      2 * (G.m : ℤ) * ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) ≤ R_bound)
    (hCapLevels : ∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ capLimit →
      SparseCoreCapHyp capExp limbMul F.limbs (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap)
    (hIntCapMax : initTargetCap cfg G ≤ intCapMax)
    (hFEdgeCap : 2 * G.n ≤ forestEdgeCap)
    (hDeepInv : DeepShiftChainInvHyps w F cfg G k wordExp stretchPrec DeepInv)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc))
    (hInit : SolverInitStepSpecSel F cfg G m V psi k epsExp
      (cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget)
      toolMul treeMul dMul kOff K pLast slot pot Rcore p initProc initSpace initBudget)
    (hRefresh : ChainRefreshStepSpecWKFBLSel w F.limbs F.fmt.precision F.rangeExponent m V psi k
      epsExp (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit intCapMax forestEdgeCap
      G.n (initTargetCap cfg G) dMul kOff K pLast slot cfg G pot DeepInv Rcore p chainRefreshProc
      refreshSpace refreshBudget toolMul treeMul)
    (hFind : FindCycleStepSpecHeap w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) dMul kOff cfg Rcore p findCycleProc findSpace findBudget
      maxEdges maxPaths)
    (hShift : ShiftLevelStepSpecWKFBLSel w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap G.n (initTargetCap cfg G) dMul kOff K F.rangeExponent pLast slot cfg G pot
      DeepInv Rcore p shiftLevelProc shiftSpace shiftBudget toolMul treeMul)
    (hBridge : ∀ Bb Rb : ℤ, GoodCycleNumericBridge F cfg G m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore maxEdges maxPaths Bb Rb)
    (hEnv : OrdSolverContractEnvelopeFullCredit F cfg G m V psi k epsExp initSpace initBudget
      findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths toolMul treeMul
      refreshSpace refreshBudget Rcore rate alloc) :
    (solverStateRepSelKFBL cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) (cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget)
      toolMul treeMul dMul kOff F.rangeExponent pLast slot maxPaths Rcore K pot DeepInv).Implements w p initProc (solverOpsDispatch base)
      (minRatioMachineContractWithV F
        (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
        G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc) := by
  let B := cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget
  obtain ⟨hEnvInit, hEnv0, hEnv1, hEnv2⟩ := hEnv
  refine ⟨solverStateRepSelKFBL_local cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k
    epsExp (detectOffTreeDrainUnit F.limbs) B toolMul treeMul dMul kOff F.rangeExponent pLast slot
    maxPaths hlocalCore K pot DeepInv,
    ?_, ?_⟩
  · -- Init
    intro args mem pos ω hargsW hpre hz hroom
    obtain ⟨hspLe, hcostLe⟩ := hEnvInit args mem hpre
    obtain ⟨body, hbody, hInitRun⟩ := hInit
    obtain ⟨finalHeap, cost, out, tok, hr, hfits, hrepSel, hcapsInit, hLayInit, hRegInit, hBudInit, hresp,
      hcost⟩ :=
      hInitRun args mem pos ω hargsW hpre hz
        (by dsimp only [minRatioMachineContractWithV, minRatioMachineContractAt] at hroom; omega)
    have hwithin : LengthsWithin G F.rangeExponent
        (readVector mem (args.getD 2 0) F.fmt.limbBits F.limbs F.fmt.precision m) := by
      obtain ⟨graph, g, l, heap, hargsEq, _, _, _, _, _, _, _, _, _, _, _, _, hw', _⟩ := hpre
      subst hargsEq; exact hw'
    have hGridInit : ∀ e ∈ G.E, ∃ q : ℤ,
        (q : ℝ) / (2 : ℝ) ^ F.fmt.precision =
          readVector mem (args.getD 2 0) F.fmt.limbBits F.limbs F.fmt.precision m e := by
      intro e _
      unfold readVector; split_ifs
      · exact ⟨Num.intVal mem (args.getD 2 0 + e * F.limbs) F.fmt.limbBits F.limbs, rfl⟩
      · exact ⟨0, by simp⟩
    set s0 := Ordered.algorithm2_init cfg G
      (readVector mem (args.getD 1 0) F.fmt.limbBits F.limbs F.fmt.precision m)
      (readVector mem (args.getD 2 0) F.fmt.limbBits F.limbs F.fmt.precision m)
    have hDeep0 : DeepInv s0.chain := hDeepInv.init _ _ hwithin hGridInit
    refine ⟨body, hbody, .returned finalHeap, out, cost, hr, s0, tok,
      ⟨hrepSel, hcapsInit, hLayInit, hDeep0, hRegInit, hBudInit.of_updateCount_zero rfl⟩, ⟨rfl, hfits⟩,
      ⟨hresp.1, hresp.2.1.trans (Nat.add_le_add_left hspLe _), hresp.2.2.1, hresp.2.2.2.1,
        hresp.2.2.2.2⟩,
      le_trans hcost hcostLe⟩
  · -- Operations `0` (Update), `1` (Query), `2` (Detect)
    intro i root model tok args mem pos ω hargsW hhead hrepSK hpre hbelow hz hroom
    obtain ⟨hrepSel, hCaps, hLay, hDeep, hReg, hBud⟩ := hrepSK
    have hXnn : (0 : ℤ) ≤ (maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision) :=
      mul_nonneg (Int.natCast_nonneg _) (pow_nonneg (by norm_num) _)
    have hrepSel0 := hrepSel
    obtain ⟨hrepF, hSel, hReemb⟩ := hrepSel
    obtain ⟨hrepS, hfull, hrcG, htcG⟩ := hrepF
    obtain ⟨hrep, hfwd, hghost⟩ := hrepS
    obtain ⟨hinv, hreach, hnfB, hintCapB⟩ := hfull
    obtain ⟨hbase, hnumInv⟩ := hinv
    obtain ⟨hextEq, hlen, hBr⟩ := hbase
    obtain ⟨hcapPos, hnfLe, _⟩ := solverStateRep_intCap hrep
    have htn : tok.1.1.1.tree.n = G.n := (solverStateRep_tree_n hrep).trans (by rw [hextEq])
    have hphi : (solverStateRepSelKFBL cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k
        epsExp (detectOffTreeDrainUnit F.limbs) B toolMul treeMul dMul kOff F.rangeExponent pLast
        slot maxPaths Rcore K pot DeepInv).phi root tok mem = _ :=
      solverStateRepSelKFBL_phi_eq ⟨hrep, hfwd, hghost⟩ hrcG htcG
    match i with
    | 0 =>
      have hpre0 := hpre
      obtain ⟨_, handle_, batch, g, l, eta, heap, U0, hargsEq, _, _, _, hBU0, _, hRefU0, _, _, _,
        _, _, _, _, _, hglIn, hU0Le, hdet⟩ := hpre
      subst hargsEq
      have hrEq : handle_ = root := by simpa using hhead
      cases hrEq
      have hheapArg : heapArg [root, batch, g, l, eta, heap] = heap := rfl
      rw [hheapArg] at hbelow hz hroom
      obtain hUBounds :=
        hEnv0 root batch g l eta heap mem model tok.1.1.1 hrep
          ⟨⟨⟨hextEq, hlen, hBr⟩, hnumInv⟩, hreach, hnfB, hintCapB⟩
          hpre0 (fun a ha => hbelow a (Or.inl ha))
      have hroomU : ∀ U, BatchAt mem batch U →
          let model1 := alg2PreLoopState cfg model U (readVector mem g 4 F.limbs F.fmt.precision m) (readVector mem l 4 F.limbs F.fmt.precision m)
          heap + updateSpaceBound F.limbs m cfg.P.d model.nextFresh U.length (loopStepBound cfg model1)
            findSpace shiftSpace maxEdges maxPaths (refreshSpace U.length) + 2 < 2 ^ w := fun U hBU => by
        have hsp := (hUBounds U hBU).1
        simp only [minRatioMachineContractWithV, minRatioMachineContractAt] at hroom hsp ⊢
        omega
      have hpsiLimW : ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ < 2 ^ w :=
        lt_of_le_of_lt (ceil_two_mul_alg2PsiGame_le_quotaBound cfg G.m) hQuotaBoundW
      have hCapModel : WireCapFacts capExp limbMul F.limbs capLimit model := by
        obtain ⟨D, η, op, T, hHist, hE, hL, hG, hm⟩ := hreach
        have hInv := ((Ordered.algorithm2_uncond_preserves_with (η := η) (1 / (2 : ℝ) ^ k) hV hHist
          hE hL (fun t ht => by rw [hG t ht]; exact hmG)
          (fun t ht => by rw [hG t ht]; exact hnG)).1 T le_rfl).1
        rw [← hm] at hInv
        intro j hj vCap eCap hlim
        rw [hInv.hLvlM, hInv.hN0]
        exact hCapLevels j hj vCap eCap hlim
      have hquotasW : ∀ U, BatchAt mem batch U →
          let model1 := alg2PreLoopState cfg model U
            (readVector mem g 4 F.limbs F.fmt.precision m) (readVector mem l 4 F.limbs F.fmt.precision m)
          ∀ i ≤ cfg.P.d,
            shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i < 2 ^ w :=
        fun U _ i hi => lt_of_le_of_lt (detectedWith_preLoop_shiftQuota_le hdet U _ _ hi) hQuotaBoundW
      have hLoopInv0 : Chain.Ordered.ShiftLoopChainInv cfg model.chain :=
        hreach.shiftLoopChainInv hV hmG hnG hConn
      have hLoopInv : ∀ U, BatchAt mem batch U →
          Chain.Ordered.ShiftLoopChainInv cfg (alg2PreLoopState cfg model U
            (readVector mem g 4 F.limbs F.fmt.precision m)
            (readVector mem l 4 F.limbs F.fmt.precision m)).chain := by
        intro U hBU
        obtain rfl := batchAt_unique_of_refresh hRefU0 hBU0 hBU
        have h := hreach.preLoop_shiftLoopChainInv hV hmG hnG hConn hRefU0
          (fun e he => lt_of_lt_of_le (by positivity) (hglIn e he).2.1)
          (fun e he => (abs_log_le_of_two_pow_bounds (hglIn e he).2.1 (hglIn e he).2.2).trans hEΨ)
          (fun e he hnot => ordAlg2_detectedWith_agree hdet e he fun ⟨u, hu, hi⟩ => hnot u hu hi)
        rwa [hfmt4] at h
      have hmLeGm : m ≤ G.m := by
        have hsub : Finset.range m ⊆ G.E := fun e he => hGE e (Finset.mem_range.mp he)
        simpa [MGraph.m] using Finset.card_le_card hsub
      have hNoGrow : ∀ U, BatchAt mem batch U → model.nextFresh + U.length ≤ tok.1.1.1.intCap := by
        intro U hBU
        obtain rfl := batchAt_unique_of_refresh hRefU0 hBU0 hBU
        unfold initTargetCap at hintCapB
        omega
      -- The budget at the start of `Update` is `B₀ + c X`, `c X`, with `c ≤ 2 G.m`.
      have hcU : model.updateCount ≤ 2 * G.m := ordAlg2_detected_updateCount_le hdet
      have hB0c : treeBudgetBase F.fmt.precision F.rangeExponent ≤
          treeBudgetBase F.fmt.precision F.rangeExponent + (model.updateCount : ℤ) *
            ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) :=
        le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg _) hXnn)
      have hBc := treeBudget_le_bound hXnn hcU hBudgetB.1
      have hRc := treeBudget_le_rbound hXnn hcU hBudgetB.2
      have hcapEvalBc : 2 * (((maxEdges + maxPaths * G.n : ℕ) : ℤ) *
          (treeBudgetBase F.fmt.precision F.rangeExponent + (model.updateCount : ℤ) *
            ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision)))) <
          (Num.capacity 4 F.limbs : ℤ) := by
        have := mul_le_mul_of_nonneg_left hBc (Int.natCast_nonneg (maxEdges + maxPaths * G.n))
        linarith
      have hcapOffBc : treeBudgetBase F.fmt.precision F.rangeExponent + (model.updateCount : ℤ) *
            ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
          (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) < (Num.capacity 4 F.limbs : ℤ) := by
        linarith
      have hacc0 : ∀ e ∈ model.extG.E, 0 ≤ model.detectAccum e ∧
          model.extℓ e * model.detectAccum e < cfg.ε :=
        fun e he => ⟨hBud.2.2.1 e, ordAlg2_detected_accum_lt hdet hεPos e he⟩
      obtain ⟨body, hbody, ret, cost, out, model', tok', sg', hr, hpost, hrep', hCaps', hLay', hSel',
          hReemb', hReg', hDeep', hintCap', hz', hretLo, hretAndCost, hframe', hfoot', hnum',
          hsep'⟩ :=
        solverOps_update_runs_credit_sel (w := w) (base := base) (chainRefreshProc := chainRefreshProc)
          (findCycleProc := findCycleProc) (shiftLevelProc := shiftLevelProc)
          (m := m) (U_cap := U_cap) (V := V) (psi := psi) (k := k) (epsExp := epsExp)
          (capExp := capExp) (limbMul := limbMul) (capLimit := capLimit)
          (wordExp := wordExp) (stretchPrec := stretchPrec) (intCapMax := intCapMax)
          (forestEdgeCap := forestEdgeCap) (vCap := G.n) (eCap := initTargetCap cfg G)
          (dMul := dMul) (kOff := kOff) (K := K) (pLast := pLast) (slot := slot)
          (findSpace := findSpace) (findBudget := findBudget)
          (shiftSpace := shiftSpace) (shiftBudget := shiftBudget)
          (maxEdges := maxEdges) (maxPaths := maxPaths) (toolMul := toolMul) (treeMul := treeMul)
          (root := root) (batch := batch) (g := g) (l := l) (eta := eta) (heap := heap) (pos := pos)
          (F := F) (cfg := cfg) (G := G) (pot := pot) (DeepInv := DeepInv)
          (B_bound := treeBudgetBase F.fmt.precision F.rangeExponent + (model.updateCount : ℤ) *
            ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision)))
          (R_bound := (model.updateCount : ℤ) *
            ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision)))
          hlocalCore hMono hw hfmt4 hV hPL hα hepsExp hp
          hRefresh hFind hShift (hBridge _ _) hMaxEdges1 hMaxEP2 hEmbBd hFEdgeCap
          (fun U gVec lVec hU hLen hGrid hAg hD =>
            hDeepInv.preLoop model U gVec lVec hreach hextEq hU hLen hGrid hAg hD)
          hDeepInv.shift hDeepInv.toModel hrep hCaps hLay hSel hReemb hReg hreach hDeep hnumInv
          hBud.2.2.2.2 hBud.2.2.2.1 hB0c hεPos hεLe hBud.2.1 hacc0
          hintCapB (hintCapB.symm ▸ hIntCapMax) hNoGrow hLoopInv0
          hCapModel hpre0 hextEq hBr hbelow hGE hz hmPos hcapPos hnfLe h5L1W hdW hepsW hpsiLimW
          h2nW hlogW hsizeM hmaxEP hcapEvalBc
          (treeBudget_fit_succ hXnn hcU hBudgetB.1 hBudgetB.2 hcapTreeB) hcapOffBc
          hroomU hquotasW hLoopInv
      obtain ⟨actual, _, _, _, hres⟩ := hpost
      have hm' : model' = ((Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).update
          model U0 (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
          (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) actual).1 := (hres U0 hBU0).1
      have hlpos : ∀ e ∈ G.E, 0 < readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m e :=
        fun e he => lt_of_lt_of_le (by positivity) (hglIn e he).2.1
      have hlR : ∀ e ∈ G.E,
          |Real.log (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m e)| ≤ cfg.Ψ :=
        fun e he => (abs_log_le_of_two_pow_bounds (hglIn e he).2.1 (hglIn e he).2.2).trans hEΨ
      have hagree : ∀ e ∈ G.E, (∀ u ∈ U0, ¬ u.Inserts e) →
          readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m e = model.extg e ∧
            readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m e = model.extℓ e :=
        fun e he hnot => ordAlg2_detectedWith_agree hdet e he fun ⟨u, hu, hi⟩ => hnot u hu hi
      have hPreFwd := hreach.preLoop_fwd hV hmG hnG hRefU0 hlpos hlR hagree
      have hreach' : OrdSolverReached cfg (1 / (2 : ℝ) ^ k) G model' := by
        rw [hm']
        exact ordSolverReached_update hreach actual hRefU0 hlpos hlR hagree
      obtain ⟨hRtBefore, hTuBefore⟩ := hreach.runtime_and_tree_le_cap hV hmG hnG
      obtain ⟨hRtAfter, hTuAfter⟩ := hreach'.runtime_and_tree_le_cap hV hmG hnG
      have hbase' : OrdSolverReachBase G model' := by
        rw [hm']
        refine ordSolverReachBase_update ⟨hextEq, hlen, hBr⟩ hRefU0 fun e he => ?_
        exact lt_of_lt_of_le (by positivity) (hglIn e he).2.1
      have hg' : model'.extg = readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m := by
        rw [hm']; exact (ordAlg2_update_ext cfg _ model U0 _ _ _).1
      have hl' : model'.extℓ = readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m := by
        rw [hm']; exact (ordAlg2_update_ext cfg _ model U0 _ _ _).2
      have hnumStep : SolverTreeNumericInv F.fmt.precision model' tok' := by
        refine solverTreeNumericInv_of_update (E := F.rangeExponent) (n := G.n) hεPos hεLe
          ((solverStateRep_tree_n hrep').trans (by rw [hbase'.1])) hnum' (by linarith)
          (by linarith) hcapTreeB hXnn hthrB fun e he => ?_
        rw [hl']
        exact (hglIn e (hbase'.1 ▸ he)).2.1
      -- The new count is `c + 1`, and the good branch raised the budget by `X`.
      have hBud' : SolverTreeBudgetInv G F.fmt.precision F.rangeExponent
          ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) model' tok' out.mem := by
        refine SolverTreeBudgetInv.update_step hcU ?_ ?_ (fun e => ?_) hsep' hnum'
        · rw [hm']; exact ordAlg2_updateWith_updateCount cfg _ model U0 _ _ _
        · intro e he
          rw [hg', hl']
          exact hglIn e (hbase'.1 ▸ he)
        · rw [hm']
          exact ordAlg2_updateWith_detectAccum_nonneg cfg _ model U0 _ _ _ hBud.2.2.1 e
      obtain ⟨hretHi, hcostHi⟩ := hretAndCost U0 hBU0
      obtain ⟨hspDom, hcostDom⟩ := hUBounds U0 hBU0
      have hg4 : readVector mem g 4 F.limbs F.fmt.precision m =
          readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m := by rw [hfmt4]
      have hl4 : readVector mem l 4 F.limbs F.fmt.precision m =
          readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m := by rw [hfmt4]
      rw [updateBudgetBound_eq, hm', hg4, hl4] at hcostHi
      have hfrInv : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh :=
        hrep.2.2.2.2.1
      have hcostShift : cost +
          ((solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp (detectOffTreeDrainUnit F.limbs) Rcore).phi
              root tok' out.mem + K * sg'.reembPot +
            toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates) +
          shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
              ((Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).update model U0
                (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
                (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) actual).1.chain * B ≤
          updateBudgetNoLoop F.limbs G.n tok.1.1.1.intCap model.nextFresh U0.length maxEdges maxPaths
              (detectOffTreeDrainUnit F.limbs) (refreshBudget U0.length) +
            (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
              (alg2PreLoopState cfg model U0
                (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
                (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m)).chain + 1) * B +
            ((solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp (detectOffTreeDrainUnit F.limbs) Rcore).phi
                root tok.1.1.1 mem + K * tok.2.reembPot +
              toolMul * ((Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).update model U0
                (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
                (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) actual).1.chain.totalRuntime +
              treeMul * ((Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).update model U0
                (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
                (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) actual).1.chain.totalTreeUpdates) := by
        dsimp only [B]
        omega
      have hA := update_fwd_amortized cfg (1 / (2 : ℝ) ^ k) model U0
        (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
        (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m)
        actual hcostShift hfwd hPreFwd
      dsimp only at hA
      obtain ⟨hamort, hfwd'⟩ := hA
      have hDual := wire_dual_credit_update_step cfg (1 / (2 : ℝ) ^ k) model U0
        (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
        (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m)
        actual
        (cost := cost)
        (phi := (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
            (detectOffTreeDrainUnit F.limbs) Rcore).phi root tok.1.1.1 mem + K * tok.2.reembPot +
          B * (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain +
                chainShiftDeposit cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain) +
          B * fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) model.chain)
        (phi' := (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
            (detectOffTreeDrainUnit F.limbs) Rcore).phi root tok' out.mem + K * sg'.reembPot +
          B * (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
                ((Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).update model U0
                  (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
                  (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) actual).1.chain +
              chainShiftDeposit cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀)
                ((Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).update model U0
                  (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
                  (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) actual).1.chain) +
          B * fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg)
              ((Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).update model U0
                (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
                (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) actual).1.chain)
        (fixed := updateBudgetNoLoop F.limbs G.n tok.1.1.1.intCap model.nextFresh U0.length
            maxEdges maxPaths (detectOffTreeDrainUnit F.limbs) (refreshBudget U0.length) +
          B + B * fwdWeight cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) 0 * U0.length)
        (toolMul := toolMul) (treeMul := treeMul)
        hfrInv (hextEq ▸ hRefU0.1) hfwd hPreFwd hRtBefore hTuBefore
        (hm' ▸ hRtAfter) (hm' ▸ hTuAfter) (by omega)
      dsimp only at hDual
      have hrepS' : (solverStateRepShift cfg F.limbs F.fmt.precision m V psi k epsExp
          (detectOffTreeDrainUnit F.limbs) B Rcore).rep root model'
          (tok', fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) model'.chain)
          out.mem :=
        ⟨hrep', by rw [hm']; exact hfwd', rfl⟩
      have hintCapEq' : tok'.intCap = initTargetCap cfg G := by
        rw [hintCap' U0 hBU0, ite_eq_right (by unfold initTargetCap at hintCapB; omega)]
        exact hintCapB
      refine ⟨body, hbody, .returned ret, out, cost, hr, model',
        (((tok', fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) model'.chain),
          (runtimeCredit cfg model', treeCredit cfg model')), sg'),
        ⟨⟨⟨hrepS', ⟨⟨hbase', hnumStep⟩, hreach', hreach'.nextFresh_le hV hmG hnG, hintCapEq'⟩,
          rfl, rfl⟩, hSel', hReemb'⟩, hCaps', hLay', hDeep', hReg', hBud'⟩,
        ⟨actual, by assumption, by assumption, by assumption, hres⟩,
        ⟨hretLo, by
          rw [hheapArg]
          simp only [Outcome.value, minRatioMachineContractWithV, minRatioMachineContractAt] at hretHi hspDom ⊢
          omega,
         hz', hframe', hfoot'⟩,
        ?_⟩
      have hphi' :
          (solverStateRepSelKFBL cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k
              epsExp (detectOffTreeDrainUnit F.limbs) B toolMul treeMul dMul kOff F.rangeExponent
              pLast slot maxPaths Rcore K pot DeepInv).phi root
            ((((tok' : SolverToken cfg F.limbs Rcore),
              fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) model'.chain),
              (runtimeCredit cfg model', treeCredit cfg model')), sg') out.mem =
          (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
              (detectOffTreeDrainUnit F.limbs) Rcore).phi root tok' out.mem +
            K * sg'.reembPot +
            B * (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model'.chain +
              chainShiftDeposit cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) model'.chain) +
            B * fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) model'.chain +
            toolMul * runtimeCredit cfg model' + treeMul * treeCredit cfg model' :=
        solverStateRepSelKFBL_phi_eq hrepS' rfl rfl
      rw [hphi', hphi, hm']
      have hget1 : [root, batch, g, l, eta, heap].getD 1 0 = batch := rfl
      simp only [minRatioMachineContractWithV, minRatioMachineContractAt, hget1] at hcostDom ⊢
      dsimp only [B] at hDual ⊢
      omega
    | 1 =>
      have hpre0 := hpre
      obtain ⟨_, handle_, e, heap, hargsEq, _⟩ := hpre
      subst hargsEq
      have hrEq : handle_ = root := by simpa using hhead
      cases hrEq
      have hheapArg : heapArg [root, e, heap] = heap := rfl
      rw [hheapArg] at hbelow hz hroom
      obtain ⟨hspDom, hcostDom⟩ :=
        hEnv1 root e heap mem model tok.1.1.1 hrep
          ⟨⟨⟨hextEq, hlen, hBr⟩, hnumInv⟩, hreach, hnfB, hintCapB⟩ hpre0
      obtain ⟨body, hbody, ret, cost, out, tok', hr, hpost, hrepSel', hCaps', hLayQ, hReg', _hcapQ, hz',
          hretLo, hretHi, hframe', hfoot', hcostHi, hkeepQ, hrecQ, hptrQ⟩ :=
        solverOps_query_preserves_sel (w := w) (base := base) (chainRefreshProc := chainRefreshProc)
          (findCycleProc := findCycleProc) (shiftLevelProc := shiftLevelProc)
          (m := m) (V := V) (psi := psi) (k := k) (epsExp := epsExp)
          (unit := B) (toolMul := toolMul) (treeMul := treeMul) (dMul := dMul) (kOff := kOff)
          (vCap := G.n) (eCap := initTargetCap cfg G) (K := K)
          (root := root) (e := e) (heap := heap) (pos := pos)
          (F := F) (cfg := cfg) (G := G) (κ := 1 / (2 : ℝ) ^ k) (α := cfg.α) (pot := pot)
          hlocalCore hw hfmt4 hp hrepSel0 hCaps hReg hpre0 hbelow hz
          (htn ▸ h2nW) (htn ▸ hlogW)
          (by simp only [minRatioMachineContractWithV, minRatioMachineContractAt] at hroom; omega)
      refine ⟨body, hbody, .returned ret, out, cost, hr, model, tok',
        ⟨hrepSel', hCaps', hLayQ hLay, hDeep, hReg', hBud.query_step hrep hkeepQ hrecQ hptrQ⟩, hpost,
        ⟨hretLo, by
          rw [hheapArg]
          simp only [Outcome.value, minRatioMachineContractWithV, minRatioMachineContractAt]
          omega,
         hz', hframe', hfoot'⟩,
        ?_⟩
      simp only [minRatioMachineContractWithV, minRatioMachineContractAt, Nat.mul_one]
      change cost + (solverStateRepSel cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k
          epsExp (detectOffTreeDrainUnit F.limbs) B toolMul treeMul dMul kOff Rcore K pot).phi
          root tok' out.mem ≤
        rate m + (solverStateRepSel cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k
          epsExp (detectOffTreeDrainUnit F.limbs) B toolMul treeMul dMul kOff Rcore K pot).phi
          root tok mem
      omega
    | 2 =>
      have hpre0 := hpre
      obtain ⟨_, handle_, heap, hargsEq⟩ := hpre
      subst hargsEq
      have hrEq : handle_ = root := by simpa using hhead
      cases hrEq
      have hheapArg : heapArg [root, heap] = heap := rfl
      rw [hheapArg] at hbelow hz hroom
      obtain ⟨hspDom, hcostDom⟩ :=
        hEnv2 root heap mem model tok.1.1.1 hrep
          ⟨⟨⟨hextEq, hlen, hBr⟩, hnumInv⟩, hreach, hnfB, hintCapB⟩ hpre0
      -- `Detect` keeps the budget `B₀ + c X`, `c X`. It fits since `c ≤ 2 G.m + 1`.
      have hB0c : treeBudgetBase F.fmt.precision F.rangeExponent ≤
          treeBudgetBase F.fmt.precision F.rangeExponent + (model.updateCount : ℤ) *
            ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) :=
        le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg _) hXnn)
      have hcapD : 2 * ((2 * tok.1.1.1.tree.n + 1 : ℕ) : ℤ) *
          ((treeBudgetBase F.fmt.precision F.rangeExponent + (model.updateCount : ℤ) *
            ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) +
            (model.updateCount : ℤ) *
              ((maxPaths : ℤ) * 2 ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
          (Num.capacity 4 F.limbs : ℤ) := by
        rw [htn]
        exact treeBudget_fit hXnn hBud.1 hBudgetB.1 hBudgetB.2 hcapTreeB
      obtain ⟨body, hbody, ret, cost, out, tok', hr, hpost, hrepSel', hCaps', hLayD, hReg', _hcapD, hz',
          hretLo, hretHi, hframe', hfoot', hcostHi, hnumD, hsepD⟩ :=
        solverOps_detect_preserves_sel (w := w) (base := base) (chainRefreshProc := chainRefreshProc)
          (findCycleProc := findCycleProc) (shiftLevelProc := shiftLevelProc)
          (m := m) (V := V) (psi := psi) (k := k) (epsExp := epsExp)
          (unit := B) (toolMul := toolMul) (treeMul := treeMul) (dMul := dMul) (kOff := kOff)
          (vCap := G.n) (eCap := initTargetCap cfg G) (K := K)
          (root := root) (heap := heap) (pos := pos)
          (F := F) (cfg := cfg) (G := G) (κ := 1 / (2 : ℝ) ^ k) (α := cfg.α) (pot := pot)
          hlocalCore hw hfmt4 hLpos hp (fun e he => hextEq ▸ hGE e he) hεPos
          hBud.2.2.2.2 hcapD
          (fun e he => (abs_detectorThreshold_le_base hεPos hεLe (hBud.2.1 e he).2.1).trans hB0c)
          hrepSel0 hCaps hReg hpre0 hbelow hz (htn ▸ h2nW) (htn ▸ hlogW)
          (by simp only [minRatioMachineContractWithV, minRatioMachineContractAt] at hroom; omega)
      refine ⟨body, hbody, .returned ret, out, cost, hr, (algorithm2_detect cfg model).2, tok',
        ⟨hrepSel', hCaps', hLayD hLay, hDeep, hReg', hBud.detect_step hsepD hnumD⟩, hpost,
        ⟨hretLo, by
          rw [hheapArg]
          simp only [Outcome.value, minRatioMachineContractWithV, minRatioMachineContractAt]
          omega,
         hz', hframe', hfoot'⟩,
        ?_⟩
      simp only [minRatioMachineContractWithV, minRatioMachineContractAt,
        Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith]
      change cost + (solverStateRepSel cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k
          epsExp (detectOffTreeDrainUnit F.limbs) B toolMul treeMul dMul kOff Rcore K pot).phi
          root tok' out.mem ≤
        rate m * (1 + (algorithm2_detect cfg model).1.card) +
          (solverStateRepSel cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k
            epsExp (detectOffTreeDrainUnit F.limbs) B toolMul treeMul dMul kOff Rcore K pot).phi
            root tok mem
      omega
    | i + 3 =>
      exact False.elim hpre.2

end MinCostFlow.MinRatio
