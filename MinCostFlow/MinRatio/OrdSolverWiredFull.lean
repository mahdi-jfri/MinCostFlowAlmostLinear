module

public import MinCostFlow.MinRatio.OrdSolverImplementsFull
public import MinCostFlow.MinRatio.OrdChainWireAdapters
public import MinCostFlow.MinRatio.WireFindCycle
public import MinCostFlow.MinRatio.ShiftQuotaWriter
public import MinCostFlow.MinRatio.OrdSolverWordBound
import MinCostFlow.MinRatio.GoodCycleBridgeWired
import MinCostFlow.IPM.ConnectedInitialConstruction
import Mathlib.Tactic

/-!
# End-to-end wired solver assembly (`ordSolver_implements_full_wired`)

Connects the six inner specifications (`OrdInitConcreteSpecW`,
`OrdChainUpdateCoreSpecW`, `OrdCycleRouteSelectSpecW`, `OrdCycleRouteEvalSpecW`,
`ShiftTermChainSyncSpecW`, `ShiftDeepChainSyncSpecW`) directly into `ordSolver_implements_full_credit`
via:
- `solverInitStepSpecCredit_of_concreteW`: discharges `SolverInitStepSpecCredit` from
  `OrdInitConcreteSpecW`, `ordSolverInitWired_runs`, and `solverInitStepSpecCredit_of_wired`
  (automatically discharging `TreeChain.Holds` at `T = 0` from `cfg.ValidOrdNoHidden`,
  `WireCapFacts` from `hCapLevels`, and `SolverTreeNumericInv` from `B_tree`);
- `chainRefreshStepSpecW_wired` + `shiftQuotaWriterSpec_proved`;
- `findCycleStepSpecW_wired`;
- `shiftLevelStepSpecW_wired`.

The other inner specifications (the Select half, the re-embedded list, and the concrete
sparse-core, update and shift bodies) enter here as hypotheses, stated as the exact `W`-specs
that are proved elsewhere.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore.Program Scaling Scaling.Machine Final

/-- Helper: `algorithm2_init` satisfies `TreeChain.Holds` under `cfg.ValidOrdNoHidden`,
`G.m ≤ M₀`, `G.n ≤ N₀`, positive lengths, and `|log ℓ e| ≤ cfg.Ψ`. -/
private theorem alg2Init_holds_exists {cfg : Alg2Config} {G : MGraph} {g l : ℕ → ℝ}
    (hV : cfg.ValidOrdNoHidden) (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀)
    (hGV : G.IsValid) (hlPos : ∀ e ∈ G.E, 0 < l e) (hlR : ∀ e ∈ G.E, |Real.log (l e)| ≤ cfg.Ψ) :
    ∃ σ σ_mwu' γ_ℓ γ_c,
      (Chain.Ordered.algorithm2_init cfg G g l).chain.toTreeChain.Holds G l σ σ_mwu' γ_ℓ γ_c := by
  have hℓ : Chain.Ordered.LenInRange (max 0 cfg.Ψ) G l := by
    intro e he
    have hlog := (hlR e he).trans (le_max_right 0 cfg.Ψ)
    rw [abs_le] at hlog
    exact ⟨by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.1,
      by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.2⟩
  have hInit := Chain.Ordered.initialize_preserves_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk G l g hGV hmG hnG hℓ
  rcases hInit with ⟨hInv, _, hG0, hℓ0, _, _, _, _, _, _⟩
  have hHolds := (hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  rw [hG0, hℓ0] at hHolds
  exact ⟨_, _, _, _, hHolds⟩

/-- Discharges `SolverInitStepSpecCreditKFBL` directly from `OrdInitConcreteSpecW` via
`ordSolverInitWired_runs` and `solverInitStepSpecCreditKFBL_of_wired`. -/
theorem solverInitStepSpecCredit_of_concreteW
    {w m V psi k epsExp clog threshold initProc initConcreteProc overwriteProc copyWords
      capExp limbMul capLimit wordExp initSpace' initFixed toolMul treeMul : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {B_tree : ℤ}
    (hInitAt : p.procs[initProc]? = some (solverInitWiredBody initConcreteProc overwriteProc copyWords))
    (hInitSpec : OrdInitConcreteSpecW w F.limbs F.fmt.precision F.rangeExponent m V psi k epsExp
      cfg Rcore G p initConcreteProc B_tree capExp limbMul capLimit wordExp initSpace' initFixed
      toolMul)
    (hOverAt : p.procs[overwriteProc]? = some (initOverwriteIntThresholdsBody clog threshold))
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hclog : ∀ n, MeetsContract w p clog (Scaling.Machine.clogTwoContract w n))
    (hlocal : Rcore.Local)
    (hV : cfg.ValidOrdNoHidden) (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀)
    (hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ)
    (hw14 : 14 ≤ w) (hFmt4 : F.fmt.limbBits = 4) (hmPos : 0 < m)
    (hM₀Eq : cfg.P.M₀ = max m threshold) (hN₀Eq : cfg.N₀ = 4 * cfg.P.M₀)
    (h4M3W : 4 * cfg.P.M₀ + 3 < 2 ^ w) (hd1W : cfg.P.d + 1 < 2 ^ w)
    (hεPos : 0 < cfg.ε) (hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent)
    (hGE : G.E = Finset.range m)
    (hEndsLt : ∀ e ∈ G.E, G.tail e < G.n ∧ G.head e < G.n)
    (hWordLvl : ∀ i < cfg.P.d,
      (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ wordExp * (F.limbs + 1) < 2 ^ w)
    (hCapLevels : ∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ capLimit →
      SparseCoreCapHyp capExp limbMul F.limbs (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap)
    (hThrB : (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_tree)
    (hCapTree : 2 * ((2 * G.n + 1 : ℕ) : ℤ) * B_tree < (Num.capacity 4 F.limbs : ℤ)) :
    SolverInitStepSpecCreditKFBL F cfg G m V psi k epsExp Rcore p initProc
      (initSpace' + initWiredExtraSpace cfg G)
      (initFixed + initWiredExtraCost cfg G)
      toolMul treeMul := by
  refine solverInitStepSpecCreditKFBL_of_wired F cfg G m V psi k epsExp Rcore p initProc
    initConcreteProc overwriteProc copyWords (initSpace' + initWiredExtraSpace cfg G) _ toolMul treeMul hInitAt hFmt4 ?_
  intro args mem pos ω hargsW hpre hz hroom
  obtain ⟨graph, g, l, heap, hargsEq, _, _, _, hGraphAt, _, hGV, _, hGraphEnd, hGradEnd, hLenEnd,
    hVecV, hlPos, hLenWithin, hGradWithin⟩ := hpre
  subst hargsEq
  rw [hFmt4] at hVecV hlPos hLenWithin hGradWithin
  have hheapArg : heapArg [graph, g, l, F.limbs, F.fmt.precision, V, heap] = heap := rfl
  rw [hheapArg] at hz hroom
  have hGm : G.m = m := by unfold MGraph.m; rw [hGE, Finset.card_range]
  have hVecValid : ∀ e < m, Num.Valid mem (l + e * F.limbs) 4 F.limbs ∧
      0 < Num.intVal mem (l + e * F.limbs) 4 F.limbs ∧ Num.Valid mem (g + e * F.limbs) 4 F.limbs := by
    intro e he
    have heG : e ∈ G.E := hGE ▸ Finset.mem_range.mpr he
    have hgv := (hVecV e he).1
    have hlv := (hVecV e he).2
    have hposR : (0 : ℝ) < (Num.intVal mem (l + e * F.limbs) 4 F.limbs : ℝ) / (2 : ℝ) ^ F.fmt.precision := by
      simpa [readVector, he, Num.fixVal] using hlPos e heG
    have hposI : (0 : ℤ) < Num.intVal mem (l + e * F.limbs) 4 F.limbs := by
      have h2p : (0 : ℝ) < (2 : ℝ) ^ F.fmt.precision := by positivity
      have hreal : (0 : ℝ) < (Num.intVal mem (l + e * F.limbs) 4 F.limbs : ℝ) :=
        (div_pos_iff_of_pos_right h2p).mp hposR
      exact_mod_cast hreal
    exact ⟨hlv, hposI, hgv⟩
  have hHoldsEx := alg2Init_holds_exists (g := readVector mem g 4 F.limbs F.fmt.precision m)
    (l := readVector mem l 4 F.limbs F.fmt.precision m) hV hmG hnG hGV hlPos
    (fun e he => (abs_log_le_of_two_pow_bounds (hLenWithin e he).1 (hLenWithin e he).2).trans hEΨ)
  have hvalBAll : ∀ e < m,
      let v := initialPathEdgeValue F.fmt.precision cfg.ε
        (Num.intVal mem (g + e * F.limbs) 4 F.limbs)
        ((Num.intVal mem (l + e * F.limbs) 4 F.limbs).toNat)
      |v.gradient| ≤ B_tree ∧ |v.length| ≤ B_tree ∧ |v.flow| ≤ B_tree ∧ |v.detector| ≤ B_tree := by
    intro e he
    have heG : e ∈ G.E := hGE ▸ Finset.mem_range.mpr he
    have h2pPos : (0 : ℝ) < (2 : ℝ) ^ F.fmt.precision := by positivity
    have hpowLe : (2 : ℤ) ^ (F.fmt.precision + F.rangeExponent) ≤
        (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hBnn : 0 ≤ B_tree :=
      le_trans (pow_nonneg (by norm_num) _) hThrB
    have hlIntPos : 0 < Num.intVal mem (l + e * F.limbs) 4 F.limbs := (hVecValid e he).2.1
    have htoNat : (((Num.intVal mem (l + e * F.limbs) 4 F.limbs).toNat : ℕ) : ℤ) =
        Num.intVal mem (l + e * F.limbs) 4 F.limbs := Int.toNat_of_nonneg hlIntPos.le
    have hgradR : |(Num.intVal mem (g + e * F.limbs) 4 F.limbs : ℝ)| / (2 : ℝ) ^ F.fmt.precision ≤
        (2 : ℝ) ^ F.rangeExponent := by
      have hg := hGradWithin e heG
      simp only [readVector, he, ↓reduceIte, Num.fixVal, abs_div, abs_of_pos h2pPos] at hg
      exact hg
    have hgradI : |Num.intVal mem (g + e * F.limbs) 4 F.limbs| ≤
        (2 : ℤ) ^ (F.fmt.precision + F.rangeExponent) := by
      have h1 : |(Num.intVal mem (g + e * F.limbs) 4 F.limbs : ℝ)| ≤
          (2 : ℝ) ^ F.rangeExponent * (2 : ℝ) ^ F.fmt.precision :=
        (div_le_iff₀ h2pPos).mp hgradR
      have h2 : (2 : ℝ) ^ F.rangeExponent * (2 : ℝ) ^ F.fmt.precision =
          ((2 : ℤ) ^ (F.fmt.precision + F.rangeExponent) : ℝ) := by
        push_cast; rw [pow_add, mul_comm]
      rw [h2] at h1
      exact_mod_cast h1
    have hlenR : (Num.intVal mem (l + e * F.limbs) 4 F.limbs : ℝ) / (2 : ℝ) ^ F.fmt.precision ≤
        (2 : ℝ) ^ F.rangeExponent := by
      have hl := (hLenWithin e heG).2
      simp only [readVector, he, ↓reduceIte, Num.fixVal] at hl
      exact hl
    have hlenI : Num.intVal mem (l + e * F.limbs) 4 F.limbs ≤
        (2 : ℤ) ^ (F.fmt.precision + F.rangeExponent) := by
      have h1 : (Num.intVal mem (l + e * F.limbs) 4 F.limbs : ℝ) ≤
          (2 : ℝ) ^ F.rangeExponent * (2 : ℝ) ^ F.fmt.precision :=
        (div_le_iff₀ h2pPos).mp hlenR
      have h2 : (2 : ℝ) ^ F.rangeExponent * (2 : ℝ) ^ F.fmt.precision =
          ((2 : ℤ) ^ (F.fmt.precision + F.rangeExponent) : ℝ) := by
        push_cast; rw [pow_add, mul_comm]
      rw [h2] at h1
      exact_mod_cast h1
    have hdetRange := detectorThreshold_mem_range (P := F.fmt.precision) hεPos hεLe
      (hLenWithin e heG).1
    have hlenEq : ((Num.intVal mem (l + e * F.limbs) 4 F.limbs).toNat : ℝ) /
        (2 : ℝ) ^ F.fmt.precision = readVector mem l 4 F.limbs F.fmt.precision m e := by
      have hcast : (((Num.intVal mem (l + e * F.limbs) 4 F.limbs).toNat : ℕ) : ℝ) =
          (Num.intVal mem (l + e * F.limbs) 4 F.limbs : ℝ) := by exact_mod_cast htoNat
      simp [readVector, he, Num.fixVal, hcast]
    dsimp only [initialPathEdgeValue]
    refine ⟨hgradI.trans (hpowLe.trans hThrB), ?_, by simpa using hBnn, ?_⟩
    · rw [htoNat, abs_of_pos hlIntPos]
      exact hlenI.trans (hpowLe.trans hThrB)
    · rw [hlenEq, abs_neg, abs_of_nonneg hdetRange.1]
      exact hdetRange.2.trans hThrB
  have hCapInit : WireCapFacts capExp limbMul F.limbs capLimit
      (Chain.Ordered.algorithm2_init cfg G
        (readVector mem g 4 F.limbs F.fmt.precision m)
        (readVector mem l 4 F.limbs F.fmt.precision m)) :=
    fun i hi vCap eCap hlim => hCapLevels i hi vCap eCap hlim
  obtain ⟨finalHeap, cost, out, tok, hr, _, hrep, hCapsInv, _hLay, _hrecap, hcap, _hsh, _hsb, hnum, _, _, hlo, hhi, hzOut, hframe, hfoot, hcost⟩ :=
    ordSolverInitWired_runs (w := w) (L := F.limbs) (P := F.fmt.precision) (E := F.rangeExponent)
      (m := m) (V := V)
      (psi := psi) (k := k) (epsExp := epsExp) (clog := clog) (threshold := threshold)
      (initConcreteProc := initConcreteProc) (overwriteProc := overwriteProc) (copyWords := copyWords)
      (capExp := capExp) (limbMul := limbMul) (capLimit := capLimit) (wordExp := wordExp)
      (initSpace' := initSpace')
      (initFixed := initFixed) (initMul := toolMul) (graph := graph) (gradient := g)
      (lengths := l) (root := heap) (pos := pos) (B_tree := B_tree)
      hInitSpec hOverAt hCopy hclog hlocal hw14 hmPos hM₀Eq hN₀Eq h4M3W hd1W hεPos hGE hEndsLt hroom
      hWordLvl hCapInit hGraphAt hGraphEnd (hGm ▸ hLenEnd) (hGm ▸ hGradEnd) hVecValid
      hLenWithin hGradWithin hz hHoldsEx hvalBAll
  have hNumInv : SolverTreeNumericInv F.fmt.precision
      (Chain.Ordered.algorithm2_init cfg G
        (readVector mem g 4 F.limbs F.fmt.precision m)
        (readVector mem l 4 F.limbs F.fmt.precision m)) tok := by
    refine solverTreeNumericInv_of_update (E := F.rangeExponent) (n := G.n) (B_bound := B_tree)
      (R_bound := 0) (X := 0) hεPos hεLe (solverStateRep_tree_n hrep) hnum (by omega) (by omega)
      (by simpa using hCapTree) le_rfl hThrB fun e he => (hLenWithin e he).1
  refine ⟨finalHeap, cost, out, tok, hr, hrep, hCapsInv, hcap, hNumInv, hlo, hhi, hzOut, hframe, hfoot, ?_⟩
  change cost + (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).phi heap tok out.mem ≤
    (initFixed + initWiredExtraCost cfg G) +
      toolMul * (Chain.Ordered.algorithm2_init cfg G
        (readVector mem g 4 F.limbs F.fmt.precision m)
        (readVector mem l 4 F.limbs F.fmt.precision m)).chain.totalRuntime +
      treeMul * (Chain.Ordered.algorithm2_init cfg G
        (readVector mem g 4 F.limbs F.fmt.precision m)
        (readVector mem l 4 F.limbs F.fmt.precision m)).chain.totalTreeUpdates
  omega

/-- **End-to-end wired `DSRep.Implements` theorem from the six inner `W`/`KFBL`-specs.**
Takes `OrdInitConcreteSpecW`, `OrdChainUpdateCoreSpecWKFBL`, `OrdCycleRouteSelectSpecW`,
`OrdCycleRouteEvalSpecW`, `ShiftTermChainSyncSpecWExt`, and `ShiftDeepChainSyncSpecWExtKFBL`, wires
them through `solverInitStepSpecCredit_of_concreteW`, `chainRefreshStepSpecWKFBL_wired`,
`shiftQuotaWriterSpec_proved`, `findCycleStepSpecW_wired`, and
`shiftLevelStepSpecWKFBL_wired_of_termExt`, and discharges `solverStateRepFullKFBL.Implements`
against `minRatioMachineContractWithV`. -/
theorem ordSolver_implements_full_wired
    {w base initProc initConcreteProc overwriteProc clog threshold
      chainRefreshProc ordEditsProc ordChainCoreProc shiftQuotaWriterProc
      findCycleProc selectRouteProc evalCycleProc
      shiftLevelProc shiftTermChainProc shiftDeepChainProc
      m U_cap V psi k epsExp capExp limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap
      initSpace' initFixed selectSpace selectBudget evalSpace evalBudget
      termSpace termFixed deepSpace deepFixed maxEdges maxPaths toolMul treeMul : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {DeepInv : ChainState cfg.T cfg.P → Prop}
    {p : Program} {B_tree B_bound R_bound : ℤ}
    {coreSpace coreFixed : ℕ → ℕ} {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ}
    (hMono : toolMul = 0 ∨ ToolCostMono cfg.T)
    (hV : cfg.ValidOrdNoHidden) (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ)
    (hw : 14 ≤ w) (hfmt4 : F.fmt.limbBits = 4) (hLpos : 0 < F.limbs)
    (hPL : F.fmt.precision ≤ 4 * F.limbs)
    (hmPos : 0 < m) (hM₀Eq : cfg.P.M₀ = max m threshold) (hN₀Eq : cfg.N₀ = 4 * cfg.P.M₀)
    (hpsiEq : psi = ⌈cfg.Ψ⌉₊)
    (h4M3W : 4 * cfg.P.M₀ + 3 < 2 ^ w) (hkW : cfg.P.k < 2 ^ w)
    (hεPos : 0 < cfg.ε) (hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent)
    (hGE : G.E = Finset.range m)
    (hEndsLt : ∀ e ∈ G.E, G.tail e < G.n ∧ G.head e < G.n)
    (hthrB : (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_bound)
    (hthrTree : (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_tree)
    (hCapTreeInit : 2 * ((2 * G.n + 1 : ℕ) : ℤ) * B_tree < (Num.capacity 4 F.limbs : ℤ))
    (hα : cfg.α = Num.IPM.alphaPrime m U_cap / 8)
    (hepsExp : epsExp = k + Num.IPM.alphaExponent m U_cap + 10)
    (h5L1W : 5 * F.limbs + 1 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) (hepsW : epsExp < 2 ^ w)
    (hQuotaBoundW : (2 * G.m + 2) *
      shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) < 2 ^ w)
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
    (hWordLvl : ∀ i < cfg.P.d,
      (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ wordExp * (F.limbs + 1) < 2 ^ w)
    (hCapLevels : ∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ capLimit →
      SparseCoreCapHyp capExp limbMul F.limbs (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap)
    (hIntCapMax : initTargetCap cfg G ≤ intCapMax)
    (hFEdgeCap : 2 * G.n ≤ forestEdgeCap)
    (hDeepInv : DeepShiftChainInvHyps w F cfg G k wordExp stretchPrec DeepInv)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc))
    (hInitAt : p.procs[initProc]? = some (solverInitWiredBody initConcreteProc overwriteProc base))
    (hOverAt : p.procs[overwriteProc]? = some (initOverwriteIntThresholdsBody clog threshold))
    (hclog : ∀ n, MeetsContract w p clog (Scaling.Machine.clogTwoContract w n))
    (hRefAt : p.procs[chainRefreshProc]? =
      some (ordChainRefreshWiredBody ordEditsProc ordChainCoreProc shiftQuotaWriterProc))
    (hEditsAt : p.procs[ordEditsProc]? = some level0BatchToOrdEditsBody)
    (hQuotaAt : p.procs[shiftQuotaWriterProc]? = some (shiftQuotaWriterBody threshold))
    (hFindAt : p.procs[findCycleProc]? =
      some (ordFindCycleWiredBody selectRouteProc evalCycleProc))
    (hShiftAt : p.procs[shiftLevelProc]? =
      some (shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc))
    (hInitConcrete : OrdInitConcreteSpecW w F.limbs F.fmt.precision F.rangeExponent m V psi k epsExp
      cfg Rcore G p initConcreteProc B_tree capExp limbMul capLimit wordExp initSpace' initFixed
      toolMul)
    (hCore : OrdChainUpdateCoreSpecWKFBL w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit G.n (initTargetCap cfg G) cfg Rcore
      p ordChainCoreProc coreSpace coreFixed toolMul treeMul B_bound R_bound)
    (hSel : OrdCycleRouteSelectSpecW w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p selectRouteProc
      selectSpace selectBudget maxEdges maxPaths)
    (hEval : OrdCycleRouteEvalSpecW w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) cfg Rcore p evalCycleProc evalSpace evalBudget
      maxEdges maxPaths)
    (hTerm : ShiftTermChainSyncSpecWExt w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit (2 * levelM cfg.TP cfg.P cfg.P.d)
      cfg Rcore p shiftTermChainProc termSpace termFixed toolMul treeMul)
    (hDeep : ShiftDeepChainSyncSpecWExtKFBL w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap G.n (initTargetCap cfg G) cfg Rcore p shiftDeepChainProc
      deepSpace deepFixed toolMul treeMul)
    (hBridge : GoodCycleNumericBridge F cfg G m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore maxEdges maxPaths B_bound R_bound)
    (hEnv : OrdSolverContractEnvelopeFullCredit F cfg G m V psi k epsExp
      (initSpace' + initWiredExtraSpace cfg G)
      (initFixed + initWiredExtraCost cfg G)
      (6 + selectSpace + evalSpace) (selectBudget + evalBudget + 90)
      (max termSpace deepSpace)
      (max termFixed deepFixed + 28 * (cfg.P.d + 1) + 220)
      maxEdges maxPaths toolMul treeMul
      (fun uLen => cfg.P.d + (8 * uLen + 1) + coreSpace uLen)
      (fun uLen => coreFixed uLen + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 120 * uLen +
        62 * (cfg.P.d + 1) + 240)
      Rcore rate alloc) :
    (solverStateRepFullKFBL cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs)
      (cycleLoopIterBudget F.limbs cfg.P.d (selectBudget + evalBudget + 90)
        (max termFixed deepFixed + 28 * (cfg.P.d + 1) + 220))
      toolMul treeMul Rcore DeepInv).Implements w p initProc (solverOpsDispatch base)
      (minRatioMachineContractWithV F
        (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
        G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc) := by
  have hw17 : 17 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 17 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw)
  have hInit := solverInitStepSpecCredit_of_concreteW (treeMul := treeMul) hInitAt hInitConcrete
    hOverAt (solverOpsProcs_meetsAll hw hp).1 hclog hlocalCore hV hmG hnG hEΨ hw hfmt4 hmPos
    hM₀Eq hN₀Eq h4M3W hdW hεPos hεLe hGE hEndsLt hWordLvl hCapLevels hthrTree hCapTreeInit
  have hQuota := shiftQuotaWriterSpec_proved (w := w) (L := F.limbs) (P := F.fmt.precision)
    (m := m) (V := V) (psi := psi) (k := k) (epsExp := epsExp)
    (drainUnit := detectOffTreeDrainUnit F.limbs) (cfg := cfg) (Rcore := Rcore)
    hQuotaAt hM₀Eq hpsiEq
  have hRefresh := chainRefreshStepSpecWKFBL_wired hlocalCore hRefAt hEditsAt hCore hQuota
    (by omega) hdW
  have hFind := findCycleStepSpecW_wired hlocalCore hFindAt hSel hEval (by omega)
  have hShift := shiftLevelStepSpecWKFBL_wired_of_termExt hShiftAt hV hTerm hDeep hw17 hdW hkW
  exact ordSolver_implements_full_credit (U_cap := U_cap) hlocalCore hMono hV hmG hnG hConn hEΨ hw hfmt4
    hLpos hPL hmPos hεPos hεLe hthrB hα hepsExp (fun e he => hGE ▸ Finset.mem_range.mpr he)
    h5L1W hdW hepsW hQuotaBoundW h2nW hlogW hsizeM hmaxEP hcapEvalB hcapTreeB hcapOffB hCapLevels
    hIntCapMax hFEdgeCap hDeepInv hp hInit hRefresh hFind hShift hBridge hEnv

/-- For every chain witness `W`, there is a constant `C_w` depending only on `W` such that
whenever `C_w ≤ allocationCoefficient`, both the static quota bound
`(2 * (namedInstance I).m + 2) * shiftQuotaBase ^ (d + 1)` and `4 * cfg.P.M₀ + 3` fit strictly
below `2 ^ w` at the final solver word size. -/
theorem concrete_solver_word_bounds_poly
    {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (SparseCore.lastLevelParams lastConstant)}
    (W : Final.ConcreteChainWitnessWithLast lastTool lastConstant lastSpec) :
    ∃ C_w : ℕ, ∀ (allocationCoefficient allocationDegree : ℕ),
      C_w ≤ allocationCoefficient →
      ∀ (source J : Scaling.Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let threshold := Final.concreteEdgeThresholdWithLast W
        let A := Final.concreteQualityBudgetWithLast W
        let Ck := Final.concreteQualityLinearCoeff threshold A
        let deg := Final.forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent threshold A I.m
        let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
        let cfg := Final.concreteCirculationCfgWithLast W J
        ipmQualityParameterWordBits I.m V k ≤ w →
        (2 * (namedInstance I).m + 2) *
            shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) < 2 ^ w ∧
        4 * cfg.P.M₀ + 3 < 2 ^ w := by
  obtain ⟨C_q, hCq⟩ := concrete_quotaBound_lt_two_pow_wordSize W
  let threshold := Final.concreteEdgeThresholdWithLast W
  refine ⟨max C_q (4 * threshold + 28), fun allocCoeff allocDeg hle source J hJn hJm hCap hw => ?_⟩
  have hq := (hCq allocCoeff allocDeg ((le_max_left _ _).trans hle) source J hJn hJm hCap hw).1
  set A := Final.concreteQualityBudgetWithLast W
  set Ck := Final.concreteQualityLinearCoeff threshold A
  set I := solverConnectedAugmented J
  set cfg := Final.concreteCirculationCfgWithLast W J
  have hImLe : I.m ≤ 7 * J.m := (solverConnectedAugmented_size J hJn hJm hCap).2
  have hM0Le : cfg.P.M₀ ≤ 7 * J.m + threshold := by
    change max I.m threshold ≤ 7 * J.m + threshold
    exact max_le (by omega) (by omega)
  have h4M3Poly : 4 * cfg.P.M₀ + 3 ≤ (4 * threshold + 28) * (J.m + 2) ^ 7 := by
    have hlin : 4 * cfg.P.M₀ + 3 ≤ (4 * threshold + 28) * (J.m + 2) := by
      have h1 : 4 * (7 * J.m + threshold) + 3 ≤ 4 * threshold * (J.m + 2) + 28 * (J.m + 2) := by
        nlinarith
      rw [Nat.add_mul]
      omega
    have hpow : J.m + 2 ≤ (J.m + 2) ^ 7 :=
      Nat.le_self_pow (by decide : 7 ≠ 0) (J.m + 2)
    exact hlin.trans (Nat.mul_le_mul_left _ hpow)
  have hdeg7 := forestProgramsScratchDegree_covers_shiftQuota allocCoeff allocDeg Ck
    (4 * threshold + 28) ((le_max_right _ _).trans hle)
  have h4M3W := lt_two_pow_wordSize_of_poly_and_hw source J hJm (by decide) hw h4M3Poly hdeg7
  exact ⟨hq, h4M3W⟩

/-- **Concrete `supported` field from `ordSolver_implements_full_wired` and the six inner `W`
specs.** Automatically discharges `cfg.ValidOrdNoHidden`, `ToolCostMono cfg.T`,
`GoodCycleNumericBridge` (`goodCycleNumericBridge_wired`), and all unconditional concrete
word-size/format inequalities (`14 ≤ w`, `5 * F.limbs + 1 < 2 ^ w`, `cfg.P.d + 1 < 2 ^ w`,
`cfg.P.k < 2 ^ w`, `epsExp < 2 ^ w`, `2 * I.n + 1 < 2 ^ w`, `Nat.log 2 (2 * I.n + 1) ≤ 4 * F.limbs`,
`Nat.size I.m ≤ F.rangeExponent + 8`, `G.E = Finset.range I.m`, `G.IsValid`). -/
theorem ordSolver_supported_full_wired
    (lastTool : LastLevelTool) (lastConstant : ℝ)
    (lastSpec : lastTool.IsSpec (SparseCore.lastLevelParams lastConstant))
    (W : Final.ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (cycleInit initConcreteProc overwriteProc clog base
      chainRefreshProc ordEditsProc ordChainCoreProc shiftQuotaWriterProc
      findCycleProc selectRouteProc evalCycleProc
      shiftLevelProc shiftTermChainProc shiftDeepChainProc : ℕ)
    (cycle : List Stmt) (cycleRate : ℕ → ℕ)
    (cycleAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ) (cycleSpace : ℕ → ℕ → ℕ)
    (allocationCoefficient allocationDegree : ℕ)
    (source J : Scaling.Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (_hCost : J.CostsBounded (J.m ^ 10))
    (hCap : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (Final.concreteEdgeThresholdWithLast W)
        (Final.concreteQualityBudgetWithLast W)
        (solverConnectedAugmented J).m) ≤
      wordSize (scratchWordMultiplier 1
        (Final.forestProgramsScratchDegree allocationCoefficient allocationDegree
          (Final.concreteQualityLinearCoeff
            (Final.concreteEdgeThresholdWithLast W)
            (Final.concreteQualityBudgetWithLast W))))
        source.solverWords) :
    let threshold := Final.concreteEdgeThresholdWithLast W
    let A := Final.concreteQualityBudgetWithLast W
    let Ck := Final.concreteQualityLinearCoeff threshold A
    let deg := Final.forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent threshold A I.m
    let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
    let dispatch := Final.mrdsSolverDispatch cycleInit (solverOpsDispatch base) cycle.length
    let forest := Final.dynLctForestBodies 4 (Final.mrdsCycleBase + cycle.length)
    let p := Final.linkedCappedSolverProgramWithV threshold A dispatch cycle forest
    let cfg := Final.concreteCirculationCfgWithLast W J
    let F := ipmQualityMinRatioFormat I.m V k hw
    let psi := ⌈cfg.Ψ⌉₊
    let epsExp := k + Num.IPM.alphaExponent I.m V + 10
    ∀ (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
      (capExp limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap
        initSpace' initFixed selectSpace selectBudget evalSpace
        evalBudget termSpace termFixed deepSpace deepFixed maxEdges maxPaths toolMul treeMul : ℕ)
      (DeepInv : ChainState cfg.T cfg.P → Prop)
      (coreSpace coreFixed : ℕ → ℕ) (B_tree B_bound R_bound : ℤ),
      Rcore.Local →
      4 * cfg.P.M₀ + 3 < 2 ^ w →
      (2 * (namedInstance I).m + 2) *
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) < 2 ^ w →
      (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_bound →
      (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_tree →
      2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) * B_tree < (Num.capacity 4 F.limbs : ℤ) →
      maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20) →
      2 * (((maxEdges + maxPaths * (namedInstance I).n : ℕ) : ℤ) * B_bound) <
        (Num.capacity 4 F.limbs : ℤ) →
      2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) *
        ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
          (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
        (Num.capacity 4 F.limbs : ℤ) →
      B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
        (Num.capacity 4 F.limbs : ℤ) →
      (∀ i < cfg.P.d,
        (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ wordExp * (F.limbs + 1) < 2 ^ w) →
      (∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ capLimit →
        SparseCoreCapHyp capExp limbMul F.limbs (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap) →
      initTargetCap cfg (namedInstance I) ≤ intCapMax →
      2 * (namedInstance I).n ≤ forestEdgeCap →
      DeepShiftChainInvHyps w F cfg (namedInstance I) k wordExp stretchPrec DeepInv →
      p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc) →
      p.procs[cycleInit]? = some (solverInitWiredBody initConcreteProc overwriteProc base) →
      p.procs[overwriteProc]? = some (initOverwriteIntThresholdsBody clog threshold) →
      (∀ n, MeetsContract w p clog (Scaling.Machine.clogTwoContract w n)) →
      p.procs[chainRefreshProc]? =
        some (ordChainRefreshWiredBody ordEditsProc ordChainCoreProc shiftQuotaWriterProc) →
      p.procs[ordEditsProc]? = some level0BatchToOrdEditsBody →
      p.procs[shiftQuotaWriterProc]? = some (shiftQuotaWriterBody threshold) →
      p.procs[findCycleProc]? = some (ordFindCycleWiredBody selectRouteProc evalCycleProc) →
      p.procs[shiftLevelProc]? = some (shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc) →
      OrdInitConcreteSpecW w F.limbs F.fmt.precision F.rangeExponent I.m V psi k epsExp cfg Rcore
        (namedInstance I) p initConcreteProc B_tree capExp limbMul capLimit wordExp initSpace'
        initFixed toolMul →
      OrdChainUpdateCoreSpecWKFBL w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit
        (namedInstance I).n (initTargetCap cfg (namedInstance I)) cfg Rcore p ordChainCoreProc
        coreSpace coreFixed toolMul treeMul B_bound R_bound →
      OrdCycleRouteSelectSpecW w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p selectRouteProc
        selectSpace selectBudget maxEdges maxPaths →
      OrdCycleRouteEvalSpecW w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) cfg Rcore p evalCycleProc evalSpace evalBudget
        maxEdges maxPaths →
      ShiftTermChainSyncSpecWExt w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit (2 * levelM cfg.TP cfg.P cfg.P.d)
        cfg Rcore p shiftTermChainProc termSpace termFixed toolMul treeMul →
      ShiftDeepChainSyncSpecWExtKFBL w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit wordExp stretchPrec intCapMax
        forestEdgeCap (namedInstance I).n (initTargetCap cfg (namedInstance I)) cfg Rcore p
        shiftDeepChainProc deepSpace deepFixed toolMul treeMul →
      OrdSolverContractEnvelopeFullCredit F cfg (namedInstance I) I.m V psi k epsExp
        (initSpace' + initWiredExtraSpace cfg (namedInstance I))
        (initFixed + initWiredExtraCost cfg (namedInstance I))
        (6 + selectSpace + evalSpace) (selectBudget + evalBudget + 90)
        (max termSpace deepSpace) (max termFixed deepFixed + 28 * (cfg.P.d + 1) + 220)
        maxEdges maxPaths toolMul treeMul
        (fun uLen => cfg.P.d + (8 * uLen + 1) + coreSpace uLen)
        (fun uLen => coreFixed uLen + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 120 * uLen +
          62 * (cfg.P.d + 1) + 240)
        Rcore cycleRate (cycleAllocation I.n I.m) →
      (∀ j < 4, ∀ args, cycleAllocation I.n I.m j args ≤ cycleSpace I.n I.m) →
      ∃ RC : DSRep (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).State,
        RC.Implements w p cycleInit (solverOpsDispatch base)
          (minRatioMachineContractWithV F
            (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) (namedInstance I) I.m V
            (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
            cycleRate (cycleAllocation I.n I.m)) ∧
        (∀ j < 4, ∀ args, cycleAllocation I.n I.m j args ≤ cycleSpace I.n I.m) := by
  intro threshold A Ck deg I V k w dispatch forest p cfg F psi epsExp
    Rcore capExp limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap
    initSpace' initFixed selectSpace selectBudget evalSpace
    evalBudget termSpace termFixed deepSpace deepFixed maxEdges maxPaths toolMul treeMul DeepInv
    coreSpace coreFixed B_tree B_bound R_bound hlocalCore h4M3W hQuotaBoundW hthrB hthrTree
    hCapTreeInit hmaxEP hcapEvalB hcapTreeB hcapOffB hWordLvl hCapLevels hIntCapMax hFEdgeCap
    hDeepInv hp hInitAt hOverAt hclog hRefAt hEditsAt hQuotaAt hFindAt hShiftAt hInitConcrete hCore
    hSel hEval hTerm hDeep hEnv hAllocLe
  have hVcfg : cfg.ValidOrdNoHidden :=
    Final.concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm (fun e => (hCap e).1)
  have hMonoCfg : ToolCostMono cfg.T :=
    sparseCoreBundleRestartToolMachWith_costMono (W.lsfInit F.limbs F.fmt.precision) W.C_lsst
      (Expander.chosenL (max I.m threshold ^ 2)) (fun _ => W.sparsify) W.params W.spanConst
  have hfit := ipm_quality_parameter_words_fit I.m V k hw
  have hw14 : 14 ≤ w := hfit.1
  have hImGeJm : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm (fun e => (hCap e).1)).1
  have hImPos : 0 < I.m := lt_of_lt_of_le hJm hImGeJm
  have hLpos : 0 < F.limbs := by
    dsimp only [F, ipmQualityMinRatioFormat, ipmQualityLimbs]; omega
  have hPL : F.fmt.precision ≤ 4 * F.limbs := by
    dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega
  have hεPos : 0 < cfg.ε := by
    dsimp only [cfg, Final.concreteCirculationCfgWithLast, Final.concreteCirculationCfgOfDims,
      Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
    positivity
  have hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent := by
    dsimp only [cfg, Final.concreteCirculationCfgWithLast, Final.concreteCirculationCfgOfDims,
      Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
    have hk : (1 : ℝ) / 2 ^ k ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    have ha : (1 : ℝ) / 2 ^ Num.IPM.alphaExponent I.m V ≤ 1 :=
      div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    have hprod : (1 : ℝ) / 2 ^ k * (1 / 2 ^ Num.IPM.alphaExponent I.m V) ≤ 1 := by
      calc (1 : ℝ) / 2 ^ k * (1 / 2 ^ Num.IPM.alphaExponent I.m V)
          ≤ 1 * 1 := mul_le_mul hk ha (by positivity) (by norm_num)
        _ = 1 := one_mul 1
    have hE : (1 : ℝ) ≤ 2 ^ F.rangeExponent := one_le_pow₀ (by norm_num)
    have hpos : (0 : ℝ) ≤ 1 / 2 ^ k * (1 / 2 ^ Num.IPM.alphaExponent I.m V) := by positivity
    linarith
  obtain ⟨_, _, _, _, hIn⟩ := Final.concreteCirculation_bounds_of (le_max_left W.M_thresh _)
    (le_max_right W.M_thresh _) (Final.concreteEdgeThresholdWithLast_ge_two W) J hJn hJm
    (fun e => (hCap e).1)
  have hmG : (namedInstance I).m ≤ cfg.P.M₀ := by
    rw [namedInstance_m]; exact le_max_left _ _
  have hInEq : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
  have hnG : (namedInstance I).n ≤ cfg.N₀ := by rw [hInEq]; exact hIn
  have hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hEndsLt : ∀ e ∈ (namedInstance I).E,
      (namedInstance I).tail e < (namedInstance I).n ∧
        (namedInstance I).head e < (namedInstance I).n := by
    have hGV := namedInstance_valid I (connectedInitialInstance_valid J.toInstance (V : ℤ)
      J.toInstance_valid)
    intro e he
    obtain ⟨ht, hh⟩ := hGV e he
    rw [hInEq]
    exact ⟨Finset.mem_range.mp ht, Finset.mem_range.mp hh⟩
  -- Unconditional word-size and format inequalities from `hw` and `hQuotaBoundW`
  have hB14 : 2 ^ 14 * ipmQualityParameterBound I.m V k < 2 ^ w := by
    have hsz : ipmQualityParameterBound I.m V k < 2 ^ (ipmQualityParameterBound I.m V k).size :=
      Nat.lt_size_self _
    calc 2 ^ 14 * ipmQualityParameterBound I.m V k
        < 2 ^ 14 * 2 ^ (ipmQualityParameterBound I.m V k).size :=
          Nat.mul_lt_mul_of_pos_left hsz (by decide)
      _ = 2 ^ (14 + (ipmQualityParameterBound I.m V k).size) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  have h5L1W : 5 * F.limbs + 1 < 2 ^ w := by
    have hLle : F.limbs ≤ ipmQualityParameterBound I.m V k := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityParameterBound]; omega
    have h1 : 5 * F.limbs + 1 ≤ 2 ^ 14 * ipmQualityParameterBound I.m V k := by
      have : 1 ≤ ipmQualityParameterBound I.m V k := by unfold ipmQualityParameterBound; omega
      omega
    exact lt_of_le_of_lt h1 hB14
  have hbaseGe10 : 10 ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k :=
    shiftQuotaBase_ge_ten _ _ cfg.P.hk
  have hbasePowLt : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) < 2 ^ w := by
    have h1 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) ≤
        (2 * (namedInstance I).m + 2) * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact lt_of_le_of_lt h1 hQuotaBoundW
  have hkW : cfg.P.k < 2 ^ w := by
    have h1 : cfg.P.k ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k := by
      unfold shiftQuotaBase
      have hpsi1 : 1 ≤ alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀ := by unfold alg2PsiGameNat; omega
      exact Nat.le_mul_of_pos_left _ (by omega)
    have h2 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ≤
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_self_pow (by omega) _
    exact lt_of_le_of_lt (h1.trans h2) hbasePowLt
  have hdW : cfg.P.d + 1 < 2 ^ w := by
    have h1 : cfg.P.d + 1 < 2 ^ (cfg.P.d + 1) := Nat.lt_two_pow_self
    have h2 : 2 ^ (cfg.P.d + 1) ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.pow_le_pow_left (by omega) _
    exact lt_trans (lt_of_lt_of_le h1 h2) hbasePowLt
  have hepsW : epsExp < 2 ^ w := by
    have hkLe : k ≤ F.rangeExponent := by
      have h1 := qualityExponent_le_qualitySlackExponent I.m V k
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityRangeExponent]; omega
    have haLe : Num.IPM.alphaExponent I.m V ≤ F.fmt.precision :=
      (ipm_quality_precision_margins I.m V k).2.2.2.2.2
    have hEP : F.rangeExponent + F.fmt.precision + 10 ≤ ipmQualityParameterBound I.m V k := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityParameterBound]; omega
    have h2 : ipmQualityParameterBound I.m V k < 2 ^ w := by
      have h1 : ipmQualityParameterBound I.m V k ≤ 2 ^ 14 * ipmQualityParameterBound I.m V k :=
        Nat.le_mul_of_pos_left _ (by decide)
      exact lt_of_le_of_lt h1 hB14
    dsimp only [epsExp]; omega
  have hInLe : I.n ≤ 2 * I.m + 2 := by
    have hInDef : I.n = J.n + 1 := rfl
    omega
  have h2nW : 2 * (namedInstance I).n + 1 < 2 ^ w := by
    rw [hInEq]
    have h20 : 20 * I.m < 2 ^ w := hfit.2.2.2.2.2.1
    omega
  have hlogW : Nat.log 2 (2 * (namedInstance I).n + 1) ≤ 4 * F.limbs := by
    rw [hInEq]
    have hlt : 2 * I.n + 1 < 2 ^ (I.m.size + 4) := by
      have hmSz : I.m < 2 ^ I.m.size := Nat.lt_size_self I.m
      have h16 : 2 ^ (I.m.size + 4) = 16 * 2 ^ I.m.size := by rw [pow_add]; ring
      omega
    have hlogLt : Nat.log 2 (2 * I.n + 1) < I.m.size + 4 :=
      (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr hlt
    have hSzP : 5 * F.rangeExponent + I.m.size + 30 ≤ F.fmt.precision :=
      (ipm_quality_precision_margins I.m V k).2.2.1
    omega
  have hsizeM : Nat.size I.m ≤ F.rangeExponent + 8 := by
    have h1 : I.m.size ≤ (I.m.size + V.size) ^ 2 :=
      (Nat.le_add_right _ _).trans (Nat.le_self_pow (by decide) _)
    have h2 : (I.m.size + V.size) ^ 2 ≤ slackRangeExponent I.m V :=
      Nat.le_mul_of_pos_left _ (by decide)
    have h3 : slackRangeExponent I.m V ≤ qualitySlackExponent I.m V k :=
      slackRangeExponent_le_qualitySlackExponent I.m V k
    have h4 : qualitySlackExponent I.m V k ≤ F.rangeExponent := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityRangeExponent]; omega
    omega
  refine ⟨solverStateRepFullKFBL cfg (1 / (2 : ℝ) ^ k) (namedInstance I) F.limbs F.fmt.precision I.m V
      psi k epsExp (detectOffTreeDrainUnit F.limbs)
      (cycleLoopIterBudget F.limbs cfg.P.d (selectBudget + evalBudget + 90)
        (max termFixed deepFixed + 28 * (cfg.P.d + 1) + 220))
      toolMul treeMul Rcore DeepInv, ?_, hAllocLe⟩
  exact ordSolver_implements_full_wired (U_cap := V) hlocalCore (Or.inr hMonoCfg) hVcfg hmG hnG
    (connectedInitialInstance_connected J.toInstance (V : ℤ))
    hEΨ hw14 rfl hLpos hPL hImPos rfl rfl rfl h4M3W hkW hεPos hεLe rfl hEndsLt hthrB hthrTree
    hCapTreeInit rfl rfl h5L1W hdW hepsW hQuotaBoundW h2nW hlogW hsizeM hmaxEP hcapEvalB hcapTreeB
    hcapOffB hWordLvl hCapLevels hIntCapMax hFEdgeCap hDeepInv hp hInitAt hOverAt hclog hRefAt
    hEditsAt hQuotaAt hFindAt hShiftAt hInitConcrete hCore hSel hEval hTerm hDeep
    (goodCycleNumericBridge_wired F cfg (namedInstance I) I.m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore maxEdges maxPaths B_bound R_bound)
    hEnv

end MinCostFlow.MinRatio
