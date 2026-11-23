module

public import MinCostFlow.Final.AssemblyDryRunSCSelInitCode
public import MinCostFlow.Final.AssemblyDryRunSCSelInitTight
public import MinCostFlow.Final.AssemblyDryRunSCSelInitFacts
public import MinCostFlow.MinRatio.OrdSolverWiredSel
import MinCostFlow.Final.AssemblyDryRunSCSelInitRun
import MinCostFlow.MinRatio.SelectHeapInit
import MinCostFlow.MinRatio.SelectRegionSkeleton
import MinCostFlow.MinRatio.SelectCopyValues
import MinCostFlow.MinRatio.SelectCoreLenFill
import MinCostFlow.MinRatio.SelectCoreList
import MinCostFlow.MinRatio.SelectEmbCopy
import MinCostFlow.MinRatio.SelectMetaTableRow
import MinCostFlow.MinRatio.SelectMetaTableWrite
import MinCostFlow.MinRatio.SelectPhiFill
import MinCostFlow.MinRatio.WireSelectHeapClear
import MinCostFlow.MinRatio.WireSelectEvalKeyBridge
import MinCostFlow.MinRatio.WireSelectUpdateEdge
import MinCostFlow.MinRatio.WireSelectUpdateLevel
import MinCostFlow.DynSpanner.Program.DynGraphOpsBasic
import MinCostFlow.DynSpanner.Program.DynGraphRefill
import MinCostFlow.DynSpanner.Program.DynGraphInit
import MinCostFlow.Final.AssemblyDryRunSCConnected
import MinCostFlow.Final.AssemblyDryRunSCFits
import MinCostFlow.Final.AssemblyDryRunSCDeepFacts
import Mathlib.Tactic

/-!
# Unconditional discharge of `hInitSel` (`SolverInitStepSpecSel`) for `drySelInitCode` (`AssemblyDryRunSCSelInit`)

Composes the concrete 96-procedure select-aware initializer block `drySelInitCode`
(`Final/AssemblyDryRunSCSelInitCode.lean`), the concrete potential `dryPot := progReembPot` and
tight `OrdInitConcreteSpecW` (`Final/AssemblyDryRunSCSelInitTight.lean`), and the initial-state
mathematical facts (`Final/AssemblyDryRunSCSelInitFacts.lean`) through
`solverInitWiredSel_runs_treeN` (`Final/AssemblyDryRunSCSelInitRun.lean`) and
`solverInitWiredSel_cost_to_spec` (`MinRatio/OrdSolverWiredSel.lean`), proving:

* `dryPLast_meetsContract`, `drySlot_meetsContract`: `MeetsContract` wrappers for `dryPLastBody`
  and `drySlotBody` against `selectPLastContract` / `selectSlotContract`.
* `drySelInitCode_hInitSel`: unconditionally discharges `SolverInitStepSpecSel` at
  `drySelInitProc ... drySelInitCode` inside `dryLinkedProgramSel ... drySelInitCode` with
  `pot := dryPot J`, `pLast := dryLastStretchP J`, `slot := drySlot I.m`, and
  `initSel := dryInitSelectSizes Psc`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. `MeetsContract` wrappers for `dryPLastBody` and `drySlotBody` -/

theorem dryPLast_meetsContract {w proc bitLen : ℕ} {p : Program} (J : Circulation)
    (hp : p.procs[proc]? = some (dryPLastBody bitLen))
    (hbits : MeetsContract w p bitLen Num.IPM.bitLengthContract)
    (hw14 : 14 ≤ w)
    (hm1W : (solverConnectedAugmented J).m + 1 < 2 ^ w) :
    MeetsContract w p proc
      (selectPLastContract w (solverConnectedAugmented J).m (dryLastStretchP J)
        (dryPLastCost (solverConnectedAugmented J).m)) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _hwords hpre
  obtain ⟨rfl, hpLastW⟩ := hpre
  obtain ⟨out, cost, hr, hmem, hcost⟩ :=
    dryPLastBody_runs (pos := pos) (mem := mem) (ω := ω) J hbits hw14 hm1W hpLastW
  exact ⟨.returned (dryLastStretchP J), out, cost, hr, ⟨hmem, rfl⟩, hcost⟩

theorem drySlot_meetsContract {w proc bitLen V L P : ℕ} {p : Program} (m : ℕ)
    (hp : p.procs[proc]? = some (drySlotBody bitLen (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed)))
    (hbits : MeetsContract w p bitLen Num.IPM.bitLengthContract)
    (hw14 : 14 ≤ w)
    (hthrW : concreteEdgeThresholdWithLast dryWitnessUsed < 2 ^ w)
    (hM0W : max m (concreteEdgeThresholdWithLast dryWitnessUsed) < 2 ^ w) :
    MeetsContract w p proc
      (selectSlotContract w m V L P (drySlot m)
        (drySlotCost (max m (concreteEdgeThresholdWithLast dryWitnessUsed)))) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _hwords hpre
  obtain ⟨rfl, hSlotW⟩ := hpre
  obtain ⟨out, cost, hr, hmem, hcost⟩ :=
    drySlotBody_runs (V := V) (L := L) (P := P) (pos := pos) (mem := mem) (ω := ω)
      m hbits hw14 hthrW hM0W hSlotW
  exact ⟨.returned (drySlot m), out, cost, hr, ⟨hmem, rfl⟩, hcost⟩

/-! ## 2. Helper arithmetic lemmas for `hvalBAll` and `hNumInit` -/

private theorem dryInitSel_valBAll {L P E m : ℕ} {cfg : Alg2Config} {G : MGraph}
    {mem : ℕ → ℕ} {g l : ℕ} {B_tree : ℤ}
    (hGE : G.E = Finset.range m)
    (hεPos : 0 < cfg.ε) (hεLe : cfg.ε ≤ (2 : ℝ) ^ E)
    (hThrB : (2 : ℤ) ^ (P + 2 * E + 1) ≤ B_tree)
    (hVecValid : ∀ e < m, Num.Valid mem (l + e * L) 4 L ∧
      0 < Num.intVal mem (l + e * L) 4 L ∧ Num.Valid mem (g + e * L) 4 L)
    (hLenWithin : IPM.LengthsWithin G E (readVector mem l 4 L P m))
    (hGradWithin : ∀ e ∈ G.E, |readVector mem g 4 L P m e| ≤ (2 : ℝ) ^ E) :
    ∀ e < m,
      let v := initialPathEdgeValue P cfg.ε
        (Num.intVal mem (g + e * L) 4 L) ((Num.intVal mem (l + e * L) 4 L).toNat)
      |v.gradient| ≤ B_tree ∧ |v.length| ≤ B_tree ∧ |v.flow| ≤ B_tree ∧ |v.detector| ≤ B_tree := by
  intro e he
  have heG : e ∈ G.E := hGE ▸ Finset.mem_range.mpr he
  have h2pPos : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have hpowLe : (2 : ℤ) ^ (P + E) ≤ (2 : ℤ) ^ (P + 2 * E + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hBnn : 0 ≤ B_tree := le_trans (pow_nonneg (by norm_num) _) hThrB
  have hlIntPos : 0 < Num.intVal mem (l + e * L) 4 L := (hVecValid e he).2.1
  have htoNat : (((Num.intVal mem (l + e * L) 4 L).toNat : ℕ) : ℤ) =
      Num.intVal mem (l + e * L) 4 L := Int.toNat_of_nonneg hlIntPos.le
  have hgradR : |(Num.intVal mem (g + e * L) 4 L : ℝ)| / (2 : ℝ) ^ P ≤ (2 : ℝ) ^ E := by
    have hg := hGradWithin e heG
    simp only [readVector, he, ↓reduceIte, Num.fixVal, abs_div, abs_of_pos h2pPos] at hg
    exact hg
  have hgradI : |Num.intVal mem (g + e * L) 4 L| ≤ (2 : ℤ) ^ (P + E) := by
    have h1 : |(Num.intVal mem (g + e * L) 4 L : ℝ)| ≤ (2 : ℝ) ^ E * (2 : ℝ) ^ P :=
      (div_le_iff₀ h2pPos).mp hgradR
    have h2 : (2 : ℝ) ^ E * (2 : ℝ) ^ P = ((2 : ℤ) ^ (P + E) : ℝ) := by
      push_cast; rw [pow_add, mul_comm]
    rw [h2] at h1
    exact_mod_cast h1
  have hlenR : (Num.intVal mem (l + e * L) 4 L : ℝ) / (2 : ℝ) ^ P ≤ (2 : ℝ) ^ E := by
    have hl := (hLenWithin e heG).2
    simp only [readVector, he, ↓reduceIte, Num.fixVal] at hl
    exact hl
  have hlenI : Num.intVal mem (l + e * L) 4 L ≤ (2 : ℤ) ^ (P + E) := by
    have h1 : (Num.intVal mem (l + e * L) 4 L : ℝ) ≤ (2 : ℝ) ^ E * (2 : ℝ) ^ P :=
      (div_le_iff₀ h2pPos).mp hlenR
    have h2 : (2 : ℝ) ^ E * (2 : ℝ) ^ P = ((2 : ℤ) ^ (P + E) : ℝ) := by
      push_cast; rw [pow_add, mul_comm]
    rw [h2] at h1
    exact_mod_cast h1
  have hdetRange := detectorThreshold_mem_range (P := P) hεPos hεLe (hLenWithin e heG).1
  have hlenEq : ((Num.intVal mem (l + e * L) 4 L).toNat : ℝ) / (2 : ℝ) ^ P =
      readVector mem l 4 L P m e := by
    have hcast : (((Num.intVal mem (l + e * L) 4 L).toNat : ℕ) : ℝ) =
        (Num.intVal mem (l + e * L) 4 L : ℝ) := by exact_mod_cast htoNat
    simp [readVector, he, Num.fixVal, hcast]
  dsimp only [initialPathEdgeValue]
  refine ⟨hgradI.trans (hpowLe.trans hThrB), ?_, by simpa using hBnn, ?_⟩
  · rw [htoNat, abs_of_pos hlIntPos]; exact hlenI.trans (hpowLe.trans hThrB)
  · rw [hlenEq, abs_neg, abs_of_nonneg hdetRange.1]; exact hdetRange.2.trans hThrB

private lemma dryInitSel_capTree_lt (I : Instance) (V k : ℕ) {w : ℕ}
    (hw : ipmQualityParameterWordBits I.m V k ≤ w)
    (h2n1Le : 2 * (namedInstance I).n + 1 ≤ 4 * I.m + 5) :
    let F := ipmQualityMinRatioFormat I.m V k hw
    2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) *
      (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) < (Num.capacity 4 F.limbs : ℤ) := by
  intro F
  have hlog1 : 2 * (namedInstance I).n + 1 < 2 ^ (F.rangeExponent + 12) := by
    have hsz : (2 * (namedInstance I).n + 1).size ≤ F.rangeExponent + 12 := by
      have h1 : (2 * (namedInstance I).n + 1).size ≤ (4 * I.m + 5).size := Nat.size_le_size h2n1Le
      have h2 : (4 * I.m + 5).size ≤ I.m.size + 4 := by
        rw [Nat.size_le]; have := Nat.lt_size_self I.m; have := Nat.one_le_pow I.m.size 2 (by decide)
        rw [pow_add]; omega
      have h3 : I.m.size ≤ F.rangeExponent + 8 := by
        have := le_trans (Nat.le_add_right I.m.size V.size) (Nat.le_self_pow (by decide : 2 ≠ 0) _)
        have hsr := slackRangeExponent_le_qualitySlackExponent I.m V k
        dsimp only [F, ipmQualityMinRatioFormat, ipmQualityRangeExponent]
        unfold slackRangeExponent at hsr; omega
      omega
    exact lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by decide) hsz)
  have h2n : ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) ≤ (2 : ℤ) ^ (F.rangeExponent + 12) := by
    exact_mod_cast le_of_lt hlog1
  have hCapEq : (Num.capacity 4 F.limbs : ℤ) = (2 : ℤ) ^ (4 * F.limbs) := by
    rw [Num.capacity, Num.base, ← pow_mul]; push_cast; rfl
  have h4L : F.fmt.precision + 3 * F.rangeExponent + 15 ≤ 4 * F.limbs := by
    dsimp only [F, ipmQualityMinRatioFormat, ipmQualityLimbs, ipmQualityPrecision,
      ipmQualityRangeExponent]
    omega
  rw [hCapEq]
  have hnn : (0 : ℤ) ≤ (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) := by positivity
  have hmul : 2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) *
      (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤
      (2 : ℤ) ^ (F.fmt.precision + 3 * F.rangeExponent + 14) := by
    have hle1 : 2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) ≤
        2 * (2 : ℤ) ^ (F.rangeExponent + 12) := by linarith
    calc 2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) *
          (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1)
        ≤ (2 * (2 : ℤ) ^ (F.rangeExponent + 12)) *
          (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) :=
          mul_le_mul_of_nonneg_right hle1 hnn
      _ = (2 : ℤ) ^ (F.fmt.precision + 3 * F.rangeExponent + 14) := by
          have hexp : F.rangeExponent + 12 + (F.fmt.precision + 2 * F.rangeExponent + 1) + 1 =
              F.fmt.precision + 3 * F.rangeExponent + 14 := by ring
          rw [mul_assoc, ← pow_add, ← pow_succ', hexp]
  exact lt_of_le_of_lt hmul (pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) (Nat.lt_of_succ_le h4L))

/-! ## 3. Core wiring of `drySelInitCode` on an abstract program `p` -/

private theorem drySelInitCode_contracts
    {w L P m V : ℕ} {cfg : Alg2Config} {G : MGraph}
    {p : Program} {b ops : ℕ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {g₀ l₀ : ℕ → ℝ} (J : Circulation)
    (hI : (solverConnectedAugmented J).m = m)
    (hw14 : 14 ≤ w) (hm1W : m + 1 < 2 ^ w)
    (hthrW : concreteEdgeThresholdWithLast dryWitnessUsed < 2 ^ w)
    (hM0W : max m (concreteEdgeThresholdWithLast dryWitnessUsed) < 2 ^ w)
    (hOps : p.HasAt ops (solverOpsProcs ops solverCycleChainRefresh solverCycleFindCycle
      solverCycleShiftLevel))
    (hb1 : p.procs[b + 1]? = some (dryPLastBody (b + 3)))
    (hb2 : p.procs[b + 2]? = some (drySlotBody (b + 3)
      (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed)))
    (hb3 : p.HasAt (b + 3) (Num.IPM.bitLengthModule (b + 3)))
    (hb5 : p.procs[b + 5]? = some (selectRegionSkeletonBody (b + 6) (b + 7)
      (b + 40 + dgIdxInitFromLists)))
    (hb6 : p.procs[b + 6]? = some selectHeapInitBody)
    (hb7 : p.procs[b + 7]? = some (selTableWriteBody (b + 8)))
    (hb8 : p.procs[b + 8]? = some selTableRowBody)
    (hb9 : p.procs[b + 9]? = some (dgCopyRefillBody (b + 36)))
    (hb10 : p.procs[b + 10]? = some (selCopyValuesBody (b + 55)))
    (hb15 : p.procs[b + 15]? = some (selCoreLenFillBody (b + 16)))
    (hb16 : p.procs[b + 16]? = some (selCoreLenEdgeBody (ops + 20) (b + 17)))
    (hb17 : p.procs[b + 17]? = some (wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops))
    (hb18 : p.procs[b + 18]? = some selFilterAbsentBody)
    (hb19 : p.procs[b + 19]? = some (selEmbCopyBody (b + 55)))
    (hb22 : p.procs[b + 22]? = some (selectRebuildLevelBody (b + 64) (b + 23)))
    (hb23 : p.procs[b + 23]? = some (selectProcessListBody (b + 23) (b + 24)))
    (hb24 : p.procs[b + 24]? = some (selectProcessEdgeBody (b + 82) (b + 61) (b + 63)))
    (hDgRef : p.HasAt (b + 25) (dgRefillModule (b + 25)))
    (hDgOps : p.HasAt (b + 25) dgOpsProcs)
    (hDgEdge : p.HasAt (b + 32) (dgEdgeProcs (b + 25)))
    (hDgBat : p.HasAt (b + 40) (dgBatchProcs (b + 25) (b + 32) (b + 37) (b + 40)))
    (hHeapAt : p.HasAt (b + 43) (selectHeapOpsModule (b + 43) 4))
    (hPhiAt : p.HasAt (b + 65) (selectPhiFillModule (b + 65) 4))
    (hEvalAt : p.HasAt (b + 82) (evalKeyModule (b + 82) 4))
    (hmod : SelectModelInv (Chain.Ordered.algorithm2_init cfg G g₀ l₀) G σ σ_mwu γ_ℓ γ_c)
    (hlPos : ∀ e ∈ G.E, 0 < l₀ e)
    (hEmbLen :
      let s0 := Chain.Ordered.algorithm2_init cfg G g₀ l₀
      ∀ j < cfg.P.d, ∀ e ∈ (s0.chain.toTreeChain.activeCore j).E \
        (s0.chain.toTreeChain.activeS j).E,
        (s0.chain.toTreeChain.activeEmb j e).length ≤ dryMaxEmbLen m)
    (hCandFit :
      let s0 := Chain.Ordered.algorithm2_init cfg G g₀ l₀
      CandidateKeysFit 4 P (dryLastStretchP J) L s0.chain.toTreeChain s0.chain.g s0.chain.ℓ) :
    let s0 := Chain.Ordered.algorithm2_init cfg G g₀ l₀
    MeetsContract w p (b + 1) (selectPLastContract w m (dryLastStretchP J) (dryPLastCost m)) ∧
    MeetsContract w p (b + 2) (selectSlotContract w m V L P (drySlot m)
      (drySlotCost (max m (concreteEdgeThresholdWithLast dryWitnessUsed)))) ∧
    MeetsContract w p (b + 25 + dgIdxInitEmpty) (dgInitEmptyContract w) ∧
    (∀ G_new : MGraph, ∀ vcS ecS,
      MeetsContract w p (b + 9)
        (dgCopyRefillContract w G.n (initTargetCap cfg G) vcS ecS dgEmptyGraph G_new)) ∧
    (∀ sb lvlMeta hbCell, MeetsContract w p (b + 5)
      (selectRegionSkeletonContract w P sb (selectHeapCap cfg G m) cfg.P.d G.n
        (initTargetCap cfg G) L (drySlot m) lvlMeta (dryLastStretchP J) hbCell)) ∧
    (∀ eL : List ℕ, MeetsContract w p (b + 10)
      (selCopyValuesContractSrc w G.m (initTargetCap cfg G) eL)) ∧
    (∀ eL : List ℕ, MeetsContract w p (b + 15)
      (selCoreLenFillContract w P (initTargetCap cfg G) eL)) ∧
    (∀ eL : List ℕ, MeetsContract w p (b + 18) (selFilterAbsentContract w eL)) ∧
    (∀ j < cfg.P.d, ∀ eL : List ℕ,
      MeetsContract w p (b + 19) (selEmbCopyContract w eL (s0.chain.toTreeChain.activeEmb j))) ∧
    (∀ (mloc : SelectLevelMetaLoc) (φ : ℕ → ℕ → ℝ),
      MeetsContract w p (b + 81)
        (selectPhiFillContract w 4 P mloc s0.chain.toTreeChain G s0.chain.g s0.chain.ℓ
          σ σ_mwu γ_ℓ γ_c φ)) ∧
    (∀ (loc : SelectHeapLoc) (mloc : SelectLevelMetaLoc) (φ : ℕ → ℕ → ℝ),
      mloc.pLast = dryLastStretchP J → mloc.Lk = L →
      MeetsContract w p (b + 22)
        (selectRebuildLevelContract w 4 P loc mloc s0.chain.toTreeChain s0.chain.g s0.chain.ℓ φ
          (fun j => s0.chain.toTreeChain.chainLen s0.chain.ℓ (j + 1))
          (evalKeySpace cfg.P.d (dryMaxEmbLen m) L)
          (evalKeyCost cfg.P.d (dryMaxEmbLen m) L))) := by
  intro s0
  have hw10 : 2 * 4 + 2 ≤ w := by omega
  have hOpsH := solverOpsProcs_initHelpers hw14 hOps
  have hBits : MeetsContract w p (b + 3) Num.IPM.bitLengthContract :=
    Num.IPM.bitLength_meetsContract
      (lt_of_lt_of_le (by decide : 2 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)) hb3
  have hHeapAny : ∀ loc : SelectHeapLoc, _ := fun loc =>
    selectHeapOpsModule_meetsContracts (w := w) (h := 4) (by decide) hw10 hHeapAt loc
  have hCopyLimbs : MeetsContract w p (b + 55) (copyLimbsToContract w) := by
    simpa only [Nat.add_assoc] using (hHeapAny ⟨0, 0, 0, 0, 0, 0⟩).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · subst hI; exact dryPLast_meetsContract (w := w) J hb1 hBits hw14 hm1W
  · exact drySlot_meetsContract (w := w) (V := V) (L := L) (P := P) m hb2 hBits hw14 hthrW hM0W
  · exact dgInitEmpty_meetsContract hDgOps
  · intro G_new vcS ecS
    exact dgCopyRefill_meetsContract hb9 fun vL eEdges => by
      simpa only [Nat.add_assoc] using
        (dgRefillModule_meetsContract (w := w) (vCap := G.n) (eCap := initTargetCap cfg G)
          (G_old := dgEmptyGraph) (G_new := G_new) (vL := vL) (eEdges := eEdges) hDgRef)
  · intro sb lvlMeta hbCell
    exact selectRegionSkeleton_meetsContract hb5
      (selectHeapInit_meetsContract hb6)
      (selTableWrite_meetsContract hb7 (selTableRow_meetsContract hb8))
      (dgInitFromLists_meetsContract hDgBat hDgEdge hDgOps)
  · intro eL; exact selCopyValues_meetsContract_src hb10 hCopyLimbs
  · intro eL
    exact selCoreLenFill_meetsContract hb15
      (selCoreLenEdge_meetsContract hb16 hOpsH.2.2.2.2.2.1 hb17
        hOpsH.2.2.2.2.1 hOpsH.2.2.1 hOpsH.2.2.2.2.2.2.1 hOpsH.1)
  · intro eL; exact selFilterAbsent_meetsContract hb18
  · intro _ _ _; exact selEmbCopy_meetsContract hb19 hCopyLimbs
  · intro mloc φ
    simpa only [Nat.add_assoc] using
      (selectPhiFillModule_meetsContract (w := w) (h := 4) (P := P)
        (mloc := mloc) (σ := σ) (σ_mwu := σ_mwu) (γ_ℓ := γ_ℓ) (γ_c := γ_c) (φ := φ)
        (by decide) hw10 hPhiAt)
  · intro loc mloc φ hpEq hLkEq
    have hH := hHeapAny loc
    have hClear : MeetsContract w p (b + 64) (heapClearLevelContract w 4 loc) := by
      simpa only [Nat.add_assoc] using hH.2.2.2.2.2.2.2.2.2.2
    have hUps : ∀ sz, MeetsContract w p (b + 61) (heapUpsertContract w 4 loc sz) := fun sz => by
      simpa only [Nat.add_assoc] using hH.2.2.2.2.2.2.2.1 sz
    have hDelIf : ∀ sz, MeetsContract w p (b + 63) (heapDeleteIfLevelContract w 4 loc sz) := fun sz => by
      simpa only [Nat.add_assoc] using hH.2.2.2.2.2.2.2.2.2.1 sz
    have hFitMloc : CandidateKeysFit 4 P mloc.pLast mloc.Lk
        s0.chain.toTreeChain s0.chain.g s0.chain.ℓ := by
      rw [hpEq, hLkEq]; exact hCandFit
    have hEdge := selectProcessEdge_meetsContract_evalKey
      (loc := loc) (mloc := mloc) (maxEmbLen := dryMaxEmbLen m)
      (φ := φ)
      (coreLen := fun j => s0.chain.toTreeChain.chainLen s0.chain.ℓ (j + 1))
      hb24 hEvalAt (by decide) hw10 hmod.1 hmod.2.1
      (fun f hf => hlPos f (hmod.1.1 ▸ hf))
      hEmbLen hFitMloc hUps hDelIf
    have hEdge' : MeetsContract w p (b + 24)
        (selectProcessEdgeContract w 4 P loc mloc s0.chain.toTreeChain s0.chain.g s0.chain.ℓ φ
          (fun j => s0.chain.toTreeChain.chainLen s0.chain.ℓ (j + 1))
          (evalKeySpace cfg.P.d (dryMaxEmbLen m) L)
          (evalKeyCost cfg.P.d (dryMaxEmbLen m) L)) := by
      rw [← hLkEq]; exact hEdge
    exact selectRebuildLevel_meetsContract hb22 hClear fun _ =>
      selectProcessList_meetsContract hb23 hEdge'

/-! ## 4. Unconditional discharge of `hInitSel` (`SolverInitStepSpecSel`) -/

set_option maxHeartbeats 800000 in
/-- **Unconditional proof of `hInitSel` (`SolverInitStepSpecSel`) for `drySelInitCode`** inside
`dryLinkedProgramSel`, fixing `pot := dryPot J`, `pLast := dryLastStretchP J`, `slot := drySlot I.m`,
and `initSel := dryInitSelectSizes Psc`. -/
theorem drySelInitCode_hInitSel
    (Psc : DrySparseCorePieces)
    (coreCode selectCode termCode deepCode : SolverInnerSubCode)
    (coreSz : DryCoreOpenSizes) (hCore : DryCoreOpenSizeBounds coreSz)
    (shiftSel : DryShiftSelectSizes) (hShiftSel : DryShiftSelectSizeBounds shiftSel) :
    let openSz := coreSz.toDryOpenSizes; let hOpen := hCore.toDryOpenSizeBounds
    let selSz := mkDrySelectRebuildSizes (dryInitSelectSizes Psc) shiftSel
    let hSel := mkDrySelectRebuildSizeBounds (dryInitSelectSizeBounds Psc) hShiftSel
    let inner := dryInnerCodeSel (dryInitCode (dryParamCode Psc)) coreCode selectCode
      termCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner drySelInitCode
    let initProc := drySelInitProc (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner drySelInitCode
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let s := dryInnerSizesWithSelect Psc openSz selSz source J
      SolverInitStepSpecSel F cfg G I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
        (cycleLoopIterBudget F.limbs cfg.P.d (s.selectBudget + s.evalBudget + 90)
          (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220))
        s.toolMul s.treeMul 4 2 (selSz.keyCost source J) (dryLastStretchP J) (drySlot I.m)
        (dryPot J) Rcore p initProc
        (s.initSpace' + initWiredExtraSpace cfg G) (s.initFixed + initWiredExtraCost cfg G) := by
  intro openSz hOpen selSz hSel inner p initProc source J hJn hJm hCost hCap hw
  dsimp only
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let thr := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let k := cappedQualityExponent thr A I.m
  let F := ipmQualityMinRatioFormat I.m V k hw
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let G := namedInstance I
  let w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source
  let limbMul := concreteReadout2LimbMul dryWitnessUsed
  let PscP := drySCParams Psc dryCapExp limbMul
  let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
  let s := dryInnerSizesWithSelect Psc openSz selSz source J
  let lay := dryTailLay Psc.sc inner
  let env := drySelInitEnv thr A Psc.sc inner
  let b := env.innerBase
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hInitProcEq : initProc = b := Nat.add_zero b
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15,
      hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23, hb24, hDgRef, hDgOps, hDgEdge, _, hDgBat,
      hHeapAt, hPhiAt, hEvalAt⟩ := drySelInitCode_hasAll Psc inner
  refine ⟨solverInitWiredSelBody solverCycleInit (lay.scOp 3) (b + 25 + dgIdxInitEmpty)
    (b + 9) (b + 4) (b + 1) (b + 2), by rw [hInitProcEq]; exact hb0, ?_⟩
  intro args mem pos ω hargsW hpre hz hroom
  obtain ⟨graph, g, l, heap, hargsEq, _, _, _, hGraphAt, _, hGV, _, hGraphEnd, hGradEnd, hLenEnd,
    hVecV, hlPos, hLenWithin, hGradWithin⟩ := hpre
  subst hargsEq
  have hFmt4 : F.fmt.limbBits = 4 := rfl
  rw [hFmt4] at hVecV hlPos hLenWithin hGradWithin
  have hheapArg : heapArg [graph, g, l, F.limbs, F.fmt.precision, V, heap] = heap := rfl
  rw [hheapArg] at hz hroom
  have hGm : G.m = I.m := namedInstance_m I
  have hInEq : G.n = I.n := by simp [G, namedInstance, MGraph.n]
  have hImGeJm : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap1).1
  have hImPos : 0 < I.m := lt_of_lt_of_le hJm hImGeJm
  have hGnLe : G.n ≤ 2 * I.m + 2 := by rw [hInEq]; change J.n + 1 ≤ 2 * I.m + 2; omega
  have h2n1Le : 2 * G.n + 1 ≤ 4 * I.m + 5 := by omega
  have hGE : G.E = Finset.range I.m := rfl
  have hEndsLt : ∀ e ∈ G.E, G.tail e < G.n ∧ G.head e < G.n := fun e he => by
    have hv := hGV e he
    rw [hInEq]
    exact ⟨Finset.mem_range.mp hv.1, Finset.mem_range.mp hv.2⟩
  have hfit := ipm_quality_parameter_words_fit I.m V k hw
  have hw14 : 14 ≤ w := hfit.1
  have hWordCoeff : Classical.choose (concrete_solver_word_bounds_poly dryWitnessUsed) ≤
      dryAllocCoeffConcrete Psc openSz hOpen selSz hSel :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hSCWordCoeff :
      Classical.choose (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed) ≤
      dryAllocCoeffConcrete Psc openSz hOpen selSz hSel :=
    le_max_right _ _
  obtain ⟨hQuotaBoundW, h4M3W⟩ :=
    Classical.choose_spec (concrete_solver_word_bounds_poly dryWitnessUsed)
      (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) hWordCoeff source J hJn hJm hCap1 hw
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of
    (le_max_left dryWitnessUsed.M_thresh _) (le_max_right dryWitnessUsed.M_thresh _)
    (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap1
  have hmG : G.m ≤ cfg.P.M₀ := by rw [hGm]; exact le_max_left _ _
  have hnG : G.n ≤ cfg.N₀ := by rw [hInEq]; exact hIn
  have hM₀Eq : cfg.P.M₀ = max I.m thr := rfl
  have hN₀Eq : cfg.N₀ = 4 * cfg.P.M₀ := rfl
  have hεPos : 0 < cfg.ε := by
    dsimp only [cfg, concreteCirculationCfgWithLast, concreteCirculationCfgOfDims,
      Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
    positivity
  have hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent := by
    dsimp only [cfg, concreteCirculationCfgWithLast, concreteCirculationCfgOfDims,
      Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
    have hk1 : (1 : ℝ) / 2 ^ k ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    have ha1 : (1 : ℝ) / 2 ^ Num.IPM.alphaExponent I.m V ≤ 1 :=
      div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    have hprod : (1 : ℝ) / 2 ^ k * (1 / 2 ^ Num.IPM.alphaExponent I.m V) ≤ 1 :=
      (mul_le_mul hk1 ha1 (by positivity) (by norm_num)).trans (by norm_num)
    have hE1 : (1 : ℝ) ≤ 2 ^ F.rangeExponent := one_le_pow₀ (by norm_num)
    have hnn : (0 : ℝ) ≤ 1 / 2 ^ k * (1 / 2 ^ Num.IPM.alphaExponent I.m V) := by positivity
    linarith
  have hwk : cfg.P.k < 2 ^ w := by
    have hpsi1 : 1 ≤ alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀ := by unfold alg2PsiGameNat; omega
    have h1 : cfg.P.k ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k := by
      unfold shiftQuotaBase; exact Nat.le_mul_of_pos_left _ (by omega)
    have h2 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ≤
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_self_pow (by omega) _
    have h3 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) ≤
        (2 * G.m + 2) * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact lt_of_le_of_lt ((h1.trans h2).trans h3) hQuotaBoundW
  have hd1W : cfg.P.d + 1 < 2 ^ w := by
    have hd1 : cfg.P.d + 1 ≤ 4 * cfg.P.M₀ + 3 := by
      have h1 : cfg.P.d ≤ (cfg.P.M₀ + 2).size := chosenD_le_size_add_two cfg.P.hM₀
      have h2 : (cfg.P.M₀ + 2).size ≤ cfg.P.M₀ + 2 := Nat.size_le.mpr Nat.lt_two_pow_self
      omega
    exact lt_of_le_of_lt hd1 h4M3W
  have hVecValid : ∀ e < I.m, Num.Valid mem (l + e * F.limbs) 4 F.limbs ∧
      0 < Num.intVal mem (l + e * F.limbs) 4 F.limbs ∧ Num.Valid mem (g + e * F.limbs) 4 F.limbs := by
    intro e he
    have heG : e ∈ G.E := hGE ▸ Finset.mem_range.mpr he
    have hposR : (0 : ℝ) < (Num.intVal mem (l + e * F.limbs) 4 F.limbs : ℝ) / (2 : ℝ) ^ F.fmt.precision := by
      have h := hlPos e heG
      have he' : e < (solverConnectedAugmented J).m := he
      simp only [readVector, he', ↓reduceIte, Num.fixVal] at h
      exact h
    have hposI : (0 : ℤ) < Num.intVal mem (l + e * F.limbs) 4 F.limbs := by
      have h2p : (0 : ℝ) < (2 : ℝ) ^ F.fmt.precision := by positivity
      exact_mod_cast (div_pos_iff_of_pos_right h2p).mp hposR
    exact ⟨(hVecV e he).2, hposI, (hVecV e he).1⟩
  have hGrid : IsDyadicGrid G F.fmt.precision (readVector mem l 4 F.limbs F.fmt.precision I.m) := by
    intro e he
    have heM : e < I.m := Finset.mem_range.mp he
    refine ⟨Num.intVal mem (l + e * F.limbs) 4 F.limbs, ?_⟩
    simp [readVector, heM, Num.fixVal]
  -- Initial-state model facts
  obtain ⟨⟨σ, σ_mwu, γ_ℓ, γ_c, hmod⟩, hReach, hRtCap, hLastBr, hVcap, hEcap, hFV, hFE,
      hGmLvl, hFmLvl, hFnLvl, hLvlM, hN0, hEmbSlot, hEmbLen, _, hFitPhi, hCandFit⟩ :=
    dryInitSel_modelFacts J hJn hJm hCap1
      (readVector mem g 4 F.limbs F.fmt.precision I.m)
      (readVector mem l 4 F.limbs F.fmt.precision I.m) hLenWithin hGrid hGradWithin
  have hGnLvl : ∀ j ≤ cfg.P.d,
      ((Chain.Ordered.algorithm2_init cfg G
        (readVector mem g 4 F.limbs F.fmt.precision I.m)
        (readVector mem l 4 F.limbs F.fmt.precision I.m)).chain.G j).n ≤ G.n := by
    intro j hj
    calc ((Chain.Ordered.algorithm2_init cfg G
            (readVector mem g 4 F.limbs F.fmt.precision I.m)
            (readVector mem l 4 F.limbs F.fmt.precision I.m)).chain.G j).V.card
        ≤ (Finset.range G.n).card :=
          Finset.card_le_card fun v hv => Finset.mem_range.mpr (hVcap j hj v hv)
      _ = G.n := Finset.card_range G.n
  have hLenFitInt := dryInitSel_hLenFitInt J hJn hJm hCap1
    (readVector mem g 4 F.limbs F.fmt.precision I.m)
    (readVector mem l 4 F.limbs F.fmt.precision I.m) hLenWithin hGrid
  have hLenFitLast := dryInitSel_hLenFitLast J hJn hJm hCap1
    (readVector mem g 4 F.limbs F.fmt.precision I.m)
    (readVector mem l 4 F.limbs F.fmt.precision I.m) hLenWithin hGrid
  -- Word bounds for `pLast`, `slot`, `thr`, `M₀`, `I.m + 1`
  have hM0W : max I.m thr < 2 ^ w :=
    lt_of_le_of_lt (by change cfg.P.M₀ ≤ 4 * cfg.P.M₀ + 3; omega) h4M3W
  have hthrW : thr < 2 ^ w := lt_of_le_of_lt (le_max_right I.m thr) hM0W
  have hm1W : I.m + 1 < 2 ^ w := by
    have hle : I.m ≤ cfg.P.M₀ := le_max_left _ _
    exact lt_of_le_of_lt (by omega : I.m + 1 ≤ 4 * cfg.P.M₀ + 3) h4M3W
  have hpLastW : dryLastStretchP J < 2 ^ w := by
    have h1 := dryLastStretchP_le_forty_rangeExponent J hJn hJm hCap1
    have hmono : (I.m + 1).size ≤ (max I.m (levelM cfg.TP cfg.P cfg.P.d) + 1).size :=
      Nat.size_le_size (Nat.add_le_add_right (le_max_left _ _) 1)
    have h40 : dryLastStretchP J ≤ 40 * F.rangeExponent := by
      dsimp only [dryLastStretchP, F, ipmQualityMinRatioFormat, I, V, k, thr, A, cfg] at h1 hmono ⊢; omega
    have h4L : 40 * F.rangeExponent ≤ 4 * F.limbs := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityLimbs, ipmQualityPrecision]; omega
    have hL4W : 4 * F.limbs < 2 ^ w := by
      have hLle : F.limbs ≤ ipmQualityParameterBound I.m V k := by
        dsimp only [F, ipmQualityMinRatioFormat, ipmQualityParameterBound]; omega
      have hsz : ipmQualityParameterBound I.m V k < 2 ^ (ipmQualityParameterBound I.m V k).size :=
        Nat.lt_size_self _
      have hB14 : 2 ^ 14 * ipmQualityParameterBound I.m V k < 2 ^ w := by
        calc 2 ^ 14 * ipmQualityParameterBound I.m V k
            < 2 ^ 14 * 2 ^ (ipmQualityParameterBound I.m V k).size :=
              Nat.mul_lt_mul_of_pos_left hsz (by decide)
          _ = 2 ^ (14 + (ipmQualityParameterBound I.m V k).size) := (pow_add 2 _ _).symm
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
      omega
    omega
  have hSlotW : drySlot I.m < 2 ^ w := by
    have h1 : drySlot I.m ≤ selectBlocksSize cfg.P.d G.n (initTargetCap cfg G) F.limbs (drySlot I.m) := by
      unfold selectBlocksSize
      have hd1 : 1 ≤ cfg.P.d + 1 := Nat.succ_pos _
      have he1 : 1 ≤ initTargetCap cfg G := by unfold initTargetCap; rw [hGm]; omega
      have hmul1 : drySlot I.m ≤ initTargetCap cfg G * drySlot I.m := Nat.le_mul_of_pos_left _ he1
      have hmul2 : initTargetCap cfg G * drySlot I.m ≤
          (cfg.P.d + 1) * (dynGraphSize G.n (initTargetCap cfg G) + G.n * F.limbs +
            initTargetCap cfg G * F.limbs + initTargetCap cfg G + initTargetCap cfg G * drySlot I.m) :=
        le_trans (by omega) (Nat.le_mul_of_pos_left _ hd1)
      omega
    have h2 : selectBlocksSize cfg.P.d G.n (initTargetCap cfg G) F.limbs (drySlot I.m) ≤
        dryInitSelectSpace source J := by
      dsimp only [dryInitSelectSpace]
      exact (Nat.le_add_left _ _).trans (((((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans
        (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)))
    have h3 : dryInitSelectSpace source J ≤ s.initSpace' := by
      change dryInitSelectSpace source J ≤ _ + dryInitSelectSpace source J
      exact Nat.le_add_left _ _
    exact lt_of_le_of_lt (((h1.trans h2).trans h3).trans (Nat.le_add_right _ _))
      (lt_of_le_of_lt (Nat.le_add_left _ heap) hroom)
  -- Tight `OrdInitConcreteSpecW`, tail procedures, solver ops, and all helper `MeetsContract`s
  have hInitTight := dryInitCode_hInitConcrete_tight_sel Psc coreCode selectCode
    termCode deepCode drySelInitCode openSz hOpen selSz hSel source J hJn hJm hCost hCap hw
  have hTail := dryLinkedProgramSel_tail_hasAt dryWitnessUsed Psc.sc inner drySelInitCode
  have hOpsAt := dryLinkedProgramSel_ops_hasAt dryWitnessUsed Psc.sc inner drySelInitCode
  have hOps := solverOpsProcs_initHelpers hw14 hOpsAt
  obtain ⟨hPLastMC, hSlotMC, hDgEmpty, hDgCopy, hSkel, hCopyVal, hCoreLen, hFilter, hEmbCopy,
      hPhiFill, hRebLvl⟩ :=
    drySelInitCode_contracts (w := w) (L := F.limbs) (P := F.fmt.precision) (m := I.m) (V := V)
      (cfg := cfg) (G := G) (p := p) (b := b) (ops := mrdsCycleBase)
      J rfl hw14 hm1W hthrW hM0W hOpsAt
      hb1 hb2 hb3 hb5 hb6 hb7 hb8 hb9 hb10 hb15 hb16 hb17 hb18 hb19 hb22 hb23 hb24
      hDgRef hDgOps hDgEdge hDgBat hHeapAt hPhiAt hEvalAt
      hmod hlPos hEmbLen hCandFit
  -- `hFootAt` at `initialGraph := G` (valid since `G` is connected, so `G.n ≤ G.m + 1`)
  have hGnm : G.n ≤ G.m + 1 := by
    have h := (drySolver_init_level_n_le_m_add_one J hJn hJm hCap1
      (readVector mem g 4 F.limbs F.fmt.precision I.m)
      (readVector mem l 4 F.limbs F.fmt.precision I.m)
      hlPos (fun e he => (abs_log_le_of_two_pow_bounds (hLenWithin e he).1 (hLenWithin e he).2).trans
        (by change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
              ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
            exact_mod_cast (by omega)))
      0 (Nat.zero_le _)).2
    have hG0 : (Chain.Ordered.algorithm2_init cfg G
      (readVector mem g 4 F.limbs F.fmt.precision I.m)
      (readVector mem l 4 F.limbs F.fmt.precision I.m)).chain.G 0 = G := hmod.1.1
    rwa [hG0] at h
  have hFootAt : ∀ j < cfg.P.d,
      SparseCoreReadoutFootAt F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
        ((Chain.Ordered.algorithm2_init cfg G
          (readVector mem g 4 F.limbs F.fmt.precision I.m)
          (readVector mem l 4 F.limbs F.fmt.precision I.m)).chain.lvlM j)
        (Chain.Ordered.algorithm2_init cfg G
          (readVector mem g 4 F.limbs F.fmt.precision I.m)
          (readVector mem l 4 F.limbs F.fmt.precision I.m)).chain.N₀
        G.n (initTargetCap cfg G) dryCapExp PscP (drySCAlloc Psc dryCapExp limbMul J)
        Rcore p lay.scOp := fun j hj => by
    rw [hLvlM j hj, hN0]
    exact (drySC_coreKFBL_sel Psc inner drySelInitCode
      (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel)
      source J hJn hJm hCap1 hw j hj G hGnm hGm.le).2
  -- Space and cost dominance
  have hSelSpLe := solverInitWiredSelSpace_le_dryInitSelectSpace source J
    (Chain.Ordered.algorithm2_init cfg G
      (readVector mem g 4 F.limbs F.fmt.precision I.m)
      (readVector mem l 4 F.limbs F.fmt.precision I.m)).chain
    hLvlM hN0 hGmLvl hFmLvl hFnLvl
  have hSelCostLe := solverInitWiredSelCost_le_dryInitSelectFixed Psc source J
    (dryPLastCost I.m) (drySlotCost cfg.P.M₀)
    (dryPLastCost_add_drySlotCost_le_dryParamCost source J)
    (Chain.Ordered.algorithm2_init cfg G
      (readVector mem g 4 F.limbs F.fmt.precision I.m)
      (readVector mem l 4 F.limbs F.fmt.precision I.m)).chain
    hLvlM hN0 hGmLvl hGnLvl hFmLvl hFnLvl
  have hTotSpLe :
      initConcreteSpace I.m G.n F.limbs cfg.P.d (dryParamSpace source J) dryCapExp
        (dryCapLimit dryWitnessUsed J) (dryLastSpace J)
        (LinkCut.PathProg.arenaEnd 0 G.n F.limbs) (20 * LinkCut.PathProg.treeLimbs F.limbs + 100)
        (dryCoreInitSpace Psc J) (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀ +
        initWiredExtraSpace cfg G +
        solverInitWiredSelSpace (Chain.Ordered.algorithm2_init cfg G
          (readVector mem g 4 F.limbs F.fmt.precision I.m)
          (readVector mem l 4 F.limbs F.fmt.precision I.m)).chain
          G.n (initTargetCap cfg G) (selectHeapCap cfg G I.m) F.limbs dryCapExp (drySlot I.m) 1
          (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs) ≤
      s.initSpace' + initWiredExtraSpace cfg G := by
    change _ + initWiredExtraSpace cfg G + _ ≤ _ + dryInitSelectSpace source J + initWiredExtraSpace cfg G
    rw [Nat.add_right_comm]
    exact Nat.add_le_add_right (Nat.add_le_add_left hSelSpLe _) _
  have hTotFixLe :
      initConcreteFixed I.m G.n F.limbs cfg.P.d (dryParamCost source J) dryCapExp
        (dryCapLimit dryWitnessUsed J) (dryLastMult J) LinkCut.PathProg.pathC PscP
        (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀ +
        initWiredExtraCost cfg G +
        solverInitWiredSelCost (Chain.Ordered.algorithm2_init cfg G
          (readVector mem g 4 F.limbs F.fmt.precision I.m)
          (readVector mem l 4 F.limbs F.fmt.precision I.m)).chain
          PscP.readout (selectHeapCap cfg G I.m) F.limbs dryCapExp (drySlot I.m)
          (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs)
          (dryPLastCost I.m) (drySlotCost cfg.P.M₀) ≤
      s.initFixed + initWiredExtraCost cfg G := by
    change _ + initWiredExtraCost cfg G + _ ≤ _ + dryInitSelectFixed Psc source J + initWiredExtraCost cfg G
    rw [Nat.add_right_comm]
    exact Nat.add_le_add_right (Nat.add_le_add_left hSelCostLe _) _
  have hRoomWired :
      heap + (initConcreteSpace I.m G.n F.limbs cfg.P.d (dryParamSpace source J) dryCapExp
        (dryCapLimit dryWitnessUsed J) (dryLastSpace J)
        (LinkCut.PathProg.arenaEnd 0 G.n F.limbs) (20 * LinkCut.PathProg.treeLimbs F.limbs + 100)
        (dryCoreInitSpace Psc J) (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀ +
        initWiredExtraSpace cfg G +
        solverInitWiredSelSpace (Chain.Ordered.algorithm2_init cfg G
          (readVector mem g 4 F.limbs F.fmt.precision I.m)
          (readVector mem l 4 F.limbs F.fmt.precision I.m)).chain
          G.n (initTargetCap cfg G) (selectHeapCap cfg G I.m) F.limbs dryCapExp (drySlot I.m) 1
          (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs)) < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add_left hTotSpLe heap) hroom
  -- Invoke `solverInitWiredSel_runs_treeN`
  obtain ⟨scOut, cost, sb, out, tokFull', sg, hrMain, hfits, hrepSel, hCapsSel, hLaySel,
      _, _, _, _, hRegSel, hTreeI, hSepI, hResp, hcost⟩ :=
    solverInitWiredSel_runs_treeN
      (fmt := F.fmt) (cfg := cfg) (κ := 1 / (2 : ℝ) ^ k) (G := G) (initialGraph := G)
      (Psc := PscP) (allocation := drySCAlloc Psc dryCapExp limbMul J) (Rcore := Rcore)
      (pot := dryPot J) (p := p) (op := lay.scOp) (ω := ω) (mem := mem) (B_tree := s.B_tree)
      (unit := cycleLoopIterBudget F.limbs cfg.P.d (s.selectBudget + s.evalBudget + 90)
        (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220))
      (toolMul := s.toolMul) (treeMul := s.treeMul) (K := selSz.keyCost source J)
      (pLast := dryLastStretchP J) (slot := drySlot I.m) (op3Space := 1)
      (evalSpace := evalKeySpace cfg.P.d (dryMaxEmbLen I.m) F.limbs)
      (evalCost := evalKeyCost cfg.P.d (dryMaxEmbLen I.m) F.limbs)
      (pLastCost := dryPLastCost I.m) (slotCost := drySlotCost cfg.P.M₀)
      (pos := pos)
      rfl rfl (drySCRep_local Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw)
      (dryPot_facts J)
      (solverTail_initWired_at hTail) hb4 hInitTight
      (solverTail_overwrite_at hTail) hOps.1
      (fun n => solverTail_clog_meetsContract hTail n)
      hPLastMC hSlotMC hw14 hfit.2.1 hSlotW hpLastW hwk hImPos
      hVcfg hmG hnG hM₀Eq hN₀Eq h4M3W hd1W hεPos hGE hEndsLt
      hGraphAt hGraphEnd (by rw [hGm]; exact hLenEnd) (by rw [hGm]; exact hGradEnd)
      hVecValid hLenWithin hGradWithin
      hfit.2.2.1 hfit.2.2.2.2.2.2.2
      (fun i hi => by
        rw [hLvlM i hi]
        exact (drySC_deepWordLvl Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) hSCWordCoeff
          source J hJn hJm hCost hCap hw i hi).2)
      (fun i hi vCap eCap hlim => by
        rw [hLvlM i hi, hN0]
        exact concrete_sparseCoreCapHyp_uniform dryWitnessUsed J hJn hJm hCap1 i hi.le vCap eCap hlim)
      (dryInitSel_valBAll hGE hεPos hεLe le_rfl hVecValid hLenWithin hGradWithin)
      hmod hReach
      (fun tok htn hnum =>
        solverTreeNumericInv_of_update (E := F.rangeExponent) (n := G.n) (B_bound := s.B_tree)
          (R_bound := 0) (X := 0) hεPos hεLe
          htn hnum (by omega) (by omega)
          (by rw [add_zero, add_zero, add_zero]; exact dryInitSel_capTree_lt I V k hw h2n1Le) le_rfl le_rfl
          fun e he => (hLenWithin e he).1)
      hLastBr hVcap hEcap hFV hFE hLenFitInt hLenFitLast hEmbSlot hGnLe hFitPhi
      hDgEmpty hSkel hCopyVal hb11 hb12 hb13 hb14 hFootAt le_rfl hDgCopy hCoreLen hFilter
      hEmbCopy hb20 hPhiFill hb21 hRebLvl hz hRoomWired
  -- The tree budget at `updateCount = 0`: the init tree holds `B_tree = 2^(P + 2E + 1) ≤ B₀`, the
  -- stored vectors are the input vectors, and every accumulator is `0`.
  have hBud : SolverTreeBudgetInv G F.fmt.precision F.rangeExponent 0
      (Chain.Ordered.algorithm2_init cfg G (readVector mem g 4 F.limbs F.fmt.precision I.m)
        (readVector mem l 4 F.limbs F.fmt.precision I.m)) tokFull'.1.1 out.mem := by
    refine ⟨Nat.zero_le _, fun e he => ?_, fun _ => le_rfl, hSepI, ?_⟩
    · exact ⟨hGradWithin e he, (hLenWithin e he).1, (hLenWithin e he).2⟩
    · rw [mul_zero, add_zero]
      refine hTreeI.mono ?_ le_rfl
      show (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤
        (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 2)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨scOut, cost, out, (tokFull', sg), hrMain, hfits, hrepSel, hCapsSel, hLaySel, hRegSel, hBud,
    ⟨hResp.1, hResp.2.1.trans (Nat.add_le_add_left hTotSpLe heap),
      hResp.2.2.1, hResp.2.2.2.1, hResp.2.2.2.2⟩, ?_⟩
  exact solverInitWiredSel_cost_to_spec hRtCap
    ((dryInitMul_add_keyCost_le_dryToolMul Psc (dryInitSelectSizes Psc) shiftSel source J).trans
      (Nat.le_add_right _ _))
    hTotFixLe hcost

end MinCostFlow.Final.DryRun

end
