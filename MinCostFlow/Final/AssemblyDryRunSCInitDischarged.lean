module

public import MinCostFlow.Final.AssemblyDryRunSCInitCode
public import MinCostFlow.Final.AssemblyDryRunSCParam
import MinCostFlow.Final.AssemblyDryRunSCOpen
import MinCostFlow.Final.AssemblyDryRunSCCoreKFBL
import MinCostFlow.Final.AssemblyDryRunSCFits
import Mathlib.Tactic

/-!
# Unconditional discharge of `hInitConcrete` for `dryInnerCodeSel` (`AssemblyDryRunSCInitDischarged`)

Packages `dryParamProcs` (`Final/AssemblyDryRunSCParam.lean`) into a concrete deterministic
`SolverInnerSubCode` block `dryParamCode Psc`, proves placement of `dryParamProcs` inside
`dryLinkedProgram` with `dryInnerCodeSel (dryInitCode (dryParamCode Psc)) ...`, and discharges
all five premises (`hParam`, `hCoreImpl`, `hLastImpl`, `hCoreLenFits`, `hLastStretchFits`) of
`dryInitCode_meets_spec` (`Final/AssemblyDryRunSCInitCode.lean`) from the proved dry-run facts.

Main theorem:
* `dryInitCode_hInitConcrete`: unconditionally proves `ForAllDryInputs ... OrdInitConcreteSpecW`
  at `lay.initConcrete` for `dryInnerCodeSel (dryInitCode (dryParamCode Psc)) coreCode selectCode
  termCode deepCode`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Concrete deterministic `SolverInnerSubCode` for `dryParamProcs` -/

/-- Fixed runtime base address of `dryParamProcs` inside
`dryLinkedProgram dryWitnessUsed Psc.sc (dryInnerCodeSel (dryInitCode paramCode) ...)`.
Depends only on `Psc.sc` (independent of all inner blocks and all problem inputs). -/
def dryParamBase (Psc : DrySparseCorePieces) : ℕ :=
  (solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
    Psc.sc solverTailBase).innerBase + 1 + dryInitConcreteLen

/-- Concrete deterministic `SolverInnerSubCode` placing `dryParamProcs (dryParamBase Psc)` at
`dryParamBase Psc` (with fixed length `(dryParamProcs (dryParamBase Psc)).length` and entry offset
`0`). -/
def dryParamCode (Psc : DrySparseCorePieces) : SolverInnerSubCode where
  procs env :=
    if env.innerBase = dryParamBase Psc then
      dryParamProcs (dryParamBase Psc)
    else
      List.replicate (dryParamProcs (dryParamBase Psc)).length .nop
  len := (dryParamProcs (dryParamBase Psc)).length
  hlen env := by split_ifs <;> simp
  hnoRand env s hs := by
    split_ifs at hs
    · exact dryParamProcs_noRand _ s hs
    · simp only [List.mem_replicate] at hs
      rw [hs.2]
      simp [Stmt.NoRand]
  off := 0

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 2. Placement of `dryParamProcs` inside `dryInnerCodeSel` -/

private theorem hasAt_peel_param {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

/-- Placement of `dryParamProcs` at `dryInitParamProc Psc.sc (dryParamCode Psc) ...` inside
`dryLinkedProgram` with `dryInnerCodeSel (dryInitCode (dryParamCode Psc)) ...`. -/
theorem dryInnerCodeSel_hasParam (Psc : DrySparseCorePieces)
    (coreCode selectCode termCode deepCode : SolverInnerSubCode) :
    let inner := dryInnerCodeSel (dryInitCode (dryParamCode Psc)) coreCode selectCode termCode deepCode
    let p := dryLinkedProgram dryWitnessUsed Psc.sc inner
    let b := dryInitParamProc Psc.sc (dryParamCode Psc) coreCode selectCode termCode deepCode
    p.HasAt b (dryParamProcs b) := by
  intro inner p b
  have hInner := dryInner_hasAt (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed)
    (mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase)
      (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length)
    Psc.sc inner
    (dynLctForestBodies 4 (mrdsCycleBase +
      (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length))
  set env := solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
    Psc.sc solverTailBase
  have hInner' : p.HasAt env.innerBase (inner.procs env) := hInner
  unfold inner dryInnerCodeSel at hInner'
  dsimp only at hInner'
  obtain ⟨_, r1⟩ := hasAt_peel_param (b' := env.innerBase + 1) hInner' (by simp)
  have hInitSub := Num.hasAt_append_left r1
  unfold dryInitCode at hInitSub
  dsimp only at hInitSub
  obtain ⟨_, hParamAt⟩ := hasAt_peel_param (b' := env.innerBase + 1 + dryInitConcreteLen) hInitSub
    (by simp [dryInitConcreteProcs_length])
  have hbEq : env.innerBase + 1 + dryInitConcreteLen = dryParamBase Psc := rfl
  have hbEq2 : b = dryParamBase Psc := by
    dsimp only [b, dryInitParamProc, dryTailLay, solverTailLayout, dryInnerCodeSel, dryInitCode,
      dryParamCode, dryParamBase, env, solverTailInnerEnv]
    omega
  rw [hbEq] at hParamAt
  have hEqProcs : (dryParamCode Psc).procs { env with innerBase := dryParamBase Psc } =
      dryParamProcs (dryParamBase Psc) := by
    simp [dryParamCode]
  rw [hEqProcs] at hParamAt
  rw [hbEq2]
  exact hParamAt

/-! ## 3. Generic-placement `hParam`, `hCoreImpl`, and `hLastImpl` for `dryInnerCodeSel` -/

private lemma dryParamRow_eq_cfg' (J : Circulation) :
    let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
    let A := concreteQualityBudgetWithLast dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent threshold A I.m
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    dryParamRow I.m V =
      [cfg.P.d, cfg.P.k, ⌈cfg.Ψ⌉₊, k, k + Num.IPM.alphaExponent I.m V + 10, cfg.N₀] ++
        (List.range cfg.P.d).map (levelM cfg.TP cfg.P) ++
        [Expander.chosenL (max I.m threshold ^ 2)] := rfl

private lemma lt_of_eq_left' {a b c : ℕ} (h : a = b) (hlt : a < c) : b < c :=
  h ▸ hlt

private theorem initParamSetupContract_congr'
    {w m V L P d₁ d₂ b₁ b₂ psi₁ psi₂ q₁ q₂ e₁ e₂ n₁ n₂ cD₁ cD₂ s₁ s₂ c₁ c₂ : ℕ}
    {lvlM : ℕ → ℕ} {p : Program} {proc : ℕ}
    (hd : d₁ = d₂) (hb : b₁ = b₂) (hpsi : psi₁ = psi₂) (hq : q₁ = q₂)
    (he : e₁ = e₂) (hn : n₁ = n₂) (hcD : cD₁ = cD₂) (hs : s₁ = s₂) (hc : c₁ = c₂)
    (h : MeetsContract w p proc
      (initParamSetupContract w m V L P d₂ b₂ psi₂ q₂ e₂ n₂ cD₂ lvlM s₂ c₂)) :
    MeetsContract w p proc
      (initParamSetupContract w m V L P d₁ b₁ psi₁ q₁ e₁ n₁ cD₁ lvlM s₁ c₁) := by
  subst hd; subst hb; subst hpsi; subst hq; subst he; subst hn; subst hcD; subst hs; subst hc
  exact h

/-- Discharges `initParamSetupContract` at any `(p, b)` where `p.HasAt b (dryParamProcs b)`. -/
theorem dryParamProcs_discharges_hParam_at
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (p : Program) (b : ℕ) (hPlace : p.HasAt b (dryParamProcs b)) :
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let w := dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source
      MeetsContract w p b
        (initParamSetupContract w I.m V F.limbs F.fmt.precision cfg.P.d cfg.P.k
          ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10) cfg.N₀
          (Expander.chosenL (cfg.P.M₀ ^ 2))
          (levelM cfg.TP cfg.P) (dryParamSpace source J) (dryParamCost source J)) := by
  intro source J hJn hJm hCost hCap hw I V k F cfg w
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  have hPlace' : p.HasAt b (wireParamModule b threshold A dryDecompK dryDecompThr dryWitnessDen
      sparsifyPathDSUsed.boundsProcs dryParamLookupEntries) := hPlace
  obtain ⟨hw14, h220000W, hmW, hVW, hthrW, hM0_2W, halphaScaleW,
      hdW, hbrW, hpsiW, hqW, hepsW, hNW, hlvlW⟩ :=
    dryParam_outputs_lt_two_pow B hB source J hJn hJm hCost hCap hw
  have hscalars := concreteCfg_scalars_eq dryWitnessUsed I.m V
  have hM0_eq : cfg.P.M₀ = max I.m threshold := hscalars.1
  have hN0_eq : cfg.N₀ = paramN0 threshold I.m := hscalars.2.1
  have hPsi_eq : ⌈cfg.Ψ⌉₊ = paramPsi threshold A I.m V := hscalars.2.2.1
  have hDepth_eq : Expander.chosenL (cfg.P.M₀ ^ 2) = Expander.chosenL (max I.m threshold ^ 2) :=
    congrArg (fun M => Expander.chosenL (M ^ 2)) hM0_eq
  have hM01 : 1 ≤ max I.m threshold := cfg.P.hM₀.trans hM0_eq.le
  have hP_eq : cfg.P = Chain.concreteChainParams (max I.m threshold) hM01 := rfl
  have hdLe : cfg.P.d ≤ (max I.m threshold + 2).size :=
    (chosenD_le_size_add_two cfg.P.hM₀).trans (congrArg (fun M => (M + 2).size) hM0_eq).le
  have hw2 : 2 < 2 ^ w := by
    have h1 : 2 ^ 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hSpaceEq : dryParamSpace source J =
      wireParamSpace dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params
        (max I.m threshold) :=
    congrArg (wireParamSpace dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params) hM0_eq
  by_cases hlt : I.m < dryLevelMCut
  · have hCostEq : dryParamCost source J =
        wireParamCost dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params
          dryParamLookupEntries I.m V (max I.m threshold) cfg.P.d
          (Expander.chosenL (max I.m threshold ^ 2)) :=
      congrArg (fun M => wireParamCost dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params
        dryParamLookupEntries I.m V M cfg.P.d (Expander.chosenL (M ^ 2))) hM0_eq
    have hJm_le_Im : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm (fun e => (hCap e).1)).1
    have hRow := dryParamRow_eq_cfg' J
    have hdepW : Expander.chosenL (max I.m threshold ^ 2) < 2 ^ w :=
      dryParam_depth_lt_two_pow B hB source J hJn hJm hCost hCap hw
    have hmem : (I.m, V, [cfg.P.d, cfg.P.k, ⌈cfg.Ψ⌉₊, k, k + Num.IPM.alphaExponent I.m V + 10, cfg.N₀] ++
        (List.range cfg.P.d).map (levelM cfg.TP cfg.P) ++
        [Expander.chosenL (max I.m threshold ^ 2)]) ∈ dryParamLookupEntries := by
      unfold dryParamLookupEntries
      refine List.mem_flatMap.mpr ⟨I.m, List.mem_range.mpr hlt, ?_⟩
      refine List.mem_map.mpr ⟨J.m - 1, List.mem_range.mpr (by omega), ?_⟩
      have hpen : solverPenalty (J.m - 1 + 1) = V :=
        congrArg solverPenalty (by omega : J.m - 1 + 1 = J.m)
      exact Prod.ext rfl (Prod.ext hpen ((congrArg (dryParamRow I.m) hpen).trans hRow))
    have huniq : ∀ e ∈ dryParamLookupEntries, e.1 = I.m → e.2.1 = V →
        e.2.2 = [cfg.P.d, cfg.P.k, ⌈cfg.Ψ⌉₊, k, k + Num.IPM.alphaExponent I.m V + 10, cfg.N₀] ++
          (List.range cfg.P.d).map (levelM cfg.TP cfg.P) ++
          [Expander.chosenL (max I.m threshold ^ 2)] := by
      intro e he h1 h2
      unfold dryParamLookupEntries at he
      obtain ⟨m', _, he'⟩ := List.mem_flatMap.mp he
      obtain ⟨j', _, rfl⟩ := List.mem_map.mp he'
      dsimp only at h1 h2 ⊢
      exact (congrArg₂ dryParamRow h1 h2).trans hRow
    exact initParamSetupContract_congr' rfl rfl rfl rfl rfl rfl hDepth_eq hSpaceEq hCostEq
      (wireParamModule_meetsContract_hit hPlace' hM01 hdLe hw2 hmW hVW
        hdW hbrW hpsiW hqW hepsW hNW hlvlW hdepW hmem huniq)
  · have hge : dryLevelMCut ≤ I.m := Nat.le_of_not_lt hlt
    have hmiss : ∀ e ∈ dryParamLookupEntries, I.m ≠ e.1 ∨ V ≠ e.2.1 := by
      intro e he
      unfold dryParamLookupEntries at he
      obtain ⟨m', hm', he'⟩ := List.mem_flatMap.mp he
      obtain ⟨j', _, rfl⟩ := List.mem_map.mp he'
      have hm'_lt : m' < dryLevelMCut := List.mem_range.mp hm'
      exact Or.inl (by omega)
    have hMcutSpec := Classical.choose_spec exists_dryLevelM_threshold
    obtain ⟨_, _, hlvlM_eq, _, _⟩ := hMcutSpec.2 J hJn hJm (fun e => (hCap e).1) hge
    obtain ⟨h4M2W, hcubeW, hdenW, hcapW, hwitW, hcw1, hcw2, hnumW⟩ :=
      dryParam_general_word_bounds B hB source J hJn hJm hCost hCap hw hge
    have hk_eq : k = paramQuality threshold A I.m := rfl
    have heps_eq : k + Num.IPM.alphaExponent I.m V + 10 = paramEpsExp threshold A I.m V := rfl
    have hd_eq : cfg.P.d = (Chain.concreteChainParams (max I.m threshold) hM01).d :=
      congrArg ChainParams.d hP_eq
    have hbr_eq : cfg.P.k = (Chain.concreteChainParams (max I.m threshold) hM01).k :=
      congrArg ChainParams.k hP_eq
    have hCostEq : dryParamCost source J =
        wireParamCost dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params
          dryParamLookupEntries I.m V (max I.m threshold)
          (Chain.concreteChainParams (max I.m threshold) hM01).d
          (Expander.chosenL (max I.m threshold ^ 2)) := by
      have h1 : dryParamCost source J =
          wireParamCost dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params
            dryParamLookupEntries I.m V (max I.m threshold) cfg.P.d
            (Expander.chosenL (max I.m threshold ^ 2)) :=
        congrArg (fun M => wireParamCost dryDecompK dryDecompThr dryWitnessDen
          sparsifyPathDSUsed.params dryParamLookupEntries I.m V M cfg.P.d
          (Expander.chosenL (M ^ 2))) hM0_eq
      exact h1.trans (congrArg (fun d => wireParamCost dryDecompK dryDecompThr dryWitnessDen
        sparsifyPathDSUsed.params dryParamLookupEntries I.m V (max I.m threshold) d
        (Expander.chosenL (max I.m threshold ^ 2))) hd_eq)
    have hM0_2W' : max I.m threshold + 2 < 2 ^ w :=
      lt_of_eq_left' (congrArg (· + 2) hM0_eq) hM0_2W
    have hN0W' : 4 * max I.m threshold < 2 ^ w :=
      lt_of_eq_left' hN0_eq hNW
    have hpsiW' : paramPsi threshold A I.m V < 2 ^ w :=
      lt_of_eq_left' hPsi_eq hpsiW
    have h4M2W' : 4 * max I.m threshold ^ 2 + 2 < 2 ^ w :=
      lt_of_eq_left' (congrArg (fun M => 4 * M ^ 2 + 2) hM0_eq) h4M2W
    have hcubeW' : (Nat.log 2 (4 * max I.m threshold ^ 2 + 2) + 2) ^ 3 < 2 ^ w :=
      lt_of_eq_left' (congrArg (fun M => (Nat.log 2 (4 * M ^ 2 + 2) + 2) ^ 3) hM0_eq) hcubeW
    have hdenW' : drySparsifyDen (max I.m threshold) < 2 ^ w :=
      lt_of_eq_left' (congrArg drySparsifyDen hM0_eq) hdenW
    have hcapW' : drySparsifyCap (max I.m threshold) < 2 ^ w :=
      lt_of_eq_left' (congrArg drySparsifyCap hM0_eq) hcapW
    have hcw1' : sparsifyPathDSUsed.params.cw *
        (Nat.log 2 (drySparsifyDen (max I.m threshold) + max I.m threshold ^ 2 +
          sparsifyPathDSUsed.params.gExp (drySparsifyDen (max I.m threshold)) (max I.m threshold ^ 2) +
          sparsifyPathDSUsed.params.gDel (drySparsifyDen (max I.m threshold)) (max I.m threshold ^ 2) + 2) + 1) ≤ w :=
      hM0_eq ▸ hcw1
    have hcw2' : sparsifyPathDSUsed.params.cw *
        (Nat.log 2 (dryWitnessDen + drySparsifyCap (max I.m threshold) +
          sparsifyPathDSUsed.params.gExp dryWitnessDen (drySparsifyCap (max I.m threshold)) +
          sparsifyPathDSUsed.params.gDel dryWitnessDen (drySparsifyCap (max I.m threshold)) + 2) + 1) ≤ w :=
      hM0_eq ▸ hcw2
    have hnumW' : ∀ i < (Chain.concreteChainParams (max I.m threshold) hM01).d,
        let M₀ := max I.m threshold
        let C := Chain.concreteChainParams M₀ hM01
        let L_sp := Expander.chosenL (M₀ ^ 2)
        let den := Expander.maxPhiDenOf dryDecompK dryDecompThr (M₀ ^ 2)
        let cap := 36 * M₀ ^ 2 * den + 1
        let g := (max (sparsifyPathDSUsed.params.gExp den (M₀ ^ 2))
          (sparsifyPathDSUsed.params.gExp dryWitnessDen cap)) ^ 2
        let γ := 3 ^ L_sp * g ^ (L_sp + 1)
        M₀ * γ ^ (i + 1) + C.k ^ i < 2 ^ w := fun i hi =>
      lt_of_eq_left'
        (congrArg₂ (· + ·) (congrArg (fun M => M * (dryGammaNat M) ^ (i + 1)) hM0_eq)
          (congrArg (fun k => k ^ i) hbr_eq))
        (hnumW i (lt_of_lt_of_eq hi hd_eq.symm))
    have hlvlM' : ∀ i < (Chain.concreteChainParams (max I.m threshold) hM01).d,
        let M₀ := max I.m threshold
        let C := Chain.concreteChainParams M₀ hM01
        let L_sp := Expander.chosenL (M₀ ^ 2)
        let den := Expander.maxPhiDenOf dryDecompK dryDecompThr (M₀ ^ 2)
        let cap := 36 * M₀ ^ 2 * den + 1
        let g := (max (sparsifyPathDSUsed.params.gExp den (M₀ ^ 2))
          (sparsifyPathDSUsed.params.gExp dryWitnessDen cap)) ^ 2
        let γ := 3 ^ L_sp * g ^ (L_sp + 1)
        levelM cfg.TP cfg.P i = (M₀ * γ ^ (i + 1) + C.k ^ i - 1) / C.k ^ i := fun i _ =>
      (hlvlM_eq i).trans
        (congrArg₂ (fun a b => (a + b - 1) / b)
          (congrArg (fun M => M * (dryGammaNat M) ^ (i + 1)) hM0_eq)
          (congrArg (fun k => k ^ i) hbr_eq))
    exact initParamSetupContract_congr' hd_eq hbr_eq hPsi_eq hk_eq heps_eq hN0_eq hDepth_eq hSpaceEq hCostEq
      (wireParamModule_meetsContract_general hPlace'
        (fun hAt => sparsifyPathDSUsed.boundsSpec w p (b + wireParamBoundsOff) hAt)
        one_le_dryDecompK one_le_dryWitnessDen hM01 hw14 h220000W hmiss
        hmW hVW hthrW hM0_2W' hN0W' hqW halphaScaleW hepsW hpsiW'
        h4M2W' hcubeW' hdenW' hcapW' hwitW hcw1' hcw2' hnumW' hlvlM')

/-- `inner`-generic last-level implementation at the initial chain's terminal graph `chain.G d`. -/
theorem drySC_hLastImpl_inner (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) :
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
      let p := dryLinkedProgram dryWitnessUsed Psc.sc inner
      let lay := dryTailLay Psc.sc inner
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ vc ec, vc + ec + 2 ≤ dryCapLimit dryWitnessUsed J →
          (lastLevelRepresentation vc ec 4 F.limbs F.fmt.precision (chain.G cfg.P.d).E).Implements
            w p lay.lastInit lay.lastOp
            (lastLevelRuntimeMachineContract F.fmt F.limbs cfg.L (chain.G cfg.P.d) vc ec
              (dryLastMult J) (dryLastStretchP J) (fun _ _ => dryLastSpace J)) := by
  intro source J hJn hJm hCost hCap hw I V k F cfg G w p lay ℓ₀ g₀ hLen chain vc ec hcap
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hlPos : ∀ e ∈ G.E, 0 < ℓ₀ e := fun e he => lt_of_lt_of_le (by positivity) (hLen e he).1
  have hlR : ∀ e ∈ G.E, |Real.log (ℓ₀ e)| ≤ cfg.Ψ := fun e he =>
    (abs_log_le_of_two_pow_bounds (hLen e he).1 (hLen e he).2).trans hEΨ
  obtain ⟨hconn, hnm⟩ :=
    drySolver_init_level_n_le_m_add_one J hJn hJm hCap1 g₀ ℓ₀ hlPos hlR cfg.P.d le_rfl
  obtain ⟨-, -, hEsub, -, -⟩ :=
    drySC_chainLen_bounds J hJn hJm hCap1 ℓ₀ g₀ hLen cfg.P.d le_rfl
  have hm : (chain.G cfg.P.d).m ≤ (solverConnectedAugmented J).m :=
    le_trans (Finset.card_le_card hEsub) (namedInstance_m I).le
  have hmD : (chain.G cfg.P.d).m ≤ levelM cfg.TP cfg.P cfg.P.d := by
    have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1
    have hGV := namedInstance_valid I
      (connectedInitialInstance_valid J.toInstance (V : ℤ) J.toInstance_valid)
    obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of
      (le_max_left dryWitnessUsed.M_thresh _) (le_max_right dryWitnessUsed.M_thresh _)
      (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap1
    have hmG : G.m ≤ cfg.P.M₀ := by rw [namedInstance_m]; exact le_max_left _ _
    have hnG : G.n ≤ cfg.N₀ := by
      have hInEq : G.n = I.n := by simp [G, namedInstance, MGraph.n]
      rw [hInEq]; exact hIn
    have hℓ : Chain.Ordered.LenInRange (max 0 cfg.Ψ) G ℓ₀ := by
      intro e he
      have hlog := (hlR e he).trans (le_max_right 0 cfg.Ψ)
      rw [abs_le] at hlog
      exact ⟨by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.1,
        by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.2⟩
    have hInit := Chain.Ordered.initialize_preserves_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
      hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk G ℓ₀ g₀ hGV hmG hnG hℓ
    have hLvl := Chain.Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
      hV.hTP hV.hγM₀ hV.hγk hInit.1 cfg.P.d le_rfl
    exact_mod_cast hLvl.2.2.1
  have hfmt : F.fmt.limbBits = 4 := rfl
  refine lastLevelRuntime_implements_mono
    (dryLastLevel_implements (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) _ Psc.sc inner _
      F.fmt (chain.G cfg.P.d) hfmt hconn hnm) ?_ ?_ ?_
  · exact packedLastLevelMultiplier_le_dryLastMultBound (le_trans hnm (Nat.add_le_add_right hmD 1)) hmD
  · have hsz := Nat.size_le_size (Nat.add_le_add_right hm 1)
    change (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * ((chain.G cfg.P.d).m + 1).size ≤
      (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * ((solverConnectedAugmented J).m + 1).size
    omega
  · intro _
    exact drySC_lastAllocLe_proved allocationCoefficient allocationDegree
      source J hJn hJm hCost hCap hw ℓ₀ g₀ hLen vc ec hcap

/-! ## 4. Unconditional discharge of `hInitConcrete` -/

/-- **Unconditional discharge of `hInitConcrete`** for `dryInnerCodeSel (dryInitCode (dryParamCode Psc))`
inside `dryLinkedProgram`. -/
theorem dryInitCode_hInitConcrete (Psc : DrySparseCorePieces)
    (coreCode selectCode termCode deepCode : SolverInnerSubCode)
    (openSz : DryOpenSizes) (hOpen : DryOpenSizeBounds openSz)
    (selSz : DrySelectRebuildSizes) (hSel : DrySelectRebuildSizeBounds selSz) :
    let inner := dryInnerCodeSel (dryInitCode (dryParamCode Psc)) coreCode selectCode termCode deepCode
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let s := dryInnerSizesWithSelect Psc openSz selSz source J
      OrdInitConcreteSpecW
        (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
        F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
        (k + Num.IPM.alphaExponent I.m V + 10)
        cfg Rcore (namedInstance I)
        (dryLinkedProgram dryWitnessUsed Psc.sc inner)
        (dryTailLay Psc.sc inner).initConcrete
        s.B_tree dryCapExp (concreteReadout2LimbMul dryWitnessUsed)
        (dryCapLimit dryWitnessUsed J)
        (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).wordExp
        s.initSpace' s.initFixed s.toolMul := by
  intro inner source J hJn hJm hCost hCap hw
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  let B := dryInnerBounds Psc openSz hOpen selSz hSel
  let hB := dryInnerBounds_hyp Psc openSz hOpen selSz hSel
  have hParam := dryParamProcs_discharges_hParam_at B hB
    (dryLinkedProgram dryWitnessUsed Psc.sc inner)
    (dryInitParamProc Psc.sc (dryParamCode Psc) coreCode selectCode termCode deepCode)
    (dryInnerCodeSel_hasParam Psc coreCode selectCode termCode deepCode)
    source J hJn hJm hCost hCap hw
  have hCoreImpl :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let limbMul := concreteReadout2LimbMul dryWitnessUsed
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let lay := dryTailLay Psc.sc inner
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ i < cfg.P.d,
          Rcore.Implements
            (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
              (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
            (dryLinkedProgram dryWitnessUsed Psc.sc inner) lay.scInit lay.scOp
            (sparseCoreOrdMachineContractKFBL F.fmt F.limbs (Expander.chosenL (cfg.P.M₀ ^ 2))
              cfg.T (chain.G i) cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ G.n (initTargetCap cfg G)
              dryCapExp (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)) ∧
          SparseCoreReadoutFootAt F.fmt F.limbs (Expander.chosenL (cfg.P.M₀ ^ 2))
            cfg.T (chain.G i) cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ G.n (initTargetCap cfg G)
            dryCapExp (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)
            Rcore (dryLinkedProgram dryWitnessUsed Psc.sc inner) lay.scOp := by
    intro I V k F cfg G limbMul Rcore lay ℓ₀ g₀ hLen chain i hi
    have hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ := by
      change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
        ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
      exact_mod_cast (by omega)
    have hlPos : ∀ e ∈ G.E, 0 < ℓ₀ e := fun e he => lt_of_lt_of_le (by positivity) (hLen e he).1
    have hlR : ∀ e ∈ G.E, |Real.log (ℓ₀ e)| ≤ cfg.Ψ := fun e he =>
      (abs_log_le_of_two_pow_bounds (hLen e he).1 (hLen e he).2).trans hEΨ
    have hnm : (chain.G i).n ≤ (chain.G i).m + 1 :=
      (drySolver_init_level_n_le_m_add_one J hJn hJm hCap1 g₀ ℓ₀ hlPos hlR i hi.le).2
    have hmle : (chain.G i).m ≤ I.m :=
      drySolver_init_level_m_le J hJn hJm hCap1 g₀ ℓ₀ hlPos hlR i hi.le
    exact drySC_coreKFBL Psc inner (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hJn hJm hCap1 hw
      i hi (chain.G i) hnm hmle
  have hLastImpl := drySC_hLastImpl_inner Psc inner
    (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel)
    source J hJn hJm hCost hCap hw
  have hCoreLenFits := drySC_hCoreLenFits_onGrid
    (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel)
    source J hJn hJm hCost hCap hw
  have hLastStretchFits := drySC_hLastStretchFits_Im
    (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel)
    source J hJn hJm hCost hCap hw
  exact dryInitCode_meets_spec Psc (dryParamCode Psc) coreCode selectCode termCode deepCode
    openSz hOpen selSz hSel source J hJn hJm hCap1 hw
    hParam hCoreImpl hLastImpl hCoreLenFits hLastStretchFits
    (fun i _ g l gr o h => le_of_eq (drySCAlloc_init_eq_dryCoreInitSpace Psc J i g l gr o _ _ h))

end MinCostFlow.Final.DryRun

end
