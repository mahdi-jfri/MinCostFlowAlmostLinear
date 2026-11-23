module

public import MinCostFlow.Final.AssemblyDryRunSCFitsBounds
public import MinCostFlow.Final.AssemblyDryRunSCInit
import MinCostFlow.MinRatio.WireInitBase
import MinCostFlow.Chain.Ordered.InitPreserves
import Mathlib.Tactic

/-!
# Chain-length and last-level stretch fixed-point fit bounds (`AssemblyDryRunSCFits`)

Proves the two fixed-point fit obligations of `initConcreteBody_meets_spec` / `DrySCInitBridgeHyps`
(`Final/AssemblyDryRunSC.lean`) for every valid dry-run circulation `J`:

1. **Per-level chain-length bounds (`drySC_chainLen_bounds`)**:
   Under `IPM.LengthsWithin G F.rangeExponent ℓ₀`, at every level `i ≤ cfg.P.d` and every edge
   `e ∈ (chain.G i).E`:
   * `(2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ chainLen ℓ₀ i e ≤ (2 : ℝ) ^ (F.rangeExponent + i * (3 * I.m.size + 12))`
     (and `≤ (2 : ℝ) ^ (2 * F.rangeExponent)` since `d * (3 * I.m.size + 12) ≤ F.rangeExponent`);
   * whenever `ℓ₀` lies on the `2 ^ (-F.fmt.precision)` fixed-point grid (`IsDyadicGrid G F.fmt.precision ℓ₀`),
     so does `chainLen ℓ₀ i` on `(chain.G i).E`.
2. **Core-length fits (`drySC_chainLen_lt_capacity_unconditional`, `drySC_hCoreLenFits_onGrid`)**:
   * Unconditionally under `IPM.LengthsWithin`, `0 < chainLen ℓ₀ (i + 1) e` and
     `2 * (chainLen ℓ₀ (i + 1) e * 2 ^ F.fmt.precision) < Num.capacity 4 F.limbs`.
   * Under `IsDyadicGrid G F.fmt.precision ℓ₀` (which `initConcreteBody_meets_spec` has from
     `len₀ = IPM.Machine.readVector mem lengths 4 L P m`), `∃ q : ℤ, Num.Fits 4 F.limbs q ∧
     (q : ℝ) / 2 ^ F.fmt.precision = chainLen ℓ₀ (i + 1) e`.
   * The form of `DrySCInitBridgeHyps.hCoreLenFits` without the premise `IsDyadicGrid` is false,
     so the field has this premise.
3. **Last-level stretch fits (`drySC_hLastStretchFits_of_le`, `drySC_hLastStretchFits_levelM`,
   `drySC_hLastStretchFits_Im`, `drySC_hLastStretchFits_actual`)**:
   Discharges `DrySCInitBridgeHyps.hLastStretchFits` verbatim for every `stretchP ≤ 100 * F.rangeExponent`,
   including the concrete last-level stretch precisions from `dryLastLevel_implements`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.IPM
  MinCostFlow.IPM.Machine MinCostFlow.SparseCore MinCostFlow.SparseCore.Program
  MinCostFlow.DynSpanner.Program MinCostFlow.Scaling MinCostFlow.MinRatio
  MinCostFlow.LastLevelProgram

/-! ## 1. Per-level chain-length range and dyadic-grid preservation -/

/-- For every valid dry-run circulation `J`, every length function `ℓ₀` in
`IPM.LengthsWithin (namedInstance I) F.rangeExponent ℓ₀`, and every level `i ≤ cfg.P.d`:
* `(chain.G i)` is a valid graph with vertices in `G.V` and edges in `G.E`;
* every edge `e ∈ (chain.G i).E` has `2 ^ (-E) ≤ chainLen ℓ₀ i e ≤ 2 ^ (E + i * (3 * I.m.size + 12))`;
* if `ℓ₀` lies on the `2 ^ (-P)` dyadic grid on `G.E`, then `chainLen ℓ₀ i` lies on the
  `2 ^ (-P)` dyadic grid on `(chain.G i).E`. -/
theorem drySC_chainLen_bounds
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    (ℓ₀ g₀ : ℕ → ℝ)
    (hLenWithin :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      IPM.LengthsWithin (namedInstance I) (ipmQualityRangeExponent I.m V k) ℓ₀) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let E := ipmQualityRangeExponent I.m V k
    let P := ipmQualityPrecision I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
      (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
    ∀ i ≤ cfg.P.d,
      (chain.G i).IsValid ∧
      (chain.G i).V ⊆ G.V ∧
      (chain.G i).E ⊆ G.E ∧
      (∀ e ∈ (chain.G i).E,
        (2 : ℝ) ^ (-(E : ℤ)) ≤ chain.toTreeChain.chainLen ℓ₀ i e ∧
        chain.toTreeChain.chainLen ℓ₀ i e ≤ (2 : ℝ) ^ (E + i * (3 * I.m.size + 12))) ∧
      (IsDyadicGrid G P ℓ₀ → IsDyadicGrid (chain.G i) P (chain.toTreeChain.chainLen ℓ₀ i)) := by
  intro I V k E P cfg G chain
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hGV : G.IsValid :=
    namedInstance_valid I (connectedInitialInstance_valid J.toInstance (V : ℤ) J.toInstance_valid)
  have hInEq : G.n = I.n := by simp [G, namedInstance, MGraph.n]
  have hImEq : G.m = I.m := namedInstance_m I
  have hImGeJm : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap).1
  have hIm1 : 1 ≤ I.m := by omega
  have hInLe : I.n ≤ 2 * I.m + 2 := by
    change J.n + 1 ≤ 2 * I.m + 2; omega
  obtain ⟨_, _, _, _, hInN₀⟩ := concreteCirculation_bounds_of
    (le_max_left dryWitnessUsed.M_thresh _) (le_max_right dryWitnessUsed.M_thresh _)
    (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap
  have hmG : G.m ≤ cfg.P.M₀ := by rw [hImEq]; exact le_max_left _ _
  have hnG : G.n ≤ cfg.N₀ := by rw [hInEq]; exact hInN₀
  have hEΨ : (E : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hlPos : ∀ e ∈ G.E, 0 < ℓ₀ e := fun e he =>
    lt_of_lt_of_le (by positivity) (hLenWithin e he).1
  have hℓRange : Chain.Ordered.LenInRange (max 0 cfg.Ψ) G ℓ₀ := by
    intro e he
    have hlog : |Real.log (ℓ₀ e)| ≤ max 0 cfg.Ψ :=
      ((abs_log_le_of_two_pow_bounds (hLenWithin e he).1 (hLenWithin e he).2).trans hEΨ).trans
        (le_max_right 0 cfg.Ψ)
    rw [abs_le] at hlog
    exact ⟨by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.1,
      by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.2⟩
  have hInit := Chain.Ordered.initialize_preserves_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hVcfg.hTP hVcfg.hLP hVcfg.hT hVcfg.hL hVcfg.hγM₀ hVcfg.hγk G ℓ₀ g₀ hGV hmG hnG hℓRange
  have hHolds := (hInit.1.toTreeChain_holds_noHidden hVcfg.hσ_mwu_mono hVcfg.hTP hVcfg.hLP
    hVcfg.hMWU hVcfg.hEmb hVcfg.hγM₀ hVcfg.hγk).1
  rw [hInit.2.2.1, hInit.2.2.2.1] at hHolds
  have hEq : ToolInitOrdEqOnE cfg.T :=
    sparseCoreBundleRestartToolMachWith_initOrdEqOnE _ _ _ _ _ _
  have hFacts := ordAlgorithm1_initialize_level_facts hEq cfg.L cfg.P
    (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀
  intro i
  induction i with
  | zero =>
    intro _
    have hG0 : chain.G 0 = G := hFacts.1
    rw [hG0]
    refine ⟨hGV, Finset.Subset.refl _, Finset.Subset.refl _, fun e he => ?_, fun hGrid => hGrid⟩
    simpa [TreeChain.chainLen] using hLenWithin e he
  | succ i ih =>
    intro hi_le
    have hi : i < cfg.P.d := by omega
    obtain ⟨hGiV, hGiSubV, hGiSubE, hGiLen, hGiGrid⟩ := ih (Nat.le_of_lt hi)
    obtain ⟨hbrLt, hLvl, _, hGeq⟩ := hHolds.2.2.2.2.1 i hi
    have hLSF := (hLvl (chain.bran i) hbrLt).1
    have hSp := (hLvl (chain.bran i) hbrLt).2
    have hGsuccV : (chain.G (i + 1)).IsValid := by
      have hGe : chain.G (i + 1) = chain.toTreeChain.S i (chain.bran i) := hGeq
      rw [hGe]
      intro f hf
      have hfCore : f ∈ (coreGraph (chain.G i) (chain.toTreeChain.lsfs i (chain.bran i))).E :=
        hSp.1.2.1 hf
      have hfGi : f ∈ (chain.G i).E := (Finset.mem_sdiff.mp hfCore).1
      have hEnd : (chain.toTreeChain.S i (chain.bran i)).tail f =
          (coreGraph (chain.G i) (chain.toTreeChain.lsfs i (chain.bran i))).tail f ∧
          (chain.toTreeChain.S i (chain.bran i)).head f =
          (coreGraph (chain.G i) (chain.toTreeChain.lsfs i (chain.bran i))).head f :=
        hSp.1.2.2 f hf
      rw [hEnd.1, hEnd.2]
      refine ⟨hSp.2.1.1 ?_, hSp.2.1.1 ?_⟩
      · exact (LSF.rootedForest_root_spec hLSF.2.1 (hGiV f hfGi).1).1
      · exact (LSF.rootedForest_root_spec hLSF.2.1 (hGiV f hfGi).2).1
    have hSubV : (chain.G (i + 1)).V ⊆ (chain.G i).V := by
      have h1 : (chain.G (i + 1)).V ⊆ (coreGraph (chain.G i) (chain.toTreeChain.lsfs i (chain.bran i))).V := by
        have : chain.G (i + 1) = chain.toTreeChain.S i (chain.bran i) := hGeq
        rw [this]; exact hSp.1.1
      exact h1.trans hLSF.2.1.2.2.1
    have hSubE : (chain.G (i + 1)).E ⊆ (chain.G i).E := by
      have h1 : (chain.G (i + 1)).E ⊆ (coreGraph (chain.G i) (chain.toTreeChain.lsfs i (chain.bran i))).E := by
        have : chain.G (i + 1) = chain.toTreeChain.S i (chain.bran i) := hGeq
        rw [this]; exact hSp.1.2.1
      exact h1.trans Finset.sdiff_subset
    have hGiN : (chain.G i).n ≤ 2 * I.m + 2 :=
      (Finset.card_le_card hGiSubV).trans (by rw [show G.V.card = G.n from rfl, hInEq]; exact hInLe)
    have hGiM : (chain.G i).m ≤ I.m :=
      (Finset.card_le_card hGiSubE).trans (by rw [show G.E.card = G.m from rfl, hImEq])
    have hFactsI := hFacts.2.2.2.2 i hi
    have hBr0 : chain.bran i = 0 := hFactsI.1
    have hScEq := hFactsI.2.2.2.2
    have hStep : ∀ e ∈ (chain.G i).E,
        chain.toTreeChain.chainLen ℓ₀ i e ≤ chain.toTreeChain.chainLen ℓ₀ (i + 1) e ∧
        chain.toTreeChain.chainLen ℓ₀ (i + 1) e ≤
          (2 : ℝ) ^ (E + (i + 1) * (3 * I.m.size + 12)) ∧
        (IsDyadicGrid (chain.G i) P (chain.toTreeChain.chainLen ℓ₀ i) →
          ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P = chain.toTreeChain.chainLen ℓ₀ (i + 1) e) := by
      intro e he
      have hGiNe : (chain.G i).V.Nonempty := ⟨(chain.G i).tail e, (hGiV e he).1⟩
      have hwstrEq : (chain.toTreeChain.activeLSF i).wstr =
          (initCompLSFWith (dryLSFInitUsed (ipmQualityLimbs I.m V k) P)
            (chain.G i) (chain.toTreeChain.chainLen ℓ₀ i) cfg.P.k 0).lsf.wstr := by
        have hact : chain.toTreeChain.activeLSF i = cfg.T.lsfs (chain.scState i) 0 := by
          simp [TreeChain.activeLSF, ChainState.toTreeChain, hi, hBr0]
        rw [hact, hScEq]
        have hcs :
            cfg.T.lsfs
                (cfg.T.initOrd cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ (chain.G i)
                  (fun e => if e ∈ (chain.G i).E then chain.toTreeChain.chainLen ℓ₀ i e else 0)
                  (fun e => if e ∈ (chain.G i).E then
                    (if i = 0 then g₀ e else chain.toTreeChain.chainLen ℓ₀ i e) else 0)
                  (chain.levelOrd i)) 0 =
            (initCompLSFWith (dryLSFInitUsed (ipmQualityLimbs I.m V k) P)
              (chain.G i) (fun e => if e ∈ (chain.G i).E then chain.toTreeChain.chainLen ℓ₀ i e else 0)
              cfg.P.k 0).lsf := by
          set st := initBundleCoreWithParams
            (dryLSFInitUsed (ipmQualityLimbs I.m V k) P)
            (Expander.chosenL (max I.m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2))
            (fun _ => canonicalSparsify sparsifyImplUsed)
            (canonicalSparsifyParams sparsifyImplUsed) (dsAmortConst sparsifyImplUsed)
            cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ (chain.G i)
            (fun e => if e ∈ (chain.G i).E then chain.toTreeChain.chainLen ℓ₀ i e else 0)
            (chain.levelOrd i)
          have hne : st.isNonempty = true := by
            dsimp only [st, initBundleCoreWithParams]
            exact decide_eq_true_eq.mpr hGiNe
          change (if st.isNonempty then (st.trees 0).cs.lsf else emptyLSF) = _
          rw [hne]
          rfl
        rw [hcs, initCompLSFWith_eq_of_eq_on_E _ _ (ℓ₁ := chain.toTreeChain.chainLen ℓ₀ i)
          (fun a ha => by simp [ha])]
      have hBnn : (0 : ℝ) ≤ (2 : ℝ) ^ (E + i * (3 * I.m.size + 12)) := by positivity
      have hℓi : ∀ f ∈ (chain.G i).E, 0 < chain.toTreeChain.chainLen ℓ₀ i f ∧
          chain.toTreeChain.chainLen ℓ₀ i f ≤ (2 : ℝ) ^ (E + i * (3 * I.m.size + 12)) :=
        fun f hf => ⟨lt_of_lt_of_le (by positivity) (hGiLen f hf).1, (hGiLen f hf).2⟩
      obtain ⟨hlo, hhi, hgr⟩ := initCompLSFWith_dryLSFInitUsed_wstr_mul
        (ipmQualityLimbs I.m V k) P I.m hIm1 hGiV hGiN hGiM hBnn hℓi cfg.P.hk cfg.P.hk he
      have hcl : chain.toTreeChain.chainLen ℓ₀ (i + 1) e =
          (initCompLSFWith (dryLSFInitUsed (ipmQualityLimbs I.m V k) P)
            (chain.G i) (chain.toTreeChain.chainLen ℓ₀ i) cfg.P.k 0).lsf.wstr e *
          chain.toTreeChain.chainLen ℓ₀ i e := by
        simp only [TreeChain.chainLen, coreLen, hwstrEq]
      rw [hcl]
      refine ⟨hlo, ?_, hgr P⟩
      calc _ ≤ (2 : ℝ) ^ (3 * I.m.size + 12) * (2 : ℝ) ^ (E + i * (3 * I.m.size + 12)) := hhi
        _ = (2 : ℝ) ^ ((3 * I.m.size + 12) + (E + i * (3 * I.m.size + 12))) := (pow_add _ _ _).symm
        _ = (2 : ℝ) ^ (E + (i + 1) * (3 * I.m.size + 12)) := by congr 1; ring
    refine ⟨hGsuccV, hSubV.trans hGiSubV, hSubE.trans hGiSubE, fun e he => ?_, fun hGrid e he => ?_⟩
    · have he_i : e ∈ (chain.G i).E := hSubE he
      obtain ⟨hlo, hhi, _⟩ := hStep e he_i
      exact ⟨(hGiLen e he_i).1.trans hlo, hhi⟩
    · exact (hStep e (hSubE he)).2.2 (hGiGrid hGrid)

/-! ## 2. Core-length capacity bound and repaired `hCoreLenFits` -/

/-- Unconditional magnitude bound for every dry-run input and every `ℓ₀` in `IPM.LengthsWithin`:
every chain length `chainLen ℓ₀ (i + 1) e` at level `i < d` is positive and satisfies
`2 * (chainLen ℓ₀ (i + 1) e * 2 ^ F.fmt.precision) < Num.capacity 4 F.limbs`. -/
theorem drySC_chainLen_lt_capacity_unconditional
    (allocationCoefficient allocationDegree : ℕ) :
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun _source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ i < cfg.P.d, ∀ e ∈ (chain.G (i + 1)).E,
          0 < chain.toTreeChain.chainLen ℓ₀ (i + 1) e ∧
          2 * (chain.toTreeChain.chainLen ℓ₀ (i + 1) e * (2 : ℝ) ^ F.fmt.precision) <
            (Num.capacity 4 F.limbs : ℝ) := by
  intro _source J hJn hJm _hCost hCap hw
  dsimp only
  intro ℓ₀ g₀ hLenWithin i hi e he
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let k := cappedQualityExponent threshold A I.m
  let F := ipmQualityMinRatioFormat I.m V k hw
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let G := namedInstance I
  let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
    (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
  have hIm1 : 1 ≤ I.m :=
    Nat.lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm (fun e => (hCap e).1)).1
  have hbd := drySC_chainLen_bounds J hJn hJm (fun e => (hCap e).1) ℓ₀ g₀ hLenWithin (i + 1) hi
  obtain ⟨hlo, hhi⟩ := hbd.2.2.2.1 e he
  have hExp : (i + 1) * (3 * I.m.size + 12) ≤ F.rangeExponent := by
    have h1 : (i + 1) * (3 * I.m.size + 12) ≤ cfg.P.d * (3 * I.m.size + 12) :=
      Nat.mul_le_mul_right _ hi
    exact h1.trans (chainLen_exponent_le_rangeExponent I.m V A hIm1 cfg.P.hM₀)
  have h2E : chain.toTreeChain.chainLen ℓ₀ (i + 1) e ≤ (2 : ℝ) ^ (2 * F.rangeExponent) := by
    have hsum : F.rangeExponent + (i + 1) * (3 * I.m.size + 12) ≤ 2 * F.rangeExponent := by
      have := Nat.add_le_add_left hExp F.rangeExponent
      rwa [← two_mul] at this
    exact hhi.trans (pow_le_pow_right₀ (by norm_num) hsum)
  have hcap := coreLen_pow_lt_capacity I.m V k
  refine ⟨lt_of_lt_of_le (by positivity) hlo, ?_⟩
  calc 2 * (chain.toTreeChain.chainLen ℓ₀ (i + 1) e * (2 : ℝ) ^ F.fmt.precision)
      ≤ 2 * ((2 : ℝ) ^ (2 * F.rangeExponent) * (2 : ℝ) ^ F.fmt.precision) := by
        gcongr
    _ = (2 : ℝ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) := by
        rw [pow_succ, pow_add]; ring
    _ < (Num.capacity 4 F.limbs : ℝ) := hcap

/-- **Repaired `hCoreLenFits` for `DrySCInitBridgeHyps` / `initConcreteBody_meets_spec`:**
For every valid dry-run input `(source, J)`, every `ℓ₀` satisfying `IPM.LengthsWithin G F.rangeExponent ℓ₀`
and lying on the `2 ^ (-F.fmt.precision)` fixed-point grid (`IsDyadicGrid G F.fmt.precision ℓ₀`),
every level `i < cfg.P.d`, and every edge `e ∈ (chain.G (i + 1)).E`, `chainLen ℓ₀ (i + 1) e` is
represented exactly by a signed integer `q` fitting in `Num.Fits 4 F.limbs`.

Note: `initConcreteBody_meets_spec` calls `hCoreLenFits` only on
`len₀ = IPM.Machine.readVector mem lengths 4 L P m`, which satisfies `IsDyadicGrid G P len₀`
by definition of `Num.fixVal`. -/
theorem drySC_hCoreLenFits_onGrid
    (allocationCoefficient allocationDegree : ℕ) :
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun _source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        IsDyadicGrid G F.fmt.precision ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ i < cfg.P.d, ∀ e ∈ (chain.G (i + 1)).E,
          ∃ q : ℤ, Num.Fits 4 F.limbs q ∧ (q : ℝ) / (2 : ℝ) ^ F.fmt.precision =
            chain.toTreeChain.chainLen ℓ₀ (i + 1) e := by
  intro source J hJn hJm hCost hCap hw
  dsimp only
  intro ℓ₀ g₀ hLenWithin hGrid i hi e he
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let F := ipmQualityMinRatioFormat I.m V k hw
  have hbd := drySC_chainLen_bounds J hJn hJm (fun e => (hCap e).1) ℓ₀ g₀ hLenWithin (i + 1) hi
  obtain ⟨q, hq⟩ := hbd.2.2.2.2 hGrid e he
  obtain ⟨hpos, hltCap⟩ := drySC_chainLen_lt_capacity_unconditional
    allocationCoefficient allocationDegree source J hJn hJm hCost hCap hw ℓ₀ g₀ hLenWithin i hi e he
  have h2P_pos : (0 : ℝ) < (2 : ℝ) ^ F.fmt.precision := by positivity
  have hqR : (q : ℝ) = (Chain.Ordered.algorithm1_initialize
      (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).L
      (concreteCirculationCfgWithLast dryWitnessUsed J).P
      (levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
        (concreteCirculationCfgWithLast dryWitnessUsed J).P)
      (concreteCirculationCfgWithLast dryWitnessUsed J).N₀
      (namedInstance I) ℓ₀ g₀).1.toTreeChain.chainLen ℓ₀ (i + 1) e * (2 : ℝ) ^ F.fmt.precision :=
    (div_eq_iff h2P_pos.ne').mp hq
  have hqPos : (0 : ℤ) ≤ q := by
    have : (0 : ℝ) ≤ (q : ℝ) := by rw [hqR]; positivity
    exact_mod_cast this
  have h2qLt : 2 * q < (Num.capacity 4 F.limbs : ℤ) := by
    have hreal : ((2 * q : ℤ) : ℝ) < ((Num.capacity 4 F.limbs : ℤ) : ℝ) := by
      push_cast; rw [hqR]; exact hltCap
    exact_mod_cast hreal
  refine ⟨q, ⟨?_, h2qLt⟩, hq⟩
  have hcap0 : (0 : ℤ) ≤ (Num.capacity 4 F.limbs : ℤ) := Int.natCast_nonneg _
  omega

/-! ## 3. Last-level stretch fits (`DrySCInitBridgeHyps.hLastStretchFits`) -/

/-- **General `hLastStretchFits` in the exact form of `DrySCInitBridgeHyps`:**
holds for every `stretchP : Circulation → Circulation → ℕ` bounded by `100 * F.rangeExponent`
on every dry-run input. -/
theorem drySC_hLastStretchFits_of_le
    (allocationCoefficient allocationDegree : ℕ)
    (stretchP : Circulation → Circulation → ℕ)
    (hStretchLe : ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      stretchP source J ≤ 100 * F.rangeExponent) :
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ e ∈ (chain.G cfg.P.d).E,
          2 * (2 : ℝ) ^ stretchP source J *
            lastLevelStretchBound (chain.G cfg.P.d) (chain.toTreeChain.chainLen ℓ₀ cfg.P.d) e <
          Num.capacity 4 F.limbs := by
  intro source J hJn hJm hCost hCap hw
  dsimp only
  intro ℓ₀ g₀ hLenWithin e he
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let k := cappedQualityExponent threshold A I.m
  let F := ipmQualityMinRatioFormat I.m V k hw
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let G := namedInstance I
  let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
    (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
  have hIm1 : 1 ≤ I.m :=
    Nat.lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm (fun e => (hCap e).1)).1
  have hbd := drySC_chainLen_bounds J hJn hJm (fun e => (hCap e).1) ℓ₀ g₀ hLenWithin cfg.P.d le_rfl
  have hExp : cfg.P.d * (3 * I.m.size + 12) ≤ F.rangeExponent :=
    chainLen_exponent_le_rangeExponent I.m V A hIm1 cfg.P.hM₀
  have hLenUpper : ∀ f ∈ (chain.G cfg.P.d).E,
      chain.toTreeChain.chainLen ℓ₀ cfg.P.d f ≤ (2 : ℝ) ^ (2 * F.rangeExponent) := by
    intro f hf
    have hsum : F.rangeExponent + cfg.P.d * (3 * I.m.size + 12) ≤ 2 * F.rangeExponent := by
      have := Nat.add_le_add_left hExp F.rangeExponent
      rwa [← two_mul] at this
    exact (hbd.2.2.2.1 f hf).2.trans (pow_le_pow_right₀ (by norm_num) hsum)
  have hLenLower : (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ chain.toTreeChain.chainLen ℓ₀ cfg.P.d e :=
    (hbd.2.2.2.1 e he).1
  have hCardLe : (chain.G cfg.P.d).E.card ≤ 2 ^ I.m.size := by
    have h1 : (chain.G cfg.P.d).E.card ≤ G.E.card := Finset.card_le_card hbd.2.2.1
    have h2 : G.E.card = I.m := namedInstance_m I
    exact (h1.trans (le_of_eq h2)).trans (Nat.lt_size_self I.m).le
  have hSumLe : ∑ f ∈ (chain.G cfg.P.d).E, chain.toTreeChain.chainLen ℓ₀ cfg.P.d f ≤
      (2 : ℝ) ^ I.m.size * (2 : ℝ) ^ (2 * F.rangeExponent) := by
    calc ∑ f ∈ (chain.G cfg.P.d).E, chain.toTreeChain.chainLen ℓ₀ cfg.P.d f
        ≤ ∑ _f ∈ (chain.G cfg.P.d).E, (2 : ℝ) ^ (2 * F.rangeExponent) :=
          Finset.sum_le_sum hLenUpper
      _ = ((chain.G cfg.P.d).E.card : ℝ) * (2 : ℝ) ^ (2 * F.rangeExponent) := by simp
      _ ≤ (2 : ℝ) ^ I.m.size * (2 : ℝ) ^ (2 * F.rangeExponent) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hCardLe) (by positivity)
  have hDivLe : (∑ f ∈ (chain.G cfg.P.d).E, chain.toTreeChain.chainLen ℓ₀ cfg.P.d f) /
      chain.toTreeChain.chainLen ℓ₀ cfg.P.d e ≤
      (2 : ℝ) ^ (3 * F.rangeExponent + I.m.size) := by
    have h2neg : (0 : ℝ) < (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) := by positivity
    have hsum_nn : 0 ≤ ∑ f ∈ (chain.G cfg.P.d).E, chain.toTreeChain.chainLen ℓ₀ cfg.P.d f :=
      Finset.sum_nonneg fun f hf => le_trans h2neg.le (hbd.2.2.2.1 f hf).1
    calc (∑ f ∈ (chain.G cfg.P.d).E, chain.toTreeChain.chainLen ℓ₀ cfg.P.d f) /
          chain.toTreeChain.chainLen ℓ₀ cfg.P.d e
        ≤ ((2 : ℝ) ^ I.m.size * (2 : ℝ) ^ (2 * F.rangeExponent)) /
            (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) :=
          div_le_div₀ (by positivity) hSumLe h2neg hLenLower
      _ = (2 : ℝ) ^ I.m.size * (2 : ℝ) ^ (2 * F.rangeExponent) * (2 : ℝ) ^ F.rangeExponent := by
          rw [zpow_neg, zpow_natCast, div_inv_eq_mul]
      _ = (2 : ℝ) ^ (3 * F.rangeExponent + I.m.size) := by
          rw [← pow_add, ← pow_add]
          exact congrArg ((2 : ℝ) ^ ·)
            ((fun a b : ℕ => show a + 2 * b + b = 3 * b + a by omega) I.m.size F.rangeExponent)
  have hBoundLe : lastLevelStretchBound (chain.G cfg.P.d)
      (chain.toTreeChain.chainLen ℓ₀ cfg.P.d) e ≤
      (2 : ℝ) ^ (3 * F.rangeExponent + I.m.size + 1) := by
    unfold lastLevelStretchBound
    have h1 : 1 ≤ 3 * F.rangeExponent + I.m.size :=
      Nat.le_trans (Nat.size_pos.mpr hIm1) (Nat.le_add_left _ _)
    have h2le : (2 : ℝ) ≤ (2 : ℝ) ^ (3 * F.rangeExponent + I.m.size) := by
      simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h1)
    have hpow : (2 : ℝ) ^ (3 * F.rangeExponent + I.m.size) +
        (2 : ℝ) ^ (3 * F.rangeExponent + I.m.size) =
        (2 : ℝ) ^ (3 * F.rangeExponent + I.m.size + 1) := by
      rw [pow_succ]; ring
    exact (add_le_add h2le hDivLe).trans_eq hpow
  have hst := hStretchLe source J hJn hJm hCost hCap hw
  have hCap := lastStretch_pow_lt_capacity I.m V k (stretchP source J) hst
  calc 2 * (2 : ℝ) ^ stretchP source J *
        lastLevelStretchBound (chain.G cfg.P.d) (chain.toTreeChain.chainLen ℓ₀ cfg.P.d) e
      ≤ 2 * (2 : ℝ) ^ stretchP source J * (2 : ℝ) ^ (3 * F.rangeExponent + I.m.size + 1) := by
        gcongr
    _ = (2 : ℝ) ^ (stretchP source J + 3 * F.rangeExponent + I.m.size + 2) := by
        rw [show stretchP source J + 3 * F.rangeExponent + I.m.size + 2 =
          1 + stretchP source J + (3 * F.rangeExponent + I.m.size + 1) by ring]
        simp only [pow_add, pow_one]
    _ < (Num.capacity 4 F.limbs : ℝ) := hCap

/-- Concrete `DrySCInitBridgeHyps.hLastStretchFits` for the `levelM d`-based stretch precision
`(1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (levelM cfg.TP cfg.P cfg.P.d + 1).size`. -/
theorem drySC_hLastStretchFits_levelM (allocationCoefficient allocationDegree : ℕ) :
    let stretchP : Circulation → Circulation → ℕ := fun _ J =>
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (levelM cfg.TP cfg.P cfg.P.d + 1).size
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ e ∈ (chain.G cfg.P.d).E,
          2 * (2 : ℝ) ^ stretchP source J *
            lastLevelStretchBound (chain.G cfg.P.d) (chain.toTreeChain.chainLen ℓ₀ cfg.P.d) e <
          Num.capacity 4 F.limbs := by
  intro stretchP
  refine drySC_hLastStretchFits_of_le allocationCoefficient allocationDegree stretchP ?_
  intro _source J hJn hJm _hCost hCap _hw
  dsimp only [stretchP, ipmQualityMinRatioFormat]
  have hmax := dryLastStretchP_le_rangeExponent J hJn hJm (fun e => (hCap e).1)
  have hmono : (levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
      (concreteCirculationCfgWithLast dryWitnessUsed J).P
      (concreteCirculationCfgWithLast dryWitnessUsed J).P.d + 1).size ≤
      (max (solverConnectedAugmented J).m (levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
        (concreteCirculationCfgWithLast dryWitnessUsed J).P
        (concreteCirculationCfgWithLast dryWitnessUsed J).P.d) + 1).size :=
    Nat.size_le_size (Nat.add_le_add_right (le_max_right _ _) 1)
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hmono) _).trans hmax

/-- Concrete `DrySCInitBridgeHyps.hLastStretchFits` for the `I.m`-based stretch precision
`(1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * ((solverConnectedAugmented J).m + 1).size`. -/
theorem drySC_hLastStretchFits_Im (allocationCoefficient allocationDegree : ℕ) :
    let stretchP : Circulation → Circulation → ℕ := fun _ J =>
      (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * ((solverConnectedAugmented J).m + 1).size
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ e ∈ (chain.G cfg.P.d).E,
          2 * (2 : ℝ) ^ stretchP source J *
            lastLevelStretchBound (chain.G cfg.P.d) (chain.toTreeChain.chainLen ℓ₀ cfg.P.d) e <
          Num.capacity 4 F.limbs := by
  intro stretchP
  refine drySC_hLastStretchFits_of_le allocationCoefficient allocationDegree stretchP ?_
  intro _source J hJn hJm _hCost hCap _hw
  dsimp only [stretchP, ipmQualityMinRatioFormat]
  have hmax := dryLastStretchP_le_rangeExponent J hJn hJm (fun e => (hCap e).1)
  have hmono : ((solverConnectedAugmented J).m + 1).size ≤
      (max (solverConnectedAugmented J).m (levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
        (concreteCirculationCfgWithLast dryWitnessUsed J).P
        (concreteCirculationCfgWithLast dryWitnessUsed J).P.d) + 1).size :=
    Nat.size_le_size (Nat.add_le_add_right (le_max_left _ _) 1)
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hmono) _).trans hmax

/-- Concrete `hLastStretchFits` directly at the exact per-graph stretch precision of
`dryLastLevel_implements`: `(1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * ((chain.G cfg.P.d).m + 1).size`. -/
theorem drySC_hLastStretchFits_actual (allocationCoefficient allocationDegree : ℕ) :
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun _source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ e ∈ (chain.G cfg.P.d).E,
          2 * (2 : ℝ) ^ ((1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * ((chain.G cfg.P.d).m + 1).size) *
            lastLevelStretchBound (chain.G cfg.P.d) (chain.toTreeChain.chainLen ℓ₀ cfg.P.d) e <
          Num.capacity 4 F.limbs := by
  intro source J hJn hJm hCost hCap hw
  dsimp only
  intro ℓ₀ g₀ hLenWithin e he
  let I := solverConnectedAugmented J
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
    (levelM cfg.TP cfg.P) cfg.N₀ (namedInstance I) ℓ₀ g₀).1
  have hIm := drySC_hLastStretchFits_Im allocationCoefficient allocationDegree
    source J hJn hJm hCost hCap hw ℓ₀ g₀ hLenWithin e he
  have hbd := drySC_chainLen_bounds J hJn hJm (fun e => (hCap e).1) ℓ₀ g₀ hLenWithin cfg.P.d le_rfl
  have hmLe : (chain.G cfg.P.d).m ≤ I.m :=
    (Finset.card_le_card hbd.2.2.1).trans (le_of_eq (namedInstance_m I))
  have hszLe : (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * ((chain.G cfg.P.d).m + 1).size ≤
      (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (I.m + 1).size :=
    Nat.add_le_add_left (Nat.mul_le_mul_left 3 (Nat.size_le_size (Nat.add_le_add_right hmLe 1))) _
  have hlb_nn : 0 ≤ lastLevelStretchBound (chain.G cfg.P.d) (chain.toTreeChain.chainLen ℓ₀ cfg.P.d) e := by
    unfold lastLevelStretchBound
    have hpos : 0 < chain.toTreeChain.chainLen ℓ₀ cfg.P.d e :=
      lt_of_lt_of_le (by positivity) (hbd.2.2.2.1 e he).1
    have hsum_nn : 0 ≤ ∑ f ∈ (chain.G cfg.P.d).E, chain.toTreeChain.chainLen ℓ₀ cfg.P.d f :=
      Finset.sum_nonneg fun f hf => le_trans (by positivity) (hbd.2.2.2.1 f hf).1
    have hdiv_nn : 0 ≤ (∑ f ∈ (chain.G cfg.P.d).E, chain.toTreeChain.chainLen ℓ₀ cfg.P.d f) /
        chain.toTreeChain.chainLen ℓ₀ cfg.P.d e := div_nonneg hsum_nn hpos.le
    linarith
  have hpow : (2 : ℝ) ^ ((1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * ((chain.G cfg.P.d).m + 1).size) ≤
      (2 : ℝ) ^ ((1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (I.m + 1).size) :=
    pow_le_pow_right₀ (by norm_num) hszLe
  have hle : 2 * (2 : ℝ) ^ ((1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * ((chain.G cfg.P.d).m + 1).size) *
      lastLevelStretchBound (chain.G cfg.P.d) (chain.toTreeChain.chainLen ℓ₀ cfg.P.d) e ≤
      2 * (2 : ℝ) ^ ((1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (I.m + 1).size) *
      lastLevelStretchBound (chain.G cfg.P.d) (chain.toTreeChain.chainLen ℓ₀ cfg.P.d) e :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow zero_le_two) hlb_nn
  exact lt_of_le_of_lt hle hIm

end MinCostFlow.Final.DryRun
