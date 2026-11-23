module

public import MinCostFlow.Final.AssemblyDryRunSCFits
public import MinCostFlow.MinRatio.ShiftDeepModelFacts
import Mathlib.Tactic

/-!
# Dry-run tool and chain-length dyadic-grid facts for the deep shift (`AssemblyDryRunSCDeepGrid`)

`Psc`-free core of `Final/AssemblyDryRunSCDeepFacts.lean`, placed strictly below
`Final/AssemblyDryRunSC.lean` so `AssemblyDryRunSC.lean` and `AssemblyDryRunSCDeepUpdate.lean` can
use `DryChainLenGridInv`, `dryChainLenGridInv_init`, `dryChainLenGridInv_shift`, and
`dryShiftDeepModelInv_of_wordBound` without an import cycle.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio LastLevelProgram DynSpanner.Program

/-- Hypothesis 1 of `shiftDeepModelInv_of_loopInv`: the dry run's sparse-core tool satisfies
`ToolCostMono`. -/
theorem drySC_toolCostMono (J : Circulation) :
    ToolCostMono (concreteCirculationCfgWithLast dryWitnessUsed J).T :=
  sparseCoreBundleRestartToolMachWith_costMono _ _ _ _ _ _

/-- Hypothesis 2 of `shiftDeepModelInv_of_loopInv`: the dry run's last-level tool satisfies
`LastLevelBuildEqOnE`. -/
theorem drySC_lastLevelBuildEqOnE (J : Circulation) :
    LastLevelBuildEqOnE (concreteCirculationCfgWithLast dryWitnessUsed J).L :=
  fixedPointLastLevelTool_buildEqOnE _ _

/-- Per-level chain-length range and `2 ^ (-P)` dyadic-grid invariant for a chain of the dry run,
including every branch `b < cfg.P.k` at every non-terminal level `i < cfg.P.d`. -/
@[expose] def DryChainLenGridInv (J : Circulation)
    (ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P) : Prop :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let E := ipmQualityRangeExponent I.m V k
  let P := ipmQualityPrecision I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  (ch.G 0).m ≤ I.m ∧ (ch.G 0).n ≤ 2 * I.m + 2 ∧
  (∀ i ≤ cfg.P.d,
    (∀ e ∈ (ch.G i).E,
      (2 : ℝ) ^ (-(E : ℤ)) ≤ ch.toTreeChain.chainLen ch.ℓ i e ∧
      ch.toTreeChain.chainLen ch.ℓ i e ≤ (2 : ℝ) ^ (E + i * (3 * I.m.size + 12))) ∧
    IsDyadicGrid (ch.G i) P (ch.toTreeChain.chainLen ch.ℓ i)) ∧
  (∀ i < cfg.P.d, ∀ b < cfg.P.k, ∀ e ∈ (ch.G i).E,
    1 ≤ (cfg.T.lsfs (ch.scState i) b).wstr e ∧
    (cfg.T.lsfs (ch.scState i) b).wstr e * ch.toTreeChain.chainLen ch.ℓ i e ≤
      (2 : ℝ) ^ (E + (i + 1) * (3 * I.m.size + 12)) ∧
    ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P =
      (cfg.T.lsfs (ch.scState i) b).wstr e * ch.toTreeChain.chainLen ch.ℓ i e) ∧
  (∃ (Gd : MGraph) (ℓd : ℕ → ℝ), Gd.m ≤ I.m ∧ (ch.lastK, ch.lastLSFs) = cfg.L.build Gd ℓd)

theorem dryInitOrd_wstr_bounds (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {M N i b e : ℕ} {G : MGraph} {ℓ g : ℕ → ℝ} {ord : ℕ → List Bundle.End}
    (hGV : G.IsValid) (hGn : G.n ≤ 2 * (solverConnectedAugmented J).m + 2)
    (hGm : G.m ≤ (solverConnectedAugmented J).m)
    (hLen :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let E := ipmQualityRangeExponent I.m V k
      ∀ f ∈ G.E, (2 : ℝ) ^ (-(E : ℤ)) ≤ ℓ f ∧ ℓ f ≤ (2 : ℝ) ^ (E + i * (3 * I.m.size + 12)))
    (hGrid :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      IsDyadicGrid G (ipmQualityPrecision I.m V k) ℓ)
    (hb : b < (concreteCirculationCfgWithLast dryWitnessUsed J).P.k) (he : e ∈ G.E) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let E := ipmQualityRangeExponent I.m V k
    let P := ipmQualityPrecision I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let sc := cfg.T.initOrd cfg.P.k M N G ℓ g ord
    1 ≤ (cfg.T.lsfs sc b).wstr e ∧
    (cfg.T.lsfs sc b).wstr e * ℓ e ≤ (2 : ℝ) ^ (E + (i + 1) * (3 * I.m.size + 12)) ∧
    ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P = (cfg.T.lsfs sc b).wstr e * ℓ e := by
  intro I V k E P cfg sc
  have hIm1 : 1 ≤ I.m :=
    Nat.lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  have hGne : G.V.Nonempty := ⟨G.tail e, (hGV e he).1⟩
  have hcs : cfg.T.lsfs sc b =
      (initCompLSFWith (dryLSFInitUsed (ipmQualityLimbs I.m V k) P) G ℓ cfg.P.k b).lsf := by
    have hne : sc.isNonempty = true := by
      dsimp only [sc, cfg, concreteCirculationCfgWithLast, concreteCirculationCfgOfDims,
        Chain.Ordered.concreteAlg2CfgWithLast, dryWitnessUsed, sparseCoreBundleRestartToolMachWith,
        initBundleCoreWithParams]
      exact decide_eq_true_eq.mpr hGne
    change (if sc.isNonempty then (sc.trees b).cs.lsf else emptyLSF) = _
    rw [hne]
    rfl
  have hBnn : (0 : ℝ) ≤ (2 : ℝ) ^ (E + i * (3 * I.m.size + 12)) := by positivity
  have hℓ : ∀ f ∈ G.E, 0 < ℓ f ∧ ℓ f ≤ (2 : ℝ) ^ (E + i * (3 * I.m.size + 12)) := fun f hf =>
    ⟨lt_of_lt_of_le (by positivity) (hLen f hf).1, (hLen f hf).2⟩
  obtain ⟨hlo, hhi, hgr⟩ := initCompLSFWith_dryLSFInitUsed_wstr_mul
    (ipmQualityLimbs I.m V k) P I.m hIm1 hGV hGn hGm hBnn hℓ cfg.P.hk hb he
  rw [hcs]
  have hℓe_pos : 0 < ℓ e := (hℓ e he).1
  refine ⟨?_, ?_, hgr P hGrid⟩
  · exact le_of_mul_le_mul_right (by simpa [one_mul] using hlo) hℓe_pos
  · calc (initCompLSFWith (dryLSFInitUsed (ipmQualityLimbs I.m V k) P) G ℓ cfg.P.k b).lsf.wstr e * ℓ e
        ≤ (2 : ℝ) ^ (3 * I.m.size + 12) * (2 : ℝ) ^ (E + i * (3 * I.m.size + 12)) := hhi
      _ = (2 : ℝ) ^ ((3 * I.m.size + 12) + (E + i * (3 * I.m.size + 12))) := (pow_add _ _ _).symm
      _ = (2 : ℝ) ^ (E + (i + 1) * (3 * I.m.size + 12)) := by congr 1; ring

theorem chainInv_G_E_subset_G0 {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {ch : ChainState cfg.T cfg.P}
    (hInv : Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch) :
    ∀ i ≤ cfg.P.d, (ch.G i).E ⊆ (ch.G 0).E := by
  intro i
  induction i with
  | zero => intro _; exact Finset.Subset.refl _
  | succ i ih =>
    intro hi
    exact (chainInv_G_succ_E_subset hV hInv hi).trans (ih (Nat.le_of_lt hi))

/-- `DryChainLenGridInv` holds on the initial chain built by `algorithm1_initialize` on
`(namedInstance I, ℓ₀, g₀)` whenever `ℓ₀` satisfies `LengthsWithin` and `IsDyadicGrid`. -/
theorem dryChainLenGridInv_init (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    (ℓ₀ g₀ : ℕ → ℝ)
    (hLenWithin :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      IPM.LengthsWithin (namedInstance I) (ipmQualityRangeExponent I.m V k) ℓ₀)
    (hGrid :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      IsDyadicGrid (namedInstance I) (ipmQualityPrecision I.m V k) ℓ₀) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    DryChainLenGridInv J
      (Ordered.algorithm1_initialize cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀
        (namedInstance I) ℓ₀ g₀).1 := by
  intro I cfg
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let E := ipmQualityRangeExponent I.m V k
  let P := ipmQualityPrecision I.m V k
  set ch := (Ordered.algorithm1_initialize cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀
    (namedInstance I) ℓ₀ g₀).1
  have hbd := drySC_chainLen_bounds J hJn hJm hCap ℓ₀ g₀ hLenWithin
  have hEq : ToolInitOrdEqOnE cfg.T := sparseCoreBundleRestartToolMachWith_initOrdEqOnE _ _ _ _ _ _
  have hFacts := ordAlgorithm1_initialize_level_facts hEq cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀
    (namedInstance I) ℓ₀ g₀
  have hG0 : ch.G 0 = namedInstance I := hFacts.1
  have hℓEq : ch.ℓ = ℓ₀ := rfl
  have hImEq : (namedInstance I).m = I.m := namedInstance_m I
  have hInEq : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
  have hImGeJm : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap).1
  have hInLe : I.n ≤ 2 * I.m + 2 := by change J.n + 1 ≤ 2 * I.m + 2; omega
  refine ⟨by rw [hG0, hImEq], by rw [hG0, hInEq]; exact hInLe, ?_, ?_, ?_⟩
  · intro i hi
    have hbi := hbd i hi
    rw [hℓEq]
    exact ⟨hbi.2.2.2.1, hbi.2.2.2.2 hGrid⟩
  · intro i hi b hb e he
    have hbi := hbd i (Nat.le_of_lt hi)
    have hGiV : (ch.G i).IsValid := hbi.1
    have hGiN : (ch.G i).n ≤ 2 * I.m + 2 :=
      (Finset.card_le_card hbi.2.1).trans (by rw [show (namedInstance I).V.card = (namedInstance I).n from rfl, hInEq]; exact hInLe)
    have hGiM : (ch.G i).m ≤ I.m :=
      (Finset.card_le_card hbi.2.2.1).trans (by rw [show (namedInstance I).E.card = (namedInstance I).m from rfl, hImEq])
    have hScEq := (hFacts.2.2.2.2 i hi).2.2.2.2
    have hScEq' : ch.scState i =
        cfg.T.initOrd cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ (ch.G i)
          (ch.toTreeChain.chainLen ℓ₀ i)
          (fun e => if e ∈ (ch.G i).E then (if i = 0 then g₀ e else ch.toTreeChain.chainLen ℓ₀ i e) else 0)
          (ch.levelOrd i) := by
      rw [hScEq]
      exact hEq cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ (ch.G i) _ _ _ _ (ch.levelOrd i)
        (fun f hf => by
          change (if f ∈ (ch.G i).E then ch.toTreeChain.chainLen ℓ₀ i f else 0) = _
          exact ite_eq_left hf)
    rw [hℓEq, hScEq']
    exact dryInitOrd_wstr_bounds J hJn hJm hCap hGiV hGiN hGiM hbi.2.2.2.1 (hbi.2.2.2.2 hGrid) hb he
  · exact ⟨ch.G cfg.P.d, ch.toTreeChain.chainLen ch.ℓ cfg.P.d,
      (Finset.card_le_card (hbd cfg.P.d le_rfl).2.2.1).trans (namedInstance_m I).le,
      hFacts.2.2.2.1⟩

/-- `DryChainLenGridInv` is preserved by `Ordered.algorithm1_shift` at every level `i₀ ≤ cfg.P.d`
(both terminal shifts `i₀ = cfg.P.d` and non-terminal deep shifts `i₀ < cfg.P.d`). -/
theorem dryChainLenGridInv_shift (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hLoopInv : Ordered.ShiftLoopChainInv (concreteCirculationCfgWithLast dryWitnessUsed J) ch)
    (hGridInv : DryChainLenGridInv J ch)
    {i₀ : ℕ} (hi₀ : i₀ ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    DryChainLenGridInv J (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1 := by
  intro cfg
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let E := ipmQualityRangeExponent I.m V k
  let P := ipmQualityPrecision I.m V k
  have hV : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  by_cases hiLt : i₀ < cfg.P.d
  · set next := (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1
    have hLoopInv' : Ordered.ShiftLoopChainInv cfg next := hLoopInv.shift hV i₀ hi₀
    have hInv' := hLoopInv'.1
    have hB' := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
      hV.hTP hV.hγM₀ hV.hγk hInv'
    have hEx := ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P ch hiLt
    have hG0Eq : next.G 0 = ch.G 0 := hEx.1 0 (Nat.zero_le _)
    have hℓEq : next.ℓ = ch.ℓ := hEx.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    obtain ⟨hG0m, hG0n, hLvlOld, hBrOld, _⟩ := hGridInv
    have hLenPre : ∀ m ≤ i₀, next.toTreeChain.chainLen next.ℓ m = ch.toTreeChain.chainLen ch.ℓ m := by
      intro m
      induction m with
      | zero => intro _; simpa [TreeChain.chainLen] using hℓEq
      | succ m ih =>
        intro hm
        have hlt : m < cfg.P.d := lt_of_lt_of_le (Nat.lt_of_succ_le hm) hiLt.le
        obtain ⟨hsc, hbr, _⟩ := hEx.2.1 m (Nat.lt_of_succ_le hm)
        simp only [TreeChain.chainLen]
        rw [ih (Nat.le_of_succ_le hm)]
        congr 1
        change (if m < cfg.P.d then cfg.T.lsfs (next.scState m) (next.bran m) else next.lastLSFs next.lastBran) =
          (if m < cfg.P.d then cfg.T.lsfs (ch.scState m) (ch.bran m) else ch.lastLSFs ch.lastBran)
        rw [ite_eq_left hlt, ite_eq_left hlt, hsc, hbr]
    have hLsfI0 : ∀ b, cfg.T.lsfs (next.scState i₀) b = cfg.T.lsfs (ch.scState i₀) b := by
      intro b
      rw [hEx.2.2.1]
      exact sparseCoreBundleRestartTool_restart_lsfs _ dryCLsstUsed _ _ (ch.scState i₀) _ b
    have hMain : ∀ j ≤ cfg.P.d,
        ((∀ e ∈ (next.G j).E,
            (2 : ℝ) ^ (-(E : ℤ)) ≤ next.toTreeChain.chainLen next.ℓ j e ∧
            next.toTreeChain.chainLen next.ℓ j e ≤ (2 : ℝ) ^ (E + j * (3 * I.m.size + 12))) ∧
          IsDyadicGrid (next.G j) P (next.toTreeChain.chainLen next.ℓ j)) ∧
        (∀ hj : j < cfg.P.d, ∀ b < cfg.P.k, ∀ e ∈ (next.G j).E,
          1 ≤ (cfg.T.lsfs (next.scState j) b).wstr e ∧
          (cfg.T.lsfs (next.scState j) b).wstr e * next.toTreeChain.chainLen next.ℓ j e ≤
            (2 : ℝ) ^ (E + (j + 1) * (3 * I.m.size + 12)) ∧
          ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P =
            (cfg.T.lsfs (next.scState j) b).wstr e * next.toTreeChain.chainLen next.ℓ j e) := by
      intro j
      induction j with
      | zero =>
        intro _
        have hLvl0 := hLvlOld 0 (Nat.zero_le _)
        refine ⟨?_, fun h0 b hb e he => ?_⟩
        · rw [hG0Eq, hLenPre 0 (Nat.zero_le _)]
          exact hLvl0
        · rw [hG0Eq] at he
          rw [hLenPre 0 (Nat.zero_le _)]
          by_cases hi0 : i₀ = 0
          · subst hi0
            rw [hLsfI0 b]
            exact hBrOld 0 h0 b hb e he
          · have hsc0 : next.scState 0 = ch.scState 0 := (hEx.2.1 0 (by omega)).1
            rw [hsc0]
            exact hBrOld 0 h0 b hb e he
      | succ j ih =>
        intro hjLe
        have hjLt : j < cfg.P.d := hjLe
        obtain ⟨hPrevLvl, hPrevBr⟩ := ih (Nat.le_of_lt hjLt)
        have hSubE : (next.G (j + 1)).E ⊆ (next.G j).E := chainInv_G_succ_E_subset hV hInv' hjLt
        have hNextLvl :
            (∀ e ∈ (next.G (j + 1)).E,
              (2 : ℝ) ^ (-(E : ℤ)) ≤ next.toTreeChain.chainLen next.ℓ (j + 1) e ∧
              next.toTreeChain.chainLen next.ℓ (j + 1) e ≤
                (2 : ℝ) ^ (E + (j + 1) * (3 * I.m.size + 12))) ∧
            IsDyadicGrid (next.G (j + 1)) P (next.toTreeChain.chainLen next.ℓ (j + 1)) := by
          have hBrJ := hPrevBr hjLt (next.bran j) (hInv'.hBran j hjLt)
          refine ⟨fun e he => ?_, fun e he => ?_⟩
          · have hej : e ∈ (next.G j).E := hSubE he
            obtain ⟨hw1, hhi, _⟩ := hBrJ e hej
            have hlo := (hPrevLvl.1 e hej).1
            have hpos : (0 : ℝ) ≤ next.toTreeChain.chainLen next.ℓ j e :=
              le_trans (by positivity) hlo
            have hcl : next.toTreeChain.chainLen next.ℓ (j + 1) e =
                (cfg.T.lsfs (next.scState j) (next.bran j)).wstr e *
                  next.toTreeChain.chainLen next.ℓ j e := by
              simp only [TreeChain.chainLen, coreLen, TreeChain.activeLSF, ChainState.toTreeChain,
                hjLt, ↓reduceIte]
            rw [hcl]
            refine ⟨?_, hhi⟩
            calc (2 : ℝ) ^ (-(E : ℤ)) ≤ next.toTreeChain.chainLen next.ℓ j e := hlo
              _ = 1 * next.toTreeChain.chainLen next.ℓ j e := (one_mul _).symm
              _ ≤ (cfg.T.lsfs (next.scState j) (next.bran j)).wstr e *
                    next.toTreeChain.chainLen next.ℓ j e :=
                  mul_le_mul_of_nonneg_right hw1 hpos
          · have hej : e ∈ (next.G j).E := hSubE he
            obtain ⟨_, _, hq⟩ := hBrJ e hej
            simpa [TreeChain.chainLen, coreLen, TreeChain.activeLSF, ChainState.toTreeChain, hjLt] using hq
        refine ⟨hNextLvl, fun hj1Lt b hb e he => ?_⟩
        by_cases hleI : j + 1 ≤ i₀
        · have hGeq : next.G (j + 1) = ch.G (j + 1) := hEx.1 (j + 1) hleI
          rw [hGeq] at he
          rw [hLenPre (j + 1) hleI]
          rcases lt_or_eq_of_le hleI with hltI | heqI
          · rw [(hEx.2.1 (j + 1) hltI).1]
            exact hBrOld (j + 1) hj1Lt b hb e he
          · rw [heqI, hLsfI0 b]
            exact hBrOld i₀ (heqI ▸ hj1Lt) b hb e (heqI ▸ he)
        · have hge : i₀ + 1 ≤ j + 1 := by omega
          have hScEq := (hEx.2.2.2.2.2.2.2.2.1 (j + 1) hge hj1Lt).1
          have hBj1 := hB' (j + 1) (Nat.le_of_lt hj1Lt)
          have hSubE0 : (next.G (j + 1)).E ⊆ (next.G 0).E :=
            chainInv_G_E_subset_G0 hV hInv' (j + 1) (Nat.le_of_lt hj1Lt)
          have hGj1M : (next.G (j + 1)).m ≤ I.m :=
            (Finset.card_le_card hSubE0).trans (hG0Eq ▸ hG0m)
          have hGj1N : (next.G (j + 1)).n ≤ 2 * I.m + 2 :=
            (Finset.card_le_card hBj1.2.1).trans (hG0Eq ▸ hG0n)
          rw [hScEq, ← hℓEq]
          exact dryInitOrd_wstr_bounds J hJn hJm hCap hBj1.1 hGj1N hGj1M
            hNextLvl.1 hNextLvl.2 hb he
    exact ⟨hG0Eq ▸ hG0m, hG0Eq ▸ hG0n, fun j hj => (hMain j hj).1, fun j hj => (hMain j hj.le).2 hj,
      ⟨next.G cfg.P.d, next.toTreeChain.chainLen ch.ℓ cfg.P.d,
        (Finset.card_le_card (chainInv_G_E_subset_G0 hV hInv' cfg.P.d le_rfl)).trans (hG0Eq ▸ hG0m),
        hEx.2.2.2.2.2.2.2.2.2.1⟩⟩
  · have hEqG : (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1.G = ch.G := by
      simp [Ordered.algorithm1_shift, hiLt]
    have hEqSc : (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1.scState = ch.scState := by
      simp [Ordered.algorithm1_shift, hiLt]
    have hEqBr : (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1.bran = ch.bran := by
      simp [Ordered.algorithm1_shift, hiLt]
    have hEqℓ : (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1.ℓ = ch.ℓ := by
      simp [Ordered.algorithm1_shift, hiLt]
    have hEqLastK : (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1.lastK = ch.lastK := by
      simp [Ordered.algorithm1_shift, hiLt]
    have hEqLastLSFs : (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1.lastLSFs = ch.lastLSFs := by
      simp [Ordered.algorithm1_shift, hiLt]
    have hLenEq : ∀ i ≤ cfg.P.d,
        (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1.toTreeChain.chainLen
          (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1.ℓ i =
        ch.toTreeChain.chainLen ch.ℓ i := by
      intro i
      induction i with
      | zero => intro _; simpa [TreeChain.chainLen] using hEqℓ
      | succ i ih =>
        intro hi
        simp only [TreeChain.chainLen]
        rw [ih (Nat.le_of_lt hi)]
        congr 1
        have hlt : i < cfg.P.d := by omega
        change (if i < cfg.P.d then cfg.T.lsfs ((Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1.scState i)
              ((Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1.bran i)
            else (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1.lastLSFs
              (Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i₀).1.lastBran) =
          (if i < cfg.P.d then cfg.T.lsfs (ch.scState i) (ch.bran i) else ch.lastLSFs ch.lastBran)
        rw [ite_eq_left hlt, ite_eq_left hlt, hEqSc, hEqBr]
    obtain ⟨h1, h2, h3, h4, h5⟩ := hGridInv
    refine ⟨by rw [hEqG]; exact h1, by rw [hEqG]; exact h2, fun j hj => ?_, fun j hj b hb e he => ?_,
      by rw [hEqLastK, hEqLastLSFs]; exact h5⟩
    · rw [hEqG, hLenEq j hj]; exact h3 j hj
    · rw [hEqG] at he; rw [hEqSc, hLenEq j hj.le]; exact h4 j hj b hb e he

/-- `rebuildSuffix` always constructs its last-level collection by calling `L.build` on the final
level-`P.d` graph. -/
theorem rebuildSuffix_lastRes_eq_build (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ),
      idx + rem = P.d →
      let res := Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd
      ∃ ℓd : ℕ → ℝ, res.2.2.2.2.2.2.2.1 = L.build (res.1 P.d) ℓd := by
  intro rem
  induction rem with
  | zero =>
    intro idx G sc bran upd cEnc cDec cFwd hsum
    have hidx : idx = P.d := by omega
    subst hidx
    exact ⟨_, rfl⟩
  | succ rem' ih =>
    intro idx G sc bran upd cEnc cDec cFwd hsum
    exact ih (idx + 1) _ _ _ _ _ _ _ (by omega)

/-- `updateLoop` either keeps `(st.lastK, st.lastLSFs)` unchanged or constructs it via `L.build`
on the output level-`P.d` graph. -/
theorem updateLoop_lastLSFs_or_build (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ),
      idx + rem = P.d →
      let stEnd := (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1
      (stEnd.lastK, stEnd.lastLSFs) = (st.lastK, st.lastLSFs) ∨
      ∃ ℓd : ℕ → ℝ, (stEnd.lastK, stEnd.lastLSFs) = L.build (stEnd.G P.d) ℓd := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU curEncAcc hsum
    have hidx : idx = P.d := by omega
    subst hidx
    dsimp only [Ordered.updateLoop]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr ⟨({ st.toTreeChain with G := fun j => if j = P.d then curG else st.G j }).chainLen ℓ' P.d,
        by simp⟩
  | succ rem' ih =>
    intro idx st curG curU curEncAcc hsum
    have hidxLt : idx < P.d := by omega
    dsimp only [Ordered.updateLoop]
    split_ifs
    · right
      simp only [Ordered.algorithm1_rebuild, hidxLt, ↓reduceDIte]
      exact rebuildSuffix_lastRes_eq_build T L P st.lvlM st.N₀ _ _ (P.d - idx) idx
        _ st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd (by omega)
    · exact ih (idx + 1) _ _ _ 0 (by omega)

/-- `algorithm1_update` either keeps `(st.lastK, st.lastLSFs)` or builds it via `L.build` on the
output level-`P.d` graph. -/
theorem algorithm1_update_lastLSFs_or_build (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P)
    (U : List Update) (g' ℓ' : ℕ → ℝ) :
    let stEnd := (Ordered.algorithm1_update T L TP P N₀ st U g' ℓ').1
    (stEnd.lastK, stEnd.lastLSFs) = (st.lastK, st.lastLSFs) ∨
    ∃ ℓd : ℕ → ℝ, (stEnd.lastK, stEnd.lastLSFs) = L.build (stEnd.G P.d) ℓd :=
  updateLoop_lastLSFs_or_build T L TP P N₀ ℓ' g' P.d 0 _ _ U _ (Nat.zero_add _)

/-- Hypothesis 4 of `shiftDeepModelInv_of_loopInv` (`hCoreLenFits`): under `DryChainLenGridInv`,
every edge length `chainLen ch.ℓ (j + 1) e` at level `j < cfg.P.d` is represented exactly by an
integer `q` fitting in `Num.Fits 4 F.limbs`. -/
theorem dryChainLenGridInv_implies_coreLenFits (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hGridInv : DryChainLenGridInv J ch) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let P := ipmQualityPrecision I.m V k
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    ∀ j < cfg.P.d, ∀ e ∈ (ch.G (j + 1)).E,
      ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P =
        ch.toTreeChain.chainLen ch.ℓ (j + 1) e := by
  intro I V k P L cfg j hj e he
  let E := ipmQualityRangeExponent I.m V k
  have hIm1 : 1 ≤ I.m :=
    Nat.lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  obtain ⟨_, _, hLvls, _, _⟩ := hGridInv
  obtain ⟨hBounds, hGrid⟩ := hLvls (j + 1) hj
  obtain ⟨hlo, hhi⟩ := hBounds e he
  obtain ⟨q, hq⟩ := hGrid e he
  have hExp : (j + 1) * (3 * I.m.size + 12) ≤ E := by
    have h1 : (j + 1) * (3 * I.m.size + 12) ≤ cfg.P.d * (3 * I.m.size + 12) :=
      Nat.mul_le_mul_right _ hj
    exact h1.trans (chainLen_exponent_le_rangeExponent I.m V
      (concreteQualityBudgetWithLast dryWitnessUsed) hIm1 cfg.P.hM₀)
  have h2E : ch.toTreeChain.chainLen ch.ℓ (j + 1) e ≤ (2 : ℝ) ^ (2 * E) := by
    have hsum : E + (j + 1) * (3 * I.m.size + 12) ≤ 2 * E := by
      have := Nat.add_le_add_left hExp E
      rwa [← two_mul] at this
    exact hhi.trans (pow_le_pow_right₀ (by norm_num) hsum)
  have hltCap : 2 * (ch.toTreeChain.chainLen ch.ℓ (j + 1) e * (2 : ℝ) ^ P) <
      (Num.capacity 4 L : ℝ) := by
    calc 2 * (ch.toTreeChain.chainLen ch.ℓ (j + 1) e * (2 : ℝ) ^ P)
        ≤ 2 * ((2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ P) := by gcongr
      _ = (2 : ℝ) ^ (P + 2 * E + 1) := by rw [pow_succ, pow_add]; ring
      _ < (Num.capacity 4 L : ℝ) := coreLen_pow_lt_capacity I.m V k
  have h2P_pos : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have hqR : (q : ℝ) = ch.toTreeChain.chainLen ch.ℓ (j + 1) e * (2 : ℝ) ^ P :=
    (div_eq_iff h2P_pos.ne').mp hq
  have hpos : (0 : ℝ) < ch.toTreeChain.chainLen ch.ℓ (j + 1) e :=
    lt_of_lt_of_le (by positivity) hlo
  have hqPos : (0 : ℤ) ≤ q := by
    have : (0 : ℝ) ≤ (q : ℝ) := by rw [hqR]; positivity
    exact_mod_cast this
  have h2qLt : 2 * q < (Num.capacity 4 L : ℤ) := by
    have hreal : ((2 * q : ℤ) : ℝ) < ((Num.capacity 4 L : ℤ) : ℝ) := by
      push_cast; rw [hqR]; exact hltCap
    exact_mod_cast hreal
  refine ⟨q, ⟨?_, h2qLt⟩, hq⟩
  have hcap0 : (0 : ℤ) ≤ (Num.capacity 4 L : ℤ) := Int.natCast_nonneg _
  omega

/-- Hypothesis 5 of `shiftDeepModelInv_of_loopInv` (`hLastStretchFits`): under `ChainInv` and
`DryChainLenGridInv`, the last-level stretch capacity bound holds for every
`stretchP ≤ 100 * F.rangeExponent` (including `dryLastStretchP`). -/
theorem dryChainLenGridInv_implies_lastStretchFits (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hInv : Ordered.ChainInv (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).L
      (concreteCirculationCfgWithLast dryWitnessUsed J).TP
      (concreteCirculationCfgWithLast dryWitnessUsed J).LP
      (concreteCirculationCfgWithLast dryWitnessUsed J).P
      (concreteCirculationCfgWithLast dryWitnessUsed J).N₀ ch)
    (hGridInv : DryChainLenGridInv J ch)
    {stretchP : ℕ}
    (hStretchLe :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      stretchP ≤ 100 * ipmQualityRangeExponent I.m V k) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    ∀ e ∈ (ch.G cfg.P.d).E,
      2 * (2 : ℝ) ^ stretchP *
        lastLevelStretchBound (ch.G cfg.P.d) (ch.toTreeChain.chainLen ch.ℓ cfg.P.d) e <
      Num.capacity 4 L := by
  intro I V k L cfg e he
  let E := ipmQualityRangeExponent I.m V k
  have hV : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hIm1 : 1 ≤ I.m :=
    Nat.lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  obtain ⟨hG0m, _, hLvls, _, _⟩ := hGridInv
  have hBounds := (hLvls cfg.P.d le_rfl).1
  have hExp : cfg.P.d * (3 * I.m.size + 12) ≤ E :=
    chainLen_exponent_le_rangeExponent I.m V (concreteQualityBudgetWithLast dryWitnessUsed)
      hIm1 cfg.P.hM₀
  have hLenUpper : ∀ f ∈ (ch.G cfg.P.d).E,
      ch.toTreeChain.chainLen ch.ℓ cfg.P.d f ≤ (2 : ℝ) ^ (2 * E) := by
    intro f hf
    have hsum : E + cfg.P.d * (3 * I.m.size + 12) ≤ 2 * E := by
      have := Nat.add_le_add_left hExp E
      rwa [← two_mul] at this
    exact (hBounds f hf).2.trans (pow_le_pow_right₀ (by norm_num) hsum)
  have hLenLower : (2 : ℝ) ^ (-(E : ℤ)) ≤ ch.toTreeChain.chainLen ch.ℓ cfg.P.d e :=
    (hBounds e he).1
  have hCardLe : (ch.G cfg.P.d).E.card ≤ 2 ^ I.m.size := by
    have h1 : (ch.G cfg.P.d).E.card ≤ (ch.G 0).E.card :=
      Finset.card_le_card (chainInv_G_E_subset_G0 hV hInv cfg.P.d le_rfl)
    exact (h1.trans hG0m).trans (Nat.lt_size_self I.m).le
  have hSumLe : ∑ f ∈ (ch.G cfg.P.d).E, ch.toTreeChain.chainLen ch.ℓ cfg.P.d f ≤
      (2 : ℝ) ^ I.m.size * (2 : ℝ) ^ (2 * E) := by
    calc ∑ f ∈ (ch.G cfg.P.d).E, ch.toTreeChain.chainLen ch.ℓ cfg.P.d f
        ≤ ∑ _f ∈ (ch.G cfg.P.d).E, (2 : ℝ) ^ (2 * E) := Finset.sum_le_sum hLenUpper
      _ = ((ch.G cfg.P.d).E.card : ℝ) * (2 : ℝ) ^ (2 * E) := by simp
      _ ≤ (2 : ℝ) ^ I.m.size * (2 : ℝ) ^ (2 * E) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hCardLe) (by positivity)
  have hDivLe : (∑ f ∈ (ch.G cfg.P.d).E, ch.toTreeChain.chainLen ch.ℓ cfg.P.d f) /
      ch.toTreeChain.chainLen ch.ℓ cfg.P.d e ≤ (2 : ℝ) ^ (3 * E + I.m.size) := by
    have h2neg : (0 : ℝ) < (2 : ℝ) ^ (-(E : ℤ)) := by positivity
    have hsum_nn : 0 ≤ ∑ f ∈ (ch.G cfg.P.d).E, ch.toTreeChain.chainLen ch.ℓ cfg.P.d f :=
      Finset.sum_nonneg fun f hf => le_trans h2neg.le (hBounds f hf).1
    calc (∑ f ∈ (ch.G cfg.P.d).E, ch.toTreeChain.chainLen ch.ℓ cfg.P.d f) /
          ch.toTreeChain.chainLen ch.ℓ cfg.P.d e
        ≤ ((2 : ℝ) ^ I.m.size * (2 : ℝ) ^ (2 * E)) / (2 : ℝ) ^ (-(E : ℤ)) :=
          div_le_div₀ (by positivity) hSumLe h2neg hLenLower
      _ = (2 : ℝ) ^ I.m.size * (2 : ℝ) ^ (2 * E) * (2 : ℝ) ^ E := by
          rw [zpow_neg, zpow_natCast, div_inv_eq_mul]
      _ = (2 : ℝ) ^ (3 * E + I.m.size) := by
          rw [← pow_add, ← pow_add]
          exact congrArg ((2 : ℝ) ^ ·) (by omega)
  have hBoundLe : lastLevelStretchBound (ch.G cfg.P.d) (ch.toTreeChain.chainLen ch.ℓ cfg.P.d) e ≤
      (2 : ℝ) ^ (3 * E + I.m.size + 1) := by
    unfold lastLevelStretchBound
    have h1 : 1 ≤ 3 * E + I.m.size :=
      Nat.le_trans (Nat.size_pos.mpr hIm1) (Nat.le_add_left _ _)
    have h2le : (2 : ℝ) ≤ (2 : ℝ) ^ (3 * E + I.m.size) := by
      simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h1)
    have hpow : (2 : ℝ) ^ (3 * E + I.m.size) + (2 : ℝ) ^ (3 * E + I.m.size) =
        (2 : ℝ) ^ (3 * E + I.m.size + 1) := by
      rw [pow_succ]; ring
    exact (add_le_add h2le hDivLe).trans_eq hpow
  have hCapLt := lastStretch_pow_lt_capacity I.m V k stretchP hStretchLe
  calc 2 * (2 : ℝ) ^ stretchP *
        lastLevelStretchBound (ch.G cfg.P.d) (ch.toTreeChain.chainLen ch.ℓ cfg.P.d) e
      ≤ 2 * (2 : ℝ) ^ stretchP * (2 : ℝ) ^ (3 * E + I.m.size + 1) := by gcongr
    _ = (2 : ℝ) ^ (stretchP + 3 * E + I.m.size + 2) := by
        rw [show stretchP + 3 * E + I.m.size + 2 =
          1 + stretchP + (3 * E + I.m.size + 1) by ring]
        simp only [pow_add, pow_one]
    _ < (Num.capacity 4 L : ℝ) := hCapLt

/-- `Psc`-free version of `drySC_shiftDeepModelInv_of_loopInv`, taking per-level word bounds
directly. -/
theorem dryShiftDeepModelInv_of_wordBound
    (allocationCoefficient allocationDegree wordExp : ℕ)
    (source J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (hWordLvl :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
      ∀ j < cfg.P.d,
        levelM cfg.TP cfg.P j < 2 ^ w ∧
        (levelM cfg.TP cfg.P j + cfg.N₀ + 2) ^ wordExp * (F.limbs + 1) < 2 ^ w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
    ∀ (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)) (stretchP : ℕ),
      i.val < cfg.P.d →
      Ordered.ShiftLoopChainInv cfg model.chain →
      DryChainLenGridInv J model.chain →
      stretchP ≤ 100 * F.rangeExponent →
      ShiftDeepModelInv w F.limbs F.fmt.precision wordExp stretchP model i ∧
      ShiftDeepModelInvKFBL model i := by
  intro I V k F cfg w model i stretchP hiLt hLoopInv hGridInv hStretchLe
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hLoopInv' := hLoopInv.shift hV i.val hiLt.le
  have hGridInv' := dryChainLenGridInv_shift J hJn hJm hCap hLoopInv hGridInv hiLt.le
  exact shiftDeepModelInv_of_loopInv hV hLoopInv hiLt
    (drySC_toolCostMono J)
    (drySC_lastLevelBuildEqOnE J)
    hWordLvl
    (fun j _ hj => dryChainLenGridInv_implies_coreLenFits J hJn hJm hCap hGridInv' j hj)
    (dryChainLenGridInv_implies_lastStretchFits J hJn hJm hCap hLoopInv'.1 hGridInv' hStretchLe)

end MinCostFlow.Final.DryRun
