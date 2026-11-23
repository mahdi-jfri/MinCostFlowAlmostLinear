module

public import MinCostFlow.Final.WireSelectSizes
public import MinCostFlow.MinRatio.SelectInitWiredCore
import MinCostFlow.Final.AssemblyDryRunSCParam
import Mathlib.Tactic

/-!
# Concrete Init select-region space and fixed cost bounds (`WireInitSelectSizes`)

Defines the concrete `initSelectSpace` and `initSelectFixed` fields of `DryInitSelectSizes`
matching `solverInitWiredSelSpace` and `solverInitWiredSelCost` (`MinRatio/SelectInitWiredCore.lean`
and `MinRatio/SelectInitWired.lean`) at the dry-run parameters, and proves:

1. `solverInitWiredSelSpace_le_dryInitSelectSpace`: for any initial chain `C` whose per-level
   graphs and active forests fit within `((namedInstance I).n, I.m)`, the exact heap space
   `solverInitWiredSelSpace` used by `solverInitWiredSel_runs` is at most `dryInitSelectSpace`.
2. `solverInitWiredSelCost_le_dryInitSelectFixed`: for any such chain `C` and any
   `pLastCost + slotCost ≤ dryParamCost source J`, the exact fixed step overhead
   `solverInitWiredSelCost` used by `solverInitWiredSel_runs` is at most `dryInitSelectFixed Psc`.
3. `dryInitSelectSpace_le_poly`: `dryInitSelectSpace` is bounded by a `PolyNat` function of `I.m`.
4. `dryInitSelectFixed_le_subpoly`: `dryInitSelectFixed Psc` is bounded by `(I.m + 1) * f I.m`
   with `SubpolyNat f`.
5. `dryInitSelectSizes Psc : DryInitSelectSizes` and `dryInitSelectSizeBounds Psc :
   DryInitSelectSizeBounds (dryInitSelectSizes Psc)`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Concrete `initSelectSpace` and `initSelectFixed` matching `solverInitWiredSel_runs` -/

/-- Worst-case `levelM` across all levels `0 .. d` of the dry-run chain. -/
def dryLevelMMax (J : Circulation) : ℕ :=
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  (Finset.Icc 0 cfg.P.d).sup (levelM cfg.TP cfg.P)

/-- Concrete `initSelectSpace` matching `solverInitWiredSelSpace` (`SelectInitWiredCore.lean`) at
`op3Space = 1`, `vCap = (namedInstance I).n`, `eCap = initTargetCap cfg (namedInstance I)`,
`cap = selectHeapCap cfg (namedInstance I) I.m`, `slot = drySlot I.m`, and
`evalSpace = evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L`. -/
def dryInitSelectSpace (_source J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let G := namedInstance I
  let d := cfg.P.d
  let vCap := G.n
  let eCap := initTargetCap cfg G
  let cap := selectHeapCap cfg G I.m
  let slot := drySlot I.m
  let LwMax := ordLevelLwMax L dryCapExp (dryLevelMMax J) cfg.N₀
  let evalSpace := evalKeySpace d (dryMaxEmbLen I.m) L
  1 + dynGraphSize vCap eCap + 3 * I.m +
  selectHeapSize cap d L + selectLevelMetaSize d +
  selectBlocksSize d vCap eCap L slot +
  d * selectFillInteriorLevelSpace I.m I.m L LwMax +
  selectFillLastLevelSpace I.m I.m L +
  (d + 1) * selectPhiFillSpace d vCap L +
  (d + 1) * selectRebuildLevelSpace 0 I.m cap L evalSpace

/-- Concrete `initSelectFixed` matching `solverInitWiredSelCost` (`SelectInitWiredCore.lean`) at
`readoutCost = (drySCParams Psc dryCapExp limbMul).readout`,
`cap = selectHeapCap cfg (namedInstance I) I.m`, `slot = drySlot I.m`,
`evalCost = evalKeyCost cfg.P.d (dryMaxEmbLen I.m) L`, and `pLastCost + slotCost ≤ dryParamCost`. -/
def dryInitSelectFixed (Psc : DrySparseCorePieces) (source J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  let G := namedInstance I
  let d := cfg.P.d
  let vCap := G.n
  let cap := selectHeapCap cfg G I.m
  let slot := drySlot I.m
  let LwMax := ordLevelLwMax L dryCapExp (dryLevelMMax J) cfg.N₀
  let evalCost := evalKeyCost d (dryMaxEmbLen I.m) L
  let readoutCost := (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).readout
  dryParamCost source J +
  readoutCost + 40 + dgCopyRefillCost 0 0 vCap I.m +
  selectRegionSkeletonCost d +
  (I.m * (18 * L + 50) + 20) +
  (d * (selectFillInteriorLevelCost readoutCost 0 0 vCap I.m I.m L LwMax slot + 60) + 10) +
  selectFillLastLevelCost 0 0 0 0 vCap I.m vCap I.m L +
  ((d + 1) * (selectPhiFillCost d vCap L + 40) + 20) +
  (d + 1) * (selectRebuildLevelCost 0 I.m cap L evalCost + 40) + 60 +
  240 + 320

/-- Concrete `DryInitSelectSizes` instance for `solverInitWiredSel_runs`. -/
def dryInitSelectSizes (Psc : DrySparseCorePieces) : DryInitSelectSizes where
  initSelectSpace := dryInitSelectSpace
  initSelectFixed := dryInitSelectFixed Psc

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 2. Dominance over `solverInitWiredSelSpace` and `solverInitWiredSelCost` -/

private lemma wireCoreLenEdgeSpace_mono {K₁ K₂ : ℕ} (h : K₁ ≤ K₂) :
    wireCoreLenEdgeSpace K₁ ≤ wireCoreLenEdgeSpace K₂ := by
  unfold wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
  have hmul : (2 * K₁) * (2 * K₁ + 1) ≤ (2 * K₂) * (2 * K₂ + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

private lemma selCoreLenEdgeSpace_mono {L Lw₁ Lw₂ : ℕ} (h : Lw₁ ≤ Lw₂) :
    selCoreLenEdgeSpace L Lw₁ ≤ selCoreLenEdgeSpace L Lw₂ := by
  unfold selCoreLenEdgeSpace
  exact Nat.add_le_add_left (wireCoreLenEdgeSpace_mono (max_le_max_left L h)) L

private lemma wireCoreLenEdgeCost_mono {K₁ K₂ : ℕ} (h : K₁ ≤ K₂) :
    wireCoreLenEdgeCost K₁ ≤ wireCoreLenEdgeCost K₂ := by
  unfold wireCoreLenEdgeCost
  have hsq : K₁ ^ 2 ≤ K₂ ^ 2 := Nat.pow_le_pow_left h 2
  nlinarith

private lemma selCoreLenEdgeCost_mono {L Lw₁ Lw₂ : ℕ} (h : Lw₁ ≤ Lw₂) :
    selCoreLenEdgeCost L Lw₁ ≤ selCoreLenEdgeCost L Lw₂ := by
  unfold selCoreLenEdgeCost
  have := wireCoreLenEdgeCost_mono (max_le_max_left L h)
  omega

private lemma dgCopyRefillCost_mono {n₁ n₂ m₁ m₂ : ℕ} (hn : n₁ ≤ n₂) (hm : m₁ ≤ m₂) :
    dgCopyRefillCost 0 0 n₁ m₁ ≤ dgCopyRefillCost 0 0 n₂ m₂ := by
  unfold dgCopyRefillCost dgRefillFromListsCost; omega

private lemma selectFillInteriorLevelSpace_mono {m₁ m₂ mF₁ mF₂ L Lw₁ Lw₂ : ℕ}
    (hm : m₁ ≤ m₂) (hmF : mF₁ ≤ mF₂) (hLw : Lw₁ ≤ Lw₂) :
    selectFillInteriorLevelSpace m₁ mF₁ L Lw₁ ≤ selectFillInteriorLevelSpace m₂ mF₂ L Lw₂ := by
  unfold selectFillInteriorLevelSpace
  have h1 := Nat.mul_le_mul hm (selCoreLenEdgeSpace_mono (L := L) hLw)
  omega

private lemma selectFillInteriorLevelCost_mono {rc nF₁ nF₂ mF₁ mF₂ m₁ m₂ L Lw₁ Lw₂ slot : ℕ}
    (hnF : nF₁ ≤ nF₂) (hmF : mF₁ ≤ mF₂) (hm : m₁ ≤ m₂) (hLw : Lw₁ ≤ Lw₂) :
    selectFillInteriorLevelCost rc 0 0 nF₁ mF₁ m₁ L Lw₁ slot ≤
      selectFillInteriorLevelCost rc 0 0 nF₂ mF₂ m₂ L Lw₂ slot := by
  unfold selectFillInteriorLevelCost
  have h1 := dgCopyRefillCost_mono hnF hmF
  have h2 := Nat.mul_le_mul hm (Nat.add_le_add_right (selCoreLenEdgeCost_mono (L := L) hLw) 40)
  have h3 := Nat.mul_le_mul_right (18 * slot + 80) hm
  omega

private lemma selectPhiFillSpace_mono {j₁ j₂ n₁ n₂ Lk : ℕ} (hj : j₁ ≤ j₂) (hn : n₁ ≤ n₂) :
    selectPhiFillSpace j₁ n₁ Lk ≤ selectPhiFillSpace j₂ n₂ Lk := by
  unfold selectPhiFillSpace phiFillEdgeStepSpace
  have h1 := Nat.mul_le_mul hn (Nat.mul_le_mul_right Lk (show 3 * j₁ + 3 ≤ 3 * j₂ + 3 by omega))
  omega

private lemma selectPhiFillCost_mono {j₁ j₂ n₁ n₂ Lk : ℕ} (hj : j₁ ≤ j₂) (hn : n₁ ≤ n₂) :
    selectPhiFillCost j₁ n₁ Lk ≤ selectPhiFillCost j₂ n₂ Lk := by
  unfold selectPhiFillCost
  have h1 := Nat.mul_le_mul_right (130 * Lk + 240) hj
  have h2 := Nat.mul_le_mul hn (Nat.add_le_add_right (Nat.add_le_add_right h1 (125 * Lk)) 900)
  exact Nat.add_le_add_right h2 200

private lemma selectRebuildLevelSpace_mono {m₁ m₂ cap Lk evalSpace : ℕ} (hm : m₁ ≤ m₂) :
    selectRebuildLevelSpace 0 m₁ cap Lk evalSpace ≤
      selectRebuildLevelSpace 0 m₂ cap Lk evalSpace := by
  unfold selectRebuildLevelSpace selectProcessListSpace
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hm) _

private lemma selectRebuildLevelCost_mono {m₁ m₂ cap Lk evalCost : ℕ} (hm : m₁ ≤ m₂) :
    selectRebuildLevelCost 0 m₁ cap Lk evalCost ≤
      selectRebuildLevelCost 0 m₂ cap Lk evalCost := by
  unfold selectRebuildLevelCost selectProcessListCost
  have h1 := Nat.mul_le_mul_right (selectProcessEdgeCost cap Lk evalCost + 40) hm
  omega

/-- `dryInitSelectSpace` dominates `solverInitWiredSelSpace` for any initial chain `C` whose
per-level graphs and active forests have at most `I.m` edges and `(namedInstance I).n` vertices. -/
theorem solverInitWiredSelSpace_le_dryInitSelectSpace
    (source J : Circulation)
    (C : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P)
    (hLvlM : ∀ j < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d,
      C.lvlM j = levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
        (concreteCirculationCfgWithLast dryWitnessUsed J).P j)
    (hN0 : C.N₀ = (concreteCirculationCfgWithLast dryWitnessUsed J).N₀)
    (hGm : ∀ j ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d,
      (C.G j).m ≤ (solverConnectedAugmented J).m)
    (hFm : ∀ j ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d,
      (C.toTreeChain.activeLSF j).F.F.m ≤ (solverConnectedAugmented J).m)
    (hFn : ∀ j ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d,
      (C.toTreeChain.activeLSF j).F.F.n ≤ (namedInstance (solverConnectedAugmented J)).n) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    solverInitWiredSelSpace C G.n (initTargetCap cfg G) (selectHeapCap cfg G I.m) L dryCapExp
      (drySlot I.m) 1 (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L) ≤
      dryInitSelectSpace source J := by
  intro I V k L cfg G
  set d := cfg.P.d
  set vCap := G.n
  set eCap := initTargetCap cfg G
  set cap := selectHeapCap cfg G I.m
  set slot := drySlot I.m
  set LwMax := ordLevelLwMax L dryCapExp (dryLevelMMax J) cfg.N₀
  set evalSpace := evalKeySpace d (dryMaxEmbLen I.m) L
  have hBlkEq : (⟨0, d, vCap, eCap, L, slot⟩ : SelectBlocksLoc).endAddr =
      selectBlocksSize d vCap eCap L slot := by
    have h := SelectBlocksLoc.endAddr_eq ⟨0, d, vCap, eCap, L, slot⟩
    simpa using h
  have hIntLe : selectInitInteriorLoopSpace C 0 L dryCapExp ≤
      d * selectFillInteriorLevelSpace I.m I.m L LwMax := by
    unfold selectInitInteriorLoopSpace
    have hsum : (Finset.Ico 0 d).sum (fun j =>
        let Lw := L + (dryCapExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (C.lvlM j + C.N₀ + 2) + 1)
        selectFillInteriorLevelSpace (C.G j).m (C.toTreeChain.activeLSF j).F.F.m L Lw) ≤
        (Finset.Ico 0 d).sum (fun _ => selectFillInteriorLevelSpace I.m I.m L LwMax) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjLt : j < d := (Finset.mem_Ico.mp hj).2
      have hMle : C.lvlM j ≤ dryLevelMMax J := by
        rw [hLvlM j hjLt]
        exact Finset.le_sup (f := levelM cfg.TP cfg.P) (Finset.mem_Icc.mpr ⟨Nat.zero_le _, hjLt.le⟩)
      have hLwLe : L + (dryCapExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (C.lvlM j + C.N₀ + 2) + 1) ≤ LwMax := by
        dsimp only [LwMax]; unfold ordLevelLwMax; rw [hN0]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _
          (Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right (Nat.add_le_add_right hMle _) 2)) 1)) L
      exact selectFillInteriorLevelSpace_mono (hGm j hjLt.le) (hFm j hjLt.le) hLwLe
    simpa [Finset.sum_const, Nat.card_Ico] using hsum
  have hLastLe : selectFillLastLevelSpace (C.G d).m (C.lastLSFs C.lastBran).F.F.m L ≤
      selectFillLastLevelSpace I.m I.m L := by
    unfold selectFillLastLevelSpace
    have h1 : (C.G d).m ≤ I.m := hGm d le_rfl
    have h2 : (C.lastLSFs C.lastBran).F.F.m ≤ I.m := by
      have hactEq : C.toTreeChain.activeLSF d = C.lastLSFs C.lastBran := by
        unfold TreeChain.activeLSF; exact ite_eq_right (lt_irrefl _)
      rw [← hactEq]; exact hFm d le_rfl
    have h3 := Nat.mul_le_mul_right (selCoreLenEdgeSpace L L) h1
    omega
  have hPhiLe : selectPhiLoopSpace C.toTreeChain 0 L ≤ (d + 1) * selectPhiFillSpace d vCap L := by
    unfold selectPhiLoopSpace
    have hsum : (Finset.Icc 0 d).sum (fun j => selectPhiFillSpace j (C.toTreeChain.activeLSF j).F.F.n L) ≤
        (Finset.Icc 0 d).sum (fun _ => selectPhiFillSpace d vCap L) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjLe : j ≤ d := (Finset.mem_Icc.mp hj).2
      exact selectPhiFillSpace_mono hjLe (hFn j hjLe)
    change (Finset.Icc 0 d).sum (fun j => selectPhiFillSpace j (C.toTreeChain.activeLSF j).F.F.n L) ≤ _
    simpa [Finset.sum_const, Nat.card_Icc] using hsum
  have hRebLe : (Finset.Icc 0 d).sum (fun j => selectRebuildLevelSpace 0 (C.G j).E.card cap L evalSpace) ≤
      (d + 1) * selectRebuildLevelSpace 0 I.m cap L evalSpace := by
    have hsum : (Finset.Icc 0 d).sum (fun j => selectRebuildLevelSpace 0 (C.G j).E.card cap L evalSpace) ≤
        (Finset.Icc 0 d).sum (fun _ => selectRebuildLevelSpace 0 I.m cap L evalSpace) := by
      refine Finset.sum_le_sum fun j hj => ?_
      exact selectRebuildLevelSpace_mono (hGm j (Finset.mem_Icc.mp hj).2)
    simpa [Finset.sum_const, Nat.card_Icc] using hsum
  have hGdM : (C.G d).m ≤ I.m := hGm d le_rfl
  change 1 + dynGraphSize vCap eCap + 3 * (C.G d).m +
    selectHeapSize cap d L + selectLevelMetaSize d +
    (⟨0, d, vCap, eCap, L, slot⟩ : SelectBlocksLoc).endAddr +
    (selectInitInteriorLoopSpace C 0 L dryCapExp +
      selectFillLastLevelSpace (C.G d).m (C.lastLSFs C.lastBran).F.F.m L +
      (selectPhiLoopSpace C.toTreeChain 0 L +
        (Finset.Icc 0 d).sum fun j => selectRebuildLevelSpace 0 (C.G j).E.card cap L evalSpace)) ≤
    1 + dynGraphSize vCap eCap + 3 * I.m +
    selectHeapSize cap d L + selectLevelMetaSize d +
    selectBlocksSize d vCap eCap L slot +
    d * selectFillInteriorLevelSpace I.m I.m L LwMax +
    selectFillLastLevelSpace I.m I.m L +
    (d + 1) * selectPhiFillSpace d vCap L +
    (d + 1) * selectRebuildLevelSpace 0 I.m cap L evalSpace
  rw [hBlkEq]
  omega

/-- `dryInitSelectFixed Psc` dominates `solverInitWiredSelCost` for any initial chain `C` whose
per-level graphs and active forests fit within `((namedInstance I).n, I.m)` and any
`pLastCost + slotCost ≤ dryParamCost source J`. -/
theorem solverInitWiredSelCost_le_dryInitSelectFixed
    (Psc : DrySparseCorePieces) (source J : Circulation)
    (pLastCost slotCost : ℕ) (hPLSl : pLastCost + slotCost ≤ dryParamCost source J)
    (C : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P)
    (hLvlM : ∀ j < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d,
      C.lvlM j = levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
        (concreteCirculationCfgWithLast dryWitnessUsed J).P j)
    (hN0 : C.N₀ = (concreteCirculationCfgWithLast dryWitnessUsed J).N₀)
    (hGm : ∀ j ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d,
      (C.G j).m ≤ (solverConnectedAugmented J).m)
    (hGn : ∀ j ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d,
      (C.G j).n ≤ (namedInstance (solverConnectedAugmented J)).n)
    (hFm : ∀ j ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d,
      (C.toTreeChain.activeLSF j).F.F.m ≤ (solverConnectedAugmented J).m)
    (hFn : ∀ j ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d,
      (C.toTreeChain.activeLSF j).F.F.n ≤ (namedInstance (solverConnectedAugmented J)).n) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    let readoutCost := (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).readout
    solverInitWiredSelCost C readoutCost (selectHeapCap cfg G I.m) L dryCapExp (drySlot I.m)
      (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) L) pLastCost slotCost ≤
      dryInitSelectFixed Psc source J := by
  intro I V k L cfg G readoutCost
  set d := cfg.P.d
  set vCap := G.n
  set cap := selectHeapCap cfg G I.m
  set slot := drySlot I.m
  set LwMax := ordLevelLwMax L dryCapExp (dryLevelMMax J) cfg.N₀
  set evalCost := evalKeyCost d (dryMaxEmbLen I.m) L
  have hGdCopy : dgCopyRefillCost 0 0 (C.G d).n (C.G d).m ≤ dgCopyRefillCost 0 0 vCap I.m :=
    dgCopyRefillCost_mono (hGn d le_rfl) (hGm d le_rfl)
  have hG0Copy : (C.G 0).m * (18 * L + 50) + 20 ≤ I.m * (18 * L + 50) + 20 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right (18 * L + 50) (hGm 0 (Nat.zero_le _))) 20
  have hIntLe : selectInitInteriorLoopCost C readoutCost 0 L dryCapExp slot ≤
      d * (selectFillInteriorLevelCost readoutCost 0 0 vCap I.m I.m L LwMax slot + 60) + 10 := by
    unfold selectInitInteriorLoopCost
    have hsum : (Finset.Ico 0 d).sum (fun j =>
        let Lw := L + (dryCapExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (C.lvlM j + C.N₀ + 2) + 1)
        selectFillInteriorLevelCost readoutCost 0 0 (C.toTreeChain.activeLSF j).F.F.n
          (C.toTreeChain.activeLSF j).F.F.m (C.G j).m L Lw slot + 60) ≤
        (Finset.Ico 0 d).sum (fun _ =>
          selectFillInteriorLevelCost readoutCost 0 0 vCap I.m I.m L LwMax slot + 60) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjLt : j < d := (Finset.mem_Ico.mp hj).2
      have hMle : C.lvlM j ≤ dryLevelMMax J := by
        rw [hLvlM j hjLt]
        exact Finset.le_sup (f := levelM cfg.TP cfg.P) (Finset.mem_Icc.mpr ⟨Nat.zero_le _, hjLt.le⟩)
      have hLwLe : L + (dryCapExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (C.lvlM j + C.N₀ + 2) + 1) ≤ LwMax := by
        dsimp only [LwMax]; unfold ordLevelLwMax; rw [hN0]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _
          (Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right (Nat.add_le_add_right hMle _) 2)) 1)) L
      exact Nat.add_le_add_right (selectFillInteriorLevelCost_mono (hFn j hjLt.le) (hFm j hjLt.le)
        (hGm j hjLt.le) hLwLe) 60
    have hsum' : (Finset.Ico 0 d).sum (fun j =>
        let Lw := L + (dryCapExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (C.lvlM j + C.N₀ + 2) + 1)
        selectFillInteriorLevelCost readoutCost 0 0 (C.toTreeChain.activeLSF j).F.F.n
          (C.toTreeChain.activeLSF j).F.F.m (C.G j).m L Lw slot + 60) ≤
        d * (selectFillInteriorLevelCost readoutCost 0 0 vCap I.m I.m L LwMax slot + 60) := by
      simpa [Finset.sum_const, Nat.card_Ico] using hsum
    exact Nat.add_le_add_right hsum' 10
  have hLastLe : selectFillLastLevelCost 0 0 0 0 (C.G d).n (C.G d).m
      (C.lastLSFs C.lastBran).F.F.n (C.lastLSFs C.lastBran).F.F.m L ≤
      selectFillLastLevelCost 0 0 0 0 vCap I.m vCap I.m L := by
    unfold selectFillLastLevelCost
    have hGmD : (C.G d).m ≤ I.m := hGm d le_rfl
    have h1 : dgCopyRefillCost 0 0 (C.G d).n (C.G d).m ≤ dgCopyRefillCost 0 0 vCap I.m :=
      dgCopyRefillCost_mono (hGn d le_rfl) hGmD
    have hactEq : C.toTreeChain.activeLSF d = C.lastLSFs C.lastBran := by
      unfold TreeChain.activeLSF; exact ite_eq_right (lt_irrefl _)
    have hFnD : (C.lastLSFs C.lastBran).F.F.n ≤ vCap := by rw [← hactEq]; exact hFn d le_rfl
    have hFmD : (C.lastLSFs C.lastBran).F.F.m ≤ I.m := by rw [← hactEq]; exact hFm d le_rfl
    have h2 := dgCopyRefillCost_mono hFnD hFmD
    have h3 := Nat.mul_le_mul_right (selCoreLenEdgeCost L L + 40) hGmD
    omega
  have hPhiLe : selectPhiLoopCost C.toTreeChain 0 L ≤
      (d + 1) * (selectPhiFillCost d vCap L + 40) + 20 := by
    unfold selectPhiLoopCost
    have hsum : (Finset.Icc 0 d).sum (fun j => selectPhiFillCost j (C.toTreeChain.activeLSF j).F.F.n L + 40) ≤
        (Finset.Icc 0 d).sum (fun _ => selectPhiFillCost d vCap L + 40) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjLe : j ≤ d := (Finset.mem_Icc.mp hj).2
      exact Nat.add_le_add_right (selectPhiFillCost_mono hjLe (hFn j hjLe)) 40
    have hsum' : (Finset.Icc 0 d).sum (fun j => selectPhiFillCost j (C.toTreeChain.activeLSF j).F.F.n L + 40) ≤
        (d + 1) * (selectPhiFillCost d vCap L + 40) := by
      simpa [Finset.sum_const, Nat.card_Icc] using hsum
    change (Finset.Icc 0 d).sum (fun j => selectPhiFillCost j (C.toTreeChain.activeLSF j).F.F.n L + 40) + 20 ≤ _
    exact Nat.add_le_add_right hsum' 20
  have hRebLe : (Finset.Icc 0 d).sum (fun j => selectRebuildLevelCost 0 (C.G j).E.card cap L evalCost + 40) ≤
      (d + 1) * (selectRebuildLevelCost 0 I.m cap L evalCost + 40) := by
    have hsum : (Finset.Icc 0 d).sum (fun j => selectRebuildLevelCost 0 (C.G j).E.card cap L evalCost + 40) ≤
        (Finset.Icc 0 d).sum (fun _ => selectRebuildLevelCost 0 I.m cap L evalCost + 40) := by
      refine Finset.sum_le_sum fun j hj => ?_
      exact Nat.add_le_add_right (selectRebuildLevelCost_mono (hGm j (Finset.mem_Icc.mp hj).2)) 40
    simpa [Finset.sum_const, Nat.card_Icc] using hsum
  change pLastCost + slotCost +
    readoutCost + 40 + dgCopyRefillCost 0 0 (C.G d).n (C.G d).m +
    (selectRegionSkeletonCost d +
      ((C.G 0).m * (18 * L + 50) + 20) +
      selectInitInteriorLoopCost C readoutCost 0 L dryCapExp slot +
      selectFillLastLevelCost 0 0 0 0 (C.G d).n (C.G d).m
        (C.lastLSFs C.lastBran).F.F.n (C.lastLSFs C.lastBran).F.F.m L +
      (selectPhiLoopCost C.toTreeChain 0 L +
        (Finset.Icc 0 d).sum (fun j => selectRebuildLevelCost 0 (C.G j).E.card cap L evalCost + 40) + 60) + 240) + 320 ≤
    dryParamCost source J +
    readoutCost + 40 + dgCopyRefillCost 0 0 vCap I.m +
    selectRegionSkeletonCost d +
    (I.m * (18 * L + 50) + 20) +
    (d * (selectFillInteriorLevelCost readoutCost 0 0 vCap I.m I.m L LwMax slot + 60) + 10) +
    selectFillLastLevelCost 0 0 0 0 vCap I.m vCap I.m L +
    ((d + 1) * (selectPhiFillCost d vCap L + 40) + 20) +
    (d + 1) * (selectRebuildLevelCost 0 I.m cap L evalCost + 40) + 60 +
    240 + 320
  omega

/-! ## 3. Asymptotic bounds: `PolyNat` for `dryInitSelectSpace` and `SubpolyNat` for `dryInitSelectFixed` -/

private lemma dryNamedInstance_n_le (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap : ∀ e, 1 ≤ J.capacity e) :
    (namedInstance (solverConnectedAugmented J)).n ≤ 2 * ((solverConnectedAugmented J).m + 1) := by
  have hsz := solverConnectedAugmented_size J hJn hJm hCap
  have hnEq : (namedInstance (solverConnectedAugmented J)).n = J.n + 1 := by
    simp [namedInstance, MGraph.n, solverConnectedAugmented, connectedInitialInstance,
      instanceOfArrays, Circulation.toInstance]
  rw [hnEq]
  omega

private lemma dryInitTargetCap_le (J : Circulation) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    initTargetCap cfg (namedInstance I) ≤ 4 * dryM0OfM I.m := by
  dsimp only
  unfold initTargetCap
  have hNf := dryNfMax_le_two_mul_M0 J
  have hmEq : (namedInstance (solverConnectedAugmented J)).m = (solverConnectedAugmented J).m :=
    namedInstance_m _
  have hMle : (solverConnectedAugmented J).m ≤ dryM0OfM (solverConnectedAugmented J).m := le_max_left _ _
  dsimp only at hNf
  omega

private lemma drySelectHeapCap_le' (J : Circulation) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    selectHeapCap cfg (namedInstance I) I.m ≤ 8 * dryM0OfM I.m := by
  have h1 := dryInitTargetCap_le J
  have hmEq : (namedInstance (solverConnectedAugmented J)).m = (solverConnectedAugmented J).m :=
    namedInstance_m _
  dsimp only at h1 ⊢
  unfold selectHeapCap
  unfold initTargetCap at h1
  omega

/-- Uniform `PolyNat` bound on `dryInitSelectSpace`. -/
theorem dryInitSelectSpace_le_poly :
    ∃ f : ℕ → ℕ, PolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryInitSelectSpace source J ≤ f (solverConnectedAugmented J).m := by
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
  have hfdP : PolyNat fd := SubpolyNat.toPolyNat hfdSub
  have hLSub : SubpolyNat dryLimbsOfM := dryLimbsOfM_subpoly
  have hLP : PolyNat dryLimbsOfM := SubpolyNat.toPolyNat hLSub
  have hEmbP : PolyNat dryMaxEmbLen := SubpolyNat.toPolyNat progTool_embLen_le_subpoly.1
  have hSlotP : PolyNat drySlot := SubpolyNat.toPolyNat progTool_embLen_le_subpoly.2.2.2
  have hM0P : PolyNat dryM0OfM := dryM0OfM_poly
  let cLw := dryCapExp + sparseCoreReadout2LimbConst
  have hArgP : PolyNat (fun M => (M + 1) * fLM M + 4 * dryM0OfM M) :=
    PolyNat.add (PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfLMSub))
      (PolyNat.const_mul hM0P 4)
  let fLw : ℕ → ℕ := fun M => dryLimbsOfM M + cLw * (Nat.log 2 (((M + 1) * fLM M + 4 * dryM0OfM M) + 2) + 1)
  have hfLwP : PolyNat fLw := SubpolyNat.toPolyNat
    (SubpolyNat.add hLSub (SubpolyNat.const_mul (subpolyNat_log_of_poly hArgP) cLw))
  let fLogCap : ℕ → ℕ := fun M => 2 * (Nat.log 2 (8 * dryM0OfM M + 2) + 1) + 1
  have hfLogCapP : PolyNat fLogCap := SubpolyNat.toPolyNat
    (SubpolyNat.add_const (SubpolyNat.const_mul (subpolyNat_log_of_poly (PolyNat.const_mul hM0P 8)) 2) 1)
  let fEdgeSp : ℕ → ℕ := fun M => 25 * (fLw M) ^ 2 + 25 * fLw M + 10
  have hfEdgeSpP : PolyNat fEdgeSp :=
    PolyNat.add_const (PolyNat.add (PolyNat.const_mul (PolyNat.pow hfLwP 2) 25)
      (PolyNat.const_mul hfLwP 25)) 10
  let fEvalSp : ℕ → ℕ := fun M =>
    4 * dryLimbsOfM M + (fd M + 1) * (3 * dryLimbsOfM M) +
      dryMaxEmbLen M * ((fd M + 1) * (3 * dryLimbsOfM M) + 3 * dryLimbsOfM M)
  have hfEvalSpP : PolyNat fEvalSp := by
    have hpg := PolyNat.mul (PolyNat.add_const hfdP 1) (PolyNat.const_mul hLP 3)
    exact PolyNat.add (PolyNat.add (PolyNat.const_mul hLP 4) hpg)
      (PolyNat.mul hEmbP (PolyNat.add hpg (PolyNat.const_mul hLP 3)))
  let fV : ℕ → ℕ := fun M => 2 * (M + 1)
  have hfVP : PolyNat fV := PolyNat.const_mul (PolyNat.add_const PolyNat.id 1) 2
  let fE : ℕ → ℕ := fun M => 4 * dryM0OfM M
  have hfEP : PolyNat fE := PolyNat.const_mul hM0P 4
  let fDG : ℕ → ℕ := fun M => 4 + 7 * fV M + 9 * fE M
  have hfDGP : PolyNat fDG :=
    PolyNat.add (PolyNat.add (PolyNat.const 4) (PolyNat.const_mul hfVP 7)) (PolyNat.const_mul hfEP 9)
  let f : ℕ → ℕ := fun M =>
    1 + fDG M + 3 * M +
    (16 + (fd M + 1) + 40 * dryM0OfM M + 16 * dryM0OfM M * dryLimbsOfM M) +
    (2 + 8 * (fd M + 1)) +
    ((fd M + 1) * (fDG M + fV M * dryLimbsOfM M + fE M * dryLimbsOfM M + fE M + fE M * drySlot M) +
      fDG M + fE M * dryLimbsOfM M) +
    fd M * (7 + 4 * M + M * fEdgeSp M) +
    (6 * M + M * fEdgeSp M) +
    (fd M + 1) * (1 + 2 * fV M + fV M * (3 * fd M + 3) * dryLimbsOfM M) +
    (fd M + 1) * (M * (2 * dryLimbsOfM M + fEvalSp M + fLogCap M * (16 * dryLimbsOfM M)))
  have hfP : PolyNat f := by
    have h1 := PolyNat.add (PolyNat.add (PolyNat.const 1) hfDGP) (PolyNat.const_mul PolyNat.id 3)
    have h2 := PolyNat.add (PolyNat.add (PolyNat.add (PolyNat.const 16) (PolyNat.add_const hfdP 1))
      (PolyNat.const_mul hM0P 40)) (PolyNat.mul (PolyNat.const_mul hM0P 16) hLP)
    have h3 := PolyNat.add (PolyNat.const 2) (PolyNat.const_mul (PolyNat.add_const hfdP 1) 8)
    have h4 := PolyNat.add (PolyNat.add
      (PolyNat.mul (PolyNat.add_const hfdP 1)
        (PolyNat.add (PolyNat.add (PolyNat.add (PolyNat.add hfDGP (PolyNat.mul hfVP hLP))
          (PolyNat.mul hfEP hLP)) hfEP) (PolyNat.mul hfEP hSlotP)))
      hfDGP) (PolyNat.mul hfEP hLP)
    have h5 := PolyNat.mul hfdP (PolyNat.add (PolyNat.add (PolyNat.const 7) (PolyNat.const_mul PolyNat.id 4))
      (PolyNat.mul PolyNat.id hfEdgeSpP))
    have h6 := PolyNat.add (PolyNat.const_mul PolyNat.id 6) (PolyNat.mul PolyNat.id hfEdgeSpP)
    have h7 := PolyNat.mul (PolyNat.add_const hfdP 1)
      (PolyNat.add (PolyNat.add (PolyNat.const 1) (PolyNat.const_mul hfVP 2))
        (PolyNat.mul (PolyNat.mul hfVP (PolyNat.add_const (PolyNat.const_mul hfdP 3) 3)) hLP))
    have h8 := PolyNat.mul (PolyNat.add_const hfdP 1)
      (PolyNat.mul PolyNat.id (PolyNat.add (PolyNat.add (PolyNat.const_mul hLP 2) hfEvalSpP)
        (PolyNat.mul hfLogCapP (PolyNat.const_mul hLP 16))))
    exact PolyNat.mono (fun M => by dsimp only [f]; omega)
      (PolyNat.add (PolyNat.add (PolyNat.add (PolyNat.add (PolyNat.add (PolyNat.add (PolyNat.add h1 h2) h3) h4) h5) h6) h7) h8)
  refine ⟨f, hfP, fun _source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  set G := namedInstance I
  have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
  have hVle : G.n ≤ fV I.m := dryNamedInstance_n_le J hJn hJm hCap
  have hEle : initTargetCap cfg G ≤ fE I.m := dryInitTargetCap_le J
  have hCapLe : selectHeapCap cfg G I.m ≤ 8 * dryM0OfM I.m := drySelectHeapCap_le' J
  have hLMmax : dryLevelMMax J ≤ (I.m + 1) * fLM I.m :=
    Finset.sup_le fun j hj => hfLM J hJn hJm hCap j (Finset.mem_Icc.mp hj).2
  have hLw : ordLevelLwMax L dryCapExp (dryLevelMMax J) cfg.N₀ ≤ fLw I.m := by
    unfold ordLevelLwMax
    dsimp only [fLw, cLw]
    have hN0 : cfg.N₀ = 4 * dryM0OfM I.m := rfl
    exact Nat.add_le_add hL (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.log_mono_right (b := 2) (by omega)) 1))
  have hLleLw : L ≤ ordLevelLwMax L dryCapExp (dryLevelMMax J) cfg.N₀ := by
    unfold ordLevelLwMax; omega
  have hEdgeSp : ∀ Lw, Lw ≤ fLw I.m → selCoreLenEdgeSpace L Lw ≤ fEdgeSp I.m := fun Lw hLw' => by
    unfold selCoreLenEdgeSpace wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
    have hmx : max L Lw ≤ fLw I.m := max_le (hLleLw.trans hLw) hLw'
    have hsq : (max L Lw) ^ 2 ≤ (fLw I.m) ^ 2 := Nat.pow_le_pow_left hmx 2
    have hLleF : L ≤ fLw I.m := hLleLw.trans hLw
    dsimp only [fEdgeSp]
    nlinarith only [hmx, hsq, hLleF]
  have hDG : dynGraphSize G.n (initTargetCap cfg G) ≤ fDG I.m := by
    unfold dynGraphSize; dsimp only [fDG]; omega
  have hHeap : selectHeapSize (selectHeapCap cfg G I.m) cfg.P.d L ≤
      16 + (fd I.m + 1) + 40 * dryM0OfM I.m + 16 * dryM0OfM I.m * dryLimbsOfM I.m := by
    unfold selectHeapSize shHdrSize
    have hm := Nat.mul_le_mul hCapLe hL
    nlinarith only [hd, hCapLe, hm]
  have hMeta : selectLevelMetaSize cfg.P.d ≤ 2 + 8 * (fd I.m + 1) := by
    unfold selectLevelMetaSize; omega
  have hBlks : selectBlocksSize cfg.P.d G.n (initTargetCap cfg G) L (drySlot I.m) ≤
      (fd I.m + 1) * (fDG I.m + fV I.m * dryLimbsOfM I.m + fE I.m * dryLimbsOfM I.m +
        fE I.m + fE I.m * drySlot I.m) + fDG I.m + fE I.m * dryLimbsOfM I.m := by
    unfold selectBlocksSize
    have h1 := Nat.mul_le_mul hVle hL
    have h2 := Nat.mul_le_mul hEle hL
    have h3 := Nat.mul_le_mul_right (drySlot I.m) hEle
    have h4 := Nat.mul_le_mul (show cfg.P.d + 1 ≤ fd I.m + 1 by omega)
      (show dynGraphSize G.n (initTargetCap cfg G) + G.n * L + initTargetCap cfg G * L +
          initTargetCap cfg G + initTargetCap cfg G * drySlot I.m ≤
          fDG I.m + fV I.m * dryLimbsOfM I.m + fE I.m * dryLimbsOfM I.m + fE I.m +
          fE I.m * drySlot I.m by omega)
    omega
  have hInt : cfg.P.d * selectFillInteriorLevelSpace I.m I.m L
      (ordLevelLwMax L dryCapExp (dryLevelMMax J) cfg.N₀) ≤
      fd I.m * (7 + 4 * I.m + I.m * fEdgeSp I.m) := by
    unfold selectFillInteriorLevelSpace
    have h1 := Nat.mul_le_mul_left I.m (hEdgeSp _ hLw)
    exact Nat.mul_le_mul hd (by omega)
  have hLast : selectFillLastLevelSpace I.m I.m L ≤ 6 * I.m + I.m * fEdgeSp I.m := by
    unfold selectFillLastLevelSpace
    have h1 := Nat.mul_le_mul_left I.m (hEdgeSp L (hLleLw.trans hLw))
    omega
  have hPhi : (cfg.P.d + 1) * selectPhiFillSpace cfg.P.d G.n L ≤
      (fd I.m + 1) * (1 + 2 * fV I.m + fV I.m * (3 * fd I.m + 3) * dryLimbsOfM I.m) := by
    unfold selectPhiFillSpace phiFillEdgeStepSpace
    have h1 : G.n * ((3 * cfg.P.d + 3) * L) ≤ fV I.m * (3 * fd I.m + 3) * dryLimbsOfM I.m := by
      rw [mul_assoc]
      exact Nat.mul_le_mul hVle (Nat.mul_le_mul (by omega) hL)
    exact Nat.mul_le_mul (by omega) (by omega)
  have hEval : evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L ≤ fEvalSp I.m := by
    simp only [evalKeySpace, evalEdgePotGradSpace, evalKeyWalkLoopSpace, evalKeyStepSpace]
    dsimp only [fEvalSp]
    have h1 := Nat.mul_le_mul (show cfg.P.d + 1 ≤ fd I.m + 1 by omega) (show 3 * L ≤ 3 * dryLimbsOfM I.m by omega)
    have h2 := Nat.mul_le_mul_left (dryMaxEmbLen I.m) (show (cfg.P.d + 1) * (3 * L) + 3 * L ≤
      (fd I.m + 1) * (3 * dryLimbsOfM I.m) + 3 * dryLimbsOfM I.m by omega)
    omega
  have hReb : (cfg.P.d + 1) * selectRebuildLevelSpace 0 I.m (selectHeapCap cfg G I.m) L
      (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L) ≤
      (fd I.m + 1) * (I.m * (2 * dryLimbsOfM I.m + fEvalSp I.m + fLogCap I.m * (16 * dryLimbsOfM I.m))) := by
    unfold selectRebuildLevelSpace heapClearLevelSpace selectProcessListSpace selectProcessEdgeSpace
      heapRebalanceSpace keyCompareSpace
    have hlg : 2 * Nat.log 2 (selectHeapCap cfg G I.m + 1) + 1 ≤ fLogCap I.m := by
      dsimp only [fLogCap]
      have := Nat.log_mono_right (b := 2) (show selectHeapCap cfg G I.m + 1 ≤ 8 * dryM0OfM I.m + 2 by omega)
      omega
    have hrebal := Nat.mul_le_mul hlg (show 16 * L ≤ 16 * dryLimbsOfM I.m by omega)
    have h1 := Nat.mul_le_mul_left I.m (show 2 * L + evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L +
      (2 * Nat.log 2 (selectHeapCap cfg G I.m + 1) + 1) * (16 * L) ≤
      2 * dryLimbsOfM I.m + fEvalSp I.m + fLogCap I.m * (16 * dryLimbsOfM I.m) by omega)
    simpa only [Nat.zero_mul, Nat.zero_add] using Nat.mul_le_mul (show cfg.P.d + 1 ≤ fd I.m + 1 by omega) h1
  change 1 + dynGraphSize G.n (initTargetCap cfg G) + 3 * I.m +
    selectHeapSize (selectHeapCap cfg G I.m) cfg.P.d L + selectLevelMetaSize cfg.P.d +
    selectBlocksSize cfg.P.d G.n (initTargetCap cfg G) L (drySlot I.m) +
    cfg.P.d * selectFillInteriorLevelSpace I.m I.m L
      (ordLevelLwMax L dryCapExp (dryLevelMMax J) cfg.N₀) +
    selectFillLastLevelSpace I.m I.m L +
    (cfg.P.d + 1) * selectPhiFillSpace cfg.P.d G.n L +
    (cfg.P.d + 1) * selectRebuildLevelSpace 0 I.m (selectHeapCap cfg G I.m) L
      (evalKeySpace cfg.P.d (dryMaxEmbLen I.m) L) ≤ f I.m
  dsimp only [f]
  omega

/-- Uniform `(I.m + 1) * SubpolyNat` bound on `dryInitSelectFixed Psc`. -/
theorem dryInitSelectFixed_le_subpoly (Psc : DrySparseCorePieces) :
    ∃ f : ℕ → ℕ, SubpolyNat f ∧
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        dryInitSelectFixed Psc source J ≤
          ((solverConnectedAugmented J).m + 1) * f (solverConnectedAugmented J).m := by
  obtain ⟨Cparam, hParam⟩ := dryParamCost_polylog
  obtain ⟨fd, hfdSub, hfd⟩ := dryD_le_subpoly
  obtain ⟨fLM, hfLMSub, hfLM⟩ := dryLevelM_le_subpoly
  obtain ⟨fKey, hfKeySub, hKey⟩ := dryKeyCost_le_subpoly
  have hSlotSub : SubpolyNat drySlot := progTool_embLen_le_subpoly.2.2.2
  have hLSub : SubpolyNat dryLimbsOfM := dryLimbsOfM_subpoly
  let rc := (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).readout
  let fParam : ℕ → ℕ := fun M => Cparam * (Nat.log 2 (M + 2) + 1) ^ 24
  have hfParamSub : SubpolyNat fParam :=
    SubpolyNat.const_mul (SubpolyNat.pow (subpolyNat_log_of_poly PolyNat.id) 24) Cparam
  let cLw := dryCapExp + sparseCoreReadout2LimbConst
  have hArgP : PolyNat (fun M => (M + 1) * fLM M + 4 * dryM0OfM M) :=
    PolyNat.add (PolyNat.mul (PolyNat.add_const PolyNat.id 1) (SubpolyNat.toPolyNat hfLMSub))
      (PolyNat.const_mul dryM0OfM_poly 4)
  let fLw : ℕ → ℕ := fun M => dryLimbsOfM M + cLw * (Nat.log 2 (((M + 1) * fLM M + 4 * dryM0OfM M) + 2) + 1)
  have hfLwSub : SubpolyNat fLw :=
    SubpolyNat.add hLSub (SubpolyNat.const_mul (subpolyNat_log_of_poly hArgP) cLw)
  let fCL : ℕ → ℕ := fun M => 35 * dryLimbsOfM M + (1400 * (fLw M) ^ 2 + 2100 * fLw M + 850) + 160
  have hfCLSub : SubpolyNat fCL :=
    SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.const_mul hLSub 35)
      (SubpolyNat.add_const (SubpolyNat.add
        (SubpolyNat.const_mul (SubpolyNat.pow hfLwSub 2) 1400)
        (SubpolyNat.const_mul hfLwSub 2100)) 850)) 160
  let f : ℕ → ℕ := fun M =>
    fParam M + (rc + 1200) + (400 * fd M + 1600) + (18 * dryLimbsOfM M + 70) +
    (fd M * (2 * rc + fCL M + 18 * drySlot M + 1900) + 10) +
    (fCL M + 2100) +
    ((fd M + 1) * (2 * (fd M * (130 * dryLimbsOfM M + 240) + 125 * dryLimbsOfM M + 900) + 240) + 20) +
    ((fd M + 1) * (fKey M + 220)) + 620
  have hfSub : SubpolyNat f := by
    have h1 := SubpolyNat.add hfParamSub (SubpolyNat.const (rc + 1200))
    have h2 := SubpolyNat.add_const (SubpolyNat.const_mul hfdSub 400) 1600
    have h3 := SubpolyNat.add_const (SubpolyNat.const_mul hLSub 18) 70
    have h4 := SubpolyNat.add_const (SubpolyNat.mul hfdSub
      (SubpolyNat.add_const (SubpolyNat.add (SubpolyNat.add (SubpolyNat.const (2 * rc)) hfCLSub)
        (SubpolyNat.const_mul hSlotSub 18)) 1900)) 10
    have h5 := SubpolyNat.add_const hfCLSub 2100
    have h6 := SubpolyNat.add_const (SubpolyNat.mul (SubpolyNat.add_const hfdSub 1)
      (SubpolyNat.add_const (SubpolyNat.const_mul
        (SubpolyNat.add_const (SubpolyNat.add
          (SubpolyNat.mul hfdSub (SubpolyNat.add_const (SubpolyNat.const_mul hLSub 130) 240))
          (SubpolyNat.const_mul hLSub 125)) 900) 2) 240)) 20
    have h7 := SubpolyNat.mul (SubpolyNat.add_const hfdSub 1) (SubpolyNat.add_const hfKeySub 220)
    have h8 := SubpolyNat.const 620
    exact SubpolyNat.mono (fun M => by dsimp only [f]; omega)
      (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add (SubpolyNat.add h1 h2) h3) h4) h5) h6) h7) h8)
  refine ⟨f, hfSub, fun source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  set L := ipmQualityLimbs I.m V k
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  set G := namedInstance I
  have hL : L ≤ dryLimbsOfM I.m := dryLimbs_le_ofM J hJn hJm hCap
  have hd : cfg.P.d ≤ fd I.m := hfd J hJn hJm hCap
  have hVle : G.n ≤ 2 * (I.m + 1) := dryNamedInstance_n_le J hJn hJm hCap
  have hJmLe : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap).1
  have hParamLe : dryParamCost source J ≤ fParam I.m := by
    refine (hParam source J hJn hJm hCap).trans ?_
    dsimp only [fParam]
    exact Nat.mul_le_mul_left Cparam (Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1) 24)
  have hLMmax : dryLevelMMax J ≤ (I.m + 1) * fLM I.m :=
    Finset.sup_le fun j hj => hfLM J hJn hJm hCap j (Finset.mem_Icc.mp hj).2
  have hLw : ordLevelLwMax L dryCapExp (dryLevelMMax J) cfg.N₀ ≤ fLw I.m := by
    unfold ordLevelLwMax
    dsimp only [fLw, cLw]
    have hN0 : cfg.N₀ = 4 * dryM0OfM I.m := rfl
    exact Nat.add_le_add hL (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.log_mono_right (b := 2) (by omega)) 1))
  have hLleLw : L ≤ ordLevelLwMax L dryCapExp (dryLevelMMax J) cfg.N₀ := by
    unfold ordLevelLwMax; omega
  have hCLLe : ∀ Lw, Lw ≤ fLw I.m → selCoreLenEdgeCost L Lw + 40 ≤ fCL I.m := fun Lw hLw' => by
    unfold selCoreLenEdgeCost wireCoreLenEdgeCost
    have hmx : max L Lw ≤ fLw I.m := max_le (hLleLw.trans hLw) hLw'
    have hsq : (max L Lw) ^ 2 ≤ (fLw I.m) ^ 2 := Nat.pow_le_pow_left hmx 2
    dsimp only [fCL]
    nlinarith only [hL, hmx, hsq]
  have hDG : dgCopyRefillCost 0 0 G.n I.m ≤ (I.m + 1) * 1200 := by
    unfold dgCopyRefillCost dgRefillFromListsCost; omega
  have hKeyLe : selectProcessEdgeCost (selectHeapCap cfg G I.m) L
      (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) L) + 40 ≤ fKey I.m :=
    (dryKeyCost_covers source J).1.trans (hKey source J hJn hJm hCap)
  have hT1 : dryParamCost source J ≤ (I.m + 1) * fParam I.m :=
    hParamLe.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hT2 : rc + 40 + dgCopyRefillCost 0 0 G.n I.m ≤ (I.m + 1) * (rc + 1200) := by
    unfold dgCopyRefillCost dgRefillFromListsCost; nlinarith only [hVle]
  have hT3 : selectRegionSkeletonCost cfg.P.d ≤ (I.m + 1) * (400 * fd I.m + 1600) := by
    unfold selectRegionSkeletonCost
    exact (show 400 * cfg.P.d + 1600 ≤ 400 * fd I.m + 1600 by omega).trans
      (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hT4 : I.m * (18 * L + 50) + 20 ≤ (I.m + 1) * (18 * dryLimbsOfM I.m + 70) := by
    nlinarith only [hL]
  have hT5 : cfg.P.d * (selectFillInteriorLevelCost rc 0 0 G.n I.m I.m L
      (ordLevelLwMax L dryCapExp (dryLevelMMax J) cfg.N₀) (drySlot I.m) + 60) + 10 ≤
      (I.m + 1) * (fd I.m * (2 * rc + fCL I.m + 18 * drySlot I.m + 1900) + 10) := by
    have hcl := hCLLe _ hLw
    have hBody : selectFillInteriorLevelCost rc 0 0 G.n I.m I.m L
        (ordLevelLwMax L dryCapExp (dryLevelMMax J) cfg.N₀) (drySlot I.m) + 60 ≤
        (I.m + 1) * (2 * rc + fCL I.m + 18 * drySlot I.m + 1900) := by
      unfold selectFillInteriorLevelCost dgCopyRefillCost dgRefillFromListsCost
      have h1 := Nat.mul_le_mul_left I.m hcl
      nlinarith only [hVle, h1]
    have hmul : cfg.P.d * (selectFillInteriorLevelCost rc 0 0 G.n I.m I.m L
        (ordLevelLwMax L dryCapExp (dryLevelMMax J) cfg.N₀) (drySlot I.m) + 60) ≤
        fd I.m * ((I.m + 1) * (2 * rc + fCL I.m + 18 * drySlot I.m + 1900)) :=
      Nat.mul_le_mul hd hBody
    nlinarith only [hmul]
  have hT6 : selectFillLastLevelCost 0 0 0 0 G.n I.m G.n I.m L ≤ (I.m + 1) * (fCL I.m + 2100) := by
    unfold selectFillLastLevelCost dgCopyRefillCost dgRefillFromListsCost
    have hcl := hCLLe L (hLleLw.trans hLw)
    have h1 := Nat.mul_le_mul_left I.m hcl
    nlinarith only [hVle, h1]
  have hT7 : (cfg.P.d + 1) * (selectPhiFillCost cfg.P.d G.n L + 40) + 20 ≤
      (I.m + 1) * ((fd I.m + 1) * (2 * (fd I.m * (130 * dryLimbsOfM I.m + 240) +
        125 * dryLimbsOfM I.m + 900) + 240) + 20) := by
    have hpf : selectPhiFillCost cfg.P.d G.n L + 40 ≤
        (I.m + 1) * (2 * (fd I.m * (130 * dryLimbsOfM I.m + 240) +
          125 * dryLimbsOfM I.m + 900) + 240) := by
      unfold selectPhiFillCost
      have h1 := Nat.mul_le_mul hd (show 130 * L + 240 ≤ 130 * dryLimbsOfM I.m + 240 by omega)
      have h2 := Nat.mul_le_mul hVle (Nat.add_le_add_right (Nat.add_le_add h1 (Nat.mul_le_mul_left 125 hL)) 900)
      nlinarith only [h2]
    have hmul := Nat.mul_le_mul (show cfg.P.d + 1 ≤ fd I.m + 1 by omega) hpf
    nlinarith only [hmul]
  have hT8 : (cfg.P.d + 1) * (selectRebuildLevelCost 0 I.m (selectHeapCap cfg G I.m) L
      (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) L) + 40) ≤
      (I.m + 1) * ((fd I.m + 1) * (fKey I.m + 220)) := by
    have hrb : selectRebuildLevelCost 0 I.m (selectHeapCap cfg G I.m) L
        (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) L) + 40 ≤ (I.m + 1) * (fKey I.m + 220) := by
      unfold selectRebuildLevelCost heapClearLevelCost selectProcessListCost
      have h1 := Nat.mul_le_mul_left I.m hKeyLe
      nlinarith only [h1]
    have hmul := Nat.mul_le_mul (show cfg.P.d + 1 ≤ fd I.m + 1 by omega) hrb
    nlinarith only [hmul]
  have hT9 : 60 + 240 + 320 ≤ (I.m + 1) * 620 := by nlinarith
  have hDist : ∀ x a1 a2 a3 a4 a5 a6 a7 a8 a9 : ℕ,
      x * (a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9) =
        x * a1 + x * a2 + x * a3 + x * a4 + x * a5 + x * a6 + x * a7 + x * a8 + x * a9 := by
    intros; ring
  change dryParamCost source J +
    rc + 40 + dgCopyRefillCost 0 0 G.n I.m +
    selectRegionSkeletonCost cfg.P.d +
    (I.m * (18 * L + 50) + 20) +
    (cfg.P.d * (selectFillInteriorLevelCost rc 0 0 G.n I.m I.m L
      (ordLevelLwMax L dryCapExp (dryLevelMMax J) cfg.N₀) (drySlot I.m) + 60) + 10) +
    selectFillLastLevelCost 0 0 0 0 G.n I.m G.n I.m L +
    ((cfg.P.d + 1) * (selectPhiFillCost cfg.P.d G.n L + 40) + 20) +
    (cfg.P.d + 1) * (selectRebuildLevelCost 0 I.m (selectHeapCap cfg G I.m) L
      (evalKeyCost cfg.P.d (dryMaxEmbLen I.m) L) + 40) + 60 +
    240 + 320 ≤ (I.m + 1) * f I.m
  dsimp only [f]
  rw [hDist]
  omega

/-- Concrete `DryInitSelectSizeBounds` proof for `dryInitSelectSizes Psc`. -/
theorem dryInitSelectSizeBounds (Psc : DrySparseCorePieces) :
    DryInitSelectSizeBounds (dryInitSelectSizes Psc) where
  hInitSelectSpacePoly := dryInitSelectSpace_le_poly
  hInitSelectFixedSub := dryInitSelectFixed_le_subpoly Psc

end MinCostFlow.Final.DryRun

end
